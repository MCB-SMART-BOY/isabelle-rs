use std::collections::BTreeMap;
use std::error::Error;
use std::fs;
use std::io;
use std::os::unix::fs::DirBuilderExt;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::rc::Rc;
use std::sync::Arc;
use std::time::{SystemTime, UNIX_EPOCH};

use isabelle_kernel::{Signature, TrustedTheory};
use isabelle_rs::ml::host::files::{
    EffectSet, EnvironmentUse, FileHostBridge, HostIoError, HostRoots, PhaseEffects, RestrictedHost,
};
use isabelle_rs::ml::host::lifecycle::{BuildLifecycle, TaskLease, WorkKind};
use isabelle_rs::ml::{ML_ENVIRONMENT_PURPOSE, Vm};

fn create_vm(scratch: &Path) -> Result<(Vm, BuildLifecycle, Arc<FileHostBridge>), Box<dyn Error>> {
    let source = fs::canonicalize("isabelle-source")?;
    let environment: BTreeMap<_, _> = [
        ("ML_SYSTEM", Some("isabelle-rs-native")),
        ("ML_PLATFORM", Some("x86_64-linux")),
        ("ISABELLE_ML_DEBUGGER", None),
    ]
    .into_iter()
    .map(|(key, value)| {
        (
            EnvironmentUse { key: key.into(), purpose: ML_ENVIRONMENT_PURPOSE.into() },
            value.map(str::to_owned),
        )
    })
    .collect();
    let grants = EffectSet {
        read_source: true,
        write_staging: true,
        read_clock: true,
        sleep: true,
        environment: environment.keys().cloned().collect(),
        ..EffectSet::default()
    };
    let mut binding = None;
    let mut vm = Vm::with_host_factory(|stop| -> Result<_, HostIoError> {
        let lifecycle = BuildLifecycle::new(stop);
        let lease = lifecycle
            .start_root(WorkKind::Evaluation, "actual original ROOT prefix")
            .map_err(|source| HostIoError::Lifecycle { operation: "start smoke", source })?;
        let roots = HostRoots {
            source,
            resources: BTreeMap::new(),
            staging_parent: scratch.into(),
            staging_name: PathBuf::from("private"),
        };
        let host = RestrictedHost::new(
            lifecycle.clone(),
            &lease,
            roots,
            grants.clone(),
            grants.clone(),
            PhaseEffects { active: grants.clone(), draining: grants },
            environment,
        )?;
        let bridge = Arc::new(FileHostBridge::new(host, lease));
        binding = Some((lifecycle, Arc::clone(&bridge)));
        Ok(bridge)
    })?;
    let (lifecycle, bridge) = binding.expect("successful factory binds lifecycle");
    vm.install_bootstrap_host(Arc::clone(&bridge))?;
    Ok((vm, lifecycle, bridge))
}

fn execute_root(scratch: &Path) -> Result<(), Box<dyn Error>> {
    let (mut vm, lifecycle, bridge) = create_vm(scratch)?;
    let context_lease =
        Rc::new(lifecycle.start_root(WorkKind::Evaluation, "native original Context")?);
    let result = vm.evaluate_root_with_context(
        lifecycle.clone(),
        Rc::clone(&context_lease),
        TrustedTheory::root("Pure", Signature::new()),
    );
    drop(vm);
    let context_completion = Rc::try_unwrap(context_lease)
        .map_err(|_| io::Error::other("Context host still holds its task lease"))
        .and_then(|lease: TaskLease| lease.complete().map_err(io::Error::other));
    let source_completion = bridge.complete();
    match result {
        Ok(progress) => {
            for source in progress.prefix.loaded_files {
                println!("EXECUTED {} {}", source.path, source.sha256);
            }
            println!(
                "NATIVE CONTEXT {} source={} replacement={}",
                progress.prefix.next_ml_file,
                progress.context_source_sha256,
                progress.replacement_structure_sha256
            );
            if let Some(path) = progress.remaining_files.first() {
                println!("NEXT {path} (not executed)");
            }
            finalize_build(&lifecycle, context_completion, source_completion)?;
            println!("Context loaded; remaining ROOT suffix is not verified");
            Ok(())
        },
        Err(failure) => {
            for source in failure.loaded_files {
                println!("EXECUTED {} {}", source.path, source.sha256);
            }
            eprintln!("STOP {}: {}", failure.failed_source, failure.error);
            lifecycle.cancel(failure.error.to_string())?;
            if let Err(error) = context_completion {
                eprintln!("CANCELLED CONTEXT LEASE {error}");
            }
            if let Err(error) = source_completion {
                eprintln!("CANCELLED SOURCE LEASE {error}");
            }
            lifecycle.finish_failed()?;
            Err(failure.error)
        },
    }
}

fn finalize_build(
    lifecycle: &BuildLifecycle,
    context_completion: Result<(), io::Error>,
    source_completion: Result<(), HostIoError>,
) -> Result<(), Box<dyn Error>> {
    let mut failures = Vec::new();
    if let Err(error) = context_completion {
        failures.push(format!("complete Context task: {error}"));
    }
    if let Err(error) = source_completion {
        failures.push(format!("complete source task: {error}"));
    }
    if !failures.is_empty() {
        let reason = failures.join("; ");
        lifecycle.cancel(reason.clone())?;
        lifecycle.finish_failed()?;
        return Err(Box::new(io::Error::other(reason)));
    }
    if let Err(error) = lifecycle.begin_draining().and_then(|_| lifecycle.try_close()) {
        lifecycle.cancel(error.to_string())?;
        lifecycle.finish_failed()?;
        return Err(Box::new(error));
    }
    Ok(())
}

fn main() -> ExitCode {
    let result = (|| -> Result<(), Box<dyn Error>> {
        let stamp = SystemTime::now().duration_since(UNIX_EPOCH)?.as_nanos();
        let scratch =
            std::env::temp_dir().join(format!("native-root-smoke-{}-{stamp}", std::process::id()));
        fs::DirBuilder::new().mode(0o700).create(&scratch)?;
        match execute_root(&scratch) {
            Ok(()) => {
                fs::remove_dir_all(&scratch)?;
                Ok(())
            },
            Err(error) => {
                eprintln!("Private ROOT diagnostics retained at {}", scratch.display());
                Err(error)
            },
        }
    })();
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("Native ROOT smoke failed: {error}");
            ExitCode::FAILURE
        },
    }
}
