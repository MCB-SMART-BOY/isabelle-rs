use std::env;
use std::path::{Path, PathBuf};

use crate::maintenance::Maintenance;
use crate::reference::{Operation as ReferenceOperation, Options as ReferenceOptions};
use crate::runner::StepError;

const MAX_TIMEOUT_SECS: u64 = 86_400;
const MAX_MEMORY_MIB: u64 = 65_536;
const MAX_AUTO_LIMIT: u64 = 10_000;
const DEFAULT_TIMEOUT_SECS: u64 = 600;
const DEFAULT_MEMORY_MIB: u64 = 4096;

#[derive(Debug, PartialEq, Eq)]
pub enum TestSelection {
    Workspace,
    Library(Option<String>),
    Target(String),
    Doc,
}

#[derive(Debug)]
pub struct Profile {
    pub source_root: PathBuf,
    pub theory: String,
    pub lemma: String,
    pub output_dir: PathBuf,
    pub context_root: Option<PathBuf>,
    pub manifest_in: Option<PathBuf>,
    pub auto_limit: Option<u64>,
    pub timeout_secs: u64,
    pub memory_mib: u64,
}

pub enum Gate {
    Links,
    Snippets,
    Templates,
    Firewall,
    Compat,
    PinnedSource,
}

pub enum Action {
    Help,
    Build(bool),
    Check(bool),
    Fmt,
    Verify,
    Lint,
    Fast,
    Strict,
    Checkpoint,
    Core,
    Lib,
    Docs,
    Gate(Gate),
    Maintenance(Maintenance),
    Supervise(Vec<String>),
    Tier(&'static str),
    Profile(Profile),
    Reference(ReferenceOptions),
    Broad,
    All,
    Test(TestSelection, bool),
    Selftest,
    Rustdoc,
    Audit(bool),
    VersionCheck(String),
    ReleaseCheck(String),
}

fn invalid(message: impl Into<String>) -> StepError {
    StepError::Input(message.into())
}

fn bounded_positive(label: &str, value: &str, maximum: u64) -> Result<u64, StepError> {
    if value.is_empty() || !value.bytes().all(|byte| byte.is_ascii_digit()) {
        return Err(invalid(format!("{label} must be a positive integer at most {maximum}")));
    }
    let number = value.parse::<u64>().map_err(|_| invalid(format!("{label} exceeds {maximum}")))?;
    if number == 0 || number > maximum {
        return Err(invalid(format!("{label} must be a positive integer at most {maximum}")));
    }
    Ok(number)
}

fn environment_limit(
    variable: &str,
    label: &str,
    default: u64,
    maximum: u64,
) -> Result<u64, StepError> {
    match env::var(variable) {
        Ok(value) => bounded_positive(label, &value, maximum),
        Err(env::VarError::NotPresent) => Ok(default),
        Err(error) => Err(invalid(format!("read {variable}: {error}"))),
    }
}

pub fn resource_limits() -> Result<(u64, u64), StepError> {
    Ok((
        environment_limit(
            "HOL_DIAGNOSTIC_TIMEOUT_SECS",
            "timeout-secs",
            DEFAULT_TIMEOUT_SECS,
            MAX_TIMEOUT_SECS,
        )?,
        environment_limit(
            "HOL_DIAGNOSTIC_MEMORY_MIB",
            "memory-mib",
            DEFAULT_MEMORY_MIB,
            MAX_MEMORY_MIB,
        )?,
    ))
}

fn require_path(label: &str, raw: &str, invocation: &Path) -> Result<PathBuf, StepError> {
    if raw.is_empty() {
        return Err(invalid(format!("{label} must not be empty")));
    }
    let path = Path::new(raw);
    let resolved = if path.is_absolute() { path.to_path_buf() } else { invocation.join(path) };
    if resolved.to_str().is_none() {
        return Err(invalid(format!("{label} resolves to a non-UTF-8 path")));
    }
    Ok(resolved)
}

fn require_field<'a>(options: &'a [(String, String)], key: &str) -> Result<&'a str, StepError> {
    options
        .iter()
        .find(|(name, _)| name == key)
        .map(|(_, value)| value.as_str())
        .ok_or_else(|| invalid(format!("missing {key}")))
}

fn option<'a>(options: &'a [(String, String)], key: &str) -> Option<&'a str> {
    options.iter().find(|(name, _)| name == key).map(|(_, value)| value.as_str())
}

fn parse_options(args: &[String], allowed: &[&str]) -> Result<Vec<(String, String)>, StepError> {
    if !args.len().is_multiple_of(2) {
        return Err(invalid(format!("missing value for {}", args[args.len() - 1])));
    }
    let mut options = Vec::new();
    for pair in args.as_chunks::<2>().0 {
        if !allowed.contains(&pair[0].as_str()) {
            return Err(invalid(format!("unknown option: {}", pair[0])));
        }
        if pair[1].is_empty() || pair[1].starts_with("--") {
            return Err(invalid(format!("missing value for {}", pair[0])));
        }
        if options.iter().any(|(name, _)| name == &pair[0]) {
            return Err(invalid(format!("duplicate option: {}", pair[0])));
        }
        options.push((pair[0].clone(), pair[1].clone()));
    }
    Ok(options)
}

fn parse_profile_limits(
    options: &[(String, String)],
) -> Result<(u64, u64, Option<u64>), StepError> {
    let timeout_secs = match option(options, "--timeout-secs") {
        Some(value) => bounded_positive("timeout-secs", value, MAX_TIMEOUT_SECS)?,
        None => environment_limit(
            "HOL_DIAGNOSTIC_TIMEOUT_SECS",
            "timeout-secs",
            DEFAULT_TIMEOUT_SECS,
            MAX_TIMEOUT_SECS,
        )?,
    };
    let memory_mib = match option(options, "--memory-mib") {
        Some(value) => bounded_positive("memory-mib", value, MAX_MEMORY_MIB)?,
        None => environment_limit(
            "HOL_DIAGNOSTIC_MEMORY_MIB",
            "memory-mib",
            DEFAULT_MEMORY_MIB,
            MAX_MEMORY_MIB,
        )?,
    };
    let auto_limit = option(options, "--auto-limit")
        .map(|value| bounded_positive("auto-limit", value, MAX_AUTO_LIMIT))
        .transpose()?;
    Ok((timeout_secs, memory_mib, auto_limit))
}

fn parse_profile(args: &[String], invocation: &Path) -> Result<Action, StepError> {
    let options = parse_options(
        args,
        &[
            "--source-root",
            "--theory",
            "--lemma",
            "--output-dir",
            "--context-root",
            "--manifest-in",
            "--auto-limit",
            "--timeout-secs",
            "--memory-mib",
        ],
    )?;
    let source_root =
        require_path("source-root", require_field(&options, "--source-root")?, invocation)?;
    if !source_root.is_dir() {
        return Err(invalid(format!("source root does not exist: {}", source_root.display())));
    }
    let output_dir =
        require_path("output-dir", require_field(&options, "--output-dir")?, invocation)?;
    if output_dir.exists() {
        return Err(invalid(format!("output directory already exists: {}", output_dir.display())));
    }
    let output_parent = output_dir.parent().ok_or_else(|| {
        invalid(format!("output directory has no parent: {}", output_dir.display()))
    })?;
    if !output_parent.is_dir() {
        return Err(invalid(format!("output parent does not exist: {}", output_parent.display())));
    }
    let context_root = option(&options, "--context-root")
        .map(|value| require_path("context-root", value, invocation))
        .transpose()?;
    let manifest_in = option(&options, "--manifest-in")
        .map(|value| require_path("manifest-in", value, invocation))
        .transpose()?;
    if let Some(path) = &manifest_in
        && !path.is_file()
    {
        return Err(invalid(format!("manifest does not exist: {}", path.display())));
    }
    let (timeout_secs, memory_mib, auto_limit) = parse_profile_limits(&options)?;
    Ok(Action::Profile(Profile {
        source_root,
        theory: require_field(&options, "--theory")?.into(),
        lemma: require_field(&options, "--lemma")?.into(),
        output_dir,
        context_root,
        manifest_in,
        auto_limit,
        timeout_secs,
        memory_mib,
    }))
}

fn parse_test(args: &[String]) -> Result<Action, StepError> {
    let (selection_args, ignored) = match args.iter().position(|arg| arg == "--") {
        Some(index) if args[index + 1..] == ["--ignored"] => (&args[..index], true),
        Some(_) => return Err(invalid("test only accepts -- --ignored after a selector")),
        None => (args, false),
    };
    let selection = match selection_args {
        [] => TestSelection::Workspace,
        [flag] if flag == "--lib" => TestSelection::Library(None),
        [flag, filter] if flag == "--lib" && !filter.starts_with('-') => {
            TestSelection::Library(Some(filter.clone()))
        },
        [flag, target] if flag == "--test" && !target.starts_with('-') => {
            TestSelection::Target(target.clone())
        },
        [flag] if flag == "--doc" => TestSelection::Doc,
        _ => {
            return Err(invalid(
                "test expects [--lib [FILTER] | --test TARGET | --doc] [-- --ignored]",
            ));
        },
    };
    Ok(Action::Test(selection, ignored))
}

fn parse_reference(args: &[String], invocation: &Path) -> Result<Action, StepError> {
    let Some((operation, rest)) = args.split_first() else {
        return Err(invalid("reference requires prepare, build, inventory, or compare"));
    };
    let operation = match operation.as_str() {
        "prepare" => ReferenceOperation::Prepare,
        "build" => ReferenceOperation::Build,
        "inventory" => ReferenceOperation::Inventory,
        "compare" => ReferenceOperation::Compare,
        _ => return Err(invalid(format!("unknown reference operation: {operation}"))),
    };
    let allowed: &[&str] = match operation {
        ReferenceOperation::Prepare => &["--workspace", "--source-root"],
        ReferenceOperation::Build => &["--workspace", "--reference-preapproval"],
        ReferenceOperation::Inventory => &["--workspace", "--build-run", "--reference-preapproval"],
        ReferenceOperation::Compare => {
            &["--rust-report", "--reference-run", "--reference-manifest", "--reference-approval"]
        },
    };
    let options = parse_options(rest, allowed)?;
    let path =
        |key| option(&options, key).map(|value| require_path(key, value, invocation)).transpose();
    let options = ReferenceOptions {
        operation,
        workspace: path("--workspace")?,
        source_root: path("--source-root")?,
        build_run: path("--build-run")?,
        rust_report: path("--rust-report")?,
        reference_run: path("--reference-run")?,
        reference_manifest: path("--reference-manifest")?,
        reference_preapproval: path("--reference-preapproval")?,
        reference_approval: path("--reference-approval")?,
    };
    options.validate()?;
    Ok(Action::Reference(options))
}

pub fn parse(args: &[String], invocation: &Path) -> Result<Action, StepError> {
    let Some((command, rest)) = args.split_first() else {
        return Ok(Action::Help);
    };
    match (command.as_str(), rest) {
        ("help" | "--help" | "-h", []) => Ok(Action::Help),
        ("build", []) => Ok(Action::Build(false)),
        ("build", [flag]) if flag == "--release" => Ok(Action::Build(true)),
        ("check", []) => Ok(Action::Check(false)),
        ("check", [flag]) if flag == "--all-targets" => Ok(Action::Check(true)),
        ("fmt", []) => Ok(Action::Fmt),
        ("verify", []) => Ok(Action::Verify),
        ("lint", []) => Ok(Action::Lint),
        ("fast", []) => Ok(Action::Fast),
        ("strict", []) => Ok(Action::Strict),
        ("checkpoint", []) => Ok(Action::Checkpoint),
        ("core", []) => Ok(Action::Core),
        ("lib", []) => Ok(Action::Lib),
        ("docs", []) => Ok(Action::Docs),
        ("links", []) => Ok(Action::Gate(Gate::Links)),
        ("snippets", []) => Ok(Action::Gate(Gate::Snippets)),
        ("templates", []) => Ok(Action::Gate(Gate::Templates)),
        ("firewall", []) => Ok(Action::Gate(Gate::Firewall)),
        ("compat", []) => Ok(Action::Gate(Gate::Compat)),
        ("pinned-source", []) => Ok(Action::Gate(Gate::PinnedSource)),
        ("install" | "fix" | "package" | "hook", _) => {
            crate::maintenance::parse(args, invocation).map(Action::Maintenance)
        },
        ("supervise", _) => Ok(Action::Supervise(rest.to_vec())),
        ("tier2", []) => Ok(Action::Tier("tier2")),
        ("tier3", []) => Ok(Action::Tier("tier3")),
        ("profile", _) => parse_profile(rest, invocation),
        ("reference", _) => parse_reference(rest, invocation),
        ("broad", []) => Ok(Action::Broad),
        ("all", []) => Ok(Action::All),
        ("test", _) => parse_test(rest),
        ("selftest", []) => Ok(Action::Selftest),
        ("rustdoc", []) => Ok(Action::Rustdoc),
        ("audit", []) => Ok(Action::Audit(false)),
        ("audit", [flag]) if flag == "rustsec" => Ok(Action::Audit(true)),
        ("version-check" | "release-check", _) => {
            let options = parse_options(rest, &["--tag"])?;
            if options.len() != 1 {
                return Err(invalid(format!("{command} requires --tag TAG")));
            }
            let tag = require_field(&options, "--tag")?.to_string();
            if command == "version-check" {
                Ok(Action::VersionCheck(tag))
            } else {
                Ok(Action::ReleaseCheck(tag))
            }
        },
        _ => {
            Err(invalid(format!("unknown or invalid xtask command: {command} {}", rest.join(" "))))
        },
    }
}

pub const HELP: &str = "Usage: cargo xtask <command> [options]\n\
  help                          Commands and proof/diagnostic distinction\n\
  build [--release]             Locked root product build (no install or publish)\n\
  check [--all-targets]         Locked root product check\n\
  fmt | lint | fast             Workspace format, strict workspace Clippy, or format + root check\n\
  verify                        Complete deterministic repository gate (no network audit/Tier)\n\
  strict | checkpoint | core    Kernel gates, focused tests, sampled HOL trust snapshot\n\
  lib | docs                    Root library or documentation gates\n\
  links | snippets | templates  Individual native Rust documentation gates\n\
  firewall | compat | pinned-source  Kernel boundary, compatibility or fixed official checkout gate\n\
  fix <check|apply>             Read-only checks or explicit source fixes\n\
  install [--release] [--check] [--dir CHECKOUT]   Build/check an existing checkout\n\
  package --artifacts PATH     Create release archives; no publishing\n\
  hook <pre-edit|post-edit>     Native path/doc-sync reminders; no source changes\n\
  supervise --worker PATH --output-dir PATH --timeout-secs N --memory-mib N ...\n\
      Low-level diagnostic supervision; no worker compilation or theorem authority.\n\
  tier2 | tier3 | broad | all    Bounded Linux diagnostics; NOT proof gates\n\
  profile --source-root PATH --theory NAME --lemma NAME --output-dir PATH\n\
      [--context-root PATH] [--manifest-in PATH] [--auto-limit N]\n\
      [--timeout-secs N] [--memory-mib N] (no --worker override)\n\
  reference compare --rust-report PATH --reference-run PATH\n\
      [--reference-manifest PATH [--reference-approval PATH]]\n\
      Structural diagnostics only; unavailable P0 evidence blocks full acceptance.\n\
      Offline data only. Local prepare/build/inventory are disabled by the JVM-free policy.\n\
  test [--lib [FILTER] | --test TARGET | --doc] [-- --ignored]\n\
      Default: complete locked workspace tests (ignored historical tests opt-in).\n\
  selftest | rustdoc | audit [rustsec]\n\
  version-check --tag TAG | release-check --tag TAG (version + verify)\n\
  all is NOT the complete quality gate; sampled HOL is NOT full compatibility.\n\
  Diagnostics require Linux, util-linux unshare/setsid and namespace privileges.\n\
  Limits default to 600 seconds/4096 MiB per worker; override\n\
  HOL_DIAGNOSTIC_TIMEOUT_SECS / HOL_DIAGNOSTIC_MEMORY_MIB.\n\
  Audit requires cargo-audit and cargo-deny. All repository automation and tests are Rust.\n";

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::time::{SystemTime, UNIX_EPOCH};

    #[test]
    fn parse_profile_relative_paths_anchor_at_invocation_directory() {
        let nonce = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
        let invocation =
            env::temp_dir().join(format!("xtask paths {} {nonce}", std::process::id()));
        fs::create_dir(&invocation).unwrap();
        fs::create_dir(invocation.join("source root")).unwrap();
        let args: Vec<String> = [
            "profile",
            "--source-root",
            "source root",
            "--theory",
            "Tiny",
            "--lemma",
            "sample",
            "--output-dir",
            "new output",
            "--timeout-secs",
            "1",
            "--memory-mib",
            "1",
        ]
        .map(str::to_string)
        .to_vec();
        let result = parse(&args, &invocation);
        fs::remove_dir_all(&invocation).unwrap();
        let Action::Profile(profile) = result.unwrap() else {
            panic!("profile command expected");
        };
        assert_eq!(profile.source_root, invocation.join("source root"));
        assert_eq!(profile.output_dir, invocation.join("new output"));
    }

    #[test]
    fn parse_test_rejects_conflicts_and_accepts_ignored_filter() {
        let invocation = Path::new("/");
        let valid = ["test", "--lib", "core::thm", "--", "--ignored"].map(str::to_string);
        let Action::Test(TestSelection::Library(Some(filter)), true) =
            parse(&valid, invocation).unwrap()
        else {
            panic!("filtered ignored library tests expected");
        };
        assert_eq!(filter, "core::thm");
        let invalid = ["test", "--lib", "--test", "bnf_tests"].map(str::to_string);
        assert!(parse(&invalid, invocation).is_err());
    }

    #[test]
    fn parse_verify_accepts_only_complete_gate_without_options() {
        let invocation = Path::new("/");
        let valid = ["verify".to_string()];
        assert!(matches!(parse(&valid, invocation), Ok(Action::Verify)));
        let invalid = ["verify", "--ignored"].map(str::to_string);
        assert!(parse(&invalid, invocation).is_err());
    }

    #[test]
    fn parse_pinned_source_accepts_only_standalone_gate() {
        let invocation = Path::new("/");
        let valid = ["pinned-source".to_string()];
        assert!(matches!(parse(&valid, invocation), Ok(Action::Gate(Gate::PinnedSource))));
        let invalid = ["pinned-source", "--ignored"].map(str::to_string);
        assert!(parse(&invalid, invocation).is_err());
    }
}
