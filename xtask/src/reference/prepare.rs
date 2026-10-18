pub(super) mod archive;

use std::fs::{self, OpenOptions};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use serde_json::{Value, json};

use super::common::{self, COMMIT};
use crate::runner::{StepError, io_error};

pub const ARCHIVE_NAME: &str = "Isabelle2025_linux.complete.tar.gz";
pub const ARCHIVE_URL: &str =
    "https://isabelle.in.tum.de/website-Isabelle2025/dist/Isabelle2025_linux.tar.gz";
pub const ARCHIVE_SIZE: u64 = 1_083_266_495;
pub const ARCHIVE_SHA256: &str = "3d1d66de371823fe31aa8ae66638f73575bac244f00b31aee1dcb62f38147c56";
pub const SETTINGS: &str = "ISABELLE_HEAPS_SYSTEM=\"/work/empty-system-heaps\"\nISABELLE_HEAPS=\"$ISABELLE_HOME_USER/heaps\"\nISABELLE_TMP_PREFIX=\"/work/tmp/isabelle\"\nISABELLE_TOOL_JAVA_OPTIONS=\"-Djava.awt.headless=true -Djava.io.tmpdir=/work/tmp -Xms256m -Xmx2g -Xss16m\"\nLD_LIBRARY_PATH=\"/run/current-system/sw/share/nix-ld/lib\"\n";
const EXTRA_DIRS: [&str; 2] = ["lib/classes", "src/Tools/Demo/lib"];

pub(super) fn failure(operation: &str, path: &Path, detail: &str) -> StepError {
    StepError::Input(format!("user-fixable: {operation} on {}: {detail}", path.display()))
}

pub(super) fn read_text(path: &Path) -> Result<String, StepError> {
    common::require_regular(path)?;
    fs::read_to_string(path).map_err(|e| io_error(format!("read {}", path.display()), e))
}

pub(super) fn exclusive_text(path: &Path, content: &str) -> Result<(), StepError> {
    let mut options = OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600);
    }
    let mut file = options
        .open(path)
        .map_err(|e| io_error(format!("create {} exclusively", path.display()), e))?;
    file.write_all(content.as_bytes()).map_err(|e| io_error(format!("write {}", path.display()), e))
}

pub(super) fn require_empty_directory(path: &Path, operation: &str) -> Result<(), StepError> {
    let mut entries = fs::read_dir(path)
        .map_err(|e| io_error(format!("enumerate {} for {operation}", path.display()), e))?;
    if let Some(entry) = entries.next() {
        entry.map_err(|e| io_error(format!("enumerate {} for {operation}", path.display()), e))?;
        return Err(failure(operation, path, "must remain empty"));
    }
    Ok(())
}

pub(super) fn ensure_text(path: &Path, content: &str) -> Result<(), StepError> {
    if fs::symlink_metadata(path).is_ok() {
        if read_text(path)? != content {
            return Err(failure("verify isolated configuration", path, "unexpected contents"));
        }
    } else {
        exclusive_text(path, content)?;
    }
    Ok(())
}

pub(super) fn ensure_directory(path: &Path) -> Result<(), StepError> {
    let builder = fs::DirBuilder::new();
    #[cfg(unix)]
    let builder = {
        use std::os::unix::fs::DirBuilderExt;
        let mut builder = builder;
        builder.mode(0o700);
        builder
    };
    if let Err(e) = builder.create(path)
        && e.kind() != std::io::ErrorKind::AlreadyExists
    {
        return Err(io_error(format!("create directory {}", path.display()), e));
    }
    if !fs::symlink_metadata(path)
        .map_err(|e| io_error(format!("inspect directory {}", path.display()), e))?
        .file_type()
        .is_dir()
    {
        return Err(failure("verify directory", path, "ordinary directory required"));
    }
    Ok(())
}

#[cfg(unix)]
pub(super) fn require_external_workspace(
    workspace: &Path,
    repository: &Path,
) -> Result<PathBuf, StepError> {
    use std::os::unix::fs::MetadataExt;
    if !workspace.is_absolute() || workspace == Path::new("/") {
        return Err(failure("select workspace", workspace, "absolute non-root path required"));
    }
    let repository = repository
        .canonicalize()
        .map_err(|e| io_error(format!("canonicalize {}", repository.display()), e))?;
    let resolved = if workspace.exists() {
        workspace.canonicalize()
    } else {
        let mut ancestor = workspace.to_path_buf();
        let mut suffix = Vec::new();
        while !ancestor.exists() {
            let name = ancestor
                .file_name()
                .ok_or_else(|| failure("select workspace", workspace, "no existing ancestor"))?;
            suffix.push(name.to_os_string());
            ancestor = ancestor
                .parent()
                .ok_or_else(|| failure("select workspace", workspace, "no existing ancestor"))?
                .to_path_buf();
        }
        ancestor.canonicalize().map(|mut path| {
            for part in suffix.into_iter().rev() {
                path.push(part);
            }
            path
        })
    }
    .map_err(|e| io_error(format!("canonicalize {}", workspace.display()), e))?;
    if resolved.starts_with(&repository) || repository.starts_with(&resolved) {
        return Err(failure(
            "select workspace",
            workspace,
            "workspace must be external to repository",
        ));
    }
    if let Ok(meta) = fs::symlink_metadata(workspace)
        && (!meta.file_type().is_dir()
            || meta.uid() != unsafe { libc::geteuid() }
            || meta.mode() & 0o022 != 0)
    {
        return Err(failure(
            "select workspace",
            workspace,
            "owned ordinary non-shared-writable directory required",
        ));
    }
    Ok(resolved)
}

#[cfg(not(unix))]
pub(super) fn require_external_workspace(
    _workspace: &Path,
    _repository: &Path,
) -> Result<PathBuf, StepError> {
    Err(StepError::Input("reference workspace requires Unix filesystem permissions".into()))
}

fn command_stdout(mut command: Command, operation: &str) -> Result<String, StepError> {
    let output = command.output().map_err(|e| {
        io_error(format!("{operation}: launch {}", command.get_program().to_string_lossy()), e)
    })?;
    if !output.status.success() {
        return Err(StepError::Exit { operation: operation.into(), status: output.status });
    }
    String::from_utf8(output.stdout)
        .map_err(|source| StepError::Utf8 { operation: operation.into(), source })
}

/// Check the repository's fixed official checkout before product verification.
pub fn check_pinned_source(repository: &Path) -> Result<(), StepError> {
    require_clean_source(&repository.join("isabelle-source"), repository)
}

pub(super) fn require_clean_source(source: &Path, repository: &Path) -> Result<(), StepError> {
    let canonical = source
        .canonicalize()
        .map_err(|e| io_error(format!("canonicalize source {}", source.display()), e))?;
    let gitlink = repository
        .join("isabelle-source")
        .canonicalize()
        .map_err(|e| io_error("canonicalize repository Gitlink", e))?;
    if !source.is_absolute() || canonical != gitlink {
        return Err(failure("verify source", source, "must be repository Gitlink"));
    }
    for relative in [
        "src/Pure/ROOT.ML",
        "src/HOL/HOL.thy",
        "src/HOL/Orderings.thy",
        "src/HOL/Set.thy",
        "src/HOL/Nat.thy",
        "src/HOL/List.thy",
        "src/HOL/Fun.thy",
        "src/HOL/Product_Type.thy",
        "src/HOL/Sum_Type.thy",
        "src/HOL/Option.thy",
    ] {
        common::require_regular(&source.join(relative))?;
    }
    let checks = [
        ("checkout HEAD", source, vec!["rev-parse", "HEAD"], COMMIT.to_owned()),
        (
            "checkout worktree",
            source,
            vec!["status", "--porcelain", "--untracked-files=all"],
            String::new(),
        ),
        (
            "index Gitlink",
            repository,
            vec!["ls-files", "--stage", "isabelle-source"],
            format!("160000 {COMMIT} 0\tisabelle-source"),
        ),
    ];
    for (identity, directory, args, wanted) in checks {
        let operation = format!("verify {identity} for {}", source.display());
        let mut command = Command::new("git");
        command.arg("-C").arg(directory).args(args);
        if command_stdout(command, &operation)?.trim() != wanted {
            return Err(failure(
                &operation,
                source,
                "expected fixed Isabelle2025 Gitlink and clean checkout",
            ));
        }
    }
    Ok(())
}

fn require_archive(path: &Path) -> Result<(), StepError> {
    common::require_regular(path)?;
    let size = fs::metadata(path)
        .map_err(|e| io_error(format!("stat archive {}", path.display()), e))?
        .len();
    if size != ARCHIVE_SIZE || common::digest_file(path)? != ARCHIVE_SHA256 {
        return Err(failure("verify official archive", path, "size or SHA256 mismatch"));
    }
    Ok(())
}

fn download_archive(partial: &Path) -> Result<(), StepError> {
    let status = Command::new("curl")
        .args([
            "--fail",
            "--show-error",
            "--location",
            "--proto",
            "=https",
            "--proto-redir",
            "=https",
            "--connect-timeout",
            "30",
            "--max-time",
            "7200",
            "--continue-at",
            "-",
            "--output",
        ])
        .arg(partial)
        .arg(ARCHIVE_URL)
        .status()
        .map_err(|e| io_error("download official archive with curl", e))?;
    if !status.success() {
        return Err(StepError::Exit {
            operation: format!("download official archive at {}", partial.display()),
            status,
        });
    }
    Ok(())
}

fn retrieve_archive(workspace: &Path) -> Result<PathBuf, StepError> {
    let archive = workspace.join(ARCHIVE_NAME);
    if fs::symlink_metadata(&archive).is_ok() {
        require_archive(&archive)?;
        return Ok(archive);
    }
    let partial = workspace.join(format!("{ARCHIVE_NAME}.partial"));
    let marker = workspace.join("download-state.json");
    let expected =
        json!({"url":ARCHIVE_URL,"size":ARCHIVE_SIZE,"sha256":ARCHIVE_SHA256,"partial":partial});
    if fs::symlink_metadata(&partial).is_ok() {
        common::require_regular(&partial)?;
        if common::read_json(&marker)? != expected {
            return Err(failure("resume archive", &partial, "unowned partial download"));
        }
    } else {
        if fs::symlink_metadata(&marker).is_ok() {
            return Err(failure("resume archive", &marker, "orphaned download marker"));
        }
        common::write_json_exclusive(&marker, &expected)?;
        exclusive_text(&partial, "")?;
    }
    if fs::metadata(&partial).map_err(|e| io_error(format!("stat {}", partial.display()), e))?.len()
        > ARCHIVE_SIZE
    {
        return Err(failure("resume archive", &partial, "partial exceeds official size"));
    }
    download_archive(&partial)?;
    require_archive(&partial)?;
    fs::hard_link(&partial, &archive)
        .map_err(|e| io_error(format!("publish official archive {}", archive.display()), e))?;
    fs::remove_file(&partial)
        .map_err(|e| io_error(format!("remove partial archive {}", partial.display()), e))?;
    Ok(archive)
}

pub(super) fn archive_git_source(source: &Path, workspace: &Path) -> Result<PathBuf, StepError> {
    let destination = workspace.join("fixed-source.tar");
    let stage = tempfile::Builder::new()
        .prefix(".fixed-source-")
        .suffix(".tar")
        .tempfile_in(workspace)
        .map_err(|e| io_error("create temporary fixed Git archive", e))?;
    let output = stage.reopen().map_err(|e| io_error("open temporary fixed Git archive", e))?;
    let status = Command::new("git")
        .arg("-C")
        .arg(source)
        .args(["archive", "--format=tar", COMMIT])
        .stdout(Stdio::from(output))
        .status()
        .map_err(|e| io_error(format!("archive Gitlink {}", source.display()), e))?;
    if !status.success() {
        return Err(StepError::Exit {
            operation: format!("archive Gitlink {}", source.display()),
            status,
        });
    }
    if fs::symlink_metadata(&destination).is_ok() {
        common::require_regular(&destination)?;
        if common::digest_file(stage.path())? != common::digest_file(&destination)? {
            return Err(failure(
                "verify fixed Git archive",
                &destination,
                "Git archive bytes differ",
            ));
        }
    } else {
        fs::hard_link(stage.path(), &destination).map_err(|e| {
            io_error(format!("publish fixed Git archive {}", destination.display()), e)
        })?;
    }
    Ok(destination)
}

pub(super) fn read_components(
    source: &Path,
    distribution: &Path,
) -> Result<Vec<String>, StepError> {
    let components = read_text(&source.join("etc/components"))?
        .lines()
        .map(str::trim)
        .filter(|s| !s.is_empty() && !s.starts_with('#'))
        .map(str::to_owned)
        .collect::<Vec<_>>();
    let release = read_text(&distribution.join("Isabelle2025/etc/components"))?
        .lines()
        .filter(|s| s.starts_with("contrib/"))
        .map(|s| s.trim().to_owned())
        .collect::<Vec<_>>();
    for component in components.iter().chain(&release) {
        let path = if component.starts_with("contrib/") {
            distribution.join("Isabelle2025").join(component)
        } else {
            source.join(component)
        };
        if !fs::symlink_metadata(&path)
            .map_err(|e| io_error(format!("inspect component {}", path.display()), e))?
            .file_type()
            .is_dir()
        {
            return Err(failure("verify component", &path, "missing or unsafe component"));
        }
        let settings = path.join("etc/settings");
        if fs::symlink_metadata(&settings).is_ok() {
            common::require_regular(&settings)?;
        }
    }
    Ok(release)
}

#[cfg(unix)]
fn config_files() -> [(String, String); 4] {
    let uid = unsafe { libc::geteuid() };
    let gid = unsafe { libc::getegid() };
    [
        ("passwd".into(), format!("reference:x:{uid}:{gid}:Reference:/work/home:/bin/bash\n")),
        ("group".into(), format!("reference:x:{gid}:\n")),
        ("hosts".into(), "127.0.0.1 localhost\n::1 localhost\n".into()),
        ("nsswitch.conf".into(), "passwd: files\ngroup: files\nhosts: files\n".into()),
    ]
}

#[cfg(unix)]
fn prepare_configuration(workspace: &Path, components: &[String]) -> Result<String, StepError> {
    let config = workspace.join("etc");
    ensure_directory(&config)?;
    for (name, content) in config_files() {
        ensure_text(&config.join(name), &content)?;
    }
    ensure_directory(&workspace.join("empty-system-heaps"))?;
    verify_configuration(workspace, components)
}
#[cfg(not(unix))]
fn prepare_configuration(_workspace: &Path, _components: &[String]) -> Result<String, StepError> {
    Err(StepError::Input("reference isolated /etc requires Unix".into()))
}

#[cfg(unix)]
pub(super) fn verify_configuration(
    workspace: &Path,
    components: &[String],
) -> Result<String, StepError> {
    let config = workspace.join("etc");
    if !fs::symlink_metadata(&config)
        .map_err(|e| io_error(format!("inspect isolated /etc {}", config.display()), e))?
        .file_type()
        .is_dir()
    {
        return Err(failure("verify isolated /etc", &config, "ordinary directory required"));
    }
    let files = config_files();
    for (name, content) in &files {
        if read_text(&config.join(name))? != *content {
            return Err(failure(
                "verify isolated configuration",
                &config.join(name),
                "unexpected contents",
            ));
        }
    }
    let mut actual = fs::read_dir(&config)
        .map_err(|e| io_error(format!("enumerate {}", config.display()), e))?
        .map(|e| {
            e.map(|x| x.file_name()).map_err(|cause| io_error("enumerate isolated /etc", cause))
        })
        .collect::<Result<Vec<_>, _>>()?;
    actual.sort();
    let mut expected =
        files.iter().map(|(name, _)| std::ffi::OsString::from(name)).collect::<Vec<_>>();
    expected.sort();
    if actual != expected {
        return Err(failure("verify isolated /etc", &config, "extra configuration files"));
    }
    let heaps = workspace.join("empty-system-heaps");
    if !fs::symlink_metadata(&heaps)
        .map_err(|e| io_error(format!("inspect heap root {}", heaps.display()), e))?
        .file_type()
        .is_dir()
    {
        return Err(failure("verify empty heap root", &heaps, "ordinary directory required"));
    }
    require_empty_directory(&heaps, "verify empty heap root")?;
    Ok(components.iter().map(|name| format!("/work/distribution/Isabelle2025/{name}\n")).collect())
}

#[cfg(not(unix))]
pub(super) fn verify_configuration(
    _workspace: &Path,
    _components: &[String],
) -> Result<String, StepError> {
    Err(StepError::Input("reference isolated /etc requires Unix".into()))
}

pub(super) fn check_legacy_configuration(
    workspace: &Path,
    components: &str,
) -> Result<(), StepError> {
    let legacy = workspace.join("home/.isabelle/p0-reference/etc");
    if fs::symlink_metadata(&legacy).is_err() {
        return Ok(());
    }
    ensure_directory(&legacy)?;
    for (name, content) in [("settings", SETTINGS), ("components", components)] {
        if read_text(&legacy.join(name))? != content {
            return Err(failure(
                "adopt legacy configuration",
                &legacy.join(name),
                "different startup settings",
            ));
        }
    }
    let actual = fs::read_dir(&legacy)
        .map_err(|e| io_error(format!("enumerate {}", legacy.display()), e))?
        .map(|entry| {
            entry
                .map(|item| item.file_name())
                .map_err(|e| io_error(format!("enumerate {}", legacy.display()), e))
        })
        .collect::<Result<std::collections::BTreeSet<_>, _>>()?;
    let expected = ["settings", "components"].into_iter().map(std::ffi::OsString::from).collect();
    if actual != expected {
        return Err(failure("adopt legacy configuration", &legacy, "extra startup files"));
    }
    Ok(())
}

pub(super) fn verify_cached_archive(workspace: &Path, report: &Value) -> Result<(), StepError> {
    let archive = workspace.join(ARCHIVE_NAME);
    require_archive(&archive)?;
    if report["archive_sha256"] != ARCHIVE_SHA256 {
        return Err(failure("verify preparation", workspace, "wrong archive digest"));
    }
    let (count, _) = archive::verify_existing_tree(
        &archive,
        &workspace.join("distribution"),
        true,
        "Isabelle2025",
        &[],
    )?;
    if report["archive_members"] != count {
        return Err(failure("verify distribution", workspace, "member count changed"));
    }
    Ok(())
}

pub(super) fn verify_cached_source(
    workspace: &Path,
    source: &Path,
    report: &Value,
) -> Result<(), StepError> {
    let fixed_tar = workspace.join("fixed-source.tar");
    if common::digest_file(&fixed_tar)? != report["git_archive_sha256"] {
        return Err(failure("verify fixed source tar", &fixed_tar, "digest changed"));
    }
    let (_, files) = archive::verify_existing_tree(
        &fixed_tar,
        &workspace.join("fixed-source"),
        false,
        "",
        &EXTRA_DIRS,
    )?;
    if report["source_files"] != files {
        return Err(failure("verify source manifest", &fixed_tar, "members differ"));
    }
    archive::verify_source_links(&fixed_tar, source)
}

pub fn prepare_workspace(
    repository: &Path,
    workspace: &Path,
    source: &Path,
) -> Result<Value, StepError> {
    require_clean_source(source, repository)?;
    let workspace = require_external_workspace(workspace, repository)?;
    if !workspace.exists() {
        #[cfg(unix)]
        {
            use std::os::unix::fs::DirBuilderExt;
            let mut builder = fs::DirBuilder::new();
            builder.recursive(true).mode(0o700);
            builder
                .create(&workspace)
                .map_err(|e| io_error(format!("create workspace {}", workspace.display()), e))?;
        }
        #[cfg(not(unix))]
        fs::create_dir_all(&workspace)
            .map_err(|e| io_error(format!("create workspace {}", workspace.display()), e))?;
    }
    require_external_workspace(&workspace, repository)?;
    let archive = retrieve_archive(&workspace)?;
    let (count, _) =
        archive::verify_tree(&archive, &workspace.join("distribution"), true, "Isabelle2025", &[])?;
    let fixed_tar = archive_git_source(source, &workspace)?;
    let (_, files) =
        archive::verify_tree(&fixed_tar, &workspace.join("fixed-source"), false, "", &EXTRA_DIRS)?;
    archive::verify_source_links(&fixed_tar, source)?;
    for name in EXTRA_DIRS {
        let path = workspace.join("fixed-source").join(name);
        ensure_directory(&path)?;
        require_empty_directory(&path, "verify writable mountpoint")?;
    }
    let components =
        read_components(&workspace.join("fixed-source"), &workspace.join("distribution"))?;
    let component_text = prepare_configuration(&workspace, &components)?;
    check_legacy_configuration(&workspace, &component_text)?;
    let differences = compare_release_sources(&workspace, &files)?;
    let report = json!({"schema":1,"git_commit":COMMIT,"source_root":source,"archive_url":ARCHIVE_URL,"archive_sha256":ARCHIVE_SHA256,"archive_bytes":ARCHIVE_SIZE,"archive_members":count,"git_archive_sha256":common::digest_file(&fixed_tar)?,"source_files":files,"release_differences":differences,"components":components,"settings_sha256":common::digest_bytes(SETTINGS.as_bytes()),"tools":{"git":find_tool("git"),"curl":find_tool("curl")},"git_archive_options":["archive","--format=tar",COMMIT]});
    let manifest = workspace.join("prepared.json");
    if fs::symlink_metadata(&manifest).is_ok() {
        if common::read_json(&manifest)? != report {
            return Err(failure("reuse prepared workspace", &manifest, "manifest differs"));
        }
    } else {
        common::write_json_exclusive(&manifest, &report)?;
    }
    Ok(
        json!({"workspace":workspace,"manifest":manifest,"source_files":files.as_array().map_or(0, Vec::len),"archive_members":count,"archive_sha256":ARCHIVE_SHA256}),
    )
}

pub(super) fn find_tool(name: &str) -> Option<PathBuf> {
    std::env::split_paths(&std::env::var_os("PATH")?).map(|directory| directory.join(name)).find(
        |path| {
            let Ok(metadata) = fs::metadata(path) else {
                return false;
            };
            if !metadata.is_file() {
                return false;
            }
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                metadata.permissions().mode() & 0o111 != 0
            }
            #[cfg(not(unix))]
            {
                true
            }
        },
    )
}

fn compare_release_sources(workspace: &Path, files: &Value) -> Result<Vec<Value>, StepError> {
    let mut differences = Vec::new();
    for file in files
        .as_array()
        .ok_or_else(|| failure("compare release", workspace, "invalid source manifest"))?
    {
        let name = file["path"]
            .as_str()
            .ok_or_else(|| failure("compare release", workspace, "invalid source path"))?;
        let path = workspace.join("distribution/Isabelle2025").join(name);
        let kind = if !path.is_file() {
            "absent-from-distribution"
        } else if common::digest_file(&path)? != file["sha256"] {
            "different-release-content"
        } else {
            continue;
        };
        differences.push(json!({"path":name,"kind":kind}));
    }
    Ok(differences)
}

#[cfg(test)]
mod tests;
