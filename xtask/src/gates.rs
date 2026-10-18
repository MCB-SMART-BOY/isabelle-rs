//! Repository-maintained documentation, trust-boundary and compatibility gates.
use std::{
    collections::HashMap,
    env, fs,
    io::{self, Write},
    path::{Path, PathBuf},
    process::Command,
};

use crate::runner::{StepError, io_error, run_command};

const SKIPPED_DIRECTORIES: &[&str] = &[".git", "target", "isabelle-source"];
const SNIPPET_LANGUAGES: &[&str] = &["bash", "sh", "shell", "powershell", "rust", "toml", "json"];
const CLASSIFICATION: &str =
    "// Classification: design-only standalone template; not production code.";
const FORBIDDEN_KERNEL: &[&str] =
    &["Typ::dummy", "compat_alpha_eq", "assume_compat", "reflexive_compat", "admit"];
const UPPER_LAYERS: &[&str] =
    &["core", "isar", "hol", "theory", "tools", "session", "lsp", "server", "wasm"];

fn collect_files(directory: &Path, extension: Option<&str>) -> Result<Vec<PathBuf>, StepError> {
    let mut files = Vec::new();
    collect_into(directory, extension, &mut files)?;
    files.sort();
    Ok(files)
}

fn collect_into(
    directory: &Path,
    extension: Option<&str>,
    files: &mut Vec<PathBuf>,
) -> Result<(), StepError> {
    let entries = fs::read_dir(directory)
        .map_err(|source| io_error(format!("enumerate {}", directory.display()), source))?;
    for entry in entries {
        let entry = entry.map_err(|source| {
            io_error(format!("enumerate entry in {}", directory.display()), source)
        })?;
        let kind = entry
            .file_type()
            .map_err(|source| io_error(format!("inspect {}", entry.path().display()), source))?;
        let path = entry.path();
        if kind.is_dir() {
            if !path
                .file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| SKIPPED_DIRECTORIES.contains(&name))
            {
                collect_into(&path, extension, files)?;
            }
        } else if kind.is_file()
            && extension.is_none_or(|ext| path.extension().is_some_and(|actual| actual == ext))
        {
            files.push(path);
        }
    }
    Ok(())
}

fn read_text(path: &Path) -> Result<String, StepError> {
    fs::read_to_string(path).map_err(|source| io_error(format!("read {}", path.display()), source))
}

fn reject_findings(operation: &str, findings: Vec<String>) -> Result<(), StepError> {
    if findings.is_empty() {
        Ok(())
    } else {
        Err(StepError::Input(format!("{operation}:\n{}", findings.join("\n"))))
    }
}

fn report_stdout(message: impl std::fmt::Display) -> Result<(), StepError> {
    writeln!(io::stdout().lock(), "{message}")
        .map_err(|source| io_error("write gate report to stdout", source))
}

fn link_targets(mut line: &str) -> impl Iterator<Item = &str> {
    std::iter::from_fn(move || {
        let start = line.find("](")? + 2;
        line = &line[start..];
        let end = line.find(')')?;
        let target = &line[..end];
        line = &line[end + 1..];
        Some(target)
    })
}

fn local_target(raw: &str) -> Option<&str> {
    let target = raw.trim().trim_matches(['<', '>']);
    if target.is_empty()
        || target.starts_with('#')
        || target.contains("://")
        || ["mailto:", "app:", "file:"].iter().any(|scheme| target.starts_with(scheme))
    {
        return None;
    }
    Some(target.split('#').next().unwrap_or(target))
}

pub fn check_links(root: &Path) -> Result<(), StepError> {
    let files = collect_files(root, Some("md"))?;
    let mut missing = Vec::new();
    for file in &files {
        let content = read_text(file)?;
        for (index, line) in content.lines().enumerate() {
            for raw in link_targets(line) {
                let Some(target) = local_target(raw) else { continue };
                let path = if Path::new(target).is_absolute() {
                    PathBuf::from(target)
                } else {
                    file.parent().unwrap_or(root).join(target)
                };
                if !path.exists() {
                    missing.push(format!("{}:{} -> {target}", file.display(), index + 1));
                }
            }
        }
    }
    reject_findings("Markdown contains missing local links", missing)?;
    report_stdout(format!("Markdown local links clean ({} files)", files.len()))
}

fn snippet_limit(name: &str, default: usize) -> Result<usize, StepError> {
    let Some(value) = env::var_os(name) else { return Ok(default) };
    let value = value
        .to_str()
        .ok_or_else(|| StepError::Input(format!("{name} must be a non-negative integer")))?;
    if value.is_empty() || !value.bytes().all(|byte| byte.is_ascii_digit()) {
        return Err(StepError::Input(format!("{name} must be a non-negative integer")));
    }
    value
        .parse::<usize>()
        .map_err(|source| StepError::Input(format!("{name} must fit usize: {source}")))
}

fn opening_language(line: &str) -> Option<&'static str> {
    let rest = line.strip_prefix("```")?;
    SNIPPET_LANGUAGES.iter().copied().find(|language| {
        rest.get(..language.len()).is_some_and(|prefix| prefix.eq_ignore_ascii_case(language))
            && (rest.len() == language.len()
                || matches!(rest.as_bytes()[language.len()], b' ' | b'\t' | b',' | b'{' | b'\r'))
    })
}

struct SnippetBlock {
    language: &'static str,
    start: usize,
    body: String,
    lines: usize,
}

fn finish_snippet(
    block: SnippetBlock,
    file: &Path,
    maximum: usize,
    duplicate_minimum: usize,
    seen: &mut HashMap<(&'static str, String), (PathBuf, usize)>,
    failures: &mut Vec<String>,
) {
    if block.lines > maximum {
        failures.push(format!(
            "{}:{}: {} fenced block has {} lines; explanatory limit is {maximum}",
            file.display(),
            block.start,
            block.language,
            block.lines
        ));
    }
    if block.lines < duplicate_minimum {
        return;
    }
    let key = (block.language, block.body);
    if let Some((previous, line)) = seen.get(&key) {
        failures.push(format!(
            "{}:{}: duplicates {} fenced block at {}:{} ({} lines)",
            file.display(),
            block.start,
            block.language,
            previous.display(),
            line,
            block.lines
        ));
    } else {
        seen.insert(key, (file.to_path_buf(), block.start));
    }
}

fn inspect_snippets(
    file: &Path,
    maximum: usize,
    duplicate_minimum: usize,
    seen: &mut HashMap<(&'static str, String), (PathBuf, usize)>,
    failures: &mut Vec<String>,
) -> Result<(), StepError> {
    let text = read_text(file)?;
    let mut block: Option<SnippetBlock> = None;
    for (index, line) in text.split_terminator('\n').enumerate() {
        if line.strip_prefix("```").is_some_and(|suffix| suffix.trim().is_empty())
            && let Some(current) = block.take()
        {
            finish_snippet(current, file, maximum, duplicate_minimum, seen, failures);
            continue;
        }
        if let Some(current) = block.as_mut() {
            current.lines += 1;
            current.body.push_str(line);
            current.body.push('\n');
        } else if let Some(language) = opening_language(line) {
            block =
                Some(SnippetBlock { language, start: index + 1, body: String::new(), lines: 0 });
        }
    }
    if let Some(current) = block {
        failures.push(format!(
            "{}:{}: unclosed {} fenced block",
            file.display(),
            current.start,
            current.language
        ));
    }
    Ok(())
}

pub fn check_snippets(root: &Path) -> Result<(), StepError> {
    let maximum = snippet_limit("MAX_EXPLANATORY_LINES", 40)?;
    let duplicate_minimum = snippet_limit("DUPLICATE_MIN_LINES", 12)?;
    let files = collect_files(root, Some("md"))?;
    let mut failures = Vec::new();
    let mut seen = HashMap::new();
    for file in &files {
        inspect_snippets(file, maximum, duplicate_minimum, &mut seen, &mut failures)?;
    }
    reject_findings("Markdown snippet policy violation", failures)?;
    report_stdout(format!(
        "Markdown snippet policy clean ({} files; explanatory limit {maximum} lines)",
        files.len()
    ))
}

fn rust_tool(name: &str) -> Command {
    let variable = if name == "rustc" { "RUSTC" } else { "RUSTFMT" };
    if let Some(executable) = env::var_os(variable).filter(|value| !value.is_empty()) {
        return Command::new(executable);
    }
    if name == "rustfmt"
        && let Some(rustc) = env::var_os("RUSTC").filter(|value| !value.is_empty())
    {
        let rustc = PathBuf::from(rustc);
        if rustc.components().count() > 1 {
            return Command::new(rustc.with_file_name("rustfmt"));
        }
    }
    Command::new(name)
}

pub fn check_templates(root: &Path) -> Result<(), StepError> {
    let templates = collect_files(&root.join("scripts/templates"), Some("rs"))?;
    if templates.is_empty() {
        return Err(StepError::Input(format!(
            "no standalone Rust templates found in {}",
            root.join("scripts/templates").display()
        )));
    }
    let temp = tempfile::tempdir()
        .map_err(|source| io_error("create isolated template metadata directory", source))?;
    let mut format = rust_tool("rustfmt");
    format.arg("--check").args(&templates);
    run_command(format, "check design template formatting", root)?;
    for template in &templates {
        let source = read_text(template)?;
        if source.split('\n').next() != Some(CLASSIFICATION) {
            return Err(StepError::Input(format!(
                "{}: missing design-only classification header",
                template.display()
            )));
        }
        let crate_name = template.file_stem().and_then(|name| name.to_str()).ok_or_else(|| {
            StepError::Input(format!("{}: template filename is not UTF-8", template.display()))
        })?;
        let mut rustc = rust_tool("rustc");
        rustc
            .args([
                "--edition",
                "2024",
                "--crate-name",
                crate_name,
                "--crate-type",
                "lib",
                "--emit",
                "metadata",
                "--out-dir",
            ])
            .arg(temp.path())
            .arg(template);
        run_command(rustc, &format!("compile standalone template {}", template.display()), root)?;
    }
    report_stdout(format!(
        "Standalone design templates compile ({} files); project API compatibility not checked",
        templates.len()
    ))
}

fn has_legacy_dependency(text: &str) -> bool {
    text.match_indices("crate::").any(|(index, _)| {
        let rest = &text[index + "crate::".len()..];
        UPPER_LAYERS.iter().any(|layer| rest.starts_with(layer))
    })
}

pub fn check_firewall(root: &Path) -> Result<(), StepError> {
    let directory = root.join("src/kernel");
    let files = collect_files(&directory, None)?;
    let mut failures = Vec::new();
    for file in files {
        let text = read_text(&file)?;
        if has_legacy_dependency(&text) {
            failures
                .push(format!("{}: imports from legacy or upper-layer modules", file.display()));
        }
        for forbidden in FORBIDDEN_KERNEL {
            if text.contains(forbidden) {
                failures.push(format!("{}: forbidden pattern '{forbidden}'", file.display()));
            }
        }
    }
    reject_findings("FIREWALL BREACH: src/kernel/", failures)?;
    report_stdout("FIREWALL CLEAN: src/kernel/ has no legacy dependencies or forbidden patterns")
}

pub fn audit_compat(root: &Path) -> Result<(), StepError> {
    const SECTIONS: &[(&str, &[&str])] = &[
        ("Compatibility theorem constructors", &["assume_compat(", "reflexive_compat("]),
        ("Compatibility equality", &["compat_alpha_eq"]),
        ("Unchecked legacy certification", &["CTerm::certify("]),
    ];
    let mut files = collect_files(&root.join("src"), None)?;
    files.extend(collect_files(&root.join("tests"), None)?);
    files.sort();
    let contents = files
        .iter()
        .map(|file| read_text(file).map(|text| (file, text)))
        .collect::<Result<Vec<_>, _>>()?;
    for (title, patterns) in SECTIONS {
        report_stdout(format!("=== {title} ==="))?;
        for (file, text) in &contents {
            for (index, line) in text.lines().enumerate() {
                if patterns.iter().any(|pattern| line.contains(pattern)) {
                    report_stdout(format!("{}:{}:{line}", file.display(), index + 1))?;
                }
            }
        }
    }
    Ok(())
}
