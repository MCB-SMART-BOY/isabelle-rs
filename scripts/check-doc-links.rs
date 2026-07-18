use std::{
    env, fs,
    path::{Path, PathBuf},
};

fn collect_markdown(dir: &Path, files: &mut Vec<PathBuf>) -> std::io::Result<()> {
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        if path.is_dir() {
            let name = path.file_name().and_then(|name| name.to_str()).unwrap_or_default();
            if !matches!(name, ".git" | "target" | "isabelle-source") {
                collect_markdown(&path, files)?;
            }
        } else if path.extension().and_then(|ext| ext.to_str()) == Some("md") {
            files.push(path);
        }
    }
    Ok(())
}

fn link_targets(line: &str) -> impl Iterator<Item = &str> {
    let mut rest = line;
    std::iter::from_fn(move || {
        let start = rest.find("](")? + 2;
        rest = &rest[start..];
        let end = rest.find(')')?;
        let target = &rest[..end];
        rest = &rest[end + 1..];
        Some(target)
    })
}

fn local_target(raw: &str) -> Option<&str> {
    let target = raw.trim().trim_matches(['<', '>']);
    if target.is_empty()
        || target.starts_with('#')
        || target.contains("://")
        || target.starts_with("mailto:")
        || target.starts_with("app:")
        || target.starts_with("file:")
    {
        return None;
    }
    Some(target.split('#').next().unwrap_or(target))
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let root = env::args().nth(1).map(PathBuf::from).unwrap_or(env::current_dir()?);
    let mut files = Vec::new();
    collect_markdown(&root, &mut files)?;
    files.sort();

    let mut missing = Vec::new();
    for file in &files {
        let source = fs::read_to_string(file)?;
        for (line_index, line) in source.lines().enumerate() {
            for raw in link_targets(line) {
                let Some(target) = local_target(raw) else { continue };
                let path = if Path::new(target).is_absolute() {
                    PathBuf::from(target)
                } else {
                    file.parent().unwrap_or(&root).join(target)
                };
                if !path.exists() {
                    missing.push(format!("{}:{} -> {target}", file.display(), line_index + 1));
                }
            }
        }
    }

    if missing.is_empty() {
        println!("Markdown local links clean ({} files)", files.len());
        return Ok(());
    }

    for link in missing {
        eprintln!("missing: {link}");
    }
    Err("Markdown contains missing local links".into())
}
