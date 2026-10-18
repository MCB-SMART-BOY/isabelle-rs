use std::fs::{self, File};
use std::io::{self, Seek, Write};
use std::path::Path;

use flate2::{Compression, write::GzEncoder};
use tempfile::NamedTempFile;
use zip::{CompressionMethod, ZipWriter, write::SimpleFileOptions};

use crate::runner::{StepError, io_error, report_line};

const PLATFORMS: [&str; 3] = ["linux", "macos", "windows"];
const BINARIES: [&str; 2] = ["isabelle-rs", "isabelle-build"];
const EXECUTABLE_MODE: u32 = 0o755;
const DOCUMENT_MODE: u32 = 0o644;
const NOTICES: [(&str, &[u8]); 3] = [
    ("LICENSE", include_bytes!("../../../LICENSE")),
    ("NOTICE", include_bytes!("../../../NOTICE")),
    ("THIRD_PARTY_LICENSES", include_bytes!("../../../THIRD_PARTY_LICENSES")),
];

fn archive_name(platform: &str) -> String {
    let extension = if platform == "windows" { "zip" } else { "tar.gz" };
    format!("isabelle-rs-{platform}-x86_64.{extension}")
}

fn binary_name(binary: &str, platform: &str) -> String {
    if platform == "windows" { format!("{binary}.exe") } else { binary.into() }
}

fn require_artifacts(directory: &Path, platform: &str) -> Result<(), StepError> {
    let folder = directory.join(format!("isabelle-rs-{platform}-x86_64"));
    let metadata = fs::symlink_metadata(&folder).map_err(|source| {
        io_error(format!("inspect artifact directory {}", folder.display()), source)
    })?;
    if !metadata.is_dir() {
        return Err(StepError::Input(format!(
            "expected real artifact directory: {}",
            folder.display()
        )));
    }
    for binary in BINARIES {
        let path = folder.join(binary_name(binary, platform));
        let metadata = fs::symlink_metadata(&path).map_err(|source| {
            io_error(format!("inspect release binary {}", path.display()), source)
        })?;
        if !metadata.is_file() {
            return Err(StepError::Input(format!(
                "expected regular release binary: {}",
                path.display()
            )));
        }
    }
    let output = directory.join(archive_name(platform));
    match fs::symlink_metadata(&output) {
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(()),
        Err(error) => {
            Err(io_error(format!("inspect archive destination {}", output.display()), error))
        },
        Ok(_) => {
            Err(StepError::Input(format!("refusing to overwrite archive {}", output.display())))
        },
    }
}

fn write_tar(output: &mut File, directory: &Path, platform: &str) -> io::Result<()> {
    let encoder = GzEncoder::new(output, Compression::default());
    let mut archive = tar::Builder::new(encoder);
    let folder = format!("isabelle-rs-{platform}-x86_64");
    for binary in BINARIES {
        let path = directory.join(&folder).join(binary);
        let mut input = File::open(&path)?;
        let metadata = input.metadata()?;
        if !metadata.is_file() {
            return Err(io::Error::other("release input is not a regular file"));
        }
        let mut header = tar::Header::new_gnu();
        header.set_size(metadata.len());
        header.set_mode(EXECUTABLE_MODE);
        header.set_mtime(0);
        header.set_cksum();
        archive.append_data(&mut header, format!("{folder}/{binary}"), &mut input)?;
    }
    for (name, bytes) in NOTICES {
        let mut header = tar::Header::new_gnu();
        header.set_size(bytes.len() as u64);
        header.set_mode(DOCUMENT_MODE);
        header.set_mtime(0);
        header.set_cksum();
        archive.append_data(&mut header, format!("{folder}/{name}"), bytes)?;
    }
    archive.into_inner()?.finish()?.flush()
}

fn write_zip<W: Write + Seek>(output: W, directory: &Path) -> Result<(), zip::result::ZipError> {
    let folder = "isabelle-rs-windows-x86_64";
    let mut archive = ZipWriter::new(output);
    let options = SimpleFileOptions::default()
        .compression_method(CompressionMethod::Deflated)
        .unix_permissions(EXECUTABLE_MODE);
    for binary in BINARIES {
        let name = format!("{binary}.exe");
        let mut input = File::open(directory.join(folder).join(&name))?;
        if !input.metadata()?.is_file() {
            return Err(io::Error::other("release input is not a regular file").into());
        }
        archive.start_file(format!("{folder}/{name}"), options)?;
        io::copy(&mut input, &mut archive)?;
    }
    for (name, bytes) in NOTICES {
        archive.start_file(format!("{folder}/{name}"), options.unix_permissions(DOCUMENT_MODE))?;
        archive.write_all(bytes)?;
    }
    archive.finish()?.flush()?;
    Ok(())
}

fn create_archive(directory: &Path, platform: &str) -> Result<(), StepError> {
    let path = directory.join(archive_name(platform));
    let operation = || format!("create release archive {}", path.display());
    let mut output =
        NamedTempFile::new_in(directory).map_err(|source| io_error(operation(), source))?;
    if platform == "windows" {
        write_zip(output.as_file_mut(), directory)
            .map_err(|source| io_error(operation(), io::Error::other(source)))?;
    } else {
        write_tar(output.as_file_mut(), directory, platform)
            .map_err(|source| io_error(operation(), source))?;
    }
    output.as_file().sync_all().map_err(|source| io_error(operation(), source))?;
    output.persist_noclobber(&path).map_err(|source| io_error(operation(), source.error))?;
    report_line(format_args!("Created {}", path.display()))
}

pub fn create_archives(directory: &Path) -> Result<(), StepError> {
    for platform in PLATFORMS {
        require_artifacts(directory, platform)?;
    }
    for platform in PLATFORMS {
        create_archive(directory, platform)?;
    }
    Ok(())
}
