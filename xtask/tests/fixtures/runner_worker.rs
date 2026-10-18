use std::io;
use std::path::PathBuf;
use std::process::ExitCode;

#[cfg(unix)]
unsafe extern "C" {
    fn raise(signal: std::ffi::c_int) -> std::ffi::c_int;
}

fn main() -> io::Result<ExitCode> {
    let arguments: Vec<_> = std::env::args_os().skip(1).collect();
    match arguments.first().and_then(|argument| argument.to_str()) {
        Some("exit") => Ok(ExitCode::from(17)),
        #[cfg(unix)]
        Some("signal") => {
            const SIGTERM: std::ffi::c_int = 15;
            // Fixed test-only signal to this process; no pointers or external input.
            unsafe { raise(SIGTERM); }
            Err(io::Error::other("SIGTERM did not terminate fixture"))
        },
        Some("touch") => { std::fs::write(PathBuf::from(&arguments[1]), [])?; Ok(ExitCode::SUCCESS) },
        Some("fail") => { std::fs::write(PathBuf::from(&arguments[1]), [])?; Ok(ExitCode::from(29)) },
        Some("copy") => {
            std::fs::copy(PathBuf::from(&arguments[1]), PathBuf::from(&arguments[2]))?;
            Ok(ExitCode::SUCCESS)
        },
        Some("wait") => {
            std::fs::write(PathBuf::from(&arguments[1]), [])?;
            io::stdin().read_line(&mut String::new())?;
            Ok(ExitCode::SUCCESS)
        },
        _ => Err(io::Error::new(io::ErrorKind::InvalidInput, "unknown runner fixture mode")),
    }
}
