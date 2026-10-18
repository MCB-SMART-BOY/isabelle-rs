use std::io;

fn main() -> io::Result<()> {
    let executable = std::env::current_exe()?;
    let directory = executable.parent().ok_or_else(|| io::Error::other("fixture executable has no parent"))?;
    std::fs::write(directory.join("pid"), std::process::id().to_string())?;
    io::stdin().read_line(&mut String::new())?;
    Ok(())
}
