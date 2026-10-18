#[path = "native_thm/support.rs"]
mod support;

fn main() -> Result<(), isabelle_kernel::KernelError> {
    let (accepted, reused) = support::run_closure()?;
    println!("accepted {:?}: {:?}", accepted.name(), accepted.prop().term());
    println!("basis=none; first dependencies={}", accepted.dependencies().len());
    println!(
        "reaccepted {:?}; theorem dependencies={}",
        reused.name(),
        reused.dependencies().len()
    );
    println!(
        "certification -> open derivation -> instantiate -> compose -> transfer -> accept -> reference: verified"
    );
    Ok(())
}
