#[path = "native_thm_variables/support.rs"]
mod support;

fn main() -> Result<(), isabelle_kernel::KernelError> {
    let outcome = support::run_closure()?;
    assert!(outcome.root.get(outcome.schema.name()).is_none());
    assert_eq!(outcome.schema_owner.get(outcome.schema.name()), Some(&outcome.schema));
    println!("accepted generic {:?}: {:?}", outcome.schema.name(), outcome.schema.prop().term());
    for token in [&outcome.left.instance, &outcome.right.instance] {
        println!(
            "accepted {:?}: {:?}; dependencies={}",
            token.name(),
            token.prop().term(),
            token.dependencies().len()
        );
    }
    println!(
        "two type instances exported, composed, transferred, accepted, and referenced; \
         reused dependencies: left={}, right={}",
        outcome.left.reused.dependencies().len(),
        outcome.right.reused.dependencies().len(),
    );
    Ok(())
}
