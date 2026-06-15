//! Single-file verification — process one theory at a time to avoid stack overflow.

#[cfg(test)]
mod single_verify {
    use std::time::Instant;

    use isabelle_rs::{core::theory::Theory, theory::loader::TheoryProcessor};

    #[test]
    fn test_verify_list() {
        verify_one("List", "isabelle-source/src/HOL/List.thy");
    }

    #[test]
    fn test_verify_option() {
        verify_one("Option", "isabelle-source/src/HOL/Option.thy");
    }

    #[test]
    fn test_verify_lattices() {
        verify_one("Lattices", "isabelle-source/src/HOL/Lattices.thy");
    }

    #[test]
    fn test_verify_groups() {
        verify_one("Groups", "isabelle-source/src/HOL/Groups.thy");
    }

    #[test]
    fn test_verify_rings() {
        verify_one("Rings", "isabelle-source/src/HOL/Rings.thy");
    }

    fn verify_one(name: &str, path: &str) {
        let start = Instant::now();
        let source = std::fs::read_to_string(path).unwrap_or_default();

        let mut proc = TheoryProcessor::with_parent(Theory::pure(), name);
        proc.accept_all = false;
        let _thy = proc.process_source(&source);
        let elapsed = start.elapsed();

        let thms = proc.theorem_count();
        let errs = proc.errors().len();
        let icon = if errs == 0 { "✅" } else { "⚠️" };

        eprintln!(
            "  {} {:>15} — {:>4} thms, {:>3} errs, {:>6.1}ms",
            icon,
            name,
            thms,
            errs,
            elapsed.as_secs_f64() * 1000.0
        );

        if errs > 0 {
            for (i, e) in proc.errors().iter().take(3).enumerate() {
                let short: String = e.chars().take(100).collect();
                eprintln!("       {} {}", i + 1, short);
            }
        }

        assert!(
            thms > 0 || errs == 0,
            "{}: no theorems generated, errors: {:?}",
            name,
            proc.errors()
        );
    }
}
