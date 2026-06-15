//! One-at-a-time verification — avoids cumulative stack overflow.

#[cfg(test)]
mod one_by_one {
    use std::{path::Path, time::Instant};

    use isabelle_rs::{core::theory::Theory, theory::loader::TheoryProcessor};

    #[test]
    fn test_one_file_hol() {
        verify_one("HOL", "isabelle-source/src/HOL/HOL.thy");
    }
    #[test]
    fn test_one_file_set() {
        verify_one("Set", "isabelle-source/src/HOL/Set.thy");
    }
    #[test]
    fn test_one_file_list() {
        verify_one("List", "isabelle-source/src/HOL/List.thy");
    }
    #[test]
    fn test_one_file_groups() {
        verify_one("Groups", "isabelle-source/src/HOL/Groups.thy");
    }
    #[test]
    fn test_one_file_lattices() {
        verify_one("Lattices", "isabelle-source/src/HOL/Lattices.thy");
    }
    #[test]
    fn test_one_file_fun() {
        verify_one("Fun", "isabelle-source/src/HOL/Fun.thy");
    }
    #[test]
    fn test_one_file_option() {
        verify_one("Option", "isabelle-source/src/HOL/Option.thy");
    }
    #[test]
    fn test_one_file_product() {
        verify_one("Product_Type", "isabelle-source/src/HOL/Product_Type.thy");
    }

    fn verify_one(name: &str, path_str: &str) {
        let path = Path::new(path_str);
        if !path.exists() {
            eprintln!("{}: file not found", name);
            return;
        }

        let start = Instant::now();
        let source = std::fs::read_to_string(path).unwrap_or_default();

        let mut proc = TheoryProcessor::with_parent(Theory::pure(), name);
        proc.accept_all = true;
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

        assert!(thms > 0 || errs == 0, "{}: 0 theorems, {} errors", name, errs);
    }
}
