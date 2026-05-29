//! BNF/datatype tests — mutual datatypes and codatatypes.
#![allow(unused)]

#[cfg(test)]
mod bnf_tests {
    use isabelle_rs::hol::hol_loader::parse_datatypes;

    #[test]
    fn test_parse_mutual_datatype() {
        let src = r#"datatype even = Zero | Even_Suc odd
  and odd = Odd_Suc even"#;
        let defs = parse_datatypes(src);
        eprintln!("Parsed {} datatypes", defs.len());
        assert_eq!(defs.len(), 2, "Expected 2 mutual datatypes");
        assert!(defs.iter().any(|d| d.name == "even"));
        assert!(defs.iter().any(|d| d.name == "odd"));
    }

    #[test]
    fn test_parse_codatatype() {
        let src = r#"codatatype 'a stream = SCons 'a "'a stream""#;
        let defs = parse_datatypes(src);
        eprintln!("Parsed {} codatatypes", defs.len());
        assert_eq!(defs.len(), 1);
        assert!(defs[0].name.contains("stream"));
    }

    #[test]
    fn test_parse_datatype_with_args() {
        let src = r#"datatype 'a list = Nil | Cons 'a "'a list""#;
        let defs = parse_datatypes(src);
        assert_eq!(defs.len(), 1);
        assert_eq!(defs[0].constructors.len(), 2);
        // Nil has 0 args
        assert_eq!(defs[0].constructors[0].1.len(), 0);
        // Cons has 2 args
        assert_eq!(defs[0].constructors[1].1.len(), 2);
    }

    #[test]
    fn test_parse_old_rep_datatype() {
        let src = r#"old_rep_datatype "0 :: nat" Suc"#;
        let defs = parse_datatypes(src);
        eprintln!("Parsed {} old_rep_datatypes", defs.len());
        assert_eq!(defs.len(), 1);
    }
}
