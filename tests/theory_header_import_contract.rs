use isabelle_rs::theory::thy_header::parse_header;

#[test]
fn parse_header_quoted_import_paths_preserves_order_and_full_names() {
    let source = r#"theory Child imports "../Parent" HOL.List "directory/With-Hyphen" begin end"#;
    let header = parse_header(source).unwrap();
    assert_eq!(header.imports, ["../Parent", "HOL.List", "directory/With-Hyphen"]);
    assert_eq!(&source[header.body_begin_position..], " end");
}

#[test]
fn parse_header_quoted_keyword_import_is_not_a_header_delimiter() {
    let header = parse_header(r#"theory Child imports "begin" "keywords" Pure begin end"#).unwrap();
    assert_eq!(header.imports, ["begin", "keywords", "Pure"]);
}

#[test]
fn parse_header_unterminated_quoted_import_rejects() {
    assert!(parse_header(r#"theory Child imports "Parent begin"#).is_err());
}
