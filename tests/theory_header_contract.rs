use isabelle_rs::theory::thy_header::parse_header;

#[test]
fn parse_header_document_preamble_preserves_real_header_and_body_offset() {
    let source = concat!(
        "(* α *)\nchapter \"Intro\"\n",
        "section \\<open>Nested ‹theory Fake imports Wrong begin›\\<close>\n",
        "text ‹More \\<open>nested\\<close> documentation›\n",
        "theory Actual imports Pure begin\nend"
    );
    let header = parse_header(source).unwrap();
    assert_eq!(header.name, "Actual");
    assert_eq!(header.imports, ["Pure"]);
    assert_eq!(&source[header.body_begin_position..], "\nend");
}

#[test]
fn parse_header_unterminated_document_does_not_find_embedded_theory() {
    for preamble in ["section ‹", "section \\<open>", "section \""] {
        let source = format!("{preamble}theory Hidden imports Pure begin end");
        assert!(parse_header(&source).is_err(), "accepted {preamble:?}");
    }
}

#[test]
fn parse_header_malformed_document_symbol_is_rejected() {
    for text in [r"\<bad symbol>", r"\<>", r"\<open"] {
        let source = format!("section ‹{text}› theory Actual imports Pure begin end");
        assert!(parse_header(&source).is_err(), "accepted {text:?}");
    }
}

#[test]
fn parse_header_non_document_preamble_is_rejected() {
    for preamble in ["ML ‹()›", "lemma hidden: True", "section", "unknown ‹text›"] {
        let source = format!("{preamble}\ntheory Actual imports Pure begin end");
        assert!(parse_header(&source).is_err(), "accepted {preamble:?}");
    }
}

#[test]
fn parse_header_document_preamble_retains_header_declarations() {
    let source = "section ‹Intro› theory Actual imports Pure keywords \"custom\" :: thy_decl begin";
    let header = parse_header(source).unwrap();
    assert_eq!(header.keywords[0].name, "custom");
    assert_eq!(header.keywords[0].kind, "thy_decl");
}
