use isabelle_rs::ml::{DenyHost, MlErrorKind, Value, Vm};

fn evaluate(source: &str) -> Vm {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate("bytes-contract.sml", source).expect("valid ML program should evaluate");
    vm
}

fn integer(vm: &Vm, name: &str) -> i64 {
    vm.lookup_value(name).expect("active VM").and_then(Value::as_int).expect("integer binding")
}

fn bytes<'a>(vm: &'a Vm, name: &str) -> &'a [u8] {
    vm.lookup_value(name).expect("active VM").and_then(Value::as_bytes).expect("string binding")
}

#[test]
fn byte_literals_boundaries_retain_single_bytes() {
    let vm = evaluate(
        r###"val zero = Char.ord #"\000";
        val ascii = Char.ord #"\127";
        val high = Char.ord #"\128";
        val maximum = Char.ord #"\255";
        val literal = "\000\127\128\255";
        val length = String.size literal;
        val first = Char.ord (String.sub (literal, 0));
        val last = Char.ord (String.sub (literal, 3));"###,
    );
    assert_eq!(
        [
            integer(&vm, "zero"),
            integer(&vm, "ascii"),
            integer(&vm, "high"),
            integer(&vm, "maximum")
        ],
        [0, 127, 128, 255]
    );
    assert_eq!(bytes(&vm, "literal"), &[0, 127, 128, 255]);
    assert_eq!(integer(&vm, "length"), 4);
    assert_eq!((integer(&vm, "first"), integer(&vm, "last")), (0, 255));
    assert_eq!(vm.lookup_value("literal").unwrap().and_then(Value::as_text), None);
}

#[test]
fn byte_string_operations_preserve_invalid_utf8() {
    let vm = evaluate(
        r###"val original = "\000\127\128\255";
        val roundtrip = String.implode (String.explode original);
        val appended = String.str (Char.chr 255) ^ String.str (Char.chr 128);
        val combined = String.concat [original, appended];
        val matches = (case String.str (Char.chr 255) of "\255" => true | _ => false);
        val equal = original = roundtrip;"###,
    );
    assert_eq!(bytes(&vm, "roundtrip"), &[0, 127, 128, 255]);
    assert_eq!(bytes(&vm, "appended"), &[255, 128]);
    assert_eq!(bytes(&vm, "combined"), &[0, 127, 128, 255, 255, 128]);
    assert_eq!(vm.lookup_value("matches").unwrap().and_then(Value::as_bool), Some(true));
    assert_eq!(vm.lookup_value("equal").unwrap().and_then(Value::as_bool), Some(true));
}

#[test]
fn byte_literal_unicode_source_uses_utf8_bytes() {
    let vm = evaluate(
        "val unicode = \"é\"; val length = String.size unicode; \
        val first = Char.ord (String.sub (unicode, 0)); \
        val second = Char.ord (String.sub (unicode, 1));",
    );
    assert_eq!(bytes(&vm, "unicode"), "é".as_bytes());
    assert_eq!(integer(&vm, "length"), 2);
    assert_eq!((integer(&vm, "first"), integer(&vm, "second")), (195, 169));
    assert_eq!(vm.lookup_value("unicode").unwrap().and_then(Value::as_text), Some("é"));
    assert_eq!(Value::text("é").as_bytes(), Some("é".as_bytes()));
    assert_eq!(Value::bytes(vec![255]).as_text(), None);
}

#[test]
fn byte_character_literals_reject_non_single_byte() {
    for literal in [r###"#"""###, r###"#"ab""###, r###"#"é""###, r###"#"\128x""###] {
        let mut vm = Vm::new(DenyHost);
        let error = vm
            .evaluate("invalid-char.sml", &format!("val invalid = {literal};"))
            .expect_err("character literal must contain one byte");
        assert_eq!(error.kind, MlErrorKind::Syntax, "{literal}");
    }
}

#[test]
fn byte_numeric_escapes_reject_out_of_range_and_non_decimal() {
    for literal in [r#""\256""#, r#""\12x""#, r#""\999""#] {
        let mut vm = Vm::new(DenyHost);
        let error = vm
            .evaluate("invalid-byte.sml", &format!("val invalid = {literal};"))
            .expect_err("numeric escape must be a byte expressed by three decimal digits");
        assert_eq!(error.kind, MlErrorKind::Syntax, "{literal}");
    }
}

#[test]
fn integer_literals_parse_both_i64_boundaries() {
    let vm = evaluate(
        "val positive = 9223372036854775807; \
        val negative = ~9223372036854775808; val minus_one = ~1; val zero = ~0;",
    );
    assert_eq!(integer(&vm, "positive"), i64::MAX);
    assert_eq!(integer(&vm, "negative"), i64::MIN);
    assert_eq!(integer(&vm, "minus_one"), -1);
    assert_eq!(integer(&vm, "zero"), 0);
}

#[test]
fn integer_literals_reject_both_i64_overflows() {
    for literal in ["9223372036854775808", "~9223372036854775809", "~18446744073709551616"] {
        let mut vm = Vm::new(DenyHost);
        let error = vm
            .evaluate("integer-overflow.sml", &format!("val invalid = {literal};"))
            .expect_err("integer literal outside i64 range must fail");
        assert_eq!(error.kind, MlErrorKind::Syntax, "{literal}");
        assert!(error.cause.contains("out of range"), "{literal}: {}", error.cause);
    }
}
