use isabelle_rs::ml::{DenyHost, MlError, MlErrorKind, Type, TypeScheme, Value, Vm};

fn evaluate(source: &str) -> Vm {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate("ml-text-basis.sml", source).expect("text basis program should evaluate");
    vm
}
fn integer(vm: &Vm, name: &str) -> i64 {
    vm.lookup_value(name).expect("running VM").and_then(Value::as_int).expect("integer result")
}
fn text<'a>(vm: &'a Vm, name: &str) -> &'a [u8] {
    vm.lookup_value(name).expect("running VM").and_then(Value::as_bytes).expect("string result")
}
fn boolean(vm: &Vm, name: &str) -> bool {
    vm.lookup_value(name).expect("running VM").and_then(Value::as_bool).expect("boolean result")
}

#[test]
fn text_bytes_at_255_are_not_utf8_codepoints() {
    let vm = evaluate(
        "val raw = String.str (Char.chr 255) ^ String.str (Char.chr 0); \
        val length = String.size raw; val first = Char.ord (String.nth raw 0); \
        val last = Char.ord (String.sub (raw, 1)); \
        val copied = String.implode (String.explode raw); \
        val prefix = String.isPrefix (String.str (Char.chr 255)) raw; \
        val negative = Char.ord ((Char.chr ~1) handle Chr => #\"x\"); \
        val beyond = (String.substring (raw, 1, 2)) handle Subscript => \"invalid\";",
    );
    assert_eq!(integer(&vm, "length"), 2);
    assert_eq!(integer(&vm, "first"), 255);
    assert_eq!(integer(&vm, "last"), 0);
    assert_eq!(text(&vm, "raw"), &[255, 0]);
    assert_eq!(text(&vm, "copied"), &[255, 0]);
    assert!(boolean(&vm, "prefix"));
    assert_eq!(integer(&vm, "negative"), 120);
    assert_eq!(text(&vm, "beyond"), b"invalid");
}

#[test]
fn substring_nested_slice_base_retains_original_bytes_and_offsets() {
    let vm = evaluate(
        "val source = \"a\" ^ String.str (Char.chr 255) ^ \"bcd\"; \
        val part = Substring.substring (source, 1, 4); \
        val nested = Substring.slice (part, 1, SOME 2); \
        val (original, offset, length) = Substring.base nested; \
        val contents = Substring.string nested; \
        val byte = Char.ord (Substring.sub (part, 0)); \
        val end_slice = Substring.slice (nested, 2, NONE); \
        val bad = (Substring.slice (nested, 3, NONE); false) handle Subscript => true;",
    );
    assert_eq!(text(&vm, "contents"), b"bc");
    assert_eq!(text(&vm, "original"), &[b'a', 255, b'b', b'c', b'd']);
    assert_eq!(integer(&vm, "offset"), 2);
    assert_eq!(integer(&vm, "length"), 2);
    assert_eq!(integer(&vm, "byte"), 255);
    assert!(boolean(&vm, "bad"));
    let source = vm.lookup_value("source").unwrap().unwrap();
    let original = vm.lookup_value("original").unwrap().unwrap();
    assert!(
        source.is_same_object(original),
        "base returns original string object rather than copied bytes"
    );
    let end = vm.lookup_value("end_slice").unwrap().unwrap();
    assert_eq!(end.as_tuple().unwrap()[2].as_int(), Some(0));
}

#[test]
fn substring_slice_keeps_original_alive_after_gc() {
    let mut vm = evaluate(
        "val retained = let val source = \"a\" ^ String.str (Char.chr 255) ^ \"z\" \
        in Substring.slice (Substring.full source, 1, SOME 1) end;",
    );
    vm.collect_garbage().expect("reachable substring remains live");
    vm.evaluate(
        "substring-after-gc.sml",
        "val (underlying, start, length) = Substring.base retained; \
         val content = Substring.string retained;",
    )
    .expect("substring remains readable after collection");
    assert_eq!(text(&vm, "underlying"), &[b'a', 255, b'z']);
    assert_eq!(text(&vm, "content"), &[255]);
    assert_eq!(integer(&vm, "start"), 1);
    assert_eq!(integer(&vm, "length"), 1);
}

#[test]
fn text_fields_tokens_and_empty_boundaries_produce_distinct_results() {
    let vm = evaluate(
        "val fields = String.fields (fn c => c = #\",\") \",a,,\"; \
        val tokens = String.tokens (fn c => c = #\",\") \",a,,\"; \
        val left = String.concatWith \"|\" fields; \
        val right = String.concatWith \"|\" tokens; \
        val empty_fields = String.fields (fn c => true) \"\"; \
        val empty_tokens = String.tokens (fn c => true) \"\"; \
        val empty_fields_length = List.length empty_fields; \
        val empty_tokens_length = List.length empty_tokens; \
        val chunks = Substring.fields (fn c => c = #\",\") (Substring.full \",a,,\"); \
        val chunk_strings = String.concatWith \"|\" (List.map Substring.string chunks); \
        val token_strings = Substring.concat (Substring.tokens (fn c => c = #\",\") (Substring.full \",a,,\")); \
        val empty = Substring.isEmpty (Substring.full \"\");",
    );
    assert_eq!(text(&vm, "left"), b"|a||");
    assert_eq!(text(&vm, "right"), b"a");
    assert_eq!(text(&vm, "chunk_strings"), b"|a||");
    assert_eq!(text(&vm, "token_strings"), b"a");
    assert_eq!(integer(&vm, "empty_fields_length"), 1);
    assert_eq!(integer(&vm, "empty_tokens_length"), 0);
    assert!(boolean(&vm, "empty"));
}

#[test]
fn text_callbacks_follow_byte_order_and_preserve_exceptions() {
    let vm = evaluate(
        "val seen = ref \"\"; \
        val mapped = String.translate (fn c => (seen := !seen ^ String.str c; String.str c ^ \"!\")) \"ab\"; \
        val order = !seen; \
        val reverse = String.fold_rev (fn c => fn s => s ^ String.str c) \"abc\" \"\"; \
        val threw = (String.map (fn c => if c = #\"b\" then raise Subscript else c) \"abc\"; false) \
            handle Subscript => true; \
        val has_later = String.exists (fn c => c = #\"b\") \"abc\";",
    );
    assert_eq!(text(&vm, "mapped"), b"a!b!");
    assert_eq!(text(&vm, "order"), b"ab");
    assert_eq!(text(&vm, "reverse"), b"cba");
    assert!(boolean(&vm, "threw"));
    assert!(boolean(&vm, "has_later"));
}

#[test]
fn text_escape_scan_and_comparisons_round_trip_bytes() {
    let vm = evaluate(
        "val original = String.str (Char.chr 255) ^ \"\\n\"; \
        val escaped = String.toString original; \
        val decoded = Option.valOf (String.fromString escaped); \
        val char_decoded = Char.ord (Option.valOf (Char.fromString \"\\\\255rest\")); \
        val c_encoded = Char.toCString #\"?\"; \
        val c_decoded = Char.ord (Option.valOf (Char.fromCString \"\\\\xFF\")); \
        val ctrl_encoded = Char.toString (Char.chr 0); \
        val read = fn n => if n = 0 then SOME (#\"z\", 1) else NONE; \
        val (scanned, consumed) = Option.valOf (Char.scan read 0); \
        val scanned_code = Char.ord scanned; \
        val smaller = String.compare (\"a\", \"b\") = LESS; \
        val sorted = Char.compare (#\"b\", #\"a\") = GREATER;",
    );
    assert_eq!(text(&vm, "escaped"), b"\\255\\n");
    assert_eq!(text(&vm, "decoded"), &[255, b'\n']);
    assert_eq!(integer(&vm, "char_decoded"), 255);
    assert_eq!(text(&vm, "c_encoded"), b"\\?");
    assert_eq!(integer(&vm, "c_decoded"), 255);
    assert_eq!(text(&vm, "ctrl_encoded"), b"\\^@");
    assert_eq!(integer(&vm, "consumed"), 1);
    assert_eq!(integer(&vm, "scanned_code"), 122);
    assert!(boolean(&vm, "smaller"));
    assert!(boolean(&vm, "sorted"));
}

#[test]
fn substring_byte_iteration_and_scan_preserve_order_and_prefixes() {
    let vm = evaluate(
        "val base = Substring.full \"zabc\"; \
        val part = Substring.slice (base, 1, SOME 3); \
        val (prefix, suffix) = Substring.position \"b\" part; \
        val left = Substring.string prefix; val right = Substring.string suffix; \
        val folded = Substring.foldr (fn (c, s) => s ^ String.str c) \"\" part; \
        val (head, tail) = Option.valOf (Substring.getc part); \
        val code = Char.ord head; val remainder = Substring.string tail; \
        val parsed = Option.valOf (String.fromString \"ab\\\\q\"); \
        val invalid_char = Option.isSome (Char.fromString (String.str (Char.chr 255))); \
        val read = fn n => if n = 0 then SOME (#\"a\", 1) else if n = 1 then SOME (#\"b\", 2) else NONE; \
        val (scanned, consumed) = Option.valOf (String.scan read 0);",
    );
    assert_eq!(text(&vm, "left"), b"a");
    assert_eq!(text(&vm, "right"), b"bc");
    assert_eq!(text(&vm, "folded"), b"cba");
    assert_eq!(integer(&vm, "code"), 97);
    assert_eq!(text(&vm, "remainder"), b"bc");
    assert_eq!(text(&vm, "parsed"), b"ab");
    assert!(!boolean(&vm, "invalid_char"));
    assert_eq!(text(&vm, "scanned"), b"ab");
    assert_eq!(integer(&vm, "consumed"), 2);
}

#[test]
fn char_fixed_polyml_boundaries_use_ascii_not_latin1_classification() {
    let vm = evaluate(
        "val limit_consistent = Char.maxOrd = Char.ord Char.maxChar; \
        val greatest = Char.ord (Char.chr Char.maxOrd); \
        val newline_print = Char.isPrint #\"\\n\"; \
        val newline_control = Char.isCntrl #\"\\n\"; \
        val high_control = Char.isCntrl (Char.chr 128); \
        val high_alpha = Char.isAlpha (Char.chr 255); \
        val high_lower = Char.ord (Char.toLower (Char.chr 192));",
    );
    assert!(boolean(&vm, "limit_consistent"));
    assert_eq!(integer(&vm, "greatest"), 255);
    assert!(!boolean(&vm, "newline_print"));
    assert!(boolean(&vm, "newline_control"));
    assert!(!boolean(&vm, "high_control"));
    assert!(!boolean(&vm, "high_alpha"));
    assert_eq!(integer(&vm, "high_lower"), 192);
}

#[test]
fn substring_span_accepts_overlaps_and_equal_distinct_bases() {
    let vm = evaluate(
        "val source = \"abc\"; \
        val overlap = Substring.string (Substring.span \
            (Substring.substring (source, 1, 1), Substring.substring (source, 0, 3))); \
        val a = String.str #\"a\"; val b = String.str #\"a\"; \
        val joined = Substring.span (Substring.full a, Substring.full b); \
        val equal_bases = Substring.string joined; \
        val differing = (Substring.span (Substring.full \"a\", Substring.full \"b\"); false) \
            handle General.Span => true;",
    );
    assert_eq!(text(&vm, "overlap"), b"bc");
    assert_eq!(text(&vm, "equal_bases"), b"a");
    assert!(boolean(&vm, "differing"));
    let base = vm.lookup_value("a").unwrap().unwrap();
    let joined = vm.lookup_value("joined").unwrap().unwrap();
    assert!(base.is_same_object(&joined.as_tuple().unwrap()[0]));
}

#[test]
fn string_scan_failed_candidate_preserves_entire_unread_suffix() {
    let vm = evaluate(
        "val newline = \"a\" ^ String.str (Char.chr 10) ^ \"b\"; \
        val illegal = \"a\" ^ String.str (Char.chr 92) ^ \"qb\"; \
        val (first, remaining1) = Option.valOf (String.scan Substring.getc (Substring.full newline)); \
        val (second, remaining2) = Option.valOf (String.scan Substring.getc (Substring.full illegal)); \
        val rest1 = Substring.string remaining1; val rest2 = Substring.string remaining2;",
    );
    assert_eq!(text(&vm, "first"), b"a");
    assert_eq!(text(&vm, "second"), b"a");
    assert_eq!(text(&vm, "rest1"), b"\nb");
    assert_eq!(text(&vm, "rest2"), b"\\qb");
}

#[test]
fn string_scan_valid_formatting_prefix_can_yield_empty_string() {
    let vm = evaluate(
        "val input = String.implode [Char.chr 92, #\" \", Char.chr 92, Char.chr 4]; \
        val converted = Option.valOf (String.fromString input); \
        val (scanned, remaining) = Option.valOf (String.scan Substring.getc (Substring.full input)); \
        val rest_code = Char.ord (Option.valOf (Substring.first remaining));",
    );
    assert_eq!(text(&vm, "converted"), b"");
    assert_eq!(text(&vm, "scanned"), b"");
    assert_eq!(integer(&vm, "rest_code"), 4);
}

#[test]
fn text_escapes_follow_fixed_polyml_sml_and_c_dialects() {
    let vm = evaluate(
        "val slash = String.str (Char.chr 92); \
        val sml = slash ^ \"u0041\"; val c_control = slash ^ \"^A\"; \
        val c_bad8 = Option.isSome (Char.fromCString (slash ^ \"8\")); \
        val c_bad9 = Option.isSome (String.fromCString (slash ^ \"9\")); \
        val raw_quote = Char.ord (Option.valOf (Char.fromCString (String.str (Char.chr 34)))); \
        val unicode_char = Char.ord (Option.valOf (Char.fromString sml)); \
        val unicode_string = Option.valOf (String.fromString sml); \
        val (scanned, tail) = Option.valOf (Char.scan Substring.getc (Substring.full sml)); \
        val scan_code = Char.ord scanned; val no_tail = Substring.isEmpty tail; \
        val c_control_code = Char.ord (Option.valOf (Char.fromCString c_control));",
    );
    assert!(!boolean(&vm, "c_bad8"));
    assert!(!boolean(&vm, "c_bad9"));
    assert_eq!(integer(&vm, "raw_quote"), 34);
    assert_eq!(integer(&vm, "unicode_char"), 65);
    assert_eq!(text(&vm, "unicode_string"), b"A");
    assert_eq!(integer(&vm, "scan_code"), 65);
    assert!(boolean(&vm, "no_tail"));
    assert_eq!(integer(&vm, "c_control_code"), 1);
}

#[test]
fn substring_negative_trim_raises_at_first_application() {
    let vm = evaluate(
        "val left = ((Substring.triml ~1; false) handle Subscript => true); \
        val right = ((Substring.trimr ~1; false) handle Subscript => true); \
        val clipped = Substring.string (Substring.triml 5 (Substring.full \"ab\"));",
    );
    assert!(boolean(&vm, "left"));
    assert!(boolean(&vm, "right"));
    assert_eq!(text(&vm, "clipped"), b"");
}

#[test]
fn substring_rejects_structural_tuple_impostors_during_type_check() {
    let mut vm = Vm::new(DenyHost);
    let error = vm
        .evaluate("substring-impostor.sml", "val fabricated = Substring.size (\"abc\", 0, 3);")
        .expect_err("nominal substring cannot be forged from a triple");
    assert_eq!(error.kind, MlErrorKind::Type);
}

fn stop_text_callback(vm: &mut Vm, _: &[Value]) -> Result<Value, MlError> {
    vm.request_stop();
    Ok(Value::bool(false))
}

#[test]
fn text_predicate_cancellation_cannot_be_caught_by_ml() {
    let mut vm = Vm::new(DenyHost);
    let char_type = Type::Constructor("char".to_owned(), vec![]);
    let bool_type = Type::Constructor("bool".to_owned(), vec![]);
    vm.register_native(
        "stop_text_callback",
        TypeScheme::mono(Type::Function(Box::new(char_type), Box::new(bool_type))),
        stop_text_callback,
    )
    .expect("native predicate registered");
    let error = vm
        .evaluate(
            "text-cancel.sml",
            "val result = (String.exists stop_text_callback \"abc\") handle _ => false;",
        )
        .expect_err("cancellation must abort String.exists despite ML handler");
    assert_eq!(error.kind, MlErrorKind::Stopped);
}

#[test]
fn text_comparison_shadowed_order_names_preserve_original_constructors() {
    let mut vm = evaluate(
        "val original_less = LESS; val original_equal = EQUAL; \
        datatype unrelated = LESS | EQUAL | GREATER;",
    );
    vm.collect_garbage().unwrap();
    vm.evaluate("shadowed-order.sml",
        "val compared = String.compare (\"a\", \"b\") = original_less; \
         val collated = String.collate (fn (a, b) => if a = b then original_equal else original_less) \
            (\"a\", \"b\") = original_less;").unwrap();
    assert!(boolean(&vm, "compared"));
    assert!(boolean(&vm, "collated"));
}

#[test]
fn text_interfaces_preserve_shared_types_and_ordering_operations() {
    let vm = evaluate(
        "structure S : STRING = String; structure C : CHAR = Char; \
        structure U : SUBSTRING = Substring; \
        val s : S.string = \"a\"; val c : S.char = C.chr 255; \
        val shared : C.string = S.^ (s, S.str c); \
        val part : U.substring = U.full shared; \
        val code = C.ord (S.sub (U.string part, 1)); \
        val ordered = S.< (\"\", s) andalso S.<= (s, s) andalso S.> (shared, s) andalso S.>= (s, s); \
        val characters = C.< (#\"a\", c) andalso C.<= (c, c) andalso C.> (c, #\"a\") andalso C.>= (c, c);",
    );
    assert_eq!(integer(&vm, "code"), 255);
    assert!(boolean(&vm, "ordered"));
    assert!(boolean(&vm, "characters"));
}

#[test]
fn substring_concat_with_preserves_empty_fields_and_slice_boundaries() {
    let vm = evaluate(
        "val a = Substring.substring (\"XabcY\", 1, 3); \
        val b = Substring.substring (\"pq\", 2, 0); \
        val c = Substring.substring (\"0de1\", 1, 2); \
        val joined = Substring.concatWith \":\" [a, b, c]; \
        val empty = Substring.concatWith \":\" []; \
        val singleton = Substring.concatWith \":\" [a]; \
        val plain = Substring.concat [a, b, c];",
    );
    assert_eq!(text(&vm, "joined"), b"abc::de");
    assert_eq!(text(&vm, "empty"), b"");
    assert_eq!(text(&vm, "singleton"), b"abc");
    assert_eq!(text(&vm, "plain"), b"abcde");
}

#[test]
fn text_opaque_signatures_conversions_preserve_global_string_types() {
    let vm = evaluate(
        r#"structure S :> STRING = String;
        structure C :> CHAR = Char;
        val parsed = Option.valOf (S.fromString "abc");
        val parsed_c = Option.valOf (S.fromCString "de");
        val sml : string = S.toString parsed;
        val c : string = S.toCString parsed_c;
        val character = Option.valOf (C.fromString "X");
        val character_c = Option.valOf (C.fromCString "Y");
        val char_sml : string = C.toString character;
        val char_c : string = C.toCString character_c;
        val code = C.ord character;"#,
    );
    assert_eq!(text(&vm, "sml"), b"abc");
    assert_eq!(text(&vm, "c"), b"de");
    assert_eq!(text(&vm, "char_sml"), b"X");
    assert_eq!(text(&vm, "char_c"), b"Y");
    assert_eq!(integer(&vm, "code"), 88);
}

#[test]
fn text_opaque_signatures_scan_accepts_global_char_reader() {
    let vm = evaluate(
        r#"structure S :> STRING = String;
        structure C :> CHAR = Char;
        val (scanned, rest) = Option.valOf (S.scan Substring.getc (Substring.full "abc"));
        val (character, tail) = Option.valOf (C.scan Substring.getc (Substring.full "Xy"));
        val result : string = S.toString scanned;
        val code = C.ord character;
        val remaining : string = Substring.string tail;
        val exhausted = Substring.isEmpty rest;"#,
    );
    assert_eq!(text(&vm, "result"), b"abc");
    assert_eq!(integer(&vm, "code"), 88);
    assert_eq!(text(&vm, "remaining"), b"y");
    assert!(boolean(&vm, "exhausted"));
}

#[test]
fn text_opaque_signatures_ordinary_members_reject_global_types() {
    for source in [
        r#"structure S :> STRING = String; val invalid = S.size "x";"#,
        r#"structure C :> CHAR = Char; val invalid = C.ord #"X";"#,
    ] {
        let mut vm = Vm::new(DenyHost);
        let error = vm
            .evaluate("opaque-text.sml", source)
            .expect_err("opaque ordinary members retain abstract parameter types");
        assert_eq!(error.kind, MlErrorKind::Type);
    }
}

#[test]
fn text_signatures_shadowed_names_preserve_captured_global_types() {
    let vm = evaluate(
        r#"structure Original = String;
        structure String = struct datatype string = Unrelated end;
        structure Char = struct datatype char = Unrelated end;
        structure S :> STRING = Original;
        val parsed = Option.valOf (S.fromString "abc");
        val result : string = S.toString parsed;
        val (scanned, rest) = Option.valOf (S.scan Substring.getc (Substring.full "de"));
        val scanned_result : string = S.toString scanned;"#,
    );
    assert_eq!(text(&vm, "result"), b"abc");
    assert_eq!(text(&vm, "scanned_result"), b"de");
}
