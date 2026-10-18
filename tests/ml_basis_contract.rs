use isabelle_rs::ml::{DenyHost, MlError, MlErrorKind, Type, TypeScheme, Value, Vm};

fn evaluate(source: &str) -> Vm {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate("basis-contract.sml", source).expect("valid ML program should evaluate");
    vm
}

fn integer(vm: &Vm, name: &str) -> i64 {
    vm.lookup_value(name).expect("active VM").and_then(Value::as_int).expect("integer binding")
}

fn boolean(vm: &Vm, name: &str) -> bool {
    vm.lookup_value(name).expect("active VM").and_then(Value::as_bool).expect("boolean binding")
}

#[test]
fn thread_exception_qualified_alias_preserves_handler_identity() {
    let vm = evaluate(
        "exception ThreadFailure = Thread.Thread; \
         val message = (raise ThreadFailure \"failed\") handle Thread.Thread text => text;",
    );
    assert_eq!(vm.lookup_value("message").unwrap().and_then(Value::as_text), Some("failed"));
}

#[test]
fn polyml_trace_exception_invokes_reporter_only_for_ml_exception_and_preserves_identity() {
    let vm = evaluate(
        "exception Probe; \
         val calls = ref 0; \
         val successful = PolyML.Exception.traceException \
             (fn () => 42, fn _ => (calls := !calls + 1; 0)); \
         val caught = (PolyML.Exception.traceException \
             (fn () => raise Probe, fn (trace, exn) => \
                 (calls := !calls + 1; raise exn)); false) handle Probe => true; \
         val reports = !calls;",
    );
    assert_eq!(integer(&vm, "successful"), 42);
    assert!(boolean(&vm, "caught"));
    assert_eq!(integer(&vm, "reports"), 1);
}

#[test]
fn polyml_pointer_eq_distinguishes_shared_objects_and_sml90_aliases() {
    let vm = evaluate(
        "val shared = ref 1; val other = ref 1; \
         val same = PolyML.pointerEq (shared, shared); \
         val distinct = PolyML.pointerEq (shared, other); \
         val immediate = PolyML.pointerEq (1, 1); \
         val ord_value = SML90.ord \"A\"; \
         val chr_value = SML90.chr 66 = \"B\"; \
         val exploded = SML90.explode \"ab\" = [\"a\", \"b\"];",
    );
    assert!(boolean(&vm, "same"));
    assert!(!boolean(&vm, "distinct"));
    assert!(boolean(&vm, "immediate"));
    assert_eq!(integer(&vm, "ord_value"), 65);
    assert!(boolean(&vm, "chr_value"));
    assert!(boolean(&vm, "exploded"));
}

#[test]
fn basis_real_and_word_literals_preserve_types_and_equality_rules() {
    let mut vm = evaluate(
        "val fraction = 0.125; val exponent = 1.25E~2; \
        val word = 0wxFF; val selected = case word of 0wxFF => 7 | _ => 0;",
    );
    assert_eq!(vm.lookup_value("fraction").unwrap().and_then(Value::as_real), Some(0.125));
    assert_eq!(vm.lookup_value("exponent").unwrap().and_then(Value::as_real), Some(0.0125));
    assert_eq!(vm.lookup_value("word").unwrap().and_then(Value::as_word), Some(255));
    assert_eq!(integer(&vm, "selected"), 7);
    let error = vm.evaluate("invalid-real-equality.sml", "val invalid = 0.0 = 0.0;").unwrap_err();
    assert_eq!(error.kind, MlErrorKind::Type);
}

#[test]
fn word_basis_bitsets_wrap_shift_and_report_conversion_overflow() {
    let vm = evaluate(
        "val combined = Word.orb (Word.<< (0w1, 0w63), 0w3); \
        val high = Word.andb (combined, Word.notb 0w3); \
        val low = Word.>> (combined, 0w63); \
        val shifted_out = Word.<< (0w1, 0w64); \
        val overflow = (Word.toInt high; 0) handle Overflow => 1;",
    );
    assert_eq!(vm.lookup_value("high").unwrap().and_then(Value::as_word), Some(1 << 63));
    assert_eq!(vm.lookup_value("low").unwrap().and_then(Value::as_word), Some(1));
    assert_eq!(vm.lookup_value("shifted_out").unwrap().and_then(Value::as_word), Some(0));
    assert_eq!(integer(&vm, "overflow"), 1);
}

#[test]
fn word_qualified_type_alias_matches_machine_word_not_word32() {
    let mut vm = evaluate("val flags: Word.word = 0w7; val copied: word = flags;");
    assert_eq!(vm.lookup_value("copied").unwrap().and_then(Value::as_word), Some(7));
    assert_eq!(
        vm.evaluate("word-width.sml", "val wrong: Word32.word = flags;").unwrap_err().kind,
        MlErrorKind::Type,
    );
}

#[cfg(unix)]
#[test]
fn os_path_from_string_preserves_unix_empty_arcs_and_root() {
    let vm = evaluate(
        "val {isAbs = absolute, vol = volume, arcs = pieces} = OS.Path.fromString \"/a//b/\"; \
         val root = OS.Path.fromString \"/\"; \
         val empty = OS.Path.fromString \"\"; \
         val valid = absolute andalso volume = \"\" andalso pieces = [\"a\", \"\", \"b\", \"\"] \
            andalso #arcs root = [\"\"] andalso #isAbs root \
            andalso #arcs empty = [] andalso not (#isAbs empty);",
    );
    assert!(boolean(&vm, "valid"));
}

#[cfg(unix)]
#[test]
fn os_path_concat_preserves_relative_arcs_and_rejects_absolute_rhs() {
    let vm = evaluate(
        "val trailing = OS.Path.concat (\"a//\", \"b\") = \"a//b\"; \
         val relative = OS.Path.concat (\"a/b\", \"../c\") = \"a/b/../c\"; \
         val root = OS.Path.concat (\"/\", \"x\") = \"/x\"; \
         val empty = OS.Path.concat (\"a/\", \"\") = \"a\"; \
         val rejected = (OS.Path.concat (\"a\", \"/b\"); false) handle OS.Path.Path => true;",
    );
    assert!(boolean(&vm, "trailing"));
    assert!(boolean(&vm, "relative"));
    assert!(boolean(&vm, "root"));
    assert!(boolean(&vm, "empty"));
    assert!(boolean(&vm, "rejected"));
}

#[test]
fn word32_contextual_literals_are_distinct_and_wrap_at_32_bits() {
    let mut vm = evaluate(
        "val upper: Word32.word = 0wxFFFFFFFF; \
        val low = Word32.andb (upper, 0wxF); \
        val rolled = Word32.<< (0w1, 0w31); \
        val shifted = Word32.>> (rolled, 0w31); \
        val sum = Word32.+ (upper, 0w2); \
        val selected = case low of 0wxF => true | _ => false;",
    );
    assert_eq!(vm.lookup_value("upper").unwrap().and_then(Value::as_word32), Some(u32::MAX));
    assert_eq!(vm.lookup_value("rolled").unwrap().and_then(Value::as_word32), Some(1 << 31));
    assert_eq!(vm.lookup_value("shifted").unwrap().and_then(Value::as_word32), Some(1));
    assert_eq!(vm.lookup_value("sum").unwrap().and_then(Value::as_word32), Some(1));
    assert!(boolean(&vm, "selected"));
    assert_eq!(
        vm.evaluate("word32-overflow.sml", "val bad: Word32.word = 0wx100000000;")
            .unwrap_err()
            .kind,
        MlErrorKind::Type
    );
    assert_eq!(
        vm.evaluate("word32-mixed.sml", "val bad = Word32.andb (0w1, Word.fromInt 1);")
            .unwrap_err()
            .kind,
        MlErrorKind::Type
    );
}

#[test]
fn word32_local_literal_inferred_from_later_body_expression() {
    let vm = evaluate(
        "fun compute () = let val k = 0wxFFFFFFFF in Word32.+ (k, 0w2) end; \
        val result = compute ();",
    );
    assert_eq!(vm.lookup_value("result").unwrap().and_then(Value::as_word32), Some(1));
}

#[test]
fn basis_overloaded_numeric_real_word_and_ordering_match_operand_types() {
    let mut vm = evaluate(
        "val int_sum = 2 + 3; val real_sum = 1.25 + 0.5; \
        val word_sum = 0w2 + 0w3; val word32_sum: Word32.word = (0w2: Word32.word) + 0w3; \
        val real_negative = ~ real_sum; val ordered = (real_sum > 1.0) andalso (word_sum < 0w6);",
    );
    assert_eq!(integer(&vm, "int_sum"), 5);
    assert_eq!(vm.lookup_value("real_sum").unwrap().and_then(Value::as_real), Some(1.75));
    assert_eq!(vm.lookup_value("word_sum").unwrap().and_then(Value::as_word), Some(5));
    assert_eq!(vm.lookup_value("word32_sum").unwrap().and_then(Value::as_word32), Some(5));
    assert_eq!(vm.lookup_value("real_negative").unwrap().and_then(Value::as_real), Some(-1.75));
    assert!(boolean(&vm, "ordered"));
    assert_eq!(
        vm.evaluate("bad-numeric.sml", "val bad = \"a\" + \"b\";").unwrap_err().kind,
        MlErrorKind::Type
    );
}

#[test]
fn basis_real_formatter_and_int_conversion_preserve_standard_sign_and_precision() {
    let vm = evaluate(
        "val negative = Int.toString (~12); \
        val rounded = Real.fmt (StringCvt.FIX (SOME 2)) 1.234; \
        val generic = Real.fmt (StringCvt.GEN NONE) 3.0; \
        val exact = Real.fmt StringCvt.EXACT 0.5; \
        val converted = real 2 + 0.5;",
    );
    assert_eq!(vm.lookup_value("negative").unwrap().and_then(Value::as_text), Some("~12"));
    assert_eq!(vm.lookup_value("rounded").unwrap().and_then(Value::as_text), Some("1.23"));
    assert_eq!(vm.lookup_value("generic").unwrap().and_then(Value::as_text), Some("3.0"));
    assert_eq!(vm.lookup_value("exact").unwrap().and_then(Value::as_text), Some("0.5"));
    assert_eq!(vm.lookup_value("converted").unwrap().and_then(Value::as_real), Some(2.5));
}

#[test]
fn basis_option_polymorphic_constructors_and_exception_identity() {
    let vm = evaluate(
        "val first = Option.valOf (SOME 11); \
        val second = Option.getOpt (NONE, true); \
        val present = Option.isSome (SOME \"x\"); \
        val absent = Option.isSome NONE; \
        val third = (Option.valOf NONE) handle Option.Option => 23; \
        val different = (Option.valOf NONE) handle Subscript => 0 | Option.Option => 29;",
    );
    assert_eq!(integer(&vm, "first"), 11);
    assert!(boolean(&vm, "second"));
    assert!(boolean(&vm, "present"));
    assert!(!boolean(&vm, "absent"));
    assert_eq!(integer(&vm, "third"), 23);
    assert_eq!(integer(&vm, "different"), 29);
}

#[test]
fn basis_list_cons_fold_and_callback_order_compute_results() {
    let vm = evaluate(
        "val values = 1 :: 2 :: nil; \
        val appended = values @ [3]; \
        val sum = List.foldl (fn (x, n) => x + n) 0 appended; \
        val order = List.foldr (fn (x, n) => 10 * n + x) 0 appended; \
        val mapped = List.map (fn n => n + 4) values; \
        val selected = List.nth (mapped, 1);",
    );
    assert_eq!(integer(&vm, "sum"), 6);
    assert_eq!(integer(&vm, "order"), 321);
    assert_eq!(integer(&vm, "selected"), 6);
}

#[test]
fn basis_string_char_and_composition_compute_results() {
    let vm = evaluate(
        "val content = \"ab\" ^ String.str #\"c\"; \
        val size = String.size content; \
        val letter = Char.ord (String.sub (content, 1)); \
        val copied = String.implode (String.explode content); \
        val combined = String.concat [content, copied]; \
        val result = (not o not) true;",
    );
    assert_eq!(integer(&vm, "size"), 3);
    assert_eq!(integer(&vm, "letter"), 98);
    assert_eq!(vm.lookup_value("combined").unwrap().and_then(Value::as_text), Some("abcabc"));
    assert!(boolean(&vm, "result"));
}

#[test]
fn basis_vector_empty_negative_and_out_of_bounds_raise_subscript() {
    let vm = evaluate(
        "val empty = Vector.length (Vector.fromList []); \
        val negative = (Vector.sub (Vector.fromList [1], ~1)) handle Subscript => 31; \
        val edge = (Vector.sub (Vector.fromList [1], 1)) handle General.Subscript => 37; \
        val string_edge = (Char.ord (String.sub (\"\", 0))) handle Subscript => 41; \
        val any_empty = Vector.exists (fn n => n = 0) (Vector.fromList []); \
        val all_empty = Vector.all (fn n => n = 0) (Vector.fromList []);",
    );
    assert_eq!(integer(&vm, "empty"), 0);
    assert_eq!(integer(&vm, "negative"), 31);
    assert_eq!(integer(&vm, "edge"), 37);
    assert_eq!(integer(&vm, "string_edge"), 41);
    assert!(!boolean(&vm, "any_empty"));
    assert!(boolean(&vm, "all_empty"));
}

#[test]
fn basis_vector_tabulate_fold_and_predicate_compute_results() {
    let vm = evaluate(
        "val vec = Vector.tabulate (3, fn i => i + 1); \
        val order = Vector.foldl (fn (x, n) => 10 * n + x) 0 vec; \
        val reverse = Vector.foldr (fn (x, n) => 10 * n + x) 0 vec; \
        val any = Vector.exists (fn n => n = 2) vec; \
        val all = Vector.all (fn n => not (n = 0)) vec;",
    );
    assert_eq!(integer(&vm, "order"), 123);
    assert_eq!(integer(&vm, "reverse"), 321);
    assert!(boolean(&vm, "any"));
    assert!(boolean(&vm, "all"));
}

#[test]
fn basis_array_alias_updates_and_iteration_observe_current_values() {
    let vm = evaluate(
        "val arr = Array.fromList [1, 2]; val alias = arr; \
        val _ = Array.update (alias, 1, 9); \
        val prior_value = Array.sub (arr, 1); \
        val ordered = Array.foldl (fn (value, n) => \
          (if value = 1 then Array.update (arr, 1, 7) else (); n + value)) 0 arr; \
        val updated_value = Array.sub (alias, 1); \
        val same = arr = alias; val different = arr = Array.fromList [1, 7];",
    );
    assert_eq!(integer(&vm, "prior_value"), 9);
    assert_eq!(integer(&vm, "ordered"), 8);
    assert_eq!(integer(&vm, "updated_value"), 7);
    assert!(boolean(&vm, "same"));
    assert!(!boolean(&vm, "different"));
}

#[test]
fn array_curried_nth_and_upd_share_array_storage() {
    let vm = evaluate(
        "val array = Array.fromList [4, 5]; \
        val _ = Array.upd array 1 9; \
        val result = Array.nth array 1;",
    );
    assert_eq!(integer(&vm, "result"), 9);
}

#[test]
fn basis_array_size_and_subscript_exceptions_remain_distinct() {
    let vm = evaluate(
        "val invalid_size = (Array.length (Array.array (~1, 0))) handle Size => 47; \
        val invalid_index = (Array.sub (Array.fromList [], 0)) handle Subscript => 53; \
        val invalid_chr = (Char.ord (Char.chr 256)) handle Char.Chr => 59;",
    );
    assert_eq!(integer(&vm, "invalid_size"), 47);
    assert_eq!(integer(&vm, "invalid_index"), 53);
    assert_eq!(integer(&vm, "invalid_chr"), 59);
}

#[test]
fn basis_polymorphic_vector_accepts_distinct_element_types() {
    let vm = evaluate(
        "fun make x = Vector.fromList [x]; \
        val integer_item = Vector.sub (make 17, 0); \
        val bool_item = Vector.sub (make true, 0);",
    );
    assert_eq!(integer(&vm, "integer_item"), 17);
    assert!(boolean(&vm, "bool_item"));
}

#[test]
fn basis_array_value_restriction_rejects_reused_element_type() {
    let mut vm = evaluate(
        "val arr = Array.fromList []; val _ = Array.update (arr, 0, 1) handle Subscript => ();",
    );
    let error = vm
        .evaluate("basis-invalid.sml", "val _ = Array.update (arr, 0, true);")
        .expect_err("array element type cannot generalize across declarations");
    assert_eq!(error.kind, MlErrorKind::Type);
}

#[test]
fn basis_vector_of_functions_rejects_equality_but_array_compares_identity() {
    let mut vm = Vm::new(DenyHost);
    let error = vm
        .evaluate(
            "basis-invalid-equality.sml",
            "val result = Vector.fromList [fn x => x] = Vector.fromList [fn x => x];",
        )
        .expect_err("vector equality requires equality element type");
    assert_eq!(error.kind, MlErrorKind::Type);
    vm.evaluate(
        "basis-valid-equality.sml",
        "val arr = Array.fromList [fn x => x]; val same = arr = arr;",
    )
    .expect("array equality compares references regardless of element type");
    assert!(boolean(&vm, "same"));
}

fn stop_at_two(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let index = args[0].as_int().expect("native callback receives an int");
    if index == 2 {
        vm.request_stop();
    }
    Ok(Value::int(index))
}

#[test]
fn basis_vector_tabulate_stop_cannot_be_caught_by_ml() {
    let mut vm = Vm::new(DenyHost);
    vm.register_native(
        "stop_at_two",
        TypeScheme::mono(Type::Function(
            Box::new(Type::Constructor("int".to_owned(), vec![])),
            Box::new(Type::Constructor("int".to_owned(), vec![])),
        )),
        stop_at_two,
    )
    .expect("native callback can be registered");
    let error = vm
        .evaluate(
            "basis-stop.sml",
            "val result = (Vector.length (Vector.tabulate (5, stop_at_two))) handle _ => 99;",
        )
        .expect_err("supervisor stop must abort callback traversal");
    assert_eq!(error.kind, MlErrorKind::Stopped);
}

#[test]
fn polyml_trace_exception_never_reports_supervisor_stop_as_ml_exception() {
    let mut vm = Vm::new(DenyHost);
    vm.register_native(
        "stop_at_two",
        TypeScheme::mono(Type::Function(
            Box::new(Type::Constructor("int".to_owned(), vec![])),
            Box::new(Type::Constructor("int".to_owned(), vec![])),
        )),
        stop_at_two,
    )
    .expect("native callback can be registered");
    let error = vm
        .evaluate(
            "trace-stop.sml",
            "val result = PolyML.Exception.traceException \
            (fn () => stop_at_two 2, fn _ => 99);",
        )
        .expect_err("supervisor stop must bypass the exception reporter");
    assert_eq!(error.kind, MlErrorKind::Stopped);
}

#[test]
fn universal_tags_keep_values_separate_and_reject_unapproved_casts() {
    let mut vm = evaluate(
        "val first: int Universal.tag = Universal.tag (); \
        val second: int Universal.tag = Universal.tag (); \
        val _ = Thread.Thread.setLocal (first, 7); \
        val is_found = Thread.Thread.getLocal first = SOME 7; \
        val is_absent = Thread.Thread.getLocal second = NONE;",
    );
    assert!(boolean(&vm, "is_found"));
    assert!(boolean(&vm, "is_absent"));
    let error = vm
        .evaluate("unsafe-cast.sml", "val forged: word = RunCall.unsafeCast (ref 1);")
        .unwrap_err();
    assert_eq!(error.kind, MlErrorKind::Type);
}

#[test]
fn thread_flags_preserve_original_word_field_and_reject_other_offsets() {
    let mut vm = evaluate(
        "val _ = RunCall.storeWord \
        (RunCall.unsafeCast (Thread.Thread.self ()), 0w1, 0w5); \
        val flags: word = RunCall.loadWord \
        (RunCall.unsafeCast (Thread.Thread.self ()), 0w1);",
    );
    assert_eq!(vm.lookup_value("flags").unwrap().and_then(Value::as_word), Some(5));
    let error = vm.evaluate("thread-foreign-offset.sml",
        "val outside: word = RunCall.loadWord (RunCall.unsafeCast (Thread.Thread.self ()), 0w2);")
        .unwrap_err();
    assert_eq!(error.kind, MlErrorKind::HostPermission);
}

#[test]
fn standard_general_list_text_and_inequality_bindings_preserve_basis_behavior() {
    let mut vm = evaluate(
        "val mapped = map (fn n => n + 1) [1, 2, 3]; \
        val total = foldl (fn (n, acc) => n + acc) 0 mapped; \
        val chars = explode (implode [chr 65, chr 66]); \
        val unequal = (hd mapped <> 1) andalso (ord (hd chars) = 65); \
        val same = (mapped <> [2, 3, 4]);",
    );
    assert_eq!(integer(&vm, "total"), 9);
    assert!(boolean(&vm, "unequal"));
    assert!(!boolean(&vm, "same"));
    let error = vm
        .evaluate("equality-on-function.sml", "val invalid = (fn n => n) <> (fn n => n);")
        .unwrap_err();
    assert_eq!(error.kind, MlErrorKind::Type);
}

#[test]
fn thread_mutex_enforces_ownership_without_leaking_lock_state() {
    let mut vm = evaluate(
        "val gate = Thread.Mutex.mutex (); \
        val first = Thread.Mutex.trylock gate; \
        val blocked = Thread.Mutex.trylock gate; \
        val _ = Thread.Mutex.unlock gate; \
        val second = Thread.Mutex.trylock gate; \
        val _ = Thread.Mutex.unlock gate;",
    );
    assert!(boolean(&vm, "first"));
    assert!(!boolean(&vm, "blocked"));
    assert!(boolean(&vm, "second"));
    let error = vm.evaluate("unheld-mutex.sml", "val _ = Thread.Mutex.unlock gate;").unwrap_err();
    assert_eq!(error.kind, MlErrorKind::Type);
}

#[test]
fn real_to_int_rounding_uses_standard_even_ties_and_checks_range() {
    let vm = evaluate(
        "val rounded = Real.round 2.5; \
        val rounded_negative = round (~2.5); \
        val bottom = Real.floor (~2.1); \
        val overflow = (Real.floor 1.0E300; false) handle Overflow => true;",
    );
    assert_eq!(integer(&vm, "rounded"), 2);
    assert_eq!(integer(&vm, "rounded_negative"), -2);
    assert_eq!(integer(&vm, "bottom"), -3);
    assert!(boolean(&vm, "overflow"));
}

#[test]
fn time_string_rounds_real_seconds_to_millisecond_precision() {
    let vm = evaluate(
        "val positive = Time.toString (Time.fromReal 1.8); \
        val negative = Time.toString (Time.fromReal (~0.0008));",
    );
    assert_eq!(vm.lookup_value("positive").unwrap().and_then(Value::as_text), Some("1.800"));
    assert_eq!(vm.lookup_value("negative").unwrap().and_then(Value::as_text), Some("~0.001"));
}

#[test]
fn basis_before_and_sml90_strings_preserve_effect_order_and_characters() {
    let vm = evaluate(
        "val seen = ref 0; \
         val prior = (seen := 1; 11) before (seen := 2); \
         val current = !seen; \
         val strings = SML90.explode \"ab\" = [\"a\", \"b\"]; \
         val reconstructed = SML90.implode [\"a\", \"bc\"] = \"abc\"; \
         val ordinal = SML90.ord (SML90.chr 255); \
         val empty_ordinal = SML90.ord \"\" handle SML90.Ord => ~1; \
         val string_pattern = case \"abc\" of \"\" => 0 | \"abc\" => 7 | _ => 1; \
         val char_pattern = case #\"x\" of #\"x\" => true | _ => false;",
    );
    assert_eq!(integer(&vm, "prior"), 11);
    assert_eq!(integer(&vm, "current"), 2);
    assert!(boolean(&vm, "strings"));
    assert!(boolean(&vm, "reconstructed"));
    assert_eq!(integer(&vm, "ordinal"), 255);
    assert_eq!(integer(&vm, "empty_ordinal"), -1);
    assert_eq!(integer(&vm, "string_pattern"), 7);
    assert!(boolean(&vm, "char_pattern"));
}

#[test]
fn polyml_compiler_defers_effects_and_consumes_one_topdec_at_a_time() {
    let mut vm = evaluate(
        "val seen = ref 0; \
         val input = ref (String.explode \"val _ = seen := !seen + 1; val separate = 37;\"); \
         fun get () = case !input of [] => NONE | c :: rest => (input := rest; SOME c); \
         val first = PolyML.compiler (get, []); \
         val initial_count = !seen; val _ = first (); val compiled_count = !seen; \
         val second = PolyML.compiler (get, []); val _ = second ();",
    );
    assert_eq!(integer(&vm, "initial_count"), 0);
    assert_eq!(integer(&vm, "compiled_count"), 1);
    assert_eq!(integer(&vm, "separate"), 37);
    vm.evaluate("compiler-identity.sml", "val result = !seen;").unwrap();
    assert_eq!(integer(&vm, "result"), 1);
}

#[test]
fn polyml_compiler_syntax_error_is_a_catchable_fail_without_effects() {
    let vm = evaluate(
        "val seen = ref 0; \
         val input = ref (String.explode \"val _ = seen := !seen + 1; val broken = ;\"); \
         fun get () = case !input of [] => NONE | c :: rest => (input := rest; SOME c); \
         val first = PolyML.compiler (get, []); val _ = first (); \
         val failed = (PolyML.compiler (get, []); false) handle Fail _ => true; \
         val preserved = !seen;",
    );
    assert!(boolean(&vm, "failed"));
    assert_eq!(integer(&vm, "preserved"), 1);
}

#[test]
fn polyml_full_gc_clears_unreachable_weak_referents_and_preserves_live_values() {
    let mut vm = evaluate(
        "val live = ref 17; \
         val strong = Weak.weak (SOME live); \
         val discarded = let val token = ref 31 in Weak.weak (SOME token) end; \
         val was_present = case !discarded of SOME (ref 31) => true | _ => false;",
    );
    assert!(boolean(&vm, "was_present"));
    vm.evaluate(
        "full-gc.sml",
        "val _ = PolyML.fullGC (); \
         val cleared = !discarded = NONE; \
         val retained = !strong = SOME live andalso !live = 17;",
    )
    .expect("native full collection must actually update weak references");
    assert!(boolean(&vm, "cleared"));
    assert!(boolean(&vm, "retained"));
}

#[test]
fn polyml_full_gc_rejects_non_unit_and_obeys_supervisor_stop() {
    let mut vm = Vm::new(DenyHost);
    let invalid =
        vm.evaluate("full-gc-type.sml", "val _ = PolyML.fullGC 1;").expect_err("fullGC takes unit");
    assert_eq!(invalid.kind, MlErrorKind::Type);
    let collect = vm.lookup_value("PolyML.fullGC").unwrap().unwrap().clone();
    let invalid_direct = vm
        .apply(&collect, &[Value::int(1)])
        .expect_err("untagged VM calls must not bypass the unit contract");
    assert_eq!(invalid_direct.kind, MlErrorKind::Type);
    vm.request_stop();
    let stopped = vm
        .apply(&collect, &[Value::unit()])
        .expect_err("supervisor stop must preempt native collection");
    assert_eq!(stopped.kind, MlErrorKind::Stopped);
}

#[test]
fn polyml_heap_image_and_object_size_are_not_falsely_advertised() {
    let mut vm = Vm::new(DenyHost);
    for name in [
        "PolyML.objSize",
        "PolyML.shareCommonData",
        "PolyML.rootFunction",
        "PolyML.SaveState.saveChild",
        "PolyML.SaveState.showHierarchy",
    ] {
        assert!(vm.lookup_value(name).unwrap().is_none(), "{name} needs Poly/ML heap semantics");
    }
    let error = vm
        .evaluate("stats-unavailable.sml", "val _ = PolyML.Statistics.getLocalStats ();")
        .expect_err("native VM cannot produce Poly/ML heap or CPU statistics");
    assert_eq!(error.kind, MlErrorKind::HostPermission);
}
