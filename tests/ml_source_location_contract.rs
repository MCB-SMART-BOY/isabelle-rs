use isabelle_rs::ml::{DenyHost, Vm};

fn integers(vm: &Vm, name: &str) -> Vec<i64> {
    vm.lookup_value(name)
        .unwrap()
        .unwrap()
        .as_tuple()
        .unwrap()
        .iter()
        .map(|value| value.as_int().unwrap())
        .collect()
}

#[test]
fn exception_location_multiline_utf8_and_named_symbol_reports_full_file_offsets() {
    let source = "(* é \\<alpha> *)\nexception E;\nval captured = (raise E) handle e => e;\n\
        val location = case PolyML.Exception.exceptionLocation captured of\n\
          SOME loc => (#startLine loc, #startPosition loc, #endLine loc, #endPosition loc)\n\
        | NONE => (0, 0, 0, 0);";
    let mut vm = Vm::new(DenyHost);
    vm.evaluate("utf8-location.ML", source).expect("exceptionLocation returns the source range");

    let prefix = source.split_once("raise E").unwrap().0;
    let symbol_bytes = "\\<alpha>".len();
    let start = (prefix.chars().count() - symbol_bytes + 2) as i64;
    assert_eq!(integers(&vm, "location"), [3, start, 3, start + 7]);
}

#[test]
fn exception_location_crlf_reports_one_line_break_and_one_symbol() {
    let source = "exception E;\r\nval captured = (raise E) handle e => e;\r\n\
        val location = case PolyML.Exception.exceptionLocation captured of\r\n\
          SOME loc => (#startLine loc, #startPosition loc, #endPosition loc)\r\n\
        | NONE => (0, 0, 0);";
    let mut vm = Vm::new(DenyHost);
    vm.evaluate("crlf-location.ML", source).expect("CRLF source positions remain stable");

    let prefix = source.split_once("raise E").unwrap().0;
    let start = prefix.len() as i64;
    assert_eq!(integers(&vm, "location"), [2, start, start + 7]);
}

#[test]
fn exception_trace_actual_call_site_reports_global_right_open_range() {
    let source = "exception E;\nfun fail () = raise E;\nval broken = fail ();";
    let mut vm = Vm::new(DenyHost);
    let error = vm
        .evaluate("call-site.ML", source)
        .expect_err("an unhandled exception retains source-backed call frames");

    let call = source.rfind("fail ()").unwrap();
    let argument = call + "fail ".len();
    let start = source[..argument].chars().count() + 1;
    let line = source[..argument].bytes().filter(|byte| *byte == b'\n').count() + 1;
    let expected = format!("call-site.ML:{line}:{start}-{line}:{}: apply", start + 2);
    assert!(
        error.trace.iter().any(|frame| frame == &expected),
        "missing actual call-site frame {expected}: {:?}",
        error.trace
    );
}

#[test]
fn exception_trace_long_named_symbol_before_call_reports_symbol_offsets() {
    let symbol = format!("\\<{}>", "a".repeat(4096));
    let source =
        format!("(* {symbol} *)\nexception E;\nfun fail () = raise E;\nval broken = fail ();");
    let mut vm = Vm::new(DenyHost);
    let error = vm
        .evaluate("long-symbol-location.ML", &source)
        .expect_err("an unhandled exception retains source-backed call frames");

    let call = source.rfind("fail ()").unwrap();
    let argument = call + "fail ".len();
    let start = source[..argument].chars().count() - symbol.len() + 2;
    let expected = format!("long-symbol-location.ML:4:{start}-4:{}: apply", start + 2);
    assert!(
        error.trace.iter().any(|frame| frame == &expected),
        "missing actual call-site frame {expected}: {:?}",
        error.trace
    );
}
