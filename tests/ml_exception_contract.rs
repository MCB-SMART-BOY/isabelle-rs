use isabelle_rs::ml::{
    DenyHost, HostBridge, HostFailure, MlErrorKind, Type, TypeScheme, Value, Vm,
};

const EXN_SOURCE: &str = include_str!("../isabelle-source/src/Pure/General/exn.ML");

fn boot_exn() -> Vm {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate("Pure/General/exn.ML", EXN_SOURCE)
        .expect("original General/exn.ML must load without source edits");
    vm
}

fn integer(vm: &Vm, name: &str) -> i64 {
    vm.lookup_value(name).unwrap().and_then(Value::as_int).expect("integer result")
}

#[test]
fn exn_original_source_capture_release_preserves_packet_and_raise_location() {
    let mut vm = boot_exn();
    vm.evaluate(
        "origin.ML",
        r#"val captured = Exn.capture0
  (fn () => (raise Exn.ERROR "boom" : exn)) ();
val original = case captured of Exn.Exn e => e | _ => Exn.ERROR "absent";
val caught = Exn.release captured handle e => e;
val initial_location = PolyML.Exception.exceptionLocation original;
val after = PolyML.Exception.exceptionLocation caught;
val same_file = case after of SOME loc => #file loc | NONE => "missing";
val initial_line = case initial_location of SOME loc => #startLine loc | NONE => 0;
val reraised_line = case after of SOME loc => #startLine loc | NONE => 0;
val classified = case caught of Exn.ERROR "boom" => true | _ => false;"#,
    )
    .expect("capture and release should preserve an exception packet");
    let original = vm.lookup_value("original").unwrap().unwrap();
    let caught = vm.lookup_value("caught").unwrap().unwrap();
    assert!(original.is_same_object(caught));
    assert_eq!(vm.lookup_value("same_file").unwrap().and_then(Value::as_text), Some("origin.ML"));
    assert_eq!(integer(&vm, "initial_line"), 2);
    assert_eq!(integer(&vm, "initial_line"), integer(&vm, "reraised_line"));
    assert_eq!(vm.lookup_value("classified").unwrap().and_then(Value::as_bool), Some(true));
}

#[test]
fn exn_distinct_nullary_raises_keep_independent_source_locations() {
    let mut vm = boot_exn();
    vm.evaluate(
        "nullary.ML",
        r#"exception X;
val first = (raise X) handle e => e;
val second = (raise X) handle e => e;
val first_line = case PolyML.Exception.exceptionLocation first of
  SOME loc => #startLine loc | NONE => 0;
val second_line = case PolyML.Exception.exceptionLocation second of
  SOME loc => #startLine loc | NONE => 0;"#,
    )
    .expect("separate raises must retain separate packets");
    assert_eq!(integer(&vm, "first_line"), 2);
    assert_eq!(integer(&vm, "second_line"), 3);
}

#[test]
fn exn_trace_exception_returns_reporter_result_for_uncaught_action() {
    let mut vm = boot_exn();
    vm.evaluate(
        "trace-compat.ML",
        r#"
val report_calls = ref 0;
val effects = ref 0;
val seen_packet = ref (NONE: exn option);
val successful = PolyML.Exception.traceException
  (fn () => 11, fn _ => ((raise Exn.ERROR "callback") : int));
val recovered = (PolyML.Exception.traceException
  (fn () => (effects := !effects + 1; raise Exn.ERROR "action"),
   fn (_, packet) =>
     (report_calls := !report_calls + 1; seen_packet := SOME packet; 7)))
  handle Exn.ERROR "action" => 9 | _ => 0;
val report_count = !report_calls;
val effect_count = !effects;
val packet_preserved =
  case !seen_packet of SOME (Exn.ERROR "action") => true | _ => false;"#,
    )
    .expect("traceException runs the reporter when the action raises");
    assert_eq!(integer(&vm, "successful"), 11);
    assert_eq!(integer(&vm, "recovered"), 7);
    assert_eq!(integer(&vm, "report_count"), 1);
    assert_eq!(integer(&vm, "effect_count"), 1);
    assert_eq!(vm.lookup_value("packet_preserved").unwrap().and_then(Value::as_bool), Some(true));
}

#[test]
fn exn_dynamic_trace_records_only_entered_calls() {
    let mut vm = boot_exn();
    let error = vm
        .evaluate(
            "dynamic-trace.ML",
            "\
        fun inner () = raise Exn.ERROR \"trace\"; \
        fun outer () = inner (); \
        val _ = outer ();",
        )
        .expect_err("the ordinary diagnostic trace still records raised exceptions");
    assert!(matches!(error.kind, MlErrorKind::Exception(_)));
    assert!(
        error
            .trace
            .first()
            .is_some_and(|frame| frame.contains("dynamic-trace.ML") && frame.contains("raise"))
    );
    assert!(
        error.trace.iter().filter(|frame| frame.contains("apply")).count() >= 2,
        "{:?}",
        error.trace
    );
}

#[test]
fn exn_failed_argument_does_not_add_unentered_apply_frame() {
    let mut vm = boot_exn();
    let error = vm
        .evaluate(
            "never-called.ML",
            "\
        exception E; fun never_called x = x; \
        val _ = never_called (raise E);",
        )
        .expect_err("argument evaluation raises before the function is applied");
    assert!(matches!(error.kind, MlErrorKind::Exception(_)));
    assert!(error.trace.iter().any(|frame| frame.contains("raise")));
    assert!(!error.trace.iter().any(|frame| frame.contains("apply")), "{:?}", error.trace);
}

#[test]
fn exn_reraise_unraised_packet_creates_native_origin_without_mutating_original() {
    let mut vm = boot_exn();
    vm.evaluate(
        "fresh-reraise.ML",
        r#"
val original = Exn.ERROR "fresh";
val initial_location = PolyML.Exception.exceptionLocation original;
val reraised = PolyML.Exception.reraise original handle e => e;
val after = PolyML.Exception.exceptionLocation reraised;
val initial_is_none = case initial_location of NONE => true | SOME _ => false;
val original_still_none =
  case PolyML.Exception.exceptionLocation original of NONE => true | SOME _ => false;
val native_file = case after of SOME loc => #file loc | NONE => "missing";
val native_line = case after of SOME loc => #startLine loc | NONE => 0;
val native_start = case after of SOME loc => #startPosition loc | NONE => 0;
val native_end = case after of SOME loc => #endPosition loc | NONE => 0;"#,
    )
    .expect("first reraise is an ordinary raise at its native implementation site");
    let original = vm.lookup_value("original").unwrap().unwrap();
    let reraised = vm.lookup_value("reraised").unwrap().unwrap();
    assert!(!original.is_same_object(reraised));
    assert_eq!(vm.lookup_value("initial_is_none").unwrap().and_then(Value::as_bool), Some(true));
    assert_eq!(
        vm.lookup_value("original_still_none").unwrap().and_then(Value::as_bool),
        Some(true)
    );
    assert!(
        vm.lookup_value("native_file")
            .unwrap()
            .and_then(Value::as_text)
            .is_some_and(|path| path.ends_with("src/ml/basis/exception_runtime.rs"))
    );
    assert!(integer(&vm, "native_line") > 0);
    assert!(integer(&vm, "native_start") > 1);
    assert_eq!(integer(&vm, "native_end"), integer(&vm, "native_start") + 1);
}

#[test]
fn exn_io_cause_and_interrupt_are_ordinary_ml_exception_identites() {
    let mut vm = boot_exn();
    vm.evaluate(
        "interrupt.ML",
        "\
        val wrapped = IO.Io {name = \"file\", function = \"read\", \
            cause = Thread.Thread.Interrupt}; \
        val nested = Exn.is_interrupt wrapped; \
        val code = Exn.failure_rc wrapped; \
        val match_io = (raise wrapped) handle IO.Io {name, function, cause} => \
            name = \"file\" andalso function = \"read\" \
            andalso Exn.is_interrupt_raw cause | _ => false; \
        val error_caught = (Exn.error \"bad\" handle Exn.ERROR message => message);",
    )
    .expect("IO.Io packet, interrupt and user error must work as exceptions");
    assert_eq!(vm.lookup_value("nested").unwrap().and_then(Value::as_bool), Some(true));
    assert_eq!(integer(&vm, "code"), 130);
    assert_eq!(vm.lookup_value("match_io").unwrap().and_then(Value::as_bool), Some(true));
    assert_eq!(vm.lookup_value("error_caught").unwrap().and_then(Value::as_text), Some("bad"));
}

struct StopHost;
impl HostBridge for StopHost {
    fn invoke(&self, _: &mut Vm, operation: &str, _: &[Value]) -> Result<Value, HostFailure> {
        Err(HostFailure::Stopped { cause: format!("{operation} cancelled by supervisor") })
    }
}

#[test]
fn exn_capture_does_not_catch_supervisor_stop() {
    let mut vm = Vm::new(StopHost);
    vm.evaluate("Pure/General/exn.ML", EXN_SOURCE).unwrap();
    vm.register_host_effect(
        "stop_now",
        TypeScheme::mono(Type::Function(
            Box::new(Type::Constructor("unit".to_owned(), vec![])),
            Box::new(Type::Constructor("int".to_owned(), vec![])),
        )),
        "stop_now",
    )
    .unwrap();
    let error = vm
        .evaluate("stop.ML", "val caught = Exn.capture0 (fn () => stop_now ()) ();")
        .expect_err("supervisor stop cannot be captured as an ML exception");
    assert_eq!(error.kind, MlErrorKind::Stopped);
}

#[test]
fn exn_reraise_rejects_foreign_vm_exception_without_catching_it() {
    let first = boot_exn();
    let foreign = first.lookup_value("Thread.Thread.Interrupt").unwrap().unwrap().clone();
    let mut second = boot_exn();
    let reraise = second.lookup_value("PolyML.Exception.reraise").unwrap().unwrap().clone();
    let error = second
        .apply(&reraise, &[foreign])
        .expect_err("foreign exception objects must not enter another runtime");
    assert_eq!(error.kind, MlErrorKind::HostFailure);
    assert_eq!(second.check_stop().unwrap_err().kind, MlErrorKind::Stopped);
}

fn register_exception_native(vm: &mut Vm, callback: isabelle_rs::ml::NativeFunction) {
    vm.register_native(
        "native_failure",
        TypeScheme::mono(Type::Function(
            Box::new(Type::Constructor("unit".to_owned(), vec![])),
            Box::new(Type::Constructor("int".to_owned(), vec![])),
        )),
        callback,
    )
    .expect("native exception callback can be registered");
}

fn foreign_exception(_: &mut Vm, _: &[Value]) -> Result<Value, isabelle_rs::ml::MlError> {
    let mut other = Vm::new(DenyHost);
    Err(other
        .evaluate("foreign-native.ML", "val _ = raise Thread.Thread.Interrupt;")
        .expect_err("other VM raises its own exception"))
}

fn same_vm_exception(vm: &mut Vm, _: &[Value]) -> Result<Value, isabelle_rs::ml::MlError> {
    Err(vm.raise_named_exception("Thread.Thread.Interrupt", None, "native_failure", "Interrupt"))
}

fn forged_kind_exception(vm: &mut Vm, args: &[Value]) -> Result<Value, isabelle_rs::ml::MlError> {
    let mut error = same_vm_exception(vm, args).expect_err("callback raises a real packet");
    error.kind = MlErrorKind::Exception(0);
    Err(error)
}

fn missing_packet_exception(
    vm: &mut Vm,
    args: &[Value],
) -> Result<Value, isabelle_rs::ml::MlError> {
    let mut error = same_vm_exception(vm, args).expect_err("callback raises a real packet");
    error.exception = None;
    Err(error)
}

fn assert_native_error_stops(vm: &mut Vm, source: &str) {
    let error = vm
        .evaluate("native-boundary.ML", source)
        .expect_err("malformed or foreign native exception cannot be caught by ML");
    assert_eq!(error.kind, MlErrorKind::HostFailure);
    assert!(error.cause.contains("Interrupt"), "{error}");
    assert_eq!(vm.check_stop().unwrap_err().kind, MlErrorKind::Stopped);
}

#[test]
fn exn_foreign_native_exception_handle_fails_closed() {
    let mut vm = boot_exn();
    register_exception_native(&mut vm, foreign_exception);
    assert_native_error_stops(&mut vm, "val result = native_failure () handle _ => 7;");
}

#[test]
fn exn_foreign_native_exception_trace_exception_fails_closed() {
    let mut vm = boot_exn();
    register_exception_native(&mut vm, foreign_exception);
    assert_native_error_stops(
        &mut vm,
        "val result = PolyML.Exception.traceException \
         (fn () => native_failure (), fn _ => 7) handle _ => 9;",
    );
}

#[test]
fn exn_same_vm_native_exception_handle_preserves_packet() {
    let mut vm = boot_exn();
    register_exception_native(&mut vm, same_vm_exception);
    vm.evaluate(
        "native-valid.ML",
        "val result = native_failure () handle Thread.Thread.Interrupt => 42 | _ => 0;",
    )
    .expect("same-runtime exception remains catchable");
    assert_eq!(integer(&vm, "result"), 42);
    assert!(vm.check_stop().is_ok());
}

#[test]
fn exn_native_forged_kind_fails_closed() {
    let mut vm = boot_exn();
    register_exception_native(&mut vm, forged_kind_exception);
    assert_native_error_stops(&mut vm, "val result = native_failure () handle _ => 7;");
}

#[test]
fn exn_native_missing_packet_fails_closed() {
    let mut vm = boot_exn();
    register_exception_native(&mut vm, missing_packet_exception);
    assert_native_error_stops(&mut vm, "val result = native_failure () handle _ => 7;");
}

#[test]
fn exn_trace_shared_polymorphic_callback_preserves_each_input_instance() {
    let mut vm = boot_exn();
    vm.evaluate(
        "shared-trace-callback.ML",
        r#"
        val calls = ref 0;
        val exception_prints = ref 0;
        val _ = PolyML.addPrettyPrinter
          (fn _ => fn _ => fn (_: exn) =>
            (exception_prints := !exception_prints + 1; PolyML.PrettyString "exception"));
        fun callback value =
          (calls := !calls + 1;
           if !calls = 1 then raise Exn.ERROR "action"
           else (PolyML.prettyRepresentation (value, 8); 7));
        val result = PolyML.Exception.traceException (callback, callback);
        val callback_count = !calls;
        val exception_print_count = !exception_prints;
    "#,
    )
    .expect("each occurrence of the shared callback keeps its own certified type");
    assert_eq!(integer(&vm, "result"), 7);
    assert_eq!(integer(&vm, "callback_count"), 2);
    assert_eq!(integer(&vm, "exception_print_count"), 1);
}
