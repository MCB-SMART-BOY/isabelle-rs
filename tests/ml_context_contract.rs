use std::rc::Rc;

use isabelle_kernel::{Signature, TrustedTheory};
use isabelle_rs::ml::host::context::ContextHost;
use isabelle_rs::ml::host::lifecycle::{BuildLifecycle, WorkKind};
use isabelle_rs::ml::host::objects::ObjectStore;
use isabelle_rs::ml::{DenyHost, Vm};

const OFFICIAL_CONTEXT: &str = include_str!("../isabelle-source/src/Pure/context.ML");
const CONTEXT_DEPENDENCIES: &str = r#"
    type 'a ord = 'a * 'a -> order;
    structure Position =
    struct
      datatype T = Pos
      val none = Pos
      fun thread_data () = Pos
      fun here _ = ""
    end;
    structure Unsynchronized = struct datatype ref = datatype ref end;
    structure Any = struct type T = exn end;
    structure Long_Name =
    struct
      fun base_name name =
        let fun last [] = "" | last [part] = part | last (_ :: rest) = last rest
        in last (String.fields (fn c => c = #".") name) end
    end;
    structure Pretty =
    struct
      type T = string
      fun str_list left right parts =
        left ^ String.concatWith ", " parts ^ right
    end;
    exception ERROR of string;
    fun error message = raise ERROR message;
    fun quote text = "\"" ^ text ^ "\"";
    structure Library =
    struct
      fun foldl f (initial, values) =
        List.foldl (fn (element, accumulator) => f (accumulator, element))
          initial values
    end;
    val hd = List.hd;
    val map = List.map;
    val length = List.length;
    structure ML_Heap =
    struct
      fun sizeof1 _ = raise ERROR "heap inspection unavailable in Context contract fixture"
      fun full_gc () = raise ERROR "GC inspection unavailable in Context contract fixture"
    end;
"#;

fn create_context_vm()
-> (Vm, BuildLifecycle, Rc<isabelle_rs::ml::host::lifecycle::TaskLease>, Rc<ContextHost>) {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate("context-prerequisites.sml", CONTEXT_DEPENDENCIES)
        .expect("provide non-kernel Basis declarations before official Context.ML");
    let lifecycle = BuildLifecycle::new(vm.stop_handle());
    let lease = Rc::new(
        lifecycle.start_root(WorkKind::Evaluation, "Context evaluation").expect("start evaluation"),
    );
    let store = ObjectStore::new(&vm, lifecycle.clone()).expect("bind logical store");
    let context = ContextHost::install_official(
        &mut vm,
        store,
        lifecycle.clone(),
        Rc::clone(&lease),
        TrustedTheory::root("Pure", Signature::new()),
        "isabelle-source/src/Pure/context.ML",
        OFFICIAL_CONTEXT,
    )
    .expect("install full official Context with sealed private bridge");
    (vm, lifecycle, lease, context)
}

fn number(vm: &Vm, name: &str) -> i64 {
    vm.lookup_value(name)
        .expect("live VM")
        .expect("evaluated binding")
        .as_int()
        .expect("int binding")
}

fn release_context(
    vm: Vm,
    context: Rc<ContextHost>,
    lease: Rc<isabelle_rs::ml::host::lifecycle::TaskLease>,
) {
    drop(vm);
    drop(context);
    Rc::try_unwrap(lease).ok().expect("no leaked Context lease").complete().expect("complete work");
}

#[test]
fn context_parents_diamond_preserves_first_input_order_and_checked_ancestry() {
    let (mut vm, _lifecycle, lease, context) = create_context_vm();
    vm.evaluate("context-parents.sml", r#"
        val root = Context.finish_thy (Context.the_global_context ());
        val a = Context.finish_thy (Context.begin_thy "A" [root]);
        val b = Context.finish_thy (Context.begin_thy "B" [root]);
        val ab = Context.begin_thy "AB" [a, b, a];
        val ba = Context.begin_thy "BA" [b, a];
        val left_first = Context.theory_long_name (List.hd (Context.parents_of ab));
        val right_first = Context.theory_long_name (List.hd (Context.parents_of ba));
        val root_reachable = Context.subthy (root, ab);
        val distinct = not (Context.eq_thy (ab, ba));
        val trimmed = Context.Certificate_Id (Context.theory_id a);
        val full = Context.Certificate a;
        val trimmed_name = Context.theory_id_name {long = true} (Context.certificate_theory_id trimmed);
        val trimmed_ancestor =
          Context.subthy_id (Context.certificate_theory_id trimmed, Context.theory_id ab);
        val joined_has_content =
          (case Context.join_certificate (trimmed, full) of
            Context.Certificate _ => true | _ => false);
        val trimmed_rejects_content =
          (Context.certificate_theory trimmed; false) handle ERROR _ => true;
        val bad_name_is_error =
          (Context.begin_thy "" [root]; false) handle ERROR _ => true;
        val bad_join_is_theory =
          (Context.join_thys [a, b]; false) handle Context.THEORY _ => true;
        val empty_join_is_list_empty =
          (Context.join_thys []; false) handle List.Empty => true;
        val named_left = Context.finish_thy (Context.begin_thy "Left.Shared" [root]);
        val named_right = Context.finish_thy (Context.begin_thy "Right.Shared" [root]);
        val duplicate_base_is_theory =
          (Context.begin_thy "Collision" [named_left, named_right]; false)
            handle Context.THEORY _ => true;
    "#).expect("ordered checked parents");
    assert_eq!(vm.lookup_value("left_first").unwrap().unwrap().as_text(), Some("A"));
    assert_eq!(vm.lookup_value("right_first").unwrap().unwrap().as_text(), Some("B"));
    assert_eq!(vm.lookup_value("root_reachable").unwrap().unwrap().as_bool(), Some(true));
    assert_eq!(vm.lookup_value("distinct").unwrap().unwrap().as_bool(), Some(true));
    assert_eq!(vm.lookup_value("trimmed_name").unwrap().unwrap().as_text(), Some("A"));
    assert_eq!(vm.lookup_value("trimmed_ancestor").unwrap().unwrap().as_bool(), Some(true));
    assert_eq!(vm.lookup_value("joined_has_content").unwrap().unwrap().as_bool(), Some(true));
    assert_eq!(vm.lookup_value("trimmed_rejects_content").unwrap().unwrap().as_bool(), Some(true));
    assert_eq!(vm.lookup_value("bad_name_is_error").unwrap().unwrap().as_bool(), Some(true));
    assert_eq!(vm.lookup_value("bad_join_is_theory").unwrap().unwrap().as_bool(), Some(true));
    assert_eq!(vm.lookup_value("empty_join_is_list_empty").unwrap().unwrap().as_bool(), Some(true));
    assert_eq!(vm.lookup_value("duplicate_base_is_theory").unwrap().unwrap().as_bool(), Some(true));
    assert!(vm.lookup_value("Native_Context.data_get").unwrap().is_none());
    assert!(vm.lookup_value("Context.Theory_Data.get").unwrap().is_none());
    assert!(vm.lookup_value("Context.Proof_Data.get").unwrap().is_none());
    assert!(vm.lookup_structure("Native_Context").unwrap().is_none());
    assert!(
        vm.evaluate("hidden-context.sml", "val leaked = Native_Context.data_get (0, a);").is_err()
    );
    vm.evaluate(
        "retained-context.sml",
        "val retained = Context.theory_long_name (List.hd (Context.parents_of ab));",
    )
    .expect("Context closures keep private native bindings after hiding");
    assert_eq!(vm.lookup_value("retained").unwrap().unwrap().as_text(), Some("A"));
    release_context(vm, context, lease);
}

#[test]
fn context_merge_callback_exception_restores_dynamic_and_keeps_old_aliases() {
    let (mut vm, _lifecycle, lease, context) = create_context_vm();
    vm.evaluate(
        "context-callback.sml",
        r#"
        exception MergeFailed;
        val effects = ref 0;
        val provisional_seen = ref "";
        val provisional_good = ref (Context.the_global_context ());
        val prior_context = Context.the_global_context ();
        val root = Context.finish_thy (Context.the_global_context ());
        val a = Context.begin_thy "A" [root];
        val b = Context.begin_thy "B" [root];
        structure Counter = Theory_Data(
          type T = int;
          val empty = 0;
          fun merge (left, right) =
            (effects := !effects + 1;
             provisional_seen := Context.theory_long_name (Context.the_global_context ());
             if !effects = 1 then provisional_good := Context.the_global_context () else ();
             if !effects = 2 then raise MergeFailed else left + right)
        );
        structure Other = Theory_Data(
          type T = int;
          val empty = 0;
          fun merge (left, right) = left + right
        );
        val a1 = Context.finish_thy (Counter.put 5 a);
        val b1 = Context.finish_thy (Counter.put 6 b);
        val merged = Context.begin_thy "Good" [a1, b1];
        val checked_callback_owner = !provisional_good;
        val caught = (Context.begin_thy "Bad" [a1, b1]; 0)
          handle MergeFailed => !effects;
        val old_data = Counter.get a;
        val new_data = Counter.get a1;
        val callback_data = Counter.get merged;
        val other_default = Other.get a1;
        val observed = !provisional_seen;
        val restored = Context.eq_thy (prior_context, Context.the_global_context ());
        val tmp_raised =
          (Context.setmp_generic_context (SOME (Context.Theory a))
             (fn () => raise MergeFailed) (); false)
          handle MergeFailed => true;
        val after_tmp = Context.eq_thy (prior_context, Context.the_global_context ());
    "#,
    )
    .expect("catch original callback exception without rolling back prior ML ref effects");
    assert_eq!(number(&vm, "caught"), 2);
    assert_eq!(number(&vm, "old_data"), 0);
    assert_eq!(number(&vm, "new_data"), 5);
    assert_eq!(number(&vm, "callback_data"), 11);
    assert_eq!(number(&vm, "other_default"), 0);
    assert_eq!(vm.lookup_value("observed").unwrap().unwrap().as_text(), Some("Bad"));
    assert_eq!(vm.lookup_value("restored").unwrap().unwrap().as_bool(), Some(true));
    assert_eq!(vm.lookup_value("tmp_raised").unwrap().unwrap().as_bool(), Some(true));
    assert_eq!(vm.lookup_value("after_tmp").unwrap().unwrap().as_bool(), Some(true));
    let old = vm.lookup_value("a").unwrap().unwrap();
    let updated = vm.lookup_value("a1").unwrap().unwrap();
    assert!(context.has_same_logical_owner(&vm, old, updated).unwrap());
    let callback_owner = vm.lookup_value("checked_callback_owner").unwrap().unwrap();
    let merged = vm.lookup_value("merged").unwrap().unwrap();
    assert!(context.has_same_logical_owner(&vm, callback_owner, merged).unwrap());
    release_context(vm, context, lease);
}

#[test]
fn context_proof_kinds_are_generative_and_late_init_does_not_mutate_alias() {
    let (mut vm, _lifecycle, lease, context) = create_context_vm();
    vm.evaluate(
        "context-proof.sml",
        r#"
        val root = Context.finish_thy (Context.the_global_context ());
        structure First = Proof_Data(type T = int; fun init _ = 1);
        structure Second = Proof_Data(type T = int; fun init _ = 2);
        val local_seen = ref false;
        structure Bound = Proof_Data(
          type T = bool;
          fun init thy =
            (local_seen := Context.eq_thy
              (Context.Proof_Context.theory_of (Context.the_local_context ()), thy); true));
        val bound_context = Context.Proof_Context.init_global root;
        val checked_local = !local_seen andalso Bound.get bound_context;
        val old = Context.Proof_Context.init_global root;
        structure Late = Proof_Data(type T = int; fun init _ = 3);
        val newer = First.put 9 old;
        val old_first = First.get old;
        val new_first = First.get newer;
        val second = Second.get newer;
        val late = Late.get old;
        val old_theory = Context.eq_thy (Context.Proof_Context.theory_of old, root);
        exception InitFailed;
        val marker = ref 0;
        structure Faulty = Proof_Data(
          type T = int;
          fun init _ = (marker := !marker + 1; raise InitFailed));
        val prior_context = Context.the_global_context ();
        val failed = (Faulty.get old; false) handle InitFailed => true;
        val restored = Context.eq_thy (prior_context, Context.the_global_context ());
        val prior_effect = !marker;
    "#,
    )
    .expect("real immutable proof data");
    for (name, expected) in [("old_first", 1), ("new_first", 9), ("second", 2), ("late", 3)] {
        assert_eq!(number(&vm, name), expected);
    }
    assert_eq!(vm.lookup_value("old_theory").unwrap().unwrap().as_bool(), Some(true));
    assert_eq!(vm.lookup_value("checked_local").unwrap().unwrap().as_bool(), Some(true));
    assert_eq!(vm.lookup_value("failed").unwrap().unwrap().as_bool(), Some(true));
    assert_eq!(vm.lookup_value("restored").unwrap().unwrap().as_bool(), Some(true));
    assert_eq!(number(&vm, "prior_effect"), 1);
    release_context(vm, context, lease);
}

#[test]
fn context_join_singleton_preserves_first_input_identity_and_certificate() {
    let (mut vm, _lifecycle, lease, context) = create_context_vm();
    vm.evaluate(
        "context-join-identity.sml",
        r#"
        val root = Context.finish_thy (Context.the_global_context ());
        val first = Context.begin_thy "Joined" [root];
        val joined = Context.join_thys [first];
        val is_descendant = Context.subthy (first, joined);
        val certificate =
          Context.join_certificate (Context.Certificate first, Context.Certificate joined);
        val certificate_is_joined =
          Context.eq_thy (Context.certificate_theory certificate, joined);
    "#,
    )
    .expect("singleton join has a checked logical owner");
    assert_eq!(vm.lookup_value("is_descendant").unwrap().unwrap().as_bool(), Some(true));
    assert_eq!(vm.lookup_value("certificate_is_joined").unwrap().unwrap().as_bool(), Some(true));
    release_context(vm, context, lease);
}

#[test]
fn context_join_invalid_member_reports_only_offending_theories() {
    let (mut vm, _lifecycle, lease, context) = create_context_vm();
    vm.evaluate(
        "context-join-offenders.sml",
        r#"
        val root = Context.finish_thy (Context.the_global_context ());
        val open_thy = Context.begin_thy "Joined" [root];
        val closed_thy = Context.finish_thy open_thy;
        val bad =
          (Context.join_thys [open_thy, closed_thy]; [])
            handle Context.THEORY ("Cannot join theories", bad) => bad;
        val only_closed =
          (case bad of [thy] => Context.eq_thy (thy, closed_thy) | _ => false);
    "#,
    )
    .expect("join rejects only the invalid members");
    assert_eq!(vm.lookup_value("only_closed").unwrap().unwrap().as_bool(), Some(true));
    release_context(vm, context, lease);
}

#[test]
fn context_raw_transfer_unrelated_theory_raises_catchable_error() {
    let (mut vm, _lifecycle, lease, context) = create_context_vm();
    vm.evaluate(
        "context-transfer-error.sml",
        r#"
        val root = Context.finish_thy (Context.the_global_context ());
        val left = Context.finish_thy (Context.begin_thy "Left" [root]);
        val right = Context.finish_thy (Context.begin_thy "Right" [root]);
        val proof = Context.Proof_Context.init_global left;
        val rejected =
          (Context.raw_transfer right proof; false) handle ERROR _ => true;
        val still_in_left =
          Context.eq_thy (Context.Proof_Context.theory_of proof, left);
    "#,
    )
    .expect("ordinary transfer error is an SML exception");
    assert_eq!(vm.lookup_value("rejected").unwrap().unwrap().as_bool(), Some(true));
    assert_eq!(vm.lookup_value("still_in_left").unwrap().unwrap().as_bool(), Some(true));
    release_context(vm, context, lease);
}

#[test]
fn context_ancestors_diamond_and_shared_depth_have_official_order() {
    let (mut vm, _lifecycle, lease, context) = create_context_vm();
    vm.evaluate(
        "context-ancestors.sml",
        r#"
        val root = Context.finish_thy (Context.the_global_context ());
        val a = Context.finish_thy (Context.begin_thy "A" [root]);
        val b = Context.finish_thy (Context.begin_thy "B" [root]);
        val diamond = Context.begin_thy "Diamond" [a, b];
        val diamond_order = String.concatWith ","
          (List.map Context.theory_long_name (Context.ancestors_of diamond));
        val a_child = Context.finish_thy (Context.begin_thy "AChild" [a]);
        val b_child = Context.finish_thy (Context.begin_thy "BChild" [b]);
        val deep = Context.begin_thy "Deep" [a_child, b_child];
        val deep_order = String.concatWith ","
          (List.map Context.theory_long_name (Context.ancestors_of deep));
        val reverse = Context.begin_thy "Reverse" [b_child, a_child];
        val reverse_order = String.concatWith ","
          (List.map Context.theory_long_name (Context.ancestors_of reverse));
    "#,
    )
    .expect("native ancestor lists are observable");
    assert_eq!(vm.lookup_value("diamond_order").unwrap().unwrap().as_text(), Some("B,A,Pure"));
    assert_eq!(
        vm.lookup_value("deep_order").unwrap().unwrap().as_text(),
        Some("BChild,AChild,B,A,Pure")
    );
    assert_eq!(
        vm.lookup_value("reverse_order").unwrap().unwrap().as_text(),
        Some("AChild,BChild,A,B,Pure")
    );
    release_context(vm, context, lease);
}

#[test]
fn context_finished_same_name_ancestor_raises_theory() {
    let (mut vm, _lifecycle, lease, context) = create_context_vm();
    vm.evaluate(
        "context-finished-name.sml",
        r#"
        val first = Context.finish_thy (Context.the_global_context ());
        val second = Context.finish_thy first;
        val duplicate =
          (Context.finish_thy second; false)
            handle Context.THEORY (message, [_, _]) => message = "Duplicate theory name";
    "#,
    )
    .expect("duplicate finished ancestor has a catchable THEORY identity");
    assert_eq!(vm.lookup_value("duplicate").unwrap().unwrap().as_bool(), Some(true));
    release_context(vm, context, lease);
}

#[test]
fn context_theory_data_put_duplicate_ancestor_raises_theory() {
    let (mut vm, _lifecycle, lease, context) = create_context_vm();
    vm.evaluate(
        "context-put-finished.sml",
        r#"
        structure Slot = Theory_Data(
          type T = int; val empty = 0; fun merge (left, _) = left);
        val first = Context.finish_thy (Context.the_global_context ());
        val second = Context.finish_thy first;
        val caught =
          (Slot.put 1 second; false)
            handle Context.THEORY ("Duplicate theory name", [_, _]) => true;
        val old_value = Slot.get second;
    "#,
    )
    .expect("metadata put exposes a catchable ancestry conflict");
    assert_eq!(vm.lookup_value("caught").unwrap().unwrap().as_bool(), Some(true));
    assert_eq!(number(&vm, "old_value"), 0);
    release_context(vm, context, lease);
}

#[test]
fn context_saved_exceptions_retain_identity_after_public_rebinding() {
    let (mut vm, _lifecycle, lease, context) = create_context_vm();
    vm.evaluate(
        "context-exception-rebinding.sml",
        r#"
        exception Old_Theory = Context.THEORY;
        exception Old_Error = ERROR;
        exception Old_Empty = List.Empty;
        val saved_begin = Context.begin_thy;
        val saved_join = Context.join_thys;
        val finished = Context.finish_thy (Context.the_global_context ());
        exception ERROR of string;
        structure Context = struct exception THEORY of string * int list end;
        structure List = struct exception Empty end;
        val original_error =
          (saved_begin "" [finished]; false)
            handle Old_Error _ => true | ERROR _ => false;
        val original_theory =
          (saved_join [finished]; false)
            handle Old_Theory _ => true | Context.THEORY _ => false;
        val original_empty =
          (saved_join []; false)
            handle Old_Empty => true | List.Empty => false;
    "#,
    )
    .expect("saved Context closures preserve generative exception identity");
    for name in ["original_error", "original_theory", "original_empty"] {
        assert_eq!(vm.lookup_value(name).unwrap().unwrap().as_bool(), Some(true));
    }
    release_context(vm, context, lease);
}

#[test]
fn context_sibling_stages_appear_in_pretty_and_trimmed_certificate_errors() {
    let (mut vm, _lifecycle, lease, context) = create_context_vm();
    vm.evaluate(
        "context-stage-display.sml",
        r#"
        structure Slot = Theory_Data(
          type T = int; val empty = 0; fun merge (left, _) = left);
        val source = Context.the_global_context ();
        val first = Slot.put 1 source;
        val second = Slot.put 2 source;
        val first_pretty = Context.pretty_thy first;
        val second_pretty = Context.pretty_thy second;
        val trimmed_message =
          (Context.certificate_theory (Context.Certificate_Id (Context.theory_id first)); "")
            handle ERROR text => text;
    "#,
    )
    .expect("stage diagnostics are available for unfinished theory");
    assert_eq!(vm.lookup_value("first_pretty").unwrap().unwrap().as_text(), Some("{Pure:2}"));
    assert_eq!(vm.lookup_value("second_pretty").unwrap().unwrap().as_text(), Some("{Pure:3}"));
    assert_eq!(
        vm.lookup_value("trimmed_message").unwrap().unwrap().as_text(),
        Some("No content for theory certificate Pure:2")
    );
    release_context(vm, context, lease);
}

#[test]
fn context_foreign_runtime_handle_revokes_lookup_without_returning_owner() {
    let (mut first, _first_lifecycle, first_lease, first_context) = create_context_vm();
    first
        .evaluate(
            "foreign-context-source.sml",
            "val foreign_theory = Context.the_global_context ();",
        )
        .expect("create theory through a compiler-certified call");
    let foreign_theory = first.lookup_value("foreign_theory").unwrap().unwrap().clone();
    let (mut second, _second_lifecycle, second_lease, second_context) = create_context_vm();
    let parents = second.lookup_value("Context.parents_of").unwrap().unwrap().clone();
    let error = second
        .apply(&parents, &[foreign_theory])
        .expect_err("a foreign theory cannot reach Context.parents_of");
    assert_eq!(error.kind, isabelle_rs::ml::MlErrorKind::HostFailure);
    assert!(second.check_stop().is_err());
    drop(second);
    drop(second_context);
    assert!(Rc::try_unwrap(second_lease).ok().unwrap().complete().is_err());
    release_context(first, first_context, first_lease);
}

#[test]
fn context_install_when_original_boundary_is_changed_revokes_build() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate("context-prerequisites.sml", CONTEXT_DEPENDENCIES)
        .expect("non-kernel Context prerequisites");
    let lifecycle = BuildLifecycle::new(vm.stop_handle());
    let lease =
        Rc::new(lifecycle.start_root(WorkKind::Evaluation, "Context installation").unwrap());
    let store = ObjectStore::new(&vm, lifecycle.clone()).unwrap();
    let changed = OFFICIAL_CONTEXT.replacen(
        "structure Context: PRIVATE_CONTEXT =",
        "structure Altered: PRIVATE_CONTEXT =",
        1,
    );
    let result = ContextHost::install_official(
        &mut vm,
        store,
        lifecycle.clone(),
        Rc::clone(&lease),
        TrustedTheory::root("Pure", Signature::new()),
        "isabelle-source/src/Pure/context.ML",
        &changed,
    );
    assert!(result.is_err());
    assert!(vm.check_stop().is_err());
    assert!(lifecycle.check_task(&lease).is_err());
}

#[test]
fn context_parent_merge_callback_observes_canonical_order_and_old_values() {
    let (mut vm, _lifecycle, lease, context) = create_context_vm();
    vm.evaluate(
        "context-ordered-merge.sml",
        r#"
        val root = Context.finish_thy (Context.the_global_context ());
        val a = Context.begin_thy "A" [root];
        val b = Context.begin_thy "B" [root];
        val callback_parents = ref "";
        structure Ordered = Theory_Data'(
          type T = string;
          val empty = "";
          fun merge args =
            (callback_parents :=
               String.concatWith "," (List.map Context.theory_long_name
                 (Context.parents_of (Context.the_global_context ())));
             String.concatWith "," (List.map
               (fn (thy, value) => Context.theory_long_name thy ^ "=" ^ value) args))
        );
        val updated_a = Context.finish_thy (Ordered.put "one" a);
        val updated_b = Context.finish_thy (Ordered.put "two" b);
        val combined = Context.begin_thy "Combined" [root, updated_b, updated_a, updated_b];
        val selected_parents =
          String.concatWith "," (List.map Context.theory_long_name (Context.parents_of combined));
        val merged_value = Ordered.get combined;
        val parent_a_value = Ordered.get updated_a;
        val parent_b_value = Ordered.get updated_b;
        val old_a_value = Ordered.get a;
        val old_b_value = Ordered.get b;
        val observed_parents = !callback_parents;
    "#,
    )
    .expect("canonical input order reaches the source merge callback without rewriting aliases");
    for (name, expected) in [
        ("selected_parents", "B,A"),
        ("observed_parents", "B,A"),
        ("merged_value", "B=two,A=one"),
        ("parent_a_value", "one"),
        ("parent_b_value", "two"),
        ("old_a_value", ""),
        ("old_b_value", ""),
    ] {
        assert_eq!(vm.lookup_value(name).unwrap().unwrap().as_text(), Some(expected));
    }
    release_context(vm, context, lease);
}

#[test]
fn context_late_proof_callback_failure_preserves_exception_and_prior_proof() {
    let (mut vm, _lifecycle, lease, context) = create_context_vm();
    vm.evaluate(
        "context-late-proof-failure.sml",
        r#"
        val root = Context.finish_thy (Context.the_global_context ());
        val original = Context.Proof_Context.init_global root;
        exception LateFailed;
        val effects = ref 0;
        val callback_context = ref false;
        structure Late = Proof_Data(
          type T = int;
          fun init thy =
            (effects := !effects + 1;
             callback_context := Context.eq_thy
               (Context.Proof_Context.theory_of (Context.the_local_context ()), thy);
             raise LateFailed)
        );
        val prior = Context.the_global_context ();
        val first = (Late.get original; false) handle LateFailed => true;
        val second = (Late.get original; false) handle LateFailed => true;
        val original_theory = Context.eq_thy (Context.Proof_Context.theory_of original, root);
        val restored = Context.eq_thy (Context.the_global_context (), prior);
        val effect_count = !effects;
        val saw_local_context = !callback_context;
    "#,
    )
    .expect("late init re-evaluates and preserves its original exception and ref effects");
    for name in ["first", "second", "original_theory", "restored", "saw_local_context"] {
        assert_eq!(vm.lookup_value(name).unwrap().unwrap().as_bool(), Some(true));
    }
    assert_eq!(number(&vm, "effect_count"), 2);
    release_context(vm, context, lease);
}
