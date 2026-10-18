//! Replacement for only the approved `structure Context: PRIVATE_CONTEXT` body.
//! The original signatures and the data functors following this structure stay
//! in the original context.ML, in their original load order.

pub(super) const SOURCE: &str = r#"
structure Context: PRIVATE_CONTEXT =
struct
  type theory = host_context_theory
  type theory_id = host_context_id
  type id = int
  type data_kind = int
  structure Proof = struct type context = host_context_proof end
  exception THEORY of string * theory list
  val PureN = "Pure"
  val data_timing = Unsynchronized.ref false
  val theory_tracing = Unsynchronized.ref false
  val proof_tracing = Unsynchronized.ref false
  fun enabled_tracing () = !theory_tracing orelse !proof_tracing
  fun note_tracing () =
    Native_Context.set_tracing (!theory_tracing, !proof_tracing, Position.thread_data ())
  val theory_id = Native_Context.theory_id
  val parents_of = Native_Context.parents
  val ancestors_of = Native_Context.ancestors
  val theory_identifier = Native_Context.identifier
  val theory_long_name = Native_Context.name
  val theory_base_name = Long_Name.base_name o theory_long_name
  fun theory_name {long} thy = if long then theory_long_name thy else theory_base_name thy
  fun theory_id_ord (a, b) = Int.compare (Native_Context.id_serial a, Native_Context.id_serial b)
  fun theory_id_name {long} thy_id =
    let val name = Native_Context.id_name thy_id
    in if long then name else Long_Name.base_name name end
  fun eq_thy_id (a, b) = Native_Context.id_eq (a, b)
  fun eq_thy (a, b) = Native_Context.eq (a, b)
  fun subthy_id (a, b) = Native_Context.id_sub (a, b)
  fun proper_subthy_id (a, b) = subthy_id (a, b) andalso not (eq_thy_id (a, b))
  fun proper_subthy (a, b) = Native_Context.sub (a, b) andalso not (eq_thy (a, b))
  fun subthy (a, b) = Native_Context.sub (a, b)
  fun display_name thy_id =
    let val name = theory_id_name {long = false} thy_id
        val stage = Native_Context.id_stage thy_id
    in if stage = 0 then name else name ^ ":" ^ Int.toString stage end
  fun get_theory {long} thy name =
    if theory_name {long = long} thy = name then
      if Native_Context.stage thy = 0 then thy
      else error ("Unfinished theory " ^ quote name)
    else
      (case List.find (fn ancestor => theory_name {long = long} ancestor = name)
             (ancestors_of thy) of
        SOME ancestor => ancestor
      | NONE => error ("Unknown ancestor theory " ^ quote name))
  fun pretty_thy thy =
    Pretty.str_list "{" "}" (map theory_long_name (rev (ancestors_of thy)) @
      [display_name (theory_id thy)])
  fun pretty_abbrev_thy thy =
    let val names = map theory_long_name (rev (ancestors_of thy)) @
          [display_name (theory_id thy)]
        val n = length names
    in Pretty.str_list "{" "}"
         (if n > 5 then "..." :: List.drop (names, n - 5) else names) end
  fun join_thys thys = (note_tracing (); Native_Context.join thys)
  fun begin_thy name imports = (note_tracing (); Native_Context.begin (name, imports))
  fun finish_thy thy = (note_tracing (); Native_Context.finish thy)
  val data_kinds = Native_Context.theory_kinds
  fun theory_data_sizeof1 thy =
    map (fn (kind, pos) => (pos, ML_Heap.sizeof1 (Native_Context.data_get (kind, thy))))
      (Native_Context.present_kinds thy)
  structure Proof_Context =
  struct
    val theory_of = Native_Context.proof_theory
    fun init_global thy = (note_tracing (); Native_Context.proof_init thy)
    fun get_global long thy name = init_global (get_theory long thy name)
  end
  fun raw_transfer thy ctxt =
    (note_tracing (); Native_Context.proof_transfer (thy, ctxt))
  datatype certificate = Certificate of theory | Certificate_Id of theory_id
  fun certificate_theory (Certificate thy) = thy
    | certificate_theory (Certificate_Id thy_id) =
        error ("No content for theory certificate " ^ display_name thy_id)
  fun certificate_theory_id (Certificate thy) = theory_id thy
    | certificate_theory_id (Certificate_Id thy_id) = thy_id
  fun eq_certificate (Certificate a, Certificate b) = eq_thy (a, b)
    | eq_certificate (Certificate_Id a, Certificate_Id b) = eq_thy_id (a, b)
    | eq_certificate _ = false
  fun join_certificate (left, right) =
    let val a = certificate_theory_id left
        val b = certificate_theory_id right
    in if eq_thy_id (a, b) then
         (case left of Certificate _ => left | _ => right)
       else if proper_subthy_id (b, a) then left
       else if proper_subthy_id (a, b) then right
       else error ("Cannot join unrelated theory certificates " ^
         display_name a ^ " and " ^ display_name b)
    end
  fun join_certificate_theory (left, right) =
    if subthy (right, left) then left
    else if proper_subthy (left, right) then right
    else error ("Cannot join unrelated theory certificates " ^
      display_name (theory_id left) ^ " and " ^ display_name (theory_id right))
  datatype generic = Theory of theory | Proof of Proof.context
  fun cases f _ (Theory thy) = f thy
    | cases _ g (Proof ctxt) = g ctxt
  fun mapping f g = cases (Theory o f) (Proof o g)
  fun mapping_result f g = cases (fn thy => let val (x, y) = f thy in (x, Theory y) end)
    (fn ctxt => let val (x, y) = g ctxt in (x, Proof y) end)
  fun the_theory (Theory thy) = thy
    | the_theory _ = error "Ill-typed context: theory expected"
  fun the_proof (Proof ctxt) = ctxt
    | the_proof _ = error "Ill-typed context: proof expected"
  fun map_theory f = Theory o f o the_theory
  fun map_proof f = Proof o f o the_proof
  fun map_theory_result f ctxt =
    let val (x, y) = f (the_theory ctxt) in (x, Theory y) end
  fun map_proof_result f ctxt =
    let val (x, y) = f (the_proof ctxt) in (x, Proof y) end
  fun theory_map f = the_theory o f o Theory
  fun proof_map f = the_proof o f o Proof
  val theory_of = cases (fn thy => thy) Proof_Context.theory_of
  val proof_of = cases Proof_Context.init_global (fn ctxt => ctxt)
  fun get_generic_context () =
    (case Native_Context.dynamic_kind () of
      0 => NONE
    | 1 => SOME (Theory (Native_Context.dynamic_theory ()))
    | 2 => SOME (Proof (Native_Context.dynamic_proof ()))
    | _ => error "Corrupt dynamic Context tag")
  fun put_generic_context NONE = Native_Context.dynamic_clear ()
    | put_generic_context (SOME (Theory thy)) = Native_Context.dynamic_set_theory thy
    | put_generic_context (SOME (Proof ctxt)) = Native_Context.dynamic_set_proof ctxt
  fun setmp_generic_context context f x =
    let val previous = get_generic_context ()
        val _ = put_generic_context context
    in (f x before put_generic_context previous)
      handle exn => (put_generic_context previous; raise exn)
    end
  fun the_generic_context () =
    (case get_generic_context () of
      SOME context => context
    | NONE => error "Unknown context")
  val the_global_context = theory_of o the_generic_context
  val the_local_context = proof_of o the_generic_context
  fun >>> f =
    let val (result, context) = f (the_generic_context ())
        val _ = put_generic_context (SOME context)
    in result end
  nonfix >>
  fun >> f = >>> (fn context => ((), f context))
  structure Theory_Data =
  struct
    val declare = fn pos => fn empty => fn merge =>
      Native_Context.data_declare (pos, empty, merge)
    fun get kind dest thy = dest (Native_Context.data_get (kind, thy))
    fun put kind make x thy =
      (note_tracing (); Native_Context.data_put (kind, make x, thy))
  end
  structure Proof_Data =
  struct
    val declare = Native_Context.proof_declare
    fun get kind dest ctxt = dest (Native_Context.proof_get (kind, ctxt))
    fun put kind make x ctxt =
      (note_tracing (); Native_Context.proof_put (kind, make x, ctxt))
  end
  fun finish_tracing () =
    let val _ = ML_Heap.full_gc ()
        val (theories, proofs, total_theories, total_proofs) =
          Native_Context.finish_tracing ()
        val contexts =
          map (fn (thy, pos) => (Theory thy, pos)) theories @
          map (fn (ctxt, pos) => (Proof ctxt, pos)) proofs
        val active_theories = length theories
        val active_proofs = length proofs
    in {contexts = contexts,
        active_contexts = active_theories + active_proofs,
        active_theories = active_theories,
        active_proofs = active_proofs,
        total_contexts = total_theories + total_proofs,
        total_theories = total_theories,
        total_proofs = total_proofs} end
end;
"#;
