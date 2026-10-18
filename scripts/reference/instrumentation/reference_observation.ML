(* Instrumented-copy only. This module does not authorize theorems. *)
structure Reference_Observation =
struct

fun required_env name =
  (case OS.Process.getEnv name of
    SOME value => if value = "" then raise Fail ("Empty observer setting " ^ name) else value
  | NONE => raise Fail ("Missing observer setting " ^ name));

fun run_id () = required_env "REFERENCE_OBSERVATION_RUN_ID";
fun run_phase () = required_env "REFERENCE_OBSERVATION_PHASE";
fun raw_path () = required_env "REFERENCE_OBSERVATION_RAW";
val _ = if run_phase () = "build" then ()
  else raise Fail "Primordial observer must begin in build phase";

val current_run_id = ref (run_id ());
val next_load = ref 0;
val active_load = ref (SOME (required_env "REFERENCE_OBSERVATION_ROOT0_LOAD_ID"));
val active_source = ref "src/Pure/ROOT0.ML";
val next_event = ref 0;
val source_ordinals = ref ([]: (string * int) list);

fun ensure_run () =
  let val id = run_id ()
  in if id = ! current_run_id then ()
    else
      (current_run_id := id; next_load := 0; active_load := NONE;
       active_source := ""; next_event := 0; source_ordinals := [])
  end;

fun encode_fields fields =
  Int.toString (List.length fields) ^ "\n" ^
  String.concat (List.map (fn value => Int.toString (size value) ^ "\n" ^ value) fields);

fun emit channel tag root_id local_id payload =
  let
    val _ = ensure_run ();
    val frame = encode_fields [channel, tag, run_id (), root_id, local_id, payload];
    val outstream = TextIO.openAppend (raw_path ());
    val result = (TextIO.output (outstream, Int.toString (size frame) ^ "\n" ^ frame);
      TextIO.flushOut outstream) handle exn => (TextIO.closeOut outstream; raise exn);
  in result; TextIO.closeOut outstream end;

fun escape_json_char c =
  (case c of
    #"\"" => "\\\""
  | #"\\" => "\\\\"
  | #"\n" => "\\n"
  | #"\r" => "\\r"
  | #"\t" => "\\t"
  | _ =>
      if Char.ord c < 32 then
        "\\u00" ^ StringCvt.padLeft #"0" 2 (Int.fmt StringCvt.HEX (Char.ord c))
      else String.str c);

fun json_string value = "\"" ^ String.translate escape_json_char value ^ "\"";

fun yxml_element name attrs contents =
  let
    val x = String.str (Char.chr 5);
    val y = String.str (Char.chr 6);
    val properties = String.concat
      (List.map (fn (key, value) => y ^ key ^ "=" ^ value) attrs);
  in x ^ y ^ name ^ properties ^ x ^ contents ^ x ^ y ^ x end;

fun source_hash source =
  let
    val input = TextIO.openIn (required_env "REFERENCE_OBSERVATION_SOURCE_HASHES");
    val contents = (TextIO.inputAll input)
      handle exn => (TextIO.closeIn input; raise exn);
    val _ = TextIO.closeIn input;
    val rows = String.tokens (fn c => c = #"\n") contents;
    val values = List.map (String.fields (fn c => c = #"\t")) rows;
  in
    (case List.filter (fn entry => case entry of [path, _] => path = source | _ => false) values of
      [[_, digest]] => if size digest = 64 then digest
        else raise Fail ("Invalid source digest for " ^ source)
    | _ => raise Fail ("Missing or duplicate source digest for " ^ source))
  end;

fun emit_registration kind name owner action =
  let
    val root = (case ! active_load of
      SOME id => id
    | NONE => raise Fail ("Registration without observable load root: " ^ name));
    val source = ! active_source;
    val phase = if run_phase () = "inventory" then "original_target"
      else if String.isPrefix "src/Pure/" source then "original_bootstrap"
      else "preparation";
    val value = "{\"kind\":" ^ json_string kind ^ ",\"name\":" ^ json_string name ^
      ",\"owner\":" ^ json_string owner ^ ",\"source\":" ^ json_string source ^
      ",\"action\":" ^ json_string action ^
      ",\"signature\":{\"domain\":null,\"range\":null}}";
    val payload = yxml_element "observation"
      [("phase", phase), ("theory", owner), ("source", source),
       ("source_sha256", source_hash source), ("field", "runtime_registration_effects")]
      (yxml_element "payload" [] value);
    val _ = next_event := ! next_event + 1;
  in emit "observer" "event" root (Int.toString (! next_event)) payload end;

fun root_entry () =
  let
    val root0 = required_env "REFERENCE_OBSERVATION_ROOT0_LOAD_ID";
    val root = required_env "REFERENCE_OBSERVATION_ROOT_LOAD_ID";
    val _ = if ! active_load = SOME root0 then ()
      else raise Fail "ROOT started outside the approved ROOT0 loader";
  in active_load := SOME root; active_source := "src/Pure/ROOT.ML" end;

fun source_path source =
  if String.isPrefix "src/" source orelse String.isPrefix "session/" source
  then source
  else if OS.Path.isAbsolute source then
    let val source_root = required_env "REFERENCE_OBSERVATION_SOURCE_ROOT" ^ "/";
        val session_root = required_env "REFERENCE_OBSERVATION_SESSION_ROOT" ^ "/"
    in if String.isPrefix source_root source then String.extract (source, size source_root, NONE)
       else if String.isPrefix session_root source then
         "session/" ^ String.extract (source, size session_root, NONE)
       else raise Fail ("Observer source outside fixed snapshot: " ^ source) end
  else "src/Pure/" ^ source;

fun load_id source =
  (next_load := ! next_load + 1;
   run_id () ^ ":" ^ Int.toString (! next_load) ^ ":" ^ source);

fun next_source_order parent =
  let
    val ordinal = (case List.find (fn (id, _) => id = parent) (! source_ordinals) of
      SOME (_, value) => value
    | NONE => 0);
    val remaining = List.filter (fn (id, _) => id <> parent) (! source_ordinals);
  in source_ordinals := (parent, ordinal + 1) :: remaining; ordinal + 1 end;

fun load_payload source parent session theory ordinal mode contents =
  encode_fields [source, parent, session, theory, Int.toString ordinal, mode, contents];

fun begin_load source session theory mode =
  let
    val _ = ensure_run ();
    val parent = (case ! active_load of NONE => "" | SOME id => id);
    val ordinal = next_source_order parent;
    val id = load_id source;
    val payload = load_payload source parent session theory ordinal mode "";
    val _ = emit "bootstrap" "load_begin" id "begin" payload;
  in (id, parent, ordinal) end;

fun end_load (id, parent, ordinal) source session theory mode text =
  emit "bootstrap" "load_end" id "end"
    (load_payload source parent session theory ordinal mode text);

fun fail_load (id, parent, ordinal) source session theory mode =
  emit "bootstrap" "load_error" id "error"
    (load_payload source parent session theory ordinal mode "");

fun with_load source session theory read evaluate =
  let
    val source = source_path source;
    val load as (id, _, _) = begin_load source session theory "actual_read_bytes";
    val prior = (! active_load, ! active_source);
    fun restore () = (active_load := #1 prior; active_source := #2 prior);
    val result =
      ((let
        val contents = read ();
        val _ = active_load := SOME id;
        val _ = active_source := source;
        val value = evaluate contents;
        val _ = end_load load source session theory "actual_read_bytes" contents;
      in value end)
       handle exn => (restore (); fail_load load source session theory "actual_read_bytes"; raise exn));
  in restore (); result end;

(* PolyML.use owns an opaque stream. Its input is not reread by the observer.
   Immutable source provenance requires independent supervisor verification. *)
fun bootstrap_file original source =
  let val path = source_path source;
      val load as (id, _, _) = begin_load path "Pure" "" "immutable_bootstrap_use";
      val prior = (! active_load, ! active_source);
      val result = ((active_load := SOME id; active_source := path; original source)
        handle exn => (active_load := #1 prior; active_source := #2 prior;
          fail_load load path "Pure" "" "immutable_bootstrap_use"; raise exn));
      val _ = end_load load path "Pure" "" "immutable_bootstrap_use" "";
  in active_load := #1 prior; active_source := #2 prior; result end;

end;
