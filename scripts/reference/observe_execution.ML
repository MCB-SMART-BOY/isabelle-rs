(* Reference-only observer: no logical declarations or Rust theorem authority. *)
local
  val roots =
    ["HOL.HOL", "HOL.Orderings", "HOL.Set", "HOL.Nat", "HOL.List", "HOL.Fun",
     "HOL.Product_Type", "HOL.Sum_Type", "HOL.Option"];
  val initial_theories = Thy_Info.get_names ();
  val _ = if exists Thy_Info.defined_theory roots
    then error "Target theory already loaded before execution observer" else ();

  fun element name attributes children = XML.Elem ((name, attributes), children);
  fun named tag name = element tag [("name", name)] [];
  fun require_position label get pos =
    (case get pos of SOME value => value
    | NONE => error ("Missing " ^ label ^ " in executed command position"));

  fun export_file thy (file: Token.file) =
    element "file"
      [("path", File.symbolic_path
          (File.full_path (Resources.master_directory thy) (#src_path file))),
       ("sha1", SHA1.rep (#digest file))] [];

  (* Resolve inputs of completed commands through the official parser; these are
     source bindings, not a trace of nested runtime/compiler file operations. *)
  val file_commands =
    ["ML_file", "ML_file_debug", "ML_file_no_debug",
     "SML_file", "SML_file_debug", "SML_file_no_debug"];
  fun resolve_command_files name previous (segment: Document_Output.segment) =
    if not (member (op =) file_commands name) then []
    else
      let
        val tokens = filter Token.is_proper (Command_Span.content (#span segment));
        val arguments = (case tokens of _ :: rest => rest
          | [] => error "Empty executed ML file command");
        val parser = Resources.parse_file --| Scan.option (Parse.$$$ ";");
        val get_file = (case Scan.read Token.stopper parser arguments of
          SOME value => value | NONE => error "Cannot resolve executed ML file command");
        val thy = Toplevel.theory_of previous;
      in [export_file thy (get_file thy)] end;

  fun export_command (segment: Document_Output.segment) previous =
    let
      val commands =
        (case Command_Span.kind (#span segment) of
          Command_Span.Command_Span (name, pos) =>
            [element "command"
              [("name", name),
               ("source", require_position "source" Position.file_of pos),
               ("line", string_of_int (require_position "line" Position.line_of pos)),
               ("offset", string_of_int (require_position "offset" Position.offset_of pos)),
               ("skipped", Bool.toString (Toplevel.is_skipped_proof (#state segment)))]
              (resolve_command_files name previous segment)]
        | Command_Span.Ignored_Span => []
        | Command_Span.Malformed_Span => error "Malformed executed command span");
    in (commands, #state segment) end;

  fun export_theory (thy, segments) =
    let
      val source = Resources.master_directory thy +
        Resources.thy_path (Path.basic (Context.theory_base_name thy));
      val _ = if Resources.loaded_files_current thy then ()
        else error ("Changed executed source files in " ^ Context.theory_long_name thy);
      (* join_results resets prev_state at each element; carry the actual preceding
         completed state across the entire source-ordered segment sequence. *)
      val (commands, _) = fold_map export_command segments (Toplevel.make_state NONE);
    in element "theory"
      [("name", Context.theory_long_name thy), ("source", File.symbolic_path source)]
      (flat commands)
    end;

  fun export_interfaces () =
    let
      (* Borrow only the retained PolyML descriptor: the bootstrap namespace also
         contains early versions of Position/YXML unsuitable for this exporter. *)
      val bootstrap = Context.Theory (Thy_Info.get_theory "ML_Bootstrap");
      val polyml = Context.setmp_generic_context (SOME bootstrap)
        (fn () => #lookupStruct ML_Env.name_space "PolyML") ()
        |> (fn SOME value => value | NONE => error "Missing retained bootstrap PolyML");
      val context = Context.Theory (Thy_Info.get_theory "HOL.List")
        |> Config.put_generic ML_Env.ML_write_global false;
    in Context.setmp_generic_context (SOME context)
      (fn () =>
        (#enterStruct ML_Env.name_space ("PolyML", polyml);
         use "/work/session/export_interfaces.ML")) () end;

  fun observe session theories =
    let
      val _ = if session = "Reference_Execution" then ()
        else error ("Unexpected reference observer session: " ^ session);
      val _ = List.app (fn name =>
        if exists (fn (thy, _) => Context.theory_long_name thy = name) theories then ()
        else error ("Missing executed reference root: " ^ name)) roots;
      val snapshot = element "execution_snapshot"
        [("version", "1"), ("reference", "Isabelle2025"), ("session", session)]
        [element "roots" [] (map (named "root") roots),
         element "initial_theories" [] (map (named "theory") initial_theories),
         element "theories" [] (map export_theory theories)];
      val _ = YXML.write_body (Path.explode "/work/inventory/execution.yxml") [snapshot];
      val _ = use "/work/session/export_reference.ML";
      val _ = export_interfaces ();
      val _ = use "/work/session/export_bootstrap.ML";
    in writeln ("Observed executed theories: " ^ string_of_int (length theories)) end;
in
  val _ = Build.add_hook observe;
end;
