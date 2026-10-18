(* Isabelle2025 reference-only registry/ML declarations; never theorem authority or a call trace. *)
local
  val roots =
    ["HOL.HOL", "HOL.Orderings", "HOL.Set", "HOL.Nat", "HOL.List", "HOL.Fun",
     "HOL.Product_Type", "HOL.Sum_Type", "HOL.Option"];
  val output = Path.explode "/work/inventory/interfaces.yxml";
  val type_print_depth = 40;
  val selected_structures =
    ["Thm", "Type", "Sign", "Consts", "Defs", "Theory", "Context", "Proofterm",
     "ML_Compiler", "ML_Env", "ML_Name_Space", "ML_Context", "Thread", "OS",
     "TextIO", "BinIO", "PolyML"];

  fun element tag attributes children = XML.Elem ((tag, attributes), children);
  fun named tag name children = element tag [("name", name)] children;
  fun group tag children = element tag [] children;
  fun text tag value = element tag [] [XML.Text value];
  fun optional_attribute name value =
    (case value of NONE => [] | SOME x => [(name, x)]);

  fun declaration_position properties =
    (case get_first (fn PolyML.PTdeclaredAt loc => SOME loc | _ => NONE) properties of
      NONE => element "declaration_position" [("availability", "unavailable")] []
    | SOME loc =>
        let val pos = Exn_Properties.position_of_polyml_location loc in
          element "declaration_position"
            ([("availability", "available")] @
              optional_attribute "file" (Position.file_of pos) @
              optional_attribute "line" (Option.map string_of_int (Position.line_of pos)) @
              optional_attribute "offset" (Option.map string_of_int (Position.offset_of pos))) []
        end);

  fun resolved_names all lookup =
    let
      fun resolve name =
        (case lookup name of
          SOME entry => (name, entry)
        | NONE => error ("ML namespace entry disappeared: " ^ quote name));
    in map resolve (sort_distinct string_ord (map #1 (all ()))) end;

  fun export_value space (name, value) =
    let
      val type_text =
        PolyML.NameSpace.Values.printType
          (PolyML.NameSpace.Values.typeof value, type_print_depth, SOME space)
        |> Pretty.from_ML |> Pretty.string_of |> YXML.parse_body |> XML.content_of;
    in element "value" [("name", name), ("type_print_depth", FixedInt.toString type_print_depth)]
      [declaration_position (PolyML.NameSpace.Values.properties value),
       text "type_text" type_text]
    end;

  fun export_type (name, constructor) =
    named "type_constructor" name
      [declaration_position (PolyML.NameSpace.TypeConstrs.properties constructor)];
  fun export_signature (name, signature_value) =
    named "signature" name
      [declaration_position (PolyML.NameSpace.Signatures.properties signature_value),
       element "members" [("availability", "unavailable"),
         ("reason", "no_public_signature_contents_api")] []];
  fun export_functor (name, functor_value) =
    named "functor" name
      [declaration_position (PolyML.NameSpace.Functors.properties functor_value),
       element "members" [("availability", "unavailable"),
         ("reason", "no_public_functor_contents_api")] []];

  fun export_namespace space include_top_level =
    let
      val values = resolved_names (#allVal space) (#lookupVal space)
        |> map (export_value space) |> group "values";
      val types = resolved_names (#allType space) (#lookupType space)
        |> map export_type |> group "type_constructors";
      val signatures =
        if include_top_level then
          resolved_names (#allSig space) (#lookupSig space) |> map export_signature
        else [];
      val functors =
        if include_top_level then
          resolved_names (#allFunct space) (#lookupFunct space) |> map export_functor
        else [];
    in [values, types, group "signatures" signatures, group "functors" functors] end;

  fun export_structure space path name =
    (case #lookupStruct space name of
      NONE => element "structure"
        [("name", name), ("path", path), ("availability", "unavailable"),
         ("reason", "not_in_theory_namespace")] []
    | SOME structure_value =>
        let
          val contents = PolyML.NameSpace.Structures.contents structure_value;
          val children = resolved_names (#allStruct contents) (#lookupStruct contents)
            |> map (fn (child, _) => export_structure contents (path ^ "." ^ child) child);
        in element "structure" [("name", name), ("path", path), ("availability", "available")]
          (declaration_position (PolyML.NameSpace.Structures.properties structure_value) ::
            export_namespace contents false @ [group "structures" children])
        end);

  fun export_commands thy =
    let
      val keywords = Thy_Header.get_keywords thy;
      val ctxt = Proof_Context.init_global thy;
      fun command name =
        let
          val _ = Outer_Syntax.check_command ctxt (name, Position.none);
          val kind = (case Keyword.command_kind keywords name of
            SOME value => value | NONE => error ("Missing kind for command " ^ quote name));
          val registration =
            if member (op =) Thy_Header.bootstrap_thys (Context.theory_base_name thy)
            then "keyword_only_bootstrap" else "at_end_checked";
        in element "command"
          [("name", name), ("kind", kind), ("registration", registration)] [] end;
    in Keyword.dest_commands keywords |> sort_strings |> map command |> group "commands" end;

  fun export_theory thy =
    Context.setmp_generic_context (SOME (Context.Theory thy))
      (fn () =>
        let
          val space = ML_Env.name_space;
          val top_level = export_namespace space true;
          val structures = map (fn name => export_structure space name name) selected_structures;
        in named "theory" (Context.theory_long_name thy)
          [export_commands thy, element "ml_abi"
            [("read_global", Bool.toString (Config.get_global thy ML_Env.ML_read_global))]
            (top_level @ [group "selected_structures" structures])]
        end) ();

  fun require_root name =
    let val thy = Thy_Info.get_theory name in
      if Context.theory_long_name thy = name then thy
      else error ("Expected exact root " ^ quote name) end;
  val nodes = maps Theory.nodes_of (map require_root roots)
    |> distinct (fn (a, b) => Context.theory_long_name a = Context.theory_long_name b)
    |> sort_by Context.theory_long_name;
  val names = map Context.theory_long_name nodes;
  val _ = if length names = length (distinct (op =) names) then ()
    else error "Repeated theory identity in interface closure";
  val _ = List.app (fn thy => List.app (fn parent =>
    if member (op =) names (Context.theory_long_name parent) then ()
    else error ("Missing parent of " ^ Context.theory_long_name thy))
    (Theory.parents_of thy)) nodes;
  val snapshot = element "interface_snapshot"
    [("version", "1"), ("reference", "Isabelle2025"),
     ("authorization", "none_reference_requirements_only"),
     ("type_text_semantics", "display_only_not_structural_type_identity"),
     ("namespace_semantics", "theory_tables_with_current_global_fallback_when_enabled")]
    [group "roots" (map (fn root => named "root" root []) roots),
     group "coverage"
       [named "observed" "theory_scoped_command_keywords_and_kinds" [],
        named "observed" "selected_public_ml_namespace_declarations" [],
        named "unavailable" "runtime_call_graph" [],
        named "unavailable" "signature_and_functor_members" [],
        named "unavailable" "private_bootstrap_runtime_structures" []],
     group "theories" (map export_theory nodes),
     group "bootstrap_interfaces" [export_theory (Thy_Info.get_theory "ML_Bootstrap")]];
  val _ = YXML.write_body output [snapshot];
in end;
