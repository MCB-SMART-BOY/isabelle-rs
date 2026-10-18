(* Isabelle2025 reference observation only: no theorem is authorized by this output. *)
local
  val roots =
    ["HOL.HOL", "HOL.Orderings", "HOL.Set", "HOL.Nat", "HOL.List", "HOL.Fun",
     "HOL.Product_Type", "HOL.Sum_Type", "HOL.Option"];
  val output = Path.explode "/work/inventory/inventory.yxml";

  fun element name attributes children = XML.Elem ((name, attributes), children);
  fun text name value = element name [] [XML.Text value];
  fun attribute name value = (name, value);
  fun encode_type T = element "type" [] (Term_XML.Encode.typ T);
  fun encode_sort S = element "sort" [] (Term_XML.Encode.sort S);
  fun encode_term t = element "term" [] (Term_XML.Encode.term_raw t);
  fun encode_name name = attribute "name" name;
  fun encode_entry ((Defs.Const, name), args) =
        element "entry" [("kind", "const"), encode_name name] (map encode_type args)
    | encode_entry ((Defs.Type, name), args) =
        element "entry" [("kind", "type"), encode_name name] (map encode_type args);
  fun encode_group name children = element name [] children;
  fun encode_named tag name children = element tag [encode_name name] children;
  fun encode_theorem_name (name, index) =
    [("name", name), ("index", string_of_int index)];
  fun encode_reference tag (id: Proofterm.thm_id, name) =
    element tag
      (encode_theorem_name name @
        [("origin", #theory_name id), ("serial", string_of_int (#serial id))]) [];

  fun is_new get_space name thy =
    not (exists (fn parent => Name_Space.declared (get_space parent) name)
      (Theory.parents_of thy));

  fun export_types thy =
    let
      val types = #types (Type.rep_tsig (Sign.tsig_of thy));
      fun export (name, decl) =
        if not (is_new Sign.type_space name thy) then []
        else
          let
            val detail =
              (case decl of
                Type.Logical_Type arity =>
                  ("logical", [("arity", string_of_int arity)], [])
              | Type.Abbreviation (args, rhs, is_syntax) =>
                  ("abbreviation", [("syntax", Bool.toString is_syntax)],
                   map (text "parameter") args @ [encode_type rhs])
              | Type.Nonterminal => ("nonterminal", [], []));
            val (kind, attributes, children) = detail;
          in [element "type_declaration" (encode_name name :: ("kind", kind) :: attributes)
                children] end;
    in maps export (Name_Space.dest_table types) |> encode_group "types" end;

  fun export_classes thy =
    let
      val algebra = #2 (#classes (Type.rep_tsig (Sign.tsig_of thy)));
      val names = Graph.keys (Sorts.classes_of algebra) |> sort_strings;
      fun export name =
        if not (is_new Sign.class_space name thy) then []
        else
          let
            val info = try (Axclass.get_info thy) name;
            val (params, axioms) =
              (case info of
                NONE => ([], [])
              | SOME {params, axioms, ...} => (params, axioms));
            val details =
              [encode_group "parameters"
                (map (fn (param, T) => encode_named "parameter" param [encode_type T]) params),
               encode_group "class_axioms"
                (map (encode_term o Thm.plain_prop_of o Thm.transfer thy) axioms)];
          in [element "class"
                [encode_name name, ("info_available", Bool.toString (is_some info))] details] end;
      val {classrel, arities} =
        Sorts.dest_algebra
          (map (#2 o #classes o Type.rep_tsig o Sign.tsig_of) (Theory.parents_of thy))
          algebra;
      val relations =
        maps (fn (sub, supers) => map (fn super =>
          element "class_relation" [("sub", sub), ("super", super)] []) supers) classrel;
      val arity_entries =
        map (fn (constructor, sorts, class) =>
          element "arity" [("type", constructor), ("class", class)]
            (map encode_sort sorts)) arities;
    in [encode_group "classes" (maps export names),
        encode_group "class_relations" relations,
        encode_group "arities" arity_entries] end;

  fun export_constants thy =
    let
      val consts = Sign.consts_of thy;
      fun export (name, (T, abbrev)) =
        if not (is_new Sign.const_space name thy) then []
        else
          [encode_named "constant" name
            ([encode_type T] @
             (case abbrev of NONE => [] | SOME rhs => [encode_named "abbreviation" name [encode_term rhs]]))];
    in #constants (Consts.dest consts) |> sort_by #1 |> maps export
       |> encode_group "constants" end;

  fun export_axioms thy =
    Theory.all_axioms_of thy
    |> filter (fn (name, _) => is_new Theory.axiom_space name thy)
    |> sort_by #1
    |> map (fn (name, prop) => encode_named "axiom" name [encode_term prop])
    |> encode_group "axioms";

  fun export_definitions thy =
    let
      val parents = Theory.parents_of thy;
      fun parent_has item (spec: Defs.spec) =
        exists (fn parent =>
          exists (fn previous =>
            #description previous = #description spec andalso #lhs previous = #lhs spec andalso
            #rhs previous = #rhs spec andalso #def previous = #def spec)
            (Defs.specifications_of (Theory.defs_of parent) item)) parents;
      fun export_spec (item, spec: Defs.spec) =
        if parent_has item spec then []
        else
          [element "specification"
            [("description", #description spec),
             ("axiom_name", the_default "" (#def spec)),
             ("has_axiom_name", Bool.toString (is_some (#def spec)))]
            [encode_group "subject" [encode_entry (item, #lhs spec)],
             encode_group "dependencies" (map encode_entry (#rhs spec))]];
      val specs = Defs.all_specifications_of (Theory.defs_of thy)
        |> maps (fn (item, entries) => maps (fn spec => export_spec (item, spec)) entries)
        |> sort_by YXML.string_of;
      val constdefs =
        Defs.dest_constdefs (map Theory.defs_of parents) (Theory.defs_of thy)
        |> sort_by #1
        |> map (fn (constant, axiom) =>
          element "constant_definition" [("constant", constant), ("axiom", axiom)] []);
    in [encode_group "specifications" specs, encode_group "constant_definitions" constdefs] end;

  fun export_oracle (name, proposition) =
    element "oracle" [encode_name name]
      (case proposition of NONE => [] | SOME prop => [encode_term prop]);

  fun export_thm thy (index, raw) =
    let
      val th = Thm.transfer thy raw;
      val owner = Thm.theory_long_name th;
      val dependencies = Thm_Deps.thm_deps thy [th]
        |> map (encode_reference "dependency") |> sort_by YXML.string_of;
      val oracles = Thm_Deps.all_oracles [th]
        |> map (fn ((name, _), prop) => (name, prop))
        |> sort (prod_ord string_ord (option_ord Term_Ord.term_ord))
        |> map export_oracle;
      val tpairs = Thm.tpairs_of th
        |> map (fn (left, right) => encode_group "tpair" [encode_term left, encode_term right]);
    in
      element "theorem"
        (encode_theorem_name index @ [("owner", owner),
          ("derivation_name", Thm_Name.print (Thm.derivation_name th)),
          ("has_skip_proof", Bool.toString (Thm_Deps.has_skip_proof [th]))])
        [encode_group "proposition" [encode_term (Thm.prop_of th)],
         encode_group "hypotheses" (map encode_term (Thm.hyps_of th)),
         encode_group "shyps" (map encode_sort (Thm.shyps_of th)),
         encode_group "tpairs" tpairs,
         encode_group "dependencies" dependencies,
         encode_group "oracle_footprint" oracles]
    end;

  fun export_facts thy =
    let
      val facts = Global_Theory.facts_of thy;
      val parents = Theory.parents_of thy;
      val space = Global_Theory.fact_space thy;
      val groups = Facts.dest_static true (map Global_Theory.facts_of parents) facts;
      fun export (name, thms) =
        encode_named "fact_group" name
          (map (export_thm thy) (Thm_Name.make_list (name, thms)));
      val indexes = Name_Space.get_names space |> sort_strings
        |> filter (fn name => is_new Global_Theory.fact_space name thy)
        |> map (fn name =>
          element "fact_index"
            [encode_name name,
             ("concealed", Bool.toString (Name_Space.is_concealed space name)),
             ("dynamic", Bool.toString (Facts.is_dynamic facts name)),
             ("origin", #theory_long_name (Name_Space.the_entry space name))] []);
      val theorem_names = Global_Theory.dest_thm_names thy
        |> map (fn (id, (name, _)) => encode_reference "named_derivation" (id, name))
        |> sort_by YXML.string_of;
    in [encode_group "fact_indexes" indexes,
        encode_group "fact_groups" (map export groups),
        encode_group "named_derivations" theorem_names] end;

  fun export_node thy =
    let
      val name = Context.theory_long_name thy;
      val master = File.symbolic_path (Resources.master_directory thy);
      val source = File.symbolic_path
        (Resources.master_directory thy +
          Resources.thy_path (Path.basic (Context.theory_base_name thy)));
      val parents = Theory.parents_of thy
        |> map (fn parent => element "parent"
             [encode_name (Context.theory_long_name parent)] []);
      val raw_imports = Resources.imports_of thy
        |> map (fn (spec, _) => text "import_specification" spec);
      val registrations = Name_Space.get_names (Thm.oracle_space thy) |> sort_strings
        |> filter (fn oracle => is_new Thm.oracle_space oracle thy)
        |> map (fn oracle => encode_named "oracle_registration" oracle []);
    in
      element "theory" [encode_name name, ("master_directory", master), ("source", source)]
        ([encode_group "parents" parents, encode_group "import_specifications" raw_imports,
          element "default_sort" [] (Term_XML.Encode.sort
            (#default (Type.rep_tsig (Sign.tsig_of thy)))),
          export_types thy] @ export_classes thy @
         [export_constants thy, export_axioms thy] @ export_definitions thy @
         export_facts thy @ [encode_group "oracle_registrations" registrations])
    end;

  fun require_root name =
    let val thy = Thy_Info.get_theory name
    in if Context.theory_long_name thy = name then thy
       else error ("Expected exact root " ^ quote name ^ ", got " ^
         quote (Context.theory_long_name thy)) end;

  val root_theories = map require_root roots;
  val nodes = maps Theory.nodes_of root_theories
    |> distinct (fn (a, b) => Context.theory_long_name a = Context.theory_long_name b)
    |> sort_by Context.theory_long_name;
  val names = map Context.theory_long_name nodes;
  val _ = if length names = length (distinct (op =) names) then ()
    else error "Repeated theory identity in reference closure";
  val _ = List.app (fn thy =>
    List.app (fn parent =>
      if member (op =) names (Context.theory_long_name parent) then ()
      else error ("Missing parent of " ^ Context.theory_long_name thy))
      (Theory.parents_of thy)) nodes;
  val coverage =
    ["static_theory_snapshot", "raw_named_static_facts", "registered_oracles",
     "transitive_oracle_footprints", "named_theorem_dependencies"];
  val unavailable =
    ["executed_commands", "ML_load_events", "resource_load_events",
     "anonymous_ephemeral_facts", "unregistered_proof_steps",
     "external_process_events", "dynamic_fact_evaluations"];
  val snapshot =
    element "reference_snapshot" [("version", "1"), ("reference", "Isabelle2025")]
      [encode_group "roots" (map (fn name => encode_named "root" name []) roots),
       encode_group "coverage" (map (fn item => text "observed" item) coverage @
         map (fn item => text "unavailable" item) unavailable),
       encode_group "theories" (map export_node nodes)];
  val _ = YXML.write_body output [snapshot];
in end;
