(* Reference-only observation of completed command states; not theorem authority. *)
local
  fun element tag attributes children = XML.Elem ((tag, attributes), children);
  fun command_info (segment: Document_Output.segment) =
    (case Command_Span.kind (#span segment) of
      Command_Span.Command_Span (name, pos) =>
        (name, (case Position.file_of pos of SOME file => file
          | NONE => error "Missing executed command source in fact observer"), #state segment)
    | Command_Span.Ignored_Span => error "Ignored executed span in fact observer"
    | Command_Span.Malformed_Span => error "Malformed executed span in fact observer");

  (* Namespace metadata is passive: Facts.dest_static forces stored lazy proofs. *)
  fun static_names thy =
    let val facts = Global_Theory.facts_of thy
    in Name_Space.get_names (Facts.space_of facts)
       |> filter_out (Facts.is_dynamic facts) end;

  fun observe_command theory (sequence, segment) (known, records) =
    let
      val (operation, source, state) = command_info segment;
      val current = if Toplevel.is_toplevel state then []
        else static_names (Toplevel.theory_of state);
      fun record name =
        element "fact_group" [
          ("theory", theory), ("sequence", string_of_int sequence),
          ("source", source), ("operation", operation), ("name", name)] [];
      val additions = filter_out (Symtab.defined known) current;
    in (fold (fn name => Symtab.update (name, ())) additions known,
        fold (fn name => cons (record name)) additions records) end;

  fun observe_theory (thy, segments) =
    let
      val theory = Context.theory_long_name thy;
      val commands = filter (fn segment =>
        (case Command_Span.kind (#span (segment: Document_Output.segment)) of
          Command_Span.Command_Span _ => true
        | Command_Span.Ignored_Span => false
        | Command_Span.Malformed_Span => error "Malformed executed span in fact observer"))
        segments;
      val indexed = map_index (fn (i, segment) => (i + 1, segment)) commands;
      val inherited = maps static_names (Theory.parents_of thy)
        |> fold (fn name => Symtab.update (name, ())) Symtab.empty;
      val (_, records) = fold (observe_command theory) indexed (inherited, []);
    in rev records end;

  fun observe session theories =
    if session <> "Reference_Execution" then
      error ("Unexpected fact observer session: " ^ session)
    else
      YXML.write_body (Path.explode "/work/inventory/fact-origins.yxml")
        [element "fact_observations" [("version", "1"), ("session", session)]
          (maps observe_theory theories)];
in
  val _ = Build.add_hook observe;
end;
