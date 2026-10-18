(* Reference input order, not a compiler call trace or Rust theorem authority. *)
local
  val source_names = ["ROOT0.ML", "ROOT.ML"];
  val source_root = Path.explode "~~/src/Pure";
  val load_commands = ["ML_file", "ML_file_debug", "ML_file_no_debug"];
  val heading_commands =
    ["chapter", "section", "subsection", "subsubsection", "paragraph", "subparagraph"];
  fun element name attributes children = XML.Elem ((name, attributes), children);
  fun require_line token =
    (case Position.line_of (ML_Lex.pos_of token) of
      SOME line => string_of_int line
    | NONE => error "Missing bootstrap statement line");
  fun decode_argument token =
    if ML_Lex.kind_of token <> ML_Lex.String then
      error "Non-literal bootstrap argument"
    else
      (case ML_Lex.content_of token |> unprefix "\"" |> unsuffix "\"" |> String.fromString of
        SOME value => value
      | NONE => error "Malformed bootstrap string argument");
  fun export_load argument =
    let val path = File.full_path source_root (Path.explode argument) in
      element "file" [("path", File.symbolic_path path),
        ("sha1", SHA1.rep (SHA1.digest (File.read path)))] []
    end;
  fun export_statement name_token argument_token terminator =
    let
      val name = ML_Lex.content_of name_token;
      val argument = decode_argument argument_token;
      val is_load = member (op =) load_commands name;
      val _ = if ML_Lex.is_ident_with (K true) name_token andalso
        (is_load orelse member (op =) heading_commands name) andalso
        ML_Lex.content_of terminator = ";" then ()
        else error ("Unsupported bootstrap source statement: " ^ name);
    in element "statement"
      [("command", name), ("kind", if is_load then "load" else "heading"),
       ("argument", argument), ("line", require_line name_token)]
      (if is_load then [export_load argument] else [])
    end;
  fun export_statements [] = []
    | export_statements (name :: argument :: terminator :: rest) =
        export_statement name argument terminator :: export_statements rest
    | export_statements _ = error "Incomplete bootstrap source statement";
  fun export_source name =
    let
      val path = source_root + Path.basic name;
      val source = File.read path;
      val tokens = ML_Lex.tokenize source |> filter_out ML_Lex.is_improper;
      val _ = if forall ML_Lex.is_regular tokens then ()
        else error ("Malformed bootstrap source: " ^ name);
    in element "source" [("path", File.symbolic_path path),
      ("sha1", SHA1.rep (SHA1.digest source))] (export_statements tokens)
    end;
  val snapshot = element "bootstrap_snapshot"
    [("version", "1"), ("reference", "Isabelle2025"),
     ("semantics", "source_declared_order_not_call_trace")]
    (map export_source source_names);
  val _ = YXML.write_body (Path.explode "/work/inventory/bootstrap.yxml") [snapshot];
in end;
