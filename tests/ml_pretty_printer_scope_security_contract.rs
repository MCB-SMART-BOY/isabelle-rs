use isabelle_rs::ml::{DenyHost, Value, Vm};

fn evaluate(source: &str) -> Vm {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate("pretty-printer-scope-security.sml", source)
        .expect("valid printer scope program should evaluate");
    vm
}

fn text<'a>(vm: &'a Vm, name: &str) -> &'a str {
    vm.lookup_value(name).expect("active VM").and_then(Value::as_text).expect("string binding")
}

#[test]
fn printer_outer_raw_registration_does_not_disclose_nested_opaque_alias() {
    let vm = evaluate(
        r#"
        structure Outer = struct
          structure Raw = struct datatype t = Wrap of string end;
          val _ = PolyML.addPrettyPrinter
            (fn _ => fn _ => fn Raw.Wrap value => PolyML.PrettyString ("raw:" ^ value));
          structure Secret :> sig type t val item: t end = struct
            datatype t = datatype Raw.t;
            val item = Wrap "private-marker"
          end;
          val public = Raw.Wrap "visible"
        end;
        val public_result = case PolyML.prettyRepresentation (Outer.public, 8) of
          PolyML.PrettyString value => value | _ => "unexpected";
        val hidden_result = case PolyML.prettyRepresentation (Outer.Secret.item, 8) of
          PolyML.PrettyString value => value | _ => "unexpected";
        "#,
    );
    assert_eq!(text(&vm, "public_result"), "raw:visible");
    assert_eq!(text(&vm, "hidden_result"), "<opaque>");
}

#[test]
fn printer_resealed_inherited_snapshot_remains_available() {
    let vm = evaluate(
        r#"
        structure Outer = struct
          structure Printed :> sig type t val item: t end = struct
            datatype t = Wrap of string;
            val item = Wrap "visible";
            val _ = PolyML.addPrettyPrinter
              (fn _ => fn _ => fn Wrap value => PolyML.PrettyString ("printed:" ^ value))
          end;
          structure Reexport :> sig type t val item: t end = struct
            type t = Printed.t;
            val item = Printed.item
          end
        end;
        val inherited_result = case PolyML.prettyRepresentation (Outer.Reexport.item, 8) of
          PolyML.PrettyString value => value | _ => "unexpected";
        "#,
    );
    assert_eq!(text(&vm, "inherited_result"), "printed:visible");
}
