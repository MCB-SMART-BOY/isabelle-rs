//! Basis signatures share the registered native value schemes, not ML lookup state.
use super::Vm;
use crate::ml::{Specification, TypeExpr, value::Signature};
use std::rc::Rc;

#[derive(Clone, Copy)]
struct NativeTypeSpec {
    name: &'static str,
    parameters: &'static [&'static str],
    has_equality: bool,
    is_eqtype: bool,
}

const VECTOR_TYPE: NativeTypeSpec =
    NativeTypeSpec { name: "vector", parameters: &["'a"], has_equality: true, is_eqtype: true };
const ARRAY_TYPE: NativeTypeSpec =
    NativeTypeSpec { name: "array", parameters: &["'a"], has_equality: true, is_eqtype: true };
const CHAR_TYPE: NativeTypeSpec =
    NativeTypeSpec { name: "char", parameters: &[], has_equality: true, is_eqtype: true };
const STRING_TYPE: NativeTypeSpec =
    NativeTypeSpec { name: "string", parameters: &[], has_equality: true, is_eqtype: true };
const SUBSTRING_TYPE: NativeTypeSpec =
    NativeTypeSpec { name: "substring", parameters: &[], has_equality: false, is_eqtype: false };

pub(super) fn install(vm: &mut Vm) {
    let interfaces: &[(&str, &str, &[NativeTypeSpec], &[&str])] = &[
        ("Vector", "VECTOR", &[VECTOR_TYPE], &[]),
        ("Array", "ARRAY", &[ARRAY_TYPE, NativeTypeSpec { is_eqtype: false, ..VECTOR_TYPE }], &[]),
        (
            "String",
            "STRING",
            &[STRING_TYPE, CHAR_TYPE],
            &["nth", "exists", "forall", "member", "fold", "fold_rev"],
        ),
        ("Char", "CHAR", &[CHAR_TYPE, STRING_TYPE], &["Chr"]),
        (
            "Substring",
            "SUBSTRING",
            &[SUBSTRING_TYPE, CHAR_TYPE, STRING_TYPE],
            &["Span", "empty", "all"],
        ),
    ];
    // Capture all Basis namespaces before signatures refer to global text types.
    for &(structure, _, types, _) in interfaces {
        install_type_aliases(vm, structure, types);
    }
    for &(structure, signature, types, excluded_values) in interfaces {
        install_interface(vm, structure, signature, types, excluded_values);
    }
}

fn install_type_aliases(vm: &mut Vm, structure: &str, types: &[NativeTypeSpec]) {
    let namespace = vm.structures.entry(structure.to_owned()).or_default();
    for &NativeTypeSpec { name, parameters, has_equality, .. } in types {
        // These are aliases of the original Basis types; no generative stamp.
        namespace.type_environment.register_type(name, parameters.len(), has_equality);
        namespace.types.insert(name.to_owned(), 0);
    }
    vm.type_environment.register_namespace(structure, namespace);
}

fn install_interface(
    vm: &mut Vm,
    structure: &str,
    signature: &str,
    types: &[NativeTypeSpec],
    excluded_values: &[&str],
) {
    let namespace = vm.structures.entry(structure.to_owned()).or_default();
    let mut specifications = types
        .iter()
        .map(|specification| Specification::Type {
            name: specification.name.to_owned(),
            parameters: specification.parameters.iter().map(|name| (*name).to_owned()).collect(),
            equality: specification.is_eqtype,
            definition: None,
        })
        .collect::<Vec<_>>();
    for mut specification in namespace.type_environment.value_specifications() {
        let Specification::Value(name, ty) = &mut specification else { continue };
        if excluded_values.contains(&name.as_str()) {
            continue;
        }
        if matches!(structure, "String" | "Char") {
            qualify_text_conversion(name, ty);
        }
        specifications.push(specification);
    }
    vm.signatures.insert(
        signature.to_owned(),
        Signature { specifications, type_environment: Rc::new(vm.type_environment.clone()) },
    );
}

fn qualify_text_conversion(name: &str, ty: &mut TypeExpr) {
    let TypeExpr::Function(input, output) = ty else { return };
    // Poly/ML StringSignatures.sml distinguishes global conversion/reader types
    // from the signature's abstract char/string, especially after :> sealing.
    match name {
        "fromString" | "fromCString" => qualify_type(input, "string", "String.string"),
        "toString" | "toCString" => qualify_type(output, "string", "String.string"),
        "scan" => qualify_type(input, "char", "Char.char"),
        _ => {},
    }
}

fn qualify_type(ty: &mut TypeExpr, local: &str, global: &str) {
    match ty {
        TypeExpr::Named(name, arguments) => {
            if name == local {
                *name = global.to_owned();
            }
            for argument in arguments {
                qualify_type(argument, local, global);
            }
        },
        TypeExpr::Function(input, output) => {
            qualify_type(input, local, global);
            qualify_type(output, local, global);
        },
        TypeExpr::Tuple(fields) => {
            for field in fields {
                qualify_type(field, local, global);
            }
        },
        TypeExpr::Record(fields) => {
            for (_, field) in fields {
                qualify_type(field, local, global);
            }
        },
        TypeExpr::Var(_) => {},
    }
}
