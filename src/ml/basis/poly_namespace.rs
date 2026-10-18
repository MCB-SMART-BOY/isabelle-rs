//! Live per-VM Poly/ML name-space tables used by the original compiler bootstrap.
use super::{
    MlError, MlErrorKind, NativeFunction, Type, TypeScheme, Value, ValueData, Vm, function, pair,
    typ,
};
use crate::ml::environment::ValueEnvironment;
use crate::ml::types::TypeConstructor;
use crate::ml::value::{Functor, Namespace, NativeFunctionId, Signature};
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::rc::Rc;

const KINDS: [(&str, &str); 6] = [
    ("Val", "Values.value"),
    ("Type", "TypeConstrs.typeConstr"),
    ("Fix", "Infixes.fixity"),
    ("Struct", "Structures.structureVal"),
    ("Sig", "Signatures.signatureVal"),
    ("Funct", "Functors.functorVal"),
];

#[derive(Clone)]
enum Entry {
    Value(Value, TypeScheme),
    Type(TypeConstructor),
    Fixity(crate::ml::syntax::Fixity),
    Structure(Namespace),
    Signature(Signature),
    Functor(Functor),
}

pub(super) fn install(vm: &mut Vm) {
    let mut fields = BTreeMap::new();
    for (suffix, type_name) in KINDS {
        let qualified = format!("PolyML.NameSpace.{type_name}");
        // Fresh Basis types belong to the new VM and cannot be rebuilt from SML bytes.
        vm.register_host_type(&qualified, 0, false).expect("fresh VM namespace type");
        let entry = typ(&qualified);
        let named_entry = pair(typ("string"), entry.clone());
        let all_type = function(typ("unit"), super::container("list", named_entry.clone()));
        let lookup_type = function(typ("string"), super::container("option", entry.clone()));
        let enter_type = function(named_entry, typ("unit"));
        fields.insert(format!("all{suffix}"), all_type);
        fields.insert(format!("lookup{suffix}"), lookup_type);
        fields.insert(format!("enter{suffix}"), enter_type);
    }
    let record_type = Type::Record(fields.clone(), false);
    vm.type_environment.register_alias("PolyML.NameSpace.nameSpace", vec![], record_type.clone());
    let mut methods = BTreeMap::new();
    for (kind, (suffix, _)) in KINDS.iter().enumerate() {
        for (prefix, callback) in [
            ("all", all_entries as NativeFunction),
            ("lookup", lookup_entry),
            ("enter", enter_entry),
        ] {
            let name = format!("{prefix}{suffix}");
            methods.insert(name, dispatch(vm, kind, callback));
        }
    }
    vm.register_value(
        "PolyML.globalNameSpace",
        TypeScheme::mono(record_type),
        Value(Rc::new(ValueData::Record(methods))),
    );
    let string = typ("string");
    let unit = typ("unit");
    vm.register_pure(
        "PolyML.Compiler.forgetValue",
        &[],
        function(string.clone(), unit.clone()),
        1,
        forget_value,
    );
    vm.register_pure(
        "PolyML.Compiler.forgetType",
        &[],
        function(string.clone(), unit.clone()),
        1,
        forget_type,
    );
    vm.register_pure(
        "PolyML.Compiler.forgetStructure",
        &[],
        function(string, unit),
        1,
        forget_structure,
    );
}

/// An ML wrapper may customize entry callbacks, but not silently redirect its lookup authority.
pub(super) fn check_wrapped_global(
    vm: &Vm,
    namespace: &Value,
    global: &Value,
) -> Result<(), MlError> {
    for (suffix, _) in KINDS {
        let field = format!("lookup{suffix}");
        let Some(expected) = global.record_field(&field) else {
            return Err(vm.error(
                MlErrorKind::HostFailure,
                "PolyML.compiler",
                "global namespace lacks lookup callback",
            ));
        };
        if namespace.record_field(&field) != Some(expected) {
            return Err(vm.error(MlErrorKind::Type, "PolyML.compiler",
                format!("custom namespace lookup {field} cannot be compiled against the global environment")));
        }
    }
    Ok(())
}

struct NamespaceSnapshot {
    values: ValueEnvironment,
    types: crate::ml::types::TypeEnvironment,
    fixities: crate::ml::parser::FixityEnvironment,
    structures: BTreeMap<String, Namespace>,
    signatures: BTreeMap<String, Signature>,
    functors: BTreeMap<String, Functor>,
}

impl NamespaceSnapshot {
    fn capture(vm: &Vm) -> Self {
        Self {
            values: vm.values.clone(),
            types: vm.type_environment.clone(),
            fixities: vm.fixities.clone(),
            structures: vm.structures.clone(),
            signatures: vm.signatures.clone(),
            functors: vm.functors.clone(),
        }
    }

    fn restore(self, vm: &mut Vm) {
        vm.values = self.values;
        vm.type_environment = self.types;
        vm.fixities = self.fixities;
        vm.structures = self.structures;
        vm.signatures = self.signatures;
        vm.functors = self.functors;
    }
}

fn changed_entries(vm: &Vm, original: &NamespaceSnapshot) -> Vec<(usize, String, Entry)> {
    let mut updates = Vec::new();
    for (name, value) in
        vm.values.iter().filter(|(name, value)| original.values.get(*name) != Some(*value))
    {
        if let Some(scheme) = vm.type_environment.lookup(name) {
            updates.push((0, name.clone(), Entry::Value(value.clone(), scheme.clone())));
        }
    }
    for (name, info) in &vm.type_environment.constructors {
        if !name.contains('.') && original.types.constructors.get(name) != Some(info) {
            updates.push((1, name.clone(), Entry::Type(info.clone())));
        }
    }
    for (name, fixity) in &vm.fixities {
        if original.fixities.get(name) != Some(fixity) {
            updates.push((2, name.clone(), Entry::Fixity(fixity.clone())));
        }
    }
    for (name, namespace) in &vm.structures {
        if !original.structures.contains_key(name) {
            updates.push((3, name.clone(), Entry::Structure(namespace.clone())));
        }
    }
    for (name, signature) in &vm.signatures {
        if !original.signatures.contains_key(name) {
            updates.push((4, name.clone(), Entry::Signature(signature.clone())));
        }
    }
    for (name, functor) in &vm.functors {
        if !original.functors.contains_key(name) {
            updates.push((5, name.clone(), Entry::Functor(functor.clone())));
        }
    }
    updates
}

pub(super) fn execute_wrapped_global(
    vm: &mut Vm,
    namespace: &Value,
    run: impl FnOnce(&mut Vm) -> Result<(), MlError>,
) -> Result<(), MlError> {
    let original = NamespaceSnapshot::capture(vm);
    let result = run(vm);
    let updates = if result.is_ok() { changed_entries(vm, &original) } else { Vec::new() };
    original.restore(vm);
    result?;
    for (kind, name, entry) in updates {
        vm.check_stop()?;
        let field = format!("enter{}", KINDS[kind].0);
        let callback = namespace
            .record_field(&field)
            .ok_or_else(|| {
                vm.error(MlErrorKind::Type, "PolyML.compiler", format!("namespace lacks {field}"))
            })?
            .clone();
        let entry_type = typ(&format!("PolyML.NameSpace.{}", KINDS[kind].1));
        let value = vm.insert_host_object(Rc::new(entry))?;
        vm.apply_with_type(
            &callback,
            &Value::tuple(vec![Value::text(name), value]),
            pair(typ("string"), entry_type),
        )?;
    }
    Ok(())
}

fn dispatch(vm: &mut Vm, kind: usize, callback: NativeFunction) -> Value {
    let id = NativeFunctionId::new(vm.runtime_id, vm.generation, vm.native_functions.len());
    vm.native_functions.push((callback, 2));
    vm.track_value(Value(Rc::new(ValueData::NativePartial {
        id,
        arguments: RefCell::new(vec![Value::int(kind as i64)]),
        argument_types: RefCell::new(vec![None]),
        result_type: RefCell::new(None),
    })))
}

fn decode_kind(vm: &Vm, args: &[Value], operation: &str) -> Result<usize, MlError> {
    let kind = args.first().and_then(Value::as_int).and_then(|kind| usize::try_from(kind).ok());
    kind.filter(|kind| *kind < KINDS.len()).ok_or_else(|| {
        vm.error(MlErrorKind::HostFailure, operation, "invalid native namespace descriptor")
    })
}

fn list_entries(vm: &Vm, kind: usize) -> Result<Vec<(String, Entry)>, MlError> {
    let entries = match kind {
        0 => {
            return vm
                .values
                .iter()
                .filter(|(name, _)| !name.contains('.'))
                .map(|(name, value)| {
                    let scheme = vm.type_environment.lookup(name).ok_or_else(|| {
                        vm.error(
                            MlErrorKind::HostFailure,
                            "PolyML.NameSpace.allVal",
                            format!("live value {name} has no elaborated type"),
                        )
                    })?;
                    Ok((name.clone(), Entry::Value(value.clone(), scheme.clone())))
                })
                .collect();
        },
        1 => vm
            .type_environment
            .constructors
            .iter()
            .filter(|(name, _)| !name.contains('.'))
            .map(|(name, info)| (name.clone(), Entry::Type(info.clone())))
            .collect(),
        2 => vm
            .fixities
            .iter()
            .map(|(name, fixity)| (name.clone(), Entry::Fixity(fixity.clone())))
            .collect(),
        3 => vm
            .structures
            .iter()
            .filter(|(name, _)| !name.starts_with("Native_"))
            .map(|(name, namespace)| (name.clone(), Entry::Structure(namespace.clone())))
            .collect(),
        4 => vm
            .signatures
            .iter()
            .map(|(name, signature)| (name.clone(), Entry::Signature(signature.clone())))
            .collect(),
        5 => vm
            .functors
            .iter()
            .map(|(name, functor)| (name.clone(), Entry::Functor(functor.clone())))
            .collect(),
        _ => {
            return Err(vm.error(
                MlErrorKind::HostFailure,
                "PolyML.NameSpace.all",
                "invalid namespace table kind",
            ));
        },
    };
    Ok(entries)
}
fn find_entry(vm: &Vm, kind: usize, name: &str) -> Option<Entry> {
    if name.starts_with("Native_") {
        return None;
    }
    match kind {
        0 => Some(Entry::Value(
            vm.values.get(name)?.clone(),
            vm.type_environment.lookup(name)?.clone(),
        )),
        1 => Some(Entry::Type(vm.type_environment.constructors.get(name)?.clone())),
        2 => Some(Entry::Fixity(vm.fixities.get(name)?.clone())),
        3 => Some(Entry::Structure(vm.structures.get(name)?.clone())),
        4 => Some(Entry::Signature(vm.signatures.get(name)?.clone())),
        5 => Some(Entry::Functor(vm.functors.get(name)?.clone())),
        _ => None,
    }
}
fn all_entries(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let kind = decode_kind(vm, args, "PolyML.NameSpace.all")?;
    if !args.get(1).is_some_and(Value::is_unit) {
        return Err(vm.error(MlErrorKind::Type, "PolyML.NameSpace.all", "expected unit"));
    }
    let entries = list_entries(vm, kind)?;
    let mut result = Vec::with_capacity(entries.len());
    for (name, entry) in entries {
        vm.check_stop()?;
        let value = vm.insert_host_object(Rc::new(entry))?;
        result.push(Value::tuple(vec![Value::text(name), value]));
    }
    Ok(Value::list(result))
}
fn lookup_entry(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let kind = decode_kind(vm, args, "PolyML.NameSpace.lookup")?;
    let name = args.get(1).and_then(Value::as_text).ok_or_else(|| {
        vm.error(MlErrorKind::Type, "PolyML.NameSpace.lookup", "expected name string")
    })?;
    let entry = find_entry(vm, kind, name);
    let value = entry.map(|entry| vm.insert_host_object(Rc::new(entry))).transpose()?;
    vm.make_option(value)
}
fn enter_entry(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let kind = decode_kind(vm, args, "PolyML.NameSpace.enter")?;
    let [name, object] = args.get(1).and_then(Value::as_tuple).ok_or_else(|| {
        vm.error(MlErrorKind::Type, "PolyML.NameSpace.enter", "expected name and entry")
    })?
    else {
        return Err(vm.error(MlErrorKind::Type, "PolyML.NameSpace.enter", "expected pair"));
    };
    let name = name.as_text().ok_or_else(|| {
        vm.error(MlErrorKind::Type, "PolyML.NameSpace.enter", "expected name string")
    })?;
    if name.starts_with("Native_") {
        return Err(vm.error(
            MlErrorKind::HostPermission,
            "PolyML.NameSpace.enter",
            format!("{name} is reserved for a private VM host bridge"),
        ));
    }
    let id = object.as_host_object().ok_or_else(|| {
        vm.error(MlErrorKind::Type, "PolyML.NameSpace.enter", "expected native namespace entry")
    })?;
    let owned = vm.get_host_object(id)?;
    let entry = owned.downcast::<Entry>().map_err(|_| {
        vm.error(MlErrorKind::Type, "PolyML.NameSpace.enter", "wrong native namespace entry kind")
    })?;
    match (kind, &*entry) {
        (0, Entry::Value(value, scheme)) => vm.register_value(name, scheme.clone(), value.clone()),
        (1, Entry::Type(info)) => {
            vm.type_environment.constructors.insert(name.to_owned(), info.clone());
        },
        (2, Entry::Fixity(fixity)) => {
            vm.fixities.insert(name.to_owned(), fixity.clone());
        },
        (3, Entry::Structure(namespace)) => {
            vm.type_environment.register_namespace(name, namespace);
            vm.values.bind_namespace(name, namespace);
            vm.structures.insert(name.to_owned(), namespace.clone());
        },
        (4, Entry::Signature(signature)) => {
            vm.signatures.insert(name.to_owned(), signature.clone());
        },
        (5, Entry::Functor(functor)) => {
            vm.functors.insert(name.to_owned(), functor.clone());
        },
        _ => {
            return Err(vm.error(
                MlErrorKind::Type,
                "PolyML.NameSpace.enter",
                "wrong native namespace entry kind",
            ));
        },
    }
    Ok(Value::unit())
}
fn forget_value(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let name = args.first().and_then(Value::as_text).ok_or_else(|| {
        vm.error(MlErrorKind::Type, "PolyML.Compiler.forgetValue", "expected name string")
    })?;
    vm.values.retain(|stored, _| stored != name);
    vm.type_environment.values.remove(name);
    vm.type_environment.constructor_values.remove(name);
    Ok(Value::unit())
}
fn forget_type(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let name = args.first().and_then(Value::as_text).ok_or_else(|| {
        vm.error(MlErrorKind::Type, "PolyML.Compiler.forgetType", "expected name string")
    })?;
    vm.type_environment.constructors.remove(name);
    Ok(Value::unit())
}
fn forget_structure(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let name = args.first().and_then(Value::as_text).ok_or_else(|| {
        vm.error(MlErrorKind::Type, "PolyML.Compiler.forgetStructure", "expected name string")
    })?;
    vm.structures.remove(name);
    let prefix = format!("{name}.");
    vm.values.retain(|stored, _| !stored.starts_with(&prefix));
    vm.type_environment.values.retain(|stored, _| !stored.starts_with(&prefix));
    vm.type_environment.constructors.retain(|stored, _| !stored.starts_with(&prefix));
    Ok(Value::unit())
}
