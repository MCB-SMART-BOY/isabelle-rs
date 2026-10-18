//! Pure computational Basis primitives used by Isabelle's General bootstrap.
use super::types::{Type, TypeScheme};
use super::value::{NativeFunctionId, ValueData};
use super::{MlError, MlErrorKind, NativeFunction, Value, Vm};
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::rc::Rc;

#[path = "basis/collections.rs"]
mod collections;
#[path = "basis/exception_runtime.rs"]
mod exception_runtime;
#[path = "basis/heap.rs"]
mod heap;
#[path = "basis/interfaces.rs"]
mod interfaces;
#[path = "basis/lists.rs"]
mod lists;
#[path = "basis/numbers.rs"]
mod numbers;
#[cfg(unix)]
#[path = "basis/os_path.rs"]
mod os_path;
#[path = "basis/poly_compiler.rs"]
mod poly_compiler;
#[path = "basis/poly_namespace.rs"]
mod poly_namespace;
#[path = "basis/printers.rs"]
pub(super) mod printers;
#[path = "basis/real.rs"]
mod real;
#[path = "basis/statistics.rs"]
pub(super) mod statistics;
#[path = "basis/substring.rs"]
mod substring;
#[path = "basis/text.rs"]
mod text;
#[path = "basis/thread_runtime.rs"]
mod thread_runtime;
#[path = "basis/thread_sync.rs"]
mod thread_sync;
#[path = "basis/time.rs"]
mod time;
#[path = "basis/weak.rs"]
mod weak;
#[path = "basis/word32.rs"]
mod word32;

fn typ(name: &str) -> Type {
    Type::Constructor(name.to_owned(), vec![])
}
fn var(id: u64) -> Type {
    Type::Variable(id)
}
fn container(name: &str, item: Type) -> Type {
    Type::Constructor(name.to_owned(), vec![item])
}
fn function(input: Type, output: Type) -> Type {
    Type::Function(Box::new(input), Box::new(output))
}
fn pair(first: Type, second: Type) -> Type {
    Type::Record(BTreeMap::from([("1".to_owned(), first), ("2".to_owned(), second)]), false)
}
fn triple(first: Type, second: Type, third: Type) -> Type {
    Type::Record(
        BTreeMap::from([
            ("1".to_owned(), first),
            ("2".to_owned(), second),
            ("3".to_owned(), third),
        ]),
        false,
    )
}
fn scheme(ids: &[u64], body: Type) -> TypeScheme {
    TypeScheme::polymorphic(ids.to_vec(), body)
}

impl Vm {
    pub(super) fn apply_native(
        &mut self,
        id: NativeFunctionId,
        collected: &[Value],
        collected_types: &[Option<Type>],
        collected_result: Option<&Type>,
        certified_argument: Option<&Type>,
        argument: &Value,
    ) -> Result<Value, MlError> {
        if !id.belongs_to(self.runtime_id, self.generation) {
            self.request_stop();
            return Err(self.error(
                MlErrorKind::HostFailure,
                "apply native",
                "foreign runtime native function",
            ));
        }
        let Some((callback, arity)) = self.native_functions.get(id.index()).copied() else {
            self.request_stop();
            return Err(self.error(
                MlErrorKind::HostFailure,
                "apply native",
                "unregistered native function",
            ));
        };
        let invocation = self
            .typed_arguments
            .last()
            .filter(|invocation| invocation.target == super::TypedInvocationTarget::Native(id));
        let mut current_type = certified_argument.cloned().or_else(|| {
            invocation.map(|invocation| self.resolve_typed_evidence(&invocation.argument))
        });
        let mut result_type = invocation
            .and_then(|invocation| invocation.result.as_ref())
            .map(|result| self.resolve_typed_evidence(result));
        let mut argument_types = collected_types.to_vec();
        if let (Some(Type::Function(expected, output)), Some(actual)) =
            (collected_result, current_type.as_ref())
        {
            let mut substitutions = BTreeMap::new();
            if !super::merge_type_template(expected, actual, &mut substitutions) {
                return Err(self.error(
                    MlErrorKind::HostFailure,
                    "apply native",
                    "compiler-certified partial application types do not unify",
                ));
            }
            for typ in argument_types.iter_mut().flatten() {
                *typ = typ.substitute(&substitutions);
            }
            current_type = current_type.map(|typ| typ.substitute(&substitutions));
            result_type = Some(output.substitute(&substitutions));
        }
        let mut arguments = Vec::with_capacity(arity);
        arguments.extend_from_slice(collected);
        arguments.push(argument.clone());
        argument_types.push(current_type.clone());
        if arguments.len() < arity {
            return Ok(self.track_value(Value(Rc::new(ValueData::NativePartial {
                id,
                arguments: RefCell::new(arguments),
                argument_types: RefCell::new(argument_types),
                result_type: RefCell::new(result_type),
            }))));
        }
        self.invoke_complete_native(id, callback, arguments, argument_types, current_type)
    }

    fn invoke_complete_native(
        &mut self,
        id: NativeFunctionId,
        callback: NativeFunction,
        arguments: Vec<Value>,
        argument_types: Vec<Option<Type>>,
        current_type: Option<Type>,
    ) -> Result<Value, MlError> {
        let result = if let Some(intrinsic) = self.type_directed_natives.get(&id).cloned() {
            if self.untyped_apply_depth > 0 {
                return Err(self.error(
                    MlErrorKind::Type,
                    "apply type-directed primitive",
                    "untyped Vm::apply argument cannot reach a type-directed primitive",
                ));
            }
            let certified = current_type.ok_or_else(|| {
                self.error(
                    MlErrorKind::Type,
                    "apply type-directed primitive",
                    "untyped Vm::apply cannot invoke a type-directed primitive",
                )
            })?;
            printers::invoke(self, intrinsic, &arguments, &certified)
        } else {
            self.native_argument_types.push(argument_types);
            let result = callback(self, &arguments);
            self.native_argument_types.pop();
            result
        };
        self.finish_native_result(result)
    }

    fn finish_native_result(&mut self, result: Result<Value, MlError>) -> Result<Value, MlError> {
        match result {
            Err(error) if matches!(error.kind, MlErrorKind::Exception(_)) => {
                self.validate_exception_error(&error, "apply native")?;
                Err(error)
            },
            Err(error)
                if matches!(
                    error.kind,
                    MlErrorKind::HostPermission | MlErrorKind::HostFailure | MlErrorKind::Stopped
                ) =>
            {
                self.request_stop();
                Err(error)
            },
            other => other,
        }
    }

    fn register_pure(
        &mut self,
        name: &str,
        ids: &[u64],
        body: Type,
        arity: usize,
        callback: NativeFunction,
    ) {
        let value = self.create_native(arity, callback);
        self.register_value(name, scheme(ids, body), value);
    }

    fn create_native(&mut self, arity: usize, callback: NativeFunction) -> Value {
        let id =
            NativeFunctionId::new(self.runtime_id, self.generation, self.native_functions.len());
        self.native_functions.push((callback, arity));
        Value::native(id)
    }

    /// Construct the actual VM-local Basis option, not a forged constructor.
    pub fn make_option(&mut self, value: Option<Value>) -> Result<Value, MlError> {
        self.check_stop()?;
        Ok(text::option(self, value))
    }

    pub(super) fn register_exception(&mut self, name: &str, aliases: &[&str]) {
        let value = Value(Rc::new(ValueData::Exception {
            identity: self.fresh_identity(),
            name: name.to_owned(),
            argument: None,
        }));
        self.basis_exceptions.insert(name.to_owned(), value.clone());
        for alias in aliases {
            self.register_value(alias, TypeScheme::mono(typ("exn")), value.clone());
        }
    }

    pub(super) fn install_pure_basis(&mut self) {
        self.type_environment.register_type("option", 1, true);
        self.type_environment.register_type("vector", 1, true);
        self.register_exception("Option", &["Option.Option"]);
        self.register_exception("Subscript", &["Subscript", "General.Subscript"]);
        self.register_exception("Size", &["Size", "General.Size"]);
        self.register_exception("Chr", &["Chr", "Char.Chr"]);
        self.register_exception("Ord", &["SML90.Ord"]);
        let none_stamp = self.fresh_identity();
        self.option_none_stamp = none_stamp;
        let none = Value(Rc::new(ValueData::Constructor {
            stamp: none_stamp,
            name: "NONE".to_owned(),
            argument: None,
        }));
        let none_scheme = scheme(&[1], container("option", var(1)));
        self.register_value("NONE", none_scheme.clone(), none.clone());
        self.register_value("Option.NONE", none_scheme, none);
        let some_stamp = self.fresh_identity();
        self.option_some_stamp = some_stamp;
        let some = Value(Rc::new(ValueData::ConstructorFunction {
            stamp: some_stamp,
            name: "SOME".to_owned(),
        }));
        let some_scheme = scheme(&[1], function(var(1), container("option", var(1))));
        self.register_value("SOME", some_scheme.clone(), some.clone());
        self.register_value("Option.SOME", some_scheme, some);
        self.install_option_list();
        text::install(self);
        substring::install(self);
        self.install_vectors_arrays();
        lists::install(self);
        interfaces::install(self);
        heap::install(self);
        exception_runtime::install(self);
        self.install_polyml_identity_basis();
        numbers::install(self);
        real::install(self);
        thread_runtime::install(self);
        time::install(self);
        #[cfg(unix)]
        os_path::install(self);
        thread_sync::install(self);
        weak::install(self);
        statistics::install(self);
        poly_namespace::install(self);
        poly_compiler::install(self);
        self.install_standard_general_bindings();
        self.register_pure(
            "o",
            &[1, 2, 3],
            function(
                pair(function(var(2), var(3)), function(var(1), var(2))),
                function(var(1), var(3)),
            ),
            1,
            compose,
        );
        self.register_pure("not", &[], function(typ("bool"), typ("bool")), 1, bool_not);
        self.register_pure("before", &[1], function(pair(var(1), typ("unit")), var(1)), 1, before);
        let int_pair = pair(typ("int"), typ("int"));
        for (name, cb) in [("Int.<", less as NativeFunction), ("Int.>=", greater_equal)] {
            self.register_pure(name, &[], function(int_pair.clone(), typ("bool")), 1, cb);
        }
    }

    fn install_standard_general_bindings(&mut self) {
        for (name, qualified) in [
            ("map", "List.map"),
            ("app", "List.app"),
            ("foldl", "List.foldl"),
            ("foldr", "List.foldr"),
            ("hd", "List.hd"),
            ("tl", "List.tl"),
            ("null", "List.null"),
            ("length", "List.length"),
            ("rev", "List.rev"),
            ("concat", "List.concat"),
            ("chr", "Char.chr"),
            ("ord", "Char.ord"),
            ("explode", "String.explode"),
            ("implode", "String.implode"),
            ("str", "String.str"),
            ("valOf", "Option.valOf"),
            ("isSome", "Option.isSome"),
            ("getOpt", "Option.getOpt"),
        ] {
            let Some(scheme) = self.type_environment.lookup(qualified).cloned() else {
                continue;
            };
            let Some(value) = self.values.get(qualified).cloned() else {
                continue;
            };
            self.register_value(name, scheme, value);
        }
    }

    fn install_option_list(&mut self) {
        let opt = container("option", var(1));
        let list = container("list", var(1));
        self.register_value(
            "nil",
            scheme(&[1], list.clone()),
            Value(Rc::new(ValueData::List(Vec::new()))),
        );
        self.type_environment.register_value_constructor("nil");
        self.values.mark_constructor("nil");
        self.register_pure(
            "::",
            &[1],
            function(pair(var(1), list.clone()), list.clone()),
            1,
            list_cons,
        );
        self.type_environment.register_value_constructor("::");
        self.values.mark_constructor("::");
        for (name, cb) in [
            ("Option.isSome", option_is_some as NativeFunction),
            ("Option.valOf", option_val_of),
            ("Option.getOpt", option_get_opt),
        ] {
            let body = match name {
                "Option.isSome" => function(opt.clone(), typ("bool")),
                "Option.valOf" => function(opt.clone(), var(1)),
                _ => function(pair(opt.clone(), var(1)), var(1)),
            };
            self.register_pure(name, &[1], body, 1, cb);
        }
        for (name, callback, output) in [
            ("List.null", list_null as NativeFunction, typ("bool")),
            ("List.length", list_length, typ("int")),
            ("List.hd", list_hd, var(1)),
            ("List.tl", list_tl, list.clone()),
            ("List.rev", list_rev, list.clone()),
        ] {
            self.register_pure(name, &[1], function(list.clone(), output), 1, callback);
        }
        self.register_exception("Empty", &["List.Empty"]);
        self.register_pure(
            "@",
            &[1],
            function(pair(list.clone(), list.clone()), list.clone()),
            1,
            list_append,
        );
        self.register_pure(
            "List.nth",
            &[1],
            function(pair(list.clone(), typ("int")), var(1)),
            1,
            list_nth,
        );
        self.register_pure(
            "List.map",
            &[1, 2],
            function(function(var(1), var(2)), function(list.clone(), container("list", var(2)))),
            2,
            list_map,
        );
        self.register_pure(
            "List.app",
            &[1],
            function(function(var(1), typ("unit")), function(list.clone(), typ("unit"))),
            2,
            list_app,
        );
        for (name, callback) in
            [("List.exists", list_exists as NativeFunction), ("List.all", list_all)]
        {
            self.register_pure(
                name,
                &[1],
                function(function(var(1), typ("bool")), function(list.clone(), typ("bool"))),
                2,
                callback,
            );
        }
        for (name, callback) in
            [("List.foldl", list_foldl as NativeFunction), ("List.foldr", list_foldr)]
        {
            self.register_pure(
                name,
                &[1, 2],
                function(
                    function(pair(var(1), var(2)), var(2)),
                    function(var(2), function(list.clone(), var(2))),
                ),
                3,
                callback,
            );
        }
    }

    fn install_vectors_arrays(&mut self) {
        collections::install(self);
    }
}
impl Vm {
    fn install_polyml_identity_basis(&mut self) {
        let string = typ("string");
        self.register_pure("SML90.ord", &[], function(string.clone(), typ("int")), 1, sml90_ord);
        self.register_pure("SML90.chr", &[], function(typ("int"), string.clone()), 1, sml90_chr);
        self.register_pure(
            "SML90.explode",
            &[],
            function(string.clone(), container("list", string.clone())),
            1,
            sml90_explode,
        );
        self.register_pure(
            "SML90.implode",
            &[],
            function(container("list", string.clone()), string),
            1,
            sml90_implode,
        );
        self.register_pure(
            "PolyML.pointerEq",
            &[1],
            function(pair(var(1), var(1)), typ("bool")),
            1,
            polyml_pointer_eq,
        );
    }
}

fn before(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let [first, second] = fields(vm, arg(vm, args, 0, "before")?, 2, "before")? else {
        return Err(vm.error(MlErrorKind::Type, "before", "expected pair"));
    };
    if !second.is_unit() {
        return Err(vm.error(MlErrorKind::Type, "before", "expected unit effect"));
    }
    Ok(first.clone())
}

fn sml90_ord(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let text = arg(vm, args, 0, "SML90.ord")?
        .as_bytes()
        .ok_or_else(|| vm.error(MlErrorKind::Type, "SML90.ord", "expected string"))?;
    let first = text
        .first()
        .ok_or_else(|| vm.raise_basis("Ord", "SML90.ord", "empty string".to_owned()))?;
    Ok(Value::int(i64::from(*first)))
}

fn sml90_chr(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let code = arg(vm, args, 0, "SML90.chr")?
        .as_int()
        .ok_or_else(|| vm.error(MlErrorKind::Type, "SML90.chr", "expected int"))?;
    let byte = u8::try_from(code)
        .map_err(|_| vm.raise_basis("Chr", "SML90.chr", format!("character code {code}")))?;
    Ok(Value::bytes(vec![byte]))
}

fn sml90_explode(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let text = arg(vm, args, 0, "SML90.explode")?
        .as_bytes()
        .ok_or_else(|| vm.error(MlErrorKind::Type, "SML90.explode", "expected string"))?;
    let mut result = Vec::with_capacity(text.len());
    for &byte in text {
        vm.check_stop()?;
        result.push(Value::bytes(vec![byte]));
    }
    Ok(Value::list(result))
}

fn sml90_implode(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let values = arg(vm, args, 0, "SML90.implode")?
        .as_list()
        .ok_or_else(|| vm.error(MlErrorKind::Type, "SML90.implode", "expected string list"))?;
    let mut result = Vec::new();
    for value in values {
        vm.check_stop()?;
        let bytes = value.as_bytes().ok_or_else(|| {
            vm.error(MlErrorKind::Type, "SML90.implode", "expected string member")
        })?;
        result.extend_from_slice(bytes);
    }
    Ok(Value::bytes(result))
}

fn polyml_pointer_eq(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let operands = fields(vm, arg(vm, args, 0, "PolyML.pointerEq")?, 2, "PolyML.pointerEq")?;
    let is_same = match (&*operands[0].0, &*operands[1].0) {
        (ValueData::Int(left), ValueData::Int(right)) => left == right,
        (ValueData::Word(left), ValueData::Word(right)) => left == right,
        (ValueData::Word32(left), ValueData::Word32(right)) => left == right,
        (ValueData::Bool(left), ValueData::Bool(right)) => left == right,
        (ValueData::Character(left), ValueData::Character(right)) => left == right,
        (ValueData::Unit, ValueData::Unit) => true,
        _ => operands[0].is_same_object(&operands[1]),
    };
    Ok(Value::bool(is_same))
}

fn arg<'a>(
    vm: &Vm,
    args: &'a [Value],
    index: usize,
    operation: &str,
) -> Result<&'a Value, MlError> {
    args.get(index)
        .ok_or_else(|| vm.error(MlErrorKind::Type, operation, format!("missing argument {index}")))
}
fn fields<'a>(
    vm: &Vm,
    value: &'a Value,
    count: usize,
    operation: &str,
) -> Result<&'a [Value], MlError> {
    match &*value.0 {
        ValueData::Tuple(values) if values.len() == count => Ok(values),
        _ => Err(vm.error(MlErrorKind::Type, operation, format!("expected {count}-tuple"))),
    }
}
fn items<'a>(vm: &Vm, value: &'a Value, operation: &str) -> Result<&'a [Value], MlError> {
    match &*value.0 {
        ValueData::List(values) | ValueData::Vector(values) => Ok(values),
        _ => Err(vm.error(MlErrorKind::Type, operation, "expected immutable sequence")),
    }
}
fn index(vm: &Vm, index: &Value, length: usize, operation: &str) -> Result<usize, MlError> {
    let value = index
        .as_int()
        .ok_or_else(|| vm.error(MlErrorKind::Type, operation, "expected integer index"))?;
    usize::try_from(value).ok().filter(|index| *index < length).ok_or_else(|| {
        vm.raise_basis("Subscript", operation, format!("index {value}, length {length}"))
    })
}
fn size(vm: &Vm, value: &Value, operation: &str) -> Result<usize, MlError> {
    let value = value
        .as_int()
        .ok_or_else(|| vm.error(MlErrorKind::Type, operation, "expected integer size"))?;
    usize::try_from(value).map_err(|_| vm.raise_basis("Size", operation, format!("size {value}")))
}
impl Vm {
    fn raise_basis(&self, name: &str, operation: &str, cause: String) -> MlError {
        let Some(exception) = self.basis_exceptions.get(name).cloned() else {
            return self.error(
                MlErrorKind::HostFailure,
                operation,
                format!("missing Basis exception {name}: {cause}"),
            );
        };
        let ValueData::Exception { identity, .. } = &*exception.0 else {
            return self.error(
                MlErrorKind::HostFailure,
                operation,
                format!("invalid Basis exception {name}: {cause}"),
            );
        };
        let mut error = self.error(MlErrorKind::Exception(*identity), operation, cause);
        error.exception = Some(exception);
        error
    }
}
fn option_argument<'a>(
    vm: &Vm,
    value: &'a Value,
    operation: &str,
) -> Result<Option<&'a Value>, MlError> {
    match &*value.0 {
        ValueData::Constructor { stamp, argument: Some(value), .. }
            if *stamp == vm.option_some_stamp =>
        {
            Ok(Some(value))
        },
        ValueData::Constructor { stamp, argument: None, .. } if *stamp == vm.option_none_stamp => {
            Ok(None)
        },
        _ => Err(vm.error(MlErrorKind::Type, operation, "expected option")),
    }
}
fn option_is_some(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    Ok(Value::bool(
        option_argument(vm, arg(vm, args, 0, "Option.isSome")?, "Option.isSome")?.is_some(),
    ))
}
fn option_val_of(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    option_argument(vm, arg(vm, args, 0, "Option.valOf")?, "Option.valOf")?
        .cloned()
        .ok_or_else(|| vm.raise_basis("Option", "Option.valOf", "NONE".to_owned()))
}
fn option_get_opt(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let pair = fields(vm, arg(vm, args, 0, "Option.getOpt")?, 2, "Option.getOpt")?;
    Ok(option_argument(vm, &pair[0], "Option.getOpt")?.unwrap_or(&pair[1]).clone())
}
fn list_null(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    Ok(Value::bool(items(vm, arg(vm, args, 0, "List.null")?, "List.null")?.is_empty()))
}
fn list_length(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    Ok(Value::int(items(vm, arg(vm, args, 0, "List.length")?, "List.length")?.len() as i64))
}
fn list_hd(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    items(vm, arg(vm, args, 0, "List.hd")?, "List.hd")?
        .first()
        .cloned()
        .ok_or_else(|| vm.raise_basis("Empty", "List.hd", "empty list".to_owned()))
}
fn list_tl(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let list = items(vm, arg(vm, args, 0, "List.tl")?, "List.tl")?;
    if list.is_empty() {
        return Err(vm.raise_basis("Empty", "List.tl", "empty list".to_owned()));
    }
    Ok(vm.track_value(Value(Rc::new(ValueData::List(list[1..].to_vec())))))
}
fn list_rev(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let mut list = items(vm, arg(vm, args, 0, "List.rev")?, "List.rev")?.to_vec();
    list.reverse();
    Ok(vm.track_value(Value(Rc::new(ValueData::List(list)))))
}
fn list_cons(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let [head, tail] = fields(vm, arg(vm, args, 0, "::")?, 2, "::")? else {
        return Err(vm.error(MlErrorKind::Type, "::", "expected pair"));
    };
    let tail = items(vm, tail, "::")?;
    let mut list = Vec::with_capacity(tail.len() + 1);
    list.push(head.clone());
    list.extend_from_slice(tail);
    Ok(vm.track_value(Value(Rc::new(ValueData::List(list)))))
}
fn list_append(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let [left, right] = fields(vm, arg(vm, args, 0, "@")?, 2, "@")? else {
        return Err(vm.error(MlErrorKind::Type, "@", "expected pair"));
    };
    let mut result = items(vm, left, "@")?.to_vec();
    result.extend_from_slice(items(vm, right, "@")?);
    Ok(vm.track_value(Value(Rc::new(ValueData::List(result)))))
}
fn list_nth(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let [list, position] = fields(vm, arg(vm, args, 0, "List.nth")?, 2, "List.nth")? else {
        return Err(vm.error(MlErrorKind::Type, "List.nth", "expected pair"));
    };
    let list = items(vm, list, "List.nth")?;
    Ok(list[index(vm, position, list.len(), "List.nth")?].clone())
}
fn list_map(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let values = items(vm, arg(vm, args, 1, "List.map")?, "List.map")?;
    let mut result = Vec::with_capacity(values.len());
    for value in values {
        vm.check_stop()?;
        result.push(apply_native_callback(vm, &args[0], value)?);
    }
    Ok(vm.track_value(Value(Rc::new(ValueData::List(result)))))
}
fn list_app(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let values = items(vm, arg(vm, args, 1, "List.app")?, "List.app")?;
    for value in values {
        vm.check_stop()?;
        apply_native_callback(vm, &args[0], value)?;
    }
    Ok(Value::unit())
}
fn predicate(vm: &mut Vm, args: &[Value], all: bool, operation: &str) -> Result<Value, MlError> {
    let values = items(vm, arg(vm, args, 1, operation)?, operation)?;
    for value in values {
        vm.check_stop()?;
        let answer = apply_native_callback(vm, &args[0], value)?.as_bool().ok_or_else(|| {
            vm.error(MlErrorKind::Type, operation, "predicate did not return bool")
        })?;
        if answer != all {
            return Ok(Value::bool(!all));
        }
    }
    Ok(Value::bool(all))
}
fn list_exists(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    predicate(vm, args, false, "List.exists")
}
fn list_all(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    predicate(vm, args, true, "List.all")
}
fn fold(vm: &mut Vm, args: &[Value], reverse: bool, operation: &str) -> Result<Value, MlError> {
    let values = items(vm, arg(vm, args, 2, operation)?, operation)?;
    let mut accumulator = args[1].clone();
    if reverse {
        for value in values.iter().rev() {
            vm.check_stop()?;
            accumulator = fold_step(vm, &args[0], value, accumulator)?;
        }
    } else {
        for value in values {
            vm.check_stop()?;
            accumulator = fold_step(vm, &args[0], value, accumulator)?;
        }
    }
    Ok(accumulator)
}
fn list_foldl(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    fold(vm, args, false, "List.foldl")
}
fn list_foldr(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    fold(vm, args, true, "List.foldr")
}
fn fold_step(vm: &mut Vm, callback: &Value, item: &Value, state: Value) -> Result<Value, MlError> {
    let tuple = vm.track_value(Value(Rc::new(ValueData::Tuple(vec![item.clone(), state]))));
    apply_native_callback(vm, callback, &tuple)
}
fn apply_native_callback(
    vm: &mut Vm,
    callback: &Value,
    argument: &Value,
) -> Result<Value, MlError> {
    let callback_type = vm.native_argument_type(0).ok_or_else(|| {
        vm.error(
            MlErrorKind::HostFailure,
            "apply native callback",
            "missing compiler-certified callback type",
        )
    })?;
    let Type::Function(input, _) = callback_type else {
        return Err(vm.error(
            MlErrorKind::HostFailure,
            "apply native callback",
            "compiler-certified callback is not a function",
        ));
    };
    vm.apply_with_type(callback, argument, *input)
}
fn compose(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let [first, second] = fields(vm, arg(vm, args, 0, "o")?, 2, "o")? else {
        return Err(vm.error(MlErrorKind::Type, "o", "expected pair"));
    };
    let Type::Record(types, false) = vm.native_argument_type(0).ok_or_else(|| {
        vm.error(MlErrorKind::HostFailure, "o", "missing compiler-certified composition type")
    })?
    else {
        return Err(vm.error(MlErrorKind::HostFailure, "o", "composition type is not a pair"));
    };
    let first_type = types
        .get("1")
        .cloned()
        .ok_or_else(|| vm.error(MlErrorKind::HostFailure, "o", "missing first function type"))?;
    let second_type = types
        .get("2")
        .cloned()
        .ok_or_else(|| vm.error(MlErrorKind::HostFailure, "o", "missing second function type"))?;
    let id = NativeFunctionId::new(vm.runtime_id, vm.generation, vm.native_functions.len());
    vm.native_functions.push((apply_composition, 3));
    let result_type = vm.native_result_type();
    Ok(vm.track_value(Value(Rc::new(ValueData::NativePartial {
        id,
        arguments: RefCell::new(vec![first.clone(), second.clone()]),
        argument_types: RefCell::new(vec![Some(first_type), Some(second_type)]),
        result_type: RefCell::new(result_type),
    }))))
}

fn apply_composition(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let second_type = vm.native_argument_type(1).ok_or_else(|| {
        vm.error(MlErrorKind::HostFailure, "o", "missing second function evidence")
    })?;
    let Type::Function(second_input, _) = second_type else {
        return Err(vm.error(MlErrorKind::HostFailure, "o", "second operand is not a function"));
    };
    let intermediate = vm.apply_with_type(&args[1], &args[2], *second_input)?;
    let first_type = vm.native_argument_type(0).ok_or_else(|| {
        vm.error(MlErrorKind::HostFailure, "o", "missing first function evidence")
    })?;
    let Type::Function(first_input, _) = first_type else {
        return Err(vm.error(MlErrorKind::HostFailure, "o", "first operand is not a function"));
    };
    vm.apply_with_type(&args[0], &intermediate, *first_input)
}
fn compare_int(vm: &Vm, args: &[Value], operation: &str) -> Result<(i64, i64), MlError> {
    let [left, right] = fields(vm, arg(vm, args, 0, operation)?, 2, operation)? else {
        return Err(vm.error(MlErrorKind::Type, operation, "expected pair"));
    };
    Ok((
        left.as_int().ok_or_else(|| vm.error(MlErrorKind::Type, operation, "expected int"))?,
        right.as_int().ok_or_else(|| vm.error(MlErrorKind::Type, operation, "expected int"))?,
    ))
}
fn less(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let (a, b) = compare_int(vm, args, "Int.<")?;
    Ok(Value::bool(a < b))
}
fn greater_equal(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let (a, b) = compare_int(vm, args, "Int.>=")?;
    Ok(Value::bool(a >= b))
}
fn bool_not(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let value = arg(vm, args, 0, "not")?
        .as_bool()
        .ok_or_else(|| vm.error(MlErrorKind::Type, "not", "expected bool"))?;
    Ok(Value::bool(!value))
}
