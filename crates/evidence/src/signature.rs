//! Structural source-signature checks for diagnostic terms; never proof authority.
use std::collections::{BTreeMap, BTreeSet};

use serde_json::Value;

use crate::EvidenceError;
use crate::common::{as_array, as_str, field, require};
use crate::compare_syntax::{SyntaxScope, validate_sort};

pub(crate) struct SignatureCache<'a> {
    inventory: &'a Value,
    entries: BTreeMap<String, Signature<'a>>,
}

impl<'a> SignatureCache<'a> {
    pub(crate) fn new(inventory: &'a Value) -> Self {
        Self { inventory, entries: BTreeMap::new() }
    }

    pub(crate) fn get(&mut self, theory: &str) -> Result<&Signature<'a>, EvidenceError> {
        if !self.entries.contains_key(theory) {
            self.entries
                .insert(theory.to_owned(), Signature::from_inventory(self.inventory, theory)?);
        }
        self.entries
            .get(theory)
            .ok_or_else(|| EvidenceError::Input(format!("missing cached signature {theory}")))
    }
}

pub(crate) struct Signature<'a> {
    types: BTreeMap<&'a str, &'a Value>,
    constants: BTreeMap<&'a str, &'a Value>,
    classes: BTreeSet<&'a str>,
}

impl<'a> Signature<'a> {
    pub(crate) fn from_inventory(
        inventory: &'a Value,
        theory_name: &str,
    ) -> Result<Self, EvidenceError> {
        let theories = as_array(field(inventory, "theories")?, "inventory theories")?;
        let mut signature =
            Self { types: BTreeMap::new(), constants: BTreeMap::new(), classes: BTreeSet::new() };
        let start = theories.iter().find(|item| item["name"] == theory_name).ok_or_else(|| {
            EvidenceError::Input(format!("unknown signature theory {theory_name}"))
        })?;
        let mut stack = vec![start];
        let mut visited = BTreeSet::new();
        while let Some(theory) = stack.pop() {
            let name = as_str(field(theory, "name")?, "signature theory")?;
            if !visited.insert(name) {
                continue;
            }
            signature.extend_declarations(theory)?;
            for parent in as_array(field(theory, "parents")?, "signature parents")? {
                let parent_name = as_str(parent, "signature parent")?;
                let ancestor =
                    theories.iter().find(|item| item["name"] == parent_name).ok_or_else(|| {
                        EvidenceError::Input(format!("unknown signature parent {parent_name}"))
                    })?;
                stack.push(ancestor);
            }
        }
        Ok(signature)
    }

    fn extend_declarations(&mut self, theory: &'a Value) -> Result<(), EvidenceError> {
        for entry in as_array(field(theory, "types")?, "type declarations")? {
            let name = as_str(field(entry, "name")?, "type name")?;
            require(
                self.types.insert(name, entry).is_none(),
                format!("duplicate visible type {name}"),
            )?;
        }
        for entry in as_array(field(theory, "constants")?, "constant declarations")? {
            let name = as_str(field(entry, "name")?, "constant name")?;
            require(
                self.constants.insert(name, entry).is_none(),
                format!("duplicate visible constant {name}"),
            )?;
        }
        for entry in as_array(field(theory, "classes")?, "class declarations")? {
            let name = as_str(field(entry, "name")?, "class name")?;
            require(self.classes.insert(name), format!("duplicate visible class {name}"))?;
        }
        Ok(())
    }

    pub(crate) fn validate_declared_sort(&self, value: &Value) -> Result<(), EvidenceError> {
        validate_sort(value)?;
        for class in as_array(value, "sort")? {
            let name = as_str(class, "sort class")?;
            require(self.classes.contains(name), format!("undeclared sort class {name}"))?;
        }
        Ok(())
    }

    pub(crate) fn validate_type(&self, typ: &Value) -> Result<(), EvidenceError> {
        match as_str(field(typ, "kind")?, "type kind")? {
            "Type" => {
                let name = as_str(field(typ, "name")?, "type constructor")?;
                let declaration = self.types.get(name).ok_or_else(|| {
                    EvidenceError::Input(format!("undeclared type constructor {name}"))
                })?;
                let arguments = as_array(field(typ, "args")?, "type arguments")?;
                let arity =
                    match as_str(field(declaration, "storage_kind")?, "type declaration kind")? {
                        "logical" => field(declaration, "arity")?.as_u64(),
                        "abbreviation" => Some(
                            as_array(field(declaration, "parameters")?, "abbreviation parameters")?
                                .len() as u64,
                        ),
                        _ => None,
                    };
                require(
                    arity == Some(arguments.len() as u64),
                    format!("invalid {name} type arity"),
                )?;
                for argument in arguments {
                    self.validate_type(argument)?;
                }
            },
            "TFree" | "TVar" => self.validate_declared_sort(field(typ, "sort")?)?,
            kind => return Err(EvidenceError::Input(format!("unknown type kind {kind}"))),
        }
        Ok(())
    }

    pub(crate) fn validate_term(&self, term: &Value) -> Result<(), EvidenceError> {
        match as_str(field(term, "kind")?, "term kind")? {
            "Const" => {
                let name = as_str(field(term, "name")?, "constant occurrence")?;
                let declaration = self
                    .constants
                    .get(name)
                    .ok_or_else(|| EvidenceError::Input(format!("undeclared constant {name}")))?;
                let typ = field(term, "type")?;
                self.validate_type(typ)?;
                let scheme = field(declaration, "type")?;
                self.validate_type(scheme)?;
                require(
                    is_type_instance(scheme, typ, &mut BTreeMap::new())?,
                    format!("constant {name} does not instantiate its declared type"),
                )?;
            },
            "Free" | "Var" => self.validate_type(field(term, "type")?)?,
            "Abs" => {
                self.validate_type(
                    term.get("binder_type").or_else(|| term.get("type")).ok_or_else(|| {
                        EvidenceError::Input("abstraction has no binder type".into())
                    })?,
                )?;
                self.validate_term(field(term, "body")?)?;
            },
            "App" => {
                self.validate_term(field(term, "function")?)?;
                self.validate_term(field(term, "argument")?)?;
            },
            "Bound" => {},
            kind => return Err(EvidenceError::Input(format!("unknown term kind {kind}"))),
        }
        Ok(())
    }

    pub(crate) fn validate_judgment(&self, statement: &Value) -> Result<(), EvidenceError> {
        SyntaxScope::default().validate_judgment(statement)?;
        self.validate_term(field(statement, "proposition")?)?;
        for hypothesis in as_array(field(statement, "hypotheses")?, "hypotheses")? {
            self.validate_term(hypothesis)?;
        }
        for pair in as_array(field(statement, "tpairs")?, "tpairs")? {
            for term in as_array(pair, "tpair")? {
                self.validate_term(term)?;
            }
        }
        for sort in as_array(field(statement, "shyps")?, "shyps")? {
            self.validate_declared_sort(sort)?;
        }
        Ok(())
    }
}

fn is_type_instance<'a>(
    scheme: &'a Value,
    actual: &'a Value,
    substitutions: &mut BTreeMap<(&'a str, &'a str, Option<u64>), &'a Value>,
) -> Result<bool, EvidenceError> {
    let kind = as_str(field(scheme, "kind")?, "constant scheme kind")?;
    if kind != "Type" {
        let identity = (
            kind,
            as_str(field(scheme, "name")?, "scheme variable")?,
            scheme.get("index").and_then(Value::as_u64),
        );
        if let Some(previous) = substitutions.get(&identity) {
            return Ok(*previous == actual);
        }
        substitutions.insert(identity, actual);
        return Ok(true);
    }
    if actual["kind"] != "Type" || actual["name"] != scheme["name"] {
        return Ok(false);
    }
    let args = as_array(field(scheme, "args")?, "scheme arguments")?;
    let instances = as_array(field(actual, "args")?, "instance arguments")?;
    if args.len() != instances.len() {
        return Ok(false);
    }
    for (expected, found) in args.iter().zip(instances) {
        if !is_type_instance(expected, found, substitutions)? {
            return Ok(false);
        }
    }
    Ok(true)
}
