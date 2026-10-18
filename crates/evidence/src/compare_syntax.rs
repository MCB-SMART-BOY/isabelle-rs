//! Structural observation comparison, never proof checking or acceptance.
use std::collections::BTreeMap;

use serde_json::Value;

use super::common::{as_array, as_object, as_str, field, require, require_fields};
use crate::{EvidenceError, EvidenceError as StepError};

const MAX_SYNTAX_DEPTH: usize = 512;

pub fn require_index(value: &Value, context: &str) -> Result<u64, StepError> {
    value.as_u64().ok_or_else(|| EvidenceError::Input(format!("{context}: invalid index")))
}

fn require_name(value: &Value, context: &str) -> Result<(), StepError> {
    require(!as_str(value, context)?.is_empty(), format!("{context}: empty name"))
}

pub fn validate_sort(value: &Value) -> Result<(), StepError> {
    let classes = as_array(value, "sort")?;
    for (index, class) in classes.iter().enumerate() {
        require_name(class, "sort class")?;
        require(!classes[..index].contains(class), "sort: duplicate class")?;
    }
    Ok(())
}

fn same_sort(left: &Value, right: &Value) -> bool {
    match (left.as_array(), right.as_array()) {
        (Some(left), Some(right)) => {
            left.len() == right.len() && left.iter().all(|v| right.contains(v))
        },
        _ => false,
    }
}

#[derive(Default)]
pub struct SyntaxScope<'a> {
    annotations: BTreeMap<(&'a str, &'a str, Option<u64>), &'a Value>,
}

impl<'a> SyntaxScope<'a> {
    pub fn validate_type(&mut self, typ: &'a Value) -> Result<(), StepError> {
        self.validate_type_at(typ, 0)
    }

    fn validate_type_at(&mut self, typ: &'a Value, depth: usize) -> Result<(), StepError> {
        require(depth <= MAX_SYNTAX_DEPTH, "type nesting limit exceeded")?;
        let kind = as_str(field(typ, "kind")?, "type kind")?;
        require_name(field(typ, "name")?, "type constructor")?;
        if kind == "Type" {
            require_fields(typ, &["kind", "name", "args"], "type constructor")?;
            for argument in as_array(field(typ, "args")?, "type arguments")? {
                self.validate_type_at(argument, depth + 1)?;
            }
            return Ok(());
        }
        require(matches!(kind, "TFree" | "TVar"), format!("unknown type kind {kind:?}"))?;
        let fields = if kind == "TVar" {
            &["kind", "name", "sort", "index"][..]
        } else {
            &["kind", "name", "sort"][..]
        };
        require_fields(typ, fields, kind)?;
        let index =
            if kind == "TVar" { Some(require_index(field(typ, "index")?, kind)?) } else { None };
        let sort = field(typ, "sort")?;
        validate_sort(sort)?;
        let identity = (kind, as_str(field(typ, "name")?, kind)?, index);
        if let Some(previous) = self.annotations.insert(identity, sort) {
            require(same_sort(previous, sort), format!("{kind} {identity:?}: conflicting sorts"))?;
        }
        Ok(())
    }

    pub fn validate_term(&mut self, term: &'a Value) -> Result<(), StepError> {
        self.validate_term_at(term, 0, 0)
    }

    fn validate_term_at(
        &mut self,
        term: &'a Value,
        bound: u64,
        depth: usize,
    ) -> Result<(), StepError> {
        require(depth <= MAX_SYNTAX_DEPTH, "term nesting limit exceeded")?;
        let kind = as_str(field(term, "kind")?, "term kind")?;
        match kind {
            "Bound" => {
                require_fields(term, &["kind", "index"], kind)?;
                require(
                    require_index(field(term, "index")?, kind)? < bound,
                    "term: escaping Bound index",
                )
            },
            "Abs" => {
                let typ = if term.get("binder_type").is_some() {
                    require_fields(term, &["kind", "binder_type", "body"], "native Abs")?;
                    field(term, "binder_type")?
                } else {
                    require_fields(term, &["kind", "name", "type", "body"], kind)?;
                    as_str(field(term, "name")?, "Abs display name")?;
                    field(term, "type")?
                };
                self.validate_type(typ)?;
                self.validate_term_at(field(term, "body")?, bound + 1, depth + 1)
            },
            "App" => {
                require_fields(term, &["kind", "function", "argument"], kind)?;
                self.validate_term_at(field(term, "function")?, bound, depth + 1)?;
                self.validate_term_at(field(term, "argument")?, bound, depth + 1)
            },
            _ => {
                require(
                    matches!(kind, "Const" | "Free" | "Var"),
                    format!("unknown term {kind:?}"),
                )?;
                let fields = if kind == "Var" {
                    &["kind", "name", "type", "index"][..]
                } else {
                    &["kind", "name", "type"][..]
                };
                require_fields(term, fields, kind)?;
                require_name(field(term, "name")?, kind)?;
                if kind == "Var" {
                    require_index(field(term, "index")?, kind)?;
                }
                self.validate_type(field(term, "type")?)
            },
        }
    }

    pub fn validate_judgment(&mut self, value: &'a Value) -> Result<(), StepError> {
        self.validate_term(field(value, "proposition")?)?;
        for hypothesis in as_array(field(value, "hypotheses")?, "hypotheses")? {
            self.validate_term(hypothesis)?;
        }
        for sort in as_array(field(value, "shyps")?, "shyps")? {
            validate_sort(sort)?;
        }
        for pair in as_array(field(value, "tpairs")?, "tpairs")? {
            let pair = as_array(pair, "tpair")?;
            require(pair.len() == 2, "invalid tpair")?;
            for term in pair {
                self.validate_term(term)?;
            }
        }
        Ok(())
    }

    pub fn validate_record(&mut self, value: &'a Value) -> Result<(), StepError> {
        match value {
            Value::Array(values) => {
                for item in values {
                    self.validate_record(item)?;
                }
            },
            Value::Object(values) => match values.get("kind").and_then(Value::as_str) {
                Some("Type" | "TFree" | "TVar") => self.validate_type(value)?,
                Some("Const" | "Free" | "Var" | "Bound" | "Abs" | "App") => {
                    self.validate_term(value)?
                },
                _ => {
                    for item in values.values() {
                        self.validate_record(item)?;
                    }
                },
            },
            _ => {},
        }
        Ok(())
    }
}

fn same_raw_type(left: &Value, right: &Value) -> bool {
    if left["kind"] != right["kind"] || left["name"] != right["name"] {
        return false;
    }
    if left["kind"] == "Type" {
        return match (left["args"].as_array(), right["args"].as_array()) {
            (Some(a), Some(b)) => {
                a.len() == b.len() && a.iter().zip(b).all(|(a, b)| same_raw_type(a, b))
            },
            _ => false,
        };
    }
    left["index"] == right["index"] && same_sort(&left["sort"], &right["sort"])
}

fn same_variable(left: &Value, right: &Value) -> bool {
    left["kind"] == right["kind"]
        && left["name"] == right["name"]
        && left["index"] == right["index"]
        && (left["kind"] != "Var" || same_raw_type(&left["type"], &right["type"]))
}

#[derive(Default)]
pub struct Renaming<'a> {
    bindings: Vec<(&'a Value, &'a Value)>,
}

impl<'a> Renaming<'a> {
    fn bind(&mut self, left: &'a Value, right: &'a Value) -> bool {
        if let Some((_, previous)) = self.bindings.iter().find(|(key, _)| same_variable(key, left))
        {
            return same_variable(previous, right);
        }
        if self.bindings.iter().any(|(_, key)| same_variable(key, right)) {
            return false;
        }
        self.bindings.push((left, right));
        true
    }

    pub fn match_type(&mut self, left: &'a Value, right: &'a Value) -> bool {
        if left["kind"] != right["kind"] {
            return false;
        }
        match left["kind"].as_str() {
            Some("Type") => match (left["args"].as_array(), right["args"].as_array()) {
                (Some(a), Some(b)) => {
                    left["name"] == right["name"]
                        && a.len() == b.len()
                        && a.iter().zip(b).all(|(a, b)| self.match_type(a, b))
                },
                _ => false,
            },
            Some("TFree") => {
                same_sort(&left["sort"], &right["sort"]) && left["name"] == right["name"]
            },
            Some("TVar") => same_sort(&left["sort"], &right["sort"]) && self.bind(left, right),
            _ => false,
        }
    }

    pub fn match_term(&mut self, left: &'a Value, right: &'a Value) -> bool {
        if left["kind"] != right["kind"] {
            return false;
        }
        match left["kind"].as_str() {
            Some("Bound") => left["index"] == right["index"],
            Some("App") => {
                self.match_term(&left["function"], &right["function"])
                    && self.match_term(&left["argument"], &right["argument"])
            },
            Some("Abs") => match (
                left.get("type").or_else(|| left.get("binder_type")),
                right.get("type").or_else(|| right.get("binder_type")),
            ) {
                (Some(a), Some(b)) => {
                    self.match_type(a, b) && self.match_term(&left["body"], &right["body"])
                },
                _ => false,
            },
            Some("Const" | "Free") => {
                left["name"] == right["name"] && self.match_type(&left["type"], &right["type"])
            },
            Some("Var") => self.match_type(&left["type"], &right["type"]) && self.bind(left, right),
            _ => false,
        }
    }
}

type Matcher<'a> = fn(&mut Renaming<'a>, &'a Value, &'a Value) -> Result<bool, StepError>;
type Continuation<'a, 'b> = dyn FnMut(&mut Renaming<'a>) -> Result<bool, StepError> + 'b;

pub fn match_unordered<'a>(
    left: &'a [Value],
    right: &'a [Value],
    renaming: &mut Renaming<'a>,
    matcher: Matcher<'a>,
    continuation: &mut Continuation<'a, '_>,
) -> Result<bool, StepError> {
    if left.len() != right.len() {
        return Ok(false);
    }
    let mut used = vec![false; right.len()];
    match_remaining(left, right, &mut used, renaming, matcher, continuation)
}

fn match_remaining<'a>(
    left: &'a [Value],
    right: &'a [Value],
    used: &mut [bool],
    renaming: &mut Renaming<'a>,
    matcher: Matcher<'a>,
    continuation: &mut Continuation<'a, '_>,
) -> Result<bool, StepError> {
    let Some((first, rest)) = left.split_first() else {
        return continuation(renaming);
    };
    for (index, candidate) in right.iter().enumerate() {
        if used[index] {
            continue;
        }
        let checkpoint = renaming.bindings.len();
        if matcher(renaming, first, candidate)? {
            used[index] = true;
            if match_remaining(rest, right, used, renaming, matcher, continuation)? {
                return Ok(true);
            }
            used[index] = false;
        }
        renaming.bindings.truncate(checkpoint);
    }
    Ok(false)
}

fn match_term_record<'a>(
    map: &mut Renaming<'a>,
    left: &'a Value,
    right: &'a Value,
) -> Result<bool, StepError> {
    Ok(map.match_term(left, right))
}

fn match_pair<'a>(
    map: &mut Renaming<'a>,
    left: &'a Value,
    right: &'a Value,
) -> Result<bool, StepError> {
    Ok(map.match_term(&left[0], &right[0]) && map.match_term(&left[1], &right[1]))
}

pub fn match_judgments(left: &Value, right: &Value) -> Result<bool, StepError> {
    match_judgments_with_constraints(left, right, &[], &[])
}

pub fn match_judgments_with_constraints(
    left: &Value,
    right: &Value,
    left_constraints: &[Value],
    right_constraints: &[Value],
) -> Result<bool, StepError> {
    match_judgments_with_premises(left, right, left_constraints, right_constraints, &[], &[])
}

pub(crate) fn match_judgments_with_premises(
    left: &Value,
    right: &Value,
    left_constraints: &[Value],
    right_constraints: &[Value],
    left_premises: &[Value],
    right_premises: &[Value],
) -> Result<bool, StepError> {
    let mut left_scope = SyntaxScope::default();
    let mut right_scope = SyntaxScope::default();
    left_scope.validate_judgment(left)?;
    right_scope.validate_judgment(right)?;
    for constraint in left_constraints {
        left_scope.validate_record(constraint)?;
    }
    for constraint in right_constraints {
        right_scope.validate_record(constraint)?;
    }
    let shyps = match_unordered(
        as_array(&left["shyps"], "shyps")?,
        as_array(&right["shyps"], "shyps")?,
        &mut Renaming::default(),
        |_, a, b| Ok(same_sort(a, b)),
        &mut |_| Ok(true),
    )?;
    let mut mapping = Renaming::default();
    if !shyps || !mapping.match_term(&left["proposition"], &right["proposition"]) {
        return Ok(false);
    }
    let (a, b) = (as_array(&left["tpairs"], "tpairs")?, as_array(&right["tpairs"], "tpairs")?);
    match_unordered(
        as_array(&left["hypotheses"], "hypotheses")?,
        as_array(&right["hypotheses"], "hypotheses")?,
        &mut mapping,
        match_term_record,
        &mut |mapping| {
            match_unordered(a, b, mapping, match_pair, &mut |mapping| {
                match_unordered(
                    left_constraints,
                    right_constraints,
                    mapping,
                    |mapping, left, right| match_record(left, right, mapping),
                    &mut |mapping| {
                        Ok(left_premises.len() == right_premises.len()
                            && left_premises
                                .iter()
                                .zip(right_premises)
                                .all(|(left, right)| mapping.match_term(left, right)))
                    },
                )
            })
        },
    )
}

pub fn match_types(left: &Value, right: &Value) -> Result<bool, StepError> {
    SyntaxScope::default().validate_type(left)?;
    SyntaxScope::default().validate_type(right)?;
    Ok(Renaming::default().match_type(left, right))
}

pub fn match_terms(left: &Value, right: &Value) -> Result<bool, StepError> {
    SyntaxScope::default().validate_term(left)?;
    SyntaxScope::default().validate_term(right)?;
    Ok(Renaming::default().match_term(left, right))
}

pub fn match_record<'a>(
    left: &'a Value,
    right: &'a Value,
    map: &mut Renaming<'a>,
) -> Result<bool, StepError> {
    match (left, right) {
        (Value::Array(a), Value::Array(b)) => {
            if a.len() != b.len() {
                return Ok(false);
            }
            for (a, b) in a.iter().zip(b) {
                if !match_record(a, b, map)? {
                    return Ok(false);
                }
            }
            Ok(true)
        },
        (Value::Object(a), Value::Object(b)) => {
            match a.get("kind").and_then(Value::as_str) {
                Some("Type" | "TVar" | "TFree") => return Ok(map.match_type(left, right)),
                Some("Const" | "Free" | "Var" | "Bound" | "Abs" | "App") => {
                    return Ok(map.match_term(left, right));
                },
                _ => {},
            }
            if a.keys().ne(b.keys()) {
                return Ok(false);
            }
            match_record_fields(left, right, map)
        },
        _ => Ok(left == right),
    }
}

fn match_record_fields<'a>(
    left: &'a Value,
    right: &'a Value,
    map: &mut Renaming<'a>,
) -> Result<bool, StepError> {
    for (key, value) in as_object(left, "record")? {
        if key != "dependencies" && !match_record(value, &right[key], map)? {
            return Ok(false);
        }
    }
    let Some(dependencies) = left.get("dependencies") else {
        return Ok(true);
    };
    match_unordered(
        as_array(dependencies, "dependencies")?,
        as_array(&right["dependencies"], "dependencies")?,
        map,
        |map, a, b| match_record(a, b, map),
        &mut |_| Ok(true),
    )
}

pub fn match_validated_records(left: &Value, right: &Value) -> Result<bool, StepError> {
    SyntaxScope::default().validate_record(left)?;
    SyntaxScope::default().validate_record(right)?;
    match_record(left, right, &mut Renaming::default())
}
