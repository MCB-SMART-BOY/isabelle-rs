//! Classifies fixed-reference axiom provenance, never logical authorization.
mod data;

use std::collections::{BTreeMap, HashMap, HashSet};

use serde_json::{Map, Value, json};

use super::common::require;
use crate::runner::StepError;
use data::{CANDIDATES, EXPLICIT_SITES};

const MAX_TERM_DEPTH: usize = 128;

fn object<'a>(
    value: &'a Value,
    keys: &[&str],
    context: &str,
) -> Result<&'a Map<String, Value>, StepError> {
    let map = value.as_object().ok_or_else(|| StepError::Input(format!("Malformed {context}")))?;
    require(
        map.len() == keys.len() && keys.iter().all(|key| map.contains_key(*key)),
        format!("Malformed {context}"),
    )?;
    Ok(map)
}

fn nonempty<'a>(value: Option<&'a Value>, context: &str) -> Result<&'a str, StepError> {
    value
        .and_then(Value::as_str)
        .filter(|text| !text.is_empty())
        .ok_or_else(|| StepError::Input(format!("Malformed {context}")))
}

fn array<'a>(value: Option<&'a Value>, context: &str) -> Result<&'a [Value], StepError> {
    value
        .and_then(Value::as_array)
        .map(Vec::as_slice)
        .ok_or_else(|| StepError::Input(format!("Malformed {context}")))
}

fn validate_type(value: &Value, depth: usize) -> Result<(), StepError> {
    require(depth <= MAX_TERM_DEPTH, "Axiom type exceeds bounded nesting depth")?;
    let kind = value.get("kind").and_then(Value::as_str);
    match kind {
        Some("Type") => {
            let typ = object(value, &["kind", "name", "args"], "axiom type constructor")?;
            nonempty(typ.get("name"), "axiom type constructor")?;
            for arg in array(typ.get("args"), "axiom type constructor")? {
                validate_type(arg, depth + 1)?;
            }
        },
        Some("TFree" | "TVar") => {
            let keys: &[_] = if kind == Some("TFree") {
                &["kind", "name", "sort"]
            } else {
                &["kind", "name", "index", "sort"]
            };
            let typ = object(value, keys, "axiom type variable")?;
            nonempty(typ.get("name"), "axiom type variable")?;
            for item in array(typ.get("sort"), "axiom type variable")? {
                nonempty(Some(item), "axiom type variable")?;
            }
            if kind == Some("TVar") {
                require(typ["index"].as_i64().is_some(), "Malformed schematic type index")?;
            }
        },
        _ => return Err(StepError::Input("Unknown axiom type constructor".into())),
    }
    Ok(())
}

fn validate_term(value: &Value, depth: usize) -> Result<(), StepError> {
    require(depth <= MAX_TERM_DEPTH, "Axiom term exceeds bounded nesting depth")?;
    match value.get("kind").and_then(Value::as_str) {
        Some("Const" | "Free" | "Var") => {
            let is_var = value["kind"] == "Var";
            let keys: &[_] =
                if is_var { &["kind", "name", "type", "index"] } else { &["kind", "name", "type"] };
            let term = object(value, keys, "axiom term atom")?;
            nonempty(term.get("name"), "term name")?;
            if is_var {
                require(term["index"].as_i64().is_some(), "Malformed schematic term index")?;
            }
            validate_type(&term["type"], depth + 1)?;
        },
        Some("Bound") => {
            let term = object(value, &["kind", "index"], "bound axiom term")?;
            require(term["index"].as_u64().is_some(), "Malformed bound index")?;
        },
        Some("Abs") => {
            let term = object(value, &["kind", "name", "type", "body"], "abstraction")?;
            require(term["name"].as_str().is_some(), "Malformed abstraction binder")?;
            validate_type(&term["type"], depth + 1)?;
            validate_term(&term["body"], depth + 1)?;
        },
        Some("App") => {
            let term = object(value, &["kind", "function", "argument"], "application")?;
            validate_term(&term["function"], depth + 1)?;
            validate_term(&term["argument"], depth + 1)?;
        },
        _ => return Err(StepError::Input("Unknown axiom term constructor".into())),
    }
    Ok(())
}

fn validate_dependency(value: &Value, context: &str) -> Result<(), StepError> {
    let entry = object(value, &["kind", "name", "types"], context)?;
    require(
        matches!(entry["kind"].as_str(), Some("type" | "const")),
        format!("Malformed {context}"),
    )?;
    nonempty(entry.get("name"), context)?;
    for typ in array(entry.get("types"), context)? {
        validate_type(typ, 0)?;
    }
    Ok(())
}

fn validate_specification(value: &Value) -> Result<Option<&str>, StepError> {
    let spec =
        object(value, &["description", "axiom_name", "subject", "dependencies"], "specification")?;
    require(spec["description"].as_str().is_some(), "Malformed specification description")?;
    validate_dependency(&spec["subject"], "subject")?;
    for entry in array(spec.get("dependencies"), "specification dependencies")? {
        validate_dependency(entry, "dependency")?;
    }
    if spec["axiom_name"].is_null() {
        Ok(None)
    } else {
        Ok(Some(nonempty(spec.get("axiom_name"), "specification axiom identity")?))
    }
}

fn read_associations(
    theory: &Value,
    axioms: &[Value],
) -> Result<BTreeMap<String, Value>, StepError> {
    let mut links: BTreeMap<String, Value> = axioms
        .iter()
        .filter_map(|axiom| axiom["name"].as_str())
        .map(|name| (name.into(), json!({"specifications": [], "constant_definitions": []})))
        .collect();
    for spec in array(theory.get("specifications"), "theory specifications")? {
        if let Some(name) = validate_specification(spec)? {
            let association = links.get_mut(name).ok_or_else(|| {
                StepError::Input(format!("Unresolved specification axiom {name}"))
            })?;
            let entries = association["specifications"].as_array_mut().ok_or_else(|| {
                StepError::Protocol {
                    operation: "associate axiom specification".into(),
                    detail: "invalid internal collection".into(),
                }
            })?;
            require(!entries.contains(spec), format!("Duplicate axiom specification: {name}"))?;
            entries.push(spec.clone());
        }
    }
    for definition in array(theory.get("constant_definitions"), "theory constant definitions")? {
        let entry = object(definition, &["constant", "axiom"], "constant definition")?;
        let constant = nonempty(entry.get("constant"), "constant definition identity")?;
        let name = nonempty(entry.get("axiom"), "constant definition identity")?;
        let association = links.get_mut(name).ok_or_else(|| {
            StepError::Input(format!("Unresolved constant definition axiom {name}"))
        })?;
        let specs = array(association.get("specifications"), "associated specifications")?;
        require(
            specs.iter().any(|spec| {
                spec["subject"]["kind"] == "const" && spec["subject"]["name"] == constant
            }),
            format!("Constant definition lacks matching specification: {name}"),
        )?;
        let entries = association["constant_definitions"].as_array_mut().ok_or_else(|| {
            StepError::Protocol {
                operation: "associate constant definition".into(),
                detail: "invalid internal collection".into(),
            }
        })?;
        require(!entries.contains(definition), format!("Duplicate constant definition: {name}"))?;
        entries.push(definition.clone());
    }
    Ok(links)
}

fn location(path: &str, start: u64, end: u64) -> Value {
    json!({"path": path, "line_start": start, "line_end": end})
}

fn introduction_for(category: &str, name: &str) -> Vec<Value> {
    match category {
        "pure_primitive_mirror" => vec![
            location("src/Pure/theory.ML", 379, 393),
            location("src/Pure/pure_thy.ML", 273, 273),
        ],
        "object_base_sort_arity" => vec![
            location("src/Pure/Isar/typedecl.ML", 69, 76),
            location("src/Pure/axclass.ML", 444, 466),
        ],
        "conditional_typedef_extension" => vec![location("src/HOL/Tools/typedef.ML", 129, 150)],
        "definition_associated" => vec![location("src/Pure/theory.ML", 323, 358)],
        "explicit_logic_axiom_candidate" | "explicit_object_arity" => EXPLICIT_SITES
            .iter()
            .filter(|(candidate, ..)| *candidate == name)
            .map(|(_, path, first, last)| location(path, *first, *last))
            .collect(),
        _ => Vec::new(),
    }
}

fn classify_candidate<'a>(
    name: &str,
    owner: &str,
    source: &str,
    links: &Value,
    candidate: Option<(&'a str, &'a str, &'a str)>,
) -> Result<&'a str, StepError> {
    if let Some((candidate_owner, candidate_source, category)) = candidate {
        require(
            (owner, source) == (candidate_owner, candidate_source),
            format!("Wrong owner/source for axiom {name}"),
        )?;
        require(
            links["specifications"].as_array().is_some_and(Vec::is_empty)
                && links["constant_definitions"].as_array().is_some_and(Vec::is_empty),
            format!("Candidate axiom has conflicting definition association: {name}"),
        )?;
        return Ok(category);
    }
    if links["specifications"]
        .as_array()
        .is_some_and(|specs| specs.iter().any(|spec| spec["subject"]["kind"] == "const"))
    {
        return Ok("definition_associated");
    }
    Ok("unclassified")
}

/// Classify observed source provenance; no entry grants native theorem authority.
pub fn classify_axioms(inventory: &Value) -> Result<Value, StepError> {
    require(
        inventory["schema_version"] == 1
            && inventory["reference"] == "Isabelle2025"
            && inventory["theories"].as_array().is_some_and(|items| !items.is_empty()),
        "Invalid or empty reference inventory",
    )?;
    let candidates: HashMap<&str, (&str, &str, &str)> = CANDIDATES
        .iter()
        .map(|&(owner, source, category, name)| (name, (owner, source, category)))
        .collect();
    require(candidates.len() == CANDIDATES.len(), "Duplicate candidate identity")?;
    let mut seen = HashSet::new();
    let mut owners = HashSet::new();
    let mut entries = Vec::new();
    for theory in array(inventory.get("theories"), "inventory theories")? {
        let owner = nonempty(theory.get("name"), "theory identity")?;
        let source = nonempty(theory.get("source"), "theory source")?;
        require(owners.insert(owner), format!("Duplicate or malformed theory identity: {owner}"))?;
        let axioms = array(theory.get("axioms"), "theory axioms")?;
        for axiom in axioms {
            let axiom = object(axiom, &["name", "term"], "axiom")?;
            let name = nonempty(axiom.get("name"), "axiom name or term")?;
            validate_term(&axiom["term"], 0)?;
            require(seen.insert(name), format!("Duplicate axiom identity: {name}"))?;
        }
        let mut associations = read_associations(theory, axioms)?;
        for axiom in axioms {
            let name = nonempty(axiom.get("name"), "axiom name")?;
            let links = associations.remove(name).ok_or_else(|| StepError::Protocol {
                operation: "classify axiom".into(),
                detail: format!("missing association for {name}"),
            })?;
            let category =
                classify_candidate(name, owner, source, &links, candidates.get(name).copied())?;
            entries.push(json!({"theory": owner, "source": source, "name": name, "term": axiom["term"], "associations": links, "category": category, "introduction": introduction_for(category, name)}));
        }
    }
    require(!entries.is_empty(), "Reference inventory contains no observed axioms")?;
    let mut counts: BTreeMap<&str, usize> = BTreeMap::new();
    let mut unclassified = Vec::new();
    for entry in &entries {
        let category = entry["category"].as_str().ok_or_else(|| StepError::Protocol {
            operation: "count classified axioms".into(),
            detail: "missing internal category".into(),
        })?;
        *counts.entry(category).or_default() += 1;
        if category == "unclassified" {
            unclassified.push(json!({"theory": entry["theory"], "name": entry["name"]}));
        }
    }
    Ok(
        json!({"schema": 1, "reference": "Isabelle2025", "authorization": "none_reference_provenance_only", "entries": entries, "counts": counts, "unclassified": unclassified}),
    )
}
