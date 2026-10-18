//! Version-two diagnostic matching. Private DAG leaf identities and thread scheduling are not cross-side keys.
use crate::common::{as_array, as_str, field, require};
use crate::compare::ComparisonDiagnostics;
use crate::compare_syntax::{Renaming, match_record, require_index};
use crate::protocol::validate_observation_owner;
use crate::signature::SignatureCache;
use crate::{EvidenceError, observation};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};

fn native_member<'a>(
    candidate: &'a Value,
    item: &Value,
) -> Result<Option<&'a Value>, EvidenceError> {
    let theory_name = as_str(field(item, "theory")?, "named theory")?;
    let group_name = as_str(field(item, "fact_group_name")?, "named group")?;
    let index = require_index(field(item, "member_index")?, "named member index")?;
    let theories = as_array(field(candidate, "theories")?, "candidate theories")?;
    Ok(theories
        .iter()
        .find(|theory| theory["name"] == theory_name)
        .and_then(|theory| theory["fact_groups"].as_array())
        .and_then(|groups| groups.iter().find(|group| group["name"] == group_name))
        .and_then(|group| group["theorems"].as_array())
        .and_then(|members| members.iter().find(|member| member["index"].as_u64() == Some(index))))
}

fn smash_type(value: &Value) -> Result<Value, EvidenceError> {
    match as_str(field(value, "kind")?, "C type kind")? {
        "Type" => Ok(json!({"kind":"Type","name":value["name"],
            "args":as_array(field(value, "args")?, "C type arguments")?.iter()
                .map(smash_type).collect::<Result<Vec<_>, _>>()?})),
        "TFree" | "TVar" => Ok(json!({"kind":"TFree","name":"'a","sort":field(value,"sort")?})),
        _ => Err(EvidenceError::Input("C projection has unknown typed constructor".into())),
    }
}

fn quotient_obligations(
    value: &Value,
    root_owner: &str,
    inventory: &Value,
) -> Result<Vec<Value>, EvidenceError> {
    let mut quotient = Vec::new();
    for (position, obligation) in as_array(value, "raw C obligations")?.iter().enumerate() {
        let mut scope = crate::compare_syntax::SyntaxScope::default();
        scope.validate_type(field(obligation, "type")?)?;
        crate::compare_syntax::validate_sort(field(obligation, "required_sort")?)?;
        let occurrence = field(obligation, "occurrence")?;
        require(
            occurrence["source"] == "C" && occurrence["path"] == json!([position]),
            "C obligation lacks its final C position",
        )?;
        let owner = as_str(field(obligation, "source_owner")?, "C source owner")?;
        validate_observation_owner(inventory, root_owner, owner)?;
        let key = json!({"source_owner":owner,"type":smash_type(field(obligation,"type")?)?,
            "required_sort":field(obligation,"required_sort")?});
        if !quotient.contains(&key) {
            quotient.push(key);
        }
    }
    Ok(quotient)
}

fn match_sort_quotient(
    reference: &Value,
    native: &Value,
    member: &Value,
    inventory: &Value,
) -> Result<bool, EvidenceError> {
    let owner = as_str(field(member, "observed_in")?, "native theorem owner")?;
    let left = quotient_obligations(reference, owner, inventory)?;
    let right = quotient_obligations(native, owner, inventory)?;
    let mut used = vec![false; right.len()];
    for obligation in &left {
        let mut found = false;
        for (index, candidate) in right.iter().enumerate() {
            if used[index] {
                continue;
            }
            let mut map = Renaming::default();
            if match_record(obligation, candidate, &mut map)? {
                used[index] = true;
                found = true;
                break;
            }
        }
        if !found {
            return Ok(false);
        }
    }
    Ok(left.len() == right.len())
}

fn validate_local_dependencies(
    value: &Value,
    theorem: &Value,
    inventory: &Value,
    signatures: &mut SignatureCache<'_>,
) -> Result<(), EvidenceError> {
    let root_owner = as_str(field(theorem, "observed_in")?, "native accepted owner")?;
    let mut occurrences = BTreeSet::new();
    for dependency in as_array(value, "named dependency instances")? {
        let owner = as_str(field(dependency, "owner")?, "dependency declaration owner")?;
        validate_observation_owner(inventory, root_owner, owner)?;
        let kind = as_str(field(dependency, "kind")?, "dependency storage kind")?;
        require(
            matches!(kind, "Axiom" | "Definition" | "Typedef" | "Class" | "Arity" | "AcceptedFact"),
            "unknown native dependency storage policy",
        )?;
        observation::validate_dependency(dependency)?;
        let occurrence =
            as_str(field(dependency, "occurrence_id")?, "local dependency occurrence")?;
        require(
            !occurrence.is_empty() && occurrences.insert(occurrence),
            "empty or duplicate local dependency occurrence",
        )?;
        let instance = field(dependency, "instance")?;
        let mut scope = crate::compare_syntax::SyntaxScope::default();
        for typ in as_array(field(instance, "types")?, "instantiated dependency types")? {
            scope.validate_type(typ)?;
        }
        for term in as_array(field(instance, "terms")?, "instantiated dependency terms")? {
            scope.validate_term(term)?;
        }
        observation::validate_dependency_signature(dependency, signatures.get(owner)?)?;
    }
    Ok(())
}

pub(super) fn compare_named(
    result: &mut ComparisonDiagnostics,
    name: &str,
    reference: &[&Value],
    candidate: &Value,
    inventory: &Value,
) -> Result<(), EvidenceError> {
    let mut signatures = SignatureCache::new(inventory);
    let mut seen = BTreeSet::new();
    for record in reference {
        let identity = (
            as_str(field(record, "theory")?, "named theory")?,
            as_str(field(record, "fact_group_name")?, "named group")?,
            require_index(field(record, "member_index")?, "named member")?,
        );
        require(seen.insert(identity), "v2 named field contains duplicate member")?;
        let Some(member) = native_member(candidate, record)? else {
            result.add_difference(format!("{name}:{identity:?}"), "native member missing");
            continue;
        };
        let native = member.get(name).and_then(|wrapper| wrapper.get("value"));
        let Some(native) = native else {
            result.blocked.push(json!({"field":name,"reason":"native member field unavailable"}));
            continue;
        };
        let expected = field(record, "value")?;
        let matches = match name {
            "full_axiom_extension_dependencies" => {
                validate_local_dependencies(expected, member, inventory, &mut signatures)?;
                validate_local_dependencies(native, member, inventory, &mut signatures)?;
                true // independent legal DAGs may have different complete leaf instance multisets
            },
            "unresolved_sort_obligations" => {
                match_sort_quotient(expected, native, member, inventory)?
            },
            "declaration_origin" => match_record(expected, native, &mut Renaming::default())?,
            _ => return Err(EvidenceError::Input(format!("unknown named field {name}"))),
        };
        result.compare_value(format!("{name}:{identity:?}"), &true, &matches);
    }
    Ok(())
}

fn normalized_event(value: &Value) -> Result<Value, EvidenceError> {
    fn strip_run(value: &mut Value) {
        if let Some(object) = value.as_object_mut() {
            object.remove("run_id");
            if let Some(root) = object.get_mut("root") {
                strip_run(root);
            }
        }
    }
    let mut normalized = value.clone();
    let object = normalized
        .as_object_mut()
        .ok_or_else(|| EvidenceError::Input("event must be a structured object".into()))?;
    for key in ["thread", "task", "serial", "run_id", "fork_branch", "scheduler_branch"] {
        object.remove(key);
    }
    if let Some(work) = object.get_mut("logical_work") {
        strip_run(work);
    }
    if let Some(edges) = object.get_mut("causal_edges") {
        let edges = edges.as_array_mut().ok_or_else(|| {
            EvidenceError::Input("observable causal edges must be an array".into())
        })?;
        for edge in edges.iter() {
            let kind = as_str(field(edge, "kind")?, "logical edge kind")?;
            require(
                matches!(
                    kind,
                    "input_future"
                        | "join_return"
                        | "fulfilment"
                        | "callback_enter"
                        | "callback_exit"
                ),
                "unknown logical work dependency edge",
            )?;
            field(edge, "from")?;
            if let Some(edge) = edge.as_object() {
                for endpoint in ["from", "to"] {
                    require(edge.contains_key(endpoint), "logical edge missing endpoint")?;
                }
            }
            field(edge, "to")?;
        }
        for edge in edges.iter_mut() {
            if let Some(from) = edge.get_mut("from") {
                strip_run(from);
            }
            if let Some(to) = edge.get_mut("to") {
                strip_run(to);
            }
        }
        edges.sort_by_key(Value::to_string);
        require(
            edges.windows(2).all(|pair| pair[0] != pair[1]),
            "duplicate observable causal dependency",
        )?;
    }
    Ok(normalized)
}

fn is_async_operation(value: &Value) -> bool {
    let operation = value
        .pointer("/origin_call/operation")
        .and_then(Value::as_str)
        .or_else(|| value.get("operation").and_then(Value::as_str))
        .unwrap_or_default();
    ["Future.map", "Future.forks", "Future.promise", "Future.join", "Future.fulfil"]
        .iter()
        .any(|name| operation.starts_with(name))
}

fn has_logical_work(value: &Value) -> Result<bool, EvidenceError> {
    let Some(work) = value.get("logical_work") else {
        return Ok(false);
    };
    field(work, "root")?;
    let operation = as_str(field(work, "operation")?, "logical work operation")?;
    require(!operation.is_empty(), "logical work lacks public operation")?;
    require_index(field(work, "parent_entry_ordinal")?, "parent logical work entry ordinal")?;
    as_array(field(value, "causal_edges")?, "logical work partial order")?;
    Ok(true)
}

fn event_root_key(metadata: &Value) -> Result<Option<String>, EvidenceError> {
    let root = as_str(field(metadata, "root_id")?, "public event root")?;
    let Ok(mut parsed) = serde_json::from_str::<Value>(root) else {
        let Some(load_root) = metadata.get("load_root") else {
            return Ok(None);
        };
        for key in ["source", "parent_source", "source_order", "session", "theory"] {
            field(load_root, key)?;
        }
        return Ok(Some(load_root.to_string()));
    };
    let Some(object) = parsed.as_object_mut() else {
        return Ok(None);
    };
    object.remove("run_id");
    for key in ["theory", "sequence", "source"] {
        field(&parsed, key)?;
    }
    Ok(Some(parsed.to_string()))
}

fn index_events<'a>(
    events: impl IntoIterator<Item = &'a Value>,
    name: &str,
    signatures: &mut SignatureCache<'_>,
) -> Result<Option<BTreeMap<String, Vec<Value>>>, EvidenceError> {
    let mut indexed = BTreeMap::<String, Vec<Value>>::new();
    for event in events {
        let payload = field(event, "value")?;
        observation::validate_event_payload(name, payload)?;
        if name == "anonymous_ephemeral_facts" {
            let owner = as_str(field(payload, "owner")?, "event owner")?;
            observation::validate_statement_signature(
                field(payload, "statement")?,
                signatures.get(owner)?,
            )?;
        }
        let Some(metadata) = event.get("metadata") else {
            return Ok(None);
        };
        let Some(root) = event_root_key(metadata)? else {
            return Ok(None);
        };
        let has_work = has_logical_work(payload)?;
        if is_async_operation(payload) && !has_work {
            return Ok(None);
        }
        let normalized = normalized_event(payload)?;
        indexed.entry(root).or_default().push(normalized);
    }
    Ok(Some(indexed))
}

fn match_event_group(left: &[Value], right: &[Value]) -> Result<bool, EvidenceError> {
    if left.len() != right.len() {
        return Ok(false);
    }
    let mut used = vec![false; right.len()];
    for original in left {
        let mut matched = false;
        for (index, actual) in right.iter().enumerate() {
            if used[index] || !match_record(original, actual, &mut Renaming::default())? {
                continue;
            }
            used[index] = true;
            matched = true;
            break;
        }
        if !matched {
            return Ok(false);
        }
    }
    Ok(true)
}

pub(super) fn compare_events(
    result: &mut ComparisonDiagnostics,
    name: &str,
    reference: &[&Value],
    candidate: &Value,
    inventory: &Value,
) -> Result<(), EvidenceError> {
    let Some(actual) = candidate.pointer(&format!("/execution/{name}")) else {
        result.blocked.push(json!({"field":name,"reason":"native event field unavailable"}));
        return Ok(());
    };
    let actual = as_array(actual, "native event records")?;
    if reference.len() != actual.len() {
        result.add_difference(format!("v2:{name}"), "observable event multiplicity differs");
        return Ok(());
    }
    let mut signatures = SignatureCache::new(inventory);
    let Some(expected) = index_events(reference.iter().copied(), name, &mut signatures)? else {
        result
            .blocked
            .push(json!({"field":name,"reason":"reference logical work/root identity incomplete"}));
        return Ok(());
    };
    let Some(observed) = index_events(actual.iter(), name, &mut signatures)? else {
        result
            .blocked
            .push(json!({"field":name,"reason":"native logical work/root identity incomplete"}));
        return Ok(());
    };
    if expected.keys().ne(observed.keys()) {
        result.add_difference(format!("v2:{name}"), "public causal roots differ");
        return Ok(());
    }
    for (root, left) in expected {
        let right = &observed[&root];
        result.compare_value(format!("v2:{name}:{root}"), &true, &match_event_group(&left, right)?);
    }
    Ok(())
}
