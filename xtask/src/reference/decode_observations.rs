//! Decode historical completed-command observations; these do not imply complete fact coverage.
use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use serde_json::{Value, json};

use super::{
    common::require,
    decode_bootstrap_events::{decode_raw_records, validate_depth},
    decode_execution, yxml,
};
use crate::runner::StepError;

pub fn decode_fact_origins(
    raw: &str,
    source_root: &Path,
    execution: &Value,
) -> Result<Value, StepError> {
    let root = yxml::parse(raw)?;
    let (attributes, children) =
        yxml::inspect(&root, "fact_observations", &["version", "session"])?;
    require(
        attributes["version"] == "1" && attributes["session"] == "Reference_Execution",
        "fact origins require the fixed reference session",
    )?;
    let mut identities = BTreeSet::new();
    let source_root = source_root
        .canonicalize()
        .map_err(|source| crate::runner::io_error("resolve observed source root", source))?;
    let mut normalized_sources = BTreeMap::new();
    let mut records = Vec::new();
    for child in yxml::elements(children)? {
        let attributes = yxml::empty_attrs(
            child,
            "fact_group",
            &["theory", "sequence", "source", "operation", "name"],
        )?;
        let theory = attributes["theory"].as_str().unwrap_or_default();
        if theory == "Reference_Execution.Reference_Observer" {
            continue;
        }
        let sequence = yxml::unsigned(attributes["sequence"].as_str().unwrap_or_default())?;
        let command = execution["theories"]
            .as_array()
            .and_then(|theories| theories.iter().find(|entry| entry["name"] == theory))
            .and_then(|entry| entry["commands"].as_array())
            .and_then(|commands| commands.iter().find(|entry| entry["sequence"] == sequence))
            .ok_or_else(|| {
                StepError::Input(format!("unobserved fact command {theory}:{sequence}"))
            })?;
        let source = attributes["source"].as_str().unwrap_or_default();
        let normalized = match normalized_sources.entry(source.to_owned()) {
            std::collections::btree_map::Entry::Occupied(entry) => entry.into_mut(),
            std::collections::btree_map::Entry::Vacant(entry) => {
                let (relative, _) =
                    decode_execution::read_fixed_file(source, &source_root, theory)?;
                entry.insert(relative)
            },
        };
        require(
            command["name"] == attributes["operation"]
                && command["source"].as_str() == Some(normalized.as_str()),
            format!("fact command identity differs in {theory}:{sequence}"),
        )?;
        let name = attributes["name"].as_str().unwrap_or_default();
        require(
            identities.insert((theory.to_owned(), sequence, name.to_owned())),
            format!("duplicate fact origin {theory}:{sequence}:{name}"),
        )?;
        records.push(json!({"theory":theory,"execution_event":sequence,
            "source":command["source"],"operation":command["name"],
            "fact_group_name":name}));
    }
    Ok(json!({"schema_version":1,"observations":records,
        "completeness":"partial_completed_command_states_only"}))
}

const V2_FIELDS: [&str; 6] = [
    "full_axiom_extension_dependencies",
    "unresolved_sort_obligations",
    "declaration_origin",
    "anonymous_ephemeral_facts",
    "dynamic_fact_evaluations",
    "runtime_registration_effects",
];

fn parse_observation(
    record: &super::decode_bootstrap_events::RawRecord<'_>,
) -> Result<(Value, Value), StepError> {
    let source = std::str::from_utf8(record.payload)
        .map_err(|_| StepError::Input("observer event payload is not UTF-8 YXML".into()))?;
    let root = yxml::parse(source)?;
    let (attrs, body) = yxml::inspect(
        &root,
        "observation",
        &["phase", "theory", "source", "source_sha256", "field"],
    )?;
    require(V2_FIELDS.contains(&attrs["field"].as_str()), "unknown observer field")?;
    require(
        matches!(
            attrs["phase"].as_str(),
            "original_bootstrap" | "original_target" | "reference_export" | "preparation"
        ),
        "invalid observer business phase",
    )?;
    require(body.len() == 1, "observer event requires one typed payload")?;
    let value = yxml::text(yxml::child(body, 0)?, "payload")?;
    let parsed: Value = serde_json::from_str(&value).map_err(|source| StepError::Json {
        operation: "decode actual observer typed event".into(),
        source,
    })?;
    validate_depth(&parsed, 0)?;
    require(parsed.is_object(), "observer event must contain structured typed value")?;
    Ok((
        json!({"run_id":record.run_id,"phase":attrs["phase"],"theory":attrs["theory"],
        "source":attrs["source"],"source_sha256":attrs["source_sha256"],
        "field":attrs["field"],"root_id":record.root_id,"local_id":record.local_id,
        "raw_record_index":record.index,"raw_frame_sha256":record.frame_sha256}),
        parsed,
    ))
}

fn require_observed_source(metadata: &Value, identity: &Value) -> Result<(), StepError> {
    let source = metadata["source"].as_str().unwrap_or_default();
    require(
        (source.starts_with("src/") || source.starts_with("session/"))
            && !source.contains('\\')
            && source.split('/').all(|part| !matches!(part, "" | "." | "..")),
        "observer event has invalid executed R source",
    )?;
    require(
        identity["source_hashes"][source] == metadata["source_sha256"]
            && metadata["source_sha256"].as_str().is_some_and(|hash| hash.len() == 64),
        format!("observer event source hash not approved for {source}"),
    )
}

fn require_observed_root(
    metadata: &Value,
    identity: &Value,
    execution: &Value,
    bootstrap: &Value,
) -> Result<(), StepError> {
    let run = metadata["run_id"].as_str().unwrap_or_default();
    let phase = metadata["phase"].as_str().unwrap_or_default();
    let root = metadata["root_id"].as_str().unwrap_or_default();
    if run == identity["build_run_id"] {
        require(
            phase == "original_bootstrap" || phase == "preparation",
            "build event cannot replace inventory target",
        )?;
    } else {
        require(run == identity["inventory_run_id"], "observer event has foreign run ID")?;
    }
    if phase == "original_bootstrap" {
        return require(
            bootstrap["loads"].as_array().is_some_and(|loads| {
                loads.iter().any(|load| {
                    load["run_id"] == run
                        && load["load_id"] == root
                        && load["source"] == metadata["source"]
                })
            }),
            "bootstrap observer event has no actual completed source load",
        );
    }
    if phase == "original_target" {
        require(run == identity["inventory_run_id"], "target event must be inventory run")?;
        let Ok(command) = serde_json::from_str::<Value>(root) else {
            return require(
                bootstrap["loads"].as_array().is_some_and(|loads| {
                    loads.iter().any(|load| {
                        load["run_id"] == run
                            && load["load_id"] == root
                            && load["source"] == metadata["source"]
                    })
                }),
                "target ML registration is not attached to an actual source load",
            );
        };
        require(
            command["run_id"] == run
                && command["source"] == metadata["source"]
                && command["theory"] == metadata["theory"]
                && execution["theories"].as_array().is_some_and(|theories| {
                    theories.iter().any(|theory| {
                        theory["name"] == command["theory"]
                            && theory["commands"].as_array().is_some_and(|commands| {
                                commands.iter().any(|item| {
                                    item["sequence"] == command["sequence"]
                                        && item["source"] == command["source"]
                                })
                            })
                    })
                }),
            "target observer event not backed by executed source command",
        )?;
    }
    Ok(())
}

fn attach_logical_root(metadata: &mut Value, bootstrap: &Value) {
    let run = metadata["run_id"].as_str().unwrap_or_default();
    let root = metadata["root_id"].as_str().unwrap_or_default();
    let Some(loads) = bootstrap["loads"].as_array() else {
        return;
    };
    let Some(load) = loads.iter().find(|load| load["run_id"] == run && load["load_id"] == root)
    else {
        return;
    };
    let parent_source = load["parent_load_id"].as_str().and_then(|parent| {
        loads
            .iter()
            .find(|candidate| candidate["run_id"] == run && candidate["load_id"] == parent)
            .map(|parent| parent["source"].clone())
    });
    metadata["load_root"] = json!({"source":load["source"],"parent_source":parent_source,
        "source_order":load["source_order"],"session":load["session"],"theory":load["theory"],
        "source_provenance":load["source_provenance"],
        "missing_parent":load["missing_parent"] == true});
}
fn required_named_members(inventory: &Value, run: &str) -> Result<Vec<Value>, StepError> {
    let theories = inventory["theories"].as_array().ok_or_else(|| {
        StepError::Input("inventory theories missing for observer coverage".into())
    })?;
    let mut members = Vec::new();
    for theory in theories {
        let name = theory["name"].as_str().unwrap_or_default();
        for group in theory["fact_groups"]
            .as_array()
            .ok_or_else(|| StepError::Input(format!("{name}: fact groups missing")))?
        {
            for member in group["theorems"]
                .as_array()
                .ok_or_else(|| StepError::Input(format!("{name}: fact members missing")))?
            {
                members.push(json!({"run_id":run,"theory":name,
                    "fact_group_name":group["name"],"member_index":member["index"]}));
            }
        }
    }
    Ok(members)
}

fn required_commands(execution: &Value, run: &str) -> Result<Vec<Value>, StepError> {
    let theories = execution["theories"].as_array().ok_or_else(|| {
        StepError::Input("executed theories missing for observer coverage".into())
    })?;
    let mut commands = Vec::new();
    for theory in theories {
        let name = theory["name"].as_str().unwrap_or_default();
        for command in theory["commands"]
            .as_array()
            .ok_or_else(|| StepError::Input(format!("{name}: commands missing")))?
        {
            commands.push(json!({"run_id":run,"theory":name,
                "sequence":command["sequence"],"source":command["source"]}));
        }
    }
    Ok(commands)
}

/// Decode raw TLV records; only actual sealed records may contribute to a field.
pub fn decode_observer_events_v2(
    raw: &[u8],
    identity: &Value,
    inventory: &Value,
    execution: &Value,
    bootstrap: &Value,
) -> Result<Value, StepError> {
    let records = decode_raw_records(raw)?;
    let mut events = BTreeMap::<(String, String), Vec<Value>>::new();
    let mut coverage = BTreeMap::<(String, String), Value>::new();
    let mut identities = BTreeSet::new();
    let mut starts = BTreeSet::new();
    for record in records.iter().filter(|item| item.channel == "observer") {
        require(
            identities.insert((record.run_id, record.root_id, record.local_id)),
            "observer local identity was reused",
        )?;
        if matches!(record.tag, "command_begin" | "command_end") {
            let root: Value = serde_json::from_str(record.root_id).map_err(|source| {
                StepError::Json { operation: "decode observed command root".into(), source }
            })?;
            require(
                root["run_id"] == record.run_id
                    && (root["run_id"] == identity["inventory_run_id"]
                        || root["run_id"] == identity["build_run_id"]),
                "command control record has foreign run or root",
            )?;
            let key = (record.run_id.to_owned(), record.root_id.to_owned());
            if record.tag == "command_begin" {
                require(starts.insert(key), "duplicate observed command begin")?;
            } else {
                require(starts.remove(&key), "observed command ended without begin")?;
            }
            continue;
        }
        let (metadata, value) = parse_observation(record)?;
        require_observed_source(&metadata, identity)?;
        require_observed_root(&metadata, identity, execution, bootstrap)?;
        let key = (record.run_id.to_owned(), metadata["field"].as_str().unwrap_or_default().into());
        match record.tag {
            "event" => {
                let mut item_metadata = metadata.clone();
                attach_logical_root(&mut item_metadata, bootstrap);
                item_metadata
                    .as_object_mut()
                    .ok_or_else(|| StepError::Input("observer metadata malformed".into()))?
                    .remove("field");
                for transient in ["raw_record_index", "raw_frame_sha256"] {
                    item_metadata
                        .as_object_mut()
                        .ok_or_else(|| StepError::Input("observer metadata malformed".into()))?
                        .remove(transient);
                }
                events.entry(key).or_default().push(json!({"metadata":item_metadata,
                    "value":value,"raw_record_index":record.index,
                    "raw_frame_sha256":record.frame_sha256}));
            },
            "seal" => {
                require(
                    value["named_members"].is_array()
                        && value["executed_commands"].is_array()
                        && value["bootstrap_loads"].is_array(),
                    "observer coverage seal missing genuine member/command/load sets",
                )?;
                require(
                    coverage
                        .insert(
                            key,
                            json!({"value":value,
                    "raw_record_index":record.index,"raw_frame_sha256":record.frame_sha256}),
                        )
                        .is_none(),
                    "duplicate observer coverage seal",
                )?;
            },
            "callback_exception" => {
                return Err(StepError::Input(format!(
                    "observer callback raised exception at {}:{}",
                    record.run_id, record.root_id
                )));
            },
            _ => {
                return Err(StepError::Input(format!(
                    "unknown observer record kind {}",
                    record.tag
                )));
            },
        }
    }
    require(starts.is_empty(), "observed command lacks end event")?;
    let mut decoded = Vec::new();
    let mut seals = Vec::new();
    let build = identity["build_run_id"].as_str().unwrap_or_default();
    let inventory_run = identity["inventory_run_id"].as_str().unwrap_or_default();
    require(
        !build.is_empty() && !inventory_run.is_empty() && build != inventory_run,
        "missing supervised observer run identities",
    )?;
    let expected_members = required_named_members(inventory, inventory_run)?;
    let expected_commands = required_commands(execution, inventory_run)?;
    for (key, seal) in coverage {
        let (run, field) = key.clone();
        let is_inventory = run == inventory_run;
        let actual_members = seal["value"]["named_members"]
            .as_array()
            .ok_or_else(|| StepError::Input("malformed observer named coverage".into()))?;
        let actual_commands = seal["value"]["executed_commands"]
            .as_array()
            .ok_or_else(|| StepError::Input("malformed observer command coverage".into()))?;
        require(
            !is_inventory
                || (actual_members == &expected_members && actual_commands == &expected_commands),
            "observer coverage does not match exact ordered inventory members and commands",
        )?;
        let items = events.remove(&key).unwrap_or_default();
        decoded.push(json!({"run_id":run,"field":field,"value":items}));
        seals.push(json!({"run_id":run,"field":field,"named_members":actual_members,
            "executed_commands":actual_commands,"bootstrap_loads":seal["value"]["bootstrap_loads"],
            "raw_record_index":seal["raw_record_index"],
            "raw_frame_sha256":seal["raw_frame_sha256"]}));
    }
    for ((run, field), items) in events {
        decoded.push(json!({"run_id":run,"field":field,"value":items}));
    }
    Ok(json!({"schema_version":2,"source_commit":identity["source_commit"],
        "overlay_id":identity["overlay_id"],"records":decoded,"coverage":seals}))
}
