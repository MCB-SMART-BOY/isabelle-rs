//! Decode only bytes emitted by the supervised bootstrap load recorder.
use std::collections::{BTreeMap, BTreeSet};

use serde_json::{Value, json};

use super::{
    common::{digest_bytes, require},
    yxml,
};
use crate::runner::StepError;

const MAX_RAW_BYTES: usize = 512 * 1024 * 1024;
const MAX_FRAME_BYTES: usize = 16 * 1024 * 1024;
const MAX_EVENTS: usize = 2_000_000;
const MAX_DEPTH: usize = 512;

pub struct RawRecord<'a> {
    pub index: usize,
    pub frame_sha256: String,
    pub channel: &'a str,
    pub tag: &'a str,
    pub run_id: &'a str,
    pub root_id: &'a str,
    pub local_id: &'a str,
    pub payload: &'a [u8],
}

fn parse_length(bytes: &[u8], offset: &mut usize, label: &str) -> Result<usize, StepError> {
    let start = *offset;
    while *offset < bytes.len() && bytes[*offset].is_ascii_digit() {
        *offset += 1;
    }
    require(
        *offset > start && bytes.get(*offset) == Some(&b'\n'),
        format!("{label}: malformed TLV length"),
    )?;
    let text = std::str::from_utf8(&bytes[start..*offset])
        .map_err(|_| StepError::Input(format!("{label}: non-ASCII TLV length")))?;
    require(
        text.len() == 1 || !text.starts_with('0'),
        format!("{label}: noncanonical TLV length"),
    )?;
    *offset += 1;
    text.parse().map_err(|_| StepError::Input(format!("{label}: overflowing TLV length")))
}

fn parse_fields<'a>(
    bytes: &'a [u8],
    count: usize,
    label: &str,
) -> Result<Vec<&'a [u8]>, StepError> {
    let mut offset = 0;
    let actual = parse_length(bytes, &mut offset, label)?;
    require(actual == count, format!("{label}: expected {count} TLV fields"))?;
    let mut fields = Vec::with_capacity(count);
    for _ in 0..count {
        let length = parse_length(bytes, &mut offset, label)?;
        let end = offset
            .checked_add(length)
            .ok_or_else(|| StepError::Input(format!("{label}: overflowing TLV field")))?;
        let field = bytes
            .get(offset..end)
            .ok_or_else(|| StepError::Input(format!("{label}: truncated TLV field")))?;
        fields.push(field);
        offset = end;
    }
    require(offset == bytes.len(), format!("{label}: trailing TLV field data"))?;
    Ok(fields)
}

fn as_text<'a>(bytes: &'a [u8], label: &str) -> Result<&'a str, StepError> {
    std::str::from_utf8(bytes).map_err(|_| StepError::Input(format!("{label}: invalid UTF-8")))
}

pub fn decode_raw_records(raw: &[u8]) -> Result<Vec<RawRecord<'_>>, StepError> {
    require(!raw.is_empty() && raw.len() <= MAX_RAW_BYTES, "observer raw empty or over budget")?;
    let mut offset = 0;
    let mut records = Vec::new();
    while offset < raw.len() {
        let length = parse_length(raw, &mut offset, "observer frame")?;
        require(
            length > 0 && length <= MAX_FRAME_BYTES && records.len() < MAX_EVENTS,
            "observer frame size or count exceeds budget",
        )?;
        let end = offset
            .checked_add(length)
            .ok_or_else(|| StepError::Input("observer frame length overflow".into()))?;
        let frame = raw
            .get(offset..end)
            .ok_or_else(|| StepError::Input("truncated observer frame".into()))?;
        let fields = parse_fields(frame, 6, "observer frame")?;
        let record = RawRecord {
            index: records.len(),
            frame_sha256: digest_bytes(frame),
            channel: as_text(fields[0], "observer channel")?,
            tag: as_text(fields[1], "observer tag")?,
            run_id: as_text(fields[2], "observer run ID")?,
            root_id: as_text(fields[3], "observer root ID")?,
            local_id: as_text(fields[4], "observer local ID")?,
            payload: fields[5],
        };
        require(
            !record.run_id.is_empty() && !record.root_id.is_empty() && !record.local_id.is_empty(),
            "observer event missing identity",
        )?;
        records.push(record);
        offset = end;
    }
    Ok(records)
}

pub fn validate_depth(value: &Value, depth: usize) -> Result<(), StepError> {
    require(depth <= MAX_DEPTH, "observer typed syntax exceeds depth budget")?;
    match value {
        Value::Array(items) => {
            for item in items {
                validate_depth(item, depth + 1)?;
            }
        },
        Value::Object(fields) => {
            for item in fields.values() {
                validate_depth(item, depth + 1)?;
            }
        },
        _ => {},
    }
    Ok(())
}

struct LoadPayload<'a> {
    source: &'a str,
    parent: &'a str,
    session: &'a str,
    theory: &'a str,
    source_order: u64,
    provenance: &'a str,
    consumed_bytes: &'a [u8],
}

fn read_bootstrap_payload<'a>(record: &'a RawRecord<'_>) -> Result<LoadPayload<'a>, StepError> {
    let fields = parse_fields(record.payload, 7, "bootstrap load")?;
    let source = as_text(fields[0], "bootstrap source")?;
    require(
        (source.starts_with("src/") || source.starts_with("session/"))
            && source.split('/').all(|part| !matches!(part, "" | "." | ".."))
            && !source.contains('\\'),
        "invalid bootstrap source path",
    )?;
    let session = as_text(fields[2], "bootstrap session")?;
    let theory = as_text(fields[3], "bootstrap theory")?;
    let source_order = as_text(fields[4], "bootstrap source order")?
        .parse::<u64>()
        .map_err(|_| StepError::Input("invalid bootstrap source order".into()))?;
    let provenance = as_text(fields[5], "bootstrap provenance")?;
    // The original recorder can leave theory empty when the load is not attributed to one.
    require(
        source_order > 0
            && !session.is_empty()
            && matches!(provenance, "actual_read_bytes" | "immutable_bootstrap_use"),
        "bootstrap load missing identity or unknown provenance",
    )?;
    Ok(LoadPayload {
        source,
        parent: as_text(fields[1], "bootstrap parent")?,
        session,
        theory,
        source_order,
        provenance,
        consumed_bytes: fields[6],
    })
}

fn validate_loaded_source(
    payload: &LoadPayload<'_>,
    record: &RawRecord<'_>,
    expected_hash: &str,
) -> Result<(), StepError> {
    if payload.provenance == "actual_read_bytes" {
        require(
            record.tag != "load_end" || digest_bytes(payload.consumed_bytes) == expected_hash,
            format!("bootstrap consumed source differs from executed R: {}", payload.source),
        )?;
        return require(
            record.tag == "load_end" || payload.consumed_bytes.is_empty(),
            "bootstrap non-end record falsely claims consumed source bytes",
        );
    }
    require(
        payload.consumed_bytes.is_empty(),
        "opaque bootstrap use falsely claims directly consumed source bytes",
    )
}

fn add_bootstrap_load(
    loads: &mut BTreeMap<(String, String), Value>,
    record: &RawRecord<'_>,
    payload: &LoadPayload<'_>,
    expected_hash: &str,
) -> Result<(), StepError> {
    let key = (record.run_id.into(), record.root_id.into());
    let load = json!({"run_id":record.run_id,"load_id":record.root_id,
        "parent_load_id":if payload.parent.is_empty() { Value::Null } else { json!(payload.parent) },
        "session":payload.session,"theory":payload.theory,"source":payload.source,
        "source_sha256":expected_hash,"source_order":payload.source_order,
        "source_provenance":payload.provenance,"started":true,"finished":false,
        "sealed":false,"observed_local_ids":[],"raw_begin_index":record.index,
        "raw_begin_sha256":record.frame_sha256});
    require(loads.insert(key, load).is_none(), "duplicate bootstrap load begin")
}

fn complete_bootstrap_load(
    loads: &mut BTreeMap<(String, String), Value>,
    record: &RawRecord<'_>,
    payload: &LoadPayload<'_>,
    expected_hash: &str,
) -> Result<(), StepError> {
    let key = (record.run_id.into(), record.root_id.into());
    let load = loads
        .get_mut(&key)
        .ok_or_else(|| StepError::Input("bootstrap load ended or sealed before begin".into()))?;
    require(
        load["source"] == payload.source
            && load["source_sha256"] == expected_hash
            && load["session"] == payload.session
            && load["theory"] == payload.theory
            && load["source_order"] == payload.source_order
            && load["source_provenance"] == payload.provenance
            && load["parent_load_id"]
                == if payload.parent.is_empty() { Value::Null } else { json!(payload.parent) },
        "bootstrap load source or identity changed",
    )?;
    if record.tag == "load_end" {
        require(load["finished"] == false, "duplicate bootstrap load end")?;
        load["finished"] = json!(true);
        load["raw_record_index"] = json!(record.index);
        load["raw_frame_sha256"] = json!(record.frame_sha256);
        return Ok(());
    }
    require(
        load["finished"] == true && load["sealed"] == false,
        "bootstrap seal before completed load or duplicate seal",
    )?;
    load["sealed"] = json!(true);
    load["raw_seal_index"] = json!(record.index);
    load["raw_seal_sha256"] = json!(record.frame_sha256);
    Ok(())
}

fn add_bootstrap_observer_events(
    records: &[RawRecord<'_>],
    loads: &mut BTreeMap<(String, String), Value>,
    events: &mut Vec<Value>,
    source_hashes: &serde_json::Map<String, Value>,
) -> Result<(), StepError> {
    for record in records.iter().filter(|item| item.channel == "observer" && item.tag == "event") {
        let raw = as_text(record.payload, "bootstrap observer event")?;
        let root = yxml::parse(raw)?;
        let (attrs, body) = yxml::inspect(
            &root,
            "observation",
            &["phase", "theory", "source", "source_sha256", "field"],
        )?;
        if attrs["phase"] != "original_bootstrap" {
            continue;
        }
        let key = (record.run_id.to_owned(), record.root_id.to_owned());
        let load = loads.get_mut(&key).ok_or_else(|| {
            StepError::Input("bootstrap theorem event has no actual load root".into())
        })?;
        require(
            load["source"] == attrs["source"]
                && source_hashes.get(&attrs["source"]) == Some(&json!(attrs["source_sha256"]))
                && body.len() == 1,
            "bootstrap theorem event source or shape differs from R",
        )?;
        let typed = yxml::text(yxml::child(body, 0)?, "payload")?;
        let value: Value = serde_json::from_str(&typed).map_err(|source| StepError::Json {
            operation: "decode bootstrap typed theorem event".into(),
            source,
        })?;
        validate_depth(&value, 0)?;
        require(value.is_object(), "bootstrap theorem event lacks typed structure")?;
        load["observed_local_ids"]
            .as_array_mut()
            .ok_or_else(|| StepError::Input("bootstrap event IDs malformed".into()))?
            .push(json!(record.local_id));
        events.push(json!({"run_id":record.run_id,"field":attrs["field"],"load_id":record.root_id,
            "local_id":record.local_id,"value":value,
            "raw_record_index":record.index,"raw_frame_sha256":record.frame_sha256}));
    }
    Ok(())
}
pub fn decode_bootstrap_events_v2(raw: &[u8], identity: &Value) -> Result<Value, StepError> {
    let records = decode_raw_records(raw)?;
    let source_hashes = identity["source_hashes"]
        .as_object()
        .ok_or_else(|| StepError::Input("missing approved executed R source hashes".into()))?;
    let build = identity["build_run_id"].as_str().unwrap_or_default();
    let inventory = identity["inventory_run_id"].as_str().unwrap_or_default();
    require(
        !build.is_empty() && !inventory.is_empty() && build != inventory,
        "missing distinct supervised run IDs",
    )?;
    let mut loads = BTreeMap::<(String, String), Value>::new();
    let mut events = Vec::new();
    let mut identities = BTreeSet::new();
    for record in records.iter().filter(|record| record.channel == "bootstrap") {
        require(
            record.run_id == build || record.run_id == inventory,
            "bootstrap load belongs to unknown run",
        )?;
        require(
            identities.insert((record.run_id, record.root_id, record.local_id)),
            "duplicate bootstrap local event identity",
        )?;
        if record.tag == "load_error" {
            return Err(StepError::Input("bootstrap source load failed".into()));
        }
        let payload = read_bootstrap_payload(record)?;
        let expected_hash =
            source_hashes.get(payload.source).and_then(Value::as_str).ok_or_else(|| {
                StepError::Input(format!(
                    "bootstrap source absent from approved executed R: {}",
                    payload.source
                ))
            })?;
        validate_loaded_source(&payload, record, expected_hash)?;
        match record.tag {
            "load_begin" => add_bootstrap_load(&mut loads, record, &payload, expected_hash)?,
            "load_end" | "load_seal" => {
                complete_bootstrap_load(&mut loads, record, &payload, expected_hash)?
            },
            _ => return Err(StepError::Input(format!("unknown bootstrap tag {}", record.tag))),
        }
    }
    require(!loads.is_empty(), "no genuine bootstrap source loads")?;
    add_bootstrap_observer_events(&records, &mut loads, &mut events, source_hashes)?;
    let keys = loads.keys().cloned().collect::<BTreeSet<_>>();
    for ((run, id), load) in &mut loads {
        require(load["finished"] == true, format!("bootstrap load {run}:{id} missing completion"))?;
        if let Some(parent) = load["parent_load_id"].as_str()
            && !keys.contains(&(run.clone(), parent.into()))
        {
            // Do not forge the top-level --use observation from a later child callback.
            load["missing_parent_load_id"] = json!(parent);
            load["missing_parent"] = json!(true);
        }
    }
    let loads = loads.into_values().collect::<Vec<_>>();
    Ok(json!({"schema_version":2,"source_commit":identity["source_commit"],
        "overlay_id":identity["overlay_id"],"loads":loads,"events":events}))
}
