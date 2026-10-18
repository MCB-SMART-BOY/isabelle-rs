//! Verify exact binary frame identities; decoded JSON is never an independent raw record.
use crate::EvidenceError;
use crate::common::{as_array, as_str, field, require};
use serde_json::Value;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;

const FRAME_FIELDS: usize = 6;
const MAX_FRAME_BYTES: usize = 4 * 1024 * 1024;
const MAX_EVENTS: usize = 2_000_000;

pub(super) struct Frame<'a> {
    pub(super) channel: &'a str,
    pub(super) tag: &'a str,
    pub(super) run_id: &'a str,
    pub(super) root_id: &'a str,
    pub(super) local_id: &'a str,
    pub(super) payload: &'a [u8],
    pub(super) sha256: String,
}

fn read_decimal(input: &[u8], cursor: &mut usize) -> Result<usize, EvidenceError> {
    let start = *cursor;
    while input.get(*cursor).is_some_and(u8::is_ascii_digit) {
        *cursor += 1;
    }
    require(
        *cursor > start && input.get(*cursor) == Some(&b'\n'),
        "raw TLV has invalid decimal length",
    )?;
    let digits = std::str::from_utf8(&input[start..*cursor]).map_err(|source| {
        EvidenceError::Input(format!("raw TLV invalid length bytes: {source}"))
    })?;
    require(digits == "0" || !digits.starts_with('0'), "raw TLV noncanonical length")?;
    *cursor += 1;
    digits
        .parse::<usize>()
        .map_err(|source| EvidenceError::Input(format!("raw TLV length overflow: {source}")))
}

fn read_chunk<'a>(input: &'a [u8], cursor: &mut usize) -> Result<&'a [u8], EvidenceError> {
    let len = read_decimal(input, cursor)?;
    require(
        len <= MAX_FRAME_BYTES && input.len().saturating_sub(*cursor) >= len,
        "raw TLV truncated or oversized chunk",
    )?;
    let chunk = &input[*cursor..*cursor + len];
    *cursor += len;
    Ok(chunk)
}

pub(super) fn parse_fields(input: &[u8], expected: usize) -> Result<Vec<&[u8]>, EvidenceError> {
    let mut cursor = 0;
    let count = read_decimal(input, &mut cursor)?;
    require(count == expected, format!("raw TLV expected {expected} fields, found {count}"))?;
    let mut fields = Vec::with_capacity(expected);
    for _ in 0..expected {
        fields.push(read_chunk(input, &mut cursor)?);
    }
    require(cursor == input.len(), "raw TLV trailing bytes")?;
    Ok(fields)
}

fn utf8(bytes: &[u8]) -> Result<&str, EvidenceError> {
    std::str::from_utf8(bytes)
        .map_err(|source| EvidenceError::Input(format!("raw TLV field not UTF-8: {source}")))
}

pub(super) fn parse_frames(
    bytes: &[u8],
    max_events: usize,
) -> Result<Vec<Frame<'_>>, EvidenceError> {
    require(!bytes.is_empty(), "raw TLV stream is empty")?;
    let mut frames = Vec::new();
    let mut cursor = 0;
    while cursor < bytes.len() {
        require(
            frames.len() < max_events.min(MAX_EVENTS),
            "raw event count exceeds approved bound",
        )?;
        let frame = read_chunk(bytes, &mut cursor)?;
        let fields = parse_fields(frame, FRAME_FIELDS)?;
        let [channel, tag, run_id, root_id, local_id, payload] = fields.as_slice() else {
            return Err(EvidenceError::Input("raw TLV field count differs".into()));
        };
        let channel = utf8(channel)?;
        let tag = utf8(tag)?;
        let run_id = utf8(run_id)?;
        let root_id = utf8(root_id)?;
        let local_id = utf8(local_id)?;
        require(
            !run_id.is_empty() && !root_id.is_empty() && !local_id.is_empty(),
            "raw frame lacks run/root/local identity",
        )?;
        require(matches!(channel, "bootstrap" | "observer"), "raw frame unknown channel")?;
        require(
            match channel {
                "bootstrap" => {
                    matches!(tag, "load_begin" | "load_end" | "load_error" | "load_seal")
                },
                _ => matches!(
                    tag,
                    "command_begin" | "command_end" | "event" | "seal" | "callback_exception"
                ),
            },
            "raw frame unknown tag",
        )?;
        frames.push(Frame {
            channel,
            tag,
            run_id,
            root_id,
            local_id,
            payload,
            sha256: base16ct::lower::encode_string(&Sha256::digest(frame)),
        });
    }
    Ok(frames)
}

pub(super) fn referenced_frame<'a>(
    entry: &Value,
    frames: &'a [Frame<'a>],
    context: &str,
) -> Result<&'a Frame<'a>, EvidenceError> {
    referenced_frame_at(entry, frames, "raw_record_index", "raw_frame_sha256", context)
}

pub(super) fn referenced_frame_at<'a>(
    entry: &Value,
    frames: &'a [Frame<'a>],
    index_key: &str,
    hash_key: &str,
    context: &str,
) -> Result<&'a Frame<'a>, EvidenceError> {
    let index = field(entry, index_key)?
        .as_u64()
        .ok_or_else(|| EvidenceError::Input(format!("{context}: invalid raw record index")))?;
    let index = usize::try_from(index).map_err(|source| {
        EvidenceError::Input(format!("{context}: raw index overflow: {source}"))
    })?;
    let frame = frames
        .get(index)
        .ok_or_else(|| EvidenceError::Input(format!("{context}: absent raw frame {index}")))?;
    require(
        as_str(field(entry, hash_key)?, "raw frame SHA256")? == frame.sha256,
        format!("{context}: decoded frame identity differs from original raw bytes"),
    )?;
    Ok(frame)
}

/// Decode the fixed Isabelle2025 observer's YXML envelope from the opened TLV
/// bytes. Frame hashes identify bytes; they do not attest to decoded content.
pub(super) fn decode_observer_payload<'a>(
    frame: &'a Frame<'_>,
    max_depth: usize,
) -> Result<([&'a str; 5], Value), EvidenceError> {
    const ATTRIBUTES: [&str; 5] = ["phase", "theory", "source", "source_sha256", "field"];
    let text = std::str::from_utf8(frame.payload).map_err(|source| {
        EvidenceError::Input(format!("observer payload is not UTF-8: {source}"))
    })?;
    let text = text
        .strip_prefix("\x05\x06observation\x06")
        .ok_or_else(|| EvidenceError::Input("observer payload lacks YXML observation".into()))?;
    let (header, body) = text
        .split_once("\x05\x05\x06payload\x05")
        .ok_or_else(|| EvidenceError::Input("observer payload lacks typed YXML value".into()))?;
    let body = body
        .strip_suffix("\x05\x06\x05\x05\x06\x05")
        .ok_or_else(|| EvidenceError::Input("observer payload has invalid YXML ending".into()))?;
    let mut parts = header.split('\x06');
    let mut values = [""; ATTRIBUTES.len()];
    for (name, value) in ATTRIBUTES.iter().zip(&mut values) {
        let attribute = parts
            .next()
            .ok_or_else(|| EvidenceError::Input(format!("observer payload lacks {name}")))?;
        *value = attribute
            .strip_prefix(name)
            .and_then(|rest| rest.strip_prefix('='))
            .ok_or_else(|| EvidenceError::Input(format!("observer payload has invalid {name}")))?;
    }
    require(parts.next().is_none(), "observer payload has unexpected YXML attributes")?;
    let decoded =
        crate::json::decode_reader_with_limit(body.as_bytes(), max_depth).map_err(|source| {
            EvidenceError::Json { name: "original observer payload".into(), source }
        })?;
    require(decoded.is_object(), "observer payload is not a structured observation")?;
    Ok((values, decoded))
}

pub(super) fn require_all_raw_events_mapped(
    frames: &[Frame<'_>],
    decoded: &Value,
) -> Result<(), EvidenceError> {
    let mut indexed = BTreeMap::new();
    for (index, frame) in frames.iter().enumerate() {
        if frame.channel == "observer" && (frame.tag == "event" || frame.tag == "seal") {
            indexed.insert(index, false);
        }
    }
    for record in as_array(field(decoded, "records")?, "decoded records")? {
        for entry in as_array(field(record, "value")?, "decoded field values")? {
            if let Some(index) = entry.get("raw_record_index").and_then(Value::as_u64) {
                let index = usize::try_from(index).map_err(|source| {
                    EvidenceError::Input(format!("raw index overflow: {source}"))
                })?;
                let frame = referenced_frame(entry, frames, "decoded event")?;
                require(
                    frame.tag == "event"
                        && indexed.get_mut(&index).is_some_and(|used| {
                            if *used {
                                false
                            } else {
                                *used = true;
                                true
                            }
                        }),
                    "duplicate or unexpected decoded event frame",
                )?;
            }
        }
    }
    for seal in as_array(field(decoded, "coverage")?, "decoded coverage")? {
        let index = field(seal, "raw_record_index")?
            .as_u64()
            .ok_or_else(|| EvidenceError::Input("coverage missing raw record index".into()))?;
        let index = usize::try_from(index).map_err(|source| {
            EvidenceError::Input(format!("coverage raw index overflow: {source}"))
        })?;
        let frame = referenced_frame(seal, frames, "decoded coverage")?;
        require(
            frame.tag == "seal"
                && indexed.get_mut(&index).is_some_and(|used| {
                    if *used {
                        false
                    } else {
                        *used = true;
                        true
                    }
                }),
            "duplicate or unexpected coverage seal frame",
        )?;
    }
    require(
        indexed.values().all(|used| *used),
        "original raw observer event or seal omitted from decoded evidence",
    )
}
