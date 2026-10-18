use serde_json::json;
use xtask::reference::decode_bootstrap_events::{decode_bootstrap_events_v2, decode_raw_records};

fn encode_fields(fields: &[&[u8]]) -> Vec<u8> {
    let mut body = format!("{}\n", fields.len()).into_bytes();
    for field in fields {
        body.extend_from_slice(format!("{}\n", field.len()).as_bytes());
        body.extend_from_slice(field);
    }
    body
}

fn encode_frame(fields: &[&[u8]]) -> Vec<u8> {
    let body = encode_fields(fields);
    let mut frame = format!("{}\n", body.len()).into_bytes();
    frame.extend_from_slice(&body);
    frame
}

#[test]
fn decode_raw_records_truncated_frame_rejects() {
    let frame = encode_frame(&[b"bootstrap", b"load_begin", b"build", b"load-1", b"1", b"x"]);
    assert!(decode_raw_records(&frame[..frame.len() - 1]).is_err());
}

#[test]
fn decode_raw_records_duplicate_or_overflow_length_rejects() {
    for raw in [b"01\n".as_slice(), b"184467440737095516161234567890\n"] {
        assert!(decode_raw_records(raw).is_err());
    }
}

#[test]
fn decode_raw_records_invalid_utf8_identity_rejects() {
    let frame = encode_frame(&[b"bootstrap", b"load_begin", b"build", b"load-1", &[0xff], b"x"]);
    assert!(decode_raw_records(&frame).is_err());
}

#[test]
fn decode_bootstrap_events_v2_wrong_loaded_bytes_rejects() {
    let begin = encode_fields(&[
        b"src/Pure/ROOT.ML",
        b"",
        b"Pure",
        b"Pure",
        b"1",
        b"actual_read_bytes",
        b"",
    ]);
    let end = encode_fields(&[
        b"src/Pure/ROOT.ML",
        b"",
        b"Pure",
        b"Pure",
        b"1",
        b"actual_read_bytes",
        b"loaded",
    ]);
    let mut frame = encode_frame(&[b"bootstrap", b"load_begin", b"build", b"load-1", b"1", &begin]);
    frame.extend_from_slice(&encode_frame(&[
        b"bootstrap",
        b"load_end",
        b"build",
        b"load-1",
        b"2",
        &end,
    ]));
    let identity = json!({"source_commit":"765fb2460a57eb46e8490283241ad46f1fac857f",
        "overlay_id":"overlay", "build_run_id":"build", "inventory_run_id":"inventory",
        "source_hashes":{"src/Pure/ROOT.ML":"0000000000000000000000000000000000000000000000000000000000000000"}});
    assert!(decode_bootstrap_events_v2(&frame, &identity).is_err());
}

#[test]
fn decode_raw_records_exact_binary_payload_round_trips() {
    let frame =
        encode_frame(&[b"bootstrap", b"load_begin", b"build", b"load-1", b"1", &[0, 5, 6, 255]]);
    let records = decode_raw_records(&frame).expect("valid exact TLV frame");
    assert_eq!(records.len(), 1);
    assert_eq!(records[0].payload, &[0, 5, 6, 255]);
}
