use serde_json::json;
use sha2::{Digest, Sha256};
use xtask::reference::decode_bootstrap_events::decode_bootstrap_events_v2;

fn fields(parts: &[&[u8]]) -> Vec<u8> {
    let mut body = format!("{}\n", parts.len()).into_bytes();
    for part in parts {
        body.extend_from_slice(format!("{}\n", part.len()).as_bytes());
        body.extend_from_slice(part);
    }
    body
}

fn frame(parts: &[&[u8]]) -> Vec<u8> {
    let body = fields(parts);
    let mut raw = format!("{}\n", body.len()).into_bytes();
    raw.extend_from_slice(&body);
    raw
}

#[test]
fn decode_bootstrap_events_v2_completed_unsealed_load_stays_incomplete() {
    let source = b"real source bytes";
    let digest = base16ct::lower::encode_string(&Sha256::digest(source));
    let begin = fields(&[
        b"src/Pure/ML/ml_name_space.ML",
        b"ROOT0-host-use",
        b"Pure",
        b"",
        b"1",
        b"immutable_bootstrap_use",
        b"",
    ]);
    let mut raw = frame(&[b"bootstrap", b"load_begin", b"build", b"load-1", b"1", &begin]);
    raw.extend_from_slice(&frame(&[b"bootstrap", b"load_end", b"build", b"load-1", b"2", &begin]));
    let identity = json!({"build_run_id":"build","inventory_run_id":"inventory",
        "source_commit":"765fb2460a57eb46e8490283241ad46f1fac857f",
        "overlay_id":"overlay", "source_hashes":{"src/Pure/ML/ml_name_space.ML":digest}});
    let decoded = decode_bootstrap_events_v2(&raw, &identity).expect("decode actual partial load");
    assert_eq!(decoded["loads"][0]["finished"], true);
    assert_eq!(decoded["loads"][0]["sealed"], false);
    assert_eq!(decoded["loads"][0]["missing_parent"], true);
    assert_eq!(decoded["loads"][0]["source_provenance"], "immutable_bootstrap_use");
}

#[test]
fn decode_bootstrap_events_v2_actual_read_bytes_consumes_exact_source() {
    let source = b"real source bytes";
    let digest = base16ct::lower::encode_string(&Sha256::digest(source));
    let begin = fields(&[
        b"session/reference_observation.ML",
        b"",
        b"Pure",
        b"",
        b"1",
        b"actual_read_bytes",
        b"",
    ]);
    let end = fields(&[
        b"session/reference_observation.ML",
        b"",
        b"Pure",
        b"",
        b"1",
        b"actual_read_bytes",
        source,
    ]);
    let mut raw = frame(&[b"bootstrap", b"load_begin", b"build", b"load-1", b"begin", &begin]);
    raw.extend_from_slice(&frame(&[b"bootstrap", b"load_end", b"build", b"load-1", b"end", &end]));
    let identity = json!({"build_run_id":"build","inventory_run_id":"inventory",
        "source_commit":"765fb2460a57eb46e8490283241ad46f1fac857f",
        "overlay_id":"overlay", "source_hashes":{"session/reference_observation.ML":digest}});
    let decoded = decode_bootstrap_events_v2(&raw, &identity).expect("decode actual read");
    assert_eq!(decoded["loads"][0]["finished"], true);
    assert_eq!(decoded["loads"][0]["sealed"], false);
    assert_eq!(decoded["loads"][0]["theory"], "");
    assert_eq!(decoded["loads"][0]["source_provenance"], "actual_read_bytes");
}

#[test]
fn decode_bootstrap_events_v2_malformed_load_field_count_rejects() {
    let digest = base16ct::lower::encode_string(&Sha256::digest(b"real source bytes"));
    let identity = json!({"build_run_id":"build","inventory_run_id":"inventory",
        "source_commit":"765fb2460a57eb46e8490283241ad46f1fac857f",
        "overlay_id":"overlay", "source_hashes":{"src/Pure/ML/ml_name_space.ML":digest}});
    for parts in [
        vec![
            b"src/Pure/ML/ml_name_space.ML".as_slice(),
            b"",
            b"Pure",
            b"1",
            b"immutable_bootstrap_use",
            b"",
        ],
        vec![
            b"src/Pure/ML/ml_name_space.ML".as_slice(),
            b"",
            b"Pure",
            b"",
            b"1",
            b"immutable_bootstrap_use",
            b"",
            b"unexpected",
        ],
    ] {
        let payload = fields(&parts);
        let raw = frame(&[b"bootstrap", b"load_begin", b"build", b"load-1", b"begin", &payload]);
        let error = decode_bootstrap_events_v2(&raw, &identity).unwrap_err();
        assert!(error.to_string().contains("expected 7 TLV fields"), "{error}");
    }
}

#[test]
fn decode_bootstrap_events_v2_duplicate_begin_rejects() {
    let digest = base16ct::lower::encode_string(&Sha256::digest(b"real source bytes"));
    let identity = json!({"build_run_id":"build","inventory_run_id":"inventory",
        "source_commit":"765fb2460a57eb46e8490283241ad46f1fac857f",
        "overlay_id":"overlay", "source_hashes":{"src/Pure/ML/ml_name_space.ML":digest}});
    let payload = fields(&[
        b"src/Pure/ML/ml_name_space.ML",
        b"",
        b"Pure",
        b"",
        b"1",
        b"immutable_bootstrap_use",
        b"",
    ]);
    let mut raw = frame(&[b"bootstrap", b"load_begin", b"build", b"load-1", b"begin", &payload]);
    raw.extend_from_slice(&frame(&[
        b"bootstrap",
        b"load_begin",
        b"build",
        b"load-1",
        b"duplicate",
        &payload,
    ]));
    let error = decode_bootstrap_events_v2(&raw, &identity).unwrap_err();
    assert!(error.to_string().contains("duplicate bootstrap load begin"), "{error}");
}

#[test]
fn decode_bootstrap_events_v2_wrong_consumed_bytes_rejects() {
    let digest = base16ct::lower::encode_string(&Sha256::digest(b"approved source bytes"));
    let identity = json!({"build_run_id":"build","inventory_run_id":"inventory",
        "source_commit":"765fb2460a57eb46e8490283241ad46f1fac857f",
        "overlay_id":"overlay", "source_hashes":{"src/Pure/ML/ml_name_space.ML":digest}});
    let begin = fields(&[
        b"src/Pure/ML/ml_name_space.ML",
        b"",
        b"Pure",
        b"",
        b"1",
        b"actual_read_bytes",
        b"",
    ]);
    let end = fields(&[
        b"src/Pure/ML/ml_name_space.ML",
        b"",
        b"Pure",
        b"",
        b"1",
        b"actual_read_bytes",
        b"different source bytes",
    ]);
    let mut raw = frame(&[b"bootstrap", b"load_begin", b"build", b"load-1", b"begin", &begin]);
    raw.extend_from_slice(&frame(&[b"bootstrap", b"load_end", b"build", b"load-1", b"end", &end]));
    let error = decode_bootstrap_events_v2(&raw, &identity).unwrap_err();
    assert!(error.to_string().contains("consumed source differs"), "{error}");
}

#[test]
fn decode_bootstrap_events_v2_empty_source_preserves_unsealed_load() {
    let source = b"";
    let digest = base16ct::lower::encode_string(&Sha256::digest(source));
    let payload =
        fields(&[b"src/Pure/empty.ML", b"", b"Pure", b"", b"1", b"actual_read_bytes", source]);
    let mut raw = frame(&[b"bootstrap", b"load_begin", b"build", b"empty", b"begin", &payload]);
    raw.extend_from_slice(&frame(&[
        b"bootstrap",
        b"load_end",
        b"build",
        b"empty",
        b"end",
        &payload,
    ]));
    let identity = json!({"build_run_id":"build","inventory_run_id":"inventory",
        "source_commit":"765fb2460a57eb46e8490283241ad46f1fac857f",
        "overlay_id":"overlay", "source_hashes":{"src/Pure/empty.ML":digest}});
    let decoded = decode_bootstrap_events_v2(&raw, &identity).expect("empty source is valid ML");
    assert_eq!(decoded["loads"][0]["source_sha256"], digest);
    assert_eq!(decoded["loads"][0]["finished"], true);
    assert_eq!(decoded["loads"][0]["sealed"], false);
}
