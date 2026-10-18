use super::*;

#[test]
fn compare_v2_bootstrap_observation_without_seal_remains_incomplete() {
    let mut fixture = ObservedFixture::new();
    fixture.is_bootstrap_sealed = false;
    let reference = fixture.verify().expect("valid original bootstrap observation");
    let comparison = compare_candidate(&reference, &fixture.base.candidate).unwrap();
    assert!(matches!(comparison, Comparison::Incomplete(_)), "{comparison:?}");
    let report = OfficialCompatibilityResult::from_comparison(comparison).as_json();
    assert_eq!(report["result"], "BlockedPrerequisite");
}

#[test]
fn verify_v2_bootstrap_altered_decoded_payload_rejects() {
    for (key, value) in [
        ("value", json!({"kind":"forged_registration"})),
        ("field", json!("anonymous_ephemeral_facts")),
    ] {
        let mut fixture = ObservedFixture::new();
        fixture.assemble_observations();
        let mut bootstrap: Value =
            serde_json::from_slice(&fixture.base.artifacts["bootstrap-events"]).unwrap();
        bootstrap["events"][0][key] = value;
        fixture
            .base
            .artifacts
            .insert("bootstrap-events".into(), serde_json::to_vec(&bootstrap).unwrap());
        let error = fixture.verify_assembled().unwrap_err();
        assert!(matches!(error, EvidenceError::Input(_)), "{key}: {error}");
    }
}
