use super::{percent_decode_url_path, version_label_for_channel};

#[test]
fn version_label_uses_channel_for_train_channels() {
    assert_eq!(version_label_for_channel("beta", "1.96.0-beta.1 (hash date)"), "beta");
    assert_eq!(version_label_for_channel("nightly", "1.96.0-nightly (hash date)"), "nightly");
}

#[test]
fn version_label_uses_channel_for_trust_channels() {
    assert_eq!(version_label_for_channel("trust", "1.96.0-trust (hash date)"), "trust");
    assert_eq!(
        version_label_for_channel("trust-2026-04-24", "1.96.0-trust (hash date)"),
        "trust-2026-04-24"
    );
    assert_eq!(version_label_for_channel("Trust", "1.96.0-trust (hash date)"), "Trust");
}

#[test]
fn version_label_uses_manifest_version_for_numbered_channels() {
    assert_eq!(version_label_for_channel("1.95", "1.95.1 (hash date)"), "1.95.1");
}

#[test]
fn file_url_paths_are_percent_decoded() {
    assert_eq!(percent_decode_url_path("/tmp/trust%20stage0").unwrap(), "/tmp/trust stage0");
}
