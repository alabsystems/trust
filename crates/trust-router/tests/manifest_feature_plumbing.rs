use std::path::Path;

#[test]
fn trust_build_feature_wires_native_three_suite_libraries() {
    let manifest =
        std::fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join("Cargo.toml"))
            .expect("trust-router manifest should be readable");
    let manifest: toml::Value =
        toml::from_str(&manifest).expect("trust-router manifest should parse");
    let trust_build = manifest["features"]["trust-build"]
        .as_array()
        .expect("trust-build feature should be an array");

    let feature_edges: Vec<_> = trust_build
        .iter()
        .map(|value| value.as_str().expect("feature edge should be a string"))
        .collect();

    assert!(
        feature_edges.contains(&"trust-bmc/trust-mc-native-trust-ir-bundle"),
        "trust-router/trust-build must enable the native trust_mc typed TrustIr bundle adapter"
    );
    assert!(
        feature_edges.contains(&"trust-wp/trust-build"),
        "trust-router/trust-build must enable the native trust_wp bridge"
    );
    assert!(
        feature_edges.contains(&"trust-vc-native"),
        "trust-router/trust-build must enable the named native trust_vc lane"
    );

    let trust_vc_native = manifest["features"]["trust-vc-native"]
        .as_array()
        .expect("trust-vc-native feature should be an array");
    let native_edges: Vec<_> = trust_vc_native
        .iter()
        .map(|value| value.as_str().expect("feature edge should be a string"))
        .collect();
    assert!(
        native_edges.contains(&"trust-vc-bridge/trust-build"),
        "trust-router/trust-vc-native must forward to the native trust_vc bridge"
    );
}
