//! Real resolver regression: transport feature unification must not put
//! provenance back beneath its own vendored OpenSSL build dependency.

#[test]
fn committed_git_and_vendored_openssl_resolve_without_a_provenance_cycle() {
    let manifest = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("Cargo.toml");
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_targo"))
        .args([
            "metadata",
            "--offline",
            "--locked",
            "--format-version",
            "1",
            "--features",
            "all-static",
            "--manifest-path",
        ])
        .arg(manifest)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let graph: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    let packages = graph["packages"].as_array().unwrap();
    let openssl = packages
        .iter()
        .find(|p| p["name"] == "trust-openssl-src")
        .unwrap();
    let dependencies = openssl["dependencies"].as_array().unwrap();
    assert!(dependencies.iter().any(|d| d["name"] == "trust-fs-acl"));
    assert!(
        !dependencies
            .iter()
            .any(|d| d["name"] == "trust-resource-provenance")
    );
    let provenance = packages
        .iter()
        .find(|p| p["name"] == "trust-resource-provenance")
        .unwrap();
    let nodes = graph["resolve"]["nodes"].as_array().unwrap();
    let committed = packages
        .iter()
        .find(|p| p["name"] == "trust-committed-source")
        .unwrap();
    let committed_node = nodes.iter().find(|n| n["id"] == committed["id"]).unwrap();
    let gix_id = &committed_node["deps"]
        .as_array()
        .unwrap()
        .iter()
        .find(|d| d["name"] == "gix")
        .unwrap()["pkg"];
    let gix_node = nodes.iter().find(|n| &n["id"] == gix_id).unwrap();
    assert!(
        gix_node["features"]
            .as_array()
            .unwrap()
            .iter()
            .any(|f| f == "blocking-http-transport-curl")
    );
    assert!(
        !provenance["dependencies"]
            .as_array()
            .unwrap()
            .iter()
            .any(|d| d["name"] == "gix")
    );
}
