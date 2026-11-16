//! Real vendored-olean consumer regressions. These are imported-context checks,
//! never closed-kernel or bridge-agreement authority.
use std::sync::atomic::{AtomicU64, Ordering};

use super::*;

struct Package {
    root: PathBuf,
    trustir: PathBuf,
    core: PathBuf,
}
impl Package {
    fn real() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let root = std::env::temp_dir().join(format!(
            "trust-manifest-binding-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir(&root).unwrap();
        let config = BridgeGateConfig::locate(BridgeGateMode::Spot);
        let trustir = root.join("trustir");
        let core = root.join("core");
        Self::flatten(&config.trustir_olean_dir, &trustir);
        Self::flatten(&config.lean_core_olean_dir, &core);
        Self { root, trustir, core }
    }
    fn flatten(source: &Path, dest: &Path) {
        std::fs::create_dir(dest).unwrap();
        let mut doc: toml::Value =
            toml::from_str(&std::fs::read_to_string(source.join("MANIFEST.toml")).unwrap())
                .unwrap();
        let host = host_triple();
        let shared = doc["files"].as_table().unwrap().clone();
        let platform = doc["platforms"][&host].as_table().unwrap().clone();
        let mut selected = shared.clone();
        if let Some(files) = platform.get("files") {
            selected.extend(files.as_table().unwrap().clone());
        }
        for (name, _) in &selected {
            let specific = platform
                .get("files")
                .and_then(|v| v.as_table())
                .is_some_and(|files| files.contains_key(name));
            let src = if specific {
                source.join("platform").join(&host).join(name)
            } else {
                source.join(name)
            };
            let target = dest.join(name);
            std::fs::create_dir_all(target.parent().unwrap()).unwrap();
            std::fs::copy(src, target).unwrap();
        }
        doc["files"] = toml::Value::Table(selected);
        let mut only_platform = platform;
        only_platform.remove("files");
        let mut platforms = toml::map::Map::new();
        platforms.insert(host, toml::Value::Table(only_platform));
        doc["platforms"] = toml::Value::Table(platforms);
        std::fs::write(dest.join("MANIFEST.toml"), toml::to_string_pretty(&doc).unwrap()).unwrap();
    }
    fn verified(&self) -> (VerifiedTree, VerifiedTree) {
        (
            verify_manifest(&self.trustir, TRUSTIR_MANIFEST_SCHEMA, true).unwrap(),
            verify_manifest(&self.core, LEAN_CORE_MANIFEST_SCHEMA, false).unwrap(),
        )
    }
    fn save(&self, label: &str, result: serde_json::Value) {
        if let Some(out) = std::env::var_os("TRUST_MANIFEST_BINDING_OUTPUT_DIR") {
            let out = PathBuf::from(out).join(label);
            std::fs::create_dir_all(&out).unwrap();
            for (name, path) in [
                ("trustir-MANIFEST.toml", self.trustir.join("MANIFEST.toml")),
                ("core-MANIFEST.toml", self.core.join("MANIFEST.toml")),
                ("verified-shared.olean", self.trustir.join("TrustIr/CmpOp.olean")),
                (
                    "selected-shadow.olean",
                    self.trustir.join("platform").join(host_triple()).join("TrustIr/CmpOp.olean"),
                ),
            ] {
                if path.is_file() {
                    std::fs::copy(path, out.join(name)).unwrap();
                }
            }
            std::fs::write(
                out.join("observation.json"),
                serde_json::to_vec_pretty(&result).unwrap(),
            )
            .unwrap();
        }
    }
}
impl Drop for Package {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.root);
    }
}
#[test]
fn real_consumer_unlisted_platform_shadow_boundary() {
    let package = Package::real();
    let shadow = package.trustir.join("platform").join(host_triple()).join("TrustIr/CmpOp.olean");
    std::fs::create_dir_all(shadow.parent().unwrap()).unwrap();
    std::fs::copy(package.trustir.join("TrustIr/Ordering.olean"), &shadow).unwrap();
    let (trustir, core) = package.verified(); // Shared digest/provenance REALLY pass.
    let mut env = Environment::default();
    env.ensure_native_reducers();
    let roots = vec!["TrustIr.CmpOp".to_owned()];
    let result = load_verified_modules(&mut env, &roots, &trustir, &core);
    let error = result.expect_err("unlisted platform bytes cannot shadow verified shared input");
    package.save("fixed-unlisted-shadow",serde_json::json!({"refused":error.to_string(),"has_expected_ICmpOp":env.get_inductive(&Name::from_string("TrustIr.ICmpOp")).is_some(),"has_unverified_MemOrdering":env.get_inductive(&Name::from_string("TrustIr.MemOrdering")).is_some(),"scope":"actual production importer refuses before registering any artifact; imported TCB only"}));
    assert!(error.to_string().contains("actual selected path"), "{error:?}");
    assert!(env.get_inductive(&Name::from_string("TrustIr.MemOrdering")).is_none());
    assert!(env.get_inductive(&Name::from_string("TrustIr.ICmpOp")).is_none());
}

fn import(
    _package: &Package,
    trustir: &VerifiedTree,
    core: &VerifiedTree,
) -> Result<Environment, BridgeGateError> {
    let mut env = Environment::default();
    env.ensure_native_reducers();
    load_verified_modules(&mut env, &["TrustIr.CmpOp".into()], trustir, core)?;
    Ok(env)
}
fn edit_manifest(root: &Path, edit: impl FnOnce(&mut toml::Value)) {
    let path = root.join("MANIFEST.toml");
    let mut doc: toml::Value = toml::from_str(&std::fs::read_to_string(&path).unwrap()).unwrap();
    edit(&mut doc);
    std::fs::write(path, toml::to_string_pretty(&doc).unwrap()).unwrap();
}
fn declare_platform(root: &Path, rel: &str, keep_shared: bool) -> PathBuf {
    let shared = root.join(rel);
    let path = root.join("platform").join(host_triple()).join(rel);
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::copy(&shared, &path).unwrap();
    edit_manifest(root, |doc| {
        let digest = doc["files"][rel].clone();
        if !keep_shared {
            doc["files"].as_table_mut().unwrap().remove(rel);
        }
        let host = host_triple();
        let row = doc["platforms"][host.as_str()].as_table_mut().unwrap();
        if !row.contains_key("files") {
            row.insert("files".into(), toml::Value::Table(toml::map::Map::new()));
        }
        let files = row.get_mut("files").unwrap();
        files.as_table_mut().unwrap().insert(rel.into(), digest);
    });
    path
}
#[test]
fn real_consumer_preserves_shared_and_declared_platform_inputs_for_both_manifests() {
    let package = Package::real();
    let (trustir, core) = package.verified();
    let env = import(&package, &trustir, &core).unwrap();
    assert!(env.get_inductive(&Name::from_string("TrustIr.ICmpOp")).is_some());
    // Declared overrides are legitimate, including a declared shared fallback.
    declare_platform(&package.trustir, "TrustIr/CmpOp.olean", true);
    declare_platform(&package.core, "Init/Prelude.olean", false);
    let (trustir, core) = package.verified();
    let env = import(&package, &trustir, &core).unwrap();
    assert!(env.get_inductive(&Name::from_string("TrustIr.ICmpOp")).is_some());
    assert!(env.get_inductive(&Name::from_string("TrustIr.MemOrdering")).is_none());
    package.save("shared-and-explicit-platform-positive",serde_json::json!({"shared_pass":true,"trustir_declared_override_pass":true,"core_declared_override_pass":true,"scope":"input-import preservation under imported TCB; no full agreement or proof grade"}));
}
#[test]
fn real_consumer_rechecks_captured_bytes_after_manifest_verification() {
    let package = Package::real();
    let (trustir, core) = package.verified();
    std::fs::copy(
        package.trustir.join("TrustIr/Ordering.olean"),
        package.trustir.join("TrustIr/CmpOp.olean"),
    )
    .unwrap();
    let error = import(&package, &trustir, &core).err().unwrap();
    assert!(error.to_string().contains("captured base sha256"), "{error:?}");
    package.save("changed-after-manifest-check",serde_json::json!({"refused":error.to_string(),"authority":"actual captured bytes, not earlier path/hash check"}));
}
#[test]
fn real_consumer_refuses_missing_selected_override_without_fallback() {
    let package = Package::real();
    let selected = declare_platform(&package.trustir, "TrustIr/CmpOp.olean", true);
    let (trustir, core) = package.verified();
    std::fs::remove_file(selected).unwrap();
    let error = import(&package, &trustir, &core).err().unwrap();
    assert!(error.to_string().contains("actual selected path"), "{error:?}");
}
#[test]
fn real_consumer_refuses_unlisted_module_and_companion_inputs() {
    for mode in 0..4 {
        let package = Package::real();
        if mode == 0 {
            edit_manifest(&package.trustir, |doc| {
                doc["files"].as_table_mut().unwrap().remove("TrustIr/CmpOp.olean");
            });
        } else {
            let extension = ["unused", "olean.server", "olean.private", "ir"][mode];
            std::fs::write(
                package.trustir.join("TrustIr/CmpOp.olean").with_extension(extension),
                b"unlisted input must be refused before parse",
            )
            .unwrap();
        }
        let (trustir, core) = package.verified();
        let error = import(&package, &trustir, &core).err().unwrap();
        assert!(
            error.to_string().contains(if mode == 0 {
                "absent from verified inventory"
            } else {
                "unmanifested captured companion/IR"
            }),
            "mode{mode}: {error:?}"
        );
    }
}
#[test]
fn real_consumer_rejects_ambiguous_inventory_and_unchecked_existing_environment() {
    let package = Package::real();
    let bytes = std::fs::read(package.trustir.join("TrustIr/CmpOp.olean")).unwrap();
    let path = package.core.join("TrustIr/CmpOp.olean");
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(&path, &bytes).unwrap();
    let digest = sha256_file(&path).unwrap();
    edit_manifest(&package.core, |doc| {
        doc["files"]
            .as_table_mut()
            .unwrap()
            .insert("TrustIr/CmpOp.olean".into(), toml::Value::String(digest));
    });
    let (trustir, core) = package.verified();
    let error = import(&package, &trustir, &core).err().unwrap();
    assert!(error.to_string().contains("ambiguous module across manifests"), "{error:?}");
    let package = Package::real();
    let (trustir, core) = package.verified();
    let mut env = Environment::default();
    let mut paths = trustir.search_dirs();
    paths.extend(core.search_dirs());
    clean_olean::load_modules_with_deps(&mut env, &["TrustIr.Ordering".into()], &paths).unwrap();
    let error =
        load_verified_modules(&mut env, &["TrustIr.CmpOp".into()], &trustir, &core).unwrap_err();
    assert!(error.to_string().contains("fresh bridge environment"), "{error:?}");
}
#[test]
#[cfg(unix)]
fn real_consumer_refuses_selected_symlinks_and_unsafe_manifest_paths() {
    let package = Package::real();
    let (trustir, core) = package.verified();
    let path = package.trustir.join("TrustIr/CmpOp.olean");
    let real = package.trustir.join("genuine-copy.olean");
    std::fs::rename(&path, &real).unwrap();
    std::os::unix::fs::symlink(&real, &path).unwrap();
    let error = import(&package, &trustir, &core).err().unwrap();
    assert!(error.to_string().contains("symlink/nonregular"), "{error:?}");
    for key in [
        "../escape.olean",
        "/absolute.olean",
        "TrustIr//Empty.olean",
        "TrustIr/../Parent.olean",
        "TrustIr\\Escape.olean",
    ] {
        let package = Package::real();
        edit_manifest(&package.trustir, |doc| {
            doc["files"]
                .as_table_mut()
                .unwrap()
                .insert(key.into(), toml::Value::String("0".repeat(64)));
        });
        let error = verify_manifest(&package.trustir, TRUSTIR_MANIFEST_SCHEMA, true).unwrap_err();
        assert!(error.to_string().contains("module inventory key"), "{key}: {error:?}");
    }
}

#[test]
fn real_consumer_loads_complete_current_vendored_population() {
    let config = BridgeGateConfig::locate(BridgeGateMode::Spot);
    let trustir =
        verify_manifest(&config.trustir_olean_dir, TRUSTIR_MANIFEST_SCHEMA, true).unwrap();
    let core =
        verify_manifest(&config.lean_core_olean_dir, LEAN_CORE_MANIFEST_SCHEMA, false).unwrap();
    let mut env = Environment::default();
    env.ensure_native_reducers();
    let roots = BRIDGE_ROOT_MODULES.iter().map(|n| n.to_string()).collect::<Vec<_>>();
    let summaries = load_verified_modules(&mut env, &roots, &trustir, &core).unwrap();
    let actual = summaries
        .iter()
        .filter_map(|s| s.module_name.as_ref())
        .map(|name| name.replace('.', "/") + ".olean")
        .collect::<BTreeSet<_>>();
    let expected = trustir.files.union(&core.files).cloned().collect::<BTreeSet<_>>();
    assert_eq!(actual, expected, "no imported or manifested module may disappear");
    assert!(!trustir.files.is_empty(), "TrustIr population must be present");
    assert!(!core.files.is_empty(), "Lean-core population must be present");
    if let Some(out) = std::env::var_os("TRUST_MANIFEST_BINDING_OUTPUT_DIR") {
        let out = PathBuf::from(out).join("actual-complete-population");
        std::fs::create_dir_all(&out).unwrap();
        std::fs::write(out.join("import.json"),serde_json::to_vec_pretty(&serde_json::json!({"modules":actual,"trustir_count":trustir.files.len(),"core_count":core.files.len(),"constants_loaded":summaries.iter().map(|s|s.added_constants).sum::<usize>(),"scope":"actual complete manifest-bound import under imported TCB; no closed replay or full agreement claim"})).unwrap()).unwrap();
    }
}
