// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Actual importer/capture controls, not production mathematical proofs.

use super::*;
use clean_kernel::{Declaration, Expr};
use clean_olean::OleanExporter;

const EXPORT_HASH: &str = "0000000000000000000000000000000000000000";

fn exported(name: &str, imports: &[(&str, bool)]) -> Vec<u8> {
    let mut env = Environment::default();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name), level_params: vec![], type_: Expr::prop(),
    }).unwrap();
    OleanExporter::export_with_env(&env, imports, &[], EXPORT_HASH).unwrap()
}

fn inventory(root: &Path) -> Manifest {
    let modules = ["VF5Check", "Child"].into_iter().map(|name| {
        let path = root.join(format!("{name}.olean"));
        let base = std::fs::read(&path).unwrap();
        let optional = |extension: &str| match std::fs::read(path.with_extension(extension)) {
            Ok(bytes) => Some(format!("{:x}", Sha256::digest(&bytes))),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
            Err(error) => panic!("fixture part unreadable: {error}"),
        };
        Module {
            path: format!("{name}.olean"), base_sha256: format!("{:x}", Sha256::digest(&base)),
            server_sha256: optional("olean.server"), private_sha256: optional("olean.private"),
            ir_sha256: optional("ir"),
        }
    }).collect();
    Manifest {
        schema: 1, clean_revision: CLEAN_REVISION.into(), lean_world: LEAN_WORLD.into(),
        source_files: BTreeMap::from([("capture-only-fixture.lean".into(), "a".repeat(64))]),
        modules,
    }
}

#[test]
fn bounded_vf5_import_preserves_real_graph_and_enforces_each_capture_limit() {
    let directory = tempfile::tempdir().unwrap();
    let root = directory.path().canonicalize().unwrap();
    let base = exported("Probe.root", &[("Child", false)]);
    let child = exported("Probe.child", &[]);
    let ir = b"captured IR DATA";
    std::fs::write(root.join("VF5Check.olean"), &base).unwrap();
    std::fs::write(root.join("Child.olean"), &child).unwrap();
    std::fs::write(root.join("VF5Check.ir"), ir).unwrap();
    let manifest = inventory(&root);
    validate_manifest(&manifest).unwrap();
    let largest = base.len().max(child.len()).max(ir.len());
    let total = base.len() + child.len() + ir.len();
    let exact = ModuleCaptureLimits::new(largest, total, 2, 1);
    let (limited, count) = import_with_limits(&root, &manifest, exact).unwrap();
    assert_eq!(count, 2);

    // Compare with the maintained ordinary checked importer, not a fake
    // loader or a preconstructed favorable report. All four parts/absence
    // checks still run inside the actual VF5 wrapper above.
    let mut ordinary = Environment::for_lean_replay();
    let mut captured = Vec::new();
    let summaries = clean_olean::load_modules_with_deps_checked(
        &mut ordinary, &[ROOT_MODULE.into()], &[root.clone()],
        &mut |_, _, _| Ok(()),
        &mut |name, _, bytes| {
            captured.push((name.clone(), bytes.base.to_vec(), bytes.server.map(<[u8]>::to_vec),
                bytes.private.map(<[u8]>::to_vec), bytes.ir.map(<[u8]>::to_vec)));
            Ok(())
        },
    ).unwrap();
    assert_eq!(summaries.len(), count);
    assert_eq!(ordinary.constants().count(), limited.constants().count());
    for name in ["Probe.root", "Probe.child"] {
        assert!(ordinary.get_const(&Name::from_string(name)).is_some());
        assert!(limited.get_const(&Name::from_string(name)).is_some());
    }
    let root_parts = captured.iter().find(|part| part.0 == Name::from_string(ROOT_MODULE)).unwrap();
    assert_eq!(root_parts.1, base);
    assert!(root_parts.2.is_none() && root_parts.3.is_none());
    assert_eq!(root_parts.4.as_deref(), Some(ir.as_slice()));

    for (bound, limits) in [
        ("part", ModuleCaptureLimits::new(largest - 1, total, 2, 1)),
        ("graph", ModuleCaptureLimits::new(largest, total - 1, 2, 1)),
        ("modules", ModuleCaptureLimits::new(largest, total, 1, 1)),
        ("imports", ModuleCaptureLimits::new(largest, total, 2, 0)),
    ] {
        let error = import_with_limits(&root, &manifest, limits).unwrap_err();
        match error {
            Vf5BaseMiss::Import(ImportError::ResourceLimit { .. }) => {}
            Vf5BaseMiss::Import(ImportError::FileUnreadable { source, .. }) => {
                assert_eq!(source.kind(), std::io::ErrorKind::InvalidData, "{bound}");
            }
            other => panic!("{bound} did not stop real capture at its budget: {other:?}"),
        }
    }
    std::fs::write(root.join("VF5Check.ir"), b"changed IR DATA").unwrap();
    assert!(matches!(import_with_limits(&root, &manifest, vf5_capture_limits()),
        Err(Vf5BaseMiss::Import(ImportError::UnsupportedModule { .. }))));
}

#[test]
fn vf5_import_counts_borrowed_companion_rows_for_every_present_root() {
    let directory = tempfile::tempdir().unwrap();
    let root = directory.path().canonicalize().unwrap();
    let base = exported("Probe.root", &[("Child", false)]);
    let header = clean_olean::parse_header(&base).unwrap();
    let region = clean_olean::CompactedRegion::new(&base, header.base_addr);
    let root_pointer = region.read_u64_at(clean_olean::HEADER_SIZE).unwrap();
    let empty = clean_olean::payload::CleanPayload::default();
    let mut server = OleanExporter::export_with_payload_after(
        &base, &[], &[], &[], EXPORT_HASH, &empty,
    ).unwrap();
    let slot = clean_olean::HEADER_SIZE;
    server[slot..slot + 8].copy_from_slice(&root_pointer.to_le_bytes());
    let mut private = OleanExporter::export_with_payload_after(
        &server, &[], &[], &[], EXPORT_HASH, &empty,
    ).unwrap();
    private[slot..slot + 8].copy_from_slice(&root_pointer.to_le_bytes());
    let child = exported("Probe.child", &[]);
    std::fs::write(root.join("VF5Check.olean"), &base).unwrap();
    std::fs::write(root.join("VF5Check.olean.server"), &server).unwrap();
    std::fs::write(root.join("VF5Check.olean.private"), &private).unwrap();
    std::fs::write(root.join("Child.olean"), &child).unwrap();
    let manifest = inventory(&root);
    let largest = [base.len(), server.len(), private.len(), child.len()].into_iter().max().unwrap();
    let total = base.len() + server.len() + private.len() + child.len();
    assert!(matches!(import_with_limits(&root, &manifest,
        ModuleCaptureLimits::new(largest, total, 2, 2)),
        Err(Vf5BaseMiss::Import(ImportError::ResourceLimit { .. }))));
    let (env, count) = import_with_limits(&root, &manifest,
        ModuleCaptureLimits::new(largest, total, 2, 3)).unwrap();
    assert_eq!(count, 2);
    assert!(env.get_const(&Name::from_string("Probe.root")).is_some());
    assert!(env.get_const(&Name::from_string("Probe.child")).is_some());
}
