//! Pinned upstream byte oracles for the 1.101 expectation migration.
//! The SHA256 values came from official raw rust-lang/rust files at the
//! baseline pin (`https://raw.githubusercontent.com/rust-lang/rust/<pin>/<path>`),
//! independently of both the local snapshots and their patch replacements.
//! Refreshed 2026-11-03 for 6a98084e4a21: input-stats.stderr and
//! output-default.stdout changed upstream since bf9448e4; the other four
//! oracles are byte-identical at both pins. Re-fetched 2026-11-04 for
//! cabb1ea4ced5 (main's pin moves 249cb163c0d0 and cabb1ea4ced5): all six
//! files are byte-identical at 6a98084e4a21, 249cb163c0d0 and cabb1ea4ced5.

use super::*;

fn root() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().parent().unwrap()
}

#[test]
fn repaired_snapshots_reconstruct_the_pinned_upstream_bytes() {
    let root = root();
    let baseline = fs::read_to_string(root.join("tests/upstream-rust/baseline.toml")).unwrap();
    assert!(
        baseline.contains("rust-lang/rust:cabb1ea4ced589dfee40c08aeffff3cac78af43b"),
        "refresh these independent oracles (fetched raw from rust-lang/rust at the new pin) when the upstream pin changes"
    );
    let manifest: PatchManifest =
        toml::from_str(&fs::read_to_string(root.join("tests/upstream-rust/patches.toml")).unwrap())
            .unwrap();
    for (path, expected_sha256) in [
        (
            "tests/ui/bootstrap/rustc_bootstrap.force_stable.stderr",
            "sha256:c1e2132d79a38047d17b64e7277a03b002eceb4b681851d89ac999385b893921",
        ),
        (
            "tests/ui/stats/input-stats.stderr",
            "sha256:fc5e0b71e08de651821c14f9d949912d88a31019f569b48bfdff4b94ab474407",
        ),
        (
            "tests/run-make/rustdoc/default-output/output-default.stdout",
            "sha256:8adf11f49f0a295ed332b8cebf30fa1342c5dc3e27c66abee83cf06f869929a2",
        ),
        (
            "tests/run-make/rustdoc/default-output/rmake.rs",
            "sha256:bf17d19465966b4cb2bf99f053d3662975246764132964d76c2f619f4d72f3b5",
        ),
    ] {
        let patches = manifest
            .patches
            .iter()
            .filter(|patch| {
                patch.status == PatchStatus::Active
                    && patch.kind == PatchKind::StringReplace
                    && patch.path.as_deref() == Some(path)
            })
            .collect::<Vec<_>>();
        assert!(!patches.is_empty(), "{path}: migration repair disappeared");
        let snapshot = fs::read_to_string(root.join(path)).unwrap();
        let mut upstream = snapshot.clone();
        for patch in patches.iter().rev() {
            let from = patch.replace.as_deref().unwrap();
            let to = patch.find.as_deref().unwrap();
            assert_eq!(
                upstream.matches(from).count(),
                patch.expected_replacements.unwrap_or(1),
                "{}: inverse must have exact multiplicity",
                patch.id
            );
            upstream = upstream.replace(from, to);
        }
        assert_eq!(
            sha256_bytes(upstream.as_bytes()),
            expected_sha256,
            "{path}: patch reversal must recover the independently fetched upstream bytes at the pin"
        );
        let mut replayed = upstream;
        for patch in patches {
            let from = patch.find.as_deref().unwrap();
            let to = patch.replace.as_deref().unwrap();
            assert_eq!(
                replayed.matches(from).count(),
                patch.expected_replacements.unwrap_or(1),
                "{}: forward replay must have exact multiplicity",
                patch.id
            );
            replayed = replayed.replace(from, to);
        }
        assert_eq!(replayed, snapshot, "{path}: re-import must retain the checked-in repair");
    }
}

#[test]
fn obsolete_pass_listing_patch_keeps_the_upstream_warning_case() {
    let root = root();
    let manifest: PatchManifest =
        toml::from_str(&fs::read_to_string(root.join("tests/upstream-rust/patches.toml")).unwrap())
            .unwrap();
    let row = manifest
        .patches
        .iter()
        .find(|row| row.id == "trust.divergence.rustdoc-run-lints-pass-description")
        .unwrap();
    assert_eq!(row.status, PatchStatus::Inactive);
    assert!(!root.join("tests/rustdoc-ui/issues/issue-91713.stdout").exists());
    for (path, expected_sha256) in [
        (
            "tests/rustdoc-ui/issues/issue-91713.rs",
            "sha256:2723daa7b88bdace7b109f761e74b5313aa0f98d8ef152c649a8f2170eca5b00",
        ),
        (
            "tests/rustdoc-ui/issues/issue-91713.stderr",
            "sha256:15098688c9246a65bc826e56043b12334f2bd4375bde5268a32b8e56c4c5afef",
        ),
    ] {
        assert_eq!(
            sha256_bytes(&fs::read(root.join(path)).unwrap()),
            expected_sha256,
            "{path}: retiring the unreachable listing must preserve the upstream case"
        );
    }
}
