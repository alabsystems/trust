use super::{are_equal_lockfiles, serialize_resolve};
use crate::context::GlobalContext;
use crate::resolver::encode::into_resolve;
use crate::workspace::Workspace;
use cargo_util_terminal::Shell;

const FIRST: &str =
    "git+https://example.invalid/patch?branch=main#1111111111111111111111111111111111111111";
const SECOND: &str =
    "git+https://example.invalid/patch?branch=main#2222222222222222222222222222222222222222";

fn with_workspace(locked: bool, check: impl FnOnce(&Workspace<'_>)) {
    let temp = tempfile::tempdir().unwrap();
    std::fs::create_dir(temp.path().join("src")).unwrap();
    std::fs::write(temp.path().join("src/lib.rs"), "").unwrap();
    let manifest = temp.path().join("Cargo.toml");
    std::fs::write(
        &manifest,
        "[package]\nname = 'unused-patch-root'\nversion = '0.1.0'\nedition = '2024'\n",
    )
    .unwrap();
    let mut gctx = GlobalContext::new(
        Shell::new(),
        temp.path().to_path_buf(),
        temp.path().join("home"),
    );
    gctx.set_search_stop_path(temp.path().to_path_buf());
    gctx.set_env(Default::default());
    gctx.configure(0, false, None, false, locked, true, &None, &[], &[])
        .unwrap();
    let ws = Workspace::new(&manifest, &gctx).unwrap();
    check(&ws);
}

fn patch(source: &str) -> String {
    format!("\n[[patch.unused]]\nname = 'unused'\nversion = '1.0.0'\nsource = '{source}'\n")
}

fn lock(unused: &str) -> String {
    format!("version = 4\n\n[[package]]\nname = 'unused-patch-root'\nversion = '0.1.0'\n{unused}")
}

#[test]
fn unused_patch_permutation_is_equal_when_locked() {
    with_workspace(true, |ws| {
        let first = patch(FIRST);
        let second = patch(SECOND).replace("name = 'unused'", "name = 'other'");
        assert!(are_equal_lockfiles(
            &lock(&format!("{first}{second}{first}")),
            &lock(&format!("{second}{first}{first}")),
            ws,
        ));
    });
}

#[test]
fn unused_patch_serialization_is_deterministic_and_preserves_precise_duplicates() {
    with_workspace(true, |ws| {
        let first = patch(FIRST);
        let second = patch(SECOND);
        let encode = |entries: &str| {
            let text = lock(entries);
            let resolve = into_resolve(toml::from_str(&text).unwrap(), &text, ws).unwrap();
            serialize_resolve(&resolve, None)
        };
        let left = encode(&format!("{first}{second}{first}"));
        let right = encode(&format!("{second}{first}{first}"));
        assert_eq!(left, right);
        let parsed: cargo_util_schemas::lockfile::TomlLockfile = toml::from_str(&left).unwrap();
        assert_eq!(parsed.patch.unused.len(), 3);
        let sources: Vec<_> = parsed
            .patch
            .unused
            .iter()
            .map(|p| p.source.as_ref().unwrap().source_str().as_str())
            .collect();
        assert_eq!(sources.iter().filter(|&&s| s == FIRST).count(), 2);
        assert_eq!(sources.iter().filter(|&&s| s == SECOND).count(), 1);
    });
}

#[test]
fn unused_patch_semantic_and_multiplicity_changes_remain_unequal() {
    with_workspace(true, |ws| {
        let first = patch(FIRST);
        let second = patch(SECOND);
        let original = lock(&format!("{first}{second}{first}"));
        let changes = [
            lock(&format!("{first}{second}")),
            lock(&format!("{first}{second}{first}{first}")),
            lock(&format!("{first}{second}{second}")),
            original.replace(
                "https://example.invalid/patch",
                "https://example.invalid/other",
            ),
            original.replace("branch=main", "branch=other"),
            original.replace("version = '1.0.0'", "version = '1.0.1'"),
            format!("{original}checksum = 'changed-checksum'\n"),
            format!("{original}dependencies = ['unexpected']\n"),
            format!("{original}replace = 'unexpected 1.0.0'\n"),
        ];
        for changed in changes {
            assert!(!are_equal_lockfiles(&original, &changed, ws), "{changed}");
        }
    });
}

#[test]
fn unused_patch_order_does_not_hide_active_graph_or_checksum_changes() {
    with_workspace(true, |ws| {
        let entries = format!("{}{}", patch(FIRST), patch(SECOND));
        let original = lock(&entries);
        let changed = original.replace("version = '0.1.0'", "version = '0.2.0'");
        assert!(!are_equal_lockfiles(&original, &changed, ws));
        let active = "\n[[package]]\nname = 'active'\nversion = '1.0.0'\nsource = 'registry+https://github.com/rust-lang/crates.io-index'\nchecksum = 'original'\n";
        let original = lock(&format!("{active}{entries}"));
        assert!(!are_equal_lockfiles(
            &original,
            &original.replace("checksum = 'original'", "checksum = 'changed'"),
            ws
        ));
        assert!(!are_equal_lockfiles(
            &original,
            &original.replace("name = 'active'", "name = 'different'"),
            ws
        ));
    });
}

#[test]
fn unused_patch_unlocked_comparison_still_requests_canonical_write() {
    with_workspace(false, |ws| {
        let first = patch(FIRST);
        let second = patch(SECOND);
        assert!(!are_equal_lockfiles(
            &lock(&format!("{first}{second}")),
            &lock(&format!("{second}{first}")),
            ws
        ));
    });
}
