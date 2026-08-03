use cargo_metadata::camino::Utf8Path;
use cargo_metadata::{DependencyKind, Metadata, NodeDep, Package};
use clippy_utils::diagnostics::span_lint_and_then;
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_lint::LateContext;
use rustc_span::DUMMY_SP;

use super::TRUST_EXTERNAL_DEPENDENCY_SOURCE;

pub(super) fn check(cx: &LateContext<'_>, metadata: &Metadata) {
    let Some(resolve) = metadata.resolve.as_ref() else {
        return;
    };
    let Some(local) = local_package(cx, metadata) else {
        return;
    };
    let Some(node) = resolve.nodes.iter().find(|node| node.id == local.id) else {
        return;
    };

    // `node.deps` is the resolved edge set of this package alone, so every entry
    // is a dependency the local manifest asked for by name. The rest of the graph
    // is reached only through one of these, and nothing in it can be brought
    // in-tree before its parent is, so reporting it here would name manifests the
    // author cannot edit.
    let mut external: Vec<(&Package, &str, DependencyKind)> = node
        .deps
        .iter()
        .filter_map(|dep| {
            let package = metadata.packages.iter().find(|package| package.id == dep.pkg)?;
            let source = source_outside_tree(
                package.source.as_ref().map(|source| source.repr.as_str()),
                &package.manifest_path,
                &metadata.workspace_root,
            )?;
            Some((package, source, edge_kind(dep)))
        })
        .collect();
    // `resolve.nodes` carries no documented order, and a per-dependency report is
    // only reviewable if the same manifest yields the same list on every run.
    external
        .sort_unstable_by(|(left, ..), (right, ..)| (&left.name, &left.version).cmp(&(&right.name, &right.version)));

    for (package, source, kind) in external {
        span_lint_and_then(
            cx,
            TRUST_EXTERNAL_DEPENDENCY_SOURCE,
            DUMMY_SP,
            format!(
                "{} `{} v{}` is built from a source outside this tree",
                kind_word(kind),
                package.name,
                package.version,
            ),
            |diag| {
                diag.note(format!("cargo resolves it from `{source}`"));
                diag.help(
                    "vendor the source in-tree — a path dependency, a workspace member, or a copy under `vendor/` — so it compiles under `trustc` with the rest of this tree, where it can be given contracts and repaired in place",
                );
            },
        );
    }
}

/// The source cargo fetches a package from, when that source is not the tree
/// being compiled.
///
/// Two facts decide this, and neither alone is enough.
///
/// Cargo writes a null source for a path source and only for a path source, so
/// `None` here already covers a path dependency, a workspace member, and a
/// `[patch]` redirected at either — including a path dependency that also
/// carries a `version`, and one that lives outside the workspace root. None of
/// those is fetched: cargo compiles them from a directory someone can edit.
///
/// A vendored tree is the case the source id alone gets wrong. Source
/// replacement (`cargo vendor` plus `[source] replace-with`) deliberately keeps
/// the id of the registry it replaced, so the package still reports
/// `registry+…` while the manifest cargo actually reads sits under the
/// workspace root. The manifest path is what settles it.
fn source_outside_tree<'a>(
    source: Option<&'a str>,
    manifest_path: &Utf8Path,
    workspace_root: &Utf8Path,
) -> Option<&'a str> {
    let source = source?;
    if manifest_path.starts_with(workspace_root) {
        return None;
    }
    // Only the ids that name a registry or a git repository are reported. An id
    // this pass does not recognise is left alone: an unreportable dependency is a
    // gap, a misreported one is a false claim about someone's manifest.
    ["registry+", "sparse+", "git+"]
        .iter()
        .any(|scheme| source.starts_with(scheme))
        .then_some(source)
}

/// The workspace package whose crate is being compiled, or `None` if no member
/// name matches it.
///
/// The metadata names packages, not compilation units, so the crate name is the
/// only handle this pass has. A target whose crate name differs from its
/// package name — a renamed `[[bin]]`, or a build script — therefore matches
/// nothing and reports nothing. That is the safe direction: it drops reports
/// rather than attaching one package's manifest to another package's build.
fn local_package<'a>(cx: &LateContext<'_>, metadata: &'a Metadata) -> Option<&'a Package> {
    let local_name = cx.tcx.crate_name(LOCAL_CRATE);
    metadata.workspace_packages().into_iter().find(|package| {
        // A manifest name keeps its dashes; a crate name is a namespace, so cargo
        // has already turned those into underscores.
        package
            .name
            .as_bytes()
            .iter()
            .map(|b| if b == &b'-' { &b'_' } else { b })
            .eq(local_name.as_str().as_bytes())
    })
}

/// How to describe an edge that may carry several kinds at once.
///
/// One package can be reached as a normal dependency on one platform and a
/// build dependency on another; the strongest reach is the one worth naming.
fn edge_kind(dep: &NodeDep) -> DependencyKind {
    dep.dep_kinds
        .iter()
        .map(|info| info.kind)
        .min_by_key(|kind| match kind {
            DependencyKind::Normal => 0,
            DependencyKind::Build => 1,
            DependencyKind::Development => 2,
            _ => 3,
        })
        // `dep_kinds` is empty in metadata written before cargo 1.41. An edge
        // with no recorded kind is an ordinary dependency.
        .unwrap_or(DependencyKind::Normal)
}

fn kind_word(kind: DependencyKind) -> &'static str {
    match kind {
        DependencyKind::Development => "dev-dependency",
        DependencyKind::Build => "build-dependency",
        _ => "dependency",
    }
}

#[cfg(test)]
mod tests_for_source_outside_tree {
    use super::source_outside_tree;
    use cargo_metadata::camino::Utf8Path;

    const ROOT: &str = "/work/app";
    const CRATES_IO: &str = "registry+https://github.com/rust-lang/crates.io-index";

    /// The reported source of a package, given what `cargo metadata` says about
    /// it. Every input below is a value observed in real metadata output.
    fn reported(source: Option<&str>, manifest_path: &str) -> Option<String> {
        source_outside_tree(source, Utf8Path::new(manifest_path), Utf8Path::new(ROOT)).map(ToOwned::to_owned)
    }

    #[test]
    fn a_registry_package_is_outside_the_tree() {
        assert_eq!(
            reported(
                Some(CRATES_IO),
                "/home/u/.cargo/registry/src/index.crates.io/itoa-1.0.11/Cargo.toml"
            ),
            Some(CRATES_IO.to_owned()),
        );
    }

    #[test]
    fn a_sparse_registry_package_is_outside_the_tree() {
        assert!(
            reported(
                Some("sparse+https://index.crates.io/"),
                "/home/u/.cargo/registry/src/x/Cargo.toml"
            )
            .is_some()
        );
    }

    #[test]
    fn a_git_package_is_outside_the_tree() {
        assert!(
            reported(
                Some("git+https://github.com/rust-lang/log?branch=master"),
                "/home/u/.cargo/git/checkouts/log-1a2b/3c4d/Cargo.toml",
            )
            .is_some()
        );
    }

    #[test]
    fn a_path_dependency_has_no_source_at_all() {
        assert_eq!(reported(None, "/work/app/vendored/regex-ish/Cargo.toml"), None);
        // Including one outside the workspace it is used from, and one that
        // carries a `version` alongside its `path`.
        assert_eq!(reported(None, "/work/outside/Cargo.toml"), None);
    }

    #[test]
    fn a_workspace_member_has_no_source_at_all() {
        assert_eq!(reported(None, "/work/app/libinner/Cargo.toml"), None);
    }

    #[test]
    fn a_patched_dependency_resolves_to_the_path_it_was_patched_with() {
        // `[patch.crates-io] itoa = { path = "vendor/itoa" }`: the *declared*
        // dependency still names the registry, but the package that satisfies it
        // is the local one, and that is what this pass reads.
        assert_eq!(reported(None, "/work/app/vendor/itoa/Cargo.toml"), None);
    }

    #[test]
    fn a_vendored_tree_keeps_the_replaced_registry_id_and_is_still_in_the_tree() {
        assert_eq!(reported(Some(CRATES_IO), "/work/app/vendor/itoa/Cargo.toml"), None);
    }

    #[test]
    fn an_unrecognised_source_id_is_not_reported() {
        assert_eq!(
            reported(Some("dir+file:///opt/vendor"), "/opt/vendor/itoa/Cargo.toml"),
            None
        );
    }

    #[test]
    fn a_prefix_of_the_workspace_root_is_not_inside_it() {
        // `starts_with` is compared by path component, so a sibling directory
        // whose name merely begins with the root's name stays outside.
        assert!(reported(Some(CRATES_IO), "/work/app-fork/itoa/Cargo.toml").is_some());
    }
}
