//! Trust: the unit graph of `targo test --plan`.
//!
//! Each request is resolved exactly as its standalone `targo test` command
//! resolves: its own dependency resolve, its own feature resolve, its own
//! roots, and its own pass through `rebuild_unit_graph_shared`. The graph
//! built is the union of those subgraphs.
//!
//! Neither step may be shared between requests:
//!
//! * A dependency resolve over the union of the requests' packages carries
//!   every selected member's dev-dependency edges, and the feature resolver
//!   walks them all. A request would get features that only another member's
//!   dev-dependencies turn on.
//! * Before sharing, a unit's identity has no `dep_hash`. Two requests that
//!   reach one crate with different dependency features would give it two
//!   dependency lists under one key, and a union taken there keeps one.
//!
//! After sharing, a unit's identity includes the hash of its dependencies, so
//! a unit two requests both produce has one list of dependency units. The
//! union checks that (`same_edges`) instead of assuming it.

use super::rebuild_unit_graph_shared;
use super::unit_generator::UnitGenerator;
use crate::compiler::unit_dependencies::build_unit_dependencies;
use crate::compiler::unit_graph::{UnitDep, UnitGraph};
use crate::compiler::{BuildConfig, CompileKind, DepKindSet, RustcTargetData};
use crate::compiler::{Unit, UnitInterner, UserIntent};
use crate::context::FeatureUnification;
use crate::ops;
use crate::ops::cargo_test::plan::{PlanRequest, ResolvedPlan};
use crate::ops::resolve::WorkspaceResolve;
use crate::resolver::{ForceAllTargets, HasDevUnits};
use crate::util::CargoResult;
use crate::util::data_structures::HashMap;
use crate::workspace::profiles::Profiles;
use crate::workspace::{PackageSet, Workspace};
use anyhow::Context as _;

/// The union of a plan's request subgraphs.
pub(super) struct PlanGraph<'gctx> {
    /// Every request's roots, each once, in request order.
    pub roots: Vec<Unit>,
    pub graph: UnitGraph,
    /// The requests (indices into `ResolvedPlan::requests`, which `--request`
    /// has already narrowed) that selected a root.
    pub root_requests: HashMap<Unit, Vec<usize>>,
    /// Each request's packages; a unit's package is in its request's set.
    pub packages: Vec<PackageSet<'gctx>>,
    pub selected_dep_kinds: DepKindSet,
}

pub(super) fn build<'gctx>(
    ws: &Workspace<'gctx>,
    plan: &ResolvedPlan,
    build_config: &BuildConfig,
    target_data: &mut RustcTargetData<'gctx>,
    profiles: &Profiles,
    interner: &UnitInterner,
    explicit_host_kind: CompileKind,
) -> CargoResult<PlanGraph<'gctx>> {
    let gctx = ws.gctx();
    anyhow::ensure!(
        matches!(build_config.intent, UserIntent::Test),
        "a test plan is only built by `targo test`"
    );
    // The scope under which a request equals its standalone command: features
    // unify over the request's own packages and nothing else.
    anyhow::ensure!(
        matches!(
            ws.resolve_feature_unification(),
            FeatureUnification::Selected
        ),
        "a test plan requires `resolver.feature-unification = \"selected\"`"
    );
    anyhow::ensure!(
        gctx.cli_unstable().build_std.is_none(),
        "a test plan does not support -Zbuild-std"
    );
    let to_host = build_config
        .requested_kinds
        .iter()
        .any(CompileKind::is_host)
        .then_some(explicit_host_kind);

    let mut planned = PlanGraph {
        roots: Vec::new(),
        graph: UnitGraph::default(),
        root_requests: HashMap::default(),
        packages: Vec::new(),
        selected_dep_kinds: DepKindSet::default(),
    };
    // The first request that produced each unit, for the refusal below.
    let mut first_request: HashMap<Unit, usize> = HashMap::default();

    for (index, request) in plan.requests.iter().enumerate() {
        // A plan has many requests, several on one package: an error from
        // any step below is useless without the request it came from.
        let (roots, graph, pkg_set) = request_graph(
            ws,
            request,
            build_config,
            target_data,
            profiles,
            interner,
            explicit_host_kind,
            to_host,
            &mut planned.selected_dep_kinds,
        )
        .with_context(|| {
            format!(
                "test plan `{}`, request `{}`",
                plan.path.display(),
                request.id
            )
        })?;
        for (unit, deps) in graph {
            match planned.graph.get(&unit) {
                None => {
                    first_request.insert(unit.clone(), index);
                    planned.graph.insert(unit, deps);
                }
                // The collision guard: equal units hash equal dependencies.
                Some(present) => anyhow::ensure!(
                    same_edges(present, &deps),
                    "requests `{}` and `{}` give {} `{}` ({:?}) different dependencies \
                     under one unit identity",
                    plan.requests[first_request[&unit]].id,
                    request.id,
                    unit.target.description_named(),
                    unit.pkg.package_id(),
                    unit.mode,
                ),
            }
        }
        for root in roots {
            let requests = planned.root_requests.entry(root.clone()).or_default();
            if requests.is_empty() {
                planned.roots.push(root);
            }
            if !requests.contains(&index) {
                requests.push(index);
            }
        }
        planned.packages.push(pkg_set);
    }
    Ok(planned)
}

/// One request's roots and shared unit graph, resolved as its standalone
/// command resolves them, with the package set its units come from.
fn request_graph<'gctx>(
    ws: &Workspace<'gctx>,
    request: &PlanRequest,
    build_config: &BuildConfig,
    target_data: &mut RustcTargetData<'gctx>,
    profiles: &Profiles,
    interner: &UnitInterner,
    explicit_host_kind: CompileKind,
    to_host: Option<CompileKind>,
    selected_dep_kinds: &mut DepKindSet,
) -> CargoResult<(Vec<Unit>, UnitGraph, PackageSet<'gctx>)> {
    let specs = request.packages.to_package_id_specs(ws)?;
    let has_dev_units = if request.filter.need_dev_deps(build_config.intent) {
        HasDevUnits::Yes
    } else {
        HasDevUnits::No
    };
    let WorkspaceResolve {
        pkg_set,
        workspace_resolve,
        targeted_resolve: resolve,
        specs_and_features,
    } = ops::resolve_ws_with_opts(
        ws,
        target_data,
        &build_config.requested_kinds,
        &request.cli_features,
        &specs,
        has_dev_units,
        ForceAllTargets::No,
        false,
    )?;
    let [resolved] = specs_and_features.as_slice() else {
        anyhow::bail!(
            "its features resolved {} times; a plan request has one feature resolve",
            specs_and_features.len()
        );
    };

    let mut packages = pkg_set.get_many(resolve.specs_to_ids(&specs)?)?;
    packages.sort_by_key(|package| package.package_id());
    let generator = UnitGenerator {
        ws,
        packages: &packages,
        spec: &request.packages,
        target_data,
        filter: &request.filter,
        requested_kinds: &build_config.requested_kinds,
        explicit_host_kind,
        intent: build_config.intent,
        resolve: &resolve,
        workspace_resolve: &workspace_resolve,
        resolved_features: &resolved.resolved_features,
        package_set: &pkg_set,
        profiles,
        interner,
        has_dev_units,
    };
    let (roots, dep_kinds) = generator.generate_root_units()?;
    selected_dep_kinds.build |= dep_kinds.build;
    selected_dep_kinds.normal |= dep_kinds.normal;
    selected_dep_kinds.dev |= dep_kinds.dev;

    let graph = build_unit_dependencies(
        ws,
        &pkg_set,
        &resolve,
        &resolved.resolved_features,
        None,
        &roots,
        &[],
        &Default::default(),
        build_config.intent,
        target_data,
        profiles,
        interner,
    )?;
    let (roots, _scrape_units, graph) = rebuild_unit_graph_shared(
        interner,
        graph,
        &roots,
        &[],
        to_host,
        build_config.compile_time_deps_only,
    );
    Ok((roots, graph, pkg_set))
}

/// Whether two dependency lists of one shared unit are the same build input:
/// the same units in the same order under the same names and flags.
///
/// `UnitDep::unit_for` is left out. It says how an edge was reached while the
/// graph was built and must not be read afterwards; a crate reached as a host
/// dependency by one request and as a normal one by another has edges that
/// differ only there. `rebuild_unit_graph_shared` keeps the first such list
/// within one request. `manifest_deps` is bookkeeping for the same reason.
fn same_edges(left: &[UnitDep], right: &[UnitDep]) -> bool {
    left.len() == right.len()
        && left.iter().zip(right).all(|(left, right)| {
            left.unit == right.unit
                && left.extern_crate_name == right.extern_crate_name
                && left.dep_name == right.dep_name
                && left.public == right.public
                && left.noprelude == right.noprelude
                && left.nounused == right.nounused
        })
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;
    use std::rc::Rc;

    use cargo_util_terminal::Shell;

    use super::*;
    use crate::compiler::CompileMode;
    use crate::compiler::unit_dependencies::IsArtifact;
    use crate::util::GlobalContext;
    use crate::util::Unhashed;
    use crate::util::interning::InternedString;
    use crate::workspace::profiles::{Profile, UnitFor};

    /// The union's guard, on the two shapes that matter: lists that differ
    /// only in how an edge was reached are one build input (the real lane's
    /// `quote` build script, reached through the host by one request and not
    /// by another), and lists that differ in anything a compiler invocation
    /// reads are not.
    #[test]
    fn edges_are_the_same_up_to_how_they_were_reached() {
        let temporary = tempfile::tempdir().unwrap();
        std::fs::create_dir(temporary.path().join("tests")).unwrap();
        for target in ["one", "two"] {
            std::fs::write(
                temporary.path().join("tests").join(format!("{target}.rs")),
                "",
            )
            .unwrap();
        }
        let manifest = temporary.path().join("Cargo.toml");
        std::fs::write(
            &manifest,
            "[package]\nname='edges-fixture'\nversion='0.1.0'\nedition='2024'\n",
        )
        .unwrap();
        let mut gctx = GlobalContext::new(
            Shell::new(),
            temporary.path().into(),
            temporary.path().join("home"),
        );
        gctx.set_search_stop_path(temporary.path());
        gctx.set_env(Default::default());
        gctx.configure(0, false, None, false, false, true, &None, &[], &[])
            .unwrap();
        let workspace = Workspace::new(&manifest, &gctx).unwrap();
        let package = workspace.current().unwrap();
        let interner = UnitInterner::new();
        let unit = |name: &str| {
            let target = package
                .targets()
                .iter()
                .find(|target| target.name() == name)
                .unwrap();
            interner.intern(
                package,
                target,
                Profile::default(),
                CompileKind::Host,
                CompileMode::Test,
                vec![],
                Rc::from(Vec::<String>::new()),
                Rc::from(Vec::<String>::new()),
                Rc::new(BTreeMap::new()),
                false,
                0,
                IsArtifact::No,
                None,
                false,
            )
        };
        let edge = || UnitDep {
            unit: unit("one"),
            unit_for: UnitFor::new_normal(CompileKind::Host),
            extern_crate_name: InternedString::new("one"),
            dep_name: None,
            public: false,
            noprelude: false,
            nounused: false,
            manifest_deps: Unhashed(None),
        };
        let with = |change: fn(&mut UnitDep)| {
            let mut changed = edge();
            change(&mut changed);
            vec![changed]
        };

        assert!(same_edges(&[edge()], &[edge()]));
        // Reached through the host, with host features: the same build input.
        let through_host = with(|edge| edge.unit_for = UnitFor::new_host(true, CompileKind::Host));
        assert_ne!(
            through_host,
            vec![edge()],
            "the lists are not equal as values"
        );
        assert!(same_edges(&[edge()], &through_host));
        let bookkeeping = with(|edge| edge.manifest_deps = Unhashed(Some(Vec::new())));
        assert!(same_edges(&[edge()], &bookkeeping));

        // Everything a compiler invocation reads tells two lists apart.
        let other_unit = vec![UnitDep {
            unit: unit("two"),
            ..edge()
        }];
        assert!(!same_edges(&[edge()], &other_unit));
        for changed in [
            with(|edge| edge.extern_crate_name = InternedString::new("renamed")),
            with(|edge| edge.dep_name = Some(InternedString::new("one"))),
            with(|edge| edge.public = true),
            with(|edge| edge.noprelude = true),
            with(|edge| edge.nounused = true),
        ] {
            assert!(!same_edges(&[edge()], &changed), "{changed:?}");
        }
        // Length and order are part of the input.
        assert!(!same_edges(&[edge()], &[edge(), edge()]));
        assert!(!same_edges(&[edge()], &[]));
        let pair = [edge(), other_unit[0].clone()];
        let swapped = [other_unit[0].clone(), edge()];
        assert!(same_edges(&pair, &pair));
        assert!(!same_edges(&pair, &swapped));
    }
}
