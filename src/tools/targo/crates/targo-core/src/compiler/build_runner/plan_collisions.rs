//! Trust: under `targo test --plan`, one target built two ways into one file
//! is an error.
//!
//! A bin is linked to `<profile>/<name>` whatever its features, and
//! `CARGO_BIN_EXE_<name>` names that path. Two requests that build one bin
//! under different features, or against different dependency features, both
//! link there: the file is whichever was linked last, and each request's
//! integration tests run it. Upstream warns ("output filename collision")
//! and builds on; a plan's build is a gate, so it stops, naming the requests.
//!
//! Collisions between different targets are left to upstream's warning: a
//! standalone command has them too, and no plan request causes them.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use super::BuildRunner;
use crate::compiler::Unit;
use crate::ops::cargo_test::plan::ResolvedPlan;
use crate::util::CargoResult;
use crate::util::data_structures::{HashMap, HashSet};

/// Refuses a plan whose graph holds two units of one package's target with
/// an output, link or export path in common. Does nothing without a plan.
pub(super) fn refuse(runner: &BuildRunner<'_, '_>) -> CargoResult<()> {
    let bcx = runner.bcx;
    let Some(plan) = bcx.build_config.test_plan.as_deref() else {
        return Ok(());
    };
    let mut units = bcx
        .unit_graph
        .keys()
        .filter(|unit| !unit.mode.is_run_custom_build())
        .collect::<Vec<_>>();
    // The same pair is named on every run.
    units.sort_unstable();
    let mut owner: HashMap<PathBuf, &Unit> = HashMap::default();
    for unit in units {
        for output in runner.outputs(unit)?.iter() {
            let paths = [
                Some(&output.path),
                output.hardlink.as_ref(),
                output.export_path.as_ref(),
            ];
            for path in paths.into_iter().flatten() {
                let Some(other) = owner.insert(path.clone(), unit) else {
                    continue;
                };
                if same_target(other, unit) && other != unit {
                    anyhow::bail!(collision(runner, plan, other, unit, path));
                }
            }
        }
    }
    Ok(())
}

fn same_target(left: &Unit, right: &Unit) -> bool {
    left.pkg.package_id() == right.pkg.package_id() && left.target == right.target
}

fn collision(
    runner: &BuildRunner<'_, '_>,
    plan: &ResolvedPlan,
    first: &Unit,
    second: &Unit,
    path: &Path,
) -> String {
    let side = |unit: &Unit| {
        let requests = requests_reaching(runner, plan, unit);
        let features = unit
            .features
            .iter()
            .map(|feature| feature.as_str())
            .collect::<Vec<_>>();
        let (noun, verb) = if requests.len() == 1 {
            ("request", "builds")
        } else {
            ("requests", "build")
        };
        format!(
            "{noun} {} {verb} it with features [{}]",
            requests
                .iter()
                .map(|id| format!("`{id}`"))
                .collect::<Vec<_>>()
                .join(", "),
            features.join(", "),
        )
    };
    format!(
        "test plan `{}` builds {} of package `{}` two ways into one file, `{}`\n\
         {}\n\
         {}\n\
         the two builds differ in the target's features or in the features of its \
         dependencies; a test that runs the file would get whichever was linked last",
        plan.path.display(),
        first.target.description_named(),
        first.pkg.name(),
        path.display(),
        side(first),
        side(second),
    )
}

/// The ids of the requests one of whose roots depends on `unit`, in plan
/// order. Only computed for the refusal.
fn requests_reaching<'plan>(
    runner: &BuildRunner<'_, '_>,
    plan: &'plan ResolvedPlan,
    unit: &Unit,
) -> Vec<&'plan str> {
    let bcx = runner.bcx;
    let mut reaching = BTreeSet::new();
    for (root, requests) in &bcx.trust_root_requests {
        if requests.iter().all(|request| reaching.contains(request)) {
            continue;
        }
        let mut seen: HashSet<&Unit> = HashSet::default();
        let mut stack = vec![root];
        let mut found = false;
        while let Some(next) = stack.pop() {
            if next == unit {
                found = true;
                break;
            }
            if seen.insert(next) {
                stack.extend(bcx.unit_graph[next].iter().map(|dep| &dep.unit));
            }
        }
        if found {
            reaching.extend(requests.iter().copied());
        }
    }
    reaching
        .into_iter()
        .map(|request| plan.requests[request].id.as_str())
        .collect()
}
