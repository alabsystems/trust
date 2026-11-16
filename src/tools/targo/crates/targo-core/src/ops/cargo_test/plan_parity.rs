//! Trust: holds a test plan's one unit graph to the graphs its requests
//! build alone.
//!
//! A plan run builds every request in one graph (`plan_graph`). What makes
//! that sound is that each request gets exactly the units its own
//! `targo test -p ..` command gets: its own dependency resolve, its own
//! features, its own shared subgraph. `--unit-graph-parity` checks it on the
//! tree at hand and builds nothing: the plan's graph must equal the union of
//! the graphs the requests' standalone commands make, unit for unit and edge
//! for edge, with the same roots. A feature that leaks from one request into
//! another, or a unit only the union has, is a difference here and never a
//! test binary that quietly tested another build.
//!
//! The standalone graph of a request is made by the ordinary, plan-free
//! route of this same invocation (`create_bcx` without a plan, with the
//! request's packages, features and targets), so the two sides share one
//! workspace, lockfile, configuration and compiler, and units of the two are
//! compared as the units they are, with everything a unit carries.

use std::collections::{BTreeMap, BTreeSet};

use crate::compiler::UnitInterner;
use crate::ops::{self, CompileOptions};
use crate::util::CargoResult;
use crate::workspace::PackageIdSpecQuery as _;
use crate::workspace::Workspace;

/// A unit graph reduced to what is compared: each unit with its dependency
/// edges, sorted, and the roots.
pub(super) struct Shape<U, E> {
    pub units: BTreeMap<U, Vec<E>>,
    pub roots: Vec<U>,
}

/// At most this many differences are named; the count says how many more.
const NAMED: usize = 12;

/// Every way `plan` differs from the union of `alone` (each a request id
/// and its standalone graph), each as one line.
pub(super) fn differences<U: Ord + Clone, E: Ord>(
    plan: &Shape<U, E>,
    alone: &[(String, Shape<U, E>)],
    name: impl Fn(&U) -> String,
) -> Vec<String> {
    let mut found = Vec::new();
    let plan_roots = plan.roots.iter().collect::<BTreeSet<_>>();
    if plan_roots.len() != plan.roots.len() {
        found.push(format!(
            "the plan's graph lists {} roots, {} of them distinct",
            plan.roots.len(),
            plan_roots.len()
        ));
    }
    let mut union_units = BTreeSet::new();
    let mut union_roots = BTreeSet::new();
    for (id, graph) in alone {
        for (unit, edges) in &graph.units {
            union_units.insert(unit);
            match plan.units.get(unit) {
                None => found.push(format!(
                    "request `{id}` alone builds {}, and the plan does not",
                    name(unit)
                )),
                Some(planned) if planned != edges => found.push(format!(
                    "request `{id}` alone builds {} on other dependencies than the plan does",
                    name(unit)
                )),
                Some(_) => {}
            }
        }
        for root in &graph.roots {
            union_roots.insert(root);
            if !plan_roots.contains(root) {
                found.push(format!(
                    "request `{id}` alone tests {}, and the plan does not",
                    name(root)
                ));
            }
        }
    }
    for unit in plan.units.keys() {
        if !union_units.contains(unit) {
            found.push(format!(
                "the plan builds {}, and no request alone does",
                name(unit)
            ));
        }
    }
    for root in &plan_roots {
        if !union_roots.contains(*root) {
            found.push(format!(
                "the plan tests {}, and no request alone does",
                name(root)
            ));
        }
    }
    found
}

/// Checks the plan bound to `options` (`plan::select`) against its requests'
/// standalone graphs. `Ok` is the parity itself; an error names the
/// differences.
pub fn check(ws: &Workspace<'_>, options: &CompileOptions) -> CargoResult<()> {
    let Some(plan) = options.build_config.test_plan.clone() else {
        anyhow::bail!("--unit-graph-parity compares a test plan's graph; it needs --plan");
    };
    let interner = UnitInterner::new();
    let shape = |options: &CompileOptions| -> CargoResult<_> {
        let bcx = ops::create_bcx(ws, options, &interner, None)?;
        let units = bcx
            .unit_graph
            .iter()
            .map(|(unit, edges)| {
                // Everything an edge gives the compiler. `unit_for` is how
                // the edge was reached while the graph was being built and
                // is not read after (`UnitDep::unit_for`); two requests
                // reach one unit by different routes.
                let mut edges = edges
                    .iter()
                    .map(|edge| {
                        (
                            edge.unit.clone(),
                            edge.extern_crate_name,
                            edge.dep_name,
                            edge.public,
                            edge.noprelude,
                            edge.nounused,
                        )
                    })
                    .collect::<Vec<_>>();
                edges.sort();
                (unit.clone(), edges)
            })
            .collect::<BTreeMap<_, _>>();
        Ok(Shape {
            units,
            roots: bcx.roots.clone(),
        })
    };
    let planned = shape(options)?;
    let name = |unit: &crate::compiler::Unit| {
        format!(
            "{} of `{}` ({:?}, features [{}])",
            unit.target.description_named(),
            unit.pkg.package_id(),
            unit.mode,
            unit.features
                .iter()
                .map(|feature| feature.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        )
    };
    let mut alone = Vec::new();
    let mut found = Vec::new();
    for request in &plan.requests {
        let mut standalone = options.clone();
        standalone.build_config.test_plan = None;
        standalone.spec = request.packages.clone();
        standalone.cli_features = request.cli_features.clone();
        standalone.filter = request.filter.clone();
        let graph = shape(&standalone)?;
        // A standalone graph is its request's own: it tests the request's
        // packages and nothing else. One that tests another request's
        // package was made with the plan still bound, and comparing the
        // plan with itself would find no difference whatever it held.
        let specs = request.packages.to_package_id_specs(ws)?;
        for root in &graph.roots {
            if !specs.iter().any(|spec| spec.matches(root.pkg.package_id())) {
                found.push(format!(
                    "request `{}` alone tests {}, which is not one of its own packages",
                    request.id,
                    name(root)
                ));
            }
        }
        alone.push((request.id.clone(), graph));
    }
    found.extend(differences(&planned, &alone, name));
    let path = plan.path.display();
    if !found.is_empty() {
        let more = found.len().saturating_sub(NAMED);
        let mut named = found.into_iter().take(NAMED).collect::<Vec<_>>();
        if more != 0 {
            named.push(format!("and {more} more"));
        }
        anyhow::bail!(
            "test plan `{path}`: its unit graph is not the union of its requests' standalone \
             graphs, so a plan run would not test what each request's own command tests:\n  {}",
            named.join("\n  ")
        );
    }
    ws.gctx().shell().status(
        "Checked",
        format!(
            "test plan `{path}`: its {} units and {} roots are those of its {} requests' \
             standalone graphs",
            planned.units.len(),
            planned.roots.len(),
            alone.len()
        ),
    )?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn graph(
        units: &[(&'static str, &[&'static str])],
        roots: &[&'static str],
    ) -> Shape<&'static str, &'static str> {
        Shape {
            units: units
                .iter()
                .map(|(unit, edges)| (*unit, edges.to_vec()))
                .collect(),
            roots: roots.to_vec(),
        }
    }

    fn found(
        plan: &Shape<&'static str, &'static str>,
        alone: Vec<(&str, Shape<&'static str, &'static str>)>,
    ) -> Vec<String> {
        let alone = alone
            .into_iter()
            .map(|(id, graph)| (id.to_owned(), graph))
            .collect::<Vec<_>>();
        differences(plan, &alone, |unit| format!("`{unit}`"))
    }

    #[test]
    fn a_plan_that_is_the_union_of_its_requests_has_no_difference() {
        let plan = graph(
            &[("a-test", &["dep"]), ("b-test", &["dep"]), ("dep", &[])],
            &["a-test", "b-test"],
        );
        let a = graph(&[("a-test", &["dep"]), ("dep", &[])], &["a-test"]);
        let b = graph(&[("b-test", &["dep"]), ("dep", &[])], &["b-test"]);
        assert_eq!(found(&plan, vec![("a", a), ("b", b)]), Vec::<String>::new());
    }

    #[test]
    fn each_side_is_held_to_the_other() {
        let a = || graph(&[("a-test", &["dep"]), ("dep", &[])], &["a-test"]);
        // A unit only the union has: one request's features reached another.
        let wider = graph(
            &[("a-test", &["dep"]), ("dep", &[]), ("dep+feature", &[])],
            &["a-test"],
        );
        assert_eq!(
            found(&wider, vec![("a", a())]),
            ["the plan builds `dep+feature`, and no request alone does"]
        );
        // A unit a request builds alone and the plan lost.
        let narrower = graph(&[("a-test", &["dep"])], &["a-test"]);
        assert_eq!(
            found(&narrower, vec![("a", a())]),
            ["request `a` alone builds `dep`, and the plan does not"]
        );
        // The same unit on other edges.
        let rewired = graph(&[("a-test", &[]), ("dep", &[])], &["a-test"]);
        assert_eq!(
            found(&rewired, vec![("a", a())]),
            ["request `a` alone builds `a-test` on other dependencies than the plan does"]
        );
        // Roots: a test the plan would not run, one only the plan runs, and
        // one it would run twice.
        let unrooted = graph(&[("a-test", &["dep"]), ("dep", &[])], &[]);
        assert_eq!(
            found(&unrooted, vec![("a", a())]),
            ["request `a` alone tests `a-test`, and the plan does not"]
        );
        let extra = graph(&[("a-test", &["dep"]), ("dep", &[])], &["a-test", "dep"]);
        assert_eq!(
            found(&extra, vec![("a", a())]),
            ["the plan tests `dep`, and no request alone does"]
        );
        let twice = graph(&[("a-test", &["dep"]), ("dep", &[])], &["a-test", "a-test"]);
        assert_eq!(
            found(&twice, vec![("a", a())]),
            ["the plan's graph lists 2 roots, 1 of them distinct"]
        );
    }
}
