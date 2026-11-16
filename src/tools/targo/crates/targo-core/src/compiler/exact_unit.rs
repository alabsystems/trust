// Trust: persistent evidence must never hash Unit's invocation-local Rc address.

use super::{BuildContext, BuildRunner, CompileKind, Unit, exact_unit_compile_target_spec_sha256};
use crate::util::CargoResult;
use crate::util::data_structures::{HashMap, HashSet};
use anyhow::Context as _;
use std::collections::BTreeMap;
use std::sync::Arc;

/// One immutable resolved graph, shared by inventory, dispatch and artifact capture.
pub(super) struct Graph {
    units: HashMap<Unit, Arc<Captured>>,
}

/// Captured dependencies and target bytes remain bound through artifact publication.
pub(super) struct Captured {
    pub digest: String,
    specs: BTreeMap<CompileKind, String>,
}

impl Captured {
    pub fn require_spec(&self, kind: CompileKind, expected: Option<&str>) -> CargoResult<()> {
        anyhow::ensure!(
            self.specs.get(&kind).map(String::as_str) == expected,
            "target specification differs from captured exact unit graph"
        );
        Ok(())
    }
    pub fn require_current(&self) -> CargoResult<()> {
        for (&kind, digest) in &self.specs {
            super::ensure_exact_unit_compile_target_spec_unchanged(kind, Some(digest))?;
        }
        Ok(())
    }
}

#[derive(serde::Serialize, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct Dependency {
    unit_sha256: String,
    extern_crate_name: String,
    dep_name: Option<String>,
    public: bool,
    noprelude: bool,
    nounused: bool,
}

pub(super) fn capture(runner: &BuildRunner<'_, '_>, unit: &Unit) -> CargoResult<Arc<Captured>> {
    let graph = runner
        .exact_unit_graph
        .get_or_init(|| Graph::new(runner.bcx).map_err(|error| format!("{error:#}")));
    let graph = graph.as_ref().map_err(|error| anyhow::anyhow!("{error}"))?;
    graph.capture(unit)
}

impl Graph {
    /// Resolving equality data creates no runner, CPU bank, GNU server, output
    /// lock or execution grant. The caller must own any required input guards.
    pub(super) fn new(bcx: &BuildContext<'_, '_>) -> CargoResult<Self> {
        let mut units = HashMap::default();
        let mut visiting = HashSet::default();
        let mut specs = BTreeMap::new();
        for unit in bcx.unit_graph.keys() {
            Self::visit(bcx, unit, &mut units, &mut visiting, &mut specs)?;
        }
        Ok(Self { units })
    }

    pub(super) fn capture(&self, unit: &Unit) -> CargoResult<Arc<Captured>> {
        let captured = self
            .units
            .get(unit)
            .context("exact unit missing from resolved graph")?;
        // This read must not be served by the immutable digest snapshot.
        captured.require_current()?;
        Ok(Arc::clone(captured))
    }

    fn visit(
        bcx: &BuildContext<'_, '_>,
        unit: &Unit,
        units: &mut HashMap<Unit, Arc<Captured>>,
        visiting: &mut HashSet<Unit>,
        specs: &mut BTreeMap<CompileKind, Option<String>>,
    ) -> CargoResult<Arc<Captured>> {
        if let Some(captured) = units.get(unit) {
            return Ok(Arc::clone(captured));
        }
        anyhow::ensure!(
            visiting.insert(unit.clone()),
            "cycle in exact unit dependency graph"
        );
        let deps = bcx
            .unit_graph
            .get(unit)
            .context("dependency absent from resolved unit graph")?;
        let mut dependencies = Vec::with_capacity(deps.len());
        let mut contributing_specs = BTreeMap::new();
        for dep in deps {
            let child = Self::visit(bcx, &dep.unit, units, visiting, specs)?;
            contributing_specs.extend(child.specs.clone());
            // unit_for is graph-construction input: its resolved effects are in
            // the child's mode/kind/profile/features. manifest_deps is explicitly
            // Unhashed bookkeeping. All final executable edge semantics follow.
            dependencies.push(Dependency {
                unit_sha256: child.digest.clone(),
                extern_crate_name: dep.extern_crate_name.to_string(),
                dep_name: dep.dep_name.map(|name| name.to_string()),
                public: dep.public,
                noprelude: dep.noprelude,
                nounused: dep.nounused,
            });
        }
        // Adjacency iteration is not semantic order. Preserve every directed
        // edge and its multiplicity, sorting only their canonical value records.
        dependencies.sort();
        for kind in std::iter::once(unit.kind)
            .chain(unit.artifact_target_for_features.map(CompileKind::Target))
        {
            let digest = if let Some(digest) = specs.get(&kind) {
                digest.clone()
            } else {
                let digest = exact_unit_compile_target_spec_sha256(kind)?;
                specs.insert(kind, digest.clone());
                digest
            };
            if let Some(digest) = digest {
                contributing_specs.insert(kind, digest);
            }
        }
        let root_spec = specs.get(&unit.kind).and_then(Option::as_deref);
        let digest = super::exact_unit_identity_sha256(
            unit,
            super::scoped_unit_compile_target(bcx, unit)?,
            root_spec,
            bcx.extra_args_for(unit)
                .map(Vec::as_slice)
                .unwrap_or_default(),
            &dependencies,
            unit.artifact_target_for_features
                .and_then(|target| specs.get(&CompileKind::Target(target)))
                .and_then(Option::as_deref),
        )?;
        visiting.remove(unit);
        let captured = Arc::new(Captured {
            digest,
            specs: contributing_specs,
        });
        units.insert(unit.clone(), Arc::clone(&captured));
        Ok(captured)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_captured_dependency_target_is_rechecked_after_capture() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("dependency.json");
        std::fs::write(&path, "{}").unwrap();
        let kind = CompileKind::Target(
            super::super::CompileTarget::new(path.to_str().unwrap(), true).unwrap(),
        );
        let digest = exact_unit_compile_target_spec_sha256(kind)
            .unwrap()
            .unwrap();
        let captured = Captured {
            digest: "not-an-execution-grant".into(),
            specs: BTreeMap::from([(kind, digest)]),
        };
        captured.require_current().unwrap();
        // The node whose artifact is published may be an ordinary host node;
        // this separately captured kind belongs to an artifact dependency.
        captured.require_spec(CompileKind::Host, None).unwrap();
        std::fs::write(&path, "[]").unwrap();
        assert!(
            captured.require_current().is_err(),
            "a cached digest cannot waive changed dependency target bytes"
        );
        std::fs::write(&path, "{}").unwrap();
        captured.require_current().unwrap();
        std::fs::remove_file(&path).unwrap();
        assert!(
            captured.require_current().is_err(),
            "an unavailable dependency target is not unchanged"
        );
    }
}
