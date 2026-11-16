//! Shared resolved inputs for ordinary and independent native command planning.
//! This view owns no runner, directory lease, CPU bank or execution permission.
use super::build_runner::{CompilationFiles, OutputFile};
use super::layout::{Layout, LayoutPaths};
use super::lto::Lto;
use super::unit_graph::UnitDep;
use super::{BuildContext, BuildRunner, Compilation, CompileMode, FileFlavor, Unit};
use crate::util::CargoResult;
use crate::util::data_structures::{HashMap, HashSet};
use crate::workspace::PackageId;
use std::borrow::Borrow;
use std::cell::RefCell;
use std::sync::Arc;

pub(super) struct RustcCommandContext<'a, 'bcx, 'gctx, L = Layout> {
    pub bcx: &'a BuildContext<'bcx, 'gctx>,
    pub compilation: &'a Compilation<'gctx>,
    pub files: Option<&'a CompilationFiles<'bcx, 'gctx, L>>,
    pub lto: &'a HashMap<Unit, Lto>,
    pub primary_packages: &'a HashSet<PackageId>,
    pub extern_selections: Option<&'a RefCell<Vec<ExternSelection>>>,
}
pub(super) struct ExternSelection {
    pub unit: Unit,
    pub outputs: Arc<Vec<OutputFile>>,
    pub index: usize,
}
impl<'a, 'bcx, 'gctx: 'bcx> RustcCommandContext<'a, 'bcx, 'gctx> {
    pub fn for_runner(runner: &'a BuildRunner<'bcx, 'gctx>) -> Self {
        Self {
            bcx: runner.bcx,
            compilation: &runner.compilation,
            files: runner.files.as_ref(),
            lto: &runner.lto,
            primary_packages: &runner.primary_packages,
            extern_selections: None,
        }
    }
}
impl<'a, 'bcx, 'gctx: 'bcx, L: Borrow<LayoutPaths>> RustcCommandContext<'a, 'bcx, 'gctx, L> {
    pub fn files(&self) -> &CompilationFiles<'bcx, 'gctx, L> {
        self.files.expect("compile files have not been prepared")
    }
    pub fn unit_deps(&self, unit: &Unit) -> &[UnitDep] {
        &self.bcx.unit_graph[unit]
    }
    pub fn outputs(&self, unit: &Unit) -> CargoResult<Arc<Vec<OutputFile>>> {
        self.files().outputs(unit, self.bcx)
    }
    pub fn is_primary_package(&self, unit: &Unit) -> bool {
        self.primary_packages.contains(&unit.pkg.package_id())
    }
    pub fn only_requires_rmeta(&self, parent: &Unit, dep: &Unit) -> bool {
        only_requires_rmeta(parent, dep)
    }
    pub fn record_extern(
        &self,
        unit: &Unit,
        outputs: &Arc<Vec<OutputFile>>,
        index: usize,
    ) -> CargoResult<()> {
        if let Some(selections) = self.extern_selections {
            selections
                .try_borrow_mut()
                .map_err(|_| anyhow::anyhow!("recursive independent extern capture"))?
                .push(ExternSelection {
                    unit: unit.clone(),
                    outputs: outputs.clone(),
                    index,
                });
        }
        Ok(())
    }
    pub fn sbom_output_files(&self, unit: &Unit) -> CargoResult<Vec<std::path::PathBuf>> {
        Ok(self
            .outputs(unit)?
            .iter()
            .filter(|output| output.flavor == FileFlavor::Sbom)
            .map(|output| output.path.clone())
            .collect())
    }
}

pub(super) fn only_requires_rmeta(parent: &Unit, dep: &Unit) -> bool {
    !parent.requires_upstream_objects()
        && parent.mode == CompileMode::Build
        && !dep.requires_upstream_objects()
        && dep.mode == CompileMode::Build
}
