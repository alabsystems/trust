//! The ordinary complete Layout acquisition, shared with trusted preparation
//! before a produced coordinator is admitted. These own real locks, not paths.
use super::{OriginalOutputLeases, compilation_files};
use crate::compiler::{BuildConfig, CompileKind, CompileTarget, Layout};
use crate::util::{
    CargoResult,
    data_structures::{HashMap, HashSet},
};
use crate::workspace::{Workspace, profiles::Profiles};
use std::sync::Arc;

pub(super) struct PreparedLayouts {
    pub(super) host: Layout,
    pub(super) targets: HashMap<CompileTarget, Layout>,
}
impl PreparedLayouts {
    pub(super) fn acquire(
        ws: &Workspace<'_>,
        kinds: &HashSet<CompileKind>,
        dest: &str,
        artifact: bool,
        exclusive_build: bool,
        retained: Option<&Arc<OriginalOutputLeases>>,
    ) -> CargoResult<Self> {
        let mut originals = retained
            .map(|original| original.borrow_for_workspace(&ws.target_dir().into_path_unlocked()))
            .transpose()?;
        let mut layout = |target| match originals.as_mut() {
            Some(originals) => {
                Layout::from_originals(ws, target, dest, artifact, exclusive_build, originals)
            }
            None => Layout::new(ws, target, dest, artifact, exclusive_build),
        };
        let host = layout(None)?;
        let mut targets = HashMap::default();
        for kind in kinds {
            if let CompileKind::Target(target) = *kind {
                targets.insert(target, layout(Some(target))?);
            }
        }
        anyhow::ensure!(
            originals.as_ref().is_none_or(Vec::is_empty),
            "continued Layout did not consume the complete original guard population"
        );
        Ok(Self { host, targets })
    }
    /// BuildConfig and Profiles are ordinary configuration, without resolving
    /// a unit graph, constructing a runner or executing a compiler.
    pub(super) fn acquire_native(
        ws: &Workspace<'_>,
        config: &BuildConfig,
        root: &std::path::Path,
    ) -> CargoResult<Self> {
        anyhow::ensure!(
            config.requested_kinds == [CompileKind::Host]
                && !config.dry_run
                && !config.unit_graph
                && !config.force_rebuild,
            "native lock preparation requires the actual native non-forced build configuration"
        );
        let profiles = Profiles::new(ws, config.requested_profile)?;
        let dest = profiles.get_dir_name();
        let component = std::path::Path::new(dest.as_str());
        anyhow::ensure!(
            component.components().count() == 1
                && matches!(
                    component.components().next(),
                    Some(std::path::Component::Normal(_))
                ),
            "native configured profile directory is not a single ordinary component"
        );
        let target = ws.target_dir().into_path_unlocked();
        let build = ws.build_dir().into_path_unlocked();
        anyhow::ensure!(
            target == root
                && build.starts_with(root)
                && build.components().all(|part| matches!(
                    part,
                    std::path::Component::RootDir | std::path::Component::Normal(_)
                )),
            "native Layout roots escape the SAME original selected output"
        );
        let kinds = config
            .requested_kinds
            .iter()
            .copied()
            .chain(std::iter::once(CompileKind::Host))
            .collect();
        Self::acquire(
            ws,
            &kinds,
            &dest,
            compilation_files::artifact_dir_required_for(config),
            true,
            None,
        )
    }
    pub(super) fn prepare(&mut self) -> CargoResult<()> {
        self.host.prepare()?;
        for target in self.targets.values_mut() {
            target.prepare()?;
        }
        Ok(())
    }
    pub(super) fn take_compile_leases(&mut self) -> CargoResult<Vec<crate::util::FileLock>> {
        let mut guards = self.host.take_compile_leases()?;
        for target in self.targets.values_mut() {
            guards.extend(target.take_compile_leases()?);
        }
        Ok(guards)
    }
}
