//! Original runtime-context connection, below the closed staged entry. Reuse
//! this context's maintained home/environment selection, not Bootstrap flags or
//! a second Cargo config evaluator. The captured directory is physical DATA;
//! native State independently acquires and retains the real cache-lock guard.
use super::*;
use std::{io, os::unix::ffi::OsStringExt as _, time::Instant};
use trust_resource_controller::{
    bootstrap_graph::offline_preparation::Request,
    descriptors::{AdmittedDirectory, DescriptorBudget},
};

struct Selection {
    source: PathBuf,
    home: PathBuf,
    environment: cargo_util::EnvironmentInputs,
}
impl Selection {
    // Negative equality/currentness only; arbitrary success here creates no
    // source, native cache lock, resource admission or semantic Seed owner.
    fn check(&self, context: &GlobalContext) -> CargoResult<()> {
        anyhow::ensure!(
            !context.values.filled()
                && !context.credential_values.filled()
                && context.preparation_configuration.is_none(),
            "original caller-cache capture must precede configuration/credential reads"
        );
        anyhow::ensure!(
            context.search_stop_path.is_none()
                && context
                    .cli_config
                    .as_ref()
                    .is_none_or(|config| config.is_empty()),
            "original caller-cache context cannot omit ancestors or import config overrides"
        );
        anyhow::ensure!(
            context.cwd == self.source
                && context.home().as_path_unlocked() == self.home
                && context.env.matches_selected(&self.environment),
            "original caller-cache context association changed"
        );
        // EXACT maintained frontend-aware selection, including presence/empty
        // precedence and its ordinary OS-home fallback. No config bytes read.
        let os_home = || {
            context
                .env
                .get_env_os("HOME")
                .filter(|home| !home.is_empty())
                .map(PathBuf::from)
                .or_else(::home::home_dir)
        };
        anyhow::ensure!(
            homedir_with_environment(&context.cwd, &context.env, os_home).as_deref()
                == Some(self.home.as_path()),
            "actual GlobalContext home differs from its original environment"
        );
        Ok(())
    }
    fn capture(
        &self,
        context: &GlobalContext,
        budget: &Arc<DescriptorBudget>,
        end: Instant,
    ) -> CargoResult<Arc<AdmittedDirectory>> {
        self.check(context)?;
        // Existing accounted descriptor demand and SAME no-follow originals.
        // This is not a kernel-FD reservation or an acquired cache lock.
        Ok(budget.capture_directory(context.home().as_path_unlocked(), end)?)
    }
}

impl GlobalContext {
    /// Bind this original runtime's Cargo home to an already authentic staged
    /// Source owner. Source/Output Managers, finalized programs and early output
    /// custody must already exist; native137 is required before Config can read.
    /// No new runtime dispatcher/marker or full/default completion is enabled.
    ///
    /// The actual source retains the exact captured Arc before preflight/send
    /// and bookends this context throughout the same-channel exchange. Config
    /// roots/credential inputs remain separately owned; a cache-directory ACK
    /// does not relax the existing unsupported external-configuration boundary.
    pub fn attach_original_preparation_cache(
        &self,
        source: &Arc<bootstrap::engine::OriginalPreparationSource>,
        budget: &Arc<DescriptorBudget>,
    ) -> CargoResult<Request> {
        let selected = (|| {
            source.check_current()?;
            let environment = cargo_util::EnvironmentInputs::from_variables(
                source
                    .preparation_environment()?
                    .iter()
                    .map(|(key, value)| {
                        (
                            OsString::from_vec(key.clone()),
                            OsString::from_vec(value.clone()),
                        )
                    }),
            )?;
            let selection = Selection {
                source: source.original_source()?.path().into(),
                home: self.home().as_path_unlocked().into(),
                environment,
            };
            let end = source.original_deadline()?;
            let directory = selection.capture(self, budget, end)?;
            Ok::<_, anyhow::Error>((selection, directory))
        })();
        let (selection, directory) = match selected {
            Ok(original) => original,
            Err(error) => {
                // No native role was acquired by a failed capture. Preserve
                // and quarantine the SAME already retained source transaction.
                return unsafe {
                    source
                        .attach_original_preparation_cache(Err(io::Error::other(error)), || Ok(()))
                }
                .map_err(Into::into);
            }
        };
        // SAFETY: the actual opaque Source was supplied by the original runtime
        // owner, selection reused THIS GlobalContext's maintained home/env/cwd,
        // and the genuine budget captured its original readonly physical tree.
        // The verifier below touches only this context and immutable DATA; it
        // must never reenter the locked Source/Graph during the handoff.
        unsafe {
            source.attach_original_preparation_cache(Ok(directory), || {
                selection.check(self).map_err(io::Error::other)
            })
        }
        .map_err(Into::into)
    }
}

#[cfg(test)]
mod tests;
