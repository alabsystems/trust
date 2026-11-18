//! Trust: the owned LLVM/LLD source-build recipe key and working-source generation:
//! the requested build evidence a source-built LLVM or LLD is reused on.

use std::ffi::OsStr;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};

use super::external_inputs::ExternalInputs;
use super::reuse_evidence::{
    CmakeGeneration, begin_cmake_miss, bounded_native_evidence, cmake_generation_matches,
    full_source_digest, observe_cmake_sources, parse_source_completion,
    recorded_llvm_dependency_key,
};
use super::{Llvm, LlvmOutput, installed_outputs};
use crate::core::builder::Builder;
use crate::core::config::TargetSelection;
use crate::utils::build_stamp::BuildStamp;
use crate::utils::helpers::t;

pub(super) fn regular_source_artifact(path: &Path) -> bool {
    fs::symlink_metadata(path).is_ok_and(|metadata| metadata.file_type().is_file())
}

// Requested build evidence, not artifact/tool contents or automatic VCS freshness.
#[derive(Clone, Debug)]
pub(super) struct SourceRecipeKey {
    pub(super) request: String,
    pub(super) dependency: String,
    pub(super) link_shared: bool,
}
pub(super) struct SelectedLlvmDependency {
    pub(super) output: LlvmOutput,
    target: TargetSelection,
    observed: Option<String>,
    external_inputs: Option<ExternalInputs>,
    failed: AtomicBool,
}
impl SelectedLlvmDependency {
    pub(super) fn observe(output: LlvmOutput, target: TargetSelection) -> Self {
        let observed = recorded_llvm_dependency_key(&output, target);
        Self { output, target, observed, external_inputs: None, failed: AtomicBool::new(false) }
    }
    fn bind_prepared(&mut self, prepared: &cmake::Prepared) {
        if !self.failed.load(Ordering::Acquire) && self.output.kind() == super::LlvmKind::External {
            self.external_inputs = ExternalInputs::from_prepared(prepared);
            self.observed = self.current_key(&self.output);
        }
    }
    fn current_key(&self, output: &LlvmOutput) -> Option<String> {
        match &self.external_inputs {
            Some(inputs) => inputs.key(output, self.target),
            None => recorded_llvm_dependency_key(output, self.target),
        }
    }
    pub(super) fn ensure_selected(&self, builder: &Builder<'_>) -> Result<(), String> {
        if self.failed.load(Ordering::Acquire) {
            return Err("selected LLVM dependency previously changed".into());
        }
        let actual = builder.ensure(Llvm { target: self.target });
        if actual.kind() != self.output.kind()
            || actual.root_dir() != self.output.root_dir()
            || actual.llvm_config() != self.output.llvm_config()
            || actual.link_shared() != self.output.link_shared()
            || self
                .observed
                .as_ref()
                .is_some_and(|before| self.current_key(&actual).as_ref() != Some(before))
        {
            self.failed.store(true, Ordering::Release);
            return Err("selected LLVM dependency changed after request preparation".into());
        }
        Ok(())
    }
    pub(super) fn unchanged(&self) -> bool {
        if self.failed.load(Ordering::Acquire) {
            return false;
        }
        self.matches_observation(self.current_key(&self.output).as_deref())
    }
    fn matches_observation(&self, current: Option<&str>) -> bool {
        let unchanged = !self.failed.load(Ordering::Acquire)
            && self.observed.as_deref().is_some_and(|before| current == Some(before));
        if !unchanged {
            self.failed.store(true, Ordering::Release);
        }
        unchanged
    }
}

#[cfg(test)]
#[path = "tests/source_recipe_dependency_tests.rs"]
mod dependency_tests;
pub(super) struct ResolvedSourceRecipe {
    pub(super) prepared: cmake::Prepared,
    pub(super) key: Option<SourceRecipeKey>,
    pub(super) postprocess_version_suffix: Option<String>,
    pub(super) dependencies: Vec<SelectedLlvmDependency>,
}
impl ResolvedSourceRecipe {
    pub(super) fn from_config(
        mut config: cmake::Config,
        suffix: Option<String>,
        mut dependencies: Vec<SelectedLlvmDependency>,
        link_shared: bool,
    ) -> Result<Self, String> {
        // No raw Config fallback: failed preparation has not established the
        // commands or cleanup namespaces that would be safe to execute.
        config.define_input_program(
            "CMAKE_MAKE_PROGRAM",
            &[OsStr::new("ninja-build"), OsStr::new("ninja")],
        );
        let prepared = config.try_prepare().map_err(|error| error.to_string())?;
        for selected in &mut dependencies {
            selected.bind_prepared(&prepared);
        }
        let key = source_recipe_key(&prepared, &dependencies, link_shared);
        Ok(Self { prepared, key, postprocess_version_suffix: suffix, dependencies })
    }
}
pub(super) fn source_recipe_key(
    prepared: &cmake::Prepared,
    dependencies: &[SelectedLlvmDependency],
    link_shared: bool,
) -> Option<SourceRecipeKey> {
    use sha2::Digest;

    use crate::utils::trust_repo_cache::{add, finish};
    let mut hash = sha2::Sha256::new();
    add(&mut hash, b"trust.bootstrap-source-cmake-request/v1");
    add(&mut hash, prepared.cache_inputs()?);
    let request = finish(hash);
    let dependency = if dependencies.is_empty() {
        "none".to_owned()
    } else {
        let mut hash = sha2::Sha256::new();
        add(&mut hash, b"trust.bootstrap-source-cmake-dependencies/v1");
        add(&mut hash, (dependencies.len() as u64).to_le_bytes());
        for selected in dependencies {
            if selected.failed.load(Ordering::Acquire) {
                return None;
            }
            add(&mut hash, selected.target.triple.as_bytes());
            add(&mut hash, selected.observed.as_ref()?.as_bytes());
        }
        finish(hash)
    };
    Some(SourceRecipeKey { request, dependency, link_shared })
}

pub(super) enum SourceRecipeResolution {
    Dry,
    UnresolvedCross,
    Unavailable(String),
    Resolved(ResolvedSourceRecipe),
}
#[derive(Clone, Copy)]
pub(super) enum SourceResolutionMode {
    Lookup,
    Build,
}

// Working bytes and requested build evidence. Automatic VCS macros retain provenance of the actual build;
// this does not identify the full CMake recipe or ThinLTO/IRSymtab algorithm.
pub(super) struct OwnSourceGeneration {
    pub(super) source: PathBuf,
    pub(super) anchor: PathBuf,
    pub(super) output: PathBuf,
    pub(super) observed: Option<String>,
}

/// A selected-build cache namespace, not portable binary identity. The fixed
/// path is part of Prepared; its derived contents deliberately are not.
pub(super) struct LlvmBuildCacheIdentity {
    pub(super) path: PathBuf,
    pub(super) bytes: Vec<u8>,
}
impl LlvmBuildCacheIdentity {
    pub(super) fn derive(
        owner: &OwnSourceGeneration,
        target: &str,
        recipe: Option<&SourceRecipeKey>,
    ) -> Self {
        use sha2::Digest;

        use crate::utils::trust_repo_cache::{add, finish};
        let value = owner
            .observed
            .as_ref()
            .zip(recipe)
            .filter(|(source, recipe)| {
                full_source_digest(source)
                    && full_source_digest(&recipe.request)
                    && (recipe.dependency == "none" || full_source_digest(&recipe.dependency))
                    && !target.is_empty()
                    && !target.contains('\n')
                    && !target.contains('\r')
            })
            .map(|(source, recipe)| {
                let mut hash = sha2::Sha256::new();
                add(&mut hash, b"trust.llvm-build-cache-namespace/v1");
                add(&mut hash, source.as_bytes());
                add(&mut hash, target.as_bytes());
                add(&mut hash, recipe.request.as_bytes());
                add(&mut hash, recipe.dependency.as_bytes());
                add(
                    &mut hash,
                    if recipe.link_shared { b"shared".as_slice() } else { b"static".as_slice() },
                );
                finish(hash)
            });
        let record = value.map_or_else(|| "unknown".to_owned(), |value| format!("known {value}"));
        Self {
            path: owner.output.join(".trust-llvm-build-id"),
            bytes: format!("trust.llvm-build-cache-namespace/v1\n{record}\n").into_bytes(),
        }
    }
    pub(super) fn write(&self) -> std::io::Result<()> {
        use std::io::Write;
        let parent = self.path.parent().unwrap();
        // begin() already established ownership; reject a replaced final root
        // or record rather than following it. No hostile concurrent-swap claim.
        if !fs::symlink_metadata(parent)?.file_type().is_dir() {
            return Err(std::io::Error::other("build identity root is not a regular directory"));
        }
        match fs::symlink_metadata(&self.path) {
            Ok(meta) if !meta.file_type().is_file() => {
                return Err(std::io::Error::other("build identity record is not a regular file"));
            }
            Err(error) if error.kind() != std::io::ErrorKind::NotFound => return Err(error),
            _ => {}
        }
        let mut temp = tempfile::NamedTempFile::new_in(parent)?;
        temp.write_all(&self.bytes)?;
        temp.as_file().sync_all()?;
        temp.persist(&self.path).map_err(|error| error.error)?;
        Ok(())
    }
    pub(super) fn matches(&self) -> bool {
        bounded_native_evidence(&self.path, 256).is_some_and(|(bytes, _)| bytes == self.bytes)
    }
}
impl OwnSourceGeneration {
    pub(super) fn observe(builder: &Builder<'_>, output: &Path) -> Self {
        let source = builder.src.join("src/llvm-project");
        let observed = if builder.config.dry_run() {
            None
        } else {
            let root = t!(crate::utils::trust_repo_cache::selected_input_namespace(output));
            t!(observe_cmake_sources(&source, &root))
        };
        Self { source, anchor: builder.out.clone(), output: output.to_owned(), observed }
    }
    pub(super) fn stamp(
        &self,
        project: &str,
        target: &str,
        recipe: Option<&SourceRecipeKey>,
    ) -> BuildStamp {
        BuildStamp::projected(&self.output).with_prefix(project).add_stamp(format!(
            "trust.{project}-working-source/v2\ntarget {}\nsource {}\nrequest {}\nlinking {}\ndependency {}\n",
            target, self.observed.as_deref().unwrap_or("unknown"),
            recipe.map_or("unknown", |key| key.request.as_str()),
            recipe.map_or("unknown", |key| if key.link_shared { "shared" } else { "static" }),
            recipe.map_or("unknown", |key| key.dependency.as_str())))
    }
    pub(super) fn refuse_linked_miss(&self) -> Result<(), String> {
        let namespace = crate::utils::trust_repo_cache::cleanup_input_namespaces(
            &self.anchor,
            &self.output,
            &[],
        )?;
        if namespace.linked {
            return Err("source-build miss through a reuse link; refusing mutation".into());
        }
        namespace.recheck()
    }
    /// Begins a miss of `stamp` under every guard a mutation of the output takes. Returns
    /// whether the CMake build of this generation, configured at this root, was kept
    /// ([`begin_cmake_miss`]); otherwise the root was begun afresh.
    pub(super) fn begin(
        &self,
        stamp: &BuildStamp,
        prepared: &cmake::Prepared,
        generation: CmakeGeneration,
        additional_inputs: &[PathBuf],
    ) -> Result<bool, String> {
        use crate::utils::trust_repo_cache::cleanup_input_namespaces;
        if generation == CmakeGeneration::Known
            && (self.observed.is_none()
                || parse_source_completion(stamp.stamp().as_bytes()).is_none())
        {
            return Err(
                "unknown source/request/mode/dependency cannot retain a known generation".into()
            );
        }
        let paths = prepared.cleanup_inputs().ok_or(
            "unavailable selected-input namespace evidence; refusing destructive source-build miss",
        )?;
        let paths = paths.iter().chain(additional_inputs).cloned().collect::<Vec<_>>();
        let namespace = cleanup_input_namespaces(&self.anchor, &self.output, &paths)?;
        if namespace.linked {
            return Err("source-build miss through a reuse link; refusing mutation".into());
        }
        // Repeat the full safety walk even when content is Unknown, before mutation.
        observe_cmake_sources(&self.source, &self.output).map_err(|error| error.to_string())?;
        namespace.recheck()?;
        begin_cmake_miss(stamp, generation).map_err(|error| error.to_string())
    }
    pub(super) fn unchanged(&self) -> bool {
        self.observed.as_ref().is_some_and(|before| {
            observe_cmake_sources(&self.source, &self.output).ok().flatten().as_ref()
                == Some(before)
        })
    }
    pub(super) fn complete(
        &self,
        stamp: &BuildStamp,
        dependencies_unchanged: impl Fn() -> bool,
    ) -> std::io::Result<bool> {
        if parse_source_completion(stamp.stamp().as_bytes()).is_none()
            || !self.unchanged()
            || !dependencies_unchanged()
            || !installed_outputs::publish(stamp)?
            || !self.unchanged()
            || installed_outputs::matches(&self.output, stamp.stamp()).is_none()
            || !dependencies_unchanged()
        {
            return Ok(false);
        }
        stamp.write()?;
        Ok(true)
    }
    pub(super) fn cache_matches(&self, project: &str, stamp: &BuildStamp, artifact: &Path) -> bool {
        if self.observed.is_none()
            || !parse_source_completion(stamp.stamp().as_bytes())
                .is_some_and(|record| record.project == project)
            || !regular_source_artifact(artifact)
        {
            return false;
        }
        let Ok(root) = crate::utils::trust_repo_cache::selected_input_namespace(&self.output)
        else {
            return false;
        };
        let read_stamp = BuildStamp::new(&root).with_prefix(project).add_stamp(stamp.stamp());
        stamp.is_up_to_date()
            && cmake_generation_matches(&read_stamp)
            && installed_outputs::matches(&self.output, stamp.stamp()).is_some()
    }
}

pub(super) fn validate_owned_source_build(builder: &Builder<'_>) -> Result<(), String> {
    // The default Bootstrap recipe has typed selected inputs. Arbitrary user
    // operands may introduce paths that cannot be protected before replacement.
    if !builder.config.llvm_build_config.is_empty()
        || builder.config.llvm_cflags.is_some()
        || builder.config.llvm_cxxflags.is_some()
        || builder.config.llvm_ldflags.is_some()
        || builder
            .config
            .llvm_use_linker
            .as_deref()
            .is_some_and(|linker| !Path::new(linker).is_absolute())
        || builder.config.llvm_pgo.generate_profile.is_some()
        || builder.config.llvm_pgo.use_profile.is_some()
    {
        return Err("custom LLVM recipe operands have unavailable cleanup namespace evidence; refusing destructive miss".into());
    }
    if !builder.selected_ninja() {
        return Err(
            "source generation replacement currently requires an explicitly bound Ninja program"
                .into(),
        );
    }
    builder.validate_ninja();
    Ok(())
}

#[cfg(all(test, unix))]
pub(super) fn prepare_owned_source_build(
    builder: &Builder<'_>,
    cfg: &mut cmake::Config,
) -> Result<cmake::Prepared, String> {
    validate_owned_source_build(builder)?;
    // This is the explicit miss-only selection consumed by CMake, not an inference
    // about what CMake would otherwise discover later.
    cfg.define_input_program(
        "CMAKE_MAKE_PROGRAM",
        &[OsStr::new("ninja-build"), OsStr::new("ninja")],
    );
    cfg.try_prepare().map_err(|error| format!("unavailable source-build cleanup inputs: {error}"))
}
