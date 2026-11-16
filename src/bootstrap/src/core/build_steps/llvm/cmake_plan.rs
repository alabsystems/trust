//! Trust: the ordered CMake request a native Bootstrap build applies, and the key
//! its reuse is compared on. Bootstrap writes, not cmake-rs' deferred defaults.

use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};

// Trust: ordered requested Bootstrap writes, not cmake-rs' deferred defaults or
// compiler/tool contents. Retain duplicates: later owner overrides are meaningful.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum CmakeOperation {
    Define(OsString, OsString),
    InputProgram(OsString, OsString),
    InputNamespace(PathBuf),
    CleanupOpaque,
    Env(OsString, OsString),
    Generator(String),
    Target(String),
    Host(String),
    OutDir(PathBuf),
    Profile(String),
    BuildTarget(String),
    // Scheduling/log arguments apply normally but cannot change configuration reuse.
    ExecutionArg(OsString),
}

#[derive(Clone, Default, Debug, PartialEq, Eq)]
pub(super) struct CmakePlan {
    source: Option<PathBuf>,
    pub(super) operations: Vec<CmakeOperation>,
}

impl CmakePlan {
    pub(super) fn source(&mut self, path: impl AsRef<Path>) -> &mut Self {
        self.source = Some(path.as_ref().to_owned());
        self
    }

    pub(super) fn new_config(&self) -> cmake::Config {
        let mut cfg = cmake::Config::new(
            self.source.as_ref().expect("CMake plan requires a source directory"),
        );
        self.apply(&mut cfg);
        cfg
    }

    pub(super) fn define(&mut self, key: impl AsRef<OsStr>, value: impl AsRef<OsStr>) -> &mut Self {
        self.operations
            .push(CmakeOperation::Define(key.as_ref().to_owned(), value.as_ref().to_owned()));
        self
    }
    pub(super) fn define_input_program(
        &mut self,
        key: impl AsRef<OsStr>,
        value: impl AsRef<OsStr>,
    ) -> &mut Self {
        self.operations
            .push(CmakeOperation::InputProgram(key.as_ref().to_owned(), value.as_ref().to_owned()));
        self
    }
    pub(super) fn env(&mut self, key: impl AsRef<OsStr>, value: impl AsRef<OsStr>) -> &mut Self {
        self.operations
            .push(CmakeOperation::Env(key.as_ref().to_owned(), value.as_ref().to_owned()));
        self
    }
    pub(super) fn generator(&mut self, value: &str) -> &mut Self {
        self.operations.push(CmakeOperation::Generator(value.into()));
        self
    }
    pub(super) fn target(&mut self, value: &str) -> &mut Self {
        self.operations.push(CmakeOperation::Target(value.into()));
        self
    }
    pub(super) fn host(&mut self, value: &str) -> &mut Self {
        self.operations.push(CmakeOperation::Host(value.into()));
        self
    }
    pub(super) fn out_dir(&mut self, value: impl AsRef<Path>) -> &mut Self {
        self.operations.push(CmakeOperation::OutDir(value.as_ref().to_owned()));
        self
    }
    pub(super) fn profile(&mut self, value: &str) -> &mut Self {
        self.operations.push(CmakeOperation::Profile(value.into()));
        self
    }
    pub(super) fn build_target(&mut self, value: &str) -> &mut Self {
        self.operations.push(CmakeOperation::BuildTarget(value.into()));
        self
    }
    pub(super) fn quiet_build(&mut self) -> &mut Self {
        self.operations.push(CmakeOperation::ExecutionArg("--quiet".into()));
        self
    }
    pub(super) fn parallel_build(&mut self, jobs: u32) -> &mut Self {
        self.operations.push(CmakeOperation::ExecutionArg("-j".into()));
        self.operations.push(CmakeOperation::ExecutionArg(jobs.to_string().into()));
        self
    }

    pub(super) fn apply(&self, cfg: &mut cmake::Config) {
        for operation in &self.operations {
            match operation {
                CmakeOperation::Define(key, value) => {
                    cfg.define(key, value);
                }
                CmakeOperation::InputNamespace(path) => {
                    cfg.input_path(path);
                }
                CmakeOperation::CleanupOpaque => {
                    cfg.opaque_cleanup_inputs();
                }
                CmakeOperation::InputProgram(key, value) => {
                    cfg.define_input_program(key, &[value.as_os_str()]);
                }
                CmakeOperation::Env(key, value) => {
                    cfg.env(key, value);
                }
                CmakeOperation::Generator(value) => {
                    cfg.generator(value);
                }
                CmakeOperation::Target(value) => {
                    cfg.target(value);
                }
                CmakeOperation::Host(value) => {
                    cfg.host(value);
                }
                CmakeOperation::OutDir(value) => {
                    cfg.out_dir(value);
                }
                CmakeOperation::Profile(value) => {
                    cfg.profile(value);
                }
                CmakeOperation::BuildTarget(value) => {
                    cfg.build_target(value);
                }
                CmakeOperation::ExecutionArg(value) => {
                    cfg.build_arg(value);
                }
            }
        }
    }

    pub(super) fn requested_key(&self) -> String {
        use sha2::Digest;

        use crate::utils::trust_repo_cache::{add, finish};
        let mut hash = sha2::Sha256::new();
        add(&mut hash, b"trust.bootstrap-cmake-request/v1");
        if let Some(source) = &self.source {
            add(&mut hash, b"source");
            add(&mut hash, source.as_os_str().as_encoded_bytes());
        } else {
            add(&mut hash, b"existing-config");
        }
        for operation in &self.operations {
            let (tag, values): (&[u8], Vec<&OsStr>) = match operation {
                CmakeOperation::Define(key, value) | CmakeOperation::InputProgram(key, value) => {
                    (b"define", vec![key, value])
                }
                CmakeOperation::Env(key, value) => (b"env", vec![key, value]),
                CmakeOperation::Generator(value) => (b"generator", vec![value.as_ref()]),
                CmakeOperation::Target(value) => (b"target", vec![value.as_ref()]),
                CmakeOperation::Host(value) => (b"host", vec![value.as_ref()]),
                CmakeOperation::OutDir(value) => (b"out-dir", vec![value.as_os_str()]),
                CmakeOperation::Profile(value) => (b"profile", vec![value.as_ref()]),
                CmakeOperation::BuildTarget(value) => (b"build-target", vec![value.as_ref()]),
                CmakeOperation::ExecutionArg(_)
                | CmakeOperation::InputNamespace(_)
                | CmakeOperation::CleanupOpaque => continue,
            };
            add(&mut hash, tag);
            for value in values {
                add(&mut hash, value.as_encoded_bytes());
            }
        }
        finish(hash)
    }
}

pub(super) fn prepared_cmake_request(
    domain: &[u8],
    plan: &CmakePlan,
    prepared: &cmake::Prepared,
) -> Option<String> {
    use sha2::Digest;

    use crate::utils::trust_repo_cache::{add, finish};
    let inputs = prepared.cache_inputs()?;
    let mut hash = sha2::Sha256::new();
    add(&mut hash, domain);
    add(&mut hash, plan.requested_key().as_bytes());
    add(&mut hash, inputs);
    Some(finish(hash))
}
