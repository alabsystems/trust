//! This module contains integral components of the build and configuration process, providing
//! support for a wide range of tasks and operations such as caching, tarballs, release
//! channels, job management, etc.

pub(crate) mod build_stamp;
pub(crate) mod cache;
pub(crate) mod cc_detect;
pub(crate) mod change_tracker;
pub(crate) mod channel;
pub(crate) mod exec;
pub(crate) mod helpers;
pub(crate) mod job;
// Trust: stage declared static native inputs in development SDKs.
pub(crate) mod llvm_native_dev;
// Trust: use the same LLVM file classification as its build script.
#[path = "../../../../compiler/rustc_llvm/native_link.rs"]
pub(crate) mod llvm_native_link;
// Trust: lend one implicit execution to a synchronous metadata child.
#[cfg(any(target_os = "macos", target_os = "linux"))]
pub(crate) mod fixed_admission;
pub(crate) mod metadata_scheduler;
pub(crate) mod render_tests;
// Trust: the named jobserver a seed Cargo gets when none is inherited
// (BOOTSTRAP-JOBSERVER-PROBE-1).
#[cfg(unix)]
pub(crate) mod seed_jobserver;
// Trust: explicit immutable runtime fixtures for compiler library tests.
pub(crate) mod retained_compiler_fixture;
pub(crate) mod tarball;
// Trust: keep the build directory out of Time Machine (EW-18).
pub(crate) mod trust_build_tree;
// Trust: refuse at the start a build location the held-input rule refuses later.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
pub(crate) mod trust_held_location;
// Trust: which sources the in-tree LLVM of a build directory was built from (the tree is
// vendored, so upstream's stamp cannot say).
// Trust: the actual compiled request owns source-readiness scope.
pub(crate) mod trust_preparation;
// Trust: native repository execution transactions and the existing build-tree lease.
pub(crate) mod trust_repo_cache;
pub(crate) mod trust_repo_lock;
pub(crate) mod trust_repo_tools;
// Trust: a dev stage-1 build's version names its sources, not HEAD (TB1).
pub(crate) mod trust_source_identity;
// Trust: seed a fresh worktree's stage 1 from another worktree's green one (EW-9).
pub(crate) mod trust_stage1_seed;
// Trust: the version-authority gate (one version line, one authority).
pub(crate) mod trust_version_authority;
// Trust: prune the superseded cargo units and duplicate objects of the build trees after
// every successful run (the Continuum's native prune; Unix only).
pub(crate) mod trust_prune;

pub(crate) mod tracing;

#[cfg(feature = "build-metrics")]
pub(crate) mod metrics;

#[cfg(feature = "tracing")]
pub(crate) mod step_graph;

#[cfg(test)]
pub(crate) mod tests;
