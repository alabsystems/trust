// Trust: there is no `toolstate` module. Toolstate only ever existed to report
// the health of rust-lang's out-of-tree tool submodules back to
// rust-lang-nursery/rust-toolstate, which Trust neither publishes to nor reads
// from; every tool bootstrap builds here is in-tree and simply must build. An
// upstream merge that reintroduces the module is reintroducing dead machinery
// (including a `git push` that writes an OAuth token to `~/.git-credentials`).
pub(crate) mod check;
pub(crate) mod clean;
pub(crate) mod clippy;
pub(crate) mod compile;
pub(crate) mod dist;
pub(crate) mod doc;
pub(crate) mod format;
// Trust: completed native runtime ownership is distinct from artifact origins.
pub(crate) mod frontend_runtime;
pub(crate) mod install;
pub(crate) mod llvm;
// Trust: explicit source/output-owned first native object producer.
pub(crate) mod native_object;
// Trust: the bounded native repository workflow composes ordinary bootstrap steps.
pub(crate) mod repo;
pub(crate) mod run;
pub(crate) mod setup;
pub(crate) mod synthetic_targets;
pub(crate) mod test;
pub(crate) mod tool;
pub(crate) mod trust_ir_cg;
pub(crate) mod vendor;

// Trust: ordinary compiler/sysroot and distribution mathematical DATA resource.
pub(crate) mod vf5_resource;
