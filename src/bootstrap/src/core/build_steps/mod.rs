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
pub(crate) mod install;
pub(crate) mod llvm;
pub(crate) mod run;
pub(crate) mod setup;
pub(crate) mod synthetic_targets;
pub(crate) mod test;
pub(crate) mod tool;
pub(crate) mod vendor;
