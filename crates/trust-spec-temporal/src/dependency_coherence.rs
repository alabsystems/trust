//! Compile-time source-coherence sentinels for the in-process temporal stack.
//!
//! Cargo intentionally does not inherit a dependency crate's `[patch]` tables.
//! Consequently, a repository-external path consumer of `trust-spec-temporal`
//! can otherwise combine the local Clean/TrustIR types used directly here with
//! the git-sourced instances inherited by `tla-check`. Those packages have the
//! same names, but Rust correctly treats their public carriers as different
//! types. For a proof pipeline, merely keeping the two universes on disjoint API
//! paths is not an acceptable form of "coherence".
//!
//! These functions need not run. Rust type-checks their bodies while compiling
//! this crate, so the private marker-trait obligations make a split source graph
//! a hard build error. A downstream root that repeats the canonical patch
//! closure gets one package instance and satisfies both obligations.

trait RepositoryCleanKernelUniverse {}

impl RepositoryCleanKernelUniverse for clean_kernel::Expr {}

fn require_repository_clean_kernel<T: RepositoryCleanKernelUniverse>(_: &T) {}

#[allow(dead_code)]
fn clean_kernel_from_ty_is_repository_kernel() {
    let ty_expr = tla_check::reflect::quote_state(&[]);
    require_repository_clean_kernel(&ty_expr);
}

#[allow(dead_code)]
fn clean_kernel_from_trust_ir_is_repository_kernel(obligation: trust_ir::ExprObligation) {
    require_repository_clean_kernel(&obligation.goal);
}

trait RepositoryTrustIrUniverse {}

impl RepositoryTrustIrUniverse for trust_ir::Module {}

fn require_repository_trust_ir<T: RepositoryTrustIrUniverse>(_: &T) {}

#[allow(dead_code)]
fn trust_ir_from_ty_is_repository_trust_ir(function: tla_check::GpuFunction) {
    require_repository_trust_ir(&function.module);
}
