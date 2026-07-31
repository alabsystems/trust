//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ build-pass
// REGRESSION (stolen-comptime-body poison, root-cause-FIXED rather than reported): a
// `#[rustc_comptime]` fn's `hir_body_const_context` is `ConstContext::Const{..}`, so
// `check_crate`'s eager const-eval of `N` runs `inner_mir_for_ctfe`'s STEALING arm and
// steals `comptime_leaf`'s elaborated MIR before the crate-wide R1 caller scan runs
// (the ordering documented in tests/ui/comptime/trust-scc-graph-excludes-comptime.rs).
// The scan used to poison the WHOLE crate over that one already-stolen body — a
// permanent, avoidable capability loss: R1 could never flip anything in any crate
// containing a comptime item. But the stolen body is not lost: `mir_for_ctfe` is the
// CONSUMER of exactly that steal (the same query the scan already uses for const/static
// item bodies), so the scan now routes comptime bodies there and stays complete.
//
// This test FAILS on the unrepaired code: with the crate poisoned, `scaled`'s
// div-by-zero kept its failure (check-fail), whereas this crate must build-PASS —
// the `flip_private_reachable.rs` shape (private helper, `#[inline] pub` caller
// establishing `divisor = 4 != 0`, discharged as sealed kernel-replayed proof
// authority) with a comptime item present. Fail-closedness is retained where it is
// still needed: the comptime body's own call edges are recorded non-reproducible
// (its callees can never classify Total), and a stolen NON-const body still poisons.
#![feature(rustc_attrs)]

#[rustc_comptime]
fn comptime_leaf() -> usize {
    1
}

// Eagerly evaluated by `check_crate`, stealing `comptime_leaf`'s elaborated MIR
// before the R1 scan runs.
const N: usize = comptime_leaf();

// Keeps `N` (and through it the comptime fn) alive without adding any arithmetic
// obligation of its own: a bare const load is obligation-free.
pub fn n() -> usize {
    N
}

fn scaled(x: u32, divisor: u32) -> u32 {
    x / divisor
}

#[inline]
pub fn api(x: u32) -> u32 {
    scaled(x, 4)
}
