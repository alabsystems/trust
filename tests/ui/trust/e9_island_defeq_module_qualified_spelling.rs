//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! **A clause that names an island definition through a Rust MODULE PATH stays
//! refused — and now says the spelling is the problem (ruling v7/D3).**
//!
//! Measured 2026-09-16 (alab-rust probes p4/p5): with the island inside
//! `mod spec`, `ensures result == spec::first(a, b)` failed with the bare "no
//! diagnostic E6 facet record exists for `spec::first`", while the identical
//! clause spelled `first(a, b)` proved. Real crates keep their specifications
//! in a module, so this is the first spelling a converted crate tries.
//!
//! The refusal is KEPT. An island definition is admitted under its Clean name,
//! in Clean's one crate-wide namespace; clause paths are not name-resolved, so
//! at this seam `spec::first` is indistinguishable from `other::first`, a
//! different Rust function sharing the bare name — stripping the qualifier
//! would bind a clause about one function to the definition of another. The
//! message now names the bare Clean spelling and both readings, with options.
//! (The hint's own negative twins — a reflected Rust carrier under the bare
//! name, and no admission at all — are pinned in `trust-spec-elab`:
//! `a_module_qualified_island_spelling_stays_refused_and_names_the_bare_clean_name`.)

pub mod spec {
    clean {
        def first (a : UInt64) (b : UInt64) : UInt64 := a
    }
}

// POSITIVE TWIN, first in the file so it is verified before the strict failure
// below ends the build: the spelling the message recommends. Same island, same
// body, no `use` — it kernel-discharges.
pub fn pick_first_bare(a: u64, b: u64) -> u64
    ensures result == first(a, b)
    //~^ NOTE island definition `first` kernel-discharges this postcondition by definitional equality
{
    a
}

pub fn pick_first_qualified(a: u64, b: u64) -> u64
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    ensures result == spec::first(a, b) //~ ERROR admitted under the bare Clean name `first`
{
    a
}

fn main() {
    let _ = pick_first_bare(1, 2);
    let _ = pick_first_qualified(1, 2);
}
