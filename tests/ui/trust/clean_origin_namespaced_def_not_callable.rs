//@ needs-trust-verify
//@ check-fail
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//! **A `def` inside a Clean `namespace` is given no Rust path — and the call
//! site is now TOLD so (ruling v7/D3).**
//!
//! Measured 2026-09-16 (probe-call 24/24b/24c): `Geo.area` below is
//! kernel-checked and visible to every Clean declaration in the crate, but only
//! an island's TOP-LEVEL `def`s are mint candidates, so neither `m::Geo::area`
//! nor `m::area` names anything. Both got a bare `E0433`/`E0425` with the
//! declaration in plain sight three lines up — and existing Lean libraries are
//! namespaced throughout, so this is the first thing a converted crate meets.
//!
//! Nothing is minted that was not minted before: a Clean namespace is still
//! not a Rust module. The errors stay; they now say why, where the declaration
//! is, and what works today (a top-level wrapper — `area_w` below, measured
//! running as probe 24c).
//!
//! `dont-require-annotations` is deliberately ABSENT: every NOTE is annotated,
//! so the close negative twin (`m::Nope::area`, a path that does not walk
//! through the namespace) fails the test if it ever grows the island note.

mod m {
    clean {
        namespace Geo
        def area (w : UInt64) (h : UInt64) : UInt64 := w * h
        end Geo
        def area_w (w : UInt64) (h : UInt64) : UInt64 := Geo.area w h
    }
    //~^^^^^ NOTE `Geo.area` is declared here, inside a block of this `clean { … }` island
    //~| NOTE `Geo.area` is declared here, inside a block of this `clean { … }` island
}

fn main() {
    // The path walks THROUGH the Clean namespace as if it were a Rust module.
    let _ = m::Geo::area(3, 4);
    //~^ ERROR cannot find `Geo` in `m`
    //~| NOTE could not find `Geo` in `m`
    //~| NOTE A Clean namespace is not a Rust module

    // The bare name, as if the namespace were transparent.
    let _ = m::area(3, 4);
    //~^ ERROR cannot find function `area` in module `m`
    //~| NOTE not found in `m`
    //~| NOTE A Clean namespace is not a Rust module

    // CLOSE NEGATIVE TWIN: ends in the nested `def`'s bare name but does not
    // walk through its namespace — an ordinary `E0433`, no island note.
    let _ = m::Nope::area(3, 4);
    //~^ ERROR cannot find `Nope` in `m`
    //~| NOTE could not find `Nope` in `m`

    // POSITIVE: the option the note gives. A top-level wrapper IS minted; an
    // `E0425` here would be an unannotated error.
    let _ = m::area_w(3, 4);
}
