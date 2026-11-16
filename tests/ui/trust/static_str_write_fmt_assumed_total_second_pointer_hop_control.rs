//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! ZERO-ROW-GATE AMENDMENT (2026-10-10, docs/DECISION_QUEUE.md ZERO-ROW-GATE): this control is now check-fail,
//! not check-pass: `mid`, `Sink::write_str` and `render` each have zero obligations
//! (pinned NOTEs) but a call no authenticated registry discharges, so each publishes an
//! `unknown` row and is refused. "check-pass here means the walk refuses on the AXIOM"
//! below now reads: the pinned NOTEs mean no obligation was added. The differential
//! with the mutant `..._second_pointer_hop_root_stays_closed.rs` is kept by the mutant
//! FORBIDDING that note: it must still refuse for its own reason.
//!
//! CONTROL for `static_str_write_fmt_assumed_total_second_pointer_hop_root_stays_closed.rs`.
//! Read both or neither.
//!
//! Byte-identical two-hop reified-pointer structure — `write_str` reifies `mid`,
//! `mid` reifies `boom`, both edges indirect — with the `#[trust::assume_total]`
//! attribute and the `panic!` removed. The leaf is genuinely total, so there is no
//! axiom under this verdict and it must verify CLEAN.
//!
//! WHAT THIS GRADES, and why the mutant alone is not enough. The transitive hop
//! makes the census read bodies it previously stopped short of. A recursion that
//! declined on the SHAPE it now walks — "an unexplored-looking hop", "a bundle that
//! reifies a pointer" — would still turn the mutant red for the wrong reason while
//! silently making every pointer-reifying bundle unspendable. This file is the half
//! that catches that: `check-pass` here means the walk refuses on the AXIOM, not on
//! the traversal.
//!
//! A prior census WAS reverted for over-declining (`16be43eca1`, seven dyn-reliance
//! fixtures), but do not read that as this file's justification — the attribution was
//! wrong and was retracted by measurement. Re-landing the census left the seven
//! failing unchanged and broke five more (`12f3b32af9`); their real cause was an
//! upstream cast-lowering change, repaired in trust-vcgen by `c9ae8b6532`. With the
//! transitive census live, all 25 `dyn_dispatch_reliance*` / `dyn_coercion*` fixtures
//! pass at stage2 — 24 `dyn_dispatch_reliance*` (`passed:24 failed:0`) plus the one
//! `dyn_coercion*`, `dyn_coercion_bundle_stays_well_typed` (`passed:1 failed:0`); an
//! earlier revision of this line said 24 for the pair of globs and undercounted the
//! second by its only member. This file guards a direction that has never actually
//! been observed failing here.
//!
//! MEASURED on stage2 `trustc` built from `ddb545d35b`, whose `trust_verify.rs` is
//! byte-identical to the one at `28220d5879` where the numbers were taken:
//! `axiom census root=<…Sink as core::fmt::Write>::write_str axiom_free=true`,
//! `user_axiom_keys=0`, `pointer_hop_reads_complete=true`, rc=0. Watched failing:
//! plant `#[trust::assume_total]` + `panic!` on `boom` and this `check-pass` fixture
//! goes red.
#![no_std]
#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(trust)]

use core::fmt;

/// No attribute, and genuinely total — the only difference from the mutant.
fn boom() {}

/// HOP 2, identical to the mutant's.
// ZERO-ROW-GATE (2026-10-10): zero bridged obligations plus a call no authenticated registry discharges publish an `unknown` row; refused.
//~vv ERROR Trust strict verification failed for `static_str_write_fmt_assumed_total_second_pointer_hop_control::mid`
//~v NOTE this function has no obligation of its own
fn mid() {
    let f: fn() = boom;
    f();
}

pub struct Sink {
    written: u32,
}

impl fmt::Write for Sink {
    // ZERO-ROW-GATE (2026-10-10): zero bridged obligations plus a call no authenticated registry discharges publish an `unknown` row; refused.
    //~vv ERROR Trust strict verification failed for `<static_str_write_fmt_assumed_total_second_pointer_hop_control::Sink
    //~v NOTE this function has no obligation of its own
    fn write_str(&mut self, s: &str) -> fmt::Result {
        // HOP 1, identical to the mutant's.
        let f: fn() = mid;
        f();
        self.written = s.len() as u32;
        Ok(())
    }
}

// ZERO-ROW-GATE (2026-10-10): zero bridged obligations plus a call no authenticated registry discharges publish an `unknown` row; refused.
//~vv ERROR Trust strict verification failed for `static_str_write_fmt_assumed_total_second_pointer_hop_control::render`
//~v NOTE this function has no obligation of its own
pub fn render(sink: &mut Sink) -> fmt::Result {
    use fmt::Write as _;
    write!(sink, "constant")
}
