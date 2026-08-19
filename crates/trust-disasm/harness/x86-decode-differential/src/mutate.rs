//! NON-VACUITY: deliberately wrong decodes the differential must catch.
//!
//! A harness that has quietly stopped comparing something reports perfect
//! agreement, which is indistinguishable from a correct decoder. The gate runs
//! this battery and requires every mutation to be CAUGHT before any agreement
//! number is believed.
//!
//! THE MUTATION IS APPLIED TO THE PROJECTION, not to the shipping decoder. What
//! is under test is whether the COMPARISON would notice a wrong answer, so
//! injecting the wrong answer at the comparison boundary tests exactly that —
//! and it keeps `trust-disasm` free of test-only mutable accessors.
//!
//! THE BATTERY IS A FLOOR. Each mutation breaks a whole class, so one candidate
//! of the right shape catches it. The real defects were narrower: the `R12`
//! index bug needed a REX.X SIB word with index `100` to be in the population
//! at all, which is why `generate::sweep` is systematic over that matrix rather
//! than random.

use crate::compare::{MemProjection, Projection};

pub const BATTERY: &[&str] = &["length", "rip_base", "drop_disp", "drop_index", "reg_rename"];

/// Apply a mutation to our side of the comparison.
pub fn apply(p: &mut Projection, mutation: &str) {
    match mutation {
        // A decoder reporting the wrong length silently reinterprets every
        // following byte.
        "length" => p.len = p.len.saturating_add(1),
        // The original defect: a RIP-relative address resolved against the
        // CURRENT instruction rather than the next one, i.e. short by its size.
        "rip_base" => {
            if let Some(MemProjection::Absolute(a)) = &mut p.mem {
                *a = a.wrapping_sub(1);
            }
        }
        // The displacement dropped from a base+index+displacement address, and
        // mislabelled an "over-approximation".
        "drop_disp" => {
            if let Some(MemProjection::Computed { disp, .. }) = &mut p.mem {
                *disp = 0;
            }
        }
        // The index register dropped, as R12 was.
        "drop_index" => {
            if let Some(MemProjection::Computed { index, .. }) = &mut p.mem {
                *index = None;
            }
        }
        // A register renamed, the shape of the AH-vs-SPL confusion.
        "reg_rename" => {
            if let Some(first) = p.regs.first_mut() {
                *first = format!("{first}_mutated");
            }
        }
        other => {
            eprintln!("unknown mutation `{other}`; --list-mutations");
            std::process::exit(2);
        }
    }
}
