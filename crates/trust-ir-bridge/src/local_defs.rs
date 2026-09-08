//! The bridge's seam for "how many values can this local hold?" and "what is its
//! value?" — the port of `trust_vcgen::local_defs`.
//!
//! THE CHANNEL SET, not a subset of it. A local receives a value through several
//! channels, and the bug class this module exists to close is a scan that enumerates
//! a proper subset. The complete set is `trust_types::LocalWrite`, produced by
//! `Statement::local_write` / `Terminator::local_write` — wildcard-free matches, in
//! the crate that owns those `#[non_exhaustive]` enums, so a new MIR variant is a
//! compile error until it is classified — plus the ENTRY definition of a PARAMETER
//! (`1..=arg_count`), which is not a statement or a terminator at all and which no
//! block scan can see.
//!
//! A predicate that scans a subset reads a local written through the others as
//! single-valued, and a fact keyed on that reading is emitted against the local's BARE
//! name, which the version fabric then binds to whichever version is terminal in the
//! block under proof — including a version that never ran the write the scan saw.
//!
//! THE BLOCK SCAN IS PRIVATE TO THIS MODULE. The bridge lowers the same
//! `VerifiableFunction` trust-vcgen verifies, so every def-counting question it asks
//! is one of the questions below.
//!
//! THE SAME ANSWER AS THE TRUST-VCGEN SEAM. Both charge the entry definition to a
//! parameter UNCONDITIONALLY and both enumerate the same channels. An earlier revision
//! of this module described the vcgen seam as relaxing that for a parameter whose entry
//! value is provably DEAD, making this one the stricter of the two; that relaxation was
//! REMOVED (two independent kernel-certified false proofs went through it — see
//! `trust_vcgen::local_defs::body_value_count`), and the two seams now answer
//! identically. `bridge_seam_implies_the_vcgen_seam` pins the direction that would
//! matter if they ever drifted (the bridge must never admit what vcgen withholds) and
//! `the_two_seams_agree_on_every_shape` pins the equality itself, on a corpus that
//! separates both answers. `trust-ir-bridge` deliberately does not depend on
//! `trust-vcgen` (see its `Cargo.toml`), so the two cannot be one function.

use trust_types::{LocalWrite, Rvalue, ValueCount, VerifiableFunction};

/// True iff `local` is a function PARAMETER — the locals with an implicit ENTRY
/// definition. The return place (`_0`) is not one.
pub(crate) fn is_parameter(func: &VerifiableFunction, local: usize) -> bool {
    is_parameter_of(func.body.arg_count, local)
}

/// [`is_parameter`] for a caller that holds the block list and the argument count but
/// not the `VerifiableFunction` — the StepBy/eq-model resolvers over `TrustBlock`s.
pub(crate) fn is_parameter_of(arg_count: usize, local: usize) -> bool {
    (1..=arg_count).contains(&local)
}

/// Visit EVERY channel by which a value can reach `local` inside `func.body.blocks`.
/// The ENTRY definition is deliberately NOT visited: every exported question below
/// adds it explicitly via [`is_parameter`].
fn for_each_local_write<'a>(
    func: &'a VerifiableFunction,
    local: usize,
    mut f: impl FnMut(LocalWrite<'a>),
) {
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let write = stmt.local_write(local);
            debug_assert!(
                write.agrees_with(stmt.write_effect()),
                "statement channel classification disagrees with WriteEffect: {stmt:?}"
            );
            f(write);
            if stmt.escapes_local(local) {
                f(LocalWrite::Escape);
            }
        }
        let write = block.terminator.local_write(local);
        debug_assert!(
            write.agrees_with(block.terminator.write_effect()),
            "terminator channel classification disagrees with WriteEffect: {:?}",
            block.terminator
        );
        f(write);
    }
}

/// How many VALUES `local` can hold: one per LOCATED whole-value write, plus the
/// implicit ENTRY definition a parameter carries — and [`ValueCount::AtLeast`] when a
/// write could not be located at all, because absence of information is neither one
/// value nor none.
///
/// Every arm is the one `trust_vcgen::local_defs::body_value_count` states, and for the
/// reasons stated there, so `the_two_seams_agree_on_every_shape` stays true.
pub(crate) fn value_count(func: &VerifiableFunction, local: usize) -> ValueCount {
    let mut n = ValueCount::ZERO.plus(usize::from(is_parameter(func, local)));
    for_each_local_write(func, local, |write| {
        n = match write {
            LocalWrite::Untouched => n,
            LocalWrite::WholeNamed(_) | LocalWrite::WholeOpaque => n.plus(1),
            // The partial channel is owned by the questions that refuse it; the alias
            // channel is the counting question's declared OPEN RESIDUAL.
            LocalWrite::Partial => n,
            LocalWrite::Escape => n,
            // Not a value: the absence of one.
            LocalWrite::Unlocatable => n.plus_unlocatable(),
        };
    });
    n
}

/// True iff `local` PROVABLY holds ONE value everywhere its bare name can be read.
pub(crate) fn holds_one_value(func: &VerifiableFunction, local: usize) -> bool {
    value_count(func, local).is_exactly(1)
}

/// The rvalue of `local`'s ONE value, when a whole-local `Assign` produces it and
/// NOTHING ELSE touches the local. `None` for a PARAMETER with any write (that write
/// is the parameter's SECOND value) and for every local reached by a channel this
/// module cannot name — this resolver's callers INLINE what it returns, so version
/// renaming cannot rescue a wrong answer.
///
/// WITH ONE EXCEPTION, AND IT IS A DEFECT: the MUTABLE ALIAS channel is admitted. The
/// arm below carries the same KNOWN DEFECT notice as
/// `trust_vcgen::local_defs::body_unique_value_def`, which is where the witness and
/// the parked measurement are written down; the two seams answer identically and must
/// be repaired together.
pub(crate) fn unique_value_def(func: &VerifiableFunction, local: usize) -> Option<&Rvalue> {
    let mut found: Option<&Rvalue> = None;
    let mut ambiguous = is_parameter(func, local);
    for_each_local_write(func, local, |write| match write {
        LocalWrite::Untouched => {}
        LocalWrite::WholeNamed(rvalue) => {
            if found.is_some() {
                ambiguous = true;
            } else {
                found = Some(rvalue);
            }
        }
        // KNOWN DEFECT — AN OPEN, KERNEL-CERTIFIED FALSE PROOF, NOT A DESIGN CHOICE.
        //
        // A store through a `&mut local` names a DIFFERENT place, so a write may have
        // arrived where no scan keyed on `local` can see it, and this resolver hands
        // back the one `Assign` it did see anyway. The live witness is `x3::pesc`
        // compiled WITHOUT `-O`, written out in full in
        // `trust_vcgen::local_defs::body_unique_value_def`'s `Escape` arm together
        // with the reason the obvious tightening (moving `Escape` into the ambiguous
        // arm) is NOT the fix: it disables the yield/origin bound behind every Rust
        // `for` loop. The parked report is `escape-residual.md`.
        LocalWrite::Escape => {}
        LocalWrite::WholeOpaque | LocalWrite::Partial | LocalWrite::Unlocatable => {
            ambiguous = true;
        }
    });
    if ambiguous { None } else { found }
}
