//@ check-pass
//@ compile-flags: -Z trust-ir-lower -Z trust-verify=off

// Trust (vtable slice 11 — the OVERWRITTEN-lane zero spellings): the differential's
// dead-seed zero speller (`zero_const`) gained exactly two arms — `Ty::Ptr ->
// Constant::Int(0)` (the null pointer; both pinned trust-ir authorities accept the
// pairing) and `Ty::Unit -> Constant::PhantomData` (the sole inhabitant) — the producer's
// own wave-PS `seed_overwritten_ty` convention, carried into the differential with the
// dead-seed COVERAGE PROOF itself as the witness: every `zero_const` consumer runs under
// `UndefClass::DeadSeeds`, and `undef_is_dead_seed` admits only Tuple/Struct-typed
// `Inst::Undef` seeds whose EVERY top-level field is overwritten by a single-use
// InsertField chain before any other use, so a `Ptr`/`Unit` at any depth sits under an
// overwritten lane and can never be read. Measured on postbuild-vtable11: Agreed
// 2640 -> 2641, clean-skip-oracle-havoc 163 -> 156, zero divergences, zero regressions.
//
// Every body below must keep COMPILING — a lowering decline is a coverage decision, never
// an error — and each pins one measured lane of the slice.

// THE FLIP (issue-97007 lib::{impl#0}::new, the one measured Agreed mover): a unit-field
// struct construction. The oracle seeds `Undef struct{Unit}` + InsertField(0, unit) — a
// fully-covered seed held before this slice ONLY on the missing `Ty::Unit` zero spelling.
pub struct Walk {
    _p: (),
}

pub const fn new() -> Walk {
    Walk { _p: () }
}

// THE PTR-LANE RECLASS (issue-37550 x / issue-87988 hotplug_callback): a closure capturing
// by reference constructs an env `struct{Ptr}` — the same fully-covered seed shape at a
// `Ty::Ptr` lane. The seed now substitutes and BOTH sides interpret ("returns/traps
// matched"), and the verdict is then honestly withheld one gate later by
// `first_unmodeled_observation`'s escaping-Alloca arm (the captured slot's address escapes
// into the env value): clean-skip-oracle-havoc -> clean-skip-unmodeled-observation, the
// tail gate being right. This body pins that the havoc gate no longer fires for the shape.
pub fn env_with_ptr_capture(event: i32) {
    let _ = || {
        match event {
            1 => (),
            2 => (),
            _ => (),
        };
    };
}

// THE POSTURES THAT MUST NOT MOVE (measured byte-identical): a flat enum-model variant
// construction covers the tag + current-variant lanes only, so the other-variant `Ptr`
// lane stays UNCOVERED and the seed stays at the LIVE-havoc gate — no zero spelling can
// unlock a lane the construction deliberately never wrote.
pub static NONE_LIKE: Option<String> = None;

// And the deriving-from divergence trap stays closed — MECHANISM MOVED by vtable
// slice 12: `zero_const` now HAS an Array arm (the seed substitutes), and the trap is
// answered one gate later by `tys_agree`'s (Tuple, Array) Err QUARANTINE — the producer
// spells `[T; N>0]` as `Ty::Tuple` while the oracle spells `Ty::Array`, and the pair is
// a documented spelling split held as a comparability failure, NEVER published as a
// signature divergence. (This body now lands clean-skip-nonscalar-param at its own
// param gate; the quarantine is pinned end-to-end by
// tests/ui/trust/trust_ir_array_slot_value_model.rs and the
// `array_lane_seed_substitutes_but_sig_quarantine_holds` unit pin.)
pub struct ArrayField([u32; 4]);

pub fn construct_array_field(value: [u32; 4]) -> ArrayField {
    ArrayField(value)
}

fn main() {}
