//@ dont-check-compiler-stderr
//@ check-pass
//@ edition: 2021
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=off
#![feature(never_type)]
#![allow(unreachable_code, dead_code)]
//! Trust (wave-UM): an ARM-LESS `match` over a scrutinee that is SYNTACTICALLY
//! uninhabited — `!` itself, or a zero-variant `enum` — seals its block with the
//! diverging terminator `Inst::Unreachable` instead of being refused.
//!
//! `match x {}` type-checks ONLY because rustc's exhaustiveness pass proved the
//! scrutinee uninhabited from this module, so no value can reach the match and
//! control cannot leave it. Built MIR says exactly that: `--emit=mir
//! -Zmir-opt-level=0` on every body below gives a single block terminated by
//! `unreachable`, which is the one instruction this lane emits.
//!
//! Before the lane the two shapes fell into unrelated fallthroughs —
//! `EnumMatch(non-enum mapped ty)` for the zero-variant enum (whose degenerate
//! `AdtDef` never registers as a `Ty::Enum`) and `Match(non-integer scrutinee)`
//! for `!`. `strict` turns each of those tags into a compile error, so this file
//! is the mutation check: measured on the control build (`snap-subject-ct`)
//! EVERY body below fails, with exactly one tag each and no other tag.
//!
//! What the lane deliberately does NOT admit, and what still refuses (probed on
//! the same build): an arm-less `match` on an uninhabited STRUCT (`struct
//! S(Void)`) or TUPLE (`(Void, u32)`) keeps `TupleMatch(no arms)`, because the
//! gate is the syntactic `!`/zero-variant-enum test, not a tcx inhabitedness
//! query — those shapes fall THROUGH to the unchanged dispatch and keep their
//! own precise tag.

enum What {}

/// The `tests/ui/enum/zero-variant-enum-pattern-matching-3037.rs` shape,
/// verbatim: a NON-SCALAR return type the match never produces a value for.
/// The lane returns no value with the block left sealed, so `lower_fn`'s
/// `!self.sealed` tail guard emits no `Return` — no `ReturnArityMismatch`.
fn what_to_string(x: What) -> String {
    match x {}
}

/// The `tests/ui/traits/reservation-impl/non-lattice-ok.rs` shape: a `!`
/// scrutinee under a GENERIC return type.
fn my_from<T>(x: !) -> T {
    match x {}
}

unsafe extern "C" {
    fn mk_ext() -> What;
}

/// The `tests/ui/traits/soundness/transmute-unit-to-never-unsound.rs` shape:
/// the scrutinee is a CALL, not a place. The lane lowers it for its EFFECTS
/// before sealing — the `Inst::Call` stays in the emitted IR, it is not
/// laundered away — and only then seals `Unreachable`. Built MIR gives such a
/// call no return edge at all (its result type is uninhabited); the producer's
/// `Call`-then-`Unreachable` is the same denotation with the successor spelled
/// out. (An `extern` declaration is used for the maker so that the FIXTURE
/// carries no second, unrelated refusal — a local `fn -> What` body of its own
/// still declines with `Ty(opaque-lane enum return)`, which this lane does not
/// touch.)
fn make_any<T>() -> T {
    match unsafe { mk_ext() } {}
}

/// The scrutinee ALREADY diverged: a `-> !` callee makes `emit_call` seal the
/// block itself (#188). The lane must observe `self.sealed` and return without
/// sealing again — `seal_with` asserts against a double seal.
fn mk_never() -> ! {
    loop {}
}

fn after_diverging_call<T>() -> T {
    match mk_never() {}
}

// A `&What` scrutinee (`match *v {}`) is deliberately NOT pinned here. The
// audit proved the gate DOES fire for it, but the `ExprKind::Deref` scrutinee
// is still lowered first (effects before the seal, as this lane requires) and
// pushes `Deref(non-scalar pointee)` on the way, so the body stays dirty under
// `strict`. It is a fair shape for a later deref-scrutinee lane, not evidence
// for this one, and pinning it would have pinned a failure.

/// STATEMENT position, not the function tail. The block is sealed mid-body and
/// the block-statement loop's `if self.sealed` break drops the dead remainder,
/// exactly as it does after a `return`.
fn not_the_tail(x: What) -> u32 {
    match x {};
    0
}

fn main() {}
