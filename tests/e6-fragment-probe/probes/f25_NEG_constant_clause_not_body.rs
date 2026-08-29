//@ probe-shape: Projection
//@ probe-expect: defeq-rejected
//@ probe-note: THE PERMANENT NEGATIVE CONTROL FOR THE CONSTANT CLASS (added
//@ probe-note: 2026-08-22, when f05-f09 flipped from refusal to discharge after
//@ probe-note: the arity-preserving ConstantUint routing (74f315aa368) and the
//@ probe-note: term-evidence domain derivation (0acfcc223a2) landed).
//@ probe-note:
//@ probe-note: The clause and the island `def` here are BYTE-IDENTICAL to the
//@ probe-note: discharging f05: `def const42 (x : UInt64) : UInt64 := 42` cited
//@ probe-note: as `const42(x)`. ONLY the Rust body differs — it returns `x`
//@ probe-note: instead of `42`. So this probe asks the one question a clause-
//@ probe-note: anchored discharge could never answer: is the verdict about the
//@ probe-note: EMITTED BODY, or merely about the clause and the declaration
//@ probe-note: agreeing with each other?
//@ probe-note:
//@ probe-note: It must stay `defeq-rejected` forever. Measured 2026-08-22: the
//@ probe-note: recognizer reads `Projection { param: 0 }`, side B mints the
//@ probe-note: projection, and the kernel refuses — "the two sides are not
//@ probe-note: definitionally equal (Eq.refl does not check)". If this probe
//@ probe-note: ever discharges, the constant lane has become clause-anchored
//@ probe-note: and every f05-f09 discharge is worthless: fix that, never this.
clean { def const42 (x : UInt64) : UInt64 := 42 }

pub fn answer(x: u64) -> u64
    ensures result == const42(x)
{
    x
}

fn main() {
    let _ = answer(7);
}
