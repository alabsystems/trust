//@ probe-shape: none
//@ probe-expect: clause-outside-fragment
//@ probe-note: NEGATIVE, must stay red. **This was the ONLY shape where `Freeze` was the
//@ probe-note: sole net in increment I1** — the measurement `f71` was wrongly said to be.
//@ probe-note: Since I2 (2026-09-19) it is no longer alone: the all-or-nothing vocabulary
//@ probe-note: rule that gave `f71` and `f91` a second net is deleted, so those two are
//@ probe-note: held by C2/K2 as well. This row's own accounting is unchanged.
//@ probe-note: `core::cell::UnsafeCell<u32>` declares exactly ONE field, `value: u32`,
//@ probe-note: which IS in the scalar vocabulary; it is a struct, it is sized, and here
//@ probe-note: it is fully instantiated. So C1, C3, the pattern check and the carrier rule
//@ probe-note: all admit it, and every later condition would give it a row. The only two
//@ probe-note: things that refuse it are C2 (rustc's `Ty::is_freeze`) and K2 (the
//@ probe-note: compiler's own structural `UnsafeCell` walk), with C2 decided first.
//@ probe-note: `f85` is the POSITIVE twin: a struct with the identical declared field
//@ probe-note: shape (`Boxed { value: u32 }`) that IS admitted. The pair is the
//@ probe-note: differential control — nothing in-tree can stub the trait solver's answer,
//@ probe-note: so two programs that differ only in interior mutability are what shows
//@ probe-note: which net is holding.
//@ probe-note: SOUNDNESS, stated plainly: admitting this would build a defining equation
//@ probe-note: over a pointee another alias may legally mutate during the call, which is
//@ probe-note: exactly what owner ruling R1 does NOT assume.
clean { def id32u (x : UInt32) : UInt32 := x }
use std::cell::UnsafeCell;
pub fn cell_peek(c: &UnsafeCell<u32>) -> u32
    ensures result == id32u(0)
{ 0 }
