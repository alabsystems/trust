// THE MINIMAL PAIR. This is `typeclass_resolution_at_concrete_type.rs` with ONE
// token changed — `op := fun x y => x + y` becomes `op := fun x _ => x` — and it
// PASSES. Measured 2026-09-19 with `CLEAN_U2_MINT_TRACE=1`:
//
//   this file                            rc=0, 0 mints
//   typeclass_resolution_at_concrete_type rc=1, 9 mints, registered {u_3,u_4,u_5}
//
// WHAT IT CORRECTS. The probe script said the discriminator was "a VALUE class
// parameter is fine; only a TYPE-kinded one plus an actual method use leaks".
// This file has a TYPE-kinded class parameter (`Mag (a : Type)`) AND an actual
// method use (`twice 5` -> `Mag.op x x`) and leaks nothing, so that is not the
// discriminator. `typeclass_value_param_is_fine.rs`'s own note has the right
// reason but attached to the wrong knob: what matters is whether the INSTANCE
// BODY mentions a polymorphic constant whose freshened levels nothing
// constrains.
//
// `x + y` on `Nat` resolves `HAdd.hAdd.{u,v,w}` — three levels, which is exactly
// the three that leak. `fun x _ => x` mentions no polymorphic constant, so
// nothing is freshened. And the leak does not need `twice`: `def five : Nat :=
// Mag.op 2 3`, with the arithmetic instance, leaks the same three, so it is
// neither the use site nor the polymorphic helper.
//
// So the defect is in elaborating the INSTANCE, not in resolving it: the stored
// instance `expr` carries levels that `Nat : Type 0` should have pinned to 0.
// See reports/2026-09-19-the-lean-typeclass-gap-is-in-the-island.md, addendum 3.
pub mod m { clean {
    class Mag (a : Type) where
      op : a -> a -> a
    instance : Mag Nat where
      op := fun x _ => x
    def twice {a : Type} [Mag a] (x : a) : a := Mag.op x x
    def five : Nat := twice 5
} }
