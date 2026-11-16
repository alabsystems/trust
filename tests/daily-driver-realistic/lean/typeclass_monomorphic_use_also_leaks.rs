// CLOSED 2026-09-19 (first-party/clean 434ba130d), with its twin
// typeclass_resolution_at_concrete_type.rs. The control that ruled OUT
// polymorphic application as the cause: the method is applied directly at
// `Nat` and the island still reported three leaked levels. It was never a
// property of the program's polymorphism; it was the instance's DECLARED
// universe list — the raw universe mint vector, returned verbatim by
// `elab_instance` instead of through `finalize_level_params`. Fixed at that
// boundary; this row is now a PASS pin.
// See reports/2026-09-19-the-lean-typeclass-gap-is-in-the-island.md.
pub mod m { clean {
    class Mag (a : Type) where
      op : a -> a -> a
    instance : Mag Nat where
      op := fun x y => x + y
    def five : Nat := Mag.op 2 3
} }
