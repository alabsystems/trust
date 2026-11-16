// CLOSED 2026-09-19 (first-party/clean 434ba130d). This row was recorded as
// MUST STAY REFUTED: the island's staged-vs-registered signature comparison
// refused `five` (`staged {} Nat` vs `registered {u_3, u_4, u_5} Nat`) while
// `clean check` passed the same six declarations.
//
// The cause was one step from where the report put it. The instance body's
// `HAdd` levels WERE solved; what leaked was the instance's DECLARED universe
// list: every `elab_instance` exit returned the elaborator's raw universe mint
// vector as the instance's level params, never through
// `finalize_level_params`, so `instMagNat.{?u_0,?u_1,?u_2} : Mag Nat`
// registered with three reserved names the kernel does not reject (it never
// checks that a declared level is USED), every later resolution freshened
// them, and `five`'s own decl close generalized them. The instance path now
// goes through the same boundary a `def` does (clean:
// crates/clean-elab/src/infer/elab_instance.rs, pinned by
// crates/clean-elab/tests/instance_value_levels_e2e.rs).
//
// This row is now a PASS pin: the island commits, `five` registers as `{} Nat`.
// reports/2026-09-19-the-lean-typeclass-gap-is-in-the-island.md.
pub mod m { clean {
    class Mag (a : Type) where
      op : a -> a -> a
    instance : Mag Nat where
      op := fun x y => x + y
    def twice {a : Type} [Mag a] (x : a) : a := Mag.op x x
    def five : Nat := twice 5
} }
