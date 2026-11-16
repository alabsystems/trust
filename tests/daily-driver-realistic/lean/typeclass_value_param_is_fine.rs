// The CONTROL that localises the universe leak: a class whose parameter is a
// VALUE rather than a type resolves and registers cleanly, method use included.
//
// CORRECTED 2026-09-19 (addendum 6): this passes because of its instance BODY,
// not its parameter kind. The same value-parameter class with `name := 3 + 4`
// leaks three levels, exactly like the Type-parameter twin — because `+` reaches
// the universe-polymorphic `HAdd`, whose three level params the instance then
// carries and `instance.rs:887` freshens at every resolution with nothing to
// constrain them. `name := 7` mentions no polymorphic constant, so nothing is
// freshened and nothing leaks.
//
// reports/2026-09-19-the-lean-typeclass-gap-is-in-the-island.md, addendum 2.
pub mod m { clean {
    class Tag (n : Nat) where
      name : Nat
    instance : Tag 0 where
      name := 7
    def five : Nat := Tag.name 0
} }
