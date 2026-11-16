# Lean-side probes

The daily-driver goal names Rust AND Lean. These probe the Lean half. Measured
2026-09-18 on stage-1 `1.99.0-dev (d32480619)`, binary sha256 identical before
and after.

    island_theorem_under_default_policy.rs  verifies under the DEFAULT policy
    induction_on_nat.rs                     recursive def + induction, verifies
    structure_and_projection.rs             structure with fields, verifies
    false_theorem_must_be_rejected.rs       MUST FAIL -- negative control

Run with `-Z trust-verify=off` for the parse/elaborate/kernel path, or with no
flag for the default verifying policy.

`false_theorem_must_be_rejected.rs` is the control that gives the others meaning.
It asks for `a <= min2 a b`, which is false. Expect:

    error: `min2_ge_left` did not elaborate: Tactic failed: omega: ... goal not provable
    error[E0425]: cannot find function `min2` in module `m`

The second line matters as much as the first: a bad proof takes the whole island
down, so the `def` beside it never registers. The island does not half-succeed.

The citation lane lives in the UI suite, not here:
`tests/ui/trust/e9_cited_island_def_discharge.rs` and its undischarged twin.

Scope and argument: `reports/2026-09-18-the-lean-half-measured.md`.

## Fragment boundary (added 2026-09-18)

    dependent_indexed_inductive.rs            Vec (a : Type) : Nat -> Type, verifies
    fin_dependent_index.rs                    Fin 3 with .val / .isLt, verifies
    typeclass_polymorphic_use_works.rs        class + instance + [Mag a] def, verifies
    typeclass_resolution_at_concrete_type.rs  MUST FAIL -- the defect

Dependent elimination WORKS. Typeclasses work through declaration, instance
declaration, and a polymorphic `[Mag a]` definition calling the class method.
What fails is the one step that resolves an instance at a CONCRETE type:

    def five : Nat := twice 5

    error: `five` was registered with a different signature than the one other
           declarations were elaborated against

Not a proof failure and not an unknown identifier: a signature-registration
mismatch at the island seam. A named instance moves the reported name onto the
instance itself, which points at the same seam.

Still unprobed on this half: libraries at mathlib scale. Nothing here imports
anything and the largest island is six lines.

Argument: `reports/2026-09-18-the-lean-fragment-boundary.md`.

## Imports and Mathlib (added 2026-09-18)

    import_is_a_standin_disclosed.rs    builds; discloses the stand-in
    mathlib_proof_must_be_refused.rs    MUST FAIL -- the certification audit

The island lane resolves no external `.olean`. `import Mathlib` is served by
Clean's built-in prelude STAND-IN and says so:

    `Mathlib` was served by Clean's built-in prelude stand-in, NOT by the library

The stand-in supplies NAMES carrying trust provenance, not kernel proofs. A
definition may mention them (`def p7 : Prop := Nat.Prime 7` builds, because a
definition asserts nothing). A PROOF resting on them is refused:

    error: Clean island proof `two_prime` failed the strict certification audit
           because it depends on trust provenance: Nat.Prime, Nat.prime_two

An invented name (`Mathlib.This.Does.Not.Exist`) is rejected outright, so this is
not a blanket accept-everything.

Mathlib-scale development is NOT supported, and the failure mode a reviewer would
most fear -- a proof silently resting on an unproved stand-in and reported as
kernel-checked -- is closed twice: disclosed at the import, refused at the audit.

Argument: `reports/2026-09-18-mathlib-is-not-resolved-and-says-so.md`.
