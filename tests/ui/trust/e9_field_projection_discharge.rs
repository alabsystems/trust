//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-pass
//@ dont-require-annotations: NOTE
//! E6/E9 widening increment 7 — DOTTED-PATH SCALAR BINDERS, end to end.
//!
//! Until this landed, every clause the kernel could close was over bare scalar
//! parameters. A fact about a `struct`'s field — which is what a real checker's
//! soundness properties are actually about — could not be *stated*, let alone
//! proved: `c.degree` was not a term the clause grammar had a rule for.
//!
//! The mechanism is deliberately small, and the smallness is the point. A
//! dotted path is ONE OPAQUE SCALAR ATOM, named by its path and bound at the
//! FIELD's carrier. Nothing reflects the struct, no aggregate type reaches the
//! kernel, and the goal below is the same term the undotted spelling would
//! produce — the dot is a NAME, not an operation. What the compiler adds is a
//! binding row per scalar field of every parameter, and a body mint that takes
//! one binder per row:
//!
//! ```text
//!   fn degree_of(c: Cst) -> u64 { c.degree }
//!     mints  trust_import_… := fun (degree : UInt64) (coeff : UInt64) => degree
//!     goal   ∀ (d : UInt64) (k : UInt64), Eq UInt64 (trust_import_… d k) (ident_isl d)
//! ```
//!
//! The flattening is canonicalized on the STRUCT, not on the clause: every
//! field is bound whether or not the clause mentions it, so the minted arity
//! cannot depend on what any one clause happens to say. And because the clause
//! side computes that list from HIR types while the mint side computes it from
//! the extracted IR, the mint RECORDS the names it bound and the discharge
//! refuses any clause whose list differs — a same-length reordering is the one
//! drift the kernel could not see for itself.

clean {
    def ident_isl (x : UInt64) : UInt64 := x

    theorem degree_le_self : forall (d : UInt64) (k : UInt64),
        Nat.le (UInt64.toNat d) (UInt64.toNat d) :=
        fun d k => Nat.le.refl (UInt64.toNat d)
}

pub struct Cst {
    pub degree: u64,
    pub coeff: u64,
}

// (1) UNCITED. `result` is bound to the E6 import of this body — which is the
// field projection `fun degree coeff => degree` — so the clause closes by
// definitional equality with no theorem at all.
pub fn degree_of(c: Cst) -> u64
    ensures result == ident_isl(c.degree)
{
    c.degree
}

// (2) The OTHER field of the same struct, to show the binder index is carried
// rather than assumed: the mint is `fun degree coeff => coeff` here.
pub fn coeff_of(c: Cst) -> u64
    ensures result == ident_isl(c.coeff)
{
    c.coeff
}

// (3) CITED — the veripb client's own citation spelling, now over a field. The
// clause mentions `result`, which binds to the E6 import
// (`fun degree coeff => degree`), and the theorem is stated over the value that
// import UNFOLDS to; the import is a reducible definition, so no theorem ever
// has to name `trust_import_*`. That is exactly how the client's nine existing
// citations discharge, and all that changed is that `c.degree` is now sayable.
//
// The clause must NOT call an island definition here: only the UNCITED defeq
// lane installs island-definition facets, so `ident_isl(c.degree) <= c.degree
// by …` is refused with "no diagnostic E6 facet record exists". That is a
// property of the cited lane, unrelated to fields, and it is why (1) and (3)
// are spelled differently.
pub fn degree_bound(c: Cst) -> u64
    ensures result <= c.degree by degree_le_self
{
    c.degree
}

// (4) TWO struct parameters — FOUR binders, and the projected one is at flat
// index 2. The flattening walks parameters in declaration order and each
// parameter's fields in declaration order, on both the clause side and the mint
// side; this is the fixture that would go red if either walk changed.
#[allow(unused_variables)]
pub fn second_degree(a: Cst, b: Cst) -> u64
    ensures result == ident_isl(b.degree)
{
    b.degree
}

fn main() {}
