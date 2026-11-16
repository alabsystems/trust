//@ probe-shape: Projection
//@ probe-expect: discharged
//@ probe-note: FLIPPED by ref-self I1 (the E6 PARAMETER VIEW), 2026-09-18. MEASURED on a
//@ probe-note: stage-1 compiler carrying the increment.
//@ probe-note: **WHAT SANCTIONS THE FLIP.** The note this header replaced said "must stay
//@ probe-note: red ... flipping this green without a post-state story is how `ensures`
//@ probe-note: starts describing entry values it cannot bind", and
//@ probe-note: `docs/design-notes/2026-09-17-clause-name-capture-and-ref-self-rulings.md`
//@ probe-note: lists reversing a written-down refusal (R3) as a decision separate from
//@ probe-note: accepting R1. The capability and the flip are the same fact — once I1
//@ probe-note: admits the shape this probe goes green whether or not its header is
//@ probe-note: edited — and what licenses it is R1's OWN second half, given with the
//@ probe-note: acceptance: a row discharged this way is graded BELOW `Certified` with a
//@ probe-note: disclosed marker. The sibling record that flipped with it is
//@ probe-note: `tests/ui/trust/e9_field_projection_fail_closed.rs`'s `via_reference`.
//@ probe-note: The post-state story the old note demanded is now supplied, as an
//@ probe-note: ASSUMPTION rather than a proof: owner ruling R1 (ACCEPTED 2026-09-17) —
//@ probe-note: a live `&T` argument with `T: Freeze` is dereferenceable and its pointee
//@ probe-note: bytes are immutable for the duration of the call. `Cst` is `Freeze` and
//@ probe-note: all-scalar, the borrow is shared and plainly named, and the body's only
//@ probe-note: use of it is `Copy((*_1).0)`, so the view presents `_0 = Copy(_1)` over
//@ probe-note: by-value `c.degree`/`c.coeff` and the `Deref` the recognizer refuses is
//@ probe-note: gone before the recognizer sees anything.
//@ probe-note: WHAT THE ROW IS WORTH: `discharged`, but NOT `Certified`. R1's second
//@ probe-note: half is binding — the row reports `Trusted`/`Constructive`, is ABSENT from
//@ probe-note: `of which N kernel-certified`, carries the marker `frozen-shared-erased` on
//@ probe-note: the spec-clean goal row, takes the distinct wire solver label
//@ probe-note: `clean-kernel-view-defeq` and ships NO kernel proof evidence, which is what
//@ probe-note: makes the authenticated `targo trust` lane withhold it. `docs/TCB.md`
//@ probe-note: carries the assumption as the `EnsuresCitationViewDischarge` row.
//@ probe-note: The mutable twin is f70, the non-`Freeze` twin f71, and the field the
//@ probe-note: clause names is pinned against the one the body reads by f73.
clean { def ident_isl (x : UInt64) : UInt64 := x }
pub struct Cst { pub degree: u64, pub coeff: u64 }
pub fn degree_of_ref(c: &Cst) -> u64
    ensures result == ident_isl(c.degree)
{ c.degree }
