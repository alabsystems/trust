//@ probe-shape: Projection
//@ probe-expect: discharged
//@ probe-note: FLIPPED BY INCREMENT I2 (disposition R4, implementer-proposed), 2026-09-19. The file name keeps
//@ probe-note: its `NEG_` prefix so the flip stays legible in `git log`; the row is now a
//@ probe-note: POSITIVE and this header is the record of why.
//@ probe-note: WHAT HELD IT RED. `Cursor` is `Freeze` and its `row`/`limit` fields ARE in
//@ probe-note: the scalar vocabulary, but `cells: Vec<u8>` is not, and increment I1
//@ probe-note: flattened a frozen shared pointee ALL-OR-NOTHING (rule D-REF-8). The stated
//@ probe-note: reason was that the MINT side (`clean_island::param_flat_rows`) recomputes
//@ probe-note: the same list and is itself all-or-nothing, so a partial clause side would
//@ probe-note: bind names the mint refuses to produce.
//@ probe-note: WHY THAT REASON DOES NOT APPLY, which is what I2 measured rather than
//@ probe-note: assumed: `param_flat_rows` never sees a borrow on this lane. The mint runs
//@ probe-note: on the VIEW's body, whose parameters are already by-value scalars, so it
//@ probe-note: takes its per-local `ty_to_domain` arm. There is ONE filter — the compiler's
//@ probe-note: `trust_frozen_shared_param_scan` — and the view does not filter at all: it
//@ probe-note: VERIFIES each listed row against the extracted IR (declared index, field
//@ probe-note: name, carrier) and refuses the WHOLE view on any disagreement. A field the
//@ probe-note: table did not list is never inspected, so however the extractor lowered
//@ probe-note: `cells` is irrelevant.
//@ probe-note: THIS PROBE FOUND A REAL DEFECT under I1, kept here because the fix is what
//@ probe-note: makes the row mean what it says. As first measured, K2 — the compiler's own
//@ probe-note: structural interior-mutability walk, decided BEFORE D-REF-8 — refused
//@ probe-note: `Cursor` at `cells.buf.inner.ptr.pointer.pointer`, because `NonNull`'s
//@ probe-note: inner pointer is a PATTERN TYPE in this tree and K2 had no arm for one.
//@ probe-note: K2 therefore disagreed with the trait solver (which answers `Freeze`) on
//@ probe-note: EVERY pointee carrying a `Vec`, `Box` or `String`. Fail-closed, and the
//@ probe-note: refusal disclosed itself — but it would have left this payoff case
//@ probe-note: undischargeable for a reason that has nothing to do with I2. K2 walks a
//@ probe-note: pattern type's BASE, which is its representation, and that is what lets this
//@ probe-note: row be green for the reason it is green.
//@ probe-note: WHAT THE FLIP COSTS. `f71` and `f84` must STAY RED, and from here they are
//@ probe-note: held by `Freeze` alone — with unsupported fields skipped, a `Cell` sibling
//@ probe-note: is skipped like this `Vec` one and the carrier rule refuses nothing. C2
//@ probe-note: (`Ty::is_freeze`) and K2 are the only net, and neither is kernel-checked.
//@ probe-note: Like every view row this is `Trusted`/`Constructive`, never `Certified`.
clean { def id32n (x : UInt32) : UInt32 := x }
pub struct Cursor { pub row: u32, pub limit: u32, pub cells: Vec<u8> }
impl Cursor {
    pub fn row_of(&self) -> u32
        ensures result == id32n(self.row)
    { self.row }
}
