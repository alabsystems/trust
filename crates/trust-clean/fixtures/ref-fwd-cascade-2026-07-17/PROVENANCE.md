# ref-fwd-cascade-2026-07-17 — immutable-reference forwarder cascade

Wrappers + their CERTIFIED callees (the ff-gate builds a cross-function
certified-callees map from the dump DIR — the callee dump MUST be present).

Pre-fix baseline:
- clamp_count(c,hi)=cmp::min(c.count,hi)  → FULLY_FAITHFUL  (field-read + Move args ALREADY cascade)
- Option::is_some/is_none, cmp::min, Ord::min → FULLY_FAITHFUL (the leaves)
- direct_fwd(o)=o.is_some()      → SHAPE_GAP  (Ref-of-param arg: `_2=Ref(_1); Call(is_some,[Move _2])`)
- wrap_set(w)=w.0.is_some()      → SHAPE_GAP  (Ref of field-of-deref)
- cfg_has_name/cfg_no_name(c)=c.name.is_some()/is_none() → SHAPE_GAP (Ref of field)

Integrated verdict: all 10 rows certify modulo the three foundational axioms in
callee-first order. In particular, `direct_fwd`, `wrap_set`, `cfg_has_name`, and
`cfg_no_name` advance from `SHAPE_GAP` to `FULLY_FAITHFUL`; the six controls remain
fully faithful.

The resolver accepts only a sole immutable `Ref` definition that dominates its
concrete call use, then reflects the referent operand. Mutable refs, reassigned
bases, later or sibling-branch definitions, ambiguous block identities, and
unmodeled projections decline. The integration test
`tests/ref_fwd_cascade.rs` loads every committed dump and requires the entire
real cascade to certify; the focused unit tests cover the adversarial declines.
