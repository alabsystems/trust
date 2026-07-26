# optres-payload-extract-2026-07-17 — the payload-extraction implementation target

The next frontier after W-DISCR-LEAF: extract the Some/Ok PAYLOAD (not just the
tag). 8 monomorphic instances (Option/Result × unwrap/expect/unwrap_or ×
i32/u8), all SHAPE_GAP.

Two sub-shapes:
- DIVERGENCE-GUARDED (unwrap/expect, 4-6bb): SwitchInt(Discriminant(o)) →
  {Some: _0 = (o as Some).0; return} {None: panic (Opaque/Unreachable)}. On the
  happy path returns the payload; the panic path diverges.
- TOTAL SELECT (unwrap_or/unwrap_or_default, 5-10bb): SwitchInt(Discriminant(o))
  → {Some: _0 = (o as Some).0} {None: _0 = d (or Default via __trust_total_clone)}.

DESIGN DIRECTION (value-faithful via the recursor): unwrap_or(o,d) =
Option.rec (λ_.Int) d (λx.x) (g o). The recursor case-split scrutinizes the enum
VALUE g o directly; the MIR's SwitchInt(Discriminant) is just how that same
case-split compiles. clean_ground.rs:440-461 already has the recursor-based
variant-field extraction primitive ("<E>.rec.{1} (motive) minors base", ι-reduces
to the active variant's field). The design + adversarial-soundness verification
is the payload-extraction-design workflow (wf_779b8c2b). Implementation composes
the existing recursor-extraction + real enum inductive carriers + the
discriminant-switch recognizer. Does NOT touch resolve_cmp_side (no m5 collision).
