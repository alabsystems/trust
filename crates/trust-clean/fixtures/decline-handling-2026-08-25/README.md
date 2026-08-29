# decline-handling-2026-08-25 — DECLINE IS NOT DISCHARGE

Real `-Ztrust-dump=mir:` extractions (stage2 `trustc`) of bodies whose obligation
set contains a **declined** row — a `VcKind::UnsupportedMir` the emitter raised
because it could not model the construct.

A verifier has three outcomes: proved, refuted, **declined**. Before this
fixture landed, two trust-clean consumers modelled only two of them:

* `whole_program::{ensures_certified_modulo_3, certify_function_in_graph}`
  selected rows by `proof_level() == L0Safety` (which includes `UnsupportedMir`)
  and handed `vc.formula` to `vc_refute::check_refute_vc`. The slice-range
  emitter built its declined row with `Formula::Bool(false)`, which is UNSAT, so
  the DECLINED row read as DISCHARGED and `vec_range_index_with_ensures`
  reached `ProofStatus::Certified` / `registry.is_assumable() == true`.
* `prove::function_safety_vcs_all_discharged` filtered by
  `mirsem::is_safety_vc_kind`, which does not name `UnsupportedMir`. A body
  whose only obligation is a declined row therefore produced an EMPTY filtered
  set, and the gate returns `true` on empty.

`sources/` holds the exact source; `oracle_rows.txt` holds the runtime oracle
(stock rustc, `-O -C debug-assertions=on`, `catch_unwind` over swept inputs).
Every `p*`/`q*`/`vec_range_index_with_ensures` row PANICS on real inputs.
`safe_div`, `safe_add` and `opaque_divisor` are the negative controls: they
never panic within their declared preconditions and must keep whatever tier
they held.

## What "OPEN" means — the one compensated kind, and where it counts

The **faithfulness** gates ask `mirsem::function_has_open_declined_vc`, not "is
there any decline". Exactly one declined kind is a **hand-off** rather than a
coverage gap, and both ends of that hand-off predate this fixture:

* `trust-vcgen`'s emitter (`generate/slice_conversion.rs`) raises
  `UnsupportedMir { kind: "Rvalue::PtrOffset" }` and says at the emission site
  that the offset's "faithful in-bounds obligation is the intrinsic lane's
  `ptr_offset_bounds_vc` (`0 <= index && index <= len`), which lives over the
  reflected `(base slice, index)` `PtrModel` in **trust-clean**, NOT here".
* `prove::function_ptr_offsets_all_discharged` is the receiving end; its own doc
  calls the row "the obligation swap", and
  `prove::diagnose_fully_faithful_gate`'s production verdict already reads
  `(via_ir || via_mirsem) && function_ptr_offsets_all_discharged`.

So an offset row is spared **only while that lane closes it**, and no other kind
is spared. At the faithfulness tier, refusing a body whose offsets all discharge
would have cost the W2 lane its spelling-independence — the same offset written
`ptr::add` certifying while written `Rvalue::PtrOffset` does not
(`mirsem::tests::ptr_offset_binop_count_certifies_identically_to_intrinsic`).
`decline_gate_tests::ptr_offset_decline_is_honored_only_when_its_lane_closes`
pins both halves.

MEASURED over the repo's own dump fixture corpus (2338 files, 2334 parse as a
`VerifiableFunction`): 121 bodies carry a declined row, and the compensation
fires on **none** of them — the four `Rvalue::PtrOffset` bodies there either
carry a second declined kind (`Rvalue::Cast`) or reach no certification tier at
all (no `#[ensures]`). Its whole live effect is the synthesized BinOp-spelled
`count` above.

### The compensation buys NOTHING at the certification tier

`whole_program::{ensures_certified_modulo_3, certify_function_in_graph}` mint a
different claim from a faithfulness verdict: whole-body panic-freedom plus
assumption authority for every caller. The offset lane does not establish it, so
those two gates refuse **every** declined kind, `Rvalue::PtrOffset` included.

SKIPPING the row there is Channel 2 one level down: in every probe below the
decline is the ONLY L0 row, so the surviving L0 set is empty and the loop's
panic-freedom half is vacuous. Measured on the `ptr-spine-corpus` `count` body,
with `#[ensures(result >= 0)]` (which refutes on the `u64` type bound alone, so
only the L0 set decides), pristine HEAD `70a7534fd1` vs the row skipped:

| probe | oracle | HEAD | skipped | refuse-all |
| --- | --- | --- | --- | --- |
| `count`, `Rvalue::PtrOffset` spelling | 0/24 panics | refused | **cert+assumable** | refused |
| ditto, panicking leaf | **24/24 panics** | refused | **cert+assumable** | refused |
| `count_after_panicking_leaf` (call-prefix layout) | **24/24 panics** | refused | **cert+assumable+`Certified`** | refused |
| every one of the above, `ptr::add` spelling | same | refused | refused | refused |

The `ptr::add` spelling is refused throughout because it keeps a real
`Assertion { "[unsafe:sep:offset] pointer offset out of bounds …" }` row that
does not refute; re-spelling the same offset as `Rvalue::PtrOffset` replaces
that row with the decline. So crediting the compensation at this tier made the
`Rvalue::PtrOffset` spelling STRICTLY MORE authoritative than the intrinsic —
refusing every decline is what makes the two spellings agree here.

The faithfulness tier is untouched: both spellings still reach
`fully_faithful`, which is what
`mirsem::tests::ptr_offset_binop_count_certifies_identically_to_intrinsic` pins.
`decline_gate_tests::ptr_offset_decline_earns_no_certification_tier` pins every
row of the table; `sources/oracle_d1.rs` is the runtime oracle.

## The named coverage gaps this defers

Every tier lost to a declined row is deferred behind a NAMED `trust_vcgen` gap,
one-sided (teaching vcgen the construct flips it back; teaching a trust-clean
gate to ignore the emitter does not):

| declined kind | what it costs | recovery |
| --- | --- | --- |
| `Rvalue::BinaryOp(Cmp)` | 8 `fully_faithful_witness` rows (`signum` family + the G6 control), 4 production rows (`Ord::cmp` i16/i32/i64/i128) | model the three-way compare |
| `Rvalue::Cast` (source type == destination type) | 4 `fully_faithful_witness` rows (`core::str::{len,is_empty}`, two corpora) | do not decline an identity cast |
| `Rvalue::Cast` (pointer provenance / fat-pointer metadata) | the record + W2 iterator lanes (`into_iter`, `Iter::new`, `Iter::next`) | model the `NonNull`/thin-pointer chain |
| `Call::*::panic-freedom-unverified` | the Option/Result payload extractors — correctly, they PANIC | not a gap: the row is the point |

The runtime oracle measures no panic in any body in rows 1-3 (`sources/` +
`oracle_rows.txt`, plus the slice-iterator / `str` / `Ord::cmp` / `signum`
sweeps recorded in the session report), so those three are FAITHFULNESS
deferrals, not panic-freedom corrections. Row 4 is measured panicking.
