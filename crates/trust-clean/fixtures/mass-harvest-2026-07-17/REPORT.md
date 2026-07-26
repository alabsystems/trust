# mass-harvest-2026-07-17 — 10-family parallel sweep through the landed lanes

10 parallel harvesters (workflow wf_4a251e25): probe crate → TRUST_DUMP_MONO=1 dump →
ff-gate grade. **248 FULLY_FAITHFUL / 100 SHAPE_GAP** across 348 graded instances.

| family | FF | gap | headline |
|---|---|---|---|
| optres-widths | 100 | 0 | is_some/is_none/is_ok/is_err × ALL 12 widths + method-call wrappers — CLEAN SWEEP |
| unwrap-or-widths | 37 | 0 | payload lane fully width-generic; ref-fwd composes (method wrappers FF) |
| enum-preds | 25 | 2 | Ordering/ControlFlow/Poll + user 2-variant enums + wrappers |
| int-preds | 20 | 16 | signum/is_positive/is_negative × i8/i32/i64 + wrappers; abs = SAFETY_GAP (Neg overflow VC) |
| real-forwarders | 20 | 4 | REAL struct-method forwarders certify end-to-end (Config/Buf/State) |
| cmp-methods | 18 | 13 | method-call min/max + struct-field forms; clamp blocked on empty-body leaf |
| nonzero-conv | 13 | 13 | NonZero::get/new = CastKind::Transmute extractor gap; From-forwarder def_path spelling miss |
| char-ascii | 9 | 9 | one more range diamond FF; branchless case-mask + 4-way or-chain gaps |
| arith-guarded | 4 | 27 | wrapping/saturating/checked — the arithmetic-semantics frontier |
| slice-str-baseline | 2 | 16 | documents the PtrMetadata/W20 gap (W-LEN-ISEMPTY in flight) |

## The next-target list (from the gap diagnoses, smallest first)
1. K≠0 single-target SwitchInt (Bound::is_excluded/is_unbounded): recognizer treats
   single-target discriminant switch as zero-test only — generalize to `discr == K`.
2. From-forwarder def_path spelling: Call func `<u32 as From<u8>>::from` vs dump
   def_path `core::convert::num::<impl From<u8> for u32>::from` — certified-callees
   lookup miss (+6 free on fix).
3. Cast rvalue in forwarder body (`buf.cap as u32` before a certified Call) — one
   IntToInt Cast statement declines an otherwise-FF forwarder.
4. char::is_ascii call_requires re-discharge at forwarder site (plumbing).
5. Two-call chain composition (a.min(b).max(c); checked_add(..).is_some()) — the
   sequential-call spine (2 calls through an intermediate local).
6. call-then-project (overflowing_add().0): Tuple-typed Call dest + Field(0) return.
7. wrapping_mul: Mul not in the straight-line op set; wrapping_add/sub reach
   SAFETY_GAP (wrap semantics vs overflow VC — needs the wrapping tier).
8. saturating intrinsics (no MIR body): W-BITINTRIN arity-2 extension family.
9. branchless ascii case-mask (Cast(bool→u8)*32 then BitOr/BitXor).
10. 4-way range or-chain (is_ascii_punctuation).
11. NonZero Transmute (extractor: niche transmute-out = field read under invariant).
12. abs: Neg-overflow safety VC needs the i::MIN edge discharged.
13. PtrMetadata family (len/is_empty/first/get) — W-LEN-ISEMPTY + W20 in flight.
14. Ord::clamp / PartialOrd::lt empty extracted bodies (W-DEREF-CMP-LEAF, extractor).
