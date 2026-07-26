# leaf-call-corpus — provenance

Trust: field-read leaf (`arrayvec::ArrayVec::len`) + first real-crate call
composition (`ArrayVecImpl::len`). Census: `reports/call-shape-census-2026-07-03.md`
§5/§6 (frontier function #1 and #5).

Unlike `fixtures/call-spine-corpus` (a self-contained `SOURCE.rs` `trustc`
compiles directly), these THREE dumps are copied VERBATIM from a REAL,
UNMODIFIED external crate — `arrayvec` **0.7.7** from crates.io — because the
leaf shape (`(*self).0` field-read + `u32→u64` widening cast) is a real-crate
pattern, not a hand-written synthetic one. The dumps were produced by the
census work (`reports/mirsem-fallback-census-2026-07-02.md` §6's recipe) with
a prebuilt stage2 `trustc` against
`~/.cargo/registry/src/index.crates.io-*/arrayvec-0.7.7/src/lib.rs`
(`-Zcontract-checks=yes --crate-type lib`; this is the original historical
invocation, and the inherited exec-projection flag is now retired for
Trust-active compilations), and are copied here byte-for-byte
(mirrored from the still-live census scratchpad
`dump_arrayvec/arrayvec__ArrayVec__<T, CAP>__len.json` etc.) — **not**
hand-edited. `regenerate.sh` reproduces them from scratch given a built
`trustc` and the crates.io registry cache.

| fixture | `def_path` | role |
|---|---|---|
| `arrayvec_len.json` | `arrayvec::ArrayVec::<T, CAP>::len` | **THE LEAF.** Body: `_2 = (*_1).0; _0 = _2 as u64; return` — a field-read of `&self` (`self.len: u32`) + a widening `u32→u64` cast, scalar return. No preconditions/postconditions (unannotated). |
| `arrayvec_impl_len.json` | `<ArrayVec<T, CAP> as ArrayVecImpl>::len` | **THE FIRST REAL-CRATE CALL COMPOSITION.** Body: `_0 = arrayvec::ArrayVec::<T, CAP>::len(copy _1) -> bb1; bb1: return` — a thin dispatcher over the leaf, already recognized by the EXISTING sole-call return shape (`sem_call_return_of_mir`, from the call-spine increment); the only blocker was the callee not being certifiable, which the leaf closes. |
| `arrayvec_is_empty.json` | `arrayvec::ArrayVec::<T, CAP>::is_empty` | **NAMED RESIDUE, CLOSED — the CALL-THEN-PUREOP recognizer.** Body: `_2 = arrayvec::ArrayVec::<T, CAP>::len(copy _1) -> bb1; bb1: { _0 = (Move _2 == 0u64); return }`. Bool return. This is a CALL-THEN-COMPARE hybrid shape: the call's dest is a temp (`_2`), not `_0` directly, and `_0`'s sole write is a `BinaryOp(Eq, …)`, not a bare `Use` passthrough — structurally DIFFERENT from the sole-call-writes-`_0`-directly shape `sem_call_return_of_mir` recognizes (even after the Bool-dest/ret widening in that increment, which only widened the DIRECT-write case). A SIBLING recognizer, `sem_call_then_pureop_of_mir` (`mirsem.rs`), now admits this shape ADDITIVELY: the call writing a sole-written temp `_t`, followed by `_0`'s sole write being a pure op (arithmetic via the existing `SemBinOp`, or comparison via the existing `SemCmpOp`) that actually consumes `_t`. The kernel certificate reuses the SAME proven `callRefinesContract` transport lemma the bare call-return shape uses, applied at a WRAPPED predicate (`wrap(callResult) = Int.beq(callResult, 0)` here, encoded 0/1-on-Int via `Bool.rec`) — no new axiom. `is_empty` certifies on BOTH lanes (MirSem AND trust-ir, ported byte-for-byte into `trustir_call.rs`), so the corpus split is now `fully_faithful=3 \| via_trustir=3 \| mirsem_fallback=0`. SCOPE: the non-call operand must be a CONSTANT (this fixture's `0u64` — a param-valued other operand is a further, not-yet-closed residue on both lanes).

Re-dump with `regenerate.sh` (requires a built stage2 `trustc` — see the repo
root `CLAUDE.md` build section — and the `arrayvec` 0.7.7 source in the local
crates.io registry cache, e.g. via `cargo add arrayvec@=0.7.7` in a scratch
crate to populate `~/.cargo/registry/src/**/arrayvec-0.7.7/`).
