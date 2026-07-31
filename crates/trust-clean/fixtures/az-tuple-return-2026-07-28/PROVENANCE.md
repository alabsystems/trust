# az (Dst, bool) tuple-return 6-fn mono-family — 2026-07-28 (Track B)

The COMMITTED re-derivation of `reports/2026-07-28-corpus-intake-published-ladder.md`
§4.1 cause (b): the report's evidence for the tuple-return leaf shape sat in a
nonstandard session scratchpad (`ffgate/az-mono-family.stderr`); this fixture is the
standard-flow replacement — dumps + ff-gate TSV + per-fn `FullyFaithfulDiagnosis`,
committed bytes. Pinned by `tests/az_tuple_return_family.rs` (a RED pin: 6/6
SHAPE_GAP today; flipping it is the deliberate act of landing the tuple-return lane).

**MIXED AUTHORITY — read before promoting anything here.** Four of the six dumps are
certification-grade crate-dump rows (`-Ztrust-dump=mir-only:`). The TWO
`az::overflowing_cast::<Src, Dst>` forwarder rows are `TRUST_DUMP_MONO=1`
observational harvests (w16-mono doctrine: the mono hook emits no proof, changes no
verdict, grants no transport credit — `fixtures/w16-mono-harvest-2026-07-25/PROVENANCE.md`).
They are here so the family diagnosis runs WITH the delegation callees present,
attributing the SHAPE_GAP to the tuple-return shape (cause b) rather than W16
callee absence (cause a). They must never be counted in a certification scoreboard.

## Generation

Producer: prebuilt stage2 `build/aarch64-apple-darwin/stage2/bin/trustc`, stamp
`rustc 1.99.0-dev (df16f7c43 2026-07-28) (trustc)`. Repo HEAD at generation:
`c6642b41a64`; `git diff --stat df16f7c43af..c6642b41a64 -- crates/trust-types/src
crates/trust-clean/src crates/trust-vcgen/src` is EMPTY, so producer and harness
agree on the dump schema and prover source (fixtures/tests-only commits in between).

Crate dump (certification-grade lane; az 1.3.0 from the local registry cache,
unmodified, published edition 2024):

```bash
LIBRARY_PATH=/opt/homebrew/lib trustc --edition 2024 --crate-type lib --crate-name az \
  -Ztrust-dump=mir-only:<dir> -Ztrust-policy=advisory -o libaz.rlib \
  ~/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/az-1.3.0/src/lib.rs
# 2,397 unique def_paths (matches the intake report's n)
```

Mono harvest (observational lane; `probe.rs` in this directory — az's fns are all
`#[inline]`, so a plain call at -O is inlined OUT of the mono graph; the probe uses
fn-pointer REIFICATION to force the instances):

```bash
TRUST_DUMP_MONO=1 LIBRARY_PATH=/opt/homebrew/lib trustc probe.rs -O --crate-type bin \
  --edition 2024 --extern az=libaz.rlib -o probe \
  -Ztrust-dump=mir:<dir> -Ztrust-policy=advisory
```

(The w16 fixture's `-Ztrust-dump-mir=<dir> -Ztrust-verify-survey` spelling predates
the current flag surface; `-Ztrust-dump=mir:<dir> -Ztrust-policy=advisory` is the
working spelling at this tip. The impl-leaf JSONs emitted by the mono lane are
byte-identical to the crate-dump rows — verified by `cmp` on
`trust-mir-1039a6f5a547afc8-b58f9f46d1b6e944.json` from both lanes.)

Diagnosis (results/family.ff-gate.tsv + .stderr):

```bash
crates/target/debug/ff-gate-diagnose-2026-07-10 dumps/ > results/family.ff-gate.tsv \
  2> results/family.ff-gate.stderr
```

## The 6-fn family (u16→u8 and i32→i16, the complete delegation ladder)

| dump | def_path | role | lane |
|---|---|---|---|
| `…1039a6f5a547afc8…` | `az::int::<impl az::OverflowingCast<u8> for u16>::overflowing_cast` | LEAF: `_2=_1 as u8; _3=_2 as u16; _4=Ne(_1,_3); _0=(_2,_4)` | crate dump |
| `…2b1e85c146fedb6…` | `az::int::<impl az::OverflowingCast<i16> for i32>::overflowing_cast` | LEAF (signed twin) | crate dump |
| `…faf3ac8ce2dec79a…` | `az::overflowing_cast::<u16, u8>` | forwarder: sole tail-call to the leaf, tuple-typed `_0` | MONO (observational) |
| `…5cc005784bdf8d8b…` | `az::overflowing_cast::<i32, i16>` | forwarder (signed twin) | MONO (observational) |
| `…219b89c557aba942…` | `az::int::<impl az::WrappingCast<u8> for u16>::wrapping_cast` | caller: `_2=call(...); _0=_2.0` projection | crate dump |
| `…fb4edc06bf5337b5…` | `az::int::<impl az::WrappingCast<i16> for i32>::wrapping_cast` | caller (signed twin) | crate dump |

## Measured result (2026-07-28, HEAD c6642b41a64)

**6/6 SHAPE_GAP with the callees present** — every conjunct false on both lanes
(`via_ir_shape=false`, `via_mirsem_shape=false`; full `FullyFaithfulDiagnosis` in
`results/family.ff-gate.stderr`). This reproduces the intake report's §4.1(2) claim
byte-for-byte and confirms the binding constraint: even with the W16-missing
delegation callees supplied, nothing in the family certifies, because the
`(scalar, bool)` tuple return has no recognizer on either lane.

Decline sites, established by code reading at this tip (file:line):

| row | trust-ir lane dies at | MirSem lane dies at |
|---|---|---|
| LEAF | `prove.rs:7824` + `prove.rs:8092` (return-ty gate `Ty::Int\|Ty::Bool`); `prove.rs:8119-8126` (scalar place-type gate); `prove.rs:8287` (`Rvalue::Cast`/`Aggregate` unmatched); `adt_shapes.rs:902` (struct-return requires `Ty::Adt`) | `return_lift.rs:461` (`sem_return_of_mir` has NO `Rvalue::Aggregate` arm — falls to `_ => None`) |
| forwarder | `call_lift.rs:940` (call dest/`_0` scalar gate `local_is_int_or_bool`) | same site (shared extractor), + callee not in certified registry |
| `.0` caller | `call_lift.rs:940` (tuple-typed call dest); `return_lift.rs:321` (`Use(_t.0)` chases only `CheckedBinaryOp` temps) | same sites |

Yield, measured on the full az crate dump at this tip: **84 of 2,397** unique
def_paths have the EXACT straight-line tuple-return leaf shape (Goto/Return-only
CFG, all statements `Use`/`Cast`/`BinaryOp(Ne)`/`Aggregate(Tuple,[scalar,bool])`)
— 60 four-stmt narrow/widen-back/Ne leaves + 24 two-stmt `(cast, false)` leaves.
The remaining 168 scalar-pair-return rows carry branching (`||` short-circuit,
float rounding) and are later rungs. Design of record for the fix:
`reports/2026-07-28-az-tuple-return-track-b.md`.
