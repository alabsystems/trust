# stdlib-leaf-num-2026-07-16 — provenance

> The dump flags were spelled `-Ztrust-dump-mir` / `-Ztrust-dump-only` when
> these bytes were produced; they are one `-Ztrust-dump=<what>:<dir>` option now.
> The recipe below is the current spelling, so it reproduces against today's
> compiler rather than the pinned one.

The **second stdlib leaf-family certification** (P1 #2 of the finishing map,
`reports/finishing-map-prove-all-of-rust-2026-07-14.md`), after
`stdlib-leaf-ascii-2026-07-16`. A core INTEGER-METHOD leaf family: the NUM
sign/predicate + bit-introspection methods on the primitive fixed-width integer
types. Full narrative + per-fn verdict table:
`reports/p1-leaf-harvest-num-2026-07-16.md`.

## CURRENT RESULT 2026-07-16 — W-BITINTRIN + W-CMP-DISCR CLOSED (24/24)

The original harvest below recorded **8/24**. Two independently gated lanes
have since closed all 16 original `SHAPE_GAP` rows. The pure, total, body-less
bit intrinsics `intrinsics::{ctpop,cttz}` are modeled as a first-class opaque,
total `call_result` (the uninterpreted-but-total honesty tier — no popcount
value theory and no new axiom, modulo 3). The signum lane recognizes the exact
`Cmp(self, 0) -> Discriminant(Ordering) -> signed recovery` lowering and checks
its three-way-sign witness in the kernel.

The bit-intrinsic classifier no longer trusts diagnostic DefPath text. The MIR
extractor stamps a non-source-spellable marker only after `TyCtxt` identifies
an exact allowlisted, body-less (`must_be_overridden`) compiler intrinsic; the
Clean recognizer requires that marker, the exact intrinsic name, and arity.
This prevents a source function named `intrinsics::ctpop` from entering the
lane. The marker is transport metadata, not a signature: a detached or edited
JSON file does not authenticate itself, so proof authority still requires the
compiler/session binding of the normal Trust evidence path.

The bit-intrinsic lane flips **12** rows to `FULLY_FAITHFUL`:

- `count_ones` ×4 and `trailing_zeros` ×4 — `_0 = ctpop/cttz(self); Return`,
  certified **via_mirsem** (the new `sem_intrinsic_call_return_of_mir`
  recognizer → the existing `call_return_adequacy_witness` kernel machinery).
- `is_power_of_two` ×4 — `count_ones(self) == 1`; once `count_ones` certifies
  as a callee, this composes and certifies **via_trustir** (call-then-compare).

The signum lane flips the remaining **4** rows. The authoritative aggregate
re-run (`census-2026-07-06`, whole 24-function corpus, callees-first) is
**`fully_faithful = 24`, `kernel_rejected = 0`, `declined = 0`, all 24
`inhabited`**. Live per-row verdicts are in `results.tsv`; the exact 17-control
oracle covers the original F panel, bit-intrinsic B panel, and signum G panel.

## Headline (the real honest number, AS OF THE ORIGINAL HARVEST — see UPDATE above)

- **8 / 24 FULLY_FAITHFUL (33%)**, `kernel_rejected = 0` on every row,
  `declined = 0` on every row.
- The 8 FF are **exactly the pure comparison sign-predicates**
  `is_positive` (`self > 0`) and `is_negative` (`self < 0`) on
  {i8,i16,i32,i64}, all via the production kernel-backed **mirsem** lane.
- The 16 declines are fail-closed `SHAPE_GAP` under-coverage (never a false
  PROVE, never a kernel rejection) mapping to **two newly-named, tractable
  sub-walls**:
  - **W-BITINTRIN** (12): `count_ones` (`intrinsics::ctpop`) and
    `trailing_zeros` (`intrinsics::cttz`) contribute 8 direct, opaque,
    body-less intrinsic rows. `is_power_of_two` contributes 4 separate
    call-spine rows (`self.count_ones() == 1`): their serialized bodies call
    `count_ones`, so they additionally require sound modular callee-summary
    composition (or a dedicated direct model). The intrinsic operations are
    pure/total/modelable and **distinct from W13 (opaque inline asm)**; the
    direct 8 are analogous to the just-landed `core::ptr` intrinsic models.
    The then-current per-body lane did not yet consume a certified callee body.
  - **W-CMP-DISCR** (4): `signum` = `three_way_compare(self,0) as Self`, which
    lowers to `Cmp(self,0)` followed by an `Ordering` discriminant read; the
    i16/i32/i64 dumps then cast that tag, while the i8 dump writes the
    discriminant directly to `_0`. The body is **fully present** (no opaque
    callee), but a future normalization must not assume the dump metadata is
    already the mathematical `-1/0/1`: the recorded i8 `Less` metadata is raw
    `255`, and the serialized type does not carry the faithful integer repr.
    The lane therefore remained fail-closed until it could signed-decode against
    an explicit destination representation.

### Original sub-family split

| sub-family | methods | FF | fraction |
|---|---|---|---|
| SIGNED (i8/i16/i32/i64) | is_positive, is_negative, signum | 8/12 | 67% |
| UNSIGNED (u8/u16/u32/u64) | is_power_of_two, count_ones, trailing_zeros | 0/12 | 0% |

**This was a genuinely different baseline from the ascii family (24/24).** The
ascii predicates were pure comparisons/range-diamonds and finished at 100%.
At harvest time the integer bit-introspection methods routed through unmodeled
compiler intrinsics, so only the comparison predicates certified. That negative
result named the two lanes now closed above.

## What is here

```
dumps/                 24 real TRUST_DUMP_MIR bodies of THIS repo's library/core
                       (the num sign/predicate + bit family), renamed from
                       hash -> sanitized def_path (:: -> __), with source paths
                       canonicalized to checkout-independent library/core paths.
results.tsv            per-fn verdict: FULLY_FAITHFUL(lane) / SHAPE_GAP(wall),
                       kernel_rejected, safety_obligations/discharged.
forgeries.tsv          exact FF-gate and census expectations for all 17
                       adversarial and positive controls.
forgeries/             17 fail-closed/positive probe bodies: F1..F6 exercise
                       the baseline lanes, B1..B5 the intrinsic lane, and
                       G1..G6 the signum lane. See "Fail-closed" below.
SOURCE/                the intent fixture crate (uses the 24 target methods at
                       concrete widths; compiles clean; dumps ONLY its own 24
                       wrappers — zero core bodies — reproducibly proving why we
                       compile library/core itself).
TOOLCHAIN.sha256       the dump-capable stage1 trustc launcher + rustc_driver
                       identities; live gate/census tools are rebuilt from HEAD.
SOURCE.sha256          exact source/workaround inputs checked before extraction.
ARTIFACTS.sha256       canonical dumps, controls, and result-table identities.
canonicalize_dump_paths.py
                       rejects/canonicalizes checkout-specific source paths.
int_log10-workaround.diff  the ONE surgical extraction workaround (identical to
                       the ascii harvest's — the unrelated int_log10 module).
regenerate.sh          checkout-relative, locked, atomic regeneration plus a
                       `--validate-only` live production regrade.
```

## Toolchain

`TOOLCHAIN.sha256` pins the aligned dump-capable stage1 compiler used for the
current extraction: `rustc 1.99.0-nightly (3f0eb9e6f 2026-07-16) (trustc)` on
`aarch64-apple-darwin`. It records both the 50 KiB launcher (`0d1a627d…`) and
the linked 494 MiB `librustc_driver-222b42be0a0fefe1.dylib`
(`bfad9516…`). Both identities matter: the launcher dynamically loads the
driver that contains the extractor, so a launcher-only checksum would not pin
the code that assigns compiler-authenticated intrinsic markers.

Full regeneration defaults to `build/host/stage1/bin/trustc` and fails closed
unless the version, host, launcher checksum, linked driver name, and driver
checksum all match. It requires the launcher's sole `LC_RPATH` to be
`@loader_path/../lib`, hashes that adjacent driver, and clears dynamic-loader
override variables for every compiler invocation. `TRUSTC` may point at a
relocated regular file/hardlink with the pinned driver beside it, but cannot
relax those identities. Publication validation does not reuse historical
verdict binaries: `regenerate.sh` builds `ff-gate-diagnose-2026-07-10` and
`census-2026-07-06` in release mode from the current checkout, then compares
every recorded machine field and every control. The current live result is
24/24 with `kernel_rejected = 0`; `results.tsv` records the exact current safety
obligation/discharge counts rather than relying on this narrative.

This pinned stage1 emits a leading `core::` local-crate qualifier in extracted
identity paths. The corpus predates that diagnostic qualification and records
crate-relative `num::...`, `intrinsics::...`, and `cmp::Ordering` identities.
Regeneration therefore strips exactly one leading `core::` only from the JSON
`def_path`, call `func`, and type/ADT `name` identity fields (including the
payload after the compiler-authenticated intrinsic marker). It does not rewrite
arbitrary string literals or source data. The recursive slicer must also scan
exactly the body count reported by extraction before selecting the 24 targets,
so a future dump-layout change cannot masquerade as an identity change.

## Extraction path (identical to the ascii harvest, and empirically re-confirmed)

1. **Why compile core itself, not a probe crate.** `SOURCE/` is the intent
   fixture. Compiling it with `-Ztrust-dump=mir:<dir>` dumps **only its own 24 wrapper
   bodies** (`pos_i8`, `ones_u16`, …) and **zero** `num::<impl …>` core bodies —
   re-verified this session. The MIR dump records LOCAL bodies only; core
   callees stay opaque `Call` terminators. So we compile `library/core` ITSELF.

2. **The int_log10 promotion cycle (why a patched copy).** The recorded
   dump-capable trustc, under any trust-dump/verify flag, forces a borrowck / `const {}`
   promotion cycle (E0391) on `num::imp::int_log10` and aborts before writing any
   dump. We dump a byte-for-byte COPY of `library/core` with ONE surgical change
   in the UNRELATED module `num/imp/int_log10.rs`: the two
   `assert_unchecked(result <= const { .. })` calls are removed
   (`int_log10-workaround.diff`). `assert_unchecked` is a pure optimizer hint;
   removing it does not change any function's result. **No certified body is
   touched** — the 24 num leaves live in `num/int_macros.rs` (signed) +
   `num/uint_macros.rs` (unsigned) and are byte-identical to HEAD library/core.

3. **The recorded end-of-run delayed-bug ICE is accepted narrowly.** The dump
   run emitted all 27,664 bodies before a `NonZero<T>::Metadata` normalization
   delayed bug. Regeneration accepts a nonzero exit only when both recorded
   diagnostic fragments are present, requires at least 27,000 dumps, requires
   the exact 24-target inventory, canonicalizes paths, and verifies every
   artifact hash before replacing the committed directory.

## Fail-closed (the acceptance path is not shape-only)

`kernel_rejected = 0` on every one of the 24 real rows and every control. The
baseline sign-predicate acceptance path is backed by the F panel below, whose
members are mutations of genuine `is_positive` i32 plus a positive control and
are run through the same gate and census:

| probe | mutation | ff-gate | must |
|---|---|---|---|
| F1 dangling_local | `Copy(_9)` — local does not exist | SHAPE_GAP, FF=false | decline ✓ |
| F2 type_lie_bool_from_use | `_0:Bool = Use(Int 0)` — a zero-risk Int rvalue into Bool return | SHAPE_GAP, FF=false | structural type rejection ✓ |
| F3 div_by_zero | `_0 = Div(self, 0)` — undischarged div VC | SHAPE_GAP, FF=false | decline ✓ |
| F4 opaque_call | compare replaced by `Call evil::opaque_oracle` | SHAPE_GAP, FF=false | decline ✓ |
| F5 unchecked_overflow_add | `_0 = Add(self, i32::MAX)` — undischarged overflow VC | **SAFETY_GAP** (sh=true, sl_sf=false), FF=false | decline ✓ |
| F6 const_true_control | `_0 = Use(const true)` — a genuinely faithful leaf | FULLY_FAITHFUL, FF=true | **certify** ✓ |

F2 isolates assignment typing from arithmetic safety: it has no overflow or
other safety obligation, so acceptance would be a pure type-confusion bug. The
production validator/assigned-rvalue gates reject it before either semantic
lane can witness a shape. F5 separately proves that a well-typed, recognized
shape with an undischarged overflow VC remains `SAFETY_GAP`; F6 is the positive
control. Together they distinguish structural typing, safety discharge, and a
genuine faithful acceptance instead of attributing F2's rejection to overflow.

### W-BITINTRIN forgery panel (the intrinsic acceptance path is fail-closed)

The pure-total intrinsic lane admits `count_ones`/`trailing_zeros` ONLY via the
STRICT pinned classifier + arity gate. A second panel (`forgeries/B*`, each a
mutation of the genuine `count_ones` u8 body; driven by
`tests/bitintrin_forgery_corpus.rs`) proves each near-miss DECLINES:

| probe | mutation | must |
|---|---|---|
| B1 fake_ctpop_defpath | exact source-spellable callee `intrinsics::ctpop::<u8>`, but no compiler marker | decline ✓ |
| B2 wrong_arity_ctpop | `ctpop(self, self)` — arity 2, not 1 | decline ✓ |
| B3 nontotal_cttz_nonzero | `intrinsics::cttz_nonzero` — PARTIAL (UB on 0) | decline ✓ |
| B4 foreign_ctpop | genuine `ctpop` but `is_foreign = true` | decline ✓ |
| B5 unmodeled_intrinsic_transmute | `intrinsics::transmute` — not a bit intrinsic | decline ✓ |

The positive control is the genuine, compiler-marked `count_ones` body itself,
which certifies a
whole-function witness that is **modulo 3** (the KERNEL accepted the opaque
`call_result` return — `genuine_bit_intrinsic_leaves_certify_modulo_3`), so
acceptance is a real kernel witness, never a shape-only promotion. B1 proves
that exact diagnostic text is insufficient. B3/B4 are the other sharp edges:
B3 has the exact call shape but a partial intrinsic (its UB precondition is
unmodeled), and B4 is genuine marked `ctpop` behind a foreign ABI. All three
decline before a body whose totality is not established can certify.

## Honesty notes

- The original 16 declines were fail-closed `SHAPE_GAP` under-coverage, never a
  false proof or kernel rejection. The current corpus is 24/24; all negative
  B/F/G controls still decline and both positive controls certify exactly as
  recorded in `forgeries.tsv`.
- All checked-in JSON source paths are canonical `library/core/...` paths; the
  original host-specific `/private/tmp/...` paths are rejected by regeneration.
- W-BITINTRIN and W-CMP-DISCR were **new** named sub-walls, neither in the
  enumerated W1–W20. W-BITINTRIN dominated the baseline (12/16 declines), but
  it contains two gates: direct intrinsic semantics for 8 rows and modular
  callee composition (or a direct model) for the 4 `is_power_of_two` rows.
- Relationship to `census-core-m5-2026-07-07`: that census measured much of this
  family at 0 FF with older lanes. The original fresh-dump harvest isolated the
  comparison sign predicates as its initial 8/24 frontier; the current lanes
  have since closed the two measured walls.

## Addendum 2026-07-16 — W-CMP-DISCR CLOSED (signum x4 flip)

The `W-CMP-DISCR` sub-wall is now **closed**. A narrow, fail-closed recognizer
normalization landed in `mirsem.rs` (`resolve_signum_ordering_sign` +
`resolve_signum_cast_rvalue`, new `SemRvalue::ArithBin` MirSem constructor). It
recognizes `signum`'s full lowering
`_2 := Cmp(self, 0)` → `_d := Discriminant(_2)` → `[_0 := Cast(_d, iN)]` and
normalizes it to the three-way sign rvalue `(self > 0) - (self < 0)`, then
kernel-checks that arithmetic witness modulo 3 by the existing Lemma-1B/1C
adequacy (a genuine kernel check of the Clean term against the vendored MirSem
semantics — **not** a shape-only promotion).

- **Standalone lane delta on the original baseline: 8/24 → 12/24.** The four
  `signum` ({i8,i16,i32,i64}) rows flip `SHAPE_GAP(W-CMP-DISCR)` → `FULLY_FAITHFUL /
  via_mirsem`; `kernel_rejected = 0`, `declined = 0` on every row. `results.tsv`
  updated. Composed with the independently landed W-BITINTRIN lane, the current
  corpus is **24/24**. `is_positive`/`is_negative` x8 and the sister
  `stdlib-leaf-ascii-2026-07-16` corpus remain fully faithful.
- **i8 vs i16/i32/i64.** `i8` signum has NO cast (`_0 := Discriminant(Cmp(self,
  0))` directly — the return IS the i8 sign-carrier); `i16`/`i32`/`i64` add a
  value-preserving sign-extend `_0 := Cast(_d:i8, iN)`. Both shapes certify.
- **Soundness — the vendored Ordering/Cmp check.** The recognizer VERIFIES the
  vendored `cmp::Ordering` representation from the dump: EXACTLY three variants
  `Less`/`Equal`/`Greater` whose discriminants, interpreted as signed at the
  sign-carrier width (`255`→`-1`, `0`→`0`, `1`→`1` at i8), ARE the sign encoding.
  Given `Cmp(self, 0)` yields `Less`/`Equal`/`Greater` per `self<0`/`=0`/`>0`,
  the tag read + sign-extend recovers `signum(self) = (self>0) - (self<0)`.

### Signum fail-closed forgery panel (`forgeries/G1..G6`)

Six `signum` probes (five adversarial mutations plus one positive control), each run
through the SAME gate + census: `kernel_rejected = 0` on all six.

| probe | mutation | ff-gate | must |
|---|---|---|---|
| G1 cmp_rhs_nonzero      | `Cmp(self, 5)` (non-zero rhs)                       | SHAPE_GAP, FF=false | decline ✓ |
| G2 wrong_disc_mapping   | `Ordering` discriminants NOT `-1`/`0`/`1`           | SHAPE_GAP, FF=false | decline ✓ |
| G3 non_ordering_enum    | non-`Ordering` enum (right variants/discs, wrong name) | SHAPE_GAP, FF=false | decline ✓ |
| G4 flipped_operands     | `Cmp(0, self)` (= `-signum`)                        | SHAPE_GAP, FF=false | decline ✓ |
| G5 unsigned_cast_dest   | cast to `u32` (the `-1` `Less` tag not recoverable) | SHAPE_GAP, FF=false | decline ✓ |
| G6 valid_control        | genuine i32 signum                                  | FULLY_FAITHFUL, FF=true | **certify** ✓ |

Every acceptance path is gated by the vendored-Ordering structural check plus
the kernel witness; every near-miss (non-zero rhs, wrong tag mapping, wrong enum,
flipped operands, unsigned recovery) DECLINES named at the recognizer, so no
false PROVE and no kernel rejection is ever minted. In-tree pins:
`mirsem.rs::real_signum_fixtures_certify_via_three_way_sign` and
`mirsem.rs::signum_forgeries_are_fail_closed`.
