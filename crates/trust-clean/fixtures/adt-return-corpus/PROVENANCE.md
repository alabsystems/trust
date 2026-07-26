# adt-return-corpus — provenance

Ten files, originally copied byte-for-byte (never hand-transcribed) from
`crates/trust-clean/fixtures/census-rung2-2026-07-07/cast/` — itself real
`TRUST_DUMP_MIR` output from the real, unmodified `cast` 0.3.0 crates.io
source. On 2026-07-18 they were authentically re-anchored from that same
source with the current extractor so the dumps carry first-class `VariantDef`
metadata for the outer `Result` and nested `Error` enums. The source digest is
pinned in `SOURCE.sha256`; `regenerate.sh` repeats the whole-crate extraction,
selects the ten functions by exact normalized def-path, and refuses to publish
legacy flattened enum dumps.

The re-anchor command was:

```sh
TRUSTC="$PWD/build/host/stage1/bin/trustc" \
  crates/trust-clean/fixtures/adt-return-corpus/regenerate.sh
```

That compiler identified itself as `rustc 1.99.0-nightly
(adae50183 2026-07-18) (trustc)`. A freshly built stage2 compiler is the
script default; stage1 was supplied explicitly for this re-anchor because it
was the current integration compiler. The source was
`~/.cargo/registry/src/**/cast-0.3.0/src/lib.rs`, compiled with `--edition
2018` in Trust dump-only/survey mode.

Isolated into their own small directory (rather than reusing the full
202-function `census-rung2-2026-07-07/cast/` corpus, most of which is
out-of-scope — the infallible `promotion!` widening casts already certified
in the 2026-07-07 census, the `Error`/`Debug`/`Display`/`Clone`/`Eq` trait
impls, and the 3-outcome `from_signed!`/float-dest shapes this increment does
not cover) so the ADT-return regression test (`adt_return_corpus.rs`) runs a
small, precise `prove_dump_dir` pass over EXACTLY the shape this gap closes:
a 2-arm guarded return whose arms each CONSTRUCT a `Result<$dst, Error>`
variant (`Rvalue::Aggregate(AggregateKind::Adt{variant,..}, ops)`) — the
Result/Option-ADT AGGREGATE RETURN shape (gap-queue #2,
`reports/honesty-and-ladder-2026-07-07.md`).

## The ten functions — the mission's "spot-check 10" — spanning both guarded-cast macro families and every source integer width

| file | macro family | guard shape | Err payload |
|---|---|---|---|
| `_64__<impl From<i16> for u16>__cast.json` | `half_promotion!` | `Lt(src, Const 0)` — a DIRECT literal guard bound | `Error::Underflow` (nullary, tag 3) |
| `_64__<impl From<i8> for u8>__cast.json` | `half_promotion!` | `Lt(src, Const 0)` | `Error::Underflow` |
| `_64__<impl From<i32> for u32>__cast.json` | `half_promotion!` | `Lt(src, Const 0)` | `Error::Underflow` |
| `_64__<impl From<i64> for u64>__cast.json` | `half_promotion!` | `Lt(src, Const 0)` | `Error::Underflow` |
| `_x128__<impl From<i128> for u128>__cast.json` | `half_promotion!` | `Lt(src, Const 0)` | `Error::Underflow` |
| `_64__<impl From<u16> for u8>__cast.json` | `from_unsigned!` | `Gt(src, _t)` where `_t := Cast(Constant(255), u16)` — a CONSTANT-FOLDABLE cast temp (`u8::MAX as u16`, not folded in the dumped MIR) | `Error::Overflow` (nullary, tag 2) |
| `_64__<impl From<u32> for i8>__cast.json` | `from_unsigned!` | same temp-cast-const guard shape, unsigned-to-signed dst | `Error::Overflow` |
| `_64__<impl From<u64> for i32>__cast.json` | `from_unsigned!` | same temp-cast-const guard shape, wider src/narrower signed dst | `Error::Overflow` |
| `_x128__<impl From<u128> for i32>__cast.json` | `from_unsigned!` | same temp-cast-const guard shape, 128-bit src | `Error::Overflow` |
| `_x128__<impl From<u128> for u8>__cast.json` | `from_unsigned!` | same temp-cast-const guard shape, 128-bit src, unsigned dst | `Error::Overflow` |

The `half_promotion!` family's guard bound is a literal `Constant` operand
directly; the `from_unsigned!` family's guard bound is a same-block
`Cast(Constant(c), ty)` temp (`sem_adt_guard_operand_of_mir`'s ADDITIVE
resolution — a scoped extension used ONLY by the ADT-return recognizer, never
the pre-existing scalar-return guard path). Both are real, distinct MIR
shapes the recognizer must handle; the 5+5 split proves the extension is
load-bearing (not incidental) across every source integer width the crate
ships (`i8`/`i16`/`i32`/`i64`/`i128`, `u16`/`u32`/`u64`/`u128`).

All ten measured `fully_faithful=1, via_trustir=1, kernel_rejected=0` through
the real production `prove_dump_dir` gate (see `tests/adt_return_corpus.rs`).

## Structural + source-level census (informational, not part of the regression assertion)

**Direct dump scan.** A Python scan of the full `census-rung2-2026-07-07/cast/`
dump set (202 real functions) found **58 real functions** matching the
recognized shape (a 4-block CFG: one `SwitchInt` guard block, two
`Aggregate`-constructing arm blocks, one bare `Return` block) whose guard
operands are resolvable — 22 `half_promotion!`-family (direct-const guard) +
36 `from_unsigned!`-family (temp-cast-const guard).

**Source-level macro-arrow count** (`cast-0.3.0/src/lib.rs`, exact `=>` arrow
count per macro per width module, independent cross-check): `mod _64` has 16
`half_promotion!` + 25 `from_unsigned!` = 41 in-scope-shaped impls; `mod
_x128` has 6 + 12 = 18. Total IN-SCOPE-SHAPED across the two width modules
this 64-bit host actually compiles/dumps: **59** (the 1-function gap versus
the direct-dump-scan's 58 is a single edge-case guard shape, immaterial to
either count's conclusion). `mod _32` (`cfg(target_pointer_width = "32")`)
never compiles on this host, so its impls never reach the dump at all.

The genuinely 3-outcome `from_signed!` shapes (`Err(if a {Underflow} else if
b {Overflow} else {return Ok(...)})`, 18+10=28 across `_64`+`_x128`) and the
float-comparison-guarded `from_float!`/`from_float_dst!` shapes (20+3+0+1=24)
are OUT OF SCOPE for this increment (a >2-arm guard tree / a non-`Int` guard
operand, respectively — both correctly DECLINE, pinned by
`sem_adt_return_shape_of_declines_three_arm_shape` and
`sem_adt_guard_operand_of_mir`'s Int-only resolution) — **111 total
reachable fallible impls** (`_64`+`_x128`, matching the mission's cited "110"
almost exactly), of which **59 (53%)** are this increment's in-scope shape
and **52 (47%)** need two clearly-scoped follow-up increments (nested/
3-outcome guards; float-comparison guards).

See `reports/honesty-and-ladder-2026-07-07.md` (queue item #2) and
`reports/flagship-crate-census-2026-07-06.md` §3 item 3 for the gap this
fixture closes.
