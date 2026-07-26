# stdlib-leaf-bitmethods-2026-07-16 — provenance

This authenticated corpus contains the 32 integer bit-method leaves
`{count_zeros, leading_zeros, swap_bytes, reverse_bits}` for
`{u8,u16,u32,u64,i8,i16,i32,i64}`.

## Current integrated revalidation (2026-07-17)

All **32/32** bodies are `FULLY_FAITHFUL` through MirSem, with a kernel witness
that is modulo 3. No row is accepted by a shape-only path, no row is declined,
and `kernel_rejected = 0` throughout. The three composed lanes are:

| sub-family | result | authority boundary |
|---|---:|---|
| unsigned `leading_zeros`/`swap_bytes`/`reverse_bits` | 12/12 | authenticated, allowlisted compiler intrinsics |
| signed and unsigned `count_zeros` | 8/8 | W-PREOP: exact `Not(self)` into pinned `count_ones` |
| signed `leading_zeros`/`swap_bytes`/`reverse_bits` | 12/12 | W-CAST: same-width opposite-signedness delegate casts |
| **whole family** | **32/32** | kernel-checked composition |

The original extraction measured 12/32. W-PREOP closed eight `count_zeros`
rows and W-CAST closed twelve signed-delegate rows. That baseline is retained
in git history; `results.tsv` records the current integrated result.

## Sharp gates

The direct leaves carry `@trust-rustc-intrinsic::` only when the compiler has
confirmed an exact allowlisted, body-less intrinsic. Clean requires that marker,
the exact intrinsic name, unary arity, and a non-foreign call. Marker text in a
detached JSON file is evidence, not independent release authority; release
authority comes from the authenticated compiler transport and session.

W-PREOP admits only an exact, sole-writer `UnaryOp(Not, value)` argument to the
pinned integer `num::<impl {integer}>::count_ones` method. It models `!x` as
`x xor -1`, reusing the existing integer xor semantics. Wrong callees, a
different method, binary operations, unresolved values, and multiply-written
temporaries all decline.

W-CAST admits only same-width integer casts that reverse signedness around a
certified unsigned primary. Width-changing, same-signedness, self-recursive,
or uncertified delegates decline. This width gate is essential because `ctlz`,
`bswap`, and `bitreverse` are width-sensitive.

## Fail-closed controls

`forgeries/` contains two six-case panels:

- F1–F6 cover the intrinsic marker, total-function allowlist, arity, foreign ABI,
  and one genuine positive control.
- G1–G6 cover the W-PREOP callee, operation, value resolution, sole-writer gate,
  and one genuine positive control.

The W-CAST panel is exercised by
`tests/w_cast_arg_forgery_corpus.rs`, including different-width casts into an
otherwise certified primary. `tests/bitmethods_intrinsic_corpus.rs` certifies
the complete 32-body corpus in callee-first order and requires a modulo-3
certificate for every body.

## Corpus inventory

```
dumps/                 32 compiler-extracted and canonicalized MIR bodies
forgeries/             12 deterministic fail-closed/positive controls
results.tsv            current per-body verdict, lane, kernel and safety fields
forgeries.tsv          expected machine fields for both control panels
SOURCE/                 source-intent fixture
SOURCE.sha256           exact source and workaround inputs
TOOLCHAIN.sha256        exact trustc launcher, driver, host and extraction pins
ARTIFACTS.sha256        exact dump/control/table inventory and hashes
canonicalize_dump_paths.py
                        constrained path canonicalization
int_log10-workaround.diff
                        extraction-only removal of unrelated optimizer hints
regenerate.sh           fail-closed validation and transactional regeneration
```

## Extraction and reproducibility boundary

The fixture compiles `library/core` itself because a probe crate dumps only its
own opaque wrappers. The extraction copy removes two unrelated
`assert_unchecked(... const { ... })` optimizer hints from `int_log10`; none of
the 32 certified bodies is modified. The pinned compiler emits the complete
recorded dump inventory before one exact, admitted delayed-bug diagnostic. The
regeneration script checks the toolchain and driver hashes, host, loader path,
diagnostic signature, recursive inventory, source hashes, canonical paths,
manifest coverage, live gate/census schemas, every result field, and every
control field before publication.

`ARTIFACTS.sha256` is an exact inventory rather than a partial checksum list:
any added, removed, duplicated, or changed dump, control, or result table makes
validation fail.
