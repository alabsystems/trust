# The qualified `.into_iter()` producer, and what `..=` really renders as (2026-08-17)

Byte-for-byte `-Ztrust-dump=mir:<dir>` output of the shipped compiler
(`build/aarch64-apple-darwin/stage2/bin/trustc`, `rustc 1.99.0-dev (0a3cd0152
2026-08-17)` — the base commit of this patch). Nothing here was hand-written or
hand-edited; the four files are the dumps exactly as the extractor produced
them, renamed only from their content-hash file names to their function names.

## Source (one file, four functions)

```rust
#[inline(never)]
pub fn vec_into_iter(v: std::vec::Vec<u8>) -> std::vec::Vec<u8> { v.into_iter().collect() }
#[inline(never)]
pub fn inclusive_small() -> std::vec::Vec<i32> { (0..=5).collect() }
#[inline(never)]
pub fn inclusive_at_ceiling() -> std::vec::Vec<i32> { (0..=((1i32<<28)-1)).collect() }
#[inline(never)]
pub fn exclusive_at_ceiling() -> std::vec::Vec<i32> { (0..(1i32<<28)).collect() }
```

```sh
trustc --edition 2021 --crate-name shapes --crate-type lib --emit=metadata \
       -Ztrust-verify=on -Ztrust-dump=mir:<dir> shapes.rs
```

## What the dumps establish

### 1. `.into_iter()` is ALWAYS the qualified spelling (`vec_into_iter.json`)

```text
<alloc::vec::Vec<u8> as core::iter::traits::collect::IntoIterator>::into_iter
  -> local 2: alloc::vec::into_iter::IntoIter<u8>
<alloc::vec::into_iter::IntoIter<u8> as core::iter::traits::iterator::Iterator>
  ::collect::<alloc::vec::Vec<u8>>::<__trust_elem_bytes@32>
```

A qualified spelling starts with `<`, so a producer authenticator that anchors
the RAW callee string against `core::`/`alloc::`/`std::` refuses it. Replaying
this exact file through `generate_unbounded_allocation_vcs`:

| tree | rows |
| --- | --- |
| `main` (`0a3cd01520`) | 0 |
| the raw-anchor form of this fix | **1** `UnsupportedMir{count-not-derivable}` |
| this patch | 0 |

That is the over-decline this fixture exists to pin, and `v.into_iter()
.collect()` is the most ordinary bounded collect in the language.

### 2. `a..=b` does NOT render as a `RangeInclusive` AGGREGATE at this stage

`inclusive_small.json` and `inclusive_at_ceiling.json` both render

```text
core::ops::range::RangeInclusive::<i32>::new(const 0_i32, <end>)
  -> local 1: core::ops::range::RangeInclusive
<core::ops::range::RangeInclusive<i32> as core::iter::traits::iterator::Iterator>
  ::collect::<alloc::vec::Vec<i32>>::<__trust_elem_bytes@12>
```

— a CALL, not an `Rvalue::Aggregate`. The exclusive sibling
(`exclusive_at_ceiling.json`) DOES render an aggregate:

```text
Aggregate(Adt { name: "core::ops::range::Range", args: "core::ops::range::Range<i32>" },
          [Constant(Int(0)), Move(_2)])
```

because `a..b` is a struct literal while `a..=b` is `RangeInclusive::new`. The
`RangeInclusive` AGGREGATE shape is what rustc produces once `new` is inlined
(measured under `-O`), which is the shape `iter_collect_count`'s aggregate arm
must get right — but it is NOT the shape source-level `..=` takes at the
drops-elaborated stage this lane reads. All three trees report 1 row for both
inclusive functions; the inclusive family was never a zero-row case here.

`exclusive_at_ceiling` is a reported Level-0 violation in the shipped compiler
run; `inclusive_at_ceiling` — the same 2^28-element allocation — is an
unproved-coverage-gap row, not a proof. Both are unchanged by this patch.

## Amendment 2026-10-06 — the destination-size token

The dumps were taken when the extractor's `__trust_elem_bytes@N` token on a
`collect` did not yet carry the destination element's layout size (`@32` above for
a `Vec<u8>` destination). The current extractor emits `@1` for the same program
(measured on stage1, 2026-10-06: `v.into_iter().collect::<Vec<u8>>()` dumps
`…::collect::<alloc::vec::Vec<u8>>::<__trust_elem_bytes@1>`). Since D12 option (a)
the bounded-source grant compares that token with the source's item bound, so every
`Vec<u8>` collect sink in this directory, `no-std-sysroot-impersonation-2026-08-17`
and `trusted-root-spoof-endless-iter-2026-08-16` was rewritten to `@1`. Nothing else
in the bundles was touched.
