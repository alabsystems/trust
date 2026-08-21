# Mutator harvest — bytesize MONOMORPHIZED instances (2026-08-19)

The sibling of `../bytesize/` closing that fixture's recorded boundary: the
generic `AddAssign<T>`/`MulAssign<T>` bodies were honest unknowns because their
`Into::into` call was unresolved. This fixture carries the CONCRETE T=u64
instances plus the core conversion chain they call — the three-link
establishment chain `from → into → add_assign::<u64>`, in one directory so the
census's callees-first (Tarjan-SCC) ordering certifies each link before its
caller.

## Recipe (reproducible)

`probe.rs` (committed here, verbatim) instantiates the generic mutators
(`b += 512u64; b *= 2u64`) against the published bytesize-1.3.0 `src/lib.rs`
(the tarball recipe in `../bytesize/PROVENANCE.md`; the `#[path]` line points
at the unpacked tarball — adjust the path when regenerating):

```sh
TRUST_DUMP_MONO=1 LIBRARY_PATH=/opt/homebrew/lib \
  build/host/stage1/bin/trustc --edition 2018 --crate-type bin --crate-name main \
  -Ztrust-dump=mir:<outdir> -Ztrust-policy=advisory -o /tmp/probe.bin probe.rs
```

Dumped 2026-08-19 with the stage1 trustc carrying the LOCAL MONO INSTANCES
extractor extension (this unit, `trust_verify.rs`): the mono lane's blanket
`def.is_local()` exclusion is narrowed to admit CONTRACT-FREE local instances
that REQUIRE monomorphization — the shared contract guard preserves the
recorded spec-identity rationale, and non-generic local bodies stay excluded
(the ordinary extractor owns them). Before that change the probe dumped only
the generic bodies (`TyKind::Param` rhs) and this chain was undumpable.

## Roles

| dump | def_path | role |
|---|---|---|
| `trust-mir-a4eaccd5f17eb45d-*` | `<u64 as From<u64>>::from` | CHAIN LEAF — 1-block identity; certifies registry-free. |
| `trust-mir-e0abcb88d90d298d-*` | `<u64 as Into<u64>>::into` | CHAIN LINK — calls `from`; certifies once `from` is registered. Its synthesized width-bound precondition is partitioned out by `is_parameter_type_range_fact`, so its `CalleeFact.requires` is known-empty. |
| `trust-mir-f023ca840d79f55a-*` | `<ByteSize as AddAssign<u64>>::add_assign` | **POSITIVE** — the FS-CALL-RHS shape: bb0 `Into::into` call into a fresh temp, checked-Add spine with the call result as rhs, `.0` store. Certifies once `into` is registered (the establishment clause). |
| `trust-mir-3317a0241ba502e-*` | `<ByteSize as MulAssign<u64>>::mul_assign` | **POSITIVE** — identical shape with `Mul`. Certifies because the var*var unsigned mul VC carries an authenticated Or-range record. That conjunct was tried 2026-08-19, **RETRACTED 2026-08-20** (the mixed QF_BV + NIA query cost ay the refutation: an unguarded overflowing mul went from `Failed` with a counterexample to `Unknown`), and **RE-LANDED** the same day once `trust-router`'s disjoint-component refutation lane could refute such a query component-wise — measured capability-neutral both ways first. |

The concrete `<ByteSize as AddAssign>::add_assign` (ByteSize rhs) row the probe
outdir also contains is deliberately NOT curated here: it comes from the
ORDINARY extractor (a non-generic local body — the mono lane excludes it by
design), and it is the same body `../bytesize/` already carries under the
`lib::` def_path; a second copy would double-count the row.
