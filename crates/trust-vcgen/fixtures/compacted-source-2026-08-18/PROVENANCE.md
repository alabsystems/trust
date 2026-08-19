# The COMPACTED source — an infinite `collect` with the `Cycle` erased

Verbatim `-Ztrust-dump=mir:<dir>` output. Nothing in this directory was
hand-edited; `def_path`, the `__trust_args@…` disambiguators and the rendered
type trees are the compiler's own.

## Why this pair exists

`ty_is_unbounded_sysroot_iterator` is a DENY-LIST over rendered type names, and
it walks the field tree because the infinity is usually in a generic argument
(the neighbouring `unbounded-sysroot-iterator-2026-08-17/` fixture). Both halves
assume the field tree is THERE.

It is not always. `trust_mir_extract::ty_convert::compact_oversized_field`
replaces any field subtree over `MAX_DATATYPE_FIELD_NODES` (64) nodes with a
by-name `Ty::Datatype`, and an expanding same-ADT recursion becomes
`Ty::Unsupported`. Before 2026-08-18 both landed on the walk's `_ => false` arm,
which is a GRANT.

The aux writes

```rust
type IntoIter = core::iter::Fuse<
    core::iter::StepBy<core::iter::Skip<core::iter::Peekable<
        core::iter::Enumerate<core::iter::Cycle<core::ops::Range<u64>>>>>>>;
```

Every layer is genuine `core`, `Cycle` is on the deny-list by name, and the value
is genuinely infinite. The compiler renders the iterator local as

```text
Adt { name: "core::iter::adapters::fuse::Fuse",
      fields: [("iter", Datatype { name: "core::option::Option", variants: [] })] }
```

— the whole `StepBy<Skip<Peekable<Enumerate<Cycle<Range<u64>>>>>>` subtree is
gone, and the one name that survives (`core::option::Option`) is not, and could
never be, on a deny-list of unbounded iterators.

## How the forged receiver gets past the STRING side

The receiver must authenticate for the walk to reach its leaf grant at all, so
the aux is built `--crate-name std` into a `#![no_std]` graph. That alone is
stamped today (`impersonates_sysroot_crate`), which is why the aux also carries

```rust
#![feature(rustc_attrs)]
#[rustc_diagnostic_item = "HashMap"]
pub struct FakeAnchor(pub u64);
```

That is residual **R2** of the producer-side stamp, disclosed by name in
`impersonates_sysroot_crate`'s own doc comment: the identity anchors are
attributes, `HashMap`'s real owner is absent from a `#![no_std]` graph, so
`get_diagnostic_item(HashMap)` resolves INTO the aux and it authenticates as the
real `std`. Closing R2 is the producer's job, not this walk's. The fixture is
here because the VALUE side must not be the only thing standing between a forged
receiver and a deleted obligation — and before this fix it was not standing at
all.

MEASURED without the anchor forgery (same aux, no `#[rustc_diagnostic_item]`):
the receiver renders `__trust_crate@7d03ef4e1350df4b::std::vec::Vec`,
`producer_receiver_value_is_authenticated_sysroot` refuses, and the row is
present. The dump is not checked in; the point is only that the two gates are
independent.

## Commands (`build/aarch64-apple-darwin/stage1/bin/trustc`, `rustc 1.99.0-dev (a27d63627 2026-08-18)`)

`stage2/bin/` was empty during this measurement — an `x.py` run was in flight —
so the `stage1` compiler was used. It is built from the same tree
(`a27d63627`), which its own `--version` reports.

```sh
T=build/aarch64-apple-darwin/stage1/bin/trustc

# exploit: the aux is built under a sysroot crate name
$T --edition 2021 --crate-type=rlib --crate-name std     -Ztrust-verify=off --out-dir R2  aux_fuse_r2.rs
$T --edition 2021 --crate-type=lib --emit=metadata -Ztrust-verify=on \
   --extern std=R2/libstd.rlib --crate-name user -Ztrust-dump=mir:dR2 consumer_fuse.rs

# control: byte-identical aux, ordinary crate name
$T --edition 2021 --crate-type=rlib --crate-name mycrate -Ztrust-verify=off --out-dir R2C aux_fuse_r2.rs
$T --edition 2021 --crate-type=lib --emit=metadata -Ztrust-verify=on \
   --extern mycrate=R2C/libmycrate.rlib --crate-name user -Ztrust-dump=mir:dR2C consumer_fuse_my.rs
```

| file | source | aux `--crate-name` |
| --- | --- | --- |
| `compacted_cycle_impersonating_std.json` | `consumer_fuse.rs` | `std` |
| `compacted_cycle_ordinary_crate_name.json` | `consumer_fuse_my.rs` | `mycrate` |

## What was MEASURED, exactly

* Exit codes and diagnostics: exploit **exit 0 with ZERO diagnostic lines**;
  control **exit 1 with 49 diagnostic lines**, two of them naming
  `UnboundedAllocation`. The two programs differ only in the aux crate's name,
  and both allocate without bound in every execution.
* Rows from `generate_unbounded_allocation_vcs`, the production entry point:
  **exploit 0, control 1** before the 2026-08-18 fix; **1 and 1** after it.
  Pinned by `bounded_source_value_tests::the_compacted_source_is_refused_under_a_sysroot_iterator_root`.
