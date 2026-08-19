# The COMPOSED source — `core`'s `Map` over somebody else's iterator

Verbatim `-Ztrust-dump=mir:<dir>` output. Nothing in this directory was
hand-edited.

## Why this pair exists

The two value-side conjuncts of the bounded-source walk ask different questions
and, on this shape, both answer "fine":

* `ty_is_authenticated_std_iterator` is a ROOT test, deliberately (its doc says
  so: a closed list of std iterator ADTs would have to be maintained against
  every std release). It reads `core::iter::adapters::map::Map` and authenticates.
* `ty_is_unbounded_sysroot_iterator` is a deny-list of SYSROOT names. The thing
  that yields forever here is `endcrate::Endless`, which is not a sysroot name
  and never will be, so there is nothing for the list to match.

The aux writes

```rust
type IntoIter = core::iter::Map<endcrate::Endless, fn(u64) -> u64>;
```

`endcrate::Endless::next` never returns `None`. The compiler renders the iterator
local as

```text
Adt { name: "core::iter::adapters::map::Map",
      fields: [("iter", Adt { name: "endcrate::Endless", fields: [("i", u64)] }),
               ("f",    FnPtr { .. })] }
```

The answer is in the bundle — the adapted source is right there, and it belongs
to no authenticated sysroot crate.

## WHAT THIS FIXTURE DOES NOT COVER, and the walk must not be credited with it

The endless iterator is defined in an ORDINARY third crate (`endcrate`), and that
is load-bearing, not incidental. Had the impersonating aux defined `Endless`
itself, the field would render `std::vec::Endless`, whose root authenticates,
and NO name test could distinguish it from a real std iterator. Separating those
two is the producer stamp's job
(`trust_mir_extract::convert::impersonates_sysroot_crate`), not this walk's.

## How the forged receiver gets past the STRING side

Same as the neighbouring `compacted-source-2026-08-18/`: the aux is built
`--crate-name std` and carries a `#[rustc_diagnostic_item = "HashMap"]` anchor,
which is residual R2 of the producer-side stamp, disclosed by name in
`impersonates_sysroot_crate`'s own doc comment.

## Commands (`build/aarch64-apple-darwin/stage1/bin/trustc`, `rustc 1.99.0-dev (a27d63627 2026-08-18)`)

`stage2/bin/` was empty during this measurement (an `x.py` run was in flight), so
the `stage1` compiler was used; it is built from the same tree and says so in its
own `--version`.

```sh
T=build/aarch64-apple-darwin/stage1/bin/trustc

$T --edition 2021 --crate-type=rlib --crate-name endcrate -Ztrust-verify=off --out-dir E aux_endless.rs

# exploit: the collection's crate is built under a sysroot crate name
$T --edition 2021 --crate-type=rlib --crate-name std -Ztrust-verify=off \
   --extern endcrate=E/libendcrate.rlib --out-dir MU aux_mapuser.rs
$T --edition 2021 --crate-type=lib --emit=metadata -Ztrust-verify=on -L E \
   --extern std=MU/libstd.rlib --crate-name user -Ztrust-dump=mir:dMU consumer_mapuser.rs

# control: byte-identical aux, ordinary crate name
$T --edition 2021 --crate-type=rlib --crate-name mycrate -Ztrust-verify=off -L E --out-dir MUC aux_mapuser.rs
$T --edition 2021 --crate-type=lib --emit=metadata -Ztrust-verify=on -L E \
   --extern mycrate=MUC/libmycrate.rlib --crate-name user -Ztrust-dump=mir:dMUC consumer_mapuser_my.rs
```

| file | source | collection aux `--crate-name` |
| --- | --- | --- |
| `map_over_user_iterator_impersonating_std.json` | `consumer_mapuser.rs` | `std` |
| `map_over_user_iterator_ordinary_crate_name.json` | `consumer_mapuser_my.rs` | `mycrate` |

## `chain_over_user_iterator_*.json` — the source one level down, inside `Option`

The same defect with `core`'s own `Option` in the way. `aux_chainuser.rs` writes

```rust
type IntoIter = core::iter::Chain<endcrate::Endless, core::option::IntoIter<u64>>;
```

and `Chain` holds each side in an `Option`, so the compiler renders

```text
Adt { name: "core::iter::adapters::chain::Chain",
      fields: [("a", Adt { name: "core::option::Option",
                           fields: [("__tag", i64), ("__v1_0", Adt { name: "endcrate::Endless", .. })],
                           variants: [None, Some[("0", Adt { name: "endcrate::Endless", .. })]] }), … ] }
```

MEASURED: with the refusal stopping at the first non-iterator sysroot ADT this
still granted — exploit **0 rows**, control **1**, exploit exit 1 with 46
diagnostic lines and `UnboundedAllocation` appearing **0** times against the
control's **2**. `Option` is therefore transparent to
`adaptor_source_field_unestablished`, and nothing else is; measured cost of that
one exception over 3 115 bundles: **zero** — not one row and not one grant moved.

Built exactly like the `map_over_user_iterator_*` pair, substituting
`aux_chainuser.rs` / `consumer_chain.rs` / `consumer_chain_my.rs`.

## `cloned_slice_of_user_elements_ok.json` — the PRECISION control

`bounded_user_elem.rs`, an ordinary crate with no forgery of any kind:

```rust
#[derive(Clone)] pub struct Item { pub a: u64, pub b: u64 }
pub fn ok(v: &[Item]) -> Vec<Item> { v.iter().cloned().collect() }
```

```sh
$T --edition 2021 --crate-type=lib --emit=metadata -Ztrust-verify=on \
   --crate-name mycrate -Ztrust-dump=mir:dBU bounded_user_elem.rs   # exit 0, no diagnostics
```

This is a genuinely bounded collect that MUST keep its grant, and it is the
tight control for the refusal above: the iterator local renders

```text
Adt { name: "core::iter::adapters::cloned::Cloned",
      fields: [("it", Adt { name: "core::slice::iter::Iter",
                            fields: [("ptr", Adt { name: "core::ptr::non_null::NonNull",
                                                   fields: [("pointer", RawPtr { pointee:
                                                              Adt { name: "mycrate::Item", .. } })] }), .. ] })] }
```

— a `core::iter::` adaptor with `mycrate::Item`, an unauthenticated ADT, inside
it. The difference from the exploit is WHERE: `mycrate::Item` is the ELEMENT of
a sysroot iterator, not the SOURCE of a sysroot adaptor. That is why
`adaptor_source_field_unestablished` stops at the first non-iterator sysroot ADT
(`core::slice::iter::Iter`) instead of walking the whole tree.

MEASURED cost of removing that stop: 8 grant sites across the 2 575 checked-in
bundles fall to 4 and the row total rises 23 → 27, losing four REAL-code grants
(`Map<slice::Iter<'_, level::Level>, closure>` twice,
`Cloned<slice::Iter<'_, (name::Name, level::Level)>>`,
`Map<slice::Iter<'_, S>, closure>`).

## What was MEASURED, exactly

* Exit codes: exploit **1** (46 diagnostic lines), control **1** (49). Like the
  `Map<RangeFrom<u64>, …>` pair next door, the exploit is not exit 0 — the
  `fn(u64) -> u64` call carries an absent-callee panic-freedom obligation that
  fails on its own account. **The unbounded-allocation obligation is deleted**,
  and that is the defect: `UnboundedAllocation` appears **0** times in the
  exploit's diagnostics and **2** times in the control's.
* Rows from `generate_unbounded_allocation_vcs`, the production entry point:
  **exploit 0, control 1** before the 2026-08-18 fix; **1 and 1** after it.
  Pinned by `bounded_source_value_tests::a_sysroot_adaptor_over_an_unauthenticated_source_is_refused`.
