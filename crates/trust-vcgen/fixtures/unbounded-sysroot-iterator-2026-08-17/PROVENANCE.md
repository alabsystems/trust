# `Map<RangeFrom<u64>, fn(u64) -> u64>` — infinity hidden in a generic argument

Verbatim `-Ztrust-dump=mir` output. Nothing in this directory was hand-edited;
`def_path` and the `__trust_args@…` disambiguators are the compiler's own.

## Why this pair exists

The 2026-08-17 round-3 refutation (`../refute3-rangefrom/`) showed that an
impersonating crate defeats every PROVENANCE authenticator by handing out a
genuine sysroot iterator that never ends —
`type IntoIter = core::ops::RangeFrom<u64>`. The repair refuses the endless
sysroot iterator ADTs by name.

This pair is the shape a name-only refusal would still miss. The aux writes

```rust
type IntoIter = core::iter::Map<core::ops::RangeFrom<u64>, fn(u64) -> u64>;
```

`core::iter::adapters::map::Map` is `core`-rooted, correctly unstamped, and reads
as an ordinary bounded adaptor; `trust_vcgen`'s generic stripping deletes exactly
the type argument that carries the infinity. The compiler's rendering of the
iterator local nevertheless contains the answer, because `Map`'s `iter` FIELD is
the `RangeFrom` — which is why `ty_is_unbounded_sysroot_iterator` walks the
rendered field tree and not only the name.

## Commands (`stage2/bin/trustc`, `rustc 1.99.0-dev (0a3cd0152 2026-08-17)`)

```sh
T=build/aarch64-apple-darwin/stage2/bin/trustc

# exploit: the aux is built under a sysroot crate name
$T --edition 2021 --crate-type=rlib --crate-name std     -Ztrust-verify=off --out-dir M  aux_map.rs
$T --edition 2021 --crate-type=lib  -Ztrust-verify=on --extern std=M/libstd.rlib \
   --crate-name user -Ztrust-dump=mir:dM  consumer_map.rs

# control: byte-identical aux, ordinary crate name
$T --edition 2021 --crate-type=rlib --crate-name mycrate -Ztrust-verify=off --out-dir MC aux_map.rs
$T --edition 2021 --crate-type=lib  -Ztrust-verify=on --extern mycrate=MC/libmycrate.rlib \
   --crate-name user -Ztrust-dump=mir:dMC consumer_map_my.rs
```

| file | source | aux `--crate-name` |
| --- | --- | --- |
| `map_over_rangefrom_impersonating_std.json` | `consumer_map.rs` | `std` |
| `map_over_rangefrom_ordinary_crate_name.json` | `consumer_map_my.rs` | `mycrate` |

## What was MEASURED, exactly

* Exit codes: exploit **1** (46 diagnostic lines), control **1** (49). Unlike the
  `RangeFrom` pair, the exploit is NOT exit 0 — the `fn(u64) -> u64` call adds an
  absent-callee panic-freedom obligation that fails on its own account. **The
  unbounded-allocation obligation is still deleted**, and that is the defect: the
  row differential, not the exit code, is what this fixture is about.
* Rows from `generate_unbounded_allocation_vcs`, the production entry point:
  round 3 grants the exploit (0 rows) and gates the control (1 row); round 4
  gates both. Pinned by
  `bounded_source_value_tests::the_map_over_rangefrom_bundles_are_gated_on_both_sides_now`.
* The iterator local renders as
  `Adt { name: "core::iter::adapters::map::Map", fields: [("iter", Adt { name:
  "core::ops::range::RangeFrom", … }), ("f", …)] }` — the name carries no generic
  arguments, the field does.
