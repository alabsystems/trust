# Mutator harvest — `bytesize` 1.3.0 (2026-08-19)

The fixture-intake unit the W19/M3 report recorded as decision 1: real
`AddAssign`-style newtype mutators, harvested from a published crate. `bytesize`
was chosen because its concrete `AddAssign` body is the exact M3 checked-RMW
shape on a `u64` newtype — `self.0 += rhs.0` — with the rhs read STAGED through
a param-field temp, which is what the FS-RHS-FIELD walk extension (landed with
this fixture) admits.

## Recipe (reproducible)

Source: the published tarball, byte-exact —
`https://static.crates.io/crates/bytesize/bytesize-1.3.0.crate` (no deps at
default features; serde is optional and off).

```sh
TRUST_DUMP_MONO=1 LIBRARY_PATH=/opt/homebrew/lib \
  build/host/stage1/bin/trustc --edition 2018 --crate-type lib \
  -Ztrust-dump=mir:<outdir> -Ztrust-policy=advisory \
  -o /tmp/bytesize.rlib bytesize-1.3.0/src/lib.rs
```

Dumped 2026-08-19 with the stage1 trustc at superproject `4d60a7dad2` (the
transparent-unwrap extractor; dumps carry the `adt_kind` stamp). The whole-crate
dump yields 170 bodies; this fixture curates the THREE `*Assign` mutator bodies,
selected by def_path. The uncurated remainder measured ff 10 / fallback 0 at
harvest time (simple getters and constructors; the Display/FromStr machinery
stays unknown).

## Roles

| dump | def_path | role |
|---|---|---|
| `trust-mir-5f2146b8225bfdaa-*` | `<ByteSize as AddAssign>::add_assign` | **POSITIVE** — `self.0 += rhs.0`: staging `_3 := Copy(_2.0)`, `_4 := CheckedAdd((*_1).0, _3)`, overflow assert, `.0` store. Proves fully faithful via trust-ir with rhs `Index(Var(rhs), Const(0))` (the opaque `idxElem` reading). |
| `trust-mir-3544e6db7e153288-*` | `<ByteSize as AddAssign<T>>::add_assign` | BOUNDARY — the generic body (`rhs.into() as u64`): an unresolved `Into::into` call; stays an honest unknown until a callee-established composition exists for it. |
| `trust-mir-4f9d969f8043efed-*` | `<ByteSize as MulAssign<T>>::mul_assign` | BOUNDARY — same class, `Mul` spine behind the same unresolved call. |

## What the walk extension does NOT claim

The staged read denotes `idxElem(param, field)` — distinct fields of one param
get distinct denotations (denoting them as the bare param `Var` would forge an
equality between different fields; the mint pin
`trust_ir_staged_param_field_rmw_mints_and_certifies` locks the denotation).
The rhs param must be a by-value struct with the `adt_kind: Struct` stamp, no
variants, and EVERY field scalar; the staging temp is single-assignment with
the M1 dead_at marker discipline. WRAP-vs-INT is unchanged: only the checked
spine with its own overflow assert mints, per the FS family's standing record.
