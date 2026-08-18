# The `#![no_std]` sysroot impersonation — an UNSTAMPED `std` (2026-08-17)

Byte-for-byte `-Ztrust-dump=mir:<dir>` output of the shipped compiler
(`build/aarch64-apple-darwin/stage2/bin/trustc`,
`rustc 1.99.0-dev (0a3cd0152 2026-08-17)`). The four `.json` files are the dumps
exactly as the extractor produced them; nothing was hand-written or hand-edited.

## Why this shape exists

The 2026-08-16 fixture next door
(`trusted-root-spoof-endless-iter-2026-08-16`) relies on the compiler's
DUPLICATE-CRATE-NAME rule having already stamped the impersonator. This one is
the case where that rule does not fire at all:

> In a `#![no_std]` graph the real `std` is never injected, so a crate built
> `--crate-name std` is the **only** `std` in the crate graph. `local_has_same_name
> || another_external_has_same_name` is therefore **false**, and the callee is
> emitted **UNSTAMPED**.

A duplicate-name test is a UNIQUENESS test, not an authenticator. The producer
fix that closes this stamps on IDENTITY instead
(`trust_mir_extract::convert::impersonates_sysroot_crate`).

## The aux crate (identical bytes for both consumer runs)

```rust
#![no_std]
pub mod vec {
    pub struct Vec<T> { pub k: u64, pub t: core::marker::PhantomData<T> }
    pub struct Endless { pub i: u64 }
    impl Iterator for Endless {
        type Item = u8;
        #[inline(never)]
        fn next(&mut self) -> Option<u8> { self.i = self.i.wrapping_add(1); Some(0) }
    }
    impl<T> Vec<T> {
        #[inline(never)]
        pub fn iter(&self) -> Endless { Endless { i: 0 } }
    }
}
```

`Endless::next` NEVER returns `None`, so `boom` allocates without bound in every
execution. The collected container is a GENUINE `alloc::vec::Vec<u8>`, reached
through `extern crate alloc` — the forgery is only the SOURCE of the iterator.

## `user_boom_impersonating_std.json` — the exploit

```sh
trustc --edition 2021 --crate-name std --crate-type rlib -Ztrust-verify=off \
       --out-dir aux aux_endless_std.rs
trustc --edition 2021 --crate-name user --crate-type lib --emit=metadata \
       -Ztrust-verify=on -Ztrust-dump=mir:<dir> \
       --extern std=aux/libstd.rlib consumer_std.rs
```

with

```rust
#![no_std]
extern crate alloc;
extern crate std;
#[inline(never)]
pub fn boom(v: &std::vec::Vec<u8>) -> alloc::vec::Vec<u8> { v.iter().collect() }
```

MEASURED result: **exit 0, zero diagnostics of any kind, zero obligations.**

The two authenticators both see an unstamped sysroot root:

```text
callee   std::vec::Vec::<u8>::iter                  (UNSTAMPED, root `std::`)
local 2  Ty::Adt { name: "std::vec::Endless" }      (UNSTAMPED, root `std::`)
```

## `user_boom_ordinary_crate_name.json` — the non-vacuity control

Byte-identical aux source compiled `--crate-name mycrate`, with `mycrate` in
place of `std` in the consumer. MEASURED result: **exit 1, two errors**,

```text
note: Trust verification: 0 proved, 0 failed, 1 unknown, 0 timed out,
      1 runtime-checked out of 2 obligation(s)
  [unknown] ... obligation: unsupported MIR
      `UnboundedAllocation::Iterator::collect::count-not-derivable`
error: Trust Level 0 safety verification incomplete for `user::boom`
error: Trust strict verification failed for `user::boom`
```

Renaming ONE crate is the entire difference between a build error and a clean
compile.

## The `.into_iter()` shape — `*_into_iter.json`

Same aux crate, with `Vec`'s endless iterator reached through `IntoIterator`
instead of an inherent `iter`:

```rust
impl<'a, T> IntoIterator for &'a Vec<T> {
    type Item = u8;
    type IntoIter = Endless;
    #[inline(never)]
    fn into_iter(self) -> Endless { Endless { i: 0 } }
}
// consumer: pub fn boom(v: &std::vec::Vec<u8>) -> alloc::vec::Vec<u8> { v.into_iter().collect() }
```

MEASURED: `--crate-name std` -> **exit 0, zero diagnostics**;
`--crate-name mycrate` -> **exit 1, two errors**. The dumped producer is

```text
<&std::vec::Vec<u8> as core::iter::traits::collect::IntoIterator>::into_iter
```

whose `DefId` belongs to the REAL `core`, so the CALLEE stamp does not reach it
— the impersonator's name survives inside the rendered `<Self as Trait>` header.
This shape is closed by the `Ty::Adt` NAME stamp alone, which is why the second
half of the fix is not redundant. Pinned by
`only_the_type_name_stamp_closes_the_into_iter_shape`.

## The crate identities, read out of the compiler's own metadata

`trustc -Zls=all` on each artifact (`stable_crate_id`, decimal and the
`{:016x}` form the stamp uses):

| crate | name | StableCrateId | stamp hex |
| --- | --- | --- | --- |
| real `core` (sysroot) | `core` | 4547985219981811333 | `3f1db07618be1e85` |
| real `alloc` (sysroot) | `alloc` | 5335379498625211300 | `4a0b1362cd751ba4` |
| real `std` (sysroot) | `std` | 7398676898008484585 | `66ad617059af4ae9` |
| **the aux built `--crate-name std`** | `std` | **1127107163555717956** | **`0fa449fe5b896344`** |
| the aux built `--crate-name mycrate` | `mycrate` | 9510639299895369244 | `83fc940dc1221e1c` |

Same NAME, different `StableCrateId` — measured, not argued. That is the whole
input to the producer fix, and it is why the fix keys on identity.

## The post-fix producer rendering is DERIVED, and derived in the test source

No compiler carrying the producer fix exists yet (`x.py` was out of scope for
this work), so the stamped bundles are not dumps — they are the verbatim exploit
bundles with the producer's two edited renderers applied, by an explicit
substitution written out in
`trust-vcgen/src/generate/no_std_sysroot_impersonation_tests.rs`:

* `__trust_crate@0fa449fe5b896344::` prefixed to a callee whose DEFINING crate is
  the impersonator (`convert::direct_call_def_path`, rule 2). In the `.iter()`
  bundle that is exactly `std::vec::Vec::<u8>::iter`; in the `.into_iter()`
  bundle there is NO such callee, so the substitution list is empty there;
* the same prefix on the `Ty::Adt` names `std::vec::Endless` and `std::vec::Vec`
  (`lib::sysroot_authenticated_def_path_str`).

The stamp's hex is the compiler's own `StableCrateId` for that artifact, read
from the table above, in the `{:016x}` format
`trust_types::stamp_unauthenticated_crate_path` writes. Everything downstream of
the substitution — `generate_unbounded_allocation_vcs`, both authenticators — is
production code running on the real bundle.

NOT stamped, and deliberately so: any callee whose own `DefId` is the real
`core`'s, even when the impersonator's type is spelled inside its qualified
`<Self as Trait>` header — the `collect` sink in both bundles, and the whole
`into_iter` producer. That channel is named residual R1; it is closed by the
VALUE-side authenticator, which reads the local's `Ty::Adt` name rather than the
callee string.
