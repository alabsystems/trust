# Trusted-root spoof, shape 5 — the ENDLESS iterator wearing `alloc::vec::` (2026-08-16)

Byte-for-byte `-Ztrust-dump=mir:<dir>` output of the shipped compiler
(`build/aarch64-apple-darwin/stage1/bin/trustc`, `rustc 1.99.0-dev (7eac555ef
2026-08-16)`). Nothing here was hand-written or hand-edited; the three files are
the dumps exactly as the extractor produced them.

## The aux crate (identical bytes for both consumer runs)

```rust
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

`Endless::next` NEVER returns `None`. The consumer is

```rust
extern crate <aux>;
#[inline(never)]
pub fn boom(v: &<aux>::vec::Vec<u8>) -> std::vec::Vec<u8> { v.iter().collect() }
```

so `boom` allocates without bound in every execution — AY's exact failure mode,
and the thing `generate_unbounded_allocation_vcs` exists to catch.

## `user_boom_impersonating_alloc.json` — the exploit

```sh
trustc --edition 2021 --crate-name alloc --crate-type rlib -Ztrust-verify=off \
       --out-dir aux aux_endless_alloc.rs
trustc --edition 2021 --crate-name user --crate-type lib --emit=metadata \
       -Ztrust-verify=on -Ztrust-dump=mir:<dir> \
       --extern alloc=aux/liballoc.rlib consumer_endless.rs
```

Measured result: **exit 0, no diagnostic of any kind, zero obligations.** The
call renders

```text
__trust_crate@1973d11b2baa21fa::alloc::vec::Vec::<u8>::iter::<__trust_args@9eb75f82a1f1d141819e81715e8e7e0e>
```

— i.e. the compiler's own duplicate-crate-name rule ALREADY stamped it as
unauthenticated (the real `alloc` is in the graph via `std`), and
`is_std_collection_iter_producer` read straight past the stamp because it tested
`callee.contains("alloc::vec::")`. This is reachable on unmodified `main`; it
does not depend on the spoof3 producer change.

## `user_boom_ordinary_crate_name.json` — the non-vacuity control

The same aux bytes compiled `--crate-name mycrate`, the same consumer with
`mycrate` in place of `alloc`. Measured result:

```text
note: Trust verification: 0 proved, 0 failed, 1 unknown, 0 timed out,
      1 runtime-checked out of 2 obligation(s)
  [unknown] ... obligation: unsupported MIR
      `UnboundedAllocation::Iterator::collect::count-not-derivable`
error: Trust Level 0 safety verification incomplete for `user::boom`
error: Trust strict verification failed for `user::boom`
```

Renaming one crate is the ENTIRE difference between two obligations and a build
error, and zero obligations and a clean compile.

## `stdctl_fine_real_std.json` — the precision control

```rust
#[inline(never)]
pub fn fine(v: &std::vec::Vec<u8>) -> std::vec::Vec<u8> { v.iter().copied().collect() }
```

compiled with an ordinary crate name against the real sysroot. The producer
renders `core::slice::<impl [u8]>::iter` — anchored root, no stamp — and the
collect is (correctly) waved through: zero obligations, clean compile. The fix
must not disturb this.
