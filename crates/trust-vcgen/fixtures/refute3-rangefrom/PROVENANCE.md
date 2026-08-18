# The `RangeFrom` refutation — a genuine `core` iterator that never ends

Verbatim `-Ztrust-dump=mir` output, produced by the 2026-08-17 round-3
adversarial review and INDEPENDENTLY REPRODUCED here before anything was
believed: a fresh dump from the sources below differs from
`exploit.json` in `def_path` alone (`user1::boom` vs `user::boom`), every other
byte identical.

## The program

```rust
// aux_rf.rs — PLAIN SAFE RUST. No internal features, no attributes.
#![no_std]
pub mod vec {
    pub struct Vec<T> { pub k: u64, pub t: core::marker::PhantomData<T> }
    impl<'a, T> IntoIterator for &'a Vec<T> {
        type Item = u64;
        type IntoIter = core::ops::RangeFrom<u64>;          // the REAL `core`
        #[inline(never)]
        fn into_iter(self) -> core::ops::RangeFrom<u64> {
            core::ops::RangeFrom { start: 0u64 }
        }
    }
}

// consumer_rf.rs
#![no_std]
extern crate alloc;
extern crate std;      // the impersonator
#[inline(never)]
pub fn boom(v: &std::vec::Vec<u8>) -> alloc::vec::Vec<u64> { v.into_iter().collect() }
```

`RangeFrom::next` never returns `None`, so `boom` allocates without bound in
every execution.

## Commands, and the measurement (`stage2/bin/trustc`, `rustc 1.99.0-dev (0a3cd0152 2026-08-17)`)

```sh
T=build/aarch64-apple-darwin/stage2/bin/trustc
$T --edition 2021 --crate-type=rlib --crate-name std     -Ztrust-verify=off --out-dir A aux_rf.rs
$T --edition 2021 --crate-type=rlib --crate-name mycrate -Ztrust-verify=off --out-dir B aux_rf_my.rs
$T --edition 2021 --crate-type=lib -Ztrust-verify=on --extern std=A/libstd.rlib \
   --crate-name user -Ztrust-dump=mir:dA consumer_rf.rs
$T --edition 2021 --crate-type=lib -Ztrust-verify=on --extern mycrate=B/libmycrate.rlib \
   --crate-name user -Ztrust-dump=mir:dB consumer_rf_my.rs
```

| run | aux `--crate-name` | exit | diagnostic lines |
| --- | --- | --- | --- |
| `exploit.json` | `std` | **0** | **0** |
| `control.json` | `mycrate` | **1** | **49** |

`--extern` rather than `-L` is load-bearing for the exploit: with `-L` the real
sysroot `std` is also a candidate and the graph fails E0464 before verification
runs.

`*_dupgraph.json` are the SAME shape in an ordinary (non-`no_std`) graph, where
the real `std` IS loaded and the extractor's duplicate-crate-name rule is
therefore true. It made no difference: both stamp rules key on the CALLEE's own
defining crate, which here is the real `core`.

## Why it walked through every provenance authenticator

```text
callee   <&std::vec::Vec<u8> as core::iter::traits::collect::IntoIterator>::into_iter
local 1  Ref -> Adt { name: "std::vec::Vec" }            (the impersonator)
local 2  Adt { name: "core::ops::range::RangeFrom" }     (the REAL `core`)
```

The impersonator's crate name reaches the callee string only as the qualified
SELF TYPE of a real-`core` trait method, and the stamp is keyed on the callee's
DEFINING crate — so the string is unstamped and `producer_receiver_path` reads
`std::vec::Vec` off the forgery. The iterator's own type is genuine `core` and is
CORRECTLY unstamped. Both provenance halves read true, and they were right to.

Closed at the two places the claim actually lives: the value's boundedness
(`ty_is_unbounded_sysroot_iterator`) and the receiver OPERAND's type
(`producer_receiver_value_is_authenticated_sysroot`) — see
`../../src/generate/bounded_source_value_tests.rs`.
