/*!
A module with low-level architecture dependent routines.

Upstream memchr fans this module out into `x86_64`, `aarch64` and `wasm32`
submodules holding hand-vectorised searches over raw pointers. None of that
exists here: this crate is architecture independent by construction, because a
verifying compiler cannot prove index arithmetic derived from `leading_zeros`
on a SIMD movemask, and an unprovable toolchain dependency is exactly what this
crate replaces. Everything therefore lives under [`all`].

No crate in the Trust dependency graph — or, at the time of writing, anywhere
in the registry — names `memchr::arch::*`, so the SIMD submodules are absent
rather than stubbed.
*/

pub mod all;
