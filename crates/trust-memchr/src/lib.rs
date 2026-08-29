/*!
Routines for string search primitives: 1, 2 or 3 byte search, and single
substring search.

This is Trust's first-party replacement for the `memchr` crate. It presents the
same public API, with the same semantics, and is wired in through
`[patch.crates-io]` so that every dependent in the toolchain — regex,
aho-corasick, bstr, object, serde_json, rustc_lexer, … — resolves to it without
source changes.

# Why it exists

Trust is a verifying compiler, and it bootstraps through its own dependency
graph. Every external crate in that graph is code the toolchain cannot prove and
cannot fix. Upstream memchr is hand-vectorised (SSE2/AVX2/NEON/simd128) over raw
pointers, and its index arithmetic is derived from movemask bit counts —
`16 - (mask.leading_zeros() >> 2) - 1` and friends — which a verifier models
opaquely and therefore cannot show is in bounds. It was the immediate blocker to
`./x.py build --stage 2`.

# What is different from upstream

* **Pure safe scalar code.** `#![no_std]` and `#![forbid(unsafe_code)]`, with no
  SIMD, no target-specific intrinsics, and no raw pointers anywhere. Consequently
  `memchr::arch` has only its `all` submodule, and the `*_raw` pointer-range
  entry points do not exist. Nothing outside memchr itself has ever named them.
* **Substring search is naive rather than Two-Way**, so `memmem` is
  `O(haystack * needle)` in the worst case where upstream guarantees
  `O(haystack + needle)`. This is a speed regression, never a result
  difference; closing it is a separate, separately-verified step. Correctness
  first.
* **Prefilters are absent.** [`memmem::Prefilter`] and
  [`arch::all::packedpair::HeuristicFrequencyRank`] are still accepted so
  existing callers compile, and are documented as having no effect.

Everything a caller can observe about *which offsets are reported* — including
empty-needle behavior, iterator laziness and fusion, and the overlap rules of
the reverse iterators — is identical to upstream, and is checked against
upstream by a differential test corpus.

# Example: using `memchr`

```
use memchr::memchr;

let haystack = b"foo bar baz quuz";
assert_eq!(Some(10), memchr(b'z', haystack));
```

# Example: matching one of three possible bytes

```
use memchr::memchr3_iter;

let haystack = b"xyzaxyzbxyzc";

let mut it = memchr3_iter(b'a', b'b', b'c', haystack).rev();
assert_eq!(Some(11), it.next());
assert_eq!(Some(7), it.next());
assert_eq!(Some(3), it.next());
assert_eq!(None, it.next());
```

# Example: iterating over substring matches

```
use memchr::memmem;

let haystack = b"foo bar foo baz foo";

let mut it = memmem::find_iter(haystack, "foo");
assert_eq!(Some(0), it.next());
assert_eq!(Some(8), it.next());
assert_eq!(Some(16), it.next());
assert_eq!(None, it.next());
```

# Crate features

The upstream feature table is reproduced exactly so that no dependent manifest
has to change.

* **std** — implies `alloc`. Upstream additionally used it for runtime SIMD
  feature detection; there is no SIMD here.
* **alloc** — enables the owned-needle APIs
  ([`memmem::Finder::into_owned`](crate::memmem::Finder::into_owned) and
  friends). The crate is fully usable in core-only contexts without it.
* **logging** — accepted and inert. Upstream traced which vector strategy it
  selected; there is one strategy here, and carrying the `log` crate would
  reintroduce the external dependency this crate exists to remove.
* **libc** — accepted and inert, as upstream.
* **use_std** — deprecated alias for `std`, as upstream.
* **rustc-dep-of-std** — used when this crate is built as part of `std` (via
  `object`). Routes `core` through `rustc-std-workspace-core`.
*/

#![deny(missing_docs)]
#![no_std]
#![forbid(unsafe_code)]

// Supporting 8-bit (or others) would be fine. If you need it, please open an
// issue: the scalar code has no width assumption, but the API contract this
// crate reproduces does not claim it.
#[cfg(not(any(
    target_pointer_width = "16",
    target_pointer_width = "32",
    target_pointer_width = "64"
)))]
compile_error!("memchr currently not supported on non-{16,32,64}");

#[cfg(any(test, feature = "std"))]
extern crate std;

#[cfg(any(test, feature = "alloc"))]
extern crate alloc;

pub use crate::memchr::{
    Memchr, Memchr2, Memchr3, memchr, memchr_iter, memchr2, memchr2_iter, memchr3, memchr3_iter,
    memrchr, memrchr_iter, memrchr2, memrchr2_iter, memrchr3, memrchr3_iter,
};

pub mod arch;
mod cow;
mod memchr;
pub mod memmem;
mod scan;
