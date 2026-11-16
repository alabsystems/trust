//@ needs-trust-verify
// `aux-crate`, not `aux-build`: this aux DELIBERATELY declares the crate name
// `alloc`, so a bare `-L` search path leaves `extern crate alloc` ambiguous
// against the sysroot's real `alloc` and the compile dies E0464 "multiple
// candidates" before any Trust check runs. `aux-crate` passes an explicit
// `--extern alloc=<path>`, which is what makes the spoof resolve to THIS crate —
// the whole point of the fixture.
//@ aux-crate: alloc=alloc.rs
//@ compile-flags: -Ztrust-verify=on -Copt-level=0
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! Crate-identity root-fix pin (2026-09-14). The foundational-crate boundary used
//! to key on `tcx.crate_name(..).as_str()` in {core,alloc,std} — a SPOOFABLE
//! `--crate-name` string. A dependency built `-Ztrust-verify=off --crate-name
//! alloc` (here, the aux file `auxiliary/alloc.rs` declares crate name `alloc`)
//! whose `boom` PANICS, called beside a `println!`, was ACCEPTED and panicked at
//! runtime: `crate_name == "alloc"` put it in the unmasked allow-list, and its
//! panic folded under the tolerated `_print` row.
//!
//! `crate_is_authentic_foundational` now authenticates core/alloc/std by LANG-ITEM
//! OWNERSHIP (a `CrateNum`): real alloc owns `Box`/`String`, real core owns
//! `Sized`, real std provides `#[panic_handler]`. This spoofed `alloc` has a
//! different `CrateNum` and owns no such lang item, so it is NOT authentic and the
//! masked-call rule fails it closed. The real sysroot crates (which own the
//! anchors) stay trusted, so ordinary `println!`/`black_box`/foundational
//! formatting are unaffected. This file MUST stay red.
extern crate alloc as spoof;

fn main() {
    let v = std::hint::black_box(5i32);
    println!("call {}", v);
    let r = spoof::boom(v);
    let _ = std::hint::black_box(r);
}
