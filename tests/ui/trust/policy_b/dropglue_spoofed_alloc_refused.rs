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
//! Drop-glue crate-identity pin (2026-09-14). The drop-glue foundational check
//! (`drop_ty_has_masked_fail_closed_glue`) used to trust
//! `tcx.crate_name(destructor.did.krate).as_str() in {core,alloc,std}` — a
//! spoofable `--crate-name` string. A dependency built `-Ztrust-verify=off
//! --crate-name alloc` (here `auxiliary/alloc.rs`) with a PANICKING `Drop`,
//! dropped beside a `println!`, was ACCEPTED and panicked at runtime: its
//! `Drop::drop` crate name was `alloc`, so the drop glue was treated as
//! foundational-TCB and folded under the tolerated `_print` row.
//!
//! `crate_is_authentic_foundational` now authenticates by lang-item ownership
//! (`CrateNum`): this spoofed `alloc` owns no `Box`/`String` lang item, so its
//! `Drop` is NOT foundational and the drop-glue check fails it closed. This file
//! MUST stay red.
extern crate alloc as spoof;
use spoof::Bomb;

fn main() {
    let v = std::hint::black_box(7i32);
    println!("runtime value = {}", v);
    let _b = Bomb(v);
}
