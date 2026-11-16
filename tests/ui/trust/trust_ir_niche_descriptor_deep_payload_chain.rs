//@ check-pass
//@ compile-flags: -Ztrust-verify=off -Ztrust-ir-lower=on
#![allow(dead_code)]
//
// Trust regression: a NICHE enum layout descriptor must not be stripped because its payload's
// by-value struct chain is deep.
//
// THE DEFECT. `register_enum` fills `Option<P>`'s descriptor from rustc's own layout (the niche
// is `Vec`'s pointer; size 24), then asks `declared_layout_resolvable` whether the validator can
// re-derive the payload's extent from the module's own rows. That walk carried a depth fuel of 8
// and answered "unresolvable" on exhaustion. The payload below is nine rows deep
// (P → Q → R → Vec<u8> → RawVec → RawVecInner → Unique → NonNull → ptr), so the fuel ran out
// on the scalar leaf, the descriptor was stripped, and the enum fell back to trust-ir's canonical
// tagged-union layout: a tag lane, then the 24-byte payload aligned after it — 32 bytes. `S`
// declares rustc's offsets (`a` at 0, `b` at 24, size 32); the validator sizes `a` from the
// module at 32, so `b` begins inside it and the whole crate module was refused:
//
//     warning: trust-ir-lower semantic finalization failed: final Trust-IR module validation
//       failed [StructLayoutInconsistent]: StructLayoutInconsistent { struct_id: 11,
//       reason: "fields overlap" }
//
// `std::path::PathBuf` (PathBuf → OsString → Buf → Vec<u8>) is exactly this chain, which is how
// autocfg 1.5.1 (`Rustc { rustc_wrapper: Option<PathBuf>, .. }`), cc 1.2.64
// (`Tool { cc_wrapper_path: Option<PathBuf>, .. }`) and ay-tla-bridge
// (`TlcArgs { config: Option<PathBuf>, .. }`) lost their modules (measured 2026-09-22). Case (a)
// spells the depth with local wrappers so the test does not ride std's private layering; case
// (b) is the std spelling that was actually measured.
//
// The predicate now walks the by-value nesting exactly (a Rust type cannot contain itself by
// value, so the walk is finite; a visiting stack guards a malformed table), so a resolvable
// payload keeps its descriptor at any depth.

// (a) THE DEFECT: three by-value wrappers over `Vec<u8>` under `Option`, beside a second field.
struct R {
    inner: Vec<u8>,
}

struct Q {
    inner: R,
}

struct P {
    inner: Q,
}

struct S {
    a: Option<P>,
    b: u64,
}

fn mk() -> S {
    S { a: None, b: 0 }
}

// (b) The std spelling that was measured: `Option<PathBuf>` beside a `PathBuf` (autocfg's
//     `Rustc`). Same overestimate, other symptom: rustc places `rustc_wrapper` at 24 in a
//     48-byte struct, so the canonical 32 bytes run PAST the declared size rather than into a
//     neighbour, and this row was refused as "declared layout is incoherent (overlap /
//     containment / ...)" beside (a)'s "fields overlap".
struct Rustc {
    rustc: std::path::PathBuf,
    rustc_wrapper: Option<std::path::PathBuf>,
}

fn rustc(p: std::path::PathBuf) -> Rustc {
    Rustc { rustc: p, rustc_wrapper: None }
}

// (c) CONTROL, two wrappers: inside the old fuel, so it kept its descriptor before the fix and
//     must keep it after.
struct S2 {
    a: Option<Q>,
    b: u64,
}

fn mk2() -> S2 {
    S2 { a: None, b: 0 }
}

fn main() {}
