//! `(*r).field` through a `&mut` of a SINGLE-SCALAR newtype — the sixth
//! `library/std` refusal — compiles, and computes the right answer in BOTH halves
//! of the u128 at -O0 and -O3.
//!
//! The refusal that stopped the stage1 `library/std` build in
//! `std_detect::detect::os::darwin::aarch64::detect_features`:
//!
//!     error: [TCG-MIR-UNSUPPORTED] ... detect_features ...: Place projection
//!     error: [TCG-MIR-UNSUPPORTED] ... detect_features ...: assignment
//!            destination projection is not scalar-bindable
//!
//! `cache::Initializer` is `struct Initializer(u128)` and its `set` takes
//! `&mut self`, so the `enable_feature` FnMut closure captures `value` WHOLE by
//! `&mut`; -O2/-O3 inlines the body into
//!
//!     _7 = copy ((*_2).0: u128);                     // <- "Place projection"
//!     ((*_2).0: u128) = BitOr(copy _7, const 1_u128);// <- "...not scalar-bindable"
//!
//! A borrowed-scalar reference has NO address, so the bare `[Deref]` arm — which
//! spends the borrow RECORD rather than a pointer — was the only deref shape the
//! place kernel could resolve. One field element on top of it is just the referent
//! local's own field, and now routes through the same kernel arm a direct
//! `target.0` place does (`deref_borrow_scalar_field_binding`, called by BOTH the
//! read and the write so they cannot name different slots).
//!
//! The closure-captured shape (`detect`) was reverted once because it SEGFAULTED at
//! -O3 (measured 2026-09-14 on the P1-P3-only build: exit 139). Root cause, fixed in
//! the same change as the resolver: after the first arm's write the join degraded
//! the borrow to a self-target placeholder whose `scalar_values` entry was the
//! REFERENT's VALUE, and a Deref-led memory lane loaded through that value as a
//! pointer. The join now keeps a same-referent borrow (so `detect` resolves), and a
//! placeholder's value never lives in `scalar_values` (so no lane can mistake it for
//! an address). `trust-ir-cg-borrow-join-lanes` pins the join/placeholder half.
//!
//! This test RUNS the result rather than only compiling it, for two reasons.
//! First, the hazard is a HALF-WRITTEN u128 (a 128-bit value written through a
//! rebased binding), so bit 0 and bit 127 are both asserted. Second — and this is
//! what `detect_direct` pins — the write and the by-value RETURN of the same
//! newtype must name the SAME storage: binding the deref-field write as a
//! projection while the whole-local read keeps the construction-time scalar
//! COMPILES and returns the pre-write value. That was a live silent miscompile on
//! the direct (no-closure) twin, measured against the LLVM backend, and it is the
//! reason the passthrough route binds the local on the write side too.
//!
//! The MIXED shape (a direct `value.0 |= ..` write before the closure-captured deref
//! writes) is its own crate: at -O3 it must return the right value; at -O0 the
//! closure is a real call, `value` is a scalar CELL, and the direct projected write
//! refuses as `[TCG-SCALAR-CELL-PROJECTION]` — a separate, pre-existing gap (measured
//! on both frozen builds), pinned here by name so closing it flips this assertion.

//@ needs-trust-ir-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{rfs, run, rustc};

fn main() {
    rfs::write(
        "derefield.rs",
        r##"

// ===== Defect B, the SILENT MISCOMPILE the reviewer measured on seven shapes =====
// Every case here COMPILED before the fix and returned the CONSTRUCTION-time
// value: the write bound the projected name while the by-value read kept the
// whole-local one. Each is asserted at -O0 AND -O3 (the class is not
// optimization-gated — the reviewer measured -O0 wrong too).
#[inline(never)] pub fn opaque_u64(v: u64) -> u64 { std::hint::black_box(v) }
#[inline(never)] pub fn opaque_usize(v: usize) -> usize { std::hint::black_box(v) }
#[inline(never)] pub fn opaque_bool(v: bool) -> bool { std::hint::black_box(v) }

#[derive(Copy, Clone)] pub struct W64(u64);
#[inline(never)] pub fn take_w64(w: W64) -> u64 { w.0 }
#[inline(never)] pub fn newtype_u64() -> u64 { let mut w = W64(0); w.0 = opaque_u64(7); take_w64(w) }
// `&mut w.0` then `*r = v`
#[inline(never)] pub fn newtype_u64_via_ref() -> u64 { let mut w = W64(0); let r = &mut w.0; *r = opaque_u64(9); take_w64(w) }
#[derive(Copy, Clone)] pub struct Idx(usize);
#[inline(never)] pub fn take_idx(i: Idx) -> usize { i.0 }
#[inline(never)] pub fn newtype_usize() -> usize { let mut i = Idx(0); i.0 = opaque_usize(5); take_idx(i) }
#[derive(Copy, Clone)] pub struct Flag(bool);
#[inline(never)] pub fn take_flag(f: Flag) -> bool { f.0 }
#[inline(never)] pub fn newtype_bool() -> bool { let mut f = Flag(false); f.0 = opaque_bool(true); take_flag(f) }
// a ZST sibling field
#[derive(Copy, Clone)] pub struct Z(u64, ());
#[inline(never)] pub fn take_z(z: Z) -> u64 { z.0 }
#[inline(never)] pub fn newtype_zst_sibling() -> u64 { let mut z = Z(0, ()); z.0 = opaque_u64(3); take_z(z) }
// a single-variant enum payload through `ref mut`
#[derive(Copy, Clone)] pub enum One { V(u64) }
#[inline(never)] pub fn take_one(o: One) -> u64 { match o { One::V(v) => v } }
#[inline(never)] pub fn single_variant_enum() -> u64 {
    let mut o = One::V(0);
    match o { One::V(ref mut v) => *v = opaque_u64(11) }
    take_one(o)
}
// a POINTER newtype — the shape the first guard would have missed
#[derive(Copy, Clone)] pub struct Cur(*const u8);
#[inline(never)] pub fn opaque_ptr(p: *const u8) -> *const u8 { std::hint::black_box(p) }
#[inline(never)] pub fn deref_cur(c: Cur) -> u8 { unsafe { *c.0 } }
#[inline(never)] pub fn pointer_newtype() -> u8 {
    let a: u8 = 11; let b: u8 = 22;
    let mut c = Cur(&a as *const u8);
    c.0 = opaque_ptr(&b as *const u8);
    deref_cur(c)
}
// an ENTRY-ARG newtype: refused before (`WholeScalarizedAggregate`), correct now
#[inline(never)] pub fn entry_arg_newtype(mut w: W64) -> W64 { w.0 = opaque_u64(13); w }

#[derive(Copy, Clone, Default, PartialEq, Debug)]
pub struct Bits(u128);

impl Bits {
    // EXACTLY std_detect's `cache::Initializer::set`: READ the field, then WRITE it.
    #[inline]
    fn set(&mut self, bit: u32) {
        let v = self.0;
        self.0 = v | (1u128 << bit);
    }
    #[inline]
    fn raw(self) -> u128 { self.0 }
}

#[inline(never)]
fn probe(enable: bool) -> bool { std::hint::black_box(enable) }

// THE GAP. The `FnMut` closure captures `value` WHOLE by `&mut` (because `set`
// takes `&mut self`), and -O2/-O3 inlines it into `((*_r).0) = ..` over a
// borrowed-scalar reference that has no address. Each write sits inside its own
// `switchInt` arm, so the rebased binding must also survive the block-parameter
// join; the by-value return then reads the referent WHOLE.
#[inline(never)]
pub fn detect() -> Bits {
    let mut value = Bits::default();
    let mut enable_feature = |f: u32, enable: bool| {
        if enable {
            value.set(f);
        }
    };
    enable_feature(0, probe(true));
    enable_feature(1, probe(false));
    enable_feature(64, probe(true));
    enable_feature(127, probe(true));
    value
}

// The non-closure twin: -O3 collapses the `&mut` to a DIRECT `(_0.0)` place. This
// case COMPILED before the fix and returned the WRONG value (0) — the write bound
// the projected name while the by-value return read the whole-local one.
#[inline(never)]
pub fn detect_direct() -> Bits {
    let mut value = Bits::default();
    let r = &mut value;
    r.set(0);
    r.set(64);
    value
}

#[inline(never)]
pub fn raw_of(b: Bits) -> u128 { b.raw() }
#[inline(never)]
pub fn hi(b: Bits) -> u64 { (raw_of(b) >> 64) as u64 }
#[inline(never)]
pub fn lo(b: Bits) -> u64 { raw_of(b) as u64 }

fn main() {
    // BOTH halves of the u128 must read back exactly: a rebased binding that
    // carried only the low lane would still pass a bit-0-only check.
    let want = (1u128 << 0) | (1u128 << 64) | (1u128 << 127);
    let got = detect();
    assert_eq!(lo(got), want as u64, "closure-captured &mut: low half");
    assert_eq!(hi(got), (want >> 64) as u64, "closure-captured &mut: high half");
    assert_eq!(raw_of(got), want, "closure-captured &mut: by-value return");

    // ... and the same value must survive the by-value return of the DIRECT twin,
    // whose projected writes must not leave the whole-local name stale.
    let want2 = (1u128 << 0) | (1u128 << 64);
    let got2 = detect_direct();
    assert_eq!(lo(got2), want2 as u64, "direct &mut: low half");
    assert_eq!(hi(got2), (want2 >> 64) as u64, "direct &mut: high half");
    assert_eq!(raw_of(got2), want2, "direct &mut: by-value return");

    // --- Defect B: every newtype shape reads back the WRITTEN value, by value ---
    assert_eq!(newtype_u64(), 7, "u64 newtype (direct field write)");
    assert_eq!(newtype_u64_via_ref(), 9, "u64 newtype via &mut w.0");
    assert_eq!(newtype_usize(), 5, "usize newtype");
    assert_eq!(newtype_bool(), true, "bool newtype");
    assert_eq!(newtype_zst_sibling(), 3, "ZST-sibling newtype");
    assert_eq!(single_variant_enum(), 11, "single-variant enum payload via ref mut");
    assert_eq!(pointer_newtype(), 22, "POINTER newtype: must read the NEW pointee");
    // The entry-arg newtype, read back through a by-value callee. (Spelled
    // `assert_eq!(entry_arg_newtype(..).0, 13)` the ASSERT itself refuses at -O0 in
    // `main` — "borrowed scalar reference used without deref", a `&tmp.0` handed to
    // the assert machinery — which is a different, pre-existing gap from the one
    // this test pins, so the value is taken by value first.)
    let entry = take_w64(entry_arg_newtype(W64(opaque_u64(1))));
    assert_eq!(entry, 13, "entry-arg newtype");
    println!("deref-field scalar borrow ok");
}
"##,
    );
    rfs::write(
        "mixed.rs",
        r##"#[derive(Copy, Clone, Default, PartialEq, Debug)]
pub struct Bits(u128);
impl Bits {
    #[inline]
    fn set(&mut self, bit: u32) { let v = self.0; self.0 = v | (1u128 << bit); }
}
#[inline(never)] fn probe(enable: bool) -> bool { std::hint::black_box(enable) }
#[inline(never)] pub fn raw_of(b: Bits) -> u128 { b.0 }
#[inline(never)]
pub fn detect_mixed() -> Bits {
    let mut value = Bits::default();
    value.0 |= 1u128 << 3;
    let mut ef = |f: u32, e: bool| { if e { value.set(f); } };
    ef(0, probe(true));
    ef(64, probe(true));
    value
}
fn main() { let want3 = (1u128 << 3) | 1 | (1u128 << 64); let got = raw_of(detect_mixed()); assert_eq!(got, want3); println!("ok"); }
"##,
    );

    // `-Cpanic=abort` throughout: unwinding is a separate axis, and with
    // `-Cpanic=unwind` an -O0 `main` full of `assert_eq!` refuses in its cleanup
    // path as `[TCG-REGALLOC-063]` (measured on both frozen builds, 2026-09-15).
    //
    // -O0 and -O3 take DIFFERENT lanes for the same source and both must be right.
    // At -O0 the closure is a real call, `&mut value` escapes, and the referent gets
    // memory identity — that half is a pin against regressing the memory lanes. At
    // -O3 the closure is inlined and the deref-field-over-a-borrowed-scalar shape
    // appears, written inside four `switchInt` arms; that half is the gap itself
    // (it refused outright, then segfaulted, before the fix).
    for opt in ["0", "3"] {
        let bin = format!("derefield{opt}");
        rustc()
            .input("derefield.rs")
            .crate_type("bin")
            .crate_name("derefield")
            .output(&bin)
            .opt_level(opt)
            .panic("abort")
            .arg("-Zcodegen-backend=trust-ir-cg")
            // Codegen axis only: the certificate lane is a separate axis (like
            // `-Ztrust-verify=off` above). AArch64 pair opcodes have no checker-accepted
            // certificate yet, so leaving proofs on would refuse every compile here with
            // [TCG-PROOF-465] regardless of what this test measures.
            .arg("-Ztrust-ir-cg-args=no-proof-certs=1")
            // The verifier is a separate axis; this test is about codegen alone.
            .arg("-Ztrust-verify=off")
            .arg("-Cdebuginfo=0")
            .run();

        run(&bin).assert_stdout_contains("deref-field scalar borrow ok");
    }

    // The mixed shape: direct write + deref writes + by-value return.
    rustc()
        .input("mixed.rs")
        .crate_type("bin")
        .crate_name("mixed")
        .output("mixed3")
        .opt_level("3")
        .panic("abort")
        .arg("-Zcodegen-backend=trust-ir-cg")
        // Codegen axis only: the certificate lane is a separate axis (like
        // `-Ztrust-verify=off` above). AArch64 pair opcodes have no checker-accepted
        // certificate yet, so leaving proofs on would refuse every compile here with
        // [TCG-PROOF-465] regardless of what this test measures.
        .arg("-Ztrust-ir-cg-args=no-proof-certs=1")
        .arg("-Ztrust-verify=off")
        .arg("-Cdebuginfo=0")
        .run();
    run("mixed3").assert_stdout_contains("ok");

    // -O0: the scalar-cell projected-write lane this leg once pinned as a NAMED
    // refusal has LANDED, so the leg is now a value assert, exactly as the note it
    // replaces instructed. MEASURED 2026-09-15 on the round-four stage1 build and on
    // the frozen `trust-stage1-r4` driver: `mixed.rs` at -O0 compiles and prints `ok`
    // under the LLVM backend and under trust-ir-cg alike. Left as `run_fail` it
    // asserts a refusal the compiler no longer emits, so the recipe would fail on a
    // lane that is now CORRECT — and it never ran in the suite because the
    // `derefield3` leg above aborted first.
    rustc()
        .input("mixed.rs")
        .crate_type("bin")
        .crate_name("mixed")
        .output("mixed0")
        .opt_level("0")
        .panic("abort")
        .arg("-Zcodegen-backend=trust-ir-cg")
        // Codegen axis only: the certificate lane is a separate axis (like
        // `-Ztrust-verify=off` above). AArch64 pair opcodes have no checker-accepted
        // certificate yet, so leaving proofs on would refuse every compile here with
        // [TCG-PROOF-465] regardless of what this test measures.
        .arg("-Ztrust-ir-cg-args=no-proof-certs=1")
        .arg("-Ztrust-verify=off")
        .arg("-Cdebuginfo=0")
        .run();
    run("mixed0").assert_stdout_contains("ok");
}
