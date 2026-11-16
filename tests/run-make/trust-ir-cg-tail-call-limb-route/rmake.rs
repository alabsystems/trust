//! The HIGH LIMB of a 128-bit call result, extracted in tail position, is not a
//! tail call — a MISCOMPILE the `-O3` machine pipeline produced silently.
//!
//! `(callee_returning_u128() >> 64) as u64` lowers, on AArch64, to
//!
//!     bl   callee            ; result pair in (x0 = lo, x1 = hi)
//!     mov  vN, x1            ; the `amt == 64` arm of the i128 constant-shift
//!                            ; fold: lo' = hi  (emit_i128_const_shift)
//!     mov  x0, vN            ; the truncation + the ABI return copy
//!     ret
//!
//! Tail-call optimization deletes every post-call move and rewrites `bl` to `b`.
//! That is sound ONLY when the moves route the callee's result register into the
//! SAME register the caller returns it in. Here they route x1 into x0, which is a
//! real computation (a limb extraction), so deleting it returns the callee's LOW
//! limb. `intervening_insts_only_route_call_result` accepted it because x1 is in
//! the call's `implicit_defs` — membership alone cannot distinguish "forward the
//! result" from "extract a limb" for a pair-returning callee.
//!
//! MEASURED on the round-four stage1 build (2026-09-15): `hi()` in
//! `trust-ir-cg-deref-field-scalar-borrow`'s fixture compiled to a bare
//! `b raw_of`, returned the low half, and aborted that test binary with SIGABRT
//! and empty output. Every case below is asserted against the value the LLVM
//! backend computes for the same source.
//!
//! The lanes that must KEEP tail-calling are pinned too (`fwd_u128`, `fwd_lo`,
//! `fwd_u64`): their routing is register-identity (x0 -> x0, x1 -> x1), so the
//! fix must not cost them their tail call.

//@ needs-trust-ir-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{rfs, run, rustc};

fn main() {
    rfs::write(
        "limbroute.rs",
        r##"
#[derive(Copy, Clone)] pub struct B(u128);
#[inline(never)] pub fn opaque(v: u128) -> u128 { std::hint::black_box(v) }
#[inline(never)] pub fn raw_of(b: B) -> u128 { b.0 }
#[inline(never)] pub fn lo_of(b: B) -> u64 { raw_of(b) as u64 }
// Every byte differs between the halves, so a returned WRONG limb cannot
// coincide with the right answer (a bit-0-only value would).
#[inline(never)] pub fn mk() -> B { B(opaque(0xAABB_CCDD_EEFF_0011_2233_4455_6677_8899u128)) }

// THE DEFECT: the high limb, extracted in tail position.
#[inline(never)] pub fn hi_u64(b: B) -> u64 { (raw_of(b) >> 64) as u64 }
#[inline(never)] pub fn hi_i64(b: B) -> i64 { (raw_of(b) >> 64) as i64 }
#[inline(never)] pub fn hi_u32(b: B) -> u32 { (raw_of(b) >> 64) as u32 }
// Narrower destinations keep a real UXTH/UXTB, so they never tail-called; they
// pin that the fold's limb re-label itself stays correct.
#[inline(never)] pub fn hi_u16(b: B) -> u16 { (raw_of(b) >> 64) as u16 }
#[inline(never)] pub fn hi_u8(b: B)  -> u8  { (raw_of(b) >> 64) as u8 }
// Neighbouring shift amounts: the general funnel, not the `amt == 64` arm.
#[inline(never)] pub fn sh63(b: B) -> u64 { (raw_of(b) >> 63) as u64 }
#[inline(never)] pub fn sh65(b: B) -> u64 { (raw_of(b) >> 65) as u64 }
// The truncation consumed by arithmetic / a compare instead of the return.
#[inline(never)] pub fn hi_plus1(b: B) -> u64 { ((raw_of(b) >> 64) as u64).wrapping_add(1) }
#[inline(never)] pub fn hi_eq(b: B) -> bool { ((raw_of(b) >> 64) as u64) == 0xAABBCCDDEEFF0011u64 }
// The same extraction passed as a CALL ARGUMENT (the other physical-register
// sink TCO deletes).
#[inline(never)] pub fn sink(v: u64) -> u64 { std::hint::black_box(v) }
#[inline(never)] pub fn hi_arg(b: B) -> u64 { sink((raw_of(b) >> 64) as u64) }
// LEGITIMATE tail calls (register-identity routing) — must stay correct.
#[inline(never)] pub fn fwd_u128(b: B) -> u128 { raw_of(b) }
#[inline(never)] pub fn fwd_lo(b: B) -> u64 { raw_of(b) as u64 }
#[inline(never)] pub fn fwd_u64(b: B) -> u64 { lo_of(b) }

fn main() {
    let v = mk();
    let raw = 0xAABB_CCDD_EEFF_0011_2233_4455_6677_8899u128;
    assert_eq!(hi_u64(v), (raw >> 64) as u64, "high limb -> u64 return");
    assert_eq!(hi_i64(v), (raw >> 64) as i64, "high limb -> i64 return");
    assert_eq!(hi_u32(v), (raw >> 64) as u32, "high limb -> u32 return");
    assert_eq!(hi_u16(v), (raw >> 64) as u16, "high limb -> u16 return");
    assert_eq!(hi_u8(v),  (raw >> 64) as u8,  "high limb -> u8 return");
    assert_eq!(sh63(v), (raw >> 63) as u64, "shift 63");
    assert_eq!(sh65(v), (raw >> 65) as u64, "shift 65");
    assert_eq!(hi_plus1(v), ((raw >> 64) as u64).wrapping_add(1), "high limb + 1");
    assert!(hi_eq(v), "high limb compared");
    assert_eq!(hi_arg(v), (raw >> 64) as u64, "high limb as a call argument");
    assert_eq!(fwd_u128(v), raw, "forwarded u128");
    assert_eq!(fwd_lo(v), raw as u64, "forwarded low limb");
    assert_eq!(fwd_u64(v), raw as u64, "forwarded u64 callee");
    println!("limb route ok");
}
"##,
    );

    // -O0 and -O3 take different machine pipelines: TCO runs only at the O2/O3
    // pass-manager levels, and only the O3 shape reached the defective guard.
    // Both are asserted so a future pipeline change cannot move the defect into
    // an unwatched level.
    for opt in ["0", "3"] {
        let bin = format!("limbroute{opt}");
        rustc()
            .input("limbroute.rs")
            .crate_type("bin")
            .crate_name("limbroute")
            .output(&bin)
            .opt_level(opt)
            .panic("abort")
            .arg("-Zcodegen-backend=trust-ir-cg")
            .arg("-Ztrust-ir-cg-args=no-proof-certs=1")
            .arg("-Ztrust-verify=off")
            .arg("-Cdebuginfo=0")
            .run();
        run(&bin).assert_stdout_contains("limb route ok");
    }
}
