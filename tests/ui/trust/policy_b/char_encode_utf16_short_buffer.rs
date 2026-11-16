//@ needs-trust-verify
//@ edition: 2021
//@ revisions: param local ufcs opt guarded two total
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[opt] compile-flags: -Copt-level=3
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[param] check-fail
//@[local] check-fail
//@[ufcs] check-fail
//@[opt] check-fail
//@[guarded] check-fail
//@[two] check-fail
//@[total] check-pass
//! **`char::encode_utf16` into a buffer that is too short is a panic on the
//! CALLER's value (UTF8-ENCODE-UTF16-SHORTBUF-1; docs/KNOWN_HAZARDS.md, "FIX
//! PREPARED 2026-10-05 … UTF8-ENCODE-UTF16-SHORTBUF-1").**
//!
//! `c.encode_utf16(buf)` panics when `buf` is shorter than `c.len_utf16()` — one
//! unit for a BMP character, two for a supplementary-plane one
//! (`library/core/src/char/methods.rs`, `encode_utf16_raw`). Its UTF-8 twin
//! `encode_utf8` was already refused (`Call::encode_utf8::panic-freedom-unverified`);
//! nothing named this one, so the vanilla-sysroot tolerance admitted it as std's
//! own defined behaviour, and the 2026-09-25 audit row that said it was refused
//! was false.
//!
//! # Before (stage 1 of `dc15b882f6`, main plus wave 16, measured 2026-10-05 with
//! exactly these revisions' flags)
//!
//! Every check-fail revision built rc=0 (one runtime-checked panic-freedom row
//! citing the bundled `core::char::methods::encode_utf16_raw`; `TRUST_VANILLA_DEBUG=1`
//! shows the root ledger admitting `core::char::methods::<impl char>::encode_utf16`
//! as `vanilla=true`), and `total` built rc=0. The witness
//! `char_encode_utf16_short_buffer_run.rs` panics on the `param`/`local` bodies.
//!
//! # After (predicted before the build; measured 2026-10-06 on the stage 1 of
//! `0ac7a96d9f`, `integ/wave18`: every check-fail function is refused with the
//! `Call::encode_utf16::panic-freedom-unverified` row, and `total` builds rc=0)
//!
//! `unwrap_panic::is_buffer_panicking_char_utf16_encoder` names the two core
//! spellings. At a ROOT call site vcgen mints the fail-closed
//! `Call::encode_utf16::panic-freedom-unverified` row (no runtime fallback, so the
//! default policy refuses), and the compiler's root-call tolerance withholds the
//! vanilla admission (`trust_vcgen::callee_is_root_call_caller_value_panic`).
//! Predicted from the `encode_utf8` twins of every check-fail revision, which take
//! the identical row and exit 1 on the BEFORE compiler at `-O0` and `-O3`, and from
//! `crates/trust-vcgen/tests/char_encode_utf16_realmir.rs` (this file's functions'
//! extracted MIR).
//!
//! # Over-refusals kept, on purpose
//!
//! No buffer length is modeled, so `guarded` (`buf.len() >= c.len_utf16()`) and
//! `two` (a `[0u16; 2]` buffer, which can never panic) are refused — parity with
//! `encode_utf8`, which refuses a 4-byte buffer today (docs/DECISION_QUEUE.md,
//! UTF8-ENCODE-UTF16-SHORTBUF-1).
//!
//! # Not charged
//!
//! `total`: the `str` iterator `s.encode_utf16()` calls `char::encode_utf16` inside
//! core's `EncodeUtf16::next`, with its own two-unit buffer. The recognizer is asked
//! of ROOT call sites only, never in the bundle walk, so that stays rc=0.

#[cfg(param)]
pub fn param_buf(c: char, buf: &mut [u16]) -> usize {
    //[param]~^ ERROR Trust strict verification failed for `char_encode_utf16_short_buffer::param_buf`
    c.encode_utf16(buf).len()
}

#[cfg(any(local, opt))]
pub fn local_buf(c: char) -> u16 {
    //[local,opt]~^ ERROR Trust strict verification failed for `char_encode_utf16_short_buffer::local_buf`
    let mut buf = [0u16; 1];
    c.encode_utf16(&mut buf);
    buf[0]
}

#[cfg(opt)]
pub fn param_buf_opt(c: char, buf: &mut [u16]) -> usize {
    //[opt]~^ ERROR Trust strict verification failed for `char_encode_utf16_short_buffer::param_buf_opt`
    c.encode_utf16(buf).len()
}

#[cfg(ufcs)]
pub fn ufcs_buf(c: char, buf: &mut [u16]) -> usize {
    //[ufcs]~^ ERROR Trust strict verification failed for `char_encode_utf16_short_buffer::ufcs_buf`
    char::encode_utf16(c, buf).len()
}

#[cfg(guarded)]
pub fn guarded_buf(c: char, buf: &mut [u16]) -> usize {
    //[guarded]~^ ERROR Trust strict verification failed for `char_encode_utf16_short_buffer::guarded_buf`
    if buf.len() >= c.len_utf16() { c.encode_utf16(buf).len() } else { 0 }
}

#[cfg(two)]
pub fn two_buf(c: char) -> u16 {
    //[two]~^ ERROR Trust strict verification failed for `char_encode_utf16_short_buffer::two_buf`
    let mut buf = [0u16; 2];
    c.encode_utf16(&mut buf);
    buf[0]
}

#[cfg(total)]
pub fn str_count(s: &str) -> usize {
    s.encode_utf16().count()
}

#[cfg(total)]
pub fn str_collect(s: &str) -> Vec<u16> {
    s.encode_utf16().collect()
}

#[cfg(total)]
pub fn char_len(c: char) -> usize {
    c.len_utf16()
}
