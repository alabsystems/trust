//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ revisions: param local
//@ compile-flags: -Ztrust-verify=off
//@ error-pattern: encode_utf16: need 2 bytes to encode U+1F600 but buffer has just 1
//@ ignore-emscripten no processes
//! The WITNESS for `char_encode_utf16_short_buffer.rs` (UTF8-ENCODE-UTF16-SHORTBUF-1):
//! the `param` and `local` bodies, built with verification OFF, handed a
//! supplementary-plane character and a one-unit buffer. Both panic (exit 101) —
//! before and after the fix, which changes only whether the VERIFIED build of the
//! same bodies is accepted (it was, rc=0, on the stage 1 of `dc15b882f6`).

fn param_buf(c: char, buf: &mut [u16]) -> usize {
    c.encode_utf16(buf).len()
}

fn local_buf(c: char) -> u16 {
    let mut buf = [0u16; 1];
    c.encode_utf16(&mut buf);
    buf[0]
}

fn main() {
    let c = std::hint::black_box('\u{1F600}');
    if cfg!(param) {
        let mut buf = [0u16; 1];
        println!("{}", param_buf(c, &mut buf));
    } else {
        println!("{}", local_buf(c));
    }
}
