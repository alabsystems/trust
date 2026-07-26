// Proof-design fixture: minimal guarded narrowing-cast obligation.
//
// This stays free of formatting and allocation so the verifier sees the
// cast proof surface without std I/O noise.

fn narrow_guarded(x: u32) -> u8 {
    if x <= u8::MAX as u32 {
        x as u8
    } else {
        u8::MAX
    }
}

fn main() {
    let _ = narrow_guarded(100);
    let _ = narrow_guarded(1000);
}
