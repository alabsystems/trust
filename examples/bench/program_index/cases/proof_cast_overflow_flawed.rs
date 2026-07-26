// Proof-design fixture: minimal flawed narrowing-cast obligation.
//
// This stays free of formatting and allocation so the verifier sees the
// cast proof surface without std I/O noise.

fn narrow_unchecked(x: u32) -> u8 {
    x as u8
}

fn main() {
    let _ = narrow_unchecked(100);
}
