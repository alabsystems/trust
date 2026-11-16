// trust-soundness-corpus entry `wp-open-macro-hygiene-mh2` (trust-wp OPEN: macro hygiene (mh2)). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
#![allow(unused_mut)]

macro_rules! zero_x {
    () => {
        let x = 0i32;
        let _ = x;
    };
}

macro_rules! five_x {
    () => {
        let x = 5i32;
        let _ = x;
    };
}

macro_rules! bump_local {
    () => {
        let mut x = 0i32;
        x += 7;
        let _ = x;
    };
}

macro_rules! mk_y_from_x {
    ($e:expr) => {
        let x = $e;
        let _ = x;
    };
}
fn mh2() {
    let x = std::hint::black_box(0i32);
    five_x!();
    println!("x = {x}");
    assert!(x == 5, "proof_assert!(x@ == 5) is false");
}
fn main() {
    mh2();
}
