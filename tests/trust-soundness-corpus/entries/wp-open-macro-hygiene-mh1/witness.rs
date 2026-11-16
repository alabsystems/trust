// trust-soundness-corpus entry `wp-open-macro-hygiene-mh1` (trust-wp OPEN: macro hygiene (mh1)). See entry.json for the claim,
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
fn mh1(x: i32) {
    zero_x!();
    println!("x = {x}");
    assert!(x == 0, "proof_assert!(x@ == 0) is false");
}
fn main() {
    mh1(std::hint::black_box(5));
}
