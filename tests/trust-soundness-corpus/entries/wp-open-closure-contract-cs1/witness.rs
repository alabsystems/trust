// trust-soundness-corpus entry `wp-open-closure-contract-cs1` (trust-wp OPEN: closure contract (cs1)). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
fn cs1(x: i32) {
    assert!(x == 5, "requires");
    let x = 0i32;
    let f = move || {
        assert!(x == 5, "closure precondition x@ == 5 is false at the call");
    };
    f();
}
fn main() {
    cs1(std::hint::black_box(5));
}
