// Value-correctness control only; no call-count claim.
mod m {
    pub fn identityValue(a: u64) -> u64 { a }
    clean {
        def idValue (a : UInt64) : UInt64 := a
        def identityCall (a : UInt64) : UInt64 := idValue (identityValue a)
        def tailLetCall (a : UInt64) : UInt64 := let p := identityValue a; p
        def pureArgument (a : UInt64) : UInt64 := identityValue (idValue a)
    }
}
fn main() {
    for value in [0u64, 1, 37, 41, 43, 1 << 32, u64::MAX] {
        assert_eq!(m::identityCall(value), value);
        assert_eq!(m::tailLetCall(value), value);
        assert_eq!(m::pureArgument(value), value);
    }
    report();
}
// The print lives in its own loop-free function: since `368e6bf306` the producer
// declines `main`'s `for` loop (a loop lowers faithfully or not at all), and the
// recipe's subject is this call's external signatures, not the loop.
fn report() {
    println!("pure_rust_identity_assertions=21");
}
