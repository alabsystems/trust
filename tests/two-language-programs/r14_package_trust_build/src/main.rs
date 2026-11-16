// The VERIFIED package lane: `targo trust build` must prove the crate.
mod m {
    clean {
        def pick (a : UInt64) (b : UInt64) : UInt64 := a
    }
}
fn main() {
    let v = m::pick(41, 7);
    assert!(v == 41);
}
