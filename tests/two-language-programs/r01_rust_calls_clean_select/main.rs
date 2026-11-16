// Rust `main` calls a kernel-checked Clean `def` from an inline island.
mod m {
    clean {
        def min2 (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b
    }
}
fn main() {
    let lo = crate::m::min2(7, 41);
    assert_eq!(lo, 7);
    assert_eq!(crate::m::min2(41, 7), 7);
    assert_eq!(crate::m::min2(0, u64::MAX), 0);
    println!("min2(7,41) = {lo}");
}
