// A Targo PACKAGE (not a bare trustc invocation) with a Clean island.
mod m {
    clean {
        def min2 (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b
    }
}
fn main() {
    let lo = m::min2(7, 41);
    assert!(lo == 7);
    println!("min2(7,41) = {lo}");
}
