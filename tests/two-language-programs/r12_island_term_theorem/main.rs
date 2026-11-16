// A term-proof theorem beside a def in one island.
mod m {
    clean {
        def pick (a : UInt64) (b : UInt64) : UInt64 := a
        theorem pick_eq (a b : UInt64) : pick a b = a := rfl
    }
}
fn main() {
    let lo = m::pick(7, 41);
    assert!(lo == 7);
    println!("pick(7,41) = {lo}");
}
