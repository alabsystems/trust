// G5, the Lean-to-Rust direction: a Clean `def` calls an ordinary Rust fn.
fn inc(x: u64) -> u64 { x.wrapping_add(1) }
clean {
    def twice_inc (x : UInt64) : UInt64 := inc (inc x)
}
fn main() {
    let v = twice_inc(5);
    assert!(v == 7);
    println!("twice_inc(5) = {v}");
}
