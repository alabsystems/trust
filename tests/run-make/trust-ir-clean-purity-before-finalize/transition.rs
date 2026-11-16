#![allow(dead_code, unused_variables)]

static mut STATE: u64 = 7;

#[inline(never)]
fn read(a: u64) -> u64 {
    let observed = a;
    observed
}

clean {
    def applyRead (a : UInt64) : UInt64 := read a
}

fn main() {
    std::hint::black_box(applyRead as fn(u64) -> u64);
}
