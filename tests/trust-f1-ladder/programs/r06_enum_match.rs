enum S { A(u64), B { w: u64, h: u64 }, C }
#[inline(never)] fn mk(x: u64) -> S { match x % 3 { 0 => S::A(x), 1 => S::B { w: x, h: 2 }, _ => S::C } }
#[inline(never)] fn area(s: &S) -> u64 { match s { S::A(r) => r * 3, S::B { w, h } => w * h, S::C => 42 } }
#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { area(&mk(x)) }
