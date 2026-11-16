#[inline(never)] fn fib(n: u64) -> u64 { if n < 2 { n } else { fib(n - 1) + fib(n - 2) } }
#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { fib(x & 15) }
