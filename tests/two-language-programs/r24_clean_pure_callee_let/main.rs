// A Clean `def` may call a PURE Rust fn, and a `let`-bound PURE call may be used
// any number of times: the compiler evaluates it ONCE, as an explicit value
// temporary, in binding order (W5 increment 7). The kernel def-eq gate (a PURE
// calculus) is exact either way — `sub2 (dbl x) (dbl x)` computes `sub2 v v = 0`
// for the one value `v = dbl x` denotes — and the once-evaluation is a
// structural check the emitter makes, not a kernel claim.
//
// An EFFECTFUL callee is a different matter: the kernel treats a Rust callee as a
// pure value, so it cannot see reads/writes of global state, and a `let`-bound
// effectful call used twice would emit two diverging calls. That is refused by
// the purity guard — see tests/ui/trust/clean_origin_effectful_callee_refused.rs.
fn dbl(x: u64) -> u64 {
    x.wrapping_add(x)
} // PURE

fn sub2(a: u64, b: u64) -> u64 {
    a.wrapping_sub(b)
} // PURE

clean {
    def dup_pure_let (x : UInt64) : UInt64 := let y := dbl x; sub2 y y
    def once_pure_let (x : UInt64) : UInt64 := let y := dbl x; sub2 y x
}

fn main() {
    assert_eq!(dup_pure_let(5), 0); // sub2(dbl 5, dbl 5) = sub2(10, 10) = 0
    assert_eq!(once_pure_let(4), 4); // sub2(dbl 4, 4) = sub2(8, 4) = 4
    println!("dup_pure_let(5) = {}", dup_pure_let(5));
}
