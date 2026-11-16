// Rust `main` calls kernel-checked Clean `def`s whose bodies are comparisons of
// two parameters returned as `Bool` (`def lt (a b : UInt64) : Bool := a < b`,
// whose kernel term is `decide (a < b)`; `==` is `BEq.beq … a b`). The emitted
// MIR is a one-block `_0 = <cmp>(l, r); return`, reflected through the frozen
// `admit_comparison_function` and verified def-eq against the island term
// before anything links. `>`/`>=` are expressed by operand order.
mod m {
    clean {
        def lt (a : UInt64) (b : UInt64) : Bool := a < b
        def le (a : UInt64) (b : UInt64) : Bool := a <= b
        def eqf (a : UInt64) (b : UInt64) : Bool := a == b
        def gt (a : UInt64) (b : UInt64) : Bool := b < a
    }
}
fn main() {
    assert!(crate::m::lt(1, 2));
    assert!(!crate::m::lt(2, 1));
    assert!(!crate::m::lt(2, 2));
    assert!(crate::m::le(2, 2));
    assert!(crate::m::eqf(5, 5));
    assert!(!crate::m::eqf(5, 6));
    assert!(crate::m::gt(2, 1)); // 2 > 1 via b < a
    let ok = crate::m::lt(3, 9) && crate::m::le(4, 4) && crate::m::eqf(7, 7) && !crate::m::gt(1, 8);
    assert!(ok);
    println!("lt(3,9)={} le(4,4)={} eqf(7,7)={} gt(2,1)={}", crate::m::lt(3, 9), crate::m::le(4, 4), crate::m::eqf(7, 7), crate::m::gt(2, 1));
}
