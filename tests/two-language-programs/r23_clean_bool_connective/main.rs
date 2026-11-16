// Rust `main` calls kernel-checked Clean `def`s that are boolean negations and
// connectives over `Bool` parameters (`def conj (a b : Bool) : Bool := a && b`,
// whose kernel term is `and a b`, def-eq to `Bool.and a b`). The emitted MIR is
// a one-block `_0 = UnaryOp(Not,p)` / `_0 = <BitAnd|BitOr>(l,r)`, reflected
// through `admit_bool_value_function` and verified def-eq before linking.
mod m {
    clean {
        def neg (b : Bool) : Bool := not b
        def conj (a : Bool) (b : Bool) : Bool := a && b
        def disj (a : Bool) (b : Bool) : Bool := a || b
    }
}
fn main() {
    assert_eq!(crate::m::neg(true), false);
    assert_eq!(crate::m::conj(true, false), false);
    assert_eq!(crate::m::disj(false, false), false);
    let a = crate::m::conj(true, true);
    let b = crate::m::disj(true, false);
    let c = crate::m::neg(false);
    println!("neg(true)={} conj(true,false)={} disj(false,false)={} all={}", crate::m::neg(true), crate::m::conj(true, false), crate::m::disj(false, false), a && b && c);
}
