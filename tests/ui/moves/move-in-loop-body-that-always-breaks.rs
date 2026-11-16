//@ check-pass
// Trust: D0.7 static-semantics source map, row BORROW-MOVES-COPIES.
//
// The loop body moves `x` and always breaks, so it never runs a second time and
// `x` is moved once. rustc accepts the program.

struct Datum {
    value: u32,
}

fn foo() -> u32 {
    let x = Datum { value: 0 };
    loop {
        let y = x;
        let _ = y.value;
        break;
    }
    0
}

fn main() {
    foo();
}
