//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
// wave-DA: a DIVERGING call argument (`break`, `return`, `panic!()` in arg
// position) seals the block inside its own lowering — the call is dead code
// and built MIR agrees (the divergence edge is the terminator). The arg loop
// stops lowering the call with no tag, the wave-MR sealed-divergence
// discipline; previously these tagged Call(unsupported arg) and the body
// stayed dirty for a call that cannot happen.

pub fn int_id(x: isize) -> isize {
    x
}

pub fn loop_break() {
    loop {
        int_id(break);
    }
}

pub fn arg_return(c: bool) -> isize {
    if c { int_id(return 3) } else { 7 }
}

fn main() {
    loop_break();
    assert_eq!(arg_return(true), 3);
    assert_eq!(arg_return(false), 7);
}
