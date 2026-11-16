// Rust `main` calls kernel-checked Clean `def`s whose bodies contain
// `let`-bindings. `let y := v; b` is definitionally `b[y := v]` (kernel zeta),
// so the emitter reduces every `let` away before recognition and the
// faithfulness gate verifies the emitted body against the island's `let` term.
mod m {
    clean {
        def id_let (x : UInt64) : UInt64 := let y := x; y
        def sq_let (x : UInt64) : UInt64 := let y := x + 1; y * y
        def shadow_let (x : UInt64) : UInt64 := let x := x + 1; x
        def nested_let (x : UInt64) : UInt64 := let y := x; let z := y + 1; z
    }
}
fn main() {
    assert_eq!(crate::m::id_let(7), 7);
    let s = crate::m::sq_let(3); // (3+1)*(3+1)
    assert_eq!(s, 16);
    assert_eq!(crate::m::shadow_let(10), 11); // the SHADOW (param+1) wins
    assert_eq!(crate::m::nested_let(5), 6); // x+1
    println!("sq_let(3) = {s}");
}
