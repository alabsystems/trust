// Trust: a Rust caller of a computational Lean declaration.
mod mathematics {
    clean {
        def double (x : UInt64) : UInt64 := x + x
    }
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn rung(x: u64) -> u64 {
    mathematics::double(x)
}
