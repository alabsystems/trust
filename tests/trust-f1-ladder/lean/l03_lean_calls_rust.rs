// Trust: the Rust callee is private, so the Lean call must inventory it.
#[inline(never)]
fn double(x: u64) -> u64 {
    x.wrapping_add(x)
}

clean {
    def apply_double (x : UInt64) : UInt64 := double x
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn rung(x: u64) -> u64 {
    apply_double(x)
}
