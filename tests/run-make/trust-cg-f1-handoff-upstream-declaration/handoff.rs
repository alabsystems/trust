// A handoff Rust definition reaches both a gated Clean identity and the real
// upstream wrapping-add declaration. Installing that body must preserve this
// definition and every pre-existing definition newly reached through it.
#![crate_name = "handoff_case"]
mod mathematics {
    clean {
        def keep (x : UInt64) : UInt64 := x
    }
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn handoff(x: u64, y: u64) -> u64 {
    mathematics::keep(x.wrapping_add(y))
}
