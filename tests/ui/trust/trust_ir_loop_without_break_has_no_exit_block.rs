//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//
// Trust (#192) regression: a `loop` that no `break` ever targets does not terminate, so its exit
// block must never be opened.
//
// `lower_loop` used to `start_block(exit_id, ..)` unconditionally. For `fn forever() -> ! { loop {} }`
// that produced a block with NO predecessor, which `finish_body` then sealed with
// `Return { values: [] }` — zero values against a one-value signature. Two validation classes fell
// out of the single defect: `UnreachableBlock` always, plus `ReturnArityMismatch` whenever the
// declared return was non-unit.
//
// Built MIR for the same function is `bb0: goto bb1; bb1: goto bb1` with no return block at all,
// which is exactly what the fix now reproduces.

// The `-> !` case: produced both classes.
pub fn forever() -> ! {
    loop {}
}

// Non-unit return reached only by divergence — `ReturnArityMismatch` on its own.
pub fn diverging_bool() -> bool {
    loop {}
}

// Unit return — `UnreachableBlock` alone.
pub fn diverging_unit() {
    loop {}
}

// `continue` targets the HEADER, not the exit, so this loop is also break-less and must be
// treated identically. This is the case a `broke` flag set by the wrong lowering arm would miss.
pub fn continue_only() -> ! {
    let mut i = 0u32;
    loop {
        i = i.wrapping_add(1);
        continue;
    }
}

// The control: a loop that DOES break still opens its exit and still carries the break's values
// (the #183 property — the write before `break` must survive the join).
pub fn breaks_with_a_write() -> u32 {
    let mut z = 0;
    let mut c = true;
    loop {
        if c {
            z = 1;
            break;
        }
        c = true;
    }
    z
}

fn main() {}
