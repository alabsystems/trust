#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features, dead_code)]

use core::intrinsics::mir::*;

static mut STATE: u64 = 7;

#[cfg(not(pure))]
#[inline(never)]
fn read(_a: u64) -> u64 {
    unsafe { STATE }
}

#[cfg(pure)]
#[inline(never)]
fn read(a: u64) -> u64 {
    let local = a.wrapping_add(7);
    let reference = &local;
    let reborrow = &*reference;
    *reborrow
}

clean {
    def applyRead (a : UInt64) : UInt64 := read a
}

#[cfg(custom_call)]
#[custom_mir(dialect = "runtime", phase = "optimized")]
fn custom_reference(a: u64) -> u64 {
    mir! {
        {
            Call(RET = applyRead(a), ReturnTo(done), UnwindContinue())
        }
        done = {
            Return()
        }
    }
}

#[cfg(custom_address)]
#[custom_mir(dialect = "runtime", phase = "optimized")]
fn custom_reference(_a: u64) -> u64 {
    mir! {
        {
            // An actual FnDef operand in custom MIR, with no Call terminator.
            let _function = applyRead;
            RET = 7;
            Return()
        }
    }
}

fn main() {
    assert_eq!(custom_reference(0), 7);
}
