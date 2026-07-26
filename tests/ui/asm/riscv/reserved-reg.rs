// Trust: Regression test for rust-lang#146393. RISC-V inline asm must reject
// registers reserved through LLVM's `reserve-x<N>` target features.
//@ add-minicore
//@ compile-flags: --target riscv64gc-unknown-linux-gnu -Ctarget-feature=+reserve-x7 -Awarnings
//@ needs-llvm-components: riscv
//@ ignore-backends: gcc

#![crate_type = "lib"]
#![feature(no_core)]
#![no_core]

extern crate minicore;
use minicore::*;

fn f() {
    unsafe {
        asm!("", out("x7") _);
        //~^ ERROR cannot use register `x7`: x7 is a reserved register on this target
    }
}
