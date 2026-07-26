// Trust: Regression test for rust-lang#146393. Reserved RISC-V GPRs must be
// removed from inline asm's allocatable/clobber register sets.
//@ add-minicore
//@ revisions: rv64gc rv64gc_reserve_x7 rv32e_reserve_x7
//@[rv64gc] compile-flags: --target riscv64gc-unknown-linux-gnu -Awarnings
//@[rv64gc] needs-llvm-components: riscv
//@[rv64gc_reserve_x7] compile-flags: --target riscv64gc-unknown-linux-gnu -Ctarget-feature=+reserve-x7 -Awarnings
//@[rv64gc_reserve_x7] needs-llvm-components: riscv
//@[rv32e_reserve_x7] compile-flags: --target riscv32e-unknown-none-elf -Ctarget-feature=+reserve-x7 -Awarnings
//@[rv32e_reserve_x7] needs-llvm-components: riscv
// ignore-tidy-linelength

#![crate_type = "rlib"]
#![feature(no_core)]
#![no_core]

extern crate minicore;
use minicore::*;

// CHECK-LABEL: @clobber_abi
// rv64gc: asm sideeffect "", "={x1},={x5},={x6},={x7},={x10}
// rv64gc_reserve_x7: asm sideeffect "", "={x1},={x5},={x6},={x10}
// rv64gc_reserve_x7-NOT: ={x7}
// rv32e_reserve_x7: asm sideeffect "", "={x1},={x5},={x6},={x10}
// rv32e_reserve_x7-NOT: ={x7}
#[no_mangle]
pub unsafe fn clobber_abi() {
    asm!("", clobber_abi("C"), options(nostack, nomem, preserves_flags));
}
