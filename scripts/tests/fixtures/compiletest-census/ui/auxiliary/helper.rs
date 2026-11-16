//@[newer] rustc-env: RUSTC_LOG=rustc_mir_build::builder=debug,trust_thir_lower::crate_module=debug,trust_thir_lower::differential=debug
//@ compile-flags: -Zchecksum-hash-algorithm=sha256
//@[older] compile-flags: -Ztrust-body-census={{build-base}}/older-aux-hir.jsonl -Ztrust-instance-census={{build-base}}/older-aux-mono.jsonl
//@[newer] compile-flags: -Ztrust-ir-lower=on -Ztrust-body-census={{build-base}}/newer-aux-hir.jsonl -Ztrust-instance-census={{build-base}}/newer-aux-mono.jsonl
pub fn identity(value: u8) -> u8 { value }
