//@ dont-check-compiler-stderr
//@[newer] rustc-env: RUSTC_LOG=rustc_mir_build::builder=debug,trust_thir_lower::crate_module=debug,trust_thir_lower::differential=debug
//@ compile-flags: -Zchecksum-hash-algorithm=sha256
//@ revisions: older newer
//@ build-pass
//@[older] edition: 2018
//@[newer] edition: 2024
//@ aux-build: helper.rs
//@ compile-flags: --crate-type=rlib
//@[older] compile-flags: -Ztrust-body-census={{build-base}}/older-hir.jsonl -Ztrust-instance-census={{build-base}}/older-mono.jsonl
//@[newer] compile-flags: -Ztrust-ir-lower=on -Ztrust-body-census={{build-base}}/newer-hir.jsonl -Ztrust-instance-census={{build-base}}/newer-mono.jsonl

extern crate helper;
pub fn root(value: u8) -> u8 { helper::identity(value) }
