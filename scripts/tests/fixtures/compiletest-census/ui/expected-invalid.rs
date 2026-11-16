//@ compile-flags: -Zchecksum-hash-algorithm=sha256
//@ check-fail
//@ dont-check-compiler-stderr
//@ compile-flags: --crate-type=rlib -Ztrust-body-census={{build-base}}/invalid-hir.jsonl -Ztrust-instance-census={{build-base}}/invalid-mono.jsonl
pub fn invalid() { let _: u8 = "bad"; } //~ ERROR mismatched types
