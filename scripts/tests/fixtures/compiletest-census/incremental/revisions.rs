//@ revisions: bpass1 bpass2
//@ compile-flags: --crate-type=rlib -Zchecksum-hash-algorithm=sha256
//@[bpass1] compile-flags: -Ztrust-body-census={{build-base}}/first-hir.jsonl -Ztrust-instance-census={{build-base}}/first-mono.jsonl
//@[bpass2] compile-flags: -Ztrust-body-census={{build-base}}/second-hir.jsonl -Ztrust-instance-census={{build-base}}/second-mono.jsonl
#[cfg(bpass1)]
pub fn value() -> u8 { 1 }
#[cfg(bpass2)]
pub fn value() -> u8 { 2 }
