#![feature(rustc_attrs)]
#![allow(internal_features)]

fn read(a: u64) -> u64 {
    a
}

clean {
    def applyPure (a : UInt64) : UInt64 := read a
}

#[rustc_clean(cfg = "warm", loaded_from_disk = "trust_clean_origin_references")]
fn referenced() -> fn(u64) -> u64 {
    applyPure
}

fn main() {
    assert_eq!(referenced()(7), 7);
}
