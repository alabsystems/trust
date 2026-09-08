//@ check-pass
//@ compile-flags: --crate-type=lib -Ztrust-ir-lower -Ztrust-verify=off
//@ forbid-output: final Trust-IR module validation failed
//@ forbid-output: CallEdgeSignatureMismatch
//@ dont-check-compiler-stderr

//! One unresolved Rust function is observed both as a direct call and as an exact
//! function-pointer coercion. The paired symbols reverse body encounter order: declaration
//! interning must be independent of whether the neutral direct observation or exact FnDef
//! observation arrives first.

unsafe extern "Rust" {
    fn direct_first_missing(value: u32) -> u32;
    fn pointer_first_missing(value: u32) -> u32;
}

pub fn direct_first_direct(value: u32) -> u32 {
    unsafe { direct_first_missing(value) }
}

pub fn direct_first_pointer() {
    let _pointer: unsafe fn(u32) -> u32 = direct_first_missing;
}

pub fn pointer_first_pointer() {
    let _pointer: unsafe fn(u32) -> u32 = pointer_first_missing;
}

pub fn pointer_first_direct(value: u32) -> u32 {
    unsafe { pointer_first_missing(value) }
}
