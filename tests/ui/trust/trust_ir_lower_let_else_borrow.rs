//@ check-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify -Ztrust-verify-level=2 -Ztrust-verify-profile=unix_hardened -Ztrust-verify-include-dependencies=yes -Ztrust-ir-lower=strict --crate-type=lib
#![no_std]

// Some => 11; None => 27. The snapshot exists only on the divergent edge.
pub fn shared_snapshot(value: Option<u32>) -> u32 {
    let outer = 11;
    let Some(_) = value else {
        let snapshot = &outer;
        return *snapshot ^ 16;
    };
    outer
}

// Some => 13; None => 29. Promotion is already requested outside let-else.
pub fn promoted_direct_store(value: Option<u32>) -> u32 {
    let mut outer = 11;
    let initial = &mut outer;
    *initial = 13;
    let Some(_) = value else {
        outer = 29;
        return outer;
    };
    outer
}

// Same outcomes, with another borrow of the existing slot only on the else edge.
pub fn promoted_else_reborrow(value: Option<u32>) -> u32 {
    let mut outer = 11;
    let initial = &mut outer;
    *initial = 13;
    let Some(_) = value else {
        let borrowed = &mut outer;
        *borrowed = 29;
        return outer;
    };
    outer
}

// Some => 11; None => 29. This is the previously unvisited borrow site.
pub fn else_only_mutable_borrow(value: Option<u32>) -> u32 {
    let mut outer = 11;
    let Some(_) = value else {
        let borrowed = &mut outer;
        *borrowed = 29;
        return outer;
    };
    outer
}

// Existing source spelling whose Match arm is already visited by the prepass.
pub fn else_only_mutable_borrow_match(value: Option<u32>) -> u32 {
    let mut outer = 11;
    match value {
        Some(_) => (),
        None => {
            let borrowed = &mut outer;
            *borrowed = 29;
            return outer;
        }
    }
    outer
}

// Some/_ => 11; None/Some => 31; None/None => 29. Requires recursive else visits.
pub fn nested_else_mutable_borrow(value: Option<u32>, inner: Option<u32>) -> u32 {
    let mut outer = 11;
    let Some(_) = value else {
        let Some(_) = inner else {
            let borrowed = &mut outer;
            *borrowed = 29;
            return outer;
        };
        return 31;
    };
    outer
}

// Some => 11; None => 31. The identical source name has distinct LocalVarIds.
pub fn else_only_shadowed_local(value: Option<u32>) -> u32 {
    let outer = 11;
    let Some(_) = value else {
        let mut outer = 29;
        let borrowed = &mut outer;
        *borrowed = 31;
        return outer;
    };
    outer
}
