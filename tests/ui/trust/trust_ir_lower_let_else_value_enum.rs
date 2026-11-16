//@ check-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify -Ztrust-verify-level=2 -Ztrust-verify-profile=unix_hardened -Ztrust-verify-include-dependencies=yes -Ztrust-ir-lower=strict --crate-type=lib
#![no_std]

// Registered payload extraction must occur only on Some. The match twin is an
// independent spelling for comparison; both branch results remain observable.
pub fn payload(value: Option<u32>) -> u32 {
    let Some(n) = value else {
        return 17;
    };
    n
}

pub fn payload_match(value: Option<u32>) -> u32 {
    match value {
        Some(n) => n,
        None => 17,
    }
}

// This catches an else-only SSA rebind leaking into the matching continuation.
pub fn divergent_else(value: Option<u32>) -> u32 {
    let mut outer = 11;
    let Some(_) = value else {
        outer = 29;
        return outer;
    };
    outer
}

// Re-evaluating the initializer would toggle `seen` a second time.
pub fn initializer_once(value: Option<u32>) -> u32 {
    let mut seen = false;
    let Some(n) = ({
        seen = !seen;
        value
    }) else {
        return if seen { 17 } else { 19 };
    };
    if seen { n } else { 23 }
}

#[repr(i8)]
pub enum Explicit {
    Negative(u32) = -3,
    Other = 5,
    Last = 9,
}

pub fn explicit_discriminant(value: Explicit) -> u32 {
    let Explicit::Negative(n) = value else {
        return 31;
    };
    n
}

pub fn niladic_variant(value: Explicit) -> u32 {
    let Explicit::Last = value else {
        return 37;
    };
    41
}

// Regression for the pre-existing caller of the extracted shared classifier.
pub fn existing_if_let(value: Option<u32>) -> u32 {
    if let Some(n) = value { n } else { 17 }
}

// Else-only assignments must reach the loop exit or next header. Both the
// let-else and match spellings return 0 for Some and 1 for None.
pub fn else_break(value: Option<u32>) -> u32 {
    let mut x = 0;
    loop {
        let Some(_) = value else {
            x = 1;
            break;
        };
        break;
    }
    x
}

pub fn else_break_match(value: Option<u32>) -> u32 {
    let mut x = 0;
    loop {
        match value {
            Some(_) => (),
            None => {
                x = 1;
                break;
            }
        }
        break;
    }
    x
}

pub fn else_continue(value: Option<u32>) -> u32 {
    let mut first = true;
    let mut x = 0;
    while first {
        first = false;
        let Some(_) = value else {
            x = 1;
            continue;
        };
    }
    x
}

pub fn else_continue_match(value: Option<u32>) -> u32 {
    let mut first = true;
    let mut x = 0;
    while first {
        first = false;
        match value {
            Some(_) => (),
            None => {
                x = 1;
                continue;
            }
        }
    }
    x
}
