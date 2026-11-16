#![no_std]
#![allow(dead_code)]

#[inline(never)]
pub fn panic_add(x: u8) -> u8 { x + 1 }

#[inline(never)]
pub fn total_leaf(x: u8) -> u8 { x }

pub fn reified_bare(x: u8) -> u8 {
    let f: fn(u8) -> u8 = panic_add;
    f(x)
}

pub fn reified_counted(x: u8, d: u8) -> u8 {
    if x > 3 {
        let f: fn(u8) -> u8 = panic_add;
        f(x)
    } else if d != 0 { x / d } else { 0 }
}

pub fn direct_counted(x: u8, d: u8) -> u8 {
    if x > 3 { panic_add(x) } else if d != 0 { x / d } else { 0 }
}

pub fn total_counted(x: u8, d: u8) -> u8 {
    if x > 3 {
        let f: fn(u8) -> u8 = total_leaf;
        f(x)
    } else if d != 0 { x / d } else { 0 }
}

pub fn guarded_counted(x: u8, d: u8) -> u8 {
    if x > 3 {
        let f: fn(u8) -> u8 = panic_add;
        f(x & 127)
    } else if d != 0 { x / d } else { 0 }
}

pub fn unknown_counted(f: fn(u8) -> u8, x: u8, d: u8) -> u8 {
    if x > 3 { f(x) } else if d != 0 { x / d } else { 0 }
}

// Target deliberately follows its callers: the dependency edge must be
// captured before MIR is stolen, not guessed from item enumeration order.
pub fn total_defined_after(x: u8) -> u8 {
    let f: fn(u8) -> u8 = later_total;
    f(x)
}

pub fn total_defined_after_counted(x: u8, d: u8) -> u8 {
    if x > 3 {
        let f: fn(u8) -> u8 = later_total;
        f(x)
    } else if d != 0 { x / d } else { 0 }
}

pub fn reassigned_counted(flag: bool, x: u8, d: u8) -> u8 {
    let mut f: fn(u8) -> u8 = total_leaf;
    if flag { f = panic_add; }
    if x > 3 { f(x) } else if d != 0 { x / d } else { 0 }
}

pub fn borrowed_counted(x: u8, d: u8) -> u8 {
    let mut f: fn(u8) -> u8 = total_leaf;
    let slot = &mut f;
    *slot = panic_add;
    if x > 3 { f(x) } else if d != 0 { x / d } else { 0 }
}

pub fn parameter_maybe_overwritten(mut f: fn(u8) -> u8, overwrite: bool, x: u8, d: u8) -> u8 {
    if overwrite { f = total_leaf; }
    if x > 3 { f(x) } else if d != 0 { x / d } else { 0 }
}

#[inline(never)]
pub fn later_total(x: u8) -> u8 { x }

// A reified constructor must not be scheduled as an independent verified root.
pub struct Wrapper(pub u8);
pub fn constructor_pointer(x: u8) -> u8 {
    let f: fn(u8) -> Wrapper = Wrapper;
    let _ = f(x);
    x
}
