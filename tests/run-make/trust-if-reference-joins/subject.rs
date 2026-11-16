#![allow(unreachable_code, unused_assignments)]
pub struct Pair {
    pub x: u32,
}
pub fn scalar_write(flag: bool) -> u32 {
    let mut a = 1;
    let mut b = 2;
    let r = if flag { &mut a } else { &mut b };
    *r += 3;
    a * 10 + b
}
pub fn field_write(flag: bool) -> u32 {
    let mut a = Pair { x: 1 };
    let mut b = Pair { x: 2 };
    (if flag { &mut a } else { &mut b }).x += 3;
    a.x * 10 + b.x
}
pub fn shared_read(flag: bool) -> u32 {
    let a = 1;
    let b = 2;
    *(if flag { &a } else { &b })
}
pub fn choose_shared<'a>(flag: bool, a: &'a u32, b: &'a u32) -> &'a u32 {
    if flag { a } else { b }
}
pub fn returned_shared(flag: bool) -> u32 {
    let a = 1;
    let b = 2;
    *choose_shared(flag, &a, &b)
}
pub fn choose_mut<'a>(flag: bool, a: &'a mut u32, b: &'a mut u32) -> &'a mut u32 {
    if flag { a } else { b }
}
pub fn returned_mut(flag: bool) -> u32 {
    let mut a = 1;
    let mut b = 2;
    *choose_mut(flag, &mut a, &mut b) += 3;
    a * 10 + b
}
pub fn one_live_arm(flag: bool) -> u32 {
    let mut a = 1;
    let r = if flag { return 22 } else { &mut a };
    *r += 3;
    a
}
pub fn nested_write(a_flag: bool, b_flag: bool) -> u32 {
    let mut a = 1;
    let mut b = 2;
    let mut c = 3;
    let r = if a_flag { if b_flag { &mut a } else { &mut b } } else { &mut c };
    *r += 3;
    a * 100 + b * 10 + c
}
pub fn static_or_caller<'a>(flag: bool, a: &'a u32) -> &'a u32 {
    if flag { &99 } else { a }
}
pub fn mixed_outlives(flag: bool) -> u32 {
    let a = 1;
    *static_or_caller(flag, &a)
}
pub fn raw_direct() -> *const u32 {
    let a = 1u32;
    &a as *const u32
}
pub fn raw_join(flag: bool) -> *const u32 {
    let a = 1u32;
    let b = 2u32;
    if flag { &a as *const u32 } else { &b as *const u32 }
}

// These helpers exercise permission preservation; readonly_join_write is never executed natively.
pub fn shared_from_mut_join(flag: bool) -> u32 {
    let mut a = 1;
    let mut b = 2;
    let r: &u32 = if flag { &mut a } else { &mut b };
    *r
}
#[allow(invalid_reference_casting)]
pub fn readonly_join_write(flag: bool) -> u32 {
    let mut a = 1u32;
    let mut b = 2u32;
    let r: &u32 = if flag { &mut a } else { &mut b };
    unsafe {
        *(r as *const u32 as *mut u32) = 9;
    }
    0
}
pub fn raw_from_caller(flag: bool, a: *const u32, b: *const u32) -> *const u32 {
    if flag { a } else { b }
}

pub fn raw_from_references(flag: bool, a: &u32, b: &u32) -> *const u32 {
    if flag { a as *const u32 } else { b as *const u32 }
}
pub fn raw_mixed_origin(flag: bool, a: &u32, b: *const u32) -> *const u32 {
    if flag { a as *const u32 } else { b }
}

pub fn local_or_caller(flag: bool, caller: &u32) -> u32 {
    let local = 7;
    *(if flag { &local } else { caller })
}

pub fn mixed_frame(flag: bool) -> u32 {
    let caller = 2;
    local_or_caller(flag, &caller)
}

pub fn raw_local_or_caller(flag: bool, caller: &u32) -> *const u32 {
    let local = 7u32;
    if flag { &local as *const u32 } else { caller as *const u32 }
}
