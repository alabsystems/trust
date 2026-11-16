#![allow(dead_code, unused_assignments, unreachable_patterns)]
enum Choice {
    A,
    B,
}
pub fn bool_from_u8(flag: bool) -> u8 {
    u8::from(flag)
}

pub fn bool_from_u16(flag: bool) -> u16 {
    u16::from(flag)
}

pub fn bool_from_u32(flag: bool) -> u32 {
    u32::from(flag)
}

pub fn bool_from_u64(flag: bool) -> u64 {
    u64::from(flag)
}

pub fn bool_from_u128(flag: bool) -> u128 {
    u128::from(flag)
}

pub fn bool_from_usize(flag: bool) -> usize {
    usize::from(flag)
}

pub fn bool_from_i8(flag: bool) -> i8 {
    i8::from(flag)
}

pub fn bool_from_i16(flag: bool) -> i16 {
    i16::from(flag)
}

pub fn bool_from_i32(flag: bool) -> i32 {
    i32::from(flag)
}

pub fn bool_from_i64(flag: bool) -> i64 {
    i64::from(flag)
}

pub fn bool_from_i128(flag: bool) -> i128 {
    i128::from(flag)
}

pub fn bool_from_isize(flag: bool) -> isize {
    isize::from(flag)
}

pub fn bool_from_argument_effect(flag: bool) -> u32 {
    let mut effects = 0;
    let value = u32::from({
        effects += 7;
        flag
    });
    value + effects
}

pub fn bool_from_callee_effect(flag: bool) -> u32 {
    let mut effects = 0;
    let value = ({
        effects += 11;
        u32::from
    })(flag);
    value + effects
}

pub fn bool_from_ordered_effects(flag: bool) -> u32 {
    let mut order = 0;
    let value = ({
        order = order * 10 + 1;
        u32::from
    })({
        order = order * 10 + 2;
        flag
    });
    order * 10 + value
}

pub fn from(flag: bool) -> u32 {
    if flag { 7 } else { 9 }
}

pub fn named_from_control(flag: bool) -> u32 {
    from(flag)
}

pub fn assigned_if(flag: bool) -> u32 {
    let mut a = 1u32;
    let mut b = 2u32;
    let mut r = &mut a;
    if flag {
        r = &mut b;
    }
    *r += 10;
    a * 100 + b
}
pub fn assigned_bool_match(flag: bool) -> u32 {
    let mut a = 1u32;
    let mut b = 2u32;
    let mut r = &mut a;
    match flag {
        true => r = &mut b,
        false => (),
    }
    *r += 10;
    a * 100 + b
}
pub fn assigned_int_match(flag: bool) -> u32 {
    let mut a = 1u32;
    let mut b = 2u32;
    let mut r = &mut a;
    match u32::from(flag) {
        1 => r = &mut b,
        _ => (),
    }
    *r += 10;
    a * 100 + b
}
pub fn assigned_tuple_match(flag: bool) -> u32 {
    let mut a = 1u32;
    let mut b = 2u32;
    let mut r = &mut a;
    match (flag, true) {
        (true, _) => r = &mut b,
        _ => (),
    }
    *r += 10;
    a * 100 + b
}
pub fn assigned_str_match(flag: bool) -> u32 {
    let mut a = 1u32;
    let mut b = 2u32;
    let mut r = &mut a;
    let text = if flag { "b" } else { "a" };
    match text {
        "b" => r = &mut b,
        _ => (),
    }
    *r += 10;
    a * 100 + b
}
pub fn assigned_float_match(flag: bool) -> u32 {
    let mut a = 1u32;
    let mut b = 2u32;
    let mut r = &mut a;
    let value = if flag { 1.0f64 } else { 0.0f64 };
    match value {
        1.0 => r = &mut b,
        _ => (),
    }
    *r += 10;
    a * 100 + b
}
pub fn assigned_enum_match(flag: bool) -> u32 {
    let mut a = 1u32;
    let mut b = 2u32;
    let mut r = &mut a;
    let choice = if flag { Choice::B } else { Choice::A };
    match choice {
        Choice::B => r = &mut b,
        Choice::A => (),
    }
    *r += 10;
    a * 100 + b
}
pub fn assigned_and(flag: bool) -> u32 {
    let mut a = 1u32;
    let mut b = 2u32;
    let mut r = &mut a;
    let _ = flag && {
        r = &mut b;
        true
    };
    *r += 10;
    a * 100 + b
}
pub fn assigned_or(flag: bool) -> u32 {
    let mut a = 1u32;
    let mut b = 2u32;
    let mut r = &mut a;
    let _ = !flag || {
        r = &mut b;
        false
    };
    *r += 10;
    a * 100 + b
}
pub fn assigned_if_let(flag: bool) -> u32 {
    let mut a = 1u32;
    let mut b = 2u32;
    let mut r = &mut a;
    if let Some(()) = if flag { Some(()) } else { None } {
        r = &mut b;
    }
    *r += 10;
    a * 100 + b
}
pub fn assigned_fresh(flag: bool) -> u32 {
    let mut a = 1u32;
    let mut b = 2u32;
    let r: &mut u32;
    if flag {
        r = &mut b;
    } else {
        r = &mut a;
    }
    *r += 10;
    a * 100 + b
}
pub fn shared_fresh(flag: bool) -> u32 {
    let a = 1u32;
    let b = 2u32;
    let r: &u32;
    if flag {
        r = &b;
    } else {
        r = &a;
    }
    *r
}
pub fn raw_direct() -> *const u32 {
    let a = 1u32;
    &raw const a
}
pub fn raw_local_join(flag: bool) -> *const u32 {
    let a = 1u32;
    let b = 2u32;
    let mut r = &raw const a;
    if flag {
        r = &raw const b;
    }
    r
}

pub fn assigned_integer_tuple(flag: bool) -> u32 {
    let mut a = 1u32;
    let mut b = 2u32;
    let mut r = &mut a;
    let tag = if flag { 1u32 } else { 0 };
    match (tag, 0u32) {
        (1, _) => r = &mut b,
        _ => (),
    }
    *r += 10;
    a * 100 + b
}
pub fn assigned_shadow(flag: bool) -> u32 {
    let mut a = 1u32;
    let mut b = 2u32;
    let mut r = &mut a;
    if flag {
        r = &mut b;
        let r = 1.5f64;
        let _ = r;
    }
    *r += 10;
    a * 100 + b
}
pub fn assigned_destructure(flag: bool) -> u32 {
    let mut a = 1u32;
    let mut b = 2u32;
    let (mut r,) = (&mut a,);
    if flag {
        r = &mut b;
    }
    *r += 10;
    a * 100 + b
}
pub fn assigned_nested(flag: bool) -> u32 {
    let mut a = 1u32;
    let mut b = 2u32;
    let mut r = &mut a;
    if flag {
        if flag {
            r = &mut b;
        }
    }
    *r += 10;
    a * 100 + b
}
pub fn assigned_one_reaching(flag: bool) -> u32 {
    let mut a = 1u32;
    let mut b = 2u32;
    let r: &mut u32;
    if flag {
        r = &mut b;
    } else {
        return 7;
    }
    *r += 10;
    a * 100 + b
}
pub fn returned_mut<'a>(flag: bool, a: &'a mut u32, b: &'a mut u32) -> &'a mut u32 {
    let mut r = a;
    if flag {
        r = b;
    }
    r
}
pub fn returned_mut_value(flag: bool) -> u32 {
    let mut a = 1u32;
    let mut b = 2u32;
    *returned_mut(flag, &mut a, &mut b) += 10;
    a * 100 + b
}
pub fn returned_shared<'a>(flag: bool, a: &'a u32, b: &'a u32) -> &'a u32 {
    let mut r = a;
    if flag {
        r = b;
    }
    r
}
pub fn returned_shared_value(flag: bool) -> u32 {
    let a = 1u32;
    let b = 2u32;
    *returned_shared(flag, &a, &b)
}
pub fn raw_mixed(flag: bool, a: &u32, b: *const u32) -> *const u32 {
    let mut r = a as *const u32;
    if flag {
        r = b;
    }
    r
}

pub fn shared_from_mut(flag: bool) -> u32 {
    let mut a = 1u32;
    let mut b = 2u32;
    let mut r: &u32 = &mut a;
    if flag {
        r = &mut b;
    }
    *r
}
pub fn raw_from_caller(flag: bool, a: &u32, b: &u32) -> *const u32 {
    let mut r = a as *const u32;
    if flag {
        r = b as *const u32;
    }
    r
}

pub fn dead_fresh(flag: bool) -> u32 {
    let a = 1u32;
    if flag {
        let p = &raw const a;
        let _ = p;
    } else {
        return 0;
    }
    1
}
pub fn dead_changed(flag: bool) -> u32 {
    let a = 1u32;
    let b = 2u32;
    let mut p = &raw const a;
    if flag {
        p = &raw const b;
    }
    // Keep this dead-pointer overwrite independent of executing an external callee.
    p = 0 as *const u32;
    7
}
pub fn dead_read_before(flag: bool) -> u32 {
    let a = 1u32;
    let b = 2u32;
    let mut p = &raw const a;
    // SAFETY: p still points to the initialized, live a before the branch.
    let before = unsafe { *p };
    if flag {
        p = &raw const b;
    }
    before
}
pub fn dead_forwarded(flag: bool) -> u32 {
    let a = 1u32;
    let b = 2u32;
    let mut p = &raw const a;
    if flag {
        p = &raw const b;
    }
    if !flag {
        p = &raw const a;
    }
    p = 0 as *const u32;
    7
}
pub fn escape_forwarded(flag: bool) -> *const u32 {
    let a = 1u32;
    let b = 2u32;
    let mut p = &raw const a;
    if flag {
        p = &raw const b;
    }
    let q = p;
    if !flag {
        p = q;
    }
    p
}
enum ReviewValue {
    A(u32),
    B(u32),
}
pub fn rb_escape(mut e: ReviewValue) -> *mut u32 {
    let r: &mut u32;
    match e {
        ReviewValue::A(ref mut x) => r = x,
        ReviewValue::B(ref mut x) => r = x,
    }
    r as *mut u32
}
pub fn rb_escape_shared(e: ReviewValue) -> *const u32 {
    let r: &u32;
    match e {
        ReviewValue::A(ref x) => r = x,
        ReviewValue::B(ref x) => r = x,
    }
    r as *const u32
}
pub fn rb_escape_or(mut e: ReviewValue) -> *mut u32 {
    let r: &mut u32;
    match e {
        ReviewValue::A(ref mut x) | ReviewValue::B(ref mut x) => r = x,
    }
    r as *mut u32
}
pub fn raw_live_read(flag: bool) -> u32 {
    let a = 1u32;
    let b = 2u32;
    let mut p = &raw const a;
    if flag {
        p = &raw const b;
    }
    // SAFETY: a and b are both initialized and still alive at this read.
    unsafe { *p }
}
