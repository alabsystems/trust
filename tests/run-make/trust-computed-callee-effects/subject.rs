#![crate_type = "lib"]
#![allow(unreachable_code, unused_assignments)]

pub fn identity(value: u32) -> u32 { value }

pub fn direct(mut count: u32) -> u32 {
    count += 1;
    identity(count)
}

pub fn computed(mut count: u32) -> u32 {
    ({ count += 1; identity })(count)
}

pub fn ordered() -> u32 {
    let mut count = 0u32;
    ({ count += 1; identity })({ count *= 10; count })
}

pub fn nested() -> u32 {
    let mut count = 0u32;
    ({ ({ count += 1; identity })(count); identity })({ count *= 10; count })
}

pub fn alias() -> u32 {
    let function = identity;
    let mut count = 0u32;
    ({ count += 1; function })({ count *= 10; count })
}

pub fn diverged() -> u32 {
    let mut count = 0u32;
    ({ return 7; identity })({ count = 99; count })
}

pub fn pointer() -> u32 {
    let function: fn(u32) -> u32 = identity;
    let mut count = 0u32;
    ({ count += 1; function })({ count *= 10; count })
}

pub fn pointer_inline() -> u32 {
    let mut count = 0u32;
    (({ count += 1; identity }) as fn(u32) -> u32)({ count *= 10; count })
}

pub fn loop_callee() -> u32 {
    let mut count = 0u32;
    loop {
        ({ count += 1; identity })(count);
        if count >= 3 { break count; }
    }
}

pub fn nested_loop_callee() -> u32 {
    let mut count = 0u32;
    loop {
        ({ loop { count += 1; break; } identity })(count);
        if count >= 3 { break count; }
    }
}

pub fn reified_loop_callee() -> u32 {
    let mut count = 0u32;
    loop {
        (({ count += 1; identity }) as fn(u32) -> u32)(count);
        if count >= 3 { break count; }
    }
}

pub fn borrowed_reify() -> u32 {
    let mut count = 0u32;
    (({ let pointer = &mut count; *pointer = 7; identity }) as fn(u32) -> u32)(count)
}
