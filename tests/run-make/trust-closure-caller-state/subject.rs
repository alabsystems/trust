#![feature(fn_traits)]
// Caller storage preserves values, capture pointers, copies, moves and aliases.
pub fn by_value_repeated() -> u32 {
    let mut value = 0u32;
    let mut update = move || { value += 1; value };
    update();
    update()
}

pub fn by_reference_repeated() -> u32 {
    let mut value = 0u32;
    { let mut update = || value += 1; update(); update(); }
    value
}

pub fn copied_value_environments() -> u32 {
    let mut value = 0u32;
    let mut first = move || { value += 1; value };
    let mut second = first;
    first(); first(); second();
    first() * 10 + second()
}

pub fn moved_reference_environment() -> u32 {
    let mut value = 0u32;
    { let first = || value += 1; let mut second = first; second(); second(); }
    value
}

pub fn moved_current_environment() -> u32 {
    let mut value = 0u32;
    let mut first = move || { value += 1; value };
    first();
    let mut second = first;
    second()
}

pub fn mutable_reference_alias() -> u32 {
    let mut value = 0u32;
    let mut update = move || { value += 1; value };
    { let alias = &mut update; alias(); alias(); }
    update()
}

pub fn shared_reference_alias() -> u32 {
    let value = 4u32;
    let read = move || value + 1;
    let alias = &read;
    alias() + read()
}

pub fn captured_reference_alias() -> u32 {
    let mut value = 0u32;
    {
        let pointer = &mut value;
        let mut update = move || *pointer += 1;
        update(); update();
    }
    value
}

pub fn destructured_value_environment() -> u32 {
    let mut value = 0u32;
    let (mut update,) = (move || { value += 1; value },);
    update(); update()
}

pub fn destructured_shared_environment() -> u32 {
    let value = 4u32;
    let (read,) = (move || value + 1,);
    read() + read()
}

pub fn branch_initialized(flag: bool) -> u32 {
    let value = 7u32;
    let source = move || value;
    let chosen;
    if flag { chosen = source; } else { chosen = source; }
    chosen()
}

pub fn match_initialized(flag: bool) -> u32 {
    let mut value = 0u32;
    let source = move || { value += 1; value };
    let mut chosen;
    match flag { true => chosen = source, false => chosen = source }
    chosen(); chosen()
}

pub fn tuple_branch_initialized(flag: bool) -> u32 {
    let value = 7u32;
    let source = move || value;
    let (chosen, count);
    if flag { chosen = source; count = 1; } else { chosen = source; count = 2; }
    chosen() + count
}

pub fn once_guard(value: &mut u32) -> u32 {
    let take = move || value;
    *take()
}

// Allocate the argument in emitted Rust so the interpreter follows a real borrow
// through the consuming closure call, without forging an entry pointer.
pub fn once_guard_local() -> u32 {
    let mut value = 7u32;
    once_guard(&mut value)
}

// Projected capture places still require an unsupported receiver model.
pub fn projected_guard() -> u32 {
    let mut pair = (1u32, 2u32);
    { let mut update = || pair.0 += 1; update(); }
    pair.0
}

// Shared array capture already has a supported body and must remain executable.
pub fn borrowed_array_capture() -> u32 {
    let values = [1u32, 2u32];
    let read = || values;
    read()[0]
}

pub fn by_value_array_guard() -> u32 {
    let values = [1u32, 2u32];
    let read = move || values;
    read()[0]
}

pub fn ordinary_tuple_guard() -> u32 {
    let mut value = 1u32;
    { let mut pair = (&mut value,); let alias = &mut pair; *alias.0 += 1; }
    value
}

// Consuming the inner closure forces a real by-value FnOnce capture. Both
// environments retain the original mutable reference; neither is a snapshot.
pub fn nested_once_effects() -> u32 {
    let mut value = 7u32;
    {
        let reference = &mut value;
        let inner = move || { let moved = reference; *moved += 3; *moved };
        let outer = move || { let moved = inner; moved() };
        outer();
    }
    value
}

pub fn nested_once_failure() -> u32 {
    let mut value = 7u32;
    let reference = &mut value;
    let inner = move || { let moved = reference; *moved += 3; 41u32 };
    let outer = move || { let moved = inner; moved() };
    let status = outer();
    value + status
}

// Equal capture images belong to different real closure bodies. Moving both
// through a concrete outer environment must retain each original target.
pub fn distinct_nested_once_targets() -> u32 {
    let mut left = 3u32;
    let mut right = 7u32;
    {
        let left_ref = &mut left;
        let first = move || { let moved = left_ref; *moved += 1; };
        let right_ref = &mut right;
        let second = move || { let moved = right_ref; *moved += 10; };
        let outer = move || {
            let moved_first = first;
            let moved_second = second;
            moved_first();
            moved_second();
        };
        // Shared borrows observe one original typed environment home. They do
        // not consume it; its later move still carries the original pointers.
        if !std::ptr::eq(&outer, &outer) { return 999; }
        outer();
    }
    left * 100 + right
}

pub fn mutable_once_home_guard() -> bool {
    let mut value = 7u32;
    let reference = &mut value;
    let mut callback = move || { let moved = reference; *moved += 1; };
    let address = &mut callback as *mut _;
    let same = std::ptr::eq(address, address);
    callback();
    same
}

pub fn once_home_address_escape_guard() -> *const () {
    let mut value = 7u32;
    let reference = &mut value;
    let callback = move || { let moved = reference; *moved += 1; };
    &callback as *const _ as *const ()
}

// A raw pointer binding can acquire later consumers. Immediate ptr::eq
// coercions do not license even a local named address of the environment.
pub fn once_home_address_binding_guard() -> bool {
    let mut value = 7u32;
    let reference = &mut value;
    let callback = move || { let moved = reference; *moved += 1; };
    let address = &callback as *const _;
    let same = std::ptr::eq(address, address);
    callback();
    same
}

mod same_spelling {
    pub fn eq<T>(left: *const T, right: *const T) -> bool { left == right }
}

// A same-spelled ordinary function has no compiler pointer-comparison identity.
pub fn once_home_other_comparison_guard() -> bool {
    let mut value = 7u32;
    let reference = &mut value;
    let callback = move || { let moved = reference; *moved += 1; };
    let same = same_spelling::eq(&callback, &callback);
    callback();
    same
}

// A nested environment containing a stack borrow must not manufacture an
// outlives-frame witness merely because its outer value is an aggregate.
pub fn nested_once_escape_guard() -> *mut u32 {
    let mut value = 7u32;
    let reference = &mut value;
    let inner = move || { let moved = reference; moved };
    let outer = move || { let moved = inner; moved() };
    outer() as *mut u32
}

// Capture analysis infers Fn here; the explicit built-in FnOnce invocation
// therefore resolves to rustc's ClosureOnce shim, not the source body Item.
pub fn zero_capture_once() -> u32 {
    let callback = || 41u32;
    core::ops::FnOnce::call_once(callback, ())
}

pub fn zero_capture_once_receiver_effects() -> u32 {
    let mut evaluations = 0u32;
    let callback = { evaluations += 1; || 41u32 };
    let result = core::ops::FnOnce::call_once(callback, ());
    evaluations * 100 + result
}

pub fn zero_capture_direct_fn() -> u32 {
    let callback = || 43u32;
    callback()
}

pub fn zero_capture_direct_fn_mut_request() -> u32 {
    let mut callback = || 47u32;
    core::ops::FnMut::call_mut(&mut callback, ())
}
