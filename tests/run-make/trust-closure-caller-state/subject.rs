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
