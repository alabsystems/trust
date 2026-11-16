#![crate_type = "lib"]

// Actual ordinary Rust slice destructuring. This fixture tests structural
// producer coverage and differential observations, never a proof grade.

pub fn bytes_ordered(a: &[u8]) -> u64 {
    match a {
        [] => 17,
        [only] => *only as u64,
        [first, middle @ .., last] => (*first as u64) ^ ((*last as u64) << 8) ^ ((middle.len() as u64) << 16),
    }
}

pub fn words_ordered(a: &[u64]) -> u64 {
    match a {
        [] => 19,
        [only] => *only,
        [first, middle @ .., last] => *first ^ (*last << 1) ^ ((middle.len() as u64) << 32),
    }
}

pub fn signed_suffix(a: &[i16]) -> i64 {
    match a {
        [] => -31,
        [only] => *only as i64,
        [left, .., right] => (*left as i64) ^ ((*right as i64) << 1),
    }
}

pub fn wildcard_and_suffix(a: &[u32]) -> u64 {
    match a {
        [] => 23,
        [_, last] => *last as u64,
        [first, ..] => *first as u64,
    }
}

pub fn bool_elements(a: &[bool]) -> u8 {
    match a {
        [] => 3,
        [only] => *only as u8,
        [first, .., last] => (*first as u8) ^ ((*last as u8) << 1),
    }
}

pub fn char_elements(a: &[char]) -> u64 {
    match a {
        [] => 29,
        [only] => *only as u64,
        [first, .., last] => (*first as u64) ^ ((*last as u64) << 32),
    }
}

pub fn zst_rest(a: &[()]) -> usize {
    match a {
        [] => 0,
        [_only] => 1,
        [_first, middle @ .., _last] => middle.len() + 2,
    }
}

pub fn local_join(a: &[u32], seed: u64) -> u64 {
    let mut value = seed;
    match a {
        [] => value = 41,
        [only] => value ^= *only as u64,
        [first, .., last] => value ^= (*first as u64) ^ ((*last as u64) << 1),
    }
    value ^ 43
}

pub fn diverging_arm(a: &[u64], seed: u64) -> u64 {
    match a {
        [] => return seed,
        [only] => *only,
        [first, .., last] => *first ^ *last,
    }
}

// Scalar-input twins execute actual local array storage, address computation,
// and payload loads in the interpreter (no caller-injected pointer memory).
pub fn execute_one(x: u64) -> u64 {
    let a = [x];
    match &a as &[u64] {
        [] => 47,
        [only] => *only,
        [first, .., last] => *first ^ *last,
    }
}

pub fn execute_two(x: u64, y: u64) -> u64 {
    let a = [x, y];
    match &a as &[u64] {
        [] => 47,
        [only] => *only,
        [first, .., last] => *first ^ (*last << 1),
    }
}

pub fn execute_rest(x: u64, y: u64, z: u64) -> u64 {
    let a = [x, y, z];
    match &a as &[u64] {
        [] => 47,
        [only] => *only,
        [first, middle @ .., last] => *first ^ (*last << 1) ^ ((middle.len() as u64) << 32),
    }
}

// Empty storage exercises the length branch before any element projection.
pub fn execute_empty(x: u64) -> u64 {
    let a: [u64; 0] = [];
    match &a as &[u64] {
        [] => x ^ 47,
        [only] => *only,
        [first, .., last] => *first ^ *last,
    }
}

// The same asymmetric payloads exercise byte stride rather than word stride.
pub fn execute_byte_pair(x: u64, y: u64) -> u64 {
    let a = [x as u8, y as u8];
    match &a as &[u8] {
        [] => 47,
        [only] => *only as u64,
        [first, .., last] => (*first as u64) ^ ((*last as u64) << 8),
    }
}

pub fn execute_zst(x: u64) -> u64 {
    let a = [(), (), ()];
    match &a as &[()] {
        [] => 47,
        [_only] => x,
        [_first, middle @ .., _last] => x ^ ((middle.len() as u64) << 32),
    }
}

pub fn execute_zst_repeat(x: u64) -> u64 {
    let a = [(); 3];
    match &a as &[()] {
        [] => 47,
        [_only] => x,
        [_first, middle @ .., _last] => x ^ ((middle.len() as u64) << 32),
    }
}

pub fn execute_unit_array_effects(x: u64) -> u64 {
    let mut value = x;
    let a = [
        { value = value * 3 + 1; },
        { value = value * 5 + 2; },
        { value = value * 7 + 3; },
    ];
    match &a as &[()] {
        [] => 47,
        [_only] => value,
        [_first, middle @ .., _last] => value ^ ((middle.len() as u64) << 32),
    }
}

pub fn execute_unit_array_diverge(x: u64) -> u64 {
    // The second element is unsupported if reached. A correct first-element
    // return evaluates neither it nor the array constructor.
    let a: [(); 2] = [{ return x ^ 7; }, unsafe { core::arch::asm!(""); }];
    let _ = a;
    0
}

pub fn refuse_unit_array_asm() -> usize {
    let a = [unsafe { core::arch::asm!(""); }];
    match &a as &[()] { [] => 0, [_first, rest @ ..] => rest.len() }
}

pub fn read_reference_join(a: &[u64], fallback: &u64) -> u64 {
    *(match a {
        [] => fallback,
        [only] => only,
        [_, .., last] => last,
    })
}

pub fn execute_reference_join(x: u64, y: u64) -> u64 {
    let a = [x, y];
    *(match &a as &[u64] {
        [] => &x,
        [only] => only,
        [_, .., last] => last,
    })
}

// These valid Rust forms retain their existing direct-producer refusals. The
// new lane does not erase guards, literal tests, mutable borrows or alternatives.
pub fn refuse_mutable(a: &mut [u16]) -> u16 {
    match a { [] => 0, [first, ..] => *first }
}

pub fn refuse_guard(a: &[u16], condition: bool) -> u16 {
    match a { [first, ..] if condition => *first, _ => 0 }
}

pub fn refuse_literal(a: &[u16]) -> u16 {
    match a { [1, ..] => 7, _ => 9 }
}

pub fn refuse_or(a: &[u16]) -> u16 {
    match a { [x] | [x, _] => *x, _ => 0 }
}

pub fn refuse_copied_binding(a: &[u16]) -> u16 {
    match a { &[x] => x, _ => 0 }
}

// Element projections remain borrow-tainted at the result join; this change
// does not invent a caller-outlives class for slice interior references.
pub fn refuse_reference_escape<'a>(a: &'a [u64], fallback: &'a u64) -> &'a u64 {
    match a { [] => fallback, [first, ..] => first }
}

// Fat-pointer result joins retain their pre-existing unsupported boundary.
pub fn refuse_fat_result(a: &[u64]) -> &[u64] {
    match a { [] => a, [_first, tail @ ..] => tail }
}

// A Unit match can still select a fat pointer through an outer local. The
// fresh local join must retain the unsupported boundary, including laundering
// the rest reference through an inner fat-pointer result join.
pub fn refuse_fat_local_escape(a: &[u64]) -> &[u64] {
    let mut tail = a;
    match a { [] => {}, [_first, rest @ ..] => tail = rest }
    tail
}

pub fn refuse_fat_local_read(a: &[u64]) -> usize {
    let mut tail = a;
    match a { [] => {}, [_first, rest @ ..] => tail = rest }
    tail.len()
}

pub fn refuse_fat_local_nested(a: &[u64], choose: bool) -> usize {
    let mut tail = a;
    match a { [] => {}, [_first, rest @ ..] => tail = if choose { rest } else { a } }
    tail.len()
}

pub fn dead_fat_local_join(a: &[u64]) -> u64 {
    let mut tail = a;
    match a { [] => {}, [_first, rest @ ..] => tail = rest }
    tail = a;
    53
}

// Returning directly from all arms avoids the outer result/local fences.
pub fn refuse_fat_inner_return(a: &[u64], choose: bool) -> &[u64] {
    match a {
        [] => return a,
        [_first, rest @ ..] => return if choose { rest } else { a },
    };
    a
}

// A pre-existing caller join is outside the matcher-owned block-ID range.
pub fn prior_fat_join_before_match(a: &[u64], b: &[u64], choose: bool) -> u64 {
    let selected = if choose { a } else { b };
    match a { [] => selected.len() as u64, [_first, ..] => selected.len() as u64 }
}

pub fn dead_fat_join_inside_match(a: &[u64], choose: bool) -> u64 {
    match a {
        [] => 0,
        [_first, rest @ ..] => {
            let mut unused = if choose { rest } else { a };
            unused = a;
            59
        }
    }
}

// Both the exact pair and the later prefix/rest pattern match this storage.
// Source order must select the suffix payload, not the prefix payload.
pub fn execute_overlap(x: u64, y: u64) -> u64 {
    let a = [x, y];
    match &a as &[u64] {
        [] => 47,
        [_, last] => *last,
        [first, ..] => *first,
    }
}
