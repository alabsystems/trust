// Forwarded pointer parameters, each passed into a call and, in most targets, read again
// afterwards. Every target must be installed from trust-ir; see rmake.rs. The comment on each
// target says what the wave-8a producer emitted for it, measured on a stage-1 compiler built
// from bd8681c2628 (2026-09-30) with this file's flags.

#[inline(never)]
pub fn bump(x: &mut u64) {
    *x += 1;
}

#[inline(never)]
pub fn inc(x: &mut u64) -> u64 {
    *x += 1;
    *x
}

#[inline(never)]
pub fn get(x: &u64) -> u64 {
    *x
}

#[inline(never)]
pub fn get2(x: &u64, y: &u64) -> u64 {
    *x + *y
}

// A shared reference forwarded twice. Was `get(move _1)` twice.
#[inline(never)]
pub fn shared_twice(x: &u64) -> u64 {
    get(x) + get(x)
}

// A shared reference forwarded twice into ONE call. Was `get2(move _1, move _1)`.
#[inline(never)]
pub fn shared_pair(x: &u64) -> u64 {
    get2(x, x)
}

// A shared reference forwarded, then loaded through. Was `get(move _1)` then `copy (*_1)`.
#[inline(never)]
pub fn shared_then_load(x: &u64) -> u64 {
    get(x) + *x
}

// A unique reference forwarded twice. Was `inc(move _1)` twice.
#[inline(never)]
pub fn mut_value_twice(x: &mut u64) -> u64 {
    inc(x) + inc(x)
}

// A unique reference forwarded into two different callees. Was `inc(move _1)`, `bump(move _1)`.
#[inline(never)]
pub fn mut_value_then_bump(x: &mut u64) -> u64 {
    let a = inc(x);
    bump(x);
    a
}

// A unique reference forwarded inside a loop: one lexical use, many dynamic ones. Was
// `bump(move _1)` on the loop body's path back to its header.
#[inline(never)]
pub fn mut_loop(x: &mut u64, n: u32) {
    let mut i = 0;
    while i < n {
        bump(x);
        i += 1;
    }
}

// A unique reference forwarded on one arm, then again after the join. Was `inc(move _1)` on the
// arm and `inc(move _1)` after it.
#[inline(never)]
pub fn mut_branch_then(x: &mut u64, c: bool) -> u64 {
    let a = if c { inc(x) } else { 7 };
    a + inc(x)
}

// Controls: each forward is the parameter's last use on every path, so a move is valid there.

#[inline(never)]
pub fn mut_branch(x: &mut u64, c: bool) -> u64 {
    if c { inc(x) } else { 7 }
}

#[inline(never)]
pub fn mut_value_once(x: &mut u64) -> u64 {
    inc(x)
}
