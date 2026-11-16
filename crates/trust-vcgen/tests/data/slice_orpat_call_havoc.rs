//! Source of the `slice_orpat_*_mir.json` fixtures
//! (tests/slice_orpat_call_havoc_realmir.rs). SLICE-LEN-CALL-HAVOC-1.
fn f1(x: i64, y: i64) -> bool { x < y }
fn f2(x: i64) -> bool { x > 0 }

pub fn op(name: &str, args: &[i64]) -> Option<bool> {
    Some(match (name, args) {
        ("set_in", [x, set]) | ("set_insert", [set, x]) => f1(*set, *x),
        ("set_union" | "set_diff" | "set_intersect" | "set_subseteq", [left, right]) => f1(*left, *right),
        ("set_big_union", [sets]) => f2(*sets),
        _ => false,
    })
}

pub fn op_simple(name: &str, args: &[i64]) -> bool {
    match (name, args) {
        ("set_union" | "set_diff", [left, right]) => f1(*left, *right),
        _ => false,
    }
}

// COUNTER: the arm guarantees len == 2, but index 2 is out of range.
pub fn orpat_oob(name: &str, args: &[i64]) -> i64 {
    match (name, args) {
        ("set_union" | "set_diff", [_, _]) => args[2],
        _ => 0,
    }
}

#[inline(never)]
fn reseat(s: &mut &[i64]) { *s = &[]; }

// COUNTER: a callee reseats the slice through `&mut s` after the length test.
pub fn reseat_after_check(args: &[i64]) -> i64 {
    let mut s: &[i64] = args;
    if s.len() == 2 {
        reseat(&mut s);
        return s[1];
    }
    0
}

#[inline(never)]
unsafe fn reseat_raw(p: *mut &[i64]) { unsafe { *p = &[]; } }

// COUNTER: the same reseat through a raw pointer taken before the check.
pub fn reseat_raw_after_check(args: &[i64]) -> i64 {
    let mut s: &[i64] = args;
    let p = &raw mut s;
    if s.len() == 2 {
        unsafe { reseat_raw(p) };
        return s[1];
    }
    0
}

// COUNTER: a `&mut &[i64]` parameter's pointee is reseated by a callee.
pub fn param_pointee_reseat(p: &mut &[i64]) -> i64 {
    if p.len() == 2 {
        reseat(p);
        return p[1];
    }
    0
}

// COUNTER: a slice pattern then a call that reseats the matched slot.
pub fn pat_then_reseat(name: &str, args: &[i64]) -> i64 {
    let mut s: &[i64] = args;
    match (name, s) {
        ("set_union" | "set_diff", [_, _]) => {
            reseat(&mut s);
            s[1]
        }
        _ => 0,
    }
}

// POSITIVE: a `&mut [i64]` parameter keeps its length across a call that receives it.
#[inline(never)]
fn touch(s: &mut [i64]) { if let Some(x) = s.first_mut() { *x = 1; } }
pub fn mut_slice_param_call(s: &mut [i64]) -> i64 {
    if s.len() == 2 {
        touch(s);
        return s[1];
    }
    0
}

pub fn orpat_ok(name: &str, args: &[i64]) -> bool {
    match (name, args) {
        ("set_union" | "set_diff", [left, right]) => f1(*left, *right),
        _ => false,
    }
}
