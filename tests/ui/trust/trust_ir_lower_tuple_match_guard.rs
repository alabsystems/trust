//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Trust (wave-TG): a GUARDED arm of a tuple match is refutable — its tests
//! (possibly none) pass into a guard block that binds the arm's fields,
//! lowers the guard, and branches to the body on `true` or to the next arm's
//! entry on `false` (the general match lane's `GuardedCatchAll` posture).
//! Every body here carried `TupleMatch(guarded arm)` before the wave;
//! `strict` turns that into a compile error, so this file is the mutation
//! check.
fn order(a: i32, b: i32) -> i32 {
    match (a, b) {
        (x, y) if x > y => 1,
        (x, y) if x < y => -1,
        _ => 0,
    }
}
fn mixed(k: u8, n: u32) -> u32 {
    match (k, n) {
        (0, v) if v > 10 => v - 10,
        (0, v) => v,
        (1, v) if v % 2 == 0 => v / 2,
        (_, v) => v + 1,
    }
}
fn wild(a: u64, b: u64) -> u64 {
    match (a, b) {
        _ if a == b => 0,
        (x, _) => x,
    }
}
fn main() {
    let ok = order(3, 2) == 1
        && order(1, 5) == -1
        && order(4, 4) == 0
        && mixed(0, 25) == 15
        && mixed(0, 5) == 5
        && mixed(1, 8) == 4
        && mixed(1, 7) == 8
        && mixed(2, 1) == 2
        && wild(3, 3) == 0
        && wild(9, 2) == 9;
    std::process::exit(!ok as i32);
}
