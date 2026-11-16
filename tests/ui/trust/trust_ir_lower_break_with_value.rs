//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off --crate-type=lib
// wave-BV: VALUE-PRODUCING loops. `let r = loop { .. break v .. }` gives the
// exit block a leading RESULT param — `[result] ++ carried` (the if-join
// `[result?] ++ merged` convention) — and every `break v` prepends its
// lowered value to the exit args. Rust's typing makes the protocol total: a
// non-unit loop's every `break` carries a value of the loop's type, and a
// no-result loop may only discard a value the TYPE SYSTEM proves is unit
// (`break ()`) — anything else keeps the fail-closed `Break(with value)`
// tag, so the loop-match lane's own conventions are untouched. A borrow-ptr
// break value refuses (`Break(borrow ptr value)` — the exit param would
// launder it past the escape ledgers). This tag co-blocked 37 bodies at
// landing — every `.await` desugar's `Ready(v) => break v` is one.

// Let-bound loop value with a carried local.
pub fn find_pow(n: u64) -> u64 {
    let mut p = 1u64;
    let r = loop {
        if p >= n {
            break p;
        }
        p *= 2;
    };
    r
}

// Tail-position loop value: the result param IS the fn's return.
pub fn first_gap(mut x: i64) -> i64 {
    loop {
        if x % 7 == 3 {
            break x;
        }
        x += 1;
    }
}

// `break ()` in a unit loop: the value is the type-proven unit no-value,
// lowered for effects only, and the exit carries only the carried locals.
pub fn unit_break_value() -> i64 {
    let mut i = 0;
    loop {
        i += 1;
        if i > 3 {
            break ();
        }
    }
    i
}

// Two breaks, one loop: both prepend their own value at their own edge.
pub fn two_exits(a: u32, b: u32) -> u32 {
    let mut i = 0u32;
    loop {
        if i == a {
            break i;
        }
        if i == b {
            break b;
        }
        i += 1;
    }
}
