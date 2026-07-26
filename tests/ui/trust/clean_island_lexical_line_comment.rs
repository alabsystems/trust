//@ compile-flags: -Z trust-verify=off
//@ check-fail
//! Current parser islands are delimited by Rust token trees. A Lean line
//! comment containing `}` is not yet an arbitrary-Lean island surface; it
//! must fail closed instead of silently changing the island boundary.

clean {
    theorem before : 0 = 0 := rfl
    -- }
    theorem after : 0 = 0 := rfl
} //~ ERROR unexpected closing delimiter: `}`

fn main() {}
