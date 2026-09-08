//@ edition: 2021
//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-LNS): NESTED loops are admitted under ONE invariant — every
//! non-promoted local the inner loop carries must ALSO be carried by every
//! enclosing loop. Given that, the shipped emission is already correct: the
//! outer back-edge arg for such a local is the inner loop's EXIT block param,
//! defined in a block that dominates the back-edge point.
//!
//! `break`/`continue` stay INNERMOST-ONLY — both match `ctx.scope == label`
//! against `loop_stack.last()` — so multi-level control flow keeps refusing.
//!
//! `nested_carried` is the value pin: `acc` is carried by BOTH loops, and a
//! stale outer back-edge arg would show up here as a wrong sum rather than as
//! a changed tag. `nested_inner_only` pins the refusal direction: `j` is
//! carried by the inner loop alone, so the invariant refuses and the body
//! keeps a tag — it must still COMPUTE correctly, which `run-pass` checks.

pub fn nested_carried() -> u32 {
    let mut acc = 0u32;
    let mut i = 0u32;
    loop {
        if i >= 3 {
            break;
        }
        let mut k = 0u32;
        loop {
            if k >= 2 {
                break;
            }
            acc += i * 10 + k;
            k += 1;
        }
        i += 1;
    }
    acc
}

/// The inner loop introduces its own carried local before the outer one binds
/// it — the invariant refuses, and the answer must still be right.
pub fn nested_inner_only() -> u32 {
    let mut total = 0u32;
    let mut i = 0u32;
    while i < 3 {
        let mut j = 0u32;
        while j < 3 {
            total += 1;
            j += 1;
        }
        i += 1;
    }
    total
}

fn main() {
    assert_eq!(nested_carried(), 0 + 1 + 10 + 11 + 20 + 21);
    assert_eq!(nested_inner_only(), 9);
}
