//@ needs-trust-verify
//@ edition: 2021
//@ revisions: entry_swap_div entry_swap_overflow entry_swap_sub entry_swap_shift
//@ revisions: entry_rotate_div entry_scratch_reuse entry_negation later_block_div
//@ revisions: requires_param neg_min_const neg_min_copy neg_min_then_index swap_div_safe
//@ revisions: swap_overflow_safe single_write last_value_used later_block_safe
//@ revisions: neg_min_plus_one_safe neg_small_const_safe requires_param_kept
//@ revisions: requires_field_kept requires_field_read_first
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[entry_swap_div] check-fail
//@[entry_swap_overflow] check-fail
//@[entry_swap_sub] check-fail
//@[entry_swap_shift] check-fail
//@[entry_rotate_div] check-fail
//@[entry_scratch_reuse] check-fail
//@[entry_negation] check-fail
//@[later_block_div] check-fail
//@[requires_param] check-fail
//@[neg_min_const] check-fail
//@[neg_min_copy] check-fail
//@[neg_min_then_index] check-fail
//@[swap_div_safe] check-pass
//@[swap_overflow_safe] check-pass
//@[single_write] check-pass
//@[last_value_used] check-pass
//@[later_block_safe] check-pass
//@[neg_min_plus_one_safe] check-pass
//@[neg_small_const_safe] check-pass
//@[requires_param_kept] check-pass
//@[requires_field_kept] check-pass
//@[requires_field_read_first] check-pass
//! **The interval environment must bound a local at every statement, not only at block
//! entries (trust-interval-drop-havoc, independent review, 2026-10-09).**
//!
//! The discharge reads a versioned name (`b#s0_1`: `b` as one statement left it) through
//! the whole-function interval environment's entry for the bare `b`. That environment was
//! the join of the fixpoint's block ENTRY states, and a value written and overwritten
//! between two statements of one block is no block's entry state. In every check-fail
//! revision below a local holds a value that only a copy remembers; the environment bound
//! the local by the values it has at block boundaries, the obligation's own `copy == local`
//! tie evaluated false, the violation looked unreachable and was DISCHARGED at generation:
//! withheld from ay and published `runtime_checked`. Plain safe code: no pointer, no call,
//! no drop.
//!
//! The `neg_min_*` revisions are the same gap at an edge instead of a statement. rustc
//! lowers a checked `-y` as `_c = y == MIN; assert(!_c)`, and the interval fixpoint reads
//! the assert's success edge back onto the operand. With the operand pinned to `MIN` that
//! edge leaves it NO value, the edge was the only state the environment had for it, and
//! an environment with an empty bound is `false` as a hypothesis: ay then PROVED the
//! negation obligation (`1 proved ... out of 1 obligation(s)`).
//!
//! # Before (main `1a7d3be9a6` with the interval-fixpoint budget fix, probe rounds `ep-r1`
//! and `ep-r2`; the reviewed branch `9a9419771e` and main `4e95b0c512` answer the same)
//!
//! Each check-fail revision except `later_block_div` built rc=0 under the default policy
//! and its driver panicked (exit 101) on every run. `later_block_div` was refuted before
//! as well and is the reference point: rustc copies a later block's reads through fresh
//! temporaries, which the environment never bounded below their type range, so the same
//! overwrite outside the entry block did not reach a discharge at the default MIR opt
//! level (it does at `-Zmir-opt-level=2`; the crate test
//! `a_value_overwritten_inside_a_later_block_is_in_the_environment` pins the MIR shape
//! without those temporaries).
//!
//! # After
//!
//! The environment also joins the value every statement leaves in what it writes
//! (`abstract_interp::transfer::join_statement_values`), so it bounds the local by every
//! value it holds, the tie is undecided, the obligation reaches ay, and ay refutes it.
//! The check-pass controls are the same shapes with values that cannot fail, and the
//! facts the environment must keep: a local written once, a local whose last value is the
//! one used, a parameter under a `requires` that nothing overwrites.
//!
//! `requires_field_kept` and `requires_field_read_first` are the cost the first form of the
//! join had, measured on stage 1 of `d712442cbe` (probe round `ep-r3`): a `requires` that
//! bounds a FIELD from one side gives the copy of the field an interval unbounded on the
//! other side, the join read that as "not a value of the type" and widened it to the whole
//! type range, and the branch the precondition makes dead was dispatched and refuted with a
//! counterexample the precondition excludes (`[overflow:add] FAILED`, on a program main
//! builds). The join now takes such an interval's part within the type's range
//! (`abstract_interp::transfer::as_value_of_type`), and both build again.

// rustc's own deny-by-default lints see through the constant shapes below. They are allowed
// here so that each revision's verdict is the verifier's and not the lint's.
#![allow(unused, unconditional_panic, arithmetic_overflow)]

// Swap two constant-initialised locals through a temporary in the entry block; `a` is 0 at the
// division.
#[cfg(entry_swap_div)]
pub fn f(k: u32) -> u32 {
    //[entry_swap_div]~^ NOTE [divzero] FAILED
    let mut a = 1u32;
    let mut b = 0u32;
    let t = a;
    a = b;
    b = t;
    (k / a).wrapping_add(b)
}

// Swap two constant-initialised locals through a temporary in the entry block; `a` is `u32::MAX`
// at the add.
#[cfg(entry_swap_overflow)]
pub fn f(k: u32) -> u32 {
    //[entry_swap_overflow]~^ NOTE [overflow:add] FAILED
    let mut a = 0u32;
    let mut b = u32::MAX;
    let t = a;
    a = b;
    b = t;
    (a + 1).wrapping_add(b).wrapping_add(k)
}

// Swap two constant-initialised locals through a temporary in the entry block; `b` is 0 at the
// subtraction.
#[cfg(entry_swap_sub)]
pub fn f(k: u32) -> u32 {
    //[entry_swap_sub]~^ NOTE [overflow:sub] FAILED
    let mut a = 0u32;
    let mut b = 9u32;
    let t = a;
    a = b;
    b = t;
    (b - 1).wrapping_add(a).wrapping_add(k)
}

// Swap two constant-initialised locals through a temporary in the entry block; `a` is 40 at the
// shift.
#[cfg(entry_swap_shift)]
pub fn f(k: u32) -> u32 {
    //[entry_swap_shift]~^ NOTE [shift:left] FAILED
    let mut a = 1u32;
    let mut b = 40u32;
    let t = a;
    a = b;
    b = t;
    (k << a).wrapping_add(b)
}

// A three-way rotation; `c` is 0 at the division.
#[cfg(entry_rotate_div)]
pub fn f(k: u32) -> u32 {
    //[entry_rotate_div]~^ NOTE [divzero] FAILED
    let mut a = 0u32;
    let mut b = 1u32;
    let mut c = 2u32;
    let t = a;
    a = b;
    b = c;
    c = t;
    (k / c).wrapping_add(a).wrapping_add(b)
}

// One scratch local reused for two unrelated values; the first is read before the reuse.
#[cfg(entry_scratch_reuse)]
pub fn f(k: u32) -> u32 {
    //[entry_scratch_reuse]~^ NOTE [overflow:mul] FAILED
    let mut scratch = 2_000_000_000u32;
    let w = scratch;
    scratch = 1;
    (w * 3).wrapping_add(scratch).wrapping_add(k)
}

// `x` is `i32::MIN` when `y` copies it, then 0.
#[cfg(entry_negation)]
pub fn f(k: i32) -> i32 {
    //[entry_negation]~^ NOTE [negation] FAILED
    let mut x = i32::MIN;
    let y = x;
    x = 0;
    (-y).wrapping_add(x).wrapping_add(k)
}

// Reference (refuted before too): every local is defined in the entry block, and `t` is 1 only
// between two statements of a later block, where `d` copies it.
#[cfg(later_block_div)]
pub fn f(k: u32) -> u32 {
    //[later_block_div]~^ NOTE [divzero] FAILED
    let mut a = 1u32;
    let mut t = 7u32;
    let mut d = 1u32;
    let mut z = 0u32;
    if k > 3 {
        z = 1;
    }
    t = a;
    d = t;
    t = 7;
    (k / (d - 1)).wrapping_add(z).wrapping_add(t)
}

// A parameter bounded by a `requires`, overwritten, copied and restored: the precondition's bound
// says nothing about the copy.
#[cfg(requires_param)]
#[trust::requires(k < 3)]
pub fn f(mut k: u32) -> u32 {
    //[requires_param]~^ NOTE [overflow:add] FAILED
    k = 4_000_000_000;
    let t = k;
    k = 0;
    (t + 1_000_000_000).wrapping_add(k)
}

// The negation check ends the entry block and its operand is `i32::MIN`: the check's success edge
// holds no value for it. Main proved this negation.
#[cfg(neg_min_const)]
pub fn f(k: i32) -> i32 {
    //[neg_min_const]~^ NOTE [negation] FAILED
    let y = i32::MIN;
    (-y).wrapping_add(k)
}

// The same through a copy.
#[cfg(neg_min_copy)]
pub fn f(k: i32) -> i32 {
    //[neg_min_copy]~^ NOTE [negation] FAILED
    let a = i32::MIN;
    let y = a;
    (-y).wrapping_add(k)
}

// The same with an out-of-bounds index after it. The index is dead code behind the panic; the
// negation is not.
#[cfg(neg_min_then_index)]
pub fn f(arr: &[u32; 3], k: i32) -> u32 {
    //[neg_min_then_index]~^ NOTE [negation] FAILED
    let y = i32::MIN;
    let z = -y;
    arr[7].wrapping_add(z as u32).wrapping_add(k as u32)
}

// Control: the swap with the constants exchanged; `a` is 1 at the division.
#[cfg(swap_div_safe)]
pub fn f(k: u32) -> u32 {
    let mut a = 0u32;
    let mut b = 1u32;
    let t = a;
    a = b;
    b = t;
    (k / a).wrapping_add(b)
}

// Control: the swap of 5 and 7; `7 + 1` cannot overflow.
#[cfg(swap_overflow_safe)]
pub fn f(k: u32) -> u32 {
    let mut a = 5u32;
    let mut b = 7u32;
    let t = a;
    a = b;
    b = t;
    (a + 1).wrapping_add(b).wrapping_add(k)
}

// Control: no overwrite at all. A local written once keeps its exact interval.
#[cfg(single_write)]
pub fn f(arr: &[u32; 3], k: u32) -> u32 {
    let d = 4u32;
    let i = 2usize;
    (k / d).wrapping_add(arr[i])
}

// Control: written twice in the entry block, and only the last value is used.
#[cfg(last_value_used)]
pub fn f(k: u32) -> u32 {
    let mut x = 9u32;
    x = 2;
    k / x
}

// Control: the later-block shape dividing by `d` itself, which is 1.
#[cfg(later_block_safe)]
pub fn f(k: u32) -> u32 {
    let mut a = 1u32;
    let mut t = 7u32;
    let mut d = 1u32;
    let mut z = 0u32;
    if k > 3 {
        z = 1;
    }
    t = a;
    d = t;
    t = 7;
    (k / d).wrapping_add(z).wrapping_add(t)
}

// Control: `-(i32::MIN + 1)` is `i32::MAX`.
#[cfg(neg_min_plus_one_safe)]
pub fn f(k: i32) -> i32 {
    let y = i32::MIN + 1;
    (-y).wrapping_add(k)
}

// Control: the negation of a small constant.
#[cfg(neg_small_const_safe)]
pub fn f(k: i32) -> i32 {
    let y = 5i32;
    (-y).wrapping_add(k)
}

// Control: a parameter under a `requires` that nothing overwrites keeps the bound.
#[cfg(requires_param_kept)]
#[trust::requires(k < 3)]
pub fn f(arr: &[u32; 3], k: usize) -> u32 {
    arr[k]
}

// Control: a FIELD under a one-sided `requires`, copied, tested and stored to in one block. The
// branch is dead by the precondition, and the interval of the copy is what says so.
#[cfg(requires_field_kept)]
#[trust::requires(p.0 <= 3)]
pub fn f(mut p: (u32, u32), q: (u32, u32)) -> u32 {
    let big = p.0 >= 10;
    p.0 = 0;
    if big { q.1 + u32::MAX } else { p.0 }
}

// Control: the same, with a whole write of the tuple after the test has read the field.
#[cfg(requires_field_read_first)]
#[trust::requires(p.0 <= 3)]
pub fn f(mut p: (u32, u32), q: (u32, u32)) -> u32 {
    let big = p.0 >= 10;
    p = q;
    p.0 = 0;
    if big { q.1 + u32::MAX } else { p.0 }
}
