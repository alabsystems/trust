//@ compile-flags: -Z trust-verify=off
//@ check-pass
//! FIRST-CLASS contract clauses (two-language design D0/D1, R3/E5): `requires` /
//! `ensures` / function-level `decreases` as signature grammar in positions vanilla Rust rejects — no
//! imports, no prelude crate, no attributes. This fixture pins the GRAMMAR
//! (verification is disabled), covering the native verifier-language lane for
//! both plain Rust-shaped and spec-vocabulary (`result`, primed outputs,
//! Lean-shaped typed `forall`/`exists`, `==>`) predicates,
//! plus multi-clause stacking (E1) and coexistence with `where` clauses.
//! Vanilla-collision guard: items NAMED `requires`/`ensures` stay ordinary
//! Rust everywhere else (drop-in invariant 1).

pub fn withdraw(balance: &mut u64, amount: u64)
    requires *balance >= amount
    ensures balance' == balance - amount
{
    *balance -= amount;
}

// Multiple clauses of each kind (E1): conjunction semantics downstream.
pub fn clamp_add(x: u32, y: u32) -> u32
    requires x <= 1000
    requires y <= 1000
    ensures result <= 2000
    ensures result >= x
{
    x + y
}

// Spec vocabulary stays out of Rust typeck via the native span-only lane.
// Quantifiers use Lean-shaped typed binders; `==>` is canonicalized to the
// downstream formula representation. Prime marks are grammar-reserved for a
// future post-state place binding, but semantic verification rejects them
// fail-closed until that binding exists. There is no native `old()` operator or
// bounded function-form quantifier workaround.
pub fn binary_search(xs: &[u32], key: u32) -> Option<usize>
    requires forall i j: usize, i < j ==> i < 10
    ensures exists i: u8, key == key && i == i
{
    xs.iter().position(|&x| x == key)
}

// Clauses coexist with a where-clause (clauses bind before `where`).
pub fn max_of<T>(a: T, b: T) -> T
    requires true
    where
        T: PartialOrd,
{
    if a > b { a } else { b }
}

// `invariant` remains ordinary verifier vocabulary in a signature predicate.
// Function-level `decreases` is instead a top-level clause boundary: it owns
// the recursive-call termination measure rather than being parsed into the
// preceding requires/ensures payload.
pub fn contextual_clause_names(invariant: u32, descent: u32) -> u32
    requires invariant <= descent
    ensures result == invariant + descent
    decreases descent
{
    invariant + descent
}

// Function-level E5 receives the same exact aggregate source sorts as the loop
// lane: collection measures are valid for slice/array parameters, while scalar
// lookalikes are rejected by the early type-admission tests.
pub fn slice_descent(xs: &[u32])
    decreases xs.len()
{
    if let Some((_, rest)) = xs.split_first() {
        slice_descent(rest);
    }
}

pub fn array_measure(xs: &[u32; 4])
    decreases xs.len()
{
    let _ = xs;
}

pub fn raw_slice_pointer_measure(p: *const [u32])
    decreases (*p).len()
{
    let _ = p;
}

// Drop-in invariant 1: `requires`/`ensures` remain ordinary identifiers in
// every vanilla position.
#[allow(dead_code)]
fn requires(x: u32) -> u32 {
    x
}

#[allow(dead_code)]
fn ensures() -> bool {
    true
}

#[allow(dead_code)]
fn decreases(x: u32) -> u32 {
    x
}

fn main() {
    let mut b = 100u64;
    withdraw(&mut b, 40);
    assert_eq!(b, 60);
    let _ = clamp_add(3, 4);
    let _ = binary_search(&[1, 2, 3], 2);
    let _ = max_of(1u8, 2u8);
    let _ = contextual_clause_names(1, 2);
    slice_descent(&[1, 2, 3]);
    array_measure(&[1, 2, 3, 4]);
    raw_slice_pointer_measure(std::ptr::slice_from_raw_parts(std::ptr::null(), 0));
    let _ = requires(1) + decreases(1) + u32::from(ensures());
}
