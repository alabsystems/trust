//@ compile-flags: -Z trust-verify=off
//@ check-fail
//@ dont-check-compiler-stderr
//! Post-state prime notation (two-language design D2, ruling Q9): in clause
//! positions, one or more `'` immediately following an identifier lex as a
//! prime token — `balance'` names the post-state of `balance`; there is no
//! `old()`. Vanilla adjacency shapes (`x'a'` char literals, `x'static`
//! lifetimes) keep their exact vanilla meaning, including the edition-2021
//! reserved-prefix error for bare adjacency outside clauses.
//!
//! This test disables proof verification intentionally. Recognition of a prime
//! token reserves the syntax for function postconditions, but must not be
//! mistaken for binding an output-state value in one-state loop clauses. The
//! always-on loop elaborator therefore rejects a primed invariant explicitly.

pub fn withdraw(balance: &mut u64, amount: u64)
    requires *balance >= amount
    ensures balance' == balance - amount
{
    *balance -= amount;
}

// Primes compose with the rest of the clause vocabulary.
pub fn transfer(src: &mut u64, dst: &mut u64, amount: u64)
    requires *src >= amount
    ensures src' == src - amount
    ensures dst' == dst + amount
    ensures forall total: u64, src' + dst' == src + dst
{
    *src -= amount;
    *dst += amount;
}

// Prime runs stay as a lossless sequence rather than collapsing into a
// lifetime-shaped sentinel.
pub fn chained(balance: &mut u64)
    ensures balance'' == balance'
{
    *balance += 1;
}

// Raw identifiers take the same adjacency path. This is handled in rustc's
// cooked lexer because the raw lexer deliberately keeps `RawIdent` vanilla.
pub fn raw_identifier(r#type: &mut u64)
    ensures r#type' == *r#type
{
    *r#type += 1;
}

// A loop invariant has no bindable post-state in the current one-state E4
// model. Keeping the token in the grammar does not silently give it meaning.
pub fn drain(mut n: u32) -> u32 {
    let mut moved = 0u32;
    while n > 0
        invariant moved' >= moved //~ ERROR invalid `invariant` clause:
        decreases n
    {
        moved = moved.saturating_add(1);
        n -= 1;
    }
    moved
}

// Vanilla adjacency keeps its meaning everywhere outside clauses.
fn vanilla() -> (char, &'static str) {
    let c = 'a';
    let r = matches!(c, 'a'..='z');
    let s: &'static str = if r { "ok" } else { "no" };
    'outer: for _ in 0..2 {
        break 'outer;
    }
    (c, s)
}

fn main() {
    let mut b = 100u64;
    withdraw(&mut b, 40);
    let (mut s, mut d) = (50u64, 10u64);
    transfer(&mut s, &mut d, 5);
    chained(&mut b);
    raw_identifier(&mut b);
    let _ = drain(3);
    let _ = vanilla();
}
