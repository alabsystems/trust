//! First-class contract clauses whose predicate cannot constrain what the
//! clause position promises. The clauses here are span-only verifier
//! vocabulary, so the fixture pins what the lint reads out of the AST alone —
//! proof is off and no verdict exists for it to consult.
#![warn(clippy::trust_contract_smell)]
#![allow(dead_code)]

// A postcondition over entry values only: it restates the precondition and
// says nothing about the value the caller receives.
fn restated_precondition(x: u32, y: u32) -> u32
    requires x <= 1000
    ensures x <= 1000
    //~^ trust_contract_smell
{
    x + y
}

// `result` names the output record, so the postcondition constrains the call.
fn names_result(x: u32, y: u32) -> u32
    requires x <= 1000
    ensures result >= x
{
    x + y
}

// A primed output is the post-state of a `&mut` borrow.
fn withdraw(balance: &mut u64, amount: u64)
    requires *balance >= amount
    ensures balance' == balance - amount
{
    *balance -= amount;
}

// A precondition built only from literals admits every call.
fn vacuous_precondition(x: u32) -> u32
    requires true
    //~^ trust_contract_smell
    ensures result == x
{
    x
}

// `false` is the same defect in the other direction: no call can satisfy it.
fn unsatisfiable_precondition(x: u32) -> u32
    requires false
    //~^ trust_contract_smell
    ensures result == x
{
    x
}

// The only invariant constrains a bound the iteration never works with, so it
// carries no induction hypothesis into the loop.
fn loop_invariant_over_constant(n: u32) -> u32 {
    let mut i = 0u32;
    while i < n
        invariant n <= 100
        //~^ trust_contract_smell
    {
        i += 1;
    }
    i
}

// One invariant relating a value the body changes is enough.
fn loop_invariant_over_accumulator(mut n: u32) -> u32 {
    let mut acc = 0u32;
    while n > 0
        invariant acc <= 1000
        decreases n
    {
        acc += 1;
        n -= 1;
    }
    acc
}

// A measure over a value the body cannot reach never decreases.
fn loop_measure_over_constant(mut n: u32, limit: u32) -> u32 {
    let mut acc = 0u32;
    while n > 0
        invariant acc <= 1000
        decreases limit
        //~^ trust_contract_smell
    {
        acc += 1;
        n -= 1;
    }
    acc
}

// A literal measure is the same defect with no name at all.
fn loop_measure_literal(n: u32) -> u32 {
    let mut i = 0u32;
    while i < n
        decreases 3
        //~^ trust_contract_smell
    {
        i += 1;
    }
    i
}

// Expansion-authored clauses belong to the macro, not to the caller who cannot
// rewrite them.
macro_rules! vacuous_contract_fn {
    ($name:ident) => {
        fn $name(x: u32) -> u32
            requires true
        {
            x
        }
    };
}

vacuous_contract_fn!(from_macro);

fn main() {}
