//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: ERROR
//! NAME-RESOLUTION NEGATIVE of `e9_cited_island_def_discharge`: an island
//! definition whose name a PARAMETER of the specified function also bears.
//!
//! In a clause, a parameter shadows an island definition of the same name — the
//! clause means what Rust means. Here that reading is FALSE: `shadowed` returns
//! the constant 7 whatever it is handed, so `result == seven` (the parameter)
//! does not hold. Under the WRONG reading — `seven` as the island constant —
//! the clause is TRUE (`7 == 7`) and `seven_refl` would appear to prove it. The
//! cited lanes therefore refuse to offer an island definition under a name the
//! function's own parameter patterns bind (`admit_clause_island_definitions`),
//! for called and bare spellings alike and whatever the parameter's type, and
//! the refusal is reported on the citation error.
//!
//! Kept in its own file so that this island's zero-arity spelling can never
//! taint the environment the sibling twins are judged in.
//!
//! `dont-require-annotations: ERROR` tolerates only the secondary
//! strict-verification errors; the primary refusal is pinned below.

// The parameter exists to SHADOW; the body deliberately ignores it.
#![allow(unused_variables)]

clean {
    def seven : UInt64 := 7
    theorem seven_refl : seven = seven := rfl
}

pub fn shadowed(seven: u64) -> u64
    ensures result == seven by seven_refl
    //~^ ERROR citation `seven_refl` failed the strict Clean statement/certification audit
    //~| NOTE the Clean island definition `seven` named in this clause was not admitted into it
{
    7
}

fn main() {
    let _ = shadowed(1);
}
