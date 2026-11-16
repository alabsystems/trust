//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify -Ztrust-verify-level=2 -Ztrust-verify-profile=unix_hardened -Ztrust-verify-include-dependencies=yes -Ztrust-ir-lower=strict --crate-type=lib
#![no_std]

// A single tag branch cannot replace the extra scalar payload comparison.
pub fn literal_payload(value: Option<u32>) -> u32 {
    //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    let Some(7) = value else {
        return 0;
    };
    1
}

// A nested tag test cannot be replaced by only the outer Some test.
pub fn nested_payload(value: Option<Option<u32>>) -> u32 {
    //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    let Some(Some(n)) = value else {
        return 0;
    };
    n
}

// Binding a reference requires the real scrutinee storage and borrow semantics.
pub fn reference_payload(value: Option<u32>) -> u32 {
    //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    let Some(ref n) = value else {
        return 0;
    };
    *n
}

pub enum Choice {
    A(u32),
    B(u32),
    C,
}

// A single case cannot treat the second matching variant as an else branch.
pub fn alternative(value: Choice) -> u32 {
    //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    let (Choice::A(n) | Choice::B(n)) = value else {
        return 0;
    };
    n
}

pub enum Only {
    A(u32),
}

// A synthetic Switch would disagree with rustc's irrefutable binding.
pub fn single_variant(value: Only) -> u32 {
    //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    let Only::A(n) = value else {
        //~^ WARN unreachable `else` clause
        return 0;
    };
    n
}

// Labeled blocks do not carry outer SSA assignments. The existing fence must
// also see an assignment nested in a let-else exit.
pub fn labeled_else_assignment_refused(value: Option<u32>) -> u32 {
    //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    let mut x = 0;
    'out: {
        let Some(_) = value else {
            x = 1;
            break 'out;
        };
    }
    x
}
