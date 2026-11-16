//@ check-pass
//@ edition: 2021
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify -Ztrust-verify-level=2 -Ztrust-verify-profile=unix_hardened -Ztrust-verify-include-dependencies=yes -Ztrust-ir-lower=strict --crate-type=lib
#![no_std]
#![allow(incomplete_features)]
#![feature(loop_match)]

// Some(_) => 7; None => 29. The only break is in the let-else body.
pub fn sole_else_break(value: Option<u32>) -> u32 {
    loop {
        let Some(_) = value else { break };
        return 7;
    }
    29
}

pub fn sole_else_break_match(value: Option<u32>) -> u32 {
    loop {
        match value {
            Some(_) => return 7,
            None => break,
        }
    }
    29
}

// Some(n) => n; None => 29 after exactly one continue. There is NO loop break.
// The never-typed Loop can be adjusted to the function's u32 result type.
pub fn sole_else_continue(value: Option<u32>) -> u32 {
    let mut first = true;
    loop {
        let Some(n) = value else {
            if first {
                first = false;
                continue;
            }
            return 29;
        };
        return n;
    }
}

pub fn sole_else_continue_match(value: Option<u32>) -> u32 {
    let mut first = true;
    loop {
        match value {
            Some(n) => return n,
            None => {
                if first {
                    first = false;
                    continue;
                }
                return 29;
            }
        }
    }
}

// Exactly one continue in an ordinary let initializer, then return 31.
pub fn initializer_continue() -> u32 {
    let mut first = true;
    loop {
        let result = {
            if first {
                first = false;
                continue;
            }
            31
        };
        return result;
    }
}

// Both loops are never-typed. No invented break scope or nested-scope sentinel
// is needed: the real function Return leaves both. Some(n) => n; None => 29.
pub fn nested_return(value: Option<u32>) -> u32 {
    loop {
        loop {
            let Some(n) = value else { return 29 };
            return n;
        }
    }
}

// The same source spelling names TWO HIR loop identities. The first break
// must leave only the inner loop, so execution reaches result = 17.
#[allow(unused_labels)]
pub fn shadowed_loop_labels() -> u32 {
    let mut result = 0;
    'next: loop {
        'next: loop {
            //~^ WARN label name `'next` shadows a label name that is already in scope
            break 'next;
        }
        result = 17;
        break 'next;
    }
    result
}

// The first syntactic break names a BLOCK. The loop's own break returns 19.
pub fn block_label_before_loop_exit() -> u32 {
    loop {
        let result = 'value: { break 'value 19 };
        break result;
    }
}

// ConstContinue names the state-update block. The sole real LOOP break is
// inside let-else in the other arm. Some(n) => n; None => 29.
pub fn loop_match_else_exit(value: Option<u32>) -> u32 {
    let mut state = false;
    #[loop_match]
    'done: loop {
        state = 'next: {
            match state {
                false => {
                    #[const_continue]
                    break 'next true;
                }
                true => {
                    let Some(n) = value else { break 'done };
                    return n;
                }
            }
        };
    }
    29
}

pub fn loop_match_plain_twin(value: Option<u32>) -> u32 {
    let mut state = false;
    'done: loop {
        match state {
            false => {
                state = true;
                continue;
            }
            true => {
                let Some(n) = value else { break 'done };
                return n;
            }
        }
    }
    29
}
