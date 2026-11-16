//@ edition: 2021
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify -Ztrust-verify-level=2 -Ztrust-verify-profile=unix_hardened -Ztrust-verify-include-dependencies=yes -Ztrust-ir-lower=strict --crate-type=lib
#![no_std]
#![allow(incomplete_features)]
#![feature(loop_match)]

// Valid Rust returns 29. The inner loop has no own break; taking its first
// observed label as its identity would instead attribute an OUTER break to it.
pub fn outer_break_supported() -> u32 {
    'outer: loop {
        loop {
            break 'outer;
        }
    }
    29
}

// Some(n) => n; None => 29. Walking let-else must not steal the outer label.
pub fn outer_break_in_else_supported(value: Option<u32>) -> u32 {
    'outer: loop {
        loop {
            let Some(n) = value else { break 'outer };
            return n;
        }
    }
    29
}

// Some(n) => n; None => 29 after an OUTER continue. The exact target
// scope determines which loop receives the new carried state.
pub fn outer_continue_in_else_supported(value: Option<u32>) -> u32 {
    let mut first = true;
    'outer: loop {
        if !first {
            return 29;
        }
        first = false;
        loop {
            let Some(n) = value else { continue 'outer };
            return n;
        }
    }
}

// Valid Rust returns true: ordinary block break updates state and then the
// loop iterates. The block is NOT the loop; current lowering must refuse the
// unsupported block-value transfer instead of incorrectly exiting with false.
pub fn loop_match_block_break_refused() -> bool {
    //~^ ERROR Break(non-innermost label)
    let mut state = false;
    #[loop_match]
    'done: loop {
        state = 'next: {
            match state {
                false => break 'next true,
                true => break 'done,
            }
        };
    }
    state
}

// Exact scope identity does not widen the existing nested LoopMatch lane.
pub fn nested_loop_match_refused() -> bool {
    //~^ ERROR Loop(nested)
    let mut state = false;
    loop {
        #[loop_match]
        'done: loop {
            state = 'next: {
                match state {
                    false => true,
                    true => break 'done,
                }
            };
        }
        return state;
    }
}
