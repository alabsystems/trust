// Regression test for rust-lang#119823.
// Miscompilation with MIR inlining and drop: when the MIR inliner
// substituted a function body that contained drop logic, it could
// incorrectly place or duplicate drop calls. This caused:
//
// 1. Double-free: a value dropped both at the inlined site and at
//    the original drop point
// 2. Missing drop: a value's destructor never executed because the
//    inliner replaced the drop with a no-op
// 3. Drop order inversion: destructors ran in the wrong order after
//    inlining rearranged the control flow
//
// The key trigger was inlining a function that takes ownership of a
// value with a non-trivial Drop impl, combined with control flow
// (if/match/loop) in the inlined body.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//@ build-pass
//@ compile-flags: -C opt-level=2 -Z mir-opt-level=2

#![allow(dead_code)]

use std::cell::RefCell;
use std::rc::Rc;

// Shared drop counter to verify correct drop behavior at compile time.
#[derive(Clone)]
struct DropCounter {
    log: Rc<RefCell<Vec<&'static str>>>,
    name: &'static str,
}

impl Drop for DropCounter {
    fn drop(&mut self) {
        self.log.borrow_mut().push(self.name);
    }
}

// Function that takes ownership and conditionally drops — the pattern
// that triggers incorrect inlining of drop logic.
#[inline(always)] // Force inlining to trigger the bug.
fn consume_conditionally(val: DropCounter, keep: bool) -> Option<DropCounter> {
    if keep {
        Some(val)
    } else {
        drop(val);
        None
    }
}

// Function with multiple drop paths through a match.
#[inline(always)]
fn consume_with_match(a: DropCounter, b: DropCounter, choice: u8) -> DropCounter {
    match choice {
        0 => {
            drop(b);
            a
        }
        1 => {
            drop(a);
            b
        }
        _ => {
            // Drop both, return a new one.
            let log = a.log.clone();
            drop(a);
            drop(b);
            DropCounter { log, name: "new" }
        }
    }
}

// Loop with drop inside — inlining this must not lose the per-iteration drop.
#[inline(always)]
fn process_in_loop(log: &Rc<RefCell<Vec<&'static str>>>, count: usize) {
    for i in 0..count {
        let name = match i {
            0 => "loop-0",
            1 => "loop-1",
            2 => "loop-2",
            _ => "loop-n",
        };
        let _guard = DropCounter {
            log: log.clone(),
            name,
        };
        // Guard dropped at end of each iteration.
    }
}

// Nested function calls with ownership transfer.
#[inline(always)]
fn transfer_ownership(val: DropCounter) -> DropCounter {
    let intermediate = DropCounter {
        log: val.log.clone(),
        name: "intermediate",
    };
    drop(intermediate); // Should drop "intermediate" here.
    val // Original value returned, NOT dropped here.
}

fn main() {
    // Test 1: Conditional drop — "keep" path should not drop.
    {
        let log = Rc::new(RefCell::new(Vec::new()));
        let val = DropCounter { log: log.clone(), name: "cond" };
        let result = consume_conditionally(val, true);
        assert!(result.is_some());
        assert!(log.borrow().is_empty()); // Not dropped yet.
        drop(result);
        assert_eq!(&*log.borrow(), &["cond"]); // Dropped exactly once.
    }

    // Test 2: Conditional drop — "discard" path should drop exactly once.
    {
        let log = Rc::new(RefCell::new(Vec::new()));
        let val = DropCounter { log: log.clone(), name: "discard" };
        let result = consume_conditionally(val, false);
        assert!(result.is_none());
        assert_eq!(&*log.borrow(), &["discard"]);
    }

    // Test 3: Match with multiple drop paths.
    {
        let log = Rc::new(RefCell::new(Vec::new()));
        let a = DropCounter { log: log.clone(), name: "a" };
        let b = DropCounter { log: log.clone(), name: "b" };
        let result = consume_with_match(a, b, 0);
        assert_eq!(&*log.borrow(), &["b"]); // b dropped, a kept.
        assert_eq!(result.name, "a");
        drop(result);
        assert_eq!(&*log.borrow(), &["b", "a"]);
    }

    // Test 4: Match path 1 — opposite drop order.
    {
        let log = Rc::new(RefCell::new(Vec::new()));
        let a = DropCounter { log: log.clone(), name: "a" };
        let b = DropCounter { log: log.clone(), name: "b" };
        let result = consume_with_match(a, b, 1);
        assert_eq!(&*log.borrow(), &["a"]); // a dropped, b kept.
        assert_eq!(result.name, "b");
        drop(result);
        assert_eq!(&*log.borrow(), &["a", "b"]);
    }

    // Test 5: Loop drops — each iteration must drop its guard.
    {
        let log = Rc::new(RefCell::new(Vec::new()));
        process_in_loop(&log, 3);
        assert_eq!(&*log.borrow(), &["loop-0", "loop-1", "loop-2"]);
    }

    // Test 6: Ownership transfer — intermediate dropped, original returned.
    {
        let log = Rc::new(RefCell::new(Vec::new()));
        let val = DropCounter { log: log.clone(), name: "original" };
        let returned = transfer_ownership(val);
        assert_eq!(&*log.borrow(), &["intermediate"]);
        assert_eq!(returned.name, "original");
        drop(returned);
        assert_eq!(&*log.borrow(), &["intermediate", "original"]);
    }
}
