#![expect(incomplete_features)]
#![feature(explicit_tail_calls)]

use std::sync::atomic::{AtomicUsize, Ordering};

static LOCAL_DROPS: AtomicUsize = AtomicUsize::new(0);
static OWNED_ARGUMENT_DROPS: AtomicUsize = AtomicUsize::new(0);

fn identity(x: u8) -> u8 {
    x
}

fn tail_identity(x: u8) -> u8
    ensures result == x
{
    become identity(x);
}

#[inline(never)]
fn panics() -> u8 {
    panic!("tail callee panic")
}

fn tail_panics() -> u8
    ensures result == 0
{
    become panics();
}

struct LocalDrop;

impl Drop for LocalDrop {
    fn drop(&mut self) {
        LOCAL_DROPS.fetch_add(1, Ordering::SeqCst);
    }
}

#[inline(never)]
fn observe_local_drop(x: u8) -> u8 {
    assert_eq!(
        LOCAL_DROPS.load(Ordering::SeqCst),
        1,
        "the tail caller's local must be dropped before the callee starts"
    );
    x
}

fn tail_with_local_drop(x: u8) -> u8
    ensures result == x
{
    let _local = LocalDrop;
    become observe_local_drop(x);
}

struct OwnedArgument;

impl Drop for OwnedArgument {
    fn drop(&mut self) {
        OWNED_ARGUMENT_DROPS.fetch_add(1, Ordering::SeqCst);
    }
}

#[inline(never)]
fn consume_owned_argument(argument: OwnedArgument, x: u8) -> u8 {
    drop(argument);
    x
}

fn tail_with_owned_argument(argument: OwnedArgument, x: u8) -> u8
    ensures result == x
{
    become consume_owned_argument(argument, x);
}

fn tail_countdown(n: u8) -> u8
    ensures result == 0
    decreases n
{
    if n == 0 {
        return 0;
    }
    become tail_countdown(n - 1);
}

#[test]
fn tail_return_runs_the_certified_postcondition() {
    assert_eq!(tail_identity(9), 9);
}

#[test]
fn expanded_tail_call_keeps_caller_unwind_semantics() {
    assert!(std::panic::catch_unwind(tail_panics).is_err());
}

#[test]
fn expanded_tail_call_preserves_local_drop_order() {
    LOCAL_DROPS.store(0, Ordering::SeqCst);
    assert_eq!(tail_with_local_drop(11), 11);
    assert_eq!(LOCAL_DROPS.load(Ordering::SeqCst), 1);
}

#[test]
fn expanded_tail_call_moves_owned_arguments_exactly_once() {
    OWNED_ARGUMENT_DROPS.store(0, Ordering::SeqCst);
    assert_eq!(tail_with_owned_argument(OwnedArgument, 13), 13);
    assert_eq!(OWNED_ARGUMENT_DROPS.load(Ordering::SeqCst), 1);
}

#[test]
fn tail_recursion_runs_decreases_and_ensures_monitors() {
    assert_eq!(tail_countdown(4), 0);
}
