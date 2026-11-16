#![allow(dead_code)]
#![feature(contracts, register_tool)]
#![register_tool(trust)]
use core::contracts::requires;
enum Kind {
    Precondition,
    Postcondition,
}
#[must_use]
fn original(kind: Kind) -> bool {
    matches!(kind, Kind::Precondition)
}
fn stolen(kind: Kind) -> bool {
    matches!(kind, Kind::Postcondition)
}
#[requires(false)]
fn authored(_kind: Kind) -> bool {
    true
}
#[trust::requires = "false"]
fn legacy_authored(_kind: Kind) -> bool {
    true
}
fn other(kind: Kind, _flag: bool) -> bool {
    original(kind)
}

fn wrong_owner(_kind: Kind) -> bool {
    true
}

fn wrong_instance(_kind: Kind) -> bool {
    true
}

fn wrong_promoted(_kind: Kind) -> bool {
    true
}

fn wrong_population(_kind: Kind) -> bool {
    true
}

fn wrong_type(_kind: Kind) -> bool {
    true
}

fn wrong_return(_kind: Kind) -> bool {
    true
}

fn wrong_structure(_kind: Kind) -> bool {
    true
}

fn wrong_bound(_kind: Kind) -> bool {
    true
}

fn wrong_unused_type(_kind: Kind, _unused: bool) -> bool {
    true
}

fn loop_authored(_kind: Kind) -> bool {
    let mut i = 0;
    while i < 1
        invariant false
    {
        i += 1;
    }
    true
}

fn unavailable(_kind: Kind) -> bool {
    false
}
