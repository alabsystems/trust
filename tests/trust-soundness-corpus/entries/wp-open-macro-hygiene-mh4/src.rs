//@ expect: reject
//@ mechanism: trust-soundness-corpus entry wp-open-macro-hygiene-mh4; the corpus runner reads per-function credits,
//@ mechanism: not this case's verdict (see tests/trust-soundness-corpus/README.md).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

macro_rules! zero_x {
    () => {
        let x = 0i32;
        let _ = x;
    };
}

macro_rules! five_x {
    () => {
        let x = 5i32;
        let _ = x;
    };
}

macro_rules! bump_local {
    () => {
        let mut x = 0i32;
        x += 7;
        let _ = x;
    };
}

macro_rules! mk_y_from_x {
    ($e:expr) => {
        let x = $e;
        let _ = x;
    };
}

pub fn mh4() {
    let x = 1i32;
    {
        bump_local!();
        proof_assert!(x@ == 7);
    }
}

// Twin: the caller's binding read as itself.
pub fn mh4_ok() {
    let x = 1i32;
    {
        bump_local!();
        proof_assert!(x@ == 1);
    }
}
