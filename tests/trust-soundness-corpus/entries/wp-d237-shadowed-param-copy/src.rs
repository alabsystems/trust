//@ expect: reject
//@ mechanism: trust-soundness-corpus entry wp-d237-shadowed-param-copy; the corpus runner reads per-function credits,
//@ mechanism: not this case's verdict (see tests/trust-soundness-corpus/README.md).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ > 0 && x@ < 100)]
pub fn pa2(x: i32) {
    let y = x;
    let x = 0i32;
    proof_assert!(y == x);
}

// Twin (va1): the shadowing binding read as itself.
#[requires(x@ > 0)]
pub fn va1(x: i32) {
    let x = 0i32;
    proof_assert!(x@ == 0);
}
