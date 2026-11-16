//@ expect: reject
//@ mechanism: trust-soundness-corpus entry wp-open-closure-contract-cs1; the corpus runner reads per-function credits,
//@ mechanism: not this case's verdict (see tests/trust-soundness-corpus/README.md).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
#[requires(x@ == 5)]
#[ensures(true)]
pub fn cs1(x: i32) {
    let x = 0i32;
    let f = #[requires(x@ == 5)]
    move || {
        let _ = x;
    };
    f();
}

// Twin: the closure's precondition is true of its capture. The body reads `x` (`let _ = x;`
// would not capture it), so the clause names a binding the closure holds.
#[requires(x@ == 5)]
#[ensures(true)]
pub fn cs1_ok(x: i32) {
    let x = 0i32;
    let f = #[requires(x@ == 0)]
    move || {
        let _c = x;
    };
    f();
}
