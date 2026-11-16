//@ expect: reject
//@ mechanism: trust-soundness-corpus entry wp-d237-shadowed-namesake; the corpus runner reads per-function credits,
//@ mechanism: not this case's verdict (see tests/trust-soundness-corpus/README.md).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use ::std::rc::Rc;
use creusot_std::prelude::*;

pub fn rs1() {
    let r = Rc::new(1i32);
    let r2 = r.clone();
    let r = Rc::new(2i32);
    proof_assert!(r == r2);
}

// Twin (va2): the clone fact read about the binding it is about.
pub fn va2() {
    let r = Rc::new(1i32);
    let r2 = r.clone();
    let r = Rc::new(2i32);
    let _ = r;
    proof_assert!(*r2 == 1i32);
}
