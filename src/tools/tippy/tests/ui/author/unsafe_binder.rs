//@ check-pass

#![feature(stmt_expr_attributes, unsafe_binders)]
#![allow(incomplete_features)]

use std::unsafe_binder::{unwrap_binder, wrap_binder};

fn main() {
    let value = 7_i32;
    let wrapped: unsafe<'a> &'a i32 = #[clippy::author]
    unsafe {
        wrap_binder!(&value)
    };
    let _: &i32 = #[clippy::author]
    unsafe {
        unwrap_binder!(wrapped; unsafe<'a> &'a i32)
    };
}
