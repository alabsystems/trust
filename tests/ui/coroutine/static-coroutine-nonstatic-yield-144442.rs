// Regression test for rust-lang#144442: 'static coroutines must not yield
// values containing non-'static references. The yield type is part of the
// coroutine's generic arguments, so a 'static bound on the coroutine must
// propagate to the yield type.

#![feature(coroutines, coroutine_trait, stmt_expr_attributes)]

use std::ops::Coroutine;

fn assert_static<T: 'static>(_: T) {}

fn yield_non_static_ref() {
    let coroutine = #[coroutine]
    |_: ()| {
        let local = String::from("hello");
        yield local.as_str();
        //~^ ERROR cannot yield value referencing local variable `local`
        //~| ERROR borrow may still be in use when coroutine yields
    };
    assert_static(coroutine);
}

fn yield_non_static_ref_from_arg<'a>(s: &'a str) {
    let coroutine = #[coroutine]
    move |_: ()| {
        yield s;
    };
    assert_static(coroutine);
    //~^ ERROR borrowed data escapes outside of function
}

fn main() {
    yield_non_static_ref();
    yield_non_static_ref_from_arg("test");
}
