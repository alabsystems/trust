//@ needs-trust-verify
//@ edition: 2021
//@ revisions: async_fn async_fn_reversed async_block tuple local_wrapper option
//@ revisions: tait_field fn_output_drop fn_output_fold certify off
//@ revisions: boxed_self_drop boxed_self_insert boxed_self_wrapper boxed_self_collect
//@ compile-flags: --crate-type lib
//@[async_fn] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@[async_fn_reversed] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@[async_block] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@[tuple] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@[local_wrapper] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@[option] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@[tait_field] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@[fn_output_drop] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@[fn_output_fold] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@[boxed_self_drop] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@[boxed_self_insert] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@[boxed_self_wrapper] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@[boxed_self_collect] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@[certify] compile-flags: -Ztrust-verify=on -Ztrust-policy=certify
//@[off] compile-flags: -Ztrust-verify=off
//@[async_fn] check-pass
//@[async_fn_reversed] check-pass
//@[async_block] check-pass
//@[tuple] check-pass
//@[local_wrapper] check-pass
//@[option] check-pass
//@[tait_field] check-pass
//@[fn_output_drop] check-pass
//@[fn_output_fold] check-pass
//@[boxed_self_drop] check-pass
//@[boxed_self_insert] check-pass
//@[boxed_self_wrapper] check-pass
//@[boxed_self_collect] check-pass
//@[certify] check-fail
//@[off] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! REGRESSION (2026-10-01, std-absent-callee): the sysroot panic census must never
//! ask rustc about a COROUTINE of the crate being compiled. Every program here is
//! valid Rust and builds with verification off (`off`); each advisory revision
//! builds with the census withheld (`TRUST_NO_SYSROOT_CENSUS=1`), so it must build
//! with the census on too.
//!
//! THE CYCLE. The census runs inside the verified body's own `optimized_mir`. A std
//! call at a type that holds a coroutine of this crate — `drop(foo(n))`, where
//! `foo` is an `async fn` that calls back into the verified `bar` — made it ask
//! for that coroutine's drop glue (`resolve_instance_raw` reads the coroutine's
//! `optimized_mir`) and, through drop shims and layout-dependent constants, its
//! layout (read off the same `optimized_mir`). That coroutine's `optimized_mir` is
//! further up the stack (`layout_of(foo::{closure#0})` -> `optimized_mir(foo::{closure#0})`
//! -> `optimized_mir(bar)` -> the census), so the compilation stopped with
//! `error[E0391]: cycle detected when optimizing MIR for foo::{closure#0}` under
//! every policy: measured on stage 1 `0c99d68db` (the census commit on its earlier
//! base), each advisory shape below aborted with E0391 and built rc 0 with the
//! census withheld on the same binary; the default policy and `certify` aborted with
//! E0391 instead of a Trust verdict.
//!
//! The shapes: the coroutine as the call's own type argument (`async_fn`, either
//! declaration order, and an `async` block), inside a tuple, a local generic
//! wrapper and an `Option` (all through the type's generic arguments), as the field
//! of a local struct with no generic arguments at all, typed with a type-alias
//! `impl Trait` (`tait_field`: only a walk of the local ADT's declared fields finds
//! it), and reached only INSIDE a std body (`fn_output_drop`, `fn_output_fold`: the
//! census root is `<RepeatWith<fn foo> as Iterator>::advance_by` / `Take<…>::fold`,
//! whose arguments name only the function item `foo`; the coroutine appears when
//! `F::Output` is normalized in the walk, and it was the report re-walk that met
//! its drop).
//!
//! On a later base (origin/main `437cc6cc56`, after main began reading a local
//! coroutine's layout from its pre-steal MIR, KNOWN_HAZARDS "CLOSED 2026-09-29 ...
//! `layout_of` -> `optimized_mir(coroutine)`") those shapes no longer cycle even
//! with the census's coroutine checks removed: they stay here as no-E0391 pins.
//! What still cycles is the route KNOWN_HAZARDS lists as open — resolving
//! `drop_glue::<Coroutine>` reads `optimized_mir(coroutine)` — reached from the
//! census inside the COROUTINE'S OWN `optimized_mir`: an `async fn` that boxes its
//! own future and drops it (`boxed_self_drop`), stores it (`boxed_self_insert`:
//! `Option::insert` at `Pin<Box<…>>`), wraps it in a local generic struct
//! (`boxed_self_wrapper`) or collects it (`boxed_self_collect`). Measured on a
//! stage 1 of that base with the root and walk checks removed (env-gated mutant
//! schemata): `error[E0391]: cycle detected when optimizing MIR for
//! g::{closure#0}` / `...which requires resolving instance
//! core::ptr::drop_glue::<{async fn body of g()}>` for each of the four, rc 0 with
//! the census withheld and with verification off; either check alone closes all
//! four.
//!
//! THE FIX (`sysroot_panic_census`, "A coroutine of this crate is never queried"):
//! before any query, a root whose arguments, or a walked instance, call, drop or
//! constant whose type, holds a coroutine of this crate (after normalization, and
//! through this crate's own ADT fields) is declined — never granted. Such a call
//! keeps the absent-callee row it had before the census existed: the advisory
//! revisions build, the default policy reports the row, and `certify` refuses `bar`
//! (`certify`) exactly as it does with the census withheld: the call keeps the row
//! it had, so the census adds no refusal note of its own here.
#![cfg_attr(any(tait_field, off), feature(type_alias_impl_trait))]
#![allow(dead_code)]

#[cfg(any(async_fn, certify, off))]
pub mod async_fn {
    pub async fn foo(n: u32) -> u32 {
        if n == 0 { 0 } else { bar(n - 1) }
    }

    pub fn bar(n: u32) -> u32 {
        //[certify]~^ ERROR Trust strict verification failed for `local_coroutine_type_no_query_cycle::async_fn::bar`
        let f = foo(n);
        std::mem::drop(f);
        n
    }
}

#[cfg(any(async_fn_reversed, off))]
pub mod async_fn_reversed {
    pub fn bar(n: u32) -> u32 {
        let f = foo(n);
        std::mem::drop(f);
        n
    }

    pub async fn foo(n: u32) -> u32 {
        if n == 0 { 0 } else { bar(n - 1) }
    }
}

#[cfg(any(async_block, off))]
pub mod async_block {
    pub fn a2() -> u8 {
        let fut = async { a2() };
        std::mem::drop(fut);
        3
    }
}

#[cfg(any(tuple, off))]
pub mod tuple {
    pub async fn foo(n: u32) -> u32 {
        if n == 0 { 0 } else { bar(n - 1) }
    }

    pub fn bar(n: u32) -> u32 {
        let f = (foo(n), 1u8);
        std::mem::drop(f);
        n
    }
}

#[cfg(any(local_wrapper, off))]
pub mod local_wrapper {
    pub struct W<F>(pub F);

    pub async fn foo(n: u32) -> u32 {
        if n == 0 { 0 } else { bar(n - 1) }
    }

    pub fn bar(n: u32) -> u32 {
        let f = W(foo(n));
        std::mem::drop(f);
        n
    }
}

#[cfg(any(option, off))]
pub mod option {
    pub async fn foo(n: u32) -> u32 {
        if n == 0 { 0 } else { bar(n - 1) }
    }

    pub fn bar(n: u32) -> u32 {
        let f = Some(foo(n));
        let g = f.is_some();
        std::mem::drop(f);
        if g { n } else { 0 }
    }
}

#[cfg(any(tait_field, off))]
pub mod tait_field {
    pub type Fut = impl core::future::Future<Output = u32>;

    pub struct H(pub Fut);

    #[define_opaque(Fut)]
    pub fn mk(n: u32) -> H {
        H(async move { bar(n) })
    }

    pub fn bar(n: u32) -> u32 {
        if n == 0 {
            return 0;
        }
        let h = mk(n - 1);
        std::mem::drop(h);
        n
    }
}

#[cfg(any(fn_output_drop, off))]
pub mod fn_output_drop {
    pub async fn foo() -> u32 {
        bar()
    }

    pub fn bar() -> u32 {
        let _ = std::iter::repeat_with(foo).nth(1);
        3
    }
}

#[cfg(any(fn_output_fold, off))]
pub mod fn_output_fold {
    pub async fn foo() -> u32 {
        bar()
    }

    pub fn bar() -> u32 {
        let n = std::iter::repeat_with(foo).take(2).count();
        n as u32
    }
}

#[cfg(any(boxed_self_drop, off))]
pub mod boxed_self_drop {
    pub async fn g(n: u32) -> u32 {
        if n == 0 {
            return 0;
        }
        let b = Box::pin(g(n - 1));
        drop(b);
        1
    }
}

#[cfg(any(boxed_self_insert, off))]
pub mod boxed_self_insert {
    pub async fn h(n: u32) -> u32 {
        if n == 0 {
            return 0;
        }
        let mut slot = None;
        let _ = slot.insert(Box::pin(h(n - 1)));
        1
    }
}

#[cfg(any(boxed_self_wrapper, off))]
pub mod boxed_self_wrapper {
    pub struct W<F>(pub F);

    pub async fn k(n: u32) -> u32 {
        if n == 0 {
            return 0;
        }
        let w = Box::new(W(Box::pin(k(n - 1))));
        drop(w);
        1
    }
}

#[cfg(any(boxed_self_collect, off))]
pub mod boxed_self_collect {
    pub async fn k(n: u32) -> u32 {
        if n == 0 {
            return 0;
        }
        let v: Vec<_> = (0..2u32).map(|i| Box::pin(k(i))).collect();
        drop(v);
        1
    }
}
