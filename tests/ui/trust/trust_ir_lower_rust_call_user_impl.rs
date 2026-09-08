//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-RC): a rust-call `Fn*::call*` whose receiver is a USER ADT — the
//! hand-written `impl Fn<(i32,)> for S` under `unboxed_closures`, and the
//! `self.call(args)` delegation between its three impls.
//!
//! WHY THIS IS AN ORDINARY `CalleeKind::Direct` CALL AND NOT AN ARITY LIE. The
//! `resolve_callee` ABI divert exists because a CLOSURE body's built params are
//! the UNTUPLED `[env, u, v]` while its call site passes `[recv, (u, v)]` — but
//! that split is created by rustc's own `DefKind::Closure` switch in
//! `construct_fn` ("HACK(eddyb) Avoid having RustCall on closures"), which
//! rewrites the ABI for closures ONLY. A non-closure
//! `extern "rust-call" fn call(&self, args: (i32,))` body keeps its params AS
//! WRITTEN — `[&S, (i32,)]`, tuple whole, arity 2 — and built MIR's call site
//! passes the tuple whole too (`spread_arg` is an FnAbi annotation the
//! extractor and bridge never read). Measured on `*.built.after.mir` and on the
//! producer's own signing (`functy = (ptr, (i32)) -> (i32)`). So
//! `[receiver, tuple]` is arity- and type-exact against the record it links,
//! and — unlike the closure path — the RECEIVER IS PASSED, never discarded for
//! a fresh unit slot: a user ADT's `&self` is a real parameter.
//!
//! NEGATIVE CONTROLS, the reason this is a pin: `neg_fnitem` (a fn-item
//! receiver resolves to `ShimKind::FnPtr`, a synthetic shim whose own call IS
//! untupled — not an `InstanceKind::Item`, must stay declining under
//! `Call(rust-call ABI)`) and `neg_closure` (a plain closure call must still
//! take `CalleeKind::ClosureCall` and untuple — this lane must not claim it).

#![feature(unboxed_closures, fn_traits)]

struct S;
impl Fn<(i32,)> for S {
    extern "rust-call" fn call(&self, (x,): (i32,)) -> i32 {
        x * x
    }
}
impl FnMut<(i32,)> for S {
    extern "rust-call" fn call_mut(&mut self, args: (i32,)) -> i32 {
        self.call(args)
    }
}
impl FnOnce<(i32,)> for S {
    type Output = i32;
    extern "rust-call" fn call_once(self, args: (i32,)) -> i32 {
        self.call(args)
    }
}

// Zero-element tuple: the `()` arity that `rust-call-shim-through-trait-box`
// exercises. The tuple is passed whole either way.
struct Z;
impl FnOnce<()> for Z {
    type Output = u32;
    extern "rust-call" fn call_once(self, _a: ()) -> u32 {
        7
    }
}

// Two-element tuple, both receiver mutabilities.
struct T2;
impl Fn<(u32, u32)> for T2 {
    extern "rust-call" fn call(&self, (a, b): (u32, u32)) -> u32 {
        a + b
    }
}
impl FnMut<(u32, u32)> for T2 {
    extern "rust-call" fn call_mut(&mut self, args: (u32, u32)) -> u32 {
        self.call(args)
    }
}
impl FnOnce<(u32, u32)> for T2 {
    type Output = u32;
    extern "rust-call" fn call_once(self, args: (u32, u32)) -> u32 {
        self.call(args)
    }
}

// NEGATIVE CONTROL: fn-item receiver -> ShimKind::FnPtr. Must STAY declining.
fn say(a: i32, b: i32) -> i32 {
    a + b
}
pub fn neg_fnitem() -> i32 {
    Fn::call(&say, (1, 2))
}

// CONTROL: a plain closure call still unt-uples through ClosureCall.
pub fn neg_closure() -> i32 {
    let f = |a: i32, b: i32| a + b;
    f(3, 4)
}

pub fn main() {}
