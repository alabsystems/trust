//@ revisions: off adv strict
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: --crate-type lib
//@[off] compile-flags: -Ztrust-verify=off
//@[adv] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@[strict] compile-flags: -Ztrust-verify=on -Ztrust-policy=strict
//@[off] check-pass
//@[adv] check-pass
//@[strict] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output: E0391
//@ forbid-output: E0733
//@ forbid-output: cycle detected
//! A STATIC whose TYPE is sized by a future (probe h2b; before:
//! `E0391 cycle detected when computing type of BUF`), plus a census soundness
//! pin THROUGH that static: `g` calls `BUF[0]`, and `BUF = [launch]` holds a
//! function that spawns a std thread. `g` must never be quiet. A
//! `const`/`static` read is never a spawn claim (S1-S3), so `g`, like `f`, gets
//! an ESCAPES row for the read (design 2026-09-29-spawn-census-by-construction
//! P2; W11 printed an UNKNOWN) and an INDIRECT row for the call through the
//! `fn()` pointer — notes under `adv`, refusals under `strict`. `work`, which
//! only builds its future, has no row; its body `work::{closure#0}` reads
//! `SHOOK`.
//!
//! Drop-in (release gate): stock rustc accepts this crate, and so does every
//! revision here. Before 2026-09-29 the verified lanes (`adv`, and `strict`, the
//! shipping default) rejected it with a query cycle: a coroutine's layout,
//! demanded from inside the type system, read the coroutine's `optimized_mir`,
//! which Trust makes depend on other bodies (the crate call-graph oracles,
//! TrustVerify's callee bundling and operand evaluation). The layout is now read
//! from the coroutine's pre-steal elaborated MIR (`trust_local_coroutine_layout`).
//! `strict` may still refuse `async` bodies — Trust verdicts, which drop-in
//! permits — and nothing else.

pub fn launch() { let _h = std::thread::spawn(|| {}); }
//[strict]~^ ERROR Trust Level 0 safety verification incomplete for `static_type_array_len::launch`: 2 obligation(s) were not proved
// Upstream 1.101: thread spawn restructured (`functions::spawn` ->
// `lifecycle::spawn_unchecked` + `spawnhook::run_spawn_hooks`); the two
// unproved rows are now the unmodeled-spawn effect and the absent-callee
// assumption, so the refusal is owned by the generic strict message rather
// than the bundled-member-Assert one. The refusal itself is unchanged.
//[strict]~| ERROR Trust strict verification failed for `static_type_array_len::launch`: 2 obligation(s) were not fully verified
pub static SHOOK: fn() = launch;
pub async fn work() -> u8 { SHOOK(); 1 }
//[strict]~^ ERROR Trust Level 0 safety verification incomplete for `static_type_array_len::work::{closure#0}`: 2 obligation(s) were not proved
//[strict]~| ERROR Trust strict verification failed for `static_type_array_len::work::{closure#0}`: coroutine executor-protocol premise is unproved
//[strict]~| ERROR Trust strict verification failed for `static_type_array_len::work::{closure#0}`: 2 obligation(s) were not fully verified
pub const fn size_of_ret<F: Fn() -> R, R>(_: &F) -> usize { core::mem::size_of::<R>() }
pub static BUF: [fn(); size_of_ret(&work)] = [launch];
pub fn f() { SHOOK() }
//[strict]~^ ERROR Trust Level 0 safety verification incomplete for `static_type_array_len::f`: 1 obligation(s) were not proved
//[strict]~| ERROR Trust strict verification failed for `static_type_array_len::f`: 1 obligation(s) were not fully verified
pub fn g() { (BUF[0])() }
//[adv,strict]~^ NOTE const or static read here holds a callable that reaches a std thread spawn
//[adv,strict]~| NOTE may spawn (indirect): an indirect call
//[strict]~| ERROR Trust Level 0 safety verification incomplete for `static_type_array_len::g`: 2 obligation(s) were not proved
//[strict]~| ERROR Trust strict verification failed for `static_type_array_len::g`: 3 obligation(s) were not fully verified
