//@ revisions: report check
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@[report] compile-flags: -Ztrust-spawn-census-shadow=report
//@[check] compile-flags: -Ztrust-spawn-census-shadow=check
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output:violates its invariant
//! Spawn census, plan step P4: the trust-ir lane in SHADOW (design §5.7). Each fn-like body
//! gets one report line, its verdict on the MIR lane (which decides every row this compilation
//! prints) and on the trust-ir lane, how they compare, and the gaps that keep the trust-ir lane
//! from deciding it. The pins are anchored at a line start, so a diagnostic that echoes this
//! file cannot satisfy them. `check` fails the build on an invariant violation (the trust-ir
//! lane QUIET where the MIR lane refuses, or reaching a spawn where it is QUIET); none here.
//!
//! The shapes: a direct spawn and two wrappers, a closure and a link name reaching it (SPAWNS on
//! both lanes, through the per-body modules' callee ledgers); naming the spawner (ESCAPES); a
//! foreign call, which may call the exported spawner (INDIRECT on both, the foreign world);
//! and where the trust-ir lane cannot decide: a panic (std's panic runtime has no trust-ir), an
//! indirect call (pools are not composed across bodies), a Rust-ABI call through a type
//! parameter (`generic_clone`: a havoc row, never PARAM), a call through an `F: FnOnce` type
//! parameter (the producer declines the whole body, `gaps=producer-declined`: since 51558bd9ff a
//! rust-call callee has no IR calling convention, docs/DECISION_QUEUE.md EXACT-THIR-ABI-1), and a
//! raw-pointer read, which the producer lowers since e0e9606dab6 but whose UB check the trust-ir
//! lane does not yet decide (`gaps=ub-check`).
//@ regex-error-pattern:(?m)^trust-spawn-census-shadow: body `launch` mir=SPAWNS trust-ir=SPAWNS equal gaps=closure-value-omitted,drop$
//@ regex-error-pattern:(?m)^trust-spawn-census-shadow: body `launch::\{closure#0\}` mir=QUIET trust-ir=QUIET equal gaps=-$
//@ regex-error-pattern:(?m)^trust-spawn-census-shadow: body `two_hop` mir=SPAWNS trust-ir=SPAWNS equal gaps=closure-value-omitted,drop$
//@ regex-error-pattern:(?m)^trust-spawn-census-shadow: body `adds` mir=INDIRECT trust-ir=UNKNOWN trust-ir-unknown gaps=panic$
//@ regex-error-pattern:(?m)^trust-spawn-census-shadow: body `names_launch` mir=ESCAPES trust-ir=ESCAPES equal gaps=closure-value-omitted,drop$
//@ regex-error-pattern:(?m)^trust-spawn-census-shadow: body `calls_pointer` mir=INDIRECT trust-ir=UNKNOWN trust-ir-unknown gaps=indirect-call$
//@ regex-error-pattern:(?m)^trust-spawn-census-shadow: body `generic` mir=QUIET trust-ir=UNKNOWN trust-ir-unknown gaps=producer-declined$
//@ regex-error-pattern:(?m)^trust-spawn-census-shadow: body `generic_clone` mir=QUIET trust-ir=UNKNOWN trust-ir-unknown gaps=elided-drops,havoc$
//@ regex-error-pattern:(?m)^trust-spawn-census-shadow: body `c_abs` mir=INDIRECT trust-ir=INDIRECT equal gaps=closure-value-omitted,foreign-callback,drop,ub-check,indirect-call$
//@ regex-error-pattern:(?m)^trust-spawn-census-shadow: body `through_link_name` mir=SPAWNS trust-ir=SPAWNS equal gaps=closure-value-omitted,drop,ub-check$
//@ regex-error-pattern:(?m)^trust-spawn-census-shadow: body `closure_call::\{closure#0\}` mir=SPAWNS trust-ir=SPAWNS equal gaps=closure-value-omitted,drop$
//@ regex-error-pattern:(?m)^trust-spawn-census-shadow: body `read` mir=INDIRECT trust-ir=UNKNOWN trust-ir-unknown gaps=ub-check$
//@ regex-error-pattern:(?m)^trust-spawn-census-shadow: crate `trust_ir_shadow_lane` bodies=15 equal=10 trust-ir-unknown=5 differs=0 fail-open=0 mir-quiet-claim=0 mir-not-walked=0 mir-fell-back=0 decided=1 residue=0$

#![allow(dead_code)]

pub fn launch() {
    let _handle = std::thread::spawn(|| {});
}

pub fn one_hop() {
    launch();
}

pub fn two_hop() {
    one_hop();
}

pub fn adds(a: u32, b: u32) -> u32 {
    a + b
}

pub fn names_launch() -> fn() {
    launch
}

pub fn calls_pointer(f: fn()) {
    f()
}

pub fn generic<F: FnOnce()>(f: F) {
    f()
}

pub fn generic_clone<T: Clone>(t: &T) -> T {
    t.clone()
}

unsafe extern "C" {
    fn abs(x: i32) -> i32;
}

pub fn c_abs(x: i32) -> i32 {
    unsafe { abs(x) }
}

#[unsafe(no_mangle)]
pub extern "C" fn trust_shadow_lane_exported_spawner() {
    launch();
}

mod inner {
    unsafe extern "C" {
        #[link_name = "trust_shadow_lane_exported_spawner"]
        pub fn by_link_name();
    }
}

pub fn through_link_name() {
    unsafe { inner::by_link_name() }
}

pub fn closure_call() {
    let c = || launch();
    c()
}

pub fn read(p: *const u32) -> u32 {
    unsafe { *p }
}
