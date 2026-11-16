//@ revisions: none walked declined cast unwind dep
//@ aux-build:shadow_hand_out_dep.rs
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ compile-flags: -Ztrust-spawn-census-shadow=check
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output:violates its invariant
//! Spawn census, plan step P4 review (probes b01-b05): foreign code may KEEP a callback it is
//! handed and call it from a later call that hands it nothing (`run`), which the MIR lane's foreign
//! world charges as INDIRECT. The trust-ir lane charged only hand-outs it walked (a foreign call's
//! operand, `walked`); a hand-out by a body the producer declines (`declined`, `cast`), through a
//! foreign declaration that may unwind (`unwind`) or through another crate's Rust (`dep`) left
//! `run` QUIET, a fail-open. Every reach of code or memory out of sight is now a hand-out, so `run`
//! is UNKNOWN (`foreign-callback`) in each. `none` hands nothing out: `run` is QUIET on both lanes.
//! No body here drops anything or calls std beyond the spawn seed, so the hand-out named by each
//! revision is the only one.
//@[none] regex-error-pattern:(?m)^trust-spawn-census-shadow: body `run` mir=QUIET trust-ir=QUIET equal gaps=-$
//@[none] regex-error-pattern:(?m)^trust-spawn-census-shadow: crate `trust_ir_shadow_lane_hand_outs` bodies=1 equal=1 trust-ir-unknown=0 differs=0 fail-open=0 mir-quiet-claim=0 mir-not-walked=0 mir-fell-back=0 decided=1 residue=0$
//@[walked] regex-error-pattern:(?m)^trust-spawn-census-shadow: body `hand_out` mir=ESCAPES trust-ir=ESCAPES equal gaps=closure-value-omitted,foreign-callback,indirect-call$
//@[walked] regex-error-pattern:(?m)^trust-spawn-census-shadow: body `run` mir=INDIRECT trust-ir=UNKNOWN trust-ir-unknown gaps=foreign-callback$
//@[declined] regex-error-pattern:(?m)^trust-spawn-census-shadow: body `hand_out` mir=ESCAPES trust-ir=UNKNOWN trust-ir-unknown gaps=producer-declined$
//@[declined] regex-error-pattern:(?m)^trust-spawn-census-shadow: body `run` mir=INDIRECT trust-ir=UNKNOWN trust-ir-unknown gaps=foreign-callback$
//@[cast] regex-error-pattern:(?m)^trust-spawn-census-shadow: body `hand_out` mir=ESCAPES trust-ir=UNKNOWN trust-ir-unknown gaps=producer-declined$
//@[cast] regex-error-pattern:(?m)^trust-spawn-census-shadow: body `run` mir=INDIRECT trust-ir=UNKNOWN trust-ir-unknown gaps=foreign-callback$
//@[unwind] regex-error-pattern:(?m)^trust-spawn-census-shadow: body `hand_out` mir=ESCAPES trust-ir=ESCAPES equal gaps=closure-value-omitted,unwinding-foreign$
//@[unwind] regex-error-pattern:(?m)^trust-spawn-census-shadow: body `run` mir=INDIRECT trust-ir=UNKNOWN trust-ir-unknown gaps=foreign-callback$
//@[dep] regex-error-pattern:(?m)^trust-spawn-census-shadow: body `hand_out` mir=ESCAPES trust-ir=UNKNOWN trust-ir-unknown gaps=extern-rust$
//@[dep] regex-error-pattern:(?m)^trust-spawn-census-shadow: body `run` mir=INDIRECT trust-ir=UNKNOWN trust-ir-unknown gaps=foreign-callback$
//@[walked] regex-error-pattern:(?m)^trust-spawn-census-shadow: body `c_launch` mir=SPAWNS trust-ir=SPAWNS equal gaps=closure-value-omitted$
//@[declined] regex-error-pattern:(?m)^trust-spawn-census-shadow: body `c_launch` mir=SPAWNS trust-ir=SPAWNS equal gaps=closure-value-omitted$
//@[cast] regex-error-pattern:(?m)^trust-spawn-census-shadow: body `c_launch` mir=SPAWNS trust-ir=SPAWNS equal gaps=closure-value-omitted$
//@[unwind] regex-error-pattern:(?m)^trust-spawn-census-shadow: body `c_launch` mir=SPAWNS trust-ir=SPAWNS equal gaps=closure-value-omitted$
//@[dep] regex-error-pattern:(?m)^trust-spawn-census-shadow: body `c_launch` mir=SPAWNS trust-ir=SPAWNS equal gaps=closure-value-omitted$

#![allow(dead_code, improper_ctypes, improper_ctypes_definitions)]

#[cfg(dep)]
extern crate shadow_hand_out_dep;

#[cfg(not(none))]
pub fn launch() -> std::thread::JoinHandle<()> {
    std::thread::spawn(|| {})
}

#[cfg(not(none))]
pub extern "C" fn c_launch() -> std::thread::JoinHandle<()> {
    launch()
}

unsafe extern "C" {
    safe fn trust_p4_run();
    #[cfg(any(walked, declined))]
    safe fn trust_p4_register(cb: extern "C" fn() -> std::thread::JoinHandle<()>);
    #[cfg(cast)]
    safe fn trust_p4_register_addr(cb: usize);
}

#[cfg(unwind)]
unsafe extern "C-unwind" {
    safe fn trust_p4_register_unwind(cb: extern "C" fn() -> std::thread::JoinHandle<()>);
}

#[cfg(walked)]
pub fn hand_out() {
    trust_p4_register(c_launch)
}

// The producer declines a body that names a constant of fn-pointer type.
#[cfg(declined)]
const CB: extern "C" fn() -> std::thread::JoinHandle<()> = c_launch;

#[cfg(declined)]
pub fn hand_out() {
    trust_p4_register(CB)
}

#[cfg(cast)]
pub fn hand_out() {
    trust_p4_register_addr(c_launch as usize)
}

#[cfg(unwind)]
pub fn hand_out() {
    trust_p4_register_unwind(c_launch)
}

#[cfg(dep)]
pub fn hand_out() {
    shadow_hand_out_dep::register(c_launch as usize)
}

pub fn run() {
    trust_p4_run()
}
