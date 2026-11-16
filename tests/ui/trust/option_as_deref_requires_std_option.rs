//@ revisions: default certify memsafe
//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: option_as_deref_dep.rs
//@ compile-flags: -Ztrust-verify=on -Coverflow-checks=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@[memsafe] compile-flags: -Ztrust-policy=memory-safe
//@ check-fail
//@ dont-check-compiler-stderr
//! A method named `Option::as_deref` is not std's (EXTRACT-REWRITE-1).
//!
//! `apply_total_clone_sentinel` rewrote a call to the obligation-free
//! `TRUST_TOTAL_CLONE_SENTINEL` when its rendered callee ended with
//! `::Option::<T>::as_deref` or `::Option::as_deref` and its first generic argument
//! was a real-sysroot `Box`/`Arc`/`Rc`/`String`/`Vec`. Only the PAYLOAD was
//! authenticated. The dependency's `Option<T = Box<u8>>` renders its method as
//! `option_as_deref_dep::Option::as_deref` (the defaulted argument is elided), its
//! payload is std's `Box<u8>`, and its `as_deref` panics.
//!
//! BEFORE (stage 1 of `38e6c69b1c`, `scratchpad/stage1-w11fix`, each revision's flags
//! with `--emit=metadata`, 2026-10-04): `-Ztrust-dump=mir` shows `victim`'s call
//! extracted as `__trust_total_clone` (its `callee_key` names
//! `option_as_deref_dep`, `krate_is_real_sysroot: false`); `victim` read
//! `no_obligations | trivially panic-free` in every revision, had no diagnostic, and
//! every revision built exit 0. The program panics (`..._run.rs`).
//!
//! AFTER (predicted, then measured): the arm is deleted, the call keeps its name,
//! and `victim` carries `[trust-absent-callee-assumption] call to absent callee
//! ... may panic`. The annotations are what the BEFORE compiler prints for a twin of
//! this file, line for line, whose dependency type is named `Opt` (rendered
//! `option_as_deref_dep::Opt::as_deref`, which the arm never matched): exactly the
//! "no rewrite" behaviour the deletion leaves. std's own `Option::<Box<u8>>::as_deref`
//! renders `core::option::Option::<alloc::boxed::Box<u8>>::as_deref`, which the arm
//! never matched either, so std is unchanged (measured BEFORE: it reads
//! `runtime_checked`, not proved, under all three policies).
//! Measured on the stage 1 of `4463aeeb6d` (2026-10-04): every annotation below fires in
//! every revision and nothing else is reported. `victim` keeps its absent-callee row
//! (runtime-checked) in every revision.

extern crate option_as_deref_dep as dep;

pub fn victim(o: &dep::Option) -> u8 {
    //[default,memsafe]~^ WARN Trust Level 0 safety verification incomplete for `option_as_deref_requires_std_option::victim`: 1 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust strict verification failed for `option_as_deref_requires_std_option::victim`: 1 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `option_as_deref_requires_std_option::victim`: 1 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `option_as_deref_requires_std_option::victim`: at least one result is not an authenticated memory-safe assumption
    o.as_deref()
}
