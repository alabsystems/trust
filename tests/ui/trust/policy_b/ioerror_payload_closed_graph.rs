//@ needs-trust-verify
//@ revisions: closed closed_strict closed_certify local_drop
//@ revisions: local_error_impl skip_impl skip_closure drop_stays_open
//@ compile-flags: -Ztrust-verify=on -Copt-level=0
//@[closed_strict] compile-flags: -Ztrust-policy=strict
//@[closed_certify] compile-flags: -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[closed] check-pass
//@[closed_strict] check-pass
//@[closed_certify] check-fail
//@[local_drop] check-pass
//@[local_error_impl] check-fail
//@[skip_impl] check-fail
//@[skip_closure] check-fail
//@[drop_stays_open] check-fail
#![crate_type = "lib"]
//! IOERROR-PAYLOAD-1 (2026-10-27, docs/DECISION_QUEUE.md): in a crate graph of
//! `core`/`alloc`/`std` alone, with no local `core::error::Error` impl and no
//! `#[trust::skip]` item, every `dyn Error` value — `io::Error`'s custom payload —
//! is a sysroot type, so the walks that asked "can this `dyn` run code nobody
//! verified" answer no for a CALL (a tolerated, runtime-checked row).
//!
//! MEASURED on a stage 1 of main `723f9ec299`: `append` (`OpenOptions::open(..)?`
//! then `write_all`) and `kind` were refused — `append` as "reaches code that
//! carries no verdict" — though the crate has no dependency at all. The
//! claude-code-alab harness, which has none, lost functions to these rows.
//!
//! Revisions, each one condition of the rule:
//!  * `local_drop`: a local destructor does not withdraw the rule — a payload at a
//!    local type runs that destructor, a body this crate verifies;
//!  * `local_error_impl`: a local `impl Error` can be a payload
//!    (`io::Error::other(Mine)`), whose `Display`/`Drop` nothing below vouches for;
//!  * `skip_impl`: a `#[trust::skip]` method of a local impl of a sysroot trait —
//!    a sysroot payload at a local type can run it;
//!  * `skip_closure`: a closure inside a `#[trust::skip]` function — a sysroot
//!    destructor in a payload can call it (`vec::Splice<Map<_, F>>` pulls `F`);
//!  * `drop_stays_open`: DROPPING an `io::Result` stays refused. The destructor
//!    walk credits a closed drop as panic-free sysroot code and opens at every
//!    local body, and a payload's drop can run local code (`BufWriter<W>`'s
//!    destructor flushes through `W::write`), so that walk does not take the rule.
//! `closed_certify` is the policy control: what the rule admits is runtime-checked,
//! never proved, and certify still refuses those bodies.
use std::io::Write;
use std::path::Path;

pub fn append(path: &Path, bytes: &[u8]) -> std::io::Result<()> {
    //[closed_certify,local_error_impl,skip_impl,skip_closure]~^ ERROR Trust
    let mut f = std::fs::OpenOptions::new().create(true).append(true).open(path)?;
    f.write_all(bytes)
}

pub fn kind(e: &std::io::Error) -> std::io::ErrorKind {
    //[closed_certify,local_error_impl,skip_impl,skip_closure]~^ ERROR Trust
    e.kind()
}

#[cfg(drop_stays_open)]
pub fn discard(path: &Path) -> u32 {
    //[drop_stays_open]~^ ERROR Trust
    let _ = append(path, b"x");
    1
}

#[cfg(local_error_impl)]
#[derive(Debug)]
pub struct Mine;

#[cfg(local_error_impl)]
impl std::fmt::Display for Mine {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("mine")
    }
}

#[cfg(local_error_impl)]
impl std::error::Error for Mine {}

#[cfg(skip_impl)]
pub struct Quiet(pub u32);

#[cfg(skip_impl)]
impl std::fmt::Debug for Quiet {
    #[trust::skip]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0 == 7 {
            panic!("unverified formatter");
        }
        f.write_str("quiet")
    }
}

#[cfg(skip_closure)]
#[trust::skip]
pub fn doubled(v: Vec<u8>) -> Vec<u8> {
    v.into_iter().map(|b| if b == 7 { panic!("unverified closure") } else { b * 2 }).collect()
}

#[cfg(local_drop)]
pub struct Guard(pub u32);

#[cfg(local_drop)]
impl Drop for Guard {
    fn drop(&mut self) {
        self.0 = self.0.wrapping_add(1);
    }
}
