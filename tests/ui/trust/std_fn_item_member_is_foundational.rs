//@ needs-trust-verify
//@ edition: 2021
//@ revisions: std_item user_item user_turbofish
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[std_item] check-pass
//@[user_item] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A bundled std iterator member whose type carries a std FUNCTION ITEM —
//! `Map<Split<'_, char>, for<'_> fn(&'_ str) -> &'_ str {core::str::<impl str>::trim}>`
//! — is std's own code end to end, so its guarded internal assert is the same
//! policy-B completeness gap as any other std member's (ordsweep2 strings/c10).
//! Before 2026-10-03 the type's `->` (and the `<impl str>` in the braced path)
//! refused the tolerance and the build failed.
//!
//! The negative revisions keep a fn item that runs USER code fatal: a user
//! function, and a std generic function instantiated at a user type.
//!
//! RE-PINNED 2026-10-15 (the merge of 2026-10-14), measured on the merged stage 1:
//! `user_turbofish` is still refused (headline now "Trust strict verification
//! failed"). `user_item` now BUILDS: main's CALL-REACH-1 walks the `map` instance,
//! and every body it can run is sysroot-resident or the LOCAL item `first_word`,
//! which is held to its own root (verified here, `s.trim_start()`); the call keeps
//! its `runtime_checked` std-member row, a default-policy warning. A fn item that
//! runs a dependency's or an unverified body stays refused by that walk.
#![allow(dead_code)]

#[cfg(std_item)]
pub fn join_fields(s: &str, sep: &str) -> String {
    let mut out = String::new();
    for (i, field) in s.split(',').map(str::trim).enumerate() {
        if i > 0 {
            out.push_str(sep);
        }
        out.push_str(field);
    }
    out
}

#[cfg(user_item)]
fn first_word(s: &str) -> &str {
    s.trim_start()
}

#[cfg(user_item)]
pub fn join_fields(s: &str, sep: &str) -> String {
    let mut out = String::new();
    for (i, field) in s.split(',').map(first_word).enumerate() {
        if i > 0 {
            out.push_str(sep);
        }
        out.push_str(field);
    }
    out
}

#[cfg(std_item)]
pub fn count_small(v: &[u32]) -> usize {
    let mut n = 0;
    for (i, x) in v.iter().map(core::convert::identity::<&u32>).enumerate() {
        if (*x as usize) < i {
            n += 1;
        }
    }
    n
}

#[cfg(user_turbofish)]
pub struct Field(pub u32);

#[cfg(user_turbofish)]
pub fn count_small(v: &[Field]) -> usize {
    //[user_turbofish]~^ ERROR Trust strict verification failed
    let mut n = 0;
    for (i, x) in v.iter().map(core::convert::identity::<&Field>).enumerate() {
        if (x.0 as usize) < i {
            n += 1;
        }
    }
    n
}
