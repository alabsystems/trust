//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ rustc-env:TRUST_SYSROOT_CENSUS_DEBUG=1
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW withheld key=`alloc::vec::Vec::<b_lane_alias_site_withholds_census_key::go::S::Inner>::truncate`
//! Trust (2026-09-27, std-absent-callee): a sysroot panic census grant is spent
//! only on call sites the census itself judged — including the sites of a B-lane
//! member, which `collect_expected_absent_callees` never walks.
//!
//! The bridge spends a compiler-total key by NAME on every row of the lowered
//! module, and the key is rendered text. `direct_call_def_path` residual 7c: a
//! type rendered INSIDE generic arguments is never cross-namespace-tagged, so the
//! module `S`'s `Inner` and the `Inner` declared inside `fn S` below both render
//! `…::go::S::Inner` there.
//!
//! * `fn S`'s own `a.truncate(0)` is `Vec::<module Inner>::truncate`: the module
//!   `Inner` has no drop glue, so the census walks it TOTAL.
//! * `b.resize_with(..)` is bundled by the B-lane, instantiated at the fn-local
//!   `Inner`, whose `Drop` panics. Its own body calls `self.truncate(new_len)`:
//!   `Vec::<fn-local Inner>::truncate`, which runs that destructor — and whose
//!   key is spelled exactly like the first.
//!
//! Before, only the root's site was censused, so the key was granted and the
//! bridge would spend it on the member's site too — a site whose instance
//! reaches a panic the census never looked at. Now the B-lane records its
//! members' sites at admission (`CensusDischarges::witness_body`), the member's
//! site is judged (it reaches `<Inner as Drop>::drop`), and the key is withheld
//! from the whole bundle. The annotation pins that withholding through the
//! census's own diagnostic (`TRUST_SYSROOT_CENSUS_DEBUG`); both functions stay
//! refused for their own reasons either way, so the verdict alone cannot show it
//! HERE. When both aliased sites sit in ONE body, the verdict does show it:
//! `own_census_key_withheld_when_one_site_declines.rs`.
#![allow(non_snake_case)]

pub mod go {
    pub mod S {
        pub struct Inner(pub u8);
    }

    pub fn S(a: &mut Vec<S::Inner>, n: usize) {
        struct Inner(u8);
        impl Drop for Inner {
            fn drop(&mut self) {
                if self.0 == 7 {
                    panic!("inner")
                }
            }
        }
        a.truncate(0);
        let mut b: Vec<Inner> = Vec::new();
        b.resize_with(n, || Inner(7));
    }
}
