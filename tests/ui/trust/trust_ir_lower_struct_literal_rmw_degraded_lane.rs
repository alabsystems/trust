//@ revisions: off certify strict external_off external_certify external_strict
//@ needs-trust-verify
//@ aux-build: rmw_literal_lanes.rs
//@ compile-flags: --crate-type=lib
//@[off] compile-flags: -Ztrust-verify=off -Ztrust-ir-lower=on
//@[off] check-pass
//@[certify] compile-flags: -Ztrust-verify=on -Ztrust-ir-lower=on -Ztrust-policy=certify
//@[certify] check-pass
//@[certify] dont-check-compiler-stderr
//@[strict] compile-flags: -Ztrust-verify=on -Ztrust-ir-lower=strict -Ztrust-policy=advisory
//@[strict] check-fail
//@[strict] dont-check-compiler-stderr
//@[external_off] compile-flags: -Ztrust-verify=off -Ztrust-ir-lower=on
//@[external_off] check-pass
//@[external_certify] compile-flags: -Ztrust-verify=on -Ztrust-ir-lower=on -Ztrust-policy=certify
//@[external_certify] check-fail
//@[external_certify] dont-check-compiler-stderr
//@[external_strict] compile-flags: -Ztrust-verify=on -Ztrust-ir-lower=strict -Ztrust-policy=advisory
//@[external_strict] check-fail
//@[external_strict] dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
// Copyright 2026 Andrew Yates
//! Trust (R101, 2026-10-21): **a struct literal never inserts a value into a placeholder lane
//! that the RMW builder spelled over a different own spelling.**
//!
//! `register_struct` dedups by `(DefId, args)`; the first registration wins. Each original body reads
//! a scalar field of `*self` BEFORE it builds `Self { .. }`. That read goes through
//! `struct_ty_rmw_opaque`, which spells every non-pure sibling with a placeholder and registers
//! the row: `Ty::Unit` for a `HashMap`, a `Vec` or a reference, and, under
//! `TRUST_OPTION_FLAG_LANES` (on by default), the `Ty::Bool` discriminant lane for an `Option`.
//! The literal's `map_ty(Self)` then gets that row back while the value it inserts keeps its own
//! spelling, and final validation of the WHOLE crate module fails. Measured before the fix on a
//! stage 1 of trust d2b525a13f (the route-G head) (`off`):
//!
//!   warning: trust-ir-lower semantic finalization failed: final Trust-IR module validation
//!   failed [OperandTypeMismatch] ...: OperandTypeMismatch { block: 0, op: "insert_field",
//!   role: "value", expected: "()", actual: "struct.N" } (and `actual: "ptr"`)
//!
//! and under `certify` the same failure is a hard error. `Instantiator::with_values` is the shape
//! of ay-dpll's `CegqiInstantiator::_create_model_instantiation`, the body behind row 101 of the
//! 2026-10-17 seal-line audit (`actual: "struct.283"`, its `HashMap<String, TermId>`).
//! `Named::unlabelled` and `Boxed::reboxed` are the `bool`-lane spelling of the same mechanism:
//! `Option<String>` and `Option<Box<u32>>` are ADMITTED enums (`map_ty` spells them `Ty::Enum`),
//! so their values are `enum.N` while the row's lane is `bool` (`expected: "bool", actual:
//! "enum.N"`, measured on the same stage 1 of d2b525a13f and on 759365fc8eb, the first port, which
//! ledgered only the `()` floor).
//!
//! After the ordinary-registration repair, the LOCAL cases below keep their real field spellings.
//! Their literals must lower, while strict still refuses their first-RMW effect abstraction.
//! The EXTERNAL cases keep exercising real R101 floors: the registration probe is local-only,
//! so these rows still carry `()` or the admitted Option's `bool` lane. Their literals must refuse
//! with `Adt(rmw-degraded field lane)`, rather than insert a differently typed value. Both groups
//! run independently: strict's external per-body errors must not abort analysis before the local
//! effect-conservation finalizer runs. The local cases remain clean under `off` and `certify`;
//! external `off` remains clean, while external `certify` explicitly refuses the four owned
//! foreign-ADT drops. That unsupported verification boundary remains required work for full
//! verified self-hosting. The run-make `trust-ir-rmw-struct-spelling` additionally
//! checks actual local-row spelling, published IR and preserved effects under both Option modes.
//! The ZST companion keeps a real external `()` floor, and the own-spelling companion keeps
//! external controls whose placeholder already is the field's own spelling.
#![allow(dead_code)]

extern crate rmw_literal_lanes;

#[cfg(any(off, certify, strict))]
pub mod local {
    use std::collections::HashMap;

    pub struct Instantiator {
        quantifier: u32,
        bound: HashMap<String, u32>,
        is_forall: bool,
    }

    impl Instantiator {
        fn width(&self) -> usize {
            self.bound.len()
        }

        pub fn with_values(&self, values: &HashMap<String, u32>) -> usize {
            //[strict]~^ ERROR effect-conservation check refused it
            let q = self.quantifier;
            let temp = Self {
                quantifier: q,
                bound: values.clone(),
                is_forall: self.is_forall,
            };
            temp.width()
        }
    }

    pub struct Buffered {
        q: u32,
        items: Vec<u32>,
        open: bool,
    }

    impl Buffered {
        pub fn emptied(&self) -> u32 {
            //[strict]~^ ERROR effect-conservation check refused it
            let q = self.q;
            let t = Self {
                q,
                items: Vec::new(),
                open: self.open,
            };
            t.q
        }
    }

    pub struct Borrowing<'a> {
        n: u32,
        r: &'a u32,
    }

    impl<'a> Borrowing<'a> {
        pub fn repointed(&self, r: &'a u32) -> u32 {
            //[strict]~^ ERROR effect-conservation check refused it
            let n = self.n;
            let t = Borrowing { n, r };
            t.n
        }
    }

    pub struct Named {
        n: u32,
        label: Option<String>,
    }

    impl Named {
        pub fn unlabelled(&self) -> u32 {
            //[strict]~^ ERROR effect-conservation check refused it
            let n = self.n;
            let t = Named { n, label: None };
            t.n
        }
    }

    pub struct Boxed {
        n: u32,
        b: Option<Box<u32>>,
    }

    impl Boxed {
        pub fn reboxed(&self) -> u32 {
            //[strict]~^ ERROR effect-conservation check refused it
            let n = self.n;
            let t = Boxed {
                n,
                b: Some(Box::new(n)),
            };
            t.n
        }
    }
}

#[cfg(any(external_off, external_certify, external_strict))]
pub mod external {
    use std::collections::HashMap;

    use rmw_literal_lanes::{
        ExternalBorrowing, ExternalBoxed, ExternalBuffered, ExternalInstantiator, ExternalNamed,
    };

    pub fn external_with_values(this: &ExternalInstantiator, values: &HashMap<String, u32>) -> u32 {
        //[external_strict]~^ ERROR Adt(rmw-degraded field lane)
        //[external_certify]~^^ ERROR this body drops a value whose type carries
        let q = this.quantifier;
        let temp = ExternalInstantiator {
            quantifier: q,
            bound: values.clone(),
            is_forall: this.is_forall,
        };
        temp.quantifier
    }

    pub fn external_emptied(this: &ExternalBuffered) -> u32 {
        //[external_strict]~^ ERROR Adt(rmw-degraded field lane)
        //[external_certify]~^^ ERROR this body drops a value whose type carries
        let q = this.q;
        let t = ExternalBuffered {
            q,
            items: Vec::new(),
            open: this.open,
        };
        t.q
    }

    pub fn external_repointed<'a>(this: &ExternalBorrowing<'a>, r: &'a u32) -> u32 {
        //[external_strict]~^ ERROR Adt(rmw-degraded field lane)
        let n = this.n;
        let t = ExternalBorrowing { n, r };
        t.n
    }

    pub fn external_unlabelled(this: &ExternalNamed) -> u32 {
        //[external_strict]~^ ERROR Adt(rmw-degraded field lane)
        //[external_certify]~^^ ERROR this body drops a value whose type carries
        let n = this.n;
        let t = ExternalNamed { n, label: None };
        t.n
    }

    pub fn external_reboxed(this: &ExternalBoxed) -> u32 {
        //[external_strict]~^ ERROR Adt(rmw-degraded field lane)
        //[external_certify]~^^ ERROR this body drops a value whose type carries
        let n = this.n;
        let t = ExternalBoxed {
            n,
            b: Some(Box::new(n)),
        };
        t.n
    }
}
