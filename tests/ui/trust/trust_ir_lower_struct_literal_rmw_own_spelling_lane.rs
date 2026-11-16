//@ revisions: off certify strict
//@ needs-trust-verify
//@ aux-build: rmw_literal_lanes.rs
//@ compile-flags: --crate-type=lib
//@[off] compile-flags: -Ztrust-verify=off -Ztrust-ir-lower=on
//@[off] check-pass
//@[certify] compile-flags: -Ztrust-verify=on -Ztrust-ir-lower=on -Ztrust-policy=certify
//@[certify] check-pass
//@[strict] compile-flags: -Ztrust-verify=on -Ztrust-ir-lower=strict -Ztrust-policy=advisory
//@[strict] check-fail
//@[strict] dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
// Copyright 2026 Andrew Yates
//! Trust (R101, 2026-10-21): **a placeholder lane that IS the field type's own spelling is not a
//! degraded lane, and a struct literal keeps inserting into it as before.**
//!
//! The RMW builder (`struct_ty_rmw_opaque`) spells every non-pure sibling with a placeholder,
//! including a field whose own `map_ty` spelling already is that placeholder: `Ty::Unit` for a
//! bare `ty::Param` (wave-PO) and a declined data enum (wave-EL), and, under
//! `TRUST_OPTION_FLAG_LANES` (on by default), `Ty::Bool` for a DECLINED `Option` (here
//! `Option<(u8, Declined)>`: `map_ty`'s enum arm spells it the discriminant, and its `None` lowers
//! to `const bool`). A value of such a field carries the lane's spelling as well, so the insert is
//! well typed. The R101 refusal (`Adt(rmw-degraded field lane)`, see
//! `trust_ir_lower_struct_literal_rmw_degraded_lane.rs`) must not reach these lanes: the builder
//! ledgers a lane only when the field's own spelling is not the placeholder.
//!
//! What pins it is `strict`. `H::rebuilt`, `G::rebuilt` and `Tagged::rebuilt` touch a degraded
//! row, so under `strict` each is refused by the effect-conservation check, on the base and with
//! the fix. If the builder ledgered these lanes too, the body would be refused at the literal
//! instead and `strict` would report `Adt(rmw-degraded field lane)` (measured on scratch mutants of
//! the fix: one that ledgers every floored `()` lane, for `H` and `G`; one that ledgers a `bool`
//! lane whenever the field's own spelling is not `()`, for `Tagged`). `mk_generic` is the same
//! `ty::Param` literal with no degraded row: the store seal's d75f13f978 refused it
//! (`Adt(unmappable field type)`, measured on build 9192), the regression Trust main declined that
//! commit for (824953985c). Under `strict` it stays clean.
//! External equivalents retain that exact control after ordinary registration became local-first:
//! a real external placeholder is still not an R101 respelling when it already is the field's own
//! spelling. Both local and external generic constructors without RMW remain clean under strict.
#![allow(dead_code)]

extern crate rmw_literal_lanes;

use rmw_literal_lanes::{ExternalDeclined, ExternalG, ExternalH, ExternalTagged};

pub enum Declined {
    A((u8, u16)),
    B,
}

pub struct H {
    n: u32,
    e: Declined,
}

impl H {
    pub fn rebuilt(&self, e: Declined) -> u32 {
        //[strict]~^ ERROR effect-conservation check refused it
        let n = self.n;
        let h = H { n, e };
        h.n
    }
}

pub struct G<T> {
    n: u32,
    t: T,
}

impl<T> G<T> {
    pub fn rebuilt(&self, t: T) -> G<T> {
        //[strict]~^ ERROR effect-conservation check refused it
        let n = self.n;
        G { n, t }
    }
}

pub fn mk_generic<T>(t: T) -> G<T> {
    G { n: 2, t }
}

pub struct Tagged {
    n: u32,
    o: Option<(u8, Declined)>,
}

impl Tagged {
    pub fn rebuilt(&self) -> u32 {
        //[strict]~^ ERROR effect-conservation check refused it
        let n = self.n;
        let t = Tagged { n, o: None };
        t.n
    }
}

pub fn external_declined_rebuilt(this: &ExternalH, e: ExternalDeclined) -> u32 {
    //[strict]~^ ERROR effect-conservation check refused it
    let n = this.n;
    let h = ExternalH { n, e };
    h.n
}

pub fn external_generic_rebuilt<T>(this: &ExternalG<T>, t: T) -> ExternalG<T> {
    //[strict]~^ ERROR effect-conservation check refused it
    let n = this.n;
    ExternalG { n, t }
}

pub fn external_mk_generic<T>(t: T) -> ExternalG<T> {
    ExternalG { n: 2, t }
}

pub fn external_tagged_rebuilt(this: &ExternalTagged) -> u32 {
    //[strict]~^ ERROR effect-conservation check refused it
    let n = this.n;
    let t = ExternalTagged { n, o: None };
    t.n
}
