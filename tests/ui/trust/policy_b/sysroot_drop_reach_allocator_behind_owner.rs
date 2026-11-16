//@ needs-trust-verify
//@ aux-build: sysroot_drop_reach_dep.rs
//@ revisions: opt_box_in res_box_in local_struct_box_in local_struct_box_in_scope
//@ revisions: local_enum_box_in_scope local_struct_vec_in_scope dep_hbox opt_dep_hbox
//@ revisions: opt_box_alias cell_set_box_in hash_map_box_in hash_map_vec_in
//@ revisions: opt_box_ref_alloc vec_in
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=json --error-format=human
//@ compile-flags: -Copt-level=0 --crate-type lib -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! A sysroot owning container whose ALLOCATOR is not the sysroot's own is not
//! drop-total, wherever it sits (2026-09-29).
//!
//! `tcx_drop_is_total` (trust-mir-extract) writes the `AdtAuth::TotalDrop` stamp,
//! and the bridge's drop classifier accepts a stamped node WITHOUT visiting its
//! fields. Its audited-container arm credited `Box`/`Vec`/`HashMap`/… as "dealloc
//! plus per-element drop, no user code", and asked of the allocator argument only
//! whether it has a DESTRUCTOR. A dependency allocator with no destructor passed,
//! although the container's glue calls its `deallocate`. So an owner of such a
//! container — `Option`, `Result`, a struct, `HashMap` — was stamped, and the
//! `Box` beneath it, whose credit `sysroot_drop_reach.rs` had withdrawn by name
//! (`sysroot_drop_reaches_dependency_code.rs#box_dep_alloc_certify`), was never
//! reached. Now an allocator position (a parameter bounded by
//! `core::alloc::Allocator`, or defaulting to `Global`) must be `Global` or
//! `System` for the stamp.
//!
//! BEFORE (stage 1 of origin/main `fbb9fa383d2` and of the first sysroot-drop-reach
//! build, m3's debug std, measured 2026-09-29 by two reviewers): every revision
//! but `vec_in` built exit 0 under `-Ztrust-policy=certify`; the `drop(..)` shapes
//! with `functions_verified` 1 of 1, the scope-end shapes with 0 of 1 and a PROVED
//! panic-freedom row (the only unproved row was the vacuous `Global`
//! global-alloc contract row, naming the wrong allocator). A verify-off `main`
//! handing each a `DepAlloc(7)` value panicked in `DepAlloc::deallocate` (exit
//! 101; `Box<[u8], DepAlloc>` aborted, 134). `dep_hbox` and `opt_box_alias` need
//! no feature gate in the verified crate. `vec_in` (`drop(Vec<u8, DepAlloc>)`)
//! was already refused under certify and is kept here as the `Ty::Seq` pin.
//! AFTER: each is refused and `p` is not counted verified.
//!
//! The credit this must KEEP — `Option<Box<u32>>`, `HashMap<u8, Box<u32>>`, an
//! explicit `Box<u32, Global>` — is pinned by
//! `sysroot_drop_reach_keeps_sysroot_credit.rs`.
#![cfg_attr(
    any(
        opt_box_in,
        res_box_in,
        local_struct_box_in,
        local_struct_box_in_scope,
        local_enum_box_in_scope,
        local_struct_vec_in_scope,
        cell_set_box_in,
        hash_map_box_in,
        hash_map_vec_in,
        opt_box_ref_alloc,
        vec_in
    ),
    feature(allocator_api)
)]

extern crate sysroot_drop_reach_dep as rdep;

#[cfg(opt_box_in)]
pub fn p(t: u8, o: Option<Box<u32, rdep::DepAlloc>>) -> u8 {
    let c = if t == 0 { 1 } else { 2 };
    drop(o);
    c
}

#[cfg(res_box_in)]
pub fn p(t: u8, r: Result<Box<u32, rdep::DepAlloc>, u8>) -> u8 {
    let c = if t == 0 { 1 } else { 2 };
    drop(r);
    c
}

#[cfg(any(local_struct_box_in, local_struct_box_in_scope))]
pub struct H(pub Box<u32, rdep::DepAlloc>);

#[cfg(local_struct_box_in)]
pub fn p(t: u8, h: H) -> u8 {
    let c = if t == 0 { 1 } else { 2 };
    drop(h);
    c
}

#[cfg(local_struct_box_in_scope)]
pub fn p(t: u8, h: H) -> u8 {
    let c = if t == 0 { 1 } else { 2 };
    let _keep = h;
    c
}

#[cfg(local_enum_box_in_scope)]
pub enum E {
    Empty,
    Held(Box<u32, rdep::DepAlloc>),
}

#[cfg(local_enum_box_in_scope)]
pub fn p(t: u8, e: E) -> u8 {
    let c = if t == 0 { 1 } else { 2 };
    let _keep = e;
    c
}

#[cfg(local_struct_vec_in_scope)]
pub struct V(pub Vec<u8, rdep::DepAlloc>);

#[cfg(local_struct_vec_in_scope)]
pub fn p(t: u8, v: V) -> u8 {
    let c = if t == 0 { 1 } else { 2 };
    let _keep = v;
    c
}

// No feature gate: the allocator is spelled only in the dependency.
#[cfg(dep_hbox)]
pub fn p(t: u8, h: rdep::HBox) -> u8 {
    let c = if t == 0 { 1 } else { 2 };
    drop(h);
    c
}

#[cfg(opt_dep_hbox)]
pub fn p(t: u8, h: Option<rdep::HBox>) -> u8 {
    let c = if t == 0 { 1 } else { 2 };
    drop(h);
    c
}

#[cfg(opt_box_alias)]
pub fn p(t: u8, o: Option<rdep::BoxIn>) -> u8 {
    let c = if t == 0 { 1 } else { 2 };
    drop(o);
    c
}

// `Cell::set` drops the old value inside core, with no `Drop` terminator in `p`.
#[cfg(cell_set_box_in)]
pub fn p(t: u8, cell: &std::cell::Cell<Option<Box<u32, rdep::DepAlloc>>>) -> u8 {
    let c = if t == 0 { 1 } else { 2 };
    cell.set(None);
    c
}

#[cfg(hash_map_box_in)]
pub fn p(t: u8, m: std::collections::HashMap<u8, Box<u32, rdep::DepAlloc>>) -> u8 {
    let c = if t == 0 { 1 } else { 2 };
    drop(m);
    c
}

#[cfg(hash_map_vec_in)]
pub fn p(t: u8, m: std::collections::HashMap<u8, Vec<u8, rdep::DepAlloc>>) -> u8 {
    let c = if t == 0 { 1 } else { 2 };
    drop(m);
    c
}

// `&A` is an allocator that forwards to `A`: not a sysroot allocator either.
#[cfg(opt_box_ref_alloc)]
pub fn p(t: u8, o: Option<Box<u32, &'static rdep::DepAlloc>>) -> u8 {
    let c = if t == 0 { 1 } else { 2 };
    drop(o);
    c
}

#[cfg(vec_in)]
pub fn p(t: u8, v: Vec<u8, rdep::DepAlloc>) -> u8 {
    let c = if t == 0 { 1 } else { 2 };
    drop(v);
    c
}

//[opt_box_in,res_box_in,local_struct_box_in,dep_hbox,opt_dep_hbox]~? RAW "functions_verified":0,
//[opt_box_alias,cell_set_box_in,hash_map_box_in,hash_map_vec_in]~? RAW "functions_verified":0,
//[opt_box_ref_alloc,vec_in]~? RAW "functions_verified":0,
//[local_struct_box_in_scope,local_enum_box_in_scope,local_struct_vec_in_scope]~? RAW "functions_verified":0,
