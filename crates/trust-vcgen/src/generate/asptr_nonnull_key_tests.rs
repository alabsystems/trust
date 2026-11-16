//! Trust (2026-10-04, ASPTR-KEY-1): the FFI non-null fact for an `as_ptr` result is
//! licensed by the compiler-minted key of a std container accessor, never by the
//! rendered path. Pinned on REAL extracted MIR.
//!
//! The string recognizer this replaces (`is_std_container_as_ptr(callee: &str)`)
//! wanted an `as_ptr`/`as_mut_ptr` leaf, a `core`/`std`/`alloc` root and one of a
//! list of container substrings ANYWHERE in the path. std's RAW-SLICE accessor
//! `core::ptr::const_ptr::<impl *const [T]>::as_ptr` returns `self as *const T` —
//! null for a null receiver — and its rendering carries `T`, so `*const
//! [VecDeque<u8>]` supplied `vec_deque` and `*const [Vec<u8>]` supplied
//! `alloc::vec`. Measured on `scratchpad/stage1-w11fix` (2026-10-04): `lie` and
//! `lie_vec` below lost the `FFI strlen: parameter 0 must be non-null` row under
//! default, certify and memory-safe, while `twin` (`*const [u8]`, no substring)
//! kept it as `unknown`; the program segfaults on a null raw slice.

use trust_types::{CalleeKey, Operand, SysrootItem, Terminator, VerifiableFunction};

use super::{STD_NONNULL_AS_PTR_ITEMS, ffi_nonnull_locals, is_std_container_as_ptr};

fn key(item: Option<SysrootItem>, real_sysroot: bool) -> CalleeKey {
    CalleeKey {
        sysroot_item: item,
        krate_is_real_sysroot: real_sysroot,
        krate_name_is_ambiguous: false,
        stable_crate_id: 0x1234,
        krate_name: if real_sysroot { "core".into() } else { "usercrate".into() },
        foreign_block_leaf: None,
        upstream_foreign_link_symbol: None,
        diverging_entry: None,
    }
}

fn load(mir: &str) -> VerifiableFunction {
    serde_json::from_str(mir).expect("the captured MIR fixture must deserialize")
}

/// Is the pointer handed to the FFI `strlen` call a proven non-null local? The
/// question `entry.rs` asks of `ffi_nonnull_locals` before it discharges the
/// `parameter 0 must be non-null` row.
fn strlen_arg_is_nonnull(func: &VerifiableFunction) -> bool {
    let nonnull = ffi_nonnull_locals(func);
    let arg = func
        .body
        .blocks
        .iter()
        .find_map(|b| match &b.terminator {
            Terminator::Call { func: callee, args, .. } if callee.ends_with("::strlen") => {
                args.first()
            }
            _ => None,
        })
        .expect("the fixture calls strlen");
    match arg {
        Operand::Copy(p) | Operand::Move(p) => nonnull.contains(&crate::place_to_var_name(func, p)),
        Operand::Constant(_) => panic!("strlen's argument is a local in every fixture"),
        _ => false,
    }
}

#[test]
fn as_ptr_nonnull_requires_a_std_container_key() {
    // Absent, user, and sysroot-but-untagged keys mint nothing.
    assert!(!is_std_container_as_ptr(None));
    assert!(!is_std_container_as_ptr(Some(&key(None, false))));
    assert!(!is_std_container_as_ptr(Some(&key(None, true))));
    // The raw-slice accessor is std's, and nullable: refused.
    for raw in [SysrootItem::RawSlicePtrAsPtr, SysrootItem::RawSlicePtrAsMutPtr] {
        assert!(!is_std_container_as_ptr(Some(&key(Some(raw), true))), "{raw:?}");
    }
    // Declared `as_ptr` items the string recognizer never admitted stay out.
    for other in [SysrootItem::StringAsPtr, SysrootItem::NonNullAsPtr, SysrootItem::BoxAsPtr] {
        assert!(!is_std_container_as_ptr(Some(&key(Some(other), true))), "{other:?}");
    }
    for item in STD_NONNULL_AS_PTR_ITEMS {
        assert!(is_std_container_as_ptr(Some(&key(Some(*item), true))), "{item:?}");
        // Every admitted tag is one the extractor can mint, and is an `as_ptr`.
        assert!(trust_types::callee_key::item_is_declared(*item), "{item:?} is undeclared");
        assert!(
            trust_types::callee_key::declared_items_with_leaf("as_ptr").contains(item)
                || trust_types::callee_key::declared_items_with_leaf("as_mut_ptr").contains(item),
            "{item:?} is not an as_ptr accessor"
        );
    }
}

#[test]
fn raw_slice_as_ptr_mints_no_nonnull_fact_on_real_mir() {
    // `lie`: `core::ptr::const_ptr::<impl *const [alloc::collections::vec_deque::
    // VecDeque<u8>]>::as_ptr`, and `lie_vec`: `…<impl *const [alloc::vec::Vec<u8>]>
    // ::as_ptr`, both keyed `RawSlicePtrAsPtr`. The string recognizer read
    // `vec_deque` / `alloc::vec` in the generic argument and made `q` (and its
    // cast) non-null.
    assert!(!strlen_arg_is_nonnull(&load(MIR_LIE)), "a null `*const [VecDeque<u8>]`");
    assert!(!strlen_arg_is_nonnull(&load(MIR_LIE_VEC)), "a null `*const [Vec<u8>]`");
    // `twin`: the same shape over `*const [u8]` — refused before and after.
    let twin = load(MIR_TWIN);
    assert!(!strlen_arg_is_nonnull(&twin));
}

#[test]
fn std_container_as_ptr_keeps_its_nonnull_fact_on_real_mir() {
    for (name, mir) in [
        ("std_slice", MIR_STD_SLICE),
        ("std_vec", MIR_STD_VEC),
        ("std_str", MIR_STD_STR),
        ("std_cstr", MIR_STD_CSTR),
    ] {
        assert!(strlen_arg_is_nonnull(&load(mir)), "{name}: std's accessor lost its fact");
    }
}

#[test]
fn a_raw_pointer_receiver_is_refused_even_under_a_container_key() {
    // An extraction that disagrees with its key — a `SliceAsPtr` tag on a call whose
    // receiver is a raw pointer — is refused: the result inherits that pointer's
    // nullness.
    let mut func = load(MIR_STD_SLICE);
    assert!(strlen_arg_is_nonnull(&func));
    let recv = func.body.locals.iter_mut().find(|l| l.index == 1).expect("the receiver `s`");
    let trust_types::Ty::Ref { inner, .. } = recv.ty.clone() else {
        panic!("std_slice's receiver is a reference")
    };
    recv.ty = trust_types::Ty::RawPtr { mutable: false, pointee: inner };
    assert!(!strlen_arg_is_nonnull(&func));
}

/// REAL extracted MIR (`-Ztrust-dump=mir:<dir>`, `scratchpad/stage1-w11fix`,
/// 2026-10-04) of `asptr.rs` (crate `asptr`, `#![feature(slice_ptr_get)]`,
/// `unsafe extern "C" { safe fn strlen(s: *const c_char) -> usize; }`), under
/// `tests/fixtures/vcgen_recognizer_anchor/`:
///
/// ```text
/// pub fn lie(p: *const [VecDeque<u8>]) -> usize { let q = p.as_ptr(); strlen(q as *const c_char) }
/// pub fn lie_vec(p: *const [Vec<u8>]) -> usize { let q = p.as_ptr(); strlen(q as *const c_char) }
/// pub fn twin(p: *const [u8]) -> usize { let q = p.as_ptr(); strlen(q as *const c_char) }
/// pub fn std_slice(s: &[u8]) -> usize { strlen(s.as_ptr() as *const c_char) }
/// pub fn std_vec(v: &Vec<u8>) -> usize { strlen(v.as_ptr() as *const c_char) }
/// pub fn std_str(s: &str) -> usize { strlen(s.as_ptr() as *const c_char) }
/// pub fn std_cstr(s: &CStr) -> usize { strlen(s.as_ptr()) }
/// ```
///
/// Keys as extracted: `RawSlicePtrAsPtr` (lie, lie_vec, twin), `SliceAsPtr`,
/// `VecAsPtr`, `StrAsPtr`, `CStrAsPtr`.
const MIR_LIE: &str =
    include_str!("../../tests/fixtures/vcgen_recognizer_anchor/asptr_lie_mir.json");
const MIR_LIE_VEC: &str =
    include_str!("../../tests/fixtures/vcgen_recognizer_anchor/asptr_lie_vec_mir.json");
const MIR_TWIN: &str =
    include_str!("../../tests/fixtures/vcgen_recognizer_anchor/asptr_twin_mir.json");
const MIR_STD_SLICE: &str =
    include_str!("../../tests/fixtures/vcgen_recognizer_anchor/asptr_std_slice_mir.json");
const MIR_STD_VEC: &str =
    include_str!("../../tests/fixtures/vcgen_recognizer_anchor/asptr_std_vec_mir.json");
const MIR_STD_STR: &str =
    include_str!("../../tests/fixtures/vcgen_recognizer_anchor/asptr_std_str_mir.json");
const MIR_STD_CSTR: &str =
    include_str!("../../tests/fixtures/vcgen_recognizer_anchor/asptr_std_cstr_mir.json");
