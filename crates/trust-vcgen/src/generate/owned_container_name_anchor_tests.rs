//! Trust (2026-10-04, OWNED-VEC-NAME-1): an owned std container is named by its
//! EXACT std path, never by the last segment of its rendered type name. Pinned on
//! REAL extracted MIR.

use trust_types::{Operand, Place, Projection, Ty, VerifiableFunction};

use super::collection_range::is_std_string_adt_name;
use super::{
    collection_abstract_len_with_base_opts, is_owned_slice_container_name,
    ty_is_owned_slice_container,
};
use crate::guards;

// ── THE OWNED-CONTAINER TYPE NAME (Trust, 2026-10-04, OWNED-VEC-NAME-1) ──────
//
// `panic_calls::is_owned_slice_container_name` decided "this `Ty::Adt` is std's
// `Vec`" by `tail == "Vec"` on the rendered name, and `guards::
// owned_container_len_var` decided "std's `String`" by `tail == "String"`. Both
// admit a fact about std's container — one length, read by `len`/`is_empty` and
// bounding `Index<usize>` — for ANY type with that last segment. A user `struct
// Vec` (or `struct String`) reaches std's methods only through its OWN `Deref`,
// which need not return the same container twice. Measured on the stage 1 of
// `38e6c69b1c` (`scratchpad/stage1-w11fix`), with the `deref` below alternating
// two fields:
//
//  * `h2`: `if w.is_empty() { return 0; } w.len() - 1` read `overflow:sub proved`
//    with the check elided (default, strict, certify), through the guard fact
//    `coll_len(w) > 0` on the ROOT `w: &uvh2::Vec`;
//  * `k`: `if i < w.len() { w[i] } else { 0 }` read `slice proved` (default,
//    strict), through the index-bound recovery `coll_len(w)` on the same root;
//  * `fld`: the same `h2` body on a `uvh2::Vec` held in a struct field read
//    `overflow:sub proved` (the field-place arm);
//  * `s2`: the `h2` body on a user `struct String` read `overflow:sub proved`.
//
// The same code with the type renamed (`Wrap`, `SWrap`) read `overflow:sub FAILED`
// and the `slice` row `unknown`: the name was the proof. Both tests now take the
// exact path (`alloc::vec::Vec`/`std::vec::Vec`, `alloc::string::String`/
// `std::string::String`). std's `Vec` is `Ty::Seq` and std's `String` is
// `alloc::string::String` in the extracted MIR below, so neither real container
// loses its fact.
//
// The rows below query each gate on the ROOT operand (`w`, the field reborrow
// `&(*f).v`), which no `Deref` hop sits between, so they pin the type test
// alone. Where a row queries the `Deref` result (`_3`, `_7`), it asserts only
// that the fact does not name the root's length: the hop itself is
// DEREF-ANCHOR-1's, and whether it is taken must not change these rows.

/// REAL extracted MIR (`-Ztrust-dump=mir:<dir>`, stage 1 of `38e6c69b1c`,
/// `scratchpad/stage1-w11fix`, 2026-10-04) of `uvh2.rs`, crate `uvh2`:
///
/// ```text
/// use std::cell::Cell;
/// pub struct Vec { pub a: std::vec::Vec<u32>, pub b: std::vec::Vec<u32>, pub flip: Cell<bool> }
/// impl core::ops::Deref for Vec {
///     type Target = std::vec::Vec<u32>;
///     fn deref(&self) -> &std::vec::Vec<u32> {
///         let f = self.flip.get(); self.flip.set(!f);
///         if f { &self.b } else { &self.a }
///     }
/// }
/// pub fn h2(w: &Vec) -> usize {
///     if w.is_empty() { return 0; }
///     w.len() - 1
/// }
/// ```
///
/// `w` (local 1) is `&uvh2::Vec`; `_3 = <uvh2::Vec as core::ops::deref::Deref>::
/// deref(w)` is `is_empty`'s receiver and `_5` (a second `deref(w)`) is `len`'s.
const MIR_UVH2_H2: &str = r#"{"name":"h2","def_path":"uvh2::h2","span":{"file":"uvh2.rs","line_start":10,"col_start":0,"line_end":13,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":1,"ty":{"Ref":{"mutable":false,"inner":{"Adt":{"name":"uvh2::Vec","fields":[["a",{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}],["b",{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}],["flip",{"Adt":{"name":"core::cell::Cell","fields":[["value",{"Adt":{"name":"core::cell::UnsafeCell","fields":[["value","Bool"]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}}},"name":"w"},{"index":2,"ty":"Bool","name":null},{"index":3,"ty":{"Ref":{"mutable":false,"inner":{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}}},"name":null},{"index":4,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":5,"ty":{"Ref":{"mutable":false,"inner":{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}}},"name":null},{"index":6,"ty":{"Tuple":[{"Int":{"width":64,"signed":false}},"Bool"]},"name":null}],"blocks":[{"id":0,"stmts":[],"terminator":{"Call":{"func":"<uvh2::Vec as core::ops::deref::Deref>::deref","args":[{"Copy":{"local":1,"projections":[]}}],"dest":{"local":3,"projections":[]},"target":1,"span":{"file":"uvh2.rs","line_start":11,"col_start":7,"line_end":11,"col_end":19},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":4448,"substs_digest":[15001299059563082412,13822348516475929551]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":1,"stmts":[],"terminator":{"Call":{"func":"alloc::vec::Vec::<u32>::is_empty","args":[{"Copy":{"local":3,"projections":[]}}],"dest":{"local":2,"projections":[]},"target":2,"span":{"file":"uvh2.rs","line_start":11,"col_start":7,"line_end":11,"col_end":19},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":8369930371133358469,"def_index":8822,"substs_digest":[937863789039580281,9258672918316184405]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":8369930371133358469,"krate_name":"alloc"}}}},{"id":2,"stmts":[],"terminator":{"SwitchInt":{"discr":{"Move":{"local":2,"projections":[]}},"targets":[[0,4]],"otherwise":3,"exhaustive_enum_unreachable":false,"span":{"file":"uvh2.rs","line_start":11,"col_start":7,"line_end":11,"col_end":19}}}},{"id":3,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Constant":{"Uint":[0,64]}}},"span":{"file":"uvh2.rs","line_start":11,"col_start":29,"line_end":11,"col_end":30}}}],"terminator":{"Goto":8}},{"id":4,"stmts":[],"terminator":{"Call":{"func":"<uvh2::Vec as core::ops::deref::Deref>::deref","args":[{"Copy":{"local":1,"projections":[]}}],"dest":{"local":5,"projections":[]},"target":5,"span":{"file":"uvh2.rs","line_start":12,"col_start":4,"line_end":12,"col_end":11},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":4448,"substs_digest":[15001299059563082412,13822348516475929551]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":5,"stmts":[],"terminator":{"Call":{"func":"alloc::vec::Vec::<u32>::len","args":[{"Copy":{"local":5,"projections":[]}}],"dest":{"local":4,"projections":[]},"target":6,"span":{"file":"uvh2.rs","line_start":12,"col_start":4,"line_end":12,"col_end":11},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":8369930371133358469,"def_index":8821,"substs_digest":[937863789039580281,9258672918316184405]},"callee_key":{"sysroot_item":"VecLen","krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":8369930371133358469,"krate_name":"alloc"}}}},{"id":6,"stmts":[{"Assign":{"place":{"local":6,"projections":[]},"rvalue":{"CheckedBinaryOp":["Sub",{"Copy":{"local":4,"projections":[]}},{"Constant":{"Uint":[1,64]}}]},"span":{"file":"uvh2.rs","line_start":12,"col_start":4,"line_end":12,"col_end":15}}}],"terminator":{"Assert":{"cond":{"Move":{"local":6,"projections":[{"Field":1}]}},"expected":false,"msg":{"Overflow":"Sub"},"target":7,"span":{"file":"uvh2.rs","line_start":12,"col_start":4,"line_end":12,"col_end":15},"unwind":"Continue"}}},{"id":7,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Move":{"local":6,"projections":[{"Field":0}]}}},"span":{"file":"uvh2.rs","line_start":12,"col_start":4,"line_end":12,"col_end":15}}}],"terminator":{"Goto":8}},{"id":8,"stmts":[],"terminator":"Return"}],"arg_count":1,"return_ty":{"Int":{"width":64,"signed":false}}},"contracts":[],"preconditions":[],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"#;

/// REAL extracted MIR (same compiler, same file) of
/// `pub fn k(w: &Vec, i: usize) -> u32 { if i < w.len() { w[i] } else { 0 } }`:
/// `_5 = deref(w)` is `len`'s receiver, `_7 = deref(w)` is the receiver of std's
/// `<alloc::vec::Vec<u32> as core::ops::index::Index<usize>>::index`.
const MIR_UVH2_K: &str = r#"{"name":"k","def_path":"uvh2::k","span":{"file":"uvh2.rs","line_start":14,"col_start":0,"line_end":16,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Int":{"width":32,"signed":false}},"name":null},{"index":1,"ty":{"Ref":{"mutable":false,"inner":{"Adt":{"name":"uvh2::Vec","fields":[["a",{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}],["b",{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}],["flip",{"Adt":{"name":"core::cell::Cell","fields":[["value",{"Adt":{"name":"core::cell::UnsafeCell","fields":[["value","Bool"]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}}},"name":"w"},{"index":2,"ty":{"Int":{"width":64,"signed":false}},"name":"i"},{"index":3,"ty":"Bool","name":null},{"index":4,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":5,"ty":{"Ref":{"mutable":false,"inner":{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}}},"name":null},{"index":6,"ty":{"Ref":{"mutable":false,"inner":{"Int":{"width":32,"signed":false}}}},"name":null},{"index":7,"ty":{"Ref":{"mutable":false,"inner":{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}}},"name":null}],"blocks":[{"id":0,"stmts":[],"terminator":{"Call":{"func":"<uvh2::Vec as core::ops::deref::Deref>::deref","args":[{"Copy":{"local":1,"projections":[]}}],"dest":{"local":5,"projections":[]},"target":1,"span":{"file":"uvh2.rs","line_start":15,"col_start":11,"line_end":15,"col_end":18},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":4448,"substs_digest":[15001299059563082412,13822348516475929551]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":1,"stmts":[],"terminator":{"Call":{"func":"alloc::vec::Vec::<u32>::len","args":[{"Copy":{"local":5,"projections":[]}}],"dest":{"local":4,"projections":[]},"target":2,"span":{"file":"uvh2.rs","line_start":15,"col_start":11,"line_end":15,"col_end":18},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":8369930371133358469,"def_index":8821,"substs_digest":[937863789039580281,9258672918316184405]},"callee_key":{"sysroot_item":"VecLen","krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":8369930371133358469,"krate_name":"alloc"}}}},{"id":2,"stmts":[{"Assign":{"place":{"local":3,"projections":[]},"rvalue":{"BinaryOp":["Lt",{"Copy":{"local":2,"projections":[]}},{"Move":{"local":4,"projections":[]}}]},"span":{"file":"uvh2.rs","line_start":15,"col_start":7,"line_end":15,"col_end":18}}}],"terminator":{"SwitchInt":{"discr":{"Move":{"local":3,"projections":[]}},"targets":[[0,6]],"otherwise":3,"exhaustive_enum_unreachable":false,"span":{"file":"uvh2.rs","line_start":15,"col_start":7,"line_end":15,"col_end":18}}}},{"id":3,"stmts":[],"terminator":{"Call":{"func":"<uvh2::Vec as core::ops::deref::Deref>::deref","args":[{"Copy":{"local":1,"projections":[]}}],"dest":{"local":7,"projections":[]},"target":4,"span":{"file":"uvh2.rs","line_start":15,"col_start":21,"line_end":15,"col_end":22},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":4448,"substs_digest":[15001299059563082412,13822348516475929551]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":4,"stmts":[],"terminator":{"Call":{"func":"<alloc::vec::Vec<u32> as core::ops::index::Index<usize>>::index","args":[{"Copy":{"local":7,"projections":[]}},{"Copy":{"local":2,"projections":[]}}],"dest":{"local":6,"projections":[]},"target":5,"span":{"file":"uvh2.rs","line_start":15,"col_start":22,"line_end":15,"col_end":25},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":39089,"substs_digest":[17091007639459144612,2033056495210424997]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":5,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Copy":{"local":6,"projections":["Deref"]}}},"span":{"file":"uvh2.rs","line_start":15,"col_start":21,"line_end":15,"col_end":25}}}],"terminator":{"Goto":7}},{"id":6,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Constant":{"Uint":[0,32]}}},"span":{"file":"uvh2.rs","line_start":15,"col_start":35,"line_end":15,"col_end":36}}}],"terminator":{"Goto":7}},{"id":7,"stmts":[],"terminator":"Return"}],"arg_count":2,"return_ty":{"Int":{"width":32,"signed":false}}},"contracts":[],"preconditions":[{"And":[{"Ge":[{"Var":["i","Int"]},{"Int":0}]},{"Le":[{"Var":["i","Int"]},{"Int":18446744073709551615}]}]}],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"#;

/// REAL extracted MIR (same compiler, same file) of
///
/// ```text
/// pub struct Fld { pub v: Vec }
/// pub fn fld(f: &Fld) -> usize {
///     if f.v.is_empty() { return 0; }
///     f.v.len() - 1
/// }
/// ```
///
/// `_4 = &((*f).v)` (a shared field reborrow of the user `Vec`) is moved into
/// `_3 = deref(_4)`, `is_empty`'s receiver.
const MIR_UVH2_FLD: &str = r#"{"name":"fld","def_path":"uvh2::fld","span":{"file":"uvh2.rs","line_start":18,"col_start":0,"line_end":21,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":1,"ty":{"Ref":{"mutable":false,"inner":{"Adt":{"name":"uvh2::Fld","fields":[["v",{"Adt":{"name":"uvh2::Vec","fields":[["a",{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}],["b",{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}],["flip",{"Adt":{"name":"core::cell::Cell","fields":[["value",{"Adt":{"name":"core::cell::UnsafeCell","fields":[["value","Bool"]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}}},"name":"f"},{"index":2,"ty":"Bool","name":null},{"index":3,"ty":{"Ref":{"mutable":false,"inner":{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}}},"name":null},{"index":4,"ty":{"Ref":{"mutable":false,"inner":{"Adt":{"name":"uvh2::Vec","fields":[["a",{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}],["b",{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}],["flip",{"Adt":{"name":"core::cell::Cell","fields":[["value",{"Adt":{"name":"core::cell::UnsafeCell","fields":[["value","Bool"]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}}},"name":null},{"index":5,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":6,"ty":{"Ref":{"mutable":false,"inner":{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}}},"name":null},{"index":7,"ty":{"Ref":{"mutable":false,"inner":{"Adt":{"name":"uvh2::Vec","fields":[["a",{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}],["b",{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}],["flip",{"Adt":{"name":"core::cell::Cell","fields":[["value",{"Adt":{"name":"core::cell::UnsafeCell","fields":[["value","Bool"]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}}},"name":null},{"index":8,"ty":{"Tuple":[{"Int":{"width":64,"signed":false}},"Bool"]},"name":null}],"blocks":[{"id":0,"stmts":[{"Assign":{"place":{"local":4,"projections":[]},"rvalue":{"Ref":{"mutable":false,"place":{"local":1,"projections":["Deref",{"Field":0}]}}},"span":{"file":"uvh2.rs","line_start":19,"col_start":7,"line_end":19,"col_end":10}}}],"terminator":{"Call":{"func":"<uvh2::Vec as core::ops::deref::Deref>::deref","args":[{"Move":{"local":4,"projections":[]}}],"dest":{"local":3,"projections":[]},"target":1,"span":{"file":"uvh2.rs","line_start":19,"col_start":7,"line_end":19,"col_end":21},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":4448,"substs_digest":[15001299059563082412,13822348516475929551]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":1,"stmts":[],"terminator":{"Call":{"func":"alloc::vec::Vec::<u32>::is_empty","args":[{"Copy":{"local":3,"projections":[]}}],"dest":{"local":2,"projections":[]},"target":2,"span":{"file":"uvh2.rs","line_start":19,"col_start":7,"line_end":19,"col_end":21},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":8369930371133358469,"def_index":8822,"substs_digest":[937863789039580281,9258672918316184405]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":8369930371133358469,"krate_name":"alloc"}}}},{"id":2,"stmts":[],"terminator":{"SwitchInt":{"discr":{"Move":{"local":2,"projections":[]}},"targets":[[0,4]],"otherwise":3,"exhaustive_enum_unreachable":false,"span":{"file":"uvh2.rs","line_start":19,"col_start":7,"line_end":19,"col_end":21}}}},{"id":3,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Constant":{"Uint":[0,64]}}},"span":{"file":"uvh2.rs","line_start":19,"col_start":31,"line_end":19,"col_end":32}}}],"terminator":{"Goto":8}},{"id":4,"stmts":[{"Assign":{"place":{"local":7,"projections":[]},"rvalue":{"Ref":{"mutable":false,"place":{"local":1,"projections":["Deref",{"Field":0}]}}},"span":{"file":"uvh2.rs","line_start":20,"col_start":4,"line_end":20,"col_end":7}}}],"terminator":{"Call":{"func":"<uvh2::Vec as core::ops::deref::Deref>::deref","args":[{"Move":{"local":7,"projections":[]}}],"dest":{"local":6,"projections":[]},"target":5,"span":{"file":"uvh2.rs","line_start":20,"col_start":4,"line_end":20,"col_end":13},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":4448,"substs_digest":[15001299059563082412,13822348516475929551]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":5,"stmts":[],"terminator":{"Call":{"func":"alloc::vec::Vec::<u32>::len","args":[{"Copy":{"local":6,"projections":[]}}],"dest":{"local":5,"projections":[]},"target":6,"span":{"file":"uvh2.rs","line_start":20,"col_start":4,"line_end":20,"col_end":13},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":8369930371133358469,"def_index":8821,"substs_digest":[937863789039580281,9258672918316184405]},"callee_key":{"sysroot_item":"VecLen","krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":8369930371133358469,"krate_name":"alloc"}}}},{"id":6,"stmts":[{"Assign":{"place":{"local":8,"projections":[]},"rvalue":{"CheckedBinaryOp":["Sub",{"Copy":{"local":5,"projections":[]}},{"Constant":{"Uint":[1,64]}}]},"span":{"file":"uvh2.rs","line_start":20,"col_start":4,"line_end":20,"col_end":17}}}],"terminator":{"Assert":{"cond":{"Move":{"local":8,"projections":[{"Field":1}]}},"expected":false,"msg":{"Overflow":"Sub"},"target":7,"span":{"file":"uvh2.rs","line_start":20,"col_start":4,"line_end":20,"col_end":17},"unwind":"Continue"}}},{"id":7,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Move":{"local":8,"projections":[{"Field":0}]}}},"span":{"file":"uvh2.rs","line_start":20,"col_start":4,"line_end":20,"col_end":17}}}],"terminator":{"Goto":8}},{"id":8,"stmts":[],"terminator":"Return"}],"arg_count":1,"return_ty":{"Int":{"width":64,"signed":false}}},"contracts":[],"preconditions":[],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"#;

/// REAL extracted MIR (same compiler, same file) of the std control
/// `pub fn h2_std(v: &std::vec::Vec<u32>) -> usize { if v.is_empty() { return 0; } v.len() - 1 }`:
/// `v` (local 1) is `&Seq<u32>`, and `is_empty`/`len` take it directly.
const MIR_UVH2_H2_STD: &str = r#"{"name":"h2_std","def_path":"uvh2::h2_std","span":{"file":"uvh2.rs","line_start":22,"col_start":0,"line_end":25,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":1,"ty":{"Ref":{"mutable":false,"inner":{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}}},"name":"v"},{"index":2,"ty":"Bool","name":null},{"index":3,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":4,"ty":{"Tuple":[{"Int":{"width":64,"signed":false}},"Bool"]},"name":null}],"blocks":[{"id":0,"stmts":[],"terminator":{"Call":{"func":"alloc::vec::Vec::<u32>::is_empty","args":[{"Copy":{"local":1,"projections":[]}}],"dest":{"local":2,"projections":[]},"target":1,"span":{"file":"uvh2.rs","line_start":23,"col_start":7,"line_end":23,"col_end":19},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":8369930371133358469,"def_index":8822,"substs_digest":[937863789039580281,9258672918316184405]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":8369930371133358469,"krate_name":"alloc"}}}},{"id":1,"stmts":[],"terminator":{"SwitchInt":{"discr":{"Move":{"local":2,"projections":[]}},"targets":[[0,3]],"otherwise":2,"exhaustive_enum_unreachable":false,"span":{"file":"uvh2.rs","line_start":23,"col_start":7,"line_end":23,"col_end":19}}}},{"id":2,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Constant":{"Uint":[0,64]}}},"span":{"file":"uvh2.rs","line_start":23,"col_start":29,"line_end":23,"col_end":30}}}],"terminator":{"Goto":6}},{"id":3,"stmts":[],"terminator":{"Call":{"func":"alloc::vec::Vec::<u32>::len","args":[{"Copy":{"local":1,"projections":[]}}],"dest":{"local":3,"projections":[]},"target":4,"span":{"file":"uvh2.rs","line_start":24,"col_start":4,"line_end":24,"col_end":11},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":8369930371133358469,"def_index":8821,"substs_digest":[937863789039580281,9258672918316184405]},"callee_key":{"sysroot_item":"VecLen","krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":8369930371133358469,"krate_name":"alloc"}}}},{"id":4,"stmts":[{"Assign":{"place":{"local":4,"projections":[]},"rvalue":{"CheckedBinaryOp":["Sub",{"Copy":{"local":3,"projections":[]}},{"Constant":{"Uint":[1,64]}}]},"span":{"file":"uvh2.rs","line_start":24,"col_start":4,"line_end":24,"col_end":15}}}],"terminator":{"Assert":{"cond":{"Move":{"local":4,"projections":[{"Field":1}]}},"expected":false,"msg":{"Overflow":"Sub"},"target":5,"span":{"file":"uvh2.rs","line_start":24,"col_start":4,"line_end":24,"col_end":15},"unwind":"Continue"}}},{"id":5,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Move":{"local":4,"projections":[{"Field":0}]}}},"span":{"file":"uvh2.rs","line_start":24,"col_start":4,"line_end":24,"col_end":15}}}],"terminator":{"Goto":6}},{"id":6,"stmts":[],"terminator":"Return"}],"arg_count":1,"return_ty":{"Int":{"width":64,"signed":false}}},"contracts":[],"preconditions":[],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"#;

/// REAL extracted MIR (same compiler) of `ustr.rs`, crate `ustr`: the `h2` shape on
/// a user `struct String` whose `Deref<Target = std::string::String>` alternates
/// two fields:
///
/// ```text
/// pub fn s2(w: &String) -> usize {
///     if w.is_empty() { return 0; }
///     w.len() - 1
/// }
/// ```
///
/// `w` (local 1) is `&ustr::String`; `_2 = deref(w)` is `is_empty`'s receiver.
const MIR_USTR_S2: &str = r#"{"name":"s2","def_path":"ustr::s2","span":{"file":"ustr.rs","line_start":10,"col_start":0,"line_end":13,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":1,"ty":{"Ref":{"mutable":false,"inner":{"Adt":{"name":"ustr::String","fields":[["a",{"Adt":{"name":"alloc::string::String","fields":[["vec",{"Seq":{"elem":{"Int":{"width":8,"signed":false}}}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}],["b",{"Adt":{"name":"alloc::string::String","fields":[["vec",{"Seq":{"elem":{"Int":{"width":8,"signed":false}}}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}],["flip",{"Adt":{"name":"core::cell::Cell","fields":[["value",{"Adt":{"name":"core::cell::UnsafeCell","fields":[["value","Bool"]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}}},"name":"w"},{"index":2,"ty":{"Ref":{"mutable":false,"inner":{"Adt":{"name":"alloc::string::String","fields":[["vec",{"Seq":{"elem":{"Int":{"width":8,"signed":false}}}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}}},"name":null},{"index":3,"ty":"Bool","name":null},{"index":4,"ty":{"Ref":{"mutable":false,"inner":{"Adt":{"name":"alloc::string::String","fields":[["vec",{"Seq":{"elem":{"Int":{"width":8,"signed":false}}}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}}},"name":null},{"index":5,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":6,"ty":{"Tuple":[{"Int":{"width":64,"signed":false}},"Bool"]},"name":null}],"blocks":[{"id":0,"stmts":[],"terminator":{"Call":{"func":"<ustr::String as core::ops::deref::Deref>::deref","args":[{"Copy":{"local":1,"projections":[]}}],"dest":{"local":2,"projections":[]},"target":3,"span":{"file":"ustr.rs","line_start":11,"col_start":7,"line_end":11,"col_end":7},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":4448,"substs_digest":[11361491447678204225,10888750686226387501]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":1,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Constant":{"Uint":[0,64]}}},"span":{"file":"ustr.rs","line_start":11,"col_start":22,"line_end":11,"col_end":22}}}],"terminator":"Return"},{"id":2,"stmts":[],"terminator":{"Call":{"func":"<ustr::String as core::ops::deref::Deref>::deref","args":[{"Copy":{"local":1,"projections":[]}}],"dest":{"local":4,"projections":[]},"target":5,"span":{"file":"ustr.rs","line_start":12,"col_start":4,"line_end":12,"col_end":4},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":4448,"substs_digest":[11361491447678204225,10888750686226387501]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":3,"stmts":[],"terminator":{"Call":{"func":"alloc::string::String::is_empty","args":[{"Copy":{"local":2,"projections":[]}}],"dest":{"local":3,"projections":[]},"target":4,"span":{"file":"ustr.rs","line_start":11,"col_start":9,"line_end":11,"col_end":9},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":8369930371133358469,"def_index":6999,"substs_digest":[14241860155052752853,2268345107747320411]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":8369930371133358469,"krate_name":"alloc"}}}},{"id":4,"stmts":[],"terminator":{"SwitchInt":{"discr":{"Copy":{"local":3,"projections":[]}},"targets":[[0,2]],"otherwise":1,"exhaustive_enum_unreachable":false,"span":{"file":"ustr.rs","line_start":11,"col_start":4,"line_end":11,"col_end":4}}}},{"id":5,"stmts":[],"terminator":{"Call":{"func":"alloc::string::String::len","args":[{"Copy":{"local":4,"projections":[]}}],"dest":{"local":5,"projections":[]},"target":6,"span":{"file":"ustr.rs","line_start":12,"col_start":6,"line_end":12,"col_end":6},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":8369930371133358469,"def_index":6998,"substs_digest":[14241860155052752853,2268345107747320411]},"callee_key":{"sysroot_item":"StringLen","krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":8369930371133358469,"krate_name":"alloc"}}}},{"id":6,"stmts":[{"Assign":{"place":{"local":6,"projections":[]},"rvalue":{"CheckedBinaryOp":["Sub",{"Copy":{"local":5,"projections":[]}},{"Constant":{"Uint":[1,64]}}]},"span":{"file":"ustr.rs","line_start":12,"col_start":4,"line_end":12,"col_end":4}}}],"terminator":{"Assert":{"cond":{"Move":{"local":6,"projections":[{"Field":1}]}},"expected":false,"msg":{"Overflow":"Sub"},"target":7,"span":{"file":"ustr.rs","line_start":12,"col_start":4,"line_end":12,"col_end":4},"unwind":"Continue"}}},{"id":7,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Copy":{"local":6,"projections":[{"Field":0}]}}},"span":{"file":"ustr.rs","line_start":13,"col_start":1,"line_end":13,"col_end":1}}}],"terminator":"Return"}],"arg_count":1,"return_ty":{"Int":{"width":64,"signed":false}}},"contracts":[],"preconditions":[],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"#;

/// REAL extracted MIR (same compiler, same file) of the std control
/// `pub fn s2_std(v: &std::string::String) -> usize { if v.is_empty() { return 0; } v.len() - 1 }`:
/// `v` (local 1) is `&alloc::string::String`.
const MIR_USTR_S2_STD: &str = r#"{"name":"s2_std","def_path":"ustr::s2_std","span":{"file":"ustr.rs","line_start":14,"col_start":0,"line_end":17,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":1,"ty":{"Ref":{"mutable":false,"inner":{"Adt":{"name":"alloc::string::String","fields":[["vec",{"Seq":{"elem":{"Int":{"width":8,"signed":false}}}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}}},"name":"v"},{"index":2,"ty":"Bool","name":null},{"index":3,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":4,"ty":{"Tuple":[{"Int":{"width":64,"signed":false}},"Bool"]},"name":null}],"blocks":[{"id":0,"stmts":[],"terminator":{"Call":{"func":"alloc::string::String::is_empty","args":[{"Copy":{"local":1,"projections":[]}}],"dest":{"local":2,"projections":[]},"target":3,"span":{"file":"ustr.rs","line_start":15,"col_start":9,"line_end":15,"col_end":9},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":8369930371133358469,"def_index":6999,"substs_digest":[14241860155052752853,2268345107747320411]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":8369930371133358469,"krate_name":"alloc"}}}},{"id":1,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Constant":{"Uint":[0,64]}}},"span":{"file":"ustr.rs","line_start":15,"col_start":22,"line_end":15,"col_end":22}}}],"terminator":"Return"},{"id":2,"stmts":[],"terminator":{"Call":{"func":"alloc::string::String::len","args":[{"Copy":{"local":1,"projections":[]}}],"dest":{"local":3,"projections":[]},"target":4,"span":{"file":"ustr.rs","line_start":16,"col_start":6,"line_end":16,"col_end":6},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":8369930371133358469,"def_index":6998,"substs_digest":[14241860155052752853,2268345107747320411]},"callee_key":{"sysroot_item":"StringLen","krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":8369930371133358469,"krate_name":"alloc"}}}},{"id":3,"stmts":[],"terminator":{"SwitchInt":{"discr":{"Copy":{"local":2,"projections":[]}},"targets":[[0,2]],"otherwise":1,"exhaustive_enum_unreachable":false,"span":{"file":"ustr.rs","line_start":15,"col_start":4,"line_end":15,"col_end":4}}}},{"id":4,"stmts":[{"Assign":{"place":{"local":4,"projections":[]},"rvalue":{"CheckedBinaryOp":["Sub",{"Copy":{"local":3,"projections":[]}},{"Constant":{"Uint":[1,64]}}]},"span":{"file":"ustr.rs","line_start":16,"col_start":4,"line_end":16,"col_end":4}}}],"terminator":{"Assert":{"cond":{"Move":{"local":4,"projections":[{"Field":1}]}},"expected":false,"msg":{"Overflow":"Sub"},"target":5,"span":{"file":"ustr.rs","line_start":16,"col_start":4,"line_end":16,"col_end":4},"unwind":"Continue"}}},{"id":5,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Copy":{"local":4,"projections":[{"Field":0}]}}},"span":{"file":"ustr.rs","line_start":17,"col_start":1,"line_end":17,"col_end":1}}}],"terminator":"Return"}],"arg_count":1,"return_ty":{"Int":{"width":64,"signed":false}}},"contracts":[],"preconditions":[],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"#;

fn parse_mir(mir: &str) -> VerifiableFunction {
    serde_json::from_str(mir).expect("the captured MIR fixture must deserialize")
}

/// The pointee of local `local`'s `&T` type.
fn pointee(func: &VerifiableFunction, local: usize) -> Ty {
    match &func.body.locals[local].ty {
        Ty::Ref { inner, .. } => (**inner).clone(),
        other => panic!("local {local} is not a reference: {other:?}"),
    }
}

/// The name of the length var `owned_container_len_var` mints for `op`, if any.
fn guard_len_name(func: &VerifiableFunction, op: &Operand) -> Option<String> {
    guards::owned_container_len_var(func, op).and_then(|f| f.var_name().map(str::to_owned))
}

const IMPERSONATOR_STAMP: &str = "__trust_crate@0fa449fe5b896344::";

#[test]
fn a_user_struct_named_vec_is_not_an_owned_slice_container() {
    // The user type exactly as the producer named it.
    let h2 = parse_mir(MIR_UVH2_H2);
    let user_vec = pointee(&h2, 1);
    assert!(matches!(&user_vec, Ty::Adt { name, .. } if name == "uvh2::Vec"), "{user_vec:?}");
    assert!(!ty_is_owned_slice_container(&user_vec), "{user_vec:?}");
    let stamped = format!("{IMPERSONATOR_STAMP}alloc::vec::Vec<u32>");
    for name in [
        "uvh2::Vec",
        "uvh2::Vec<u32>",
        "user::vec::Vec<u32>",
        "mycrate::alloc::vec::Vec",
        "Vec",
        "Vec<u32>",
        stamped.as_str(),
    ] {
        assert!(!is_owned_slice_container_name(name), "`{name}` is not std's `Vec`");
        assert!(!ty_is_owned_slice_container(&Ty::adt(name, vec![])), "`{name}`");
    }
    // std's `Vec`: the extractor's `Seq` (as extracted), and the exact path a
    // faithful-lane `Ty::Adt` carries.
    let h2_std = parse_mir(MIR_UVH2_H2_STD);
    let std_vec = pointee(&h2_std, 1);
    assert!(matches!(std_vec, Ty::Seq { .. }), "{std_vec:?}");
    assert!(ty_is_owned_slice_container(&std_vec));
    for name in ["alloc::vec::Vec", "alloc::vec::Vec<u32>", "std::vec::Vec", "std::vec::Vec<u32>"] {
        assert!(is_owned_slice_container_name(name), "`{name}` is std's `Vec`");
        assert!(ty_is_owned_slice_container(&Ty::adt(name, vec![])), "`{name}`");
    }
}

#[test]
fn a_user_struct_named_string_is_not_std_string() {
    let s2 = parse_mir(MIR_USTR_S2);
    assert!(matches!(&pointee(&s2, 1), Ty::Adt { name, .. } if name == "ustr::String"));
    let stamped = format!("{IMPERSONATOR_STAMP}alloc::string::String");
    for name in ["ustr::String", "String", "mycrate::string::String", stamped.as_str()] {
        assert!(!is_std_string_adt_name(name), "`{name}` is not std's `String`");
    }
    let s2_std = parse_mir(MIR_USTR_S2_STD);
    assert!(
        matches!(&pointee(&s2_std, 1), Ty::Adt { name, .. } if is_std_string_adt_name(name)),
        "the extracted std `String` must keep its name: {:?}",
        pointee(&s2_std, 1)
    );
    assert!(is_std_string_adt_name("std::string::String"));
}

#[test]
fn the_is_empty_guard_names_no_length_on_a_user_vec_root() {
    let h2 = parse_mir(MIR_UVH2_H2);
    let root = guards::coll_len_var(&h2, 1).var_name().map(str::to_owned);
    assert!(root.is_some());
    // The root `w: &uvh2::Vec`: the type gate alone.
    assert_eq!(guard_len_name(&h2, &Operand::Copy(Place::local(1))), None);
    // `is_empty`'s receiver `_3 = deref(w)`: the fact must not name `w`'s length.
    assert_ne!(guard_len_name(&h2, &Operand::Copy(Place::local(3))), root);
    // std's `&Vec<u32>` (`Seq`) keeps its length var.
    let h2_std = parse_mir(MIR_UVH2_H2_STD);
    assert_eq!(
        guard_len_name(&h2_std, &Operand::Copy(Place::local(1))),
        guards::coll_len_var(&h2_std, 1).var_name().map(str::to_owned)
    );
}

/// The `Cell<bool>` the extracted `uvh2::Vec` holds in `flip`, exactly as
/// [`MIR_UVH2_FLD`] spells it.
const FLIP_CELL_BOOL: &str = r#"{"Adt":{"name":"core::cell::Cell","fields":[["value",{"Adt":{"name":"core::cell::UnsafeCell","fields":[["value","Bool"]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}"#;

/// [`MIR_UVH2_FLD`] with `uvh2::Vec`'s `flip: Cell<bool>` re-typed `flip: bool` at every
/// occurrence (`f`'s `&Fld` and `_4`'s `&uvh2::Vec`): a `Freeze` user `Vec` in the same
/// field shape. DERIVED, not extracted — the statements are unchanged, as `fld` never
/// names `flip` (only the user `deref` does).
fn fld_with_a_freeze_user_vec() -> VerifiableFunction {
    assert_eq!(MIR_UVH2_FLD.matches(FLIP_CELL_BOOL).count(), 3, "the edit must hit every `flip`");
    let edited = MIR_UVH2_FLD.replace(FLIP_CELL_BOOL, r#""Bool""#);
    assert!(!edited.contains("Cell"));
    parse_mir(&edited)
}

/// Trust: 2026-10-15 (INTERIOR-MUT-CHANNEL-1 re-pin). Until G2 this row asserted that
/// `_4 = &((*f).v)` traces to the FIELD place `(*f).v`. The extracted `uvh2::Vec` holds
/// `flip: Cell<bool>`, which its own `deref(&self)` writes on every call, so `(*f).v`
/// holds `UnsafeCell` bytes a shared reference does not freeze: it is not one value for
/// the whole body (`place_is_body_stable`, G2's "a place behind the root's `Deref` whose
/// type may hold a cell"), and the trace stops at `_4`. The field arm's TYPE gate is
/// pinned on the `Freeze` twin below, which still reaches it.
#[test]
fn the_is_empty_guard_names_no_length_on_a_user_vec_field() {
    let fld = parse_mir(MIR_UVH2_FLD);
    let field = Place { local: 1, projections: vec![Projection::Deref, Projection::Field(0)] };
    assert!(!crate::place_is_body_stable(&fld, &field), "`(*f).v` holds `flip`'s cell bytes");
    assert_eq!(guards::base_collection_place_unique(&fld, 4), Some(Place::local(4)));
    assert!(matches!(&pointee(&fld, 4), Ty::Adt { name, .. } if name == "uvh2::Vec"));
    assert_eq!(guard_len_name(&fld, &Operand::Copy(Place::local(4))), None);
    let field_len = guards::coll_len_var_place(&fld, &field).var_name().map(str::to_owned);
    assert!(field_len.is_some());
    assert_ne!(guard_len_name(&fld, &Operand::Copy(Place::local(3))), field_len);
}

/// The same field shape on a `Freeze` user `Vec` ([`fld_with_a_freeze_user_vec`]):
/// `_4 = &((*f).v)` traces to the FIELD place, so this reaches the field arm, and the
/// type gate alone declines to name a length there.
#[test]
fn the_is_empty_guard_names_no_length_on_a_freeze_user_vec_field() {
    let fld = fld_with_a_freeze_user_vec();
    let field = Place { local: 1, projections: vec![Projection::Deref, Projection::Field(0)] };
    assert!(crate::place_is_body_stable(&fld, &field));
    assert_eq!(guards::base_collection_place_unique(&fld, 4), Some(field.clone()));
    assert!(matches!(&pointee(&fld, 4), Ty::Adt { name, .. } if name == "uvh2::Vec"));
    assert_eq!(guard_len_name(&fld, &Operand::Copy(Place::local(4))), None);
    let field_len = guards::coll_len_var_place(&fld, &field).var_name().map(str::to_owned);
    assert!(field_len.is_some());
    assert_ne!(guard_len_name(&fld, &Operand::Copy(Place::local(3))), field_len);
}

#[test]
fn the_is_empty_guard_names_no_length_on_a_user_string_root() {
    let s2 = parse_mir(MIR_USTR_S2);
    let root = guards::coll_len_var(&s2, 1).var_name().map(str::to_owned);
    assert!(root.is_some());
    assert_eq!(guard_len_name(&s2, &Operand::Copy(Place::local(1))), None);
    assert_ne!(guard_len_name(&s2, &Operand::Copy(Place::local(2))), root);
    // std's `&String` keeps its byte-length var.
    let s2_std = parse_mir(MIR_USTR_S2_STD);
    assert_eq!(
        guard_len_name(&s2_std, &Operand::Copy(Place::local(1))),
        guards::coll_len_var(&s2_std, 1).var_name().map(str::to_owned)
    );
}

#[test]
fn the_index_bound_recovers_no_length_on_a_user_vec_root() {
    let k = parse_mir(MIR_UVH2_K);
    // The root `w: &uvh2::Vec`: the type gate alone.
    assert!(
        collection_abstract_len_with_base_opts(&k, &Operand::Copy(Place::local(1)), true).is_none()
    );
    // The index receiver `_7 = deref(w)`: whatever it recovers, it is not `w`'s.
    let got = collection_abstract_len_with_base_opts(&k, &Operand::Copy(Place::local(7)), true);
    assert!(got.as_ref().is_none_or(|(base, _)| *base != 1), "{got:?}");
    // std's `&Vec<u32>` (`Seq`) keeps it.
    let h2_std = parse_mir(MIR_UVH2_H2_STD);
    let (base, len) =
        collection_abstract_len_with_base_opts(&h2_std, &Operand::Copy(Place::local(1)), true)
            .expect("std's `&Vec` recovers its abstract length");
    assert_eq!(base, 1);
    assert_eq!(len.var_name(), guards::coll_len_var(&h2_std, 1).var_name());
}
