//! Trust (2026-10-04, DEREF-ANCHOR-1): the base-collection trace hops a `deref`
//! call only for std's own `Vec`/`String` `Deref`, on a receiver that IS a std
//! `Vec`/`String`. Pinned on REAL extracted MIR.
//!
//! `guards::base_collection_step` follows a length-PRESERVING deref: the result and
//! the receiver denote one sequence, so the result's length may be tied to the
//! receiver's base (`coll_len(base)`). Its `deref`/`deref_mut` arm admitted any
//! callee whose TRAIT path is std's (`callee_is_std_ops_method`), so a user type's
//! `impl Deref<Target = Vec<u32>>` was hopped too. rustc keys that call on the
//! `Deref::deref` trait-method DefId (core's), so neither the callee key nor the
//! trait path names the impl that runs. A user `deref` may return a different `Vec`
//! on each call; `if w.len() == 0 { return 0; } w.len() - 1` tied both `len()`
//! results to one `coll_len(w)`, the overflow row came back kernel-certified, and
//! the check was elided (the program returned `usize::MAX` where vanilla Rust
//! panics). Measured on the stage 1 of `38e6c69b1c` (`scratchpad/stage1-w11fix`)
//! under default, strict, certify and memory-safe.
//!
//! The hop now requires BOTH a callee that is std's `Vec`/`String` `Deref`/`DerefMut`
//! by the exact qualified spelling (self type and trait-and-method half split at the
//! top-level ` as `) AND a receiver whose pointee type, read from the MIR, is the
//! extractor's `Ty::Seq` (std's `Vec`), std's `Vec` by exact path, or std's `String`
//! by exact path.
//!
//! The MIR below is `-Ztrust-dump=mir:<dir>` output, captured with the same stage 1
//! (2026-10-04, `-Ztrust-verify=on -Coverflow-checks=on --crate-type lib`), of `body.rs`:
//! the item code of `tests/ui/trust/deref_len_tie_requires_std_self.rs` without its
//! header and annotation comments (hence the crate name `body`), re-serialized without
//! whitespace.

use trust_types::{VcKind, VerificationResult};

use super::*;

/// `pub fn h(w: &Wrap) -> usize { if w.len() == 0 { return 0; } w.len() - 1 }`, with
/// `impl Deref for Wrap { type Target = Vec<u32>; .. }` alternating `&self.a` /
/// `&self.b`. `_4` and `_6` are the two `<body::Wrap as core::ops::deref::Deref>::deref(_1)`
/// results; `_3` and `_5` their `Vec::len`s; `_7` is the checked `_5 - 1`.
const MIR_H: &str = r#"{"name":"h","def_path":"body::h","span":{"file":"body.rs","line_start":20,"col_start":0,"line_end":25,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":1,"ty":{"Ref":{"mutable":false,"inner":{"Adt":{"name":"body::Wrap","fields":[["a",{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}],["b",{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}],["flip",{"Adt":{"name":"core::cell::Cell","fields":[["value",{"Adt":{"name":"core::cell::UnsafeCell","fields":[["value","Bool"]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}}},"name":"w"},{"index":2,"ty":"Bool","name":null},{"index":3,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":4,"ty":{"Ref":{"mutable":false,"inner":{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}}},"name":null},{"index":5,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":6,"ty":{"Ref":{"mutable":false,"inner":{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}}},"name":null},{"index":7,"ty":{"Tuple":[{"Int":{"width":64,"signed":false}},"Bool"]},"name":null}],"blocks":[{"id":0,"stmts":[],"terminator":{"Call":{"func":"<body::Wrap as core::ops::deref::Deref>::deref","args":[{"Copy":{"local":1,"projections":[]}}],"dest":{"local":4,"projections":[]},"target":1,"span":{"file":"body.rs","line_start":21,"col_start":7,"line_end":21,"col_end":14},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":4448,"substs_digest":[3389159713730315041,15945493201324690163]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":1,"stmts":[],"terminator":{"Call":{"func":"alloc::vec::Vec::<u32>::len","args":[{"Copy":{"local":4,"projections":[]}}],"dest":{"local":3,"projections":[]},"target":2,"span":{"file":"body.rs","line_start":21,"col_start":7,"line_end":21,"col_end":14},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":8369930371133358469,"def_index":8821,"substs_digest":[937863789039580281,9258672918316184405]},"callee_key":{"sysroot_item":"VecLen","krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":8369930371133358469,"krate_name":"alloc"}}}},{"id":2,"stmts":[{"Assign":{"place":{"local":2,"projections":[]},"rvalue":{"BinaryOp":["Eq",{"Move":{"local":3,"projections":[]}},{"Constant":{"Uint":[0,64]}}]},"span":{"file":"body.rs","line_start":21,"col_start":7,"line_end":21,"col_end":19}}}],"terminator":{"SwitchInt":{"discr":{"Move":{"local":2,"projections":[]}},"targets":[[0,4]],"otherwise":3,"exhaustive_enum_unreachable":false,"span":{"file":"body.rs","line_start":21,"col_start":7,"line_end":21,"col_end":19}}}},{"id":3,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Constant":{"Uint":[0,64]}}},"span":{"file":"body.rs","line_start":22,"col_start":15,"line_end":22,"col_end":16}}}],"terminator":{"Goto":8}},{"id":4,"stmts":[],"terminator":{"Call":{"func":"<body::Wrap as core::ops::deref::Deref>::deref","args":[{"Copy":{"local":1,"projections":[]}}],"dest":{"local":6,"projections":[]},"target":5,"span":{"file":"body.rs","line_start":24,"col_start":4,"line_end":24,"col_end":11},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":4448,"substs_digest":[3389159713730315041,15945493201324690163]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":5,"stmts":[],"terminator":{"Call":{"func":"alloc::vec::Vec::<u32>::len","args":[{"Copy":{"local":6,"projections":[]}}],"dest":{"local":5,"projections":[]},"target":6,"span":{"file":"body.rs","line_start":24,"col_start":4,"line_end":24,"col_end":11},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":8369930371133358469,"def_index":8821,"substs_digest":[937863789039580281,9258672918316184405]},"callee_key":{"sysroot_item":"VecLen","krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":8369930371133358469,"krate_name":"alloc"}}}},{"id":6,"stmts":[{"Assign":{"place":{"local":7,"projections":[]},"rvalue":{"CheckedBinaryOp":["Sub",{"Copy":{"local":5,"projections":[]}},{"Constant":{"Uint":[1,64]}}]},"span":{"file":"body.rs","line_start":24,"col_start":4,"line_end":24,"col_end":15}}}],"terminator":{"Assert":{"cond":{"Move":{"local":7,"projections":[{"Field":1}]}},"expected":false,"msg":{"Overflow":"Sub"},"target":7,"span":{"file":"body.rs","line_start":24,"col_start":4,"line_end":24,"col_end":15},"unwind":"Continue"}}},{"id":7,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Move":{"local":7,"projections":[{"Field":0}]}}},"span":{"file":"body.rs","line_start":24,"col_start":4,"line_end":24,"col_end":15}}}],"terminator":{"Goto":8}},{"id":8,"stmts":[],"terminator":"Return"}],"arg_count":1,"return_ty":{"Int":{"width":64,"signed":false}}},"contracts":[],"preconditions":[],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"#;

/// `s_len`: the same shape with `Target = String`. `_2` and `_5` are the two
/// `<body::S as core::ops::deref::Deref>::deref(_1)` results (`&String`).
const MIR_S_LEN: &str = r#"{"name":"s_len","def_path":"body::s_len","span":{"file":"body.rs","line_start":43,"col_start":0,"line_end":48,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":1,"ty":{"Ref":{"mutable":false,"inner":{"Adt":{"name":"body::S","fields":[["a",{"Adt":{"name":"alloc::string::String","fields":[["vec",{"Seq":{"elem":{"Int":{"width":8,"signed":false}}}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}],["b",{"Adt":{"name":"alloc::string::String","fields":[["vec",{"Seq":{"elem":{"Int":{"width":8,"signed":false}}}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}],["flip",{"Adt":{"name":"core::cell::Cell","fields":[["value",{"Adt":{"name":"core::cell::UnsafeCell","fields":[["value","Bool"]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}}},"name":"w"},{"index":2,"ty":{"Ref":{"mutable":false,"inner":{"Adt":{"name":"alloc::string::String","fields":[["vec",{"Seq":{"elem":{"Int":{"width":8,"signed":false}}}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}}},"name":null},{"index":3,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":4,"ty":"Bool","name":null},{"index":5,"ty":{"Ref":{"mutable":false,"inner":{"Adt":{"name":"alloc::string::String","fields":[["vec",{"Seq":{"elem":{"Int":{"width":8,"signed":false}}}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}}},"name":null},{"index":6,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":7,"ty":{"Tuple":[{"Int":{"width":64,"signed":false}},"Bool"]},"name":null}],"blocks":[{"id":0,"stmts":[],"terminator":{"Call":{"func":"<body::S as core::ops::deref::Deref>::deref","args":[{"Copy":{"local":1,"projections":[]}}],"dest":{"local":2,"projections":[]},"target":3,"span":{"file":"body.rs","line_start":44,"col_start":7,"line_end":44,"col_end":7},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":4448,"substs_digest":[13957670767106039621,10950911686846084277]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":1,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Constant":{"Uint":[0,64]}}},"span":{"file":"body.rs","line_start":45,"col_start":8,"line_end":45,"col_end":8}}}],"terminator":"Return"},{"id":2,"stmts":[],"terminator":{"Call":{"func":"<body::S as core::ops::deref::Deref>::deref","args":[{"Copy":{"local":1,"projections":[]}}],"dest":{"local":5,"projections":[]},"target":5,"span":{"file":"body.rs","line_start":47,"col_start":4,"line_end":47,"col_end":4},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":4448,"substs_digest":[13957670767106039621,10950911686846084277]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":3,"stmts":[],"terminator":{"Call":{"func":"alloc::string::String::len","args":[{"Copy":{"local":2,"projections":[]}}],"dest":{"local":3,"projections":[]},"target":4,"span":{"file":"body.rs","line_start":44,"col_start":9,"line_end":44,"col_end":9},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":8369930371133358469,"def_index":6998,"substs_digest":[14241860155052752853,2268345107747320411]},"callee_key":{"sysroot_item":"StringLen","krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":8369930371133358469,"krate_name":"alloc"}}}},{"id":4,"stmts":[{"Assign":{"place":{"local":4,"projections":[]},"rvalue":{"BinaryOp":["Eq",{"Copy":{"local":3,"projections":[]}},{"Constant":{"Uint":[0,64]}}]},"span":{"file":"body.rs","line_start":44,"col_start":7,"line_end":44,"col_end":7}}}],"terminator":{"SwitchInt":{"discr":{"Copy":{"local":4,"projections":[]}},"targets":[[0,2]],"otherwise":1,"exhaustive_enum_unreachable":false,"span":{"file":"body.rs","line_start":44,"col_start":4,"line_end":44,"col_end":4}}}},{"id":5,"stmts":[],"terminator":{"Call":{"func":"alloc::string::String::len","args":[{"Copy":{"local":5,"projections":[]}}],"dest":{"local":6,"projections":[]},"target":6,"span":{"file":"body.rs","line_start":47,"col_start":6,"line_end":47,"col_end":6},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":8369930371133358469,"def_index":6998,"substs_digest":[14241860155052752853,2268345107747320411]},"callee_key":{"sysroot_item":"StringLen","krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":8369930371133358469,"krate_name":"alloc"}}}},{"id":6,"stmts":[{"Assign":{"place":{"local":7,"projections":[]},"rvalue":{"CheckedBinaryOp":["Sub",{"Copy":{"local":6,"projections":[]}},{"Constant":{"Uint":[1,64]}}]},"span":{"file":"body.rs","line_start":47,"col_start":4,"line_end":47,"col_end":4}}}],"terminator":{"Assert":{"cond":{"Move":{"local":7,"projections":[{"Field":1}]}},"expected":false,"msg":{"Overflow":"Sub"},"target":7,"span":{"file":"body.rs","line_start":47,"col_start":4,"line_end":47,"col_end":4},"unwind":"Continue"}}},{"id":7,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Copy":{"local":7,"projections":[{"Field":0}]}}},"span":{"file":"body.rs","line_start":48,"col_start":1,"line_end":48,"col_end":1}}}],"terminator":"Return"}],"arg_count":1,"return_ty":{"Int":{"width":64,"signed":false}}},"contracts":[],"preconditions":[],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"#;

/// `outer_len`: two USER hops, `<body::Outer as Deref>::deref(_1)` (`_5`, `_8`: `&Wrap`)
/// then `<body::Wrap as Deref>::deref` (`_4`, `_7`: `&Vec<u32>`).
const MIR_OUTER_LEN: &str = r#"{"name":"outer_len","def_path":"body::outer_len","span":{"file":"body.rs","line_start":62,"col_start":0,"line_end":67,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":1,"ty":{"Ref":{"mutable":false,"inner":{"Adt":{"name":"body::Outer","fields":[["inner",{"Adt":{"name":"body::Wrap","fields":[["a",{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}],["b",{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}],["flip",{"Adt":{"name":"core::cell::Cell","fields":[["value",{"Adt":{"name":"core::cell::UnsafeCell","fields":[["value","Bool"]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}}},"name":"o"},{"index":2,"ty":"Bool","name":null},{"index":3,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":4,"ty":{"Ref":{"mutable":false,"inner":{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}}},"name":null},{"index":5,"ty":{"Ref":{"mutable":false,"inner":{"Adt":{"name":"body::Wrap","fields":[["a",{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}],["b",{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}],["flip",{"Adt":{"name":"core::cell::Cell","fields":[["value",{"Adt":{"name":"core::cell::UnsafeCell","fields":[["value","Bool"]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}}},"name":null},{"index":6,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":7,"ty":{"Ref":{"mutable":false,"inner":{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}}},"name":null},{"index":8,"ty":{"Ref":{"mutable":false,"inner":{"Adt":{"name":"body::Wrap","fields":[["a",{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}],["b",{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}],["flip",{"Adt":{"name":"core::cell::Cell","fields":[["value",{"Adt":{"name":"core::cell::UnsafeCell","fields":[["value","Bool"]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}}},"name":null},{"index":9,"ty":{"Tuple":[{"Int":{"width":64,"signed":false}},"Bool"]},"name":null}],"blocks":[{"id":0,"stmts":[],"terminator":{"Call":{"func":"<body::Outer as core::ops::deref::Deref>::deref","args":[{"Copy":{"local":1,"projections":[]}}],"dest":{"local":5,"projections":[]},"target":1,"span":{"file":"body.rs","line_start":63,"col_start":7,"line_end":63,"col_end":14},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":4448,"substs_digest":[9906638170851184919,12806563315078525104]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":1,"stmts":[],"terminator":{"Call":{"func":"<body::Wrap as core::ops::deref::Deref>::deref","args":[{"Copy":{"local":5,"projections":[]}}],"dest":{"local":4,"projections":[]},"target":2,"span":{"file":"body.rs","line_start":63,"col_start":7,"line_end":63,"col_end":14},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":4448,"substs_digest":[3389159713730315041,15945493201324690163]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":2,"stmts":[],"terminator":{"Call":{"func":"alloc::vec::Vec::<u32>::len","args":[{"Copy":{"local":4,"projections":[]}}],"dest":{"local":3,"projections":[]},"target":3,"span":{"file":"body.rs","line_start":63,"col_start":7,"line_end":63,"col_end":14},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":8369930371133358469,"def_index":8821,"substs_digest":[937863789039580281,9258672918316184405]},"callee_key":{"sysroot_item":"VecLen","krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":8369930371133358469,"krate_name":"alloc"}}}},{"id":3,"stmts":[{"Assign":{"place":{"local":2,"projections":[]},"rvalue":{"BinaryOp":["Eq",{"Move":{"local":3,"projections":[]}},{"Constant":{"Uint":[0,64]}}]},"span":{"file":"body.rs","line_start":63,"col_start":7,"line_end":63,"col_end":19}}}],"terminator":{"SwitchInt":{"discr":{"Move":{"local":2,"projections":[]}},"targets":[[0,5]],"otherwise":4,"exhaustive_enum_unreachable":false,"span":{"file":"body.rs","line_start":63,"col_start":7,"line_end":63,"col_end":19}}}},{"id":4,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Constant":{"Uint":[0,64]}}},"span":{"file":"body.rs","line_start":64,"col_start":15,"line_end":64,"col_end":16}}}],"terminator":{"Goto":10}},{"id":5,"stmts":[],"terminator":{"Call":{"func":"<body::Outer as core::ops::deref::Deref>::deref","args":[{"Copy":{"local":1,"projections":[]}}],"dest":{"local":8,"projections":[]},"target":6,"span":{"file":"body.rs","line_start":66,"col_start":4,"line_end":66,"col_end":11},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":4448,"substs_digest":[9906638170851184919,12806563315078525104]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":6,"stmts":[],"terminator":{"Call":{"func":"<body::Wrap as core::ops::deref::Deref>::deref","args":[{"Copy":{"local":8,"projections":[]}}],"dest":{"local":7,"projections":[]},"target":7,"span":{"file":"body.rs","line_start":66,"col_start":4,"line_end":66,"col_end":11},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":4448,"substs_digest":[3389159713730315041,15945493201324690163]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":7,"stmts":[],"terminator":{"Call":{"func":"alloc::vec::Vec::<u32>::len","args":[{"Copy":{"local":7,"projections":[]}}],"dest":{"local":6,"projections":[]},"target":8,"span":{"file":"body.rs","line_start":66,"col_start":4,"line_end":66,"col_end":11},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":8369930371133358469,"def_index":8821,"substs_digest":[937863789039580281,9258672918316184405]},"callee_key":{"sysroot_item":"VecLen","krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":8369930371133358469,"krate_name":"alloc"}}}},{"id":8,"stmts":[{"Assign":{"place":{"local":9,"projections":[]},"rvalue":{"CheckedBinaryOp":["Sub",{"Copy":{"local":6,"projections":[]}},{"Constant":{"Uint":[1,64]}}]},"span":{"file":"body.rs","line_start":66,"col_start":4,"line_end":66,"col_end":15}}}],"terminator":{"Assert":{"cond":{"Move":{"local":9,"projections":[{"Field":1}]}},"expected":false,"msg":{"Overflow":"Sub"},"target":9,"span":{"file":"body.rs","line_start":66,"col_start":4,"line_end":66,"col_end":15},"unwind":"Continue"}}},{"id":9,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Move":{"local":9,"projections":[{"Field":0}]}}},"span":{"file":"body.rs","line_start":66,"col_start":4,"line_end":66,"col_end":15}}}],"terminator":{"Goto":10}},{"id":10,"stmts":[],"terminator":"Return"}],"arg_count":1,"return_ty":{"Int":{"width":64,"signed":false}}},"contracts":[],"preconditions":[],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"#;

/// Control `std_vec_view(v: &Vec<u32>)`: `if v.len() == 0 { return 0; } let t: &[u32] = v;
/// t.len() - 1`. `_4 = <alloc::vec::Vec<u32> as core::ops::deref::Deref>::deref(_1)`, `_1:
/// &Seq<u32>`; the overflow row needs the hop `_4 -> _1`.
const MIR_STD_VEC_VIEW: &str = r#"{"name":"std_vec_view","def_path":"body::std_vec_view","span":{"file":"body.rs","line_start":74,"col_start":0,"line_end":80,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":1,"ty":{"Ref":{"mutable":false,"inner":{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}}},"name":"v"},{"index":2,"ty":"Bool","name":null},{"index":3,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":4,"ty":{"Ref":{"mutable":false,"inner":{"Slice":{"elem":{"Int":{"width":32,"signed":false}}}}}},"name":"t"},{"index":5,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":6,"ty":{"Tuple":[{"Int":{"width":64,"signed":false}},"Bool"]},"name":null}],"blocks":[{"id":0,"stmts":[],"terminator":{"Call":{"func":"alloc::vec::Vec::<u32>::len","args":[{"Copy":{"local":1,"projections":[]}}],"dest":{"local":3,"projections":[]},"target":1,"span":{"file":"body.rs","line_start":75,"col_start":7,"line_end":75,"col_end":14},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":8369930371133358469,"def_index":8821,"substs_digest":[937863789039580281,9258672918316184405]},"callee_key":{"sysroot_item":"VecLen","krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":8369930371133358469,"krate_name":"alloc"}}}},{"id":1,"stmts":[{"Assign":{"place":{"local":2,"projections":[]},"rvalue":{"BinaryOp":["Eq",{"Move":{"local":3,"projections":[]}},{"Constant":{"Uint":[0,64]}}]},"span":{"file":"body.rs","line_start":75,"col_start":7,"line_end":75,"col_end":19}}}],"terminator":{"SwitchInt":{"discr":{"Move":{"local":2,"projections":[]}},"targets":[[0,3]],"otherwise":2,"exhaustive_enum_unreachable":false,"span":{"file":"body.rs","line_start":75,"col_start":7,"line_end":75,"col_end":19}}}},{"id":2,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Constant":{"Uint":[0,64]}}},"span":{"file":"body.rs","line_start":76,"col_start":15,"line_end":76,"col_end":16}}}],"terminator":{"Goto":6}},{"id":3,"stmts":[],"terminator":{"Call":{"func":"<alloc::vec::Vec<u32> as core::ops::deref::Deref>::deref","args":[{"Copy":{"local":1,"projections":[]}}],"dest":{"local":4,"projections":[]},"target":4,"span":{"file":"body.rs","line_start":78,"col_start":20,"line_end":78,"col_end":21},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":4448,"substs_digest":[7380399338322949592,16186388883692782947]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":4,"stmts":[{"Assign":{"place":{"local":5,"projections":[]},"rvalue":{"UnaryOp":["PtrMetadata",{"Copy":{"local":4,"projections":[]}}]},"span":{"file":"body.rs","line_start":79,"col_start":4,"line_end":79,"col_end":11}}},{"Assign":{"place":{"local":6,"projections":[]},"rvalue":{"CheckedBinaryOp":["Sub",{"Copy":{"local":5,"projections":[]}},{"Constant":{"Uint":[1,64]}}]},"span":{"file":"body.rs","line_start":79,"col_start":4,"line_end":79,"col_end":15}}}],"terminator":{"Assert":{"cond":{"Move":{"local":6,"projections":[{"Field":1}]}},"expected":false,"msg":{"Overflow":"Sub"},"target":5,"span":{"file":"body.rs","line_start":79,"col_start":4,"line_end":79,"col_end":15},"unwind":"Continue"}}},{"id":5,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Move":{"local":6,"projections":[{"Field":0}]}}},"span":{"file":"body.rs","line_start":79,"col_start":4,"line_end":79,"col_end":15}}}],"terminator":{"Goto":6}},{"id":6,"stmts":[],"terminator":"Return"}],"arg_count":1,"return_ty":{"Int":{"width":64,"signed":false}}},"contracts":[],"preconditions":[],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"#;

/// Control `std_string_view(s: &String)`: the same through
/// `<alloc::string::String as core::ops::deref::Deref>::deref(_1)` (`_4`), `_1: &String`.
const MIR_STD_STRING_VIEW: &str = r#"{"name":"std_string_view","def_path":"body::std_string_view","span":{"file":"body.rs","line_start":82,"col_start":0,"line_end":88,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":1,"ty":{"Ref":{"mutable":false,"inner":{"Adt":{"name":"alloc::string::String","fields":[["vec",{"Seq":{"elem":{"Int":{"width":8,"signed":false}}}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}}},"name":"s"},{"index":2,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":3,"ty":"Bool","name":null},{"index":4,"ty":{"Ref":{"mutable":false,"inner":{"Slice":{"elem":{"Int":{"width":8,"signed":false}}}}}},"name":null},{"index":5,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":6,"ty":{"Tuple":[{"Int":{"width":64,"signed":false}},"Bool"]},"name":null}],"blocks":[{"id":0,"stmts":[],"terminator":{"Call":{"func":"alloc::string::String::len","args":[{"Copy":{"local":1,"projections":[]}}],"dest":{"local":2,"projections":[]},"target":3,"span":{"file":"body.rs","line_start":83,"col_start":9,"line_end":83,"col_end":9},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":8369930371133358469,"def_index":6998,"substs_digest":[14241860155052752853,2268345107747320411]},"callee_key":{"sysroot_item":"StringLen","krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":8369930371133358469,"krate_name":"alloc"}}}},{"id":1,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Constant":{"Uint":[0,64]}}},"span":{"file":"body.rs","line_start":84,"col_start":8,"line_end":84,"col_end":8}}}],"terminator":"Return"},{"id":2,"stmts":[],"terminator":{"Call":{"func":"<alloc::string::String as core::ops::deref::Deref>::deref","args":[{"Copy":{"local":1,"projections":[]}}],"dest":{"local":4,"projections":[]},"target":4,"span":{"file":"body.rs","line_start":86,"col_start":18,"line_end":86,"col_end":18},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":4448,"substs_digest":[14885610625367427710,7401071494707805791]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":3,"stmts":[{"Assign":{"place":{"local":3,"projections":[]},"rvalue":{"BinaryOp":["Eq",{"Copy":{"local":2,"projections":[]}},{"Constant":{"Uint":[0,64]}}]},"span":{"file":"body.rs","line_start":83,"col_start":7,"line_end":83,"col_end":7}}}],"terminator":{"SwitchInt":{"discr":{"Copy":{"local":3,"projections":[]}},"targets":[[0,2]],"otherwise":1,"exhaustive_enum_unreachable":false,"span":{"file":"body.rs","line_start":83,"col_start":4,"line_end":83,"col_end":4}}}},{"id":4,"stmts":[],"terminator":{"Call":{"func":"core::str::<impl str>::len","args":[{"Copy":{"local":4,"projections":[]}}],"dest":{"local":5,"projections":[]},"target":5,"span":{"file":"body.rs","line_start":87,"col_start":6,"line_end":87,"col_end":6},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":16525,"substs_digest":[14241860155052752853,2268345107747320411]},"callee_key":{"sysroot_item":"StrLen","krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":5,"stmts":[{"Assign":{"place":{"local":6,"projections":[]},"rvalue":{"CheckedBinaryOp":["Sub",{"Copy":{"local":5,"projections":[]}},{"Constant":{"Uint":[1,64]}}]},"span":{"file":"body.rs","line_start":87,"col_start":4,"line_end":87,"col_end":4}}}],"terminator":{"Assert":{"cond":{"Move":{"local":6,"projections":[{"Field":1}]}},"expected":false,"msg":{"Overflow":"Sub"},"target":6,"span":{"file":"body.rs","line_start":87,"col_start":4,"line_end":87,"col_end":4},"unwind":"Continue"}}},{"id":6,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Copy":{"local":6,"projections":[{"Field":0}]}}},"span":{"file":"body.rs","line_start":88,"col_start":1,"line_end":88,"col_end":1}}}],"terminator":"Return"}],"arg_count":1,"return_ty":{"Int":{"width":64,"signed":false}}},"contracts":[],"preconditions":[],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"#;

fn parse(mir: &str) -> VerifiableFunction {
    serde_json::from_str(mir).expect("the captured MIR fixture must deserialize")
}

/// `(dest local, receiver local)` of every call to exactly `callee`.
fn calls_to(func: &VerifiableFunction, callee: &str) -> Vec<(usize, usize)> {
    func.body
        .blocks
        .iter()
        .filter_map(|b| match &b.terminator {
            Terminator::Call { func: f, args, dest, .. } if f == callee => match args.first() {
                Some(Operand::Copy(p) | Operand::Move(p)) => Some((dest.local, p.local)),
                _ => None,
            },
            _ => None,
        })
        .collect()
}

/// Respell every call to `from` as `to`; the MIR (receiver types included) is untouched.
fn respell(func: &mut VerifiableFunction, from: &str, to: &str) {
    let mut n = 0;
    for b in &mut func.body.blocks {
        if let Terminator::Call { func: f, .. } = &mut b.terminator
            && f == from
        {
            *f = to.to_string();
            n += 1;
        }
    }
    assert!(n > 0, "the fixture has no call to {from}");
}

/// Every `- 1` overflow row's verdict from the real in-process ay, on a big stack
/// (VC generation and the solver search overflow libtest's default stack).
fn sub_overflow_verdicts(func: VerifiableFunction) -> Vec<VerificationResult> {
    std::thread::Builder::new()
        .stack_size(32 * 1024 * 1024)
        .spawn(move || {
            let vcs: Vec<_> = crate::generate_vcs(&func)
                .into_iter()
                .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Sub, .. }))
                .collect();
            let router = crate::test_router::deterministic_test_router();
            router.verify_all(&vcs).into_iter().map(|(_, r)| r).collect::<Vec<_>>()
        })
        .expect("spawn solver thread")
        .join()
        .expect("solver thread must not panic")
}

const WRAP_DEREF: &str = "<body::Wrap as core::ops::deref::Deref>::deref";
const S_DEREF: &str = "<body::S as core::ops::deref::Deref>::deref";
const OUTER_DEREF: &str = "<body::Outer as core::ops::deref::Deref>::deref";
const STD_VEC_DEREF: &str = "<alloc::vec::Vec<u32> as core::ops::deref::Deref>::deref";
const STD_STRING_DEREF: &str = "<alloc::string::String as core::ops::deref::Deref>::deref";

/// THE LIE: both `w.len()` receivers traced through the user `deref` to `w` (`_1`),
/// so both lengths were `coll_len(w)`. Each `deref` result is now its own base.
#[test]
fn a_user_deref_to_a_std_vec_is_not_a_length_preserving_hop() {
    let h = parse(MIR_H);
    assert_eq!(calls_to(&h, WRAP_DEREF), [(4, 1), (6, 1)]);
    for dest in [4, 6] {
        assert_eq!(
            base_collection_local_unique(&h, dest),
            Some(dest),
            "a user `Deref` may return a different `Vec` per call; `_{dest}` must not trace to `w`"
        );
        assert_eq!(base_collection_place_unique(&h, dest), Some(trust_types::Place::local(dest)));
    }
}

#[test]
fn a_user_deref_to_a_std_string_is_not_a_length_preserving_hop() {
    let s_len = parse(MIR_S_LEN);
    assert_eq!(calls_to(&s_len, S_DEREF), [(2, 1), (5, 1)]);
    for dest in [2, 5] {
        assert_eq!(base_collection_local_unique(&s_len, dest), Some(dest));
    }
}

#[test]
fn neither_of_two_user_deref_hops_is_followed() {
    let outer_len = parse(MIR_OUTER_LEN);
    assert_eq!(calls_to(&outer_len, OUTER_DEREF), [(5, 1), (8, 1)]);
    assert_eq!(calls_to(&outer_len, WRAP_DEREF), [(4, 5), (7, 8)]);
    for dest in [4, 5, 7, 8] {
        assert_eq!(base_collection_local_unique(&outer_len, dest), Some(dest));
    }
}

/// CONTROL: std's own `Vec` `Deref` on a `&Vec<u32>` (`Ty::Seq`) receiver is still
/// a length-preserving hop; the `t.len() - 1` row rests on it.
#[test]
fn std_vec_own_deref_still_hops() {
    let f = parse(MIR_STD_VEC_VIEW);
    assert_eq!(calls_to(&f, STD_VEC_DEREF), [(4, 1)]);
    assert_eq!(base_collection_local_unique(&f, 4), Some(1));
}

/// CONTROL: std's own `String` `Deref` on a `&String` receiver.
#[test]
fn std_string_own_deref_still_hops() {
    let f = parse(MIR_STD_STRING_VIEW);
    assert_eq!(calls_to(&f, STD_STRING_DEREF), [(4, 1)]);
    assert_eq!(base_collection_local_unique(&f, 4), Some(1));
}

/// The RECEIVER conjunct is load-bearing on its own: `h`'s MIR with its user calls
/// respelled as std `Vec`'s own `Deref`. The receiver is still `&body::Wrap`, so the
/// hop is refused although the spelling passes.
#[test]
fn std_vec_deref_spelling_on_a_user_receiver_is_not_followed() {
    let mut h = parse(MIR_H);
    respell(&mut h, WRAP_DEREF, STD_VEC_DEREF);
    for dest in [4, 6] {
        assert_eq!(base_collection_local_unique(&h, dest), Some(dest));
    }
}

/// The SPELLING conjunct is load-bearing on its own, and it splits at the TOP-LEVEL
/// ` as `: a user trait method named `deref` on std's `Vec`, whose element type is a
/// fn item spelling std's `Deref`. The callee is REAL extracted MIR (the wave-12
/// scout's `fnitem.rs`, stage 1 of `38e6c69b1c`); it contains
/// ` as core::ops::deref::Deref>::deref`, which the old crate-root test
/// (`callee_is_std_ops_method`'s `contains(" as core::ops::")`) admitted. The
/// receiver is a std `Vec` (`_1: &Seq<u32>`), so only the spelling refuses it.
#[test]
fn a_user_trait_deref_on_a_std_vec_is_not_followed() {
    let mut f = parse(MIR_STD_VEC_VIEW);
    respell(
        &mut f,
        STD_VEC_DEREF,
        "<alloc::vec::Vec<for<'_> fn(&'_ fnitem::W) -> &'_ <fnitem::W as \
         core::ops::deref::Deref>::Target {<fnitem::W as core::ops::deref::Deref>::deref}> as \
         fnitem::Tr>::deref",
    );
    assert_eq!(base_collection_local_unique(&f, 4), Some(4));
}

/// End to end through vcgen and the real in-process ay: the three user-`Deref` rows
/// are no longer proved (before the fix each was UNSAT through the false tie), and
/// std's own `Vec`/`String` `Deref` rows still are.
#[test]
fn user_deref_overflow_rows_are_not_proved_and_std_deref_rows_are() {
    for (name, mir) in [("h", MIR_H), ("s_len", MIR_S_LEN), ("outer_len", MIR_OUTER_LEN)] {
        let verdicts = sub_overflow_verdicts(parse(mir));
        assert!(!verdicts.is_empty(), "{name}: the `- 1` overflow row must be generated");
        for verdict in &verdicts {
            assert!(
                !matches!(verdict, VerificationResult::Proved { .. }),
                "{name}: `w.len() - 1` under a guard on ANOTHER user-`deref` result: {verdict:?}"
            );
        }
    }
    for (name, mir) in
        [("std_vec_view", MIR_STD_VEC_VIEW), ("std_string_view", MIR_STD_STRING_VIEW)]
    {
        let verdicts = sub_overflow_verdicts(parse(mir));
        assert!(
            !verdicts.is_empty()
                && verdicts.iter().all(|v| matches!(v, VerificationResult::Proved { .. })),
            "{name}: std's own deref keeps the length tie: {verdicts:?}"
        );
    }
}

/// The spelling half, row by row. Accepted: exactly std's own `Vec`/`String`
/// `Deref`/`DerefMut`, in the extractor's spelling (measured) and the two re-export
/// spellings. Refused: every other self type, every other trait, the unqualified
/// trait-method path (it names no self type), a method suffix, the duplicate-crate
/// `__trust_args` tag, a stamped impersonator, and the fn-item forgery.
#[test]
fn std_container_deref_spelling_table() {
    use StdDerefSelf::{String as Str, Vec as V};
    let accepted = [
        (STD_VEC_DEREF, V),
        ("<alloc::vec::Vec<u8> as core::ops::deref::DerefMut>::deref_mut", V),
        ("<std::vec::Vec<u8> as std::ops::Deref>::deref", V),
        ("<alloc::vec::Vec<rational::Rat> as core::ops::Deref>::deref", V),
        ("<alloc::vec::Vec<u32, alloc::alloc::Global> as core::ops::deref::Deref>::deref", V),
        (STD_STRING_DEREF, Str),
        ("<alloc::string::String as core::ops::deref::DerefMut>::deref_mut", Str),
        ("<std::string::String as std::ops::Deref>::deref", Str),
    ];
    for (callee, want) in accepted {
        assert_eq!(std_container_deref_self(callee), Some(want), "{callee}");
    }
    let refused = [
        WRAP_DEREF,
        S_DEREF,
        OUTER_DEREF,
        "<mycrate::Vec as core::ops::deref::Deref>::deref",
        "<mycrate::vec::Vec<u8> as core::ops::deref::Deref>::deref",
        "<mycrate::String as core::ops::deref::Deref>::deref",
        "<alloc::sync::Arc<alloc::vec::Vec<u32>> as core::ops::deref::Deref>::deref",
        "<alloc::rc::Rc<alloc::vec::Vec<u32>> as core::ops::deref::Deref>::deref",
        "<alloc::boxed::Box<alloc::vec::Vec<u32>> as core::ops::deref::Deref>::deref",
        "<alloc::borrow::Cow<'_, [u32]> as core::ops::deref::Deref>::deref",
        "<T as core::ops::deref::Deref>::deref",
        "<alloc::collections::vec_deque::VecDeque<u32> as core::ops::deref::Deref>::deref",
        "core::ops::deref::Deref::deref",
        "<alloc::vec::Vec<u32> as mycrate::Tr>::deref",
        "<alloc::vec::Vec<u32> as mycrate::core::ops::deref::Deref>::deref",
        "<alloc::vec::Vec<u32> as core::ops::deref::Deref>::deref_mut",
        "<alloc::vec::Vec<u32> as core::ops::deref::Deref>::deref::<__trust_args@00000000000000010000000000000023>",
        "__trust_crate@1973d11b2baa21fa::<alloc::vec::Vec<u32> as core::ops::deref::Deref>::deref",
        "<__trust_crate@1973d11b2baa21fa::alloc::vec::Vec<u32> as core::ops::deref::Deref>::deref",
        "<alloc::vec::Vec<for<'_> fn(&'_ fnitem::W) -> &'_ <fnitem::W as \
         core::ops::deref::Deref>::Target {<fnitem::W as core::ops::deref::Deref>::deref}> as \
         fnitem::Tr>::deref",
        "alloc::vec::Vec::<u32>::as_slice",
    ];
    for callee in refused {
        assert_eq!(std_container_deref_self(callee), None, "{callee}");
    }
}

/// The receiver half, on the real locals: `&Seq<u32>` and `&alloc::string::String`
/// are std containers of the matching kind; `&body::Wrap`, `&body::S`, `&body::Outer`
/// are not, and a `Vec` callee on a `String` receiver (or the reverse) is refused.
#[test]
fn deref_receiver_must_be_the_named_std_container() {
    let place = trust_types::Place::local;
    let vec_view = parse(MIR_STD_VEC_VIEW);
    assert!(deref_receiver_is_std_container(&vec_view, &place(1), StdDerefSelf::Vec));
    assert!(!deref_receiver_is_std_container(&vec_view, &place(1), StdDerefSelf::String));
    let string_view = parse(MIR_STD_STRING_VIEW);
    assert!(deref_receiver_is_std_container(&string_view, &place(1), StdDerefSelf::String));
    assert!(!deref_receiver_is_std_container(&string_view, &place(1), StdDerefSelf::Vec));
    let h = parse(MIR_H);
    assert!(matches!(h.body.locals[1].ty, Ty::Ref { .. }));
    assert!(!deref_receiver_is_std_container(&h, &place(1), StdDerefSelf::Vec));
    let s_len = parse(MIR_S_LEN);
    assert!(!deref_receiver_is_std_container(&s_len, &place(1), StdDerefSelf::String));
    let outer_len = parse(MIR_OUTER_LEN);
    assert!(!deref_receiver_is_std_container(&outer_len, &place(1), StdDerefSelf::Vec));
    // A `Ty::Adt` named std's `Vec` by exact path is std's `Vec` too; one whose LAST
    // segment merely reads `Vec` is not. (`h`'s `_1: &body::Wrap`, renamed.)
    let rename = |to: &str| {
        let mut f = parse(MIR_H);
        let Ty::Ref { inner, .. } = &mut f.body.locals[1].ty else { panic!("`w: &Wrap`") };
        let Ty::Adt { name, .. } = inner.as_mut() else { panic!("`Wrap` is an ADT") };
        *name = to.to_string();
        f
    };
    for (name, container, want) in [
        ("alloc::vec::Vec<u32>", StdDerefSelf::Vec, true),
        ("std::vec::Vec<u32>", StdDerefSelf::Vec, true),
        ("uvh::Vec", StdDerefSelf::Vec, false),
        ("uvh::vec::Vec<u32>", StdDerefSelf::Vec, false),
        ("alloc::string::String", StdDerefSelf::String, true),
        ("std::string::String", StdDerefSelf::String, true),
        ("mycrate::String", StdDerefSelf::String, false),
        ("alloc::string::String", StdDerefSelf::Vec, false),
        ("alloc::vec::Vec<u32>", StdDerefSelf::String, false),
    ] {
        assert_eq!(
            deref_receiver_is_std_container(&rename(name), &place(1), container),
            want,
            "receiver `&{name}` for {container:?}'s deref"
        );
    }
    // Not a reference at all: the pointee test never runs.
    let mut by_value = parse(MIR_STD_VEC_VIEW);
    let Ty::Ref { inner, .. } = by_value.body.locals[1].ty.clone() else {
        panic!("`v: &Vec<u32>`")
    };
    by_value.body.locals[1].ty = *inner;
    assert!(!deref_receiver_is_std_container(&by_value, &place(1), StdDerefSelf::Vec));
}
