//! Trust (2026-10-04, IDX-TIE-1 second consumer): the immutable nested-index
//! LENGTH tie reads std's `Index<usize>` result on a std container, not any
//! method named `index` on any shared reference. Pinned on REAL extracted MIR.

use trust_types::{Formula, Terminator, Ty, VerifiableFunction};

// ── THE STD INDEX ON A STD CONTAINER (Trust, 2026-10-04, IDX-TIE-1) ──────────
//
// `build_immutable_index_len_tie_facts` ties `coll_len(dest_a) == coll_len(dest_b)`
// for two `index` calls at one stable index on one shared-ref root. Its soundness
// is "the same element of an unchanged container is the same inner collection" —
// a theorem about std's `Index<usize>` on a slice, array or `Vec`, and about
// nothing else. It recognized the callee by `slice_conversion::is_slice_index_call`
// (`method_tail` is `index`/`index_mut`) and accepted ANY shared-ref root:
//
//  * two user trait methods named `index` (`<Two as LoV>::index`, returning a
//    long `Vec`, and `<Two as HiV>::index`, returning an empty one) were tied, so
//    `if j < LoV::index(t, i).len() { HiV::index(t, i)[j] }` read `slice proved`
//    (default and strict exit 0; the binary panics `index out of bounds: the len
//    is 0 but the index is 1`) — `tests/ui/trust/index_len_tie_requires_std_index.rs`;
//  * std's own index reached through a USER `Deref` (`w[i]` on a `W: Deref<Target
//    = Vec<Vec<u32>>>` whose `deref` alternates two fields) traced both reads to
//    the root `w: &W` and tied two different inner `Vec`s.
//
// It now requires `unwrap_panic::is_std_scalar_index_call` (the value tie's own
// predicate) AND a root whose pointee is a slice, an array, the extractor's `Seq`
// (std's `Vec`), or std's `Vec` by exact path.

/// REAL extracted MIR (`-Ztrust-dump=mir:<dir>`, stage 1 of integ/wave11
/// `936573497e`, 2026-10-04) of `lt_index.rs`:
///
/// ```text
/// pub trait LoV { fn index(&self, i: usize) -> &Vec<u32>; }
/// pub trait HiV { fn index(&self, i: usize) -> &Vec<u32>; }
/// pub struct Two { pub long: Vec<u32>, pub empty: Vec<u32> }
/// impl LoV for Two { fn index(&self, _i: usize) -> &Vec<u32> { &self.long } }
/// impl HiV for Two { fn index(&self, _i: usize) -> &Vec<u32> { &self.empty } }
/// pub fn g(t: &Two, i: usize, j: usize) -> u32 {
///     if j < LoV::index(t, i).len() { HiV::index(t, i)[j] } else { 0 }
/// }
/// ```
///
/// The two user calls are `<lt_index::Two as lt_index::LoV>::index` (dest 6) and
/// `<lt_index::Two as lt_index::HiV>::index` (dest 8), both on the root `t: &Two`.
const MIR_LT_INDEX_G: &str = r#"{"name":"g","def_path":"lt_index::g","span":{"file":"lt_index.rs","line_start":6,"col_start":0,"line_end":8,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Int":{"width":32,"signed":false}},"name":null},{"index":1,"ty":{"Ref":{"mutable":false,"inner":{"Adt":{"name":"lt_index::Two","fields":[["long",{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}],["empty",{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}}},"name":"t"},{"index":2,"ty":{"Int":{"width":64,"signed":false}},"name":"i"},{"index":3,"ty":{"Int":{"width":64,"signed":false}},"name":"j"},{"index":4,"ty":"Bool","name":null},{"index":5,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":6,"ty":{"Ref":{"mutable":false,"inner":{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}}},"name":null},{"index":7,"ty":{"Ref":{"mutable":false,"inner":{"Int":{"width":32,"signed":false}}}},"name":null},{"index":8,"ty":{"Ref":{"mutable":false,"inner":{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}}},"name":null}],"blocks":[{"id":0,"stmts":[],"terminator":{"Call":{"func":"<lt_index::Two as lt_index::LoV>::index","args":[{"Copy":{"local":1,"projections":[]}},{"Copy":{"local":2,"projections":[]}}],"dest":{"local":6,"projections":[]},"target":1,"span":{"file":"lt_index.rs","line_start":7,"col_start":11,"line_end":7,"col_end":27},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":10344856220393918095,"def_index":4,"substs_digest":[14889886795331915861,15669301498226851191]},"callee_key":{"krate_is_real_sysroot":false,"krate_name_is_ambiguous":false,"stable_crate_id":10344856220393918095,"krate_name":"lt_index"}}}},{"id":1,"stmts":[],"terminator":{"Call":{"func":"alloc::vec::Vec::<u32>::len","args":[{"Copy":{"local":6,"projections":[]}}],"dest":{"local":5,"projections":[]},"target":2,"span":{"file":"lt_index.rs","line_start":7,"col_start":11,"line_end":7,"col_end":33},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":8369930371133358469,"def_index":8821,"substs_digest":[937863789039580281,9258672918316184405]},"callee_key":{"sysroot_item":"VecLen","krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":8369930371133358469,"krate_name":"alloc"}}}},{"id":2,"stmts":[{"Assign":{"place":{"local":4,"projections":[]},"rvalue":{"BinaryOp":["Lt",{"Copy":{"local":3,"projections":[]}},{"Move":{"local":5,"projections":[]}}]},"span":{"file":"lt_index.rs","line_start":7,"col_start":7,"line_end":7,"col_end":33}}}],"terminator":{"SwitchInt":{"discr":{"Move":{"local":4,"projections":[]}},"targets":[[0,6]],"otherwise":3,"exhaustive_enum_unreachable":false,"span":{"file":"lt_index.rs","line_start":7,"col_start":7,"line_end":7,"col_end":33}}}},{"id":3,"stmts":[],"terminator":{"Call":{"func":"<lt_index::Two as lt_index::HiV>::index","args":[{"Copy":{"local":1,"projections":[]}},{"Copy":{"local":2,"projections":[]}}],"dest":{"local":8,"projections":[]},"target":4,"span":{"file":"lt_index.rs","line_start":7,"col_start":36,"line_end":7,"col_end":52},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":10344856220393918095,"def_index":6,"substs_digest":[14889886795331915861,15669301498226851191]},"callee_key":{"krate_is_real_sysroot":false,"krate_name_is_ambiguous":false,"stable_crate_id":10344856220393918095,"krate_name":"lt_index"}}}},{"id":4,"stmts":[],"terminator":{"Call":{"func":"<alloc::vec::Vec<u32> as core::ops::index::Index<usize>>::index","args":[{"Copy":{"local":8,"projections":[]}},{"Copy":{"local":3,"projections":[]}}],"dest":{"local":7,"projections":[]},"target":5,"span":{"file":"lt_index.rs","line_start":7,"col_start":52,"line_end":7,"col_end":55},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":39089,"substs_digest":[17091007639459144612,2033056495210424997]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":5,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Copy":{"local":7,"projections":["Deref"]}}},"span":{"file":"lt_index.rs","line_start":7,"col_start":36,"line_end":7,"col_end":55}}}],"terminator":{"Goto":7}},{"id":6,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Constant":{"Uint":[0,32]}}},"span":{"file":"lt_index.rs","line_start":7,"col_start":65,"line_end":7,"col_end":66}}}],"terminator":{"Goto":7}},{"id":7,"stmts":[],"terminator":"Return"}],"arg_count":3,"return_ty":{"Int":{"width":32,"signed":false}}},"contracts":[],"preconditions":[{"And":[{"Ge":[{"Var":["i","Int"]},{"Int":0}]},{"Le":[{"Var":["i","Int"]},{"Int":18446744073709551615}]}]},{"And":[{"Ge":[{"Var":["j","Int"]},{"Int":0}]},{"Le":[{"Var":["j","Int"]},{"Int":18446744073709551615}]}]}],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"#;

/// REAL extracted MIR (same compiler) of the control `nest_ctl.rs`:
///
/// ```text
/// pub fn nest(v: &Vec<Vec<u32>>, i: usize, j: usize) -> u32 {
///     if i < v.len() && j < v[i].len() { v[i][j] } else { 0 }
/// }
/// ```
///
/// Both `v[i]` are `<alloc::vec::Vec<alloc::vec::Vec<u32>> as
/// core::ops::index::Index<usize>>::index` (dests 8 and 10) on the root `v`, typed
/// `&Seq<Seq<u32>>`.
const MIR_NEST_SHARED: &str = r#"{"name":"nest","def_path":"nest_ctl::nest","span":{"file":"nest_ctl.rs","line_start":1,"col_start":0,"line_end":3,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Int":{"width":32,"signed":false}},"name":null},{"index":1,"ty":{"Ref":{"mutable":false,"inner":{"Seq":{"elem":{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}}}}},"name":"v"},{"index":2,"ty":{"Int":{"width":64,"signed":false}},"name":"i"},{"index":3,"ty":{"Int":{"width":64,"signed":false}},"name":"j"},{"index":4,"ty":"Bool","name":null},{"index":5,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":6,"ty":"Bool","name":null},{"index":7,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":8,"ty":{"Ref":{"mutable":false,"inner":{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}}},"name":null},{"index":9,"ty":{"Ref":{"mutable":false,"inner":{"Int":{"width":32,"signed":false}}}},"name":null},{"index":10,"ty":{"Ref":{"mutable":false,"inner":{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}}},"name":null}],"blocks":[{"id":0,"stmts":[],"terminator":{"Call":{"func":"alloc::vec::Vec::<alloc::vec::Vec<u32>>::len","args":[{"Copy":{"local":1,"projections":[]}}],"dest":{"local":5,"projections":[]},"target":1,"span":{"file":"nest_ctl.rs","line_start":2,"col_start":11,"line_end":2,"col_end":18},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":8369930371133358469,"def_index":8821,"substs_digest":[6417032960996364332,5012686771394125218]},"callee_key":{"sysroot_item":"VecLen","krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":8369930371133358469,"krate_name":"alloc"}}}},{"id":1,"stmts":[{"Assign":{"place":{"local":4,"projections":[]},"rvalue":{"BinaryOp":["Lt",{"Copy":{"local":2,"projections":[]}},{"Move":{"local":5,"projections":[]}}]},"span":{"file":"nest_ctl.rs","line_start":2,"col_start":7,"line_end":2,"col_end":18}}}],"terminator":{"SwitchInt":{"discr":{"Move":{"local":4,"projections":[]}},"targets":[[0,8]],"otherwise":2,"exhaustive_enum_unreachable":false,"span":{"file":"nest_ctl.rs","line_start":2,"col_start":7,"line_end":2,"col_end":18}}}},{"id":2,"stmts":[],"terminator":{"Call":{"func":"<alloc::vec::Vec<alloc::vec::Vec<u32>> as core::ops::index::Index<usize>>::index","args":[{"Copy":{"local":1,"projections":[]}},{"Copy":{"local":2,"projections":[]}}],"dest":{"local":8,"projections":[]},"target":3,"span":{"file":"nest_ctl.rs","line_start":2,"col_start":27,"line_end":2,"col_end":30},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":39089,"substs_digest":[13454921569776302161,2279604291215425737]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":3,"stmts":[],"terminator":{"Call":{"func":"alloc::vec::Vec::<u32>::len","args":[{"Copy":{"local":8,"projections":[]}}],"dest":{"local":7,"projections":[]},"target":4,"span":{"file":"nest_ctl.rs","line_start":2,"col_start":26,"line_end":2,"col_end":36},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":8369930371133358469,"def_index":8821,"substs_digest":[937863789039580281,9258672918316184405]},"callee_key":{"sysroot_item":"VecLen","krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":8369930371133358469,"krate_name":"alloc"}}}},{"id":4,"stmts":[{"Assign":{"place":{"local":6,"projections":[]},"rvalue":{"BinaryOp":["Lt",{"Copy":{"local":3,"projections":[]}},{"Move":{"local":7,"projections":[]}}]},"span":{"file":"nest_ctl.rs","line_start":2,"col_start":22,"line_end":2,"col_end":36}}}],"terminator":{"SwitchInt":{"discr":{"Move":{"local":6,"projections":[]}},"targets":[[0,8]],"otherwise":5,"exhaustive_enum_unreachable":false,"span":{"file":"nest_ctl.rs","line_start":2,"col_start":22,"line_end":2,"col_end":36}}}},{"id":5,"stmts":[],"terminator":{"Call":{"func":"<alloc::vec::Vec<alloc::vec::Vec<u32>> as core::ops::index::Index<usize>>::index","args":[{"Copy":{"local":1,"projections":[]}},{"Copy":{"local":2,"projections":[]}}],"dest":{"local":10,"projections":[]},"target":6,"span":{"file":"nest_ctl.rs","line_start":2,"col_start":40,"line_end":2,"col_end":43},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":39089,"substs_digest":[13454921569776302161,2279604291215425737]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":6,"stmts":[],"terminator":{"Call":{"func":"<alloc::vec::Vec<u32> as core::ops::index::Index<usize>>::index","args":[{"Copy":{"local":10,"projections":[]}},{"Copy":{"local":3,"projections":[]}}],"dest":{"local":9,"projections":[]},"target":7,"span":{"file":"nest_ctl.rs","line_start":2,"col_start":43,"line_end":2,"col_end":46},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":39089,"substs_digest":[17091007639459144612,2033056495210424997]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":7,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Copy":{"local":9,"projections":["Deref"]}}},"span":{"file":"nest_ctl.rs","line_start":2,"col_start":39,"line_end":2,"col_end":46}}}],"terminator":{"Goto":9}},{"id":8,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Constant":{"Uint":[0,32]}}},"span":{"file":"nest_ctl.rs","line_start":2,"col_start":56,"line_end":2,"col_end":57}}}],"terminator":{"Goto":9}},{"id":9,"stmts":[],"terminator":"Return"}],"arg_count":3,"return_ty":{"Int":{"width":32,"signed":false}}},"contracts":[],"preconditions":[{"And":[{"Ge":[{"Var":["i","Int"]},{"Int":0}]},{"Le":[{"Var":["i","Int"]},{"Int":18446744073709551615}]}]},{"And":[{"Ge":[{"Var":["j","Int"]},{"Int":0}]},{"Le":[{"Var":["j","Int"]},{"Int":18446744073709551615}]}]}],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"#;

/// REAL extracted MIR (same compiler) of `deref_w.rs`:
///
/// ```text
/// pub struct W { pub flip: Cell<bool>, pub a: Vec<Vec<u32>>, pub b: Vec<Vec<u32>> }
/// impl Deref for W {
///     type Target = Vec<Vec<u32>>;
///     fn deref(&self) -> &Vec<Vec<u32>> {
///         let f = self.flip.get(); self.flip.set(!f);
///         if f { &self.a } else { &self.b }
///     }
/// }
/// pub fn h(w: &W, i: usize, j: usize) -> u32 { if j < w[i].len() { w[i][j] } else { 0 } }
/// ```
///
/// Each `w[i]` is `<deref_w::W as core::ops::deref::Deref>::deref(w)` (dests 7 and
/// 10) then std's `Vec<Vec<u32>>` index (dests 6 and 9). The std-deref hop traces
/// both to the root `w: &W`.
const MIR_DEREF_W_H: &str = r#"{"name":"h","def_path":"deref_w::h","span":{"file":"deref_w.rs","line_start":12,"col_start":0,"line_end":14,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Int":{"width":32,"signed":false}},"name":null},{"index":1,"ty":{"Ref":{"mutable":false,"inner":{"Adt":{"name":"deref_w::W","fields":[["flip",{"Adt":{"name":"core::cell::Cell","fields":[["value",{"Adt":{"name":"core::cell::UnsafeCell","fields":[["value","Bool"]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}],["a",{"Seq":{"elem":{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}}}],["b",{"Seq":{"elem":{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}}},"name":"w"},{"index":2,"ty":{"Int":{"width":64,"signed":false}},"name":"i"},{"index":3,"ty":{"Int":{"width":64,"signed":false}},"name":"j"},{"index":4,"ty":"Bool","name":null},{"index":5,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":6,"ty":{"Ref":{"mutable":false,"inner":{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}}},"name":null},{"index":7,"ty":{"Ref":{"mutable":false,"inner":{"Seq":{"elem":{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}}}}},"name":null},{"index":8,"ty":{"Ref":{"mutable":false,"inner":{"Int":{"width":32,"signed":false}}}},"name":null},{"index":9,"ty":{"Ref":{"mutable":false,"inner":{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}}},"name":null},{"index":10,"ty":{"Ref":{"mutable":false,"inner":{"Seq":{"elem":{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}}}}},"name":null}],"blocks":[{"id":0,"stmts":[],"terminator":{"Call":{"func":"<deref_w::W as core::ops::deref::Deref>::deref","args":[{"Copy":{"local":1,"projections":[]}}],"dest":{"local":7,"projections":[]},"target":1,"span":{"file":"deref_w.rs","line_start":13,"col_start":11,"line_end":13,"col_end":12},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":4448,"substs_digest":[13373871122401701778,4464211249249668075]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":1,"stmts":[],"terminator":{"Call":{"func":"<alloc::vec::Vec<alloc::vec::Vec<u32>> as core::ops::index::Index<usize>>::index","args":[{"Copy":{"local":7,"projections":[]}},{"Copy":{"local":2,"projections":[]}}],"dest":{"local":6,"projections":[]},"target":2,"span":{"file":"deref_w.rs","line_start":13,"col_start":12,"line_end":13,"col_end":15},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":39089,"substs_digest":[13454921569776302161,2279604291215425737]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":2,"stmts":[],"terminator":{"Call":{"func":"alloc::vec::Vec::<u32>::len","args":[{"Copy":{"local":6,"projections":[]}}],"dest":{"local":5,"projections":[]},"target":3,"span":{"file":"deref_w.rs","line_start":13,"col_start":11,"line_end":13,"col_end":21},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":8369930371133358469,"def_index":8821,"substs_digest":[937863789039580281,9258672918316184405]},"callee_key":{"sysroot_item":"VecLen","krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":8369930371133358469,"krate_name":"alloc"}}}},{"id":3,"stmts":[{"Assign":{"place":{"local":4,"projections":[]},"rvalue":{"BinaryOp":["Lt",{"Copy":{"local":3,"projections":[]}},{"Move":{"local":5,"projections":[]}}]},"span":{"file":"deref_w.rs","line_start":13,"col_start":7,"line_end":13,"col_end":21}}}],"terminator":{"SwitchInt":{"discr":{"Move":{"local":4,"projections":[]}},"targets":[[0,8]],"otherwise":4,"exhaustive_enum_unreachable":false,"span":{"file":"deref_w.rs","line_start":13,"col_start":7,"line_end":13,"col_end":21}}}},{"id":4,"stmts":[],"terminator":{"Call":{"func":"<deref_w::W as core::ops::deref::Deref>::deref","args":[{"Copy":{"local":1,"projections":[]}}],"dest":{"local":10,"projections":[]},"target":5,"span":{"file":"deref_w.rs","line_start":13,"col_start":24,"line_end":13,"col_end":25},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":4448,"substs_digest":[13373871122401701778,4464211249249668075]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":5,"stmts":[],"terminator":{"Call":{"func":"<alloc::vec::Vec<alloc::vec::Vec<u32>> as core::ops::index::Index<usize>>::index","args":[{"Copy":{"local":10,"projections":[]}},{"Copy":{"local":2,"projections":[]}}],"dest":{"local":9,"projections":[]},"target":6,"span":{"file":"deref_w.rs","line_start":13,"col_start":25,"line_end":13,"col_end":28},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":39089,"substs_digest":[13454921569776302161,2279604291215425737]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":6,"stmts":[],"terminator":{"Call":{"func":"<alloc::vec::Vec<u32> as core::ops::index::Index<usize>>::index","args":[{"Copy":{"local":9,"projections":[]}},{"Copy":{"local":3,"projections":[]}}],"dest":{"local":8,"projections":[]},"target":7,"span":{"file":"deref_w.rs","line_start":13,"col_start":28,"line_end":13,"col_end":31},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":39089,"substs_digest":[17091007639459144612,2033056495210424997]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":7,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Copy":{"local":8,"projections":["Deref"]}}},"span":{"file":"deref_w.rs","line_start":13,"col_start":24,"line_end":13,"col_end":31}}}],"terminator":{"Goto":9}},{"id":8,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Constant":{"Uint":[0,32]}}},"span":{"file":"deref_w.rs","line_start":13,"col_start":41,"line_end":13,"col_end":42}}}],"terminator":{"Goto":9}},{"id":9,"stmts":[],"terminator":"Return"}],"arg_count":3,"return_ty":{"Int":{"width":32,"signed":false}}},"contracts":[],"preconditions":[{"And":[{"Ge":[{"Var":["i","Int"]},{"Int":0}]},{"Le":[{"Var":["i","Int"]},{"Int":18446744073709551615}]}]},{"And":[{"Ge":[{"Var":["j","Int"]},{"Int":0}]},{"Le":[{"Var":["j","Int"]},{"Int":18446744073709551615}]}]}],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"#;

fn parse_mir(mir: &str) -> VerifiableFunction {
    serde_json::from_str(mir).expect("the captured MIR fixture must deserialize")
}

fn len_tie(func: &VerifiableFunction, a: usize, b: usize) -> Formula {
    Formula::Eq(
        Box::new(crate::guards::coll_len_var(func, a)),
        Box::new(crate::guards::coll_len_var(func, b)),
    )
}

#[test]
fn two_user_methods_named_index_get_no_length_tie() {
    let g = parse_mir(MIR_LT_INDEX_G);
    let callees: Vec<&str> = g
        .body
        .blocks
        .iter()
        .filter_map(|b| match &b.terminator {
            Terminator::Call { func, .. } => Some(func.as_str()),
            _ => None,
        })
        .collect();
    assert!(callees.contains(&"<lt_index::Two as lt_index::LoV>::index"), "{callees:?}");
    assert!(callees.contains(&"<lt_index::Two as lt_index::HiV>::index"), "{callees:?}");
    let facts = super::build_immutable_index_len_tie_facts(&g);
    assert!(facts.is_empty(), "two user `index` methods read two different Vecs: {facts:?}");
}

#[test]
fn std_index_through_a_user_deref_gets_no_length_tie() {
    let h = parse_mir(MIR_DEREF_W_H);
    let facts = super::build_immutable_index_len_tie_facts(&h);
    assert!(
        facts.is_empty(),
        "a user `Deref` need not return the same Vec twice, so the root `&W` ties nothing: {facts:?}"
    );
}

#[test]
fn std_nested_vec_index_keeps_its_length_tie() {
    // The control the builder was written for: two `v[i]` on a shared
    // `&Vec<Vec<u32>>` denote one inner `Vec`, so the `j < v[i].len()` guard
    // discharges `v[i][j]` (`slice proved` on stage1-w11).
    let nest = parse_mir(MIR_NEST_SHARED);
    assert!(matches!(
        &nest.body.locals[1].ty,
        Ty::Ref { mutable: false, inner } if matches!(&**inner, Ty::Seq { .. })
    ));
    let facts = super::build_immutable_index_len_tie_facts(&nest);
    assert_eq!(facts, vec![len_tie(&nest, 8, 10)]);
}

#[test]
fn a_bare_or_user_spelled_index_on_a_std_root_gets_no_length_tie() {
    // The SAME control, with only the callee spelling changed. A bare
    // `std::ops::Index::index` is not what the extractor emits and names no impl;
    // a user key (`Index<x::K<usize>>`) or a user trait is not std's `Index<usize>`.
    for spelling in [
        "std::ops::Index::index",
        "core::ops::Index::index",
        "<alloc::vec::Vec<alloc::vec::Vec<u32>> as core::ops::index::Index<x::K<usize>>>::index",
        "<alloc::vec::Vec<alloc::vec::Vec<u32>> as x::Idx>::index",
        "<alloc::vec::Vec<alloc::vec::Vec<u32>> as core::ops::index::IndexMut<usize>>::index_mut",
    ] {
        let mut nest = parse_mir(MIR_NEST_SHARED);
        for block in &mut nest.body.blocks {
            if let Terminator::Call { func, .. } = &mut block.terminator
                && func.as_str()
                    == "<alloc::vec::Vec<alloc::vec::Vec<u32>> as core::ops::index::Index<usize>>::index"
            {
                *func = spelling.to_string();
            }
        }
        let facts = super::build_immutable_index_len_tie_facts(&nest);
        assert!(facts.is_empty(), "`{spelling}`: {facts:?}");
    }
}

#[test]
fn a_std_index_on_a_user_root_type_gets_no_length_tie() {
    // The root gate on its own: std's callee, but the traced root's pointee is a
    // user type (a user `struct Vec` included), not a slice, an array or std's `Vec`.
    for name in ["user::W", "user::Vec", "user::vec::Vec<u32>"] {
        let mut nest = parse_mir(MIR_NEST_SHARED);
        nest.body.locals[1].ty = Ty::Ref { mutable: false, inner: Box::new(Ty::adt(name, vec![])) };
        let facts = super::build_immutable_index_len_tie_facts(&nest);
        assert!(facts.is_empty(), "`{name}`: {facts:?}");
    }
    // std's `Vec` by its exact path (a synthetic `Ty::Adt` std `Vec`) and a slice
    // root keep it.
    for inner in [
        Ty::adt("alloc::vec::Vec<alloc::vec::Vec<u32>>", vec![]),
        Ty::adt("std::vec::Vec", vec![]),
        Ty::Slice { elem: Box::new(Ty::Unit) },
    ] {
        let mut nest = parse_mir(MIR_NEST_SHARED);
        nest.body.locals[1].ty = Ty::Ref { mutable: false, inner: Box::new(inner.clone()) };
        let facts = super::build_immutable_index_len_tie_facts(&nest);
        assert_eq!(facts.len(), 1, "{inner:?}: {facts:?}");
    }
}
