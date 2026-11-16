//! Trust (2026-10-03, NAME-ANCHOR-1): the length-of-place recognizers name std's
//! `len`, not a method merely NAMED `len`. Pinned on REAL extracted MIR.

use trust_types::{BlockId, Formula, Operand, Place, Terminator, VerifiableFunction};

// ── THE STD LENGTH, NOT A METHOD NAMED `len` (Trust, 2026-10-03, NAME-ANCHOR-1) ─
//
// `operand_is_len_of_place` arm (a), `len_def_block` and `operand_is_len_of_base`
// read `_n = <..>::len(&place)` as the length of `place` whenever the callee's
// method tail was `len`. A user trait method named `len` may return anything, and
// the field-guard lane minted `coll_len(w.v) > j` from `if j < L::len(&w.v)`: the
// `w.v[j]` row came back `slice proved` (kernel-certified) on an index that
// panics (`tests/ui/trust/len_guard_field_user_trait_len.rs`). All three now ask
// `call_facts::is_std_inherent_len_call`, the matcher the `_len == coll_len` tie
// already uses.

/// REAL extracted MIR (`-Ztrust-dump=mir:<dir>`, stage 1 of main `a0877b2a62`,
/// 2026-10-03) of `len_draft.rs`:
///
/// ```text
/// pub struct W { pub v: Vec<u32> }
/// pub trait L { fn len(&self) -> usize; }
/// impl L for Vec<u32> { fn len(&self) -> usize { Vec::len(self).saturating_add(5) } }
/// pub fn f(w: &W, j: usize) -> u32 { if j < L::len(&w.v) { w.v[j] } else { 0 } }
/// pub fn f_ge(w: &W, j: usize) -> u32 { if L::len(&w.v) > j { w.v[j] } else { 0 } }
/// pub fn f_fq(w: &W, j: usize) -> u32 { if j < <Vec<u32> as L>::len(&w.v) { w.v[j] } else { 0 } }
/// pub fn f_good(w: &W, j: usize) -> u32 { if j < w.v.len() { w.v[j] } else { 0 } }
/// ```
///
/// The user call is extracted as `<alloc::vec::Vec<u32> as len_draft::L>::len`,
/// the genuine one as `alloc::vec::Vec::<u32>::len`.
const MIR_USER_LEN_F: &str = r#"{"name":"f","def_path":"len_draft::f","span":{"file":"len_draft.rs","line_start":23,"col_start":0,"line_end":25,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Int":{"width":32,"signed":false}},"name":null},{"index":1,"ty":{"Ref":{"mutable":false,"inner":{"Adt":{"name":"len_draft::W","fields":[["v",{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}}},"name":"w"},{"index":2,"ty":{"Int":{"width":64,"signed":false}},"name":"j"},{"index":3,"ty":"Bool","name":null},{"index":4,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":5,"ty":{"Ref":{"mutable":false,"inner":{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}}},"name":null},{"index":6,"ty":{"Ref":{"mutable":false,"inner":{"Int":{"width":32,"signed":false}}}},"name":null},{"index":7,"ty":{"Ref":{"mutable":false,"inner":{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}}},"name":null}],"blocks":[{"id":0,"stmts":[{"Assign":{"place":{"local":5,"projections":[]},"rvalue":{"Ref":{"mutable":false,"place":{"local":1,"projections":["Deref",{"Field":0}]}}},"span":{"file":"len_draft.rs","line_start":24,"col_start":18,"line_end":24,"col_end":22}}}],"terminator":{"Call":{"func":"<alloc::vec::Vec<u32> as len_draft::L>::len","args":[{"Copy":{"local":5,"projections":[]}}],"dest":{"local":4,"projections":[]},"target":1,"span":{"file":"len_draft.rs","line_start":24,"col_start":11,"line_end":24,"col_end":23},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":7993866034593849452,"def_index":6,"substs_digest":[7380399338322949592,16186388883692782947]},"callee_key":{"krate_is_real_sysroot":false,"krate_name_is_ambiguous":false,"stable_crate_id":7993866034593849452,"krate_name":"len_draft"}}}},{"id":1,"stmts":[{"Assign":{"place":{"local":3,"projections":[]},"rvalue":{"BinaryOp":["Lt",{"Copy":{"local":2,"projections":[]}},{"Move":{"local":4,"projections":[]}}]},"span":{"file":"len_draft.rs","line_start":24,"col_start":7,"line_end":24,"col_end":23}}}],"terminator":{"SwitchInt":{"discr":{"Move":{"local":3,"projections":[]}},"targets":[[0,4]],"otherwise":2,"exhaustive_enum_unreachable":false,"span":{"file":"len_draft.rs","line_start":24,"col_start":7,"line_end":24,"col_end":23}}}},{"id":2,"stmts":[{"Assign":{"place":{"local":7,"projections":[]},"rvalue":{"Ref":{"mutable":false,"place":{"local":1,"projections":["Deref",{"Field":0}]}}},"span":{"file":"len_draft.rs","line_start":24,"col_start":26,"line_end":24,"col_end":29}}}],"terminator":{"Call":{"func":"<alloc::vec::Vec<u32> as core::ops::index::Index<usize>>::index","args":[{"Move":{"local":7,"projections":[]}},{"Copy":{"local":2,"projections":[]}}],"dest":{"local":6,"projections":[]},"target":3,"span":{"file":"len_draft.rs","line_start":24,"col_start":29,"line_end":24,"col_end":32},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":39089,"substs_digest":[17091007639459144612,2033056495210424997]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":3,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Copy":{"local":6,"projections":["Deref"]}}},"span":{"file":"len_draft.rs","line_start":24,"col_start":26,"line_end":24,"col_end":32}}}],"terminator":{"Goto":5}},{"id":4,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Constant":{"Uint":[0,32]}}},"span":{"file":"len_draft.rs","line_start":24,"col_start":42,"line_end":24,"col_end":43}}}],"terminator":{"Goto":5}},{"id":5,"stmts":[],"terminator":"Return"}],"arg_count":2,"return_ty":{"Int":{"width":32,"signed":false}}},"contracts":[],"preconditions":[{"And":[{"Ge":[{"Var":["j","Int"]},{"Int":0}]},{"Le":[{"Var":["j","Int"]},{"Int":18446744073709551615}]}]}],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"#;
const MIR_USER_LEN_F_GE: &str = r#"{"name":"f_ge","def_path":"len_draft::f_ge","span":{"file":"len_draft.rs","line_start":27,"col_start":0,"line_end":29,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Int":{"width":32,"signed":false}},"name":null},{"index":1,"ty":{"Ref":{"mutable":false,"inner":{"Adt":{"name":"len_draft::W","fields":[["v",{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}}},"name":"w"},{"index":2,"ty":{"Int":{"width":64,"signed":false}},"name":"j"},{"index":3,"ty":"Bool","name":null},{"index":4,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":5,"ty":{"Ref":{"mutable":false,"inner":{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}}},"name":null},{"index":6,"ty":{"Ref":{"mutable":false,"inner":{"Int":{"width":32,"signed":false}}}},"name":null},{"index":7,"ty":{"Ref":{"mutable":false,"inner":{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}}},"name":null}],"blocks":[{"id":0,"stmts":[{"Assign":{"place":{"local":5,"projections":[]},"rvalue":{"Ref":{"mutable":false,"place":{"local":1,"projections":["Deref",{"Field":0}]}}},"span":{"file":"len_draft.rs","line_start":28,"col_start":14,"line_end":28,"col_end":18}}}],"terminator":{"Call":{"func":"<alloc::vec::Vec<u32> as len_draft::L>::len","args":[{"Copy":{"local":5,"projections":[]}}],"dest":{"local":4,"projections":[]},"target":1,"span":{"file":"len_draft.rs","line_start":28,"col_start":7,"line_end":28,"col_end":19},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":7993866034593849452,"def_index":6,"substs_digest":[7380399338322949592,16186388883692782947]},"callee_key":{"krate_is_real_sysroot":false,"krate_name_is_ambiguous":false,"stable_crate_id":7993866034593849452,"krate_name":"len_draft"}}}},{"id":1,"stmts":[{"Assign":{"place":{"local":3,"projections":[]},"rvalue":{"BinaryOp":["Gt",{"Move":{"local":4,"projections":[]}},{"Copy":{"local":2,"projections":[]}}]},"span":{"file":"len_draft.rs","line_start":28,"col_start":7,"line_end":28,"col_end":23}}}],"terminator":{"SwitchInt":{"discr":{"Move":{"local":3,"projections":[]}},"targets":[[0,4]],"otherwise":2,"exhaustive_enum_unreachable":false,"span":{"file":"len_draft.rs","line_start":28,"col_start":7,"line_end":28,"col_end":23}}}},{"id":2,"stmts":[{"Assign":{"place":{"local":7,"projections":[]},"rvalue":{"Ref":{"mutable":false,"place":{"local":1,"projections":["Deref",{"Field":0}]}}},"span":{"file":"len_draft.rs","line_start":28,"col_start":26,"line_end":28,"col_end":29}}}],"terminator":{"Call":{"func":"<alloc::vec::Vec<u32> as core::ops::index::Index<usize>>::index","args":[{"Move":{"local":7,"projections":[]}},{"Copy":{"local":2,"projections":[]}}],"dest":{"local":6,"projections":[]},"target":3,"span":{"file":"len_draft.rs","line_start":28,"col_start":29,"line_end":28,"col_end":32},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":39089,"substs_digest":[17091007639459144612,2033056495210424997]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":3,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Copy":{"local":6,"projections":["Deref"]}}},"span":{"file":"len_draft.rs","line_start":28,"col_start":26,"line_end":28,"col_end":32}}}],"terminator":{"Goto":5}},{"id":4,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Constant":{"Uint":[0,32]}}},"span":{"file":"len_draft.rs","line_start":28,"col_start":42,"line_end":28,"col_end":43}}}],"terminator":{"Goto":5}},{"id":5,"stmts":[],"terminator":"Return"}],"arg_count":2,"return_ty":{"Int":{"width":32,"signed":false}}},"contracts":[],"preconditions":[{"And":[{"Ge":[{"Var":["j","Int"]},{"Int":0}]},{"Le":[{"Var":["j","Int"]},{"Int":18446744073709551615}]}]}],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"#;
const MIR_USER_LEN_F_FQ: &str = r#"{"name":"f_fq","def_path":"len_draft::f_fq","span":{"file":"len_draft.rs","line_start":31,"col_start":0,"line_end":33,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Int":{"width":32,"signed":false}},"name":null},{"index":1,"ty":{"Ref":{"mutable":false,"inner":{"Adt":{"name":"len_draft::W","fields":[["v",{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}}},"name":"w"},{"index":2,"ty":{"Int":{"width":64,"signed":false}},"name":"j"},{"index":3,"ty":"Bool","name":null},{"index":4,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":5,"ty":{"Ref":{"mutable":false,"inner":{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}}},"name":null},{"index":6,"ty":{"Ref":{"mutable":false,"inner":{"Int":{"width":32,"signed":false}}}},"name":null},{"index":7,"ty":{"Ref":{"mutable":false,"inner":{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}}},"name":null}],"blocks":[{"id":0,"stmts":[{"Assign":{"place":{"local":5,"projections":[]},"rvalue":{"Ref":{"mutable":false,"place":{"local":1,"projections":["Deref",{"Field":0}]}}},"span":{"file":"len_draft.rs","line_start":32,"col_start":32,"line_end":32,"col_end":36}}}],"terminator":{"Call":{"func":"<alloc::vec::Vec<u32> as len_draft::L>::len","args":[{"Copy":{"local":5,"projections":[]}}],"dest":{"local":4,"projections":[]},"target":1,"span":{"file":"len_draft.rs","line_start":32,"col_start":11,"line_end":32,"col_end":37},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":7993866034593849452,"def_index":6,"substs_digest":[7380399338322949592,16186388883692782947]},"callee_key":{"krate_is_real_sysroot":false,"krate_name_is_ambiguous":false,"stable_crate_id":7993866034593849452,"krate_name":"len_draft"}}}},{"id":1,"stmts":[{"Assign":{"place":{"local":3,"projections":[]},"rvalue":{"BinaryOp":["Lt",{"Copy":{"local":2,"projections":[]}},{"Move":{"local":4,"projections":[]}}]},"span":{"file":"len_draft.rs","line_start":32,"col_start":7,"line_end":32,"col_end":37}}}],"terminator":{"SwitchInt":{"discr":{"Move":{"local":3,"projections":[]}},"targets":[[0,4]],"otherwise":2,"exhaustive_enum_unreachable":false,"span":{"file":"len_draft.rs","line_start":32,"col_start":7,"line_end":32,"col_end":37}}}},{"id":2,"stmts":[{"Assign":{"place":{"local":7,"projections":[]},"rvalue":{"Ref":{"mutable":false,"place":{"local":1,"projections":["Deref",{"Field":0}]}}},"span":{"file":"len_draft.rs","line_start":32,"col_start":40,"line_end":32,"col_end":43}}}],"terminator":{"Call":{"func":"<alloc::vec::Vec<u32> as core::ops::index::Index<usize>>::index","args":[{"Move":{"local":7,"projections":[]}},{"Copy":{"local":2,"projections":[]}}],"dest":{"local":6,"projections":[]},"target":3,"span":{"file":"len_draft.rs","line_start":32,"col_start":43,"line_end":32,"col_end":46},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":39089,"substs_digest":[17091007639459144612,2033056495210424997]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":3,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Copy":{"local":6,"projections":["Deref"]}}},"span":{"file":"len_draft.rs","line_start":32,"col_start":40,"line_end":32,"col_end":46}}}],"terminator":{"Goto":5}},{"id":4,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Constant":{"Uint":[0,32]}}},"span":{"file":"len_draft.rs","line_start":32,"col_start":56,"line_end":32,"col_end":57}}}],"terminator":{"Goto":5}},{"id":5,"stmts":[],"terminator":"Return"}],"arg_count":2,"return_ty":{"Int":{"width":32,"signed":false}}},"contracts":[],"preconditions":[{"And":[{"Ge":[{"Var":["j","Int"]},{"Int":0}]},{"Le":[{"Var":["j","Int"]},{"Int":18446744073709551615}]}]}],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"#;
const MIR_STD_LEN_F_GOOD: &str = r#"{"name":"f_good","def_path":"len_draft::f_good","span":{"file":"len_draft.rs","line_start":35,"col_start":0,"line_end":37,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Int":{"width":32,"signed":false}},"name":null},{"index":1,"ty":{"Ref":{"mutable":false,"inner":{"Adt":{"name":"len_draft::W","fields":[["v",{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}}},"name":"w"},{"index":2,"ty":{"Int":{"width":64,"signed":false}},"name":"j"},{"index":3,"ty":"Bool","name":null},{"index":4,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":5,"ty":{"Ref":{"mutable":false,"inner":{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}}},"name":null},{"index":6,"ty":{"Ref":{"mutable":false,"inner":{"Int":{"width":32,"signed":false}}}},"name":null},{"index":7,"ty":{"Ref":{"mutable":false,"inner":{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}}},"name":null}],"blocks":[{"id":0,"stmts":[{"Assign":{"place":{"local":5,"projections":[]},"rvalue":{"Ref":{"mutable":false,"place":{"local":1,"projections":["Deref",{"Field":0}]}}},"span":{"file":"len_draft.rs","line_start":36,"col_start":11,"line_end":36,"col_end":14}}}],"terminator":{"Call":{"func":"alloc::vec::Vec::<u32>::len","args":[{"Move":{"local":5,"projections":[]}}],"dest":{"local":4,"projections":[]},"target":1,"span":{"file":"len_draft.rs","line_start":36,"col_start":11,"line_end":36,"col_end":20},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":8369930371133358469,"def_index":8821,"substs_digest":[937863789039580281,9258672918316184405]},"callee_key":{"sysroot_item":"VecLen","krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":8369930371133358469,"krate_name":"alloc"}}}},{"id":1,"stmts":[{"Assign":{"place":{"local":3,"projections":[]},"rvalue":{"BinaryOp":["Lt",{"Copy":{"local":2,"projections":[]}},{"Move":{"local":4,"projections":[]}}]},"span":{"file":"len_draft.rs","line_start":36,"col_start":7,"line_end":36,"col_end":20}}}],"terminator":{"SwitchInt":{"discr":{"Move":{"local":3,"projections":[]}},"targets":[[0,4]],"otherwise":2,"exhaustive_enum_unreachable":false,"span":{"file":"len_draft.rs","line_start":36,"col_start":7,"line_end":36,"col_end":20}}}},{"id":2,"stmts":[{"Assign":{"place":{"local":7,"projections":[]},"rvalue":{"Ref":{"mutable":false,"place":{"local":1,"projections":["Deref",{"Field":0}]}}},"span":{"file":"len_draft.rs","line_start":36,"col_start":23,"line_end":36,"col_end":26}}}],"terminator":{"Call":{"func":"<alloc::vec::Vec<u32> as core::ops::index::Index<usize>>::index","args":[{"Move":{"local":7,"projections":[]}},{"Copy":{"local":2,"projections":[]}}],"dest":{"local":6,"projections":[]},"target":3,"span":{"file":"len_draft.rs","line_start":36,"col_start":26,"line_end":36,"col_end":29},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":39089,"substs_digest":[17091007639459144612,2033056495210424997]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":3,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Copy":{"local":6,"projections":["Deref"]}}},"span":{"file":"len_draft.rs","line_start":36,"col_start":23,"line_end":36,"col_end":29}}}],"terminator":{"Goto":5}},{"id":4,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Constant":{"Uint":[0,32]}}},"span":{"file":"len_draft.rs","line_start":36,"col_start":39,"line_end":36,"col_end":40}}}],"terminator":{"Goto":5}},{"id":5,"stmts":[],"terminator":"Return"}],"arg_count":2,"return_ty":{"Int":{"width":32,"signed":false}}},"contracts":[],"preconditions":[{"And":[{"Ge":[{"Var":["j","Int"]},{"Int":0}]},{"Le":[{"Var":["j","Int"]},{"Int":18446744073709551615}]}]}],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"#;

fn parse_mir(mir: &str) -> VerifiableFunction {
    serde_json::from_str(mir).expect("the captured MIR fixture must deserialize")
}

/// The block whose terminator is the `w.v[j]` index call.
fn index_block(func: &VerifiableFunction) -> BlockId {
    func.body
        .blocks
        .iter()
        .find(
            |b| matches!(&b.terminator, Terminator::Call { func: c, .. } if c.ends_with("::index")),
        )
        .map(|b| b.id)
        .expect("the fixture indexes `w.v`")
}

#[test]
fn a_user_trait_len_mints_no_field_guard_fact() {
    for (name, mir) in
        [("f", MIR_USER_LEN_F), ("f_ge", MIR_USER_LEN_F_GE), ("f_fq", MIR_USER_LEN_F_FQ)]
    {
        let func = parse_mir(mir);
        let map = super::build_len_guard_field_map(&func);
        assert!(
            map.is_empty(),
            "`{name}`: a user `L::len` is not the length of `w.v`; got {map:?}"
        );
    }
}

#[test]
fn the_std_vec_len_keeps_its_field_guard_fact() {
    let func = parse_mir(MIR_STD_LEN_F_GOOD);
    let map = super::build_len_guard_field_map(&func);
    let facts = map.get(&index_block(&func)).expect("`w.v.len()` guards the `w.v[j]` read");
    assert!(
        facts.iter().any(|f| matches!(f, Formula::Gt(..))),
        "`j < w.v.len()` gives `coll_len(w.v) > j` on the read: {facts:?}"
    );
}

/// REAL extracted MIR (same stage 1) of `lenbase.rs`, the base-local twin:
///
/// ```text
/// pub fn head(v: &Vec<u32>) -> &[u32] { let n = L::len(v); &v[..n] }     // `_2 = <.. as lenbase::L>::len(copy _1)`
/// pub fn head_good(v: &Vec<u32>) -> &[u32] { let n = v.len(); &v[..n] }  // `_2 = alloc::vec::Vec::<u32>::len(copy _1)`
/// ```
const MIR_USER_LEN_HEAD: &str = r#"{"name":"head","def_path":"lenbase::head","span":{"file":"lenbase.rs","line_start":9,"col_start":0,"line_end":12,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Ref":{"mutable":false,"inner":{"Slice":{"elem":{"Int":{"width":32,"signed":false}}}}}},"name":null},{"index":1,"ty":{"Ref":{"mutable":false,"inner":{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}}},"name":"v"},{"index":2,"ty":{"Int":{"width":64,"signed":false}},"name":"n"},{"index":3,"ty":{"Adt":{"name":"core::ops::range::RangeTo","fields":[["end",{"Int":{"width":64,"signed":false}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}},"name":null}],"blocks":[{"id":0,"stmts":[],"terminator":{"Call":{"func":"<alloc::vec::Vec<u32> as lenbase::L>::len","args":[{"Copy":{"local":1,"projections":[]}}],"dest":{"local":2,"projections":[]},"target":1,"span":{"file":"lenbase.rs","line_start":10,"col_start":12,"line_end":10,"col_end":21},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":13026113645171968224,"def_index":4,"substs_digest":[7380399338322949592,16186388883692782947]},"callee_key":{"krate_is_real_sysroot":false,"krate_name_is_ambiguous":false,"stable_crate_id":13026113645171968224,"krate_name":"lenbase"}}}},{"id":1,"stmts":[{"Assign":{"place":{"local":3,"projections":[]},"rvalue":{"Aggregate":[{"Adt":{"name":"core::ops::range::RangeTo","variant":0,"active_field":null,"args":"core::ops::range::RangeTo<usize>"}},[{"Copy":{"local":2,"projections":[]}}]]},"span":{"file":"lenbase.rs","line_start":11,"col_start":7,"line_end":11,"col_end":10}}}],"terminator":{"Call":{"func":"<alloc::vec::Vec<u32> as core::ops::index::Index<core::ops::range::RangeTo<usize>>>::index","args":[{"Copy":{"local":1,"projections":[]}},{"Move":{"local":3,"projections":[]}}],"dest":{"local":0,"projections":[]},"target":2,"span":{"file":"lenbase.rs","line_start":11,"col_start":6,"line_end":11,"col_end":11},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":39089,"substs_digest":[626731377287611787,18102695247268701042]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":2,"stmts":[],"terminator":"Return"}],"arg_count":1,"return_ty":{"Ref":{"mutable":false,"inner":{"Slice":{"elem":{"Int":{"width":32,"signed":false}}}}}}},"contracts":[],"preconditions":[],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"#;
const MIR_STD_LEN_HEAD_GOOD: &str = r#"{"name":"head_good","def_path":"lenbase::head_good","span":{"file":"lenbase.rs","line_start":13,"col_start":0,"line_end":16,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Ref":{"mutable":false,"inner":{"Slice":{"elem":{"Int":{"width":32,"signed":false}}}}}},"name":null},{"index":1,"ty":{"Ref":{"mutable":false,"inner":{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}}},"name":"v"},{"index":2,"ty":{"Int":{"width":64,"signed":false}},"name":"n"},{"index":3,"ty":{"Adt":{"name":"core::ops::range::RangeTo","fields":[["end",{"Int":{"width":64,"signed":false}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}},"name":null}],"blocks":[{"id":0,"stmts":[],"terminator":{"Call":{"func":"alloc::vec::Vec::<u32>::len","args":[{"Copy":{"local":1,"projections":[]}}],"dest":{"local":2,"projections":[]},"target":1,"span":{"file":"lenbase.rs","line_start":14,"col_start":12,"line_end":14,"col_end":19},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":8369930371133358469,"def_index":8821,"substs_digest":[937863789039580281,9258672918316184405]},"callee_key":{"sysroot_item":"VecLen","krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":8369930371133358469,"krate_name":"alloc"}}}},{"id":1,"stmts":[{"Assign":{"place":{"local":3,"projections":[]},"rvalue":{"Aggregate":[{"Adt":{"name":"core::ops::range::RangeTo","variant":0,"active_field":null,"args":"core::ops::range::RangeTo<usize>"}},[{"Copy":{"local":2,"projections":[]}}]]},"span":{"file":"lenbase.rs","line_start":15,"col_start":7,"line_end":15,"col_end":10}}}],"terminator":{"Call":{"func":"<alloc::vec::Vec<u32> as core::ops::index::Index<core::ops::range::RangeTo<usize>>>::index","args":[{"Copy":{"local":1,"projections":[]}},{"Move":{"local":3,"projections":[]}}],"dest":{"local":0,"projections":[]},"target":2,"span":{"file":"lenbase.rs","line_start":15,"col_start":6,"line_end":15,"col_end":11},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":39089,"substs_digest":[626731377287611787,18102695247268701042]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":2,"stmts":[],"terminator":"Return"}],"arg_count":1,"return_ty":{"Ref":{"mutable":false,"inner":{"Slice":{"elem":{"Int":{"width":32,"signed":false}}}}}}},"contracts":[],"preconditions":[],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"#;

#[test]
fn a_user_trait_len_is_not_the_length_of_its_base() {
    let n = Operand::Copy(Place::local(2));
    let head = parse_mir(MIR_USER_LEN_HEAD);
    assert!(!super::operand_is_len_of_base(&head, &n, 1, 8), "`L::len(v)` is not `v.len()`");
    assert_eq!(super::len_def_block(&head, &n, 8), None, "no length snapshot for `L::len(v)`");

    let good = parse_mir(MIR_STD_LEN_HEAD_GOOD);
    assert!(super::operand_is_len_of_base(&good, &n, 1, 8), "`v.len()` is the length of `v`");
    assert_eq!(super::len_def_block(&good, &n, 8), Some(0), "`v.len()` is defined in bb0");
}

/// The matcher the three length-of-place recognizers now share is the one the
/// `_len == coll_len(base)` tie uses: the std `Vec`/slice/`str`/`String` `len`
/// (`total_summary_len_call`) and `VecDeque::len`, in the spellings the extractor
/// emits, and nothing a user crate can spell.
#[test]
fn std_len_matcher_is_the_tie_sites_matcher() {
    for callee in [
        "alloc::vec::Vec::<u32>::len",
        "std::vec::Vec::<i64>::len",
        "core::slice::<impl [u8]>::len",
        "core::str::<impl str>::len",
        "alloc::string::String::len",
        "alloc::collections::vec_deque::VecDeque::<u32>::len",
    ] {
        assert!(super::is_std_inherent_len_call(callee), "std length: {callee}");
        assert!(
            trust_types::total_call_summaries::total_summary_len_call(callee)
                || callee.contains("VecDeque"),
            "the tie site's matcher agrees: {callee}"
        );
    }
    for callee in [
        "<alloc::vec::Vec<u32> as len_draft::L>::len",
        "<alloc::vec::Vec<u32> as lenbase::L>::len",
        "len_draft::len",
        "mycrate::Vec::<u32>::len",
        "mycrate::alloc::vec::Vec::<u32>::len",
        "__trust_crate@deadbeef::alloc::vec::Vec::<u32>::len",
        "core::slice::Iter::<u8>::len",
        "<core::slice::Iter<'_, u8> as core::iter::ExactSizeIterator>::len",
        "alloc::collections::btree::map::BTreeMap::<u32, u32>::len",
    ] {
        assert!(!super::is_std_inherent_len_call(callee), "not a std container length: {callee}");
    }
}

// ── THE STD LENGTH BY ITS DefId KEY, THROUGH THE `__trust_args` TAG (LEN-KEY-1) ──
//
// Trust (2026-10-06, LEN-KEY-1): in a graph with a duplicate crate name (an
// ordinary Cargo graph: a crates.io `memchr` shares std's dependency's name) the
// extractor renders std's `len` as `alloc::vec::Vec::<u32>::len::<__trust_args@…>`,
// which the exact string matcher declines. The tie site and these three
// recognizers also accept the call's compiler-minted key (`VecLen`, `SliceLen`,
// `StrLen`, `StringLen` on a residency-authenticated sysroot DefId). The fixtures
// are REAL extracted MIR of `tests/dup_crate_name_len_tie_realmir.rs`'s source (the
// stage 1 of `c797f90c1`, a `memchr` extern loaded); its header has the source.

fn dup_fixture(name: &str) -> VerifiableFunction {
    let path =
        format!("{}/tests/fixtures/dup_crate_name_len_tie/{name}.json", env!("CARGO_MANIFEST_DIR"));
    parse_mir(&std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}")))
}

/// `field_good`'s `w.v`: `(*_1).0`.
fn field_v() -> Place {
    Place {
        local: 1,
        projections: vec![trust_types::Projection::Deref, trust_types::Projection::Field(0)],
    }
}

#[test]
fn a_tagged_std_len_is_the_length_of_its_place_by_its_key() {
    // `plain_tie`: bb0 `_3 = alloc::vec::Vec::<u32>::len::<__trust_args@…>(copy _1)`.
    let n = Operand::Copy(Place::local(3));
    let plain = dup_fixture("plain_tie");
    assert!(super::operand_is_len_of_base(&plain, &n, 1, 8), "tagged `v.len()` is `v`'s length");
    assert_eq!(super::len_def_block(&plain, &n, 8), Some(0), "defined in bb0");
    // `field_good`: bb0 `_4 = alloc::vec::Vec::<u32>::len::<__trust_args@…>(move _5)`, `_5 = &(*_1).0`.
    let field = dup_fixture("field_good");
    assert!(super::operand_is_len_of_place(&field, &Operand::Copy(Place::local(4)), &field_v()));

    // The same calls with the key withdrawn: the tagged string alone admits nothing.
    for (mut func, name) in [(plain, "plain_tie"), (field, "field_good")] {
        for b in &mut func.body.blocks {
            if let Terminator::Call { func: callee, callee_key, .. } = &mut b.terminator
                && callee.contains("::len::<__trust_args@")
            {
                *callee_key = None;
            }
        }
        if name == "plain_tie" {
            assert!(!super::operand_is_len_of_base(&func, &n, 1, 8), "{name}: key withdrawn");
            assert_eq!(super::len_def_block(&func, &n, 8), None, "{name}: key withdrawn");
        } else {
            let len = Operand::Copy(Place::local(4));
            assert!(
                !super::operand_is_len_of_place(&func, &len, &field_v()),
                "{name}: key withdrawn"
            );
        }
    }
}

#[test]
fn a_tagged_user_len_is_still_not_the_length_of_its_place() {
    // A GENERIC local impl keeps the trait spelling AND the tag:
    // `<alloc::vec::Vec<u32> as dup_len_tie::GL>::len::<__trust_args@…>`, keyed on the
    // local trait method (no sysroot tag).
    let plain = dup_fixture("plain_user_generic_len");
    let n = Operand::Copy(Place::local(3));
    assert!(!super::operand_is_len_of_base(&plain, &n, 1, 8), "`GL::len(v)` is not `v.len()`");
    assert_eq!(super::len_def_block(&plain, &n, 8), None);
    let field = dup_fixture("field_user_generic_len");
    assert!(!super::operand_is_len_of_place(&field, &Operand::Copy(Place::local(4)), &field_v()));
}

#[test]
fn the_len_key_is_std_inherent_len_only_on_a_resident_sysroot_crate() {
    use trust_types::{CalleeKey, SysrootItem as S};
    let key = |item: Option<S>, real: bool| CalleeKey {
        sysroot_item: item,
        krate_is_real_sysroot: real,
        krate_name_is_ambiguous: false,
        stable_crate_id: 1,
        krate_name: "alloc".to_string(),
        foreign_block_leaf: None,
        upstream_foreign_link_symbol: None,
        diverging_entry: None,
    };
    for item in [S::VecLen, S::SliceLen, S::StrLen, S::StringLen] {
        assert!(super::callee_key_is_std_inherent_len(Some(&key(Some(item), true))), "{item:?}");
        assert!(
            !super::callee_key_is_std_inherent_len(Some(&key(Some(item), false))),
            "{item:?} on a crate that is not the resident sysroot"
        );
    }
    assert!(!super::callee_key_is_std_inherent_len(Some(&key(Some(S::CloneClone), true))));
    assert!(!super::callee_key_is_std_inherent_len(Some(&key(None, true))));
    assert!(!super::callee_key_is_std_inherent_len(None));
}
