//! Trust (2026-10-04, NAME-ANCHOR-2): an `Ord::min`/`max`/`clamp` fact names the
//! SELECTED IMPL, not only the trait path. Pinned on REAL extracted MIR.

use trust_types::{
    BlockId, ConstValue, LocalDecl, Operand, Place, SourceSpan, Terminator, Ty, VerifiableBody,
    VerifiableFunction,
};

// ── THE SELF TYPE, NOT ONLY THE TRAIT (Trust, 2026-10-04, NAME-ANCHOR-2) ──────
//
// NAME-ANCHOR-1 anchored `call_facts::ord_method` to std's trait path
// (`<T as core::cmp::Ord>::min`). That names the TRAIT METHOD, whose DefId is
// core's, but not the body that runs: `Ord::min`/`max`/`clamp` are provided
// methods any impl may override. A user `impl Ord for E` on a `#[repr(u8)]`
// fieldless enum whose `min` returns `E::B` renders as
// `<ordenum::E as core::cmp::Ord>::min` with `callee_key` `krate_name: core`,
// `krate_is_real_sysroot: true`. The call-dest lane minted `dest <= arg` for it,
// the Clean kernel certified the `+ 100` overflow row, the elision deleted the
// check, and `f(E::A)` returned 44 where vanilla Rust panics
// (`tests/ui/trust/ord_min_max_requires_primitive_self{,_run}.rs`). Every
// consumer now asks `call_facts::primitive_int_ord_method`, which also requires
// the destination to be a primitive integer and every argument to be that type.

/// REAL extracted MIR (`-Ztrust-dump=mir:<dir>`, stage 1 of integ/wave11
/// `936573497e`, 2026-10-04) of `ordenum.rs`:
///
/// ```text
/// #[repr(u8)] #[derive(PartialEq, Eq, PartialOrd, Clone, Copy)]
/// pub enum E { A = 0, B = 200 }
/// impl Ord for E {
///     fn cmp(&self, o: &Self) -> Ordering { (*self as u8).cmp(&(*o as u8)) }
///     fn min(self, _o: Self) -> Self { E::B }
///     fn max(self, _o: Self) -> Self { E::A }
/// }
/// pub fn f(x: E) -> u8 { (x.min(E::A) as u8) + 100 }   // `<ordenum::E as core::cmp::Ord>::min`
/// pub fn g(x: E) -> u8 { (x.max(E::B) as u8) - 100 }   // `<ordenum::E as core::cmp::Ord>::max`
/// ```
///
/// Both call dests are local 2, `Ty::Adt ordenum::E`; the second argument is an
/// aggregate-defined local 3.
const MIR_ORDENUM_F: &str = r#"{"name":"f","def_path":"ordenum::f","span":{"file":"ordenum.rs","line_start":11,"col_start":0,"line_end":11,"col_end":50},"body":{"locals":[{"index":0,"ty":{"Int":{"width":8,"signed":false}},"name":null},{"index":1,"ty":{"Adt":{"name":"ordenum::E","fields":[["__tag",{"Int":{"width":64,"signed":true}}]],"variants":[{"name":"A","discriminant":0,"fields":[]},{"name":"B","discriminant":200,"fields":[]}],"disc_index_safe":true,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Enum"}},"name":"x"},{"index":2,"ty":{"Adt":{"name":"ordenum::E","fields":[["__tag",{"Int":{"width":64,"signed":true}}]],"variants":[{"name":"A","discriminant":0,"fields":[]},{"name":"B","discriminant":200,"fields":[]}],"disc_index_safe":true,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Enum"}},"name":null},{"index":3,"ty":{"Adt":{"name":"ordenum::E","fields":[["__tag",{"Int":{"width":64,"signed":true}}]],"variants":[{"name":"A","discriminant":0,"fields":[]},{"name":"B","discriminant":200,"fields":[]}],"disc_index_safe":true,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Enum"}},"name":null},{"index":4,"ty":{"Int":{"width":8,"signed":false}},"name":null},{"index":5,"ty":{"Tuple":[{"Int":{"width":8,"signed":false}},"Bool"]},"name":null}],"blocks":[{"id":0,"stmts":[{"Assign":{"place":{"local":3,"projections":[]},"rvalue":{"Aggregate":[{"Adt":{"name":"ordenum::E","variant":0,"active_field":null,"args":"ordenum::E"}},[]]},"span":{"file":"ordenum.rs","line_start":11,"col_start":30,"line_end":11,"col_end":34}}}],"terminator":{"Call":{"func":"<ordenum::E as core::cmp::Ord>::min","args":[{"Copy":{"local":1,"projections":[]}},{"Move":{"local":3,"projections":[]}}],"dest":{"local":2,"projections":[]},"target":1,"span":{"file":"ordenum.rs","line_start":11,"col_start":24,"line_end":11,"col_end":35},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":3570,"substs_digest":[12033310276903382575,7400709930554413516]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":1,"stmts":[{"Assign":{"place":{"local":4,"projections":[]},"rvalue":{"Discriminant":{"local":2,"projections":[]}},"span":{"file":"ordenum.rs","line_start":11,"col_start":23,"line_end":11,"col_end":42}}},{"Assign":{"place":{"local":5,"projections":[]},"rvalue":{"CheckedBinaryOp":["Add",{"Copy":{"local":4,"projections":[]}},{"Constant":{"Uint":[100,8]}}]},"span":{"file":"ordenum.rs","line_start":11,"col_start":23,"line_end":11,"col_end":48}}}],"terminator":{"Assert":{"cond":{"Move":{"local":5,"projections":[{"Field":1}]}},"expected":false,"msg":{"Overflow":"Add"},"target":2,"span":{"file":"ordenum.rs","line_start":11,"col_start":23,"line_end":11,"col_end":48},"unwind":"Continue"}}},{"id":2,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Move":{"local":5,"projections":[{"Field":0}]}}},"span":{"file":"ordenum.rs","line_start":11,"col_start":23,"line_end":11,"col_end":48}}}],"terminator":"Return"}],"arg_count":1,"return_ty":{"Int":{"width":8,"signed":false}}},"contracts":[],"preconditions":[{"Or":[{"Eq":[{"Var":["_4","Int"]},{"Int":0}]},{"Eq":[{"Var":["_4","Int"]},{"Int":200}]}]}],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"#;
const MIR_ORDENUM_G: &str = r#"{"name":"g","def_path":"ordenum::g","span":{"file":"ordenum.rs","line_start":12,"col_start":0,"line_end":12,"col_end":50},"body":{"locals":[{"index":0,"ty":{"Int":{"width":8,"signed":false}},"name":null},{"index":1,"ty":{"Adt":{"name":"ordenum::E","fields":[["__tag",{"Int":{"width":64,"signed":true}}]],"variants":[{"name":"A","discriminant":0,"fields":[]},{"name":"B","discriminant":200,"fields":[]}],"disc_index_safe":true,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Enum"}},"name":"x"},{"index":2,"ty":{"Adt":{"name":"ordenum::E","fields":[["__tag",{"Int":{"width":64,"signed":true}}]],"variants":[{"name":"A","discriminant":0,"fields":[]},{"name":"B","discriminant":200,"fields":[]}],"disc_index_safe":true,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Enum"}},"name":null},{"index":3,"ty":{"Adt":{"name":"ordenum::E","fields":[["__tag",{"Int":{"width":64,"signed":true}}]],"variants":[{"name":"A","discriminant":0,"fields":[]},{"name":"B","discriminant":200,"fields":[]}],"disc_index_safe":true,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Enum"}},"name":null},{"index":4,"ty":{"Int":{"width":8,"signed":false}},"name":null},{"index":5,"ty":{"Tuple":[{"Int":{"width":8,"signed":false}},"Bool"]},"name":null}],"blocks":[{"id":0,"stmts":[{"Assign":{"place":{"local":3,"projections":[]},"rvalue":{"Aggregate":[{"Adt":{"name":"ordenum::E","variant":1,"active_field":null,"args":"ordenum::E"}},[]]},"span":{"file":"ordenum.rs","line_start":12,"col_start":30,"line_end":12,"col_end":34}}}],"terminator":{"Call":{"func":"<ordenum::E as core::cmp::Ord>::max","args":[{"Copy":{"local":1,"projections":[]}},{"Move":{"local":3,"projections":[]}}],"dest":{"local":2,"projections":[]},"target":1,"span":{"file":"ordenum.rs","line_start":12,"col_start":24,"line_end":12,"col_end":35},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":3569,"substs_digest":[12033310276903382575,7400709930554413516]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":1,"stmts":[{"Assign":{"place":{"local":4,"projections":[]},"rvalue":{"Discriminant":{"local":2,"projections":[]}},"span":{"file":"ordenum.rs","line_start":12,"col_start":23,"line_end":12,"col_end":42}}},{"Assign":{"place":{"local":5,"projections":[]},"rvalue":{"CheckedBinaryOp":["Sub",{"Copy":{"local":4,"projections":[]}},{"Constant":{"Uint":[100,8]}}]},"span":{"file":"ordenum.rs","line_start":12,"col_start":23,"line_end":12,"col_end":48}}}],"terminator":{"Assert":{"cond":{"Move":{"local":5,"projections":[{"Field":1}]}},"expected":false,"msg":{"Overflow":"Sub"},"target":2,"span":{"file":"ordenum.rs","line_start":12,"col_start":23,"line_end":12,"col_end":48},"unwind":"Continue"}}},{"id":2,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Move":{"local":5,"projections":[{"Field":0}]}}},"span":{"file":"ordenum.rs","line_start":12,"col_start":23,"line_end":12,"col_end":48}}}],"terminator":"Return"}],"arg_count":1,"return_ty":{"Int":{"width":8,"signed":false}}},"contracts":[],"preconditions":[{"Or":[{"Eq":[{"Var":["_4","Int"]},{"Int":0}]},{"Eq":[{"Var":["_4","Int"]},{"Int":200}]}]}],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"#;

fn parse_mir(mir: &str) -> VerifiableFunction {
    serde_json::from_str(mir).expect("the captured MIR fixture must deserialize")
}

/// Every semantic-guard fact (any block) that bounds the call dest `dest` — the
/// shapes `ord_min_max_clamp_result_facts` mints: `<=`/`>=` for `min`/`max`, and
/// the conjunction (constant bounds) or guarded disjunction for `clamp`.
fn ord_dest_facts(func: &VerifiableFunction, dest: usize) -> Vec<String> {
    let name = crate::place_to_var_name(func, &Place::local(dest));
    let map = super::build_semantic_guard_map(func);
    let mut out: Vec<String> = map
        .values()
        .flatten()
        .map(|f| format!("{f:?}"))
        .filter(|s| {
            ["Le(", "Ge(", "And(", "Or("].iter().any(|p| s.starts_with(p))
                && (s.contains(&format!("Var(\"{name}\"")) || s.contains(&format!("Var(\"{name}#")))
        })
        .collect();
    out.sort();
    out.dedup();
    out
}

#[test]
fn a_user_ord_min_override_mints_no_call_dest_fact() {
    let f = parse_mir(MIR_ORDENUM_F);
    let Terminator::Call { func: callee, .. } = &f.body.blocks[0].terminator else {
        panic!("block 0 of `f` is the `min` call")
    };
    assert_eq!(callee, "<ordenum::E as core::cmp::Ord>::min");
    // The trait-path anchor alone still says "std's min" — that is the point:
    // it names the trait, not the impl.
    assert_eq!(super::ord_method(callee), Some("min"));
    let facts = ord_dest_facts(&f, 2);
    assert!(facts.is_empty(), "a user `Ord::min` override bounds nothing: {facts:?}");
    assert!(!super::local_is_min_max_result(&f, 2), "dest 2 is a user `min` result");
    assert!(super::build_min_max_facts(&f).is_empty());
}

#[test]
fn a_user_ord_max_override_mints_no_call_dest_fact() {
    let g = parse_mir(MIR_ORDENUM_G);
    let Terminator::Call { func: callee, .. } = &g.body.blocks[0].terminator else {
        panic!("block 0 of `g` is the `max` call")
    };
    assert_eq!(callee, "<ordenum::E as core::cmp::Ord>::max");
    let facts = ord_dest_facts(&g, 2);
    assert!(facts.is_empty(), "a user `Ord::max` override bounds nothing: {facts:?}");
    assert!(!super::local_is_min_max_result(&g, 2), "dest 2 is a user `max` result");
    assert!(super::build_min_max_facts(&g).is_empty());
}

const U32: Ty = Ty::Int { width: 32, signed: false };

fn user_e() -> Ty {
    Ty::adt("user::E", vec![("__tag".to_string(), Ty::Int { width: 64, signed: true })])
}

/// `_2 = <callee>(_1, consts..)` then return, every local of type `self_ty`. The
/// constant arguments are what the const-bound summaries read.
fn ord_call_func(callee: &str, self_ty: Ty, consts: &[i128]) -> VerifiableFunction {
    let mut args = vec![Operand::Copy(Place::local(1))];
    args.extend(consts.iter().map(|&c| Operand::Constant(ConstValue::Int(c))));
    VerifiableFunction {
        name: "h".into(),
        def_path: "user::h".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: self_ty.clone(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: self_ty, name: None },
            ],
            blocks: vec![
                trust_types::BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: trust_types::UnwindEdge::Unreachable,
                        func: callee.into(),
                        args,
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        callee_identity: None,
                        callee_key: None,
                        is_foreign: false,
                    },
                },
                trust_types::BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

#[test]
fn const_bound_summaries_refuse_a_user_self() {
    // `min_call_const_upper_bound`, `ret_call_const_lower_bound`,
    // `cast_source_const_lower` and `cast_source_const_upper_nonneg` read a bound
    // off the constant argument of a `min`/`max`/`clamp` that DEFINES the local.
    // For a user `Self` the body that runs is the user impl, which may return
    // anything.
    for (trait_path, free) in
        [("<user::E as core::cmp::Ord>", "core::cmp"), ("<user::E as std::cmp::Ord>", "std::cmp")]
    {
        let min = ord_call_func(&format!("{trait_path}::min"), user_e(), &[0]);
        assert_eq!(super::min_call_const_upper_bound(&min, 2), None, "{trait_path}::min");
        let free_min = ord_call_func(&format!("{free}::min"), user_e(), &[0]);
        assert_eq!(super::min_call_const_upper_bound(&free_min, 2), None, "{free}::min");
        let max = ord_call_func(&format!("{trait_path}::max"), user_e(), &[200]);
        assert_eq!(super::ret_call_const_lower_bound(&max, 2), None, "{trait_path}::max");
        assert_eq!(super::cast_source_const_lower(&max, 2), None, "{trait_path}::max");
        let clamp = ord_call_func(&format!("{trait_path}::clamp"), user_e(), &[0, 200]);
        assert_eq!(super::ret_call_const_lower_bound(&clamp, 2), None, "{trait_path}::clamp");
        assert_eq!(super::cast_source_const_upper_nonneg(&clamp, 2), None, "{trait_path}::clamp");
        assert!(!super::local_is_min_max_result(&min, 2), "{trait_path}::min");
        assert!(!super::local_is_min_max_result(&max, 2), "{trait_path}::max");
        assert!(ord_dest_facts(&min, 2).is_empty(), "{trait_path}::min");
        assert!(ord_dest_facts(&free_min, 2).is_empty(), "{free}::min");
        assert!(ord_dest_facts(&max, 2).is_empty(), "{trait_path}::max");
        assert!(ord_dest_facts(&clamp, 2).is_empty(), "{trait_path}::clamp");
    }
}

#[test]
fn a_primitive_self_keeps_every_ord_fact() {
    // The controls: the same shapes at `u32`, whose `Ord` only `core` implements.
    let min = ord_call_func("<u32 as core::cmp::Ord>::min", U32, &[10]);
    assert_eq!(super::min_call_const_upper_bound(&min, 2), Some(10));
    assert!(super::local_is_min_max_result(&min, 2));
    assert!(!ord_dest_facts(&min, 2).is_empty(), "u32 min keeps its call-dest bound");
    let free_min = ord_call_func("core::cmp::min", U32, &[10]);
    assert_eq!(super::min_call_const_upper_bound(&free_min, 2), Some(10));
    let max = ord_call_func("<u32 as core::cmp::Ord>::max", U32, &[3]);
    assert_eq!(super::ret_call_const_lower_bound(&max, 2), Some(3));
    assert_eq!(super::cast_source_const_lower(&max, 2), Some(3));
    assert!(super::local_is_min_max_result(&max, 2));
    assert!(!ord_dest_facts(&max, 2).is_empty(), "u32 max keeps its call-dest bound");
    let clamp = ord_call_func("<u32 as core::cmp::Ord>::clamp", U32, &[1, 9]);
    assert_eq!(super::ret_call_const_lower_bound(&clamp, 2), Some(1));
    assert_eq!(super::cast_source_const_upper_nonneg(&clamp, 2), Some(9));
    assert!(!ord_dest_facts(&clamp, 2).is_empty(), "u32 clamp keeps its call-dest bound");
    let usize_min =
        ord_call_func("<usize as core::cmp::Ord>::min", Ty::PtrSizedInt { signed: false }, &[8]);
    assert_eq!(super::min_call_const_upper_bound(&usize_min, 2), Some(8));
}

#[test]
fn an_argument_of_another_type_refuses_the_fact() {
    // `Ord::min(self, other: Self) -> Self`: every argument IS `Self`. An extracted
    // call whose argument type differs from the destination is not a shape the
    // producer emits for a primitive impl, so it is refused rather than guessed.
    let mut min = ord_call_func("<u32 as core::cmp::Ord>::min", U32, &[10]);
    min.body.locals[1].ty = user_e();
    assert_eq!(super::min_call_const_upper_bound(&min, 2), None);
    assert!(!super::local_is_min_max_result(&min, 2));
    assert!(ord_dest_facts(&min, 2).is_empty(), "{:?}", ord_dest_facts(&min, 2));
}
