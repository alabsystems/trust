// Trust: the two GLOBAL-FACT RECOGNIZER gates that only an in-crate test can reach —
// `is_nonzero_get_call`'s definition-path match, and
// `checked_result_field0_consumer`'s uniqueness bail. Both are producers of facts
// that get conjoined into `vc.formula` before the whole-formula version rename, so a
// recognizer that matches the wrong callee, or a "the consumer" that is one of
// several, mints a fact about a value the program never computed.

use trust_types::VerifiableFunction;

use super::call_facts::is_nonzero_get_call;
use super::callee_summaries::build_nonzero_get_dest_facts;
use super::loop_bounds::{build_flattened_index_facts, checked_result_field0_consumer};
use super::value_facts::build_discriminant_variant_range_facts;

/// REAL compiler output. `-Ztrust-dump=mir` on
///
///   pub fn nz_cell(a: u32, c: &Cell<NonZeroU32>) -> u32 { let d = c.get(); a / d.get() }
///
/// emits TWO calls: `core::cell::Cell::<core::num::nonzero::NonZero<u32>>::get` into
/// the `NonZero`-typed `_3`, and the genuine
/// `core::num::nonzero::NonZero::<u32>::get` into the integer `_4`. The first satisfies
/// every conjunct of the pre-fix substring recognizer (`core::` root, a `::num::`
/// segment, a `NonZero` component, method tail `get`) purely through its GENERIC
/// ARGUMENT.
const MIR_NZ_CELL: &str = r#"{"name":"nz_cell","def_path":"f3::nz_cell","span":{"file":"f3.rs","line_start":3,"col_start":0,"line_end":6,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Int":{"width":32,"signed":false}},"name":null},{"index":1,"ty":{"Int":{"width":32,"signed":false}},"name":"a"},{"index":2,"ty":{"Ref":{"mutable":false,"inner":{"Adt":{"name":"core::cell::Cell","fields":[["value",{"Adt":{"name":"core::cell::UnsafeCell","fields":[["value",{"Adt":{"name":"core::num::nonzero::NonZero","fields":[["0",{"Adt":{"name":"core::num::niche_types::NonZeroU32Inner","fields":[["0",{"Int":{"width":32,"signed":false}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}}},"name":"c"},{"index":3,"ty":{"Adt":{"name":"core::num::nonzero::NonZero","fields":[["0",{"Adt":{"name":"core::num::niche_types::NonZeroU32Inner","fields":[["0",{"Int":{"width":32,"signed":false}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}},"name":null},{"index":4,"ty":{"Int":{"width":32,"signed":false}},"name":null},{"index":5,"ty":"Bool","name":null}],"blocks":[{"id":0,"stmts":[],"terminator":{"Call":{"func":"core::cell::Cell::<core::num::nonzero::NonZero<u32>>::get","args":[{"Move":{"local":2,"projections":[]}}],"dest":{"local":3,"projections":[]},"target":1,"span":{"file":"f3.rs","line_start":4,"col_start":14,"line_end":4,"col_end":14},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue"}}},{"id":1,"stmts":[],"terminator":{"Call":{"func":"core::num::nonzero::NonZero::<u32>::get","args":[{"Move":{"local":3,"projections":[]}}],"dest":{"local":4,"projections":[]},"target":2,"span":{"file":"f3.rs","line_start":5,"col_start":10,"line_end":5,"col_end":10},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue"}}},{"id":2,"stmts":[{"Assign":{"place":{"local":5,"projections":[]},"rvalue":{"BinaryOp":["Eq",{"Copy":{"local":4,"projections":[]}},{"Constant":{"Uint":[0,32]}}]},"span":{"file":"f3.rs","line_start":5,"col_start":4,"line_end":5,"col_end":4}}}],"terminator":{"Assert":{"cond":{"Move":{"local":5,"projections":[]}},"expected":false,"msg":"DivisionByZero","target":3,"span":{"file":"f3.rs","line_start":5,"col_start":4,"line_end":5,"col_end":4},"unwind":"Continue"}}},{"id":3,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"BinaryOp":["Div",{"Copy":{"local":1,"projections":[]}},{"Copy":{"local":4,"projections":[]}}]},"span":{"file":"f3.rs","line_start":5,"col_start":4,"line_end":5,"col_end":4}}}],"terminator":"Return"}],"arg_count":2,"return_ty":{"Int":{"width":32,"signed":false}}},"contracts":[],"preconditions":[{"And":[{"Ge":[{"Var":["a","Int"]},{"Int":0}]},{"Le":[{"Var":["a","Int"]},{"Int":4294967295}]}]}],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"#;

/// The callee string the extractor produced for `Cell::<NonZeroU32>::get`, verbatim.
const CELL_OF_NONZERO_GET: &str = "core::cell::Cell::<core::num::nonzero::NonZero<u32>>::get";
/// The callee string the extractor produced for the genuine accessor, verbatim.
const NONZERO_GET: &str = "core::num::nonzero::NonZero::<u32>::get";

/// A generic ARGUMENT must not satisfy an owner-path test. Erasing the balanced
/// `<…>` groups reduces this callee to `core::cell::Cell::get`, whose owner segment
/// is `Cell`.
///
/// Killed by mutant F3-SUBSTRING (`is_nonzero_get_call` returned to
/// `contains("::num::") && contains("NonZero") && method_tail == "get"`), under which
/// this callee matches.
#[test]
fn cell_of_nonzero_get_is_not_nonzero_get() {
    assert!(!is_nonzero_get_call(CELL_OF_NONZERO_GET));
}

/// The genuine accessor must STILL match — the tightening is a narrowing, and this is
/// the row that keeps it from narrowing to nothing. Killed by any mutant that makes
/// `is_nonzero_get_call` constantly false, and by an owner test that forgets the
/// middle turbofish (`NonZero::<u32>::get` leaves a `::::` seam once `<u32>` is
/// erased; without the seam collapse the owner segment reads as empty).
#[test]
fn the_genuine_nonzero_get_still_matches() {
    assert!(is_nonzero_get_call(NONZERO_GET));
    assert!(is_nonzero_get_call("std::num::nonzero::NonZero::<i8>::get"));
}

/// The two negative shapes the base's authority argument names, held here at the
/// recognizer rather than only at a verdict: a user crate root, and a longer tail.
#[test]
fn the_recognizer_keeps_its_crate_root_and_exact_tail() {
    assert!(!is_nonzero_get_call("mycrate::num::nonzero::NonZero::<u32>::get"));
    assert!(!is_nonzero_get_call("core::num::nonzero::NonZero::<u32>::get_unchecked"));
}

/// END TO END on the real capture: exactly ONE non-zero fact is minted for `nz_cell`,
/// and it is about the integer destination `_4` of the genuine accessor — never about
/// the `NonZero`-typed `_3` that `Cell::get` writes.
///
/// Killed by mutant F3-SUBSTRING **only in combination with** mutant NOTYPE (dropping
/// the integer-lowered-destination check): with the substring recognizer alone the
/// type check still rejects `_3`, so the count stays 1. NOTYPE is reported as a
/// SURVIVOR of this lane's mutant sweep — under the tightened recognizer every
/// callee that reaches the type check is a genuine `NonZero<T>::get`, whose return is
/// an integer for every `T`, so no faithful capture can distinguish the two. The
/// check stays as a fail-closed guard on `place_to_var_name`, not as a tested one.
#[test]
fn only_the_genuine_accessor_dest_gets_the_non_zero_fact() {
    let func: VerifiableFunction =
        serde_json::from_str(MIR_NZ_CELL).expect("the captured MIR fixture must deserialize");
    let facts = build_nonzero_get_dest_facts(&func);
    assert_eq!(facts.len(), 1, "one fact, for the genuine accessor only; got {facts:?}");
    let rendered = format!("{:?}", facts[0]);
    assert!(rendered.contains("\"_4\""), "the fact must bind the integer dest `_4`: {rendered}");
}

/// `checked_result_field0_consumer` says "the" consumer, so it must decline when
/// there is more than one. It previously returned the FIRST match, which is a
/// silently partial answer: `build_flattened_index_facts` would gate and bound one
/// index local while a second local reading the same `_t.0` got neither.
///
/// The fixture is `MIR_NZ_CELL`'s shape with a two-consumer body substituted, built
/// here rather than captured because rustc never emits two whole-local reads of one
/// checked-op field: this row pins the CONTRACT of the helper, not a compiler shape.
/// Killed by mutant F2-FIRSTMATCH (restoring the early `return Some(place.local)`).
#[test]
fn checked_result_field0_consumer_declines_when_not_unique() {
    let one: VerifiableFunction = serde_json::from_str(MIR_TWO_CONSUMERS_ONE)
        .expect("the single-consumer fixture must deserialize");
    assert_eq!(checked_result_field0_consumer(&one, 2), Some(3));
    let two: VerifiableFunction = serde_json::from_str(MIR_TWO_CONSUMERS_TWO)
        .expect("the two-consumer fixture must deserialize");
    assert_eq!(checked_result_field0_consumer(&two, 2), None);
}

/// `_3 = _2.0` — one whole-local consumer of the checked-op tuple `_2`.
const MIR_TWO_CONSUMERS_ONE: &str = r#"{"name":"one","def_path":"p::one","span":{"file":"p.rs","line_start":1,"col_start":0,"line_end":1,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":1,"ty":{"Int":{"width":64,"signed":false}},"name":"a"},{"index":2,"ty":{"Tuple":[{"Int":{"width":64,"signed":false}},"Bool"]},"name":null},{"index":3,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":4,"ty":{"Int":{"width":64,"signed":false}},"name":null}],"blocks":[{"id":0,"stmts":[{"Assign":{"place":{"local":2,"projections":[]},"rvalue":{"CheckedBinaryOp":["Add",{"Copy":{"local":1,"projections":[]}},{"Constant":{"Uint":[1,64]}}]},"span":{"file":"p.rs","line_start":1,"col_start":1,"line_end":1,"col_end":1}}},{"Assign":{"place":{"local":3,"projections":[]},"rvalue":{"Use":{"Copy":{"local":2,"projections":[{"Field":0}]}}},"span":{"file":"p.rs","line_start":1,"col_start":1,"line_end":1,"col_end":1}}},{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Copy":{"local":3,"projections":[]}}},"span":{"file":"p.rs","line_start":1,"col_start":1,"line_end":1,"col_end":1}}}],"terminator":"Return"}],"arg_count":1,"return_ty":{"Int":{"width":64,"signed":false}}},"contracts":[],"preconditions":[],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"#;

/// The same body with a SECOND whole-local consumer `_4 = _2.0` appended.
const MIR_TWO_CONSUMERS_TWO: &str = r#"{"name":"two","def_path":"p::two","span":{"file":"p.rs","line_start":1,"col_start":0,"line_end":1,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":1,"ty":{"Int":{"width":64,"signed":false}},"name":"a"},{"index":2,"ty":{"Tuple":[{"Int":{"width":64,"signed":false}},"Bool"]},"name":null},{"index":3,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":4,"ty":{"Int":{"width":64,"signed":false}},"name":null}],"blocks":[{"id":0,"stmts":[{"Assign":{"place":{"local":2,"projections":[]},"rvalue":{"CheckedBinaryOp":["Add",{"Copy":{"local":1,"projections":[]}},{"Constant":{"Uint":[1,64]}}]},"span":{"file":"p.rs","line_start":1,"col_start":1,"line_end":1,"col_end":1}}},{"Assign":{"place":{"local":3,"projections":[]},"rvalue":{"Use":{"Copy":{"local":2,"projections":[{"Field":0}]}}},"span":{"file":"p.rs","line_start":1,"col_start":1,"line_end":1,"col_end":1}}},{"Assign":{"place":{"local":4,"projections":[]},"rvalue":{"Use":{"Copy":{"local":2,"projections":[{"Field":0}]}}},"span":{"file":"p.rs","line_start":1,"col_start":1,"line_end":1,"col_end":1}}},{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Copy":{"local":3,"projections":[]}}},"span":{"file":"p.rs","line_start":1,"col_start":1,"line_end":1,"col_end":1}}}],"terminator":"Return"}],"arg_count":1,"return_ty":{"Int":{"width":64,"signed":false}}},"contracts":[],"preconditions":[],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"#;

/// `-Ztrust-dump` capture (PRISTINE 70a7534fd1 stage2) of
///
///   pub fn grid_plain(g: &[u8; 6]) -> u8 {
///       let mut s = 0u8;
///       for y in 0..2usize { for x in 0..3usize {
///           let i = y * 3 + x;
///           s = s.wrapping_add(g[i]); } }
///       s
///   }
///
/// The SAME capture the verdict-level rows in
/// `crates/trust-vcgen/tests/merged_local_vacuity.rs` use; it is here as well because
/// `build_flattened_index_facts` is `pub(super)` and only an in-crate row can count
/// the facts it emits, which is the only way to separate the two independent bounds.
/// Both copies must be updated together if the capture is ever re-taken.
const MIR_GRID_PLAIN: &str = r#"{"name":"grid_plain","def_path":"f2_ctl::grid_plain","span":{"file":"f2_ctl.rs","line_start":1,"col_start":0,"line_end":10,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Int":{"width":8,"signed":false}},"name":null},{"index":1,"ty":{"Ref":{"mutable":false,"inner":{"Array":{"elem":{"Int":{"width":8,"signed":false}},"len":6}}}},"name":"g"},{"index":2,"ty":{"Int":{"width":8,"signed":false}},"name":"s"},{"index":3,"ty":{"Adt":{"name":"core::ops::range::Range","fields":[["start",{"Int":{"width":64,"signed":false}}],["end",{"Int":{"width":64,"signed":false}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}},"name":null},{"index":4,"ty":{"Adt":{"name":"core::ops::range::Range","fields":[["start",{"Int":{"width":64,"signed":false}}],["end",{"Int":{"width":64,"signed":false}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}},"name":null},{"index":5,"ty":{"Adt":{"name":"core::ops::range::Range","fields":[["start",{"Int":{"width":64,"signed":false}}],["end",{"Int":{"width":64,"signed":false}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}},"name":"iter"},{"index":6,"ty":{"Adt":{"name":"core::option::Option","fields":[["__tag",{"Int":{"width":64,"signed":true}}],["__v1_0",{"Int":{"width":64,"signed":false}}]],"variants":[{"name":"None","discriminant":0,"fields":[]},{"name":"Some","discriminant":1,"fields":[["0",{"Int":{"width":64,"signed":false}}]]}],"disc_index_safe":true,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Enum"}},"name":null},{"index":7,"ty":{"Ref":{"mutable":true,"inner":{"Adt":{"name":"core::ops::range::Range","fields":[["start",{"Int":{"width":64,"signed":false}}],["end",{"Int":{"width":64,"signed":false}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}}},"name":null},{"index":8,"ty":{"Int":{"width":64,"signed":true}},"name":null},{"index":9,"ty":{"Int":{"width":64,"signed":false}},"name":"y"},{"index":10,"ty":{"Adt":{"name":"core::ops::range::Range","fields":[["start",{"Int":{"width":64,"signed":false}}],["end",{"Int":{"width":64,"signed":false}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}},"name":null},{"index":11,"ty":{"Adt":{"name":"core::ops::range::Range","fields":[["start",{"Int":{"width":64,"signed":false}}],["end",{"Int":{"width":64,"signed":false}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}},"name":null},{"index":12,"ty":{"Adt":{"name":"core::ops::range::Range","fields":[["start",{"Int":{"width":64,"signed":false}}],["end",{"Int":{"width":64,"signed":false}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}},"name":"iter"},{"index":13,"ty":{"Adt":{"name":"core::option::Option","fields":[["__tag",{"Int":{"width":64,"signed":true}}],["__v1_0",{"Int":{"width":64,"signed":false}}]],"variants":[{"name":"None","discriminant":0,"fields":[]},{"name":"Some","discriminant":1,"fields":[["0",{"Int":{"width":64,"signed":false}}]]}],"disc_index_safe":true,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Enum"}},"name":null},{"index":14,"ty":{"Ref":{"mutable":true,"inner":{"Adt":{"name":"core::ops::range::Range","fields":[["start",{"Int":{"width":64,"signed":false}}],["end",{"Int":{"width":64,"signed":false}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}}},"name":null},{"index":15,"ty":{"Int":{"width":64,"signed":true}},"name":null},{"index":16,"ty":{"Int":{"width":64,"signed":false}},"name":"x"},{"index":17,"ty":{"Int":{"width":64,"signed":false}},"name":"i"},{"index":18,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":19,"ty":{"Tuple":[{"Int":{"width":64,"signed":false}},"Bool"]},"name":null},{"index":20,"ty":{"Tuple":[{"Int":{"width":64,"signed":false}},"Bool"]},"name":null},{"index":21,"ty":{"Int":{"width":8,"signed":false}},"name":null},{"index":22,"ty":{"Int":{"width":8,"signed":false}},"name":null},{"index":23,"ty":{"Int":{"width":8,"signed":false}},"name":null},{"index":24,"ty":"Bool","name":null}],"blocks":[{"id":0,"stmts":[{"Assign":{"place":{"local":2,"projections":[]},"rvalue":{"Use":{"Constant":{"Uint":[0,8]}}},"span":{"file":"f2_ctl.rs","line_start":2,"col_start":16,"line_end":2,"col_end":19}}},{"Assign":{"place":{"local":4,"projections":[]},"rvalue":{"Aggregate":[{"Adt":{"name":"core::ops::range::Range","variant":0,"active_field":null,"args":"core::ops::range::Range<usize>"}},[{"Constant":{"Uint":[0,64]}},{"Constant":{"Uint":[2,64]}}]]},"span":{"file":"f2_ctl.rs","line_start":3,"col_start":13,"line_end":3,"col_end":22}}}],"terminator":{"Call":{"func":"<core::ops::range::Range<usize> as core::iter::traits::collect::IntoIterator>::into_iter","args":[{"Move":{"local":4,"projections":[]}}],"dest":{"local":3,"projections":[]},"target":1,"span":{"file":"f2_ctl.rs","line_start":3,"col_start":13,"line_end":3,"col_end":22},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue"}}},{"id":1,"stmts":[{"Assign":{"place":{"local":5,"projections":[]},"rvalue":{"Use":{"Move":{"local":3,"projections":[]}}},"span":{"file":"f2_ctl.rs","line_start":3,"col_start":13,"line_end":3,"col_end":22}}}],"terminator":{"Goto":2}},{"id":2,"stmts":[{"Assign":{"place":{"local":7,"projections":[]},"rvalue":{"Ref":{"mutable":true,"place":{"local":5,"projections":[]}}},"span":{"file":"f2_ctl.rs","line_start":3,"col_start":13,"line_end":3,"col_end":22}}}],"terminator":{"Call":{"func":"<core::ops::range::Range<usize> as core::iter::traits::iterator::Iterator>::next","args":[{"Copy":{"local":7,"projections":[]}}],"dest":{"local":6,"projections":[]},"target":3,"span":{"file":"f2_ctl.rs","line_start":3,"col_start":13,"line_end":3,"col_end":22},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue"}}},{"id":3,"stmts":[{"Assign":{"place":{"local":8,"projections":[]},"rvalue":{"Discriminant":{"local":6,"projections":[]}},"span":{"file":"f2_ctl.rs","line_start":3,"col_start":13,"line_end":3,"col_end":22}}}],"terminator":{"SwitchInt":{"discr":{"Move":{"local":8,"projections":[]}},"targets":[[0,6],[1,5]],"otherwise":4,"exhaustive_enum_unreachable":true,"span":{"file":"f2_ctl.rs","line_start":3,"col_start":13,"line_end":3,"col_end":22}}}},{"id":4,"stmts":[],"terminator":"Unreachable"},{"id":5,"stmts":[{"Assign":{"place":{"local":9,"projections":[]},"rvalue":{"Use":{"Copy":{"local":6,"projections":[{"Downcast":1},{"Field":0}]}}},"span":{"file":"f2_ctl.rs","line_start":3,"col_start":8,"line_end":3,"col_end":9}}},{"Assign":{"place":{"local":11,"projections":[]},"rvalue":{"Aggregate":[{"Adt":{"name":"core::ops::range::Range","variant":0,"active_field":null,"args":"core::ops::range::Range<usize>"}},[{"Constant":{"Uint":[0,64]}},{"Constant":{"Uint":[3,64]}}]]},"span":{"file":"f2_ctl.rs","line_start":4,"col_start":17,"line_end":4,"col_end":26}}}],"terminator":{"Call":{"func":"<core::ops::range::Range<usize> as core::iter::traits::collect::IntoIterator>::into_iter","args":[{"Move":{"local":11,"projections":[]}}],"dest":{"local":10,"projections":[]},"target":7,"span":{"file":"f2_ctl.rs","line_start":4,"col_start":17,"line_end":4,"col_end":26},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue"}}},{"id":6,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Copy":{"local":2,"projections":[]}}},"span":{"file":"f2_ctl.rs","line_start":9,"col_start":4,"line_end":9,"col_end":5}}}],"terminator":"Return"},{"id":7,"stmts":[{"Assign":{"place":{"local":12,"projections":[]},"rvalue":{"Use":{"Move":{"local":10,"projections":[]}}},"span":{"file":"f2_ctl.rs","line_start":4,"col_start":17,"line_end":4,"col_end":26}}}],"terminator":{"Goto":8}},{"id":8,"stmts":[{"Assign":{"place":{"local":14,"projections":[]},"rvalue":{"Ref":{"mutable":true,"place":{"local":12,"projections":[]}}},"span":{"file":"f2_ctl.rs","line_start":4,"col_start":17,"line_end":4,"col_end":26}}}],"terminator":{"Call":{"func":"<core::ops::range::Range<usize> as core::iter::traits::iterator::Iterator>::next","args":[{"Copy":{"local":14,"projections":[]}}],"dest":{"local":13,"projections":[]},"target":9,"span":{"file":"f2_ctl.rs","line_start":4,"col_start":17,"line_end":4,"col_end":26},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue"}}},{"id":9,"stmts":[{"Assign":{"place":{"local":15,"projections":[]},"rvalue":{"Discriminant":{"local":13,"projections":[]}},"span":{"file":"f2_ctl.rs","line_start":4,"col_start":17,"line_end":4,"col_end":26}}}],"terminator":{"SwitchInt":{"discr":{"Move":{"local":15,"projections":[]}},"targets":[[0,2],[1,10]],"otherwise":4,"exhaustive_enum_unreachable":true,"span":{"file":"f2_ctl.rs","line_start":4,"col_start":17,"line_end":4,"col_end":26}}}},{"id":10,"stmts":[{"Assign":{"place":{"local":16,"projections":[]},"rvalue":{"Use":{"Copy":{"local":13,"projections":[{"Downcast":1},{"Field":0}]}}},"span":{"file":"f2_ctl.rs","line_start":4,"col_start":12,"line_end":4,"col_end":13}}},{"Assign":{"place":{"local":19,"projections":[]},"rvalue":{"CheckedBinaryOp":["Mul",{"Copy":{"local":9,"projections":[]}},{"Constant":{"Uint":[3,64]}}]},"span":{"file":"f2_ctl.rs","line_start":5,"col_start":20,"line_end":5,"col_end":25}}}],"terminator":{"Assert":{"cond":{"Move":{"local":19,"projections":[{"Field":1}]}},"expected":false,"msg":{"Overflow":"Mul"},"target":11,"span":{"file":"f2_ctl.rs","line_start":5,"col_start":20,"line_end":5,"col_end":25},"unwind":"Continue"}}},{"id":11,"stmts":[{"Assign":{"place":{"local":18,"projections":[]},"rvalue":{"Use":{"Move":{"local":19,"projections":[{"Field":0}]}}},"span":{"file":"f2_ctl.rs","line_start":5,"col_start":20,"line_end":5,"col_end":25}}},{"Assign":{"place":{"local":20,"projections":[]},"rvalue":{"CheckedBinaryOp":["Add",{"Copy":{"local":18,"projections":[]}},{"Copy":{"local":16,"projections":[]}}]},"span":{"file":"f2_ctl.rs","line_start":5,"col_start":20,"line_end":5,"col_end":29}}}],"terminator":{"Assert":{"cond":{"Move":{"local":20,"projections":[{"Field":1}]}},"expected":false,"msg":{"Overflow":"Add"},"target":12,"span":{"file":"f2_ctl.rs","line_start":5,"col_start":20,"line_end":5,"col_end":29},"unwind":"Continue"}}},{"id":12,"stmts":[{"Assign":{"place":{"local":17,"projections":[]},"rvalue":{"Use":{"Move":{"local":20,"projections":[{"Field":0}]}}},"span":{"file":"f2_ctl.rs","line_start":5,"col_start":20,"line_end":5,"col_end":29}}},{"Assign":{"place":{"local":22,"projections":[]},"rvalue":{"Use":{"Copy":{"local":2,"projections":[]}}},"span":{"file":"f2_ctl.rs","line_start":6,"col_start":16,"line_end":6,"col_end":17}}},{"Assign":{"place":{"local":24,"projections":[]},"rvalue":{"BinaryOp":["Lt",{"Copy":{"local":17,"projections":[]}},{"Constant":{"Uint":[6,64]}}]},"span":{"file":"f2_ctl.rs","line_start":6,"col_start":31,"line_end":6,"col_end":35}}}],"terminator":{"Assert":{"cond":{"Move":{"local":24,"projections":[]}},"expected":true,"msg":"BoundsCheck","target":13,"span":{"file":"f2_ctl.rs","line_start":6,"col_start":31,"line_end":6,"col_end":35},"unwind":"Continue"}}},{"id":13,"stmts":[{"Assign":{"place":{"local":23,"projections":[]},"rvalue":{"Use":{"Copy":{"local":1,"projections":["Deref",{"Index":17}]}}},"span":{"file":"f2_ctl.rs","line_start":6,"col_start":31,"line_end":6,"col_end":35}}}],"terminator":{"Call":{"func":"@trust-rustc-total-primitive-method::core::num::<impl u8>::wrapping_add","args":[{"Move":{"local":22,"projections":[]}},{"Move":{"local":23,"projections":[]}}],"dest":{"local":21,"projections":[]},"target":14,"span":{"file":"f2_ctl.rs","line_start":6,"col_start":16,"line_end":6,"col_end":36},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue"}}},{"id":14,"stmts":[{"Assign":{"place":{"local":2,"projections":[]},"rvalue":{"Use":{"Move":{"local":21,"projections":[]}}},"span":{"file":"f2_ctl.rs","line_start":6,"col_start":12,"line_end":6,"col_end":36}}}],"terminator":{"Goto":8}}],"arg_count":1,"return_ty":{"Int":{"width":8,"signed":false}}},"contracts":[],"preconditions":[{"Or":[{"Eq":[{"Var":["_8","Int"]},{"Int":0}]},{"Eq":[{"Var":["_8","Int"]},{"Int":1}]}]},{"Or":[{"Eq":[{"Var":["_15","Int"]},{"Int":0}]},{"Eq":[{"Var":["_15","Int"]},{"Int":1}]}]}],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"#;

/// THE TWO INDEPENDENT BOUNDS, at the fact level — the pair the `facts.push` split is
/// about. `MIR_GRID_PLAIN` is a `for y in 0..2 { for x in 0..3 { … } }`, so the
/// producer mints the MUL-RESULT bound `_18 <= 3` and the FLATTENED-INDEX bound
/// `i <= 5`, and each stands on its own gate.
///
/// BOTH STAND ON THE SEAM'S OPEN DEFECT, and that is worth knowing here rather than
/// only at the arm: the `Iterator::next` desugar `&mut`-borrows BOTH range locals
/// (`_7 = &mut _5` in bb2, `_14 = &mut _12` in bb8), so the range-aggregate trace
/// resolves them only because `local_defs::unique_value_def` still admits the ESCAPE
/// channel. Refusing the alias there empties this row entirely — which is why the
/// repair has to move the iterator tracers onto an ORIGIN question instead. See
/// `body_unique_value_def`'s `Escape` arm.
#[test]
fn a_stable_flattened_index_emits_both_independent_bounds() {
    let func: VerifiableFunction =
        serde_json::from_str(MIR_GRID_PLAIN).expect("the captured MIR fixture must deserialize");
    let rendered: Vec<String> =
        build_flattened_index_facts(&func).iter().map(|f| format!("{f:?}")).collect();
    assert_eq!(
        rendered,
        vec![
            "Le(Var(\"_18\", Int), Int(3))".to_string(),
            "Le(Var(\"i\", Int), Int(5))".to_string()
        ],
        "the mul-result bound and the flattened-index bound are both minted"
    );
}

/// THE ROW THAT PINS THE FLATTENED-INDEX GATE, on the ESCAPE channel. `MIR_GRID_PLAIN`
/// with a `&mut` of the INDEX local `_17` (`i`) inserted right after its definition,
/// and a `&mut usize` local declared to receive it — the write channel a def-site scan
/// cannot see, because a later `*p = v` names `p` and not `i`.
///
/// The gate is `stable_checked_result_field0_consumer`, which for a non-parameter local
/// is `local_versions_collapse_to_bare` = `local_defs::is_single_static_assignment` —
/// the write-CHANNEL predicate, which disqualifies `LocalWrite::Escape`. Reading the
/// two definitions together is what makes this row worth having: `build_flattened_
/// index_facts` gates the index fact and NOT the mul-result fact, so only one of the
/// two bounds may move.
///
/// SYNTHESIZED, and deliberately so: this is the CONTRACT of the gate, not a compiler
/// shape — the same standing as the base's `MIR_NZ_REASSIGNED`. A verdict-level
/// assertion would not substitute: a withheld bound leaves the obligation
/// undischarged, which is a conservative loss and not a verdict this suite should
/// demand.
///
/// The row SEPARATES: the unedited capture emits BOTH bounds
/// (`a_stable_flattened_index_emits_both_independent_bounds`), and borrowing `_17`
/// must withhold `i <= 5` while leaving the mul-result bound `_18 <= 3` alone.
#[test]
fn a_borrow_of_the_flattened_index_withholds_the_index_bound() {
    let borrowed = MIR_GRID_PLAIN
        .replace(INDEX_DEF, &format!("{INDEX_DEF},{MUT_BORROW_OF_INDEX}"))
        .replace(LAST_LOCAL_DECL, &format!("{LAST_LOCAL_DECL},{BORROW_LOCAL_DECL}"));
    assert_ne!(borrowed, MIR_GRID_PLAIN, "both edits must land");
    let func: VerifiableFunction =
        serde_json::from_str(&borrowed).expect("the edited fixture must still deserialize");
    let rendered: Vec<String> =
        build_flattened_index_facts(&func).iter().map(|f| format!("{f:?}")).collect();
    assert!(
        !rendered.iter().any(|f| f.contains("\"i\"")),
        "the borrowed index may never carry a bound; got {rendered:?}"
    );
    assert_eq!(
        rendered,
        vec!["Le(Var(\"_18\", Int), Int(3))".to_string()],
        "and ONLY the index bound is withheld — the mul-result bound survives, which is \
         what makes this row separating"
    );
}

/// `_17 = move _20.0` — the flattened-index definition, verbatim from the capture.
const INDEX_DEF: &str = r#"{"Assign":{"place":{"local":17,"projections":[]},"rvalue":{"Use":{"Move":{"local":20,"projections":[{"Field":0}]}}},"span":{"file":"f2_ctl.rs","line_start":5,"col_start":20,"line_end":5,"col_end":29}}}"#;
/// `_25 = &mut _17`, spliced in after it.
const MUT_BORROW_OF_INDEX: &str = r#"{"Assign":{"place":{"local":25,"projections":[]},"rvalue":{"Ref":{"mutable":true,"place":{"local":17,"projections":[]}}},"span":{"file":"f2_ctl.rs","line_start":5,"col_start":20,"line_end":5,"col_end":29}}}"#;
/// The capture's last local declaration, verbatim, so the new one can follow it.
const LAST_LOCAL_DECL: &str = r#"{"index":24,"ty":"Bool","name":null}"#;
/// `_25: &mut usize`, the borrow's destination.
const BORROW_LOCAL_DECL: &str = r#"{"index":25,"ty":{"Ref":{"mutable":true,"inner":{"Int":{"width":64,"signed":false}}}},"name":null}"#;

/// SYNTHESIZED: `d = Discriminant(e)` on a two-variant enum, `d` bare. The producer
/// emits the fact twice — once over the canonical source-keyed discriminant name and
/// once over the DEST name `d`. `d` is `_3`, a TEMP: rustc gives every
/// `Rvalue::Discriminant` a fresh temp, and a PARAMETER destination would be
/// two-valued whatever its explicit def count (see `param_entry_gate_tests`).
const MIR_DISC_DEST_STABLE: &str = r#"{"name":"disc_stable","def_path":"p::disc_stable","span":{"file":"p.rs","line_start":1,"col_start":1,"line_end":1,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Int":{"width":64,"signed":true}},"name":null},{"index":1,"ty":{"Adt":{"name":"f1::E","fields":[["__tag",{"Int":{"width":64,"signed":true}}]],"variants":[{"name":"A","discriminant":0,"fields":[]},{"name":"B","discriminant":1,"fields":[]}],"disc_index_safe":true,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Enum"}},"name":"e"},{"index":2,"ty":{"Int":{"width":64,"signed":true}},"name":"b"},{"index":3,"ty":{"Int":{"width":64,"signed":true}},"name":"d"}],"blocks":[{"id":0,"stmts":[{"Assign":{"place":{"local":3,"projections":[]},"rvalue":{"Discriminant":{"local":1,"projections":[]}},"span":{"file":"p.rs","line_start":1,"col_start":1,"line_end":1,"col_end":1}}},{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Copy":{"local":3,"projections":[]}}},"span":{"file":"p.rs","line_start":1,"col_start":1,"line_end":1,"col_end":1}}}],"terminator":"Return"}],"arg_count":2,"return_ty":{"Int":{"width":64,"signed":true}}},"contracts":[],"preconditions":[],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"#;

/// The same body with a SECOND definition of the `Discriminant` destination
/// (`d = copy b`) appended. rustc gives a `Discriminant` read its own fresh temp, so
/// no capture of this shape exists; the row pins the gate's CONTRACT.
const MIR_DISC_DEST_MERGED: &str = r#"{"name":"disc_merged","def_path":"p::disc_merged","span":{"file":"p.rs","line_start":1,"col_start":1,"line_end":1,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Int":{"width":64,"signed":true}},"name":null},{"index":1,"ty":{"Adt":{"name":"f1::E","fields":[["__tag",{"Int":{"width":64,"signed":true}}]],"variants":[{"name":"A","discriminant":0,"fields":[]},{"name":"B","discriminant":1,"fields":[]}],"disc_index_safe":true,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Enum"}},"name":"e"},{"index":2,"ty":{"Int":{"width":64,"signed":true}},"name":"b"},{"index":3,"ty":{"Int":{"width":64,"signed":true}},"name":"d"}],"blocks":[{"id":0,"stmts":[{"Assign":{"place":{"local":3,"projections":[]},"rvalue":{"Discriminant":{"local":1,"projections":[]}},"span":{"file":"p.rs","line_start":1,"col_start":1,"line_end":1,"col_end":1}}},{"Assign":{"place":{"local":3,"projections":[]},"rvalue":{"Use":{"Copy":{"local":2,"projections":[]}}},"span":{"file":"p.rs","line_start":1,"col_start":1,"line_end":1,"col_end":1}}},{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Copy":{"local":3,"projections":[]}}},"span":{"file":"p.rs","line_start":1,"col_start":1,"line_end":1,"col_end":1}}}],"terminator":"Return"}],"arg_count":2,"return_ty":{"Int":{"width":64,"signed":true}}},"contracts":[],"preconditions":[],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"#;

/// A REDEFINED `Discriminant` destination must lose the tag-set fact — a value it can
/// hold has no reason to be a variant tag. The SOURCE-keyed name keeps its fact
/// unconditionally: it denotes `e`'s discriminant, and every value `e` can hold is an
/// inhabitant of the same enum.
///
/// Killed by mutant F1-DESTGATE-DROP (pushing the dest name unconditionally), which is
/// otherwise a SURVIVOR of every other row in this lane and of the whole
/// `trust-vcgen` suite.
#[test]
fn a_redefined_discriminant_dest_loses_its_tag_fact() {
    let stable: VerifiableFunction = serde_json::from_str(MIR_DISC_DEST_STABLE)
        .expect("the stable-dest fixture must deserialize");
    let merged: VerifiableFunction = serde_json::from_str(MIR_DISC_DEST_MERGED)
        .expect("the merged-dest fixture must deserialize");
    let names = |f: &VerifiableFunction| -> Vec<String> {
        build_discriminant_variant_range_facts(f).iter().map(|x| format!("{x:?}")).collect()
    };
    let stable_names = names(&stable);
    assert_eq!(stable_names.len(), 2, "source-keyed name AND dest name: {stable_names:?}");
    assert!(
        stable_names.iter().any(|f| f.contains("\"d\"")),
        "the bare dest carries the fact: {stable_names:?}"
    );
    let merged_names = names(&merged);
    assert_eq!(merged_names.len(), 1, "source-keyed name only: {merged_names:?}");
    assert!(
        !merged_names[0].contains("\"d\""),
        "the redefined dest must NOT carry it: {merged_names:?}"
    );
}
