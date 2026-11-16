//! Unit tests for the drop-initialization join, effect-conservation matcher, trust-ir census and
//! sidecar. The MIR census and the finalize wiring need a `TyCtxt` and are pinned end to end instead
//! (`tests/ui/trust/trust_ir_effect_conservation_*.rs`,
//! `tests/run-make/trust-effect-conservation`).

use std::collections::{BTreeMap, BTreeSet};

use rustc_span::DUMMY_SP;
use rustc_span::def_id::{DefId, DefIndex, LOCAL_CRATE};
use trust_ir::value::GlobalId;
use trust_ir::{
    Block, BlockId, FieldDef, FuncId, FuncTy, Function, Inst, InstrNode, Module, ProofAnnotation,
    StructDef, StructId, StructRepr, Ty, ValueId,
};

use super::*;

fn init_state(maybe_init: &[u32], moved_fields: &[(u32, u32)]) -> InitState {
    InitState {
        maybe_init: maybe_init.iter().copied().map(Local::from_u32).collect(),
        moved_fields: moved_fields
            .iter()
            .map(|&(local, field)| (Local::from_u32(local), field))
            .collect(),
    }
}

#[test]
fn init_state_join_keeps_equal_and_subsumed_facts_unchanged() {
    let state = init_state(&[1, 2], &[(1, 0)]);
    for other in [state.clone(), init_state(&[1], &[(1, 0), (1, 1)])] {
        let mut joined = state.clone();
        assert!(!joined.join(&other));
        assert_eq!(joined, state);
    }
    let mut empty = InitState::default();
    assert!(!empty.join(&InitState::default()));
    assert_eq!(empty, InitState::default());
}

#[test]
fn init_state_join_reports_either_set_changing_and_then_is_idempotent() {
    for (mut state, other, expected) in [
        // Only the may set grows.
        (
            init_state(&[1], &[(1, 0)]),
            init_state(&[1, 2], &[(1, 0)]),
            init_state(&[1, 2], &[(1, 0)]),
        ),
        // Only the must set shrinks.
        (
            init_state(&[1, 2], &[(1, 0), (2, 0)]),
            init_state(&[1, 2], &[(2, 0)]),
            init_state(&[1, 2], &[(2, 0)]),
        ),
        // An initially empty must set cannot acquire the other path's moved field.
        (init_state(&[], &[]), init_state(&[1], &[(1, 0)]), init_state(&[1], &[])),
        // An empty incoming must set removes every definitely moved field.
        (init_state(&[1], &[(1, 0)]), init_state(&[], &[]), init_state(&[1], &[])),
    ] {
        let other_before = other.clone();
        assert!(state.join(&other));
        assert_eq!(state, expected);
        assert_eq!(other, other_before);
        assert!(!state.join(&other));
        assert_eq!(state, expected);
    }
}

#[test]
fn init_state_join_detects_equal_sized_disjoint_and_overlapping_inputs() {
    for (mut state, other, expected) in [
        // Equal input sizes do not mean equal memberships. May growth and must
        // shrinkage cancel in the total cardinality in both of these joins.
        (init_state(&[1], &[(1, 0)]), init_state(&[2], &[(2, 0)]), init_state(&[1, 2], &[])),
        (
            init_state(&[1, 2], &[(1, 0), (2, 0)]),
            init_state(&[2, 3], &[(2, 0), (3, 0)]),
            init_state(&[1, 2, 3], &[(2, 0)]),
        ),
    ] {
        let before_total = state.maybe_init.len() + state.moved_fields.len();
        assert!(state.join(&other));
        assert_eq!(state, expected);
        assert_eq!(state.maybe_init.len() + state.moved_fields.len(), before_total);
        assert!(!state.join(&other));
        assert_eq!(state, expected);
    }
}

fn def(i: u32) -> DefId {
    DefId { krate: LOCAL_CRATE, index: DefIndex::from_u32(i) }
}

fn call(ids: &[u32]) -> MirEffect {
    MirEffect {
        kind: MirEffectKind::Call {
            ids: ids.iter().map(|i| def(*i)).collect(),
            site_args: None,
            equivalence: None,
            enum_result: false,
            enum_args: Vec::new(),
        },
        span: DUMMY_SP,
    }
}

fn mir(effects: Vec<MirEffect>, arg_count: u32) -> MirCensus {
    MirCensus {
        effects,
        arg_count,
        arg_enum: Vec::new(),
        ret_enum: false,
        store_values: Vec::new(),
        enum_types: BTreeSet::new(),
        ..MirCensus::default()
    }
}

fn ir(effects: Vec<IrEffectKind>, param_count: u32) -> IrCensus {
    IrCensus { effects, param_count, ..IrCensus::default() }
}

fn eff(kind: MirEffectKind) -> MirEffect {
    MirEffect { kind, span: DUMMY_SP }
}

fn kinds(u: &[Unpaired]) -> Vec<TagKind> {
    u.iter().map(|u| u.kind).collect()
}

/// The wave-ER / field-store-RHS failure: MIR calls `close`, the spliced trust-ir does not.
#[test]
fn a_dropped_call_is_not_conserved() {
    let m = mir(vec![call(&[7])], 1);
    let got = unpaired_effects(&m, &ir(vec![], 1));
    assert_eq!(kinds(&got), vec![TagKind::NotConserved(Effect::Call)]);
    assert_eq!(got[0].mir_index, 0);
}

#[test]
fn a_call_pairs_by_ledger_identity_and_only_by_it() {
    let m = mir(vec![call(&[7])], 0);
    // The ledger records (site, resolved); either one pairs.
    assert!(
        unpaired_effects(
            &m,
            &ir(
                vec![IrEffectKind::Call {
                    ids: vec![def(7), def(9)],
                    site: None,
                    placeholder_result: false,
                    placeholder_params: Vec::new()
                }],
                0
            )
        )
        .is_empty()
    );
    assert!(
        unpaired_effects(
            &m,
            &ir(
                vec![IrEffectKind::Call {
                    ids: vec![def(3), def(7)],
                    site: None,
                    placeholder_result: false,
                    placeholder_params: Vec::new()
                }],
                0
            )
        )
        .is_empty()
    );
    // A call to something else does not pair, nor does an unledgered call.
    let other = ir(
        vec![
            IrEffectKind::Call {
                ids: vec![def(8)],
                site: None,
                placeholder_result: false,
                placeholder_params: Vec::new(),
            },
            IrEffectKind::UnledgeredCall,
        ],
        0,
    );
    assert_eq!(kinds(&unpaired_effects(&m, &other)), vec![TagKind::NotConserved(Effect::Call)]);
}

/// Multiplicity: two `close` calls in MIR need two in trust-ir.
#[test]
fn calls_pair_one_to_one() {
    let m = mir(vec![call(&[7]), call(&[7])], 0);
    let one = ir(
        vec![IrEffectKind::Call {
            ids: vec![def(7)],
            site: None,
            placeholder_result: false,
            placeholder_params: Vec::new(),
        }],
        0,
    );
    let got = unpaired_effects(&m, &one);
    assert_eq!(kinds(&got), vec![TagKind::NotConserved(Effect::Call)]);
    assert_eq!(got[0].mir_index, 1);
    let two = ir(
        vec![
            IrEffectKind::Call {
                ids: vec![def(7)],
                site: None,
                placeholder_result: false,
                placeholder_params: Vec::new()
            };
            2
        ],
        0,
    );
    assert!(unpaired_effects(&m, &two).is_empty());
}

/// Pairing is a MAXIMUM matching, not first-fit: a MIR call admitting two identities must not
/// take the only trust-ir call another MIR call could pair with.
#[test]
fn call_pairing_is_a_maximum_matching() {
    // MIR: B = {Fn::call (100), closure (42)} first, then A = {closure (42)}.
    // trust-ir: a call to 42 and a call to 100. First-fit would give B the 42 and leave A bare.
    let m = mir(vec![call(&[100, 42]), call(&[42])], 0);
    let irs = ir(
        vec![
            IrEffectKind::Call {
                ids: vec![def(42)],
                site: None,
                placeholder_result: false,
                placeholder_params: Vec::new(),
            },
            IrEffectKind::Call {
                ids: vec![def(100)],
                site: None,
                placeholder_result: false,
                placeholder_params: Vec::new(),
            },
        ],
        0,
    );
    assert!(unpaired_effects(&m, &irs).is_empty());
}

/// `f()` on a closure is `<{closure} as Fn>::call` in MIR; the producer calls the closure.
#[test]
fn a_fn_trait_call_pairs_through_its_closure() {
    let m = mir(vec![call(&[100, 42])], 0);
    assert!(
        unpaired_effects(
            &m,
            &ir(
                vec![IrEffectKind::Call {
                    ids: vec![def(42)],
                    site: None,
                    placeholder_result: false,
                    placeholder_params: Vec::new()
                }],
                0
            )
        )
        .is_empty()
    );
}

/// An audited equivalence may stay unpaired; nothing else may.
#[test]
fn only_an_audited_equivalence_stays_unpaired() {
    let pure = MirEffect {
        kind: MirEffectKind::Call {
            ids: vec![def(5)],
            site_args: None,
            equivalence: Some(Equivalence::RangeNext),
            enum_result: false,
            enum_args: Vec::new(),
        },
        span: DUMMY_SP,
    };
    assert!(unpaired_effects(&mir(vec![pure.clone()], 0), &ir(vec![], 0)).is_empty());
    // And it still pairs (by identity) when the trust-ir does carry the call.
    let carried = ir(
        vec![IrEffectKind::Call {
            ids: vec![def(5)],
            site: None,
            placeholder_result: false,
            placeholder_params: Vec::new(),
        }],
        0,
    );
    assert!(unpaired_effects(&mir(vec![pure], 0), &carried).is_empty());
}

#[test]
fn indirect_calls_pair_with_indirect_or_unledgered_calls() {
    let m = mir(vec![eff(MirEffectKind::IndirectCall), eff(MirEffectKind::IndirectCall)], 0);
    let both = ir(vec![IrEffectKind::UnledgeredCall, IrEffectKind::IndirectCall], 0);
    assert!(unpaired_effects(&m, &both).is_empty());
    // A ledgered direct call to a known callee is not an indirect call.
    let direct = ir(
        vec![
            IrEffectKind::IndirectCall,
            IrEffectKind::Call {
                ids: vec![def(1)],
                site: None,
                placeholder_result: false,
                placeholder_params: Vec::new(),
            },
        ],
        0,
    );
    assert_eq!(
        kinds(&unpaired_effects(&m, &direct)),
        vec![TagKind::NotConserved(Effect::IndirectCall)]
    );
}

#[test]
fn stores_pair_by_root() {
    let st = |r| eff(MirEffectKind::Store(r));
    // Through argument 0 needs a store through parameter 0 when the counts agree.
    let m = mir(vec![st(MemRoot::Arg(0))], 2);
    let wrong_param = ir(vec![IrEffectKind::Store(IrRoot::Arg(1))], 2);
    assert_eq!(
        kinds(&unpaired_effects(&m, &wrong_param)),
        vec![TagKind::NotConserved(Effect::Store)]
    );
    assert!(unpaired_effects(&m, &ir(vec![IrEffectKind::Store(IrRoot::Arg(0))], 2)).is_empty());
    // Parameter counts differ (a spread or an elided ZST parameter): parameters pool.
    assert!(unpaired_effects(&m, &ir(vec![IrEffectKind::Store(IrRoot::Arg(1))], 3)).is_empty());
    // A store to the body's own alloca never covers an escaping store.
    let local = ir(vec![IrEffectKind::Store(IrRoot::Local)], 2);
    assert_eq!(kinds(&unpaired_effects(&m, &local)), vec![TagKind::NotConserved(Effect::Store)]);
    // A static pairs with a global or a loaded pointer, never with a parameter.
    let s = mir(vec![st(MemRoot::Static)], 1);
    assert!(unpaired_effects(&s, &ir(vec![IrEffectKind::Store(IrRoot::Global)], 1)).is_empty());
    assert!(unpaired_effects(&s, &ir(vec![IrEffectKind::Store(IrRoot::Indirect)], 1)).is_empty());
    assert_eq!(
        kinds(&unpaired_effects(&s, &ir(vec![IrEffectKind::Store(IrRoot::Arg(0))], 1))),
        vec![TagKind::NotConserved(Effect::Store)]
    );
}

/// `guard_scope`: MIR drops a `Guard` whose `Drop` closes a descriptor; trust-ir has no drop.
#[test]
fn an_elided_drop_is_an_abstraction() {
    let m = mir(vec![eff(MirEffectKind::Drop { destructor: false })], 1);
    assert_eq!(kinds(&unpaired_effects(&m, &ir(vec![], 1))), vec![TagKind::Abstracted(Lane::Drop)]);
    assert!(unpaired_effects(&m, &ir(vec![IrEffectKind::Drop], 1)).is_empty());
}

#[test]
fn asm_and_yield_pair_by_count() {
    let m =
        mir(vec![eff(MirEffectKind::Asm { empty_noreturn: false }), eff(MirEffectKind::Yield)], 0);
    assert_eq!(
        kinds(&unpaired_effects(&m, &ir(vec![], 0))),
        vec![TagKind::NotConserved(Effect::Asm), TagKind::NotConserved(Effect::Yield)]
    );
    assert!(
        unpaired_effects(&m, &ir(vec![IrEffectKind::Asm, IrEffectKind::Suspend], 0)).is_empty()
    );
}

/// An `asm!("", options(noreturn))` (no template, no operand) is UB to reach and emits nothing;
/// the producer's `unreachable` for it loses no effect. Any other asm must be paired.
#[test]
fn only_an_empty_noreturn_asm_may_stay_unpaired() {
    let empty = mir(vec![eff(MirEffectKind::Asm { empty_noreturn: true })], 0);
    assert!(unpaired_effects(&empty, &ir(vec![], 0)).is_empty());
    let real = mir(vec![eff(MirEffectKind::Asm { empty_noreturn: false })], 0);
    assert_eq!(
        kinds(&unpaired_effects(&real, &ir(vec![], 0))),
        vec![TagKind::NotConserved(Effect::Asm)]
    );
}

/// Extra trust-ir effects are the differentials' business, not this gate's.
#[test]
fn extra_trust_ir_effects_are_not_a_mismatch() {
    let extra = ir(
        vec![
            IrEffectKind::Call {
                ids: vec![def(1)],
                site: None,
                placeholder_result: false,
                placeholder_params: Vec::new(),
            },
            IrEffectKind::Store(IrRoot::Arg(0)),
        ],
        1,
    );
    assert!(unpaired_effects(&mir(vec![], 1), &extra).is_empty());
}

fn site_call(id: u32, args: Vec<SiteArg>, equivalence: Option<Equivalence>) -> MirEffect {
    MirEffect {
        kind: MirEffectKind::Call {
            ids: vec![def(id)],
            site_args: Some(args),
            equivalence,
            enum_result: false,
            enum_args: Vec::new(),
        },
        span: DUMMY_SP,
    }
}

fn ir_site_call(ids: &[u32], site: Option<(u32, Vec<SiteArg>)>) -> IrEffectKind {
    IrEffectKind::Call {
        ids: ids.iter().map(|i| def(*i)).collect(),
        site: site.map(|(d, a)| (def(d), a)),
        placeholder_result: false,
        placeholder_params: Vec::new(),
    }
}

fn foo_ty() -> SiteArg {
    SiteArg::Ty(crate::SiteTy::Adt(def(50), Vec::new()))
}

fn str_ty() -> SiteArg {
    SiteArg::Ty(crate::SiteTy::Str)
}

/// Review finding 2 (2026-10-01): a trait method's `FnDef` is shared by every impl, so pairing on
/// it alone let an exempt `<str as PartialEq>::eq` trust-ir call stand for a LOST user
/// `<Foo as PartialEq>::eq`. With the receiver in the site args, the user call stays unpaired.
#[test]
fn a_trait_call_pairs_only_at_its_own_receiver() {
    const EQ: u32 = 20;
    let m = mir(
        vec![
            site_call(EQ, vec![foo_ty(), foo_ty()], None),
            site_call(EQ, vec![str_ty(), str_ty()], Some(Equivalence::BuiltinEq)),
        ],
        0,
    );
    // The trust-ir carries only the `str` comparison: the user `eq` (and its `close`) is lost.
    let only_str = ir(vec![ir_site_call(&[EQ, 99], Some((EQ, vec![str_ty(), str_ty()])))], 0);
    let got = unpaired_effects(&m, &only_str);
    assert_eq!(kinds(&got), vec![TagKind::NotConserved(Effect::Call)]);
    assert_eq!(got[0].mir_index, 0);
    // Both carried: conserved, whichever order the trust-ir lists them in.
    for irs in [
        vec![
            ir_site_call(&[EQ, 51], Some((EQ, vec![foo_ty(), foo_ty()]))),
            ir_site_call(&[EQ, 99], Some((EQ, vec![str_ty(), str_ty()]))),
        ],
        vec![
            ir_site_call(&[EQ, 99], Some((EQ, vec![str_ty(), str_ty()]))),
            ir_site_call(&[EQ, 51], Some((EQ, vec![foo_ty(), foo_ty()]))),
        ],
    ] {
        assert!(unpaired_effects(&m, &ir(irs, 0)).is_empty());
    }
    // The user call alone (the `str` comparison lowered byte-wise): conserved.
    let only_foo = ir(vec![ir_site_call(&[EQ, 51], Some((EQ, vec![foo_ty(), foo_ty()])))], 0);
    assert!(unpaired_effects(&m, &only_foo).is_empty());
}

/// Review finding 2's false REFUSALS (`str_then_user`, `range_then_user`): an exempt call listed
/// FIRST in MIR must not take the only trust-ir call an effectful call can pair with, even where
/// identities are compared by `DefId` alone (a site the producer recorded without args).
#[test]
fn effectful_calls_are_matched_before_exempt_ones() {
    const NEXT: u32 = 30;
    let mut exempt = call(&[NEXT]);
    if let MirEffectKind::Call { equivalence, .. } = &mut exempt.kind {
        *equivalence = Some(Equivalence::RangeNext);
    }
    let m = mir(vec![exempt, call(&[NEXT])], 0);
    let one = ir(vec![ir_site_call(&[NEXT], None)], 0);
    assert!(unpaired_effects(&m, &one).is_empty());
    // And without the trust-ir call the effectful one is the one reported.
    let got = unpaired_effects(&m, &ir(vec![], 0));
    assert_eq!(kinds(&got), vec![TagKind::NotConserved(Effect::Call)]);
    assert_eq!(got[0].mir_index, 1);
}

/// A generic site (args the encoder cannot spell) still pairs by `DefId`.
#[test]
fn an_unspellable_site_pairs_by_def_id() {
    let m = mir(vec![call(&[40])], 0);
    let spelled = ir(vec![ir_site_call(&[40], Some((40, vec![foo_ty()])))], 0);
    assert!(unpaired_effects(&m, &spelled).is_empty());
    let mut m2 = mir(vec![site_call(40, vec![foo_ty()], None)], 0);
    assert!(unpaired_effects(&m2, &ir(vec![ir_site_call(&[40], None)], 0)).is_empty());
    // Two spelled sites of different `FnDef`s do not pair through the resolved id …
    m2.effects[0] = site_call(41, vec![foo_ty()], None);
    let other = ir(vec![ir_site_call(&[40, 41], Some((40, vec![foo_ty()])))], 0);
    assert_eq!(kinds(&unpaired_effects(&m2, &other)), vec![TagKind::NotConserved(Effect::Call)]);
    // … except through the closure a `Fn*` call carries.
    if let MirEffectKind::Call { ids, .. } = &mut m2.effects[0].kind {
        ids.push(def(40));
    }
    assert!(unpaired_effects(&m2, &other).is_empty());
}

/// Review finding 1 (2026-10-01): a panic check the producer dropped (the division in an opaque
/// `Option` payload under the field-store mutation) passed the gate, and trust-cg compiled the
/// body: the linked binary returned where the program must panic. Checks pair within their class.
#[test]
fn a_lost_panic_check_is_not_conserved() {
    let m = mir(vec![eff(MirEffectKind::Assert(AssertClass::DivZero))], 2);
    assert_eq!(
        kinds(&unpaired_effects(&m, &ir(vec![], 2))),
        vec![TagKind::NotConserved(Effect::Assert)]
    );
    assert!(
        unpaired_effects(&m, &ir(vec![IrEffectKind::Assert(AssertClass::DivZero)], 2)).is_empty()
    );
    // A check of another class does not stand in for it.
    assert_eq!(
        kinds(&unpaired_effects(&m, &ir(vec![IrEffectKind::Assert(AssertClass::Bounds)], 2))),
        vec![TagKind::NotConserved(Effect::Assert)]
    );
    // Multiplicity: two overflow checks need two.
    let two = mir(
        vec![
            eff(MirEffectKind::Assert(AssertClass::Overflow)),
            eff(MirEffectKind::Assert(AssertClass::Overflow)),
        ],
        0,
    );
    let got = unpaired_effects(&two, &ir(vec![IrEffectKind::Assert(AssertClass::Overflow)], 0));
    assert_eq!(kinds(&got), vec![TagKind::NotConserved(Effect::Assert)]);
}

/// Review finding 7 (2026-10-01): an elided drop whose glue runs a destructor (a lock guard's
/// unlock, an fd's close) is tagged `destructor` beside `drop`, so a reader that accepts only the
/// memory-release lane refuses it.
#[test]
fn an_elided_destructor_is_tagged_beside_the_drop() {
    let m = mir(vec![eff(MirEffectKind::Drop { destructor: true })], 1);
    assert_eq!(
        kinds(&unpaired_effects(&m, &ir(vec![], 1))),
        vec![TagKind::Abstracted(Lane::Drop), TagKind::Abstracted(Lane::Destructor)]
    );
    assert!(unpaired_effects(&m, &ir(vec![IrEffectKind::Drop], 1)).is_empty());
    let memory = mir(vec![eff(MirEffectKind::Drop { destructor: false })], 1);
    assert_eq!(
        kinds(&unpaired_effects(&memory, &ir(vec![], 1))),
        vec![TagKind::Abstracted(Lane::Drop)]
    );
    // Which drop is missing is unknown: one of two missing, one a destructor — tagged.
    let mixed = mir(
        vec![
            eff(MirEffectKind::Drop { destructor: false }),
            eff(MirEffectKind::Drop { destructor: true }),
        ],
        1,
    );
    assert_eq!(
        kinds(&unpaired_effects(&mixed, &ir(vec![IrEffectKind::Drop], 1))),
        vec![TagKind::Abstracted(Lane::Drop), TagKind::Abstracted(Lane::Destructor)]
    );
}

/// Review finding 3 (2026-10-01): an enum the body holds by value that the producer collapses
/// to a placeholder is the opaque lane wherever it sits (a tuple, a struct literal, a slot).
#[test]
fn a_collapsed_enum_held_by_value_is_the_opaque_lane() {
    let a = Abstractions { collapsed_enum_values: 1, ..Abstractions::default() };
    assert_eq!(abstraction_kinds(&a), vec![TagKind::Abstracted(Lane::OpaqueLane)]);
    assert!(abstraction_kinds(&Abstractions::default()).is_empty());
}

/// Review finding 6 (2026-10-01): `BuiltinEq` read only `Self`, so a user
/// `impl PartialEq<Foo> for u32` (or `for str`), whose `eq` closes a descriptor, was classed as
/// the effect-free std comparison. Both sides must be the same builtin type.
#[test]
fn builtin_eq_needs_its_own_type_on_both_sides() {
    use crate::SiteTy;
    let u32_ty = SiteTy::Uint(rustc_middle::ty::UintTy::U32);
    let foo = SiteTy::Adt(def(50), Vec::new());
    assert!(is_builtin_eq(&u32_ty, &u32_ty));
    assert!(is_builtin_eq(&SiteTy::Str, &SiteTy::Str));
    assert!(is_builtin_eq(&SiteTy::Tuple(Vec::new()), &SiteTy::Tuple(Vec::new())));
    let slice = SiteTy::Slice(Box::new(u32_ty.clone()));
    assert!(is_builtin_eq(&slice, &slice));
    // A user impl with a builtin `Self` is user code.
    assert!(!is_builtin_eq(&u32_ty, &foo));
    assert!(!is_builtin_eq(&SiteTy::Str, &foo));
    // A user type on the left is never builtin; nor a slice of `str`.
    assert!(!is_builtin_eq(&foo, &foo));
    let strs = SiteTy::Slice(Box::new(SiteTy::Str));
    assert!(!is_builtin_eq(&strs, &strs));
}

// ---- the trust-ir census -------------------------------------------------------------------

fn v(i: u32) -> ValueId {
    ValueId::new(i)
}

fn node(inst: Inst) -> InstrNode {
    InstrNode::new(inst)
}

fn node_r(inst: Inst, r: u32) -> InstrNode {
    InstrNode::new(inst).with_result(v(r))
}

/// A module with one function of the given blocks; block 0 is the entry with `params` pointer
/// parameters (`%0..`).
fn module_with(params: u32, blocks: Vec<Block>, structs: Vec<StructDef>) -> Module {
    let mut module = Module::new("census");
    let ty = module
        .add_func_type(FuncTy {
            params: (0..params).map(|_| Ty::Ptr).collect(),
            returns: Vec::new(),
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "body", ty, BlockId::new(0));
    f.blocks = blocks;
    module.functions.push(f);
    module.structs = structs;
    module
}

fn entry(params: u32, body: Vec<InstrNode>) -> Block {
    let mut b = Block::new(BlockId::new(0));
    for i in 0..params {
        b = b.with_param(v(i), Ty::Ptr);
    }
    b.body = body;
    b
}

fn ret() -> InstrNode {
    node(Inst::Return { values: Vec::new() })
}

fn store(ptr: u32, value: u32) -> InstrNode {
    node(Inst::Store { ty: Ty::I32, ptr: v(ptr), value: v(value), volatile: false, align: None })
}

#[test]
fn store_roots_follow_the_pointer() {
    // %0 param; %1 = gep %0; %2 = alloca; %3 = load ptr %0; %4 = globaladdr; %5 = const
    let body = vec![
        node_r(Inst::GEP { pointee_ty: Ty::I32, base: v(0), indices: vec![], inbounds: true }, 1),
        node_r(Inst::Alloca { ty: Ty::I32, count: None, align: None }, 2),
        node_r(Inst::Load { ty: Ty::Ptr, ptr: v(0), volatile: false, align: None }, 3),
        node_r(Inst::GlobalAddr { global: GlobalId::new(0) }, 4),
        store(1, 9),
        store(2, 9),
        store(3, 9),
        store(4, 9),
        ret(),
    ];
    let m = module_with(1, vec![entry(1, body)], vec![]);
    let c = ir_census(
        &m,
        &m.functions[0],
        &BTreeMap::new(),
        &BTreeMap::new(),
        &BTreeSet::new(),
        LedgeredLanes::default(),
    );
    assert_eq!(
        c.effects,
        vec![
            IrEffectKind::Store(IrRoot::Arg(0)),
            IrEffectKind::Store(IrRoot::Local),
            IrEffectKind::Store(IrRoot::Indirect),
            IrEffectKind::Store(IrRoot::Global),
        ]
    );
    assert_eq!(c.shape.escaping_stores, 3);
    assert_eq!(c.param_count, 1);
}

/// A pointer carried around a loop in a block parameter keeps its root when every incoming
/// value agrees, and becomes `Indirect` when two roots meet.
#[test]
fn block_parameters_join_their_incoming_roots() {
    // bb0(%0, %1): br bb1(%0) ; bb1(%2): store %2 ; condbr -> bb1(%2) | bb2 ; bb2: br bb3(%1)
    // bb3(%3): ... reached from bb2 with %1 and from bb1? no: keep bb3 single-source, then a
    // second join bb4 that mixes %0 and %1.
    let mut b0 = entry(2, vec![node(Inst::Br { target: BlockId::new(1), args: vec![v(0)] })]);
    b0.id = BlockId::new(0);
    let mut b1 = Block::new(BlockId::new(1)).with_param(v(2), Ty::Ptr);
    b1.body = vec![
        store(2, 9),
        node(Inst::CondBr {
            cond: v(9),
            then_target: BlockId::new(1),
            then_args: vec![v(2)],
            else_target: BlockId::new(2),
            else_args: vec![],
        }),
    ];
    let mut b2 = Block::new(BlockId::new(2));
    b2.body = vec![node(Inst::CondBr {
        cond: v(9),
        then_target: BlockId::new(3),
        then_args: vec![v(0)],
        else_target: BlockId::new(3),
        else_args: vec![v(1)],
    })];
    let mut b3 = Block::new(BlockId::new(3)).with_param(v(3), Ty::Ptr);
    b3.body = vec![store(3, 9), ret()];
    let m = module_with(2, vec![b0, b1, b2, b3], vec![]);
    let c = ir_census(
        &m,
        &m.functions[0],
        &BTreeMap::new(),
        &BTreeMap::new(),
        &BTreeSet::new(),
        LedgeredLanes::default(),
    );
    assert_eq!(
        c.effects,
        vec![IrEffectKind::Store(IrRoot::Arg(0)), IrEffectKind::Store(IrRoot::Indirect)]
    );
}

#[test]
fn calls_carry_their_ledger_identity() {
    let body = vec![
        node_r(Inst::Call { callee: FuncId::new(1), args: vec![] }, 1),
        node_r(Inst::Call { callee: FuncId::new(2), args: vec![] }, 2),
        node_r(
            Inst::CallIndirect {
                callee: v(1),
                sig: trust_ir::FuncTyId::new(0),
                args: vec![],
                calling_conv: Default::default(),
            },
            3,
        ),
        ret(),
    ];
    let m = module_with(0, vec![entry(0, body)], vec![]);
    let mut ledger = BTreeMap::new();
    ledger.insert(FuncId::new(1), LedgerRow::ids(vec![def(11), def(12)]));
    let c = ir_census(
        &m,
        &m.functions[0],
        &ledger,
        &BTreeMap::new(),
        &BTreeSet::new(),
        LedgeredLanes::default(),
    );
    assert_eq!(
        c.effects,
        vec![
            IrEffectKind::Call {
                ids: vec![def(11), def(12)],
                site: None,
                placeholder_result: false,
                placeholder_params: Vec::new()
            },
            IrEffectKind::UnledgeredCall,
            IrEffectKind::IndirectCall,
        ]
    );
    assert_eq!((c.shape.direct_calls, c.shape.indirect_calls), (2, 1));
}

/// A trust-ir `Assert` is an effect, classed by its proof annotation, and in the shape.
#[test]
fn asserts_are_classed_by_their_annotation() {
    let body = vec![
        node(Inst::Assert { cond: v(0), kind: trust_ir::AssertKind::Unspecified, site: None })
            .with_proof(ProofAnnotation::DivNonZero),
        node(Inst::Assert { cond: v(0), kind: trust_ir::AssertKind::Unspecified, site: None })
            .with_proof(ProofAnnotation::InBounds),
        node(Inst::Assert { cond: v(0), kind: trust_ir::AssertKind::Unspecified, site: None })
            .with_proof(ProofAnnotation::ShiftInRange),
        node(Inst::Assert { cond: v(0), kind: trust_ir::AssertKind::Unspecified, site: None })
            .with_proof(ProofAnnotation::NoOverflow),
        node(Inst::Assert { cond: v(0), kind: trust_ir::AssertKind::Unspecified, site: None }),
        ret(),
    ];
    let m = module_with(1, vec![entry(1, body)], vec![]);
    let c = ir_census(
        &m,
        &m.functions[0],
        &BTreeMap::new(),
        &BTreeMap::new(),
        &BTreeSet::new(),
        LedgeredLanes::default(),
    );
    assert_eq!(
        c.effects,
        vec![
            IrEffectKind::Assert(AssertClass::DivZero),
            IrEffectKind::Assert(AssertClass::Bounds),
            IrEffectKind::Assert(AssertClass::Shift),
            IrEffectKind::Assert(AssertClass::Overflow),
            IrEffectKind::Assert(AssertClass::Other),
        ]
    );
    assert_eq!(c.shape.asserts, 5);
}

/// Unreachable blocks hold no effect: a call after a `ret` is not in the census.
#[test]
fn unreachable_blocks_are_not_counted() {
    let mut dead = Block::new(BlockId::new(1));
    dead.body = vec![node_r(Inst::Call { callee: FuncId::new(1), args: vec![] }, 1), ret()];
    let m = module_with(0, vec![entry(0, vec![ret()]), dead], vec![]);
    assert!(
        ir_census(
            &m,
            &m.functions[0],
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeSet::new(),
            LedgeredLanes::default()
        )
        .effects
        .is_empty()
    );
}

/// The D28 lanes leave these traces in the EMITTED trust-ir: a touch of a degraded struct
/// profile, an `undef`, a ledgered union / enum-parameter lane, and an enum value spelled as a
/// lone `bool`/`()`. A layout-less struct alone is NOT one (a huge array, a coroutine env).
#[test]
fn value_abstractions_are_seen() {
    let degraded = StructDef {
        id: StructId::new(0),
        name: "S".to_string(),
        fields: vec![
            FieldDef { name: "rows".to_string(), ty: Ty::Unit, offset: None },
            FieldDef { name: "n".to_string(), ty: Ty::I32, offset: None },
        ],
        size: None,
        align: None,
        repr: StructRepr::Rust,
        origin: None,
    };
    let s = Ty::Struct(StructId::new(0));
    // The opaque `()` lane's `self.rows = v`: load; extractfield (); insertfield; store.
    let body = vec![
        node_r(Inst::Load { ty: s.clone(), ptr: v(0), volatile: false, align: None }, 1),
        node_r(Inst::ExtractField { ty: Ty::Unit, aggregate: v(1), field: 0 }, 2),
        node_r(Inst::InsertField { ty: s.clone(), aggregate: v(1), field: 0, value: v(2) }, 3),
        node(Inst::Store { ty: s.clone(), ptr: v(0), value: v(3), volatile: false, align: None }),
        ret(),
    ];
    let m = module_with(1, vec![entry(1, body)], vec![degraded]);
    let as_degraded: BTreeSet<StructId> = [StructId::new(0)].into_iter().collect();
    let c = ir_census(
        &m,
        &m.functions[0],
        &BTreeMap::new(),
        &BTreeMap::new(),
        &as_degraded,
        LedgeredLanes::default(),
    );
    assert_eq!(c.abstractions.degraded_struct_touches, 3);
    assert_eq!(abstraction_kinds(&c.abstractions), vec![TagKind::Abstracted(Lane::OpaqueLane)]);
    // The SAME instructions over a layout-less struct the producer did NOT degrade (a huge-array
    // struct, a coroutine environment): faithful, no tag.
    let c = ir_census(
        &m,
        &m.functions[0],
        &BTreeMap::new(),
        &BTreeMap::new(),
        &BTreeSet::new(),
        LedgeredLanes::default(),
    );
    assert!(abstraction_kinds(&c.abstractions).is_empty());

    // `self.boxed = close_then_some(fd)` → `undef bool` stored.
    let undef = vec![node_r(Inst::Undef { ty: Ty::Bool }, 1), ret()];
    let m = module_with(1, vec![entry(1, undef)], vec![]);
    let c = ir_census(
        &m,
        &m.functions[0],
        &BTreeMap::new(),
        &BTreeMap::new(),
        &BTreeSet::new(),
        LedgeredLanes::default(),
    );
    assert_eq!(abstraction_kinds(&c.abstractions), vec![TagKind::Abstracted(Lane::Undef)]);

    // A union / enum-parameter lane the producer ledgered: each its own tag, so a reader that
    // accepts the opaque lane does not accept a union it never claimed to model.
    let m = module_with(0, vec![entry(0, vec![ret()])], vec![]);
    let union = LedgeredLanes { union_lane: true, enum_param_lane: false };
    let c =
        ir_census(&m, &m.functions[0], &BTreeMap::new(), &BTreeMap::new(), &BTreeSet::new(), union);
    assert_eq!(abstraction_kinds(&c.abstractions), vec![TagKind::Abstracted(Lane::UnionLane)]);
    let param = LedgeredLanes { union_lane: false, enum_param_lane: true };
    let c =
        ir_census(&m, &m.functions[0], &BTreeMap::new(), &BTreeMap::new(), &BTreeSet::new(), param);
    assert_eq!(abstraction_kinds(&c.abstractions), vec![TagKind::Abstracted(Lane::EnumParamLane)]);
    // And a plain body carries no tag at all.
    let c = ir_census(
        &m,
        &m.functions[0],
        &BTreeMap::new(),
        &BTreeMap::new(),
        &BTreeSet::new(),
        LedgeredLanes::default(),
    );
    assert!(abstraction_kinds(&c.abstractions).is_empty());
}

/// An enum rustc types as such, spelled as a lone `bool`/`()` in a parameter, the result or a
/// paired call's result, is a placeholder (`fn f(o: Option<Box<i32>>) -> bool` with `o: bool`).
#[test]
fn enum_values_spelled_as_bool_are_placeholders() {
    let mut m = mir(vec![], 1);
    m.arg_enum = vec![true];
    let mut ir_side = ir(vec![], 1);
    ir_side.param_placeholder = vec![true];
    assert_eq!(placeholder_values(&m, &ir_side), 1);
    // A `bool` parameter that rustc also types as `bool` is faithful.
    m.arg_enum = vec![false];
    assert_eq!(placeholder_values(&m, &ir_side), 0);
    // A paired call whose MIR destination is an enum and whose callee returns a lone `bool`.
    let mut m = mir(vec![call(&[9])], 0);
    if let MirEffectKind::Call { enum_result, .. } = &mut m.effects[0].kind {
        *enum_result = true;
    }
    let ir_side = ir(
        vec![IrEffectKind::Call {
            ids: vec![def(9)],
            site: None,
            placeholder_result: true,
            placeholder_params: Vec::new(),
        }],
        0,
    );
    assert_eq!(placeholder_values(&m, &ir_side), 1);
    let ir_side = ir(
        vec![IrEffectKind::Call {
            ids: vec![def(9)],
            site: None,
            placeholder_result: false,
            placeholder_params: Vec::new(),
        }],
        0,
    );
    assert_eq!(placeholder_values(&m, &ir_side), 0);
}

/// The same lane in a CALL ARGUMENT (`resize_with_cell_px(fd, r, c, None)` passed `false` to a
/// callee declared `(i32, u16, u16, bool)`) and in a STORE (`*slot = None` for an
/// `Option<(u32, u32)>` stored as one `false` byte).
#[test]
fn enum_arguments_and_stores_spelled_as_bool_are_placeholders() {
    let mut m = mir(vec![call(&[9])], 0);
    if let MirEffectKind::Call { enum_args, .. } = &mut m.effects[0].kind {
        *enum_args = vec![false, true];
    }
    let callee = |params: Vec<bool>| {
        ir(
            vec![IrEffectKind::Call {
                ids: vec![def(9)],
                site: None,
                placeholder_result: false,
                placeholder_params: params,
            }],
            0,
        )
    };
    assert_eq!(placeholder_values(&m, &callee(vec![false, true])), 1);
    // A real `bool` argument in the same position is faithful.
    assert_eq!(placeholder_values(&m, &callee(vec![true, false])), 0);
    // Argument lists that do not line up: any enum against any placeholder counts once.
    assert_eq!(placeholder_values(&m, &callee(vec![true])), 1);

    let mut m = mir(vec![], 1);
    m.store_values = vec![(MemRoot::Arg(0), StoreValue::ValuedEnum)];
    let mut ir_side = ir(vec![], 1);
    ir_side.placeholder_stores = vec![IrRoot::Arg(0)];
    assert_eq!(placeholder_values(&m, &ir_side), 1);
    // The program also writes a `bool` there: the `bool` store may be that one.
    m.store_values.push((MemRoot::Arg(0), StoreValue::BoolOrUnit));
    assert_eq!(placeholder_values(&m, &ir_side), 0);
    // A store to ANOTHER root does not count.
    m.store_values = vec![(MemRoot::Arg(1), StoreValue::ValuedEnum)];
    let mut ir_two = ir(vec![], 2);
    ir_two.placeholder_stores = vec![IrRoot::Arg(0)];
    m.arg_count = 2;
    assert_eq!(placeholder_values(&m, &ir_two), 0);
}

/// On the trust-ir side a call's argument placeholders are read off the VALUES passed (a per-body
/// module declares no callee), and its result off the type the producer observed the site bind.
#[test]
fn call_placeholders_are_read_off_values_and_the_observed_result() {
    let body = vec![
        node_r(Inst::Const { ty: Ty::Bool, value: trust_ir::Constant::Bool(false) }, 1),
        node_r(Inst::Call { callee: FuncId::new(1), args: vec![v(0), v(1)] }, 2),
        ret(),
    ];
    let m = module_with(1, vec![entry(1, body)], vec![]);
    let mut ledger = BTreeMap::new();
    ledger.insert(FuncId::new(1), LedgerRow::ids(vec![def(4)]));
    let mut returns = BTreeMap::new();
    returns.insert(FuncId::new(1), Ty::Bool);
    let c = ir_census(
        &m,
        &m.functions[0],
        &ledger,
        &returns,
        &BTreeSet::new(),
        LedgeredLanes::default(),
    );
    assert_eq!(
        c.effects,
        vec![IrEffectKind::Call {
            ids: vec![def(4)],
            site: None,
            placeholder_result: true,
            placeholder_params: vec![false, true],
        }]
    );
}

/// THE MUTATION TEST, at unit level: the field-store RHS lane before ec8b51bb3b lowered
/// `self.v = rows_after_close(fd)` without the call. Remove the call from the faithful census
/// and the gate must refuse; put it back and it must not.
#[test]
fn removing_a_lanes_call_is_caught() {
    let call_close =
        |callee: u32| node_r(Inst::Call { callee: FuncId::new(callee), args: vec![v(1)] }, 2);
    let faithful = vec![call_close(1), store(0, 2), ret()];
    let mutated = vec![store(0, 1), ret()];
    let mut ledger = BTreeMap::new();
    ledger.insert(FuncId::new(1), LedgerRow::ids(vec![def(30)]));
    let oracle = mir(vec![call(&[30]), eff(MirEffectKind::Store(MemRoot::Arg(0)))], 2);
    for (body, conserved) in [(faithful, true), (mutated, false)] {
        let m = module_with(2, vec![entry(2, body)], vec![]);
        let c = ir_census(
            &m,
            &m.functions[0],
            &ledger,
            &BTreeMap::new(),
            &BTreeSet::new(),
            LedgeredLanes::default(),
        );
        let got = unpaired_effects(&oracle, &c);
        assert_eq!(got.is_empty(), conserved, "{got:?}");
        if !conserved {
            assert_eq!(kinds(&got), vec![TagKind::NotConserved(Effect::Call)]);
        }
    }
}

/// The splice-consistency check compares ledger-free shapes: a call the splice lost is a
/// different shape, a renumbered callee is not.
#[test]
fn shapes_compare_effects_not_identities() {
    let body =
        |callee| vec![node_r(Inst::Call { callee: FuncId::new(callee), args: vec![] }, 1), ret()];
    let a = module_with(0, vec![entry(0, body(1))], vec![]);
    let b = module_with(0, vec![entry(0, body(7))], vec![]);
    let c = module_with(0, vec![entry(0, vec![ret()])], vec![]);
    assert_eq!(ir_shape(&a, &a.functions[0]), ir_shape(&b, &b.functions[0]));
    assert_ne!(ir_shape(&a, &a.functions[0]), ir_shape(&c, &c.functions[0]));
}

// ---- tags and the sidecar ------------------------------------------------------------------

#[test]
fn tag_labels_round_trip_and_typos_accept_nothing() {
    for kind in [
        TagKind::NotConserved(Effect::Call),
        TagKind::NotConserved(Effect::Store),
        TagKind::NotConserved(Effect::Assert),
        TagKind::NotConserved(Effect::Splice),
        TagKind::Abstracted(Lane::Drop),
        TagKind::Abstracted(Lane::Destructor),
        TagKind::Abstracted(Lane::Undef),
        TagKind::Abstracted(Lane::OpaqueLane),
        TagKind::Abstracted(Lane::UnionLane),
        TagKind::Abstracted(Lane::EnumParamLane),
    ] {
        assert_eq!(TagKind::from_label(&kind.label()), Some(kind));
    }
    assert_eq!(TagKind::from_label("abstracted(opaque)"), None);
    assert_eq!(TagKind::from_label("abstracted"), None);
    assert_eq!(
        TagKind::from_label("not-conserved(assert)"),
        Some(TagKind::NotConserved(Effect::Assert))
    );
    assert_eq!(
        TagKind::from_label("abstracted(destructor)"),
        Some(TagKind::Abstracted(Lane::Destructor))
    );
    let t = Tag { kind: TagKind::NotConserved(Effect::Call), site: "`close` at x.rs:3:5".into() };
    assert_eq!(t.to_string(), "EffectNotConserved(call, `close` at x.rs:3:5)");
    let t = Tag { kind: TagKind::Abstracted(Lane::Undef), site: String::new() };
    assert_eq!(t.to_string(), "Abstracted(undef)");
}

#[test]
fn typed_adapter_sidecar_discloses_source_basis_and_keeps_missing_rows_refused() {
    let source = BodyVerdict {
        def_path: "source".into(),
        clean: true,
        tags: vec![],
        assembled: Some(FuncId::new(0)),
        equivalences: BTreeMap::new(),
        drop_claim_live: None,
        drop_sites: Vec::new(),
    };
    let derived =
        BodyVerdict { def_path: String::new(), assembled: Some(FuncId::new(2)), ..source.clone() };
    let missing = BodyVerdict {
        assembled: Some(FuncId::new(3)),
        tags: vec![Tag {
            kind: TagKind::NotConserved(Effect::Census),
            site: "no source or derived witness".into(),
        }],
        ..source.clone()
    };
    let adapters = BTreeMap::from([(
        FuncId::new(2),
        closure_adapters::Witness {
            adapter: FuncId::new(2),
            owner: FuncId::new(0),
            body: FuncId::new(1),
            closure: trust_ir::ClosureTyId::new(0),
        },
    )]);
    let text = render_sidecar_with_adapters(
        "probe",
        "probe.trust-ir.txt",
        b"source image",
        &[("source".into(), &source), ("adapter".into(), &derived), ("missing".into(), &missing)],
        &adapters,
    );
    let json: serde_json::Value = serde_json::from_str(&text).unwrap();
    let rows = json["functions"].as_array().unwrap();
    assert_eq!(rows.len(), 3);
    assert_eq!(rows[0]["verdict"], "conserved");
    assert!(rows[0].get("basis").is_none());
    assert_eq!(rows[1]["verdict"], "conserved");
    assert_eq!(rows[1]["basis"]["kind"], "typed-closure-adapter");
    assert_eq!(rows[1]["basis"]["owner_func_id"], 0);
    assert_eq!(rows[1]["basis"]["body_func_id"], 1);
    assert_eq!(rows[2]["verdict"], "refused");
    assert_eq!(rows[2]["tags"][0], "not-conserved(census)");
    assert!(rows[2].get("basis").is_none());
}

#[test]
fn the_sidecar_binds_its_module_text_and_lists_every_function() {
    let ok = BodyVerdict {
        def_path: "close_ret".into(),
        clean: true,
        tags: vec![],
        assembled: Some(FuncId::new(0)),
        equivalences: BTreeMap::from([("bool-from-integer", 1)]),
        drop_claim_live: None,
        drop_sites: Vec::new(),
    };
    let bad = BodyVerdict {
        def_path: "S::set_rows_call".into(),
        clean: true,
        tags: vec![
            Tag { kind: TagKind::Abstracted(Lane::OpaqueLane), site: "x".into() },
            Tag { kind: TagKind::Abstracted(Lane::Drop), site: "a \"drop\"".into() },
        ],
        assembled: Some(FuncId::new(1)),
        equivalences: BTreeMap::new(),
        drop_claim_live: None,
        drop_sites: Vec::new(),
    };
    let text = b"; TrustIr text format v1\n";
    let out = render_sidecar(
        "p7",
        "p7.trust-ir.txt",
        text,
        &[("close_ret".into(), &ok), ("S::set_rows_call".into(), &bad)],
    );
    assert!(out.contains(&format!("\"schema\": \"{SIDECAR_SCHEMA}\"")), "{out}");
    assert!(out.contains(&format!("\"fnv1a64\": \"{:016x}\"", fnv1a64(text))), "{out}");
    assert!(out.contains(&format!("\"bytes\": {}", text.len())), "{out}");
    let lines: Vec<&str> = out.lines().filter(|l| l.contains("\"function\":")).collect();
    assert_eq!(lines.len(), 2);
    assert!(lines[0].contains("\"verdict\": \"conserved\", \"tags\": []"), "{}", lines[0]);
    assert!(lines[0].contains("\"equivalences\": {\"bool-from-integer\": 1}"), "{}", lines[0]);
    assert!(lines[1].contains("\"equivalences\": {}"), "{}", lines[1]);
    assert!(
        lines[1].contains("\"verdict\": \"refused\", \"tags\": [\"abstracted(drop)\", \"abstracted(opaque-lane)\"]"),
        "{}",
        lines[1]
    );
    // JSON escaping of a detail string.
    assert!(lines[1].contains("Abstracted(drop, a \\\"drop\\\")"), "{}", lines[1]);
}

#[test]
fn fnv1a64_matches_the_reference_vectors() {
    assert_eq!(fnv1a64(b""), 0xcbf2_9ce4_8422_2325);
    assert_eq!(fnv1a64(b"a"), 0xaf63_dc4c_8601_ec8c);
    assert_eq!(fnv1a64(b"foobar"), 0x8594_4171_f739_67e8);
}

// ── The drop leg (step 2 increment 4b) ───────────────────────────────────────

fn dk(
    identity: crate::drops::DropIdentity,
    span_lo: u32,
    style: crate::drops::LiveStyle,
) -> DropKey {
    DropKey {
        identity,
        ty: 42,
        span: rustc_span::Span::with_root_ctxt(
            rustc_span::BytePos(span_lo),
            rustc_span::BytePos(span_lo + 1),
        ),
        style,
    }
}

/// The producer placed every drop the oracle has: nothing is missing or extra, and the module
/// carries exactly the drops the producer recorded.
#[test]
fn a_faithfully_dropped_body_is_conserved_on_the_drop_leg() {
    use crate::drops::DropIdentity::*;
    use crate::drops::LiveStyle::*;
    let oracle = [dk(Param(0), 10, Static), dk(Var(3), 20, Static)];
    let claim = [dk(Var(3), 20, Static), dk(Param(0), 10, Static)];
    let got = compare_drops(&oracle, Some((&claim, 2)), 2);
    assert_eq!(got, DropComparison::default());
}

/// No claim (the producer placed nothing): every live oracle drop is MISSING (elided).
#[test]
fn with_no_claim_every_oracle_drop_is_missing() {
    use crate::drops::DropIdentity::*;
    use crate::drops::LiveStyle::*;
    let oracle = [dk(Param(0), 10, Static), dk(Other, 30, Conditional)];
    let got = compare_drops(&oracle, None, 0);
    assert_eq!(got.missing, vec![0, 1]);
    assert!(got.extra.is_empty());
    assert_eq!(got.ledger, None);
}

/// A MISSING drop and an EXTRA drop both refuse; a drop at the right place with the wrong style
/// is both (the oracle's is missing, the claim's is extra).
#[test]
fn a_missing_or_extra_or_restyled_drop_is_a_finding() {
    use crate::drops::DropIdentity::*;
    use crate::drops::LiveStyle::*;
    let oracle = [dk(Param(0), 10, Static)];
    // Missing: the claim lacks it.
    assert_eq!(compare_drops(&oracle, Some((&[], 0)), 0).missing, vec![0]);
    // Extra: a second drop of the same parameter (a double drop).
    let twice = [dk(Param(0), 10, Static), dk(Param(0), 10, Static)];
    let got = compare_drops(&oracle, Some((&twice, 2)), 2);
    assert!(got.missing.is_empty());
    assert_eq!(got.extra, vec![1]);
    // Restyled: the oracle needs a flag, the claim drops statically.
    let flagged = [dk(Param(0), 10, Conditional)];
    let got = compare_drops(&flagged, Some((&oracle, 1)), 1);
    assert_eq!((got.missing, got.extra), (vec![0], vec![0]));
    // Misplaced: same local, another point.
    let elsewhere = [dk(Param(0), 11, Static)];
    let got = compare_drops(&oracle, Some((&elsewhere, 1)), 1);
    assert_eq!((got.missing, got.extra), (vec![0], vec![0]));
}

/// The module must carry exactly the `Inst::Drop`s the producer recorded emitting.
#[test]
fn a_module_whose_drops_differ_from_the_ledger_is_a_finding() {
    use crate::drops::DropIdentity::*;
    use crate::drops::LiveStyle::*;
    let oracle = [dk(Param(0), 10, Static)];
    let got = compare_drops(&oracle, Some((&oracle, 1)), 2);
    assert_eq!(got.ledger, Some((1, 2)));
}

#[test]
fn the_drop_effect_label_round_trips() {
    let k = TagKind::NotConserved(Effect::Drop);
    assert_eq!(k.label(), "not-conserved(drop)");
    assert_eq!(TagKind::from_label("not-conserved(drop)"), Some(k));
}

/// Step 2 increment 4c: a body the check withdrew becomes a declaration that names none of its old
/// values, so a module built on the handoff still validates.
#[test]
fn a_stripped_body_keeps_no_value_names_and_still_validates() {
    let mut module = Module::new("m");
    module.target_info = Some(crate::drop_glue_oracle::oracle_target());
    let sig = module
        .add_func_type(FuncTy {
            params: vec![Ty::U32],
            returns: vec![],
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "f", sig, BlockId::new(0));
    let mut b = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::U32);
    b.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    f.blocks = vec![b];
    f.producer = Some(trust_ir::Producer::TRust);
    f.value_names = Some(vec![(ValueId::new(0), "x".to_string())]);
    f.linkage = trust_ir::Linkage::External;
    module.try_add_function(f).expect("Module::try_add_function: test fixture");
    assert_eq!(strip_unconserved_bodies(&mut module, &BTreeSet::new()), 1);
    let f = module.function_by_id(FuncId::new(0)).unwrap();
    assert!(f.is_declaration() && f.value_names.is_none() && f.scopes.is_none());
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "{errors:?}");
}

/// Test 15 (step 6.5.1, INC6.5-JUDGE): a template record keeps EVERY census input the mainline
/// record keeps — the drop claim and refusal, the degraded struct rows (and the census computed
/// with them), the two placeholder lanes and the collapsed enum types — and it lands in the
/// registry's TEMPLATE map only, never beside the mainline record. `record_template_body` builds
/// it with `producer_body`, the one rule `record_producer_body` builds the mainline record with.
#[test]
fn record_template_body_keeps_every_census_input() {
    let degraded = StructId::new(0);
    let mut module = module_with(
        1,
        vec![entry(1, vec![node_r(Inst::Undef { ty: Ty::Struct(degraded) }, 1), ret()])],
        vec![StructDef {
            id: degraded,
            name: "Degraded".to_string(),
            fields: vec![FieldDef { name: "v".to_string(), ty: Ty::Unit, offset: None }],
            size: None,
            align: None,
            repr: StructRepr::Rust,
            origin: None,
        }],
    );
    module.functions[0].name = "dep::pick".to_string();
    let claim = crate::drops::DropClaim { emitted: 2, ..Default::default() };
    let lanes = LedgeredLanes { union_lane: true, enum_param_lane: true };
    let collapsed: BTreeSet<u128> = [0xC0FFEE].into_iter().collect();
    let body = producer_body(
        "dep::pick".to_string(),
        &module,
        &[],
        crate::BodyKind::Fn,
        true,
        &[degraded],
        lanes,
        collapsed.clone(),
        Some(claim),
        Some("why no drop".to_string()),
    );
    let mut registry = CensusRegistry::default();
    registry.insert_template(5, body);
    let kept = registry.template(5).expect("the template record");
    assert_eq!(kept.drop_claim.as_ref().map(|c| c.emitted), Some(2), "the drop claim");
    assert_eq!(kept.drop_refusal.as_deref(), Some("why no drop"), "the drop refusal");
    assert_eq!(kept.degraded_structs, vec![degraded], "the degraded rows");
    assert_eq!(kept.census.abstractions.degraded_struct_touches, 1, "and the census read them");
    assert!(kept.census.abstractions.union_lane, "the union lane");
    assert!(kept.census.abstractions.enum_param_lane, "the enum-parameter lane");
    assert_eq!(kept.collapsed_enums, collapsed, "the collapsed enum types");
    assert!(registry.producer.is_empty(), "never beside the mainline record");
    assert!(registry.template_duplicated.is_empty());
    // A second record of the same definition is not trusted.
    let again = producer_body(
        "dep::pick".to_string(),
        &module,
        &[],
        crate::BodyKind::Fn,
        true,
        &[],
        LedgeredLanes::default(),
        BTreeSet::new(),
        None,
        None,
    );
    registry.insert_template(5, again);
    assert!(registry.template_duplicated.contains(&5));
}

#[test]
fn exact_store_roots_preserve_arguments_counts_and_effect_multiplicity() {
    let mut oracle = mir(vec![eff(MirEffectKind::Store(MemRoot::Indirect))], 3);
    oracle.exact_store_args.insert(0, 1);
    oracle.store_values.push((MemRoot::Indirect, StoreValue::Other));
    let side = |root, count| IrCensus {
        effects: vec![IrEffectKind::Store(root)],
        param_count: count,
        ..Default::default()
    };
    assert!(unpaired_effects(&oracle, &side(IrRoot::Arg(1), 3)).is_empty());
    for (root, count) in [
        (IrRoot::Arg(0), 3),
        (IrRoot::Arg(1), 2),
        (IrRoot::Arg(1), 4),
        (IrRoot::Global, 3),
        (IrRoot::Indirect, 3),
        (IrRoot::Local, 3),
    ] {
        assert_eq!(
            kinds(&unpaired_effects(&oracle, &side(root, count))),
            vec![TagKind::NotConserved(Effect::Store)]
        );
    }
    assert_eq!(unpaired_effects(&oracle, &IrCensus::default()).len(), 1);
    oracle.effects.push(eff(MirEffectKind::Store(MemRoot::Indirect)));
    oracle.exact_store_args.insert(1, 1);
    oracle.store_values.push((MemRoot::Indirect, StoreValue::Other));
    assert_eq!(unpaired_effects(&oracle, &side(IrRoot::Arg(1), 3)).len(), 1);
    // The legacy coarse argument pooling is deliberately unchanged.
    let legacy = mir(vec![eff(MirEffectKind::Store(MemRoot::Arg(0)))], 3);
    assert!(unpaired_effects(&legacy, &side(IrRoot::Arg(1), 2)).is_empty());
}

#[test]
fn exact_store_pairing_cannot_hide_an_enum_placeholder() {
    let mut oracle = mir(vec![eff(MirEffectKind::Store(MemRoot::Indirect))], 2);
    oracle.exact_store_args.insert(0, 1);
    oracle.store_values = vec![(MemRoot::Indirect, StoreValue::ValuedEnum)];
    let mut lowered = IrCensus {
        effects: vec![IrEffectKind::Store(IrRoot::Arg(1))],
        param_count: 2,
        placeholder_stores: vec![IrRoot::Arg(1)],
        ..Default::default()
    };
    assert!(unpaired_effects(&oracle, &lowered).is_empty());
    assert_eq!(placeholder_values(&oracle, &lowered), 1);
    assert!(
        abstraction_kinds(&judgement_abstractions(&oracle, &lowered, &BTreeSet::new()))
            .contains(&TagKind::Abstracted(Lane::OpaqueLane))
    );
    lowered.effects = vec![IrEffectKind::Store(IrRoot::Arg(0))];
    assert_eq!(unpaired_effects(&oracle, &lowered).len(), 1);
    lowered.effects = vec![IrEffectKind::Store(IrRoot::Arg(1))];
    lowered.param_count = 1;
    assert_eq!(unpaired_effects(&oracle, &lowered).len(), 1);
    lowered.param_count = 2;
    oracle.store_values.clear();
    assert_eq!(unpaired_effects(&oracle, &lowered).len(), 1);
}

#[test]
fn exact_store_bindings_survive_the_actual_drop_filter() {
    let mut oracle = mir(
        vec![
            eff(MirEffectKind::Drop { destructor: false }),
            eff(MirEffectKind::Store(MemRoot::Indirect)),
            eff(MirEffectKind::Drop { destructor: true }),
            eff(MirEffectKind::Store(MemRoot::Indirect)),
        ],
        2,
    );
    oracle.exact_store_args = BTreeMap::from([(1, 0), (3, 1)]);
    oracle.store_values =
        vec![(MemRoot::Indirect, StoreValue::Other), (MemRoot::Indirect, StoreValue::ValuedEnum)];
    let filtered = without_drop_effects(&oracle);
    assert_eq!(filtered.exact_store_args, BTreeMap::from([(0, 0), (1, 1)]));
    let lowered = IrCensus {
        effects: vec![IrEffectKind::Store(IrRoot::Arg(0)), IrEffectKind::Store(IrRoot::Arg(1))],
        param_count: 2,
        placeholder_stores: vec![IrRoot::Arg(1)],
        ..Default::default()
    };
    assert!(unpaired_effects(&filtered, &lowered).is_empty());
    assert_eq!(placeholder_values(&filtered, &lowered), 1);
    assert_eq!(oracle.effects.len(), 4);
    assert_eq!(oracle.exact_store_args, BTreeMap::from([(1, 0), (3, 1)]));
}
