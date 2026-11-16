//! Trust: the golden wire layout of the `TyEncodable` MIR types, keyed to
//! [`METADATA_VERSION`](super::METADATA_VERSION).
//!
//! MIR bodies ride crate metadata (`optimized_mir`, `mir_for_ctfe`, ...), so a
//! field or variant added to a `TyEncodable` MIR type changes the rmeta wire
//! format even when no rmeta *table* changes. `f24fdb2fdb` did exactly that —
//! it added `Statement::trust_modular_arith` with the header still saying 12 —
//! and a driver at that commit decoding an older same-version sysroot ICEd
//! mid-stream ("invalid enum variant tag while decoding `StmtDebugInfo`")
//! instead of refusing the crate with E0514. `47236131c9` paid the owed bump.
//!
//! This test is the source-side guard for that class. It encodes a fixed
//! corpus of MIR values through a recording [`TyEncoder`], so every field and
//! discriminant the derived encoders emit becomes one token of a text trace,
//! and records the variant count of every `TyEncodable` MIR enum it can name.
//! The trace is pinned in `mir_layout.golden` together with the
//! `METADATA_VERSION` it was recorded under:
//!
//! * trace changed, version NOT bumped: fail — "bump METADATA_VERSION". This is
//!   the f24fdb2fdb shape, and `--bless` refuses to launder it.
//! * version bumped: fail until the golden is re-recorded under the new
//!   version (`./x.py test compiler/rustc_metadata --bless`), so the NEXT
//!   change is measured against a golden that names its own version.
//! * corpus GREW (every golden line still present, in order, plus new ones):
//!   blessable without a bump. A new sample or a newly counted enum records a
//!   layout that was already on the wire; it cannot hide a change, because a
//!   change to anything already recorded alters an existing line.
//!
//! [`every_tyencodable_mir_enum_is_counted`] keeps the variant-count list from
//! rotting: it scans `rustc_middle/src/mir` for every enum deriving an encoder
//! and fails when one is missing from [`variant_counts`].
//!
//! Coverage boundary, stated so nobody reads more into a green than it holds:
//! values that need a `TyCtxt` to construct (`Ty`, `ty::Const`, `Region`,
//! non-empty interned lists, `mir::Const`) cannot be built here, so a type
//! reachable only through them (`LocalDecl`, `CoroutineInfo`, `ConstOperand`,
//! ...) is covered by its enum's variant count, not by a sample encoding. A
//! struct that is neither sampled nor an enum is not covered at all: a field
//! added to `LocalDecl` or `CoroutineLayout` passes this test. The encodable
//! enums private to their `rustc_middle` module cannot be named here either;
//! [`UNNAMEABLE_ENUMS`] lists each with what, if anything, still pins it.

use std::fmt::Write as _;

use rustc_abi::{FieldIdx, VariantIdx};
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::{CRATE_HIR_ID, ItemLocalId};
use rustc_index::IndexVec;
use rustc_middle::mir::coverage::CoverageKind;
use rustc_middle::mir::interpret::{AllocId, Allocation};
use rustc_middle::mir::trust_contract::TrustContractBundle;
use rustc_middle::mir::*;
use rustc_middle::ty::codec::TyEncoder;
use rustc_middle::ty::{self, Ty, UserTypeAnnotationIndex};
use rustc_serialize::{Encodable, Encoder};
use rustc_span::def_id::{CRATE_DEF_ID, CrateNum, DefId, DefIndex};
use rustc_span::{
    ByteSymbol, DUMMY_SP, ExpnId, Span, SpanEncoder, Spanned, Symbol, SyntaxContext, sym,
};

use super::METADATA_VERSION;

const GOLDEN_PATH: &str = "src/rmeta/mir_layout.golden";
const GOLDEN: &str = include_str!("mir_layout.golden");

/// An encoder that renders every primitive the derived encoders emit as one
/// width-tagged token. Width tags matter: widening a field from `u32` to `u64`
/// is a format change even when the value is the same.
struct LayoutRecorder<'tcx> {
    tokens: Vec<String>,
    type_shorthands: FxHashMap<Ty<'tcx>, usize>,
    predicate_shorthands: FxHashMap<ty::PredicateKind<'tcx>, usize>,
}

impl<'tcx> LayoutRecorder<'tcx> {
    fn new() -> Self {
        LayoutRecorder {
            tokens: Vec::new(),
            type_shorthands: FxHashMap::default(),
            predicate_shorthands: FxHashMap::default(),
        }
    }

    fn push(&mut self, token: String) {
        self.tokens.push(token);
    }
}

impl Encoder for LayoutRecorder<'_> {
    fn emit_usize(&mut self, v: usize) {
        self.push(format!("usize:{v}"));
    }
    fn emit_u128(&mut self, v: u128) {
        self.push(format!("u128:{v}"));
    }
    fn emit_u64(&mut self, v: u64) {
        self.push(format!("u64:{v}"));
    }
    fn emit_u32(&mut self, v: u32) {
        self.push(format!("u32:{v}"));
    }
    fn emit_u16(&mut self, v: u16) {
        self.push(format!("u16:{v}"));
    }
    fn emit_u8(&mut self, v: u8) {
        self.push(format!("u8:{v}"));
    }
    fn emit_isize(&mut self, v: isize) {
        self.push(format!("isize:{v}"));
    }
    fn emit_i128(&mut self, v: i128) {
        self.push(format!("i128:{v}"));
    }
    fn emit_i64(&mut self, v: i64) {
        self.push(format!("i64:{v}"));
    }
    fn emit_i32(&mut self, v: i32) {
        self.push(format!("i32:{v}"));
    }
    fn emit_i16(&mut self, v: i16) {
        self.push(format!("i16:{v}"));
    }
    fn emit_raw_bytes(&mut self, s: &[u8]) {
        self.push(format!("bytes:{s:02x?}"));
    }
}

impl SpanEncoder for LayoutRecorder<'_> {
    fn encode_span(&mut self, _span: Span) {
        // The span codec is the rmeta encoder's own business (and is covered by
        // its own tables); here a span is one opaque slot in its parent.
        self.push("span".to_string());
    }
    fn encode_symbol(&mut self, _sym: Symbol) {
        // One opaque slot, like a span: which symbol it is (and the preinterned
        // symbol table's numbering) is not a property of the MIR types.
        self.push("sym".to_string());
    }
    fn encode_byte_symbol(&mut self, _byte_sym: ByteSymbol) {
        panic!("the golden corpus must not contain a ByteSymbol");
    }
    fn encode_expn_id(&mut self, _expn_id: ExpnId) {
        panic!("the golden corpus must not contain an ExpnId");
    }
    fn encode_syntax_context(&mut self, _syntax_context: SyntaxContext) {
        panic!("the golden corpus must not contain a SyntaxContext");
    }
    fn encode_crate_num(&mut self, crate_num: CrateNum) {
        self.push(format!("crate:{}", crate_num.as_u32()));
    }
    fn encode_def_index(&mut self, def_index: DefIndex) {
        self.push(format!("def_index:{}", def_index.as_u32()));
    }
    fn encode_def_id(&mut self, def_id: DefId) {
        self.push(format!("def_id:{}:{}", def_id.krate.as_u32(), def_id.index.as_u32()));
    }
}

impl<'tcx> TyEncoder<'tcx> for LayoutRecorder<'tcx> {
    // The rmeta encoder clears crate-local data; so does this one.
    const CLEAR_CROSS_CRATE: bool = true;

    fn position(&self) -> usize {
        self.tokens.len()
    }
    fn type_shorthands(&mut self) -> &mut FxHashMap<Ty<'tcx>, usize> {
        &mut self.type_shorthands
    }
    fn predicate_shorthands(&mut self) -> &mut FxHashMap<ty::PredicateKind<'tcx>, usize> {
        &mut self.predicate_shorthands
    }
    fn encode_alloc_id(&mut self, _alloc_id: &AllocId) {
        panic!("the golden corpus must not contain an AllocId");
    }
}

fn trace<'tcx, T: Encodable<LayoutRecorder<'tcx>>>(value: &T) -> String {
    let mut recorder = LayoutRecorder::new();
    value.encode(&mut recorder);
    recorder.tokens.join(" ")
}

fn si() -> SourceInfo {
    SourceInfo { span: DUMMY_SP, scope: SourceScope::from_u32(1) }
}

fn place<'tcx>(local: u32) -> Place<'tcx> {
    Place::from(Local::from_u32(local))
}

fn bb(i: u32) -> BasicBlock {
    BasicBlock::from_u32(i)
}

fn stmt<'tcx>(kind: StatementKind<'tcx>) -> Statement<'tcx> {
    Statement::new(si(), kind)
}

fn term<'tcx>(kind: TerminatorKind<'tcx>) -> Terminator<'tcx> {
    Terminator { source_info: si(), kind }
}

fn copy<'tcx>(local: u32) -> Operand<'tcx> {
    Operand::Copy(place(local))
}

fn assign<'tcx>(rvalue: Rvalue<'tcx>) -> Statement<'tcx> {
    stmt(StatementKind::Assign(Box::new((place(1), rvalue))))
}

fn statements<'tcx>() -> Vec<(&'static str, Statement<'tcx>)> {
    let mut with_debuginfo = stmt(StatementKind::Nop);
    with_debuginfo.debuginfos.push(StmtDebugInfo::AssignRef(Local::from_u32(2), place(3)));
    with_debuginfo.debuginfos.push(StmtDebugInfo::InvalidAssign(Local::from_u32(4)));
    vec![
        ("Statement/Nop", stmt(StatementKind::Nop)),
        ("Statement/Nop+debuginfos", with_debuginfo),
        (
            "Statement/Assign(BinaryOp)+trust_modular_arith",
            Statement::new_trust_modular_arith(
                si(),
                StatementKind::Assign(Box::new((
                    place(1),
                    Rvalue::BinaryOp(
                        BinOp::AddWithOverflow,
                        Box::new((copy(2), Operand::Move(place(3)))),
                    ),
                ))),
            ),
        ),
        ("Statement/Assign(Use)", assign(Rvalue::Use(copy(2), WithRetag::Yes))),
        (
            "Statement/Assign(ThreadLocalRef)",
            assign(Rvalue::ThreadLocalRef(CRATE_DEF_ID.to_def_id())),
        ),
        ("Statement/Assign(RawPtr)", assign(Rvalue::RawPtr(RawPtrKind::Mut, place(2)))),
        ("Statement/Assign(UnaryOp)", assign(Rvalue::UnaryOp(UnOp::Neg, copy(2)))),
        ("Statement/Assign(Discriminant)", assign(Rvalue::Discriminant(place(2)))),
        (
            "Statement/Assign(Aggregate(Tuple))",
            assign(Rvalue::Aggregate(
                Box::new(AggregateKind::Tuple),
                IndexVec::<FieldIdx, _>::from_raw(vec![copy(2), copy(3)]),
            )),
        ),
        (
            "Statement/Assign(Aggregate(Adt))",
            assign(Rvalue::Aggregate(
                Box::new(AggregateKind::Adt(
                    CRATE_DEF_ID.to_def_id(),
                    VariantIdx::from_u32(1),
                    ty::GenericArgs::empty(),
                    Some(UserTypeAnnotationIndex::from_u32(0)),
                    Some(FieldIdx::from_u32(2)),
                )),
                IndexVec::new(),
            )),
        ),
        ("Statement/Assign(CopyForDeref)", assign(Rvalue::CopyForDeref(place(2)))),
        (
            "Statement/FakeRead",
            stmt(StatementKind::FakeRead(Box::new((FakeReadCause::ForIndex, place(1))))),
        ),
        (
            "Statement/SetDiscriminant",
            stmt(StatementKind::SetDiscriminant {
                place: Box::new(place(1)),
                variant_index: VariantIdx::from_u32(3),
            }),
        ),
        ("Statement/StorageLive", stmt(StatementKind::StorageLive(Local::from_u32(5)))),
        ("Statement/StorageDead", stmt(StatementKind::StorageDead(Local::from_u32(5)))),
        ("Statement/PlaceMention", stmt(StatementKind::PlaceMention(Box::new(place(2))))),
        (
            "Statement/AscribeUserType",
            stmt(StatementKind::AscribeUserType(
                Box::new((
                    place(1),
                    UserTypeProjection {
                        base: UserTypeAnnotationIndex::from_u32(0),
                        projs: vec![ProjectionElem::Deref],
                    },
                )),
                ty::Variance::Contravariant,
            )),
        ),
        (
            "Statement/Coverage",
            stmt(StatementKind::Coverage(CoverageKind::BlockMarker {
                id: rustc_middle::mir::coverage::BlockMarkerId::from_u32(1),
            })),
        ),
        (
            "Statement/Intrinsic(Assume)",
            stmt(StatementKind::Intrinsic(Box::new(NonDivergingIntrinsic::Assume(copy(2))))),
        ),
        ("Statement/ConstEvalCounter", stmt(StatementKind::ConstEvalCounter)),
        (
            "Statement/BackwardIncompatibleDropHint",
            stmt(StatementKind::BackwardIncompatibleDropHint {
                place: Box::new(place(1)),
                reason: BackwardIncompatibleDropReason::Edition2024,
            }),
        ),
    ]
}

fn terminators<'tcx>() -> Vec<(&'static str, Terminator<'tcx>)> {
    vec![
        (
            "Terminator/Goto",
            term(TerminatorKind::Goto { target: bb(1), loop_hint_attrs: Default::default() }),
        ),
        (
            "Terminator/SwitchInt",
            term(TerminatorKind::SwitchInt {
                discr: copy(1),
                targets: SwitchTargets::static_if(7, bb(1), bb(2)),
            }),
        ),
        ("Terminator/UnwindResume", term(TerminatorKind::UnwindResume)),
        (
            "Terminator/UnwindTerminate",
            term(TerminatorKind::UnwindTerminate(UnwindTerminateReason::InCleanup)),
        ),
        ("Terminator/Return", term(TerminatorKind::Return)),
        ("Terminator/Unreachable", term(TerminatorKind::Unreachable)),
        (
            "Terminator/Drop",
            term(TerminatorKind::Drop {
                place: place(1),
                target: bb(1),
                unwind: UnwindAction::Cleanup(bb(3)),
                replace: true,
                drop: Some(bb(2)),
            }),
        ),
        (
            "Terminator/Call",
            term(TerminatorKind::Call {
                func: copy(4),
                args: Box::new([Spanned { node: Operand::Move(place(2)), span: DUMMY_SP }]),
                destination: place(0),
                target: Some(bb(1)),
                unwind: UnwindAction::Terminate(UnwindTerminateReason::Abi),
                call_source: CallSource::OverloadedOperator,
                fn_span: DUMMY_SP,
            }),
        ),
        (
            "Terminator/TailCall",
            term(TerminatorKind::TailCall {
                func: copy(4),
                args: Box::new([Spanned { node: copy(2), span: DUMMY_SP }]),
                fn_span: DUMMY_SP,
            }),
        ),
        (
            "Terminator/Assert",
            term(TerminatorKind::Assert {
                cond: copy(1),
                expected: false,
                msg: Box::new(AssertKind::BoundsCheck { len: copy(2), index: copy(3) }),
                target: bb(1),
                unwind: UnwindAction::Unreachable,
            }),
        ),
        (
            "Terminator/Yield",
            term(TerminatorKind::Yield {
                value: copy(1),
                resume: bb(1),
                resume_arg: place(2),
                drop: None,
            }),
        ),
        ("Terminator/CoroutineDrop", term(TerminatorKind::CoroutineDrop)),
        (
            "Terminator/FalseEdge",
            term(TerminatorKind::FalseEdge { real_target: bb(1), imaginary_target: bb(2) }),
        ),
        (
            "Terminator/FalseUnwind",
            term(TerminatorKind::FalseUnwind {
                real_target: bb(1),
                unwind: UnwindAction::Continue,
            }),
        ),
    ]
}

/// A body with every sampleable component populated: blocks with statements
/// and a cleanup flag, a source scope with crate-local data (which the rmeta
/// encoder must CLEAR), and a debuginfo entry.
fn body<'tcx>() -> Body<'tcx> {
    let mut blocks = IndexVec::new();
    blocks.push(BasicBlockData::new_stmts(
        vec![stmt(StatementKind::StorageLive(Local::from_u32(1)))],
        Some(term(TerminatorKind::Goto { target: bb(1), loop_hint_attrs: Default::default() })),
        false,
    ));
    blocks.push(BasicBlockData::new(Some(term(TerminatorKind::Return)), true));
    let mut body = Body::new_cfg_only(blocks);
    body.source_scopes.push(SourceScopeData {
        span: DUMMY_SP,
        parent_scope: None,
        inlined: None,
        inlined_parent_scope: None,
        local_data: ClearCrossCrate::Set(SourceScopeLocalData {
            lint_root: CRATE_HIR_ID,
            trust_loop_hir_local_id: Some(ItemLocalId::from_u32(7)),
        }),
    });
    body.source_scopes.push(SourceScopeData {
        span: DUMMY_SP,
        parent_scope: Some(OUTERMOST_SOURCE_SCOPE),
        inlined: None,
        inlined_parent_scope: Some(OUTERMOST_SOURCE_SCOPE),
        local_data: ClearCrossCrate::Clear,
    });
    body.var_debug_info.push(VarDebugInfo {
        name: sym::len,
        source_info: si(),
        composite: None,
        value: VarDebugInfoContents::Place(place(1)),
        argument_index: Some(1),
    });
    body.arg_count = 1;
    body.spread_arg = Some(Local::from_u32(1));
    body.pass_count = 3;
    body.injection_phase = Some(MirPhase::Runtime(RuntimePhase::Optimized));
    body
}

/// The variant count of every `TyEncodable` MIR enum this crate can name. A
/// variant appended at the END of an enum shifts no existing discriminant, so
/// no sample above would see it — but an older decoder still cannot read it.
fn variant_counts() -> Vec<(&'static str, usize)> {
    use std::mem::variant_count as n;

    use rustc_middle::mir::coverage::{CovTerm, MappingKind, Op, PointKind};
    use rustc_middle::mir::interpret::{ErrorHandled, GlobalAlloc, Scalar, ValTreeCreationError};
    use rustc_middle::mir::trust_contract::*;
    use rustc_middle::mir::trust_once::TrustOnceCellKind;
    use rustc_middle::mir::trust_proof::*;
    use rustc_middle::mir::trust_proof_item::*;
    use rustc_middle::mir::{
        AnnotationSource, BindingForm, ConstraintCategory, MentionedItem, ReturnConstraint,
    };

    vec![
        ("AggregateKind", n::<AggregateKind<'static>>()),
        ("AnalysisPhase", n::<AnalysisPhase>()),
        ("AnnotationSource", n::<AnnotationSource>()),
        ("AssertKind", n::<AssertKind<Operand<'static>>>()),
        ("BackwardIncompatibleDropReason", n::<BackwardIncompatibleDropReason>()),
        ("BinOp", n::<BinOp>()),
        ("BindingForm", n::<BindingForm<'static>>()),
        ("BorrowKind", n::<BorrowKind>()),
        ("CallSource", n::<CallSource>()),
        ("CastKind", n::<CastKind>()),
        ("ClearCrossCrate", n::<ClearCrossCrate<()>>()),
        ("CoercionSource", n::<CoercionSource>()),
        ("Const", n::<Const<'static>>()),
        ("ConstValue", n::<ConstValue>()),
        ("ConstraintCategory", n::<ConstraintCategory<'static>>()),
        ("CovTerm", n::<CovTerm>()),
        ("CoverageKind", n::<CoverageKind>()),
        ("ErrorHandled", n::<ErrorHandled>()),
        ("FakeBorrowKind", n::<FakeBorrowKind>()),
        ("FakeReadCause", n::<FakeReadCause>()),
        ("GlobalAlloc", n::<GlobalAlloc<'static>>()),
        ("InlineAsmMacro", n::<InlineAsmMacro>()),
        ("InlineAsmOperand", n::<InlineAsmOperand<'static>>()),
        ("LocalInfo", n::<LocalInfo<'static>>()),
        ("MappingKind", n::<MappingKind>()),
        ("MentionedItem", n::<MentionedItem<'static>>()),
        ("MirPhase", n::<MirPhase>()),
        ("MutBorrowKind", n::<MutBorrowKind>()),
        ("NonDivergingIntrinsic", n::<NonDivergingIntrinsic<'static>>()),
        ("Op", n::<Op>()),
        ("Operand", n::<Operand<'static>>()),
        ("PointKind", n::<PointKind>()),
        ("ProjectionElem", n::<ProjectionElem<Local, Ty<'static>>>()),
        ("RawPtrKind", n::<RawPtrKind>()),
        ("ReturnConstraint", n::<ReturnConstraint>()),
        ("RuntimeChecks", n::<RuntimeChecks>()),
        ("RuntimePhase", n::<RuntimePhase>()),
        ("Rvalue", n::<Rvalue<'static>>()),
        ("Scalar", n::<Scalar>()),
        ("StatementKind", n::<StatementKind<'static>>()),
        ("StmtDebugInfo", n::<StmtDebugInfo<'static>>()),
        ("TerminatorKind", n::<TerminatorKind<'static>>()),
        ("UnOp", n::<UnOp>()),
        ("UnwindAction", n::<UnwindAction>()),
        ("UnwindTerminateReason", n::<UnwindTerminateReason>()),
        ("ValTreeCreationError", n::<ValTreeCreationError<'static>>()),
        ("VarDebugInfoContents", n::<VarDebugInfoContents<'static>>()),
        ("WithRetag", n::<WithRetag>()),
        // Trust-owned MIR types; `trust_contracts` is an rmeta table.
        ("TrustBinOp", n::<TrustBinOp>()),
        ("TrustContractKind", n::<TrustContractKind>()),
        ("TrustContractPayloadType", n::<TrustContractPayloadType<'static>>()),
        ("TrustContractPredicateKind", n::<TrustContractPredicateKind>()),
        ("TrustContractProposition", n::<TrustContractProposition>()),
        ("TrustContractPropositionDomain", n::<TrustContractPropositionDomain>()),
        ("TrustContractSource", n::<TrustContractSource>()),
        ("TrustContractSubject", n::<TrustContractSubject>()),
        ("TrustContractVerifierSort", n::<TrustContractVerifierSort>()),
        ("TrustHardenedVcCategory", n::<TrustHardenedVcCategory>()),
        ("TrustObligationKind", n::<TrustObligationKind>()),
        ("TrustOnceCellKind", n::<TrustOnceCellKind>()),
        ("TrustProofBody", n::<TrustProofBody>()),
        ("TrustProofItemKind", n::<TrustProofItemKind>()),
        ("TrustProofItemSource", n::<TrustProofItemSource>()),
        ("TrustProofLevel", n::<TrustProofLevel>()),
        ("TrustProofStrength", n::<TrustProofStrength>()),
        ("TrustProofTarget", n::<TrustProofTarget>()),
        ("TrustRuntimeFallbackReason", n::<TrustRuntimeFallbackReason>()),
        ("TrustSpawnVerdict", n::<TrustSpawnVerdict>()),
        ("TrustStatus", n::<TrustStatus>()),
    ]
}

/// The layout as recorded under the current `METADATA_VERSION`.
fn render_layout() -> String {
    let mut out = String::new();
    for (name, value) in statements() {
        writeln!(out, "{name}: {}", trace(&value)).unwrap();
    }
    for (name, value) in terminators() {
        writeln!(out, "{name}: {}", trace(&value)).unwrap();
    }
    writeln!(out, "Body: {}", trace(&body())).unwrap();
    // An allocation rides rmeta inside every `ConstValue::Indirect`; its
    // hand-written encoder elides the bytes when all are zero, so sample both.
    let nonzero: Allocation = Allocation::from_bytes_byte_aligned_immutable(&[1u8, 0, 2][..], ());
    writeln!(out, "Allocation/bytes: {}", trace(&nonzero)).unwrap();
    let zeroed: Allocation = Allocation::from_bytes_byte_aligned_immutable(&[0u8; 4][..], ());
    writeln!(out, "Allocation/all_zero: {}", trace(&zeroed)).unwrap();
    writeln!(
        out,
        "TrustContractBundle/empty: {}",
        trace(&TrustContractBundle::empty(CRATE_DEF_ID.to_def_id()))
    )
    .unwrap();
    for (name, count) in variant_counts() {
        writeln!(out, "variant_count {name}: {count}").unwrap();
    }
    out
}

const VERSION_PREFIX: &str = "METADATA_VERSION ";

fn render_golden(version: u8, layout: &str) -> String {
    format!(
        "# Trust: recorded by compiler/rustc_metadata/src/rmeta/tests.rs -- the\n\
         # TyEncodable MIR wire layout under the METADATA_VERSION below. Re-record\n\
         # ONLY after bumping METADATA_VERSION:\n\
         #   ./x.py test compiler/rustc_metadata --bless\n\
         {VERSION_PREFIX}{version}\n{layout}"
    )
}

/// Returns `(version, layout)` of the checked-in golden.
fn parse_golden(golden: &str) -> (u8, String) {
    let mut version = None;
    let mut layout = String::new();
    for line in golden.lines() {
        if line.starts_with('#') {
            continue;
        }
        if let Some(v) = line.strip_prefix(VERSION_PREFIX) {
            version = Some(v.trim().parse::<u8>().expect("golden METADATA_VERSION is a u8"));
            continue;
        }
        layout.push_str(line);
        layout.push('\n');
    }
    (version.expect("golden names the METADATA_VERSION it was recorded under"), layout)
}

fn bless_requested() -> bool {
    std::env::var_os("RUSTC_BLESS").is_some_and(|v| v != "0")
}

/// The verdict, separated from I/O so the mutation tests below can drive it.
#[derive(Debug, PartialEq)]
enum Verdict {
    Matches,
    /// The layout moved while `METADATA_VERSION` stayed put: the f24fdb2fdb
    /// class. Never blessable.
    NeedsBump,
    /// `METADATA_VERSION` moved: the golden must be re-recorded under it.
    NeedsRerecord,
    /// Every golden line is still present, in order, and new lines were added:
    /// the corpus grew. Blessable without a bump, since nothing recorded moved.
    CorpusGrew,
}

/// Whether `golden` is an in-order subsequence of `current`, line by line.
fn only_additions(golden: &str, current: &str) -> bool {
    let mut current = current.lines();
    golden.lines().all(|g| current.any(|c| c == g))
}

fn judge(current_version: u8, current_layout: &str, golden: &str) -> Verdict {
    let (golden_version, golden_layout) = parse_golden(golden);
    if current_version != golden_version {
        Verdict::NeedsRerecord
    } else if current_layout == golden_layout {
        Verdict::Matches
    } else if only_additions(&golden_layout, current_layout) {
        Verdict::CorpusGrew
    } else {
        Verdict::NeedsBump
    }
}

fn first_difference(golden: &str, current: &str) -> String {
    let (_, golden_layout) = parse_golden(golden);
    let mut g = golden_layout.lines();
    let mut c = current.lines();
    loop {
        match (g.next(), c.next()) {
            (None, None) => return "no line differs".to_string(),
            (a, b) if a == b => continue,
            (a, b) => {
                return format!(
                    "golden:  {}\ncurrent: {}",
                    a.unwrap_or("<absent>"),
                    b.unwrap_or("<absent>")
                );
            }
        }
    }
}

#[test]
fn tyencodable_mir_layout_is_pinned_to_metadata_version() {
    let layout = render_layout();
    match judge(METADATA_VERSION, &layout, GOLDEN) {
        Verdict::Matches => {}
        Verdict::NeedsBump => panic!(
            "a TyEncodable MIR type changed its rmeta wire layout without a METADATA_VERSION \
             bump.\n\
             MIR bodies ride crate metadata, so an older driver or sysroot with the SAME \
             METADATA_VERSION would decode this layout mid-stream and ICE instead of refusing \
             the crate with E0514 (the f24fdb2fdb `StmtDebugInfo` ICE).\n\
             Fix: bump METADATA_VERSION in compiler/rustc_metadata/src/rmeta/mod.rs (currently \
             {METADATA_VERSION}) in the SAME commit, then re-record with \
             `./x.py test compiler/rustc_metadata --bless`. --bless refuses without the bump.\n\
             First difference:\n{}",
            first_difference(GOLDEN, &layout),
        ),
        Verdict::NeedsRerecord | Verdict::CorpusGrew if bless_requested() => {
            let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(GOLDEN_PATH);
            std::fs::write(&path, render_golden(METADATA_VERSION, &layout))
                .unwrap_or_else(|e| panic!("cannot bless {}: {e}", path.display()));
        }
        Verdict::NeedsRerecord => panic!(
            "METADATA_VERSION is {METADATA_VERSION} but {GOLDEN_PATH} was recorded under {}; \
             re-record it with `./x.py test compiler/rustc_metadata --bless` so the next layout \
             change is measured against this version",
            parse_golden(GOLDEN).0,
        ),
        Verdict::CorpusGrew => panic!(
            "the MIR layout corpus grew (every recorded line is unchanged); record the new lines \
             with `./x.py test compiler/rustc_metadata --bless`"
        ),
    }
}

#[test]
fn golden_verdicts_cover_the_f24fdb2fdb_shape() {
    // The protocol itself, pinned independently of today's layout: a changed
    // layout under an unchanged version is the unblessable verdict.
    let golden = render_golden(12, "Statement/Nop: span u32:1 u8:10 usize:0\n");
    assert_eq!(judge(12, "Statement/Nop: span u32:1 u8:10 usize:0\n", &golden), Verdict::Matches);
    // f24fdb2fdb: a trailing `bool` on `Statement`, header still 12.
    assert_eq!(
        judge(12, "Statement/Nop: span u32:1 u8:10 usize:0 u8:0\n", &golden),
        Verdict::NeedsBump
    );
    // 47236131c9: the owed bump, golden not yet re-recorded.
    assert_eq!(
        judge(13, "Statement/Nop: span u32:1 u8:10 usize:0 u8:0\n", &golden),
        Verdict::NeedsRerecord
    );
    // A new sample beside an unchanged one only grows the corpus...
    assert_eq!(
        judge(12, "Statement/Nop: span u32:1 u8:10 usize:0\nvariant_count X: 2\n", &golden),
        Verdict::CorpusGrew
    );
    // ...but growth cannot launder a change to a recorded line, and dropping a
    // recorded line is a change too.
    assert_eq!(
        judge(12, "Statement/Nop: span u32:1 u8:10 usize:0 u8:0\nvariant_count X: 2\n", &golden),
        Verdict::NeedsBump
    );
    assert_eq!(judge(12, "variant_count X: 2\n", &golden), Verdict::NeedsBump);
}

/// The names of every enum under `rustc_middle/src/mir` whose derive list
/// names an encoder (`TyEncodable`, `Encodable`, `Encodable_NoContext`).
fn encodable_mir_enums_in_source() -> Vec<String> {
    fn visit(dir: &std::path::Path, out: &mut Vec<String>) {
        let mut entries: Vec<_> = std::fs::read_dir(dir)
            .unwrap_or_else(|e| panic!("cannot read {}: {e}", dir.display()))
            .map(|entry| entry.unwrap().path())
            .collect();
        entries.sort();
        for path in entries {
            if path.is_dir() {
                visit(&path, out);
            } else if path.extension().is_some_and(|ext| ext == "rs") {
                scan(&std::fs::read_to_string(&path).unwrap(), out);
            }
        }
    }
    fn scan(source: &str, out: &mut Vec<String>) {
        // Attributes accumulate until the item they decorate; a doc comment,
        // blank line or other attribute between them does not reset them.
        let mut attrs = String::new();
        let mut depth = 0i32;
        for line in source.lines() {
            let line = line.trim();
            if depth > 0 || line.starts_with("#[") {
                depth += line.matches('[').count() as i32 - line.matches(']').count() as i32;
                attrs.push_str(line);
                continue;
            }
            if line.is_empty() || line.starts_with("//") {
                continue;
            }
            let item = line.strip_prefix("pub ").or_else(|| {
                line.strip_prefix("pub(").and_then(|rest| rest.split_once(") ")).map(|(_, r)| r)
            });
            let item = item.unwrap_or(line);
            let encodes =
                ["TyEncodable", "Encodable", "Encodable_NoContext"].iter().any(|derive| {
                    attrs.split(|c: char| !c.is_alphanumeric() && c != '_').any(|w| w == *derive)
                });
            if let Some(rest) = item.strip_prefix("enum ")
                && encodes
            {
                let name: String =
                    rest.chars().take_while(|c| c.is_alphanumeric() || *c == '_').collect();
                out.push(name);
            }
            attrs.clear();
        }
    }
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../rustc_middle/src/mir");
    let mut out = Vec::new();
    visit(&root, &mut out);
    out
}

/// Encodable enums under `rustc_middle/src/mir` that are private to their
/// module, so `variant_count` cannot name them from this crate. Each entry says
/// what, if anything, still pins it; none of them has its variant count pinned.
const UNNAMEABLE_ENUMS: &[(&str, &str)] = &[
    (
        "AllocDiscriminant",
        "private to `mir::interpret`; written only by `specialized_encode_alloc_id`, which \
         needs a `TyCtxt` to look the allocation up, so nothing here pins it",
    ),
    (
        "InitMaskBlocks",
        "private to `mir::interpret::allocation::init_mask`; the `Allocation/*` samples pin \
         its `Lazy` tag and payload, not its variant count",
    ),
];

#[test]
fn every_tyencodable_mir_enum_is_counted() {
    let mut counted: Vec<&str> = variant_counts().into_iter().map(|(name, _)| name).collect();
    let in_source = encodable_mir_enums_in_source();
    // The scan itself must see the enums it exists to find, or an empty scan
    // (moved directory, changed derive spelling) would pass vacuously.
    for known in ["StatementKind", "TerminatorKind", "StmtDebugInfo", "TrustStatus"] {
        assert!(in_source.iter().any(|n| n == known), "scan missed {known}: {in_source:?}");
    }
    // An exemption must name an enum that still exists, or it is dead weight
    // that would silently exempt a future enum of the same name.
    for (name, why) in UNNAMEABLE_ENUMS {
        assert!(
            in_source.iter().any(|n| n == name),
            "UNNAMEABLE_ENUMS lists {name} ({why}), but the scan no longer finds it; drop the entry"
        );
        assert!(!counted.contains(name), "{name} is both counted and listed as unnameable");
    }
    counted.extend(UNNAMEABLE_ENUMS.iter().map(|(name, _)| *name));
    let missing: Vec<&String> =
        in_source.iter().filter(|name| !counted.contains(&name.as_str())).collect();
    assert!(
        missing.is_empty(),
        "these TyEncodable MIR enums are not in `variant_counts`, so a variant appended to them \
         would ride rmeta unpinned: {missing:?}. Add each, then record it with \
         `./x.py test compiler/rustc_metadata --bless` (an addition needs no METADATA_VERSION bump)"
    );
}

#[test]
fn the_recorder_sees_a_statement_field_the_derive_emits() {
    // The sensitivity the golden relies on, measured on today's `Statement`:
    // `trust_modular_arith` is the last token of a `Statement` trace, so a
    // field of the f24fdb2fdb kind is visible to this recorder.
    let plain = trace(&stmt(StatementKind::Nop));
    let modular = trace(&Statement::new_trust_modular_arith(si(), StatementKind::Nop));
    assert!(plain.ends_with("u8:0"), "{plain}");
    assert!(modular.ends_with("u8:1"), "{modular}");
    assert_eq!(plain.split(' ').count(), modular.split(' ').count());
}

// Trust: step 2 increment 6 (6.2) — a trust-ir entry crosses rmeta as its length plus its RAW
// bytes (one `emit_raw_bytes`, not the element-by-element `Vec<u8>` path), and decodes back
// exactly. The bytes are opaque here: their own magic and schema are the entry decoder's.
#[test]
fn trust_ir_entry_blob_is_its_length_plus_raw_bytes() {
    use rustc_middle::middle::trust_ir_entry::TrustIrEntryBlob;
    use rustc_serialize::Decodable;
    use rustc_serialize::opaque::mem_encoder::MemEncoder;
    use rustc_serialize::opaque::{MAGIC_END_BYTES, MemDecoder};

    let blob = TrustIrEntryBlob(vec![0x54, 0x00, 0xff, 0x7f]);
    assert_eq!(trace(&blob), "usize:4 bytes:[54, 00, ff, 7f]");
    assert_eq!(trace(&TrustIrEntryBlob::default()), "usize:0 bytes:[]");
    let mut encoder = MemEncoder::new();
    blob.encode(&mut encoder);
    let mut bytes = encoder.finish();
    bytes.extend_from_slice(MAGIC_END_BYTES);
    let mut decoder = MemDecoder::new(&bytes, 0).expect("footer");
    assert_eq!(TrustIrEntryBlob::decode(&mut decoder), blob);
}
