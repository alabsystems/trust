// t216_cg_home_coherence.rs — ONE rule for where a local's value lives in the
// MIR codegen lane (`lower.rs`), checked by executing a writer x reader x kind
// matrix against the values Rust gives.
//
// Trust (ticket 216 cg-bridge, review 4): a local used to live in two places at
// once — an SSA value (`local_values`) and, once its address was needed, a stack
// slot (`local_stack_slots`). A direct write updated the SSA value, a write
// through an address or a projection updated the slot, and each read picked one
// of the two by its own rule. Rounds 2-4 patched single paths, and each patch
// opened a new silent miscompile (the skeptic's probes at the end of this file).
// The rule `lower.rs` now keeps is the one this matrix states:
//
//   a local that has a stack HOME (every tuple/ADT/array local, and every local
//   whose address is taken anywhere in the body) is MEMORY-ONLY: every write to
//   it stores into the home, every read of it loads from the home, and a place
//   through a pointer starts from the pointer's CURRENT value (loaded from the
//   pointer's own home when it has one). An aggregate value is carried as the
//   ADDRESS of its bytes (trust-cg ISel's convention), so a whole-aggregate
//   write is a byte copy, never a `Load`/`Store` of a struct type.
//
// Every case below is a `fn() -> u64` lowered by the real backend, emitted as a
// Mach-O object, linked with a C driver and run on the host CPU
// (aarch64-apple-darwin; elsewhere only the lowering is checked, and the test
// says so). Each case runs in its own process, so a crash is one case's
// failure, not the whole table's. The expected value of every case is computed
// by hand below from the Rust semantics of the program the case builds.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fs;
use std::process::Command;

use trust_cg_bridge::codegen_backend::TrustCgCodegenBackend;
use trust_types::{
    AdtKind, AggregateKind, BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place,
    Projection, Rvalue, SourceSpan, Statement, Terminator, Ty, VariantDef, VerifiableBody,
    VerifiableFunction,
};

// ---------------------------------------------------------------------------
// Types.
// ---------------------------------------------------------------------------

fn pair_ty() -> Ty {
    Ty::Tuple(vec![Ty::u64(), Ty::u64()])
}

/// `enum E { A(u64) = 3, B(u64) = 7 }` as the extractor shapes it:
/// `[__tag: i64, __v0_0: u64, __v1_0: u64]`.
fn enum_ty() -> Ty {
    let variants = [("A", 3i128), ("B", 7i128)];
    let mut fields = vec![("__tag".to_string(), Ty::i64())];
    for index in 0..variants.len() {
        fields.push((format!("__v{index}_0"), Ty::u64()));
    }
    Ty::Adt {
        adt_kind: Some(AdtKind::Enum),
        layout: None,
        name: "t216h::E".into(),
        fields: fields.into(),
        variants: variants
            .iter()
            .map(|(name, discriminant)| VariantDef {
                name: (*name).into(),
                discriminant: *discriminant,
                fields: vec![("0".into(), Ty::u64())],
            })
            .collect::<Vec<_>>()
            .into(),
        disc_index_safe: true,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    }
}

/// `struct S { a: u64, e: E }`.
fn struct_ty() -> Ty {
    Ty::Adt {
        adt_kind: Some(AdtKind::Struct),
        layout: None,
        name: "t216h::S".into(),
        fields: vec![("a".to_string(), Ty::u64()), ("e".to_string(), enum_ty())].into(),
        variants: Vec::new().into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    }
}

fn raw_mut(pointee: Ty) -> Ty {
    Ty::RawPtr { mutable: true, pointee: Box::new(pointee) }
}

fn raw_const(pointee: Ty) -> Ty {
    Ty::RawPtr { mutable: false, pointee: Box::new(pointee) }
}

/// The declared discriminant of `E`'s variant `index`.
fn disc(variant: usize) -> u64 {
    [3, 7][variant]
}

// ---------------------------------------------------------------------------
// MIR spelling helpers.
// ---------------------------------------------------------------------------

fn at(local: usize, projections: Vec<Projection>) -> Place {
    Place { local, projections }
}

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}

fn u64c(value: u64) -> Operand {
    Operand::Constant(ConstValue::Uint(u128::from(value), 64))
}

fn copy(place: Place) -> Rvalue {
    Rvalue::Use(Operand::Copy(place))
}

fn tuple(operands: Vec<Operand>) -> Rvalue {
    Rvalue::Aggregate(AggregateKind::Tuple, operands)
}

fn adt(name: &str, variant: usize, operands: Vec<Operand>) -> Rvalue {
    Rvalue::Aggregate(
        AggregateKind::Adt { name: name.into(), variant, active_field: None, args: None },
        operands,
    )
}

fn enum_value(variant: usize, payload: u64) -> Rvalue {
    adt("t216h::E", variant, vec![u64c(payload)])
}

const F0: Projection = Projection::Field(0);
const F1: Projection = Projection::Field(1);
const DEREF: Projection = Projection::Deref;

fn downcast(variant: usize) -> Projection {
    Projection::Downcast(variant)
}

/// One straight-line step of a case: a statement, or a call that ends its block.
#[derive(Clone)]
enum Item {
    S(Statement),
    Call { func: String, args: Vec<Operand>, dest: Place },
}

/// A function's locals, `_0: u64` first; `new` hands out the next index.
struct Locals(Vec<Ty>);

impl Locals {
    fn new(&mut self, ty: Ty) -> usize {
        self.0.push(ty);
        self.0.len() - 1
    }
}

/// Lays items out into blocks: a call ends the open block and continues in a
/// fresh one.
struct Blocks {
    done: Vec<BasicBlock>,
    open: usize,
    stmts: Vec<Statement>,
    next: usize,
}

impl Blocks {
    fn new() -> Self {
        Self { done: Vec::new(), open: 0, stmts: Vec::new(), next: 1 }
    }

    fn fresh(&mut self) -> usize {
        self.next += 1;
        self.next - 1
    }

    fn push(&mut self, items: &[Item]) {
        for item in items {
            match item {
                Item::S(statement) => self.stmts.push(statement.clone()),
                Item::Call { func, args, dest } => {
                    let target = self.fresh();
                    self.finish(Terminator::Call {
                        is_unsafe_sig: false,
                        callee_identity: None,
                        callee_key: None,
                        is_foreign: false,
                        func: func.clone(),
                        args: args.clone(),
                        dest: dest.clone(),
                        target: Some(BlockId(target)),
                        span: SourceSpan::default(),
                        atomic: None,
                        unwind: trust_types::UnwindEdge::Unreachable,
                    });
                    self.open = target;
                }
            }
        }
    }

    fn finish(&mut self, terminator: Terminator) {
        self.done.push(BasicBlock {
            id: BlockId(self.open),
            stmts: std::mem::take(&mut self.stmts),
            terminator,
        });
    }
}

fn function(
    name: &str,
    locals: Vec<Ty>,
    blocks: Vec<BasicBlock>,
    arg_count: usize,
    return_ty: Ty,
) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("t216h::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: locals
                .into_iter()
                .enumerate()
                .map(|(index, ty)| LocalDecl { index, ty, name: None })
                .collect(),
            blocks,
            arg_count,
            return_ty,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

// ---------------------------------------------------------------------------
// The matrix: local kinds, their states, writers, readers and CFG shapes.
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq)]
enum Kind {
    Scalar,
    Pair,
    Enum,
    Struct,
}

impl Kind {
    fn ty(self) -> Ty {
        match self {
            Kind::Scalar => Ty::u64(),
            Kind::Pair => pair_ty(),
            Kind::Enum => enum_ty(),
            Kind::Struct => struct_ty(),
        }
    }

    fn tag(self) -> &'static str {
        match self {
            Kind::Scalar => "scalar",
            Kind::Pair => "pair",
            Kind::Enum => "enum",
            Kind::Struct => "struct",
        }
    }
}

/// The Rust value of the local under test.
#[derive(Clone, Copy, Debug)]
enum State {
    Scalar(u64),
    Pair(u64, u64),
    /// (variant index, payload)
    Enum(usize, u64),
    /// (a, variant index of e, payload of e)
    Struct(u64, usize, u64),
}

/// Emit the statements that write `state` into `place` (a whole write).
fn build_into(place: Place, state: State, locals: &mut Locals) -> Vec<Item> {
    match state {
        State::Scalar(v) => vec![Item::S(assign(place, Rvalue::Use(u64c(v))))],
        State::Pair(a, b) => vec![Item::S(assign(place, tuple(vec![u64c(a), u64c(b)])))],
        State::Enum(variant, payload) => {
            vec![Item::S(assign(place, enum_value(variant, payload)))]
        }
        State::Struct(a, variant, payload) => {
            let e = locals.new(enum_ty());
            vec![
                Item::S(assign(Place::local(e), enum_value(variant, payload))),
                Item::S(assign(
                    place,
                    adt("t216h::S", 0, vec![u64c(a), Operand::Move(Place::local(e))]),
                )),
            ]
        }
    }
}

fn initial(kind: Kind) -> State {
    match kind {
        Kind::Scalar => State::Scalar(10),
        Kind::Pair => State::Pair(1, 2),
        Kind::Enum => State::Enum(0, 4),
        Kind::Struct => State::Struct(1, 0, 4),
    }
}

/// A second value of the same kind, different from `initial` in every lane.
fn other(kind: Kind) -> State {
    match kind {
        Kind::Scalar => State::Scalar(20),
        Kind::Pair => State::Pair(3, 4),
        Kind::Enum => State::Enum(1, 8),
        Kind::Struct => State::Struct(5, 1, 8),
    }
}

#[derive(Clone, Copy, Debug)]
enum Writer {
    /// `x = <other>` / `x = copy u`.
    Whole,
    /// A write to a field of `x` itself.
    Field,
    /// `p = &raw mut x`, then a write through `p`.
    RawMut,
    /// `p = &raw mut o; pp = &raw mut p; *pp = &raw mut x`, then a write
    /// through `p` — p's current value was written through its OWN address.
    Reassigned,
    /// `s = (&raw mut x, 0)`, then a write through `s.0`.
    InAggregate,
    /// `(x as B).0 = 6; SetDiscriminant(x, B)` (on `x.e` for the struct).
    SetDiscriminant,
    /// An aggregate built straight into `x` or into a field of it.
    Build,
    /// `set(&raw mut x)`: a callee writes through the pointer argument.
    Callee,
}

impl Writer {
    const ALL: [Writer; 8] = [
        Writer::Whole,
        Writer::Field,
        Writer::RawMut,
        Writer::Reassigned,
        Writer::InAggregate,
        Writer::SetDiscriminant,
        Writer::Build,
        Writer::Callee,
    ];

    fn tag(self) -> &'static str {
        match self {
            Writer::Whole => "whole",
            Writer::Field => "field",
            Writer::RawMut => "rawmut",
            Writer::Reassigned => "reassigned",
            Writer::InAggregate => "inaggr",
            Writer::SetDiscriminant => "setdisc",
            Writer::Build => "build",
            Writer::Callee => "callee",
        }
    }
}

/// The name of the helper `fn set_<kind>(p: *mut K)` a `Callee` writer calls,
/// and the write it performs on `*p` (the same write `RawMut` performs).
fn setter_name(kind: Kind) -> String {
    format!("t216h_set_{}", kind.tag())
}

/// Which pointer write the setter performs: a field write for every kind
/// (the enum's `RawMut` spelling is a whole write, so it takes the payload
/// write instead).
fn setter_writer(kind: Kind) -> Writer {
    if kind == Kind::Enum { Writer::Reassigned } else { Writer::RawMut }
}

fn id_name(kind: Kind) -> String {
    format!("t216h_id_{}", kind.tag())
}

/// The write a pointer-based writer performs through `ptr_place` (a place that
/// evaluates to `*mut K`), and the state it leaves in the pointee.
fn write_through(
    kind: Kind,
    writer: Writer,
    ptr: Vec<Projection>,
    ptr_local: usize,
    locals: &mut Locals,
) -> (Vec<Item>, State) {
    let pointee = |suffix: &[Projection]| {
        let mut projections = ptr.clone();
        projections.push(DEREF);
        projections.extend_from_slice(suffix);
        at(ptr_local, projections)
    };
    match (kind, writer) {
        (Kind::Scalar, _) => {
            (vec![Item::S(assign(pointee(&[]), Rvalue::Use(u64c(42))))], State::Scalar(42))
        }
        (Kind::Pair, Writer::Reassigned) => {
            (vec![Item::S(assign(pointee(&[F0]), Rvalue::Use(u64c(5))))], State::Pair(5, 2))
        }
        (Kind::Pair, Writer::InAggregate) => {
            (vec![Item::S(assign(pointee(&[F1]), Rvalue::Use(u64c(7))))], State::Pair(1, 7))
        }
        (Kind::Pair, _) => {
            (vec![Item::S(assign(pointee(&[F1]), Rvalue::Use(u64c(9))))], State::Pair(1, 9))
        }
        (Kind::Enum, Writer::RawMut | Writer::InAggregate) => {
            // A WHOLE enum written through the pointer: `f = B(8); *p = copy f`.
            let f = locals.new(enum_ty());
            (
                vec![
                    Item::S(assign(Place::local(f), enum_value(1, 8))),
                    Item::S(assign(pointee(&[]), copy(Place::local(f)))),
                ],
                State::Enum(1, 8),
            )
        }
        (Kind::Enum, _) => (
            vec![Item::S(assign(pointee(&[downcast(0), F0]), Rvalue::Use(u64c(9))))],
            State::Enum(0, 9),
        ),
        (Kind::Struct, Writer::RawMut) => (
            vec![Item::S(assign(pointee(&[F1, downcast(0), F0]), Rvalue::Use(u64c(6))))],
            State::Struct(1, 0, 6),
        ),
        (Kind::Struct, Writer::Reassigned) => {
            (vec![Item::S(assign(pointee(&[F0]), Rvalue::Use(u64c(7))))], State::Struct(7, 0, 4))
        }
        (Kind::Struct, Writer::InAggregate) => {
            (vec![Item::S(assign(pointee(&[F0]), Rvalue::Use(u64c(8))))], State::Struct(8, 0, 4))
        }
        (Kind::Struct, _) => {
            (vec![Item::S(assign(pointee(&[F0]), Rvalue::Use(u64c(9))))], State::Struct(9, 0, 4))
        }
    }
}

/// The writer's statements on local `x`, and the state `x` holds after them;
/// `None` where the writer has no spelling for the kind.
fn writer_items(
    kind: Kind,
    writer: Writer,
    x: usize,
    locals: &mut Locals,
) -> Option<(Vec<Item>, State)> {
    let ty = kind.ty();
    Some(match writer {
        Writer::Whole => match kind {
            Kind::Scalar => (vec![Item::S(assign(Place::local(x), Rvalue::Use(u64c(42))))], {
                State::Scalar(42)
            }),
            _ => {
                let u = locals.new(ty);
                let mut items = build_into(Place::local(u), other(kind), locals);
                items.push(Item::S(assign(Place::local(x), copy(Place::local(u)))));
                (items, other(kind))
            }
        },
        Writer::Field => match kind {
            Kind::Scalar => return None,
            Kind::Pair => {
                (vec![Item::S(assign(at(x, vec![F1]), Rvalue::Use(u64c(9))))], State::Pair(1, 9))
            }
            Kind::Enum => (
                vec![Item::S(assign(at(x, vec![downcast(0), F0]), Rvalue::Use(u64c(9))))],
                State::Enum(0, 9),
            ),
            Kind::Struct => (
                vec![Item::S(assign(at(x, vec![F0]), Rvalue::Use(u64c(9))))],
                State::Struct(9, 0, 4),
            ),
        },
        Writer::RawMut => {
            let p = locals.new(raw_mut(ty));
            let mut items =
                vec![Item::S(assign(Place::local(p), Rvalue::AddressOf(true, Place::local(x))))];
            let (write, state) = write_through(kind, writer, vec![], p, locals);
            items.extend(write);
            (items, state)
        }
        Writer::Reassigned => {
            let o = locals.new(ty.clone());
            let p = locals.new(raw_mut(ty.clone()));
            let pp = locals.new(raw_mut(raw_mut(ty)));
            let mut items = build_into(Place::local(o), other(kind), locals);
            items.extend([
                Item::S(assign(Place::local(p), Rvalue::AddressOf(true, Place::local(o)))),
                Item::S(assign(Place::local(pp), Rvalue::AddressOf(true, Place::local(p)))),
                Item::S(assign(at(pp, vec![DEREF]), Rvalue::AddressOf(true, Place::local(x)))),
            ]);
            let (write, state) = write_through(kind, writer, vec![], p, locals);
            items.extend(write);
            (items, state)
        }
        Writer::InAggregate => {
            let r = locals.new(raw_mut(ty.clone()));
            let s = locals.new(Ty::Tuple(vec![raw_mut(ty), Ty::u64()]));
            let mut items = vec![
                Item::S(assign(Place::local(r), Rvalue::AddressOf(true, Place::local(x)))),
                Item::S(assign(
                    Place::local(s),
                    tuple(vec![Operand::Move(Place::local(r)), u64c(0)]),
                )),
            ];
            let (write, state) = write_through(kind, writer, vec![F0], s, locals);
            items.extend(write);
            (items, state)
        }
        Writer::SetDiscriminant => {
            let base = match kind {
                Kind::Enum => vec![],
                Kind::Struct => vec![F1],
                Kind::Scalar | Kind::Pair => return None,
            };
            let mut payload = base.clone();
            payload.extend([downcast(1), F0]);
            let state = match kind {
                Kind::Enum => State::Enum(1, 6),
                _ => State::Struct(1, 1, 6),
            };
            (
                vec![
                    Item::S(assign(at(x, payload), Rvalue::Use(u64c(6)))),
                    Item::S(Statement::SetDiscriminant { place: at(x, base), variant_index: 1 }),
                ],
                state,
            )
        }
        Writer::Build => match kind {
            Kind::Scalar => return None,
            Kind::Pair => (
                vec![Item::S(assign(Place::local(x), tuple(vec![u64c(5), u64c(6)])))],
                State::Pair(5, 6),
            ),
            Kind::Enum => {
                (vec![Item::S(assign(Place::local(x), enum_value(1, 8)))], State::Enum(1, 8))
            }
            // rustc's `x.e = E::B(8)`: `(_x.1: E) = E::B(const 8)`.
            Kind::Struct => {
                (vec![Item::S(assign(at(x, vec![F1]), enum_value(1, 8)))], State::Struct(1, 1, 8))
            }
        },
        Writer::Callee => {
            let p = locals.new(raw_mut(ty.clone()));
            let unit = locals.new(Ty::Unit);
            // The state the callee's write leaves (the helper performs it).
            let mut scratch = Locals(vec![Ty::Unit, raw_mut(ty)]);
            let (_, state) = write_through(kind, setter_writer(kind), vec![], 1, &mut scratch);
            (
                vec![
                    Item::S(assign(Place::local(p), Rvalue::AddressOf(true, Place::local(x)))),
                    Item::Call {
                        func: setter_name(kind),
                        args: vec![Operand::Move(Place::local(p))],
                        dest: Place::local(unit),
                    },
                ],
                state,
            )
        }
    })
}

#[derive(Clone, Copy, Debug)]
enum Reader {
    /// Fields of `x` read by projection (the payload lane for the enum).
    Field,
    /// `discriminant(x)` (of `x.e` for the struct).
    Discriminant,
    /// `v = copy x`, then every lane of `v`.
    Copy,
    /// `q = &raw const x` taken BEFORE the writer, then every lane of `*q`.
    Pointer,
    /// `u = id(copy x)` through a real call, then every lane of `u`.
    Call,
}

impl Reader {
    const ALL: [Reader; 5] =
        [Reader::Field, Reader::Discriminant, Reader::Copy, Reader::Pointer, Reader::Call];

    fn tag(self) -> &'static str {
        match self {
            Reader::Field => "field",
            Reader::Discriminant => "disc",
            Reader::Copy => "copy",
            Reader::Pointer => "ptr",
            Reader::Call => "call",
        }
    }
}

/// `dest = a * scale + b` (all u64).
fn mul_add(dest: Place, a: usize, scale: u64, b: usize, locals: &mut Locals) -> Vec<Item> {
    let m = locals.new(Ty::u64());
    vec![
        Item::S(assign(
            Place::local(m),
            Rvalue::BinaryOp(BinOp::Mul, Operand::Copy(Place::local(a)), u64c(scale)),
        )),
        Item::S(assign(
            dest,
            Rvalue::BinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local(m)),
                Operand::Copy(Place::local(b)),
            ),
        )),
    ]
}

/// `t = copy place` into a fresh u64 local.
fn read_u64(place: Place, locals: &mut Locals, items: &mut Vec<Item>) -> usize {
    let t = locals.new(Ty::u64());
    items.push(Item::S(assign(Place::local(t), copy(place))));
    t
}

/// `t = discriminant(place) as u64` into a fresh u64 local.
fn read_disc(place: Place, locals: &mut Locals, items: &mut Vec<Item>) -> usize {
    let d = locals.new(Ty::isize());
    let t = locals.new(Ty::u64());
    items.push(Item::S(assign(Place::local(d), Rvalue::Discriminant(place))));
    items.push(Item::S(assign(
        Place::local(t),
        Rvalue::Cast(Operand::Copy(Place::local(d)), Ty::u64()),
    )));
    t
}

/// `_0 = <every lane of the value at base>`, encoded in one u64, with the
/// enum's payload read in the lane of `variant` (the case's final variant).
fn encode_all(
    base: &dyn Fn(&[Projection]) -> Place,
    kind: Kind,
    variant: usize,
    locals: &mut Locals,
) -> Vec<Item> {
    let mut items = Vec::new();
    match kind {
        Kind::Scalar => items.push(Item::S(assign(Place::local(0), copy(base(&[]))))),
        Kind::Pair => {
            let a = read_u64(base(&[F0]), locals, &mut items);
            let b = read_u64(base(&[F1]), locals, &mut items);
            items.extend(mul_add(Place::local(0), a, 100, b, locals));
        }
        Kind::Enum => {
            let d = read_disc(base(&[]), locals, &mut items);
            let p = read_u64(base(&[downcast(variant), F0]), locals, &mut items);
            items.extend(mul_add(Place::local(0), d, 1000, p, locals));
        }
        Kind::Struct => {
            let a = read_u64(base(&[F0]), locals, &mut items);
            let d = read_disc(base(&[F1]), locals, &mut items);
            let p = read_u64(base(&[F1, downcast(variant), F0]), locals, &mut items);
            let low = locals.new(Ty::u64());
            items.extend(mul_add(Place::local(low), d, 1000, p, locals));
            items.extend(mul_add(Place::local(0), a, 100_000, low, locals));
        }
    }
    items
}

fn encode_state(state: State) -> u64 {
    match state {
        State::Scalar(v) => v,
        State::Pair(a, b) => a * 100 + b,
        State::Enum(variant, payload) => disc(variant) * 1000 + payload,
        State::Struct(a, variant, payload) => a * 100_000 + disc(variant) * 1000 + payload,
    }
}

fn final_variant(state: State) -> usize {
    match state {
        State::Enum(variant, _) | State::Struct(_, variant, _) => variant,
        State::Scalar(_) | State::Pair(..) => 0,
    }
}

/// The reader's statements (after the writer) and the value Rust gives for
/// them; `prep` goes BEFORE the writer. `None` where the reader has no
/// spelling for the kind.
fn reader_items(
    kind: Kind,
    reader: Reader,
    x: usize,
    state: State,
    locals: &mut Locals,
    prep: &mut Vec<Item>,
) -> Option<(Vec<Item>, u64)> {
    let variant = final_variant(state);
    let direct = |suffix: &[Projection]| at(x, suffix.to_vec());
    Some(match reader {
        Reader::Field => match (kind, state) {
            (Kind::Scalar, _) => return None,
            (Kind::Pair, _) => (encode_all(&direct, kind, variant, locals), encode_state(state)),
            (Kind::Enum, State::Enum(_, payload)) => {
                let mut items = Vec::new();
                let p = read_u64(direct(&[downcast(variant), F0]), locals, &mut items);
                items.push(Item::S(assign(Place::local(0), copy(Place::local(p)))));
                (items, payload)
            }
            (Kind::Struct, State::Struct(a, _, payload)) => {
                let mut items = Vec::new();
                let av = read_u64(direct(&[F0]), locals, &mut items);
                let p = read_u64(direct(&[F1, downcast(variant), F0]), locals, &mut items);
                items.extend(mul_add(Place::local(0), av, 100_000, p, locals));
                (items, a * 100_000 + payload)
            }
            _ => unreachable!("state matches kind"),
        },
        Reader::Discriminant => {
            let place = match kind {
                Kind::Enum => direct(&[]),
                Kind::Struct => direct(&[F1]),
                Kind::Scalar | Kind::Pair => return None,
            };
            let mut items = Vec::new();
            let d = read_disc(place, locals, &mut items);
            items.push(Item::S(assign(Place::local(0), copy(Place::local(d)))));
            (items, disc(variant))
        }
        Reader::Copy => {
            let v = locals.new(kind.ty());
            let mut items = vec![Item::S(assign(Place::local(v), copy(Place::local(x))))];
            items.extend(encode_all(&|s: &[Projection]| at(v, s.to_vec()), kind, variant, locals));
            (items, encode_state(state))
        }
        Reader::Pointer => {
            let q = locals.new(raw_const(kind.ty()));
            prep.push(Item::S(assign(Place::local(q), Rvalue::AddressOf(false, Place::local(x)))));
            let through = |s: &[Projection]| {
                let mut projections = vec![DEREF];
                projections.extend_from_slice(s);
                at(q, projections)
            };
            (encode_all(&through, kind, variant, locals), encode_state(state))
        }
        Reader::Call => {
            let u = locals.new(kind.ty());
            let mut items = vec![Item::Call {
                func: id_name(kind),
                args: vec![Operand::Copy(Place::local(x))],
                dest: Place::local(u),
            }];
            items.extend(encode_all(&|s: &[Projection]| at(u, s.to_vec()), kind, variant, locals));
            (items, encode_state(state))
        }
    })
}

#[derive(Clone, Copy, Debug)]
enum Shape {
    /// Writer and reader in one block stream.
    Straight,
    /// The reader in the block a `goto` from the writer reaches.
    Goto,
    /// `switchInt(c = 1) -> [1: writer, otherwise: nothing]`, both joining at
    /// the reader: the join block has two predecessors.
    Join,
}

impl Shape {
    const ALL: [Shape; 3] = [Shape::Straight, Shape::Goto, Shape::Join];

    fn tag(self) -> &'static str {
        match self {
            Shape::Straight => "straight",
            Shape::Goto => "goto",
            Shape::Join => "join",
        }
    }
}

struct Case {
    function: VerifiableFunction,
    expected: u64,
}

fn case(kind: Kind, writer: Writer, reader: Reader, shape: Shape) -> Option<Case> {
    let mut locals = Locals(vec![Ty::u64()]);
    let x = locals.new(kind.ty());
    let mut pre = build_into(Place::local(x), initial(kind), &mut locals);
    let (write, state) = writer_items(kind, writer, x, &mut locals)?;
    let (read, expected) = reader_items(kind, reader, x, state, &mut locals, &mut pre)?;

    let mut blocks = Blocks::new();
    match shape {
        Shape::Straight => {
            blocks.push(&pre);
            blocks.push(&write);
            blocks.push(&read);
        }
        Shape::Goto => {
            blocks.push(&pre);
            blocks.push(&write);
            let next = blocks.fresh();
            blocks.finish(Terminator::Goto(BlockId(next)));
            blocks.open = next;
            blocks.push(&read);
        }
        Shape::Join => {
            let c = locals.new(Ty::u64());
            pre.push(Item::S(assign(Place::local(c), Rvalue::Use(u64c(1)))));
            blocks.push(&pre);
            let (then_block, else_block, join) = (blocks.fresh(), blocks.fresh(), blocks.fresh());
            blocks.finish(Terminator::SwitchInt {
                discr: Operand::Copy(Place::local(c)),
                targets: vec![(1, BlockId(then_block))],
                otherwise: BlockId(else_block),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            });
            blocks.open = then_block;
            blocks.push(&write);
            blocks.finish(Terminator::Goto(BlockId(join)));
            blocks.open = else_block;
            blocks.finish(Terminator::Goto(BlockId(join)));
            blocks.open = join;
            blocks.push(&read);
        }
    }
    blocks.finish(Terminator::Return);
    let name = format!("hc_{}_{}_{}_{}", kind.tag(), writer.tag(), reader.tag(), shape.tag());
    Some(Case { function: function(&name, locals.0, blocks.done, 0, Ty::u64()), expected })
}

/// `fn id(x: K) -> K { x }` and `fn set(p: *mut K) { <the RawMut write> }` for
/// every kind: the callees the `Call` reader and the `Callee` writer reach.
fn helpers() -> Vec<VerifiableFunction> {
    let mut out = Vec::new();
    for kind in [Kind::Scalar, Kind::Pair, Kind::Enum, Kind::Struct] {
        out.push(function(
            &id_name(kind),
            vec![kind.ty(), kind.ty()],
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![assign(Place::local(0), copy(Place::local(1)))],
                terminator: Terminator::Return,
            }],
            1,
            kind.ty(),
        ));
        let mut locals = Locals(vec![Ty::Unit, raw_mut(kind.ty())]);
        let (write, _) = write_through(kind, setter_writer(kind), vec![], 1, &mut locals);
        let stmts = write
            .into_iter()
            .map(|item| match item {
                Item::S(statement) => statement,
                Item::Call { .. } => unreachable!("a pointer write has no call"),
            })
            .collect();
        out.push(function(
            &setter_name(kind),
            locals.0,
            vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
            1,
            Ty::Unit,
        ));
    }
    out
}

fn matrix() -> Vec<Case> {
    let mut cases = Vec::new();
    for kind in [Kind::Scalar, Kind::Pair, Kind::Enum, Kind::Struct] {
        for writer in Writer::ALL {
            for reader in Reader::ALL {
                for shape in Shape::ALL {
                    if let Some(c) = case(kind, writer, reader, shape) {
                        cases.push(c);
                    }
                }
            }
        }
    }
    cases
}

// ---------------------------------------------------------------------------
// Native execution, one process per case.
// ---------------------------------------------------------------------------

fn backend() -> TrustCgCodegenBackend {
    TrustCgCodegenBackend::host()
}

#[derive(Debug)]
enum Outcome {
    Ok,
    Wrong(u64),
    Refused(String),
    Crashed(String),
    NotRun,
}

/// Lower, emit, link and run every case; one `(name, expected, outcome)` per case.
fn run(cases: &[Case], helpers: &[VerifiableFunction]) -> Vec<(String, u64, Outcome)> {
    let native = cfg!(all(target_os = "macos", target_arch = "aarch64"));
    let directory = tempfile::TempDir::new().expect("temporary link directory");
    let mut helper_objects = Vec::new();
    let mut helper_errors = Vec::new();
    let emit = |f: &VerifiableFunction| -> Result<Vec<u8>, String> {
        let lir = backend().lower_function(f).map_err(|e| format!("lower: {e}"))?;
        let mut objects = backend().emit_objects(&[lir]).map_err(|e| format!("emit: {e}"))?;
        Ok(objects.remove(0).1)
    };
    for helper in helpers {
        match emit(helper) {
            Ok(object) => helper_objects.push((helper.name.clone(), object)),
            Err(e) => helper_errors.push((helper.name.clone(), e)),
        }
    }
    let mut outcomes: Vec<(String, u64, Outcome)> = Vec::new();
    let mut runnable = Vec::new();
    for (index, c) in cases.iter().enumerate() {
        let name = c.function.name.clone();
        let uses =
            |helper: &str| {
                c.function.body.blocks.iter().any(
                    |b| matches!(&b.terminator, Terminator::Call { func, .. } if func == helper),
                )
            };
        if let Some((helper, e)) = helper_errors.iter().find(|(h, _)| uses(h)) {
            outcomes.push((name, c.expected, Outcome::Refused(format!("helper {helper}: {e}"))));
            continue;
        }
        match emit(&c.function) {
            Ok(object) => {
                let path = directory.path().join(format!("{name}.o"));
                fs::write(&path, object).expect("write object");
                runnable.push((index, path));
                outcomes.push((name, c.expected, Outcome::NotRun));
            }
            Err(e) => outcomes.push((name, c.expected, Outcome::Refused(e))),
        }
    }
    if !native {
        eprintln!("SKIP native execution: requires an aarch64-apple-darwin host");
        return outcomes;
    }
    let mut object_paths = Vec::new();
    for (name, object) in &helper_objects {
        let path = directory.path().join(format!("{name}.o"));
        fs::write(&path, object).expect("write helper object");
        object_paths.push(path);
    }
    let mut decls = String::new();
    let mut table = String::new();
    for (index, path) in &runnable {
        let name = &cases[*index].function.name;
        decls.push_str(&format!("extern uint64_t {name}(void);\n"));
        table.push_str(&format!("  {name},\n"));
        object_paths.push(path.clone());
    }
    let driver_path = directory.path().join("driver.c");
    let executable_path = directory.path().join("t216h");
    fs::write(
        &driver_path,
        format!(
            "#include <stdint.h>\n#include <stdio.h>\n#include <stdlib.h>\n{decls}\
             static uint64_t (*const table[])(void) = {{\n{table}  0\n}};\n\
             int main(int argc, char **argv) {{\n  (void)argc;\n  \
             printf(\"%llu\\n\", (unsigned long long)table[atoi(argv[1])]());\n  return 0;\n}}\n"
        ),
    )
    .expect("write C driver");
    let linked = Command::new("cc")
        .arg(&driver_path)
        .args(&object_paths)
        .arg("-o")
        .arg(&executable_path)
        .output()
        .expect("invoke cc");
    assert!(
        linked.status.success(),
        "native link failed: {}",
        String::from_utf8_lossy(&linked.stderr)
    );
    for (slot, (index, _)) in runnable.iter().enumerate() {
        let Some(ran) = run_bounded(&executable_path, slot) else {
            outcomes[*index].2 = Outcome::Crashed(format!("no exit within {PROBE_DEADLINE:?}"));
            continue;
        };
        let outcome = if !ran.status.success() {
            Outcome::Crashed(format!("{:?}", ran.status))
        } else {
            let value: u64 = String::from_utf8_lossy(&ran.stdout)
                .trim()
                .parse()
                .expect("the driver prints one u64");
            if value == cases[*index].expected { Outcome::Ok } else { Outcome::Wrong(value) }
        };
        outcomes[*index].2 = outcome;
    }
    outcomes
}

/// How long one probe may run. A case that loops forever (a loop whose
/// counter lives where the lowering does not look) is a failure of that case,
/// not a hung test; a minute is a hang detector, not a latency budget.
const PROBE_DEADLINE: std::time::Duration = std::time::Duration::from_secs(60);

/// Run probe `slot`, or `None` when it has not exited by `PROBE_DEADLINE`
/// (it is then killed with `SIGKILL`, which writes no crash report).
fn run_bounded(executable: &std::path::Path, slot: usize) -> Option<std::process::Output> {
    let mut child = Command::new(executable)
        .arg(slot.to_string())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("run one probe");
    let start = std::time::Instant::now();
    loop {
        if child.try_wait().expect("poll one probe").is_some() {
            return Some(child.wait_with_output().expect("collect one probe"));
        }
        if start.elapsed() > PROBE_DEADLINE {
            let _ = child.kill();
            let _ = child.wait();
            return None;
        }
        std::thread::sleep(std::time::Duration::from_millis(20));
    }
}

/// Print every case as a `CASE <name> <status>` line (the table the commit
/// message counts) and fail on any case that is not `ok`.
fn report(outcomes: &[(String, u64, Outcome)]) {
    let mut failures = Vec::new();
    for (name, expected, outcome) in outcomes {
        let status = match outcome {
            Outcome::Ok => "ok".to_string(),
            Outcome::Wrong(got) => format!("WRONG got {got} want {expected}"),
            Outcome::Refused(e) => format!("REFUSED {}", e.replace('\n', " ")),
            Outcome::Crashed(s) => format!("CRASHED {s}"),
            Outcome::NotRun => "not-run".to_string(),
        };
        eprintln!("CASE {name} {status}");
        if !matches!(outcome, Outcome::Ok | Outcome::NotRun) {
            failures.push(format!("{name}: {status}"));
        }
    }
    eprintln!("SUMMARY {} cases, {} not ok", outcomes.len(), failures.len());
    assert!(failures.is_empty(), "cases disagree with Rust:\n  {}", failures.join("\n  "));
}

// ---------------------------------------------------------------------------
// Tests.
// ---------------------------------------------------------------------------

/// Every writer x reader x kind x CFG shape the matrix spells agrees with Rust.
#[test]
fn every_writer_is_seen_by_every_reader() {
    let cases = matrix();
    assert!(cases.len() > 300, "the matrix shrank: {} cases", cases.len());
    report(&run(&cases, &helpers()));
}

fn skeptic(name: &str, locals: Vec<Ty>, stmts: Vec<Statement>, expected: u64) -> Case {
    let blocks = vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }];
    Case { function: function(name, locals, blocks, 0, Ty::u64()), expected }
}

/// The skeptic's probes of 99ce1bb814, verbatim.
///
/// (a) `a = 10; b = 20; p = &raw mut a; pp = &raw mut p; *pp = &raw mut b;
///     *p = 5` leaves a = 10, b = 5; the pair twin `(*p).1 = 9` leaves
///     a.1 = 2, b.1 = 9.
/// (b) `t = (1, 2); u = (3, 4); t = copy u; t.0 = 9; v = copy t` gives
///     v = (9, 4).
///
/// Measured with this file on 99ce1bb814's `lower.rs`: b = 20 (the write
/// followed p's stale SSA value, not the `&raw mut b` that `*pp` stored in
/// p's slot), a.1 = 9 and b.1 = 4 (the pair write went to a), and v.1 a
/// stack-garbage word (the whole copy never reached t's slot). On
/// cb0551b399's: b = 20, v.0 = 3 and v.1 garbage; the pair twin was right.
#[test]
fn the_skeptics_probes_agree_with_rust() {
    let reassign = |name: &str, answer: usize, expected: u64| {
        skeptic(
            name,
            vec![Ty::u64(), Ty::u64(), Ty::u64(), raw_mut(Ty::u64()), raw_mut(raw_mut(Ty::u64()))],
            vec![
                assign(Place::local(1), Rvalue::Use(u64c(10))),
                assign(Place::local(2), Rvalue::Use(u64c(20))),
                assign(Place::local(3), Rvalue::AddressOf(true, Place::local(1))),
                assign(Place::local(4), Rvalue::AddressOf(true, Place::local(3))),
                assign(at(4, vec![DEREF]), Rvalue::AddressOf(true, Place::local(2))),
                assign(at(3, vec![DEREF]), Rvalue::Use(u64c(5))),
                assign(Place::local(0), copy(Place::local(answer))),
            ],
            expected,
        )
    };
    let reassign_pair = |name: &str, answer: Place, expected: u64| {
        skeptic(
            name,
            vec![Ty::u64(), pair_ty(), pair_ty(), raw_mut(pair_ty()), raw_mut(raw_mut(pair_ty()))],
            vec![
                assign(Place::local(1), tuple(vec![u64c(1), u64c(2)])),
                assign(Place::local(2), tuple(vec![u64c(3), u64c(4)])),
                assign(Place::local(3), Rvalue::AddressOf(true, Place::local(1))),
                assign(Place::local(4), Rvalue::AddressOf(true, Place::local(3))),
                assign(at(4, vec![DEREF]), Rvalue::AddressOf(true, Place::local(2))),
                assign(at(3, vec![DEREF, F1]), Rvalue::Use(u64c(9))),
                assign(Place::local(0), copy(answer)),
            ],
            expected,
        )
    };
    let copy_then_field = |name: &str, field: usize, expected: u64| {
        skeptic(
            name,
            vec![Ty::u64(), pair_ty(), pair_ty(), pair_ty()],
            vec![
                assign(Place::local(1), tuple(vec![u64c(1), u64c(2)])),
                assign(Place::local(2), tuple(vec![u64c(3), u64c(4)])),
                assign(Place::local(1), copy(Place::local(2))),
                assign(at(1, vec![F0]), Rvalue::Use(u64c(9))),
                assign(Place::local(3), copy(Place::local(1))),
                assign(Place::local(0), copy(Place::field(3, field))),
            ],
            expected,
        )
    };
    let cases = vec![
        reassign("sk_a_a", 1, 10),
        reassign("sk_a_b", 2, 5),
        reassign_pair("sk_a_pair_a1", Place::field(1, 1), 2),
        reassign_pair("sk_a_pair_b1", Place::field(2, 1), 9),
        copy_then_field("sk_b_v0", 0, 9),
        copy_then_field("sk_b_v1", 1, 4),
    ];
    report(&run(&cases, &[]));
}

fn call_item(func: &str, args: Vec<Operand>, dest: Place) -> Item {
    Item::Call { func: func.into(), args, dest }
}

/// A homed FORMAL is stored into its home on entry, a homed local carried
/// around a loop lives in memory (never a block parameter), and the shapes the
/// rule cannot keep are refused by name rather than lowered. (A homed formal
/// in a body whose entry block is a branch target was refused here until
/// review 6; it now enters through a prologue block,
/// `an_entry_block_that_is_a_branch_target_gets_a_prologue`.)
#[test]
fn homes_hold_across_formals_and_loops_and_refuse_what_they_cannot_keep() {
    // fn bump(x: u64) -> u64 { let p = &raw mut x; *p = x + 1; x }
    let bump = function(
        "t216h_bump",
        vec![Ty::u64(), Ty::u64(), raw_mut(Ty::u64()), Ty::u64()],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![
                assign(Place::local(2), Rvalue::AddressOf(true, Place::local(1))),
                assign(
                    Place::local(3),
                    Rvalue::BinaryOp(BinOp::Add, Operand::Copy(Place::local(1)), u64c(1)),
                ),
                assign(at(2, vec![DEREF]), copy(Place::local(3))),
                assign(Place::local(0), copy(Place::local(1))),
            ],
            terminator: Terminator::Return,
        }],
        1,
        Ty::u64(),
    );
    let mut blocks = Blocks::new();
    blocks.push(&[call_item("t216h_bump", vec![u64c(41)], Place::local(0))]);
    blocks.finish(Terminator::Return);
    let formal = Case {
        function: function("hc_homed_formal", vec![Ty::u64()], blocks.done, 0, Ty::u64()),
        expected: 42,
    };

    // x = 0; p = &raw mut x; i = 0;
    // loop { if i == 3 { break } *p = x + 1; i = i + 1 }  x
    let (x, p, i, c, t) = (1, 2, 3, 4, 5);
    let add = |dest: usize, src: Place| {
        assign(Place::local(dest), Rvalue::BinaryOp(BinOp::Add, Operand::Copy(src), u64c(1)))
    };
    let looped = Case {
        function: function(
            "hc_homed_loop",
            vec![Ty::u64(), Ty::u64(), raw_mut(Ty::u64()), Ty::u64(), Ty::Bool, Ty::u64()],
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        assign(Place::local(x), Rvalue::Use(u64c(0))),
                        assign(Place::local(p), Rvalue::AddressOf(true, Place::local(x))),
                        assign(Place::local(i), Rvalue::Use(u64c(0))),
                    ],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![assign(
                        Place::local(c),
                        Rvalue::BinaryOp(BinOp::Eq, Operand::Copy(Place::local(i)), u64c(3)),
                    )],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(c)),
                        targets: vec![(1, BlockId(3))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![
                        add(t, Place::local(x)),
                        assign(at(p, vec![DEREF]), copy(Place::local(t))),
                        add(i, Place::local(i)),
                    ],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![assign(Place::local(0), copy(Place::local(x)))],
                    terminator: Terminator::Return,
                },
            ],
            0,
            Ty::u64(),
        ),
        expected: 3,
    };
    report(&run(&[formal, looped], &[bump]));

    let refused = |f: &VerifiableFunction| match backend().lower_function(f) {
        Ok(_) => panic!("{} must be refused", f.name),
        Err(e) => e.to_string(),
    };
    // An aggregate is carried by its address: a cast of it to a scalar would
    // reinterpret the address.
    let cast = function(
        "hc_aggregate_cast",
        vec![Ty::u64(), pair_ty()],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![
                assign(Place::local(1), tuple(vec![u64c(1), u64c(2)])),
                assign(Place::local(0), Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::u64())),
            ],
            terminator: Terminator::Return,
        }],
        0,
        Ty::u64(),
    );
    let err = refused(&cast);
    assert!(err.contains("cast of aggregate"), "{err}");
    // A scalar written as a whole aggregate carries no bytes to copy.
    let scalar_into_pair = function(
        "hc_scalar_into_pair",
        vec![Ty::u64(), pair_ty()],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![
                assign(Place::local(1), Rvalue::Use(u64c(7))),
                assign(Place::local(0), copy(Place::field(1, 0))),
            ],
            terminator: Terminator::Return,
        }],
        0,
        Ty::u64(),
    );
    let err = refused(&scalar_into_pair);
    assert!(err.contains("does not carry"), "{err}");
}

// ---------------------------------------------------------------------------
// Review 5: the rule's remaining holes, each a case that failed first.
// ---------------------------------------------------------------------------

fn usize_ty() -> Ty {
    Ty::usize()
}

fn usizec(value: u64) -> Operand {
    Operand::Constant(ConstValue::Uint(u128::from(value), 64))
}

/// `*const [u64]`: a slice FAT pointer, two words (data, length).
fn slice_ptr_ty() -> Ty {
    raw_const(Ty::Slice { elem: Box::new(Ty::u64()) })
}

fn arr3_ty() -> Ty {
    Ty::Array { elem: Box::new(Ty::u64()), len: 3 }
}

fn bin(dest: usize, op: BinOp, a: Operand, b: Operand) -> Statement {
    assign(Place::local(dest), Rvalue::BinaryOp(op, a, b))
}

fn cp(place: Place) -> Operand {
    Operand::Copy(place)
}

fn index(local: usize) -> Projection {
    Projection::Index(local)
}

/// A case of straight-line items (calls split blocks), `_0: u64`.
fn straight(name: &str, locals: Vec<Ty>, items: Vec<Item>, expected: u64) -> Case {
    let mut blocks = Blocks::new();
    blocks.push(&items);
    blocks.finish(Terminator::Return);
    Case { function: function(name, locals, blocks.done, 0, Ty::u64()), expected }
}

/// `arr = [10, 20, 30]; s = *const [u64] from (&raw const arr as *const u64, 3)`,
/// then `tail` over locals `_6..`: `s` is `_5`, `arr` `_1`, `&raw const arr` `_2`.
fn slice_case(name: &str, extra: Vec<Ty>, tail: Vec<Item>, expected: u64) -> Case {
    let mut locals =
        vec![Ty::u64(), arr3_ty(), raw_const(arr3_ty()), raw_const(Ty::u64()), usize_ty()];
    locals.push(slice_ptr_ty());
    locals.extend(extra);
    let mut items = vec![
        Item::S(assign(
            Place::local(1),
            Rvalue::Aggregate(AggregateKind::Array, vec![u64c(10), u64c(20), u64c(30)]),
        )),
        Item::S(assign(Place::local(2), Rvalue::AddressOf(false, Place::local(1)))),
        Item::S(assign(Place::local(3), Rvalue::Cast(cp(Place::local(2)), raw_const(Ty::u64())))),
        Item::S(assign(Place::local(4), Rvalue::Use(usizec(3)))),
        Item::S(assign(
            Place::local(5),
            Rvalue::Aggregate(
                AggregateKind::RawPtr {
                    pointee_ty: Ty::Slice { elem: Box::new(Ty::u64()) },
                    mutable: false,
                },
                vec![cp(Place::local(3)), cp(Place::local(4))],
            ),
        )),
    ];
    items.extend(tail);
    straight(name, locals, items, expected)
}

fn metadata(dest: usize, of: Place) -> Item {
    Item::S(assign(Place::local(dest), Rvalue::UnaryOp(trust_types::UnOp::PtrMetadata, cp(of))))
}

/// `fn len(s: *const [u64]) -> usize`, `fn id(s) -> *const [u64]` and
/// `fn last(s: *const [u64]) -> u64 { (*s)[len - 1] }`.
fn slice_helpers() -> Vec<VerifiableFunction> {
    let one_block =
        |stmts| vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }];
    vec![
        function(
            "t216h_slice_len",
            vec![usize_ty(), slice_ptr_ty()],
            one_block(vec![assign(
                Place::local(0),
                Rvalue::UnaryOp(trust_types::UnOp::PtrMetadata, cp(Place::local(1))),
            )]),
            1,
            usize_ty(),
        ),
        function(
            "t216h_slice_id",
            vec![slice_ptr_ty(), slice_ptr_ty()],
            one_block(vec![assign(Place::local(0), copy(Place::local(1)))]),
            1,
            slice_ptr_ty(),
        ),
        function(
            "t216h_slice_last",
            vec![Ty::u64(), slice_ptr_ty()],
            one_block(vec![assign(
                Place::local(0),
                copy(at(
                    1,
                    vec![
                        DEREF,
                        Projection::ConstantIndex { offset: 1, min_length: 1, from_end: true },
                    ],
                )),
            )]),
            1,
            Ty::u64(),
        ),
    ]
}

/// A slice fat pointer is a two-word value carried, like every aggregate, as
/// the ADDRESS of its bytes: built, copied, homed, projected, passed, returned,
/// stored in a tuple, cast and written through a pointer, its length word
/// survives. `s.len()` is `PtrMetadata(copy s)` in current MIR.
///
/// Measured on 87791e2409 (the review-4 head): the length read back a
/// stack-address word (8339151912 unhomed, 6557808768 homed) while the data
/// word survived; origin/main 565bd805eb gave 18446744073709551600 and 1.
#[test]
fn a_slice_fat_pointer_keeps_both_words() {
    let sp = slice_ptr_ty;
    let s = || Place::local(5);
    let mul_add = |dest: usize, a: usize, scale: u64, b: usize, tmp: usize| {
        vec![
            Item::S(bin(tmp, BinOp::Mul, cp(Place::local(a)), u64c(scale))),
            Item::S(bin(dest, BinOp::Add, cp(Place::local(tmp)), cp(Place::local(b)))),
        ]
    };
    let mut cases = vec![
        slice_case(
            "fp_len",
            vec![usize_ty()],
            vec![metadata(6, s()), Item::S(assign(Place::local(0), copy(Place::local(6))))],
            3,
        ),
        slice_case(
            "fp_len_homed",
            vec![raw_const(sp()), usize_ty()],
            vec![
                Item::S(assign(Place::local(6), Rvalue::AddressOf(false, s()))),
                metadata(7, s()),
                Item::S(assign(Place::local(0), copy(Place::local(7)))),
            ],
            3,
        ),
        slice_case(
            "fp_elem",
            vec![usize_ty()],
            vec![
                Item::S(assign(Place::local(6), Rvalue::Use(usizec(2)))),
                Item::S(assign(Place::local(0), copy(at(5, vec![DEREF, index(6)])))),
            ],
            30,
        ),
        slice_case(
            "fp_elem_homed",
            vec![raw_const(sp()), usize_ty()],
            vec![
                Item::S(assign(Place::local(6), Rvalue::AddressOf(false, s()))),
                Item::S(assign(Place::local(7), Rvalue::Use(usizec(2)))),
                Item::S(assign(Place::local(0), copy(at(5, vec![DEREF, index(7)])))),
            ],
            30,
        ),
        slice_case(
            "fp_len_of_copy",
            vec![sp(), usize_ty()],
            vec![
                Item::S(assign(Place::local(6), copy(s()))),
                metadata(7, Place::local(6)),
                Item::S(assign(Place::local(0), copy(Place::local(7)))),
            ],
            3,
        ),
        slice_case(
            "fp_len_rvalue",
            vec![usize_ty()],
            vec![
                Item::S(assign(Place::local(6), Rvalue::Len(at(5, vec![DEREF])))),
                Item::S(assign(Place::local(0), copy(Place::local(6)))),
            ],
            3,
        ),
        slice_case(
            "fp_call_len",
            vec![usize_ty()],
            vec![
                call_item("t216h_slice_len", vec![cp(s())], Place::local(6)),
                Item::S(assign(Place::local(0), copy(Place::local(6)))),
            ],
            3,
        ),
        slice_case(
            "fp_call_last",
            vec![],
            vec![call_item("t216h_slice_last", vec![cp(s())], Place::local(0))],
            30,
        ),
        slice_case(
            "fp_call_id",
            vec![sp(), usize_ty(), usize_ty(), Ty::u64(), Ty::u64()],
            [
                vec![
                    call_item("t216h_slice_id", vec![cp(s())], Place::local(6)),
                    metadata(7, Place::local(6)),
                    Item::S(assign(Place::local(8), Rvalue::Use(usizec(1)))),
                    Item::S(assign(Place::local(9), copy(at(6, vec![DEREF, index(8)])))),
                ],
                mul_add(0, 7, 100, 9, 10),
            ]
            .concat(),
            320,
        ),
        slice_case(
            "fp_in_tuple",
            vec![Ty::Tuple(vec![sp(), Ty::u64()]), usize_ty(), Ty::u64(), Ty::u64()],
            [
                vec![
                    Item::S(assign(Place::local(6), tuple(vec![cp(s()), u64c(7)]))),
                    metadata(7, Place::field(6, 0)),
                    Item::S(assign(Place::local(8), copy(Place::field(6, 1)))),
                ],
                mul_add(0, 7, 10, 8, 9),
            ]
            .concat(),
            37,
        ),
        slice_case(
            "fp_subslice",
            vec![sp(), usize_ty(), usize_ty(), Ty::u64(), Ty::u64()],
            [
                vec![
                    Item::S(assign(
                        Place::local(6),
                        Rvalue::AddressOf(
                            false,
                            at(
                                5,
                                vec![
                                    DEREF,
                                    Projection::Subslice { from: 1, to: 3, from_end: false },
                                ],
                            ),
                        ),
                    )),
                    metadata(7, Place::local(6)),
                    Item::S(assign(Place::local(8), Rvalue::Use(usizec(0)))),
                    Item::S(assign(Place::local(9), copy(at(6, vec![DEREF, index(8)])))),
                ],
                mul_add(0, 7, 100, 9, 10),
            ]
            .concat(),
            220,
        ),
        slice_case(
            "fp_unsize_cast",
            vec![sp(), usize_ty(), usize_ty(), Ty::u64(), Ty::u64()],
            [
                vec![
                    Item::S(assign(Place::local(6), Rvalue::Cast(cp(Place::local(2)), sp()))),
                    metadata(7, Place::local(6)),
                    Item::S(assign(Place::local(8), Rvalue::Use(usizec(1)))),
                    Item::S(assign(Place::local(9), copy(at(6, vec![DEREF, index(8)])))),
                ],
                mul_add(0, 7, 100, 9, 10),
            ]
            .concat(),
            320,
        ),
        slice_case(
            "fp_cast_to_thin",
            vec![raw_const(Ty::u64())],
            vec![
                Item::S(assign(Place::local(6), Rvalue::Cast(cp(s()), raw_const(Ty::u64())))),
                Item::S(assign(Place::local(0), copy(at(6, vec![DEREF])))),
            ],
            10,
        ),
        slice_case(
            "fp_written_through_pointer",
            vec![sp(), raw_mut(sp()), usize_ty()],
            vec![
                Item::S(assign(
                    Place::local(6),
                    Rvalue::Aggregate(
                        AggregateKind::RawPtr {
                            pointee_ty: Ty::Slice { elem: Box::new(Ty::u64()) },
                            mutable: false,
                        },
                        vec![cp(Place::local(3)), usizec(1)],
                    ),
                )),
                Item::S(assign(Place::local(7), Rvalue::AddressOf(true, Place::local(6)))),
                Item::S(assign(at(7, vec![DEREF]), copy(s()))),
                metadata(8, Place::local(6)),
                Item::S(assign(Place::local(0), copy(Place::local(8)))),
            ],
            3,
        ),
    ];
    cases.shrink_to_fit();
    report(&run(&cases, &slice_helpers()));
}

fn copy_nonoverlapping(src: Operand, dst: Operand, count: Operand, elem_ty: Ty) -> Item {
    Item::S(Statement::CopyNonOverlapping { src, dst, count, elem_ty, span: SourceSpan::default() })
}

/// `copy_nonoverlapping` is a write through a pointer and is lowered as one
/// (a byte copy of `count * size_of::<T>()`); a statement the lowering has no
/// meaning for is REFUSED, never dropped. `assume` is the one intrinsic
/// statement with no codegen effect.
///
/// Measured on 87791e2409: `cno_scalar` returned 2 (the copy was dropped) and
/// a body with a `Statement::Unsupported` lowered, linked and ran.
#[test]
fn pointer_copies_are_written_and_unknown_statements_are_refused() {
    let cases = vec![
        straight(
            "cno_scalar",
            vec![Ty::u64(), Ty::u64(), Ty::u64(), raw_const(Ty::u64()), raw_mut(Ty::u64())],
            vec![
                Item::S(assign(Place::local(1), Rvalue::Use(u64c(1)))),
                Item::S(assign(Place::local(2), Rvalue::Use(u64c(2)))),
                Item::S(assign(Place::local(3), Rvalue::AddressOf(false, Place::local(1)))),
                Item::S(assign(Place::local(4), Rvalue::AddressOf(true, Place::local(2)))),
                copy_nonoverlapping(cp(Place::local(3)), cp(Place::local(4)), usizec(1), Ty::u64()),
                Item::S(assign(Place::local(0), copy(Place::local(2)))),
            ],
            1,
        ),
        // A runtime count: 2 of 3 elements, so the third keeps its value.
        straight(
            "cno_array_runtime_count",
            vec![
                Ty::u64(),
                arr3_ty(),
                arr3_ty(),
                raw_const(arr3_ty()),
                raw_mut(arr3_ty()),
                raw_const(Ty::u64()),
                raw_mut(Ty::u64()),
                usize_ty(),
                usize_ty(),
                Ty::u64(),
                Ty::u64(),
                Ty::u64(),
                Ty::u64(),
                Ty::u64(),
            ],
            vec![
                Item::S(assign(
                    Place::local(1),
                    Rvalue::Aggregate(AggregateKind::Array, vec![u64c(5), u64c(6), u64c(7)]),
                )),
                Item::S(assign(Place::local(2), Rvalue::Repeat(u64c(0), 3))),
                Item::S(assign(Place::local(3), Rvalue::AddressOf(false, Place::local(1)))),
                Item::S(assign(Place::local(4), Rvalue::AddressOf(true, Place::local(2)))),
                Item::S(assign(
                    Place::local(5),
                    Rvalue::Cast(cp(Place::local(3)), raw_const(Ty::u64())),
                )),
                Item::S(assign(
                    Place::local(6),
                    Rvalue::Cast(cp(Place::local(4)), raw_mut(Ty::u64())),
                )),
                Item::S(assign(Place::local(7), Rvalue::Use(usizec(2)))),
                copy_nonoverlapping(
                    cp(Place::local(5)),
                    cp(Place::local(6)),
                    cp(Place::local(7)),
                    Ty::u64(),
                ),
                Item::S(assign(Place::local(8), Rvalue::Use(usizec(1)))),
                Item::S(assign(
                    Place::local(9),
                    copy(at(
                        2,
                        vec![Projection::ConstantIndex {
                            offset: 0,
                            min_length: 3,
                            from_end: false,
                        }],
                    )),
                )),
                Item::S(assign(Place::local(10), copy(at(2, vec![index(8)])))),
                Item::S(assign(
                    Place::local(11),
                    copy(at(
                        2,
                        vec![Projection::ConstantIndex {
                            offset: 2,
                            min_length: 3,
                            from_end: false,
                        }],
                    )),
                )),
                // 100 * dst[0] + 10 * dst[1] + dst[2]
                Item::S(bin(12, BinOp::Mul, cp(Place::local(9)), u64c(100))),
                Item::S(bin(13, BinOp::Mul, cp(Place::local(10)), u64c(10))),
                Item::S(bin(12, BinOp::Add, cp(Place::local(12)), cp(Place::local(13)))),
                Item::S(bin(0, BinOp::Add, cp(Place::local(12)), cp(Place::local(11)))),
            ],
            560,
        ),
        straight(
            "cno_pair",
            vec![
                Ty::u64(),
                pair_ty(),
                pair_ty(),
                raw_const(pair_ty()),
                raw_mut(pair_ty()),
                Ty::u64(),
            ],
            vec![
                Item::S(assign(Place::local(1), tuple(vec![u64c(1), u64c(2)]))),
                Item::S(assign(Place::local(2), tuple(vec![u64c(3), u64c(4)]))),
                Item::S(assign(Place::local(3), Rvalue::AddressOf(false, Place::local(1)))),
                Item::S(assign(Place::local(4), Rvalue::AddressOf(true, Place::local(2)))),
                copy_nonoverlapping(cp(Place::local(3)), cp(Place::local(4)), usizec(1), pair_ty()),
                Item::S(bin(5, BinOp::Mul, cp(Place::field(2, 0)), u64c(10))),
                Item::S(bin(0, BinOp::Add, cp(Place::local(5)), cp(Place::field(2, 1)))),
            ],
            12,
        ),
        straight(
            "assume_is_no_write",
            vec![Ty::u64(), Ty::u64(), Ty::Bool],
            vec![
                Item::S(assign(Place::local(1), Rvalue::Use(u64c(5)))),
                Item::S(bin(2, BinOp::Eq, cp(Place::local(1)), u64c(5))),
                Item::S(Statement::Intrinsic {
                    name: "assume".into(),
                    args: vec![cp(Place::local(2))],
                }),
                Item::S(assign(Place::local(0), copy(Place::local(1)))),
            ],
            5,
        ),
    ];
    report(&run(&cases, &[]));

    let refused = |stmt: Statement| {
        let f = function(
            "hc_refused_statement",
            vec![Ty::u64(), Ty::u64(), raw_mut(Ty::u64())],
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    assign(Place::local(1), Rvalue::Use(u64c(1))),
                    assign(Place::local(2), Rvalue::AddressOf(true, Place::local(1))),
                    stmt,
                    assign(Place::local(0), copy(Place::local(1))),
                ],
                terminator: Terminator::Return,
            }],
            0,
            Ty::u64(),
        );
        match backend().lower_function(&f) {
            Ok(_) => panic!("a body with this statement must be refused"),
            Err(e) => e.to_string(),
        }
    };
    let err = refused(Statement::Unsupported {
        kind: "probe".into(),
        detail: "a statement that writes *_2 = 5 in the source".into(),
        operands: vec![cp(Place::local(2))],
        span: SourceSpan::default(),
    });
    assert!(err.contains("probe"), "{err}");
    let err = refused(Statement::Intrinsic {
        name: "volatile_store_fixture".into(),
        args: vec![cp(Place::local(2)), u64c(5)],
    });
    assert!(err.contains("volatile_store_fixture"), "{err}");
}

/// The stack bytes a lowered function reserves.
fn stack_bytes(f: &VerifiableFunction) -> (usize, u64) {
    let lir = backend().lower_function(f).expect("lowers");
    (lir.stack_slots.len(), lir.stack_slots.iter().map(|slot| u64::from(slot.size)).sum())
}

/// An aggregate built into a local is built IN the local's home — one slot,
/// no copy — whenever no operand can read the bytes the build overwrites;
/// when one can (an aggregate operand of the same local, or through a
/// pointer), it is built in a fresh slot and copied, and the swap stays a swap.
///
/// Measured on 87791e2409: `[u64; 786432]` took two 6 MiB slots (origin/main
/// one) and `big_repeat` CRASHED (SIGSEGV, stack overflow) where origin/main
/// ran; every built tuple/array/checked pair carried a second slot of its size.
#[test]
fn a_built_aggregate_lives_in_its_home_alone() {
    const N: u64 = 786_432;
    let big = straight(
        "big_repeat",
        vec![Ty::u64(), Ty::Array { elem: Box::new(Ty::u64()), len: N }],
        vec![
            Item::S(assign(
                Place::local(1),
                Rvalue::Repeat(u64c(0x0101_0101_0101_0101), N as usize),
            )),
            Item::S(assign(
                Place::local(0),
                copy(at(
                    1,
                    vec![Projection::ConstantIndex { offset: 7, min_length: 8, from_end: false }],
                )),
            )),
        ],
        0x0101_0101_0101_0101,
    );
    let big_footprint = stack_bytes(&big.function);
    let pair_built = straight(
        "pair_built",
        vec![Ty::u64(), pair_ty()],
        vec![
            Item::S(assign(Place::local(1), tuple(vec![u64c(1), u64c(2)]))),
            Item::S(assign(Place::local(0), copy(Place::field(1, 1)))),
        ],
        2,
    );
    let pair_footprint = stack_bytes(&pair_built.function);
    let checked = straight(
        "checked_built",
        vec![Ty::u64(), Ty::u64(), Ty::Tuple(vec![Ty::u64(), Ty::Bool])],
        vec![
            Item::S(assign(Place::local(1), Rvalue::Use(u64c(41)))),
            Item::S(assign(
                Place::local(2),
                Rvalue::CheckedBinaryOp(BinOp::Add, cp(Place::local(1)), u64c(1)),
            )),
            Item::S(assign(Place::local(0), copy(Place::field(2, 0)))),
        ],
        42,
    );
    let checked_footprint = stack_bytes(&checked.function);

    let pp = || Ty::Tuple(vec![pair_ty(), pair_ty()]);
    // w = ((1, 2), (3, 4)), then `rebuild`; the answer is w read as 4 digits.
    let nested = |name: &str, extra: Vec<Ty>, rebuild: Vec<Item>, expected: u64| {
        let mut locals =
            vec![Ty::u64(), pair_ty(), pair_ty(), pp(), Ty::u64(), Ty::u64(), Ty::u64()];
        locals.extend(extra);
        let digits = [
            Item::S(bin(4, BinOp::Mul, cp(at(3, vec![F0, F0])), u64c(1000))),
            Item::S(bin(5, BinOp::Mul, cp(at(3, vec![F0, F1])), u64c(100))),
            Item::S(bin(4, BinOp::Add, cp(Place::local(4)), cp(Place::local(5)))),
            Item::S(bin(5, BinOp::Mul, cp(at(3, vec![F1, F0])), u64c(10))),
            Item::S(bin(4, BinOp::Add, cp(Place::local(4)), cp(Place::local(5)))),
            Item::S(bin(0, BinOp::Add, cp(Place::local(4)), cp(at(3, vec![F1, F1])))),
        ];
        let mut items = vec![
            Item::S(assign(Place::local(1), tuple(vec![u64c(1), u64c(2)]))),
            Item::S(assign(Place::local(2), tuple(vec![u64c(3), u64c(4)]))),
            Item::S(assign(
                Place::local(3),
                tuple(vec![Operand::Move(Place::local(1)), Operand::Move(Place::local(2))]),
            )),
        ];
        items.extend(rebuild);
        items.extend(digits);
        straight(name, locals, items, expected)
    };
    let cases = vec![
        big,
        pair_built,
        checked,
        // t = (t.1, t.0): scalar operands are read before any lane is written.
        straight(
            "swap_scalars_in_home",
            vec![Ty::u64(), pair_ty(), Ty::u64()],
            vec![
                Item::S(assign(Place::local(1), tuple(vec![u64c(1), u64c(2)]))),
                Item::S(assign(
                    Place::local(1),
                    tuple(vec![cp(Place::field(1, 1)), cp(Place::field(1, 0))]),
                )),
                Item::S(bin(2, BinOp::Mul, cp(Place::field(1, 0)), u64c(10))),
                Item::S(bin(0, BinOp::Add, cp(Place::local(2)), cp(Place::field(1, 1)))),
            ],
            21,
        ),
        // w = (w.1, w.0) with aggregate lanes: the operands are w's own bytes.
        nested(
            "swap_pairs_of_self",
            vec![],
            vec![Item::S(assign(
                Place::local(3),
                tuple(vec![cp(Place::field(3, 1)), cp(Place::field(3, 0))]),
            ))],
            3412,
        ),
        // w = (c, *q) with q = &w.0: the second operand reads the first lane.
        nested(
            "build_reads_self_through_pointer",
            vec![raw_const(pair_ty()), pair_ty()],
            vec![
                Item::S(assign(Place::local(7), Rvalue::AddressOf(false, Place::field(3, 0)))),
                Item::S(assign(Place::local(8), tuple(vec![u64c(5), u64c(6)]))),
                Item::S(assign(
                    Place::local(3),
                    tuple(vec![cp(Place::local(8)), cp(at(7, vec![DEREF]))]),
                )),
            ],
            5612,
        ),
        // *p = (w.1, w.0) with p = &w: the destination is w through a pointer.
        nested(
            "build_into_self_through_pointer",
            vec![raw_mut(pp())],
            vec![
                Item::S(assign(Place::local(7), Rvalue::AddressOf(true, Place::local(3)))),
                Item::S(assign(
                    at(7, vec![DEREF]),
                    tuple(vec![cp(Place::field(3, 1)), cp(Place::field(3, 0))]),
                )),
            ],
            3412,
        ),
        // [a; 3] with an aggregate element.
        straight(
            "repeat_pair_element",
            vec![Ty::u64(), pair_ty(), Ty::Array { elem: Box::new(pair_ty()), len: 3 }, Ty::u64()],
            vec![
                Item::S(assign(Place::local(1), tuple(vec![u64c(7), u64c(8)]))),
                Item::S(assign(Place::local(2), Rvalue::Repeat(cp(Place::local(1)), 3))),
                Item::S(bin(
                    3,
                    BinOp::Mul,
                    cp(at(
                        2,
                        vec![
                            Projection::ConstantIndex { offset: 0, min_length: 3, from_end: false },
                            F0,
                        ],
                    )),
                    u64c(10),
                )),
                Item::S(bin(
                    0,
                    BinOp::Add,
                    cp(Place::local(3)),
                    cp(at(
                        2,
                        vec![
                            Projection::ConstantIndex { offset: 2, min_length: 3, from_end: false },
                            F1,
                        ],
                    )),
                )),
            ],
            78,
        ),
    ];
    let outcomes = run(&cases, &[]);
    eprintln!(
        "FOOTPRINT big {big_footprint:?} pair {pair_footprint:?} checked {checked_footprint:?}"
    );
    let footprints_ok =
        big_footprint == (1, N * 8) && pair_footprint == (1, 16) && checked_footprint.0 == 1;
    if !footprints_ok {
        for (name, expected, outcome) in &outcomes {
            eprintln!("CASE {name} want {expected}: {outcome:?}");
        }
    }
    assert_eq!(big_footprint, (1, N * 8), "the array has one home and no build slot");
    assert_eq!(pair_footprint, (1, 16), "the pair has one home and no build slot");
    assert_eq!(checked_footprint.0, 1, "the checked pair has one home and no build slot");
    report(&outcomes);
}

// ---------------------------------------------------------------------------
// Review 6: a fat pointer compared, a build through a slice, and an entry
// block that is a branch target — each a case that failed first.
// ---------------------------------------------------------------------------

/// The fat pointer `slice_case`'s `s` is compared against (`_7`).
#[derive(Clone, Copy)]
enum Other {
    /// `copy s`: the same data word and the same length.
    Same,
    /// `(data, 2)`: the same data word, a shorter length.
    Shorter,
    /// `(&arr[1], 1)`: a higher data word, a shorter length.
    Higher,
}

/// `_8 = op(a, b); _0 = _8 as u64` over `s` (`_5`) and `other` (`_7`), with
/// `_6 = &raw const (*s)[1]`. `s_first` puts `s` on the left.
fn fat_cmp(name: &str, op: BinOp, other: Other, s_first: bool, expected: u64) -> Case {
    let s = || cp(Place::local(5));
    let raw_slice = |data: Operand, len: u64| {
        Rvalue::Aggregate(
            AggregateKind::RawPtr {
                pointee_ty: Ty::Slice { elem: Box::new(Ty::u64()) },
                mutable: false,
            },
            vec![data, usizec(len)],
        )
    };
    let other_value = match other {
        Other::Same => copy(Place::local(5)),
        Other::Shorter => raw_slice(cp(Place::local(3)), 2),
        Other::Higher => raw_slice(cp(Place::local(6)), 1),
    };
    let (a, b) = if s_first { (s(), cp(Place::local(7))) } else { (cp(Place::local(7)), s()) };
    slice_case(
        name,
        vec![raw_const(Ty::u64()), slice_ptr_ty(), Ty::Bool],
        vec![
            Item::S(assign(
                Place::local(6),
                Rvalue::AddressOf(
                    false,
                    at(
                        5,
                        vec![
                            DEREF,
                            Projection::ConstantIndex { offset: 1, min_length: 2, from_end: false },
                        ],
                    ),
                ),
            )),
            Item::S(assign(Place::local(7), other_value)),
            Item::S(bin(8, op, a, b)),
            Item::S(assign(Place::local(0), Rvalue::Cast(cp(Place::local(8)), Ty::u64()))),
        ],
        expected,
    )
}

/// `==`, `!=`, `<`, `<=`, `>`, `>=` on two slice fat pointers compare the
/// PAIRS (data, length), data word first, unsigned — Rust's wide-pointer
/// comparison (`ptr::eq` and `PartialOrd` on `*const [T]` are these BinOps in
/// MIR) — and an operation with no meaning on a fat pointer is refused.
///
/// Measured on bb4cf0f81d (the review-5 head): every operand was its carrier,
/// so the Icmp compared the two locals' HOME addresses: `fat_eq_same` gave 0
/// and `fat_ne_same` 1, and `Cmp`, `Add` and `Not` on a fat pointer lowered.
#[test]
fn a_fat_pointer_comparison_compares_both_words() {
    let cases = vec![
        fat_cmp("fat_eq_same", BinOp::Eq, Other::Same, true, 1),
        fat_cmp("fat_ne_same", BinOp::Ne, Other::Same, true, 0),
        fat_cmp("fat_eq_shorter", BinOp::Eq, Other::Shorter, true, 0),
        fat_cmp("fat_ne_shorter", BinOp::Ne, Other::Shorter, true, 1),
        fat_cmp("fat_eq_higher", BinOp::Eq, Other::Higher, true, 0),
        fat_cmp("fat_le_same", BinOp::Le, Other::Same, true, 1),
        fat_cmp("fat_ge_same", BinOp::Ge, Other::Same, true, 1),
        fat_cmp("fat_lt_same", BinOp::Lt, Other::Same, true, 0),
        // Same data word: the length decides.
        fat_cmp("fat_shorter_lt_s", BinOp::Lt, Other::Shorter, false, 1),
        fat_cmp("fat_s_lt_shorter", BinOp::Lt, Other::Shorter, true, 0),
        fat_cmp("fat_s_gt_shorter", BinOp::Gt, Other::Shorter, true, 1),
        fat_cmp("fat_shorter_ge_s", BinOp::Ge, Other::Shorter, false, 0),
        // Different data words: the data word decides, whatever the lengths.
        fat_cmp("fat_s_lt_higher", BinOp::Lt, Other::Higher, true, 1),
        fat_cmp("fat_s_gt_higher", BinOp::Gt, Other::Higher, true, 0),
        fat_cmp("fat_higher_ge_s", BinOp::Ge, Other::Higher, false, 1),
        fat_cmp("fat_higher_le_s", BinOp::Le, Other::Higher, false, 0),
    ];
    report(&run(&cases, &[]));

    let refused = |name: &str, dest_ty: Ty, rvalue: Rvalue| {
        let case =
            slice_case(name, vec![dest_ty], vec![Item::S(assign(Place::local(6), rvalue))], 0);
        match backend().lower_function(&case.function) {
            Ok(_) => panic!("{name} must be refused"),
            Err(e) => e.to_string(),
        }
    };
    let s = || cp(Place::local(5));
    let err = refused("fat_cmp3", Ty::i8(), Rvalue::BinaryOp(BinOp::Cmp, s(), s()));
    assert!(err.contains("fat pointer"), "{err}");
    let err = refused("fat_add", usize_ty(), Rvalue::BinaryOp(BinOp::Add, s(), s()));
    assert!(err.contains("fat pointer"), "{err}");
    let err = refused("fat_not", slice_ptr_ty(), Rvalue::UnaryOp(trust_types::UnOp::Not, s()));
    assert!(err.contains("aggregate"), "{err}");
}

/// A build whose operands or destination are reached through a slice's data
/// pointer — `_s[k]` on a local of the `Ty::Slice` spelling needs no `Deref`
/// — can overlap the destination, and is built in a fresh slot and copied.
///
/// Measured on bb4cf0f81d: `build_target` looked for a `Deref` only, built
/// these in place, and the second lane read the first one's new bytes:
/// `rebuild_from_slice_ci`, `rebuild_from_slice_index`,
/// `build_into_slice_ci` and `build_into_slice_index` gave 3434 (the `Deref`
/// control gave 3412).
#[test]
fn a_build_through_a_slice_is_not_built_in_place() {
    let pair_slice = || Ty::Slice { elem: Box::new(pair_ty()) };
    let ci = |offset: usize| Projection::ConstantIndex { offset, min_length: 2, from_end: false };
    // w = [(1, 2), (3, 4)]; p = &raw const w as *const [(u64, u64)];
    // s: [(u64, u64)] = p; then `rebuild`; the answer is w as 4 digits.
    // Locals: w _1, p0 _2, p _3, s _4, i0 _5 (= 0), i1 _6 (= 1), digits _7 _8,
    // lanes _9 _10.
    let over_w = |name: &str, rebuild: Vec<Item>| {
        let locals = vec![
            Ty::u64(),
            Ty::Array { elem: Box::new(pair_ty()), len: 2 },
            raw_const(Ty::Array { elem: Box::new(pair_ty()), len: 2 }),
            raw_const(pair_slice()),
            pair_slice(),
            usize_ty(),
            usize_ty(),
            Ty::u64(),
            Ty::u64(),
            pair_ty(),
            pair_ty(),
        ];
        let lane = |k: usize, field: Projection| cp(at(1, vec![ci(k), field]));
        let mut items = vec![
            Item::S(assign(Place::local(9), tuple(vec![u64c(1), u64c(2)]))),
            Item::S(assign(Place::local(10), tuple(vec![u64c(3), u64c(4)]))),
            Item::S(assign(
                Place::local(1),
                Rvalue::Aggregate(
                    AggregateKind::Array,
                    vec![cp(Place::local(9)), cp(Place::local(10))],
                ),
            )),
            Item::S(assign(Place::local(2), Rvalue::AddressOf(false, Place::local(1)))),
            Item::S(assign(
                Place::local(3),
                Rvalue::Cast(cp(Place::local(2)), raw_const(pair_slice())),
            )),
            Item::S(assign(Place::local(4), Rvalue::Cast(cp(Place::local(3)), pair_slice()))),
            Item::S(assign(Place::local(5), Rvalue::Use(usizec(0)))),
            Item::S(assign(Place::local(6), Rvalue::Use(usizec(1)))),
        ];
        items.extend(rebuild);
        items.extend([
            Item::S(bin(7, BinOp::Mul, lane(0, F0), u64c(1000))),
            Item::S(bin(8, BinOp::Mul, lane(0, F1), u64c(100))),
            Item::S(bin(7, BinOp::Add, cp(Place::local(7)), cp(Place::local(8)))),
            Item::S(bin(8, BinOp::Mul, lane(1, F0), u64c(10))),
            Item::S(bin(7, BinOp::Add, cp(Place::local(7)), cp(Place::local(8)))),
            Item::S(bin(0, BinOp::Add, cp(Place::local(7)), lane(1, F1))),
        ]);
        straight(name, locals, items, 3412)
    };
    let array = |a: Place, b: Place| Rvalue::Aggregate(AggregateKind::Array, vec![cp(a), cp(b)]);

    // v = [((1, 2), (3, 4))]; s: [((u64, u64), (u64, u64))] over v; then
    // `s[k] = (v[0].1, v[0].0)`; the answer is v[0] as 4 digits.
    // Locals: v _1, p0 _2, p _3, s _4, k _5 (= 0), digits _6 _7, lanes _8 _9,
    // element _10.
    let pp = || Ty::Tuple(vec![pair_ty(), pair_ty()]);
    let pp_slice = || Ty::Slice { elem: Box::new(pp()) };
    let into_s = |name: &str, dest: Projection| {
        let locals = vec![
            Ty::u64(),
            Ty::Array { elem: Box::new(pp()), len: 1 },
            raw_const(Ty::Array { elem: Box::new(pp()), len: 1 }),
            raw_const(pp_slice()),
            pp_slice(),
            usize_ty(),
            Ty::u64(),
            Ty::u64(),
            pair_ty(),
            pair_ty(),
            pp(),
        ];
        let v0 = |outer: Projection, inner: Projection| {
            cp(at(
                1,
                vec![
                    Projection::ConstantIndex { offset: 0, min_length: 1, from_end: false },
                    outer,
                    inner,
                ],
            ))
        };
        let v0_half = |outer: Projection| {
            cp(at(
                1,
                vec![
                    Projection::ConstantIndex { offset: 0, min_length: 1, from_end: false },
                    outer,
                ],
            ))
        };
        let items = vec![
            Item::S(assign(Place::local(8), tuple(vec![u64c(1), u64c(2)]))),
            Item::S(assign(Place::local(9), tuple(vec![u64c(3), u64c(4)]))),
            Item::S(assign(
                Place::local(10),
                tuple(vec![cp(Place::local(8)), cp(Place::local(9))]),
            )),
            Item::S(assign(
                Place::local(1),
                Rvalue::Aggregate(AggregateKind::Array, vec![cp(Place::local(10))]),
            )),
            Item::S(assign(Place::local(2), Rvalue::AddressOf(false, Place::local(1)))),
            Item::S(assign(
                Place::local(3),
                Rvalue::Cast(cp(Place::local(2)), raw_const(pp_slice())),
            )),
            Item::S(assign(Place::local(4), Rvalue::Cast(cp(Place::local(3)), pp_slice()))),
            Item::S(assign(Place::local(5), Rvalue::Use(usizec(0)))),
            Item::S(assign(at(4, vec![dest]), tuple(vec![v0_half(F1), v0_half(F0)]))),
            Item::S(bin(6, BinOp::Mul, v0(F0, F0), u64c(1000))),
            Item::S(bin(7, BinOp::Mul, v0(F0, F1), u64c(100))),
            Item::S(bin(6, BinOp::Add, cp(Place::local(6)), cp(Place::local(7)))),
            Item::S(bin(7, BinOp::Mul, v0(F1, F0), u64c(10))),
            Item::S(bin(6, BinOp::Add, cp(Place::local(6)), cp(Place::local(7)))),
            Item::S(bin(0, BinOp::Add, cp(Place::local(6)), v0(F1, F1))),
        ];
        straight(name, locals, items, 3412)
    };

    let cases = vec![
        over_w(
            "rebuild_from_slice_ci",
            vec![Item::S(assign(Place::local(1), array(at(4, vec![ci(1)]), at(4, vec![ci(0)]))))],
        ),
        over_w(
            "rebuild_from_slice_index",
            vec![Item::S(assign(
                Place::local(1),
                array(at(4, vec![index(6)]), at(4, vec![index(5)])),
            ))],
        ),
        // The control: the same read spelled with a `Deref`.
        over_w(
            "rebuild_from_deref_ci",
            vec![Item::S(assign(
                Place::local(1),
                array(at(3, vec![DEREF, ci(1)]), at(3, vec![DEREF, ci(0)])),
            ))],
        ),
        into_s(
            "build_into_slice_ci",
            Projection::ConstantIndex { offset: 0, min_length: 1, from_end: false },
        ),
        into_s("build_into_slice_index", index(5)),
    ];
    report(&run(&cases, &[]));
}

/// A body whose entry block is a branch target gets a PROLOGUE block: it
/// stores the homed formals into their homes and hands the entry block its
/// formals' values once, and every edge back into the entry block skips it.
///
/// Measured on bb4cf0f81d: `loop_first`, `walk_formal_slice` and
/// `sum_homed_formals` were REFUSED ("needs a prologue block the bridge does
/// not build") — a slice formal is homed since review 5, so every
/// `fn f(s: &[T])` whose bb0 has a predecessor was refused; origin/main
/// 8e8e84edfa lowered `loop_first` (10). `count_up_ssa_formal` (one back edge
/// into bb0) never exited (the entry block read the formal's entry value on
/// every pass), and `two_back_edges_ssa_formal` (two) read an entry block
/// parameter the entry path never set.
#[test]
fn an_entry_block_that_is_a_branch_target_gets_a_prologue() {
    let switch = |discr: usize, value: u128, then: usize, otherwise: usize| Terminator::SwitchInt {
        discr: cp(Place::local(discr)),
        targets: vec![(value, BlockId(then))],
        otherwise: BlockId(otherwise),
        exhaustive_enum_unreachable: false,
        span: SourceSpan::default(),
    };
    let block = |id: usize, stmts: Vec<Statement>, terminator: Terminator| BasicBlock {
        id: BlockId(id),
        stmts,
        terminator,
    };
    let helpers = vec![
        // fn loop_first(s: *const [u64]) -> u64 { loop { let x = s[0]; if x == 10 { return x } } }
        function(
            "t216h_loop_first",
            vec![Ty::u64(), slice_ptr_ty()],
            vec![
                block(
                    0,
                    vec![assign(
                        Place::local(0),
                        copy(at(
                            1,
                            vec![
                                DEREF,
                                Projection::ConstantIndex {
                                    offset: 0,
                                    min_length: 1,
                                    from_end: false,
                                },
                            ],
                        )),
                    )],
                    switch(0, 10, 1, 0),
                ),
                block(1, vec![], Terminator::Return),
            ],
            1,
            Ty::u64(),
        ),
        // fn walk(mut s: *const [u64]) -> u64 { while s.len() != 1 { s = &s[1..] } s[0] }
        function(
            "t216h_walk",
            vec![Ty::u64(), slice_ptr_ty(), usize_ty(), Ty::Bool],
            vec![
                block(
                    0,
                    vec![
                        assign(
                            Place::local(2),
                            Rvalue::UnaryOp(trust_types::UnOp::PtrMetadata, cp(Place::local(1))),
                        ),
                        bin(3, BinOp::Eq, cp(Place::local(2)), usizec(1)),
                    ],
                    switch(3, 1, 1, 2),
                ),
                block(
                    1,
                    vec![assign(
                        Place::local(0),
                        copy(at(
                            1,
                            vec![
                                DEREF,
                                Projection::ConstantIndex {
                                    offset: 0,
                                    min_length: 1,
                                    from_end: false,
                                },
                            ],
                        )),
                    )],
                    Terminator::Return,
                ),
                block(
                    2,
                    vec![assign(
                        Place::local(1),
                        Rvalue::AddressOf(
                            false,
                            at(
                                1,
                                vec![
                                    DEREF,
                                    Projection::Subslice { from: 1, to: 0, from_end: true },
                                ],
                            ),
                        ),
                    )],
                    Terminator::Goto(BlockId(0)),
                ),
            ],
            1,
            Ty::u64(),
        ),
        // fn sum(mut x: u64, mut a: u64) -> u64 {
        //     let p = &raw mut x; let q = &raw mut a;
        //     while x != 0 { *q = a + x; *p = x - 1 } a }
        function(
            "t216h_sum",
            vec![
                Ty::u64(),
                Ty::u64(),
                Ty::u64(),
                raw_mut(Ty::u64()),
                raw_mut(Ty::u64()),
                Ty::Bool,
                Ty::u64(),
                Ty::u64(),
            ],
            vec![
                block(
                    0,
                    vec![
                        assign(Place::local(3), Rvalue::AddressOf(true, Place::local(1))),
                        assign(Place::local(4), Rvalue::AddressOf(true, Place::local(2))),
                        bin(5, BinOp::Eq, cp(Place::local(1)), u64c(0)),
                    ],
                    switch(5, 1, 1, 2),
                ),
                block(1, vec![assign(Place::local(0), copy(Place::local(2)))], Terminator::Return),
                block(
                    2,
                    vec![
                        bin(6, BinOp::Add, cp(Place::local(2)), cp(Place::local(1))),
                        assign(at(4, vec![DEREF]), copy(Place::local(6))),
                        bin(7, BinOp::Sub, cp(Place::local(1)), u64c(1)),
                        assign(at(3, vec![DEREF]), copy(Place::local(7))),
                    ],
                    Terminator::Goto(BlockId(0)),
                ),
            ],
            2,
            Ty::u64(),
        ),
        // fn count_up(mut x: u64) -> u64 { while x < 50 { x += 7 } x }
        function(
            "t216h_count_up",
            vec![Ty::u64(), Ty::u64(), Ty::Bool],
            vec![
                block(
                    0,
                    vec![bin(2, BinOp::Ge, cp(Place::local(1)), u64c(50))],
                    switch(2, 1, 2, 1),
                ),
                block(
                    1,
                    vec![bin(1, BinOp::Add, cp(Place::local(1)), u64c(7))],
                    Terminator::Goto(BlockId(0)),
                ),
                block(2, vec![assign(Place::local(0), copy(Place::local(1)))], Terminator::Return),
            ],
            1,
            Ty::u64(),
        ),
        // fn two_edges(mut x: u64) -> u64 {
        //     while x < 100 { x += 7; if x % 2 != 0 { x += 1 } } x }
        // with both the even and the odd path jumping back into bb0.
        function(
            "t216h_two_edges",
            vec![Ty::u64(), Ty::u64(), Ty::Bool, Ty::u64(), Ty::Bool],
            vec![
                block(
                    0,
                    vec![bin(2, BinOp::Ge, cp(Place::local(1)), u64c(100))],
                    switch(2, 1, 3, 1),
                ),
                block(
                    1,
                    vec![
                        bin(1, BinOp::Add, cp(Place::local(1)), u64c(7)),
                        bin(3, BinOp::Rem, cp(Place::local(1)), u64c(2)),
                        bin(4, BinOp::Eq, cp(Place::local(3)), u64c(0)),
                    ],
                    switch(4, 1, 0, 2),
                ),
                block(
                    2,
                    vec![bin(1, BinOp::Add, cp(Place::local(1)), u64c(1))],
                    Terminator::Goto(BlockId(0)),
                ),
                block(3, vec![assign(Place::local(0), copy(Place::local(1)))], Terminator::Return),
            ],
            1,
            Ty::u64(),
        ),
    ];
    let cases = vec![
        slice_case(
            "loop_first",
            vec![],
            vec![call_item("t216h_loop_first", vec![cp(Place::local(5))], Place::local(0))],
            10,
        ),
        slice_case(
            "walk_formal_slice",
            vec![],
            vec![call_item("t216h_walk", vec![cp(Place::local(5))], Place::local(0))],
            30,
        ),
        straight(
            "sum_homed_formals",
            vec![Ty::u64()],
            vec![call_item("t216h_sum", vec![u64c(4), u64c(0)], Place::local(0))],
            10,
        ),
        straight(
            "count_up_ssa_formal",
            vec![Ty::u64()],
            vec![call_item("t216h_count_up", vec![u64c(0)], Place::local(0))],
            56,
        ),
        straight(
            "two_back_edges_ssa_formal",
            vec![Ty::u64()],
            vec![call_item("t216h_two_edges", vec![u64c(0)], Place::local(0))],
            104,
        ),
    ];
    report(&run(&cases, &helpers));
}

/// A local that is live into a re-entered entry block but is NOT a formal has
/// no value on the prologue edge: the prologue can hand the entry block only
/// the formals' entry values. Valid MIR never reads such a local before a
/// write, but the bridge does not prove that, so the body is REFUSED by name.
///
/// Measured with ee8804d02c's lower.rs (review 6): both shapes lowered and
/// emitted with no error, the entry block's parameter for `_2` left unset on
/// the prologue edge. With bb4cf0f81d's (review 5, no prologue) ISel refused
/// both ("value ... not defined before use"). Since the merge of origin/main
/// bcf750b5c8 the prologue is main's pre-entry block; with the refusal
/// disabled there, ISel again refuses both, not by name.
#[test]
fn a_non_formal_live_into_a_reentered_entry_block_is_refused() {
    let switch = |discr: usize, then: usize, otherwise: usize| Terminator::SwitchInt {
        discr: cp(Place::local(discr)),
        targets: vec![(1, BlockId(then))],
        otherwise: BlockId(otherwise),
        exhaustive_enum_unreachable: false,
        span: SourceSpan::default(),
    };
    let block = |id: usize, stmts: Vec<Statement>, terminator: Terminator| BasicBlock {
        id: BlockId(id),
        stmts,
        terminator,
    };
    // bb0: _3 = _2 == _1 reads `_2` before any write reaches it.
    let entry = || {
        block(0, vec![bin(3, BinOp::Eq, cp(Place::local(2)), cp(Place::local(1)))], switch(3, 2, 1))
    };
    let ret = || block(2, vec![assign(Place::local(0), copy(Place::local(2)))], Terminator::Return);
    let locals = || vec![Ty::u64(), Ty::u64(), Ty::u64(), Ty::Bool, Ty::Bool];
    // One back edge: bb1: _2 = _1; goto bb0.
    let one_edge = function(
        "hc_nonformal_one_back_edge",
        locals(),
        vec![
            entry(),
            block(
                1,
                vec![assign(Place::local(2), copy(Place::local(1)))],
                Terminator::Goto(BlockId(0)),
            ),
            ret(),
        ],
        1,
        Ty::u64(),
    );
    // Two back edges: bb1: _2 = _1; _4 = _1 == 0; if _4 { goto bb0 } else { bb3: goto bb0 }.
    let two_edges = function(
        "hc_nonformal_two_back_edges",
        locals(),
        vec![
            entry(),
            block(
                1,
                vec![
                    assign(Place::local(2), copy(Place::local(1))),
                    bin(4, BinOp::Eq, cp(Place::local(1)), u64c(0)),
                ],
                switch(4, 0, 3),
            ),
            ret(),
            block(3, vec![], Terminator::Goto(BlockId(0))),
        ],
        1,
        Ty::u64(),
    );
    let mut wrong = Vec::new();
    for f in [&one_edge, &two_edges] {
        // Lower AND emit: ISel is where an unset value used to be caught.
        let outcome = match backend().lower_function(f) {
            Err(e) => format!("lower: {e}"),
            Ok(lir) => match backend().emit_objects(&[lir]) {
                Err(e) => format!("emit: {e}"),
                Ok(_) => "EMITTED with no error".to_string(),
            },
        };
        let refused = outcome.contains("_2 is live into the re-entered entry block bb0")
            && outcome.contains("not a formal");
        println!("{} {}: {outcome}", if refused { "ok" } else { "NOT OK" }, f.name);
        if !refused {
            wrong.push(f.name.clone());
        }
    }
    assert!(wrong.is_empty(), "must be refused: {wrong:?}");
}
