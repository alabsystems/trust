// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache 2.0

//! KNOWN_HAZARDS BACKING-FIRST-LOAD-1: a CERTIFIED `#[trust::backing]` struct's
//! use-site ASSUME `backing_alloc_size >= len` may bound a pointer only by the
//! length of the SAME struct value the pointer was loaded from, read on the
//! path that reaches the row. Each body here is UB at runtime for some input,
//! so its bounds row must NOT prove; the guarded `self.ptr.add(i)` under
//! `i < self.len` (and its `from_raw_parts` twin) must keep proving.
//!
//! The MIR is written in the shape the extractor emits at `-Copt-level=0`
//! (`backing_stale3.rs` / `backing_stale4.rs` of the 2026-09-30 review); the
//! rows go through the production generation entry the compiler calls, with
//! the struct certified, and are judged by the in-process ay router.

use trust_types::{
    BasicBlock, BinOp, ConstValue, LocalDecl, UnwindEdge, VerifiableBody, VerificationResult,
};

use super::*;

const ADD: &str = "core::ptr::const_ptr::<impl *const u8>::add";
const OFFSET: &str = "core::ptr::const_ptr::<impl *const u8>::offset";
const FROM_RAW_PARTS: &str = "core::slice::raw::from_raw_parts";

fn buf() -> Ty {
    Ty::Adt {
        adt_kind: None,
        layout: None,
        variants: Vec::new().into(),
        name: "Buf".into(),
        fields: vec![
            ("ptr".into(), Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) }),
            ("len".into(), Ty::usize()),
        ]
        .into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    }
}

fn buf_ref() -> Ty {
    Ty::Ref { mutable: false, inner: Box::new(buf()) }
}

fn ptr_u8() -> Ty {
    Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) }
}

fn slice_ref() -> Ty {
    Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }) }
}

fn decl(index: usize, ty: Ty, name: Option<&str>) -> LocalDecl {
    LocalDecl { index, ty, name: name.map(Into::into) }
}

/// `(*base).field`
fn field(base: usize, field: usize) -> Place {
    Place { local: base, projections: vec![Projection::Deref, Projection::Field(field)] }
}

fn copy(local: usize) -> Operand {
    Operand::Copy(Place::local(local))
}

fn moved(local: usize) -> Operand {
    Operand::Move(Place::local(local))
}

fn assign(dest: usize, rvalue: Rvalue) -> Statement {
    Statement::Assign { place: Place::local(dest), rvalue, span: SourceSpan::default() }
}

fn load(dest: usize, base: usize, f: usize) -> Statement {
    assign(dest, Rvalue::Use(Operand::Copy(field(base, f))))
}

fn mov(dest: usize, src: usize) -> Statement {
    assign(dest, Rvalue::Use(copy(src)))
}

fn konst(dest: usize, n: u128) -> Statement {
    assign(dest, Rvalue::Use(Operand::Constant(ConstValue::Uint(n, 64))))
}

fn lt(dest: usize, a: usize, b: usize) -> Statement {
    assign(dest, Rvalue::BinaryOp(BinOp::Lt, moved(a), moved(b)))
}

fn le(dest: usize, a: usize, b: usize) -> Statement {
    assign(dest, Rvalue::BinaryOp(BinOp::Le, moved(a), moved(b)))
}

fn block(id: usize, stmts: Vec<Statement>, terminator: Terminator) -> BasicBlock {
    BasicBlock { id: BlockId(id), stmts, terminator }
}

/// `switchInt(move cond) -> [0: otherwise_false, otherwise: if_true]`
fn branch(cond: usize, if_true: usize, if_false: usize) -> Terminator {
    Terminator::SwitchInt {
        discr: moved(cond),
        targets: vec![(0, BlockId(if_false))],
        otherwise: BlockId(if_true),
        exhaustive_enum_unreachable: false,
        span: SourceSpan::default(),
    }
}

fn call(callee: &str, key: &str, args: Vec<Operand>, dest: usize, target: usize) -> Terminator {
    Terminator::Call {
        unwind: UnwindEdge::Unreachable,
        is_unsafe_sig: true,
        callee_identity: None,
        callee_key: super::tests::fixture_key(key),
        is_foreign: false,
        func: callee.to_string(),
        args,
        dest: Place::local(dest),
        target: Some(BlockId(target)),
        span: SourceSpan::default(),
        atomic: None,
    }
}

/// The unsafe operation of a body's guarded block: `dest = op(ptr, count)`.
#[derive(Clone, Copy, Debug)]
enum Spelling {
    /// `ptr.add(count)` — `<*const u8>::add`.
    Add,
    /// `ptr.offset(count as isize)` — `<*const u8>::offset`.
    Offset,
    /// `slice::from_raw_parts(ptr, count)` — the copy-bounds row.
    FromRawParts,
}

impl Spelling {
    fn call(self, ptr: usize, count: usize, dest: usize, target: usize) -> Terminator {
        match self {
            Spelling::Add => {
                call(ADD, "core::ptr::const_ptr::add", vec![moved(ptr), moved(count)], dest, target)
            }
            Spelling::Offset => call(
                OFFSET,
                "core::ptr::const_ptr::offset",
                vec![moved(ptr), moved(count)],
                dest,
                target,
            ),
            Spelling::FromRawParts => call(
                FROM_RAW_PARTS,
                "core::slice::raw::from_raw_parts",
                vec![moved(ptr), moved(count)],
                dest,
                target,
            ),
        }
    }

    fn return_ty(self) -> Ty {
        match self {
            Spelling::FromRawParts => slice_ref(),
            Spelling::Add | Spelling::Offset => ptr_u8(),
        }
    }

    fn count_ty(self) -> Ty {
        match self {
            Spelling::Offset => Ty::isize(),
            Spelling::Add | Spelling::FromRawParts => Ty::usize(),
        }
    }

    /// The call's count operand, from the `usize` index `src`: the index itself,
    /// or `src as isize` for `offset`.
    fn count_def(self, dest: usize, src: usize) -> Statement {
        match self {
            Spelling::Offset => assign(dest, Rvalue::Cast(copy(src), Ty::isize())),
            Spelling::Add | Spelling::FromRawParts => mov(dest, src),
        }
    }

    /// The guard comparison: `i < n` for an offset (one-past is the only
    /// in-bounds end), `i <= n` for a slice of `i` elements.
    fn guard(self, dest: usize, a: usize, b: usize) -> Statement {
        match self {
            Spelling::FromRawParts => le(dest, a, b),
            Spelling::Add | Spelling::Offset => lt(dest, a, b),
        }
    }
}

const ALL: [Spelling; 3] = [Spelling::Add, Spelling::Offset, Spelling::FromRawParts];

fn function(
    name: &str,
    spelling: Spelling,
    locals: Vec<LocalDecl>,
    arg_count: usize,
    blocks: Vec<BasicBlock>,
) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("backing_first_load::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            return_ty: spelling.return_ty(),
            locals,
            arg_count,
            blocks,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// POSITIVE CONTROL: `fn ok(&self, i) { if i < self.len { self.ptr.add(i) } else { self.ptr } }`
fn ok(spelling: Spelling) -> VerifiableFunction {
    // _1 self, _2 i, _3 cond, _4 i copy, _5 len load, _6 ptr load, _7 count
    let locals = vec![
        decl(0, spelling.return_ty(), None),
        decl(1, buf_ref(), Some("self")),
        decl(2, Ty::usize(), Some("i")),
        decl(3, Ty::Bool, None),
        decl(4, Ty::usize(), None),
        decl(5, Ty::usize(), None),
        decl(6, ptr_u8(), None),
        decl(7, spelling.count_ty(), None),
    ];
    let blocks = vec![
        block(0, vec![mov(4, 2), load(5, 1, 1), spelling.guard(3, 4, 5)], branch(3, 1, 3)),
        block(1, vec![load(6, 1, 0), spelling.count_def(7, 2)], spelling.call(6, 7, 0, 2)),
        block(2, vec![], Terminator::Return),
        block(3, vec![], Terminator::Return),
    ];
    function("ok", spelling, locals, 2, blocks)
}

/// `Buf::at_bad` / `Buf::add_bad`: `let mut n = self.len; n = 1 << 40; if i < n { self.ptr.add(i) }`.
/// `Buf::map(10).add_bad(1 << 39)` offsets 2^39 bytes into a 10-byte mapping.
fn at_bad(spelling: Spelling) -> VerifiableFunction {
    // _1 self, _2 i, _3 n, _4 cond, _5 i copy, _6 n copy, _7 ptr load, _8 count
    let locals = vec![
        decl(0, spelling.return_ty(), None),
        decl(1, buf_ref(), Some("self")),
        decl(2, Ty::usize(), Some("i")),
        decl(3, Ty::usize(), Some("n")),
        decl(4, Ty::Bool, None),
        decl(5, Ty::usize(), None),
        decl(6, Ty::usize(), None),
        decl(7, ptr_u8(), None),
        decl(8, spelling.count_ty(), None),
    ];
    let blocks = vec![
        block(
            0,
            vec![load(3, 1, 1), konst(3, 1 << 40), mov(5, 2), mov(6, 3), spelling.guard(4, 5, 6)],
            branch(4, 1, 3),
        ),
        block(1, vec![load(7, 1, 0), spelling.count_def(8, 2)], spelling.call(7, 8, 0, 2)),
        block(2, vec![], Terminator::Return),
        block(3, vec![], Terminator::Return),
    ];
    function("at_bad", spelling, locals, 2, blocks)
}

/// `Buf::cross` (and the free `two(a, b, i)`): `let mut s = self; let n = s.len; s = other;
/// if i < n { s.ptr.add(i) }`. `Buf::map(1 << 40).cross(&Buf::map(2), 1 << 39)` is UB.
fn cross(name: &str, spelling: Spelling) -> VerifiableFunction {
    // _1 self/a, _2 other/b, _3 i, _4 s, _5 n, _6 cond, _7 i copy, _8 n copy, _9 ptr, _10 count
    let locals = vec![
        decl(0, spelling.return_ty(), None),
        decl(1, buf_ref(), Some(if name == "two" { "a" } else { "self" })),
        decl(2, buf_ref(), Some(if name == "two" { "b" } else { "other" })),
        decl(3, Ty::usize(), Some("i")),
        decl(4, buf_ref(), Some("s")),
        decl(5, Ty::usize(), Some("n")),
        decl(6, Ty::Bool, None),
        decl(7, Ty::usize(), None),
        decl(8, Ty::usize(), None),
        decl(9, ptr_u8(), None),
        decl(10, spelling.count_ty(), None),
    ];
    let blocks = vec![
        block(
            0,
            vec![
                mov(4, 1),
                load(5, 4, 1),
                mov(4, 2),
                mov(7, 3),
                mov(8, 5),
                spelling.guard(6, 7, 8),
            ],
            branch(6, 1, 3),
        ),
        block(1, vec![load(9, 4, 0), spelling.count_def(10, 3)], spelling.call(9, 10, 0, 2)),
        block(2, vec![], Terminator::Return),
        block(3, vec![], Terminator::Return),
    ];
    function(name, spelling, locals, 3, blocks)
}

/// JOIN (the first loaded length is not the one every path holds):
/// `let n = if c { self.len } else { other.len }; if i < n { self.ptr.add(i) }`.
/// `c == false` with `other.len > self.len` is UB.
fn join_len(spelling: Spelling) -> VerifiableFunction {
    // _1 self, _2 other, _3 c, _4 i, _5 n, _6 cond, _7 i copy, _8 n copy, _9 ptr, _10 count
    let locals = vec![
        decl(0, spelling.return_ty(), None),
        decl(1, buf_ref(), Some("self")),
        decl(2, buf_ref(), Some("other")),
        decl(3, Ty::Bool, Some("c")),
        decl(4, Ty::usize(), Some("i")),
        decl(5, Ty::usize(), Some("n")),
        decl(6, Ty::Bool, None),
        decl(7, Ty::usize(), None),
        decl(8, Ty::usize(), None),
        decl(9, ptr_u8(), None),
        decl(10, spelling.count_ty(), None),
    ];
    let blocks = vec![
        block(0, vec![], branch(3, 1, 2)),
        block(1, vec![load(5, 1, 1)], Terminator::Goto(BlockId(3))),
        block(2, vec![load(5, 2, 1)], Terminator::Goto(BlockId(3))),
        block(3, vec![mov(7, 4), mov(8, 5), spelling.guard(6, 7, 8)], branch(6, 4, 6)),
        block(4, vec![load(9, 1, 0), spelling.count_def(10, 4)], spelling.call(9, 10, 0, 5)),
        block(5, vec![], Terminator::Return),
        block(6, vec![], Terminator::Return),
    ];
    function("join_len", spelling, locals, 4, blocks)
}

/// JOIN, the other order (the length a LATER block loads is not the one the
/// pointer's path holds): `let n = if c { other.len } else { self.len }; …`.
fn join_len_rev(spelling: Spelling) -> VerifiableFunction {
    let mut f = join_len(spelling);
    f.name = "join_len_rev".into();
    f.def_path = "backing_first_load::join_len_rev".into();
    f.body.blocks[1].stmts = vec![load(5, 2, 1)];
    f.body.blocks[2].stmts = vec![load(5, 1, 1)];
    f
}

/// STALE BASE (the struct is rewritten between the length load and the pointer
/// load, through a `&mut`): `let n = self.len; *self = *other; if i < n { self.ptr.add(i) }`.
fn rewritten_base(spelling: Spelling) -> VerifiableFunction {
    // _1 self: &mut Buf, _2 other, _3 i, _4 n, _5 cond, _6 i copy, _7 n copy, _8 ptr, _9 count
    let locals = vec![
        decl(0, spelling.return_ty(), None),
        decl(1, Ty::Ref { mutable: true, inner: Box::new(buf()) }, Some("self")),
        decl(2, buf_ref(), Some("other")),
        decl(3, Ty::usize(), Some("i")),
        decl(4, Ty::usize(), Some("n")),
        decl(5, Ty::Bool, None),
        decl(6, Ty::usize(), None),
        decl(7, Ty::usize(), None),
        decl(8, ptr_u8(), None),
        decl(9, spelling.count_ty(), None),
    ];
    let store = Statement::Assign {
        place: Place { local: 1, projections: vec![Projection::Deref] },
        rvalue: Rvalue::Use(Operand::Copy(Place {
            local: 2,
            projections: vec![Projection::Deref],
        })),
        span: SourceSpan::default(),
    };
    let blocks = vec![
        block(
            0,
            vec![load(4, 1, 1), store, mov(6, 3), mov(7, 4), spelling.guard(5, 6, 7)],
            branch(5, 1, 3),
        ),
        block(1, vec![load(8, 1, 0), spelling.count_def(9, 3)], spelling.call(8, 9, 0, 2)),
        block(2, vec![], Terminator::Return),
        block(3, vec![], Terminator::Return),
    ];
    function("rewritten_base", spelling, locals, 3, blocks)
}

/// ANOTHER STRUCT of the same shape: `fn foreign(&self, o: &Other, i) { if i < o.len { o.ptr.add(i) } }`.
/// Only `Buf` is certified; `Other`'s pointer and length are unrelated.
fn foreign(spelling: Spelling) -> VerifiableFunction {
    let Ty::Adt {
        adt_kind,
        layout,
        variants,
        fields,
        disc_index_safe,
        faithful_enum_repr,
        enum_layout,
        arbitrary_precision,
        validity_wrapper,
        ..
    } = buf()
    else {
        unreachable!()
    };
    let other = Ty::Adt {
        adt_kind,
        layout,
        variants,
        name: "Other".into(),
        fields,
        disc_index_safe,
        faithful_enum_repr,
        enum_layout,
        arbitrary_precision,
        validity_wrapper,
    };
    // _1 self, _2 o, _3 i, _4 cond, _5 i copy, _6 len load, _7 ptr load, _8 count
    let locals = vec![
        decl(0, spelling.return_ty(), None),
        decl(1, buf_ref(), Some("self")),
        decl(2, Ty::Ref { mutable: false, inner: Box::new(other) }, Some("o")),
        decl(3, Ty::usize(), Some("i")),
        decl(4, Ty::Bool, None),
        decl(5, Ty::usize(), None),
        decl(6, Ty::usize(), None),
        decl(7, ptr_u8(), None),
        decl(8, spelling.count_ty(), None),
    ];
    let blocks = vec![
        block(0, vec![mov(5, 3), load(6, 2, 1), spelling.guard(4, 5, 6)], branch(4, 1, 3)),
        block(1, vec![load(7, 2, 0), spelling.count_def(8, 3)], spelling.call(7, 8, 0, 2)),
        block(2, vec![], Terminator::Return),
        block(3, vec![], Terminator::Return),
    ];
    function("foreign", spelling, locals, 3, blocks)
}

/// JOIN of the POINTER (the walk's last writer is not the path's):
/// `let q = if c { self.ptr.add(8) } else { self.ptr.add(1) }; if i < self.len { q.add(i) }`.
/// `c == true` with `i == self.len - 1` ends 7 bytes past the allocation.
fn join_ptr(spelling: Spelling) -> VerifiableFunction {
    // _1 self, _2 c, _3 i, _4 q, _5 ptr load, _6 ptr load, _7 cond, _8 i copy, _9 len load, _10 count
    let locals = vec![
        decl(0, spelling.return_ty(), None),
        decl(1, buf_ref(), Some("self")),
        decl(2, Ty::Bool, Some("c")),
        decl(3, Ty::usize(), Some("i")),
        decl(4, ptr_u8(), Some("q")),
        decl(5, ptr_u8(), None),
        decl(6, ptr_u8(), None),
        decl(7, Ty::Bool, None),
        decl(8, Ty::usize(), None),
        decl(9, Ty::usize(), None),
        decl(10, spelling.count_ty(), None),
    ];
    let step = |n: u128| Operand::Constant(ConstValue::Uint(n, 64));
    let blocks = vec![
        block(0, vec![], branch(2, 1, 2)),
        block(
            1,
            vec![load(5, 1, 0)],
            call(ADD, "core::ptr::const_ptr::add", vec![moved(5), step(8)], 4, 3),
        ),
        block(
            2,
            vec![load(6, 1, 0)],
            call(ADD, "core::ptr::const_ptr::add", vec![moved(6), step(1)], 4, 3),
        ),
        block(3, vec![mov(8, 3), load(9, 1, 1), lt(7, 8, 9)], branch(7, 4, 6)),
        block(4, vec![spelling.count_def(10, 3)], spelling.call(4, 10, 0, 5)),
        block(5, vec![], Terminator::Return),
        block(6, vec![], Terminator::Return),
    ];
    function("join_ptr", spelling, locals, 3, blocks)
}

/// How the joined pointer local `q` is written from a field-loaded pointer.
#[derive(Clone, Copy, Debug)]
enum Carry {
    /// `q = copy p`.
    Copy,
    /// `q = copy p as *const u8`.
    Cast,
    /// `q = p.cast::<u8>()`.
    CastCall,
}

/// JOIN of the pointer's SOURCE VALUE: `let q = if c { other.ptr } else { self.ptr };
/// if i < self.len { q.add(i) }`. The walk visits the `else` block last, so its
/// last-writer tag says `self`; `c == true` with `other.len < self.len` is UB.
fn join_carry(carry: Carry, spelling: Spelling) -> VerifiableFunction {
    // _1 self, _2 other, _3 c, _4 i, _5 q, _6 other ptr, _7 self ptr, _8 cond,
    // _9 i copy, _10 len load, _11 count
    let locals = vec![
        decl(0, spelling.return_ty(), None),
        decl(1, buf_ref(), Some("self")),
        decl(2, buf_ref(), Some("other")),
        decl(3, Ty::Bool, Some("c")),
        decl(4, Ty::usize(), Some("i")),
        decl(5, ptr_u8(), Some("q")),
        decl(6, ptr_u8(), None),
        decl(7, ptr_u8(), None),
        decl(8, Ty::Bool, None),
        decl(9, Ty::usize(), None),
        decl(10, Ty::usize(), None),
        decl(11, spelling.count_ty(), None),
    ];
    let carried = |block_id: usize, src: usize| match carry {
        Carry::Copy => block(block_id, vec![mov(5, src)], Terminator::Goto(BlockId(3))),
        Carry::Cast => block(
            block_id,
            vec![assign(5, Rvalue::Cast(moved(src), ptr_u8()))],
            Terminator::Goto(BlockId(3)),
        ),
        Carry::CastCall => block(
            block_id,
            vec![],
            call(
                "core::ptr::const_ptr::<impl *const u8>::cast::<u8>",
                "core::ptr::const_ptr::cast",
                vec![moved(src)],
                5,
                3,
            ),
        ),
    };
    let mut first = carried(1, 6);
    first.stmts.insert(0, load(6, 2, 0));
    let mut second = carried(2, 7);
    second.stmts.insert(0, load(7, 1, 0));
    let blocks = vec![
        block(0, vec![], branch(3, 1, 2)),
        first,
        second,
        block(3, vec![mov(9, 4), load(10, 1, 1), lt(8, 9, 10)], branch(8, 4, 6)),
        block(4, vec![spelling.count_def(11, 4)], spelling.call(5, 11, 0, 5)),
        block(5, vec![], Terminator::Return),
        block(6, vec![], Terminator::Return),
    ];
    function(&format!("join_{carry:?}").to_lowercase(), spelling, locals, 4, blocks)
}

/// CAPABILITY CONTROL (a copy of `self` is the same value):
/// `let s = self; if i < self.len { s.ptr.add(i) }`.
fn ok_through_copy(spelling: Spelling) -> VerifiableFunction {
    // _1 self, _2 i, _3 s, _4 cond, _5 i copy, _6 len load, _7 ptr load, _8 count
    let locals = vec![
        decl(0, spelling.return_ty(), None),
        decl(1, buf_ref(), Some("self")),
        decl(2, Ty::usize(), Some("i")),
        decl(3, buf_ref(), Some("s")),
        decl(4, Ty::Bool, None),
        decl(5, Ty::usize(), None),
        decl(6, Ty::usize(), None),
        decl(7, ptr_u8(), None),
        decl(8, spelling.count_ty(), None),
    ];
    let blocks = vec![
        block(
            0,
            vec![mov(3, 1), mov(5, 2), load(6, 1, 1), spelling.guard(4, 5, 6)],
            branch(4, 1, 3),
        ),
        block(1, vec![load(7, 3, 0), spelling.count_def(8, 2)], spelling.call(7, 8, 0, 2)),
        block(2, vec![], Terminator::Return),
        block(3, vec![], Terminator::Return),
    ];
    function("ok_through_copy", spelling, locals, 2, blocks)
}

/// CAPABILITY CONTROL (every load of the one length is that length; the guard reads
/// the SECOND): `let a = self.len; let b = self.len; if i < b { self.ptr.add(i) }`.
fn ok_second_load(spelling: Spelling) -> VerifiableFunction {
    // _1 self, _2 i, _3 a, _4 b, _5 cond, _6 i copy, _7 b copy, _8 ptr load, _9 count
    let locals = vec![
        decl(0, spelling.return_ty(), None),
        decl(1, buf_ref(), Some("self")),
        decl(2, Ty::usize(), Some("i")),
        decl(3, Ty::usize(), Some("a")),
        decl(4, Ty::usize(), Some("b")),
        decl(5, Ty::Bool, None),
        decl(6, Ty::usize(), None),
        decl(7, Ty::usize(), None),
        decl(8, ptr_u8(), None),
        decl(9, spelling.count_ty(), None),
    ];
    let blocks = vec![
        block(
            0,
            vec![load(3, 1, 1), load(4, 1, 1), mov(6, 2), mov(7, 4), spelling.guard(5, 6, 7)],
            branch(5, 1, 3),
        ),
        block(1, vec![load(8, 1, 0), spelling.count_def(9, 2)], spelling.call(8, 9, 0, 2)),
        block(2, vec![], Terminator::Return),
        block(3, vec![], Terminator::Return),
    ];
    function("ok_second_load", spelling, locals, 2, blocks)
}

fn is_bounds_row(vc: &VerificationCondition) -> bool {
    match &vc.kind {
        // An access the engine cannot bound keeps the unverified-call row instead.
        VcKind::Assertion { message } => {
            message.contains("[unsafe:sep:offset]") || message.contains("[unsafe:sep:call]")
        }
        VcKind::CopyBoundsViolation { detail, .. } => detail.contains("backing field"),
        _ => false,
    }
}

/// Every backing bounds row of `func` under a CERTIFIED `Buf`, through the
/// compiler's generation entry, with whether ay (or generation-time discharge)
/// proves it.
fn bounds_verdicts(func: &VerifiableFunction, hardened: bool) -> Vec<(String, bool)> {
    let context = crate::VcgenContext::for_function(func.def_path.clone())
        .with_backing(true)
        .with_callee_summaries(
            crate::CalleeSummaryContext::default()
                .with_certified_backing_structs(std::iter::once("Buf".to_string()).collect()),
        );
    let (solver, discharged) =
        crate::generate_vcs_with_discharge_and_summaries_configured_with_context(
            func,
            &crate::modular::SummaryDatabase::new(),
            hardened,
            &context,
        );
    let router = crate::test_router::deterministic_test_router();
    // The in-process router has no backend for a `CopyBoundsViolation` row ("no backend
    // can handle this VC"); its formula is a violation like any assertion's, so it is
    // judged as one: UNSAT ⇔ the copy is in bounds.
    let routed: Vec<_> = solver
        .into_iter()
        .filter(is_bounds_row)
        .map(|vc| {
            let label = format!("{:?}", vc.kind);
            let judged =
                VerificationCondition { kind: VcKind::Assertion { message: label.clone() }, ..vc };
            (label, judged)
        })
        .collect();
    let judged: Vec<_> = routed.iter().map(|(_, vc)| vc.clone()).collect();
    let mut verdicts: Vec<(String, bool)> = routed
        .iter()
        .zip(router.verify_all(&judged))
        .map(|((label, _), (_, result))| {
            (label.clone(), matches!(result, VerificationResult::Proved { .. }))
        })
        .collect();
    verdicts.extend(discharged.into_iter().filter(|(vc, _)| is_bounds_row(vc)).map(
        |(vc, result)| {
            (format!("{:?}", vc.kind), matches!(result, VerificationResult::Proved { .. }))
        },
    ));
    verdicts
}

/// Every `(function, spelling, hardened)` of `shapes` whose bounds row PROVED (or
/// whose row is missing): each is UB for some input, so the list must be empty.
fn false_proofs(shapes: &[fn(Spelling) -> VerifiableFunction]) -> Vec<String> {
    let mut wrong = Vec::new();
    for shape in shapes {
        for spelling in ALL {
            let func = shape(spelling);
            for hardened in [false, true] {
                let verdicts = bounds_verdicts(&func, hardened);
                if verdicts.is_empty() {
                    wrong.push(format!(
                        "{} {spelling:?} hardened={hardened}: no bounds row",
                        func.name
                    ));
                }
                for (row, proved) in verdicts {
                    if proved {
                        wrong.push(format!(
                            "{} {spelling:?} hardened={hardened}: PROVED {row}",
                            func.name
                        ));
                    }
                }
            }
        }
    }
    wrong
}

fn assert_no_false_proof(shapes: &[fn(Spelling) -> VerifiableFunction]) {
    let wrong = false_proofs(shapes);
    assert!(wrong.is_empty(), "UB bodies whose bounds row proved:\n{}", wrong.join("\n"));
}

#[test]
fn guarded_access_of_the_same_value_still_proves() {
    // `offset` is left out: its count is `i as isize`, and the signed count carries no
    // `count >= 0` range on main either (its row is unproven there with or without this fix).
    let mut missing = Vec::new();
    let shapes: [fn(Spelling) -> VerifiableFunction; 3] = [ok, ok_through_copy, ok_second_load];
    for shape in shapes {
        for spelling in [Spelling::Add, Spelling::FromRawParts] {
            let func = shape(spelling);
            for hardened in [false, true] {
                let verdicts = bounds_verdicts(&func, hardened);
                if verdicts.is_empty() || !verdicts.iter().all(|(_, proved)| *proved) {
                    missing.push(format!(
                        "{} {spelling:?} hardened={hardened}: {verdicts:?}",
                        func.name
                    ));
                }
            }
        }
    }
    assert!(
        missing.is_empty(),
        "`if i < self.len {{ self.ptr.add(i) }}` must prove under a certified backing \
         invariant:\n{}",
        missing.join("\n")
    );
}

#[test]
fn a_reassigned_length_local_is_not_the_field() {
    assert_no_false_proof(&[at_bad]);
}

#[test]
fn the_length_of_one_value_does_not_bound_the_pointer_of_another() {
    assert_no_false_proof(&[|s| cross("cross", s), |s| cross("two", s)]);
}

#[test]
fn a_length_joined_from_two_values_bounds_neither_pointer() {
    assert_no_false_proof(&[join_len, join_len_rev]);
}

#[test]
fn a_struct_rewritten_after_its_length_load_is_a_new_value() {
    assert_no_false_proof(&[rewritten_base]);
}

#[test]
fn a_struct_of_another_type_is_not_the_certified_one() {
    assert_no_false_proof(&[foreign]);
}

#[test]
fn a_pointer_joined_from_two_offsets_takes_neither_walk_offset() {
    assert_no_false_proof(&[join_ptr]);
}

#[test]
fn a_pointer_joined_from_two_values_carries_neither_tag() {
    assert_no_false_proof(&[
        |s| join_carry(Carry::Copy, s),
        |s| join_carry(Carry::Cast, s),
        |s| join_carry(Carry::CastCall, s),
    ]);
}

/// RAW-NAME COLLISION: the length local's SOURCE name is `_9`, which the pipeline
/// demotes to `_6` (it is fallback-shaped), while local 9 is an unnamed copy of `big`:
/// `fn bad(&self, i, big) { let _9 = self.len; if i < big { self.ptr.add(i) } }`.
/// UB whenever `self.len <= i < big`. Spelling the ASSUME's length by the raw name
/// made it `alloc_size >= _9`, which the pipeline reads as `big`.
fn raw_name_collision(spelling: Spelling) -> VerifiableFunction {
    // _1 self, _2 i, _3 big, _4 cond, _5 i copy, _6 "_9" len load, _7 ptr, _8 count, _9 big copy
    let locals = vec![
        decl(0, spelling.return_ty(), None),
        decl(1, buf_ref(), Some("self")),
        decl(2, Ty::usize(), Some("i")),
        decl(3, Ty::usize(), Some("big")),
        decl(4, Ty::Bool, None),
        decl(5, Ty::usize(), None),
        decl(6, Ty::usize(), Some("_9")),
        decl(7, ptr_u8(), None),
        decl(8, spelling.count_ty(), None),
        decl(9, Ty::usize(), None),
    ];
    let blocks = vec![
        block(
            0,
            vec![load(6, 1, 1), mov(9, 3), mov(5, 2), spelling.guard(4, 5, 9)],
            branch(4, 1, 3),
        ),
        block(1, vec![load(7, 1, 0), spelling.count_def(8, 2)], spelling.call(7, 8, 0, 2)),
        block(2, vec![], Terminator::Return),
        block(3, vec![], Terminator::Return),
    ];
    function("raw_name_collision", spelling, locals, 3, blocks)
}

/// The same body with the length local named `m`: nothing bounds `i` by the length,
/// so this must not prove either (the collision test's proof is the name's alone).
fn raw_name_control(spelling: Spelling) -> VerifiableFunction {
    let mut f = raw_name_collision(spelling);
    f.name = "raw_name_control".into();
    f.def_path = "backing_first_load::raw_name_control".into();
    f.body.locals[6].name = Some("m".into());
    f
}

#[test]
fn a_length_local_is_spelled_as_the_pipeline_spells_it() {
    assert_no_false_proof(&[raw_name_collision, raw_name_control]);
}

/// A `Buf` with a third field `next: &Buf` naming ANOTHER `Buf`. It is still the
/// certified backing struct (one raw-pointer field, one unsigned field).
fn buf3() -> Ty {
    let Ty::Adt {
        adt_kind,
        layout,
        variants,
        fields,
        disc_index_safe,
        faithful_enum_repr,
        enum_layout,
        arbitrary_precision,
        validity_wrapper,
        ..
    } = buf()
    else {
        unreachable!()
    };
    let mut fields: Vec<_> = fields.iter().cloned().collect();
    fields.push(("next".into(), buf_ref()));
    Ty::Adt {
        adt_kind,
        layout,
        variants,
        name: "Buf".into(),
        fields: fields.into(),
        disc_index_safe,
        faithful_enum_repr,
        enum_layout,
        arbitrary_precision,
        validity_wrapper,
    }
}

/// `let s: &Buf = <s_def>; if i < self.len { s.ptr.add(i) }` over the 3-field `Buf`.
fn via(name: &str, spelling: Spelling, s_def: Rvalue) -> VerifiableFunction {
    let r3 = Ty::Ref { mutable: false, inner: Box::new(buf3()) };
    // _1 self, _2 i, _3 s, _4 cond, _5 i copy, _6 len load, _7 ptr load, _8 count
    let locals = vec![
        decl(0, spelling.return_ty(), None),
        decl(1, r3.clone(), Some("self")),
        decl(2, Ty::usize(), Some("i")),
        decl(3, r3, Some("s")),
        decl(4, Ty::Bool, None),
        decl(5, Ty::usize(), None),
        decl(6, Ty::usize(), None),
        decl(7, ptr_u8(), None),
        decl(8, spelling.count_ty(), None),
    ];
    let blocks = vec![
        block(
            0,
            vec![assign(3, s_def), mov(5, 2), load(6, 1, 1), spelling.guard(4, 5, 6)],
            branch(4, 1, 3),
        ),
        block(1, vec![load(7, 3, 0), spelling.count_def(8, 2)], spelling.call(7, 8, 0, 2)),
        block(2, vec![], Terminator::Return),
        block(3, vec![], Terminator::Return),
    ];
    function(name, spelling, locals, 2, blocks)
}

/// `let s = &*self.next;`: a reborrow of ANOTHER value's pointee (the chain may
/// follow only `&(*r)` of a root `r`, not a deeper path).
fn reborrow_next(spelling: Spelling) -> VerifiableFunction {
    let next = Place {
        local: 1,
        projections: vec![Projection::Deref, Projection::Field(2), Projection::Deref],
    };
    via("reborrow_next", spelling, Rvalue::Ref { mutable: false, place: next })
}

/// `let s = self.next;`: a copy of ANOTHER value's reference (the chain may follow
/// only a whole-local copy of a root, not a field).
fn copy_next(spelling: Spelling) -> VerifiableFunction {
    via("copy_next", spelling, Rvalue::Use(Operand::Copy(field(1, 2))))
}

/// CAPABILITY CONTROL: `let s = &*self;` is the same value as `self`.
fn ok_through_reborrow(spelling: Spelling) -> VerifiableFunction {
    let deref_self = Place { local: 1, projections: vec![Projection::Deref] };
    via("ok_through_reborrow", spelling, Rvalue::Ref { mutable: false, place: deref_self })
}

/// CAPABILITY CONTROL over the 3-field `Buf`: `let s = self;`.
fn ok_through_copy3(spelling: Spelling) -> VerifiableFunction {
    via("ok_through_copy3", spelling, Rvalue::Use(copy(1)))
}

#[test]
fn a_reference_reached_through_a_field_is_another_value() {
    assert_no_false_proof(&[reborrow_next, copy_next]);
}

#[test]
fn a_shared_reborrow_of_the_same_value_still_proves() {
    let mut missing = Vec::new();
    let shapes: [fn(Spelling) -> VerifiableFunction; 2] = [ok_through_reborrow, ok_through_copy3];
    for shape in shapes {
        for spelling in [Spelling::Add, Spelling::FromRawParts] {
            let func = shape(spelling);
            for hardened in [false, true] {
                let verdicts = bounds_verdicts(&func, hardened);
                if verdicts.is_empty() || !verdicts.iter().all(|(_, proved)| *proved) {
                    missing.push(format!(
                        "{} {spelling:?} hardened={hardened}: {verdicts:?}",
                        func.name
                    ));
                }
            }
        }
    }
    assert!(missing.is_empty(), "a reborrow or copy of `self` is `self`:\n{}", missing.join("\n"));
}
