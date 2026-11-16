//! Per-root translation: trust-ir bodies -> one [`EventProgram`] (design
//! §2.3-§2.4). See the crate docs for the pipeline; [`crate::rules::RULES`]
//! lists every rule with its approximation direction.
//!
//! The abstract value of an SSA value ([`AVal`]) is a literal or a program
//! variable, a guard ([`Cond`]), an untracked value (`Expr::Opaque` once
//! materialized), a pointer into a promoted `alloca` cell (or an unknown
//! pointer), or an aggregate of those. Program variables are global per
//! actor; each translated function instance ([`Spec`]) has its own, which
//! is sound because recursion is refused.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use trust_ir::{
    BinOp, Block as IrBlock, BlockId as IrBlockId, CastOp, Constant, FuncId, ICmpOp, Inst,
    InstrNode, Module, OverflowOp, SourceSpan, Ty, UnOp, ValueId,
};
use trust_platform::std_summaries::{self, CommandShape, StdioPlan};
use trust_platform::symbols::{self, ClauseId, Modeled};
use trust_platform::{Call, Errno, Oracle, SocketOp, darwin};
use trust_platform_derive::lower::{LowerError, lower};
use trust_platform_derive::program::{
    Bind, Block, Body, BodyId, CmpOp, Cond, Event, EventProgram, Expr, FdInherit, FdParam, Loc,
    Operand, Policies, Provenance, Root, SpawnSite, StdCall, Stmt, StmtKind, Term, Var, VarId,
};

use crate::audit::is_panic;
use crate::rules::{
    P_FORK_SUCCEEDS, P_HOOK_HARNESS, P_NO_LANES, P_NO_WRAP, P_PANIC, P_STD_ROW_NOMINAL,
};
use crate::shape::{IntTy, Shape, fd_carrier_in, int_ty, shape_of, trivially_dropped};
use crate::sites::{Scan, std_is, std_under};
use crate::{
    Callee, CensusContext, CensusOptions, CensusPremise, IrSite, PolicySite, Refusal, RootKind,
    RootProgram, fn_path,
};

/// Which process a body runs in.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Ctx {
    /// The root process.
    Parent,
    /// A forked child before its exec (a raw fork's continuation, a
    /// `pre_exec` closure): descriptor loops become `ForRange`.
    Child,
}

/// Where an untracked value came from (printed with every refusal it
/// causes).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Why {
    Param(String),
    Call(String),
    Trunc,
    Op(String),
    Memory,
    Undef,
}

impl std::fmt::Display for Why {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Why::Param(p) => write!(f, "the root's parameter `{p}` (library environment)"),
            Why::Call(c) => write!(f, "the result of `{c}`"),
            Why::Trunc => write!(f, "a truncating cast"),
            Why::Op(o) => write!(f, "{o}"),
            Why::Memory => write!(f, "a load through a pointer the census does not follow"),
            Why::Undef => write!(f, "an undefined value"),
        }
    }
}

/// A pointer value.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PtrVal {
    /// Into promoted cell `cell`, at a field path.
    Cell {
        cell: usize,
        path: Vec<u32>,
    },
    Null,
    Unknown,
}

/// The abstract value of an SSA value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AVal {
    Op(Operand),
    Opaque(Why),
    Cond(Cond),
    Ptr(PtrVal),
    Agg(Vec<AVal>),
    Unit,
    Fn(FuncId),
}

/// One leaf of a flattened value: a variable (an integer, or an untracked
/// blob) or a pointer (whose value is not kept in a variable).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Leaf {
    Var(VarId),
    Ptr,
}

#[derive(Clone, Debug)]
struct Cell {
    shape: Shape,
    leaves: Vec<Leaf>,
    fd_carrier: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct SpecKey {
    func: FuncId,
    ctx: Ctx,
    ptrs: Vec<PtrVal>,
    hook: bool,
    /// In a child: the program site whose child runs this instance (an
    /// `exec*` in it is that site's exec: its census site maps there).
    /// Instances are not shared between two sites' children.
    child_site: Option<usize>,
}

/// One translated function instance.
#[derive(Clone, Debug)]
struct Spec {
    body: BodyId,
    params: Vec<(Shape, Vec<Leaf>)>,
    ret: (Shape, Vec<Leaf>),
    may_halt: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FnKind {
    Normal,
    ForkChild,
    Hook,
}

struct PB {
    stmts: Vec<Stmt>,
    term: Option<(Term, Loc, Option<String>)>,
}

/// The translation state of one function instance.
struct FnState {
    func: FuncId,
    ctx: Ctx,
    kind: FnKind,
    body: BodyId,
    name: String,
    blocks: Vec<PB>,
    cur: usize,
    values: BTreeMap<ValueId, AVal>,
    cmp_ty: BTreeMap<ValueId, IntTy>,
    entries: BTreeMap<IrBlockId, usize>,
    bparams: BTreeMap<IrBlockId, Vec<(Shape, Vec<Leaf>)>>,
    work: VecDeque<(IrBlockId, usize, usize)>,
    ret: (Shape, Vec<Leaf>),
    may_halt: bool,
    promotable: BTreeSet<ValueId>,
    /// The producer's overflow asserts: assert condition -> overflow flag
    /// (and each flag -> itself).
    overflow_asserted: BTreeMap<ValueId, ValueId>,
    stopped: bool,
    /// In a child: the program site whose child this is ([`SpecKey`]).
    child_site: Option<usize>,
}

impl FnState {
    fn new_block(&mut self) -> usize {
        self.blocks.push(PB { stmts: Vec::new(), term: None });
        self.blocks.len() - 1
    }

    fn push(&mut self, kind: StmtKind, loc: &Loc) {
        self.blocks[self.cur].stmts.push(Stmt { kind, loc: loc.clone(), tag: None });
    }

    fn terminate(&mut self, term: Term, loc: &Loc, tag: Option<String>) {
        let b = &mut self.blocks[self.cur];
        if b.term.is_none() {
            b.term = Some((term, loc.clone(), tag));
        }
    }

    /// Branch on `cond`; returns (then, else) blocks, `cur` unchanged.
    fn branch(&mut self, cond: Cond, loc: &Loc, tag: Option<String>) -> (usize, usize) {
        let t = self.new_block();
        let e = self.new_block();
        self.terminate(Term::Branch { cond, then: t, els: e }, loc, tag);
        (t, e)
    }
}

/// Signals that the current path ended (a terminator or a halt).
struct Stop;

/// Why a path ends where the program's would not (or might not).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HaltKind {
    /// A failed assert or a panicking call (premise P-PANIC-ENDS-PATH).
    Panic,
    /// A wrapping add/sub that would wrap (premise P-NO-WRAP).
    Wrap,
    /// `unreachable` / `assume(false)` / `_exit` in the root process: exact.
    Exact,
    /// A callee ended its path: this one ends with it.
    Propagate,
}

/// The translation of one root.
pub(crate) struct RootT<'a> {
    m: &'a Module,
    cx: &'a dyn CensusContext,
    o: &'a CensusOptions,
    callees: &'a [Callee],
    scan: &'a Scan,
    vars: Vec<Var>,
    bodies: Vec<Option<Body>>,
    body_ctx: Vec<Ctx>,
    sites: Vec<SpawnSite>,
    policy_sites: Vec<PolicySite>,
    fd_params: Vec<FdParam>,
    locs: BTreeMap<Loc, IrSite>,
    refusals: Vec<(Option<IrSite>, Refusal)>,
    premises: BTreeMap<&'static str, CensusPremise>,
    halt_var: VarId,
    pub(crate) halt_blocks: BTreeMap<(BodyId, usize), HaltKind>,
    specs: BTreeMap<SpecKey, Spec>,
    stack: Vec<FuncId>,
    path: BTreeSet<FuncId>,
    cells: Vec<Cell>,
    origins: BTreeMap<VarId, (Loc, Why)>,
    notes: Vec<String>,
    /// Variables known never to be 0: the parent's view of a raw fork's
    /// result (the child's pid, or -1).
    nonzero: BTreeSet<VarId>,
}

/// Command builder methods that only configure the command (no platform
/// effect until it is spawned; the configuration is C4's).
const COMMAND_CONFIG: &[&str] = &[
    "new",
    "arg",
    "args",
    "env",
    "envs",
    "env_remove",
    "env_clear",
    "current_dir",
    "stdin",
    "stdout",
    "stderr",
    "uid",
    "gid",
    "groups",
    "process_group",
    "arg0",
    "get_program",
    "get_args",
    "get_envs",
    "get_current_dir",
];

fn cmp_of(op: ICmpOp) -> (CmpOp, bool, Option<bool>) {
    // (op, swap operands, wants signed view: None = either)
    match op {
        ICmpOp::Eq => (CmpOp::Eq, false, None),
        ICmpOp::Ne => (CmpOp::Ne, false, None),
        ICmpOp::Slt => (CmpOp::Lt, false, Some(true)),
        ICmpOp::Sle => (CmpOp::Le, false, Some(true)),
        ICmpOp::Sgt => (CmpOp::Gt, false, Some(true)),
        ICmpOp::Sge => (CmpOp::Ge, false, Some(true)),
        ICmpOp::Ult => (CmpOp::Lt, false, Some(false)),
        ICmpOp::Ule => (CmpOp::Le, false, Some(false)),
        ICmpOp::Ugt => (CmpOp::Gt, false, Some(false)),
        ICmpOp::Uge => (CmpOp::Ge, false, Some(false)),
    }
}

/// `n` (any integer) as a value of `t` (two's complement wrap).
fn wrap_to(n: i128, t: IntTy) -> Option<i64> {
    if t.bits == 1 {
        return Some(i64::from(n & 1 != 0));
    }
    if t.bits >= 64 {
        return i64::try_from(n).ok();
    }
    let m = 1i128 << t.bits;
    let mut v = n.rem_euclid(m);
    if t.signed && v >= m / 2 {
        v -= m;
    }
    i64::try_from(v).ok()
}

fn fold_bin(op: BinOp, t: IntTy, a: i64, b: i64) -> Option<i64> {
    let (a, b) = (i128::from(a), i128::from(b));
    let ua = |x: i128| if t.bits < 64 { x.rem_euclid(1i128 << t.bits) } else { x };
    let r = match op {
        BinOp::Add => a + b,
        BinOp::Sub => a - b,
        BinOp::Mul => a * b,
        BinOp::SDiv if b != 0 => a / b,
        BinOp::SRem if b != 0 => a % b,
        BinOp::UDiv if b != 0 => ua(a) / ua(b),
        BinOp::URem if b != 0 => ua(a) % ua(b),
        BinOp::And | BinOp::BAnd => a & b,
        BinOp::Or | BinOp::BOr => a | b,
        BinOp::Xor | BinOp::BXor => a ^ b,
        BinOp::Shl if (0..i128::from(t.bits.max(1))).contains(&b) => a << b,
        BinOp::AShr if (0..i128::from(t.bits.max(1))).contains(&b) => a >> b,
        BinOp::LShr if (0..i128::from(t.bits.max(1))).contains(&b) => ua(a) >> b,
        _ => return None,
    };
    wrap_to(r, t)
}

/// Leaf `i`'s position range in a shape, by field path.
fn sub_shape<'s>(shape: &'s Shape, path: &[u32]) -> Option<(usize, &'s Shape)> {
    let mut start = 0usize;
    let mut s = shape;
    for &i in path {
        let Shape::Agg(fields) = s else { return None };
        let i = i as usize;
        start += fields.get(..i)?.iter().map(Shape::leaf_count).sum::<usize>();
        s = fields.get(i)?;
    }
    Some((start, s))
}

fn shape_compatible(a: &Shape, b: &Shape) -> bool {
    match (a, b) {
        (Shape::Int(_) | Shape::Blob, Shape::Int(_) | Shape::Blob) | (Shape::Ptr, Shape::Ptr) => {
            true
        }
        (Shape::Unit, Shape::Unit) => true,
        (Shape::Agg(x), Shape::Agg(y)) => {
            x.len() == y.len() && x.iter().zip(y).all(|(p, q)| shape_compatible(p, q))
        }
        _ => false,
    }
}

impl<'a> RootT<'a> {
    fn new(
        m: &'a Module,
        cx: &'a dyn CensusContext,
        o: &'a CensusOptions,
        callees: &'a [Callee],
        scan: &'a Scan,
    ) -> RootT<'a> {
        let mut rt = RootT {
            m,
            cx,
            o,
            callees,
            scan,
            vars: Vec::new(),
            bodies: Vec::new(),
            body_ctx: Vec::new(),
            sites: Vec::new(),
            policy_sites: Vec::new(),
            fd_params: Vec::new(),
            locs: BTreeMap::new(),
            refusals: Vec::new(),
            premises: BTreeMap::new(),
            halt_var: 0,
            halt_blocks: BTreeMap::new(),
            specs: BTreeMap::new(),
            stack: Vec::new(),
            path: BTreeSet::new(),
            cells: Vec::new(),
            origins: BTreeMap::new(),
            notes: Vec::new(),
            nonzero: BTreeSet::new(),
        };
        rt.vars.push(Var { name: "__census_halt".to_string(), init: 0 });
        rt.halt_var = 0;
        rt
    }

    fn var(&mut self, name: String) -> VarId {
        self.vars.push(Var { name, init: -1 });
        self.vars.len() - 1
    }

    fn refuse(&mut self, at: Option<IrSite>, r: Refusal) {
        if !self.refusals.iter().any(|(a, x)| *a == at && *x == r) {
            self.refusals.push((at, r));
        }
    }

    fn premise(&mut self, code: &'static str, text: &str, at: &Loc) {
        let p = self.premises.entry(code).or_insert_with(|| CensusPremise {
            code,
            text: text.to_string(),
            at: Vec::new(),
        });
        if !p.at.contains(&at.0) {
            p.at.push(at.0.clone());
        }
    }

    fn func(&self, f: FuncId) -> &'a trust_ir::Function {
        &self.m.functions[f.as_usize()]
    }

    fn func_ty(&self, f: FuncId) -> Option<&'a trust_ir::FuncTy> {
        self.m.func_types.get(self.func(f).ty.as_usize())
    }

    fn ret_shape(&self, f: FuncId) -> Shape {
        match self.func_ty(f).map(|t| t.returns.as_slice()) {
            None | Some([]) => Shape::Unit,
            Some([t]) => shape_of(self.m, t),
            Some(ts) => Shape::Agg(ts.iter().map(|t| shape_of(self.m, t)).collect()),
        }
    }

    fn ret_ty(&self, f: FuncId) -> Option<&'a Ty> {
        self.func_ty(f).and_then(|t| t.returns.first())
    }

    fn fresh_leaves(&mut self, shape: &Shape, name: &str) -> Vec<Leaf> {
        let mut out = Vec::new();
        self.fresh_into(shape, name, &mut out);
        out
    }

    fn fresh_into(&mut self, shape: &Shape, name: &str, out: &mut Vec<Leaf>) {
        match shape {
            Shape::Int(_) | Shape::Blob => {
                let v = self.var(format!("{name}.{}", out.len()));
                out.push(Leaf::Var(v));
            }
            Shape::Ptr => out.push(Leaf::Ptr),
            Shape::Unit => {}
            Shape::Agg(fs) => {
                for f in fs {
                    self.fresh_into(f, name, out);
                }
            }
        }
    }

    /// The value of `shape` read from `leaves` (pointer leaves take
    /// `ptrs` in order, else unknown).
    fn aval_from(
        shape: &Shape,
        leaves: &[Leaf],
        pos: &mut usize,
        ptrs: &mut dyn Iterator<Item = PtrVal>,
    ) -> AVal {
        match shape {
            Shape::Int(_) | Shape::Blob => {
                let v = match leaves.get(*pos) {
                    Some(Leaf::Var(v)) => AVal::Op(Operand::Var(*v)),
                    _ => AVal::Opaque(Why::Op("a missing leaf".into())),
                };
                *pos += 1;
                v
            }
            Shape::Ptr => {
                *pos += 1;
                AVal::Ptr(ptrs.next().unwrap_or(PtrVal::Unknown))
            }
            Shape::Unit => AVal::Unit,
            Shape::Agg(fs) => {
                AVal::Agg(fs.iter().map(|f| Self::aval_from(f, leaves, pos, ptrs)).collect())
            }
        }
    }

    /// A skeleton value of `shape` whose leaves are untracked.
    fn skeleton(shape: &Shape, why: &Why) -> AVal {
        match shape {
            Shape::Int(_) | Shape::Blob => AVal::Opaque(why.clone()),
            Shape::Ptr => AVal::Ptr(PtrVal::Unknown),
            Shape::Unit => AVal::Unit,
            Shape::Agg(fs) => AVal::Agg(fs.iter().map(|f| Self::skeleton(f, why)).collect()),
        }
    }

    fn loc(
        &mut self,
        fs: &FnState,
        block: IrBlockId,
        inst: usize,
        span: Option<SourceSpan>,
    ) -> Loc {
        let at = IrSite { func: fs.func, block, inst, span };
        let text = span.map_or_else(|| "?".to_string(), |s| self.cx.render_span(s));
        let loc = Loc(format!("{text} {} [{at}]", fs.name));
        self.locs.insert(loc.clone(), at);
        loc
    }

    // ---- scalar materialization -------------------------------------------

    fn opaque_var(&mut self, fs: &mut FnState, why: Why, loc: &Loc) -> VarId {
        let v = self.var(format!("{}:opaque", fs.name));
        fs.push(StmtKind::Assign { var: v, expr: Expr::Opaque }, loc);
        self.origins.insert(v, (loc.clone(), why));
        v
    }

    fn cond_var(&mut self, fs: &mut FnState, c: Cond, loc: &Loc) -> VarId {
        let v = self.var(format!("{}:bool", fs.name));
        let (t, e) = fs.branch(c, loc, None);
        let j = fs.new_block();
        fs.cur = t;
        fs.push(StmtKind::Assign { var: v, expr: Expr::Use(Operand::Lit(1)) }, loc);
        fs.terminate(Term::Goto(j), loc, None);
        fs.cur = e;
        fs.push(StmtKind::Assign { var: v, expr: Expr::Use(Operand::Lit(0)) }, loc);
        fs.terminate(Term::Goto(j), loc, None);
        fs.cur = j;
        v
    }

    /// A scalar operand for `v`, materializing guards and untracked values.
    fn operand(&mut self, fs: &mut FnState, v: &AVal, loc: &Loc) -> Operand {
        match v {
            AVal::Op(o) => *o,
            AVal::Cond(Cond::Const(b)) => Operand::Lit(i64::from(*b)),
            AVal::Cond(c) => Operand::Var(self.cond_var(fs, c.clone(), loc)),
            AVal::Opaque(w) => Operand::Var(self.opaque_var(fs, w.clone(), loc)),
            AVal::Agg(fs_) => {
                let inner: Vec<&AVal> = fs_.iter().filter(|x| !matches!(x, AVal::Unit)).collect();
                if let [one] = inner.as_slice() {
                    let one = (*one).clone();
                    self.operand(fs, &one, loc)
                } else {
                    Operand::Var(self.opaque_var(
                        fs,
                        Why::Op("an aggregate used as a scalar".into()),
                        loc,
                    ))
                }
            }
            AVal::Ptr(PtrVal::Null) => Operand::Lit(0),
            AVal::Ptr(_) | AVal::Unit | AVal::Fn(_) => {
                Operand::Var(self.opaque_var(fs, Why::Op("a pointer used as a scalar".into()), loc))
            }
        }
    }

    fn cond(&mut self, v: &AVal) -> Cond {
        match v {
            AVal::Cond(c) => c.clone(),
            AVal::Op(Operand::Lit(n)) => Cond::Const(*n != 0),
            AVal::Op(o) => Cond::Cmp(CmpOp::Ne, *o, Operand::Lit(0)),
            _ => Cond::Nondet,
        }
    }

    /// Flatten `v` by `shape` into scalar operands / pointers.
    fn flatten(
        &mut self,
        fs: &mut FnState,
        v: &AVal,
        shape: &Shape,
        loc: &Loc,
        out: &mut Vec<Result<Operand, PtrVal>>,
    ) {
        match shape {
            Shape::Int(_) | Shape::Blob => {
                let o = match v {
                    AVal::Op(_) | AVal::Cond(_) | AVal::Opaque(_) => self.operand(fs, v, loc),
                    AVal::Agg(_) => self.operand(fs, v, loc),
                    _ => Operand::Var(self.opaque_var(fs, Why::Op("a shape mismatch".into()), loc)),
                };
                out.push(Ok(o));
            }
            Shape::Ptr => out.push(Err(match v {
                AVal::Ptr(p) => p.clone(),
                _ => PtrVal::Unknown,
            })),
            Shape::Unit => {}
            Shape::Agg(fields) => {
                let parts: Vec<AVal> = match v {
                    AVal::Agg(xs) => xs.clone(),
                    _ => Vec::new(),
                };
                for (i, f) in fields.iter().enumerate() {
                    let p = parts.get(i).cloned().unwrap_or_else(|| match v {
                        AVal::Opaque(w) => Self::skeleton(f, w),
                        _ => Self::skeleton(f, &Why::Op("a shape mismatch".into())),
                    });
                    self.flatten(fs, &p, f, loc, out);
                }
            }
        }
    }

    /// Assign `v` (flattened by `shape`) to `leaves`, through temporaries
    /// when a source reads a destination (parallel copy).
    fn assign_leaves(
        &mut self,
        fs: &mut FnState,
        v: &AVal,
        shape: &Shape,
        leaves: &[Leaf],
        loc: &Loc,
    ) {
        let mut flat = Vec::new();
        self.flatten(fs, v, shape, loc, &mut flat);
        self.copy_flat(fs, &flat, leaves, loc);
    }

    fn copy_flat(
        &mut self,
        fs: &mut FnState,
        flat: &[Result<Operand, PtrVal>],
        leaves: &[Leaf],
        loc: &Loc,
    ) {
        let dests: BTreeSet<VarId> = leaves
            .iter()
            .filter_map(|l| if let Leaf::Var(v) = l { Some(*v) } else { None })
            .collect();
        let reads_dest = flat.iter().any(|x| matches!(x, Ok(Operand::Var(v)) if dests.contains(v)));
        let mut pairs = Vec::new();
        for (x, l) in flat.iter().zip(leaves) {
            match (x, l) {
                (Ok(o), Leaf::Var(d)) => pairs.push((*d, *o)),
                (Err(PtrVal::Cell { cell, .. }), Leaf::Ptr) => {
                    let cell = *cell;
                    self.cell_escapes(
                        fs,
                        cell,
                        loc,
                        "a pointer to it flows through a block parameter or memory",
                    );
                }
                _ => {}
            }
        }
        if reads_dest {
            let temps: Vec<(VarId, VarId)> = pairs
                .iter()
                .map(|(d, o)| {
                    let t = self.var(format!("{}:copy", fs.name));
                    fs.push(StmtKind::Assign { var: t, expr: Expr::Use(*o) }, loc);
                    (*d, t)
                })
                .collect();
            for (d, t) in temps {
                fs.push(StmtKind::Assign { var: d, expr: Expr::Use(Operand::Var(t)) }, loc);
            }
        } else {
            for (d, o) in pairs {
                fs.push(StmtKind::Assign { var: d, expr: Expr::Use(o) }, loc);
            }
        }
    }

    /// A pointer to a promoted cell escaped where the census cannot follow
    /// it: the cell's later contents are unknown.
    fn cell_escapes(&mut self, fs: &mut FnState, cell: usize, loc: &Loc, how: &str) {
        let at = self.locs.get(loc).copied();
        if let Some(c) = self.cells.get(cell).and_then(|c| c.fd_carrier.clone()) {
            self.refuse(
                at,
                Refusal::FdEscape { what: format!("a cell holding `{c}` escapes: {how}") },
            );
        } else {
            self.refuse(
                at,
                Refusal::IrUnsupported {
                    inst: format!("a pointer to a tracked local escapes: {how} (at {loc})"),
                },
            );
        }
        self.havoc_cell(fs, cell, &[], loc);
    }

    /// The callee may write the cell (through a pointer argument): its
    /// leaves become untracked.
    fn havoc_cell(&mut self, fs: &mut FnState, cell: usize, path: &[u32], loc: &Loc) {
        let Some(c) = self.cells.get(cell).cloned() else { return };
        let Some((start, sub)) = sub_shape(&c.shape, path) else { return };
        for l in c.leaves.iter().skip(start).take(sub.leaf_count()) {
            if let Leaf::Var(v) = l {
                fs.push(StmtKind::Assign { var: *v, expr: Expr::Opaque }, loc);
                self.origins.insert(
                    *v,
                    (loc.clone(), Why::Op("a write by a callee the census does not model".into())),
                );
            }
        }
    }

    /// Arguments passed to a callee the census does not translate: pointer
    /// arguments into cells are havocked; fd carriers passed by value or by
    /// pointer escape (C-13's widened escape rule).
    fn havoc_args(
        &mut self,
        fs: &mut FnState,
        callee: FuncId,
        args: &[ValueId],
        loc: &Loc,
        what: &str,
    ) {
        let at = self.locs.get(loc).copied();
        let ptys: Vec<Ty> = self.func_ty(callee).map(|t| t.params.clone()).unwrap_or_default();
        for (i, a) in args.iter().enumerate() {
            let v = fs.values.get(a).cloned().unwrap_or(AVal::Opaque(Why::Undef));
            if let Some(t) = ptys.get(i)
                && let Some(c) = fd_carrier_in(self.m, t)
            {
                self.refuse(
                    at,
                    Refusal::FdEscape { what: format!("`{c}` passed by value to {what}") },
                );
            }
            let mut ptrs = Vec::new();
            collect_ptrs(&v, &mut ptrs);
            for p in ptrs {
                if let PtrVal::Cell { cell, path } = p {
                    if let Some(c) = self.cells.get(cell).and_then(|c| c.fd_carrier.clone()) {
                        self.refuse(
                            at,
                            Refusal::FdEscape {
                                what: format!("a pointer to `{c}` passed to {what}"),
                            },
                        );
                    }
                    self.havoc_cell(fs, cell, &path, loc);
                }
            }
        }
    }

    fn set_result(&mut self, fs: &mut FnState, node: &InstrNode, v: AVal) {
        if let Some(r) = node.results.first() {
            fs.values.insert(*r, v);
        }
    }

    fn opaque_result(&mut self, fs: &mut FnState, node: &InstrNode, why: Why) {
        self.set_result(fs, node, AVal::Opaque(why));
    }

    // ---- halts ------------------------------------------------------------

    /// End the path here.
    fn halt(&mut self, fs: &mut FnState, loc: &Loc, kind: HaltKind) {
        fs.push(StmtKind::Assign { var: self.halt_var, expr: Expr::Use(Operand::Lit(1)) }, loc);
        let term = if fs.kind == FnKind::Hook {
            Term::Return(Some(Operand::Lit(-1)))
        } else {
            Term::Return(None)
        };
        fs.terminate(term, loc, None);
        self.halt_blocks.insert((fs.body, fs.cur), kind);
        fs.may_halt = true;
    }

    /// Branch: on `ok` continue, else end the path.
    fn guard(
        &mut self,
        fs: &mut FnState,
        ok: Cond,
        loc: &Loc,
        tag: Option<String>,
        kind: HaltKind,
    ) {
        if ok == Cond::Const(true) {
            return;
        }
        let (t, e) = fs.branch(ok, loc, tag);
        fs.cur = e;
        self.halt(fs, loc, kind);
        fs.cur = t;
    }

    // ---- function instances -----------------------------------------------

    fn spec(&mut self, key: SpecKey, at: Option<IrSite>) -> Option<Spec> {
        if let Some(s) = self.specs.get(&key) {
            return Some(s.clone());
        }
        if self.stack.len() >= self.o.max_inline_depth {
            self.refuse(
                at,
                Refusal::Size { what: "the inlining depth".into(), limit: self.o.max_inline_depth },
            );
            return None;
        }
        if self.bodies.len() >= self.o.max_bodies {
            self.refuse(
                at,
                Refusal::Size { what: "the bodies per root".into(), limit: self.o.max_bodies },
            );
            return None;
        }
        let f = key.func;
        let func = self.func(f);
        let name = fn_path(self.m, f);
        let body = self.bodies.len();
        self.bodies.push(None);
        self.body_ctx.push(key.ctx);
        self.stack.push(f);
        self.path.insert(f);
        let ptys: Vec<Ty> = self.func_ty(f).map(|t| t.params.clone()).unwrap_or_default();
        let mut ptrs = key.ptrs.clone().into_iter();
        let mut params = Vec::new();
        let mut values = BTreeMap::new();
        let entry = func.blocks.iter().find(|b| b.id == func.entry).or(func.blocks.first());
        let entry_params: Vec<ValueId> =
            entry.map(|b| b.params.iter().map(|(v, _)| *v).collect()).unwrap_or_default();
        for (i, t) in ptys.iter().enumerate() {
            let sh = shape_of(self.m, t);
            let leaves = self.fresh_leaves(&sh, &format!("{name}:%{i}"));
            let mut pos = 0;
            let v = Self::aval_from(&sh, &leaves, &mut pos, &mut ptrs);
            if let Some(id) = entry_params.get(i) {
                values.insert(*id, v);
            }
            params.push((sh, leaves));
        }
        let ret_sh = self.ret_shape(f);
        let ret_leaves = self.fresh_leaves(&ret_sh, &format!("{name}:ret"));
        let kind = if key.hook { FnKind::Hook } else { FnKind::Normal };
        let mut fs =
            self.fn_state(f, key.ctx, kind, body, name.clone(), values, (ret_sh, ret_leaves));
        fs.child_site = key.child_site;
        if let Some(e) = entry {
            fs.entries.insert(e.id, 0);
            fs.work.push_back((e.id, 0, 0));
        }
        self.run_fn(&mut fs);
        self.stack.pop();
        let spec =
            Spec { body, params: params.clone(), ret: fs.ret.clone(), may_halt: fs.may_halt };
        let body_params: Vec<VarId> = params
            .iter()
            .flat_map(|(_, ls)| {
                ls.iter().filter_map(|l| if let Leaf::Var(v) = l { Some(*v) } else { None })
            })
            .collect();
        self.finish_body(fs, body_params);
        self.specs.insert(key, spec.clone());
        Some(spec)
    }

    #[allow(clippy::too_many_arguments)]
    fn fn_state(
        &self,
        f: FuncId,
        ctx: Ctx,
        kind: FnKind,
        body: BodyId,
        name: String,
        values: BTreeMap<ValueId, AVal>,
        ret: (Shape, Vec<Leaf>),
    ) -> FnState {
        let (promotable, overflow_asserted) = prepass(self.func(f));
        FnState {
            func: f,
            ctx,
            kind,
            body,
            name,
            blocks: vec![PB { stmts: Vec::new(), term: None }],
            cur: 0,
            values,
            cmp_ty: BTreeMap::new(),
            entries: BTreeMap::new(),
            bparams: BTreeMap::new(),
            work: VecDeque::new(),
            ret,
            may_halt: false,
            promotable,
            overflow_asserted,
            stopped: false,
            child_site: None,
        }
    }

    fn finish_body(&mut self, fs: FnState, params: Vec<VarId>) {
        let end = Loc(format!("<end of {}>", fs.name));
        let blocks = fs
            .blocks
            .into_iter()
            .map(|b| {
                let (term, term_loc, term_tag) =
                    b.term.unwrap_or((Term::Return(None), end.clone(), None));
                Block { stmts: b.stmts, term, term_loc, term_tag }
            })
            .collect();
        self.bodies[fs.body] = Some(Body { name: fs.name, params, blocks });
    }

    fn block_index(&self, f: FuncId, b: IrBlockId) -> Option<usize> {
        self.func(f).blocks.iter().position(|x| x.id == b)
    }

    fn enqueue(&mut self, fs: &mut FnState, b: IrBlockId) -> usize {
        if let Some(p) = fs.entries.get(&b) {
            return *p;
        }
        let p = fs.new_block();
        fs.entries.insert(b, p);
        if let Some(bi) = self.block_index(fs.func, b) {
            let func = self.func(fs.func);
            let mut slots = Vec::new();
            for (v, t) in &func.blocks[bi].params {
                let sh = shape_of(self.m, t);
                let leaves = self.fresh_leaves(&sh, &format!("{}:%{}", fs.name, v.0));
                let mut pos = 0;
                let val = Self::aval_from(&sh, &leaves, &mut pos, &mut std::iter::empty());
                fs.values.insert(*v, val);
                slots.push((sh, leaves));
            }
            fs.bparams.insert(b, slots);
        }
        fs.work.push_back((b, 0, p));
        p
    }

    fn run_fn(&mut self, fs: &mut FnState) {
        while let Some((b, start, p)) = fs.work.pop_front() {
            if fs.blocks.len() > self.o.max_blocks {
                let at = Some(IrSite { func: fs.func, block: b, inst: start, span: None });
                self.refuse(
                    at,
                    Refusal::Size {
                        what: format!("the blocks of `{}`", fs.name),
                        limit: self.o.max_blocks,
                    },
                );
                return;
            }
            let Some(bi) = self.block_index(fs.func, b) else {
                self.refuse(
                    None,
                    Refusal::Internal { detail: format!("no block bb{} in `{}`", b.0, fs.name) },
                );
                continue;
            };
            let block = &self.func(fs.func).blocks[bi];
            fs.cur = p;
            fs.stopped = false;
            for idx in start..block.body.len() {
                if self.inst(fs, block, idx).is_err() {
                    break;
                }
            }
            if !fs.stopped {
                let loc = Loc(format!("<end of bb{} of {}>", b.0, fs.name));
                self.refuse(
                    None,
                    Refusal::Internal {
                        detail: format!("bb{} of `{}` has no terminator", b.0, fs.name),
                    },
                );
                fs.terminate(Term::Return(None), &loc, None);
            }
        }
    }

    // ---- instructions -----------------------------------------------------

    fn val(fs: &FnState, v: ValueId) -> AVal {
        fs.values.get(&v).cloned().unwrap_or(AVal::Opaque(Why::Undef))
    }

    #[allow(clippy::too_many_lines)]
    fn inst(&mut self, fs: &mut FnState, block: &IrBlock, idx: usize) -> Result<(), Stop> {
        let node = &block.body[idx];
        let at = IrSite { func: fs.func, block: block.id, inst: idx, span: node.span };
        let loc = self.loc(fs, block.id, idx, node.span);
        let r0 = node.results.first().copied();
        match &node.inst {
            Inst::Const { ty, value } => {
                let v = const_aval(ty, value);
                self.set_result(fs, node, v);
            }
            Inst::NullPtr => self.set_result(fs, node, AVal::Ptr(PtrVal::Null)),
            Inst::GlobalAddr { .. } => self.set_result(fs, node, AVal::Ptr(PtrVal::Unknown)),
            Inst::Undef { .. } => self.opaque_result(fs, node, Why::Undef),
            Inst::Copy { operand, .. } => {
                let v = Self::val(fs, *operand);
                self.set_result(fs, node, v);
            }
            Inst::Borrow { ptr } | Inst::BorrowMut { ptr } => {
                let v = Self::val(fs, *ptr);
                self.set_result(fs, node, v);
            }
            Inst::EndBorrow { .. } | Inst::Fence { .. } | Inst::Dealloc { .. } => {}
            Inst::HeapAlloc { .. } => self.set_result(fs, node, AVal::Ptr(PtrVal::Unknown)),
            Inst::BinOp { op, ty, lhs, rhs } => {
                let v = self.binop(fs, *op, ty, *lhs, *rhs, &loc);
                self.set_result(fs, node, v);
            }
            Inst::UnOp { op, ty, operand } => {
                let x = Self::val(fs, *operand);
                let v = match (op, int_ty(ty), &x) {
                    (UnOp::Not, Some(t), _) if t.bits == 1 => {
                        let c = self.cond(&x);
                        AVal::Cond(Cond::Not(Box::new(c)))
                    }
                    (UnOp::Not, Some(t), AVal::Op(Operand::Lit(n))) => wrap_to(!i128::from(*n), t)
                        .map_or(AVal::Opaque(Why::Op("not".into())), |n| AVal::Op(Operand::Lit(n))),
                    (UnOp::Neg, Some(t), AVal::Op(Operand::Lit(n))) => wrap_to(-i128::from(*n), t)
                        .map_or(AVal::Opaque(Why::Op("neg".into())), |n| AVal::Op(Operand::Lit(n))),
                    _ => AVal::Opaque(Why::Op(format!("unary {op:?}"))),
                };
                self.set_result(fs, node, v);
            }
            Inst::Overflow { op, ty, lhs, rhs } => {
                self.overflow(fs, node, *op, ty, *lhs, *rhs, &loc);
            }
            Inst::ICmp { op, ty, lhs, rhs } => {
                let c = self.icmp(fs, *op, ty, *lhs, *rhs, &loc);
                if let (Some(r), Some(t)) = (r0, int_ty(ty)) {
                    fs.cmp_ty.insert(r, t);
                }
                self.set_result(fs, node, AVal::Cond(c));
            }
            Inst::FCmp { .. } => {
                self.set_result(fs, node, AVal::Opaque(Why::Op("a float compare".into())))
            }
            Inst::Cast { op, src_ty, dst_ty, operand } => {
                let v = self.cast(fs, *op, src_ty, dst_ty, *operand, &loc);
                self.set_result(fs, node, v);
            }
            Inst::Select { ty, cond, then_val, else_val } => {
                let c = self.cond(&Self::val(fs, *cond));
                let (a, b) = (Self::val(fs, *then_val), Self::val(fs, *else_val));
                let v = match c {
                    Cond::Const(true) => a,
                    Cond::Const(false) => b,
                    c => match int_ty(ty) {
                        Some(t) if t.bits == 1 => {
                            let (ca, cb) = (self.cond(&a), self.cond(&b));
                            AVal::Cond(match (ca, cb) {
                                (Cond::Const(false), Cond::Const(true)) => Cond::Not(Box::new(c)),
                                (Cond::Const(true), Cond::Const(false)) => c,
                                (ca, cb) => Cond::Or(
                                    Box::new(Cond::And(Box::new(c.clone()), Box::new(ca))),
                                    Box::new(Cond::And(
                                        Box::new(Cond::Not(Box::new(c))),
                                        Box::new(cb),
                                    )),
                                ),
                            })
                        }
                        Some(_) => {
                            let r = self.var(format!("{}:select", fs.name));
                            let (oa, ob) = (self.operand(fs, &a, &loc), self.operand(fs, &b, &loc));
                            let (t, e) = fs.branch(c, &loc, None);
                            let j = fs.new_block();
                            fs.cur = t;
                            fs.push(StmtKind::Assign { var: r, expr: Expr::Use(oa) }, &loc);
                            fs.terminate(Term::Goto(j), &loc, None);
                            fs.cur = e;
                            fs.push(StmtKind::Assign { var: r, expr: Expr::Use(ob) }, &loc);
                            fs.terminate(Term::Goto(j), &loc, None);
                            fs.cur = j;
                            AVal::Op(Operand::Var(r))
                        }
                        None => AVal::Opaque(Why::Op("a non-integer select".into())),
                    },
                };
                self.set_result(fs, node, v);
            }
            Inst::ExtractField { aggregate, field, .. } => {
                let v = match Self::val(fs, *aggregate) {
                    AVal::Agg(xs) => xs
                        .get(*field as usize)
                        .cloned()
                        .unwrap_or(AVal::Opaque(Why::Op("a missing field".into()))),
                    AVal::Opaque(w) => AVal::Opaque(w),
                    _ => AVal::Opaque(Why::Op("a field of an untracked aggregate".into())),
                };
                self.set_result(fs, node, v);
            }
            Inst::InsertField { ty, aggregate, field, value } => {
                let mut base = match Self::val(fs, *aggregate) {
                    AVal::Agg(xs) => xs,
                    AVal::Opaque(w) => match Self::skeleton(&shape_of(self.m, ty), &w) {
                        AVal::Agg(xs) => xs,
                        _ => Vec::new(),
                    },
                    _ => match Self::skeleton(&shape_of(self.m, ty), &Why::Undef) {
                        AVal::Agg(xs) => xs,
                        _ => Vec::new(),
                    },
                };
                let i = *field as usize;
                while base.len() <= i {
                    base.push(AVal::Unit);
                }
                base[i] = Self::val(fs, *value);
                self.set_result(fs, node, AVal::Agg(base));
            }
            Inst::PtrFromParts { data, metadata, .. } => {
                let v = AVal::Agg(vec![Self::val(fs, *data), Self::val(fs, *metadata)]);
                self.set_result(fs, node, v);
            }
            Inst::PtrData { ptr, .. } | Inst::PtrMetadata { ptr, .. } => {
                let field = usize::from(matches!(node.inst, Inst::PtrMetadata { .. }));
                let v = match Self::val(fs, *ptr) {
                    AVal::Agg(xs) => xs.get(field).cloned().unwrap_or(AVal::Opaque(Why::Memory)),
                    AVal::Ptr(p) if field == 0 => AVal::Ptr(p),
                    _ => AVal::Opaque(Why::Memory),
                };
                self.set_result(fs, node, v);
            }
            Inst::Alloca { ty, .. } => {
                let promote = r0.is_some_and(|r| fs.promotable.contains(&r));
                let carrier = fd_carrier_in(self.m, ty);
                if promote {
                    let shape = shape_of(self.m, ty);
                    let leaves = self.fresh_leaves(
                        &shape,
                        &format!("{}:cell%{}", fs.name, r0.map_or(0, |r| r.0)),
                    );
                    self.cells.push(Cell { shape, leaves, fd_carrier: carrier });
                    let cell = self.cells.len() - 1;
                    self.set_result(fs, node, AVal::Ptr(PtrVal::Cell { cell, path: Vec::new() }));
                } else {
                    if let Some(c) = carrier {
                        self.refuse(
                            Some(at),
                            Refusal::FdEscape {
                                what: format!("`{c}` lives in memory whose address escapes"),
                            },
                        );
                    }
                    self.set_result(fs, node, AVal::Ptr(PtrVal::Unknown));
                }
            }
            Inst::GEP { base, indices, .. } => {
                let v = match Self::val(fs, *base) {
                    AVal::Ptr(PtrVal::Cell { cell, mut path }) => {
                        let lits: Option<Vec<i64>> = indices
                            .iter()
                            .map(|i| match Self::val(fs, *i) {
                                AVal::Op(Operand::Lit(n)) => Some(n),
                                _ => None,
                            })
                            .collect();
                        match lits.as_deref() {
                            Some([0, rest @ ..]) if rest.iter().all(|x| *x >= 0) => {
                                path.extend(rest.iter().map(|x| *x as u32));
                                AVal::Ptr(PtrVal::Cell { cell, path })
                            }
                            _ => {
                                self.cell_escapes(fs, cell, &loc, "a non-constant offset into it");
                                AVal::Ptr(PtrVal::Unknown)
                            }
                        }
                    }
                    _ => AVal::Ptr(PtrVal::Unknown),
                };
                self.set_result(fs, node, v);
            }
            Inst::Load { ty, ptr, .. } => {
                let v = self.load(fs, ty, &Self::val(fs, *ptr), &loc);
                self.set_result(fs, node, v);
            }
            Inst::Store { ty, ptr, value, .. } => {
                let (p, v) = (Self::val(fs, *ptr), Self::val(fs, *value));
                self.store(fs, ty, &p, &v, &loc, at);
            }
            Inst::MemCopy { dst, .. } | Inst::MemSet { dst, .. } => {
                if let AVal::Ptr(PtrVal::Cell { cell, path }) = Self::val(fs, *dst) {
                    self.havoc_cell(fs, cell, &path, &loc);
                }
            }
            Inst::Drop { ty, .. } => {
                if !trivially_dropped(self.m, ty) {
                    let impls = crate::shape::drop_impl_types(self.m);
                    let what = crate::shape::effectful_drop(self.m, ty, &impls)
                        .unwrap_or_else(|| format!("{ty:?} (drop glue not audited)"));
                    self.refuse(Some(at), Refusal::DropUnmodeled { ty: what });
                }
            }
            Inst::AtomicLoad { .. } | Inst::AtomicRMW { .. } | Inst::CmpXchg { .. } => {
                for r in &node.results {
                    fs.values.insert(*r, AVal::Opaque(Why::Op("an atomic".into())));
                }
            }
            Inst::AtomicStore { ptr, .. } => {
                if let AVal::Ptr(PtrVal::Cell { cell, path }) = Self::val(fs, *ptr) {
                    self.havoc_cell(fs, cell, &path, &loc);
                }
            }
            // A siteless assert's failure is a panic halt whatever its kind (trust-ir v52 names
            // the panic, not whether the check fails). A SITED one (v54) calls its panic entry,
            // which this translation does not model: it falls to the refusal below.
            Inst::Assert { cond, kind: _, site: None } => {
                let c = self.cond(&Self::val(fs, *cond));
                let tag = self.overflow_tag(fs, *cond);
                self.guard(fs, c, &loc, tag, HaltKind::Panic);
            }
            Inst::Assume { cond } => {
                let c = self.cond(&Self::val(fs, *cond));
                self.guard(fs, c, &loc, None, HaltKind::Exact);
            }
            Inst::Call { callee, args } => {
                return self.call(fs, block, idx, node, *callee, args, at, &loc);
            }
            Inst::CallIndirect { .. } => {
                self.refuse(Some(at), Refusal::IndirectCall { at: loc.0.clone() });
                for r in &node.results {
                    fs.values.insert(*r, AVal::Opaque(Why::Op("an indirect call".into())));
                }
            }
            Inst::Br { target, args } => {
                self.edge_into(fs, *target, args, &loc);
                let t = self.enqueue(fs, *target);
                fs.terminate(Term::Goto(t), &loc, None);
                fs.stopped = true;
                return Err(Stop);
            }
            Inst::CondBr { cond, then_target, then_args, else_target, else_args } => {
                let c = self.cond(&Self::val(fs, *cond));
                match c {
                    Cond::Const(b) => {
                        let (t, a) =
                            if b { (then_target, then_args) } else { (else_target, else_args) };
                        self.edge_into(fs, *t, a, &loc);
                        let e = self.enqueue(fs, *t);
                        fs.terminate(Term::Goto(e), &loc, None);
                    }
                    c => {
                        let tag = fs.cmp_ty.get(cond).map(|t| format!("census:cmp:{}", t.name()));
                        let cur = fs.cur;
                        let te = self.edge_block(fs, *then_target, then_args, &loc);
                        let ee = self.edge_block(fs, *else_target, else_args, &loc);
                        fs.cur = cur;
                        fs.terminate(Term::Branch { cond: c, then: te, els: ee }, &loc, tag);
                    }
                }
                fs.stopped = true;
                return Err(Stop);
            }
            Inst::Switch { value, default, default_args, cases, .. } => {
                let v = Self::val(fs, *value);
                let o = self.operand(fs, &v, &loc);
                let mut chosen = None;
                if let Operand::Lit(n) = o {
                    chosen = Some(
                        cases
                            .iter()
                            .find(|c| const_lit(&c.value) == Some(n))
                            .map_or((default, default_args), |c| (&c.target, &c.args)),
                    );
                }
                if let Some((t, a)) = chosen {
                    self.edge_into(fs, *t, a, &loc);
                    let e = self.enqueue(fs, *t);
                    fs.terminate(Term::Goto(e), &loc, None);
                } else {
                    // The parent's fork result is the child's pid or -1,
                    // never 0 (as `icmp` folds it): a `0` arm is the child's.
                    let nonzero = matches!(o, Operand::Var(x) if self.nonzero.contains(&x));
                    for c in cases {
                        let Some(k) = const_lit(&c.value) else {
                            self.refuse(
                                Some(at),
                                Refusal::IrUnsupported {
                                    inst: "a switch case that is not an integer".into(),
                                },
                            );
                            continue;
                        };
                        if nonzero && k == 0 {
                            continue;
                        }
                        let cur = fs.cur;
                        let te = self.edge_block(fs, c.target, &c.args, &loc);
                        let next = fs.new_block();
                        fs.cur = cur;
                        fs.terminate(
                            Term::Branch {
                                cond: Cond::Cmp(CmpOp::Eq, o, Operand::Lit(k)),
                                then: te,
                                els: next,
                            },
                            &loc,
                            None,
                        );
                        fs.cur = next;
                    }
                    let cur = fs.cur;
                    let de = self.edge_block(fs, *default, default_args, &loc);
                    fs.cur = cur;
                    fs.terminate(Term::Goto(de), &loc, None);
                }
                fs.stopped = true;
                return Err(Stop);
            }
            Inst::Return { values } => {
                self.ret(fs, values, &loc, at);
                fs.stopped = true;
                return Err(Stop);
            }
            Inst::Unreachable => {
                self.halt(fs, &loc, HaltKind::Exact);
                fs.stopped = true;
                return Err(Stop);
            }
            other => {
                let name = format!("{other:?}");
                let short: String = name.chars().take_while(|c| c.is_alphanumeric()).collect();
                self.refuse(
                    Some(at),
                    Refusal::IrUnsupported { inst: format!("`{short}` at {loc}") },
                );
                for r in &node.results {
                    fs.values.insert(*r, AVal::Opaque(Why::Op(short.clone())));
                }
                if other.is_terminator() {
                    self.halt(fs, &loc, HaltKind::Exact);
                    fs.stopped = true;
                    return Err(Stop);
                }
            }
        }
        Ok(())
    }

    /// `census:ovf:<ty>` when `cond` is the producer's overflow assert
    /// (`select %flag, false, true`).
    fn overflow_tag(&self, fs: &FnState, cond: ValueId) -> Option<String> {
        let flag = fs.overflow_asserted.get(&cond)?;
        Some(
            fs.cmp_ty
                .get(flag)
                .map_or_else(|| "census:ovf:?".to_string(), |t| format!("census:ovf:{}", t.name())),
        )
    }

    fn binop(
        &mut self,
        fs: &mut FnState,
        op: BinOp,
        ty: &Ty,
        lhs: ValueId,
        rhs: ValueId,
        loc: &Loc,
    ) -> AVal {
        let (a, b) = (Self::val(fs, lhs), Self::val(fs, rhs));
        let Some(t) = int_ty(ty) else {
            return AVal::Opaque(Why::Op(format!("{op:?} on a non-integer")));
        };
        if t.bits == 1
            && matches!(
                op,
                BinOp::And | BinOp::Or | BinOp::Xor | BinOp::BAnd | BinOp::BOr | BinOp::BXor
            )
        {
            let (ca, cb) = (self.cond(&a), self.cond(&b));
            return AVal::Cond(match op {
                BinOp::And | BinOp::BAnd => Cond::And(Box::new(ca), Box::new(cb)),
                BinOp::Or | BinOp::BOr => Cond::Or(Box::new(ca), Box::new(cb)),
                _ => match (ca, cb) {
                    (x, Cond::Const(true)) | (Cond::Const(true), x) => Cond::Not(Box::new(x)),
                    (x, Cond::Const(false)) | (Cond::Const(false), x) => x,
                    (x, y) => Cond::Or(
                        Box::new(Cond::And(
                            Box::new(x.clone()),
                            Box::new(Cond::Not(Box::new(y.clone()))),
                        )),
                        Box::new(Cond::And(Box::new(Cond::Not(Box::new(x))), Box::new(y))),
                    ),
                },
            });
        }
        if let (AVal::Op(Operand::Lit(x)), AVal::Op(Operand::Lit(y))) = (&a, &b) {
            return fold_bin(op, t, *x, *y)
                .map_or(AVal::Opaque(Why::Op(format!("{op:?} of constants"))), |n| {
                    AVal::Op(Operand::Lit(n))
                });
        }
        match op {
            BinOp::Add | BinOp::Sub => {
                if t.bits >= 64 {
                    return AVal::Opaque(Why::Op(format!("a 64-bit {op:?}")));
                }
                let (oa, ob) = (self.operand(fs, &a, loc), self.operand(fs, &b, loc));
                let ob = match (op, ob) {
                    (BinOp::Add, o) => o,
                    (_, Operand::Lit(n)) => Operand::Lit(-n),
                    _ => return AVal::Opaque(Why::Op("a subtraction of a variable".into())),
                };
                let r = self.var(format!("{}:{op:?}", fs.name));
                fs.push(StmtKind::Assign { var: r, expr: Expr::Add(oa, ob) }, loc);
                // P-NO-WRAP: a wrapping add that would wrap cuts the path.
                let ok = Cond::And(
                    Box::new(Cond::Cmp(CmpOp::Le, Operand::Var(r), Operand::Lit(t.max()))),
                    Box::new(Cond::Cmp(CmpOp::Ge, Operand::Var(r), Operand::Lit(t.min()))),
                );
                self.guard(fs, ok, loc, Some(format!("census:wrap:{}", t.name())), HaltKind::Wrap);
                AVal::Op(Operand::Var(r))
            }
            _ => AVal::Opaque(Why::Op(format!("{op:?} of a tracked value"))),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn overflow(
        &mut self,
        fs: &mut FnState,
        node: &InstrNode,
        op: OverflowOp,
        ty: &Ty,
        lhs: ValueId,
        rhs: ValueId,
        loc: &Loc,
    ) {
        let (a, b) = (Self::val(fs, lhs), Self::val(fs, rhs));
        let (vr, fr) = (node.results.first().copied(), node.results.get(1).copied());
        let t = int_ty(ty);
        let put = |fs: &mut FnState, v: AVal, f: AVal| {
            if let Some(r) = vr {
                fs.values.insert(r, v);
            }
            if let Some(r) = fr {
                fs.values.insert(r, f);
            }
        };
        let Some(t) = t.filter(|t| t.bits < 64) else {
            put(fs, AVal::Opaque(Why::Op("a 64-bit overflow op".into())), AVal::Cond(Cond::Nondet));
            return;
        };
        if let (AVal::Op(Operand::Lit(x)), AVal::Op(Operand::Lit(y))) = (&a, &b) {
            let r = match op {
                OverflowOp::AddOverflow => i128::from(*x) + i128::from(*y),
                OverflowOp::SubOverflow => i128::from(*x) - i128::from(*y),
                OverflowOp::MulOverflow => i128::from(*x) * i128::from(*y),
            };
            let inr = i64::try_from(r).ok().is_some_and(|v| t.contains(v));
            let v = wrap_to(r, t)
                .map_or(AVal::Opaque(Why::Op("overflow".into())), |n| AVal::Op(Operand::Lit(n)));
            put(fs, v, AVal::Cond(Cond::Const(!inr)));
            return;
        }
        let (oa, ob) = (self.operand(fs, &a, loc), self.operand(fs, &b, loc));
        let ob = match (op, ob) {
            (OverflowOp::AddOverflow, o) => o,
            (OverflowOp::SubOverflow, Operand::Lit(n)) => Operand::Lit(-n),
            _ => {
                put(
                    fs,
                    AVal::Opaque(Why::Op(format!("{op:?} of variables"))),
                    AVal::Cond(Cond::Nondet),
                );
                return;
            }
        };
        let r = self.var(format!("{}:{op:?}", fs.name));
        fs.push(StmtKind::Assign { var: r, expr: Expr::Add(oa, ob) }, loc);
        let flag = Cond::Or(
            Box::new(Cond::Cmp(CmpOp::Gt, Operand::Var(r), Operand::Lit(t.max()))),
            Box::new(Cond::Cmp(CmpOp::Lt, Operand::Var(r), Operand::Lit(t.min()))),
        );
        if let Some(f) = fr {
            fs.cmp_ty.insert(f, t);
        }
        // Exact while the producer asserts the flag before the value is used
        // (checked arithmetic); otherwise the value would wrap: cut the path.
        if !fr.is_some_and(|f| fs.overflow_asserted.contains_key(&f)) {
            let ok = Cond::Not(Box::new(flag.clone()));
            self.guard(fs, ok, loc, Some(format!("census:wrap:{}", t.name())), HaltKind::Wrap);
        }
        put(fs, AVal::Op(Operand::Var(r)), AVal::Cond(flag));
    }

    /// The value of `v` (type `from`) seen as `signed` (same width).
    fn view(
        &mut self,
        fs: &mut FnState,
        v: Operand,
        from: IntTy,
        signed: bool,
        loc: &Loc,
    ) -> Option<Operand> {
        if from.signed == signed || from.bits == 1 {
            return Some(v);
        }
        if from.bits >= 64 {
            return None;
        }
        let m = 1i64 << from.bits;
        if let Operand::Lit(n) = v {
            let to = IntTy { bits: from.bits, signed };
            return wrap_to(i128::from(n), to).map(Operand::Lit);
        }
        let r = self.var(format!("{}:view", fs.name));
        let (c, adj) = if signed {
            (Cond::Cmp(CmpOp::Gt, v, Operand::Lit(m / 2 - 1)), -m)
        } else {
            (Cond::Cmp(CmpOp::Lt, v, Operand::Lit(0)), m)
        };
        let (t, e) = fs.branch(c, loc, None);
        let j = fs.new_block();
        fs.cur = t;
        fs.push(StmtKind::Assign { var: r, expr: Expr::Add(v, Operand::Lit(adj)) }, loc);
        fs.terminate(Term::Goto(j), loc, None);
        fs.cur = e;
        fs.push(StmtKind::Assign { var: r, expr: Expr::Use(v) }, loc);
        fs.terminate(Term::Goto(j), loc, None);
        fs.cur = j;
        Some(Operand::Var(r))
    }

    fn icmp(
        &mut self,
        fs: &mut FnState,
        op: ICmpOp,
        ty: &Ty,
        lhs: ValueId,
        rhs: ValueId,
        loc: &Loc,
    ) -> Cond {
        let (a, b) = (Self::val(fs, lhs), Self::val(fs, rhs));
        let Some(t) = int_ty(ty) else {
            // Pointer compares: only null against null/non-null is decided.
            return match (op, &a, &b) {
                (ICmpOp::Eq, AVal::Ptr(PtrVal::Null), AVal::Ptr(PtrVal::Null)) => Cond::Const(true),
                (ICmpOp::Ne, AVal::Ptr(PtrVal::Null), AVal::Ptr(PtrVal::Null)) => {
                    Cond::Const(false)
                }
                (ICmpOp::Eq, AVal::Ptr(PtrVal::Cell { .. }), AVal::Ptr(PtrVal::Null))
                | (ICmpOp::Eq, AVal::Ptr(PtrVal::Null), AVal::Ptr(PtrVal::Cell { .. })) => {
                    Cond::Const(false)
                }
                (ICmpOp::Ne, AVal::Ptr(PtrVal::Cell { .. }), AVal::Ptr(PtrVal::Null))
                | (ICmpOp::Ne, AVal::Ptr(PtrVal::Null), AVal::Ptr(PtrVal::Cell { .. })) => {
                    Cond::Const(true)
                }
                _ => Cond::Nondet,
            };
        };
        if let (AVal::Opaque(w), _) | (_, AVal::Opaque(w)) = (&a, &b) {
            self.notes.push(format!(
                "over-approximation: the guard at {loc} compares {w}, which the census does not \
                 track: both arms are explored (Cond::Nondet)"
            ));
            return Cond::Nondet;
        }
        let (cop, _, signed) = cmp_of(op);
        let (mut oa, mut ob) = (self.operand(fs, &a, loc), self.operand(fs, &b, loc));
        // The parent's fork result is the child's pid or -1, never 0.
        if matches!(cop, CmpOp::Eq | CmpOp::Ne) {
            let nz = |o: Operand| matches!(o, Operand::Var(v) if self.nonzero.contains(&v));
            if (nz(oa) && ob == Operand::Lit(0)) || (nz(ob) && oa == Operand::Lit(0)) {
                return Cond::Const(cop == CmpOp::Ne);
            }
        }
        if let Some(s) = signed {
            match (self.view(fs, oa, t, s, loc), self.view(fs, ob, t, s, loc)) {
                (Some(x), Some(y)) => {
                    oa = x;
                    ob = y;
                }
                _ => return Cond::Nondet,
            }
        }
        if let (Operand::Lit(x), Operand::Lit(y)) = (oa, ob) {
            return Cond::Const(match cop {
                CmpOp::Eq => x == y,
                CmpOp::Ne => x != y,
                CmpOp::Lt => x < y,
                CmpOp::Le => x <= y,
                CmpOp::Gt => x > y,
                CmpOp::Ge => x >= y,
            });
        }
        Cond::Cmp(cop, oa, ob)
    }

    fn cast(
        &mut self,
        fs: &mut FnState,
        op: CastOp,
        src: &Ty,
        dst: &Ty,
        x: ValueId,
        loc: &Loc,
    ) -> AVal {
        let v = Self::val(fs, x);
        match (op, int_ty(src), int_ty(dst)) {
            (CastOp::Trunc, Some(s), Some(d)) => match v {
                AVal::Op(Operand::Lit(n)) => wrap_to(i128::from(n), d)
                    .map_or(AVal::Opaque(Why::Trunc), |n| AVal::Op(Operand::Lit(n))),
                AVal::Cond(c) if d.bits == 1 => AVal::Cond(c),
                _ if s.bits <= d.bits => v,
                _ => AVal::Opaque(Why::Trunc),
            },
            (CastOp::ZExt | CastOp::SExt | CastOp::Bitcast, Some(s), Some(d)) => {
                if let AVal::Cond(c) = &v {
                    return AVal::Cond(c.clone());
                }
                if matches!(v, AVal::Opaque(_)) {
                    return v;
                }
                let want_signed = match op {
                    CastOp::ZExt => false,
                    CastOp::SExt => true,
                    _ => d.signed,
                };
                let o = self.operand(fs, &v, loc);
                let Some(viewed) = self.view(fs, o, s, want_signed, loc) else {
                    return AVal::Opaque(Why::Op("a 64-bit reinterpretation".into()));
                };
                // Widening keeps the viewed value; the target's own view of it
                // is the same number when it fits (it does, for a wider type,
                // except an unsigned view put into a same-width signed type,
                // which `Bitcast` handled above).
                if d.bits < 64 && !d.signed && want_signed {
                    // sext into an unsigned type: negative values wrap.
                    let dd = IntTy { bits: d.bits, signed: true };
                    return self
                        .view(fs, viewed, dd, false, loc)
                        .map_or(AVal::Opaque(Why::Op("a reinterpretation".into())), AVal::Op);
                }
                AVal::Op(viewed)
            }
            (CastOp::PtrToPtr | CastOp::Bitcast, None, None) => v,
            (CastOp::IntToPtr, _, _) => AVal::Ptr(PtrVal::Unknown),
            (CastOp::PtrToInt, _, _) => {
                if let AVal::Ptr(PtrVal::Cell { cell, .. }) = v {
                    self.cell_escapes(fs, cell, loc, "its address is converted to an integer");
                }
                AVal::Opaque(Why::Op("a pointer as an integer".into()))
            }
            _ => AVal::Opaque(Why::Op(format!("a {op:?} cast"))),
        }
    }

    fn load(&mut self, fs: &mut FnState, ty: &Ty, p: &AVal, loc: &Loc) -> AVal {
        let AVal::Ptr(PtrVal::Cell { cell, path }) = p else {
            return AVal::Opaque(Why::Memory);
        };
        let Some(c) = self.cells.get(*cell).cloned() else { return AVal::Opaque(Why::Memory) };
        let want = shape_of(self.m, ty);
        let Some((start, sub)) = sub_shape(&c.shape, path) else {
            return AVal::Opaque(Why::Memory);
        };
        if !shape_compatible(sub, &want) {
            return AVal::Opaque(Why::Op("a load of another type".into()));
        }
        // A leaf read as another integer type of the same width is
        // REINTERPRETED (an i32 cell holding -1 read as u32 is 4294967295:
        // the review's F9); another width is untracked.
        let (from, to) = (leaf_shapes(sub), leaf_shapes(&want));
        let n = want.leaf_count();
        let mut leaves = Vec::new();
        for (k, l) in c.leaves.iter().skip(start).take(n).enumerate() {
            match l {
                Leaf::Var(v) => {
                    let t = self.var(format!("{}:load", fs.name));
                    let o = self.convert(fs, Operand::Var(*v), from.get(k), to.get(k), loc);
                    let expr = o.map_or(Expr::Opaque, Expr::Use);
                    if expr == Expr::Opaque {
                        self.origins.insert(
                            t,
                            (loc.clone(), Why::Op("a load of another integer width".into())),
                        );
                    }
                    fs.push(StmtKind::Assign { var: t, expr }, loc);
                    leaves.push(Leaf::Var(t));
                }
                Leaf::Ptr => leaves.push(Leaf::Ptr),
            }
        }
        let mut pos = 0;
        Self::aval_from(&want, &leaves, &mut pos, &mut std::iter::empty())
    }

    /// `o`, a value of leaf shape `from`, as a value of leaf shape `to`:
    /// itself when the types agree (or either is untracked), its
    /// same-width reinterpretation when only the signedness differs, `None`
    /// (untracked) otherwise.
    fn convert(
        &mut self,
        fs: &mut FnState,
        o: Operand,
        from: Option<&Shape>,
        to: Option<&Shape>,
        loc: &Loc,
    ) -> Option<Operand> {
        match (from, to) {
            (Some(Shape::Int(a)), Some(Shape::Int(b))) if a != b => {
                if a.bits == b.bits {
                    self.view(fs, o, *a, b.signed, loc)
                } else {
                    None
                }
            }
            _ => Some(o),
        }
    }

    fn store(&mut self, fs: &mut FnState, ty: &Ty, p: &AVal, v: &AVal, loc: &Loc, at: IrSite) {
        let mut ptrs = Vec::new();
        collect_ptrs(v, &mut ptrs);
        match p {
            AVal::Ptr(PtrVal::Cell { cell, path }) => {
                let Some(c) = self.cells.get(*cell).cloned() else { return };
                let want = shape_of(self.m, ty);
                let Some((start, sub)) = sub_shape(&c.shape, path) else {
                    self.havoc_cell(fs, *cell, &[], loc);
                    return;
                };
                if !shape_compatible(sub, &want) {
                    self.havoc_cell(fs, *cell, path, loc);
                    return;
                }
                let leaves: Vec<Leaf> =
                    c.leaves.iter().skip(start).take(want.leaf_count()).copied().collect();
                // Stored as the cell's own leaf types (F9: the same
                // reinterpretation a load makes).
                let (from, to) = (leaf_shapes(&want), leaf_shapes(sub));
                let mut flat = Vec::new();
                self.flatten(fs, v, &want, loc, &mut flat);
                let mut conv = Vec::new();
                for (k, x) in flat.into_iter().enumerate() {
                    conv.push(match x {
                        Ok(o) => Ok(self
                            .convert(fs, o, from.get(k), to.get(k), loc)
                            .unwrap_or_else(|| {
                                Operand::Var(self.opaque_var(
                                    fs,
                                    Why::Op("a store of another integer width".into()),
                                    loc,
                                ))
                            })),
                        Err(p) => Err(p),
                    });
                }
                self.copy_flat(fs, &conv, &leaves, loc);
            }
            _ => {
                for q in ptrs {
                    if let PtrVal::Cell { cell, .. } = q {
                        self.cell_escapes(fs, cell, loc, "a pointer to it is stored to memory");
                    }
                }
                if let Some(c) = fd_carrier_in(self.m, ty) {
                    self.refuse(
                        Some(at),
                        Refusal::FdEscape {
                            what: format!(
                                "`{c}` stored through a pointer the census does not follow"
                            ),
                        },
                    );
                }
            }
        }
    }

    /// Parallel copies of `args` into `target`'s parameters, in the current
    /// block.
    fn edge_into(&mut self, fs: &mut FnState, target: IrBlockId, args: &[ValueId], loc: &Loc) {
        if args.is_empty() {
            return;
        }
        self.enqueue(fs, target);
        let slots = fs.bparams.get(&target).cloned().unwrap_or_default();
        if slots.len() != args.len() {
            // A branch to the entry block (whose parameters are the
            // function's), or a malformed edge: the copies have nowhere to go.
            let at = self.locs.get(loc).copied();
            self.refuse(
                at,
                Refusal::IrUnsupported {
                    inst: format!(
                        "an edge with {} arguments into bb{} of `{}`, which has {} parameter slots",
                        args.len(),
                        target.0,
                        fs.name,
                        slots.len()
                    ),
                },
            );
            return;
        }
        let mut flat = Vec::new();
        let mut dest = Vec::new();
        for (a, (sh, leaves)) in args.iter().zip(&slots) {
            let v = Self::val(fs, *a);
            self.flatten(fs, &v, sh, loc, &mut flat);
            dest.extend(leaves.iter().copied());
        }
        self.copy_flat(fs, &flat, &dest, loc);
    }

    /// A block holding the edge's copies, then a jump to `target`.
    fn edge_block(
        &mut self,
        fs: &mut FnState,
        target: IrBlockId,
        args: &[ValueId],
        loc: &Loc,
    ) -> usize {
        if args.is_empty() {
            return self.enqueue(fs, target);
        }
        let b = fs.new_block();
        fs.cur = b;
        self.edge_into(fs, target, args, loc);
        let t = self.enqueue(fs, target);
        fs.terminate(Term::Goto(t), loc, None);
        b
    }

    fn ret(&mut self, fs: &mut FnState, values: &[ValueId], loc: &Loc, at: IrSite) {
        let v = match values {
            [] => AVal::Unit,
            [x] => Self::val(fs, *x),
            xs => AVal::Agg(xs.iter().map(|x| Self::val(fs, *x)).collect()),
        };
        match fs.kind {
            FnKind::ForkChild => {
                let func = fs.name.clone();
                self.refuse(Some(at), Refusal::ForkChildReturns { func });
                fs.terminate(Term::Return(None), loc, None);
            }
            FnKind::Hook => {
                // io::Result<()>: tag 0 is Ok -> 0, else -1 (what the
                // STD-SPAWN-FORK child body tests).
                let tag = match &v {
                    AVal::Agg(xs) => xs.first().cloned().unwrap_or(AVal::Opaque(Why::Undef)),
                    other => other.clone(),
                };
                match tag {
                    AVal::Op(Operand::Lit(n)) => {
                        fs.terminate(
                            Term::Return(Some(Operand::Lit(if n == 0 { 0 } else { -1 }))),
                            loc,
                            None,
                        );
                    }
                    other => {
                        let c = match other {
                            AVal::Op(o) => Cond::Cmp(CmpOp::Eq, o, Operand::Lit(0)),
                            _ => Cond::Nondet,
                        };
                        let (t, e) = fs.branch(c, loc, None);
                        fs.cur = t;
                        fs.terminate(Term::Return(Some(Operand::Lit(0))), loc, None);
                        fs.cur = e;
                        fs.terminate(Term::Return(Some(Operand::Lit(-1))), loc, None);
                    }
                }
            }
            FnKind::Normal => {
                let (sh, leaves) = fs.ret.clone();
                self.assign_leaves(fs, &v, &sh, &leaves, loc);
                fs.terminate(Term::Return(None), loc, None);
            }
        }
    }

    // ---- calls ------------------------------------------------------------

    #[allow(clippy::too_many_arguments)]
    fn call(
        &mut self,
        fs: &mut FnState,
        block: &IrBlock,
        idx: usize,
        node: &InstrNode,
        callee: FuncId,
        args: &[ValueId],
        at: IrSite,
        loc: &Loc,
    ) -> Result<(), Stop> {
        let c = self.callees.get(callee.as_usize()).cloned().unwrap_or(Callee::Unresolved {
            name: format!("func.{}", callee.0),
            why: "no such function".into(),
        });
        match c {
            Callee::Body { .. } => self.call_body(fs, node, callee, args, at, loc),
            Callee::Foreign { link_name, .. } => {
                return self.foreign(fs, block, idx, node, callee, &link_name, args, at, loc);
            }
            Callee::Std { paths } => return self.std(fs, node, callee, &paths, args, at, loc),
            Callee::CoreAlloc { path } => {
                if is_panic(&path) {
                    self.halt(fs, loc, HaltKind::Panic);
                    fs.stopped = true;
                    return Err(Stop);
                }
                if std_is(std::slice::from_ref(&path), "core::mem::drop") {
                    return self.std(fs, node, callee, &[path], args, at, loc);
                }
                self.audited_pure(fs, node, callee, &[path], args, at, loc);
            }
            Callee::LocalRefused { path } => {
                self.refuse(Some(at), Refusal::CalleeNotLowered { path: path.clone() });
                self.opaque_result(fs, node, Why::Call(path));
            }
            Callee::Upstream { krate, path } => {
                self.refuse(Some(at), Refusal::Upstream { krate, path: path.clone() });
                self.opaque_result(fs, node, Why::Call(path));
            }
            Callee::Unresolved { name, why } => {
                self.refuse(Some(at), Refusal::Resolve { name: name.clone(), why });
                self.opaque_result(fs, node, Why::Call(name));
            }
        }
        Ok(())
    }

    fn call_body(
        &mut self,
        fs: &mut FnState,
        node: &InstrNode,
        callee: FuncId,
        args: &[ValueId],
        at: IrSite,
        loc: &Loc,
    ) {
        if let Some(pos) = self.stack.iter().position(|f| *f == callee) {
            let mut cycle: Vec<String> =
                self.stack[pos..].iter().map(|f| fn_path(self.m, *f)).collect();
            cycle.push(fn_path(self.m, callee));
            self.refuse(Some(at), Refusal::Recursion { cycle });
            self.opaque_result(fs, node, Why::Call(fn_path(self.m, callee)));
            return;
        }
        let ptys: Vec<Ty> = self.func_ty(callee).map(|t| t.params.clone()).unwrap_or_default();
        let mut flat = Vec::new();
        for (i, t) in ptys.iter().enumerate() {
            let sh = shape_of(self.m, t);
            let v = args.get(i).map_or(AVal::Opaque(Why::Undef), |a| Self::val(fs, *a));
            self.flatten(fs, &v, &sh, loc, &mut flat);
        }
        let ptrs: Vec<PtrVal> = flat.iter().filter_map(|x| x.as_ref().err().cloned()).collect();
        let key =
            SpecKey { func: callee, ctx: fs.ctx, ptrs, hook: false, child_site: fs.child_site };
        let Some(spec) = self.spec(key, Some(at)) else {
            self.opaque_result(fs, node, Why::Call(fn_path(self.m, callee)));
            return;
        };
        let dests: Vec<Leaf> = spec.params.iter().flat_map(|(_, l)| l.iter().copied()).collect();
        let mut cargs = Vec::new();
        for (x, l) in flat.iter().zip(&dests) {
            if let (Ok(o), Leaf::Var(d)) = (x, l) {
                cargs.push((*d, *o));
            }
        }
        fs.push(StmtKind::Call { body: spec.body, args: cargs, ret: None }, loc);
        if spec.may_halt {
            let c = Cond::Cmp(CmpOp::Eq, Operand::Var(self.halt_var), Operand::Lit(1));
            let (t, e) = fs.branch(c, loc, None);
            fs.cur = t;
            let term = if fs.kind == FnKind::Hook {
                Term::Return(Some(Operand::Lit(-1)))
            } else {
                Term::Return(None)
            };
            fs.terminate(term, loc, None);
            self.halt_blocks.insert((fs.body, t), HaltKind::Propagate);
            fs.may_halt = true;
            fs.cur = e;
        }
        // Copy the callee's return leaves (they are reused by its next call).
        let (sh, leaves) = spec.ret.clone();
        let mut copies = Vec::new();
        for l in &leaves {
            match l {
                Leaf::Var(v) => {
                    let t = self.var(format!("{}:ret", fs.name));
                    fs.push(StmtKind::Assign { var: t, expr: Expr::Use(Operand::Var(*v)) }, loc);
                    copies.push(Leaf::Var(t));
                }
                Leaf::Ptr => copies.push(Leaf::Ptr),
            }
        }
        let mut pos = 0;
        let v = Self::aval_from(&sh, &copies, &mut pos, &mut std::iter::empty());
        self.set_result(fs, node, v);
    }

    fn lit_arg(fs: &FnState, args: &[ValueId], i: usize) -> Option<i64> {
        match args.get(i).map(|a| Self::val(fs, *a)) {
            Some(AVal::Op(Operand::Lit(n))) => Some(n),
            Some(AVal::Cond(Cond::Const(b))) => Some(i64::from(b)),
            None => None,
            _ => None,
        }
    }

    fn fd_arg(&mut self, fs: &mut FnState, args: &[ValueId], i: usize, loc: &Loc) -> Operand {
        let v = args.get(i).map_or(AVal::Opaque(Why::Undef), |a| Self::val(fs, *a));
        self.operand(fs, &v, loc)
    }

    /// The outcomes an event explores: the nominal one and ONE
    /// representative of the environment failures its clause admits
    /// (`trust_platform::clauses::admissible_failures`: ENFILE, ENOMEM,
    /// ENOBUFS, a sandbox's EACCES, …). One stands for all: the census
    /// tracks no errno (every failure binds -1, and a read of errno is
    /// untracked), and a failure has no descriptor-table effect. `execv*`
    /// keeps ENOENT (its listed failure).
    fn oracles_of(call: &Call<Operand>) -> Vec<Oracle> {
        if matches!(call, Call::Exec) {
            return vec![Oracle::Nominal, Oracle::Fail(Errno::ENOENT)];
        }
        trust_platform::clauses::oracle_space(call).into_iter().take(2).collect()
    }

    #[allow(clippy::too_many_arguments)]
    fn event(
        &mut self,
        fs: &mut FnState,
        loc: &Loc,
        symbol: &str,
        call: Call<Operand>,
        bind: Bind,
        site: Option<usize>,
        ofd: Vec<String>,
    ) {
        let oracles = Self::oracles_of(&call);
        fs.push(
            StmtKind::Event(Event {
                symbol: symbol.to_string(),
                call,
                bind,
                oracles,
                site,
                ofd_names: ofd,
                std_origin: None,
                path: None,
                assumption: None,
            }),
            loc,
        );
    }

    #[allow(clippy::too_many_arguments, clippy::too_many_lines)]
    fn foreign(
        &mut self,
        fs: &mut FnState,
        block: &IrBlock,
        idx: usize,
        node: &InstrNode,
        callee: FuncId,
        link: &str,
        args: &[ValueId],
        at: IrSite,
        loc: &Loc,
    ) -> Result<(), Stop> {
        let l = match symbols::lookup(link) {
            Ok(l) => l,
            Err(e) => {
                self.refuse(
                    Some(at),
                    Refusal::Unmodeled { symbol: e.symbol, reason: e.reason.to_string() },
                );
                self.havoc_args(fs, callee, args, loc, &format!("`{link}`"));
                self.opaque_result(fs, node, Why::Call(link.to_string()));
                return Ok(());
            }
        };
        let c = match l.modeled {
            Modeled::Clause(c) => c,
            Modeled::SpawnBuilder(_) => {
                self.refuse(Some(at), Refusal::SpawnBuilderEscape { symbol: link.to_string() });
                self.opaque_result(fs, node, Why::Call(link.to_string()));
                return Ok(());
            }
            Modeled::Neutral => {
                fs.push(StmtKind::Neutral { symbol: link.to_string() }, loc);
                self.havoc_args(fs, callee, args, loc, &format!("`{link}`"));
                self.opaque_result(fs, node, Why::Call(link.to_string()));
                return Ok(());
            }
            Modeled::StdRow(_) | Modeled::StdCommandSpawn => {
                self.refuse(
                    Some(at),
                    Refusal::Internal { detail: format!("C name `{link}` looked up as a std row") },
                );
                self.opaque_result(fs, node, Why::Call(link.to_string()));
                return Ok(());
            }
            // A row the model gained after this census was written: named,
            // never guessed.
            #[allow(unreachable_patterns)]
            other => {
                self.refuse(
                    Some(at),
                    Refusal::Unmodeled {
                        symbol: link.to_string(),
                        reason: format!("{other:?}: a model row the census does not translate yet"),
                    },
                );
                self.havoc_args(fs, callee, args, loc, &format!("`{link}`"));
                self.opaque_result(fs, node, Why::Call(link.to_string()));
                return Ok(());
            }
        };
        let child = fs.ctx == Ctx::Child;
        let ret = |rt: &mut RootT<'_>, fs: &mut FnState| {
            let r = rt.var(format!("{}:{link}", fs.name));
            (r, Bind::ret(r))
        };
        let nonconst = |rt: &mut RootT<'_>, what: &str| {
            rt.refuse(
                Some(at),
                Refusal::NonConstArg { symbol: link.to_string(), arg: what.to_string() },
            );
        };
        let ofd = |rt: &RootT<'_>, fs: &FnState, n: usize| -> Vec<String> {
            let base = format!(
                "{}@{}",
                fs.name,
                node.span.map_or_else(|| at.to_string(), |s| rt.cx.render_span(s))
            );
            (0..n).map(|i| if i == 0 { base.clone() } else { format!("{base}#{i}") }).collect()
        };
        match c {
            ClauseId::Fork => {
                if child {
                    self.refuse(
                        Some(at),
                        Refusal::Unmodeled {
                            symbol: link.into(),
                            reason:
                                "fork in a forked child (SD-3 split points are not implemented)"
                                    .into(),
                        },
                    );
                    self.opaque_result(fs, node, Why::Call(link.into()));
                    return Ok(());
                }
                self.fork(fs, block, idx, node, at, loc);
            }
            ClauseId::Exec => {
                if !child {
                    self.refuse(
                        Some(at),
                        Refusal::Unmodeled {
                            symbol: link.into(),
                            reason: "exec of the root process (X3 STD-COMMANDEXT-EXEC)".into(),
                        },
                    );
                    self.opaque_result(fs, node, Why::Call(link.into()));
                    return Ok(());
                }
                // The exec of a forked child is its fork's: the exec's own
                // census site reads that program site's verdict.
                match (self.scan.site_at(at), fs.child_site) {
                    (Some(cs), Some(ps)) => {
                        let p = PolicySite { site: cs, program_site: ps };
                        if !self.policy_sites.contains(&p) {
                            self.policy_sites.push(p);
                        }
                    }
                    (Some(_), None) => self.refuse(
                        Some(at),
                        Refusal::Internal {
                            detail: "an exec in a child with no spawn site to answer for it".into(),
                        },
                    ),
                    (None, _) => {}
                }
                let (r, b) = ret(self, fs);
                self.event(fs, loc, link, Call::Exec, b, None, Vec::new());
                self.set_result(fs, node, AVal::Op(Operand::Var(r)));
            }
            ClauseId::Exit => {
                let Some(status) = Self::lit_arg(fs, args, 0).and_then(|n| i32::try_from(n).ok())
                else {
                    nonconst(self, "status");
                    self.halt(fs, loc, HaltKind::Exact);
                    fs.stopped = true;
                    return Err(Stop);
                };
                if child {
                    self.event(
                        fs,
                        loc,
                        link,
                        Call::Exit { status },
                        Bind::none(),
                        None,
                        Vec::new(),
                    );
                } else {
                    self.halt(fs, loc, HaltKind::Exact);
                    fs.stopped = true;
                    return Err(Stop);
                }
            }
            ClauseId::Fcntl => {
                let fd = self.fd_arg(fs, args, 0, loc);
                let Some(cmd) = Self::lit_arg(fs, args, 1).and_then(|n| i32::try_from(n).ok())
                else {
                    nonconst(self, "the command");
                    self.opaque_result(fs, node, Why::Call(link.into()));
                    return Ok(());
                };
                const EXEC: [i32; 6] = [
                    darwin::F_DUPFD,
                    darwin::F_DUPFD_CLOEXEC,
                    darwin::F_GETFD,
                    darwin::F_SETFD,
                    darwin::F_GETFL,
                    darwin::F_SETFL,
                ];
                if !EXEC.contains(&cmd) {
                    self.refuse(Some(at), Refusal::Unmodeled { symbol: link.into(), reason: format!("fcntl command {cmd} is not modeled (record locks are lock-release, C6)") });
                    self.opaque_result(fs, node, Why::Call(link.into()));
                    return Ok(());
                }
                // F_GETFD/F_GETFL take no argument; every other modeled
                // command reads one, and C leaves it undefined when the call
                // passes none (never "0": for F_SETFD that would clear
                // close-on-exec and declare a lane).
                let takes_arg = !matches!(cmd, darwin::F_GETFD | darwin::F_GETFL);
                let arg = if args.len() > 2 {
                    match Self::lit_arg(fs, args, 2) {
                        Some(n) => n,
                        None => {
                            nonconst(self, "the argument");
                            self.opaque_result(fs, node, Why::Call(link.into()));
                            return Ok(());
                        }
                    }
                } else if takes_arg {
                    nonconst(self, "the argument (none passed: undefined in C)");
                    self.opaque_result(fs, node, Why::Call(link.into()));
                    return Ok(());
                } else {
                    0
                };
                let (r, b) = ret(self, fs);
                self.event(fs, loc, link, Call::Fcntl { fd, cmd, arg }, b, None, Vec::new());
                self.set_result(fs, node, AVal::Op(Operand::Var(r)));
            }
            ClauseId::Close | ClauseId::Dup | ClauseId::Accept => {
                let fd = self.fd_arg(fs, args, 0, loc);
                let call = match c {
                    ClauseId::Close => Call::Close { fd },
                    ClauseId::Dup => Call::Dup { fd },
                    _ => Call::Accept { fd },
                };
                if c == ClauseId::Accept {
                    self.havoc_args(
                        fs,
                        callee,
                        &args[1.min(args.len())..],
                        loc,
                        &format!("`{link}`"),
                    );
                }
                let n = trust_platform_derive::lower::allocates(&call);
                let names = ofd(self, fs, n);
                let (r, b) = ret(self, fs);
                self.event(fs, loc, link, call, b, None, names);
                self.set_result(fs, node, AVal::Op(Operand::Var(r)));
            }
            ClauseId::Dup2 => {
                let from = self.fd_arg(fs, args, 0, loc);
                let to = self.fd_arg(fs, args, 1, loc);
                let (r, b) = ret(self, fs);
                self.event(fs, loc, link, Call::Dup2 { from, to }, b, None, Vec::new());
                self.set_result(fs, node, AVal::Op(Operand::Var(r)));
            }
            ClauseId::Ioctl => {
                let fd = self.fd_arg(fs, args, 0, loc);
                let Some(req) = Self::lit_arg(fs, args, 1)
                    // A request constant typed `i32` reads sign-extended.
                    .map(|n| u64::try_from(n).unwrap_or(u64::from(n as u32)))
                else {
                    nonconst(self, "the request");
                    self.opaque_result(fs, node, Why::Call(link.into()));
                    return Ok(());
                };
                if req != darwin::FIOCLEX && req != darwin::FIONCLEX {
                    nonconst(self, "the argument (only FIOCLEX/FIONCLEX take none)");
                    self.opaque_result(fs, node, Why::Call(link.into()));
                    return Ok(());
                }
                let (r, b) = ret(self, fs);
                self.event(
                    fs,
                    loc,
                    link,
                    Call::Ioctl { fd, request: req, arg: 0 },
                    b,
                    None,
                    Vec::new(),
                );
                self.set_result(fs, node, AVal::Op(Operand::Var(r)));
            }
            ClauseId::Kqueue => {
                let names = ofd(self, fs, 1);
                let (r, b) = ret(self, fs);
                self.event(fs, loc, link, Call::Kqueue, b, None, names);
                self.set_result(fs, node, AVal::Op(Operand::Var(r)));
            }
            ClauseId::Socket => {
                let lits: Option<Vec<i32>> = (0..3)
                    .map(|i| Self::lit_arg(fs, args, i).and_then(|n| i32::try_from(n).ok()))
                    .collect();
                let Some([domain, ty, protocol]) = lits.as_deref().map(|v| [v[0], v[1], v[2]])
                else {
                    nonconst(self, "domain/type/protocol");
                    self.opaque_result(fs, node, Why::Call(link.into()));
                    return Ok(());
                };
                let names = ofd(self, fs, 1);
                let (r, b) = ret(self, fs);
                self.event(fs, loc, link, Call::Socket { domain, ty, protocol }, b, None, names);
                self.set_result(fs, node, AVal::Op(Operand::Var(r)));
            }
            ClauseId::SocketOp => {
                let fd = self.fd_arg(fs, args, 0, loc);
                let op = match link {
                    "bind" => SocketOp::Bind,
                    "listen" => SocketOp::Listen,
                    "connect" => SocketOp::Connect,
                    "shutdown" => SocketOp::Shutdown,
                    "setsockopt" => SocketOp::Setsockopt,
                    "getsockopt" => SocketOp::Getsockopt,
                    "getsockname" => SocketOp::Getsockname,
                    _ => SocketOp::Getpeername,
                };
                self.havoc_args(fs, callee, &args[1.min(args.len())..], loc, &format!("`{link}`"));
                let (r, b) = ret(self, fs);
                self.event(fs, loc, link, Call::SocketOp { fd, op }, b, None, Vec::new());
                self.set_result(fs, node, AVal::Op(Operand::Var(r)));
            }
            ClauseId::Pipe | ClauseId::Socketpair => {
                let (call, arr) = if c == ClauseId::Pipe {
                    (Some(Call::Pipe), 0)
                } else {
                    let lits: Option<Vec<i32>> = (0..3)
                        .map(|i| Self::lit_arg(fs, args, i).and_then(|n| i32::try_from(n).ok()))
                        .collect();
                    (lits.map(|v| Call::Socketpair { domain: v[0], ty: v[1], protocol: v[2] }), 3)
                };
                let Some(call) = call else {
                    nonconst(self, "domain/type/protocol");
                    self.opaque_result(fs, node, Why::Call(link.into()));
                    return Ok(());
                };
                let target = args.get(arr).map(|a| Self::val(fs, *a));
                let Some(AVal::Ptr(PtrVal::Cell { cell, path })) = target else {
                    self.refuse(Some(at), Refusal::FdEscape { what: format!("`{link}` writes its descriptors through a pointer the census does not follow") });
                    self.opaque_result(fs, node, Why::Call(link.into()));
                    return Ok(());
                };
                let leaves: Vec<VarId> = self
                    .cells
                    .get(cell)
                    .and_then(|c| {
                        let (start, sub) = sub_shape(&c.shape, &path)?;
                        let ls: Vec<VarId> = c
                            .leaves
                            .iter()
                            .skip(start)
                            .take(sub.leaf_count())
                            .filter_map(|l| if let Leaf::Var(v) = l { Some(*v) } else { None })
                            .collect();
                        (ls.len() >= 2).then_some(ls)
                    })
                    .unwrap_or_default();
                if leaves.len() < 2 {
                    self.refuse(Some(at), Refusal::FdEscape { what: format!("`{link}` writes into memory the census does not lay out as two descriptors") });
                    self.opaque_result(fs, node, Why::Call(link.into()));
                    return Ok(());
                }
                let names = ofd(self, fs, 2);
                let (t0, t1) = (
                    self.var(format!("{}:{link}.0", fs.name)),
                    self.var(format!("{}:{link}.1", fs.name)),
                );
                let r = self.var(format!("{}:{link}", fs.name));
                self.event(fs, loc, link, call, Bind::pair(t0, t1), None, names);
                let (ok, err) =
                    fs.branch(Cond::Cmp(CmpOp::Eq, Operand::Var(t0), Operand::Lit(-1)), loc, None);
                let j = fs.new_block();
                fs.cur = ok;
                fs.push(StmtKind::Assign { var: r, expr: Expr::Use(Operand::Lit(-1)) }, loc);
                fs.terminate(Term::Goto(j), loc, None);
                fs.cur = err;
                fs.push(
                    StmtKind::Assign { var: leaves[0], expr: Expr::Use(Operand::Var(t0)) },
                    loc,
                );
                fs.push(
                    StmtKind::Assign { var: leaves[1], expr: Expr::Use(Operand::Var(t1)) },
                    loc,
                );
                fs.push(StmtKind::Assign { var: r, expr: Expr::Use(Operand::Lit(0)) }, loc);
                fs.terminate(Term::Goto(j), loc, None);
                fs.cur = j;
                self.set_result(fs, node, AVal::Op(Operand::Var(r)));
            }
            ClauseId::Open => {
                nonconst(self, "the path (C-string literals are producer increment B4)");
                self.opaque_result(fs, node, Why::Call(link.into()));
            }
            ClauseId::Getrlimit | ClauseId::Setrlimit => {
                nonconst(self, "the rlimit out-parameter (C3)");
                self.opaque_result(fs, node, Why::Call(link.into()));
            }
            ClauseId::Spawn => {
                self.refuse(Some(at), Refusal::SpawnBuilderEscape { symbol: link.into() });
                self.opaque_result(fs, node, Why::Call(link.into()));
            }
            ClauseId::Waitpid => {
                if child {
                    self.refuse(
                        Some(at),
                        Refusal::Unmodeled {
                            symbol: link.into(),
                            reason: "waitpid in a forked child (SD-3 split points)".into(),
                        },
                    );
                    self.opaque_result(fs, node, Why::Call(link.into()));
                    return Ok(());
                }
                let pid = self.fd_arg(fs, args, 0, loc);
                let Some(options) = Self::lit_arg(fs, args, 2).and_then(|n| i32::try_from(n).ok())
                else {
                    nonconst(self, "the options");
                    self.opaque_result(fs, node, Why::Call(link.into()));
                    return Ok(());
                };
                self.havoc_args(
                    fs,
                    callee,
                    &args[1.min(args.len())..2.min(args.len())],
                    loc,
                    &format!("`{link}`"),
                );
                let (r, b) = ret(self, fs);
                self.event(fs, loc, link, Call::Waitpid { pid, options }, b, None, Vec::new());
                self.set_result(fs, node, AVal::Op(Operand::Var(r)));
            }
            ClauseId::ThreadCreate => {
                self.refuse(
                    Some(at),
                    Refusal::ThreadUnresolved {
                        why: "pthread_create: dynamic thread roots need M2's SpawnThread".into(),
                    },
                );
                self.opaque_result(fs, node, Why::Call(link.into()));
            }
            #[allow(unreachable_patterns)]
            other => {
                self.refuse(
                    Some(at),
                    Refusal::Unmodeled {
                        symbol: link.into(),
                        reason: format!("clause {other:?}: not translated by the census yet"),
                    },
                );
                self.havoc_args(fs, callee, args, loc, &format!("`{link}`"));
                self.opaque_result(fs, node, Why::Call(link.into()));
            }
        }
        Ok(())
    }

    /// A raw `fork` in the root process: the parent continues with the pid;
    /// the child runs a cloned continuation with the result 0.
    fn fork(
        &mut self,
        fs: &mut FnState,
        block: &IrBlock,
        idx: usize,
        node: &InstrNode,
        at: IrSite,
        loc: &Loc,
    ) {
        let span = node.span.map_or_else(|| at.to_string(), |s| self.cx.render_span(s));
        let program_site = self.sites.len();
        self.sites.push(SpawnSite {
            name: format!("{}@{span}", fs.name),
            loc: loc.clone(),
            policy: Some(FdInherit { lanes: Vec::new() }),
        });
        self.premise(P_NO_LANES, "the site's fd-inherit policy has no lanes (C0): leaks are reported, a missing lane is not", loc);
        self.premise(P_FORK_SUCCEEDS, "a raw fork succeeds: its failure (-1, no child; EAGAIN/ENOMEM) is not explored, so the parent's failure path is not checked", loc);
        if let Some(cs) = self.scan.site_at(at) {
            self.policy_sites.push(PolicySite { site: cs, program_site });
        }
        let Some(r) = node.results.first().copied() else {
            self.refuse(Some(at), Refusal::Internal { detail: "fork without a result".into() });
            return;
        };
        let pid = self.var(format!("{}:%{}", fs.name, r.0));
        self.nonzero.insert(pid);
        // The child: the rest of this block, then whatever it reaches.
        let mut values = fs.values.clone();
        values.insert(r, AVal::Op(Operand::Lit(0)));
        let child_body = self.bodies.len();
        self.bodies.push(None);
        self.body_ctx.push(Ctx::Child);
        let name = format!("{} [child of the fork at {span}]", fs.name);
        let mut cs = self.fn_state(
            fs.func,
            Ctx::Child,
            FnKind::ForkChild,
            child_body,
            name,
            values,
            (Shape::Unit, Vec::new()),
        );
        cs.child_site = Some(program_site);
        cs.work.push_back((block.id, idx + 1, 0));
        self.run_fn(&mut cs);
        self.finish_body(cs, Vec::new());
        fs.push(
            StmtKind::Fork {
                child: child_body,
                site: program_site,
                bind: Some(pid),
                std_origin: None,
            },
            loc,
        );
        fs.values.insert(r, AVal::Op(Operand::Var(pid)));
    }

    #[allow(clippy::too_many_lines, clippy::too_many_arguments)]
    fn std(
        &mut self,
        fs: &mut FnState,
        node: &InstrNode,
        callee: FuncId,
        paths: &[String],
        args: &[ValueId],
        at: IrSite,
        loc: &Loc,
    ) -> Result<(), Stop> {
        let first = paths.first().cloned().unwrap_or_default();
        let cmd = std_under(paths, "std::process::Command::")
            .or_else(|| std_under(paths, "std::os::unix::process::CommandExt::"));
        if let Some(p) = cmd {
            let method = p.rsplit("::").next().unwrap_or("").to_string();
            match method.as_str() {
                "spawn" | "output" | "status" | "exec" => {
                    self.refuse(Some(at), Refusal::CommandUnknown { method: p });
                    self.opaque_result(fs, node, Why::Call(first));
                }
                "pre_exec" | "before_exec" => self.pre_exec(fs, node, callee, args, at, loc),
                m if COMMAND_CONFIG.contains(&m) => {
                    self.havoc_args(fs, callee, &args[1.min(args.len())..], loc, &format!("`{p}`"));
                    let v = match self.ret_ty(callee) {
                        Some(Ty::Ptr | Ty::Ref(_) | Ty::RefMut(_)) => {
                            args.first().map_or(AVal::Ptr(PtrVal::Unknown), |a| Self::val(fs, *a))
                        }
                        _ => AVal::Opaque(Why::Call(p)),
                    };
                    self.set_result(fs, node, v);
                }
                _ => {
                    self.refuse(Some(at), Refusal::CommandShape { method: p.clone() });
                    self.opaque_result(fs, node, Why::Call(p));
                }
            }
            return Ok(());
        }
        if std_under(paths, "std::process::Stdio::").is_some() {
            self.havoc_args(fs, callee, args, loc, &format!("`{first}`"));
            self.opaque_result(fs, node, Why::Call(first));
            return Ok(());
        }
        if std_is(paths, "std::mem::drop") || std_is(paths, "core::mem::drop") {
            // `mem::drop(x)` runs x's drop glue: exact (nothing) only for a
            // type whose glue is certainly empty; an fd carrier's is a close
            // (a row after X3/inc 4b), a user guard's runs its Drop impl, and
            // any other struct's is not audited (the review's F2).
            let ty = self.func_ty(callee).and_then(|t| t.params.first().cloned());
            match ty {
                Some(t) if trivially_dropped(self.m, &t) => {}
                Some(t) => {
                    let impls = crate::shape::drop_impl_types(self.m);
                    let what =
                        crate::shape::effectful_drop(self.m, &t, &impls).unwrap_or_else(|| {
                            format!("{} (drop glue not audited)", ty_name(self.m, &t))
                        });
                    self.refuse(Some(at), Refusal::DropUnmodeled { ty: what });
                }
                None => self.refuse(
                    Some(at),
                    Refusal::DropUnmodeled { ty: "(a drop of an unknown type)".into() },
                ),
            }
            return Ok(());
        }
        if paths.iter().any(|p| is_panic(p)) {
            self.halt(fs, loc, HaltKind::Panic);
            fs.stopped = true;
            return Err(Stop);
        }
        // Thread roots BEFORE the symbol table: X3a's STD-THREAD-SPAWN row
        // would otherwise translate the spawn as a bare event whose closure
        // never runs (the review's F10).
        if THREAD_SPAWNS.iter().any(|t| std_is(paths, t)) {
            self.refuse(
                Some(at),
                Refusal::ThreadUnresolved {
                    why: format!("`{first}`: dynamic thread roots need M2's SpawnThread"),
                },
            );
            self.havoc_args(fs, callee, args, loc, &format!("`{first}`"));
            self.opaque_result(fs, node, Why::Call(first));
            return Ok(());
        }
        for p in paths {
            let Ok(l) = symbols::lookup(p) else { continue };
            let norm = l.normalized.clone();
            match l.modeled {
                Modeled::Neutral => {
                    return {
                        self.neutral_fd(fs, node, callee, &norm, args, at, loc);
                        Ok(())
                    };
                }
                Modeled::StdRow(id) => {
                    self.std_row(fs, node, callee, &norm, id, args, at, loc);
                    return Ok(());
                }
                Modeled::StdCommandSpawn => {
                    self.refuse(Some(at), Refusal::CommandUnknown { method: norm });
                    self.opaque_result(fs, node, Why::Call(first));
                    return Ok(());
                }
                Modeled::Clause(_) | Modeled::SpawnBuilder(_) => {}
                #[allow(unreachable_patterns)]
                other => {
                    self.refuse(
                        Some(at),
                        Refusal::UnknownStd {
                            path: format!(
                                "{norm} ({other:?}: a std row the census does not translate yet)"
                            ),
                        },
                    );
                    self.havoc_args(fs, callee, args, loc, &format!("`{first}`"));
                    self.opaque_result(fs, node, Why::Call(first));
                    return Ok(());
                }
            }
        }
        self.audited_pure(fs, node, callee, paths, args, at, loc);
        Ok(())
    }

    /// A std/core/alloc call outside the std table: translated only if it is
    /// on the census's audited effect-free lists ([`crate::audit`]) — and,
    /// for an entry that dispatches through its generic arguments' trait
    /// impls, only with integer arguments; else `PC-UNKNOWN-STD`. A
    /// combinator that takes a closure is never on the lists: what it calls
    /// is never silently skipped (the review's F3).
    #[allow(clippy::too_many_arguments)]
    fn audited_pure(
        &mut self,
        fs: &mut FnState,
        node: &InstrNode,
        callee: FuncId,
        paths: &[String],
        args: &[ValueId],
        at: IrSite,
        loc: &Loc,
    ) {
        let first = paths.first().cloned().unwrap_or_default();
        match crate::audit::lookup(paths) {
            Some(e) if !e.dispatch || self.integers_only(fs, callee, args) => {
                self.havoc_args(fs, callee, args, loc, &format!("`{first}`"));
                let sh = self.ret_shape(callee);
                self.set_result(fs, node, Self::skeleton(&sh, &Why::Call(first)));
            }
            Some(e) => {
                self.refuse(
                    Some(at),
                    Refusal::UnknownStd {
                        path: format!(
                            "{first} ({}: with arguments the census cannot see are integers, a \
                             user impl may run anything)",
                            e.why
                        ),
                    },
                );
                self.havoc_args(fs, callee, args, loc, &format!("`{first}`"));
                self.opaque_result(fs, node, Why::Call(first));
            }
            None => {
                self.refuse(Some(at), Refusal::UnknownStd { path: first.clone() });
                self.havoc_args(fs, callee, args, loc, &format!("`{first}`"));
                self.opaque_result(fs, node, Why::Call(first));
            }
        }
    }

    /// Whether every argument is an integer: by value, or a pointer into a
    /// promoted cell whose pointee holds integer leaves only.
    fn integers_only(&self, fs: &FnState, callee: FuncId, args: &[ValueId]) -> bool {
        let ptys: Vec<Ty> = self.func_ty(callee).map(|t| t.params.clone()).unwrap_or_default();
        args.iter().enumerate().all(|(i, a)| {
            if ptys.get(i).is_some_and(|t| int_ty(t).is_some()) {
                return true;
            }
            match Self::val(fs, *a) {
                AVal::Ptr(PtrVal::Cell { cell, path }) => self.cells.get(cell).is_some_and(|c| {
                    sub_shape(&c.shape, &path).is_some_and(|(_, sh)| ints_only(sh))
                }),
                _ => false,
            }
        })
    }

    /// The descriptor leaf of a carrier value (or of the carrier a pointer
    /// points at).
    fn carrier_fd(&mut self, fs: &mut FnState, v: &AVal, loc: &Loc) -> AVal {
        match v {
            AVal::Ptr(PtrVal::Cell { cell, path }) => {
                let Some(c) = self.cells.get(*cell).cloned() else {
                    return AVal::Opaque(Why::Memory);
                };
                let Some((start, sub)) = sub_shape(&c.shape, path) else {
                    return AVal::Opaque(Why::Memory);
                };
                let ints: Vec<VarId> = c
                    .leaves
                    .iter()
                    .skip(start)
                    .take(sub.leaf_count())
                    .filter_map(|l| if let Leaf::Var(v) = l { Some(*v) } else { None })
                    .collect();
                match ints.as_slice() {
                    [one] => {
                        let t = self.var(format!("{}:fd", fs.name));
                        fs.push(
                            StmtKind::Assign { var: t, expr: Expr::Use(Operand::Var(*one)) },
                            loc,
                        );
                        AVal::Op(Operand::Var(t))
                    }
                    _ => AVal::Opaque(Why::Op("a carrier the census does not lay out".into())),
                }
            }
            AVal::Agg(_) | AVal::Op(_) => {
                let mut leaves = Vec::new();
                single_scalar(v, &mut leaves);
                match leaves.as_slice() {
                    [one] => (*one).clone(),
                    _ => AVal::Opaque(Why::Op("a carrier the census does not lay out".into())),
                }
            }
            AVal::Opaque(w) => AVal::Opaque(w.clone()),
            _ => AVal::Opaque(Why::Memory),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn neutral_fd(
        &mut self,
        fs: &mut FnState,
        node: &InstrNode,
        callee: FuncId,
        path: &str,
        args: &[ValueId],
        at: IrSite,
        loc: &Loc,
    ) {
        let a0 = args.first().map_or(AVal::Opaque(Why::Undef), |a| Self::val(fs, *a));
        let v = if path.ends_with("AsRawFd::as_raw_fd") || path.ends_with("IntoRawFd::into_raw_fd")
        {
            self.carrier_fd(fs, &a0, loc)
        } else if path.ends_with("FromRawFd::from_raw_fd") {
            let sh = self.ret_shape(callee);
            let o = self.operand(fs, &a0, loc);
            fill_single(&sh, AVal::Op(o))
        } else {
            self.refuse(
                Some(at),
                Refusal::Internal {
                    detail: format!("neutral std row `{path}` with no value rule"),
                },
            );
            AVal::Opaque(Why::Call(path.to_string()))
        };
        fs.push(StmtKind::Neutral { symbol: path.to_string() }, loc);
        self.set_result(fs, node, v);
    }

    #[allow(clippy::too_many_arguments)]
    fn std_row(
        &mut self,
        fs: &mut FnState,
        node: &InstrNode,
        callee: FuncId,
        path: &str,
        id: &'static str,
        args: &[ValueId],
        at: IrSite,
        loc: &Loc,
    ) {
        let unbound = |rt: &mut RootT<'_>, fs: &mut FnState, why: &str| {
            rt.refuse(Some(at), Refusal::UnknownStd { path: format!("{path} ({why})") });
            rt.opaque_result(fs, node, Why::Call(path.to_string()));
        };
        if id == "STD-THREAD-SPAWN" {
            self.refuse(
                Some(at),
                Refusal::ThreadUnresolved {
                    why: format!("`{path}`: dynamic thread roots need M2's SpawnThread"),
                },
            );
            self.havoc_args(fs, callee, args, loc, &format!("`{path}`"));
            self.opaque_result(fs, node, Why::Call(path.to_string()));
            return;
        }
        if id == "STD-OPEN" || id == "STD-UNIX-BIND" || id == "STD-UNIX-CONNECT" {
            unbound(self, fs, "a row parametric in a path the census does not read (B4/C4)");
            return;
        }
        if !GENERIC_ROWS.contains(&id) {
            unbound(self, fs, &format!("{id}: a row the census does not translate"));
            return;
        }
        let Some(row) = std_summaries::row(id) else {
            unbound(self, fs, "no row");
            return;
        };
        if row.program.iter().any(trust_platform::script::ProgramStep::branches) {
            unbound(self, fs, &format!("{id}: a row with a guarded step"));
            return;
        }
        let uses_arg = row.program.iter().any(|s| {
            let mut any = false;
            let _ = s.call.map(|o| any |= matches!(o, trust_platform::script::Operand::Arg(_)));
            any
        });
        let mut rargs = Vec::new();
        if uses_arg {
            let a0 = args.first().map_or(AVal::Opaque(Why::Undef), |a| Self::val(fs, *a));
            let fd = self.carrier_fd(fs, &a0, loc);
            rargs.push(self.operand(fs, &fd, loc));
        }
        let n = row.returns.len();
        // The result: io::Result<T> (tag, payload) or T, whose integer
        // leaves are exactly the row's returns.
        let Some(ret_ty) = self.ret_ty(callee).cloned() else {
            unbound(self, fs, "no result type");
            return;
        };
        let (enum_payload, payload_ty) = match &ret_ty {
            Ty::Enum(eid) => {
                let e = self.m.enums.iter().find(|e| e.id == *eid);
                match e.and_then(|e| e.variants.first()).and_then(|v| v.fields.first()) {
                    Some(t) => (true, t.clone()),
                    None => {
                        unbound(self, fs, "an enum result without an Ok payload");
                        return;
                    }
                }
            }
            t => (false, t.clone()),
        };
        let psh = shape_of(self.m, &payload_ty);
        let mut int_leaves = 0usize;
        count_ints(&psh, &mut int_leaves);
        if int_leaves != n {
            unbound(self, fs, "the result does not hold exactly the row's descriptors");
            return;
        }
        let rets: Vec<VarId> = (0..n).map(|i| self.var(format!("{}:{id}.{i}", fs.name))).collect();
        let span = node.span.map_or_else(|| at.to_string(), |s| self.cx.render_span(s));
        let names: Vec<String> = (0..n)
            .map(|i| {
                if i == 0 {
                    format!("{}@{span}", fs.name)
                } else {
                    format!("{}@{span}#{i}", fs.name)
                }
            })
            .collect();
        fs.push(
            StmtKind::Std(StdCall::Row {
                path: path.to_string(),
                args: rargs,
                bind: rets.clone(),
                ofd_names: names,
            }),
            loc,
        );
        self.premise(P_STD_ROW_NOMINAL, "a std row's steps take their nominal outcome (the derivation lowers rows nominal-only): the row's error path (ENFILE, ENOMEM, EMFILE) is not explored", loc);
        let mut it = rets.iter();
        let payload = fill_ints(&psh, &mut it);
        let v = if enum_payload {
            let tag = self.cond_var(
                fs,
                Cond::Cmp(CmpOp::Eq, Operand::Var(rets[0]), Operand::Lit(-1)),
                loc,
            );
            AVal::Agg(vec![AVal::Op(Operand::Var(tag)), payload])
        } else {
            payload
        };
        self.set_result(fs, node, v);
    }

    /// `CommandExt::pre_exec(closure)`: the closure runs in the child of a
    /// harness spawn made right after the registration (P-HOOK-HARNESS).
    fn pre_exec(
        &mut self,
        fs: &mut FnState,
        node: &InstrNode,
        callee: FuncId,
        args: &[ValueId],
        at: IrSite,
        loc: &Loc,
    ) {
        let cmd = args.first().map_or(AVal::Ptr(PtrVal::Unknown), |a| Self::val(fs, *a));
        self.set_result(fs, node, cmd);
        if fs.ctx == Ctx::Child {
            self.refuse(
                Some(at),
                Refusal::PreExecUnresolved {
                    why: "pre_exec registered inside a forked child".into(),
                },
            );
            return;
        }
        let bound = self
            .scan
            .hooks
            .get(&(at.func, at.block, at.inst))
            .cloned()
            .unwrap_or_else(|| self.cx.closure_body_of(callee, at.span));
        let closure = match bound {
            Ok(c) => c,
            Err(why) => {
                self.refuse(Some(at), Refusal::PreExecUnresolved { why });
                return;
            }
        };
        if !matches!(self.callees.get(closure.as_usize()), Some(Callee::Body { .. })) {
            let path = fn_path(self.m, closure);
            self.refuse(
                Some(at),
                Refusal::PreExecUnresolved {
                    why: format!("the closure `{path}` has no spliced body"),
                },
            );
            return;
        }
        // The closure environment, captured at registration.
        let env_ty = self.func_ty(callee).and_then(|t| t.params.get(1).cloned());
        let env_shape = env_ty.as_ref().map_or(Shape::Unit, |t| shape_of(self.m, t));
        let leaves = self.fresh_leaves(&env_shape, &format!("{}:pre_exec env", fs.name));
        let env = args.get(1).map_or(AVal::Opaque(Why::Undef), |a| Self::val(fs, *a));
        self.assign_leaves(fs, &env, &env_shape, &leaves, loc);
        let carrier = env_ty.as_ref().and_then(|t| fd_carrier_in(self.m, t));
        self.cells.push(Cell { shape: env_shape, leaves, fd_carrier: carrier });
        let cell = self.cells.len() - 1;
        let span = node.span.map_or_else(|| at.to_string(), |s| self.cx.render_span(s));
        let program_site = self.sites.len();
        self.sites.push(SpawnSite {
            name: format!("pre_exec harness {}@{span}", fs.name),
            loc: loc.clone(),
            policy: Some(FdInherit { lanes: Vec::new() }),
        });
        let key = SpecKey {
            func: closure,
            ctx: Ctx::Child,
            ptrs: vec![PtrVal::Cell { cell, path: Vec::new() }],
            hook: true,
            child_site: Some(program_site),
        };
        let Some(spec) = self.spec(key, Some(at)) else { return };
        if let Some(cs) = self.scan.site_at(at) {
            self.policy_sites.push(PolicySite { site: cs, program_site });
        }
        self.premise(P_HOOK_HARNESS, "a pre_exec closure is checked in the child of a synthetic current Trust SP1 harness spawn made right after its registration (default descriptor strip, inherited stdio, no other hook): the real command and its earlier configuration are not recovered until C4", loc);
        self.premise(P_NO_LANES, "the site's fd-inherit policy has no lanes (C0): leaks are reported, a missing lane is not", loc);
        fs.push(
            StmtKind::Std(StdCall::CommandSpawn {
                stdio: [StdioPlan::Inherit; 3],
                // P_HOOK_HARNESS remains a synthetic-shape premise, not
                // general Command object recovery. Use current Trust's
                // placement, status relocation and pre-hook strip together.
                shape: CommandShape::with_pre_exec(),
                pre_exec: vec![spec.body],
                site: program_site,
                bind: None,
            }),
            loc,
        );
    }
}

/// std's thread-spawning functions (refused before the symbol table).
const THREAD_SPAWNS: &[&str] = &[
    "std::thread::spawn",
    "std::thread::Builder::spawn",
    "std::thread::Builder::spawn_unchecked",
    "std::thread::Builder::spawn_scoped",
    "std::thread::Scope::spawn",
    "std::thread::scope",
];

/// The std rows the census translates generically ([`RootT::std_row`]):
/// descriptor-returning rows whose only argument is a carrier's descriptor.
const GENERIC_ROWS: &[&str] =
    &["STD-PIPE", "STD-PAIR", "STD-PAIR-DGRAM", "STD-ACCEPT", "STD-TRY-CLONE"];

/// The leaf shapes of `s`, in leaf order (one per Int / Ptr / Blob).
fn leaf_shapes(s: &Shape) -> Vec<Shape> {
    let mut out = Vec::new();
    fn go(s: &Shape, out: &mut Vec<Shape>) {
        match s {
            Shape::Int(_) | Shape::Ptr | Shape::Blob => out.push(s.clone()),
            Shape::Unit => {}
            Shape::Agg(fs) => fs.iter().for_each(|f| go(f, out)),
        }
    }
    go(s, &mut out);
    out
}

fn ints_only(s: &Shape) -> bool {
    match s {
        Shape::Int(_) | Shape::Unit => true,
        Shape::Agg(fs) => fs.iter().all(ints_only),
        Shape::Ptr | Shape::Blob => false,
    }
}

/// A readable name of a trust-ir type.
fn ty_name(m: &Module, t: &Ty) -> String {
    match t {
        Ty::Struct(id) => m
            .structs
            .iter()
            .find(|s| s.id == *id)
            .map_or_else(|| format!("{t:?}"), |s| s.name.clone()),
        Ty::Enum(id) => m
            .enums
            .iter()
            .find(|e| e.id == *id)
            .map_or_else(|| format!("{t:?}"), |e| e.name.clone()),
        other => format!("{other:?}"),
    }
}

fn collect_ptrs(v: &AVal, out: &mut Vec<PtrVal>) {
    match v {
        AVal::Ptr(p) => out.push(p.clone()),
        AVal::Agg(xs) => xs.iter().for_each(|x| collect_ptrs(x, out)),
        _ => {}
    }
}

fn single_scalar<'v>(v: &'v AVal, out: &mut Vec<&'v AVal>) {
    match v {
        AVal::Agg(xs) => xs.iter().for_each(|x| single_scalar(x, out)),
        AVal::Unit => {}
        x => out.push(x),
    }
}

fn count_ints(s: &Shape, n: &mut usize) {
    match s {
        Shape::Int(_) => *n += 1,
        Shape::Agg(fs) => fs.iter().for_each(|f| count_ints(f, n)),
        _ => {}
    }
}

fn fill_ints(s: &Shape, it: &mut std::slice::Iter<'_, VarId>) -> AVal {
    match s {
        Shape::Int(_) => it.next().map_or(AVal::Opaque(Why::Undef), |v| AVal::Op(Operand::Var(*v))),
        Shape::Blob => AVal::Opaque(Why::Undef),
        Shape::Ptr => AVal::Ptr(PtrVal::Unknown),
        Shape::Unit => AVal::Unit,
        Shape::Agg(fs) => AVal::Agg(fs.iter().map(|f| fill_ints(f, it)).collect()),
    }
}

/// `shape` with its single integer leaf set to `v`.
fn fill_single(s: &Shape, v: AVal) -> AVal {
    let mut n = 0;
    count_ints(s, &mut n);
    if n != 1 {
        return AVal::Opaque(Why::Op("a carrier the census does not lay out".into()));
    }
    fn go(s: &Shape, v: &AVal) -> AVal {
        match s {
            Shape::Int(_) => v.clone(),
            Shape::Blob => AVal::Opaque(Why::Undef),
            Shape::Ptr => AVal::Ptr(PtrVal::Unknown),
            Shape::Unit => AVal::Unit,
            Shape::Agg(fs) => AVal::Agg(fs.iter().map(|f| go(f, v)).collect()),
        }
    }
    go(s, &v)
}

fn const_lit(c: &Constant) -> Option<i64> {
    match c {
        Constant::Int(n) => i64::try_from(*n).ok(),
        Constant::U128(n) => i64::try_from(*n).ok(),
        Constant::Bool(b) => Some(i64::from(*b)),
        _ => None,
    }
}

fn const_aval(ty: &Ty, c: &Constant) -> AVal {
    match c {
        Constant::Bool(b) => AVal::Cond(Cond::Const(*b)),
        Constant::Int(_) | Constant::U128(_) => match (const_lit(c), int_ty(ty)) {
            (Some(n), Some(t)) if t.bits == 1 => AVal::Cond(Cond::Const(n != 0)),
            (Some(n), _) => AVal::Op(Operand::Lit(n)),
            _ => AVal::Opaque(Why::Op("a constant wider than 64 bits".into())),
        },
        Constant::Aggregate(xs) => AVal::Agg(xs.iter().map(|x| const_aval(&Ty::Unit, x)).collect()),
        Constant::Closure { captures, .. } => {
            AVal::Agg(captures.iter().map(|x| const_aval(&Ty::Unit, x)).collect())
        }
        Constant::FnDef(f) => AVal::Fn(*f),
        Constant::PhantomData | Constant::Uninit => AVal::Unit,
        _ => AVal::Opaque(Why::Op("a constant the census does not read".into())),
    }
}

/// Which allocas never escape (their pointer is only loaded from, stored
/// to, offset by constants, borrowed, or passed to a call), and which
/// overflow flags the producer asserts (`select %flag, false, true;
/// assert`).
fn prepass(func: &trust_ir::Function) -> (BTreeSet<ValueId>, BTreeMap<ValueId, ValueId>) {
    let mut def: BTreeMap<ValueId, &Inst> = BTreeMap::new();
    for b in &func.blocks {
        for n in &b.body {
            for r in &n.results {
                def.insert(*r, &n.inst);
            }
        }
    }
    let is_const =
        |v: &ValueId| matches!(def.get(v), Some(Inst::Const { value: Constant::Int(_), .. }));
    // Derived pointers: alloca -> {alloca, geps, borrows, copies of it}.
    let allocas: Vec<ValueId> =
        def.iter().filter(|(_, i)| matches!(i, Inst::Alloca { .. })).map(|(v, _)| *v).collect();
    let mut root_of: BTreeMap<ValueId, ValueId> = allocas.iter().map(|a| (*a, *a)).collect();
    let mut bad: BTreeSet<ValueId> = BTreeSet::new();
    let mut changed = true;
    while changed {
        changed = false;
        for b in &func.blocks {
            for n in &b.body {
                let derived = match &n.inst {
                    Inst::GEP { base, indices, .. } if indices.iter().all(is_const) => Some(*base),
                    Inst::GEP { base, .. } => {
                        if let Some(r) = root_of.get(base) {
                            bad.insert(*r);
                        }
                        None
                    }
                    Inst::Borrow { ptr } | Inst::BorrowMut { ptr } => Some(*ptr),
                    Inst::Copy { operand, .. } => Some(*operand),
                    Inst::Cast { op: CastOp::PtrToPtr, operand, .. } => Some(*operand),
                    _ => None,
                };
                if let (Some(src), Some(res)) = (derived, n.results.first())
                    && let Some(r) = root_of.get(&src).copied()
                    && !root_of.contains_key(res)
                {
                    root_of.insert(*res, r);
                    changed = true;
                }
            }
        }
    }
    for b in &func.blocks {
        for n in &b.body {
            let mut escape = |v: &ValueId| {
                if let Some(r) = root_of.get(v) {
                    bad.insert(*r);
                }
            };
            match &n.inst {
                Inst::Load { .. } | Inst::Alloca { .. } | Inst::EndBorrow { .. } => {}
                Inst::Store { value, .. } => escape(value),
                Inst::GEP { .. }
                | Inst::Borrow { .. }
                | Inst::BorrowMut { .. }
                | Inst::Copy { .. } => {}
                Inst::Cast { op: CastOp::PtrToPtr, .. } => {}
                Inst::Call { .. } | Inst::Invoke { .. } => {}
                Inst::MemCopy { src, .. } => escape(src),
                Inst::Br { args, .. } => args.iter().for_each(&mut escape),
                Inst::CondBr { then_args, else_args, .. } => {
                    then_args.iter().chain(else_args).for_each(&mut escape);
                }
                Inst::Switch { default_args, cases, .. } => {
                    default_args
                        .iter()
                        .chain(cases.iter().flat_map(|c| c.args.iter()))
                        .for_each(&mut escape);
                }
                Inst::Return { values } => values.iter().for_each(&mut escape),
                Inst::InsertField { value, .. } => escape(value),
                Inst::Select { then_val, else_val, .. } => {
                    escape(then_val);
                    escape(else_val);
                }
                Inst::Cast { operand, .. } => escape(operand),
                Inst::CallIndirect { args, .. } => args.iter().for_each(&mut escape),
                Inst::AtomicStore { value, .. } | Inst::AtomicRMW { value, .. } => escape(value),
                _ => {}
            }
        }
    }
    let promotable = allocas.into_iter().filter(|a| !bad.contains(a)).collect();
    // Asserted overflow flags.
    let mut asserted = BTreeMap::new();
    for b in &func.blocks {
        for n in &b.body {
            if let Inst::Assert { cond, site: None, .. } = &n.inst
                && let Some(Inst::Select { cond: flag, then_val, else_val, .. }) = def.get(cond)
                && matches!(
                    def.get(then_val),
                    Some(Inst::Const { value: Constant::Bool(false), .. })
                )
                && matches!(
                    def.get(else_val),
                    Some(Inst::Const { value: Constant::Bool(true), .. })
                )
                && matches!(def.get(flag), Some(Inst::Overflow { .. }))
            {
                asserted.insert(*flag, *flag);
                asserted.insert(*cond, *flag);
            }
        }
    }
    (promotable, asserted)
}

/// Translate one root. `Err` carries every refusal.
pub(crate) fn translate_root(
    m: &Module,
    cx: &dyn CensusContext,
    o: &CensusOptions,
    callees: &[Callee],
    scan: &Scan,
    root: FuncId,
    kind: RootKind,
) -> Result<RootProgram, Vec<(Option<IrSite>, Refusal)>> {
    let mut rt = RootT::new(m, cx, o, callees, scan);
    let name = fn_path(m, root);
    // The root's parameters: descriptors (RL-INIT) or untracked values.
    let ptys: Vec<Ty> = rt.func_ty(root).map(|t| t.params.clone()).unwrap_or_default();
    let fd_idx: BTreeSet<usize> = cx.fd_params(root).into_iter().collect();
    let mut ptrs = Vec::new();
    let mut opaque_params: Vec<(String, Shape, usize)> = Vec::new();
    let mut fd_cells: Vec<(usize, usize)> = Vec::new();
    for (i, t) in ptys.iter().enumerate() {
        let sh = shape_of(m, t);
        let mut n_ptr = 0;
        count_ptrs(&sh, &mut n_ptr);
        let is_fd = fd_idx.contains(&i) || fd_carrier_in(m, t).is_some();
        if is_fd && n_ptr == 1 && sh == Shape::Ptr {
            // A reference to a descriptor: a cell holding it.
            let leaves = rt.fresh_leaves(&Shape::Int(IntTy::I32), &format!("{name}:*%{i}"));
            rt.cells.push(Cell {
                shape: Shape::Int(IntTy::I32),
                leaves,
                fd_carrier: Some("a descriptor parameter".into()),
            });
            let cell = rt.cells.len() - 1;
            fd_cells.push((i, cell));
            ptrs.push(PtrVal::Cell { cell, path: Vec::new() });
        } else {
            for _ in 0..n_ptr {
                ptrs.push(PtrVal::Unknown);
            }
        }
        opaque_params.push((format!("%{i}"), sh, usize::from(is_fd)));
    }
    let key = SpecKey { func: root, ctx: Ctx::Parent, ptrs, hook: false, child_site: None };
    let entry_loc = Loc(format!("<entry of {name}>"));
    rt.stack.clear();
    let spec = rt.spec(key, None);
    let wrapper = rt.bodies.len();
    rt.bodies.push(None);
    rt.body_ctx.push(Ctx::Parent);
    let mut stmts = Vec::new();
    if let Some(spec) = &spec {
        for ((pname, _sh, is_fd), (_, leaves)) in opaque_params.iter().zip(&spec.params) {
            let ints: Vec<VarId> = leaves
                .iter()
                .filter_map(|l| if let Leaf::Var(v) = l { Some(*v) } else { None })
                .collect();
            if *is_fd == 1 && ints.len() == 1 {
                rt.fd_params.push(FdParam {
                    var: ints[0],
                    class: format!("param:{name}:{pname}"),
                    peer_class: None,
                });
                continue;
            }
            for v in ints {
                stmts.push(Stmt {
                    kind: StmtKind::Assign { var: v, expr: Expr::Opaque },
                    loc: entry_loc.clone(),
                    tag: None,
                });
                rt.origins.insert(v, (entry_loc.clone(), Why::Param(pname.clone())));
            }
        }
        for (i, cell) in &fd_cells {
            if let Some(Leaf::Var(v)) = rt.cells[*cell].leaves.first() {
                rt.fd_params.push(FdParam {
                    var: *v,
                    class: format!("param:{name}:*%{i}"),
                    peer_class: None,
                });
            }
        }
        stmts.push(Stmt {
            kind: StmtKind::Call { body: spec.body, args: Vec::new(), ret: None },
            loc: entry_loc.clone(),
            tag: None,
        });
    }
    rt.bodies[wrapper] = Some(Body {
        name: format!("{name} (library entry)"),
        params: Vec::new(),
        blocks: vec![Block {
            stmts,
            term: Term::Return(None),
            term_loc: entry_loc.clone(),
            term_tag: None,
        }],
    });
    let mut bodies: Vec<Body> = rt
        .bodies
        .iter()
        .enumerate()
        .map(|(i, b)| {
            b.clone().unwrap_or_else(|| Body {
                name: format!("<unfinished {i}>"),
                params: Vec::new(),
                blocks: vec![Block {
                    stmts: Vec::new(),
                    term: Term::Return(None),
                    term_loc: entry_loc.clone(),
                    term_tag: None,
                }],
            })
        })
        .collect();
    let mut extra_refusals = Vec::new();
    let mut notes = Vec::new();
    crate::forrange::taint(
        &mut bodies,
        &rt.vars,
        &rt.origins,
        &rt.locs,
        &mut extra_refusals,
        &mut notes,
    );
    let ctx = rt.body_ctx.clone();
    crate::forrange::recognize(&mut bodies, &ctx, &rt.halt_blocks, &mut notes);
    // Premises for the path-ending rules that survived recognition.
    for (bi, b) in bodies.iter().enumerate() {
        for k in reachable_blocks(b) {
            match rt.halt_blocks.get(&(bi, k)) {
                Some(HaltKind::Panic) => rt.premise(P_PANIC, "a panic (failed assert, panicking call) ends the path; unwinding into callers' drops is not modeled", &b.blocks[k].term_loc),
                Some(HaltKind::Wrap) => rt.premise(P_NO_WRAP, "a wrapping integer add/sub on a tracked value does not wrap on the explored paths (a path on which it would is cut)", &b.blocks[k].term_loc),
                _ => {}
            }
        }
    }
    let mut refusals = std::mem::take(&mut rt.refusals);
    for r in extra_refusals {
        if !refusals.iter().any(|(_, x)| *x == r.1) {
            refusals.push(r);
        }
    }
    let file = m.files.first().cloned().unwrap_or_default();
    let program = EventProgram {
        name: name.clone(),
        provenance: vec![Provenance {
            repo: "trust-ir".to_string(),
            commit: m.name.clone(),
            path: file,
            what: format!("census C0 of `{name}`"),
        }],
        vars: rt.vars.clone(),
        bodies,
        roots: vec![Root { name: name.clone(), body: wrapper, dormant: false }],
        sites: rt.sites.clone(),
        fd_params: rt.fd_params.clone(),
        disclosures: Vec::new(),
        // fd-inherit only: the census translates none of M2's constructs
        // (flock, named opens, thread start/join are named refusals), so it
        // states no M2 policy.
        policies: Policies::default(),
    };
    notes.extend(rt.notes.clone());
    if !refusals.is_empty() {
        return Err(refusals);
    }
    if rt.policy_sites.is_empty() {
        return Err(vec![(None, Refusal::NoRoot)]);
    }
    Ok(RootProgram {
        root,
        name,
        kind,
        program,
        locs: rt.locs.clone(),
        policy_sites: rt.policy_sites.clone(),
        premises: rt.premises.values().cloned().collect(),
        bodies: rt.path.clone(),
        notes,
    })
}

fn count_ptrs(s: &Shape, n: &mut usize) {
    match s {
        Shape::Ptr => *n += 1,
        Shape::Agg(fs) => fs.iter().for_each(|f| count_ptrs(f, n)),
        _ => {}
    }
}

/// Blocks reachable from a body's entry.
#[must_use]
pub fn reachable_blocks(b: &Body) -> Vec<usize> {
    let mut seen = vec![false; b.blocks.len()];
    let mut stack = vec![0usize];
    let mut out = Vec::new();
    while let Some(k) = stack.pop() {
        if k >= seen.len() || seen[k] {
            continue;
        }
        seen[k] = true;
        out.push(k);
        match &b.blocks[k].term {
            Term::Goto(t) => stack.push(*t),
            Term::Branch { then, els, .. } => {
                stack.push(*then);
                stack.push(*els);
            }
            Term::Return(_) => {}
        }
    }
    out.sort_unstable();
    out
}

/// The derivation's own static check (lower: symbol joins, I-FD-SPECIFIED,
/// X1's untracked-value check) on a root's program: any error is a named
/// refusal.
#[must_use]
pub fn derive_precheck(rp: &RootProgram) -> Vec<(Option<IrSite>, Refusal)> {
    match lower(&rp.program) {
        Ok(_) => Vec::new(),
        Err(e) => {
            let at = |l: &Loc| rp.locs.get(l).copied();
            vec![match e {
                LowerError::Unmodeled { effect, loc } => (
                    at(&loc),
                    Refusal::Unmodeled { symbol: effect.symbol, reason: effect.reason.to_string() },
                ),
                LowerError::Untracked { var, used_as, loc, origin } => (
                    at(&loc),
                    Refusal::UntrackedFd {
                        symbol: used_as,
                        arg: format!("`{var}` (from {origin})"),
                    },
                ),
                other => (
                    None,
                    Refusal::Internal {
                        detail: format!(
                            "the derivation's static check refused the census output: {other}"
                        ),
                    },
                ),
            }]
        }
    }
}
