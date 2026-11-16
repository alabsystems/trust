//! The E6-ONLY TREE reader — increments I3′ and I4′ of the E6 admission
//! expansion (`docs/design-notes/2026-09-28-e6-admission-expansion.md` §5
//! rule 2, §6): `bool` connective trees (I3′) and value decision trees —
//! `if`/`else`, `match` with literal arms, `matches!` (I4′).
//!
//! # What it reads
//!
//! A function returning `bool`, `uN` or `iN` whose body is an ACYCLIC
//! control-flow graph of
//!
//! * value statements `_k = <rvalue>` into non-parameter locals, where the
//!   rvalue is a copy of a parameter, a temporary or a literal; `!x`,
//!   `x & y`, `x | y`, `x ^ y` over `bool`; or a comparison `l ⊲ r`
//!   (`==`, `!=`, `<`, `<=`, `>`, `>=`) — over `bool` subterms for `==`/`!=`,
//!   and over fixed-width integer parameters, literals and arithmetic otherwise;
//! * two-way `switchInt`s on a `bool` (the SHORT-CIRCUIT control flow rustc
//!   lowers `&&` and `||` into, and every `if`), multi-target `switchInt`s on
//!   an integer PARAMETER (a `match` with literal arms and `_`, `matches!` —
//!   I4′), `goto` joins, and `Return`,
//!
//! read by SYMBOLIC EXECUTION over an environment (local → term): statements
//! update it in order, and a `switchInt` on a `bool` runs each arm to the
//! switch's immediate post-dominator and MERGES the arms there, a local they
//! disagree on becoming the decision `if d { then-value } else { else-value }`
//! (`Reader::region`). The function's value is `_0` at `Return`. The
//! decision tree is then NORMALIZED to the
//! connectives the source was written with ([`normalize_bool`]): an arm that is
//! a `bool` literal turns the decision into `&&`/`||`/`!`, so `a && b` reads
//! back as `And(a, b)` and `a || b || c` as the right-nested `Or(a, Or(b, c))`
//! (the nesting of MIR's short-circuit tree AND of Clean's parse of `||`,
//! pinned by `e6_spelling_pins.rs::or_parses_right_nested`).
//!
//! # Why evaluation order does not matter
//!
//! Every leaf is a parameter, a literal or a comparison of those, and every
//! node is a total, effect-free `bool` operation, so a short-circuit `&&`
//! changes WHETHER its right operand is evaluated, never the result: the image
//! is the non-short-circuit `Bool.and`, exactly as the frozen `BoolBinary`
//! shape's is. The reader refuses every statement or terminator outside that
//! vocabulary. TG14 adds the marker-authenticated `wrapping_*` and `checked_*`
//! primitives and the overflow pair of a `CheckedBinaryOp`. Option payloads
//! are readable only on their Some edge. Every `Assert` refuses, the overflow
//! `Assert` that guards a pair's `.0` included: an image is total, so a body
//! that panics on some input has no faithful image here, and the confined D-a
//! `self_result_only` lane is the only route that may ever read such a body
//! (`docs/DECISION_QUEUE.md` E6-TG14-PANIC-EDGE-1). Other calls, casts,
//! borrows and projected writes refuse.
//!
//! # What it deliberately does not read
//!
//! * ORDERINGS over `bool` (`<`, `<=`, `>`, `>=`): `false < true`, and an
//!   equality image for one is the false import review H1 found. Refused, in
//!   a tree exactly as alone.
//! * Integer bit operations and comparisons over a computed select remain
//!   outside the fragment. TG14 reads `wrapping_add`/`_sub`/`_mul` trees at
//!   u8..u64/i8..i64 with their exact modular images; `checked_*` operations
//!   branch on mathematical overflow rather than silently using a wrapped
//!   result.
//! * RAW `+`, `-` and `*` (`BinOp::Add`/`Sub`/`Mul`, rustc's lowering with
//!   overflow checks off): the facet validator charges it as an undischarged
//!   panic operation, and the same source panics in an overflow-checked build,
//!   so it is never read as the wrapped value (the pins in
//!   `crates/trust-certify/tests/e6_import_pins.rs`).
//! * A CONSTANT body — one whose value no parameter reaches (`true`,
//!   `if c { 1 } else { 1 }`): that is the frozen constant shape's scope.
//! * A `match` whose discriminant is computed, a `Ty::Char` (no carrier here)
//!   or an enum (`exhaustive_enum_unreachable`), and any `Unreachable` arm —
//!   an EXHAUSTIVE range `match` needs a `_` arm to be read (design note I4′).
//!   The extraction the E6 lane reads (legacy mode) lowers a `char` to its
//!   `u32` scalar value and `usize`/`isize` to the target's pointer-width
//!   integers, so those arrive here as plain `uN`/`iN` and are read as such
//!   (harness row `d_match_char`); only the faithful extraction keeps
//!   `Ty::Char` and `Ty::PtrSizedInt`.
//! * A `u128` decision or comparison: read here, but the producer has no
//!   image at `U128` and refuses the mint (harness row `d_match_u128`).
//! * Guards and bindings are not visible as such in the extracted MIR: a
//!   binding arm is a copy of the scrutinee parameter, and a guard is a
//!   comparison and a branch (MEASURED on stage-1 MIR: `n if n > 5` at the
//!   default opt level is exactly `if x > 5`) — so they are read as the
//!   decisions they lower to, and a guard that borrows its binding (`-O`
//!   keeps `&x`) is refused as a borrow.
//!
//! # Value decisions (I4′)
//!
//! A decision whose arms are not `bool` literals stays an [`E6Term::Ite`] —
//! `if c { a } else { b }` at any carrier, including `bool` — and a `match`
//! becomes a chain of them over `d == v` tests (`Reader::match_decision`).
//! Arms are parameters, literals, and nested decisions; the producer mints
//! each as Clean's `ite` over the test's proposition, which is what an
//! island's `if … then … else …` elaborates to.
//!
//! Its reading is in the trusted base (`docs/TCB.md`,
//! `EnsuresCitationDischarge`): what it reads becomes a kernel defining
//! equation through `trust_spec_elab::admit_e6_tree_function`. The
//! differential harness (`crates/trust-certify/tests/e6_differential.rs`)
//! executes a fixture row of every carrier this reader and that producer
//! admit — `bool`, `u8`, `i8`, `u16` and `i16` on EVERY input; `u32`, `i32`,
//! `u64`, `i64` and `i128` on a fixed boundary-plus-xorshift SAMPLE — against
//! the Rust body. That is a row per carrier and construct, not every body:
//! a shape no row spells is checked only by the kernel's typing of its image.

use std::collections::BTreeMap;

use crate::{
    BasicBlock, BinOp, BlockId, ConstValue, Operand, Rvalue, Statement, Terminator, Ty, UnOp,
    VerifiableFunction,
};

/// Compiler-authenticated wrapping operation for the E6-only tree lane.
/// This leaves the frozen unsigned Clean-origin recognizer unchanged.
#[must_use]
pub fn wrapping_primitive(callee: &str) -> Option<(BinOp, Ty)> {
    let path = callee.strip_prefix(crate::TRUST_RUSTC_TOTAL_PRIMITIVE_METHOD_PATH_PREFIX)?;
    let tail = path.strip_prefix("core::num::<impl ")?;
    let (scalar, method) = tail.split_once(">::")?;
    let (signed, digits) = if let Some(w) = scalar.strip_prefix('i') {
        (true, w)
    } else {
        (false, scalar.strip_prefix('u')?)
    };
    let width = match digits {
        "8" => 8,
        "16" => 16,
        "32" => 32,
        "64" => 64,
        _ => return None,
    };
    let op = match method {
        "wrapping_add" => BinOp::Add,
        "wrapping_sub" => BinOp::Sub,
        "wrapping_mul" => BinOp::Mul,
        _ => return None,
    };
    Some((op, Ty::Int { width, signed }))
}

/// Exact checked primitive identity for the E6-only matched-Option lane.
#[must_use]
pub fn checked_primitive(callee: &str) -> Option<(BinOp, Ty)> {
    let path = callee.strip_prefix(crate::TRUST_RUSTC_CHECKED_PRIMITIVE_METHOD_PATH_PREFIX)?;
    let tail = path.strip_prefix("core::num::<impl ")?;
    let (scalar, method) = tail.split_once(">::")?;
    let (signed, digits) = if let Some(w) = scalar.strip_prefix('i') {
        (true, w)
    } else {
        (false, scalar.strip_prefix('u')?)
    };
    let width = match digits {
        "8" => 8,
        "16" => 16,
        "32" => 32,
        "64" => 64,
        _ => return None,
    };
    let op = match method {
        "checked_add" | "wrapping_add" => BinOp::Add,
        "checked_sub" | "wrapping_sub" => BinOp::Sub,
        "checked_mul" | "wrapping_mul" => BinOp::Mul,
        _ => return None,
    };
    Some((op, Ty::Int { width, signed }))
}

/// The pinned, directly tagged Option of a fixed-width scalar. No niche
/// layouts, user enums, references, or pointer-sized payloads enter this lane.
#[must_use]
pub fn option_payload(ty: &Ty) -> Option<&Ty> {
    let Ty::Adt { name, variants, disc_index_safe: true, .. } = ty else {
        return None;
    };
    if name != "core::option::Option" {
        return None;
    }
    let [none, some] = variants.as_slice() else {
        return None;
    };
    if none.name != "None"
        || none.discriminant != 0
        || !none.fields.is_empty()
        || some.name != "Some"
        || some.discriminant != 1
    {
        return None;
    }
    let [(_, ty @ Ty::Int { width: 8 | 16 | 32 | 64, .. })] = some.fields.as_slice() else {
        return None;
    };
    Some(ty)
}

/// The comparison an [`E6Term::Cmp`] decides. `>` and `>=` arrive
/// OPERAND-SWAPPED as `Lt`/`Le` (`a > b` is `b < a`), the normalization the
/// clause elaborator and the frozen recognizer both use.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum E6Cmp {
    /// `==`.
    Eq,
    /// `!=`.
    Ne,
    /// `<`.
    Lt,
    /// `<=`.
    Le,
}

/// The scalar carrier a comparison's operands share.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum E6Carrier {
    /// `bool`.
    Bool,
    /// `uN`, by width in bits.
    Unsigned(u32),
    /// `iN`, by width in bits.
    Signed(u32),
}

impl E6Carrier {
    /// The carrier of a scalar type, or `None` outside the vocabulary.
    #[must_use]
    pub fn of(ty: &Ty) -> Option<Self> {
        match ty {
            Ty::Bool => Some(E6Carrier::Bool),
            Ty::Int { width, signed } if matches!(width, 8 | 16 | 32 | 64 | 128) => {
                Some(if *signed { E6Carrier::Signed(*width) } else { E6Carrier::Unsigned(*width) })
            }
            _ => None,
        }
    }
}

/// A term of the E6-only tree reader: what a body computes, over its
/// parameters. The compiler-side twin of `trust_spec_elab::E6TreeTerm`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum E6Term {
    /// A 0-based source parameter.
    Param(usize),
    /// A `bool` literal.
    Bool(bool),
    /// An integer literal, at the carrier of the position it is used in (the
    /// reader has already checked it fits that carrier).
    Int(i128),
    /// Fixed-width modular arithmetic: a marker-authenticated `wrapping_*`
    /// call, a `checked_*` payload on its Some edge, or the `.0` of an overflow
    /// pair that no `Assert` guards (an `Assert` refuses the whole body).
    Arith { op: BinOp, carrier: E6Carrier, left: Box<E6Term>, right: Box<E6Term> },
    /// Whether exact mathematical arithmetic lies outside its carrier.
    Overflow { op: BinOp, carrier: E6Carrier, left: Box<E6Term>, right: Box<E6Term> },
    /// Internal Option value; its payload is readable only in the Some arm.
    Checked { value: Box<E6Term>, overflow: Box<E6Term>, available: bool },
    /// Internal Option discriminant, retaining the storage it refines.
    CheckedTag { local: usize, overflow: Box<E6Term> },
    /// `!x` over `bool`.
    Not(Box<E6Term>),
    /// `x && y` (and the non-short-circuit `x & y`) over `bool`.
    And(Box<E6Term>, Box<E6Term>),
    /// `x || y` (and `x | y`) over `bool`.
    Or(Box<E6Term>, Box<E6Term>),
    /// `x ^ y` over `bool`.
    Xor(Box<E6Term>, Box<E6Term>),
    /// `left ⊲ right`, both operands of `carrier`.
    Cmp {
        /// The comparison.
        op: E6Cmp,
        /// The operands' shared carrier.
        carrier: E6Carrier,
        /// Left operand.
        left: Box<E6Term>,
        /// Right operand.
        right: Box<E6Term>,
    },
    /// `if cond { then } else { els }` (I4′): a decision whose arms are not
    /// both reducible to connectives — a value select, a `match` arm chain,
    /// or a `bool` decision over non-literal arms.
    Ite {
        /// The `bool` decided on.
        cond: Box<E6Term>,
        /// The value when `cond` holds.
        then: Box<E6Term>,
        /// The value otherwise.
        els: Box<E6Term>,
    },
}

impl E6Term {
    fn not(x: E6Term) -> E6Term {
        E6Term::Not(Box::new(x))
    }
    fn and(x: E6Term, y: E6Term) -> E6Term {
        E6Term::And(Box::new(x), Box::new(y))
    }
    fn or(x: E6Term, y: E6Term) -> E6Term {
        E6Term::Or(Box::new(x), Box::new(y))
    }
    fn ite(cond: E6Term, then: E6Term, els: E6Term) -> E6Term {
        E6Term::Ite { cond: Box::new(cond), then: Box::new(then), els: Box::new(els) }
    }

    /// Whether any node of the term is an [`E6Term::Ite`].
    #[must_use]
    pub fn has_ite(&self) -> bool {
        match self {
            E6Term::Param(_) | E6Term::Bool(_) | E6Term::Int(_) => false,
            E6Term::Overflow { left, right, .. } => left.has_ite() || right.has_ite(),
            E6Term::Checked { value, overflow, .. } => value.has_ite() || overflow.has_ite(),
            E6Term::CheckedTag { overflow, .. } => overflow.has_ite(),
            E6Term::Not(x) => x.has_ite(),
            E6Term::And(x, y) | E6Term::Or(x, y) | E6Term::Xor(x, y) => x.has_ite() || y.has_ite(),
            E6Term::Arith { left, right, .. } | E6Term::Cmp { left, right, .. } => {
                left.has_ite() || right.has_ite()
            }
            E6Term::Ite { .. } => true,
        }
    }

    /// Whether any leaf of the term is a parameter.
    #[must_use]
    pub fn mentions_param(&self) -> bool {
        match self {
            E6Term::Param(_) => true,
            E6Term::Bool(_) | E6Term::Int(_) => false,
            E6Term::Overflow { left, right, .. } => left.mentions_param() || right.mentions_param(),
            E6Term::Checked { value, overflow, .. } => {
                value.mentions_param() || overflow.mentions_param()
            }
            E6Term::CheckedTag { overflow, .. } => overflow.mentions_param(),
            E6Term::Not(x) => x.mentions_param(),
            E6Term::And(x, y) | E6Term::Or(x, y) | E6Term::Xor(x, y) => {
                x.mentions_param() || y.mentions_param()
            }
            E6Term::Arith { left, right, .. } | E6Term::Cmp { left, right, .. } => {
                left.mentions_param() || right.mentions_param()
            }
            E6Term::Ite { cond, then, els } => {
                cond.mentions_param() || then.mentions_param() || els.mentions_param()
            }
        }
    }

    /// The number of nodes, for the size bound.
    #[must_use]
    pub fn size(&self) -> usize {
        1 + match self {
            E6Term::Param(_) | E6Term::Bool(_) | E6Term::Int(_) => 0,
            E6Term::Overflow { left, right, .. } => left.size() + right.size(),
            E6Term::Checked { value, overflow, .. } => value.size() + overflow.size(),
            E6Term::CheckedTag { overflow, .. } => overflow.size(),
            E6Term::Not(x) => x.size(),
            E6Term::And(x, y) | E6Term::Or(x, y) | E6Term::Xor(x, y) => x.size() + y.size(),
            E6Term::Arith { left, right, .. } | E6Term::Cmp { left, right, .. } => {
                left.size() + right.size()
            }
            E6Term::Ite { cond, then, els } => cond.size() + then.size() + els.size(),
        }
    }
}

/// Rewrite the `bool` decisions of `t` into the connectives a short-circuit
/// source was written with, bottom-up, and nest every `&&`/`||` chain to the
/// RIGHT. Each rule is a Boolean identity over PURE, TOTAL operands (every
/// term the reader builds is one), so the result denotes the same function;
/// `normalization_rules_are_identities` checks every rule on every assignment
/// of its operands, and `normalization_preserves_every_small_tree` every
/// decision tree of depth two over three `bool`s.
///
/// | decision | becomes | the source that lowers to it |
/// |---|---|---|
/// | `if c {true} else {false}` | `c` | `c` in value position |
/// | `if c {false} else {true}` | `!c` | `!c` through a branch |
/// | `if c {true} else {e}` | `c \|\| e` | `c \|\| e` |
/// | `if c {t} else {false}` | `c && t` | `c && t` |
/// | `if c {false} else {e}` | `!c && e` | `!c && e` |
/// | `if c {t} else {true}` | `!c \|\| t` | `!c \|\| t` |
/// | `if c {x₁ \|\| … \|\| e} else {e}` | `(c && (x₁ \|\| …)) \|\| e` | the same |
/// | `if c {e} else {x₁ && … && e}` | `(c \|\| (x₁ && …)) && e` | the same |
/// | `if c {e} else {x₁ \|\| … \|\| e}` | `(!c && (x₁ \|\| …)) \|\| e` | the same |
/// | `if c {x₁ && … && e} else {e}` | `(!c \|\| (x₁ && …)) && e` | the same |
///
/// The last four recover an `&&` nested under `||` (and back): rustc shares
/// the `||`'s right operand between the two failure edges of the `&&`, and
/// the walk reaches it from both arms. Anything else stays a decision.
///
/// RIGHT NESTING: `(x && y) && z` becomes `x && (y && z)`, and likewise for
/// `||` — associativity, exact over `bool`. It is what Clean's parser makes of
/// an island's `x && y && z` (`e6_spelling_pins.rs`: `and_parses_right_nested`,
/// `or_parses_right_nested`), and what MIR's short-circuit tree already is;
/// the non-short-circuit `s & i & n` arrives LEFT-nested and is re-nested so
/// that ay's `self_ind & init_valid & entry_ind` meets its natural island.
/// `^` is not re-nested (Clean has no infix `xor`; an island spells the calls).
#[must_use]
pub fn normalize_bool(t: E6Term) -> E6Term {
    use E6Term::{And, Bool, Cmp, Ite, Not, Or, Xor};
    match t {
        Ite { cond, then, els } => {
            let c = normalize_bool(*cond);
            let th = normalize_bool(*then);
            let el = normalize_bool(*els);
            match (th, el) {
                (Bool(true), Bool(false)) => c,
                (Bool(false), Bool(true)) => E6Term::not(c),
                (Bool(true), el) => or_(c, el),
                (th, Bool(false)) => and_(c, th),
                (Bool(false), el) => and_(E6Term::not(c), el),
                (th, Bool(true)) => or_(E6Term::not(c), th),
                (th, el) => {
                    if let Some(xs) = spine_prefix(&th, &el, Spine::Or) {
                        or_(and_(c, xs), el)
                    } else if let Some(xs) = spine_prefix(&el, &th, Spine::And) {
                        and_(or_(c, xs), th)
                    } else if let Some(xs) = spine_prefix(&el, &th, Spine::Or) {
                        or_(and_(E6Term::not(c), xs), th)
                    } else if let Some(xs) = spine_prefix(&th, &el, Spine::And) {
                        and_(or_(E6Term::not(c), xs), el)
                    } else {
                        E6Term::ite(c, th, el)
                    }
                }
            }
        }
        Not(x) => E6Term::not(normalize_bool(*x)),
        And(x, y) => and_(normalize_bool(*x), normalize_bool(*y)),
        Or(x, y) => or_(normalize_bool(*x), normalize_bool(*y)),
        Xor(x, y) => Xor(Box::new(normalize_bool(*x)), Box::new(normalize_bool(*y))),
        Cmp { op, carrier, left, right } => Cmp {
            op,
            carrier,
            left: Box::new(normalize_bool(*left)),
            right: Box::new(normalize_bool(*right)),
        },
        leaf => leaf,
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Spine {
    And,
    Or,
}

/// `x && y`, nested to the right: `(a && b) && y` is `a && (b && y)`.
fn and_(x: E6Term, y: E6Term) -> E6Term {
    match x {
        E6Term::And(a, b) => E6Term::and(*a, and_(*b, y)),
        x => E6Term::and(x, y),
    }
}

/// `x || y`, nested to the right.
fn or_(x: E6Term, y: E6Term) -> E6Term {
    match x {
        E6Term::Or(a, b) => E6Term::or(*a, or_(*b, y)),
        x => E6Term::or(x, y),
    }
}

/// When `t` is a right-nested `spine` chain `x₁ ∘ … ∘ xₖ ∘ last` (k ≥ 1),
/// the right-nested chain `x₁ ∘ … ∘ xₖ` of its operands before `last`.
fn spine_prefix(t: &E6Term, last: &E6Term, spine: Spine) -> Option<E6Term> {
    let mut xs: Vec<&E6Term> = Vec::new();
    let mut at = t;
    loop {
        let (x, rest) = match (spine, at) {
            (Spine::And, E6Term::And(x, rest)) | (Spine::Or, E6Term::Or(x, rest)) => {
                (x.as_ref(), rest.as_ref())
            }
            _ => return None,
        };
        xs.push(x);
        if *rest == *last {
            break;
        }
        at = rest;
    }
    // The loop pushes before it can stop, so `xs` is never empty here; an empty
    // prefix would make no chain, and the rule that asked keeps its decision.
    let mut it = xs.into_iter().rev();
    let innermost = it.next()?.clone();
    Some(it.fold(innermost, |acc, x| match spine {
        Spine::And => E6Term::and(x.clone(), acc),
        Spine::Or => E6Term::or(x.clone(), acc),
    }))
}

/// How many block visits the walk may make before it fails closed. A block
/// is revisited only when it is shared by two arms without post-dominating
/// them (the `||` operand an `&&`'s two failure edges share); the bound only
/// stops a pathological CFG.
const MAX_BLOCK_VISITS: usize = 2048;

/// How many nodes a read term may have before the reader fails closed.
const MAX_TERM_SIZE: usize = 4096;

/// A value in the symbolic environment: its term and its MIR type.
#[derive(Debug, Clone)]
struct Sym {
    term: E6Term,
    ty: Ty,
}

struct Reader<'f> {
    func: &'f VerifiableFunction,
    post_dominators: PostDominators,
    visits: usize,
    option_defaults: BTreeMap<usize, usize>,
}

fn binop_spelling(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Rem => "%",
        BinOp::Eq => "==",
        BinOp::Ne => "!=",
        BinOp::Lt => "<",
        BinOp::Le => "<=",
        BinOp::Gt => ">",
        BinOp::Ge => ">=",
        BinOp::BitAnd => "&",
        BinOp::BitOr => "|",
        BinOp::BitXor => "^",
        BinOp::Shl => "<<",
        BinOp::Shr => ">>",
        BinOp::Cmp => "cmp",
    }
}

impl<'f> Reader<'f> {
    fn local_ty(&self, local: usize) -> Result<&Ty, String> {
        if let Some(l) = self.func.body.locals.get(local)
            && l.index == local
        {
            return Ok(&l.ty);
        }
        self.func
            .body
            .locals
            .iter()
            .find(|l| l.index == local)
            .map(|l| &l.ty)
            .ok_or_else(|| format!("the local `_{local}` has no declaration"))
    }

    fn is_param(&self, local: usize) -> bool {
        local >= 1 && local <= self.func.body.arg_count
    }

    fn block(&self, id: BlockId) -> Result<&'f BasicBlock, String> {
        let func: &'f VerifiableFunction = self.func;
        if let Some(b) = func.body.blocks.get(id.0)
            && b.id == id
        {
            return Ok(b);
        }
        func.body
            .blocks
            .iter()
            .find(|b| b.id == id)
            .ok_or_else(|| format!("the block bb{} does not exist", id.0))
    }

    /// The term an operand denotes. `expected` types an untyped signed
    /// literal (`ConstValue::Int` carries no width); every other operand
    /// carries its own type, which must then equal `expected`.
    fn operand(
        &self,
        op: &Operand,
        expected: Option<&Ty>,
        env: &BTreeMap<usize, Sym>,
    ) -> Result<Sym, String> {
        let sym = match op {
            Operand::Copy(p) | Operand::Move(p) => {
                if let [crate::Projection::Field(field @ (0 | 1))] = p.projections.as_slice() {
                    if let Some(Sym {
                        term: E6Term::Checked { value, overflow, .. },
                        ty: Ty::Tuple(fields),
                    }) = env.get(&p.local)
                    {
                        let ty = fields.get(*field).ok_or("invalid overflow-pair projection")?;
                        if expected.is_some_and(|want| want != ty) {
                            return Err("mistyped overflow-pair projection".into());
                        }
                        return Ok(Sym {
                            term: if *field == 0 { *value.clone() } else { *overflow.clone() },
                            ty: ty.clone(),
                        });
                    }
                }
                if matches!(
                    p.projections.as_slice(),
                    [crate::Projection::Downcast(1), crate::Projection::Field(0)]
                ) {
                    let sym = env.get(&p.local).ok_or("an unresolved Option payload")?;
                    let ty = option_payload(&sym.ty)
                        .ok_or("a payload outside the tagged Option fragment")?;
                    let E6Term::Checked { value, available: true, .. } = &sym.term else {
                        return Err("an Option payload read outside its Some arm".into());
                    };
                    if expected.is_some_and(|want| want != ty) {
                        return Err("a mistyped Option payload".into());
                    }
                    return Ok(Sym { term: *value.clone(), ty: ty.clone() });
                }
                if !p.projections.is_empty() {
                    return Err(format!("a read through a projection of `_{}`", p.local));
                }
                if self.is_param(p.local) {
                    let ty = self.local_ty(p.local)?.clone();
                    if E6Carrier::of(&ty).is_none() {
                        return Err(format!(
                            "a read of the parameter `_{}` of type `{}`, which has no scalar \
                             carrier here",
                            p.local,
                            super::ty_spelling(&ty)
                        ));
                    }
                    Sym { term: E6Term::Param(p.local - 1), ty }
                } else {
                    env.get(&p.local).cloned().ok_or_else(|| {
                        format!("a read of `_{}` before any write to it on this path", p.local)
                    })?
                }
            }
            Operand::Constant(ConstValue::Bool(b)) => Sym { term: E6Term::Bool(*b), ty: Ty::Bool },
            Operand::Constant(ConstValue::Uint(v, w)) => {
                let ty = Ty::Int { width: *w, signed: false };
                if E6Carrier::of(&ty).is_none()
                    || (*w < 128 && *v >> *w != 0)
                    || i128::try_from(*v).is_err()
                {
                    return Err(format!("the literal {v} at `u{w}`, outside the carriers"));
                }
                Sym { term: E6Term::Int(*v as i128), ty }
            }
            Operand::Constant(ConstValue::Int(v)) => {
                let Some(ty @ Ty::Int { width, signed: true }) = expected else {
                    return Err(format!("the signed literal {v} whose carrier is not known here"));
                };
                let fits = *width == 128 || {
                    let bound = 1i128 << (width - 1);
                    (-bound..bound).contains(v)
                };
                if E6Carrier::of(ty).is_none() || !fits {
                    return Err(format!("the literal {v}, outside `{}`", super::ty_spelling(ty)));
                }
                Sym { term: E6Term::Int(*v), ty: ty.clone() }
            }
            _ => return Err("an operand the E6 tree reader does not model".to_owned()),
        };
        if let Some(want) = expected
            && &sym.ty != want
        {
            return Err(format!(
                "a `{}` value where the MIR expects `{}`",
                super::ty_spelling(&sym.ty),
                super::ty_spelling(want)
            ));
        }
        Ok(sym)
    }

    /// Both operands of a binary operation, typing an untyped literal on one
    /// side by the other side.
    fn operand_pair(
        &self,
        l: &Operand,
        r: &Operand,
        env: &BTreeMap<usize, Sym>,
    ) -> Result<(Sym, Sym), String> {
        let untyped = |o: &Operand| matches!(o, Operand::Constant(ConstValue::Int(_)));
        if untyped(l) {
            let rs = self.operand(r, None, env)?;
            let ls = self.operand(l, Some(&rs.ty), env)?;
            Ok((ls, rs))
        } else {
            let ls = self.operand(l, None, env)?;
            let rs = self.operand(r, Some(&ls.ty), env)?;
            Ok((ls, rs))
        }
    }

    /// The exact modular image of a marker-authenticated `wrapping_*` call:
    /// both operands and the destination share one fixed-width carrier. A raw
    /// `BinaryOp` never reaches this (`Self::rvalue` refuses it).
    fn wrapping_arith(
        &self,
        op: BinOp,
        l: &Operand,
        r: &Operand,
        dest: &Ty,
        env: &BTreeMap<usize, Sym>,
    ) -> Result<Sym, String> {
        let (ls, rs) = self.operand_pair(l, r, env)?;
        let carrier = E6Carrier::of(dest).ok_or("arithmetic on a non-integer")?;
        if !matches!(dest, Ty::Int { width: 8 | 16 | 32 | 64, .. })
            || ls.ty != *dest
            || rs.ty != *dest
        {
            return Err("arithmetic operands must share a fixed-width integer carrier".into());
        }
        Ok(Sym {
            term: E6Term::Arith { op, carrier, left: Box::new(ls.term), right: Box::new(rs.term) },
            ty: dest.clone(),
        })
    }

    fn rvalue(&self, rv: &Rvalue, dest: &Ty, env: &BTreeMap<usize, Sym>) -> Result<Sym, String> {
        match rv {
            Rvalue::Use(op) => self.operand(op, Some(dest), env),
            Rvalue::UnaryOp(UnOp::Not, x) => {
                let xs = self.operand(x, Some(dest), env)?;
                if xs.ty != Ty::Bool {
                    return Err(format!(
                        "the negation `!` on `{}` (a bitwise negation; bitwise operations are \
                         increment I2′)",
                        super::ty_spelling(&xs.ty)
                    ));
                }
                Ok(Sym { term: E6Term::not(xs.term), ty: Ty::Bool })
            }
            // Raw arithmetic is an undischarged panic operation and is never
            // read (E6-TG14-PANIC-EDGE-1): only the marker-authenticated
            // `wrapping_*` call reads as `Arith` (`Self::wrapping_arith`).
            Rvalue::BinaryOp(op @ (BinOp::Add | BinOp::Sub | BinOp::Mul), l, _) => Err(format!(
                "the raw arithmetic `{}` (`BinOp::{op:?}`){}, an undischarged panic operation: \
                 the tree reader reads only the marker-authenticated `wrapping_*` and \
                 `checked_*` calls",
                binop_spelling(*op),
                self.operand(l, None, env)
                    .map(|s| format!(" on `{}`", super::ty_spelling(&s.ty)))
                    .unwrap_or_default()
            )),
            Rvalue::BinaryOp(op @ (BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor), l, r) => {
                let (ls, rs) = self.operand_pair(l, r, env)?;
                if ls.ty != Ty::Bool || rs.ty != Ty::Bool || *dest != Ty::Bool {
                    return Err(format!(
                        "the bit operation `{}` on `{}` (bitwise operations on integers are \
                         increment I2′)",
                        binop_spelling(*op),
                        super::ty_spelling(&ls.ty)
                    ));
                }
                let (x, y) = (Box::new(ls.term), Box::new(rs.term));
                let term = match op {
                    BinOp::BitAnd => E6Term::And(x, y),
                    BinOp::BitOr => E6Term::Or(x, y),
                    _ => E6Term::Xor(x, y),
                };
                Ok(Sym { term, ty: Ty::Bool })
            }
            Rvalue::BinaryOp(
                op @ (BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge),
                l,
                r,
            ) => {
                if *dest != Ty::Bool {
                    return Err("a comparison into a non-`bool` place".to_owned());
                }
                let (ls, rs) = self.operand_pair(l, r, env)?;
                let carrier = E6Carrier::of(&ls.ty)
                    .ok_or_else(|| format!("a comparison over `{}`", super::ty_spelling(&ls.ty)))?;
                if carrier == E6Carrier::Bool {
                    if !matches!(op, BinOp::Eq | BinOp::Ne) {
                        return Err(format!(
                            "the ordering `{}` over `bool` (an ordering has no E6 image: only \
                             `==` and `!=` over `bool` are read, and an equality image for an \
                             ordering would be a false import)",
                            binop_spelling(*op)
                        ));
                    }
                }
                if carrier != E6Carrier::Bool {
                    fn operand(t: &E6Term) -> bool {
                        match t {
                            E6Term::Param(_) | E6Term::Int(_) => true,
                            E6Term::Arith { left, right, .. } => operand(left) && operand(right),
                            _ => false,
                        }
                    }
                    if !operand(&ls.term) || !operand(&rs.term) {
                        return Err(format!(
                            "a comparison `{}` over `{}` whose operand is computed outside the arithmetic fragment",
                            binop_spelling(*op),
                            super::ty_spelling(&ls.ty),
                        ));
                    }
                    if !ls.term.mentions_param() && !rs.term.mentions_param() {
                        return Err("a comparison of two literals".into());
                    }
                }
                let (op, left, right) = match op {
                    BinOp::Eq => (E6Cmp::Eq, ls.term, rs.term),
                    BinOp::Ne => (E6Cmp::Ne, ls.term, rs.term),
                    BinOp::Lt => (E6Cmp::Lt, ls.term, rs.term),
                    BinOp::Le => (E6Cmp::Le, ls.term, rs.term),
                    // `a > b` is `b < a`; `a >= b` is `b <= a`.
                    BinOp::Gt => (E6Cmp::Lt, rs.term, ls.term),
                    _ => (E6Cmp::Le, rs.term, ls.term),
                };
                Ok(Sym {
                    term: E6Term::Cmp { op, carrier, left: Box::new(left), right: Box::new(right) },
                    ty: Ty::Bool,
                })
            }
            Rvalue::BinaryOp(op, l, _) => Err(format!(
                "the operation `{}` (`BinOp::{op:?}`){}",
                binop_spelling(*op),
                self.operand(l, None, env)
                    .map(|s| format!(" on `{}`", super::ty_spelling(&s.ty)))
                    .unwrap_or_default()
            )),
            Rvalue::CheckedBinaryOp(op @ (BinOp::Add | BinOp::Sub | BinOp::Mul), l, r) => {
                let Ty::Tuple(fields) = dest else {
                    return Err("checked arithmetic outside an overflow pair".into());
                };
                let [ty @ Ty::Int { width: 8 | 16 | 32 | 64, .. }, Ty::Bool] = fields.as_slice()
                else {
                    return Err("unsupported overflow-pair carrier".into());
                };
                let ls = self.operand(l, Some(ty), env)?.term;
                let rs = self.operand(r, Some(ty), env)?.term;
                let carrier = E6Carrier::of(ty)
                    .ok_or_else(|| "unsupported overflow-pair carrier".to_owned())?;
                Ok(Sym {
                    term: E6Term::Checked {
                        value: Box::new(E6Term::Arith {
                            op: *op,
                            carrier,
                            left: Box::new(ls.clone()),
                            right: Box::new(rs.clone()),
                        }),
                        overflow: Box::new(E6Term::Overflow {
                            op: *op,
                            carrier,
                            left: Box::new(ls),
                            right: Box::new(rs),
                        }),
                        available: false,
                    },
                    ty: dest.clone(),
                })
            }
            Rvalue::CheckedBinaryOp(op, ..) => {
                Err(format!("the overflow-checked `{}`, a panic path", binop_spelling(*op)))
            }
            Rvalue::UncheckedBinaryOp(op, ..) => Err(format!(
                "the unchecked `{}` (undefined behaviour on overflow)",
                binop_spelling(*op)
            )),
            Rvalue::Cast(..) => Err("a cast".to_owned()),
            Rvalue::Discriminant(p) if p.projections.is_empty() => {
                let sym = env.get(&p.local).ok_or("an unresolved Option discriminant")?;
                option_payload(&sym.ty)
                    .ok_or("an enum discriminant outside the checked Option fragment")?;
                let E6Term::Checked { overflow, .. } = &sym.term else {
                    return Err("an unmodeled Option discriminant".into());
                };
                if !matches!(dest, Ty::Int { width: 8 | 16 | 32 | 64, .. }) {
                    return Err("an unmodeled discriminant carrier".into());
                }
                Ok(Sym {
                    term: E6Term::CheckedTag { local: p.local, overflow: overflow.clone() },
                    ty: dest.clone(),
                })
            }
            Rvalue::Ref { .. } | Rvalue::AddressOf(..) => Err("a borrow".to_owned()),
            _ => Err("an rvalue the E6 tree reader does not model".to_owned()),
        }
    }

    /// Execute the statements of `bb` into `env`.
    fn statements(&self, bb: &BasicBlock, env: &mut BTreeMap<usize, Sym>) -> Result<(), String> {
        for stmt in &bb.stmts {
            if crate::admissible_body::is_value_neutral(stmt) {
                continue;
            }
            let Statement::Assign { place, rvalue, .. } = stmt else {
                return Err("a statement other than an assignment".to_owned());
            };
            if !place.projections.is_empty() {
                return Err(format!("a write through a projection of `_{}`", place.local));
            }
            if self.is_param(place.local) {
                return Err(format!("a write to the parameter `_{}`", place.local));
            }
            let dest = self.local_ty(place.local)?.clone();
            let sym = self.rvalue(rvalue, &dest, env)?;
            if sym.term.size() > MAX_TERM_SIZE {
                return Err(format!("a term larger than {MAX_TERM_SIZE} nodes"));
            }
            env.insert(place.local, sym);
        }
        Ok(())
    }

    /// Execute from `from` until control reaches `stop` (a block, or the
    /// function's EXIT for `None`), and answer the environment there.
    ///
    /// A `switchInt` is executed as a DECISION: each arm runs to the switch's
    /// IMMEDIATE POST-DOMINATOR — the block every path from the switch passes
    /// through — and the arms' environments are MERGED there, a local the arms
    /// disagree on becoming `if d { … } else { … }` over their values (the
    /// SSA φ, exact because every term is a pure function of the never-written
    /// parameters, so `d` denotes at the join what it denoted at the switch).
    /// Execution then continues ONCE from the join. So a short-circuit result
    /// computed into a temporary and used afterwards (`!(a && b)`,
    /// `let x = a && b; x || a`) is read as the expression the source wrote,
    /// not duplicated into each arm.
    fn region(
        &mut self,
        from: BlockId,
        stop: Option<BlockId>,
        mut env: BTreeMap<usize, Sym>,
    ) -> Result<BTreeMap<usize, Sym>, String> {
        let mut at = from;
        loop {
            if Some(at) == stop {
                return Ok(env);
            }
            self.visits += 1;
            if self.visits > MAX_BLOCK_VISITS {
                return Err(format!(
                    "a control-flow graph that unfolds past {MAX_BLOCK_VISITS} blocks"
                ));
            }
            let bb = self.block(at)?;
            self.statements(bb, &mut env)?;
            match &bb.terminator {
                Terminator::Return => {
                    return if stop.is_none() {
                        Ok(env)
                    } else {
                        Err("a `Return` inside a decision that should rejoin".to_owned())
                    };
                }
                Terminator::Goto(target) => at = *target,
                Terminator::SwitchInt {
                    discr,
                    targets,
                    otherwise,
                    exhaustive_enum_unreachable,
                    ..
                } => {
                    let join = self.post_dominators.immediate(at)?;
                    if join.is_none() && stop.is_some() {
                        return Err("a decision that does not rejoin inside its region".to_owned());
                    }
                    let d = self.operand(discr, None, &env)?;
                    if *exhaustive_enum_unreachable && !matches!(d.term, E6Term::CheckedTag { .. })
                    {
                        return Err("an enum-discriminant `switchInt`".to_owned());
                    }
                    if let E6Term::CheckedTag { local, overflow } = &d.term {
                        let mut on_none = None;
                        let mut on_some = None;
                        for (label, target) in targets {
                            let slot = match label {
                                0 => &mut on_none,
                                1 => &mut on_some,
                                _ => return Err("invalid Option tag label".into()),
                            };
                            if slot.replace(*target).is_some() {
                                return Err("duplicate Option tag label".into());
                            }
                        }
                        if *exhaustive_enum_unreachable && (on_none.is_none() || on_some.is_none())
                        {
                            return Err("an incomplete exhaustive Option tag switch".into());
                        }
                        if *exhaustive_enum_unreachable {
                            let default = self.block(*otherwise)?;
                            if matches!(default.terminator, Terminator::Unreachable)
                                && default
                                    .stmts
                                    .iter()
                                    .all(crate::admissible_body::is_value_neutral)
                            {
                                self.option_defaults.insert(at.0, otherwise.0);
                            }
                        }
                        let none_env = env.clone();
                        let mut some_env = env;
                        let Some(Sym {
                            term: E6Term::Checked { available, overflow: current, .. },
                            ..
                        }) = some_env.get_mut(local)
                        else {
                            return Err("lost Option storage identity".into());
                        };
                        if current.as_ref() != overflow.as_ref() {
                            return Err(
                                "an Option discriminant outlived a write to its storage".into()
                            );
                        }
                        *available = true;
                        let none = self.region(on_none.unwrap_or(*otherwise), join, none_env)?;
                        let some = self.region(on_some.unwrap_or(*otherwise), join, some_env)?;
                        env = merge(&none, &some, |t, e| E6Term::ite(*overflow.clone(), t, e))?;
                    } else {
                        env = self.decision(&d, targets, *otherwise, join, env)?;
                    }

                    match join {
                        Some(j) => at = j,
                        None => return Ok(env),
                    }
                }
                Terminator::Call {
                    func,
                    args,
                    dest,
                    target: Some(target),
                    atomic: None,
                    is_foreign: false,
                    is_unsafe_sig: false,
                    ..
                } => {
                    if let Some((op, payload)) = checked_primitive(func) {
                        if !dest.projections.is_empty()
                            || self.is_param(dest.local)
                            || args.len() != 2
                        {
                            return Err("a malformed checked primitive call".into());
                        }
                        let ty = self.local_ty(dest.local)?.clone();
                        if option_payload(&ty) != Some(&payload) {
                            return Err("a checked call with a mismatched Option carrier".into());
                        }
                        let left = self.operand(&args[0], Some(&payload), &env)?.term;
                        let right = self.operand(&args[1], Some(&payload), &env)?.term;
                        let carrier = E6Carrier::of(&payload)
                            .ok_or_else(|| "unsupported checked primitive carrier".to_owned())?;
                        let overflow = E6Term::Overflow {
                            op,
                            carrier,
                            left: Box::new(left.clone()),
                            right: Box::new(right.clone()),
                        };
                        let value = E6Term::Arith {
                            op,
                            carrier,
                            left: Box::new(left),
                            right: Box::new(right),
                        };
                        let term = E6Term::Checked {
                            value: Box::new(value),
                            overflow: Box::new(overflow),
                            available: false,
                        };
                        if term.size() > MAX_TERM_SIZE {
                            return Err("a checked expression exceeds the term bound".into());
                        }
                        env.insert(dest.local, Sym { term, ty });
                        at = *target;
                    } else if let Some((op, expected)) = wrapping_primitive(func) {
                        if !dest.projections.is_empty()
                            || self.is_param(dest.local)
                            || args.len() != 2
                        {
                            return Err("a projected or malformed wrapping call".into());
                        }
                        let ty = self.local_ty(dest.local)?.clone();
                        if ty != expected {
                            return Err("a wrapping call with a mismatched carrier".into());
                        }
                        let value = self.wrapping_arith(op, &args[0], &args[1], &ty, &env)?;
                        if value.term.size() > MAX_TERM_SIZE {
                            return Err("a wrapping expression exceeds the term bound".into());
                        }
                        env.insert(dest.local, value);
                        at = *target;
                    } else {
                        return Err(format!("the call to `{func}`"));
                    }
                }
                Terminator::Call { func, .. } | Terminator::TailCall { func, .. } => {
                    return Err(format!("the call to `{func}`"));
                }
                // Every `Assert` is a panic path, the overflow `Assert` behind a
                // `CheckedBinaryOp` pair included: reading past it would give a
                // body that panics a total image (E6-TG14-PANIC-EDGE-1).
                Terminator::Assert { msg, .. } => {
                    return Err(format!("an `Assert` (`{msg:?}`), a panic path"));
                }
                Terminator::Unreachable => {
                    return Err("an `Unreachable` terminator".to_owned());
                }
                Terminator::Drop { .. } => return Err("a `Drop`".to_owned()),
                Terminator::Resume => return Err("an unwind `Resume`".to_owned()),
                Terminator::Opaque { kind, .. } => {
                    return Err(format!("a terminator the extractor does not model (`{kind}`)"));
                }
            }
        }
    }

    /// Run the arms of a `switchInt` on `d` to `join` and merge them.
    fn decision(
        &mut self,
        d: &Sym,
        targets: &[(u128, BlockId)],
        otherwise: BlockId,
        join: Option<BlockId>,
        env: BTreeMap<usize, Sym>,
    ) -> Result<BTreeMap<usize, Sym>, String> {
        if d.ty != Ty::Bool {
            return self.match_decision(d, targets, otherwise, join, env);
        }
        let (mut on_false, mut on_true) = (None, None);
        for (value, target) in targets {
            let slot = match value {
                0 => &mut on_false,
                1 => &mut on_true,
                v => return Err(format!("a `switchInt` on a `bool` against the value {v}")),
            };
            if slot.replace(*target).is_some() {
                return Err("a `switchInt` that lists one value twice".to_owned());
            }
        }
        let then = self.region(on_true.unwrap_or(otherwise), join, env.clone())?;
        let els = self.region(on_false.unwrap_or(otherwise), join, env)?;
        merge(&then, &els, |t, e| E6Term::ite(d.term.clone(), t, e))
    }

    /// Trust (E6 expansion I4′): a multi-target `switchInt` on an INTEGER
    /// parameter — a `match` with literal arms, or `matches!` — read as the
    /// chain `if d == v₁ { arm₁ } else if d == v₂ { arm₂ } … else { otherwise }`
    /// in the switch's target order (the values are distinct, so the order
    /// does not change the function).
    ///
    /// `switchInt` values are BIT PATTERNS at the discriminant's width (`-1i8`
    /// arrives as `255`, review H7), so each value is read back at the
    /// discriminant's own type through [`Ty::decode_switch_label`], the one
    /// definition of that decode: an unsigned value must be below `2^w`, and
    /// a signed one at or above `2^(w-1)` is the negative `v - 2^w`. The
    /// discriminant must be a PARAMETER (a computed one is a bit operation or
    /// arithmetic, outside the fragment), of an unsigned or signed carrier (a
    /// `char` has none here).
    fn match_decision(
        &mut self,
        d: &Sym,
        targets: &[(u128, BlockId)],
        otherwise: BlockId,
        join: Option<BlockId>,
        env: BTreeMap<usize, Sym>,
    ) -> Result<BTreeMap<usize, Sym>, String> {
        let carrier = E6Carrier::of(&d.ty).ok_or_else(|| {
            format!("a `switchInt` on `{}`, which has no carrier here", super::ty_spelling(&d.ty))
        })?;
        if !matches!(d.term, E6Term::Param(_)) {
            return Err(format!(
                "a `switchInt` on a computed `{}` (a `match` reads a parameter)",
                super::ty_spelling(&d.ty)
            ));
        }
        let mut seen = std::collections::BTreeSet::new();
        let mut arms = Vec::with_capacity(targets.len());
        for (value, target) in targets {
            if !seen.insert(*value) {
                return Err("a `switchInt` that lists one value twice".to_owned());
            }
            // The ONE definition of the label decode (`Ty::decode_switch_label`,
            // over `decode_raw_two_complement`): `None` for a pattern with bits
            // above the width, and fail closed on it.
            let literal = d.ty.decode_switch_label(*value).ok_or_else(|| {
                format!("the `switchInt` value {value}, outside `{}`", super::ty_spelling(&d.ty))
            })?;
            arms.push((literal, self.region(*target, join, env.clone())?));
        }
        let mut acc = self.region(otherwise, join, env)?;
        for (literal, arm) in arms.into_iter().rev() {
            let test = E6Term::Cmp {
                op: E6Cmp::Eq,
                carrier,
                left: Box::new(d.term.clone()),
                right: Box::new(E6Term::Int(literal)),
            };
            acc = merge(&arm, &acc, |t, e| E6Term::ite(test.clone(), t, e))?;
        }
        Ok(acc)
    }
}

/// The locals two arms both define, a local they disagree on joined by
/// `join(then, else)`; a local only one arm defines is dropped (a later read
/// of it fails closed as a read before a write).
fn merge(
    then: &BTreeMap<usize, Sym>,
    els: &BTreeMap<usize, Sym>,
    join: impl Fn(E6Term, E6Term) -> E6Term,
) -> Result<BTreeMap<usize, Sym>, String> {
    let mut out = BTreeMap::new();
    for (local, t) in then {
        let Some(e) = els.get(local) else { continue };
        if t.ty != e.ty {
            return Err(format!("`_{local}` holds different types on two arms"));
        }
        let term =
            if t.term == e.term { t.term.clone() } else { join(t.term.clone(), e.term.clone()) };
        if term.size() > MAX_TERM_SIZE {
            return Err(format!("a term larger than {MAX_TERM_SIZE} nodes"));
        }
        out.insert(*local, Sym { term, ty: t.ty.clone() });
    }
    Ok(out)
}

/// `n <= 512` is enforced in [`PostDominators::of`], so `n + 1 <= 513` bits
/// fits in 9 `u64` words (576 bits).
const PDOM_WORDS: usize = 9;
type PdomBitSet = [u64; PDOM_WORDS];

#[inline]
fn pdom_set(set: &mut PdomBitSet, idx: usize) {
    set[idx >> 6] |= 1u64 << (idx & 63);
}

/// The post-dominator sets of a function's CFG, over its blocks plus a
/// virtual EXIT that every `Return` flows to. Only computed for an ACYCLIC
/// graph (checked first); a block with no path to EXIT (an `Unreachable`, a
/// call without a return edge) post-dominates vacuously and is refused when
/// the walk reaches it.
struct PostDominators {
    ids: Vec<BlockId>,
    /// `sets[i]` bit `j`: block `j` post-dominates block `i` (index `n` is EXIT).
    sets: Vec<PdomBitSet>,
}

impl PostDominators {
    fn of(func: &VerifiableFunction) -> Result<Self, String> {
        let blocks = &func.body.blocks;
        let n = blocks.len();
        if n > 512 {
            return Err(format!("a body of {n} blocks"));
        }
        let ids: Vec<BlockId> = blocks.iter().map(|b| b.id).collect();
        let index = |id: BlockId| {
            if ids.get(id.0) == Some(&id) {
                Some(id.0)
            } else {
                ids.iter().position(|b| *b == id)
            }
        };
        let mut succ: Vec<Vec<usize>> = Vec::with_capacity(n);
        for b in blocks {
            let next: Vec<usize> = match &b.terminator {
                Terminator::Return => vec![n],
                Terminator::Assert { target: t, .. } | Terminator::Call { target: Some(t), .. } => {
                    vec![index(*t).ok_or("a call to a missing block")?]
                }
                Terminator::Goto(t) => vec![index(*t).ok_or("a jump to a missing block")?],
                Terminator::SwitchInt { targets, otherwise, .. } => targets
                    .iter()
                    .map(|(_, t)| *t)
                    .chain(std::iter::once(*otherwise))
                    .map(|t| index(t).ok_or("a jump to a missing block"))
                    .collect::<Result<_, _>>()?,
                _ => Vec::new(),
            };
            succ.push(next);
        }
        // Acyclic first: a back edge reachable from the entry is a loop.
        let mut state = vec![0u8; n];
        let mut stack: Vec<(usize, usize)> = if n > 0 { vec![(0, 0)] } else { Vec::new() };
        if n > 0 {
            state[0] = 1;
        }
        while let Some(top) = stack.last_mut() {
            let (at, k) = *top;
            if let Some(&to) = succ[at].get(k) {
                top.1 += 1;
                if to == n {
                    continue;
                }
                match state[to] {
                    0 => {
                        state[to] = 1;
                        stack.push((to, 0));
                    }
                    1 => return Err(format!("a loop (the back edge into bb{})", ids[to].0)),
                    _ => {}
                }
            } else {
                state[at] = 2;
                stack.pop();
            }
        }
        // pdom(EXIT) = {EXIT}; pdom(b) = {b} ∪ ⋂ pdom(succ(b)), from ALL.
        let total = n + 1;
        let words_used = total.div_ceil(64);
        let mut all_mask = [0u64; PDOM_WORDS];
        for (w, slot) in all_mask.iter_mut().enumerate().take(words_used) {
            *slot = if w + 1 < words_used || (total & 63) == 0 {
                u64::MAX
            } else {
                (1u64 << (total & 63)) - 1
            };
        }
        let mut sets = vec![all_mask; total];
        sets[n] = [0u64; PDOM_WORDS];
        pdom_set(&mut sets[n], n);
        let mut changed = true;
        while changed {
            changed = false;
            for b in (0..n).rev() {
                let mut next = all_mask;
                for &s in &succ[b] {
                    let s_set = &sets[s];
                    for w in 0..words_used {
                        next[w] &= s_set[w];
                    }
                }
                pdom_set(&mut next, b);
                if next[..words_used] != sets[b][..words_used] {
                    sets[b] = next;
                    changed = true;
                }
            }
        }
        Ok(PostDominators { ids, sets })
    }

    /// The immediate post-dominator of `block`: `Some(block)` for a real
    /// block, `None` for the EXIT.
    fn immediate(&self, block: BlockId) -> Result<Option<BlockId>, String> {
        let n = self.ids.len();
        let i = if self.ids.get(block.0) == Some(&block) {
            block.0
        } else {
            self.ids.iter().position(|b| *b == block).ok_or("a missing block")?
        };
        let mut strict_i = self.sets[i];
        strict_i[i >> 6] &= !(1u64 << (i & 63));
        // The strict post-dominators form a chain; the immediate one is the
        // member whose own post-dominator set is exactly that chain.
        for (w, &word) in strict_i.iter().enumerate() {
            let mut bits = word;
            while bits != 0 {
                let bit = bits.trailing_zeros() as usize;
                let j = (w << 6) + bit;
                if self.sets[j] == strict_i {
                    return Ok((j < n).then(|| self.ids[j]));
                }
                bits &= bits - 1;
            }
        }
        Err(format!("bb{} has no immediate post-dominator", block.0))
    }
}

/// Read `func` with the E6-only TREE reader: its normalized term, or the
/// first thing the reader refused (a sentence for the refusal a user sees).
///
/// Consulted by the E6 importer only after `recognize_admissible_body`, island
/// forwarding and the single-node I1′ reading all answered `None` (see
/// [`super::read_e6_body`]). Fails closed on everything outside the module
/// docs' vocabulary.
///
/// # Errors
///
/// The construct the reader stopped at, spelled for a diagnostic.
fn read_e6_tree_and_defaults(
    func: &VerifiableFunction,
) -> Result<(E6Term, BTreeMap<usize, usize>), String> {
    let expanded = func.with_tail_calls_expanded();
    let func = expanded.as_ref();
    // Trust (E6 expansion I4′): a VALUE decision tree may return any scalar
    // carrier the comparisons have (`bool`, `uN`, `iN`).
    if E6Carrier::of(&func.body.return_ty).is_none() {
        return Err(format!(
            "a `{}`-valued body (the tree reader reads `bool`, `uN` and `iN` values)",
            super::ty_spelling(&func.body.return_ty)
        ));
    }
    let Some(entry) = func.body.blocks.first() else {
        return Err("an empty body".to_owned());
    };
    let post_dominators = PostDominators::of(func)?;
    let mut reader = Reader { func, post_dominators, visits: 0, option_defaults: BTreeMap::new() };
    let mut env = reader.region(entry.id, None, BTreeMap::new())?;
    let result =
        env.remove(&0).ok_or_else(|| "a path to `Return` that never writes `_0`".to_owned())?;
    if result.ty != func.body.return_ty {
        return Err("a returned value whose type is not the declared return type".to_owned());
    }
    let term = normalize_bool(result.term);
    // A body whose value no parameter reaches (`true`, `if c { 1 } else { 1 }`)
    // is a CONSTANT, which is the frozen constant shape's scope, not a tree's.
    if !term.mentions_param() {
        return Err("a constant body (no parameter reaches its value)".to_owned());
    }
    Ok((term, reader.option_defaults))
}

/// Read a scalar E6 tree. See this module's vocabulary and refusal rules.
///
/// # Errors
/// The first construct outside the reader's fragment.
pub fn read_e6_tree(func: &VerifiableFunction) -> Result<E6Term, String> {
    read_e6_tree_and_defaults(func).map(|(term, _)| term)
}

/// Unreachable defaults excluded by the complete typed checked-Option
/// symbolic read: the authenticated value has exactly tags 0/1, both arms
/// exist, and every incoming edge is such a switch's otherwise edge.
/// No other Unreachable block or effectful default gains admission.
#[must_use]
pub fn checked_option_impossible_defaults(
    func: &VerifiableFunction,
) -> std::collections::HashSet<BlockId> {
    let empty = std::collections::HashSet::new();
    if !func.body.blocks.iter().any(|bb| matches!(bb.terminator, Terminator::Unreachable))
        || func.body.blocks.iter().enumerate().any(|(i, bb)| bb.id.0 != i)
        || func.body.locals.iter().enumerate().any(|(i, local)| local.index != i)
    {
        return empty;
    }
    let Ok((_, owners)) = read_e6_tree_and_defaults(func) else {
        return empty;
    };
    owners.values().copied().map(BlockId).filter(|default| {
        func.body.blocks.iter().all(|bb| {
            let incoming = crate::structural_termination::terminator_has_successor(&bb.terminator, *default);
            !incoming || (owners.get(&bb.id.0) == Some(&default.0)
                && matches!(&bb.terminator, Terminator::SwitchInt { targets, otherwise, .. }
                    if otherwise == default && !targets.iter().any(|(_, target)| target == default)))
        })
    }).collect()
}

#[cfg(test)]
mod tests;
