// trust-js-autoform: the TrustJS M4 strict-mode arithmetic FLOOR.
//
// SCOPE — read this before anything else. This crate is the DETERMINISTIC,
// correct-by-construction strict-mode baseline floor of §4 of
// docs/design/2026-07-20-trust-native-javascript-engine.md, for ONE tiny
// fragment. It is emphatically NOT the M4 autoformalization tier:
//   * NO LLM in the loop, NO intent inference (§5), NO proposal scaffold.
//   * NO native install / validation certificate, NO guard elimination.
//   * NO general fragment — the ONLY thing lowered is a top-level
//         function f(p0, p1, ...) { return <arith-expr>; }
//     whose <arith-expr> uses ONLY parameter identifiers, JS numeric literals
//     (decimal f64, never BigInt), the binary operators `+ - * / %`, unary
//     `-` and unary `+`, and parentheses. EVERYTHING else REFUSES.
//
// A refusal is the faithful-tier fallback (§4 object 4): always sound. A WRONG
// lowering is a hard failure. So when unsure we REFUSE, and even a lowering we
// believe correct is emitted ONLY after every sample in a fixed edge-case
// corpus is checked bit-for-bit against the independent semantics oracle
// (trust-js-interp — §4 object 1). The Rust artifact is claimed equivalent to
// the JS *only where independently checked equal*; that check is the honesty
// core (the delta ledger, §4 object 3).
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use trust_js_interp::{InterpOutcome, evaluate_case_opts};
use trust_js_parse::ast::{Arg, DeclKind, Expr, ForHead, Func, Pat, PropKey, Stmt};
use trust_js_parse::{ParseOutcome, parse_script};
use trust_js_trace::{Completion, ProjectedValue};
use trust_js_value::{numeric_literal_mv, projection_number_repr};

/// The formal artifact (§4 object 2): a small, total, typed IR. This is the
/// **numeric** (Num, IEEE-754 `f64`) half; [`BoolIr`] is the **boolean** half.
/// Every value in the fragment types to exactly one of {Num, Bool}, and the
/// WHOLE return expression must type to Num (a bare-boolean-result function is
/// out of the numeric-result fragment — refused). JS Number arithmetic *is*
/// `f64` arithmetic, so each arithmetic node maps to one Rust `f64` operation.
/// `Param(i)` is the `i`-th formal parameter (0-based); `Lit` a JS numeric
/// literal's mathematical value; unary `+` on a number is the identity
/// (`ToNumber(number) == number`, bit-for-bit) and is therefore *folded away* at
/// lowering time — there is no `Pos` node. `Cond` is a numeric-result
/// conditional `c ? t : e` with a boolean test and numeric branches; it renders
/// to a Rust `if <test> { <cons> } else { <alt> }` expression.
///
/// `Local(i)` is a reference to the value held in **slot `i`** by a `const`/`let`
/// binding. Slots are a single ordered vector: slots `0..arity` are the formal
/// parameters (always Num), and slots `arity..` are the locals in declaration
/// order. A parameter reference lowers to `Param(i)` (renders `p{i}`); a
/// numeric-local reference lowers to `Local(i)` (renders `l{i}`) — the two share
/// one runtime slot vector and differ only in how they render.
///
/// None of these mappings is *assumed* correct: each lowering is proven bit-for-
/// bit against the interp oracle over the edge-case corpus, or it refuses.
#[derive(Debug, Clone, PartialEq)]
pub enum ArithIr {
    Param(usize),
    /// A reference to a NUMERIC (`f64`) local binding in absolute slot `i`
    /// (`i >= arity`). See the type-level doc for the slot model.
    Local(usize),
    Lit(f64),
    Neg(Box<ArithIr>),
    Add(Box<ArithIr>, Box<ArithIr>),
    Sub(Box<ArithIr>, Box<ArithIr>),
    Mul(Box<ArithIr>, Box<ArithIr>),
    Div(Box<ArithIr>, Box<ArithIr>),
    Rem(Box<ArithIr>, Box<ArithIr>),
    /// JS bitwise `a | b`: `ToInt32(a) | ToInt32(b)` (as `i32`), the signed `i32`
    /// widened back to a Number. Unlike a transcendental (`Math.pow`), `ToInt32`
    /// and integer `|/&/^` are EXACT integer functions — a precise mathematical
    /// definition every correct implementation (V8, the interp, Rust) computes
    /// bit-identically — so the same-oracle fidelity check is sound, not a
    /// tautology. Renders `((__js_to_int32(a) | __js_to_int32(b)) as f64)`.
    BitOr(Box<ArithIr>, Box<ArithIr>),
    /// JS bitwise `a & b`: `ToInt32(a) & ToInt32(b)` (`i32`) → Number.
    BitAnd(Box<ArithIr>, Box<ArithIr>),
    /// JS bitwise `a ^ b`: `ToInt32(a) ^ ToInt32(b)` (`i32`) → Number.
    BitXor(Box<ArithIr>, Box<ArithIr>),
    /// JS `a << b`: `ToInt32(a) << (ToUint32(b) & 31)` (`i32`, wrapping) → Number.
    Shl(Box<ArithIr>, Box<ArithIr>),
    /// JS `a >> b`: `ToInt32(a) >> (ToUint32(b) & 31)` — ARITHMETIC (sign-
    /// propagating) shift of the signed `i32` → Number. `-1 >> 0 === -1`.
    Shr(Box<ArithIr>, Box<ArithIr>),
    /// JS `a >>> b`: `ToUint32(a) >>> (ToUint32(b) & 31)` — LOGICAL (zero-fill)
    /// shift of the UNSIGNED `u32` → Number. The result is unsigned, so
    /// `-1 >>> 0 === 4294967295` (a `u32 < 2^32 < 2^53`, an exact `f64`), NOT `-1`.
    UShr(Box<ArithIr>, Box<ArithIr>),
    /// JS bitwise `~a`: `!ToInt32(a)` (`i32`) → Number. `~0 === -1`, `~5 === -6`.
    BitNot(Box<ArithIr>),
    /// `if <test> { <cons> } else { <alt> }` — a numeric-result conditional
    /// (`c ? t : e` where `c` is boolean and both branches are numeric).
    Cond {
        test: Box<BoolIr>,
        cons: Box<ArithIr>,
        alt: Box<ArithIr>,
    },
    /// A NON-RECURSIVE call to an EARLIER-declared top-level function, identified
    /// by its absolute index in the module's function table (`callee`), with one
    /// numeric argument IR per callee parameter (arg count == callee arity, each
    /// arg Num). Every function returns Num, so a call is a numeric node. The call
    /// graph is ACYCLIC by declaration order — a function may call only functions
    /// declared strictly before it — so evaluation always terminates. Renders
    /// `name(a0, a1, ...)`.
    Call {
        callee: usize,
        args: Vec<ArithIr>,
    },
    /// A call to an allow-listed `Math.<name>(args)` builtin (`op` the builtin,
    /// `args` one numeric IR per argument — 1 for a unary op, 2 for a binary one;
    /// the arity is enforced at lowering). Every builtin is a numeric node (Num
    /// result). This is the M4 **propose-validate-refuse** surface: each op's Rust
    /// lowering is a PROPOSAL (a direct `f64` method for `abs/floor/ceil/trunc/
    /// sqrt`, or a JS-semantics `__js_math_*` helper for `sign/round/min/max`),
    /// which the delta ledger then VALIDATES bit-for-bit against the interp oracle
    /// over the corpus — a divergence on ANY sample refuses the lowering. The
    /// proposal is untrusted; the ledger is the authority. See [`MathOp`].
    MathCall {
        op: MathOp,
        args: Vec<ArithIr>,
    },
}

/// An allow-listed `Math.*` builtin. Every other `Math.<name>` (`Math.random` —
/// nondeterministic — `Math.hypot`, `Math.log`, trig, `Math.pow` and every other
/// TRANSCENDENTAL, `Math.PI` as a member, …) refuses. The SHIP rule is narrow: a
/// `Math` op is admitted ONLY if its Rust lowering is bit-identical to JS for ALL
/// inputs — which holds for the IEEE-correctly-rounded operations, NOT for
/// transcendentals. The unary ops `Abs`/`Floor`/`Ceil`/`Trunc`/`Sqrt` map DIRECTLY
/// to the same `f64` method the interp oracle calls, so they are bit-identical by
/// construction; `Sign`/`Round`/`Min`/`Max` are traps where a naive Rust map
/// diverges from JS (signed zero, NaN propagation, half-to-`+Inf`) but the exact
/// answer is still IEEE-determined, so each renders via a prepended `__js_math_*`
/// helper whose body mirrors the oracle EXACTLY. A transcendental like `Math.pow`
/// is REFUSED, never shipped: IEEE-754 does not mandate a correctly-rounded `pow`,
/// so `f64::powf` (platform libm) is not bit-identical to JS `Math.pow` (V8), and
/// an oracle-check against the interp — which computes `Math.pow` with the SAME
/// `f64::powf` — would be a TAUTOLOGY that validates nothing. Nothing is trusted:
/// the ledger proves every admitted op bit-for-bit against the oracle, or refuses.
///
/// Variant order is the canonical helper-emission order (derived `Ord`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum MathOp {
    /// `Math.abs` ⇒ `x.abs()`.
    Abs,
    /// `Math.floor` ⇒ `x.floor()`.
    Floor,
    /// `Math.ceil` ⇒ `x.ceil()`.
    Ceil,
    /// `Math.trunc` ⇒ `x.trunc()`.
    Trunc,
    /// `Math.sqrt` ⇒ `x.sqrt()` (IEEE-exact, correctly rounded).
    Sqrt,
    /// `Math.sign` ⇒ `__js_math_sign` (`±0`/`NaN` preserved, NOT `f64::signum`).
    Sign,
    /// `Math.round` ⇒ `__js_math_round` (ties toward `+Inf`, NOT `f64::round`).
    Round,
    /// `Math.min` (EXACTLY 2 args) ⇒ `__js_math_min` (NaN-propagating, `-0 < +0`).
    Min,
    /// `Math.max` (EXACTLY 2 args) ⇒ `__js_math_max` (NaN-propagating, `+0 > -0`).
    Max,
    // NOTE: `Math.pow` is deliberately NOT a variant. It is a TRANSCENDENTAL and is
    // REFUSED at lowering, never shipped: IEEE-754 does not mandate a correctly-
    // rounded `pow`, so `f64::powf` is not bit-identical to JS `Math.pow`, and an
    // oracle-check would be a tautology (the interp uses the same `f64::powf`). See
    // `lower_math_call`. (Adversarial audit finding, 2026-07-23.)
}

impl MathOp {
    /// The required argument count: 1 for a unary op, 2 for a binary one.
    fn arity(self) -> usize {
        match self {
            MathOp::Abs
            | MathOp::Floor
            | MathOp::Ceil
            | MathOp::Trunc
            | MathOp::Sqrt
            | MathOp::Sign
            | MathOp::Round => 1,
            MathOp::Min | MathOp::Max => 2,
        }
    }

    /// The Rust `f64` method for a DIRECT-map unary op (bit-identical to the
    /// oracle, which calls the same method), or `None` for a trap op that needs a
    /// JS-semantics helper.
    fn direct_method(self) -> Option<&'static str> {
        match self {
            MathOp::Abs => Some("abs"),
            MathOp::Floor => Some("floor"),
            MathOp::Ceil => Some("ceil"),
            MathOp::Trunc => Some("trunc"),
            MathOp::Sqrt => Some("sqrt"),
            _ => None,
        }
    }

    /// The prepended `__js_math_*` helper name for a trap op, or `None` for a
    /// direct-map op.
    fn helper_name(self) -> Option<&'static str> {
        match self {
            MathOp::Sign => Some("__js_math_sign"),
            MathOp::Round => Some("__js_math_round"),
            MathOp::Min => Some("__js_math_min"),
            MathOp::Max => Some("__js_math_max"),
            _ => None,
        }
    }

    /// The full standalone Rust source of this op's helper (trap ops only; `None`
    /// for a direct-map op). `eval_math` mirrors each body EXACTLY, and
    /// `compile_check` proves render ≡ eval with the real rustc over the corpus.
    fn helper_source(self) -> Option<&'static str> {
        match self {
            MathOp::Sign => Some(HELPER_SIGN),
            MathOp::Round => Some(HELPER_ROUND),
            MathOp::Min => Some(HELPER_MIN),
            MathOp::Max => Some(HELPER_MAX),
            _ => None,
        }
    }
}

// The standalone Rust source of each trap-op helper. These are prepended to the
// rendered module (only the ones actually used) and their bodies mirror the
// interp oracle EXACTLY (`trust-js-interp` `js_math_round` / the Math.sign /
// Math.min|max reductions). `eval_math`'s `js_math_*` fns are the same logic, and
// `compile_check` proves render ≡ eval bit-for-bit with rustc. (No `pow` helper:
// `Math.pow` is a transcendental and refuses — see the `MathOp` doc.)
const HELPER_SIGN: &str = "fn __js_math_sign(x: f64) -> f64 { if x.is_nan() || x == 0.0 { x } else if x < 0.0 { -1.0 } else { 1.0 } }";
const HELPER_ROUND: &str = "fn __js_math_round(x: f64) -> f64 { if !x.is_finite() || x.trunc() == x { x } else if x > 0.0 && x < 0.5 { 0.0 } else if x < 0.0 && x >= -0.5 { -0.0 } else { let f = x.floor(); if x - f >= 0.5 { f + 1.0 } else { f } } }";
const HELPER_MIN: &str = "fn __js_math_min(a: f64, b: f64) -> f64 { if a.is_nan() || b.is_nan() { f64::NAN } else if a < b { a } else if b < a { b } else if a.is_sign_negative() { a } else { b } }";
const HELPER_MAX: &str = "fn __js_math_max(a: f64, b: f64) -> f64 { if a.is_nan() || b.is_nan() { f64::NAN } else if a > b { a } else if b > a { b } else if a.is_sign_positive() { a } else { b } }";

// The standalone Rust source of the ECMA-262 `ToUint32` (7.1.7) / `ToInt32`
// (7.1.6) helpers, prepended to a rendered module that uses any JS bitwise / shift
// operator (only the ones actually needed, and `__js_to_int32` always drags in
// `__js_to_uint32`, its dependency). Their bodies mirror the interp oracle EXACTLY
// (`trust-js-value::{to_uint32, to_int32}`), and `js_to_uint32`/`js_to_int32` below
// are the SAME logic, so `compile_check` proves render ≡ eval bit-for-bit with the
// real rustc. These are EXACT integer functions (a precise modular definition every
// correct implementation computes bit-identically), so — unlike a transcendental —
// shipping them is sound, and the same-oracle fidelity check validates rather than
// tautologizes. `ToUint32(x)`: NaN/±0/±Infinity ⇒ 0; else reduce `trunc(x)` mod
// 2^32 into `[0, 2^32)` (via exact `fmod`, then negate for a negative source).
// `ToInt32(x)` = `ToUint32(x)` reinterpreted as a signed `i32` (2's complement).
const HELPER_TO_UINT32: &str = "fn __js_to_uint32(x: f64) -> u32 { if !x.is_finite() || x == 0.0 { 0 } else { let t = x.trunc(); let m = t.abs() % 4294967296.0; let u = m as u32; if t < 0.0 && u != 0 { u32::MAX - u + 1 } else { u } } }";
const HELPER_TO_INT32: &str = "fn __js_to_int32(x: f64) -> i32 { __js_to_uint32(x) as i32 }";

/// The **boolean** half of the IR: expressions that type to Bool. A `Bool`
/// value can only arise from a numeric comparison, a boolean equality, the
/// logical operators, or a boolean-branched conditional — never from a bare
/// literal or parameter (params are Num; boolean literals are refused). Boolean
/// values may feed a conditional's test, the logical operators, `!`, or a
/// boolean equality, but the WHOLE return must be Num, so a top-level `BoolIr`
/// is refused.
#[derive(Debug, Clone, PartialEq)]
pub enum BoolIr {
    /// A reference to a BOOLEAN local binding in absolute slot `i` (`i >= arity`).
    /// Only locals can be boolean (parameters are always Num), so there is no
    /// boolean `Param`. Renders `l{i}`.
    Local(usize),
    /// A comparison of two NUMERIC operands, yielding Bool. JS relational /
    /// strict-equality on two numbers is exactly the corresponding Rust `f64`
    /// comparison (`NaN` unordered, `-0 == +0`) — proven per sample by the
    /// ledger, or refused.
    Cmp { op: CmpOp, left: Box<ArithIr>, right: Box<ArithIr> },
    /// Equality of two BOOLEAN operands (`===`/`==`/`!==`/`!=` where both sides
    /// are booleans). Same-type `==`/`===` on booleans does no coercion, so it
    /// is exactly Rust `bool == bool` / `bool != bool`.
    BoolEq { op: BoolEqOp, left: Box<BoolIr>, right: Box<BoolIr> },
    /// `&&` on two booleans (short-circuit). Both operands are booleans, so the
    /// JS "returns an operand value" rule yields a genuine boolean equal to Rust
    /// `bool && bool`.
    And(Box<BoolIr>, Box<BoolIr>),
    /// `||` on two booleans (short-circuit), analogous to [`BoolIr::And`].
    Or(Box<BoolIr>, Box<BoolIr>),
    /// Logical `!` of a boolean.
    Not(Box<BoolIr>),
    /// A boolean-result conditional `c ? t : e` where both branches are boolean.
    Cond { test: Box<BoolIr>, cons: Box<BoolIr>, alt: Box<BoolIr> },
}

/// A numeric comparison operator (Num × Num → Bool).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CmpOp {
    /// `<`
    Lt,
    /// `<=`
    Le,
    /// `>`
    Gt,
    /// `>=`
    Ge,
    /// `===` / `==` on two numbers (Rust `f64 ==`: `NaN != NaN`, `-0 == +0`).
    NumEq,
    /// `!==` / `!=` on two numbers (Rust `f64 !=`).
    NumNe,
}

/// A boolean equality operator (Bool × Bool → Bool).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BoolEqOp {
    /// `===` / `==` on two booleans (Rust `bool ==`).
    Eq,
    /// `!==` / `!=` on two booleans (Rust `bool !=`).
    Ne,
}

/// The delta ledger (§4 object 3) for one lowering: how many edge-case samples
/// were checked bit-for-bit against the interp oracle, whether all agreed, and
/// the first disagreement if any. A `VerifiedLowering` only ever carries a
/// ledger with `all_equal == true` and `first_divergence == None`; a divergence
/// is surfaced as a `Refusal` and nothing is emitted.
#[derive(Debug, Clone, PartialEq)]
pub struct DeltaLedger {
    pub samples_checked: usize,
    pub all_equal: bool,
    pub first_divergence: Option<Divergence>,
}

/// One checked disagreement between the interp oracle and `eval_ir`.
#[derive(Debug, Clone, PartialEq)]
pub struct Divergence {
    /// The input tuple (one f64 per formal parameter).
    pub input: Vec<f64>,
    /// The oracle (JS) result, in canonical projection form (`-0`, `NaN`, ...).
    pub js: String,
    /// The `eval_ir` (Rust) result, same projection form.
    pub rust: String,
    /// Raw bit patterns, for the record.
    pub js_bits: u64,
    pub rust_bits: u64,
}

/// One lowered top-level function in a module's function table. `name` is its JS
/// name (a distinct top-level `function`), `arity` its parameter count, `bindings`
/// its `const`/`let` locals in declaration order (empty for a pure `return`-only
/// function), and `ret_ir` its final **numeric** return expression. `ret_ir` (and
/// any binding initializer) may reference parameters (`Param`), earlier locals
/// (`Local`/`BoolIr::Local`), and — via [`ArithIr::Call`] — functions declared
/// strictly earlier in the same module (by absolute index into the table).
#[derive(Debug, Clone, PartialEq)]
pub struct LoweredFn {
    pub name: String,
    pub arity: usize,
    pub bindings: Vec<Binding>,
    pub ret_ir: ArithIr,
}

/// A VALID, fidelity-checked lowering of a WHOLE module (one or more top-level
/// functions): the inspectable Rust artifact for the whole module, the ENTRY
/// function's IR, and the ledger proving bit-for-bit agreement with the oracle on
/// the corpus (the ENTRY function checked against the JS oracle).
///
/// `functions` is the module's function table in declaration order; `entry` is
/// the index of the ENTRY function (always the LAST-declared, `functions.len() -
/// 1`) — earlier functions are non-recursive helpers. `rust_source` renders ALL
/// functions (helpers first, then entry, matching declaration order so earlier
/// `fn`s are in scope). For backward compatibility with the single-function floor,
/// `bindings` and `ir` mirror the ENTRY function's `bindings` / `ret_ir` exactly
/// (a single-function source is the degenerate 1-function module — `functions` has
/// one element, `entry == 0`, and `rust_source` is byte-identical to the floor).
/// Evaluate the whole module with [`eval_module`].
#[derive(Debug, Clone, PartialEq)]
pub struct VerifiedLowering {
    pub rust_source: String,
    pub bindings: Vec<Binding>,
    pub ir: ArithIr,
    pub ledger: DeltaLedger,
    pub functions: Vec<LoweredFn>,
    pub entry: usize,
    /// The array-fold ENTRY (increment 6), if this module reduces a numeric array
    /// via a single for-of. `None` for a scalar module. When `Some`, `functions`
    /// holds only the scalar helpers (the fold is the entry, evaluated with
    /// [`eval_fold`] / rendered by [`render_fold_module`]), `entry == functions.len()`
    /// (a sentinel past the helpers), and `bindings`/`ir` mirror the fold's
    /// pre-bindings / return for inspection only.
    pub fold: Option<FoldFn>,
}

/// One lowered numeric ARRAY-FOLD function — the sole for-of reduction shape (M4
/// floor increment 6): `function f(ARR, s0, …) { <binding>* let ACC = <init>;
/// for (const X of ARR) { ACC = <step>; } return <ret>; }`. `ARR` is the implicit
/// first parameter (slot 0, rendered `arr: &[f64]`, referenced ONLY as the for-of
/// iterable); `s0…` are trailing scalar `Num` params (slots `1..=scalar_arity`,
/// rendered `p1…`). `pre_bindings` are SSA locals before the accumulator; the
/// accumulator (`acc_slot`, initialized by `acc_init`) is the one mutable local,
/// reduced left-to-right by `step` (a numeric expr over the accumulator, the loop
/// variable `loop_var_slot`, the scalars, and the pre-bindings); `ret` is the
/// numeric return over the accumulator, scalars, and pre-bindings (NOT the loop
/// variable, which is out of scope after the loop). `step`/`acc_init`/`ret` may
/// also CALL a strictly-earlier scalar helper (via [`ArithIr::Call`]). Every
/// mapping is proven bit-for-bit against the interp oracle over the array corpus
/// by [`eval_fold`], or the whole lowering refuses. The reduction terminates on
/// any finite array.
#[derive(Debug, Clone, PartialEq)]
pub struct FoldFn {
    pub name: String,
    pub scalar_arity: usize,
    pub pre_bindings: Vec<Binding>,
    pub acc_slot: usize,
    pub acc_init: ArithIr,
    pub loop_var_slot: usize,
    pub step: ArithIr,
    pub ret: ArithIr,
}

/// One `const`/`let` local binding. `slot` is its absolute slot index
/// (`arity + k` for the `k`-th local), and `init` is the typed initializer IR —
/// `Num(ArithIr)` for a numeric local, `Bool(BoolIr)` for a boolean local. The
/// binding's static type is its initializer's type. Both `const` and `let`
/// lower identically here (each name is bound exactly once — SSA), so the JS
/// keyword is not retained; the Rust artifact always emits an immutable `let`.
#[derive(Debug, Clone, PartialEq)]
pub struct Binding {
    pub slot: usize,
    pub init: TypedIr,
}

/// A lowered expression tagged with its static type ({Num, Bool}). It is the
/// type of a binding initializer and the internal result of `lower_typed`.
#[derive(Debug, Clone, PartialEq)]
pub enum TypedIr {
    Num(ArithIr),
    Bool(BoolIr),
}

/// The static type of a subexpression / binding: exactly one of {Num, Bool} —
/// plus the fold-only `Array` marker for the single array parameter of an
/// array-fold function (increment 6). `Array` is NOT a value type: it occupies a
/// slot but resolves to no expression IR, so any reference outside the for-of
/// iterable refuses as a free identifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Ty {
    Num,
    Bool,
    /// A number-ARRAY parameter (the fold's iterable). Only a fold function's
    /// first parameter has this type; see [`Scope::reference`].
    Array,
}

/// A runtime slot value during [`eval_func`]: a slot holds either a JS Number
/// (`f64`) or a boolean, matching its binding's static type. Total by
/// construction — a type-confused read (impossible after the checker) degrades
/// to `NaN` / `false`, which would surface as a divergence, never a panic.
#[derive(Debug, Clone, Copy)]
enum Slot {
    Num(f64),
    Bool(bool),
}

/// Why a source was refused. Every arm emits NOTHING (the faithful-tier
/// fallback). Refusal is always sound; a wrong lowering never is.
#[derive(Debug, Clone, PartialEq)]
pub enum Refusal {
    /// The source did not parse as a Script (or the parser soundly refused it).
    ParseError { reason: String },
    /// The program is not EXACTLY one top-level function declaration.
    NotSingleFunction { reason: String },
    /// A formal parameter is not a plain identifier (default / rest /
    /// destructuring / duplicate), or the function is async / a generator.
    UnsupportedParameter { reason: String },
    /// The body is not `<const|let binding>* return <expr>;`: no trailing
    /// `return`, a `return;` with no value, or an empty body.
    NotSingleArithReturn { reason: String },
    /// A statement before the final `return` is not a supported `const`/`let`
    /// binding: a bare expression / reassignment (`x = …`, `x++`), an `if` /
    /// loop / block / `switch` / `try`, or an early / duplicate `return`. This
    /// fragment is straight-line and SSA-only — each name is bound exactly once
    /// and never reassigned.
    UnsupportedStatement { reason: String },
    /// A `const`/`let`-shaped declaration outside the supported single, plain,
    /// initialized identifier binding: `var` / `using`, a destructuring pattern,
    /// multiple declarators (`const a=1, b=2`), or a missing initializer.
    UnsupportedBinding { reason: String },
    /// A binding name that redeclares / shadows a parameter or an already-declared
    /// local. (Usually the parser rejects this first as a duplicate lexical
    /// declaration; this is the checker's own fail-closed guard.)
    Redeclaration { name: String },
    /// The return expression uses a construct outside the fragment.
    UnsupportedConstruct { construct: String },
    /// A call whose callee is not an EARLIER-declared top-level function: a call
    /// to the current function itself or a later-declared one (RECURSION — direct,
    /// forward, or a mutual-recursion cycle), a call to an undeclared name, or a
    /// call to a name bound as a parameter / local (only earlier top-level
    /// functions are callable). Enforced simply: a function may only call functions
    /// declared strictly before it, so the call graph is acyclic and terminating.
    UnknownCallee { name: String },
    /// A call whose argument count does not equal the callee's arity.
    CallArityMismatch { name: String, expected: usize, found: usize },
    /// A static type error inside the fragment ({Num, Bool}): an operand's type
    /// did not match what the operator requires — e.g. `(a>0)+1` (Bool where Num
    /// is required), a non-boolean `?:` condition, mismatched `?:` branch types,
    /// or a mixed `Num == Bool`. We REFUSE — the fragment never coerces.
    TypeError { reason: String },
    /// The whole return expression types to Bool, not Num. Only numeric-result
    /// functions are in the fragment; a bare-boolean return is refused.
    NonNumericResult { reason: String },
    /// The interp oracle could not return a JS number for a sample, so it could
    /// not be checked — we REFUSE rather than pass a sample unchecked (the
    /// oracle is never faked).
    OracleUnavailable { input: Vec<f64>, reason: String },
    /// A sample where `eval_ir` and the interp oracle disagree bit-for-bit — a
    /// caught delta. The lowering is rejected; nothing is emitted.
    FidelityDivergence { input: Vec<f64>, js: String, rust: String },
    /// The TypeScript source (input to [`lower_ts_and_verify`]) is NOT pure
    /// erasable TypeScript: the `trust-ts-strip` eraser refused to elide
    /// it to behaviourally-identical JavaScript (an `enum`, `namespace`/`module`,
    /// parameter property, decorator, `export =`/`import =`, or any other
    /// non-erasure construct). This is the M4-TS fragment boundary — we do NOT
    /// attempt the non-erasable `transform` lowering here. `reason` is the
    /// eraser's own fail-closed message. Nothing is emitted (sound fallback).
    NonErasableTypeScript { reason: String },
}

// ===========================================================================
// Public API
// ===========================================================================

/// Lower a strict pure-arithmetic JS function declaration to an inspectable
/// Rust artifact, and return it ONLY if every edge-case sample checks bit-for-
/// bit against the trust-js-interp oracle. Anything outside the fragment, or
/// any fidelity divergence, is a `Refusal` (nothing emitted).
///
/// # Errors
/// Returns a [`Refusal`] for any out-of-fragment construct, any parameter shape
/// we do not model, any oracle unavailability, or any checked divergence.
pub fn lower_and_verify(js: &str) -> Result<VerifiedLowering, Refusal> {
    match lower_module(js)? {
        Module::Scalar(functions) => {
            // The ENTRY is the LAST-declared function (arity = its params); earlier
            // functions are non-recursive helpers. A scalar module is never empty.
            let entry = functions.len() - 1;
            let ledger = check_fidelity_module(js, &functions, entry)?;
            let rust_source = render_module(&functions);
            // Mirror the entry function's bindings/ir for backward compatibility
            // with the single-function floor. Clone before moving `functions` in.
            let bindings = functions[entry].bindings.clone();
            let ir = functions[entry].ret_ir.clone();
            Ok(VerifiedLowering { rust_source, bindings, ir, ledger, functions, entry, fold: None })
        }
        Module::Fold { helpers, fold } => {
            // The ENTRY is the array-fold; `helpers` are the scalar helpers it may
            // call. The SAME oracle-checked ledger validates the fold bit-for-bit
            // over the array corpus (the oracle runs the real JS for-of).
            let ledger = check_fidelity_fold(js, &helpers, &fold)?;
            let rust_source = render_fold_module(&helpers, &fold);
            // Mirror the fold's pre-bindings / return for inspection only.
            let bindings = fold.pre_bindings.clone();
            let ir = fold.ret.clone();
            let entry = helpers.len();
            Ok(VerifiedLowering {
                rust_source,
                bindings,
                ir,
                ledger,
                functions: helpers,
                entry,
                fold: Some(fold),
            })
        }
    }
}

/// Lower an **erasable TypeScript** source to the same inspectable, fidelity-
/// checked Rust artifact as [`lower_and_verify`], by composing the
/// `trust-ts-strip` type-eraser with the existing JS lowering. This is the
/// "and TypeScript" front door of TrustJS (increment 7).
///
/// The pipeline is two stages, and its equivalence is **transitive**:
///
/// 1. `trust_ts_strip::strip(ts)` elides the TypeScript type syntax to
///    behaviourally-identical JavaScript (width-preserving blanking). This is the
///    ERASURE path only: a source that is NOT pure erasure — an `enum`,
///    `namespace`/`module`, parameter property, decorator, `export =`/`import =`,
///    or any other non-erasable construct — is a fail-closed
///    [`StripOutcome::Refused`], surfaced here as
///    [`Refusal::NonErasableTypeScript`]. We do NOT attempt the non-erasable
///    `transform` lowering (out of the M4-TS fragment for now). `TS ≡ stripped-JS`
///    is trust-ts-strip's faithfulness GATE, not a theorem: its corpus runs each
///    erasable file's stripped JS and the original `.ts` through Node and
///    requires byte-identical stdout, and requires a fail-closed refusal on each
///    non-erasable file. That is bounded differential evidence over a corpus, so
///    an erasure bug outside the corpus is not excluded by anything here.
/// 2. The resulting **stripped JS** is fed to [`lower_and_verify`] unchanged. The
///    interp oracle then runs the STRIPPED JS (the interp is a JS interpreter), so
///    the delta ledger checks `stripped-JS ≡ Rust` bit-for-bit over the numeric
///    corpus, exactly as for a JS input. Its result — a [`VerifiedLowering`] or a
///    [`Refusal`] (e.g. an out-of-fragment stripped behaviour) — is returned
///    unchanged.
///
/// **Honesty.** The floor lowers BEHAVIOR — the stripped JS run on the numeric
/// corpus — NOT the TypeScript types. Type annotations are ERASED and never
/// trusted as facts (consistent with the doctrine that TS types are conjectures,
/// not verified propositions), so an annotation that disagrees with the runtime
/// behaviour is simply ignored: the ledger judges behaviour. The equivalence is
/// the composition `TS ≡ stripped-JS` (the eraser's Node-differential gate)
/// `∧ stripped-JS ≡ Rust` (the corpus-bounded ledger) — BOTH hops corpus-bounded
/// evidence, the SAME honesty as the JS path, one erasure hop earlier.
///
/// # Errors
/// Returns [`Refusal::NonErasableTypeScript`] if the source is not pure erasable
/// TypeScript, or any [`Refusal`] that [`lower_and_verify`] raises on the stripped
/// JS (out-of-fragment construct, oracle unavailability, or a checked divergence).
pub fn lower_ts_and_verify(ts: &str) -> Result<VerifiedLowering, Refusal> {
    match trust_ts_strip::strip(ts) {
        trust_ts_strip::StripOutcome::Js(js) => lower_and_verify(&js),
        trust_ts_strip::StripOutcome::Refused(reason) => {
            Err(Refusal::NonErasableTypeScript { reason })
        }
    }
}

/// Native evaluation of a NUMERIC IR node over the arguments alone (no local
/// bindings). This is the public entry point for a bare [`ArithIr`] — e.g. a
/// pure-`return` function's IR — where every slot the IR references is a
/// parameter: the arguments become the complete slot vector (all Num). For a
/// function WITH `const`/`let` bindings, use [`eval_func`], which materializes
/// the local slots first. Total: an out-of-range / type-confused slot read
/// (impossible after the checker) degrades to `NaN`, which surfaces as a
/// divergence rather than a panic.
#[must_use]
pub fn eval_ir(ir: &ArithIr, args: &[f64]) -> f64 {
    let slots: Vec<Slot> = args.iter().map(|&a| Slot::Num(a)).collect();
    // No function table: `eval_ir` is the bare-IR entry point for a CALL-FREE
    // numeric IR (a single-function floor lowering). A `Call` node here (only
    // possible in a multi-function module's entry IR) has no callee to resolve and
    // degrades to `NaN`; use [`eval_module`] for a multi-function module.
    eval_num(ir, &slots, &[])
}

/// Native evaluation of a WHOLE lowered function (the execution side of the
/// formal artifact once bindings are present): seed the slot vector with the
/// argument values (slots `0..arity`, all Num), then, in declaration order,
/// evaluate each binding's initializer over the slots so far and push its value
/// (Num or Bool) as the next slot, then evaluate the final numeric return over
/// the full slot vector. This computes exactly what `render_rust`'s
/// `let`-bearing Rust body computes.
#[must_use]
pub fn eval_func(bindings: &[Binding], ret: &ArithIr, args: &[f64]) -> f64 {
    // No function table: a single-function floor lowering has no cross-function
    // calls. For a multi-function module, evaluate the ENTRY via [`eval_module`],
    // which threads the whole table so `Call` nodes resolve.
    eval_func_over(bindings, ret, args, &[])
}

/// Evaluate a WHOLE lowered MODULE: run its ENTRY function (`functions[entry]`) on
/// `args`, resolving every [`ArithIr::Call`] through the module's function table.
/// This is the execution side of a multi-function `VerifiedLowering`. Total: an
/// out-of-range callee index (impossible after the checker) degrades to `NaN`,
/// which surfaces as a divergence rather than a panic; the acyclic call graph
/// (each function calls only earlier ones) guarantees termination.
#[must_use]
pub fn eval_module(functions: &[LoweredFn], entry: usize, args: &[f64]) -> f64 {
    match functions.get(entry) {
        Some(f) => eval_func_over(&f.bindings, &f.ret_ir, args, functions),
        None => f64::NAN,
    }
}

/// Evaluate a WHOLE lowered ARRAY-FOLD (increment 6): reduce `array` left-to-right
/// into the accumulator, then evaluate the return. This is the execution side of a
/// fold `VerifiedLowering`, matching exactly what `render_fold_module`'s
/// `let mut`/`for`-bearing Rust body computes and what the JS for-of does. `helpers`
/// is the scalar-helper table the fold's step / init / return may `Call`; pass
/// `&[]` if there are none. `scalars.len()` must equal `fold.scalar_arity`. Total:
/// an out-of-range slot / callee (impossible after the checker) degrades to `NaN`,
/// which surfaces as a divergence rather than a panic; a finite array terminates.
#[must_use]
pub fn eval_fold(fold: &FoldFn, helpers: &[LoweredFn], array: &[f64], scalars: &[f64]) -> f64 {
    // Seed the slot vector: slot 0 is the array placeholder (never read — the
    // array is consumed only by the loop), slots `1..=scalar_arity` the scalars.
    let mut slots: Vec<Slot> = Vec::with_capacity(2 + scalars.len() + fold.pre_bindings.len());
    slots.push(Slot::Num(f64::NAN));
    for &s in scalars {
        slots.push(Slot::Num(s));
    }
    // Pre-bindings, in declaration order (each over the slots so far).
    for b in &fold.pre_bindings {
        let v = match &b.init {
            TypedIr::Num(ir) => Slot::Num(eval_num(ir, &slots, helpers)),
            TypedIr::Bool(ir) => Slot::Bool(eval_bool(ir, &slots, helpers)),
        };
        slots.push(v);
    }
    // The accumulator (index == acc_slot) then a loop-variable placeholder
    // (index == loop_var_slot).
    let acc0 = eval_num(&fold.acc_init, &slots, helpers);
    slots.push(Slot::Num(acc0));
    slots.push(Slot::Num(f64::NAN));
    // Left-to-right reduction: bind the loop variable, recompute the accumulator.
    for &e in array {
        slots[fold.loop_var_slot] = Slot::Num(e);
        let next = eval_num(&fold.step, &slots, helpers);
        slots[fold.acc_slot] = Slot::Num(next);
    }
    // The return: over the accumulator, the scalars, and the pre-bindings.
    eval_num(&fold.ret, &slots, helpers)
}

/// Evaluate one function's body (bindings then return) over `args`, resolving
/// calls through `fns` (the module's whole function table). Shared by
/// [`eval_func`] (empty table) and [`eval_module`] (whole table). This computes
/// exactly what the rendered Rust `let`-bearing body computes.
fn eval_func_over(bindings: &[Binding], ret: &ArithIr, args: &[f64], fns: &[LoweredFn]) -> f64 {
    let mut slots: Vec<Slot> = args.iter().map(|&a| Slot::Num(a)).collect();
    for b in bindings {
        let v = match &b.init {
            TypedIr::Num(ir) => Slot::Num(eval_num(ir, &slots, fns)),
            TypedIr::Bool(ir) => Slot::Bool(eval_bool(ir, &slots, fns)),
        };
        slots.push(v);
    }
    eval_num(ret, &slots, fns)
}

/// Read slot `i` as a Number (`NaN` if the slot is absent or holds a boolean —
/// impossible after the checker, which types every numeric reference to a Num
/// slot; the fallback keeps eval total).
fn slot_num(slots: &[Slot], i: usize) -> f64 {
    match slots.get(i) {
        Some(Slot::Num(v)) => *v,
        _ => f64::NAN,
    }
}

/// Read slot `i` as a boolean (`false` if the slot is absent or holds a Number —
/// impossible after the checker; the fallback keeps eval total).
fn slot_bool(slots: &[Slot], i: usize) -> bool {
    match slots.get(i) {
        Some(Slot::Bool(b)) => *b,
        _ => false,
    }
}

/// Evaluate a numeric-typed IR node to an `f64` over the slot vector, resolving
/// any `Call` through the module's function table `fns`.
fn eval_num(ir: &ArithIr, slots: &[Slot], fns: &[LoweredFn]) -> f64 {
    match ir {
        // A parameter (slot < arity) and a numeric local (slot >= arity) both
        // read the same slot vector as a Number.
        ArithIr::Param(i) | ArithIr::Local(i) => slot_num(slots, *i),
        ArithIr::Lit(v) => *v,
        ArithIr::Neg(a) => -eval_num(a, slots, fns),
        ArithIr::Add(a, b) => eval_num(a, slots, fns) + eval_num(b, slots, fns),
        ArithIr::Sub(a, b) => eval_num(a, slots, fns) - eval_num(b, slots, fns),
        ArithIr::Mul(a, b) => eval_num(a, slots, fns) * eval_num(b, slots, fns),
        ArithIr::Div(a, b) => eval_num(a, slots, fns) / eval_num(b, slots, fns),
        // JS `%` (ECMA-262 Number::remainder) is truncated fmod-style, and so
        // is Rust's `f64 %`. This equality is not assumed — it is PROVEN per
        // sample by the fidelity check, or the lowering refuses.
        ArithIr::Rem(a, b) => eval_num(a, slots, fns) % eval_num(b, slots, fns),
        // JS bitwise / shift ops over ToInt32 / ToUint32 (EXACT integer functions).
        // Each mirrors the interp oracle (`trust-js-interp::ops`) and the rendered
        // Rust EXACTLY: `|/&/^/~` on `i32`, `<<`/`>>` an arithmetic shift of the
        // signed `i32`, `>>>` a logical shift of the UNSIGNED `u32` (result unsigned,
        // e.g. `-1 >>> 0 == 4294967295`). The shift count is `ToUint32(b) & 31`.
        // `wrapping_sh*` with a count `< 32` is a plain shift (never a panic); the
        // `f64::from` widening is exact (`i32`/`u32` ⊂ exactly-representable `f64`).
        ArithIr::BitOr(a, b) => {
            f64::from(js_to_int32(eval_num(a, slots, fns)) | js_to_int32(eval_num(b, slots, fns)))
        }
        ArithIr::BitAnd(a, b) => {
            f64::from(js_to_int32(eval_num(a, slots, fns)) & js_to_int32(eval_num(b, slots, fns)))
        }
        ArithIr::BitXor(a, b) => {
            f64::from(js_to_int32(eval_num(a, slots, fns)) ^ js_to_int32(eval_num(b, slots, fns)))
        }
        ArithIr::Shl(a, b) => {
            let x = js_to_int32(eval_num(a, slots, fns));
            let s = js_to_uint32(eval_num(b, slots, fns)) & 31;
            f64::from(x.wrapping_shl(s))
        }
        ArithIr::Shr(a, b) => {
            let x = js_to_int32(eval_num(a, slots, fns));
            let s = js_to_uint32(eval_num(b, slots, fns)) & 31;
            f64::from(x.wrapping_shr(s))
        }
        ArithIr::UShr(a, b) => {
            let x = js_to_uint32(eval_num(a, slots, fns));
            let s = js_to_uint32(eval_num(b, slots, fns)) & 31;
            f64::from(x.wrapping_shr(s))
        }
        ArithIr::BitNot(a) => f64::from(!js_to_int32(eval_num(a, slots, fns))),
        // `c ? t : e`: evaluate the boolean test, then the taken branch. JS
        // evaluates only the taken branch; both branches are pure here, so the
        // result is identical, but we still take only the branch the test picks.
        ArithIr::Cond { test, cons, alt } => {
            if eval_bool(test, slots, fns) {
                eval_num(cons, slots, fns)
            } else {
                eval_num(alt, slots, fns)
            }
        }
        // A non-recursive call to an earlier top-level function: evaluate each
        // argument over the CURRENT slots, then run the callee's body with those
        // as its fresh param slots (its own local slot vector). The callee index
        // is absolute in `fns`; an out-of-range index (impossible after the
        // checker) degrades to `NaN` (surfaces as a divergence, never a panic).
        ArithIr::Call { callee, args } => {
            let argvals: Vec<f64> = args.iter().map(|a| eval_num(a, slots, fns)).collect();
            match fns.get(*callee) {
                Some(f) => eval_func_over(&f.bindings, &f.ret_ir, &argvals, fns),
                None => f64::NAN,
            }
        }
        // A `Math.*` builtin: evaluate the arguments, then apply the op's EXACT JS
        // semantics — the SAME logic the rendered Rust computes (compile-check
        // proves render ≡ eval) and, in turn, the interp oracle (the ledger proves
        // eval ≡ oracle, or refuses).
        ArithIr::MathCall { op, args } => {
            let argvals: Vec<f64> = args.iter().map(|a| eval_num(a, slots, fns)).collect();
            eval_math(*op, &argvals)
        }
    }
}

/// Apply a `Math.*` op to already-evaluated arguments. Each op's semantics mirror
/// the rendered Rust EXACTLY: a direct `f64` method for `abs`/`floor`/`ceil`/
/// `trunc`/`sqrt`, a JS-semantics `js_math_*` helper (== the emitted `__js_math_*`
/// helper == the interp oracle) for `sign`/`round`/`min`/`max`. Total: a
/// missing argument (impossible after the arity-checked lowering) reads `NaN`.
fn eval_math(op: MathOp, args: &[f64]) -> f64 {
    let x = args.first().copied().unwrap_or(f64::NAN);
    let y = args.get(1).copied().unwrap_or(f64::NAN);
    match op {
        MathOp::Abs => x.abs(),
        MathOp::Floor => x.floor(),
        MathOp::Ceil => x.ceil(),
        MathOp::Trunc => x.trunc(),
        MathOp::Sqrt => x.sqrt(),
        MathOp::Sign => js_math_sign(x),
        MathOp::Round => js_math_round(x),
        MathOp::Min => js_math_min(x, y),
        MathOp::Max => js_math_max(x, y),
    }
}

// The trap-op semantics, mirroring `HELPER_*` (and the interp oracle) EXACTLY.
// JS `Math.sign`: `±0` and `NaN` preserved (NOT `f64::signum`, which is sign-bit
// based and returns `±1` for `±0`).
#[allow(clippy::float_cmp)]
fn js_math_sign(x: f64) -> f64 {
    if x.is_nan() || x == 0.0 {
        x
    } else if x < 0.0 {
        -1.0
    } else {
        1.0
    }
}

// JS `Math.round`: ties round toward `+Inf` (NOT `f64::round`, which rounds ties
// away from zero); `±0`/`±Inf`/`NaN` preserved; `(-0.5, 0)` maps to `-0`. Mirrors
// `trust-js-interp::builtins_misc::js_math_round`.
#[allow(clippy::float_cmp)]
fn js_math_round(x: f64) -> f64 {
    if !x.is_finite() || x.trunc() == x {
        x
    } else if x > 0.0 && x < 0.5 {
        0.0
    } else if (-0.5..0.0).contains(&x) {
        -0.0
    } else {
        let f = x.floor();
        if x - f >= 0.5 { f + 1.0 } else { f }
    }
}

// JS `Math.min`: NaN-propagating (NOT `f64::min`, NaN-ignoring); `-0 < +0`.
fn js_math_min(a: f64, b: f64) -> f64 {
    if a.is_nan() || b.is_nan() {
        f64::NAN
    } else if a < b {
        a
    } else if b < a {
        b
    } else if a.is_sign_negative() {
        a
    } else {
        b
    }
}

// JS `Math.max`: NaN-propagating; `+0 > -0`.
fn js_math_max(a: f64, b: f64) -> f64 {
    if a.is_nan() || b.is_nan() {
        f64::NAN
    } else if a > b {
        a
    } else if b > a {
        b
    } else if a.is_sign_positive() {
        a
    } else {
        b
    }
}

// ECMA-262 `ToUint32` (7.1.7): NaN/±0/±Infinity ⇒ 0; else reduce `trunc(x)` mod
// 2^32 into `[0, 2^32)`. This is an EXACT integer function — the SAME logic as
// `HELPER_TO_UINT32` (the emitted Rust) and `trust-js-value::to_uint32` (the interp
// oracle), so eval ≡ render ≡ oracle bit-for-bit (`compile_check` and the ledger
// prove it). `fmod` on exact `f64` integers is exact, so even a large-magnitude
// finite `x` (e.g. `1e300`, `4294967297`, `2**53`) reduces bit-exactly.
#[allow(clippy::float_cmp, clippy::cast_possible_truncation, clippy::cast_sign_loss)]
fn js_to_uint32(x: f64) -> u32 {
    if !x.is_finite() || x == 0.0 {
        0
    } else {
        let t = x.trunc();
        let m = t.abs() % 4_294_967_296.0; // m ∈ [0, 2^32), an exact integer
        let u = m as u32;
        if t < 0.0 && u != 0 {
            u32::MAX - u + 1 // 2^32 - u (the negative source's two's-complement)
        } else {
            u
        }
    }
}

// ECMA-262 `ToInt32` (7.1.6): `ToUint32(x)` reinterpreted as a signed `i32` (two's
// complement). `u as i32` is the bit-reinterpret, matching the interp oracle
// (`trust-js-value::to_int32`) and `HELPER_TO_INT32` exactly.
#[allow(clippy::cast_possible_wrap)]
fn js_to_int32(x: f64) -> i32 {
    js_to_uint32(x) as i32
}

// NOTE: there is deliberately no `js_math_pow`. `Math.pow` is a TRANSCENDENTAL and
// is REFUSED at lowering (see `lower_math_call`), never shipped: IEEE-754 does not
// mandate a correctly-rounded `pow`, so `f64::powf` is not bit-identical to JS
// `Math.pow` in general, and an oracle-check against the interp — which computes
// `Math.pow` with the SAME `f64::powf` — would be a tautology that validates
// nothing. (Note `p*p`, the same value in JS, lowers to exact Rust `*` and IS
// correct; only the `Math.pow` route is unsound.)

/// Evaluate a boolean-typed IR node to a `bool` over the slot vector. Comparisons
/// of two numbers use the Rust `f64` comparisons (which model JS relational /
/// strict-equality on numbers, including `NaN` unordered and `-0 == +0`);
/// `&&`/`||` short-circuit exactly as JS does on boolean operands. The ledger is
/// still the authority: if any of these mappings were wrong, the whole numeric
/// result would diverge from the oracle and the lowering would refuse.
#[allow(clippy::float_cmp)]
fn eval_bool(ir: &BoolIr, slots: &[Slot], fns: &[LoweredFn]) -> bool {
    match ir {
        // A boolean local reads the same slot vector as a boolean.
        BoolIr::Local(i) => slot_bool(slots, *i),
        BoolIr::Cmp { op, left, right } => {
            let l = eval_num(left, slots, fns);
            let r = eval_num(right, slots, fns);
            match op {
                CmpOp::Lt => l < r,
                CmpOp::Le => l <= r,
                CmpOp::Gt => l > r,
                CmpOp::Ge => l >= r,
                CmpOp::NumEq => l == r,
                CmpOp::NumNe => l != r,
            }
        }
        BoolIr::BoolEq { op, left, right } => {
            let l = eval_bool(left, slots, fns);
            let r = eval_bool(right, slots, fns);
            match op {
                BoolEqOp::Eq => l == r,
                BoolEqOp::Ne => l != r,
            }
        }
        BoolIr::And(a, b) => eval_bool(a, slots, fns) && eval_bool(b, slots, fns),
        BoolIr::Or(a, b) => eval_bool(a, slots, fns) || eval_bool(b, slots, fns),
        BoolIr::Not(a) => !eval_bool(a, slots, fns),
        BoolIr::Cond { test, cons, alt } => {
            if eval_bool(test, slots, fns) {
                eval_bool(cons, slots, fns)
            } else {
                eval_bool(alt, slots, fns)
            }
        }
    }
}

/// Render the inspectable Rust artifact (§4 object 2):
/// `fn <name>(p0: f64, ...) -> f64 { <let-bindings> <expr> }`, with minimal
/// parens that preserve JS/Rust operator precedence and left-associativity.
/// Parameters are the positional `p0..p{arity-1}`; each `const`/`let` local is a
/// typed, immutable Rust `let l{slot}: f64 = …;` (numeric) or
/// `let l{slot}: bool = …;` (boolean), in declaration order (slots start at
/// `arity`, so local names never collide with the `p*` params or each other);
/// the final numeric return is the block tail. With no bindings the body is just
/// the tail expression — byte-identical to the pure-arith floor.
#[must_use]
pub fn render_rust(bindings: &[Binding], ret: &ArithIr, fn_name: &str, arity: usize) -> String {
    // Backward-compatible single-function render (no cross-function calls): an
    // empty function table means a `Call` node has no name to resolve. Use
    // [`render_module`] to render a multi-function module (which threads the table
    // so calls render `name(a0, ...)`).
    render_one_fn(fn_name, arity, bindings, ret, &[])
}

/// Render the WHOLE module: every function as a free `fn`, in declaration order
/// (helpers first, then the entry, so an earlier `fn` is in scope at every call
/// site), joined by newlines. A call renders `name(a0, a1, ...)` by looking the
/// callee up in `functions`. For a single-function module this is byte-identical
/// to the single-function floor render (one element, no separator added).
#[must_use]
pub fn render_module(functions: &[LoweredFn]) -> String {
    let body = functions
        .iter()
        .map(|f| render_one_fn(&f.name, f.arity, &f.bindings, &f.ret_ir, functions))
        .collect::<Vec<_>>()
        .join("\n");
    // Prepend the prelude helper definitions the module actually uses, so the
    // rendered module is self-contained and compiles standalone: the `__js_to_*`
    // ToInt32/ToUint32 bitwise helpers first, then the `__js_math_*` trap-op helpers
    // (both only the ones needed). A module with neither prepends nothing, so its
    // output is byte-identical to the pre-bitwise / pre-Math floor (direct-map ops
    // and pure arithmetic render inline).
    let mut prelude: Vec<&'static str> = collect_bit_helpers(functions);
    prelude.extend(collect_math_helpers(functions));
    if prelude.is_empty() { body } else { format!("{}\n{body}", prelude.join("\n")) }
}

/// Render a WHOLE array-fold module (increment 6): every scalar helper as a free
/// `fn` (declaration order, so an earlier helper is in scope at every call site),
/// then the fold function, joined by newlines — with any `__js_math_*` trap
/// helpers used anywhere prepended in canonical order. The fold renders
/// `fn f(arr: &[f64], p1: f64, …) -> f64 { <pre lets> let mut l{acc}: f64 = <init>;
/// for &l{x} in arr { l{acc} = <step>; } <ret> }`.
#[must_use]
pub fn render_fold_module(helpers: &[LoweredFn], fold: &FoldFn) -> String {
    let mut parts: Vec<String> = helpers
        .iter()
        .map(|f| render_one_fn(&f.name, f.arity, &f.bindings, &f.ret_ir, helpers))
        .collect();
    parts.push(render_fold_fn(fold, helpers));
    let body = parts.join("\n");
    // Prelude: the `__js_to_*` bitwise helpers first, then the `__js_math_*` trap
    // helpers (only the ones used anywhere in the fold module).
    let mut prelude: Vec<&'static str> = collect_bit_helpers_fold(helpers, fold);
    prelude.extend(collect_math_helpers_fold(helpers, fold));
    if prelude.is_empty() { body } else { format!("{}\n{body}", prelude.join("\n")) }
}

/// Render one array-fold function. The array parameter is the first Rust param
/// (`arr: &[f64]`, referenced only by the `for` loop); scalars render `p1…`. The
/// accumulator is a `let mut l{acc}` (the sole mutable local, so distinct from the
/// immutable pre-binding / loop-variable `let`s); the loop var is `&l{x}` (deref so
/// it binds `f64`); the return is the block tail. A `Call` resolves its name
/// through `fns` (the scalar-helper table).
fn render_fold_fn(fold: &FoldFn, fns: &[LoweredFn]) -> String {
    let mut params: Vec<String> = Vec::with_capacity(1 + fold.scalar_arity);
    params.push("arr: &[f64]".to_string());
    for i in 0..fold.scalar_arity {
        params.push(format!("p{}: f64", 1 + i));
    }
    let mut body = String::new();
    for b in &fold.pre_bindings {
        match &b.init {
            TypedIr::Num(ir) => {
                body.push_str(&format!("let l{}: f64 = {}; ", b.slot, render_num(ir, 0, fns)));
            }
            TypedIr::Bool(ir) => {
                body.push_str(&format!("let l{}: bool = {}; ", b.slot, render_bool(ir, 0, fns)));
            }
        }
    }
    body.push_str(&format!(
        "let mut l{}: f64 = {}; ",
        fold.acc_slot,
        render_num(&fold.acc_init, 0, fns)
    ));
    body.push_str(&format!(
        "for &l{} in arr {{ l{} = {}; }} ",
        fold.loop_var_slot,
        fold.acc_slot,
        render_num(&fold.step, 0, fns)
    ));
    body.push_str(&render_num(&fold.ret, 0, fns));
    format!("fn {}({}) -> f64 {{ {body} }}", fold.name, params.join(", "))
}

/// Collect the trap-op `__js_math_*` helpers used anywhere in a fold module — the
/// scalar helpers PLUS the fold's pre-bindings, accumulator init, step, and return
/// — deduplicated in canonical order. (Same discipline as [`collect_math_helpers`].)
fn collect_math_helpers_fold(helpers: &[LoweredFn], fold: &FoldFn) -> Vec<&'static str> {
    let mut ops: std::collections::BTreeSet<MathOp> = std::collections::BTreeSet::new();
    for f in helpers {
        for b in &f.bindings {
            match &b.init {
                TypedIr::Num(ir) => collect_math_ops_num(ir, &mut ops),
                TypedIr::Bool(ir) => collect_math_ops_bool(ir, &mut ops),
            }
        }
        collect_math_ops_num(&f.ret_ir, &mut ops);
    }
    for b in &fold.pre_bindings {
        match &b.init {
            TypedIr::Num(ir) => collect_math_ops_num(ir, &mut ops),
            TypedIr::Bool(ir) => collect_math_ops_bool(ir, &mut ops),
        }
    }
    collect_math_ops_num(&fold.acc_init, &mut ops);
    collect_math_ops_num(&fold.step, &mut ops);
    collect_math_ops_num(&fold.ret, &mut ops);
    ops.iter().filter_map(|op| op.helper_source()).collect()
}

/// Collect the `__js_math_*` helper definitions the module needs — the trap-op
/// helpers (`sign`/`round`/`min`/`max`) used anywhere in any function's
/// bindings or return — deduplicated and in a fixed canonical order (the `MathOp`
/// variant order), so the rendered module is deterministic. Direct-map ops
/// (`abs`/`floor`/`ceil`/`trunc`/`sqrt`) need no helper.
fn collect_math_helpers(functions: &[LoweredFn]) -> Vec<&'static str> {
    let mut ops: std::collections::BTreeSet<MathOp> = std::collections::BTreeSet::new();
    for f in functions {
        for b in &f.bindings {
            match &b.init {
                TypedIr::Num(ir) => collect_math_ops_num(ir, &mut ops),
                TypedIr::Bool(ir) => collect_math_ops_bool(ir, &mut ops),
            }
        }
        collect_math_ops_num(&f.ret_ir, &mut ops);
    }
    ops.iter().filter_map(|op| op.helper_source()).collect()
}

/// Walk a numeric IR collecting every `Math.*` op it uses (direct-map ops included;
/// [`MathOp::helper_source`] filters them out when emitting helpers).
fn collect_math_ops_num(ir: &ArithIr, ops: &mut std::collections::BTreeSet<MathOp>) {
    match ir {
        ArithIr::Param(_) | ArithIr::Local(_) | ArithIr::Lit(_) => {}
        ArithIr::Neg(a) => collect_math_ops_num(a, ops),
        ArithIr::Add(a, b)
        | ArithIr::Sub(a, b)
        | ArithIr::Mul(a, b)
        | ArithIr::Div(a, b)
        | ArithIr::Rem(a, b)
        | ArithIr::BitOr(a, b)
        | ArithIr::BitAnd(a, b)
        | ArithIr::BitXor(a, b)
        | ArithIr::Shl(a, b)
        | ArithIr::Shr(a, b)
        | ArithIr::UShr(a, b) => {
            collect_math_ops_num(a, ops);
            collect_math_ops_num(b, ops);
        }
        ArithIr::BitNot(a) => collect_math_ops_num(a, ops),
        ArithIr::Cond { test, cons, alt } => {
            collect_math_ops_bool(test, ops);
            collect_math_ops_num(cons, ops);
            collect_math_ops_num(alt, ops);
        }
        ArithIr::Call { args, .. } => {
            for a in args {
                collect_math_ops_num(a, ops);
            }
        }
        ArithIr::MathCall { op, args } => {
            ops.insert(*op);
            for a in args {
                collect_math_ops_num(a, ops);
            }
        }
    }
}

/// Walk a boolean IR collecting every `Math.*` op in its numeric operands.
fn collect_math_ops_bool(ir: &BoolIr, ops: &mut std::collections::BTreeSet<MathOp>) {
    match ir {
        BoolIr::Local(_) => {}
        BoolIr::Cmp { left, right, .. } => {
            collect_math_ops_num(left, ops);
            collect_math_ops_num(right, ops);
        }
        BoolIr::BoolEq { left, right, .. } => {
            collect_math_ops_bool(left, ops);
            collect_math_ops_bool(right, ops);
        }
        BoolIr::And(a, b) | BoolIr::Or(a, b) => {
            collect_math_ops_bool(a, ops);
            collect_math_ops_bool(b, ops);
        }
        BoolIr::Not(a) => collect_math_ops_bool(a, ops),
        BoolIr::Cond { test, cons, alt } => {
            collect_math_ops_bool(test, ops);
            collect_math_ops_bool(cons, ops);
            collect_math_ops_bool(alt, ops);
        }
    }
}

/// Which `ToInt32` / `ToUint32` helpers a rendered module needs. `int32` is set by
/// any `|`/`&`/`^`/`~` and by the `<<`/`>>` operand conversion; `uint32` by any
/// shift (the count is `ToUint32(b)`) and by `>>>`'s operand. `__js_to_int32` calls
/// `__js_to_uint32`, so `int32` DRAGS IN `uint32` (resolved in [`bit_helper_list`]).
#[derive(Default, Clone, Copy)]
struct BitHelperUse {
    int32: bool,
    uint32: bool,
}

/// The helper source list for a `BitHelperUse`, in a fixed order (the primitive
/// `__js_to_uint32` first, then `__js_to_int32` which depends on it), only the
/// helpers actually needed. `int32` implies `uint32` (its dependency).
fn bit_helper_list(mut u: BitHelperUse) -> Vec<&'static str> {
    if u.int32 {
        u.uint32 = true;
    }
    let mut out: Vec<&'static str> = Vec::new();
    if u.uint32 {
        out.push(HELPER_TO_UINT32);
    }
    if u.int32 {
        out.push(HELPER_TO_INT32);
    }
    out
}

/// Walk a numeric IR marking which `ToInt32`/`ToUint32` helpers its bitwise / shift
/// nodes need (see [`BitHelperUse`]).
fn collect_bit_use_num(ir: &ArithIr, u: &mut BitHelperUse) {
    match ir {
        ArithIr::Param(_) | ArithIr::Local(_) | ArithIr::Lit(_) => {}
        ArithIr::Neg(a) => collect_bit_use_num(a, u),
        ArithIr::BitNot(a) => {
            u.int32 = true;
            collect_bit_use_num(a, u);
        }
        ArithIr::Add(a, b)
        | ArithIr::Sub(a, b)
        | ArithIr::Mul(a, b)
        | ArithIr::Div(a, b)
        | ArithIr::Rem(a, b) => {
            collect_bit_use_num(a, u);
            collect_bit_use_num(b, u);
        }
        ArithIr::BitOr(a, b) | ArithIr::BitAnd(a, b) | ArithIr::BitXor(a, b) => {
            u.int32 = true;
            collect_bit_use_num(a, u);
            collect_bit_use_num(b, u);
        }
        ArithIr::Shl(a, b) | ArithIr::Shr(a, b) => {
            u.int32 = true;
            u.uint32 = true;
            collect_bit_use_num(a, u);
            collect_bit_use_num(b, u);
        }
        ArithIr::UShr(a, b) => {
            u.uint32 = true;
            collect_bit_use_num(a, u);
            collect_bit_use_num(b, u);
        }
        ArithIr::Cond { test, cons, alt } => {
            collect_bit_use_bool(test, u);
            collect_bit_use_num(cons, u);
            collect_bit_use_num(alt, u);
        }
        ArithIr::Call { args, .. } | ArithIr::MathCall { args, .. } => {
            for a in args {
                collect_bit_use_num(a, u);
            }
        }
    }
}

/// Walk a boolean IR marking the `ToInt32`/`ToUint32` helpers its numeric operands
/// need.
fn collect_bit_use_bool(ir: &BoolIr, u: &mut BitHelperUse) {
    match ir {
        BoolIr::Local(_) => {}
        BoolIr::Cmp { left, right, .. } => {
            collect_bit_use_num(left, u);
            collect_bit_use_num(right, u);
        }
        BoolIr::BoolEq { left, right, .. } => {
            collect_bit_use_bool(left, u);
            collect_bit_use_bool(right, u);
        }
        BoolIr::And(a, b) | BoolIr::Or(a, b) => {
            collect_bit_use_bool(a, u);
            collect_bit_use_bool(b, u);
        }
        BoolIr::Not(a) => collect_bit_use_bool(a, u),
        BoolIr::Cond { test, cons, alt } => {
            collect_bit_use_bool(test, u);
            collect_bit_use_bool(cons, u);
            collect_bit_use_bool(alt, u);
        }
    }
}

/// Collect the `__js_to_*` helper definitions a scalar module needs — those used in
/// any function's bindings or return — in [`bit_helper_list`] order.
fn collect_bit_helpers(functions: &[LoweredFn]) -> Vec<&'static str> {
    let mut u = BitHelperUse::default();
    for f in functions {
        for b in &f.bindings {
            match &b.init {
                TypedIr::Num(ir) => collect_bit_use_num(ir, &mut u),
                TypedIr::Bool(ir) => collect_bit_use_bool(ir, &mut u),
            }
        }
        collect_bit_use_num(&f.ret_ir, &mut u);
    }
    bit_helper_list(u)
}

/// Collect the `__js_to_*` helpers a fold module needs — the scalar helpers PLUS the
/// fold's pre-bindings, accumulator init, step, and return.
fn collect_bit_helpers_fold(helpers: &[LoweredFn], fold: &FoldFn) -> Vec<&'static str> {
    let mut u = BitHelperUse::default();
    for f in helpers {
        for b in &f.bindings {
            match &b.init {
                TypedIr::Num(ir) => collect_bit_use_num(ir, &mut u),
                TypedIr::Bool(ir) => collect_bit_use_bool(ir, &mut u),
            }
        }
        collect_bit_use_num(&f.ret_ir, &mut u);
    }
    for b in &fold.pre_bindings {
        match &b.init {
            TypedIr::Num(ir) => collect_bit_use_num(ir, &mut u),
            TypedIr::Bool(ir) => collect_bit_use_bool(ir, &mut u),
        }
    }
    collect_bit_use_num(&fold.acc_init, &mut u);
    collect_bit_use_num(&fold.step, &mut u);
    collect_bit_use_num(&fold.ret, &mut u);
    bit_helper_list(u)
}

/// Render one function as `fn <name>(p0: f64, ...) -> f64 { <let-bindings> <expr> }`,
/// resolving any `Call` name through `fns` (the module's function table).
fn render_one_fn(
    fn_name: &str,
    arity: usize,
    bindings: &[Binding],
    ret: &ArithIr,
    fns: &[LoweredFn],
) -> String {
    let params: Vec<String> = (0..arity).map(|i| format!("p{i}: f64")).collect();
    let mut body = String::new();
    for b in bindings {
        match &b.init {
            TypedIr::Num(ir) => {
                body.push_str(&format!("let l{}: f64 = {}; ", b.slot, render_num(ir, 0, fns)));
            }
            TypedIr::Bool(ir) => {
                body.push_str(&format!("let l{}: bool = {}; ", b.slot, render_bool(ir, 0, fns)));
            }
        }
    }
    body.push_str(&render_num(ret, 0, fns));
    format!("fn {fn_name}({}) -> f64 {{ {body} }}", params.join(", "))
}

// ===========================================================================
// Fragment gate + lowering (fail closed)
// ===========================================================================

/// The single-function view used by the render-only test helper (`rendered`): the
/// ENTRY function's shape. Multi-function lowering goes through [`lower_module`].
#[cfg(test)]
struct Lowered {
    name: String,
    arity: usize,
    bindings: Vec<Binding>,
    ret: ArithIr,
}

/// The resolution context for lowering ONE function's expressions: its own lexical
/// `scope` (params + already-declared locals) and `fns`, the module's ALREADY-
/// LOWERED (strictly-earlier) top-level functions, which are the ONLY names a call
/// may resolve to. Because `fns` holds only earlier functions and lowering is in
/// declaration order, the call graph is acyclic by construction (no recursion of
/// any kind), so composition trivially terminates.
struct LowerCtx<'a> {
    scope: &'a Scope,
    fns: &'a [LoweredFn],
}

/// The lowered form of a whole module: either an all-scalar function table (the
/// ENTRY is its last element) or a set of scalar helpers plus ONE array-fold entry
/// (increment 6). Private; [`lower_and_verify`] turns it into a `VerifiedLowering`.
enum Module {
    Scalar(Vec<LoweredFn>),
    Fold { helpers: Vec<LoweredFn>, fold: FoldFn },
}

/// Lower a WHOLE module: the source must be ONLY top-level `function` declarations
/// (any non-function top-level statement refuses the whole module). Each function
/// is lowered in declaration order into a function table; a function's call-
/// resolution scope is the set of ALREADY-lowered (strictly earlier) functions —
/// so a call to the current function itself, a later one, or any cycle simply
/// cannot resolve and refuses (recursion is impossible). Duplicate top-level
/// function names refuse (a call name must resolve to exactly one function).
///
/// A function whose body contains a top-level `for (… of …)` loop is an
/// **array-fold** (increment 6): it is the module ENTRY and MUST be the
/// LAST-declared function (earlier functions are scalar helpers it may call); a
/// fold in any earlier position refuses. A scalar module returns `Module::Scalar`
/// (non-empty, entry = last); a fold module returns `Module::Fold` (scalar helpers
/// + the fold).
fn lower_module(js: &str) -> Result<Module, Refusal> {
    let prog = match parse_script(js, false) {
        ParseOutcome::Script(p) => p,
        ParseOutcome::EarlyError { reason } => {
            return Err(Refusal::ParseError { reason: format!("early error: {reason}") });
        }
        ParseOutcome::Unsupported { reason } => {
            return Err(Refusal::ParseError { reason: format!("unsupported: {reason}") });
        }
    };

    if prog.body.is_empty() {
        return Err(Refusal::NotSingleFunction {
            reason: "the source contains no top-level function declarations".to_string(),
        });
    }

    let n = prog.body.len();
    let mut functions: Vec<LoweredFn> = Vec::with_capacity(n);
    for (idx, stmt) in prog.body.iter().enumerate() {
        // Every top-level statement must be a function declaration. A non-function
        // top-level statement (a `const`/`let`/`var`, a bare expression, etc.)
        // refuses the WHOLE module — the fragment has no top-level bindings.
        let Stmt::FuncDecl(func) = stmt else {
            return Err(Refusal::NotSingleFunction {
                reason: "a top-level statement is not a function declaration (the module must \
                         be only `function` declarations)"
                    .to_string(),
            });
        };
        // An array-fold (for-of) function is the module ENTRY: it must be the
        // LAST-declared function, and there is at most one. Its callable scope is
        // the earlier scalar helpers; on success we return immediately.
        if func_has_for_of(func) {
            if idx != n - 1 {
                return Err(Refusal::UnsupportedStatement {
                    reason: "an array-fold (for-of) function must be the LAST-declared function \
                             (the module entry); a helper function is scalar and may not contain \
                             a loop"
                        .to_string(),
                });
            }
            let fold = lower_fold_func(func, &functions)?;
            if functions.iter().any(|f| f.name == fold.name) {
                return Err(Refusal::Redeclaration { name: fold.name });
            }
            return Ok(Module::Fold { helpers: functions, fold });
        }
        // A scalar function; its callable scope is only the earlier functions.
        let lowered = lower_one_func(func, &functions)?;
        // A duplicate top-level function name would make a call name ambiguous
        // (and, in JS, later-wins hoisting could alias a recursive self-call).
        // Refuse fail-closed. (Function declarations at script top level are not
        // lexical, so the parser does not reject the duplicate for us.)
        if functions.iter().any(|f| f.name == lowered.name) {
            return Err(Refusal::Redeclaration { name: lowered.name });
        }
        functions.push(lowered);
    }
    Ok(Module::Scalar(functions))
}

/// Whether a function body contains a top-level `for (… of …)` loop — the trigger
/// for the array-fold shape. A for-of nested inside another statement is not a
/// fold trigger (the containing statement refuses on the scalar path).
fn func_has_for_of(func: &Func) -> bool {
    func.body.iter().any(|s| matches!(s, Stmt::ForOf { .. }))
}

/// Lower ONE array-fold function (increment 6) against `fns` (the strictly-earlier
/// SCALAR helpers it may call). The shape is EXACTLY
/// `function f(ARR, s0, …) { <binding>* let ACC = <init>; for (const X of ARR) {
/// ACC = <step>; } return <ret>; }`, with `ARR` the first parameter (a number
/// array — detected as the for-of iterable), `s0…` scalar `Num` params, a mutable
/// `let` accumulator reduced by a single `const X` for-of over `ARR`, and a numeric
/// return. Anything outside this exact shape refuses, fail-closed (a refusal is
/// always sound). Slot model: array = slot 0 (`Ty::Array`, non-referenceable),
/// scalars = slots `1..=k` (Num), then pre-bindings, the accumulator, and the loop
/// variable in declaration order.
fn lower_fold_func(func: &Func, fns: &[LoweredFn]) -> Result<FoldFn, Refusal> {
    let (name, body) = gate_func(func)?;
    let params = param_names(func)?;
    let Some((array_name, scalar_names)) = params.split_first() else {
        return Err(Refusal::UnsupportedParameter {
            reason: "an array-fold function needs an array parameter (its first parameter) \
                     followed by zero or more scalar parameters"
                .to_string(),
        });
    };
    let scalar_arity = scalar_names.len();

    // Body = [ <pre-binding>* , let ACC = <init> , for-of , return <expr> ].
    // Split off the trailing `return <expr>;`.
    let (last, before_ret) = body.split_last().ok_or_else(|| Refusal::NotSingleArithReturn {
        reason: "empty function body (no `return <expr>;`)".to_string(),
    })?;
    let ret_expr = match last {
        Stmt::Return(Some(e)) => e,
        Stmt::Return(None) => {
            return Err(Refusal::NotSingleArithReturn {
                reason: "the final statement is `return;` with no value".to_string(),
            });
        }
        _ => {
            return Err(Refusal::NotSingleArithReturn {
                reason: "the function body does not end with `return <expr>;`".to_string(),
            });
        }
    };
    // The statement immediately before the return must be the for-of loop.
    let (loop_stmt, pre_and_acc) =
        before_ret.split_last().ok_or_else(|| Refusal::UnsupportedStatement {
            reason: "an array-fold body must be `<binding>* let ACC = <init>; \
                     for (const X of ARR) { ACC = <expr>; } return <expr>;` — the for-of loop \
                     is missing"
                .to_string(),
        })?;
    let Stmt::ForOf { left, right, body: loop_body, is_await } = loop_stmt else {
        return Err(Refusal::UnsupportedStatement {
            reason: "the statement before the final return is not a `for (const X of ARR)` loop"
                .to_string(),
        });
    };
    if *is_await {
        return Err(Refusal::UnsupportedConstruct { construct: "for-await-of loop".to_string() });
    }
    // for-of head: `const X` with a plain identifier (no let/var, no destructuring).
    let ForHead::Decl(DeclKind::Const, Pat::Ident(loop_var_name)) = left else {
        return Err(Refusal::UnsupportedStatement {
            reason: "the for-of head must bind `const X` with a plain identifier (a `let`/`var` \
                     loop variable, a destructuring head, or an index/entries iteration refuses)"
                .to_string(),
        });
    };
    // The iterable must be EXACTLY the array parameter identifier.
    let Expr::Ident(iter_name) = right else {
        return Err(Refusal::UnsupportedStatement {
            reason: "the for-of iterates over something other than the array parameter (only \
                     `for (const X of ARR)` over the first parameter is supported — not a \
                     literal, a scalar, or an expression)"
                .to_string(),
        });
    };
    if iter_name != array_name {
        return Err(Refusal::UnsupportedStatement {
            reason: format!(
                "the for-of iterates over `{iter_name}`, not the array parameter `{array_name}` \
                 (the array must be the first parameter, used only as the iterable)"
            ),
        });
    }
    // The loop body must be exactly one `ACC = <expr>` assignment.
    let body_stmt = single_loop_body_stmt(loop_body)?;
    let Stmt::Expr(Expr::Assign { op, target, value: step_expr }) = body_stmt else {
        return Err(Refusal::UnsupportedStatement {
            reason: "the for-of body is not a single `ACC = <expr>` assignment (no local \
                     binding, `if`, `break`/`continue`, nested loop, or extra statements)"
                .to_string(),
        });
    };
    if *op != "=" {
        return Err(Refusal::UnsupportedStatement {
            reason: format!(
                "the fold step uses the compound assignment `{op}` (only a plain `ACC = <expr>` \
                 is supported)"
            ),
        });
    }
    let Pat::Ident(acc_name) = target.as_ref() else {
        return Err(Refusal::UnsupportedStatement {
            reason: "the fold step assigns to a non-identifier target (indexing / member / \
                     destructuring)"
                .to_string(),
        });
    };
    // The statement immediately before the for-of must declare the accumulator
    // `let ACC = <init>` (a mutable `let`, NOT `const`).
    let (acc_decl, pre_stmts) =
        pre_and_acc.split_last().ok_or_else(|| Refusal::UnsupportedStatement {
            reason: "the accumulator declaration `let ACC = <init>` before the for-of is missing"
                .to_string(),
        })?;
    let (acc_bind_name, acc_init_expr) = gate_acc_decl(acc_decl)?;
    if acc_bind_name != acc_name.as_str() {
        return Err(Refusal::UnsupportedStatement {
            reason: format!(
                "the accumulator declared before the loop is `{acc_bind_name}`, but the fold \
                 step assigns `{acc_name}` (the loop must reduce the declared accumulator)"
            ),
        });
    }

    // Build the fold's slot scope: array (slot 0, non-referenceable), scalars
    // (slots `1..=k`, Num), then pre-bindings, the accumulator, and the loop var.
    let mut scope = Scope::new(1 + scalar_arity);
    scope.declare(array_name.clone(), 0, Ty::Array);
    for (i, sn) in scalar_names.iter().enumerate() {
        scope.declare(sn.clone(), 1 + i, Ty::Num);
    }

    // Pre-bindings: ordinary SSA `const`/`let` locals (Num or Bool). A name that
    // collides with a param, an earlier local, the accumulator, or the loop
    // variable refuses.
    let mut pre_bindings: Vec<Binding> = Vec::with_capacity(pre_stmts.len());
    for stmt in pre_stmts {
        let (bind_name, init_expr) = gate_binding(stmt)?;
        if scope.lookup(&bind_name).is_some()
            || bind_name == *acc_name
            || &bind_name == loop_var_name
        {
            return Err(Refusal::Redeclaration { name: bind_name });
        }
        let init = lower_typed(init_expr, &LowerCtx { scope: &scope, fns })?;
        let ty = match &init {
            TypedIr::Num(_) => Ty::Num,
            TypedIr::Bool(_) => Ty::Bool,
        };
        let slot = scope.next_slot();
        scope.declare(bind_name, slot, ty);
        pre_bindings.push(Binding { slot, init });
    }

    // The accumulator: a numeric initializer over params + pre-bindings (it may
    // not reference itself or the loop variable). Declared at the next slot.
    if scope.lookup(acc_name).is_some() {
        return Err(Refusal::Redeclaration { name: acc_name.clone() });
    }
    let acc_init = lower_num(acc_init_expr, &LowerCtx { scope: &scope, fns })?;
    let acc_slot = scope.next_slot();
    scope.declare(acc_name.clone(), acc_slot, Ty::Num);

    // The loop variable: a numeric slot, in scope ONLY for the step.
    if scope.lookup(loop_var_name).is_some() {
        return Err(Refusal::Redeclaration { name: loop_var_name.clone() });
    }
    let loop_var_slot = scope.next_slot();
    scope.declare(loop_var_name.clone(), loop_var_slot, Ty::Num);
    let step = lower_num(step_expr, &LowerCtx { scope: &scope, fns })?;

    // The return: numeric, over params + pre-bindings + accumulator, but NOT the
    // loop variable (out of scope after the loop) — pop it before lowering.
    scope.pop_last();
    let ret = lower_num(ret_expr, &LowerCtx { scope: &scope, fns })?;

    Ok(FoldFn { name, scalar_arity, pre_bindings, acc_slot, acc_init, loop_var_slot, step, ret })
}

/// The single statement inside a fold loop body: a `{ … }` block must hold exactly
/// one statement; a bare (unbraced) body is that one statement. Zero / multiple
/// statements refuse.
fn single_loop_body_stmt(body: &Stmt) -> Result<&Stmt, Refusal> {
    match body {
        Stmt::Block(stmts) => {
            if stmts.len() == 1 {
                Ok(&stmts[0])
            } else {
                Err(Refusal::UnsupportedStatement {
                    reason: format!(
                        "the fold loop body must be exactly one `ACC = <expr>` assignment, found \
                         {} statements",
                        stmts.len()
                    ),
                })
            }
        }
        other => Ok(other),
    }
}

/// Gate the accumulator declaration `let ACC = <init>;` before the for-of. It MUST
/// be a `let` (a mutable-style accumulator, reassigned in the loop) with a single
/// plain-identifier declarator and an initializer. A `const` accumulator (cannot be
/// reassigned), `var`, `using`, destructuring, multiple declarators, or a missing
/// initializer refuses. Returns `(name, initializer)`.
fn gate_acc_decl(stmt: &Stmt) -> Result<(&str, &Expr), Refusal> {
    let Stmt::Decl { kind, decls } = stmt else {
        return Err(Refusal::UnsupportedStatement {
            reason: "the statement before the for-of is not an accumulator declaration \
                     `let ACC = <init>`"
                .to_string(),
        });
    };
    match kind {
        DeclKind::Let => {}
        DeclKind::Const => {
            return Err(Refusal::UnsupportedBinding {
                reason: "the accumulator is declared `const` (it must be a `let`, since the fold \
                         reassigns it each iteration)"
                    .to_string(),
            });
        }
        DeclKind::Var => {
            return Err(Refusal::UnsupportedBinding {
                reason: "the accumulator is declared `var` (only a `let` accumulator is supported)"
                    .to_string(),
            });
        }
        DeclKind::Using | DeclKind::AwaitUsing => {
            return Err(Refusal::UnsupportedBinding {
                reason: "`using` / `await using` accumulator".to_string(),
            });
        }
    }
    if decls.len() != 1 {
        return Err(Refusal::UnsupportedBinding {
            reason: format!(
                "the accumulator declaration has {} declarators (only a single `let ACC = <init>` \
                 is supported)",
                decls.len()
            ),
        });
    }
    let (pat, init) = &decls[0];
    let Pat::Ident(nm) = pat else {
        return Err(Refusal::UnsupportedBinding {
            reason: "the accumulator uses a destructuring / non-identifier pattern".to_string(),
        });
    };
    let Some(init_expr) = init else {
        return Err(Refusal::UnsupportedBinding {
            reason: format!("the accumulator `{nm}` has no initializer"),
        });
    };
    Ok((nm.as_str(), init_expr))
}

/// Lower ONE top-level function against `fns` (the strictly-earlier functions it
/// may call). Same single-function fragment as the floor — `<binding>* return
/// <expr>;`, numeric params, numeric result — with the initializer/return grammar
/// now able to CALL an earlier function.
fn lower_one_func(func: &Func, fns: &[LoweredFn]) -> Result<LoweredFn, Refusal> {
    let (name, body) = gate_func(func)?;
    let param_names = param_names(func)?;
    let arity = param_names.len();

    // The body is `<const|let binding>* return <expr>;`. Split off the trailing
    // `return`, then walk the leading statements as bindings, building an ordered
    // symbol table (params in slots `0..arity`, then locals in declaration order).
    let (init_stmts, ret_expr) = split_return(body)?;

    let mut scope = Scope::new(arity);
    for (i, pn) in param_names.iter().enumerate() {
        // Params occupy slots `0..arity` and are always Num.
        scope.declare(pn.clone(), i, Ty::Num);
    }

    let mut bindings: Vec<Binding> = Vec::with_capacity(init_stmts.len());
    for stmt in init_stmts {
        let (bind_name, init_expr) = gate_binding(stmt)?;
        // Redeclaration / shadowing of a parameter or an already-declared local
        // is refused (avoids scope subtlety). The parser usually rejects a
        // duplicate lexical declaration first; this is the fail-closed guard.
        if scope.lookup(&bind_name).is_some() {
            return Err(Refusal::Redeclaration { name: bind_name });
        }
        // Type the initializer against the scope so far (params + earlier
        // locals) and the earlier-functions table. A reference to any not-yet-
        // declared name refuses inside `lower_typed` (TDZ / use-before-decl /
        // free variable). The local's type IS its initializer's type.
        let init = lower_typed(init_expr, &LowerCtx { scope: &scope, fns })?;
        let ty = match &init {
            TypedIr::Num(_) => Ty::Num,
            TypedIr::Bool(_) => Ty::Bool,
        };
        let slot = scope.next_slot();
        scope.declare(bind_name, slot, ty);
        bindings.push(Binding { slot, init });
    }

    // The whole return expression MUST type to Num. A bare-boolean result is out
    // of the numeric-result fragment and is refused (nothing emitted).
    let ret_ir = match lower_typed(ret_expr, &LowerCtx { scope: &scope, fns })? {
        TypedIr::Num(ir) => ir,
        TypedIr::Bool(_) => {
            return Err(Refusal::NonNumericResult {
                reason: "the return expression is a boolean; only numeric-result \
                         functions are in the fragment"
                    .to_string(),
            });
        }
    };
    Ok(LoweredFn { name, arity, bindings, ret_ir })
}

/// The single-function view of a module's ENTRY, for the render-only test helper.
/// (The whole module goes through [`lower_module`]; this drops the helpers and is
/// used only where a single function is rendered without cross-function calls.)
#[cfg(test)]
fn lower(js: &str) -> Result<Lowered, Refusal> {
    match lower_module(js)? {
        Module::Scalar(functions) => {
            let entry = functions.into_iter().next_back().expect("scalar module is non-empty");
            Ok(Lowered {
                name: entry.name,
                arity: entry.arity,
                bindings: entry.bindings,
                ret: entry.ret_ir,
            })
        }
        // `lower`/`rendered` are scalar-only render helpers; a fold module is
        // exercised through `lower_and_verify` (see the fold tests).
        Module::Fold { .. } => panic!("lower() is scalar-only; use lower_and_verify for a fold"),
    }
}

/// Check the function header (not `async` / generator / arrow, and named) and
/// return `(name, body-statements)`. The body shape (`<binding>* return`) is
/// validated by [`split_return`] + [`gate_binding`].
fn gate_func(func: &Func) -> Result<(String, &[Stmt]), Refusal> {
    if func.is_async {
        return Err(Refusal::UnsupportedConstruct { construct: "async function".to_string() });
    }
    if func.is_gen {
        return Err(Refusal::UnsupportedConstruct { construct: "generator function".to_string() });
    }
    if func.is_arrow || func.expr_body.is_some() {
        // A `function` declaration is never an arrow; guard anyway (fail closed).
        return Err(Refusal::UnsupportedConstruct {
            construct: "arrow / concise body".to_string(),
        });
    }
    let Some(name) = &func.name else {
        return Err(Refusal::NotSingleFunction {
            reason: "anonymous function declaration (cannot be called by name)".to_string(),
        });
    };
    Ok((name.clone(), func.body.as_slice()))
}

/// Split a function body into its leading statements and the trailing
/// `return <expr>;`. Refuses an empty body, a `return;` with no value, or a body
/// that does not end in `return <expr>;`.
fn split_return(body: &[Stmt]) -> Result<(&[Stmt], &Expr), Refusal> {
    let Some((last, init)) = body.split_last() else {
        return Err(Refusal::NotSingleArithReturn {
            reason: "empty function body (no `return <expr>;`)".to_string(),
        });
    };
    match last {
        Stmt::Return(Some(expr)) => Ok((init, expr)),
        Stmt::Return(None) => Err(Refusal::NotSingleArithReturn {
            reason: "the final statement is `return;` with no value".to_string(),
        }),
        _ => Err(Refusal::NotSingleArithReturn {
            reason: "the function body does not end with `return <expr>;`".to_string(),
        }),
    }
}

/// Gate one leading statement as a supported `const`/`let` binding, returning its
/// `(name, initializer)`. Refuses fail-closed anything else: `var` / `using`, a
/// destructuring pattern, multiple declarators, a missing initializer, and any
/// non-declaration statement (a reassignment `x = …` / `x++`, an `if` / loop /
/// block, or an early / duplicate `return`).
fn gate_binding(stmt: &Stmt) -> Result<(String, &Expr), Refusal> {
    match stmt {
        Stmt::Decl { kind, decls } => {
            match kind {
                DeclKind::Const | DeclKind::Let => {}
                DeclKind::Var => {
                    return Err(Refusal::UnsupportedBinding {
                        reason: "`var` declaration (function-scope hoisting is out of the \
                                 SSA fragment)"
                            .to_string(),
                    });
                }
                DeclKind::Using | DeclKind::AwaitUsing => {
                    return Err(Refusal::UnsupportedBinding {
                        reason: "`using` / `await using` declaration".to_string(),
                    });
                }
            }
            if decls.len() != 1 {
                return Err(Refusal::UnsupportedBinding {
                    reason: format!(
                        "multiple declarators in one declaration ({} bindings; only a single \
                         declarator is supported)",
                        decls.len()
                    ),
                });
            }
            let (pat, init) = &decls[0];
            let Pat::Ident(nm) = pat else {
                return Err(Refusal::UnsupportedBinding {
                    reason: "destructuring / non-identifier binding pattern".to_string(),
                });
            };
            let Some(init_expr) = init else {
                return Err(Refusal::UnsupportedBinding {
                    reason: format!("binding `{nm}` has no initializer"),
                });
            };
            Ok((nm.clone(), init_expr))
        }
        // A reassignment / update is a non-declaration statement — called out
        // explicitly because this fragment is SSA-only (each name is bound once).
        Stmt::Expr(Expr::Assign { .. }) | Stmt::Expr(Expr::Update { .. }) => {
            Err(Refusal::UnsupportedStatement {
                reason: "assignment / update statement (this fragment is SSA-only: each name is \
                         bound exactly once and never reassigned)"
                    .to_string(),
            })
        }
        _ => Err(Refusal::UnsupportedStatement {
            reason: "a statement other than a `const`/`let` binding appears before the final \
                     `return` (no `if`, loops, blocks, bare expressions, or early returns)"
                .to_string(),
        }),
    }
}

/// Every parameter must be a plain, distinct identifier.
fn param_names(func: &Func) -> Result<Vec<String>, Refusal> {
    let mut names: Vec<String> = Vec::with_capacity(func.params.len());
    for p in &func.params {
        match p {
            Pat::Ident(n) => {
                if names.contains(n) {
                    return Err(Refusal::UnsupportedParameter {
                        reason: format!("duplicate parameter name `{n}`"),
                    });
                }
                names.push(n.clone());
            }
            _ => {
                return Err(Refusal::UnsupportedParameter {
                    reason: "parameter is not a plain identifier (default / rest / destructuring)"
                        .to_string(),
                });
            }
        }
    }
    Ok(names)
}

/// An ordered lexical symbol table: parameters (slots `0..arity`, always Num)
/// followed by `const`/`let` locals in declaration order (slots `arity..`).
/// Lookup is by name over the entries declared *so far*, so an initializer can
/// only reference already-declared names (lexical order) — a not-yet-declared
/// name is simply absent and refuses.
struct Scope {
    arity: usize,
    entries: Vec<ScopeEntry>,
}

struct ScopeEntry {
    name: String,
    slot: usize,
    ty: Ty,
}

impl Scope {
    fn new(arity: usize) -> Self {
        Scope { arity, entries: Vec::new() }
    }

    /// The next free absolute slot index. Slots are declared contiguously from
    /// 0 (params first), so this is exactly the number of entries so far.
    fn next_slot(&self) -> usize {
        self.entries.len()
    }

    fn declare(&mut self, name: String, slot: usize, ty: Ty) {
        self.entries.push(ScopeEntry { name, slot, ty });
    }

    fn lookup(&self, name: &str) -> Option<&ScopeEntry> {
        self.entries.iter().find(|e| e.name == name)
    }

    /// Pop the most-recently-declared entry. Used by the fold lowering to drop the
    /// loop variable from scope after the step (it is out of scope in the return).
    fn pop_last(&mut self) {
        self.entries.pop();
    }

    /// Build the typed IR reference for `name`, or `None` if it is not in scope.
    /// A parameter (slot `< arity`) becomes `ArithIr::Param`; a numeric local
    /// becomes `ArithIr::Local`; a boolean local becomes `BoolIr::Local`
    /// (parameters are never boolean). An array parameter (`Ty::Array`) is NOT a
    /// value expression — it resolves to `None`, so any reference other than the
    /// for-of iterable (which `lower_fold_func` matches by name) refuses as a free
    /// identifier.
    fn reference(&self, name: &str) -> Option<TypedIr> {
        let e = self.lookup(name)?;
        match e.ty {
            Ty::Num if e.slot < self.arity => Some(TypedIr::Num(ArithIr::Param(e.slot))),
            Ty::Num => Some(TypedIr::Num(ArithIr::Local(e.slot))),
            Ty::Bool => Some(TypedIr::Bool(BoolIr::Local(e.slot))),
            Ty::Array => None,
        }
    }
}

/// Lower one expression, statically type it to {Num, Bool}, or refuse. `ctx`
/// resolves identifiers to parameters and already-declared locals, and calls to
/// strictly-earlier top-level functions.
fn lower_typed(expr: &Expr, ctx: &LowerCtx) -> Result<TypedIr, Refusal> {
    match expr {
        Expr::Paren(inner) => lower_typed(inner, ctx),

        // A reference resolves to a parameter or an already-declared local
        // (lexical order). A name that is neither — a free variable, or a local
        // used before its own declaration (TDZ / use-before-decl) — is refused.
        Expr::Ident(name) => {
            ctx.scope.reference(name).ok_or_else(|| Refusal::UnsupportedConstruct {
                construct: format!(
                    "free identifier `{name}` (not a parameter or an already-declared local)"
                ),
            })
        }

        Expr::Num(raw) => match numeric_literal_mv(raw) {
            Ok(v) => Ok(TypedIr::Num(ArithIr::Lit(v))),
            Err(reason) => Err(Refusal::UnsupportedConstruct {
                construct: format!("numeric literal `{raw}` outside modeled slice: {reason}"),
            }),
        },

        Expr::BigInt(_) => {
            Err(Refusal::UnsupportedConstruct { construct: "BigInt literal".to_string() })
        }

        Expr::Unary { op, arg } => match *op {
            // Unary `-` / `+` require a numeric operand, yield a number.
            "-" => Ok(TypedIr::Num(ArithIr::Neg(Box::new(lower_num(arg, ctx)?)))),
            // Unary `+` on a number is the identity (ToNumber(number) == number,
            // bit-for-bit incl. -0 and NaN) — fold it away. It still REQUIRES a
            // numeric operand (`+(a>0)` is ToNumber(bool), which we do not model
            // — refuse rather than coerce).
            "+" => Ok(TypedIr::Num(lower_num(arg, ctx)?)),
            // Logical NOT requires a boolean operand, yields a boolean.
            "!" => Ok(TypedIr::Bool(BoolIr::Not(Box::new(lower_bool(arg, ctx)?)))),
            // Bitwise NOT `~a` = `!ToInt32(a)` — requires a NUMERIC operand (a
            // boolean is a type error at `lower_num`, never coerced), yields a
            // number. EXACT integer op, so it ships (unlike a transcendental).
            "~" => Ok(TypedIr::Num(ArithIr::BitNot(Box::new(lower_num(arg, ctx)?)))),
            other => Err(Refusal::UnsupportedConstruct {
                construct: format!("unary operator `{other}`"),
            }),
        },

        Expr::Binary { op, left, right } => lower_binary(op, left, right, ctx),

        // A CALL to a strictly-earlier top-level function: `g(e0, e1, ...)`.
        Expr::Call { callee, args, optional, in_chain } => {
            lower_call(callee, args, *optional, *in_chain, ctx)
        }

        // `&&` / `||`: Bool × Bool → Bool. Both operands MUST be boolean —
        // JS `x && y` on non-booleans returns an operand *value* (via ToBoolean),
        // which we do not model, so a non-boolean operand is refused (not
        // coerced). `??` is out of the fragment.
        Expr::Logical { op, left, right } => match *op {
            "&&" => Ok(TypedIr::Bool(BoolIr::And(
                Box::new(lower_bool(left, ctx)?),
                Box::new(lower_bool(right, ctx)?),
            ))),
            "||" => Ok(TypedIr::Bool(BoolIr::Or(
                Box::new(lower_bool(left, ctx)?),
                Box::new(lower_bool(right, ctx)?),
            ))),
            other => Err(Refusal::UnsupportedConstruct {
                construct: format!("logical operator `{other}`"),
            }),
        },

        // `c ? t : e`: the condition MUST be boolean (we do not model ToBoolean
        // of a number — `a ? .. : ..` with numeric `a` is refused). Both branches
        // must have the SAME type T; the conditional's type is T.
        Expr::Cond { test, cons, alt } => {
            let t = lower_bool(test, ctx)?;
            let c = lower_typed(cons, ctx)?;
            let a = lower_typed(alt, ctx)?;
            match (c, a) {
                (TypedIr::Num(c), TypedIr::Num(a)) => Ok(TypedIr::Num(ArithIr::Cond {
                    test: Box::new(t),
                    cons: Box::new(c),
                    alt: Box::new(a),
                })),
                (TypedIr::Bool(c), TypedIr::Bool(a)) => Ok(TypedIr::Bool(BoolIr::Cond {
                    test: Box::new(t),
                    cons: Box::new(c),
                    alt: Box::new(a),
                })),
                _ => Err(Refusal::TypeError {
                    reason: "conditional branches have different types (one number, one boolean)"
                        .to_string(),
                }),
            }
        }

        // Everything else in the fragment is refused, by name for legibility.
        Expr::Str { .. } => {
            Err(Refusal::UnsupportedConstruct { construct: "string literal".to_string() })
        }
        Expr::Template { .. } | Expr::TaggedTemplate { .. } => {
            Err(Refusal::UnsupportedConstruct { construct: "template literal".to_string() })
        }
        Expr::Bool(_) => {
            Err(Refusal::UnsupportedConstruct { construct: "boolean literal".to_string() })
        }
        Expr::Null => Err(Refusal::UnsupportedConstruct { construct: "null".to_string() }),
        Expr::This => Err(Refusal::UnsupportedConstruct { construct: "this".to_string() }),
        // `Expr::Call` is handled above (a call to an earlier top-level function,
        // else a refusal). `new` / `super(...)` / `import(...)` are always out.
        Expr::New { .. } | Expr::SuperCall(_) | Expr::ImportCall(_) => {
            Err(Refusal::UnsupportedConstruct { construct: "call expression".to_string() })
        }
        Expr::Member { .. } | Expr::SuperProp(_) => {
            Err(Refusal::UnsupportedConstruct { construct: "member access".to_string() })
        }
        Expr::Update { op, .. } => {
            Err(Refusal::UnsupportedConstruct { construct: format!("update operator `{op}`") })
        }
        Expr::Assign { .. } => {
            Err(Refusal::UnsupportedConstruct { construct: "assignment expression".to_string() })
        }
        Expr::Seq(_) => {
            Err(Refusal::UnsupportedConstruct { construct: "comma sequence".to_string() })
        }
        Expr::Array { .. } => {
            Err(Refusal::UnsupportedConstruct { construct: "array literal".to_string() })
        }
        Expr::Object(_) => {
            Err(Refusal::UnsupportedConstruct { construct: "object literal".to_string() })
        }
        Expr::Function(_) | Expr::Arrow(_) | Expr::Class(_) => {
            Err(Refusal::UnsupportedConstruct { construct: "nested function / class".to_string() })
        }
        other => Err(Refusal::UnsupportedConstruct {
            construct: format!("unsupported expression: {other:?}"),
        }),
    }
}

/// Lower a binary operator, enforcing operand types.
fn lower_binary(op: &str, left: &Expr, right: &Expr, ctx: &LowerCtx) -> Result<TypedIr, Refusal> {
    match op {
        // Arithmetic: Num × Num → Num. `+` is numeric here BECAUSE both operands
        // are required to be Num — a string/BigInt/boolean operand is refused at
        // the operand, never lowered to Add (so `+` can never be concat).
        "+" | "-" | "*" | "/" | "%" => {
            let l = Box::new(lower_num(left, ctx)?);
            let r = Box::new(lower_num(right, ctx)?);
            Ok(TypedIr::Num(match op {
                "+" => ArithIr::Add(l, r),
                "-" => ArithIr::Sub(l, r),
                "*" => ArithIr::Mul(l, r),
                "/" => ArithIr::Div(l, r),
                "%" => ArithIr::Rem(l, r),
                _ => unreachable!("matched arithmetic op above"),
            }))
        }

        // Relational: Num × Num → Bool. JS abstract relational comparison on two
        // numbers is exactly the corresponding Rust `f64` comparison — proven per
        // sample by the ledger.
        "<" | "<=" | ">" | ">=" => {
            let l = Box::new(lower_num(left, ctx)?);
            let r = Box::new(lower_num(right, ctx)?);
            let cmp = match op {
                "<" => CmpOp::Lt,
                "<=" => CmpOp::Le,
                ">" => CmpOp::Gt,
                ">=" => CmpOp::Ge,
                _ => unreachable!("matched relational op above"),
            };
            Ok(TypedIr::Bool(BoolIr::Cmp { op: cmp, left: l, right: r }))
        }

        // Equality: either Num × Num → Bool or Bool × Bool → Bool. On two numbers
        // `==`/`===` do NO coercion (same type), so both are `f64 ==`
        // (`NaN != NaN`, `-0 == +0`); on two booleans both are `bool ==`. A MIXED
        // `Num == Bool` would coerce in JS — we REFUSE it (never coerce).
        "===" | "==" | "!==" | "!=" => {
            let lt = lower_typed(left, ctx)?;
            let rt = lower_typed(right, ctx)?;
            let is_eq = op == "===" || op == "==";
            match (lt, rt) {
                (TypedIr::Num(l), TypedIr::Num(r)) => {
                    let cmp = if is_eq { CmpOp::NumEq } else { CmpOp::NumNe };
                    Ok(TypedIr::Bool(BoolIr::Cmp {
                        op: cmp,
                        left: Box::new(l),
                        right: Box::new(r),
                    }))
                }
                (TypedIr::Bool(l), TypedIr::Bool(r)) => {
                    let beq = if is_eq { BoolEqOp::Eq } else { BoolEqOp::Ne };
                    Ok(TypedIr::Bool(BoolIr::BoolEq {
                        op: beq,
                        left: Box::new(l),
                        right: Box::new(r),
                    }))
                }
                _ => Err(Refusal::TypeError {
                    reason: format!(
                        "`{op}` compares a number with a boolean (the fragment does not coerce)"
                    ),
                }),
            }
        }

        // Bitwise / shift: Num × Num → Num, over ToInt32/ToUint32 (EXACT integer
        // functions — the OPPOSITE of a transcendental, so shipping is sound and the
        // same-oracle ledger validates rather than tautologizes). Both operands are
        // required Num — a boolean operand is a type error at `lower_num` (never
        // coerced), and a BigInt operand refuses at the operand as a BigInt literal
        // — so these can never be a BigInt-or string-coercing route.
        "|" | "&" | "^" | "<<" | ">>" | ">>>" => {
            let l = Box::new(lower_num(left, ctx)?);
            let r = Box::new(lower_num(right, ctx)?);
            Ok(TypedIr::Num(match op {
                "|" => ArithIr::BitOr(l, r),
                "&" => ArithIr::BitAnd(l, r),
                "^" => ArithIr::BitXor(l, r),
                "<<" => ArithIr::Shl(l, r),
                ">>" => ArithIr::Shr(l, r),
                ">>>" => ArithIr::UShr(l, r),
                _ => unreachable!("matched bitwise op above"),
            }))
        }

        // `**`, `instanceof`, `in`, ... — out of the fragment.
        other => {
            Err(Refusal::UnsupportedConstruct { construct: format!("binary operator `{other}`") })
        }
    }
}

/// Lower an expression and require it to be Num, else a type error (refuse).
fn lower_num(expr: &Expr, ctx: &LowerCtx) -> Result<ArithIr, Refusal> {
    match lower_typed(expr, ctx)? {
        TypedIr::Num(ir) => Ok(ir),
        TypedIr::Bool(_) => Err(Refusal::TypeError {
            reason: "expected a number here, found a boolean expression".to_string(),
        }),
    }
}

/// Lower an expression and require it to be Bool, else a type error (refuse).
fn lower_bool(expr: &Expr, ctx: &LowerCtx) -> Result<BoolIr, Refusal> {
    match lower_typed(expr, ctx)? {
        TypedIr::Bool(ir) => Ok(ir),
        TypedIr::Num(_) => Err(Refusal::TypeError {
            reason: "expected a boolean here, found a numeric expression".to_string(),
        }),
    }
}

/// Lower a call `g(e0, e1, ...)` to a strictly-earlier top-level function, or
/// refuse. An allow-listed `Math.<name>(args)` builtin call is intercepted FIRST
/// (see [`lower_math_call`]); everything else must be a direct call to an
/// earlier top-level function. The call-resolution rules (all fail-closed,
/// nothing emitted):
///   * the callee must be a plain identifier (a member/computed/other callee —
///     e.g. `obj.f(a)` — is refused as a call expression; the sole exception is a
///     `Math.<name>(...)` builtin, handled before this point);
///   * an optional call (`g?.(x)`) or a call inside an optional chain is refused;
///   * a name bound as a parameter / local is NOT callable — only earlier
///     top-level functions are (`Refusal::UnknownCallee`);
///   * the name must resolve to a function declared STRICTLY EARLIER in the module
///     (`ctx.fns`); a call to the current function itself, a later one, an
///     undeclared name, or any cycle cannot resolve and refuses as an unknown
///     callee (so recursion of every kind is impossible);
///   * the argument count must equal the callee's arity
///     (`Refusal::CallArityMismatch`); a spread argument is refused;
///   * every argument must be Num (a boolean argument is a `Refusal::TypeError`).
///
/// The result type is Num (every function returns Num). The callee's table index
/// is absolute (the position in `ctx.fns`, which equals its index in the final
/// module table), so it is a stable reference for eval and render.
fn lower_call(
    callee: &Expr,
    args: &[Arg],
    optional: bool,
    in_chain: bool,
    ctx: &LowerCtx,
) -> Result<TypedIr, Refusal> {
    if optional || in_chain {
        return Err(Refusal::UnsupportedConstruct {
            construct: "optional call / call in an optional chain".to_string(),
        });
    }
    // A `Math.<name>(...)` builtin call: a member callee whose object is the free
    // `Math` global (NOT shadowed by a parameter / local). Route to the allow-
    // listed Math lowering — a recognized builtin PROPOSES a JS-exact Rust
    // lowering the ledger then validates; anything else refuses. If `Math` is
    // shadowed by a param/local it is an ordinary value, so we fall through, and
    // the non-identifier-callee path below refuses the member call.
    if let Expr::Member { obj, prop, optional: m_opt, in_chain: m_chain } = callee
        && let Expr::Ident(obj_name) = obj.as_ref()
        && obj_name == "Math"
        && ctx.scope.lookup("Math").is_none()
    {
        if *m_opt || *m_chain {
            return Err(Refusal::UnsupportedConstruct {
                construct: "optional `Math` member call".to_string(),
            });
        }
        let PropKey::Ident(method) = prop.as_ref() else {
            return Err(Refusal::UnsupportedConstruct {
                construct: "Math computed / non-identifier member call".to_string(),
            });
        };
        return lower_math_call(method, args, ctx);
    }
    let Expr::Ident(name) = callee else {
        return Err(Refusal::UnsupportedConstruct {
            construct: "call expression with a non-identifier callee (only a direct call to an \
                        earlier top-level function by name is supported)"
                .to_string(),
        });
    };
    // A name bound as a parameter / local shadows any same-named earlier function
    // and is not itself callable in this fragment — refuse (never call a value).
    if ctx.scope.lookup(name).is_some() {
        return Err(Refusal::UnknownCallee { name: name.clone() });
    }
    // Resolve to a strictly-earlier top-level function (acyclic by order).
    let Some(callee_idx) = ctx.fns.iter().position(|f| f.name == *name) else {
        return Err(Refusal::UnknownCallee { name: name.clone() });
    };
    let callee_arity = ctx.fns[callee_idx].arity;
    if args.len() != callee_arity {
        return Err(Refusal::CallArityMismatch {
            name: name.clone(),
            expected: callee_arity,
            found: args.len(),
        });
    }
    let mut arg_irs: Vec<ArithIr> = Vec::with_capacity(args.len());
    for a in args {
        let Arg::Expr(e) = a else {
            return Err(Refusal::UnsupportedConstruct {
                construct: "spread argument in a call".to_string(),
            });
        };
        // Each argument must be a numeric (Num) expression — refuse a boolean arg.
        arg_irs.push(lower_num(e, ctx)?);
    }
    Ok(TypedIr::Num(ArithIr::Call { callee: callee_idx, args: arg_irs }))
}

/// Lower an allow-listed `Math.<method>(args)` builtin call, or refuse. For each
/// supported builtin this PROPOSES a JS-exact Rust lowering (`ArithIr::MathCall`);
/// the delta ledger then VALIDATES it bit-for-bit against the interp oracle over
/// the corpus (a divergence on ANY sample ⇒ Refusal, emitted nowhere). The
/// proposal is untrusted; the ledger is the authority.
///
/// Allow-list (everything else ⇒ `Refusal::UnsupportedConstruct`, including
/// `Math.random` — nondeterministic — `Math.hypot`, `Math.log`, trig, and every
/// TRANSCENDENTAL, `Math.pow` among them):
///   * unary (1 arg): `abs`, `floor`, `ceil`, `trunc`, `sqrt`, `sign`, `round`;
///   * binary (EXACTLY 2 args): `min`, `max`.
///
/// `min`/`max` are restricted to exactly 2 args (JS is variadic; ≠2 refuses, to
/// stay simple and sound). A wrong arity, a spread argument, or a boolean argument
/// refuses. Every argument must be Num. The result type is Num.
///
/// `Math.pow` is REFUSED: only operations whose Rust lowering is bit-identical to
/// JS for ALL inputs may ship (the IEEE-correctly-rounded ops above). `pow` is a
/// transcendental — IEEE-754 does not mandate a correctly-rounded `pow`, so
/// `f64::powf` is not bit-identical to JS `Math.pow` — and the oracle-check would
/// be a tautology (the interp uses the same `f64::powf`), so it cannot be validated
/// bit-exact. It falls back to the faithful tier. (Adversarial audit, 2026-07-23.)
fn lower_math_call(method: &str, args: &[Arg], ctx: &LowerCtx) -> Result<TypedIr, Refusal> {
    let op = match method {
        "abs" => MathOp::Abs,
        "floor" => MathOp::Floor,
        "ceil" => MathOp::Ceil,
        "trunc" => MathOp::Trunc,
        "sqrt" => MathOp::Sqrt,
        "sign" => MathOp::Sign,
        "round" => MathOp::Round,
        "min" => MathOp::Min,
        "max" => MathOp::Max,
        // `Math.pow` is a TRANSCENDENTAL: IEEE-754 does not mandate a correctly-
        // rounded `pow`, so `f64::powf` (platform libm) is not bit-identical to JS
        // `Math.pow` (V8), and an oracle-check against the interp — which computes
        // `Math.pow` with the SAME `f64::powf` — would be a tautology validating
        // nothing. It cannot be shipped bit-exact, so it REFUSES to the faithful
        // tier. (Adversarial audit finding, 2026-07-23.)
        "pow" => {
            return Err(Refusal::UnsupportedConstruct {
                construct: "Math.pow (transcendental — not IEEE-correctly-rounded, \
                            cannot be validated bit-exact vs JS)"
                    .to_string(),
            });
        }
        other => {
            return Err(Refusal::UnsupportedConstruct {
                construct: format!("Math.{other} (unsupported Math builtin)"),
            });
        }
    };
    let expected = op.arity();
    if args.len() != expected {
        return Err(Refusal::UnsupportedConstruct {
            construct: format!(
                "Math.{method} expects exactly {expected} argument(s), found {}",
                args.len()
            ),
        });
    }
    let mut arg_irs: Vec<ArithIr> = Vec::with_capacity(args.len());
    for a in args {
        let Arg::Expr(e) = a else {
            return Err(Refusal::UnsupportedConstruct {
                construct: format!("spread argument in a Math.{method} call"),
            });
        };
        // Every Math argument must be Num — refuse (never coerce) a boolean.
        arg_irs.push(lower_num(e, ctx)?);
    }
    Ok(TypedIr::Num(ArithIr::MathCall { op, args: arg_irs }))
}

// ===========================================================================
// Rendering (minimal-paren, precedence-correct)
// ===========================================================================

// A single precedence ladder over BOTH the numeric and boolean renderers
// (higher binds tighter). It mirrors Rust's grammar so `self_prec < parent_prec`
// inserts exactly the parens needed. The arithmetic rungs keep their relative
// order (ADD < MUL < UNARY < ATOM), so pure-arith output is byte-identical to
// before. A conditional (`if/else` expression) is the loosest rung, so it is
// parenthesized whenever it appears as any operand.
const PREC_COND: u8 = 1; // if <c> { t } else { e }
const PREC_OR: u8 = 2; // ||
const PREC_AND: u8 = 3; // &&
const PREC_CMP: u8 = 4; // < <= > >= == != (non-associative in Rust)
const PREC_ADD: u8 = 5; // + -
const PREC_MUL: u8 = 6; // * / %
const PREC_UNARY: u8 = 7; // unary - , !
const PREC_ATOM: u8 = 8; // param / literal

/// Render a NUMERIC IR node, parenthesizing iff `self_prec < parent_prec`.
/// `fns` supplies callee names for a `Call` node.
fn render_num(ir: &ArithIr, parent_prec: u8, fns: &[LoweredFn]) -> String {
    let (text, self_prec) = match ir {
        ArithIr::Param(i) => (format!("p{i}"), PREC_ATOM),
        ArithIr::Local(i) => (format!("l{i}"), PREC_ATOM),
        ArithIr::Lit(v) => (render_f64_lit(*v), PREC_ATOM),
        ArithIr::Neg(a) => {
            // Operand rendered at ATOM threshold: any binary or nested unary is
            // parenthesized (`-(a * b)`, `-(-x)`); atoms stay bare (`-p0`).
            let inner = render_num(a, PREC_ATOM, fns);
            // Safety belt: never emit `--` (would not be a valid Rust operator).
            let s =
                if inner.starts_with('-') { format!("-({inner})") } else { format!("-{inner}") };
            (s, PREC_UNARY)
        }
        ArithIr::Add(a, b) => (render_num_bin(a, "+", b, PREC_ADD, fns), PREC_ADD),
        ArithIr::Sub(a, b) => (render_num_bin(a, "-", b, PREC_ADD, fns), PREC_ADD),
        ArithIr::Mul(a, b) => (render_num_bin(a, "*", b, PREC_MUL, fns), PREC_MUL),
        ArithIr::Div(a, b) => (render_num_bin(a, "/", b, PREC_MUL, fns), PREC_MUL),
        ArithIr::Rem(a, b) => (render_num_bin(a, "%", b, PREC_MUL, fns), PREC_MUL),
        // JS bitwise / shift ops. Each renders as a SELF-PARENTHESIZED cast
        // (`(( … ) as f64)`), so the whole node is an ATOM — it binds tightest and
        // is never re-parenthesized by an outer operator, and its own inner parens
        // keep the `as` binding right. Operands render inside the `__js_to_*(…)`
        // call parens (a bottom-precedence position ⇒ parent_prec 0). The bodies are
        // IDENTICAL to `eval_num`'s (compile_check proves render ≡ eval).
        ArithIr::BitOr(a, b) => (render_bit_int_bin("|", a, b, fns), PREC_ATOM),
        ArithIr::BitAnd(a, b) => (render_bit_int_bin("&", a, b, fns), PREC_ATOM),
        ArithIr::BitXor(a, b) => (render_bit_int_bin("^", a, b, fns), PREC_ATOM),
        ArithIr::Shl(a, b) => {
            (render_bit_shift("__js_to_int32", "wrapping_shl", a, b, fns), PREC_ATOM)
        }
        ArithIr::Shr(a, b) => {
            (render_bit_shift("__js_to_int32", "wrapping_shr", a, b, fns), PREC_ATOM)
        }
        ArithIr::UShr(a, b) => {
            (render_bit_shift("__js_to_uint32", "wrapping_shr", a, b, fns), PREC_ATOM)
        }
        ArithIr::BitNot(a) => {
            (format!("((!__js_to_int32({})) as f64)", render_num(a, 0, fns)), PREC_ATOM)
        }
        ArithIr::Cond { test, cons, alt } => {
            (render_if(test, RenderBranch::Num(cons), RenderBranch::Num(alt), fns), PREC_COND)
        }
        // A call renders `name(a0, a1, ...)`. Each argument sits inside the call
        // parentheses (comma-separated), a bottom-precedence position needing no
        // outer parens, so render args at parent_prec 0. A call is an ATOM (binds
        // tightest, like a param), so it is never parenthesized by an operator.
        ArithIr::Call { callee, args } => {
            let name = fns.get(*callee).map_or("__unknown_callee", |f| f.name.as_str());
            let arglist = args.iter().map(|a| render_num(a, 0, fns)).collect::<Vec<_>>().join(", ");
            (format!("{name}({arglist})"), PREC_ATOM)
        }
        // A `Math.*` builtin renders either as a direct method call
        // (`<recv>.abs()`) or a JS-semantics helper call (`__js_math_min(a0, a1)`).
        // Both bind tightest (a method / function call is an ATOM), so the whole
        // node is never parenthesized by an outer operator.
        ArithIr::MathCall { op, args } => {
            let text = if let Some(method) = op.direct_method() {
                // Method-call receiver: postfix `.m()` binds tightest, so render the
                // receiver at ATOM threshold — any operator receiver is
                // parenthesized (`(p0 + p1).abs()`), an atom stays bare (`p0.abs()`).
                let recv = args
                    .first()
                    .map_or_else(|| "f64::NAN".to_string(), |a| render_num(a, PREC_ATOM, fns));
                format!("{recv}.{method}()")
            } else {
                // Helper call: args sit inside the call parens (a bottom-precedence
                // position needing no outer parens), so render each at parent 0.
                let name = op.helper_name().unwrap_or("__js_math_unknown");
                let arglist =
                    args.iter().map(|a| render_num(a, 0, fns)).collect::<Vec<_>>().join(", ");
                format!("{name}({arglist})")
            };
            (text, PREC_ATOM)
        }
    };
    if self_prec < parent_prec { format!("({text})") } else { text }
}

/// Render a BOOLEAN IR node, parenthesizing iff `self_prec < parent_prec`.
/// `fns` supplies callee names for any `Call` nested in a numeric operand.
fn render_bool(ir: &BoolIr, parent_prec: u8, fns: &[LoweredFn]) -> String {
    let (text, self_prec) = match ir {
        BoolIr::Local(i) => (format!("l{i}"), PREC_ATOM),
        BoolIr::Cmp { op, left, right } => {
            let sym = match op {
                CmpOp::Lt => "<",
                CmpOp::Le => "<=",
                CmpOp::Gt => ">",
                CmpOp::Ge => ">=",
                CmpOp::NumEq => "==",
                CmpOp::NumNe => "!=",
            };
            // Comparison is non-associative in Rust: render both numeric operands
            // one rung above CMP, so anything at/below comparison precedence (a
            // numeric conditional) is parenthesized.
            (
                format!(
                    "{} {sym} {}",
                    render_num(left, PREC_CMP + 1, fns),
                    render_num(right, PREC_CMP + 1, fns)
                ),
                PREC_CMP,
            )
        }
        BoolIr::BoolEq { op, left, right } => {
            let sym = match op {
                BoolEqOp::Eq => "==",
                BoolEqOp::Ne => "!=",
            };
            (
                format!(
                    "{} {sym} {}",
                    render_bool(left, PREC_CMP + 1, fns),
                    render_bool(right, PREC_CMP + 1, fns)
                ),
                PREC_CMP,
            )
        }
        // `&&` / `||` are left-associative: left child at own precedence, right
        // child one rung higher.
        BoolIr::And(a, b) => (
            format!("{} && {}", render_bool(a, PREC_AND, fns), render_bool(b, PREC_AND + 1, fns)),
            PREC_AND,
        ),
        BoolIr::Or(a, b) => (
            format!("{} || {}", render_bool(a, PREC_OR, fns), render_bool(b, PREC_OR + 1, fns)),
            PREC_OR,
        ),
        BoolIr::Not(a) => (format!("!{}", render_bool(a, PREC_UNARY, fns)), PREC_UNARY),
        BoolIr::Cond { test, cons, alt } => {
            (render_if(test, RenderBranch::Bool(cons), RenderBranch::Bool(alt), fns), PREC_COND)
        }
    };
    if self_prec < parent_prec { format!("({text})") } else { text }
}

/// A conditional branch to render — numeric or boolean.
enum RenderBranch<'a> {
    Num(&'a ArithIr),
    Bool(&'a BoolIr),
}

impl RenderBranch<'_> {
    fn render(&self, fns: &[LoweredFn]) -> String {
        // A branch sits inside `{ … }`, a block-tail position, so it needs no
        // outer parens regardless of its own precedence.
        match self {
            RenderBranch::Num(ir) => render_num(ir, 0, fns),
            RenderBranch::Bool(ir) => render_bool(ir, 0, fns),
        }
    }
}

/// Render `if <test> { <cons> } else { <alt> }`. The test is a boolean rendered
/// one rung above COND, so only a nested conditional test is parenthesized
/// (`if (if a {…} else {…}) {…}`); comparisons/logical stay bare.
fn render_if(
    test: &BoolIr,
    cons: RenderBranch<'_>,
    alt: RenderBranch<'_>,
    fns: &[LoweredFn],
) -> String {
    format!(
        "if {} {{ {} }} else {{ {} }}",
        render_bool(test, PREC_COND + 1, fns),
        cons.render(fns),
        alt.render(fns)
    )
}

/// Left-associative numeric binary render: left child at own precedence, right
/// child at one higher (so `a - (b - c)` and `a / (b / c)` keep their parens).
fn render_num_bin(l: &ArithIr, op: &str, r: &ArithIr, prec: u8, fns: &[LoweredFn]) -> String {
    format!("{} {op} {}", render_num(l, prec, fns), render_num(r, prec + 1, fns))
}

/// Render a bitwise `|`/`&`/`^` node as `((__js_to_int32(a) OP __js_to_int32(b)) as
/// f64)` — a self-parenthesized cast (see the `render_num` bitwise arms). Operands
/// sit inside the `__js_to_int32(…)` call parens, so each renders at parent 0.
fn render_bit_int_bin(sym: &str, a: &ArithIr, b: &ArithIr, fns: &[LoweredFn]) -> String {
    format!(
        "((__js_to_int32({}) {sym} __js_to_int32({})) as f64)",
        render_num(a, 0, fns),
        render_num(b, 0, fns)
    )
}

/// Render a shift node `((<conv>(a).<method>(__js_to_uint32(b) & 31)) as f64)`.
/// `conv` is `__js_to_int32` for `<<`/`>>` (arithmetic) or `__js_to_uint32` for
/// `>>>` (logical); `method` is `wrapping_shl` / `wrapping_shr`. The shift count is
/// `ToUint32(b) & 31` (ECMA-262 `shiftCount`), a `u32` in `[0, 31]`.
fn render_bit_shift(
    conv: &str,
    method: &str,
    a: &ArithIr,
    b: &ArithIr,
    fns: &[LoweredFn],
) -> String {
    format!(
        "(({conv}({}).{method}(__js_to_uint32({}) & 31)) as f64)",
        render_num(a, 0, fns),
        render_num(b, 0, fns)
    )
}

/// A bit-exact, readable Rust `f64` literal. Finite non-zero values use Rust's
/// shortest round-trip Debug form (always contains `.` or `e`, so it is a valid
/// float literal and, being correctly rounded on both sides, denotes the same
/// bits). All source `Lit`s are non-negative (JS has no negative literal token;
/// negatives are unary minus), so this never begins with `-` for a real `Lit`.
fn render_f64_lit(v: f64) -> String {
    if v.is_nan() {
        return "f64::NAN".to_string();
    }
    if v == f64::INFINITY {
        return "f64::INFINITY".to_string();
    }
    if v == f64::NEG_INFINITY {
        return "f64::NEG_INFINITY".to_string();
    }
    if v == 0.0 {
        return if v.is_sign_negative() { "-0.0".to_string() } else { "0.0".to_string() };
    }
    format!("{v:?}")
}

// ===========================================================================
// The delta ledger: fidelity check vs the independent semantics oracle
// ===========================================================================

/// Build the deterministic sample corpus for `arity` parameters:
///   * "axis probes" — every base edge value on every parameter position, with
///     the others pinned to 1.0 (guarantees per-parameter edge coverage even
///     when the cross-product is reduced);
///   * plus the full cartesian product of a per-parameter list — the full base
///     set when `base^arity <= max_samples`, else the largest reduced prefix
///     whose product fits.
///
/// Deduplicated bit-exactly, capped at the manifest's `max_samples`. The value
/// set and the cap both come from the pinned fidelity manifest
/// ([`fidelity::pin`]) rather than from a constant here, so narrowing either
/// one is manifest drift a reviewer sees, not an edit in the same file as the
/// lowering that was failing on it.
fn build_samples(arity: usize) -> Vec<Vec<f64>> {
    if arity == 0 {
        return vec![Vec::new()];
    }
    let pin = fidelity::pin();
    let max_samples = pin.max_samples();
    let base = pin.base_samples();

    // Axis probes first (so their coverage survives the cap).
    let mut raw: Vec<Vec<f64>> = Vec::new();
    for i in 0..arity {
        for &e in base {
            let mut t = vec![1.0_f64; arity];
            t[i] = e;
            raw.push(t);
        }
    }

    // Per-parameter list length: full base if the full product fits, else the
    // largest `m` with `m^arity <= max_samples` (at least 1).
    let full_fits = base.len().checked_pow(arity as u32).is_some_and(|s| s <= max_samples);
    let per = if full_fits {
        base.len()
    } else {
        let mut m = 1usize;
        while (m + 1).checked_pow(arity as u32).is_some_and(|s| s <= max_samples) {
            m += 1;
        }
        m
    };
    let list = &base[..per];

    // Cartesian product via a mixed-radix counter (fully deterministic).
    if let Some(total) = list.len().checked_pow(arity as u32) {
        for n in 0..total {
            let mut t = Vec::with_capacity(arity);
            let mut r = n;
            for _ in 0..arity {
                t.push(list[r % list.len()]);
                r /= list.len();
            }
            raw.push(t);
        }
    }

    // Dedup bit-exactly, preserving order, capping at the manifest's bound.
    let mut seen: std::collections::HashSet<Vec<u64>> = std::collections::HashSet::new();
    let mut out: Vec<Vec<f64>> = Vec::new();
    for t in raw {
        let key: Vec<u64> = t.iter().map(|v| v.to_bits()).collect();
        if seen.insert(key) {
            out.push(t);
            if out.len() >= max_samples {
                break;
            }
        }
    }
    out
}

/// The array shapes the fold fidelity check runs over, as fixed by the pinned
/// manifest ([`fidelity::pin`]): the empty array; a singleton of every scalar
/// edge value; a few all-same, ascending, NaN-containing, ±0-containing, and
/// ±Inf-containing arrays; a mixed edge array; and a couple of everyday arrays.
/// Fixed order, so the corpus is byte-deterministic.
fn build_array_corpus() -> Vec<Vec<f64>> {
    fidelity::pin().array_corpus().to_vec()
}

/// Build the deterministic fold corpus for `scalar_arity` scalar params: the full
/// array corpus crossed with the scalar tuples ([`build_samples`]). The array
/// corpus is kept whole; the scalar tuples are reduced to a prefix so the product
/// stays within the manifest's fold sample cap.
fn build_fold_corpus(scalar_arity: usize) -> Vec<(Vec<f64>, Vec<f64>)> {
    let arrays = build_array_corpus();
    let scalar_tuples = build_samples(scalar_arity);
    let max_scalars = (fidelity::pin().fold_max_samples() / arrays.len().max(1)).max(1);
    let used: &[Vec<f64>] = if scalar_tuples.len() > max_scalars {
        &scalar_tuples[..max_scalars]
    } else {
        &scalar_tuples
    };
    let mut out = Vec::with_capacity(arrays.len() * used.len());
    for a in &arrays {
        for s in used {
            out.push((a.clone(), s.clone()));
        }
    }
    out
}

/// Two f64 values denote the SAME JS Number iff they are bit-identical, EXCEPT
/// that all NaNs are one observable JS number (a pure-arith function's only
/// observable is its Number result, and JS collapses every NaN payload — the
/// interp projection already renders them all as `"NaN"`). This is the strict
/// notion the task wants: `-0.0 != 0.0`, `±Infinity` exact, all finite exact,
/// and `NaN == NaN`.
fn same_js_number(a: f64, b: f64) -> bool {
    if a.is_nan() && b.is_nan() { true } else { a.to_bits() == b.to_bits() }
}

/// Run the fidelity check: for every sample, compare [`eval_func`] (which
/// materializes the local bindings, then evaluates the return) against the interp
/// oracle bit-for-bit. The oracle evaluates the ORIGINAL source (bindings and
/// all) and returns a Number, so the same per-sample check covers the bindings
/// for free — a subtly wrong binding / slot / return mapping produces a
/// divergence. Returns an all-equal ledger, or a `Refusal` (oracle unavailable,
/// or a caught divergence). The oracle is NEVER faked: a sample the oracle cannot
/// answer with a number refuses the whole lowering.
#[cfg(test)]
fn check_fidelity(
    js: &str,
    name: &str,
    bindings: &[Binding],
    ret: &ArithIr,
    arity: usize,
) -> Result<DeltaLedger, Refusal> {
    // A single-function module: wrap the one function and check its entry (index
    // 0). This preserves the floor's check semantics exactly (no cross-function
    // calls), so it is the natural degenerate case of the module check.
    let functions = vec![LoweredFn {
        name: name.to_string(),
        arity,
        bindings: bindings.to_vec(),
        ret_ir: ret.clone(),
    }];
    check_fidelity_module(js, &functions, 0)
}

/// Run the fidelity check for a WHOLE module: for every sample over the ENTRY
/// function's arity, compare [`eval_module`] (which runs the entry, resolving
/// helper calls through the function table) against the interp oracle bit-for-bit.
/// The oracle evaluates the ORIGINAL source — ALL function declarations, hoisted —
/// with a call to the entry appended, so the SAME per-sample check covers the
/// helper calls and bindings for free: a subtly wrong callee, argument, slot, or
/// return mapping produces a per-sample divergence and the whole module refuses.
/// Returns an all-equal ledger, or a `Refusal` (oracle unavailable, or a caught
/// divergence). The oracle is NEVER faked: a sample the oracle cannot answer with
/// a number refuses the whole lowering.
fn check_fidelity_module(
    js: &str,
    functions: &[LoweredFn],
    entry: usize,
) -> Result<DeltaLedger, Refusal> {
    let arity = functions[entry].arity;
    let name = functions[entry].name.as_str();
    let samples = build_samples(arity);
    let mut checked = 0usize;
    for input in &samples {
        let rust = eval_module(functions, entry, input);
        let js_val = match oracle_eval(js, name, input) {
            Ok(v) => v,
            Err(reason) => return Err(Refusal::OracleUnavailable { input: input.clone(), reason }),
        };
        if !same_js_number(js_val, rust) {
            return Err(Refusal::FidelityDivergence {
                input: input.clone(),
                js: projection_number_repr(js_val),
                rust: projection_number_repr(rust),
            });
        }
        checked += 1;
    }
    Ok(DeltaLedger { samples_checked: checked, all_equal: true, first_divergence: None })
}

/// Run the fidelity check for an ARRAY-FOLD (increment 6): for every (array,
/// scalar-tuple) in the fold corpus, compare [`eval_fold`] (the left-to-right
/// reduction) against the interp oracle bit-for-bit. The oracle evaluates the
/// ORIGINAL source with a REAL for-of call appended — `f([e0, e1, …], s0, …)` — so
/// JS reduction semantics (left-to-right order, NaN propagation through `+`, signed
/// zero) are the authority; a subtly wrong init / step / return / slot mapping
/// produces a per-sample divergence and the whole lowering refuses. Returns an
/// all-equal ledger, or a `Refusal` (oracle unavailable, or a caught divergence).
/// The oracle is NEVER faked: a sample it cannot answer with a number refuses.
fn check_fidelity_fold(
    js: &str,
    helpers: &[LoweredFn],
    fold: &FoldFn,
) -> Result<DeltaLedger, Refusal> {
    let corpus = build_fold_corpus(fold.scalar_arity);
    let mut checked = 0usize;
    for (array, scalars) in &corpus {
        let rust = eval_fold(fold, helpers, array, scalars);
        let arglist = fold_arglist(array, scalars);
        let js_val = match oracle_eval_call(js, &fold.name, &arglist) {
            Ok(v) => v,
            Err(reason) => {
                let mut input = array.clone();
                input.extend_from_slice(scalars);
                return Err(Refusal::OracleUnavailable { input, reason });
            }
        };
        if !same_js_number(js_val, rust) {
            let mut input = array.clone();
            input.extend_from_slice(scalars);
            return Err(Refusal::FidelityDivergence {
                input,
                js: projection_number_repr(js_val),
                rust: projection_number_repr(rust),
            });
        }
        checked += 1;
    }
    Ok(DeltaLedger { samples_checked: checked, all_equal: true, first_divergence: None })
}

/// The JS argument list for a fold oracle call: the array literal, then each scalar
/// as a bit-exact JS literal — `[e0, e1, …], s0, s1, …` (just the array when there
/// are no scalars).
fn fold_arglist(array: &[f64], scalars: &[f64]) -> String {
    let mut parts = Vec::with_capacity(1 + scalars.len());
    parts.push(js_array_literal(array));
    for &s in scalars {
        parts.push(js_literal(s));
    }
    parts.join(", ")
}

/// A JS array literal `[e0, e1, …]` whose elements are the bit-exact scalar
/// literals of `elems` (empty array => `[]`).
fn js_array_literal(elems: &[f64]) -> String {
    let inner = elems.iter().map(|&e| js_literal(e)).collect::<Vec<_>>().join(", ");
    format!("[{inner}]")
}

/// Evaluate `name(args...)` against the ORIGINAL JS source through the interp
/// oracle (§4 object 1) and return the exact JS Number result. We append a call
/// to the user's real source (never a re-render), so the oracle judges what the
/// JS actually means. The projected completion value round-trips bit-exactly
/// back to f64 (the projection is the canonical ECMA-262 shortest decimal with
/// `-0` distinguished; NaN/±Infinity are canonical tokens).
fn oracle_eval(js: &str, name: &str, args: &[f64]) -> Result<f64, String> {
    let arglist = args.iter().map(|v| js_literal(*v)).collect::<Vec<_>>().join(", ");
    oracle_eval_call(js, name, &arglist)
}

/// Evaluate `name(<arglist>)` against the ORIGINAL JS source through the interp
/// oracle, where `arglist` is a pre-built JS argument string (a scalar list for a
/// plain function, or an array literal + scalars for a fold). See [`oracle_eval`].
fn oracle_eval_call(js: &str, name: &str, arglist: &str) -> Result<f64, String> {
    let src = format!("{js}\n{name}({arglist})");
    match evaluate_case_opts(&[], &src, false, true) {
        InterpOutcome::Trace(t) => match t.completion {
            Completion::Normal { v: Some(ProjectedValue::Num { v }) } => {
                parse_projected_num(&v).ok_or_else(|| format!("unparseable projected number {v:?}"))
            }
            Completion::Normal { v: Some(other) } => {
                Err(format!("oracle returned a non-number completion: {other:?}"))
            }
            Completion::Normal { v: None } => {
                Err("oracle returned no completion value".to_string())
            }
            other => Err(format!("oracle abrupt/other completion: {other:?}")),
        },
        InterpOutcome::NoCoverage { reason } => Err(format!("interp NoCoverage: {reason}")),
    }
}

/// A JS expression whose ToNumber is bit-exactly `v` (for passing a sample into
/// the oracle). Finite values use the shortest round-trip decimal (which the
/// interp lexes back to the identical f64); specials use the number globals.
fn js_literal(v: f64) -> String {
    if v.is_nan() {
        return "NaN".to_string();
    }
    if v == f64::INFINITY {
        return "Infinity".to_string();
    }
    if v == f64::NEG_INFINITY {
        return "(-Infinity)".to_string();
    }
    if v == 0.0 {
        // `-0` is unary minus of the 0 literal => -0.0; `0` => +0.0.
        return if v.is_sign_negative() { "(-0)".to_string() } else { "0".to_string() };
    }
    let s = trust_js_value::js_number_to_string(v);
    // Negative finite => unary minus of a positive literal; parenthesize so it
    // is unambiguous in argument position.
    if s.starts_with('-') { format!("({s})") } else { s }
}

/// Parse a projected number repr (from the interp) back to an exact f64.
fn parse_projected_num(repr: &str) -> Option<f64> {
    match repr {
        "NaN" => Some(f64::NAN),
        "Infinity" => Some(f64::INFINITY),
        "-Infinity" => Some(f64::NEG_INFINITY),
        "-0" => Some(-0.0),
        // Every other repr is the canonical shortest decimal, which Rust's
        // correctly-rounded parser reads back to the identical f64.
        other => other.parse::<f64>().ok(),
    }
}

// The pinned evidence: the oracle, the input domains, and the (empty) waiver
// list, loaded from a compile-time manifest whose digest covers every value.
// This crate reads its own corpus; it does not choose it.
pub mod fidelity;

#[cfg(test)]
mod tests;

// Empirical render-fidelity check: compile the ACTUAL rendered `rust_source`
// with the real rustc and prove it bit-equals `eval_ir` on the corpus. Closes
// the audit gap that `check_fidelity` never executes the rendered string.
#[cfg(test)]
mod compile_check;
