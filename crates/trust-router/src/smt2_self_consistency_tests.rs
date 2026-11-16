// trust-router/smt2_self_consistency_tests.rs: the transcript is its own witness.
//
// A `problem_smt2` transcript is EVIDENCE — it is what the Carcara N-version
// cross-check replays and what the revalidation digest is taken over. Evidence
// that a solver would reject is not evidence, so the property pinned here is
// the transcript's INTERNAL consistency:
//
//     for every formula the lane accepts, the `(set-logic L)` line the
//     transcript opens with admits every sort its own `(declare-*)` lines
//     declare and every symbol and operator its own `(assert …)` applies.
//
// This is deliberately checked by PARSING THE EMITTED TEXT rather than by
// re-asking `detect_logic`: the defect class this file exists to close is
// exactly a classifier and a declarer walking different lists, and a test that
// consults the classifier again would agree with the bug. What the parsed
// `(set-logic L)` name is measured against is the ONE admissibility table,
// `trust_types::logic_lattice::LOGIC_LATTICE` — the same data the selector
// chose `L` by, read here rather than copied, so the two cannot drift. An
// unlisted name or an unclassified token is a test FAILURE, not a silent pass,
// so a logic name or an operator added later cannot slip through this file
// unexamined.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};

use trust_types::logic_lattice::Theories;
use trust_types::smt_logic::check_formula_sort;
use trust_types::{Formula, RoundingMode, Sort};

use crate::in_process_ay_backend::problem_smt2;

// This module is gated on `ay-backend` in lib.rs: `problem_smt2` — the
// canonical transcript this file is about — lives behind that feature. The
// `_tests` suffix is what `scripts/check_tcb_panic_freedom.sh` recognizes as a
// test-named file, so this file's assertion machinery is not charged to the
// TCB's production panic surface.

// ─────────────────────────────────────────────────────────────────────────────
// 1. WHAT A LOGIC NAME ADMITS (the shared table, read not copied)
// ─────────────────────────────────────────────────────────────────────────────

/// One theory requirement a transcript makes of its own logic line.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Req {
    /// A `forall`/`exists` binder appears in the assertion.
    Quantifiers,
    /// An `(Array _ _)` sort is declared, or `select`/`store` is applied.
    Arrays,
    /// A `(_ BitVec n)` sort is declared, or a bitvector literal/operator is
    /// applied.
    BitVectors,
    /// The `Int` sort, or an integer-only operator (`div`, `mod`, `bv2nat`).
    Ints,
    /// The `Real` sort, or the rational division operator `/`.
    Reals,
    /// A bare numeral, or a sort-generic arithmetic/ordering operator
    /// (`+ - * < <= > >=`). SMT-LIB numerals are `Int` terms in an integer
    /// logic and `Real` terms in a reals logic, so EITHER theory admits them.
    Numeric,
    /// A `(_ FloatingPoint e s)` or `RoundingMode` sort, or an `fp.*`
    /// operator/literal/rounding-mode constant.
    Floats,
    /// A `(declare-fun f (A …) R)` of arity >= 1 — an uninterpreted FUNCTION.
    /// A 0-ary `declare-fun` is an ordinary free constant, which every SMT-LIB
    /// logic admits, so it makes no `Uf` requirement of its own.
    Uf,
    /// A `(declare-datatype …)`, a `(declare-sort N 0)` standing in for a
    /// datatype back-edge, a datatype sort identifier in a declaration, or a
    /// constructor/selector/tester application.
    Datatypes,
    /// An arithmetic term OUTSIDE the linear fragment: any `div`/`mod`/`abs`
    /// application, a `/` whose operands are not all constant, or a `*` that
    /// is not `constant × free constant symbol` (in either order).
    ///
    /// WRITTEN FROM THE [S1] DECLARATIONS, NOT FROM THE CLASSIFIER. `QF_LIA`'s
    /// `:language` admits "no occurrences of the function symbols `**`, `/`,
    /// `div`, `mod`, and `abs`, and no occurrences of the function symbol `*`,
    /// except as specified in the :extensions attribute", and the extension is
    /// "terms of the form `c`, `(* c x)`, or `(* x c)` where `x` is a free
    /// constant and `c` is a term of the form `n` or `(- n)`"; `QF_LRA` reads
    /// the same over `*` and `/` with rational coefficients. So `(div x 2)` is
    /// NOT a `QF_LIA` term — the numeral divisor buys nothing — and
    /// `(* 3 (+ x y))` is not either.
    ///
    /// THE REQUIREMENT IS ON THE TEXT, NOT ON THE `Formula`. A `QF_LIA` header
    /// over `(assert (> (* x y) 0))` is a transcript whose own assertion its
    /// logic line does not admit — the linear integer logic is defined over
    /// linear terms only — and that is exactly the class of disagreement this
    /// file exists to catch, read here off the emitted s-expression.
    ///
    /// DELIBERATELY NO STRONGER THAN THE SELECTOR'S RULE, in the safe
    /// direction. `trust_types::logic_lattice::node_theories` decides linearity
    /// by a SHALLOW test on the `Formula` (a coefficient times a `Var`/`SymVar`
    /// of arithmetic sort), so it over-approximates: `(* x (+ 2 3))` charges
    /// `NONLINEAR` there, and so does a coefficient times a 0-ary declared
    /// symbol. The check below folds `(- n)`, `(/ n m)` and bare numerals into
    /// "constant", accepts ANY 0-ary declared or bound symbol as the free
    /// constant, and so charges NO MORE OFTEN than the selector did. That
    /// ordering matters: if this checker charged MORE than the selector, a
    /// transcript the selector headed correctly would fail here.
    Nonlinear,
    /// An arithmetic ATOM that is NOT difference-shaped appears — i.e. the
    /// transcript needs the full `LIA`/`LRA` atom grammar and not SMT-LIB's
    /// `QF_IDL`/`QF_RDL` subfragment.
    ///
    /// THE REQUIREMENT THIS FILE EXISTED WITHOUT, AND THE ONE IT WAS MOST
    /// NEEDED FOR. `Theories::WIDE_ARITH` was added to the shared record to
    /// stop an over-narrow `(set-logic QF_IDL)` from heading a general
    /// arithmetic transcript — the same defect class this checker DID catch for
    /// datatype field sorts, one dimension over — and until this variant landed
    /// the checker had no vocabulary for it, so a `QF_IDL` header over
    /// `(assert (<= (+ x y) 10))` passed here silently. It is silent in-house
    /// too: ay maps `QF_IDL` onto its full `QfLia` solver and enforces no
    /// fragment restriction, so only an external replayer would reject the
    /// evidence. `an_over_narrow_difference_logic_header_is_rejected` plants
    /// exactly that defect and asserts this requirement catches it.
    ///
    /// THE REQUIREMENT IS READ OFF THE TEXT, NOT OFF THE `Formula`, and the
    /// recognizer ([`is_difference_shaped_atom`]) is written from the [S1]
    /// declarations quoted on `trust_types::logic_lattice::LOGIC_LATTICE`
    /// rather than by calling `wide_arithmetic_theories`. Importing the
    /// production classifier would make this checker agree with that
    /// classifier's bugs, which is the one thing this file may never do.
    ///
    /// DELIBERATELY WEAKER THAN THE SELECTOR'S RULE, IN THE SAFE DIRECTION —
    /// the same ordering [`Req::Nonlinear`] is written under, and here it is
    /// what makes two independent rules safe to hold apart.
    /// `logic_lattice::is_difference_atom` recognizes THREE shapes and refuses
    /// the bare bound `x ▷◁ k` (neither declaration lists it), so production
    /// charges `WIDE_ARITH` for `(> x 3)` and heads `QF_LIA`. The recognizer
    /// below accepts a STRICTLY LARGER set of atoms — the bare bound, the
    /// mirrored forms, and a fully recursive closed-term test for the bound —
    /// so it charges this requirement NO MORE OFTEN than production charged the
    /// bit. That ordering is what makes a false FAILURE impossible: the only
    /// rows admitting an arithmetic sort WITHOUT `WIDE_ARITH` are `QF_IDL` and
    /// `QF_RDL`; production emits those only when ITS narrower recognizer
    /// accepted every atom, and every atom it accepts this one accepts too.
    WideArith,
    /// An `(Array I E)` sort is written whose `I`/`E` are NOT both `Int` and
    /// NOT both positive-width `(_ BitVec n)` — so the transcript needs a name
    /// whose declaration admits an ARBITRARY array sort, not one of the
    /// `*ALIA`/`*ABV*` names.
    ///
    /// WRITTEN FROM THE [S1] DECLARATIONS. `QF_AUFLIA`: "all array terms have
    /// sort `(Array Int Int)`". `QF_ABV`: "all array terms have sort of the
    /// form `(Array (_ BitVec i) (_ BitVec j))` for some `i, j > 0`". `QF_AX`
    /// and `AUFNIRA` place no restriction on array sorts (though `QF_AX` admits
    /// no `Int` sort and `AUFNIRA` no `BitVec` sort; the base-sort requirements
    /// charged alongside settle which of them, or `ALL`, is legal). So a
    /// `(Array Bool Bool)`, a nested array, a mixed `(Array Int (_ BitVec 8))`
    /// or a zero-width bitvector array (not a legal sort at all) is charged
    /// here, read off the `declare-fun` / binder / datatype field sort as
    /// written, and only a row carrying `Theories::WIDE_ARRAY` admits it.
    ///
    /// SAME RULE AS PRODUCTION'S, which is the safe direction here: the shape
    /// test is a total function of the two written sorts, so there is no
    /// recognizer to be more or less permissive about, and
    /// `logic_lattice::sort_theories` charges the bit on exactly these shapes.
    WideArray,
}

/// What ONE SMT-LIB logic name admits — READ FROM THE SHARED TABLE, not from a
/// second hand-written copy.
///
/// The admissibility table used to be written out again in this file, one row
/// per logic name, on the argument that a test which re-asks the classifier
/// would agree with the classifier's bug. That argument is still right, and it
/// is satisfied WITHOUT a second copy: this file never asks `detect_logic`
/// anything — it PARSES THE EMITTED TEXT and looks the parsed `(set-logic L)`
/// name up in [`trust_types::logic_lattice::LOGIC_LATTICE`], the same data the
/// selector chose `L` by. What that catches is a disagreement between the LOGIC
/// LINE and the DECLARATIONS AND ASSERTION beside it, which is a property of
/// the transcript, not of the table. Two copies of the table could drift from
/// each other, and the drift would make this checker pass a transcript the
/// selector mislabelled — precisely the failure mode the copy was meant to
/// prevent.
///
/// An unlisted name is still a test FAILURE, so a logic name added to the
/// selector without a row cannot slip through here unexamined.
fn admissibility(logic: &str) -> Theories {
    trust_types::logic_lattice::logic_admits(logic).unwrap_or_else(|| {
        panic!(
            "no admissibility row for logic `{logic}`: a logic name reached a transcript \
             without a row in `trust_types::logic_lattice::LOGIC_LATTICE` saying what it \
             admits, so nothing checks that the transcripts it heads are well formed"
        )
    })
}

/// Whether the logic that admits `admits` admits one transcript requirement.
///
/// The only requirement that is not a single lattice dimension is
/// [`Req::Numeric`]: a bare numeral or a sort-generic arithmetic operator is an
/// `Int` term in an integer logic and a `Real` term in a reals logic, so EITHER
/// arithmetic theory admits it. ([`Req::Nonlinear`] IS a single dimension —
/// `Theories::NONLINEAR` — but it is the only one charged from an application's
/// ARGUMENTS rather than from a sort or an operator name; see
/// [`linearity_requirement`]. [`Req::WideArith`] is a single dimension too, and
/// the only one charged from a WHOLE ATOM rather than from any one node; see
/// [`linear_form_requirements`].)
fn allows(admits: Theories, req: Req) -> bool {
    match req {
        Req::Quantifiers => admits.contains(Theories::QUANTIFIERS),
        Req::Arrays => admits.contains(Theories::ARRAYS),
        Req::BitVectors => admits.contains(Theories::BITVECTORS),
        Req::Ints => admits.contains(Theories::INTS),
        Req::Reals => admits.contains(Theories::REALS),
        Req::Numeric => admits.contains(Theories::INTS) || admits.contains(Theories::REALS),
        Req::Floats => admits.contains(Theories::FLOATS),
        Req::Uf => admits.contains(Theories::UF),
        Req::Datatypes => admits.contains(Theories::DATATYPES),
        Req::Nonlinear => admits.contains(Theories::NONLINEAR),
        Req::WideArith => admits.contains(Theories::WIDE_ARITH),
        Req::WideArray => admits.contains(Theories::WIDE_ARRAY),
    }
}

/// Whether a term in the emitted text is a NUMERIC CONSTANT — the shape a
/// product may be multiplied by, or a quotient divided by, and stay LINEAR.
///
/// The three forms this workspace's lowering can produce for one: a bare
/// numeral (`Int`/`UInt`), `(- n)` (a negative literal, and the numerator of a
/// negative `Rat`) and `(/ n m)` (a `Rat`'s `Reals`-theory spelling, per
/// `trust_ir_contract::RatLit::to_smtlib`). A decimal literal counts too.
///
/// It stops there on purpose: see [`Req::Nonlinear`] for why this must charge
/// no MORE than `logic_lattice::node_theories` does.
///
/// The grammar is the declarations', not a recursive closure: ONE negation of a
/// bare numeral or decimal (`(- (- 3))` is neither `n` nor `(- n)`), and a
/// quotient only of an integer coefficient over a bare numeral (`QF_LRA`'s
/// `(/ c n)`), so `(- (/ 1 2))` and `(/ (/ 1 2) 3)` are not coefficients.
fn is_constant_term(term: &Sexp) -> bool {
    let bare = |t: &Sexp| matches!(t, Sexp::Atom(a) if is_numeral_atom(a));
    let integer = |t: &Sexp| matches!(t, Sexp::Atom(a) if is_numeral_atom(a) && !a.contains('.'));
    match term {
        Sexp::Atom(_) => bare(term),
        Sexp::List(items) => match items.as_slice() {
            [Sexp::Atom(head), operand] if head == "-" => bare(operand),
            [Sexp::Atom(head), num, den] if head == "/" => {
                let negated_integer = matches!(num, Sexp::List(n) if matches!(n.as_slice(),
                    [Sexp::Atom(h), m] if h == "-" && integer(m)));
                (integer(num) || negated_integer) && integer(den)
            }
            _ => false,
        },
    }
}

/// The LINEARITY requirement of ONE application, given its head and its
/// ARGUMENTS — the one requirement that is not a property of the head alone.
///
/// `(* 3 x)` is a linear term of `QF_LIA` and `(* x y)` is not, and the two are
/// the same operator. The rule is the [S1] `:extensions` clause quoted on
/// [`Req::Nonlinear`]: a product is linear iff all but at most ONE of its
/// operands are constant terms and that one, if present, is a FREE CONSTANT
/// SYMBOL — a 0-ary declared or quantifier-bound name, the same test
/// [`is_free_constant_symbol`] applies for the difference grammar. (SMT-LIB's
/// `*` is n-ary, so this is written over the whole operand list.)
///
/// `div`/`mod`/`abs` are charged UNCONDITIONALLY: the linear declarations
/// exclude them by name, with no numeral-divisor exception. `rem` is kept in
/// that list against a lowering that might one day spell it. `/` is charged
/// unless every operand is constant — a rational coefficient `(/ 1 2)` is a
/// term of `QF_LRA`; `(/ r t)` over two symbols is not.
fn linearity_requirement(
    head: &str,
    args: &[Sexp],
    declared: &Declared,
    bound: &[String],
    out: &mut Vec<(Req, String)>,
) {
    let (nonlinear, why) = match head {
        "*" => {
            let non_constant: Vec<&Sexp> =
                args.iter().filter(|arg| !is_constant_term(arg)).collect();
            let linear = match non_constant.as_slice() {
                [] => true,
                [single] => is_free_constant_symbol(single, declared, bound),
                _ => false,
            };
            (
                !linear,
                "the assertion applies `*` other than as `(* c x)` with `c` a constant \
                       and `x` a free constant symbol",
            )
        }
        "div" | "mod" | "abs" | "rem" => {
            (true, "the assertion applies an operator the linear declarations exclude by name")
        }
        "/" => (
            !args.iter().all(is_constant_term),
            "the assertion applies `/` other than as a rational coefficient",
        ),
        _ => (false, ""),
    };
    if nonlinear {
        out.push((Req::Nonlinear, format!("{why} (`{head}`)")));
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// 1b. THE LINEAR-FORM REQUIREMENT — difference atoms, read off the s-expression
// ─────────────────────────────────────────────────────────────────────────────
//
// SMT-LIB's two DIFFERENCE logics admit a STRICT SUBFRAGMENT of integer (resp.
// real) arithmetic: only Boolean combinations of the atom shapes their [S1]
// declarations list. `trust_types::logic_lattice` carries them as the two rows
// that name an arithmetic sort and do NOT carry `Theories::WIDE_ARITH`, so a
// record of `{INTS}` selects `QF_IDL` and `{INTS, WIDE_ARITH}` selects
// `QF_LIA`. A transcript whose record LOST the wide bit is therefore headed by
// a name admitting only `x - y ▷◁ n` over an assertion that is not in that
// grammar — an over-narrow header, exactly what this file exists to catch, and
// the reason `Theories::WIDE_ARITH` was added in the first place.
//
// THE RULES BELOW ARE WRITTEN FROM THE DECLARATIONS, NOT FROM THE CLASSIFIER.
// Nothing here calls `wide_arithmetic_theories`, `is_difference_atom` or any
// other production entry point: a checker that re-asks the classifier agrees
// with the classifier's bugs, which is the whole reason this module parses text.
// What it is measured against is the shared ADMISSIBILITY TABLE alone — the
// same row the selector chose the name by — exactly as every other requirement
// in this file is.
//
// THE RECOGNIZER IS DELIBERATELY MORE PERMISSIVE THAN PRODUCTION'S, which is
// the direction that cannot produce a false failure; see [`Req::WideArith`] for
// the argument. The extra shapes are the BARE BOUND `(op x k)` (which neither
// declaration lists, so production widens on it), the MIRRORED forms, and a
// fully recursive closed-term test for the bound `k`.

/// True iff `term` is a CLOSED NUMERIC TERM — an arithmetic term with no symbol
/// anywhere inside it, which is what the bound `k` of a difference atom may be.
///
/// FULLY RECURSIVE, DELIBERATELY. The declarations' bound is `m` or `(- m)` for
/// a numeral `m`, and this workspace's lowering can also put a folded constant
/// there (`(- 3)`, `(/ 3 4)` for a rational, `(+ 1 2)` from a partially folded
/// term). A test that stopped at a bare numeral would call those atoms
/// non-difference and charge the requirement more often than production charged
/// the bit — the one direction that turns a correctly-headed transcript into a
/// failure here. Recursing can only recognize MORE, which can only charge LESS.
fn is_closed_numeric_term(term: &Sexp) -> bool {
    match term {
        Sexp::Atom(atom) => is_numeral_atom(atom),
        Sexp::List(items) => match items.split_first() {
            Some((Sexp::Atom(head), args)) if !args.is_empty() => {
                matches!(head.as_str(), "+" | "-" | "*" | "/")
                    && args.iter().all(is_closed_numeric_term)
            }
            _ => false,
        },
    }
}

/// True iff `atom` is an SMT-LIB NUMERAL or DECIMAL literal.
///
/// Separate from [`is_constant_term`] on purpose: that predicate answers "is
/// this a LINEAR multiplier", a question about the `N`-family dimension, and
/// `trust_types::logic_lattice` keeps its own two predicates apart for the same
/// reason. Merging them would let a change made for one dimension move the
/// other silently.
fn is_numeral_atom(atom: &str) -> bool {
    !atom.is_empty()
        && atom != "."
        && atom.chars().all(|c| c.is_ascii_digit() || c == '.')
        && atom.chars().filter(|c| *c == '.').count() <= 1
}

/// True iff `term` is a FREE CONSTANT SYMBOL — the only term either difference
/// declaration lets a side of a difference be.
///
/// A `(declare-fun x () Int)` symbol renders as a bare atom and is exactly "a
/// free constant symbol"; a quantifier-BOUND name renders the same way and is
/// accepted here too. Accepting bound names is the permissive direction: both
/// difference logics are quantifier-free, so a transcript carrying a binder is
/// already outside every row that could fail this requirement, and refusing
/// them could only charge the requirement more often.
///
/// An APPLIED symbol, a `select`, an `ite`, a literal or any other compound
/// term is NOT one, so an atom built over one is not recognized and the
/// requirement is charged — the conservative direction, and the same line
/// `logic_lattice::difference_operand_sort` draws.
fn is_free_constant_symbol(term: &Sexp, declared: &Declared, bound: &[String]) -> bool {
    match term {
        Sexp::Atom(name) => {
            declared.functions.get(name.as_str()) == Some(&0)
                || bound.iter().any(|b| b == name.as_str())
        }
        Sexp::List(_) => false,
    }
}

/// True iff `atom` is an atom of SMT-LIB's difference grammar as the [S1]
/// declarations write it, PLUS the three permissive extensions named above.
///
/// `op` is `<`, `<=`, `>`, `>=`, `=` or `distinct` — the operator list both
/// declarations give.
///
/// * `(op x y)` — two free constant symbols;
/// * `(op (- x y) k)` and `(op k (- x y))` — a difference against a closed
///   numeric bound, in either order;
/// * `(op x k)` and `(op k x)` — the BARE BOUND. Neither declaration lists it,
///   so production widens here and this does not; see [`Req::WideArith`] for
///   why that asymmetry is the safe one.
///
/// The two sides' SORTS are deliberately not compared. Production requires them
/// equal; not requiring it recognizes more, charges less, and cannot fail a
/// transcript production headed correctly.
fn is_difference_shaped_atom(atom: &Sexp, declared: &Declared, bound: &[String]) -> bool {
    let Sexp::List(items) = atom else { return false };
    let [Sexp::Atom(op), lhs, rhs] = items.as_slice() else { return false };
    if !matches!(op.as_str(), "<" | "<=" | ">" | ">=" | "=" | "distinct") {
        return false;
    }
    let symbol = |term: &Sexp| is_free_constant_symbol(term, declared, bound);
    let difference = |term: &Sexp| match term {
        Sexp::List(parts) => match parts.as_slice() {
            [Sexp::Atom(head), left, right] if head == "-" => symbol(left) && symbol(right),
            _ => false,
        },
        Sexp::Atom(_) => false,
    };
    // `(op x y)`
    (symbol(lhs) && symbol(rhs))
        // `(op (- x y) k)` and its mirror
        || (difference(lhs) && is_closed_numeric_term(rhs))
        || (is_closed_numeric_term(lhs) && difference(rhs))
        // the BARE BOUND `(op x k)` and its mirror
        || (symbol(lhs) && is_closed_numeric_term(rhs))
        || (is_closed_numeric_term(lhs) && symbol(rhs))
}

/// True iff `term` — taken as ONE ATOM — mentions the integer or real theory at
/// all, which is what decides whether an unrecognized atom has any arithmetic
/// to widen.
///
/// Reads this file's OWN requirement walk rather than a second rule, so
/// "mentions arithmetic" cannot drift from "the requirements carry `Ints`,
/// `Reals` or `Numeric`". [`Req::Numeric`] counts because a bare numeral and
/// the sort-generic comparison operators are exactly how an arithmetic atom
/// presents in the emitted text.
fn atom_mentions_arithmetic(term: &Sexp, declared: &Declared, bound: &[String]) -> bool {
    let mut reqs: Vec<(Req, String)> = Vec::new();
    let mut scope = bound.to_vec();
    assertion_requirements(term, declared, &mut scope, &mut reqs);
    reqs.iter().any(|(req, _)| matches!(req, Req::Ints | Req::Reals | Req::Numeric))
}

/// Charge [`Req::WideArith`] for every ATOM of the asserted term that is
/// arithmetic and NOT difference-shaped.
///
/// Both difference logics are defined as "Boolean combinations of" their atoms,
/// so the Boolean connectives are TRANSPARENT and everything under them is
/// walked; a quantifier body is walked too (a binder already takes the query
/// out of every `QF_` row, so recursing there costs nothing and keeps this
/// function total). EVERYTHING ELSE IS AN ATOM.
///
/// `xor` is deliberately NOT transparent, matching
/// `logic_lattice::wide_arith_required`, which has no `Xor` arm either: an
/// `xor` over arithmetic is treated as one unrecognized atom by both, so the
/// two rules agree there rather than diverging for no reason.
fn linear_form_requirements(
    term: &Sexp,
    declared: &Declared,
    bound: &mut Vec<String>,
    out: &mut Vec<(Req, String)>,
) {
    if let Sexp::List(items) = term
        && let Some(head) = items.first().and_then(Sexp::atom)
    {
        match head {
            "not" | "and" | "or" | "=>" | "ite" => {
                for part in &items[1..] {
                    linear_form_requirements(part, declared, bound, out);
                }
                return;
            }
            "forall" | "exists" if items.len() >= 3 => {
                let depth = bound.len();
                for binding in items[1].items() {
                    if let Some(name) = binding.items().first().and_then(Sexp::atom) {
                        bound.push(name.to_string());
                    }
                }
                linear_form_requirements(&items[2], declared, bound, out);
                bound.truncate(depth);
                return;
            }
            _ => {}
        }
    }
    if is_difference_shaped_atom(term, declared, bound) {
        return;
    }
    if !atom_mentions_arithmetic(term, declared, bound) {
        return;
    }
    out.push((
        Req::WideArith,
        "the assertion carries an arithmetic atom that is not difference-shaped, so the \
         transcript needs the full LIA/LRA atom grammar"
            .to_string(),
    ));
}

// ─────────────────────────────────────────────────────────────────────────────
// 2. S-EXPRESSION PARSING
// ─────────────────────────────────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq, Eq)]
enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

impl Sexp {
    fn atom(&self) -> Option<&str> {
        match self {
            Sexp::Atom(a) => Some(a),
            Sexp::List(_) => None,
        }
    }
    fn items(&self) -> &[Sexp] {
        match self {
            Sexp::List(items) => items,
            Sexp::Atom(_) => &[],
        }
    }
}

/// Parse every top-level s-expression in `text`. Handles `|quoted symbols|`,
/// which `escape_smtlib_symbol` emits for names that are not simple symbols.
fn parse_all(text: &str) -> Vec<Sexp> {
    let chars: Vec<char> = text.chars().collect();
    let mut i = 0usize;
    let mut stack: Vec<Vec<Sexp>> = Vec::new();
    let mut out: Vec<Sexp> = Vec::new();

    while i < chars.len() {
        let c = chars[i];
        if c.is_whitespace() {
            i += 1;
        } else if c == '(' {
            stack.push(Vec::new());
            i += 1;
        } else if c == ')' {
            let done = stack.pop().expect("unbalanced ')' in transcript");
            let node = Sexp::List(done);
            match stack.last_mut() {
                Some(parent) => parent.push(node),
                None => out.push(node),
            }
            i += 1;
        } else if c == '|' {
            let start = i;
            i += 1;
            while i < chars.len() && chars[i] != '|' {
                i += 1;
            }
            assert!(i < chars.len(), "unterminated |quoted symbol| in transcript");
            i += 1;
            let atom: String = chars[start..i].iter().collect();
            push_atom(&mut stack, &mut out, atom);
        } else {
            let start = i;
            while i < chars.len()
                && !chars[i].is_whitespace()
                && chars[i] != '('
                && chars[i] != ')'
                && chars[i] != '|'
            {
                i += 1;
            }
            let atom: String = chars[start..i].iter().collect();
            push_atom(&mut stack, &mut out, atom);
        }
    }
    assert!(stack.is_empty(), "unbalanced '(' in transcript");
    out
}

fn push_atom(stack: &mut [Vec<Sexp>], out: &mut Vec<Sexp>, atom: String) {
    match stack.last_mut() {
        Some(parent) => parent.push(Sexp::Atom(atom)),
        None => out.push(Sexp::Atom(atom)),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// 3. WHAT A TRANSCRIPT REQUIRES OF ITS OWN LOGIC
// ─────────────────────────────────────────────────────────────────────────────

/// Everything a transcript declares, so the assertion walk can tell a declared
/// symbol from an operator it has never heard of.
#[derive(Debug, Default)]
struct Declared {
    /// symbol -> arity, from `(declare-fun name (args…) result)`.
    functions: BTreeMap<String, usize>,
    /// sort identifiers introduced by `declare-sort` / `declare-datatype`.
    sorts: BTreeSet<String>,
    /// the subset introduced by `declare-sort` alone — a datatype back-edge
    /// whose constructors/selectors are therefore NOT declared anywhere.
    uninterpreted_sorts: BTreeSet<String>,
    /// constructor names from `declare-datatype`.
    constructors: BTreeSet<String>,
    /// selector/field names from `declare-datatype`.
    fields: BTreeSet<String>,
}

/// The theory requirements of one SORT as written in a declaration.
fn sort_requirements(sort: &Sexp, why: &str, out: &mut Vec<(Req, String)>) {
    match sort {
        Sexp::Atom(name) => match name.as_str() {
            "Bool" => {}
            "Int" => out.push((Req::Ints, format!("{why}: the Int sort"))),
            "Real" => out.push((Req::Reals, format!("{why}: the Real sort"))),
            "RoundingMode" => out.push((Req::Floats, format!("{why}: the RoundingMode sort"))),
            // Any other bare sort identifier is a datatype (or the
            // `declare-sort` stand-in for a datatype back-edge): SMT-LIB has no
            // other user-introduced nullary sort in these transcripts.
            _ => out.push((Req::Datatypes, format!("{why}: the datatype sort `{name}`"))),
        },
        Sexp::List(items) => {
            let head = items.first().and_then(Sexp::atom).unwrap_or("");
            match head {
                "_" => match items.get(1).and_then(Sexp::atom).unwrap_or("") {
                    "BitVec" => out.push((Req::BitVectors, format!("{why}: a BitVec sort"))),
                    "FloatingPoint" => {
                        out.push((Req::Floats, format!("{why}: a FloatingPoint sort")));
                    }
                    other => panic!("{why}: unclassified indexed sort `(_ {other} …)`"),
                },
                "Array" => {
                    out.push((Req::Arrays, format!("{why}: an Array sort")));
                    // THE SHAPE, as the [S1] declarations restrict it: only
                    // `(Array Int Int)` and a positive-width
                    // `(Array (_ BitVec i) (_ BitVec j))` are admitted by the
                    // `*ALIA`/`*ABV*` names; everything else needs a row
                    // carrying `WIDE_ARRAY`. See [`Req::WideArray`].
                    let is_int = |sort: &Sexp| sort.atom() == Some("Int");
                    let is_positive_bitvec = |sort: &Sexp| match sort.items() {
                        [u, b, n] if u.atom() == Some("_") && b.atom() == Some("BitVec") => {
                            n.atom().is_some_and(|w| {
                                !w.is_empty()
                                    && w.chars().all(|c| c.is_ascii_digit())
                                    && w.chars().any(|c| c != '0')
                            })
                        }
                        _ => false,
                    };
                    let declared_shape = (is_int(&items[1]) && is_int(&items[2]))
                        || (is_positive_bitvec(&items[1]) && is_positive_bitvec(&items[2]));
                    if !declared_shape {
                        out.push((
                            Req::WideArray,
                            format!(
                                "{why}: an Array sort that is neither `(Array Int Int)` nor a \
                                 positive-width `(Array (_ BitVec i) (_ BitVec j))`"
                            ),
                        ));
                    }
                    sort_requirements(&items[1], why, out);
                    sort_requirements(&items[2], why, out);
                }
                other => panic!("{why}: unclassified sort form `({other} …)`"),
            }
        }
    }
}

/// The theory requirements of one indexed identifier `(_ name idx…)`, whether
/// it stands alone as a term or heads an application.
fn indexed_requirements(items: &[Sexp], out: &mut Vec<(Req, String)>) {
    let name = items.get(1).and_then(Sexp::atom).unwrap_or("");
    let what = format!("the assertion applies `(_ {name} …)`");
    match name {
        // `(_ bvN W)` — a bitvector literal.
        n if n.starts_with("bv") && n[2..].chars().all(|c| c.is_ascii_digit()) => {
            out.push((Req::BitVectors, what));
        }
        "extract" | "zero_extend" | "sign_extend" | "repeat" | "rotate_left" | "rotate_right" => {
            out.push((Req::BitVectors, what));
        }
        // Int -> BV: both theories.
        "int2bv" => {
            out.push((Req::BitVectors, what.clone()));
            out.push((Req::Ints, what));
        }
        // FP literals and the FP conversion families.
        "NaN" | "+oo" | "-oo" | "+zero" | "-zero" => out.push((Req::Floats, what)),
        "to_fp" | "to_fp_unsigned" => out.push((Req::Floats, what)),
        // FP -> BV: both theories.
        "fp.to_sbv" | "fp.to_ubv" => {
            out.push((Req::Floats, what.clone()));
            out.push((Req::BitVectors, what));
        }
        // `((_ is Ctor) t)` — the datatype tester.
        "is" => out.push((Req::Datatypes, what)),
        other => panic!(
            "unclassified indexed identifier `(_ {other} …)` in the assertion: add it to \
             `indexed_requirements` with the theory it needs, or this check silently stops \
             covering it"
        ),
    }
}

/// Every bitvector operator name the canonical lowering can emit.
const BV_OPS: &[&str] = &[
    "bvadd", "bvsub", "bvmul", "bvudiv", "bvsdiv", "bvurem", "bvsrem", "bvsmod", "bvand", "bvor",
    "bvxor", "bvnot", "bvneg", "bvshl", "bvlshr", "bvashr", "bvult", "bvule", "bvugt", "bvuge",
    "bvslt", "bvsle", "bvsgt", "bvsge", "concat",
];

/// Sort-generic connectives and conditionals: no theory of their own.
const THEORY_FREE: &[&str] =
    &["true", "false", "not", "and", "or", "=>", "=", "distinct", "ite", "xor"];

/// The five SMT-LIB rounding-mode constants.
const ROUNDING_MODES: &[&str] = &["RNE", "RNA", "RTP", "RTN", "RTZ", "roundNearestTiesToEven"];

/// The theory requirements of one ATOM in the assertion.
fn atom_requirements(
    atom: &str,
    declared: &Declared,
    bound: &[String],
    out: &mut Vec<(Req, String)>,
) {
    let what = format!("the assertion mentions `{atom}`");
    if THEORY_FREE.contains(&atom) {
        return;
    }
    if !atom.is_empty() && atom.chars().all(|c| c.is_ascii_digit()) {
        // A bare numeral: an Int term in an integer logic, a Real term in a
        // reals logic. Either admits it.
        out.push((Req::Numeric, what));
        return;
    }
    if ROUNDING_MODES.contains(&atom) {
        out.push((Req::Floats, what));
        return;
    }
    if bound.iter().any(|b| b == atom) {
        // A quantifier-BOUND variable: its sort came from the binder, which
        // `assertion_requirements` already required.
        return;
    }
    if declared.functions.contains_key(atom) {
        // A declared symbol used as a term. Its SORT was already required by
        // its own `declare-fun` line; a 0-ary use adds nothing, and a use with
        // arguments is handled at the application head.
        return;
    }
    if declared.constructors.contains(atom) || declared.fields.contains(atom) {
        out.push((Req::Datatypes, what));
        return;
    }
    if declared.sorts.contains(atom) {
        out.push((Req::Datatypes, what));
        return;
    }
    if !declared.uninterpreted_sorts.is_empty() {
        // The BY-NAME datatype spelling. Its sort is declared uninterpreted
        // (`(declare-sort Expr 0)`) and its constructor/selector/tester symbols
        // therefore have no `declare-datatype` to come from — the flat
        // `Ty::Adt` encoding models them elsewhere. That is a KNOWN property of
        // that spelling and not what this file is about; record the datatype
        // requirement and move on rather than pretend the symbol is unknown.
        out.push((Req::Datatypes, format!("{what} (a member of an uninterpreted datatype sort)")));
        return;
    }
    panic!(
        "unclassified atom `{atom}` in the assertion: it is neither a declared symbol, a bound \
         variable, nor a known literal/operator. Either the transcript applies an UNDECLARED \
         symbol (a malformed query) or this checker needs teaching about it — both are failures."
    );
}

/// The theory requirements of the asserted term, walked structurally.
///
/// `bound` is the quantifier scope in force at this node: a bound variable is
/// not declared anywhere in the transcript, so without it every binder use
/// would read as an undeclared symbol.
fn assertion_requirements(
    term: &Sexp,
    declared: &Declared,
    bound: &mut Vec<String>,
    out: &mut Vec<(Req, String)>,
) {
    match term {
        Sexp::Atom(a) => atom_requirements(a, declared, bound, out),
        Sexp::List(items) => {
            if items.is_empty() {
                return;
            }
            // `(_ …)` standing alone as a term (a bitvector or FP literal).
            if items[0].atom() == Some("_") {
                indexed_requirements(items, out);
                return;
            }
            // `((_ op idx…) args…)` — an indexed operator applied.
            if let Sexp::List(head) = &items[0] {
                assert_eq!(
                    head.first().and_then(Sexp::atom),
                    Some("_"),
                    "an application head that is a list must be an indexed identifier: {items:?}"
                );
                indexed_requirements(head, out);
                for arg in &items[1..] {
                    assertion_requirements(arg, declared, bound, out);
                }
                return;
            }
            let head = items[0].atom().expect("checked above");
            match head {
                // Quantifiers: the flag AND the binder sorts, which appear only
                // in the binding list.
                "forall" | "exists" => {
                    out.push((Req::Quantifiers, format!("the assertion binds with `{head}`")));
                    let depth = bound.len();
                    for binding in items[1].items() {
                        let pair = binding.items();
                        assert_eq!(pair.len(), 2, "a binder must be `(name sort)`: {binding:?}");
                        sort_requirements(&pair[1], "a quantifier binder", out);
                        bound.push(pair[0].atom().expect("binder name").to_string());
                    }
                    assertion_requirements(&items[2], declared, bound, out);
                    bound.truncate(depth);
                }
                // `(as Ctor Sort)` — a qualified nullary datatype constructor.
                "as" => {
                    out.push((Req::Datatypes, "the assertion uses `(as …)`".to_string()));
                    sort_requirements(&items[2], "an `(as …)` sort ascription", out);
                }
                _ => {
                    // The head as an operator or a declared function symbol.
                    if declared.functions.contains_key(head) {
                        // An APPLICATION of a declared symbol with arguments is
                        // an uninterpreted function use.
                        if items.len() > 1 {
                            out.push((
                                Req::Uf,
                                format!("the assertion applies the declared symbol `{head}`"),
                            ));
                        }
                    } else {
                        operator_requirements(head, declared, out);
                        // LINEARITY is the one requirement the head alone does
                        // not settle: `(* 3 x)` is linear and `(* x y)` is not.
                        linearity_requirement(head, &items[1..], declared, bound, out);
                    }
                    for arg in &items[1..] {
                        assertion_requirements(arg, declared, bound, out);
                    }
                }
            }
        }
    }
}

/// The theory requirements of one application HEAD that is not a declared
/// symbol.
fn operator_requirements(head: &str, declared: &Declared, out: &mut Vec<(Req, String)>) {
    let what = format!("the assertion applies `{head}`");
    if THEORY_FREE.contains(&head) {
        return;
    }
    if BV_OPS.contains(&head) {
        out.push((Req::BitVectors, what));
        return;
    }
    // `bv2nat` produces an Int from a BV: both theories.
    if head == "bv2nat" || head == "bv2int" {
        out.push((Req::BitVectors, what.clone()));
        out.push((Req::Ints, what));
        return;
    }
    if head == "fp" || head.starts_with("fp.") {
        out.push((Req::Floats, what));
        return;
    }
    match head {
        // Sort-generic arithmetic and ordering: Int or Real.
        "+" | "-" | "*" | "<" | "<=" | ">" | ">=" => out.push((Req::Numeric, what)),
        // Integer-only Euclidean division.
        "div" | "mod" | "abs" => out.push((Req::Ints, what)),
        // Rational division.
        "/" => out.push((Req::Reals, what)),
        "select" | "store" => out.push((Req::Arrays, what)),
        _ => {
            // A datatype constructor or selector applied to arguments.
            if declared.constructors.contains(head) || declared.fields.contains(head) {
                out.push((Req::Datatypes, what));
                return;
            }
            // A selector/tester of a BY-NAME datatype: the sort is declared
            // uninterpreted, so its members have no `declare-datatype` to come
            // from. See `atom_requirements` for why that is recorded, not
            // refused, here.
            if !declared.uninterpreted_sorts.is_empty() {
                out.push((
                    Req::Datatypes,
                    format!("{what} (a member of an uninterpreted datatype sort)"),
                ));
                return;
            }
            panic!(
                "unclassified operator `{head}` at an application head: either the transcript \
                 applies an UNDECLARED symbol (a malformed query) or `operator_requirements` \
                 needs teaching about it — both are failures."
            );
        }
    }
}

/// THE PROPERTY. Build the canonical transcript for `formula`, parse it, and
/// assert that the `(set-logic L)` line admits everything the rest of the
/// transcript declares and applies.
fn assert_transcript_self_consistent(formula: &Formula, label: &str) {
    let text = problem_smt2(formula);
    let unmet = unmet_transcript_requirements(&text, label);
    assert!(
        unmet.is_empty(),
        "[{label}] MALFORMED TRANSCRIPT: the logic line does not admit {unmet:?}.\n{text}"
    );
}

/// The requirements of `text` that its own `(set-logic L)` line does NOT admit
/// — empty for a self-consistent transcript.
///
/// SPLIT OUT OF [`assert_transcript_self_consistent`] SO THE CHECKER CAN BE
/// SHOWN TO FAIL. A checker that cannot fail on a planted defect is not a
/// checker, and the only way to plant one is to hand it TEXT rather than a
/// `Formula`: everything `problem_smt2` emits is (by construction, and by every
/// test in this file) already self-consistent, so a defect has to be written
/// into the transcript directly. `an_over_narrow_difference_logic_header_is_
/// rejected` takes a real emitted transcript, narrows its header by one
/// dimension, and asserts this function reports it.
///
/// STRUCTURAL problems are still panics, not entries: a transcript that does
/// not parse, has no `(check-sat)`, or applies a symbol this file cannot
/// classify is a failure of a different kind and must not be reportable as an
/// ordinary unmet requirement.
fn unmet_transcript_requirements(text: &str, label: &str) -> Vec<(Req, String)> {
    let forms = parse_all(text);
    assert!(forms.len() >= 3, "[{label}] transcript too short:\n{text}");

    // (set-logic L)
    let head = forms[0].items();
    assert_eq!(
        head.first().and_then(Sexp::atom),
        Some("set-logic"),
        "[{label}] a transcript must open with (set-logic …):\n{text}"
    );
    let logic = head[1].atom().expect("logic name is an atom").to_string();
    let admits = admissibility(&logic);

    // The declarations, and what they require.
    let mut declared = Declared::default();
    let mut reqs: Vec<(Req, String)> = Vec::new();
    let mut assertion: Option<&Sexp> = None;
    let mut saw_check_sat = false;

    for form in &forms[1..] {
        let items = form.items();
        match items.first().and_then(Sexp::atom).unwrap_or("") {
            "declare-sort" => {
                let name = items[1].atom().expect("declare-sort name").to_string();
                assert_eq!(
                    items[2].atom(),
                    Some("0"),
                    "[{label}] only nullary sorts are declared here: {form:?}"
                );
                reqs.push((
                    Req::Datatypes,
                    format!("`(declare-sort {name} 0)` stands in for a datatype back-edge"),
                ));
                declared.sorts.insert(name.clone());
                declared.uninterpreted_sorts.insert(name);
            }
            "declare-datatype" => {
                let name = items[1].atom().expect("declare-datatype name").to_string();
                reqs.push((Req::Datatypes, format!("`(declare-datatype {name} …)`")));
                declared.sorts.insert(name);
                for ctor in items[2].items() {
                    let parts = ctor.items();
                    let ctor_name =
                        parts.first().and_then(Sexp::atom).expect("constructor name").to_string();
                    declared.constructors.insert(ctor_name);
                    for field in &parts[1..] {
                        let fp = field.items();
                        assert_eq!(fp.len(), 2, "[{label}] a field must be `(name sort)`");
                        declared.fields.insert(fp[0].atom().expect("field name").to_string());
                        sort_requirements(&fp[1], "a datatype field sort", &mut reqs);
                    }
                }
            }
            "declare-fun" => {
                let name = items[1].atom().expect("declare-fun name").to_string();
                let args = items[2].items();
                if !args.is_empty() {
                    reqs.push((
                        Req::Uf,
                        format!("`(declare-fun {name} …)` has arity {}", args.len()),
                    ));
                }
                for arg in args {
                    sort_requirements(arg, &format!("an argument sort of `{name}`"), &mut reqs);
                }
                sort_requirements(&items[3], &format!("the result sort of `{name}`"), &mut reqs);
                declared.functions.insert(name, args.len());
            }
            "assert" => assertion = Some(&items[1]),
            "check-sat" => saw_check_sat = true,
            other => panic!("[{label}] unexpected transcript command `{other}`:\n{text}"),
        }
    }

    assert!(saw_check_sat, "[{label}] transcript has no (check-sat):\n{text}");
    let assertion = assertion.unwrap_or_else(|| panic!("[{label}] transcript has no (assert …)"));
    assertion_requirements(assertion, &declared, &mut Vec::new(), &mut reqs);
    // THE LINEAR-FORM REQUIREMENT, charged from whole ATOMS rather than from
    // any one node — the dimension no per-node walk above can decide. It runs
    // AFTER `assertion_requirements`, so `atom_mentions_arithmetic` can reuse
    // that walk on each atom without meeting an unclassified symbol first.
    linear_form_requirements(assertion, &declared, &mut Vec::new(), &mut reqs);

    reqs.into_iter()
        .filter(|(req, _)| !allows(admits, *req))
        .map(|(req, why)| (req, format!("`(set-logic {logic})` does not admit {req:?}, but {why}")))
        .collect()
}

// ─────────────────────────────────────────────────────────────────────────────
// 4. THE GENERATOR
// ─────────────────────────────────────────────────────────────────────────────

/// xorshift64* — deterministic, dependency-free, and seeded per case so a
/// failure names the exact case that produced it.
struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1)
    }
    fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next_u64() % n as u64) as usize
    }
}

/// A short, stable tag for a sort — the key that keeps one uninterpreted
/// symbol name bound to ONE signature, which is what
/// `uninterpreted_signature_conflict` requires of an acceptable formula.
fn sort_tag(sort: &Sort) -> String {
    match sort {
        Sort::Bool => "b".into(),
        Sort::Int => "i".into(),
        Sort::Real => "r".into(),
        Sort::BitVec(w) => format!("bv{w}"),
        Sort::Float { eb, sb } => format!("f{eb}x{sb}"),
        Sort::RoundingMode => "rm".into(),
        Sort::Array(i, e) => format!("a{}z{}", sort_tag(i), sort_tag(e)),
        Sort::Datatype { name, .. } => format!("d{name}"),
        _ => "u".into(),
    }
}

/// The name an uninterpreted symbol of this signature always gets.
fn uf_name(args: &[Sort], result: &Sort) -> String {
    let mut name = String::from("uf");
    for a in args {
        name.push('_');
        name.push_str(&sort_tag(a));
    }
    name.push_str("__");
    name.push_str(&sort_tag(result));
    name
}

/// The recursive datatype, FULL spelling: `Expr = Const(c: bv32) | App(f: Expr,
/// x: Expr) | Unit`. Its self-references are BY-NAME back-edges, the second
/// spelling.
fn expr_full() -> Sort {
    let back = expr_by_name();
    Sort::Datatype {
        name: "Expr".into(),
        constructors: vec![
            ("Const".into(), vec![("ec".into(), Sort::BitVec(32))]),
            ("App".into(), vec![("ef".into(), back.clone()), ("ex".into(), back)]),
            ("Unit".into(), Vec::new()),
        ],
    }
}

/// The recursive datatype, BY-NAME spelling.
fn expr_by_name() -> Sort {
    Sort::Datatype { name: "Expr".into(), constructors: Vec::new() }
}

/// A non-recursive datatype with scalar fields in three theories, so a
/// datatype declaration itself carries Int/BV/Real sorts.
fn box_full() -> Sort {
    Sort::Datatype {
        name: "Boxed".into(),
        constructors: vec![(
            "MkBoxed".into(),
            vec![
                ("bi".into(), Sort::Int),
                ("br".into(), Sort::Real),
                ("bb".into(), Sort::BitVec(8)),
            ],
        )],
    }
}

fn rm() -> Box<Formula> {
    Box::new(Formula::FpRoundingMode(RoundingMode::RNE))
}

fn var(name: &str, sort: Sort) -> Formula {
    Formula::Var(name.into(), sort)
}

/// A well-sorted term of `sort`.
fn term(rng: &mut Rng, sort: &Sort, depth: u32) -> Formula {
    match sort {
        Sort::Bool => bool_term(rng, depth),
        Sort::Int => int_term(rng, depth),
        Sort::Real => real_term(rng, depth),
        Sort::BitVec(w) => bv_term(rng, *w, depth),
        Sort::Float { eb, sb } => fp_term(rng, *eb, *sb, depth),
        Sort::Array(..) => array_term(rng, sort, depth),
        Sort::Datatype { .. } => dt_term(rng, sort, depth),
        other => var("rmv", other.clone()),
    }
}

fn leaf_or(rng: &mut Rng, depth: u32, choices: usize) -> usize {
    if depth == 0 { 0 } else { rng.below(choices) }
}

fn int_term(rng: &mut Rng, depth: u32) -> Formula {
    match leaf_or(rng, depth, 9) {
        0 => Formula::Int(i128::from(rng.below(64) as i64) - 16),
        1 => var(&format!("ivar{}", rng.below(3)), Sort::Int),
        2 => Formula::UInt(rng.below(100) as u128),
        3 => Formula::Add(Box::new(int_term(rng, depth - 1)), Box::new(int_term(rng, depth - 1))),
        4 => Formula::Mul(Box::new(int_term(rng, depth - 1)), Box::new(int_term(rng, depth - 1))),
        5 => Formula::Div(Box::new(int_term(rng, depth - 1)), Box::new(int_term(rng, depth - 1))),
        6 => Formula::BvToInt(Box::new(bv_term(rng, 8, depth - 1)), 8, rng.below(2) == 0),
        7 => Formula::FnApp {
            func: uf_name(&[Sort::Bool], &Sort::Int),
            args: vec![bool_term(rng, depth - 1)],
            sort: Sort::Int,
        },
        _ => Formula::Sel {
            datatype: "Boxed".into(),
            field: "bi".into(),
            field_sort: Sort::Int,
            arg: Box::new(dt_term(rng, &box_full(), depth - 1)),
        },
    }
}

fn real_term(rng: &mut Rng, depth: u32) -> Formula {
    match leaf_or(rng, depth, 6) {
        0 => Formula::rat_from_int(i128::from(rng.below(32) as i64) - 8),
        1 => var(&format!("rvar{}", rng.below(2)), Sort::Real),
        2 => Formula::rat("3", "4").expect("canonical rational"),
        3 => Formula::Add(Box::new(real_term(rng, depth - 1)), Box::new(real_term(rng, depth - 1))),
        4 => Formula::Neg(Box::new(real_term(rng, depth - 1))),
        _ => Formula::FnApp {
            func: uf_name(&[Sort::Bool], &Sort::Real),
            args: vec![bool_term(rng, depth - 1)],
            sort: Sort::Real,
        },
    }
}

fn bv_term(rng: &mut Rng, width: u32, depth: u32) -> Formula {
    let binops: &[fn(Box<Formula>, Box<Formula>, u32) -> Formula] = &[
        Formula::BvAdd,
        Formula::BvSub,
        Formula::BvMul,
        Formula::BvAnd,
        Formula::BvOr,
        Formula::BvXor,
        Formula::BvUDiv,
        Formula::BvSRem,
        Formula::BvShl,
        Formula::BvAShr,
    ];
    match leaf_or(rng, depth, 10) {
        0 => Formula::BitVec { value: rng.below(200) as i128, width },
        1 => var(&format!("bv{width}v{}", rng.below(3)), Sort::BitVec(width)),
        2 => {
            let op = binops[rng.below(binops.len())];
            op(
                Box::new(bv_term(rng, width, depth - 1)),
                Box::new(bv_term(rng, width, depth - 1)),
                width,
            )
        }
        3 => Formula::BvNot(Box::new(bv_term(rng, width, depth - 1)), width),
        4 => Formula::IntToBv(Box::new(int_term(rng, depth - 1)), width),
        5 if width == 32 || width == 64 => {
            let (eb, sb) = if width == 32 { (8, 24) } else { (11, 53) };
            Formula::FpToIeeeBv(Box::new(fp_term(rng, eb, sb, depth - 1)))
        }
        6 => {
            // The TOTAL saturating FP -> BV conversions, inside the width
            // domain where the native and text lanes agree.
            let (eb, sb) = if rng.below(2) == 0 { (8, 24) } else { (11, 53) };
            let value = Box::new(fp_term(rng, eb, sb, depth - 1));
            if rng.below(2) == 0 {
                Formula::FpToSbv { rm: rm(), value, width, eb, sb }
            } else {
                Formula::FpToUbv { rm: rm(), value, width, eb, sb }
            }
        }
        7 if width >= 2 => {
            let lo = width / 2;
            Formula::BvConcat(
                Box::new(bv_term(rng, width - lo, depth - 1)),
                Box::new(bv_term(rng, lo, depth - 1)),
            )
        }
        8 => Formula::FnApp {
            func: uf_name(&[Sort::Bool], &Sort::BitVec(width)),
            args: vec![bool_term(rng, depth - 1)],
            sort: Sort::BitVec(width),
        },
        _ => Formula::Ite(
            Box::new(bool_term(rng, depth - 1)),
            Box::new(bv_term(rng, width, depth - 1)),
            Box::new(bv_term(rng, width, depth - 1)),
        ),
    }
}

fn fp_term(rng: &mut Rng, eb: u32, sb: u32, depth: u32) -> Formula {
    match leaf_or(rng, depth, 10) {
        0 => Formula::FpNaN { eb, sb },
        1 => var(&format!("fp{eb}_{sb}v{}", rng.below(2)), Sort::Float { eb, sb }),
        2 => Formula::FpInf { neg: rng.below(2) == 0, eb, sb },
        3 => Formula::FpZero { neg: rng.below(2) == 0, eb, sb },
        4 => Formula::FpAdd(
            rm(),
            Box::new(fp_term(rng, eb, sb, depth - 1)),
            Box::new(fp_term(rng, eb, sb, depth - 1)),
        ),
        5 => Formula::FpMul(
            rm(),
            Box::new(fp_term(rng, eb, sb, depth - 1)),
            Box::new(fp_term(rng, eb, sb, depth - 1)),
        ),
        6 => Formula::FpAbs(Box::new(fp_term(rng, eb, sb, depth - 1))),
        7 => Formula::FpFromBits { bits: Box::new(bv_term(rng, eb + sb, depth - 1)), eb, sb },
        8 => {
            let value = Box::new(bv_term(rng, 16, depth - 1));
            if rng.below(2) == 0 {
                Formula::FpFromSbv { rm: rm(), value, eb, sb }
            } else {
                Formula::FpFromUbv { rm: rm(), value, eb, sb }
            }
        }
        _ => {
            // FP -> FP format conversion from the OTHER format.
            let (seb, ssb) = if eb == 8 { (11, 53) } else { (8, 24) };
            Formula::FpConvert {
                rm: rm(),
                value: Box::new(fp_term(rng, seb, ssb, depth - 1)),
                eb,
                sb,
            }
        }
    }
}

fn array_term(rng: &mut Rng, sort: &Sort, depth: u32) -> Formula {
    let Sort::Array(index, element) = sort else { unreachable!() };
    match leaf_or(rng, depth, 3) {
        0 => var(&format!("arr{}v{}", sort_tag(sort), rng.below(2)), sort.clone()),
        1 => Formula::Store(
            Box::new(array_term(rng, sort, depth - 1)),
            Box::new(term(rng, index, depth - 1)),
            Box::new(term(rng, element, depth - 1)),
        ),
        _ => Formula::FnApp {
            func: uf_name(&[Sort::Bool], sort),
            args: vec![bool_term(rng, depth - 1)],
            sort: sort.clone(),
        },
    }
}

fn dt_term(rng: &mut Rng, sort: &Sort, depth: u32) -> Formula {
    let Sort::Datatype { name, constructors } = sort else { unreachable!() };
    // A BY-NAME reference has no constructors to apply: only a variable or an
    // uninterpreted application can carry it.
    if constructors.is_empty() || depth == 0 {
        return match rng.below(2) {
            0 => var(&format!("dt{name}v{}", rng.below(2)), sort.clone()),
            _ => Formula::FnApp {
                func: uf_name(&[Sort::Bool], sort),
                args: vec![bool_term(rng, 0)],
                sort: sort.clone(),
            },
        };
    }
    match rng.below(4) {
        0 => var(&format!("dt{name}v{}", rng.below(2)), sort.clone()),
        1 => Formula::FnApp {
            func: uf_name(&[Sort::Bool], sort),
            args: vec![bool_term(rng, depth - 1)],
            sort: sort.clone(),
        },
        _ => {
            let (ctor, fields) = &constructors[rng.below(constructors.len())];
            let args =
                fields.iter().map(|(_, fsort)| term(rng, fsort, depth - 1)).collect::<Vec<_>>();
            Formula::Ctor { ctor: ctor.clone(), args, sort: sort.clone() }
        }
    }
}

/// The sorts an equation, a binder or an uninterpreted result can range over.
fn sort_menu() -> Vec<Sort> {
    vec![
        Sort::Bool,
        Sort::Int,
        Sort::Real,
        Sort::BitVec(8),
        Sort::BitVec(32),
        Sort::BitVec(64),
        Sort::Float { eb: 8, sb: 24 },
        Sort::Float { eb: 11, sb: 53 },
        Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)),
        Sort::Array(Box::new(Sort::Int), Box::new(Sort::BitVec(8))),
        Sort::Array(Box::new(Sort::BitVec(8)), Box::new(Sort::Real)),
        // A purely bitvector array, so the fuzz can reach the `*ABV*` rows of
        // the admissibility table (an Int index would trip the BV-mixed-with-Int
        // lever and answer `ALL` instead).
        Sort::Array(Box::new(Sort::BitVec(8)), Box::new(Sort::BitVec(32))),
        expr_full(),
        expr_by_name(),
        box_full(),
    ]
}

fn bool_term(rng: &mut Rng, depth: u32) -> Formula {
    match leaf_or(rng, depth, 14) {
        0 => Formula::Bool(rng.below(2) == 0),
        1 => var(&format!("pvar{}", rng.below(2)), Sort::Bool),
        2 => Formula::Pred("dir_open".into(), vec![int_term(rng, 0)]),
        3 => Formula::Pred("priv_dropped".into(), Vec::new()),
        4 => {
            let menu = sort_menu();
            let s = &menu[rng.below(menu.len())];
            Formula::Eq(Box::new(term(rng, s, depth - 1)), Box::new(term(rng, s, depth - 1)))
        }
        5 => Formula::Not(Box::new(bool_term(rng, depth - 1))),
        6 => Formula::And(vec![bool_term(rng, depth - 1), bool_term(rng, depth - 1)]),
        7 => Formula::Implies(
            Box::new(bool_term(rng, depth - 1)),
            Box::new(bool_term(rng, depth - 1)),
        ),
        8 => {
            let int_side = rng.below(2) == 0;
            let (a, b) = if int_side {
                (int_term(rng, depth - 1), int_term(rng, depth - 1))
            } else {
                (real_term(rng, depth - 1), real_term(rng, depth - 1))
            };
            match rng.below(4) {
                0 => Formula::Lt(Box::new(a), Box::new(b)),
                1 => Formula::Le(Box::new(a), Box::new(b)),
                2 => Formula::Gt(Box::new(a), Box::new(b)),
                _ => Formula::Ge(Box::new(a), Box::new(b)),
            }
        }
        9 => {
            let w = [8u32, 32, 64][rng.below(3)];
            let a = Box::new(bv_term(rng, w, depth - 1));
            let b = Box::new(bv_term(rng, w, depth - 1));
            match rng.below(4) {
                0 => Formula::BvULt(a, b, w),
                1 => Formula::BvULe(a, b, w),
                2 => Formula::BvSLt(a, b, w),
                _ => Formula::BvSLe(a, b, w),
            }
        }
        10 => {
            let (eb, sb) = if rng.below(2) == 0 { (8, 24) } else { (11, 53) };
            let a = Box::new(fp_term(rng, eb, sb, depth - 1));
            match rng.below(6) {
                0 => Formula::FpIsNaN(a),
                1 => Formula::FpIsZero(a),
                2 => Formula::FpIsNegative(a),
                3 => Formula::FpLt(a, Box::new(fp_term(rng, eb, sb, depth - 1))),
                4 => Formula::FpGe(a, Box::new(fp_term(rng, eb, sb, depth - 1))),
                _ => Formula::FpEq(a, Box::new(fp_term(rng, eb, sb, depth - 1))),
            }
        }
        11 => Formula::IsCtor {
            datatype: "Expr".into(),
            ctor: "Const".into(),
            arg: Box::new(dt_term(rng, &expr_full(), depth - 1)),
        },
        12 => {
            // A quantifier — the binder sort is the position no
            // `children()`-based walk can see.
            let menu = sort_menu();
            let s = menu[rng.below(menu.len())].clone();
            let body = Box::new(if rng.below(2) == 0 {
                // The bound variable is USED …
                Formula::Eq(Box::new(var("qv", s.clone())), Box::new(term(rng, &s, depth - 1)))
            } else {
                // … and here it is NOT, which is the shape that made the binder
                // sort invisible to every classifier that walked children only.
                bool_term(rng, depth - 1)
            });
            let bindings = vec![("qv".into(), s)];
            if rng.below(2) == 0 {
                Formula::Forall(bindings, body)
            } else {
                Formula::Exists(bindings, body)
            }
        }
        _ => {
            // An array read, which reaches the element theory through the
            // array sort alone.
            let menu = sort_menu();
            let arrs: Vec<&Sort> = menu.iter().filter(|s| matches!(s, Sort::Array(..))).collect();
            let s = arrs[rng.below(arrs.len())].clone();
            let Sort::Array(index, element) = &s else { unreachable!() };
            let read = Formula::Select(
                Box::new(array_term(rng, &s, depth - 1)),
                Box::new(term(rng, index, depth - 1)),
            );
            Formula::Eq(Box::new(read), Box::new(term(rng, element, depth - 1)))
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// 5. THE TESTS
// ─────────────────────────────────────────────────────────────────────────────

/// THE FUZZ. 512 well-sorted formulas spanning every contract variant the
/// generator above reaches — every literal family, the whole Bv and Fp
/// families including all five FP conversions, arrays, quantifiers (bound
/// variable used AND unused), uninterpreted predicates and function
/// applications at every sort in the menu, and BOTH datatype spellings (the
/// full `(declare-datatype …)` definition and the by-name back-edge that
/// becomes `(declare-sort … 0)`).
///
/// For each: the exported transcript must be SELF-CONSISTENT — its own
/// `(set-logic L)` line must admit every sort its own declarations write and
/// every symbol and operator its own assertion applies.
#[test]
fn exported_transcripts_are_self_consistent_across_a_broad_formula_fuzz() {
    let mut logics: BTreeMap<String, usize> = BTreeMap::new();
    let mut checked = 0usize;
    for seed in 0..512u64 {
        let mut rng = Rng::new(seed + 1);
        let formula = bool_term(&mut rng, 4);
        // The property is stated for formulas the lane ACCEPTS, and a
        // well-sorted Bool top level is the precondition every gate is read
        // under.
        assert_eq!(
            check_formula_sort(&formula),
            Ok(Sort::Bool),
            "seed {seed}: the generator must only produce well-sorted Bool formulas: {formula:?}"
        );
        assert!(
            trust_types::ay_bridge::is_lowerable_formula(&formula),
            "seed {seed}: the generator must only produce formulas the bridge can lower"
        );
        let logic = crate::smt2_export::detect_logic(&formula).to_string();
        *logics.entry(logic).or_default() += 1;
        assert_transcript_self_consistent(&formula, &format!("seed {seed}"));
        checked += 1;
    }
    assert!(checked >= 400, "the fuzz must cover at least 400 formulas, covered {checked}");
    // The fuzz is worthless if it only ever produces one logic; require real
    // spread across the table.
    assert!(logics.len() >= 8, "the fuzz must exercise several logic lines, saw only {logics:?}");
}

/// MEASURED SHAPE 1. `Eq(FnApp{"g", [], BitVec(8)}, FnApp{"g", [], BitVec(8)})`
/// — well sorted at `Bool` — exported as `(set-logic QF_LIA)` beside
/// `(declare-fun g () (_ BitVec 8))`: the logic line did not admit the
/// bitvector sort its own declaration wrote, because `analyze_formula`
/// classified only the `Var`/`SymVar` sort positions and `FnApp` was not one
/// of them.
#[test]
fn fn_app_at_bitvec_result_sort_selects_a_bitvector_logic() {
    let g = || Formula::FnApp { func: "g".into(), args: Vec::new(), sort: Sort::BitVec(8) };
    let formula = Formula::Eq(Box::new(g()), Box::new(g()));
    assert_eq!(check_formula_sort(&formula), Ok(Sort::Bool));

    let text = problem_smt2(&formula);
    assert!(
        text.contains("(declare-fun g () (_ BitVec 8))"),
        "the transcript must declare g at its BitVec result sort:\n{text}"
    );
    assert!(
        !text.starts_with("(set-logic QF_LIA)"),
        "an integer logic cannot head a transcript that declares a bitvector:\n{text}"
    );
    // `g` is 0-ARY: a `(declare-fun g () …)` is an ordinary free constant,
    // which every SMT-LIB logic admits, so this makes no UF requirement — the
    // same rule `Req::Uf` is charged by. What the logic line must admit is the
    // BitVec SORT the declaration writes, and `QF_BV` is the least name that
    // does.
    assert_eq!(crate::smt2_export::detect_logic(&formula), "QF_BV");
    assert_transcript_self_consistent(&formula, "FnApp at BitVec(8)");
}

/// MEASURED SHAPE 2. The same defect at `Float { eb: 8, sb: 24 }`: the
/// transcript declared `(declare-fun g () (_ FloatingPoint 8 24))` under
/// `(set-logic QF_LIA)`. `g` is 0-ary — a free constant every logic admits —
/// so the only requirement is the FloatingPoint SORT, and `QF_FP` is the least
/// name that admits it. (An FP-sorted symbol of arity >= 1 WOULD need UF
/// alongside FP, which no standard name spells, and takes `ALL`; the
/// `FnApp argument sort` case below is that shape.)
#[test]
fn fn_app_at_float_result_sort_selects_a_floating_point_logic() {
    let g = || Formula::FnApp {
        func: "g".into(),
        args: Vec::new(),
        sort: Sort::Float { eb: 8, sb: 24 },
    };
    let formula = Formula::Eq(Box::new(g()), Box::new(g()));
    assert_eq!(check_formula_sort(&formula), Ok(Sort::Bool));

    let text = problem_smt2(&formula);
    assert!(
        text.contains("(declare-fun g () (_ FloatingPoint 8 24))"),
        "the transcript must declare g at its Float result sort:\n{text}"
    );
    assert_eq!(crate::smt2_export::detect_logic(&formula), "QF_FP");
    assert_transcript_self_consistent(&formula, "FnApp at Float(8,24)");
}

/// The same hole at the other two positions a previous round left out:
/// `Ctor`'s result sort is already a datatype (so it was covered by the
/// datatype lever), but `Sel`'s FIELD sort is an ordinary scalar and was not.
#[test]
fn sel_field_sort_and_pred_argument_sorts_reach_the_logic_line() {
    // A selector whose FIELD sort is a bitvector, over a datatype. Since Lever
    // A was re-pointed (2026-09-18) the datatype lever no longer answers `ALL`
    // here, so the field sort has to reach the logic line ON ITS OWN — which is
    // what this test was written to check, and what `QF_UFBVDT` records.
    let sel = Formula::Eq(
        Box::new(Formula::Sel {
            datatype: "Expr".into(),
            field: "ec".into(),
            field_sort: Sort::BitVec(32),
            arg: Box::new(Formula::Var("e".into(), expr_by_name())),
        }),
        Box::new(Formula::BitVec { value: 0, width: 32 }),
    );
    assert_eq!(crate::smt2_export::detect_logic(&sel), "QF_UFBVDT");
    assert_transcript_self_consistent(&sel, "Sel field sort");

    // An uninterpreted FUNCTION applied to a float argument: the declaration
    // line writes the FP sort, so the logic must admit it even though no
    // variable in the formula is FP-sorted.
    let formula = Formula::Eq(
        Box::new(Formula::FnApp {
            func: "h".into(),
            args: vec![Formula::FpNaN { eb: 11, sb: 53 }],
            sort: Sort::Int,
        }),
        Box::new(Formula::Int(0)),
    );
    let text = problem_smt2(&formula);
    assert!(
        text.contains("(declare-fun h ((_ FloatingPoint 11 53)) Int)"),
        "the transcript must declare h at its applied argument sort:\n{text}"
    );
    assert_transcript_self_consistent(&formula, "FnApp argument sort");
}

/// A quantifier whose bound variable is never USED: the binder sort is not a
/// `children()` edge, so only the shared sort-position inventory sees it.
#[test]
fn unused_quantifier_binder_sort_still_reaches_the_logic_line() {
    let formula =
        Formula::Forall(vec![("unused".into(), Sort::BitVec(16))], Box::new(Formula::Bool(true)));
    // Quantifiers + bitvectors is `BV`, and the point is that the selector has
    // to have SEEN the binder sort to get there: a walk that missed it would
    // answer `QF_UF` over a transcript whose own `forall` binds a `(_ BitVec
    // 16)`. (This asserted `ALL` while the table under-stated itself to stay
    // monotone; the precise name is back, and the property being tested — the
    // binder sort reaching the logic line — is the same either way.)
    assert_eq!(crate::smt2_export::detect_logic(&formula), "BV");
    assert_transcript_self_consistent(&formula, "unused BV binder");
}

/// Both datatype spellings, each on its own, produce a well-formed preamble
/// under a datatype-capable logic.
///
/// LEVER A, RE-POINTED 2026-09-18: the two spellings no longer head the same
/// name, and the difference is the point. A BY-NAME reference carries no field
/// sorts at all, so its record is `{Datatypes}` and it heads `QF_DT`; the FULL
/// definition names a `(_ BitVec 32)` field, which `sort_theories` now follows
/// into, so its record is `{Datatypes, BitVectors}` and it heads `QF_UFBVDT`.
/// Before that recursion landed the full spelling headed `QF_DT` too, over a
/// `(declare-datatype …)` line writing a bitvector sort — the exact
/// over-narrow header `assert_transcript_self_consistent` exists to catch, and
/// the module's fuzz did catch it.
#[test]
fn both_datatype_spellings_export_a_self_consistent_transcript() {
    for (label, sort, expected) in
        [("full", expr_full(), "QF_UFBVDT"), ("by-name", expr_by_name(), "QF_DT")]
    {
        let formula = Formula::Eq(
            Box::new(Formula::Var("e".into(), sort.clone())),
            Box::new(Formula::Var("e".into(), sort)),
        );
        assert_eq!(crate::smt2_export::detect_logic(&formula), expected, "{label}");
        assert_transcript_self_consistent(&formula, label);
    }
}

// ── The FP -> BV width boundary (the second residual) ────────────────────────

/// THE FP WIDTH BOUNDARY, at the MEASURED edge of the agreeing domain — 64,
/// signed and unsigned alike (see `fp_to_bv_agreeing_width` for the
/// measurement: ay's FP bit-blaster computes the target format's extremal
/// values in `u64`, so the native lane panics above 64 signed and clamps to the
/// wrong maximum above 64 unsigned). The text lane is exact at EVERY width
/// since trust-ir `4ac1b25c`, so 64 is now ay's encode limit alone, not a
/// disagreement between the lanes.
///
/// Checked here on the TEXT side: at the boundary width the transcript must be
/// producible, and must carry the exact clamp literals at the exact literal
/// widths the BigInt lane builds.
#[test]
fn fp_to_bv_text_lane_matches_the_bigint_bounds_at_the_domain_edge() {
    // Signed: the largest admitted width is 64 — ay's native encode limit.
    // The text lane itself is exact at every width.
    let w: u32 = 64;
    let formula = Formula::Eq(
        Box::new(Formula::FpToSbv {
            rm: rm(),
            value: Box::new(Formula::FpNaN { eb: 11, sb: 53 }),
            width: w,
            eb: 11,
            sb: 53,
        }),
        Box::new(Formula::BitVec { value: 0, width: w }),
    );
    let text = problem_smt2(&formula);
    // The exact constants the BigInt lane builds, at the same literal widths.
    let two_pow = |n: u32| {
        let mut v = vec![0u8; 0];
        v.clear();
        // 2^n as a decimal string, built without u128.
        let mut digits = vec![1u32];
        for _ in 0..n {
            let mut carry = 0u32;
            for d in &mut digits {
                let x = *d * 2 + carry;
                *d = x % 10;
                carry = x / 10;
            }
            if carry > 0 {
                digits.push(carry);
            }
        }
        digits.iter().rev().map(|d| char::from(b'0' + *d as u8)).collect::<String>()
    };
    let pos = two_pow(w - 1);
    assert!(
        text.contains(&format!("(_ bv{pos} {})", w + 1)),
        "the positive clamp bound 2^(w-1) must be emitted at width w+1:\n{text}"
    );
    assert!(
        text.contains(&format!("(_ bv{pos} {w})")),
        "the signed MIN clamp value 2^(w-1) must be emitted at width w:\n{text}"
    );
    assert_transcript_self_consistent(&formula, "FpToSbv at the signed boundary width 64");

    // Unsigned: the largest agreeing width is also 64 — ay's unsigned branch
    // does not panic above it, but it clamps its representable maximum to
    // `u64::MAX` instead of `2^w - 1`, which is a silent divergence rather than
    // a fail-closed one.
    let w: u32 = 64;
    let formula = Formula::Eq(
        Box::new(Formula::FpToUbv {
            rm: rm(),
            value: Box::new(Formula::FpNaN { eb: 11, sb: 53 }),
            width: w,
            eb: 11,
            sb: 53,
        }),
        Box::new(Formula::BitVec { value: 0, width: w }),
    );
    let text = problem_smt2(&formula);
    assert!(
        text.contains(&format!("(_ bv{} {})", two_pow(w), w + 1)),
        "the unsigned clamp bound 2^w must be emitted at width w+1:\n{text}"
    );
    assert_transcript_self_consistent(&formula, "FpToUbv at the unsigned boundary width 64");
}

/// Above the qualified width the router still declines. Current AY can
/// encode wider conversions; these direct measurements do not qualify every
/// operand's native/text agreement, so this pins the conservative policy.
#[test]
fn fp_to_bv_above_the_agreeing_width_is_declined_by_the_router() {
    use trust_types::{SourceSpan, VcKind, VerificationCondition};

    use crate::backend_trait::VerificationBackend;

    for (signed, width) in [(true, 65u32), (false, 65u32)] {
        let value = Box::new(Formula::FpNaN { eb: 11, sb: 53 });
        let conv = if signed {
            Formula::FpToSbv { rm: rm(), value, width, eb: 11, sb: 53 }
        } else {
            Formula::FpToUbv { rm: rm(), value, width, eb: 11, sb: 53 }
        };
        let formula = Formula::Eq(Box::new(conv), Box::new(Formula::BitVec { value: 0, width }));
        assert_eq!(
            check_formula_sort(&formula),
            Ok(Sort::Bool),
            "the shape is WELL SORTED — the gate is about lane agreement, not sorts"
        );
        let backend = crate::in_process_ay_backend::InProcessAyBackend::new();
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "fp_width_boundary".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
            obligation: None,
        };
        let outcome = backend.verify(&vc);
        let reason = format!("{outcome:?}");
        assert!(
            reason.contains("saturating fp.to_")
                && reason.contains("above the qualified width 64")
                && reason.contains("bitblast.rs"),
            "width {width} (signed={signed}) must be DECLINED with the qualification \
             reason, got: {reason}"
        );
    }
}

/// AY's BigInt bounds removed the old signed panic at width 65.
/// Check the bridge expansion directly across that historical boundary;
/// the router qualification gate remains a separate, fail-closed policy.
#[test]
fn the_native_lane_encodes_fp_to_sbv_across_the_old_host_word_boundary() {
    for width in [64, 65, 127, 128, 200] {
        assert!(native_fp_to_sbv_encodes(width), "width {width} must encode");
    }
}

/// Build the bridge's guarded `FpToSbv` expansion at `width` and hand it to ay,
/// returning whether ay encoded it without panicking.
fn native_fp_to_sbv_encodes(width: u32) -> bool {
    use ay_bindings::AYProgram;
    use ay_bindings::execute_direct::execute_incremental;

    let formula = Formula::Eq(
        Box::new(Formula::FpToSbv {
            rm: rm(),
            value: Box::new(Formula::FpNaN { eb: 11, sb: 53 }),
            width,
            eb: 11,
            sb: 53,
        }),
        Box::new(Formula::BitVec { value: 0, width }),
    );
    assert_eq!(check_formula_sort(&formula), Ok(Sort::Bool), "the probe must be well sorted");

    // ay's executor carries shared, non-reentrant state; take the same lock the
    // in-process backend does.
    let _guard = trust_types::ay_exec_lock().lock().unwrap_or_else(|e| e.into_inner());

    let outcome = crate::test_panic_hook::catch_unwind_silently(|| {
        let mut program = AYProgram::new();
        // The NATIVE lane's own name (see `in_process_ay_backend::
        // native_lane_logic`): this probe drives `execute_incremental`, so a
        // name `parse_logic` refuses would report "did not encode" for a header
        // defect rather than for the encoding boundary this measures.
        program.set_logic(crate::in_process_ay_backend::native_lane_logic(
            crate::smt2_export::formula_features(&formula),
        ));
        // Fallible: a formula this lane refuses to lower is not an encoding
        // this measurement can make, so report it as "did not encode" rather
        // than unwrapping into the caught-panic path below.
        let Ok(expr) = trust_types::ay_bridge::formula_to_expr(&formula) else {
            return false;
        };
        program.assert(expr);
        program.check_sat();
        execute_incremental(&program).is_ok()
    });

    outcome.unwrap_or(false)
}

/// THE `QF_FP` / BITVECTOR INCONSISTENCY (the second low).
///
/// `Formula::FpConst` lowers — on both lanes — to
/// `((_ to_fp eb sb) (_ bv<bits> eb+sb))`: an FP literal built out of a
/// BITVECTOR literal. This checker charges `Req::BitVectors` for a `(_ bvN W)`
/// atom, the shared table says `QF_FP` admits no bitvectors, and
/// `analyze_formula` used to set only the float bit for `FpConst` — three
/// statements that cannot all be right. SMT-LIB settles it: the
/// `to_fp`-from-bitvector form belongs to the combined BV+FP fragment
/// (`QF_BVFP`), not to `QF_FP`, so the FEATURE SIDE was the wrong one and now
/// sets both bits. The three agree, and this pins the agreement from the text.
#[test]
fn an_fp_bit_pattern_literal_is_not_headed_by_qf_fp() {
    let formula = Formula::FpEq(
        Box::new(Formula::FpConst { bits: 0x4009_21FB_5444_2D18, eb: 11, sb: 53 }),
        Box::new(Formula::FpNaN { eb: 11, sb: 53 }),
    );
    assert_eq!(check_formula_sort(&formula), Ok(Sort::Bool));

    let text = problem_smt2(&formula);
    assert!(
        text.contains("((_ to_fp 11 53) (_ bv"),
        "the FpConst lowering must carry a bitvector literal:\n{text}"
    );
    assert_ne!(
        crate::smt2_export::detect_logic(&formula),
        "QF_FP",
        "a transcript carrying a `(_ bvN W)` literal cannot be headed by a logic with no \
         bitvector theory:\n{text}"
    );
    assert_transcript_self_consistent(&formula, "FpConst bit pattern");

    // …while the FP literals whose SMT-LIB spelling mentions no other theory
    // keep the precise pure-FP name.
    let pure = Formula::FpIsNaN(Box::new(Formula::FpNaN { eb: 11, sb: 53 }));
    assert_eq!(crate::smt2_export::detect_logic(&pure), "QF_FP");
    assert_transcript_self_consistent(&pure, "pure FP literal");
}

/// THE MEASURED M1 SHAPE, pinned from the text.
///
/// `And([Gt(Var(x, Int), Int(0)), FpIsNaN(f)])` was exported as
/// `(set-logic QF_FP)` over `(declare-fun __trust_u_x () Int)` — the logic line
/// declaring a sort it does not admit — in 8 of 2000 generated transcripts.
/// The cause was structural, not a missing case: `detect_logic`'s
/// floating-point arm returned before anything read `has_integers`, which
/// `analyze_formula` had computed correctly all along. The selector is now a
/// total function of the whole feature record, so no arm can decide early.
///
/// WHAT THE TWO CASES PIN, and why they no longer pin the same NAME. The
/// property under test is that the header ADMITS the mixture, never that it is
/// `ALL`; the SMT-LIB name audit gave one of the two mixtures a real name:
///
/// * `Int` — still `ALL`. Every SMT-LIB logic admitting floats and integers
///   together (`QF_UFFPDTNIRA`, `UFFPDTNIRA`, `AUFFPDTNIRA`, `AUFBVFPDTNIRA`)
///   also admits DATATYPES **and** NONLINEARITY, so a row for it would
///   re-point three dimensions at once to buy one. Re-pointing Lever A
///   (2026-09-18) deliberately did not reach this class, so the top is still
///   the honest answer. This is the exact shape M1 was reported as.
/// * `Real` — now `QF_FPLRA`, a real SMT-LIB name for floats with linear real
///   arithmetic. It was `ALL` for want of a row. The M1 property is unchanged
///   and is what the assertion below actually checks: the header admits both
///   FLOATS and REALS, and is not `QF_FP`.
///
/// `assert_transcript_self_consistent` re-derives the requirement from the
/// EMITTED TEXT in both cases, so neither name can pass this vacuously.
#[test]
fn floating_point_mixed_with_integer_arithmetic_is_not_headed_by_qf_fp() {
    for (label, other, expected, mixed_in) in [
        (
            "Int",
            Formula::Gt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0))),
            "ALL",
            Req::Ints,
        ),
        (
            "Real",
            Formula::Gt(
                Box::new(Formula::Var("r".into(), Sort::Real)),
                Box::new(Formula::rat_from_int(0)),
            ),
            "QF_FPLRA",
            Req::Reals,
        ),
    ] {
        let formula = Formula::And(vec![
            other,
            Formula::FpIsNaN(Box::new(Formula::Var("f".into(), Sort::Float { eb: 11, sb: 53 }))),
        ]);
        assert_eq!(check_formula_sort(&formula), Ok(Sort::Bool), "[{label}] well sorted");
        let logic = crate::smt2_export::detect_logic(&formula);
        assert_ne!(
            logic, "QF_FP",
            "[{label}] the M1 defect: a logic line narrower than its own \
             declarations"
        );
        // THE PROPERTY, independent of the name: the header admits the float
        // AND the other arithmetic sort it is mixed with.
        assert!(
            allows(admissibility(&logic), Req::Floats) && allows(admissibility(&logic), mixed_in),
            "[{label}] `{logic}` must admit BOTH floats and {label} arithmetic"
        );
        // The name itself, pinned so a table edit that re-points either case
        // shows up here rather than silently.
        assert_eq!(logic, expected, "[{label}] the name this mixture heads is pinned");
        assert_transcript_self_consistent(&formula, &format!("FP mixed with {label}"));
    }
}

/// THE LINEARITY SHAPE, pinned from the text — the same defect class as M1, one
/// dimension over.
///
/// `(assert (> (* x y) 0))` used to be exported as `(set-logic QF_LIA)`: the
/// linear integer logic is defined over LINEAR terms, so the logic line was
/// narrower than the assertion beneath it, and a strict replayer of the
/// transcript is entitled to reject that evidence. With
/// `Theories::NONLINEAR` in the shared record the header is `QF_NIA`, and
/// because `Req::Nonlinear` is charged HERE from the emitted s-expression, a
/// regression cannot pass this check vacuously: the checker reads the
/// assertion, not the classifier.
///
/// The linear companions are pinned in the same test, because the risk of this
/// dimension is the false POSITIVE — a literal multiplier is a linear term, and
/// calling every `*` nonlinear would send ordinary VCs to `QF_NIA`.
#[test]
fn nonlinear_integer_arithmetic_is_not_headed_by_qf_lia() {
    // THE CHECK IS NOT VACUOUS: the linear logics genuinely refuse the
    // requirement, so a regression that re-headed `(* x y)` with `QF_LIA` would
    // be caught here and not merely pass under a permissive row.
    for linear in ["QF_LIA", "QF_LRA", "QF_LIRA", "LIA", "QF_UFLIA", "AUFLIA"] {
        assert!(
            !allows(admissibility(linear), Req::Nonlinear),
            "`{linear}` must NOT admit a nonlinear term"
        );
    }
    for nonlinear in ["QF_NIA", "QF_NRA", "NIA", "QF_UFNIA", "QF_AUFNIA", "AUFNIRA", "ALL"] {
        assert!(
            allows(admissibility(nonlinear), Req::Nonlinear),
            "`{nonlinear}` must admit a nonlinear term"
        );
    }

    let x = || Formula::Var("x".into(), Sort::Int);
    let y = || Formula::Var("y".into(), Sort::Int);
    let positive = |term: Formula| Formula::Gt(Box::new(term), Box::new(Formula::Int(0)));

    // OUTSIDE `QF_LIA`, each for the reason its [S1] `:language` gives: a
    // product of two symbols; `div`/`mod` with ANY divisor (excluded by name —
    // a numeral divisor buys nothing); and a coefficient times a COMPOUND term,
    // which is not `(* c x)` with `x` a free constant.
    for (label, term) in [
        ("x * y", Formula::Mul(Box::new(x()), Box::new(y()))),
        ("x div y", Formula::Div(Box::new(x()), Box::new(y()))),
        ("x rem y", Formula::Rem(Box::new(x()), Box::new(y()))),
        ("x div 2", Formula::Div(Box::new(x()), Box::new(Formula::Int(2)))),
        ("x rem 2", Formula::Rem(Box::new(x()), Box::new(Formula::Int(2)))),
        (
            "3 * (x + y)",
            Formula::Mul(
                Box::new(Formula::Int(3)),
                Box::new(Formula::Add(Box::new(x()), Box::new(y()))),
            ),
        ),
    ] {
        let formula = positive(term);
        assert_eq!(check_formula_sort(&formula), Ok(Sort::Bool), "[{label}] well sorted");
        assert_eq!(
            crate::smt2_export::detect_logic(&formula),
            "QF_NIA",
            "[{label}] is outside the linear integer fragment and must not be headed by `QF_LIA`"
        );
        assert_transcript_self_consistent(&formula, label);
    }
    // …and a coefficient times an APPLIED uninterpreted function carries UF
    // into the `N` name.
    let scaled_uf = positive(Formula::Mul(
        Box::new(Formula::Int(3)),
        Box::new(Formula::FnApp { func: "f".into(), args: vec![x()], sort: Sort::Int }),
    ));
    assert_eq!(check_formula_sort(&scaled_uf), Ok(Sort::Bool));
    assert_eq!(crate::smt2_export::detect_logic(&scaled_uf), "QF_UFNIA", "[3 * f(x)]");
    assert_transcript_self_consistent(&scaled_uf, "3 * f(x)");

    // INSIDE `QF_LIA`: a sum, and the two `:extensions` shapes with an integer
    // coefficient — positive, `(- n)`, on either side.
    for (label, term) in [
        ("3 * x", Formula::Mul(Box::new(Formula::Int(3)), Box::new(x()))),
        ("x * 3", Formula::Mul(Box::new(x()), Box::new(Formula::Int(3)))),
        ("-3 * x", Formula::Mul(Box::new(Formula::Int(-3)), Box::new(x()))),
        (
            "(- 3) * x",
            Formula::Mul(Box::new(Formula::Neg(Box::new(Formula::Int(3)))), Box::new(x())),
        ),
        ("x + y", Formula::Add(Box::new(x()), Box::new(y()))),
    ] {
        let formula = positive(term);
        assert_eq!(check_formula_sort(&formula), Ok(Sort::Bool), "[{label}] well sorted");
        assert_eq!(
            crate::smt2_export::detect_logic(&formula),
            "QF_LIA",
            "[{label}] is a LINEAR term and must stay in the linear logic"
        );
        assert_transcript_self_consistent(&formula, label);
    }
    // …and the rational coefficient of `QF_LRA`'s `:extensions`, `(/ c n)`.
    let r = || Formula::Var("r".into(), Sort::Real);
    let half_r = Formula::Gt(
        Box::new(Formula::Mul(
            Box::new(Formula::rat("1", "2").expect("canonical rational")),
            Box::new(r()),
        )),
        Box::new(Formula::rat_from_int(0)),
    );
    assert_eq!(check_formula_sort(&half_r), Ok(Sort::Bool));
    assert_eq!(crate::smt2_export::detect_logic(&half_r), "QF_LRA", "[(1/2) * r]");
    assert_transcript_self_consistent(&half_r, "(1/2) * r");
}

/// ARRAY SORTS BIND THE HEADER BY SHAPE, read off the emitted `declare-fun`
/// line: `(Array Int Int)` heads a `*ALIA` name, a positive-width
/// `(Array (_ BitVec i) (_ BitVec j))` heads a `*ABV` name, and every other
/// shape heads a name whose [S1] declaration admits an arbitrary array sort
/// (`QF_AX`, `AUFNIRA`) or the top.
#[test]
fn array_transcripts_bind_index_and_element_fragments() {
    let int_int = Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int));
    for (index, element, expected) in [
        (Sort::Bool, Sort::Bool, "QF_AX"),
        (Sort::Int, Sort::Bool, "AUFNIRA"),
        (Sort::Int, int_int.clone(), "AUFNIRA"),
        (Sort::BitVec(8), Sort::Bool, "ALL"),
        (Sort::Bool, Sort::BitVec(8), "ALL"),
        (Sort::Int, Sort::BitVec(8), "ALL"),
        (Sort::Int, Sort::Int, "QF_ALIA"),
        (Sort::BitVec(8), Sort::BitVec(32), "QF_ABV"),
    ] {
        let sort = Sort::Array(Box::new(index), Box::new(element));
        let label = format!("{sort:?}");
        let formula =
            Formula::Eq(Box::new(var("a", sort.clone())), Box::new(var("b", sort.clone())));
        assert_eq!(check_formula_sort(&formula), Ok(Sort::Bool), "[{label}] well sorted");
        let text = problem_smt2(&formula);
        assert_eq!(
            parse_all(&text)[0].items()[1].atom(),
            Some(expected),
            "[{label}] the header is pinned by the array's shape:\n{text}"
        );
        // The header admits the shape BY THE TABLE — a wide shape only under a
        // row carrying `WIDE_ARRAY` — and the transcript is self-consistent
        // with the shape read off its own declaration.
        let wide = !matches!(expected, "QF_ALIA" | "QF_ABV");
        assert_eq!(allows(admissibility(expected), Req::WideArray), wide, "[{label}]");
        assert_transcript_self_consistent(&formula, &label);
    }
}

/// THE INDEPENDENT ORACLE REJECTS NARROWED TRANSCRIPTS — pure text in, no
/// `Formula`, no classifier.
///
/// Every requirement in this file is written from the [S1] declarations and
/// measured against the shared admissibility TABLE, never against the
/// production classifiers, so a defect planted in the TEXT is caught even if
/// `node_theories`/`sort_theories` were edited to agree with it. Each narrowed
/// transcript below is one the production lane can no longer emit; the oracle
/// must still reject it, and must accept the same body under `ALL` and the
/// legal bodies under their precise names.
///
/// THE LINEAR ROW SET IS DERIVED FROM THE TABLE, not listed by hand: every row
/// admitting `INTS` or `REALS` without `NONLINEAR` is a name whose declaration
/// excludes `div`/`mod`, so `(div x 2)` under any of them is an unmet
/// `Nonlinear` requirement.
#[test]
fn independent_fragment_oracle_rejects_narrowed_transcripts() {
    let transcript = |logic: &str, body: &str| format!("(set-logic {logic})\n{body}\n(check-sat)");
    let unmet_kinds = |logic: &str, body: &str| -> Vec<Req> {
        unmet_transcript_requirements(&transcript(logic, body), &format!("{logic}: {body}"))
            .into_iter()
            .map(|(req, _)| req)
            .collect()
    };

    // NARROWED: each body under a header its [S1] declaration does not admit.
    for (body, narrow, expected) in [
        (
            "(declare-fun x () Int) (declare-fun y () Int) (assert (> (* x y) 0))",
            "QF_LIA",
            Req::Nonlinear,
        ),
        (
            "(declare-fun r () Real) (declare-fun t () Real) (assert (> (/ r t) 0))",
            "QF_LRA",
            Req::Nonlinear,
        ),
        ("(declare-fun x () Int) (assert (= (div x 2) 1))", "QF_LIA", Req::Nonlinear),
        ("(declare-fun x () Int) (assert (= (mod x 2) 1))", "QF_LIA", Req::Nonlinear),
        // `(- (- 3))` is neither `n` nor `(- n)`.
        ("(declare-fun x () Int) (assert (> (* (- (- 3)) x) 0))", "QF_LIA", Req::Nonlinear),
        // `(- (/ 1 2))` is none of `QF_LRA`'s `d`, `(- d)`, `(/ c n)`.
        ("(declare-fun r () Real) (assert (> (* (- (/ 1 2)) r) 0))", "QF_LRA", Req::Nonlinear),
        (
            "(declare-fun x () Int) (declare-fun y () Int) (assert (> (* 3 (+ x y)) 0))",
            "QF_LIA",
            Req::Nonlinear,
        ),
        (
            "(declare-fun f (Int) Int) (declare-fun x () Int) (assert (> (* 3 (f x)) 0))",
            "QF_UFLIA",
            Req::Nonlinear,
        ),
        ("(declare-fun a () (Array Bool Bool)) (assert (= a a))", "QF_ABV", Req::WideArray),
        (
            "(declare-fun a () (Array Int (Array Int Int))) (assert (= a a))",
            "QF_AUFLIA",
            Req::WideArray,
        ),
        ("(declare-fun a () (Array Int Bool)) (assert (= a a))", "QF_ALIA", Req::WideArray),
        (
            "(declare-fun a () (Array (_ BitVec 0) (_ BitVec 8))) (assert (= a a))",
            "QF_ABV",
            Req::WideArray,
        ),
    ] {
        let unmet = unmet_kinds(narrow, body);
        assert!(
            unmet.contains(&expected),
            "the oracle must reject `(set-logic {narrow})` over `{body}` with {expected:?}; it \
             reported {unmet:?}"
        );
        assert!(unmet_kinds("ALL", body).is_empty(), "`ALL` admits `{body}`");
    }

    // LEGAL: the `:extensions` shapes and the declared array shapes, under
    // their precise names.
    for (body, logic) in [
        ("(declare-fun x () Int) (assert (> (* (- 3) x) 0))", "QF_LIA"),
        ("(declare-fun x () Int) (assert (> (* x 3) 0))", "QF_LIA"),
        ("(declare-fun r () Real) (assert (> (* (/ 1 2) r) 0))", "QF_LRA"),
        ("(declare-fun r () Real) (assert (> (* (/ (- 1) 2) r) 0))", "QF_LRA"),
        ("(declare-fun a () (Array Int Int)) (assert (= a a))", "QF_AUFLIA"),
        ("(declare-fun a () (Array Int Int)) (assert (= a a))", "QF_ALIA"),
        ("(declare-fun a () (Array (_ BitVec 8) (_ BitVec 32))) (assert (= a a))", "QF_ABV"),
        ("(declare-fun a () (Array Bool Bool)) (assert (= a a))", "QF_AX"),
        ("(declare-fun a () (Array Int Bool)) (assert (= a a))", "AUFNIRA"),
    ] {
        let unmet = unmet_kinds(logic, body);
        assert!(unmet.is_empty(), "`(set-logic {logic})` admits `{body}`; reported {unmet:?}");
    }

    // EVERY LINEAR ROW REFUSES `div` — derived from the table.
    let linear_rows: Vec<&str> = trust_types::logic_lattice::LOGIC_LATTICE
        .iter()
        .filter(|row| {
            (row.admits.contains(Theories::INTS) || row.admits.contains(Theories::REALS))
                && !row.admits.contains(Theories::NONLINEAR)
        })
        .map(|row| row.name)
        .collect();
    assert!(linear_rows.contains(&"QF_LIA") && linear_rows.contains(&"QF_IDL"));
    // MEASURED 2026-09-22 over this revision's `LOGIC_LATTICE`: 29 rows admit
    // `INTS` or `REALS` without `NONLINEAR` (the two difference rows, the
    // `*LIA`/`*LRA`/`*LIRA` names and their UF/array/BV/FP/DT relatives). The
    // count is pinned so a row added to or dropped from the linear family
    // shows up here, and so the loop below cannot pass vacuously.
    assert_eq!(linear_rows.len(), 29, "the derived linear row set: {linear_rows:?}");
    for logic in &linear_rows {
        let unmet = unmet_kinds(logic, "(declare-fun x () Int) (assert (= (div x 2) 1))");
        assert!(
            unmet.contains(&Req::Nonlinear),
            "`{logic}` is a linear name and must refuse `(div x 2)`; reported {unmet:?}"
        );
    }
    // …and no `N` row that admits integers does.
    for row in trust_types::logic_lattice::LOGIC_LATTICE {
        if row.admits.contains(Theories::NONLINEAR) && row.admits.contains(Theories::INTS) {
            let unmet = unmet_kinds(row.name, "(declare-fun x () Int) (assert (= (div x 2) 1))");
            assert!(!unmet.contains(&Req::Nonlinear), "`{}` admits `div`: {unmet:?}", row.name);
        }
    }
}

/// THE LINEAR-FORM SHAPE, AND THE PROOF THAT THIS CHECKER CAN FAIL ON IT.
///
/// A checker that cannot fail on a planted defect is not a checker, and until
/// [`Req::WideArith`] existed this one could not fail on the defect class
/// `Theories::WIDE_ARITH` was added to prevent: an over-narrow `QF_IDL`/`QF_RDL`
/// header. The test plants exactly that.
///
/// WHY THE DEFECT HAS TO BE PLANTED IN THE TEXT. `problem_smt2` heads
/// `(assert (<= (+ x y) 10))` with `QF_LIA`, correctly — so there is no formula
/// that makes the production lane emit the defect, and handing this checker a
/// `Formula` could never exercise the new requirement's failure path. The
/// transcript is therefore taken REAL and its header alone is narrowed by one
/// dimension, which is precisely the shape a record-builder that forgot
/// `wide_arithmetic_theories` would produce (see `smt2_export::analyze_formula`
/// step (4), whose omission would answer `QF_IDL` for every integer query).
///
/// THE THREE CASES, in the order that makes the result mean something:
///
/// 1. the CONTROL — the undoctored transcript has NO unmet requirement, so the
///    rejection below is caused by the header and not by the machinery;
/// 2. the PLANTED DEFECT — with `QF_IDL` in the header, the checker reports
///    `Req::WideArith` unmet;
/// 3. the NON-VACUITY GUARD — a genuinely difference-shaped assertion, whose
///    real header IS `QF_IDL`, passes. Without this the requirement could be
///    "charge `WideArith` always", which would reject case 2 for free and would
///    have broken every integer transcript in the file.
#[test]
fn an_over_narrow_difference_logic_header_is_rejected() {
    let x = || Formula::Var("x".into(), Sort::Int);
    let y = || Formula::Var("y".into(), Sort::Int);

    // A GENERAL arithmetic atom: `x + y <= 10`. Not an atom of either
    // difference declaration.
    let general = Formula::Le(
        Box::new(Formula::Add(Box::new(x()), Box::new(y()))),
        Box::new(Formula::Int(10)),
    );
    assert_eq!(check_formula_sort(&general), Ok(Sort::Bool));
    let honest = problem_smt2(&general);
    assert!(
        honest.starts_with("(set-logic QF_LIA)"),
        "the production lane heads a general integer atom with the general integer logic:\n{honest}"
    );

    // (1) THE CONTROL.
    assert!(
        unmet_transcript_requirements(&honest, "QF_LIA control").is_empty(),
        "the honestly-headed transcript must be self-consistent:\n{honest}"
    );

    // (2) THE PLANTED DEFECT: the same transcript, header narrowed to the
    // difference logic. `QF_IDL` admits `Theories::INTS` and NOT
    // `Theories::WIDE_ARITH`, so its atom grammar does not contain `(+ x y)`.
    let planted = honest.replacen("(set-logic QF_LIA)", "(set-logic QF_IDL)", 1);
    assert_ne!(planted, honest, "the header must actually have been narrowed");
    let unmet = unmet_transcript_requirements(&planted, "planted QF_IDL");
    assert!(
        unmet.iter().any(|(req, _)| *req == Req::WideArith),
        "the checker must REJECT `(set-logic QF_IDL)` over `(+ x y)`; it reported {unmet:?}\n\
         {planted}"
    );
    // …and the report NAMES THE HEADER it failed against, so a real failure
    // tells the reader which logic line was too narrow rather than only that
    // something was.
    let (_, why) =
        unmet.iter().find(|(req, _)| *req == Req::WideArith).expect("just asserted present");
    assert!(
        why.contains("(set-logic QF_IDL)") && why.contains("WideArith"),
        "the rejection must name the offending header and the dimension: {why}"
    );

    // (3) THE NON-VACUITY GUARD: `x - y > 3` IS an atom of `QF_IDL`'s
    // declaration, the production lane heads it `QF_IDL`, and the checker must
    // accept that — otherwise the requirement is "always charged" and case (2)
    // proves nothing.
    let difference = Formula::Gt(
        Box::new(Formula::Sub(Box::new(x()), Box::new(y()))),
        Box::new(Formula::Int(3)),
    );
    assert_eq!(check_formula_sort(&difference), Ok(Sort::Bool));
    assert_eq!(
        crate::smt2_export::detect_logic(&difference),
        "QF_IDL",
        "a difference-shaped atom heads the difference logic"
    );
    let text = problem_smt2(&difference);
    assert!(
        unmet_transcript_requirements(&text, "QF_IDL difference").is_empty(),
        "a genuinely difference-shaped transcript must NOT be charged the wide requirement:\n{text}"
    );
    assert_transcript_self_consistent(&difference, "QF_IDL difference");

    // THE REQUIREMENT IS NOT VACUOUS AT THE TABLE EITHER: the difference rows
    // genuinely refuse it and the general rows genuinely admit it, so a table
    // edit that widened `QF_IDL` would show up here rather than silently.
    for narrow in ["QF_IDL", "QF_RDL"] {
        assert!(
            !allows(admissibility(narrow), Req::WideArith),
            "`{narrow}` must NOT admit a non-difference arithmetic atom"
        );
    }
    for wide in ["QF_LIA", "QF_LRA", "QF_LIRA", "LIA", "QF_UFLIA", "AUFLIA", "QF_NIA", "ALL"] {
        assert!(
            allows(admissibility(wide), Req::WideArith),
            "`{wide}` must admit a non-difference arithmetic atom"
        );
    }
}

/// THE BARE BOUND, AND THE ASYMMETRY THIS CHECKER IS DELIBERATELY BUILT WITH.
///
/// `x > 3` is NOT an atom of either difference declaration (neither lists
/// `(op x n)`), so `logic_lattice::is_difference_atom` refuses it and the
/// production lane heads the transcript `QF_LIA`. This checker's recognizer
/// ACCEPTS it — see [`Req::WideArith`] — so it charges nothing, and `QF_LIA`
/// admits the requirement either way.
///
/// The asymmetry is the whole safety argument, so it is pinned rather than
/// described: the checker must charge the requirement NO MORE OFTEN than
/// production charges the bit, because the checker charging MORE is what turns
/// a correctly-headed transcript into a failure here.
#[test]
fn the_checker_charges_the_wide_requirement_no_more_often_than_production() {
    use trust_types::logic_lattice::{Theories, wide_arithmetic_theories};

    let x = || Formula::Var("x".into(), Sort::Int);
    let y = || Formula::Var("y".into(), Sort::Int);
    let p = || Formula::Var("p".into(), Sort::Real);
    let q = || Formula::Var("q".into(), Sort::Real);

    let cases: Vec<(&str, Formula)> = vec![
        // Production charges the bit; so may this checker.
        (
            "x + y <= 10",
            Formula::Le(
                Box::new(Formula::Add(Box::new(x()), Box::new(y()))),
                Box::new(Formula::Int(10)),
            ),
        ),
        (
            "x * 3 > 0",
            Formula::Gt(
                Box::new(Formula::Mul(Box::new(x()), Box::new(Formula::Int(3)))),
                Box::new(Formula::Int(0)),
            ),
        ),
        // Production charges it (the bare bound is not in either declaration);
        // this checker does NOT. The permitted direction.
        ("x > 3", Formula::Gt(Box::new(x()), Box::new(Formula::Int(3)))),
        ("3 < x", Formula::Lt(Box::new(Formula::Int(3)), Box::new(x()))),
        (
            "3 < x - y (mirrored)",
            Formula::Lt(
                Box::new(Formula::Int(3)),
                Box::new(Formula::Sub(Box::new(x()), Box::new(y()))),
            ),
        ),
        // Neither charges it.
        (
            "x - y > 3",
            Formula::Gt(
                Box::new(Formula::Sub(Box::new(x()), Box::new(y()))),
                Box::new(Formula::Int(3)),
            ),
        ),
        ("x < y", Formula::Lt(Box::new(x()), Box::new(y()))),
        ("p < q", Formula::Lt(Box::new(p()), Box::new(q()))),
        // A boolean combination, and a non-arithmetic atom beside it.
        (
            "(x < y) and (x - y > 3)",
            Formula::And(vec![
                Formula::Lt(Box::new(x()), Box::new(y())),
                Formula::Gt(
                    Box::new(Formula::Sub(Box::new(x()), Box::new(y()))),
                    Box::new(Formula::Int(3)),
                ),
            ]),
        ),
        (
            "(x < y) and (x + y > 3)",
            Formula::And(vec![
                Formula::Lt(Box::new(x()), Box::new(y())),
                Formula::Gt(
                    Box::new(Formula::Add(Box::new(x()), Box::new(y()))),
                    Box::new(Formula::Int(3)),
                ),
            ]),
        ),
        ("not (b)", Formula::Not(Box::new(Formula::Var("b".into(), Sort::Bool)))),
    ];

    for (label, formula) in &cases {
        assert_eq!(check_formula_sort(formula), Ok(Sort::Bool), "[{label}] well sorted");
        let production = wide_arithmetic_theories(formula).contains(Theories::WIDE_ARITH);

        // What the CHECKER charges, read off the emitted text with the same
        // machinery `unmet_transcript_requirements` uses.
        let text = problem_smt2(formula);
        let forms = parse_all(&text);
        let mut declared = Declared::default();
        let mut assertion: Option<&Sexp> = None;
        for form in &forms[1..] {
            let items = form.items();
            match items.first().and_then(Sexp::atom).unwrap_or("") {
                "declare-fun" => {
                    let name = items[1].atom().expect("declare-fun name").to_string();
                    declared.functions.insert(name, items[2].items().len());
                }
                "assert" => assertion = Some(&items[1]),
                _ => {}
            }
        }
        let assertion = assertion.expect("every transcript carries an assertion");
        let mut reqs: Vec<(Req, String)> = Vec::new();
        linear_form_requirements(assertion, &declared, &mut Vec::new(), &mut reqs);
        let checker = reqs.iter().any(|(req, _)| *req == Req::WideArith);

        assert!(
            production || !checker,
            "[{label}] the checker charged `Req::WideArith` where production did NOT — that \
             ordering would fail a transcript the selector headed correctly:\n{text}"
        );
        // …and the transcript is self-consistent whichever way the two fall.
        assert_transcript_self_consistent(formula, label);
    }
}

/// THE `N` FAMILY IS REACHABLE FROM A FORMULA, and the transcript each name
/// heads is self-consistent.
///
/// One exhibit per newly reachable name that a `Formula` can actually produce,
/// so the rows are not table decoration: the check parses the emitted text and
/// measures the header against the shared admissibility table, which is the
/// same data `select_logic_name` chose it by.
#[test]
fn every_reachable_nonlinear_logic_name_heads_a_self_consistent_transcript() {
    let xi = || Formula::Var("x".into(), Sort::Int);
    let yi = || Formula::Var("y".into(), Sort::Int);
    let xr = || Formula::Var("p".into(), Sort::Real);
    let yr = || Formula::Var("q".into(), Sort::Real);
    let int_product = || Formula::Mul(Box::new(xi()), Box::new(yi()));
    let real_product = || Formula::Mul(Box::new(xr()), Box::new(yr()));
    let positive_int = |t: Formula| Formula::Gt(Box::new(t), Box::new(Formula::Int(0)));
    let positive_real = |t: Formula| Formula::Gt(Box::new(t), Box::new(Formula::rat_from_int(0)));
    let uf_of =
        |arg: Formula| Formula::FnApp { func: "f".to_string(), args: vec![arg], sort: Sort::Int };
    let real_uf_of =
        |arg: Formula| Formula::FnApp { func: "g".to_string(), args: vec![arg], sort: Sort::Real };
    let array =
        || Formula::Var("arr".into(), Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)));

    let cases: Vec<(&str, Formula)> = vec![
        // {Nonlinear, Ints}
        ("QF_NIA", positive_int(int_product())),
        // {Nonlinear, Reals}
        ("QF_NRA", positive_real(real_product())),
        // {Nonlinear, Ints, Quantifiers}
        (
            "NIA",
            Formula::Forall(
                vec![(trust_types::Symbol::intern("y"), Sort::Int)],
                Box::new(positive_int(int_product())),
            ),
        ),
        // {Nonlinear, Reals, Quantifiers}
        (
            "NRA",
            Formula::Forall(
                vec![(trust_types::Symbol::intern("q"), Sort::Real)],
                Box::new(positive_real(real_product())),
            ),
        ),
        // {Nonlinear, Ints, Arrays}
        (
            "QF_ANIA",
            positive_int(Formula::Mul(
                Box::new(Formula::Select(Box::new(array()), Box::new(xi()))),
                Box::new(yi()),
            )),
        ),
        // {Nonlinear, Ints, UF}
        ("QF_UFNIA", positive_int(Formula::Mul(Box::new(uf_of(xi())), Box::new(yi())))),
        // {Nonlinear, Reals, UF}
        ("QF_UFNRA", positive_real(Formula::Mul(Box::new(real_uf_of(xr())), Box::new(yr())))),
        // {Nonlinear, Ints, Reals}
        ("QF_NIRA", Formula::And(vec![positive_int(int_product()), positive_real(real_product())])),
        // {Nonlinear, Ints, UF, Quantifiers}
        (
            "UFNIA",
            Formula::Forall(
                vec![(trust_types::Symbol::intern("y"), Sort::Int)],
                Box::new(positive_int(Formula::Mul(Box::new(uf_of(xi())), Box::new(yi())))),
            ),
        ),
        // {Nonlinear, Reals, UF, Quantifiers}
        (
            "UFNRA",
            Formula::Forall(
                vec![(trust_types::Symbol::intern("q"), Sort::Real)],
                Box::new(positive_real(Formula::Mul(Box::new(real_uf_of(xr())), Box::new(yr())))),
            ),
        ),
        // {Nonlinear, Ints, Reals, UF, Quantifiers} — no arrays.
        (
            "UFNIRA",
            Formula::Forall(
                vec![(trust_types::Symbol::intern("y"), Sort::Int)],
                Box::new(Formula::And(vec![
                    positive_int(Formula::Mul(Box::new(uf_of(xi())), Box::new(yi()))),
                    positive_real(real_product()),
                ])),
            ),
        ),
        // {Nonlinear, Ints, UF, Arrays}
        (
            "QF_AUFNIA",
            Formula::And(vec![
                positive_int(Formula::Mul(Box::new(uf_of(xi())), Box::new(yi()))),
                Formula::Gt(
                    Box::new(Formula::Select(Box::new(array()), Box::new(xi()))),
                    Box::new(Formula::Int(0)),
                ),
            ]),
        ),
        // {Nonlinear, Ints, UF, Arrays, Quantifiers} — no reals.
        (
            "AUFNIA",
            Formula::Forall(
                vec![(trust_types::Symbol::intern("y"), Sort::Int)],
                Box::new(Formula::And(vec![
                    positive_int(Formula::Mul(Box::new(uf_of(xi())), Box::new(yi()))),
                    Formula::Gt(
                        Box::new(Formula::Select(Box::new(array()), Box::new(xi()))),
                        Box::new(Formula::Int(0)),
                    ),
                ])),
            ),
        ),
        // {Nonlinear, Ints, Reals, UF, Quantifiers, Arrays}
        (
            "AUFNIRA",
            Formula::Forall(
                vec![(trust_types::Symbol::intern("y"), Sort::Int)],
                Box::new(Formula::And(vec![
                    positive_int(Formula::Mul(Box::new(uf_of(xi())), Box::new(yi()))),
                    positive_real(real_product()),
                    Formula::Gt(
                        Box::new(Formula::Select(Box::new(array()), Box::new(xi()))),
                        Box::new(Formula::Int(0)),
                    ),
                ])),
            ),
        ),
    ];

    for (expected, formula) in &cases {
        assert_eq!(
            check_formula_sort(formula),
            Ok(Sort::Bool),
            "[{expected}] the exhibit must be well sorted"
        );
        assert_eq!(
            crate::smt2_export::detect_logic(formula),
            *expected,
            "[{expected}] this shape must head exactly that name"
        );
        assert_transcript_self_consistent(formula, expected);
    }
}
