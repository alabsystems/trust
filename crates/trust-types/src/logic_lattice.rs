// trust-types/logic_lattice.rs: the ONE SMT-LIB logic-name lattice.
//
// Every SMT lane in the workspace has to write a `(set-logic L)` line, and the
// only thing that makes such a line EVIDENCE rather than decoration is that `L`
// admits every theory the rest of the transcript uses. Before this module the
// answer was computed by two independent early-return cascades
// (`trust_types::smt_logic::select_logic` and trust-router's
// `smt2_export::detect_logic`), and a cascade decides on a PREFIX of the
// features: `detect_logic` returned `QF_FP` for
// `And([Gt(Var(x, Int), Int(0)), FpIsNaN(f)])` because the floating-point arm
// fired before anything read `has_integers`, so the transcript declared
// `(declare-fun __trust_u_x () Int)` under a logic with no integer sort.
//
// This module replaces both cascades with a TOTAL function of the feature set:
//
//   1. [`Theories`] — the feature record, one bit per theory dimension.
//   2. [`LOGIC_LATTICE`] — the admissibility table, written ONCE, as data:
//      one row per logic name that may be emitted, saying what that name
//      admits. The selector and the self-consistency test both read THIS
//      table; there is no second hand-written copy to drift from it.
//   3. [`select_logic_name`] — a single decision over all bits: the least row
//      that admits every required theory (a lattice join), `ALL` if none does.
//
// THE INVARIANT, proved by EXHAUSTIVE ENUMERATION of the entire 2^11 feature
// powerset in this module's `tests`:
//
//   ADMISSIBILITY  for every feature set S: `admits(select(S)) ⊇ S`.
//                  (`every_feature_set_selects_an_admitting_logic`)
//
// That is the whole contract, and it is the only property any caller needs —
// INCLUDING the group and batch callers, provided they SELECT FROM THE UNION.
// A group of queries f1…fn asserted under ONE `(set-logic L)` needs `L` to
// admit every feature any member uses, i.e. `admits(L) ⊇ features(f1) ∪ … ∪
// features(fn)`; taking `L = select(⋃ features(fi))` gives exactly that by
// ADMISSIBILITY ALONE. The union is available to every such caller — it is a
// fold of `Theories::union` over formulas the caller already holds — so no
// caller needs the selector to be monotone, and `union_admissibility_covers_
// every_member` pins the argument over all 4_194_304 ordered pairs.
//
// MONOTONICITY (`S1 ⊆ S2` ⇒ `admits(select(S1)) ⊆ admits(select(S2))`) is
// therefore NOT claimed as a general property of this table, and it is NOT
// true of it. It fails on exactly 751 of the 177_147 subset-related pairs, and
// the failures are exactly characterized and pinned by
// `monotonicity_fails_only_from_sets_no_row_names_exactly`: a pair violates it
// only when `S1` is a feature set that NO ROW OF THE TABLE ADMITS EXACTLY
// ([`is_named_exactly`]), and there are exactly 30 such `S1`. The reason is
// structural: when SMT-LIB has no name for `S1` itself, the least admitting
// row must commit to EXTRA dimensions it did not ask for (`{Quantifiers, Ints,
// Reals}` → `AUFLIRA`, which also promises UF), and a superset that SMT-LIB
// does name exactly (`{Quantifiers, Ints, Reals, Nonlinear}` → `UFNIRA`) then
// admits less than it did. Equivalently: whenever
// `S1` is a set the table NAMES, monotonicity HOLDS. No consumer is allowed to
// depend on the failures — see the audit in `select_logic_name`'s docs, which
// cites every call site.
//
// This is the same characterization the table carried when it was stated as
// "S1 is MODIFIER-ONLY" ([`Theories::is_modifier_only`]: built from
// `{Quantifiers, Arrays, UF, Nonlinear}` alone, with no base sort theory) —
// every modifier-only set except `{UF}`, `{Quantifiers, UF}` and the
// array-bearing nonlinear ones is unnamed, which is why that weaker form fit
// the old table exactly. It stopped fitting when the three INVENTED mixed
// linear-arithmetic names (`LIRA`, `UFLIRA`, `QF_UFLIRA`) came out: those rows
// named `{Quantifiers, Ints, Reals}` and its two UF variants EXACTLY, and
// deleting them left three base-sort sets unnamed. `is_modifier_only` survives
// as the sub-characterization it always was, and the test still pins it.
//
// THE NINTH DIMENSION IS LINEARITY, and it is the one that is not a THEORY: an
// SMT-LIB arithmetic logic spells linearity into the family name (`LIA`/`NIA`,
// `LRA`/`NRA`), so `x * y > 0` headed `QF_LIA` — a name admitting only linear
// terms — until `Theories::NONLINEAR` and the `N` rows landed (fourteen then,
// fifteen since `ANIA` joined them, eighteen since the datatype rows did,
// nineteen since Lever C closed). That
// was the same defect class as the `QF_FP`-over-an-`Int`-declaration above,
// one dimension over: a logic line NARROWER than the transcript under it. The
// bit is charged only on the mathematical-integer/real `Mul`/`Div`/`Rem`
// nodes, never on `BvMul` or `fp.mul`, because `QF_BV` and `QF_FP` admit those
// unconditionally and SMT-LIB names no `QF_NBV`.
//
// THE TENTH DIMENSION IS LINEAR FORM, and it is the one that had to be spelled
// BACKWARDS. SMT-LIB's DIFFERENCE LOGICS (`QF_IDL`, `QF_RDL`) admit a STRICT
// SUBFRAGMENT of `{Ints}` / `{Reals}`: only atoms of the shapes their
// declarations list. A record dimension meaning "is difference-only" would be a
// RESTRICTION, and this record's whole semantics is `⊆` — MORE BITS = MORE
// DEMANDED — so a restriction bit would break the subset reading and the union
// property with it (two difference-only queries could union to a set claiming a
// restriction neither conjunct has). [`Theories::WIDE_ARITH`] is therefore the
// bit for the LARGER fragment: it is SET when some arithmetic atom is NOT
// provably difference-shaped, so `{Ints}` (no wide bit) takes `QF_IDL`,
// `{Ints, WideArith}` takes `QF_LIA`, and `S1 ⊆ S2` still reads "S2 demands at
// least what S1 demands". THE CLASSIFIER IS CONSERVATIVE IN THE SOUND
// DIRECTION: [`wide_arithmetic_theories`] charges the bit unless EVERY atom of
// the formula is provably in the fragment, so a shape it does not recognize
// widens the header rather than narrowing it.
//
// ONE SHARED BIT, NOT ONE PER SORT. A per-sort split (`WIDE_INT`/`WIDE_REAL`)
// would take the powerset to 2^11 and buy nothing, because SMT-LIB names NO
// logic that is difference-restricted over one sort and general over the other:
// there is no `IDLLRA`. With one bit a query mixing a general `Real` atom with
// difference-only `Int` atoms charges the bit and takes `QF_LIRA`, which is
// exactly the honest name for it; with two bits it would take the same name by
// a longer route. The shared bit is also the SOUND collapse — it can only ever
// widen — so the cheaper record is the safer one.
//
// THE ELEVENTH DIMENSION IS ARRAY SHAPE, and it is spelled backwards for the
// same reason. The array-bearing [S1] declarations RESTRICT the array sort:
// `QF_AUFLIA` to `(Array Int Int)`, `QF_ABV` to `(Array (_ BitVec i)
// (_ BitVec j))` with `i, j > 0`; only `QF_AX` and `AUFNIRA` admit an
// arbitrary one. A `(Array Bool Bool)` or a nested array under `QF_ALIA` is
// therefore the same over-narrow header as `x * y` under `QF_LIA`, one theory
// over, and until [`Theories::WIDE_ARRAY`] landed the record could not say so
// — every `ARRAYS` row claimed every array. The bit is the DEMAND for the
// larger fragment, charged by [`sort_theories`] on every array sort that is
// neither declared shape, and carried by exactly the rows whose declarations
// place no restriction.
//
// THE LINEAR FRAGMENT IS READ OFF THE DECLARATIONS TOO, since the same
// revision. `QF_LIA`'s `:language` excludes `div`/`mod`/`abs` BY NAME and
// admits `*` only as `(* c x)`/`(* x c)` with `x` a FREE CONSTANT, so `x div 2`
// and `3 * (x + y)` charge [`Theories::NONLINEAR`] exactly as `x * y` does —
// the numeral divisor and the literal coefficient buy nothing the declaration
// grants. See the bit's doc for the quoted text.
//
// EVERY NAME IN THE TABLE IS ATTESTED, and the three sources are cited once
// here so no reader has to re-litigate a spelling (see [`LOGIC_LATTICE`]'s
// PROVENANCE note for which source carries which name):
//
//   [S1] the SMT-LIB standard's own logic declarations, one `Logics/<NAME>.smt2`
//        file each, indexed at <https://smt-lib.org/logics-all.shtml>;
//   [S2] the SMT-LIB benchmark library, which ships ONE ARCHIVE PER LOGIC —
//        `<NAME>.tar.zst` — in "SMT-LIB Release 2025 (non-incremental
//        benchmarks)", <https://zenodo.org/records/15493090>;
//   [S3] the SMT-COMP division lists, `<year>/divisions.json` for 2019…2023 at
//        <https://github.com/SMT-COMP/smt-comp>, which are drawn from the
//        library's logic directories.
//
// A name absent from ALL THREE is not an SMT-LIB logic, and emitting one is a
// defect of the same class as emitting a name that is too narrow: the header
// is not evidence, because no replayer can check it. Three such names were
// carried here and are gone — see the REMOVED note on [`LOGIC_LATTICE`].
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::{Formula, Sort};

// ─────────────────────────────────────────────────────────────────────────────
// 1. THE FEATURE RECORD
// ─────────────────────────────────────────────────────────────────────────────

/// The set of SMT theory dimensions a query uses, or a logic name admits.
///
/// Eleven bits, so the whole powerset is 2048 elements and both properties
/// above are settled by enumeration rather than by sampling.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Theories(u16);

impl Theories {
    /// No theory at all: a purely propositional (Core) query.
    pub const NONE: Self = Self(0);
    /// A `forall`/`exists` binder appears.
    pub const QUANTIFIERS: Self = Self(1 << 0);
    /// An `(Array _ _)` sort is declared, or `select`/`store` is applied.
    pub const ARRAYS: Self = Self(1 << 1);
    /// A `(_ BitVec n)` sort, literal or operator appears.
    pub const BITVECTORS: Self = Self(1 << 2);
    /// The `Int` sort, an integer literal, or an integer-only operator.
    pub const INTS: Self = Self(1 << 3);
    /// The `Real` sort or an exact rational literal.
    pub const REALS: Self = Self(1 << 4);
    /// A `(_ FloatingPoint e s)`/`RoundingMode` sort or an `fp.*` term.
    pub const FLOATS: Self = Self(1 << 5);
    /// An uninterpreted FUNCTION of arity >= 1 is applied. A 0-ary
    /// `declare-fun` is an ordinary free constant, which every SMT-LIB logic
    /// admits, so it is deliberately NOT this bit — the same rule the
    /// transcript self-consistency checker charges `Req::Uf` by.
    pub const UF: Self = Self(1 << 6);
    /// A datatype sort, or a constructor/selector/tester application.
    pub const DATATYPES: Self = Self(1 << 7);
    /// An arithmetic term OUTSIDE the LINEAR fragment appears: a `Mul` that is
    /// not `literal × free constant` (in either order), or ANY `Div`/`Rem`.
    ///
    /// WRITTEN FROM THE [S1] DECLARATION, NOT FROM THE TEXTBOOK. `QF_LIA`'s
    /// `:language` is "Closed quantifier-free formulas built over an arbitrary
    /// expansion of the Ints signature with free constant symbols, but whose
    /// terms of sort Int are all linear, that is, have no occurrences of the
    /// function symbols `**`, `/`, `div`, `mod`, and `abs`, and no occurrences
    /// of the function symbol `*`, except as specified in the :extensions
    /// attribute", and its `:extensions` is "Terms containing `*` with
    /// _concrete_ coefficients are also allowed, that is, terms of the form
    /// `c`, `(* c x)`, or `(* x c)` where `x` is a free constant and `c` is a
    /// term of the form `n` or `(- n)` for some numeral `n`". `QF_LRA` reads
    /// the same way over `*` and `/`, with `c` "an integer or rational
    /// coefficient" — `m`, `(- m)`, a decimal `d`, `(- d)`, or `(/ c n)`.
    ///
    /// Two consequences that the informal "nonlinear" gloss gets wrong, and
    /// that this bit therefore charges:
    ///
    /// * `div`/`mod` are excluded OUTRIGHT — `x div 2` is not a `QF_LIA` term
    ///   whatever its divisor, so EVERY `Div`/`Rem` charges the bit and heads
    ///   the `N` family, whose declarations do not restrict them;
    /// * the non-coefficient factor must be a FREE CONSTANT — `3 * (x + y)`,
    ///   `3 * f(x)` and `3 * (select a i)` are not `(* c x)` with `x` a free
    ///   constant, so they charge the bit too. Only `Var`/`SymVar` of sort
    ///   `Int`/`Real` count as free constants here ([`is_free_constant`]).
    ///
    /// THE DIMENSION IS ARITHMETIC-ONLY AND IT IS A QUALIFIER, NOT A SORT.
    /// SMT-LIB spells linearity into the arithmetic family name (`LIA` vs
    /// `NIA`, `LRA` vs `NRA`) and NOWHERE ELSE: `QF_BV` admits `bvmul` of two
    /// variables unconditionally — there is no `QF_NBV` — and no floating-point
    /// logic carries a linearity qualifier either. So this bit is set for
    /// `Mul`/`Div`/`Rem` on the mathematical-integer/real nodes and NEVER for
    /// `BvMul`/`BvUDiv`/`BvSDiv`/`BvURem`/`BvSRem` or any `Fp*` operator; see
    /// [`node_theories`].
    ///
    /// MULTIPLICATION OF A FREE CONSTANT BY A LITERAL IS LINEAR. `3 * x`,
    /// `x * (-3)` and `(1/2) * r` stay in `QF_LIA`/`QF_LRA`, which is the whole
    /// point of the distinction; everything else `Mul`/`Div`/`Rem` can spell
    /// leaves it. Over-charging is the SOUND direction: an `N` name admits
    /// strictly more, so it cannot turn a SAT violation into UNSAT.
    pub const NONLINEAR: Self = Self(1 << 8);
    /// An arithmetic atom that is NOT provably a DIFFERENCE CONSTRAINT appears
    /// — i.e. the query needs the full `LIA`/`LRA` atom grammar and not just
    /// SMT-LIB's `IDL`/`RDL` subfragment.
    ///
    /// THE BIT IS SPELLED FOR THE LARGER FRAGMENT, DELIBERATELY. The natural
    /// reading of this class is "the query is difference-only", but a bit
    /// meaning THAT is a RESTRICTION, and every other bit here is a DEMAND: the
    /// table's semantics is `required ⊆ admits`, so a restriction bit would
    /// make a superset admit LESS and would break [`Theories::union`] — two
    /// difference-only queries asserted under one `(set-logic …)` would union
    /// to a set still claiming the restriction even after a general atom joined
    /// them. Charging the bit for the WIDER fragment keeps the subset reading:
    /// `{INTS}` ⊂ `{INTS, WIDE_ARITH}`, `QF_IDL` ⊂ `QF_LIA`, and a union is
    /// wide as soon as either side is.
    ///
    /// CONSERVATIVE IN THE SOUND DIRECTION. [`wide_arithmetic_theories`] sets
    /// this bit unless EVERY atom of the formula is provably inside the
    /// difference grammar its sort's declaration writes down. Failing to set it
    /// on a general formula is the over-narrow-header defect this whole module
    /// exists to close, so every shape the recognizer does not understand —
    /// every `Add`, every `Mul`, every `select`, every compound operand, every
    /// non-numeral bound — charges the bit.
    ///
    /// ONE BIT FOR BOTH SORTS. See the module header: SMT-LIB names no logic
    /// that is difference-restricted over `Int` and general over `Real`, so a
    /// second bit would double the powerset and name nothing new.
    pub const WIDE_ARITH: Self = Self(1 << 9);
    /// An `(Array _ _)` sort appears whose index and element sorts are NOT one
    /// of the two shapes the array-bearing [S1] declarations restrict
    /// themselves to — i.e. the query needs a logic whose declaration admits an
    /// ARBITRARY array sort, not one of the `*ALIA`/`*ABV` names.
    ///
    /// WRITTEN FROM THE DECLARATIONS. `QF_AUFLIA` [S1]: "all array terms have
    /// sort `(Array Int Int)`". `QF_ABV` [S1]: "all array terms have sort of
    /// the form `(Array (_ BitVec i) (_ BitVec j))` for some `i, j > 0`".
    /// `QF_AX` [S1]: "Closed quantifier-free formulas built over an arbitrary
    /// expansion of the ArraysEx signature with free sort and constant
    /// symbols" — no restriction. `AUFNIRA` [S1]: "Closed formulas built over
    /// arbitrary expansions of the Reals_Ints and ArraysEx signatures with
    /// free sort and function symbols" — no restriction on array sorts. So a
    /// `(Array Bool Bool)`, a `(Array Int Bool)`, a `(Array Int (Array Int
    /// Int))`, a mixed `(Array Int (_ BitVec 8))` or a zero-width bitvector
    /// array is admitted by NO row spelled `*ALIA`/`*ABV*`, and
    /// [`sort_theories`] charges this bit for exactly those shapes. WHICH wider
    /// row admits one is settled, as for the plain bit, by the base-sort bits
    /// the same sort also charges: over free sorts only (`Bool`), `QF_AX`;
    /// with `Int`/`Real` indices or elements, `AUFNIRA` (`QF_AX` admits no
    /// `Int` sort); a mixed `Int`/`BitVec` array, only `ALL` (`AUFNIRA` admits
    /// no `BitVec` sort). A zero-width `(_ BitVec 0)` is not a legal SMT-LIB
    /// sort at all; charging it here sends it to `ALL`, the fail-closed answer,
    /// instead of a restricted `*ABV*` row.
    ///
    /// THE BIT IS SPELLED FOR THE LARGER FRAGMENT, exactly as [`WIDE_ARITH`]
    /// is and for the same reason: every bit of this record is a DEMAND
    /// (`required ⊆ admits`), never a restriction, so `{ARRAYS}` ⊂ `{ARRAYS,
    /// WIDE_ARRAY}` and a union is wide as soon as either side is. A plain
    /// `ARRAYS` row admits the two RESTRICTED shapes; which of the two it
    /// admits is settled by its base-sort bits, since an `(Array Int Int)`
    /// also charges `INTS` and an `(Array (_ BitVec i) (_ BitVec j))` also
    /// charges `BITVECTORS`.
    ///
    /// WHAT IT COSTS, deliberately: a row with NO [S1] declaration to cite —
    /// `QF_ABVFP`, `QF_AUFBVLIA`, `QF_ABVFPLRA` and their relatives, all [S2]
    /// or [S3] only — keeps plain `ARRAYS` and so no longer names an array
    /// mixing its base sorts (`(Array (_ BitVec 32) (_ FloatingPoint 8 24))`
    /// heads `ALL` now). That is precision lost in the SOUND direction; a row
    /// gets this bit only with its own declaration quoted.
    pub const WIDE_ARRAY: Self = Self(1 << 10);

    /// Every dimension: what `ALL` admits.
    ///
    /// Derived from [`Theories::BIT_COUNT`] rather than written as `u16::MAX`,
    /// so adding a twelfth bit cannot leave `ALL` admitting less than the
    /// powerset the tests enumerate — a shape that would keep
    /// `the_table_is_well_formed` green while ADMISSIBILITY failed.
    pub const EVERYTHING: Self = Self((1 << Self::BIT_COUNT) - 1);

    /// The BASE SORT theories — the dimensions that decide which SMT-LIB logic
    /// FAMILY a name belongs to, as opposed to the MODIFIERS (`QUANTIFIERS`,
    /// `ARRAYS`, `UF`, `NONLINEAR`) that a family name carries as a prefix or
    /// an infix letter.
    ///
    /// The distinction is not cosmetic: SMT-LIB names a logic for a family
    /// (`LIA`, `BV`, `FP`, …) and decorates it with modifiers (`QF_`, `A`,
    /// `UF`, the `N`-for-`L` swap), and names ALMOST NOTHING for a modifier
    /// alone. The exceptions are real and are both in the table: `QF_AX` is
    /// "arrays and nothing else" and `UF` is "quantifiers and uninterpreted
    /// functions and nothing else" [S1, S2]. There is still no name for
    /// "nonlinear and nothing else" — `N` replaces the `L` of an arithmetic
    /// family that has to be named anyway — nor for "quantifiers alone".
    ///
    /// This mask is therefore a SUB-characterization of where selection fails
    /// to be monotone, not the characterization: the sets that violate are the
    /// ones NO ROW NAMES EXACTLY ([`is_named_exactly`]), which since the
    /// invented `LIRA`/`UFLIRA`/`QF_UFLIRA` rows came out includes three sets
    /// that DO name a base sort theory. See the module header and
    /// `monotonicity_fails_only_from_sets_no_row_names_exactly`.
    ///
    /// `NONLINEAR`, `WIDE_ARITH` and `WIDE_ARRAY` are deliberately NOT in this
    /// mask. The first two are qualifiers on an arithmetic family, not sorts:
    /// nothing is `NONLINEAR`-sorted or `WIDE_ARITH`-sorted, and a set carrying
    /// either with no `INTS`/`REALS` is unreachable from a formula (see
    /// [`node_theories`] and [`wide_arithmetic_theories`]) but still has to
    /// select something, which is exactly the modifier-only situation. The
    /// third is a qualifier on `ARRAYS` in the same way.
    pub const BASE_SORTS: Self = Self(
        Self::BITVECTORS.0 | Self::INTS.0 | Self::REALS.0 | Self::FLOATS.0 | Self::DATATYPES.0,
    );

    /// The number of distinct dimensions, i.e. `2^BIT_COUNT` feature sets.
    pub const BIT_COUNT: u32 = 11;

    /// The union (join) of two feature sets.
    #[must_use]
    pub const fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    /// Add `other`'s dimensions to `self`.
    pub fn insert(&mut self, other: Self) {
        self.0 |= other.0;
    }

    /// The union (join) of a whole sequence of feature sets.
    ///
    /// THE GROUP/BATCH ENTRY POINT. Every caller that writes ONE
    /// `(set-logic …)` line over SEVERAL formulas folds their records through
    /// here and calls [`select_logic_name`] ONCE on the result; ADMISSIBILITY
    /// of that single selection is then exactly the property the shared line
    /// needs (see the module header). Selecting per member and combining the
    /// NAMES afterwards would need monotonicity, which this table does not
    /// have.
    #[must_use]
    pub fn union_all(sets: impl IntoIterator<Item = Self>) -> Self {
        sets.into_iter().fold(Self::NONE, Self::union)
    }

    /// True iff this set names no BASE SORT theory — it is built from
    /// `QUANTIFIERS`/`ARRAYS`/`UF`/`NONLINEAR`/`WIDE_ARITH`/`WIDE_ARRAY` alone
    /// (`Theories::NONE` included), so there are `2^6 = 64` of them.
    ///
    /// Most of these sets are where the selection fails to be monotone, but
    /// they are no longer the whole story: see [`is_named_exactly`],
    /// [`Theories::BASE_SORTS`] and the module header.
    #[must_use]
    pub const fn is_modifier_only(self) -> bool {
        self.0 & Self::BASE_SORTS.0 == 0
    }

    /// True iff every dimension of `other` is present in `self`.
    #[must_use]
    pub const fn contains(self, other: Self) -> bool {
        self.0 & other.0 == other.0
    }

    /// True iff `self` is a subset of `other` — i.e. `other` admits `self`.
    #[must_use]
    pub const fn is_subset_of(self, other: Self) -> bool {
        self.0 & !other.0 == 0
    }

    /// True iff no dimension is present.
    #[must_use]
    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }

    /// How many dimensions are present. The table's ordering key.
    #[must_use]
    pub const fn len(self) -> u32 {
        self.0.count_ones()
    }

    /// The raw bits, so a test can enumerate the powerset. Always within
    /// [`Theories::EVERYTHING`].
    #[must_use]
    pub const fn bits(self) -> u16 {
        self.0
    }

    /// A feature set from raw bits, so a test can enumerate the powerset.
    ///
    /// FAIL-CLOSED ON UNKNOWN BITS. The backing integer is a `u16` and only
    /// [`Theories::BIT_COUNT`] of its bits name a dimension. A word carrying a
    /// bit above them is a record this revision cannot read — a dimension a
    /// newer writer knew and this reader does not — and the only name that
    /// provably admits a dimension nobody can name is the top. So such a word
    /// becomes [`Theories::EVERYTHING`], which keeps every KNOWN requirement it
    /// carried (`EVERYTHING` is a superset of all of them) AND forces `ALL`.
    /// Masking the unknown bits off instead would silently DROP a demand, which
    /// is the over-narrow direction this module exists to close; letting them
    /// through would build a set `ALL` does not admit and break ADMISSIBILITY
    /// for a value no enumeration covers. Either way the result is inside the
    /// powerset the tests enumerate, and the function stays total.
    /// `unknown_raw_feature_bits_force_all_without_dropping_known_requirements`
    /// pins this over every `u16`.
    #[must_use]
    pub const fn from_bits(bits: u16) -> Self {
        if bits & !Self::EVERYTHING.0 != 0 { Self::EVERYTHING } else { Self(bits) }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// 2. THE ADMISSIBILITY TABLE
// ─────────────────────────────────────────────────────────────────────────────

/// One logic NAME and the theories it admits.
#[derive(Debug, Clone, Copy)]
pub struct LogicRow {
    /// The SMT-LIB logic name written into `(set-logic …)`.
    pub name: &'static str,
    /// What that name admits.
    pub admits: Theories,
}

const fn row(name: &'static str, admits: Theories) -> LogicRow {
    LogicRow { name, admits }
}

/// THE ADMISSIBILITY TABLE — the single source for both the selector
/// ([`select_logic_name`]) and the transcript self-consistency checker
/// (trust-router's `smt2_self_consistency_tests::admissibility`), so a row can
/// never be right in one and wrong in the other.
///
/// Each row is written out rather than derived from the name's spelling (the
/// `A` in `AUFLIA` means "arrays" and the `A` in `LIA` means "arithmetic": a
/// spelling-derived rule is how a table like this gets quietly wrong).
///
/// PROVENANCE IS PART OF EACH ROW'S CORRECTNESS. The module header's sources
/// are `[S1]` the SMT-LIB standard's logic declarations, `[S2]` the SMT-LIB
/// benchmark library release, which ships one archive per logic, and `[S3]` the
/// SMT-COMP division lists drawn from that library. **Every name below except
/// two is in [S2], the current release**, so the notes that follow cite only
/// the exceptions and the names under discussion rather than repeating a tag
/// per row. The two exceptions are:
///
/// * `UFNRA` — [S3] only (an SMT-COMP division 2020–2023). It is a real
///   SMT-LIB logic name; its benchmarks are simply not a directory of the
///   current release.
/// * `ALL` — not an SMT-LIB logic at all. It is the universal solver-accepted
///   top (cvc5, z3, ay), and is documented as the top below.
///
/// Three names that were here are NOT attested by any of the three and are
/// gone; see the REMOVED note.
///
/// The `WA` column is [`Theories::WIDE_ARITH`] — "admits arithmetic atoms that
/// are not difference-shaped". It is `yes` on exactly the rows whose family
/// carries the full `LIA`/`LRA` atom grammar, and `no` on `QF_IDL`/`QF_RDL`,
/// which is the whole point of the dimension. A row with no `Int`/`Real` column
/// carries `no`, for the same reason it carries `no` under `NL`: the qualifier
/// belongs to an arithmetic family, and a set carrying it without a base
/// arithmetic sort is unreachable from a formula.
///
/// The eleventh column, [`Theories::WIDE_ARRAY`] — "admits an array sort other
/// than `(Array Int Int)` or a positive-width `(Array (_ BitVec i)
/// (_ BitVec j))`" — is NOT drawn: it is `yes` on exactly THREE rows, `QF_AX`,
/// `AUFNIRA` and `ALL`, the ones whose [S1] declarations place no restriction
/// on the array sort (quoted on the bit and on those two rows), and `no` on
/// every other row, including every `A`-spelled row that has only an [S2]/[S3]
/// attestation and therefore no declaration to cite. `the_table_is_well_formed`
/// pins the family at two (`ALL` excluded).
///
/// | logic       | quant | array | BV  | Int | Real | FP  | UF  | DT  | NL  | WA  |
/// |-------------|-------|-------|-----|-----|------|-----|-----|-----|-----|-----|
/// | QF_UF       |   no  |   no  |  no |  no |  no  |  no | yes |  no |  no |  no |
/// | QF_BV       |   no  |   no  | yes |  no |  no  |  no |  no |  no |  no |  no |
/// | QF_FP       |   no  |   no  |  no |  no |  no  | yes |  no |  no |  no |  no |
/// | QF_AX       |   no  |  yes  |  no |  no |  no  |  no |  no |  no |  no |  no |
/// | QF_IDL      |   no  |   no  |  no | yes |  no  |  no |  no |  no |  no |  no |
/// | QF_RDL      |   no  |   no  |  no |  no | yes  |  no |  no |  no |  no |  no |
/// | QF_DT       |   no  |   no  |  no |  no |  no  |  no |  no | yes |  no |  no |
/// | QF_LIA      |   no  |   no  |  no | yes |  no  |  no |  no |  no |  no | yes |
/// | QF_LRA      |   no  |   no  |  no |  no | yes  |  no |  no |  no |  no | yes |
/// | BV          |  yes  |   no  | yes |  no |  no  |  no |  no |  no |  no |  no |
/// | QF_ABV      |   no  |  yes  | yes |  no |  no  |  no |  no |  no |  no |  no |
/// | QF_UFBV     |   no  |   no  | yes |  no |  no  |  no | yes |  no |  no |  no |
/// | UF          |  yes  |   no  |  no |  no |  no  |  no | yes |  no |  no |  no |
/// | QF_BVFP     |   no  |   no  | yes |  no |  no  | yes |  no |  no |  no |  no |
/// | QF_UFFP     |   no  |   no  |  no |  no |  no  | yes | yes |  no |  no |  no |
/// | FP          |  yes  |   no  |  no |  no |  no  | yes |  no |  no |  no |  no |
/// | QF_UFDT     |   no  |   no  |  no |  no |  no  |  no | yes | yes |  no |  no |
/// | LIA         |  yes  |   no  |  no | yes |  no  |  no |  no |  no |  no | yes |
/// | LRA         |  yes  |   no  |  no |  no | yes  |  no |  no |  no |  no | yes |
/// | QF_UFLIA    |   no  |   no  |  no | yes |  no  |  no | yes |  no |  no | yes |
/// | QF_UFLRA    |   no  |   no  |  no |  no | yes  |  no | yes |  no |  no | yes |
/// | QF_LIRA     |   no  |   no  |  no | yes | yes  |  no |  no |  no |  no | yes |
/// | QF_ALIA     |   no  |  yes  |  no | yes |  no  |  no |  no |  no |  no | yes |
/// | QF_NIA      |   no  |   no  |  no | yes |  no  |  no |  no |  no | yes | yes |
/// | QF_NRA      |   no  |   no  |  no |  no | yes  |  no |  no |  no | yes | yes |
/// | QF_FPLRA    |   no  |   no  |  no |  no | yes  | yes |  no |  no |  no | yes |
/// | ABV         |  yes  |  yes  | yes |  no |  no  |  no |  no |  no |  no |  no |
/// | UFBV        |  yes  |   no  | yes |  no |  no  |  no | yes |  no |  no |  no |
/// | QF_AUFBV    |   no  |  yes  | yes |  no |  no  |  no | yes |  no |  no |  no |
/// | BVFP        |  yes  |   no  | yes |  no |  no  | yes |  no |  no |  no |  no |
/// | QF_ABVFP    |   no  |  yes  | yes |  no |  no  | yes |  no |  no |  no |  no |
/// | UFDT        |  yes  |   no  |  no |  no |  no  |  no | yes | yes |  no |  no |
/// | QF_UFBVDT   |   no  |   no  | yes |  no |  no  |  no | yes | yes |  no |  no |
/// | ALIA        |  yes  |  yes  |  no | yes |  no  |  no |  no |  no |  no | yes |
/// | UFLIA       |  yes  |   no  |  no | yes |  no  |  no | yes |  no |  no | yes |
/// | UFLRA       |  yes  |   no  |  no |  no | yes  |  no | yes |  no |  no | yes |
/// | QF_AUFLIA   |   no  |  yes  |  no | yes |  no  |  no | yes |  no |  no | yes |
/// | NIA         |  yes  |   no  |  no | yes |  no  |  no |  no |  no | yes | yes |
/// | NRA         |  yes  |   no  |  no |  no | yes  |  no |  no |  no | yes | yes |
/// | QF_ANIA     |   no  |  yes  |  no | yes |  no  |  no |  no |  no | yes | yes |
/// | QF_UFNIA    |   no  |   no  |  no | yes |  no  |  no | yes |  no | yes | yes |
/// | QF_UFNRA    |   no  |   no  |  no |  no | yes  |  no | yes |  no | yes | yes |
/// | QF_NIRA     |   no  |   no  |  no | yes | yes  |  no |  no |  no | yes | yes |
/// | FPLRA       |  yes  |   no  |  no |  no | yes  | yes |  no |  no |  no | yes |
/// | AUFBV       |  yes  |  yes  | yes |  no |  no  |  no | yes |  no |  no |  no |
/// | ABVFP       |  yes  |  yes  | yes |  no |  no  | yes |  no |  no |  no |  no |
/// | UFBVFP      |  yes  |   no  | yes |  no |  no  | yes | yes |  no |  no |  no |
/// | QF_AUFBVFP  |   no  |  yes  | yes |  no |  no  | yes | yes |  no |  no |  no |
/// | UFBVDT      |  yes  |   no  | yes |  no |  no  |  no | yes | yes |  no |  no |
/// | QF_UFDTLIA  |   no  |   no  |  no | yes |  no  |  no | yes | yes |  no | yes |
/// | QF_UFBVLIA  |   no  |   no  | yes | yes |  no  |  no | yes |  no |  no | yes |
/// | AUFLIRA     |  yes  |   no  |  no | yes | yes  |  no | yes |  no |  no | yes |
/// | AUFLIA      |  yes  |  yes  |  no | yes |  no  |  no | yes |  no |  no | yes |
/// | UFNIA       |  yes  |   no  |  no | yes |  no  |  no | yes |  no | yes | yes |
/// | UFNRA       |  yes  |   no  |  no |  no | yes  |  no | yes |  no | yes | yes |
/// | QF_AUFNIA   |   no  |  yes  |  no | yes |  no  |  no | yes |  no | yes | yes |
/// | ANIA        |  yes  |  yes  |  no | yes |  no  |  no |  no |  no | yes | yes |
/// | AUFBVFP     |  yes  |  yes  | yes |  no |  no  | yes | yes |  no |  no |  no |
/// | QF_UFDTLIRA |   no  |   no  |  no | yes | yes  |  no | yes | yes |  no | yes |
/// | QF_UFDTNIA  |   no  |   no  |  no | yes |  no  |  no | yes | yes | yes | yes |
/// | UFDTLIA     |  yes  |   no  |  no | yes |  no  |  no | yes | yes |  no | yes |
/// | QF_AUFBVLIA |   no  |  yes  | yes | yes |  no  |  no | yes |  no |  no | yes |
/// | AUFNIA      |  yes  |  yes  |  no | yes |  no  |  no | yes |  no | yes | yes |
/// | UFNIRA      |  yes  |   no  |  no | yes | yes  |  no | yes |  no | yes | yes |
/// | UFDTLIRA    |  yes  |   no  |  no | yes | yes  |  no | yes | yes |  no | yes |
/// | UFDTNIA     |  yes  |   no  |  no | yes |  no  |  no | yes | yes | yes | yes |
/// | AUFNIRA     |  yes  |  yes  |  no | yes | yes  |  no | yes |  no | yes | yes |
/// | UFDTNIRA    |  yes  |   no  |  no | yes | yes  |  no | yes | yes | yes | yes |
/// | ALL         |  yes  |  yes  | yes | yes | yes  | yes | yes | yes | yes | yes |
///
/// **EVERY ROW IS THE HONEST SMT-LIB SIGNATURE.** In particular `QF_UF` admits
/// uninterpreted functions, which is what the name means, and the BV and Real
/// families carry their modifier spellings (`BV`, `QF_ABV`, `QF_UFBV`, `ABV`,
/// `UFBV`, `QF_AUFBV`, `AUFBV`, `LRA`, `QF_UFLRA`) instead of collapsing to
/// `ALL`. An earlier revision of this table UNDER-stated `QF_UF` as admitting
/// nothing and dropped those nine names, because a table that is FULLY MONOTONE
/// cannot contain them (see the module header): `{Arrays} ⊆ {Arrays, Ints}` and
/// `{Arrays} ⊆ {Arrays, BitVectors}` force `admits(select({Arrays}))` inside
/// `QF_ALIA ∩ QF_ABV = {Arrays}` — which, as it happens, SMT-LIB DOES spell,
/// `QF_AX` [S1, S2], now a row of its own. Under-stating a row is SOUND — it
/// can only push the selector to a wider name — but it is not free: it sent
/// every modifier-carrying bitvector query to `ALL`, changing which ay pipeline
/// the query takes, and 230 of the 256 feature sets of the then-8-dimensional
/// powerset selected `ALL`. With the honest rows restored that figure was 223,
/// and a quantified/array/UF bitvector query heads the BV logic that names its
/// own theory. (The powerset is 2048 since the ARRAY-SHAPE bit, 1024 from the
/// LINEAR-FORM bit before it;
/// `the_share_of_the_powerset_that_takes_all_is_pinned` carries the current
/// split and the fractions, which are the comparable figures.) Monotonicity is
/// what was given up, and no consumer needs it — every group and batch consumer
/// selects once from the UNION of its members' features, which ADMISSIBILITY
/// alone covers.
///
/// **THE `N` FAMILY.** Eighteen rows carry `NONLINEAR`, and they are the same
/// arithmetic families as the `L` rows with SMT-LIB's `L`→`N` swap: `QF_NIA`,
/// `QF_NRA`, `NIA`, `NRA`, `QF_ANIA`, `QF_UFNIA`, `QF_UFNRA`, `QF_NIRA`,
/// `UFNIA`, `UFNRA`, `QF_AUFNIA`, `ANIA`, `AUFNIA`, `UFNIRA`, `AUFNIRA`, and
/// the three datatype ones `QF_UFDTNIA`, `UFDTNIA`, `UFDTNIRA` — every
/// one a name in the SMT-LIB logic set [S2; `UFNRA` S3, SMT-COMP 2020–2023],
/// written out here rather than derived from a spelling. Note that the swap is
/// ARITHMETIC-ONLY: there is no `QF_NBV` and no nonlinear floating-point name,
/// because `QF_BV` admits `bvmul` and `QF_FP` admits `fp.mul` unconditionally.
/// [`Theories::NONLINEAR`] is therefore never set by a bitvector or
/// floating-point node.
///
/// **THE FLOATING-POINT FAMILY.** Sixteen rows carry `FLOATS`. `QF_FP` is the
/// pure fragment; `QF_UFFP`, `FP` add a modifier; and `QF_BVFP`, `BVFP`,
/// `QF_ABVFP`, `ABVFP`, `UFBVFP`, `QF_AUFBVFP`, `AUFBVFP` are the COMBINED
/// BV+FP fragment SMT-LIB puts the `to_fp`-from-bitvector form in — the exact
/// fragment [`node_theories`]'s `FpConst` arm names, and which this table could
/// not express until these rows landed, so every `FpConst`-bearing transcript
/// was headed `ALL`. `QF_FPLRA`/`FPLRA` are FP with linear REAL arithmetic, and
/// `QF_BVFPLRA`/`BVFPLRA`/`QF_ABVFPLRA`/`ABVFPLRA` (Lever C, closed
/// 2026-09-18) are the same with bitvectors — the ONLY SMT-LIB spelling for any
/// mix of BITVECTORS with REALS, which is why `{BitVectors, Reals}` had no name
/// until they landed. All sixteen are in the library release [S2].
///
/// NINE OF THE SIXTEEN ARE NAMES THE NATIVE IN-PROCESS LANE CANNOT PARSE
/// (`QF_UFFP`, `FP`, `BVFP`, `FPLRA`, `ABVFP`, `UFBVFP`, `QF_AUFBVFP`,
/// `AUFBVFP`, and the four `*BVFPLRA` ones — twelve, counting them all). That
/// is a fact about that lane and NOT about these rows: it re-selects from the
/// sublattice it can parse
/// (`trust_router::in_process_ay_backend::native_lane_logic`). When the FP rows
/// first landed the guard did not exist, and each of those names silently cost
/// the whole verdict for the sets that selected it — see the criterion note
/// below, which is where that defect is recorded.
///
/// **THE DIFFERENCE FAMILY.** Two rows name an arithmetic sort and do NOT carry
/// [`Theories::WIDE_ARITH`] — `QF_IDL` and `QF_RDL` [S1, S2, S3] — and they are
/// the only rows whose set is a STRICT SUBFRAGMENT of another row's base
/// theory. Their admissibility is written from the [S1] declarations verbatim,
/// not from the informal "difference logic" gloss, and the two declarations are
/// NOT the same shape:
///
/// * `QF_IDL`: atoms are `q`, `(op (- x y) n)`, `(op (- x y) (- n))` or
///   `(op x y)`, where `q` is Bool, `op ∈ {<, <=, >, >=, =, distinct}`, `x`/`y`
///   are free constant symbols of sort `Int` and `n` is a NUMERAL.
/// * `QF_RDL`: atoms are `p`, `(op (- x y) c)`, `(op x y)` and the scaled form
///   `(op (- (+ x … x) (+ y … y)) c)` with `n > 1` occurrences, where `c` is
///   `m` or `(- m)` for a numeral `m` and `x`/`y` are free constant symbols of
///   sort `Real`.
///
/// NEITHER declaration lists `(op x n)`. A bare `x > 3` is therefore NOT an
/// atom of either fragment, whatever the textbook gloss says, and
/// [`is_difference_atom`] does not recognize it — which is why an ordinary
/// bounds check still heads `QF_LIA`. That is the conservative direction:
/// recognizing FEWER shapes can only set [`Theories::WIDE_ARITH`] more often,
/// and setting it more often can only WIDEN the header.
///
/// WHY THIS CLASS NEEDED A DIMENSION AND NOT A ROW, in one measured sentence:
/// ay maps `QF_IDL -> QfLia` and `QF_RDL -> QfLra`
/// (`ay-dpll/src/logic_detection/parse.rs`) and enforces NO fragment
/// restriction, so a header narrower than its content is decided CORRECTLY
/// in-house and would fail only at an external replayer — measured 2026-09-18
/// on four out-of-fragment queries, every one answered correctly, three of them
/// with a strict-verified proof, under `(set-logic QF_IDL)`/`(set-logic
/// QF_RDL)`. A row alone would have been SILENT IN-HOUSE, which is the worst
/// shape a defect in this module can take.
///
/// **THE DATATYPE FAMILY — LEVER A, RE-POINTED 2026-09-18 ON MEASUREMENT.**
/// Twelve rows carry `DATATYPES`: `QF_DT`, `QF_UFDT`, `UFDT`, `QF_UFBVDT`,
/// `UFBVDT`, `QF_UFDTLIA`, `QF_UFDTLIRA`, `QF_UFDTNIA`, `UFDTLIA`, `UFDTLIRA`,
/// `UFDTNIA`, `UFDTNIRA` [S2]. Until this revision every datatype-bearing
/// feature set took `ALL`, on a recorded fear that a `DT` row "would silently
/// re-point" `in_process_ay_backend`'s datatype programs. That fear is MEASURED
/// FALSE, and the measurement is what moved the lever:
///
/// * ay's in-process lane carries its OWN logic-name gate,
///   `ay_bindings::execute_direct::logic::parse_logic`, which maps **every name
///   whose spelling contains `DT`** to `Logic::All` BEFORE any routing happens.
///   A `DT` row therefore cannot change which pipeline ay takes; it can only
///   change the text of the header. The re-point is neutral BY CONSTRUCTION,
///   not merely by sample.
/// * It is also neutral by sample: 8 datatype queries × 19 candidate `DT`
///   names, every one byte-identical to the `ALL` result — same verdict, same
///   artifact, including the two queries `ALL` itself answers `unknown`.
/// * The live consumer keeps passing. `logic == "ALL" || logic.contains("DT")`
///   holds for every name added here, and `AYProgram::upgrade_logic_for_
///   datatypes` leaves a `DT`-spelled logic alone instead of widening it.
///
/// **THE `A`-LEADING DATATYPE NAMES ARE STILL ABSENT, AND THE REASON IS
/// `AUFLIRA`'s.** `AUFDTLIA`, `AUFDTLIRA`, `AUFDTNIRA`, `AUFBVDTLIA`,
/// `AUFBVDTNIA`, `AUFBVDTNIRA` [S2] are real names and were measured accepted,
/// but no [S1] declaration exists for ANY of them — the standard's logic
/// declarations stop at the SMT-LIB 1.2 set and know no `DT` logic at all — so
/// there is nothing to cite for what their leading `A` admits. `AUFLIRA` is the
/// standing proof that a leading `A` may name a RESTRICTED array fragment
/// (`(Array Int Real)` only), and a row claiming unconditional `ARRAYS` on an
/// uncitable `A` is exactly the OVER-statement this table must never make.
/// Claiming everything EXCEPT `ARRAYS` is not an option either: that set is
/// already named by the row's own `UF*` sibling (`AUFDTLIA` minus arrays IS
/// `UFDTLIA`), and two rows admitting one set make the name an accident of
/// table order. So array-bearing datatype sets keep taking `ALL`, and closing
/// that needs an [S1]-grade citation, not a table edit.
///
/// **WHAT IS STILL DELIBERATELY ABSENT, AND WHY.** `ALL` is the answer wherever
/// this table declines to name a set. Each class below was AUDITED against the
/// SMT-LIB logic set, so these are REJECTIONS WITH REASONS, not gaps — and
/// where a class is NOT a rejection, the bullet says so in those words rather
/// than sitting in this list looking like one.
///
/// **THE CRITERION, STATED ONCE (revised 2026-09-18).** A name belongs in this
/// table iff BOTH of:
///
///   (C1) it is ATTESTED AS A CURRENT LOGIC by [S1], [S2] or [S3] — an invented
///        spelling is a header no replayer can check. [S3] counts because the
///        division lists are drawn from the library's own logic directories,
///        with ONE exclusion, and it is the exclusion `AX` falls under: a name
///        whose only attestation is [S3] AND which has been MEASURED ABSENT
///        from the current [S2] release is a RETIRED spelling, not a current
///        one. Nothing else in this note is in that position; and
///   (C2) this record can say what it admits WITHOUT OVER-STATING against the
///        declaration cited for it — which is why `AUFLIRA` does not claim
///        `ARRAYS` (its declaration restricts the array sort), why the
///        `A`-leading `*DT*` names are absent (no declaration exists to cite),
///        and why `QF_UFIDL`/`UFIDL` are absent (their declaration restricts
///        TERMS in a way `{UF, Ints}` does not record).
///
/// **WHAT IS NOT A CRITERION, AND THE ROUND THAT GOT IT WRONG.** Whether ONE
/// CONSUMER'S PARSER accepts the spelling is NOT a property of the name, and it
/// was wrong to write it into this table. It was written in anyway: six real
/// names were refused on the ground that
/// `ay_bindings::execute_direct::logic::parse_logic` — the name gate of the
/// NATIVE in-process lane — answers `ExecuteError::UnsupportedLogic` for them,
/// while TEN rows this table already carried (`QF_UFFP`, `FP`, `BVFP`,
/// `QF_ANIA`, `FPLRA`, `ABVFP`, `UFBVFP`, `QF_AUFBVFP`, `ANIA`, `AUFBVFP`) are
/// refused by that SAME parser and were kept. One criterion, two answers —
/// and the ten were the dangerous half, because the text lane and the native
/// lane read this table together and the native lane turned each of those ten
/// into `Unknown` with no verdict and no artifact.
///
/// THE FIX IS IN THE LANE, NOT IN THE TABLE.
/// `trust_router::in_process_ay_backend::native_lane_logic` selects the NATIVE
/// lane's `(set-logic …)` from the sublattice of rows that parser accepts, so
/// the native lane can never be handed a name it refuses, whatever this table
/// names. Measured 2026-09-18 at pin `first-party/ay` c4ade436: exactly those
/// ten of the (then) 69 rows were refused, 76 of the 1024 feature sets were
/// selecting one of them, and the guard is a NO-OP on every one of the other
/// 948 — on every feature set, that is, whose selected name that parser already
/// accepted, which is why it cannot move a verdict that exists today.
/// BOTH GAPS ARE NOW CLOSED UPSTREAM, and this paragraph is kept because the
/// reasoning is what a future narrowing will need. ay 9d2cda9c8 (2026-09-19)
/// fixed the header refusal — `parse_logic` consults an `SMT_LIB_LOGICS`
/// mapping after `Logic::from_str` fails, so all sixteen names now parse — and
/// the binder gap behind it: a natively built quantifier is now indexed for
/// alpha-sharing, so its retained source re-elaborates to the same `TermId`
/// (the soundness guard itself was not touched — it still demands one id).
/// RE-MEASURED at that pin: all ten names reach the solver under their precise
/// spelling, FOUR decide (`QF_UFFP`, `QF_ANIA`, `UFBVFP`, `QF_AUFBVFP` — up
/// from three, `UFBVFP` being the quantified one the binder fix restored), and
/// the remaining six stop on ay's own quantifier INCOMPLETENESS — honest
/// `unknown`s from inside the solver, not a header refusal and not a source
/// reconstruction abort. `native_lane_logic` is consequently a TOTAL NO-OP at
/// this pin, differing from `select_logic_name` on zero of the 1024 sets; it is
/// kept, and pinned as a no-op, so a future narrowing in ay fails a unit test
/// instead of silently costing a verdict. The parser is therefore retired as a
/// table criterion, the six names it refused are measured against (C1)/(C2)
/// like any others — all six PASS, and all six are now rows — and this note no
/// longer states a rule it does not apply.
///
/// * **`QF_ADT`.** Not attested by [S1], [S2] or [S3] — it is a solver-side
///   spelling, not a library logic, and the standard declarations know neither
///   it nor `QF_DT`'s `A` variant. `QF_DT` is the attested name for
///   quantifier-free datatypes and is the row that was added. Pinned as an
///   absence in `the_table_is_well_formed`, beside the three invented `*LIRA`
///   spellings, so a future edit has to argue with the citation.
/// * **BITVECTORS mixed with INTS or REALS — NO LONGER ABSENT. LEVER C IS
///   CLOSED, 2026-09-18.** `QF_UFBVLIA` and `QF_AUFBVLIA` [S3, SMT-COMP
///   divisions] came in when the lever was SPLIT; the other six —
///   `UFBVLIA` [S2], `QF_AUFBVNIA` [S3], and the four `*BVFPLRA` names
///   `QF_BVFPLRA`, `BVFPLRA`, `QF_ABVFPLRA`, `ABVFPLRA` [S2], which mix BV with
///   REALS through the FP family — were held out ONLY because the native lane's
///   parser refuses them, and that is not a criterion (see above). RE-DERIVED
///   AGAINST (C1)/(C2), one at a time, and all six pass with a sibling already
///   in the table on identical footing: `UFBVLIA` is `QF_UFBVLIA` quantified;
///   `QF_AUFBVNIA` is `QF_AUFBVLIA` nonlinear and carries the same [S3]
///   standing; `QF_BVFPLRA`/`BVFPLRA`/`QF_ABVFPLRA`/`ABVFPLRA` stand exactly as
///   `QF_FPLRA`, `FPLRA`, `QF_ABVFP` and `ABVFP` do, and the two `A`-leading
///   ones claim `ARRAYS` on the same [S2] declarations `QF_ABVFP`/`ABVFP`
///   already claim it on. So all six are rows.
///   WHAT THAT MOVED, measured over the whole 1024-set powerset: 53 feature
///   sets change name, 49 of them OFF `ALL` onto a real SMT-LIB name and 4 from
///   `AUFNIRA` onto a narrower `*BVFPLRA`. `{BitVectors, Reals}` in particular
///   gets its FIRST name, `QF_BVFPLRA` — its only SMT-LIB spellings are the
///   `*BVFPLRA` family — and `the_common_anchors_are_pinned` pins the move.
///   MEASURED SAFE ON BOTH CONSUMING LANES, because a row this table adds goes
///   out on two wires: the SUBPROCESS lane's external `ay` accepts all six —
///   re-probed 2026-09-18 against ay 0.13.0+build.8256, `; ignoring unsupported
///   logic` printed for the FABRICATED control only — and the NATIVE lane's
///   LINKED parser accepts all six as well, re-measured 2026-09-19 against
///   `first-party/ay` `9d2cda9c8727`.
///   WHAT THAT RE-MEASUREMENT CHANGED, recorded rather than quietly amended:
///   this clause used to read "the NATIVE lane cannot see any of the six …, so
///   its header is unchanged for all 1024 sets". That was true while
///   `ay_bindings::execute_direct::logic::parse_logic` refused all six. It no
///   longer does, so the six move the native header for exactly the SAME 53
///   feature sets they move the text one — the two lanes now agree on every
///   header, and `trust_router::in_process_ay_backend`'s
///   `the_guard_is_a_no_op_wherever_the_table_already_names_something_parseable`
///   pins both the 53 and the pairs.
///   THE REPLACED JUSTIFICATION, recorded so it is not re-derived: this bullet
///   once read "`QF_AUFBV` over an `Int` declaration is the measured
///   `unknown` + MODEL-UNCONFIRMED shape". Re-measured 2026-09-18 at the
///   current pin over five shapes, that is REFUTED: four of the five come back
///   DECIDED under `QF_AUFBV`, three with a strict-verified UNSAT artifact, and
///   the one `unknown` reproduces IDENTICALLY under `ALL` — it is a property of
///   ay's combined BV+LIA SAT lane, not of the header. The anchors survive; the
///   evidence under them changed.
/// * **`QF_UFIDL` and `UFIDL`** [S1, S2]. Both absent, and since the native
///   parser stopped being a criterion there is exactly ONE reason, which covers
///   both: their [S1] declaration is NOT "`QF_IDL` with uninterpreted
///   functions". It restricts TERMS, requiring that "for every term of the form
///   `(op t1 t2)` with `op` in `{+, -}`, at least one of `t1` and `t2` is a
///   numeral" — which the difference ATOM `(- x y)` does not satisfy. A row
///   admitting `{UF, Ints}` (resp. `{Quantifiers, UF, Ints}`) would therefore
///   over-state against its own declaration — a (C2) failure — so `{UF, Ints}`
///   keeps taking `QF_UFLIA`. THE STALE HALF, removed: this bullet used to
///   refuse `UFIDL` separately because the in-process lane ANSWERED
///   `unsupported logic: UFIDL`. It no longer does — measured 2026-09-19, the
///   linked parser accepts `UFIDL` — which is exactly why that was never a
///   reason that belonged here; (C2) refuses `UFIDL` on its own, unmoved.
///   [`Theories::WIDE_ARITH`] would support both rows the moment a citation
///   supports the semantics.
/// * **`ALRA`, `AUFLRA`, `QF_AUFLRA`, `QF_AUFLIRA` — THE ARRAY-AND-REAL GAP,
///   SETTLED 2026-09-19. All four FAIL (C1): NO SOURCE KNOWS ANY OF THEM.**
///   This is the class an earlier round left open as "could not attest", which
///   reads like a gap in the looking; it is not. All three sources were driven
///   for all four names and every answer is NEGATIVE:
///   * [S1] the standard's logic declarations
///     (<https://smt-lib.org/logics-all.shtml>) list 25 names and none of the
///     four is among them (`AUFLIRA`, `UFLRA`, `LRA`, `QF_UFLRA` and
///     `QF_AUFLIA` are — the neighbours, which is what makes the four look
///     plausible);
///   * [S2] the 2025 library release (<https://zenodo.org/records/15493090>)
///     ships 89 per-logic archives and none of the four has one (`AUFLIRA`,
///     `ALIA`, `QF_ALIA`, `QF_ABVFPLRA`, `ABVFPLRA` do);
///   * [S3] the SMT-COMP division lists name none of the four, in the 2023
///     file or the 2019 one.
///
///   THE TRAP THIS CLASS IS BUILT OUT OF, and the reason it is written out at
///   length rather than listed: ALL FOUR ARE ACCEPTED BY THE NATIVE LANE'S
///   PARSER. `trust_router::in_process_ay_backend::NATIVE_LANE_LOGIC_VOCABULARY`
///   carries `AUFLRA`, `ALRA`, `QF_AUFLRA` and `QF_AUFLIRA` as MEASURED
///   `parse_logic` acceptances. That is exactly the criterion this table
///   RETIRED (see "WHAT IS NOT A CRITERION" above) — and here it points the
///   other way from the one that got it wrong before: a consumer accepting a
///   spelling is no more evidence that it is a logic than a consumer refusing
///   one is evidence that it is not. A row added on that footing would put an
///   UNATTESTED name in a `(set-logic …)` line, which is the same defect class
///   as an over-narrow header: a replayer cannot check it.
///   AND THE CRITERION GOT WEAKER STILL ON 2026-09-19, which is worth knowing
///   before anyone reaches for it again: ay `9d2cda9c8727` widened
///   `parse_logic` until it accepts every one of this table's 75 rows and
///   refuses exactly `HORN` and a fabricated control. A test of "does ay parse
///   it" now separates almost nothing.
///
///   WHAT THE GAP COSTS, measured over the powerset rather than asserted.
///   28 of the 256 `{Arrays, Reals, …}` sets head `AUFNIRA` (cardinality 7):
///   exactly the ones carrying no `BITVECTORS`/`FLOATS`/`DATATYPES` (those go
///   to `ALL`) and at least one of `UF`/`INTS`/`NONLINEAR` (without one of the
///   three, `QF_ABVFPLRA`/`ABVFPLRA` — Lever C's rows — already admit them at
///   cardinality five and six). Of those 28, **20 are promised NONLINEARITY or
///   INTEGERS they do not use**, and `AUFNIRA` names exactly ONE of the 28
///   exactly. So an array-over-reals query with an uninterpreted function
///   heads a nonlinear-integer name, which is the complaint.
///
///   Over-stating in that direction is SOUND — a wider name admits strictly
///   more, so it cannot turn a SAT violation into UNSAT — and it costs
///   precision only. `the_array_and_real_gap_is_pinned_with_its_rejection`
///   pins the extent, the characterization and the four absences together, so
///   a future edit argues with the citations above rather than with nothing.
/// * **The STRING names** (`QF_S`, `QF_SLIA`, `QF_SNIA` [S2]). Real but
///   UNREACHABLE: [`crate::Sort`] has no string sort, so no feature set in this
///   powerset can require them.
/// * **`AX`** (quantified arrays alone, [S3] only). The (C1) exclusion, and the
///   only name under it: it is MEASURED ABSENT from the SMT-LIB library release
///   [S2], so its single [S3] attestation is of a retired spelling.
///   `{Quantifiers, Arrays}` therefore still takes `ABV`. Its quantifier-free
///   sibling `QF_AX` IS attested [S1, S2] and was added. (The [S3]-attested
///   names that ARE rows — `QF_UFBVLIA`, `QF_AUFBVLIA`, `QF_AUFBVNIA` — have
///   never been measured absent from [S2]; the day one is, this bullet is where
///   it goes.)
/// * **FLOATS mixed with INTS**, in any combination — and this one is NOT a
///   rejection, so it is labelled as what it is: an OPEN DECISION, deliberately
///   not taken here. SMT-LIB has no such name outside the `*FPDT*` family
///   (`QF_UFFPDTNIRA`, `UFFPDTNIRA`, `AUFFPDTNIRA`, `AUFBVFPDTNIRA` [S2]), all
///   of which pass (C1) and (C2) — they admit exactly what they say. What holds
///   them out is neither criterion but BLAST RADIUS: every name in the family
///   drags FLOATS, DATATYPES and NONLINEARITY in together, so adding one
///   re-points three dimensions at once to buy one, and that is a measurement
///   of its own. Until it is made, `{Floats, Ints}` takes `ALL` — the M1
///   defect's shape, still answered `ALL`, now for a stated reason rather than
///   for want of looking.
///
/// **THE TWO LANES AGREED ABOUT LOGIC NAMES AS OF 2026-09-19, AND NEITHER OF
/// THEM GOVERNS THIS TABLE.** Re-measured with both wires driven:
///
/// * the EXTERNAL `ay` binary (ay 0.13.0+build.8256), which is what the
///   SUBPROCESS lanes — `trust_router::incremental_ay` and
///   `smtlib_backend::generate_smtlib_script` — hand a `(set-logic …)` to,
///   accepts EVERY name in this table and every name this note refuses, and
///   prints `; ignoring unsupported logic` for a FABRICATED control only
///   (probed 2026-09-18);
/// * the LINKED library (`ay_bindings::execute_direct`), which is what the
///   NATIVE in-process lane takes, ALSO accepts every name in this table —
///   re-measured 2026-09-19 against `first-party/ay` `9d2cda9c8727`, all 75
///   rows, with `HORN` and a fabricated control as the two refusals.
///
/// THIS BULLET USED TO SAY THE LINKED LIBRARY REFUSED SIXTEEN OF THEM, and it
/// did: `QF_UFFP`, `FP`, `BVFP`, `QF_ANIA`, `FPLRA`, `ABVFP`, `UFBVFP`,
/// `QF_AUFBVFP`, `QF_BVFPLRA`, `ANIA`, `AUFBVFP`, `UFBVLIA`, `BVFPLRA`,
/// `QF_ABVFPLRA`, `QF_AUFBVNIA` and `ABVFPLRA` each answered
/// `ExecuteError::UnsupportedLogic`, byte-identical to the fabricated control,
/// and aborted the whole solve. ay `9d2cda9c8727` added an attested-name table
/// (`SMT_LIB_LOGICS`) that maps them to `Logic::All`, and all sixteen now reach
/// a verdict. The disagreement is recorded rather than deleted because it is
/// the reason the narrowing lives on the LANE and not in this table.
///
/// A future re-measure that probes only the CLI gets the wrong answer for the
/// native lane, and one that probes only the linked library gets the wrong
/// answer for the subprocess lane. DRIVE BOTH — the agreement above is a
/// measurement at one pin, not a property. What neither answer may do is
/// decide table membership: this table names what SMT-LIB attests (C1/C2), and
/// each lane narrows to what IT can parse —
/// `trust_router::in_process_ay_backend::native_lane_logic` for the native one
/// (a NO-OP at this pin, kept so a narrowing in ay fails a test instead of
/// losing a verdict), nothing for the subprocess one, because nothing is
/// needed.
///
/// **REMOVED, BECAUSE THEY ARE NOT SMT-LIB NAMES.** Three rows carried mixed
/// linear-arithmetic spellings that no source knows: `LIRA`
/// (`{Quantifiers, Ints, Reals}`), `UFLIRA` (`{Quantifiers, UF, Ints, Reals}`)
/// and `QF_UFLIRA` (`{UF, Ints, Reals}`). None appears in [S1], [S2] or [S3];
/// Yices' logic table names `QF_LIRA` and `QF_UFLIRA` explicitly among "logic
/// names that are NOT officially part of SMT-LIB"
/// (<https://yices.csl.sri.com/doc/smt-logics.html>) — and of those two only
/// `QF_LIRA` has since become a library logic [S2, S3], which is why `QF_LIRA`
/// STAYS and `QF_UFLIRA` goes. They were plausible by the naming schema and
/// wrong in fact, and emitting one is a defect: a replayer cannot check a
/// header that names no logic. All three are replaced by the LEAST REAL NAME
/// admitting their sets, which is the same one for all three — `AUFLIRA` [S1,
/// S2], the SMT-LIB name for quantified mixed linear arithmetic with arrays and
/// uninterpreted functions. That is a WIDENING in every case (`AUFLIRA` also
/// promises arrays and UF, and for `QF_UFLIRA` it also drops the
/// quantifier-free restriction), so it only ever admits more. `QF_UFDTLIRA` and
/// `QF_UFNIRA` were considered as narrower replacements for `QF_UFLIRA` and
/// rejected: the first drags DATATYPES in, and the second is attested only by
/// Yices' 2015 snapshot of smt-lib.org, not by [S1], [S2] or [S3].
/// `QF_UFDTLIRA` IS a row since Lever A was re-pointed, and it is NOT a
/// narrower replacement even now — it admits `{UF, Ints, Reals}` at the same
/// cardinality as `AUFLIRA`, so the two TIE and table order settles it in
/// `AUFLIRA`'s favour, which is why `AUFLIRA` leads the five-dimension group.
///
/// Widening to `ALL` only ever ADMITS MORE; it never changes a formula's
/// models, so it cannot turn a SAT violation into UNSAT (no false proof).
///
/// Ordered by increasing `admits.len()`. Unlike the previous revision, the
/// order is now LOAD-BEARING for DETERMINISM, not merely an aid: several rows
/// can be minimal for the same feature set (seven rows admit `∅`), so
/// [`select_logic_name`] takes the FIRST minimal-cardinality row in this order
/// and `selection_is_the_first_minimal_row_in_table_order` pins that rule over
/// the whole powerset. Two placements are deliberate: `QF_UF` leads the
/// one-dimension group, so a Core-only query heads the name every tool already
/// writes for it; and `AUFLIRA` leads the five-dimension group, so the mixed
/// linear-arithmetic sets head a LINEAR, DATATYPE-FREE name rather than tying
/// with `QF_UFDTLIRA`, which also promises datatypes.
pub const LOGIC_LATTICE: &[LogicRow] = &[
    // — one dimension —
    //
    // `QF_UF` leads: six other rows also admit `∅`, and a Core-only query must
    // head the name every tool already writes for it.
    row("QF_UF", Theories::UF),
    row("QF_BV", Theories::BITVECTORS),
    row("QF_FP", Theories::FLOATS),
    // The DIFFERENCE rows. `INTS`/`REALS` WITHOUT `WIDE_ARITH` is exactly "an
    // integer (resp. real) query every one of whose atoms is difference-shaped
    // as the [S1] declaration writes it", which is what these names admit; the
    // general fragment is one bit up, at `QF_LIA`/`QF_LRA`. See the DIFFERENCE
    // FAMILY note above for the two declarations, which are not the same shape.
    row("QF_IDL", Theories::INTS),
    row("QF_RDL", Theories::REALS),
    // Lever A, re-pointed: quantifier-free datatypes and nothing else.
    row("QF_DT", Theories::DATATYPES),
    // — two dimensions —
    //
    // `QF_AX` LEADS THIS GROUP, and the placement is load-bearing: `QF_ABV`
    // also admits `{Arrays}` at cardinality two, and the tie must go to the
    // name that promises no base sort. `QF_AX` carries `WIDE_ARRAY` because
    // its [S1] declaration restricts the array sort NOT AT ALL ("Closed
    // quantifier-free formulas built over an arbitrary expansion of the
    // ArraysEx signature with free sort and constant symbols"), so it is the
    // quantifier-free name for a `(Array Bool Bool)` or a nested array — the
    // shapes `QF_ALIA`/`QF_ABV` are declared NOT to admit. See
    // [`Theories::WIDE_ARRAY`].
    row("QF_AX", Theories::ARRAYS.union(Theories::WIDE_ARRAY)),
    row("QF_LIA", Theories::INTS.union(Theories::WIDE_ARITH)),
    row("QF_LRA", Theories::REALS.union(Theories::WIDE_ARITH)),
    row("BV", Theories::QUANTIFIERS.union(Theories::BITVECTORS)),
    row("QF_ABV", Theories::ARRAYS.union(Theories::BITVECTORS)),
    row("QF_UFBV", Theories::UF.union(Theories::BITVECTORS)),
    row("UF", Theories::QUANTIFIERS.union(Theories::UF)),
    row("QF_BVFP", Theories::BITVECTORS.union(Theories::FLOATS)),
    row("QF_UFFP", Theories::UF.union(Theories::FLOATS)),
    row("FP", Theories::QUANTIFIERS.union(Theories::FLOATS)),
    row("QF_UFDT", Theories::UF.union(Theories::DATATYPES)),
    // — three dimensions —
    row("LIA", Theories::QUANTIFIERS.union(Theories::INTS).union(Theories::WIDE_ARITH)),
    row("LRA", Theories::QUANTIFIERS.union(Theories::REALS).union(Theories::WIDE_ARITH)),
    row("QF_UFLIA", Theories::UF.union(Theories::INTS).union(Theories::WIDE_ARITH)),
    row("QF_UFLRA", Theories::UF.union(Theories::REALS).union(Theories::WIDE_ARITH)),
    row("QF_LIRA", Theories::INTS.union(Theories::REALS).union(Theories::WIDE_ARITH)),
    row("QF_ALIA", Theories::ARRAYS.union(Theories::INTS).union(Theories::WIDE_ARITH)),
    row("QF_NIA", Theories::NONLINEAR.union(Theories::INTS).union(Theories::WIDE_ARITH)),
    row("QF_NRA", Theories::NONLINEAR.union(Theories::REALS).union(Theories::WIDE_ARITH)),
    row("QF_FPLRA", Theories::REALS.union(Theories::FLOATS).union(Theories::WIDE_ARITH)),
    row("ABV", Theories::QUANTIFIERS.union(Theories::ARRAYS).union(Theories::BITVECTORS)),
    row("UFBV", Theories::QUANTIFIERS.union(Theories::UF).union(Theories::BITVECTORS)),
    row("QF_AUFBV", Theories::ARRAYS.union(Theories::UF).union(Theories::BITVECTORS)),
    row("BVFP", Theories::QUANTIFIERS.union(Theories::BITVECTORS).union(Theories::FLOATS)),
    row("QF_ABVFP", Theories::ARRAYS.union(Theories::BITVECTORS).union(Theories::FLOATS)),
    row("UFDT", Theories::QUANTIFIERS.union(Theories::UF).union(Theories::DATATYPES)),
    row("QF_UFBVDT", Theories::UF.union(Theories::BITVECTORS).union(Theories::DATATYPES)),
    // — four dimensions —
    row(
        "ALIA",
        Theories::QUANTIFIERS
            .union(Theories::ARRAYS)
            .union(Theories::INTS)
            .union(Theories::WIDE_ARITH),
    ),
    row(
        "UFLIA",
        Theories::QUANTIFIERS.union(Theories::UF).union(Theories::INTS).union(Theories::WIDE_ARITH),
    ),
    row(
        "UFLRA",
        Theories::QUANTIFIERS
            .union(Theories::UF)
            .union(Theories::REALS)
            .union(Theories::WIDE_ARITH),
    ),
    row(
        "QF_AUFLIA",
        Theories::ARRAYS.union(Theories::UF).union(Theories::INTS).union(Theories::WIDE_ARITH),
    ),
    row(
        "NIA",
        Theories::NONLINEAR
            .union(Theories::QUANTIFIERS)
            .union(Theories::INTS)
            .union(Theories::WIDE_ARITH),
    ),
    row(
        "NRA",
        Theories::NONLINEAR
            .union(Theories::QUANTIFIERS)
            .union(Theories::REALS)
            .union(Theories::WIDE_ARITH),
    ),
    row(
        "QF_ANIA",
        Theories::NONLINEAR
            .union(Theories::ARRAYS)
            .union(Theories::INTS)
            .union(Theories::WIDE_ARITH),
    ),
    row(
        "QF_UFNIA",
        Theories::NONLINEAR.union(Theories::UF).union(Theories::INTS).union(Theories::WIDE_ARITH),
    ),
    row(
        "QF_UFNRA",
        Theories::NONLINEAR.union(Theories::UF).union(Theories::REALS).union(Theories::WIDE_ARITH),
    ),
    row(
        "QF_NIRA",
        Theories::NONLINEAR
            .union(Theories::INTS)
            .union(Theories::REALS)
            .union(Theories::WIDE_ARITH),
    ),
    row(
        "FPLRA",
        Theories::QUANTIFIERS
            .union(Theories::REALS)
            .union(Theories::FLOATS)
            .union(Theories::WIDE_ARITH),
    ),
    row(
        "AUFBV",
        Theories::QUANTIFIERS
            .union(Theories::ARRAYS)
            .union(Theories::UF)
            .union(Theories::BITVECTORS),
    ),
    row(
        "ABVFP",
        Theories::QUANTIFIERS
            .union(Theories::ARRAYS)
            .union(Theories::BITVECTORS)
            .union(Theories::FLOATS),
    ),
    row(
        "UFBVFP",
        Theories::QUANTIFIERS
            .union(Theories::UF)
            .union(Theories::BITVECTORS)
            .union(Theories::FLOATS),
    ),
    row(
        "QF_AUFBVFP",
        Theories::ARRAYS.union(Theories::UF).union(Theories::BITVECTORS).union(Theories::FLOATS),
    ),
    row(
        "UFBVDT",
        Theories::QUANTIFIERS
            .union(Theories::UF)
            .union(Theories::BITVECTORS)
            .union(Theories::DATATYPES),
    ),
    row(
        "QF_UFDTLIA",
        Theories::UF.union(Theories::DATATYPES).union(Theories::INTS).union(Theories::WIDE_ARITH),
    ),
    // Lever C, the ACCEPTED half: bitvectors mixed with integers. Measured
    // 2026-09-18 accepted by `ay_bindings::execute_direct::logic::parse_logic`
    // and identical to `ALL` on every decided query; the six REFUSED names of
    // the same class are on the rejection list above.
    row(
        "QF_UFBVLIA",
        Theories::UF.union(Theories::BITVECTORS).union(Theories::INTS).union(Theories::WIDE_ARITH),
    ),
    // LEVER C, CLOSED 2026-09-18: the names that used to be refused because the
    // NATIVE lane's parser refuses them. That was never a property of the NAME
    // — it is a property of one CONSUMER — and it is now handled where the
    // consumer is, by `trust_router::in_process_ay_backend::native_lane_logic`.
    // See the rejection note above for the criterion that replaced it. Every
    // one of these six is appended at the END of its cardinality group, so no
    // existing tie changes hands.
    //
    // `QF_BVFPLRA` [S2] is the row that gives `{BitVectors, Reals}` its first
    // name: SMT-LIB spells that mix only through the FP family.
    row(
        "QF_BVFPLRA",
        Theories::BITVECTORS
            .union(Theories::FLOATS)
            .union(Theories::REALS)
            .union(Theories::WIDE_ARITH),
    ),
    // — five dimensions —
    //
    // `AUFLIRA` LEADS THIS GROUP, and the placement is load-bearing:
    // `QF_UFDTLIRA` (below) also admits `{UF, Ints, Reals}` at cardinality five,
    // so the two tie and table order picks the datatype-free name.
    //
    // `AUFLIRA` WITHOUT ITS ARRAY BIT. The name carries an `A`, and the row
    // deliberately does NOT claim `ARRAYS`. SMT-LIB's AUFLIRA declaration
    // restricts every array term to sort `(Array Int Real)` or
    // `(Array Int (Array Int Real))`, which is a STRICT SUBFRAGMENT of this
    // record's unconditional `ARRAYS` bit — the record cannot express "arrays,
    // but only at those two sorts", so a row claiming `ARRAYS` here would let
    // the selector emit a name NARROWER than its own content, the one direction
    // this table must never take. Under-stating costs only precision: an
    // array-bearing mixed-linear set falls through to `AUFNIRA`, whose
    // declaration explicitly permits an arbitrary array sort and is therefore
    // the honest name for it. Measured: claiming `ARRAYS` here captured eight
    // array-bearing sets from `AUFNIRA` and the module's own transcript fuzz
    // reproduced the resulting over-narrow header within 6000 seeds. The same
    // argument is what keeps the `A`-leading DATATYPE names out of the table
    // entirely — see the note above.
    row(
        "AUFLIRA",
        Theories::QUANTIFIERS
            .union(Theories::UF)
            .union(Theories::INTS)
            .union(Theories::REALS)
            .union(Theories::WIDE_ARITH),
    ),
    row(
        "AUFLIA",
        Theories::QUANTIFIERS
            .union(Theories::ARRAYS)
            .union(Theories::UF)
            .union(Theories::INTS)
            .union(Theories::WIDE_ARITH),
    ),
    row(
        "UFNIA",
        Theories::NONLINEAR
            .union(Theories::QUANTIFIERS)
            .union(Theories::UF)
            .union(Theories::INTS)
            .union(Theories::WIDE_ARITH),
    ),
    row(
        "UFNRA",
        Theories::NONLINEAR
            .union(Theories::QUANTIFIERS)
            .union(Theories::UF)
            .union(Theories::REALS)
            .union(Theories::WIDE_ARITH),
    ),
    row(
        "QF_AUFNIA",
        Theories::NONLINEAR
            .union(Theories::ARRAYS)
            .union(Theories::UF)
            .union(Theories::INTS)
            .union(Theories::WIDE_ARITH),
    ),
    row(
        "ANIA",
        Theories::NONLINEAR
            .union(Theories::QUANTIFIERS)
            .union(Theories::ARRAYS)
            .union(Theories::INTS)
            .union(Theories::WIDE_ARITH),
    ),
    row(
        "AUFBVFP",
        Theories::QUANTIFIERS
            .union(Theories::ARRAYS)
            .union(Theories::UF)
            .union(Theories::BITVECTORS)
            .union(Theories::FLOATS),
    ),
    row(
        "QF_UFDTLIRA",
        Theories::UF
            .union(Theories::DATATYPES)
            .union(Theories::INTS)
            .union(Theories::REALS)
            .union(Theories::WIDE_ARITH),
    ),
    row(
        "QF_UFDTNIA",
        Theories::NONLINEAR
            .union(Theories::UF)
            .union(Theories::DATATYPES)
            .union(Theories::INTS)
            .union(Theories::WIDE_ARITH),
    ),
    row(
        "UFDTLIA",
        Theories::QUANTIFIERS
            .union(Theories::UF)
            .union(Theories::DATATYPES)
            .union(Theories::INTS)
            .union(Theories::WIDE_ARITH),
    ),
    row(
        "QF_AUFBVLIA",
        Theories::ARRAYS
            .union(Theories::UF)
            .union(Theories::BITVECTORS)
            .union(Theories::INTS)
            .union(Theories::WIDE_ARITH),
    ),
    // LEVER C, CLOSED — the five-dimension half. `UFBVLIA` [S2] is
    // `QF_UFBVLIA`'s quantified sibling; `BVFPLRA` and `QF_ABVFPLRA` [S2] are
    // `QF_BVFPLRA`'s quantified and array-bearing ones, and both have the same
    // standing as the `ABVFP`/`QF_ABVFP` rows already in this group.
    row(
        "UFBVLIA",
        Theories::QUANTIFIERS
            .union(Theories::UF)
            .union(Theories::BITVECTORS)
            .union(Theories::INTS)
            .union(Theories::WIDE_ARITH),
    ),
    row(
        "BVFPLRA",
        Theories::QUANTIFIERS
            .union(Theories::BITVECTORS)
            .union(Theories::FLOATS)
            .union(Theories::REALS)
            .union(Theories::WIDE_ARITH),
    ),
    row(
        "QF_ABVFPLRA",
        Theories::ARRAYS
            .union(Theories::BITVECTORS)
            .union(Theories::FLOATS)
            .union(Theories::REALS)
            .union(Theories::WIDE_ARITH),
    ),
    // — six dimensions —
    row(
        "AUFNIA",
        Theories::NONLINEAR
            .union(Theories::QUANTIFIERS)
            .union(Theories::ARRAYS)
            .union(Theories::UF)
            .union(Theories::INTS)
            .union(Theories::WIDE_ARITH),
    ),
    row(
        "UFNIRA",
        Theories::NONLINEAR
            .union(Theories::QUANTIFIERS)
            .union(Theories::UF)
            .union(Theories::INTS)
            .union(Theories::REALS)
            .union(Theories::WIDE_ARITH),
    ),
    row(
        "UFDTLIRA",
        Theories::QUANTIFIERS
            .union(Theories::UF)
            .union(Theories::DATATYPES)
            .union(Theories::INTS)
            .union(Theories::REALS)
            .union(Theories::WIDE_ARITH),
    ),
    row(
        "UFDTNIA",
        Theories::NONLINEAR
            .union(Theories::QUANTIFIERS)
            .union(Theories::UF)
            .union(Theories::DATATYPES)
            .union(Theories::INTS)
            .union(Theories::WIDE_ARITH),
    ),
    // LEVER C, CLOSED — the six-dimension half. `QF_AUFBVNIA` [S3] is
    // `QF_AUFBVLIA`'s nonlinear sibling and carries the same [S3] standing;
    // `ABVFPLRA` [S2] is `QF_ABVFPLRA` with quantifiers.
    row(
        "QF_AUFBVNIA",
        Theories::ARRAYS
            .union(Theories::UF)
            .union(Theories::BITVECTORS)
            .union(Theories::NONLINEAR)
            .union(Theories::INTS)
            .union(Theories::WIDE_ARITH),
    ),
    row(
        "ABVFPLRA",
        Theories::QUANTIFIERS
            .union(Theories::ARRAYS)
            .union(Theories::BITVECTORS)
            .union(Theories::FLOATS)
            .union(Theories::REALS)
            .union(Theories::WIDE_ARITH),
    ),
    // — seven dimensions —
    row(
        "UFDTNIRA",
        Theories::NONLINEAR
            .union(Theories::QUANTIFIERS)
            .union(Theories::UF)
            .union(Theories::DATATYPES)
            .union(Theories::INTS)
            .union(Theories::REALS)
            .union(Theories::WIDE_ARITH),
    ),
    // — eight dimensions —
    //
    // `AUFNIRA` carries `WIDE_ARRAY`: its [S1] declaration is "Closed formulas
    // built over arbitrary expansions of the Reals_Ints and ArraysEx
    // signatures with free sort and function symbols" — an ARBITRARY array
    // sort, unlike `AUFLIA`'s `(Array Int Int)` — so it is the least real name
    // for an array-bearing set whose array is neither `(Array Int Int)` nor a
    // positive-width `(Array (_ BitVec i) (_ BitVec j))`, short of `ALL`.
    row(
        "AUFNIRA",
        Theories::NONLINEAR
            .union(Theories::QUANTIFIERS)
            .union(Theories::ARRAYS)
            .union(Theories::WIDE_ARRAY)
            .union(Theories::UF)
            .union(Theories::INTS)
            .union(Theories::REALS)
            .union(Theories::WIDE_ARITH),
    ),
    // — the top —
    row("ALL", Theories::EVERYTHING),
];

/// The logic name to write for a query that uses exactly `required`.
///
/// A TOTAL function of the feature set — the whole record is computed first and
/// this makes ONE decision over all the bits: the FIRST row of
/// [`LOGIC_LATTICE`], in table order, that admits every required theory with
/// the fewest admitted theories overall. `ALL` is in the table and admits
/// everything, so the answer is always defined; the `unwrap`-free fallback
/// below is a totality belt, not a reachable branch.
///
/// Proved by exhaustive enumeration in this module's tests: the result admits
/// `required` (ADMISSIBILITY — `every_feature_set_selects_an_admitting_logic`),
/// it is MINIMAL, i.e. no admitting row admits strictly less
/// (`selection_is_a_minimal_admitting_row`), and the tie among equally-minimal
/// rows is broken deterministically by table order
/// (`selection_is_the_first_minimal_row_in_table_order`).
///
/// # The selection is NOT monotone, and no caller depends on it
///
/// See the module header for the exact characterization (751 of 177_147 subset
/// pairs, all with an `S1` no row names exactly). What replaces monotonicity for the
/// multi-formula callers is UNION-THEN-SELECT-ONCE. THE AUDIT, one line per
/// call site in the workspace, current as of this revision:
///
/// | call site | shape | needs |
/// |---|---|---|
/// | `trust_types::smt_logic::select_logic` | ONE formula | admissibility |
/// | `trust_types::ay_bridge` (4 sites, via `select_logic`) | ONE formula | admissibility |
/// | `trust_router::smt2_export::detect_logic` | ONE formula | admissibility |
/// | `trust_router::smtlib_backend::generate_smtlib_script` | ONE formula | admissibility |
/// | `trust_router::in_process_ay_backend::problem_smt2` (the TEXT transcript) | ONE formula | admissibility |
/// | `trust_router::in_process_ay_backend::build_program` (the NATIVE program) | ONE formula | admissibility, from the ACCEPTED sublattice — it calls `native_lane_logic`, not this function, so a name that consumer's parser cannot read can never reach it. Measured 2026-09-19 at ay 9d2cda9c8: that parser refuses NONE of this table's rows, so the call is currently a no-op — kept, and pinned as one, against a future narrowing |
/// | `trust_router::incremental_ay::detect_group_logic` | GROUP | union, then ONE select |
/// | `trust_router::incremental_ay::IncrementalAYSession` base logic | SESSION | union, then ONE select; a caller's explicit logic is honoured only when it PROVABLY admits that union, else widened — an override [`logic_admits`] does not know is credited with Core only |
/// | `trust_clean::logic_classification::classify_formula` | ONE formula | reads the record, not a name |
/// | `trust_types::smtlib2_printer` | strings, no `Formula` | pinned to `ALL` (the top) |
///
/// EVERY ONE OF THOSE SITES GETS ITS RECORD FROM A BUILDER THAT INCLUDES
/// [`wide_arithmetic_theories`]. There are exactly two builders —
/// [`formula_theories`] here and `trust_router::smt2_export::analyze_formula`,
/// which adds the transcript's `declare-fun` signature sorts — and since
/// `QF_IDL`/`QF_RDL` became rows, a builder that omits the linear-form bit
/// would answer `QF_IDL` for every integer query. `the_wide_bit_is_not_
/// derivable_node_by_node` and trust-router's `features_carry_the_linear_form_
/// bit` pin the two against each other.
///
/// The single-formula sites cannot need monotonicity: they select once, from
/// the complete record of the one formula they emit. The two multi-formula
/// sites are the ones that WOULD have needed it, and both now fold
/// [`Theories::union_all`] over their members and call this function ONCE on
/// the result — `incremental_ay` additionally keeps the session's running union
/// in `SessionState::session_theories` and re-selects (re-initializing the
/// solver's base scope) whenever a later query widens it, so the live
/// `(set-logic …)` always admits every query asserted under it. No consumer was
/// found that needs monotonicity and cannot be expressed over a union.
const fn select_row_index_slow(required: Theories) -> u8 {
    let mut best_idx: Option<usize> = None;
    let mut best_len: u32 = u32::MAX;
    let mut i = 0;
    while i < LOGIC_LATTICE.len() {
        let candidate = &LOGIC_LATTICE[i];
        if required.is_subset_of(candidate.admits) {
            let len = candidate.admits.len();
            if best_idx.is_none() || len < best_len {
                best_idx = Some(i);
                best_len = len;
            }
        }
        i += 1;
    }
    match best_idx {
        Some(idx) => idx as u8,
        None => (LOGIC_LATTICE.len() - 1) as u8,
    }
}

const SELECT_INDEX_BY_BITS: [u8; 1 << Theories::BIT_COUNT] = {
    let mut table = [0u8; 1 << Theories::BIT_COUNT];
    let mut bits = 0usize;
    while bits < (1 << Theories::BIT_COUNT) {
        table[bits] = select_row_index_slow(Theories(bits as u16));
        bits += 1;
    }
    table
};

#[must_use]
pub const fn select_logic_name(required: Theories) -> &'static str {
    let bits = required.0 as usize;
    if bits >= SELECT_INDEX_BY_BITS.len() {
        return "ALL";
    }
    let idx = SELECT_INDEX_BY_BITS[bits] as usize;
    if idx < LOGIC_LATTICE.len() {
        LOGIC_LATTICE[idx].name
    } else {
        // Unreachable: `ALL` admits every feature set. Answering `ALL` rather
        // than panicking keeps this function total for the TCB gate.
        "ALL"
    }
}

/// What the logic name `name` admits, or `None` if it is not a name this
/// workspace emits.
///
/// The transcript self-consistency checker reads the table through here, so the
/// row the checker tests a transcript against is literally the row the selector
/// chose it by.
///
/// # `None` MEANS "THIS TABLE CANNOT SAY", NOT "NOT A LOGIC"
///
/// The table holds every name this workspace EMITS, audited against the SMT-LIB
/// sources cited in the module header. It is NOT a census of SMT-LIB: the
/// module header's rejection list still names real logics that are deliberately
/// absent (the `A`-leading `*DT*` names, `QF_UFIDL`, `UFIDL`, the string
/// logics, `AX`, the `*FPDT*` family), and every one of them answers `None`
/// here. The six `*BVLIA`/`*BVFPLRA`/`*BVNIA` names that used to head this list
/// are now ROWS — see the module header's revised criterion.
///
/// # A NAME THIS FUNCTION KNOWS MAY STILL BE ONE A CONSUMER CANNOT PARSE
///
/// Admissibility is all this table records. Sixteen of its names are refused by
/// the NATIVE in-process lane's own parser, which is a property of that lane
/// and not of the name; that lane re-selects from the sublattice it can parse
/// (`trust_router::in_process_ay_backend::native_lane_logic`) instead of asking
/// this table to shrink.
///
/// So a caller holding a name from OUTSIDE this workspace — an operator's
/// explicit `(set-logic …)` override, say — may not read `None` as "that is not
/// a logic" and refuse. What `None` licenses is exactly one inference, and it
/// is the one that holds for every SMT-LIB logic real or hypothetical: the name
/// admits AT LEAST [`Theories::NONE`], because every SMT-LIB logic includes
/// Core. Anything more is unproven. `trust_router::incremental_ay`'s
/// `IncrementalAYSession::base_logic_for` is the consumer that depends on this
/// reading, and its docs state the contract it builds on it.
#[must_use]
pub fn logic_admits(name: &str) -> Option<Theories> {
    LOGIC_LATTICE.iter().find(|row| row.name == name).map(|row| row.admits)
}

/// True iff some row admits EXACTLY `required` — i.e. SMT-LIB, as this table
/// records it, has a name for that feature set and nothing more.
///
/// This is the predicate the monotonicity characterization is stated in: a
/// subset pair can only violate `admits(select(S1)) ⊆ admits(select(S2))` when
/// `S1` is NOT named exactly, because an unnamed `S1` forces the selector onto
/// a row carrying dimensions `S1` never asked for, which a named superset is
/// then free not to carry. See
/// `monotonicity_fails_only_from_sets_no_row_names_exactly`.
#[must_use]
pub const fn is_named_exactly(required: Theories) -> bool {
    let bits = required.0 as usize;
    if bits >= SELECT_INDEX_BY_BITS.len() {
        return false;
    }
    let idx = SELECT_INDEX_BY_BITS[bits] as usize;
    if idx < LOGIC_LATTICE.len() {
        LOGIC_LATTICE[idx].admits.0 == required.0
    } else {
        false
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// 3. READING THE FEATURE RECORD OFF A FORMULA
// ─────────────────────────────────────────────────────────────────────────────

fn array_sort_theories(index: &Sort, element: &Sort) -> Theories {
    let theories =
        Theories::ARRAYS.union(sort_theories(index)).union(sort_theories(element));
    // THE TWO RESTRICTED SHAPES, as the [S1] declarations write them:
    // `QF_AUFLIA` admits only `(Array Int Int)`, `QF_ABV` only
    // `(Array (_ BitVec i) (_ BitVec j))` with `i, j > 0`. Anything
    // else — a `Bool` index or element, a nested array, a mixed
    // `(Array Int (_ BitVec 8))`, a zero-width bitvector — needs a
    // name whose declaration admits an ARBITRARY array sort
    // (`QF_AX`, `AUFNIRA`, `ALL`); see [`Theories::WIDE_ARRAY`].
    match (index, element) {
        (Sort::Int, Sort::Int) => theories,
        (Sort::BitVec(i), Sort::BitVec(j)) if *i > 0 && *j > 0 => theories,
        _ => theories.union(Theories::WIDE_ARRAY),
    }
}

/// The theories one SORT belongs to.
///
/// Follows arrays into BOTH positions, since an `(Array Int (_ BitVec 8))`
/// needs the array AND the bitvector theory.
///
/// AND IT FOLLOWS A DATATYPE INTO ITS CONSTRUCTORS' FIELD SORTS, which it did
/// NOT have to do while Lever A routed every datatype-bearing query to `ALL`:
/// the old body stopped at [`Theories::DATATYPES`] and said so, because the top
/// admits everything a field could possibly name. Re-pointing Lever A
/// (2026-09-18) made that reasoning false, and the module's own transcript
/// self-consistency fuzz caught it at seed 4 within one run:
///
/// ```text
/// (set-logic QF_UFDTLIRA)
/// (declare-datatype Expr ((Const (ec (_ BitVec 32))) (App (ef Expr) (ex Expr)) (Unit)))
/// ```
///
/// — a `(_ BitVec 32)` written into the transcript under a logic line that
/// admits no bitvector theory, which is EXACTLY the defect class this module
/// exists to close, arriving through the one sort position nothing else walks.
/// A `declare-datatype` line names every field sort, so every field sort has to
/// reach the logic line.
///
/// TERMINATION is structural: [`Sort`] is a finite tree, and a RECURSIVE
/// datatype spells its back-edge as a by-name reference (a `Sort::Datatype`
/// with NO constructors), so the recursion below bottoms out on it.
#[must_use]
pub fn sort_theories(sort: &Sort) -> Theories {
    match sort {
        Sort::Bool => Theories::NONE,
        Sort::Int => Theories::INTS,
        Sort::Real => Theories::REALS,
        Sort::BitVec(_) => Theories::BITVECTORS,
        Sort::Float { .. } | Sort::RoundingMode => Theories::FLOATS,
        Sort::Array(index, element) => array_sort_theories(index, element),
        Sort::Datatype { constructors, .. } => {
            let mut theories = Theories::DATATYPES;
            for (_, fields) in constructors {
                for (_, field_sort) in fields {
                    theories.insert(sort_theories(field_sort));
                }
            }
            theories
        }
        // A future `#[non_exhaustive]` sort is one this classifier cannot
        // read, and a sort it cannot read is one no row can be shown to admit:
        // it forces the top rather than contributing nothing, which would let a
        // narrower header stand over a declaration this revision never saw.
        // (The in-process lane declines such a sort outright —
        // `unlowerable_sort_position` — before any logic line is written, so
        // this arm is a belt, and a fail-closed one.)
        _ => Theories::EVERYTHING,
    }
}

/// True iff `node` is a CONCRETE COEFFICIENT — the `c` of the `(* c x)` /
/// `(* x c)` forms the linear declarations' `:extensions` admit ([S1], quoted
/// on [`Theories::NONLINEAR`]).
///
/// `QF_LIA`: "`c` is a term of the form `n` or `(- n)` for some numeral `n`".
/// `QF_LRA`: an integer coefficient `m` / `(- m)`, or a rational one — "`d`,
/// `(- d)` or `(/ c n)` for some decimal `d`, integer coefficient `c` and
/// numeral `n` other than 0". So `Int`, `UInt` and `Rat` are coefficients
/// (a `Rat` lowers to `(/ (- m) n)` / `(/ m n)`, i.e. `(/ c n)` with an
/// integer coefficient numerator — `RatLit::to_smtlib`), and a `Neg` of a
/// NON-NEGATIVE integer literal is one (`(- 3)`). A `Neg` of a negative `Int`
/// is NOT: `Int(-3)` already renders as `(- 3)`, so its negation is
/// `(- (- 3))`, which is neither `n` nor `(- n)`. Nor is a `Neg` of a `Rat`,
/// because `(- (/ 1 2))` is none of the listed forms. Folding either would
/// claim a spelling the declaration does not list.
///
/// DELIBERATELY SHALLOW, AND THEREFORE AN OVER-APPROXIMATION OF NONLINEARITY.
/// `Mul(x, Add(Int(2), Int(3)))` multiplies by a constant but not by a
/// COEFFICIENT, so [`node_theories`] calls it nonlinear and the query heads
/// `QF_NIA` instead of `QF_LIA`. That is the SOUND direction: a wider logic
/// admits strictly more, so it cannot turn a SAT violation into UNSAT. The
/// opposite shape — an UNDER-approximation, e.g. testing "contains no `Var`",
/// which misses `Mul(x, FnApp(f, [Int(1)]))` — would head a linear logic over a
/// genuinely nonlinear assertion, which is the defect this dimension exists to
/// close. trust-clean's `CleanExtras` uses the under-approximating form for its
/// own purpose (picking a certification DEGRADATION STRATEGY, where missing a
/// nonlinear term only costs a certificate); a logic NAME may not.
fn is_numeric_literal(node: &Formula) -> bool {
    match node {
        Formula::Int(_) | Formula::UInt(_) | Formula::Rat { .. } => true,
        Formula::Neg(inner) => {
            matches!(**inner, Formula::Int(n) if n >= 0) || matches!(**inner, Formula::UInt(_))
        }
        _ => false,
    }
}

/// True iff `node` is the `x` of the linear declarations' `(* c x)` /
/// `(* x c)` — "`x` is a free constant" ([S1], `QF_LIA`/`QF_LRA`
/// `:extensions`) — read as a `Var`/`SymVar` of sort `Int` or `Real`, which
/// is what renders as a bare symbol declared by `(declare-fun x () Int)`.
///
/// DELIBERATELY NARROWER THAN [`difference_operand_sort`], which also accepts
/// a 0-ary `FnApp`: that predicate answers a `QF_IDL`/`QF_RDL` question and
/// this one an `N`-family question, and the two dimensions are kept apart so
/// an edit made for one cannot move the other. Refusing the 0-ary application
/// here is the conservative direction — the product charges
/// [`Theories::NONLINEAR`] and the header widens. Every compound term — a sum,
/// an applied function, a `select`, an `ite`, another product — is refused for
/// the same reason: `3 * (x + y)` is not `(* c x)` with `x` a free constant,
/// whatever its arithmetic value, and `QF_AUFLIA`'s wider `:extensions` ("a
/// free constant or a term with top symbol not in Ints") is not the rule the
/// narrowest linear name is declared under.
fn is_free_constant(node: &Formula) -> bool {
    matches!(
        node,
        Formula::Var(_, Sort::Int | Sort::Real) | Formula::SymVar(_, Sort::Int | Sort::Real)
    )
}

/// The theories ONE NODE contributes on its own — its LITERAL/OPERATOR content
/// and, for the three ARITHMETIC SHAPES that decide LINEARITY, the SHALLOW
/// FORM of its own operands; not its children's own content and not the sorts
/// it carries.
///
/// THE ONE PLACE THIS FUNCTION READS A CHILD. [`Theories::NONLINEAR`] is not a
/// property of a node in isolation — `(* 3 x)` is linear and `(* x y)` is not,
/// and the two are the same `Mul` constructor — so the `Mul` arm tests its
/// operands with [`is_numeric_literal`] and [`is_free_constant`], one-level
/// pattern matches that never recurse into a subterm's own theory content.
/// (`Div`/`Rem` read no child at all any more: they are nonlinear outright.)
/// Every other arm still contributes on its own. The distinction matters because the whole
/// module exists to stop two walkers from disagreeing: the shared traversal in
/// [`formula_theories`] visits every node, so each `Mul` is classified when the
/// walk reaches IT, and reading its immediate operands adds no second walk.
///

/// Sorts are classified separately, from the shared sort-position inventory
/// (`smt_logic::visit_node_sort_positions`), because a `Ctor`/`FnApp` result
/// sort, a `Sel` field sort and a quantifier BINDER sort each reach a theory no
/// `Var` in the formula need carry. This function is the other half: the theory
/// content that no sort position carries.
///
/// `FpConst` is the one arm worth naming. It lowers — on BOTH lanes — to
/// `((_ to_fp eb sb) (_ bv<bits> eb+sb))`, i.e. an FP literal built out of a
/// BITVECTOR literal. SMT-LIB puts that `to_fp`-from-bitvector form in the
/// combined BV+FP fragment (`QF_BVFP`), not in `QF_FP`, so the node needs both
/// bits. Before this it set only the float bit, and a transcript carrying
/// `(_ bv0 64)` could be headed `QF_FP` — the same disagreement between the
/// logic line and the text below it that this module exists to remove.
#[must_use]
pub fn node_theories(node: &Formula) -> Theories {
    match node {
        // Bitvector literals and operators.
        Formula::BitVec { .. }
        | Formula::BvAdd(..)
        | Formula::BvSub(..)
        | Formula::BvMul(..)
        | Formula::BvUDiv(..)
        | Formula::BvSDiv(..)
        | Formula::BvURem(..)
        | Formula::BvSRem(..)
        | Formula::BvAnd(..)
        | Formula::BvOr(..)
        | Formula::BvXor(..)
        | Formula::BvNot(..)
        | Formula::BvShl(..)
        | Formula::BvLShr(..)
        | Formula::BvAShr(..)
        | Formula::BvULt(..)
        | Formula::BvULe(..)
        | Formula::BvSLt(..)
        | Formula::BvSLe(..)
        | Formula::BvExtract { .. }
        | Formula::BvConcat(..)
        | Formula::BvZeroExt(..)
        | Formula::BvSignExt(..) => Theories::BITVECTORS,

        // The Int<->BV bridges touch BOTH theories: `(bv2int x)` is an
        // Int-sorted term with no Int variable or literal anywhere, and
        // `((_ int2bv w) n)` has an Int-sorted operand.
        Formula::BvToInt(..) | Formula::IntToBv(..) => Theories::BITVECTORS.union(Theories::INTS),

        // Floating point crossing into the bitvector theory: the conversions
        // that produce or consume a BV, and the `FpConst` bit-pattern literal.
        Formula::FpConst { .. }
        | Formula::FpToIeeeBv(..)
        | Formula::FpFromBits { .. }
        | Formula::FpToSbv { .. }
        | Formula::FpToUbv { .. }
        | Formula::FpFromSbv { .. }
        | Formula::FpFromUbv { .. } => Theories::FLOATS.union(Theories::BITVECTORS),

        // Pure floating point: literals, predicates and arithmetic whose
        // SMT-LIB spelling mentions no other theory.
        Formula::FpNaN { .. }
        | Formula::FpInf { .. }
        | Formula::FpZero { .. }
        | Formula::FpRoundingMode(..)
        | Formula::FpConvert { .. }
        | Formula::FpAdd(..)
        | Formula::FpSub(..)
        | Formula::FpMul(..)
        | Formula::FpDiv(..)
        | Formula::FpFma(..)
        | Formula::FpSqrt(..)
        | Formula::FpRem(..)
        | Formula::FpNeg(..)
        | Formula::FpAbs(..)
        | Formula::FpMin(..)
        | Formula::FpMax(..)
        | Formula::FpEq(..)
        | Formula::FpLt(..)
        | Formula::FpLe(..)
        | Formula::FpGt(..)
        | Formula::FpGe(..)
        | Formula::FpIsNaN(..)
        | Formula::FpIsInfinite(..)
        | Formula::FpIsZero(..)
        | Formula::FpIsNormal(..)
        | Formula::FpIsSubnormal(..)
        | Formula::FpIsNegative(..)
        | Formula::FpIsPositive(..) => Theories::FLOATS,

        // Integer and rational LITERALS. (`UInt` renders as a plain SMT-LIB
        // numeral exactly as `Int` does, so it needs the same theory.) The
        // arithmetic nodes (`Add`/`Sub`/`Mul`/…) are sort-GENERIC and carry the
        // theory of their operands, which this same walk classifies — so they
        // contribute no SORT bit here. What three of them DO contribute is the
        // LINEARITY bit, below.
        Formula::Int(_) | Formula::UInt(_) => Theories::INTS,
        Formula::Rat { .. } => Theories::REALS,

        // NONLINEAR ARITHMETIC — the `L`→`N` swap in the SMT-LIB family name.
        //
        // A product is LINEAR only in the two shapes the [S1] `:extensions`
        // list — `(* c x)` and `(* x c)`, `c` a concrete coefficient and `x` a
        // FREE CONSTANT — and nonlinear otherwise: `3 * x` and `x * (-3)` are
        // linear terms of `QF_LIA`; `x * y`, `3 * (x + y)`, `3 * f(x)` and
        // `3 * (select a i)` are not. `Mul` is sort-generic (`infer_sort`
        // propagates the operand sort), so this arm covers the `Real` product
        // too and the REALS bit arrives from the same walk's sort positions —
        // `{NONLINEAR, REALS}` heads `QF_NRA`.
        Formula::Mul(a, b)
            if !((is_numeric_literal(a) && is_free_constant(b))
                || (is_free_constant(a) && is_numeric_literal(b))) =>
        {
            Theories::NONLINEAR
        }
        // Division and remainder are NEVER linear. `QF_LIA`'s `:language`
        // excludes them by name — "no occurrences of the function symbols
        // `**`, `/`, `div`, `mod`, and `abs`" — with no numeral-divisor
        // exception (the `:extensions` clause speaks of `*` only), so `x div 2`
        // is as far outside the linear name as `x div y`, and both head the `N`
        // family, whose declarations restrict neither. Both nodes are Int-only
        // in this contract (`smt_logic::infer_sort` returns `Sort::Int`
        // unconditionally and `check_formula_sort` rejects `Real` operands), so
        // they can only ever produce `{NONLINEAR, INTS, …}`, never a nonlinear
        // REAL requirement. They lower to SMT-LIB `div`/`mod` (the `Div`
        // lowering spells both).
        Formula::Div(..) | Formula::Rem(..) => Theories::NONLINEAR,
        // `Add`, `Sub`, `Neg`, and the two linear product shapes above, are
        // linear whatever their operands, and fall through to `NONE`.
        //
        // NOT HERE, DELIBERATELY: `BvMul`/`BvUDiv`/`BvSDiv`/`BvURem`/`BvSRem`
        // and every `Fp*` operator. SMT-LIB has no `QF_NBV` and no nonlinear
        // floating-point name — `QF_BV` admits `bvmul` of two variables and
        // `QF_FP` admits `fp.mul`, unconditionally — so charging the bit there
        // would push every bitvector multiply to `ALL` for nothing. Those arms
        // are matched ABOVE, so they cannot reach these guards.

        // Array operations. (An array-sorted VARIABLE or binder is a sort
        // position, classified from the sort inventory; so is the `(Array I E)`
        // a constant array spells, which is where a WIDE_ARRAY shape such as
        // `(Array Int (_ BitVec 8))` is charged.) `((as const S) v)` is the
        // de-facto ArraysEx extension ay, Z3 and cvc5 accept under the array
        // logics; a text consumer whose solver lacks it refuses the node
        // (trust-ir-contract's ConstArray contract), it is never approximated.
        Formula::Select(..) | Formula::Store(..) | Formula::ConstArray { .. } => Theories::ARRAYS,

        // Quantifiers. Only the FLAG is term-level: the binder SORTS are sort
        // positions, and they are NOT `children()` edges.
        Formula::Forall(..) | Formula::Exists(..) => Theories::QUANTIFIERS,

        // An applied uninterpreted symbol of arity >= 1 is a genuine UF
        // requirement; a 0-ary one is an ordinary free constant that every
        // SMT-LIB logic admits. Its argument and result SORTS are sort
        // positions, classified from the inventory.
        Formula::Pred(_, args) if !args.is_empty() => Theories::UF,
        Formula::FnApp { args, .. } if !args.is_empty() => Theories::UF,

        _ => Theories::NONE,
    }
}

/// The SORT-AND-OPERATOR half of the feature record: every sort position, every
/// by-name datatype reference, and every literal/operator.
///
/// ONE TRAVERSAL over the ONE sort inventory
/// (`smt_logic::visit_node_sort_positions` +
/// `smt_logic::node_named_datatype_reference`), so the logic line cannot see a
/// different set of sorts from the one the declarations are written from.
///
/// This is everything [`node_theories`] can decide NODE BY NODE. The LINEAR
/// FORM dimension cannot be decided that way — it is a property of a whole
/// ATOM — so it is computed separately by [`wide_arithmetic_theories`] and
/// unioned in by [`formula_theories`].
fn node_sort_theories(node: &Formula) -> Theories {
    match node {
        Formula::ConstArray { index_sort, elem_sort, .. } => {
            array_sort_theories(index_sort, elem_sort)
        }
        _ => {
            let mut theories = Theories::NONE;
            crate::smt_logic::visit_node_sort_positions(node, &mut |sort| {
                theories.insert(sort_theories(sort));
            });
            theories
        }
    }
}

fn base_theories(formula: &Formula) -> Theories {
    let mut theories = Theories::NONE;
    crate::visit_formula_nodes(formula, &mut |node| {
        theories.insert(node_sort_theories(node));
        if crate::smt_logic::node_named_datatype_reference(node).is_some() {
            theories.insert(Theories::DATATYPES);
        }
        theories.insert(node_theories(node));
    });
    theories
}

/// The complete feature record of `formula`: [`base_theories`] plus the
/// LINEAR-FORM qualifier [`wide_arithmetic_theories`].
///
/// trust-router's transcript lane adds one more source on top of this — the
/// `declare-fun` SIGNATURE map it declares uninterpreted symbols from — and
/// then calls the same [`select_logic_name`]. **That lane builds its record
/// from [`sort_theories`], [`node_theories`] AND [`wide_arithmetic_theories`]
/// directly** (`smt2_export::analyze_formula`); the linear-form bit is a
/// PUBLIC part of the record precisely so a second record-builder cannot
/// silently omit it and emit `QF_IDL` over a general arithmetic transcript.
#[must_use]
pub fn formula_theories(formula: &Formula) -> Theories {
    let base = base_theories(formula);
    if base.contains(Theories::INTS) || base.contains(Theories::REALS) {
        base.union(wide_arithmetic_theories(formula))
    } else {
        base
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// 4. THE LINEAR-FORM QUALIFIER — reading DIFFERENCE ATOMS off a formula
// ─────────────────────────────────────────────────────────────────────────────

/// The arithmetic sort a DIFFERENCE ATOM may range over. `Int` and `Real` are
/// kept apart because a difference atom's two sides must agree, and because
/// `QF_IDL`'s and `QF_RDL`'s declarations are different grammars.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DiffSort {
    Int,
    Real,
}

/// The sort of `node` if it is a FREE CONSTANT SYMBOL of an arithmetic sort —
/// the only term `QF_IDL`/`QF_RDL` let either side of a difference be.
///
/// A `Var`/`SymVar` and a 0-ARY `FnApp` all render as a bare symbol declared by
/// `(declare-fun x () Int)`, which is exactly "a free constant symbol of sort
/// Int". An APPLIED `FnApp`, a `select`, an `ite`, a literal, or any compound
/// term answers `None`, so an atom built over one is not recognized and widens
/// the header.
///
/// A quantifier-BOUND variable is also a `Var` and is deliberately not
/// distinguished here: both difference logics are quantifier-free, so a bound
/// variable can only occur under [`Theories::QUANTIFIERS`], which no difference
/// row admits.
fn difference_operand_sort(node: &Formula) -> Option<DiffSort> {
    let sort = match node {
        Formula::Var(_, sort) | Formula::SymVar(_, sort) => sort,
        Formula::FnApp { args, sort, .. } if args.is_empty() => sort,
        _ => return None,
    };
    match sort {
        Sort::Int => Some(DiffSort::Int),
        Sort::Real => Some(DiffSort::Real),
        _ => None,
    }
}

/// True iff `node` is `m` or `(- m)` for a NUMERAL `m` — the only bound either
/// difference grammar accepts.
///
/// [`Formula::Rat`] is deliberately NOT one, even at denominator 1: it renders
/// as an exact rational term, and `QF_RDL`'s declaration says the bound is "an
/// expression of the form `m` or `(- m)` for some numeral `m`". Refusing it
/// costs only precision — the atom widens the header — while accepting it would
/// claim a shape the declaration does not list.
///
/// A `Neg` of a NEGATIVE `Int` is not one either: `Int(-3)` already renders as
/// `(- 3)`, so its negation is `(- (- 3))`, neither `m` nor `(- m)`.
///
/// This is NOT [`is_numeric_literal`], which folds `Rat` in: that predicate
/// answers "is this a LINEAR multiplier", a question about the `N`-family
/// dimension, and the two must not be merged.
fn is_numeral_bound(node: &Formula) -> bool {
    match node {
        Formula::Int(_) | Formula::UInt(_) => true,
        Formula::Neg(inner) => {
            matches!(**inner, Formula::Int(n) if n >= 0) || matches!(**inner, Formula::UInt(_))
        }
        _ => false,
    }
}

/// True iff `node` is an atom of SMT-LIB's `QF_IDL`/`QF_RDL` grammar, as those
/// declarations write it ([S1]; quoted in full on [`LOGIC_LATTICE`]).
///
/// THE THREE RECOGNIZED SHAPES, and nothing else:
///
/// * `(op (- x y) n)` and `(op (- x y) (- n))` — a difference of two free
///   constant symbols of the SAME arithmetic sort against a numeral;
/// * `(op x y)` — two free constant symbols of the same arithmetic sort.
///
/// `op` is `<`, `<=`, `>`, `>=` or `=`. (`distinct` is in the declarations'
/// list, but this contract has no `Distinct` node, so there is nothing to
/// match.)
///
/// WHAT IS DELIBERATELY NOT RECOGNIZED, each a conservative widening:
///
/// * `(op x n)` — a bare bound such as `x > 3`. NEITHER declaration lists it,
///   which surprises everyone who knows the textbook definition, so it is
///   called out here: an ordinary bounds check heads `QF_LIA`, not `QF_IDL`.
/// * `(op n (- x y))` — the MIRRORED form. It is semantically equivalent, but
///   a replayer checks the TEXT, and the text `(< 3 (- x y))` is not one of the
///   listed atoms.
/// * `QF_RDL`'s scaled form `(op (- (+ x … x) (+ y … y)) c)`. Real, listed, and
///   not recognized: it would take a term-shape equality check for no reachable
///   benefit, and failing to recognize it only widens.
/// * Anything whose operands are not free constants — `select`, an applied
///   function, a nested sum, an `ite`.
fn is_difference_atom(node: &Formula) -> bool {
    let (lhs, rhs) = match node {
        Formula::Lt(a, b)
        | Formula::Le(a, b)
        | Formula::Gt(a, b)
        | Formula::Ge(a, b)
        | Formula::Eq(a, b) => (a.as_ref(), b.as_ref()),
        _ => return false,
    };
    // `(op x y)`: two free constant symbols of the SAME arithmetic sort.
    if let (Some(left), Some(right)) = (difference_operand_sort(lhs), difference_operand_sort(rhs))
    {
        return left == right;
    }
    // `(op (- x y) n)` / `(op (- x y) (- n))`.
    match lhs {
        Formula::Sub(x, y) => match (difference_operand_sort(x), difference_operand_sort(y)) {
            (Some(left), Some(right)) => left == right && is_numeral_bound(rhs),
            _ => false,
        },
        _ => false,
    }
}

/// True iff `node`'s subtree mentions the `Int` or `Real` theory at all — the
/// test that decides whether an UNRECOGNIZED atom is an ARITHMETIC atom (and so
/// charges [`Theories::WIDE_ARITH`]) or carries no arithmetic to widen.
///
/// Reads the same sort-position inventory and [`node_theories`] as
/// [`base_theories`], short-circuiting on the first node that contributes
/// `INTS` or `REALS` so "mentions arithmetic" cannot drift from "the record
/// carries `INTS` or `REALS`".
fn mentions_arithmetic(node: &Formula) -> bool {
    const ARITH: u16 = Theories::INTS.0 | Theories::REALS.0;
    !crate::all_formula_nodes(node, &mut |sub| {
        if (node_theories(sub).0 & ARITH) != 0 {
            return false;
        }
        (node_sort_theories(sub).0 & ARITH) == 0
    })
}

/// The recursive half of [`wide_arithmetic_theories`]: descend the BOOLEAN
/// structure, and at each ATOM decide whether it forces the wider fragment.
///
/// The boolean connectives are transparent — `QF_IDL` and `QF_RDL` are
/// "Boolean combinations of" their atoms — so `Not`/`And`/`Or`/`Implies`/`Ite`
/// recurse and a quantifier body recurses too (a quantifier already takes the
/// query out of every `QF_` row, so recursing there costs nothing and keeps the
/// function total). EVERYTHING ELSE IS AN ATOM: if it is not a recognized
/// difference atom and it mentions arithmetic, it is wide.
///
/// TOTALITY AND COST. The connective walk partitions the formula into DISJOINT
/// atom subtrees, so the [`base_theories`] call inside [`mentions_arithmetic`]
/// runs over each node at most once across the whole walk: the pass is linear,
/// not quadratic.
fn wide_arith_required(node: &Formula) -> bool {
    match node {
        Formula::Not(inner) => wide_arith_required(inner),
        Formula::And(parts) | Formula::Or(parts) => {
            parts.iter().any(|part| wide_arith_required(part))
        }
        Formula::Implies(antecedent, consequent) => {
            wide_arith_required(antecedent) || wide_arith_required(consequent)
        }
        Formula::Ite(condition, then_branch, else_branch) => {
            wide_arith_required(condition)
                || wide_arith_required(then_branch)
                || wide_arith_required(else_branch)
        }
        Formula::Forall(_, body) | Formula::Exists(_, body) => wide_arith_required(body),
        atom => !is_difference_atom(atom) && mentions_arithmetic(atom),
    }
}

/// [`Theories::WIDE_ARITH`] if `formula` needs the full `LIA`/`LRA` atom
/// grammar, [`Theories::NONE`] if every one of its atoms is provably inside
/// SMT-LIB's difference fragment.
///
/// CONSERVATIVE IN THE SOUND DIRECTION, WHICH IS THE WHOLE CONTRACT. The bit is
/// CLEARED only when the recognizer understands every atom. Any shape it does
/// not understand — a sum, a product, a `select`, an applied function, a
/// non-numeral bound, a mirrored comparison, a bare `x > 3` — sets it, and
/// setting it can only move the selection to a WIDER name. The opposite
/// mistake, clearing it on a general formula, is exactly the over-narrow header
/// this module exists to close, and it is the one that would be SILENT: ay maps
/// `QF_IDL` onto its full `QfLia` solver and enforces no fragment restriction,
/// so nothing in-house would report it (measured 2026-09-18).
///
/// PUBLIC BECAUSE THERE IS A SECOND RECORD-BUILDER. trust-router's
/// `smt2_export::analyze_formula` assembles its own `Theories` from
/// [`sort_theories`] and [`node_theories`] plus the transcript's `declare-fun`
/// signatures; it MUST union this in too, or its lane would answer `QF_IDL`
/// for a record that carries `INTS` and nothing else. `logic_lattice`'s
/// `the_wide_bit_is_not_derivable_node_by_node` and trust-router's
/// `features_carry_the_linear_form_bit` pin the two lanes together.
#[must_use]
pub fn wide_arithmetic_theories(formula: &Formula) -> Theories {
    if wide_arith_required(formula) { Theories::WIDE_ARITH } else { Theories::NONE }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every feature set in the 2^11 powerset, as `Theories`.
    fn powerset() -> Vec<Theories> {
        (0..(1u16 << Theories::BIT_COUNT)).map(Theories::from_bits).collect()
    }

    fn admits_of(name: &str) -> Theories {
        logic_admits(name)
            .unwrap_or_else(|| panic!("`{name}` was selected but has no row in LOGIC_LATTICE"))
    }

    /// THE POWERSET IS SMALL ENOUGH TO ENUMERATE. 11 bool dimensions, no enum
    /// dimensions: 2048 feature sets and 4_194_304 ordered pairs. Nothing is
    /// sampled, nothing is fuzzed, and no reduction is needed. (It was 8
    /// dimensions, 256 sets and 65_536 pairs before the LINEARITY bit, then 9
    /// dimensions, 512 sets and 262_144 pairs before the LINEAR-FORM bit, then
    /// 10 dimensions, 1024 sets and 1_048_576 pairs before the ARRAY-SHAPE bit;
    /// the enumeration is still exhaustive at the new size, which is what made
    /// adding each bit a table edit rather than a proof-strategy change.)
    #[test]
    fn the_enumeration_covers_the_entire_feature_powerset() {
        assert_eq!(Theories::BIT_COUNT, 11);
        assert_eq!(powerset().len(), 2048, "2^11 feature sets");
        // `EVERYTHING` must be exactly the union of the enumerated sets, or
        // `ALL` would admit less than the powerset and ADMISSIBILITY would be
        // proved over sets the table cannot serve.
        assert_eq!(Theories::union_all(powerset()), Theories::EVERYTHING);
        // `from_bits` fails closed, so no caller can build a set outside the
        // enumeration by handing it an out-of-range word — it gets the top.
        assert_eq!(Theories::from_bits(u16::MAX), Theories::EVERYTHING);
    }

    /// ADMISSIBILITY — THE INVARIANT, for every one of the 2048 feature sets:
    /// the selected logic admits every theory in the set.
    ///
    /// This is the only property the table promises and the only one any caller
    /// is allowed to rely on.
    #[test]
    fn every_feature_set_selects_an_admitting_logic() {
        for required in powerset() {
            let chosen = select_logic_name(required);
            let admits = admits_of(chosen);
            assert!(
                required.is_subset_of(admits),
                "select_logic_name({required:?}) = `{chosen}`, which admits {admits:?} — \
                 it does not admit every required theory"
            );
        }
    }

    /// ADMISSIBILITY OF THE UNION — what every GROUP and BATCH consumer rests
    /// on, over all 4_194_304 ordered pairs of feature sets: selecting ONCE from
    /// `S1 ∪ S2` yields a name admitting `S1` AND `S2`.
    ///
    /// This is the replacement for monotonicity. A caller writing one
    /// `(set-logic L)` over several formulas folds their records with
    /// [`Theories::union_all`] and selects once; this test says that the single
    /// name so obtained covers every member, with no ordering property of the
    /// selector involved. (It is a corollary of admissibility — `S1 ⊆ S1 ∪ S2` —
    /// but it is the form the consumers cite, so it is checked in that form.)
    #[test]
    fn union_admissibility_covers_every_member() {
        let sets = powerset();
        let mut checked = 0usize;
        for &s1 in &sets {
            for &s2 in &sets {
                let joint = Theories::union_all([s1, s2]);
                let admits = admits_of(select_logic_name(joint));
                assert!(
                    s1.is_subset_of(admits) && s2.is_subset_of(admits),
                    "selecting from the union {joint:?} gave `{}` (admitting {admits:?}), which \
                     does not cover both {s1:?} and {s2:?}",
                    select_logic_name(joint)
                );
                checked += 1;
            }
        }
        assert_eq!(checked, 4_194_304, "every ordered pair must have been checked");
    }

    /// MINIMALITY: no row that also admits the set admits STRICTLY LESS than
    /// the chosen one. The selection never widens beyond what the table offers.
    ///
    /// This is the honest weakening of the previous revision's "UNIQUE LEAST
    /// admitting row". A least row need not exist — five rows admit `∅`, and
    /// none of them is inside the others — but a MINIMAL one always does, and
    /// the selector always finds one.
    #[test]
    fn selection_is_a_minimal_admitting_row() {
        for required in powerset() {
            let chosen_name = select_logic_name(required);
            let chosen = admits_of(chosen_name);
            for candidate in LOGIC_LATTICE {
                if !required.is_subset_of(candidate.admits) {
                    continue;
                }
                let strictly_smaller =
                    candidate.admits.is_subset_of(chosen) && candidate.admits != chosen;
                assert!(
                    !strictly_smaller,
                    "for {required:?} the selector chose `{chosen_name}` (admitting {chosen:?}), \
                     but `{}` also admits the set and admits strictly less ({:?})",
                    candidate.name, candidate.admits
                );
            }
        }
    }

    /// DETERMINISM: the chosen row is the FIRST minimal-cardinality admitting
    /// row in [`LOGIC_LATTICE`] order. Reordering the table is therefore an
    /// observable change, and this test is what makes that explicit.
    #[test]
    fn selection_is_the_first_minimal_row_in_table_order() {
        for required in powerset() {
            let chosen = select_logic_name(required);
            let best_len = LOGIC_LATTICE
                .iter()
                .filter(|row| required.is_subset_of(row.admits))
                .map(|row| row.admits.len())
                .min()
                .expect("`ALL` admits every set");
            let expected = LOGIC_LATTICE
                .iter()
                .find(|row| required.is_subset_of(row.admits) && row.admits.len() == best_len)
                .expect("the minimum was just computed over a non-empty set");
            assert_eq!(
                chosen, expected.name,
                "for {required:?} the selector must pick the first row of cardinality \
                 {best_len} that admits it"
            );
        }
    }

    /// MONOTONICITY IS NOT A PROPERTY OF THIS TABLE, and this test says exactly
    /// where it fails rather than asserting it or dropping it.
    ///
    /// Over all 177_147 subset-related pairs, `admits(select(S1)) ⊆
    /// admits(select(S2))` fails for EXACTLY the pairs whose `S1` is a feature
    /// set NO ROW NAMES EXACTLY ([`is_named_exactly`]), and there are exactly
    /// 751 such failures spread over exactly 30 sets. Equivalently: whenever
    /// SMT-LIB, as this table records it, HAS a name for `S1` itself,
    /// monotonicity HOLDS.
    ///
    /// THE STRUCTURAL REASON. When `S1` is unnamed the minimal admitting row
    /// must carry dimensions `S1` never asked for — `{UF, Ints, Reals}` takes
    /// `AUFLIRA`, which also promises quantifiers — and a superset that IS
    /// named exactly is then free not to carry them: `{UF, Ints, Reals,
    /// Datatypes, WideArith}` takes `QF_UFDTLIRA`, no quantifiers, and
    /// `AUFLIRA ⊄ QF_UFDTLIRA`.
    ///
    /// THE HISTORY, because the SHAPE of this characterization changed and the
    /// count moved in both directions:
    ///
    /// * 37 failures over 7 sets before the LINEARITY bit, 139 over 11 after —
    ///   and in both the violating `S1` were exactly the MODIFIER-ONLY sets
    ///   ([`Theories::is_modifier_only`]), which is how this test used to be
    ///   written. That form held only because three rows — `LIRA`, `UFLIRA`,
    ///   `QF_UFLIRA` — named three base-sort sets exactly, and those three names
    ///   are not SMT-LIB logics (see the REMOVED note on [`LOGIC_LATTICE`]).
    /// * Deleting them left those three sets unnamed, so they began to violate,
    ///   which is what forced the characterization up to its real form. It is a
    ///   STRENGTHENING, not a loosening: "unnamed" implied nothing here before
    ///   and implies nothing now, while "modifier-only" was the accident of a
    ///   table containing invented names. The modifier-only claim is still
    ///   checked below, as the sub-characterization it always was.
    /// * `QF_AX` and `UF` then REMOVED two long-standing violators — `{Arrays}`
    ///   and `{Quantifiers, UF}` are named exactly now — and the FP rows added
    ///   one, `{BitVectors, Floats, UF}`, which no single name covers: 116 over
    ///   13.
    /// * The LINEAR-FORM bit and the Lever A / Lever C SPLIT took it to 289 over
    ///   20. Most of that growth was mechanical: the powerset doubled, so every
    ///   modifier-only violator acquired a `WideArith` twin. The one
    ///   NON-mechanical arrival is `{UF, Ints, Reals}` (and its wide twin),
    ///   which stopped violating when `AUFLIRA` became honest about arrays and
    ///   started again when `QF_UFDTLIRA` — a datatype row that admits the same
    ///   set at the same cardinality but promises no quantifiers — joined the
    ///   table. That is the characterization doing its job: the set still has no
    ///   EXACT name, and it is the absence of an exact name, not any particular
    ///   row, that the failure tracks.
    /// * CLOSING LEVER C took it to 455 over 29, and every one of the nine new
    ///   sources is the same shape: a `*BVFPLRA` row gave some superset a name
    ///   carrying NEITHER `INTS` nor `UF`, so the `*LIA`/`*UFBV*` name a
    ///   smaller subset takes stopped being contained in it. `{A,W}` → `QF_ALIA`
    ///   under `{A,Reals,W}` → `QF_ABVFPLRA` is the clearest instance. Growing
    ///   this count is the PRICE of a more precise table and nothing else: the
    ///   sets that acquired a violation are exactly sets with no exact name,
    ///   which is what the characterization has always said, and no consumer
    ///   reads the selector pairwise (see below).
    /// * THE ARRAY-SHAPE BIT took it to 751 over 30. The powerset doubled
    ///   again, so every source acquired a `WideArray` twin's worth of pairs,
    ///   and ONE new source arrived: `{Arrays}` itself. `QF_AX` now admits
    ///   `{Arrays, WideArray}` — its declaration restricts nothing — so
    ///   `{Arrays}` alone has no exact name any more, heads `QF_AX`, and
    ///   `{Arrays, BitVectors}` → `QF_ABV` no longer contains it. That is the
    ///   characterization again, and the reason `{Arrays}` left the
    ///   named-exactly list below: it is unreachable from a formula (an array
    ///   sort always charges a base sort or the wide bit), so the table names
    ///   what can occur.
    ///
    /// NOTHING RELIES ON THIS. The group/batch consumers select from the UNION
    /// (`union_admissibility_covers_every_member`); the audit of every call
    /// site is in [`select_logic_name`]'s docs.
    #[test]
    fn monotonicity_fails_only_from_sets_no_row_names_exactly() {
        let sets = powerset();
        let mut related = 0usize;
        let mut violations = 0usize;
        let mut violating_sources: Vec<Theories> = Vec::new();
        for &s1 in &sets {
            for &s2 in &sets {
                if !s1.is_subset_of(s2) {
                    continue;
                }
                related += 1;
                let a1 = admits_of(select_logic_name(s1));
                let a2 = admits_of(select_logic_name(s2));
                if a1.is_subset_of(a2) {
                    continue;
                }
                violations += 1;
                assert!(
                    !is_named_exactly(s1),
                    "monotonicity failed at {s1:?} ⊆ {s2:?} (`{}` ⊄ `{}`), but a row admits \
                     {s1:?} EXACTLY — the documented characterization says that cannot happen",
                    select_logic_name(s1),
                    select_logic_name(s2)
                );
                if !violating_sources.contains(&s1) {
                    violating_sources.push(s1);
                }
            }
        }
        // 3^11: one of {out, in-S1-and-S2, in-S2-only} per bit.
        assert_eq!(related, 177_147, "every subset-related pair must have been checked");
        assert_eq!(violations, 751, "the extent of the failure is pinned, not merely bounded");

        // The thirty sets are enumerated rather than described, so a table edit
        // that moves one of them shows up as a diff in this list.
        violating_sources.sort_unstable();
        let nl = Theories::NONLINEAR;
        let q = Theories::QUANTIFIERS;
        let a = Theories::ARRAYS;
        let uf = Theories::UF;
        let bv = Theories::BITVECTORS;
        let fp = Theories::FLOATS;
        let ints = Theories::INTS;
        let reals = Theories::REALS;
        let w = Theories::WIDE_ARITH;
        let wa = Theories::WIDE_ARRAY;
        let expected: Vec<Theories> = vec![
            // MODIFIER-ONLY, WITHOUT the linear-form bit — the nine the table
            // carried before the linear-form bit, plus `{Arrays}`, which
            // joined when `QF_AX` took the array-shape bit and stopped naming
            // it exactly.
            Theories::NONE,
            q,
            a,
            q.union(a),
            a.union(uf),
            q.union(a).union(uf),
            nl,
            nl.union(q),
            nl.union(uf),
            nl.union(q).union(uf),
            // MODIFIER-ONLY, WITH it. Ten, and the membership is still NOT
            // simply "the nine above plus `W`": `{UF,W}` and `{Q,UF,W}` violate
            // although their bases `{UF}` and `{Q,UF}` do not — `QF_UF` and
            // `UF` name those exactly, and no row names their wide twins.
            // `{A,W}` and `{Q,A,W}` JOINED when Lever C closed: `QF_ALIA`/
            // `ALIA` promise `INTS`, and `{A,Reals,W}` — a superset — now has
            // `QF_ABVFPLRA`, which does not.
            w,
            q.union(w),
            a.union(w),
            q.union(a).union(w),
            uf.union(w),
            q.union(uf).union(w),
            nl.union(w),
            nl.union(q).union(w),
            nl.union(uf).union(w),
            nl.union(q).union(uf).union(w),
            // THE TEN THAT NAME A BASE SORT. `{BitVectors, Floats, UF}` has
            // no wide twin: `WIDE_ARITH` with no `INTS`/`REALS` alongside
            // `BV`+`FP` takes `ALL`, which is monotone trivially. The seven
            // `{A,Reals,…}` / `{…,BV,W}` entries are Lever C's arrivals: the
            // `*BVFPLRA` rows gave array-and-real and bitvector-and-real sets
            // names that carry neither `INTS` nor `UF`, so the `*LIA` name a
            // smaller subset takes is no longer contained in them.
            bv.union(fp).union(uf),
            ints.union(reals).union(uf),
            ints.union(reals).union(uf).union(w),
            a.union(reals),
            q.union(a).union(reals),
            a.union(reals).union(w),
            q.union(a).union(reals).union(w),
            bv.union(w),
            q.union(bv).union(w),
            a.union(bv).union(w),
        ];
        let mut expected_sorted = expected;
        expected_sorted.sort_unstable();
        assert_eq!(
            violating_sources, expected_sorted,
            "the sets monotonicity fails from are pinned by name"
        );

        // THE SUB-CHARACTERIZATION, kept because it is what the module header
        // records about SMT-LIB's naming habits: every violating source that
        // names NO base sort theory is modifier-only by definition, and only
        // TEN violators name one — `{BitVectors, Floats, UF}`, which no single
        // FP name covers; the mixed linear `{UF, Ints, Reals}` with its wide
        // twin, which tie `AUFLIRA` against `QF_UFDTLIRA`; and the seven Lever
        // C brought in, where a `*BVFPLRA` name carries neither `INTS` nor `UF`
        // and so fails to contain the `*LIA`/`*UFBV*` name a subset takes.
        let base_sort_violators: Vec<Theories> =
            violating_sources.iter().copied().filter(|s| !s.is_modifier_only()).collect();
        let mut expected_base = vec![
            bv.union(fp).union(uf),
            ints.union(reals).union(uf),
            ints.union(reals).union(uf).union(w),
            a.union(reals),
            q.union(a).union(reals),
            a.union(reals).union(w),
            q.union(a).union(reals).union(w),
            bv.union(w),
            q.union(bv).union(w),
            a.union(bv).union(w),
        ];
        expected_base.sort_unstable();
        assert_eq!(
            base_sort_violators, expected_base,
            "only the sets SMT-LIB leaves unnamed may violate from a base sort theory"
        );

        // `{UF}` alone is NOT among them: `QF_UF` admits exactly `{UF}` and
        // every superset's row admits UF too. Nor is `{Quantifiers, UF}`
        // (`UF`) any longer — naming a set exactly is what takes it off this
        // list. `{Ints}` and `{Reals}` joined that company with
        // `QF_IDL`/`QF_RDL`, and `{Datatypes}` with `QF_DT`. `{Arrays}` LEFT
        // it when `QF_AX` took `WIDE_ARRAY`: the exactly-named array set is now
        // `{Arrays, WideArray}`, and bare `{Arrays}` is unreachable anyway.
        for named in [Theories::UF, q.union(uf), ints, reals, Theories::DATATYPES, a.union(wa)] {
            assert!(is_named_exactly(named));
            assert!(!violating_sources.contains(&named));
        }
        assert!(!is_named_exactly(a) && violating_sources.contains(&a));
        // Nor is any modifier-only set carrying BOTH `NONLINEAR` and `ARRAYS`:
        // `QF_ANIA` admits exactly `{Nonlinear, Arrays, Ints, WideArith}` and
        // every superset's row admits all four.
        for extra in [Theories::NONE, q, uf, q.union(uf)] {
            assert!(!violating_sources.contains(&nl.union(a).union(extra)));
        }
    }

    /// HOW MUCH OF THE POWERSET TAKES `ALL`, pinned as a number — AND AS A
    /// FRACTION, because the powerset itself changed size twice.
    ///
    /// THE HISTORY. The revision that under-stated `QF_UF` and dropped the nine
    /// modifier-carrying BV/Real names sent **230 of 256** feature sets to
    /// `ALL`; with the honest rows restored it was **223 of 256** (87.1%). The
    /// LINEARITY bit took the powerset to 512, at **439 of 512** (85.7%), and
    /// the SMT-LIB name audit (the FP family, `QF_AX`, `UF`, `ANIA`, `AUFLIRA`
    /// for the three invented `*LIRA` names) brought that to **422 of 512**
    /// (82.4%).
    ///
    /// AFTER THE LINEAR-FORM BIT AND THE LEVER A / LEVER C ROWS the powerset
    /// was 1024 and the split was 337 of the 512 LINEAR sets (65.8%), 400 of
    /// the 512 NONLINEAR sets (78.1%) — the datatype rows reach the `N` family
    /// too (`QF_UFDTNIA`, `UFDTNIA`, `UFDTNIRA`) — and 737 of 1024 overall
    /// (72.0%), against 422 of 512 (82.4%) before.
    ///
    /// AFTER THE ARRAY-SHAPE BIT the powerset is 2048 and the split is:
    ///
    /// * **785 of the 1024 LINEAR sets** (76.7%) take `ALL`.
    /// * **848 of the 1024 NONLINEAR sets** (82.8%) take `ALL`.
    /// * **1633 of 2048 overall** (79.7%). The rise is the `WideArray` half:
    ///   only `QF_AX`, `AUFNIRA` and `ALL` carry the bit, so of the 1024 sets
    ///   that carry it every one outside those two names' reach takes the top.
    ///   Among the sets a formula can present the figure is what matters, and
    ///   it is below.
    ///
    /// CLOSING LEVER C (2026-09-18) IS THE LAST MOVE IN THOSE FIGURES, and it
    /// is worth reading separately because it is the one that came from
    /// RETIRING A CRITERION rather than from a new dimension. The six names the
    /// table had refused on the ground that ay's IN-PROCESS parser refuses them
    /// — `UFBVLIA`, `QF_AUFBVNIA`, `QF_BVFPLRA`, `BVFPLRA`, `QF_ABVFPLRA`,
    /// `ABVFPLRA` — became rows once that ground moved to the lane it belongs
    /// to (`trust_router::in_process_ay_backend::native_lane_logic`). 53 of the
    /// 1024 sets changed name: 49 off `ALL` (786 → 737) and 4 from `AUFNIRA`
    /// onto a narrower `*BVFPLRA`. The NATIVE lane's header moved for none of
    /// the 1024, because it selects from the accepted sublattice and no new row
    /// joins it.
    ///
    /// THE COMPARABLE FIGURES, because a doubled powerset makes the headline
    /// percentages talk past each other. Two readings, both computed here:
    ///
    /// * **THE IMAGE OF THE OLD POWERSET.** Every 9-bit set corresponds to the
    ///   10-bit set with `WIDE_ARITH` SET — "arithmetic is general", which is
    ///   what the 9-bit record always implicitly meant. Of those 512,
    ///   **375 take `ALL`**, against 422 before the two levers and 404 before
    ///   Lever C closed.
    /// * **THE REACHABLE SETS.** `NONLINEAR` and `WIDE_ARITH` are both
    ///   qualifiers on an arithmetic family, so a set carrying either without
    ///   `INTS` or `REALS` cannot arise from any formula. There are 832
    ///   reachable sets, of which **604 take `ALL`** (72.6%), against 366 of
    ///   448 (81.7%) before. This is the honest comparison.
    ///
    /// NOTHING REACHABLE MOVED ONTO `ALL`. Eighteen UNREACHABLE sets did —
    /// `{BitVectors, Floats, WideArith}` and its relatives, which claim the
    /// linear-form qualifier with no arithmetic sort to qualify — and they are
    /// pinned below as `ALL` precisely because no formula can present them.
    #[test]
    fn the_share_of_the_powerset_that_takes_all_is_pinned() {
        let takes_all = |s: &&Theories| select_logic_name(**s) == "ALL";
        let all_count = powerset().iter().filter(takes_all).count();
        let linear_all = powerset()
            .iter()
            .filter(|s| !s.contains(Theories::NONLINEAR))
            .filter(takes_all)
            .count();
        let nonlinear_all =
            powerset().iter().filter(|s| s.contains(Theories::NONLINEAR)).filter(takes_all).count();
        assert_eq!(
            linear_all, 785,
            "LINEAR feature sets selecting `ALL`, of 1024 (was 337 of 512)"
        );
        assert_eq!(
            nonlinear_all, 848,
            "NONLINEAR feature sets selecting `ALL`, of 1024 (was 400 of 512)"
        );
        assert_eq!(
            all_count, 1633,
            "feature sets selecting `ALL`, of 2048 (was 737 of 1024 before the array-shape bit)"
        );
        assert_eq!(linear_all + nonlinear_all, all_count);

        // THE IMAGE OF THE OLD 9-BIT POWERSET: the sets that carry the
        // linear-form bit, i.e. "arithmetic is general". 375 of 512 before the
        // array-shape bit, against the 422 of 512 the 9-bit table recorded.
        let wide_all = powerset()
            .iter()
            .filter(|s| s.contains(Theories::WIDE_ARITH))
            .filter(takes_all)
            .count();
        assert_eq!(wide_all, 823, "of the 1024 WIDE_ARITH sets, `ALL`'s share (was 375 of 512)");

        // THE REACHABLE SETS: a qualifier bit needs something to qualify, so
        // `NONLINEAR`/`WIDE_ARITH` without `INTS`/`REALS`, and `WIDE_ARRAY`
        // without `ARRAYS`, are sets no formula can present.
        let reachable = |s: &&Theories| {
            let arithmetic = s.contains(Theories::INTS) || s.contains(Theories::REALS);
            (!s.contains(Theories::NONLINEAR) || arithmetic)
                && (!s.contains(Theories::WIDE_ARITH) || arithmetic)
                && (!s.contains(Theories::WIDE_ARRAY) || s.contains(Theories::ARRAYS))
        };
        let reachable_count = powerset().iter().filter(reachable).count();
        let reachable_all = powerset().iter().filter(reachable).filter(takes_all).count();
        assert_eq!(reachable_count, 1248, "feature sets a formula can actually present");
        assert_eq!(reachable_all, 968, "reachable sets selecting `ALL` (was 604 of 832)");

        // THE DIFFERENCE ROWS. Exactly two feature sets in the whole powerset
        // head a difference logic, and they are the two the fragment names:
        // integer (resp. real) content with NO wide atom and no modifier.
        // Everything else arithmetic carries `WIDE_ARITH` or a modifier and
        // heads a general name, which is what keeps the blast radius of this
        // dimension exactly as small as its declarations are narrow.
        let difference_named = powerset()
            .iter()
            .filter(|s| matches!(select_logic_name(**s), "QF_IDL" | "QF_RDL"))
            .count();
        assert_eq!(difference_named, 2, "only `{{Ints}}` and `{{Reals}}` head a difference logic");
        assert_eq!(select_logic_name(Theories::INTS), "QF_IDL");
        assert_eq!(select_logic_name(Theories::REALS), "QF_RDL");
        assert_eq!(select_logic_name(Theories::INTS.union(Theories::WIDE_ARITH)), "QF_LIA");
        assert_eq!(select_logic_name(Theories::REALS.union(Theories::WIDE_ARITH)), "QF_LRA");

        // LEVER A, RE-POINTED: 68 of the 1024 datatype-bearing sets now head a
        // `DT` name instead of `ALL`, and every one of those names contains
        // `DT` — which is what keeps `in_process_ay_backend`'s datatype-program
        // assertion (`logic == "ALL" || logic.contains("DT")`) true and what
        // makes `AYProgram::upgrade_logic_for_datatypes` leave the header
        // alone.
        let datatype_named = powerset()
            .iter()
            .filter(|s| s.contains(Theories::DATATYPES))
            .filter(|s| select_logic_name(**s) != "ALL")
            .count();
        assert_eq!(datatype_named, 68, "datatype-bearing sets with an SMT-LIB name, of 1024");
        for set in powerset().iter().filter(|s| s.contains(Theories::DATATYPES)) {
            let name = select_logic_name(*set);
            assert!(
                name == "ALL" || name.contains("DT"),
                "{set:?} carries datatypes but heads `{name}`, which names no datatype theory"
            );
        }
        for (set, name) in [
            (Theories::DATATYPES, "QF_DT"),
            (Theories::DATATYPES.union(Theories::UF), "QF_UFDT"),
            (Theories::DATATYPES.union(Theories::QUANTIFIERS), "UFDT"),
            (Theories::DATATYPES.union(Theories::BITVECTORS), "QF_UFBVDT"),
            (
                Theories::DATATYPES.union(Theories::QUANTIFIERS).union(Theories::BITVECTORS),
                "UFBVDT",
            ),
            (Theories::DATATYPES.union(Theories::INTS).union(Theories::WIDE_ARITH), "QF_UFDTLIA"),
            (
                Theories::DATATYPES
                    .union(Theories::INTS)
                    .union(Theories::REALS)
                    .union(Theories::WIDE_ARITH),
                "QF_UFDTLIRA",
            ),
            (
                Theories::DATATYPES
                    .union(Theories::NONLINEAR)
                    .union(Theories::INTS)
                    .union(Theories::WIDE_ARITH),
                "QF_UFDTNIA",
            ),
            (
                Theories::DATATYPES
                    .union(Theories::QUANTIFIERS)
                    .union(Theories::INTS)
                    .union(Theories::WIDE_ARITH),
                "UFDTLIA",
            ),
            (
                Theories::DATATYPES
                    .union(Theories::QUANTIFIERS)
                    .union(Theories::INTS)
                    .union(Theories::REALS)
                    .union(Theories::WIDE_ARITH),
                "UFDTLIRA",
            ),
            (
                Theories::DATATYPES
                    .union(Theories::QUANTIFIERS)
                    .union(Theories::NONLINEAR)
                    .union(Theories::INTS)
                    .union(Theories::WIDE_ARITH),
                "UFDTNIA",
            ),
            (
                Theories::DATATYPES
                    .union(Theories::QUANTIFIERS)
                    .union(Theories::NONLINEAR)
                    .union(Theories::INTS)
                    .union(Theories::REALS)
                    .union(Theories::WIDE_ARITH),
                "UFDTNIRA",
            ),
        ] {
            assert_eq!(
                select_logic_name(set),
                name,
                "{set:?} must head the datatype name `{name}` after Lever A was re-pointed"
            );
        }
        // The `A`-LEADING datatype names are NOT in the table (no [S1]
        // declaration to cite for their array fragment), so an array-bearing
        // datatype set still takes `ALL`. Pinned as the deliberate gap it is.
        assert_eq!(select_logic_name(Theories::DATATYPES.union(Theories::ARRAYS)), "ALL");
        // Nor is the FP+DT pair: `{Floats, Datatypes}` is the FLOATS-with-INTS
        // rejection's neighbour and was not revisited.
        assert_eq!(select_logic_name(Theories::DATATYPES.union(Theories::FLOATS)), "ALL");

        // LEVER C, CLOSED: twenty of the 256 `{BitVectors, Ints}` sets now head
        // an SMT-LIB name — eight from the two names the SPLIT admitted
        // (`QF_UFBVLIA`, `QF_AUFBVLIA`) and twelve more from `UFBVLIA` and
        // `QF_AUFBVNIA`, which came in when the native parser stopped deciding
        // table membership. The remaining 236 carry a dimension no such name
        // admits (`FLOATS`, `REALS`, `DATATYPES`) and still take `ALL`.
        let bv_int_named = powerset()
            .iter()
            .filter(|s| s.contains(Theories::BITVECTORS) && s.contains(Theories::INTS))
            .filter(|s| select_logic_name(**s) != "ALL")
            .count();
        assert_eq!(bv_int_named, 20, "bitvector-with-integer sets with an SMT-LIB name, of 256");

        // THE SEVENTEEN SETS THE FP FAMILY MOVED OFF `ALL`, each pinned to the
        // name that now heads it. Every one carries `FLOATS`; nothing else
        // moved, and nothing moved the other way.
        for (set, name) in [
            (Theories::QUANTIFIERS.union(Theories::FLOATS), "FP"),
            (Theories::ARRAYS.union(Theories::FLOATS), "QF_ABVFP"),
            (Theories::QUANTIFIERS.union(Theories::ARRAYS).union(Theories::FLOATS), "ABVFP"),
            (Theories::BITVECTORS.union(Theories::FLOATS), "QF_BVFP"),
            (Theories::QUANTIFIERS.union(Theories::BITVECTORS).union(Theories::FLOATS), "BVFP"),
            (Theories::ARRAYS.union(Theories::BITVECTORS).union(Theories::FLOATS), "QF_ABVFP"),
            (
                Theories::QUANTIFIERS
                    .union(Theories::ARRAYS)
                    .union(Theories::BITVECTORS)
                    .union(Theories::FLOATS),
                "ABVFP",
            ),
            (Theories::REALS.union(Theories::FLOATS), "QF_FPLRA"),
            (Theories::QUANTIFIERS.union(Theories::REALS).union(Theories::FLOATS), "FPLRA"),
            (Theories::UF.union(Theories::FLOATS), "QF_UFFP"),
            (Theories::QUANTIFIERS.union(Theories::UF).union(Theories::FLOATS), "UFBVFP"),
            (Theories::ARRAYS.union(Theories::UF).union(Theories::FLOATS), "QF_AUFBVFP"),
            (
                Theories::QUANTIFIERS
                    .union(Theories::ARRAYS)
                    .union(Theories::UF)
                    .union(Theories::FLOATS),
                "AUFBVFP",
            ),
            (Theories::BITVECTORS.union(Theories::FLOATS).union(Theories::UF), "UFBVFP"),
            (
                Theories::QUANTIFIERS
                    .union(Theories::BITVECTORS)
                    .union(Theories::FLOATS)
                    .union(Theories::UF),
                "UFBVFP",
            ),
            (
                Theories::ARRAYS
                    .union(Theories::BITVECTORS)
                    .union(Theories::FLOATS)
                    .union(Theories::UF),
                "QF_AUFBVFP",
            ),
            (
                Theories::QUANTIFIERS
                    .union(Theories::ARRAYS)
                    .union(Theories::BITVECTORS)
                    .union(Theories::FLOATS)
                    .union(Theories::UF),
                "AUFBVFP",
            ),
        ] {
            assert_eq!(
                select_logic_name(set),
                name,
                "{set:?} used to take `ALL` for want of an SMT-LIB floating-point row"
            );
        }

        // THE NAMES THE AUDIT RE-POINTED, none of them from or to `ALL`. The
        // three `*LIRA` sets are the removed invented names' own sets.
        for (set, name) in [
            (Theories::ARRAYS, "QF_AX"),
            (Theories::QUANTIFIERS.union(Theories::UF), "UF"),
            (Theories::QUANTIFIERS.union(Theories::INTS).union(Theories::REALS), "AUFLIRA"),
            (Theories::UF.union(Theories::INTS).union(Theories::REALS), "AUFLIRA"),
            (
                Theories::QUANTIFIERS
                    .union(Theories::UF)
                    .union(Theories::INTS)
                    .union(Theories::REALS),
                "AUFLIRA",
            ),
            // …and with the linear-form bit, which is the reachable shape.
            // `QF_UFDTLIRA` ties `AUFLIRA` here at cardinality five and loses
            // on table order; if that placement ever moves, this assertion is
            // what says so.
            (
                Theories::UF
                    .union(Theories::INTS)
                    .union(Theories::REALS)
                    .union(Theories::WIDE_ARITH),
                "AUFLIRA",
            ),
            (Theories::QUANTIFIERS.union(Theories::ARRAYS).union(Theories::NONLINEAR), "ANIA"),
            (
                Theories::QUANTIFIERS
                    .union(Theories::ARRAYS)
                    .union(Theories::INTS)
                    .union(Theories::NONLINEAR),
                "ANIA",
            ),
        ] {
            assert_eq!(select_logic_name(set), name, "{set:?} must head `{name}` after the audit");
        }

        // The eight `{Arrays, Reals}` sets, and what this pin is really about:
        // NOT ONE OF THEM MAY HEAD `AUFLIRA`. An audit pass once moved them
        // there, narrower by the nonlinear promise; that was WRONG. SMT-LIB
        // restricts every AUFLIRA array term to `(Array Int Real)` /
        // `(Array Int (Array Int Real))`, a strict subfragment this record's
        // unconditional `ARRAYS` bit cannot express, so `AUFLIRA` does not
        // claim `ARRAYS` at all (see its row) and can never head an
        // array-bearing set.
        //
        // SIX still take `AUFNIRA`, whose declaration explicitly permits an
        // arbitrary array sort. TWO moved when Lever C closed: the sets
        // carrying NEITHER `UF` NOR `INTS` now head `QF_ABVFPLRA`/`ABVFPLRA`,
        // which admit arrays and reals at cardinality five and six against
        // `AUFNIRA`'s seven. Those two names claim `ARRAYS` on exactly the
        // footing `QF_ABVFP`/`ABVFP` — already rows, already heading
        // `{Arrays, Floats}` — claim it on; the day a citation restricts that
        // family's array sort, all six `*BVFP*` rows move together and this is
        // one of the assertions that will say so.
        for extra in [
            Theories::NONE,
            Theories::QUANTIFIERS,
            Theories::UF,
            Theories::QUANTIFIERS.union(Theories::UF),
        ] {
            for ints in [Theories::NONE, Theories::INTS] {
                let set = Theories::ARRAYS.union(Theories::REALS).union(extra).union(ints);
                let chosen = select_logic_name(set);
                assert_ne!(
                    chosen, "AUFLIRA",
                    "{set:?} bears arrays at an arbitrary sort, and `AUFLIRA` claims none"
                );
                let expected = if extra.contains(Theories::UF) || ints.contains(Theories::INTS) {
                    "AUFNIRA"
                } else if extra.contains(Theories::QUANTIFIERS) {
                    "ABVFPLRA"
                } else {
                    "QF_ABVFPLRA"
                };
                assert_eq!(chosen, expected, "{set:?} must head `{expected}`");
            }
        }

        // The `N` rows are reachable: each names its own set exactly.
        for (set, name) in [
            (Theories::NONLINEAR.union(Theories::INTS), "QF_NIA"),
            (Theories::NONLINEAR.union(Theories::REALS), "QF_NRA"),
            (Theories::NONLINEAR.union(Theories::QUANTIFIERS).union(Theories::INTS), "NIA"),
            (Theories::NONLINEAR.union(Theories::QUANTIFIERS).union(Theories::REALS), "NRA"),
            (Theories::NONLINEAR.union(Theories::ARRAYS).union(Theories::INTS), "QF_ANIA"),
            (Theories::NONLINEAR.union(Theories::UF).union(Theories::INTS), "QF_UFNIA"),
            (Theories::NONLINEAR.union(Theories::UF).union(Theories::REALS), "QF_UFNRA"),
            (Theories::NONLINEAR.union(Theories::INTS).union(Theories::REALS), "QF_NIRA"),
            (
                Theories::NONLINEAR
                    .union(Theories::QUANTIFIERS)
                    .union(Theories::UF)
                    .union(Theories::INTS),
                "UFNIA",
            ),
            (
                Theories::NONLINEAR
                    .union(Theories::QUANTIFIERS)
                    .union(Theories::UF)
                    .union(Theories::REALS),
                "UFNRA",
            ),
            (
                Theories::NONLINEAR
                    .union(Theories::ARRAYS)
                    .union(Theories::UF)
                    .union(Theories::INTS),
                "QF_AUFNIA",
            ),
            (
                Theories::NONLINEAR
                    .union(Theories::QUANTIFIERS)
                    .union(Theories::ARRAYS)
                    .union(Theories::UF)
                    .union(Theories::INTS),
                "AUFNIA",
            ),
            (
                Theories::NONLINEAR
                    .union(Theories::QUANTIFIERS)
                    .union(Theories::UF)
                    .union(Theories::INTS)
                    .union(Theories::REALS),
                "UFNIRA",
            ),
            (
                Theories::NONLINEAR
                    .union(Theories::QUANTIFIERS)
                    .union(Theories::ARRAYS)
                    .union(Theories::UF)
                    .union(Theories::INTS)
                    .union(Theories::REALS),
                "AUFNIRA",
            ),
            // The gap `UFLRA` closes: named exactly, no longer via `UFLIRA`.
            (Theories::QUANTIFIERS.union(Theories::UF).union(Theories::REALS), "UFLRA"),
            // `ANIA` is the row the audit added to the `N` family: quantified
            // arrays over nonlinear integers, which took `AUFNIA` — a name that
            // also promises UF — for want of it.
            (
                Theories::NONLINEAR
                    .union(Theories::QUANTIFIERS)
                    .union(Theories::ARRAYS)
                    .union(Theories::INTS),
                "ANIA",
            ),
        ] {
            assert_eq!(
                select_logic_name(set),
                name,
                "{set:?} must head the precise name `{name}`, not a widened one"
            );
        }

        // A NONLINEAR set mixed with a theory SMT-LIB names no nonlinear logic
        // for still takes `ALL` — the honest answer, and unreachable from a
        // formula besides (the bit is only ever set by an Int/Real node).
        // `{Nonlinear, Floats}` is the last of them.
        assert_eq!(select_logic_name(Theories::NONLINEAR.union(Theories::FLOATS)), "ALL");
        // `{Nonlinear, BitVectors}` LEFT that company when Lever C closed:
        // `QF_AUFBVNIA` is a row now and admits both. (Still unreachable — a
        // `bvmul` never charges `NONLINEAR` — but the answer is no longer the
        // top.)
        assert_eq!(
            select_logic_name(Theories::NONLINEAR.union(Theories::BITVECTORS)),
            "QF_AUFBVNIA"
        );
        // `{Nonlinear, Datatypes}` is no longer one of them: `QF_UFDTNIA` is a
        // row since Lever A was re-pointed, and it admits both.
        assert_eq!(select_logic_name(Theories::NONLINEAR.union(Theories::DATATYPES)), "QF_UFDTNIA");

        // THE UNREACHABLE LINEAR-FORM SETS: `WIDE_ARITH` with no arithmetic
        // sort to qualify. No formula can present one —
        // `wide_arithmetic_theories` charges the bit only at an atom that
        // mentions `Int` or `Real` — so whatever they head is honest either
        // way, and Lever C gave two of them a name because the `*BVFPLRA` rows
        // carry `WIDE_ARITH` alongside `BITVECTORS`/`FLOATS`.
        assert_eq!(
            select_logic_name(
                Theories::WIDE_ARITH.union(Theories::BITVECTORS).union(Theories::FLOATS)
            ),
            "QF_BVFPLRA"
        );
        assert_eq!(
            select_logic_name(
                Theories::WIDE_ARITH.union(Theories::QUANTIFIERS).union(Theories::BITVECTORS)
            ),
            "UFBVLIA"
        );

        for (set, name) in [
            (Theories::QUANTIFIERS.union(Theories::BITVECTORS), "BV"),
            (Theories::ARRAYS.union(Theories::BITVECTORS), "QF_ABV"),
            (Theories::UF.union(Theories::BITVECTORS), "QF_UFBV"),
            (Theories::QUANTIFIERS.union(Theories::ARRAYS).union(Theories::BITVECTORS), "ABV"),
            (Theories::QUANTIFIERS.union(Theories::UF).union(Theories::BITVECTORS), "UFBV"),
            (Theories::ARRAYS.union(Theories::UF).union(Theories::BITVECTORS), "QF_AUFBV"),
            (
                Theories::QUANTIFIERS
                    .union(Theories::ARRAYS)
                    .union(Theories::UF)
                    .union(Theories::BITVECTORS),
                "AUFBV",
            ),
            (Theories::QUANTIFIERS.union(Theories::REALS), "LRA"),
            (Theories::UF.union(Theories::REALS), "QF_UFLRA"),
        ] {
            assert_eq!(
                select_logic_name(set),
                name,
                "{set:?} must head the precise name `{name}`, not a widened one"
            );
        }
    }

    /// The table is a function: no name appears twice with different rows, no
    /// two rows admit the same set, and `ALL` is the top.
    #[test]
    fn the_table_is_well_formed() {
        for (i, row) in LOGIC_LATTICE.iter().enumerate() {
            for other in LOGIC_LATTICE.iter().skip(i + 1) {
                assert_ne!(row.name, other.name, "`{}` has two rows", row.name);
                assert_ne!(
                    row.admits, other.admits,
                    "`{}` and `{}` admit the same set, so the name chosen between them is an \
                     accident of table order",
                    row.name, other.name
                );
            }
        }
        assert_eq!(logic_admits("ALL"), Some(Theories::EVERYTHING));
        // The honest signature: `QF_UF` is the quantifier-free theory of
        // UNINTERPRETED FUNCTIONS with equality, and the table now says so.
        assert_eq!(logic_admits("QF_UF"), Some(Theories::UF));
        assert_eq!(logic_admits("QF_MADE_UP"), None);

        // THE THREE NAMES THE SMT-LIB AUDIT REMOVED. No source — the standard's
        // logic declarations, the benchmark library release, or the SMT-COMP
        // division lists — knows any of them, so emitting one produced a header
        // a replayer could not check. This is pinned as an ABSENCE so a future
        // edit that "restores" a plausible-looking spelling has to argue with
        // the citation in [`LOGIC_LATTICE`] rather than with nothing.
        for invented in ["LIRA", "UFLIRA", "QF_UFLIRA"] {
            assert_eq!(
                logic_admits(invented),
                None,
                "`{invented}` is not an SMT-LIB logic name and must not be emittable"
            );
        }
        // Their replacement, and the sets they used to carry, all take it.
        assert_eq!(
            logic_admits("AUFLIRA"),
            Some(
                Theories::QUANTIFIERS
                    .union(Theories::UF)
                    .union(Theories::INTS)
                    .union(Theories::REALS)
                    .union(Theories::WIDE_ARITH)
            )
        );

        // `is_named_exactly` agrees with the rows, in both directions.
        for row in LOGIC_LATTICE {
            assert!(is_named_exactly(row.admits), "`{}`'s own set must be named", row.name);
        }
        // THE FAMILY SIZES THE DOC PROSE QUOTES, pinned so the prose cannot
        // drift from the rows. `ALL` carries every dimension and is excluded
        // from both counts, as the prose is.
        let family = |bit: Theories| {
            LOGIC_LATTICE.iter().filter(|r| r.name != "ALL" && r.admits.contains(bit)).count()
        };
        // LEVER C CLOSED 2026-09-18 moved three of these: `QF_AUFBVNIA` joins
        // the `N` family, the four `*BVFPLRA` names join the FP family, and all
        // six carry the full atom grammar.
        assert_eq!(family(Theories::NONLINEAR), 19, "the `N` family, as the table doc counts it");
        assert_eq!(family(Theories::FLOATS), 16, "the FP family, as the table doc counts it");
        assert_eq!(family(Theories::DATATYPES), 12, "the `DT` family, as the table doc counts it");
        assert_eq!(
            family(Theories::WIDE_ARITH),
            46,
            "every row whose family carries the full LIA/LRA atom grammar"
        );
        // The ARRAY-SHAPE family: exactly the rows whose [S1] declaration
        // places no restriction on the array sort (`ALL` excluded, as above).
        assert_eq!(family(Theories::WIDE_ARRAY), 2, "`QF_AX` and `AUFNIRA`, and nothing else");
        assert_eq!(LOGIC_LATTICE.len(), 75, "the table's size is part of its doc");
        // Six rows are minimal (one dimension each), which is the tie the
        // table ORDER breaks for a Core-only query. (`QF_AX` was a seventh
        // until it took `WIDE_ARRAY`.)
        assert_eq!(LOGIC_LATTICE.iter().filter(|r| r.admits.len() == 1).count(), 6);

        // EVERY ARITHMETIC ROW CARRIES `WIDE_ARITH` EXCEPT THE TWO DIFFERENCE
        // ONES. This is the shape that makes the dimension sound: if a general
        // arithmetic row ever lost the bit, a wide query would select it and
        // the header would be narrower than the transcript. Stated as a
        // property over the rows rather than as a count, so a new row has to
        // satisfy it rather than move a number.
        for row in LOGIC_LATTICE {
            let arithmetic =
                row.admits.contains(Theories::INTS) || row.admits.contains(Theories::REALS);
            let wide = row.admits.contains(Theories::WIDE_ARITH);
            let difference = matches!(row.name, "QF_IDL" | "QF_RDL");
            assert_eq!(
                arithmetic && !difference,
                wide,
                "`{}` must carry WIDE_ARITH iff it names an arithmetic sort and is not a \
                 difference logic",
                row.name
            );
        }

        // LEVER A IS RE-POINTED: `QF_DT` names `{Datatypes}` exactly.
        assert_eq!(logic_admits("QF_DT"), Some(Theories::DATATYPES));
        assert!(is_named_exactly(Theories::DATATYPES));
        // The DIFFERENCE rows name their sets exactly, and the general rows
        // name the wide versions exactly.
        assert_eq!(logic_admits("QF_IDL"), Some(Theories::INTS));
        assert_eq!(logic_admits("QF_RDL"), Some(Theories::REALS));
        assert_eq!(
            logic_admits("QF_LIA"),
            Some(Theories::INTS.union(Theories::WIDE_ARITH)),
            "the general integer logic must admit the wide fragment its name promises"
        );

        // LEVER C: still no row admits bitvectors mixed with integers EXACTLY
        // — `QF_UFBVLIA` and `QF_AUFBVLIA` are the accepted names and both
        // promise UF, which is honest: SMT-LIB spells no `QF_BVLIA`.
        assert!(
            !is_named_exactly(Theories::BITVECTORS.union(Theories::INTS)),
            "SMT-LIB names no bare bitvector-with-integer logic"
        );
        assert_eq!(
            logic_admits("QF_UFBVLIA"),
            Some(
                Theories::UF
                    .union(Theories::BITVECTORS)
                    .union(Theories::INTS)
                    .union(Theories::WIDE_ARITH)
            )
        );

        // THE NAMES THIS TABLE REFUSES, and the ONLY reasons left after the
        // native lane's parser was retired as a criterion (2026-09-18):
        // `QF_ADT` and the `A`-leading `*DT*` names fail (C1)/(C2) — unattested,
        // or no declaration to cite for what their leading `A` admits — and
        // `QF_UFIDL`/`UFIDL` fail (C2), their declaration restricting TERMS in
        // a way `{UF, Ints}` does not record. The six `*BVLIA`/`*BVFPLRA`/
        // `*BVNIA` names that used to head this list are ROWS now: they were
        // refused ONLY because one consumer's parser refuses them, which is a
        // lane concern and is handled at the lane. Pinned as ABSENCES so a
        // future edit argues with the citation.
        for refused in [
            "QF_ADT",
            "QF_UFIDL",
            "UFIDL",
            "AUFDTLIA",
            "AUFDTLIRA",
            "AUFDTNIRA",
            "AUFBVDTLIA",
            "AUFBVDTNIA",
            "AUFBVDTNIRA",
            // The ARRAY-AND-REAL candidates, settled 2026-09-19: all four fail
            // (C1) against all three sources. See the rejection note, and
            // `the_array_and_real_gap_is_pinned_with_its_rejection` for what
            // their absence costs.
            "ALRA",
            "AUFLRA",
            "QF_AUFLRA",
            "QF_AUFLIRA",
        ] {
            assert_eq!(
                logic_admits(refused),
                None,
                "`{refused}` is on the rejection list and must not be emittable"
            );
        }
    }

    /// THE ARRAY-AND-REAL PRECISION GAP, PINNED WITH ITS REJECTION.
    ///
    /// An array-over-reals query that also applies an uninterpreted function,
    /// or mentions an integer, heads `AUFNIRA` — a name promising NONLINEARITY
    /// and INTEGERS it need not use. The four names that would close it —
    /// `ALRA`, `AUFLRA`, `QF_AUFLRA`, `QF_AUFLIRA` — were driven against all
    /// three sources on 2026-09-19 and NONE is attested by ANY of them, so the
    /// gap is SMT-LIB's and not this table's. The rejection note on
    /// [`LOGIC_LATTICE`] carries the citations; this test carries the
    /// consequences, so neither can drift from the other.
    ///
    /// WHAT IS PINNED, in the order that makes the pin mean something:
    ///
    /// 1. the four names are NOT emittable — [`logic_admits`] answers `None`;
    /// 2. the EXTENT of the gap — exactly 60 of the 512 array-and-real sets
    ///    head `AUFNIRA`: the 28 of the 256 without `WIDE_ARRAY` that carry
    ///    `UF`, `INTS` or `NONLINEAR`, plus all 32 unblocked sets WITH it,
    ///    since `AUFNIRA` is the only name short of `ALL` whose declaration
    ///    admits an arbitrary array sort. Adding a row would move this number,
    ///    so a future edit cannot land silently;
    /// 3. the sets that are ALREADY served precisely, so the residue is not
    ///    over-stated: an array-and-real set with neither `UF` nor `INTS` heads
    ///    `QF_ABVFPLRA` or `ABVFPLRA` at cardinality five or six, which Lever C
    ///    brought in;
    /// 4. that the gap costs PRECISION and not soundness — `AUFNIRA` admits
    ///    every set that selects it, which `every_feature_set_selects_an_
    ///    admitting_logic` already proves over the whole powerset and which is
    ///    re-stated here for these 28 specifically.
    ///
    /// THE ONE THING THIS TEST MAY NOT BE READ AS. The four names ARE accepted
    /// by ay's in-process `parse_logic` (they sit in
    /// `trust_router::in_process_ay_backend::NATIVE_LANE_LOGIC_VOCABULARY` as
    /// measured acceptances). That is not attestation — it is the retired
    /// criterion pointing the other way — and it is why the rejection is
    /// written against [S1]/[S2]/[S3] and nothing else.
    #[test]
    fn the_array_and_real_gap_is_pinned_with_its_rejection() {
        // (1) The four candidates are not rows, so none can reach a header.
        for candidate in ["ALRA", "AUFLRA", "QF_AUFLRA", "QF_AUFLIRA"] {
            assert_eq!(
                logic_admits(candidate),
                None,
                "`{candidate}` is attested by no source ([S1], [S2], [S3] all driven \
                 2026-09-19) and must not be emittable"
            );
        }

        let a = Theories::ARRAYS;
        let r = Theories::REALS;
        let uf = Theories::UF;
        let ints = Theories::INTS;

        // (2) THE EXTENT, and its exact characterization.
        let array_real: Vec<Theories> =
            powerset().into_iter().filter(|s| s.contains(a) && s.contains(r)).collect();
        assert_eq!(array_real.len(), 512, "the array-and-real corner of the powerset");
        let widened: Vec<Theories> =
            array_real.iter().copied().filter(|s| select_logic_name(*s) == "AUFNIRA").collect();
        assert_eq!(widened.len(), 60, "array-and-real sets heading `AUFNIRA`, of 512");

        // THE CHARACTERIZATION, derived rather than sampled. `AUFNIRA` admits
        // `{Nonlinear, Quantifiers, Arrays, WideArray, UF, Ints, Reals,
        // WideArith}`, so an array-and-real set heads it exactly when it
        // carries none of `BITVECTORS`/`FLOATS`/`DATATYPES` (which would take
        // it to `ALL`) AND either at least one of `UF`/`INTS`/`NONLINEAR`
        // (without one of those, the narrower `QF_ABVFPLRA`/`ABVFPLRA` rows
        // already admit it) or `WIDE_ARRAY` (which those two rows do not
        // admit). Free bits `Q`, `UF`, `I`, `NL`, `W` give 32 without the
        // array-shape bit, less the 4 that carry none of the three: 28; and
        // all 32 with it: 60.
        let nl = Theories::NONLINEAR;
        let wa = Theories::WIDE_ARRAY;
        for set in &array_real {
            let chosen = select_logic_name(*set);
            let blocked = set.contains(Theories::BITVECTORS)
                || set.contains(Theories::FLOATS)
                || set.contains(Theories::DATATYPES);
            let needs_a_seventh = set.contains(uf) || set.contains(ints) || set.contains(nl);
            assert_eq!(
                chosen == "AUFNIRA",
                !blocked && (needs_a_seventh || set.contains(wa)),
                "{set:?} heads `{chosen}` — the gap's characterization has moved"
            );
            // (4) PRECISION, NOT SOUNDNESS: whatever it heads admits it.
            assert!(
                set.is_subset_of(admits_of(chosen)),
                "{set:?} heads `{chosen}`, which does not admit it"
            );
        }

        // THE PRECISION COMPLAINT ITSELF, counted: of the 60, how many are
        // promised NONLINEARITY or INTEGERS they do not use. (The other 16
        // carry both already, so `AUFNIRA` over-states them in at most the
        // modifier dimensions, and exactly ONE of the 60 — the full
        // `{NL,Q,A,WA,UF,I,R,W}` — `AUFNIRA` names EXACTLY.)
        let overstated = widened.iter().filter(|s| !s.contains(nl) || !s.contains(ints)).count();
        assert_eq!(
            overstated, 44,
            "array-and-real sets headed by a name promising nonlinearity or integers they do \
             not use — the cost the four unattested `A*LRA` names would have removed"
        );
        assert_eq!(
            widened.iter().filter(|s| **s == admits_of("AUFNIRA")).count(),
            1,
            "`AUFNIRA` names exactly one of the 60 exactly; the other 59 it over-states"
        );

        // (3) The half that IS served precisely — neither UF nor INTS — so the
        // residue above is exactly the UF/INT half and not the whole corner.
        assert_eq!(select_logic_name(a.union(r)), "QF_ABVFPLRA");
        assert_eq!(select_logic_name(a.union(r).union(Theories::WIDE_ARITH)), "QF_ABVFPLRA");
        assert_eq!(select_logic_name(a.union(r).union(Theories::QUANTIFIERS)), "ABVFPLRA");
        // …and the half that is not.
        assert_eq!(select_logic_name(a.union(r).union(uf)), "AUFNIRA");
        assert_eq!(select_logic_name(a.union(r).union(uf).union(Theories::WIDE_ARITH)), "AUFNIRA");
        assert_eq!(
            select_logic_name(a.union(r).union(ints).union(Theories::WIDE_ARITH)),
            "AUFNIRA"
        );
        // …and the ARRAY-SHAPE half: an array-and-real set whose array is
        // neither declared shape has exactly one name short of `ALL`.
        assert_eq!(select_logic_name(a.union(r).union(wa)), "AUFNIRA");
        // `AUFNIRA` is cardinality 8 — the number that makes this a PRECISION
        // complaint rather than a correctness one.
        assert_eq!(admits_of("AUFNIRA").len(), 8);
    }

    /// The table is sorted by admitted cardinality, which is what makes
    /// `select_logic_name`'s first-minimum scan agree with table order.
    #[test]
    fn the_table_is_ordered_by_admitted_cardinality() {
        for pair in LOGIC_LATTICE.windows(2) {
            assert!(
                pair[0].admits.len() <= pair[1].admits.len(),
                "`{}` (admitting {} theories) must not precede `{}` (admitting {})",
                pair[0].name,
                pair[0].admits.len(),
                pair[1].name,
                pair[1].admits.len()
            );
        }
    }

    /// The specific shape M1 was reported as: floating point mixed with integer
    /// arithmetic must NOT answer `QF_FP`, because the transcript declares an
    /// `Int`-sorted variable beside the float.
    ///
    /// `{Floats, Ints}` still answers `ALL`, and after the SMT-LIB name audit
    /// that is a MEASURED answer rather than an unexamined one: every SMT-LIB
    /// name admitting both floats and integers (`QF_UFFPDTNIRA`, `UFFPDTNIRA`,
    /// `AUFFPDTNIRA`, `AUFBVFPDTNIRA`) also admits DATATYPES AND NONLINEARITY,
    /// so a row would re-point three dimensions at once to buy one — see the
    /// rejection list on [`LOGIC_LATTICE`]. Re-pointing Lever A did NOT reach
    /// this class, and this assertion is what says so.
    ///
    /// What DID change is the neighbouring mixes. `{Floats, Reals}` heads
    /// `QF_FPLRA` and `{Floats, BitVectors}` heads `QF_BVFP` — both real
    /// SMT-LIB names, both previously `ALL` for want of a row. `QF_BVFP` in
    /// particular is the fragment [`node_theories`]'s `FpConst` arm already
    /// pointed at: an FP literal lowers through a BITVECTOR literal, so every
    /// `FpConst`-bearing transcript carried both bits and was headed `ALL`.
    #[test]
    fn floating_point_mixed_with_integers_is_not_qf_fp() {
        let mixed = Theories::FLOATS.union(Theories::INTS);
        assert_eq!(select_logic_name(mixed), "ALL");
        assert_eq!(select_logic_name(mixed.union(Theories::WIDE_ARITH)), "ALL");
        assert_eq!(select_logic_name(Theories::FLOATS), "QF_FP");
        assert_eq!(select_logic_name(Theories::FLOATS.union(Theories::REALS)), "QF_FPLRA");
        assert_eq!(select_logic_name(Theories::FLOATS.union(Theories::BITVECTORS)), "QF_BVFP");
        // Still narrower than the content would be if integers joined in.
        assert_eq!(
            select_logic_name(Theories::FLOATS.union(Theories::BITVECTORS).union(Theories::INTS)),
            "ALL"
        );
    }

    /// The bottom and a few anchors, so a table edit that silently re-points a
    /// common case shows up here.
    #[test]
    fn the_common_anchors_are_pinned() {
        // A purely propositional query. Five rows admit `∅` besides `QF_UF`;
        // the tie is broken by table order, and `QF_UF` is deliberately first
        // because it is what every tool already writes for a Core-only query.
        assert_eq!(select_logic_name(Theories::NONE), "QF_UF");
        assert_eq!(select_logic_name(Theories::UF), "QF_UF");
        assert_eq!(select_logic_name(Theories::BITVECTORS), "QF_BV");
        // THE ARITHMETIC ANCHORS MOVED, AND THIS IS WHERE. `{Ints}` alone means
        // "an integer query every one of whose atoms is provably a difference
        // constraint", which is exactly `QF_IDL`; the ordinary case carries
        // `WIDE_ARITH` and is unchanged at `QF_LIA`. Same for the reals.
        // [`wide_arithmetic_theories`] is what decides which of the two a
        // formula presents, and it is conservative: it charges the bit unless
        // it can prove every atom is in the fragment.
        assert_eq!(select_logic_name(Theories::INTS), "QF_IDL");
        assert_eq!(select_logic_name(Theories::INTS.union(Theories::WIDE_ARITH)), "QF_LIA");
        assert_eq!(select_logic_name(Theories::REALS), "QF_RDL");
        assert_eq!(select_logic_name(Theories::REALS.union(Theories::WIDE_ARITH)), "QF_LRA");
        assert_eq!(select_logic_name(Theories::QUANTIFIERS.union(Theories::INTS)), "LIA");
        assert_eq!(select_logic_name(Theories::ARRAYS.union(Theories::INTS)), "QF_ALIA");
        assert_eq!(
            select_logic_name(Theories::UF.union(Theories::ARRAYS).union(Theories::INTS)),
            "QF_AUFLIA"
        );
        // `QF_AX` is the SMT-LIB name for arrays and nothing else, so `{Arrays}`
        // no longer has to borrow a base family (`QF_ABV`) to be named — and
        // since its declaration restricts the array sort not at all, it is the
        // name for an array of ANY shape with no base sort beside it.
        assert_eq!(select_logic_name(Theories::ARRAYS), "QF_AX");
        assert_eq!(select_logic_name(Theories::ARRAYS.union(Theories::WIDE_ARRAY)), "QF_AX");
        // An `(Array Int Int)` heads `QF_ALIA`; an `(Array Int Bool)` or a
        // nested array over integers does not — `QF_ALIA`'s family is
        // declared over `(Array Int Int)` only — and heads the least name whose
        // declaration admits an arbitrary array sort.
        assert_eq!(
            select_logic_name(
                Theories::ARRAYS
                    .union(Theories::WIDE_ARRAY)
                    .union(Theories::INTS)
                    .union(Theories::WIDE_ARITH)
            ),
            "AUFNIRA"
        );
        // `UF` is the SMT-LIB name for quantifiers over uninterpreted functions
        // and nothing else; it used to borrow `UFBV`.
        assert_eq!(select_logic_name(Theories::QUANTIFIERS.union(Theories::UF)), "UF");
        // LEVER A, RE-POINTED 2026-09-18: datatypes head their own SMT-LIB
        // names. `QF_DT` is the quantifier-free one. Every name reachable from
        // a datatype-bearing set contains `DT`, which is what keeps ay's
        // `parse_logic` routing (`contains("DT") -> Logic::All`) and
        // `in_process_ay_backend`'s datatype-program assertion both true.
        assert_eq!(select_logic_name(Theories::DATATYPES), "QF_DT");
        assert_eq!(select_logic_name(Theories::DATATYPES.union(Theories::UF)), "QF_UFDT");
        // …but an ARRAY-bearing datatype set still takes `ALL`: the `A`-leading
        // `DT` names have no [S1] declaration to cite for their array fragment,
        // and `AUFLIRA` is the standing proof that a leading `A` can be
        // restricted. See the note on [`LOGIC_LATTICE`].
        assert_eq!(select_logic_name(Theories::DATATYPES.union(Theories::ARRAYS)), "ALL");
        // LEVER C, SPLIT ON MEASUREMENT 2026-09-18. `{BitVectors, Ints}` moves
        // off `ALL` onto `QF_UFBVLIA`, the narrowest name ay's in-process lane
        // ACCEPTS for that mix — measured identical to `ALL` on every decided
        // query of a ten-query sweep. This is a DELIBERATE anchor change.
        assert_eq!(select_logic_name(Theories::BITVECTORS.union(Theories::INTS)), "QF_UFBVLIA");
        assert_eq!(
            select_logic_name(
                Theories::BITVECTORS.union(Theories::INTS).union(Theories::WIDE_ARITH)
            ),
            "QF_UFBVLIA"
        );
        assert_eq!(
            select_logic_name(
                Theories::ARRAYS
                    .union(Theories::BITVECTORS)
                    .union(Theories::INTS)
                    .union(Theories::WIDE_ARITH)
            ),
            "QF_AUFBVLIA"
        );
        // LEVER C, CLOSED 2026-09-18 — TWO DELIBERATE ANCHOR MOVES, and they
        // are the visible half of the six rows that came in when the native
        // lane's parser stopped being a table criterion.
        //
        // `{BitVectors, Reals}` MOVES OFF `ALL` onto `QF_BVFPLRA`. SMT-LIB
        // spells that mix only through the FP family, so this is its first
        // name; before the row it was `ALL` for want of any spelling this table
        // would carry.
        assert_eq!(select_logic_name(Theories::BITVECTORS.union(Theories::REALS)), "QF_BVFPLRA");
        // And a NONLINEAR bitvector-integer mix moves off `ALL` onto
        // `QF_AUFBVNIA`, `QF_AUFBVLIA`'s nonlinear sibling.
        assert_eq!(
            select_logic_name(
                Theories::BITVECTORS
                    .union(Theories::INTS)
                    .union(Theories::NONLINEAR)
                    .union(Theories::WIDE_ARITH)
            ),
            "QF_AUFBVNIA"
        );
        // WHAT THE NATIVE LANE SEES IS UNCHANGED BY BOTH MOVES, and that is
        // pinned where the narrowing lives:
        // `trust_router::in_process_ay_backend::native_lane_logic` selects from
        // the sublattice ay's in-process parser accepts, which neither new row
        // joins, so its header for these two sets is still `ALL`. A row this
        // table adds can move the TEXT header and nothing else.
    }

    /// A DATATYPE'S FIELD SORTS REACH THE LOGIC LINE.
    ///
    /// `declare-datatype` writes every constructor's field sort into the
    /// transcript, so the logic line has to admit every one of them. While
    /// Lever A routed all datatypes to `ALL` this was free — the top admits
    /// everything — and [`sort_theories`] stopped at [`Theories::DATATYPES`]
    /// with a comment saying why. Re-pointing Lever A made that reasoning
    /// false, and trust-router's transcript self-consistency fuzz caught the
    /// consequence at seed 4 of one run: `(set-logic QF_UFDTLIRA)` over
    /// `(declare-datatype Expr ((Const (ec (_ BitVec 32))) …))`, a bitvector
    /// sort under a logic that admits no bitvector theory.
    ///
    /// This test is the trust-types-side guard for that, so the regression has
    /// a pin at the source as well as at the fuzz.
    #[test]
    fn a_datatypes_field_sorts_reach_the_feature_record() {
        use crate::Sort;

        // A RECURSIVE definition: `App`'s fields are by-name back-edges, which
        // carry no constructors, so the recursion terminates on them.
        let by_name = Sort::Datatype { name: "Expr".into(), constructors: Vec::new() };
        let full = Sort::Datatype {
            name: "Expr".into(),
            constructors: vec![
                ("Const".to_string(), vec![("ec".to_string(), Sort::BitVec(32))]),
                (
                    "App".to_string(),
                    vec![("ef".to_string(), by_name.clone()), ("ex".to_string(), by_name.clone())],
                ),
            ],
        };

        // The BY-NAME spelling names no field at all.
        assert_eq!(sort_theories(&by_name), Theories::DATATYPES);
        assert_eq!(select_logic_name(sort_theories(&by_name)), "QF_DT");

        // The FULL spelling names a bitvector field, and the record must say
        // so — otherwise the transcript's own `declare-datatype` line writes a
        // sort its logic line does not admit.
        let full_record = sort_theories(&full);
        assert!(
            full_record.contains(Theories::BITVECTORS),
            "a `(_ BitVec 32)` field sort must reach the feature record"
        );
        assert_eq!(full_record, Theories::DATATYPES.union(Theories::BITVECTORS));
        assert_eq!(select_logic_name(full_record), "QF_UFBVDT");

        // A field at every other base sort reaches it too, and through an
        // ARRAY-sorted field as well — the two walks compose.
        let mixed = Sort::Datatype {
            name: "Mixed".into(),
            constructors: vec![(
                "Mk".to_string(),
                vec![
                    ("i".to_string(), Sort::Int),
                    ("r".to_string(), Sort::Real),
                    ("f".to_string(), Sort::Float { eb: 8, sb: 24 }),
                    ("m".to_string(), Sort::Array(Box::new(Sort::Int), Box::new(Sort::BitVec(8)))),
                ],
            )],
        };
        let record = sort_theories(&mixed);
        for bit in [
            Theories::DATATYPES,
            Theories::INTS,
            Theories::REALS,
            Theories::FLOATS,
            Theories::ARRAYS,
            Theories::BITVECTORS,
        ] {
            assert!(record.contains(bit), "every field sort's theory must reach the record");
        }
        // No name covers that, and `ALL` is the honest answer for it.
        assert_eq!(select_logic_name(record), "ALL");
    }

    /// THE LINEAR-FORM DIMENSION, pinned as BEHAVIOUR over real formulas.
    ///
    /// WHAT THE GAP WAS. `Theories` had no way to say "every arithmetic atom of
    /// this query is a difference constraint", so `QF_IDL` and `QF_RDL` — real
    /// SMT-LIB logics — could not be rows at all: a row claiming `QF_IDL`
    /// admits `{Ints}` would have let the selector head `x + y > 3` with a name
    /// admitting only `x - y ▷◁ n`, which is the over-narrow header this module
    /// exists to close, one dimension over from the `QF_FP`-over-an-`Int`
    /// defect and the `QF_LIA`-over-`x*y` one.
    ///
    /// WHY IT HAD TO BE A DIMENSION AND NOT A ROW: measured 2026-09-18, ay maps
    /// `QF_IDL` to its full `QfLia` solver and enforces no fragment
    /// restriction, so an over-narrow `(set-logic QF_IDL)` is decided correctly
    /// in-house, with a strict-verified proof where applicable, and nothing in
    /// the workspace would ever report it. Only an external replayer would.
    ///
    /// WHAT THIS TEST PINS: the exact boundary of [`is_difference_atom`], one
    /// assertion per shape, INCLUDING the shapes that surprise — `x > 3` is not
    /// an atom of either declaration, so an ordinary bounds check heads
    /// `QF_LIA`.
    #[test]
    fn the_difference_fragment_is_read_off_the_formula_conservatively() {
        use crate::Sort;
        use crate::smt_logic::select_logic;

        let x = || Formula::Var("x".to_string(), Sort::Int);
        let y = || Formula::Var("y".to_string(), Sort::Int);
        let lit = |n: i128| Formula::Int(n);
        let diff = |a: Formula, b: Formula| Formula::Sub(Box::new(a), Box::new(b));

        // IN THE FRAGMENT — the three atom shapes QF_IDL's declaration lists.
        let bounded_difference = Formula::Gt(Box::new(diff(x(), y())), Box::new(lit(3)));
        let negative_bound =
            Formula::Le(Box::new(diff(x(), y())), Box::new(Formula::Neg(Box::new(lit(3)))));
        let bare_comparison = Formula::Lt(Box::new(x()), Box::new(y()));
        let equality = Formula::Eq(Box::new(x()), Box::new(y()));
        // A 0-ARY `FnApp` is a free constant symbol too — `(declare-fun c () Int)`.
        let free_constant = |name: &str| Formula::FnApp {
            func: name.to_string(),
            args: Vec::new(),
            sort: Sort::Int,
        };
        let constant_difference =
            Formula::Ge(Box::new(diff(free_constant("c"), free_constant("d"))), Box::new(lit(0)));
        // A BOOLEAN COMBINATION of them is still in the fragment.
        let combination = Formula::And(vec![
            bounded_difference.clone(),
            Formula::Not(Box::new(bare_comparison.clone())),
        ]);
        for (label, formula) in [
            ("(> (- x y) 3)", &bounded_difference),
            ("(<= (- x y) (- 3))", &negative_bound),
            ("(< x y)", &bare_comparison),
            ("(= x y)", &equality),
            ("(>= (- c d) 0)", &constant_difference),
            ("a boolean combination of them", &combination),
        ] {
            let theories = formula_theories(formula);
            assert!(
                !theories.contains(Theories::WIDE_ARITH),
                "`{label}` is inside SMT-LIB's QF_IDL atom grammar, so the linear-form bit \
                 must NOT be charged"
            );
            assert_eq!(select_logic(formula), "QF_IDL", "`{label}` must head the difference logic");
        }

        // OUT OF THE FRAGMENT — every one of these charges the bit, and every
        // one of them heads the general linear logic instead.
        let sum =
            Formula::Gt(Box::new(Formula::Add(Box::new(x()), Box::new(y()))), Box::new(lit(3)));
        // NOT AN ATOM OF EITHER DECLARATION, however much the textbook gloss
        // says otherwise: neither QF_IDL nor QF_RDL lists `(op x n)`.
        let bare_bound = Formula::Gt(Box::new(x()), Box::new(lit(3)));
        // The MIRRORED difference. Semantically the same; textually not one of
        // the listed atoms, and a replayer checks the text.
        let mirrored = Formula::Lt(Box::new(lit(3)), Box::new(diff(x(), y())));
        // A difference of non-constants.
        let applied = Formula::Gt(
            Box::new(diff(
                Formula::FnApp { func: "f".to_string(), args: vec![x()], sort: Sort::Int },
                y(),
            )),
            Box::new(lit(3)),
        );
        // A difference against a non-numeral bound.
        let variable_bound = Formula::Gt(Box::new(diff(x(), y())), Box::new(x()));
        // One general atom anywhere in a conjunction of difference atoms is
        // enough — which is the UNION property doing its job at the atom level.
        let mixed = Formula::And(vec![bounded_difference.clone(), sum.clone()]);
        for (label, formula) in [
            ("(> (+ x y) 3)", &sum),
            ("(> x 3)", &bare_bound),
            ("(< 3 (- x y))", &mirrored),
            ("(> (- (f x) y) 3)", &applied),
            ("(> (- x y) x)", &variable_bound),
            ("a difference atom conjoined with a general one", &mixed),
        ] {
            let theories = formula_theories(formula);
            assert!(
                theories.contains(Theories::WIDE_ARITH),
                "`{label}` is NOT provably inside the difference grammar, so the linear-form \
                 bit must be charged — the conservative direction"
            );
            assert!(theories.contains(Theories::INTS), "`{label}` is an integer query");
        }
        assert_eq!(select_logic(&sum), "QF_LIA");
        assert_eq!(select_logic(&bare_bound), "QF_LIA");
        assert_eq!(select_logic(&mirrored), "QF_LIA");
        assert_eq!(select_logic(&variable_bound), "QF_LIA");
        assert_eq!(select_logic(&mixed), "QF_LIA");
        // The applied one drags UF in as well, so it heads the UF variant.
        assert_eq!(select_logic(&applied), "QF_UFLIA");

        // THE REAL SIDE. `QF_RDL`'s declaration is a DIFFERENT grammar, and the
        // difference that matters here is the BOUND: it must be `m` or `(- m)`
        // for a numeral `m`, and this contract spells a Real constant as a
        // `Formula::Rat`, which renders as an exact rational. So the bounded
        // real difference is NOT recognized — conservatively — and only the
        // bare comparison of two real constants reaches `QF_RDL`.
        let real = |name: &str| Formula::Var(name.to_string(), Sort::Real);
        let real_comparison = Formula::Lt(Box::new(real("p")), Box::new(real("q")));
        assert!(!formula_theories(&real_comparison).contains(Theories::WIDE_ARITH));
        assert_eq!(select_logic(&real_comparison), "QF_RDL");

        let rational_bound = Formula::Gt(
            Box::new(Formula::Sub(Box::new(real("p")), Box::new(real("q")))),
            Box::new(Formula::rat_from_int(3)),
        );
        assert!(
            formula_theories(&rational_bound).contains(Theories::WIDE_ARITH),
            "a `Rat` bound is not the numeral QF_RDL's declaration asks for, so the atom is \
             not recognized and the header widens"
        );
        assert_eq!(select_logic(&rational_bound), "QF_LRA");

        // A QUANTIFIER takes the query out of both difference logics, because
        // both are quantifier-free and neither row admits `QUANTIFIERS`. The
        // classifier still recurses into the body, so the bit itself stays
        // honest; it is the ROW that declines.
        let quantified = Formula::Forall(
            vec![(crate::Symbol::intern("z"), Sort::Int)],
            Box::new(bounded_difference.clone()),
        );
        assert!(!formula_theories(&quantified).contains(Theories::WIDE_ARITH));
        assert_eq!(select_logic(&quantified), "LIA");
    }

    /// THE LINEAR-FORM BIT CANNOT BE DERIVED NODE BY NODE, which is why it is
    /// computed separately and exported separately.
    ///
    /// `node_theories` classifies ONE node from its own content (plus, for the
    /// three arithmetic shapes, the shallow form of its operands). Difference
    /// shape is a property of a WHOLE ATOM: `(- x y)` is the same `Sub` node in
    /// `(> (- x y) 3)`, which is in the fragment, and in `(> (- x y) x)`, which
    /// is not. So no per-node rule can decide it, and a second record-builder
    /// that assembles `Theories` from `sort_theories` + `node_theories` alone —
    /// trust-router's `smt2_export::analyze_formula` is exactly that — would
    /// produce `{Ints}` for EVERY integer query and emit `QF_IDL` over general
    /// arithmetic.
    ///
    /// This test pins the two halves of that argument: `node_theories` never
    /// charges the bit, and [`wide_arithmetic_theories`] does. trust-router's
    /// `features_carry_the_linear_form_bit` pins the other lane.
    #[test]
    fn the_wide_bit_is_not_derivable_node_by_node() {
        use crate::Sort;

        let x = || Formula::Var("x".to_string(), Sort::Int);
        let y = || Formula::Var("y".to_string(), Sort::Int);
        let general = Formula::Gt(
            Box::new(Formula::Add(Box::new(x()), Box::new(y()))),
            Box::new(Formula::Int(3)),
        );

        // No node of a general arithmetic formula charges the bit…
        general.visit(&mut |node| {
            assert!(
                !node_theories(node).contains(Theories::WIDE_ARITH),
                "no per-node classification may charge the linear-form bit"
            );
        });
        // …and no node of ANY formula does, over the whole `Formula` vocabulary
        // the other tests in this module build.
        assert_eq!(wide_arithmetic_theories(&general), Theories::WIDE_ARITH);
        assert!(formula_theories(&general).contains(Theories::WIDE_ARITH));

        // The two `Sub`-bearing atoms that differ only in their BOUND, which is
        // the pair no node rule can tell apart.
        let in_fragment = Formula::Gt(
            Box::new(Formula::Sub(Box::new(x()), Box::new(y()))),
            Box::new(Formula::Int(3)),
        );
        let out_of_fragment =
            Formula::Gt(Box::new(Formula::Sub(Box::new(x()), Box::new(y()))), Box::new(x()));
        assert_eq!(wide_arithmetic_theories(&in_fragment), Theories::NONE);
        assert_eq!(wide_arithmetic_theories(&out_of_fragment), Theories::WIDE_ARITH);

        // A formula with NO arithmetic charges nothing, so a Core or bitvector
        // query is untouched by this dimension.
        let boolean = Formula::Not(Box::new(Formula::Var("b".to_string(), Sort::Bool)));
        assert_eq!(wide_arithmetic_theories(&boolean), Theories::NONE);
        let bitvector = Formula::BvULt(
            Box::new(Formula::Var("a".to_string(), Sort::BitVec(8))),
            Box::new(Formula::BitVec { value: 3, width: 8 }),
            8,
        );
        assert_eq!(wide_arithmetic_theories(&bitvector), Theories::NONE);
        assert_eq!(select_logic_name(formula_theories(&bitvector)), "QF_BV");
    }

    /// THE LINEARITY DIMENSION, pinned as behaviour rather than described in
    /// prose. THIS TEST IS THE INVERTED FORM OF A KNOWN-GAP TEST, kept in the
    /// same place so the regression it guards is the one that was actually
    /// there.
    ///
    /// WHAT THE GAP WAS. `Theories` had no LINEARITY dimension, so a NONLINEAR
    /// integer formula — `x * y > 0` over two `Int` variables — presented the
    /// feature set `{Ints}`, exactly as `x + y > 0` does, and headed `QF_LIA`:
    /// a logic whose SMT-LIB definition admits only linear terms. The
    /// transcript was therefore headed by a name NARROWER than its own
    /// `(assert …)` line, the same DEFECT CLASS as M1 (`QF_FP` over an `Int`
    /// declaration), one dimension over. `QF_LIA` is not a claim ay or z3
    /// enforces, so nothing mis-answered because of it; a strict replayer of
    /// the transcript was entitled to reject the evidence.
    ///
    /// WHAT CLOSED IT. A 9th bit ([`Theories::NONLINEAR`]), fourteen `N`-family
    /// rows, and the `Mul`/`Div`/`Rem` arms of [`node_theories`]. Both
    /// exhaustive proofs stayed exhaustive at the new size — and stayed so
    /// again when the 10th bit doubled it, at 1024 feature sets and 1_048_576
    /// ordered pairs.
    ///
    /// WHAT THIS TEST PINS, one assertion per shape that the classifier must
    /// keep apart. The linear/nonlinear split is not "is it a `Mul`": a product
    /// with a LITERAL operand is a linear term and must stay in `QF_LIA`, and
    /// getting that wrong would send a large share of ordinary VCs to `QF_NIA`
    /// for nothing.
    #[test]
    fn nonlinearity_is_visible_to_the_feature_record() {
        use crate::Sort;

        let x = || Formula::Var("x".to_string(), Sort::Int);
        let y = || Formula::Var("y".to_string(), Sort::Int);
        let gt_zero = |term: Formula| Formula::Gt(Box::new(term), Box::new(Formula::Int(0)));
        let logic_of = |f: &Formula| select_logic_name(formula_theories(f));

        // LINEAR: a sum, and the two `:extensions` product shapes — a concrete
        // coefficient times a FREE CONSTANT, on either side.
        let sum = gt_zero(Formula::Add(Box::new(x()), Box::new(y())));
        let scaled = gt_zero(Formula::Mul(Box::new(Formula::Int(3)), Box::new(x())));
        let scaled_right = gt_zero(Formula::Mul(Box::new(x()), Box::new(Formula::Int(3))));
        // A NEGATIVE coefficient is a coefficient: `(- n)` is in the list.
        let negated_scale =
            gt_zero(Formula::Mul(Box::new(Formula::Neg(Box::new(Formula::Int(3)))), Box::new(x())));
        let negative_literal_scale =
            gt_zero(Formula::Mul(Box::new(Formula::Int(-3)), Box::new(x())));
        // A `SymVar` renders as the same bare declared symbol a `Var` does.
        let sym_scaled = gt_zero(Formula::Mul(
            Box::new(Formula::Int(3)),
            Box::new(Formula::SymVar(crate::Symbol::intern("s"), Sort::Int)),
        ));
        for (label, formula) in [
            ("x + y", &sum),
            ("3 * x", &scaled),
            ("x * 3", &scaled_right),
            ("(-3) * x", &negated_scale),
            ("-3 * x", &negative_literal_scale),
            ("3 * s", &sym_scaled),
        ] {
            assert!(
                !formula_theories(formula).contains(Theories::NONLINEAR),
                "`{label}` is a LINEAR term and must not set the nonlinearity bit"
            );
            assert_eq!(logic_of(formula), "QF_LIA", "`{label}` must stay in the linear logic");
        }

        // NONLINEAR: a product of two non-literals; division and remainder by
        // ANYTHING (`QF_LIA`'s `:language` excludes `div`/`mod` by name, with
        // no numeral-divisor exception); and a coefficient times a COMPOUND
        // term, which is not `(* c x)` with `x` a free constant.
        let product = gt_zero(Formula::Mul(Box::new(x()), Box::new(y())));
        let quotient = gt_zero(Formula::Div(Box::new(x()), Box::new(y())));
        let remainder = gt_zero(Formula::Rem(Box::new(x()), Box::new(y())));
        let halved = gt_zero(Formula::Div(Box::new(x()), Box::new(Formula::Int(2))));
        let parity = gt_zero(Formula::Rem(Box::new(x()), Box::new(Formula::Int(2))));
        let scaled_sum = gt_zero(Formula::Mul(
            Box::new(Formula::Int(3)),
            Box::new(Formula::Add(Box::new(x()), Box::new(y()))),
        ));
        let scaled_negation =
            gt_zero(Formula::Mul(Box::new(Formula::Neg(Box::new(x()))), Box::new(Formula::Int(3))));
        // `Int(-3)` renders `(- 3)`, so negating it renders `(- (- 3))` — neither
        // `n` nor `(- n)`, so not a coefficient the declaration lists.
        let double_negation = gt_zero(Formula::Mul(
            Box::new(Formula::Neg(Box::new(Formula::Int(-3)))),
            Box::new(x()),
        ));
        for (label, formula) in [
            ("x * y", &product),
            ("(- (- 3)) * x", &double_negation),
            ("x div y", &quotient),
            ("x rem y", &remainder),
            ("x div 2", &halved),
            ("x rem 2", &parity),
            ("3 * (x + y)", &scaled_sum),
            ("(- x) * 3", &scaled_negation),
        ] {
            let theories = formula_theories(formula);
            assert!(
                theories.contains(Theories::NONLINEAR) && theories.contains(Theories::INTS),
                "`{label}` is outside the LINEAR integer fragment"
            );
            assert_eq!(
                logic_of(formula),
                "QF_NIA",
                "`{label}` must head the nonlinear integer logic, not `QF_LIA`"
            );
        }

        // A coefficient times an APPLIED uninterpreted function, and times an
        // array read: both compound, both nonlinear, and each carries its own
        // modifier into the `N` name.
        let f_of_x = || Formula::FnApp { func: "f".to_string(), args: vec![x()], sort: Sort::Int };
        let scaled_uf = gt_zero(Formula::Mul(Box::new(Formula::Int(3)), Box::new(f_of_x())));
        assert!(formula_theories(&scaled_uf).contains(Theories::NONLINEAR));
        assert_eq!(logic_of(&scaled_uf), "QF_UFNIA", "`3 * f(x)` is not `(* c x)`");
        let arr = || {
            Formula::Var("arr".to_string(), Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)))
        };
        let scaled_read = gt_zero(Formula::Mul(
            Box::new(Formula::Int(3)),
            Box::new(Formula::Select(Box::new(arr()), Box::new(x()))),
        ));
        assert!(formula_theories(&scaled_read).contains(Theories::NONLINEAR));
        assert_eq!(logic_of(&scaled_read), "QF_ANIA", "`3 * (select a i)` is not `(* c x)`");

        // The record now SEPARATES the two shapes that used to be identical.
        assert_ne!(
            formula_theories(&sum),
            formula_theories(&product),
            "the 9-bit record must tell `x + y` from `x * y` — that separation IS the fix"
        );
    }

    /// The REAL side of the linearity split, and the one shape `Div`/`Rem`
    /// cannot produce.
    ///
    /// `Mul` is sort-GENERIC (`smt_logic::infer_sort` propagates the operand
    /// sort), so a nonlinear REAL product is reachable and heads `QF_NRA`.
    /// `Div` and `Rem` are Int-ONLY in this contract — `infer_sort` returns
    /// `Sort::Int` unconditionally and `check_formula_sort` rejects `Real`
    /// operands — so `{NONLINEAR, REALS}` can arise from `Mul` and from nothing
    /// else.
    #[test]
    fn a_nonlinear_real_product_heads_the_nonlinear_real_logic() {
        use crate::Sort;

        let p = Formula::Var("p".to_string(), Sort::Real);
        let q = Formula::Var("q".to_string(), Sort::Real);
        let half = Formula::rat("1", "2").expect("1/2 is a well-formed rational literal");
        let zero = || Formula::rat_from_int(0);

        // `p * q > 0` — nonlinear reals.
        let product =
            Formula::Gt(Box::new(Formula::Mul(Box::new(p.clone()), Box::new(q))), Box::new(zero()));
        assert_eq!(
            formula_theories(&product),
            Theories::REALS.union(Theories::NONLINEAR).union(Theories::WIDE_ARITH),
            "a product of two Real variables is nonlinear real arithmetic, and a product is \
             not a difference atom, so the linear-form bit is charged too"
        );
        assert_eq!(select_logic_name(formula_theories(&product)), "QF_NRA");

        // `(1/2) * p > 0` — a RATIONAL COEFFICIENT, still linear: `QF_LRA`'s
        // `:extensions` list `(/ c n)`, which is how a `Rat` lowers. This is
        // the shape a shallow constant test that forgets `Rat` gets wrong.
        let scaled = Formula::Gt(
            Box::new(Formula::Mul(Box::new(half.clone()), Box::new(p.clone()))),
            Box::new(zero()),
        );
        assert!(
            !formula_theories(&scaled).contains(Theories::NONLINEAR),
            "multiplication by a rational COEFFICIENT is linear"
        );
        assert_eq!(select_logic_name(formula_theories(&scaled)), "QF_LRA");

        // `(- (1/2)) * p` — a NEGATED rational. `(- (/ 1 2))` is not one of the
        // listed coefficient forms (`d`, `(- d)`, `(/ c n)`), so it is not
        // folded and the product widens to `QF_NRA`. A negative `Rat` proper
        // lowers to `(/ (- 1) 2)`, which IS `(/ c n)`, and stays linear.
        let negated = Formula::Gt(
            Box::new(Formula::Mul(Box::new(Formula::Neg(Box::new(half))), Box::new(p.clone()))),
            Box::new(zero()),
        );
        assert!(formula_theories(&negated).contains(Theories::NONLINEAR));
        assert_eq!(select_logic_name(formula_theories(&negated)), "QF_NRA");
        let negative_rat = Formula::rat("-1", "2").expect("-1/2 is a well-formed rational literal");
        let negative_scaled = Formula::Gt(
            Box::new(Formula::Mul(Box::new(negative_rat), Box::new(p))),
            Box::new(zero()),
        );
        assert!(!formula_theories(&negative_scaled).contains(Theories::NONLINEAR));
        assert_eq!(select_logic_name(formula_theories(&negative_scaled)), "QF_LRA");
    }

    /// UNKNOWN RAW BITS FORCE `ALL` AND DROP NOTHING — over every `u16`, not
    /// only the enumerated powerset.
    ///
    /// A word carrying a bit above [`Theories::BIT_COUNT`] is a record this
    /// revision cannot read. Masking it would silently drop a demand and let a
    /// narrower header stand; passing it through would break ADMISSIBILITY on
    /// a value no enumeration covers. `from_bits` does neither: the result
    /// keeps every known bit the word carried, is inside the powerset, and
    /// selects `ALL`.
    #[test]
    fn unknown_raw_feature_bits_force_all_without_dropping_known_requirements() {
        let known_mask = Theories::EVERYTHING.bits();
        for raw in 0..=u16::MAX {
            let required = Theories::from_bits(raw);
            assert_eq!(required.bits() & !known_mask, 0, "{raw:#06x}: inside the powerset");
            assert!(
                required.contains(Theories::from_bits(raw & known_mask)),
                "{raw:#06x}: every known requirement is kept"
            );
            if raw & !known_mask != 0 {
                assert_eq!(
                    required,
                    Theories::EVERYTHING,
                    "{raw:#06x}: unknown bits force the top"
                );
                assert_eq!(select_logic_name(required), "ALL");
            } else {
                assert_eq!(required.bits(), raw, "{raw:#06x}: a known word is read exactly");
            }
        }
        assert_eq!(Theories::from_bits(1 << Theories::BIT_COUNT), Theories::EVERYTHING);
    }

    /// ARRAY SORTS ARE ADMITTED BY SHAPE, as the [S1] declarations write them:
    /// `(Array Int Int)` under the `*ALIA` names, `(Array (_ BitVec i)
    /// (_ BitVec j))` with `i, j > 0` under the `*ABV` names, and anything else
    /// only under a name whose declaration admits an ARBITRARY array sort.
    #[test]
    fn array_sorts_outside_the_declared_shapes_charge_the_wide_array_bit() {
        use crate::Sort;

        let int_int = Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int));
        let bv_bv = Sort::Array(Box::new(Sort::BitVec(8)), Box::new(Sort::BitVec(32)));
        for (label, sort, expected) in [
            ("(Array Int Int)", &int_int, "QF_ALIA"),
            ("(Array (_ BitVec 8) (_ BitVec 32))", &bv_bv, "QF_ABV"),
        ] {
            let theories = sort_theories(sort);
            assert!(!theories.contains(Theories::WIDE_ARRAY), "`{label}` is a declared shape");
            assert_eq!(select_logic_name(theories), expected, "`{label}`");
        }

        let wide: Vec<(&str, Sort, &str)> = vec![
            ("(Array Bool Bool)", Sort::Array(Box::new(Sort::Bool), Box::new(Sort::Bool)), "QF_AX"),
            ("(Array Int Bool)", Sort::Array(Box::new(Sort::Int), Box::new(Sort::Bool)), "AUFNIRA"),
            ("(Array Bool Int)", Sort::Array(Box::new(Sort::Bool), Box::new(Sort::Int)), "AUFNIRA"),
            ("(Array Int Real)", Sort::Array(Box::new(Sort::Int), Box::new(Sort::Real)), "AUFNIRA"),
            (
                "(Array Int (Array Int Int))",
                Sort::Array(Box::new(Sort::Int), Box::new(int_int.clone())),
                "AUFNIRA",
            ),
            (
                "(Array Int (_ BitVec 8))",
                Sort::Array(Box::new(Sort::Int), Box::new(Sort::BitVec(8))),
                "ALL",
            ),
            (
                "(Array (_ BitVec 8) Bool)",
                Sort::Array(Box::new(Sort::BitVec(8)), Box::new(Sort::Bool)),
                "ALL",
            ),
            (
                "(Array (_ BitVec 0) (_ BitVec 8))",
                Sort::Array(Box::new(Sort::BitVec(0)), Box::new(Sort::BitVec(8))),
                "ALL",
            ),
            (
                "(Array (_ BitVec 8) (_ FloatingPoint 8 24))",
                Sort::Array(Box::new(Sort::BitVec(8)), Box::new(Sort::Float { eb: 8, sb: 24 })),
                "ALL",
            ),
        ];
        for (label, sort, expected) in &wide {
            let theories = sort_theories(sort);
            assert!(
                theories.contains(Theories::WIDE_ARRAY),
                "`{label}` is outside both declared shapes and must charge WIDE_ARRAY"
            );
            assert!(theories.contains(Theories::ARRAYS));
            let chosen = select_logic_name(theories);
            assert_eq!(chosen, *expected, "`{label}`");
            assert!(
                admits_of(chosen).contains(Theories::WIDE_ARRAY),
                "`{label}` heads `{chosen}`, whose declaration restricts the array sort"
            );
        }

        // The rows that carry the bit are exactly the three whose [S1]
        // declarations place no restriction on the array sort.
        let wide_rows: Vec<&str> = LOGIC_LATTICE
            .iter()
            .filter(|r| r.admits.contains(Theories::WIDE_ARRAY))
            .map(|r| r.name)
            .collect();
        assert_eq!(wide_rows, ["QF_AX", "AUFNIRA", "ALL"]);
        // …and every other array row keeps plain `ARRAYS`, i.e. admits only
        // the two declared shapes.
        for row in LOGIC_LATTICE {
            if row.admits.contains(Theories::ARRAYS) && !wide_rows.contains(&row.name) {
                assert!(!row.admits.contains(Theories::WIDE_ARRAY), "`{}`", row.name);
            }
        }
        // The full record of a formula over a wide array carries the bit too,
        // through the shared sort-position walk.
        let bools = Formula::Eq(
            Box::new(Formula::Var("a".to_string(), wide[0].1.clone())),
            Box::new(Formula::Var("b".to_string(), wide[0].1.clone())),
        );
        assert!(formula_theories(&bools).contains(Theories::WIDE_ARRAY));
        assert_eq!(select_logic_name(formula_theories(&bools)), "QF_AX");
    }

    /// BITVECTOR AND FLOATING-POINT MULTIPLICATION ARE NOT "NONLINEAR".
    ///
    /// SMT-LIB spells linearity only into the arithmetic family names: `QF_BV`
    /// admits `bvmul` of two variables and `QF_FP` admits `fp.mul`,
    /// unconditionally, and there is no `QF_NBV`. Charging the bit on those
    /// nodes would push every bitvector multiply to `ALL`, so this test pins
    /// that it is not charged.
    #[test]
    fn bitvector_and_float_multiplication_carry_no_linearity_bit() {
        use crate::Sort;

        let a = || Formula::Var("a".to_string(), Sort::BitVec(8));
        let b = || Formula::Var("b".to_string(), Sort::BitVec(8));
        let bv_product = Formula::BvMul(Box::new(a()), Box::new(b()), 8);
        let theories = formula_theories(&bv_product);
        assert!(!theories.contains(Theories::NONLINEAR), "`bvmul` is not nonlinear arithmetic");
        assert_eq!(select_logic_name(theories), "QF_BV");

        let quotient = Formula::BvUDiv(Box::new(a()), Box::new(b()), 8);
        assert!(!formula_theories(&quotient).contains(Theories::NONLINEAR));
        let signed_rem = Formula::BvSRem(Box::new(a()), Box::new(b()), 8);
        assert!(!formula_theories(&signed_rem).contains(Theories::NONLINEAR));

        let f = Formula::Var("f".to_string(), Sort::Float { eb: 8, sb: 24 });
        let g = Formula::Var("g".to_string(), Sort::Float { eb: 8, sb: 24 });
        let fp_product = Formula::FpMul(
            Box::new(Formula::FpRoundingMode(crate::RoundingMode::RNE)),
            Box::new(f),
            Box::new(g),
        );
        assert!(
            !formula_theories(&fp_product).contains(Theories::NONLINEAR),
            "`fp.mul` is not nonlinear arithmetic"
        );
        assert_eq!(select_logic_name(formula_theories(&fp_product)), "QF_FP");
    }

    /// THE UF DIMENSION AT THE PUBLIC ENTRY POINT — item 2's regression guard.
    ///
    /// The exposure is that `trust_types::smt_logic::select_logic` is `pub` and
    /// re-exported from the crate root, so an EXTERNAL caller can hand it any
    /// formula and write the answer into a `(set-logic …)` line. If any public
    /// entry point could answer with a name that does not admit an APPLIED
    /// UNINTERPRETED SYMBOL, that transcript would declare
    /// `(declare-fun f (Int) Int)` under a logic with no UF.
    ///
    /// It cannot, and this test says so THROUGH THE PUBLIC FUNCTION rather than
    /// through the lattice: `node_theories` charges `Theories::UF` for every
    /// `Pred`/`FnApp` of arity >= 1, `formula_theories` visits every node
    /// including quantifier BODIES, and
    /// `every_feature_set_selects_an_admitting_logic` already proves over all
    /// 2048 sets that the chosen row admits everything required. What is left to
    /// pin is the composition, and the shapes where a walker could plausibly
    /// stop early.
    ///
    /// THE ONE DELIBERATE EXCLUSION, also pinned here: a 0-ary `Pred`/`FnApp`
    /// is an ordinary free constant, which every SMT-LIB logic admits, so it
    /// does NOT charge UF — the same arity rule trust-router's transcript
    /// checker charges `Req::Uf` by. Removing the guard would push every
    /// formula with a free `declare-fun` constant into a UF logic and break the
    /// paired checker.
    #[test]
    fn no_public_selection_answers_a_logic_that_refuses_applied_uf() {
        use crate::Sort;
        use crate::smt_logic::select_logic;

        let int_arg = || Formula::Var("n".to_string(), Sort::Int);
        let uf_term =
            || Formula::FnApp { func: "f".to_string(), args: vec![int_arg()], sort: Sort::Int };
        let uf_pred = || Formula::Pred(crate::Symbol::intern("p"), vec![int_arg()]);

        // Every shape that buries the application somewhere a prefix-reading
        // walker might not reach: an arithmetic operand, a quantifier BODY, an
        // array index, a nonlinear product, and a bare predicate.
        let shapes: Vec<(&str, Formula)> = vec![
            ("bare predicate", uf_pred()),
            (
                "arithmetic operand",
                Formula::Gt(
                    Box::new(Formula::Add(Box::new(uf_term()), Box::new(Formula::Int(1)))),
                    Box::new(Formula::Int(0)),
                ),
            ),
            (
                "quantifier body",
                Formula::Forall(vec![(crate::Symbol::intern("n"), Sort::Int)], Box::new(uf_pred())),
            ),
            (
                "array index",
                Formula::Eq(
                    Box::new(Formula::Select(
                        Box::new(Formula::Var(
                            "arr".to_string(),
                            Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)),
                        )),
                        Box::new(uf_term()),
                    )),
                    Box::new(Formula::Int(0)),
                ),
            ),
            (
                "nonlinear product",
                Formula::Gt(
                    Box::new(Formula::Mul(Box::new(uf_term()), Box::new(int_arg()))),
                    Box::new(Formula::Int(0)),
                ),
            ),
        ];

        for (label, formula) in &shapes {
            let theories = formula_theories(formula);
            assert!(
                theories.contains(Theories::UF),
                "`{label}` applies an uninterpreted symbol, so the record must carry UF"
            );
            // THE PUBLIC ANSWER, and the lattice answer, must both admit it.
            for (via, name) in [
                ("select_logic", select_logic(formula)),
                ("select_logic_name", { select_logic_name(theories) }),
            ] {
                let admits = admits_of(name);
                assert!(
                    admits.contains(Theories::UF),
                    "`{label}` via {via} answered `{name}`, which admits {admits:?} — a logic \
                     that does not admit an APPLIED uninterpreted symbol"
                );
            }
        }

        // The nonlinear shape additionally proves the two dimensions compose:
        // a UF-bearing nonlinear integer formula gets a name admitting BOTH.
        let (_, nonlinear_uf) = &shapes[4];
        assert_eq!(select_logic(nonlinear_uf), "QF_UFNIA");

        // A 0-ary application is NOT charged: `(declare-fun c () Int)` is a
        // free constant every logic admits, so `QF_LIA` over it is honest.
        let nullary = Formula::Gt(
            Box::new(Formula::FnApp { func: "c".to_string(), args: vec![], sort: Sort::Int }),
            Box::new(Formula::Int(0)),
        );
        assert!(!formula_theories(&nullary).contains(Theories::UF));
        assert_eq!(select_logic(&nullary), "QF_LIA");
    }
}
