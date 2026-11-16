//! TINV step 8 (increments 8a and 8b): candidate synthesis, the UNTRUSTED Houdini seed
//! (`docs/design/2026-10-04-type-invariant-tinv.md` §2 P3, §6 step 8).
//!
//! [`synthesize`] proposes, for one candidate struct `S`, a list of Int-sorted
//! conjuncts over the [`field_var`] placeholders of step 7.4. Houdini (step 7.6) and
//! `certify_vc` decide which survive, and step 9's non-vacuity gate checks a model of
//! the survivors with [`eval`] before anything is minted. NOTHING HERE IS AUTHORITY:
//! a wrong, missing or extra candidate can only cost precision, because every
//! surviving conjunct is proved at every E/C/R/U/M/Drop point before it is used.
//! The one output with a soundness role is the REFUSAL: an `S` value this module
//! cannot see being constructed ([`CandidateRefusal::ConstantConstruction`],
//! [`CandidateRefusal::Unresolved`]) would enter the program with no E point, so the
//! type is withheld rather than seeded.
//!
//! RECONCILED WITH 7.4. The step-8 plan proposed its own term, conjunct and
//! instantiation types. The landed vocabulary is reused instead:
//! * a conjunct is a [`CandidateConjunct`] whose formula reads only [`field_var`]
//!   placeholders, inside the language [`super::instantiate`] admits; the [`Template`]
//!   it came from is kept beside it for display and for the kernel-reach flag;
//! * terms are rendered by step 7.4's `Sigma` (`obligations::sigma_of_root` /
//!   `sigma_of_operands`): a Value term for an INTEGER field only, a Len term for a
//!   `Vec` (`Ty::Seq`, `guards::coll_len_var_place`) or a `&[T]`/`&str` field
//!   (`{name}__slice_len`). [`classify_field`] proposes a term exactly where `Sigma`
//!   renders one (a test pins the parity), so no candidate reads a term that can
//!   never be stated;
//! * there is no `BvToInt` lift: `super::instantiate` refuses a term that is not
//!   Int-sorted by its own shape, so a bit-vector-sorted field term makes its
//!   conjuncts unstatable (fail closed) rather than cast.
//!
//! G16: every template is over unbounded `Int`; the only arithmetic is `*` in
//! [`Template::LenEqProd`]. No template mentions a discriminant (`is_some`): the
//! discriminant variable is source-keyed and never re-versioned by a write to its
//! place, so an `is_some` term would be shared between the entry hypothesis and the
//! post-write goal (plan soundness risk 1). Those templates wait for increment 8e.

use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};

use trust_types::{
    AdtKind, AggregateKind, BinOp, BlockId, ConstValue, Formula, Operand, Place, PlaceWriteChannel,
    Projection, Rvalue, Statement, Terminator, Ty, TypeInvariantSite, VerifiableFunction,
};

use super::{CandidateConjunct, FieldTerm, TinvType, as_field_var, field_var};
use crate::local_defs;
use crate::place_write::{self, Reach, WriteFinding};

/// More enumerated candidates than this refuses the type (TINV-9(k)): Houdini's cost is
/// per conjunct per obligation point. Deterministic truncation would be as sound
/// (candidates are untrusted); refusing is the recorded choice.
pub const MAX_CONJUNCTS: usize = 512;

/// At most this many constants per Int field: the smallest half and the largest half.
pub const MAX_POOL_PER_FIELD: usize = 8;

/// Where a Len term's length lives.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LenCarrier {
    /// `Vec<T>` (`Ty::Seq`): the field's own Int-sorted name (`coll_len_var_place`).
    OwnedContainer,
    /// `&[T]` / `&str`: the fat pointer's `{name}__slice_len` twin.
    SliceRef,
}

/// How one field of `S` takes part in the templates.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FieldShape {
    /// An integer field: one Value term. `min`/`max` are the type's range; `max` is
    /// `None` only for `u128`, whose maximum exceeds `i128`.
    Int { min: i128, max: Option<i128> },
    /// A `bool` field. It has no term in v1: the only P3 templates over a bool are the
    /// `is_some` ones (increment 8e), and step 7.4's `Sigma` renders no bool term.
    Bool,
    /// A field with a length: one Len term.
    Len(LenCarrier),
    /// No term (an `Option`, a `String`, a nested struct, a float, ...).
    NoTerm,
}

impl FieldShape {
    /// The terms field `i` of this shape contributes.
    #[must_use]
    pub fn term(&self, i: usize) -> Option<FieldTerm> {
        match self {
            FieldShape::Int { .. } => Some(FieldTerm::Value(i)),
            FieldShape::Len(_) => Some(FieldTerm::Len(i)),
            FieldShape::Bool | FieldShape::NoTerm => None,
        }
    }
}

/// One P3 template instance. Field indices are MIR field indices of `S`; which term
/// each one reads (Value or Len) is fixed by the variant.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Template {
    /// `c <= f`.
    GeConst { f: usize, c: i128 },
    /// `f <= c`.
    LeConst { f: usize, c: i128 },
    /// `a < b` over two Int fields.
    Lt { a: usize, b: usize },
    /// `a <= b` over two Int fields.
    Le { a: usize, b: usize },
    /// `a <= len(g)`.
    LeLen { a: usize, g: usize },
    /// `len(f) == g * h`, `g <= h` by field index.
    LenEqProd { f: usize, g: usize, h: usize },
}

impl Template {
    /// The conjunct over [`field_var`] placeholders, in the language
    /// [`super::instantiate`] admits.
    #[must_use]
    pub fn formula(&self) -> Formula {
        let v = |i| Box::new(field_var(FieldTerm::Value(i)));
        let l = |i| Box::new(field_var(FieldTerm::Len(i)));
        let k = |c| Box::new(Formula::Int(c));
        match *self {
            Template::GeConst { f, c } => Formula::Le(k(c), v(f)),
            Template::LeConst { f, c } => Formula::Le(v(f), k(c)),
            Template::Lt { a, b } => Formula::Lt(v(a), v(b)),
            Template::Le { a, b } => Formula::Le(v(a), v(b)),
            Template::LeLen { a, g } => Formula::Le(v(a), l(g)),
            Template::LenEqProd { f, g, h } => {
                Formula::Eq(l(f), Box::new(Formula::Mul(v(g), v(h))))
            }
        }
    }

    /// Whether the Clean kernel can certify this shape's preservation today (design §9
    /// 0(b)): the linear templates yes; `len == g*h` NO, because preserving it through
    /// a mutator needs product congruence (`g1 = g0 ∧ h1 = h0 ⇒ g1*h1 = g0*h0`), which
    /// the kernel lane does not prove. It is still generated (decision TINV-9(l)): it is
    /// expected to die at P5 under TINV-2 and to survive only if a congruence
    /// recognizer lands. Informational; Houdini and `certify_vc` decide.
    #[must_use]
    pub fn kernel_certifiable_today(&self) -> bool {
        !matches!(self, Template::LenEqProd { .. })
    }

    /// Source-level rendering with the field names of `fields`.
    #[must_use]
    pub fn display(&self, fields: &[(String, Ty)]) -> String {
        let n = |i: usize| fields.get(i).map_or_else(|| format!("#{i}"), |(name, _)| name.clone());
        match *self {
            Template::GeConst { f, c } => format!("{c} <= {}", n(f)),
            Template::LeConst { f, c } => format!("{} <= {c}", n(f)),
            Template::Lt { a, b } => format!("{} < {}", n(a), n(b)),
            Template::Le { a, b } => format!("{} <= {}", n(a), n(b)),
            Template::LeLen { a, g } => format!("{} <= len({})", n(a), n(g)),
            Template::LenEqProd { f, g, h } => format!("len({}) == {} * {}", n(f), n(g), n(h)),
        }
    }
}

/// One `S` value: each term's integer value, indexed by field. `None` is unknown.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct FieldValuation {
    pub value: Vec<Option<i128>>,
    pub len: Vec<Option<i128>>,
}

impl FieldValuation {
    /// The value of `t`. A negative length is not a length, so it reads as unknown.
    #[must_use]
    pub fn get(&self, t: FieldTerm) -> Option<i128> {
        match t {
            FieldTerm::Value(i) => *self.value.get(i)?,
            FieldTerm::Len(i) => self.len.get(i).copied().flatten().filter(|l| *l >= 0),
        }
    }

    /// Whether every term `shapes` defines has a value within its type's range (a
    /// length is `>= 0`). Step 9's non-vacuity gate accepts only such a valuation.
    #[must_use]
    pub fn is_complete_and_in_range(&self, shapes: &[FieldShape]) -> bool {
        shapes.iter().enumerate().all(|(i, shape)| match shape {
            FieldShape::Int { min, max } => self
                .value
                .get(i)
                .copied()
                .flatten()
                .is_some_and(|v| v >= *min && max.is_none_or(|m| v <= m)),
            FieldShape::Len(_) => self.get(FieldTerm::Len(i)).is_some(),
            FieldShape::Bool | FieldShape::NoTerm => true,
        })
    }
}

/// Recursion bound for [`eval`]; deeper formulas evaluate to `None`.
const EVAL_DEPTH: usize = 256;

#[derive(Clone, Copy)]
enum Val {
    I(i128),
    B(bool),
}

/// Exact evaluation of a conjunct at one valuation, over unbounded `Int` computed with
/// checked `i128`. `None` — never `Some(true)` — on overflow, on a missing or
/// non-placeholder variable, on an ill-sorted node, on any node outside the admitted
/// template language, and past [`EVAL_DEPTH`]. Connectives are three-valued: `And`
/// is `false` as soon as one conjunct is `false` (that holds whatever the unknown ones
/// are), `true` only if all are `true`.
#[must_use]
pub fn eval(f: &Formula, v: &FieldValuation) -> Option<bool> {
    match eval_at(f, v, 0)? {
        Val::B(b) => Some(b),
        Val::I(_) => None,
    }
}

fn eval_at(f: &Formula, v: &FieldValuation, depth: usize) -> Option<Val> {
    if depth > EVAL_DEPTH {
        return None;
    }
    let d = depth + 1;
    let int = |x: &Formula| match eval_at(x, v, d)? {
        Val::I(i) => Some(i),
        Val::B(_) => None,
    };
    Some(match f {
        Formula::Bool(b) => Val::B(*b),
        Formula::Int(i) => Val::I(*i),
        Formula::Var(..) => Val::I(v.get(as_field_var(f)?)?),
        Formula::Not(a) => match eval_at(a, v, d)? {
            Val::B(b) => Val::B(!b),
            Val::I(_) => return None,
        },
        Formula::Neg(a) => Val::I(int(a)?.checked_neg()?),
        Formula::And(kids) | Formula::Or(kids) => {
            let is_and = matches!(f, Formula::And(_));
            let mut saw_dominating = false;
            let mut all_some = true;
            for k in kids {
                match eval_at(k, v, d) {
                    Some(Val::B(b)) => {
                        if b == !is_and {
                            saw_dominating = true;
                        }
                    }
                    Some(Val::I(_)) => return None,
                    None => {
                        if !super::is_admitted_node(k) {
                            return None;
                        }
                        all_some = false;
                    }
                }
            }
            if saw_dominating {
                Val::B(!is_and)
            } else if all_some {
                Val::B(is_and)
            } else {
                return None;
            }
        }
        Formula::Implies(a, b) => {
            let lhs = match eval_at(a, v, d) {
                Some(Val::B(x)) => Some(!x),
                Some(Val::I(_)) => return None,
                None => {
                    if !super::is_admitted_node(a) {
                        return None;
                    }
                    None
                }
            };
            let rhs = match eval_at(b, v, d) {
                Some(Val::B(y)) => Some(y),
                Some(Val::I(_)) => return None,
                None => {
                    if !super::is_admitted_node(b) {
                        return None;
                    }
                    None
                }
            };
            if lhs == Some(true) || rhs == Some(true) {
                Val::B(true)
            } else if lhs.is_some() && rhs.is_some() {
                Val::B(false)
            } else {
                return None;
            }
        }
        Formula::Eq(a, b) => match (eval_at(a, v, d)?, eval_at(b, v, d)?) {
            (Val::I(x), Val::I(y)) => Val::B(x == y),
            (Val::B(x), Val::B(y)) => Val::B(x == y),
            _ => return None,
        },
        Formula::Lt(a, b) => Val::B(int(a)? < int(b)?),
        Formula::Le(a, b) => Val::B(int(a)? <= int(b)?),
        Formula::Gt(a, b) => Val::B(int(a)? > int(b)?),
        Formula::Ge(a, b) => Val::B(int(a)? >= int(b)?),
        Formula::Add(a, b) => Val::I(int(a)?.checked_add(int(b)?)?),
        Formula::Sub(a, b) => Val::I(int(a)?.checked_sub(int(b)?)?),
        Formula::Mul(a, b) => Val::I(int(a)?.checked_mul(int(b)?)?),
        Formula::Ite(c, t, e) => match eval_at(c, v, d)? {
            Val::B(true) => eval_at(t, v, d)?,
            Val::B(false) => eval_at(e, v, d)?,
            Val::I(_) => return None,
        },
        _ => return None,
    })
}

/// One `Rvalue::Aggregate(Adt S)` — an E point step 7 owes.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConstructionSite {
    /// The constructing body's `def_path`.
    pub function: String,
    pub site: TypeInvariantSite,
    pub dest: Place,
}

/// The candidate seed of one type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CandidateSet {
    /// `def_path` is the aggregate name (crate-qualified, the key step 9 must mint
    /// `VcKind::TypeInvariant.ty` from); `fields` are the constructed type's fields;
    /// `conjuncts` are the pre-filtered candidates with ids `0..n` in enumeration
    /// order.
    pub ty: TinvType,
    /// Parallel to `ty.fields`.
    pub shapes: Vec<FieldShape>,
    /// Parallel to `ty.conjuncts`: the template each conjunct is an instance of.
    pub templates: Vec<Template>,
    /// Every construction site, sorted by (function, block, statement).
    pub sites: Vec<ConstructionSite>,
    /// Sites whose every term is a known in-range constant, with that valuation. Every
    /// conjunct in `ty.conjuncts` evaluates `Some(true)` on each (the pre-filter
    /// deleted the rest), so each is a non-vacuity model step 9 may check. Provenance
    /// does not matter to that gate: it needs a range-valid model, not a reachable one.
    pub const_witnesses: Vec<(ConstructionSite, FieldValuation)>,
    pub notes: Vec<String>,
}

/// Why no candidate set is produced. Every variant withholds the type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CandidateRefusal {
    /// No body of the inventory constructs `S` with an aggregate.
    NoConstructor,
    /// The aggregate's type is not a plain struct: an enum or union, a variant other
    /// than 0, an `active_field`, or a struct kind the extractor did not stamp.
    NotAStruct { function: String, site: TypeInvariantSite },
    /// Two constructions disagree on the field names or shapes, or an aggregate's
    /// operand count is not its field count.
    ShapeDisagrees { function: String },
    /// A construction this module cannot follow: the destination's type does not
    /// resolve to `S`, an `S`-typed place is assigned by an rvalue that is neither an
    /// aggregate nor a copy, or a statement/terminator whose operands are not listed.
    Unresolved { function: String, site: TypeInvariantSite },
    /// A constant that may hold an `S` value: it constructs `S` with no aggregate, so
    /// no E point would be owed (a `const` item or a GVN-folded literal). With
    /// `position_known: false` the constant is opaque and its position's type is not
    /// known (a call argument), so it is refused for what it may be.
    ConstantConstruction { function: String, site: TypeInvariantSite, position_known: bool },
    /// More than [`MAX_CONJUNCTS`] candidates were enumerated.
    TooManyConjuncts { count: usize },
}

// ---------------------------------------------------------------------------------------
// 8a: field shapes
// ---------------------------------------------------------------------------------------

/// The range of an integer type, or `None` for a non-integer.
fn int_range(ty: &Ty) -> Option<(i128, Option<i128>)> {
    let (width, signed) = match ty {
        Ty::Int { width, signed } => (*width, *signed),
        Ty::PtrSizedInt { signed } => (64, *signed),
        _ => return None,
    };
    if width == 0 || width > 128 {
        return None;
    }
    Some(if signed {
        let max = if width == 128 { i128::MAX } else { (1i128 << (width - 1)) - 1 };
        (-max - 1, Some(max))
    } else if width == 128 {
        (0, None)
    } else {
        (0, Some((1i128 << width) - 1))
    })
}

fn is_option(ty: &Ty) -> bool {
    matches!(ty, Ty::Adt { name, .. } if name.ends_with("::option::Option"))
}

/// The shape of a field of type `ty`, and a note when it gets no term.
///
/// Mirrors step 7.4's term rendering exactly (`obligations::value_term`/`len_term`):
/// Value for `Ty::Int`/`Ty::PtrSizedInt`; Len for `Ty::Seq` and for a reference to a
/// slice or `str`. A `String` or `VecDeque` has a length too (`guards.rs`'s
/// owned-container arms), but `Sigma` renders none for it, so it is `NoTerm` here.
#[must_use]
pub fn classify_field(name: &str, ty: &Ty) -> (FieldShape, Option<String>) {
    if let Some((min, max)) = int_range(ty) {
        return (FieldShape::Int { min, max }, None);
    }
    match ty {
        Ty::Bool => (
            FieldShape::Bool,
            Some(format!(
                "field `{name}`: bool, no term in v1 (its templates are the is_some ones, 8e)"
            )),
        ),
        Ty::Seq { .. } => (FieldShape::Len(LenCarrier::OwnedContainer), None),
        Ty::Ref { inner, .. } if matches!(inner.as_ref(), Ty::Slice { .. } | Ty::Str) => {
            (FieldShape::Len(LenCarrier::SliceRef), None)
        }
        _ if is_option(ty) => (
            FieldShape::NoTerm,
            Some(format!(
                "field `{name}`: Option, no term in v1: the discriminant variable is \
                 source-keyed and unversioned, so is_some/payload templates wait for 8e"
            )),
        ),
        _ => (FieldShape::NoTerm, Some(format!("field `{name}`: no term for this type"))),
    }
}

// ---------------------------------------------------------------------------------------
// 8b: construction sites and the constant refusal
// ---------------------------------------------------------------------------------------

/// A construction site with what the pool and the pre-filter read from it.
struct Scanned {
    site: ConstructionSite,
    fields: Vec<(String, Ty)>,
    ops: Vec<Operand>,
}

/// The type of the position an operand is used at.
enum Position<'a> {
    /// Known: judged by whether it reaches `S`.
    Known(Cow<'a, Ty>),
    /// Not known here (a call argument, a cast source, an unlisted operand).
    Unknown,
    /// A primitive operand (a comparison, arithmetic, a switch discriminant, an assert
    /// condition): MIR types it as a scalar, so it holds no `S`.
    Scalar,
}

fn is_s(ty: &Ty, name: &str) -> bool {
    matches!(ty, Ty::Adt { name: n, .. } | Ty::Datatype { name: n, .. } if n == name)
}

/// Whether a constant may hold an `S` value at `pos`. Scalars, strings, fn items,
/// payload-free variants and scalar-field structs other than `S` never do, except in a
/// position typed `S` (where any constant constructs one). Every other carrier (an
/// opaque constant, a memory image, a variant added later) is judged by its position
/// and refuses where that is unknown.
fn constant_may_hold_s(
    c: &ConstValue,
    pos: &Position<'_>,
    name: &str,
    defs: &trust_types::DatatypeDefs,
) -> bool {
    let reaches = |t: &Ty| place_write::type_reaches(t, name, defs) != Reach::No;
    let at_s_position = matches!(pos, Position::Known(t) if reaches(t));
    let scalar_class = match c {
        ConstValue::Bool(_)
        | ConstValue::Int(_)
        | ConstValue::Uint(..)
        | ConstValue::Float(_)
        | ConstValue::FloatBits { .. }
        | ConstValue::Unit
        | ConstValue::Str { .. }
        | ConstValue::OpaqueScalar { .. }
        | ConstValue::ConstParam { .. }
        | ConstValue::UnitVariantRef { .. }
        | ConstValue::EmptyClosureRef { .. }
        | ConstValue::CallableItem { .. } => true,
        // Trust: TINV — a nested struct constant of `S` holds an `S` too (the mint's
        // `constant_may_hold_s` already says so; synthesis read it as a scalar).
        ConstValue::StructScalarFieldsRef { adt_name, fields, .. } => {
            adt_name != name
                && !names_s(c, name)
                && fields.iter().all(|f| !constant_may_hold_s(f, &Position::Scalar, name, defs))
        }
        // The image's type is diagnostic data, so it may only REFUSE: a memory image is
        // otherwise judged by its position like any opaque constant.
        ConstValue::MemoryImage(image) if reaches(&image.ty) => return true,
        _ => false,
    };
    if scalar_class {
        return at_s_position;
    }
    match pos {
        Position::Known(t) => reaches(t),
        Position::Unknown => true,
        Position::Scalar => false,
    }
}

/// Decision TINV-32: whether `constants_clear` (the compiler's census evidence that no
/// constant of this body can hold `S`) may clear the constant `c` at `pos`. Never where
/// the extraction itself says the position or the constant reaches `S` (`Reach::Yes`):
/// MIR typing makes that a contradiction of the evidence, so the refusal stands.
fn constant_cleared(
    c: &ConstValue,
    pos: &Position<'_>,
    name: &str,
    defs: &trust_types::DatatypeDefs,
    constants_clear: bool,
) -> bool {
    let definitely = |t: &Ty| place_write::type_reaches(t, name, defs) == Reach::Yes;
    constants_clear
        && !matches!(pos, Position::Known(t) if definitely(t))
        && !matches!(c, ConstValue::MemoryImage(image) if definitely(&image.ty))
        && !names_s(c, name)
}

/// Whether the extraction itself types the constant `c` as (holding) an `S`: a
/// scalar-field struct constant of `S`, at any depth of its fields. TINV-32 evidence never
/// clears such a constant (it contradicts the evidence).
pub(crate) fn names_s(c: &ConstValue, name: &str) -> bool {
    match c {
        ConstValue::StructScalarFieldsRef { adt_name, fields, .. } => {
            adt_name == name || fields.iter().any(|f| names_s(f, name))
        }
        _ => false,
    }
}

/// TINV-32: the extractor lowers some NON-constant rvalues (a `Box<T> -> Box<dyn Trait>`
/// unsize, an exposed-provenance cast, a const-generic repeat) to
/// `Rvalue::Use(Operand::Constant(OpaqueConst))`. The census's evidence covers rustc
/// constants only, and nothing in the extraction tells such an operand apart from a
/// folded `_x = const C`, so the evidence never clears an `OpaqueConst` that is the whole
/// rvalue of an assignment.
pub(crate) fn may_be_invented_opaque(stmt: &Statement) -> bool {
    matches!(
        stmt,
        Statement::Assign {
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::OpaqueConst(_))),
            ..
        }
    )
}

fn check_operand(
    func: &VerifiableFunction,
    ty: &str,
    op: &Operand,
    pos: &Position<'_>,
    site: TypeInvariantSite,
    constants_clear: bool,
) -> Result<(), CandidateRefusal> {
    let defs = &func.body.datatype_defs;
    let hit = match op {
        Operand::Copy(_) | Operand::Move(_) => false,
        Operand::Constant(c) => {
            constant_may_hold_s(c, pos, ty, defs)
                && !constant_cleared(c, pos, ty, defs, constants_clear)
        }
        // A symbolic or unsupported operand is an opaque value, judged like an opaque
        // constant. The constant evidence never clears it (TINV-32): nothing here says it
        // came from a rustc constant.
        _ => match pos {
            Position::Known(t) => place_write::type_reaches(t, ty, defs) != Reach::No,
            Position::Unknown => true,
            Position::Scalar => false,
        },
    };
    if hit {
        return Err(CandidateRefusal::ConstantConstruction {
            function: func.def_path.clone(),
            site,
            position_known: !matches!(pos, Position::Unknown),
        });
    }
    Ok(())
}

/// The type of operand `i` of an aggregate into `dest`, when the destination's type
/// says it.
fn aggregate_operand_ty<'a>(
    dest_ty: Option<&'a Ty>,
    kind: &AggregateKind,
    i: usize,
) -> Option<&'a Ty> {
    match (dest_ty?, kind) {
        (Ty::Adt { fields, variants, .. }, AggregateKind::Adt { variant, active_field, .. }) => {
            if let Some(f) = active_field {
                return fields.get(*f).map(|(_, t)| t);
            }
            if variants.is_empty() {
                fields.get(i).map(|(_, t)| t)
            } else {
                variants.get(*variant)?.fields.get(i).map(|(_, t)| t)
            }
        }
        (Ty::Tuple(tys), AggregateKind::Tuple) => tys.get(i),
        (Ty::Array { elem, .. }, AggregateKind::Array) => Some(elem),
        (Ty::Closure { upvars, .. }, AggregateKind::Closure { .. }) => upvars.get(i),
        _ => None,
    }
}

fn site_at(block: BlockId, statement_index: usize) -> TypeInvariantSite {
    TypeInvariantSite { block: block.0, statement_index }
}

/// Every `S` aggregate of `func`, or the refusal. See [`construction_sites`].
/// `constants_clear` is the TINV-32 evidence for this body ([`constant_cleared`]).
fn scan(
    func: &VerifiableFunction,
    ty: &str,
    constants_clear: bool,
) -> Result<Vec<Scanned>, CandidateRefusal> {
    let func = func.with_tail_calls_expanded();
    let func = func.as_ref();
    let fname = || func.def_path.clone();
    let mut out = Vec::new();
    for block in &func.body.blocks {
        for (k, stmt) in block.stmts.iter().enumerate() {
            let at = site_at(block.id, k);
            let unresolved = || CandidateRefusal::Unresolved { function: fname(), site: at };
            let clear = constants_clear && !may_be_invented_opaque(stmt);
            match stmt {
                Statement::Assign { place, rvalue, .. } => {
                    let dest_ty = crate::place_ty_cow(func, place);
                    if let Rvalue::Aggregate(
                        kind @ AggregateKind::Adt { name, variant, active_field, .. },
                        ops,
                    ) = rvalue
                        && name == ty
                    {
                        if *variant != 0 || active_field.is_some() {
                            return Err(CandidateRefusal::NotAStruct {
                                function: fname(),
                                site: at,
                            });
                        }
                        let Some(Ty::Adt { name: dn, fields, variants, adt_kind, .. }) =
                            dest_ty.as_deref()
                        else {
                            return Err(unresolved());
                        };
                        if dn != ty {
                            return Err(unresolved());
                        }
                        if *adt_kind != Some(AdtKind::Struct) || !variants.is_empty() {
                            return Err(CandidateRefusal::NotAStruct {
                                function: fname(),
                                site: at,
                            });
                        }
                        if ops.len() != fields.len() {
                            return Err(CandidateRefusal::ShapeDisagrees { function: fname() });
                        }
                        for (i, op) in ops.iter().enumerate() {
                            let pos = aggregate_operand_ty(dest_ty.as_deref(), kind, i)
                                .map_or(Position::Unknown, |t| Position::Known(Cow::Borrowed(t)));
                            check_operand(func, ty, op, &pos, at, constants_clear)?;
                        }
                        out.push(Scanned {
                            site: ConstructionSite {
                                function: fname(),
                                site: at,
                                dest: place.clone(),
                            },
                            fields: fields.iter().cloned().collect(),
                            ops: ops.clone(),
                        });
                        continue;
                    }
                    // An `S`-typed place assigned by anything but an aggregate, a copy or a
                    // constant (judged below) is a construction this scan cannot see.
                    if dest_ty.as_deref().is_some_and(|t| is_s(t, ty))
                        && !matches!(rvalue, Rvalue::Use(_) | Rvalue::CopyForDeref(_))
                    {
                        return Err(unresolved());
                    }
                    fn known_pos(t: Option<&Ty>) -> Position<'_> {
                        t.map_or(Position::Unknown, |t| Position::Known(Cow::Borrowed(t)))
                    }
                    match rvalue {
                        Rvalue::Use(op) => {
                            check_operand(func, ty, op, &known_pos(dest_ty.as_deref()), at, clear)?;
                        }
                        Rvalue::Repeat(op, _) => {
                            let elem = match dest_ty.as_deref() {
                                Some(Ty::Array { elem, .. }) => Some(elem.as_ref()),
                                _ => None,
                            };
                            check_operand(func, ty, op, &known_pos(elem), at, clear)?;
                        }
                        Rvalue::Aggregate(kind, ops) => {
                            for (i, op) in ops.iter().enumerate() {
                                let pos =
                                    known_pos(aggregate_operand_ty(dest_ty.as_deref(), kind, i));
                                check_operand(func, ty, op, &pos, at, clear)?;
                            }
                        }
                        Rvalue::Cast(op, _) => {
                            check_operand(func, ty, op, &Position::Unknown, at, clear)?;
                        }
                        Rvalue::BinaryOp(_, a, b)
                        | Rvalue::CheckedBinaryOp(_, a, b)
                        | Rvalue::UncheckedBinaryOp(_, a, b) => {
                            check_operand(func, ty, a, &Position::Scalar, at, clear)?;
                            check_operand(func, ty, b, &Position::Scalar, at, clear)?;
                        }
                        Rvalue::UnaryOp(_, a) => {
                            check_operand(func, ty, a, &Position::Scalar, at, clear)?;
                        }
                        Rvalue::PtrOffset { ptr, count } => {
                            check_operand(func, ty, ptr, &Position::Scalar, at, clear)?;
                            check_operand(func, ty, count, &Position::Scalar, at, clear)?;
                        }
                        Rvalue::Unsupported { operands, .. } => {
                            for op in operands {
                                check_operand(func, ty, op, &Position::Unknown, at, clear)?;
                            }
                        }
                        Rvalue::Ref { .. }
                        | Rvalue::Discriminant(_)
                        | Rvalue::Len(_)
                        | Rvalue::AddressOf(..)
                        | Rvalue::CopyForDeref(_) => {}
                        _ => return Err(unresolved()),
                    }
                }
                Statement::Intrinsic { args, .. } => {
                    for op in args {
                        check_operand(func, ty, op, &Position::Unknown, at, clear)?;
                    }
                }
                Statement::CopyNonOverlapping { src, dst, count, .. } => {
                    check_operand(func, ty, src, &Position::Scalar, at, clear)?;
                    check_operand(func, ty, dst, &Position::Scalar, at, clear)?;
                    check_operand(func, ty, count, &Position::Scalar, at, clear)?;
                }
                Statement::Unsupported { operands, .. } => {
                    for op in operands {
                        check_operand(func, ty, op, &Position::Unknown, at, clear)?;
                    }
                }
                Statement::StorageLive(_)
                | Statement::StorageDead(_)
                | Statement::SetDiscriminant { .. }
                | Statement::Deinit { .. }
                | Statement::Retag { .. }
                | Statement::PlaceMention(_)
                | Statement::Coverage
                | Statement::ConstEvalCounter
                | Statement::Nop => {}
                _ => return Err(unresolved()),
            }
        }
        let at = site_at(block.id, block.stmts.len());
        match &block.terminator {
            Terminator::Call { args, .. } | Terminator::TailCall { args, .. } => {
                for op in args {
                    check_operand(func, ty, op, &Position::Unknown, at, constants_clear)?;
                }
            }
            Terminator::SwitchInt { discr, .. } => {
                check_operand(func, ty, discr, &Position::Scalar, at, constants_clear)?;
            }
            Terminator::Assert { cond, .. } => {
                check_operand(func, ty, cond, &Position::Scalar, at, constants_clear)?;
            }
            Terminator::Goto(_)
            | Terminator::Return
            | Terminator::Drop { .. }
            | Terminator::Unreachable
            | Terminator::Resume => {}
            _ => return Err(CandidateRefusal::Unresolved { function: fname(), site: at }),
        }
    }
    Ok(out)
}

/// Every construction of `ty` (the aggregate name, crate-qualified) in `func`: each
/// `Rvalue::Aggregate(Adt ty)` — a constructor, a derived `Clone`/`Default` body, a
/// ctor shim, a `const` body; no kind of body is filtered. Refuses when `func` may
/// construct `ty` some other way ([`CandidateRefusal`]).
pub fn construction_sites(
    func: &VerifiableFunction,
    ty: &str,
) -> Result<Vec<ConstructionSite>, CandidateRefusal> {
    Ok(scan(func, ty, false)?.into_iter().map(|s| s.site).collect())
}

// ---------------------------------------------------------------------------------------
// 8b: the constant pool
// ---------------------------------------------------------------------------------------

/// What an integer operand is known to be.
enum IntSource<'a> {
    Const(i128),
    /// The value of one of these calls (a local's every defining call).
    Calls(Vec<&'a Terminator>),
    Other,
}

/// A literal, or a whole local with ONE value definition that is a literal, or a
/// whole local defined only by calls (`local_defs`, the seam every def question goes
/// through).
fn int_const(func: &VerifiableFunction, op: &Operand) -> Option<i128> {
    if let Some(c) = crate::generate::operand_const_int(op) {
        return Some(c);
    }
    let (Operand::Copy(p) | Operand::Move(p)) = op else { return None };
    if !p.projections.is_empty() {
        return None;
    }
    let Some(Rvalue::Use(inner)) = local_defs::unique_value_def(func, p.local) else {
        return None;
    };
    crate::generate::operand_const_int(inner)
}

fn int_source<'a>(func: &'a VerifiableFunction, op: &Operand) -> IntSource<'a> {
    if let Some(c) = int_const(func, op) {
        return IntSource::Const(c);
    }
    let (Operand::Copy(p) | Operand::Move(p)) = op else { return IntSource::Other };
    if !p.projections.is_empty()
        || local_defs::is_parameter(func, p.local)
        || !crate::generate::terminator_presence_for(func).has_bare_dest_call
    {
        return IntSource::Other;
    }
    match local_defs::value_calls(func, p.local) {
        Some(calls) if !calls.is_empty() => IntSource::Calls(calls),
        _ => IntSource::Other,
    }
}

/// The constants a primitive-integer `min`/`max`/`clamp` call contributes. Gated by
/// `primitive_int_ord_method` (NAME-ANCHOR-2): a user `Ord` impl contributes nothing.
/// `clamp` contributes `lo` and `hi` only when both are constants with `lo <= hi`
/// (otherwise the call panics and bounds nothing).
fn ord_constants(func: &VerifiableFunction, call: &Terminator) -> Vec<i128> {
    let Terminator::Call { func: callee, args, dest, .. } = call else { return Vec::new() };
    match crate::generate::primitive_int_ord_method(func, callee, args, dest) {
        Some("clamp") if args.len() == 3 => {
            match (int_const(func, &args[1]), int_const(func, &args[2])) {
                (Some(lo), Some(hi)) if lo <= hi => vec![lo, hi],
                _ => Vec::new(),
            }
        }
        Some("min" | "max") => args.iter().filter_map(|a| int_const(func, a)).collect(),
        _ => Vec::new(),
    }
}

/// Whether `call` is a primitive integer's `Default::default()` (the value `0`). Used
/// only for pre-filter valuations: a misrecognition deletes a candidate (precision) or
/// yields a range-valid model (all the non-vacuity gate needs), never a proof.
fn is_int_default_call(func: &VerifiableFunction, call: &Terminator) -> bool {
    let Terminator::Call { func: callee, args, dest, .. } = call else { return false };
    args.is_empty()
        && (callee.ends_with(" as core::default::Default>::default")
            || callee.ends_with(" as std::default::Default>::default"))
        && crate::place_ty_cow(func, dest).is_some_and(|t| int_range(&t).is_some())
}

/// The constants an operand that fills an Int field contributes to its pool.
fn source_constants(func: &VerifiableFunction, op: &Operand, out: &mut BTreeSet<i128>) {
    match int_source(func, op) {
        IntSource::Const(c) => {
            out.insert(c);
        }
        IntSource::Calls(calls) => {
            for call in calls {
                out.extend(ord_constants(func, call));
            }
        }
        IntSource::Other => {}
    }
}

/// The value an operand that fills an Int field is known to have, for a valuation.
fn known_value(func: &VerifiableFunction, op: &Operand) -> Option<i128> {
    match int_source(func, op) {
        IntSource::Const(c) => Some(c),
        IntSource::Calls(calls) if calls.iter().all(|c| is_int_default_call(func, c)) => Some(0),
        _ => None,
    }
}

/// The field of `S` an operand reads: `copy (p).i` with `p` of type `S`, or a whole
/// local whose one value definition is such a read.
fn reads_field(func: &VerifiableFunction, op: &Operand, ty: &str) -> Option<usize> {
    let (Operand::Copy(p) | Operand::Move(p)) = op else { return None };
    let direct = |p: &Place| {
        let (Projection::Field(i), parent) = p.projections.split_last()? else { return None };
        crate::place_prefix_ty_cow(func, p.local, parent)
            .is_some_and(|t| is_s(&t, ty))
            .then_some(*i)
    };
    if let Some(i) = direct(p) {
        return Some(i);
    }
    if !p.projections.is_empty() {
        return None;
    }
    match local_defs::unique_value_def(func, p.local)? {
        Rvalue::Use(Operand::Copy(q) | Operand::Move(q)) | Rvalue::CopyForDeref(q) => direct(q),
        _ => None,
    }
}

/// The constant pool of every Int field (BTreeSets: the order never depends on the
/// inventory's order). Sources: (a) the site operands' literals and (b) their
/// `clamp`/`min`/`max` constants; (c) the same for every plain store into the field;
/// (d) `c - 1, c, c + 1` for every comparison of the field with a constant `c`;
/// (e) `0` and `1`. Out-of-range values are dropped; above [`MAX_POOL_PER_FIELD`]
/// the smallest and largest halves are kept, with a note.
fn constant_pools(
    inventory: &[&VerifiableFunction],
    ty: &str,
    scanned: &[(usize, Scanned)],
    shapes: &[FieldShape],
    fields: &[(String, Ty)],
    notes: &mut Vec<String>,
) -> Vec<BTreeSet<i128>> {
    let mut pools: Vec<BTreeSet<i128>> = vec![BTreeSet::new(); shapes.len()];
    let is_int = |i: usize| matches!(shapes.get(i), Some(FieldShape::Int { .. }));
    if !(0..shapes.len()).any(is_int) {
        return pools;
    }
    for (i, pool) in pools.iter_mut().enumerate() {
        if is_int(i) {
            pool.extend([0, 1]);
        }
    }
    // (a), (b): site operands.
    for (fi, s) in scanned {
        let func = inventory[*fi];
        for (i, op) in s.ops.iter().enumerate() {
            if is_int(i) {
                source_constants(func, op, &mut pools[i]);
            }
        }
    }
    for func in inventory {
        let func = func.with_tail_calls_expanded();
        let func = func.as_ref();
        let _scope = crate::generate::EntryScope::enter(func);
        // (c): stores into a field of `S`.
        let has_candidate_field_store = func.body.blocks.iter().any(|b| {
            b.stmts.iter().any(|s| {
                matches!(
                    s,
                    Statement::Assign { place, rvalue: Rvalue::Use(_), .. }
                        if matches!(place.projections.last(), Some(Projection::Field(f)) if is_int(*f))
                )
            }) || matches!(
                &b.terminator,
                Terminator::Call { dest, .. }
                    if matches!(dest.projections.last(), Some(Projection::Field(f)) if is_int(*f))
            )
        });
        if has_candidate_field_store {
            for finding in place_write::classify_writes_expanded(func) {
                let WriteFinding::Field {
                    adt, field, owner, channel, site, element_only: false, ..
                } = &finding
                else {
                    continue;
                };
                if adt != ty || !is_int(*field) {
                    continue;
                }
                let mut written = owner.clone();
                written.projections.push(Projection::Field(*field));
                let Some(block) = func
                    .body
                    .blocks
                    .get(site.block)
                    .filter(|b| b.id.0 == site.block)
                    .or_else(|| func.body.blocks.iter().find(|b| b.id.0 == site.block))
                else {
                    continue;
                };
                match (channel, block.stmts.get(site.statement_index)) {
                    (
                        PlaceWriteChannel::Store,
                        Some(Statement::Assign { place, rvalue: Rvalue::Use(op), .. }),
                    ) if *place == written => {
                        source_constants(func, op, &mut pools[*field]);
                    }
                    (PlaceWriteChannel::CallDest, None) => {
                        if let Terminator::Call { dest, .. } = &block.terminator
                            && *dest == written
                        {
                            pools[*field].extend(ord_constants(func, &block.terminator));
                        }
                    }
                    _ => {}
                }
            }
        }
        // (d): comparisons with a constant.
        for block in &func.body.blocks {
            for stmt in &block.stmts {
                let Statement::Assign { rvalue: Rvalue::BinaryOp(op, a, b), .. } = stmt else {
                    continue;
                };
                if !matches!(
                    op,
                    BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Eq | BinOp::Ne
                ) {
                    continue;
                }
                for (x, y) in [(a, b), (b, a)] {
                    // PERF-COMPILER-VCGEN-707: check `reads_field(func, x, ty)` and
                    // `is_int(i)` before `int_const(func, y)` so we only query
                    // `local_defs` on `y` when `x` actually reads an Int field of `S`.
                    if let Some(i) = reads_field(func, x, ty)
                        && is_int(i)
                        && let Some(c) = int_const(func, y)
                    {
                        pools[i].extend(
                            [c.checked_sub(1), Some(c), c.checked_add(1)].into_iter().flatten(),
                        );
                    }
                }
            }
        }
    }
    for (i, pool) in pools.iter_mut().enumerate() {
        let Some(FieldShape::Int { min, max }) = shapes.get(i) else { continue };
        pool.retain(|c| *c >= *min && max.is_none_or(|m| *c <= m));
        if pool.len() > MAX_POOL_PER_FIELD {
            let half = MAX_POOL_PER_FIELD / 2;
            let all: Vec<i128> = pool.iter().copied().collect();
            let kept: BTreeSet<i128> =
                all[..half].iter().chain(&all[all.len() - half..]).copied().collect();
            notes.push(format!(
                "field `{}`: {} constants, kept the {half} smallest and {half} largest",
                fields[i].0,
                all.len()
            ));
            *pool = kept;
        }
    }
    pools
}

// ---------------------------------------------------------------------------------------
// 8b: enumeration, pre-filter, synthesis
// ---------------------------------------------------------------------------------------

/// The P3 templates over `shapes` and `pools`, in a fixed order: per Int field (by
/// index) its constant bounds (by constant), skipping a bound the type already implies;
/// then `a < b` and `a <= b` over ordered pairs of distinct Int fields; then
/// `a <= len(g)`; then `len(f) == g*h` with `g <= h`.
fn enumerate(shapes: &[FieldShape], pools: &[BTreeSet<i128>]) -> Vec<Template> {
    let ints: Vec<usize> =
        (0..shapes.len()).filter(|i| matches!(shapes[*i], FieldShape::Int { .. })).collect();
    let lens: Vec<usize> =
        (0..shapes.len()).filter(|i| matches!(shapes[*i], FieldShape::Len(_))).collect();
    let mut out = Vec::new();
    for &f in &ints {
        let FieldShape::Int { min, max } = shapes[f] else { continue };
        for &c in &pools[f] {
            if c != min {
                out.push(Template::GeConst { f, c });
            }
            if max != Some(c) {
                out.push(Template::LeConst { f, c });
            }
        }
    }
    for &a in &ints {
        for &b in &ints {
            if a != b {
                out.push(Template::Lt { a, b });
                out.push(Template::Le { a, b });
            }
        }
    }
    for &a in &ints {
        for &g in &lens {
            out.push(Template::LeLen { a, g });
        }
    }
    for &f in &lens {
        for (gi, &g) in ints.iter().enumerate() {
            for &h in &ints[gi..] {
                out.push(Template::LenEqProd { f, g, h });
            }
        }
    }
    out
}

/// The valuation a construction site gives: an Int field whose operand is a known
/// in-range value, every other term unknown (no length is read off a site in v1).
fn site_valuation(func: &VerifiableFunction, s: &Scanned, shapes: &[FieldShape]) -> FieldValuation {
    let n = shapes.len();
    let mut v = FieldValuation { value: vec![None; n], len: vec![None; n] };
    for (i, (op, shape)) in s.ops.iter().zip(shapes).enumerate() {
        if let FieldShape::Int { min, max } = shape {
            v.value[i] =
                known_value(func, op).filter(|c| *c >= *min && max.is_none_or(|m| *c <= m));
        }
    }
    v
}

/// The candidate set of `ty` over the whole inventory (every body of the crate, P1).
///
/// Deterministic: bodies are visited in `(def_path, name)` order, pools are ordered
/// sets, the enumeration order is fixed, and sites are sorted; a permuted inventory
/// gives an equal result. The first refusal in that order is returned.
pub fn synthesize(
    ty: &str,
    inventory: &[VerifiableFunction],
) -> Result<CandidateSet, CandidateRefusal> {
    synthesize_with_constant_evidence(ty, inventory, &[])
}

/// [`synthesize`], with the compiler's per-body constant evidence (decision TINV-32):
/// `constants_clear[i]` says the census proved that no constant operand of
/// `inventory[i]` can hold `ty` (the union of its walk over every constant's rustc type
/// misses `ty`, and no constant kept a parameter, an alias or a `dyn`). Such a body's
/// opaque constants no longer refuse `ty`; a symbolic or unsupported operand still does.
/// A slice that is not parallel to `inventory` is no evidence at all.
pub fn synthesize_with_constant_evidence(
    ty: &str,
    inventory: &[VerifiableFunction],
    constants_clear: &[bool],
) -> Result<CandidateSet, CandidateRefusal> {
    let parallel = constants_clear.len() == inventory.len();
    let mut order: Vec<(&VerifiableFunction, bool)> =
        inventory.iter().enumerate().map(|(i, f)| (f, parallel && constants_clear[i])).collect();
    order.sort_by(|(a, _), (b, _)| (&a.def_path, &a.name).cmp(&(&b.def_path, &b.name)));

    let mut scanned: Vec<(usize, Scanned)> = Vec::new();
    for (fi, (func, clear)) in order.iter().enumerate() {
        scanned.extend(scan(func, ty, *clear)?.into_iter().map(|s| (fi, s)));
    }
    let order: Vec<&VerifiableFunction> = order.into_iter().map(|(f, _)| f).collect();
    scanned.sort_by(|(_, a), (_, b)| {
        (&a.site.function, a.site.site.block, a.site.site.statement_index)
            .cmp(&(&b.site.function, b.site.site.block, b.site.site.statement_index))
            .then_with(|| {
                if a.site.dest == b.site.dest {
                    std::cmp::Ordering::Equal
                } else {
                    format!("{:?}", a.site.dest).cmp(&format!("{:?}", b.site.dest))
                }
            })
    });
    let Some((_, first)) = scanned.first() else { return Err(CandidateRefusal::NoConstructor) };

    let fields = first.fields.clone();
    let mut notes = Vec::new();
    let mut shapes = Vec::with_capacity(fields.len());
    for (name, fty) in &fields {
        let (shape, note) = classify_field(name, fty);
        shapes.push(shape);
        notes.extend(note);
    }
    for (_, s) in scanned.iter().skip(1) {
        let agrees = s.fields.len() == fields.len()
            && s.fields.iter().zip(&fields).zip(&shapes).all(|(((n1, t1), (n2, t2)), s2)| {
                n1 == n2 && (t1 == t2 || classify_field(n1, t1).0 == *s2)
            });
        if !agrees {
            return Err(CandidateRefusal::ShapeDisagrees { function: s.site.function.clone() });
        }
    }

    let pools = constant_pools(&order, ty, &scanned, &shapes, &fields, &mut notes);
    let templates = enumerate(&shapes, &pools);
    if templates.len() > MAX_CONJUNCTS {
        return Err(CandidateRefusal::TooManyConjuncts { count: templates.len() });
    }

    // Delete-only pre-filter: a template false at a construction site can never be
    // established there.
    let valuations: Vec<FieldValuation> =
        scanned.iter().map(|(fi, s)| site_valuation(order[*fi], s, &shapes)).collect();
    let mut kept = Vec::with_capacity(templates.len());
    let mut conjuncts = Vec::with_capacity(templates.len());
    let mut deleted = 0usize;
    for t in templates {
        let f = t.formula();
        if valuations.iter().any(|v| eval(&f, v) == Some(false)) {
            deleted += 1;
        } else {
            let id = u32::try_from(conjuncts.len()).unwrap_or(u32::MAX);
            kept.push(t);
            conjuncts.push(CandidateConjunct { id, formula: f });
        }
    }
    if deleted > 0 {
        notes.push(format!("pre-filter: {deleted} candidates false at a construction site"));
    }
    if kept.iter().any(|t| !t.kernel_certifiable_today()) {
        notes.push(
            "len(f) == g * h: generated, but its preservation needs product congruence the \
             kernel does not certify today (design §9 0(b)); expected to die at P5"
                .into(),
        );
    }

    let const_witnesses = scanned
        .iter()
        .zip(&valuations)
        .filter(|(_, v)| v.is_complete_and_in_range(&shapes))
        .map(|((_, s), v)| (s.site.clone(), v.clone()))
        .collect();
    Ok(CandidateSet {
        ty: TinvType { def_path: ty.to_string(), fields, conjuncts },
        shapes,
        templates: kept,
        sites: scanned.into_iter().map(|(_, s)| s.site).collect(),
        const_witnesses,
        notes,
    })
}

/// The conjuncts of `set` by id, for display and diagnostics.
#[must_use]
pub fn describe(set: &CandidateSet) -> BTreeMap<u32, String> {
    set.ty
        .conjuncts
        .iter()
        .zip(&set.templates)
        .map(|(c, t)| (c.id, t.display(&set.ty.fields)))
        .collect()
}

#[cfg(test)]
#[path = "candidate_tests.rs"]
mod tests;
