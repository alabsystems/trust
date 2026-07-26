// Trust: SMT→CIC reconstruction for the GUARDED-CHECK class of safety VCs.
//
// The safety obligations Trust generates (bounds, overflow, div-by-zero) are
// LINEAR INTEGER ARITHMETIC: the type's range is carried as `Int` hypotheses
// (e.g. `0 ≤ x ≤ 4294967295` for `u32`), and the VC is discharged by proving the
// asserted conjunction UNSATISFIABLE. The most common discharge is a *guarded
// check*: the guard contributes `i < len` and the violation arm contributes
// `i ≥ len` (= `len ≤ i`) — a direct contradiction.
//
// This module reconstructs that discharge as a foundational kernel proof: from
// `a < b` and `b ≤ a`, `Int.lt_of_lt_of_le` yields `a < a`, which `Int.lt_irrefl`
// refutes — a proof of `False` resting only on constructive order lemmas (empty
// axiom closure ⇒ modulo 3). It is the proof core a full QF_LIA→CIC refutation
// producer (Farkas combinations) generalizes.

use clean_kernel::{
    BinderData, BinderInfo, Declaration, Environment, Expr, Level, LevelVec, Name, TypeChecker,
};

fn cst(s: &str) -> Expr {
    Expr::const_(Name::from_string(s), LevelVec::new())
}

fn int() -> Expr {
    cst("Int")
}

fn bd() -> BinderData {
    BinderData::from(BinderInfo::Default)
}

/// The refutation lemma type `Π(a b:Int). Int.lt a b → Int.le b a → False`.
pub fn lt_le_contradiction_type() -> Expr {
    // Under λa λb:           Int.lt a b   = lt #1 #0
    let h1 = Expr::apps(cst("Int.lt"), [Expr::bvar(1), Expr::bvar(0)]);
    // Under λa λb λh1:       Int.le b a   = le #1 #2
    let h2 = Expr::apps(cst("Int.le"), [Expr::bvar(1), Expr::bvar(2)]);
    Expr::pi(
        bd(),
        int(),
        Expr::pi(bd(), int(), Expr::pi(bd(), h1, Expr::pi(bd(), h2, cst("False")))),
    )
}

/// The refutation proof
/// `λa λb (h1:a<b) (h2:b≤a). Int.lt_irrefl a (Int.lt_of_lt_of_le a b a h1 h2)`.
pub fn lt_le_contradiction_proof() -> Expr {
    // Under λa λb λh1 λh2:  a=#3 b=#2 h1=#1 h2=#0
    let lt_aa = Expr::apps(
        cst("Int.lt_of_lt_of_le"),
        [Expr::bvar(3), Expr::bvar(2), Expr::bvar(3), Expr::bvar(1), Expr::bvar(0)],
    );
    let false_pf = Expr::apps(cst("Int.lt_irrefl"), [Expr::bvar(3), lt_aa]);
    let h1_ty = Expr::apps(cst("Int.lt"), [Expr::bvar(1), Expr::bvar(0)]);
    let h2_ty = Expr::apps(cst("Int.le"), [Expr::bvar(1), Expr::bvar(2)]);
    Expr::lam(
        bd(),
        int(),
        Expr::lam(bd(), int(), Expr::lam(bd(), h1_ty, Expr::lam(bd(), h2_ty, false_pf))),
    )
}

/// Outcome of reconstructing a safety VC's discharge as a kernel proof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RefuteOutcome {
    /// The VC's contradiction was reconstructed and kernel-checked modulo 3.
    RefutedModulo3,
    /// The kernel rejected the reconstruction, or it depends on non-foundational
    /// axioms (must stay empty for soundness).
    KernelRejected(String),
}

/// Build a fresh order-lemma environment (`with_prelude` + `init_int_ord_lemmas`).
fn env_with_order_lemmas() -> Result<Environment, String> {
    // Trust (perf): the order-lemma env is a fixed, VC-INDEPENDENT prelude that
    // was rebuilt (with_prelude + a full kernel re-typecheck of thousands of
    // decls) on EVERY refutation VC. Memoize it once behind a `OnceLock` and
    // hand out an `Arc`-backed CLONE (O(#decls) refcount copy, µs) — the same
    // proven pattern as `clean_bridge::certification_env`. Soundness is
    // unchanged: a clone is byte-identical to a fresh build and every real VC
    // term is still fully kernel-checked against it (callers clone-then-mutate a
    // local env, never the shared template).
    static MEMO: std::sync::OnceLock<Result<Environment, String>> = std::sync::OnceLock::new();
    MEMO.get_or_init(|| {
        let mut env = Environment::with_prelude();
        env.init_int_ord_lemmas().map_err(|e| format!("{e:?}"))?;
        Ok(env)
    })
    .clone()
}

/// Kernel-check the guarded-check refutation lemma and confirm its axiom closure
/// is ⊆ the 3 foundational axioms — i.e. the guarded bounds/overflow discharge is
/// a genuine modulo-3 proof.
pub fn check_lt_le_contradiction() -> RefuteOutcome {
    let env = match env_with_order_lemmas() {
        Ok(e) => e,
        Err(e) => return RefuteOutcome::KernelRejected(e),
    };
    let ty = lt_le_contradiction_type();
    let proof = lt_le_contradiction_proof();
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &ty) {
            return RefuteOutcome::KernelRejected(format!("check_type: {e:?}"));
        }
    }
    let mut env = env;
    let name = Name::from_string("Trust.Safety.guarded_check_refutation");
    if env
        .add_decl(Declaration::Definition {
            name: name.clone(),
            level_params: vec![],
            type_: ty,
            value: proof,
            is_reducible: false,
        })
        .is_err()
    {
        return RefuteOutcome::KernelRejected("add_decl".to_string());
    }
    match env.axiom_deps(&name) {
        Some(r) if r.is_empty() => RefuteOutcome::RefutedModulo3,
        Some(r) => RefuteOutcome::KernelRejected(format!("{} non-foundational axioms", r.len())),
        None => RefuteOutcome::KernelRejected("declaration not found".to_string()),
    }
}

// Silence unused-import warning when only some helpers are exercised.
const _: fn() -> Level = || Level::zero();

use std::collections::{HashMap, HashSet};

use trust_types::Formula;

use crate::clean_ground::ground_int;

/// The set of struct parameters whose fields ground STRUCTURALLY: each entry is
/// `(source_param_name, AdtCarrier)` for a struct that registered as a real named
/// inductive modulo 3 (see [`crate::clean_ground::register_adt_carriers`]). Built
/// from a function's locals (param name → `Ty::Adt`) intersected with the
/// registry, so only kernel-certified structs drive the recursion.
#[derive(Debug, Default, Clone)]
pub struct StructParams {
    by_param: HashMap<String, crate::reflect::AdtCarrier>,
    /// Registered enum parameters, including enums whose flattened/source view
    /// failed alias validation. Keeping this set separate prevents an enum's
    /// numeric MIR index from falling through to the struct/carrier index space.
    enum_params: HashSet<String>,
    /// Validated enum projection spellings (`.1`, `@0.0`, `.__v0_0`) mapped to
    /// their single flattened/source field name (`__v0_0`). Installed only when
    /// the complete flattened layout exactly agrees with every variant payload.
    enum_aliases_by_param: HashMap<String, HashMap<String, String>>,
}

impl StructParams {
    /// Whether `name` is a `<param>.<field>` reference to a registered struct
    /// param's NAMED integer field — i.e. it grounds STRUCTURALLY (a named
    /// projection of the real inductive), not as an opaque atom. A machine integer
    /// field (`Ty::Int`) reflects to the `Trust.Sort.BitVec w` carrier and a raw
    /// pointer to `Trust.Sort.Int`; both are integer operands. Bool / composite /
    /// generic fields are NOT integer operands, so they return false.
    pub fn is_struct_int_field(&self, name: &str) -> bool {
        // Canonicalize the field key first so BOTH the named form (`f.exponent`, as a
        // spec/precondition writes it) AND the MIR INDEX form (`f.1`, as the rvalue
        // extractor emits it) resolve to the same named field — exactly the
        // canonicalization the refutation engine applies. Falls back to the raw name.
        let canonical = self.canonical_field_name(name).unwrap_or_else(|| name.to_string());
        let Some((param, field)) = canonical.split_once('.') else { return false };
        let Some(carrier) = self.by_param.get(param) else { return false };
        // `AdtCarrier::fields` is only a deduplicated compatibility/union view for
        // enums. It cannot identify a payload projection: two variants may both
        // have a field named `0`. Enum arithmetic aliases are handled separately,
        // while structural enum grounding requires a variant-qualified recursor.
        if carrier.is_enum() {
            return false;
        }
        carrier
            .fields
            .iter()
            .find(|(n, _)| n == field)
            .is_some_and(|(_, code)| is_int_field_carrier(code))
    }

    /// GOAL-ITEM #1 — for a `<param>.<key>` reference to a registered struct param's
    /// NAMED integer field, the `(inductive_name, field_idx)` the field projects:
    /// the registered Clean inductive (`Trust.Adt.<Name>` / `Trust.FloatN`) and the
    /// 0-based field index. Resolves BOTH the named form (`p.x`) and the MIR INDEX
    /// form (`p.0`) to the same `(inductive, idx)`. Returns `None` if `name` is not a
    /// registered struct's named INT field (so the caller fails closed to opaque/Prod).
    /// This is what lets the depth metric certify the field grounds over the named
    /// projection in the real kernel ([`crate::clean_ground::field_grounds_structurally_modulo_3`]).
    #[must_use]
    pub fn struct_int_field_target(&self, name: &str) -> Option<(String, u32)> {
        let canonical = self.canonical_field_name(name).unwrap_or_else(|| name.to_string());
        let (param, field) = canonical.split_once('.')?;
        let carrier = self.by_param.get(param)?;
        if carrier.is_enum() {
            return None; // enum payloads require variant-qualified recursor access, not a struct proj
        }
        let (idx, (_, code)) = carrier.fields.iter().enumerate().find(|(_, (n, _))| n == field)?;
        // Only an INTEGER-operand field grounds structurally as an arithmetic operand;
        // Bool / composite / generic fields are not (they fail closed to opaque/Prod).
        if !is_int_field_carrier(code) {
            return None;
        }
        Some((carrier.name.clone(), u32::try_from(idx).ok()?))
    }

    /// Canonicalize a variable name `<param>.<key>` of a registered struct param
    /// to its NAMED field form. The MIR rvalue extractor names a struct field by
    /// its INDEX (`p.0`), while specs name it (`p.x`); for a registered struct we
    /// map the index to the named field so the two unify. A name that is already a
    /// valid named field, or that is not a `<param>.<key>` of a registered struct,
    /// is returned unchanged (sound — never invents a binding).
    fn canonical_field_name(&self, name: &str) -> Option<String> {
        // Enum projections have two MIR spellings: a flattened field index
        // (`e.1`, where slot 0 is `__tag`) and a downcast-relative field
        // (`e@0.0`). Specs use the flattened named spelling (`e.__v0_0`). Only a
        // completely validated layout installs aliases among those three forms.
        let enum_sep = name.find(|ch| ch == '.' || ch == '@');
        if let Some(split) = enum_sep {
            let (param, suffix) = name.split_at(split);
            if self.enum_params.contains(param) {
                let flattened = self.enum_aliases_by_param.get(param)?.get(suffix)?;
                return Some(format!("{param}.{flattened}"));
            }
        }

        let (param, key) = name.split_once('.')?;
        let carrier = self.by_param.get(param)?;
        // Even if a malformed/public parameter name prevented the enum-prefix
        // parser above from recognizing its boundary, never fall through to the
        // enum carrier's union-field index space.
        if carrier.is_enum() {
            return None;
        }
        // Already a named field → unchanged.
        if carrier.fields.iter().any(|(n, _)| n == key) {
            return Some(name.to_string());
        }
        // Numeric index → the named struct/float field at that index. Enums have
        // already returned through the separately validated source-layout map.
        let idx: usize = key.parse().ok()?;
        let (fname, _) = carrier.fields.get(idx)?;
        Some(format!("{param}.{fname}"))
    }

    /// Whether `name` is the bare aggregate of a registered struct param.
    fn is_aggregate(&self, name: &str) -> bool {
        !name.contains('.') && self.by_param.contains_key(name)
    }

    /// Build from a function's locals: a parameter local whose `Ty::Adt` reflects
    /// to a carrier present in `registry` becomes a structural struct param.
    pub fn from_function(
        func: &trust_types::VerifiableFunction,
        registry: &crate::clean_ground::AdtRegistry,
    ) -> Self {
        let mut by_param = HashMap::new();
        let mut enum_params = HashSet::new();
        let mut enum_aliases_by_param = HashMap::new();
        let n = func.body.arg_count;
        for i in 1..=n {
            let Some(local) = func.body.locals.get(i) else { continue };
            let Some(pname) = local.name.clone() else { continue };
            // A struct parameter whose inductive registered modulo 3 grounds its
            // fields structurally.
            if let Some(carrier) = crate::reflect::reflect_struct(&local.ty) {
                if registry.get(&carrier.name) == Some(&carrier) {
                    if let trust_types::Ty::Adt { variants, .. } = &local.ty
                        && !variants.is_empty()
                    {
                        enum_params.insert(pname.clone());
                        // `.` and `@` delimit field/downcast spellings. Extracted
                        // Rust identifiers never contain them; a hand-built public
                        // payload that does is ambiguous and therefore gets no
                        // aliases (the enum fallback above still blocks it).
                        let alias_namespace_safe =
                            !pname.is_empty() && !pname.chars().any(|ch| ch == '.' || ch == '@');
                        if alias_namespace_safe
                            && let Some(aliases) = validated_enum_field_aliases(&local.ty, &carrier)
                        {
                            enum_aliases_by_param.insert(pname.clone(), aliases);
                        }
                    }
                    by_param.insert(pname.clone(), carrier);
                    continue;
                }
            }
            // GOAL-ITEM #3 — a FLOAT parameter (`f: f32`/`f64`, possibly behind a
            // transparent reference) whose `Trust.FloatN` inductive registered modulo
            // 3 grounds its IEEE fields structurally: `f.exponent`/`f.mantissa` are
            // named Int projections (`BitVec` → Int), `f.sign` is the inert Bool field.
            let mut fty = &local.ty;
            while let trust_types::Ty::Ref { inner, .. } = fty {
                fty = inner;
            }
            if let trust_types::Ty::Float { width } = fty {
                if let Some(carrier) = crate::reflect::reflect_float(*width) {
                    if registry.get(&carrier.name).is_some() {
                        by_param.insert(pname, carrier);
                    }
                }
            }
        }
        StructParams { by_param, enum_params, enum_aliases_by_param }
    }
}

/// Validate the extractor's complete flattened enum view and construct aliases
/// from every supported MIR/spec spelling to its unique flattened payload name.
/// Any missing, reordered, renamed, duplicated, or type-mismatched field rejects
/// the whole map, so canonicalization can only remove syntax—not invent an
/// equality between distinct enum slots.
fn validated_enum_field_aliases(
    ty: &trust_types::Ty,
    carrier: &crate::reflect::AdtCarrier,
) -> Option<HashMap<String, String>> {
    let trust_types::Ty::Adt { fields, variants, .. } = ty else { return None };
    if variants.is_empty() || !carrier.is_enum() || carrier.constructors.len() != variants.len() {
        return None;
    }
    let [(tag_name, tag_ty), payloads @ ..] = fields.as_slice() else { return None };
    if tag_name != "__tag" || !matches!(tag_ty, trust_types::Ty::Int { .. }) {
        return None;
    }

    let expected_payloads = variants.iter().map(|variant| variant.fields.len()).sum::<usize>();
    if payloads.len() != expected_payloads {
        return None;
    }

    let mut aliases = HashMap::new();
    let mut flattened_names = HashSet::new();
    let mut flat_index = 1usize; // index 0 is the discriminant and is never a payload alias.
    for (variant_index, variant) in variants.iter().enumerate() {
        let ctor = carrier.constructors.get(variant_index)?;
        if ctor.discriminant != variant.discriminant || ctor.fields.len() != variant.fields.len() {
            return None;
        }
        for (field_index, ((source_name, source_ty), (ctor_name, _))) in
            variant.fields.iter().zip(&ctor.fields).enumerate()
        {
            if ctor_name != source_name {
                return None;
            }
            let flattened = format!("__v{variant_index}_{source_name}");
            if !flattened_names.insert(flattened.clone()) {
                return None;
            }
            let (actual_name, actual_ty) = fields.get(flat_index)?;
            if actual_name != &flattened || actual_ty != source_ty {
                return None;
            }
            // Every syntax key must designate exactly one semantic field. These
            // key classes are disjoint for an extractor-produced layout; any
            // collision in a public/deserialized payload rejects the whole map.
            if aliases.insert(format!(".{flat_index}"), flattened.clone()).is_some()
                || aliases
                    .insert(format!("@{variant_index}.{field_index}"), flattened.clone())
                    .is_some()
                || aliases.insert(format!(".{flattened}"), flattened).is_some()
            {
                return None;
            }
            flat_index += 1;
        }
    }
    Some(aliases)
}

/// Whether a reflected field-type carrier is an INTEGER operand carrier: a
/// machine integer (`Trust.Sort.BitVec w`, the carrier `reflect_ty` produces for
/// `Ty::Int`) or the `Trust.Sort.Int` math-integer / raw-pointer carrier. These
/// are the field types whose values participate in the linear arithmetic engine;
/// Bool / composite / generic field carriers are not.
fn is_int_field_carrier(code: &crate::kernel_check::ProofTerm) -> bool {
    use crate::kernel_check::ProofTerm as P;
    match code {
        P::Const(c) => c == crate::reflect::CARRIER_INT,
        // `Trust.Sort.BitVec <w>` = App(Const(BitVec), Const(w)).
        P::App(f, _) => matches!(&**f, P::Const(c) if c == crate::reflect::CARRIER_BITVEC),
        _ => false,
    }
}

/// Collect the distinct linear-variable names in first-appearance order, with
/// registered-struct awareness.
///
/// A struct param `p` of a registered inductive `Trust.Adt.<Name>` is itself
/// `Sort::Int` (the `Sort::from_ty` fallback for an Adt), but a struct VALUE is
/// NOT an integer operand — only its scalar FIELDS are. So:
/// - a bare `Var(p, Int)` for a registered struct param is the aggregate and is
///   DROPPED (it carries no integer content of its own);
/// - a named Int field `Var("p.x", Int)` of a registered struct is bound as a
///   linear var (so `p.x + p.y`-style VCs reconstruct linearly);
/// - a Bool field is inert (admitted, not arithmetic);
/// - a `.`-bearing name that is NOT a registered struct field is treated as an
///   ordinary opaque Int var (unchanged, sound — a fresh linear variable).
///
/// `params` carries the registered struct params (built from the function's
/// locals ∩ the registry). With EMPTY `params`, every Int/Bool variable follows
/// the ordinary non-struct path unchanged.
fn collect_int_vars(
    f: &Formula,
    order: &mut Vec<(String, bool)>,
    seen: &mut HashSet<String>,
    params: &StructParams,
) -> bool {
    use trust_types::{Formula as F, Sort};
    match f {
        // Bare aggregate of a registered struct: not an integer operand — drop it.
        F::Var(n, Sort::Int) if params.is_aggregate(n) => true,
        F::Var(n, Sort::Int) => {
            if seen.insert(n.clone()) {
                order.push((n.clone(), false));
            }
            true
        }
        F::Var(n, Sort::Bool) => {
            if seen.insert(n.clone()) {
                order.push((n.clone(), true));
            }
            true
        }
        F::Var(_, _) => false,
        F::Bool(_) | F::Int(_) | F::UInt(_) => true,
        F::Not(a) => collect_int_vars(a, order, seen, params),
        F::And(v) | F::Or(v) => v.iter().all(|x| collect_int_vars(x, order, seen, params)),
        F::Implies(a, b)
        | F::Eq(a, b)
        | F::Lt(a, b)
        | F::Le(a, b)
        | F::Gt(a, b)
        | F::Ge(a, b)
        | F::Add(a, b)
        | F::Sub(a, b)
        | F::Mul(a, b)
        | F::Div(a, b) => {
            collect_int_vars(a, order, seen, params) && collect_int_vars(b, order, seen, params)
        }
        _ => false,
    }
}

/// Rewrite every `Var(<param>.<key>, s)` of a registered struct param to its
/// canonical NAMED-field form (`p.0` → `p.x`), so the index-named MIR rvalue
/// fields unify with the named spec/precondition fields. All other vars are
/// unchanged. With an empty [`StructParams`] this is the identity, so the
/// non-struct path is unaffected.
fn canonicalize_struct_fields(f: &Formula, params: &StructParams) -> Formula {
    use trust_types::Formula as F;
    let bx = |x: F| Box::new(x);
    let r = |x: &F| canonicalize_struct_fields(x, params);
    match f {
        F::Var(n, s) => match params.canonical_field_name(n) {
            Some(canon) if &canon != n => F::Var(canon, s.clone()),
            _ => f.clone(),
        },
        F::Not(a) => F::Not(bx(r(a))),
        F::And(v) => F::And(v.iter().map(r).collect()),
        F::Or(v) => F::Or(v.iter().map(r).collect()),
        F::Implies(a, b) => F::Implies(bx(r(a)), bx(r(b))),
        F::Eq(a, b) => F::Eq(bx(r(a)), bx(r(b))),
        F::Lt(a, b) => F::Lt(bx(r(a)), bx(r(b))),
        F::Le(a, b) => F::Le(bx(r(a)), bx(r(b))),
        F::Gt(a, b) => F::Gt(bx(r(a)), bx(r(b))),
        F::Ge(a, b) => F::Ge(bx(r(a)), bx(r(b))),
        F::Add(a, b) => F::Add(bx(r(a)), bx(r(b))),
        F::Sub(a, b) => F::Sub(bx(r(a)), bx(r(b))),
        F::Mul(a, b) => F::Mul(bx(r(a)), bx(r(b))),
        F::Div(a, b) => F::Div(bx(r(a)), bx(r(b))),
        F::Rem(a, b) => F::Rem(bx(r(a)), bx(r(b))),
        F::Neg(a) => F::Neg(bx(r(a))),
        F::Ite(c, t, e) => F::Ite(bx(r(c)), bx(r(t)), bx(r(e))),
        other => other.clone(),
    }
}

/// Flatten a (possibly nested) conjunction into its atoms.
fn flatten_and(f: &Formula, out: &mut Vec<Formula>) {
    match f {
        Formula::And(v) => v.iter().for_each(|x| flatten_and(x, out)),
        other => out.push(other.clone()),
    }
}

/// An auxiliary MIR temporary (`_3#s0_0`, `__ret`, …), as opposed to a source
/// parameter — these are the SSA temps introduced by branch lowering, defined by
/// `Eq(temp, …)` conjuncts that we inline.
fn is_aux(name: &str) -> bool {
    name.starts_with('_') || name.contains('#')
}

/// Substitute `Var(name, _) := val` throughout `f`.
fn subst_var(f: &Formula, name: &str, val: &Formula) -> Formula {
    use trust_types::Formula as F;
    let bx = |x: F| Box::new(x);
    let s = |x: &F| subst_var(x, name, val);
    match f {
        F::Var(n, _) if n == name => val.clone(),
        F::Not(a) => F::Not(bx(s(a))),
        F::And(v) => F::And(v.iter().map(s).collect()),
        F::Or(v) => F::Or(v.iter().map(s).collect()),
        F::Implies(a, b) => F::Implies(bx(s(a)), bx(s(b))),
        F::Eq(a, b) => F::Eq(bx(s(a)), bx(s(b))),
        F::Lt(a, b) => F::Lt(bx(s(a)), bx(s(b))),
        F::Le(a, b) => F::Le(bx(s(a)), bx(s(b))),
        F::Gt(a, b) => F::Gt(bx(s(a)), bx(s(b))),
        F::Ge(a, b) => F::Ge(bx(s(a)), bx(s(b))),
        F::Add(a, b) => F::Add(bx(s(a)), bx(s(b))),
        F::Sub(a, b) => F::Sub(bx(s(a)), bx(s(b))),
        F::Mul(a, b) => F::Mul(bx(s(a)), bx(s(b))),
        F::Div(a, b) => F::Div(bx(s(a)), bx(s(b))),
        other => other.clone(),
    }
}

/// Push `Not` through comparisons (`¬(a<b) ⇒ a≥b`, etc.) and drop double
/// negations, recursing through connectives — so the engine sees plain
/// comparison atoms instead of negated guards.
fn normalize_not(f: &Formula) -> Formula {
    use trust_types::Formula as F;
    match f {
        F::Not(inner) => match normalize_not(inner) {
            F::Lt(a, b) => F::Ge(a, b),
            F::Le(a, b) => F::Gt(a, b),
            F::Gt(a, b) => F::Le(a, b),
            F::Ge(a, b) => F::Lt(a, b),
            F::Not(x) => *x,
            other => F::Not(Box::new(other)),
        },
        F::And(v) => F::And(v.iter().map(normalize_not).collect()),
        F::Or(v) => F::Or(v.iter().map(normalize_not).collect()),
        F::Implies(a, b) => F::Implies(Box::new(normalize_not(a)), Box::new(normalize_not(b))),
        other => other.clone(),
    }
}

/// Locate the FIRST `Ite(cond, then, else)` subterm anywhere in `f` (pre-order),
/// returning its three components by reference. Used to drive the `Ite → Or`
/// case-split rewrite ([`lift_ite`]).
fn find_first_ite(f: &Formula) -> Option<(&Formula, &Formula, &Formula)> {
    use trust_types::Formula as F;
    if let F::Ite(c, t, e) = f {
        return Some((c, t, e));
    }
    for child in f.children() {
        if let Some(found) = find_first_ite(child) {
            return Some(found);
        }
    }
    None
}

/// Replace EVERY occurrence of the `Ite(cond, then, else)` whose condition is
/// `cond` with `branch` throughout `f`. (`cond` identifies the clamp uniquely in
/// the VCs we handle — a single guarded clamp per value — so substituting all
/// matching `Ite`s with the chosen branch is exact under that condition.)
fn subst_ite(f: &Formula, cond: &Formula, branch: &Formula) -> Formula {
    use trust_types::Formula as F;
    if let F::Ite(c, _, _) = f {
        if c.as_ref() == cond {
            return branch.clone();
        }
    }
    let bx = |x: F| Box::new(x);
    let s = |x: &F| subst_ite(x, cond, branch);
    match f {
        F::Not(a) => F::Not(bx(s(a))),
        F::And(v) => F::And(v.iter().map(s).collect()),
        F::Or(v) => F::Or(v.iter().map(s).collect()),
        F::Implies(a, b) => F::Implies(bx(s(a)), bx(s(b))),
        F::Eq(a, b) => F::Eq(bx(s(a)), bx(s(b))),
        F::Lt(a, b) => F::Lt(bx(s(a)), bx(s(b))),
        F::Le(a, b) => F::Le(bx(s(a)), bx(s(b))),
        F::Gt(a, b) => F::Gt(bx(s(a)), bx(s(b))),
        F::Ge(a, b) => F::Ge(bx(s(a)), bx(s(b))),
        F::Add(a, b) => F::Add(bx(s(a)), bx(s(b))),
        F::Sub(a, b) => F::Sub(bx(s(a)), bx(s(b))),
        F::Mul(a, b) => F::Mul(bx(s(a)), bx(s(b))),
        F::Div(a, b) => F::Div(bx(s(a)), bx(s(b))),
        F::Ite(c, t, e) => F::Ite(bx(s(c)), bx(s(t)), bx(s(e))),
        other => other.clone(),
    }
}

/// Eliminate every `Ite(cond, a, b)` term by the SOUND case-split rewrite: a
/// formula `P` containing such a term is equivalent to
/// `(cond ∧ P[a]) ∨ ((¬cond) ∧ P[b])`
/// because `cond` is a decidable/total boolean — exactly one branch is taken,
/// and the `¬cond` literal on the else arm is what carries the bound (e.g.
/// `¬(pct > 100)` ⇒ `pct ≤ 100`). Clamp idioms (`x.min(C)`, `if x>C {C} else {x}`,
/// `x.clamp(lo,hi)`) lower to `Eq(p, Ite(¬(x>C), x, C))`; this lifts that to the
/// disjunction the n-ary `Or` case-split ([`refute_or_split`]) then discharges:
/// the `cond` arm fixes `p = x` (with `x ≤ C` from `cond`), the `¬cond` arm fixes
/// `p = C`. Applied to a fixpoint so nested / multiple `Ite`s are all removed.
/// `normalize_not` later pushes the `cond`/`¬cond` literals into usable
/// comparison atoms. Returns `f` unchanged if it has no `Ite`.
fn lift_ite(f: &Formula) -> Formula {
    use trust_types::Formula as F;
    // Extract the first Ite's condition + branches (cloned so the borrow ends).
    let Some((cond, then_b, else_b)) =
        find_first_ite(f).map(|(c, t, e)| (c.clone(), t.clone(), e.clone()))
    else {
        return f.clone();
    };
    let then_f = subst_ite(f, &cond, &then_b);
    let else_f = subst_ite(f, &cond, &else_b);
    let not_cond = F::Not(Box::new(cond.clone()));
    // Recurse to remove any remaining Ites in each branch (different conditions,
    // or Ites nested inside `then_b`/`else_b` that the substitution carried in).
    let disj = F::Or(vec![
        F::And(vec![cond, lift_ite(&then_f)]),
        F::And(vec![not_cond, lift_ite(&else_f)]),
    ]);
    disj
}

/// Is `a` an aux-temp DEFINITION conjunct `Eq(Var(aux), rhs)`?
fn as_aux_def(a: &Formula) -> Option<(String, Formula)> {
    if let Formula::Eq(l, r) = a {
        if let Formula::Var(n, _) = &**l {
            if is_aux(n) {
                return Some((n.clone(), (**r).clone()));
            }
        }
    }
    None
}

/// Collect every aux-temp definition `Eq(Var(aux), rhs)` reachable from `f`
/// through NESTED `And` nodes only — never crossing an `Or` (or `Implies`/`Not`)
/// boundary. The result is the full def set jointly asserted with any atom in the
/// SAME conjunctive (single-path) context as `f`.
///
/// SOUNDNESS — within-context single version: every name collected here lives in
/// one conjunctive scope, with NO disjunction between the def site and the use
/// site. SSA gives each MIR local exactly one def per straight-line path, and the
/// path-split (`lift_ite` / the `Or` arms) has already separated per-path values
/// into distinct `Or` branches. So inside a single `And`-subtree each aux base has
/// AT MOST ONE def, and substituting that def into every atom of the subtree is a
/// model-preserving rewrite. We deliberately stop at `Or`: a def inside one arm
/// must never be applied to a sibling arm (those are different live values of the
/// same base), which would be unsound — collecting only through `And` guarantees
/// we never conflate two arms.
fn collect_subtree_aux_defs(f: &Formula, out: &mut Vec<(String, Formula)>) {
    use trust_types::Formula as F;
    if let Some((n, rhs)) = as_aux_def(f) {
        out.push((n, rhs));
        return;
    }
    if let F::And(v) = f {
        for a in v {
            collect_subtree_aux_defs(a, out);
        }
    }
    // Any other connective (`Or`, `Implies`, `Not`) opens a new scope: do not
    // descend — its defs are local to that branch and collected when the recursion
    // reaches it as a child of an `And`, or handled by `inline_aux_deep` itself.
}

/// Recursively inline aux-temp definitions through the WHOLE formula tree (not
/// just the top-level conjunction). At every `And` node, this collects the defs
/// from the ENTIRE `And`-subtree rooted here (via [`collect_subtree_aux_defs`],
/// which descends through nested `And`s but stops at `Or`), resolves them against
/// the accumulated outer-scope `env` and each other to a fixpoint, drops the
/// definition conjuncts, and inlines the def map into the surviving conjuncts;
/// `Or` arms inherit the enclosing `env`. This reaches the def chains that clamp
/// VCs bury inside `Or` arms — e.g. `Eq(_4, pct>100)`, `Eq(p, Ite(…))`,
/// `Eq(_8, p)` — so by the time `lift_ite`/`bv_overflow_rewrite` run, no
/// ungroundable Bool-aux equality survives to break grounding, and every clamp
/// `Ite` has been carried to its real use sites.
///
/// Collecting from the whole subtree (not just THIS node's direct conjuncts) is
/// what lets a GLOBAL bound fact stated in an OUTER conjunct — e.g.
/// `scaled#s5_0 ≤ 255` — see the def `scaled#s5_0 = (_6#s4_0/100)` that sits in a
/// deeply NESTED inner `And` of the same arm. Without it, the outer bound keeps
/// the variable name while the violation `scaled#s5_0 > 255` (in the inner `And`)
/// gets inlined to `(…)/100 > 255`, so the two no longer share a term and the
/// immediate contradiction `≤255 ∧ >255` is never seen. Sound: each inlined
/// `Eq(aux, rhs)` is a definition and — per [`collect_subtree_aux_defs`] — every
/// name has a single live value in this conjunctive context, so substituting it
/// everywhere and dropping it preserves the formula's models.
fn inline_aux_deep(f: &Formula, env: &[(String, Formula)]) -> Formula {
    use trust_types::Formula as F;
    match f {
        F::And(v) => {
            // Defs reachable from THIS And-subtree (through nested `And`s, not
            // crossing `Or`), seeded with the outer env, resolved to a fixpoint.
            // Gathering the whole subtree (not just direct conjuncts) lets an outer
            // bound atom be rewritten by a def that lives in an inner nested `And`.
            let mut defs: Vec<(String, Formula)> = env.to_vec();
            collect_subtree_aux_defs(f, &mut defs);
            for _ in 0..defs.len() {
                let snapshot = defs.clone();
                for (_, rhs) in defs.iter_mut() {
                    for (dn, dv) in &snapshot {
                        *rhs = subst_var(rhs, dn, dv);
                    }
                }
            }
            // Keep non-def conjuncts; inline defs, recurse, normalize.
            let mut out: Vec<F> = Vec::new();
            for a in v {
                if as_aux_def(a).is_some() {
                    continue; // a definition — inlined, not asserted
                }
                // A nested `And` child is recursed into WITHOUT pre-substituting:
                // the recursion drops that subtree's OWN def conjuncts (each an `Eq`
                // direct conjunct caught by `as_aux_def` before any substitution) and
                // then inlines `defs` into its surviving atoms. Pre-substituting here
                // would clobber a def's own LHS `Var` (e.g. rewrite `_4#s0_0 = pct>100`
                // to `(pct>100) = (pct>100)`) so it would no longer be recognized and
                // dropped — leaving an ungroundable Bool `Eq` that defeats grounding.
                // Non-`And` atoms have no buried def to protect, so substitute them
                // here (this is what carries `defs` into an OUTER bound atom like
                // `scaled#s5_0 ≤ 255` whose def sits in a deeper nested `And`).
                if matches!(a, F::And(_)) {
                    out.push(inline_aux_deep(a, &defs));
                } else {
                    let mut atom = a.clone();
                    for (dn, dv) in &defs {
                        atom = subst_var(&atom, dn, dv);
                    }
                    out.push(inline_aux_deep(&atom, &defs));
                }
            }
            F::And(out)
        }
        F::Or(v) => F::Or(v.iter().map(|d| inline_aux_deep(d, env)).collect()),
        F::Implies(a, b) => {
            F::Implies(Box::new(inline_aux_deep(a, env)), Box::new(inline_aux_deep(b, env)))
        }
        F::Not(a) => F::Not(Box::new(inline_aux_deep(a, env))),
        other => {
            // A leaf atom: apply the accumulated env then normalize negations.
            let mut atom = other.clone();
            for (dn, dv) in env {
                atom = subst_var(&atom, dn, dv);
            }
            normalize_not(&atom)
        }
    }
}

/// Preprocess a VC so the linear engine can see it: inline auxiliary-temp
/// definitions (`Eq(_t, rhs)` conjuncts, resolved to a fixpoint) THROUGHOUT the
/// formula tree (including inside `Or` arms — see [`inline_aux_deep`]), drop those
/// definition atoms, and push negations into comparisons. A guarded check like
/// `_3=len ∧ _4=(i<_3) ∧ _4 ∧ i≥_3` collapses to `i<len ∧ i≥len`.
fn simplify_vc(formula: &Formula) -> Formula {
    let inlined = inline_aux_deep(formula, &[]);
    let mut atoms = Vec::new();
    flatten_and(&inlined, &mut atoms);
    Formula::And(atoms)
}

/// The ORIGINAL top-level-only simplification (used on the non-clamp path so those
/// VCs reduce exactly as before): flatten the top `And`, inline its top-level
/// `Eq(aux, rhs)` defs (fixpoint), drop them, push negations into comparisons.
fn simplify_vc_toplevel(formula: &Formula) -> Formula {
    let mut atoms = Vec::new();
    flatten_and(formula, &mut atoms);

    let mut defs: Vec<(String, Formula)> = Vec::new();
    for a in &atoms {
        if let Some((n, rhs)) = as_aux_def(a) {
            defs.push((n, rhs));
        }
    }
    for _ in 0..defs.len() {
        let snapshot = defs.clone();
        for (_, rhs) in defs.iter_mut() {
            for (dn, dv) in &snapshot {
                *rhs = subst_var(rhs, dn, dv);
            }
        }
    }
    let mut out: Vec<Formula> = Vec::new();
    for a in &atoms {
        if as_aux_def(a).is_some() {
            continue;
        }
        let mut atom = a.clone();
        for (dn, dv) in &defs {
            atom = subst_var(&atom, dn, dv);
        }
        out.push(normalize_not(&atom));
    }
    Formula::And(out)
}

/// Normalize a comparison atom to `(strict, lo, hi)` meaning `lo < hi` (strict)
/// or `lo ≤ hi`. `Gt`/`Ge` are flipped.
pub(crate) fn normalize_cmp(f: &Formula) -> Option<(bool, Formula, Formula)> {
    use trust_types::Formula as F;
    match f {
        F::Lt(a, b) => Some((true, (**a).clone(), (**b).clone())),
        F::Gt(a, b) => Some((true, (**b).clone(), (**a).clone())),
        F::Le(a, b) => Some((false, (**a).clone(), (**b).clone())),
        F::Ge(a, b) => Some((false, (**b).clone(), (**a).clone())),
        _ => None,
    }
}

/// Reconstruct a kernel proof that a safety VC conjunction is UNSATISFIABLE,
/// for the guarded-check fragment: the conjunction contains `a < b` and `b ≤ a`
/// (in any comparison spelling), a direct contradiction. Returns `(proof, type)`
/// where `type = Π(vars:Int). conjunction → False`, both kernel-ready. `None` if
/// the VC is outside the fragment (non-`Int` vars, or no direct contradiction).
/// A BV operand of a mul-overflow check → (Int var name, its inclusive upper bound).
/// A value-preserving widening `BvZeroExt(x:BitVec(W), _)` or a plain `BitVec(W)` var
/// ranges over `0..=2^W-1`, so its Int abstraction is bounded by `2^W-1`.
fn bv_mul_operand_to_int(op: &Formula) -> Option<(String, i128)> {
    use trust_types::{Formula as F, Sort};
    let (name, width) = match op {
        F::BvZeroExt(inner, _added) => match &**inner {
            F::Var(n, Sort::BitVec(w)) => (n.clone(), *w),
            _ => return None,
        },
        F::Var(n, Sort::BitVec(w)) => (n.clone(), *w),
        _ => return None,
    };
    if width >= 127 {
        return None;
    }
    Some((format!("{name}__as_int"), (1i128 << width) - 1))
}

/// A BV multiplication operand → its Int abstraction plus any bound conjuncts:
/// a BitVec literal constant becomes `Int(c)` (no bound); a BV/zero-extended var
/// becomes a fresh bounded Int var `0 ≤ v ≤ 2^W-1`.
fn bv_mul_operand(op: &Formula) -> Option<(Formula, Vec<Formula>)> {
    use trust_types::{Formula as F, Sort};
    if let F::BitVec { value, .. } = op {
        return Some((F::Int(*value), Vec::new()));
    }
    let (name, ca) = bv_mul_operand_to_int(op)?;
    let v = F::Var(name, Sort::Int);
    Some((
        v.clone(),
        vec![
            F::Le(Box::new(F::Int(0)), Box::new(v.clone())),
            F::Le(Box::new(v), Box::new(F::Int(ca))),
        ],
    ))
}

/// If `atom` IS the BV
/// unsigned-mul-overflow encoding `Not(Eq(BvUDiv(BvMul(a,b,w),a,w), b))`, return
/// its sound Int abstraction `0≤a≤ca ∧ 0≤b≤cb ∧ a*b > 2^w-1` (an `And` atom),
/// else `None`. Lets the in-place rewrite ([`bv_overflow_rewrite`]) replace a BV
/// overflow check buried inside an `Or` arm (clamp VCs nest it under the path
/// case-split) — same one-directional Int abstraction, soundness identical.
fn bv_overflow_atom_to_int(atom: &Formula) -> Option<Formula> {
    use trust_types::Formula as F;
    let F::Not(inner) = atom else { return None };
    let F::Eq(udiv, b_check) = &**inner else { return None };
    let F::BvUDiv(mul, a_div, _dw) = &**udiv else { return None };
    let F::BvMul(a_bv, b_bv, w) = &**mul else { return None };
    if a_div.as_ref() != a_bv.as_ref() || b_check.as_ref() != b_bv.as_ref() {
        return None;
    }
    let (a_f, mut conj) = bv_mul_operand(a_bv)?;
    let (b_f, b_conj) = bv_mul_operand(b_bv)?;
    conj.extend(b_conj);
    if *w > 64 {
        return None;
    }
    let max = (1i128 << *w) - 1;
    conj.push(F::Gt(Box::new(F::Mul(Box::new(a_f), Box::new(b_f))), Box::new(F::Int(max))));
    Some(F::And(conj))
}

/// Recursively replace every BV unsigned-mul-overflow atom in `f` with its sound
/// Int abstraction (in place, preserving the surrounding `And`/`Or` structure),
/// reaching BV overflow checks nested inside `Or` arms — the shape clamp VCs
/// produce once the path is case-split. The encoding `trust-vcgen` emits is
/// `Not(Eq(BvUDiv(BvMul(a,b,w), a, w), b))` ("the w-bit product doesn't divide
/// back ⇒ it overflowed w bits"); under the operands' bounds `0≤a≤ca`, `0≤b≤cb`
/// this is exactly `a*b > 2^w-1`. Each replacement is a one-directional
/// ABSTRACTION (UNSAT of the Int form implies UNSAT of the BV form), so we only
/// ever turn a refutable check into a proof and NEVER claim a proof for a genuine
/// (unbounded) overflow — that Int form stays SAT and falls through.
fn bv_overflow_rewrite(f: &Formula) -> Formula {
    use trust_types::Formula as F;
    if let Some(abstracted) = bv_overflow_atom_to_int(f) {
        return abstracted;
    }
    // The divisor-nonzero guard `Not(Eq(<bv operand>, BitVec{0}))` that vcgen emits
    // alongside the `BvUDiv` overflow check (so the udiv is meaningful). It carries
    // no fact the Int abstraction needs — drop it to `True` (sound: removing a
    // hypothesis can only make refutation harder, never unsound) so no stray
    // `BitVec` operand survives to make `collect_int_vars` bail.
    if is_bv_nonzero_guard(f) {
        return F::Bool(true);
    }
    let bx = |x: F| Box::new(x);
    let s = |x: &F| bv_overflow_rewrite(x);
    match f {
        F::Not(a) => F::Not(bx(s(a))),
        F::And(v) => F::And(v.iter().map(s).collect()),
        F::Or(v) => F::Or(v.iter().map(s).collect()),
        F::Implies(a, b) => F::Implies(bx(s(a)), bx(s(b))),
        other => other.clone(),
    }
}

/// `Not(Eq(op, BitVec{0}))` where `op` is a `BitVec`-sorted operand (a
/// `BvZeroExt(Var(_,BitVec))` or bare `Var(_,BitVec)`) — the divisor-nonzero
/// guard accompanying a `BvUDiv` overflow check. (`is_bv_operand`.)
fn is_bv_nonzero_guard(f: &Formula) -> bool {
    use trust_types::Formula as F;
    let F::Not(inner) = f else { return false };
    let F::Eq(a, b) = &**inner else { return false };
    matches!(&**b, F::BitVec { value: 0, .. }) && is_bv_operand(a)
}

/// A `BitVec`-sorted operand: a `BvZeroExt` of a `BitVec` var, or a bare `BitVec`
/// var. (Used to spot the leftover divisor-nonzero guard.)
fn is_bv_operand(f: &Formula) -> bool {
    use trust_types::{Formula as F, Sort};
    match f {
        F::BvZeroExt(inner, _) => matches!(&**inner, F::Var(_, Sort::BitVec(_))),
        F::Var(_, Sort::BitVec(_)) => true,
        _ => false,
    }
}

/// Whole-formula BV-overflow abstraction (the pre-clamp behavior): if the FIRST
/// (flat, top-level) conjunct that is a BV unsigned-mul-overflow check abstracts
/// to Int, replace the WHOLE VC with that single abstraction. Used on the non-clamp
/// (no-`Ite`) path so those VCs reduce exactly as before — `bv_overflow_rewrite`'s
/// in-place rewrite is reserved for clamp VCs, where the check is nested in an `Or`
/// arm and must be reached without perturbing the simple VCs' proof shapes.
fn bv_overflow_to_int(f: &Formula) -> Option<Formula> {
    let mut atoms = Vec::new();
    flatten_and(f, &mut atoms);
    atoms.iter().find_map(bv_overflow_atom_to_int)
}

/// Does `f` contain an `Ite` term anywhere? Gates the clamp pipeline.
fn has_ite(f: &Formula) -> bool {
    find_first_ite(f).is_some()
}

/// The VC-preprocessing pipeline shared by [`refute_vc`] and the tests: inline aux
/// defs, abstract BV-overflow checks, and (for clamp VCs) eliminate `Ite`. The BV
/// abstraction and `Ite` lift are GATED on the presence of an `Ite`: a clamp VC
/// uses the in-place `bv_overflow_rewrite` + `lift_ite` (reaching checks nested in
/// `Or` arms); every other VC uses the original whole-formula `bv_overflow_to_int`
/// and skips the lift, so its (already-green) proof shape is byte-for-byte
/// unchanged.
/// Replace every `BvToInt(..)` subterm by a fresh, deterministically-named `Int`
/// variable — the same term always maps to the same var (keyed by its structure).
///
/// SOUNDNESS (one-directional abstraction): a `BvToInt(t)` term is `Int`-sorted but
/// outside the linear fragment (`collect_int_vars`/`ground_int` reject it), so its
/// mere presence in an irrelevant hypothesis forces `refute_vc` to bail. Replacing
/// it by a fresh `Int` var keeps EVERY atom that mentions it (now stated about the
/// var) and adds NO constraint, so the abstracted conjunction is strictly WEAKER. A
/// refutation of the weaker conjunction is parametric in the fresh var; instantiating
/// the var back to `BvToInt(t)` yields a refutation of the original. We therefore can
/// only ever turn a refutable VC into a proof, never fabricate one for a SAT VC — the
/// abstracted form stays SAT and falls through. This is exactly what lets the masked
/// shift amount `BvToInt(BvAnd(n,31))` (carried with its `≤ 31` bound as an explicit
/// hypothesis by vcgen) and the constant-shift VCs (blocked only by an unrelated
/// `BvToInt(BvShl(..))` byte-assembly hypothesis) reach the linear engine.
fn abstract_opaque_int(f: &Formula) -> Formula {
    fn go(f: &Formula, names: &mut HashMap<String, String>) -> Formula {
        use trust_types::{Formula as F, Sort};
        if let F::BvToInt(..) = f {
            // Deterministic name from the term's structure; identical terms collide
            // to the same fresh var (so their shared bounds line up in the engine).
            let key = format!("{f:?}");
            let next = names.len();
            let name =
                names.entry(key).or_insert_with(|| format!("__trust_opaque_int_{next}")).clone();
            return F::Var(name, Sort::Int);
        }
        let bx = |x: F| Box::new(x);
        let s = |x: &F, m: &mut HashMap<String, String>| go(x, m);
        match f {
            F::Not(a) => F::Not(bx(s(a, names))),
            F::And(v) => F::And(v.iter().map(|x| go(x, names)).collect()),
            F::Or(v) => F::Or(v.iter().map(|x| go(x, names)).collect()),
            F::Implies(a, b) => F::Implies(bx(s(a, names)), bx(s(b, names))),
            F::Eq(a, b) => F::Eq(bx(s(a, names)), bx(s(b, names))),
            F::Lt(a, b) => F::Lt(bx(s(a, names)), bx(s(b, names))),
            F::Le(a, b) => F::Le(bx(s(a, names)), bx(s(b, names))),
            F::Gt(a, b) => F::Gt(bx(s(a, names)), bx(s(b, names))),
            F::Ge(a, b) => F::Ge(bx(s(a, names)), bx(s(b, names))),
            F::Add(a, b) => F::Add(bx(s(a, names)), bx(s(b, names))),
            F::Sub(a, b) => F::Sub(bx(s(a, names)), bx(s(b, names))),
            F::Mul(a, b) => F::Mul(bx(s(a, names)), bx(s(b, names))),
            F::Div(a, b) => F::Div(bx(s(a, names)), bx(s(b, names))),
            F::Ite(c, t, e) => F::Ite(bx(s(c, names)), bx(s(t, names)), bx(s(e, names))),
            other => other.clone(),
        }
    }
    go(f, &mut HashMap::new())
}

fn preprocess_vc(formula: &Formula) -> Formula {
    let formula = &abstract_opaque_int(formula);
    if has_ite(formula) {
        // Clamp VC: deep aux-inline reaches the def chains buried in `Or` arms,
        // in-place BV abstraction reaches nested overflow checks, and `lift_ite`
        // case-splits each clamp condition.
        let simplified = simplify_vc(formula);
        let abstracted = bv_overflow_rewrite(&simplified);
        let lifted = lift_ite(&abstracted);
        normalize_not(&lifted)
    } else {
        // Every other VC keeps the original pipeline (top-level aux-inline + whole-
        // formula BV abstraction), PLUS (M6 rung 2) the same `normalize_not` flip the
        // Ite branch already applies: `Not(Lt/Le/Gt/Ge(a,b))` → the direct opposite
        // comparison (`¬(a<b) → a≥b`, etc). Previously this flip only ran on the
        // Ite/clamp path, so a NEGATED comparison guard (`if !(idx >= depth) { .. }`,
        // or a `SwitchInt`'s "otherwise" edge landing on `Not(cond)`) stayed invisible
        // to `collect_comp_hyps_props` (which only reads DIRECT Lt/Le/Gt/Ge/Eq atoms,
        // never `Not(..)`) outside a clamp shape. `normalize_not` is pure formula
        // rewriting with no proof-term reuse — the eventual proof is built FRESH from
        // `ground_formula_prop` of the (now-normalized) formula in `refute_vc_with`,
        // so broadening where it runs cannot desync a stale proof from its type; it
        // can only ever make MORE hypotheses legible to the linear engine, never
        // fewer, and a formula with no `Not(comparison)` atoms is a FIXED POINT of
        // `normalize_not` (it only rewrites `Not`/`And`/`Or`/`Implies` nodes), so
        // already-green proofs stay unchanged — pinned by
        // `preprocess_vc_is_unchanged_on_a_comparison_only_formula` below, and by
        // the full existing suite (every prior non-Ite discharge test) staying green.
        let simplified = simplify_vc_toplevel(formula);
        let abstracted = bv_overflow_to_int(&simplified).unwrap_or(simplified);
        normalize_not(&abstracted)
    }
}

pub fn refute_vc(formula: &Formula) -> Option<(Expr, Expr)> {
    refute_vc_with(formula, &StructParams::default())
}

/// [`refute_vc`] with Phase 1 struct-param awareness: registered struct params
/// recurse into their named Int fields (and the bare aggregate is dropped) via
/// [`collect_int_vars`]. With an EMPTY [`StructParams`] this is identical to
/// `refute_vc`, so the non-struct path is byte-for-byte unchanged.
pub(crate) fn refute_vc_with(formula: &Formula, params: &StructParams) -> Option<(Expr, Expr)> {
    // Phase 1 — canonicalize registered struct-field names (`p.0` → `p.x`) so the
    // index-named rvalue fields unify with the named spec/precondition fields, then
    // run the unchanged pipeline. With an empty `params` this is a no-op.
    let canonicalized = canonicalize_struct_fields(formula, params);
    let normalized = preprocess_vc(&canonicalized);
    let formula = &normalized;
    let (mut vars, mut seen) = (Vec::new(), HashSet::new());
    if !collect_int_vars(formula, &mut vars, &mut seen, params) {
        return None;
    }
    let mut atoms = Vec::new();
    flatten_and(formula, &mut atoms);
    let n = vars.len() as u32;
    let cst = |s: &str| Expr::const_(Name::from_string(s), LevelVec::new());

    // Conjunction as the hypothesis type (under the n var binders; vᵢ = #(n-1-idx)).
    let type_map: HashMap<String, Expr> = vars
        .iter()
        .enumerate()
        .map(|(idx, (v, _))| (v.clone(), Expr::bvar(n - 1 - idx as u32)))
        .collect();
    let conj_ty = ground_formula_prop(formula, &type_map)?;

    // The proof of False under λvars λh (extra-binder depth 0).
    let false_pf = build_false(&atoms, &vars, n, 0)?;

    let mut proof = Expr::lam(bd(), conj_ty.clone(), false_pf);
    let mut ty = Expr::pi(bd(), conj_ty, cst("False"));
    // Wrap the variable binders innermost-first (vₙ₋₁ … v₀) with each var's carrier.
    for (_, is_bool) in vars.iter().rev() {
        let carrier = if *is_bool { cst("Bool") } else { int() };
        proof = Expr::lam(bd(), carrier.clone(), proof);
        ty = Expr::pi(bd(), carrier, ty);
    }
    Some((proof, ty))
}

/// A hypothesis available in the current proof context: a normalized comparison
/// `lo (<|≤) hi` together with a kernel proof term of it.
pub(crate) struct Hyp {
    pub(crate) strict: bool,
    pub(crate) lo: Formula,
    pub(crate) hi: Formula,
    pub(crate) proof: Expr,
}

impl Hyp {
    pub(crate) fn new(strict: bool, lo: Formula, hi: Formula, proof: Expr) -> Self {
        Hyp { strict, lo, hi, proof }
    }
}

/// Positively prove `Int.lt a b` from the hypotheses: `a < m ≤ b`
/// (`Int.lt_of_lt_of_le`) or `a ≤ m < b` (`Int.lt_of_le_of_lt`), with `≤` steps
/// discharged by [`derive_le`]. Used by inhabitation to prove a `<` postcondition
/// from the precondition (e.g. `0 < x ⊢ 0 < x+1`).
pub(crate) fn prove_lt(
    a: &Formula,
    b: &Formula,
    hyps: &[Hyp],
    map: &HashMap<String, Expr>,
    depth: u32,
) -> Option<Expr> {
    let cst = |s: &str| Expr::const_(Name::from_string(s), LevelVec::new());
    let a = &fold_consts(a);
    let b = &fold_consts(b);
    // Literal `c1 < c2`: `Int.lt a b := Int.le (a+1) b`, so the witness is
    // `Int.NonNeg.mk (c2 − c1 − 1)` (the nonneg-difference literal).
    if let (Formula::Int(ac), Formula::Int(bc)) = (a, b) {
        if ac < bc {
            // `c2 − c1 − 1` via checked i128 arithmetic so an extreme literal
            // pair (e.g. `i128::MIN < i128::MAX`) cannot panic; if the nonneg
            // difference doesn't fit a `u64` witness we fail closed (return None).
            // Trust: fix-closed against the literal-difference subtract overflow.
            if let Some(diff) = bc.checked_sub(*ac).and_then(|d| d.checked_sub(1)) {
                if let Ok(diff) = u64::try_from(diff) {
                    return Some(Expr::apps(cst("Int.NonNeg.mk"), [Expr::nat_lit(diff)]));
                }
            }
        }
        return None;
    }
    for h in hyps {
        if h.strict && &h.lo == a {
            if let Some(m_le_b) = derive_le(&h.hi, b, hyps, map, depth) {
                return Some(Expr::apps(
                    cst("Int.lt_of_lt_of_le"),
                    [
                        ground_int(a, map)?,
                        ground_int(&h.hi, map)?,
                        ground_int(b, map)?,
                        h.proof.clone(),
                        m_le_b,
                    ],
                ));
            }
        }
        if h.strict && &h.hi == b {
            if let Some(a_le_m) = derive_le(a, &h.lo, hyps, map, depth) {
                return Some(Expr::apps(
                    cst("Int.lt_of_le_of_lt"),
                    [
                        ground_int(a, map)?,
                        ground_int(&h.lo, map)?,
                        ground_int(b, map)?,
                        a_le_m,
                        h.proof.clone(),
                    ],
                ));
            }
        }
    }
    // Strict predecessor `base - k < base` (k ≥ 1 literal): the basic fact a
    // `len - 1 < len` / mirror-index check rests on. Independent of any hyp.
    if let Formula::Sub(base, kf) = a {
        if let Formula::Int(k) = &**kf {
            if *k >= 1 && &**base == b {
                if let Some(pf) = lt_sub_lit(&ground_int(b, map)?, *k) {
                    return Some(pf);
                }
            }
        }
    }
    // `left - r < b` via the case-(a) clamp `left - r ≤ left` (when `0 ≤ r`) chained
    // with a strict `left < b`: this surfaces the TIGHT bound `(len-1)-i ≤ len-1`
    // directly (the generic `sub_upper_bound` prefers the loose two-sided `≤ u64::MAX`
    // type bound and so misses the strict gap). Discharges the mirror-index
    // `(len-1)-i < len` via `(len-1)-i ≤ len-1 < len`.
    if depth > 0 {
        if let Formula::Sub(left, right) = a {
            if let Some(h0) = hyps
                .iter()
                .find(|h| matches!(&h.lo, Formula::Int(0)) && &h.hi == &**right && !h.strict)
            {
                if let Some(left_lt_b) = prove_lt(left, b, hyps, map, depth - 1) {
                    let a_le_left = sub_le_self(
                        &ground_int(left, map)?,
                        &ground_int(right, map)?,
                        h0.proof.clone(),
                    );
                    return Some(Expr::apps(
                        cst("Int.lt_of_le_of_lt"),
                        [
                            ground_int(a, map)?,
                            ground_int(left, map)?,
                            ground_int(b, map)?,
                            a_le_left,
                            left_lt_b,
                        ],
                    ));
                }
            }
        }
    }
    // Upper-bound-then-strict: bound `a` from above by a midpoint `m` (the full
    // additive/sub/mul upper-bound machinery — covers `idx*8 ≤ 24`, `(len-1)-i ≤
    // len-1`), then prove the strict `m < b`. `a ≤ m < b` ⇒ `a < b`
    // (`Int.lt_of_le_of_lt`). The `m < b` step recurses (e.g. `24 < 32` literal,
    // or `len-1 < len` via the predecessor fact above) and `depth` strictly
    // decreases, so it terminates. This is what discharges the guarded shift
    // (`idx*8 ≥ 32` under `idx ≤ 3`) and arithmetic mirror-index VCs.
    if depth > 0 {
        if let Some((m, a_le_m)) = additive_upper_bound(a, hyps, map) {
            if &m != a {
                if let Some(m_lt_b) = prove_lt(&m, b, hyps, map, depth - 1) {
                    return Some(Expr::apps(
                        cst("Int.lt_of_le_of_lt"),
                        [
                            ground_int(a, map)?,
                            ground_int(&m, map)?,
                            ground_int(b, map)?,
                            a_le_m,
                            m_lt_b,
                        ],
                    ));
                }
            }
        }
    }
    // `base + j < b` from a guard `c ≤ b - base` with `j < c` (literals): the
    // index `off + 1` is strictly below `len` when `len - off ≥ 4` (`off + 1 <
    // off + 4 ≤ len`). `base + j < base + c` is `Int.add_lt_add_left`, and
    // `base + c ≤ b` moves the addend across the subtraction (`add_across_le`).
    if let Formula::Add(base, jf) = a {
        if let Formula::Int(j) = &**jf {
            for h in hyps {
                if h.strict {
                    continue;
                }
                let Formula::Sub(a_h, b_h) = &h.hi else { continue };
                if a_h.as_ref() != b || &**b_h != &**base {
                    continue;
                }
                let Formula::Int(c) = &h.lo else { continue };
                if *j >= *c {
                    continue; // need a STRICT gap j < c
                }
                // base + j < base + c   (add_lt_add_left j c (j<c) base)
                let j_lt_c = Expr::apps(
                    cst("Int.NonNeg.mk"),
                    [Expr::nat_lit(u64::try_from(*c - *j - 1).ok()?)],
                );
                let lt_step = Expr::apps(
                    cst("Int.add_lt_add_left"),
                    [ground_int(jf, map)?, ground_int(&h.lo, map)?, j_lt_c, ground_int(base, map)?],
                );
                // base + c ≤ b
                let bc_le_b = add_across_le(
                    &ground_int(b, map)?,
                    &ground_int(base, map)?,
                    &ground_int(&h.lo, map)?,
                    h.proof.clone(),
                );
                let base_c = fold_consts(&Formula::Add(base.clone(), Box::new(h.lo.clone())));
                return Some(Expr::apps(
                    cst("Int.lt_of_lt_of_le"),
                    [
                        ground_int(a, map)?,
                        ground_int(&base_c, map)?,
                        ground_int(b, map)?,
                        lt_step,
                        bc_le_b,
                    ],
                ));
            }
        }
    }
    // Fallback: `Int.lt a b := Int.le (a+1) b` (reducible) — so any proof of
    // `a+1 ≤ b` IS a proof of `a < b` (e.g. `x < x+1` via `le_refl (x+1)`).
    let a_plus_1 = Formula::Add(Box::new(a.clone()), Box::new(Formula::Int(1)));
    derive_le(&a_plus_1, b, hyps, map, depth)
}

/// Variable → de-Bruijn index when under the `n` var-binders, the conjunction
/// binder `h`, and `depth` further case binders. (`vᵢ = #(n - idx + depth)`.)
fn var_map(vars: &[(String, bool)], n: u32, depth: u32) -> HashMap<String, Expr> {
    vars.iter()
        .enumerate()
        .map(|(idx, (v, _))| (v.clone(), Expr::bvar(n - idx as u32 + depth)))
        .collect()
}

/// `a + c ≤ b + d` from `h1 : a ≤ b` and `h2 : c ≤ d` — `Int.add_le_add_right`
/// (`a+c ≤ b+c`) chained with `Int.add_le_add_left` (`b+c ≤ b+d`) by `Int.le_trans`.
fn add_le_add(
    a: &Formula,
    b: &Formula,
    c: &Formula,
    d: &Formula,
    h1: Expr,
    h2: Expr,
    map: &HashMap<String, Expr>,
) -> Option<Expr> {
    let k = |s: &str| Expr::const_(Name::from_string(s), LevelVec::new());
    let add = |x: Expr, y: Expr| Expr::apps(k("Int.add"), [x, y]);
    let (ga, gb, gc, gd) =
        (ground_int(a, map)?, ground_int(b, map)?, ground_int(c, map)?, ground_int(d, map)?);
    // a+c ≤ b+c
    let right = Expr::apps(k("Int.add_le_add_right"), [ga.clone(), gb.clone(), h1, gc.clone()]);
    // b+c ≤ b+d
    let left = Expr::apps(k("Int.add_le_add_left"), [gc.clone(), gd.clone(), h2, gb.clone()]);
    Some(Expr::apps(
        k("Int.le_trans"),
        [add(ga, gc.clone()), add(gb.clone(), gc), add(gb, gd), right, left],
    ))
}

/// `Int.neg x`.
fn neg_e(x: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Int.neg"), LevelVec::new()), x)
}

/// `Eq.subst` over the `NonNeg` motive: from `h : NonNeg x` and `eq : Eq x y`,
/// produce a term of type `NonNeg y`. (`Int.le a b ≡ NonNeg (Int.sub b a)`, so this
/// is how every order fact is transported between def-equal `sub` spellings.)
fn subst_nonneg(x: Expr, y: Expr, eq_xy: Expr, h: Expr) -> Expr {
    let cst = |s: &str| Expr::const_(Name::from_string(s), LevelVec::new());
    let motive = Expr::lam(bd(), int(), Expr::app(cst("Int.NonNeg"), Expr::bvar(0)));
    Expr::apps(
        Expr::const_(Name::from_string("Eq.subst"), vec![Level::succ(Level::zero())]),
        [int(), motive, x, y, eq_xy, h],
    )
}

/// `Eq.trans` over `Int`.
fn eq_trans(a: Expr, b: Expr, c: Expr, p: Expr, q: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.trans"), vec![Level::succ(Level::zero())]),
        [int(), a, b, c, p, q],
    )
}

/// `Int.neg b ≤ Int.zero` from `h : Int.le Int.zero b`. (Negation flips a nonneg
/// to nonpos.) `h : NonNeg (b - 0)`; the goal `neg b ≤ 0 ≡ NonNeg (0 - neg b)`.
/// Transport `h` along `Eq (b - 0) (0 - neg b)` (both reduce to `b`): the first
/// half is `add_zero b` (`b + 0 = b`, def-eq to `b - 0 = b`), the second is
/// `zero_add` ∘ `neg_neg` (`0 - neg b ≡ 0 + neg(neg b) = neg(neg b) = b`). All
/// constructive ⇒ modulo 3. (`b_e` is the grounded `Int` operand.)
fn neg_le_zero(b_e: &Expr, h: Expr) -> Expr {
    let cst = |s: &str| Expr::const_(Name::from_string(s), LevelVec::new());
    let zero = cst("Int.zero");
    let sub = |x: Expr, y: Expr| Expr::apps(cst("Int.sub"), [x, y]);
    let add = |x: Expr, y: Expr| Expr::apps(cst("Int.add"), [x, y]);
    let nnb = neg_e(neg_e(b_e.clone()));
    // half2 : (0 - neg b) = b  via  zero_add (neg neg b) ∘ neg_neg b
    let s0 = sub(zero.clone(), neg_e(b_e.clone()));
    let zero_add_nnb = Expr::app(cst("Int.zero_add"), nnb.clone());
    let neg_neg_b = Expr::app(cst("Int.neg_neg"), b_e.clone());
    let half2 = eq_trans(s0.clone(), nnb, b_e.clone(), zero_add_nnb, neg_neg_b);
    // eq : (b - 0) = (0 - neg b)  via  add_zero b  ∘  symm half2
    let sb0 = sub(b_e.clone(), zero.clone());
    let half1 = Expr::app(cst("Int.add_zero"), b_e.clone()); // (b+0)=b, def-eq (b-0)=b
    let eq = eq_trans(sb0.clone(), b_e.clone(), s0.clone(), half1, eq_symm(&s0, b_e, &half2));
    let _ = add; // (kept for symmetry/readability)
    subst_nonneg(sb0, s0, eq, h)
}

/// `Int.le (Int.add b c) a` from `h : Int.le c (Int.sub a b)` — move the addend
/// `b` across the subtraction (`c ≤ a - b  ⊢  b + c ≤ a`). `h : NonNeg((a-b) - c)`;
/// goal `NonNeg(a - (b+c))`. The two `sub`s are def-equal: `(a-b)-c ≡ (a + -b) + -c`
/// and `a-(b+c) ≡ a + -(b+c)`. Transport `h` along the equality
/// `(a + -b) + -c = a + -(b+c)` built from `Int.add_assoc a (-b) (-c)` (regroup to
/// `a + (-b + -c)`) then `Int.neg_add b c` (rewrite `-b + -c → -(b+c)` under the
/// right summand). Constructive ⇒ modulo 3. Discharges the `len - off ≥ k ⊢
/// off + k ≤ len` step the `s[off+1]` slice-bounds VCs need.
fn add_across_le(a_e: &Expr, b_e: &Expr, c_e: &Expr, h: Expr) -> Expr {
    let cst = |s: &str| Expr::const_(Name::from_string(s), LevelVec::new());
    let l1 = || vec![Level::succ(Level::zero())];
    let add = |x: Expr, y: Expr| Expr::apps(cst("Int.add"), [x, y]);
    let sub = |x: Expr, y: Expr| Expr::apps(cst("Int.sub"), [x, y]);
    let nb = neg_e(b_e.clone());
    let nc = neg_e(c_e.clone());
    let bc = add(b_e.clone(), c_e.clone());
    // lhs = (a + -b) + -c  ≡  (a - b) - c.   target = a + -(b+c)  ≡  a - (b+c).
    let lhs = add(add(a_e.clone(), nb.clone()), nc.clone());
    let target = add(a_e.clone(), neg_e(bc.clone())); // a + -(b+c)
    // assoc : (a + -b) + -c = a + (-b + -c)
    let assoc = Expr::apps(cst("Int.add_assoc"), [a_e.clone(), nb.clone(), nc.clone()]);
    // neg_add b c : -(b+c) = (-b) + (-c).  symm ⇒ (-b + -c) = -(b+c).
    let neg_add = Expr::apps(cst("Int.neg_add"), [b_e.clone(), c_e.clone()]);
    let neg_add_symm = eq_symm(&neg_e(bc.clone()), &add(nb.clone(), nc.clone()), &neg_add);
    // Rewrite the right summand `(-b + -c) → -(b+c)` under `λz. Eq mid (a + z)`,
    // transporting `Eq.refl mid`-free: motive λz. Eq lhs (a + z), from mid to target.
    let motive = Expr::lam(
        bd(),
        int(),
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), l1()),
            [int(), lhs.clone().lift(1), add(a_e.clone().lift(1), Expr::bvar(0))],
        ),
    );
    // eq : lhs = a + -(b+c)  =  Eq.subst motive (mid's right summand) ... applied to `assoc`.
    let eq = Expr::apps(
        Expr::const_(Name::from_string("Eq.subst"), l1()),
        [int(), motive, add(nb.clone(), nc.clone()), neg_e(bc.clone()), neg_add_symm, assoc],
    );
    let _ = sub; // (kept for readability)
    subst_nonneg(lhs, target, eq, h)
}

/// `Int.neg hi ≤ Int.neg lo` from `h : Int.le lo hi`. `h : NonNeg (hi - lo) ≡
/// NonNeg (hi + neg lo)`; goal `neg hi ≤ neg lo ≡ NonNeg (neg lo + neg(neg hi))`.
/// Transport along `Eq (hi + neg lo) (neg lo + neg(neg hi))`: `add_comm` flips to
/// `neg lo + hi`, then `symm(neg_neg hi)` rewrites `hi → neg(neg hi)` under the
/// right summand (`Eq.subst` with an `Eq`-motive). Constructive ⇒ modulo 3.
fn neg_le_neg(hi_e: &Expr, lo_e: &Expr, h: Expr) -> Expr {
    let cst = |s: &str| Expr::const_(Name::from_string(s), LevelVec::new());
    let add = |x: Expr, y: Expr| Expr::apps(cst("Int.add"), [x, y]);
    let l1 = || vec![Level::succ(Level::zero())];
    let nlo = neg_e(lo_e.clone());
    let nnhi = neg_e(neg_e(hi_e.clone()));
    let lhs = add(hi_e.clone(), nlo.clone()); // hi + neg lo
    let comm = Expr::apps(cst("Int.add_comm"), [hi_e.clone(), nlo.clone()]); // (hi+neg lo)=(neg lo+hi)
    // motive λz. Eq (hi + neg lo) (neg lo + z)
    let motive = Expr::lam(
        bd(),
        int(),
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), l1()),
            [int(), lhs.clone().lift(1), add(nlo.clone().lift(1), Expr::bvar(0))],
        ),
    );
    let neg_neg_hi = Expr::app(cst("Int.neg_neg"), hi_e.clone()); // (neg neg hi)=hi
    let eq = Expr::apps(
        Expr::const_(Name::from_string("Eq.subst"), l1()),
        [int(), motive, hi_e.clone(), nnhi.clone(), eq_symm(&nnhi, hi_e, &neg_neg_hi), comm],
    );
    let rhs = add(nlo, nnhi);
    subst_nonneg(lhs, rhs, eq, h)
}

/// `Int.le (Int.sub a b) a` from `h0 : Int.le Int.zero b` (case F2-a). The
/// constant-/var-minuend clamp `a - b ≤ a` when `b ≥ 0` (e.g. `255 - tw`,
/// `u8 tw`). Lift `neg b ≤ 0` to `a + neg b ≤ a + 0` (`add_le_add_left`) then
/// rewrite `a + 0 → a` (`add_zero`); `a + neg b ≡ a - b` by delta. Modulo 3.
fn sub_le_self(a_e: &Expr, b_e: &Expr, h0: Expr) -> Expr {
    let cst = |s: &str| Expr::const_(Name::from_string(s), LevelVec::new());
    let add = |x: Expr, y: Expr| Expr::apps(cst("Int.add"), [x, y]);
    let zero = cst("Int.zero");
    let nlz = neg_le_zero(b_e, h0); // neg b ≤ 0
    // add_le_add_left (neg b) 0 nlz a : (a + neg b) ≤ (a + 0)
    let step = Expr::apps(
        cst("Int.add_le_add_left"),
        [neg_e(b_e.clone()), zero.clone(), nlz, a_e.clone()],
    );
    // transport (a + 0) → a via add_zero a, motive λz. NonNeg(sub z (a + neg b))
    let lhs = add(a_e.clone(), neg_e(b_e.clone()));
    let motive = Expr::lam(
        bd(),
        int(),
        Expr::app(
            cst("Int.NonNeg"),
            Expr::apps(cst("Int.sub"), [Expr::bvar(0), lhs.clone().lift(1)]),
        ),
    );
    let a0 = add(a_e.clone(), zero);
    let add_zero_a = Expr::app(cst("Int.add_zero"), a_e.clone());
    Expr::apps(
        Expr::const_(Name::from_string("Eq.subst"), vec![Level::succ(Level::zero())]),
        [int(), motive, a0, a_e.clone(), add_zero_a, step],
    )
}

/// `Int.le (Int.sub a b) (Int.sub ua lb)` from `h_a : Int.le a ua` and
/// `h_b : Int.le lb b` (case F2-b, two-sided). `a - b ≡ a + neg b`,
/// `ua - lb ≡ ua + neg lb`; combine `h_a` with `neg b ≤ neg lb` (`neg_le_neg`
/// from `h_b`) via the `add_le_add_right` ∘ `add_le_add_left` ∘ `le_trans`
/// chain (same shape as [`add_le_add`]). Modulo 3.
fn sub_le_sub(a_e: &Expr, b_e: &Expr, ua_e: &Expr, lb_e: &Expr, h_a: Expr, h_b: Expr) -> Expr {
    let cst = |s: &str| Expr::const_(Name::from_string(s), LevelVec::new());
    let add = |x: Expr, y: Expr| Expr::apps(cst("Int.add"), [x, y]);
    let hneg = neg_le_neg(b_e, lb_e, h_b); // neg b ≤ neg lb
    // (a + neg b) ≤ (ua + neg b)
    let right = Expr::apps(
        cst("Int.add_le_add_right"),
        [a_e.clone(), ua_e.clone(), h_a, neg_e(b_e.clone())],
    );
    // (ua + neg b) ≤ (ua + neg lb)
    let left = Expr::apps(
        cst("Int.add_le_add_left"),
        [neg_e(b_e.clone()), neg_e(lb_e.clone()), hneg, ua_e.clone()],
    );
    let mid1 = add(a_e.clone(), neg_e(b_e.clone()));
    let mid2 = add(ua_e.clone(), neg_e(b_e.clone()));
    let mid3 = add(ua_e.clone(), neg_e(lb_e.clone()));
    Expr::apps(cst("Int.le_trans"), [mid1, mid2, mid3, right, left])
}

/// Bound a subtraction `f = Sub(left, right)` from above, returning `(m, proof:
/// f ≤ m)`. Two F2 cases: (a) if some hyp gives `0 ≤ right`, then `f ≤ left`
/// (`sub_le_self`); (b) if `left ≤ ua` and `lb ≤ right`, then `f ≤ ua - lb`
/// (`sub_le_sub`), with the bound folded to a literal when both parts are. The
/// two-sided (b) is tried first (tighter when both bounds are present), falling
/// back to (a). Used as a `derive_le` midpoint and by [`additive_upper_bound`].
fn sub_upper_bound(
    f: &Formula,
    hyps: &[Hyp],
    map: &HashMap<String, Expr>,
) -> Option<(Formula, Expr)> {
    let Formula::Sub(left, right) = f else { return None };
    // (b) two-sided: `left ≤ ua` and `lb ≤ right` ⇒ `left - right ≤ ua - lb`. Both
    // bounds must resolve to a literal so the midpoint is a constant (and the
    // self-referential strict violation `left < (left-right)` cannot pose as an
    // upper bound — `operand_upper` only takes NON-strict literal bounds / literals).
    if let (Some((ua, ua_f, h_a)), Some((lb, lb_f, h_b))) =
        (operand_upper(left, hyps, map), operand_lower(right, hyps, map))
    {
        let proof =
            sub_le_sub(&ground_int(left, map)?, &ground_int(right, map)?, &ua, &lb, h_a, h_b);
        let bound = fold_consts(&Formula::Sub(Box::new(ua_f), Box::new(lb_f)));
        return Some((bound, proof));
    }
    // (a) constant-/var-minuend clamp: `0 ≤ right` ⇒ `left - right ≤ left`.
    let nonneg =
        hyps.iter().find(|h| matches!(&h.lo, Formula::Int(0)) && &h.hi == &**right && !h.strict);
    if let Some(h0) = nonneg {
        if let (Some(la), Some(lb_)) = (ground_int(left, map), ground_int(right, map)) {
            let proof = sub_le_self(&la, &lb_, h0.proof.clone());
            return Some((left.as_ref().clone(), proof));
        }
    }
    None
}

/// A literal upper bound `(ub, ub_formula, proof: t ≤ ub)` for a VARIABLE operand
/// `t`: a NON-strict literal hyp `t ≤ ub`. Requiring a VARIABLE (not a literal)
/// operand keeps the resulting `sub_le_sub` proof's `Int.sub`-spelled type def-eq
/// to its `fold_consts` literal midpoint — a literal operand would force the
/// kernel to fold `Int.sub (ofNat a)(ofNat b)` at a lemma-argument position, which
/// it does not (the literal-arg reduction trap). Used by [`sub_upper_bound`] (b)
/// and [`sub_lower_bound`].
fn operand_upper(
    t: &Formula,
    hyps: &[Hyp],
    map: &HashMap<String, Expr>,
) -> Option<(Expr, Formula, Expr)> {
    if matches!(t, Formula::Int(_)) {
        return None;
    }
    let h = hyps.iter().find(|h| &h.lo == t && !h.strict && matches!(h.hi, Formula::Int(_)))?;
    Some((ground_int(&h.hi, map)?, h.hi.clone(), h.proof.clone()))
}

/// A literal lower bound `(lb, lb_formula, proof: lb ≤ t)` for a VARIABLE operand
/// `t`: a NON-strict literal hyp `lb ≤ t`. (See [`operand_upper`] for why a literal
/// operand is rejected.)
fn operand_lower(
    t: &Formula,
    hyps: &[Hyp],
    map: &HashMap<String, Expr>,
) -> Option<(Expr, Formula, Expr)> {
    if matches!(t, Formula::Int(_)) {
        return None;
    }
    let h = hyps.iter().find(|h| &h.hi == t && !h.strict && matches!(h.lo, Formula::Int(_)))?;
    Some((ground_int(&h.lo, map)?, h.lo.clone(), h.proof.clone()))
}

/// Bound a subtraction `f = Sub(left, right)` from BELOW (F2, two-sided lower
/// arm), returning `(m, proof: m ≤ f)`. From a literal lower bound `lb ≤ left`
/// and a literal upper bound `right ≤ ub` we get `lb - ub ≤ left - right`
/// (`sub_le_sub`), the folded literal `lb - ub` being the bound. This discharges
/// the UNDERFLOW arm `left - right < MIN` of a widening difference like
/// `(a as i64) - (b as i64)` (`x - y ≥ i32::MIN - i32::MAX`).
fn sub_lower_bound(
    f: &Formula,
    hyps: &[Hyp],
    map: &HashMap<String, Expr>,
) -> Option<(Formula, Expr)> {
    let Formula::Sub(left, right) = f else { return None };
    let (lb, lb_f, h_l) = operand_lower(left, hyps, map)?;
    let (ub, ub_f, h_u) = operand_upper(right, hyps, map)?;
    // sub_le_sub lb ub left right (h:lb≤left) (h:right≤ub) : (lb - ub) ≤ (left - right)
    let proof = sub_le_sub(&lb, &ub, &ground_int(left, map)?, &ground_int(right, map)?, h_l, h_u);
    let bound = fold_consts(&Formula::Sub(Box::new(lb_f), Box::new(ub_f)));
    Some((bound, proof))
}

/// Recursively compute an upper bound for an additive/constant expression `f`:
/// returns `(bound, proof : f ≤ bound)`. A literal bounds itself (`le_refl`); a sum
/// `a+b` bounds by `ub(a)+ub(b)` (`add_le_add`); a subtraction `a-b` bounds via
/// [`sub_upper_bound`] (F2); any other term (a variable) uses a direct hypothesis
/// `f ≤ m`. The bound is folded to a constant when its parts are. Lets NESTED sums
/// (`a+b+c`, `i+off`, `a*(255-b)`, …) discharge, which single-level lifting can't.
fn additive_upper_bound(
    f: &Formula,
    hyps: &[Hyp],
    map: &HashMap<String, Expr>,
) -> Option<(Formula, Expr)> {
    let cst = |s: &str| Expr::const_(Name::from_string(s), LevelVec::new());
    match f {
        Formula::Int(_) => Some((f.clone(), Expr::app(cst("Int.le_refl"), ground_int(f, map)?))),
        Formula::Add(a, b) => {
            let (ma, pa) = additive_upper_bound(a, hyps, map)?;
            let (mb, pb) = additive_upper_bound(b, hyps, map)?;
            let step = add_le_add(a, &ma, b, &mb, pa, pb, map)?;
            let bound = fold_consts(&Formula::Add(Box::new(ma), Box::new(mb)));
            Some((bound, step))
        }
        // A subtraction inside a sum/product (F2): bound `a-b` by `a` (b≥0) or by
        // `ua-lb` (two-sided), via `sub_upper_bound`.
        Formula::Sub(..) => sub_upper_bound(f, hyps, map),
        // A product `base * c` with `c ≥ 0` a literal: recursively bound `base ≤ mb`
        // then lift to `base*c ≤ mb*c` (`Int.mul_le_mul_of_nonneg_right`), folding
        // the bound to a literal when `mb` is. This is the additive analogue of the
        // `derive_le` mul-lift, surfaced here so a shift amount `idx*8` gets a
        // literal upper bound (`idx ≤ 3 ⇒ idx*8 ≤ 24`) for the strict shift check.
        Formula::Mul(base, cf) => {
            let Formula::Int(c) = &**cf else { return None };
            if *c < 0 {
                return None;
            }
            let cu = u64::try_from(*c).ok()?;
            let (mb, pb) = additive_upper_bound(base, hyps, map)?;
            let zero_le_c = Expr::apps(cst("Int.NonNeg.mk"), [Expr::nat_lit(cu)]);
            let step = Expr::apps(
                cst("Int.mul_le_mul_of_nonneg_right"),
                [
                    ground_int(base, map)?,
                    ground_int(&mb, map)?,
                    ground_int(cf, map)?,
                    pb,
                    zero_le_c,
                ],
            );
            let bound = fold_consts(&Formula::Mul(Box::new(mb), cf.clone()));
            Some((bound, step))
        }
        _ => {
            // Pick the TIGHTEST literal bound `f ≤ m` (a variable can carry both its
            // loose type bound and a tighter computed bound, e.g. `_4 ≤ 2^32-1` AND
            // `_4 ≤ 131070`); the loose one would defeat the additive sum.
            let mut best: Option<&Hyp> = None;
            for h in hyps {
                if &h.lo == f {
                    if let Formula::Int(hi) = h.hi {
                        if best.is_none_or(|b| matches!(&b.hi, Formula::Int(bh) if hi < *bh)) {
                            best = Some(h);
                        }
                    } else if best.is_none() {
                        best = Some(h);
                    }
                }
            }
            let h = best?;
            let pf = if h.strict {
                Expr::apps(
                    cst("Int.le_of_lt"),
                    [ground_int(f, map)?, ground_int(&h.hi, map)?, h.proof.clone()],
                )
            } else {
                h.proof.clone()
            };
            Some((h.hi.clone(), pf))
        }
    }
}

/// `a ≤ b` from `h : a = b`, via `Eq.subst` rewriting `le_refl a : a ≤ a`.
fn le_from_eq(a: &Expr, b: &Expr, eq_proof: &Expr) -> Expr {
    let cst = |s: &str| Expr::const_(Name::from_string(s), LevelVec::new());
    let l1 = || vec![Level::succ(Level::zero())];
    // motive `λz. Int.le a z` (a lifted under the z-binder).
    let motive = Expr::lam(bd(), int(), Expr::apps(cst("Int.le"), [a.lift(1), Expr::bvar(0)]));
    let le_refl_a = Expr::app(cst("Int.le_refl"), a.clone());
    Expr::apps(
        Expr::const_(Name::from_string("Eq.subst"), l1()),
        [int(), motive, a.clone(), b.clone(), eq_proof.clone(), le_refl_a],
    )
}

/// `b = a` from `h : a = b`.
fn eq_symm(a: &Expr, b: &Expr, eq_proof: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.symm"), vec![Level::succ(Level::zero())]),
        [int(), a.clone(), b.clone(), eq_proof.clone()],
    )
}

/// `Int.lt (Int.sub base k) base` for a literal `k ≥ 1` — the strict predecessor
/// fact `base - k < base`. (`base_e` is the grounded `Int` minuend.) Built from
/// the literal strict `-k < 0` (`Int.NonNeg.mk (k-1)`) lifted by `base` via
/// `Int.add_lt_add_right`, then both summands transported to the canonical
/// `sub` spelling: the RHS `0 + base → base` (`Int.zero_add`) and the LHS
/// `(-k) + base → base + (-k)` (`Int.add_comm`), with `base + (-k) ≡ base - k`
/// by delta. Constructive ⇒ modulo 3. Discharges the `len - 1 < len` /
/// `(len-1)-i < len` strict step the slice-mirror / last-index VCs need.
fn lt_sub_lit(base_e: &Expr, k: i128) -> Option<Expr> {
    if k < 1 {
        return None;
    }
    let cst = |s: &str| Expr::const_(Name::from_string(s), LevelVec::new());
    let l1 = || vec![Level::succ(Level::zero())];
    let add = |x: Expr, y: Expr| Expr::apps(cst("Int.add"), [x, y]);
    // `-k` and `0` as Int literals (clean's native reducer folds these).
    let neg_k = int_lit(-k);
    let zero = int_lit(0);
    // `-k < 0`  ≡  NonNeg(0 - (-k + 1)) = NonNeg(k-1).  k ≥ 1 ⇒ k-1 ≥ 0.
    let diff = u64::try_from(k - 1).ok()?;
    let neg_k_lt_0 = Expr::apps(cst("Int.NonNeg.mk"), [Expr::nat_lit(diff)]);
    // add_lt_add_right (-k) 0 (h:-k<0) base : (-k + base) < (0 + base)
    let raw = Expr::apps(
        cst("Int.add_lt_add_right"),
        [neg_k.clone(), zero.clone(), neg_k_lt_0, base_e.clone()],
    );
    // Transport RHS `0 + base → base` via `Int.zero_add base`. Motive λz. lt (-k+base) z.
    let lhs0 = add(neg_k.clone(), base_e.clone());
    let zero_base = add(zero, base_e.clone());
    let zero_add = Expr::app(cst("Int.zero_add"), base_e.clone());
    let motive_r =
        Expr::lam(bd(), int(), Expr::apps(cst("Int.lt"), [lhs0.clone().lift(1), Expr::bvar(0)]));
    let mid = Expr::apps(
        Expr::const_(Name::from_string("Eq.subst"), l1()),
        [int(), motive_r, zero_base, base_e.clone(), zero_add, raw],
    );
    // Transport LHS `(-k) + base → base + (-k)` via `Int.add_comm (-k) base`.
    // Motive λz. lt z base.  Result type `lt (base + (-k)) base ≡ lt (base - k) base`.
    let base_neg_k = add(base_e.clone(), neg_k.clone());
    let add_comm = Expr::apps(cst("Int.add_comm"), [neg_k, base_e.clone()]);
    let motive_l =
        Expr::lam(bd(), int(), Expr::apps(cst("Int.lt"), [Expr::bvar(0), base_e.clone().lift(1)]));
    Some(Expr::apps(
        Expr::const_(Name::from_string("Eq.subst"), l1()),
        [int(), motive_l, lhs0, base_neg_k, add_comm, mid],
    ))
}

/// An `Int` literal as a kernel `Expr` (`Int.ofNat`/`Int.negSucc`), matching
/// [`crate::clean_ground::ground_int`]'s encoding.
fn int_lit(k: i128) -> Expr {
    let cst = |s: &str| Expr::const_(Name::from_string(s), LevelVec::new());
    // Trust: EXACT ENCODING (2026-07-24) — `Expr::nat_lit_u128` covers the FULL
    // magnitude range. The former `as u64` was `n mod 2^64`, a SILENT TRUNCATION that
    // made this map NON-INJECTIVE and caused a demonstrated LIVE FALSE ACCEPT (see
    // `clean_ground::int_lit_to_expr`). Byte-identity with the other encoders is
    // PRESERVED, and so is every existing term: `BigNat::from_limbs` normalizes a
    // trailing zero limb back to `BigNat::Small`, so `nat_lit_u128(k) == nat_lit(k)`
    // for every `k <= u64::MAX` (asserted by `int_lit_encoders_agree_and_are_exact`).
    // `Int.negSucc` carries `|n| - 1`, which fits `u128` for every `i128` (including
    // `i128::MIN`, where `-n` is not representable).
    if k >= 0 {
        Expr::app(cst("Int.ofNat"), Expr::nat_lit_u128(k.unsigned_abs()))
    } else {
        Expr::app(cst("Int.negSucc"), Expr::nat_lit_u128(k.unsigned_abs() - 1))
    }
}

/// `q == p + 1` (in either `Add` orientation) — the `le_self_add_one` step.
fn is_succ(q: &Formula, p: &Formula) -> bool {
    let one = Formula::Int(1);
    matches!(q, Formula::Add(a, b)
        if (**a == *p && **b == one) || (**b == *p && **a == one))
}

/// Derive a kernel proof of `Int.le p q` from the hypotheses by bounded linear
/// reasoning: reflexivity, a direct `p ≤ q` (or `p < q` weakened), the successor
/// step `p ≤ p+1` (`Int.le_self_add_one`), and `Int.le_trans` chains through
/// hypothesis/successor midpoints. This is the Farkas step overflow VCs need
/// (e.g. `lo ≤ x ⊢ lo ≤ x+1`). All lemmas are constructive ⇒ modulo 3.
/// Constant-fold `Add`/`Sub`/`Mul` of integer literals (so `255+1` becomes `256`,
/// enabling literal comparisons). Variables are left untouched.
fn fold_consts(f: &Formula) -> Formula {
    use trust_types::Formula as F;
    // Trust: machine-integer VCs can carry literals as large as `usize::MAX`
    // (e.g. a `row > usize::MAX / cols` index guard). Folding with raw `i128`
    // arithmetic overflows and panics — use CHECKED ops and leave the node
    // unfolded on overflow rather than fabricate a wrong constant (sound: we only
    // ever replace `op(lit, lit)` by its exact value).
    let bin =
        |a: F, b: F, lit: fn(i128, i128) -> Option<i128>, mk: fn(Box<F>, Box<F>) -> F| match (a, b)
        {
            (F::Int(x), F::Int(y)) => match lit(x, y) {
                Some(v) => F::Int(v),
                None => mk(Box::new(F::Int(x)), Box::new(F::Int(y))),
            },
            (a, b) => mk(Box::new(a), Box::new(b)),
        };
    match f {
        F::Add(a, b) => bin(fold_consts(a), fold_consts(b), i128::checked_add, F::Add),
        F::Sub(a, b) => bin(fold_consts(a), fold_consts(b), i128::checked_sub, F::Sub),
        F::Mul(a, b) => bin(fold_consts(a), fold_consts(b), i128::checked_mul, F::Mul),
        other => other.clone(),
    }
}

pub(crate) fn derive_le(
    p: &Formula,
    q: &Formula,
    hyps: &[Hyp],
    map: &HashMap<String, Expr>,
    depth: u32,
) -> Option<Expr> {
    let cst = |s: &str| Expr::const_(Name::from_string(s), LevelVec::new());
    let p = &fold_consts(p);
    let q = &fold_consts(q);
    if p == q {
        return Some(Expr::app(cst("Int.le_refl"), ground_int(p, map)?));
    }
    // Literal ≤ literal: `Int.le c1 c2 := Int.NonNeg (c2 - c1)`; for `c1 ≤ c2` the
    // difference is a nonneg literal witnessed by `Int.NonNeg.mk`. For `c1 > c2`
    // fall through — the (false) bound may still be *derivable* through the
    // hypotheses, which signals they are contradictory.
    if let (Formula::Int(pc), Formula::Int(qc)) = (p, q) {
        if pc <= qc {
            // Clean's native Int reducer reduces `Int.le` for literal magnitudes up
            // to `u64::MAX`; beyond that it declines, so refuse to emit a proof the
            // kernel would reject (it would surface as a rejection rather than a clean
            // fall-through). Such bounds — only u128-overflow thresholds in practice —
            // fall through to AY.
            const KERNEL_INT_LIT_BOUND: i128 = u64::MAX as i128;
            if *pc < -KERNEL_INT_LIT_BOUND || *qc > KERNEL_INT_LIT_BOUND {
                return None;
            }
            if let Ok(diff) = u64::try_from(qc - pc) {
                return Some(Expr::apps(cst("Int.NonNeg.mk"), [Expr::nat_lit(diff)]));
            }
            return None;
        }
    }
    for h in hyps {
        if &h.lo == p && &h.hi == q {
            return Some(if h.strict {
                Expr::apps(
                    cst("Int.le_of_lt"),
                    [ground_int(p, map)?, ground_int(q, map)?, h.proof.clone()],
                )
            } else {
                h.proof.clone()
            });
        }
    }
    // `0 ≤ left - right` from a hypothesis `right ≤ left` (subtraction-underflow
    // guard, e.g. `if a >= b { a - b }`). `h : Int.le right left` is `NonNeg(left-right)`;
    // the goal `Int.le 0 (left-right)` is `NonNeg((left-right) - 0)`. Since
    // `(left-right) - 0 ≡ (left-right) + 0` (Int.neg 0 reduces) and `Int.add_zero`
    // proves `(left-right) + 0 = (left-right)`, transport `h` along that equality
    // under the `NonNeg` motive via `Eq.subst`. No kernel reduction change.
    if matches!(p, Formula::Int(0)) {
        if let Formula::Sub(left, right) = q {
            for h in hyps {
                if h.lo == **right && h.hi == **left && !h.strict {
                    let x = ground_int(q, map)?; // Int.sub left right
                    let add_x_zero = Expr::apps(cst("Int.add"), [x.clone(), cst("Int.zero")]);
                    let add_zero_x = Expr::app(cst("Int.add_zero"), x.clone());
                    let eq = eq_symm(&add_x_zero, &x, &add_zero_x); // x = x + 0
                    let motive =
                        Expr::lam(bd(), int(), Expr::app(cst("Int.NonNeg"), Expr::bvar(0)));
                    return Some(Expr::apps(
                        Expr::const_(
                            Name::from_string("Eq.subst"),
                            vec![Level::succ(Level::zero())],
                        ),
                        [int(), motive, x.clone(), add_x_zero, eq, h.proof.clone()],
                    ));
                }
            }
        }
    }
    // `b + j ≤ a` (j a literal) from a hypothesis `j' ≤ a - b` with `j ≤ j'`
    // literal: `b + j ≤ b + j' ≤ a`. The `b + j' ≤ a` step moves the addend across
    // the subtraction (`add_across_le`); `b + j ≤ b + j'` is `add_le_add_left`. This
    // is what an `s[off + 1]` index check needs under the guard `len - off ≥ 4`
    // (`off + 1 ≤ off + 4 ≤ len`). Guarded on `j ≥ 0` so the literal grounding and
    // the `j ≤ j'` ordering stay in the nonneg fragment the helpers assume.
    if let Formula::Add(b, jf) = p {
        if let Formula::Int(j) = &**jf {
            if *j >= 0 {
                for h in hyps {
                    if h.strict {
                        continue;
                    }
                    let Formula::Sub(a_h, b_h) = &h.hi else { continue };
                    if &**b_h != &**b || a_h.as_ref() != q {
                        continue;
                    }
                    let Formula::Int(jp) = &h.lo else { continue };
                    if *jp < *j {
                        continue;
                    }
                    // bc_le_a : b + j' ≤ a   (move addend across)
                    let bc_le_a = add_across_le(
                        &ground_int(q, map)?,
                        &ground_int(b, map)?,
                        &ground_int(&h.lo, map)?,
                        h.proof.clone(),
                    );
                    if *jp == *j {
                        return Some(bc_le_a); // b + j ≤ a directly
                    }
                    // bj_le_bjp : (b + j) ≤ (b + j')  via add_le_add_left j j' (j≤j') b.
                    // `j ≤ j'` is the literal nonneg-difference proof `NonNeg.mk (j'-j)`.
                    let j_le_jp = Expr::apps(
                        cst("Int.NonNeg.mk"),
                        [Expr::nat_lit(u64::try_from(*jp - *j).ok()?)],
                    );
                    let bj_le_bjp = Expr::apps(
                        cst("Int.add_le_add_left"),
                        [
                            ground_int(jf, map)?,
                            ground_int(&h.lo, map)?,
                            j_le_jp,
                            ground_int(b, map)?,
                        ],
                    );
                    let bjp = fold_consts(&Formula::Add(b.clone(), Box::new(h.lo.clone())));
                    return Some(Expr::apps(
                        cst("Int.le_trans"),
                        [
                            ground_int(p, map)?,
                            ground_int(&bjp, map)?,
                            ground_int(q, map)?,
                            bj_le_bjp,
                            bc_le_a,
                        ],
                    ));
                }
            }
        }
    }
    // `p ≤ left - right` (F2 two-sided lower arm): bound the difference from below
    // by `lb - ub` (`sub_lower_bound`) and chain `p ≤ lb-ub ≤ left-right`. Discharges
    // the underflow arm `MIN ≤ (a as i64) - (b as i64)` of an `abs_diff`-style VC.
    if matches!(q, Formula::Sub(..)) && depth > 0 {
        if let Some((bound, bound_le_q)) = sub_lower_bound(q, hyps, map) {
            if &bound != q {
                if let Some(p_le_bound) = derive_le(p, &bound, hyps, map, depth - 1) {
                    return Some(Expr::apps(
                        cst("Int.le_trans"),
                        [
                            ground_int(p, map)?,
                            ground_int(&bound, map)?,
                            ground_int(q, map)?,
                            p_le_bound,
                            bound_le_q,
                        ],
                    ));
                }
            }
        }
    }
    // `base + 1 ≤ q` from a STRICT hypothesis `base < q`: by definition
    // `Int.lt base q := Int.le (Int.add base 1) q`, so the strict proof IS the goal
    // (discharges the overflow arm of a signed `x+1` guarded by `x < MAX`).
    if let Formula::Add(base, kf) = p {
        if matches!(**kf, Formula::Int(1)) {
            for h in hyps {
                if h.strict && h.lo == **base && h.hi == *q {
                    return Some(h.proof.clone());
                }
            }
        }
    }
    if is_succ(q, p) {
        return Some(Expr::app(cst("Int.le_self_add_one"), ground_int(p, map)?));
    }
    if depth == 0 {
        return None;
    }
    // `p ≤ base - 1` from a STRICT hyp `p < base`. The `1` is spelled in the canonical
    // `Int.ofNat (Nat.succ Nat.zero)` form that `Int.lt`'s definition uses, so the
    // strict proof `h : Int.lt p base ≡ Int.le (p+1) base` matches `add_le_add_right`'s
    // expected argument type syntactically (the arg-position def-eq does not reduce
    // `nat-literal 1 ≡ Nat.succ Nat.zero` the way a goal position does).
    if let Formula::Sub(base, kf) = q {
        if matches!(**kf, Formula::Int(1)) {
            for h in hyps {
                if h.strict && h.lo == *p && h.hi == **base {
                    let p_e = ground_int(p, map)?;
                    let base_e = ground_int(base, map)?;
                    let one =
                        Expr::app(cst("Int.ofNat"), Expr::app(cst("Nat.succ"), cst("Nat.zero")));
                    let neg = Expr::app(cst("Int.neg"), one.clone());
                    let p1 = Expr::apps(cst("Int.add"), [p_e.clone(), one.clone()]);
                    let step = Expr::apps(
                        cst("Int.add_le_add_right"),
                        [p1.clone(), base_e.clone(), h.proof.clone(), neg.clone()],
                    );
                    let lhs = Expr::apps(cst("Int.add"), [p1, neg.clone()]);
                    let cancel = Expr::apps(cst("Int.add_neg_cancel_right"), [p_e.clone(), one]);
                    let base_plus = Expr::apps(cst("Int.add"), [base_e.lift(1), neg.lift(1)]);
                    let motive = Expr::lam(
                        bd(),
                        int(),
                        Expr::apps(cst("Int.le"), [Expr::bvar(0), base_plus]),
                    );
                    return Some(Expr::apps(
                        Expr::const_(
                            Name::from_string("Eq.subst"),
                            vec![Level::succ(Level::zero())],
                        ),
                        [int(), motive, lhs, p_e, cancel, step],
                    ));
                }
            }
        }
    }
    // `base - 1 ≤ q` (q a literal) via `base-1 ≤ q-1 ≤ q`: shift `base ≤ q` by the
    // LITERAL `-1` (`negSucc 0`, which the native reducers fold) using
    // `add_le_add_right`, giving `base-1 ≤ q-1` (the literal `q + (-1)` reduces to
    // `q-1`), then the literal `q-1 ≤ q`, chained by `le_trans`. (`-1` is the literal
    // form here — not the canonical `Int.neg 1` — since this arm passes the already-
    // `Int.le` `base ≤ q`, so there is no `Int.lt`-vs-`Int.le` arg mismatch, and the
    // literal `-1` is what reduces.) Discharges the overflow arm `x-1 > MAX`.
    if let Formula::Sub(base, kf) = p {
        if matches!(**kf, Formula::Int(1)) {
            if let Formula::Int(qc) = q {
                if let Some(base_le_q) = derive_le(base, q, hyps, map, depth - 1) {
                    let base_e = ground_int(base, map)?;
                    let q_e = ground_int(q, map)?;
                    let neg1 = ground_int(&Formula::Int(-1), map)?;
                    let step = Expr::apps(
                        cst("Int.add_le_add_right"),
                        [base_e.clone(), q_e.clone(), base_le_q, neg1.clone()],
                    );
                    let base_minus = Expr::apps(cst("Int.add"), [base_e, neg1]);
                    // Use the LITERAL `q-1` as the `le_trans` midpoint: `step`'s RHS
                    // `q + (-1)` reduces to it, and it matches `qm1_le_q`'s LHS exactly
                    // (whereas the unreduced `Int.add q (-1)` blocks `Int.sub`'s fold).
                    let q_minus_1 = Formula::Int(qc - 1);
                    let qm1_e = ground_int(&q_minus_1, map)?;
                    let qm1_le_q = derive_le(&q_minus_1, q, hyps, map, depth - 1)?;
                    return Some(Expr::apps(
                        cst("Int.le_trans"),
                        [base_minus, qm1_e, q_e, step, qm1_le_q],
                    ));
                }
            }
        }
    }
    // `p ≤ base + 1` via `p ≤ base ≤ base+1` (`Int.le_self_add_one` + `le_trans`) —
    // discharges the underflow arm `MIN ≤ x+1` from the range bound `MIN ≤ x`.
    if let Formula::Add(base, kf) = q {
        if matches!(**kf, Formula::Int(1)) {
            if let Some(p_le_base) = derive_le(p, base, hyps, map, depth - 1) {
                let base_le_succ = Expr::app(cst("Int.le_self_add_one"), ground_int(base, map)?);
                return Some(Expr::apps(
                    cst("Int.le_trans"),
                    [
                        ground_int(p, map)?,
                        ground_int(base, map)?,
                        ground_int(q, map)?,
                        p_le_base,
                        base_le_succ,
                    ],
                ));
            }
        }
    }
    // `p ≤ left + right` from LOWER bounds `la ≤ left`, `lb ≤ right`: derive
    // `la+lb ≤ left+right` (`add_le_add`) and chain `p ≤ la+lb ≤ left+right`.
    // Discharges the underflow arm `MIN ≤ a+b` of a signed two-variable add.
    if let Formula::Add(left, right) = q {
        if !matches!(**right, Formula::Int(1)) {
            let lower = |side: &Formula, h: &Hyp| -> Option<(Formula, Expr)> {
                (&h.hi == side).then(|| {
                    let pf = if h.strict {
                        Expr::apps(
                            cst("Int.le_of_lt"),
                            [
                                ground_int(&h.lo, map).unwrap(),
                                ground_int(side, map).unwrap(),
                                h.proof.clone(),
                            ],
                        )
                    } else {
                        h.proof.clone()
                    };
                    (h.lo.clone(), pf)
                })
            };
            for hl in hyps {
                let Some((la, la_le)) = lower(left, hl) else { continue };
                for hr in hyps {
                    let Some((lb, lb_le)) = lower(right, hr) else { continue };
                    let Some(step) = add_le_add(&la, left, &lb, right, la_le.clone(), lb_le, map)
                    else {
                        continue;
                    };
                    let lsum =
                        fold_consts(&Formula::Add(Box::new(la.clone()), Box::new(lb.clone())));
                    if let Some(p_le_lsum) = derive_le(p, &lsum, hyps, map, depth - 1) {
                        return Some(Expr::apps(
                            cst("Int.le_trans"),
                            [
                                ground_int(p, map)?,
                                ground_int(&lsum, map)?,
                                ground_int(q, map)?,
                                p_le_lsum,
                                step,
                            ],
                        ));
                    }
                }
            }
        }
    }
    // `0 ≤ base*c` from `0 ≤ base` and `0 ≤ c` (`Int.mul_nonneg`) — the lower
    // (underflow) bound of an unsigned `base*c`.
    if let (Formula::Int(0), Formula::Mul(base, cf)) = (p, q) {
        if let Formula::Int(c) = &**cf {
            if *c >= 0 {
                if let (Some(zero_le_base), Ok(cu)) =
                    (derive_le(&Formula::Int(0), base, hyps, map, depth - 1), u64::try_from(*c))
                {
                    let zero_le_c = Expr::apps(cst("Int.NonNeg.mk"), [Expr::nat_lit(cu)]);
                    return Some(Expr::apps(
                        cst("Int.mul_nonneg"),
                        [ground_int(base, map)?, ground_int(cf, map)?, zero_le_base, zero_le_c],
                    ));
                }
            }
        }
    }
    // Midpoints `m` with a proof of `p ≤ m`: hypotheses `p ≤/< m`, `p ≤ p+1`, and
    // (when `p = base + k`) the monotone lift `base ≤ m ⊢ base+k ≤ m+k`.
    let mut mids: Vec<(Formula, Expr)> = Vec::new();
    for h in hyps {
        if &h.lo == p {
            let p_le_m = if h.strict {
                Expr::apps(
                    cst("Int.le_of_lt"),
                    [ground_int(p, map)?, ground_int(&h.hi, map)?, h.proof.clone()],
                )
            } else {
                h.proof.clone()
            };
            mids.push((h.hi.clone(), p_le_m));
        }
    }
    if let Formula::Add(base, kf) = p {
        if matches!(**kf, Formula::Int(_)) {
            for h in hyps {
                if &h.lo == &**base {
                    let base_le_m = if h.strict {
                        Expr::apps(
                            cst("Int.le_of_lt"),
                            [ground_int(base, map)?, ground_int(&h.hi, map)?, h.proof.clone()],
                        )
                    } else {
                        h.proof.clone()
                    };
                    // add_le_add_right base m (base≤m) k : (base+k) ≤ (m+k)
                    let step = Expr::apps(
                        cst("Int.add_le_add_right"),
                        [
                            ground_int(base, map)?,
                            ground_int(&h.hi, map)?,
                            base_le_m,
                            ground_int(kf, map)?,
                        ],
                    );
                    let m_plus_k = fold_consts(&Formula::Add(Box::new(h.hi.clone()), kf.clone()));
                    mids.push((m_plus_k, step));
                }
            }
        }
    }
    // If `p` is a sum (possibly NESTED, e.g. `a+b+c`, `i+off`), bound it by the sum
    // of its parts' upper bounds via `additive_upper_bound` (recursive `add_le_add`),
    // giving `p ≤ Σ bounds`. Handles multi-term additive overflow VCs that single-
    // level lifting can't reach.
    if matches!(p, Formula::Add(..)) {
        if let Some((bound, p_le_bound)) = additive_upper_bound(p, hyps, map) {
            mids.push((bound, p_le_bound));
        }
    }
    // If `p` is a subtraction `a-b` (F2): bound it above by `a` (when `b ≥ 0`) or
    // by `ua-lb` (two-sided), via `sub_upper_bound` — discharges overflow arms over
    // a clamp like `255 - tw` or `b - a`.
    if matches!(p, Formula::Sub(..)) {
        if let Some((bound, p_le_bound)) = sub_upper_bound(p, hyps, map) {
            mids.push((bound, p_le_bound));
        }
    }
    // If `p = base * c` (c a nonneg literal), lift `base ≤ m` to `base*c ≤ m*c`.
    if let Formula::Mul(base, cf) = p {
        if let Formula::Int(c) = &**cf {
            if *c >= 0 {
                if let Ok(cu) = u64::try_from(*c) {
                    for h in hyps {
                        if &h.lo == &**base {
                            let base_le_m = if h.strict {
                                Expr::apps(
                                    cst("Int.le_of_lt"),
                                    [
                                        ground_int(base, map)?,
                                        ground_int(&h.hi, map)?,
                                        h.proof.clone(),
                                    ],
                                )
                            } else {
                                h.proof.clone()
                            };
                            // 0 ≤ c (literal) and mul_le_mul_of_nonneg_right.
                            let zero_le_c = Expr::apps(cst("Int.NonNeg.mk"), [Expr::nat_lit(cu)]);
                            let step = Expr::apps(
                                cst("Int.mul_le_mul_of_nonneg_right"),
                                [
                                    ground_int(base, map)?,
                                    ground_int(&h.hi, map)?,
                                    ground_int(cf, map)?,
                                    base_le_m,
                                    zero_le_c,
                                ],
                            );
                            let m_times_c =
                                fold_consts(&Formula::Mul(Box::new(h.hi.clone()), cf.clone()));
                            mids.push((m_times_c, step));
                        }
                    }
                }
            }
        }
    }
    // If `p = left * right` (both non-constant), lift `left≤ml ∧ right≤mr ∧ 0≤left ∧
    // 0≤right` to `left*right ≤ ml*mr` via `Int.mul_le_mul`. This is what discharges a
    // bounded two-variable multiplication-overflow VC (e.g. a widening `u16*u16`).
    if let Formula::Mul(left, right) = p {
        let non_const = |f: &Formula| !matches!(f, Formula::Int(_));
        if non_const(left) && non_const(right) {
            let le_of = |h: &Hyp| -> Option<Expr> {
                if h.strict {
                    Some(Expr::apps(
                        cst("Int.le_of_lt"),
                        [ground_int(&h.lo, map)?, ground_int(&h.hi, map)?, h.proof.clone()],
                    ))
                } else {
                    Some(h.proof.clone())
                }
            };
            // For a factor `t`, find `(upper_bound, proof: t ≤ ub)`: a direct hyp, or
            // — for a `Sub` factor (F2) like `255 - tw` — `sub_upper_bound`.
            let upper = |t: &Formula| -> Option<(Formula, Expr)> {
                if let Some(h) = hyps.iter().find(|h| &h.lo == t) {
                    return Some((h.hi.clone(), le_of(h)?));
                }
                if matches!(t, Formula::Sub(..)) {
                    return sub_upper_bound(t, hyps, map);
                }
                None
            };
            // For a factor `t`, a proof of `0 ≤ t`: a direct hyp, or — for a `Sub`
            // factor — the existing `0 ≤ a-b` derivation (via `derive_le`).
            let nonneg = |t: &Formula| -> Option<Expr> {
                if let Some(h) = hyps
                    .iter()
                    .find(|h| matches!(&h.lo, Formula::Int(0)) && &h.hi == t && !h.strict)
                {
                    return Some(h.proof.clone());
                }
                if matches!(t, Formula::Sub(..)) {
                    return derive_le(&Formula::Int(0), t, hyps, map, depth.saturating_sub(1));
                }
                None
            };
            if let (Some((ml, pul)), Some((mr, pur)), Some(pnl), Some(pnr)) =
                (upper(left), upper(right), nonneg(left), nonneg(right))
            {
                // Int.mul_le_mul a b c d : a≤b → c≤d → 0≤a → 0≤c → a*c ≤ b*d
                let step = Expr::apps(
                    cst("Int.mul_le_mul"),
                    [
                        ground_int(left, map)?,
                        ground_int(&ml, map)?,
                        ground_int(right, map)?,
                        ground_int(&mr, map)?,
                        pul,
                        pur,
                        pnl,
                        pnr,
                    ],
                );
                let mid = fold_consts(&Formula::Mul(Box::new(ml), Box::new(mr)));
                mids.push((mid, step));
            }
        }
    }
    let succ = Formula::Add(Box::new(p.clone()), Box::new(Formula::Int(1)));
    mids.push((succ, Expr::app(cst("Int.le_self_add_one"), ground_int(p, map)?)));

    for (m, p_le_m) in mids {
        if &m == p {
            continue;
        }
        if let Some(m_le_q) = derive_le(&m, q, hyps, map, depth - 1) {
            return Some(Expr::apps(
                cst("Int.le_trans"),
                [ground_int(p, map)?, ground_int(&m, map)?, ground_int(q, map)?, p_le_m, m_le_q],
            ));
        }
    }
    None
}

/// Find a strict `x < y` and derive the opposite `y ≤ x` by linear reasoning,
/// building the `False` proof via the lt/le contradiction core; failing that,
/// detect a derivable false literal bound `c1 ≤ c2` (`c1 > c2`).
fn build_contradiction(hyps: &[Hyp], map: &HashMap<String, Expr>) -> Option<Expr> {
    let cst = |s: &str| Expr::const_(Name::from_string(s), LevelVec::new());
    for a in hyps {
        if !a.strict || a.lo == a.hi {
            continue; // anchor on a genuine strict `x < y`
        }
        if let Some(le) = derive_le(&a.hi, &a.lo, hyps, map, 3) {
            // a : x < y ;  le : y ≤ x   ⇒   x < x   ⇒   False
            let x = ground_int(&a.lo, map)?;
            let y = ground_int(&a.hi, map)?;
            return Some(Expr::apps(lt_le_contradiction_proof(), [x, y, a.proof.clone(), le]));
        }
    }
    // Non-strict anchor: a hypothesis `lo ≤ hi` whose REVERSE strict `hi < lo` is
    // independently provable contradicts itself (`hi < lo ≤ hi ⇒ hi < hi`). This is
    // the dual of the strict-anchor cycle above, and is exactly the shape the
    // ShiftOverflow (`32 ≤ idx*8` with `idx*8 < 32` from `idx ≤ 3`) and arithmetic
    // SliceBoundsCheck (`len ≤ len-1` with `len-1 < len`; `len ≤ (len-1)-i` with
    // `(len-1)-i < len`) violations take — the violation atom `idx ≥ width` /
    // `mirror ≥ len` normalizes to a NON-strict `lo ≤ hi`, not a strict atom.
    for a in hyps {
        if a.strict || a.lo == a.hi {
            continue;
        }
        if let Some(hi_lt_lo) = prove_lt(&a.hi, &a.lo, hyps, map, 4) {
            // a : lo ≤ hi ;  hi_lt_lo : hi < lo
            // lt_of_lt_of_le hi lo hi (hi<lo) (lo≤hi) : hi < hi ; lt_irrefl hi _ : False
            let lo = ground_int(&a.lo, map)?;
            let hi = ground_int(&a.hi, map)?;
            let lt_hihi = Expr::apps(
                cst("Int.lt_of_lt_of_le"),
                [hi.clone(), lo, hi.clone(), hi_lt_lo, a.proof.clone()],
            );
            return Some(Expr::apps(cst("Int.lt_irrefl"), [hi, lt_hihi]));
        }
    }
    // No strict atom closed a cycle: look for a derivable FALSE literal bound
    // `c1 ≤ c2` with `c1 > c2` (then `c2 < c1 ≤ c2 ⇒ c2 < c2`). The literals come
    // from the hypotheses (e.g. an `Eq`-bound chain forcing `1 ≤ 0`).
    let mut lits: Vec<i128> = Vec::new();
    for h in hyps {
        for f in [&h.lo, &h.hi] {
            if let Formula::Int(k) = f {
                if !lits.contains(k) {
                    lits.push(*k);
                }
            }
        }
    }
    for &c1 in &lits {
        for &c2 in &lits {
            if c1 <= c2 {
                continue;
            }
            let (p, q) = (Formula::Int(c1), Formula::Int(c2));
            if let (Some(c1_le_c2), Some(c2_lt_c1)) =
                (derive_le(&p, &q, hyps, map, 3), prove_lt(&q, &p, hyps, map, 3))
            {
                // lt_of_lt_of_le c2 c1 c2 (c2<c1) (c1≤c2) : c2 < c2 ; lt_irrefl c2 _ : False
                let (pe, qe) = (ground_int(&p, map)?, ground_int(&q, map)?);
                let lt_qq = Expr::apps(
                    cst("Int.lt_of_lt_of_le"),
                    [qe.clone(), pe, qe.clone(), c2_lt_c1, c1_le_c2],
                );
                return Some(Expr::apps(cst("Int.lt_irrefl"), [qe, lt_qq]));
            }
        }
    }
    None
}

/// A propositional hypothesis carried through the recursive refutation: its
/// `formula` together with a kernel `proof` term of that formula, valid under the
/// CURRENT binder depth. Unlike the flat-`atoms` projection path, props let the
/// engine recurse through nested `And`/`Or` (clamp VCs nest the BV-overflow / `Ite`
/// case-split arbitrarily deep) by carrying each hypothesis's proof explicitly.
struct Prop {
    formula: Formula,
    proof: Expr,
}

/// Deterministic work cap for propositional case splitting. Real guarded VCs
/// nest only a handful of disjunctions; allowing an unbounded Cartesian
/// expansion made one large body consume a worker indefinitely. Exhaustion is
/// fail-closed (`None`), leaving the obligation for another verifier lane.
const REFUTE_SEARCH_FUEL: usize = 16_384;

/// Lift every carried prop proof by `amount` loose-bvar levels — applied when the
/// engine descends under a fresh `Or.rec` binder so the existing props stay valid
/// in the deeper context.
fn lift_props(props: &[Prop], amount: u32) -> Vec<Prop> {
    props.iter().map(|p| Prop { formula: p.formula.clone(), proof: p.proof.lift(amount) }).collect()
}

/// Flatten a prop list: replace each `And(v)` prop with its projected conjuncts
/// (`And.left`/`And.right` over the prop's own proof), drop trivially-`true`
/// props, to a fixpoint. Leaves comparisons / equalities / `Not` / `Or` / `Bool`
/// as atomic props. Aux-temp `Eq` definitions surviving inside a disjunct are kept
/// as ordinary equality hypotheses (they feed the linear engine).
fn flatten_props(props: Vec<Prop>, map: &HashMap<String, Expr>) -> Option<Vec<Prop>> {
    let mut out: Vec<Prop> = Vec::new();
    let mut work = props;
    while let Some(p) = work.pop() {
        match &p.formula {
            Formula::And(v) => {
                // Project each conjunct of `And(v)` out of `p.proof`.
                for (i, conj) in v.iter().enumerate() {
                    let proof = and_projection(v, i, &p.proof, map)?;
                    work.push(Prop { formula: conj.clone(), proof });
                }
            }
            Formula::Bool(true) => {} // inert
            _ => out.push(p),
        }
    }
    Some(out)
}

/// Build a proof of `False` from the conjunction `atoms` (hypothesis `h = #depth`).
/// Seeds the recursive proof-carrying engine ([`refute_props`]) with one prop per
/// top-level atom (proof = its `And` projection), then drives the closure
/// (linear/propositional contradiction, n-ary `Or.rec` case-split, nested `And`
/// flattening).
fn build_false(atoms: &[Formula], vars: &[(String, bool)], n: u32, depth: u32) -> Option<Expr> {
    let map = var_map(vars, n, depth);
    let h = Expr::bvar(depth);
    let mut props = Vec::with_capacity(atoms.len());
    for (i, a) in atoms.iter().enumerate() {
        props.push(Prop { formula: a.clone(), proof: and_projection(atoms, i, &h, &map)? });
    }
    let mut fuel = REFUTE_SEARCH_FUEL;
    refute_props(props, vars, n, depth, &mut fuel)
}

/// The recursive refutation core. Given `props` (hypotheses with explicit proofs,
/// valid at `depth`), prove `False` by — in order — flattening nested `And`s, a
/// `false` hypothesis, a linear `lt`/`le` contradiction (`build_contradiction`),
/// a propositional `P`/`¬P` clash, or an n-ary `Or.rec` case-split where each
/// disjunct is added as a fresh hypothesis and the remaining props (lifted under
/// the new binder) are re-refuted. This subsumes the old `build_false` /
/// `refute_or_split` / `close_or_leaf` trio and additionally handles disjuncts
/// that are themselves nested `And`/`Or` — the shape clamp VCs produce once the
/// `Ite` path-split and BV-overflow checks are lifted.
fn refute_props(
    props: Vec<Prop>,
    vars: &[(String, bool)],
    n: u32,
    depth: u32,
    fuel: &mut usize,
) -> Option<Expr> {
    *fuel = fuel.checked_sub(1)?;
    // Fail closed past a generous case-split depth — VCs needing deeper nesting
    // than this fall through to AY rather than overflowing the stack. (`depth`
    // counts both source `Or` arms and the binder each `Or.rec` introduces; real
    // clamp VCs nest ≤ ~4.)
    if depth > 32 {
        return None;
    }
    let map = var_map(vars, n, depth);
    let props = flatten_props(props, &map)?;

    // A `false` hypothesis proves `False` outright.
    if let Some(p) = props.iter().find(|p| matches!(p.formula, Formula::Bool(false))) {
        return Some(p.proof.clone());
    }

    // Linear `lt`/`le` contradiction over the comparison/equality props.
    let comp = collect_comp_hyps_props(&props, &map)?;
    if let Some(pf) = build_contradiction(&comp, &map) {
        return Some(pf);
    }

    // Propositional `P` against `¬P` — `(¬P) P : False`.
    for pi in &props {
        for pj in &props {
            if let Formula::Not(inner) = &pj.formula {
                if **inner == pi.formula {
                    return Some(Expr::app(pj.proof.clone(), pi.proof.clone()));
                }
            }
        }
    }

    // N-ary `Or` case-split. Try each `Or` prop — only the one whose disjuncts all
    // close works. The other props are carried (lifted) into each case.
    for (idx, p) in props.iter().enumerate() {
        let Formula::Or(ds) = &p.formula else { continue };
        if ds.is_empty() {
            continue;
        }
        let rest: Vec<Prop> = props
            .iter()
            .enumerate()
            .filter(|(j, _)| *j != idx)
            .map(|(_, q)| Prop { formula: q.formula.clone(), proof: q.proof.clone() })
            .collect();
        if let Some(pf) = refute_or_split(&rest, ds, p.proof.clone(), vars, n, depth, fuel) {
            return Some(pf);
        }
    }

    // DISEQUALITY case-split: a `Not(Eq(a, b))` prop (`a b : Int`) is, on its
    // own, invisible to `collect_comp_hyps_props` (which only reads direct
    // comparisons/equalities) — a common real shape is a `x != 0` guard
    // dominating a `x - 1` subtraction (integer trichotomy makes `x != 0`
    // exactly as strong as `x < 0 ∨ x > 0`, and combined with a `0 ≤ x` type
    // bound that becomes `x > 0`, i.e. `x ≥ 1`). Synthesize the disjunction
    // via `Int.lt_trichotomy` ([`or_from_ne`]) and hand it to the SAME
    // `refute_or_split` engine as a native `Or`, so both sub-goals still have
    // to close on their own merits — this never invents a fact, it only makes
    // an already-true disequality's case-split available to the linear
    // engine. Tried after the native `Or` loop (a strictly more expensive
    // fallback, so cheaper matches are not slowed down).
    for (idx, p) in props.iter().enumerate() {
        let Formula::Not(inner) = &p.formula else { continue };
        let Formula::Eq(a, b) = inner.as_ref() else { continue };
        let (Some(a_e), Some(b_e)) = (ground_int(a, &map), ground_int(b, &map)) else { continue };
        let or_proof = or_from_ne(&a_e, &b_e, &p.proof);
        let ds = [Formula::Lt(a.clone(), b.clone()), Formula::Lt(b.clone(), a.clone())];
        let rest: Vec<Prop> = props
            .iter()
            .enumerate()
            .filter(|(j, _)| *j != idx)
            .map(|(_, q)| Prop { formula: q.formula.clone(), proof: q.proof.clone() })
            .collect();
        if let Some(pf) = refute_or_split(&rest, &ds, or_proof, vars, n, depth, fuel) {
            return Some(pf);
        }
    }
    None
}

/// From `ne_proof0 : Not(Eq(a, b))` (`a b : Int`, grounded at the CURRENT
/// binder depth `0`), derive a proof of `Or(Int.lt a b, Int.lt b a)` via
/// `Int.lt_trichotomy a b : Or(a<b, Or(a=b, b<a))`, eliminating the middle
/// `a=b` disjunct against `ne_proof0` (`False.elim` on `ne_proof0 h_eq`).
///
/// SOUNDNESS: `Int.lt_trichotomy` is a constructive, empty-domain-axiom-closure
/// theorem in the prelude (`clean-kernel/src/env/order_int.rs`'s
/// `register_int_lt_trichotomy_proof`), so this introduces NO new axiom
/// dependency — the result stays modulo exactly 3 whenever the rest of the
/// proof does. This is the standard integer-trichotomy case-split (`a ≠ b` on
/// a total order gives `a<b ∨ b<a`); it mirrors the depth-indexed `.lift(k)`
/// `Or.rec`-nesting discipline `clean_ground::prove_negated_guard_cmp` already
/// uses for the same `Int.lt_trichotomy` lemma against a different disjunct.
/// Fail-closed at the CALL SITE, not here: the kernel type-checks the result
/// before any discharge is counted (`check_refute_vc_inner`), so a de Bruijn
/// slip in this construction can only ever produce a rejected (non-)proof,
/// never a false certificate.
fn or_from_ne(a0: &Expr, b0: &Expr, ne_proof0: &Expr) -> Expr {
    let l1 = || vec![Level::succ(Level::zero())];
    let a = |k: u32| a0.lift(k);
    let b = |k: u32| b0.lift(k);
    let ne = |k: u32| ne_proof0.lift(k);
    let lt_ab = |k: u32| Expr::apps(cst("Int.lt"), [a(k), b(k)]);
    let lt_ba = |k: u32| Expr::apps(cst("Int.lt"), [b(k), a(k)]);
    let eq_ab =
        |k: u32| Expr::apps(Expr::const_(Name::from_string("Eq"), l1()), [int(), a(k), b(k)]);
    let or_inner = |k: u32| Expr::apps(cst("Or"), [eq_ab(k), lt_ba(k)]);
    let goal = |k: u32| Expr::apps(cst("Or"), [lt_ab(k), lt_ba(k)]);

    // Outer `Or.rec` at base depth (k=0); each outer-case lambda body is at
    // k=1; the inner `Or.rec`'s cases are at k=2. (Byte-for-byte the same
    // depth discipline as `prove_negated_guard_cmp`'s outer/inner split.)
    let outer_motive = Expr::lam(bd(), Expr::apps(cst("Or"), [lt_ab(0), or_inner(0)]), goal(1));
    // Case `a < b`: `Or.inl _ _ h`.
    let case_lt =
        Expr::lam(bd(), lt_ab(0), Expr::apps(cst("Or.inl"), [lt_ab(1), lt_ba(1), Expr::bvar(0)]));
    // Case `Or(a=b, b<a)`: inner `Or.rec`.
    let inner_motive = Expr::lam(bd(), or_inner(1), goal(2));
    // Sub-case `a = b`: contradicts `ne_proof`, `False.elim` to the goal.
    let case_eq = Expr::lam(
        bd(),
        eq_ab(1),
        Expr::apps(
            Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
            [goal(2), Expr::app(ne(2), Expr::bvar(0))],
        ),
    );
    // Sub-case `b < a`: `Or.inr _ _ h`.
    let case_gt =
        Expr::lam(bd(), lt_ba(1), Expr::apps(cst("Or.inr"), [lt_ab(2), lt_ba(2), Expr::bvar(0)]));
    let case_inner = Expr::lam(
        bd(),
        or_inner(0),
        Expr::apps(
            cst("Or.rec"),
            [eq_ab(1), lt_ba(1), inner_motive, case_eq, case_gt, Expr::bvar(0)],
        ),
    );
    let tri = Expr::apps(cst("Int.lt_trichotomy"), [a(0), b(0)]);
    Expr::apps(cst("Or.rec"), [lt_ab(0), or_inner(0), outer_motive, case_lt, case_inner, tri])
}

/// Comparison/equality hypotheses drawn from a prop list (the prop-carrying
/// analogue of [`collect_comp_hyps`]): a comparison prop yields its `Hyp`, an
/// integer `Eq(a,b)` prop yields both `a ≤ b` and `b ≤ a` (`Eq.subst` on
/// `le_refl`). Non-arithmetic props (`Not`, `Or`, bools) are skipped.
fn collect_comp_hyps_props(props: &[Prop], map: &HashMap<String, Expr>) -> Option<Vec<Hyp>> {
    let mut out = Vec::new();
    for p in props {
        if let Some((strict, lo, hi)) = normalize_cmp(&p.formula) {
            out.push(Hyp { strict, lo, hi, proof: p.proof.clone() });
        } else if let Formula::Eq(a, b) = &p.formula {
            if let (Some(ae), Some(be)) = (ground_int(a, map), ground_int(b, map)) {
                out.push(Hyp::new(
                    false,
                    (**a).clone(),
                    (**b).clone(),
                    le_from_eq(&ae, &be, &p.proof),
                ));
                let symm = eq_symm(&ae, &be, &p.proof);
                out.push(Hyp::new(
                    false,
                    (**b).clone(),
                    (**a).clone(),
                    le_from_eq(&be, &ae, &symm),
                ));
            }
        }
    }
    Some(out)
}

/// Refute `rest ∧ Or[d0, …, d_{m-1}]` (m ≥ 1) by an `Or.rec` case-split, nesting
/// one recursor per disjunct boundary. The grounded `Or` is right-nested
/// (`Or d0 (Or d1 (… d_{m-1}))`), so we peel the head `d0` and recurse on the
/// tail. `or_proof` proves `Or[ds]` (or, for m == 1, proves `ds[0]` directly) at
/// the current `depth`. Each nested `Or.rec` adds exactly one binder; the carried
/// `rest` props are lifted by 1 into each case and the fresh disjunct hypothesis
/// `#0` is added, then `refute_props` re-drives the closure.
fn refute_or_split(
    rest: &[Prop],
    ds: &[Formula],
    or_proof: Expr,
    vars: &[(String, bool)],
    n: u32,
    depth: u32,
    fuel: &mut usize,
) -> Option<Expr> {
    let cst = |s: &str| Expr::const_(Name::from_string(s), LevelVec::new());

    // Base case: a single remaining disjunct — `or_proof` IS its proof. Add it as
    // a fresh hypothesis at the current depth and re-refute `rest ∧ d`.
    if ds.len() == 1 {
        let mut props: Vec<Prop> = rest
            .iter()
            .map(|p| Prop { formula: p.formula.clone(), proof: p.proof.clone() })
            .collect();
        props.push(Prop { formula: ds[0].clone(), proof: or_proof });
        return refute_props(props, vars, n, depth, fuel);
    }

    // `Or d0 Rest` where `Rest = Or[ds[1..]]` (right-nested). Motive `λ_. False`.
    let d0 = &ds[0];
    let map = var_map(vars, n, depth);
    let d0_p = ground_formula_prop(d0, &map)?;
    let rest_p = ground_formula_prop(&Formula::Or(ds[1..].to_vec()), &map)?;
    let motive =
        Expr::lam(bd(), Expr::apps(cst("Or"), [d0_p.clone(), rest_p.clone()]), cst("False"));

    // inl `λ(h0 : d0). <refute rest ∧ d0 at depth+1>` — `rest` lifted under the
    // new binder, `d0` the fresh hypothesis `#0`.
    let case_inl = {
        let mut props = lift_props(rest, 1);
        props.push(Prop { formula: d0.clone(), proof: Expr::bvar(0) });
        let body = refute_props(props, vars, n, depth + 1, fuel)?;
        Expr::lam(bd(), d0_p.clone(), body)
    };
    // inr `λ(hr : Rest). <case-split Rest at depth+1>` — `hr = #0` proves the tail
    // `Or`, fed back into the recursion one binder deeper (rest also lifted).
    let case_inr = {
        let lifted = lift_props(rest, 1);
        let body = refute_or_split(&lifted, &ds[1..], Expr::bvar(0), vars, n, depth + 1, fuel)?;
        Expr::lam(bd(), rest_p.clone(), body)
    };
    Some(Expr::apps(cst("Or.rec"), [d0_p, rest_p, motive, case_inl, case_inr, or_proof]))
}

/// Ground a full propositional VC formula (connectives + comparisons) into a
/// kernel `Prop`, mapping vars via `map`. (`crate::clean_ground::ground_prop` is
/// the inhabitation-side analogue; this is the refutation-side copy that also
/// handles `Or`/`Implies` as they appear in real VCs.)
fn ground_formula_prop(f: &Formula, map: &HashMap<String, Expr>) -> Option<Expr> {
    use trust_types::Formula as F;
    let cst = |s: &str| Expr::const_(Name::from_string(s), LevelVec::new());
    let a2 = |op: &str, x: Expr, y: Expr| Expr::apps(cst(op), [x, y]);
    match f {
        F::Bool(true) => Some(cst("True")),
        // A bare boolean variable conjunct asserts it is `true`.
        F::Var(n, trust_types::Sort::Bool) => {
            let b = map.get(n)?.clone();
            Some(Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [cst("Bool"), b, cst("Bool.true")],
            ))
        }
        F::Bool(false) => Some(cst("False")),
        F::Not(a) => Some(Expr::app(cst("Not"), ground_formula_prop(a, map)?)),
        F::And(v) => fold_conn(v, "And", "True", map),
        F::Or(v) => fold_conn(v, "Or", "False", map),
        // Trust: CALL-RESULT-AWARE COMPOSITION (ensures-forwarding, 2026-07-09)
        // — FIX: `a -> b` (`Prop` implication) IS the Pi-type `Π(_:a). b`
        // (CIC's own definition — there is no separate `Implies` inductive/
        // constant in the kernel prelude, unlike `And`/`Or`, which genuinely
        // ARE registered inductives `fold_conn` applies). The prior encoding
        // (`Expr::apps(cst("Implies"), [a, b])`) referenced a NEVER-REGISTERED
        // constant, so ANY formula containing `F::Implies` unconditionally
        // failed kernel type-checking (`UnknownConst("Implies")`) — every
        // refutation attempt over such a formula silently collapsed to `None`
        // (undischarged), regardless of whether the rest of the conjunction
        // held a genuine contradiction. `b` does not depend on the Pi-bound
        // witness of `a` (Prop implication is non-dependent), so no de Bruijn
        // lifting is needed — `b`'s own `Expr` is reused as-is, exactly like
        // every OTHER two-place connective this function builds
        // (`And`/`Or`/`Eq`/`Le`/…, none of which introduce a binder either).
        // A real Pi-type is foundational CIC — no axiom, modulo 3 unaffected.
        F::Implies(a, b) => {
            Some(Expr::pi(bd(), ground_formula_prop(a, map)?, ground_formula_prop(b, map)?))
        }
        F::Le(a, b) => Some(a2("Int.le", ground_int(a, map)?, ground_int(b, map)?)),
        F::Ge(a, b) => Some(a2("Int.le", ground_int(b, map)?, ground_int(a, map)?)),
        F::Lt(a, b) => Some(a2("Int.lt", ground_int(a, map)?, ground_int(b, map)?)),
        F::Gt(a, b) => Some(a2("Int.lt", ground_int(b, map)?, ground_int(a, map)?)),
        F::Eq(a, b) => Some(Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [cst("Int"), ground_int(a, map)?, ground_int(b, map)?],
        )),
        _ => None,
    }
}

fn fold_conn(v: &[Formula], op: &str, unit: &str, map: &HashMap<String, Expr>) -> Option<Expr> {
    let cst = |s: &str| Expr::const_(Name::from_string(s), LevelVec::new());
    match v {
        [] => Some(cst(unit)),
        [x] => ground_formula_prop(x, map),
        [h, t @ ..] => {
            Some(Expr::apps(cst(op), [ground_formula_prop(h, map)?, fold_conn(t, op, unit, map)?]))
        }
    }
}

/// Build the projection `And.left (And.right^k h)` reaching atom `target` of a
/// flat conjunction of `atoms.len()` items (matching the right-nested encoding
/// `And a0 (And a1 (… an))`). The props for `And.left`/`And.right` are supplied
/// explicitly (the kernel `And.left : {a b} → And a b → a`).
fn and_projection(
    atoms: &[Formula],
    target: usize,
    h: &Expr,
    map: &HashMap<String, Expr>,
) -> Option<Expr> {
    let cst = |s: &str| Expr::const_(Name::from_string(s), LevelVec::new());
    // Ground each atom-prop once.
    let props: Vec<Expr> =
        atoms.iter().map(|a| ground_formula_prop(a, map)).collect::<Option<_>>()?;
    let n = props.len();
    // Right-nested conjunction prop for the suffix starting at index `k`.
    let suffix_prop = |k: usize| -> Option<Expr> {
        if k >= n {
            return None;
        }
        let mut acc = props[n - 1].clone();
        for idx in (k..n - 1).rev() {
            acc = Expr::apps(cst("And"), [props[idx].clone(), acc]);
        }
        Some(acc)
    };
    // Descend: at each step the current term has type `And props[k] (suffix k+1)`.
    let mut cur = h.clone();
    let mut k = 0usize;
    while k < target {
        let head = props[k].clone();
        let tail = suffix_prop(k + 1)?;
        cur = Expr::apps(cst("And.right"), [head, tail, cur]);
        k += 1;
    }
    if target == n - 1 {
        // Last atom: it IS the tail, no final And.left.
        Some(cur)
    } else {
        let head = props[target].clone();
        let tail = suffix_prop(target + 1)?;
        Some(Expr::apps(cst("And.left"), [head, tail, cur]))
    }
}

/// Kernel-check a reconstructed VC refutation and confirm modulo 3.
///
/// Runs on a worker thread with a large stack: the clamp/overflow proofs this
/// module now produces case-split the path and the `Ite` condition, and the
/// kernel's `whnf`/`def_eq` recursion during checking (literal reduction over
/// 32-bit overflow thresholds, nested `mul_le_mul`/`le_trans` chains) can exceed
/// the default 2 MiB stack even though the proof TERM is shallow. The worker is
/// purely a stack-management wrapper — same proof, same kernel, no semantic change
/// — and the kernel `Environment` is built fresh inside, so nothing is shared.
pub fn check_refute_vc(formula: &Formula) -> Option<RefuteOutcome> {
    // §6 contract: a VC is reconstructed IFF the kernel VERIFIES its proof. So the
    // public outcome is binary — `Some(RefutedModulo3)` only on kernel success, and
    // `None` (undischarged) otherwise. A `KernelRejected` from the inner engine
    // (malformed proof term, a residue on non-foundational axioms, or a worker
    // panic) is a FAILED reconstruction, not a discharge and NOT an unsoundness:
    // the kernel rejecting a candidate proof is soundness working, not failing.
    // Collapsing it to `None` here keeps any route's malformed proof from ever
    // being counted as a discharge or mislabeled "unsound" downstream; the worst a
    // buggy route can do is leave a (genuinely safe) VC undischarged. The
    // `KernelRejected` diagnostic remains available via `check_refute_vc_diag`.
    match check_refute_vc_diag(formula) {
        Some(RefuteOutcome::RefutedModulo3) => Some(RefuteOutcome::RefutedModulo3),
        _ => None,
    }
}

/// Phase 1 — [`check_refute_vc`] with struct-param awareness: registered struct
/// params recurse into their named Int fields. With an EMPTY [`StructParams`] this
/// equals `check_refute_vc`. Returns `Some(RefutedModulo3)` only on kernel success.
pub fn check_refute_vc_with(formula: &Formula, params: &StructParams) -> Option<RefuteOutcome> {
    match check_refute_vc_diag_with(formula, params) {
        Some(RefuteOutcome::RefutedModulo3) => Some(RefuteOutcome::RefutedModulo3),
        _ => None,
    }
}

/// Diagnostic entry point: returns the full [`RefuteOutcome`] including
/// `KernelRejected` (used by tests that want to assert a candidate proof failed
/// kernel checking). Production §6 accounting uses [`check_refute_vc`], which
/// collapses any non-`RefutedModulo3` outcome to `None`.
pub fn check_refute_vc_diag(formula: &Formula) -> Option<RefuteOutcome> {
    check_refute_vc_diag_with(formula, &StructParams::default())
}

/// [`check_refute_vc_diag`] with Phase 1 struct-param awareness.
pub(crate) fn check_refute_vc_diag_with(
    formula: &Formula,
    params: &StructParams,
) -> Option<RefuteOutcome> {
    // 64 MiB comfortably covers the deepest clamp-VC kernel checks observed
    // (proof Expr depth ~70, kernel reduction ~30× that).
    const STACK: usize = 64 * 1024 * 1024;
    std::thread::scope(|s| {
        match std::thread::Builder::new()
            .stack_size(STACK)
            .spawn_scoped(s, || check_refute_vc_inner(formula, params))
        {
            // Spawn failed (e.g. resource limits): fall back to checking inline.
            Err(_) => check_refute_vc_inner(formula, params),
            Ok(handle) => handle.join().unwrap_or(Some(RefuteOutcome::KernelRejected(
                "refutation worker panicked".to_string(),
            ))),
        }
    })
}

fn check_refute_vc_inner(formula: &Formula, params: &StructParams) -> Option<RefuteOutcome> {
    let (proof, ty) = refute_vc_with(formula, params)?;
    let mut env = match env_with_order_lemmas() {
        Ok(e) => e,
        Err(e) => return Some(RefuteOutcome::KernelRejected(e)),
    };
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &ty) {
            return Some(RefuteOutcome::KernelRejected(format!("check_type: {e:?}")));
        }
    }
    let name = Name::from_string("Trust.Safety.vc_refutation");
    if env
        .add_decl(Declaration::Definition {
            name: name.clone(),
            level_params: vec![],
            type_: ty,
            value: proof,
            is_reducible: false,
        })
        .is_err()
    {
        return Some(RefuteOutcome::KernelRejected("add_decl".to_string()));
    }
    Some(match env.axiom_deps(&name) {
        Some(r) if r.is_empty() => RefuteOutcome::RefutedModulo3,
        Some(r) => RefuteOutcome::KernelRejected(format!("{} non-foundational axioms", r.len())),
        None => RefuteOutcome::KernelRejected("declaration not found".to_string()),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Trust: CALL-RESULT-AWARE COMPOSITION (ensures-forwarding, 2026-07-09) —
    /// REGRESSION PIN for the `F::Implies` grounding bug this increment fixed:
    /// `ground_formula_prop` used to build `Implies a b` as an APPLICATION of a
    /// NEVER-REGISTERED constant named `"Implies"` (there is no such constant —
    /// `Prop` implication IS the Pi-type `Π(_:a). b`, unlike `And`/`Or`, which
    /// genuinely ARE registered inductives). Any VC formula containing
    /// `F::Implies` — e.g. `trust_vcgen`'s own bool-cast encoding `Implies(b,
    /// x=1) ∧ Implies(¬b, x=0)`, the `to_ascii_{lower,upper}case` shape's real
    /// emission — UNCONDITIONALLY failed kernel type-checking
    /// (`UnknownConst("Implies")`), so `check_refute_vc` silently collapsed to
    /// `None` (undischarged) regardless of whether the surrounding conjunction
    /// held a genuine contradiction. This is the NARROW claim, pinned
    /// directly: `ground_formula_prop` on an `F::Implies` now produces a term
    /// that TYPE-CHECKS as a genuine `Prop` (a real Pi-type) in the standard
    /// order-lemma environment — BEFORE the fix, this same call constructed
    /// `Expr::apps(cst("Implies"), [..])`, which is `UnknownConst("Implies")`
    /// under ANY environment (no declaration ever registers that name). The
    /// end-to-end case-split reconstruction over a REAL Implies-bearing VC is
    /// separately pinned by `prove::tests::
    /// u8_ascii_to_ascii_lowercase_uppercase_recognized_via_call_chain_pureop`
    /// (`function_safety_vcs_all_discharged` on the ACTUAL `to_ascii_lowercase`
    /// emission, which carries exactly this `Implies` shape).
    #[test]
    fn implies_grounds_to_a_type_checking_pi_type_not_unknown_const() {
        use std::collections::HashMap;

        use trust_types::{Formula as F, Sort};
        let x = || F::Var("x".into(), Sort::Int);
        // `x >= 0 -> x >= 0` — a trivial but genuine `F::Implies` between two
        // real Props (mirrors `trust_vcgen`'s own bool-cast encoding's SHAPE:
        // an Implies whose antecedent/consequent are themselves comparisons).
        let f = F::Implies(
            Box::new(F::Ge(Box::new(x()), Box::new(F::Int(0)))),
            Box::new(F::Ge(Box::new(x()), Box::new(F::Int(0)))),
        );
        // `map` binds "x" to the SOLE outer-binder's bound variable (bvar 0) —
        // mirrors `refute_vc_with`'s own `type_map` construction exactly (a
        // De Bruijn-bound variable under a matching outer Pi/Lambda scaffold,
        // never a raw closed FVar).
        let map: HashMap<String, Expr> = {
            let mut m = HashMap::new();
            m.insert("x".to_string(), Expr::bvar(0));
            m
        };
        let prop = ground_formula_prop(&f, &map).expect("F::Implies must ground to SOME term");
        // Wrap in the SAME `Π(x:Int). <prop>` scaffold `refute_vc_with` uses for
        // its own var binders, then confirm the WHOLE thing type-checks as a
        // real Sort — BEFORE the fix, `ground_formula_prop` produced
        // `Expr::apps(cst("Implies"), [..])`, an application of a name NO
        // environment ever registers (`UnknownConst("Implies")`), regardless
        // of the wrapping context.
        let whole_ty = Expr::pi(bd(), int(), prop);
        let env = env_with_order_lemmas().expect("order-lemma env");
        let tc = TypeChecker::new(&env);
        let _ = tc.infer_type(&whole_ty).expect(
            "Pi(x:Int). (x>=0 -> x>=0) must type-check (a real Pi-type, not UnknownConst(\"Implies\"))",
        );
    }

    /// PHASE 1 GATE 2 (synthetic) — a struct-field safety VC reconstructs: a
    /// bounded `p.x + p.y` participates in a linear contradiction
    /// (`0≤p.x≤5 ∧ 0≤p.y≤3 ∧ p.x+p.y>1000`) and refutes to a real Clean kernel
    /// proof modulo exactly 3 axioms. The struct's named Int fields `p.x`/`p.y`
    /// are bound as INDEPENDENT linear variables (the same `Var(name, Int)` the
    /// arithmetic engine handles), so the additive overflow reconstruction
    /// applies directly — proving struct-field safety VCs are in the linear
    /// fragment after collect_int_vars recurses the struct into its fields.
    #[test]
    fn struct_field_additive_overflow_refuted_modulo_3() {
        use trust_types::{Formula as F, Sort};
        let fx = || F::Var("p.x".into(), Sort::Int);
        let fy = || F::Var("p.y".into(), Sort::Int);
        // 0 ≤ p.x ≤ 5 ∧ 0 ≤ p.y ≤ 3 ∧ p.x + p.y > 1000  — UNSAT (max sum 8).
        let vc = F::And(vec![
            F::Ge(Box::new(fx()), Box::new(F::Int(0))),
            F::Le(Box::new(fx()), Box::new(F::Int(5))),
            F::Ge(Box::new(fy()), Box::new(F::Int(0))),
            F::Le(Box::new(fy()), Box::new(F::Int(3))),
            F::Gt(Box::new(F::Add(Box::new(fx()), Box::new(fy()))), Box::new(F::Int(1000))),
        ]);
        assert_eq!(
            check_refute_vc_diag(&vc),
            Some(RefuteOutcome::RefutedModulo3),
            "a bounded struct-field sum p.x+p.y>1000 must refute modulo 3"
        );
        // And the registered-struct fields are recognized as linear Int vars.
        let (mut order, mut seen) = (Vec::new(), std::collections::HashSet::new());
        let params = StructParams::default();
        assert!(collect_int_vars(&vc, &mut order, &mut seen, &params));
        let names: Vec<&str> = order.iter().map(|(n, _)| n.as_str()).collect();
        assert!(names.contains(&"p.x") && names.contains(&"p.y"));
    }

    /// M6 rung 2 — DISEQUALITY-GUARDED SUBTRACTION (`or_from_ne`). The clean-kernel
    /// census's real, undischarged `infer_implicit_n` shape: `x - 1` guarded by
    /// `x != 0` (a Rust `if num_params != 0 { ... num_params - 1 ... }`, which
    /// lowers to `Not(Eq(x, 0))` rather than a direct `x >= 1` comparison —
    /// `collect_comp_hyps_props` alone cannot see a disequality, so this needs
    /// the trichotomy case-split). `0 ≤ x ∧ x ≠ 0 ⟹ x ≥ 1`, so `x - 1 < 0` is
    /// UNSAT: refutes modulo exactly 3 axioms via `Int.lt_trichotomy`.
    #[test]
    fn disequality_guarded_sub_refuted_modulo_3() {
        use trust_types::{Formula as F, Sort};
        let x = || F::Var("x".into(), Sort::Int);
        let vc = F::And(vec![
            F::Ge(Box::new(x()), Box::new(F::Int(0))),
            F::Not(Box::new(F::Eq(Box::new(x()), Box::new(F::Int(0))))),
            F::Lt(Box::new(F::Sub(Box::new(x()), Box::new(F::Int(1)))), Box::new(F::Int(0))),
        ]);
        assert_eq!(
            check_refute_vc_diag(&vc),
            Some(RefuteOutcome::RefutedModulo3),
            "0<=x and x!=0 must refute the x-1<0 violation via trichotomy"
        );
    }

    /// ADVERSARIAL PROBE (fail-closed pin, basic-math a+b lesson): drop the `x !=
    /// 0` guard entirely. `x = 0` is now a REAL counterexample (`0 - 1 < 0` truly
    /// holds), so the exact same violation core must stay UNDISCHARGED — the new
    /// disequality case-split must never fire on a formula that carries no
    /// disequality hypothesis at all, and must never manufacture a false proof.
    #[test]
    fn unguarded_sub_stays_not_faithful() {
        use trust_types::{Formula as F, Sort};
        let x = || F::Var("x".into(), Sort::Int);
        let vc = F::And(vec![
            F::Ge(Box::new(x()), Box::new(F::Int(0))),
            F::Lt(Box::new(F::Sub(Box::new(x()), Box::new(F::Int(1)))), Box::new(F::Int(0))),
        ]);
        assert_eq!(
            check_refute_vc_diag(&vc),
            None,
            "x-1<0 with NO x!=0 guard is a genuine potential underflow (x=0) — must stay open"
        );
    }

    /// ADVERSARIAL PROBE — an IRRELEVANT disequality (`x != 5`) does not rule out
    /// the actual violating value (`x = 0`), so the case-split must still fail to
    /// close either branch and the violation must stay UNDISCHARGED. Pins that
    /// `or_from_ne` only ever contributes a SOUND disjunction (`x<5 ∨ x>5`), never
    /// a spurious discharge from an unrelated disequality.
    #[test]
    fn irrelevant_disequality_does_not_falsely_discharge() {
        use trust_types::{Formula as F, Sort};
        let x = || F::Var("x".into(), Sort::Int);
        let vc = F::And(vec![
            F::Ge(Box::new(x()), Box::new(F::Int(0))),
            F::Not(Box::new(F::Eq(Box::new(x()), Box::new(F::Int(5))))),
            F::Lt(Box::new(F::Sub(Box::new(x()), Box::new(F::Int(1)))), Box::new(F::Int(0))),
        ]);
        assert_eq!(
            check_refute_vc_diag(&vc),
            None,
            "x!=5 does not exclude x=0 — the x-1<0 violation must stay open"
        );
    }

    /// M6 rung 2 — `preprocess_vc`'s `normalize_not` broadening. A NEGATED
    /// comparison guard (`Not(Lt(depth, idx))`, e.g. from a `SwitchInt`
    /// "otherwise" edge or a source-level `if !(depth < idx)`) previously stayed
    /// invisible to `collect_comp_hyps_props` OUTSIDE a clamp/`Ite` VC shape
    /// (`normalize_not` ran only on the `has_ite` path). `¬(depth < idx)` flips
    /// to `depth ≥ idx`, which makes `depth - idx` non-negative, so the
    /// underflow violation `depth - idx < 0` must refute.
    #[test]
    fn negated_comparison_guard_refuted_modulo_3() {
        use trust_types::{Formula as F, Sort};
        let idx = || F::Var("idx".into(), Sort::Int);
        let depth = || F::Var("depth".into(), Sort::Int);
        let vc = F::And(vec![
            F::Ge(Box::new(idx()), Box::new(F::Int(0))),
            F::Ge(Box::new(depth()), Box::new(F::Int(0))),
            F::Not(Box::new(F::Lt(Box::new(depth()), Box::new(idx())))),
            F::Lt(Box::new(F::Sub(Box::new(depth()), Box::new(idx()))), Box::new(F::Int(0))),
        ]);
        assert_eq!(
            check_refute_vc_diag(&vc),
            Some(RefuteOutcome::RefutedModulo3),
            "Not(depth<idx) i.e. depth>=idx must refute the depth-idx<0 violation"
        );
    }

    /// ADVERSARIAL PROBE — drop the negated guard: `depth - idx` with idx, depth
    /// unrelated is a genuine potential underflow (e.g. idx=5, depth=3), so the
    /// SAME violation core must stay UNDISCHARGED with no guard present at all.
    #[test]
    fn unguarded_reverse_sub_stays_not_faithful() {
        use trust_types::{Formula as F, Sort};
        let idx = || F::Var("idx".into(), Sort::Int);
        let depth = || F::Var("depth".into(), Sort::Int);
        let vc = F::And(vec![
            F::Ge(Box::new(idx()), Box::new(F::Int(0))),
            F::Ge(Box::new(depth()), Box::new(F::Int(0))),
            F::Lt(Box::new(F::Sub(Box::new(depth()), Box::new(idx()))), Box::new(F::Int(0))),
        ]);
        assert_eq!(
            check_refute_vc_diag(&vc),
            None,
            "depth-idx<0 with NO ordering guard is a genuine potential underflow — must stay open"
        );
    }

    /// NO-REGRESSION PIN for the `preprocess_vc` `normalize_not` broadening: a
    /// formula built ENTIRELY from direct comparisons (no `Not(..)` anywhere) is a
    /// fixed point of `normalize_not`, so `preprocess_vc` on the non-Ite path is
    /// byte-identical to before this change. Reuses the exact shape of the
    /// pre-existing `guarded_subtraction_underflow_refuted_via_add_zero` control.
    #[test]
    fn preprocess_vc_is_unchanged_on_a_comparison_only_formula() {
        use trust_types::{Formula as F, Sort};
        let a = || F::Var("a".into(), Sort::Int);
        let b = || F::Var("b".into(), Sort::Int);
        let vc = F::And(vec![
            F::Ge(Box::new(a()), Box::new(b())),
            F::Lt(Box::new(F::Sub(Box::new(a()), Box::new(b()))), Box::new(F::Int(0))),
        ]);
        assert_eq!(
            preprocess_vc(&vc),
            vc,
            "a Not-free formula must be a fixed point of preprocess_vc's normalize_not step"
        );
        assert_eq!(check_refute_vc(&vc), Some(RefuteOutcome::RefutedModulo3));
    }

    /// PHASE 1 — collect_int_vars recurses a REGISTERED struct param into its
    /// named Int fields. A struct `Pt{x:i32,y:i32}` registered in the registry,
    /// referenced bare as `Var("p", Int)` in a VC that also constrains `p.x`/`p.y`,
    /// binds the named fields as linear vars (the bare `p` itself is dropped — a
    /// struct value is not an integer operand, only its fields are).
    #[test]
    fn registered_struct_param_recurses_into_named_int_fields() {
        use trust_types::{Formula as F, Sort};
        // Register Pt{x:i32,y:i32}.
        let ty = trust_types::Ty::Adt { adt_kind: None, layout: None, 
            variants: Vec::new(),
            name: "Pt".into(),
            fields: vec![
                ("x".into(), trust_types::Ty::Int { width: 32, signed: true }),
                ("y".into(), trust_types::Ty::Int { width: 32, signed: true }),
            ],
            disc_index_safe: false,
            faithful_enum_repr: None, enum_layout: None, };
        let carrier = crate::reflect::reflect_struct(&ty).expect("Pt reflects");
        let mut env = clean_kernel::Environment::with_prelude();
        let registry =
            crate::clean_ground::register_adt_carriers(&mut env, std::slice::from_ref(&carrier));
        assert!(registry.get("Trust.Adt.Pt").is_some(), "Pt registered modulo 3");

        // Build StructParams from a function whose param `p : Pt` is registered.
        use trust_types::{LocalDecl, VerifiableBody, VerifiableFunction};
        let i32t = || trust_types::Ty::Int { width: 32, signed: true };
        let func = VerifiableFunction {
            name: "uses_pt".into(),
            def_path: "crate::uses_pt".into(),
            span: Default::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: i32t(), name: Some("_0".into()) },
                    LocalDecl { index: 1, ty, name: Some("p".into()) },
                ],
                blocks: vec![],
                arg_count: 1,
                return_ty: i32t(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };
        let params = StructParams::from_function(&func, &registry);

        // A VC that references the struct param `p` (Int-sorted, the from_ty
        // fallback) plus its field vars. The recursion DROPS the bare aggregate
        // `p` and binds p.x/p.y as linear vars.
        let vc = F::And(vec![
            F::Var("p".into(), Sort::Int),
            F::Le(Box::new(F::Var("p.x".into(), Sort::Int)), Box::new(F::Int(5))),
            F::Ge(Box::new(F::Var("p.y".into(), Sort::Int)), Box::new(F::Int(0))),
        ]);
        let (mut order, mut seen) = (Vec::new(), std::collections::HashSet::new());
        assert!(
            collect_int_vars(&vc, &mut order, &mut seen, &params),
            "registered struct fields must stay in the linear fragment"
        );
        let names: Vec<&str> = order.iter().map(|(n, _)| n.as_str()).collect();
        assert!(names.contains(&"p.x"), "p.x bound as a linear var");
        assert!(names.contains(&"p.y"), "p.y bound as a linear var");
        assert!(
            !names.contains(&"p"),
            "the bare struct aggregate p must be dropped, not bound as Int"
        );
    }

    /// Enum MIR field indices live in the flattened source layout, which keeps
    /// `__tag` at index 0. Both variants deliberately use the same raw tuple-field
    /// name `0`; the carrier's compatibility union therefore has only one `0`
    /// entry and cannot distinguish the variants. The validated source layout
    /// must keep `e@0.0`/`e.1` distinct from `e@1.0`/`e.2`, while still unifying
    /// each pair with its exact flattened contract spelling.
    #[test]
    fn enum_numeric_field_uses_source_layout_and_rejects_tag_alias() {
        use trust_types::{
            Formula as F, LocalDecl, Sort, Ty, VariantDef, VerifiableBody, VerifiableFunction,
        };

        let u32t = || Ty::Int { width: 32, signed: false };
        let enum_ty = Ty::Adt { adt_kind: None, layout: None, 
            name: "E".into(),
            fields: vec![
                ("__tag".into(), Ty::Int { width: 64, signed: true }),
                ("__v0_0".into(), u32t()),
                ("__v1_0".into(), u32t()),
            ],
            variants: vec![
                VariantDef {
                    name: "A".into(),
                    discriminant: 0,
                    fields: vec![("0".into(), u32t())],
                },
                VariantDef {
                    name: "B".into(),
                    discriminant: 1,
                    fields: vec![("0".into(), u32t())],
                },
            ],
            disc_index_safe: false,
            faithful_enum_repr: None, enum_layout: None, };
        let carrier = crate::reflect::reflect_struct(&enum_ty).expect("E reflects as an enum");
        assert_eq!(carrier.fields.len(), 1, "the sum carrier exposes payloads, not __tag");
        assert_eq!(carrier.fields[0].0, "0", "constructor fields retain source names");
        let mut env = clean_kernel::Environment::with_prelude();
        let registry =
            crate::clean_ground::register_adt_carriers(&mut env, std::slice::from_ref(&carrier));

        let func = VerifiableFunction {
            name: "enum_field_bump".into(),
            def_path: "crate::enum_field_bump".into(),
            span: Default::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: u32t(), name: Some("_0".into()) },
                    LocalDecl { index: 1, ty: enum_ty, name: Some("e".into()) },
                ],
                blocks: vec![],
                arg_count: 1,
                return_ty: u32t(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };
        let params = StructParams::from_function(&func, &registry);

        assert_eq!(params.canonical_field_name("e.1").as_deref(), Some("e.__v0_0"));
        assert_eq!(params.canonical_field_name("e@0.0").as_deref(), Some("e.__v0_0"));
        assert_eq!(params.canonical_field_name("e.__v0_0").as_deref(), Some("e.__v0_0"));
        assert_eq!(params.canonical_field_name("e.2").as_deref(), Some("e.__v1_0"));
        assert_eq!(params.canonical_field_name("e@1.0").as_deref(), Some("e.__v1_0"));
        assert_eq!(params.canonical_field_name("e.__v1_0").as_deref(), Some("e.__v1_0"));
        assert_eq!(
            params.canonical_field_name("e.0"),
            None,
            "the flattened discriminant must not alias the first payload"
        );
        assert_eq!(params.canonical_field_name("e@2.0"), None);
        assert_eq!(params.canonical_field_name("e@0.1"), None);

        // Arithmetic refutation needs only the validated syntax equality. The
        // same variant's flat/downcast spellings become one Int and contradict.
        let same_variant = F::And(vec![
            F::Le(Box::new(F::Var("e.__v0_0".into(), Sort::Int)), Box::new(F::Int(5))),
            F::Gt(Box::new(F::Var("e@0.0".into(), Sort::Int)), Box::new(F::Int(5))),
        ]);
        assert_eq!(
            check_refute_vc_with(&same_variant, &params),
            Some(RefuteOutcome::RefutedModulo3),
            "validated named/downcast spellings of one payload must unify"
        );

        let same_variant_flat = F::And(vec![
            F::Le(Box::new(F::Var("e.__v1_0".into(), Sort::Int)), Box::new(F::Int(5))),
            F::Gt(Box::new(F::Var("e.2".into(), Sort::Int)), Box::new(F::Int(5))),
        ]);
        assert_eq!(
            check_refute_vc_with(&same_variant_flat, &params),
            Some(RefuteOutcome::RefutedModulo3),
            "validated named/flat-index spellings of one payload must unify"
        );

        // The raw constructor field name `0` occurs in BOTH variants. A union-
        // field lookup would conflate them and falsely refute this satisfiable
        // conjunction; variant-qualified aliases must keep it open.
        let different_variants = F::And(vec![
            F::Le(Box::new(F::Var("e.__v0_0".into(), Sort::Int)), Box::new(F::Int(5))),
            F::Gt(Box::new(F::Var("e@1.0".into(), Sort::Int)), Box::new(F::Int(5))),
        ]);
        assert_eq!(
            check_refute_vc_with(&different_variants, &params),
            None,
            "same raw field name in distinct variants must never alias"
        );

        let tag_vs_payload = F::And(vec![
            F::Le(Box::new(F::Var("e.__v0_0".into(), Sort::Int)), Box::new(F::Int(5))),
            F::Gt(Box::new(F::Var("e.0".into(), Sort::Int)), Box::new(F::Int(5))),
        ]);
        assert_eq!(
            check_refute_vc_with(&tag_vs_payload, &params),
            None,
            "the tag slot must never alias a payload"
        );

        // The existing depth target is a single-constructor structure projection.
        // An enum union index is not such a projection; enum grounding must remain
        // closed until a variant-qualified recursor target is carried end-to-end.
        assert!(!params.is_struct_int_field("e.__v0_0"));
        assert_eq!(params.struct_int_field_target("e.__v0_0"), None);
    }

    /// A malformed flattened enum view installs no aliases at all. In
    /// particular, it must not fall through to the carrier's raw field index and
    /// accidentally identify the discriminant with constructor field `0`.
    #[test]
    fn malformed_enum_flat_layout_keeps_all_projection_aliases_closed() {
        use trust_types::{Formula as F, Sort, Ty, VariantDef};

        let u32t = || Ty::Int { width: 32, signed: false };
        let i64t = || Ty::Int { width: 64, signed: true };
        let one_payload_variants = || {
            vec![VariantDef {
                name: "A".into(),
                discriminant: 0,
                fields: vec![("0".into(), u32t())],
            }]
        };
        let malformed_cases = vec![
            ("missing tag", vec![("__v0_0".into(), u32t())], one_payload_variants()),
            (
                "misordered tag",
                vec![("__v0_0".into(), u32t()), ("__tag".into(), i64t())],
                one_payload_variants(),
            ),
            (
                "wrong payload name",
                vec![("__tag".into(), i64t()), ("__wrong_payload_name".into(), u32t())],
                one_payload_variants(),
            ),
            (
                "wrong payload type",
                vec![("__tag".into(), i64t()), ("__v0_0".into(), Ty::Bool)],
                one_payload_variants(),
            ),
            ("missing payload", vec![("__tag".into(), i64t())], one_payload_variants()),
            (
                "extra payload",
                vec![
                    ("__tag".into(), i64t()),
                    ("__v0_0".into(), u32t()),
                    ("__v9_extra".into(), u32t()),
                ],
                one_payload_variants(),
            ),
            (
                "duplicate flattened payload",
                vec![
                    ("__tag".into(), i64t()),
                    ("__v0_0".into(), u32t()),
                    ("__v0_0".into(), u32t()),
                ],
                vec![VariantDef {
                    name: "A".into(),
                    discriminant: 0,
                    fields: vec![("0".into(), u32t()), ("0".into(), u32t())],
                }],
            ),
            (
                "cross-variant payload order swapped",
                vec![
                    ("__tag".into(), i64t()),
                    ("__v1_0".into(), u32t()),
                    ("__v0_0".into(), u32t()),
                ],
                vec![
                    VariantDef {
                        name: "A".into(),
                        discriminant: 0,
                        fields: vec![("0".into(), u32t())],
                    },
                    VariantDef {
                        name: "B".into(),
                        discriminant: 1,
                        fields: vec![("0".into(), u32t())],
                    },
                ],
            ),
        ];

        for (case, fields, variants) in malformed_cases {
            let malformed = Ty::Adt { adt_kind: None, layout: None, 
                name: format!("Malformed_{case}"),
                fields,
                variants,
                disc_index_safe: false,
                faithful_enum_repr: None, enum_layout: None, };
            let carrier = crate::reflect::reflect_struct(&malformed)
                .unwrap_or_else(|| panic!("{case}: variant view reflects"));
            assert!(
                validated_enum_field_aliases(&malformed, &carrier).is_none(),
                "{case}: malformed layout must install no aliases"
            );
            let params = StructParams {
                by_param: [("e".into(), carrier)].into(),
                enum_params: ["e".into()].into(),
                enum_aliases_by_param: HashMap::new(),
            };
            assert_eq!(params.canonical_field_name("e.1"), None, "{case}");
            assert_eq!(params.canonical_field_name("e@0.0"), None, "{case}");
            assert_eq!(params.canonical_field_name("e.0"), None, "{case}");

            // This conjunction is contradictory only if the malformed layout
            // invents an alias between the named and numeric/downcast spellings.
            let named_vs_flat = F::And(vec![
                F::Le(Box::new(F::Var("e.__v0_0".into(), Sort::Int)), Box::new(F::Int(5))),
                F::Gt(Box::new(F::Var("e.1".into(), Sort::Int)), Box::new(F::Int(5))),
            ]);
            assert_eq!(
                check_refute_vc_with(&named_vs_flat, &params),
                None,
                "{case}: malformed flat layout must stay fail-closed"
            );
            let named_vs_downcast = F::And(vec![
                F::Le(Box::new(F::Var("e.__v0_0".into(), Sort::Int)), Box::new(F::Int(5))),
                F::Gt(Box::new(F::Var("e@0.0".into(), Sort::Int)), Box::new(F::Int(5))),
            ]);
            assert_eq!(
                check_refute_vc_with(&named_vs_downcast, &params),
                None,
                "{case}: malformed downcast layout must stay fail-closed"
            );
        }
    }

    /// PHASE 2 — the CONCRETE field of a GENERIC struct reconstructs structurally.
    /// `Wrapper<T>{value:T, count:u32}` registers as a PARAMETERIZED inductive
    /// (modulo 3, over `T:Type`); a bounded add-overflow VC on the concrete `count`
    /// field — `0 ≤ count ≤ 100 ∧ count + 1 > 2^32-1` — is UNSAT and refutes to a
    /// real Clean kernel proof modulo exactly 3 axioms via the named `count` field.
    /// The generic `value: T` field never enters the integer fragment (parametricity).
    #[test]
    fn generic_struct_concrete_field_overflow_refuted_modulo_3() {
        use trust_types::{Formula as F, LocalDecl, Sort, Ty, VerifiableBody, VerifiableFunction};
        // Register the parameterized Wrapper<T>{value:T, count:u32}.
        let ty = Ty::Adt { adt_kind: None, layout: None, 
            variants: Vec::new(),
            name: "Wrapper".into(),
            fields: vec![
                (
                    "value".into(),
                    Ty::Unsupported {
                        kind: "TyKind::Param".into(),
                        detail: "generic parameter T/#0 needs monomorphization".into(),
                    },
                ),
                ("count".into(), Ty::Int { width: 32, signed: false }),
            ],
            disc_index_safe: false,
            faithful_enum_repr: None, enum_layout: None, };
        let carrier =
            crate::reflect::reflect_struct(&ty).expect("Wrapper<T> reflects parameterized");
        assert!(carrier.is_parameterized());
        let mut env = clean_kernel::Environment::with_prelude();
        let registry =
            crate::clean_ground::register_adt_carriers(&mut env, std::slice::from_ref(&carrier));
        assert!(
            registry.get("Trust.Adt.Wrapper").is_some(),
            "Wrapper<T> registered as a parameterized inductive modulo 3"
        );

        let u32t = || Ty::Int { width: 32, signed: false };
        let func = VerifiableFunction {
            name: "count_bump".into(),
            def_path: "crate::count_bump".into(),
            span: Default::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: u32t(), name: Some("_0".into()) },
                    LocalDecl { index: 1, ty, name: Some("w".into()) },
                ],
                blocks: vec![],
                arg_count: 1,
                return_ty: u32t(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };
        let params = StructParams::from_function(&func, &registry);

        // `w.count` is a structural Int field; `w.value` (generic T) is not.
        assert!(params.is_struct_int_field("w.count"), "concrete count field is structural Int");
        assert!(
            !params.is_struct_int_field("w.value"),
            "generic T field is NOT an integer operand (parametricity)"
        );

        // 0 ≤ count ≤ 100 ∧ count + 1 > 2^32-1 — UNSAT (max count+1 is 101).
        let c = || F::Var("w.count".into(), Sort::Int);
        let vc = F::And(vec![
            F::Ge(Box::new(c()), Box::new(F::Int(0))),
            F::Le(Box::new(c()), Box::new(F::Int(100))),
            F::Gt(
                Box::new(F::Add(Box::new(c()), Box::new(F::Int(1)))),
                Box::new(F::Int((1i128 << 32) - 1)),
            ),
        ]);
        assert_eq!(
            check_refute_vc_diag_with(&vc, &params),
            Some(RefuteOutcome::RefutedModulo3),
            "the concrete count-field overflow VC must reconstruct modulo 3 over the parameterized inductive"
        );
    }

    /// The §6 `fixedmath_percent_*`/`permille_*` clamp-cast SHAPE, with the SSA
    /// version suffixes that previously defeated the engine. The cast VC, after the
    /// clamp `Ite` path-split, carries a GLOBAL upper bound `scaled#s5_0 ≤ 255`
    /// stated in an OUTER conjunct, while the cast violation `scaled#s5_0 > 255`
    /// and the def chain `scaled#s5_0 = _6#s4_0/100`, `_6#s4_0 = _10`,
    /// `_10 = _7#s3_0 * _8#s3_2`, `_7#s3_0 = x`, `_8#s3_2 = p` sit in a DEEPER
    /// nested `And` of the same arm. Before the subtree-wide aux-def collection,
    /// the inner violation was inlined to `(x*p)/100 > 255` while the outer bound
    /// kept the variable name `scaled#s5_0`, so the two no longer shared a term and
    /// the immediate `≤255 ∧ >255` contradiction was invisible. Now both resolve to
    /// `(x*p)/100`, and EACH clamp arm closes. The `#sN_M` suffixes are load-bearing
    /// here: this is the exact regression the production cast VCs hit.
    #[test]
    fn versioned_clamp_cast_outer_bound_meets_inner_violation_refuted() {
        use trust_types::{Formula as F, Sort};
        let v = |n: &str| F::Var(n.into(), Sort::Int);
        let eq = |a: F, b: F| F::Eq(Box::new(a), Box::new(b));
        // Deeply-nested def chain + violation, as the real cast VC nests it.
        let inner = F::And(vec![
            eq(
                v("p#s1_0"),
                F::Ite(
                    Box::new(F::Gt(Box::new(v("pct")), Box::new(F::Int(100)))),
                    Box::new(F::Int(100)),
                    Box::new(v("pct")),
                ),
            ),
            eq(v("_7#s3_0"), v("x")),
            eq(v("_8#s3_2"), v("p#s1_0")),
            eq(v("_10#s3_3"), F::Mul(Box::new(v("_7#s3_0")), Box::new(v("_8#s3_2")))),
            eq(v("_6#s4_0"), v("_10#s3_3")),
            eq(v("scaled#s5_0"), F::Div(Box::new(v("_6#s4_0")), Box::new(F::Int(100)))),
            // the cast violation, buried beside its def
            F::Gt(Box::new(v("scaled#s5_0")), Box::new(F::Int(100))),
        ]);
        // Outer conjunct carries the GLOBAL bound by NAME, far above the def.
        let vc = F::And(vec![
            F::Ge(Box::new(v("x")), Box::new(F::Int(0))),
            F::Ge(Box::new(v("pct")), Box::new(F::Int(0))),
            F::Le(Box::new(v("scaled#s5_0")), Box::new(F::Int(100))),
            inner,
        ]);
        assert_eq!(
            check_refute_vc_diag(&vc),
            Some(RefuteOutcome::RefutedModulo3),
            "the outer Le(scaled#s5_0,100) must meet the inner Gt(scaled#s5_0,100) \
             once the deeply-nested def chain is inlined into the outer bound"
        );
    }

    /// SOUNDNESS GUARD for the subtree-wide aux-def inlining: two DIFFERENT live
    /// values of the same base name `v` live in two different `Or` arms, and a fact
    /// holds in only one arm. The formula is SATISFIABLE (pick the arm whose value
    /// is consistent), so it MUST NOT be refuted. If the canonicalization wrongly
    /// applied arm-A's def `v#a = 300` to arm-B (or conflated the two `v#…`
    /// versions), it would fabricate a contradiction and return a refutation — a
    /// false proof. `collect_subtree_aux_defs` STOPS at `Or`, so each arm's def
    /// stays local; this test pins that the engine honestly returns `None`.
    #[test]
    fn different_values_same_base_across_arms_not_refuted() {
        use trust_types::{Formula as F, Sort};
        let v = |n: &str| F::Var(n.into(), Sort::Int);
        let eq = |a: F, b: F| F::Eq(Box::new(a), Box::new(b));
        // Two arms, each DEFINING the same SSA base `_v#s0_0` to a DIFFERENT value
        // and each asserting `_v#s0_0 < 255`:
        //   Arm A: `_v#s0_0 = 300 ∧ _v#s0_0 < 255`   (UNSAT on its own — 300 < 255 false)
        //   Arm B: `_v#s0_0 = 10  ∧ _v#s0_0 < 255`   (SAT — 10 < 255 true)
        // The DISJUNCTION is SATISFIABLE (arm B holds), so the VC is NOT a
        // contradiction and MUST return `None`. The danger this guards: if subtree
        // collection pulled arm A's def `_v#s0_0 = 300` ACROSS the `Or` into arm B
        // (or conflated the two arms' values of `_v`), it would manufacture
        // `300 < 255` in arm B and fabricate a refutation. `collect_subtree_aux_defs`
        // STOPS at `Or`, so each arm keeps its own def — arm B closes only if its
        // OWN value 10 violates the bound, which it does not. Nested under an outer
        // `And` so the clamp pipeline's `inline_aux_deep` (not the top-level path)
        // drives the inlining.
        let arm_a = F::And(vec![
            eq(v("_v#s0_0"), F::Int(300)),
            F::Lt(Box::new(v("_v#s0_0")), Box::new(F::Int(255))),
        ]);
        let arm_b = F::And(vec![
            eq(v("_v#s0_0"), F::Int(10)),
            F::Lt(Box::new(v("_v#s0_0")), Box::new(F::Int(255))),
        ]);
        // Force the clamp (`inline_aux_deep`) pipeline via a trivial top-level `Ite`
        // def, and surround the `Or` with an outer conjunct so subtree collection
        // runs at an `And` enclosing the `Or`.
        let vc = F::And(vec![
            eq(
                v("_w#s0_1"),
                F::Ite(
                    Box::new(F::Gt(Box::new(v("_v#s0_0")), Box::new(F::Int(0)))),
                    Box::new(F::Int(1)),
                    Box::new(F::Int(0)),
                ),
            ),
            F::Or(vec![arm_a, arm_b]),
        ]);
        assert_eq!(
            check_refute_vc_diag(&vc),
            None,
            "SATISFIABLE (arm B holds): must NOT fabricate a refutation by \
             pulling arm A's def `_v#s0_0=300` across the `Or` into arm B"
        );
    }

    /// Companion negative control: a SINGLE arm where the base's one live value
    /// `_v#s0_0 = 300` does contradict `_v#s0_0 ≤ 255` IS refuted — confirming the
    /// guard above stays `None` because of arm separation, not because the engine
    /// is simply blind to the contradiction.
    #[test]
    fn single_arm_value_against_bound_is_refuted() {
        use trust_types::{Formula as F, Sort};
        let v = |n: &str| F::Var(n.into(), Sort::Int);
        let eq = |a: F, b: F| F::Eq(Box::new(a), Box::new(b));
        let vc = F::And(vec![
            eq(v("_v#s0_0"), F::Int(300)),
            F::Le(Box::new(v("_v#s0_0")), Box::new(F::Int(255))),
        ]);
        assert_eq!(check_refute_vc_diag(&vc), Some(RefuteOutcome::RefutedModulo3));
    }

    /// A synthetic clamp VC `x = Ite(y > 100, 100, y) ∧ x > 100` (i.e. `x = min(y,100)`
    /// with `x > 100`) is refuted modulo 3. `lift_ite` rewrites the `Ite` into the
    /// disjunction `(y>100 ∧ x=100) ∨ (y≤100 ∧ x=y)`; the n-ary `Or` case-split closes
    /// BOTH arms — the `y>100` arm via `x=100` against `x>100`, the `y≤100` arm via
    /// `x=y≤100` against `x>100`. Exercises the clamp pipeline end-to-end.
    #[test]
    fn clamp_ite_min_refuted_both_arms() {
        use trust_types::{Formula as F, Sort};
        let v = |n: &str| F::Var(n.into(), Sort::Int);
        let vc = F::And(vec![
            F::Eq(
                Box::new(v("x")),
                Box::new(F::Ite(
                    Box::new(F::Gt(Box::new(v("y")), Box::new(F::Int(100)))),
                    Box::new(F::Int(100)),
                    Box::new(v("y")),
                )),
            ),
            F::Gt(Box::new(v("x")), Box::new(F::Int(100))),
        ]);
        assert_eq!(check_refute_vc(&vc), Some(RefuteOutcome::RefutedModulo3));
    }

    /// A clamp-then-bound PRODUCT VC in the §6 `fixedmath` Mul shape: a clamp
    /// `x = Ite(p>100,100,p)` co-occurs with a bounded product overflow
    /// `0≤a≤255 ∧ 0≤b≤255 ∧ a*b > 65535` (whose `a*b ≤ 255*255 = 65025` cannot exceed
    /// 65535). Refuted modulo 3: `lift_ite` splits the path on `p>100` into a 2-arm
    /// `Or`, and EACH arm — carrying the same product hypotheses — closes via the
    /// two-variable `Int.mul_le_mul` lift against the violation. Exercises `lift_ite`
    /// + the nested `Or` case-split + per-arm `mul_le_mul`, i.e. the exact path the
    /// `fixedmath_percent_*`/`permille_*` Mul VCs take.
    #[test]
    fn clamp_then_bounded_product_refuted() {
        use trust_types::{Formula as F, Sort};
        let v = |n: &str| F::Var(n.into(), Sort::Int);
        let bnd = |n: &str| {
            vec![
                F::Le(Box::new(F::Int(0)), Box::new(v(n))),
                F::Le(Box::new(v(n)), Box::new(F::Int(255))),
            ]
        };
        let mut atoms = vec![F::Eq(
            Box::new(v("x")),
            Box::new(F::Ite(
                Box::new(F::Gt(Box::new(v("p")), Box::new(F::Int(100)))),
                Box::new(F::Int(100)),
                Box::new(v("p")),
            )),
        )];
        atoms.extend(bnd("a"));
        atoms.extend(bnd("b"));
        atoms.push(F::Gt(
            Box::new(F::Mul(Box::new(v("a")), Box::new(v("b")))),
            Box::new(F::Int(65535)),
        ));
        assert_eq!(check_refute_vc(&F::And(atoms)), Some(RefuteOutcome::RefutedModulo3));
    }

    /// The guarded-check safety-VC discharge (`i < len ∧ len ≤ i ⇒ False`) is a
    /// genuine kernel proof modulo exactly the 3 foundational axioms.
    #[test]
    fn guarded_check_refutation_is_modulo_3() {
        assert_eq!(check_lt_le_contradiction(), RefuteOutcome::RefutedModulo3);
    }

    /// The general producer reconstructs a real-shaped guarded bounds VC
    /// (`i < len ∧ len ≤ i`) over its free variables into `Π(i len:Int). … → False`,
    /// kernel-checked modulo 3 — safety-VC discharge wired end-to-end from a `Formula`.
    #[test]
    fn guarded_vc_refuted_from_formula_modulo_3() {
        use trust_types::{Formula as F, Sort};
        let v = |n: &str| F::Var(n.into(), Sort::Int);
        let vc = F::And(vec![
            F::Lt(Box::new(v("i")), Box::new(v("len"))), // guard: i < len
            F::Le(Box::new(v("len")), Box::new(v("i"))), // violation: len ≤ i
        ]);
        assert_eq!(check_refute_vc(&vc), Some(RefuteOutcome::RefutedModulo3));
    }

    /// A two-strict cycle `a < b ∧ b < a` is refuted modulo 3 — the second strict
    /// atom is weakened to `b ≤ a` via `Int.le_of_lt` and fed to the lt/le core.
    #[test]
    fn two_strict_cycle_refuted_modulo_3() {
        use trust_types::{Formula as F, Sort};
        let v = |n: &str| F::Var(n.into(), Sort::Int);
        let vc = F::And(vec![
            F::Lt(Box::new(v("a")), Box::new(v("b"))),
            F::Lt(Box::new(v("b")), Box::new(v("a"))),
        ]);
        assert_eq!(check_refute_vc(&vc), Some(RefuteOutcome::RefutedModulo3));
    }

    /// A Farkas-derived overflow VC: `0 ≤ x ∧ x+1 < 0` (unsigned-underflow
    /// direction) is refuted modulo 3 — the producer derives `0 ≤ x+1` via
    /// `le_trans (0≤x) (x ≤ x+1)` and feeds it to the lt/le core.
    #[test]
    fn overflow_underflow_vc_refuted_via_le_trans() {
        use trust_types::{Formula as F, Sort};
        let v = |n: &str| F::Var(n.into(), Sort::Int);
        let x_plus_1 = F::Add(Box::new(v("x")), Box::new(F::Int(1)));
        let vc = F::And(vec![
            F::Le(Box::new(F::Int(0)), Box::new(v("x"))),   // 0 ≤ x
            F::Lt(Box::new(x_plus_1), Box::new(F::Int(0))), // x+1 < 0
        ]);
        assert_eq!(check_refute_vc(&vc), Some(RefuteOutcome::RefutedModulo3));
    }

    /// A widening-overflow VC `0 ≤ x ∧ x ≤ 255 ∧ 2147483647 < x+1` (a `u8`→`i32`
    /// `x+1`, which cannot overflow) is refuted modulo 3: the engine derives
    /// `x+1 ≤ 256` via `add_le_add_right` on `x ≤ 255`, then `256 ≤ 2147483647` via
    /// the literal `Int.NonNeg.mk` proof, chained by `le_trans` — the Farkas +
    /// literal-comparison path.
    #[test]
    fn widening_overflow_vc_refuted_via_add_le_add_and_literal() {
        use trust_types::{Formula as F, Sort};
        let x = || F::Var("x".into(), Sort::Int);
        let vc = F::And(vec![
            F::Le(Box::new(F::Int(0)), Box::new(x())),
            F::Le(Box::new(x()), Box::new(F::Int(255))),
            F::Lt(
                Box::new(F::Int(2147483647)),
                Box::new(F::Add(Box::new(x()), Box::new(F::Int(1)))),
            ),
        ]);
        assert_eq!(check_refute_vc(&vc), Some(RefuteOutcome::RefutedModulo3));
    }

    /// A multi-variable additive-overflow VC `0≤a≤5 ∧ 0≤b≤3 ∧ 10 < a+b` is refuted
    /// modulo 3: the engine sums the per-variable bounds `a≤5`, `b≤3` to `a+b ≤ 8`
    /// via `Int.add_le_add` (`add_le_add_right` ∘ `add_le_add_left` by `le_trans`),
    /// then contradicts `10 < a+b ≤ 8`. Single-variable lifting cannot reach this.
    #[test]
    fn additive_overflow_two_vars_refuted_via_add_le_add() {
        use trust_types::{Formula as F, Sort};
        let a = || F::Var("a".into(), Sort::Int);
        let b = || F::Var("b".into(), Sort::Int);
        let vc = F::And(vec![
            F::Le(Box::new(F::Int(0)), Box::new(a())),
            F::Le(Box::new(a()), Box::new(F::Int(5))),
            F::Le(Box::new(F::Int(0)), Box::new(b())),
            F::Le(Box::new(b()), Box::new(F::Int(3))),
            F::Lt(Box::new(F::Int(10)), Box::new(F::Add(Box::new(a()), Box::new(b())))),
        ]);
        assert_eq!(check_refute_vc(&vc), Some(RefuteOutcome::RefutedModulo3));
    }

    /// A BITVECTOR-encoded multiplication-overflow VC — the exact shape
    /// `trust-vcgen` emits for a widening `u16*u16 → u32` multiply,
    /// `¬(bv_x = 0) ∧ ¬(bvudiv(bvmul(bv_x,bv_y), bv_x) = bv_y)` over
    /// `BvZeroExt(_:BitVec(16),16)` operands — is reconstructed modulo 3.
    /// `bv_overflow_to_int` recognizes the encoding and rewrites it to the
    /// sound Int abstraction `0≤x≤65535 ∧ 0≤y≤65535 ∧ x*y > u32::MAX`, which
    /// the two-variable `Int.mul_le_mul` lift then refutes
    /// (`x*y ≤ 65535*65535 = 4294836225 ≤ u32::MAX`). No AY, no new Clean lemma.
    #[test]
    fn bitvector_widening_mul_overflow_refuted_via_bv_to_int() {
        use trust_types::{Formula as F, Sort};
        let bvx = || F::BvZeroExt(Box::new(F::Var("x".into(), Sort::BitVec(16))), 16);
        let bvy = || F::BvZeroExt(Box::new(F::Var("y".into(), Sort::BitVec(16))), 16);
        let vc = F::And(vec![
            F::Not(Box::new(F::Eq(Box::new(bvx()), Box::new(F::BitVec { value: 0, width: 32 })))),
            F::Not(Box::new(F::Eq(
                Box::new(F::BvUDiv(
                    Box::new(F::BvMul(Box::new(bvx()), Box::new(bvy()), 32)),
                    Box::new(bvx()),
                    32,
                )),
                Box::new(bvy()),
            ))),
        ]);
        assert_eq!(check_refute_vc(&vc), Some(RefuteOutcome::RefutedModulo3));
    }

    /// The `u64` analogue — a widening `u32*u32 → u64` whose overflow threshold
    /// `2^64-1` exceeds `i64::MAX`. This reconstructs modulo 3 only because Clean's
    /// native Int reducer carries `i128` (reduces `Int.le` up to `u64::MAX`); it
    /// regression-guards that kernel fix from the Trust side.
    #[test]
    fn bitvector_u64_widening_mul_overflow_refuted_via_bv_to_int() {
        use trust_types::{Formula as F, Sort};
        let bvx = || F::BvZeroExt(Box::new(F::Var("x".into(), Sort::BitVec(32))), 32);
        let bvy = || F::BvZeroExt(Box::new(F::Var("y".into(), Sort::BitVec(32))), 32);
        let vc = F::And(vec![
            F::Not(Box::new(F::Eq(Box::new(bvx()), Box::new(F::BitVec { value: 0, width: 64 })))),
            F::Not(Box::new(F::Eq(
                Box::new(F::BvUDiv(
                    Box::new(F::BvMul(Box::new(bvx()), Box::new(bvy()), 64)),
                    Box::new(bvx()),
                    64,
                )),
                Box::new(bvy()),
            ))),
        ]);
        assert_eq!(check_refute_vc(&vc), Some(RefuteOutcome::RefutedModulo3));
    }

    /// A SIGNED add-overflow VC with the disjunctive violation vcgen emits —
    /// `MIN ≤ x ≤ MAX ∧ x < MAX ∧ (x+1 < MIN ∨ x+1 > MAX)` (from `if x < MAX { x+1 }`)
    /// — is refuted modulo 3. Both `Or` arms close: the overflow arm `x+1 > MAX`
    /// against the guard `x < MAX` (which IS `x+1 ≤ MAX` since `Int.lt a b := le (a+1) b`),
    /// and the underflow arm `x+1 < MIN` against `MIN ≤ x ≤ x+1`. Exercises the
    /// `Or.rec` case-split plus both `Add(base,1)` `derive_le` cases.
    #[test]
    fn signed_add_overflow_refuted_via_or_split_and_add_one_le() {
        use trust_types::{Formula as F, Sort};
        let x = || F::Var("x".into(), Sort::Int);
        let (min, max) = (-2147483648i128, 2147483647i128);
        let xp1 = || F::Add(Box::new(x()), Box::new(F::Int(1)));
        let vc = F::And(vec![
            F::Le(Box::new(F::Int(min)), Box::new(x())),
            F::Le(Box::new(x()), Box::new(F::Int(max))),
            F::Lt(Box::new(x()), Box::new(F::Int(max))),
            F::Or(vec![
                F::Lt(Box::new(xp1()), Box::new(F::Int(min))),
                F::Gt(Box::new(xp1()), Box::new(F::Int(max))),
            ]),
        ]);
        assert_eq!(check_refute_vc(&vc), Some(RefuteOutcome::RefutedModulo3));
    }

    /// `MIN ≤ x-1` from a strict lower bound `MIN < x` — the underflow arm of a
    /// signed `x-1`. `MIN < x` is `Int.le (x... no: Int.lt MIN x ≡ Int.le (MIN+1) x`;
    /// shifting by `Int.neg 1` (`add_le_add_right`) and cancelling `(MIN+1)+(-1)=MIN`
    /// (`add_neg_cancel_right` under `Eq.subst`) yields `MIN ≤ x-1`. The `1` is the
    /// CANONICAL `Int.ofNat (Nat.succ Nat.zero)` (matching `Int.lt`'s definition) so
    /// the strict proof matches `add_le_add_right`'s argument type syntactically.
    #[test]
    fn sub_one_underflow_le_from_strict_lower_bound() {
        use trust_types::{Formula as F, Sort};
        let x = || F::Var("x".into(), Sort::Int);
        let min = -2147483648i128;
        let vc = F::And(vec![
            F::Lt(Box::new(F::Int(min)), Box::new(x())),
            F::Lt(Box::new(F::Sub(Box::new(x()), Box::new(F::Int(1)))), Box::new(F::Int(min))),
        ]);
        assert_eq!(check_refute_vc(&vc), Some(RefuteOutcome::RefutedModulo3));
    }

    /// The full SIGNED `x-1` decrement-underflow VC `MIN ≤ x ≤ MAX ∧ x > MIN ∧
    /// (x-1 < MIN ∨ x-1 > MAX)` (from `if x > MIN { x-1 }`) — both `Or` arms close:
    /// the underflow arm `x-1 < MIN` against the guard `MIN < x` (canonical-1 path),
    /// and the (vacuous) overflow arm `x-1 > MAX` against `x ≤ MAX` (literal-`-1`
    /// `le_trans` path: `x-1 ≤ MAX-1 ≤ MAX`).
    #[test]
    fn signed_decrement_underflow_refuted_both_arms() {
        use trust_types::{Formula as F, Sort};
        let x = || F::Var("x".into(), Sort::Int);
        let (min, max) = (-2147483648i128, 2147483647i128);
        let xm1 = || F::Sub(Box::new(x()), Box::new(F::Int(1)));
        let vc = F::And(vec![
            F::Le(Box::new(F::Int(min)), Box::new(x())),
            F::Le(Box::new(x()), Box::new(F::Int(max))),
            F::Gt(Box::new(x()), Box::new(F::Int(min))),
            F::Or(vec![
                F::Lt(Box::new(xm1()), Box::new(F::Int(min))),
                F::Gt(Box::new(xm1()), Box::new(F::Int(max))),
            ]),
        ]);
        assert_eq!(check_refute_vc(&vc), Some(RefuteOutcome::RefutedModulo3));
    }

    /// A NESTED additive-overflow VC `0≤a,b,c≤5 ∧ a+b+c > 100` is refuted modulo 3:
    /// `additive_upper_bound` recurses through `Add(Add(a,b),c)` to `a+b+c ≤ 15`
    /// (chained `add_le_add`), then `15 ≤ 100`. Single-level summing can't reach a
    /// three-term sum.
    #[test]
    fn nested_three_term_add_overflow_refuted() {
        use trust_types::{Formula as F, Sort};
        let v = |n: &str| F::Var(n.into(), Sort::Int);
        let abc = F::Add(Box::new(F::Add(Box::new(v("a")), Box::new(v("b")))), Box::new(v("c")));
        let bnd = |n: &str| {
            vec![
                F::Le(Box::new(F::Int(0)), Box::new(v(n))),
                F::Le(Box::new(v(n)), Box::new(F::Int(5))),
            ]
        };
        let mut atoms: Vec<F> = ["a", "b", "c"].iter().flat_map(|n| bnd(n)).collect();
        atoms.push(F::Lt(Box::new(F::Int(100)), Box::new(abc)));
        assert_eq!(check_refute_vc(&F::And(atoms)), Some(RefuteOutcome::RefutedModulo3));
    }

    /// A SIGNED two-variable add-overflow VC `(-1000<a<1000) ∧ (-1000<b<1000) ∧
    /// (a+b<MIN ∨ a+b>MAX)` (from `if -1000<a<1000 && -1000<b<1000 { a+b }`). Both
    /// `Or` arms close via two-variable `add_le_add`: the overflow arm `a+b>MAX`
    /// from the UPPER bounds (`a+b ≤ 1000+1000 ≤ MAX`) and the underflow arm
    /// `a+b<MIN` from the LOWER bounds (`MIN ≤ -1000+-1000 ≤ a+b`).
    #[test]
    fn signed_two_var_add_overflow_refuted_via_add_le_add_both_sides() {
        use trust_types::{Formula as F, Sort};
        let a = || F::Var("a".into(), Sort::Int);
        let b = || F::Var("b".into(), Sort::Int);
        let (min, max) = (-2147483648i128, 2147483647i128);
        let ab = || F::Add(Box::new(a()), Box::new(b()));
        let vc = F::And(vec![
            F::Lt(Box::new(a()), Box::new(F::Int(1000))),
            F::Lt(Box::new(b()), Box::new(F::Int(1000))),
            F::Lt(Box::new(F::Int(-1000)), Box::new(a())),
            F::Lt(Box::new(F::Int(-1000)), Box::new(b())),
            F::Or(vec![
                F::Lt(Box::new(ab()), Box::new(F::Int(min))),
                F::Gt(Box::new(ab()), Box::new(F::Int(max))),
            ]),
        ]);
        assert_eq!(check_refute_vc(&vc), Some(RefuteOutcome::RefutedModulo3));
    }

    /// A bitvector multiply-by-CONSTANT overflow VC — `(x as u32) * 2` for `x:u16`.
    /// `bv_overflow_to_int` maps the BitVec literal operand to `Int(2)` (no bound)
    /// and the widened var to `0≤x≤2^16-1`, so the existing `base*c` lift refutes
    /// `x*2 ≤ 65535*2 < 2^32-1`.
    #[test]
    fn bitvector_mul_by_constant_overflow_refuted() {
        use trust_types::{Formula as F, Sort};
        let bvx = || F::BvZeroExt(Box::new(F::Var("x".into(), Sort::BitVec(16))), 16);
        let two = || F::BitVec { value: 2, width: 32 };
        let vc = F::And(vec![
            F::Not(Box::new(F::Eq(Box::new(bvx()), Box::new(F::BitVec { value: 0, width: 32 })))),
            F::Not(Box::new(F::Eq(
                Box::new(F::BvUDiv(
                    Box::new(F::BvMul(Box::new(bvx()), Box::new(two()), 32)),
                    Box::new(bvx()),
                    32,
                )),
                Box::new(two()),
            ))),
        ]);
        assert_eq!(check_refute_vc(&vc), Some(RefuteOutcome::RefutedModulo3));
    }

    /// A guarded subtraction-underflow VC `a ≥ b ∧ a - b < 0` (the shape vcgen
    /// emits for `if a >= b { a - b }`) is refuted modulo 3: `0 ≤ a-b` is derived
    /// from the guard `b ≤ a` via `Eq.subst`/`Int.add_zero` (bridging the `-0` in
    /// `Int.le 0 (a-b) = NonNeg((a-b)-0)`), then contradicts `a-b < 0`. No kernel
    /// reduction change — the proof is a pure lemma application.
    #[test]
    fn guarded_subtraction_underflow_refuted_via_add_zero() {
        use trust_types::{Formula as F, Sort};
        let a = || F::Var("a".into(), Sort::Int);
        let b = || F::Var("b".into(), Sort::Int);
        let vc = F::And(vec![
            F::Ge(Box::new(a()), Box::new(b())),
            F::Lt(Box::new(F::Sub(Box::new(a()), Box::new(b()))), Box::new(F::Int(0))),
        ]);
        assert_eq!(check_refute_vc(&vc), Some(RefuteOutcome::RefutedModulo3));
    }

    /// F2 case (a): `0 ≤ b ∧ a - b > a` is refuted modulo 3 — the constant-/var-
    /// minuend clamp `a - b ≤ a` (the violation's anchor `a < a-b`) is derived from
    /// `0 ≤ b` via `sub_le_self` (lift `neg b ≤ 0` to `a + neg b ≤ a + 0`, then
    /// `add_zero`), contradicting `a < a-b`. Pure lemma application, no kernel change.
    #[test]
    fn sub_le_self_clamp_refuted() {
        use trust_types::{Formula as F, Sort};
        let v = |n: &str| F::Var(n.into(), Sort::Int);
        let vc = F::And(vec![
            F::Le(Box::new(F::Int(0)), Box::new(v("b"))),
            F::Gt(Box::new(F::Sub(Box::new(v("a")), Box::new(v("b")))), Box::new(v("a"))),
        ]);
        assert_eq!(check_refute_vc(&vc), Some(RefuteOutcome::RefutedModulo3));
    }

    /// F2 case (c): the surfaced subtraction upper bound feeds the two-variable
    /// `Int.mul_le_mul` lift — `0≤a≤255 ∧ 0≤b≤255 ∧ a*(255-b) > 65535` is refuted
    /// modulo 3. `a*(255-b) ≤ 255*255 = 65025 ≤ 65535`: the `255-b` factor is bounded
    /// by `sub_upper_bound` (`255 - b ≤ 255` from `0 ≤ b`) and shown nonneg
    /// (`0 ≤ 255-b` from `b ≤ 255`), so the product lift discharges.
    #[test]
    fn product_with_subtraction_factor_refuted_via_mul_le_mul() {
        use trust_types::{Formula as F, Sort};
        let v = |n: &str| F::Var(n.into(), Sort::Int);
        let prod =
            F::Mul(Box::new(v("a")), Box::new(F::Sub(Box::new(F::Int(255)), Box::new(v("b")))));
        let vc = F::And(vec![
            F::Le(Box::new(F::Int(0)), Box::new(v("a"))),
            F::Le(Box::new(v("a")), Box::new(F::Int(255))),
            F::Le(Box::new(F::Int(0)), Box::new(v("b"))),
            F::Le(Box::new(v("b")), Box::new(F::Int(255))),
            F::Gt(Box::new(prod), Box::new(F::Int(65535))),
        ]);
        assert_eq!(check_refute_vc(&vc), Some(RefuteOutcome::RefutedModulo3));
    }

    /// F2 case (b), two-sided BOTH arms: a widening difference `(a as i64) - (b as
    /// i64)` for `a,b : i32` (`MIN ≤ x,y ≤ MAX`) cannot leave i64 range. The VC
    /// `MIN_i32≤x≤MAX_i32 ∧ MIN_i32≤y≤MAX_i32 ∧ (x-y < MIN_i64 ∨ x-y > MAX_i64)` is
    /// refuted modulo 3: the overflow arm via `sub_le_sub` (`x-y ≤ MAX_i32 - MIN_i32`)
    /// and the underflow arm via `sub_lower_bound` (`MIN_i32 - MAX_i32 ≤ x-y`), each
    /// `Int.neg`-monotone (`neg_le_neg`) + `add_le_add`, chained by `le_trans`.
    #[test]
    fn widening_difference_both_arms_refuted_via_sub_le_sub() {
        use trust_types::{Formula as F, Sort};
        let v = |n: &str| F::Var(n.into(), Sort::Int);
        let (i32min, i32max) = (-2147483648i128, 2147483647i128);
        let (i64min, i64max) = (-9223372036854775808i128, 9223372036854775807i128);
        let bnds = |n: &str| {
            vec![
                F::Le(Box::new(F::Int(i32min)), Box::new(v(n))),
                F::Le(Box::new(v(n)), Box::new(F::Int(i32max))),
            ]
        };
        let xy = || F::Sub(Box::new(v("x")), Box::new(v("y")));
        let mut atoms: Vec<F> = bnds("x").into_iter().chain(bnds("y")).collect();
        atoms.push(F::Or(vec![
            F::Lt(Box::new(xy()), Box::new(F::Int(i64min))),
            F::Gt(Box::new(xy()), Box::new(F::Int(i64max))),
        ]));
        assert_eq!(check_refute_vc(&F::And(atoms)), Some(RefuteOutcome::RefutedModulo3));
    }

    /// A multiplication-overflow VC `0 ≤ x ∧ x ≤ 999 ∧ u32::MAX < x*2` (a `u32`
    /// `x*2` that cannot overflow) is refuted modulo 3: the engine derives
    /// `x*2 ≤ 999*2 = 1998` via `Int.mul_le_mul_of_nonneg_right` on `x ≤ 999`,
    /// then `1998 ≤ u32::MAX` by the literal proof, chained by `le_trans`.
    #[test]
    fn mul_overflow_vc_refuted_via_mul_le_mul() {
        use trust_types::{Formula as F, Sort};
        let x = || F::Var("x".into(), Sort::Int);
        let vc = F::And(vec![
            F::Le(Box::new(F::Int(0)), Box::new(x())),
            F::Le(Box::new(x()), Box::new(F::Int(999))),
            F::Lt(
                Box::new(F::Int(4294967295)),
                Box::new(F::Mul(Box::new(x()), Box::new(F::Int(2)))),
            ),
        ]);
        assert_eq!(check_refute_vc(&vc), Some(RefuteOutcome::RefutedModulo3));
    }

    /// A range-check VC `lo ≤ i ∧ i ≤ hi ∧ (i < lo ∨ hi < i)` is refuted modulo 3
    /// via `Or.rec` case-split — each disjunct directly contradicts a bound.
    #[test]
    fn range_check_vc_refuted_via_or_rec() {
        use trust_types::{Formula as F, Sort};
        let v = |n: &str| F::Var(n.into(), Sort::Int);
        let vc = F::And(vec![
            F::Le(Box::new(v("lo")), Box::new(v("i"))),
            F::Le(Box::new(v("i")), Box::new(v("hi"))),
            F::Or(vec![
                F::Lt(Box::new(v("i")), Box::new(v("lo"))), // i < lo
                F::Lt(Box::new(v("hi")), Box::new(v("i"))), // hi < i
            ]),
        ]);
        assert_eq!(check_refute_vc(&vc), Some(RefuteOutcome::RefutedModulo3));
    }

    /// A guarded bounds VC in REAL MIR shape — aux temps `_3 := len`,
    /// `_4 := (i < _3)`, the guard `_4` asserted, and the violation `i ≥ _3` — is
    /// refuted modulo 3: `simplify_vc` inlines the temps to `i < len ∧ i ≥ len`,
    /// which the linear engine contradicts. This is the boolean-aux-var layer.
    #[test]
    fn guarded_vc_with_aux_temps_refuted_modulo_3() {
        use trust_types::{Formula as F, Sort};
        let iv = |n: &str| F::Var(n.into(), Sort::Int);
        let bv = |n: &str| F::Var(n.into(), Sort::Bool);
        let vc = F::And(vec![
            F::Eq(Box::new(iv("_3")), Box::new(iv("len"))), // _3 := len
            F::Eq(Box::new(bv("_4")), Box::new(F::Lt(Box::new(iv("i")), Box::new(iv("_3"))))), // _4 := i<_3
            bv("_4"),                                     // guard: _4 holds (i < _3)
            F::Ge(Box::new(iv("i")), Box::new(iv("_3"))), // violation: i ≥ _3
        ]);
        assert_eq!(check_refute_vc(&vc), Some(RefuteOutcome::RefutedModulo3));
    }

    /// A guarded division in REAL MIR shape — `_g := (b==0)`, guard `¬_g`
    /// (i.e. `b ≠ 0`), and the div-by-zero violation `b == 0` — is refuted modulo
    /// 3 via the propositional contradiction `(¬(b==0)) (b==0) : False` after
    /// `simplify_vc` inlines `_g`.
    #[test]
    fn guarded_div_by_zero_refuted_via_prop_contradiction() {
        use trust_types::{Formula as F, Sort};
        let b = F::Var("b".into(), Sort::Int);
        let g = F::Var("_g".into(), Sort::Bool);
        let cond = F::Eq(Box::new(b), Box::new(F::Int(0))); // b == 0
        let vc = F::And(vec![
            F::Eq(Box::new(g.clone()), Box::new(cond.clone())), // _g := (b == 0)
            F::Not(Box::new(g)),                                // guard: ¬_g (b ≠ 0)
            cond,                                               // violation: b == 0
        ]);
        assert_eq!(check_refute_vc(&vc), Some(RefuteOutcome::RefutedModulo3));
    }

    /// An equality plus a contradicting strict — `ret = x ∧ ret < x` — is refuted
    /// modulo 3: `Eq`-handling yields `x ≤ ret` (via `Eq.subst` on `le_refl`), which
    /// the strict `ret < x` contradicts.
    #[test]
    fn eq_with_strict_refuted_via_eq_subst() {
        use trust_types::{Formula as F, Sort};
        let v = |n: &str| F::Var(n.into(), Sort::Int);
        let vc = F::And(vec![
            F::Eq(Box::new(v("ret")), Box::new(v("x"))),
            F::Lt(Box::new(v("ret")), Box::new(v("x"))),
        ]);
        assert_eq!(check_refute_vc(&vc), Some(RefuteOutcome::RefutedModulo3));
    }

    /// `Eq` forcing a false literal bound: `r = 1 ∧ r ≤ 0` is refuted modulo 3 —
    /// `Eq`-handling gives `1 ≤ r`, chained with `r ≤ 0` to the false `1 ≤ 0`,
    /// contradicted by the literal `0 < 1`.
    #[test]
    fn eq_with_false_literal_bound_refuted() {
        use trust_types::{Formula as F, Sort};
        let vc = F::And(vec![
            F::Eq(Box::new(F::Var("r".into(), Sort::Int)), Box::new(F::Int(1))),
            F::Le(Box::new(F::Var("r".into(), Sort::Int)), Box::new(F::Int(0))),
        ]);
        assert_eq!(check_refute_vc(&vc), Some(RefuteOutcome::RefutedModulo3));
    }

    /// An unguarded / satisfiable VC (just `i ≥ len`, a real out-of-bounds bug)
    /// has no contradiction — the producer fails closed (never fabricates a proof).
    #[test]
    fn unguarded_vc_is_not_refuted() {
        use trust_types::{Formula as F, Sort};
        let v = |n: &str| F::Var(n.into(), Sort::Int);
        let vc = F::Ge(Box::new(v("i")), Box::new(v("len")));
        assert_eq!(refute_vc(&vc).is_none(), true);
    }

    /// The enum-match exhaustiveness `Unreachable` VC, in the exact shape `trust-vcgen`
    /// emits for `match s { A=>.., B=>.., C=>.. }` with a compiler `_ => unreachable!()`:
    /// the discriminant-validity `disc ∈ {0,1,2}` (a 3-way `Or`, grounded right-nested
    /// into `Or d0 (Or d1 d2)`) together with the per-variant exclusions
    /// `disc ≠ 0 ∧ disc ≠ 1 ∧ disc ≠ 2`, whose conjunction is `False`. Refuted modulo 3
    /// by the n-ary `Or.rec` case-split: each `disc = k` disjunct (a hypothesis) closes
    /// propositionally against its `disc ≠ k` atom (`(¬(disc=k)) (disc=k) : False`).
    #[test]
    fn enum_exhaustiveness_three_way_unreachable_refuted_via_nary_or() {
        use trust_types::{Formula as F, Sort};
        let d = || F::Var("disc".into(), Sort::Int);
        let eq = |k: i128| F::Eq(Box::new(d()), Box::new(F::Int(k)));
        let neq = |k: i128| F::Not(Box::new(eq(k)));
        let vc = F::And(vec![
            F::And(vec![neq(0), neq(1), neq(2)]),
            F::And(vec![F::Or(vec![eq(0), eq(1), eq(2)]), F::Bool(true)]),
        ]);
        assert_eq!(check_refute_vc(&vc), Some(RefuteOutcome::RefutedModulo3));
    }

    /// The 4-variant enum-exhaustiveness `Unreachable` VC — `disc ∈ {0,1,2,3}` against
    /// `disc ≠ 0 ∧ … ∧ disc ≠ 3` — refuted modulo 3. Drives the n-ary `Or.rec` one
    /// level deeper than the three-way case (the recursor nests `Or d0 (Or d1 (Or d2 d3))`),
    /// confirming the de-Bruijn depth bookkeeping stays correct as binders accumulate.
    #[test]
    fn enum_exhaustiveness_four_way_unreachable_refuted_via_nary_or() {
        use trust_types::{Formula as F, Sort};
        let d = || F::Var("disc".into(), Sort::Int);
        let eq = |k: i128| F::Eq(Box::new(d()), Box::new(F::Int(k)));
        let neq = |k: i128| F::Not(Box::new(eq(k)));
        let vc = F::And(vec![
            F::And(vec![neq(0), neq(1), neq(2), neq(3)]),
            F::And(vec![F::Or(vec![eq(0), eq(1), eq(2), eq(3)]), F::Bool(true)]),
        ]);
        assert_eq!(check_refute_vc(&vc), Some(RefuteOutcome::RefutedModulo3));
    }

    #[test]
    fn propositional_refutation_fuel_exhaustion_declines_fail_closed() {
        // The work fuse is checked before even an immediately contradictory
        // hypothesis is consumed. Exhaustion therefore cannot accidentally
        // return an incomplete proof assembled by the search.
        let prop = || Prop { formula: Formula::Bool(false), proof: Expr::bvar(0) };
        let mut exhausted = 0;
        assert!(refute_props(vec![prop()], &[], 0, 0, &mut exhausted).is_none());

        // One unit is enough for this non-recursive leaf, proving the first
        // assertion exercises the fuse rather than an unrelated decline.
        let mut one_step = 1;
        assert!(refute_props(vec![prop()], &[], 0, 0, &mut one_step).is_some());
        assert_eq!(one_step, 0);
    }

    /// A GUARDED-SHIFT overflow VC `0 ≤ idx ∧ idx ≤ 3 ∧ idx*8 ≥ 32` (the shape
    /// `bitops_byte_at`'s `value >> (idx*8)` produces under the byte-index guard
    /// `idx ≤ 3`) is refuted modulo 3. The violation `idx*8 ≥ 32` normalizes to the
    /// NON-strict `32 ≤ idx*8`; the new non-strict anchor derives the reverse strict
    /// `idx*8 < 32` from the literal upper bound `idx*8 ≤ 3*8 = 24 < 32`
    /// (`additive_upper_bound`'s `Mul` lift via `mul_le_mul_of_nonneg_right`), giving
    /// `idx*8 < idx*8 ⇒ False`. This is the linear-contradiction route the masked /
    /// guarded shift-width checks take once the opaque BV shift amount is grounded.
    #[test]
    fn guarded_shift_mul_bound_refuted_via_nonstrict_anchor() {
        use trust_types::{Formula as F, Sort};
        let idx = || F::Var("idx".into(), Sort::Int);
        let prod = || F::Mul(Box::new(idx()), Box::new(F::Int(8)));
        let vc = F::And(vec![
            F::Le(Box::new(F::Int(0)), Box::new(idx())),
            F::Le(Box::new(idx()), Box::new(F::Int(3))),
            F::Ge(Box::new(prod()), Box::new(F::Int(32))), // violation: shift width ≥ 32
        ]);
        assert_eq!(check_refute_vc(&vc), Some(RefuteOutcome::RefutedModulo3));
    }

    /// A masked-shift VC where the shift amount is an OPAQUE `BvToInt(BvAnd(..))`
    /// term (the `n & 31` idiom) carried with its `≤ 31` bound, plus the violation
    /// `amt ≥ 32`. `abstract_opaque_int` replaces the `BvToInt(..)` subterm by a fresh
    /// `Int` var (sound one-directional abstraction — keeps every atom, adds none), so
    /// the engine sees `0 ≤ v ∧ v ≤ 31 ∧ v ≥ 32` and the non-strict anchor closes it
    /// via `v < 32` (`v ≤ 31 < 32`). Mirrors `bitops_rotl`'s in-range shift check.
    #[test]
    fn masked_opaque_shift_amount_refuted_via_abstraction() {
        use trust_types::{Formula as F, Sort};
        // amt = (n & 31) as the vcgen-emitted BvToInt(BvAnd(IntToBv(n,32),31,32)) term.
        let amt = || {
            F::BvToInt(
                Box::new(F::BvAnd(
                    Box::new(F::IntToBv(Box::new(F::Var("n".into(), Sort::Int)), 32)),
                    Box::new(F::IntToBv(Box::new(F::Int(31)), 32)),
                    32,
                )),
                32,
                false,
            )
        };
        let vc = F::And(vec![
            F::Le(Box::new(F::Int(0)), Box::new(amt())),
            F::Le(Box::new(amt()), Box::new(F::Int(31))),
            F::Ge(Box::new(amt()), Box::new(F::Int(32))), // violation: shift width ≥ 32
        ]);
        assert_eq!(check_refute_vc(&vc), Some(RefuteOutcome::RefutedModulo3));
    }

    /// An ARITHMETIC slice-index VC `0 ≤ i ∧ i < len ∧ (len-1) - i ≥ len` (the mirror
    /// index `s[(len-1) - i]` under `i < len`) is refuted modulo 3. The violation
    /// `(len-1)-i ≥ len` normalizes to the non-strict `len ≤ (len-1)-i`; the anchor
    /// derives `(len-1)-i < len` via the case-(a) clamp `(len-1)-i ≤ len-1`
    /// (`sub_le_self` from `0 ≤ i`) chained with the strict predecessor `len-1 < len`
    /// (`lt_sub_lit`), giving the self-contradiction.
    #[test]
    fn arithmetic_slice_mirror_index_refuted_via_sub_le_self_and_pred() {
        use trust_types::{Formula as F, Sort};
        let v = |n: &str| F::Var(n.into(), Sort::Int);
        let mirror =
            || F::Sub(Box::new(F::Sub(Box::new(v("len")), Box::new(F::Int(1)))), Box::new(v("i")));
        let vc = F::And(vec![
            F::Le(Box::new(F::Int(0)), Box::new(v("i"))),
            F::Lt(Box::new(v("i")), Box::new(v("len"))),
            F::Ge(Box::new(mirror()), Box::new(v("len"))), // violation: mirror ≥ len
        ]);
        assert_eq!(check_refute_vc(&vc), Some(RefuteOutcome::RefutedModulo3));
    }

    /// An ARITHMETIC slice-index VC `len - off ≥ 4 ∧ off < len ∧ off + 1 ≥ len` (the
    /// `s[off + 1]` access guarded by `len - off ≥ 4`, the shape `parse_*_u32_at`
    /// produces) is refuted modulo 3. The violation `off+1 ≥ len` normalizes to
    /// `len ≤ off+1`; the anchor derives `off+1 < len` by moving the addend across the
    /// guard subtraction — `off+1 < off+4` (`add_lt_add_left`) and `off+4 ≤ len`
    /// (`add_across_le` from `4 ≤ len-off`) — chained by `lt_of_lt_of_le`.
    #[test]
    fn arithmetic_slice_off_plus_one_refuted_via_add_across() {
        use trust_types::{Formula as F, Sort};
        let v = |n: &str| F::Var(n.into(), Sort::Int);
        let vc = F::And(vec![
            F::Ge(Box::new(F::Sub(Box::new(v("len")), Box::new(v("off")))), Box::new(F::Int(4))),
            F::Lt(Box::new(v("off")), Box::new(v("len"))),
            F::Ge(Box::new(F::Add(Box::new(v("off")), Box::new(F::Int(1)))), Box::new(v("len"))),
        ]);
        assert_eq!(check_refute_vc(&vc), Some(RefuteOutcome::RefutedModulo3));
    }

    /// A genuinely SATISFIABLE arithmetic slice VC — `0 ≤ i ∧ i + 1 ≥ len` with NO
    /// upper guard on `i` (a real out-of-bounds: `i = len-1` makes `i+1 = len`) — is
    /// NOT refuted. Guards the non-strict anchor / `add_across_le` against fabricating
    /// a proof for an unguarded index. (Soundness regression test.)
    #[test]
    fn unguarded_arithmetic_slice_index_not_refuted() {
        use trust_types::{Formula as F, Sort};
        let v = |n: &str| F::Var(n.into(), Sort::Int);
        let vc = F::And(vec![
            F::Le(Box::new(F::Int(0)), Box::new(v("i"))),
            F::Ge(Box::new(F::Add(Box::new(v("i")), Box::new(F::Int(1)))), Box::new(v("len"))),
        ]);
        assert_eq!(refute_vc(&vc), None);
    }

    /// ADVERSARIAL PROBE 1 (equality-boundary guard) — SOUNDNESS GUARD: a `≤`
    /// (non-strict) guard `i ≤ len` together with the negated-safety atom `len ≤ i`
    /// asserts ONLY `i = len` (both directions of `≤` hold simultaneously) — a
    /// genuinely SATISFIABLE case (e.g. `i = len = 0`), NOT a contradiction. A
    /// bounds check that only guards with `≤` instead of the strict `<` a real
    /// index access needs is exactly the off-by-one this probes for: two
    /// non-strict bounds in opposite directions must NEVER manufacture a STRICT
    /// fact (which is what the engine would need to reach `False` here — `Int.lt`
    /// is `Int.le (a+1) b`, a genuine `+1` gap that two plain `≤`s cannot supply).
    /// Must NOT refute — pins that `derive_le`/`prove_lt` never fabricate
    /// strictness from non-strict premises alone.
    #[test]
    fn nonstrict_guard_both_directions_is_equality_not_refuted() {
        use trust_types::{Formula as F, Sort};
        let v = |n: &str| F::Var(n.into(), Sort::Int);
        let vc = F::And(vec![
            F::Le(Box::new(v("i")), Box::new(v("len"))), // guard: i ≤ len (NOT i < len)
            F::Le(Box::new(v("len")), Box::new(v("i"))), // "violation": len ≤ i
        ]);
        assert_eq!(
            check_refute_vc(&vc),
            None,
            "i≤len ∧ len≤i asserts i=len (satisfiable) — must NOT be refuted"
        );
    }
}
