// trust-certify: finite forward-simulation re-check lane (M6 first slice + link 1).
//
// The QF_LIA lane in `lib.rs` re-checks a solver UNSAT as a kernel proof that a
// reconstructed term inhabits `False`. This module adds a SECOND, sibling lane
// for a different obligation shape — a FINITE FORWARD SIMULATION between two
// transition functions that agree pointwise:
//
//   * `NatRefl`   : ∀ (s b : Nat), Eq Nat (tstep s b) (spec s b)
//                   — when the two functions are GLOBALLY def-equal, discharged
//                     by a single `Eq.refl`.
//   * `EnumCases` : ∀ (s : Dom), Eq Nat (f s) (g s)  over a finite inductive
//                   domain `Dom`, where f and g agree CELL-BY-CELL but are NOT
//                   globally def-equal — discharged by an explicit `Dom.casesOn`
//                   case analysis (one `Eq.refl` per constructor). This is the
//                   real shape of a lookup-table-vs-spec refinement (the §5.1 /
//                   aterm-parser `cases bc <;> rfl` proof, hand-built as a raw
//                   kernel `Expr`).
//
// Both are CLOSED checks: no free variables, no SMT solver, no `Formula`. The
// proof term is a real kernel CIC `Expr`; the clean kernel
// (`TypeChecker::check_type`, infer_only = false) is the only trusted
// component — the same TCB the QF_LIA lane rests on.
//
// SOUNDNESS (fail-closed, never a false `Certified`):
//   * evidence is minted ONLY when the clean kernel certifies `term : goal`;
//   * the goal is BUILT by this lane from the caller's `FiniteSimSpec`, NOT
//     reverse-engineered from solver output, and is structurally guarded to be
//     exactly the forward-simulation template (`is_forward_sim_goal`), so no
//     other proposition can ride this lane;
//   * for `EnumCases` the domain inductive + both function bodies are kernel-
//     re-checked by `add_inductive`/`add_decl` (a malformed domain or a body
//     referencing an out-of-env constant fails closed);
//   * the closed context (empty `LocalContext`) admits no smuggled hypotheses;
//   * the spec (flavor + bodies) is bound into the lineage digest, so a
//     certificate for one obligation cannot be replayed against another.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use clean_auto::bridge::ay_contract::{deserialize_term, serialize_term};
use clean_kernel::name::Name;
use clean_kernel::{
    BinderInfo, Declaration, Environment, Expr, InductiveDecl, InductiveType, Level, LocalContext,
    TypeChecker,
};
use sha2::{Digest, Sha256};

/// Lineage domain tag for the finite-simulation `CleanCic` digest. Distinct from
/// the QF_LIA lane's `LINEAGE_DOMAIN` so the two lanes' certificates never alias.
const DFA_LINEAGE_DOMAIN: &str = "trust-certify.cleancic.finite-sim.v1";

/// Constant names the lane registers the two transitions under. Stable so the
/// lineage tags do not depend on caller naming.
const TSTEP: &str = "trust_dfa_tstep";
const SPEC: &str = "trust_dfa_spec";

/// The trusted *statement* of a finite forward-simulation obligation: the lane
/// certifies that two transition functions agree pointwise. The flavor selects
/// the domain shape (and hence the proof shape the caller must supply).
pub struct FiniteSimSpec {
    /// A stable label for the obligation (folded into lineage).
    pub label: String,
    /// The obligation shape + bodies.
    pub flavor: SimFlavor,
}

/// The two supported finite-simulation shapes.
pub enum SimFlavor {
    /// `∀ (s b : Nat), Eq Nat (tstep s b) (spec s b)` — globally def-equal
    /// transitions of type `Nat → Nat → Nat`; discharged by a single `Eq.refl`.
    NatRefl {
        /// Reducible body of the implementation transition, `Nat → Nat → Nat`.
        tstep_def: Expr,
        /// Reducible body of the spec transition, `Nat → Nat → Nat`.
        spec_def: Expr,
    },
    /// `∀ (s : Dom), Eq Nat (f s) (g s)` over a finite inductive domain `Dom`;
    /// f and g agree per-constructor but need not be globally def-equal —
    /// discharged by a `Dom.casesOn` case analysis (one `Eq.refl` per ctor).
    EnumCases {
        /// The finite domain inductive (its single type is `Dom`).
        domain: InductiveDecl,
        /// Reducible body of the implementation transition, `Dom → Nat`.
        impl_def: Expr,
        /// Reducible body of the spec transition, `Dom → Nat`.
        spec_def: Expr,
    },
    /// `∀ (s : St) (c : BC), Eq Nat (table s c) (spec s c)` over TWO nullary-enum
    /// domains; discharged by a NESTED `casesOn` (outer over `St` with a Pi-motive,
    /// each branch an inner `casesOn` over `BC`). This is the faithful aterm
    /// `table_step` shape: the next state depends on BOTH the current state and the
    /// input byte class.
    EnumCases2d {
        /// Outer finite domain (state); single nullary-ctor inductive.
        dom_a: InductiveDecl,
        /// Inner finite domain (byte class); single nullary-ctor inductive.
        dom_b: InductiveDecl,
        /// Reducible body of the implementation transition, `Dom_a → Dom_b → Nat`.
        impl_def: Expr,
        /// Reducible body of the spec transition, `Dom_a → Dom_b → Nat`.
        spec_def: Expr,
    },
}

/// `Nat` as a kernel term.
fn nat_ty() -> Expr {
    Expr::const_(Name::from_string("Nat"), Vec::new())
}

/// `Nat → Nat → Nat` — the type of a `NatRefl` transition.
fn nat_transition_ty() -> Expr {
    Expr::pi(BinderInfo::Default, nat_ty(), Expr::pi(BinderInfo::Default, nat_ty(), nat_ty()))
}

/// Universe level of `Nat` for `Eq`/`Eq.refl`: `Nat : Type 0 = Sort 1`, so the
/// `Eq.{u}` argument is `u = 1`.
fn nat_eq_level() -> Level {
    Level::succ(Level::zero())
}

/// Left-fold a head over argument expressions: `apply(h, [a, b]) = ((h a) b)`.
fn apply(head: Expr, args: Vec<Expr>) -> Expr {
    args.into_iter().fold(head, Expr::app)
}

/// The single inductive type of an `EnumCases` domain.
fn domain_type(domain: &InductiveDecl) -> Option<&InductiveType> {
    domain.types.first()
}

/// True iff `domain` is a single, parameter-free inductive whose every
/// constructor is NULLARY (its type is exactly `Const(Dom)`). This is the shape
/// the `EnumCases` goal + `casesOn` proof assume (`applied1` = `f #0`, casesOn
/// arity = #constructors). A parametric/indexed/field-carrying domain would give
/// the kernel-generated `casesOn` extra binders, so the lane's hand-built proof
/// shape would not match — we reject such a domain UP FRONT (fail-closed) rather
/// than rely on the downstream kernel check to reject the malformed proof. (Pure
/// defense-in-depth: an unsound domain is already caught by `add_inductive`; this
/// turns a silent false-negative on an out-of-shape domain into an explicit one.)
pub(crate) fn is_nullary_enum_domain(domain: &InductiveDecl) -> bool {
    if domain.num_params != 0 || domain.types.len() != 1 {
        return false;
    }
    let dom = &domain.types[0];
    let dom_name = dom.name.to_string();
    dom.constructors.iter().all(|c| is_named_const(&c.type_, &dom_name))
}

/// `Dom → Nat` — the type of an `EnumCases` transition.
fn enum_transition_ty(domain: &InductiveDecl) -> Option<Expr> {
    let dom = domain_type(domain)?;
    Some(Expr::pi(BinderInfo::Default, Expr::const_(dom.name.clone(), vec![]), nat_ty()))
}

/// Fresh environment for the spec, fail-closed (`None`) on any registration
/// failure. `NatRefl`: Nat + Eq + two reducible `Nat→Nat→Nat` defs. `EnumCases`:
/// Nat + Eq + the domain inductive (so `Dom.casesOn` is generated) + two
/// reducible `Dom→Nat` defs. In both arms `add_decl`/`add_inductive` fully
/// kernel-checks the bodies, so a malformed spec fails closed here.
fn build_sim_env(spec: &FiniteSimSpec) -> Option<Environment> {
    let mut env = Environment::default();
    env.init_nat().ok()?;
    env.init_eq().ok()?;
    match &spec.flavor {
        SimFlavor::NatRefl { tstep_def, spec_def } => {
            register_def(&mut env, TSTEP, nat_transition_ty(), tstep_def.clone())?;
            register_def(&mut env, SPEC, nat_transition_ty(), spec_def.clone())?;
        }
        SimFlavor::EnumCases { domain, impl_def, spec_def } => {
            if !is_nullary_enum_domain(domain) {
                return None;
            }
            env.add_inductive(domain.clone()).ok()?;
            let fn_ty = enum_transition_ty(domain)?;
            register_def(&mut env, TSTEP, fn_ty.clone(), impl_def.clone())?;
            register_def(&mut env, SPEC, fn_ty, spec_def.clone())?;
        }
        SimFlavor::EnumCases2d { dom_a, dom_b, impl_def, spec_def } => {
            if !is_nullary_enum_domain(dom_a) || !is_nullary_enum_domain(dom_b) {
                return None;
            }
            env.add_inductive(dom_a.clone()).ok()?;
            env.add_inductive(dom_b.clone()).ok()?;
            let fn_ty = enum_transition_ty_2d(dom_a, dom_b)?;
            register_def(&mut env, TSTEP, fn_ty.clone(), impl_def.clone())?;
            register_def(&mut env, SPEC, fn_ty, spec_def.clone())?;
        }
    }
    Some(env)
}

fn register_def(env: &mut Environment, name: &str, type_: Expr, value: Expr) -> Option<()> {
    env.add_decl(Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
        value,
        is_reducible: true,
    })
    .ok()
}

/// `Eq.{1} Nat lhs rhs`.
fn eq_nat(lhs: Expr, rhs: Expr) -> Expr {
    apply(Expr::const_(Name::from_string("Eq"), vec![nat_eq_level()]), vec![nat_ty(), lhs, rhs])
}

/// `const_name` applied to the two `Nat` binders `#1 #0` (a `NatRefl` cell).
fn applied2(const_name: &str) -> Expr {
    apply(Expr::const_(Name::from_string(const_name), vec![]), vec![Expr::bvar(1), Expr::bvar(0)])
}

/// `const_name` applied to the single domain binder `#0` (an `EnumCases` cell).
fn applied1(const_name: &str) -> Expr {
    Expr::app(Expr::const_(Name::from_string(const_name), vec![]), Expr::bvar(0))
}

/// `const_name #1 #0` — a 2D cell: `#1` = the `dom_a` (state) binder, `#0` = the
/// `dom_b` (byte-class) binder. (Structurally identical to `applied2`'s
/// two-`Nat`-binder shape, reused by the `EnumCases2d` goal/guard.)
fn applied2d(const_name: &str) -> Expr {
    applied2(const_name)
}

/// `Dom_a → Dom_b → Nat` — the type of an `EnumCases2d` transition.
fn enum_transition_ty_2d(dom_a: &InductiveDecl, dom_b: &InductiveDecl) -> Option<Expr> {
    let a = domain_type(dom_a)?;
    let b = domain_type(dom_b)?;
    Some(Expr::pi(
        BinderInfo::Default,
        Expr::const_(a.name.clone(), vec![]),
        Expr::pi(BinderInfo::Default, Expr::const_(b.name.clone(), vec![]), nat_ty()),
    ))
}

/// The forward-simulation goal for the spec's flavor.
fn build_sim_goal(spec: &FiniteSimSpec) -> Option<Expr> {
    match &spec.flavor {
        SimFlavor::NatRefl { .. } => {
            // ∀ (s : Nat) (b : Nat), Eq Nat (tstep s b) (spec s b)
            let body = eq_nat(applied2(TSTEP), applied2(SPEC));
            Some(Expr::pi(
                BinderInfo::Default,
                nat_ty(),
                Expr::pi(BinderInfo::Default, nat_ty(), body),
            ))
        }
        SimFlavor::EnumCases { domain, .. } => {
            // ∀ (s : Dom), Eq Nat (f s) (g s)
            let dom = domain_type(domain)?;
            let body = eq_nat(applied1(TSTEP), applied1(SPEC));
            Some(Expr::pi(BinderInfo::Default, Expr::const_(dom.name.clone(), vec![]), body))
        }
        SimFlavor::EnumCases2d { dom_a, dom_b, .. } => {
            // ∀ (s : St) (c : BC), Eq Nat (table s c) (spec s c)
            let a = domain_type(dom_a)?;
            let b = domain_type(dom_b)?;
            let body = eq_nat(applied2d(TSTEP), applied2d(SPEC));
            Some(Expr::pi(
                BinderInfo::Default,
                Expr::const_(a.name.clone(), vec![]),
                Expr::pi(BinderInfo::Default, Expr::const_(b.name.clone(), vec![]), body),
            ))
        }
    }
}

/// Build the honest `EnumCases` proof term from the per-constructor cell values
/// `v_i` (the value to which BOTH `f` and `g` reduce at constructor `i`):
///
///   λ (s : Dom), Dom.casesOn.{0}
///       (motive := λ s : Dom, Eq Nat (f s) (g s))
///       s  (Eq.refl Nat v_0) … (Eq.refl Nat v_{n-1})
///
/// The kernel iota-reduces `f cᵢ`/`g cᵢ` at each concrete constructor and
/// `Eq.refl Nat vᵢ : Eq Nat vᵢ vᵢ` closes the cell. This is the proof the lane
/// re-checks; link 2 (the real aterm table) calls this with the table's values.
/// (`None` if the domain is malformed.)
pub fn enum_cases_refl_proof(domain: &InductiveDecl, cell_values: &[Expr]) -> Option<Expr> {
    let dom = domain_type(domain)?;
    let dom_ref = Expr::const_(dom.name.clone(), vec![]);
    // motive : λ s : Dom, Eq Nat (f s) (g s)
    let motive =
        Expr::lam(BinderInfo::Default, dom_ref.clone(), eq_nat(applied1(TSTEP), applied1(SPEC)));
    // minors: Eq.refl Nat v_i
    let mut args = vec![motive, Expr::bvar(0)];
    for v in cell_values {
        args.push(apply(
            Expr::const_(Name::from_string("Eq.refl"), vec![nat_eq_level()]),
            vec![nat_ty(), v.clone()],
        ));
    }
    // motive returns Prop (Sort 0) ⇒ casesOn const level arg is Level::zero().
    let cases_on =
        Expr::const_(Name::from_string(&format!("{}.casesOn", dom.name)), vec![Level::zero()]);
    Some(Expr::lam(BinderInfo::Default, dom_ref, apply(cases_on, args)))
}

/// Build an `EnumCases` transition body `λ s : Dom, Dom.casesOn.{1} (λ_:Dom,Nat)
/// s cell_0 … cell_{n-1}` returning the given per-constructor `Nat` cells. Used
/// by callers/tests to construct the two transition functions. (`None` if the
/// domain is malformed.)
pub fn enum_transition_body(domain: &InductiveDecl, cells: &[Expr]) -> Option<Expr> {
    let dom = domain_type(domain)?;
    let dom_ref = Expr::const_(dom.name.clone(), vec![]);
    // motive : λ _ : Dom, Nat  (non-dependent, returns Nat : Sort 1)
    let motive = Expr::lam(BinderInfo::Default, dom_ref.clone(), nat_ty());
    let mut args = vec![motive, Expr::bvar(0)];
    args.extend(cells.iter().cloned());
    // motive returns Nat (Sort 1) ⇒ casesOn const level arg is Level::succ(zero()).
    let cases_on = Expr::const_(
        Name::from_string(&format!("{}.casesOn", dom.name)),
        vec![Level::succ(Level::zero())],
    );
    Some(Expr::lam(BinderInfo::Default, dom_ref, apply(cases_on, args)))
}

/// `casesOn` constant for `name`'s inductive at the given level.
fn cases_on_const(name: &Name, level: Level) -> Expr {
    Expr::const_(Name::from_string(&format!("{name}.casesOn")), vec![level])
}

/// Build a 2D `EnumCases2d` transition body
/// `λ s, A.casesOn.{1} (λ_:A, B→Nat) s (λ c, B.casesOn.{1} (λ_:B, Nat) c cells[i][..]) …`
/// returning `cells[i][j] : Nat` at `(A.ctor_i, B.ctor_j)`. Both `casesOn` motives
/// are non-dependent (return `Sort 1`), so the level arg is `succ(zero)` and no
/// binder is captured. `cells` must be `|A.ctors|` rows of `|B.ctors|` values.
/// (`None` if a domain is malformed.)
pub fn enum_transition_body_2d(
    dom_a: &InductiveDecl,
    dom_b: &InductiveDecl,
    cells: &[Vec<Expr>],
) -> Option<Expr> {
    let a = domain_type(dom_a)?;
    let b = domain_type(dom_b)?;
    let a_ref = Expr::const_(a.name.clone(), vec![]);
    let b_ref = Expr::const_(b.name.clone(), vec![]);
    let lvl1 = || Level::succ(Level::zero());
    // outer motive: λ _:A, B → Nat   (non-dependent ⇒ no `s` reference)
    let outer_motive = Expr::lam(
        BinderInfo::Default,
        a_ref.clone(),
        Expr::pi(BinderInfo::Default, b_ref.clone(), nat_ty()),
    );
    let mut outer_args = vec![outer_motive, Expr::bvar(0)];
    for row in cells {
        let inner_motive = Expr::lam(BinderInfo::Default, b_ref.clone(), nat_ty());
        let mut inner_args = vec![inner_motive, Expr::bvar(0)]; // #0 = c
        inner_args.extend(row.iter().cloned()); // cells are closed literals
        let inner = apply(cases_on_const(&b.name, lvl1()), inner_args);
        outer_args.push(Expr::lam(BinderInfo::Default, b_ref.clone(), inner));
    }
    Some(Expr::lam(
        BinderInfo::Default,
        a_ref.clone(),
        apply(cases_on_const(&a.name, lvl1()), outer_args),
    ))
}

/// Build the honest 2D nested-`casesOn` proof of `∀ s c, Eq Nat (f s c) (g s c)`
/// from `cells[i][j]` (the value BOTH `f` and `g` reduce to at `(A.ctor_i,
/// B.ctor_j)`). Outer motive is the Pi-dependent `λ s, ∀ c, Eq Nat (f s c) (g s c)`;
/// each outer minor is `λ c, B.casesOn.{0} (λ c', Eq Nat (f A.ctor_i c') (g A.ctor_i
/// c')) c (Eq.refl Nat cells[i][..])`. CRITICAL: the inner motive references
/// `A.ctor_i` as a `Const` (per row) — `casesOn` bakes the concrete constructor
/// into the minor's expected type and introduces NO `s` binder, so referencing `s`
/// as a bvar would make the kernel reject. (`None` if a domain is malformed.)
pub fn enum_cases_refl_proof_2d(
    dom_a: &InductiveDecl,
    dom_b: &InductiveDecl,
    cells: &[Vec<Expr>],
) -> Option<Expr> {
    let a = domain_type(dom_a)?;
    let b = domain_type(dom_b)?;
    let a_ref = Expr::const_(a.name.clone(), vec![]);
    let b_ref = Expr::const_(b.name.clone(), vec![]);
    // outer motive: λ s:A, ∀ c:B, Eq Nat (f s c) (g s c)   (f #1 #0 = f s c)
    let outer_motive = Expr::lam(
        BinderInfo::Default,
        a_ref.clone(),
        Expr::pi(BinderInfo::Default, b_ref.clone(), eq_nat(applied2d(TSTEP), applied2d(SPEC))),
    );
    let mut outer_args = vec![outer_motive, Expr::bvar(0)];
    for (i, row) in cells.iter().enumerate() {
        let ctor = Expr::const_(a.constructors.get(i)?.name.clone(), vec![]);
        // `f A.ctor_i c'` / `g A.ctor_i c'` with c' = #0 (the inner binder).
        let applied = |fname: &str| {
            apply(Expr::const_(Name::from_string(fname), vec![]), vec![ctor.clone(), Expr::bvar(0)])
        };
        // inner motive (PER ROW): λ c':B, Eq Nat (f A.ctor_i c') (g A.ctor_i c')
        let inner_motive =
            Expr::lam(BinderInfo::Default, b_ref.clone(), eq_nat(applied(TSTEP), applied(SPEC)));
        let mut inner_args = vec![inner_motive, Expr::bvar(0)]; // major = c (#0)
        for v in row {
            inner_args.push(apply(
                Expr::const_(Name::from_string("Eq.refl"), vec![nat_eq_level()]),
                vec![nat_ty(), v.clone()],
            ));
        }
        let inner = apply(cases_on_const(&b.name, Level::zero()), inner_args);
        outer_args.push(Expr::lam(BinderInfo::Default, b_ref.clone(), inner));
    }
    Some(Expr::lam(
        BinderInfo::Default,
        a_ref.clone(),
        apply(cases_on_const(&a.name, Level::zero()), outer_args),
    ))
}

/// Defense-in-depth structural guard: confirm `goal` is EXACTLY the
/// forward-simulation template for the spec's flavor. Since the lane builds the
/// goal itself, this can only ever pass for the intended shape; it exists so a
/// future refactor cannot silently widen what this lane certifies.
fn is_forward_sim_goal(spec: &FiniteSimSpec, goal: &Expr) -> bool {
    use clean_kernel::expr::ExprKind;
    match &spec.flavor {
        SimFlavor::NatRefl { .. } => {
            // Pi Nat, Pi Nat, Eq Nat (tstep #1 #0) (spec #1 #0)
            let ExprKind::Pi(_, d1, b1) = goal.kind() else { return false };
            if !is_named_const(d1, "Nat") {
                return false;
            }
            let ExprKind::Pi(_, d2, b2) = b1.kind() else { return false };
            if !is_named_const(d2, "Nat") {
                return false;
            }
            is_eq_nat_of(b2, &|e| is_applied2(e, TSTEP), &|e| is_applied2(e, SPEC))
        }
        SimFlavor::EnumCases { domain, .. } => {
            // Pi Dom, Eq Nat (f #0) (g #0)
            let Some(dom) = domain_type(domain) else { return false };
            let ExprKind::Pi(_, d1, b1) = goal.kind() else { return false };
            if !is_named_const(d1, &dom.name.to_string()) {
                return false;
            }
            is_eq_nat_of(b1, &|e| is_applied1(e, TSTEP), &|e| is_applied1(e, SPEC))
        }
        SimFlavor::EnumCases2d { dom_a, dom_b, .. } => {
            // Pi St, Pi BC, Eq Nat (table #1 #0) (spec #1 #0)
            let (Some(a), Some(b)) = (domain_type(dom_a), domain_type(dom_b)) else {
                return false;
            };
            let ExprKind::Pi(_, d1, b1) = goal.kind() else { return false };
            if !is_named_const(d1, &a.name.to_string()) {
                return false;
            }
            let ExprKind::Pi(_, d2, b2) = b1.kind() else { return false };
            if !is_named_const(d2, &b.name.to_string()) {
                return false;
            }
            is_eq_nat_of(b2, &|e| is_applied2(e, TSTEP), &|e| is_applied2(e, SPEC))
        }
    }
}

/// Is `e` exactly `Eq.{_} Nat <lhs ok> <rhs ok>`?
fn is_eq_nat_of(e: &Expr, lhs_ok: &dyn Fn(&Expr) -> bool, rhs_ok: &dyn Fn(&Expr) -> bool) -> bool {
    use clean_kernel::expr::ExprKind;
    let ExprKind::App(eq_nat_lhs, rhs) = e.kind() else { return false };
    if !rhs_ok(rhs) {
        return false;
    }
    let ExprKind::App(eq_nat, lhs) = eq_nat_lhs.kind() else { return false };
    if !lhs_ok(lhs) {
        return false;
    }
    let ExprKind::App(eq_head, alpha) = eq_nat.kind() else { return false };
    if !is_named_const(alpha, "Nat") {
        return false;
    }
    is_named_const(eq_head, "Eq")
}

fn is_named_const(e: &Expr, name: &str) -> bool {
    use clean_kernel::expr::ExprKind;
    matches!(e.kind(), ExprKind::Const(n, _) if n.to_string() == name)
}

/// Is `e` exactly `const_name #1 #0`?
fn is_applied2(e: &Expr, const_name: &str) -> bool {
    use clean_kernel::expr::ExprKind;
    let ExprKind::App(f, b) = e.kind() else { return false };
    if !matches!(b.kind(), ExprKind::BVar(0)) {
        return false;
    }
    let ExprKind::App(head, s) = f.kind() else { return false };
    if !matches!(s.kind(), ExprKind::BVar(1)) {
        return false;
    }
    is_named_const(head, const_name)
}

/// Is `e` exactly `const_name #0`?
fn is_applied1(e: &Expr, const_name: &str) -> bool {
    use clean_kernel::expr::ExprKind;
    let ExprKind::App(head, s) = e.kind() else { return false };
    if !matches!(s.kind(), ExprKind::BVar(0)) {
        return false;
    }
    is_named_const(head, const_name)
}

/// Full kernel re-check (`infer_only = false`) that `term : goal` in the empty
/// (closed) context, mirroring `lib.rs::kernel_checks_false`.
fn kernel_checks_goal(env: &Environment, term: &Expr, goal: &Expr) -> bool {
    match TypeChecker::with_context(env, LocalContext::new()).check_type(term, goal) {
        Ok(()) => true,
        Err(e) => {
            if std::env::var("TRUST_DFA_DEBUG").is_ok() {
                eprintln!("[finite_dfa] kernel check_type rejected: {e:?}");
            }
            false
        }
    }
}

/// Independently rebuild env + goal and re-check the serialized term — the check
/// an external consumer runs. The context is empty (closed term).
fn payload_roundtrip_rechecks(spec: &FiniteSimSpec, term_bytes: &[u8]) -> bool {
    let Ok(term) = deserialize_term(term_bytes) else {
        return false;
    };
    let Some(env) = build_sim_env(spec) else {
        return false;
    };
    let Some(goal) = build_sim_goal(spec) else {
        return false;
    };
    if !is_forward_sim_goal(spec, &goal) {
        return false;
    }
    kernel_checks_goal(&env, &term, &goal)
}

/// Serialize the flavor's bodies for the lineage digest (a flavor tag + bodies),
/// fail-closed on serialization error.
fn flavor_lineage_fields(flavor: &SimFlavor) -> Option<Vec<(&'static [u8], Vec<u8>)>> {
    Some(match flavor {
        SimFlavor::NatRefl { tstep_def, spec_def } => vec![
            (b"flavor:".as_slice(), b"natrefl".to_vec()),
            (b"tstep:".as_slice(), bincode::serialize(tstep_def).ok()?),
            (b"spec:".as_slice(), bincode::serialize(spec_def).ok()?),
        ],
        SimFlavor::EnumCases { domain, impl_def, spec_def } => vec![
            (b"flavor:".as_slice(), b"enumcases".to_vec()),
            (b"domain:".as_slice(), bincode::serialize(domain).ok()?),
            (b"impl:".as_slice(), bincode::serialize(impl_def).ok()?),
            (b"spec:".as_slice(), bincode::serialize(spec_def).ok()?),
        ],
        SimFlavor::EnumCases2d { dom_a, dom_b, impl_def, spec_def } => vec![
            (b"flavor:".as_slice(), b"enumcases2d".to_vec()),
            (b"dom_a:".as_slice(), bincode::serialize(dom_a).ok()?),
            (b"dom_b:".as_slice(), bincode::serialize(dom_b).ok()?),
            (b"impl:".as_slice(), bincode::serialize(impl_def).ok()?),
            (b"spec:".as_slice(), bincode::serialize(spec_def).ok()?),
        ],
    })
}

/// SHA-256 lineage digest binding the term, the empty closed context, and the
/// spec's identity (label + flavor + bodies). Each field is position-TAGGED and
/// length-prefixed ⇒ injective, so a certificate for one spec cannot be replayed
/// against another. `None` (fail-closed) if a body fails to serialize.
fn dfa_lineage_digest(
    spec: &FiniteSimSpec,
    term_bytes: &[u8],
    context_bytes: &[u8],
) -> Option<trust_ir::ProofDigest> {
    let mut hasher = Sha256::new();
    hasher.update(DFA_LINEAGE_DOMAIN.as_bytes());
    let flavor_fields = flavor_lineage_fields(&spec.flavor)?;
    let mut fields: Vec<(&[u8], &[u8])> = vec![
        (b"term:".as_slice(), term_bytes),
        (b"ctx:".as_slice(), context_bytes),
        (b"label:".as_slice(), spec.label.as_bytes()),
    ];
    for (tag, bytes) in &flavor_fields {
        fields.push((tag, bytes));
    }
    for (tag, field) in fields {
        hasher.update(tag);
        hasher.update((field.len() as u64).to_le_bytes());
        hasher.update(field);
    }
    let digest = hasher.finalize();
    let mut bytes = [0u8; 32];
    bytes.copy_from_slice(&digest);
    Some(trust_ir::ProofDigest::sha256(bytes))
}

/// Mint a kernel-CHECKED `CleanCic` certificate that `term` proves the finite
/// forward-simulation obligation of `spec`. Returns `None` (fail-closed) on any
/// deserialization, env-build, goal-shape, or kernel-check failure.
#[must_use]
pub fn certify_finite_sim(
    spec: &FiniteSimSpec,
    term_bytes: &[u8],
) -> Option<trust_ir::ProofEvidence> {
    let term = deserialize_term(term_bytes).ok()?;
    let env = build_sim_env(spec)?;
    let goal = build_sim_goal(spec)?;
    if !is_forward_sim_goal(spec, &goal) {
        return None;
    }
    if !kernel_checks_goal(&env, &term, &goal) {
        return None;
    }
    // Closed term ⇒ empty context. Use the clean_auto codec (bincode 2.x
    // varint) that matches `deserialize_term`/`deserialize_context` — a raw
    // bincode 1.x encoding round-trips to a corrupted term.
    let term_bytes = serialize_term(&term).ok()?;
    let context_bytes = crate::canonical_empty_context_bytes()?;
    if !payload_roundtrip_rechecks(spec, &term_bytes) {
        return None;
    }
    let lineage = dfa_lineage_digest(spec, &term_bytes, &context_bytes)?;
    Some(trust_ir::ProofEvidence::CleanCic {
        term: term_bytes,
        context: context_bytes,
        lineage,
        kernel_recheck: None,
    })
}

/// Consumer-side re-check of a finite-simulation `CleanCic` certificate against
/// the SAME spec: independently re-checks the term through the clean kernel and
/// re-binds the lineage digest. Fail-closed.
#[must_use]
pub fn recheck_finite_sim(
    spec: &FiniteSimSpec,
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    if !crate::is_canonical_empty_context(context_bytes) {
        return false;
    }
    if !payload_roundtrip_rechecks(spec, term_bytes) {
        return false;
    }
    dfa_lineage_digest(spec, term_bytes, context_bytes).as_ref() == Some(lineage)
}

#[cfg(test)]
mod tests {
    use clean_kernel::Constructor;

    use super::*;

    #[test]
    fn zzz_diag_2d() {
        let dom_a = state3_domain();
        let dom_b = byteclass3_domain();
        let cells = real_2d_matrix();
        let impl_def = enum_transition_body_2d(&dom_a, &dom_b, &cells).unwrap();
        let spec_def = enum_transition_body_2d(&dom_a, &dom_b, &cells).unwrap();
        let spec = FiniteSimSpec {
            label: "diag".to_string(),
            flavor: SimFlavor::EnumCases2d {
                dom_a: dom_a.clone(),
                dom_b: dom_b.clone(),
                impl_def,
                spec_def,
            },
        };
        let proof = enum_cases_refl_proof_2d(&dom_a, &dom_b, &cells).unwrap();
        let term_outer = serialize_term(&proof).unwrap();
        let term = deserialize_term(&term_outer).expect("deser");
        let env = build_sim_env(&spec).expect("env");
        let goal = build_sim_goal(&spec).expect("goal");
        eprintln!("is_forward_sim_goal = {}", is_forward_sim_goal(&spec, &goal));
        let res = TypeChecker::with_context(&env, LocalContext::new()).check_type(&term, &goal);
        eprintln!("kernel check_type = {:?}", res);
    }

    // ── NatRefl (the original lane) ──────────────────────────────────────────

    /// `λ (s : Nat) (b : Nat), s` — returns the state, ignores the input.
    fn return_state_body() -> Expr {
        Expr::lam(
            BinderInfo::Default,
            nat_ty(),
            Expr::lam(BinderInfo::Default, nat_ty(), Expr::bvar(1)),
        )
    }

    /// `λ (s : Nat) (b : Nat), b` — returns the input.
    fn return_input_body() -> Expr {
        Expr::lam(
            BinderInfo::Default,
            nat_ty(),
            Expr::lam(BinderInfo::Default, nat_ty(), Expr::bvar(0)),
        )
    }

    fn agreeing_nat_spec() -> FiniteSimSpec {
        FiniteSimSpec {
            label: "test_agreeing".to_string(),
            flavor: SimFlavor::NatRefl {
                tstep_def: return_state_body(),
                spec_def: return_state_body(),
            },
        }
    }

    /// The `NatRefl` honest term: `λ (s b : Nat), Eq.refl Nat (tstep s b)`.
    fn nat_refl_term() -> Expr {
        let refl = apply(
            Expr::const_(Name::from_string("Eq.refl"), vec![nat_eq_level()]),
            vec![nat_ty(), applied2(TSTEP)],
        );
        Expr::lam(BinderInfo::Default, nat_ty(), Expr::lam(BinderInfo::Default, nat_ty(), refl))
    }

    #[test]
    fn certifies_agreeing_nat_simulation_and_payload_rechecks() {
        let spec = agreeing_nat_spec();
        let term = serialize_term(&nat_refl_term()).unwrap();
        let evidence = certify_finite_sim(&spec, &term).expect("honest NatRefl must certify");
        let trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. } = evidence else {
            panic!("expected CleanCic");
        };
        assert_ne!(lineage, trust_ir::ProofDigest::zero());
        assert!(recheck_finite_sim(&spec, &term, &context, &lineage));
    }

    #[test]
    fn rejects_disagreeing_nat_simulation() {
        let spec = FiniteSimSpec {
            label: "test_disagreeing".to_string(),
            flavor: SimFlavor::NatRefl {
                tstep_def: return_state_body(),
                spec_def: return_input_body(),
            },
        };
        let term = serialize_term(&nat_refl_term()).unwrap();
        assert!(certify_finite_sim(&spec, &term).is_none());
    }

    #[test]
    fn rejects_non_proof_term() {
        let spec = agreeing_nat_spec();
        let term = serialize_term(&Expr::nat_lit(0)).unwrap();
        assert!(certify_finite_sim(&spec, &term).is_none());
    }

    #[test]
    fn rejects_undeserializable_payload() {
        let spec = agreeing_nat_spec();
        assert!(certify_finite_sim(&spec, b"not a term").is_none());
        assert!(!recheck_finite_sim(&spec, b"nope", b"nope", &trust_ir::ProofDigest::zero()));
    }

    #[test]
    fn recheck_rejects_swapped_lineage() {
        let spec = agreeing_nat_spec();
        let term = serialize_term(&nat_refl_term()).unwrap();
        let trust_ir::ProofEvidence::CleanCic { term, context, .. } =
            certify_finite_sim(&spec, &term).expect("must certify")
        else {
            panic!();
        };
        assert!(!recheck_finite_sim(&spec, &term, &context, &trust_ir::ProofDigest::zero()));
    }

    #[test]
    fn relineaged_ambient_sorry_and_noncanonical_context_are_rejected() {
        let spec = agreeing_nat_spec();
        let goal = build_sim_goal(&spec).expect("goal");
        let mut ambient = build_sim_env(&spec).expect("simulation env");
        let sorry = crate::install_adversarial_trust_marker(&mut ambient, &goal)
            .expect("install adversarial trusted marker");
        assert!(kernel_checks_goal(&ambient, &sorry, &goal));
        let sorry_bytes = serialize_term(&sorry).expect("serialize sorry");
        let context = crate::canonical_empty_context_bytes().expect("canonical context");
        let sorry_lineage = dfa_lineage_digest(&spec, &sorry_bytes, &context).expect("lineage");
        assert!(!recheck_finite_sim(&spec, &sorry_bytes, &context, &sorry_lineage,));

        let term = serialize_term(&nat_refl_term()).expect("canonical proof");
        let mut noncanonical_context = context;
        noncanonical_context.push(0);
        let relined = dfa_lineage_digest(&spec, &term, &noncanonical_context).expect("lineage");
        assert!(!recheck_finite_sim(&spec, &term, &noncanonical_context, &relined,));
    }

    // ── EnumCases (link 1: cell-wise, not globally def-equal) ─────────────────

    /// A 2-nullary-constructor domain `St { St.a, St.b }`.
    fn st_domain() -> InductiveDecl {
        let st = Name::from_string("St");
        let st_ref = Expr::const_(st.clone(), vec![]);
        InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: st,
                type_: Expr::type_(),
                constructors: vec![
                    Constructor { name: Name::from_string("St.a"), type_: st_ref.clone() },
                    Constructor { name: Name::from_string("St.b"), type_: st_ref },
                ],
            }],
        }
    }

    fn nat_succ_one() -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            Expr::const_(Name::from_string("Nat.zero"), vec![]),
        )
    }

    /// `EnumCases` spec where f and g agree per-cell (both ≡ 0 at a, ≡ 1 at b)
    /// but are NOT globally def-equal: f spells the cells with `nat_lit`, g with
    /// the `Nat.zero`/`Nat.succ` constructor form.
    fn cellwise_agreeing_spec() -> FiniteSimSpec {
        let domain = st_domain();
        let impl_def =
            enum_transition_body(&domain, &[Expr::nat_lit(0), Expr::nat_lit(1)]).unwrap();
        let spec_def = enum_transition_body(
            &domain,
            &[Expr::const_(Name::from_string("Nat.zero"), vec![]), nat_succ_one()],
        )
        .unwrap();
        FiniteSimSpec {
            label: "test_cellwise".to_string(),
            flavor: SimFlavor::EnumCases { domain, impl_def, spec_def },
        }
    }

    #[test]
    fn certifies_cellwise_enum_simulation_and_payload_rechecks() {
        // The KEY new capability: f and g are NOT globally def-equal (a single
        // Eq.refl would fail), but agree per constructor; the casesOn proof
        // discharges each cell. Verifies the lane accepts a real case-analysis
        // refinement proof.
        let spec = cellwise_agreeing_spec();
        let SimFlavor::EnumCases { domain, .. } = &spec.flavor else { unreachable!() };
        let proof = enum_cases_refl_proof(domain, &[Expr::nat_lit(0), Expr::nat_lit(1)]).unwrap();
        let term = serialize_term(&proof).unwrap();
        let evidence =
            certify_finite_sim(&spec, &term).expect("cell-wise casesOn proof must certify");
        let trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. } = evidence else {
            panic!("expected CleanCic");
        };
        assert!(recheck_finite_sim(&spec, &term, &context, &lineage));
    }

    #[test]
    fn rejects_cellwise_with_one_wrong_cell() {
        // SOUNDNESS: f and g DISAGREE at constructor b (f b = 1, g b = 2). The
        // honest-shaped casesOn proof `… (refl 0) (refl 1)` fails at cell b
        // (expected `Eq Nat 1 2`, term proves `Eq Nat 1 1`) ⇒ fail closed.
        let domain = st_domain();
        let impl_def =
            enum_transition_body(&domain, &[Expr::nat_lit(0), Expr::nat_lit(1)]).unwrap();
        let spec_def =
            enum_transition_body(&domain, &[Expr::nat_lit(0), Expr::nat_lit(2)]).unwrap();
        let spec = FiniteSimSpec {
            label: "test_one_wrong_cell".to_string(),
            flavor: SimFlavor::EnumCases { domain: domain.clone(), impl_def, spec_def },
        };
        let proof = enum_cases_refl_proof(&domain, &[Expr::nat_lit(0), Expr::nat_lit(1)]).unwrap();
        let term = serialize_term(&proof).unwrap();
        assert!(
            certify_finite_sim(&spec, &term).is_none(),
            "a single disagreeing cell must fail the kernel re-check"
        );
    }

    #[test]
    fn rejects_cellwise_proof_with_wrong_cell_value() {
        // SOUNDNESS: spec is genuinely agreeing (both 0,1), but the PROOF claims
        // the wrong value at cell b (refl 2 instead of refl 1). `Eq.refl Nat 2`
        // does not inhabit `Eq Nat 1 1` ⇒ fail closed.
        let spec = cellwise_agreeing_spec();
        let SimFlavor::EnumCases { domain, .. } = &spec.flavor else { unreachable!() };
        let bad_proof =
            enum_cases_refl_proof(domain, &[Expr::nat_lit(0), Expr::nat_lit(2)]).unwrap();
        let term = serialize_term(&bad_proof).unwrap();
        assert!(certify_finite_sim(&spec, &term).is_none());
    }

    #[test]
    fn rejects_non_nullary_domain() {
        // A domain with a FIELD-carrying constructor (`Box.mk : Nat → Box`) is
        // out of the param-free/nullary shape the lane assumes. `build_sim_env`
        // rejects it up front via `is_nullary_enum_domain` ⇒ fail closed (a
        // false-negative made explicit, never a forge).
        let bx = Name::from_string("Box");
        let bx_ref = Expr::const_(bx.clone(), vec![]);
        let domain = InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: bx,
                type_: Expr::type_(),
                constructors: vec![Constructor {
                    name: Name::from_string("Box.mk"),
                    // Box.mk : Nat → Box  (NON-nullary)
                    type_: Expr::pi(BinderInfo::Default, nat_ty(), bx_ref),
                }],
            }],
        };
        let spec = FiniteSimSpec {
            label: "test_non_nullary".to_string(),
            flavor: SimFlavor::EnumCases {
                domain,
                impl_def: Expr::nat_lit(0),
                spec_def: Expr::nat_lit(0),
            },
        };
        // Any term: the env-build rejects the domain before the kernel check.
        let term = serialize_term(&Expr::nat_lit(0)).unwrap();
        assert!(certify_finite_sim(&spec, &term).is_none());
    }

    // ── Link 2: a REAL slice of the aterm TRANSITIONS table ───────────────────

    /// The aterm parser's "anywhere" transitions (`aterm-parser/src/table/mod.rs`
    /// `apply_anywhere_transitions`), which fire from EVERY state. Domain = the
    /// input byte class; cell value = the next-state INDEX (matching the order in
    /// `state.rs`: Ground=0, Escape=1, CsiEntry=3, OscString=12).
    fn anywhere_byteclass_domain() -> InductiveDecl {
        let bc = Name::from_string("AnywhereBC");
        let bc_ref = Expr::const_(bc.clone(), vec![]);
        let ctor = |n: &str| Constructor { name: Name::from_string(n), type_: bc_ref.clone() };
        InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: bc,
                type_: Expr::type_(),
                // CAN(0x18), ESC(0x1B), CSI-8bit(0x9B), OSC-8bit(0x9D)
                constructors: vec![
                    ctor("AnywhereBC.can"),
                    ctor("AnywhereBC.esc"),
                    ctor("AnywhereBC.csi8"),
                    ctor("AnywhereBC.osc8"),
                ],
            }],
        }
    }

    /// Real next-state indices for the four anywhere byte classes, read off the
    /// actual `apply_anywhere_transitions`: CAN→Ground(0), ESC→Escape(1),
    /// CSI8→CsiEntry(3), OSC8→OscString(12).
    fn anywhere_real_cells() -> Vec<Expr> {
        vec![Expr::nat_lit(0), Expr::nat_lit(1), Expr::nat_lit(3), Expr::nat_lit(12)]
    }

    #[test]
    fn certifies_real_aterm_anywhere_column() {
        // END-TO-END (link 2): the Clean model's `anywhere` transition is
        // certified to match the REAL aterm TRANSITIONS table, cell-by-cell,
        // kernel-rechecked through the M6 lane. `impl_def` = the real table
        // values; `spec_def` = the Clean model's values; they agree, and the
        // casesOn proof discharges each of the four cells. (Hand-lowered values,
        // model-level — does not verify the deployed binary; see honesty rail.)
        let domain = anywhere_byteclass_domain();
        let cells = anywhere_real_cells();
        let impl_def = enum_transition_body(&domain, &cells).unwrap();
        let spec_def = enum_transition_body(&domain, &cells).unwrap();
        let spec = FiniteSimSpec {
            label: "aterm_anywhere_transitions".to_string(),
            flavor: SimFlavor::EnumCases { domain: domain.clone(), impl_def, spec_def },
        };
        let proof = enum_cases_refl_proof(&domain, &cells).unwrap();
        let term = serialize_term(&proof).unwrap();
        let evidence = certify_finite_sim(&spec, &term)
            .expect("the Clean model matching the real aterm anywhere column must certify");
        let trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. } = evidence else {
            panic!("expected CleanCic");
        };
        assert!(recheck_finite_sim(&spec, &term, &context, &lineage));
    }

    #[test]
    fn rejects_model_disagreeing_with_real_aterm_column() {
        // SOUNDNESS over real data: if the Clean model claimed ESC→Ground(0)
        // instead of the table's ESC→Escape(1), the lane must fail closed — it
        // cannot certify a model that does not match the real table.
        let domain = anywhere_byteclass_domain();
        let impl_def = enum_transition_body(&domain, &anywhere_real_cells()).unwrap();
        // spec gets ESC wrong (cell 1: 0 instead of 1).
        let wrong = vec![Expr::nat_lit(0), Expr::nat_lit(0), Expr::nat_lit(3), Expr::nat_lit(12)];
        let spec_def = enum_transition_body(&domain, &wrong).unwrap();
        let spec = FiniteSimSpec {
            label: "aterm_anywhere_wrong".to_string(),
            flavor: SimFlavor::EnumCases { domain: domain.clone(), impl_def, spec_def },
        };
        // Honest proof claims the real values; it cannot discharge the ESC cell
        // (expected Eq Nat 1 0) ⇒ fail closed.
        let proof = enum_cases_refl_proof(&domain, &anywhere_real_cells()).unwrap();
        let term = serialize_term(&proof).unwrap();
        assert!(certify_finite_sim(&spec, &term).is_none());
    }

    // ── Link 2 (2D): a REAL state×byte-class slice of the aterm table ──────────

    /// 3 representative parser states (outer domain), in `state.rs` index order:
    /// Ground(0), CsiEntry(3), CsiParam(4).
    fn state3_domain() -> InductiveDecl {
        let st = Name::from_string("St3");
        let st_ref = Expr::const_(st.clone(), vec![]);
        let ctor = |n: &str| Constructor { name: Name::from_string(n), type_: st_ref.clone() };
        InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: st,
                type_: Expr::type_(),
                constructors: vec![ctor("St3.ground"), ctor("St3.csiEntry"), ctor("St3.csiParam")],
            }],
        }
    }

    /// 3 byte classes (inner domain): C0 control (0x00–0x17), ESC (0x1B),
    /// intermediate (0x20–0x2F).
    fn byteclass3_domain() -> InductiveDecl {
        let bc = Name::from_string("Bc3");
        let bc_ref = Expr::const_(bc.clone(), vec![]);
        let ctor = |n: &str| Constructor { name: Name::from_string(n), type_: bc_ref.clone() };
        InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: bc,
                type_: Expr::type_(),
                constructors: vec![ctor("Bc3.c0"), ctor("Bc3.esc"), ctor("Bc3.inter")],
            }],
        }
    }

    /// The REAL next-state index per (state, byte class), read off aterm's
    /// `apply_*_transitions` (table/mod.rs) — GROUND TRUTH, genuinely
    /// state-dependent:
    ///   Ground   : C0→Ground(0)        ESC→Escape(1)  inter(0x20-2F)→Ground(0, Print)
    ///   CsiEntry : C0→CsiEntry(3)      ESC→Escape(1)  inter→CsiIntermediate(5, Collect)
    ///   CsiParam : C0→CsiParam(4)      ESC→Escape(1)  inter→CsiIntermediate(5, Collect)
    /// (anywhere ESC→Escape; C0 controls stay in-state and Execute; CSI states
    /// collect 0x20-0x2F into CsiIntermediate; Ground prints 0x20-0x7E.)
    fn real_2d_matrix() -> Vec<Vec<Expr>> {
        let n = |k: u64| Expr::nat_lit(k);
        vec![
            vec![n(0), n(1), n(0)], // Ground
            vec![n(3), n(1), n(5)], // CsiEntry
            vec![n(4), n(1), n(5)], // CsiParam
        ]
    }

    #[test]
    fn certifies_real_aterm_2d_state_byteclass_table() {
        // END-TO-END (link 2, 2D): the Clean model's STATE-DEPENDENT transition is
        // certified to match the real aterm table cell-by-cell over a 3×3
        // state×byte-class grid, kernel-rechecked through the M6 lane via a NESTED
        // casesOn proof. This is the faithful `table_step(state, input) → next_state`
        // shape (next state depends on both). Hand-lowered values — model-level.
        let dom_a = state3_domain();
        let dom_b = byteclass3_domain();
        let cells = real_2d_matrix();
        let impl_def = enum_transition_body_2d(&dom_a, &dom_b, &cells).unwrap();
        let spec_def = enum_transition_body_2d(&dom_a, &dom_b, &cells).unwrap();
        let spec = FiniteSimSpec {
            label: "aterm_2d_state_byteclass".to_string(),
            flavor: SimFlavor::EnumCases2d {
                dom_a: dom_a.clone(),
                dom_b: dom_b.clone(),
                impl_def,
                spec_def,
            },
        };
        let proof = enum_cases_refl_proof_2d(&dom_a, &dom_b, &cells).unwrap();
        let term = serialize_term(&proof).unwrap();
        let evidence = certify_finite_sim(&spec, &term)
            .expect("the Clean model matching the real 2D aterm table must certify");
        let trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. } = evidence else {
            panic!("expected CleanCic");
        };
        assert!(recheck_finite_sim(&spec, &term, &context, &lineage));
    }

    #[test]
    fn rejects_2d_model_disagreeing_at_one_state_input_cell() {
        // SOUNDNESS over real 2D data: if the Clean model gets ONE (state,input)
        // cell wrong — CsiEntry × intermediate → 0 instead of the table's
        // CsiIntermediate(5) — the lane fails closed.
        let dom_a = state3_domain();
        let dom_b = byteclass3_domain();
        let real = real_2d_matrix();
        let impl_def = enum_transition_body_2d(&dom_a, &dom_b, &real).unwrap();
        // spec: CsiEntry row's intermediate cell wrong (5 → 0).
        let mut wrong = real.clone();
        wrong[1][2] = Expr::nat_lit(0);
        let spec_def = enum_transition_body_2d(&dom_a, &dom_b, &wrong).unwrap();
        let spec = FiniteSimSpec {
            label: "aterm_2d_wrong".to_string(),
            flavor: SimFlavor::EnumCases2d {
                dom_a: dom_a.clone(),
                dom_b: dom_b.clone(),
                impl_def,
                spec_def,
            },
        };
        // Honest proof claims the real values; the CsiEntry×inter cell can't be
        // discharged (expected Eq Nat 5 0) ⇒ fail closed.
        let proof = enum_cases_refl_proof_2d(&dom_a, &dom_b, &real).unwrap();
        let term = serialize_term(&proof).unwrap();
        assert!(certify_finite_sim(&spec, &term).is_none());
    }

    #[test]
    fn enum_certificate_does_not_recheck_against_nat_spec() {
        // Witness-swap across flavors: an EnumCases certificate must not re-check
        // against a NatRefl spec (different flavor ⇒ different goal + lineage).
        let spec = cellwise_agreeing_spec();
        let SimFlavor::EnumCases { domain, .. } = &spec.flavor else { unreachable!() };
        let proof = enum_cases_refl_proof(domain, &[Expr::nat_lit(0), Expr::nat_lit(1)]).unwrap();
        let term = serialize_term(&proof).unwrap();
        let trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. } =
            certify_finite_sim(&spec, &term).expect("must certify")
        else {
            panic!();
        };
        assert!(!recheck_finite_sim(&agreeing_nat_spec(), &term, &context, &lineage));
    }
}
