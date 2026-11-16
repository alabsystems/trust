//! Constructive Boolean proofs for the original fixed-width scalar bits.
//!
//! The original Formula renderer remains the goal. This helper expands only
//! finite scalar spines, proves local Boolean identities by Bool.rec, and
//! transports every bit equality through List.cons. No solver, fresh semantic
//! variable, premise, or narrower goal participates.
use super::*;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum Bit {
    Lit(bool),
    Sym(String),
    Not(Box<Bit>),
    And(Box<Bit>, Box<Bit>),
    Or(Box<Bit>, Box<Bit>),
    Xor(Box<Bit>, Box<Bit>),
    Ite(Box<Bit>, Box<Bit>, Box<Bit>),
}
use Bit::*;
fn boxed(bit: Bit) -> Box<Bit> {
    Box::new(bit)
}
fn bool_ite(p: Expr, t: Expr, e: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]),
        [lam(kx::bool_ty(), kx::bool_ty()), e, t, p],
    )
}
pub(super) fn expr(bit: &Bit) -> Expr {
    replace(bit, &BTreeMap::new())
}
fn replace(bit: &Bit, atoms: &BTreeMap<Bit, Expr>) -> Expr {
    if let Some(value) = atoms.get(bit) {
        return value.clone();
    }
    match bit {
        Lit(value) => Expr::const_str(if *value { "Bool.true" } else { "Bool.false" }),
        Sym(name) => Expr::const_str(name),
        Not(a) => kx::bnot(replace(a, atoms)),
        And(a, b) => kx::band(replace(a, atoms), replace(b, atoms)),
        Or(a, b) => Expr::apps(Expr::const_str("Bool.or"), [replace(a, atoms), replace(b, atoms)]),
        Xor(a, b) => kx::bxor(replace(a, atoms), replace(b, atoms)),
        Ite(p, t, e) => bool_ite(replace(p, atoms), replace(t, atoms), replace(e, atoms)),
    }
}
pub(super) fn list(bits: &[Bit]) -> Expr {
    bits.iter().rev().fold(kx::nil(), |tail, head| kx::cons(expr(head), tail))
}
fn arguments(bit: &Bit) -> Vec<Bit> {
    match bit {
        Not(a) => vec![(**a).clone()],
        And(a, b) | Or(a, b) | Xor(a, b) => vec![(**a).clone(), (**b).clone()],
        Ite(p, t, e) => vec![(**p).clone(), (**t).clone(), (**e).clone()],
        _ => vec![],
    }
}
fn with_arguments(bit: &Bit, a: &[Bit]) -> Bit {
    match bit {
        Not(_) => Not(boxed(a[0].clone())),
        And(..) => And(boxed(a[0].clone()), boxed(a[1].clone())),
        Or(..) => Or(boxed(a[0].clone()), boxed(a[1].clone())),
        Xor(..) => Xor(boxed(a[0].clone()), boxed(a[1].clone())),
        Ite(..) => Ite(boxed(a[0].clone()), boxed(a[1].clone()), boxed(a[2].clone())),
        _ => bit.clone(),
    }
}

// A local identity has at most three arbitrary Boolean operands. Checking all
// branches constructs its actual dependent eliminator proof; it is not a test
// oracle. A wrong identity leaves a branch ill-typed at the final kernel check.
fn local_identity(left: &Bit, right: &Bit, atoms: &[Bit]) -> Expr {
    let atoms: Vec<_> = atoms.iter().cloned().collect::<BTreeSet<_>>().into_iter().collect();
    assert!(atoms.len() <= 3);
    fn cases(
        left: &Bit,
        right: &Bit,
        atoms: &[Bit],
        index: usize,
        values: &BTreeMap<Bit, Expr>,
    ) -> Expr {
        if index == atoms.len() {
            return refl(kx::bool_ty(), replace(left, values));
        }
        let mut motive_values = values.clone();
        motive_values.insert(atoms[index].clone(), Expr::bvar(0));
        let motive = lam(
            kx::bool_ty(),
            equality(kx::bool_ty(), replace(left, &motive_values), replace(right, &motive_values)),
        );
        let mut low = values.clone();
        low.insert(atoms[index].clone(), expr(&Lit(false)));
        let mut high = values.clone();
        high.insert(atoms[index].clone(), expr(&Lit(true)));
        Expr::apps(
            Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
            [
                motive,
                cases(left, right, atoms, index + 1, &low),
                cases(left, right, atoms, index + 1, &high),
                expr(&atoms[index]),
            ],
        )
    }
    // Initialize every operand as a separate lemma parameter before
    // eliminating any one of them. Related actual expressions (x, !x) must
    // not be rewritten inside a later operand's motive.
    let values = atoms.iter().map(|atom| (atom.clone(), expr(atom))).collect();
    cases(left, right, &atoms, 0, &values)
}

fn normalize(bit: &Bit) -> (Bit, Expr) {
    let raw = arguments(bit);
    let mut current = raw.clone();
    let mut proof = refl(kx::bool_ty(), expr(bit));
    for (index, child) in raw.iter().enumerate() {
        let (normalized, child_proof) = normalize(child);
        if *child == normalized {
            continue;
        }
        let before = with_arguments(bit, &current);
        let mut target = current.clone();
        target[index] = normalized.clone();
        let after = with_arguments(bit, &target);
        // Only this argument is abstracted. Other arguments are closed terms
        // over the same named data constants, so no de-Bruijn shift is hidden.
        let placeholder = Sym(format!("__unused_local_argument_{index}"));
        let mut abstract_args = current.clone();
        abstract_args[index] = placeholder.clone();
        let abstract_bit = with_arguments(bit, &abstract_args);
        let function = lam(
            kx::bool_ty(),
            replace(&abstract_bit, &BTreeMap::from([(placeholder, Expr::bvar(0))])),
        );
        let step = congr(
            kx::bool_ty(),
            kx::bool_ty(),
            expr(child),
            expr(&normalized),
            function,
            child_proof,
        );
        proof = trans(kx::bool_ty(), expr(bit), expr(&before), expr(&after), proof, step);
        current = target;
    }
    let before = with_arguments(bit, &current);
    let after = match &before {
        Not(a) => match &**a {
            Lit(v) => Lit(!v),
            Not(b) => (**b).clone(),
            _ => before.clone(),
        },
        And(a, b) => {
            if **a == Lit(false) || **b == Lit(false) {
                Lit(false)
            } else if **a == Lit(true) || a == b {
                (**b).clone()
            } else if **b == Lit(true) {
                (**a).clone()
            } else if b < a {
                And(b.clone(), a.clone())
            } else {
                before.clone()
            }
        }
        Or(a, b) => {
            if **a == Lit(true) || **b == Lit(true) {
                Lit(true)
            } else if **a == Lit(false) || a == b {
                (**b).clone()
            } else if **b == Lit(false) {
                (**a).clone()
            } else if b < a {
                Or(b.clone(), a.clone())
            } else {
                before.clone()
            }
        }
        Xor(a, b) => {
            if a == b {
                Lit(false)
            } else if **a == Lit(false) {
                (**b).clone()
            } else if **b == Lit(false) {
                (**a).clone()
            } else if **a == Lit(true) {
                Not(b.clone())
            } else if **b == Lit(true) {
                Not(a.clone())
            } else if b < a {
                Xor(b.clone(), a.clone())
            } else {
                before.clone()
            }
        }
        Ite(p, t, e) => {
            if **p == Lit(true) || t == e {
                (**t).clone()
            } else if **p == Lit(false) {
                (**e).clone()
            } else if **t == Lit(true) && **e == Lit(false) {
                (**p).clone()
            } else if **t == Lit(false) && **e == Lit(true) {
                Not(p.clone())
            } else {
                before.clone()
            }
        }
        _ => before.clone(),
    };
    if before == after {
        return (before, proof);
    }
    let atoms = match &before {
        Not(a) => match &**a {
            Not(inner) => vec![(**inner).clone()],
            _ => current.clone(),
        },
        _ => current.clone(),
    }
    .into_iter()
    .filter(|bit| !matches!(bit, Lit(_)))
    .collect::<Vec<_>>();
    let local = local_identity(&before, &after, &atoms);
    let proof = trans(kx::bool_ty(), expr(bit), expr(&before), expr(&after), proof, local);
    let (normal, tail) = normalize(&after);
    (normal.clone(), trans(kx::bool_ty(), expr(bit), expr(&after), expr(&normal), proof, tail))
}

fn bool_bits(formula: &Formula, context: &mut Context) -> Option<Bit> {
    match formula {
        Formula::Bool(v) => Some(Lit(*v)),
        Formula::Not(a) => Some(Not(boxed(bool_bits(a, context)?))),
        Formula::Eq(a, b) => {
            let a = bits(a, context, false)?;
            let b = bits(b, context, false)?;
            if a.len() != b.len() {
                return None;
            }
            Some(a.into_iter().zip(b).rev().fold(Lit(true), |tail, (a, b)| {
                And(boxed(Not(boxed(Xor(boxed(a), boxed(b))))), boxed(tail))
            }))
        }
        _ => None,
    }
}
fn bits(formula: &Formula, context: &mut Context, frame: bool) -> Option<Vec<Bit>> {
    let expected = width(formula)? as usize;
    let out = match formula {
        Formula::Var(name, Sort::BitVec(w)) => {
            context.variable(name, &Sort::BitVec(*w))?;
            let (_, names) = scalar_bits(name, *w);
            context.bits.extend(names.iter().cloned());
            names.into_iter().rev().map(Sym).collect()
        }
        Formula::BitVec { value, .. } => {
            (0..expected).map(|bit| Lit(((*value as u128 >> bit) & 1) != 0)).collect()
        }
        Formula::BvExtract { inner, high, low } => {
            bits(inner, context, frame)?[*low as usize..=*high as usize].to_vec()
        }
        Formula::BvZeroExt(inner, extra) => {
            let mut values = bits(inner, context, frame)?;
            values.extend(std::iter::repeat_n(Lit(false), *extra as usize));
            values
        }
        Formula::BvSignExt(inner, extra) => {
            let mut values = bits(inner, context, frame)?;
            let sign = values.last()?.clone();
            values.extend(std::iter::repeat_n(sign, *extra as usize));
            values
        }
        Formula::BvNot(inner, _) => {
            bits(inner, context, frame)?.into_iter().map(|b| Not(boxed(b))).collect()
        }
        Formula::BvAnd(a, b, _) | Formula::BvOr(a, b, _) | Formula::BvXor(a, b, _) => {
            bits(a, context, frame)?
                .into_iter()
                .zip(bits(b, context, frame)?)
                .map(|(a, b)| match formula {
                    Formula::BvAnd(..) => And(boxed(a), boxed(b)),
                    Formula::BvOr(..) => Or(boxed(a), boxed(b)),
                    _ => Xor(boxed(a), boxed(b)),
                })
                .collect()
        }
        Formula::BvShl(inner, amount, 64) if frame => {
            let Formula::BitVec { value, width: 64 } = &**amount else { return None };
            let shift = u32::try_from(*value).ok()?;
            if shift >= 64 {
                return None;
            }
            let mut out = vec![Lit(false); shift as usize];
            out.extend(bits(inner, context, true)?);
            out.truncate(64);
            out
        }
        Formula::BvConcat(high, low) => {
            let mut a = bits(low, context, frame)?;
            a.extend(bits(high, context, frame)?);
            a
        }
        Formula::Ite(p, t, e) => {
            let p = bool_bits(p, context)?;
            bits(t, context, frame)?
                .into_iter()
                .zip(bits(e, context, frame)?)
                .map(|(t, e)| Ite(boxed(p.clone()), boxed(t), boxed(e)))
                .collect()
        }
        _ => return None,
    };
    (out.len() == expected).then_some(out)
}

pub(super) fn frame_bits(formula: &Formula, context: &mut Context) -> Option<Vec<Bit>> {
    bits(formula, context, true)
}
pub(super) fn render(formula: &Formula, context: &mut Context) -> Option<Expr> {
    Some(kx::leaf(list(&bits(formula, context, false)?)))
}

// A closed proof combinator shares the suffix values rather than repeatedly
// expanding them inside both congrArg functions and Eq.trans argument types.
// Its six arguments still include BOTH actual values and BOTH actual proofs.
fn cons_congruence() -> Expr {
    let a = Expr::bvar(5);
    let b = Expr::bvar(4);
    let ta = Expr::bvar(3);
    let tb = Expr::bvar(2);
    let before = kx::cons(a.clone(), ta.clone());
    let middle = kx::cons(b.clone(), ta.clone());
    let after = kx::cons(b.clone(), tb.clone());
    let hp = congr(
        kx::bool_ty(),
        kx::list_bool(),
        a,
        b,
        lam(kx::bool_ty(), kx::cons(Expr::bvar(0), Expr::bvar(4))),
        Expr::bvar(1),
    );
    let tp = congr(
        kx::list_bool(),
        kx::list_bool(),
        ta,
        tb,
        lam(kx::list_bool(), kx::cons(Expr::bvar(5), Expr::bvar(0))),
        Expr::bvar(0),
    );
    let body = trans(kx::list_bool(), before, middle, after, hp, tp);
    let body = lam(equality(kx::list_bool(), Expr::bvar(2), Expr::bvar(1)), body);
    let body = lam(equality(kx::bool_ty(), Expr::bvar(3), Expr::bvar(2)), body);
    lam(kx::bool_ty(), lam(kx::bool_ty(), lam(kx::list_bool(), lam(kx::list_bool(), body))))
}

pub(super) fn equation(
    machine: &Formula,
    source: &Formula,
    context: &mut Context,
) -> Option<(Expr, Expr, Expr, Expr)> {
    let a = bits(machine, context, false)?;
    let b = bits(source, context, false)?;
    if a.len() != b.len() {
        return None;
    }
    let left = kx::evalf(original_value(machine, context)?);
    let right = kx::evalf(original_value(source, context)?);
    if machine == source {
        return Some((
            equality(kx::list_bool(), left.clone(), right.clone()),
            refl(kx::list_bool(), left.clone()),
            left,
            right,
        ));
    }
    let proof = prove_bits(&a, &b)?;
    let tail_a = list(&a);
    let tail_b = list(&b);
    // The proposition stays in the canonical original renderer. Only the
    // proof's value arguments use these definitionally equal explicit bits,
    // avoiding repeated expansion of original sign-extension operands. The
    // final kernel check must establish that conversion against the full goal.
    Some((equality(kx::list_bool(), left, right), proof, tail_a, tail_b))
}

pub(super) fn prove_bits(a: &[Bit], b: &[Bit]) -> Option<Expr> {
    if a.len() != b.len() {
        return None;
    }
    let mut tail_a = kx::nil();
    let mut tail_b = kx::nil();
    let mut proof = refl(kx::list_bool(), kx::nil());
    let cons = cons_congruence();
    for (a, b) in a.iter().zip(b).rev() {
        let (an, ap) = normalize(a);
        let (bn, bp) = normalize(b);
        if an != bn {
            return None;
        }
        let reverse = Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![Level::succ(Level::zero())]),
            [kx::bool_ty(), expr(b), expr(&bn), bp],
        );
        let head = trans(kx::bool_ty(), expr(a), expr(&an), expr(b), ap, reverse);
        let old = kx::cons(expr(a), tail_a.clone());
        let new = kx::cons(expr(b), tail_b.clone());
        proof = Expr::apps(
            cons.clone(),
            [expr(a), expr(b), tail_a.clone(), tail_b.clone(), head, proof],
        );
        tail_a = old;
        tail_b = new;
    }
    Some(proof)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn v(name: &str, width: u32) -> Formula {
        Formula::Var(name.into(), Sort::BitVec(width))
    }
    fn b(f: Formula) -> Box<Formula> {
        Box::new(f)
    }
    fn slice(f: Formula, h: u32, l: u32) -> Formula {
        Formula::BvExtract { inner: b(f), high: h, low: l }
    }
    fn c(value: i128, width: u32) -> Formula {
        Formula::BitVec { value, width }
    }
    #[test]
    fn signed_projection_original_equations_keep_all_bits() {
        for w in [8, 16] {
            let raw = v("X0", 64);
            let narrow = slice(raw.clone(), w - 1, 0);
            let physical = Formula::BvSignExt(b(narrow.clone()), 32 - w);
            let projected = Formula::BvOr(
                b(Formula::BvAnd(b(raw.clone()), b(c(0xffff_ffff_0000_0000, 64)), 64)),
                b(Formula::BvZeroExt(b(physical.clone()), 32)),
                64,
            );
            let valid = Formula::Eq(b(slice(raw.clone(), 31, 0)), b(physical));
            let eqfix = Formula::Eq(b(projected.clone()), b(raw.clone()));
            let pairs = vec![
                (slice(projected.clone(), w - 1, 0), narrow),
                (slice(projected, 63, 32), slice(raw, 63, 32)),
                (
                    Formula::Ite(b(eqfix), b(c(1, 1)), b(c(0, 1))),
                    Formula::Ite(b(valid), b(c(1, 1)), b(c(0, 1))),
                ),
            ];
            let checked = super::super::discharge_conjunction(&pairs)
                .expect("entire original signed domain laws");
            assert_eq!(checked.original_equations(), pairs);
            let mut wrong = pairs.clone();
            wrong[1].1 = slice(v("X0", 64), 62, 31);
            assert!(
                super::super::discharge_conjunction(&wrong).is_none(),
                "high32 is not disposable padding"
            );
        }
    }
    #[test]
    fn related_operands_are_independent_recursor_parameters() {
        let x = v("related", 8);
        let nx = Formula::BvNot(b(x.clone()), 8);
        let pairs =
            vec![(Formula::BvAnd(b(nx.clone()), b(x.clone()), 8), Formula::BvAnd(b(x), b(nx), 8))];
        let checked = super::super::discharge_conjunction(&pairs)
            .expect("commutation remains valid for related operands");
    }
    #[test]
    fn false_local_boolean_identity_is_rejected_by_kernel() {
        let a = Sym("a".into());
        let b = Sym("b".into());
        let left = And(boxed(a.clone()), boxed(b.clone()));
        let right = Or(boxed(a.clone()), boxed(b.clone()));
        let proof = local_identity(&left, &right, &[a, b]);
        let goal = equality(kx::bool_ty(), expr(&left), expr(&right));
        let context =
            Context { bits: ["a".into(), "b".into()].into_iter().collect(), ..Context::default() };
        assert!(
            run_recheck_thread("reject-false-local-bool", move || {
                let env = context_env(&context).unwrap();
                clean_kernel::TypeChecker::with_mode(&env, env.mode())
                    .check_type(&proof, &goal)
                    .is_err()
            })
            .unwrap()
        );
    }
    #[test]
    fn renderer_versions_preserve_formula_and_context_but_not_compact_syntax() {
        let v = Formula::BvSignExt(b(v("versioned", 8)), 24);
        let pairs = vec![(v.clone(), v)];
        let (old, oc) = super::super::original_conjunction_goal_version(&pairs, 1).unwrap();
        let (new, nc) = super::super::original_conjunction_goal_version(&pairs, 2).unwrap();
        assert_ne!(old, new);
        assert_eq!(oc, nc);
        assert!(super::super::original_conjunction_goal_version(&pairs, 99).is_none());
        let check = super::super::discharge_conjunction(&pairs).unwrap();
        assert_eq!(check.original_equations(), pairs);
    }
    #[test]
    fn memory_with_signed_value_uses_current_original_statement() {
        let memory = Formula::Var(
            "memory_signed".into(),
            Sort::Array(b_sort(Sort::BitVec(64)), b_sort(Sort::BitVec(8))),
        );
        let pointer = v("pointer_signed", 64);
        let value = v("value_signed", 8);
        let extended = Formula::BvSignExt(b(value.clone()), 56);
        let byte = slice(extended, 7, 0);
        let stored = Formula::Store(b(memory), b(pointer.clone()), b(byte));
        let read = Formula::Select(b(stored), b(pointer));
        let pairs = vec![(read.clone(), value.clone())];
        let checked = super::super::discharge_conjunction(&pairs)
            .expect("signed store/read fallback uses version2 canonical goal");
        assert_eq!(checked.original_equations(), pairs);
        assert!(
            super::super::discharge_conjunction(&[(read, Formula::BvNot(b(value), 8))]).is_none()
        );
    }
    fn b_sort(s: Sort) -> Box<Sort> {
        Box::new(s)
    }
}
