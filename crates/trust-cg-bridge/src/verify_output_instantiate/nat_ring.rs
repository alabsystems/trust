// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! An untrusted `+`/`*` normaliser over `Nat` that produces kernel proof terms.
//!
//! The bridge-side value theory (`bv_value`, and the strength-reduction
//! theorems built on it) needs many rearrangements of `Nat.add` / `Nat.mul`
//! terms: `n * succ d + m = n + (n * d + m)`, `2 * (a * b) = a * (2 * b)`, and
//! so on. Writing each as a chain of `Nat.add_assoc` / `Nat.mul_comm` /
//! distributivity instances by hand is error-prone, so this module computes
//! the chain.
//!
//! # Authority
//!
//! None. [`ring_eq`] returns a TERM; it is spliced into a
//! `Declaration::Theorem`'s proof and the Clean kernel type-checks the whole
//! declaration against its statement. A wrong normalisation step can only make
//! that check fail. Every lemma a produced term cites is a prelude theorem
//! listed in [`CITED`] or one of the helper theorems in [`names`], and the
//! environment that uses them audits each name (`add_comm::audit_theorems`).
//!
//! # The normal form
//!
//! An expression is a commutative-semiring polynomial over ATOMS: every
//! subterm that is not `Nat.add`, `Nat.mul`, `Nat.succ`, `Nat.zero` or a
//! small literal (a variable, `bvToNat xs`, `Nat.mod a n`, ...). Atoms are
//! compared structurally and numbered in order of first appearance in one
//! [`ring_eq`] call, so both sides share one numbering. The normal form is
//! fully right-nested with explicit terminators, so that every merge is a
//! local step:
//!
//! ```text
//! sum     ::= 0 | mono + sum          (monomials strictly increasing)
//! mono    ::= c * prod                (c a literal >= 1)
//! prod    ::= 1 | atom * prod         (atoms non-decreasing)
//! ```
//!
//! # What the kernel computes
//!
//! Only literal arithmetic on the coefficients (`Nat.add` / `Nat.mul` of two
//! literals, reduced natively) and the defeqs `x + 0 ≡ x`, `x * 0 ≡ 0`,
//! `succ x ≡ x + 1`, `0 ≡ Nat.zero`, `1 ≡ succ zero`. Never `Nat.mod`,
//! `Nat.div` or a recursor over closed data.

use clean_kernel::{BigNat, Expr, ExprKind, Literal};

use super::kterm::{Fresh, congr_arg, eq, lams, nadd, nat, nlit, nmul, pis, refl, symm, trans};

/// The prelude theorems a produced term cites. Each must pass the audit of the
/// environment the term is checked in.
pub(crate) const CITED: [&str; 10] = [
    "Nat.add_assoc",
    "Nat.add_comm",
    "Nat.mul_assoc",
    "Nat.mul_comm",
    "Nat.left_distrib",
    "Nat.right_distrib",
    "Nat.mul_one",
    "Nat.one_mul",
    "Nat.zero_add",
    "Nat.zero_mul",
];

/// The helper theorems a produced term cites, proved here ([`theorems`]) and
/// registered by `bv_value` before anything that uses the normaliser.
pub(crate) mod names {
    pub(crate) const ADD_LEFT_COMM: &str = "Trust.BVV.add_left_comm";
    pub(crate) const ADD_ADD_ADD_COMM: &str = "Trust.BVV.add_add_add_comm";
    pub(crate) const MUL_LEFT_COMM: &str = "Trust.BVV.mul_left_comm";
    pub(crate) const MUL_MUL_MUL_COMM: &str = "Trust.BVV.mul_mul_mul_comm";
    pub(crate) const ALL: [&str; 4] =
        [ADD_LEFT_COMM, ADD_ADD_ADD_COMM, MUL_LEFT_COMM, MUL_MUL_MUL_COMM];
}

// ── equations as data ────────────────────────────────────────────────────────

/// A proof `proof : lhs = rhs` over `Nat`, kept with its two sides so steps
/// can be chained without re-inferring types. The sides are what the term
/// states; where a step's own type differs from them only by a definitional
/// unfolding (`x + 0` for `x`), the kernel checks that unfolding.
#[derive(Clone, Debug)]
pub(crate) struct Eqn {
    pub(crate) lhs: Expr,
    pub(crate) rhs: Expr,
    pub(crate) proof: Expr,
}

impl Eqn {
    /// `lemma args… : lhs = rhs`.
    pub(crate) fn cite(name: &str, args: Vec<Expr>, lhs: Expr, rhs: Expr) -> Self {
        Self { lhs, rhs, proof: Expr::apps(Expr::const_str(name), args) }
    }
    /// `Eq.refl lhs`, stated as `lhs = rhs`: the kernel accepts it only when
    /// the two sides are definitionally equal.
    pub(crate) fn by_defeq(lhs: Expr, rhs: Expr) -> Self {
        Self { proof: refl(nat(), lhs.clone()), lhs, rhs }
    }
    /// `Eq.trans self next : self.lhs = next.rhs`, with `self.rhs` as the
    /// middle term (`next.lhs` must be definitionally equal to it).
    pub(crate) fn then(self, next: Eqn) -> Self {
        Self {
            proof: trans(
                nat(),
                self.lhs.clone(),
                self.rhs.clone(),
                next.rhs.clone(),
                self.proof,
                next.proof,
            ),
            lhs: self.lhs,
            rhs: next.rhs,
        }
    }
    /// `Eq.symm self : rhs = lhs`.
    pub(crate) fn symm(self) -> Self {
        Self {
            proof: symm(nat(), self.lhs.clone(), self.rhs.clone(), self.proof),
            lhs: self.rhs,
            rhs: self.lhs,
        }
    }
    /// `congrArg (fun t => ctx t) self : ctx lhs = ctx rhs`.
    pub(crate) fn under(self, fr: &mut Fresh, ctx: impl Fn(Expr) -> Expr) -> Self {
        let (t_id, t) = fr.local();
        let f = lams(vec![(t_id, nat())], ctx(t));
        Self {
            proof: congr_arg(nat(), nat(), self.lhs.clone(), self.rhs.clone(), f, self.proof),
            lhs: ctx(self.lhs),
            rhs: ctx(self.rhs),
        }
    }
}

/// `a1 + b1 = a2 + b2` from `a1 = a2` and `b1 = b2`.
fn add_both(fr: &mut Fresh, pa: Eqn, pb: Eqn) -> Eqn {
    let b1 = pb.lhs.clone();
    let a2 = pa.rhs.clone();
    pa.under(fr, |t| nadd(t, b1.clone())).then(pb.under(fr, |t| nadd(a2.clone(), t)))
}

/// `a1 * b1 = a2 * b2` from `a1 = a2` and `b1 = b2`.
fn mul_both(fr: &mut Fresh, pa: Eqn, pb: Eqn) -> Eqn {
    let b1 = pb.lhs.clone();
    let a2 = pa.rhs.clone();
    pa.under(fr, |t| nmul(t, b1.clone())).then(pb.under(fr, |t| nmul(a2.clone(), t)))
}

// ── the helper theorems ──────────────────────────────────────────────────────

/// `left_comm op : ∀ a b c, a ∘ (b ∘ c) = b ∘ (a ∘ c)` from the prelude's
/// associativity and commutativity of `∘`.
fn left_comm(op: fn(Expr, Expr) -> Expr, assoc: &str, comm: &str) -> (Expr, Expr) {
    let mut fr = Fresh::new();
    let stmt = |a: &Expr, b: &Expr, c: &Expr| {
        eq(nat(), op(a.clone(), op(b.clone(), c.clone())), op(b.clone(), op(a.clone(), c.clone())))
    };
    let ty = {
        let (a_id, a) = fr.local();
        let (b_id, b) = fr.local();
        let (c_id, c) = fr.local();
        pis(vec![(a_id, nat()), (b_id, nat()), (c_id, nat())], stmt(&a, &b, &c))
    };
    let val = {
        let (a_id, a) = fr.local();
        let (b_id, b) = fr.local();
        let (c_id, c) = fr.local();
        let assoc_abc = Eqn::cite(
            assoc,
            vec![a.clone(), b.clone(), c.clone()],
            op(op(a.clone(), b.clone()), c.clone()),
            op(a.clone(), op(b.clone(), c.clone())),
        );
        let swap = Eqn::cite(
            comm,
            vec![a.clone(), b.clone()],
            op(a.clone(), b.clone()),
            op(b.clone(), a.clone()),
        )
        .under(&mut fr, |t| op(t, c.clone()));
        let assoc_bac = Eqn::cite(
            assoc,
            vec![b.clone(), a.clone(), c.clone()],
            op(op(b.clone(), a.clone()), c.clone()),
            op(b.clone(), op(a.clone(), c.clone())),
        );
        let body = assoc_abc.symm().then(swap).then(assoc_bac);
        lams(vec![(a_id, nat()), (b_id, nat()), (c_id, nat())], body.proof)
    };
    (ty, val)
}

/// `four_comm op : ∀ a b c d, (a ∘ b) ∘ (c ∘ d) = (a ∘ c) ∘ (b ∘ d)`, from
/// associativity and the matching `left_comm` theorem.
fn four_comm(op: fn(Expr, Expr) -> Expr, assoc: &str, lcomm: &str) -> (Expr, Expr) {
    let mut fr = Fresh::new();
    let stmt = |a: &Expr, b: &Expr, c: &Expr, d: &Expr| {
        eq(
            nat(),
            op(op(a.clone(), b.clone()), op(c.clone(), d.clone())),
            op(op(a.clone(), c.clone()), op(b.clone(), d.clone())),
        )
    };
    let ty = {
        let (a_id, a) = fr.local();
        let (b_id, b) = fr.local();
        let (c_id, c) = fr.local();
        let (d_id, d) = fr.local();
        pis(vec![(a_id, nat()), (b_id, nat()), (c_id, nat()), (d_id, nat())], stmt(&a, &b, &c, &d))
    };
    let val = {
        let (a_id, a) = fr.local();
        let (b_id, b) = fr.local();
        let (c_id, c) = fr.local();
        let (d_id, d) = fr.local();
        let cd = op(c.clone(), d.clone());
        let bd = op(b.clone(), d.clone());
        let s1 = Eqn::cite(
            assoc,
            vec![a.clone(), b.clone(), cd.clone()],
            op(op(a.clone(), b.clone()), cd.clone()),
            op(a.clone(), op(b.clone(), cd)),
        );
        let s2 = Eqn::cite(
            lcomm,
            vec![b.clone(), c.clone(), d.clone()],
            op(b.clone(), op(c.clone(), d.clone())),
            op(c.clone(), bd.clone()),
        )
        .under(&mut fr, |t| op(a.clone(), t));
        let s3 = Eqn::cite(
            assoc,
            vec![a.clone(), c.clone(), bd.clone()],
            op(op(a.clone(), c.clone()), bd.clone()),
            op(a.clone(), op(c.clone(), bd)),
        )
        .symm();
        let body = s1.then(s2).then(s3);
        lams(vec![(a_id, nat()), (b_id, nat()), (c_id, nat()), (d_id, nat())], body.proof)
    };
    (ty, val)
}

/// The helper theorems in dependency order: `(name, statement, proof)`.
pub(crate) fn theorems() -> Vec<(&'static str, Expr, Expr)> {
    let named = |name: &'static str, (ty, val): (Expr, Expr)| (name, ty, val);
    vec![
        named(names::ADD_LEFT_COMM, left_comm(nadd, "Nat.add_assoc", "Nat.add_comm")),
        named(names::ADD_ADD_ADD_COMM, four_comm(nadd, "Nat.add_assoc", names::ADD_LEFT_COMM)),
        named(names::MUL_LEFT_COMM, left_comm(nmul, "Nat.mul_assoc", "Nat.mul_comm")),
        named(names::MUL_MUL_MUL_COMM, four_comm(nmul, "Nat.mul_assoc", names::MUL_LEFT_COMM)),
    ]
}

// ── the normaliser ───────────────────────────────────────────────────────────

/// A monomial `coeff * a1 * … * ak` with `atoms` sorted (non-decreasing).
#[derive(Clone, Debug, PartialEq, Eq)]
struct Mono {
    atoms: Vec<usize>,
    coeff: u64,
}

/// What `e` is to the normaliser.
enum View<'a> {
    Add(&'a Expr, &'a Expr),
    Mul(&'a Expr, &'a Expr),
    Succ(&'a Expr),
    Lit(u64),
    Atom,
}

fn view(e: &Expr) -> View<'_> {
    if let ExprKind::Lit(Literal::Nat(BigNat::Small(n))) = e.kind() {
        return View::Lit(*n);
    }
    let head = e.get_app_fn();
    let ExprKind::Const(name, _) = head.kind() else {
        return View::Atom;
    };
    let args = e.get_app_args();
    match (name.to_string().as_str(), args.len()) {
        ("Nat.add", 2) => View::Add(args[0], args[1]),
        ("Nat.mul", 2) => View::Mul(args[0], args[1]),
        ("Nat.succ", 1) => View::Succ(args[0]),
        ("Nat.zero", 0) => View::Lit(0),
        _ => View::Atom,
    }
}

/// Recursion bound on the input terms: the theorems this serves are small,
/// and a bound keeps a malformed input from exhausting the stack.
const MAX_DEPTH: usize = 256;

struct Ring<'f> {
    atoms: Vec<Expr>,
    fr: &'f mut Fresh,
}

impl Ring<'_> {
    fn atom_id(&mut self, e: &Expr) -> usize {
        if let Some(i) = self.atoms.iter().position(|a| a == e) {
            return i;
        }
        self.atoms.push(e.clone());
        self.atoms.len() - 1
    }

    /// `a1 * (a2 * (… * (ak * 1)))`.
    fn prod(&self, atoms: &[usize]) -> Expr {
        atoms.iter().rev().fold(nlit(1), |acc, &i| nmul(self.atoms[i].clone(), acc))
    }

    /// `c * prod`.
    fn mono(&self, m: &Mono) -> Expr {
        nmul(nlit(m.coeff), self.prod(&m.atoms))
    }

    /// `m1 + (m2 + (… + (mk + 0)))`.
    fn sum(&self, s: &[Mono]) -> Expr {
        s.iter().rev().fold(nlit(0), |acc, m| nadd(self.mono(m), acc))
    }

    /// `e = sum(s)` and `s`.
    fn norm(&mut self, e: &Expr, depth: usize) -> Option<(Vec<Mono>, Eqn)> {
        if depth > MAX_DEPTH {
            return None;
        }
        match view(e) {
            View::Lit(0) => Some((vec![], Eqn::by_defeq(e.clone(), nlit(0)))),
            View::Lit(c) => {
                let s = vec![Mono { atoms: vec![], coeff: c }];
                // `c * 1 + 0` computes to `c`.
                let rhs = self.sum(&s);
                Some((s, Eqn::by_defeq(e.clone(), rhs)))
            }
            View::Atom => {
                let i = self.atom_id(e);
                let s = vec![Mono { atoms: vec![i], coeff: 1 }];
                // a = 1 * (a * 1)  (by mul_one, one_mul), and `+ 0` unfolds.
                let a1 = nmul(e.clone(), nlit(1));
                let p = Eqn::cite(
                    "Nat.one_mul",
                    vec![a1.clone()],
                    nmul(nlit(1), a1.clone()),
                    a1.clone(),
                )
                .then(Eqn::cite("Nat.mul_one", vec![e.clone()], a1, e.clone()))
                .symm();
                let rhs = self.sum(&s);
                Some((s, Eqn { lhs: p.lhs, rhs, proof: p.proof }))
            }
            View::Succ(a) => {
                // succ a ≡ a + 1.
                let plus = nadd(a.clone(), nlit(1));
                let (s, p) = self.norm(&plus, depth + 1)?;
                Some((s, Eqn::by_defeq(e.clone(), plus).then(p)))
            }
            View::Add(a, b) => {
                let (sa, pa) = self.norm(a, depth + 1)?;
                let (sb, pb) = self.norm(b, depth + 1)?;
                let both = add_both(self.fr, pa, pb);
                let (s, p) = self.add_sums(&sa, &sb)?;
                Some((s, both.then(p)))
            }
            View::Mul(a, b) => {
                let (sa, pa) = self.norm(a, depth + 1)?;
                let (sb, pb) = self.norm(b, depth + 1)?;
                let both = mul_both(self.fr, pa, pb);
                let (s, p) = self.mul_sums(&sa, &sb)?;
                Some((s, both.then(p)))
            }
        }
    }

    /// `sum(s1) + sum(s2) = sum(s)`, merging like monomials.
    fn add_sums(&mut self, s1: &[Mono], s2: &[Mono]) -> Option<(Vec<Mono>, Eqn)> {
        let (r1, r2) = (self.sum(s1), self.sum(s2));
        let lhs = nadd(r1.clone(), r2.clone());
        let (Some((m1, t1)), Some((m2, t2))) = (s1.split_first(), s2.split_first()) else {
            if s1.is_empty() {
                // 0 + r2 = r2
                return Some((s2.to_vec(), Eqn::cite("Nat.zero_add", vec![r2.clone()], lhs, r2)));
            }
            // r1 + 0 ≡ r1
            return Some((s1.to_vec(), Eqn::by_defeq(lhs, r1)));
        };
        let (e1, e2) = (self.mono(m1), self.mono(m2));
        let (q1, q2) = (self.sum(t1), self.sum(t2));
        match m1.atoms.cmp(&m2.atoms) {
            std::cmp::Ordering::Less => {
                // (m1 + t1) + r2 = m1 + (t1 + r2)
                let s1_ = Eqn::cite(
                    "Nat.add_assoc",
                    vec![e1.clone(), q1.clone(), r2.clone()],
                    lhs,
                    nadd(e1.clone(), nadd(q1, r2)),
                );
                let (rest, p) = self.add_sums(t1, s2)?;
                let p = p.under(self.fr, |t| nadd(e1.clone(), t));
                let mut s = vec![m1.clone()];
                s.extend(rest);
                Some((s, s1_.then(p)))
            }
            std::cmp::Ordering::Greater => {
                // r1 + (m2 + t2) = m2 + (r1 + t2)
                let s1_ = Eqn::cite(
                    names::ADD_LEFT_COMM,
                    vec![r1.clone(), e2.clone(), q2.clone()],
                    lhs,
                    nadd(e2.clone(), nadd(r1, q2)),
                );
                let (rest, p) = self.add_sums(s1, t2)?;
                let p = p.under(self.fr, |t| nadd(e2.clone(), t));
                let mut s = vec![m2.clone()];
                s.extend(rest);
                Some((s, s1_.then(p)))
            }
            std::cmp::Ordering::Equal => {
                // (m1 + t1) + (m2 + t2) = (m1 + m2) + (t1 + t2)
                let s1_ = Eqn::cite(
                    names::ADD_ADD_ADD_COMM,
                    vec![e1.clone(), q1.clone(), e2.clone(), q2.clone()],
                    lhs,
                    nadd(nadd(e1.clone(), e2.clone()), nadd(q1, q2)),
                );
                // c1 * x + c2 * x = (c1 + c2) * x, and `c1 + c2` computes.
                let coeff = m1.coeff.checked_add(m2.coeff)?;
                let m = Mono { atoms: m1.atoms.clone(), coeff };
                let x = self.prod(&m.atoms);
                let combine = Eqn::cite(
                    "Nat.right_distrib",
                    vec![nlit(m1.coeff), nlit(m2.coeff), x.clone()],
                    nmul(nadd(nlit(m1.coeff), nlit(m2.coeff)), x),
                    nadd(e1, e2),
                )
                .symm();
                let combine = Eqn { rhs: self.mono(&m), ..combine };
                let (rest, p) = self.add_sums(t1, t2)?;
                let both = add_both(self.fr, combine, p);
                let mut s = vec![m];
                s.extend(rest);
                Some((s, s1_.then(both)))
            }
        }
    }

    /// `sum(s1) * sum(s2) = sum(s)`, distributing.
    fn mul_sums(&mut self, s1: &[Mono], s2: &[Mono]) -> Option<(Vec<Mono>, Eqn)> {
        let (r1, r2) = (self.sum(s1), self.sum(s2));
        let lhs = nmul(r1.clone(), r2.clone());
        let Some((m1, t1)) = s1.split_first() else {
            // 0 * r2 = 0
            return Some((vec![], Eqn::cite("Nat.zero_mul", vec![r2], lhs, nlit(0))));
        };
        let (e1, q1) = (self.mono(m1), self.sum(t1));
        // (m1 + t1) * r2 = m1 * r2 + t1 * r2
        let dist = Eqn::cite(
            "Nat.right_distrib",
            vec![e1.clone(), q1.clone(), r2.clone()],
            lhs,
            nadd(nmul(e1, r2.clone()), nmul(q1, r2)),
        );
        let (sa, pa) = self.mono_mul_sum(m1, s2)?;
        let (sb, pb) = self.mul_sums(t1, s2)?;
        let both = add_both(self.fr, pa, pb);
        let (s, p) = self.add_sums(&sa, &sb)?;
        Some((s, dist.then(both).then(p)))
    }

    /// `mono(m) * sum(s2) = sum(s)`.
    fn mono_mul_sum(&mut self, m: &Mono, s2: &[Mono]) -> Option<(Vec<Mono>, Eqn)> {
        let (e, r2) = (self.mono(m), self.sum(s2));
        let lhs = nmul(e.clone(), r2);
        let Some((m2, t2)) = s2.split_first() else {
            // m * 0 ≡ 0
            return Some((vec![], Eqn::by_defeq(lhs, nlit(0))));
        };
        let (e2, q2) = (self.mono(m2), self.sum(t2));
        // m * (m2 + t2) = m * m2 + m * t2
        let dist = Eqn::cite(
            "Nat.left_distrib",
            vec![e.clone(), e2.clone(), q2.clone()],
            lhs,
            nadd(nmul(e.clone(), e2), nmul(e, q2)),
        );
        let (mm, pm) = self.mono_mul_mono(m, m2)?;
        let single = vec![mm];
        // m * m2 = mm, stated as `mm + 0` (which unfolds to `mm`).
        let pm = Eqn { rhs: self.sum(&single), ..pm };
        let (sb, pb) = self.mono_mul_sum(m, t2)?;
        let both = add_both(self.fr, pm, pb);
        let (s, p) = self.add_sums(&single, &sb)?;
        Some((s, dist.then(both).then(p)))
    }

    /// `mono(m1) * mono(m2) = mono(m)`.
    fn mono_mul_mono(&mut self, m1: &Mono, m2: &Mono) -> Option<(Mono, Eqn)> {
        let (x1, x2) = (self.prod(&m1.atoms), self.prod(&m2.atoms));
        let (c1, c2) = (nlit(m1.coeff), nlit(m2.coeff));
        // (c1 * x1) * (c2 * x2) = (c1 * c2) * (x1 * x2)
        let four = Eqn::cite(
            names::MUL_MUL_MUL_COMM,
            vec![c1.clone(), x1.clone(), c2.clone(), x2.clone()],
            nmul(nmul(c1.clone(), x1.clone()), nmul(c2.clone(), x2.clone())),
            nmul(nmul(c1.clone(), c2.clone()), nmul(x1, x2)),
        );
        let (atoms, px) = self.prod_merge(&m1.atoms, &m2.atoms);
        let cc = nmul(c1, c2);
        let px = px.under(self.fr, |t| nmul(cc.clone(), t));
        let m = Mono { atoms, coeff: m1.coeff.checked_mul(m2.coeff)? };
        // `c1 * c2` computes to the literal.
        let px = Eqn { rhs: self.mono(&m), ..px };
        Some((m, four.then(px)))
    }

    /// `prod(a1) * prod(a2) = prod(merge)`.
    fn prod_merge(&mut self, a1: &[usize], a2: &[usize]) -> (Vec<usize>, Eqn) {
        let (p1, p2) = (self.prod(a1), self.prod(a2));
        let lhs = nmul(p1.clone(), p2.clone());
        let (Some((&h1, r1)), Some((&h2, r2))) = (a1.split_first(), a2.split_first()) else {
            if a1.is_empty() {
                // 1 * p2 = p2
                return (a2.to_vec(), Eqn::cite("Nat.one_mul", vec![p2.clone()], lhs, p2));
            }
            // p1 * 1 = p1
            return (a1.to_vec(), Eqn::cite("Nat.mul_one", vec![p1.clone()], lhs, p1));
        };
        if h1 <= h2 {
            // (h1 * q1) * p2 = h1 * (q1 * p2)
            let (x, q1) = (self.atoms[h1].clone(), self.prod(r1));
            let step = Eqn::cite(
                "Nat.mul_assoc",
                vec![x.clone(), q1.clone(), p2.clone()],
                lhs,
                nmul(x.clone(), nmul(q1, p2)),
            );
            let (rest, p) = self.prod_merge(r1, a2);
            let p = p.under(self.fr, |t| nmul(x.clone(), t));
            let mut atoms = vec![h1];
            atoms.extend(rest);
            (atoms, step.then(p))
        } else {
            // p1 * (h2 * q2) = h2 * (p1 * q2)
            let (x, q2) = (self.atoms[h2].clone(), self.prod(r2));
            let step = Eqn::cite(
                names::MUL_LEFT_COMM,
                vec![p1.clone(), x.clone(), q2.clone()],
                lhs,
                nmul(x.clone(), nmul(p1, q2)),
            );
            let (rest, p) = self.prod_merge(a1, r2);
            let p = p.under(self.fr, |t| nmul(x.clone(), t));
            let mut atoms = vec![h2];
            atoms.extend(rest);
            (atoms, step.then(p))
        }
    }
}

/// A proof of `lhs = rhs` when the two are equal as commutative-semiring
/// polynomials over their atoms; `None` when they are not (or a coefficient
/// leaves `u64`, or a term is deeper than the bound). The term cites only
/// [`CITED`] and [`names::ALL`]; the kernel checks it where it is used.
pub(crate) fn ring_eq(fr: &mut Fresh, lhs: &Expr, rhs: &Expr) -> Option<Eqn> {
    let mut ring = Ring { atoms: Vec::new(), fr };
    let (s1, p1) = ring.norm(lhs, 0)?;
    let (s2, p2) = ring.norm(rhs, 0)?;
    (s1 == s2).then(|| p1.then(p2.symm()))
}

/// From `h : a = b`, a proof of `a2 = b2` when `a2` and `a` are equal as
/// polynomials, and so are `b` and `b2`.
pub(crate) fn ring_rw(fr: &mut Fresh, h: Eqn, a2: &Expr, b2: &Expr) -> Option<Eqn> {
    let pa = ring_eq(fr, a2, &h.lhs)?;
    let pb = ring_eq(fr, &h.rhs, b2)?;
    Some(pa.then(h).then(pb))
}

#[cfg(test)]
mod tests {
    use clean_kernel::name::Name;
    use clean_kernel::{Declaration, Environment, TypeChecker};

    use super::super::{add_comm, run_recheck_thread};
    use super::*;

    /// The commuting base plus the helper theorems, audited.
    fn ring_env() -> Environment {
        let mut env = add_comm::commuting_base().expect("base").clone();
        for (name, type_, value) in theorems() {
            env.add_decl(Declaration::Theorem {
                name: Name::from_string(name),
                level_params: vec![],
                type_,
                value,
            })
            .unwrap_or_else(|e| panic!("{name}: {e:?}"));
        }
        add_comm::audit_theorems(&env, &names::ALL).expect("helper theorems audit");
        add_comm::audit_theorems(&env, &CITED).expect("cited prelude lemmas audit");
        env
    }

    /// Check `∀ vars, lhs = rhs` with the normaliser's proof; `None` when the
    /// normaliser declines.
    fn prove(nvars: usize, build: impl Fn(&[Expr]) -> (Expr, Expr)) -> Option<bool> {
        let mut fr = Fresh::new();
        let locals: Vec<_> = (0..nvars).map(|_| fr.local()).collect();
        let vars: Vec<Expr> = locals.iter().map(|(_, v)| v.clone()).collect();
        let (lhs, rhs) = build(&vars);
        let p = ring_eq(&mut fr, &lhs, &rhs)?;
        let binders: Vec<_> = locals.iter().map(|(id, _)| (*id, nat())).collect();
        let ty = pis(binders.clone(), eq(nat(), lhs, rhs));
        let val = lams(binders, p.proof);
        Some(
            run_recheck_thread("nat-ring-test", move || {
                let env = ring_env();
                let tc = TypeChecker::with_mode(&env, env.mode());
                tc.check_type(&val, &ty).map_err(|e| format!("{e:?}"))
            })
            .expect("kernel thread")
            .is_ok(),
        )
    }

    #[test]
    fn helper_theorems_check_and_pass_the_audit() {
        run_recheck_thread("nat-ring-helpers", || {
            let _ = ring_env();
        })
        .expect("kernel thread");
    }

    /// Identities the value theory needs, each proved by the normaliser and
    /// accepted by the kernel.
    #[test]
    fn ring_identities_are_kernel_checked() {
        let succ = |e: &Expr| super::super::kterm::succ(e.clone());
        type Case = (&'static str, usize, Box<dyn Fn(&[Expr]) -> (Expr, Expr)>);
        let cases: Vec<Case> = vec![
            (
                "x*3+7 = 7+3*x",
                1,
                Box::new(|v| {
                    (
                        nadd(nmul(v[0].clone(), nlit(3)), nlit(7)),
                        nadd(nlit(7), nmul(nlit(3), v[0].clone())),
                    )
                }),
            ),
            (
                "x+x = 2*x",
                1,
                Box::new(|v| (nadd(v[0].clone(), v[0].clone()), nmul(nlit(2), v[0].clone()))),
            ),
            (
                "n*succ d + m = n + (n*d + m)",
                3,
                Box::new(move |v| {
                    (
                        nadd(nmul(v[0].clone(), succ(&v[1])), v[2].clone()),
                        nadd(v[0].clone(), nadd(nmul(v[0].clone(), v[1].clone()), v[2].clone())),
                    )
                }),
            ),
            (
                "n*0 + m = m",
                2,
                Box::new(|v| {
                    (
                        nadd(nmul(v[0].clone(), super::super::kterm::zero()), v[1].clone()),
                        v[1].clone(),
                    )
                }),
            ),
            (
                "2*(a*b) = a*(2*b)",
                2,
                Box::new(|v| {
                    (
                        nmul(nlit(2), nmul(v[0].clone(), v[1].clone())),
                        nmul(v[0].clone(), nmul(nlit(2), v[1].clone())),
                    )
                }),
            ),
            (
                "(a+b)*(a+b) = a*a + 2*a*b + b*b",
                2,
                Box::new(|v| {
                    let (a, b) = (v[0].clone(), v[1].clone());
                    (
                        nmul(nadd(a.clone(), b.clone()), nadd(a.clone(), b.clone())),
                        nadd(
                            nadd(
                                nmul(a.clone(), a.clone()),
                                nmul(nmul(nlit(2), a.clone()), b.clone()),
                            ),
                            nmul(b.clone(), b),
                        ),
                    )
                }),
            ),
            (
                "succ b + 2*r = succ (b + 2*r)",
                2,
                Box::new(move |v| {
                    let r2 = nmul(nlit(2), v[1].clone());
                    (nadd(succ(&v[0]), r2.clone()), succ(&nadd(v[0].clone(), r2)))
                }),
            ),
            (
                "2 + 2*r = 2 * succ r",
                1,
                Box::new(move |v| {
                    (nadd(nlit(2), nmul(nlit(2), v[0].clone())), nmul(nlit(2), succ(&v[0])))
                }),
            ),
            (
                "a = 0 + 1*a",
                1,
                Box::new(|v| (v[0].clone(), nadd(nlit(0), nmul(nlit(1), v[0].clone())))),
            ),
            (
                "(q*n + r) + n*k = r + n*(q + k)",
                4,
                Box::new(|v| {
                    let (q, n, r, k) = (v[0].clone(), v[1].clone(), v[2].clone(), v[3].clone());
                    (
                        nadd(
                            nadd(nmul(q.clone(), n.clone()), r.clone()),
                            nmul(n.clone(), k.clone()),
                        ),
                        nadd(r, nmul(n, nadd(q, k))),
                    )
                }),
            ),
        ];
        for (name, n, build) in cases {
            assert_eq!(prove(n, build), Some(true), "{name}");
        }
    }

    /// Unequal polynomials are declined, not given a term.
    #[test]
    fn unequal_polynomials_are_declined() {
        assert_eq!(prove(1, |v| (nmul(v[0].clone(), nlit(2)), nmul(v[0].clone(), nlit(3)))), None);
        assert_eq!(prove(2, |v| (nadd(v[0].clone(), nlit(1)), nadd(v[1].clone(), nlit(1)))), None);
        assert_eq!(
            prove(2, |v| (nmul(v[0].clone(), v[1].clone()), nadd(v[0].clone(), v[1].clone()))),
            None
        );
    }

    /// The normaliser's term for one identity is not a proof of another: the
    /// kernel, not the normaliser, decides.
    #[test]
    fn a_ring_term_is_rejected_against_a_different_goal() {
        let mut fr = Fresh::new();
        let (x_id, x) = fr.local();
        let lhs = nadd(x.clone(), x.clone());
        let p = ring_eq(&mut fr, &lhs, &nmul(nlit(2), x.clone())).expect("x + x = 2 * x");
        let wrong = pis(vec![(x_id, nat())], eq(nat(), lhs, nmul(nlit(3), x)));
        let val = lams(vec![(x_id, nat())], p.proof);
        let verdict = run_recheck_thread("nat-ring-negative", move || {
            let env = ring_env();
            let tc = TypeChecker::with_mode(&env, env.mode());
            tc.check_type(&val, &wrong).is_ok()
        })
        .expect("kernel thread");
        assert!(!verdict, "x + x = 3 * x was accepted");
    }
}
