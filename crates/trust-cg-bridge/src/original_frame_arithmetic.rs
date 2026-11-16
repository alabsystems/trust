//! Constructive proof DATA for original fixed-width frame arithmetic.
//!
//! No arithmetic normalizer or ABI assumption is authoritative here. These
//! terms use the existing BVC ripple-adder definitions, List.rec and Bool.rec;
//! the consumer must check them against its independently rebuilt ORIGINAL goal.
use clean_kernel::{BinderInfo, Expr, FVarId, Level, Name};

fn c(name: &str) -> Expr {
    Expr::const_str(name)
}
fn b(value: bool) -> Expr {
    c(if value { "Bool.true" } else { "Bool.false" })
}
fn bt() -> Expr {
    c("Bool")
}
fn lb() -> Expr {
    Expr::app(Expr::const_(Name::from_string("List"), vec![Level::zero()]), bt())
}
fn nil() -> Expr {
    Expr::app(Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]), bt())
}
fn cons(h: Expr, t: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]), [bt(), h, t])
}
fn list(bits: &[Expr]) -> Expr {
    bits.iter().rev().fold(nil(), |t, h| cons(h.clone(), t))
}
fn eq(ty: Expr, x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]), [ty, x, y])
}
fn refl(ty: Expr, x: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
        [ty, x],
    )
}
fn add(x: Expr, y: Expr, carry: Expr) -> Expr {
    Expr::apps(c("Clean.BVI.addRecM"), [x, y, carry])
}
fn all_false(x: Expr) -> Expr {
    Expr::app(c("Clean.BVC.bvAllFalse"), x)
}
fn not(x: Expr) -> Expr {
    Expr::app(c("Bool.not"), x)
}
fn bv_not(x: Expr) -> Expr {
    Expr::app(c("Clean.BVC.bvNot"), x)
}
fn beq(x: Expr, y: Expr) -> Expr {
    Expr::apps(c("Clean.BVC.bvBeq"), [x, y])
}
fn bool_rec(motive: Expr, low: Expr, high: Expr, major: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
        [motive, low, high, major],
    )
}
fn lambda(id: FVarId, ty: Expr, body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, ty, body.abstract_fvar(id))
}
fn pi(id: FVarId, ty: Expr, body: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, ty, body.abstract_fvar(id))
}
struct Locals(u64);
impl Locals {
    fn fresh(&mut self) -> (FVarId, Expr) {
        self.0 += 1;
        let id = FVarId::new(self.0);
        (id, Expr::fvar(id))
    }
}
fn prepend_proof(head: Expr, left: Expr, right: Expr, proof: Expr) -> Expr {
    let level = Level::succ(Level::zero());
    let fun = Expr::lam(BinderInfo::Default, lb(), cons(head, Expr::bvar(0)));
    Expr::apps(
        Expr::const_(Name::from_string("congrArg"), vec![level.clone(), level]),
        [lb(), lb(), left, right, fun, proof],
    )
}
fn cancel_lhs(xs: Expr, carry: Expr) -> Expr {
    add(add(xs.clone(), bv_not(all_false(xs.clone())), carry.clone()), all_false(xs), not(carry))
}
fn cancel_goal(xs: Expr, carry: Expr) -> Expr {
    eq(lb(), cancel_lhs(xs.clone(), carry), xs)
}

/// Closed List.rec proof, with no environmental lemma/axiom registration:
/// ∀ xs c, add(add(xs, allTrue(xs), c), allFalse(xs), !c) = xs.
/// The two carries remain complementary; every cons step checks all four
/// constructor cases of the current head and carry by dependent elimination.
pub(crate) fn complementary_carry_cancellation() -> (Expr, Expr) {
    let mut l = Locals(0);
    let (xsid, xs) = l.fresh();
    let (cid, carry) = l.fresh();
    let ty = pi(xsid, lb(), pi(cid, bt(), cancel_goal(xs.clone(), carry.clone())));
    let motive = lambda(xsid, lb(), pi(cid, bt(), cancel_goal(xs.clone(), carry.clone())));
    let base = lambda(cid, bt(), refl(lb(), nil()));
    let (hid, h) = l.fresh();
    let (tid, t) = l.fresh();
    let (ihid, ih) = l.fresh();
    let ih_ty = pi(cid, bt(), cancel_goal(t.clone(), carry.clone()));
    let mut head_branches = Vec::new();
    for hv in [false, true] {
        let mut carry_branches = Vec::new();
        for cv in [false, true] {
            let next = b(hv || cv);
            carry_branches.push(prepend_proof(
                b(hv),
                cancel_lhs(t.clone(), next.clone()),
                t.clone(),
                Expr::app(ih.clone(), next),
            ));
        }
        let motive_c = lambda(cid, bt(), cancel_goal(cons(b(hv), t.clone()), carry.clone()));
        head_branches.push(lambda(
            cid,
            bt(),
            bool_rec(motive_c, carry_branches[0].clone(), carry_branches[1].clone(), carry.clone()),
        ));
    }
    let motive_h =
        lambda(hid, bt(), pi(cid, bt(), cancel_goal(cons(h.clone(), t.clone()), carry.clone())));
    let step = bool_rec(motive_h, head_branches[0].clone(), head_branches[1].clone(), h.clone());
    let step = lambda(hid, bt(), lambda(tid, lb(), lambda(ihid, ih_ty, step)));
    let proof = Expr::apps(
        Expr::const_(Name::from_string("List.rec"), vec![Level::zero(), Level::zero()]),
        [bt(), motive, base, step, xs],
    );
    (ty, lambda(xsid, lb(), proof))
}
fn mask16(tail: Expr) -> Expr {
    let mut v = cons(b(true), all_false(tail));
    for _ in 0..4 {
        v = cons(b(false), v)
    }
    v
}
fn minus16(tail: Expr) -> Expr {
    let mut v = cons(b(true), bv_not(all_false(tail)));
    for _ in 0..4 {
        v = cons(b(false), v)
    }
    v
}
fn root(bits: &[Expr], tail: Expr) -> Expr {
    bits.iter().rev().fold(tail, |t, h| cons(h.clone(), t))
}
fn restore_lhs(low: &[Expr], tail: Expr, sub: bool) -> Expr {
    let sp = root(low, tail.clone());
    let pos = mask16(tail.clone());
    let (negative, carry) =
        if sub { (bv_not(pos.clone()), b(true)) } else { (minus16(tail), b(false)) };
    add(add(sp, negative, carry), pos, b(false))
}
fn restore_goal(low: &[Expr], tail: Expr, sub: bool) -> Expr {
    eq(lb(), restore_lhs(low, tail.clone(), sub), root(low, tail))
}

fn restore_lemma(sub: bool) -> Expr {
    let mut l = Locals(0);
    let (tid, tail) = l.fresh();
    let vars: Vec<_> = (0..5).map(|_| l.fresh()).collect();
    let lows: Vec<_> = vars.iter().map(|(_, v)| v.clone()).collect();
    let cancellation = complementary_carry_cancellation().1;
    fn cases(
        index: usize,
        vars: &[(FVarId, Expr)],
        low: &[Expr],
        tail: &Expr,
        sub: bool,
        cancellation: &Expr,
    ) -> Expr {
        if index == 5 {
            let mut proof = Expr::apps(cancellation.clone(), [tail.clone(), low[4].clone()]);
            let mut left = cancel_lhs(tail.clone(), low[4].clone());
            let mut right = tail.clone();
            for h in low.iter().rev() {
                proof = prepend_proof(h.clone(), left.clone(), right.clone(), proof);
                left = cons(h.clone(), left);
                right = cons(h.clone(), right)
            }
            return proof;
        }
        let mut lo = low.to_vec();
        lo[index] = b(false);
        let mut hi = low.to_vec();
        hi[index] = b(true);
        let motive = lambda(vars[index].0, bt(), restore_goal(low, tail.clone(), sub));
        bool_rec(
            motive,
            cases(index + 1, vars, &lo, tail, sub, cancellation),
            cases(index + 1, vars, &hi, tail, sub, cancellation),
            low[index].clone(),
        )
    }
    let mut proof = cases(0, &vars, &lows, &tail, sub, &cancellation);
    for (id, _) in vars.iter().rev() {
        proof = lambda(*id, bt(), proof)
    }
    lambda(tid, lb(), proof)
}
/// Proof of the exact 64-bit ORIGINAL nested additions `(SP + -16) + 16 = SP`.
/// Returns untrusted proof data; a final independent goal/kernel check is required.
pub(crate) fn restore_sp(bits: &[Expr; 64]) -> Expr {
    Expr::apps(
        restore_lemma(false),
        std::iter::once(list(&bits[5..])).chain(bits[..5].iter().cloned()),
    )
}
/// Same exact restoration when the ORIGINAL source term is explicit subtraction.
pub(crate) fn restore_sp_sub(bits: &[Expr; 64]) -> Expr {
    Expr::apps(
        restore_lemma(true),
        std::iter::once(list(&bits[5..])).chain(bits[..5].iter().cloned()),
    )
}
fn constant_n(value: i128, width: usize) -> Expr {
    list(&(0..width).map(|n| b(((value as u128 >> n) & 1) != 0)).collect::<Vec<_>>())
}
fn constant(value: i128) -> Expr {
    constant_n(value, 64)
}
fn nested_n(base: Expr, addends: &[i128], width: usize) -> Expr {
    addends.iter().fold(base, |x, k| add(x, constant_n(*k, width), b(false)))
}
fn nested(base: Expr, addends: &[i128]) -> Expr {
    nested_n(base, addends, 64)
}
// Total List.tail expressed by the existing eliminator. No new declaration or
// model rule is installed. Used only to share the full ORIGINAL higher tails.
fn tail(value: Expr) -> Expr {
    let motive = Expr::lam(BinderInfo::Default, lb(), lb());
    let step = Expr::lam(
        BinderInfo::Default,
        bt(),
        Expr::lam(BinderInfo::Default, lb(), Expr::lam(BinderInfo::Default, lb(), Expr::bvar(1))),
    );
    Expr::apps(
        Expr::const_(
            Name::from_string("List.rec"),
            vec![Level::succ(Level::zero()), Level::zero()],
        ),
        [bt(), motive, nil(), step, value],
    )
}
fn drop4(mut value: Expr) -> Expr {
    for _ in 0..4 {
        value = tail(value)
    }
    value
}
fn append(prefix: Expr, rest: Expr) -> Expr {
    Expr::apps(c("Clean.BVC.bvAppend"), [prefix, rest])
}
/// Actual exact nested-add address terms, useful to independently build a goal.
pub(crate) fn offset_goal(bits: &[Expr; 64], left: &[i128], right: &[i128]) -> Expr {
    eq(bt(), beq(nested(list(bits), left), nested(list(bits), right)), b(false))
}
/// Constructive inequality when exact constant chains differ in their low4 sum.
/// All sixteen low-bit branches are proved by reduction; higher60 SP bits remain
/// arbitrary. No alignment, no-no-wrap or numeric-domain premise is assumed.
pub(crate) fn distinct_offsets(bits: &[Expr; 64], left: &[i128], right: &[i128]) -> Option<Expr> {
    if left.len() > 8 || right.len() > 8 {
        return None;
    }
    let residue = |xs: &[i128]| xs.iter().fold(0u8, |x, y| x.wrapping_add(*y as u8)) & 15;
    if residue(left) == residue(right) {
        return None;
    }
    let mut l = Locals(0);
    let (aid, at) = l.fresh();
    let (bid, btail) = l.fresh();
    let vars: Vec<_> = (0..4).map(|_| l.fresh()).collect();
    let low: Vec<_> = vars.iter().map(|(_, e)| e.clone()).collect();
    fn goal(low: &[Expr], at: &Expr, btail: &Expr, left: &[i128], right: &[i128]) -> Expr {
        let a = append(nested_n(list(low), left, 4), at.clone());
        let b = append(nested_n(list(low), right, 4), btail.clone());
        eq(bt(), beq(a, b), self::b(false))
    }
    fn cases(
        i: usize,
        vars: &[(FVarId, Expr)],
        low: &[Expr],
        at: &Expr,
        btail: &Expr,
        left: &[i128],
        right: &[i128],
    ) -> Expr {
        if i == 4 {
            return refl(bt(), b(false));
        }
        let mut lo = low.to_vec();
        lo[i] = b(false);
        let mut hi = low.to_vec();
        hi[i] = b(true);
        let motive = lambda(vars[i].0, bt(), goal(low, at, btail, left, right));
        bool_rec(
            motive,
            cases(i + 1, vars, &lo, at, btail, left, right),
            cases(i + 1, vars, &hi, at, btail, left, right),
            low[i].clone(),
        )
    }
    let mut proof = cases(0, &vars, &low, &at, &btail, left, right);
    for (id, _) in vars.iter().rev() {
        proof = lambda(*id, bt(), proof)
    }
    let proof = lambda(aid, lb(), lambda(bid, lb(), proof));
    let actual_left = nested(list(bits), left);
    let actual_right = nested(list(bits), right);
    Some(Expr::apps(
        proof,
        [drop4(actual_left), drop4(actual_right)].into_iter().chain(bits[..4].iter().cloned()),
    ))
}
/// Independently render the two exact fixed-width arithmetic goals.
pub(crate) fn restoration_goal(bits: &[Expr; 64], sub: bool) -> Expr {
    let sp = list(bits);
    let left = if sub {
        add(add(sp.clone(), bv_not(constant(16)), b(true)), constant(16), b(false))
    } else {
        nested(sp.clone(), &[-16, 16])
    };
    eq(lb(), left, sp)
}
