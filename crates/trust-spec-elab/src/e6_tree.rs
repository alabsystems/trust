//! The E6-ONLY TREE producer — increments I3′ and I4′ of the E6 admission
//! expansion (`docs/design-notes/2026-09-28-e6-admission-expansion.md` §5
//! rule 3): mint the defining equation of a `bool` connective tree or a value
//! decision tree the compiler-side reader
//! (`trust_types::e6_expr::read_e6_tree`) read.
//!
//! The term is built as kernel [`Expr`]s DIRECTLY — never printed to Rust and
//! re-parsed (the frozen [`crate::admit_expr_function`] route puts a printer
//! and operator precedence into the base, design note H9) — and handed to
//! `add_decl`, which re-types it at `d₀ → … → dₙ₋₁ → Bool`.
//!
//! # The images (design note §4 rows 10 and 11)
//!
//! | tree node | image |
//! |---|---|
//! | `!x`, `x && y`, `x \|\| y`, `x ^ y` | `Bool.not`, `Bool.and`, `Bool.or`, `Bool.xor` — the spellings the clause elaborator emits for `!`, `&&`, `\|\|` |
//! | `l == r`, `l != r` over `bool` | `Decidable.decide (Eq Bool l r) (instDecidableEqBool l r)`, under `Bool.not` for `!=` — the I1′ image |
//! | `l ⊲ r` over `uN`/`iN` | `Decidable.decide p i`, `(p, i)` from the frozen [`crate::decidable_comparison`] (read-only), under `Bool.not` for `!=` — the frozen comparison mint's image |
//! | `if c { t } else { e }` (I4′) | `ite.{1} C p i ⟦t⟧ ⟦e⟧` — Clean's own `if … then … else …`. For a comparison `c` the `(p, i)` pair is the comparison's, as the frozen select mint's is (a `!=` test is its `==` with the arms swapped; a `!` test likewise); for any other `bool` `c` it is `(Eq Bool c true, instDecidableEqBool c true)`, which is what an island's `if c then …` over a `Bool` elaborates to — never `cond` (design note §4 rows 7 and 12: `cond` is not defeq to an island `if`) |
//!
//! A literal takes the SAME elaboration a clause gives it (`Domain::zero`,
//! `numeral`, `negative_numeral`), range-checked against its carrier.
//!
//! # FAITHFULNESS
//!
//! Each node's image is its Rust meaning on every input: `Bool.and`/`or`/
//! `not`/`xor` ARE `&&`/`||`/`!`/`^` on two pure, total `bool` values (the
//! reader admits nothing effectful or partial below a connective, so a
//! short-circuit changes only WHETHER an operand is evaluated); `decide
//! (a = b)` is `bool` equality; and the comparison images are the ones the
//! frozen comparison mint already rests on (unsigned: the carrier's own
//! order instance; signed: the sign-flip order keys). The differential
//! harness (`crates/trust-certify/tests/e6_differential.rs`) executes every
//! fixture shape's image against the Rust function — on every input up to 16
//! bits, on a fixed boundary-plus-spread sample at `u32`..`i128` — with a row
//! for each carrier this producer mints.
//!
//! What this module does NOT decide: an ORDERING over `bool` has no image
//! here (review H1) — a `Cmp` over `Bool` with `Lt`/`Le` is refused, never
//! given the equality image.

use clean_kernel::expr::BinderInfo;
use clean_kernel::{Declaration, Environment, Expr, Level, Name};

use crate::{Admission, DeclaredCarriers, Domain, SelectCmp};

/// The comparison an [`E6TreeTerm::Cmp`] decides. The compiler-side twin is
/// `trust_types::e6_expr::E6Cmp`; `>`/`>=` arrive operand-swapped.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum E6TreeCmp {
    /// `==`.
    Eq,
    /// `!=`.
    Ne,
    /// `<`.
    Lt,
    /// `<=`.
    Le,
}

/// The fixed-width arithmetic operations admitted by the E6 tree reader.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum E6TreeArith {
    /// Addition modulo 2^n.
    Add,
    /// Subtraction modulo 2^n.
    Sub,
    /// Multiplication modulo 2^n.
    Mul,
}

/// A term the E6-only tree reader read, over the function's parameters. The
/// compiler-side twin is `trust_types::e6_expr::E6Term`; this producer keeps
/// its own vocabulary independently of the source-import bridge (the same boundary
/// [`crate::CmpOperand`] keeps).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum E6TreeTerm {
    /// A 0-based source parameter.
    Param(usize),
    /// A `bool` literal.
    Bool(bool),
    /// An integer literal, at the carrier of its position.
    Int(i128),
    /// Fixed-width wrapping arithmetic, using the domain's exact modular image.
    Arith { op: E6TreeArith, left: Box<E6TreeTerm>, right: Box<E6TreeTerm> },
    /// Overflow of exact arithmetic at `domain`; checked arithmetic returns
    /// None precisely when this predicate is true.
    Overflow { op: E6TreeArith, domain: Domain, left: Box<E6TreeTerm>, right: Box<E6TreeTerm> },
    /// `!x`.
    Not(Box<E6TreeTerm>),
    /// `x && y`.
    And(Box<E6TreeTerm>, Box<E6TreeTerm>),
    /// `x || y`.
    Or(Box<E6TreeTerm>, Box<E6TreeTerm>),
    /// `x ^ y`.
    Xor(Box<E6TreeTerm>, Box<E6TreeTerm>),
    /// `left ⊲ right`, both at `domain`.
    Cmp {
        /// The comparison.
        op: E6TreeCmp,
        /// The operands' carrier.
        domain: Domain,
        /// Left operand.
        left: Box<E6TreeTerm>,
        /// Right operand.
        right: Box<E6TreeTerm>,
    },
    /// `if cond { then } else { els }` (I4′), both arms at the carrier of the
    /// position.
    Ite {
        /// The `bool` decided on.
        cond: Box<E6TreeTerm>,
        /// The value when `cond` holds.
        then: Box<E6TreeTerm>,
        /// The value otherwise.
        els: Box<E6TreeTerm>,
    },
}

struct Renderer<'a> {
    param_domains: &'a [Domain],
}

fn app<I>(name: &str, args: I) -> Expr
where
    I: IntoIterator<Item = Expr>,
{
    Expr::apps(Expr::const_(Name::interned(name), vec![]), args)
}

impl Renderer<'_> {
    fn n(&self) -> usize {
        self.param_domains.len()
    }

    /// The image of `t` at carrier `dom`, or why it has none.
    fn render(&self, t: &E6TreeTerm, dom: &Domain) -> Result<Expr, String> {
        match t {
            E6TreeTerm::Param(i) => {
                let have = self.param_domains.get(*i).ok_or_else(|| {
                    format!("tree parameter {i} out of range for a {}-parameter function", self.n())
                })?;
                if have != dom {
                    return Err(format!(
                        "tree parameter {i} has carrier `{}` where `{}` is needed",
                        have.rust_name(),
                        dom.rust_name()
                    ));
                }
                Ok(Expr::bvar(crate::de_bruijn_index(self.n(), *i, 0)?))
            }
            E6TreeTerm::Bool(b) => dom.bool_lit(*b),
            E6TreeTerm::Int(v) => {
                if !matches!(dom, Domain::Machine(_) | Domain::Signed(_)) {
                    return Err(format!(
                        "an integer literal has no image at `{}` in a tree",
                        dom.rust_name()
                    ));
                }
                match v.cmp(&0) {
                    std::cmp::Ordering::Equal => Ok(dom.zero()),
                    std::cmp::Ordering::Greater => dom.numeral(v.unsigned_abs()),
                    std::cmp::Ordering::Less => dom.negative_numeral(v.unsigned_abs()),
                }
            }
            E6TreeTerm::Arith { op, left, right } => {
                if !matches!(dom, Domain::Machine(_) | Domain::Signed(_)) {
                    return Err("E6 arithmetic needs a fixed-width integer carrier".into());
                }
                let which = match op {
                    E6TreeArith::Add => "add",
                    E6TreeArith::Sub => "sub",
                    E6TreeArith::Mul => "mul",
                };
                dom.arithmetic(which, self.render(left, dom)?, self.render(right, dom)?)
            }
            E6TreeTerm::Overflow { op, domain, left, right } => {
                self.need_bool(dom, "arithmetic overflow")?;
                let l = self.render(left, domain)?;
                let r = self.render(right, domain)?;
                match domain {
                    Domain::Machine(width) => {
                        let to_nat_const = width.to_nat_const();
                        let to_nat = |x| app(to_nat_const, [x]);
                        let (l, r) = (to_nat(l), to_nat(r));
                        Ok(if *op == E6TreeArith::Sub {
                            app("Nat.blt", [l, r])
                        } else {
                            let nat_op = match op {
                                E6TreeArith::Add => "Nat.add",
                                E6TreeArith::Sub => "Nat.sub",
                                E6TreeArith::Mul => "Nat.mul",
                            };
                            app(
                                "Bool.not",
                                [app(
                                    "Nat.ble",
                                    [
                                        app(nat_op, [l, r]),
                                        crate::kernel_nat_lit(width.max_value()),
                                    ],
                                )],
                            )
                        })
                    }
                    Domain::Signed(width) => {
                        let to_int_const = width.signed_lift_const();
                        let to_int = |x| app(to_int_const, [x]);
                        let int_op = match op {
                            E6TreeArith::Add => "Int.add",
                            E6TreeArith::Sub => "Int.sub",
                            E6TreeArith::Mul => "Int.mul",
                        };
                        let exact = app(int_op, [to_int(l), to_int(r)]);
                        Ok(app(
                            "Bool.not",
                            [app(width.signed_fits_const(), [exact])],
                        ))
                    }
                    _ => Err("checked arithmetic needs a fixed-width integer carrier".into()),
                }
            }
            E6TreeTerm::Not(x) => {
                self.need_bool(dom, "`!`")?;
                Ok(app("Bool.not", [self.render(x, &Domain::Bool)?]))
            }
            E6TreeTerm::And(x, y) | E6TreeTerm::Or(x, y) | E6TreeTerm::Xor(x, y) => {
                let name = match t {
                    E6TreeTerm::And(..) => "Bool.and",
                    E6TreeTerm::Or(..) => "Bool.or",
                    _ => "Bool.xor",
                };
                self.need_bool(dom, name)?;
                Ok(app(name, [self.render(x, &Domain::Bool)?, self.render(y, &Domain::Bool)?]))
            }
            E6TreeTerm::Cmp { op, domain, left, right } => {
                self.need_bool(dom, "a comparison")?;
                let decided = self.decide(*op, domain, left, right)?;
                Ok(if *op == E6TreeCmp::Ne { app("Bool.not", [decided]) } else { decided })
            }
            E6TreeTerm::Ite { cond, then, els } => {
                // Exhaustive: a new carrier must say whether `ite` over it is
                // faithful, not inherit an answer from a wildcard.
                let carrier_ok = match dom {
                    Domain::Bool | Domain::Machine(_) | Domain::Signed(_) => true,
                    Domain::Nat
                    | Domain::Int
                    | Domain::U128
                    | Domain::USize(_)
                    | Domain::ISize(_)
                    | Domain::OptionSigned(_)
                    | Domain::RegisteredAdt(_) => false,
                };
                if !carrier_ok {
                    return Err(format!("a decision has no E6 image at `{}`", dom.rust_name()));
                }
                let (prop, inst, swapped) = self.condition(cond, false)?;
                let (t, e) = (self.render(then, dom)?, self.render(els, dom)?);
                let (t, e) = if swapped { (e, t) } else { (t, e) };
                Ok(Expr::apps(
                    Expr::const_(Name::interned("ite"), vec![Level::succ(Level::zero())]),
                    [dom.ty(), prop, inst, t, e],
                ))
            }
        }
    }

    /// The `(proposition, Decidable instance)` an `ite` on `cond` scrutinizes,
    /// and whether its arms must be SWAPPED (`!c` and `a != b` decide `c` and
    /// `a == b` with the arms exchanged — the same function).
    fn condition(&self, cond: &E6TreeTerm, swapped: bool) -> Result<(Expr, Expr, bool), String> {
        match cond {
            E6TreeTerm::Not(c) => self.condition(c, !swapped),
            E6TreeTerm::Cmp { op, domain, left, right } => {
                let (prop, inst) = self.decision(*op, domain, left, right)?;
                Ok((prop, inst, swapped ^ (*op == E6TreeCmp::Ne)))
            }
            other => {
                let c = self.render(other, &Domain::Bool)?;
                let t = Domain::Bool.bool_lit(true)?;
                let prop = Expr::apps(
                    Expr::const_(Name::interned("Eq"), vec![Level::succ(Level::zero())]),
                    [Domain::Bool.ty(), c.clone(), t.clone()],
                );
                Ok((prop, app("instDecidableEqBool", [c, t]), swapped))
            }
        }
    }

    fn need_bool(&self, dom: &Domain, what: &str) -> Result<(), String> {
        if *dom == Domain::Bool {
            Ok(())
        } else {
            Err(format!("{what} is `bool`-valued, used at `{}`", dom.rust_name()))
        }
    }

    /// `Decidable.decide p i` for `left ⊲ right` at `domain`, with `!=`
    /// decided as `==` (the caller negates it).
    fn decide(
        &self,
        op: E6TreeCmp,
        domain: &Domain,
        left: &E6TreeTerm,
        right: &E6TreeTerm,
    ) -> Result<Expr, String> {
        let (prop, inst) = self.decision(op, domain, left, right)?;
        Ok(app("Decidable.decide", [prop, inst]))
    }

    /// The `(proposition, Decidable instance)` pair `left ⊲ right` decides,
    /// `!=` as `==`.
    fn decision(
        &self,
        op: E6TreeCmp,
        domain: &Domain,
        left: &E6TreeTerm,
        right: &E6TreeTerm,
    ) -> Result<(Expr, Expr), String> {
        match domain {
            Domain::Bool => {
                // H1: an ordering over `bool` has no image, never `==`'s.
                if !matches!(op, E6TreeCmp::Eq | E6TreeCmp::Ne) {
                    return Err("an ordering over `bool` has no E6 image".to_owned());
                }
                let l = self.render(left, &Domain::Bool)?;
                let r = self.render(right, &Domain::Bool)?;
                let bool_ty = Domain::Bool.ty();
                let prop = Expr::apps(
                    Expr::const_(Name::interned("Eq"), vec![Level::succ(Level::zero())]),
                    [bool_ty, l.clone(), r.clone()],
                );
                Ok((prop, app("instDecidableEqBool", [l, r])))
            }
            Domain::Machine(_) | Domain::Signed(_) => {
                fn operand(t: &E6TreeTerm) -> bool {
                    match t {
                        E6TreeTerm::Param(_) | E6TreeTerm::Int(_) => true,
                        E6TreeTerm::Arith { left, right, .. } => operand(left) && operand(right),
                        _ => false,
                    }
                }
                if !operand(left) || !operand(right) {
                    return Err(
                        "an integer comparison operand is outside the arithmetic fragment".into()
                    );
                }
                fn has_parameter(t: &E6TreeTerm) -> bool {
                    match t {
                        E6TreeTerm::Param(_) => true,
                        E6TreeTerm::Arith { left, right, .. } => {
                            has_parameter(left) || has_parameter(right)
                        }
                        _ => false,
                    }
                }
                if !has_parameter(left) && !has_parameter(right) {
                    return Err("an integer comparison needs a parameter operand".into());
                }
                let cmp = match op {
                    E6TreeCmp::Eq | E6TreeCmp::Ne => SelectCmp::Eq,
                    E6TreeCmp::Lt => SelectCmp::Lt,
                    E6TreeCmp::Le => SelectCmp::Le,
                };
                let l = self.render(left, domain)?;
                let r = self.render(right, domain)?;
                crate::decidable_comparison(domain, cmp, l, r)
            }
            other => Err(format!(
                "a comparison over `{}` has no E6 tree image (the comparison images decide over \
                 `bool`, a machine-integer or a signed-integer carrier)",
                other.rust_name()
            )),
        }
    }
}

/// Mint an E6 [`Admission`] for a function whose body the E6-only TREE reader
/// read as `term` (E6 admission expansion I3′, I4′): `fun p₀ … pₙ₋₁ =>
/// ⟦term⟧`, each parameter bound at its OWN carrier (`param_domains`, so a
/// tree over `bool` flags and `u8` comparisons is one mint), returning `ret`.
///
/// Fail-closed: `ret` must be `Bool`, a machine-integer or a signed-integer
/// carrier; every node must type at the carrier its position needs
/// ([`E6TreeTerm`]'s docs);
/// an ordering over `bool`, a computed operand outside the arithmetic fragment, a literal
/// outside its carrier, or a carrier with no comparison image refuses; and
/// `add_decl` FULL-KERNEL-CHECKS the definition.
///
/// # Errors
///
/// Why no image was minted.
pub fn admit_e6_tree_function(
    env: &mut Environment,
    kernel_const: &str,
    param_domains: &[Domain],
    ret: &Domain,
    term: &E6TreeTerm,
) -> Result<Admission, String> {
    if !matches!(ret, Domain::Bool | Domain::Machine(_) | Domain::Signed(_)) {
        return Err(format!(
            "an E6 tree returns `bool`, `uN` or `iN`; this function returns `{}`",
            ret.rust_name()
        ));
    }
    fn seed(env: &mut Environment, term: &E6TreeTerm) -> Result<(), String> {
        match term {
            E6TreeTerm::Overflow { domain: Domain::Signed(width), left, right, .. } => {
                crate::seed_checked_model(env, *width)?;
                seed(env, left)?;
                seed(env, right)
            }
            E6TreeTerm::Overflow { left, right, .. }
            | E6TreeTerm::Arith { left, right, .. }
            | E6TreeTerm::Cmp { left, right, .. }
            | E6TreeTerm::And(left, right)
            | E6TreeTerm::Or(left, right)
            | E6TreeTerm::Xor(left, right) => {
                seed(env, left)?;
                seed(env, right)
            }
            E6TreeTerm::Not(x) => seed(env, x),
            E6TreeTerm::Ite { cond, then, els } => {
                seed(env, cond)?;
                seed(env, then)?;
                seed(env, els)
            }
            _ => Ok(()),
        }
    }
    seed(env, term)?;
    let renderer = Renderer { param_domains };
    let body = renderer.render(term, ret)?;
    let lam = param_domains
        .iter()
        .rev()
        .fold(body, |acc, pd| Expr::lam(BinderInfo::Default, pd.ty(), acc));
    let arrow_ty = param_domains.iter().rev().fold(ret.ty(), |acc, pd| Expr::arrow(pd.ty(), acc));
    env.add_decl(Declaration::Definition {
        name: Name::from_string(kernel_const),
        level_params: vec![],
        type_: arrow_ty,
        value: lam,
        is_reducible: true,
    })
    .map_err(|e| format!("kernel rejected the tree defining equation: {e:?}"))?;
    Ok(Admission::reflected(kernel_const, param_domains.len()).with_declared_signature(
        Some(ret.clone()),
        Some(DeclaredCarriers::of_domains(param_domains, ret)),
    ))
}
