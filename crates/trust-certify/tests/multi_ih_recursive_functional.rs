// trust-certify: MULTI-IH recursive datatype-function induction, kernel-checked.
//
// The sibling `level_recursive_functional` demonstrates the induction discharge
// for a UNARY-recursive constructor (`Level.succ (pred)` — ONE recursive field,
// ONE inductive hypothesis, closed by a single `congrArg`). The named next step
// toward grounding the kernel's own `infer_type <-> whnf <-> is_def_eq` cluster
// (see `recursive_datatype_functional.rs` HONEST SCOPE) is MULTI-IH constructors
// — the shape of `Level.Max`/`Level.IMax`, whose two recursive fields each carry
// their own inductive hypothesis.
//
// THIS test hand-builds that multi-IH discharge and kernel-checks it, so the
// capability is demonstrated sound before the vcgen auto-generator mechanizes it:
//
//   1. registers `BTree = leaf | node (left : BTree) (right : BTree)` via
//      `add_inductive` — a TWO-recursive-field constructor, so `BTree.rec`'s
//      node minor is `(a b : BTree) -> motive a -> motive b -> motive (node a b)`
//      (TWO inductive hypotheses);
//   2. registers a RECURSIVE model `rebuild : BTree -> BTree` DEFINED BY
//      `BTree.rec` (leaf -> leaf, node a b -> node (rebuild a) (rebuild b));
//   3. proves the functional fact `forall t, Eq BTree (rebuild t) t` by a
//      `BTree.rec` term whose node minor consumes BOTH IHs `iha : rebuild a = a`
//      and `ihb : rebuild b = b`, chaining them through two `congrArg`s and an
//      `Eq.trans` — a genuine TWO-IH induction the clean kernel re-checks.
//
// NO MASQUERADE (both IHs are load-bearing, kernel-witnessed):
//   * the refl-only pseudo-proof `fun t => Eq.refl BTree (rebuild t)` of the TRUE
//     goal is REJECTED (`rebuild t` is stuck on the free `t`; only the `BTree.rec`
//     term carrying both IHs closes it) — `rebuild_id_requires_induction`;
//   * the per-constructor node STEP `rebuild (node a b) = node (rebuild a)
//     (rebuild b)` IS definitional (iota), closed by `Eq.refl` WITHOUT induction
//     — `rebuild_node_step_is_definitional` — confirming the kernel's reduction
//     genuinely fires, so the `rebuild t = t` obligation is a real (two-IH)
//     induction, not a reduction artifact.
//
// SOUNDNESS: env = `init_eq` (Eq/Eq.refl/Eq.trans/congrArg) + the reconstructed
// `BTree` inductive + the `rebuild` definition (no smuggled axioms), closed
// context; every fact is `TypeChecker::check_type`-accepted (or REJECTED for the
// negative controls). This is a MODEL-LEVEL CIC demonstration over a reconstructed
// datatype — the recursion PRIMITIVE (multi-IH), not the literal Rust kernel fns.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use clean_kernel::name::Name;
use clean_kernel::{
    BinderInfo, Constructor, Declaration, Environment, Expr, InductiveDecl, InductiveType, Level,
    LocalContext, TypeChecker,
};

// --- kernel-term helpers (raw CIC Expr, de Bruijn) --------------------------

fn btree_ty() -> Expr {
    Expr::const_(Name::from_string("BTree"), Vec::new())
}
fn btree_leaf() -> Expr {
    Expr::const_(Name::from_string("BTree.leaf"), Vec::new())
}
fn btree_node(l: Expr, r: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("BTree.node"), Vec::new()), [l, r])
}
fn rebuild(x: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("rebuild"), Vec::new()), x)
}

/// `BTree : Type 0 = Sort 1`, so Eq/Eq.refl/congrArg/Eq.trans over `BTree` take
/// `u = 1`.
fn u1() -> Level {
    Level::succ(Level::zero())
}

/// `Eq.{1} BTree a b`.
fn eq_btree(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Eq"), vec![u1()]), [btree_ty(), a, b])
}

/// `inductive BTree : Type where | leaf | node (left : BTree) (right : BTree)` —
/// the two-recursive-field constructor whose recursor minor carries TWO IHs.
fn btree_inductive() -> InductiveDecl {
    let btree = Name::from_string("BTree");
    let btree_ref = Expr::const_(btree.clone(), vec![]);
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: btree,
            type_: Expr::type_(),
            constructors: vec![
                Constructor { name: Name::from_string("BTree.leaf"), type_: btree_ref.clone() },
                Constructor {
                    name: Name::from_string("BTree.node"),
                    // BTree -> BTree -> BTree
                    type_: Expr::pi(
                        BinderInfo::Default,
                        btree_ref.clone(),
                        Expr::pi(BinderInfo::Default, btree_ref.clone(), btree_ref),
                    ),
                },
            ],
        }],
    }
}

/// The RECURSIVE model `rebuild : BTree -> BTree`, DEFINED BY `BTree.rec.{1}`:
/// `fun (t : BTree) => BTree.rec (fun _ => BTree) leaf
///     (fun (a b : BTree) (iha ihb : BTree) => node iha ihb) t`.
/// leaf -> leaf, node a b -> node (rebuild a) (rebuild b).
fn rebuild_value() -> Expr {
    // motive := fun _:BTree => BTree
    let motive = Expr::lam(BinderInfo::Default, btree_ty(), btree_ty());
    let leaf_case = btree_leaf();
    // node minor (fields-then-IHs): fun (a b : BTree) (iha ihb : BTree) => node iha ihb
    // under [a,b,iha,ihb]: iha = #1, ihb = #0.
    let node_case = Expr::lam(
        BinderInfo::Default,
        btree_ty(),
        Expr::lam(
            BinderInfo::Default,
            btree_ty(),
            Expr::lam(
                BinderInfo::Default,
                btree_ty(),
                Expr::lam(
                    BinderInfo::Default,
                    btree_ty(),
                    btree_node(Expr::bvar(1), Expr::bvar(0)),
                ),
            ),
        ),
    );
    let rec_app = Expr::apps(
        Expr::const_(Name::from_string("BTree.rec"), vec![u1()]),
        [motive, leaf_case, node_case, Expr::bvar(0)],
    );
    Expr::lam(BinderInfo::Default, btree_ty(), rec_app)
}

fn rebuild_type() -> Expr {
    Expr::pi(BinderInfo::Default, btree_ty(), btree_ty())
}

/// Goal: `forall (t : BTree), Eq BTree (rebuild t) t`.
fn rebuild_id_goal() -> Expr {
    Expr::pi(BinderInfo::Default, btree_ty(), eq_btree(rebuild(Expr::bvar(0)), Expr::bvar(0)))
}

/// The genuinely inductive TWO-IH proof, by `BTree.rec.{0}` (Prop motive):
/// node minor = `Eq.trans (congrArg (fun x => node x RB) iha)
///                        (congrArg (fun y => node a y) ihb)`
/// where RA = rebuild a, RB = rebuild b.
fn rebuild_id_proof() -> Expr {
    // motive := fun (x : BTree) => Eq BTree (rebuild x) x   (x = #0)
    let motive =
        Expr::lam(BinderInfo::Default, btree_ty(), eq_btree(rebuild(Expr::bvar(0)), Expr::bvar(0)));

    // base (leaf) : Eq.refl.{1} BTree BTree.leaf  (: Eq BTree (rebuild leaf) leaf by iota)
    let base = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![u1()]),
        [btree_ty(), btree_leaf()],
    );

    // IH binder types (under the minor's preceding binders):
    //   iha : Eq BTree (rebuild a) a   — written under [a,b], a = #1
    let iha_ty = eq_btree(rebuild(Expr::bvar(1)), Expr::bvar(1));
    //   ihb : Eq BTree (rebuild b) b   — written under [a,b,iha], b = #1
    let ihb_ty = eq_btree(rebuild(Expr::bvar(1)), Expr::bvar(1));

    // node minor BODY under [a,b,iha,ihb]: a=#3, b=#2, iha=#1, ihb=#0.
    // f1 := fun (x : BTree) => node x (rebuild b)   — under one more binder, b = #3.
    let f1 = Expr::lam(
        BinderInfo::Default,
        btree_ty(),
        btree_node(Expr::bvar(0), rebuild(Expr::bvar(3))),
    );
    // congrArg.{1,1} BTree BTree (rebuild a) a f1 iha : node (rebuild a) (rebuild b) = node a (rebuild b)
    let congr1 = Expr::apps(
        Expr::const_(Name::from_string("congrArg"), vec![u1(), u1()]),
        [
            btree_ty(),            // {α}
            btree_ty(),            // {β}
            rebuild(Expr::bvar(3)), // {a₁} = rebuild a
            Expr::bvar(3),          // {a₂} = a
            f1,                     // f
            Expr::bvar(1),          // h = iha
        ],
    );
    // f2 := fun (y : BTree) => node a y   — under one more binder, a = #4.
    let f2 = Expr::lam(
        BinderInfo::Default,
        btree_ty(),
        btree_node(Expr::bvar(4), Expr::bvar(0)),
    );
    // congrArg.{1,1} BTree BTree (rebuild b) b f2 ihb : node a (rebuild b) = node a b
    let congr2 = Expr::apps(
        Expr::const_(Name::from_string("congrArg"), vec![u1(), u1()]),
        [
            btree_ty(),
            btree_ty(),
            rebuild(Expr::bvar(2)), // {a₁} = rebuild b
            Expr::bvar(2),          // {a₂} = b
            f2,
            Expr::bvar(0),          // h = ihb
        ],
    );
    // Eq.trans.{1} BTree (node RA RB) (node a RB) (node a b) congr1 congr2
    let node_a_rb = btree_node(Expr::bvar(3), rebuild(Expr::bvar(2)));
    let node_ra_rb = btree_node(rebuild(Expr::bvar(3)), rebuild(Expr::bvar(2)));
    let node_a_b = btree_node(Expr::bvar(3), Expr::bvar(2));
    let trans = Expr::apps(
        Expr::const_(Name::from_string("Eq.trans"), vec![u1()]),
        [btree_ty(), node_ra_rb, node_a_rb, node_a_b, congr1, congr2],
    );

    let node_case = Expr::lam(
        BinderInfo::Default,
        btree_ty(), // a
        Expr::lam(
            BinderInfo::Default,
            btree_ty(), // b
            Expr::lam(
                BinderInfo::Default,
                iha_ty, // iha
                Expr::lam(BinderInfo::Default, ihb_ty, trans),
            ),
        ),
    );

    let rec_app = Expr::apps(
        Expr::const_(Name::from_string("BTree.rec"), vec![Level::zero()]), // Prop motive => .{0}
        [motive, base, node_case, Expr::bvar(0)],
    );
    Expr::lam(BinderInfo::Default, btree_ty(), rec_app)
}

/// NEGATIVE control: `fun (t : BTree) => Eq.refl BTree (rebuild t)`. Its type is
/// `forall t, Eq BTree (rebuild t) (rebuild t)`, NOT the goal `... (rebuild t) t`
/// (`rebuild t` is stuck on the free `t`). The kernel MUST reject it.
fn rebuild_id_refl_only() -> Expr {
    let refl = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![u1()]),
        [btree_ty(), rebuild(Expr::bvar(0))],
    );
    Expr::lam(BinderInfo::Default, btree_ty(), refl)
}

/// Definitional CONTRAST goal
/// `forall a b, Eq BTree (rebuild (node a b)) (node (rebuild a) (rebuild b))`
/// — TRUE by iota alone, no IH needed.
fn rebuild_node_step_goal() -> Expr {
    // forall (a : BTree) (b : BTree), Eq BTree (rebuild (node a b)) (node (rebuild a) (rebuild b))
    // under [a,b]: a=#1, b=#0.
    let body = eq_btree(
        rebuild(btree_node(Expr::bvar(1), Expr::bvar(0))),
        btree_node(rebuild(Expr::bvar(1)), rebuild(Expr::bvar(0))),
    );
    Expr::pi(
        BinderInfo::Default,
        btree_ty(),
        Expr::pi(BinderInfo::Default, btree_ty(), body),
    )
}

/// `fun a b => Eq.refl BTree (node (rebuild a) (rebuild b))` — closes the
/// definitional contrast WITHOUT induction (rebuild (node a b) reduces by iota).
fn rebuild_node_step_refl_proof() -> Expr {
    // under [a,b]: a=#1, b=#0.
    let refl = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![u1()]),
        [btree_ty(), btree_node(rebuild(Expr::bvar(1)), rebuild(Expr::bvar(0)))],
    );
    Expr::lam(
        BinderInfo::Default,
        btree_ty(),
        Expr::lam(BinderInfo::Default, btree_ty(), refl),
    )
}

fn build_env() -> Environment {
    let mut env = Environment::new();
    env.init_eq().expect("init_eq");
    env.add_inductive(btree_inductive())
        .expect("add BTree inductive (=> BTree.rec)");
    env.add_decl(Declaration::Definition {
        name: Name::from_string("rebuild"),
        level_params: vec![],
        type_: rebuild_type(),
        value: rebuild_value(),
        is_reducible: true,
    })
    .expect("register recursive `rebuild` (kernel type-checks its BTree.rec body)");
    env
}

fn kernel_checks(env: &Environment, term: &Expr, goal: &Expr) -> bool {
    TypeChecker::with_context(env, LocalContext::new())
        .check_type(term, goal)
        .is_ok()
}

// --- the tests --------------------------------------------------------------

/// THE MILESTONE: a genuinely inductive functional fact about a RECURSIVE model
/// over a datatype with a TWO-recursive-field constructor is kernel-checked via
/// `BTree.rec` carrying and consuming BOTH inductive hypotheses.
#[test]
fn rebuild_id_multi_ih_functional_fact_kernel_checks() {
    let env = build_env();
    assert!(
        kernel_checks(&env, &rebuild_id_proof(), &rebuild_id_goal()),
        "clean kernel must accept the BTree.rec TWO-IH proof of `forall t, rebuild t = t`"
    );
}

/// The fact GENUINELY requires induction: the refl-only pseudo-proof is REJECTED
/// (`rebuild t` is stuck on free `t`; only the two-IH `BTree.rec` term closes it).
#[test]
fn rebuild_id_requires_induction() {
    let env = build_env();
    assert!(
        !kernel_checks(&env, &rebuild_id_refl_only(), &rebuild_id_goal()),
        "Eq.refl alone must NOT type-check `forall t, rebuild t = t` (rebuild t stuck on free t)"
    );
}

/// CONTRAST: the per-constructor node step IS definitional (iota), closed by
/// `Eq.refl` with no induction — confirming the kernel's reduction fires, so the
/// `rebuild t = t` obligation above is a real two-IH induction, not an artifact.
#[test]
fn rebuild_node_step_is_definitional() {
    let env = build_env();
    assert!(
        kernel_checks(&env, &rebuild_node_step_refl_proof(), &rebuild_node_step_goal()),
        "Eq.refl must close the definitional node step `rebuild (node a b) = node (rebuild a) (rebuild b)`"
    );
}
