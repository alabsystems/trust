//! Unit tests of the E6-only TREE reader (I3′). The end-to-end check — a
//! fixture row of every carrier and construct it reads, from real MIR,
//! executed against the Rust body (every input up to 16 bits, a fixed sample
//! above) — is `crates/trust-certify/tests/e6_differential.rs`; these pin the
//! reader's vocabulary and its fail-closed edges on hand-built MIR.

use super::*;
use crate::{AssertMessage, BasicBlock, LocalDecl, Place, SourceSpan, VerifiableBody};

// ---------------------------------------------------------------------------
// A reference evaluator for terms over `bool` and small-integer parameters
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum V {
    B(bool),
    I(i128),
}

fn eval(t: &E6Term, ps: &[V]) -> V {
    let b = |t: &E6Term| match eval(t, ps) {
        V::B(x) => x,
        V::I(_) => panic!("an integer where a bool was expected"),
    };
    match t {
        E6Term::Param(i) => ps[*i],
        E6Term::Bool(x) => V::B(*x),
        E6Term::Int(v) => V::I(*v),
        E6Term::Overflow { .. } | E6Term::Checked { .. } | E6Term::CheckedTag { .. } => {
            panic!("not used by Boolean normalization fixtures")
        }
        E6Term::Arith { op, carrier, left, right } => {
            let (V::I(l), V::I(r)) = (eval(left, ps), eval(right, ps)) else {
                panic!("integer arithmetic");
            };
            let width = match carrier {
                E6Carrier::Unsigned(w) | E6Carrier::Signed(w) => *w,
                _ => panic!("integer carrier"),
            };
            let raw = match op {
                BinOp::Add => l.wrapping_add(r),
                BinOp::Sub => l.wrapping_sub(r),
                BinOp::Mul => l.wrapping_mul(r),
                _ => panic!("arithmetic op"),
            };
            let bits = raw & ((1i128 << width) - 1);
            V::I(if matches!(carrier, E6Carrier::Signed(_)) && bits >= (1i128 << (width - 1)) {
                bits - (1i128 << width)
            } else {
                bits
            })
        }
        E6Term::Not(x) => V::B(!b(x)),
        E6Term::And(x, y) => V::B(b(x) && b(y)),
        E6Term::Or(x, y) => V::B(b(x) || b(y)),
        E6Term::Xor(x, y) => V::B(b(x) ^ b(y)),
        E6Term::Cmp { op, left, right, .. } => {
            let (l, r) = (eval(left, ps), eval(right, ps));
            V::B(match (op, l, r) {
                (E6Cmp::Eq, l, r) => l == r,
                (E6Cmp::Ne, l, r) => l != r,
                (E6Cmp::Lt, V::I(l), V::I(r)) => l < r,
                (E6Cmp::Le, V::I(l), V::I(r)) => l <= r,
                other => panic!("no ordering over {other:?}"),
            })
        }
        E6Term::Ite { cond, then, els } => {
            if b(cond) {
                eval(then, ps)
            } else {
                eval(els, ps)
            }
        }
    }
}

fn bool_inputs(n: usize) -> Vec<Vec<V>> {
    (0..1u32 << n).map(|m| (0..n).map(|i| V::B(m >> i & 1 == 1)).collect()).collect()
}

fn p(i: usize) -> E6Term {
    E6Term::Param(i)
}

/// Every normalization rule is an identity: on every assignment of its three
/// operands (the condition, and the two arm operands where a rule has them),
/// the normalized term and the decision it replaced agree — and each rule
/// really fires (the result is not left a decision).
#[test]
fn normalization_rules_are_identities() {
    let (c, x, e, y) = (p(0), p(1), p(2), p(3));
    let t = || E6Term::Bool(true);
    let f = || E6Term::Bool(false);
    let or = |a, b| E6Term::or(a, b);
    let and = |a, b| E6Term::and(a, b);
    let cases = [
        E6Term::ite(c.clone(), t(), f()),
        E6Term::ite(c.clone(), f(), t()),
        E6Term::ite(c.clone(), t(), e.clone()),
        E6Term::ite(c.clone(), x.clone(), f()),
        E6Term::ite(c.clone(), f(), e.clone()),
        E6Term::ite(c.clone(), x.clone(), t()),
        E6Term::ite(c.clone(), or(x.clone(), e.clone()), e.clone()),
        E6Term::ite(c.clone(), e.clone(), and(x.clone(), e.clone())),
        E6Term::ite(c.clone(), e.clone(), or(x.clone(), e.clone())),
        E6Term::ite(c.clone(), and(x.clone(), e.clone()), e.clone()),
        // The four spine rules with a two-operand prefix.
        E6Term::ite(c.clone(), or(x.clone(), or(y.clone(), e.clone())), e.clone()),
        E6Term::ite(c.clone(), e.clone(), and(x.clone(), and(y.clone(), e.clone()))),
        E6Term::ite(c.clone(), e.clone(), or(x.clone(), or(y.clone(), e.clone()))),
        E6Term::ite(c.clone(), and(x.clone(), and(y.clone(), e.clone())), e.clone()),
        // Left-nested chains are re-nested to the right.
        and(and(c.clone(), x.clone()), and(e.clone(), y.clone())),
        or(or(c.clone(), x.clone()), e.clone()),
    ];
    for case in cases {
        let normal = normalize_bool(case.clone());
        assert!(!normal.has_ite(), "{case:?} stayed a decision: {normal:?}");
        assert!(right_nested(&normal), "{normal:?} is not right-nested");
        for input in bool_inputs(4) {
            assert_eq!(eval(&normal, &input), eval(&case, &input), "{case:?} at {input:?}");
        }
    }
    // A decision whose arms are not literals and share no operand stays one.
    let kept = E6Term::ite(c, x, e);
    assert_eq!(normalize_bool(kept.clone()), kept);
}

/// No `&&` (`||`) node has an `&&` (`||`) as its LEFT operand.
fn right_nested(t: &E6Term) -> bool {
    match t {
        E6Term::And(x, y) => !matches!(**x, E6Term::And(..)) && right_nested(x) && right_nested(y),
        E6Term::Or(x, y) => !matches!(**x, E6Term::Or(..)) && right_nested(x) && right_nested(y),
        E6Term::Not(x) => right_nested(x),
        E6Term::Xor(x, y) => right_nested(x) && right_nested(y),
        E6Term::Checked { value, overflow, .. } => right_nested(value) && right_nested(overflow),
        E6Term::CheckedTag { overflow, .. } => right_nested(overflow),
        E6Term::Overflow { left, right, .. }
        | E6Term::Arith { left, right, .. }
        | E6Term::Cmp { left, right, .. } => right_nested(left) && right_nested(right),
        E6Term::Ite { cond, then, els } => {
            right_nested(cond) && right_nested(then) && right_nested(els)
        }
        _ => true,
    }
}

/// The normalization is applied BOTTOM-UP and repeatedly through the tree:
/// every decision tree over three `bool` parameters whose leaves are
/// parameters and literals normalizes to a term with the same value on every
/// input (a brute-force sweep over all such trees of depth two).
#[test]
fn normalization_preserves_every_small_tree() {
    let mut leaves = vec![E6Term::Bool(true), E6Term::Bool(false)];
    leaves.extend((0..3).map(p));
    let mut depth1 = leaves.clone();
    for c in 0..3 {
        for a in &leaves {
            for b in &leaves {
                depth1.push(E6Term::ite(p(c), a.clone(), b.clone()));
            }
        }
    }
    let mut checked = 0;
    for c in 0..3 {
        for a in &depth1 {
            for b in &depth1 {
                let tree = E6Term::ite(p(c), a.clone(), b.clone());
                let normal = normalize_bool(tree.clone());
                assert!(right_nested(&normal), "{normal:?} is not right-nested");
                for input in bool_inputs(3) {
                    assert_eq!(eval(&normal, &input), eval(&tree, &input), "{tree:?} at {input:?}");
                }
                checked += 1;
            }
        }
    }
    assert!(checked > 10_000, "only {checked} trees");
}

// ---------------------------------------------------------------------------
// Hand-built MIR
// ---------------------------------------------------------------------------

fn func(locals: Vec<Ty>, arg_count: usize, blocks: Vec<BasicBlock>) -> VerifiableFunction {
    VerifiableFunction {
        name: "f".into(),
        def_path: "probe::f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            return_ty: locals[0].clone(),
            locals: locals
                .into_iter()
                .enumerate()
                .map(|(index, ty)| LocalDecl { index, ty, name: None })
                .collect(),
            blocks,
            arg_count,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn asn(local: usize, rvalue: Rvalue) -> Statement {
    Statement::Assign { place: Place::local(local), rvalue, span: SourceSpan::default() }
}

fn cp(l: usize) -> Operand {
    Operand::Copy(Place::local(l))
}

fn tru() -> Operand {
    Operand::Constant(ConstValue::Bool(true))
}

fn fls() -> Operand {
    Operand::Constant(ConstValue::Bool(false))
}

fn u8c(v: u128) -> Operand {
    Operand::Constant(ConstValue::Uint(v, 8))
}

fn bb(id: usize, stmts: Vec<Statement>, terminator: Terminator) -> BasicBlock {
    BasicBlock { id: BlockId(id), stmts, terminator }
}

fn goto(t: usize) -> Terminator {
    Terminator::Goto(BlockId(t))
}

/// `switchInt(discr) [0 -> on_false] otherwise on_true`, rustc's two-way
/// branch on a `bool`.
fn branch(discr: Operand, on_false: usize, on_true: usize) -> Terminator {
    Terminator::SwitchInt {
        discr,
        targets: vec![(0, BlockId(on_false))],
        otherwise: BlockId(on_true),
        exhaustive_enum_unreachable: false,
        span: SourceSpan::default(),
    }
}

fn bools(n: usize, temps: usize) -> Vec<Ty> {
    vec![Ty::Bool; 1 + n + temps]
}

fn u8t() -> Ty {
    Ty::Int { width: 8, signed: false }
}

/// `a && b` at the unoptimized level: the short-circuit into a temporary,
/// then `_0 = copy _3`.
fn and_unopt() -> VerifiableFunction {
    func(
        bools(2, 1),
        2,
        vec![
            bb(0, vec![], branch(cp(1), 2, 1)),
            bb(1, vec![asn(3, Rvalue::Use(cp(2)))], goto(3)),
            bb(2, vec![asn(3, Rvalue::Use(fls()))], goto(3)),
            bb(3, vec![asn(0, Rvalue::Use(cp(3)))], Terminator::Return),
        ],
    )
}

#[test]
fn short_circuit_and_or_read_as_connectives() {
    assert_eq!(read_e6_tree(&and_unopt()), Ok(E6Term::and(p(0), p(1))));
    // `a || b || c` at `-O`: both `true` edges share one block; the reading
    // is RIGHT-nested, as MIR's tree and Clean's parse of `||` are.
    let or3 = func(
        bools(3, 0),
        3,
        vec![
            bb(0, vec![], branch(cp(1), 1, 2)),
            bb(1, vec![], branch(cp(2), 3, 2)),
            bb(2, vec![asn(0, Rvalue::Use(tru()))], goto(4)),
            bb(3, vec![asn(0, Rvalue::Use(cp(3)))], goto(4)),
            bb(4, vec![], Terminator::Return),
        ],
    );
    assert_eq!(read_e6_tree(&or3), Ok(E6Term::or(p(0), E6Term::or(p(1), p(2)))));
}

/// ay's `gate_keeps_sat` (`was_sat && (confirmed || !enforce)`) at `-O`,
/// verbatim from the harness dump.
#[test]
fn ays_gate_reads_as_written() {
    let gate = func(
        bools(3, 0),
        3,
        vec![
            bb(0, vec![], branch(cp(1), 2, 1)),
            bb(1, vec![], branch(cp(2), 4, 3)),
            bb(2, vec![asn(0, Rvalue::Use(fls()))], goto(6)),
            bb(3, vec![asn(0, Rvalue::Use(tru()))], goto(5)),
            bb(4, vec![asn(0, Rvalue::UnaryOp(UnOp::Not, cp(3)))], goto(5)),
            bb(5, vec![], goto(6)),
            bb(6, vec![], Terminator::Return),
        ],
    );
    assert_eq!(read_e6_tree(&gate), Ok(E6Term::and(p(0), E6Term::or(p(1), E6Term::not(p(2))))));
}

/// `(a && b) || (!a && c)` at `-O`: the `&&`'s two failure edges share the
/// `||`'s right operand, and the reading recovers the nesting.
#[test]
fn an_and_under_an_or_is_recovered() {
    let mix = func(
        bools(3, 0),
        3,
        vec![
            bb(0, vec![], branch(cp(1), 3, 1)),
            bb(1, vec![], branch(cp(2), 3, 2)),
            bb(2, vec![asn(0, Rvalue::Use(tru()))], goto(7)),
            bb(3, vec![], branch(cp(1), 4, 5)),
            bb(4, vec![asn(0, Rvalue::Use(cp(3)))], goto(6)),
            bb(5, vec![asn(0, Rvalue::Use(fls()))], goto(6)),
            bb(6, vec![], goto(7)),
            bb(7, vec![], Terminator::Return),
        ],
    );
    assert_eq!(
        read_e6_tree(&mix),
        Ok(E6Term::or(E6Term::and(p(0), p(1)), E6Term::and(E6Term::not(p(0)), p(2))))
    );
}

/// Comparison leaves: integer parameters and literals, `>`/`>=` by operand
/// swap, `!=` kept as `Ne`; single-block `&`/`|`/`^`/`!` over `bool`.
#[test]
fn comparison_leaves_and_single_block_connectives() {
    // `a < 10 || b > 200` over u8, `-O`.
    let f = func(
        vec![Ty::Bool, u8t(), u8t(), Ty::Bool],
        2,
        vec![
            bb(
                0,
                vec![asn(3, Rvalue::BinaryOp(BinOp::Lt, cp(1), u8c(10)))],
                branch(Operand::Move(Place::local(3)), 2, 1),
            ),
            bb(1, vec![asn(0, Rvalue::Use(tru()))], goto(3)),
            bb(2, vec![asn(0, Rvalue::BinaryOp(BinOp::Gt, cp(2), u8c(200)))], goto(3)),
            bb(3, vec![], Terminator::Return),
        ],
    );
    let cmp = |op, l, r| E6Term::Cmp {
        op,
        carrier: E6Carrier::Unsigned(8),
        left: Box::new(l),
        right: Box::new(r),
    };
    assert_eq!(
        read_e6_tree(&f),
        Ok(E6Term::or(
            cmp(E6Cmp::Lt, p(0), E6Term::Int(10)),
            cmp(E6Cmp::Lt, E6Term::Int(200), p(1))
        ))
    );
    // `s & i & n` and `acc ^ c`, one block each.
    let band = func(
        bools(3, 1),
        3,
        vec![bb(
            0,
            vec![
                asn(4, Rvalue::BinaryOp(BinOp::BitAnd, cp(1), cp(2))),
                asn(0, Rvalue::BinaryOp(BinOp::BitAnd, Operand::Move(Place::local(4)), cp(3))),
            ],
            Terminator::Return,
        )],
    );
    // Re-nested to the RIGHT, as Clean parses an island's `s && i && n`.
    assert_eq!(read_e6_tree(&band), Ok(E6Term::and(p(0), E6Term::and(p(1), p(2)))));
    let xor = func(
        bools(2, 0),
        2,
        vec![bb(
            0,
            vec![asn(0, Rvalue::BinaryOp(BinOp::BitXor, cp(1), cp(2)))],
            Terminator::Return,
        )],
    );
    assert_eq!(read_e6_tree(&xor), Ok(E6Term::Xor(Box::new(p(0)), Box::new(p(1)))));
    // A signed literal is typed by the other operand: `a == -1` over i8.
    let i8t = Ty::Int { width: 8, signed: true };
    let neg = func(
        vec![Ty::Bool, i8t],
        1,
        vec![bb(
            0,
            vec![asn(
                0,
                Rvalue::BinaryOp(BinOp::Eq, cp(1), Operand::Constant(ConstValue::Int(-1))),
            )],
            Terminator::Return,
        )],
    );
    assert_eq!(
        read_e6_tree(&neg),
        Ok(E6Term::Cmp {
            op: E6Cmp::Eq,
            carrier: E6Carrier::Signed(8),
            left: Box::new(p(0)),
            right: Box::new(E6Term::Int(-1)),
        })
    );
}

/// A short-circuit result computed into a temporary and USED after the join
/// reads as the expression the source wrote: the arms are merged at the
/// switch's immediate post-dominator, not the continuation duplicated into
/// each arm (which would read `!(a && b)` as the De Morgan dual `!a || !b` — the
/// same function, but not the island's spelling).
#[test]
fn a_short_circuit_used_after_its_join_reads_as_written() {
    // `!(a && b)`, unoptimized: `_3 = a && b` by short circuit, then `!_3`.
    let not_and = func(
        bools(2, 1),
        2,
        vec![
            bb(0, vec![], branch(cp(1), 2, 1)),
            bb(1, vec![asn(3, Rvalue::Use(cp(2)))], goto(3)),
            bb(2, vec![asn(3, Rvalue::Use(fls()))], goto(3)),
            bb(
                3,
                vec![asn(0, Rvalue::UnaryOp(UnOp::Not, Operand::Move(Place::local(3))))],
                Terminator::Return,
            ),
        ],
    );
    assert_eq!(read_e6_tree(&not_and), Ok(E6Term::not(E6Term::and(p(0), p(1)))));
    // `let x = a && b; x || a`, `-O`: a second decision on the first's result.
    let let_bound = func(
        bools(2, 2),
        2,
        vec![
            bb(0, vec![], branch(cp(1), 2, 1)),
            bb(1, vec![asn(3, Rvalue::Use(cp(2)))], goto(3)),
            bb(2, vec![asn(3, Rvalue::Use(fls()))], goto(3)),
            bb(3, vec![asn(4, Rvalue::Use(cp(3)))], branch(Operand::Move(Place::local(4)), 5, 4)),
            bb(4, vec![asn(0, Rvalue::Use(tru()))], goto(6)),
            bb(5, vec![asn(0, Rvalue::Use(cp(1)))], goto(6)),
            bb(6, vec![], Terminator::Return),
        ],
    );
    assert_eq!(read_e6_tree(&let_bound), Ok(E6Term::or(E6Term::and(p(0), p(1)), p(0))));
}

/// A temporary REASSIGNED on one path is read with MIR's sequential meaning
/// (the value at the read), and one assigned differently on two paths is
/// read per path — the path unfolding is what makes both exact.
#[test]
fn temporaries_are_read_per_path_and_in_order() {
    let f = func(
        bools(2, 1),
        2,
        vec![
            bb(0, vec![asn(3, Rvalue::Use(cp(1))), asn(3, Rvalue::Use(cp(2)))], goto(1)),
            bb(1, vec![asn(0, Rvalue::UnaryOp(UnOp::Not, cp(3)))], Terminator::Return),
        ],
    );
    assert_eq!(read_e6_tree(&f), Ok(E6Term::not(p(1))));
}

/// The FAIL-CLOSED edges (design note I3′ and I4′ tests): an effectful
/// terminator, a projection, a cycle, an ordering over `bool`, a computed
/// comparison operand, a panic path, and the `match` edges I4′ refuses. A red
/// here after a widening is a soundness incident unless the widening is that
/// increment's, and moves the case.
#[test]
fn the_tree_reader_fails_closed() {
    let refused = |why: &str, f: &VerifiableFunction, says: &str| {
        let err = read_e6_tree(f).expect_err(why);
        assert!(err.contains(says), "{why}: `{err}` does not say `{says}`");
    };
    // An effectful statement: a call.
    let call = func(
        bools(1, 0),
        1,
        vec![
            bb(
                0,
                vec![],
                Terminator::Call {
                    func: "probe::g".into(),
                    args: vec![cp(1)],
                    dest: Place::local(0),
                    target: Some(BlockId(1)),
                    span: SourceSpan::default(),
                    atomic: None,
                    is_foreign: false,
                    is_unsafe_sig: false,
                    unwind: Default::default(),
                    callee_identity: None,
                    callee_key: None,
                },
            ),
            bb(1, vec![], Terminator::Return),
        ],
    );
    refused("a call", &call, "the call to `probe::g`");
    // A projection.
    let proj = func(
        bools(2, 0),
        2,
        vec![bb(
            0,
            vec![asn(0, Rvalue::BinaryOp(BinOp::Eq, Operand::Copy(Place::field(1, 0)), cp(2)))],
            Terminator::Return,
        )],
    );
    refused("a projection", &proj, "projection");
    // A cycle.
    let cycle = func(
        bools(1, 0),
        1,
        vec![
            bb(0, vec![], goto(1)),
            bb(1, vec![], branch(cp(1), 2, 1)),
            bb(2, vec![asn(0, Rvalue::Use(tru()))], Terminator::Return),
        ],
    );
    refused("a cycle", &cycle, "a loop");
    // An ordering over bool, in a tree exactly as alone.
    let lt = func(
        bools(3, 1),
        3,
        vec![
            bb(
                0,
                vec![asn(4, Rvalue::BinaryOp(BinOp::Lt, cp(1), cp(2)))],
                branch(Operand::Move(Place::local(4)), 1, 2),
            ),
            bb(1, vec![asn(0, Rvalue::Use(cp(3)))], goto(3)),
            bb(2, vec![asn(0, Rvalue::Use(tru()))], goto(3)),
            bb(3, vec![], Terminator::Return),
        ],
    );
    refused("an ordering over bool", &lt, "the ordering `<` over `bool`");
    // A comparison whose integer operand is computed.
    let computed = func(
        vec![Ty::Bool, u8t(), u8t(), u8t()],
        2,
        vec![bb(
            0,
            vec![
                asn(3, Rvalue::BinaryOp(BinOp::BitAnd, cp(1), cp(2))),
                asn(0, Rvalue::BinaryOp(BinOp::Eq, Operand::Move(Place::local(3)), u8c(0))),
            ],
            Terminator::Return,
        )],
    );
    refused("a bit operation over u8", &computed, "the bit operation `&` on `u8`");
    // A panic path.
    let assert = func(
        bools(1, 0),
        1,
        vec![
            bb(
                0,
                vec![],
                Terminator::Assert {
                    cond: cp(1),
                    expected: true,
                    msg: AssertMessage::Overflow(BinOp::Add),
                    target: BlockId(1),
                    span: SourceSpan::default(),
                    unwind: Default::default(),
                },
            ),
            bb(1, vec![asn(0, Rvalue::Use(cp(1)))], Terminator::Return),
        ],
    );
    refused("an Assert", &assert, "an `Assert`");
    // Unchecked and checked arithmetic are never read as operations.
    for (rv, says) in [
        (Rvalue::UncheckedBinaryOp(BinOp::Eq, cp(1), cp(2)), "unchecked"),
        (Rvalue::CheckedBinaryOp(BinOp::Eq, cp(1), cp(2)), "overflow-checked"),
    ] {
        let f = func(bools(2, 0), 2, vec![bb(0, vec![asn(0, rv)], Terminator::Return)]);
        refused(says, &f, says);
    }
    // A write to a parameter.
    let write = func(
        bools(2, 0),
        2,
        vec![bb(
            0,
            vec![asn(1, Rvalue::Use(cp(2))), asn(0, Rvalue::Use(cp(1)))],
            Terminator::Return,
        )],
    );
    refused("a parameter write", &write, "a write to the parameter `_1`");
    // A read before any write on this path (bb2 skips the write).
    let unwritten = func(
        bools(1, 1),
        1,
        vec![
            bb(0, vec![], branch(cp(1), 2, 1)),
            bb(1, vec![asn(2, Rvalue::Use(tru()))], goto(2)),
            bb(2, vec![asn(0, Rvalue::Use(cp(2)))], Terminator::Return),
        ],
    );
    refused("a read before a write", &unwritten, "before any write");
    // I4′'s edges: a `match` on a COMPUTED discriminant, on a `char`, one
    // that lists a value twice or one outside the width, and an exhaustive
    // `match` whose `otherwise` is `Unreachable`.
    let sw = |discr: Operand, locals: Vec<Ty>, targets: Vec<(u128, BlockId)>, otherwise: usize| {
        func(
            locals,
            1,
            vec![
                bb(
                    0,
                    vec![],
                    Terminator::SwitchInt {
                        discr,
                        targets,
                        otherwise: BlockId(otherwise),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                ),
                bb(1, vec![asn(0, Rvalue::Use(tru()))], goto(3)),
                bb(2, vec![asn(0, Rvalue::Use(fls()))], goto(3)),
                bb(3, vec![], Terminator::Return),
                bb(4, vec![], Terminator::Unreachable),
            ],
        )
    };
    let mut computed = sw(cp(2), vec![Ty::Bool, u8t(), u8t()], vec![(1, BlockId(1))], 2);
    computed.body.blocks[0].stmts = vec![asn(2, Rvalue::BinaryOp(BinOp::BitAnd, cp(1), u8c(3)))];
    refused("a computed discriminant", &computed, "the bit operation `&` on `u8`");
    let mut copied = sw(cp(2), vec![Ty::Bool, u8t(), u8t()], vec![(1, BlockId(1))], 2);
    copied.body.blocks[0].stmts = vec![asn(2, Rvalue::Use(cp(1)))];
    assert!(read_e6_tree(&copied).is_ok(), "a copy of the parameter IS the parameter");
    refused(
        "a char match",
        &sw(cp(1), vec![Ty::Bool, Ty::Char], vec![(97, BlockId(1))], 2),
        "a read of the parameter `_1` of type `char`",
    );
    refused(
        "a value listed twice",
        &sw(cp(1), vec![Ty::Bool, u8t()], vec![(1, BlockId(1)), (1, BlockId(2))], 2),
        "lists one value twice",
    );
    refused(
        "a value outside u8",
        &sw(cp(1), vec![Ty::Bool, u8t()], vec![(256, BlockId(1))], 2),
        "the `switchInt` value 256, outside `u8`",
    );
    refused(
        "an Unreachable otherwise",
        &sw(cp(1), vec![Ty::Bool, u8t()], vec![(0, BlockId(1)), (1, BlockId(2))], 4),
        "an `Unreachable` terminator",
    );
    // A match on a SELECTED value (`match if c { a } else { 3 } { 1 => …`).
    let on_select = func(
        vec![Ty::Bool, Ty::Bool, u8t(), u8t()],
        2,
        vec![
            bb(0, vec![], branch(cp(1), 2, 1)),
            bb(1, vec![asn(3, Rvalue::Use(cp(2)))], goto(3)),
            bb(2, vec![asn(3, Rvalue::Use(u8c(3)))], goto(3)),
            bb(
                3,
                vec![],
                Terminator::SwitchInt {
                    discr: cp(3),
                    targets: vec![(1, BlockId(4))],
                    otherwise: BlockId(5),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            ),
            bb(4, vec![asn(0, Rvalue::Use(tru()))], goto(6)),
            bb(5, vec![asn(0, Rvalue::Use(fls()))], goto(6)),
            bb(6, vec![], Terminator::Return),
        ],
    );
    refused("a match on a select", &on_select, "a `switchInt` on a computed `u8`");
    // A CONSTANT body is the frozen constant shape's scope, not a tree's.
    refused(
        "a constant bool",
        &func(bools(1, 0), 1, vec![bb(0, vec![asn(0, Rvalue::Use(tru()))], Terminator::Return)]),
        "a constant body",
    );
    // A select over a carrier the reader has none for (`f32`).
    let f32t = Ty::Float { width: 32 };
    refused(
        "a float-valued select",
        &func(
            vec![f32t.clone(), Ty::Bool, f32t.clone(), f32t],
            3,
            vec![
                bb(0, vec![], branch(cp(1), 2, 1)),
                bb(1, vec![asn(0, Rvalue::Use(cp(2)))], goto(3)),
                bb(2, vec![asn(0, Rvalue::Use(cp(3)))], goto(3)),
                bb(3, vec![], Terminator::Return),
            ],
        ),
        "`f32`-valued body",
    );
}

/// I4′: value decisions. A select over parameters and literals at any
/// carrier stays a decision; `>` in a select swaps the OPERANDS and keeps the
/// arms (review H7: `if a > b { a } else { b }` is `if b < a { a } else { b }`);
/// a `match` on `u8` is a chain of `==` tests in target order; an `i8`
/// scrutinee's bit patterns are read back as the negatives they are
/// (`255` is `-1`); and a `matches!` folds to a right-nested `||` of tests.
#[test]
fn value_decisions_read_as_decisions() {
    let cmp =
        |op, carrier, l, r| E6Term::Cmp { op, carrier, left: Box::new(l), right: Box::new(r) };
    // `if c { a } else { b }` over u8 and over bool.
    for ty in [u8t(), Ty::Bool] {
        let sel = func(
            vec![ty.clone(), Ty::Bool, ty.clone(), ty],
            3,
            vec![
                bb(0, vec![], branch(cp(1), 2, 1)),
                bb(1, vec![asn(0, Rvalue::Use(cp(2)))], goto(3)),
                bb(2, vec![asn(0, Rvalue::Use(cp(3)))], goto(3)),
                bb(3, vec![], Terminator::Return),
            ],
        );
        assert_eq!(read_e6_tree(&sel), Ok(E6Term::ite(p(0), p(1), p(2))));
    }
    // `if a > b { a } else { b }`.
    let max = func(
        vec![u8t(), u8t(), u8t(), u8t(), Ty::Bool],
        2,
        vec![
            bb(
                0,
                vec![asn(4, Rvalue::BinaryOp(BinOp::Gt, cp(1), cp(2)))],
                branch(Operand::Move(Place::local(4)), 2, 1),
            ),
            bb(1, vec![asn(3, Rvalue::Use(cp(1)))], goto(3)),
            bb(2, vec![asn(3, Rvalue::Use(cp(2)))], goto(3)),
            bb(3, vec![asn(0, Rvalue::Use(cp(3)))], Terminator::Return),
        ],
    );
    assert_eq!(
        read_e6_tree(&max),
        Ok(E6Term::ite(cmp(E6Cmp::Lt, E6Carrier::Unsigned(8), p(1), p(0)), p(0), p(1)))
    );
    // `match x { 0 => 10, 7 => 30, _ => 0 }` on u8.
    let switch = |discr_ty: Ty, ret: Ty, targets: Vec<(u128, BlockId)>, arms: Vec<Operand>| {
        let mut blocks = vec![bb(
            0,
            vec![],
            Terminator::SwitchInt {
                discr: cp(1),
                targets,
                otherwise: BlockId(arms.len()),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        )];
        let n = arms.len();
        for (i, arm) in arms.into_iter().enumerate() {
            blocks.push(bb(i + 1, vec![asn(0, Rvalue::Use(arm))], goto(n + 1)));
        }
        blocks.push(bb(n + 1, vec![], Terminator::Return));
        func(vec![ret, discr_ty], 1, blocks)
    };
    let m = switch(
        u8t(),
        u8t(),
        vec![(0, BlockId(1)), (7, BlockId(2))],
        vec![u8c(10), u8c(30), u8c(0)],
    );
    let eq8 = |v| cmp(E6Cmp::Eq, E6Carrier::Unsigned(8), p(0), E6Term::Int(v));
    assert_eq!(
        read_e6_tree(&m),
        Ok(E6Term::ite(
            eq8(0),
            E6Term::Int(10),
            E6Term::ite(eq8(7), E6Term::Int(30), E6Term::Int(0))
        ))
    );
    // `match x { -1 => 1, _ => 0 }` on i8: the switch value is the pattern 255.
    let i8t = Ty::Int { width: 8, signed: true };
    let lit = |v: i128| Operand::Constant(ConstValue::Int(v));
    let n = switch(i8t.clone(), i8t, vec![(255, BlockId(1))], vec![lit(1), lit(0)]);
    assert_eq!(
        read_e6_tree(&n),
        Ok(E6Term::ite(
            cmp(E6Cmp::Eq, E6Carrier::Signed(8), p(0), E6Term::Int(-1)),
            E6Term::Int(1),
            E6Term::Int(0)
        ))
    );
    // `matches!(x, 1 | 2 | 7)`: `bool`-literal arms fold to `||`.
    let mt = switch(
        u8t(),
        Ty::Bool,
        vec![(1, BlockId(1)), (2, BlockId(2)), (7, BlockId(3))],
        vec![tru(), tru(), tru(), fls()],
    );
    assert_eq!(read_e6_tree(&mt), Ok(E6Term::or(eq8(1), E6Term::or(eq8(2), eq8(7)))));
}

#[test]
fn tg14_arithmetic_comparisons_and_primitive_identity() {
    for width in [8, 16, 32, 64] {
        for signed in [false, true] {
            let scalar = Ty::Int { width, signed };
            for (op, name) in [
                (BinOp::Add, "wrapping_add"),
                (BinOp::Sub, "wrapping_sub"),
                (BinOp::Mul, "wrapping_mul"),
            ] {
                let locals =
                    vec![Ty::Bool, scalar.clone(), scalar.clone(), scalar.clone(), scalar.clone()];
                let spelling = format!(
                    "{}core::num::<impl {}{width}>::{name}",
                    crate::TRUST_RUSTC_TOTAL_PRIMITIVE_METHOD_PATH_PREFIX,
                    if signed { "i" } else { "u" }
                );
                // The marker-authenticated call reads as its exact modular image.
                let wrapped = func(
                    locals.clone(),
                    3,
                    vec![
                        bb(
                            0,
                            vec![],
                            Terminator::Call {
                                func: spelling.clone(),
                                args: vec![cp(2), cp(3)],
                                dest: Place::local(4),
                                target: Some(BlockId(1)),
                                span: SourceSpan::default(),
                                atomic: None,
                                is_foreign: false,
                                is_unsafe_sig: false,
                                unwind: Default::default(),
                                callee_identity: None,
                                callee_key: None,
                            },
                        ),
                        bb(
                            1,
                            vec![asn(0, Rvalue::BinaryOp(BinOp::Le, cp(1), cp(4)))],
                            Terminator::Return,
                        ),
                    ],
                );
                let term = read_e6_tree(&wrapped).unwrap();
                assert!(
                    matches!(term,E6Term::Cmp { right, .. } if matches!(*right,E6Term::Arith { op:actual,.. } if actual==op))
                );
                // The same comparison over RAW arithmetic is an undischarged
                // panic operation: the reader refuses it (E6-TG14-PANIC-EDGE-1),
                // and it cannot manufacture its own NoPanic facet either.
                let f = func(
                    locals,
                    3,
                    vec![bb(
                        0,
                        vec![
                            asn(4, Rvalue::BinaryOp(op, cp(2), cp(3))),
                            asn(0, Rvalue::BinaryOp(BinOp::Le, cp(1), cp(4))),
                        ],
                        Terminator::Return,
                    )],
                );
                let raw = read_e6_tree(&f).expect_err("raw arithmetic is never read");
                assert!(raw.contains("the raw arithmetic"), "{raw}");
                assert!(!crate::facet_inference::infer_facets(&[f.clone()])[&f.def_path].no_panic);
                assert_eq!(wrapping_primitive(&spelling), Some((op, scalar.clone())));
                assert!(
                    wrapping_primitive(
                        spelling.trim_start_matches(
                            crate::TRUST_RUSTC_TOTAL_PRIMITIVE_METHOD_PATH_PREFIX
                        )
                    )
                    .is_none()
                );
                assert!(wrapping_primitive(&spelling.replace("core::", "evil::")).is_none());
            }
        }
    }
}

#[test]
fn tg14_checked_option_requires_the_some_arm() {
    for width in [8, 16, 32, 64] {
        for signed in [false, true] {
            let scalar = Ty::Int { width, signed };
            let option = Ty::adt_enum_with_disc_safety(
                "core::option::Option",
                vec![
                    crate::VariantDef { name: "None".into(), discriminant: 0, fields: vec![] },
                    crate::VariantDef {
                        name: "Some".into(),
                        discriminant: 1,
                        fields: vec![("0".into(), scalar.clone())],
                    },
                ],
                true,
            );
            let method = format!(
                "{}core::num::<impl {}{width}>::checked_sub",
                crate::TRUST_RUSTC_CHECKED_PRIMITIVE_METHOD_PATH_PREFIX,
                if signed { "i" } else { "u" }
            );
            let payload = Operand::Copy(Place {
                local: 4,
                projections: vec![crate::Projection::Downcast(1), crate::Projection::Field(0)],
            });
            let call = Terminator::Call {
                func: method,
                args: vec![cp(2), cp(3)],
                dest: Place::local(4),
                target: Some(BlockId(1)),
                span: SourceSpan::default(),
                atomic: None,
                is_foreign: false,
                is_unsafe_sig: false,
                unwind: Default::default(),
                callee_identity: None,
                callee_key: None,
            };
            let mut f = func(
                vec![
                    Ty::Bool,
                    scalar.clone(),
                    scalar.clone(),
                    scalar,
                    option,
                    Ty::Int { width: 64, signed: false },
                ],
                3,
                vec![
                    bb(0, vec![], call),
                    bb(
                        1,
                        vec![asn(5, Rvalue::Discriminant(Place::local(4)))],
                        Terminator::SwitchInt {
                            discr: cp(5),
                            targets: vec![(0, BlockId(2))],
                            otherwise: BlockId(3),
                            exhaustive_enum_unreachable: false,
                            span: SourceSpan::default(),
                        },
                    ),
                    bb(2, vec![asn(0, Rvalue::Use(fls()))], Terminator::Return),
                    bb(
                        3,
                        vec![asn(0, Rvalue::BinaryOp(BinOp::Le, cp(1), payload.clone()))],
                        Terminator::Return,
                    ),
                ],
            );
            assert!(read_e6_tree(&f).is_ok(), "{width}/{signed}: {:?}", read_e6_tree(&f));
            assert!(
                crate::facet_inference::infer_facets(&[f.clone()])[&f.def_path].all(),
                "checked Option is total"
            );
            let mut exhaustive = f.clone();
            if let Terminator::SwitchInt {
                targets, otherwise, exhaustive_enum_unreachable, ..
            } = &mut exhaustive.body.blocks[1].terminator
            {
                *targets = vec![(0, BlockId(2)), (1, BlockId(3))];
                *otherwise = BlockId(4);
                *exhaustive_enum_unreachable = true;
            }
            exhaustive.body.blocks.push(bb(4, vec![], Terminator::Unreachable));
            assert!(checked_option_impossible_defaults(&exhaustive).contains(&BlockId(4)));
            assert!(crate::facet_inference::infer_facets(&[exhaustive.clone()])[&f.def_path].all());
            let mut redirected = exhaustive.clone();
            if let Terminator::SwitchInt { targets, .. } = &mut redirected.body.blocks[1].terminator
            {
                targets[0].1 = BlockId(4);
            }
            assert!(checked_option_impossible_defaults(&redirected).is_empty());
            assert!(!crate::facet_inference::infer_facets(&[redirected])[&f.def_path].all());
            let mut effectful = exhaustive.clone();
            effectful.body.blocks[4].stmts.push(asn(0, Rvalue::Use(tru())));
            assert!(checked_option_impossible_defaults(&effectful).is_empty());
            assert!(!crate::facet_inference::infer_facets(&[effectful])[&f.def_path].all());
            let mut extra_edge = exhaustive.clone();
            extra_edge.body.blocks.push(bb(5, vec![], Terminator::Goto(BlockId(4))));
            assert!(checked_option_impossible_defaults(&extra_edge).is_empty());
            assert!(!crate::facet_inference::infer_facets(&[extra_edge])[&f.def_path].all());
            let mut stale = f.clone();
            let switch = stale.body.blocks[1].terminator.clone();
            let mut replacement = stale.body.blocks[0].terminator.clone();
            if let Terminator::Call { args, target, .. } = &mut replacement {
                args.swap(0, 1);
                *target = Some(BlockId(4));
            }
            stale.body.blocks[1].terminator = replacement;
            stale.body.blocks.push(bb(4, vec![], switch));
            assert!(
                read_e6_tree(&stale).unwrap_err().contains("outlived a write"),
                "a stale discriminant cannot authorize the replacement Option's payload"
            );
            f.body.blocks[2].stmts = vec![asn(0, Rvalue::BinaryOp(BinOp::Le, cp(1), payload))];
            assert!(read_e6_tree(&f).unwrap_err().contains("outside its Some arm"));
        }
    }
}

#[test]
fn tg14_plain_subtraction_does_not_discharge_its_own_overflow_obligation() {
    for width in [8, 16, 32, 64] {
        for signed in [false, true] {
            let scalar = Ty::Int { width, signed };
            let f = func(
                vec![
                    Ty::Bool,
                    scalar.clone(),
                    scalar.clone(),
                    scalar.clone(),
                    Ty::Tuple(vec![scalar.clone(), Ty::Bool]),
                    scalar,
                    Ty::Bool,
                ],
                3,
                vec![
                    bb(
                        0,
                        vec![
                            asn(4, Rvalue::CheckedBinaryOp(BinOp::Sub, cp(2), cp(3))),
                            asn(5, Rvalue::Use(Operand::Copy(Place::field(4, 0)))),
                            asn(6, Rvalue::Use(Operand::Copy(Place::field(4, 1)))),
                        ],
                        Terminator::Assert {
                            cond: cp(6),
                            expected: false,
                            msg: AssertMessage::Overflow(BinOp::Sub),
                            target: BlockId(1),
                            span: SourceSpan::default(),
                            unwind: Default::default(),
                        },
                    ),
                    bb(
                        1,
                        vec![asn(0, Rvalue::BinaryOp(BinOp::Le, cp(1), cp(5)))],
                        Terminator::Return,
                    ),
                ],
            );
            // The overflow `Assert` is a panic path: the reader refuses it
            // rather than reading past it to the wrapped `.0`, which would
            // answer where Rust panics (E6-TG14-PANIC-EDGE-1).
            let err = read_e6_tree(&f).expect_err("an overflow Assert must refuse the tree");
            assert!(err.contains("an `Assert`") && err.contains("a panic path"), "{err}");
            assert!(
                !crate::facet_inference::infer_facets(&[f.clone()])[&f.def_path].no_panic,
                "reading arithmetic must not prove its overflow obligation"
            );
            let mut wrong_flag = f.clone();
            if let Terminator::Assert { expected, .. } = &mut wrong_flag.body.blocks[0].terminator {
                *expected = true;
            }
            assert!(read_e6_tree(&wrong_flag).is_err(), "an inverted overflow Assert must refuse");
        }
    }
}
