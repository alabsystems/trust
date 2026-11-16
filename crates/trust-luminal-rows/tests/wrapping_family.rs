// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0 OR the MIT license
//
// ══════════════════════════════════════════════════════════════════════════
// Luminal row `logical-ir-shapes/wrapping-family` on trust-ir's integer
// tensor arithmetic.
// ══════════════════════════════════════════════════════════════════════════
//
// Luminal (f0875e6, src/logical/ir.rs `WrappingAdd`, `WrappingMul`,
// `WrappingReduceSum`, `WrappingScanSum`, `WrappingScanProd`): total
// two's-complement operations that model PyTorch integer arithmetic modulo
// 2^w, with results bounded to the dtype range. Luminal's own test
// (src/logical/op/wrapping_tests.rs) states them for Int (32-bit), Int64 and
// UInt64.
//
// trust-ir has no separate wrapping operations: its integer `add` and `mul`
// wrap, in a TensorMap body as in scalar code, and TensorReduce `add`/`mul`
// fold with them. It has no scan instruction; an inclusive scan along the
// last axis is one TensorView that reads `x[i, t]` at `[i, j, t]` when
// `t <= j` and the fill (the operator's identity, 0 or 1) otherwise
// (`t + n * min(max(t - j, 0), 1)` leaves the axis exactly when `t > j`),
// then one TensorReduce over `t`.
//
// What this target checks, for i32, i64 and u64, on tensors holding MIN, MAX
// and -1 (for u64, -1 is MAX's residue 2^64 - 1) with 0, 1, 2 and their
// neighbours: elementwise add and mul, the sum over each axis and over both,
// and the inclusive sum and product scans equal hand loops of modular
// arithmetic on residues (and, where it fits, exact integer arithmetic taken
// modulo 2^w); each result's element type is the operand's and every element
// lies in the dtype's range; the overflow corners give the two's-complement
// answers (MAX + 1 = MIN, MIN * -1 = MIN, MAX * MAX = 1, ...); and SemR's
// `semr_eval` returns the interpreter's verdict on every run.

use std::path::Path;

use trust_ir::{BinOp, Inst, TensorIndexExpr as E, TensorMapNode, TensorReduceOp, Ty, ValueId};
use trust_ir_build::FunctionBuilder;
use trust_luminal_rows::{
    Case, Differential, Row, case, coordinates, instructions, module_of, offset, tensor,
    tensor_value,
};

const ID: &str = "logical-ir-shapes/wrapping-family";

/// One element type: its name, width and signedness.
#[derive(Debug, Clone, Copy)]
struct Elem {
    name: &'static str,
    bits: u32,
    signed: bool,
}

const ELEMS: [Elem; 3] = [
    Elem { name: "i32", bits: 32, signed: true },
    Elem { name: "i64", bits: 64, signed: true },
    Elem { name: "u64", bits: 64, signed: false },
];

impl Elem {
    fn ty(self) -> Ty {
        match (self.bits, self.signed) {
            (32, true) => Ty::I32,
            (64, true) => Ty::I64,
            (64, false) => Ty::U64,
            _ => unreachable!("one of ELEMS"),
        }
    }
    fn modulus(self) -> u128 {
        1u128 << self.bits
    }
    fn min(self) -> i128 {
        if self.signed { -(1i128 << (self.bits - 1)) } else { 0 }
    }
    fn max(self) -> i128 {
        if self.signed { (1i128 << (self.bits - 1)) - 1 } else { (1i128 << self.bits) - 1 }
    }
    /// The residue modulo 2^w of an integer.
    fn residue(self, v: i128) -> u128 {
        v.rem_euclid(1i128 << self.bits) as u128
    }
    /// The integer a residue denotes at this type (two's complement when
    /// signed).
    fn denote(self, r: u128) -> i128 {
        assert!(r < self.modulus(), "a residue is below 2^w");
        let v = r as i128;
        if self.signed && r >= self.modulus() / 2 { v - (1i128 << self.bits) } else { v }
    }
    /// MIN, MAX and -1 (its residue for an unsigned type), then 0, 1, 2 and
    /// the extremes' neighbours: nine values, a 3x3 tensor.
    fn corners(self) -> Vec<i128> {
        let minus_one = self.denote(self.residue(-1));
        vec![
            self.min(),
            self.max(),
            minus_one,
            0,
            1,
            2,
            self.denote(self.residue(self.min() + 1)),
            self.max() - 1,
            self.denote(self.residue(-2)),
        ]
    }
}

// ───────────────────────────── by hand ─────────────────────────────

/// `a + b` modulo 2^w on residues.
fn add_mod(e: Elem, a: u128, b: u128) -> u128 {
    (a + b) % e.modulus()
}

/// `a * b` modulo 2^w on residues (both below 2^64, so the product fits).
fn mul_mod(e: Elem, a: u128, b: u128) -> u128 {
    (a * b) % e.modulus()
}

fn hand_elementwise(e: Elem, op: BinOp, a: &[i128], b: &[i128]) -> Vec<i128> {
    a.iter()
        .zip(b)
        .map(|(&x, &y)| {
            let (rx, ry) = (e.residue(x), e.residue(y));
            let modular = match op {
                BinOp::Add => add_mod(e, rx, ry),
                BinOp::Mul => mul_mod(e, rx, ry),
                _ => unreachable!(),
            };
            // The same answer from exact integer arithmetic taken modulo 2^w
            // (the product of two 64-bit magnitudes fits u128 exactly).
            let exact = match op {
                BinOp::Add => e.residue(x + y),
                BinOp::Mul if e.signed => e.residue(x * y),
                BinOp::Mul => (x as u128 * y as u128) % e.modulus(),
                _ => unreachable!(),
            };
            assert_eq!(modular, exact, "two hand loops agree on {x} {op:?} {y}");
            e.denote(modular)
        })
        .collect()
}

/// The `op` fold (identity first) over the elements of `x` (extents `dims`)
/// whose coordinate along `axes` varies, at each kept coordinate.
fn hand_reduce(
    e: Elem,
    add: bool,
    dims: &[u64],
    x: &[i128],
    axes: &[usize],
) -> (Vec<u64>, Vec<i128>) {
    let kept: Vec<usize> = (0..dims.len()).filter(|a| !axes.contains(a)).collect();
    let out_dims: Vec<u64> = kept.iter().map(|&a| dims[a]).collect();
    let out = coordinates(&out_dims)
        .iter()
        .map(|o| {
            let mut acc: u128 = if add { 0 } else { 1 };
            for c in coordinates(dims) {
                if kept.iter().zip(o).all(|(&a, &v)| c[a] == v) {
                    let r = e.residue(x[offset(dims, &c)]);
                    acc = if add { add_mod(e, acc, r) } else { mul_mod(e, acc, r) };
                }
            }
            e.denote(acc)
        })
        .collect();
    (out_dims, out)
}

/// The inclusive scan of rank-2 `x` along axis 1 by hand.
fn hand_scan(e: Elem, add: bool, dims: &[u64], x: &[i128]) -> Vec<i128> {
    let (m, n) = (dims[0] as usize, dims[1] as usize);
    let mut out = Vec::with_capacity(m * n);
    for i in 0..m {
        let mut acc: u128 = if add { 0 } else { 1 };
        for j in 0..n {
            let r = e.residue(x[i * n + j]);
            acc = if add { add_mod(e, acc, r) } else { mul_mod(e, acc, r) };
            out.push(e.denote(acc));
        }
    }
    out
}

// ───────────────────────────── in trust-ir ─────────────────────────────

fn elementwise(
    e: Elem,
    op: BinOp,
) -> impl Fn(&mut FunctionBuilder<'_>, &[ValueId]) -> ValueId + 'static {
    move |fb, p| {
        fb.tensor_map(
            tensor(e.ty(), 2),
            vec![p[0], p[1]],
            vec![TensorMapNode::BinOp { op, ty: e.ty(), lhs: 0, rhs: 1 }],
        )
    }
}

fn reduce(
    e: Elem,
    axes: Vec<u32>,
) -> impl Fn(&mut FunctionBuilder<'_>, &[ValueId]) -> ValueId + 'static {
    move |fb, p| {
        fb.tensor_reduce(
            tensor(e.ty(), 2 - axes.len() as u32),
            p[0],
            TensorReduceOp::Add,
            axes.clone(),
        )
    }
}

/// The inclusive scan along axis 1: one triangular TensorView with the
/// identity as fill, then one TensorReduce over the new last axis.
fn scan(e: Elem, add: bool) -> impl Fn(&mut FunctionBuilder<'_>, &[ValueId]) -> ValueId + 'static {
    move |fb, p| {
        let identity = fb.iconst(e.ty(), if add { 0 } else { 1 });
        let exprs = vec![
            E::SrcExtent(0), // 0  m
            E::SrcExtent(1), // 1  n
            E::Coord(0),     // 2  i
            E::Coord(1),     // 3  j
            E::Coord(2),     // 4  t
            E::Sub(4, 3),    // 5  t - j
            E::Lit(0),       // 6
            E::Max(5, 6),    // 7  max(t - j, 0)
            E::Lit(1),       // 8
            E::Min(7, 8),    // 9  1 when t > j, else 0
            E::Mul(9, 1),    // 10 n when t > j, else 0
            E::Add(4, 10),   // 11 t, or past the axis when t > j
        ];
        let triangle = fb.tensor_view(
            tensor(e.ty(), 3),
            p[0],
            vec![],
            exprs,
            vec![0, 1, 1],
            vec![2, 11],
            Some(identity),
        );
        fb.tensor_reduce(
            tensor(e.ty(), 2),
            triangle,
            if add { TensorReduceOp::Add } else { TensorReduceOp::Mul },
            vec![2],
        )
    }
}

fn module() -> trust_ir::Module {
    let mut fns: Vec<Case> = Vec::new();
    for e in ELEMS {
        let t2 = tensor(e.ty(), 2);
        fns.push(case(
            format!("add_{}", e.name),
            vec![t2.clone(), t2.clone()],
            t2.clone(),
            elementwise(e, BinOp::Add),
        ));
        fns.push(case(
            format!("mul_{}", e.name),
            vec![t2.clone(), t2.clone()],
            t2.clone(),
            elementwise(e, BinOp::Mul),
        ));
        fns.push(case(
            format!("sum_rows_{}", e.name),
            vec![t2.clone()],
            tensor(e.ty(), 1),
            reduce(e, vec![1]),
        ));
        fns.push(case(
            format!("sum_cols_{}", e.name),
            vec![t2.clone()],
            tensor(e.ty(), 1),
            reduce(e, vec![0]),
        ));
        fns.push(case(
            format!("sum_all_{}", e.name),
            vec![t2.clone()],
            tensor(e.ty(), 0),
            reduce(e, vec![0, 1]),
        ));
        fns.push(case(format!("cumsum_{}", e.name), vec![t2.clone()], t2.clone(), scan(e, true)));
        fns.push(case(format!("cumprod_{}", e.name), vec![t2.clone()], t2, scan(e, false)));
    }
    module_of("luminal_wrapping_family", &fns)
}

/// Asserts the result's element type is `e`'s and each element lies in its
/// range.
fn in_range(e: Elem, what: &str, elem: &Ty, values: &[i128]) {
    assert_eq!(*elem, e.ty(), "{what}: the element type is the operand's");
    assert!(
        values.iter().all(|v| (e.min()..=e.max()).contains(v)),
        "{what}: every element in [{}, {}]: {values:?}",
        e.min(),
        e.max()
    );
}

fn check_add_and_mul(d: &mut Differential<'_>) {
    let dims = [3u64, 3];
    for e in ELEMS {
        let a = e.corners();
        let mut b = a.clone();
        b.reverse();
        // Each corner against itself, against the reversed corners, and
        // against a column of 1, -1 and 2.
        let mut c: Vec<i128> = Vec::new();
        for _ in 0..3 {
            c.extend([1, e.denote(e.residue(-1)), 2]);
        }
        for (rhs, label) in [(&a, "a"), (&b, "reversed"), (&c, "units")] {
            for op in [BinOp::Add, BinOp::Mul] {
                let name = format!("{}_{}", if op == BinOp::Add { "add" } else { "mul" }, e.name);
                let (elem, got_dims, got) = d.computes(
                    &name,
                    vec![tensor_value(&e.ty(), &dims, &a), tensor_value(&e.ty(), &dims, rhs)],
                );
                assert_eq!(got_dims, dims.to_vec());
                in_range(e, &name, &elem, &got);
                assert_eq!(got, hand_elementwise(e, op, &a, rhs), "{name} on corners x {label}");
            }
        }
    }
}

fn check_overflow_corners(d: &mut Differential<'_>) {
    // The two's-complement answers, stated outright, one pair per element.
    for e in ELEMS {
        let (min, max, m1) = (e.min(), e.max(), e.denote(e.residue(-1)));
        let lhs = [max, min, m1, min, max, m1];
        let rhs = [1, m1, m1, m1, max, 1];
        let (_, _, sums) = d.computes(
            &format!("add_{}", e.name),
            vec![tensor_value(&e.ty(), &[2, 3], &lhs), tensor_value(&e.ty(), &[2, 3], &rhs)],
        );
        let (_, _, prods) = d.computes(
            &format!("mul_{}", e.name),
            vec![tensor_value(&e.ty(), &[2, 3], &lhs), tensor_value(&e.ty(), &[2, 3], &rhs)],
        );
        if e.signed {
            // MAX + 1 = MIN, MIN + -1 = MAX, -1 + -1 = -2, MIN + -1 = MAX,
            // MAX + MAX = -2, -1 + 1 = 0.
            assert_eq!(sums, vec![min, max, -2, max, -2, 0], "{} sums", e.name);
            // MAX * 1 = MAX, MIN * -1 = MIN, -1 * -1 = 1, MIN * -1 = MIN,
            // MAX * MAX = 1, -1 * 1 = -1.
            assert_eq!(prods, vec![max, min, 1, min, 1, -1], "{} products", e.name);
        } else {
            // u64: MIN = 0 and -1 = MAX. MAX + 1 = 0, 0 + MAX = MAX,
            // MAX + MAX = MAX - 1, ...
            assert_eq!(sums, vec![0, max, max - 1, max, max - 1, 0], "u64 sums");
            assert_eq!(prods, vec![max, 0, 1, 0, 1, max], "u64 products");
        }
    }
}

fn check_reduce_sum(d: &mut Differential<'_>) {
    let dims = [3u64, 3];
    for e in ELEMS {
        let x = e.corners();
        for (name, axes, out_rank) in [
            ("sum_rows", vec![1usize], 1usize),
            ("sum_cols", vec![0], 1),
            ("sum_all", vec![0, 1], 0),
        ] {
            let name = format!("{name}_{}", e.name);
            let (elem, got_dims, got) = d.computes(&name, vec![tensor_value(&e.ty(), &dims, &x)]);
            let (want_dims, want) = hand_reduce(e, true, &dims, &x, &axes);
            assert_eq!(got_dims.len(), out_rank);
            assert_eq!(got_dims, want_dims, "{name}: the kept extents");
            in_range(e, &name, &elem, &got);
            assert_eq!(got, want, "{name}");
        }
        // [MAX, 1, MIN]: MAX + 1 wraps (to MIN, or to 0 for u64), and the
        // sum is 0 either way.
        let row = [e.max(), 1, e.min()];
        let (_, _, got) =
            d.computes(&format!("sum_rows_{}", e.name), vec![tensor_value(&e.ty(), &[1, 3], &row)]);
        assert_eq!(got, vec![e.denote(e.residue(e.max() + 1 + e.min()))]);
        // An empty reduced axis gives the identity.
        let (_, got_dims, got) =
            d.computes(&format!("sum_rows_{}", e.name), vec![tensor_value(&e.ty(), &[2, 0], &[])]);
        assert_eq!((got_dims, got), (vec![2], vec![0, 0]));
    }
}

fn check_scans(m: &trust_ir::Module, d: &mut Differential<'_>) {
    for e in ELEMS {
        for add in [true, false] {
            let name = format!("{}_{}", if add { "cumsum" } else { "cumprod" }, e.name);
            let insts = instructions(m, &name);
            assert!(
                matches!(
                    insts.as_slice(),
                    [
                        Inst::Const { .. },
                        Inst::TensorView { .. },
                        Inst::TensorReduce { .. },
                        Inst::Return { .. }
                    ]
                ),
                "{name}: the identity, one view, one reduction: {insts:?}"
            );
            for (dims, x) in [
                (vec![3u64, 3], e.corners()),
                (vec![1, 4], vec![e.max(), e.max(), e.min(), e.denote(e.residue(-1))]),
                (vec![2, 1], vec![e.min(), e.max()]),
                (vec![2, 0], vec![]),
            ] {
                let (elem, got_dims, got) =
                    d.computes(&name, vec![tensor_value(&e.ty(), &dims, &x)]);
                assert_eq!(got_dims, dims, "{name}: a scan keeps the extents");
                in_range(e, &name, &elem, &got);
                assert_eq!(got, hand_scan(e, add, &dims, &x), "{name} on {dims:?}");
            }
        }
    }
}

fn main() {
    let m = module();
    let mut d = Differential::new(&m);
    let mut row = Row::new(ID);
    row.check("WrappingAdd and WrappingMul are modular hand loops", || check_add_and_mul(&mut d));
    row.check("the overflow corners at MIN, MAX and -1", || check_overflow_corners(&mut d));
    row.check("WrappingReduceSum is a modular fold", || check_reduce_sum(&mut d));
    row.check("WrappingScanSum and WrappingScanProd are one view and one reduction", || {
        check_scans(&m, &mut d)
    });
    let semr = d.semr(Path::new(env!("CARGO_TARGET_TMPDIR")));
    row.finish(semr);
}
