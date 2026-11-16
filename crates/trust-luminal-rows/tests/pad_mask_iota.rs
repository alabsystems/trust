// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0 OR the MIT license
//
// ══════════════════════════════════════════════════════════════════════════
// Luminal row `logical-ir-shapes/pad-mask-iota` from existing trust-ir
// instructions (TensorMap, TensorView, Const).
// ══════════════════════════════════════════════════════════════════════════
//
// Luminal (f0875e6, src/logical/ir.rs `record_mask_iota`): a pad mask over
// the padded extents `before + dim + after` is an iota whose value is the
// product, over the padded axes, of 0/1 comparison indicators
// `IntCastFromBool(before < coord + 1)` (when `before != 0`) and
// `IntCastFromBool(coord < before + dim)` (when `after != 0`), the empty
// product being 1: predication by arithmetic through the bool bridge.
//
// trust-ir at wire v70 has no iota instruction (PKG-U13i adds one). Here:
//
//   * the MASK is one TensorView of an all-ones tensor (a TensorMap of the
//     padded tensor with the scalar 1) with fill 0: the view's in-range rule
//     `0 <= coord - before < dim` is the two comparisons at once;
//   * each Luminal FACTOR is one fill-0 TensorView of a rank-1 all-ones
//     tensor broadcast to the padded extents, whose in-range rule is that
//     factor's comparison alone (`coord - before` read in `dim + after`, or
//     `coord` read in `before + dim`), and the PRODUCT of the factors present
//     is a TensorMap of `mul`s;
//   * the BOOL BRIDGE is `icmp ne` to Bool and `zext` back to i32 in one
//     TensorMap, and the mask PREDICATES by arithmetic: the padded tensor
//     with any fill, multiplied by the mask, is the padded tensor with 0.
//
// What this target checks, on rank 1, 2 and 3, with padding on one side, on
// both sides, on none, and an axis of extent 0: the mask, every factor and
// the product equal Luminal's iota expression evaluated by hand at every
// coordinate; the bridge returns the mask; the predicated pad equals a hand
// pad with 0; every function uses only Const, TensorMap and TensorView; and
// SemR's `semr_eval` returns the interpreter's verdict on every run.

use std::path::Path;

use trust_ir::{BinOp, CastOp, ICmpOp, Inst, TensorIndexExpr as E, TensorMapNode, Ty, ValueId};
use trust_ir_build::FunctionBuilder;
use trust_luminal_rows::{
    Case, Differential, Row, case, coordinates, instructions, module_of, offset, tensor,
    tensor_value,
};

const ID: &str = "logical-ir-shapes/pad-mask-iota";

fn i32t() -> Ty {
    Ty::I32
}

/// One pad: the unpadded extents and the padding before and after each axis.
#[derive(Debug, Clone)]
struct Pad {
    name: &'static str,
    dims: Vec<u64>,
    before: Vec<u64>,
    after: Vec<u64>,
}

impl Pad {
    fn rank(&self) -> usize {
        self.dims.len()
    }
    fn out_dims(&self) -> Vec<u64> {
        (0..self.rank()).map(|k| self.before[k] + self.dims[k] + self.after[k]).collect()
    }
    /// Luminal's factors, in its order: per axis, `lo` (`before < coord +
    /// 1`) when `before != 0`, then `hi` (`coord < before + dim`) when
    /// `after != 0`.
    fn factors(&self) -> Vec<(usize, Side)> {
        let mut out = Vec::new();
        for k in 0..self.rank() {
            if self.before[k] != 0 {
                out.push((k, Side::Lo));
            }
            if self.after[k] != 0 {
                out.push((k, Side::Hi));
            }
        }
        out
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Side {
    Lo,
    Hi,
}

fn pads() -> Vec<Pad> {
    let pad = |name, dims: &[u64], before: &[u64], after: &[u64]| Pad {
        name,
        dims: dims.to_vec(),
        before: before.to_vec(),
        after: after.to_vec(),
    };
    vec![
        pad("both_r1", &[3], &[2], &[1]),
        pad("after_r1", &[4], &[0], &[2]),
        pad("before_r1", &[4], &[3], &[0]),
        pad("mixed_r2", &[2, 3], &[1, 0], &[2, 1]),
        pad("none_r2", &[2, 2], &[0, 0], &[0, 0]),
        pad("mixed_r3", &[1, 2, 2], &[1, 0, 2], &[0, 1, 1]),
        pad("empty_axis_r2", &[0, 2], &[1, 1], &[1, 0]),
    ]
}

// ───────────────────────────── by hand ─────────────────────────────

/// `IntCastFromBool(b)`.
fn from_bool(b: bool) -> i128 {
    i128::from(b)
}

/// One of Luminal's factors at coordinate `c`, as `record_mask_iota` states
/// it.
fn hand_factor(p: &Pad, k: usize, side: Side, c: &[u64]) -> i128 {
    let (coord, before, dim) = (c[k], p.before[k], p.dims[k]);
    match side {
        Side::Lo => from_bool(before < coord + 1),
        Side::Hi => from_bool(coord < before + dim),
    }
}

/// Luminal's iota expression at every coordinate of the padded extents: the
/// product of the factors present, the empty product 1.
fn hand_mask(p: &Pad) -> Vec<i128> {
    coordinates(&p.out_dims())
        .iter()
        .map(|c| p.factors().iter().map(|&(k, side)| hand_factor(p, k, side, c)).product())
        .collect()
}

/// `x` padded with `fill` by hand.
fn hand_pad(p: &Pad, x: &[i128], fill: i128) -> Vec<i128> {
    coordinates(&p.out_dims())
        .iter()
        .map(|c| {
            let inside: Option<Vec<u64>> = (0..p.rank())
                .map(|k| c[k].checked_sub(p.before[k]).filter(|at| *at < p.dims[k]))
                .collect();
            inside.map_or(fill, |at| x[offset(&p.dims, &at)])
        })
        .collect()
}

// ───────────────────────────── in trust-ir ─────────────────────────────

/// `tensor_map(x, 1) { or $1, $1 }`: an all-ones tensor of `x`'s extents.
fn ones(fb: &mut FunctionBuilder<'_>, x: ValueId, rank: usize) -> ValueId {
    let one = fb.iconst(i32t(), 1);
    fb.tensor_map(
        tensor(i32t(), rank as u32),
        vec![x, one],
        vec![TensorMapNode::BinOp { op: BinOp::Or, ty: i32t(), lhs: 1, rhs: 1 }],
    )
}

/// `src` (extents `dims`) padded by `p` with `fill`: ONE TensorView whose
/// nodes are the pad's own parameters, its result extents
/// `src_extent(k) + before + after`.
fn pad_view(fb: &mut FunctionBuilder<'_>, p: &Pad, src: ValueId, fill: ValueId) -> ValueId {
    let mut exprs = Vec::new();
    let mut node = |e: E| {
        exprs.push(e);
        (exprs.len() - 1) as u32
    };
    let (mut shape, mut index) = (Vec::new(), Vec::new());
    for k in 0..p.rank() {
        let c = node(E::Coord(k as u32));
        let b = node(E::Lit(p.before[k]));
        index.push(node(E::Sub(c, b)));
        let e = node(E::SrcExtent(k as u32));
        let both = node(E::Lit(p.before[k] + p.after[k]));
        shape.push(node(E::Add(e, both)));
    }
    fb.tensor_view(tensor(i32t(), p.rank() as u32), src, vec![], exprs, shape, index, Some(fill))
}

/// The pad mask: the all-ones tensor padded with 0.
fn mask(fb: &mut FunctionBuilder<'_>, p: &Pad, x: ValueId) -> ValueId {
    let all = ones(fb, x, p.rank());
    let zero = fb.iconst(i32t(), 0);
    pad_view(fb, p, all, zero)
}

/// One of Luminal's factors as one fill-0 TensorView: a rank-1 all-ones
/// tensor of extent `dim + after` (lo) or `before + dim` (hi), read at
/// `coord(k) - before` (lo) or `coord(k)` (hi), over the padded extents.
fn factor(fb: &mut FunctionBuilder<'_>, p: &Pad, x: ValueId, k: usize, side: Side) -> ValueId {
    let all = ones(fb, x, p.rank());
    let one = fb.iconst(i32t(), 1);
    let zero = fb.iconst(i32t(), 0);
    let len = match side {
        Side::Lo => p.dims[k] + p.after[k],
        Side::Hi => p.before[k] + p.dims[k],
    };
    // A rank-1 run of 1s of extent `len`: every source coordinate is 0, and
    // where the source has no element there (an extent 0) the fill is 1.
    let run = fb.tensor_view(
        tensor(i32t(), 1),
        all,
        vec![],
        vec![E::Lit(len), E::Lit(0)],
        vec![0],
        vec![1; p.rank()],
        Some(one),
    );
    let out = p.out_dims();
    let mut exprs: Vec<E> = out.iter().map(|&d| E::Lit(d)).collect();
    let shape: Vec<u32> = (0..out.len() as u32).collect();
    exprs.push(E::Coord(k as u32));
    let coord = (exprs.len() - 1) as u32;
    let at = match side {
        Side::Lo => {
            exprs.push(E::Lit(p.before[k]));
            exprs.push(E::Sub(coord, coord + 1));
            coord + 2
        }
        Side::Hi => coord,
    };
    fb.tensor_view(tensor(i32t(), p.rank() as u32), run, vec![], exprs, shape, vec![at], Some(zero))
}

/// The product of Luminal's factors: one `mul` per factor after the first in
/// one TensorMap; one factor is itself (`or $0, $0`); none is the all-ones
/// tensor (the empty product, `IntLit 1`).
fn product(fb: &mut FunctionBuilder<'_>, p: &Pad, x: ValueId) -> ValueId {
    let fs: Vec<ValueId> = p.factors().iter().map(|&(k, side)| factor(fb, p, x, k, side)).collect();
    let ty = tensor(i32t(), p.rank() as u32);
    match fs.len() {
        0 => ones(fb, x, p.rank()),
        n => {
            let body = if n == 1 {
                vec![TensorMapNode::BinOp { op: BinOp::Or, ty: i32t(), lhs: 0, rhs: 0 }]
            } else {
                (1..n as u32)
                    .map(|j| TensorMapNode::BinOp {
                        op: BinOp::Mul,
                        ty: i32t(),
                        // node j-1 multiplies the running product (operand
                        // 0, then node j-2's lane) by operand j.
                        lhs: if j == 1 { 0 } else { n as u32 + j - 2 },
                        rhs: j,
                    })
                    .collect()
            };
            fb.tensor_map(ty, fs, body)
        }
    }
}

/// The mask through the bool bridge: `zext(icmp ne mask, 0)`.
fn bridge(fb: &mut FunctionBuilder<'_>, p: &Pad, x: ValueId) -> ValueId {
    let m = mask(fb, p, x);
    let zero = fb.iconst(i32t(), 0);
    fb.tensor_map(
        tensor(i32t(), p.rank() as u32),
        vec![m, zero],
        vec![
            TensorMapNode::ICmp { op: ICmpOp::Ne, ty: i32t(), lhs: 0, rhs: 1 },
            TensorMapNode::Cast { op: CastOp::ZExt, src_ty: Ty::Bool, dst_ty: i32t(), operand: 2 },
        ],
    )
}

/// Predication by arithmetic: `x` padded with 7, times the mask.
fn predicate(fb: &mut FunctionBuilder<'_>, p: &Pad, x: ValueId) -> ValueId {
    let seven = fb.iconst(i32t(), 7);
    let padded = pad_view(fb, p, x, seven);
    let m = mask(fb, p, x);
    fb.tensor_map(
        tensor(i32t(), p.rank() as u32),
        vec![padded, m],
        vec![TensorMapNode::BinOp { op: BinOp::Mul, ty: i32t(), lhs: 0, rhs: 1 }],
    )
}

type Build = fn(&mut FunctionBuilder<'_>, &Pad, ValueId) -> ValueId;

fn function(name: String, p: &Pad, build: Build) -> Case {
    let p = p.clone();
    let ty = tensor(i32t(), p.rank() as u32);
    case(name, vec![ty.clone()], ty, move |fb, params| build(fb, &p, params[0]))
}

fn factor_name(p: &Pad, k: usize, side: Side) -> String {
    format!("{}_factor_{k}_{}", p.name, if side == Side::Lo { "lo" } else { "hi" })
}

fn module() -> trust_ir::Module {
    let mut fns = Vec::new();
    for p in pads() {
        fns.push(function(format!("{}_mask", p.name), &p, mask));
        fns.push(function(format!("{}_product", p.name), &p, product));
        fns.push(function(format!("{}_bridge", p.name), &p, bridge));
        fns.push(function(format!("{}_predicate", p.name), &p, predicate));
        for (k, side) in p.factors() {
            let ty = tensor(i32t(), p.rank() as u32);
            let q = p.clone();
            fns.push(case(factor_name(&p, k, side), vec![ty.clone()], ty, move |fb, params| {
                factor(fb, &q, params[0], k, side)
            }));
        }
    }
    module_of("luminal_pad_mask_iota", &fns)
}

fn x(p: &Pad) -> Vec<i128> {
    (0..trust_luminal_rows::count(&p.dims) as i128).map(|k| 3 * k - 5).collect()
}

fn arg(p: &Pad) -> Vec<trust_ir::InterpretValue> {
    vec![tensor_value(&i32t(), &p.dims, &x(p))]
}

fn check_only_existing_instructions(m: &trust_ir::Module) {
    for f in &m.functions {
        for inst in instructions(m, &f.name) {
            assert!(
                matches!(
                    inst,
                    Inst::Const { .. }
                        | Inst::TensorMap { .. }
                        | Inst::TensorView { .. }
                        | Inst::Return { .. }
                ),
                "{}: only Const, TensorMap and TensorView, got {inst:?}",
                f.name
            );
        }
    }
    for p in pads() {
        let views = instructions(m, &format!("{}_mask", p.name))
            .into_iter()
            .filter(|i| matches!(i, Inst::TensorView { .. }))
            .count();
        assert_eq!(views, 1, "{}: the mask is one view", p.name);
    }
}

fn check_mask_is_the_iota(d: &mut Differential<'_>) {
    for p in pads() {
        let (elem, dims, got) = d.computes(&format!("{}_mask", p.name), arg(&p));
        assert_eq!(elem, i32t());
        assert_eq!(dims, p.out_dims(), "{}: the padded extents", p.name);
        assert_eq!(got, hand_mask(&p), "{}: Luminal's iota expression", p.name);
    }
}

fn check_each_factor(d: &mut Differential<'_>) {
    for p in pads() {
        for (k, side) in p.factors() {
            let (_, dims, got) = d.computes(&factor_name(&p, k, side), arg(&p));
            assert_eq!(dims, p.out_dims());
            let want: Vec<i128> =
                coordinates(&p.out_dims()).iter().map(|c| hand_factor(&p, k, side, c)).collect();
            assert_eq!(got, want, "{}: factor {k} {side:?}", p.name);
        }
    }
}

fn check_product(d: &mut Differential<'_>) {
    for p in pads() {
        let (_, dims, got) = d.computes(&format!("{}_product", p.name), arg(&p));
        assert_eq!(dims, p.out_dims());
        assert_eq!(got, hand_mask(&p), "{}: the product of the factors", p.name);
    }
    // The empty product: no padding gives all ones.
    let none = &pads()[4];
    assert!(none.factors().is_empty());
    assert!(hand_mask(none).iter().all(|v| *v == 1));
}

fn check_bridge_and_predication(d: &mut Differential<'_>) {
    for p in pads() {
        let (_, _, got) = d.computes(&format!("{}_bridge", p.name), arg(&p));
        assert_eq!(got, hand_mask(&p), "{}: the bool bridge returns the mask", p.name);
        let (_, dims, got) = d.computes(&format!("{}_predicate", p.name), arg(&p));
        assert_eq!(dims, p.out_dims());
        assert_eq!(got, hand_pad(&p, &x(&p), 0), "{}: predication by the mask", p.name);
        assert!(hand_mask(&p).iter().all(|v| *v == 0 || *v == 1), "the mask is 0/1");
    }
}

fn main() {
    let m = module();
    let mut d = Differential::new(&m);
    let mut row = Row::new(ID);
    row.check("built from existing instructions only", || check_only_existing_instructions(&m));
    row.check("the pad mask is Luminal's iota expression", || check_mask_is_the_iota(&mut d));
    row.check("each comparison factor is one fill-0 view", || check_each_factor(&mut d));
    row.check("the mask is the product of the per-axis factors", || check_product(&mut d));
    row.check("predication by arithmetic through the bool bridge", || {
        check_bridge_and_predication(&mut d)
    });
    let semr = d.semr(Path::new(env!("CARGO_TARGET_TMPDIR")));
    row.finish(semr);
}
