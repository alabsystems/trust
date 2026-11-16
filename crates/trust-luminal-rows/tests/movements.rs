// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0 OR the MIT license
//
// ══════════════════════════════════════════════════════════════════════════
// Luminal row `logical-ir-shapes/movements` on trust-ir's `Inst::TensorView`.
// ══════════════════════════════════════════════════════════════════════════
//
// Luminal (f0875e6, src/logical/ir.rs `Movement` and `movement_entries`):
// seven movement primitives (Permute, ExpandDim, RemoveDim, SplitDims,
// MergeDims, Repeat, Shrink), each lowered to exactly ONE IndexMapApply whose
// per-parent-axis entries are stated from the movement's own parameters, with
// arity/axis refusals; a chain of movements is a chain of views.
//
// trust-ir has no movement instruction: its one view instruction is a
// coordinate function. `movement_view` below is Luminal's `movement_entries`
// restated for it: per SOURCE axis one index node (Luminal's per-parent-axis
// entry: `Coord` for a coordinate, `Lit` for a literal, `Mul`/`Div`/`Rem` by
// a movement parameter or a source extent), and per result axis one shape
// node (Luminal's new dims), the source's extents read as `SrcExtent` nodes
// and the movement's parameters as `Lit` nodes (ExpandDim's size also as a
// `usize` parameter, Luminal's symbolic size). Its refusals are Luminal's,
// word for word in substance, plus two Luminal does not make: a Permute that
// is not a permutation, and SplitDims by 0 (both would be undefined or
// meaningless views).
//
// What this target checks:
//
//   * each movement, on several shapes, is a function whose body is exactly
//     one TensorView and the return; its result extents are Luminal's new
//     dims and every element is what a hand loop of the movement reads;
//   * a chain (SplitDims, Permute, MergeDims) is three views, equal to the
//     three hand loops applied in turn;
//   * every arity/axis refusal of `movement_entries`;
//   * the views a refused movement would need are refused by the validator
//     by rule (V4 index arity, V5 a source axis or result axis out of scope),
//     and a shrink past the source's extent and a split by 0 are undefined
//     behaviour by their normative messages in both engines;
//   * SemR's `semr_eval` returns the interpreter's verdict on every run.

use std::path::Path;

use trust_ir::{Inst, TensorIndexExpr as E, Ty};
use trust_ir_build::{ValidationError, validate_module};
use trust_luminal_rows::{
    Case, Differential, Row, case, coordinates, instructions, int, module_of, offset, tensor,
    tensor_value,
};

const ID: &str = "logical-ir-shapes/movements";

const OUT_OF_RANGE: &str = "tensor view: a source coordinate is out of range";
const DIVIDES_BY_ZERO: &str = "tensor view: an index expression divides by zero";

/// ExpandDim's size: a literal, or the view's `usize` parameter 0 (a size
/// known only at run time, Luminal's symbolic `IntExpr`).
#[derive(Debug, Clone)]
enum Size {
    Lit(u64),
    Param,
}

/// Luminal's `Movement`, front-based axes as there.
#[derive(Debug, Clone)]
enum Movement {
    /// out dim i = in dim axes[i].
    Permute(Vec<usize>),
    /// A broadcast dim inserted at `axis`.
    ExpandDim { axis: usize, size: Size },
    /// The size-1 dim at `axis` removed.
    RemoveDim { axis: usize },
    /// dims[axis] = old / inner (outer), inner inserted after it.
    SplitDims { axis: usize, inner: u64 },
    /// axis2 merged into axis1: axis1 reads merged / inner, axis2 merged % inner.
    MergeDims { axis1: usize, axis2: usize },
    /// Per-axis tile: dim -> dim * r, the coordinate read modulo the old dim.
    Repeat(Vec<u64>),
    /// Zero-start slice: the same coordinates, smaller extents.
    Shrink { new_dims: Vec<u64> },
}

/// A TensorView's coordinate function under construction.
#[derive(Debug, Default, Clone)]
struct View {
    exprs: Vec<E>,
    shape: Vec<u32>,
    index: Vec<u32>,
    /// How many `usize` parameters the nodes read.
    params: usize,
}

impl View {
    fn node(&mut self, e: E) -> u32 {
        self.exprs.push(e);
        (self.exprs.len() - 1) as u32
    }
    fn coord(&mut self, axis: usize) -> u32 {
        self.node(E::Coord(axis as u32))
    }
    fn lit(&mut self, n: u64) -> u32 {
        self.node(E::Lit(n))
    }
    fn extent(&mut self, axis: usize) -> u32 {
        self.node(E::SrcExtent(axis as u32))
    }
}

/// One movement's view, stated from the movement's own parameters, and the
/// result's extents (Luminal's new dims) on a source of extents `prev`; or
/// the refusal. Mirrors `movement_entries`.
fn movement_view(movement: &Movement, prev: &[u64]) -> Result<(View, Vec<u64>), String> {
    let rank = prev.len();
    let mut v = View::default();
    let new_dims: Vec<u64> = match movement {
        Movement::Permute(axes) => {
            if axes.len() != rank {
                return Err(format!("permute arity {} vs rank {rank}", axes.len()));
            }
            let mut seen = vec![false; rank];
            for &p in axes {
                if p >= rank || std::mem::replace(&mut seen[p], true) {
                    return Err(format!("permute {axes:?} is not a permutation of 0..{rank}"));
                }
            }
            let mut index = vec![0u32; rank];
            for (q, &p) in axes.iter().enumerate() {
                index[p] = v.coord(q);
            }
            for &p in axes {
                let n = v.extent(p);
                v.shape.push(n);
            }
            v.index = index;
            axes.iter().map(|&p| prev[p]).collect()
        }
        Movement::ExpandDim { axis, size } => {
            let axis = *axis;
            if axis > rank {
                return Err(format!("expand_dim axis {axis} vs rank {rank}"));
            }
            for p in 0..rank {
                let n = v.coord(if p < axis { p } else { p + 1 });
                v.index.push(n);
            }
            for q in 0..=rank {
                let n = if q == axis {
                    match size {
                        Size::Lit(s) => v.lit(*s),
                        Size::Param => {
                            v.params = 1;
                            v.node(E::Param(0))
                        }
                    }
                } else {
                    v.extent(if q < axis { q } else { q - 1 })
                };
                v.shape.push(n);
            }
            let mut dims = prev.to_vec();
            // A run-time size is the run's argument; the hand side passes it.
            dims.insert(axis, if let Size::Lit(s) = size { *s } else { 0 });
            dims
        }
        Movement::RemoveDim { axis } => {
            let axis = *axis;
            if axis >= rank || prev[axis] != 1 {
                return Err(format!(
                    "remove_dim axis {axis} of dims {prev:?} (must be a size-1 axis)"
                ));
            }
            for p in 0..rank {
                let n =
                    if p == axis { v.lit(0) } else { v.coord(if p < axis { p } else { p - 1 }) };
                v.index.push(n);
            }
            for p in (0..rank).filter(|p| *p != axis) {
                let n = v.extent(p);
                v.shape.push(n);
            }
            let mut dims = prev.to_vec();
            dims.remove(axis);
            dims
        }
        Movement::SplitDims { axis, inner } => {
            let (axis, inner) = (*axis, *inner);
            if axis >= rank {
                return Err(format!("split_dims axis {axis} vs rank {rank}"));
            }
            if inner == 0 {
                return Err(format!("split_dims axis {axis} by inner 0"));
            }
            for p in 0..rank {
                let n = if p == axis {
                    let outer = v.coord(axis);
                    let by = v.lit(inner);
                    let scaled = v.node(E::Mul(outer, by));
                    let low = v.coord(axis + 1);
                    v.node(E::Add(scaled, low))
                } else {
                    v.coord(if p < axis { p } else { p + 1 })
                };
                v.index.push(n);
            }
            for q in 0..=rank {
                let n = if q < axis {
                    v.extent(q)
                } else if q == axis {
                    let old = v.extent(axis);
                    let by = v.lit(inner);
                    v.node(E::Div(old, by))
                } else if q == axis + 1 {
                    v.lit(inner)
                } else {
                    v.extent(q - 1)
                };
                v.shape.push(n);
            }
            let mut dims = prev.to_vec();
            dims[axis] = prev[axis] / inner;
            dims.insert(axis + 1, inner);
            dims
        }
        Movement::MergeDims { axis1, axis2 } => {
            let (axis1, axis2) = (*axis1, *axis2);
            if axis1 >= axis2 || axis2 >= rank {
                return Err(format!("merge_dims ({axis1},{axis2}) vs rank {rank}"));
            }
            for p in 0..rank {
                let n = if p == axis1 || p == axis2 {
                    let merged = v.coord(axis1);
                    let inner = v.extent(axis2);
                    v.node(if p == axis1 { E::Div(merged, inner) } else { E::Rem(merged, inner) })
                } else {
                    v.coord(if p < axis2 { p } else { p - 1 })
                };
                v.index.push(n);
            }
            for q in 0..rank - 1 {
                let n = if q == axis1 {
                    let a = v.extent(axis1);
                    let b = v.extent(axis2);
                    v.node(E::Mul(a, b))
                } else {
                    v.extent(if q < axis2 { q } else { q + 1 })
                };
                v.shape.push(n);
            }
            let mut dims = prev.to_vec();
            dims[axis1] = prev[axis1] * prev[axis2];
            dims.remove(axis2);
            dims
        }
        Movement::Repeat(repeats) => {
            if repeats.len() != rank {
                return Err(format!("repeat arity {} vs rank {rank}", repeats.len()));
            }
            for (p, &r) in repeats.iter().enumerate() {
                let n = if r == 1 {
                    v.coord(p)
                } else {
                    let c = v.coord(p);
                    let old = v.extent(p);
                    v.node(E::Rem(c, old))
                };
                v.index.push(n);
            }
            for (p, &r) in repeats.iter().enumerate() {
                let n = if r == 1 {
                    v.extent(p)
                } else {
                    let old = v.extent(p);
                    let by = v.lit(r);
                    v.node(E::Mul(old, by))
                };
                v.shape.push(n);
            }
            prev.iter().zip(repeats).map(|(d, r)| d * r).collect()
        }
        Movement::Shrink { new_dims } => {
            if new_dims.len() != rank {
                return Err(format!("shrink arity {} vs rank {rank}", new_dims.len()));
            }
            if let Some(p) = (0..rank).find(|&p| new_dims[p] > prev[p]) {
                return Err(format!(
                    "shrink {new_dims:?} of dims {prev:?}: axis {p} grows (an in-bounds shrink only)"
                ));
            }
            for p in 0..rank {
                let n = v.coord(p);
                v.index.push(n);
            }
            for &d in new_dims {
                let n = v.lit(d);
                v.shape.push(n);
            }
            new_dims.clone()
        }
    };
    Ok((v, new_dims))
}

/// The source coordinate the movement reads at result coordinate `c`, by
/// the movement's meaning, on a source of extents `prev` (the hand loop).
fn hand_source(movement: &Movement, prev: &[u64], c: &[u64]) -> Vec<u64> {
    match movement {
        Movement::Permute(axes) => {
            let mut src = vec![0; prev.len()];
            for (q, &p) in axes.iter().enumerate() {
                src[p] = c[q];
            }
            src
        }
        Movement::ExpandDim { axis, .. } => {
            let mut src = c.to_vec();
            src.remove(*axis);
            src
        }
        Movement::RemoveDim { axis } => {
            let mut src = c.to_vec();
            src.insert(*axis, 0);
            src
        }
        Movement::SplitDims { axis, inner } => {
            let mut src = c.to_vec();
            let low = src.remove(axis + 1);
            src[*axis] = src[*axis] * inner + low;
            src
        }
        Movement::MergeDims { axis1, axis2 } => {
            // Undo the merge: the merged coordinate is the row-major pair
            // (axis1, axis2) of extents (prev[axis1], prev[axis2]).
            let mut src = c.to_vec();
            let merged = src[*axis1];
            src[*axis1] = merged / prev[*axis2];
            src.insert(*axis2, merged % prev[*axis2]);
            src
        }
        Movement::Repeat(_) => c.iter().zip(prev).map(|(x, d)| x % d).collect(),
        Movement::Shrink { .. } => c.to_vec(),
    }
}

/// The movement applied by hand to `data` of extents `prev`: the result's
/// extents and elements.
fn hand(movement: &Movement, prev: &[u64], data: &[i128], dims: &[u64]) -> Vec<i128> {
    coordinates(dims).iter().map(|c| data[offset(prev, &hand_source(movement, prev, c))]).collect()
}

/// The emitter of `view` on the function's parameter 0 (the source) and, if
/// the view reads one, parameter 1 (its `usize` operand).
fn emit(
    v: &View,
    result: Ty,
) -> impl Fn(&mut trust_ir_build::FunctionBuilder<'_>, &[trust_ir::ValueId]) -> trust_ir::ValueId + 'static
{
    let v = v.clone();
    move |fb, p| {
        let params = p[1..=v.params].to_vec();
        fb.tensor_view(
            result.clone(),
            p[0],
            params,
            v.exprs.clone(),
            v.shape.clone(),
            v.index.clone(),
            None,
        )
    }
}

/// One movement case: its function name, movement and source extents.
struct Moved {
    name: &'static str,
    movement: Movement,
    prev: Vec<u64>,
}

fn moved(name: &'static str, movement: Movement, prev: &[u64]) -> Moved {
    Moved { name, movement, prev: prev.to_vec() }
}

fn cases() -> Vec<Moved> {
    use Movement as M;
    vec![
        moved("permute_201", M::Permute(vec![2, 0, 1]), &[2, 3, 4]),
        moved("permute_102", M::Permute(vec![1, 0, 2]), &[2, 3, 4]),
        moved("permute_identity", M::Permute(vec![0, 1, 2]), &[2, 3, 4]),
        moved("transpose", M::Permute(vec![1, 0]), &[3, 5]),
        moved("expand_front", M::ExpandDim { axis: 0, size: Size::Lit(3) }, &[2, 3]),
        moved("expand_middle", M::ExpandDim { axis: 1, size: Size::Lit(2) }, &[2, 3]),
        moved("expand_back", M::ExpandDim { axis: 2, size: Size::Lit(4) }, &[2, 3]),
        moved("expand_symbolic", M::ExpandDim { axis: 1, size: Size::Param }, &[3]),
        moved("expand_rank0", M::ExpandDim { axis: 0, size: Size::Lit(5) }, &[]),
        moved("remove_middle", M::RemoveDim { axis: 1 }, &[2, 1, 4]),
        moved("remove_front", M::RemoveDim { axis: 0 }, &[1, 3]),
        moved("remove_to_rank0", M::RemoveDim { axis: 0 }, &[1]),
        moved("split_middle", M::SplitDims { axis: 1, inner: 3 }, &[2, 6, 4]),
        moved("split_last", M::SplitDims { axis: 1, inner: 2 }, &[3, 4]),
        moved("split_prefix", M::SplitDims { axis: 1, inner: 3 }, &[2, 7]),
        moved("merge_01", M::MergeDims { axis1: 0, axis2: 1 }, &[2, 3, 4]),
        moved("merge_12", M::MergeDims { axis1: 1, axis2: 2 }, &[2, 3, 4]),
        moved("merge_02", M::MergeDims { axis1: 0, axis2: 2 }, &[2, 3, 4]),
        moved("repeat_rows", M::Repeat(vec![2, 1]), &[2, 3]),
        moved("repeat_all", M::Repeat(vec![3, 2, 1]), &[1, 2, 3]),
        moved("repeat_zero", M::Repeat(vec![0, 2]), &[2, 3]),
        moved("shrink_2d", M::Shrink { new_dims: vec![2, 3] }, &[3, 4]),
        moved("shrink_3d", M::Shrink { new_dims: vec![1, 3, 2] }, &[2, 3, 4]),
        moved("shrink_empty", M::Shrink { new_dims: vec![0, 4] }, &[3, 4]),
    ]
}

/// The three views of the chain `SplitDims(1, 3)`, `Permute([2, 0, 1])`,
/// `MergeDims(1, 2)` on a `[2, 6]` source, with each step's extents.
fn chain() -> Vec<(Movement, Vec<u64>, View, Vec<u64>)> {
    let steps = [
        Movement::SplitDims { axis: 1, inner: 3 },
        Movement::Permute(vec![2, 0, 1]),
        Movement::MergeDims { axis1: 1, axis2: 2 },
    ];
    let mut prev = vec![2u64, 6];
    let mut out = Vec::new();
    for m in steps {
        let (v, dims) = movement_view(&m, &prev).expect("each chain step is accepted");
        out.push((m, prev.clone(), v, dims.clone()));
        prev = dims;
    }
    out
}

fn element() -> Ty {
    Ty::I32
}

fn data(dims: &[u64]) -> Vec<i128> {
    (0..trust_luminal_rows::count(dims) as i128).map(|k| k * 7 - 40).collect()
}

fn module() -> trust_ir::Module {
    let mut fns: Vec<Case> = Vec::new();
    for c in cases() {
        let (v, dims) = movement_view(&c.movement, &c.prev)
            .unwrap_or_else(|why| panic!("{}: accepted, got {why}", c.name));
        let result = tensor(element(), dims.len() as u32);
        let mut params = vec![tensor(element(), c.prev.len() as u32)];
        params.extend((0..v.params).map(|_| Ty::Usize));
        fns.push(case(c.name, params, result.clone(), emit(&v, result)));
    }
    let steps = chain();
    let rank0 = steps[0].1.len() as u32;
    let last = steps.last().expect("a chain").3.len() as u32;
    fns.push(case(
        "chain",
        vec![tensor(element(), rank0)],
        tensor(element(), last),
        move |fb, p| {
            let mut x = p[0];
            for (_, _, v, dims) in &steps {
                x = fb.tensor_view(
                    tensor(element(), dims.len() as u32),
                    x,
                    vec![],
                    v.exprs.clone(),
                    v.shape.clone(),
                    v.index.clone(),
                    None,
                );
            }
            x
        },
    ));
    // Views built past a refused movement, run for their undefined
    // behaviour: a shrink to [2, 5] of a [2, 4] source, and a split of axis
    // 0 by 0 (the shape reads `src_extent(0) / 0`).
    fns.push(case(
        "shrink_past_extent",
        vec![tensor(element(), 2)],
        tensor(element(), 2),
        |fb, p| {
            fb.tensor_view(
                tensor(element(), 2),
                p[0],
                vec![],
                vec![E::Lit(2), E::Lit(5), E::Coord(0), E::Coord(1)],
                vec![0, 1],
                vec![2, 3],
                None,
            )
        },
    ));
    fns.push(case("split_by_zero", vec![tensor(element(), 1)], tensor(element(), 2), |fb, p| {
        fb.tensor_view(
            tensor(element(), 2),
            p[0],
            vec![],
            vec![
                E::SrcExtent(0),
                E::Lit(0),
                E::Div(0, 1),
                E::Coord(0),
                E::Coord(1),
                E::Mul(3, 1),
                E::Add(5, 4),
            ],
            vec![2, 1],
            vec![6],
            None,
        )
    }));
    module_of("luminal_movements", &fns)
}

fn check_each_movement_is_one_view(m: &trust_ir::Module, d: &mut Differential<'_>) {
    for c in cases() {
        let insts = instructions(m, c.name);
        assert!(
            matches!(insts.as_slice(), [Inst::TensorView { .. }, Inst::Return { .. }]),
            "{}: exactly one TensorView, then the return; got {insts:?}",
            c.name
        );
        let (_, mut dims) = movement_view(&c.movement, &c.prev).expect("accepted");
        let x = data(&c.prev);
        // A run-time ExpandDim size is the function's second argument: run
        // it at 4 and at 0 (an empty broadcast).
        let sizes: Vec<Option<u64>> = match c.movement {
            Movement::ExpandDim { size: Size::Param, .. } => vec![Some(4), Some(0)],
            _ => vec![None],
        };
        for size in sizes {
            let mut args = vec![tensor_value(&element(), &c.prev, &x)];
            if let (Some(size), Movement::ExpandDim { axis, .. }) = (size, &c.movement) {
                args.push(int(&Ty::Usize, i128::from(size)));
                dims[*axis] = size;
            }
            let (elem, got_dims, got) = d.computes(c.name, args);
            assert_eq!(elem, element(), "{}: the element type carries over", c.name);
            assert_eq!(got_dims, dims, "{}: Luminal's new dims", c.name);
            assert_eq!(got, hand(&c.movement, &c.prev, &x, &dims), "{}", c.name);
        }
    }
}

fn check_a_chain_is_a_chain_of_views(m: &trust_ir::Module, d: &mut Differential<'_>) {
    let insts = instructions(m, "chain");
    assert_eq!(
        insts.iter().filter(|i| matches!(i, Inst::TensorView { .. })).count(),
        3,
        "one view per movement: {insts:?}"
    );
    assert_eq!(insts.len(), 4, "three views and the return");
    let steps = chain();
    let start = steps[0].1.clone();
    let x = data(&start);
    let mut want = x.clone();
    for (movement, prev, _, dims) in &steps {
        want = hand(movement, prev, &want, dims);
    }
    let (_, got_dims, got) = d.computes("chain", vec![tensor_value(&element(), &start, &x)]);
    assert_eq!(&got_dims, &steps.last().expect("a chain").3);
    assert_eq!(got, want, "the chain is the three hand loops in turn");
}

fn check_luminal_refusals() {
    use Movement as M;
    let refused = [
        (M::Permute(vec![0, 1]), vec![2, 3, 4], "permute arity 2 vs rank 3"),
        (M::Permute(vec![0, 0, 1]), vec![2, 3, 4], "is not a permutation of 0..3"),
        (M::ExpandDim { axis: 3, size: Size::Lit(2) }, vec![2, 3], "expand_dim axis 3 vs rank 2"),
        (M::RemoveDim { axis: 2 }, vec![2, 1], "remove_dim axis 2 of dims [2, 1]"),
        (
            M::RemoveDim { axis: 0 },
            vec![2, 1],
            "remove_dim axis 0 of dims [2, 1] (must be a size-1 axis)",
        ),
        (M::SplitDims { axis: 2, inner: 2 }, vec![2, 4], "split_dims axis 2 vs rank 2"),
        (M::SplitDims { axis: 0, inner: 0 }, vec![4], "split_dims axis 0 by inner 0"),
        (M::MergeDims { axis1: 1, axis2: 1 }, vec![2, 3], "merge_dims (1,1) vs rank 2"),
        (M::MergeDims { axis1: 1, axis2: 0 }, vec![2, 3], "merge_dims (1,0) vs rank 2"),
        (M::MergeDims { axis1: 0, axis2: 2 }, vec![2, 3], "merge_dims (0,2) vs rank 2"),
        (M::Repeat(vec![2]), vec![2, 3], "repeat arity 1 vs rank 2"),
        (M::Shrink { new_dims: vec![1, 2, 3] }, vec![2, 3], "shrink arity 3 vs rank 2"),
        (M::Shrink { new_dims: vec![2, 5] }, vec![2, 4], "axis 1 grows"),
    ];
    for (movement, prev, says) in refused {
        let why = movement_view(&movement, &prev)
            .err()
            .unwrap_or_else(|| panic!("{movement:?} on {prev:?} must be refused"));
        assert!(why.contains(says), "{movement:?}: {why:?} names {says:?}");
    }
}

/// The validator's InvalidTensorView reasons for one view of a `tensor<i32,
/// src_rank>` source into a `tensor<i32, rank>` result.
fn view_refusals(
    src_rank: u32,
    rank: u32,
    exprs: Vec<E>,
    shape: Vec<u32>,
    index: Vec<u32>,
) -> Vec<String> {
    let m = module_of(
        "malformed_view",
        &[case(
            "malformed",
            vec![tensor(element(), src_rank)],
            tensor(element(), rank),
            move |fb, p| {
                fb.tensor_view(
                    tensor(element(), rank),
                    p[0],
                    vec![],
                    exprs.clone(),
                    shape.clone(),
                    index.clone(),
                    None,
                )
            },
        )],
    );
    let errors = validate_module(&m);
    assert!(!errors.is_empty(), "a malformed view is refused");
    errors
        .iter()
        .map(|e| match e {
            ValidationError::InvalidTensorView { reason, .. } => reason.clone(),
            other => panic!("refused by InvalidTensorView, got {other:?}"),
        })
        .collect()
}

fn check_malformed_views_are_validator_refusals() {
    // A rank-3 permute stated with two index nodes (its arity refusal).
    let r = view_refusals(
        3,
        3,
        vec![E::Coord(1), E::Coord(0), E::SrcExtent(1), E::SrcExtent(0), E::SrcExtent(2)],
        vec![2, 3, 4],
        vec![0, 1],
    );
    assert!(
        r.iter().any(|r| r.starts_with("rule V4: 2 index nodes for a source of rank 3")),
        "{r:?}"
    );
    // A merge naming source axis 2 of a rank-2 source.
    let r = view_refusals(
        2,
        1,
        vec![
            E::Coord(0),
            E::SrcExtent(2),
            E::Div(0, 1),
            E::Rem(0, 1),
            E::SrcExtent(0),
            E::Mul(4, 1),
        ],
        vec![5],
        vec![2, 3],
    );
    assert!(
        r.iter().any(|r| r.starts_with("rule V5: node 1 (src_extent(2)) reads out of its scope")),
        "{r:?}"
    );
    // An expand that reads result axis 2 of a rank-2 result.
    let r = view_refusals(1, 2, vec![E::Coord(2), E::Lit(3), E::SrcExtent(0)], vec![1, 2], vec![0]);
    assert!(
        r.iter().any(|r| r.starts_with("rule V5: node 0 (coord(2)) reads out of its scope")),
        "{r:?}"
    );
}

fn check_out_of_bounds_views_are_undefined_behaviour(d: &mut Differential<'_>) {
    d.ub(
        "shrink_past_extent",
        vec![tensor_value(&element(), &[2, 4], &data(&[2, 4]))],
        OUT_OF_RANGE,
    );
    d.ub("split_by_zero", vec![tensor_value(&element(), &[4], &data(&[4]))], DIVIDES_BY_ZERO);
    // A shrink inside the extent is not.
    let (_, dims, _) =
        d.computes("shrink_past_extent", vec![tensor_value(&element(), &[2, 5], &data(&[2, 5]))]);
    assert_eq!(dims, vec![2, 5]);
}

fn main() {
    let m = module();
    let mut d = Differential::new(&m);
    let mut row = Row::new(ID);
    row.check("each movement is exactly one TensorView, equal to its hand loop", || {
        check_each_movement_is_one_view(&m, &mut d)
    });
    row.check("a chain of movements is a chain of views", || {
        check_a_chain_is_a_chain_of_views(&m, &mut d)
    });
    row.check("Luminal's arity/axis refusals", check_luminal_refusals);
    row.check(
        "malformed views are validator refusals by rule",
        check_malformed_views_are_validator_refusals,
    );
    row.check("an out-of-bounds view is undefined behaviour", || {
        check_out_of_bounds_views_are_undefined_behaviour(&mut d)
    });
    let semr = d.semr(Path::new(env!("CARGO_TARGET_TMPDIR")));
    row.finish(semr);
}
