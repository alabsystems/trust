// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0 OR the MIT license
//
// ══════════════════════════════════════════════════════════════════════════
// Luminal row `logical-ir-shapes/gather` on trust-ir's `Inst::TensorGather`.
// ══════════════════════════════════════════════════════════════════════════
//
// Luminal (f0875e6, src/logical/ir.rs `record_gather` and
// src/logical/op/gather/*.egg): coordinate-form gather takes one Int
// coordinate tensor per data axis, all sharing one shape that becomes the
// output shape; rank-0 data is refused, out-of-bounds coordinates are declared
// undefined behaviour, and data bounds carry over.
//
// What this target checks, at Trust's first-party/trust-ir pin:
//
//   * shape: rank-2 data at two rank-1 coordinate tensors returns a rank-1
//     tensor whose extents are the coordinates', and so do rank-0, rank-2 and
//     empty coordinate tensors and rank-1 and rank-3 data; every element is
//     the data's at the coordinate a hand loop reads;
//   * rank and dtype rules, each refused by the validator by its own rule
//     (G1 a result element other than the data's, G2 rank-0 data and a
//     coordinate count other than the data rank, G3 a coordinate that is not
//     an integer tensor of the result's rank), while each coordinate tensor
//     may have its own integer type (signed, unsigned, `usize`);
//   * a coordinate outside its axis (at the extent, negative, huge) and
//     coordinate tensors of different extents are undefined behaviour by
//     their normative messages, in the interpreter and in SemR;
//   * data bounds carry over: the result's element type is the data's, and
//     every gathered element lies within the data's least and greatest
//     element (the data held at its type's extremes too);
//   * SemR's `semr_eval` returns the interpreter's verdict on every run.
//
// trust-ir has no value-range facts at wire v70 (PKG-U13h), so "bounds carry
// over" is the element type and the values the runs observe.

use std::path::Path;

use trust_ir::Ty;
use trust_ir_build::{ValidationError, validate_module};
use trust_luminal_rows::{
    Differential, Row, case, coordinates, module_of, offset, tensor, tensor_value,
};

const ID: &str = "logical-ir-shapes/gather";

const EXTENTS: &str = "tensor gather: coordinate tensors have different extents";
const OUTSIDE: &str = "tensor gather: a coordinate is outside its axis";

/// `fn name(data, coords..) -> result { tensor_gather result %data coords
/// [%coords..] }`.
fn gather(name: &str, data: Ty, coords: Vec<Ty>, result: Ty) -> trust_luminal_rows::Case {
    let mut params = vec![data];
    params.extend(coords);
    let ty = result.clone();
    case(name, params, result, move |fb, p| fb.tensor_gather(ty.clone(), p[0], p[1..].to_vec()))
}

/// The accepted cases: data of rank 1, 2 and 3; coordinates of rank 0, 1 and
/// 2, each coordinate tensor its own integer type.
fn accepted() -> Vec<trust_luminal_rows::Case> {
    let i64t = || Ty::I64;
    vec![
        // The row's own form: rank-2 data, rank-1 coordinates.
        gather(
            "rows_cols",
            tensor(i64t(), 2),
            vec![tensor(Ty::I32, 1), tensor(Ty::Usize, 1)],
            tensor(i64t(), 1),
        ),
        // Rank-2 coordinates: the result is rank 2.
        gather(
            "grid",
            tensor(i64t(), 2),
            vec![tensor(Ty::U8, 2), tensor(Ty::I64, 2)],
            tensor(i64t(), 2),
        ),
        // Rank-0 coordinates: one element, a rank-0 result.
        gather(
            "point",
            tensor(i64t(), 2),
            vec![tensor(Ty::U16, 0), tensor(Ty::I8, 0)],
            tensor(i64t(), 0),
        ),
        // Rank-1 data.
        gather("vector", tensor(Ty::I32, 1), vec![tensor(Ty::U64, 1)], tensor(Ty::I32, 1)),
        // Rank-3 data at three rank-1 coordinate tensors.
        gather(
            "cube",
            tensor(Ty::U32, 3),
            vec![tensor(Ty::I16, 1), tensor(Ty::Usize, 1), tensor(Ty::U8, 1)],
            tensor(Ty::U32, 1),
        ),
    ]
}

/// A gather by a hand-written loop: for every row-major position `p` of the
/// coordinate tensors, `data`'s element at `(coords[0][p], ..)`.
fn hand(data_dims: &[u64], data: &[i128], coord_dims: &[u64], coords: &[&[i128]]) -> Vec<i128> {
    assert_eq!(data_dims.len(), coords.len());
    (0..trust_luminal_rows::count(coord_dims))
        .map(|p| {
            let at: Vec<u64> = coords
                .iter()
                .map(|c| u64::try_from(c[p]).expect("the hand loop reads in range"))
                .collect();
            data[offset(data_dims, &at)]
        })
        .collect()
}

fn matrix() -> Vec<i128> {
    // A [3, 4] i64 matrix with its type's extremes among ordinary values.
    vec![
        i128::from(i64::MIN),
        -7,
        0,
        3,
        11,
        i128::from(i64::MAX),
        -1,
        5,
        -100,
        42,
        i128::from(i64::MIN) + 1,
        9,
    ]
}

fn check_shape_and_values(d: &mut Differential<'_>) {
    let dims = [3u64, 4];
    let data = matrix();
    let x = || tensor_value(&Ty::I64, &dims, &data);

    // Rank-1 coordinates of extent 5, every row and column reached.
    let rows = [0i128, 2, 1, 2, 0];
    let cols = [3i128, 0, 1, 2, 0];
    let (elem, got_dims, got) = d.computes(
        "rows_cols",
        vec![x(), tensor_value(&Ty::I32, &[5], &rows), tensor_value(&Ty::Usize, &[5], &cols)],
    );
    assert_eq!(elem, Ty::I64, "the result element is the data's");
    assert_eq!(got_dims, vec![5], "the output shape is the coordinates' shape");
    assert_eq!(got, hand(&dims, &data, &[5], &[&rows, &cols]));

    // Empty coordinates: an empty result, nothing read.
    let (_, got_dims, got) = d.computes(
        "rows_cols",
        vec![x(), tensor_value(&Ty::I32, &[0], &[]), tensor_value(&Ty::Usize, &[0], &[])],
    );
    assert_eq!((got_dims, got), (vec![0], vec![]));

    // Rank-2 coordinates [2, 3].
    let r2 = [2i128, 2, 0, 1, 0, 2];
    let c2 = [0i128, 3, 3, 1, 2, 1];
    let (_, got_dims, got) = d.computes(
        "grid",
        vec![x(), tensor_value(&Ty::U8, &[2, 3], &r2), tensor_value(&Ty::I64, &[2, 3], &c2)],
    );
    assert_eq!(got_dims, vec![2, 3], "rank-2 coordinates give a rank-2 result");
    assert_eq!(got, hand(&dims, &data, &[2, 3], &[&r2, &c2]));

    // Rank-0 coordinates.
    let (_, got_dims, got) = d.computes(
        "point",
        vec![x(), tensor_value(&Ty::U16, &[], &[1]), tensor_value(&Ty::I8, &[], &[1])],
    );
    assert_eq!(got_dims, Vec::<u64>::new(), "rank-0 coordinates give a rank-0 result");
    assert_eq!(got, vec![data[offset(&dims, &[1, 1])]]);

    // Rank-1 data, a repeated coordinate.
    let v = [10i128, -20, 30, i128::from(i32::MIN), i128::from(i32::MAX)];
    let at = [4i128, 0, 4, 3, 1, 1];
    let (_, got_dims, got) = d.computes(
        "vector",
        vec![tensor_value(&Ty::I32, &[5], &v), tensor_value(&Ty::U64, &[6], &at)],
    );
    assert_eq!(got_dims, vec![6]);
    assert_eq!(got, hand(&[5], &v, &[6], &[&at]));

    // Rank-3 data [2, 3, 2].
    let cube_dims = [2u64, 3, 2];
    let cube: Vec<i128> = (0..12).map(|k| k * 1000 + 7).collect();
    let (a, b, c) = ([1i128, 0, 1, 0], [2i128, 0, 1, 2], [1i128, 1, 0, 0]);
    let (_, got_dims, got) = d.computes(
        "cube",
        vec![
            tensor_value(&Ty::U32, &cube_dims, &cube),
            tensor_value(&Ty::I16, &[4], &a),
            tensor_value(&Ty::Usize, &[4], &b),
            tensor_value(&Ty::U8, &[4], &c),
        ],
    );
    assert_eq!(got_dims, vec![4]);
    assert_eq!(got, hand(&cube_dims, &cube, &[4], &[&a, &b, &c]));
}

/// The validator's refusal reasons for a module of the one case `c`, each
/// `InvalidTensorGather`.
fn refusals(c: trust_luminal_rows::Case) -> Vec<String> {
    let name = c.name.clone();
    let m = module_of(&format!("refused_{name}"), &[c]);
    let errors = validate_module(&m);
    assert!(!errors.is_empty(), "{name} must be refused");
    errors
        .iter()
        .map(|e| match e {
            ValidationError::InvalidTensorGather { reason, .. } => reason.clone(),
            other => panic!("{name}: refused by InvalidTensorGather, got {other:?}"),
        })
        .collect()
}

fn assert_refused(c: trust_luminal_rows::Case, rule: &str, says: &str) {
    let name = c.name.clone();
    let reasons = refusals(c);
    assert!(
        reasons.iter().any(|r| r.starts_with(&format!("rule {rule}:")) && r.contains(says)),
        "{name}: refused by rule {rule} ({says}), got {reasons:?}"
    );
}

fn check_rank_and_dtype_rules() {
    // Each accepted case validates, with mixed integer coordinate types.
    trust_luminal_rows::assert_validates(&module_of("accepted", &accepted()));
    // Rank-0 data is refused (Luminal refuses it too).
    assert_refused(
        gather("rank0_data", tensor(Ty::I64, 0), vec![], tensor(Ty::I64, 0)),
        "G2",
        "rank-0 data has no axis to index",
    );
    // One coordinate tensor per data axis: one too few, one too many.
    assert_refused(
        gather("too_few", tensor(Ty::I64, 2), vec![tensor(Ty::Usize, 1)], tensor(Ty::I64, 1)),
        "G2",
        "1 coordinate operands for data of rank 2",
    );
    assert_refused(
        gather(
            "too_many",
            tensor(Ty::I64, 2),
            vec![tensor(Ty::Usize, 1), tensor(Ty::Usize, 1), tensor(Ty::Usize, 1)],
            tensor(Ty::I64, 1),
        ),
        "G2",
        "3 coordinate operands for data of rank 2",
    );
    // The coordinates share one rank, the result's.
    assert_refused(
        gather(
            "ranks_differ",
            tensor(Ty::I64, 2),
            vec![tensor(Ty::Usize, 1), tensor(Ty::Usize, 2)],
            tensor(Ty::I64, 1),
        ),
        "G3",
        "coordinate operand 1",
    );
    assert_refused(
        gather(
            "result_rank",
            tensor(Ty::I64, 2),
            vec![tensor(Ty::Usize, 1), tensor(Ty::Usize, 1)],
            tensor(Ty::I64, 2),
        ),
        "G3",
        "not an integer tensor of rank 2",
    );
    // A coordinate is an integer TENSOR: a scalar is refused.
    assert_refused(
        gather("scalar_coord", tensor(Ty::I64, 1), vec![Ty::Usize], tensor(Ty::I64, 0)),
        "G3",
        "coordinate operand 0 has type usize",
    );
    // The result's element is the data's.
    assert_refused(
        gather(
            "result_elem",
            tensor(Ty::I64, 2),
            vec![tensor(Ty::Usize, 1), tensor(Ty::Usize, 1)],
            tensor(Ty::I32, 1),
        ),
        "G1",
        "the data has type tensor<i64, 2>",
    );
}

fn check_out_of_range_is_undefined_behaviour(d: &mut Differential<'_>) {
    let dims = [3u64, 4];
    let x = || tensor_value(&Ty::I64, &dims, &matrix());
    let run = |d: &mut Differential<'_>, rows: &[i128], cols: &[i128], message: &str| {
        d.ub(
            "rows_cols",
            vec![
                x(),
                tensor_value(&Ty::I32, &[rows.len() as u64], rows),
                tensor_value(&Ty::Usize, &[cols.len() as u64], cols),
            ],
            message,
        );
    };
    // At the extent, on either axis.
    run(d, &[0, 3], &[0, 0], OUTSIDE);
    run(d, &[0, 1], &[4, 0], OUTSIDE);
    // Negative (a signed coordinate type).
    run(d, &[1, -1], &[0, 0], OUTSIDE);
    // Huge (an unsigned coordinate past every extent).
    run(d, &[0, 0], &[0, i128::from(u64::MAX)], OUTSIDE);
    // The last position only: the whole gather is undefined.
    run(d, &[0, 1, 2, 2, 3], &[0, 1, 2, 3, 3], OUTSIDE);
    // Coordinate tensors of different extents.
    run(d, &[0, 1, 2], &[0, 1], EXTENTS);
    // Rank-1 data, the coordinate at the extent.
    d.ub(
        "vector",
        vec![tensor_value(&Ty::I32, &[2], &[1, 2]), tensor_value(&Ty::U64, &[1], &[2])],
        OUTSIDE,
    );
    // Empty data: every coordinate is outside.
    d.ub(
        "vector",
        vec![tensor_value(&Ty::I32, &[0], &[]), tensor_value(&Ty::U64, &[1], &[0])],
        OUTSIDE,
    );
}

fn check_bounds_carry_over(d: &mut Differential<'_>) {
    // Data at its type's extremes, gathered at every coordinate once.
    let dims = [3u64, 4];
    let data = matrix();
    let all = coordinates(&dims);
    let rows: Vec<i128> = all.iter().map(|c| i128::from(c[0])).collect();
    let cols: Vec<i128> = all.iter().map(|c| i128::from(c[1])).collect();
    let (elem, _, got) = d.computes(
        "rows_cols",
        vec![
            tensor_value(&Ty::I64, &dims, &data),
            tensor_value(&Ty::I32, &[12], &rows),
            tensor_value(&Ty::Usize, &[12], &cols),
        ],
    );
    assert_eq!(elem, Ty::I64, "the element type carries over");
    assert_eq!(got, data, "a gather at every coordinate in order is the data");
    let (lo, hi) = (*data.iter().min().expect("data"), *data.iter().max().expect("data"));
    // And at repeated, scattered coordinates: every element within the
    // data's least and greatest.
    let rows = [1i128, 1, 0, 2, 2, 0, 1];
    let cols = [1i128, 1, 0, 2, 0, 3, 0];
    let (_, _, got) = d.computes(
        "rows_cols",
        vec![
            tensor_value(&Ty::I64, &dims, &data),
            tensor_value(&Ty::I32, &[7], &rows),
            tensor_value(&Ty::Usize, &[7], &cols),
        ],
    );
    assert!(
        got.iter().all(|v| (lo..=hi).contains(v) && data.contains(v)),
        "every gathered element is one of the data's: {got:?}"
    );
    assert!(got.contains(&lo) && got.contains(&hi), "both extremes reached");
}

fn main() {
    let m = module_of("luminal_gather", &accepted());
    let mut d = Differential::new(&m);
    let mut row = Row::new(ID);
    row.check("shape: the output shape is the coordinates' shape", || {
        check_shape_and_values(&mut d)
    });
    row.check("rank and dtype rules are validator refusals", check_rank_and_dtype_rules);
    row.check("an out-of-range coordinate is undefined behaviour", || {
        check_out_of_range_is_undefined_behaviour(&mut d)
    });
    row.check("data bounds carry over", || check_bounds_carry_over(&mut d));
    let semr = d.semr(Path::new(env!("CARGO_TARGET_TMPDIR")));
    row.finish(semr);
}
