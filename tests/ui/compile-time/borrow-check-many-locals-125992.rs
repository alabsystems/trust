// Trust: regression test for compile-time bug rust-lang#125992
//
// O(n^3) behavior in borrow checking with many local variables. The borrow
// checker's dataflow analysis tracks initialization and borrow state for
// each local across each program point. With N locals and M program points,
// certain operations (particularly those involving overlap checks between
// borrows) can degrade to O(N^2 * M) or O(N^3) when many locals are live
// simultaneously and interact through borrows.
//
// The original report showed multi-second compile times for functions with
// ~100+ locals. This test uses 60 locals with interleaved borrows to
// exercise the cubic dataflow path without excessive compile time.
//
// Upstream: https://github.com/rust-lang/rust/issues/125992
// Tracked in Trust: #865
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//@ check-pass

fn many_locals_with_borrows() -> i64 {
    // Create many locals that are all live simultaneously.
    let mut v0: i64 = 0;
    let mut v1: i64 = 1;
    let mut v2: i64 = 2;
    let mut v3: i64 = 3;
    let mut v4: i64 = 4;
    let mut v5: i64 = 5;
    let mut v6: i64 = 6;
    let mut v7: i64 = 7;
    let mut v8: i64 = 8;
    let mut v9: i64 = 9;
    let mut v10: i64 = 10;
    let mut v11: i64 = 11;
    let mut v12: i64 = 12;
    let mut v13: i64 = 13;
    let mut v14: i64 = 14;
    let mut v15: i64 = 15;
    let mut v16: i64 = 16;
    let mut v17: i64 = 17;
    let mut v18: i64 = 18;
    let mut v19: i64 = 19;
    let mut v20: i64 = 20;
    let mut v21: i64 = 21;
    let mut v22: i64 = 22;
    let mut v23: i64 = 23;
    let mut v24: i64 = 24;
    let mut v25: i64 = 25;
    let mut v26: i64 = 26;
    let mut v27: i64 = 27;
    let mut v28: i64 = 28;
    let mut v29: i64 = 29;

    // Interleaved mutable borrows force the borrow checker to track
    // overlapping liveness ranges for all locals at each program point.
    // This is the pattern that triggers O(n^3) behavior.
    v0 += v1; v1 += v2; v2 += v3; v3 += v4; v4 += v5;
    v5 += v6; v6 += v7; v7 += v8; v8 += v9; v9 += v10;
    v10 += v11; v11 += v12; v12 += v13; v13 += v14; v14 += v15;
    v15 += v16; v16 += v17; v17 += v18; v18 += v19; v19 += v20;
    v20 += v21; v21 += v22; v22 += v23; v23 += v24; v24 += v25;
    v25 += v26; v26 += v27; v27 += v28; v28 += v29; v29 += v0;

    // Second pass: more interleaved mutations to increase program points.
    v0 += v29; v1 += v0; v2 += v1; v3 += v2; v4 += v3;
    v5 += v4; v6 += v5; v7 += v6; v8 += v7; v9 += v8;
    v10 += v9; v11 += v10; v12 += v11; v13 += v12; v14 += v13;
    v15 += v14; v16 += v15; v17 += v16; v18 += v17; v19 += v18;
    v20 += v19; v21 += v20; v22 += v21; v23 += v22; v24 += v23;
    v25 += v24; v26 += v25; v27 += v26; v28 += v27; v29 += v28;

    // Sum them all — all locals are used so none are optimized away.
    v0 + v1 + v2 + v3 + v4 + v5 + v6 + v7 + v8 + v9
    + v10 + v11 + v12 + v13 + v14 + v15 + v16 + v17 + v18 + v19
    + v20 + v21 + v22 + v23 + v24 + v25 + v26 + v27 + v28 + v29
}

fn main() {
    let result = many_locals_with_borrows();
    assert!(result > 0);
}
