// Trust (RANGE-FOLD-MID-DEF-1, 2026-10-11): regression test for a wrong-code bug in
// `MatchBranchSimplification`'s contiguous-range fold (`simplify_range_comparison`,
// rust-lang#123305). The fold rewrites
//   bb0: _c1 = Le(const lo, copy x); switchInt(_c1) -> [0: out, otherwise: mid]
//   mid: _c2 = Le(copy x, const hi); switchInt(_c2) -> [0: out, otherwise: in]
// into one `x - lo <= hi - lo` test in bb0 that jumps straight to `in`. That skips `mid`'s
// assignment to `_c2` on every path out of bb0 (the in-range path, and the `x > hi` path that
// used to write `false`), and the trailing `simplify_cfg` usually deletes `mid`. The fold only
// checked that `_c1` was read nowhere else, never `_c2`, so a later read of `_c2` saw a stale or
// uninitialized value. The fix declines the fold whenever `_c2` is mentioned anywhere other than
// `mid`'s own definition and terminator.
//
// * `user_var`: `_c2` is the user variable `b`, read after the join, so the function returned
//   the initial `false` for every x in 10..=20.
// * `gvn_loop`: `_c2` is a match temp that GVN reuses for the loop's `matches!(x, 0..=20)`. The
//   loop header has two predecessors, so SsaRangePropagation cannot fold that read to `true`,
//   and it read a local nothing writes (LLVM folded `gvn_loop(15, 3)` to 0).
// * `gvn_branch`: the same reuse, branched on (the loop arm LLVM deleted).
// * `straight_line`: the reuse without a loop. SsaRangePropagation folds the read to `true`
//   first and masks the bug at plain -O, so the `nosrp` revision disables it to keep the pin
//   independent of that pass.
//
// The program collects every mismatch and panics once at the end, so a run lists each broken
// function rather than only the first.
//
// BEFORE (2026-10-11, the stage 1 of integ7 after wave 23, main = 1213387e6d, at
// `scratchpad/stage1-w24probe/bin/rustc`): `rustc --edition 2021 --cfg <rev> -Ccodegen-units=1
// -Ztrust-verify=off <the revision's flags>`, then run the binary:
//   o1, o3, os: exit 101, `user_var: 11 wrong (first: user_var(10) = false, want true)`,
//               `gvn_loop: 11 wrong (first: gvn_loop(10, 3) = 0, want 3)`,
//               `gvn_branch: 11 wrong (first: gvn_branch(10, 3) = 0, want 6)`
//   nosrp:      exit 101, the same three lines plus
//               `straight_line: 11 wrong (first: straight_line(10, 3) = 3, want 4)`
// Every revision exits 0 with `-Zmir-enable-passes=-MatchBranchSimplification` added on the
// same compiler, and on stock rustc 1.97.1 (`~/.rustup/toolchains/1.97.1-aarch64-apple-darwin`,
// the same flags minus `-Ztrust-verify=off`; `nosrp` there via `RUSTC_BOOTSTRAP=1`).
// AFTER (predicted; not built in the lane): every revision exits 0.

//@ run-pass
//@ edition: 2021
//@ revisions: o1 o3 os nosrp
//@ compile-flags: -Ztrust-verify=off
//@[o1] compile-flags: -O
//@[o3] compile-flags: -Copt-level=3
//@[os] compile-flags: -Copt-level=s
//@[nosrp] compile-flags: -O -Zmir-enable-passes=-SsaRangePropagation

use std::hint::black_box;

#[inline(never)]
fn user_var(x: u8) -> bool {
    let mut b = false;
    if let 10.. = x {
        b = x <= 20;
        if let true = b {
            black_box(());
        }
    }
    b
}

#[inline(never)]
fn gvn_loop(x: u8, n: u32) -> u32 {
    let mut acc = 0u32;
    let mut i = 0u32;
    if let 10..=20 = x {
        loop {
            acc += matches!(x, 0..=20) as u32;
            i += 1;
            if i == n {
                break;
            }
        }
    }
    acc
}

#[inline(never)]
fn gvn_branch(x: u8, n: u32) -> u32 {
    let mut acc = 0u32;
    let mut i = 0u32;
    if let 10..=20 = x {
        loop {
            if matches!(x, 0..=20) {
                acc += black_box(2);
            } else {
                acc += black_box(5) * 3;
            }
            i += 1;
            if i == n {
                break;
            }
        }
    }
    acc
}

#[inline(never)]
fn straight_line(x: u8, n: u32) -> u32 {
    match x {
        10..=20 => n + matches!(x, 0..=20) as u32,
        _ => 0,
    }
}

/// Records how many inputs `name` got wrong, with the first one.
fn check<T: PartialEq + std::fmt::Debug>(
    failures: &mut Vec<String>,
    name: &str,
    cases: impl Iterator<Item = (String, T, T)>,
) {
    let mut wrong = 0;
    let mut first = None;
    for (call, got, want) in cases {
        if got != want {
            wrong += 1;
            first.get_or_insert(format!("{call} = {got:?}, want {want:?}"));
        }
    }
    if let Some(first) = first {
        failures.push(format!("{name}: {wrong} wrong (first: {first})"));
    }
}

fn main() {
    let n = black_box(3u32);
    let inside = |x: u8| (10..=20).contains(&x);
    let mut failures = Vec::new();

    check(
        &mut failures,
        "user_var",
        (0..=u8::MAX).map(|x| (format!("user_var({x})"), user_var(black_box(x)), inside(x))),
    );
    check(
        &mut failures,
        "gvn_loop",
        (0..=u8::MAX).map(|x| {
            let want = if inside(x) { n } else { 0 };
            (format!("gvn_loop({x}, {n})"), gvn_loop(black_box(x), n), want)
        }),
    );
    check(
        &mut failures,
        "gvn_branch",
        (0..=u8::MAX).map(|x| {
            let want = if inside(x) { 2 * n } else { 0 };
            (format!("gvn_branch({x}, {n})"), gvn_branch(black_box(x), n), want)
        }),
    );
    check(
        &mut failures,
        "straight_line",
        (0..=u8::MAX).map(|x| {
            let want = if inside(x) { n + 1 } else { 0 };
            (format!("straight_line({x}, {n})"), straight_line(black_box(x), n), want)
        }),
    );

    assert!(failures.is_empty(), "\n{}", failures.join("\n"));
}
