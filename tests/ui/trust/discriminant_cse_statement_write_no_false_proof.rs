//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ compile-flags: -Ztrust-verify-output=json --error-format=human
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//@ forbid-output: "line_start":47,"col_start":39,"line_end":47,"col_end":46},"outcome":"proved"
//@ forbid-output: "line_start":64,"col_start":19,"line_end":64,"col_end":23},"outcome":"proved"
//! DISC-CSE-PRE-BARRIER-WRITE-1: under `-Ztrust-policy=certify`, a discriminant tie
//! across a plain statement write certified two false rows in safe Rust.
//!
//! `build_discriminant_cse_facts` grouped `discriminant(*&cur)` before and after
//! `cur = None` (and `discriminant(*&s)` around `s = S::Busy`) by their canonical
//! referent and tied them, because neither read follows a `Call`/`Drop`/`Opaque`. The
//! tie made the second arm infeasible: `assign`'s `v + 255` overflow row and `idx`'s
//! `a[i]` bounds row were PROVED and kernel-certified, and the certify build succeeded.
//! `assign(1)` panics "attempt to add with overflow" and `idx(&[1, 2, 3, 4], 9)` panics
//! "index out of bounds" (`discriminant_cse_statement_write_run.rs` is the run twin).
//!
//! The `forbid-output` lines name the two rows' JSON verdicts by span: neither may come
//! out `proved`. The check build must fail: each row is now a real refutation.
//!
//! BEFORE (measured 2026-10-12 on the wave-25 probe stage 1, `scratchpad/stage1-w25probe`,
//! with exactly these flags): exit 0, and the JSON carries both forbidden rows with
//! `"outcome":"proved"`. Without the two JSON flags the same build exits 0 and
//! `assign` and `idx` each report "2 proved, 0 failed ... of which 2 kernel-certified
//! by the clean CIC kernel".
//!
//! AFTER (measured 2026-10-13, the integ/wave25 stage 1): a pre-barrier tie needs a
//! body-stable referent or a frozen shared-reference parameter's pointee; `cur` and `s`
//! are each assigned twice, so no tie is made, both rows are refuted and certify exits 1,
//! as the barrier and by-value controls of the scout's `ctl.rs` already were. trust-vcgen's
//! `tests/discriminant_cse_statement_write_realmir.rs` measures the row verdicts on the
//! compiler's own extraction of these bodies. Do not "fix" this file by deleting a
//! `forbid-output` line: each forbidden row is a panic the run twin reaches.

pub fn assign(v: u8) -> u8 {
    let mut cur = Some(v);
    if let None = &cur {
        return 0;
    }
    cur = None;
    if let Some(_) = &cur { 0 } else { v + 255 }
}

#[derive(Clone, Copy)]
pub enum S {
    Idle,
    Busy,
}

pub fn idx(a: &[u8; 4], i: usize) -> u8 {
    let mut s = S::Idle;
    if let S::Busy = &s {
        return 0;
    }
    s = S::Busy;
    match &s {
        S::Idle => 0,
        S::Busy => a[i],
    }
}
