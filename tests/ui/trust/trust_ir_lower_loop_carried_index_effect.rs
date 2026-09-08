//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-LCX): the loop-carried-assignment collector must see an
//! assignment nested inside an INDEX subexpression.
//!
//! `effectful_index_read` is the WITNESS of a live wrong-value bug this wave
//! fixes: before it, the body reported `clean=true` while the value
//! differential measured `mode=MirOracle, equal=false` — the block's
//! `k = k + 1` was invisible to `collect_assigned_into` (its Binary/Assign
//! arms never descended into an `ExprKind::Index`), so `k` was not carried,
//! every iteration read the PRE-LOOP `k`, and the sum came out 60 where the
//! real program computes 90.
//!
//! `run-pass` is the point: the values are checked against real execution, so
//! a regression to the blind collector fails here as a wrong VALUE rather than
//! merely changing a count.
//!
//! `separate_statement_control` is the minimal pair that was ALWAYS correct
//! (the collector's Block arm sees a statement-level assignment), kept so the
//! fix cannot silently narrow it.

/// The witness: the index expression carries the mutation.
pub fn effectful_index_read() -> i64 {
    let a = [10i64, 20, 30, 40];
    let mut s = 0i64;
    let mut k = 0usize;
    let mut i = 0;
    while i < 3 {
        s = s + a[{
            k = k + 1;
            k
        }];
        i += 1;
    }
    s
}

/// The write-side twin: the STORE's index subexpression carries the mutation.
pub fn effectful_index_write() -> i64 {
    let mut a = [0i64; 4];
    let mut k = 0usize;
    let mut i = 0;
    while i < 4 {
        a[{
            k = k + 1;
            k - 1
        }] = i as i64;
        i += 1;
    }
    a[0] + a[1] * 10 + a[2] * 100 + a[3] * 1000
}

/// The minimal pair: the same mutation as a separate statement — always seen.
pub fn separate_statement_control() -> i64 {
    let a = [10i64, 20, 30, 40];
    let mut s = 0i64;
    let mut k = 0usize;
    let mut i = 0;
    while i < 3 {
        k = k + 1;
        s = s + a[k];
        i += 1;
    }
    s
}

fn main() {
    assert_eq!(effectful_index_read(), 90);
    assert_eq!(effectful_index_write(), 3210);
    assert_eq!(separate_statement_control(), 90);
}
