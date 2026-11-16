// Trust (2026-09-25, W4 ALLOC-LEN adversarial round 1): a large-coefficient row
// must not hold the compiler in clean_auto's proof reconstruction.
//
// `A01` is VERBATIM the violation formula that the w4-alloc-str stage-1 trustc
// (`0.10.0+gab7e41892` + b06b56569a) handed `trust_certify` for probe a01's
// capacity-only `unbounded_allocation` row, captured with
//
// ```text
// AY_CERT_DUMP=1 trustc --edition 2021 --crate-type rlib a01_wide_target_avail.rs
// ```
//
// for `pub fn f(s: &[u8]) -> Vec<[u8; 1 << 30]> { if s.len() < (1usize << 32)
// { Vec::with_capacity(s.len()) } else { Vec::new() } }`. The row is TRUE (UNSAT:
// `_7 = s_len = _3 < 2^32` against `2^30 · _7 ≥ 2^63`), ay proved it, and then
// `certify_linear_int_fragment` handed ay's proof to clean_auto, whose symbolic
// additive closeout expanded the `2^30` Farkas multiplier into a TREE of 2^30
// copies of each alias bound: the compile recursed in `IntAddNf::flatten` for
// more than 11 minutes at a 184 GB footprint. vcgen no longer emits this row
// for a01 (its availability ceiling is kept), but the shape is still reachable
// (a two-term count over wide array elements), so the gate is what these tests
// pin — every call runs under a watchdog, so a regression FAILS instead of
// hanging the suite.
//
// Round 2 (2026-09-26): round 1's gate capped the pool's LARGEST coefficient,
// and the adversarial re-probe got past it with coefficients all at most 2^12
// whose certificate MULTIPLIES them: `B45` (t23's `String::with_capacity(a.len()
// + b.len())` under `a.len() * 4093 < 2^60 ∧ b.len() * 4091 < 2^60`; ay's
// Farkas coefficients are `4093/4091`, so clean_auto's integer multipliers are
// `4093 · 4091 ≈ 2^24`: 37.7 GB in 38 s on the round-1 compiler) and `B48`, the
// same guards over a plain bounds check, which blows up on origin/main too
// (38 GB in 30 s). Both are now declined before the solve by the pool's
// coefficient PRODUCT (gate 1 in `reconstruction_scale.rs`), and each would be
// declined again after it by the leaves ay's actual certificate expands to
// (gate 2: measured with gate 1 held at round 1's maximum, 2026-09-26, `B45`'s
// certificate is ~4.7e8 leaves and `B48`'s ~4.0e8, against a cap of 2^12).
// With both gates disabled, each test was killed at a 6 GB RSS limit within
// 15-21 s instead of returning (measured at the old clean pin `336d20039`;
// clean `0f4b211a0`'s own leaf cap, in the pin since `ca1ef61a3a`, now bounds
// the closeout inside clean_auto as well).
//
// Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.

use std::sync::mpsc;
use std::time::Duration;

use trust_types::{Formula, Sort};

const A01: &str = r###"And([And([Ge(Var("_4", Int), Int(0)), Le(Var("_4", Int), Int(18446744073709551615))]), And([Le(Var("_5", Int), Int(32)), And([Eq(Var("_3", Int), Var("s__slice_len", Int)), Eq(Var("_5", Int), Int(32)), Eq(Var("_6", Bool), Lt(Var("_5", Int), Int(64))), Eq(Var("_4", Int), Int(4294967296)), Eq(Var("_2", Bool), Lt(Var("_3", Int), Var("_4", Int))), And([Var("_6", Bool), Lt(Var("_3", Int), Var("_4", Int)), And([Le(Int(0), Var("_7", Int)), Le(Var("_7", Int), Int(18446744073709551615))]), And([Eq(Var("_7", Int), Var("s__slice_len", Int)), Ge(Mul(Int(1073741824), Var("_7", Int)), Int(9223372036854775808))])])])])])"###;

/// VERBATIM the violation the round-1 stage-1 trustc handed `trust_certify` for
/// probe b45's capacity-only `unbounded_allocation` row (`AY_CERT_DUMP=1`,
/// 2026-09-26):
///
/// ```text
/// pub fn f(a: &str, b: &str) -> String {
///     if a.len() * 4093 < (1usize << 60) && b.len() * 4091 < (1usize << 60) {
///         String::with_capacity(a.len() + b.len())
///     } else { String::new() }
/// }
/// ```
///
/// TRUE: the guards bound the count below `2^49`, and the row asks `≥ 2^63`.
const B45: &str = r###"And([And([Ge(Var("_14", Int), Int(0)), Le(Var("_14", Int), Int(18446744073709551615)), Ge(Var("_7", Int), Int(0)), Le(Var("_7", Int), Int(18446744073709551615))]), And([Eq(Var("_5", Int), Var("a__slice_len", Int)), Eq(Var("_12", Int), Var("b__slice_len", Int)), Eq(Var("_18", Int), Var("a__slice_len", Int)), Eq(Var("_19", Int), Var("b__slice_len", Int)), Or([Gt(Add(Var("_18", Int), Var("_19", Int)), Int(18446744073709551615)), Eq(Var("_17", Int), Add(Var("_18", Int), Var("_19", Int)))]), Le(Var("_8", Int), Int(60)), Le(Var("_15", Int), Int(60)), And([Ge(Var("_5", Int), Int(0)), Le(Var("_5", Int), Int(9223372036854775807)), And([Le(Int(0), Mul(Var("_5", Int), Int(4093))), Le(Mul(Var("_5", Int), Int(4093)), Int(18446744073709551615))]), Eq(Var("_6.0#s1_0", Int), Mul(Var("_5", Int), Int(4093))), And([Le(Int(0), Var("_5", Int)), Le(Var("_5", Int), Int(18446744073709551615))]), And([Le(Int(0), Int(4093)), Le(Int(4093), Int(18446744073709551615))]), Eq(Var("_4", Int), Var("_6.0#s1_0", Int)), Eq(Var("_8", Int), Int(60)), Eq(Var("_9", Bool), Lt(Var("_8", Int), Int(64))), Eq(Var("_7", Int), Int(1152921504606846976)), Eq(Var("_3", Bool), Lt(Var("_4", Int), Var("_7", Int))), Ge(Var("_12", Int), Int(0)), Le(Var("_12", Int), Int(9223372036854775807)), And([Le(Int(0), Mul(Var("_12", Int), Int(4091))), Le(Mul(Var("_12", Int), Int(4091)), Int(18446744073709551615))]), Eq(Var("_13.0#s5_0", Int), Mul(Var("_12", Int), Int(4091))), And([Le(Int(0), Var("_12", Int)), Le(Var("_12", Int), Int(18446744073709551615))]), And([Le(Int(0), Int(4091)), Le(Int(4091), Int(18446744073709551615))]), Eq(Var("_11", Int), Var("_13.0#s5_0", Int)), Eq(Var("_15", Int), Int(60)), Eq(Var("_16", Bool), Lt(Var("_15", Int), Int(64))), Eq(Var("_14", Int), Int(1152921504606846976)), Eq(Var("_10", Bool), Lt(Var("_11", Int), Var("_14", Int))), Ge(Var("_18", Int), Int(0)), Le(Var("_18", Int), Int(9223372036854775807)), Ge(Var("_19", Int), Int(0)), Le(Var("_19", Int), Int(9223372036854775807)), And([Le(Int(0), Add(Var("_18", Int), Var("_19", Int))), Le(Add(Var("_18", Int), Var("_19", Int)), Int(18446744073709551615))]), Eq(Var("_20.0#s10_0", Int), Add(Var("_18", Int), Var("_19", Int))), And([Le(Int(0), Var("_18", Int)), Le(Var("_18", Int), Int(18446744073709551615))]), And([Le(Int(0), Var("_19", Int)), Le(Var("_19", Int), Int(18446744073709551615))]), And([Not(Var("_6.1#s1_0", Bool)), Var("_9", Bool), Lt(Var("_4", Int), Var("_7", Int)), Not(Var("_13.1#s5_0", Bool)), Var("_16", Bool), Lt(Var("_11", Int), Var("_14", Int)), Not(Var("_20.1#s10_0", Bool)), And([Le(Int(0), Var("_20.0#s10_0", Int)), Le(Var("_20.0#s10_0", Int), Int(18446744073709551615))]), And([And([Le(Int(0), Var("_17", Int)), Le(Var("_17", Int), Int(18446744073709551615))]), And([Eq(Var("_17", Int), Var("_20.0#s10_0", Int)), Ge(Mul(Int(1), Var("_17", Int)), Int(9223372036854775808))])])])])])])"###;

/// VERBATIM the violation of probe b48's `big[c]` bounds check (origin/main
/// reaches it; `AY_CERT_DUMP=1` on the round-1 stage-1 trustc, 2026-09-26):
///
/// ```text
/// pub fn f(a: &str, b: &str, big: &[u8; 1 << 12]) -> u8 {
///     let c = a.len() + b.len();
///     if a.len() * 4093 < (1usize << 22) && b.len() * 4091 < (1usize << 22) {
///         big[c]
///     } else { 0 }
/// }
/// ```
///
/// TRUE: `c < 2 · 1025 < 4096`.
const B48: &str = r###"And([And([Ge(Var("_12", Int), Int(0)), Le(Var("_12", Int), Int(18446744073709551615)), Ge(Var("_19", Int), Int(0)), Le(Var("_19", Int), Int(18446744073709551615))]), And([Ge(Var("_5", Int), Int(0)), Le(Var("_5", Int), Int(9223372036854775807)), Ge(Var("_6", Int), Int(0)), Le(Var("_6", Int), Int(9223372036854775807)), And([Le(Int(0), Add(Var("_5", Int), Var("_6", Int))), Le(Add(Var("_5", Int), Var("_6", Int)), Int(18446744073709551615))]), Eq(Var("_7.0#s2_0", Int), Add(Var("_5", Int), Var("_6", Int))), And([Le(Int(0), Var("_5", Int)), Le(Var("_5", Int), Int(18446744073709551615))]), And([Le(Int(0), Var("_6", Int)), Le(Var("_6", Int), Int(18446744073709551615))]), Eq(Var("c", Int), Var("_7.0#s2_0", Int)), Ge(Var("_10", Int), Int(0)), Le(Var("_10", Int), Int(9223372036854775807)), And([Le(Int(0), Mul(Var("_10", Int), Int(4093))), Le(Mul(Var("_10", Int), Int(4093)), Int(18446744073709551615))]), Eq(Var("_11.0#s4_0", Int), Mul(Var("_10", Int), Int(4093))), And([Le(Int(0), Var("_10", Int)), Le(Var("_10", Int), Int(18446744073709551615))]), And([Le(Int(0), Int(4093)), Le(Int(4093), Int(18446744073709551615))]), Eq(Var("_9", Int), Var("_11.0#s4_0", Int)), Eq(Var("_13", Int), Int(22)), Eq(Var("_14", Bool), Lt(Var("_13", Int), Int(64))), Eq(Var("_12", Int), Int(4194304)), Eq(Var("_8", Bool), Lt(Var("_9", Int), Var("_12", Int))), Ge(Var("_17", Int), Int(0)), Le(Var("_17", Int), Int(9223372036854775807)), And([Le(Int(0), Mul(Var("_17", Int), Int(4091))), Le(Mul(Var("_17", Int), Int(4091)), Int(18446744073709551615))]), Eq(Var("_18.0#s8_0", Int), Mul(Var("_17", Int), Int(4091))), And([Le(Int(0), Var("_17", Int)), Le(Var("_17", Int), Int(18446744073709551615))]), And([Le(Int(0), Int(4091)), Le(Int(4091), Int(18446744073709551615))]), Eq(Var("_16", Int), Var("_18.0#s8_0", Int)), Eq(Var("_20", Int), Int(22)), Eq(Var("_21", Bool), Lt(Var("_20", Int), Int(64))), Eq(Var("_19", Int), Int(4194304)), Eq(Var("_15", Bool), Lt(Var("_16", Int), Var("_19", Int))), And([Not(Var("_7.1#s2_0", Bool)), Not(Var("_11.1#s4_0", Bool)), Var("_14", Bool), Lt(Var("_9", Int), Var("_12", Int)), Not(Var("_18.1#s8_0", Bool)), Var("_21", Bool), Lt(Var("_16", Int), Var("_19", Int)), Eq(Var("_5", Int), Var("a__slice_len", Int)), Eq(Var("_6", Int), Var("b__slice_len", Int)), Eq(Var("_10", Int), Var("a__slice_len", Int)), Eq(Var("_17", Int), Var("b__slice_len", Int)), Or([Gt(Add(Var("_5", Int), Var("_6", Int)), Int(18446744073709551615)), Eq(Var("c", Int), Add(Var("_5", Int), Var("_6", Int)))]), Le(Var("_13", Int), Int(22)), Le(Var("_20", Int), Int(22)), And([Eq(Var("_5", Int), Var("a", Int)), Eq(Var("_6", Int), Var("b", Int)), And([Le(Int(0), Add(Var("_5", Int), Var("_6", Int))), Le(Add(Var("_5", Int), Var("_6", Int)), Int(18446744073709551615))]), Eq(Var("_7.0#s2_0", Int), Add(Var("_5", Int), Var("_6", Int))), And([Le(Int(0), Var("_5", Int)), Le(Var("_5", Int), Int(18446744073709551615))]), And([Le(Int(0), Var("_6", Int)), Le(Var("_6", Int), Int(18446744073709551615))]), Eq(Var("c", Int), Var("_7.0#s2_0", Int)), Eq(Var("_10", Int), Var("a", Int)), And([Le(Int(0), Mul(Var("_10", Int), Int(4093))), Le(Mul(Var("_10", Int), Int(4093)), Int(18446744073709551615))]), Eq(Var("_11.0#s4_0", Int), Mul(Var("_10", Int), Int(4093))), And([Le(Int(0), Var("_10", Int)), Le(Var("_10", Int), Int(18446744073709551615))]), And([Le(Int(0), Int(4093)), Le(Int(4093), Int(18446744073709551615))]), Eq(Var("_9", Int), Var("_11.0#s4_0", Int)), Eq(Var("_13", Int), Int(22)), Eq(Var("_14", Bool), Lt(Var("_13", Int), Int(64))), Eq(Var("_12", Int), Int(4194304)), Eq(Var("_8", Bool), Lt(Var("_9", Int), Var("_12", Int))), Eq(Var("_17", Int), Var("b", Int)), And([Le(Int(0), Mul(Var("_17", Int), Int(4091))), Le(Mul(Var("_17", Int), Int(4091)), Int(18446744073709551615))]), Eq(Var("_18.0#s8_0", Int), Mul(Var("_17", Int), Int(4091))), And([Le(Int(0), Var("_17", Int)), Le(Var("_17", Int), Int(18446744073709551615))]), And([Le(Int(0), Int(4091)), Le(Int(4091), Int(18446744073709551615))]), Eq(Var("_16", Int), Var("_18.0#s8_0", Int)), Eq(Var("_20", Int), Int(22)), Eq(Var("_21", Bool), Lt(Var("_20", Int), Int(64))), Eq(Var("_19", Int), Int(4194304)), Eq(Var("_15", Bool), Lt(Var("_16", Int), Var("_19", Int))), And([Eq(Var("_22", Bool), Lt(Var("c", Int), Int(4096))), Ge(Var("c", Int), Int(4096))])])])])])"###;

/// The capacity atom of `A01`, for the coefficient variants below.
const A01_CAPACITY_ATOM: &str =
    r###"Ge(Mul(Int(1073741824), Var("_7", Int)), Int(9223372036854775808))"###;

/// Well past anything the gate lets through, and generous for a loaded machine:
/// a gated decline returns in milliseconds, the ungated a01 row never returns.
const WATCHDOG: Duration = Duration::from_secs(180);

/// `A01` with its capacity atom's coefficient replaced.
fn with_coefficient(coefficient: u64) -> String {
    assert!(A01.contains(A01_CAPACITY_ATOM), "the capture's capacity atom moved");
    A01.replace(
        A01_CAPACITY_ATOM,
        &format!(r###"Ge(Mul(Int({coefficient}), Var("_7", Int)), Int(9223372036854775808))"###),
    )
}

/// `Some(certified)` when `certify_violation` returns inside [`WATCHDOG`],
/// `None` when it does not (the thread is abandoned; the process exit reaps it).
fn certify_within_watchdog(text: &str) -> Option<bool> {
    let formula = parse(text);
    let (tx, rx) = mpsc::channel();
    std::thread::Builder::new()
        .name("certify-under-watchdog".into())
        .spawn(move || {
            let _ = tx.send(trust_certify::certify_violation(&formula).is_some());
        })
        .expect("spawn");
    rx.recv_timeout(WATCHDOG).ok()
}

#[test]
fn the_captured_a01_row_returns_promptly_and_uncertified() {
    assert_eq!(
        certify_within_watchdog(A01),
        Some(false),
        "the 2^30-coefficient row must be declined by the reconstruction-scale gate, \
         not expanded by clean_auto (None = still running at the watchdog)"
    );
}

#[test]
fn one_past_the_cap_declines_promptly() {
    assert_eq!(certify_within_watchdog(&with_coefficient((1 << 12) + 1)), Some(false));
}

#[test]
fn the_b45_coprime_guarded_capacity_row_returns_promptly_and_uncertified() {
    assert_eq!(
        certify_within_watchdog(B45),
        Some(false),
        "every literal coefficient is at most 2^12, but ay's certificate multiplies \
         4093 by 4091: the row must be declined, not expanded (None = still running)"
    );
}

#[test]
fn the_b48_origin_main_bounds_check_twin_returns_promptly_and_uncertified() {
    assert_eq!(
        certify_within_watchdog(B48),
        Some(false),
        "the pre-existing entry point: a bounds check under the same coprime guards"
    );
}

#[test]
fn positive_control_a_small_coefficient_still_certifies_through_ay() {
    // The same row with a coefficient the gate admits: `8 · _7 ≥ 2^63` under
    // `_7 < 2^32` is still UNSAT, and still reaches the ay lane (the in-tree
    // lanes decline the alias chain), so the gate is the only difference.
    assert_eq!(
        certify_within_watchdog(&with_coefficient(8)),
        Some(true),
        "a coefficient under the cap must still certify — the gate is narrow"
    );
}

/// Minimal reader for the `Debug` spelling of `Formula` used in the capture
/// (the same grammar `unbounded_allocation_scaled_count_certification.rs` reads).
struct Reader<'a> {
    s: &'a [u8],
    i: usize,
}

impl Reader<'_> {
    fn skip_ws(&mut self) {
        while self.i < self.s.len() && self.s[self.i] == b' ' {
            self.i += 1;
        }
    }
    fn eat(&mut self, c: u8) {
        self.skip_ws();
        assert_eq!(self.s[self.i], c, "expected `{}` at byte {}", c as char, self.i);
        self.i += 1;
    }
    fn peek(&mut self) -> u8 {
        self.skip_ws();
        self.s[self.i]
    }
    fn ident(&mut self) -> String {
        self.skip_ws();
        let start = self.i;
        while self.s[self.i].is_ascii_alphanumeric() || self.s[self.i] == b'_' {
            self.i += 1;
        }
        String::from_utf8(self.s[start..self.i].to_vec()).unwrap()
    }
    fn int(&mut self) -> i128 {
        self.skip_ws();
        let start = self.i;
        if self.s[self.i] == b'-' {
            self.i += 1;
        }
        while self.s[self.i].is_ascii_digit() {
            self.i += 1;
        }
        std::str::from_utf8(&self.s[start..self.i]).unwrap().parse().unwrap()
    }
    fn string(&mut self) -> String {
        self.eat(b'"');
        let start = self.i;
        while self.s[self.i] != b'"' {
            self.i += 1;
        }
        let out = String::from_utf8(self.s[start..self.i].to_vec()).unwrap();
        self.i += 1;
        out
    }
    fn list(&mut self) -> Vec<Formula> {
        self.eat(b'[');
        let mut out = Vec::new();
        while self.peek() != b']' {
            out.push(self.formula());
            if self.peek() == b',' {
                self.eat(b',');
            }
        }
        self.eat(b']');
        out
    }
    fn formula(&mut self) -> Formula {
        let name = self.ident();
        self.eat(b'(');
        let out = match name.as_str() {
            "And" => Formula::And(self.list()),
            "Or" => Formula::Or(self.list()),
            "Not" => Formula::Not(Box::new(self.formula())),
            "Int" => Formula::Int(self.int()),
            "Var" => {
                let var = self.string();
                self.eat(b',');
                let sort = match self.ident().as_str() {
                    "Int" => Sort::Int,
                    "Bool" => Sort::Bool,
                    other => panic!("unexpected sort {other}"),
                };
                Formula::Var(var, sort)
            }
            op => {
                let a = Box::new(self.formula());
                self.eat(b',');
                let b = Box::new(self.formula());
                match op {
                    "Ge" => Formula::Ge(a, b),
                    "Le" => Formula::Le(a, b),
                    "Gt" => Formula::Gt(a, b),
                    "Lt" => Formula::Lt(a, b),
                    "Eq" => Formula::Eq(a, b),
                    "Sub" => Formula::Sub(a, b),
                    "Add" => Formula::Add(a, b),
                    "Mul" => Formula::Mul(a, b),
                    other => panic!("unexpected operator {other}"),
                }
            }
        };
        self.eat(b')');
        out
    }
}

fn parse(text: &str) -> Formula {
    let mut reader = Reader { s: text.as_bytes(), i: 0 };
    let formula = reader.formula();
    assert_eq!(reader.i, text.len(), "trailing input after the formula");
    formula
}
