#!/usr/bin/env bash
# THE DAILY-DRIVER BENCH — how much ORDINARY Rust the strict default lane verifies.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
#
# WHY THIS EXISTS. The goal is a toolchain that replaces Rust as a
# daily driver, and until this script the evidence for it was a ten-program
# battery plus whatever one-liners an agent happened to type that session. Ten
# programs cannot tell "the verifier is weak at iterators" from "one of those ten
# used `join`", and a number re-derived by hand each session is not a series.
#
# Sixty programs, nine categories, one line each, all of them things a person
# writes without thinking about verification. Each is compiled with the DEFAULT
# policy — no `--unverified`, no advisory — so a pass means the strict lane
# actually discharged it.
#
# HOW TO READ A FAILURE. Every failure is a REFUSAL with a named cause, never a
# wrong answer, and the script prints the cause next to the name. Chase the cause,
# not the count: seven failures over five causes means five pieces of work, and
# three of the seven share one.
#
# Usage:  scripts/daily_driver_bench.sh [path-to-trustc]
set -uo pipefail
TC="${1:-$(cd "$(dirname "$0")/.." && pwd)/build/host/stage1/bin/trustc}"
[ -x "$TC" ] || { echo "no trustc at $TC (build it, or pass a path)"; exit 2; }
WORK="$(mktemp -d)"; trap 'rm -rf "$WORK"' EXIT
echo "compiler: $("$TC" --version 2>&1 | head -1)"
pass=0; tot=0; declare -a FAILED=(); SEEN_NAMES=
# Cause patterns, in TWO TIERS, because ranking by pattern order does not work:
# `grep -oE` returns matches in TEXT order, and trustc routinely puts a specific
# cause and a generic one on the SAME note line. Measured three times now — the
# `fmt` pair, `float/v4`, and `str/s8` — each attributed to a downstream message
# sitting a few words to the left of the real one.
#
# TIER 1 names the construct or obligation itself. TIER 2 is the generic
# routing and engine messages, which only say WHERE the pipeline stopped; they
# are consulted only when tier 1 matches nothing at all.
CAUSES_1="unproven panic-freedom obligation for a call to an absent callee"
CAUSES_1="$CAUSES_1|unproved assumption-panic row"
CAUSES_1="$CAUSES_1|is not verified panic-free"
CAUSES_1="$CAUSES_1|unsupported MIR .[A-Za-z0-9_:.-]+"
CAUSES_1="$CAUSES_1|\\[overflow:[a-z]+\\] FAILED|\\[remzero\\] FAILED|\\[divzero\\] FAILED|\\[bounds\\] FAILED"
CAUSES_1="$CAUSES_1|\\[float_[a-z_]+\\] [A-Z]+"
CAUSES_1="$CAUSES_1|member Assert kind|guarded or non-entry-prefix"

CAUSES_2="no full-verification primary owner|UnsupportedDirectCallSummary"
CAUSES_2="$CAUSES_2|uses a public dialect operation without a private producer-semantics"
CAUSES_2="$CAUSES_2|uses Alloca without an internally bound extent|uses GEP without authenticated"

b() { # b <category> <name> <source>
  # A case NAME is not cosmetic: CORRECT_REFUSAL and FALSE_REFUTATION are matched
  # by `category/name`, and the per-case source file is `$WORK/$name.rs`. So two
  # cases sharing a name silently overwrite each other's source and let a
  # classification land on the wrong program. Measured 2026-09-18: `ctrl/c6`
  # named two different programs for a day after a new case was appended without
  # checking. Refuse rather than report a number built on an ambiguous label.
  case " $SEEN_NAMES " in
    *" $1/$2 "*)
      echo "bench defect: duplicate case name \`$1/$2\` — names must be unique" >&2
      exit 3
      ;;
  esac
  SEEN_NAMES="$SEEN_NAMES $1/$2"
  tot=$((tot+1)); printf '%s\n' "$3" > "$WORK/$2.rs"
  out=$("$TC" --edition 2021 --crate-type lib --out-dir "$WORK/out" "$WORK/$2.rs" 2>&1)
  if [ $? -eq 0 ]; then pass=$((pass+1)); printf '  PASS  %-8s %s\n' "$1" "$2"; return; fi
  # CAUSE ATTRIBUTION. trustc prints its own root-cause notes BEFORE a block
  # headed "--- native verifier detail (... engine internals, not required to
  # act on this error)". Everything after that header is a DOWNSTREAM symptom
  # of whatever the root-cause notes already said, so read the root region
  # first and only fall back to the whole log.
  #
  # Measured 2026-09-18, and it had been wrong since this script was written:
  # `fmt/m3` and `fmt/m4` were attributed to "uses Alloca without an internally
  # bound extent" for weeks. That string is an engine internal, 13 lines below
  # the header. The real cause, printed above it, is an unproven panic-freedom
  # row for an absent callee — and it is NOT the format_args array at all: the
  # same `Display` impl written as `f.write_str("x")`, which allocates nothing,
  # fails identically. The alloca lane would have been days of work on the
  # wrong defect.
  #
  # Ordering inside each region is FIRST OCCURRENCE, not `sort -u`, which
  # picked alphabetically and so had no relationship to which cause was root.
  root=$(printf '%s' "$out" | sed -n '1,/native verifier detail/p')
  cause=""
  for pat in "$CAUSES_1" "$CAUSES_2"; do
    cause=$(printf '%s' "$root" | grep -oE "$pat" | head -1)
    [ -n "$cause" ] || cause=$(printf '%s' "$out" | grep -oE "$pat" | head -1)
    [ -n "$cause" ] && break
  done
  FAILED+=("$1/$2: ${cause:-unattributed}")
  printf '  fail  %-8s %-4s :: %s\n' "$1" "$2" "${cause:-unattributed}"
}
b arith a1 'pub fn f(a: u32, b: u32) -> u32 { a.wrapping_add(b) }'
b arith a2 'pub fn f(a: u32, b: u32) -> u32 { a.saturating_sub(b) }'
b arith a3 'pub fn f(a: u32) -> u32 { a / 4 }'
b arith a4 'pub fn f(a: u32, b: u32) -> Option<u32> { a.checked_mul(b) }'
b arith a5 'pub fn f(a: i32) -> i32 { if a == i32::MIN { 0 } else { -a } }'
b arith a6 'pub fn f(a: u32) -> u32 { a % 7 }'
b arith a7 'pub fn f(a: u8) -> u8 { a >> 2 }'
b arith a8 'pub fn f(a: u32, b: u32) -> u32 { if b == 0 { 0 } else { a / b } }'
b ctrl c1 'pub fn f(b: bool, x: u32) -> u32 { if b { x } else { 0 } }'
b ctrl c2 'pub fn f(x: u32) -> u32 { match x { 0 => 1, 1 => 1, _ => 2 } }'
b ctrl c3 'pub fn f(n: u32) -> u32 { let mut i = 0u32; while i < n.min(10) { i += 1; } i }'
b ctrl c4 'pub fn f(n: u32) -> u32 { let mut a = 0u32; for i in 0..n.min(10) { a = a.wrapping_add(i); } a }'
# c5/c9: the bottom-tested loop. c9, with a CONSTANT break bound, was a false
# refutation until 2026-09-18 and now verifies. c5 routes its bound through
# `x.min(5)` and stays red. It is counted as a FALSE REFUTATION rather than a
# gap: the compiler prints `[overflow:add] FAILED` on a loop that ends at r <= 6,
# and a refutation of correct code is what the user is shown whatever the
# certification status of the witness behind it.
#
# THE MECHANISM, measured 2026-09-18. Do not re-derive it from the spelling —
# `min` is a red herring and two diagnoses died on it. The discriminator is
# CONSTANT versus VARIABLE break bound, and the control that shows it has no
# call in it at all:
#
#   let b = if x < 5 { x } else { 5 };
#   let mut r = 0; loop { r += 1; if r > b { break; } }   // FAILS, same shape
#
# c9's constant bound passes; that variable bound fails; neither involves a call.
#
# THE ENGINE THAT DECIDES BOTH IS PDR, not the interval lane. Measured: each row
# reports `selected PdrProof`, and trust-mc's IC3/PDR infers the loop invariant
# for the CONSTANT bound and `refuted obligation` for the variable one. The
# interval lane cannot contribute to either, by construction:
# `augment_vc_with_abstract_state` returns the VC unchanged whenever the formula
# mentions bitvector theory, because its facts are Int-sorted and would give one
# variable two sorts. A machine-width row gets no interval facts at all.
#
# So closing c5 is a trust-mc PDR question (infer an invariant relating the
# counter to a VARIABLE bound), or a much larger one: give the machine-width lane
# interval facts in the matching BV sort. The second touches every bitvector VC
# in the compiler and needs its own soundness argument.
#
# Two things measured and found INERT, so nobody repeats them:
#   * `TRUST_ORD_MIN_TAG_FIX`, the one behaviour-changing flag in trust-vcgen:
#     whole bench, both settings, identical failure sets; c5's own output
#     differs only in an `elapsed_ms` field.
#   * Refining an integer `Ord::min`/`max` call destination to its exact
#     interval instead of the Top the call havoc leaves. Sound, unit-tested in
#     both directions, and it changes no end-to-end verdict: still 64/71.
#     Reverted; see reports/2026-09-18-c5-is-not-a-min-problem.md.
#
# NAMING: c9, not c6. This case was added on 2026-09-18 as a second `c6`,
# colliding with the early-return division case below — and the labels are not
# cosmetic, because CORRECT_REFUSAL and FALSE_REFUTATION are matched by name.
# Two rows answering to `ctrl/c6` would have let a classification land on the
# wrong program.
b ctrl c9 'pub fn f() -> u32 { let mut r = 0; loop { r += 1; if r > 5 { break; } } r }'
b ctrl c5 'pub fn f(x: u32) -> u32 { let mut r = 0; loop { r += 1; if r > x.min(5) { break; } } r }'
b ctrl c6 'pub fn f(x: i32) -> i32 { if x < 0 { return 0; } x / 2 }'
b ctrl c7 'pub fn f(x: i32) -> i32 { if x < 0 { 0 } else { x / 2 } }'
b ctrl c8 'pub fn f(x: i32) -> i32 { if x < 0 { 0 } else if x > 100 { 0 } else { x / 2 } }'
b coll k1 'pub fn f(v: &[u32]) -> usize { v.len() }'
b coll k2 'pub fn f(v: &[u32]) -> u32 { if v.is_empty() { 0 } else { v[0] } }'
b coll k3 'pub fn f() -> Vec<u32> { let mut v = Vec::new(); v.push(1); v }'
b coll k4 'use std::collections::HashMap; pub fn f() -> usize { let mut m = HashMap::new(); m.insert(1u32, 2u32); m.len() }'
b coll k5 'pub fn f(v: &mut Vec<u32>) { v.sort(); }'
b coll k6 'pub fn f(v: &[u32]) -> Vec<u32> { v.to_vec() }'
b coll k7 'pub fn f(v: &[u32], i: usize) -> Option<&u32> { v.get(i) }'
b coll k8 'pub fn f(v: &[u32]) -> u32 { v.iter().copied().max().unwrap_or(0) }'
b str s1 'pub fn f(s: &str) -> usize { s.len() }'
b str s2 'pub fn f(s: &str) -> &str { s.trim() }'
b str s3 'pub fn f(s: &str) -> String { s.to_uppercase() }'
b str s4 'pub fn f(s: &str) -> Option<char> { s.chars().next() }'
b str s5 'pub fn f(s: &str) -> u32 { s.parse::<u32>().unwrap_or(0) }'
b str s6 'pub fn f(a: &str, b: &str) -> String { let mut t = String::from(a); t.push_str(b); t }'
b str s7 'pub fn f(v: &[String]) -> String { v.join(",") }'
b str s8 'pub fn f(s: &str) -> Vec<&str> { s.split(char::is_whitespace).collect() }'
b iter i1 'pub fn f(v: &[u32]) -> usize { v.iter().count() }'
b iter i2 'pub fn f(v: &[u32]) -> Vec<u32> { v.iter().map(|x| x + 1).collect() }'
b iter i3 'pub fn f(v: &[u32]) -> usize { v.iter().filter(|x| **x > 2).count() }'
b iter i4 'pub fn f(v: &[i32]) -> i32 { v.iter().fold(0, |a, b| a + b) }'
b iter i5 'pub fn f(v: &[u32]) -> bool { v.iter().any(|x| *x == 3) }'
b iter i6 'pub fn f(v: &[u32]) -> Option<&u32> { v.iter().max() }'
b iter i7 'pub fn f(a: &[u32], b: &[u32]) -> usize { a.iter().zip(b.iter()).count() }'
b iter i8 'pub fn f(v: &[u32]) -> usize { v.iter().enumerate().filter(|(i,_)| i % 2 == 0).count() }'
b err e1 'pub fn f(x: Option<u32>) -> u32 { x.unwrap_or(0) }'
b err e2 'pub fn f(r: Result<u32, ()>) -> u32 { r.unwrap_or(0) }'
b err e3 'pub fn f(x: Option<u32>) -> Result<u32, ()> { x.ok_or(()) }'
b err e4 'pub fn g(a: u32) -> Result<u32, ()> { if a > 5 { Err(()) } else { Ok(a) } } pub fn f(a: u32) -> Result<u32, ()> { let b = g(a)?; Ok(b) }'
b err e5 'pub fn f(a: u32) -> Result<u32, String> { if a > 5 { Err("big".to_string()) } else { Ok(a) } }'
b err e6 'pub enum E { A, B } pub fn f(e: &E) -> u32 { match e { E::A => 1, E::B => 2 } }'
b types t1 'pub struct P { pub x: i32, pub y: i32 } pub fn f(p: &P) -> i32 { p.x.wrapping_add(p.y) }'
b types t2 'pub trait S { fn a(&self) -> u32; } pub struct Q(pub u32); impl S for Q { fn a(&self) -> u32 { self.0 } } pub fn f(q: &Q) -> u32 { q.a() }'
b types t3 'pub fn f<T: Copy>(v: &[T]) -> Option<T> { v.first().copied() }'
b types t4 'pub enum E { A(u32), B } pub fn f(e: &E) -> u32 { match e { E::A(v) => *v, E::B => 0 } }'
b types t5 'pub fn f(v: &[u32]) -> u32 { match v { [] => 0, [a, ..] => *a } }'
b types t6 'pub fn f(t: (u32, u32)) -> u32 { t.0.wrapping_add(t.1) }'
b fmt m1 'pub fn f(x: u32) -> String { format!("{}", x) }'
b fmt m2 'pub fn f(x: u32) -> String { format!("{} {}", x, x) }'
b fmt m3 'use std::fmt; pub struct W(pub u32); impl fmt::Display for W { fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "{}", self.0) } }'
b fmt m4 '#[derive(Debug)] pub struct W(pub u32); pub fn f(w: &W) -> String { format!("{:?}", w) }'
b closure z1 'pub fn f(v: &[u32]) -> usize { v.iter().filter(|x| **x > 1).count() }'
b closure z2 'pub fn f(x: u32) -> u32 { let g = |a: u32| a.wrapping_add(1); g(x) }'
b closure z3 'pub fn f(v: &mut Vec<u32>) { v.retain(|x| *x > 1); }'
b float  v1 'pub fn f(x: f64) -> f64 { x + 1.0 }'
b float  v2 'pub fn f(x: f64) -> f64 { x * 2.0 }'
b float  v3 'pub fn f(a: f64, b: f64) -> f64 { a + b }'
b float  v4 'pub fn f(x: f64) -> f64 { x.abs() }'
b float  v5 'pub fn f(n: u32) -> f64 { (n as f64) * 2.0 }'
b float  v6 'pub fn f(x: f64) -> f64 { x.clamp(-1.0, 1.0) * 2.0 }'
# v7-v10: the CONTRACTED float row. v2/v3 above are unconstrained and really can
# overflow to infinity, so their refusal is correct and no verifier change can
# turn them green — writing a magnitude bound is the answer, and these four
# measure that it works. The f32 pair was a KNOWN GAP until 2026-09-17: the
# discharge compared every interval against f64-scaled thresholds, so an f32
# bound could not be admitted without discharging adds that overflow.
b float  v7 'pub fn f(x: f64) -> f64 requires x <= 1.0 && x >= -1.0 { x * 2.0 }'
b float  v8 'pub fn f(a: f64, b: f64) -> f64 requires a <= 1.0 && a >= -1.0 && b <= 1.0 && b >= -1.0 { a + b }'
b float  v9 'pub fn f(x: f32) -> f32 requires x <= 1.0 && x >= -1.0 { x * 2.0 }'
b float  v10 'pub fn f(a: f32, b: f32) -> f32 requires a <= 1.0 && a >= -1.0 && b <= 1.0 && b >= -1.0 { a + b }'
b closure z4 'pub fn f(v: &[u32]) -> Vec<u32> { let mut w = v.to_vec(); w.sort_by(|a,b| a.cmp(b)); w }'
echo
echo "daily-driver bench: $pass / $tot verified"
if [ ${#FAILED[@]} -gt 0 ]; then
  # A refusal is not automatically a defect. Traced 2026-09-18, each to its
  # mechanism, and four of the ten are the verifier being CORRECT:
  #
  #   fmt/m3, fmt/m4      a user `Display`/`Debug` impl calls
  #                       `Formatter::write_str`, whose body is
  #                       `self.buf.write_str(..)` on a `&mut dyn fmt::Write`
  #                       the CALLER chose. A user `impl fmt::Write` may panic,
  #                       so the impl's panic-freedom is not a property of its
  #                       own body. An allowance for exactly this once existed
  #                       and was retired as a measured false proof.
  #
  # Reporting those as "gaps" overstates the work left and invites someone to
  # widen a lane that must stay closed. They still BLOCK the user, which is why
  # they stay in the denominator.
  # WITHDRAWN 2026-09-18, by measurement: float/v2 and float/v3 were listed here
  # with the note "no verifier change may turn these green". A verifier change
  # turned them green the same day, so the note was not a fact about IEEE-754 —
  # it was a fact about a defect, stated as if it were about the language.
  #
  # Reaching infinity is real and the note was right about that. It was wrong
  # about the consequence. Overflow to +/-inf is DEFINED in Rust: no trap, no UB,
  # no panic. `VcKind::proof_level()` rules the row `L1Functional` on exactly that
  # ground, citing DESIGN_PHILOSOPHY section 9, and a second gate keyed on the
  # coarse verifier-API family counted it as Level-0 anyway. The refusal was a
  # disagreement between two gates, not the verifier being correct.
  #
  # The lesson for this list: "correct refusal" is a claim that the OBLIGATION is
  # warranted, not that the program is unusual. Before adding a row, check what
  # `proof_level()` says about its kind — if the answer is not L0, a refusal is a
  # defect however reasonable the prose sounds.
  CORRECT_REFUSAL=" fmt/m3 fmt/m4 "
  # DELIBERATELY EMPTY since 2026-09-19: the bench carries no known false
  # refutation. `ctrl/c5` was the last one and it CLOSED — bottom-tested loops
  # and `min`-bounded limits both landed in round 2 of the loop-bound work
  # (reports/2026-09-19-the-benchs-last-false-refutation.md). The long comment
  # above about c5 describes why it USED to fail and is kept as the argument,
  # not as status.
  #
  # CAVEAT, so the empty list is not read as a stronger claim than it is: a row
  # that REGRESSES lands in GAPS and is printed as a capability gap, which is
  # the forgiving label. An unexpected red here is a regression until someone
  # has re-derived which of the three it is.
  FALSE_REFUTATION=" "
  correct=0; wrong=0; gap=0
  declare -a GAPS=() RIGHT=() WRONG=()
  for row in "${FAILED[@]}"; do
    name=${row%%:*}
    if [[ "$CORRECT_REFUSAL" == *" $name "* ]]; then
      correct=$((correct+1)); RIGHT+=("$row")
    elif [[ "$FALSE_REFUTATION" == *" $name "* ]]; then
      wrong=$((wrong+1)); WRONG+=("$row")
    else
      gap=$((gap+1)); GAPS+=("$row")
    fi
  done
  echo "  not verified: $((correct+wrong+gap))  =  $gap capability gap(s) + $correct correct refusal(s) + $wrong false refutation(s)"
  [ $gap -gt 0 ] && { echo "capability gaps:"; printf '%s\n' "${GAPS[@]}" | sed 's/^/  /'; }
  [ $wrong -gt 0 ] && { echo "FALSE REFUTATIONS (the verifier rejecting correct code):"; printf '%s\n' "${WRONG[@]}" | sed 's/^/  /'; }
  [ $correct -gt 0 ] && { echo "correct refusals (do not 'fix' these):"; printf '%s\n' "${RIGHT[@]}" | sed 's/^/  /'; }
fi
[ "$pass" -eq "$tot" ]
