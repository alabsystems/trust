#!/usr/bin/env bash
# THE DAILY-DRIVER PROBES — the findings of 2026-09-18, made self-checking.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
#
# WHY THIS EXISTS. The daily-driver bench measures 71 one-liners and reads 64/71.
# That number was standing in for "the toolchain replaces Rust", which it cannot
# support: the same compiler verifies 3 of 6 ordinary multi-function programs.
# The probes here are the cases that gap is made of, plus the Lean half, which
# the bench does not touch at all.
#
# EVERY ROW ENCODES ITS EXPECTED OUTCOME, including the ones expected to FAIL.
# A must-fail probe that starts passing is as much a regression as a passing one
# that breaks: `derive_hash_alone` failing is a measured policy consequence, and
# `false_theorem_must_be_rejected` passing would mean the Clean kernel had stopped
# refusing a false proof. This script is red in both directions on purpose.
#
# Usage:  scripts/daily_driver_probes.sh [path-to-trustc]
set -uo pipefail
TC="${1:-$(cd "$(dirname "$0")/.." && pwd)/build/host/stage1/bin/trustc}"
[ -x "$TC" ] || { echo "no trustc at $TC (build it, or pass a path)"; exit 2; }
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
WORK="$(mktemp -d)"; trap 'rm -rf "$WORK"' EXIT
echo "compiler: $("$TC" --version 2>&1 | head -1)"

ok=0; bad=0
# expect: "pass", "fail" or "conditional"; edition and flags differ between the
# two halves. `conditional` is open_dispatch_ladder.sh's disposition, and is
# stronger than `pass`: exit 0, the OD-1 instance-hypothesis disclosure in the
# log, AND a second build under `-Ztrust-policy=certify` that refuses. A row
# whose hypothesis disappears, or that certify accepts, diverges.
COND_NEEDLE='recorded as `assumption:instance-hypothesis` (skipped, NOT proved)'
CERT_NEEDLE='Trust certify verification failed'
run() { # run <expect> <edition> <flags> <file>
  local expect=$1 ed=$2 flags=$3 file=$4 name
  name="$(basename "$file" .rs)"
  # shellcheck disable=SC2086
  "$TC" $flags --crate-type=lib --edition "$ed" --out-dir "$WORK" "$ROOT/$file" >"$WORK/$name.log" 2>&1
  local rc=$?
  local got=pass; [ $rc -eq 0 ] || got=fail
  if [ "$expect" = conditional ] && [ "$got" = pass ]; then
    if ! grep -qF -- "$COND_NEEDLE" "$WORK/$name.log"; then
      got="pass without the instance-hypothesis disclosure"
    else
      # shellcheck disable=SC2086
      "$TC" $flags -Ztrust-policy=certify --crate-type=lib --edition "$ed" --out-dir "$WORK" \
        "$ROOT/$file" >"$WORK/$name.certify.log" 2>&1
      local crc=$?
      if [ $crc -ne 0 ] && grep -qF -- "$CERT_NEEDLE" "$WORK/$name.certify.log"; then
        got=conditional
      elif [ $crc -eq 0 ]; then
        got="pass that certify accepts"
      else
        got="pass whose certify build exited $crc without \"$CERT_NEEDLE\": $(sed -n '/^error/{p;q;}' "$WORK/$name.certify.log" | cut -c1-120)"
      fi
    fi
  fi
  if [ "$got" = "$expect" ]; then ok=$((ok+1)); printf '  ok    %-44s %s\n' "$name" "$got"
  else bad=$((bad+1)); printf '  WRONG %-44s expected %s, got %s\n' "$name" "$expect" "$got"; fi
}

D=tests/daily-driver-realistic
echo "-- Rust: six ordinary multi-function programs (3 of 6 verify) --"
run pass 2024 "" $D/p1.rs
run pass 2024 "" $D/p2.rs
run pass 2024 "" $D/p3.rs
run fail 2024 "" $D/p4.rs
run fail 2024 "" $D/p5.rs
run pass 2024 "" $D/p6.rs

echo "-- Rust: derives. Hash blocks a crate; Debug is a conditional pass since D1 increment 2 --"
# 2026-09-25 (D1 increment 2): a derived `Debug` is admitted as a writer-relative
# CONDITIONAL pass (advisory "panic-free relative to its `Formatter`'s writer";
# `certify` still refuses). `derive_debug_alone` and `p6` flipped fail -> pass
# deliberately with that landing.
run pass 2024 "" $D/derive_debug_alone.rs
run fail 2024 "" $D/derive_hash_alone.rs
run pass 2024 "" $D/derive_others_alone.rs

echo "-- Rust: open dispatch. Declaring is fine; INVOKING is fail-closed --"
# One designed rule, not a defect: a call whose body the verifier cannot pin is
# fail-closed. It accounts for p4 AND p6 as well — but NOT for the same reason,
# and the earlier claim here that both "reach the same dyn Write dispatch" was
# measured wrong on 2026-09-19. p6 is a `derive(Debug)` and did charge
# `<dyn core::fmt::Write as core::fmt::Write>::write_str` (a writer edge, excused
# relative to the Formatter's writer since D1 increment 2, so p6 now passes); p4 charges
# `<dyn p4::Shape as p4::Shape>::area`, a USER trait object with no `core::fmt`
# in it at all. One rule, four callee kinds (dyn trait, generic param, closure,
# sysroot-at-a-user-type) — see reports/2026-09-19-open-dispatch-is-one-gate-
# and-the-lattice-already-exists.md. The passing row is the control: a trait
# bound that is never INVOKED through is fine.
# `opendispatch_generic_static` was `fail` until OD-1 phase 1 (c77d7678cf,
# 2026-10-04) admitted an open generic call as a disclosed instance hypothesis.
# Measured on pack 16387 (29ebb403d) 2026-11-13: exit 0 with the disclosure,
# and `-Ztrust-policy=certify` exits 1 with "Trust certify verification failed".
run fail 2024 "" $D/opendispatch_trait_dyn_single.rs
run conditional 2024 "" $D/opendispatch_generic_static.rs
run fail 2024 "" $D/opendispatch_closure_call.rs
run pass 2024 "" $D/opendispatch_bound_unused_is_fine.rs

echo "-- Rust: a sysroot callee reached through a bundled member (CLOSED 2026-09-19) --"
# WAS a false refutation. The tolerance ledger was built from the ROOT body's
# call sites while the bridge charges rows for callees absent anywhere in the
# BUNDLE, so a callee reached through a bundled member had no entry and failed
# closed. Closed on the fourth attempt, by widening the ledger, the family panic
# recognisers and the intrinsic rule TOGETHER — they are consistent only
# together. reports/2026-09-19-the-fourth-attempt-widened-all-three.md.
run pass 2024 "" $D/checked_add_helper_no_longer_poisons_caller.rs
# The guard rails for that widening: a sysroot routine handed a USER type still
# dispatches into user code and must stay refused, reached through a helper or not.
run fail 2024 "" $D/sysroot_at_user_type_behind_a_helper_must_refuse.rs
run fail 2024 "" $D/sysroot_generic_over_user_ord_behind_a_helper_must_refuse.rs
run pass 2024 "" $D/saturating_add_helper_is_fine.rs
# overflowing_add uses the SAME intrinsic and passes, differing only in returning
# a tuple instead of branching on the flag to build an Option. That contrast is what
# locates the unsupported model: the branch, not the intrinsic.
run pass 2024 "" $D/overflowing_add_helper_is_fine.rs

echo "-- Rust: the loop bound was iterator-only (closed 2026-09-18) --"
# These two were `fail` until 2026-09-18. `generate/loop_bounds.rs` already had the
# accumulator bound, but the trip count was read ONLY off an `Iterator::next`
# driver, so a hand-written `while` got no `K` and the mechanism was silent. The
# counter test now drives the loop (`counter_loop_driver`, one per loop since
# 2026-09-29); measured `TRUST_ACC[f] acc=1 K=3 per_max=1 init=0 -> bound _1 <= 3`,
# and both verify.
run pass 2024 "" $D/loop_accumulator_minimal_witness.rs
run pass 2024 "" $D/loop_accumulator_constant_bound.rs
run pass 2024 "" $D/loop_induction_variable_passes.rs
run pass 2024 "" $D/loop_accumulator_workaround_condition.rs
run pass 2024 "" $D/loop_accumulator_workaround_assert.rs
# These two must STAY refuted: they are the guard rails against a trip-count or
# relational refinement over-firing. The first has an UNBOUNDED addend (a trip
# count bounds how many additions happen, not how large each one is); the second
# keeps the addend a constant 2 but reaches `2n`, so the bound must carry the
# STRIDE and must be intersected with the accumulator's own type range.
run fail 2024 "" $D/loop_accumulator_correct_refusal_unbounded_addend.rs
run fail 2024 "" $D/loop_accumulator_correct_refusal_bounded_addend_really_overflows.rs
# NOT a guard rail. `while i < n { c += 1; i += 1 }` is SAFE for every `n` (the
# head invariant `c == i <= n` caps the last increment at `n <= u32::MAX`), so
# its refusal is a FALSE REFUTATION. The expectation is `fail` because that is
# what the toolchain does today; a change that flips it to pass is a FIX, and
# this row moving is the signal to say so, not to restore the old expectation.
run fail 2024 "" $D/loop_accumulator_unbounded_n_is_safe_but_refused.rs
# BOTTOM-tested loops with a `min`-bounded limit (bench `ctrl/c5`, the bench's
# LAST false refutation; closed 2026-09-19). Three things differ from a `while`
# loop at once: the TRUE edge exits, the compared operand is a COPY of the
# counter, and the limit is an `Ord::min` destination. The two refusals isolate
# the `min`: `max` is a LOWER bound, and an unconstrained limit has no trip count.
run pass 2024 "" $D/loop_bottom_tested_min_bound_passes.rs
# A separate accumulator under a `min`-bounded RANGE. The literal twin
# (`0..10`) always proved; this one had no trip count until 2026-09-19, because
# `range_trip_count_upper_bound` demanded a literal end. Over-approximating K
# only weakens the emitted bound, so admitting `min`'s constant is sound.
run pass 2024 "" $D/loop_accumulator_min_bounded_range_now_proves.rs
# A counter over a SLICE. The trip count is `isize::MAX` when the element is
# provably non-ZST — the same bound and the same gate `conjoin_slice_len_bounds`
# already uses. The ZST twin below must stay RED: `[(); usize::MAX]` is a valid
# slice, so that counter really does overflow.
run pass 2024 "" $D/loop_counter_over_a_slice_now_proves.rs
run fail 2024 "" $D/loop_counter_over_a_zst_slice_must_refuse.rs
# The `.iter()` spelling, which needs one more hop (`into_iter(v.iter())`), and
# must inherit the same ZST exception.
run pass 2024 "" $D/loop_counter_over_slice_iter_now_proves.rs
run fail 2024 "" $D/loop_counter_over_a_zst_slice_iter_must_refuse.rs
run fail 2024 "" $D/loop_bottom_tested_max_bound_must_refuse.rs
run fail 2024 "" $D/loop_bottom_tested_unbounded_must_refuse.rs

L=$D/lean
echo "-- Lean: the island fragment --"
run pass 2021 "-Z trust-verify=off" $L/island_theorem_under_default_policy.rs
run pass 2021 "-Z trust-verify=off" $L/induction_on_nat.rs
run pass 2021 "-Z trust-verify=off" $L/structure_and_projection.rs
run pass 2021 "-Z trust-verify=off" $L/dependent_indexed_inductive.rs
run pass 2021 "-Z trust-verify=off" $L/fin_dependent_index.rs
run fail 2021 "-Z trust-verify=off" $L/false_theorem_must_be_rejected.rs

echo "-- Lean: typeclasses, and the resolution defect --"
run pass 2021 "-Z trust-verify=off" $L/typeclass_polymorphic_use_works.rs
# Two controls that localise the leak, and the SECOND corrects the first.
# `typeclass_value_param_is_fine` was read as "a VALUE class parameter is fine;
# only a TYPE-kinded one plus an actual method use leaks" — measured wrong on
# 2026-09-19. `..._instance_body_without_arithmetic_is_fine` has a TYPE-kinded
# class parameter AND a method use and passes; it differs from the failing
# fixture by ONE token in the INSTANCE BODY. The discriminator is whether that
# body mentions a polymorphic constant (`x + y` -> `HAdd.{u,v,w}`, the three
# levels that leak), not anything about the class parameter or the use site.
run pass 2021 "-Z trust-verify=off" $L/typeclass_value_param_is_fine.rs
run pass 2021 "-Z trust-verify=off" $L/typeclass_instance_body_without_arithmetic_is_fine.rs
# CLOSED 2026-09-19 (clean 434ba130d): an instance's declared universe
# parameters now go through the same levelMVarToParam boundary a `def` does, so
# `instMagNat` registers with NO universe parameters and nothing is freshened
# onto its users. Both rows flipped fail -> pass on the rebuilt trustc.
run pass 2021 "-Z trust-verify=off" $L/typeclass_resolution_at_concrete_type.rs
run pass 2021 "-Z trust-verify=off" $L/typeclass_monomorphic_use_also_leaks.rs

echo "-- Lean: imports are a disclosed stand-in, and proofs on it are refused --"
run pass 2021 "-Z trust-verify=off" $L/import_is_a_standin_disclosed.rs
run fail 2021 "-Z trust-verify=off" $L/mathlib_proof_must_be_refused.rs

echo
echo "daily-driver probes: $ok as documented, $bad diverged"
[ $bad -eq 0 ] || {
  echo
  echo "A divergence is not automatically a regression — it may be a FIX."
  echo "Re-read the row's report under reports/2026-09-18-* before editing this file,"
  echo "and move the expectation only with the measurement that justifies it."
  exit 1
}
