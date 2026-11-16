#!/usr/bin/env bash
# Direct-call-summary census — WHY the modular call summary declines, and HOW OFTEN.
#
# `try_direct_call_summary` (first-party/trust-mc, trust-mc-trust-bmc/src/translate_chc.rs)
# is the mechanism that lets a caller be proved panic-free THROUGH a call: it
# interprets the callee's body into the caller's CHC encoding. It declines
# through 83 separate labelled exits, and before this instrument existed there was NO
# counter of SUCCESSFUL summaries anywhere in tree — a decline reached the
# transport as one undifferentiated `UnsupportedDirectCallSummary` diagnostic.
#
# Three campaign runs re-derived these numbers by hand in scratchpad harnesses.
# All three died with their agent, and the last one's figures turned out to be
# unreproducible: an exhaustive search of both repos found no trace of the
# harness or the corpus. THAT is why this is committed.
#
#   scripts/call_summary_census.sh [OPTIONS]
#
#     --corpus DIR        read native-bundle dumps from DIR (repeatable).
#                         Default: tests/trust-call-summary-census/corpus — four
#                         real dumps kept so the instrument's positive control
#                         can run with NO trustc and no scratchpad.
#     --dump-corpus DIR   FIRST compile tests/ui/trust/*.rs with
#                         `-Ztrust-dump=native-bundle:DIR` to produce a real
#                         corpus, then census it. Needs a working `trustc`.
#     --out DIR           write rows.tsv / summary.json / report.txt here.
#                         Default: reports/call-summary-census-<utc-date>.
#     --scope requests|all   which functions to translate per bundle (see the
#                         binary's --scope; default `requests`).
#     --max-files N       census at most N bundles (0 = all).
#     --max-seconds S     wall-clock cap for the census itself (default 900).
#     --dump-cap S        per-file wall cap while dumping a corpus (default 120).
#     --dump-max-files N  compile at most N fixtures while dumping (0 = all).
#                         A full sweep is ~300 compilations; this is what makes
#                         the recipe runnable inside a gate budget.
#     --dump-floor-pct N  refuse a dump sweep in which fewer than N% of the
#                         compilations produced a bundle (default 30).
#                         CALIBRATION, full sweep 2026-08-29: 300 compiled,
#                         65.0% exited NONZERO but 86.7% produced a bundle, and
#                         156 fixtures did both. The guard keys on DUMPS because
#                         an exit-code guard refuses this recipe's healthy run.
#     --selftest          prove the census's own checks can FAIL, then exit.
#
# The census PROVES ITS OWN INSTRUMENT FIRED on every run: it prints a
# conservation check (census rows == an independent `Inst::Call` recount off the
# IR), a positive control (summaries observed > 0), a decline control, and a
# zero-false-positive check (no row attributed to `__unlabelled__`). It exits
# nonzero when any of those fails. A census that cannot show it fired is worth
# nothing, so this is normal output, not a thing a reader must remember to run.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

set -uo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
MC="$REPO/first-party/trust-mc"

CORPORA=()
DUMP_CORPUS=""
OUT=""
SCOPE="requests"
MAX_FILES=0
MAX_SECONDS=900
DUMP_CAP=120
DUMP_FLOOR_PCT=30
DUMP_MAX_FILES=0
SELFTEST=0

while [ $# -gt 0 ]; do
  case "$1" in
    --corpus)       CORPORA+=("$2"); shift 2 ;;
    --dump-corpus)  DUMP_CORPUS="$2"; shift 2 ;;
    --out)          OUT="$2"; shift 2 ;;
    --scope)        SCOPE="$2"; shift 2 ;;
    --max-files)    MAX_FILES="$2"; shift 2 ;;
    --max-seconds)  MAX_SECONDS="$2"; shift 2 ;;
    --dump-cap)     DUMP_CAP="$2"; shift 2 ;;
    --dump-floor-pct) DUMP_FLOOR_PCT="$2"; shift 2 ;;
    --dump-max-files) DUMP_MAX_FILES="$2"; shift 2 ;;
    --selftest)     SELFTEST=1; shift ;;
    -h|--help)      sed -n '2,52p' "${BASH_SOURCE[0]}"; exit 0 ;;
    *) echo "call_summary_census: unknown option $1" >&2; exit 2 ;;
  esac
done

[ -n "$OUT" ] || OUT="$REPO/reports/call-summary-census-$(date -u +%Y-%m-%d)"
mkdir -p "$OUT" || exit 2

# ---------------------------------------------------------------------------
# Find a REAL targo.
#
# A stage whose `targo` was never rebuilt ships upstream `cargo` under the name
# `targo`. It then works, so nothing complains. The two discriminators that
# have survived every packaging change are BEHAVIOURAL: the real one accepts
# `--unverified`, and its major.minor is 1.99 rather than cargo's 1.96. The
# inode test and the `(targo 0.1.0)` suffix have both been measured WRONG.
# ---------------------------------------------------------------------------
find_targo() {
  local candidate
  for candidate in \
      "${TARGO:-}" \
      "$REPO/build/host/stage1/bin/targo" \
      "$REPO/build/host/stage2/bin/targo" \
      "$(command -v targo 2>/dev/null)"; do
    [ -n "$candidate" ] && [ -x "$candidate" ] || continue
    "$candidate" --unverified --version >/dev/null 2>&1 || continue
    echo "$candidate"
    return 0
  done
  return 1
}

TARGO_BIN="$(find_targo)"
if [ -z "$TARGO_BIN" ]; then
  cat >&2 <<'EOF'
call_summary_census: no real `targo` found.

  Tried $TARGO, build/host/stage1/bin/targo, build/host/stage2/bin/targo, PATH.
  A stage that was never rebuilt ships upstream `cargo` under the name `targo`;
  it REJECTS `--unverified`, which is how this check tells them apart.

  Options:
    * point at one explicitly:   TARGO=/path/to/targo scripts/call_summary_census.sh ...
    * build one:                 ./x.py build      (hours, and takes the build lock)
    * install a published one:   atpkg update      (minutes)
EOF
  exit 2
fi
echo "targo:  $TARGO_BIN  ($("$TARGO_BIN" --unverified --version 2>&1 | head -1))"

# ---------------------------------------------------------------------------
# The build tree is EXCLUSIVE. `x.py build` deletes stage1/bin/rustc at start,
# so a build started under this census destroys the driver it is using. Hold
# the lock for the whole run — and, per the same rule, never around `x.py`,
# which takes it itself.
# ---------------------------------------------------------------------------
#
# `--pid $$` is LOAD-BEARING and was missing. The former shell owner defaulted
# the holder pid to its own short-lived administrative process, which exited as
# soon as it printed the token. Native acquisition requires an explicit durable
# owner. The old lock on disk therefore named a DEAD
# holder from the moment it was taken, and reclaim of a dead holder is automatic,
# so the very next acquirer walked straight through it. Measured 2026-08-29:
# `status` reported `free` while a census sweep was running, and a second
# invocation acquired the lock without waiting. A lock that self-releases is a
# silent instrument — worse than none, because it reads as protection.
# `scripts/run_measurement_sweep.sh` already passes `--pid $$`; this now matches.
INHERITED_LOCK_TOKEN="${TRUST_BUILD_LOCK_TOKEN:-}"
LOCK_TOKEN="$("$TARGO_BIN" trust repo lock acquire --repo-root "$REPO" \
    --kind measurement --purpose "call-summary census" --pid $$ --wait 120)" || exit 3
[ -n "$LOCK_TOKEN" ] || { echo 'native measurement lease returned no token' >&2; exit 3; }
release_measurement_lock() {
  if [ "$LOCK_TOKEN" != "$INHERITED_LOCK_TOKEN" ]; then
    "$TARGO_BIN" trust repo lock release "$LOCK_TOKEN" --repo-root "$REPO" >/dev/null 2>&1
  fi
}
trap release_measurement_lock EXIT

# ---------------------------------------------------------------------------
# Optional: produce a real corpus.
#
# macOS ships NEITHER `timeout` NOR `gtimeout`. A census that used one exited
# 127 on every invocation and reported ZERO obligations across 361 fixtures —
# which read as a clean result. The in-repo convention is a perl alarm, and the
# child is BACKGROUNDED and `wait`ed rather than run in the foreground, because
# a caught signal is not delivered while a foreground external command runs
# (measured: 20s trap latency foreground vs 0s through `child & wait $!`).
# ---------------------------------------------------------------------------
if [ -n "$DUMP_CORPUS" ]; then
  TRUSTC="${TRUSTC:-$(dirname "$TARGO_BIN")/trustc}"
  if [ ! -x "$TRUSTC" ]; then
    echo "call_summary_census: no trustc at $TRUSTC (set TRUSTC=... to override)" >&2
    exit 2
  fi
  mkdir -p "$DUMP_CORPUS" "$OUT/dump-logs" || exit 2
  echo "dump:   $TRUSTC -> $DUMP_CORPUS"
  echo "driver: $("$TRUSTC" --version 2>&1 | head -1)"

  n=0; ok=0; bad=0; produced=0; barren=0; skipped=0
  : > "$OUT/dump-index.tsv"
  printf 'fixture\trc\tdumps\texpect\n' >> "$OUT/dump-index.tsv"
  for src in "$REPO"/tests/ui/trust/*.rs; do
    if [ "$DUMP_MAX_FILES" -ne 0 ] && [ "$n" -ge "$DUMP_MAX_FILES" ]; then
      echo "  STOP: --dump-max-files $DUMP_MAX_FILES reached (PARTIAL corpus)"
      break
    fi
    base="$(basename "$src" .rs)"

    # Two fixture classes CANNOT compile under this recipe, and counting them as
    # instrument failures is what made the guard below trip on a healthy sweep:
    #   * `aux-build` needs a companion crate compiled first (compiletest does
    #     that; a bare trustc invocation gets E0463 and dumps NOTHING);
    #   * `ignore-test` is disabled upstream.
    # Skipped and REPORTED, never silently folded into the failure count.
    if grep -q '^//@ *aux-build:' "$src"; then
      skipped=$((skipped + 1))
      printf '%s\t-\t0\tskip:aux-build\n' "$base" >> "$OUT/dump-index.tsv"
      continue
    fi
    if grep -q '^//@ *ignore-test' "$src"; then
      skipped=$((skipped + 1))
      printf '%s\t-\t0\tskip:ignore-test\n' "$base" >> "$OUT/dump-index.tsv"
      continue
    fi

    n=$((n + 1))
    before="$(find "$DUMP_CORPUS" -name '*.json' | wc -l | tr -d ' ')"
    perl -e 'alarm shift; exec @ARGV' "$DUMP_CAP" \
      "$TRUSTC" -Ztrust-verify=on --crate-type lib --crate-name "c$n" \
        -Ztrust-dump=native-bundle:"$DUMP_CORPUS" \
        --emit=metadata -o "$OUT/dump-logs/$base.rmeta" "$src" \
        > "$OUT/dump-logs/$base.log" 2>&1 &
    wait $! ; rc=$?
    if [ "$rc" -eq 0 ]; then ok=$((ok + 1)); else bad=$((bad + 1)); fi
    rm -f "$OUT/dump-logs/$base.rmeta"
    after="$(find "$DUMP_CORPUS" -name '*.json' | wc -l | tr -d ' ')"
    made=$((after - before))
    if [ "$made" -gt 0 ]; then produced=$((produced + 1)); else barren=$((barren + 1)); fi
    # `expect` records whether a NONZERO exit is the fixture's declared intent,
    # so the log can be read without re-deriving it from the directives.
    if grep -qE '^//@(\[[a-z0-9_]+\])? *(check-fail|build-fail|run-crash|error-pattern)' "$src"
    then expect="expect-fail"; else expect="expect-pass"; fi
    printf '%s\t%s\t%s\t%s\n' "$base" "$rc" "$made" "$expect" >> "$OUT/dump-index.tsv"

    if [ $((n % 40)) -eq 0 ]; then
      mb="$(du -sm "$DUMP_CORPUS" 2>/dev/null | cut -f1)"
      free="$(df -m "$DUMP_CORPUS" | tail -1 | awk '{print $4}')"
      echo "  ...$n compiled ($ok exit-0 / $bad nonzero; $produced produced a dump), $after dumps, ${mb}MB, ${free}MB free"
      # A corpus sweep has filled this volume to zero bytes free, at which point
      # NOTHING works — not `rm`, not `pkill` on the process still filling it.
      if [ "${free:-999999}" -lt 4000 ]; then echo "  STOP: <4GB free"; break; fi
      if [ "${mb:-0}" -gt 6000 ]; then echo "  STOP: corpus exceeded 6GB"; break; fi
    fi
  done
  total_dumps="$(find "$DUMP_CORPUS" -name '*.json' | wc -l | tr -d ' ')"
  echo "dump:   $n compiled ($skipped skipped), $ok exit-0, $bad nonzero, \
$produced produced >=1 dump, $barren produced none, $total_dumps bundle dumps"

  # ------------------------------------------------------------------------
  # THE GUARD, and why it no longer keys on the exit code.
  #
  # It used to fail when a MAJORITY of dump invocations exited nonzero. That
  # predicate is wrong for THIS corpus, and wrong in the direction that makes
  # the committed regeneration recipe unrunnable: `tests/ui/trust` holds 100
  # `check-fail` + 3 `build-fail` + 4 `run-crash` fixtures whose nonzero exit is
  # the POINT of the test, plus every fixture whose own `//@ compile-flags` this
  # recipe deliberately overrides. Measured 2026-08-29 over the whole suite:
  # 300 compiled, 195 (65.0%) exited NONZERO, 260 (86.7%) produced a bundle, and
  # 156 did BOTH -- the two are near-independent, because a verification failure
  # is emitted AFTER the dump is written. The old guard refused its own recipe.
  #
  # What it was actually built to catch is a dump lane that produces NOTHING —
  # the `timeout`-binary failure where every invocation exited 127 and a
  # 361-fixture sweep read as a clean zero. That is a statement about DUMPS, and
  # it is now measured as one. Exit codes are still counted and printed, because
  # they are informative; they are just not the health signal.
  # ------------------------------------------------------------------------
  if [ "$total_dumps" -eq 0 ]; then
    echo "call_summary_census: FAIL — the dump lane produced ZERO bundles from $n compilations." >&2
    echo "  This is the failure the guard exists for: a driver that cannot dump reads as a" >&2
    echo "  clean small corpus. Read $OUT/dump-logs/*.log and $OUT/dump-index.tsv." >&2
    exit 1
  fi
  if [ "$n" -gt 0 ] && [ $((produced * 100)) -lt $((n * DUMP_FLOOR_PCT)) ]; then
    echo "call_summary_census: FAIL — only $produced of $n compilations produced any bundle" >&2
    echo "  (floor ${DUMP_FLOOR_PCT}%; the 2026-08-29 calibration sweep measured 86.7%)." >&2
    echo "  Read $OUT/dump-index.tsv: the 'dumps' column is the one that matters, not 'rc'." >&2
    echo "  Override with --dump-floor-pct N if the corpus itself changed shape." >&2
    exit 1
  fi
  CORPORA+=("$DUMP_CORPUS")
fi

# Default corpus: the four committed control dumps. Tiny, but always present
# and needs no trustc — so the instrument's self-checks can be run by anyone
# from a source checkout alone. They are chosen to contain a summary AND three
# distinct declines, because a control that cannot make the checks FIRE proves
# nothing. See tests/trust-call-summary-census/README.md.
if [ ${#CORPORA[@]} -eq 0 ]; then
  CORPORA+=("$REPO/tests/trust-call-summary-census/corpus")
  echo "corpus: (default) committed control corpus — pass --corpus DIR for a real sweep"
fi

# ---------------------------------------------------------------------------
# Build and run the census binary.
# ---------------------------------------------------------------------------
echo "build:  call-summary-census"

# ---------------------------------------------------------------------------
# A MEASUREMENT MUST LEAVE THE SUBMODULE CLEAN.
#
# `first-party/trust-mc` redirects `trust-ir`/`trust-ir-build` at the SIBLING
# submodule via `[patch]`, and that sibling moves independently of trust-mc's
# committed `Cargo.lock` — so the first build re-resolves and rewrites the lock
# (measured 2026-08-29: `clean-kernel` 0.5.0 -> 0.6.0). Nothing about running a
# census is a decision to move a dependency, and a stale/dirty `first-party/`
# worktree has silently REVERTED pins in this repo twice: a later `git add`
# sweeps the drift in as if it were intended.
#
# The lock is therefore snapshotted by BYTES and restored unconditionally, on
# every exit path including a signal — and the rewrite is DISCLOSED rather than
# hidden, because a lock that keeps wanting to move is a real fact about the
# pins. `--locked` is not the answer: it would refuse to build at all, turning a
# pin question into a broken instrument.
# ---------------------------------------------------------------------------
LOCK_SNAPSHOT=""
if [ -f "$MC/Cargo.lock" ]; then
  # Outside $OUT deliberately: a stray copy of a Cargo.lock sitting in reports/
  # is the kind of artifact that later gets read as evidence of a pin.
  LOCK_SNAPSHOT="$(mktemp -t trust-mc-cargo-lock)" || LOCK_SNAPSHOT=""
  [ -n "$LOCK_SNAPSHOT" ] && cp "$MC/Cargo.lock" "$LOCK_SNAPSHOT"
fi
restore_submodule_lock() {
  [ -n "$LOCK_SNAPSHOT" ] && [ -f "$LOCK_SNAPSHOT" ] || return 0
  if ! cmp -s "$LOCK_SNAPSHOT" "$MC/Cargo.lock"; then
    echo "lock:   restoring first-party/trust-mc/Cargo.lock — the build re-resolved it" >&2
    echo "        (the sibling trust-ir pin and trust-mc's committed lock disagree;" >&2
    echo "         that is a PIN question, not something a census may decide)" >&2
    cp "$LOCK_SNAPSHOT" "$MC/Cargo.lock"
  fi
}
cleanup_lock_snapshot() { [ -n "$LOCK_SNAPSHOT" ] && rm -f "$LOCK_SNAPSHOT"; return 0; }
if [ -n "$LOCK_TOKEN" ]; then
  trap 'restore_submodule_lock; cleanup_lock_snapshot; release_measurement_lock' EXIT
else
  trap 'restore_submodule_lock; cleanup_lock_snapshot' EXIT
fi

( cd "$MC" && "$TARGO_BIN" --unverified build --release \
    -p trust-mc-trust-bmc --features census-cli --bin call-summary-census ) \
  > "$OUT/build.log" 2>&1 &
wait $! ; build_rc=$?
restore_submodule_lock
if [ "$build_rc" -ne 0 ]; then
  echo "call_summary_census: FAIL — census binary did not build (rc=$build_rc)" >&2
  tail -30 "$OUT/build.log" >&2
  exit 1
fi
BIN="$MC/target/release/call-summary-census"
[ -x "$BIN" ] || { echo "call_summary_census: $BIN missing after a successful build" >&2; exit 1; }

# How many labelled exits the interpreter HAS. Read from the ONE pinned
# constant (the in-crate test's), so the report can say how many exits are a
# measured zero without a second copy of the number drifting away from it.
INVENTORY="$(sed -n 's/.*EXPECTED_LABELLED_EXITS: usize = \([0-9]*\).*/\1/p' \
    "$MC/trust-mc-trust-bmc/tests/call_summary_census.rs" | head -1)"
: "${INVENTORY:=0}"

# ---------------------------------------------------------------------------
# --selftest: mutation-grade proof that the census's OWN checks can fail.
#
# Every number in this instrument is read as a slice decision, so the checks
# that guard it must be seen to fire, not asserted to work. Two of them were
# not: `sole` was reported at TAG granularity for a tag spanning nine opcodes,
# and a dedup check written the obvious way PASSED against a tally that
# double-counted every site. Both are now controls that run on demand.
# ---------------------------------------------------------------------------
if [ "$SELFTEST" = "1" ]; then
  st_rc=0
  st_fail() { echo "  [FAIL] $*" >&2; st_rc=1; }
  st_pass() { echo "  [PASS] $*"; }
  echo
  echo "-- CENSUS SELFTEST --"

  # (1) The aggregator's own unit tests, including `sole_is_refined_by_opcode`
  #     — the controlled discriminator between the refined and rolled-up
  #     columns. `Cause::new` is the single place a decline becomes a cause
  #     key, so reinstating the tag-only key is a one-line mutation of
  #     PRODUCTION code and turns that test red.
  ( cd "$MC" && "$TARGO_BIN" --unverified test --release \
      -p trust-mc-trust-bmc --features census-cli --bin call-summary-census ) \
    > "$OUT/selftest-unit.log" 2>&1 &
  wait $! ; unit_rc=$?
  restore_submodule_lock
  if [ "$unit_rc" -eq 0 ]; then
    st_pass "aggregator unit tests ($(grep -c '^test tests::' "$OUT/selftest-unit.log") case(s))"
  else
    st_fail "aggregator unit tests — see $OUT/selftest-unit.log"
    tail -20 "$OUT/selftest-unit.log" >&2
  fi

  # (2) DEDUP CONTROL. The same corpus passed twice must not move a single
  #     count. Before the fix this doubled `sites` (4 -> 8) while `distinct
  #     modules` stayed at 4, and conservation PASSED because the independent
  #     `Inst::Call` recount doubled by the same factor.
  CTRL="$REPO/tests/trust-call-summary-census/corpus"
  once="$("$BIN" --scope all --label-inventory "$INVENTORY" "$CTRL" 2>&1)"
  twice="$("$BIN" --scope all --label-inventory "$INVENTORY" "$CTRL" "$CTRL" 2>&1)"
  sites_once="$(printf '%s\n' "$once"  | sed -n 's/.*total direct-call sites *\([0-9]*\).*/\1/p')"
  sites_twice="$(printf '%s\n' "$twice" | sed -n 's/.*total direct-call sites *\([0-9]*\).*/\1/p')"
  if [ -n "$sites_once" ] && [ "$sites_once" = "$sites_twice" ]; then
    st_pass "dedup control — one corpus dir vs the same dir twice: $sites_once sites both times"
  else
    st_fail "dedup control — sites moved from '$sites_once' to '$sites_twice' when a corpus dir was repeated"
  fi
  if printf '%s\n' "$twice" | grep -q '\[PASS\] dedup'; then
    st_pass "dedup self-check reports PASS on a deliberately repeated corpus"
  else
    st_fail "dedup self-check did not pass on a repeated corpus"
  fi

  # (3) THE DUMP GUARD MUST FIRE. Driving the dump lane with a `trustc` that
  #     cannot compile anything reproduces the exact failure the guard exists
  #     for: every invocation fails and the corpus is empty. `/usr/bin/false`
  #     stands in for the `timeout`-binary-exits-127 case that once had a
  #     361-fixture sweep read as "zero obligations".
  #
  #     The nested run inherits TRUST_BUILD_LOCK_TOKEN so its own acquire is
  #     re-entrant rather than deadlocking against this one.
  st_tmp="$(mktemp -d -t call-summary-selftest)"
  TRUSTC=/usr/bin/false TRUST_BUILD_LOCK_TOKEN="$LOCK_TOKEN" \
    bash "$REPO/scripts/call_summary_census.sh" \
      --dump-corpus "$st_tmp/corpus" --out "$st_tmp/out" --dump-max-files 5 \
      > "$OUT/selftest-guard.log" 2>&1 &
  wait $! ; guard_rc=$?
  restore_submodule_lock
  if [ "$guard_rc" -ne 0 ] && grep -q 'produced ZERO bundles' "$OUT/selftest-guard.log"; then
    st_pass "dump guard fires on a dump lane that produces nothing (exit $guard_rc)"
  else
    st_fail "dump guard did NOT fire on an empty dump lane (exit $guard_rc) — a census that"
    st_fail "  cannot refuse an empty corpus reads a broken driver as a clean small result"
  fi
  rm -rf "$st_tmp"

  echo
  if [ "$st_rc" -eq 0 ]; then
    echo "call_summary_census --selftest: ok (controls pass; every checked arm was seen to fire)"
  else
    echo "call_summary_census --selftest: FAILED" >&2
  fi
  exit "$st_rc"
fi

perl -e 'alarm shift; exec @ARGV' $((MAX_SECONDS + 120)) \
  "$BIN" --scope "$SCOPE" --max-files "$MAX_FILES" --max-seconds "$MAX_SECONDS" \
         --label-inventory "$INVENTORY" \
         --rows "$OUT/rows.tsv" --json "$OUT/summary.json" "${CORPORA[@]}" \
  2>&1 | tee "$OUT/report.txt" &
wait $! ; census_rc=${PIPESTATUS[0]:-$?}

echo
echo "artifacts: $OUT"
if [ "$census_rc" -ne 0 ]; then
  echo "call_summary_census: FAIL — the instrument self-check did not pass (rc=$census_rc)." >&2
  echo "  Read the INSTRUMENT SELF-CHECK block in $OUT/report.txt: a census that cannot" >&2
  echo "  demonstrate it fired reports nothing, and a zero here is not a clean result." >&2
fi
exit "$census_rc"
