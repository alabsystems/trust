#!/bin/zsh
# Run a trust-ir producer scorecard sweep UNDER A MEASUREMENT SENTINEL.
#
#   usage: scripts/run_measurement_sweep.sh <out-dir-name> "<purpose>" [sample-size]
#   e.g.   scripts/run_measurement_sweep.sh postbuild-soundness "dyn false-PROVE fix + slice 20"
#
# WHY THIS EXISTS
#
# A wait is not a lock. `pgrep -x bootstrap` only sees a build that has ALREADY started, and
# nothing in the tree expressed the converse: that a 37-minute measurement is in flight and the
# binary underneath it must not move. `x.py build` deletes `stage1/bin/rustc` at start, so a
# build launched during a sweep kills it.
#
# Measured this session: slice 20 shipped with its corpus sweep never run because it was killed
# three times this way; a further sweep died at 4m27s and another at 37s. That is the entire
# reason `postbuild-slice20-control` is not a valid post-slice-20 control.
#
# So this publishes `.trust-measurement-in-flight` at the repo root. The contract is one line:
# READ IT BEFORE YOU BUILD. It carries pid, start time, purpose and expected duration, so a lane
# that finds it can decide to wait rather than guess.
#
# THE TRAP IS THE LOAD-BEARING HALF. A sentinel that outlives its sweep blocks every other lane
# indefinitely — a worse failure than the one it prevents. It is removed on success, failure,
# INT and TERM alike, and `--force` exists for the case where a crash left one behind.
#
# ---------------------------------------------------------------------------------------
# 2026-08-20 — THE SENTINEL IS NOW BACKED BY A REAL LOCK, and the sentinel itself is kept.
#
# Everything above stayed true and stayed insufficient: the sentinel is ADVISORY. It made
# conflicts visible to whoever looked, and nothing made anyone look. Four more measurement
# runs were destroyed in one session. So this script now also takes
# a native Targo build-tree lease — the same ownership Bootstrap takes before it builds.
# The native manager owns acquisition, holder identity, recovery and release.
#
# `.trust-measurement-in-flight` is STILL published, with the same fields, because other
# lanes are reading it right now and a flag day mid-session would be worse than the problem.
# It is now the compatibility surface; the lock is the enforcement.
#
# Two refusals MOVED into the lock rather than disappearing: "bootstrap is running" (now
# `pgrep -x bootstrap`, scoped to this repo root, so a sibling clone's build does not fire
# it) and "a measurement is already in flight" for the case where the other sweep is LIVE.
# The stale-sentinel refusal below is unchanged, `--force` still means what it meant.
set -u

# Default to THIS script's own repo rather than a hardcoded home path: the
# publication boundary bans absolute /Users/... paths in exported content, and
# the sweep is exported. TRUST_REPO still overrides for out-of-tree runs.
# `BASH_SOURCE` is a BASH-ism and this script's shebang is `#!/bin/zsh`, where it is
# unset — so the expansion collapsed to "", `dirname ""` gave ".", and the lock path
# became `//scripts/trust_build_lock.sh`. The sweep then refused to start at all:
#   REFUSING: //scripts/trust_build_lock.sh is missing; this sweep would run unprotected
# Failing CLOSED there is correct and is what caught this. `$0` is the script path under
# zsh; the `:-` keeps it working if the file is ever run through bash instead.
REPO=${TRUST_REPO:-$(cd "$(dirname "${BASH_SOURCE[0]:-$0}")/.." && pwd)}
SENTINEL=$REPO/.trust-measurement-in-flight
# Trust: `build/host` symlinks to `build/<host-triple>`, so this resolves on every
# platform. Naming `aarch64-apple-darwin` literally made this line dead on any
# non-Apple host (measured 2026-08-31 on aarch64-unknown-linux-gnu, where that
# directory does not exist). The env/arg override above is unchanged.
RUSTC=${TRUST_RUSTC:-$REPO/build/host/stage1/bin/rustc}

FORCE=0
if [ "${1:-}" = "--force" ]; then
  FORCE=1
  rm -f "$SENTINEL"; echo "removed a stale sentinel"; shift
fi

OUT_NAME=${1:?usage: run_measurement_sweep.sh <out-dir-name> "<purpose>" [sample-size]}
PURPOSE=${2:-unspecified}
SIZE=${3:-2000}
OUT=$REPO/reports/trust-ir-producer-baseline-2026-07-01/$OUT_NAME

# --- THE LOCK, first, because it is the refusal that a build also honours ------
#
# Taken before every other check so that nothing can start a build in the window between
# "this sweep decided it was safe" and "this sweep published its sentinel" — which is
# precisely the window that killed a sweep 37 seconds in.
LOCK_ARGS=(acquire --kind measurement --purpose "$PURPOSE -> $OUT_NAME" --pid $$
           --contract "DO NOT run x.py while this is held; it deletes stage1/bin/rustc")
if [ "$FORCE" = 1 ]; then
  LOCK_ARGS+=(--break --reason "run_measurement_sweep.sh --force by $(id -un)")
fi
INHERITED_LOCK_TOKEN=${TRUST_BUILD_LOCK_TOKEN:-}
LOCK_TOKEN=$("${TARGO:-targo}" trust repo lock "${LOCK_ARGS[@]}" --repo-root "$REPO") || exit 3
[ -n "$LOCK_TOKEN" ] || { echo "REFUSING: the build lock returned no token"; exit 3; }

# THE TRAP, installed the instant the lock is held: every exit path from here on releases
# both artifacts. Explicit `exit` in the signal arms because a zsh trap body that falls
# through resumes the script, which would release the lock and then keep sweeping.
cleanup() {
  rm -f "$SENTINEL"
  if [ "$LOCK_TOKEN" != "$INHERITED_LOCK_TOKEN" ]; then
    "${TARGO:-targo}" trust repo lock release "$LOCK_TOKEN" --repo-root "$REPO" >/dev/null 2>&1
  fi
}
trap 'cleanup; exit 130' INT
trap 'cleanup; exit 143' TERM
trap cleanup EXIT

# --- remaining refusals, cheapest first ---------------------------------------
if [ -e "$SENTINEL" ]; then
  echo "REFUSING: a measurement is already in flight —"; sed 's/^/    /' "$SENTINEL"
  echo "  (if that pid is dead, re-run with --force)"; exit 3
fi
if [ ! -x "$RUSTC" ]; then
  echo "REFUSING: $RUSTC is missing (x.py deletes it at build start)"; exit 3
fi

# A rebuilt driver over an unstaged sysroot answers E0463 on EVERY file, which the scorecard
# faithfully records as ~2000 compile failures rather than "not ready". That has already produced
# one bogus measurement. Prove compilability before reserving the window.
#
# `-Z trust-verify=off` IS LOAD-BEARING, and omitting it made this gate refuse unconditionally.
# trustc is batteries-on: with verification live, `println!` raises an unproven panic-freedom
# obligation for an absent callee (std's body is not in the lowered bundle), the fail-closed
# default turns that into a BUILD ERROR, and the probe exits non-zero. That is the verifier
# working correctly — so the check reported "stage1 cannot compile hello-world" on a perfectly
# healthy stage1, every time, and no sweep could ever start. Measured 2026-08-19: exit 1 with
# "an unproven panic-freedom obligation for a call to an absent callee ... is a build error".
#
# The probe must therefore invoke the compiler THE WAY THE SWEEP DOES. The scorecard passes
# `-Z trust-verify=off` on every sampled file (producer-only measurement; the trust-ir hook is
# independent of the verifier), so a smoke test that omits it is not testing the thing that is
# about to run. It also still catches the case it exists for: an unstaged sysroot answers E0463
# whether or not the verifier is on.
TMP=$(mktemp -d)
printf 'fn main(){println!("ok");}\n' > "$TMP/hw.rs"
if ! "$RUSTC" -Z trust-verify=off --edition 2021 --emit=metadata --crate-type lib \
       -o "$TMP/hw.rmeta" "$TMP/hw.rs" >/dev/null 2>&1; then
  echo "REFUSING: stage1 rustc does not compile hello-world (E0463 / unstaged sysroot?)"
  rm -rf "$TMP"; exit 3
fi
rm -rf "$TMP"

{
  echo "pid=$$"
  echo "started=$(date '+%Y-%m-%d %H:%M:%S')"
  echo "purpose=$PURPOSE"
  echo "out=$OUT"
  echo "rustc=$("$RUSTC" --version)"
  echo "sample_size=$SIZE"
  echo "expected_minutes=~37"
  echo "lock_token=$LOCK_TOKEN"
  echo "contract=DO NOT run x.py while this file exists; it deletes stage1/bin/rustc"
  echo "enforced_by=targo trust repo lock (x.py takes the same lock)"
} > "$SENTINEL"

echo "=== measurement sentinel published (and the build lock is HELD):"
sed 's/^/    /' "$SENTINEL"; echo

# BACKGROUND + `wait`, not a foreground call. A caught signal that arrives while the shell
# is running a foreground external command is not delivered until that command RETURNS —
# so with `python3 ...` in the foreground, a `kill -TERM` on this script would sit unhandled
# for the whole remaining sweep and the trap above would be decorative. The `wait` builtin
# IS interruptible. Measured 2026-08-20: 20s trap latency foreground vs 0s through `wait`.
# TRUST_CORPUS_LOCK selects the CONTENT-PINNED corpus instead of re-deriving one
# with a seeded sample. The seeded sample is a function of the eligible
# population LENGTH and was never stable (see scripts/trust_ir_corpus_lock.py),
# so a locked sweep is the only kind directly comparable to a recorded one.
# --sample-size is meaningless under a lock — the lock IS the corpus — so it is
# omitted rather than passed and silently ignored.
if [ -n "${TRUST_CORPUS_LOCK:-}" ]; then
  echo "=== corpus: CONTENT-PINNED via $TRUST_CORPUS_LOCK (sampling bypassed)"
  # Trust (2026-08-28): timeout 60 -> 120 -> 240. issue-109004-drop-large-array.rs
  # compiles in ~15s SOLO but sits at the 60s edge under 8-way parallel load,
  # and it timed out in 3 of 5 corpus-locked sweeps in one session — each time
  # silently dropping its 7 bodies (1 Agreed) from the census and turning the
  # sweep comparison into a re-run. The cap exists to bound pathological
  # compiles, not to sample machine load. 120 then timed out TWICE more on a
  # SHARED machine (load average 18 from concurrent sessions; the same file,
  # 13.7s solo, measured between the two) — the bound must absorb external
  # load the sweep does not control, so 240. (A comment must sit HERE, above the command — a `#` line inside a
  # backslash continuation TERMINATES the argv at the previous token; measured:
  # one sweep silently ran fresh-sampled, lock and timeout both dropped.)
  python3 "$REPO/scripts/trust_ir_producer_scorecard.py" \
    --trustc "$RUSTC" --out-dir "$OUT" \
    --corpus-lock "$TRUST_CORPUS_LOCK" --jobs 8 --timeout 240 &
else
python3 "$REPO/scripts/trust_ir_producer_scorecard.py" \
  --trustc "$RUSTC" --out-dir "$OUT" \
  --sample-size "$SIZE" --jobs 8 --timeout 240 &
fi
wait $!
rc=$?
echo "=== sweep exited rc=$rc at $(date '+%H:%M:%S'); sentinel and build lock released"
exit $rc
