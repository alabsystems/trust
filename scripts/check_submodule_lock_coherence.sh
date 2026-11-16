#!/usr/bin/env bash
# check_submodule_lock_coherence.sh — can each first-party lock still be replayed?
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# WHY THIS EXISTS
# ---------------
# A `Cargo.lock` is an assertion — "this exact resolution is what this tree
# builds" — and `--locked` is the ONLY thing that ever reads it as one. Every
# other command treats a stale lock as a chore: it silently rewrites the file
# and carries on green.
#
# READ THIS BEFORE ASSUMING THIS SCRIPT IS THE ONLY PROBE. It is not, and the
# first version of this header wrongly said so ("no lane in this repo ran
# `--locked` over first-party/*"). `tools/preflight.py` tier 2b is a
# resolver-grade `metadata --locked` sweep over 45 workspaces. What keeps it
# quiet about `first-party/*` is not absence but GRADING:
#
#   * it is opt-in (`tools/preflight.sh --deep`); a plain `x.py build` takes
#     only CACHED verdicts, and an untouched tree has none;
#   * `lock_severity` returns FAIL only when "a bootstrap step resolves this
#     workspace with --locked", so a submodule skew prints as a WARN reading
#     `not on any build path`.
#
# That grading is right about the BUILD and wrong about the PACK: the pack
# builds the wp drivers STANDALONE, which is exactly where a stale lock gets
# rewritten and stamps `.dirty`. So this is not a second opinion on the same
# question — it asks the question the pack cares about, fail-closed, with no
# build-path exemption. If you are extending coverage, consider teaching
# `lock_severity` about the pack rather than growing this file.
#
# Measured 2026-09-20 with the stage2 targo (379912412): THREE of the nine
# submodules recorded a resolution that could no longer be replayed.
#
#   trust-wp   29 ay-* entries at 0.26.0; first-party/ay is pinned at 0.27.0
#   trust-mc   clean pinned at 68ad1b20; the manifests name 61c10a67
#   trust-vc   missing the num-integer edge that ay 0.27.0 added
#
# It is not cosmetic. A build whose lock must be rewritten rewrites it, which
# leaves the submodule worktree dirty, which makes the drivers' build.rs stamp
# `.dirty` into their version string — so the wp binaries in the 2026-09-19
# pack claim uncommitted edits about a checkout that has none, and no
# reproducible build of them was possible. The dirt is invisible besides:
# this clone sets `submodule.*.ignore = all`, so `git status` shows nothing.
#
# WHAT THIS DOES NOT DO
# ---------------------
# It does not fix anything, because the fix does not belong here: a refreshed
# lock has to be COMMITTED IN THE SUBMODULE and the gitlink moved deliberately
# (docs/first-party-pin-ledger.md). It prints the recipe instead.
#
# It resolves over the network by design — a git dependency whose rev is not in
# the local cache is exactly the drift being looked for, and `--offline` would
# report it as a false FAIL. Do not wire this into the push gate for that
# reason; run it before cutting a pack, and after any pin moves.
#
# Exit 0 iff every submodule carrying a Cargo.lock resolves under --locked.
set -euo pipefail

cd "$(git -C "$(dirname "$0")/.." rev-parse --show-toplevel)"

# The targo that IS targo. A stage whose targo was never rebuilt ships upstream
# cargo under the name, and `--unverified` is the only discriminator that has
# held (CLAUDE.md). This script runs no compilation, so it never names a lane;
# the probe is only here to reject a cargo-in-disguise before it answers.
TARGO="${TARGO:-}"
if [ -z "$TARGO" ]; then
  for candidate in build/host/stage2/bin/targo build/host/stage1/bin/targo "$(command -v targo || true)"; do
    if [ -n "$candidate" ] && [ -x "$candidate" ]; then TARGO="$candidate"; break; fi
  done
fi
if [ -z "$TARGO" ] || [ ! -x "$TARGO" ]; then
  echo "FAIL: no targo found. Build one (./x.py build) or set TARGO=<path>." >&2
  exit 2
fi
# Absolute, because each submodule is probed from inside its own directory and
# a relative path would resolve against that instead of the repo root.
case "$TARGO" in /*) ;; *) TARGO="$PWD/$TARGO" ;; esac
if ! "$TARGO" --unverified --version >/dev/null 2>&1; then
  echo "FAIL: '$TARGO' rejects --unverified, so it is upstream cargo wearing" >&2
  echo "      targo's name. A lock verdict from it is not about this toolchain." >&2
  exit 2
fi

# A HALF-BUILT SYSROOT REPORTS EVERY MODULE AS SKEWED. Resolution shells out to
# `trustc -vV`, so a targo whose sibling trustc is missing fails every probe
# with `could not execute process `trustc -vV``, which looks exactly like nine
# simultaneous lock failures. Measured 2026-09-20: run during an `x.py build`
# — which deletes the stage binaries at start — this printed 9/9 FAIL on a tree
# whose locks were all clean minutes earlier. Refuse instead of lying.
if [ ! -x "$(dirname "$TARGO")/trustc" ]; then
  echo "FAIL: no trustc beside '$TARGO'. Resolution shells out to \`trustc -vV\`," >&2
  echo "      so every module would report a false skew. If an x.py build is" >&2
  echo "      running, wait for it: the stage binaries are deleted at build start." >&2
  exit 2
fi

modules=()
while IFS= read -r line; do
  modules+=("${line#submodule.}")
done < <(git config --blob HEAD:.gitmodules --get-regexp 'submodule\..*\.path' | awk '{print $2}')

fail=0
checked=0
failed_paths=()
for path in "${modules[@]}"; do
  [ -f "$path/Cargo.toml" ] || { printf 'SKIP  %-24s no Cargo.toml\n' "$path"; continue; }
  [ -f "$path/Cargo.lock" ] || { printf 'SKIP  %-24s no Cargo.lock\n' "$path"; continue; }
  checked=$((checked + 1))
  err="$(mktemp)"
  # cd, NOT --manifest-path. Cargo reads .cargo/config.toml from the CURRENT
  # DIRECTORY upward, never from the manifest's ancestors, so a sweep run from
  # the superproject root resolves every submodule under the SUPERPROJECT's
  # config — a different graph than the standalone build this is a claim about.
  # Measured 2026-09-20: trust-vc FAILS via --manifest-path from the root and
  # PASSES from inside its own directory, with no file changing in between.
  # A PASS is RELATIVE TO THE CONFIG that applies from inside this directory,
  # and a `[patch]` there can hide a real skew. Measured 2026-09-20:
  # first-party/trust-vc's manifest names ay rev c1dd8ecb while its lock records
  # 849c19fa — a skew tools/preflight.py reports — yet `--locked` resolves,
  # because .cargo/config.toml patches that same git URL to `../ay` (the pinned
  # submodule), so the rev never participates. That is genuinely inert TODAY.
  # It stops being inert the moment the patch stops applying, and that config's
  # own header documents how: cargo DROPS a patch whose path source fails the
  # version requirement, silently, with a warning nobody reads. So annotate the
  # verdict rather than letting a bare PASS overstate it.
  patched=0
  if [ -f "$path/.cargo/config.toml" ]; then
    patched="$(grep -c '^\[patch\.' "$path/.cargo/config.toml" || true)"
  fi
  if (cd "$path" && "$TARGO" metadata --format-version 1 --locked >/dev/null 2>"$err"); then
    if [ "${patched:-0}" -gt 0 ]; then
      printf 'PASS  %-24s --locked resolves (under %s [patch] table(s) — verdict is patch-relative)\n' \
        "$path" "$patched"
    else
      printf 'PASS  %-24s --locked resolves\n' "$path"
    fi
  else
    # `error: unknown field ...` from a nested manifest inside a git checkout is
    # NOT the failure — that scan is non-fatal and exits 0. Report the line that
    # actually names the lock.
    reason="$(grep -m1 'cannot update the lock file' "$err" || grep -m1 '^error' "$err" || echo 'unknown')"
    printf 'FAIL  %-24s %s\n' "$path" "${reason:0:96}"
    failed_paths+=("$path")
    fail=1
  fi
  rm -f "$err"
done

echo
echo "summary: checked=${checked} failed=${#failed_paths[@]}"
if [ "$fail" -eq 0 ]; then
  echo "PASS: every first-party lock still replays"
  exit 0
fi

cat <<EOF

FAIL: a recorded resolution cannot be replayed. Anything built from these
submodules standalone rewrites the lock, dirties the worktree, and stamps
'.dirty' into the binaries' version string.

To fix ONE of them, refresh the lock where the pin actually builds and commit
it in the submodule — never by hand, and never in a sibling checkout whose own
siblings are at different versions (trust-wp's ay is a PATH dep, so its lock is
only correct relative to the ay beside it):

    cd ${failed_paths[0]}
    ${TARGO} metadata --format-version 1 >/dev/null   # rewrites Cargo.lock
    git diff Cargo.lock                               # read it: a version bump
                                                      # is expected, a resolver
                                                      # rewrite is not
    git checkout -b pin/\$(date +%Y-%m-%d)-lock-refresh
    git commit -m 'lock: ...' Cargo.lock
    git push origin HEAD:refs/heads/pin/...

then move the gitlink in the superproject and record it:
docs/first-party-pin-ledger.md. Pin to the pushed branch, not to the sibling's
main — trust-wp's main is hundreds of commits past its pin.
EOF
exit 1
