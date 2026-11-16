#!/usr/bin/env bash
# Trust: targo-trust's own unit tests, as one scoped push lane (TRUST-KI-1014-3).
#
# WHY THIS EXISTS. Until 2026-10-14 no push row ran a single targo-trust test.
# `scoped.compiler-check` lists targo-trust/ in its scope, but x.py check has no
# step for it; `fast.targo-trust-check` compiles its targets and runs none, and
# is not in the push tier; `quick.targo-trust-tests` runs the whole suite and is
# not in the push tier either; `scoped.crates-tests` BUILDS targo-trust only to
# hand it to trust-integration-tests. So a change under targo-trust/, or under
# one of the `crates/` packages it is built from (a `trust-vcgen` change reaches
# targo-trust), was pushed with none of targo-trust's own tests run
# (docs/KNOWN_HAZARDS.md, TRUST-KI-1014-3).
#
# WHAT IT RUNS, AND WHAT IT DOES NOT. The unit binary alone:
#
#     targo --unverified test --manifest-path targo-trust/Cargo.toml --locked --bin targo-trust
#
# (targo-trust has no lib target: its unit tests are the `--bin` test binary),
# default features, ~2,240 tests in 33-36 s once built (measured 2026-10-14 on an
# 18-core Mac at a load of 26-54; a cold build of the test profile took 6.6 min,
# an incremental one after a targo-trust change 33 s). NOT the integration
# binaries under targo-trust/tests/: the whole suite takes 16-22 minutes, and
# while it runs the first exec of any new file on a Mac waits 10-61 s
# (TRUST-KI-1014-3), a cost no push should pay for every change in scope.
# `quick.targo-trust-tests` still runs them.
#
# SCOPE — why this is not paid on every push. The lane runs only when the push
# changes what the unit binary is built from:
#
#   * anything under targo-trust/ (its sources, Cargo.toml, Cargo.lock, tests);
#   * the directory of any local package in targo-trust's dependency graph, as
#     `targo metadata` resolves it for the default features (48 of the crates/
#     packages, one vendor/ package and 73 first-party packages on 2026-10-14),
#     a first-party gitlink that holds one (a moved pin changes that package),
#     and Cargo.toml, whose [workspace] tables the crates/ packages
#     inherit from;
#   * the root .cargo/ directory, whose config every build here reads.
#
# The graph is read only when a changed path could be in it (crates/, vendor/,
# first-party/, .cargo/), in about a second, offline and --locked. A graph that
# cannot be read RUNS the tests — failing toward running, never toward
# skipping. Anything else prints SKIPPED and exits 0, the same idiom as
# scoped.completion-gate-tests.
#
# ONLY THE SCOPE DECISION reads the pushed refs. The tests run on THIS
# WORKTREE, which is the pushed tip in the ordinary case (the hook runs from
# the worktree being pushed). A push of some OTHER ref is scoped by that ref's
# changes but tested against this worktree, as in scoped.completion-gate-tests.
#
# THE BUILD uses the caller's Cargo/Targo target selection. The pre-push hook
# defaults it to this worktree's crates/target, matching the landing gate and
# scoped.crates-tests' targo-trust prebuild. A direct invocation without an
# override uses targo-trust/target by default. No build/ lock: nothing here
# reads or writes build/.
#
# Usage: check_targo_trust_unit_tests.sh [base-ref]
#   With base-ref, scope is `<base-ref>...HEAD`. Without it, scope is the pushed
#   refs in TRUST_PUSHED_REFS (scripts/hooks/pre-push exports them), else
#   `origin/main...HEAD` — see WHAT THIS PUSH CHANGES below. Exits 0 when green
#   OR out of scope (every out-of-scope exit prints a line beginning
#   `SKIPPED: `, which the harness grades SKIP, not PASS), 1 when red or when
#   the run reported no test (ZERO TESTS IS NOT A PASS), 2 when it cannot run
#   (no targo).
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
set -uo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel 2>/dev/null)" || {
  echo "not inside a git worktree" >&2
  exit 2
}
cd "$REPO_ROOT" || exit 2

# An owned `land_gate land` transaction only ADDS the full canonical suite.
# This is not a saved PASS: the helper runs all targets now. The hook keeps
# its actual child exit in shell-local state, outside all test subprocesses.
if [ -n "${TRUST_LAND_TARGO_HEAD:-}" ]; then
  exec python3 scripts/land_gate.py landing-targo
fi

# WHAT THIS PUSH CHANGES — the subject the scope is judged on, read exactly as
# scripts/check_completion_gate_tests.sh reads it (its comment block of the same
# name says why each part is as it is: two dots for an update, three for a new
# branch, --no-renames, -z, --ignore-submodules=none, and an undiffable range
# runs the lane). scripts/tests/scoped_lane_push_scope_test.py drives this lane
# through the same cases as the other copies, so they cannot drift apart unseen.
ranges=()
if [ -n "${1:-}" ]; then
  ranges=("$1...HEAD")
  against="$1"
  subject="$1...HEAD (explicit base argument; TRUST_PUSHED_REFS not read)"
else
  while read -r _local_ref local_sha _remote_ref remote_sha _rest; do
    [ -n "${remote_sha:-}" ] || continue                  # not a four-field ref line
    case "$local_sha" in *[!0]*) ;; *) continue ;; esac   # a deletion pushes nothing
    case "$remote_sha" in
      *[!0]*) ranges+=("$remote_sha..$local_sha") ;;      # an update: remote tree vs pushed tree
      *) ranges+=("origin/main...$local_sha") ;;          # a new branch: what it adds since its fork
    esac
  done <<<"${TRUST_PUSHED_REFS:-}"
  if [ "${#ranges[@]}" -gt 0 ]; then
    against="the pushed refs"
    subject="the pushed refs (TRUST_PUSHED_REFS, ${#ranges[@]} update(s)); an update is the tree diff <remote>..<local>, a new branch origin/main...<local>: ${ranges[*]}"
  else
    ranges=("origin/main...HEAD")
    against="origin/main"
    if [ -n "${TRUST_PUSHED_REFS:-}" ]; then
      subject="origin/main...HEAD (TRUST_PUSHED_REFS names no update to diff, only deletions or malformed lines)"
    else
      subject="origin/main...HEAD (no push in flight; TRUST_PUSHED_REFS unset or empty)"
    fi
  fi
fi
echo "SUBJECT: $subject"

changed=""
undiffable=""
for range in "${ranges[@]}"; do
  if part="$(set -o pipefail; git -c diff.renames=false diff --no-renames --ignore-submodules=none --name-only -z "$range" 2>/dev/null | tr '\0' '\n')"; then
    [ -z "$part" ] || changed+="$part"$'\n'
  else
    undiffable="$range"
    break
  fi
done
changed="$(printf '%s' "$changed" | LC_ALL=C sort -u)"

# The paths a change under which can change the unit binary, beyond
# targo-trust/ itself: every local package in its default-feature dependency
# graph, by directory. Printed one per line, relative to the repository root,
# each ending in `/`; a first-party gitlink holding one is printed bare. Fails
# (and prints nothing) when the graph cannot be read.
dependency_scope() {
  local metadata units
  units="$(targo --unverified test --manifest-path targo-trust/Cargo.toml --locked --offline \
    --bin targo-trust --unit-graph -Z unstable-options 2>/dev/null)" || return 1
  metadata="$(targo metadata --manifest-path targo-trust/Cargo.toml --format-version 1 \
    --locked --offline 2>/dev/null)" || return 1
  "$PYTHON_BIN" -c '
import json, os, sys
root = os.path.realpath(sys.argv[1])
metadata, unit_graph = json.load(sys.stdin)
packages = metadata["packages"]
manifest = os.path.join(root, "targo-trust", "Cargo.toml")
roots = [p["id"] for p in packages if os.path.realpath(p["manifest_path"]) == manifest]
if len(roots) != 1 or unit_graph["version"] != 1:
    sys.exit(1)
units = unit_graph["units"]
if not units or not unit_graph["roots"] or any(units[i]["pkg_id"] != roots[0] for i in unit_graph["roots"]):
    sys.exit(1)
# Metadata unifies features across every workspace member, overapproximating
# optional compiler edges. Only the native unit graph represents this exact
# default-feature test invocation, including its host/build dependencies.
reachable = {unit["pkg_id"] for unit in units}
if not reachable.issubset({p["id"] for p in packages}):
    sys.exit(1)
scope = {"Cargo.toml", "Cargo.lock"}
for package in packages:
    if package["id"] not in reachable:
        continue
    if package.get("source") is not None:
        continue  # a registry or git package: nothing in this tree
    directory = os.path.relpath(os.path.dirname(os.path.realpath(package["manifest_path"])), root)
    if directory.startswith(".."):
        continue
    scope.add(directory + "/")
    parts = directory.split("/")
    if len(parts) >= 2 and parts[0] == "first-party":
        scope.add("first-party/" + parts[1])
    if parts[0] == "crates":
        scope.add("Cargo.toml")
if not scope:
    sys.exit(1)
print("\n".join(sorted(scope)))
' "$REPO_ROOT" <<<"[$metadata,$units]"
}

if [ -x /usr/bin/python3 ]; then
  PYTHON_BIN=/usr/bin/python3
elif command -v python3 >/dev/null 2>&1; then
  PYTHON_BIN="$(command -v python3)"
else
  PYTHON_BIN=""
fi

in_scope=""
if [ -n "$undiffable" ]; then
  echo "cannot compute the diff $undiffable — running rather than assuming safe"
elif [ -z "$changed" ]; then
  echo "SKIPPED: no changes against $against — nothing to check"
  exit 0
else
  in_scope="$(grep -E '^(targo-trust/|\.cargo/)' <<<"$changed")"
  if [ -z "$in_scope" ] && grep -qE '^(crates|vendor|first-party)/' <<<"$changed"; then
    if [ -n "$PYTHON_BIN" ] && command -v targo >/dev/null 2>&1 \
        && scope="$(dependency_scope)"; then
      # A changed path is in scope when it is a gitlink or file the scope
      # names, or lies under a package directory it names.
      in_scope="$(awk 'NR == FNR { scope[$0] = 1; if ($0 ~ /\/$/) dirs[$0] = 1; next }
        { if ($0 in scope) { print; next }
          for (d in dirs) if (index($0, d) == 1) { print; next } }' \
        <(printf '%s\n' "$scope") <(printf '%s\n' "$changed"))"
    else
      echo "cannot read targo-trust's dependency graph (targo metadata, python3) — running"
      echo "rather than assuming safe"
      in_scope="(the dependency graph could not be read)"
    fi
  fi
  if [ -z "$in_scope" ]; then
    echo "SKIPPED: nothing targo-trust's unit binary is built from changed against $against —"
    echo "         this lane cannot be broken by this push."
    echo "         (changed: $(wc -l <<<"$changed" | tr -d ' ') file(s))"
    exit 0
  fi
  echo "in scope: $(wc -l <<<"$in_scope" | tr -d ' ') relevant path(s) changed vs $against:"
  head -20 <<<"$in_scope" | sed 's/^/  /'
fi

# PREREQUISITES ARE A FAILURE, NOT A SKIP: in scope means this push changes what
# the binary is built from, and a lane that then exits 0 because the machine
# lacks targo passed without running.
if ! command -v targo >/dev/null 2>&1; then
  echo "FAIL: targo-trust unit tests NOT RUN — no \`targo\` on PATH (the Trust toolchain's Cargo;"
  echo "      docs/BUILD_AND_INSTALL.md)" >&2
  exit 2
fi

echo "targo-trust unit tests: targo --unverified test --manifest-path targo-trust/Cargo.toml --locked --bin targo-trust"
output_file="$(mktemp -t trust-targo-trust-unit.XXXXXX)" || exit 2
trap 'rm -f "$output_file"' EXIT
targo --unverified test --manifest-path targo-trust/Cargo.toml --locked --bin targo-trust 2>&1 \
  | tee "$output_file"
status="${PIPESTATUS[0]}"
# ZERO TESTS IS NOT A PASS: a binary that reports no passed test ran nothing.
passed="$(sed -nE 's/^test result: ok\. ([0-9]+) passed; 0 failed.*/\1/p' "$output_file" | tail -1)"
if [ "$status" -ne 0 ]; then
  echo "targo-trust unit tests: FAIL (exit $status)"
  exit 1
fi
if [ -z "$passed" ] || [ "$passed" -eq 0 ]; then
  echo "targo-trust unit tests: FAIL — the run reported no passed test"
  exit 1
fi
echo "targo-trust unit tests: PASS ($passed passed)"
