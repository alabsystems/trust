#!/usr/bin/env bash
# Trust: the bootstrap recreator's and the sealing script's own tests, as one
# scoped push lane.
#
# WHY THIS EXISTS. scripts/recreate_bootstrap.py builds every toolchain from a
# seed and scripts/promote-toolchain.sh seals it. Their tests,
# scripts/tests/recreate_bootstrap_test.py and
# scripts/tests/promote_toolchain_test.sh, ran in NO push row: only under the
# fast-profile aggregate `scripts.tests.suite` (scripts/check_script_tests.sh),
# which the pre-push hook does not run and whose row has never recorded a
# green. So on 2026-10-12 two fixes to exactly these scripts (a7ebff4816: the
# prerequisite report is the native-authority capture; 5a2d23c537: a tool-start
# gate at sealing time) each landed through a hook that printed PRE-PUSH: GREEN
# without running one of their tests; the evidence for them was whoever ran the
# files by hand. It is the hole that let a tippy that could not start sit on
# main for three days: a subject no push lane exercises.
#
# WHAT IT RUNS. The four files in TESTS, each exactly as the aggregate runs it
# (`python -B <file>`, `bash <file>`, stdin at /dev/null), under the newest
# Python >= 3.11 on PATH. The daily suite executes production snapshot boundaries
# with real isolated Git and the unchanged recreator audit. Retain each actual
# suite duration; earlier two-suite timing does not include daily staging.
#
# SCOPE: when it runs. Only when the push changes a file in SCOPE below: the
# registered tests, this lane, and the code those load or run from
# the tree. Each entry was read from the load site named beside it, not
# guessed, and scripts/tests/check_bootstrap_script_tests_test.py re-derives
# the list from the same sources on every push, in both directions (an entry
# nothing loads, a load no entry names). Anything else prints SKIPPED and exits
# 0, the idiom of scoped.compiler-check and scoped.completion-gate-tests. A
# range that cannot be diffed is in scope: failing toward running.
#
# NOT SEEN, and said on every run: what the registered tests read from the tree as
# DATA is not in SCOPE, so a push that changes only such a file is not tested
# here. Measured 2026-10-12 with an audit hook over the recreate test's own
# process (887 files of the checkout opened): 868 Cargo.toml manifests, those of
# the nine first-party submodules among them (the stage0 manifest-closure
# tests), INSTALL.md, README.md, docs/BOOTSTRAP_FROM_SCRATCH.md and
# docs/BUILD_AND_INSTALL.md (the tests that hold those documents to what the
# script prints), src/bootstrap/defaults/bootstrap.compiler.toml and five
# sources under src/bootstrap/src/core/ (read through tools/preflight.py),
# .cargo/config.toml and x. The promote test copies six probe sources from
# tests/ui/trust/ (its own `for rel in` list) and reads no other data. The
# aggregate still runs both tests on any tree; whether a data file should
# bring this lane into scope is an open cost question (a first-party pin
# move would).
#
# Usage: check_bootstrap_script_tests.sh [base-ref]
#   With base-ref, scope is `<base-ref>...HEAD`. Without it, scope is the pushed
#   refs in TRUST_PUSHED_REFS (scripts/hooks/pre-push exports them), else
#   `origin/main...HEAD`: see WHAT THIS PUSH CHANGES below. Exits 0 when green
#   OR out of scope, 1 when a test is red or the lane refuses to judge.
#   Every out-of-scope exit (an empty diff included) prints a line beginning
#   `SKIPPED: `: the harness and the hook grade that SKIP, not PASS, so a run
#   that tested nothing can never advance this row's `last_green`.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
set -uo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel 2>/dev/null)" || {
  echo "not inside a git worktree" >&2
  exit 2
}
cd "$REPO_ROOT" || exit 2

# The tests, as a fixed list: a glob would pick up or drop a file on a rename.
TESTS=(
  scripts/tests/recreate_bootstrap_test.py
  scripts/tests/promote_toolchain_test.sh
  scripts/tests/daily_toolchain_stage_test.py
  scripts/tests/seed_lock_inventory_test.py
)

# What the registered tests run from the tree. Exact paths; each line says where it is
# loaded (file:line as of 2026-10-12, or the name that holds the list).
#   scripts/recreate_bootstrap.py   the subject; recreate_bootstrap_test.py:29
#       loads it by path (SCRIPT)
#   scripts/promote-toolchain.sh    the subject; promote_toolchain_test.sh:13
#       copies it into a fixture repository and runs it there
#   scripts/tests/recreate_bootstrap_test.py, scripts/tests/promote_toolchain_test.sh
#       the tests
#   scripts/check_bootstrap_script_tests.sh   this lane
#   scripts/seed_host_ledger.py     recreate_bootstrap.py seed_host_ledger_module()
#       imports it by path; the recreate test copies and loads it
#   scripts/seed_fixed_point.py     seed_host_ledger.py fixed_point_module() loads it
#       by path for a record of the fixed-point kind (capture_host_record)
#   scripts/check_seed_freshness.py recreate_bootstrap.py validate_seed() and
#       capture_validated_seed_lineage() start it as a child; the recreate test
#       runs the real one from a scratch checkout (SEED_VALIDATION_SCRIPTS)
#   scripts/mint_seed_support.py    imported by check_seed_freshness.py
#       (native_payload_host, configured_seed_overrides); same list
#   scripts/create_local_genesis_stage0.py   recreate_bootstrap.py
#       _load_genesis_adapter_generator() compiles and runs its source, and
#       ensure_local_genesis_stage0() starts it. The recreate test never opens
#       the real one (measured), so it is here as code the SUBJECT loads
#   tools/preflight.py              recreate_bootstrap_test.py loads it by path
#       (GeneratedCompilerProfileTests, StageToolProducersMatchBootstrapTests).
#       Outside scripts/, and an import all the same
#   tools/verify-toolchain.sh       promote-toolchain.sh:173 runs it; the
#       promote test copies it (its `for rel in` list, line 13)
#   scripts/verify_sysroot_libraries.py  promote-toolchain.sh verify_surface()
#       checks full host/installed std targets; copied by the promote test
#   scripts/lib/trust_toolchain_surface.sh   sourced by tools/verify-toolchain.sh:519
#       and required by promote-toolchain.sh:166; same list
#   scripts/lib/trust_build_provenance.py    promote-toolchain.sh:720 runs it;
#       the promote test loads it too (line 406); same list
#   scripts/lib/seal_content_identity.py     promote-toolchain.sh:701 and :1335
#       run it; the promote test runs the checkout's copy (lines 339, 366)
#   scripts/lib/stage_receipt_provenance.py  promote-toolchain.sh:742 runs it
#       (prov_stage_receipt: the stage receipt a seal names in its PROVENANCE);
#       the promote test copies it (same list), and the recreate test loads it
#       by path (STAGE_RECEIPT_READER, line 39) to hold its rules to the
#       recreator's
#   scripts/prune_seal_symlinks.py  promote-toolchain.sh:1184 runs it; same list
#   scripts/freeze_toolchain_sources.py  promotion freezes the committed std
#       closure with it; the promote suite also runs its dedicated Git controls
#   scripts/tests/freeze_toolchain_sources_test.py  invoked by the promote suite
#   src/tools/trust-stage0-dist/prepare.py  supplies the existing TOML writer
#       used by source-manifest normalization; copied by the promote fixture
#   scripts/bootstrap_dependency_closure.py  recreate_bootstrap.py
#       stage0_bootstrap_manifest_roots() compiles and runs its source (the
#       shared recipe-manifest reader); src/bootstrap/bootstrap.py runs it before
#       build-ish compilation. The recreate test reaches it through
#       the recreator
#   Native build-tree ownership is exercised through the selected Targo image;
#       the preservation fixture no longer copies or runs a shell lock owner.
#   scripts/mint_seed_recovery.py  mint_and_prove_seed.sh and mint_seed_support.py
#       load recovery state while reconstructing a seed.
#   scripts/native_sdk_tools.py and scripts/sdk_frontend_component.py
#       promote-toolchain.sh runs native SDK and frontend identity checks.
#   scripts/seed_custody_source.py and scripts/lib/seed_linux.py
#       daily_toolchain_stage.py and its tests load the custody/platform adapters.
#   scripts/daily_dependency_git.py and scripts/daily_registry_proxy.py
#       daily_toolchain_stage.py and its tests load dependency/registry transport.
#   Incremental reclamation runs the native build-tree library through an
#       actual Bootstrap/Targo frontend; its Rust tests own that policy.
# Named by the subjects and NOT loaded, so not here: scripts/check_driver_extra_symbols.py,
# scripts/seed_staircase.py (words in promote-toolchain.sh's messages and usage).
# The imported Clean Lean tests execute mint's actual closed environment.
# The imported build-slot tests execute the actual admission script with fixture
# account-directory lookup and real locks; they never use the user's slot pool.
# The lock-inventory test loads seed_input_archives.py, which loads
# seed_input_records.py and the already-scoped bootstrap_dependency_closure.py;
# its manifest graph is the already-scoped recreator source.
# The daily suite also loads the reproducer's real Git authority reader and runs
# its own real Git fixtures; its other pipeline owners remain explicit fixtures.
SCOPE=(
  scripts/daily_toolchain_stage.py
  scripts/tests/daily_toolchain_stage_test.py
  scripts/tests/seed_lock_inventory_test.py
  scripts/seed_input_archives.py
  scripts/seed_input_records.py
  scripts/tests/fixtures/publication_daily_consumer_outcomes.py
  scripts/submodule_sync.sh
  scripts/recreate_bootstrap.py
  scripts/bootstrap_xpy.py
  scripts/tests/bootstrap_xpy_environment_test.py
  scripts/tests/seed_runtime_prerequisite_test.py
  scripts/promote-toolchain.sh
  scripts/tests/recreate_bootstrap_test.py
  scripts/tests/mint_clean_lean_inputs_test.py
  scripts/tests/build_slot_test.py
  scripts/build-slot
  scripts/mint_and_prove_seed.sh
  scripts/tests/promote_toolchain_test.sh
  scripts/check_bootstrap_script_tests.sh
  scripts/seed_host_ledger.py
  scripts/seed_fixed_point.py
  scripts/seed_root_initialization.py
  scripts/seed_custody_source.py
  scripts/lib/seed_linux.py
  scripts/daily_dependency_git.py
  scripts/daily_registry_proxy.py
  scripts/check_seed_freshness.py
  scripts/lib/native_serial.py
  scripts/lib/landing_targo.py
  scripts/lib/seed_compiler_identity.py
  scripts/mint_seed_support.py
  scripts/mint_seed_recovery.py
  scripts/native_sdk_tools.py
  scripts/sdk_frontend_component.py
  scripts/sdk_targo_component.py
  scripts/sdk_targo_current_component.py
  scripts/sdk_targo_transport_witness.py
  scripts/create_local_genesis_stage0.py
  tools/preflight.py
  tools/verify-toolchain.sh
  scripts/verify_sysroot_libraries.py
  scripts/lib/trust_toolchain_surface.sh
  scripts/lib/trust_build_provenance.py
  scripts/lib/seal_content_identity.py
  scripts/lib/stage_receipt_provenance.py
  scripts/prune_seal_symlinks.py
  scripts/freeze_toolchain_sources.py
  scripts/tests/freeze_toolchain_sources_test.py
  src/tools/trust-stage0-dist/prepare.py
  src/tools/trust-stage0-dist/bootstrap_steps.py
  scripts/bootstrap_dependency_closure.py
  x.py
)

# WHAT THIS PUSH CHANGES: the subject the scope is judged on. Three readings,
# and the `SUBJECT:` line says which one ran. This is the block
# scripts/check_completion_gate_tests.sh and scripts/check_compiler_targets_build.sh
# carry (their comments give the history of each choice), kept the same on
# purpose; scripts/tests/scoped_lane_push_scope_test.py drives all three lanes
# through it:
#
#   * a base-ref argument: `<base-ref>...HEAD`;
#   * otherwise, under scripts/hooks/pre-push, TRUST_PUSHED_REFS (one
#     "<local-ref> <local-sha> <remote-ref> <remote-sha>" line per update): the
#     UNION over every pushed update of the TREE diff `<remote-sha>..<local-sha>`
#     (so a force push that drops in-scope commits is in scope); a new branch
#     (all-zero remote-sha) contributes `origin/main...<local-sha>`, and a
#     deletion (all-zero local-sha) nothing;
#   * otherwise (unset, empty, or naming only deletions or lines that are not
#     four fields): `origin/main...HEAD`.
#
# --no-renames, so a file moved OUT of scope still counts (its old path is
# listed as deleted); -z, so a path git would C-quote is compared as it is;
# --ignore-submodules=none, so no setting hides a changed entry. A range whose
# diff cannot be computed (an unresolvable base, an object this clone lacks, no
# merge base) is not a licence to skip: it counts as in scope.
#
# One thing differs from the two lanes above, because of WHICH TREE IS TESTED
# below: this lane remembers, per range, the commit whose tree it stands for
# (`tips`), and which of them are in scope.
ranges=()
tips=()
if [ -n "${1:-}" ]; then
  ranges=("$1...HEAD")
  tips=(HEAD)
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
    tips+=("$local_sha")
  done <<<"${TRUST_PUSHED_REFS:-}"
  if [ "${#ranges[@]}" -gt 0 ]; then
    against="the pushed refs"
    subject="the pushed refs (TRUST_PUSHED_REFS, ${#ranges[@]} update(s)); an update is the tree diff <remote>..<local>, a new branch origin/main...<local>: ${ranges[*]}"
  else
    ranges=("origin/main...HEAD")
    tips=(HEAD)
    against="origin/main"
    if [ -n "${TRUST_PUSHED_REFS:-}" ]; then
      subject="origin/main...HEAD (TRUST_PUSHED_REFS names no update to diff, only deletions or malformed lines)"
    else
      subject="origin/main...HEAD (no push in flight; TRUST_PUSHED_REFS unset or empty)"
    fi
  fi
fi
echo "SUBJECT: $subject"

scope_lines="$(printf '%s\n' "${SCOPE[@]}")"
changed=""
relevant=""
undiffable=""
tested_tips=()   # the commits whose trees this lane must speak for
i=0
while [ "$i" -lt "${#ranges[@]}" ]; do
  range="${ranges[$i]}"
  tip="${tips[$i]}"
  i=$((i + 1))
  if part="$(set -o pipefail; git -c diff.renames=false diff --no-renames --ignore-submodules=none --name-only -z "$range" 2>/dev/null | tr '\0' '\n')"; then
    [ -n "$part" ] || continue
    changed+="$part"$'\n'
    if hits="$(grep -Fx -e "$scope_lines" <<<"$part")"; then
      relevant+="$hits"$'\n'
      tested_tips+=("$tip")
    fi
  else
    [ -n "$undiffable" ] || undiffable="$range"
    tested_tips+=("$tip")
  fi
done
changed="$(printf '%s' "$changed" | LC_ALL=C sort -u)"
relevant="$(printf '%s' "$relevant" | LC_ALL=C sort -u)"

not_seen() {
  echo "$1 the tree files the registered tests read as data are outside this lane's scope (Cargo.toml"
  echo "$1 manifests and first-party pins, four documents, src/bootstrap/ sources, six"
  echo "$1 tests/ui/trust probes: the NOT SEEN paragraph of scripts/check_bootstrap_script_tests.sh)."
}

if [ -n "$undiffable" ]; then
  echo "cannot compute the diff $undiffable — running rather than assuming safe"
elif [ -z "$changed" ]; then
  echo "SKIPPED: no changes against $against — nothing to check"
  exit 0
elif [ -z "$relevant" ]; then
  echo "SKIPPED: neither the bootstrap recreator, the sealing script, their two tests, nor code"
  echo "         those load changed against $against — this lane ran nothing."
  echo "         (changed: $(wc -l <<<"$changed" | tr -d ' ') file(s))"
  not_seen "        "
  exit 0
fi
if [ -n "$relevant" ]; then
  echo "in scope: $(wc -l <<<"$relevant" | tr -d ' ') relevant file(s) changed vs $against:"
  sed 's/^/  /' <<<"$relevant"
fi

refuse() {
  # A lane that cannot say which tree it tested has tested nothing it can
  # vouch for. Red, never SKIPPED: in scope means this push changes the
  # recreator, the sealer or their tests.
  echo "bootstrap-script tests NOT RUN — this is a red, not a pass." >&2
  exit 1
}

# WHICH TREE IS TESTED. The tests are files that load other files of a
# checkout, so they run in THIS checkout, and the verdict is about a pushed
# commit only if this checkout holds that commit's tree. The two older
# shell-scoped lanes take only their SCOPE from the pushed refs and then test
# the worktree whatever it holds (their own comments name the gap). This lane
# establishes the identity or refuses:
#
#   1. every pushed commit that is in scope (or whose range could not be
#      diffed) has HEAD's tree. `git push origin HEAD:main` and a push of the
#      checked-out branch satisfy it; `git push origin other-branch` from a
#      checkout of something else does not, and is refused by name;
#   2. no tracked file is modified, staged or deleted against HEAD (submodule
#      worktrees are judged in 4);
#   3. every SCOPE file is, byte for byte, HEAD's blob (read through `git
#      cat-file` and `cmp`: no stat cache, no filter), and a SCOPE path HEAD
#      does not hold does not exist here;
#   4. every submodule HEAD pins is checked out at its pin with no tracked
#      modification: the recreate test reads the first-party trees' Cargo.toml
#      manifests from the checkout (all nine, measured), and
#      Stage0ManifestCapabilityTests.test_recipe_roots_are_source_derived_and_new_literal_roots_cannot_disappear
#      fails outright without first-party/ty. The older lanes answer a stale
#      submodule the same way: a FAIL that names scripts/submodule_sync.sh,
#      never a SKIP and never a weaker test.
#
# NOT established: files git does not track (an untracked or ignored file
# could change a verdict only by shadowing a module on the tests' import path,
# scripts/tests/ and scripts/lib/, and is not compared), and, outside SCOPE, a
# tracked file whose edit an index flag hides from `git status` (skip-worktree,
# assume-unchanged).
head_commit="$(git rev-parse --verify --quiet 'HEAD^{commit}')" || {
  echo "FAIL: cannot resolve HEAD: there is no checkout to test" >&2
  refuse
}
head_tree="$(git rev-parse --verify --quiet 'HEAD^{tree}')" || {
  echo "FAIL: cannot resolve HEAD^{tree}" >&2
  refuse
}
identity_fail=0
for tip in ${tested_tips[@]+"${tested_tips[@]}"}; do
  [ "$tip" != HEAD ] || continue
  if ! tip_tree="$(git rev-parse --verify --quiet "$tip^{tree}")"; then
    echo "FAIL: the pushed commit $tip is in scope, and this clone cannot read its tree." >&2
    identity_fail=1
  elif [ "$tip_tree" != "$head_tree" ]; then
    echo "FAIL: the pushed commit $tip is in scope, and this checkout holds another tree" >&2
    echo "      (HEAD is $head_commit). The tests run on the files of a checkout, so they would" >&2
    echo "      judge HEAD and not that commit." >&2
    identity_fail=1
  fi
done
if [ "$identity_fail" -ne 0 ]; then
  echo "      Push from a clean checkout of the commit being pushed, for example" >&2
  echo "          git worktree add --detach <dir> <commit> && bash scripts/submodule_sync.sh --root <dir> --fetch --restore" >&2
  echo "      and \`git -C <dir> push <remote> HEAD:<branch>\` from there." >&2
  refuse
fi

if ! dirty="$(git --no-optional-locks status --porcelain=v1 --untracked-files=no --ignore-submodules=all 2>/dev/null)"; then
  echo "FAIL: \`git status\` failed, so this checkout cannot be compared with HEAD" >&2
  refuse
fi
if [ -n "$dirty" ]; then
  echo "FAIL: this checkout has uncommitted changes to tracked files, so it is not the tree of" >&2
  echo "      $head_commit and the tests would judge something no push carries:" >&2
  head -10 <<<"$dirty" | sed 's/^/        /' >&2
  echo "      Commit them (and push that), or push from a clean checkout of the commit." >&2
  refuse
fi

mismatch=""
for path in "${SCOPE[@]}"; do
  if git cat-file -e "HEAD:$path" 2>/dev/null; then
    if [ ! -f "$path" ] || [ -L "$path" ] || ! git cat-file blob "HEAD:$path" | cmp -s - "$path"; then
      mismatch+="        $path (differs from the blob HEAD holds)"$'\n'
    fi
  elif [ -e "$path" ] || [ -L "$path" ]; then
    mismatch+="        $path (HEAD holds no such file; one exists here)"$'\n'
  fi
done
if [ -n "$mismatch" ]; then
  echo "FAIL: files this lane's tests run are not, byte for byte, what HEAD holds:" >&2
  printf '%s' "$mismatch" >&2
  echo "      (a filter or line-ending conversion, an index flag hiding an edit, or an untracked" >&2
  echo "      file). Push from a clean checkout of the commit." >&2
  refuse
fi

if ! gitlinks="$(git ls-tree -r HEAD 2>/dev/null | awk '$1 == "160000" { pin = $3; sub(/^[^\t]*\t/, ""); print pin "\t" $0 }')"; then
  echo "FAIL: cannot list the submodules HEAD pins" >&2
  refuse
fi
stale=""
while IFS=$'\t' read -r pin module; do
  [ -n "$module" ] || continue
  if [ ! -e "$module/.git" ]; then
    stale+="        $module: not checked out (pin ${pin:0:12})"$'\n'
  elif ! at="$(git -C "$module" rev-parse --verify --quiet 'HEAD^{commit}')"; then
    stale+="        $module: its HEAD cannot be read (pin ${pin:0:12})"$'\n'
  elif [ "$at" != "$pin" ]; then
    stale+="        $module: at ${at:0:12}, pinned ${pin:0:12}"$'\n'
  else
    first="$(git -C "$module" --no-optional-locks status --porcelain=v1 --untracked-files=no --ignore-submodules=all 2>&1 | head -1)"
    [ -z "$first" ] || stale+="        $module: at its pin, but not clean (git status: $first)"$'\n'
  fi
done <<<"$gitlinks"
if [ -n "$stale" ]; then
  echo "FAIL: this checkout does not hold the submodule sources the pushed tree pins:" >&2
  printf '%s' "$stale" >&2
  echo "      scripts/tests/recreate_bootstrap_test.py reads the first-party trees' Cargo.toml" >&2
  echo "      manifests from the checkout (one of its tests fails outright without first-party/ty)," >&2
  echo "      so a verdict here would not be about the pins. Run" >&2
  echo "          bash scripts/submodule_sync.sh --fetch --restore" >&2
  echo "      (never a blanket \`git submodule update\`) until \`bash scripts/submodule_sync.sh\`" >&2
  echo "      reports every worktree at its pin, then push again." >&2
  refuse
fi
echo "tree under test: this checkout, which holds the tree of $head_commit: tracked files unmodified, the ${#SCOPE[@]} scope files byte-identical to its blobs, $(grep -c . <<<"$gitlinks" | tr -d ' ') submodule(s) at their pins"

# The recreate test skips whole classes below 3.11 (tomllib) and cannot even
# be loaded as a file there (tools/preflight.py exits at import), so an older
# interpreter is a prerequisite failure, not a quieter run. Newest first, as
# scripts/check_script_tests.sh selects.
PYTHON_BIN=""
for candidate in python3.14 python3.13 python3.12 python3.11 python3 python; do
  if command -v "$candidate" >/dev/null 2>&1 \
     && "$candidate" -c 'import sys; sys.exit(0 if sys.version_info >= (3, 11) else 1)' 2>/dev/null; then
    PYTHON_BIN="$candidate"
    break
  fi
done
if [ -z "$PYTHON_BIN" ]; then
  echo "FAIL: no Python >= 3.11 on PATH (tried python3.14 python3.13 python3.12 python3.11 python3 python)." >&2
  echo "      scripts/tests/recreate_bootstrap_test.py needs tomllib; under an older interpreter it" >&2
  echo "      skips classes or does not load. Install one and push again." >&2
  refuse
fi
for test in "${TESTS[@]}"; do
  if [ ! -f "$test" ]; then
    echo "FAIL: $test is missing — a test this lane exists to run. Update TESTS and SCOPE" >&2
    echo "      together if it moved." >&2
    refuse
  fi
done
echo "interpreter: $PYTHON_BIN ($("$PYTHON_BIN" --version 2>&1))"

LOG_DIR="$(mktemp -d -t trust-bootstrap-script-tests.XXXXXX)" || {
  echo "FAIL: cannot create a scratch directory for the test logs" >&2
  refuse
}
trap 'rm -rf "${LOG_DIR:?}"' EXIT

# TRUST_PUSHED_REFS and TRUST_PUSH_REMOTE are the hook's words to its lanes.
# The tests are not readers of the push, and `TRUST_` is a prefix the
# recreator's native-authority capture refuses as ambient build authority, so
# a test that runs that capture on the real environment would judge the hook's
# variables instead of the script. Everything else is the caller's environment.
# -B: no bytecode written into the tree. </dev/null: a test must not read the
# hook's stdin.
failed=""
summary=""
lane_started=$SECONDS
for test in "${TESTS[@]}"; do
  log="$LOG_DIR/$(basename "$test").log"
  case "$test" in
    *.py) runner=("$PYTHON_BIN" -B "$test") ;;
    *)    runner=(bash "$test") ;;
  esac
  echo "=== $test ==="
  started=$SECONDS
  env -u TRUST_PUSHED_REFS -u TRUST_PUSH_REMOTE PYTHON_BIN="$PYTHON_BIN" \
    "${runner[@]}" </dev/null >"$log" 2>&1
  rc=$?
  seconds=$((SECONDS - started))
  # What each file reports when it ran: unittest's `Ran N tests`, the promote
  # test's closing count. Exit 0 without it is a run that tested nothing.
  case "$test" in
    *.py)
      ran="$(sed -nE 's/^Ran ([0-9]+) tests? in .*/\1/p' "$log" | tail -1)"
      skipped="$(sed -nE 's/^OK \(.*skipped=([0-9]+).*\)$/\1/p' "$log" | tail -1)"
      what="${ran:-0} tests, ${skipped:-0} skipped"
      ;;
    *)
      ran="$(sed -nE 's/^Promotion toolchain tests: ([0-9]+) cases passed.*/\1/p' "$log" | tail -1)"
      what="${ran:-0} cases"
      ;;
  esac
  if [ "$rc" -ne 0 ]; then
    cat "$log"
    echo "--- $test: FAIL (exit $rc, ${seconds} s)"
    failed+=" $test(exit=$rc)"
  elif [ -z "$ran" ] || [ "$ran" -eq 0 ]; then
    cat "$log"
    echo "--- $test: FAIL (exit 0 without reporting a single test: an empty run is not a pass)"
    failed+=" $test(ran-nothing)"
  else
    echo "--- $test: PASS ($what, ${seconds} s)"
    summary+="${summary:+; }$(basename "$test") $what in ${seconds} s"
  fi
done
total=$((SECONDS - lane_started))

not_seen "NOT SEEN:"
if [ -n "$failed" ]; then
  echo "FAIL: bootstrap-script tests red:$failed (${total} s)" >&2
  exit 1
fi
echo "bootstrap-script tests: PASS ($summary; ${total} s)"
exit 0
