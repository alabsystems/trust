#!/usr/bin/env bash
# A MEASUREMENT THAT DOES NOT NAME ITS TREE IS NOT A MEASUREMENT.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# ===========================================================================
# WHY THIS EXISTS
# ===========================================================================
# 2026-08-19 22:45:39, a lane committed wave-SG. 22:47:17 it edited
# `crates/trust-thir-lower/src/lib.rs` and never `git add`ed the edit. 22:47-50
# it ran the crate suite against that edit and got **599 passed, 0 failed** —
# a real run of a real tree. 23:00 it amended; the committed blob was still the
# pre-edit one. 23:25 it pushed `8e214e90d5`, whose body quotes the 599.
# `8e214e90d5` is RED at exactly one test. A confirmed-miscompile-class gate was
# reverted on the strength of that, silently, and the class sat ungated 2h10m.
# reports/revert-silence-rca-2026-08-20.md, commit a84866de8d.
#
# The number was NOT fabricated. The commit message described the WORKING TREE
# rather than the COMMIT. Nothing could tell the two apart, because the
# measurement never said which tree it was of.
#
# The RCA specified the fix and called it "a lane-runner convention, not
# something a pre-push hook can enforce". THAT PART IS WRONG, and this file is
# the disagreement. A convention cannot be enforced. An ASSERTION can — because
# an assertion about a blob is checkable against the commit that carries it.
#
# ===========================================================================
# THE TWO RULES
# ===========================================================================
# R1 — A STAMP THAT LIES IS A REFUSED PUSH.  [universal; no epoch, no waiver]
#
#   A commit body may carry trailers of the form
#
#       Measured-on: <repo-relative path>@<40-hex blob>
#
#   emitted ready-to-paste by `scripts/lib/measure_stamp.sh`. Every one of them
#   is resolved against THAT COMMIT'S OWN TREE (`git rev-parse <sha>:<path>`)
#   and must match. It is the whole mechanism: the incident's honest stamp would
#   have said `d08476acf3`, the commit carried `0a2fd94a8d`, and this rule turns
#   that disagreement into a refusal instead of a footnote nobody can see.
#
#   R1 has NO exemption list and NO epoch, and it needs none: it is vacuous on
#   every commit that carries no trailer, so it cannot retroactively condemn
#   history. It only ever judges a claim someone chose to make.
#   In pre-push mode the subject is the commits introduced to the actual
#   destination, for both rules. Published ancestry is outside that subject;
#   --history and explicit ranges still report every incorrect historical stamp.
#
# R2 — A SOUNDNESS-GATE COMMIT THAT QUOTES A TEST COUNT MUST STAMP.
#      [epoch-gated at EPOCH below]
#
#   A commit whose body quotes a test-count claim ("599 passed", "0 failed",
#   "51/51 GREEN", "test result: ok") AND whose diff touches a soundness-gate
#   path must carry at least one `Measured-on:` trailer.
#
#   "Touches" is judged per parent and without rename pairing: a move touches
#   the path it leaves, and a merge touches every path in which its tree differs
#   from ANY parent, whether or not the merge had conflicts.
#
#   R2 is deliberately NARROWER than "every commit quoting a number". Measured
#   over the 569 commits in the seven days to 2026-08-20: 101 quote a test-count
#   claim (17.8%), and 37 of those touch a soundness-gate path (6.5% of all
#   commits, ~5/day). Requiring a stamp of all 101 would have put a new mandatory
#   trailer in front of one push in six — and the fastest way to lose a gate is
#   to make it expensive enough that `--no-verify` becomes a habit. 6.5%, aimed
#   at exactly the class where a wrong number reverts a miscompile gate, is a
#   rule that gets obeyed. The narrowing is stated here rather than hidden so
#   that what R2 does NOT cover is on the record: see WHAT REMAINS CONVENTIONAL.
#
#   On a push with a known destination, R2 applies to newly published commits.
#   A commit already reachable from that destination's advertised refs does not
#   acquire a retroactive trailer requirement when main is merged into a topic.
#   Local remote-tracking refs are not evidence of publication. R1 still checks
#   every selected stamp, including already-published commits; explicit ranges
#   and --history retain both rules over their complete selected history.
#
# ===========================================================================
# WHAT REMAINS CONVENTIONAL — stated, not glossed
# ===========================================================================
#   * R2 does not reach a claim-quoting commit outside the soundness-gate paths.
#     Such a commit may still quote an unstamped number. R1 still binds it if it
#     stamps at all.
#   * Neither rule can force the stamp to be of the run that produced the number.
#     A lane that pastes a trailer for a blob it never measured is FABRICATING,
#     not mistaking — a different act from the one the RCA found, and one no
#     mechanical check on a commit can distinguish. What is closed is the honest
#     mistake, which is the one that actually happened.
#   * The `--log` mode binds only logs that are actually fed to it. Runners that
#     never call it are unbound by it; that is why R1/R2 sit at the COMMIT, the
#     one artifact every lane must produce and every push must present.
#   * `git push --no-verify` skips the hook, as it skips every hook here. It
#     leaves a reflog entry rather than a habit.
#
# ===========================================================================
# AT COMMIT TIME TOO (2026-10-24, docs/DECISION_QUEUE.md PUSH-PATH-COMMIT-MSG)
# ===========================================================================
# Until then both rules met a commit only at push, minutes into the hook and
# after the commit existed, and the remedy was to reword commits already made
# (R101's rewording). `--commit-msg FILE`, run by scripts/hooks/commit-msg,
# judges the commit BEING MADE with exactly the code above: it writes the index
# the commit is made from as a tree (`git write-tree`; git hands the hook that
# index in GIT_INDEX_FILE for `commit -a` and `commit <paths>` too), makes a
# probe commit object of that tree, HEAD and every MERGE_HEAD parent, and the
# message as git will store it (git's default cleanup: an edited message loses
# its comment lines and everything from `commit -v`'s scissors line, a message
# given with -m or -F keeps both), and judges that one commit as a range. No ref is written; the probe is an unreachable object gc removes. So
# R1 refuses the wave-SG stamp of an edit that was never `git add`ed before a
# commit exists, and R2 sees a merge exactly as the sweep does (`-m`, every
# parent). What it cannot see: a commit-msg hook is not told about `--amend`,
# whose commit takes HEAD's parents, so an amend is judged against HEAD (the
# paths the amend itself changes); what the amended commit already touched is
# judged at push, as before. `git commit --no-verify` skips the hook, and the
# push still judges the commit.
#
# ===========================================================================
# USAGE
# ===========================================================================
#   scripts/check_measurement_provenance.sh --log FILE...       # the log gate
#   scripts/check_measurement_provenance.sh --pre-push [--remote DESTINATION]
#                                                            # git's stdin
#   scripts/check_measurement_provenance.sh --push-context      # --pre-push via $TRUST_PUSHED_REFS
#   scripts/check_measurement_provenance.sh --history [<since>] # second net
#   scripts/check_measurement_provenance.sh <rev-range>...
#   scripts/check_measurement_provenance.sh --audit-runners <dir>
#                                                # adoption counter over the
#                                                # lane runners (report, not gate)
#   scripts/check_measurement_provenance.sh --commit-msg FILE   # the commit being made
#                                                # (scripts/hooks/commit-msg)
#   scripts/check_measurement_provenance.sh --selftest          # mutation proof
#
# Exit codes:
#   0  every examined measurement names a tree, and every named tree is real
#   1  a stamp disagrees with its commit, or a stamp that R2 requires is absent,
#      or (--log) a log carries no stamp / a stamp showing dirt
#   2  the checker could not do its job (fails closed; never reports green)
set -uo pipefail

# THE EPOCH. R2 judges commits whose COMMITTER date is at or after this. It is a
# constant in a soundness gate, not a knob: moving it FORWARD exempts new
# commits, so it shows up as a diff to this file in review. Committer date, not
# author date, because these lanes land through `git commit-tree` — the author
# date can be arbitrarily old, the committer date is when it was made.
EPOCH="2026-08-20"

LEDGER_REL="scripts/measurement-provenance-grandfathered.txt"

# The same path set scripts/check_revert_rationale.sh calls a soundness-gate
# revert. Kept verbatim rather than shared, for the same reason that script
# keeps it inline: one gate must not go green because another gate's constant
# moved.
SOUNDNESS_PATH_RE='^(crates/trust-thir-lower/|crates/trust-ir|compiler/rustc_mir_transform/src/trust_|scripts/check_|scripts/hooks|src/tools/trust|tests/trust-comprehensive/divergences.toml)'

die() { printf 'check_measurement_provenance: %s\n' "$*" >&2; exit 2; }

# ===========================================================================
# --log : the log gate
# ===========================================================================
# Rejects a log with no stamp, and a log whose stamp shows dirt in the measured
# paths. This is the mode a runner calls on its own output, and the mode a
# record-writing script calls before it believes a log.
check_logs() {
  local rc=0 n=0 f
  for f in "$@"; do
    n=$((n + 1))
    if [ ! -f "$f" ]; then
      echo "  x $f — no such log. A measurement that produced no file produced no evidence."
      rc=1
      continue
    fi
    if ! grep -q '^=== MEASURE-STAMP v1$' "$f"; then
      if grep -q '^=== MEASURE-STAMP v1 UNSTAMPABLE' "$f"; then
        echo "  x $f — the stamp says UNSTAMPABLE: the runner could not name a tree."
        sed -n '/^=== MEASURE-STAMP v1 UNSTAMPABLE/,/^=== END MEASURE-STAMP/p' "$f" | sed 's/^/        /'
      else
        echo "  x $f — NO PROVENANCE STAMP. This log does not say which tree it measured,"
        echo "        so it is not a claim about any tree. Add one line to the runner:"
        echo "            bash \"\$TRUST_ROOT/scripts/lib/measure_stamp.sh\" <path under test>"
      fi
      rc=1
      continue
    fi
    # A stamp with no declared path measures nothing in particular.
    if grep -q '^--- file     NONE-DECLARED$' "$f"; then
      echo "  x $f — the stamp declares NO measured path. Pass the files under test."
      rc=1
      continue
    fi
    local dirty
    dirty="$(grep -c ' DIRTY$' "$f" 2>/dev/null || true)"
    dirty="${dirty//[^0-9]/}"
    if [ -n "$dirty" ] && [ "$dirty" -gt 0 ]; then
      echo "  x $f — measured $dirty path(s) that DIFFER FROM HEAD:"
      grep ' DIRTY$' "$f" | sed 's/^/        /'
      echo "        This is the wave-SG shape exactly: a real run of a tree that was"
      echo "        never committed. Commit the edit and re-measure, or publish the"
      echo "        result as a WORKING-TREE probe and never as a verdict on a sha."
      rc=1
      continue
    fi
    echo "  ok $f"
  done
  if [ "$n" -eq 0 ]; then
    echo "check_measurement_provenance --log: no log named — an empty scan is not a pass" >&2
    return 2
  fi
  return "$rc"
}

# ===========================================================================
# --audit-runners : the ADOPTION COUNTER
# ===========================================================================
# The RCA measured "83 measurement scripts, 41 record a blob or worktree dirt,
# 42 do not" once, by hand, and that number cannot be re-derived — which is the
# same defect in miniature. This is the classifier, so the split is a live
# reading rather than a remembered one, and so the retrofit has a counter that
# goes down.
#
# A RUNNER is a shell script at depth <= 2 under the scan root (the lane
# runners; not the repo's own scripts, and not anything inside a nested git
# worktree or clone) that EXECUTES a measurement: cargo test/build, x.py, a
# compiled probe, or a whole-crate dump.
#
# It is STAMPED when it calls scripts/lib/measure_stamp.sh, or already does by
# hand what the helper does: `git hash-object` of a measured path, or
# `git status --porcelain`.
#
# This is a REPORT, not a gate: it exits 0 whatever it finds. The lane
# scratchpads are untracked working directories that several lanes are writing
# to concurrently, so failing a push on their contents would be a gate on
# somebody else's uncommitted work. What is GATED is the commit (R1/R2); this
# only measures how far adoption has got.
#
# The scan root is REQUIRED. It used to default to `scratchpad`, which is now
# gitignored local state (its tracked contents were deleted in 6ba5324748), so
# whether the no-argument call scanned anything depended on what happened to be
# on disk; naming the root makes the caller say which lane directory the count
# is about.
audit_runners() {
  local root="${1:-}"
  [ -n "$root" ] || { echo "audit-runners: name the directory to scan (there is no default)" >&2; return 2; }
  [ -d "$root" ] || { echo "audit-runners: no such directory: $root" >&2; return 2; }
  local wt_roots
  wt_roots="$(git worktree list --porcelain 2>/dev/null | sed -n 's/^worktree //p')"

  local total=0 stamped=0 unstamped=0
  local -a UNSTAMPED=() STAMPED_L=()
  local f
  while IFS= read -r f; do
    [ -f "$f" ] || continue
    # Skip anything inside a nested worktree or clone: those are checkouts of
    # this repository, not lane runners.
    local abs skip=0 w
    abs="$(cd "$(dirname "$f")" 2>/dev/null && pwd)/$(basename "$f")" || continue
    while IFS= read -r w; do
      [ -n "$w" ] || continue
      case "$abs" in "$w"/*) [ "$w" = "$PWD" ] || skip=1 ;; esac
    done <<<"$wt_roots"
    [ "$skip" -eq 0 ] || continue
    case "$f" in */.git/*) continue ;; esac
    # Does it MEASURE?
    grep -qE 'cargo[^\n]*(test|build|rustc)|x\.py|test result|--lib|\.o[[:space:]]|objdump|nm -|MUTATION|scorecard' "$f" 2>/dev/null || continue
    total=$((total + 1))
    if grep -qE 'measure_stamp|hash-object|status --porcelain' "$f" 2>/dev/null; then
      stamped=$((stamped + 1)); STAMPED_L+=("$f")
    else
      unstamped=$((unstamped + 1)); UNSTAMPED+=("$f")
    fi
  done < <(find "$root" -maxdepth 2 -name '*.sh' -type f 2>/dev/null | sort)

  echo "=== runner provenance adoption (root: $root) ==="
  echo "  measurement runners : $total"
  echo "  STAMPED             : $stamped"
  echo "  unstamped           : $unstamped"
  if [ "$unstamped" -gt 0 ]; then
    echo
    echo "  runners that report a measurement without naming the tree:"
    local u
    for u in "${UNSTAMPED[@]}"; do echo "    - $u"; done
    echo
    echo "  Retrofit is one line inside the block that writes the log:"
    echo "      bash \"\$TRUST_ROOT/scripts/lib/measure_stamp.sh\" <the files under test>"
  fi
  return 0
}

# ===========================================================================
# commit modes
# ===========================================================================

# --push-context is --pre-push with the ref lines taken from TRUST_PUSHED_REFS.
# A manifest command string is fixed and receives no stdin, so scripts/hooks/pre-push
# exports the refs instead and the SAME row text runs in both runners. UNSET means
# no push is in flight and the subject WIDENS to --history; it never narrows to
# nothing. Unset, not empty: an empty-but-set var is a real push with no updated
# refs, which must stay the green it is today. SUBJECT: says which reading it took,
# so a `push` run outside a hook cannot be mistaken for a rehearsal of one.
if [ "${1:-}" = "--push-context" ]; then
  shift
  self="$0"; case "$self" in /*) ;; *) self="$PWD/$self" ;; esac
  if [ -n "${TRUST_PUSHED_REFS+x}" ]; then
    refcount="$(printf '%s' "$TRUST_PUSHED_REFS" | grep -c . || true)"
    echo "SUBJECT: push ($refcount ref update(s))"
    if [ -n "${TRUST_PUSH_REMOTE:-}" ]; then
      exec bash "$self" --pre-push --remote "$TRUST_PUSH_REMOTE" "$@" <<< "$TRUST_PUSHED_REFS"
    fi
    exec bash "$self" --pre-push "$@" <<< "$TRUST_PUSHED_REFS"
  fi
  echo "SUBJECT: history (no push in flight; TRUST_PUSHED_REFS unset)"
  exec bash "$self" --history "$@"
fi

REPO_ROOT="$(git rev-parse --show-toplevel 2>/dev/null)" || true
# The destination's advertised refs are read by ONE helper shared with the
# revert-rationale and caller-skew lanes; resolved beside THIS file, before the
# cd below.
DESTINATION_LIB="$(cd -P "$(dirname "${BASH_SOURCE[0]}")" 2>/dev/null && pwd -P)/lib/push_destination.sh"
# This file, by an absolute path (--commit-msg re-enters it after the cd below).
SELF_PATH="$(cd -P "$(dirname "${BASH_SOURCE[0]}")" 2>/dev/null && pwd -P)/$(basename "${BASH_SOURCE[0]}")"

# ---------------------------------------------------------------------------
# THE ANCHORED WAIVER READING (push context). Without push context
# (TRUST_PUSHED_REFS unset) the grandfather ledger is the checkout's file, as it
# always was. With it set, the checkout is not the push: an UNCOMMITTED row
# waived the pushed unstamped claim, and a naive "read the pushed tip" would let
# a row committed IN THE SAME PUSH (a swap keeps the count at 5) waive it — both
# reproduced in docs/issues/2026-09-28-push-lanes-judge-the-checkout-not-the-push.md
# (case R). So the waiver set is read only from git objects, as
#
#     rows(anchor) ∩ rows(pushed tip)       for every non-deletion ref line,
#
# intersected across the lines, where the ANCHOR is a tree this push cannot
# author:
#   * an update: the destination's current tip (the line's remote sha);
#   * a new ref, or an update whose old tip this store does not hold: the
#     merge-base of the pushed tip with the main the destination advertises;
#   * neither: NO anchor, and the waiver set is EMPTY. An empty set only ever
#     judges more commits, never fewer.
# The worktree ledger is never read in this reading. A malformed ref line is
# exit 2, not skipped. Kept verbatim beside scripts/check_revert_rationale.sh's
# copy rather than shared, for the reason SOUNDNESS_PATH_RE is.
# ---------------------------------------------------------------------------
ANCHORED=0
[ -n "${TRUST_PUSHED_REFS+x}" ] && ANCHORED=1
ANCHOR_LINES=()
DEST_ADVERTISED=""
DEST_LOADED=0
WAIVER_WORK=""

anchored_line_ok() {  # <local-ref> <local-sha> <remote-ref> <remote-sha>
  [ -n "$1" ] && [ -n "$3" ] || return 1
  [[ "$2" =~ ^([0-9a-f]{40}|[0-9a-f]{64})$ ]] || return 1
  [[ "$4" =~ ^([0-9a-f]{40}|[0-9a-f]{64})$ ]] || return 1
}

# Sets ANCHOR (empty when there is none) and ANCHOR_WHY. Never a subshell, so
# `die` ends the checker.
resolve_anchor() {  # <local-sha> <remote-sha>
  local local_sha="$1" remote_sha="$2" dest_main mb rc
  ANCHOR=""; ANCHOR_WHY=""
  if [ -n "${remote_sha//0/}" ] \
     && ANCHOR="$(git --no-replace-objects rev-parse --verify --quiet "${remote_sha}^{commit}" 2>/dev/null)"; then
    ANCHOR_WHY="the destination's tip"
    return 0
  fi
  ANCHOR=""
  if [ -z "$PUSH_REMOTE" ]; then
    ANCHOR_WHY="NO ANCHOR: no destination tip here and no destination named"
    return 0
  fi
  if [ "$DEST_LOADED" -eq 0 ]; then
    # shellcheck source=lib/push_destination.sh
    { [ -f "$DESTINATION_LIB" ] && . "$DESTINATION_LIB"; } \
      || die "$DESTINATION_LIB is missing; refusing to guess the waiver anchor"
    DEST_ADVERTISED="$(trust_push_destination_refs "$PUSH_REMOTE")" \
      || die "cannot read the push destination's advertised refs; refusing to guess the waiver anchor"
    DEST_LOADED=1
  fi
  dest_main="$(printf '%s\n' "$DEST_ADVERTISED" | awk '$2 == "refs/heads/main" { print $1; exit }')"
  if [ -z "$dest_main" ]; then
    ANCHOR_WHY="NO ANCHOR: the destination advertises no main this store holds"
    return 0
  fi
  mb="$(git --no-replace-objects merge-base "$local_sha" "$dest_main" 2>/dev/null)"; rc=$?
  if [ "$rc" -eq 0 ] && [ -n "$mb" ]; then
    ANCHOR="$mb"
    ANCHOR_WHY="merge-base with the destination's main"
  elif [ "$rc" -eq 1 ]; then
    ANCHOR_WHY="NO ANCHOR: no history in common with the destination's main"
  else
    die "cannot compute the merge-base of $local_sha and the destination's main"
  fi
}

# The full-sha rows of the ledger in one commit's tree, sorted: the same
# reading the sweep gives a file (comment stripped, whitespace removed, a row is
# exactly 40 hex). No ledger at that commit is no rows; an unreadable tree is
# exit 2.
ledger_rows() {  # <commit>
  local entry _mode type oid
  entry="$(git --no-replace-objects ls-tree "$1" -- "$LEDGER_REL" 2>/dev/null)" \
    || die "cannot read the tree of $1 — refusing to guess its grandfather ledger"
  [ -n "$entry" ] || return 0
  read -r _mode type oid _ <<< "$entry"
  [ "$type" = blob ] || return 0
  { git --no-replace-objects cat-file blob "$oid" 2>/dev/null \
      | awk '{ sub(/#.*/, ""); gsub(/[ \t\r\n]/, ""); if ($0 ~ /^[0-9a-f]{40}$/) print }' \
      | LC_ALL=C sort -u; } \
    || die "cannot read $LEDGER_REL at $1 — refusing to guess its grandfather ledger"
}

# Writes the anchored waiver set to <file> and reports where it came from.
anchored_waivers() {  # <file>
  local out="$1" work line local_sha remote_sha n_a n_t first=1 none=0
  work="$(mktemp -d "${TMPDIR:-/tmp}/provenance-waivers.XXXXXX")" || die "cannot create a scratch directory"
  WAIVER_WORK="$work"
  : >"$out"
  local notes=()
  for line in "${ANCHOR_LINES[@]}"; do
    local_sha="${line% *}"; remote_sha="${line#* }"
    resolve_anchor "$local_sha" "$remote_sha"
    ledger_rows "$local_sha" >"$work/tip" || exit 2
    n_t="$(grep -c . "$work/tip" || true)"
    if [ -z "$ANCHOR" ]; then
      none=1
      notes+=("  ${local_sha:0:12}: ${ANCHOR_WHY}; ${n_t} row(s) at the pushed tip waive nothing")
      continue
    fi
    ledger_rows "$ANCHOR" >"$work/anchor" || exit 2
    n_a="$(grep -c . "$work/anchor" || true)"
    LC_ALL=C comm -12 "$work/anchor" "$work/tip" >"$work/line"
    if [ "$first" -eq 1 ]; then
      cp "$work/line" "$out"
      first=0
    else
      LC_ALL=C comm -12 "$out" "$work/line" >"$work/meet"
      cp "$work/meet" "$out"
    fi
    notes+=("  ${local_sha:0:12}: anchor ${ANCHOR:0:12} (${ANCHOR_WHY}); ${n_a} row(s) there, ${n_t} at the pushed tip")
  done
  [ "$none" -eq 0 ] || : >"$out"
  echo "WAIVERS: $(grep -c . "$out" || true) grandfather row(s) apply — rows(anchor) ∩ rows(pushed tip), never the checkout's ledger"
  printf '%s\n' "${notes[@]}"
}

REVS_ARGS=()
MODE=""
PUSH_REMOTE=""
case "${1:---help}" in
  --waiver-anchors)
    # INTERNAL, for scripts/tests/: the anchor each pushed ref line resolves to,
    # one `ANCHOR <local-sha> <anchor-sha|NONE> <why>` line per non-deletion
    # line, so the "may only shrink" ratchet in the tests uses THIS rule rather
    # than a copy of it.
    MODE=waiver-anchors
    shift
    if [ "$#" -ne 0 ]; then
      [ "$#" -eq 2 ] && [ "$1" = "--remote" ] && [ -n "$2" ] \
        || die "--waiver-anchors accepts only --remote DESTINATION"
      PUSH_REMOTE="$2"
    fi
    ;;
  --commit-msg)
    # The commit being made; see AT COMMIT TIME TOO above.
    MODE=commit-msg
    shift
    [ "$#" -eq 1 ] && [ -n "$1" ] || die "--commit-msg takes exactly the message file git hands its commit-msg hook"
    COMMIT_MSG_FILE="$1"
    case "$COMMIT_MSG_FILE" in /*) ;; *) COMMIT_MSG_FILE="$PWD/$COMMIT_MSG_FILE" ;; esac
    ;;
  --log)
    shift
    echo "=== measurement provenance (--log; $# log(s)) ==="
    check_logs "$@"
    exit $?
    ;;
  --audit-runners)
    shift
    audit_runners "${1:-}"
    exit $?
    ;;
  --selftest)
    MODE=selftest
    ;;
  --selftest-run)
    # Internal re-entry for the selftest, which builds its own scratch
    # repository. Not a user-facing override: there is no way to point the
    # normal modes at a different repo or a different ledger.
    shift
    MODE=range
    REVS_ARGS=("$@")
    ;;
  --pre-push)
    MODE=pre-push
    shift
    if [ "$#" -ne 0 ]; then
      [ "$#" -eq 2 ] && [ "$1" = "--remote" ] && [ -n "$2" ] \
        || die "--pre-push accepts only --remote DESTINATION"
      PUSH_REMOTE="$2"
    fi
    # Read every line git feeds us so it never sees EPIPE, and keep them: the
    # subject of this gate is exactly the commits this push would introduce.
    # Anchored, an unterminated last line is judged too, and a line that is not
    # four fields with full shas is a refusal: a line skipped is a ref unjudged.
    while read -r _local_ref local_sha _remote_ref remote_sha \
          || { [ "$ANCHORED" -eq 1 ] && [ -n "${_local_ref:-}" ]; }; do
      if [ "$ANCHORED" -eq 1 ] && [ -n "${_local_ref:-}" ]; then
        anchored_line_ok "$_local_ref" "${local_sha:-}" "${_remote_ref:-}" "${remote_sha:-}" \
          || die "malformed pushed-ref line '${_local_ref} ${local_sha:-} ${_remote_ref:-} ${remote_sha:-}'"
      fi
      [ -n "${local_sha:-}" ] || continue
      case "$local_sha" in
        *[!0]*) ;;
        *) continue ;;   # all-zero local sha = branch deletion; nothing to judge
      esac
      ANCHOR_LINES+=("$local_sha ${remote_sha:-0}")
      if [ -z "${remote_sha:-}" ] || [ -z "${remote_sha//0/}" ]; then
        # A persistent --not also negates subsequent ref updates. Keep every
        # pushed tip positive; local tracking refs cannot exempt new commits.
        REVS_ARGS+=("$local_sha")
      else
        REVS_ARGS+=("${remote_sha}..${local_sha}")
      fi
    done
    if [ "${#REVS_ARGS[@]}" -eq 0 ]; then
      echo "MEASUREMENT PROVENANCE: nothing to judge (no updated refs on stdin)."
      exit 0
    fi
    ;;
  --history)
    # The SECOND net. A hook binds only the machines that installed it, and the
    # commit this gate exists for came from a machine whose lane was elsewhere.
    MODE=history
    shift
    if [ -n "${1:-}" ]; then REVS_ARGS=("${1}..HEAD"); else REVS_ARGS=("--since=90.days" "--all"); fi
    ;;
  -h|--help)
    sed -n '/^# USAGE/,/^#   2  the checker/p' "$0" | sed 's/^# \{0,1\}//'
    exit 0
    ;;
  *)
    MODE=range
    REVS_ARGS=("$@")
    ;;
esac

[ -n "$REPO_ROOT" ] || die "not inside a git worktree"
cd "$REPO_ROOT" || die "cannot enter $REPO_ROOT"

if [ "$MODE" = commit-msg ]; then
  # AT COMMIT TIME TOO (above): the commit being made, as one probe commit.
  [ -f "$COMMIT_MSG_FILE" ] || die "--commit-msg: no such message file: $COMMIT_MSG_FILE"
  [ -f "$SELF_PATH" ] || die "cannot locate this checker to judge the probe commit"
  # The message as git will store it. git's cleanup depends on whether the
  # message was edited: it hands a hook GIT_EDITOR=: when no editor ran, and
  # then (the default `whitespace` cleanup) keeps comment lines. When an editor
  # ran, the default `strip` drops them and everything from the scissors line
  # `git commit -v` writes. commit.cleanup overrides the default; a
  # --cleanup on the command line is not visible here.
  comment_char="$(git config --get core.commentChar 2>/dev/null || true)"
  case "$comment_char" in ?) ;; *) comment_char='#' ;; esac
  editing=1; [ "${GIT_EDITOR:-}" != ":" ] || editing=0
  case "$(git config --get commit.cleanup 2>/dev/null || true)" in
    strip) cut_scissors="$editing"; strip_comments=1 ;;
    scissors) cut_scissors="$editing"; strip_comments=0 ;;
    whitespace|verbatim) cut_scissors=0; strip_comments=0 ;;
    *) cut_scissors="$editing"; strip_comments="$editing" ;;
  esac
  CLEANED_MSG="$(mktemp "${TMPDIR:-/tmp}/provenance-commit-msg.XXXXXX")" || die "cannot create a scratch file"
  trap 'rm -f "$CLEANED_MSG"' EXIT
  awk -v cc="$comment_char" -v cut="$cut_scissors" -v strip="$strip_comments" '
    cut == 1 && $0 == cc " ------------------------ >8 ------------------------" { exit }
    strip == 1 && substr($0, 1, 1) == cc { next }
    { print }' "$COMMIT_MSG_FILE" >"$CLEANED_MSG" || die "cannot read $COMMIT_MSG_FILE"
  probe_tree="$(git --no-replace-objects write-tree 2>/dev/null)" \
    || die "cannot write the index as a tree (git write-tree) — refusing to judge a commit I cannot see"
  probe_parents=(); probe_not=()
  if parent="$(git --no-replace-objects rev-parse --verify --quiet 'HEAD^{commit}' 2>/dev/null)"; then
    probe_parents+=(-p "$parent"); probe_not+=("^$parent")
  fi
  merge_head_file="$(git rev-parse --git-path MERGE_HEAD 2>/dev/null)" || die "cannot locate MERGE_HEAD"
  if [ -f "$merge_head_file" ]; then
    while read -r merge_parent _; do
      [ -n "${merge_parent:-}" ] || continue
      parent="$(git --no-replace-objects rev-parse --verify --quiet "${merge_parent}^{commit}" 2>/dev/null)" \
        || die "MERGE_HEAD names ${merge_parent}, which is not a commit here"
      probe_parents+=(-p "$parent"); probe_not+=("^$parent")
    done <"$merge_head_file"
  fi
  # Identity and signing do not reach either rule; fixed so that neither can
  # stop the probe.
  probe="$(GIT_AUTHOR_NAME=commit-msg-probe GIT_AUTHOR_EMAIL=probe@commit-msg.invalid \
           GIT_COMMITTER_NAME=commit-msg-probe GIT_COMMITTER_EMAIL=probe@commit-msg.invalid \
           git --no-replace-objects -c commit.gpgSign=false commit-tree "$probe_tree" \
             ${probe_parents[@]+"${probe_parents[@]}"} -F "$CLEANED_MSG" 2>/dev/null)" \
    || die "cannot make the probe commit (git commit-tree) — refusing to judge a commit I cannot see"
  out="$(env -u TRUST_PUSHED_REFS -u TRUST_PUSH_REMOTE bash "$SELF_PATH" "$probe" ${probe_not[@]+"${probe_not[@]}"} 2>&1)"
  rc=$?
  [ "$rc" -ne 0 ] || exit 0
  echo "commit-msg: measurement provenance judged the commit being made (as probe object ${probe:0:12}, on no ref):"
  printf '%s\n' "$out" | sed "s/${probe}/<the commit being made>/g"
  if [ "$rc" -eq 1 ]; then
    echo
    echo "Nothing was committed. Your message is kept in .git/COMMIT_EDITMSG; after adding"
    echo "the stamp, commit again with:  git commit -e -F \"\$(git rev-parse --git-path COMMIT_EDITMSG)\""
  fi
  exit "$rc"
fi

if [ "$MODE" = waiver-anchors ]; then
  while read -r _local_ref local_sha _remote_ref remote_sha || [ -n "${_local_ref:-}" ]; do
    [ -n "${_local_ref:-}" ] || continue
    anchored_line_ok "$_local_ref" "${local_sha:-}" "${_remote_ref:-}" "${remote_sha:-}" \
      || die "malformed pushed-ref line '${_local_ref} ${local_sha:-} ${_remote_ref:-} ${remote_sha:-}'"
    [ -n "${local_sha//0/}" ] || continue
    resolve_anchor "$local_sha" "$remote_sha"
    printf 'ANCHOR %s %s %s\n' "$local_sha" "${ANCHOR:-NONE}" "$ANCHOR_WHY"
  done
  exit 0
fi

if [ "$MODE" = pre-push ] && [ -n "$PUSH_REMOTE" ]; then
  # Select the subject once, before either rule runs. Applying destination
  # ancestry only to missing R2 stamps accidentally audited all historical R1
  # stamps when creating a branch, including commits this push cannot change.
  # Explicit negative revisions do not negate subsequent pushed tips.
  # What counts as advertised (peeled tags; an unavailable object supplies no
  # ancestry evidence and is never replaced by a local tracking ref or fetched;
  # a malformed advertisement is refused) is scripts/lib/push_destination.sh's
  # contract, shared with the revert-rationale and caller-skew lanes.
  load_destination() {
    local destination commit _ref
    # shellcheck source=lib/push_destination.sh
    { [ -f "$DESTINATION_LIB" ] && . "$DESTINATION_LIB"; } \
      || die "$DESTINATION_LIB is missing; refusing to guess published history"
    destination="$(trust_push_destination_refs "$PUSH_REMOTE")" \
      || die "cannot read the push destination's advertised refs"
    DEST_ADVERTISED="$destination"; DEST_LOADED=1
    while read -r commit _ref; do
      [ -n "${commit:-}" ] || continue
      # Append only real exclusions. Expanding a separate empty array under
      # Bash 3.2's nounset fails instead of contributing zero revisions.
      REVS_ARGS+=("^$commit")
    done <<< "$destination"
  }
  load_destination
  echo "SUBJECT: commits introduced to the push destination; --history retains published-claim audits."
fi

# --------------------------------------------------------------------- sweep
run_sweep() {
  local ledger="$1"; shift
  local log
  log="$(git --no-replace-objects log --format='%H%x1f%cI%x1f%s%x1f%b%x1e' "$@" 2>/dev/null)" \
    || die "git log $* failed — refusing to report green on a range I cannot read"

  # ONE `git log` for the whole range: a `git log -1` per revision costs ~90s
  # over this repository's history, which is how a gate becomes something
  # people route around.
  printf '%s' "$log" | awk -v ledger="$ledger" -v epoch="$EPOCH" '
    BEGIN {
      # The ledger is read while RS is still a newline. Setting RS to the record
      # separator first swallows the file as one record and waives nothing —
      # the exact ordering bug scripts/tests/ caught in the revert gate.
      while ((getline row < ledger) > 0) {
        sub(/#.*/, "", row); gsub(/[ \t\r\n]/, "", row)
        if (row ~ /^[0-9a-f]{40}$/) waived[row] = 1
      }
      RS = "\036"; FS = "\037"
    }
    {
      sha = $1; sub(/^[\n\r]+/, "", sha)
      if (sha !~ /^[0-9a-f]{40}$/) next
      examined++
      cdate = substr($2, 1, 10)
      body = $4

      # ---- R1: every Measured-on: trailer is a claim to be checked ---------
      n = split(body, lines, "\n")
      stamped = 0
      for (i = 1; i <= n; i++) {
        line = lines[i]
        sub(/^[ \t\r]+/, "", line); sub(/[ \t\r]+$/, "", line)
        if (tolower(line) !~ /^measured-on:/) continue
        stamped++
        claim = substr(line, index(line, ":") + 1)
        gsub(/^[ \t]+|[ \t]+$/, "", claim)
        printf "TRAILER\037%s\037%s\n", sha, claim
      }
      if (stamped) stampedcommits++

      # ---- R2: claim + soundness path + post-epoch => a stamp is required --
      if (cdate < epoch) next
      if (sha in waived) { grandfathered++; next }
      if (stamped) next
      claimline = ""
      for (i = 1; i <= n; i++) {
        line = lines[i]
        # Match the shapes these lanes actually write. Anchored on a NUMBER so
        # that prose about "passing tests" is not a claim; a claim is a count.
        if (line ~ /[0-9]+[ \t]+passed/ ||
            line ~ /[0-9]+[ \t]+failed/ ||
            line ~ /[0-9]+[ \t]*\/[ \t]*[0-9]+[ \t]+(GREEN|green|passed|passing)/ ||
            line ~ /test result:[ \t]*(ok|FAILED)/ ||
            line ~ /[0-9]+[ \t]+tests?[ \t]+pass(ed|ing)/) {
          gsub(/^[ \t\r]+|[ \t\r]+$/, "", line)
          claimline = line
          break
        }
      }
      if (claimline == "") next
      printf "CLAIM\037%s\037%s\n", sha, claimline
    }
    END { printf "STATS\037%d\037%d\037%d\n", examined + 0, stampedcommits + 0, grandfathered + 0 }
  '
}

if [ "$MODE" = "selftest" ]; then
  :
else
  LEDGER="$REPO_ROOT/$LEDGER_REL"
  [ -f "$LEDGER" ] || LEDGER=/dev/null
  if [ "$MODE" = pre-push ] && [ "$ANCHORED" -eq 1 ]; then
    # Push context: the waiver set comes from git objects, never the checkout.
    # See THE ANCHORED WAIVER READING above.
    WAIVER_FILE="$(mktemp "${TMPDIR:-/tmp}/provenance-waiver-set.XXXXXX")" || die "cannot create a scratch file"
    trap 'rm -f "$WAIVER_FILE"; [ -z "$WAIVER_WORK" ] || rm -rf "$WAIVER_WORK"' EXIT
    anchored_waivers "$WAIVER_FILE"
    LEDGER="$WAIVER_FILE"
  fi
  SWEEP="$(run_sweep "$LEDGER" "${REVS_ARGS[@]}")" || exit 2

  EXAMINED=0; STAMPED=0; WAIVED=0
  R1_FAIL=(); R2_FAIL=(); TRAILERS=0
  statline="$(printf '%s\n' "$SWEEP" | grep '^STATS' | head -1)"
  if [ -n "$statline" ]; then
    EXAMINED="$(printf '%s' "$statline" | cut -d$'\037' -f2)"
    STAMPED="$(printf '%s' "$statline" | cut -d$'\037' -f3)"
    WAIVED="$(printf '%s' "$statline" | cut -d$'\037' -f4)"
  fi

  while IFS=$'\037' read -r kind sha rest; do
    [ -n "${kind:-}" ] || continue
    case "$kind" in
      TRAILER)
        TRAILERS=$((TRAILERS + 1))
        # `<path>@<blob>`; the path may itself contain `@`, so split at the LAST.
        blob="${rest##*@}"
        path="${rest%@*}"
        if [ -z "$path" ] || [ "$path" = "$rest" ]; then
          R1_FAIL+=("$sha
      malformed trailer: 'Measured-on: $rest'
      expected  Measured-on: <repo-relative path>@<40-hex blob>")
          continue
        fi
        case "$blob" in
          [0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f]) ;;
          ABSENT|unhashable)
            R1_FAIL+=("$sha
      Measured-on: $path@$blob
      the stamp itself records that the file could not be hashed. A measurement
      of a file the runner could not read is not a measurement of that file.")
            continue ;;
          *)
            R1_FAIL+=("$sha
      Measured-on: $path@$blob
      the blob is not a 40-hex object id. Paste the '--- trailer' lines that
      scripts/lib/measure_stamp.sh emits; do not retype them.")
            continue ;;
        esac
        actual="$(git --no-replace-objects rev-parse --verify --quiet "${sha}:${path}" 2>/dev/null || true)"
        if [ -z "$actual" ]; then
          R1_FAIL+=("$sha
      Measured-on: $path@$blob
      this commit's tree HAS NO SUCH PATH. The stamp names a file the commit
      does not carry, so the commit cannot be the thing that was measured.")
        elif [ "$actual" != "$blob" ]; then
          R1_FAIL+=("$sha
      Measured-on: $path@$blob
      but this commit carries  $path@$actual
      THE MEASUREMENT IS OF A DIFFERENT TREE. This is wave-SG exactly: a real
      run of a tree that was never committed, published as a verdict on a sha.
      Commit what you measured, or re-measure what you committed.")
        fi
        ;;
      CLAIM)
        R2_FAIL+=("$sha
      quotes: ${rest:0:96}
      touches a soundness-gate path and carries no 'Measured-on:' trailer.")
        ;;
    esac
  done < <(printf '%s\n' "$SWEEP" | grep -v '^STATS' || true)

  # R2 candidates are confirmed only now, because deciding whether a commit
  # touches a soundness-gate path costs a `git diff-tree` per commit and must not
  # be paid for the whole range. Post-epoch claim-quoting commits are the only
  # ones that reach here.
  #
  # The listing is plumbing with each default that hides a path pinned off:
  #   -z                        raw paths. The default C-quotes a non-ASCII name
  #                             ("crates/trust-thir-lower/src/g\303\244te.rs"),
  #                             which the anchored regex never matches, and
  #                             core.quotePath=false still quotes a tab, a quote
  #                             or a backslash.
  #   --no-renames              a move lists its OLD path as well, so moving a
  #                             gate out of the soundness paths touches them,
  #                             exactly as deleting it does.
  #   -m                        a merge is diffed against EACH parent and the
  #                             union taken. The default combined diff lists only
  #                             paths that differ from every parent, so a clean
  #                             merge that brings a gate edit in listed nothing,
  #                             and whether a merge was judged depended on whether
  #                             it had conflicts. A merge's tree is a new tree; a
  #                             count in its message is a claim about it. The
  #                             union, not the first parent alone: which parent a
  #                             merge extends depends on who ran it and where it
  #                             is pushed (main merged into a topic, then the
  #                             topic fast-forwarded onto main, brings the topic's
  #                             gates in against parent 2), so the lane does not
  #                             guess.
  #   --ignore-submodules=none  a gitlink move stays visible whatever a tracked
  #                             .gitmodules ignore= says (plumbing honours it;
  #                             the per-clone diff.ignoreSubmodules reaches only
  #                             porcelain, which this listing no longer is).
  #   --root                    a root commit lists what it adds.
  # A listing git cannot produce is a refusal (exit 2), never "touches nothing":
  # R1 already refuses a tree it cannot read, and R2 must fail the same way.
  R2_CONFIRMED=()
  for entry in "${R2_FAIL[@]:-}"; do
    [ -n "$entry" ] || continue
    sha="${entry%%$'\n'*}"
    # tr turns each NUL terminator into a newline and each newline INSIDE a path
    # into \001, so one line is exactly one path. pipefail carries git's status.
    paths="$(git --no-replace-objects diff-tree -r -z -m --root --no-renames \
               --ignore-submodules=none --name-only --no-commit-id "$sha" \
             | tr '\012\000' '\001\012')" \
      || die "cannot list the paths $sha touches — refusing to report green on a commit I could not read"
    touched=(); seen=$'\n'
    while IFS= read -r p; do
      [ -n "$p" ] || continue
      [[ "$p" =~ $SOUNDNESS_PATH_RE ]] || continue
      # -m lists a path once per parent it differs from.
      case "$seen" in *$'\n'"$p"$'\n'*) continue ;; esac
      seen="$seen$p"$'\n'
      touched+=("$p")
    done <<< "$paths"
    [ "${#touched[@]}" -gt 0 ] || continue
    R2_CONFIRMED+=("$entry
      soundness-gate paths in this commit: ${touched[*]:0:3}")
  done

  echo "=== measurement provenance (${MODE}; ${EXAMINED} commit(s), ${STAMPED} stamped, ${TRAILERS} trailer(s), ${WAIVED} grandfathered) ==="

  if [ "${#R1_FAIL[@]}" -eq 0 ] && [ "${#R2_CONFIRMED[@]}" -eq 0 ]; then
    echo "MEASUREMENT PROVENANCE: GREEN — every stamp names a tree this commit carries."
    exit 0
  fi

  if [ "${#R1_FAIL[@]}" -gt 0 ]; then
    echo
    echo "FAIL (R1): a provenance stamp disagrees with the commit that carries it."
    for f in "${R1_FAIL[@]}"; do echo "  x $f"; done
  fi
  if [ "${#R2_CONFIRMED[@]}" -gt 0 ]; then
    echo
    echo "FAIL (R2): a soundness-gate commit quotes a test count and names no tree."
    for f in "${R2_CONFIRMED[@]}"; do echo "  x $f"; done
  fi

  cat <<'EOF'

A test count is a claim about ONE tree. Say which:

    bash scripts/lib/measure_stamp.sh <the files under test>   # inside the
                                                               # worktree you ran
    # then paste its '--- trailer' lines into the commit body:
    Measured-on: crates/trust-thir-lower/src/lib.rs@<blob>

The stamp is checked against the commit's own tree, so pasting it after a
further edit fails rather than passing quietly. That is the point: on
2026-08-19 a real "599 passed, 0 failed" was published about a tree that was
never committed, a confirmed-miscompile-class gate was reverted on it, and the
class sat ungated for 2h10m. reports/revert-silence-rca-2026-08-20.md

'git push --no-verify' skips this hook and leaves no record of why.
EOF
  exit 1
fi

# ===========================================================================
# --selftest — THE MUTATION PROOF
#
# A provenance gate that has never been seen to REJECT is a gate nobody tested,
# and one that passes on a dirty tree is worse than none. This builds a scratch
# repository, REPLAYS THE ACTUAL INCIDENT (commit, then edit without adding,
# then measure, then publish), and asserts the refusal. It touches nothing
# outside its own mktemp directory and it uses THIS script, not a copy.
# ===========================================================================
SELFTEST_TMP=""
selftest_cleanup() { [ -n "${SELFTEST_TMP:-}" ] && rm -rf "$SELFTEST_TMP"; return 0; }

selftest() {
  local me helper tmp pass=0 fail=0 rc
  me="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/$(basename "${BASH_SOURCE[0]}")"
  helper="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/lib/measure_stamp.sh"
  [ -f "$helper" ] || { echo "selftest: $helper missing"; return 2; }
  tmp="$(mktemp -d)"; SELFTEST_TMP="$tmp"; trap selftest_cleanup EXIT

  mkdir -p "$tmp/repo/crates/trust-thir-lower/src"
  cd "$tmp/repo" || return 2
  git init -q . && git config user.email s@l && git config user.name s
  git config commit.gpgsign false
  local SRC=crates/trust-thir-lower/src/lib.rs
  printf 'fn f() { let off = q(); }\n' > "$SRC"
  git add -A >/dev/null && git commit -qm baseline >/dev/null

  say() { printf '%s\n' "$*"; }
  expect() { # expect <want-rc> <label> -- <args...>
    local want="$1" label="$2"; shift 3
    bash "$me" "$@" >"$tmp/out" 2>&1; rc=$?
    if [ "$rc" -eq "$want" ]; then say "  PASS  $label (rc=$rc)"; pass=$((pass+1))
    else say "  FAIL  $label (want rc=$want, got $rc)"; sed 's/^/        /' "$tmp/out"; fail=$((fail+1)); fi
  }
  expect_grep() { # expect_grep <want-rc> <needle> <label> -- <args...>
    local want="$1" needle="$2" label="$3"; shift 4
    bash "$me" "$@" >"$tmp/out" 2>&1; rc=$?
    if [ "$rc" -eq "$want" ] && grep -q "$needle" "$tmp/out"; then
      say "  PASS  $label (rc=$rc, names it)"; pass=$((pass+1))
    else
      say "  FAIL  $label (want rc=$want got $rc; needle '$needle' present: $(grep -c "$needle" "$tmp/out"))"
      sed 's/^/        /' "$tmp/out"; fail=$((fail+1))
    fi
  }

  say "=== measurement-provenance selftest ==="

  # ---- the log gate -------------------------------------------------------
  printf 'running 599 tests\ntest result: ok. 599 passed; 0 failed\n' > "$tmp/nostamp.log"
  expect_grep 1 "NO PROVENANCE STAMP" "unstamped log -> REJECTED" -- --log "$tmp/nostamp.log"

  # A clean tree, stamped: accepted.
  { bash "$helper" "$SRC"; printf 'test result: ok. 599 passed; 0 failed\n'; } > "$tmp/clean.log" 2>&1
  expect 0 "stamped log on a CLEAN tree -> accepted" -- --log "$tmp/clean.log"

  # ---- THE INCIDENT, replayed --------------------------------------------
  # Edit the file WITHOUT `git add` — exactly 22:47:17 — then measure.
  printf 'fn f() { let (off, off_source) = q(); }\n' > "$SRC"
  { bash "$helper" "$SRC"; printf 'test result: ok. 599 passed; 0 failed\n'; } > "$tmp/dirty.log" 2>&1
  expect_grep 1 "DIFFER FROM HEAD" "THE INCIDENT: stamped log on an UNCOMMITTED edit -> REJECTED" -- --log "$tmp/dirty.log"

  # The trailer the honest stamp emits names the tree that was measured...
  local measured_blob committed_blob trailer
  measured_blob="$(git hash-object "$SRC")"
  committed_blob="$(git rev-parse "HEAD:$SRC")"
  if [ "$measured_blob" = "$committed_blob" ]; then
    say "  FAIL  fixture: the edit did not change the blob"; fail=$((fail+1))
  else
    say "  PASS  fixture: measured $measured_blob != committed $committed_blob"; pass=$((pass+1))
  fi

  # ...and publishing it on the PRE-EDIT commit is R1's whole subject.
  git checkout -q -- "$SRC"
  git commit -q --allow-empty -m "feat: wave-SG lands

599 passed, 0 failed, 12 of them this lane's.

Measured-on: $SRC@$measured_blob
" >/dev/null
  expect_grep 1 "DIFFERENT TREE" "THE INCIDENT: trailer names a tree the commit does not carry -> REJECTED" \
    -- --selftest-run "HEAD~1..HEAD"

  # The same commit with the trailer it should have had is GREEN.
  git commit -q --amend --allow-empty -m "feat: wave-SG lands

599 passed, 0 failed.

Measured-on: $SRC@$committed_blob
" >/dev/null
  expect 0 "trailer that names the committed tree -> GREEN" -- --selftest-run "HEAD~1..HEAD"

  # ---- R1 corner cases ----------------------------------------------------
  git commit -q --allow-empty -m "x

Measured-on: crates/trust-thir-lower/src/nope.rs@$committed_blob
" >/dev/null
  expect_grep 1 "HAS NO SUCH PATH" "trailer naming a path the commit lacks -> REJECTED" -- --selftest-run "HEAD~1..HEAD"

  git commit -q --amend --allow-empty -m "x

Measured-on: $SRC@deadbeef
" >/dev/null
  expect_grep 1 "not a 40-hex" "trailer with a short/garbage blob -> REJECTED" -- --selftest-run "HEAD~1..HEAD"

  # A commit with NO trailer at all is not condemned by R1.
  git commit -q --amend --allow-empty -m "x: no claim, no trailer" >/dev/null
  expect 0 "commit with no trailer and no claim -> GREEN (R1 is vacuous)" -- --selftest-run "HEAD~1..HEAD"

  # ---- R2 -----------------------------------------------------------------
  # A claim on a soundness-gate path with no stamp. The fixture path IS one
  # (crates/trust-thir-lower/), and the commit must be post-epoch, which a
  # freshly created commit is.
  printf 'fn f() { let off = q(); /* v2 */ }\n' > "$SRC"
  git add -A >/dev/null
  git commit -qm "fix(thir-lower): tighten the offset gate

The crate suite is 599 passed, 0 failed at this tree.
" >/dev/null
  expect_grep 1 "FAIL (R2)" "R2: soundness-gate commit quoting a count, unstamped -> REJECTED" -- --selftest-run "HEAD~1..HEAD"

  # ...and the same commit with a true stamp passes.
  git commit -q --amend -m "fix(thir-lower): tighten the offset gate

The crate suite is 599 passed, 0 failed at this tree.

Measured-on: $SRC@$(git hash-object "$SRC")
" >/dev/null
  expect 0 "R2: the same commit, stamped truthfully -> GREEN" -- --selftest-run "HEAD~1..HEAD"

  # A claim OUTSIDE the soundness paths is not R2's subject — stated, not hidden.
  mkdir -p docs && printf 'notes\n' > docs/n.md && git add -A >/dev/null
  git commit -qm "docs: notes

1234 passed, 0 failed somewhere else entirely.
" >/dev/null
  expect 0 "R2 does NOT reach a claim outside the soundness paths (documented gap)" -- --selftest-run "HEAD~1..HEAD"

  # ---- R2: what the path listing must not hide ------------------------------
  # Each case below was GREEN when the listing was `git show --name-only`. The
  # porcelain defaults each one leans on are pinned in this scratch repo, so a
  # global config that happens to switch one off cannot make a case vacuous.
  git config core.quotePath true
  git config diff.renames true
  local main_branch
  main_branch="$(git symbolic-ref --short HEAD)"

  # A non-ASCII name is C-quoted by porcelain, and the anchored regex never
  # matched the quoted form.
  printf 'gate\n' > "crates/trust-thir-lower/src/g$(printf '\303\244')te.rs"
  git add -A >/dev/null
  git commit -qm "fix(thir-lower): the umlaut gate

599 passed, 0 failed.
" >/dev/null
  expect_grep 1 "FAIL (R2)" "R2: a gate file with a NON-ASCII name, unstamped -> REJECTED" -- --selftest-run "HEAD~1..HEAD"

  # Moving a gate OUT of the soundness paths touches them, as deleting it does.
  printf 'gate\n' > crates/trust-thir-lower/src/moved.rs
  git add -A >/dev/null && git commit -qm "add the gate to be moved" >/dev/null
  mkdir -p crates/elsewhere
  git mv crates/trust-thir-lower/src/moved.rs crates/elsewhere/moved.rs
  git commit -qm "refactor: move the gate

599 passed, 0 failed.
" >/dev/null
  expect_grep 1 "FAIL (R2)" "R2: a RENAME out of the soundness paths, unstamped -> REJECTED" -- --selftest-run "HEAD~1..HEAD"

  # A CLEAN merge that brings a gate edit in: the combined diff lists nothing.
  git checkout -qb topic
  printf 'fn f() { let off = q(); /* v3 */ }\n' > "$SRC"
  git add -A >/dev/null && git commit -qm "wip: offset gate edit (no claim)" >/dev/null
  git checkout -q "$main_branch"
  printf 'more\n' >> docs/n.md
  git add -A >/dev/null && git commit -qm "docs: more notes" >/dev/null
  GIT_MERGE_AUTOEDIT=no git merge -q --no-ff topic -m "Merge topic: tighten the offset gate

599 passed, 0 failed.
" >/dev/null
  expect_grep 1 "FAIL (R2)" "R2: a CLEAN --no-ff merge bringing in a gate edit, unstamped -> REJECTED" -- --selftest-run "HEAD~1..HEAD"

  # ...and its control: a merge whose parents differ only outside the
  # soundness paths is not R2's subject.
  git checkout -qb topic2
  printf 'a\n' > docs/t2.md
  git add -A >/dev/null && git commit -qm "docs: t2" >/dev/null
  git checkout -q "$main_branch"
  printf 'b\n' > docs/t3.md
  git add -A >/dev/null && git commit -qm "docs: t3" >/dev/null
  GIT_MERGE_AUTOEDIT=no git merge -q --no-ff topic2 -m "Merge topic2: notes

1234 passed, 0 failed.
" >/dev/null
  expect 0 "R2: a merge that differs from its parents only outside the soundness paths -> GREEN" -- --selftest-run "HEAD~1..HEAD"

  # A gitlink under a soundness path, on a clone with diff.ignoreSubmodules=all.
  # The config is set only after the commit: with it set, `git commit` itself
  # sees nothing to commit.
  mkdir -p src/tools/trust-sub
  git update-index --add --cacheinfo "160000,$(git rev-parse HEAD),src/tools/trust-sub"
  git commit -qm "chore: pin trust-sub

599 passed, 0 failed.
" >/dev/null
  git config diff.ignoreSubmodules all
  expect_grep 1 "FAIL (R2)" "R2: a GITLINK under a soundness path, diff.ignoreSubmodules=all -> REJECTED" -- --selftest-run "HEAD~1..HEAD"
  git config --unset diff.ignoreSubmodules

  # The same, hidden by a TRACKED `.gitmodules` ignore=all instead. Plumbing
  # honours this one too, so only --ignore-submodules=none sees the gitlink.
  printf '[submodule "trust-sub2"]\n\tpath = src/tools/trust-sub2\n\turl = ./none\n\tignore = all\n' > .gitmodules
  git add .gitmodules && git commit -qm "chore: declare trust-sub2 (no claim)" >/dev/null
  mkdir -p src/tools/trust-sub2
  git update-index --add --cacheinfo "160000,$(git rev-parse HEAD),src/tools/trust-sub2"
  git commit -qm "chore: pin trust-sub2

599 passed, 0 failed.
" >/dev/null
  expect_grep 1 "FAIL (R2)" "R2: a GITLINK under a soundness path, .gitmodules ignore=all -> REJECTED" -- --selftest-run "HEAD~1..HEAD"

  # A tree git cannot read is a refusal, never "touches nothing". LAST: it
  # corrupts the scratch repository on purpose.
  printf 'fn f() { let off = q(); /* v4 */ }\n' > "$SRC"
  git add "$SRC" && git commit -qm "fix(thir-lower): again

599 passed, 0 failed.
" >/dev/null
  local tree
  tree="$(git rev-parse 'HEAD^{tree}')"
  rm -f ".git/objects/${tree:0:2}/${tree:2}"
  expect_grep 2 "cannot list the paths" "R2: a commit whose tree cannot be read -> exit 2 (fails closed, never green)" -- --selftest-run "HEAD~1..HEAD"

  # ---- the ledger may not waive by accident -------------------------------
  # A grandfather row is read only as a full 40-hex sha; anything else is inert.
  say ""
  say "selftest: $pass passed, $fail failed"
  [ "$fail" -eq 0 ]
}

selftest
