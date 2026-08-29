#!/usr/bin/env bash
# A REVERT MUST STATE WHY. The gate that makes a silent revert unpushable.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# WHY THIS EXISTS
# ---------------
# 2026-08-20, measured, not recalled. `8e214e90d5` landed wave-SG, the gate that
# closes the struct-interior offset class — a CONFIRMED miscompile mechanism
# (rustc's reorder-aware `layout.fields.offset` emitted as a byte displacement
# that the consumer's declaration-order image does not agree with; the executed
# discriminator returns a different live field's value, in bounds, well typed,
# with no error). `31814afa35` reverted it two and a half hours later. The whole
# commit body was:
#
#     This reverts commit 8e214e90d5fb8f11b47c35080bfc85711ec32d5a.
#
# and nothing else — no reason in the message, none in a report, none in a lane
# note, no commit comment on the remote. Measured: the gate held `main` for
# 2h08m, the class was ungated again for the next 2h10m, and it came back only
# because ANOTHER lane independently re-derived the evidence and re-landed it
# as `52cf9c47db`.
#
# The revert itself was very likely CORRECT: at `8e214e90d5` the crate's own
# `--lib` suite was RED (wave-SG widened a binding from `let off` to
# `let (off, off_source)` and silently invalidated the literal that
# `zero_displacement_tests::test_the_zero_displacement_guard_runs_after_the_offset_query`
# searches for). Reverting a red commit is the right reflex. Writing down which
# red is not optional — without it the next lane cannot tell "this broke a test,
# fix the needle" from "this gate is wrong, do not re-land it", and has to spend
# hours re-deriving a fact the reverter already had in hand.
#
# So this gate does not judge whether a revert is justified. It requires only
# that the justification EXIST, in the one place that always travels with the
# commit.
#
# THE RULE
# --------
# A commit whose subject begins `Revert "` — or `Reapply "`, which is what
# modern git generates when the thing being reverted is itself a revert, and
# which is exactly the re-land case where the reason matters most — must carry
# a body with at least MIN_CHARS non-whitespace characters that are not:
#   * the generated `This reverts commit <sha>.` line,
#   * a generated `(cherry picked from commit <sha>)` line,
#   * a git trailer (`Co-authored-by:`, `Signed-off-by:`, and the rest of the
#     standard set) — a `Co-Authored-By:` line is attribution, never a reason,
#     and without this exclusion every agent-authored bare revert would pass.
#
# Nothing here inspects the reverted commit to decide WHETHER the rule applies:
# the rule is universal, so it cannot be dodged by a revert whose subject does
# not look load-bearing. When the reverted sha is resolvable the report says
# whether it touched a soundness-gate path, because that is what makes the
# refusal concrete — but the requirement does not depend on it.
#
# ESCAPE HATCH is git's own (`git push --no-verify`), which shows up in the
# reflog rather than in a habit. There is no environment variable, and there is
# no minimum-length knob: a tunable threshold is a threshold someone tunes to 0.
#
# GRANDFATHERED HISTORY. Eleven bare reverts predate this gate. They are listed
# by full sha in `scripts/revert-rationale-grandfathered.txt` so that pushing a
# branch which carries them does not fail on somebody else's old silence. That
# list may only ever shrink; adding a row to it for a NEW revert is the same act
# as deleting the gate, and the file says so.
#
# Usage:
#   scripts/check_revert_rationale.sh --pre-push        # reads git's pre-push stdin
#   scripts/check_revert_rationale.sh --push-context    # --pre-push via $TRUST_PUSHED_REFS
#   scripts/check_revert_rationale.sh <rev-range>...    # e.g. origin/main..HEAD
#   scripts/check_revert_rationale.sh --history [<since-rev>]   # default: 90 days, --all
#
# Exit codes:
#   0  no unexplained revert in the examined set
#   1  at least one unexplained revert
#   2  the checker could not do its job (fails closed; never reports green)

set -uo pipefail

MIN_CHARS=40
LEDGER_REL="scripts/revert-rationale-grandfathered.txt"

# Paths whose change makes a revert a SOUNDNESS-GATE revert. Informational only:
# it sharpens the refusal message, it never decides whether the rule applies.
SOUNDNESS_PATH_RE='^(crates/trust-thir-lower/|crates/trust-ir|compiler/rustc_trust|scripts/check_|scripts/hooks|src/tools/trust|tests/trust-comprehensive/divergences.toml)'

die() { printf 'check_revert_rationale: %s\n' "$*" >&2; exit 2; }

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
    exec bash "$self" --pre-push "$@" <<< "$TRUST_PUSHED_REFS"
  fi
  echo "SUBJECT: history (no push in flight; TRUST_PUSHED_REFS unset)"
  exec bash "$self" --history "$@"
fi

REPO_ROOT="$(git rev-parse --show-toplevel 2>/dev/null)" || die "not inside a git worktree"
cd "$REPO_ROOT" || die "cannot enter $REPO_ROOT"

# ------------------------------------------------------------- rev enumeration
REVS_ARGS=()
MODE=""
case "${1:---help}" in
  --pre-push)
    MODE=pre-push
    shift
    # pre-push is fed "<local-ref> <local-sha> <remote-ref> <remote-sha>" lines.
    # Read every one of them: git must never see EPIPE on this fd.
    while read -r _local_ref local_sha _remote_ref remote_sha; do
      [ -n "${local_sha:-}" ] || continue
      # An all-zero local sha is a branch DELETION; there is nothing to judge.
      case "$local_sha" in
        *[!0]*) ;;
        *) continue ;;
      esac
      if [ -z "${remote_sha:-}" ] || [ -z "${remote_sha//0/}" ]; then
        # New ref on the remote: judge what this push introduces that no remote
        # already holds, rather than the branch's whole ancestry.
        REVS_ARGS+=("$local_sha" "--not" "--remotes")
      else
        REVS_ARGS+=("${remote_sha}..${local_sha}")
      fi
    done
    if [ "${#REVS_ARGS[@]}" -eq 0 ]; then
      echo "REVERT RATIONALE: nothing to judge (no updated refs on stdin)."
      exit 0
    fi
    ;;
  --history)
    # The SECOND net, and the reason it exists: a hook only binds the machines
    # that installed it, and `31814afa35` was pushed from a machine whose lane
    # was working on something else entirely. This mode judges every branch tip
    # in the recent past, so a bare revert pushed past the hook is caught by the
    # next lane that runs the gate manifest rather than by nobody.
    MODE=history
    shift
    if [ -n "${1:-}" ]; then
      REVS_ARGS=("${1}..HEAD")
    else
      REVS_ARGS=("--since=90.days" "--all")
    fi
    ;;
  -h|--help)
    sed -n '/^# Usage:/,/^#   2 /p' "$0" | sed 's/^# \{0,1\}//'
    exit 0
    ;;
  *)
    MODE=range
    REVS_ARGS=("$@")
    ;;
esac

# ------------------------------------------------------------------- the sweep
# ONE `git log` for the whole range, not one per commit: a `git log -1` per
# revision costs ~90s over this repository's 7,089 commits, which is how a gate
# becomes something people route around.
#
# `%x1f` separates the three fields, `%x1e` separates records. A body is
# multi-line by nature, so it must be the LAST field.
LOG="$(git log --format='%H%x1f%s%x1f%b%x1e' "${REVS_ARGS[@]}" 2>/dev/null)" \
  || die "git log ${REVS_ARGS[*]} failed — refusing to report green on a range I cannot read"

SWEEP="$(printf '%s' "$LOG" | awk -v ledger="$LEDGER_REL" -v min="$MIN_CHARS" '
  BEGIN {
    # The ledger is read FIRST, while RS is still a newline. Setting RS to the
    # record separator before this loop swallows the whole file as one record
    # and silently waives nothing — the failure mode this ordering exists to
    # prevent, and the one `L1` in scripts/tests/ caught.
    while ((getline row < ledger) > 0) {
      sub(/#.*/, "", row)
      gsub(/[ \t\r\n]/, "", row)
      if (row ~ /^[0-9a-f]{40}$/) waived[row] = 1
    }
    RS = "\036"; FS = "\037"
  }
  {
    sha = $1
    sub(/^[\n\r]+/, "", sha)
    if (sha !~ /^[0-9a-f]{40}$/) next
    examined++
    subject = $2
    # `Reapply "` is git >= 2.42s subject for a revert-of-a-revert; older git
    # spells the same commit `Revert "Revert "`. Both are matched, so the rule
    # does not depend on the git version that happened to author the commit.
    if (subject !~ /^Revert "/ && subject !~ /^Reapply "/) next
    reverts++
    if (sha in waived) { grandfathered++; next }

    n = split($3, lines, "\n")
    chars = 0
    for (i = 1; i <= n; i++) {
      line = lines[i]
      sub(/^[ \t\r]+/, "", line)
      sub(/[ \t\r]+$/, "", line)
      if (line == "") continue
      if (line ~ /^This reverts commit [0-9a-fA-F]{7,40}\.?$/) continue
      if (line ~ /^\(cherry picked from commit [0-9a-fA-F]{7,40}\)$/) continue
      low = tolower(line)
      if (low ~ /^(co-authored-by|co-developed-by|signed-off-by|reviewed-by|acked-by|tested-by|reported-by|suggested-by|helped-by|cc|change-id):/) continue
      gsub(/[ \t]/, "", line)
      chars += length(line)
    }
    if (chars >= min) next
    printf "OFFENDER\037%s\037%s\037%d\n", sha, subject, chars
  }
  END { printf "STATS\037%d\037%d\037%d\n", examined + 0, reverts + 0, grandfathered + 0 }
')" || die "the sweep failed — refusing to report green"

EXAMINED=0; REVERTS=0; WAIVED=0
OFFENDERS=()
while IFS=$'\037' read -r kind a b c; do
  case "$kind" in
    STATS) EXAMINED="$a"; REVERTS="$b"; WAIVED="$c" ;;
    OFFENDER)
      sha="$a"; subject="$b"; chars="$c"
      # The refusal is decided. Everything below only makes it concrete.
      reverted="$(git log -1 --format=%b "$sha" 2>/dev/null \
        | sed -n "s/^This reverts commit \([0-9a-fA-F]\{7,40\}\)\.\{0,1\}$/\1/p" | head -1)"
      note=""
      if [ -n "$reverted" ] && git cat-file -e "${reverted}^{commit}" 2>/dev/null; then
        touched="$(git show --name-only --format= "$reverted" 2>/dev/null \
          | grep -E "$SOUNDNESS_PATH_RE" | head -3 | tr "\n" " ")"
        if [ -n "$touched" ]; then
          note="      the reverted commit touches SOUNDNESS-GATE paths: ${touched%% }"
        fi
      elif [ -n "$reverted" ]; then
        note="      the reverted commit ${reverted} is not in this object store"
      fi
      OFFENDERS+=("${sha}  ${subject}
      body carries ${chars} explanatory characters; ${MIN_CHARS} are required${note:+
$note}")
      ;;
  esac
done <<<"$SWEEP"

if [ "$EXAMINED" -eq 0 ] && [ "$MODE" != "history" ]; then
  # A range that resolves to nothing is legitimate (an empty push); a range we
  # could not read is not, and `git log` above would already have died.
  :
fi

# ------------------------------------------------------------------ the report
echo "=== revert-rationale (${MODE}; ${EXAMINED} commit(s), ${REVERTS} revert(s), ${WAIVED} grandfathered) ==="

if [ "${#OFFENDERS[@]}" -eq 0 ]; then
  echo "REVERT RATIONALE: GREEN — every revert states a reason."
  exit 0
fi

echo
echo "FAIL: a revert that does not say WHY."
for o in "${OFFENDERS[@]}"; do echo "  x $o"; done
cat <<'EOF'

A revert is a decision, and the decision is the part that does not survive in
the diff. Write it in the commit message — one or two sentences is enough:

    git commit --amend            # or: git rebase -i, then reword

    Revert "<subject>"

    This reverts commit <sha>.

    <WHY>. Name the observation: the test that went red and its verbatim
    final line, the gate that refused, the build that broke. If the reverted
    change is still believed CORRECT, say so and say what has to be true
    before it is re-landed.

Reverting a red commit is the right reflex; doing it silently is what costs
the next lane hours. `git push --no-verify` skips this hook and leaves no
record of why.
EOF
exit 1
