#!/usr/bin/env bash
# check_frozen_files.sh — THE ORACLE FREEZE GATE.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# ===========================================================================
# WHAT THIS IS FOR
# ===========================================================================
# The differential is the ORACLE: rustc's own freshly-built MIR is what the
# AI-generated compiler components are checked against. A change that weakens it
# does not fix a disagreement, it MANUFACTURES an agreement — and it does so
# invisibly, because the number it moves is the number everyone reads as
# evidence.
#
# So a small set of files is FROZEN (scripts/frozen-files.txt). Until 2026-08-20
# that freeze was enforced by lanes remembering it. Measured that day: three
# commits had moved two of the four frozen files, and the movement was found by
# an audit, not by a gate. All three turned out to be legitimate work — which is
# the point. A rule that fires only when someone remembers it cannot tell the
# three good commits from the one it exists to catch, because it never fires.
#
# ===========================================================================
# WHAT IT CHECKS, AND THE ONE THING IT DELIBERATELY DOES NOT
# ===========================================================================
# It checks BLOB IDENTITY, in the tree being judged, against a pin. Nothing
# else. It does not parse Rust, does not classify a change as safe, and
# does not decide whether an edit "only samples more". Those are judgements, and
# a gate that makes judgements is a gate that can be argued with.
#
# Every judgement is therefore pushed OUT of the script and INTO a written
# waiver with a date, a commit list and a reason (scripts/frozen-waivers.txt).
# The gate's whole job is to make sure the judgement was WRITTEN DOWN — in the
# tree being judged, beside the move it excuses.
#
# It does print one ADVISORY: whether a moved file's change is comment-only.
# That is never a pass. Line-comment stripping is not a Rust lexer (a `//`
# inside a string literal defeats it), so believing it would be exactly the kind
# of soft heuristic this gate exists to replace. It is printed to make the
# honest case cheap to waive, not to waive it.
#
# ===========================================================================
# WHICH TREE IS JUDGED — TWO READINGS, AND THE `SUBJECT:` LINE SAYS WHICH
# ===========================================================================
# A tree is judged WHOLE: its frozen files, ITS OWN manifest and waivers
# (scripts/frozen-files.txt, scripts/frozen-waivers.txt) and the files ITS OWN
# ENFORCED-BY citations name, all read from that one tree. Nothing is mixed
# across trees, because each mix is a hole:
#
#   * a waiver written but never committed excused a committed move, and the
#     push landed a moved oracle file beside an EMPTY waivers file;
#   * a manifest row deleted but never committed ("GREEN — 0 frozen file(s)")
#     was a way to point the gate at a different manifest, which the header
#     below says does not exist;
#   * a citation to a test file that was never committed resolved, so the
#     remote carried a claim backed by nothing.
#
# PUSH CONTEXT — TRUST_PUSHED_REFS is set and names at least one ref
# (scripts/hooks/pre-push exports git's own pre-push lines, one
# "<local-ref> <local-sha> <remote-ref> <remote-sha>" per update, and
# scripts/hooks-pin/pre-push passes the same lines to this gate). The tree of
# EVERY pushed commit is judged: each local sha is peeled to its commit (an
# annotated tag hands over the tag object), a deletion (all-zero local sha)
# lands no tree and is skipped, and the push is RED if any pushed tree is RED.
# The remote sha is not consulted: the verdict is a property of the tree that
# lands, so a force push, a rewind, `git push origin other:main`, a tag or a
# multi-ref push is judged exactly like a fast-forward of HEAD. THE WORKING
# TREE IS NOT READ — it is not pushed, and an uncommitted scratch edit must not
# refuse a push whose tree is at the pin. A pushed branch or tag whose tree has
# no manifest is RED: the gate cannot tell a tree that never carried the oracle
# from one that deleted the manifest to escape it. A line that is not four
# fields, or a sha that does not peel to a commit, refuses (exit 2). A push that
# names only deletions, or no ref at all (set but empty: git runs pre-push with
# empty stdin when every ref is already up to date), lands no tree: it judges
# nothing and prints `SKIPPED: ` (the harness grades that SKIP, not PASS). It
# never falls back to HEAD and the working tree, which would refuse a push of
# nothing over an uncommitted scratch edit.
#
# Until 2026-09-28 the gate never read TRUST_PUSHED_REFS: it judged HEAD and the
# working tree whatever was pushed, so `git push origin bad:main` from a
# pristine checkout, or a tag push of a moved commit, was GREEN and landed; and
# a pristine ref pushed from a checkout whose HEAD had moved was refused.
#
# STANDING READING — TRUST_PUSHED_REFS unset (a manual run, the fast profile
# outside a push). Two trees are judged, each whole: HEAD's committed tree,
# and the working tree. They close different holes. The working tree is what
# you are about to commit; HEAD is what you are about to push. A check on only
# the working tree misses "commit the change, then restore the file"; a check
# on only HEAD misses the edit you have not committed yet. An unborn HEAD (no
# commit yet) judges the working tree alone; a HEAD that does not resolve for
# any other reason refuses.
#
# ABSENT IS A MOVE, AND A GIT FAILURE IS NOT ABSENT. A frozen path that is not a
# file in the judged tree (deleted, renamed away, replaced by a directory) is
# DELETED/RED. Until 2026-09-28 a path absent at HEAD read as "HEAD did not
# move", so `git rm --cached` of a frozen file, or a `git mv` + rewrite with a
# copy left at the old path, committed and pushed GREEN. Any git command that
# fails is RED, never "nothing there".
#
# ===========================================================================
# WHAT BACKS THE CLAIM (2026-09-24)
# ===========================================================================
# An ordinary waiver's sentence is "this change REFUSES MORE (or
# SAMPLES MORE) and admits nothing new". The exact rmeta_entry.rs producer
# exception for blob65d75e5a71ad9b9514517966b61e5352fda2933e is separately
# adjudicated in docs/decisions/2026-11-06-official-s-producer-adjudication.md
# and recorded in frozen-files.txt. It changes no executable freeze check or
# other row's rule.
# The separately adjudicated schema5 blob14dc6d4053135949a93464613a38f25e859fc14f
# is recorded in docs/decisions/2026-11-06-r-schema5-adjudication.md; it likewise
# changes no executable check and supplies no admission or proof authority.
# The blob check above makes sure the written judgement is present; nothing
# above asks whether it is TRUE. A row may now
# cite the TEST that fails if it is false:
#
#     ENFORCED-BY: crates/x/src/y_tests.rs::the_test_fn[, path::fn ...]
#
# Every citation must RESOLVE — the file exists in THE JUDGED tree and carries a
# `#[test]` fn of that name — or the gate is RED: a citation to nothing is a
# claim that has rotted into a sentence about nothing. This is the trust-ir
# `check_enforcement_links.py` idea (E2 RESOLVES, E3 WITNESS) applied to
# waivers; it does not RUN the test (the crate's suite does), and it proves
# nothing about the claim. It makes an unbacked claim VISIBLE and a rotted one
# a failure.
#
# A row with no citation is PROSE-ONLY. Those are printed, counted, and
# ratcheted: when scripts/frozen-waivers.txt carries `# prose-only-max: N`,
# the count must EQUAL N — higher is a new claim nobody tested, lower means
# somebody must write the smaller number down. The number can only move in a
# commit that says why.
#
# A citation backs what its test executes, and no more. When a cited row's
# load-bearing claim is only PARTLY executed, the row says which part is not,
# in a clause
#
#     PROSE-RESIDUAL: <the part of the claim no cited test fails on>
#
# and the gate counts those rows exactly like prose-only ones, under their own
# ratchet, `# prose-residual-max: N` (2026-09-28). Without it a row whose tests
# pin half its claim would read as fully backed, and the prose-only count —
# the one number that keeps an unexecuted claim VISIBLE — would drop to a
# value the claims do not support. The clause is DECLARED by the row's writer:
# the gate cannot tell whether a cited test tests the claim (it never could),
# so it counts what is written down and makes the count move only in a commit
# that says why. Both ratchets, like every other row, are read from the
# judged tree's own waivers file.
#
# A waiver whose blob IS the pin is SPENT too (2026-09-28): moving the pin
# ratified the movement, so the row documents nothing and step 3 of
# scripts/frozen-files.txt says to delete it. Until then the gate flagged only
# a waiver whose blob neither HEAD nor the working tree carries, so a ratified
# row stayed GREEN forever — the opposite of the property the waivers file
# states. (A waiver is now SPENT in a judged tree that does not carry its
# blob, and the pin it is compared to is that tree's own manifest row.)
#
# ===========================================================================
# THE PIN-RELATIVE DELTA (2026-09-28)
# ===========================================================================
# What a ratification adopts is the move FROM THE PIN, never the last increment:
# moving the pin adopts every line between the pin and the waived blob. A row
# written as "CARRIED FORWARD from the previous waiver" and adjudicating only
# its own increment therefore under-describes the movement it asks a reviewer to
# ratify — and when a carried-forward row replaced a history instead of
# extending it (e621a31544, differential.rs), the earlier adjudications left the
# live file altogether and the row read as the whole account.
#
# So every LIVE row (its blob is in the judged tree and is not the pin) carries
# exactly one clause
#
#     PIN-DELTA: +A/-D
#
# where A/D are the lines the waived blob adds/deletes against the pin in the
# judged tree's OWN manifest, i.e. what
#
#     git diff --numstat --diff-algorithm=myers <pin-blob> <waived-blob>
#
# prints. The gate measures it and is RED when the clause is missing, appears
# more than once, or disagrees — so a row that states the increment since an
# earlier waiver is RED unless that increment happens to be the whole delta.
# The algorithm is named because numstat depends on it (see `pin_delta`).
# Like ENFORCED-BY this checks what a script can decide and no more: that the
# row KNOWS the size of the move it asks to be ratified. Whether its prose
# accounts for all of it stays a judgement, and the number makes an account
# that covers a fraction of it visible at a glance.
#
# ===========================================================================
# NO ESCAPE HATCH, BY CONSTRUCTION
# ===========================================================================
# There is no --force and no manifest override, and no environment variable
# that excuses anything. TRUST_PUSHED_REFS chooses WHICH trees are judged, never
# how: every tree it names is held to its own committed ledgers, and under
# both scripts/hooks/pre-push and scripts/hooks-pin/pre-push the hook itself
# sets it from git's stdin, overwriting whatever the caller's environment
# held. (Until 2026-09-28 scripts/hooks-pin/pre-push did not pass it, so under
# that hook a value inherited from the caller's environment was read; it now
# passes TRUST_PUSHED_REFS="$PUSHED_REFS", as its reach and skew lanes
# already did.) The selftest builds its own scratch
# repository and runs this gate INSIDE it, exactly as a user would, rather than
# re-pointing this one — so "point the gate at a different manifest" is not a
# code path that exists. Git's own `--no-verify` remains, and it shows up in
# the reflog rather than in a habit.
#
#   scripts/check_frozen_files.sh              # the gate
#   scripts/check_frozen_files.sh --check-source # same gate, original citation reader
#   scripts/check_frozen_files.sh --print      # pinned vs HEAD vs worktree
#   scripts/check_frozen_files.sh --selftest   # mutation-proof the gate itself
#
# Exit 0 = in every judged tree, every frozen file is at its pin or moved with
#          a waiver IN THAT TREE naming that exact blob and stating its delta
#          from the pin (or, in push context,
#          no tree lands — only deletions, or nothing: `SKIPPED: `).
#          1 = a frozen file moved and nobody wrote it down, or a git read
#          failed. 2 = the gate could
#          not tell what to judge (a malformed push line, an unpeelable sha, a
#          HEAD that does not resolve, no git worktree).
set -uo pipefail

# ---------------------------------------------------------------------------
# Scratch: ledgers and cited files read out of git objects land here, never in
# a fixed /tmp name. Removed on exit together with the selftest's repository.
# ---------------------------------------------------------------------------
FG_TMP=""
SELFTEST_TMP=""
selftest_cleanup() { [ -n "${SELFTEST_TMP:-}" ] && rm -rf "$SELFTEST_TMP"; return 0; }
fg_cleanup() { [ -n "${FG_TMP:-}" ] && rm -rf "$FG_TMP"; selftest_cleanup; }

fg_tmp_init() {
  [ -n "$FG_TMP" ] && return 0
  FG_TMP="$(mktemp -d "${TMPDIR:-/tmp}/freeze-gate.XXXXXX")" || {
    echo "freeze-gate: cannot create a scratch directory — refusing" >&2
    FG_TMP=""
    return 2
  }
}

# Strict data transport only. A failure leaves the caller on its original
# reader; neither partial output nor a successful source build is a verdict.
FG_CITATION_FACTS=()
# Select an implementation, never a verdict or a different subject. The source
# reader below is also the existing fallback when compiled facts are unavailable.
FG_CITATION_READER=auto
read_citation_facts() {
  local file="$1" count="$2" header="" fact="" valid=1 disallowed
  FG_CITATION_FACTS=()
  # Bash read discards NULs on some versions. Admit bytes before reading lines.
  disallowed="$(LC_ALL=C tr -d '\012\040\055\060-\071\141-\172' < "$file" | wc -c)" || return 1
  [ "$disallowed" -eq 0 ] || return 1
  {
    IFS= read -r header || valid=0
    [ "$header" = "trust-oracle-freeze-facts-v1 $count" ] || valid=0
    while IFS= read -r fact; do
      case "$fact" in test|not-file|missing-test|git-error) ;; *) valid=0 ;; esac
      FG_CITATION_FACTS+=("$fact")
      if [ "${#FG_CITATION_FACTS[@]}" -gt "$count" ]; then valid=0; break; fi
    done
    [ -z "$fact" ] || valid=0  # reject an unterminated final row
  } < "$file"
  [ "$valid" -eq 1 ] && [ "${#FG_CITATION_FACTS[@]}" -eq "$count" ]
}

# ---------------------------------------------------------------------------
# tree_entry <root> <commit> <relpath>
#   0 -> <relpath> is a FILE (a blob) in <commit>'s tree; its sha1 is in TE_OID
#   1 -> it is ABSENT there, or is not a file (a directory, a gitlink)
#   2 -> git failed: the commit or its tree could not be read
# Absent and failed are different answers; see "ABSENT IS A MOVE" in the header.
# `ls-tree` exits 0 with no output for an absent path and non-zero when it
# cannot read the tree, which is exactly the split `rev-parse <c>:<path>` loses.
# ---------------------------------------------------------------------------
tree_entry() {
  local root="$1" commit="$2" rel="$3" out line meta name mode type oid
  TE_OID=""
  out="$(git -C "$root" ls-tree -z --full-tree "$commit" -- "$rel" 2>/dev/null </dev/null | tr '\0' '\n')" || return 2
  [ -n "$out" ] || return 1
  line="${out%%$'\n'*}"
  meta="${line%%$'\t'*}"
  name="${line#*$'\t'}"
  [ "$name" = "$rel" ] || return 1
  read -r mode type oid <<< "$meta"
  [ "$type" = blob ] && [ -n "$oid" ] || return 1
  TE_OID="$oid"
  return 0
}

# ---------------------------------------------------------------------------
# A SIDE is one tree judged whole: SIDE_COMMIT names a commit, or is "" for
# the working tree under SIDE_ROOT. Both helpers answer 0 / 1 absent / 2 failed.
#   side_blob <relpath>          -> SB_OID
#   side_cat  <relpath> <dest>   -> the file's bytes in <dest>
# ---------------------------------------------------------------------------
SIDE_ROOT=""
SIDE_COMMIT=""
SIDE_N=0
side_blob() {
  local rel="$1" rc
  SB_OID=""
  if [ -z "$SIDE_COMMIT" ]; then
    [ -f "$SIDE_ROOT/$rel" ] || return 1
    SB_OID="$(git -C "$SIDE_ROOT" hash-object -- "$SIDE_ROOT/$rel" 2>/dev/null </dev/null)" || return 2
    [ -n "$SB_OID" ] || return 2
    return 0
  fi
  tree_entry "$SIDE_ROOT" "$SIDE_COMMIT" "$rel"; rc=$?
  SB_OID="$TE_OID"
  return "$rc"
}

side_cat() {
  local rel="$1" dest="$2" rc
  if [ -z "$SIDE_COMMIT" ]; then
    [ -f "$SIDE_ROOT/$rel" ] || return 1
    cat -- "$SIDE_ROOT/$rel" > "$dest" 2>/dev/null || return 2
    return 0
  fi
  tree_entry "$SIDE_ROOT" "$SIDE_COMMIT" "$rel"; rc=$?
  [ "$rc" -eq 0 ] || return "$rc"
  git -C "$SIDE_ROOT" cat-file blob "$TE_OID" > "$dest" 2>/dev/null </dev/null || return 2
}

# Strip Rust LINE comments and trailing whitespace. ADVISORY ONLY — see the
# header. Never consulted for the verdict.
strip_line_comments() {
  sed -E 's/[[:space:]]+$//' | grep -vE '^[[:space:]]*//'
}

# test_fn_exists <file> <ident>  -> 0 iff <file> has `fn <ident>(` preceded,
# within six lines (attributes may stack), by a `#[test]` attribute. A plain
# fn of that name is NOT a witness: nothing executes it.
test_fn_exists() {
  awk -v want="$2" '
    /^[[:space:]]*#\[test\]/ { armed = NR; next }
    # An attribute attaches to the NEXT fn only: every fn line consumes it.
    /^[[:space:]]*(pub(\([a-z]+\))? )?fn / {
      if (armed && NR - armed <= 6 &&
          $0 ~ ("^[[:space:]]*(pub(\\([a-z]+\\))? )?fn " want "[[:space:]]*\\(")) {
        found = 1; exit
      }
      armed = 0
    }
    END { exit !found }
  ' "$1"
}

# citations_of <reason> -> one `path::fn` per line, from every
# `ENFORCED-BY: a::f, b::g` clause in the reason. Empty when there is none.
citations_of() {
  printf '%s' "$1" \
    | grep -oE 'ENFORCED-BY:[[:space:]]*[A-Za-z0-9_./-]+::[A-Za-z0-9_]+([[:space:]]*,[[:space:]]*[A-Za-z0-9_./-]+::[A-Za-z0-9_]+)*' \
    | sed -E 's/^ENFORCED-BY:[[:space:]]*//' \
    | tr ',' '\n' \
    | sed -E 's/^[[:space:]]+//; s/[[:space:]]+$//' \
    | grep -v '^$' || true
}

# pin_delta <pin-blob> <relpath> <tag>  -> 0 with PD_ADD / PD_DEL set to the
# lines <relpath> in the judged side adds and deletes against <pin-blob>; 2 when
# git fails (the pin object is missing, the side cannot be read, diff errors).
#
# The measurement is `git diff --numstat --diff-algorithm=myers <pin> <blob>`,
# spelled out and never left to configuration: numstat counts depend on the diff
# algorithm (measured 2026-09-28 on crate_module.rs 135ad7b0 -> e2216c1754, the
# ratified move: myers +7737/-832, histogram +7389/-484), so a `diff.algorithm` setting in a
# writer's or a pusher's git config would otherwise decide the verdict. It diffs
# FILE CONTENTS (--no-index over two scratch copies) because a working-tree side
# carries blobs git has hashed but never stored; the counts are the ones the
# blob-to-blob command prints for the same two texts.
pin_delta() {
  local pin="$1" rel="$2" tag="$3" a b out rc
  PD_ADD=""
  PD_DEL=""
  a="$FG_TMP/$tag.pd_pin"
  b="$FG_TMP/$tag.pd_side"
  git -C "$SIDE_ROOT" cat-file blob "$pin" > "$a" 2>/dev/null </dev/null || return 2
  side_cat "$rel" "$b" || return 2
  out="$(git -C "$SIDE_ROOT" diff --no-index --no-ext-diff --no-textconv --numstat \
           --diff-algorithm=myers -- "$a" "$b" 2>/dev/null </dev/null)"
  rc=$?
  # --no-index exits 1 when the files differ, which is the expected case here.
  [ "$rc" -le 1 ] || return 2
  if [ -z "$out" ]; then
    PD_ADD=0
    PD_DEL=0
    return 0
  fi
  read -r PD_ADD PD_DEL _ <<< "$out"
  case "$PD_ADD" in ''|*[!0-9]*) return 2 ;; esac
  case "$PD_DEL" in ''|*[!0-9]*) return 2 ;; esac
  return 0
}

# check_pin_delta <label> <path> <waived-blob> <pin-blob> <reason>  -> 0 / 1
#
# A live waiver row must carry exactly one `PIN-DELTA: +A/-D` clause, and A/D
# must be what the waived blob adds/deletes against THE PIN in the judged
# tree's own manifest. See "THE PIN-RELATIVE DELTA" in the header.
check_pin_delta() {
  local label="$1" path="$2" wblob="$3" wpin="$4" wreason="$5" clauses count claim
  clauses="$(printf '%s' "$wreason" | grep -oE 'PIN-DELTA:[[:space:]]*\+[0-9]+/-[0-9]+' || true)"
  count=0
  [ -z "$clauses" ] || count="$(printf '%s\n' "$clauses" | wc -l | tr -d '[:space:]')"
  if ! pin_delta "$wpin" "$path" "pd$SIDE_N"; then
    echo "  GIT ERROR could not measure $path against its pin ${wpin:0:12} in $label (PIN-DELTA)"
    return 1
  fi
  if [ "$count" -eq 0 ]; then
    echo "  NO-DELTA  $path  $wblob"
    echo "            a live waiver must state its delta FROM THE PIN (${wpin:0:12}), measured:"
    echo "              PIN-DELTA: +$PD_ADD/-$PD_DEL"
    echo "            and its account must cover that whole delta, not only the last increment"
    return 1
  fi
  if [ "$count" -gt 1 ]; then
    echo "  PIN-DELTA $path  $wblob"
    echo "            carries $count PIN-DELTA clauses; a row states ONE delta, from the pin"
    return 1
  fi
  claim="${clauses#PIN-DELTA:}"
  claim="${claim#"${claim%%[![:space:]]*}"}"
  if [ "$claim" != "+$PD_ADD/-$PD_DEL" ]; then
    echo "  PIN-DELTA $path  $wblob"
    echo "            the row says PIN-DELTA: $claim, but against the pin (${wpin:0:12}) this blob is"
    echo "            +$PD_ADD/-$PD_DEL (git diff --numstat --diff-algorithm=myers ${wpin:0:12} ${wblob:0:12})."
    echo "            A delta from an EARLIER WAIVER is not a delta from the pin: the account must"
    echo "            cover every line the pin does not carry."
    return 1
  fi
  echo "  PIN-DELTA $path  +$PD_ADD/-$PD_DEL from the pin ${wpin:0:12} (matches the row)"
  return 0
}

# ---------------------------------------------------------------------------
# judge_side <root> <commit-or-""> <label>  -> 0 GREEN, 1 RED, 2 no scratch
#
# Judges ONE tree whole: its frozen files against ITS manifest, ITS waivers,
# and the files ITS citations name. Every `while read` also takes a last line
# with no trailing newline (`|| [ -n ... ]`): without that, a ledger whose final
# row lacked one silently lost that row, and a manifest of one such row read as
# "GREEN — 0 frozen file(s)".
# ---------------------------------------------------------------------------
# FINDING KEYS (2026-10-24, docs/DECISION_QUEUE.md INHERITED-RED). A red cause
# that is a property of the judged tree alone prints `FINDING: <key>` (the key
# names the path and the blobs, so the same red read from two trees gives the
# same key, and a blob the push moved again gives a new one). Every other red
# cause (a git error, a citation, a ratchet, a PIN-DELTA) sets FG_UNKEYED, and
# `FINDINGS: complete` is printed only when no cause was unkeyed: the pre-push
# hook grades a red INHERITED only from a complete set (scripts/hooks/pre-push).
FG_UNKEYED=0
keyed_red() {
  failed=1
  echo "FINDING: $1"
}

T_CHECKED=0
T_WAIVED=0
T_CITED=0
T_PROSE=0
T_RESIDUAL=0
JUDGED=0
JUDGED_LABELS=""

judge_side() {
  SIDE_ROOT="$1"
  SIDE_COMMIT="$2"
  local label="$3" failed=0 checked=0 waived=0 prose_only=0 prose_residual=0 cited=0 rc n
  fg_tmp_init || { FG_UNKEYED=1; return 2; }
  SIDE_N=$((SIDE_N + 1))
  n="$SIDE_N"
  local manifest="$FG_TMP/$n.manifest" waivers="$FG_TMP/$n.waivers"
  JUDGED=$((JUDGED + 1))
  JUDGED_LABELS="${JUDGED_LABELS:+$JUDGED_LABELS; }$label"
  echo "--- $label ---"

  side_cat scripts/frozen-files.txt "$manifest"; rc=$?
  if [ "$rc" -eq 1 ]; then
    echo "  NO MANIFEST scripts/frozen-files.txt is not a file in $label: a tree with no"
    echo "            manifest freezes nothing, and one that deleted it escapes the freeze"
    keyed_red "NO-MANIFEST scripts/frozen-files.txt"
    # Waivers and citations below were not visited; this is not a complete set
    # of findings that the push hook can safely inherit from the destination.
    FG_UNKEYED=1
    return 1
  elif [ "$rc" -ne 0 ]; then
    echo "  GIT ERROR could not read scripts/frozen-files.txt from $label"
    FG_UNKEYED=1
    return 1
  fi
  side_cat scripts/frozen-waivers.txt "$waivers"; rc=$?
  if [ "$rc" -eq 1 ]; then
    : > "$waivers"          # PROVEN absent: an empty waiver set
  elif [ "$rc" -ne 0 ]; then
    echo "  GIT ERROR could not read scripts/frozen-waivers.txt from $label"
    FG_UNKEYED=1
    return 1
  fi

  # --- the frozen files -----------------------------------------------------
  local path pin rule reason moved found wrow wblob wdate wcommits wreason
  local -a manifest_paths=() manifest_pins=()
  while IFS='|' read -r path pin rule reason || [ -n "$path" ]; do
    case "$path" in ''|\#*) continue ;; esac
    manifest_paths+=("$path")
    manifest_pins+=("$pin")
    checked=$((checked + 1))

    side_blob "$path"; rc=$?
    if [ "$rc" -eq 1 ]; then
      echo "  DELETED   $path"
      echo "            the frozen path is not a file in $label; a deletion or a rename is a"
      echo "            move, not an exemption"
      keyed_red "DELETED $path"
      continue
    elif [ "$rc" -ne 0 ]; then
      echo "  GIT ERROR could not read $path from $label"
      failed=1; FG_UNKEYED=1
      continue
    fi
    moved="$SB_OID"

    if [ "$moved" = "$pin" ]; then
      echo "  PINNED    $path  $pin"
      continue
    fi

    # Moved. Is there a waiver IN THIS TREE naming EXACTLY this blob?
    found=0
    while IFS='|' read -r wrow wblob wdate wcommits wreason || [ -n "$wrow" ]; do
      case "$wrow" in ''|\#*) continue ;; esac
      if [ "$wrow" = "$path" ] && [ "$wblob" = "$moved" ]; then
        found=1
        break
      fi
    done < "$waivers"
    if [ "$found" -eq 1 ]; then
      echo "  WAIVED    $path  $moved"
      echo "            $wdate  $wcommits"
      echo "            ${wreason:0:160}"
      waived=$((waived + 1))
      continue
    fi
    keyed_red "MOVED $path $pin $moved"
    echo "  MOVED     $path"
    echo "            pinned   $pin"
    echo "            now      $moved"
    echo "            NO WAIVER in $label names this blob. The freeze is not a style rule:"
    echo "            this file is part of the oracle ($rule)."
    # Advisory only.
    if git -C "$SIDE_ROOT" cat-file -p "$pin" 2>/dev/null </dev/null | strip_line_comments > "$FG_TMP/$n.adv_a" &&
       side_cat "$path" "$FG_TMP/$n.adv_raw" &&
       strip_line_comments < "$FG_TMP/$n.adv_raw" > "$FG_TMP/$n.adv_b"; then
      if cmp -s "$FG_TMP/$n.adv_a" "$FG_TMP/$n.adv_b"; then
        echo "            ADVISORY: line-comment-only change (NOT a pass; strip is not a lexer)."
      fi
    fi
    local fix_delta="PIN-DELTA: +<added>/-<deleted>"
    if pin_delta "$pin" "$path" "fix$n"; then
      fix_delta="PIN-DELTA: +$PD_ADD/-$PD_DEL"
    fi
    echo "            Fix: add a row to scripts/frozen-waivers.txt, and commit it with the move —"
    echo "              $path|$moved|$(date -u +%Y-%m-%d)|<commit>|<why this only SAMPLES MORE or REFUSES MORE, over the WHOLE delta from the pin> $fix_delta"
  done < "$manifest"

  if [ "$checked" -eq 0 ]; then
    echo "  EMPTY     scripts/frozen-files.txt in $label freezes no file: a manifest with no"
    echo "            rows is not a pass, it is a freeze that was switched off"
    failed=1; FG_UNKEYED=1
  fi

  # --- waivers that should not exist ---------------------------------------
  local known cur wpin i
  while IFS='|' read -r wrow wblob wdate wcommits wreason || [ -n "$wrow" ]; do
    case "$wrow" in ''|\#*) continue ;; esac
    known=0
    wpin=""
    for i in "${!manifest_paths[@]}"; do
      if [ "${manifest_paths[$i]}" = "$wrow" ]; then
        known=1
        wpin="${manifest_pins[$i]}"
        break
      fi
    done
    if [ "$known" -eq 0 ]; then
      echo "  ORPHAN    $wrow  $wblob"
      echo "            waives a path that is not in scripts/frozen-files.txt; a waiver against"
      echo "            nothing is a waiver nobody reviews. Remove it, or freeze the file."
      keyed_red "ORPHAN $wrow $wblob"
      continue
    fi
    side_blob "$wrow"; rc=$?
    if [ "$rc" -eq 2 ]; then
      echo "  GIT ERROR could not read $wrow from $label"
      failed=1; FG_UNKEYED=1
      continue
    fi
    cur="$SB_OID"
    if [ "$wblob" != "$cur" ]; then
      echo "  SPENT     $wrow  $wblob"
      echo "            $label does not carry this blob, so this waiver documents nothing"
      echo "            there. Delete it. (A waiver must not outlive its change — the same rule"
      echo "            scripts/hooks-pin/pin-waivers.txt applies to submodule drift.)"
      keyed_red "SPENT $wrow $wblob"
    elif [ "$wblob" = "$wpin" ]; then
      echo "  SPENT     $wrow  $wblob"
      echo "            this blob IS the pin in $label's own manifest: the movement was ratified,"
      echo "            so this waiver documents nothing. Delete it (scripts/frozen-files.txt, step 3)."
      keyed_red "SPENT $wrow $wblob"
    else
      # A LIVE row: it must state the delta from THE PIN, not from the last waiver.
      # See "THE PIN-RELATIVE DELTA" in the header.
      check_pin_delta "$label" "$wrow" "$wblob" "$wpin" "$wreason" || { failed=1; FG_UNKEYED=1; }
    fi
  done < "$waivers"

  # --- what backs each waiver's refinement claim ----------------------------
  # See "WHAT BACKS THE CLAIM" in the header. Every ENFORCED-BY citation must
  # resolve to a #[test] fn IN THIS TREE; rows with none are PROSE-ONLY and
  # ratcheted by `# prose-only-max: N` when THIS TREE's waivers file carries
  # it. Cited rows that carry a `PROSE-RESIDUAL:` clause are counted and
  # ratcheted the same way, by `# prose-residual-max: N`.
  local cites cite cpath cfn residual cfile="$FG_TMP/$n.cited"
  # Retain the exact citation order and duplicates. Only committed blob/parser
  # facts are shared: all ledger judgments and the mutable-tree reader below
  # remain here. A missing/unsupported native reader runs the real legacy path.
  local -a row_citations=()
  local citation_count=0 row_index=0 fact_index=0 native_facts=0 fact
  local request_file="$FG_TMP/$n.requests" fact_file="$FG_TMP/$n.facts" facts_script
  : > "$request_file"
  while IFS='|' read -r wrow wblob wdate wcommits wreason || [ -n "$wrow" ]; do
    case "$wrow" in ''|\#*) continue ;; esac
    cites="$(citations_of "$wreason")"
    row_citations+=("$cites")
    if [ -n "$SIDE_COMMIT" ]; then
      while IFS= read -r cite; do
        [ -n "$cite" ] || continue
        printf '%s\0%s\0' "${cite%%::*}" "${cite##*::}" >> "$request_file"
        citation_count=$((citation_count + 1))
      done <<< "$cites"
    fi
  done < "$waivers"
  if [ "$citation_count" -gt 0 ] && [ "$FG_CITATION_READER" = auto ]; then
    facts_script="$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)/oracle_freeze_facts.sh"
    if bash "$facts_script" --repo "$SIDE_ROOT" --commit "$SIDE_COMMIT" \
        < "$request_file" > "$fact_file" 2> "$FG_TMP/$n.facts.err" &&
        read_citation_facts "$fact_file" "$citation_count"; then
      native_facts=1
    fi
    if [ "$native_facts" -ne 1 ]; then
      echo "freeze-gate: compiled citation facts unavailable; checking with the original reader" >&2
      FG_CITATION_FACTS=()
    fi
  fi
  while IFS='|' read -r wrow wblob wdate wcommits wreason || [ -n "$wrow" ]; do
    case "$wrow" in ''|\#*) continue ;; esac
    cites="${row_citations[$row_index]}"
    row_index=$((row_index + 1))
    if [ -z "$cites" ]; then
      prose_only=$((prose_only + 1))
      echo "  PROSE-ONLY $wrow  $wblob"
      echo "            no ENFORCED-BY citation: nothing that executes backs this row's refinement claim"
      continue
    fi
    if [[ "$wreason" == *"PROSE-RESIDUAL:"* ]]; then
      residual="${wreason#*PROSE-RESIDUAL:}"
      residual="${residual%%ENFORCED-BY:*}"
      residual="${residual#"${residual%%[![:space:]]*}"}"
      prose_residual=$((prose_residual + 1))
      echo "  PROSE-RESIDUAL $wrow  $wblob"
      echo "            cited, but part of its claim is executed by nothing: ${residual:0:160}"
    fi
    while IFS= read -r cite; do
      [ -n "$cite" ] || continue
      cpath="${cite%%::*}"
      cfn="${cite##*::}"
      fact=""
      if [ "$native_facts" -eq 1 ]; then
        fact="${FG_CITATION_FACTS[$fact_index]}"
        fact_index=$((fact_index + 1))
        case "$fact" in not-file) rc=1 ;; git-error) rc=2 ;; *) rc=0 ;; esac
      else
        side_cat "$cpath" "$cfile"; rc=$?
      fi
      if [ "$rc" -eq 1 ]; then
        echo "  UNRESOLVED $wrow  cites $cite"
        echo "            $cpath is not a file in $label: a citation to nothing is a claim that has rotted"
        failed=1; FG_UNKEYED=1
        continue
      elif [ "$rc" -ne 0 ]; then
        echo "  GIT ERROR could not read $cpath from $label (cited by $wrow)"
        failed=1; FG_UNKEYED=1
        continue
      fi
      if { [ "$native_facts" -eq 1 ] && [ "$fact" = missing-test ]; } ||
         { [ "$native_facts" -ne 1 ] && ! test_fn_exists "$cfile" "$cfn"; }; then
        echo "  UNRESOLVED $wrow  cites $cite"
        echo "            $cpath in $label carries no #[test] fn $cfn: a test that does not exist fails nothing"
        failed=1; FG_UNKEYED=1
        continue
      fi
      cited=$((cited + 1))
      echo "  ENFORCED  $wrow  $cite"
    done <<< "$cites"
  done < "$waivers"
  local ratchet
  ratchet="$(grep -oE '^# prose-only-max: [0-9]+' "$waivers" | head -1 | grep -oE '[0-9]+$' || true)"
  if [ -n "$ratchet" ] && [ "$prose_only" -ne "$ratchet" ]; then
    echo "  RATCHET   prose-only rows: measured $prose_only, scripts/frozen-waivers.txt says $ratchet"
    if [ "$prose_only" -gt "$ratchet" ]; then
      echo "            a row without an ENFORCED-BY citation was added: cite the test that fails if its"
      echo "            claim is false, or raise the number in a commit that says why it cannot be tested"
    else
      echo "            fewer prose-only rows than the ledger records: write the smaller number down"
    fi
    failed=1; FG_UNKEYED=1
  fi
  local residual_ratchet
  residual_ratchet="$(grep -oE '^# prose-residual-max: [0-9]+' "$waivers" | head -1 | grep -oE '[0-9]+$' || true)"
  if [ -n "$residual_ratchet" ] && [ "$prose_residual" -ne "$residual_ratchet" ]; then
    echo "  RATCHET   prose-residual rows: measured $prose_residual, scripts/frozen-waivers.txt says $residual_ratchet"
    if [ "$prose_residual" -gt "$residual_ratchet" ]; then
      echo "            a cited row now declares a part of its claim nothing executes: back that part"
      echo "            with a test, or raise the number in a commit that says why it cannot be tested"
    else
      echo "            fewer prose-residual rows than the ledger records: write the smaller number down"
    fi
    failed=1; FG_UNKEYED=1
  fi

  T_CHECKED=$((T_CHECKED + checked))
  T_WAIVED=$((T_WAIVED + waived))
  T_CITED=$((T_CITED + cited))
  T_PROSE=$((T_PROSE + prose_only))
  T_RESIDUAL=$((T_RESIDUAL + prose_residual))
  if [ "$failed" -eq 0 ]; then
    echo "  => GREEN: $checked frozen file(s), $waived waived, $cited citation(s) resolved, $prose_only prose-only, $prose_residual prose-residual."
    return 0
  fi
  echo "  => RED"
  return 1
}

# ---------------------------------------------------------------------------
# The two readings (see "WHICH TREE IS JUDGED" in the header).
# ---------------------------------------------------------------------------
push_reading() {
  local root="$1" line lref lsha rref rsha rest commit judged=" " rc=0 deletions=0 i
  local -a commits=() labels=()
  while IFS= read -r line || [ -n "$line" ]; do
    case "$line" in *[![:space:]]*) ;; *) continue ;; esac
    lref="" lsha="" rref="" rsha="" rest=""
    read -r lref lsha rref rsha rest <<< "$line"
    if [ -z "$rsha" ] || [ -n "$rest" ]; then
      echo "freeze-gate: a TRUST_PUSHED_REFS line is not '<local-ref> <local-sha> <remote-ref> <remote-sha>':" >&2
      echo "freeze-gate:   $line" >&2
      echo "freeze-gate: cannot tell what this push lands, so it is not judged at all — refusing" >&2
      return 2
    fi
    case "$lsha" in
      *[!0]*) ;;
      *) deletions=$((deletions + 1)); continue ;;   # a deletion lands no tree
    esac
    commit="$(git -C "$root" rev-parse --verify --quiet "$lsha^{commit}" 2>/dev/null </dev/null)" || commit=""
    if [ -z "$commit" ]; then
      echo "freeze-gate: pushed $lref ($lsha) does not peel to a commit in this repository —" >&2
      echo "freeze-gate: its tree cannot be judged — refusing" >&2
      return 2
    fi
    case "$judged" in *" $commit "*) continue ;; esac
    judged="$judged$commit "
    commits+=("$commit")
    labels+=("pushed $lref -> $rref (commit $commit)")
  done <<< "$TRUST_PUSHED_REFS"

  if [ "${#commits[@]}" -eq 0 ]; then
    echo "SUBJECT: the pushed refs (TRUST_PUSHED_REFS): $deletions deletion(s) and no update — no tree lands"
    if [ "$deletions" -gt 0 ]; then
      echo "SKIPPED: this push only deletes refs; there is no pushed tree to judge"
    else
      echo "SKIPPED: TRUST_PUSHED_REFS is set but names no ref (git runs pre-push with empty stdin when every ref is already up to date); there is no pushed tree to judge"
    fi
    return 0
  fi
  echo "SUBJECT: the pushed refs (TRUST_PUSHED_REFS, ${#commits[@]} pushed tree(s), $deletions deletion(s)); each pushed commit's own tree, ledgers and citations — the working tree is not pushed and is not read"
  i=0
  while [ "$i" -lt "${#commits[@]}" ]; do
    judge_side "$root" "${commits[$i]}" "${labels[$i]}" || rc=1
    i=$((i + 1))
  done
  return "$rc"
}

standing_reading() {
  local root="$1" why="$2" head sym rc=0
  if head="$(git -C "$root" rev-parse --verify --quiet 'HEAD^{commit}' 2>/dev/null </dev/null)" && [ -n "$head" ]; then
    echo "SUBJECT: HEAD ($head) and the working tree, each judged whole — $why"
    judge_side "$root" "$head" "HEAD ($head)" || rc=1
  elif sym="$(git -C "$root" symbolic-ref -q HEAD 2>/dev/null </dev/null)" &&
       ! git -C "$root" rev-parse --verify --quiet "$sym" >/dev/null 2>&1 </dev/null; then
    echo "SUBJECT: the working tree alone — HEAD ($sym) is unborn, nothing is committed; $why"
  else
    echo "freeze-gate: HEAD does not resolve to a commit and is not unborn — refusing" >&2
    return 2
  fi
  judge_side "$root" "" "the working tree" || rc=1
  return "$rc"
}

# ---------------------------------------------------------------------------
# --print
# ---------------------------------------------------------------------------
do_print() {
  local root="$1" manifest="$2" h w
  printf '%-52s %-42s %-42s %s\n' FILE PINNED HEAD WORKTREE
  local path pin rule reason
  SIDE_ROOT="$root"
  while IFS='|' read -r path pin rule reason || [ -n "$path" ]; do
    case "$path" in ''|\#*) continue ;; esac
    SIDE_COMMIT=HEAD
    if side_blob "$path"; then h="$SB_OID"; else h="<absent-or-unreadable>"; fi
    SIDE_COMMIT=""
    if side_blob "$path"; then w="$SB_OID"; else w="<absent-or-unreadable>"; fi
    printf '%-52s %-42s %-42s %s\n' "$(basename "$path")" "$pin" "$h" "$w"
  done < "$manifest"
}

# ---------------------------------------------------------------------------
# --selftest — the MUTATION PROOF.
#
# A gate that has never been seen to fail is a gate nobody has tested. This
# builds a scratch repository, plants distinct defects, and asserts the verdict
# each time — in the standing reading by running the gate inside that
# repository, and in push context through REAL `git push`es to a scratch bare
# remote whose pre-push hook exports TRUST_PUSHED_REFS the way
# scripts/hooks/pre-push does. It touches nothing outside its own mktemp
# directory and it runs THIS script, not a copy.
# ---------------------------------------------------------------------------
selftest() {
  local me tmp rc pass=0 fail=0 base
  me="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/$(basename "${BASH_SOURCE[0]}")"
  # A selftest run from inside a git hook must not inherit that hook's
  # repository: every git call below is about the scratch repository only.
  unset GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY \
        GIT_ALTERNATE_OBJECT_DIRECTORIES GIT_COMMON_DIR GIT_PREFIX GIT_NAMESPACE
  tmp="$(mktemp -d "${TMPDIR:-/tmp}/freeze-selftest.XXXXXX")" || return 2
  SELFTEST_TMP="$tmp"

  local bad_fact
  printf 'trust-oracle-freeze-facts-v1 2\ntest\ntest\n' > "$tmp/facts"
  if read_citation_facts "$tmp/facts" 2 && [ "${#FG_CITATION_FACTS[@]}" -eq 2 ]; then
    echo "  PASS  exact native facts retain duplicate classifications"; pass=$((pass + 1))
  else
    echo "  FAIL  exact native facts rejected"; fail=$((fail + 1))
  fi
  if (tr() { return 1; }; read_citation_facts "$tmp/facts" 2); then
    echo "  FAIL  byte-admission read error accepted"; fail=$((fail + 1))
  else
    echo "  PASS  byte-admission read error uses the original reader"; pass=$((pass + 1))
  fi
  for bad_fact in \
    'trust-oracle-freeze-facts-v1 1\nte\0st\n' \
    'trust-oracle-freeze-facts-v1 1\ntest' \
    'trust-oracle-freeze-facts-v1 1\ntest\ntest\n' \
    'trust-oracle-freeze-facts-v1 1\nunknown\n' \
    'trust-oracle-freeze-facts-v2 1\ntest\n'; do
    printf '%b' "$bad_fact" > "$tmp/facts"
    if read_citation_facts "$tmp/facts" 1; then
      echo "  FAIL  malformed native fact transport accepted"; fail=$((fail + 1))
    else
      echo "  PASS  malformed native fact transport uses the original reader"; pass=$((pass + 1))
    fi
  done

  mkdir -p "$tmp/repo/src" "$tmp/repo/scripts" "$tmp/hooks"
  git init -q --bare "$tmp/remote.git" || return 2
  cd "$tmp/repo" || return 2
  git init -q . || return 2
  git symbolic-ref HEAD refs/heads/main
  git config user.email selftest@localhost
  git config user.name selftest
  git config commit.gpgsign false
  git config tag.gpgsign false
  git config core.hooksPath "$tmp/hooks"
  git remote add origin "$tmp/remote.git"
  # The fixture's pre-push hook: git's stdin exported as TRUST_PUSHED_REFS,
  # then this gate — the same wiring as scripts/hooks/pre-push.
  cat > "$tmp/hooks/pre-push" <<HOOK
#!/usr/bin/env bash
TRUST_PUSHED_REFS="\$(cat)"
export TRUST_PUSHED_REFS
bash "$me" > "$tmp/hook.out" 2>&1
HOOK
  chmod +x "$tmp/hooks/pre-push"

  printf 'fn oracle() -> bool {\n    // the comparison\n    true\n}\n' > src/frozen.rs
  printf 'fn other() {}\n' > src/loose.rs
  local PIN
  PIN="$(git hash-object src/frozen.rs)"
  printf 'src/frozen.rs|%s|BYTE-IDENTICAL|selftest fixture\n' "$PIN" > scripts/frozen-files.txt
  : > scripts/frozen-waivers.txt
  git add -A >/dev/null
  git commit -qm baseline >/dev/null
  base="$(git rev-parse HEAD)"

  local M="$tmp/repo/scripts/frozen-files.txt" W="$tmp/repo/scripts/frozen-waivers.txt"
  local MOVE='fn oracle() -> bool {\n    // the comparison\n    false\n}\n'
  local TESTS='#[test]\nfn the_pin_holds() {}\n\nfn not_a_test() {}\n'

  expect() { # expect <want-rc> <label>   — the STANDING reading, run in the repo
    local want="$1" label="$2" got
    (cd "$tmp/repo" && env -u TRUST_PUSHED_REFS bash "$me") >"$tmp/out" 2>&1
    got=$?
    if [ "$got" -eq "$want" ]; then
      echo "  PASS  $label (rc=$got)"; pass=$((pass + 1))
    else
      echo "  FAIL  $label (want rc=$want, got rc=$got)"; sed 's/^/        /' "$tmp/out"; fail=$((fail + 1))
    fi
  }
  expect_refs() { # expect_refs <want-rc> <label> <TRUST_PUSHED_REFS>
    local want="$1" label="$2" got
    (cd "$tmp/repo" && TRUST_PUSHED_REFS="$3" bash "$me") >"$tmp/out" 2>&1
    got=$?
    if [ "$got" -eq "$want" ]; then
      echo "  PASS  $label (rc=$got)"; pass=$((pass + 1))
    else
      echo "  FAIL  $label (want rc=$want, got rc=$got)"; sed 's/^/        /' "$tmp/out"; fail=$((fail + 1))
    fi
  }
  push_expect() { # push_expect accepted|refused <label> <git push args...>
    local want="$1" label="$2" got=accepted
    shift 2
    : > "$tmp/hook.out"
    git push -q -f origin "$@" >"$tmp/push.out" 2>&1 || got=refused
    if [ "$got" = refused ] && ! grep -q 'FREEZE GATE: RED' "$tmp/hook.out"; then
      got="refused-but-not-by-the-gate"
    fi
    if [ "$got" = "$want" ]; then
      echo "  PASS  $label ($got)"; pass=$((pass + 1))
    else
      echo "  FAIL  $label (want $want, got $got)"
      sed 's/^/        push: /' "$tmp/push.out"; sed 's/^/        gate: /' "$tmp/hook.out"
      fail=$((fail + 1))
    fi
  }
  out_has() { # out_has <label> <ERE>: the last reading printed a line matching it
    if grep -qE -- "$2" "$tmp/out"; then
      echo "  PASS  $1"; pass=$((pass + 1))
    else
      echo "  FAIL  $1 (no line matches /$2/)"; sed 's/^/        /' "$tmp/out"; fail=$((fail + 1))
    fi
  }
  out_lacks() { # out_lacks <label> <ERE>: the last reading printed no such line
    if grep -qE -- "$2" "$tmp/out"; then
      echo "  FAIL  $1 (a line matches /$2/)"; sed 's/^/        /' "$tmp/out"; fail=$((fail + 1))
    else
      echo "  PASS  $1"; pass=$((pass + 1))
    fi
  }
  fresh() { # back to the committed baseline on main, nothing untracked
    git checkout -q -f main && git reset -q --hard "$base" && git clean -qfdx
  }

  echo "=== freeze-gate selftest ==="
  echo "--- standing reading (TRUST_PUSHED_REFS unset): HEAD and the working tree ---"

  # 1. pristine
  expect 0 "pristine tree is GREEN"

  # A missing manifest prevents the remaining waiver/citation checks. It is
  # red, but cannot claim a complete finding set: otherwise the push hook can
  # inherit NO-MANIFEST while additional edits and a broken citation disappear.
  fresh
  rm "$M"
  git add -A && git commit -qm "fixture: missing freeze manifest"
  local missing_base missing_tip extra_blob
  missing_base="$(git rev-parse HEAD)"
  printf "$MOVE" > src/frozen.rs
  extra_blob="$(git hash-object src/loose.rs)"
  printf 'src/loose.rs|%s|2026-01-01|deadbeef|orphan. ENFORCED-BY: src/missing.rs::the_pin_holds\n' "$extra_blob" > "$W"
  expect 1 "missing manifest beside an extra move and broken waiver -> RED"
  out_has "  ... the missing manifest is keyed" "^FINDING: NO-MANIFEST scripts/frozen-files\\.txt\$"
  out_lacks "  ... unvisited checks withhold FINDINGS: complete" "^FINDINGS: complete\$"
  git add -A && git commit -qm "fixture: additional move and broken waiver"
  missing_tip="$(git rev-parse HEAD)"
  expect_refs 1 "pushed missing-manifest tree with additional defects -> RED" \
    "refs/heads/main $missing_tip refs/heads/main $missing_base"
  out_has "  ... pushed missing manifest is keyed" "^FINDING: NO-MANIFEST scripts/frozen-files\\.txt\$"
  out_lacks "  ... pushed incomplete findings cannot be inherited" "^FINDINGS: complete\$"
  fresh

  # 2. a moved frozen file with no waiver
  printf "$MOVE" > src/frozen.rs
  expect 1 "moved frozen file, no waiver -> RED"
  # The red is keyed, so the pre-push hook can compare it with the
  # destination's (INHERITED grading): one FINDING per cause, then the marker.
  out_has "  ... keyed: FINDING: MOVED <path> <pin> <moved blob>" \
    "^FINDING: MOVED src/frozen\.rs $PIN $(git hash-object src/frozen.rs)\$"
  out_has "  ... and every cause is keyed: FINDINGS: complete" "^FINDINGS: complete\$"

  # 3. a waiver naming the WRONG blob does not excuse it
  printf 'src/frozen.rs|%s|2026-01-01|deadbeef|wrong blob\n' \
    "0000000000000000000000000000000000000000" > "$W"
  expect 1 "waiver naming a DIFFERENT blob -> RED (no blanket waivers)"

  # 4. a waiver naming the exact blob does
  printf 'src/frozen.rs|%s|2026-01-01|deadbeef|adjudicated. PIN-DELTA: +1/-1\n' "$(git hash-object src/frozen.rs)" > "$W"
  expect 0 "waiver naming the exact blob -> GREEN"

  # 5. editing again after the waiver was written re-arms the gate
  printf 'fn oracle() -> bool {\n    // the comparison\n    !false\n}\n' > src/frozen.rs
  expect 1 "second edit after a waiver -> RED (the waiver pins one blob)"

  # 6. a waiver that is no longer needed must be deleted
  git checkout -q -- src/frozen.rs
  printf 'src/frozen.rs|%s|2026-01-01|deadbeef|stale\n' \
    "0000000000000000000000000000000000000000" > "$W"
  expect 1 "spent waiver on a pinned file -> RED (delete it)"

  # 7. a waiver for a path nobody froze
  printf 'src/loose.rs|%s|2026-01-01|deadbeef|orphan\n' "$(git hash-object src/loose.rs)" > "$W"
  expect 1 "waiver for an unfrozen path -> RED"

  # 8. THE COMMIT-THEN-RESTORE HOLE: HEAD carries the change, worktree does not
  fresh
  printf "$MOVE" > src/frozen.rs
  git commit -qam "sneak" >/dev/null
  git checkout -q "$base" -- src/frozen.rs
  expect 1 "HEAD moved, worktree restored -> RED (both sides are checked)"

  # 9. a COMMENT-ONLY change is still RED (advisory, never a pass)
  fresh
  printf 'fn oracle() -> bool {\n    // the comparison, restated\n    true\n}\n' > src/frozen.rs
  (cd "$tmp/repo" && env -u TRUST_PUSHED_REFS bash "$me") >"$tmp/out" 2>&1
  rc=$?
  if [ "$rc" -eq 1 ] && grep -q "line-comment-only" "$tmp/out"; then
    echo "  PASS  comment-only change -> RED, and the advisory names it"; pass=$((pass + 1))
  else
    echo "  FAIL  comment-only change (rc=$rc; advisory present: $(grep -c 'line-comment-only' "$tmp/out"))"
    sed 's/^/        /' "$tmp/out"; fail=$((fail + 1))
  fi

  # 10-15. ENFORCED-BY citations must RESOLVE to a #[test] fn, and prose-only
  # rows are ratcheted by `# prose-only-max: N`.
  fresh
  printf "$TESTS" > src/frozen_tests.rs
  printf "$MOVE" > src/frozen.rs
  local MOVED
  MOVED="$(git hash-object src/frozen.rs)"
  printf 'src/frozen.rs|%s|2026-01-01|deadbeef|refuses more. PIN-DELTA: +1/-1. ENFORCED-BY: src/frozen_tests.rs::the_pin_holds\n' "$MOVED" > "$W"
  expect 0 "waiver citing an existing #[test] fn -> GREEN"
  printf 'src/frozen.rs|%s|2026-01-01|deadbeef|refuses more. PIN-DELTA: +1/-1. ENFORCED-BY: src/frozen_tests.rs::not_a_test\n' "$MOVED" > "$W"
  expect 1 "citation naming a fn that is not a #[test] -> RED (nothing executes it)"
  out_lacks "  ... an unkeyed cause (a citation) withholds FINDINGS: complete" "^FINDINGS: complete\$"
  # A keyed cause beside the unkeyed one: the key prints, the marker still not.
  local LOOSE
  LOOSE="$(git hash-object src/loose.rs)"
  printf 'src/frozen.rs|%s|2026-01-01|deadbeef|refuses more. PIN-DELTA: +1/-1. ENFORCED-BY: src/frozen_tests.rs::not_a_test\nsrc/loose.rs|%s|2026-01-01|deadbeef|orphan\n' "$MOVED" "$LOOSE" > "$W"
  expect 1 "an orphan waiver beside an unresolved citation -> RED"
  out_has "  ... keyed: FINDING: ORPHAN <path> <blob>" "^FINDING: ORPHAN src/loose\.rs $LOOSE\$"
  out_lacks "  ... and the unkeyed citation still withholds FINDINGS: complete" "^FINDINGS: complete\$"
  printf 'src/frozen.rs|%s|2026-01-01|deadbeef|refuses more. PIN-DELTA: +1/-1. ENFORCED-BY: src/missing.rs::the_pin_holds\n' "$MOVED" > "$W"
  expect 1 "citation naming a missing file -> RED"
  printf '# prose-only-max: 0\nsrc/frozen.rs|%s|2026-01-01|deadbeef|refuses more, says nobody. PIN-DELTA: +1/-1\n' "$MOVED" > "$W"
  expect 1 "prose-only row above the ratchet -> RED"
  printf '# prose-only-max: 1\nsrc/frozen.rs|%s|2026-01-01|deadbeef|refuses more, says nobody. PIN-DELTA: +1/-1\n' "$MOVED" > "$W"
  expect 0 "prose-only row at the ratchet -> GREEN"
  printf '# prose-only-max: 2\nsrc/frozen.rs|%s|2026-01-01|deadbeef|refuses more, says nobody. PIN-DELTA: +1/-1\n' "$MOVED" > "$W"
  expect 1 "ratchet above the measurement -> RED (write the smaller number down)"

  # 16-18. A cited row that declares a PROSE-RESIDUAL is counted and ratcheted
  # like a prose-only one: a citation does not hide the half nothing executes.
  local CITED_RESIDUAL='refuses more. PIN-DELTA: +1/-1. PROSE-RESIDUAL: the dump arm is argued, not run. ENFORCED-BY: src/frozen_tests.rs::the_pin_holds'
  printf '# prose-residual-max: 0\nsrc/frozen.rs|%s|2026-01-01|deadbeef|%s\n' "$MOVED" "$CITED_RESIDUAL" > "$W"
  expect 1 "cited row with a prose residual above its ratchet -> RED"
  printf '# prose-residual-max: 1\nsrc/frozen.rs|%s|2026-01-01|deadbeef|%s\n' "$MOVED" "$CITED_RESIDUAL" > "$W"
  expect 0 "cited row with a prose residual at its ratchet -> GREEN"
  printf '# prose-residual-max: 2\nsrc/frozen.rs|%s|2026-01-01|deadbeef|%s\n' "$MOVED" "$CITED_RESIDUAL" > "$W"
  expect 1 "prose-residual ratchet above the measurement -> RED"

  # 19. A waiver naming the PIN itself: the movement was ratified by moving the
  # pin and the row was left behind. Before 2026-09-28 this was GREEN.
  git checkout -q -- src/frozen.rs
  printf 'src/frozen.rs|%s|2026-01-01|deadbeef|ratified, row left behind\n' "$PIN" > "$W"
  expect 1 "waiver naming the pinned blob (ratified, not deleted) -> RED"

  # 20-24. THE PIN-RELATIVE DELTA (2026-09-28): a live row states, in ONE
  # `PIN-DELTA: +A/-D` clause, what its blob adds and deletes against THE PIN,
  # and the gate measures it. Every live row above carries +1/-1, which is what
  # $MOVE is against the pin, so each of those cases still isolates its own defect.
  fresh
  printf "$MOVE" > src/frozen.rs
  printf 'src/frozen.rs|%s|2026-01-01|deadbeef|adjudicated, no delta stated\n' "$MOVED" > "$W"
  expect 1 "live waiver with no PIN-DELTA clause -> RED"
  printf 'src/frozen.rs|%s|2026-01-01|deadbeef|adjudicated. PIN-DELTA: +2/-1\n' "$MOVED" > "$W"
  expect 1 "live waiver whose PIN-DELTA disagrees with the measured delta -> RED"
  printf 'src/frozen.rs|%s|2026-01-01|deadbeef|adjudicated. PIN-DELTA: +1/-1, earlier PIN-DELTA: +1/-1\n' "$MOVED" > "$W"
  expect 1 "live waiver with two PIN-DELTA clauses -> RED"
  # The carry-forward break (e621a31544): the file moves AGAIN and the new row
  # accounts for, and counts, only the increment since the last waived blob.
  local AGAIN='fn oracle() -> bool {\n    // the comparison\n    false\n}\nfn guard() {}\n'
  local AGAIN_BLOB
  printf "$AGAIN" > src/frozen.rs
  AGAIN_BLOB="$(git hash-object src/frozen.rs)"
  printf 'src/frozen.rs|%s|2026-01-01|deadbeef|CARRIED FORWARD from the %s row; adds guard. PIN-DELTA: +1/-0\n' \
    "$AGAIN_BLOB" "$MOVED" > "$W"
  expect 1 "carried-forward row counting the increment since the last waiver, not the pin -> RED"
  printf 'src/frozen.rs|%s|2026-01-01|deadbeef|the whole move from the pin: flips the result, adds guard. PIN-DELTA: +2/-1\n' \
    "$AGAIN_BLOB" > "$W"
  expect 0 "the same row stating its delta from the pin -> GREEN"

  # 25-27. HEAD is judged against HEAD's OWN ledgers (FF-2, standing reading).
  fresh
  printf "$MOVE" > src/frozen.rs
  git commit -qam "move, waiver not committed" >/dev/null
  printf 'src/frozen.rs|%s|2026-01-01|deadbeef|written, never committed. PIN-DELTA: +1/-1\n' "$MOVED" > "$W"
  expect 1 "committed move, waiver only in the worktree -> RED (HEAD's own waivers are empty)"
  git checkout -q -- "$W"
  : > "$M"
  expect 1 "committed move, manifest emptied only in the worktree -> RED"
  git checkout -q -- "$M"
  printf 'src/frozen.rs|%s|2026-01-01|deadbeef|written and committed. PIN-DELTA: +1/-1\n' "$MOVED" > "$W"
  git commit -qam "waiver" >/dev/null
  expect 0 "committed move with its committed waiver -> GREEN"

  # 28. a manifest that freezes nothing is not a pass
  fresh
  printf '# only comments\n' > "$M"
  expect 1 "manifest with zero rows (worktree only, nothing moved) -> RED"

  # 29. a final ledger row with no trailing newline is still a row
  fresh
  printf 'src/frozen.rs|%s|BYTE-IDENTICAL|no newline' "$PIN" > "$M"
  git commit -qam "manifest row without a trailing newline" >/dev/null
  printf "$MOVE" > src/frozen.rs
  expect 1 "moved file whose manifest row has no trailing newline -> RED"

  # 30-31. ABSENT AT HEAD IS A MOVE (FF-3): a committed deletion or rename,
  # with a pristine copy left behind in the worktree.
  fresh
  git rm -q --cached src/frozen.rs
  git commit -qm "untrack the oracle, keep the file" >/dev/null
  expect 1 "committed git rm --cached, file left untracked -> RED (absent at HEAD)"
  fresh
  git mv src/frozen.rs src/oracle_v2.rs
  printf 'fn oracle() -> bool {\n    false\n}\n' > src/oracle_v2.rs
  git add -A >/dev/null
  git commit -qm "rename and rewrite the oracle" >/dev/null
  git show "$base:src/frozen.rs" > src/frozen.rs
  expect 1 "committed git mv + rewrite, untracked copy at the old path -> RED"

  # 32-33. HEAD's citations resolve against HEAD's tree (FF-4, standing).
  fresh
  printf "$MOVE" > src/frozen.rs
  printf 'src/frozen.rs|%s|2026-01-01|deadbeef|refuses more. PIN-DELTA: +1/-1. ENFORCED-BY: src/frozen_tests.rs::the_pin_holds\n' "$MOVED" > "$W"
  git commit -qam "move with a cited waiver" >/dev/null
  printf "$TESTS" > src/frozen_tests.rs
  expect 1 "committed cited waiver, cited test file untracked -> RED"
  TARGO="$tmp/absent-native-targo" expect 1 "missing native builder still rejects the uncommitted citation"
  out_has "missing native builder uses the real original reader" '^freeze-gate: compiled citation facts unavailable; checking with the original reader$'
  git add src/frozen_tests.rs && git commit -qm "the cited test" >/dev/null
  expect 0 "committed cited waiver, cited test file committed -> GREEN"
  TARGO="$tmp/absent-native-targo" expect 0 "missing native builder still checks and accepts the committed citation"
  out_has "the accepting fallback also ran the real original reader" '^freeze-gate: compiled citation facts unavailable; checking with the original reader$'

  echo "--- push context: real git pushes through a pre-push hook ---"
  fresh
  push_expect accepted "push of the pristine baseline is accepted" main:main

  # FF-1: what is judged is what is pushed, not HEAD.
  git checkout -q -b bad
  printf "$MOVE" > src/frozen.rs
  git commit -qam "move, no waiver" >/dev/null
  git tag v-bad
  git tag -a -m "annotated" va-bad
  git checkout -q main
  push_expect refused "HEAD pristine, git push origin bad:main -> refused" bad:main
  push_expect refused "lightweight tag of a moved commit -> refused" refs/tags/v-bad
  push_expect refused "annotated tag of a moved commit -> refused" refs/tags/va-bad
  push_expect refused "multi-ref push, one ref moved -> refused" main:ok bad:bad
  git checkout -q bad
  push_expect accepted "HEAD carries an unwaived move, pushing pristine main:x -> accepted" main:clean-copy
  push_expect accepted "a deletion-only push -> accepted" :clean-copy
  if grep -q '^SKIPPED: ' "$tmp/hook.out"; then
    echo "  PASS  a deletion-only push says SKIPPED, not GREEN"; pass=$((pass + 1))
  else
    echo "  FAIL  a deletion-only push did not print SKIPPED"; sed 's/^/        /' "$tmp/hook.out"; fail=$((fail + 1))
  fi

  # FF-5: the worktree is not pushed.
  fresh
  printf 'fn oracle() -> bool {\n    // scratch edit, never committed\n    false\n}\n' > src/frozen.rs
  push_expect accepted "pristine pushed tree, dirty frozen file in the worktree -> accepted" main:ff5-copy
  # Remote main already carries main: git still runs pre-push, with EMPTY stdin.
  push_expect accepted "an up-to-date push (empty stdin), dirty worktree -> accepted" main:main
  if grep -q '^SKIPPED: TRUST_PUSHED_REFS is set but names no ref' "$tmp/hook.out"; then
    echo "  PASS  an up-to-date push says SKIPPED, and does not fall back to the worktree"; pass=$((pass + 1))
  else
    echo "  FAIL  an up-to-date push did not print its SKIPPED line"; sed 's/^/        /' "$tmp/hook.out"; fail=$((fail + 1))
  fi

  # FF-2: the pushed tree's OWN ledgers.
  fresh
  git checkout -q -b w2
  printf "$MOVE" > src/frozen.rs
  git commit -qam "move, waiver not committed" >/dev/null
  printf 'src/frozen.rs|%s|2026-01-01|deadbeef|written, never committed. PIN-DELTA: +1/-1\n' "$MOVED" > "$W"
  push_expect refused "committed move, waiver only in the worktree -> refused" w2:w2
  git checkout -q -- "$W"
  : > "$M"
  push_expect refused "committed move, manifest emptied only in the worktree -> refused" w2:w2
  git checkout -q -- "$M"
  printf 'src/frozen.rs|%s|2026-01-01|deadbeef|written and committed. PIN-DELTA: +1/-1\n' "$MOVED" > "$W"
  git commit -qam "waiver" >/dev/null
  push_expect accepted "committed move with its committed waiver -> accepted" w2:w2

  # FF-3: a pushed tree without the frozen path.
  fresh
  git checkout -q -b rmb
  git rm -q src/frozen.rs
  git commit -qm "delete the oracle" >/dev/null
  git show "$base:src/frozen.rs" > src/frozen.rs
  push_expect refused "pushed tree lacks the frozen path (pristine copy left untracked) -> refused" rmb:rmb

  # FF-4: citations resolve in the pushed tree.
  fresh
  git checkout -q -b cite
  printf "$MOVE" > src/frozen.rs
  printf 'src/frozen.rs|%s|2026-01-01|deadbeef|refuses more. PIN-DELTA: +1/-1. ENFORCED-BY: src/frozen_tests.rs::the_pin_holds\n' "$MOVED" > "$W"
  git commit -qam "move with a cited waiver" >/dev/null
  printf "$TESTS" > src/frozen_tests.rs
  push_expect refused "cited test file untracked, never pushed -> refused" cite:cite
  git add src/frozen_tests.rs && git commit -qm "the cited test" >/dev/null
  push_expect accepted "cited test file committed and pushed -> accepted" cite:cite

  # The prose-residual ratchet and the SPENT-at-the-pin rule, in the pushed
  # tree: its OWN waivers file carries the ratchet, its OWN manifest the pin.
  # Each branch is pushed from a pristine main checkout, so only a gate that
  # reads the pushed tree sees what the branch carries.
  fresh
  git checkout -q -b resid
  printf "$MOVE" > src/frozen.rs
  printf "$TESTS" > src/frozen_tests.rs
  printf '# prose-residual-max: 0\nsrc/frozen.rs|%s|2026-01-01|deadbeef|%s\n' "$MOVED" "$CITED_RESIDUAL" > "$W"
  git add -A >/dev/null && git commit -qm "cited waiver with a residual, ratchet 0" >/dev/null
  git checkout -q main
  push_expect refused "pushed prose residual above its committed ratchet, HEAD pristine -> refused" resid:resid
  git checkout -q resid
  printf '# prose-residual-max: 1\nsrc/frozen.rs|%s|2026-01-01|deadbeef|%s\n' "$MOVED" "$CITED_RESIDUAL" > "$W"
  git commit -qam "ratchet 1" >/dev/null
  push_expect accepted "pushed prose residual at its committed ratchet -> accepted" resid:resid
  printf '# prose-residual-max: 0\nsrc/frozen.rs|%s|2026-01-01|deadbeef|%s\n' "$MOVED" "$CITED_RESIDUAL" > "$W"
  push_expect accepted "committed ratchet holds, worktree ratchet edited (never pushed) -> accepted" resid:resid-copy
  expect 1 "the same worktree ratchet edit, standing reading -> RED (the worktree is judged whole)"
  # The PIN-RELATIVE DELTA in the pushed tree, against the pushed tree's own pin.
  fresh
  git checkout -q -b pd
  printf "$MOVE" > src/frozen.rs
  printf 'src/frozen.rs|%s|2026-01-01|deadbeef|adjudicated, no delta stated\n' "$MOVED" > "$W"
  git commit -qam "move with a waiver that states no delta" >/dev/null
  git checkout -q main
  push_expect refused "pushed live waiver with no PIN-DELTA, HEAD pristine -> refused" pd:pd
  git checkout -q pd
  printf 'src/frozen.rs|%s|2026-01-01|deadbeef|adjudicated. PIN-DELTA: +1/-1\n' "$MOVED" > "$W"
  git commit -qam "the delta from the pin, stated" >/dev/null
  git checkout -q main
  push_expect accepted "pushed live waiver stating its delta from the pin -> accepted" pd:pd
  fresh
  git checkout -q -b ratify
  printf "$MOVE" > src/frozen.rs
  printf 'src/frozen.rs|%s|BYTE-IDENTICAL|selftest fixture, pin moved\n' "$MOVED" > "$M"
  git commit -qam "ratify: the pin moves to the new blob" >/dev/null
  push_expect accepted "pushed tree whose manifest pin was moved, no waiver left -> accepted" ratify:ratify
  printf 'src/frozen.rs|%s|2026-01-01|deadbeef|ratified, row left behind\n' "$MOVED" > "$W"
  git commit -qam "a waiver row left naming the new pin" >/dev/null
  git checkout -q main
  push_expect refused "pushed waiver naming its own tree's pin (ratified, not deleted), HEAD pristine -> refused" ratify:ratify

  # What cannot be judged is refused, not waved through.
  fresh
  local Z=0000000000000000000000000000000000000000
  expect_refs 2 "a TRUST_PUSHED_REFS line that is not four fields -> refused (rc 2)" \
    "refs/heads/main $base"
  expect_refs 2 "a pushed sha this repository does not have -> refused (rc 2)" \
    "refs/heads/main 1111111111111111111111111111111111111111 refs/heads/main $Z"
  expect_refs 2 "a pushed sha that does not peel to a commit (a blob) -> refused (rc 2)" \
    "refs/heads/main $PIN refs/heads/main $Z"
  printf "$MOVE" > src/frozen.rs
  expect_refs 0 "TRUST_PUSHED_REFS set but empty, dirty worktree -> SKIPPED, not the standing reading" ""
  if grep -q '^SKIPPED: ' "$tmp/out" && ! grep -q 'the working tree' "$tmp/out"; then
    echo "  PASS  the set-but-empty reading judges nothing and says SKIPPED"; pass=$((pass + 1))
  else
    echo "  FAIL  the set-but-empty reading did not SKIP"; sed 's/^/        /' "$tmp/out"; fail=$((fail + 1))
  fi

  echo ""
  echo "selftest: $pass passed, $fail failed"
  [ "$fail" -eq 0 ]
}

# ---------------------------------------------------------------------------
main() {
  trap fg_cleanup EXIT
  local root rc
  case "${1:---check}" in
    --selftest)
      selftest
      ;;
    --print)
      root="$(git rev-parse --show-toplevel 2>/dev/null)" || {
        echo "freeze-gate: not inside a git worktree" >&2; return 2; }
      do_print "$root" "$root/scripts/frozen-files.txt"
      ;;
    --check|--check-source)
      if [ "${1:---check}" = --check-source ]; then
        FG_CITATION_READER=source
      fi
      root="$(git rev-parse --show-toplevel 2>/dev/null)" || {
        echo "freeze-gate: not inside a git worktree" >&2; return 2; }
      echo "=== oracle freeze (scripts/frozen-files.txt) ==="
      if [ -n "${TRUST_PUSHED_REFS+set}" ]; then
        push_reading "$root"; rc=$?
      else
        standing_reading "$root" "no push in flight (TRUST_PUSHED_REFS unset)"; rc=$?
      fi
      echo ""
      if [ "$rc" -eq 0 ]; then
        [ "$JUDGED" -gt 0 ] || return 0      # SKIPPED: already printed
        echo "FREEZE GATE: GREEN — $JUDGED tree(s) judged [$JUDGED_LABELS]: $T_CHECKED frozen-file check(s), $T_WAIVED waived, $T_CITED citation(s) resolved, $T_PROSE prose-only, $T_RESIDUAL prose-residual."
        return 0
      fi
      if [ "$rc" -eq 2 ]; then
        echo "FREEZE GATE: RED — the gate could not tell what to judge, so it judged nothing GREEN."
        return 2
      fi
      echo "FREEZE GATE: RED — a frozen file moved with nothing written down in the tree that carries it, or a waiver cites nothing that runs."
      [ "$FG_UNKEYED" -ne 0 ] || echo "FINDINGS: complete"
      return 1
      ;;
    *)
      echo "usage: $0 [--check|--check-source|--print|--selftest]" >&2
      return 2
      ;;
  esac
}

main "$@"
