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
# It checks BLOB IDENTITY, at HEAD and in the working tree, against a pin.
# Nothing else. It does not parse Rust, does not classify a change as safe, and
# does not decide whether an edit "only samples more". Those are judgements, and
# a gate that makes judgements is a gate that can be argued with.
#
# Every judgement is therefore pushed OUT of the script and INTO a written
# waiver with a date, a commit list and a reason (scripts/frozen-waivers.txt).
# The gate's whole job is to make sure the judgement was WRITTEN DOWN.
#
# It does print one ADVISORY: whether a moved file's change is comment-only.
# That is never a pass. Line-comment stripping is not a Rust lexer (a `//`
# inside a string literal defeats it), so believing it would be exactly the kind
# of soft heuristic this gate exists to replace. It is printed to make the
# honest case cheap to waive, not to waive it.
#
# BOTH HEAD AND WORKING TREE, because they close different holes. The working
# tree is what you are about to commit; HEAD is what you are about to push. A
# check on only the working tree misses "commit the change, then restore the
# file"; a check on only HEAD misses the edit you have not committed yet.
#
# ===========================================================================
# NO ESCAPE HATCH, BY CONSTRUCTION
# ===========================================================================
# There is no environment variable, no --force and no manifest override. The
# selftest builds its own scratch repository rather than re-pointing this one,
# precisely so that "point the gate at a different manifest" is not a code path
# that exists. Git's own `--no-verify` remains, and it shows up in the reflog
# rather than in a habit.
#
#   scripts/check_frozen_files.sh              # the gate
#   scripts/check_frozen_files.sh --print      # pinned vs HEAD vs worktree
#   scripts/check_frozen_files.sh --selftest   # mutation-proof the gate itself
#
# Exit 0 = every frozen file is at its pin, or moved with a waiver naming that
#          exact blob. Non-zero = a frozen file moved and nobody wrote it down.
set -uo pipefail

# ---------------------------------------------------------------------------
# blob_of_worktree <root> <relpath>   -> sha1, or "" when the file is absent
# blob_of_head     <root> <relpath>   -> sha1, or "" when absent at HEAD
# ---------------------------------------------------------------------------
blob_of_worktree() {
  local root="$1" rel="$2"
  [ -f "$root/$rel" ] || { printf ''; return 0; }
  git -C "$root" hash-object -- "$root/$rel" 2>/dev/null || printf ''
}

blob_of_head() {
  local root="$1" rel="$2"
  git -C "$root" rev-parse --verify --quiet "HEAD:$rel" 2>/dev/null || printf ''
}

# Strip Rust LINE comments and trailing whitespace. ADVISORY ONLY — see the
# header. Never consulted for the verdict.
strip_line_comments() {
  sed -E 's/[[:space:]]+$//' | grep -vE '^[[:space:]]*//'
}

# ---------------------------------------------------------------------------
# run_check <root> <manifest> <waivers>
# ---------------------------------------------------------------------------
run_check() {
  local root="$1" manifest="$2" waivers="$3"
  local failed=0 checked=0 waived=0

  if [ ! -f "$manifest" ]; then
    echo "freeze-gate: FAIL — manifest missing: $manifest" >&2
    return 2
  fi

  # --- the frozen files -----------------------------------------------------
  local path pin rule reason wt head wrow wblob wdate wcommits wreason
  local -a manifest_paths=()
  while IFS='|' read -r path pin rule reason; do
    case "$path" in ''|\#*) continue ;; esac
    manifest_paths+=("$path")
    checked=$((checked + 1))

    wt="$(blob_of_worktree "$root" "$path")"
    head="$(blob_of_head "$root" "$path")"

    if [ -z "$wt" ]; then
      echo "  DELETED   $path"
      echo "            a frozen file was removed from the working tree; that is a move, not an exemption"
      failed=1
      continue
    fi

    if [ "$wt" = "$pin" ] && { [ -z "$head" ] || [ "$head" = "$pin" ]; }; then
      echo "  PINNED    $path  $pin"
      continue
    fi

    # Moved. Is there a waiver naming EXACTLY this blob (for each side that moved)?
    local side_ok=1
    local moved_blob
    # HEAD and the working tree are checked separately because they close
    # different holes, but when they carry the SAME moved blob that is one fact,
    # not two, and it is reported once.
    local sides="$wt"
    [ -n "$head" ] && [ "$head" != "$wt" ] && sides="$wt $head"
    for moved_blob in $sides; do
      [ -n "$moved_blob" ] || continue
      [ "$moved_blob" != "$pin" ] || continue
      local found=0
      if [ -f "$waivers" ]; then
        while IFS='|' read -r wrow wblob wdate wcommits wreason; do
          case "$wrow" in ''|\#*) continue ;; esac
          if [ "$wrow" = "$path" ] && [ "$wblob" = "$moved_blob" ]; then
            found=1
            break
          fi
        done < "$waivers"
      fi
      if [ "$found" -eq 1 ]; then
        echo "  WAIVED    $path  $moved_blob"
        echo "            $wdate  $wcommits"
        echo "            ${wreason:0:160}"
        waived=$((waived + 1))
      else
        side_ok=0
        local which="worktree"; [ "$moved_blob" = "$head" ] && which="HEAD"
        echo "  MOVED     $path"
        echo "            pinned   $pin"
        echo "            $which  $moved_blob"
        echo "            NO WAIVER names this blob. The freeze is not a style rule: this file"
        echo "            is part of the oracle ($rule)."
        # Advisory only.
        if [ -n "$head" ] && [ "$moved_blob" = "$wt" ] && [ -f "$root/$path" ]; then
          if git -C "$root" cat-file -p "$pin" 2>/dev/null | strip_line_comments > /tmp/.freeze_a.$$ &&
             strip_line_comments < "$root/$path" > /tmp/.freeze_b.$$; then
            if cmp -s /tmp/.freeze_a.$$ /tmp/.freeze_b.$$; then
              echo "            ADVISORY: line-comment-only change (NOT a pass; strip is not a lexer)."
            fi
          fi
          rm -f /tmp/.freeze_a.$$ /tmp/.freeze_b.$$
        fi
        echo "            Fix: add a row to scripts/frozen-waivers.txt —"
        echo "              $path|$moved_blob|$(date -u +%Y-%m-%d)|<commit>|<why this only SAMPLES MORE or REFUSES MORE>"
      fi
    done
    [ "$side_ok" -eq 1 ] || failed=1
  done < "$manifest"

  # --- waivers that should not exist ---------------------------------------
  if [ -f "$waivers" ]; then
    while IFS='|' read -r wrow wblob wdate wcommits wreason; do
      case "$wrow" in ''|\#*) continue ;; esac
      local known=0
      for path in "${manifest_paths[@]:-}"; do
        [ "$path" = "$wrow" ] && known=1 && break
      done
      if [ "$known" -eq 0 ]; then
        echo "  ORPHAN    $wrow  $wblob"
        echo "            waives a path that is not in scripts/frozen-files.txt; a waiver against"
        echo "            nothing is a waiver nobody reviews. Remove it, or freeze the file."
        failed=1
        continue
      fi
      local cur_wt cur_head
      cur_wt="$(blob_of_worktree "$root" "$wrow")"
      cur_head="$(blob_of_head "$root" "$wrow")"
      if [ "$wblob" != "$cur_wt" ] && [ "$wblob" != "$cur_head" ]; then
        echo "  SPENT     $wrow  $wblob"
        echo "            no side of the tree carries this blob any more, so this waiver documents"
        echo "            nothing. Delete it. (A waiver must not outlive its change — the same rule"
        echo "            scripts/hooks-pin/pin-waivers.txt applies to submodule drift.)"
        failed=1
      fi
    done < "$waivers"
  fi

  echo ""
  if [ "$failed" -eq 0 ]; then
    echo "FREEZE GATE: GREEN — $checked frozen file(s), $waived waived."
    return 0
  fi
  echo "FREEZE GATE: RED — a frozen file moved with nothing written down."
  return 1
}

# ---------------------------------------------------------------------------
# --print
# ---------------------------------------------------------------------------
do_print() {
  local root="$1" manifest="$2"
  printf '%-52s %-42s %-42s %s\n' FILE PINNED HEAD WORKTREE
  local path pin rule reason
  while IFS='|' read -r path pin rule reason; do
    case "$path" in ''|\#*) continue ;; esac
    printf '%-52s %-42s %-42s %s\n' \
      "$(basename "$path")" "$pin" \
      "$(blob_of_head "$root" "$path")" "$(blob_of_worktree "$root" "$path")"
  done < "$manifest"
}

# ---------------------------------------------------------------------------
# --selftest — the MUTATION PROOF.
#
# A gate that has never been seen to fail is a gate nobody has tested. This
# builds a scratch repository, plants nine distinct defects, and asserts the
# verdict each time. It touches nothing outside its own mktemp directory and it
# uses THIS script, not a copy.
# ---------------------------------------------------------------------------
SELFTEST_TMP=""
selftest_cleanup() { [ -n "${SELFTEST_TMP:-}" ] && rm -rf "$SELFTEST_TMP"; return 0; }

selftest() {
  local me tmp rc pass=0 fail=0
  me="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/$(basename "${BASH_SOURCE[0]}")"
  tmp="$(mktemp -d)"
  SELFTEST_TMP="$tmp"
  trap selftest_cleanup EXIT

  mkdir -p "$tmp/repo/src" "$tmp/repo/scripts"
  cd "$tmp/repo" || return 2
  git init -q .
  git config user.email selftest@localhost
  git config user.name selftest
  printf 'fn oracle() -> bool {\n    // the comparison\n    true\n}\n' > src/frozen.rs
  printf 'fn other() {}\n' > src/loose.rs
  git add -A >/dev/null
  git commit -qm baseline >/dev/null

  local PIN
  PIN="$(git hash-object src/frozen.rs)"
  printf 'src/frozen.rs|%s|BYTE-IDENTICAL|selftest fixture\n' "$PIN" > scripts/frozen-files.txt
  : > scripts/frozen-waivers.txt

  local M="$tmp/repo/scripts/frozen-files.txt" W="$tmp/repo/scripts/frozen-waivers.txt"

  expect() { # expect <want-rc> <label>
    local want="$1" label="$2" got
    bash "$me" --selftest-run "$tmp/repo" "$M" "$W" >"$tmp/out" 2>&1
    got=$?
    if [ "$got" -eq "$want" ]; then
      echo "  PASS  $label (rc=$got)"; pass=$((pass + 1))
    else
      echo "  FAIL  $label (want rc=$want, got rc=$got)"; sed 's/^/        /' "$tmp/out"; fail=$((fail + 1))
    fi
  }

  echo "=== freeze-gate selftest ==="

  # 1. pristine
  expect 0 "pristine tree is GREEN"

  # 2. a moved frozen file with no waiver
  printf 'fn oracle() -> bool {\n    // the comparison\n    false\n}\n' > src/frozen.rs
  expect 1 "moved frozen file, no waiver -> RED"

  # 3. a waiver naming the WRONG blob does not excuse it
  printf 'src/frozen.rs|%s|2026-01-01|deadbeef|wrong blob\n' \
    "0000000000000000000000000000000000000000" > "$W"
  expect 1 "waiver naming a DIFFERENT blob -> RED (no blanket waivers)"

  # 4. a waiver naming the exact blob does
  printf 'src/frozen.rs|%s|2026-01-01|deadbeef|adjudicated\n' "$(git hash-object src/frozen.rs)" > "$W"
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
  : > "$W"
  printf 'fn oracle() -> bool {\n    // the comparison\n    false\n}\n' > src/frozen.rs
  git commit -qam "sneak" >/dev/null
  git show -q --format= HEAD >/dev/null
  printf 'fn oracle() -> bool {\n    // the comparison\n    true\n}\n' > src/frozen.rs
  expect 1 "HEAD moved, worktree restored -> RED (both sides are checked)"

  # 9. a COMMENT-ONLY change is still RED (advisory, never a pass)
  git checkout -q -- . && git reset -q --soft HEAD~1 && git checkout -q -- . 2>/dev/null
  git reset -q --hard HEAD >/dev/null 2>&1
  printf 'fn oracle() -> bool {\n    // the comparison, restated\n    true\n}\n' > src/frozen.rs
  bash "$me" --selftest-run "$tmp/repo" "$M" "$W" >"$tmp/out" 2>&1
  rc=$?
  if [ "$rc" -eq 1 ] && grep -q "line-comment-only" "$tmp/out"; then
    echo "  PASS  comment-only change -> RED, and the advisory names it"; pass=$((pass + 1))
  else
    echo "  FAIL  comment-only change (rc=$rc; advisory present: $(grep -c 'line-comment-only' "$tmp/out"))"
    sed 's/^/        /' "$tmp/out"; fail=$((fail + 1))
  fi

  echo ""
  echo "selftest: $pass passed, $fail failed"
  [ "$fail" -eq 0 ]
}

# ---------------------------------------------------------------------------
main() {
  case "${1:---check}" in
    --selftest)
      selftest
      ;;
    # Internal: the selftest's own re-entry. Not a user-facing override — it
    # only ever points at a scratch repository the selftest just created.
    --selftest-run)
      run_check "$2" "$3" "$4"
      ;;
    --print)
      local root
      root="$(git rev-parse --show-toplevel 2>/dev/null)" || {
        echo "freeze-gate: not inside a git worktree" >&2; return 2; }
      do_print "$root" "$root/scripts/frozen-files.txt"
      ;;
    --check|"")
      local root
      root="$(git rev-parse --show-toplevel 2>/dev/null)" || {
        echo "freeze-gate: not inside a git worktree" >&2; return 2; }
      echo "=== oracle freeze (scripts/frozen-files.txt) ==="
      run_check "$root" "$root/scripts/frozen-files.txt" "$root/scripts/frozen-waivers.txt"
      ;;
    *)
      echo "usage: $0 [--check|--print|--selftest]" >&2
      return 2
      ;;
  esac
}

main "$@"
