#!/usr/bin/env bash
# check_tcb_panic_freedom.sh — TCB panic-surface ratchet gate (self-hardening).
#
# The verifier's TRUSTED CORE (trust-vcgen, trust-router, trust-types,
# trust-loop, trust-cache, the in-tree trust_verify MIR pass, and the bridges)
# must not panic on production paths: a panic/unwrap/expect/unreachable in the
# verifier crashes the compiler (a reliability bug) and is soundness-adjacent
# (a half-built proof state aborted mid-flight). This gate COUNTS the panicking
# constructs on production paths in the TCB and FAILS if the total EXCEEDS a
# committed baseline, so new panics are caught while the existing backlog is
# burned down deliberately (the baseline only ever ratchets DOWN).
#
# This is a BASELINE-RATCHET gate, not a claim of panic-freedom. The current
# baseline is the honest production-path count at the time of committing; the
# accompanying audit (reports/tcb-hardening-audit.md) classifies offenders.
#
# What "production path" means here:
#   * test-named files (tests.rs, *_tests.rs, test_*.rs, *_test.rs) are excluded;
#   * every `#[cfg(test)]` item — `mod`, `fn`, `impl`, anything — is dropped
#     whole, by tracking its brace depth to the closing brace;
#   * comment text and the CONTENTS of string/char literals are erased before
#     matching, so only executable code is counted.
#
# That last filter is load-bearing rather than cosmetic. The TCB's own subject
# matter IS panicking code: vcgen emits obligations that discharge a user's
# `.unwrap()`, and trust_verify names the panic intrinsic it recognizes. Their
# prose is therefore saturated with the very tokens this gate greps for, so a
# raw line grep charges an engineer for EXPLAINING panic handling and rewards
# deleting the explanation. A gate that taxes documentation is worse than no
# gate. Erasing comments and literal text costs one lexing pass and makes the
# number mean what its name says.
#
# The lexer is a character state machine (line comments, nesting block
# comments, strings with escapes, raw strings with hash delimiters, char
# literals distinguished from lifetimes), not a Rust parser. It is intended to
# be deterministic and monotone, not perfectly precise — the ratchet semantics
# tolerate a stable heuristic. A `.unwrap()` on its own continuation line of a
# method chain still counts, correctly.
#
# Usage:
#   scripts/check_tcb_panic_freedom.sh            # gate against the baseline
#   scripts/check_tcb_panic_freedom.sh --print    # per-pattern + per-crate counts
#   scripts/check_tcb_panic_freedom.sh --update-baseline  # rewrite the committed
#                                                          # baseline to current
#                                                          # (use ONLY to ratchet
#                                                          #  DOWN after fixes)
#
# Wiring: `targo trust gate scripts` runs this as a hard failure, and
# scripts/check_all.sh delegates to that gate — so a regression here is a red
# repo, not an advisory.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache 2.0
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

# TCB source roots (directory OR single file). Keep in sync with the audit.
TCB_ROOTS=(
  "crates/trust-vcgen/src"
  "crates/trust-router/src"
  "crates/trust-types/src"
  "crates/trust-loop/src"
  "crates/trust-cache/src"
  "crates/trust-ir-bridge/src"
  "crates/trust-vc-bridge/src"
  "crates/trust-cg-bridge/src"
  "crates/trust-ny-bridge/src"
  "crates/trust-wasm-bridge/src"
  "compiler/rustc_mir_transform/src/trust_verify.rs"
)

# Committed baseline: the gate FAILS if the live total exceeds this. Ratchet
# DOWN only (after landing hardening). Stored beside the script so the audit
# and the gate read one source of truth. `#`-prefixed lines are commentary —
# whoever moves the number records WHY there.
BASELINE_FILE="$REPO_ROOT/scripts/check_tcb_panic_freedom.baseline"

# ---- Rust line lexer + cfg(test) stripper -----------------------------------
# Emits a file's production-path lines with comments and literal contents
# erased. Lexer state (block comment, string, raw string) persists across
# lines, so a multi-line literal cannot leak tokens into the count. Brace
# depth is only ever counted on ALREADY-erased lines, so a `'{'` char literal
# or a `"}"` in a message cannot end a `#[cfg(test)]` block early — the defect
# that used to let test bodies through.
read -r -d '' LEX_AWK <<'AWK' || true
BEGIN { st = 0; bdepth = 0; rhash = 0; in_test = 0; depth = 0; pend = 0 }
# st: 0 = code, 1 = block comment, 2 = string, 3 = raw string
function erase(s,   out, i, n, c, d, h, j) {
  out = ""; i = 1; n = length(s)
  while (i <= n) {
    c = substr(s, i, 1); d = substr(s, i, 2)
    if (st == 1) {                       # Rust block comments nest
      if (d == "*/") { bdepth--; i += 2; if (bdepth <= 0) st = 0; continue }
      if (d == "/*") { bdepth++; i += 2; continue }
      i++; continue
    }
    if (st == 2) {
      if (c == "\\") { i += 2; continue }
      if (c == "\"") { st = 0; out = out "\""; i++; continue }
      i++; continue
    }
    if (st == 3) {                       # raw string: no escapes, hash-delimited
      if (c == "\"") {
        h = 0
        while (substr(s, i + 1 + h, 1) == "#") h++
        if (h >= rhash) { st = 0; out = out "\""; i += 1 + rhash; continue }
      }
      i++; continue
    }
    if (d == "//") break                 # line comment: nothing after it is code
    if (d == "/*") { st = 1; bdepth = 1; i += 2; continue }
    if (c == "\"") { st = 2; out = out "\""; i++; continue }
    # A leading r/b sigil only opens a literal when it is not part of an
    # identifier (`for`, `sub`, a variable named `r`).
    if ((c == "r" || c == "b") && (out == "" || substr(out, length(out), 1) !~ /[A-Za-z0-9_]/)) {
      j = i + 1
      if (c == "b" && substr(s, j, 1) == "r") j++
      h = 0
      while (substr(s, j + h, 1) == "#") h++
      if (substr(s, j + h, 1) == "\"") {
        if (h > 0) { rhash = h; st = 3; out = out "\""; i = j + h + 1; continue }
        st = 2; out = out "\""; i = j + 1; continue
      }
    }
    if (c == "'") {
      if (d == "'\\") {                  # escaped char literal: run to its close
        j = i + 2
        while (j <= n && substr(s, j, 1) != "'") j++
        out = out "''"; i = j + 1; continue
      }
      if (substr(s, i + 2, 1) == "'") { out = out "''"; i += 3; continue }
      out = out c; i++; continue         # otherwise a lifetime
    }
    out = out c; i++
  }
  return out
}
{
  line = erase($0)
  if (in_test == 1) {
    o = gsub(/{/, "{", line); c = gsub(/}/, "}", line)
    depth += o - c
    if (depth <= 0) in_test = 0
    next
  }
  if (line ~ /#\[cfg\(test\)\]/ || line ~ /#\[cfg\(all\([^)]*test[^)]*\)\)\]/) { pend = 1; next }
  if (pend == 1) {
    pend = 0
    # A braced item (mod/fn/impl/struct) is skipped whole; a `mod tests;`
    # DECLARATION has no brace and only drops its own line — its body lives in
    # an excluded, test-named file.
    if (line ~ /\{/) {
      o = gsub(/{/, "{", line); c = gsub(/}/, "}", line)
      depth = o - c
      if (depth > 0) in_test = 1
    }
    next
  }
  print FILENAME ":" line
}
AWK

# List the .rs files under a root (dir or single file), excluding test-named files.
tcb_files() {
  local root="$1"
  if [ -f "$root" ]; then
    printf '%s\n' "$root"
    return 0
  fi
  if [ -d "$root" ]; then
    find "$root" -name '*.rs' \
      ! -name 'tests.rs' \
      ! -name '*_tests.rs' \
      ! -name 'test_*.rs' \
      ! -name '*_test.rs' \
      | LC_ALL=C sort
  fi
}

# One lexing pass over the whole TCB, cached as `<path>:<code>` lines. Every
# count below is a grep over this stream, so adding a breakdown is free.
STREAM="$(mktemp "${TMPDIR:-/tmp}/tcb-panic-stream.XXXXXX")"
trap 'rm -f "$STREAM"' EXIT
build_stream() {
  local root f
  : > "$STREAM"
  for root in "${TCB_ROOTS[@]}"; do
    while IFS= read -r f; do
      [ -n "$f" ] || continue
      awk "$LEX_AWK" "$f" >> "$STREAM"
    done < <(tcb_files "$root")
  done
}

# The panicking-construct patterns. `.unwrap()` is the exact zero-arg method;
# `.expect(` is the method form (avoids matching e.g. `expect(` free fns);
# the macro forms are guarded by a non-identifier left boundary so we do not
# match `my_unreachable!` or words inside identifiers. The `<path>:` prefix on
# every stream line is itself a non-identifier boundary, so a construct at
# column 0 still matches.
RE_UNWRAP='\.unwrap\(\)'
RE_EXPECT='\.expect\('
RE_PANIC='(^|[^A-Za-z0-9_])panic!'
RE_UNREACHABLE='(^|[^A-Za-z0-9_])unreachable!'
RE_UNIMPLEMENTED='(^|[^A-Za-z0-9_])unimplemented!'
RE_TODO='(^|[^A-Za-z0-9_])todo!'
RE_ANY="$RE_UNWRAP|$RE_EXPECT|$RE_PANIC|$RE_UNREACHABLE|$RE_UNIMPLEMENTED|$RE_TODO"

count_pattern() {
  grep -cE "$1" "$STREAM" || true
}

# Populates the LAST_* and TOTAL globals (must run in the parent shell, NOT a
# command substitution, so the globals survive under `set -u`).
LAST_UNWRAP=0; LAST_EXPECT=0; LAST_PANIC=0
LAST_UNREACHABLE=0; LAST_UNIMPLEMENTED=0; LAST_TODO=0; TOTAL=0
compute_total() {
  build_stream
  LAST_UNWRAP=$(count_pattern "$RE_UNWRAP")
  LAST_EXPECT=$(count_pattern "$RE_EXPECT")
  LAST_PANIC=$(count_pattern "$RE_PANIC")
  LAST_UNREACHABLE=$(count_pattern "$RE_UNREACHABLE")
  LAST_UNIMPLEMENTED=$(count_pattern "$RE_UNIMPLEMENTED")
  LAST_TODO=$(count_pattern "$RE_TODO")
  TOTAL=$((LAST_UNWRAP + LAST_EXPECT + LAST_PANIC + LAST_UNREACHABLE + LAST_UNIMPLEMENTED + LAST_TODO))
}

print_breakdown() {
  echo "TCB production-path panic surface (code only; test items and comment/literal text excluded):"
  printf "  %-16s %s\n" ".unwrap()"        "$LAST_UNWRAP"
  printf "  %-16s %s\n" ".expect(...)"     "$LAST_EXPECT"
  printf "  %-16s %s\n" "panic!"           "$LAST_PANIC"
  printf "  %-16s %s\n" "unreachable!"     "$LAST_UNREACHABLE"
  printf "  %-16s %s\n" "unimplemented!"   "$LAST_UNIMPLEMENTED"
  printf "  %-16s %s\n" "todo!"            "$LAST_TODO"
}

# Per-root attribution: a single grand total tells you the ratchet broke but
# not where, and "where" is the first question anyone asks.
print_per_root() {
  local root n
  echo "Per source root (lines carrying at least one construct):"
  for root in "${TCB_ROOTS[@]}"; do
    n=$(awk -v r="$root" 'index($0, r) == 1' "$STREAM" | grep -cE "$RE_ANY" || true)
    printf "  %-50s %s\n" "$root" "$n"
  done
}

# Read the committed number, ignoring `#` commentary and blank lines.
read_baseline() {
  awk '/^[[:space:]]*#/ { next } /^[[:space:]]*$/ { next } { gsub(/[^0-9]/, "", $0); print; exit }' "$BASELINE_FILE"
}

case "${1:-gate}" in
  --print|print)
    compute_total
    print_breakdown
    echo "  ----------------"
    printf "  %-16s %s\n" "TOTAL" "$TOTAL"
    echo ""
    print_per_root
    exit 0
    ;;
  --update-baseline)
    compute_total
    OLD="(none)"
    [ -f "$BASELINE_FILE" ] && OLD="$(read_baseline)"
    # Preserve the `#` header verbatim: it carries the rationale for the last
    # move, which is the part a bare number cannot express.
    NEW_BASELINE="$(mktemp "${TMPDIR:-/tmp}/tcb-panic-baseline.XXXXXX")"
    if [ -f "$BASELINE_FILE" ]; then
      awk '/^[[:space:]]*#/ { print; next } { exit }' "$BASELINE_FILE" > "$NEW_BASELINE"
    fi
    printf '%s\n' "$TOTAL" >> "$NEW_BASELINE"
    mv "$NEW_BASELINE" "$BASELINE_FILE"
    print_breakdown
    echo "  ----------------"
    echo "Baseline updated: $OLD -> $TOTAL  ($BASELINE_FILE)"
    echo "NOTE: commit the new baseline. Ratchet DOWN only, and record WHY in the"
    echo "      '#' header of the baseline file — an unexplained number is not evidence."
    exit 0
    ;;
  gate|"")
    ;;
  -h|--help|help)
    awk 'NR > 1 && /^#/ { sub(/^# ?/, ""); print; next } NR > 1 { exit }' "${BASH_SOURCE[0]}"
    exit 0
    ;;
  *)
    echo "Unknown mode: $1 (use gate | --print | --update-baseline)" >&2
    exit 2
    ;;
esac

if [ ! -f "$BASELINE_FILE" ]; then
  echo "FAIL: missing baseline file: $BASELINE_FILE" >&2
  echo "DETAIL: run 'scripts/check_tcb_panic_freedom.sh --update-baseline' to seed it." >&2
  exit 1
fi
BASELINE="$(read_baseline)"
if [ -z "$BASELINE" ]; then
  echo "FAIL: baseline file is empty/non-numeric: $BASELINE_FILE" >&2
  exit 1
fi

compute_total
echo "=== TCB panic-freedom ratchet ==="
print_breakdown
echo "  ----------------"
echo "  live total: $TOTAL    baseline: $BASELINE"
if [ "$TOTAL" -gt "$BASELINE" ]; then
  echo ""
  print_per_root
  echo ""
  echo "FAIL: TCB production-path panic surface GREW ($TOTAL > baseline $BASELINE)."
  echo "      A new unwrap/expect/panic/unreachable/unimplemented/todo landed in the"
  echo "      verifier's trusted core. Replace it with a propagated error/Result, or"
  echo "      (if it is a documented invariant) justify it in"
  echo "      reports/tcb-hardening-audit.md and ratchet the baseline only after review."
  exit 1
fi
if [ "$TOTAL" -lt "$BASELINE" ]; then
  echo ""
  echo "NOTE: TCB panic surface SHRANK ($TOTAL < baseline $BASELINE). Nice."
  echo "      Ratchet the baseline down: scripts/check_tcb_panic_freedom.sh --update-baseline"
fi
echo ""
echo "PASS: TCB panic surface within baseline ($TOTAL <= $BASELINE)."
exit 0
