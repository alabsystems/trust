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
# baseline caps the production-path count of this lexer. Measurements are in
# docs/STATUS.md; this syntactic metric does not establish panic-freedom.
#
# What "production path" means here:
#   * test-named files (tests.rs, *_tests.rs, test_*.rs, *_test.rs) are excluded;
#   * every `#[cfg(test)]` item — `mod`, `fn`, `impl`, anything — is dropped
#     whole, by tracking its brace depth to the closing brace;
#   * a module FILE is excluded when every resolved `mod` declaration of it
#     is test-only, explicitly or through established parent-file ancestry
#     (with `#[path]` and inline nesting resolved); a production declaration,
#     no declaration or an ungrounded cycle keeps the file counted;
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
#   scripts/check_tcb_panic_freedom.sh --print    # per-pattern + per-crate counts,
#                                                 # and the files excluded as test-only
#   scripts/check_tcb_panic_freedom.sh --list     # every counted site, one per line
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

REPO_ROOT="$(cd -P "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)"
cd "$REPO_ROOT"

# TCB source roots (directory OR single file), including the split compiler pass.
TCB_ROOTS=(
  "crates/trust-vcgen/src"
  "crates/trust-router/src"
  "crates/trust-types/src"
  "crates/trust-loop/src"
  "crates/trust-cache/src"
  "crates/trust-ir-bridge/src"
  "crates/trust-vc-bridge/src"
  "crates/trust-cg-bridge/src"
  "crates/trust-wasm-bridge/src"
  "compiler/rustc_mir_transform/src/trust_verify.rs"
  "compiler/rustc_mir_transform/src/trust_verify/"
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
#
# The same pass records every `mod NAME;` DECLARATION it reads (into the file
# named by `-v DECLS=`), with the inline modules it sits in, the `#[path]` it
# carries and whether it is test-only. `build_stream` resolves those to files
# and drops a file whose every declaration is test-only (see `test_only_files`).
read -r -d '' LEX_AWK <<'AWK' || true
BEGIN { st = 0; bdepth = 0; rhash = 0; in_test = 0; depth = 0; pend = 0
        gdepth = 0; nmods = 0; pathattr = ""
        CFG_TEST = "#\\[cfg\\(test\\)\\]|#\\[cfg\\(all\\([^)]*test[^)]*\\)\\)\\]" }
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
# The inline modules enclosing the current line, as path components ("a/b/").
function inline_path(   k, p) {
  p = ""
  for (k = 1; k <= nmods; k++) p = p mname[k] "/"
  return p
}
# Record a `mod NAME;` declaration and track inline `mod NAME {` nesting. Runs
# on EVERY line, test or not, so brace depth and nesting stay exact; `is_test`
# says whether the line belongs to a `#[cfg(test)]` item. `line` is the erased
# text, `raw` the original: a `#[path = "…"]` value is literal content, which
# `erase` blanks, so it is read back from `raw`.
function note_decls(raw, line, is_test,   m, o, c) {
  if (line ~ /#\[path[ \t]*=/ && match(raw, /#\[path[ \t]*=[ \t]*"[^"]*"/)) {
    pathattr = substr(raw, RSTART, RLENGTH)
    sub(/^#\[path[ \t]*=[ \t]*"/, "", pathattr); sub(/"$/, "", pathattr)
  }
  if (match(line, /(^|[^A-Za-z0-9_])mod[ \t]+[A-Za-z_][A-Za-z0-9_]*[ \t]*;/)) {
    m = substr(line, RSTART, RLENGTH)
    sub(/^[^A-Za-z0-9_]?mod[ \t]+/, "", m); sub(/[ \t]*;$/, "", m)
    if (DECLS != "") print FILENAME "\t" inline_path() "\t" m "\t" pathattr "\t" is_test >> DECLS
    pathattr = ""
  } else if (match(line, /(^|[^A-Za-z0-9_])mod[ \t]+[A-Za-z_][A-Za-z0-9_]*[ \t]*\{/)) {
    m = substr(line, RSTART, RLENGTH)
    sub(/^[^A-Za-z0-9_]?mod[ \t]+/, "", m); sub(/[ \t]*\{$/, "", m)
    nmods++; mname[nmods] = m; mdepth[nmods] = gdepth + 1
    pathattr = ""
  } else if (line ~ /[;{}]/) {
    pathattr = ""                        # some other item took the attribute
  }
  o = gsub(/{/, "{", line); c = gsub(/}/, "}", line)
  gdepth += o - c
  while (nmods > 0 && gdepth < mdepth[nmods]) nmods--
}
{
  line = erase($0)
  note_decls($0, line, (in_test == 1 || pend == 1 || line ~ CFG_TEST) ? 1 : 0)
  if (in_test == 1) {
    o = gsub(/{/, "{", line); c = gsub(/}/, "}", line)
    depth += o - c
    if (depth <= 0) in_test = 0
    next
  }
  if (match(line, CFG_TEST)) {
    pend = 1
    # `#[cfg(test)] mod x;` (or `… fn t() {`) on ONE line: the item is the
    # rest of this line, not the next one, which would otherwise be swallowed.
    line = substr(line, RSTART + RLENGTH)
    if (line !~ /[{;]/) next
  }
  if (pend == 1) {
    # Scan forward to the ITEM the `#[cfg(test)]` attaches to. Anything between
    # is a further attribute or a signature continuation and is dropped while
    # STAYING pending — an item is either braced or `;`-terminated, so this
    # search is bounded and cannot run away.
    #
    # Staying pending is the whole point. This used to clear `pend` after
    # exactly ONE line, so it only stripped `#[cfg(test)]` items whose brace sat
    # on the very next line. The ubiquitous
    #     #[cfg(test)]
    #     #[test]
    #     fn t() { ... a.unwrap() ... }
    # form therefore leaked its ENTIRE BODY into the production count: `#[test]`
    # carries no brace, `pend` reset, and `fn t() {` was then read as
    # production code. Measured 2026-08-26 on this tree, that mismeasurement was
    # the whole of the gate's red.
    #
    # A braced item (mod/fn/impl/struct) is skipped whole; a `mod tests;`
    # DECLARATION has no brace and only drops its own line — its body lives in
    # an excluded, test-named file.
    if (line ~ /\{/) {
      pend = 0
      o = gsub(/{/, "{", line); c = gsub(/}/, "}", line)
      depth = o - c
      if (depth > 0) in_test = 1
      next
    }
    if (line ~ /;/) { pend = 0; next }
    next
  }
  print FILENAME ":" FNR ":" line
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

# One lexing pass over the whole TCB, cached as `<path>:<line>:<code>` lines.
# Every count below is a grep over this stream, so adding a breakdown is free —
# and `--list` is that same grep, printed instead of counted.
STREAM="$(mktemp "${TMPDIR:-/tmp}/tcb-panic-stream.XXXXXX")"
RAW="$(mktemp "${TMPDIR:-/tmp}/tcb-panic-raw.XXXXXX")"
DECLS="$(mktemp "${TMPDIR:-/tmp}/tcb-panic-decls.XXXXXX")"
FILES="$(mktemp "${TMPDIR:-/tmp}/tcb-panic-files.XXXXXX")"
ALL_FILES="$(mktemp "${TMPDIR:-/tmp}/tcb-panic-all-files.XXXXXX")"
TEST_ONLY="$(mktemp "${TMPDIR:-/tmp}/tcb-panic-test-only.XXXXXX")"
trap 'rm -f "$STREAM" "$RAW" "$DECLS" "$FILES" "$ALL_FILES" "$TEST_ONLY"' EXIT
# `.expect(` IS NOT ALWAYS `Option::expect`. A file may define its own
# `fn expect(&self, ..)`, and an inherent method SHADOWS the std ones — neither
# `Option` nor `Result` can be `Self` here, because they are foreign types this
# workspace cannot `impl`. Measured 2026-09-21: the two spec parsers
# (`trust-types/src/spec_parse.rs`, `spec_attrs.rs`) each define
# `fn expect(&mut self, expected: &Token, label: &str) -> Result<(), SpecParseError>`
# and call it 32 times between them, EVERY ONE `?`-propagated. Counting those as
# panic sites is the same class of error as the 2026-07-24 entry's counting of
# comment prose: it inflates the number with things that cannot panic, and it can
# be "reduced" by making a parser worse.
#
# The rewrite below is deliberately visible in `--list` rather than silent, so a
# reader sees WHY a call was not counted instead of wondering where it went.
#
# IT IS RECEIVER-SCOPED (`self.expect(`), NOT FILE-SCOPED, ON PURPOSE. A
# file-scoped exclusion would hide a genuine `Option::expect` sitting in the same
# parser file, which is exactly the hole this gate exists to catch. The cost is
# that a call to the inherent method through some OTHER binding is still counted
# — an over-count, which is the safe direction, and there are zero such calls
# today (all 32 are `self.`).
#
# MUTATION-PROVED 2026-09-21, four plants against a 250 base, each restored:
#   Option::expect in a file with no inherent method      250 -> 251  (counted)
#   a `self.`-receiver expect in that same file           251 -> 252  (counted)
#   the inherent method reached through a binding         250 -> 251  (counted)
#   a REAL Option::expect inside spec_parse.rs            251 -> 252  (counted)
# So the exclusion fires only where method resolution says it must, and the
# counter still detects every real panic site including in the excluded files.
inherent_expect_file() {
  grep -qE '^[[:space:]]*(pub(\([^)]*\))?[[:space:]]+)?fn expect\(&(mut )?self' "$1"
}

# A FILE DECLARED ONLY UNDER `#[cfg(test)]` IS TEST CODE, WHATEVER ITS NAME.
# The name filter in `tcb_files` and the item stripper in `LEX_AWK` both miss
# it: `#[cfg(test)] #[path = "compiler_consumer_census.rs"] mod census;` drops
# only the declaration line, and the file's whole body was then read as
# production. Measured 2026-10-10 on main ce026e1c63b, that put 13 test-only
# constructs into the count: trust-cg-bridge's compiler_consumer_census.rs x9
# (declared at compiler_consumer.rs:269-271) and trust-vcgen's
# referent_fold/fold_cost_fix.rs x4 (declared inside the inline
# `mod referent_fold` of lib.rs). Neither file is compiled outside `cfg(test)`.
#
# The rule is per declaration, and fails toward COUNTING: a file is dropped only
# when it has at least one resolved `mod` declaration in the TCB and EVERY one
# of them is test-only (carries `#[cfg(test)]`, sits inside a `#[cfg(test)]`
# item, or comes from an already established test-only source file). Resolve
# declarations in test-named files too, without treating the name as ancestry.
# A single production declaration keeps it; a file no declaration
# resolves to (a crate root, a `#[path]` from outside the TCB, a shape this
# resolver does not model) keeps it. Resolution is Rust's: a declaration in
# lib.rs/main.rs/mod.rs names `<dir>/<inline mods>/name{.rs,/mod.rs}`, one in
# `foo.rs` names `<dir>/foo/<inline mods>/name{.rs,/mod.rs}`; a `#[path]` is
# relative to the declaring file's directory, or, inside an inline module, to
# that module's directory. Only a TCB file can be a target, so a misresolved
# declaration lands on no file rather than on the wrong one.
#
# Mutation-proved by scripts/tests/check_tcb_panic_freedom_test.sh in the four
# directions (a production file counts; a file declared only under cfg(test)
# does not; a file declared both ways counts; `#[path]` and inline nesting
# resolve), plus an undeclared file counting.
test_only_files() {
  awk -F '\t' -v FILES="$ALL_FILES" -v CANDIDATES="$FILES" '
    function norm(p,   n, a, s, i, k, out) {
      n = split(p, a, "/"); k = 0
      for (i = 1; i <= n; i++) {
        if (a[i] == "" || a[i] == ".") continue
        if (a[i] == ".." && k > 0 && s[k] != "..") { k--; continue }
        s[++k] = a[i]
      }
      out = ""
      for (i = 1; i <= k; i++) out = out (i > 1 ? "/" : "") s[i]
      return out
    }
    BEGIN {
      while ((getline l < FILES) > 0) tcb[l] = 1
      while ((getline l < CANDIDATES) > 0) candidate[l] = 1
    }
    {
      f = $1; inl = $2; name = $3; pth = $4; t = $5
      d = f; sub(/\/[^\/]*$/, "", d)
      b = f; sub(/^.*\//, "", b)
      if (b == "lib.rs" || b == "main.rs" || b == "mod.rs") m = d
      else { m = d "/" b; sub(/\.rs$/, "", m) }
      if (pth != "") {
        c1 = norm((inl == "") ? d "/" pth : m "/" inl pth); c2 = ""
      } else {
        c1 = norm(m "/" inl name ".rs"); c2 = norm(m "/" inl name "/mod.rs")
      }
      if (c1 in tcb) target = c1
      else if (c2 != "" && (c2 in tcb)) target = c2
      else next
      targets[target] = 1
      from[++edges] = f; to[edges] = target; explicit_test[edges] = (t == 1)
    }
    END {
      # Only established test ancestry propagates. An orphan, an unanchored
      # cycle or any incoming production declaration keeps a file counted.
      do {
        changed = 0
        for (x in prod_decl) delete prod_decl[x]
        for (i = 1; i <= edges; i++)
          if (!explicit_test[i] && !(from[i] in test_only)) prod_decl[to[i]] = 1
        for (x in targets)
          if (!(x in prod_decl) && !(x in test_only)) { test_only[x] = 1; changed = 1 }
      } while (changed)
      # Named test files were already excluded by the filename rule. Report
      # only files whose counted population this declaration rule changes.
      for (x in test_only) if (x in candidate) print x
    }
  ' "$DECLS" | LC_ALL=C sort
}

build_stream() {
  local root f
  # An absent sparse-checkout input is unknown, not a zero-panic source file.
  # In a checkout, include every committed Rust file in the required roots;
  # checking only the directory would miss a partially materialized root.
  for root in "${TCB_ROOTS[@]}"; do
    if [ ! -f "$root" ] && [ ! -d "$root" ]; then
      echo "NOT JUDGED: missing TCB source root: $root" >&2
      exit 2
    fi
  done
  if [ "$(git rev-parse --show-toplevel 2>/dev/null || true)" = "$REPO_ROOT" ]; then
    if ! git ls-tree -r --name-only -z HEAD -- "${TCB_ROOTS[@]}" > "$FILES"; then
      echo "NOT JUDGED: cannot enumerate committed TCB sources" >&2
      exit 2
    fi
    while IFS= read -r -d '' f; do
      case "$f" in
        *.rs)
          if [ ! -f "$f" ]; then
            echo "NOT JUDGED: missing committed TCB source: $f" >&2
            exit 2
          fi
          ;;
      esac
    done < "$FILES"
  fi
  : > "$RAW"; : > "$DECLS"; : > "$FILES"; : > "$ALL_FILES"
  for root in "${TCB_ROOTS[@]}"; do
    tcb_files "$root" >> "$FILES"
    # Filename-excluded parents still declare children. Do not infer test
    # ancestry from a name: parse their declarations and require a cfg(test)
    # chain from the actual parent, just as for every other source file.
    if [ -f "$root" ]; then
      printf '%s\n' "$root" >> "$ALL_FILES"
    else
      find "$root" -name '*.rs' | LC_ALL=C sort >> "$ALL_FILES"
    fi
  done
  while IFS= read -r f; do
    [ -n "$f" ] || continue
    if inherent_expect_file "$f"; then
      awk -v DECLS="$DECLS" "$LEX_AWK" "$f" | sed 's/self\.expect(/self.<inherent-expect>(/g' >> "$RAW"
    else
      awk -v DECLS="$DECLS" "$LEX_AWK" "$f" >> "$RAW"
    fi
  done < "$ALL_FILES"
  test_only_files > "$TEST_ONLY"
  # The stream is RAW minus the lines of test-only files. (A `getline` set,
  # not the `NR == FNR` idiom, which misreads an empty skip list.)
  awk -v SKIP="$TEST_ONLY" -v FILES="$FILES" '
    BEGIN {
      while ((getline l < SKIP) > 0) skip[l] = 1
      while ((getline l < FILES) > 0) candidate[l] = 1
    }
    { p = $0; sub(/:.*/, "", p); if ((p in candidate) && !(p in skip)) print }
  ' "$RAW" > "$STREAM"
}

# The files `build_stream` dropped as test-only, each with the construct lines
# it would otherwise have added: printed, so an exclusion is never silent.
print_test_only() {
  local f n
  [ -s "$TEST_ONLY" ] || return 0
  echo "Not counted, every resolved \`mod\` declaration has test-only ancestry (construct lines in the file):"
  while IFS= read -r f; do
    n=$(awk -v f="$f" 'index($0, f ":") == 1' "$RAW" | grep -cE "$RE_ANY" || true)
    printf "  %-66s %s\n" "$f" "$n"
  done < "$TEST_ONLY"
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
  # One canonical nonnegative decimal, bounded for portable shell integer
  # comparisons. An overflowing test inside an if would otherwise fail open.
  awk '
    /^[[:space:]]*#/ { next }
    /^[[:space:]]*$/ { next }
    {
      records++
      if (records != 1 || $0 !~ /^[ \t]*(0|[1-9][0-9]*)[ \t]*$/) { bad = 1; exit 1 }
      value = $0; gsub(/^[ \t]+|[ \t]+$/, "", value)
      if (length(value) > 10 || value + 0 > 2147483647) { bad = 1; exit 1 }
    }
    END { if (bad || records != 1) exit 1; print value }
  ' "$BASELINE_FILE"
}

# The sites themselves. The gate says "replace it with a propagated
# error/Result" and until now could not say WHICH — so the first move after a
# red was to re-derive this by hand, with a different lexer than the gate's.
print_sites() {
  local root
  for root in "${TCB_ROOTS[@]}"; do
    awk -v r="$root" 'index($0, r) == 1' "$STREAM" | grep -E "$RE_ANY" || true
  done
}

case "${1:-gate}" in
  --list|list)
    build_stream
    print_sites
    exit 0
    ;;
  --print|print)
    compute_total
    print_breakdown
    echo "  ----------------"
    printf "  %-16s %s\n" "TOTAL" "$TOTAL"
    echo ""
    print_per_root
    if [ -s "$TEST_ONLY" ]; then
      echo ""
      print_test_only
    fi
    exit 0
    ;;
  --update-baseline)
    if [ -L "$BASELINE_FILE" ] || { [ -e "$BASELINE_FILE" ] && [ ! -f "$BASELINE_FILE" ]; }; then
      echo "FAIL: baseline path must be a regular file or absent: $BASELINE_FILE" >&2
      exit 1
    fi
    compute_total
    OLD="(none)"
    if [ -f "$BASELINE_FILE" ]; then
      if ! OLD="$(read_baseline)"; then
        echo "FAIL: baseline must contain one integer in 0..2147483647: $BASELINE_FILE" >&2
        exit 1
      fi
      if [ "$TOTAL" -gt "$OLD" ]; then
        echo "FAIL: refusing to raise the TCB panic baseline ($OLD -> $TOTAL)." >&2
        exit 1
      fi
      if [ "$TOTAL" -eq "$OLD" ]; then
        echo "Baseline unchanged: $OLD ($BASELINE_FILE)"
        exit 0
      fi
    fi
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
if ! BASELINE="$(read_baseline)"; then
  echo "FAIL: baseline must contain one integer in 0..2147483647: $BASELINE_FILE" >&2
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
  print_test_only
  echo ""
  echo "FAIL: TCB production-path panic surface GREW ($TOTAL > baseline $BASELINE)."
  echo "      A new unwrap/expect/panic/unreachable/unimplemented/todo landed in the"
  echo "      verifier's trusted core. Replace it with a propagated error/Result, or"
  echo "      (if it is a documented invariant) justify it in"
  echo "      docs/OPEN_ISSUES.md; the baseline updater never raises the ceiling."
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
