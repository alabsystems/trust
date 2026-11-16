#!/usr/bin/env bash
# regen_census_fixtures.sh — re-pin trust-platform-census's real dumps on a
# named trustc (platform-pass plan L0).
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# WHY THIS EXISTS
# ---------------
# The census tests (crates/trust-platform-census/tests/) read trust-ir TEXT
# that a stage1 trustc printed for the fixture sources beside it
# (tests/ir/<name>.rs -> tests/ir/<name>.trust_ir). The host pass will
# reproduce what those tests assert on the producer of the day, so the dumps
# must be regenerable from one command, and every dump must say which trustc
# printed it. The first dumps (stage1 771983b92) were made by hand with no
# recorded command line; this script is that command line.
#
# WHAT IT DOES
# ------------
# For each name in REGEN_NAMES (or the names given, each of which must be in
# it), from inside tests/ir so the module's `file 0` is the bare `<name>.rs`:
#
#   trustc -Ztrust-verify=off -Ztrust-ir-lower=on -Ztrust-dump=ir:<work>
#          --crate-type lib --crate-name <name> --edition 2021
#          --extern libc=<the trustc's own sysroot libc rlib (and its .rmeta)>
#          -Zcrate-attr=feature(rustc_private) <name>.rs
#
# and writes <work>/<name>.trust-ir.txt to tests/ir/<name>.trust_ir with one
# provenance line after the text-format header:
#
#   ; trustc <commit-hash> <commit-date>
#
# read from `trustc -vV`. The plan spells it `# trustc`; in trust-ir text a
# comment is `;`, and `; #word` is a DIRECTIVE the parser refuses unless the
# vocabulary names it, so the line is a plain `;` comment.
# tests/dump_provenance.rs refuses a dump without it.
#
# * A fixture that calls `upstream_spawn::` (adv3) also gets
#   --extern upstream_spawn=<tests/ir/upstream_spawn.rs built first as an
#   rlib by the same trustc>.
# * Edition 2021: the 771983b92 dumps capture `strip.bound` (an `(i32)`
#   closure environment), which is 2021's disjoint capture.
# * `-Zcrate-attr=feature(rustc_private)`: the sysroot's libc is built as a
#   std dependency, unstable-if-unmarked; the attribute is passed on the
#   command line so the fixture sources (and every span in them) stay
#   byte-identical.
#
# WHAT IT DOES NOT REGENERATE (and refuses if named)
# --------------------------------------------------
# * adv7: adv7m.trust_ir is a labeled hand edit of adv7's 771983b92 dump; the
#   pair stays together.
# * adv2t, adv7m (hand edits), synthetic (hand-written), aterm_uds/aterm_pty
#   (they need an aterm checkout: plan L3.0). They have no `<name>.rs` here
#   or are not in REGEN_NAMES.
#
# FAIL-CLOSED
# -----------
# A trustc whose -vV has no commit hash or date, a sysroot with zero or
# several libc rlibs, a failed compile, a missing or empty dump, a dump whose
# first line is not the text-format header, whose module is not <name>, or
# whose file table names anything but `<name>.rs` (a machine path):
# each stops the script before tests/ir is touched for that name. A name is
# replaced atomically (write beside, then rename).
#
# USAGE
# -----
#   scripts/trust_platform/regen_census_fixtures.sh --trustc <stage1 trustc> [name...]
#   scripts/trust_platform/regen_census_fixtures.sh --list
set -euo pipefail

# The dumps this script owns. tests/dump_provenance.rs reads this line: every
# name here must share one `; trustc` header (one re-pin, never a partial one).
REGEN_NAMES="census_shapes adv adv2 adv3 adv4 adv5 adv6 adv8 constructs"

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
IR_DIR="$REPO_ROOT/crates/trust-platform-census/tests/ir"
HEADER='; TrustIr text format v1'

die() { echo "regen_census_fixtures: $*" >&2; exit 1; }

usage() {
  sed -n '/^# USAGE/,/^set -euo/p' "${BASH_SOURCE[0]}" | sed '1,2d;$d' | sed 's/^# \{0,1\}//' >&2
  exit 2
}

trustc=""
names=()
while [ $# -gt 0 ]; do
  case "$1" in
    --trustc) [ $# -ge 2 ] || usage; trustc="$2"; shift 2 ;;
    --trustc=*) trustc="${1#--trustc=}"; shift ;;
    --list) echo "$REGEN_NAMES"; exit 0 ;;
    -h|--help) usage ;;
    -*) die "unknown option \`$1\`" ;;
    *) names+=("$1"); shift ;;
  esac
done
[ -n "$trustc" ] || usage
[ -x "$trustc" ] || die "--trustc \`$trustc\` is not an executable"
if [ ${#names[@]} -eq 0 ]; then
  read -r -a names <<<"$REGEN_NAMES"
fi
for n in "${names[@]}"; do
  case " $REGEN_NAMES " in
    *" $n "*) ;;
    *) die "\`$n\` is not a regenerated dump (REGEN_NAMES: $REGEN_NAMES)" ;;
  esac
  [ -f "$IR_DIR/$n.rs" ] || die "no source $IR_DIR/$n.rs"
done

# Provenance: the trustc's own answer, never a document.
vv="$("$trustc" -vV)" || die "\`$trustc -vV\` failed"
sha="$(printf '%s\n' "$vv" | sed -n 's/^commit-hash: //p')"
date="$(printf '%s\n' "$vv" | sed -n 's/^commit-date: //p')"
host="$(printf '%s\n' "$vv" | sed -n 's/^host: //p')"
[[ "$sha" =~ ^[0-9a-f]{40}$ ]] || die "\`$trustc -vV\` names no commit hash (got \`$sha\`)"
[[ "$date" =~ ^[0-9]{4}-[0-9]{2}-[0-9]{2}$ ]] || die "\`$trustc -vV\` names no commit date (got \`$date\`)"
[ -n "$host" ] || die "\`$trustc -vV\` names no host"
provenance="; trustc $sha $date"

sysroot="$("$trustc" --print sysroot)" || die "\`$trustc --print sysroot\` failed"
shopt -s nullglob
rlibs=("$sysroot/lib/rustlib/$host/lib/"liblibc-*.rlib)
shopt -u nullglob
[ ${#rlibs[@]} -eq 1 ] \
  || die "expected exactly one liblibc-*.rlib in $sysroot/lib/rustlib/$host/lib, found ${#rlibs[@]}"
libc_rlib="${rlibs[0]}"
# A sysroot built with split metadata ships a stub rlib beside the full .rmeta
# ("only metadata stub found for `rlib` dependency `libc`"): name both.
extern_libc=(--extern "libc=$libc_rlib")
if [ -f "${libc_rlib%.rlib}.rmeta" ]; then
  extern_libc+=(--extern "libc=${libc_rlib%.rlib}.rmeta")
fi

work="$(mktemp -d "${TMPDIR:-/tmp}/regen_census_fixtures.XXXXXX")"
trap 'rm -rf "${work:?}"' EXIT

echo "trustc  $trustc"
echo "        $provenance"
echo "libc    $libc_rlib"

# adv3.rs calls into an upstream crate: build tests/ir/upstream_spawn.rs (the
# crate tests/ir/nm/libupstream_spawn.nm was read from) with the same trustc,
# and name it to every fixture whose source uses it.
upstream_rlib=""
build_upstream() {
  [ -n "$upstream_rlib" ] && return 0
  mkdir -p "$work/deps"
  (
    cd "$IR_DIR"
    "$trustc" -Ztrust-verify=off --crate-type rlib --crate-name upstream_spawn --edition 2021 \
      "${extern_libc[@]}" '-Zcrate-attr=feature(rustc_private)' \
      --out-dir "$work/deps" upstream_spawn.rs
  ) >"$work/deps/compile.log" 2>&1 || {
    cat "$work/deps/compile.log" >&2
    die "upstream_spawn: trustc failed (log above)"
  }
  upstream_rlib="$work/deps/libupstream_spawn.rlib"
  [ -f "$upstream_rlib" ] || die "upstream_spawn: no $upstream_rlib"
}

for n in "${names[@]}"; do
  mkdir -p "$work/$n/out"
  externs=("${extern_libc[@]}")
  if grep -q 'upstream_spawn::' "$IR_DIR/$n.rs"; then
    build_upstream
    externs+=(--extern "upstream_spawn=$upstream_rlib")
  fi
  (
    cd "$IR_DIR"
    "$trustc" -Ztrust-verify=off -Ztrust-ir-lower=on "-Ztrust-dump=ir:$work/$n/ir" \
      --crate-type lib --crate-name "$n" --edition 2021 \
      "${externs[@]}" '-Zcrate-attr=feature(rustc_private)' \
      --out-dir "$work/$n/out" "$n.rs"
  ) >"$work/$n/compile.log" 2>&1 || {
    cat "$work/$n/compile.log" >&2
    die "$n: trustc failed (log above)"
  }
  dump="$work/$n/ir/$n.trust-ir.txt"
  [ -s "$dump" ] || { cat "$work/$n/compile.log" >&2; die "$n: no dump at $dump"; }
  first="$(head -n 1 "$dump")"
  [ "$first" = "$HEADER" ] || die "$n: the dump's first line is \`$first\`, not \`$HEADER\`"
  grep -qx "module \"$n\"" "$dump" || die "$n: the dump is not module \"$n\""
  grep -q '^; trustc ' "$dump" && die "$n: the producer already printed a \`; trustc\` line"
  # A committed dump carries no machine path (scripts/check_fixture_span_paths.py).
  if grep -E '^file [0-9]+ "' "$dump" | grep -vqx "file [0-9]* \"$n.rs\""; then
    grep -E '^file [0-9]+ "' "$dump" >&2
    die "$n: the dump names a source file other than \`$n.rs\` (above)"
  fi
  out="$IR_DIR/$n.trust_ir"
  {
    printf '%s\n' "$HEADER" "$provenance"
    tail -n +2 "$dump"
  } >"$out.regen"
  mv "$out.regen" "$out"
  echo "wrote   tests/ir/$n.trust_ir ($(wc -l <"$out" | tr -d ' ') lines)"
  if [ -s "$work/$n/compile.log" ]; then
    echo "        (trustc printed $(wc -l <"$work/$n/compile.log" | tr -d ' ') lines; first: $(head -n 1 "$work/$n/compile.log"))"
  fi
done
