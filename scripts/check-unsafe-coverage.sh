#!/usr/bin/env bash
# Reproducible completeness check for Trust's unsafe-operation coverage.
#
# Runs the stage2 `trustc` over the demo fixtures and asserts that EVERY
# user-expressible unsafe-operation kind is CAUGHT fail-closed (its obligation
# tag appears), and that the discriminating CONTROLS (safe calls, immutable
# statics, in-feature target-feature calls) are NOT flagged. This pins the
# "prove no others exist" (catch direction) result so it cannot silently
# regress. The demo fixtures live in examples/unsafe-coverage/.
#
# Usage:  scripts/check-unsafe-coverage.sh [verify-timeout-ms]
set -uo pipefail

if [ "$#" -gt 1 ]; then
  echo "usage: $0 [verify-timeout-ms]" >&2
  exit 2
fi
if [ "${TRUST_VERIFY_TIMEOUT_MS+x}" = x ]; then
  echo "TRUST_VERIFY_TIMEOUT_MS is retired; pass verify-timeout-ms as the optional positional argument" >&2
  exit 2
fi

VERIFY_TIMEOUT_MS="${1:-15000}"
case "$VERIFY_TIMEOUT_MS" in
  ''|*[!0-9]*|0) echo "verify-timeout-ms must be a positive integer" >&2; exit 2 ;;
esac

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
HOST="$("$REPO"/build/*/stage2/bin/trustc -vV 2>/dev/null | sed -n 's/^host: //p' | head -1)"
HOST="${HOST:-aarch64-apple-darwin}"
T="$REPO/build/$HOST/stage2/bin/trustc"
DEMOS="$REPO/examples/unsafe-coverage"
BREW_PREFIX="${TRUST_BREW_PREFIX:-$(brew --prefix 2>/dev/null || echo /opt/homebrew)}"
export DYLD_LIBRARY_PATH="$BREW_PREFIX/opt/llvm/lib:$BREW_PREFIX/opt/z3/lib:$BREW_PREFIX/opt/zstd/lib${DYLD_LIBRARY_PATH:+:$DYLD_LIBRARY_PATH}"

[ -x "$T" ] || { echo "no stage2 trustc at $T — run ./x.py build --stage 2"; exit 1; }

fail=0
# run <file> <extra-flags> -> sets $OUT to the JSON-mode stderr+stdout
run() { OUT="$($T $2 -Z trust-policy=advisory \
            -Z "trust-verify-timeout-ms=$VERIFY_TIMEOUT_MS" \
            -Z trust-verify-output=json --crate-type lib \
            --out-dir /tmp/trust-unsafe-cov "$DEMOS/$1" 2>&1)"; }
# The transport's `function` field is crate-qualified (`<crate>::<fn>`); the
# trailing quote anchors the match so `caller` cannot match `safe_caller`.
fn_row() { echo "$OUT" | grep '"type":"function_result"' | grep -E "\"function\":\"([A-Za-z0-9_]+::)*$1\""; }

# expect_caught <file> <flags> <tag> <fn>
expect_caught() {
  run "$1" "$2"
  # tag must land on THAT fn's own row: a whole-output grep passes when the tag
  # fired on some other fn in the same fixture, which is a false-proof window.
  ROW="$(fn_row "$4")"
  if [ -n "$ROW" ] && echo "$ROW" | grep -q "$3"; then
    echo "  PASS  $4: $3 caught"
  else
    echo "  FAIL  $4: expected $3 caught in $1"; fail=1
  fi
}
# expect_clean <file> <flags> <tag> <fn>  (fn must be reported, and its row must NOT carry the tag)
expect_clean() {
  run "$1" "$2"
  ROW="$(fn_row "$4")"
  if [ -z "$ROW" ]; then
    # absent fn would otherwise pass vacuously — a control that never ran proves nothing
    echo "  FAIL  $4: no function_result row in $1"; fail=1
  elif echo "$ROW" | grep -q "$3"; then
    echo "  FAIL  $4: $3 should NOT fire (false positive) in $1"; fail=1
  else
    echo "  PASS  $4: $3 correctly not flagged"
  fi
}

echo "== unsafe-operation catch completeness =="
expect_caught inline_asm_caught.rs            ""              "unsafe:asm"                    "double_via_asm"
expect_caught union_field_access_caught.rs    ""              "unsafe:union-field"            "float_to_bits"
expect_caught mutable_static_caught.rs        ""              "unsafe:mutable-static"         "bump"
expect_caught unmodeled_unsafe_call_caught.rs ""              "unsafe:unmodeled-call"         "caller"
expect_caught target_feature_call_caught.rs   "--edition 2021" "unsafe:unmodeled-call"        "caller_without_feature"

echo "== discriminating controls (must NOT be flagged) =="
expect_clean  target_feature_call_caught.rs   "--edition 2021" "unsafe:unmodeled-call"        "caller_with_feature"
# aterm's real mmap.rs as a false-positive control: NO spurious union/static/
# layout flags. (Whether HIGH-2 is *proved* here is NOT asserted — see
# docs/high2-obligation-demo.md for the layered blockers.)
run aterm_mmap_real_source.rs "--edition 2021"
ROWS="$(echo "$OUT" | grep -c '"type":"function_result"')"
case "$ROWS" in ''|*[!0-9]*) ROWS=0 ;; esac
if [ "$ROWS" -eq 0 ]; then
  # no rows => fixture did not compile or emitted nothing; a control that never
  # ran proves nothing (same guard as expect_clean above)
  echo "  FAIL  aterm real mmap: no function_result rows in aterm_mmap_real_source.rs"; fail=1
else
  for tag in "unsafe:union-field" "unsafe:mutable-static" "unsafe:layout-constrained-field"; do
    if echo "$OUT" | grep -q "$tag"; then echo "  FAIL  aterm real mmap: spurious $tag"; fail=1
    else echo "  PASS  aterm real mmap: no spurious $tag"; fi
  done
fi

[ "$fail" = 0 ] && echo "ALL UNSAFE-COVERAGE CHECKS PASSED" || echo "SOME CHECKS FAILED"
exit "$fail"
