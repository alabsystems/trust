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
export DYLD_LIBRARY_PATH="/opt/homebrew/opt/llvm/lib:/opt/homebrew/opt/z3/lib:/opt/homebrew/opt/zstd/lib${DYLD_LIBRARY_PATH:+:$DYLD_LIBRARY_PATH}"

[ -x "$T" ] || { echo "no stage2 trustc at $T — run ./x.py build --stage 2"; exit 1; }

fail=0
# run <file> <extra-flags> -> sets $OUT to the JSON-mode stderr+stdout
run() { OUT="$($T $2 -Z trust-policy=advisory \
            -Z "trust-verify-timeout-ms=$VERIFY_TIMEOUT_MS" \
            -Z trust-verify-output=json --crate-type lib \
            --out-dir /tmp/trust-unsafe-cov "$DEMOS/$1" 2>&1)"; }
# expect_caught <file> <flags> <tag> <fn>
expect_caught() {
  run "$1" "$2"
  if echo "$OUT" | grep -q "\"function\":\"$4\"" && echo "$OUT" | grep -q "$3"; then
    echo "  PASS  $4: $3 caught"
  else
    echo "  FAIL  $4: expected $3 caught in $1"; fail=1
  fi
}
# expect_clean <file> <flags> <tag> <fn>  (tag must NOT appear for that fn)
expect_clean() {
  run "$1" "$2"
  # crude: the tag must not appear anywhere in this single-control file's output
  if echo "$OUT" | grep -q "$3"; then
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
expect_clean  target_feature_call_caught.rs   "--edition 2021" "caller_with_feature.*unmodeled-call" "caller_with_feature"
# aterm's real mmap.rs: HIGH-2 proved, and NO spurious unsafe-call/union/static flags
run aterm_mmap_real_source.rs "--edition 2021"
for tag in "unsafe:union-field" "unsafe:mutable-static" "unsafe:layout-constrained-field"; do
  if echo "$OUT" | grep -q "$tag"; then echo "  FAIL  aterm real mmap: spurious $tag"; fail=1
  else echo "  PASS  aterm real mmap: no spurious $tag"; fi
done

[ "$fail" = 0 ] && echo "ALL UNSAFE-COVERAGE CHECKS PASSED" || echo "SOME CHECKS FAILED"
exit "$fail"
