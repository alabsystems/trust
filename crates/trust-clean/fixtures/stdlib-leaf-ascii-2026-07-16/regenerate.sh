#!/bin/sh
# Regenerate the stdlib-leaf-ascii-2026-07-16 dumps + verdicts from THIS repo's
# own library/core (Trust ships the stdlib — the certified code is code we
# compile). 24 functions: the `is_ascii_*` classification-predicate family on
# `char` and `u8`.
#
# Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0 OR MIT
#
# EXTRACTION PATH (see PROVENANCE.md for full honesty notes):
#   * Core leaf-fn MIR is NOT reachable from a downstream probe crate (the MIR
#     dump records LOCAL bodies only; core callees stay opaque Call terminators).
#     A fixture crate that *calls* `x.is_ascii_digit()` dumps only the caller.
#     So we compile library/core ITSELF, as census-core-m5-2026-07-07 did.
#   * The CURRENT dump-capable stage2 trustc (2026-07-15, `7df54072f`) forces an
#     `int_log10` `const { .. }` promotion cycle DURING the trust verify pass's
#     borrowck (a plain `trustc lib.rs` with NO trust flags compiles core fine;
#     ANY trust-dump/verify flag trips it). We therefore compile a COPY of
#     library/core with ONE surgical workaround in the UNRELATED module
#     `num/imp/int_log10.rs` (see int_log10-workaround.diff): the two
#     `assert_unchecked(.. const { .. })` optimizer HINTS are removed. This does
#     not change any function's result and does not touch any certified body —
#     the 24 ascii predicates live in `num/mod.rs` + `char/methods.rs` and are
#     byte-identical to HEAD library/core.
#
# Pass `--validate-only` to hash-check and regrade the committed 24 dumps with
# freshly built production tools, without requiring the historical extractor.
set -eu
HERE="$(cd "$(dirname "$0")" && pwd)"
REPO=$(cd "${REPO:-$HERE/../../../..}" && pwd)
TRUSTC=${TRUSTC:-$REPO/build/host/stage2/bin/trustc} # prebuilt stage2; do not rebuild here
VALIDATE_ONLY=0
case "${1:-}" in
  --validate-only)
    VALIDATE_ONLY=1
    shift
    ;;
  "") ;;
  *)
    echo "usage: $0 [--validate-only]" >&2
    exit 2
    ;;
esac
test "$#" -eq 0 || {
  echo "usage: $0 [--validate-only]" >&2
  exit 2
}
TMP=$(mktemp -d)
CANDIDATE_ROOT="$HERE/.regenerate-ascii.$$"
BACKUP_ROOT="$HERE/.dumps.previous.$$"
LOCK_DIR="$HERE/.regenerate-ascii.lock"
VALIDATION_TARGET_DIR=${TRUST_ASCII_VALIDATION_TARGET_DIR:-$TMP/cargo-target}
cleanup() {
  if test -d "$BACKUP_ROOT"; then
    if ! test -d "$HERE/dumps"; then
      mv "$BACKUP_ROOT" "$HERE/dumps"
    else
      rm -rf "$BACKUP_ROOT"
    fi
  fi
  rm -rf "$TMP" "$CANDIDATE_ROOT"
  rm -rf "$LOCK_DIR"
}
if ! mkdir "$LOCK_DIR"; then
  echo "error: another ASCII corpus validation/regeneration is already running" >&2
  rm -rf "$TMP"
  exit 1
fi
trap cleanup EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM

hash_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  else
    shasum -a 256 "$1" | awk '{print $1}'
  fi
}

check_manifest() {
  base=$1
  manifest=$2
  if command -v sha256sum >/dev/null 2>&1; then
    (cd "$base" && sha256sum -c "$manifest")
  else
    (cd "$base" && shasum -a 256 -c "$manifest")
  fi
}

check_manifest "$REPO" "$HERE/SOURCE.sha256"

if test "$VALIDATE_ONLY" -eq 0; then
# Fail closed unless this is the recorded trustc launcher. The historical
# driver/sysroot and external library bundle was not retained, so launcher
# equality alone is not full toolchain provenance; the canonicalized dump
# hashes below are the final equality check.
test -x "$TRUSTC" || {
  echo "error: dump-capable stage2 trustc not found at $TRUSTC (set TRUSTC explicitly)" >&2
  exit 1
}
expected_version=$(sed -n 's/^trustc version: //p' "$HERE/TOOLCHAIN.sha256")
expected_trustc_hash=$(sed -n 's/^trustc binary sha256: //p' "$HERE/TOOLCHAIN.sha256")
actual_version=$("$TRUSTC" --version)
actual_trustc_hash=$(hash_file "$TRUSTC")
test "$actual_version" = "$expected_version" || {
  echo "error: trustc version drift: $actual_version" >&2
  exit 1
}
test "$actual_trustc_hash" = "$expected_trustc_hash" || {
  echo "error: trustc binary hash drift: $actual_trustc_hash" >&2
  exit 1
}

# 1. materialise the patched core copy (siblings symlinked for `#[path=..]`).
cp -R "$REPO/library/core" "$TMP/L-core"
mkdir -p "$TMP/L"
mv "$TMP/L-core" "$TMP/L/core"
ln -s "$REPO/library/stdarch"       "$TMP/L/stdarch"
ln -s "$REPO/library/portable-simd" "$TMP/L/portable-simd"
# Apply the one recorded workaround. A failed or previously-applied patch is a
# source mismatch and must not silently produce a partial corpus.
patch --forward -p0 -d "$TMP/L/core" < "$HERE/int_log10-workaround.diff"

# 2. dump ALL of the patched core (the tail-of-run delayed-bug ICE about
#    NonZero<T>::Metadata is emitted AFTER every body is written — dumps intact).
mkdir -p "$TMP/dump"
TRUST_LIBRARY_PATH=${TRUST_LIBRARY_PATH:-/opt/homebrew/lib}
test -d "$TRUST_LIBRARY_PATH" || {
  echo "error: recorded extraction LIBRARY_PATH is unavailable: $TRUST_LIBRARY_PATH" >&2
  exit 1
}
set +e
LIBRARY_PATH="$TRUST_LIBRARY_PATH" \
  "$TRUSTC" --edition 2024 --crate-type lib --crate-name core \
  -Z"trust-dump=mir:$TMP/dump" -Ztrust-policy=advisory \
  -o "$TMP/core.rlib" "$TMP/L/core/src/lib.rs" \
  > "$TMP/trustc.stdout" 2> "$TMP/trustc.stderr"
dump_status=$?
set -e
echo "trustc exit=$dump_status; dumped $(find "$TMP/dump" -type f -name '*.json' | wc -l) bodies"
if test "$dump_status" -ne 0; then
  if ! grep -F "NonZero" "$TMP/trustc.stderr" >/dev/null || \
     ! grep -F "normaliz" "$TMP/trustc.stderr" >/dev/null; then
    echo "error: trustc failed without the recorded post-dump NonZero normalization bug" >&2
    tail -n 80 "$TMP/trustc.stderr" >&2
    exit 1
  fi
  echo "accepted recorded post-dump NonZero normalization failure; exact corpus checks follow" >&2
fi

# 3. Slice into a candidate directory (rename hash filenames -> def_path).
# The checked-in corpus is replaced only after every structural/hash/verdict
# check below succeeds.
mkdir -p "$CANDIDATE_ROOT/dumps"
for f in "$TMP/dump"/*.json; do
  dp=$(python3 -c "import json,sys;print(json.load(open(sys.argv[1])).get('def_path',''))" "$f")
  case "$dp" in
    "num::<impl u8>::is_ascii"*|"char::methods::<impl char>::is_ascii"*)
      san=$(printf '%s' "$dp" | sed 's/::/__/g')
      cp "$f" "$CANDIDATE_ROOT/dumps/$san.json" ;;
  esac
done
python3 "$HERE/canonicalize_dump_paths.py" "$CANDIDATE_ROOT/dumps"
else
  # Validation-only mode grades the immutable checked-in corpus with freshly
  # rebuilt production tools; it does not require or replace historical dumps.
  mkdir -p "$CANDIDATE_ROOT"
  cp -R "$HERE/dumps" "$CANDIDATE_ROOT/dumps"
fi

dump_count=$(find "$CANDIDATE_ROOT/dumps" -type f -name '*.json' | wc -l | tr -d ' ')
test "$dump_count" -eq 24 || {
  echo "error: expected exactly 24 ASCII-family dumps, found $dump_count" >&2
  exit 1
}

# The result table is also the canonical expected def-path inventory. Reject a
# missing, duplicate, renamed, or extra body before grading it.
tail -n +2 "$HERE/results.tsv" | cut -f1 | sort > "$TMP/expected-paths"
for f in "$CANDIDATE_ROOT"/dumps/*.json; do
  python3 -c "import json,sys; print(json.load(open(sys.argv[1]))['def_path'])" "$f"
done | sort > "$TMP/actual-paths"
test "$(wc -l < "$TMP/expected-paths" | tr -d ' ')" -eq 24
test "$(uniq "$TMP/expected-paths" | wc -l | tr -d ' ')" -eq 24
cmp "$TMP/expected-paths" "$TMP/actual-paths"
cp "$HERE/results.tsv" "$CANDIDATE_ROOT/results.tsv"
check_manifest "$CANDIDATE_ROOT" "$HERE/ARTIFACTS.sha256"
echo "sliced and hash-verified 24 ASCII-family dumps into dumps/"

# 4. Rebuild both production-facing census tools from this checkout, run them,
# and compare every recorded verdict/lane/kernel/safety field. This validates
# `results.tsv`; it does not merely print suggested commands.
CARGO_TARGET_DIR="$VALIDATION_TARGET_DIR" CARGO_NET_OFFLINE=${CARGO_NET_OFFLINE:-true} \
  RUSTC_BOOTSTRAP=1 \
  cargo build --release --locked -p trust-clean --manifest-path "$REPO/crates/Cargo.toml" \
  --bin ff-gate-diagnose-2026-07-10 --bin census-2026-07-06
TOOLS="$VALIDATION_TARGET_DIR/release"
"$TOOLS/ff-gate-diagnose-2026-07-10" "$CANDIDATE_ROOT/dumps" \
  > "$TMP/ff-gate.tsv" 2> "$TMP/ff-gate.stderr"
TRUST_CENSUS_BUDGET_SECS=${TRUST_CENSUS_BUDGET_SECS:-90} \
  "$TOOLS/census-2026-07-06" "$CANDIDATE_ROOT/dumps" \
  > "$TMP/census.tsv" 2> "$TMP/census.stderr"
if grep -F "# WARNING:" "$TMP/census.stderr" >/dev/null; then
  echo "error: census reported an incomplete or unreliable row" >&2
  grep -F "# WARNING:" "$TMP/census.stderr" >&2
  exit 1
fi
expected_ff_header='def_path	cluster_tag	via_ir_shape	via_ir_safety	via_mirsem_shape	via_mirsem_sl_safety_discharged	via_mirsem_call_requires	via_mirsem_loop_full	fully_faithful'
expected_census_header='def_path	total	inhabited	type_grounded_not_inhabited	not_grounded	kernel_rejected	safety_obligations	safety_discharged	fully_faithful	via_trustir	mirsem_fallback	declined	expr_fold_decline'
test "$(sed -n '1p' "$TMP/ff-gate.tsv")" = "$(printf '%b' "$expected_ff_header")" || {
  echo "error: FF-gate TSV schema drift" >&2
  exit 1
}
test "$(sed -n '1p' "$TMP/census.tsv")" = "$(printf '%b' "$expected_census_header")" || {
  echo "error: census TSV schema drift" >&2
  exit 1
}

awk -F '\t' '
  NR == FNR { if (FNR > 1) expected[$1] = $2; next }
  FNR == 1 { next }
  {
    got = ($9 == "true" ? "FULLY_FAITHFUL" : $2)
    if (!($1 in expected) || got != expected[$1]) {
      print "FF-gate mismatch for " $1 ": expected " expected[$1] ", got " got > "/dev/stderr"
      bad = 1
    }
    if (++count[$1] != 1) { print "duplicate FF-gate row " $1 > "/dev/stderr"; bad = 1 }
    seen[$1] = 1
  }
  END {
    for (p in expected) if (!(p in seen)) { print "FF-gate missing " p > "/dev/stderr"; bad = 1 }
    exit bad
  }
' "$HERE/results.tsv" "$TMP/ff-gate.tsv"

awk -F '\t' '
  NR == FNR {
    if (FNR > 1) {
      verdict[$1] = $2; lane[$1] = $3; rejected[$1] = $4
      safety[$1] = $5; discharged[$1] = $6
    }
    next
  }
  FNR == 1 { next }
  {
    got_verdict = ($9 == 1 ? "FULLY_FAITHFUL" : "SHAPE_GAP")
    got_lane = ($10 == 1 ? "via_trustir" : ($11 == 1 ? "mirsem" : "-"))
    if (!($1 in verdict) || $2 != 1 || got_verdict != verdict[$1] || got_lane != lane[$1] ||
        $6 != rejected[$1] || $7 != safety[$1] || $8 != discharged[$1] || $12 != 0) {
      print "census mismatch for " $1 > "/dev/stderr"
      bad = 1
    }
    if (++count[$1] != 1) { print "duplicate census row " $1 > "/dev/stderr"; bad = 1 }
    seen[$1] = 1
  }
  END {
    for (p in verdict) if (!(p in seen)) { print "census missing " p > "/dev/stderr"; bad = 1 }
    exit bad
  }
' "$HERE/results.tsv" "$TMP/census.tsv"

if test "$VALIDATE_ONLY" -eq 0; then
  mv "$HERE/dumps" "$BACKUP_ROOT"
  if mv "$CANDIDATE_ROOT/dumps" "$HERE/dumps"; then
    rm -rf "$BACKUP_ROOT"
  else
    mv "$BACKUP_ROOT" "$HERE/dumps"
    exit 1
  fi
fi
fully_faithful=$(awk -F '\t' 'NR > 1 && $2 == "FULLY_FAITHFUL" { n++ } END { print n + 0 }' "$HERE/results.tsv")
kernel_rejected=$(awk -F '\t' 'NR > 1 { n += $4 } END { print n + 0 }' "$HERE/results.tsv")
echo "validated machine fields: $fully_faithful/24 fully faithful, kernel_rejected=$kernel_rejected; wall tags are manual"
