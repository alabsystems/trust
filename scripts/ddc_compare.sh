#!/usr/bin/env bash
# ddc_compare.sh — Diverse Double-Compilation (DDC) HARNESS SKELETON.
#
# ==========================================================================
#  WHAT THIS IS — AND WHAT IT IS NOT
# ==========================================================================
#  DDC (David A. Wheeler, "Fully Countering Trusting Trust through Diverse
#  Double-Compilation") defeats a Thompson trusting-trust backdoor by compiling
#  a compiler's SOURCE with TWO compilers of DISJOINT lineage and checking that
#  both, after a fixed-point re-compile, yield a BYTE-IDENTICAL stage-2 compiler.
#  A backdoor in one toolchain cannot survive into the other's output unless the
#  SAME backdoor independently exists in both — which disjoint lineages preclude.
#
#  This script wires up the MECHANISM: take two seed compilers A and B, build
#  Trust source with each (`x.py build --stage 2 --set build.rustc=...`), diff
#  the stage2 outputs. It is a reusable harness.
#
#  COMPILER B IS A STOCK-AS-ORACLE (docs/DECISION_QUEUE.md
#  D16: keep it, pinned; it gates nothing yet, a defect). B must not be of
#  Trust's lineage, so a stock rustc is this harness's purpose, not a migration
#  target. The token `upstream` is the ONE pinned oracle, rustup's `1.97.1`
#  (below src/stage0's floor since 2026-10-19, so x.py refuses it), found with
#  RUSTUP_AUTO_INSTALL=0 so a missing toolchain is never downloaded. When it is
#  absent the script prints `SKIPPED: NOT RUN: oracle 1.97.1 not installed` and
#  exits 0, which the comprehensive harness grades SKIP: never a pass, never a
#  block. The token `seed` is the stage0 bootstrap is configured with, a Trust
#  snapshot (src/stage0) since 2026-07-13.
#
#  IT IS *NOT* A THOMPSON RESULT BY ITSELF. `upstream` is an official rust-lang
#  build that never passed through a Trust build, but every rustc descends from
#  rust-lang's bootstrap chain, so disjointness further back is the operator's
#  claim (--disjoint), not this script's. Without it the output is labeled a
#  MECHANISM REHEARSAL: it proves the harness works and surfaces
#  nondeterminism. A Mes -> tinycc -> rustc chain and a second machine would
#  strengthen B.
#
#  This script REFUSES to print "Thompson defeated" under any circumstances. The
#  strongest claim it will emit is "mechanism rehearsal: A and B produced
#  byte-identical / differing stage2 trustc", annotated with the lineage caveat.
#
# ==========================================================================
#  USAGE
# ==========================================================================
#   scripts/ddc_compare.sh <rustc-A> <rustc-B> [--disjoint] [--dry-run]
#                          [--artifact PATH] [--log DIR]
#
#   <rustc-A>, <rustc-B>  a path to a rustc executable (its toolchain's `cargo`
#                         must sit beside it), or a token:
#                           "seed"     -> the configured stage0; no override
#                           "upstream" -> the pinned stock oracle, rustup 1.97.1
#   --disjoint            ASSERT (operator's responsibility) that A and B are
#                         lineage-disjoint. Without it, output is labeled
#                         "mechanism rehearsal (NOT lineage-disjoint)".
#   --dry-run             print the plan + the two build commands, build nothing.
#                         It prints `SKIPPED: NOT RUN: --dry-run ...`: a plan is
#                         not a comparison, so the harness never grades it PASS.
#   --artifact PATH       which stage2 artifact to diff; a glob is expanded after
#                         each build. May be repeated. Default: the trustc driver,
#                         librustc_driver-*.dylib (the compiler itself) and std's
#                         rlib.
#
#  Both builds hold a native Targo build-tree lease (build/ is exclusive): the lock
#  spans each `rm -rf` of stage2 and its x.py, which re-enters it through
#  TRUST_BUILD_LOCK_TOKEN. A held tree refuses with exit 2 before anything is
#  deleted.
#
# ==========================================================================
#  EXIT CODES
# ==========================================================================
#   0  the two stage2 outputs were byte-identical -- or, with a line
#      `SKIPPED: NOT RUN: ...`, the pinned oracle is absent and nothing ran
#   1  they differed (expected unless source build is fully deterministic AND
#      the two toolchains agree)
#   2  setup / build failure
#
# ==========================================================================
#  DETERMINISM PREREQUISITE
# ==========================================================================
#  DDC requires the source build to be REPRODUCIBLE first — otherwise A-vs-A
#  already differs and the comparison is meaningless. Validate that separately
#  with scripts/repro_build_selfcompare.sh BEFORE trusting a DDC mismatch as
#  "lineage divergence" rather than "build nondeterminism". This script applies
#  the same neutralizers (SOURCE_DATE_EPOCH + --remap-path-prefix).

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

HOST_TRIPLE="${TRUST_HOST_TRIPLE:-$(uname -m | sed 's/arm64/aarch64/')-apple-darwin}"
EPOCH="${TRUST_REPRO_EPOCH:-1000000000}"
LOGDIR="${TRUST_DDC_LOGDIR:-reports/ddc-rehearsal}"
DRY_RUN=0
DISJOINT=0
declare -a ARTIFACTS

# The one stock oracle compiler B may name (docs/DECISION_QUEUE.md D16).
STOCK_ORACLE=1.97.1

# Prints the seed rustc for a token or path; empty for `seed` (no override).
# Returns 1 when `upstream` is not installed. `rustup which` installs a missing
# toolchain unless RUSTUP_AUTO_INSTALL=0 (docs/KNOWN_HAZARDS.md, the seal-9192
# entry, item (e)).
resolve_rustc() {
  case "$1" in
    seed)     echo "" ;;
    upstream) RUSTUP_AUTO_INSTALL=0 rustup which --toolchain "$STOCK_ORACLE" rustc 2>/dev/null ;;
    *)        echo "$1" ;;
  esac
}

if [ $# -lt 2 ]; then
  sed -n '2,83p' "$0"; exit 2
fi
RUSTC_A_RAW="$1"; RUSTC_B_RAW="$2"; shift 2
while [ $# -gt 0 ]; do
  case "$1" in
    --disjoint) DISJOINT=1; shift ;;
    --dry-run)  DRY_RUN=1; shift ;;
    --artifact) ARTIFACTS+=("$2"); shift 2 ;;
    --log)      LOGDIR="$2"; shift 2 ;;
    -h|--help)  sed -n '2,83p' "$0"; exit 0 ;;
    *) echo "unknown arg: $1" >&2; exit 2 ;;
  esac
done

for raw in "$RUSTC_A_RAW" "$RUSTC_B_RAW"; do
  if [ "$raw" = upstream ] && ! resolve_rustc upstream >/dev/null; then
    echo "SKIPPED: NOT RUN: oracle $STOCK_ORACLE not installed (rustup toolchain $STOCK_ORACLE)"
    exit 0
  fi
done
RUSTC_A="$(resolve_rustc "$RUSTC_A_RAW")"
RUSTC_B="$(resolve_rustc "$RUSTC_B_RAW")"

if [ "${#ARTIFACTS[@]}" -eq 0 ]; then
  # trustc is a thin driver; the compiler is librustc_driver, and std is what
  # every program links. A backdoor would live in the last two.
  ARTIFACTS=("build/${HOST_TRIPLE}/stage2/bin/trustc"
             "build/${HOST_TRIPLE}/stage2/lib/librustc_driver-*.dylib"
             "build/${HOST_TRIPLE}/stage2/lib/rustlib/${HOST_TRIPLE}/lib/libstd-*.rlib")
fi

mkdir -p "$LOGDIR"
STAMP="$(date +%Y%m%d-%H%M%S)"
LOG="${LOGDIR}/ddc-${STAMP}.log"
log() { echo "$@" | tee -a "$LOG"; }

if [ "$DISJOINT" -eq 1 ]; then
  CLAIM_BANNER="DDC RUN (operator asserts A and B are lineage-DISJOINT)"
else
  CLAIM_BANNER="DDC MECHANISM REHEARSAL — NOT a Thompson result (A and B NOT asserted lineage-disjoint)"
fi

log "=================================================================="
log " ${CLAIM_BANNER}"
log "=================================================================="
log "rustc A : ${RUSTC_A_RAW} -> ${RUSTC_A:-<configured stage0>}"
log "rustc B : ${RUSTC_B_RAW} -> ${RUSTC_B:-<configured stage0>}"
log "host    : ${HOST_TRIPLE}"
log "epoch   : ${EPOCH}"
log "artifacts to diff:"; for a in "${ARTIFACTS[@]}"; do log "    ${a}"; done
log ""
if [ "$DISJOINT" -eq 0 ]; then
  log "NOTE: A and B are not asserted lineage-disjoint. A matching result proves"
  log "      the HARNESS + build determinism, NOT that Thompson trusting-trust is"
  log "      defeated (see the header)."
  log ""
fi

# Determinism neutralizers (same as repro_build_selfcompare.sh).
export SOURCE_DATE_EPOCH="$EPOCH"
export RUSTFLAGS="--remap-path-prefix=${REPO_ROOT}=/trust-source --remap-path-prefix=${HOME}=/home/trust"
export RUSTC_BOOTSTRAP=1
export LIBRARY_PATH="${LIBRARY_PATH:-/opt/homebrew/lib}"

# build/ is EXCLUSIVE (CLAUDE.md): hold the build lock across both rm + x.py
# pairs. x.py re-enters it through TRUST_BUILD_LOCK_TOKEN; a token inherited
# from a caller stays the caller's to release.
take_build_lock() {
  local inherited="${TRUST_BUILD_LOCK_TOKEN:-}" token
  token="$("${TARGO:-targo}" trust repo lock acquire --repo-root "$REPO_ROOT" --kind build --purpose "ddc_compare.sh: two stage2 rebuilds" \
             --pid $$ --contract "ddc_compare.sh deletes and rebuilds stage2 twice")" || true
  if [ -z "$token" ]; then
    log "ERROR: native build-tree acquisition refused; nothing deleted"
    exit 2
  fi
  export TRUST_BUILD_LOCK_TOKEN="$token"
  if [ "$token" != "$inherited" ]; then
    release_ddc_lock() {
      "${TARGO:-targo}" trust repo lock release "$TRUST_BUILD_LOCK_TOKEN" --repo-root "$REPO_ROOT" >/dev/null 2>&1
    }
    trap release_ddc_lock EXIT
  fi
}

build_with() {
  # $1 = seed rustc path (empty: the configured stage0), $2 = tag
  local rustc="$1" tag="$2"
  log "--- [${tag}] clean stage2 outputs, build Trust with rustc=${rustc:-<configured stage0>} ---"
  local cmd=(python3 x.py build --stage 2)
  if [ -n "$rustc" ]; then
    # bootstrap reads the seed from build.rustc/build.cargo; an exported RUSTC
    # reaches it only in bootstrap's own unit tests (config.rs, cfg!(test)).
    cmd+=(--set "build.rustc=${rustc}" --set "build.cargo=$(dirname "$rustc")/cargo")
  fi
  log "    SOURCE_DATE_EPOCH=${EPOCH} \\"
  log "    RUSTFLAGS='${RUSTFLAGS}' \\"
  log "    ${cmd[*]}"
  if [ "$DRY_RUN" -eq 1 ]; then
    log "    [dry-run] not executed"
    return 0
  fi
  if [ -n "$rustc" ] && { [ ! -x "$rustc" ] || [ ! -x "$(dirname "$rustc")/cargo" ]; }; then
    log "    ERROR: rustc or its sibling cargo not executable: ${rustc}"; exit 2
  fi
  # Full stage2 rebuild from the given seed compiler.
  rm -rf "build/${HOST_TRIPLE}/stage2" "build/${HOST_TRIPLE}/stage2-rustc" \
         "build/${HOST_TRIPLE}/stage2-codegen"
  if ! "${cmd[@]}" >>"${LOG}.build-${tag}" 2>&1; then
    log "    BUILD ${tag} FAILED — see ${LOG}.build-${tag}"; exit 2
  fi
}

# The snapshot name of an artifact pattern: its basename with `*` spelled `_`.
artifact_key() { basename "$1" | tr '*' '_'; }

snapshot() {
  # $1 = tag; copies the artifacts under LOGDIR with the tag. A glob must match
  # exactly one file (stage2 was deleted before the build).
  local tag="$1" a key
  local -a hits
  for a in "${ARTIFACTS[@]}"; do
    key="$(artifact_key "$a")"
    hits=()
    while IFS= read -r hit; do hits+=("$hit"); done < <(compgen -G "$a" || true)
    if [ "${#hits[@]}" -eq 1 ] && [ -f "${hits[0]}" ]; then
      cp "${hits[0]}" "${LOGDIR}/${key}.${tag}.${STAMP}"
      log "    snapshot ${tag}: ${hits[0]} sha256=$(shasum -a 256 "${hits[0]}" | awk '{print $1}')"
    else
      log "    snapshot ${tag}: ${#hits[@]} files match ${a} (want 1)"
    fi
  done
}

[ "$DRY_RUN" -eq 0 ] && take_build_lock
build_with "$RUSTC_A" A
[ "$DRY_RUN" -eq 0 ] && snapshot A
build_with "$RUSTC_B" B
[ "$DRY_RUN" -eq 0 ] && snapshot B

if [ "$DRY_RUN" -eq 1 ]; then
  log ""
  log "[dry-run] plan printed; no builds run, no comparison performed."
  echo "SKIPPED: NOT RUN: --dry-run (plan only; no build, no comparison)"
  exit 0
fi

log ""
log "=== STAGE2 OUTPUT COMPARISON ==="
RC=0
for a in "${ARTIFACTS[@]}"; do
  base="$(artifact_key "$a")"
  fa="${LOGDIR}/${base}.A.${STAMP}"
  fb="${LOGDIR}/${base}.B.${STAMP}"
  if [ ! -f "$fa" ] || [ ! -f "$fb" ]; then
    log "  ${base}: MISSING snapshot(s) — cannot compare"; RC=2; continue
  fi
  if cmp -s "$fa" "$fb"; then
    log "  ${base}: BYTE-IDENTICAL"
  else
    log "  ${base}: DIFFER"
    log "    sha256(A)=$(shasum -a 256 "$fa" | awk '{print $1}')"
    log "    sha256(B)=$(shasum -a 256 "$fb" | awk '{print $1}')"
    log "    first diff: $(cmp -l "$fa" "$fb" 2>/dev/null | head -1)"
    log "    differing bytes (common length): $(cmp -l "$fa" "$fb" 2>/dev/null | wc -l | tr -d ' ')"
    [ "$RC" -eq 0 ] && RC=1
  fi
done

log ""
if [ "$DISJOINT" -eq 1 ]; then
  if [ "$RC" -eq 0 ]; then
    log "RESULT: stage2 outputs byte-identical across asserted-disjoint A and B."
    log "        (Validity depends on the operator's --disjoint assertion being TRUE.)"
  else
    log "RESULT: stage2 outputs DIFFER. Either build nondeterminism (run"
    log "        repro_build_selfcompare.sh) or genuine lineage divergence."
  fi
else
  log "RESULT (MECHANISM REHEARSAL — NOT a Thompson result): see per-artifact lines."
  log "        A and B are not asserted lineage-disjoint; this validates the harness"
  log "        and surfaces nondeterminism only."
fi
log "log: ${LOG}"
exit "$RC"
