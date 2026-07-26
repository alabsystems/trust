#!/usr/bin/env bash
# repro_build_selfcompare.sh — single-machine reproducible-build SELF-COMPARE.
#
# PURPOSE
#   Build one determinism-relevant Trust artifact TWICE, INDEPENDENTLY, with the
#   standard determinism neutralizers applied, then BYTE-COMPARE the two outputs.
#   This is the DDC PREREQUISITE: "same source => same bytes" must be checkable
#   before Diverse Double-Compilation means anything.
#
#   This is NOT a Thompson result and NOT a DDC run. It measures whether a single
#   toolchain reproduces its own output. (See scripts/ddc_compare.sh for the DDC
#   mechanism rehearsal.)
#
# WHAT IS COMPARED (default)
#   The verified codegen backend dylib:
#     build/<host>/stage2-codegen/<host>/release/librustc_codegen_trust_cg.dylib
#   This is the genuinely-compiled artifact (the sysroot copy is a hardlink of it),
#   and it is the component whose emit-determinism is already unit-tested
#   (crates/trust-cg-bridge/tests/emit_determinism.rs). The self-compare lifts that
#   from "object writer is deterministic in-process" to "the whole crate dylib
#   reproduces across two independent compiler invocations."
#
# INDEPENDENCE
#   A cached rebuild reuses artifacts and is trivially identical — NOT a real test.
#   Between builds we DELETE the stage2 codegen build dir + the emitted dylib so the
#   crate is genuinely recompiled and relinked. Stage0/stage1 are left intact (this
#   keeps each rebuild to a few minutes, not a full clean stage2).
#
# NEUTRALIZERS (applied via env; bootstrap.py preserves a pre-set RUSTFLAGS,
#   see src/bootstrap/bootstrap.py:1301-1303)
#   - SOURCE_DATE_EPOCH      : fixed epoch, kills timestamp fields
#   - --remap-path-prefix    : repo root + $HOME -> stable logical paths
#   (rustc 1.96.0 already defaults embed-source=no and randomize-layout=no, so no
#    explicit flag is needed for those; -C embed-source is NOT a valid option here.)
#
# HONESTY
#   This script reports the REAL result. If the two builds differ, it prints the
#   sha256s, the first differing byte offset, and a section guess, and EXITS 1.
#   It does not massage, retry, or hide differences.
#
# USAGE
#   scripts/repro_build_selfcompare.sh [--artifact PATH] [--build-path X.PY-PATH]
#                                      [--keep] [--log DIR]
#   Env overrides:
#     TRUST_REPRO_EPOCH      (default 1000000000)
#     TRUST_REPRO_LOGDIR     (default reports/repro-selfcompare)
#
# EXIT CODES
#   0  byte-identical (reproducible)
#   1  differ (nondeterminism present — the honest work-list)
#   2  setup/build failure

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

HOST_TRIPLE="${TRUST_HOST_TRIPLE:-$(uname -m | sed 's/arm64/aarch64/')-apple-darwin}"
BUILD_PATH="compiler/rustc_codegen_trust_cg"
# When building only the codegen-backend PATH TARGET (not a full stage2), bootstrap
# emits the freshly-compiled dylib into stage2-rustc/.../release/, NOT into the
# stage2-codegen sysroot tree (that tree is assembled only by a full stage2 build).
# So this is the genuine compiled artifact to byte-compare.
ARTIFACT="build/${HOST_TRIPLE}/stage2-rustc/${HOST_TRIPLE}/release/librustc_codegen_trust_cg.dylib"
RELEASE_DIR="build/${HOST_TRIPLE}/stage2-rustc/${HOST_TRIPLE}/release"
# Crate name token for surgical fingerprint/dep removal (deps stay cached).
CRATE_TOKEN="rustc_codegen_trust_cg"
EPOCH="${TRUST_REPRO_EPOCH:-1000000000}"
LOGDIR="${TRUST_REPRO_LOGDIR:-reports/repro-selfcompare}"
KEEP=0

while [ $# -gt 0 ]; do
  case "$1" in
    --artifact) ARTIFACT="$2"; shift 2 ;;
    --build-path) BUILD_PATH="$2"; shift 2 ;;
    --log) LOGDIR="$2"; shift 2 ;;
    --keep) KEEP=1; shift ;;
    -h|--help) sed -n '2,48p' "$0"; exit 0 ;;
    *) echo "unknown arg: $1" >&2; exit 2 ;;
  esac
done

mkdir -p "$LOGDIR"
STAMP="$(date +%Y%m%d-%H%M%S)"
MATCHLOG="${LOGDIR}/selfcompare-${STAMP}.log"

export SOURCE_DATE_EPOCH="$EPOCH"
export RUSTFLAGS="--remap-path-prefix=${REPO_ROOT}=/trust-source --remap-path-prefix=${HOME}=/home/trust"
export RUSTC_BOOTSTRAP=1
export LIBRARY_PATH="${LIBRARY_PATH:-/opt/homebrew/lib}"

log() { echo "$@" | tee -a "$MATCHLOG"; }

log "=== repro_build_selfcompare ${STAMP} ==="
log "repo_root      : ${REPO_ROOT}"
log "host_triple    : ${HOST_TRIPLE}"
log "build_path     : ${BUILD_PATH}"
log "artifact       : ${ARTIFACT}"
log "SOURCE_DATE_EPOCH: ${EPOCH}"
log "RUSTFLAGS      : ${RUSTFLAGS}"
log ""

build_once() {
  local tag="$1"
  log "--- build ${tag}: forcing independence (surgical: drop ${CRATE_TOKEN} fingerprint + dylib, keep deps cached) ---"
  # Remove ONLY the codegen-backend crate's own fingerprint + emitted dylib + its
  # dep-dir dylib. Its dependency rlibs stay cached, so cargo recompiles+relinks
  # JUST this crate — a genuine independent rebuild without a 6+ min full graph
  # rebuild. (Removing the whole stage2-rustc tree also works but is far slower.)
  rm -rf "${RELEASE_DIR}/.fingerprint/${CRATE_TOKEN}-"* 2>/dev/null || true
  rm -f  "${RELEASE_DIR}/deps/lib${CRATE_TOKEN}-"*.dylib 2>/dev/null || true
  rm -f  "${RELEASE_DIR}/lib${CRATE_TOKEN}.dylib" "${RELEASE_DIR}/lib${CRATE_TOKEN}.d" 2>/dev/null || true
  rm -f  "$ARTIFACT"
  log "--- build ${tag}: x.py build --stage 2 ${BUILD_PATH} ---"
  local t0 t1
  t0="$(date +%s)"
  if ! python3 x.py build --stage 2 "$BUILD_PATH" >>"${MATCHLOG}.build-${tag}" 2>&1; then
    log "BUILD ${tag} FAILED — see ${MATCHLOG}.build-${tag}"
    exit 2
  fi
  t1="$(date +%s)"
  if [ ! -f "$ARTIFACT" ]; then
    log "ARTIFACT MISSING after build ${tag}: ${ARTIFACT}"
    exit 2
  fi
  log "build ${tag} done in $((t1 - t0))s"
}

build_once A
SHA_A="$(shasum -a 256 "$ARTIFACT" | awk '{print $1}')"
SIZE_A="$(stat -f%z "$ARTIFACT" 2>/dev/null || stat -c%s "$ARTIFACT")"
cp "$ARTIFACT" "${LOGDIR}/artifact-A-${STAMP}.bin"
log "sha256(A) = ${SHA_A}  size=${SIZE_A}"

build_once B
SHA_B="$(shasum -a 256 "$ARTIFACT" | awk '{print $1}')"
SIZE_B="$(stat -f%z "$ARTIFACT" 2>/dev/null || stat -c%s "$ARTIFACT")"
cp "$ARTIFACT" "${LOGDIR}/artifact-B-${STAMP}.bin"
log "sha256(B) = ${SHA_B}  size=${SIZE_B}"

log ""
log "=== RESULT ==="
A_BIN="${LOGDIR}/artifact-A-${STAMP}.bin"
B_BIN="${LOGDIR}/artifact-B-${STAMP}.bin"

if [ "$SHA_A" = "$SHA_B" ]; then
  log "MATCH: byte-identical across two independent builds."
  log "       artifact reproduces with the applied neutralizers."
  RC=0
else
  log "DIFFER: the two independent builds are NOT byte-identical."
  log "  sha256(A)=${SHA_A} size=${SIZE_A}"
  log "  sha256(B)=${SHA_B} size=${SIZE_B}"
  if [ "$SIZE_A" != "$SIZE_B" ]; then
    log "  size differs (${SIZE_A} vs ${SIZE_B}): structural nondeterminism (CGU/symbol count)."
  fi
  TOTAL_DIFF="$(cmp -l "$A_BIN" "$B_BIN" 2>/dev/null | wc -l | tr -d ' ' || echo '?')"
  FIRST="$(cmp -l "$A_BIN" "$B_BIN" 2>/dev/null | head -1 || true)"
  log "  differing bytes (within common length): ${TOTAL_DIFF}"
  log "  first difference (offset oct, A oct, B oct): ${FIRST:-<none in common prefix>}"
  # Best-effort section attribution via otool if available.
  if command -v otool >/dev/null 2>&1 && [ -n "${FIRST}" ]; then
    OFF_DEC="$(( $(echo "$FIRST" | awk '{print $1}') - 1 ))"
    log "  first diff decimal offset: ${OFF_DEC}"
    log "  (Mach-O section map for offset attribution:)"
    otool -l "$A_BIN" 2>/dev/null | grep -E "segname|sectname|fileoff|offset " | head -40 | sed 's/^/    /' | tee -a "$MATCHLOG" >/dev/null
  fi
  RC=1
fi

if [ "$KEEP" -eq 0 ]; then
  rm -f "$A_BIN" "$B_BIN"
  log "(removed captured artifact copies; pass --keep to retain)"
fi

log ""
log "log written: ${MATCHLOG}"
exit "$RC"
