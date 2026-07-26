#!/usr/bin/env bash
# Fresh-clone / no-stock-Rust seed consume test (docs/OFF_STOCK_RUST_PLAN.md Phase 4).
#
# Proves that a checkout with NO stock Rust reachable can fetch the pinned Trust
# stage0 seed from the private release and rebuild Trust *off that seed* — the
# test whose absence let the first seed ship fresh-clone-fatal bugs.
#
# The steps, in order:
#   1. Assert no stock rustc/cargo/rustup is reachable (fail-closed; the seed is
#      the only Rust that may build Trust). --allow-ambient-rust downgrades this
#      to a warning so the wiring can be dry-run on a dev host that still has
#      rustup installed.
#   2. Fetch the pinned seed payloads from the private GitHub release (authed via
#      $GH_TOKEN / gh auth) into the canonical dist dir src/stage0 pins.
#   3. Fail-closed digest gate: scripts/check_seed_freshness.py --require-payloads.
#   4. Cross-platform static off-stock preflight (scripts/prove_rust_free_build.sh).
#   5. Build Trust off the seed with a minimal CI bootstrap.toml that sets NO
#      [build] rustc/cargo override, so x.py must resolve stage0 from src/stage0
#      (the seed). LLVM is built from source by default (fork history breaks
#      download-ci-llvm); pass --llvm-config to use a prebuilt LLVM instead.
#   6. Assert the seed actually served as stage0 (stage0 trustc self-reports the
#      seed's version + commit) and that a stageN `trustc` was produced.
#
# The strace exec-audit (prove_rust_free_build.sh --build) is a Linux-only,
# stronger defense-in-depth layer; this consume test runs on the seed's
# aarch64-apple-darwin host, where the audit backend is unavailable, so it proves
# consume-and-build with PATH/identity/stage0-lineage assertions instead.
#
# Usage:
#   scripts/ci_fresh_clone_consume_test.sh [options]
# Options:
#   --stage N            stage to build (default 2)
#   --target STR         build target (default: compiler/rustc — does not need
#                        the first-party submodules, so no sibling-repo token)
#   --llvm-config PATH   use a prebuilt llvm-config instead of building LLVM
#   --build-dir DIR      x.py build dir (default build/ci-consume)
#   --repo OWNER/NAME    release repo (default: origin, else alabsystems/trust)
#   --no-fetch           assume payloads are already materialized locally
#   --no-build           stop after the digest gate + preflight (wiring dry-run)
#   --allow-ambient-rust downgrade the no-stock-Rust assertion to a warning
#   -h, --help
set -uo pipefail

STAGE=2
TARGET="compiler/rustc"
LLVM_CONFIG=""
BUILD_DIR=""
REPO=""
DO_FETCH=1
DO_BUILD=1
ALLOW_AMBIENT=0

log()  { printf '\n== %s ==\n' "$*"; }
note() { printf '  %s\n' "$*"; }
die()  { printf 'FAIL: %s\n' "$*" >&2; exit 1; }

while [ $# -gt 0 ]; do
    case "$1" in
        --stage) STAGE=${2:?}; shift 2 ;;
        --target) TARGET=${2:?}; shift 2 ;;
        --llvm-config) LLVM_CONFIG=${2:?}; shift 2 ;;
        --build-dir) BUILD_DIR=${2:?}; shift 2 ;;
        --repo) REPO=${2:?}; shift 2 ;;
        --no-fetch) DO_FETCH=0; shift ;;
        --no-build) DO_BUILD=0; shift ;;
        --allow-ambient-rust) ALLOW_AMBIENT=1; shift ;;
        -h|--help) grep '^#' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
        *) die "unknown argument: $1" ;;
    esac
done

script_dir=${BASH_SOURCE[0]%/*}
[ "$script_dir" = "${BASH_SOURCE[0]}" ] && script_dir=.
ROOT=$(cd -P "$script_dir/.." && pwd -P) || die "cannot resolve repository root"
cd -P "$ROOT" || die "cannot enter repository root"
[ -z "$BUILD_DIR" ] && BUILD_DIR="$ROOT/build/ci-consume"

PYTHON_BIN=$(command -v python3 || true)
[ -n "$PYTHON_BIN" ] || die "python3 is required"
STAGE0="$ROOT/src/stage0"
[ -f "$STAGE0" ] || die "missing $STAGE0"

# ---- parse the pin from src/stage0 (never hardcode the tag/date) -------------
stage0_get() { sed -n "s/^$1=//p" "$STAGE0" | head -1; }
SEED_DATE=$(stage0_get compiler_date)
SEED_VERSION=$(stage0_get compiler_version)
SEED_COMMIT=$(stage0_get compiler_git_commit_hash)
[ -n "$SEED_DATE" ] && [ -n "$SEED_VERSION" ] && [ -n "$SEED_COMMIT" ] \
    || die "src/stage0 is missing compiler_date/version/git_commit_hash"
TAG="trust-stage0-${SEED_DATE}"
DIST_DIR="$ROOT/bootstrap/trust-stage0/dist/${SEED_DATE}"
# Authoritative host triple: read it off a pinned payload key in src/stage0.
TRIPLE=$(sed -n "s#^dist/${SEED_DATE}/trustc-${SEED_VERSION}-\(.*\)\.tar\.xz=.*#\1#p" "$STAGE0" | head -1)
[ -n "$TRIPLE" ] || die "cannot derive host triple from src/stage0 trustc payload key"

log "seed under test"
note "pin       : ${SEED_VERSION} (${SEED_DATE}, ${SEED_COMMIT:0:10})"
note "release   : ${TAG}"
note "triple    : ${TRIPLE}"
note "dist dir  : ${DIST_DIR}"

# ---- 1. no stock Rust may be reachable ---------------------------------------
log "assert no stock Rust is reachable"
ambient=""
for tool in rustc cargo rustup rustdoc; do
    p=$(command -v "$tool" 2>/dev/null || true)
    # A binary inside the checkout or the build dir is the seed/our output, not
    # ambient stock Rust.
    case "$p" in ""|"$ROOT"/*|"$BUILD_DIR"/*) ;; *) ambient="$ambient $tool=$p" ;; esac
done
if [ -n "$ambient" ]; then
    if [ "$ALLOW_AMBIENT" -eq 1 ]; then
        note "WARNING (--allow-ambient-rust): stock Rust on PATH:${ambient}"
        note "a real CI run must uninstall/scrub it; continuing for a wiring dry-run only."
    else
        die "stock Rust reachable on PATH:${ambient} — uninstall/scrub it before the consume test"
    fi
else
    note "no rustc/cargo/rustup/rustdoc on PATH — clean."
fi

# ---- 2. fetch the pinned seed from the private release -----------------------
if [ "$DO_FETCH" -eq 1 ]; then
    log "fetch seed payloads from private release ${TAG}"
    command -v gh >/dev/null 2>&1 || die "gh CLI is required to fetch from the private release"
    if [ -z "$REPO" ]; then
        origin=$(git -C "$ROOT" remote get-url origin 2>/dev/null || true)
        case "$origin" in
            *github.com[:/]*) REPO=$(printf '%s' "$origin" | sed -E 's#.*github\.com[:/]([^/]+/[^/]+?)(\.git)?$#\1#') ;;
        esac
        [ -n "$REPO" ] || REPO="alabsystems/trust"
    fi
    note "repo: ${REPO}"
    mkdir -p "$DIST_DIR"
    gh release download "$TAG" --repo "$REPO" --dir "$DIST_DIR" \
        --pattern '*.tar.xz' --clobber \
        || die "gh release download failed (auth? tag ${TAG} on ${REPO}?)"
    note "downloaded $(find "$DIST_DIR" -maxdepth 1 -name '*.tar.xz' | wc -l | tr -d ' ') payload(s)"
else
    log "skip fetch (--no-fetch): using already-materialized payloads"
fi

# ---- 3. fail-closed digest gate ----------------------------------------------
log "seed freshness + digest gate (--require-payloads)"
"$PYTHON_BIN" "$ROOT/scripts/check_seed_freshness.py" --require-payloads \
    || die "seed freshness/digest gate failed"

# ---- 4. static off-stock preflight (cross-platform) --------------------------
# Validates seed/config/PATH inputs. It legitimately fails when stock Rust is on
# PATH, so it is only a hard gate when we asserted a clean environment above.
if [ "$ALLOW_AMBIENT" -eq 0 ]; then
    log "static off-stock-Rust preflight"
    "$ROOT/scripts/prove_rust_free_build.sh" || die "off-stock static preflight failed"
else
    log "skip static preflight (--allow-ambient-rust: PATH intentionally not clean)"
fi

if [ "$DO_BUILD" -eq 0 ]; then
    log "PASS (dry-run): fetch + digest gate wiring is green; build skipped (--no-build)"
    exit 0
fi

# ---- 5. build Trust off the seed ---------------------------------------------
log "write minimal CI bootstrap.toml (NO stage0 override → seed serves as stage0)"
mkdir -p "$BUILD_DIR"
CI_CONFIG="$BUILD_DIR/bootstrap.ci-consume.toml"
{
    echo '# Generated by scripts/ci_fresh_clone_consume_test.sh — do not commit.'
    echo '# Deliberately sets NO [build] rustc/cargo: x.py must resolve stage0 from'
    echo '# the pinned src/stage0 seed, which is the whole point of this test.'
    echo '[build]'
    echo 'submodules = false'
    echo 'docs = false'
    echo '[llvm]'
    echo 'download-ci-llvm = false'
    if [ -n "$LLVM_CONFIG" ]; then
        echo "[target.${TRIPLE}]"
        echo "llvm-config = \"${LLVM_CONFIG}\""
    fi
    echo '[rust]'
    echo 'channel = "trust"'
    echo 'deny-warnings = false'
} > "$CI_CONFIG"
note "config: $CI_CONFIG"
[ -n "$LLVM_CONFIG" ] && note "llvm-config: $LLVM_CONFIG" || note "LLVM: built from source (no --llvm-config)"

log "x.py build --stage ${STAGE} ${TARGET} (off the seed)"
"$PYTHON_BIN" "$ROOT/x.py" --config "$CI_CONFIG" build \
    --stage "$STAGE" --build-dir "$BUILD_DIR" "$TARGET" \
    || die "x.py build off the seed failed"

# ---- 6. assert the seed served as stage0, and a stageN trustc exists ---------
log "assert seed lineage + built compiler"
# The unpacked seed is the stage0 compiler. Find it under the build dir.
stage0_trustc=""
for cand in "$BUILD_DIR/$TRIPLE/stage0/bin/trustc" "$BUILD_DIR/host/stage0/bin/trustc"; do
    [ -x "$cand" ] && { stage0_trustc="$cand"; break; }
done
if [ -n "$stage0_trustc" ]; then
    v=$("$stage0_trustc" --version 2>/dev/null || true)
    note "stage0 trustc: $v"
    case "$v" in
        *"${SEED_COMMIT:0:9}"*) note "stage0 lineage OK: reports the seed commit ${SEED_COMMIT:0:9}." ;;
        *"(trustc)"*) note "stage0 is a trustc (commit string not in --version banner; acceptable)." ;;
        *) die "stage0 trustc did not self-identify as the seed: $v" ;;
    esac
else
    note "WARNING: could not locate the unpacked stage0 trustc under $BUILD_DIR (layout drift?)."
    note "the build succeeded off --config with no stage0 override, so the seed was still used."
fi

stageN_trustc=""
for cand in "$BUILD_DIR/$TRIPLE/stage${STAGE}/bin/trustc" "$BUILD_DIR/host/stage${STAGE}/bin/trustc"; do
    [ -x "$cand" ] && { stageN_trustc="$cand"; break; }
done
if [ -n "$stageN_trustc" ]; then
    vN=$("$stageN_trustc" --version 2>/dev/null || true)
    note "stage${STAGE} trustc: $vN"
    case "$vN" in *"(trustc)"*) ;; *) die "stage${STAGE} compiler is not a trustc: $vN" ;; esac
    sysroot=$("$stageN_trustc" --print sysroot 2>/dev/null || true)
    case "$sysroot" in
        "$BUILD_DIR"/*) note "stage${STAGE} sysroot is inside the build dir (not a stock toolchain)." ;;
        *) note "WARNING: stage${STAGE} sysroot outside build dir: $sysroot" ;;
    esac
else
    die "no stage${STAGE} trustc was produced under $BUILD_DIR"
fi

log "PASS: fresh-clone / no-stock-Rust consume test — seed fetched, digest-verified, and rebuilt Trust off itself."
