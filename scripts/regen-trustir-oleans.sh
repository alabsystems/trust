#!/usr/bin/env bash
# Trust: the Lean↔Clean bridge AUDIT LANE (option (iii) of
# reports/bridge-assembly-11arms-2026-07-02.md §5, kept as a rebuild tool).
#
# Rebuilds trust-ir's Lean semantics (.olean) from the pinned Git objects
# sources with the pinned Lean toolchain, computes the minimal module closure
# of the exported BRIDGE_ROOT_MODULES union, and:
#
#   default (--check): verifies the VENDORED artifacts —
#     crates/trust-clean/fixtures/trustir-oleans (TrustIr modules) and
#     vendor/lean-core-oleans (Lean-core Init closure) — are byte-identical
#     to the fresh rebuild / the toolchain's own files, that the vendored set
#     EQUALS the closure, and that the manifest commit equals the checked-out
#     first-party/trust-ir HEAD. Exit nonzero on any mismatch.
#
#   --write: regenerates the vendored trees + MANIFEST.toml files from the
#     rebuild (use after a trust-ir pin bump; commit the result).
#
# Requirements: a Lean toolchain matching first-party/trust-ir/lean/
# trust_ir-semantics/lean-toolchain. Provide it either via elan (installed
# automatically with `elan run --install`) or by setting LEAN_TOOLCHAIN_BIN to
# the toolchain's bin/ directory (lake + lean). Rust-side closure computation
# uses the in-tree clean-olean (`targo --unverified run -p trust-bridge-closure --bin bridge_closure`).
# Set TRUST_REGEN_KEEP_WORK=1 to retain the successful producer snapshot for
# same-source metadata accounting. This changes cleanup only, never the proof roots.
# TRUST_REGEN_NATIVE_LINKER may name an absolute executable linker for Lake's
# nativeLinker configuration (for example, a user-prefix Apple toolchain).
#
# This is a TOOL anyone can run — the default-on gate itself
# (crates/trust-clean/tests/lean_clean_bridge.rs) never needs a Lean
# toolchain; that is the point of vendoring.
set -euo pipefail
# Keep every named repository independent of a hook/caller's Git identity.
unset $(git rev-parse --local-env-vars)

KEEP_WORK="${TRUST_REGEN_KEEP_WORK:-0}"
case "$KEEP_WORK" in
    0|1) ;;
    *) echo "regen-trustir-oleans: TRUST_REGEN_KEEP_WORK must be 0 or 1" >&2; exit 2 ;;
esac

NATIVE_LINKER="${TRUST_REGEN_NATIVE_LINKER:-}"
if [[ -n "$NATIVE_LINKER" ]]; then
    [[ "$NATIVE_LINKER" == /* && -f "$NATIVE_LINKER" && -x "$NATIVE_LINKER" ]] || {
        echo "regen-trustir-oleans: TRUST_REGEN_NATIVE_LINKER must name an absolute executable file" >&2
        exit 2
    }
fi

MODE="check"
if [[ "${1:-}" == "--write" ]]; then MODE="write"; fi
REUSE_ANCHOR=""
if [[ "${1:-}" == "--reuse-source-inputs" ]]; then
    [[ "$#" == 2 && "$2" =~ ^[0-9a-f]{40}$ ]] || {
        echo "usage: scripts/regen-trustir-oleans.sh --reuse-source-inputs <original-artifact-commit>" >&2
        exit 2
    }
    MODE="reuse"
    REUSE_ANCHOR="$2"
fi

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SUB="$ROOT/first-party/trust-ir"
SRC="$SUB/lean/trust_ir-semantics"
FIX="$ROOT/crates/trust-clean/fixtures/trustir-oleans"
VEN="$ROOT/vendor/lean-core-oleans"

# Trust (2026-11-08): name the build target in the environment. atpkg's targo refuses the
# workspace's `.cargo/config.toml` `target-dir` ("build cache ownership refused: explicit
# build target is unmanaged or unsupported", exit 75, no build started) and accepts the same
# directory as CARGO_TARGET_DIR, which is how the land gate's crates legs name it. The
# olean-audit leg names none, so the audit refused in under a second on every atpkg-managed
# host (land gate 20261108T022428). A caller's own target keeps its precedence.
if [[ -z "${CARGO_TARGET_DIR:-}${CARGO_BUILD_TARGET_DIR:-}${TARGO_TARGET_DIR:-}" ]]; then
    export CARGO_TARGET_DIR="$ROOT/crates/target"
fi

[[ -e "$SUB/.git" ]] || { echo "ERROR: $SUB is not initialized"; exit 1; }
COMMIT="$(git -C "$SUB" rev-parse HEAD)"
# The clean revision the regenerated set is staged against. Clean supplies the
# olean reader and the kernel on the replay side, so the manifest records both
# ends of the bridge, not just the source end. scripts/check_bridge_pin.sh
# holds this equal to the indexed gitlink.
CLEAN_COMMIT="$(git -C "$ROOT/first-party/clean" rev-parse HEAD)"

if [[ -n "$(git -C "$SUB" status --porcelain -- lean/trust_ir-semantics)" ]]; then
    echo "ERROR: $SRC has local modifications — the rebuild would not represent commit $COMMIT."
    git -C "$SUB" status --porcelain -- lean/trust_ir-semantics
    exit 1
fi

# --- Reserve a fresh producer snapshot -----------------------------------
WORK="$(mktemp -d "${TMPDIR:-/tmp}/regen-trustir-oleans.XXXXXX")"
cleanup_bridge_work() {
    local status=$?
    trap - EXIT
    if [[ "$status" -eq 0 && "$KEEP_WORK" -eq 0 ]]; then
        rm -rf "$WORK" || printf 'bridge producer: cleanup failed; scratch retained: %s\n' "$WORK" >&2
    elif [[ "$status" -eq 0 ]]; then
        printf 'bridge producer: successful snapshot retained by TRUST_REGEN_KEEP_WORK=1: %s\n' "$WORK" >&2
    else
        printf 'bridge producer: exit %s; failed scratch retained: %s\n' "$status" "$WORK" >&2
    fi
    exit "$status"
}
trap cleanup_bridge_work EXIT
WORK="$(cd "$WORK" && pwd -P)"

# --- Resolve the in-tree bridge utility ----------------------------------
# Trust: resolve the build tool instead of hardcoding one stage layout. The stage2 path is
# what a fully-bootstrapped mac has; a Linux clone that builds `--stage 1` has only the
# stage1 tree, and the hardcoded path made the regen fail there with "No such file or
# directory" — which then wedged a pin bump between fast.bridge-pin (manifest must be
# regenerated with the pin) and the preflight's pin_behind_history (holding the pin walks
# it backward). The newest genuine Targo that loads this checkout wins.
TARGO=""
genuine_targo() {
    local version
    version="$("$1" --unverified --version 2>/dev/null)" || return 1
    # A compatibility wrapper that strips the flag before invoking cargo must
    # not authorize an unnamed Rust lane either.
    [[ "$version" == targo\ * ]]
}
# Trust (2026-09-12): a STATED targo wins, then the build tree, then PATH. This
# machine had only a stage0 `build/` (the toolchain is installed by atpkg, not
# built here), so the loop below found nothing and the only exit was "build one
# first" — a refusal with no fix option (v7/D3). The PATH fallback is guarded by
# the same `--unverified` probe as the build-tree candidates, so a cargo wearing
# targo's name still cannot slip in as the build tool.
if [ -n "${TRUST_REGEN_TARGO:-}" ]; then
  if [ -x "$TRUST_REGEN_TARGO" ]; then
    if ! genuine_targo "$TRUST_REGEN_TARGO"; then
      echo "regen-trustir-oleans: TRUST_REGEN_TARGO is not a genuine Targo (--unverified --version must identify targo)" >&2
      exit 1
    fi
    TARGO="$TRUST_REGEN_TARGO"
  else
    echo "regen-trustir-oleans: TRUST_REGEN_TARGO='$TRUST_REGEN_TARGO' is not an executable file" >&2
    exit 1
  fi
fi
# Trust (2026-09-23): the NEWEST candidate that can LOAD this checkout wins, not the
# first one in a fixed order. The fixed order picked an August `build/host/stage2`
# targo over this week's, and that one rejects manifest keys the siblings have since
# adopted (`compiler_timeout_secs`), so a clean pin move died here with
# "unknown field" while every installed toolchain loaded the workspace fine. Loading
# `Cargo.toml` is the property this script needs, so it is what is probed.
if [ -z "$TARGO" ]; then
  REJECTED=""
  # `|| true` inside the group: `ls` exits non-zero when ANY operand is missing, and
  # under `set -o pipefail` that killed this assignment -- and the script, with no
  # message -- on every host lacking one of the four build paths, so the PATH fallback
  # above never ran (measured 2026-09-28: the check died right after "computing
  # closure" on a machine whose only targo is atpkg's).
  CANDIDATES="$( { ls -t "$ROOT"/build/host/stage2/bin/targo "$ROOT"/build/host/stage1/bin/targo \
      "$ROOT"/build/*/stage1/bin/targo "$ROOT"/build/*/stage2/bin/targo \
      "$(command -v targo 2>/dev/null)" 2>/dev/null || true; } | awk '!seen[$0]++')"
  while IFS= read -r cand; do
    [ -n "$cand" ] && [ -x "$cand" ] || continue
    if ! genuine_targo "$cand"; then
      REJECTED="$REJECTED\n  $cand (not a genuine Targo)"
      continue
    fi
    if (cd "$ROOT" && "$cand" metadata --manifest-path Cargo.toml --format-version 1 \
          --no-deps --offline >/dev/null 2>&1); then
      TARGO="$cand"; break
    fi
    REJECTED="$REJECTED\n  $cand (cannot load Cargo.toml)"
  done <<< "$CANDIDATES"
  if [ -n "$TARGO" ] && [ -n "$REJECTED" ]; then
    printf "regen-trustir-oleans: using %s; skipped newer:%b\n" "$TARGO" "$REJECTED" >&2
  fi
fi
if [ -z "$TARGO" ]; then
  [ -n "${REJECTED:-}" ] && printf "regen-trustir-oleans: no candidate targo loads this checkout:%b\n" "$REJECTED" >&2
  echo "regen-trustir-oleans: no targo found under build/*/stage{1,2}/bin and none on PATH." >&2
  echo "  fix, one of:  export TRUST_REGEN_TARGO=/path/to/targo   # a targo you name" >&2
  echo "                put a targo on PATH (atpkg installs one)" >&2
  echo "                ./x.py build --stage 1 targo                # build one here" >&2
  exit 1
fi
# Every candidate has already admitted the genuine unverified frontend. Every
# Rust invocation below names that lane; a cargo-shaped stale stage is refused.

# A selected revision may reuse the original bytes only when the shared
# verifier establishes complete input equality from actual Git objects.
# This preserves the original producer/platform stamps, including their dates.
# Stage the selected gitlinks first; the updater reads that exact index.
if [[ "$MODE" == "reuse" ]]; then
    (cd "$ROOT" && "$TARGO" --unverified run --offline --quiet --locked \
        --manifest-path Cargo.toml -p trust-bridge-closure --no-default-features --bin bridge_source_reuse \
        -- --prepare-source-reuse "$ROOT" "$REUSE_ANCHOR")
    exit 0
fi

# The compiled utility exports raw blobs at COMMIT. Git archive attributes,
# checkout filters, ignored files and later live edits cannot change this input.
SRC="$WORK/trust_ir-semantics"
(cd "$ROOT" && "$TARGO" --unverified run --quiet --locked --manifest-path Cargo.toml \
    -p trust-bridge-closure --bin bridge_closure -- --snapshot-lean "$SUB" "$COMMIT" "$SRC")
TOOLCHAIN="$(cat "$SRC/lean-toolchain")"
SHIP_LIB="$SRC/.lake/build/lib"

# --- Locate the toolchain named by the immutable producer source ----------
if [[ -n "${LEAN_TOOLCHAIN_BIN:-}" ]]; then
    # Preserve caller-relative selection before the native build enters ROOT.
    LEAN_BIN_DIR="$(cd -- "$LEAN_TOOLCHAIN_BIN" && pwd -P)"
elif command -v elan >/dev/null 2>&1; then
    # Bind both the executable and core-library lookup to Lean's own prefix,
    # rather than accidentally mixing an elan proxy with another installation.
    LEAN_PREFIX="$(elan run --install "$TOOLCHAIN" lean --print-prefix)"
    LEAN_BIN_DIR="$LEAN_PREFIX/bin"
else
    echo "ERROR: need the pinned Lean toolchain ($TOOLCHAIN)."
    echo "Install elan (https://github.com/leanprover/elan) or set LEAN_TOOLCHAIN_BIN=<toolchain>/bin."
    exit 1
fi
# The compiled utility queries and admits this exact pair. NUL-framed data
# preserves paths with spaces/newlines; no report value is shell source.
TOOL_REPORT="$WORK/toolchain-readback"
(cd "$ROOT" && "$TARGO" --unverified run --quiet --locked --manifest-path Cargo.toml \
    -p trust-bridge-closure --bin bridge_closure -- --admit-lean-toolchain "$SRC" "$LEAN_BIN_DIR" "$TOOL_REPORT")
{
    if ! {
        IFS= read -r -d '' TOOL_SCHEMA &&
        IFS= read -r -d '' TRIPLE &&
        IFS= read -r -d '' TOOLCHAIN &&
        IFS= read -r -d '' LEAN_VERSION &&
        IFS= read -r -d '' LEAN_BIN_DIR &&
        IFS= read -r -d '' CORE_LIB
    }; then
        echo "ERROR: truncated native toolchain readback" >&2
        exit 1
    fi
    if [[ "$TOOL_SCHEMA" != trust.lean-toolchain-readback.v1 ]]; then
        echo "ERROR: unrecognized native toolchain readback schema" >&2
        exit 1
    fi
    TOOL_EXTRA=""
    if IFS= read -r -d '' TOOL_EXTRA || [[ -n "$TOOL_EXTRA" ]]; then
        echo "ERROR: trailing native toolchain readback data" >&2
        exit 1
    fi
} < "$TOOL_REPORT"
LAKE=("$LEAN_BIN_DIR/lake")
if [[ -n "$NATIVE_LINKER" ]]; then
    LAKE+=(-K "nativeLinker=$NATIVE_LINKER")
fi
echo "toolchain: $LEAN_VERSION"
echo "platform: $TRIPLE"
echo "trust-ir:  $COMMIT"

# Build the genuine exported roots and their imports, rather than unrelated
# project targets. The same Rust constant drives the loader below, so adding a
# root cannot silently leave its olean unbuilt. A whole Lean-project build is
# separate coverage: Proofs.MemorySafety is outside this bridge's import cone
# and exhausted a bounded 24 GiB native Linux build before any bridge replay.
ROOTS="$WORK/root_modules.txt"
(cd "$ROOT" && "$TARGO" --unverified run --quiet --locked --manifest-path Cargo.toml \
    -p trust-bridge-closure --bin bridge_closure -- --roots) > "$ROOTS"
[[ -s "$ROOTS" ]] || { echo "ERROR: the bridge exports no root modules" >&2; exit 1; }
LAKE_TARGETS=()
while IFS= read -r module; do
    [[ "$module" =~ ^TrustIr(\.[A-Za-z][A-Za-z0-9_]*)+$ ]] || {
        echo "ERROR: invalid exported bridge root module: $module" >&2; exit 1;
    }
    LAKE_TARGETS+=("+$module:olean")
done < "$ROOTS"
echo "lake build (fresh exported bridge roots + imports) ..."
(cd "$WORK/trust_ir-semantics" && "${LAKE[@]}" build "${LAKE_TARGETS[@]}")

# --- Compute the full union closure with the in-tree clean-olean -----------
echo "computing closure of the exported bridge root modules ..."
CLOSURE="$WORK/closure_modules.txt"
(cd "$ROOT" && "$TARGO" --unverified run --quiet --locked --manifest-path Cargo.toml \
    -p trust-bridge-closure --bin bridge_closure -- "$SHIP_LIB" "$CORE_LIB") > "$CLOSURE"
N_TOTAL="$(wc -l < "$CLOSURE" | tr -d ' ')"
N_TRUSTIR="$(grep -c '^TrustIr' "$CLOSURE")"
echo "closure: $N_TOTAL modules ($N_TRUSTIR TrustIr, $((N_TOTAL - N_TRUSTIR)) Lean-core)"

# --- Reproducibility screen: no bignum in a built closure module ----------
# Trust (2026-10-13): Lean 4.8.0's compactor writes a bignum (a natural at or
# above 2^63, an MPZ object) into the .olean with its uninitialised struct
# padding, so a module holding one gets different bytes on every build of the
# same source, and its digest can never be reproduced (measured: three fresh
# builds of trust-ir 3d315a17 gave three `Semantics/Cast.olean` digests). The
# Lean-core oleans are the toolchain's own files, copied, not rebuilt here.
CLOSURE_BUILT=()
while IFS= read -r module; do
    case "$module" in
        TrustIr*) CLOSURE_BUILT+=("$SHIP_LIB/${module//.//}.olean") ;;
    esac
done < "$CLOSURE"
if ! python3 "$ROOT/scripts/lean_olean_bignums.py" --refuse "${CLOSURE_BUILT[@]}"; then
    echo "ERROR: a TrustIr module of the bridge closure persists a bignum (listed above), so"
    echo "  its .olean is not reproducible under Lean 4.8.0 (scripts/lean_olean_bignums.py says why)."
    echo "  fix: in trust-ir, keep the value out of the module's environment; for a bound the"
    echo "  compiler folds into a closed term (\`u < 2 ^ 64\`), name the exponent with a"
    echo "  \`@[noinline]\` constant, as \`Sem.addrBits\` in TrustIr/Semantics/Cast.lean does."
    exit 1
fi

# --- Check or write the vendored trees + manifests -------------------------
python3 - "$MODE" "$ROOT" "$CLOSURE" "$SHIP_LIB" "$CORE_LIB" "$COMMIT" "$TOOLCHAIN" "$LEAN_VERSION" "$CLEAN_COMMIT" "$TRIPLE" "$ROOTS" <<'EOF'
import hashlib, os, re, shutil, sys, datetime

(mode, root, closure_file, ship_lib, core_lib, commit, toolchain, lean_version,
 clean_commit, triple, roots_file) = sys.argv[1:12]
fix = os.path.join(root, "crates/trust-clean/fixtures/trustir-oleans")
ven = os.path.join(root, "vendor/lean-core-oleans")

def sha256(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()

modules = [l.strip() for l in open(closure_file) if l.strip()]
roots = [l.strip() for l in open(roots_file) if l.strip()]
built = {}   # (tree, rel) -> built source path
for m in modules:
    rel = m.replace(".", "/") + ".olean"
    if m.startswith("TrustIr"):
        built[("trustir", rel)] = os.path.join(ship_lib, rel)
    else:
        built[("lean-core", rel)] = os.path.join(core_lib, rel)

def tree_dir(tree):
    return fix if tree == "trustir" else ven

def platform_rel(t, rel):
    """On-disk path (relative to the tree) for a PLATFORM-SPECIFIC olean."""
    return os.path.join("platform", t, rel)


def read_existing(path):
    """Recover (shared, platforms) from an existing v2 manifest.

    Hand-rolled because this repo's python has no tomllib and the format is
    one we write ourselves. Returns empty structures for a missing file or a
    v1 manifest — v1 has no platform dimension, so there is nothing to carry
    forward and the caller simply republishes as v2.

    This function is the whole reason regeneration is non-destructive: WITHOUT
    it, writing on one platform silently evicts every other platform's bytes.
    """
    shared, platforms = {}, {}
    if not os.path.exists(path):
        return shared, platforms
    section = None
    cur = None
    for line in open(path):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        m = re.match(r'^\[platforms\."([^"]+)"\.files\]$', line)
        if m:
            section, cur = "pfiles", platforms.setdefault(
                m.group(1), {"lean_version": "", "built_on": "",
                             "built_from_trustir_commit": "", "files": {}})
            continue
        m = re.match(r'^\[platforms\."([^"]+)"\]$', line)
        if m:
            section, cur = "pmeta", platforms.setdefault(
                m.group(1), {"lean_version": "", "built_on": "",
                             "built_from_trustir_commit": "", "files": {}})
            continue
        if line == "[files]":
            section, cur = "files", None
            continue
        if line.startswith("["):
            section, cur = "other", None
            continue
        m = re.match(r'^"([^"]+)"\s*=\s*"([0-9a-f]{64})"$', line)
        if m and section == "files":
            shared[m.group(1)] = m.group(2)
        elif m and section == "pfiles":
            cur["files"][m.group(1)] = m.group(2)
        elif section == "pmeta":
            m2 = re.match(
                r'^(lean_version|built_on|built_from_trustir_commit)\s*=\s*"(.*)"$', line)
            if m2:
                cur[m2.group(1)] = m2.group(2)
    return shared, platforms


def partition(per_platform):
    """Split {triple: {rel: sha}} into (shared, {triple: {rel: sha}}).

    A file is SHARED only when every known platform has it AND they all agree
    on the hash; anything else is platform-specific. With one platform known,
    everything is shared — which is correct, and becomes partitioned the first
    time a second platform disagrees.
    """
    triples = sorted(per_platform)
    if not triples:
        return {}, {}
    common = set(per_platform[triples[0]])
    for t in triples[1:]:
        common &= set(per_platform[t])
    shared = {}
    for rel in sorted(common):
        vals = {per_platform[t][rel] for t in triples}
        if len(vals) == 1:
            shared[rel] = next(iter(vals))
    spec = {t: {rel: sha for rel, sha in per_platform[t].items() if rel not in shared}
            for t in triples}
    return shared, {t: v for t, v in spec.items() if v}


def manifest_body(tree, shared, platforms):
    today = datetime.date.today().isoformat()
    if tree == "trustir":
        head = [
            'schema = "trust.trust-clean.trustir-oleans.manifest.v2"', "", "[provenance]",
            f'trustir_commit = "{commit}"',
            "# The first-party/clean revision these bytes are staged against — the olean",
            "# reader that decodes them and the kernel that admits the decoded declarations",
            "# both live there, so a clean pin bump changes what \"the bridge replays\" means",
            "# just as surely as a trust-ir bump changes what it replays. Kept equal to the",
            "# indexed gitlink by scripts/check_bridge_pin.sh; the replay itself is",
            "# validated by crates/trust-clean/tests/lean_clean_bridge.rs.",
            f'clean_commit = "{clean_commit}"',
            f'lean_toolchain = "{toolchain}"',
            f'root_module = "{roots[0]}"',
            'root_modules = [' + ', '.join(f'"{root}"' for root in roots) + ']',
            'source_subdir = "lean/trust_ir-semantics"',
            'build_command = "lake build ' + ' '.join(f'+{root}:olean' for root in roots) + ' (unmodified sources at trustir_commit; toolchain pinned by lean-toolchain)"',
            "# Full union import closure of root_modules: computed by loading the roots with",
            "# clean-olean load_modules_with_deps and vendoring exactly the visited TrustIr",
            "# modules. Regenerate + audit with scripts/regen-trustir-oleans.sh.",
        ]
    else:
        head = [
            'schema = "trust.vendor.lean-core-oleans.manifest.v2"', "", "[provenance]",
            f'lean_toolchain = "{toolchain}"',
            f'origin = "elan-installed {toolchain} release toolchain, lib/lean"',
            f'root_module = "{roots[0]}"',
            'root_modules = [' + ', '.join(f'"{root}"' for root in roots) + ']',
            "# FOREIGN vendored artifacts (Lean 4 core Init .oleans) — the transitive",
            "# Lean-core union import closure of the exported trust-ir bridge roots.",
            "# Consumed by crates/trust-clean/src/trustir_bridge.rs. Regenerate + audit",
            "# with scripts/regen-trustir-oleans.sh.",
        ]
    # v2 splits the file table by build platform. `lean_version` and `built_on`
    # moved OUT of [provenance] on purpose: a single stamp there necessarily
    # named one platform and silently claimed to describe every byte, which is
    # false the moment a second platform vendors artifacts.
    lines = head + [
        "",
        "# Files whose bytes are IDENTICAL on every platform listed below. Path is",
        "# the key, relative to this manifest.",
        "[files]",
    ]
    for rel in sorted(shared):
        lines.append(f'"{rel}" = "{shared[rel]}"')
    lines += [
        "",
        "# Per-platform artifacts. A file appears here only when platforms actually",
        "# DISAGREE on its bytes; its on-disk path is platform/<triple>/<key>. A",
        "# consumer must verify the shared set plus its OWN triple, and must fail",
        "# closed on a triple absent here rather than fall back to another",
        "# platform's bytes. `built_from_trustir_commit` is the trust-ir revision THAT",
        "# platform's bytes were built from; a platform whose value differs from",
        "# [provenance] trustir_commit is carried forward, not rebuilt, and a consumer",
        "# on that triple must refuse to replay it under trustir_commit's name.",
    ]
    for t in sorted(platforms):
        p = platforms[t]
        lines += [
            "",
            f'[platforms."{t}"]',
            f'lean_version = "{p["lean_version"]}"',
            f'built_on = "{p["built_on"]}"',
        ]
        # The trust-ir revision THIS platform's bytes were built from. A platform
        # carried forward by a regeneration elsewhere keeps its OWN value, so the
        # manifest never labels old bytes with the new commit (2026-09-24: Linux
        # oleans built from 00180257 were stamped 29744d5f). A carried platform
        # with no recorded value is written as "unknown", which every consumer
        # refuses. The Lean-core tree is built from the toolchain alone.
        if tree == "trustir":
            lines.append(
                f'built_from_trustir_commit = "{p.get("built_from_trustir_commit") or "unknown"}"')
        if p["files"]:
            lines.append(f'[platforms."{t}".files]')
            for rel in sorted(p["files"]):
                lines.append(f'"{rel}" = "{p["files"][rel]}"')
    return "\n".join(lines) + "\n"

failures = 0
if mode == "check":
    # 1. Byte-compare THIS PLATFORM's effective set against the vendored copy.
    #    A file is compared at platform/<triple>/<rel> when the manifest says
    #    the platforms disagree about it, and at <rel> otherwise. Comparing a
    #    foreign platform's bytes against a local rebuild is exactly the false
    #    failure that made the single-table layout unusable on two machines.
    for tree in ("trustir", "lean-core"):
        d = tree_dir(tree)
        shared, platforms = read_existing(os.path.join(d, "MANIFEST.toml"))
        mine = platforms.get(triple)
        if platforms and mine is None:
            print(f"PLATFORM NOT VENDORED: {os.path.join(d, 'MANIFEST.toml')} lists "
                  f"[{', '.join(sorted(platforms))}] but not {triple}.")
            print(f"  Add it with: scripts/regen-trustir-oleans.sh --write   "
                  f"(non-destructive; other platforms are carried forward)")
            failures += 1
            continue
        spec = set(mine["files"]) if mine else set()

        expected = set()
        for (tr, rel), src in sorted(built.items()):
            if tr != tree:
                continue
            rel_path = platform_rel(triple, rel) if rel in spec else rel
            expected.add(rel_path)
            dst = os.path.join(d, rel_path)
            if not os.path.exists(dst):
                print(f"MISSING vendored file: {dst}")
                failures += 1
            elif sha256(src) != sha256(dst):
                print(f"BYTE MISMATCH: {rel_path} (rebuild differs from vendored copy)")
                failures += 1

        # 2. Vendored tree must hold exactly: the closure for this platform,
        #    plus every OTHER platform's declared per-platform files. Those are
        #    legitimate residents, not strays — flagging them EXTRA is how a
        #    second platform's artifacts used to get deleted.
        for t, p in platforms.items():
            if t == triple:
                continue
            for rel in p["files"]:
                expected.add(platform_rel(t, rel))

        on_disk = set()
        for dirpath, _, names in os.walk(d):
            for n in names:
                if n.endswith(".olean"):
                    on_disk.add(os.path.relpath(os.path.join(dirpath, n), d))
        for rel in sorted(on_disk - expected):
            print(f"EXTRA vendored file (not in closure): {os.path.join(d, rel)}")
            failures += 1
        for rel in sorted(expected - on_disk):
            print(f"CLOSURE file missing from vendored tree: {os.path.join(d, rel)}")
            failures += 1
    # 3. Manifest commit must equal the checked-out submodule HEAD.
    manifest = os.path.join(fix, "MANIFEST.toml")
    text = open(manifest).read() if os.path.exists(manifest) else ""
    if not re.search(rf'^trustir_commit = "{commit}"$', text, re.M):
        print(f"MANIFEST PIN DRIFT: {manifest} does not record trustir_commit = {commit}")
        failures += 1
    _, trustir_platforms = read_existing(manifest)
    built_from = trustir_platforms.get(triple, {}).get("built_from_trustir_commit", "")
    if built_from != commit:
        print(f"PLATFORM PROVENANCE DRIFT: {manifest} records {triple} bytes built from "
              f"trust-ir {built_from or '<nothing>'}, not {commit}")
        failures += 1
    if f'clean_commit = "{clean_commit}"' not in text:
        print(f"MANIFEST PIN DRIFT: {manifest} does not record clean_commit = {clean_commit}")
        failures += 1
    if failures:
        print(f"AUDIT FAILED: {failures} mismatch(es). Regenerate with: scripts/regen-trustir-oleans.sh --write")
        sys.exit(1)
    print(f"AUDIT OK: vendored artifacts are byte-identical to a fresh pinned rebuild "
          f"({len(built)} files), the vendored set equals the closure, and the manifest "
          f"pin matches {commit[:12]}.")
else:
    today = datetime.date.today().isoformat()
    counts = {}
    for tree in ("trustir", "lean-core"):
        d = tree_dir(tree)
        old_shared, old_platforms = read_existing(os.path.join(d, "MANIFEST.toml"))

        # Files this build produced, and their hashes.
        cur = {rel: sha256(src) for (tr, rel), src in built.items() if tr == tree}

        # Snapshot every byte another platform might still need, BEFORE the
        # tree is touched. This is the subtle case: a file that is shared today
        # becomes platform-specific the moment THIS build disagrees with it,
        # and at that instant the other platform's only copy is sitting at the
        # shared path about to be overwritten.
        carry = {}
        for t, p in old_platforms.items():
            if t == triple:
                continue
            for rel in (set(old_shared) | set(p["files"])) & set(cur):
                src = os.path.join(
                    d, platform_rel(t, rel) if rel in p["files"] else rel)
                if os.path.exists(src):
                    carry[(t, rel)] = open(src, "rb").read()

        # Rebuild each known platform's full view, restricted to the CURRENT
        # closure so a trust-ir bump that drops a module drops it everywhere
        # instead of stranding it as bogus per-platform state.
        per = {}
        for t, p in old_platforms.items():
            if t == triple:
                continue
            merged = dict(old_shared)
            merged.update(p["files"])
            keep = {rel: sha for rel, sha in merged.items()
                    if rel in cur and (t, rel) in carry}
            if keep:
                per[t] = keep
        per[triple] = cur

        new_shared, new_spec = partition(per)

        if os.path.exists(d):
            shutil.rmtree(d)
        os.makedirs(d)

        def emit(rel_path, data=None, src=None):
            dst = os.path.join(d, rel_path)
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            if data is not None:
                open(dst, "wb").write(data)
            else:
                shutil.copyfile(src, dst)

        for rel in sorted(new_shared):
            emit(rel, src=built[(tree, rel)])
        for t, files in new_spec.items():
            for rel in sorted(files):
                if t == triple:
                    emit(platform_rel(t, rel), src=built[(tree, rel)])
                else:
                    emit(platform_rel(t, rel), data=carry[(t, rel)])

        platforms = {}
        for t in per:
            prev = old_platforms.get(t, {})
            platforms[t] = {
                "lean_version": lean_version if t == triple else prev.get("lean_version", ""),
                "built_on": today if t == triple else prev.get("built_on", ""),
                "built_from_trustir_commit": (
                    commit if t == triple else prev.get("built_from_trustir_commit", "")),
                "files": new_spec.get(t, {}),
            }
        with open(os.path.join(d, "MANIFEST.toml"), "w") as f:
            f.write(manifest_body(tree, new_shared, platforms))
        counts[tree] = (len(new_shared), sum(len(v) for v in new_spec.values()), sorted(per))

    ts, tp, tpl = counts["trustir"]
    cs, cp, cpl = counts["lean-core"]
    print(f"REGENERATED: TrustIr {ts} shared + {tp} per-platform; "
          f"Lean-core {cs} shared + {cp} per-platform "
          f"(trust-ir {commit[:12]}, this build {triple}).")
    print(f"  platforms carried: {', '.join(sorted(set(tpl) | set(cpl)))}")
    print("  Review + commit.")
EOF
