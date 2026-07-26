#!/usr/bin/env bash
# Trust: the Lean↔Clean bridge AUDIT LANE (option (iii) of
# reports/bridge-assembly-11arms-2026-07-02.md §5, kept as a rebuild tool).
#
# Rebuilds trust-ir's Lean semantics (.olean) from the CHECKED-OUT pinned
# sources with the pinned Lean toolchain, computes the minimal module closure
# of the bridge root (TrustIr.Semantics.Arith), and:
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
# uses the in-tree clean-olean (cargo run --example bridge_closure).
#
# This is a TOOL anyone can run — the default-on gate itself
# (crates/trust-clean/tests/lean_clean_bridge.rs) never needs a Lean
# toolchain; that is the point of vendoring.
set -euo pipefail

MODE="check"
if [[ "${1:-}" == "--write" ]]; then MODE="write"; fi

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SUB="$ROOT/first-party/trust-ir"
SRC="$SUB/lean/trust_ir-semantics"
FIX="$ROOT/crates/trust-clean/fixtures/trustir-oleans"
VEN="$ROOT/vendor/lean-core-oleans"

[[ -f "$SRC/lean-toolchain" ]] || { echo "ERROR: $SRC/lean-toolchain not found (submodule initialized?)"; exit 1; }
TOOLCHAIN="$(cat "$SRC/lean-toolchain")"
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

# --- Locate the pinned Lean toolchain -------------------------------------
if [[ -n "${LEAN_TOOLCHAIN_BIN:-}" ]]; then
    LAKE=("$LEAN_TOOLCHAIN_BIN/lake")
    LEAN_BIN_DIR="$LEAN_TOOLCHAIN_BIN"
elif command -v elan >/dev/null 2>&1; then
    LAKE=(elan run --install "$TOOLCHAIN" lake)
    # `command -v lean` may resolve elan's Homebrew-installed proxy
    # (`/opt/homebrew/bin/lean`) rather than the selected toolchain binary.  Lean
    # reports the exact active toolchain root itself; bind both the executable
    # and core-library lookup to that prefix so the audit cannot silently mix a
    # proxy installation with the pinned compiler.
    LEAN_PREFIX="$(elan run --install "$TOOLCHAIN" lean --print-prefix)"
    LEAN_BIN_DIR="$LEAN_PREFIX/bin"
else
    echo "ERROR: need the pinned Lean toolchain ($TOOLCHAIN)."
    echo "Install elan (https://github.com/leanprover/elan) or set LEAN_TOOLCHAIN_BIN=<toolchain>/bin."
    exit 1
fi
CORE_LIB="$LEAN_BIN_DIR/../lib/lean"
[[ -d "$CORE_LIB" ]] || { echo "ERROR: Lean core olean dir not found at $CORE_LIB"; exit 1; }
LEAN_VERSION="$("$LEAN_BIN_DIR/lean" --version)"
echo "toolchain: $LEAN_VERSION"
echo "trust-ir:  $COMMIT"

# --- Rebuild from the pinned sources in a scratch copy --------------------
WORK="$(mktemp -d "${TMPDIR:-/tmp}/regen-trustir-oleans.XXXXXX")"
trap 'rm -rf "$WORK"' EXIT
cp -R "$SRC" "$WORK/trust_ir-semantics"
rm -rf "$WORK/trust_ir-semantics/.lake"
echo "lake build (fresh) ..."
(cd "$WORK/trust_ir-semantics" && "${LAKE[@]}" build >/dev/null)
SHIP_LIB="$WORK/trust_ir-semantics/.lake/build/lib"

# --- Compute the minimal closure with the in-tree clean-olean --------------
echo "computing closure of the bridge root module ..."
CLOSURE="$WORK/closure_modules.txt"
(cd "$ROOT" && RUSTC_BOOTSTRAP=1 cargo run --quiet --manifest-path crates/Cargo.toml \
    -p trust-clean --example bridge_closure -- "$SHIP_LIB" "$CORE_LIB") > "$CLOSURE"
N_TOTAL="$(wc -l < "$CLOSURE" | tr -d ' ')"
N_TRUSTIR="$(grep -c '^TrustIr' "$CLOSURE")"
echo "closure: $N_TOTAL modules ($N_TRUSTIR TrustIr, $((N_TOTAL - N_TRUSTIR)) Lean-core)"

# --- Check or write the vendored trees + manifests -------------------------
python3 - "$MODE" "$ROOT" "$CLOSURE" "$SHIP_LIB" "$CORE_LIB" "$COMMIT" "$TOOLCHAIN" "$LEAN_VERSION" "$CLEAN_COMMIT" <<'EOF'
import hashlib, os, shutil, sys, datetime

(mode, root, closure_file, ship_lib, core_lib, commit, toolchain, lean_version,
 clean_commit) = sys.argv[1:10]
fix = os.path.join(root, "crates/trust-clean/fixtures/trustir-oleans")
ven = os.path.join(root, "vendor/lean-core-oleans")

def sha256(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()

modules = [l.strip() for l in open(closure_file) if l.strip()]
built = {}   # (tree, rel) -> built source path
for m in modules:
    rel = m.replace(".", "/") + ".olean"
    if m.startswith("TrustIr"):
        built[("trustir", rel)] = os.path.join(ship_lib, rel)
    else:
        built[("lean-core", rel)] = os.path.join(core_lib, rel)

def tree_dir(tree):
    return fix if tree == "trustir" else ven

def manifest_body(tree, entries):
    today = datetime.date.today().isoformat()
    if tree == "trustir":
        head = [
            'schema = "trust.trust-clean.trustir-oleans.manifest.v1"', "", "[provenance]",
            f'trustir_commit = "{commit}"',
            "# The first-party/clean revision these bytes are staged against — the olean",
            "# reader that decodes them and the kernel that admits the decoded declarations",
            "# both live there, so a clean pin bump changes what \"the bridge replays\" means",
            "# just as surely as a trust-ir bump changes what it replays. Kept equal to the",
            "# indexed gitlink by scripts/check_bridge_pin.sh; the replay itself is",
            "# validated by crates/trust-clean/tests/lean_clean_bridge.rs.",
            f'clean_commit = "{clean_commit}"',
            f'lean_toolchain = "{toolchain}"',
            f'lean_version = "{lean_version}"',
            'root_module = "TrustIr.Semantics.Arith"',
            'source_subdir = "lean/trust_ir-semantics"',
            'build_command = "lake build (unmodified sources at trustir_commit; toolchain pinned by lean-toolchain)"',
            f'built_on = "{today}"',
            "# Minimal module closure of root_module: computed by loading the root with",
            "# clean-olean load_module_with_deps and vendoring exactly the visited TrustIr",
            "# modules. Regenerate + audit with scripts/regen-trustir-oleans.sh.",
        ]
    else:
        head = [
            'schema = "trust.vendor.lean-core-oleans.manifest.v1"', "", "[provenance]",
            f'lean_toolchain = "{toolchain}"',
            f'lean_version = "{lean_version}"',
            f'origin = "elan-installed {toolchain} release toolchain, lib/lean"',
            'root_module = "TrustIr.Semantics.Arith"',
            f'built_on = "{today}"',
            "# FOREIGN vendored artifacts (Lean 4 core Init .oleans) — the transitive",
            "# Lean-core import closure of the trust-ir arithmetic-semantics root module.",
            "# Consumed by crates/trust-clean/src/trustir_bridge.rs. Regenerate + audit",
            "# with scripts/regen-trustir-oleans.sh.",
        ]
    lines = head + ["", "[files]"]
    for rel, digest in sorted(entries):
        lines.append(f'"{rel}" = "{digest}"')
    return "\n".join(lines) + "\n"

failures = 0
if mode == "check":
    # 1. Byte-compare every closure file against the vendored copy.
    per_tree = {"trustir": set(), "lean-core": set()}
    for (tree, rel), src in sorted(built.items()):
        per_tree[tree].add(rel)
        dst = os.path.join(tree_dir(tree), rel)
        if not os.path.exists(dst):
            print(f"MISSING vendored file: {dst}")
            failures += 1
        elif sha256(src) != sha256(dst):
            print(f"BYTE MISMATCH: {rel} (rebuild differs from vendored copy)")
            failures += 1
    # 2. Vendored trees must contain nothing outside the closure.
    for tree in per_tree:
        d = tree_dir(tree)
        on_disk = set()
        for dirpath, _, names in os.walk(d):
            for n in names:
                if n.endswith(".olean"):
                    on_disk.add(os.path.relpath(os.path.join(dirpath, n), d))
        extra = on_disk - per_tree[tree]
        missing = per_tree[tree] - on_disk
        for rel in sorted(extra):
            print(f"EXTRA vendored file (not in closure): {os.path.join(d, rel)}")
            failures += 1
        for rel in sorted(missing):
            print(f"CLOSURE file missing from vendored tree: {os.path.join(d, rel)}")
            failures += 1
    # 3. Manifest commit must equal the checked-out submodule HEAD.
    manifest = os.path.join(fix, "MANIFEST.toml")
    text = open(manifest).read() if os.path.exists(manifest) else ""
    if f'trustir_commit = "{commit}"' not in text:
        print(f"MANIFEST PIN DRIFT: {manifest} does not record trustir_commit = {commit}")
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
    for tree in ("trustir", "lean-core"):
        d = tree_dir(tree)
        if os.path.exists(d):
            shutil.rmtree(d)
        os.makedirs(d)
    entries = {"trustir": [], "lean-core": []}
    for (tree, rel), src in sorted(built.items()):
        dst = os.path.join(tree_dir(tree), rel)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        shutil.copyfile(src, dst)
        entries[tree].append((rel, sha256(dst)))
    for tree in ("trustir", "lean-core"):
        with open(os.path.join(tree_dir(tree), "MANIFEST.toml"), "w") as f:
            f.write(manifest_body(tree, entries[tree]))
    print(f"REGENERATED: {len(entries['trustir'])} TrustIr + {len(entries['lean-core'])} "
          f"Lean-core oleans + manifests (trust-ir {commit[:12]}). Review + commit.")
EOF
