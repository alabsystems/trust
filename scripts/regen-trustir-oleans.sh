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

# The platform triple these bytes are built FOR, taken from Lean's own version
# string ("Lean (version 4.8.0, aarch64-apple-darwin, commit ..., Release)").
# Deliberately NOT `uname`: what matters is the triple the toolchain reports for
# the artifacts it just emitted, not the shell's idea of the host.
TRIPLE="$(printf '%s' "$LEAN_VERSION" | sed -n 's/.*version [^,]*, \([^,]*\),.*/\1/p')"
if [[ -z "$TRIPLE" ]]; then
    echo "ERROR: could not parse a platform triple out of: $LEAN_VERSION" >&2
    echo "       The vendored olean set is platform-partitioned and cannot be" >&2
    echo "       written without knowing which platform produced these bytes." >&2
    exit 1
fi
echo "platform: $TRIPLE"
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
TARGO="$ROOT/build/host/stage2/bin/targo"
# `--unverified` is a TARGO flag, and a stage2 that predates the targo rebrand ships a plain
# cargo under that name — it rejects the flag as an unknown argument and the regen dies with a
# cargo usage message that says nothing about oleans. Probe instead of assuming. Passing it when
# it IS supported still matters: this is a build tool, not a proof artifact, and a verified build
# of the whole `crates/` graph here would be minutes of work for no claim anyone reads.
# Unquoted below on purpose (bash 3.2: an empty array expansion under `set -u` aborts); the value
# is a fixed literal, so word-splitting is exactly the intent.
if "$TARGO" --unverified --version >/dev/null 2>&1; then UNVERIFIED="--unverified"; else UNVERIFIED=""; fi
(cd "$ROOT" && "$TARGO" $UNVERIFIED run --quiet --manifest-path crates/Cargo.toml \
    -p trust-clean --example bridge_closure -- "$SHIP_LIB" "$CORE_LIB") > "$CLOSURE"
N_TOTAL="$(wc -l < "$CLOSURE" | tr -d ' ')"
N_TRUSTIR="$(grep -c '^TrustIr' "$CLOSURE")"
echo "closure: $N_TOTAL modules ($N_TRUSTIR TrustIr, $((N_TOTAL - N_TRUSTIR)) Lean-core)"

# --- Check or write the vendored trees + manifests -------------------------
python3 - "$MODE" "$ROOT" "$CLOSURE" "$SHIP_LIB" "$CORE_LIB" "$COMMIT" "$TOOLCHAIN" "$LEAN_VERSION" "$CLEAN_COMMIT" "$TRIPLE" <<'EOF'
import hashlib, os, re, shutil, sys, datetime

(mode, root, closure_file, ship_lib, core_lib, commit, toolchain, lean_version,
 clean_commit, triple) = sys.argv[1:11]
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
                m.group(1), {"lean_version": "", "built_on": "", "files": {}})
            continue
        m = re.match(r'^\[platforms\."([^"]+)"\]$', line)
        if m:
            section, cur = "pmeta", platforms.setdefault(
                m.group(1), {"lean_version": "", "built_on": "", "files": {}})
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
            m2 = re.match(r'^(lean_version|built_on)\s*=\s*"(.*)"$', line)
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
            'root_module = "TrustIr.Semantics.Arith"',
            'source_subdir = "lean/trust_ir-semantics"',
            'build_command = "lake build (unmodified sources at trustir_commit; toolchain pinned by lean-toolchain)"',
            "# Minimal module closure of root_module: computed by loading the root with",
            "# clean-olean load_module_with_deps and vendoring exactly the visited TrustIr",
            "# modules. Regenerate + audit with scripts/regen-trustir-oleans.sh.",
        ]
    else:
        head = [
            'schema = "trust.vendor.lean-core-oleans.manifest.v2"', "", "[provenance]",
            f'lean_toolchain = "{toolchain}"',
            f'origin = "elan-installed {toolchain} release toolchain, lib/lean"',
            'root_module = "TrustIr.Semantics.Arith"',
            "# FOREIGN vendored artifacts (Lean 4 core Init .oleans) — the transitive",
            "# Lean-core import closure of the trust-ir arithmetic-semantics root module.",
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
        "# platform's bytes.",
    ]
    for t in sorted(platforms):
        p = platforms[t]
        lines += [
            "",
            f'[platforms."{t}"]',
            f'lean_version = "{p["lean_version"]}"',
            f'built_on = "{p["built_on"]}"',
        ]
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
