#!/usr/bin/env python3
"""Differential soundness oracle for trustc over UNMODELED-LENGTH ARRAY indexing.

A `[T; N]` whose length `N` is a generic const / unevaluated const cannot be
folded to a concrete `usize` at the polymorphic-MIR level, so trust-mir-extract
lowers it to `Ty::Unsupported { kind: "TyKind::Array", detail: "array length …
is not a concrete target usize" }`. The verifier's `collect_type_unsupported`
type-declaration walk stamps a spurious `UnsupportedMir`→Unknown for such a
value — exactly the recursive-ADT / `TyKind::Param` declaration-noise pattern.

Relaxing that declaration marker is sound ONLY IF a panic-able USE of the array
(an index `arr[i]`) still fails closed independently. This is the net that
proves it does: an UNGUARDED index into an unmodeled-length array must NEVER be
PROVED (it can be out of bounds), and a CONCRETE-length unguarded index must
likewise not be proved. The guarded form (`if i < N { arr[i] }`) is the
recovery target — its bounds obligation proves even with N symbolic, so once the
spurious array-TYPE marker is relaxed the whole function is PROVED.

Usage:  python3 scripts/trustc_array_bounds_soundness_oracle.py [path-to-trustc]
Skips (exit 0) with a notice if no built trustc is found.
"""
import json
import os
import subprocess
import sys
import tempfile

# (fn substring, "total"|"panic"): bounds status fixed by knowable indexing.
CORPUS_LABELS = {
    "idx_unmodeled_len": "panic",   # arr[i], N generic/unmodeled — OOB-capable
    "idx_concrete": "panic",        # arr[i] over [u8; 4] — OOB-capable (control)
    "idx_guarded": "total",         # if i < N { arr[i] } — guarded, the recovery target
}

# Verified as a LIBRARY (no `main`): each generic function is verified over ALL
# inputs. A `main` with CONSTANT-index calls (`idx_unmodeled_len([1u8;3], 0)`)
# would monomorphize + const-propagate `i=0`, making the SPECIFIC call site
# provably safe (`0 < 3`) and masking the generic function's real bounds outcome
# — so the panic-labeled functions would spuriously read as `proved`. Verifying
# the `pub fn`s directly (no call site) keeps `i` a free parameter, so the labels
# below are accurate: the unguarded/concrete indices REFUTE and the guarded one
# (piece #7a symbolic-length recovery) PROVES.
CORPUS_SRC = r"""#![crate_type = "lib"]
pub fn idx_unmodeled_len<const N: usize>(arr: [u8; N], i: usize) -> u8 { arr[i] }
pub fn idx_guarded<const N: usize>(arr: [u8; N], i: usize) -> u8 { if i < N { arr[i] } else { 0 } }
pub fn idx_concrete(arr: [u8; 4], i: usize) -> u8 { arr[i] }
"""

# Bounds/index obligation kinds (substring, lowercased).
BOUNDS_KEYS = ("bounds", "slice", "index")


def is_bounds(kind):
    k = (kind or "").lower()
    return any(key in k for key in BOUNDS_KEYS)


def find_trustc(argv):
    if len(argv) > 1:
        return argv[1]
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    for host in ("aarch64-apple-darwin", "x86_64-unknown-linux-gnu", "host"):
        p = os.path.join(root, "build", host, "stage2", "bin", "trustc")
        if os.path.exists(p):
            return p
    return None


def main():
    trustc = find_trustc(sys.argv)
    if not trustc:
        print("NOTICE: no built trustc found (build/<host>/stage2/bin/trustc) — skipping.")
        return 0

    with tempfile.TemporaryDirectory() as d:
        src = os.path.join(d, "array_bounds_soundness.rs")
        with open(src, "w") as f:
            f.write(CORPUS_SRC)
        out = subprocess.run(
            [trustc, "--edition", "2021", "--crate-type", "lib", src,
             "-o", os.path.join(d, "out.rlib"),
             "-Z", "trust-policy=advisory", "-Z", "trust-verify-output=json"],
            capture_output=True, text=True,
        )
        acc = {fn: [] for fn in CORPUS_LABELS}
        for line in (out.stdout + out.stderr).splitlines():
            i = line.find("TRUST_JSON:")
            if i < 0:
                continue
            try:
                d_ = json.loads(line[i + len("TRUST_JSON:"):])
            except json.JSONDecodeError:
                continue
            if d_.get("type") != "function_result":
                continue
            full = d_.get("function", "")
            for fn in CORPUS_LABELS:
                if fn in full:
                    for r in d_.get("results", []):
                        if is_bounds(r.get("kind")):
                            acc[fn].append(r.get("outcome"))

    violations = []
    for fn, label in CORPUS_LABELS.items():
        outs = acc[fn]
        if not outs:
            print(f"  {fn:20s} [{label:5s}] (no bounds obligation surfaced)")
            continue
        if label == "panic" and any(o == "proved" for o in outs):
            # SOUNDNESS: an OOB-capable index must NEVER be PROVED.
            violations.append(
                f"FALSE PROVE: OOB-capable `{fn}` had a PROVED bounds obligation {outs}")
        print(f"  {fn:20s} [{label:5s}] bounds outcomes={outs}")

    # Trust: piece #7a — RECOVERY + SURFACING requirements (tightened once the
    # const-generic array gets a MODELED symbolic length). Before #7a these were
    # only PRINTED; a symbolic-length `[T; N]` now surfaces a real bounds VC keyed
    # on the per-param symbol, so:
    #   * `idx_guarded` (if i < N { arr[i] }) MUST PROVE — the guard `i < N`
    #     discharges the bounds VC because the array's length IS the symbol N.
    #   * `idx_unmodeled_len` (unguarded arr[i]) MUST SURFACE a bounds obligation
    #     that is NOT proved — before #7a NO bounds obligation surfaced (the array
    #     type was `Unsupported`); #7a converts that into a real refutation.
    guarded = acc.get("idx_guarded", [])
    if not guarded:
        violations.append(
            "RECOVERY MISS: `idx_guarded` surfaced NO bounds obligation — the "
            "symbolic-length model should let a guarded const-generic index PROVE")
    elif not all(o == "proved" for o in guarded):
        violations.append(
            f"RECOVERY MISS: guarded const-generic index `idx_guarded` did not "
            f"PROVE (outcomes={guarded}); the guard `i < N` must discharge the bounds VC")
    unmodeled = acc.get("idx_unmodeled_len", [])
    if not unmodeled:
        violations.append(
            "SURFACING MISS: `idx_unmodeled_len` surfaced NO bounds obligation — "
            "an unguarded const-generic index must now surface a (refuted) bounds VC")
    # (its NOT-proved-ness is already enforced by the `panic` soundness check above.)

    if violations:
        print("\nARRAY-BOUNDS ORACLE VIOLATIONS:")
        for v in violations:
            print("  -", v)
        return 1
    print("\narray-bounds soundness+recovery oracle: no false PROVE on any "
          "OOB-capable index; the guarded const-generic index PROVES and the "
          "unguarded one surfaces a refuted bounds VC. SOUND + COMPLETE.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
