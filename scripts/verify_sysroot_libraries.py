#!/usr/bin/env python3
"""Check the structural library surface of a full Trust SDK.

library/sysroot/Cargo.toml selects std, test, proc_macro and trust-bignum;
std's dependency closure also supplies core, alloc and compiler_builtins.
Declared full-library targets and other installed targets carrying std must
contain that closure. Other installed targets may be core-only: they must carry
a core rlib, and their public artifact cohorts are checked.

This checks filenames, file types and sizes, not metadata semantics or proofs.
The build, UI and consumer gates remain necessary.
"""

import argparse
import json
from pathlib import Path
import re
import stat


REQUIRED = ("core", "alloc", "std", "compiler_builtins", "test", "proc_macro", "trust_bignum")
PUBLIC_CRATES = REQUIRED + ("libc", "hashbrown")
ARTIFACT_PATTERNS = {
    crate: re.compile(r"lib" + re.escape(crate) + r"(?:-(.*))?\.(rlib|rmeta)\Z", re.DOTALL)
    for crate in PUBLIC_CRATES
}


def target_name(value):
    if not value or value in (".", "..") or "/" in value or "\\" in value or "\0" in value:
        raise argparse.ArgumentTypeError("a target must be one directory name")
    return value


def inspect(sysroot, targets):
    root = Path(sysroot).resolve(strict=True)
    if not root.is_dir():
        raise ValueError("sysroot is not a directory")
    declared = set(targets)
    if not declared:
        raise ValueError("declare at least the compiler host as a full-library target")
    for target in declared:
        target_name(target)
    rustlib = root / "lib/rustlib"
    installed = set()
    if rustlib.is_dir():
        installed = {entry.name for entry in rustlib.iterdir()
                     if entry.is_dir() and (entry / "lib").is_dir()}
    result = {"schema": "trust.sysroot-library-surface.v1", "sysroot": str(root),
              "declared_full_library_targets": sorted(declared), "targets": {},
              "errors": [], "semantic_qualification": False}
    for target in sorted(declared | installed):
        lib = rustlib / target / "lib"
        if not lib.is_dir() or lib.resolve(strict=True) != lib:
            result["errors"].append(f"{target}: missing or aliased public library directory")
            continue
        files = list(lib.iterdir())
        full = target in declared or any(
            ARTIFACT_PATTERNS["std"].fullmatch(p.name) for p in files)
        crates = {}
        for crate in PUBLIC_CRATES:
            # Rust's artifact suffix is an opaque disambiguator. A renamed
            # artifact can still participate in lookup; do not ignore it just
            # because the suffix is not a lowercase hexadecimal hash.
            pattern = ARTIFACT_PATTERNS[crate]
            artifacts = []
            for path in sorted(files):
                match = pattern.fullmatch(path.name)
                if not match:
                    continue
                if not match[1] or "\n" in match[1] or "\r" in match[1]:
                    result["errors"].append(f"{target}: invalid public library filename {path.name!r}")
                    continue
                meta = path.lstat()
                if not stat.S_ISREG(meta.st_mode) or not meta.st_size:
                    result["errors"].append(f"{target}: invalid public library {path.name}")
                    continue
                artifacts.append({"file": path.name, "artifact_id": match[1],
                                  "kind": match[2], "bytes": meta.st_size})
            crates[crate] = artifacts
            required = crate == "core" or (full and crate in REQUIRED)
            if required and not any(a["kind"] == "rlib" for a in artifacts):
                result["errors"].append(f"{target}: missing {crate} rlib")
            if len({a["artifact_id"] for a in artifacts}) > 1:
                names = ", ".join(a["file"] for a in artifacts)
                result["errors"].append(f"{target}: multiple public {crate} artifact cohorts: {names}")
        result["targets"][target] = {"full_library_required": full, "crates": crates}
    return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sysroot", type=Path, required=True)
    parser.add_argument("--target", type=target_name, action="append", required=True,
                        help="declared full-library target; repeat for each promised target")
    args = parser.parse_args(argv)
    try:
        result = inspect(args.sysroot, args.target)
    except (OSError, ValueError) as error:
        result = {"schema": "trust.sysroot-library-surface.v1", "errors": [str(error)],
                  "semantic_qualification": False}
    print(json.dumps(result, sort_keys=True))
    return 1 if result["errors"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
