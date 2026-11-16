#!/usr/bin/env python3
"""Regenerate the E6 differential harness fixtures from shapes.rs.

Usage:
    python3 crates/trust-certify/tests/fixtures/e6_differential/regen.py <trustc>

Compiles `shapes.rs` twice with the given Trust compiler — once without and once
with `-O`, because the E6 readers see the optimizer's MIR — under
`-Ztrust-dump=mir:<dir>`, which serializes every extracted `VerifiableFunction`
exactly as the E6 intake receives it (`trust_verify.rs`, the dump beside
`record_fn_facets`). The per-function dumps are collected into
`shapes.unopt.json` / `shapes.opt.json`, keyed by def path, with the FNV-1a-64
hash of `shapes.rs` and the compiler's version recorded. The harness
(`crates/trust-certify/tests/e6_differential.rs`) refuses fixtures whose hash
does not match the source it `include!`s.

The compile is expected to FAIL verification (the shapes carry no contracts and
some are refused on purpose): extraction and the dump happen before
verification, so a non-zero exit is fine as long as every function was dumped.
"""
from __future__ import annotations

import json
import pathlib
import re
import subprocess
import sys
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
SOURCE = HERE / "shapes.rs"
# Compiled from the repo root through a RELATIVE path, so every span's `file`
# is repo-relative: a committed dump may not carry a machine path
# (scripts/check_fixture_span_paths.py, and the publication guard).
REPO_ROOT = HERE.parents[4]
SOURCE_REL = SOURCE.relative_to(REPO_ROOT)
CRATE = "e6_shapes"


def fnv1a64(data: bytes) -> str:
    h = 0xCBF29CE484222325
    for b in data:
        h ^= b
        h = (h * 0x100000001B3) & 0xFFFFFFFFFFFFFFFF
    return f"{h:016x}"


def main() -> int:
    if len(sys.argv) != 2:
        print(__doc__, file=sys.stderr)
        return 2
    trustc = sys.argv[1]
    version = subprocess.run(
        [trustc, "--version"], capture_output=True, text=True, check=True
    ).stdout.strip()
    source = SOURCE.read_bytes()
    declared = re.findall(r"^pub fn (\w+)\(", source.decode(), flags=re.M)
    for tag, flags in (("unopt", []), ("opt", ["-O"])):
        with tempfile.TemporaryDirectory() as dump, tempfile.TemporaryDirectory() as out:
            cmd = [
                trustc,
                "--edition",
                "2024",
                "--crate-type",
                "lib",
                "--crate-name",
                CRATE,
                "-Ztrust-verify=on",
                f"-Ztrust-dump=mir:{dump}",
                "--out-dir",
                out,
                *flags,
                str(SOURCE_REL),
            ]
            subprocess.run(cmd, capture_output=True, text=True, cwd=REPO_ROOT)
            functions = {}
            for path in sorted(pathlib.Path(dump).glob("*.json")):
                func = json.loads(path.read_text())
                def_path = func["def_path"]
                if def_path.startswith(f"{CRATE}::") and def_path.count("::") == 1:
                    functions[def_path] = func
        missing = [n for n in declared if f"{CRATE}::{n}" not in functions]
        if missing:
            print(f"[{tag}] no dump for: {', '.join(missing)}", file=sys.stderr)
            return 1
        doc = {
            "generator": "crates/trust-certify/tests/fixtures/e6_differential/regen.py",
            "compiler": version,
            "flags": flags,
            "source_fnv1a64": fnv1a64(source),
            "functions": dict(sorted(functions.items())),
        }
        target = HERE / f"shapes.{tag}.json"
        text = json.dumps(doc, separators=(",", ":"), sort_keys=False) + "\n"
        for leak in (str(pathlib.Path.home()), "/private/", "/var/folders/"):
            if leak in text:
                print(f"[{tag}] the dump carries a machine path ({leak}); refusing", file=sys.stderr)
                return 1
        target.write_text(text)
        print(f"[{tag}] {len(functions)} function(s) -> {target} ({target.stat().st_size} bytes)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
