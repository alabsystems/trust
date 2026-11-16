#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Exercise internal-lint cache transitions through actual unverified Targo."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import shlex
import subprocess
import sys


CASES = {
    "disabled-same": (False, False),
    "enabled-same": (True, True),
    "disabled-to-enabled": (False, True),
    "enabled-to-disabled": (True, False),
}
MANIFEST = '''[package]
name="internal-lint-incremental"
version="0.0.0"
edition="2021"
[workspace]
[profile.dev]
incremental=true
debug=2
split-debuginfo="unpacked"
[lints.rust]
unknown_lints="allow"
'''
SOURCE = '''#![allow(rustc::default_hash_types, rustc::potential_query_instability)]
pub fn step(value: u64) -> u64 {{ value.wrapping_add({}) }}
'''


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def compiler_command(stderr):
    for line in stderr.splitlines():
        if "Running `" in line and "--crate-name internal_lint_incremental" in line:
            return shlex.split(line.split("Running `", 1)[1].rsplit("`", 1)[0])
    return []


def option(tokens, name):
    return name in tokens or any(
        token == "-Z" and index + 1 < len(tokens) and tokens[index + 1] == name[2:]
        for index, token in enumerate(tokens)
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--targo", type=Path, required=True)
    parser.add_argument("--rustc", type=Path, required=True)
    parser.add_argument("--evidence", type=Path, required=True)
    args = parser.parse_args()
    for path in (args.targo, args.rustc):
        assert path.is_absolute() and path.is_file(), "explicit actual native tools required"
    assert args.evidence.is_absolute() and not args.evidence.exists(), "new owned evidence required"
    environment = os.environ.copy()
    for key in ("RUSTFLAGS", "RUSTDOCFLAGS", "CARGO_ENCODED_RUSTFLAGS", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER"):
        assert not environment.get(key), "competing compiler configuration: " + key
    args.evidence.mkdir(mode=0o700, parents=True)
    before = {str(path): digest(path) for path in (args.targo, args.rustc)}
    for path, argv in ((args.targo, ["--unverified", "--version"]), (args.rustc, ["-vV"])):
        process = subprocess.run([str(path), *argv], capture_output=True)
        (args.evidence / (path.name + ".version")).write_bytes(process.stdout + process.stderr)
        assert process.returncode == 0, "native tool identity observation refused"
    rows = []
    for name, modes in CASES.items():
        root = args.evidence / name
        (root / "src").mkdir(parents=True)
        (root / "Cargo.toml").write_text(MANIFEST)
        env = dict(environment, RUSTC=str(args.rustc), CARGO_HOME=str(root / "home"),
                   CARGO_TARGET_DIR=str(root / "target"), CARGO_NET_OFFLINE="true")
        source = root / "src/lib.rs"
        source.write_text(SOURCE.format(1))
        lock = subprocess.run([str(args.targo), "generate-lockfile", "--offline"],
                              cwd=root, env=env, capture_output=True)
        (root / "lock.stdout").write_bytes(lock.stdout)
        (root / "lock.stderr").write_bytes(lock.stderr)
        row = {"case": name, "lock_exit": lock.returncode, "builds": []}
        for index, enabled in enumerate(modes if lock.returncode == 0 else []):
            source.write_text(SOURCE.format(index + 1))
            argv = [str(args.targo), "--unverified", "rustc", "--offline", "--locked",
                    "--lib", "-vv", "--", "-Zincremental-verify-ich=yes"]
            if enabled:
                argv.append("-Zunstable-options")
            process = subprocess.run(argv, cwd=root, env=env, capture_output=True)
            (root / f"{index}.stdout").write_bytes(process.stdout)
            (root / f"{index}.stderr").write_bytes(process.stderr)
            stderr = process.stderr.decode(errors="replace")
            tokens = compiler_command(stderr)
            paths = [token[len("incremental="):] for token in tokens if token.startswith("incremental=")]
            build = {"exit": process.returncode, "enabled": enabled, "incremental": paths,
                     "actual_mode": option(tokens, "-Zunstable-options"),
                     "ich_verification": option(tokens, "-Zincremental-verify-ich=yes"),  # gitleaks:allow (a rustc flag)
                     "original_ice": "shallow_lint_levels_on" in stderr and "unstable fingerprints" in stderr}
            row["builds"].append(build)
            print(json.dumps({"case": name, "phase": index, **build}), flush=True)
            if process.returncode:
                break
        builds = row["builds"]
        row["pass"] = len(builds) == 2 and all(
            build["exit"] == 0 and build["actual_mode"] == build["enabled"]
            and build["ich_verification"] and len(build["incremental"]) == 1 for build in builds
        ) and builds[0]["incremental"] == builds[1]["incremental"]
        rows.append(row)
        (args.evidence / "observations.json").write_text(json.dumps(rows, indent=2) + "\n")
    after = {str(path): digest(path) for path in (args.targo, args.rustc)}
    result = {"before": before, "after": after, "cases": rows,
              "pass": before == after and all(row["pass"] for row in rows)}
    (args.evidence / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    return 0 if result["pass"] else 1


if __name__ == "__main__":
    sys.exit(main())
