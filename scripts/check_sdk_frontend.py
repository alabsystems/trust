#!/usr/bin/env python3
"""A metadata-only SDK frontend dependency canary, not proof or release evidence.

Use the exported compiler and only its own sysroot. No build-tree -L paths,
wrappers, RUSTC_BOOTSTRAP, mutable search roots or downloaded crates are used.
This checks metadata compatibility. Linking/running a frontend and the existing
native/runtime-closure checks are separate export requirements.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(sdk, expected_commit, output):
    sdk = Path(sdk).resolve(strict=True)
    output = Path(output).absolute()
    output.mkdir(parents=True, exist_ok=False)
    compiler = sdk / "bin/trustc"
    source = Path(__file__).resolve().parents[1] / "tests/fixtures/sdk_frontend_canary.rs"
    copied = output / source.name
    copied.write_bytes(source.read_bytes())
    scratch = output / "tmp"
    scratch.mkdir(mode=0o700)
    # Metadata-only rustc launches no linker, build script or solver subprocess.
    env = {"PATH": "/usr/bin:/bin:/usr/sbin:/sbin", "HOME": str(output),
           "TMPDIR": str(scratch), "LC_ALL": "C"}
    commands = []
    receipt = {"classification": "unverified frontend metadata dependency canary",
               "sdk": str(sdk), "expected_commit": expected_commit,
               "source_sha256": sha(copied), "status": "NOT JUDGED"}
    try:
        if compiler.is_symlink() or not compiler.is_file():
            raise RuntimeError("exported trustc must be an independent regular file")
        before = sha(compiler)
        def run(argv, label):
            commands.append(argv)
            result = subprocess.run(argv, env=env, cwd=output,
                                    capture_output=True, timeout=60)
            (output / (label + ".stdout")).write_bytes(result.stdout)
            (output / (label + ".stderr")).write_bytes(result.stderr)
            if result.returncode:
                raise RuntimeError(f"{label} exited {result.returncode}")
            return result.stdout.decode("utf-8", "strict")
        version = run([str(compiler), "-Vv"], "version")
        commits = re.findall(r"^commit-hash: ([0-9a-f]{40})$", version, re.M)
        if commits != [expected_commit] or "binary: trustc\n" not in version:
            raise RuntimeError("exported compiler identity differs from the frozen commit")
        sysroot = run([str(compiler), "--print", "sysroot"], "sysroot").strip()
        if Path(sysroot).resolve(strict=True) != sdk:
            raise RuntimeError("compiler resolves another SDK sysroot")
        artifact = output / "frontend_canary.rmeta"
        run([str(compiler), "-Ztrust-verify=off", "--edition=2024",
             "--crate-name", "trust_sdk_frontend_canary", "--crate-type=lib",
             "--sysroot", str(sdk), "--emit=metadata", "-o", str(artifact),
             str(copied)], "frontend")
        if not artifact.is_file() or artifact.is_symlink() or not artifact.stat().st_size:
            raise RuntimeError("metadata check did not produce nonempty metadata")
        if sha(compiler) != before:
            raise RuntimeError("exported compiler changed during the dependency canary")
        receipt.update(status="PASS", compiler_sha256=before,
                       artifact_sha256=sha(artifact), artifact_bytes=artifact.stat().st_size)
    except (OSError, RuntimeError, subprocess.TimeoutExpired, UnicodeError) as error:
        receipt.update(status="REFUSED", reason=str(error))
    finally:
        receipt["commands"] = commands
        (output / "result.json").write_text(json.dumps(receipt, indent=2) + "\n")
    return receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sdk", required=True, type=Path)
    parser.add_argument("--expected-commit", required=True)
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args()
    if not re.fullmatch(r"[0-9a-f]{40}", args.expected_commit):
        parser.error("--expected-commit must be a full lowercase commit SHA")
    result = check(args.sdk, args.expected_commit, args.out)
    print(json.dumps(result, indent=2))
    return 0 if result["status"] == "PASS" else 1

if __name__ == "__main__":
    sys.exit(main())
