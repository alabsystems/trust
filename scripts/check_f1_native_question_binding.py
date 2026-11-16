#!/usr/bin/env python3
"""Execute the exact F1/native-question regression through genuine Trust tools."""

import argparse
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts/lib"))
import landing_targo


def genuine_targo_identity(targo, env, fds):
    # Acceptance of the explicit lane distinguishes Targo from an upstream
    # Cargo binary under that filename. Release branding formats can differ.
    output = subprocess.check_output(
        [str(targo), "--unverified", "--version"], cwd=ROOT, env=env,
        text=True, pass_fds=fds,
    )
    lines = output.strip().splitlines()
    identity = lines[0] if lines else ""
    if not identity.startswith("targo "):
        raise RuntimeError("selected tool is not genuine Targo: " + identity)
    return identity


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--targo", type=Path, required=True)
    parser.add_argument("--target-dir", type=Path, required=True)
    args = parser.parse_args()
    targo = args.targo.resolve(strict=True)
    env = os.environ.copy()
    # The explicit Targo lane owns compiler selection and build-script TARGET.
    # Compiletest's wrapper and TARGET describe its subjects, not this host
    # test build; leaking TARGET also invalidates otherwise identical facts.
    for key in ("RUSTC", "RUSTDOC", "RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS",
                "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER", "CARGO_BUILD_RUSTC", "TARGET"):
        env.pop(key, None)
    env["PATH"] = str(targo.parent) + os.pathsep + env.get("PATH", "")
    fds = landing_targo.resource_fds(env)
    genuine_targo_identity(targo, env, fds)
    argv = [
        str(ROOT / "scripts/build-slot"), "--cpus", "6", "--", str(targo),
        "--unverified", "test", "--offline", "--locked", "--manifest-path",
        str(ROOT / "Cargo.toml"), "-p", "trust-cg-bridge", "--features", "ay-proofs",
        "--test", "f1_native_question_binding", "--target-dir", str(args.target_dir.resolve()),
        "--config", "build.test-jobs=2", "--config", "build.test-weight=1",
        "--", "--nocapture",
    ]
    lines = []
    with subprocess.Popen(argv, cwd=ROOT, env=env, text=True, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, pass_fds=fds) as process:
        for line in process.stdout:
            print(line, end="", flush=True)
            lines.append(line)
        code = process.wait()
    if code:
        return code
    if not re.search(r"test result: ok\.\s+3 passed;\s+0 failed;\s+0 ignored;", "".join(lines)):
        raise RuntimeError("the complete three-test F1 native binding inventory did not execute")
    print("F1_NATIVE_QUESTION_BINDING_TESTS_PASSED=3", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
