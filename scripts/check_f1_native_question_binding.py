#!/usr/bin/env python3
"""Execute the exact F1/native-question regression through genuine Trust tools."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts/lib"))
import landing_targo

PACKAGE = "trust-cg-bridge"
TARGET = "f1_native_question_binding"
TEST_NAMES = {
    "actual_native_questions_and_compiled_function_share_ir_owned_digests",
    "changed_verified_function_is_refused_even_when_unknown_output_would_ship",
    "unchanged_body_does_not_hide_a_changed_module_type_context",
}


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


def require_native_test_execution(lines):
    refusal = "the complete three-test F1 native binding inventory did not execute"
    actions, artifacts, test_stdout = [], [], []
    for line in lines:
        try:
            row = json.loads(line)
        except json.JSONDecodeError:
            continue
        if not isinstance(row, dict):
            continue
        reason = row.get("reason")
        if reason == "test-execution":
            actions.append(row)
        elif reason == "compiler-artifact" and row.get("executable"):
            target = row.get("target")
            if isinstance(target, dict) and target.get("name") == TARGET and target.get("kind") == ["test"]:
                artifacts.append(row)
        elif reason == "test-output":
            if (row.get("schema") != "targo.test-output.v1" or row.get("index") != 0
                    or row.get("stream") not in ("stdout", "stderr")
                    or not isinstance(row.get("line"), str)
                    or [a.get("state") for a in actions] != ["ready", "running"]):
                raise RuntimeError(f"{refusal}: invalid managed test output")
            if row["stream"] == "stdout":
                test_stdout.append(row["line"])

    if [a.get("state") for a in actions] != ["ready", "running", "passed"] or len(artifacts) != 1:
        raise RuntimeError(f"{refusal}: missing exact test artifact or lifecycle")
    artifact, = artifacts
    package_dir = ROOT / "crates" / PACKAGE
    manifest = artifact.get("manifest_path")
    source = artifact["target"].get("src_path")
    profile = artifact.get("profile")
    executable = artifact["executable"]
    package_id = artifact.get("package_id")
    if (not isinstance(manifest, str) or Path(manifest).resolve() != package_dir / "Cargo.toml"
            or not isinstance(source, str) or Path(source).resolve() != package_dir / "tests" / f"{TARGET}.rs"
            or not isinstance(profile, dict) or profile.get("test") is not True
            or not isinstance(executable, str) or not Path(executable).is_absolute()
            or not isinstance(package_id, str) or not package_id):
        raise RuntimeError(f"{refusal}: incorrect test artifact")
    binding = {
        "schema": "targo.test-execution.v2", "index": 0, "total": 1,
        "package": PACKAGE, "package_id": package_id, "target": TARGET, "kind": "test",
        "prerequisite_artifact": executable, "weight": 1, "signal": None,
    }
    if (any(any(key not in action or action[key] != value for key, value in binding.items())
            or action.get("harness") is not True or action.get("exclusive") is not False
            for action in actions)
            or [action.get("exit_code") for action in actions] != [None, None, 0]):
        raise RuntimeError(f"{refusal}: managed test action did not match the compiled artifact")

    # Targo reports the compiler artifact digest and the scheduler names it as
    # the prerequisite. Read back the artifact before accepting the result.
    digest = hashlib.sha256()
    with Path(executable).open("rb") as image:
        for chunk in iter(lambda: image.read(1 << 20), b""):
            digest.update(chunk)
    if digest.hexdigest() != artifact.get("trust_executable_sha256"):
        raise RuntimeError(f"{refusal}: test artifact digest changed or missing")

    successes = [
        match[1] for line in test_stdout
        if (match := re.fullmatch(r"test (\S+) \.\.\. ok", line))
    ]
    summaries = [line for line in test_stdout if line.startswith("test result:")]
    complete = "test result: ok. 3 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out;"
    if (len(successes) != len(TEST_NAMES) or set(successes) != TEST_NAMES
            or len(summaries) != 1 or not summaries[0].startswith(complete)):
        raise RuntimeError(f"{refusal}: managed stdout did not report the expected tests")


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
                "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER", "CARGO_BUILD_RUSTC", "TARGET",
                "RUST_TEST_NOCAPTURE"):
        env.pop(key, None)
    env["PATH"] = str(targo.parent) + os.pathsep + env.get("PATH", "")
    fds = landing_targo.resource_fds(env)
    genuine_targo_identity(targo, env, fds)
    argv = [
        str(ROOT / "scripts/build-slot"), "--cpus", "6", "--", str(targo),
        "--unverified", "test", "--offline", "--locked", "--manifest-path",
        str(ROOT / "Cargo.toml"), "-p", PACKAGE, "--features", "ay-proofs",
        "--test", TARGET, "--target-dir", str(args.target_dir.resolve()),
        "--config", "build.test-jobs=2", "--config", "build.test-weight=1",
        "--message-format=json-render-diagnostics", "--", "--format=pretty",
    ]
    lines = []
    with subprocess.Popen(argv, cwd=ROOT, env=env, text=True, stdout=subprocess.PIPE,
                          pass_fds=fds) as process:
        for line in process.stdout:
            print(line, end="", flush=True)
            lines.append(line)
        code = process.wait()
    if code:
        return code
    require_native_test_execution(lines)
    print("F1_NATIVE_QUESTION_BINDING_TESTS_PASSED=3", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
