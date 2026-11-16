#!/usr/bin/env python3
"""Exercise actual schema-6 producer/consumer source claims, never proof authority."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / "scripts/lib"))
import landing_targo


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("observer", "targo", "sysroot", "out"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    args.out = args.out.resolve()
    args.out.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ)
    if any(env.get(key) for key in ("RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "RUSTDOCFLAGS")):
        raise RuntimeError("qualification cannot override ambient compiler flags")
    fds = landing_targo.resource_fds(env)
    paths = [Path(__file__).resolve(), HERE / "source_word64_metadata.rs",
             HERE / "source_word64_metadata/producer.rs",
             HERE / "source_word64_metadata/consumer.rs"]
    inputs = {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths}
    snapshots = args.out / "inputs"
    snapshots.mkdir()
    for index, path in enumerate(paths):
        (snapshots / f"{index}-{path.name}").write_bytes(path.read_bytes())
    (args.out / "INPUTS.json").write_text(json.dumps(inputs, indent=2) + "\n")
    env.update(CARGO_INCREMENTAL="0")

    def run(label, command, extra=None):
        result = subprocess.run(command, env=dict(env, **(extra or {})), cwd=ROOT,
                                pass_fds=fds, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE)
        (args.out / (label + ".stdout")).write_text(result.stdout)
        (args.out / (label + ".stderr")).write_text(result.stderr)
        if result.returncode:
            raise RuntimeError(f"{label} failed ({result.returncode}); evidence retained")
        return result.stdout

    compiler = args.sysroot.resolve() / "bin/trustc"
    version = run("compiler-version", [str(compiler), "-vV"])
    observer_version = run("observer-version", [str(args.observer), "-vV"])
    identity = lambda text: re.search(r"^commit-hash: ([0-9a-f]{40})$", text, re.M).group(1)
    if identity(version) != identity(observer_version):
        raise RuntimeError("observer driver and producing compiler must be the same source")
    if not run("targo-version", [str(args.targo), "--unverified", "--version"]).startswith(
            "targo "):
        raise RuntimeError("genuine Targo required")

    def manifest(name, crate, source):
        directory = args.out / name
        directory.mkdir()
        path = directory / "Cargo.toml"
        path.write_text(f'[package]\nname={json.dumps(name)}\nversion="0.0.0"\n'
                        f'edition="2021"\n[workspace]\n[lib]\nname={json.dumps(crate)}\n'
                        f'path={json.dumps(str(source))}\n'
                        '[profile.dev]\ndebug=0\nincremental=false\n')
        return path

    def command(path):
        return [str(args.targo), "--unverified", "rustc", "--offline", "--lib",
                "--manifest-path", str(path), "--target-dir", str(path.parent / "target"),
                "--message-format=json", "--", "--sysroot", str(args.sysroot.resolve()),
                "-Ztrust-ir-lower", "-Coverflow-checks=off"]

    producer = manifest("source-claim-producer", "source_claim_dep",
                        HERE / "source_word64_metadata/producer.rs")
    stdout = run("producer", command(producer), {"RUSTC": str(compiler)})
    artifacts = []
    for line in stdout.splitlines():
        try:
            item = json.loads(line)
        except json.JSONDecodeError:
            continue
        if (item.get("reason") == "compiler-artifact" and
                item.get("target", {}).get("name") == "source_claim_dep"):
            artifacts.extend(Path(path) for path in item["filenames"] if path.endswith(".rlib"))
    if len(artifacts) != 1 or not artifacts[0].is_file():
        raise RuntimeError(f"one actual producer rlib required: {artifacts}")
    consumer = manifest("source-claim-consumer", "source_claim_user",
                        HERE / "source_word64_metadata/consumer.rs")
    argv = command(consumer) + ["--extern", "source_claim_dep=" + str(artifacts[0])]
    run("consumer", argv, {"RUSTC": str(args.observer.resolve()),
                            "SOURCE_ENTRY_OUT": str(args.out / "capture")})
    callee = json.loads((args.out / "capture/CORE-CALLEE.json").read_text())
    if (callee["source_kind"] != "RegisteredWrappingAdd" or callee["parameters"] != 2 or
            callee["proof_authority"] is not False or
            callee["actual_registration_rechecked"] is not True or
            callee["actual_D28_rechecked"] is not True):
        raise RuntimeError("actual core source/IR intake failed")
    rows = json.loads((args.out / "capture/RESULTS.json").read_text())
    expected = {"identity": True, "double": True, "pair": True,
                "statements": False, "located": None}
    if {name: row["source_present"] for name, row in rows.items()} != expected:
        raise RuntimeError("complete fixed source-claim roster did not qualify")
    if any(row["proof_authority"] is not False or
           row["actual_D28_rechecked"] is not (name != "located")
           for name, row in rows.items()):
        raise RuntimeError("source data cannot replace effects or grant proof authority")
    if inputs != {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths}:
        raise RuntimeError("qualification sources changed during execution")
    (args.out / "QUALIFIED.json").write_text(json.dumps({
        "compiler_commit": identity(version), "inputs": inputs,
        "producer_rlib_sha256": hashlib.sha256(artifacts[0].read_bytes()).hexdigest(),
        "source_cases": 4, "legacy_refusal_cases": 1,
        "scope": ("Actual source-claim metadata transport only; "
                  "no source TV, ABI, NoUB or admission.")
    }, indent=2) + "\n")
    print("PASS 4/4 actual source-entry controls and 1/1 legacy refusal; no proof/admission claim")


if __name__ == "__main__":
    main()
