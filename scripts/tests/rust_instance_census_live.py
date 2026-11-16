#!/usr/bin/env python3
"""Retained development controls for the actual Trust mono-item observer.

Requires an explicit Trust binary and new external output directory. This binds
the launcher/local drivers and fixtures, not the complete dynamic/sysroot input
closure. A separate sealed-toolchain harness is required for acceptance evidence.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
FIXTURES = ROOT / "scripts/tests/fixtures/rust-instance-census"
SPEC = importlib.util.spec_from_file_location("instance_census", ROOT / "scripts/rust_instance_census.py")
census = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(census)


def digest(path):
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(chunk)
    return value.hexdigest()


def save(path, value):
    with path.open("x") as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write("\n")


def read_report(path):
    if not path.is_file():
        return None
    with path.open("rb") as stream:
        return stream.read(census.MAX_BYTES + 1)


def comparable_snapshot(snapshot):
    """Rename invocation-local allocations bijectively, preserving aliasing.

    Inputs have already passed the census reader. First references in the
    ordered owner/occurrence population determine labels, never memory content.
    V1 snapshots retain their existing exact comparison.
    """
    if snapshot is None or snapshot.get("schema") not in (census.SCHEMA_V2, census.SCHEMA_V3):
        return snapshot
    occurrence_tables = ["dependency_occurrences"]
    if snapshot["schema"] == census.SCHEMA_V3:
        occurrence_tables.append("eager_const_root_occurrences")
    names = {}
    for table in occurrence_tables:
        for row in snapshot[table]:
            for key in ("source", "target"):
                value = row.get(key)
                if type(value) is str and value.startswith("alloc:") and value not in names:
                    names[value] = "alloc:" + str(len(names) + 1)
    result = copy.deepcopy(snapshot)
    for table in ["dependency_nodes", *occurrence_tables]:
        for row in result[table]:
            for key in ("id", "source", "target"):
                value = row.get(key)
                if type(value) is str and value.startswith("alloc:"):
                    row[key] = names[value]
    result["dependency_nodes"].sort(key=lambda row: row["id"])
    return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--trustc", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args(argv)
    compiler = args.trustc.resolve(strict=True)
    if compiler.name != "trustc":
        parser.error("explicit Trust binary required; no stock fallback")
    output = args.out.absolute()
    if output.exists() or output.is_symlink() or not output.parent.is_dir():
        parser.error("--out must be NEW with an existing parent")
    resolved_output = output.resolve()
    if resolved_output == ROOT or ROOT in resolved_output.parents:
        parser.error("--out must be external to the source checkout")
    if any(key.startswith("DYLD_") for key in os.environ):
        parser.error("remove ambient dynamic-loader overrides before this probe")
    output.mkdir()
    paths = [compiler, Path(__file__).resolve(), ROOT / "scripts/rust_instance_census.py",
             FIXTURES / "instances.rs", FIXTURES / "invalid.rs", FIXTURES / "unplaced.rs",
             *sorted((compiler.parent.parent / "lib").glob("librustc_driver-*"))]

    def snapshot():
        return {"files": {str(path): digest(path) for path in paths},
                "revision": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
                "source_status": subprocess.check_output(["git", "status", "--porcelain=v1"], cwd=ROOT, text=True)}

    before = None
    runs, errors = {}, []

    def run(label, source, *, collect=True, lowering=False, metadata=False, checksum=True, existing=None,
            optimized=False, eager=False):
        folder = output / label
        folder.mkdir()
        report = existing or folder / "census.jsonl"
        command = [str(compiler), str(source), "--edition=2024", "--crate-name=instance_probe",
                   "--crate-type=lib", "-Ztrust-verify=off", "-Zthreads=1",
                   "-Copt-level=" + ("3" if optimized else "0"),
                   "-Ztrust-ir-lower=" + ("on" if lowering else "off"), "--out-dir=" + str(folder),
                   "--emit=" + ("metadata" if metadata else "mir,obj")]
        if checksum:
            command.append("-Zchecksum-hash-algorithm=sha256")
        if eager:
            command.append("-Clink-dead-code=yes")
        if collect:
            command.append("-Ztrust-instance-census=" + str(report))
        started = time.monotonic()
        with (folder / "stdout.txt").open("xb") as stdout, (folder / "stderr.txt").open("xb") as stderr:
            try:
                code = subprocess.run(command, cwd=folder, stdout=stdout, stderr=stderr, timeout=180).returncode
            except subprocess.TimeoutExpired:
                code = None
        row = {"command": command, "exit_code": code, "elapsed_seconds": time.monotonic() - started,
               "report_sha256": digest(report) if report.is_file() else None,
               "outputs": {p.name: digest(p) for p in folder.iterdir() if p.suffix in (".o", ".mir", ".rmeta")}}
        if collect and existing is None:
            row["census"] = census.parse_census(read_report(report),
                                                input_path=str(source), exit_code=code, lowering=lowering)
        runs[label] = row
        save(folder / "result.json", row)
        print(label, "exit=" + str(code), "census=" + row.get("census", {}).get("status", "not-requested"), flush=True)
        return row

    try:
        before = snapshot()
        save(output / "before.json", before)
        version = subprocess.run([str(compiler), "-vV"], capture_output=True, text=True, timeout=30)
        save(output / "version.json", {"command": [str(compiler), "-vV"], "exit_code": version.returncode,
                                       "stdout": version.stdout, "stderr": version.stderr})
        if version.returncode != 0 or "commit-hash: " not in version.stdout:
            raise ValueError("compiler identity probe failed")
        source = FIXTURES / "instances.rs"
        baseline = run("baseline", source, collect=False)
        control = run("control", source)
        subject = run("subject", source, lowering=True)
        metadata = run("metadata", source, metadata=True)
        unplaced = run("optimized-roots", FIXTURES / "unplaced.rs", optimized=True)
        eager = run("eager-roots", FIXTURES / "unplaced.rs", optimized=True, eager=True)
        existing_path = output / "existing-census.jsonl"
        with existing_path.open("xb") as stream:
            stream.write(b"existing-output-sentinel\n")
        existing_digest = digest(existing_path)
        collision = run("existing-output", source, existing=existing_path)
        no_checksum = run("missing-checksum", source, checksum=False)
        invalid = run("invalid-source", FIXTURES / "invalid.rs")
        for label, row in (("baseline", baseline), ("control", control), ("subject", subject),
                           ("metadata", metadata), ("optimized-roots", unplaced), ("eager-roots", eager)):
            required = {".rmeta"} if label == "metadata" else {".mir", ".o"}
            if {Path(name).suffix for name in row["outputs"]} != required:
                errors.append(label + ": missing requested output population")
        if baseline["exit_code"] != 0 or not baseline["outputs"]:
            errors.append("baseline fixture did not compile")
        if control["exit_code"] != 0 or control["outputs"] != baseline["outputs"]:
            errors.append("observer failed or changed baseline emitted bytes")
        for label, row in (("control", control), ("subject", subject)):
            observed = row.get("census", {})
            if row["exit_code"] != 0 or observed.get("status") != "collector_observed":
                errors.append(label + ": actual collector not measured")
                continue
            items = observed["snapshot"]["items"]
            generic = [i for i in items if "::identity" in i["def"] and i["definition_is_local"]]
            if len(generic) != 2 or len({i["generic_args"] for i in generic}) != 2:
                errors.append(label + ": two concrete generic instantiations missing")
            if not any(i["kind"] == "shim-drop-glue" for i in items):
                errors.append(label + ": generated drop shim missing")
            if not any(i["kind"] == "static" and "::VALUE" in i["def"] for i in items):
                errors.append(label + ": static missing")
        if comparable_snapshot(control.get("census", {}).get("snapshot")) != comparable_snapshot(subject.get("census", {}).get("snapshot")):
            errors.append("lowering flag changed concrete collector/usage/CGU population")
        if metadata["exit_code"] != 0 or metadata.get("census", {}).get("status") != "unmeasured":
            errors.append("metadata-only compile did not stay explicitly unmeasured")
        for label, row, strategy in (("optimized-roots", unplaced, "lazy"), ("eager-roots", eager, "eager")):
            observed = row.get("census", {})
            if row["exit_code"] != 0 or observed.get("status") != "collector_observed":
                errors.append(label + ": actual optimized collector not measured")
            elif observed["header"]["collection_strategy"] != strategy:
                errors.append(label + ": collection strategy changed")
        # At least one close control must really exercise unplaced collected
        # items. An empty list is not fabricated into coverage of that seam.
        if not any(row.get("census", {}).get("snapshot", {}).get("unplaced_items") for row in (unplaced, eager)):
            errors.append("unplaced-item control did not exercise its intended population")
        if (collision["exit_code"] != 1 or digest(existing_path) != existing_digest
                or "cannot create NEW output" not in (output / "existing-output/stderr.txt").read_text()):
            errors.append("existing census not preserved and refused")
        if (no_checksum["exit_code"] != 1 or no_checksum["report_sha256"] is not None
                or "requires -Zchecksum-hash-algorithm=sha256" not in (output / "missing-checksum/stderr.txt").read_text()):
            errors.append("missing checksum requirement not refused before publication")
        invalid_path = output / "invalid-source/census.jsonl"
        if invalid["exit_code"] != 1 or not invalid_path.is_file():
            errors.append("invalid source did not leave an explicit incomplete census")
        else:
            # Validate only the retained partial format under a hypothetical
            # successful process. The real exit stays 1 in the run record; it
            # is never overridden or promoted into compiler success.
            partial = census.parse_census(read_report(invalid_path), input_path=str(FIXTURES / "invalid.rs"), exit_code=0)
            if partial["status"] != "incomplete":
                errors.append("invalid source did not retain exactly a valid begin record")
    except (Exception, KeyboardInterrupt) as error:
        errors.append(f"probe interrupted or failed: {type(error).__name__}: {error}")
    # Never put a return in finally: interruption or preflight failure must not
    # become an empty success report. Missing expected cases are always failures.
    expected = {"baseline", "control", "subject", "metadata", "optimized-roots", "eager-roots",
                "existing-output", "missing-checksum", "invalid-source"}
    if set(runs) != expected:
        errors.append("incomplete live control population")
    try:
        after = snapshot()
    except (Exception, KeyboardInterrupt) as error:
        after = {"snapshot_failed": f"{type(error).__name__}: {error}"}
        errors.append("final input snapshot failed")
    save(output / "after.json", after)
    stable = before is not None and before == after
    if not stable:
        errors.append("probe inputs changed")
    result = {"kind": "mono-item-census-development-controls-not-G1", "status": "failed" if errors else "passed",
              "inputs_stable": stable, "runs": runs, "errors": errors,
              "complete_toolchain_closure_bound": False, "whole_program_complete": False}
    save(output / "result.json", result)
    print(json.dumps({"status": result["status"], "errors": errors, "output": str(output)}, indent=2))
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
