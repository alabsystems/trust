#!/usr/bin/env python3
"""Retained development controls for the actual compiler Lean-island observer.

Live use requires explicit --trustc and a NEW external --out directory. No
compiler fallback, blessing, skipped control, producer denominator or runtime
completion claim exists here. Complete sysroot/native/toolchain closure must be
bound by an outer harness; this driver binds exact local inputs and the driver
actually loaded by direct -vV probes. Inline unit tests use mocked children only.

The script-test aggregate runs only the seven mocks through the adjacent
lean_island_census_live_test.py entry point. The 20 live cases require this
driver's explicit --trustc/--out invocation; no standing live lane is implied.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import signal
import subprocess
import time
import unittest
from unittest import mock
import tempfile

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("lean_census_live_reader", ROOT / "scripts/lean_island_census.py")
census = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(census)

# These are the complete fixed fixture inputs, not extracted producer rows.
FIXTURES = {
    "zero.rs": b"pub fn rust_value() -> u8 { 7 }\n",
    "ordered.rs": """#![allow(dead_code)]
clean {
    def πρόταση : Prop := True
    def απόδειξη : True := True.intro
    theorem θεώρημα : True := True.intro
    def Τύπος : Type := Nat
    def υπολογισμός (n : UInt8) : UInt8 := n
    inductive CensusChoice where
    | first : CensusChoice
    | second : CensusChoice
}
clean {
    theorem δεύτερο : True := απόδειξη
}
pub fn rust_value() -> u8 { 7 }
""".encode("utf-8"),
    "modules.rs": b"""#[cfg(any())]
clean mod intentionally_missing;
#[cfg(any())]
clean { theorem absentByCfg : True := True.intro }
mod nested;
clean mod external;
""",
    "nested.rs": b"clean { theorem nestedProof : True := True.intro }\n",
    "external.clean": b"theorem externalProof : True := True.intro\n",
    # LEAN-CENSUS-IMPORT-BATCH-1: Clean's lexer selects the suffix (a comment
    # naming trust_import_ no longer does), so each suffix names a real import.
    "suffix.rs": b"""pub fn first(a: u64, _b: u64) -> u64 { a }
clean { theorem headerProof : True := True.intro }
clean { theorem suffixProof (a b : UInt64) : trust_import_lean_census_probe__first a b = a := rfl }
clean { theorem followingProof : True := headerProof }
""",
    "rejected.rs": b"""clean { theorem headerProof : True := True.intro }
clean {
    def retainedBeforeFailure : Nat := 7
    theorem missingImport : True := trust_import_missing_from_this_fixture
}
clean { theorem followingRejectedProof : True := True.intro }
""",
    "parse-error.rs": b"pub fn incomplete( {\n",
    "lean-mismatch.rs": b"clean { def wrongType : Nat := True }\n",
    "duplicate-header.rs": b"""clean { theorem repeatedHeader : True := True.intro }
clean { theorem repeatedHeader : True := True.intro }
""",
    "resolver-rejected.rs": b"""clean { def cannotMint (x : UInt8) : UInt8 := True }
pub fn call_refused(x: u8) -> u8 { cannotMint(x) }
""",
    "all-deferred.rs": b"""pub fn rust_value(x: u8) -> u8 { x }
clean { theorem deferredProof (x : UInt8) : trust_import_lean_census_probe__rust_value x = x := rfl }
""",
    "relative.rs": b"""pub static BYTES: &[u8] = include_bytes!("bytes.bin");
clean { theorem relativeProof : True := True.intro }
""",
    "bytes.bin": b"\xff\xfe\x00\x01\x80",
}

# Every required invocation is retained even if preflight or an earlier case
# fails. The two parity pairs use the same source, compiler and language lane.
CASES = [
    ("zero", "zero.rs", {}),
    ("ordered-baseline", "ordered.rs", {"collect": False}),
    ("ordered", "ordered.rs", {}),
    ("modules", "modules.rs", {}),
    ("enabled-baseline", "suffix.rs", {"collect": False, "verification": True}),
    ("enabled-suffix", "suffix.rs", {"verification": True}),
    ("disabled-suffix", "suffix.rs", {}),
    ("rejected-disabled", "rejected.rs", {}),
    ("rejected-enabled", "rejected.rs", {"verification": True}),
    ("parse-error", "parse-error.rs", {}),
    ("lean-mismatch", "lean-mismatch.rs", {}),
    ("duplicate-header", "duplicate-header.rs", {}),
    ("resolver-rejected-baseline", "resolver-rejected.rs", {"collect": False}),
    ("resolver-rejected", "resolver-rejected.rs", {}),
    ("resolver-rejected-enabled", "resolver-rejected.rs", {"verification": True}),
    ("all-deferred", "all-deferred.rs", {}),
    ("metadata", "ordered.rs", {"metadata": True}),
    ("existing-output", "zero.rs", {"existing": True}),
    ("missing-sha", "zero.rs", {"checksum": False}),
    ("relative-remap-binary", "relative.rs", {"relative": True}),
]


def digest(path):
    value = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(chunk)
    return value.hexdigest()


def save(path, value):
    # Serialize fully before exclusive creation; malformed values cannot leave
    # a partial JSON receipt. Escaping also makes diagnostic Unicode harmless.
    raw = (json.dumps(value, indent=2, sort_keys=True, allow_nan=False) + "\n").encode("utf-8")
    with Path(path).open("xb") as stream:
        stream.write(raw)


def read_report(path):
    if not path.is_file():
        return None
    with path.open("rb") as stream:
        return stream.read(census.MAX_BYTES + 1)


def execute(command, cwd, folder, timeout):
    """Own/reap the actual child; a timeout is not a natural compiler exit."""
    row = {"command": command, "cwd": str(cwd), "exit_code": None,
           "reaped_child_exit": None, "timed_out": False, "launch_error": None}
    started = time.monotonic()
    child = None
    with (folder / "stdout.txt").open("xb") as stdout, (folder / "stderr.txt").open("xb") as stderr:
        try:
            child = subprocess.Popen(command, cwd=cwd, stdout=stdout, stderr=stderr,
                                     start_new_session=True)
            row["child_pid"] = child.pid
            try:
                row["exit_code"] = child.wait(timeout=timeout)
                row["reaped_child_exit"] = row["exit_code"]
            except subprocess.TimeoutExpired:
                row["timed_out"] = True
                if child.poll() is None:
                    os.killpg(child.pid, signal.SIGTERM)
                try:
                    row["reaped_child_exit"] = child.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    os.killpg(child.pid, signal.SIGKILL)
                    row["reaped_child_exit"] = child.wait()
        except OSError as error:
            row["launch_error"] = f"{type(error).__name__}: {error}"
        except BaseException:
            if child is not None and child.poll() is None:
                os.killpg(child.pid, signal.SIGTERM)
                try:
                    child.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    os.killpg(child.pid, signal.SIGKILL)
                    child.wait()
            raise
    row["elapsed_seconds"] = time.monotonic() - started
    return row


def run_case(compiler, output, label, filename, *, collect=True, verification=False,
             metadata=False, checksum=True, existing=False, relative=False, timeout=180):
    folder = output / label
    folder.mkdir()
    fixture_root = output / "fixtures"
    source = fixture_root / filename
    report = output / "existing-census.jsonl" if existing else folder / "census.jsonl"
    source_arg = filename if relative else str(source)
    command = [str(compiler), source_arg, "--edition=2024", "--crate-name=lean_census_probe",
               "--crate-type=lib", "-Ztrust-verify=" + ("on" if verification else "off"),
               "-Ztrust-ir-lower=off", "-Zthreads=1", "-Copt-level=0", "-Cdebuginfo=0",
               "--out-dir=" + str(folder), "--emit=" + ("metadata" if metadata else "mir,obj")]
    if checksum:
        command.append("-Zchecksum-hash-algorithm=sha256")
    if collect:
        command.append("-Ztrust-lean-census=" + str(report))
    if relative:
        command.append("--remap-path-prefix=" + str(fixture_root) + "=/lean-census-remapped")
    # Session::trust_ir_lower_enabled_by_flags makes verification-on imply
    # direct lowering even with an explicit requested `off`. Bind the effective
    # lane from this fixed command's flags, never from the observed JSON header.
    # Verification-off is the lane in which the explicit `off` takes effect.
    effective_lowering = verification
    row = execute(command, fixture_root, folder, timeout)
    row.update(source=str(source), verification=verification,
               requested_lowering=False, lowering=effective_lowering, collect=collect,
               report_sha256=digest(report) if report.is_file() else None,
               stdout_sha256=digest(folder / "stdout.txt"), stderr_sha256=digest(folder / "stderr.txt"),
               outputs={p.name: digest(p) for p in folder.iterdir() if p.suffix in (".o", ".mir", ".rmeta")})
    if collect:
        # Never replace a rejected compiler exit with hypothetical success.
        # Timeout retains its prefix with unknown natural exit, and separately
        # exposes the actual cleanup/reap status in reaped_child_exit.
        row["census"] = census.parse_census(read_report(report), input_path=str(source),
                                          verification=verification, lowering=effective_lowering,
                                          exit_code=row["exit_code"])
    save(folder / "result.json", row)
    print(label, "exit=" + str(row["exit_code"]),
          "records=" + row.get("census", {}).get("record_status", "not-requested"), flush=True)
    return row


def rows(run):
    return [entry["declaration"] for entry in run.get("census", {}).get("declarations", [])]


def events(run):
    return run.get("census", {}).get("validated_prefix", [])


def verdicts(runs, output, existing_digest):
    """Assertions over the full fixed population, never a successful-only subset."""
    controls = {}
    positive = {name for name, _, _ in CASES} - {
        "rejected-disabled", "rejected-enabled", "parse-error", "lean-mismatch",
        "duplicate-header", "existing-output", "missing-sha",
        "resolver-rejected-baseline", "resolver-rejected", "resolver-rejected-enabled"}
    for label, _, options in CASES:
        row = runs.get(label, {})
        controls[label + ":finished"] = bool(row) and row.get("exit_code") is not None and not row.get("timed_out") and not row.get("launch_error") and not row.get("harness_error")
        if label in positive:
            required = {".rmeta"} if options.get("metadata") else {".mir", ".o"}
            controls[label + ":success-and-artifacts"] = row.get("exit_code") == 0 and {Path(name).suffix for name in row.get("outputs", {})} == required
            if options.get("collect", True):
                controls[label + ":complete-observation"] = row.get("census", {}).get("record_status") == "observed-complete" and row["census"]["process_status"] == "success"
        if options.get("collect", True) and "census" in row:
            observed = row["census"]
            controls[label + ":diagnostic-boundary"] = (
                observed["binding_status"] == "unverified" and not observed["whole_program_complete"]
                and observed["runtime_body_universe"] == "unmeasured"
                and observed["denominator_status"] == "denominator_unverified"
                and all(item["runtime_classification"] == "unmeasured" for item in rows(row))
                and all(entry["declaration"]["runtime_classification"] == "unmeasured"
                        for entry in observed.get("resolver_declarations", [])))
    for baseline, subject in [("ordered-baseline", "ordered"), ("enabled-baseline", "enabled-suffix")]:
        left, right = runs.get(baseline, {}), runs.get(subject, {})
        controls[subject + ":observer-parity"] = left.get("exit_code") == right.get("exit_code") == 0 and bool(left.get("outputs")) and left.get("outputs") == right.get("outputs")
    controls["zero:empty-inventory"] = runs.get("zero", {}).get("census", {}).get("inventory") == [] and not rows(runs.get("zero", {}))
    ordered = runs.get("ordered", {})
    by_name = {row["name"]: row for row in rows(ordered)}
    expected_classes = {"πρόταση": "type-family", "απόδειξη": "proof-only", "θεώρημα": "proof-only",
                        "Τύπος": "type-family", "υπολογισμός": "computational-candidate", "δεύτερο": "proof-only",
                        "CensusChoice": "type-family", "CensusChoice.first": "primitive-candidate",
                        "CensusChoice.second": "primitive-candidate", "CensusChoice.rec": "primitive-candidate",
                        "CensusChoice.recOn": "primitive-candidate"}
    for name, kind in expected_classes.items():
        controls["ordered:class:" + name] = by_name.get(name, {}).get("kernel_classification", {}).get("kind") == kind
    controls["ordered:two-actual-islands"] = len(ordered.get("census", {}).get("inventory") or []) == 2
    controls["ordered:generated-owner"] = by_name.get("CensusChoice.recOn", {}).get("ownership") == "kernel-inductive-owner"
    controls["ordered:bodyless-recursor-retained"] = by_name.get("CensusChoice.rec", {}).get("has_value") is False
    controls["ordered:authored-order"] = [event["islands"] for event in ordered.get("census", {}).get("checks", [])] == [[0, 1]]
    module_names = {row["name"] for row in rows(runs.get("modules", {}))}
    controls["modules:cfg-and-loaded-unit"] = {"nestedProof", "externalProof"} <= module_names and "absentByCfg" not in module_names and len(runs.get("modules", {}).get("census", {}).get("inventory") or []) == 2
    # LEAN-CENSUS-IMPORT-BATCH-1 (census v3): TG14 checks the deferred suffix as
    # ONE header-first import batch after the admission boundary, which both
    # lanes record (TG3 mints admissions with verification off too).
    for label, verification in [("enabled-suffix", True), ("disabled-suffix", False)]:
        expected = ["pre-walk-header-first", "post-admission-import-batch" if verification else "verification-disabled-import-batch"]
        actual = runs.get(label, {})
        checks = actual.get("census", {}).get("checks", [])
        controls[label + ":exact-phases"] = [item["mode"] for item in checks] == expected
        controls[label + ":one-suffix-batch"] = [item["islands"] for item in checks] == [[0], [1, 2]]
        controls[label + ":admission-boundary"] = sum(event["event"] == "program_admissions_boundary" for event in events(actual)) == 1
        controls[label + ":complete-suffix"] = {"headerProof", "suffixProof", "followingProof"} <= {row["name"] for row in rows(actual)}
    # TG14's semantics, accepted by v3 and not re-pinned to get green: the
    # refused unit is excluded with nothing retained from it, the following
    # island commits, and the refused import does not taint the session.
    for label in ["rejected-disabled", "rejected-enabled"]:
        row = runs.get(label, {})
        observed = row.get("census", {})
        checks = observed.get("checks", [])
        names = {item["name"] for item in rows(row)}
        stderr_path = output / label / "stderr.txt"
        stderr = stderr_path.read_text(errors="replace") if stderr_path.is_file() else ""
        controls[label + ":real-rejection-prefix"] = row.get("exit_code") == 1 and observed.get("process_status") == "failed" and observed.get("record_status") == "incomplete" and not any(event["event"] == "complete" for event in events(row))
        controls[label + ":refused-unit-excluded-following-retained"] = (
            "followingRejectedProof" in names and "retainedBeforeFailure" not in names and len(checks) == 2
            and checks[1]["rejected"] and not checks[1]["kernel_roster"]["session_tainted"]
            and (checks[1]["kernel_roster"].get("import_recovery") or {}).get("refused_units") == [0])
        controls[label + ":exact-missing-name-error"] = "trust_import_missing_from_this_fixture" in stderr and "Lean island census" not in stderr
    early = runs.get("parse-error", {})
    controls["parse-error:begin-only"] = early.get("exit_code") == 1 and early.get("census", {}).get("process_status") == "failed" and early.get("census", {}).get("record_status") == "incomplete" and [event["event"] for event in events(early)] == ["begin"]
    for label, expected_diagnostic in [("lean-mismatch", "expected Nat, got Prop"),
                                       ("duplicate-header", "is declared twice in this batch")]:
        row = runs.get(label, {})
        stderr_path = output / label / "stderr.txt"
        stderr = stderr_path.read_text(errors="replace") if stderr_path.is_file() else ""
        controls[label + ":actual-early-rejection"] = (row.get("exit_code") == 1
            and row.get("census", {}).get("process_status") == "failed"
            and row.get("census", {}).get("record_status") == "incomplete"
            and any(item["rejected"] for item in row.get("census", {}).get("resolver_checks", []))
            and expected_diagnostic.lower() in stderr.lower())
        controls[label + ":no-fabricated-terminal-kernel-check"] = (
            "the island was parsed by the Clean parser and checked by the Clean CIC kernel" not in stderr)
    # Each stage observed a different actual checking session. Repeated names
    # are not additional program bodies and never enter the HIR rows() helper.
    root_rows = ordered.get("census", {}).get("resolver_declarations", [])
    root_by_name = {entry["declaration"]["name"]: entry["declaration"] for entry in root_rows}
    for name, kind in expected_classes.items():
        controls["ordered:resolver-class:" + name] = root_by_name.get(name, {}).get("kernel_classification", {}).get("kind") == kind
    root_checks = ordered.get("census", {}).get("resolver_checks", [])
    hir_checks = ordered.get("census", {}).get("checks", [])
    controls["ordered:separate-root-and-hir-checks"] = (
        len(root_checks) == len(hir_checks) == 1
        and root_checks[0]["mode"] == "root-fragment-header-first"
        and root_checks[0]["sequence"] < hir_checks[0]["sequence"]
        and len(rows(ordered)) == len(hir_checks[0]["kernel_roster"]["declarations"])
        and len(root_rows) == len(root_checks[0]["kernel_roster"]["declarations"]))
    controls["zero:empty-root-observation"] = (
        runs.get("zero", {}).get("census", {}).get("resolver_inventory") == []
        and runs.get("zero", {}).get("census", {}).get("resolver_checks") == [])
    deferred = runs.get("all-deferred", {}).get("census", {})
    controls["all-deferred:no-fabricated-resolver-check"] = (
        len(deferred.get("resolver_inventory") or []) == 1
        and deferred.get("resolver_checks") == []
        and any(row["declaration"]["name"] == "deferredProof" for row in deferred.get("declarations", [])))
    for label in ("resolver-rejected", "resolver-rejected-enabled"):
        row = runs.get(label, {})
        observed = row.get("census", {})
        checks = observed.get("resolver_checks", [])
        controls[label + ":early-rejection-retained"] = (
            row.get("exit_code") == 1 and observed.get("record_status") == "incomplete"
            and len(checks) == 1 and checks[0]["rejected"]
            and checks[0]["kernel_roster"]["check_rejected"]
            and bool(checks[0]["kernel_roster"]["source_declarations"])
            and observed.get("inventory") is None and observed.get("checks") == []
            and [event["event"] for event in events(row)] == ["begin", "resolver_inventory", "resolver_check"])
    baseline = runs.get("resolver-rejected-baseline", {})
    observed = runs.get("resolver-rejected", {})
    controls["resolver-rejected:observer-parity"] = (
        baseline.get("exit_code") == observed.get("exit_code") == 1
        and baseline.get("outputs") == observed.get("outputs") == {}
        and baseline.get("stderr_sha256") == observed.get("stderr_sha256"))
    controls["metadata:actual-checks-not-mono-collection"] = bool(runs.get("metadata", {}).get("census", {}).get("checks")) and {item["name"] for item in rows(runs.get("metadata", {}))} == set(by_name)
    collision = runs.get("existing-output", {})
    controls["existing-output:preserved"] = collision.get("exit_code") == 1 and digest(output / "existing-census.jsonl") == existing_digest and not collision.get("outputs")
    controls["existing-output:exact-refusal"] = "cannot create NEW output" in (output / "existing-output/stderr.txt").read_text(errors="replace") if (output / "existing-output/stderr.txt").is_file() else False
    missing = runs.get("missing-sha", {})
    controls["missing-sha:no-publication"] = missing.get("exit_code") == 1 and missing.get("report_sha256") is None and not missing.get("outputs")
    controls["missing-sha:exact-refusal"] = "requires -Zchecksum-hash-algorithm=sha256" in (output / "missing-sha/stderr.txt").read_text(errors="replace") if (output / "missing-sha/stderr.txt").is_file() else False
    remapped = runs.get("relative-remap-binary", {})
    footers = [event for event in events(remapped) if event["event"] == "complete"]
    binary = [item for footer in footers for item in footer["loaded_sources"] if Path(item["file"]).name == "bytes.bin"]
    controls["relative-remap:exact-root-label"] = bool(events(remapped)) and events(remapped)[0]["input"] == str(output / "fixtures/relative.rs")
    controls["binary:honest-empty-text-surrogate"] = len(binary) == 1 and binary[0]["source_map_checksum_sha256"] == hashlib.sha256(b"").hexdigest() and binary[0]["raw_auxiliary_input_bytes"] == "unmeasured" and binary[0]["source_map_checksum_sha256"] != digest(output / "fixtures/bytes.bin")
    controls["binary:build-io-unmeasured"] = bool(footers) and footers[0]["source_map_checksum_scope"] == census.SOURCE_MAP_CHECKSUM_SCOPE and footers[0]["other_inputs"]["raw_file_bytes"] == "unmeasured"
    return controls


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--trustc", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--timeout", type=int, default=180)
    args = parser.parse_args(argv)
    compiler = args.trustc.resolve(strict=True)
    if compiler.name != "trustc" or not compiler.is_file():
        parser.error("explicit real trustc binary required; no compiler fallback")
    if not 1 <= args.timeout <= 1800:
        parser.error("--timeout must be between 1 and 1800 seconds")
    output = args.out.absolute()
    if output.exists() or output.is_symlink() or not output.parent.is_dir():
        parser.error("--out must be NEW with an existing parent")
    if output.resolve() == ROOT or ROOT in output.resolve().parents:
        parser.error("--out must be external to the source checkout")
    compiler_root = compiler.parent.parent
    if output.resolve() == compiler_root or compiler_root in output.resolve().parents:
        parser.error("--out must be external to the selected compiler sysroot")
    if any(key.startswith(("DYLD_", "LD_", "RUST", "CARGO_", "TRUST_")) for key in os.environ):
        parser.error("remove ambient compiler/loader overrides before the probe")
    output.mkdir()
    fixture_root = output / "fixtures"
    fixture_root.mkdir()
    for name, raw in FIXTURES.items():
        with (fixture_root / name).open("xb") as stream:
            stream.write(raw)
    existing = output / "existing-census.jsonl"
    with existing.open("xb") as stream:
        stream.write(b"retained-existing-output-sentinel\n")
    existing_digest = digest(existing)
    input_paths = [compiler, Path(__file__).resolve(), ROOT / "scripts/lean_island_census.py",
                   ROOT / "compiler/rustc_mir_transform/src/trust_lean_census.rs",
                   ROOT / "compiler/rustc_mir_transform/src/trust_lean_census_order.rs",
                   ROOT / "compiler/rustc_mir_transform/src/trust_verify.rs",
                   ROOT / "compiler/rustc_interface/src/passes.rs",
                   ROOT / "compiler/rustc_session/src/options.rs",
                   ROOT / "compiler/rustc_session/src/session.rs",
                   ROOT / "compiler/rustc_session/src/trust_lean_census.rs",
                   ROOT / "compiler/rustc_session/src/lib.rs",
                   ROOT / "compiler/rustc_session/Cargo.toml",
                   ROOT / "compiler/rustc_resolve/src/trust_clean_mint.rs",
                   ROOT / "compiler/rustc_resolve/src/macros.rs",
                   ROOT / "Cargo.lock",
                   ROOT / "crates/trust-certify/src/clean_census.rs",
                   ROOT / "crates/trust-certify/src/clean_island.rs",
                   ROOT / "crates/trust-certify/src/clean_island_batch.rs",
                   *(fixture_root / name for name in FIXTURES)]

    def snapshot(label):
        env = dict(os.environ)
        env["DYLD_PRINT_LIBRARIES"] = "1"
        version = subprocess.run([str(compiler), "-vV"], env=env, capture_output=True, timeout=30)
        with (output / (label + "-version.stdout")).open("xb") as stream:
            stream.write(version.stdout)
        with (output / (label + "-version.stderr")).open("xb") as stream:
            stream.write(version.stderr)
        drivers = [path for path in sorted((compiler.parent.parent / "lib").glob("librustc_driver-*")) if str(path).encode() in version.stderr]
        if version.returncode != 0 or b"binary: trustc\n" not in version.stdout or b"trust: " not in version.stdout or len(drivers) != 1:
            raise RuntimeError("explicit Trust version and actual loaded local driver must be observed")
        return {"files": {str(path): digest(path) for path in [*input_paths, *drivers]},
                "revision": subprocess.check_output(["/usr/bin/git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
                "source_status": subprocess.check_output(["/usr/bin/git", "status", "--porcelain=v1"], cwd=ROOT, text=True),
                "version": version.stdout.decode("utf-8"), "loaded_drivers": [str(path) for path in drivers],
                "per_compile_driver_observed": False}

    before = None
    runs, errors, controls = {}, [], {}
    try:
        before = snapshot("before")
        save(output / "before.json", before)
        for label, filename, options in CASES:
            try:
                runs[label] = run_case(compiler, output, label, filename, timeout=args.timeout, **options)
            except Exception as error:
                runs[label] = {"harness_error": f"{type(error).__name__}: {error}", "exit_code": None}
                save(output / (label + "-failure.json"), runs[label])
        controls = verdicts(runs, output, existing_digest)
    except (Exception, KeyboardInterrupt) as error:
        errors.append(f"probe interrupted or failed: {type(error).__name__}: {error}")
    if set(runs) != {label for label, _, _ in CASES}:
        errors.append("incomplete live control population")
    if not controls:
        errors.append("no completed live control adjudication")
    errors.extend("failed control: " + label for label, passed in controls.items() if not passed)
    try:
        after = snapshot("after")
    except (Exception, KeyboardInterrupt) as error:
        after = {"snapshot_failed": f"{type(error).__name__}: {error}"}
        errors.append("final input snapshot failed")
    save(output / "after.json", after)
    stable = before is not None and before == after
    if not stable:
        errors.append("probe inputs changed or could not be bound")
    result = {"kind": "lean-island-census-development-controls-not-G1-G2", "status": "failed" if errors else "passed",
              "required_cases": [label for label, _, _ in CASES], "inputs_stable": stable,
              "controls": controls, "runs": runs, "errors": errors,
              "complete_toolchain_closure_bound": False, "closure_requirement": "separate outer harness",
              "whole_program_complete": False, "runtime_body_universe": "unmeasured",
              "denominator_status": "denominator_unverified", "product_proof_authority": False}
    save(output / "result.json", result)
    print(json.dumps({"status": result["status"], "errors": errors, "output": str(output)}, indent=2))
    return 1 if errors else 0


class MockProcessControls(unittest.TestCase):
    """Mock-only lifecycle checks; no actual compiler execution."""

    @staticmethod
    def begin_prefix(command, child, *, direct_lowering=None):
        source = command[1]
        verification = "-Ztrust-verify=on" in command
        report = Path(next(arg.split("=", 1)[1] for arg in command if arg.startswith("-Ztrust-lean-census=")))
        event = {"schema": census.SCHEMA_V3, "event": "begin", "sequence": 0,
                 "previous_record_sha256": None, "input": source,
                 "compiler_version": "mock child only", "target": "mock-target", "edition": "2024",
                 "verification_enabled": verification,
                 "direct_lowering": verification if direct_lowering is None else direct_lowering,
                 "authority": "diagnostic-only", "scope": "actual-root-fragment-and-hir-island-checks",
                 "runtime_body_universe": "unmeasured", "denominator_status": "denominator_unverified"}
        with report.open("xb") as stream:
            stream.write(json.dumps(event).encode() + b"\n")
        return child

    def test_nonzero_exit_is_never_replaced_for_consumer(self):
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp)
            (output / "fixtures").mkdir()
            (output / "fixtures/zero.rs").write_bytes(FIXTURES["zero.rs"])
            child = mock.Mock(pid=12345)
            child.wait.return_value = 17
            with mock.patch.object(subprocess, "Popen", side_effect=lambda command, **_: self.begin_prefix(command, child)):
                result = run_case(Path("/explicit/trustc"), output, "failure", "zero.rs")
            self.assertEqual(result["exit_code"], 17)
            self.assertEqual(result["census"]["process_status"], "failed")
            self.assertEqual(result["census"]["record_status"], "incomplete")
            self.assertEqual([event["event"] for event in events(result)], ["begin"])

    def test_effective_verified_lane_is_bound_independently_of_recorded_header(self):
        for recorded_lowering in (True, False):
            with self.subTest(recorded_lowering=recorded_lowering), tempfile.TemporaryDirectory() as tmp:
                output = Path(tmp)
                (output / "fixtures").mkdir()
                (output / "fixtures/zero.rs").write_bytes(FIXTURES["zero.rs"])
                child = mock.Mock(pid=12345)
                child.wait.return_value = 0
                with mock.patch.object(subprocess, "Popen", side_effect=lambda command, **_: self.begin_prefix(command, child, direct_lowering=recorded_lowering)):
                    result = run_case(Path("/explicit/trustc"), output, "verified", "zero.rs", verification=True)
                self.assertIn("-Ztrust-ir-lower=off", result["command"])
                self.assertFalse(result["requested_lowering"])
                self.assertTrue(result["lowering"])
                if recorded_lowering:
                    self.assertEqual(result["census"]["record_status"], "incomplete")
                    self.assertEqual([event["event"] for event in events(result)], ["begin"])
                else:
                    self.assertEqual(result["census"]["record_status"], "malformed")
                    self.assertEqual(events(result), [])
                    self.assertTrue(any(error["message"] == "wrong invocation lane" for error in result["census"]["errors"]))

    def test_timeout_retains_unknown_natural_exit_and_actual_cleanup_exit(self):
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp)
            (output / "fixtures").mkdir()
            (output / "fixtures/zero.rs").write_bytes(FIXTURES["zero.rs"])
            child = mock.Mock(pid=12345)
            child.wait.side_effect = [subprocess.TimeoutExpired(["trustc"], 1), -15]
            child.poll.return_value = None
            with mock.patch.object(subprocess, "Popen", side_effect=lambda command, **_: self.begin_prefix(command, child)), mock.patch.object(os, "killpg") as kill:
                row = run_case(Path("/explicit/trustc"), output, "timeout", "zero.rs", timeout=1)
            self.assertIsNone(row["exit_code"])
            self.assertEqual(row["reaped_child_exit"], -15)
            self.assertTrue(row["timed_out"])
            self.assertEqual(row["census"]["process_status"], "unmeasured")
            self.assertEqual(row["census"]["record_status"], "incomplete")
            self.assertEqual([event["event"] for event in events(row)], ["begin"])
            kill.assert_called_once_with(12345, signal.SIGTERM)

    def test_launch_error_is_explicit_and_next_case_can_run(self):
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp)
            (output / "fixtures").mkdir()
            (output / "fixtures/zero.rs").write_bytes(FIXTURES["zero.rs"])
            child = mock.Mock(pid=12345)
            child.wait.return_value = 0
            with mock.patch.object(subprocess, "Popen", side_effect=[OSError("mock launch failure"), child]):
                first = run_case(Path("/explicit/trustc"), output, "first", "zero.rs")
                second = run_case(Path("/explicit/trustc"), output, "second", "zero.rs")
            self.assertIn("mock launch failure", first["launch_error"])
            self.assertEqual(first["census"]["process_status"], "unmeasured")
            self.assertEqual(second["exit_code"], 0)
            self.assertEqual(second["census"]["record_status"], "missing")

    def test_serialization_failure_never_leaves_partial_destination(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "report.json"
            with self.assertRaises(ValueError):
                save(path, {"invalid": float("nan")})
            self.assertFalse(path.exists())
            save(path, {"diagnostic": "\ud800"})
            self.assertEqual(json.loads(path.read_text()), {"diagnostic": "\ud800"})

    def test_interruption_stops_and_reaps_the_owned_child(self):
        with tempfile.TemporaryDirectory() as tmp:
            child = mock.Mock(pid=12345)
            child.wait.side_effect = [KeyboardInterrupt(), -15]
            child.poll.return_value = None
            with mock.patch.object(subprocess, "Popen", return_value=child), mock.patch.object(os, "killpg") as kill:
                with self.assertRaises(KeyboardInterrupt):
                    execute(["/explicit/trustc"], Path(tmp), Path(tmp), 1)
            kill.assert_called_once_with(12345, signal.SIGTERM)
            self.assertEqual(child.wait.call_count, 2)

    def test_missing_case_or_artifact_population_cannot_pass(self):
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp)
            (output / "existing-census.jsonl").write_bytes(b"sentinel")
            controls = verdicts({"ordered-baseline": {"exit_code": 0, "outputs": {}}},
                                output, digest(output / "existing-census.jsonl"))
            self.assertFalse(controls["zero:finished"])
            self.assertFalse(controls["ordered-baseline:success-and-artifacts"])
            self.assertFalse(controls["ordered:observer-parity"])


if __name__ == "__main__":
    raise SystemExit(main())
