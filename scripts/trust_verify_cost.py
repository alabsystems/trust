#!/usr/bin/env python3
"""Measure PKG-C5d's fixed 500-function workload with a prebuilt Trust compiler.

Run outside an existing build-slot invocation. This command enters the canonical
exclusive measurement window itself; admission wait is excluded from compiler
wall time. The result checks reported compatibility-MIR verification outcomes,
not certificates or the target direct-IR pipeline. It grants no proof authority.
Raw source, compiler output, native time output and identities are retained even
when the compiler fails. This diagnostic is not an ordinary source-push gate.
"""

from __future__ import annotations

import argparse
from collections import Counter
from decimal import Context, Decimal, InvalidOperation, localcontext
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import time
import uuid

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts" / "lib"))
from landing_targo import resource_fds
from trust_program_wire import PREFIX, WireError, inspect_wire

COUNT = 500
CRATE = "trust_verify_cost"
MAX_WALL_SECONDS = Decimal("5")
MAX_RSS_BYTES = 400_000_000  # MB, not MiB.
MAX_STREAM_BYTES = 64 * 1024 * 1024
FUNCTIONS = tuple(f"{CRATE}::cost_{index:04}" for index in range(COUNT))
LINUX_TIME = "TRUST_VERIFY_COST_TIME_V1"
FUNCTION_SOURCE_DOMAIN = b"trust-function-source/v1\0"


class CostError(ValueError):
    pass


def function_items() -> dict[str, str]:
    # Each addition has a real overflow obligation on an unconstrained input,
    # discharged by its explicit branch guard. No precondition excludes inputs.
    return {name: f"pub fn cost_{index:04}(x: u64) -> u64 {{ if x < 100 {{ x + 1 }} else {{ x }} }}"
            for index, name in enumerate(FUNCTIONS)}


def function_source_hashes() -> dict[str, str]:
    # Match obligation_identity.rs::function_source_digest on this deliberately
    # fixed ASCII workload, not on arbitrary Rust. It has identifiers, decimal
    # integers and single punctuation characters, and no comments or literals.
    # The maintained producer joins these tokens with one space after this
    # domain separator. The actual Rust algorithm/emitter are bookended inputs.
    return {name: hashlib.sha256(FUNCTION_SOURCE_DOMAIN + " ".join(
        re.findall(r"[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[^\s]", text)).encode("ascii")).hexdigest()
            for name, text in function_items().items()}


def workload() -> bytes:
    return ("#![no_std]\n\n" + "\n".join(function_items().values()) + "\n").encode()


def file_record(path: Path) -> dict:
    with path.open("rb") as stream:
        before = os.fstat(stream.fileno())
        if not stat.S_ISREG(before.st_mode):
            raise CostError(f"not a regular file: {path}")
        hasher = hashlib.sha256()
        while chunk := stream.read(1024 * 1024):
            hasher.update(chunk)
        digest = hasher.hexdigest()
        after = os.fstat(stream.fileno())
    identity = lambda row: (row.st_dev, row.st_ino, row.st_size, row.st_mtime_ns, row.st_ctime_ns)
    if identity(before) != identity(after) or identity(after) != identity(path.stat()):
        raise CostError(f"file changed while being identified: {path}")
    return {"path": str(path), "bytes": after.st_size, "sha256": digest,
            "device": after.st_dev, "inode": after.st_ino,
            "mtime_ns": after.st_mtime_ns, "ctime_ns": after.st_ctime_ns}


def strict_transport(stderr: str) -> list[dict]:
    def pairs(items):
        result = {}
        for key, value in items:
            if key in result:
                raise CostError(f"duplicate JSON key: {key}")
            result[key] = value
        return result

    def constant(value):
        raise CostError(f"non-JSON numeric constant: {value}")

    def floating(value):
        number = float(value)
        if not math.isfinite(number):
            raise CostError("nonfinite JSON number")
        return number

    rows = []
    for line in stderr.splitlines():
        if not line.startswith(PREFIX):
            continue  # The maintained accounting reader rejects embedded prefixes.
        try:
            row = json.loads(line[len(PREFIX):], object_pairs_hook=pairs,
                             parse_constant=constant, parse_float=floating)
            pending = [(row, 0)]
            while pending:
                value, depth = pending.pop()
                if depth > 128:
                    raise CostError("transport JSON exceeds depth 128")
                if isinstance(value, dict):
                    pending.extend((item, depth + 1) for item in value.values())
                elif isinstance(value, list):
                    pending.extend((item, depth + 1) for item in value)
        except (ValueError, TypeError, RecursionError) as error:
            raise CostError(f"invalid verification transport: {error}") from error
        rows.append(row)
    return rows


def judge_wire(stderr: str, stdout: str) -> dict:
    rows = strict_transport(stderr)
    try:
        accounting = inspect_wire(stderr, stdout, crate_name=CRATE, session="",
                                  required_functions=FUNCTIONS)
    except WireError as error:
        raise CostError(str(error)) from error
    if accounting["functions"] != list(FUNCTIONS):
        raise CostError("the complete function population must be exactly the fixed 500")
    if accounting["nonclean"]:
        raise CostError("a function has a failed, unknown, skipped or runtime-checked obligation")
    expected_sources = function_source_hashes()
    kinds, grades, keys = Counter(), Counter(), []
    for row in rows:
        if row.get("type") != "function_result":
            continue
        results = row["results"]
        if not results or sum(item["kind"] == "arithmetic_overflow_add" for item in results) != 1:
            raise CostError(f"{row['function']}: exactly one real addition-overflow row is required")
        if type(row.get("cached")) is not int or row["cached"] != 0:
            raise CostError(f"{row['function']}: cached or unreported work cannot meet the fresh workload")
        checks = row.get("runtime_checks")
        if not isinstance(checks, dict) or checks.get("overflow_checks") is not True:
            raise CostError(f"{row['function']}: compiler did not report enabled overflow checks")
        if not isinstance(row.get("modeled_facts", []), list) or row.get("modeled_facts", []):
            raise CostError(f"{row['function']}: modeled premises change the benchmark workload")
        if row.get("transport_budget") is not None:
            raise CostError(f"{row['function']}: transport withholding changes the complete measured population")
        source = row.get("source_sha256")
        identities = row.get("stable_ids")
        if source != expected_sources[row["function"]]:
            raise CostError(f"{row['function']}: body source identity differs from the fixed generated item")
        if (not isinstance(identities, list) or len(identities) != len(results)
                or not all(isinstance(value, str) and re.fullmatch(r"[0-9a-f]{16}", value)
                           for value in identities)
                or len(set(identities)) != len(identities)):
            raise CostError(f"{row['function']}: incomplete or duplicate obligation identities")
        # The transport contains LOCAL ids. Its canonical full key is derived
        # from the exact owner, never accepted from a foreign/full-key string.
        keys.extend(row["function"] + "#" + identity for identity in identities)
        kinds.update(item["kind"] for item in results)
        # Retain labels without upgrading them. This harness checks no proof.
        grades.update(str(item.get("proof_grade", "unreported")) for item in results)
    return {"functions": accounting["functions"], "outcomes": accounting["counts"],
            "body_source_sha256": expected_sources, "obligation_keys": keys,
            "obligation_kinds": dict(kinds), "reported_proof_grades": dict(grades),
            "identity_scope": "body source digests independently recomputed; local ids are canonical "
                              "and paired with exact owners, not independently re-minted proof authority"}


def native_time(stderr: str, system: str) -> dict:
    lines = stderr.splitlines()
    if system == "Darwin":
        wall_lines = [line for line in lines if line.startswith("real ")]
        rss_lines = [line for line in lines if "maximum resident set size" in line]
        if (any(not re.fullmatch(r"real [0-9]+(?:\.[0-9]+)?", line) for line in wall_lines)
                or any(not re.fullmatch(r"[ \t]*[0-9]+[ \t]+maximum resident set size[ \t]*", line)
                       for line in rss_lines)):
            raise CostError("malformed native time/resource candidate")
        wall = [line.split()[1] for line in wall_lines]
        rss = [line.split()[0] for line in rss_lines]
        unit = 1
    elif system == "Linux":
        metric_lines = [line for line in lines if LINUX_TIME in line]
        if any(not re.fullmatch(LINUX_TIME + r" [0-9]+(?:\.[0-9]+)? [0-9]+", line)
               for line in metric_lines):
            raise CostError("malformed native time/resource candidate")
        metrics = [line.split()[1:] for line in metric_lines]
        wall, rss = ([row[0] for row in metrics], [row[1] for row in metrics])
        unit = 1024
    else:
        raise CostError("native resource measurement supports Darwin and Linux only")
    if len(wall) != 1 or len(rss) != 1:
        raise CostError("missing, malformed or duplicate native time/resource record")
    if len(wall[0]) > 64 or len(rss[0]) > 20:
        raise CostError("native time/resource number exceeds its representation bound")
    seconds = Decimal(wall[0])
    # Native time prints rounded decimal seconds. Use a conservative upper bound
    # rather than claiming 5.00 proves the actual duration was at most five.
    with localcontext(Context(prec=len(seconds.as_tuple().digits) + 2)):
        quantum = Decimal(1).scaleb(seconds.as_tuple().exponent)
        upper = seconds + quantum
    peak = int(rss[0]) * unit
    if not seconds.is_finite() or seconds < 0 or peak <= 0:
        raise CostError("invalid native duration or peak RSS")
    return {"reported_wall_seconds": str(seconds),
            "wall_upper_bound_seconds": str(upper),
            "peak_rss_bytes": peak,
            "rss_scope": "native time's maximum resident set size of the compiler command; "
                         "not the sum of concurrent process RSS or external-service memory",
            "time_scope": "compiler command, including verification and metadata emission; "
                          "excludes admission wait, version probe and Python wire grading"}


def judge_run(exit_code: int, stderr: str, stdout: str, system: str) -> dict:
    if exit_code != 0:
        raise CostError(f"compiler/admission command exited {exit_code}; favorable rows cannot repair it")
    wire = judge_wire(stderr, stdout)
    measured = native_time(stderr, system)
    met = (Decimal(measured["wall_upper_bound_seconds"]) <= MAX_WALL_SECONDS
           and measured["peak_rss_bytes"] <= MAX_RSS_BYTES)
    return {"wire": wire, "measurement": measured, "cost_bound_met": met}


def run_recorded(command: list[str], directory: Path, env: dict[str, str], fds: tuple[int, ...]) -> dict:
    started = time.monotonic_ns()
    with (directory / "stdout.raw").open("xb") as stdout, (directory / "stderr.raw").open("xb") as stderr:
        child = subprocess.run(command, stdout=stdout, stderr=stderr, env=env, pass_fds=fds)
    return {"argv": command, "exit_code": child.returncode,
            "admission_and_command_wall_ns": time.monotonic_ns() - started}


def read_stream(path: Path) -> str:
    if path.stat().st_size > MAX_STREAM_BYTES:
        raise CostError(f"retained stream exceeds {MAX_STREAM_BYTES}-byte reader bound: {path.name}")
    return path.read_text(encoding="utf-8", errors="strict")


def host_matches(host: str, system: str, machine: str) -> bool:
    architecture = {"arm64": "aarch64", "aarch64": "aarch64", "x86_64": "x86_64"}.get(machine)
    return bool(architecture and host.startswith(architecture + "-") and (
        (system == "Darwin" and host.endswith("-apple-darwin"))
        or (system == "Linux" and "-linux-" in host)))


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--trustc", default=os.environ.get("TRUSTC", "trustc"))
    parser.add_argument("--out-dir", type=Path,
                        help="new evidence directory; default is a private persistent cache directory")
    args = parser.parse_args(argv)
    directory = None
    result = {"schema": "trust.verification-cost/v1", "state": "REFUSED",
              "cost_bound_met": False,
              "workload_functions": COUNT, "route": "compatibility-MIR verification; LLVM default",
              "proof_authority": False, "source_refinement_proven": False,
              "direct_ir_pipeline_complete": False,
              "limits": {"wall_seconds": str(MAX_WALL_SECONDS), "peak_rss_bytes": MAX_RSS_BYTES},
              "host": {"node": platform.node(), "system": platform.system(),
                       "machine": platform.machine()}}
    try:
        if os.environ.get("BUILD_SLOT_HELD") is not None:
            raise CostError("run outside build-slot; this harness acquires its own exclusive window")
        for key in ("TRUST_NO_VERIFY", "TRUST_SKIP_VERIFY", "RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS"):
            if os.environ.get(key):
                raise CostError(f"inherited {key} competes with the measured verification request")
        compiler = shutil.which(args.trustc)
        if compiler is None:
            raise CostError("no prebuilt Trust compiler found; build it under ordinary admission first")
        compiler = Path(compiler).resolve(strict=True)
        with compiler.open("rb") as binary:
            if binary.read(4) not in (b"\x7fELF", b"\xcf\xfa\xed\xfe", b"\xfe\xed\xfa\xcf",
                                      b"\xce\xfa\xed\xfe", b"\xfe\xed\xfa\xce",
                                      b"\xca\xfe\xba\xbe", b"\xbe\xba\xfe\xca"):
                raise CostError("name the physical prebuilt compiler with --trustc, not a launcher script")
        if args.out_dir is None:
            parent = Path.home() / ".cache" / "trust" / "verification-cost"
            parent.mkdir(mode=0o700, parents=True, exist_ok=True)
            directory = Path(tempfile.mkdtemp(prefix="run-", dir=parent))
        else:
            candidate = args.out_dir.resolve()
            candidate.mkdir(mode=0o700, parents=False, exist_ok=False)
            directory = candidate
        result["output_directory"] = str(directory)
        env = dict(os.environ, LC_ALL="C")
        fds = resource_fds(env)
        before = file_record(compiler)
        probe = subprocess.run([str(compiler), "-vV"], capture_output=True, env=env, pass_fds=fds)
        (directory / "version.stdout.raw").write_bytes(probe.stdout)
        (directory / "version.stderr.raw").write_bytes(probe.stderr)
        if probe.returncode:
            raise CostError("prebuilt compiler version probe failed")
        hosts = re.findall(r"^host: (\S+)$", probe.stdout.decode("utf-8"), re.M)
        if len(hosts) != 1 or not host_matches(hosts[0], platform.system(), platform.machine()):
            raise CostError("compiler host does not match this native measurement machine")
        result["compiler_host"] = hosts[0]
        result["compiler_provenance"] = "selected image hash and its self-reported -vV; not authenticated source custody"
        revision = subprocess.run(["git", "rev-parse", "HEAD", "HEAD^{tree}"], cwd=ROOT,
                                  capture_output=True, text=True)
        if revision.returncode:
            raise CostError("cannot bind the harness source revision")
        revision_rows = revision.stdout.splitlines()
        if len(revision_rows) != 2 or any(not re.fullmatch(r"[0-9a-f]{40,64}", row) for row in revision_rows):
            raise CostError("invalid harness source revision")
        result["harness_source"] = {"commit": revision_rows[0], "tree": revision_rows[1],
                                    "scope": "repository metadata; exact selected input files are hashed separately",
                                    "revision_alone_does_not_exclude_worktree_edits": True}
        source = directory / "workload.rs"
        source.write_bytes(workload())
        metadata = directory / "workload.rmeta"
        command = [str(compiler), str(source), "--crate-name", CRATE, "--crate-type=lib",
                   "--edition=2024", "--emit=metadata", "-o", str(metadata),
                   "-Copt-level=0", "-Coverflow-checks=on", "-Cmetadata=" + uuid.uuid4().hex,
                   "-Ztrust-verify=on", "-Ztrust-policy=certify", "-Ztrust-verify-output=json"]
        timer = ["/usr/bin/time", "-p", "-l"] if platform.system() == "Darwin" else [
            "/usr/bin/time", "-f", LINUX_TIME + " %e %M"]
        if platform.system() not in ("Darwin", "Linux"):
            raise CostError("native resource measurement supports Darwin and Linux only")
        gate = ROOT / "scripts" / "build-slot"
        result["input_files"] = [file_record(source), file_record(Path(__file__).resolve()),
                                 file_record(ROOT / "scripts/lib/trust_program_wire.py"),
                                 file_record(ROOT / "scripts/lib/landing_targo.py"), file_record(gate),
                                 file_record(Path("/usr/bin/time")),
                                 file_record(ROOT / "crates/trust-types/src/obligation_identity.rs"),
                                 file_record(ROOT / "crates/trust-types/src/result.rs"),
                                 file_record(ROOT / "compiler/rustc_mir_transform/src/trust_verify.rs")]
        result["compiler_before"] = before
        result["compiler_argv"] = command
        result["run"] = run_recorded([str(gate), "--exclusive", "--wait-timeout", "1800", "--",
                                      *timer, *command], directory, env, fds)
        result["compiler_after"] = file_record(compiler)
        if result["compiler_after"] != before:
            raise CostError("compiler image identity changed during the measurement")
        result["inputs_after"] = [file_record(Path(row["path"])) for row in result["input_files"]]
        if result["inputs_after"] != result["input_files"]:
            raise CostError("benchmark source or selected reader/gate/time input changed during execution")
        result.update(judge_run(result["run"]["exit_code"], read_stream(directory / "stderr.raw"),
                                read_stream(directory / "stdout.raw"), platform.system()))
        result["metadata_artifact"] = file_record(metadata)
        if result["metadata_artifact"]["bytes"] == 0:
            raise CostError("compiler produced empty metadata")
        result["state"] = "ENGINEERING_COST_BOUND_MET" if result["cost_bound_met"] else "COST_BOUND_EXCEEDED"
        code = 0 if result["cost_bound_met"] else 1
    except (CostError, OSError, UnicodeError, RuntimeError, InvalidOperation) as error:
        result["reason"] = str(error)
        result["state"] = "REFUSED"
        result["cost_bound_met"] = False
        code = 2
    if directory is not None:
        # Every attempt gets a new directory; never overwrite earlier evidence.
        result["retained_raw_files"] = []
        for name in ("stdout.raw", "stderr.raw", "version.stdout.raw", "version.stderr.raw"):
            path = directory / name
            if path.exists():
                try:
                    result["retained_raw_files"].append(file_record(path))
                except (CostError, OSError) as error:
                    result["raw_identity_error"] = str(error)
                    result["state"] = "REFUSED"
                    result["cost_bound_met"] = False
                    code = 2
        (directory / "RESULT.json").write_text(json.dumps(result, indent=2, allow_nan=False) + "\n")
        print(str(directory / "RESULT.json"))
    print(result["state"] + (": " + result["reason"] if "reason" in result else ""))
    return code


if __name__ == "__main__":
    raise SystemExit(main())
