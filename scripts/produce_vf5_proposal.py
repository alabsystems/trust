#!/usr/bin/env python3
"""Prepare UNTRUSTED VF5 math inputs for one exact current compiler artifact.

Run under the canonical build-slot using a declared whole Lean installation
and changed-source prepare_vf5_inputs tool. No proof authority is produced:
the ordinary compiler must replay the original RowProved judgment itself.
This script never edits Clean, its fixtures, a provider, an old output or pins.

The required --prepare-tool is a separately built prepare_vf5_inputs image.
Publishing this driver does not establish that the helper, production proof
base or ordinary compiler integration has been built or qualified.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import stat
import subprocess
from types import SimpleNamespace

ROOT = Path(__file__).resolve().parents[1]
FAMILY = "crates/clean-olean/tests/fixtures/lean/v4.30.0-rc2/vf5_f1"
SEMR = "crates/clean-olean/tests/fixtures/lean/v4.30.0-rc2/semr"
WORLD = "v4.30.0-rc2"
MAX_INPUT_BYTES = 8 * 1024 * 1024
MAX_LOG_BYTES = 64 * 1024 * 1024


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def read_regular(path: Path, limit: int) -> bytes:
    """Bound an actual regular descriptor, including replacement by a FIFO."""
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_NONBLOCK", 0)
    descriptor = os.open(path, flags)
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode) or before.st_size > limit:
            raise ValueError(f"nonregular or oversized input: {path}")
        with os.fdopen(descriptor, "rb", closefd=False) as stream:
            data = stream.read(limit + 1)
        after = os.fstat(descriptor)
        observed = lambda value: (value.st_dev, value.st_ino, value.st_size, value.st_mtime_ns, value.st_ctime_ns)
        if len(data) > limit or observed(before) != observed(after):
            raise ValueError(f"oversized or changed input: {path}")
        return data
    finally:
        os.close(descriptor)


def write_new(path: Path, data: bytes) -> None:
    with path.open("xb") as stream:
        stream.write(data)


def write_json(path: Path, value: object) -> None:
    write_new(path, (json.dumps(value, sort_keys=True, indent=2) + "\n").encode())


def order_lines(data: bytes) -> list[str]:
    return [line.strip() for line in data.decode().splitlines()
            if line.strip() and not line.lstrip().startswith("#")]


def build_sources(read) -> list[tuple[str, str]]:
    """Original handwritten order through Mutants (search's data-only import).

    The production base packager independently selects ONLY VF5Check's actual
    typed dependency graph; generated historical rows are never compiled here.
    """
    result = []
    for step in order_lines(read(f"{FAMILY}/ORDER")):
        if step == "theory chk_lia":
            for stem in order_lines(read("theories/chk_lia/ORDER")):
                if not stem.isidentifier():
                    raise ValueError("unsupported theory build directive")
                result.append((stem, f"theories/chk_lia/{stem}.lean"))
        elif step == "from semr SemR":
            result.append(("SemR", f"{SEMR}/SemR.lean"))
        elif step.isidentifier():
            result.append((step, f"{FAMILY}/{step}.lean"))
            if step == "VF5Mutants":
                return result
        else:
            raise ValueError(f"unsupported family build directive: {step}")
    raise ValueError("original handwritten VF5Mutants endpoint absent")


class RecordedCommands:
    def __init__(self, output: Path):
        self.output = output
        self.records = []

    def run(self, argv, *, cwd=None, env=None, capture_output=True, text=True):
        if not capture_output or not text:
            raise ValueError("unexpected producer subprocess contract")
        index = len(self.records)
        stdout = self.output / f"command-{index:04d}.stdout"
        stderr = self.output / f"command-{index:04d}.stderr"
        input_record = None
        if argv and str(argv[-1]).endswith(".lean"):
            source = Path(argv[-1])
            if not source.is_absolute():
                source = Path(cwd) / source
            data = read_regular(source, MAX_INPUT_BYTES)
            saved = self.output / f"command-{index:04d}.input.lean"
            write_new(saved, data)
            input_record = {"path": str(source), "captured": str(saved), "sha256": sha(data)}
        record = {"index": index, "argv": [str(arg) for arg in argv],
                  "cwd": str(cwd), "returncode": None,
                  "stdout": str(stdout), "stderr": str(stderr), "source": input_record}
        try:
            with stdout.open("xb") as out, stderr.open("xb") as err:
                result = subprocess.run(argv, cwd=cwd, env=env, stdout=out, stderr=err, check=False)
            record["returncode"] = result.returncode
        except OSError as error:
            record["spawn_error"] = {"type": type(error).__name__, "detail": str(error)}
            raise
        finally:
            self.records.append(record)
            write_json(self.output / f"command-{index:04d}.json", record)
        return subprocess.CompletedProcess(argv, result.returncode,
            read_regular(stdout, MAX_LOG_BYTES).decode(), read_regular(stderr, MAX_LOG_BYTES).decode())


def selected_clean_revision() -> str:
    row = subprocess.check_output(["git", "-C", str(ROOT), "ls-tree", "HEAD", "first-party/clean"],
        text=True, env=dict(os.environ, GIT_NO_REPLACE_OBJECTS="1", GIT_NO_LAZY_FETCH="1", GIT_OPTIONAL_LOCKS="0"))
    fields = row.split()
    if len(fields) != 4 or fields[:2] != ["160000", "commit"]:
        raise ValueError("selected Clean gitlink absent")
    return fields[2]


def read_source_blob(clean_source: Path, revision: str, path: str) -> bytes:
    """Read the fixed Git object itself; a current checkout is never a fallback."""
    environment = dict(os.environ, GIT_NO_REPLACE_OBJECTS="1", GIT_NO_LAZY_FETCH="1", GIT_OPTIONAL_LOCKS="0")
    data = subprocess.check_output(
        ["git", "-C", str(clean_source), "cat-file", "blob", f"{revision}:{path}"], env=environment,
    )
    if len(data) > MAX_INPUT_BYTES:
        raise ValueError(f"oversized source blob: {path}")
    return data


def fixed_source_identity(calls, tool: Path, *, cwd: Path, env) -> dict:
    """Read the fixed consumer's source DATA, never infer it from a newer gitlink."""
    response = calls.run([str(tool), "source-identity"], cwd=cwd, env=env)
    if response.returncode:
        raise ValueError("fixed consumer source identity query failed")

    def unique(items):
        result = {}
        for key, value in items:
            if key in result:
                raise ValueError(f"duplicate fixed source identity field: {key}")
            result[key] = value
        return result

    def invalid_constant(value):
        raise ValueError(f"invalid fixed source identity constant: {value}")

    identity = json.loads(response.stdout, object_pairs_hook=unique, parse_constant=invalid_constant)
    if (type(identity) is not dict
            or set(identity) != {"schema", "kind", "clean_revision", "lean_world", "production_admission"}
            or type(identity["schema"]) is not int or identity["schema"] != 1
            or identity["kind"] != "vf5-fixed-source-identity-v1"
            or identity["lean_world"] != WORLD
            or identity["production_admission"] is not False):
        raise ValueError("unsupported fixed consumer source identity")
    revision = identity["clean_revision"]
    if (type(revision) is not str or len(revision) != 40
            or any(character not in "0123456789abcdef" for character in revision)):
        raise ValueError("invalid fixed consumer Clean source revision")
    return identity


def produce(args: argparse.Namespace) -> None:
    from recreate_bootstrap import CleanLeanSelection

    output = args.output.absolute()
    output.mkdir(mode=0o700)  # no reuse, deletion or replacement of old evidence
    work = output / "work"
    work.mkdir()
    calls = RecordedCommands(output)
    root_revision = selected_clean_revision()
    revision = None
    selection = CleanLeanSelection(args.lean_manifest, args.lean_lib, args.lean_manifest_sha256)
    sources = {}
    result = {"kind": "vf5-untrusted-preparation-v1", "production_admission": False,
              "root_clean_revision": root_revision, "completed": False}

    def read(path: str) -> bytes:
        data = read_source_blob(args.clean_source, revision, path)
        sources[path] = sha(data)
        return data

    try:
        selected_env = selection.environment(ROOT)
        lean_root = args.lean_lib.resolve().parent.parent
        lean = lean_root / "bin/lean"
        environment = {**os.environ, **selected_env, "LEAN_PATH": str(work)}
        identity = fixed_source_identity(calls, args.prepare_tool, cwd=work, env=environment)
        revision = identity["clean_revision"]
        result["clean_revision"] = revision
        version = calls.run([str(lean), "--version"], cwd=work, env=environment)
        if version.returncode or "4.30.0-rc2" not in version.stdout:
            raise ValueError("declared whole Lean has wrong version")
        if read("lean-toolchain").decode().strip() != "leanprover/lean4:v4.30.0-rc2":
            raise ValueError("selected source requires a different Lean world")
        artifact = read_regular(args.artifact, MAX_INPUT_BYTES)
        write_new(output / "artifact.tirb", artifact)
        result["artifact_sha256"] = sha(artifact)
        for stem, path in build_sources(read):
            write_new(work / f"{stem}.lean", read(path))
            built = calls.run([str(lean), "--root", ".", "-o", f"{stem}.olean", f"{stem}.lean"], cwd=work, env=environment)
            if built.returncode:
                raise ValueError(f"Lean producer compilation failed: {stem}, exit {built.returncode}")
        search_path = output / "untrusted_search.py"
        write_new(search_path, read("scripts/vf5_f1_producer.py"))
        spec = importlib.util.spec_from_file_location("trust_vf5_untrusted_search", search_path)
        if spec is None or spec.loader is None:
            raise ValueError("cannot load selected untrusted producer source")
        search = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(search)
        # Only declared tool/output routing changes. Original search/checker
        # source is recorded verbatim; it supplies no proof authority.
        search.BUILD = work
        search.lean_bin = lambda: lean
        search.subprocess = SimpleNamespace(run=calls.run)
        annotation, _functions, certificates = search.search(artifact)
        if certificates is None:
            raise ValueError("untrusted search found no complete proposal")
        names, roots, entries = search.meta(artifact, annotation)
        if not names or entries is not True:
            raise ValueError("untrusted proposal lacks functions or entry-shape checks")
        proposal = ("import VF5Check\nopen SemR VF5\nnamespace TrustVF5Proposal\n"
                    "def annotation := " + search.lean_annot(annotation) + "\n"
                    "def certificates : List (Nat × List (List ChkLIA.Step)) := "
                    + search.lean_certs(certificates) + "\nend TrustVF5Proposal\n")
        write_new(work / "TrustVF5Proposal.lean", proposal.encode())
        built = calls.run([str(lean), "--root", ".", "-o", "TrustVF5Proposal.olean", "TrustVF5Proposal.lean"], cwd=work, env=environment)
        if built.returncode:
            raise ValueError(f"Lean proposal compilation failed: exit {built.returncode}")
        source_book = output / "SOURCE-INPUTS.json"
        write_json(source_book, {"clean_revision": revision, "lean_world": WORLD, "source_files": sources})
        for command in [
            [str(args.prepare_tool), "package", str(work), str(args.lean_lib), str(source_book), str(output / "base")],
            [str(args.prepare_tool), "proposal", str(work), str(work), str(args.lean_lib), str(output / "artifact.tirb"), str(output / "proposal.json")],
        ]:
            child = calls.run(command, cwd=work, env=environment)
            if child.returncode:
                raise ValueError(f"untrusted input extraction failed: exit {child.returncode}")
        result.update(completed=True, functions=[{"fid": fid, "symbol_hex": name.hex()} for fid, name in sorted(names.items())], roots=roots)
    except (Exception, SystemExit) as error:
        result["completed"] = False
        result["error"] = {"type": type(error).__name__, "detail": str(error)}
        raise
    finally:
        # Independent after-validation also runs on a producer failure; neither
        # this source/provider check nor a child exit is a theorem verdict.
        try:
            selection.environment(ROOT)
            result["lean_after_validated"] = True
        except Exception as error:
            result["lean_after_validated"] = False
            result["lean_after_error"] = str(error)
            result["completed"] = False
        result["source_files"] = sources
        result["commands"] = calls.records
        write_json(output / "RESULT.json", result)
    if not result["completed"]:
        raise ValueError("preparation did not complete with unchanged declared Lean inputs")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    for option in ("clean-source", "lean-lib", "lean-manifest", "artifact", "prepare-tool", "output"):
        parser.add_argument("--" + option, type=Path, required=True)
    parser.add_argument("--lean-manifest-sha256", required=True)
    args = parser.parse_args()
    try:
        produce(args)
    except (Exception, SystemExit) as error:
        print(f"VF5 untrusted preparation failed: {error}", file=__import__("sys").stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
