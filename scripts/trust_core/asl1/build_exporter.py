#!/usr/bin/env python3
"""Build the real pinned ASLRef extractor in fresh, explicit external paths.

Uses only the pinned redistributable asllib sources. Does not fetch an Arm
machine package, install tools, reuse executable caches or supply proof grades.
Host OCaml/Dune/Menhir/Zarith are explicit caller-selected TCB inputs.
"""
from concurrent.futures import ThreadPoolExecutor
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
PIN = "ffad2692c4580538e8db7bf6631aa886edfc7423"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-dir", type=Path, required=True)
    parser.add_argument("--build-dir", type=Path, required=True)
    parser.add_argument("--tool-bin", type=Path, required=True)
    parser.add_argument("--library-dir", type=Path, required=True)
    args = parser.parse_args()
    source = args.source_dir.expanduser().resolve()
    build = args.build_dir.expanduser().resolve()
    repo = ROOT
    for path in (source, build):
        if path == repo or repo in path.parents or path.exists():
            raise SystemExit("source/build paths must be fresh external directories")
    if source == build or source in build.parents or build in source.parents:
        raise SystemExit("source and build directories must be disjoint")
    manifest = json.loads((HERE / "ASLREF-PIN.json").read_text())
    require(manifest["repository"] == "herd/herdtools7" and manifest["commit"] == PIN,
            "unexpected ASLRef repository or immutable commit")
    source.mkdir(parents=True)
    build.mkdir(parents=True)
    records = manifest["files"]
    require(len(records) == 64 and len({row["path"] for row in records}) == 64,
            "incomplete or duplicate ASLRef source population")

    def fetch(row):
        relative = PurePosixPath(row["path"])
        require(not relative.is_absolute() and ".." not in relative.parts,
                "ASLRef source path escapes the selected directory")
        data = subprocess.check_output([
            "agh", "cat", f"herd/herdtools7@{PIN}:asllib/{relative}",
            "--max-bytes", "1048576",
        ])
        blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        require(len(data) == row["bytes"] and blob == row["git_blob"]
                and hashlib.sha256(data).hexdigest() == row["sha256"],
                "pinned ASLRef source size/Git blob/SHA-256 mismatch: " + str(relative))
        path = source.joinpath(*relative.parts)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)

    with ThreadPoolExecutor(max_workers=6) as pool:
        list(pool.map(fetch, records))
    extension = source / "bridge"
    extension.mkdir()
    (extension / "exporter.ml").write_bytes((HERE / "aslref_export.ml").read_bytes())
    (extension / "dune").write_text(
        "(executable (name exporter) (libraries asllib zarith unix))\n"
    )
    inputs = {str(source / row["path"]): row["sha256"] for row in records}
    inputs[str(extension / "exporter.ml")] = digest(extension / "exporter.ml")
    inputs[str(extension / "dune")] = digest(extension / "dune")
    environment = dict(os.environ)
    for key in list(environment):
        if key.startswith("OCAML") or key in ("CAML_LD_LIBRARY_PATH", "DUNE_BUILD_DIR"):
            environment.pop(key)
    tools = args.tool_bin.expanduser().resolve()
    environment["PATH"] = str(tools) + os.pathsep + environment.get("PATH", "")
    environment["OCAMLPATH"] = str(args.library_dir.expanduser().resolve())
    versions = {}
    for tool, flag in (("ocamlc", "-version"), ("dune", "--version"), ("menhir", "--version")):
        executable = tools / tool
        versions[tool] = {
            "path": str(executable), "sha256": digest(executable),
            "version": subprocess.check_output([str(executable), flag], env=environment).decode().strip(),
        }
    command = [str(ROOT / "scripts/build-slot"), "--cpus", "2", "--mem-gb", "2", "--",
               str(tools / "dune"), "build", "--root", str(source), "--build-dir", str(build),
               "--profile", "release", "-j2", "bridge/exporter.exe"]
    with (build / "build.log").open("wb") as log:
        run = subprocess.run(command, cwd=source, env=environment,
                             stdout=log, stderr=subprocess.STDOUT)
    changed = [path for path, wanted in inputs.items() if digest(Path(path)) != wanted]
    for row in versions.values():
        if digest(Path(row["path"])) != row["sha256"]:
            changed.append(row["path"])
    executable = build / "default/bridge/exporter.exe"
    good = run.returncode == 0 and not changed and executable.is_file()
    report = {
        "status": "PINNED_ASLREF_SOURCE_BUILD_PASS" if good else "REFUSED",
        "aslref_commit": PIN, "inputs": inputs, "host_tools": versions,
        "argv": command, "exit": run.returncode, "changed_inputs": changed,
        "executable": str(executable),
        "executable_sha256": digest(executable) if executable.is_file() else None,
        "scope": "Actual unverified source producer TCB; no ASL/ISA/refinement/grade claim",
    }
    (build / "RESULT.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "inputs"}, indent=2))
    raise SystemExit(0 if good else 1)


if __name__ == "__main__":
    main()
