#!/usr/bin/env python3
"""Authenticate inputs for an explicit first native Linux Trust root producer.

This read-only preflight is not a native build or root admission. It does not
download, install, wrap or relabel a compiler. Complete GENESIS-ROOT evidence
must subsequently pass seed_host_ledger's separate initialization admission.
"""

from __future__ import annotations

import os as _floor_os
import shutil as _floor_shutil
import sys as _floor_sys

# Trust: python floor. This preflight reads TOML with tomllib (3.11+).
# `python3 initialize_linux_root_seed.py` on a machine whose python3 is older
# (3.9 on macOS CommandLineTools) re-execs here under the newest >=3.11 on PATH
# (scripts/tests/python_floor_test.py holds every such script to this).
if __name__ == "__main__" and _floor_sys.version_info < (3, 11):
    for _floor_candidate in ("python3.14", "python3.13", "python3.12", "python3.11"):
        _floor_path = _floor_shutil.which(_floor_candidate)
        if _floor_path:
            _floor_argv = [_floor_path, "-I", "-S", "-B", _floor_os.path.abspath(__file__), *_floor_sys.argv[1:]]
            _floor_os.execv(_floor_path, _floor_argv)
    _floor_sys.exit("initialize_linux_root_seed.py requires Python 3.11+ (tomllib); none found on PATH")

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path, PurePosixPath
import os
import stat
import subprocess
import time
import tarfile
import tomllib


def load(name: str, path: Path):
    if "__trust_source_loader__" in globals():
        return __trust_source_loader__.module(name, path)
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise ValueError(f"missing initialization helper: {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


HERE = Path(__file__).resolve().parent
support = load("trust_root_mint_support", HERE / "mint_seed_support.py")
ledger = load("trust_root_host_ledger", HERE / "seed_host_ledger.py")
initialization = load("trust_root_initialization", HERE / "seed_root_initialization.py")
linux = load("trust_root_linux", HERE / "lib/seed_linux.py")


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def git(root: Path, *args: str, raw=False, end=None):
    if '__trust_source_loader__' in globals() and __trust_source_loader__.context is not None:
        live = __trust_source_loader__.context
        argv = ['/usr/bin/git','--no-replace-objects','-c','core.fsmonitor=false',
                '-c','core.untrackedCache=false','-C',str(root),*args]
        env = {'PATH':'/usr/bin:/bin','HOME':'/','LC_ALL':'C',
               'GIT_CONFIG_NOSYSTEM':'1','GIT_CONFIG_GLOBAL':'/dev/null'}
        seconds = 60 if end is None else min(60, end - time.monotonic())
        result = live.auxiliary('git','initialize.git',argv,Path.cwd(),env,
                                maximum=48*2**20,seconds=seconds,raw=raw)
        require(result.returncode == 0, f'cannot authenticate source Git state: {result.stderr!r}')
        return result.stdout if raw else result.stdout.strip()
    if end is not None:
        require(time.monotonic() < end, "original source capture deadline expired")
    result = subprocess.run(["/usr/bin/git", "--no-replace-objects", "-c", "core.fsmonitor=false",
                             "-c", "core.untrackedCache=false", "-C", str(root), *args],
                            env={"PATH": "/usr/bin:/bin", "HOME": "/", "LC_ALL": "C",
                                 "GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": "/dev/null"},
                            capture_output=True, text=not raw,
                            timeout=60 if end is None else min(60, max(0, end - time.monotonic())), check=False)
    require(result.returncode == 0, f"cannot authenticate source Git state: {result.stderr.strip()}")
    return result.stdout if raw else result.stdout.strip()


def source_snapshot(root: Path, expected_commit: str, *, physical=None, deadline=None) -> dict:
    """Bind every actual recursive gitlink and tracked byte, including symlinks."""
    root = root.resolve(strict=True)
    repositories = []

    def visit(path: Path, commit: str) -> None:
        def read(*arguments, raw=False):
            return git(path, *arguments, raw=raw, end=deadline)
        physical_entries = []
        require(Path(read("rev-parse", "--show-toplevel")).resolve() == path,
                "source provider is uninitialized or resolves to a different repository")
        require(read("rev-parse", "HEAD") == commit, "source provider differs from its exact pin")
        require(read("rev-parse", "--is-shallow-repository") == "false", "shallow source is not admitted")
        for name in ("objects/info/alternates", "info/grafts"):
            named = Path(read("rev-parse", "--git-path", name))
            named = named if named.is_absolute() else path / named
            require(not named.exists(), "source alternates or grafts are not admitted")
        require(not read("for-each-ref", "refs/replace"), "source replacement refs are not admitted")
        require(not read("status", "--porcelain=v1", "--untracked-files=all", "--ignore-submodules=none"),
                "source provider must be clean and committed")
        flags = read("ls-files", "-v", "-z").split("\0")
        require(all(not entry or entry[0] == "H" for entry in flags),
                "source assume-unchanged or skip-worktree bits are not admitted")
        state = hashlib.sha256()
        children, count = [], 0
        physical_bytes = 0
        for entry in read("ls-files", "--stage", "-z").split("\0"):
            if deadline is not None:
                require(time.monotonic() < deadline and count < 2_000_000,
                        "original physical source capture deadline/entry bound expired")
            if not entry:
                continue
            metadata, _, relative = entry.partition("\t")
            mode, object_id, stage = metadata.split()
            require(stage == "0", "source index has unresolved entries")
            if physical is not None:
                physical_entries.append({"path":relative,"git_mode":mode,"object_id":object_id})
            named = path / relative
            if mode == "160000":
                children.append((named, object_id))
                digest = object_id
            elif mode == "120000":
                require(named.is_symlink(), "tracked source link is no longer a link")
                data = os.fsencode(os.readlink(named))
                digest = hashlib.sha256(data).hexdigest()
                blob = hashlib.new("sha1" if len(object_id) == 40 else "sha256")
                blob.update(f"blob {len(data)}\0".encode() + data)
                require(blob.hexdigest() == object_id, "tracked source link differs from its committed bytes")
            else:
                require(mode in ("100644", "100755") and named.is_file() and not named.is_symlink(),
                        "tracked source file is missing or has a different kind")
                require(named.stat().st_mode & 0o111 == int(mode, 8) & 0o111,
                        "tracked source executable modes differ from their committed index")
                fd = os.open(named, os.O_RDONLY | os.O_NOFOLLOW)
                with os.fdopen(fd, "rb") as stream:
                    before = os.fstat(stream.fileno())
                    require(stat.S_ISREG(before.st_mode), "tracked source is no longer a regular file")
                    if deadline is not None:
                        physical_bytes += before.st_size
                        require(physical_bytes <= 64 * 1024 * 1024 * 1024, "physical source payload bound exceeded")
                    blob = hashlib.new("sha1" if len(object_id) == 40 else "sha256")
                    blob.update(f"blob {before.st_size}\0".encode())
                    content = hashlib.sha256()
                    for block in iter(lambda: stream.read(1 << 20), b""):
                        if deadline is not None:
                            require(time.monotonic() < deadline, "original physical source read deadline expired")
                        blob.update(block)
                        content.update(block)
                    after = os.fstat(stream.fileno())
                fields = ("st_dev", "st_ino", "st_size", "st_mtime_ns", "st_ctime_ns", "st_mode")
                require(all(getattr(before, k) == getattr(after, k) for k in fields),
                        "tracked source changed during byte capture")
                require(blob.hexdigest() == object_id,
                        f"tracked source differs from its committed bytes despite Git's status: {named}")
                digest = content.hexdigest()
            state.update(json.dumps([relative, mode, object_id, digest], separators=(",", ":")).encode() + b"\n")
            count += 1
        require(count > 0, "source repository contains no tracked inputs")
        repositories.append({"path": path.relative_to(root).as_posix(), "commit": commit,
                             "tree": read("rev-parse", "HEAD^{tree}"),
                             "tracked_files": count, "tracked_bytes_sha256": state.hexdigest()})
        if physical is not None:
            size = read("cat-file", "-s", commit)
            require(size.isascii() and size.isdigit() and int(size) <= 2 * 1024 * 1024,
                    "source commit object exceeds physical proof bound")
            physical(path, commit, repositories[-1]["tree"], physical_entries,
                     read("cat-file", "commit", commit, raw=True))
        for child, pin in children:
            visit(child, pin)
        require(read("rev-parse", "HEAD") == commit
                and not read("status", "--porcelain=v1", "--untracked-files=all", "--ignore-submodules=none"),
                "source changed during its input snapshot")

    visit(root, expected_commit)
    return {"schema": "trust.genesis-source-closure.v1", "source_commit": expected_commit,
            "repositories": repositories}


def bind_archive(archive: Path, expected_sha256: str, sysroot: Path, component: str, host: str) -> dict:
    """Bind bin/lib/libexec payload bytes of one authenticated official archive."""
    archive = support.canonical_regular_file(archive, "external bootstrap archive")
    require(support.sha256_file(archive) == expected_sha256, "external bootstrap archive checksum mismatch")
    top = archive.name.removesuffix(".tar.xz")
    require(top.endswith("-" + host), "external bootstrap archive platform mismatch")
    inner = f"rust-std-{host}" if component == "rust-std" else component
    records, seen, expanded, members = [], set(), 0, 0
    with tarfile.open(archive, "r:xz") as bundle:
        for member in bundle:
            members += 1
            require(members <= support.MAX_ARCHIVE_MEMBERS, "external archive member count exceeds its bound")
            path = support.normalized_member(member.name)
            require(path.parts[0] == top and str(path) not in seen, "external archive has an escaping or duplicate path")
            seen.add(str(path))
            require(member.isfile() or member.isdir() or member.issym() or member.islnk(),
                    "external archive has a special entry")
            require(not member.mode & 0o6000, "external archive has privileged payload modes")
            if member.isfile():
                expanded += member.size
                require(0 <= member.size and expanded <= support.MAX_UNPACKED_BYTES,
                        "external archive expansion exceeds its bound")
            if member.issym() or member.islnk():
                support.resolved_link(path, member.linkname, hard=member.islnk())
            if len(path.parts) < 3 or path.parts[1] != inner:
                continue
            relative = PurePosixPath(*path.parts[2:])
            if relative.parts[0] not in ("bin", "lib", "libexec") or member.isdir():
                continue
            installed = sysroot.joinpath(*relative.parts)
            require(installed.resolve(strict=True).is_relative_to(sysroot), "external tool escapes its selected sysroot")
            if member.isfile():
                require(installed.is_file() and not installed.is_symlink(), "external installed payload kind mismatch")
                stream = bundle.extractfile(member)
                require(stream is not None, "external archive payload is unreadable")
                digest = support.sha256_stream(stream)
                require(support.sha256_file(installed) == digest, "external installed payload differs from its archive")
                records.append({"path": str(relative), "sha256": digest})
            elif member.issym():
                require(installed.is_symlink() and installed.readlink().as_posix() == member.linkname,
                        "external installed link differs from its archive")
                records.append({"path": str(relative), "link": member.linkname})
            else:
                target = support.resolved_link(path, member.linkname, hard=True)
                require(len(target.parts) > 2 and target.parts[:2] == (top, inner),
                        "external hardlink escapes its payload component")
                source = sysroot.joinpath(*target.parts[2:])
                require(installed.is_file() and support.sha256_file(installed) == support.sha256_file(source),
                        "external installed hardlink bytes differ")
                records.append({"path": str(relative), "sha256": support.sha256_file(source)})
    required = "bin/rustc" if component == "rustc" else "bin/cargo" if component == "cargo" else None
    require(records and (required is None or any(r["path"] == required for r in records)),
            "external archive has no required native payload")
    return {"component": component, "archive_sha256": expected_sha256, "payloads": records}


def external_root(role: str, host: str, manifest: Path, archives: Path, sysroot: Path, admission: dict) -> dict:
    expected = admission["external_roots"][role]
    manifest_bytes = ledger.read_proof_file(manifest)
    require(hashlib.sha256(manifest_bytes).hexdigest() == expected["manifest_sha256"],
            "external root channel manifest differs from its exact pin")
    document = tomllib.loads(manifest_bytes.decode("utf-8"))
    sysroot = sysroot.resolve(strict=True)
    require(sysroot.is_dir(), "external root is not a native sysroot")
    components = []
    for name in ("rustc", "cargo", "rust-std"):
        target = document.get("pkg", {}).get(name, {}).get("target", {}).get(host, {})
        require(target.get("available") is True, "external root has no exact native component")
        url = target.get("xz_url", "")
        require(url.startswith("https://static.rust-lang.org/dist/"), "external archive URL leaves its official origin")
        components.append(bind_archive(archives / url.rsplit("/", 1)[1], target["xz_hash"], sysroot, name, host))
    identity = support.compiler_identity(sysroot, f"explicit {role} external oracle", stock_oracle=True)
    require(identity["lineage"] == "stock" and identity["host"] == host
            and identity["commit"] == expected["commit"] and identity["date"] == expected["date"]
            and identity["release"] == expected["release"], "external root actual compiler identity mismatch")
    runtime = linux.external_bootstrap_closure(sysroot, host)
    require(not runtime["unresolved"], "external root has unbound native runtime libraries")
    linux.unchanged(runtime)
    return {"admission": "external-bootstrap-root-only", "counts_as_trust_stage0_evidence": False,
            "manifest_sha256": expected["manifest_sha256"], "identity": identity,
            "components": components, "runtime": runtime}


def prepared_admission(root: Path, host: str, admission: dict, source: dict, roots: dict) -> dict:
    """Recheck actual archive/manifest/proof bytes; prepare metadata, never land pins."""
    text = ledger.read_proof_file(root / "src/stage0").decode("utf-8")
    pins = {}
    for line in text.splitlines():
        key, separator, value = line.partition("=")
        if separator and not key.startswith("#"):
            require(key not in pins, "duplicate prepared source pin")
            pins[key] = value
    seed = root / "bootstrap/trust-stage0"
    records = {}
    for selected in ledger.pinned_hosts(pins):
        prefix = f"host-proofs/{selected}"
        stored = json.loads(ledger.read_proof(seed, ledger.record_path(selected)), object_pairs_hook=ledger.json_object)
        if selected == host:
            raw = ledger.read_proof(seed, prefix + "/GENESIS-ROOT")
            require(stored.get("schema") == ledger.GENESIS_SCHEMA, "prepared native initialization has another evidence kind")
            records[selected], _ = ledger.capture_host_record(seed, pins, selected, stored)
            proof_prefix = prefix + "/initialization/"
            require(json.loads(ledger.read_proof(seed, proof_prefix + "source-closure.json")) == source,
                    "prepared source evidence differs from the actually authenticated current source")
            for role, name in (("genesis", "external-root.json"), ("ddc", "ddc-root.json")):
                require(json.loads(ledger.read_proof(seed, proof_prefix + name)) == roots[role],
                        "prepared external root evidence differs from its actual authenticated archive/tool capture")
            initialization.check_archive_joins(seed, pins, selected, ledger.parse_receipt(raw),
                                               ledger.validate_surface(ledger.read_proof(seed, prefix + "/seed-surface.json"),
                                                                       selected, admission["source_version"]), ledger.read_proof)
        else:
            require(selected == admission["legacy_admission"]["host"],
                    "initialization cannot invent a foreign host admission")
            require(stored.get("schema") == ledger.LEGACY_SCHEMA, "prepared foreign host is not its original legacy admission")
            records[selected], _ = ledger.capture_host_record(seed, pins, selected, stored)
        for relative, expected in records[selected]["payloads"].items():
            archive = support.canonical_regular_file(seed / relative, "prepared native seed archive")
            require(support.sha256_file(archive) == expected, "prepared seed archive checksum differs from its pin")
            with tarfile.open(archive, "r:xz") as bundle:
                support.archive_metadata(bundle, archive, archive.name.removesuffix(".tar.xz"), admission["source_commit"])
    require(host in records and admission["legacy_admission"]["host"] in records,
            "first Linux initialization must preserve the exact original Darwin admission")
    manifest = ledger.read_proof_file(seed / "dist" / pins["compiler_date"] / "channel-rust-trust.toml")
    require(all(hashlib.sha256(manifest).hexdigest() == pins[f"{name}_channel_manifest_hash"]
                for name in ("compiler", "rustfmt")), "prepared channel manifest differs from its pins")
    # Reuse the canonical archive entrypoint reader, then require the exact
    # initialization surface to match the native archive members it actually ships.
    recreate = load("trust_root_recreate", HERE / "recreate_bootstrap.py")
    errors = []
    payloads = [{"path": "bootstrap/trust-stage0/" + k} for k in pins if k.startswith("dist/")]
    _, bindings = recreate._capture_seed_archive_members(root, host, pins, payloads, errors)
    require(not errors, "prepared native archive entrypoints are incomplete: " + "; ".join(errors))
    ledger.check_entrypoint_bindings(records[host], bindings)
    require(all(support.sha256_file(seed / relative) == expected
                for record in records.values() for relative, expected in record["payloads"].items()),
            "prepared archives changed during admission capture")
    return {"host_records": records, "stage0_sha256": digest_bytes(text.encode()),
            "channel_manifest_sha256": digest_bytes(manifest)}


def digest_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def check_inputs(args) -> dict:
    admission = initialization.policy(ledger.read_proof_file)
    host = support.native_host(args.host)
    require(host in initialization.LINUX_HOSTS, "initialization must run on the exact native Linux host")
    source = source_snapshot(args.source_root, admission["source_commit"])
    actual_providers = {row["path"]: row["commit"] for row in source["repositories"]}
    require(all(actual_providers.get(path) == commit for path, commit in admission["providers"].items()),
            "first native Linux root requires all original canonical source providers")
    std_source = support.canonical_regular_file(args.std_source_archive, "authenticated shared std source archive")
    require(support.sha256_file(std_source) == admission["std_source_archive_sha256"],
            "shared std source archive differs from its exact existing pin")
    roots = {role: external_root(role, host, getattr(args, role + "_manifest"),
                                getattr(args, role + "_archives"), getattr(args, role + "_sysroot"), admission)
             for role in ("genesis", "ddc")}
    result = {"schema": "trust.linux-root-initialization-inputs.v1", "status": "inputs-authenticated",
            "host": host, "source": source, "external_roots": roots,
            "scope": "tracked recursive source, external compiler/std/tool archive bytes and native ELF observations",
            "admitted_root_seed": False, "counts_as_trust_stage0_evidence": False}
    if args.prepared_root:
        result["prepared_admission"] = prepared_admission(args.prepared_root, host, admission, source, roots)
    require(source_snapshot(args.source_root, admission["source_commit"]) == source,
            "source changed during initialization input capture")
    after_roots = {role: external_root(role, host, getattr(args, role + "_manifest"),
                                      getattr(args, role + "_archives"), getattr(args, role + "_sysroot"), admission)
                   for role in ("genesis", "ddc")}
    require(after_roots == roots, "external archive/std/tool/runtime inputs changed during capture")
    require(support.sha256_file(std_source) == admission["std_source_archive_sha256"],
            "shared std source archive changed during initialization capture")
    return result


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, required=True)
    parser.add_argument("--std-source-archive", type=Path, required=True)
    parser.add_argument("--host")
    parser.add_argument("--prepared-root", type=Path, help="check completed native producer archives/evidence, never change main pins")
    for role in ("genesis", "ddc"):
        for field in ("manifest", "archives", "sysroot"):
            parser.add_argument(f"--{role}-{field}", type=Path, required=True)
    parser.add_argument("--snapshot", type=Path, help="write a fresh input snapshot, never a GENESIS-ROOT")
    args = parser.parse_args(argv)
    try:
        result = check_inputs(args)
        if args.snapshot:
            support.write_json_exclusive(args.snapshot, result)
        print(json.dumps({k: result[k] for k in ("schema", "status", "host", "admitted_root_seed",
                                               "counts_as_trust_stage0_evidence")}, indent=2))
        return 0
    except (OSError, ValueError, support.WorkflowError) as error:
        print(json.dumps({"status": "refused", "reason": str(error), "admitted_root_seed": False}))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
