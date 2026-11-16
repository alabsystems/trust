#!/usr/bin/env python3
"""Retain completed Stage1 producer images before another bootstrap changes them.

This is engineering provenance and artifact storage, never a proof receipt,
installed SDK, or reusable Cargo/ABI cache. Run immediately after successful
normal emission, before install/dist work that can replace stamps or sysroots.
"""
from __future__ import annotations

import argparse
import contextlib
import hashlib
import json
import os
from pathlib import Path
import re
import runpy
import stat
import time
import traceback


class Refusal(RuntimeError):
    pass


def require(condition, message):
    if not condition:
        raise Refusal(message)


def digest(path):
    h = hashlib.sha256()
    with open(path, "rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def identity(info):
    return (info.st_dev, info.st_ino, info.st_mode, info.st_nlink,
            info.st_size, info.st_mtime_ns, info.st_ctime_ns)


@contextlib.contextmanager
def real_directory(path):
    """Open every component without following a link; retain the final dirfd."""
    path = Path(path)
    require(path.is_absolute() and ".." not in path.parts, f"noncanonical directory: {path}")
    fd = os.open("/", os.O_RDONLY | os.O_DIRECTORY)
    try:
        for part in path.parts[1:]:
            child = os.open(part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=fd)
            os.close(fd)
            fd = child
        yield fd
    finally:
        os.close(fd)


def directory_identity(path):
    with real_directory(path) as fd:
        return identity(os.fstat(fd))[:3]



# Bootstrap's one documented source-output alias. Retained destinations remain
# entirely real directories; no arbitrary or nested source alias is admitted.
BUILD_NOINDEX = "build.noindex"


def source_build_alias(root):
    lexical = root / "build"
    if not lexical.is_symlink():
        return None
    physical = root / BUILD_NOINDEX
    try:
        link_before = identity(lexical.lstat())
        target = os.readlink(lexical)
        require(target in {BUILD_NOINDEX, str(physical)},
                "source build alias is not a direct build.noindex spelling")
        require(stat.S_ISDIR(physical.lstat().st_mode)
                and lexical.resolve(strict=True) == physical,
                "source build alias is not the real sibling build.noindex")
        directory = directory_identity(physical)
        require(link_before == identity(lexical.lstat()), "source build alias changed during capture")
    except (OSError, RuntimeError) as error:
        raise Refusal("source build alias cannot be bound to real build.noindex") from error
    return {"path": str(lexical), "target": target, "identity": list(link_before),
            "physical_directory": str(physical), "directory_identity": list(directory)}


def logical_source_relative(root, path):
    require(path.is_absolute() and path.is_relative_to(root) and ".." not in path.parts,
            "source producer path is outside its root")
    relative = path.relative_to(root)
    alias = source_build_alias(root)
    if relative.parts and relative.parts[0] == BUILD_NOINDEX and alias is not None:
        relative = Path("build", *relative.parts[1:])
    return relative


def physical_source_path(root, relative, alias):
    if relative.parts[0] == "build" and alias is not None:
        return root / BUILD_NOINDEX / Path(*relative.parts[1:])
    return root / relative


def read_record(path):
    path = Path(path).absolute()
    with real_directory(path.parent) as parent_fd:
        fd = os.open(path.name, os.O_RDONLY | os.O_NOFOLLOW, dir_fd=parent_fd)
        with os.fdopen(fd, "rb") as stream:
            before = os.fstat(stream.fileno())
            require(stat.S_ISREG(before.st_mode), "emission record is not regular")
            raw = stream.read()
            require(identity(before) == identity(os.fstat(stream.fileno()))
                    == identity(os.stat(path.name, dir_fd=parent_fd, follow_symlinks=False)), "emission record changed")
    return json.loads(raw), hashlib.sha256(raw).hexdigest(), list(identity(before))


def source_book(root, emission, owner):
    require(emission.get("exit") == 0 and emission.get("source_bookends_equal") is True,
            "emission is not a successful source-bookended run")
    phases = emission.get("phases")
    require(isinstance(phases, list) and len(phases) == 1 and phases[0].get("phase") == "emission"
            and phases[0].get("exit") == 0, "emission phase is not uniquely successful")
    argv = phases[0].get("argv", [])
    constructor = str(root / "scripts/recreate_bootstrap.py")
    require(argv.count(constructor) == 1, "emission did not name the selected source constructor")
    tail = argv[argv.index(constructor) + 1:]
    require(tail.count("--stage") == 1 and tail[tail.index("--stage") + 1:][:1] == ["1"]
            and "--no-build" not in tail and "--require-seed" in tail
            and "--no-register" in tail and "--no-atpkg" in tail,
            "emission is not the unregistered canonical seed-first Stage1 build")
    before, after = emission.get("source_before"), emission.get("source_after")
    require(before == after and isinstance(after, list) and bool(after), "emission source books differ or are empty")
    require(len({row["path"] for row in after}) == len(after), "duplicate emission repository")
    lineage = owner["capture_source_lineage"](root)
    require(lineage.get("status") == "immutable_release" and not lineage.get("errors"), "current source lineage is not clean and immutable")
    rows = {row["path"]: row for row in lineage["repositories"]}
    require(set(rows) == {row["path"] for row in after}, "current recursive repository population differs")
    require(rows["."]["head"] == emission["selected_public_commit"], "selected source commit differs")
    for row in after:
        current = rows[row["path"]]
        require(row["tracked_status"] == "" and current["head"] == row["commit"]
                and current["head_tree"] == row["tree"], f"source subject differs: {row['path']}")
    configs = {}
    for name in ("bootstrap.toml", "config.toml"):
        path = root / name
        if name in emission:
            require(path.is_file() and not path.is_symlink(), f"missing/aliased configuration: {name}")
            require(digest(path) == emission[name]["sha256"], f"configuration changed: {name}")
            configs[name] = emission[name]
        else:
            require(not path.exists() and not path.is_symlink(), f"unrecorded configuration: {name}")
    require(bool(configs), "emission contains no configuration binding")
    return {"lineage": lineage, "configs": configs}


def stamp_entries(root, host, target, role, raw):
    """Parse bootstrap's h/t/s stamp with exact producer namespaces."""
    require(raw and raw.endswith(b"\0"), "empty or unterminated producer stamp")
    require(role in {"compiler0-rustc", "compiler1-std"}, "unknown stamp generation")
    build = root / "build" / host
    prefix, profile = ("stage1-rustc", "release") if role == "compiler0-rustc" else ("stage1-std", "dist")
    entries = []
    for field in raw[:-1].split(b"\0"):
        require(bool(field) and field[:1] in (b"h", b"t", b"s"), "unknown/empty dependency tag")
        tag = field[:1].decode("ascii")
        path = Path(os.fsdecode(field[1:]))
        require(path.is_absolute() and ".." not in path.parts, f"noncanonical stamp path: {path}")
        path = root / logical_source_relative(root, path)
        namespace = build / prefix / (profile if tag == "h" else target + "/" + profile)
        require(path.is_relative_to(namespace) and path != namespace, f"stamp path outside {role}/{tag} namespace: {path}")
        entries.append({"path": path.relative_to(root).as_posix(), "dependency_tag": tag,
                        "producer_role": role, "target": target})
    require(len({row["path"] for row in entries}) == len(entries), "duplicate producer stamp path")
    return entries


def build_plan(root, host, targets, owner):
    """Select producers, not final SDK destinations or compiler-private ABI."""
    for triple in (host, *targets):
        require(bool(re.fullmatch(r"[A-Za-z0-9_]+(?:-[A-Za-z0-9_]+)+", triple)), "invalid target triple")
    require(targets and len(set(targets)) == len(targets) and host in targets, "targets must uniquely include the host")
    require(host.endswith("-apple-darwin"), "only the maintained native Apple Stage1 producer layout is supported")
    alias = source_build_alias(root)
    build = root / "build" / host
    plan = [{"path": (build / "stage1-rustc" / host / "release/rustc-main").relative_to(root).as_posix(),
             "producer_role": "compiler0-entrypoint", "target": host}]
    stamps = [(build / "stage1-rustc" / host / "release/.librustc-stamp", "compiler0-rustc", host)]
    stamps += [(build / "stage1-std" / target / "dist/.libstd-stamp", "compiler1-std", target) for target in targets]
    for path, role, target in stamps:
        plan.append({"path": path.relative_to(root).as_posix(), "producer_role": role + "-stamp", "target": target})
    # Retain stamps first; parsing must use the retained bytes, not a live reread.
    tools = build / "stage2-tools-bin" / host
    public = build / "stage1/bin"
    require(public.is_dir() and not public.is_symlink(), "normal Stage1 bin directory is missing/aliased")
    actual = {path.name for path in public.iterdir() if path.is_file() and os.access(path, os.X_OK)}
    required = owner["expected_public_stage_tools"]()
    require(required <= actual, f"normal Stage1 lacks mandatory tools: {sorted(required - actual)}")
    names = set(owner["stage_tool_producers_for"](actual).values()) | {"rust-analyzer-proc-macro-srv"}
    for name in sorted(names):
        plan.append({"path": (tools / name).relative_to(root).as_posix(), "producer_role": "compiler0-tool", "target": host})
    plan.append({"path": (build / "lld/bin/lld").relative_to(root).as_posix(), "producer_role": "native-LLVM-LLD", "target": host})
    aliases = []
    for path in sorted((build / "llvm/lib").glob("libLLVM*.dylib")):
        resolved = path.resolve(strict=True)
        native = physical_source_path(root, (build / "llvm/lib").relative_to(root), alias)
        require(resolved.is_relative_to(native), f"external LLVM runtime alias: {path}")
        resolved_relative = logical_source_relative(root, resolved).as_posix()
        aliases.append({"path": path.relative_to(root).as_posix(), "resolved": resolved_relative,
                        "link": os.readlink(path) if path.is_symlink() else None})
        plan.append({"path": resolved_relative, "producer_role": "native-LLVM-runtime", "target": host})
    for path in sorted((build / "stage0/lib/rustlib" / host / "lib").glob("libstd*.dylib")):
        plan.append({"path": path.relative_to(root).as_posix(), "producer_role": "seed-compiler-runtime-only", "target": host})
    return plan, stamps, aliases


def retain_file(root, output_fd, relative, cutoff_ns):
    """Copy from a retained source fd into retained destination dirfds."""
    relative = Path(relative)
    require(not relative.is_absolute() and ".." not in relative.parts and relative.parts, "invalid retained relative path")
    alias_before = source_build_alias(root)
    source = physical_source_path(root, relative, alias_before)
    parents = [root]
    for part in source.parent.relative_to(root).parts:
        parents.append(parents[-1] / part)
    with real_directory(source.parent) as parent_fd:
        parents_before = [directory_identity(path) for path in parents]
        fd = os.open(source.name, os.O_RDONLY | os.O_NOFOLLOW, dir_fd=parent_fd)
        try:
            before = os.fstat(fd)
            require(stat.S_ISREG(before.st_mode), f"producer is not regular: {source}")
            require(before.st_mtime_ns <= cutoff_ns, f"producer was replaced after emission: {source}")
            dest_fd = os.dup(output_fd)
            try:
                for part in relative.parts[:-1]:
                    try:
                        os.mkdir(part, 0o700, dir_fd=dest_fd)
                    except FileExistsError:
                        pass
                    child = os.open(part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=dest_fd)
                    os.close(dest_fd)
                    dest_fd = child
                target_fd = os.open(relative.name, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600, dir_fd=dest_fd)
                h = hashlib.sha256()
                with os.fdopen(target_fd, "wb") as target, os.fdopen(os.dup(fd), "rb") as original:
                    for chunk in iter(lambda: original.read(1 << 20), b""):
                        target.write(chunk)
                        h.update(chunk)
                    target.flush()
                    os.fchmod(target.fileno(), stat.S_IMODE(before.st_mode) & ~0o222)
                check_fd = os.open(relative.name, os.O_RDONLY | os.O_NOFOLLOW, dir_fd=dest_fd)
                with os.fdopen(check_fd, "rb") as check:
                    retained_before = os.fstat(check.fileno())
                    copied = hashlib.sha256()
                    for chunk in iter(lambda: check.read(1 << 20), b""):
                        copied.update(chunk)
                    require(identity(retained_before) == identity(os.fstat(check.fileno()))
                            == identity(os.stat(relative.name, dir_fd=dest_fd, follow_symlinks=False)), "retained image changed during initial readback")
                require(copied.hexdigest() == h.hexdigest(), f"retained bytes differ: {source}")
                require(identity(before) == identity(os.fstat(fd)) == identity(os.stat(source.name, dir_fd=parent_fd, follow_symlinks=False)), f"producer changed during copy: {source}")
                parents_after = [directory_identity(path) for path in parents]
                require(parents_before == parents_after, f"producer directory role changed: {source}")
                require(source_build_alias(root) == alias_before, "source build alias changed during copy")
            finally:
                os.close(dest_fd)
        finally:
            os.close(fd)
    return {"source_relative": relative.as_posix(), "physical_source_relative": source.relative_to(root).as_posix(),
            "source_build_alias": alias_before, "sha256": h.hexdigest(), "bytes": before.st_size,
            "source_physical_before": list(identity(before)), "source_physical_after": list(identity(before)),
            "retained_physical": list(identity(retained_before)),
            "source_directory_roles": [{"path": str(path), "identity": list(value)} for path, value in zip(parents, parents_before)],
            "original_mode": stat.S_IMODE(before.st_mode), "retained_mode": stat.S_IMODE(before.st_mode) & ~0o222}


def retained_parent(output_fd, parts):
    fd, roles = os.dup(output_fd), []
    try:
        for part in parts:
            child = os.open(part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=fd)
            os.close(fd)
            fd = child
            roles.append(identity(os.fstat(fd))[:3])
        return fd, roles
    except BaseException:
        os.close(fd)
        raise


def read_retained(output_fd, relative, record, *, collect=False):
    """Reopen the recorded image through real directories, never a live alias."""
    relative = Path(relative)
    require(not relative.is_absolute() and ".." not in relative.parts, "invalid retained image path")
    parent_fd, directory_roles = retained_parent(output_fd, relative.parts[:-1])
    try:
        fd = os.open(relative.name, os.O_RDONLY | os.O_NOFOLLOW, dir_fd=parent_fd)
        with os.fdopen(fd, "rb") as stream:
            before = os.fstat(stream.fileno())
            require(stat.S_ISREG(before.st_mode) and stat.S_IMODE(before.st_mode) == record["retained_mode"], "retained image type/mode changed")
            require(list(identity(before)) == record["retained_physical"], "retained image identity changed")
            h, chunks = hashlib.sha256(), []
            for chunk in iter(lambda: stream.read(1 << 20), b""):
                h.update(chunk)
                if collect:
                    chunks.append(chunk)
            require(h.hexdigest() == record["sha256"], "retained image bytes changed")
            require(identity(before) == identity(os.fstat(stream.fileno()))
                    == identity(os.stat(relative.name, dir_fd=parent_fd, follow_symlinks=False)), "retained image changed during read")
        after_fd, after_roles = retained_parent(output_fd, relative.parts[:-1])
        try:
            require(directory_roles == after_roles, "retained image directory roles changed during read")
        finally:
            os.close(after_fd)
        return b"".join(chunks) if collect else None
    finally:
        os.close(parent_fd)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", required=True, type=Path)
    parser.add_argument("--emission-result", required=True, type=Path)
    parser.add_argument("--host", required=True)
    parser.add_argument("--target", required=True, action="append")
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args(argv)
    root, output = args.repo_root.absolute(), args.output.absolute()
    require(".." not in root.parts and root.resolve(strict=True) == root, "source root is aliased/noncanonical")
    require(".." not in output.parts and not output.is_relative_to(root), "retention must be outside source/build inputs")
    require(not output.exists() and not output.is_symlink(), "retention output already exists")
    result = {"schema": 1, "started_unix": time.time(), "scope": "emitted producer artifact/provenance retention only; NEVER Cargo/ABI build-cache inputs",
              "verified": False, "release_ready": False, "controller_sha256": digest(Path(__file__)), "files": []}
    with real_directory(output.parent) as parent_fd:
        os.mkdir(output.name, 0o700, dir_fd=parent_fd)
        output_fd = os.open(output.name, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=parent_fd)
        with contextlib.ExitStack() as output_cleanup:
            output_cleanup.callback(os.close, output_fd)
            try:
                emission, emission_sha, emission_physical = read_record(args.emission_result)
                owner_path = root / "scripts/recreate_bootstrap.py"
                owner = runpy.run_path(str(owner_path))
                result["selected_constructor_sha256"] = digest(owner_path)
                before = source_book(root, emission, owner)
                result.update(selected_source=emission["selected_public_commit"], emission_result_sha256=emission_sha,
                              emission_ended_unix=emission["ended_unix"], emission_record_physical=emission_physical,
                              source_before=before, host=args.host, targets=args.target)
                cutoff = int(emission["ended_unix"] * 1e9)
                plan, stamps, aliases = build_plan(root, args.host, args.target, owner)
                retained = {}
                roles = {}
                def keep(row):
                    relative = row["path"]
                    roles.setdefault(relative, []).append({key: value for key, value in row.items() if key != "path"})
                    if relative not in retained:
                        retained[relative] = retain_file(root, output_fd, relative, cutoff)
                    result["files"] = [{**value, "roles": roles[path]} for path, value in sorted(retained.items())]
                for path, role, target in stamps:
                    keep({"path": path.relative_to(root).as_posix(), "producer_role": role + "-stamp", "target": target})
                    for row in stamp_entries(root, args.host, target, role,
                                             read_retained(output_fd, path.relative_to(root), retained[path.relative_to(root).as_posix()], collect=True)):
                        keep(row)
                for row in plan:
                    keep(row)
                result["files"] = [{**row, "roles": roles[path]} for path, row in sorted(retained.items())]
                result["native_runtime_aliases"] = aliases
                # Re-evaluate all live selection inputs after copying. No alias or stamp
                # can silently select a different producer during this capture.
                require(build_plan(root, args.host, args.target, owner) == (plan, stamps, aliases), "producer plan/aliases changed")
                for path, _, _ in stamps:
                    require(digest(path) == retained[path.relative_to(root).as_posix()]["sha256"], "producer stamp changed")
                for relative, row in retained.items():
                    read_retained(output_fd, relative, row)
                    require(source_build_alias(root) == row["source_build_alias"], "source build alias changed before capture completed")
                    path = physical_source_path(root, Path(relative), row["source_build_alias"])
                    require(list(identity(path.lstat())) == row["source_physical_before"], f"producer changed before capture completed: {path}")
                    for directory in row["source_directory_roles"]:
                        require(list(directory_identity(Path(directory["path"]))) == directory["identity"], f"producer directory changed: {directory['path']}")
                require(read_record(args.emission_result) == (emission, emission_sha, emission_physical), "emission result changed")
                require(digest(owner_path) == result["selected_constructor_sha256"], "selected constructor changed")
                require(digest(Path(__file__)) == result["controller_sha256"], "retention controller changed")
                result["source_after"] = source_book(root, emission, owner)
                require(before == result["source_after"], "source/configuration changed during retention")
                require(directory_identity(output) == identity(os.fstat(output_fd))[:3], "retention directory role changed")
                result["exit"] = 0
            except BaseException as error:
                result.update(exit=1, error=repr(error), traceback=traceback.format_exc())
            result["ended_unix"] = time.time()
            fd = os.open("RESULT.json", os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o400, dir_fd=output_fd)
            with os.fdopen(fd, "w") as stream:
                json.dump(result, stream, indent=2)
                stream.write("\n")
    print(json.dumps({key: value for key, value in result.items() if key not in {"files", "source_before", "source_after"}}, indent=2))
    return result["exit"]


if __name__ == "__main__":
    raise SystemExit(main())
