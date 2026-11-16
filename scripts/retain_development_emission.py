#!/usr/bin/env python3
"""Retain one successful compiler1-owned BUILD development image.

Only artifact/input provenance: not SDK qualification, FullEnvelope, native
runtime ownership, proof, release or a reusable Cargo/ABI cache. Stage1's active
retainer and its IO/refusal implementation remain unchanged.
"""
from __future__ import annotations

import argparse
import contextlib
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import runpy
import shutil
import stat
import subprocess
import sys
import time


def _require_python_311():
    if sys.version_info >= (3, 11):
        return
    if __name__ != "__main__":
        raise SystemExit("development retention requires Python 3.11+ tomllib")
    # The version probes are interpreter startups too. Preserve these policies
    # before executing any candidate, not only when handing off the script.
    startup = []
    if sys.flags.isolated:
        startup.append("-I")
    else:
        if sys.flags.ignore_environment:
            startup.append("-E")
        if sys.flags.no_user_site:
            startup.append("-s")
    if sys.flags.no_site:
        startup.append("-S")
    if sys.dont_write_bytecode:
        startup.append("-B")
    if sys.flags.optimize:
        startup.append("-" + "O" * sys.flags.optimize)
    original = getattr(sys, "orig_argv", None)
    if original:
        arguments = original[1:]
    else:
        # macOS Python 3.9 has no orig_argv. Preserve isolation, site and
        # bytecode policy when restarting this standalone file's invocation.
        arguments = [*startup, __file__, *sys.argv[1:]]
    for candidate in ("python3.14", "python3.13", "python3.12", "python3.11"):
        path = shutil.which(candidate)
        if path is None:
            continue
        try:
            check = subprocess.run(
                [path, *startup, "-c", "import sys; raise SystemExit(sys.version_info < (3, 11))"],
                stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL, timeout=5,
            )
        except (OSError, subprocess.TimeoutExpired):
            continue
        if check.returncode == 0:
            os.execv(path, [path, *arguments])
    raise SystemExit("development retention requires Python 3.11+ tomllib; none found on PATH")


_require_python_311()

try:
    import tomllib
except ModuleNotFoundError:
    raise SystemExit("development retention requires Python 3.11+ tomllib; use managed Python 3.14")
import traceback

_READER = Path(__file__).with_name("retain_stage1_emission.py")
_spec = importlib.util.spec_from_file_location("trust_emitted_producer_io", _READER)
io = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(io)
Refusal = io.Refusal
require = io.require
digest = io.digest
identity = io.identity
directory_identity = io.directory_identity
real_directory = io.real_directory
read_record = io.read_record
read_retained = io.read_retained
retain_file = io.retain_file
source_build_alias = io.source_build_alias
physical_source_path = io.physical_source_path
logical_source_relative = io.logical_source_relative

LLD_FLAVORS = ("ld.lld", "ld64.lld", "lld-link", "wasm-ld")
# The actual Bootstrap LLVM_TOOLS surface, plus its renamed objcopy entry.
LLVM_TOOLS = frozenset(("llvm-cov", "llvm-nm", "llvm-objcopy", "llvm-objdump",
                        "llvm-profdata", "llvm-readobj", "llvm-size", "llvm-strip",
                        "llvm-ar", "llvm-as", "llvm-dis", "llvm-link", "llc", "opt", "llubi"))


def installed_native_tools(root, host):
    directory = root / "build" / host / "stage2/lib/rustlib" / host / "bin"
    require(directory.is_dir() and not directory.is_symlink(), "installed native tool directory is missing/aliased")
    entries, llvm = [], {}
    for path in sorted(directory.iterdir()):
        if path.name == "gcc-ld":
            require(path.is_dir() and not path.is_symlink(), "installed linker directory is aliased")
            require({p.name for p in path.iterdir()} == set(LLD_FLAVORS), "installed linker flavor population differs")
            entries.extend(path / name for name in LLD_FLAVORS)
        else:
            require(path.name in LLVM_TOOLS | {"rust-objcopy", "rust-lld"}, "unknown installed native tool: " + str(path))
            entries.append(path)
            if path.name != "rust-lld":
                llvm[path.relative_to(root).as_posix()] = "llvm-objcopy" if path.name == "rust-objcopy" else path.name
    for path in entries:
        require(path.is_file() and not path.is_symlink(), "installed native tool is not regular: " + str(path))
    return entries, llvm


def regular_snapshot(path):
    """Bind one observed provider input without following its final component."""
    with real_directory(path.parent) as parent_fd:
        fd = os.open(path.name, os.O_RDONLY | os.O_NOFOLLOW, dir_fd=parent_fd)
        with os.fdopen(fd, "rb") as stream:
            before = os.fstat(stream.fileno())
            require(stat.S_ISREG(before.st_mode), "native provider input is not regular")
            sha = hashlib.file_digest(stream, "sha256").hexdigest()
            require(identity(before) == identity(os.fstat(stream.fileno()))
                    == identity(os.stat(path.name, dir_fd=parent_fd, follow_symlinks=False)), "native provider input changed")
    return {"path": str(path), "sha256": sha, "physical": list(identity(before))}


def llvm_tool_sources(root, host):
    """Observe the same native --bindir selection as Bootstrap's compiler step.

    This is post-emission byte custody, never the external LLVM's source-build
    identity, original build-input custody, or proof authority.
    """
    _, installed = installed_native_tools(root, host)
    if not installed:
        return None
    config = configuration(root)
    parsed = tomllib.loads((root / config["path"]).read_text())
    selected = parsed.get("target", {}).get(host, {}).get("llvm-config")
    if selected is None:
        selected = str(physical_source_path(root, Path("build") / host / "llvm/bin/llvm-config", source_build_alias(root)))
    require(isinstance(selected, str), "native llvm-config selection is not text")
    program = Path(selected)
    require(program.is_absolute() and ".." not in program.parts, "native llvm-config selection is not absolute/canonical")
    before = regular_snapshot(program)
    response = subprocess.run([str(program), "--bindir"], capture_output=True, timeout=30)
    require(response.returncode == 0 and len(response.stdout) <= 65536, "native llvm-config --bindir failed")
    lines = response.stdout.decode().splitlines()
    require(len(lines) == 1 and lines[0], "native LLVM bindir is ambiguous")
    directory = Path(lines[0])
    require(directory.is_absolute() and ".." not in directory.parts and directory.name == "bin", "native LLVM bindir is not a canonical bin directory")
    with real_directory(directory):
        provider_root = directory.parent
        root_identity = list(directory_identity(provider_root))
        bindings = []
        for installed_path, name in sorted(installed.items()):
            path = directory / name
            resolved = path.resolve(strict=True)
            require(resolved.is_relative_to(provider_root), "native LLVM tool alias escapes selected provider")
            require(resolved.is_file() and not resolved.is_symlink(), "native LLVM tool source is not regular")
            bindings.append({"installed": installed_path, "selected": str(path),
                             "resolved": resolved.relative_to(provider_root).as_posix(),
                             "alias": os.readlink(path) if path.is_symlink() else None,
                             "selection_physical": list(identity(path.lstat()))})
    require(before == regular_snapshot(program), "native llvm-config changed during selection")
    require(digest(root / config["path"]) == config["sha256"], "native provider configuration changed")
    return {"root": str(provider_root), "root_identity": root_identity,
            "configuration": before, "bindir_stdout_sha256": hashlib.sha256(response.stdout).hexdigest(),
            "bindir_stderr_sha256": hashlib.sha256(response.stderr).hexdigest(), "bindings": bindings}


def configuration(root):
    paths = [p for p in (root / "bootstrap.toml", root / "config.toml") if p.exists() or p.is_symlink()]
    require(len(paths) == 1, "development capture requires exactly one direct source configuration")
    path = paths[0]
    require(path.is_file() and not path.is_symlink(), "development configuration is missing/aliased")
    parsed = tomllib.loads(path.read_text())
    require(not parsed.get("include"), "recursive config includes are unsupported; capture an explicit root configuration or add an effective-config adapter")
    build = parsed.get("build", {})
    require(isinstance(build, dict) and type(build.get("full-bootstrap")) is bool,
            "set explicit [build].full-bootstrap=false (normal uplift) or true; retention never guesses Std generation")
    host, hosts, targets = build.get("build"), build.get("host"), build.get("target")
    require(isinstance(host, str) and hosts == [host], "development capture needs explicit native build/host configuration")
    require(isinstance(targets, list) and targets and all(isinstance(value, str) for value in targets)
            and len(set(targets)) == len(targets) and host in targets, "development capture needs the complete explicit configured target population")
    return {"path": path.name, "sha256": digest(path), "full_bootstrap": build["full-bootstrap"],
            "public_std_stage": 2 if build["full-bootstrap"] else 1, "host": host, "targets": targets}


def native_request(root, argv):
    launcher = str(root / "x.py")
    require(isinstance(argv, list) and argv.count(launcher) == 1, "emission must name its actual native x.py constructor once")
    tail = argv[argv.index(launcher) + 1:]
    require(tail and tail.pop(0) == "build", "development capture needs an actual BUILD invocation")
    stage, selectors = None, []
    while tail:
        token = tail.pop(0)
        if token == "--stage":
            require(stage is None and tail, "ambiguous/missing native producer stage")
            stage = tail.pop(0)
        elif token in {"--jobs", "-j"}:
            require(tail and re.fullmatch(r"[1-9][0-9]*", tail.pop(0)), "invalid native job count")
        elif token == "--config":
            require(tail and Path(tail.pop(0)) == root / configuration(root)["path"], "native configuration differs")
        else:
            require(token in {"trustc-dev", "rustc-dev"},
                    "unsupported native override/selector; use sole explicit BUILD development component, not --set/dry-run/kept/skip/default routes")
            selectors.append(token)
    require(stage == "1" and len(selectors) == 1, "native request must select exactly one stage1 development producer")
    return {"constructor": launcher, "producer_stage": 1, "output_stage": 2, "selector": selectors[0]}


def source_book(root, emission, owner):
    require(emission.get("exit") == 0 and emission.get("source_bookends_equal") is True,
            "emission is not a successful source-bookended run")
    phases = emission.get("phases")
    require(isinstance(phases, list) and len(phases) == 1 and phases[0].get("phase") == "emission"
            and phases[0].get("exit") == 0, "native emission phase is not uniquely successful")
    request = native_request(root, phases[0].get("argv"))
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
    config = configuration(root)
    require(config["path"] in emission and config["sha256"] == emission[config["path"]]["sha256"], "configuration changed or was not captured")
    return {"lineage": lineage, "configuration": config, "native_request": request}


def stamp_entries(root, host, target, role, raw):
    require(raw and raw.endswith(b"\0"), "empty or unterminated producer stamp")
    if role == "compiler1-rustc":
        stage, family, profile = 2, "rustc", "release"
    else:
        match = re.fullmatch(r"compiler([12])-std", role)
        require(match is not None, "unknown development stamp generation")
        stage, family, profile = int(match[1]), "std", "dist"
    build = root / "build" / host / f"stage{stage}-{family}"
    rows = []
    for field in raw[:-1].split(b"\0"):
        require(field and field[:1] in (b"h", b"t", b"s"), "unknown/empty dependency tag")
        tag = field[:1].decode("ascii")
        path = Path(os.fsdecode(field[1:]))
        require(path.is_absolute() and ".." not in path.parts, f"noncanonical stamp path: {path}")
        path = root / logical_source_relative(root, path)
        namespace = build / (profile if tag == "h" else target + "/" + profile)
        require(path.is_relative_to(namespace) and path != namespace, f"stamp path outside {role}/{tag} namespace: {path}")
        rows.append({"path": path.relative_to(root).as_posix(), "dependency_tag": tag,
                     "producer_role": role, "target": target})
    require(len({row["path"] for row in rows}) == len(rows), "duplicate producer stamp path")
    return rows


def build_plan(root, host, targets, owner):
    for triple in (host, *targets):
        require(bool(re.fullmatch(r"[A-Za-z0-9_]+(?:-[A-Za-z0-9_]+)+", triple)), "invalid target triple")
    require(targets and len(set(targets)) == len(targets) and host in targets, "targets must uniquely include the host")
    require(host.endswith("-apple-darwin"), "only the maintained native Apple development layout is supported")
    config = configuration(root)
    require(config["host"] == host and len(targets) == len(config["targets"])
            and set(targets) == set(config["targets"]), "retention host/targets differ from actual native configuration")
    std_stage = config["public_std_stage"]
    alias = source_build_alias(root)
    build, prefix = root / "build" / host, root / "build" / host / "stage2"
    plan = [{"path": (build / "stage2-rustc" / host / "release/rustc-main").relative_to(root).as_posix(),
             "producer_role": "compiler1-entrypoint", "target": host}]
    stamps = [(build / "stage2-rustc" / host / "release/.librustc-stamp", "compiler1-rustc", host)]
    stamps += [(build / f"stage{std_stage}-std" / target / "dist/.libstd-stamp", f"compiler{std_stage}-std", target) for target in targets]
    runtime_std = (build / "stage1-std" / host / "dist/.libstd-stamp", "compiler1-std", host)
    if runtime_std not in stamps:
        stamps.append(runtime_std)
    public = prefix / "bin"
    require(public.is_dir() and not public.is_symlink(), "normal stage2 bin directory is missing/aliased")
    actual = {p.name for p in public.iterdir() if p.is_file() and os.access(p, os.X_OK)}
    require(owner["expected_public_stage_tools"]() <= actual, "stage2 lacks mandatory public tools")
    for name in sorted(set(owner["stage_tool_producers_for"](actual).values()) | {"rust-analyzer-proc-macro-srv"}):
        plan.append({"path": (build / "stage3-tools-bin" / host / name).relative_to(root).as_posix(), "producer_role": "compiler1-tool", "target": host})
    plan.append({"path": (build / "lld/bin/lld").relative_to(root).as_posix(), "producer_role": "native-LLVM-LLD", "target": host})
    # Observe the actual installed image too. No guessed metadata graft or
    # unlisted target population is selected for the later SDK compositor.
    for directory in [public, prefix / "libexec", prefix / "lib", *[prefix / "lib/rustlib" / t / "lib" for t in targets]]:
        require(directory.is_dir() and not directory.is_symlink(), f"missing/aliased installed image directory: {directory}")
        for p in sorted(directory.iterdir()):
            if p.is_file() or p.is_symlink():
                plan.append({"path": p.relative_to(root).as_posix(), "producer_role": "actual-stage2-installed-image",
                             "target": directory.parent.name if directory.name == "lib" and directory.parent.name in targets else host})
        if directory.name == "lib" and directory.parent.name in targets:
            for name in ["rustc-dependencies", "self-contained"]:
                extra = directory / name
                if extra.exists():
                    require(extra.is_dir() and not extra.is_symlink(), "installed library subdirectory is aliased")
                    for p in sorted(extra.iterdir()):
                        require(p.is_file() and not p.is_symlink(), "installed library member is not regular")
                        plan.append({"path": p.relative_to(root).as_posix(), "producer_role": "actual-stage2-installed-image", "target": directory.parent.name})
    installed, _ = installed_native_tools(root, host)
    for path in installed:
        plan.append({"path": path.relative_to(root).as_posix(), "producer_role": "actual-stage2-installed-image", "target": host})
    if any(path.parent.name == "gcc-ld" for path in installed):
        plan.append({"path": (build / "stage3-tools-bin" / host / "lld-wrapper").relative_to(root).as_posix(),
                     "producer_role": "compiler1-lld-wrapper", "target": host})
    aliases = []
    for p in sorted((build / "llvm/lib").glob("libLLVM*.dylib")):
        resolved = p.resolve(strict=True)
        native = physical_source_path(root, (build / "llvm/lib").relative_to(root), alias)
        require(resolved.is_relative_to(native), f"external LLVM runtime alias: {p}")
        relative = logical_source_relative(root, resolved).as_posix()
        aliases.append({"path": p.relative_to(root).as_posix(), "resolved": relative,
                        "link": os.readlink(p) if p.is_symlink() else None})
        plan.append({"path": relative, "producer_role": "native-LLVM-runtime", "target": host, "runtime_name": p.name})
    return plan, stamps, aliases


def verify_installed_bindings(root, host, targets, owner, retained, roles, read_bytes, llvm_inputs=None):
    """Finite producer-to-installed byte equality, never build/proof authority."""
    build = Path("build") / host
    prefix = build / "stage2"
    def same(left, right):
        left, right = str(left), str(right)
        require(left in retained and right in retained, f"missing observed binding: {left} / {right}")
        require(retained[left]["sha256"] == retained[right]["sha256"], f"installed producer mismatch: {left} / {right}")
    entry = build / "stage2-rustc" / host / "release/rustc-main"
    for name in ("trustc", "rustc"):
        same(prefix / "bin" / name, entry)
    actual = {Path(name).name for name in retained if Path(name).parent == prefix / "bin"}
    for public, producer in owner["stage_tool_producers_for"](actual).items():
        same(prefix / "bin" / public, build / "stage3-tools-bin" / host / producer)
    for left, right in (("targo", "cargo"), ("trustdoc", "rustdoc")):
        same(prefix / "bin" / left, prefix / "bin" / right)
    same(prefix / "libexec/trust-analyzer-proc-macro-srv",
         build / "stage3-tools-bin" / host / "rust-analyzer-proc-macro-srv")
    for installed in (prefix / "bin/rust-lld", prefix / "lib/rustlib" / host / "bin/rust-lld"):
        same(installed, build / "lld/bin/lld")
    installed, llvm_tools = installed_native_tools(root, host)
    for path in installed:
        if path.parent.name == "gcc-ld":
            same(path.relative_to(root), build / "stage3-tools-bin" / host / "lld-wrapper")
    if llvm_tools:
        require(isinstance(llvm_inputs, dict), "installed LLVM tools lack observed native provider inputs")
        bindings = llvm_inputs["selection"]["bindings"]
        require(len(bindings) == len(llvm_tools) and {r["installed"] for r in bindings} == set(llvm_tools), "native LLVM binding population differs")
        sources = {r["source_relative"]: r for r in llvm_inputs["files"]}
        for row in bindings:
            require(row["installed"] in retained and row["resolved"] in sources, "missing retained native LLVM binding")
            require(retained[row["installed"]]["sha256"] == sources[row["resolved"]]["sha256"], "installed native LLVM tool differs from selected provider: " + row["installed"])
    public_std_stage = configuration(root)["public_std_stage"]
    allowed, runtime = {}, {}
    def admit(path, source):
        allowed.setdefault(str(path), set()).add(retained[source]["sha256"])
    std_names = {target: set() for target in targets}
    for source, source_roles in roles.items():
        for role in source_roles:
            family = role.get("producer_role")
            if family == "native-LLVM-runtime":
                name = role.get("runtime_name", Path(source).name)
                runtime.setdefault(str(prefix / "lib" / name), set()).add(retained[source]["sha256"])
                continue
            if family not in {"compiler1-rustc", "compiler1-std", "compiler2-std"}:
                continue
            tag, target = role["dependency_tag"], role["target"]
            name = Path(source).name
            routed = host if tag == "h" else target
            directory = prefix / "lib/rustlib" / routed / "lib"
            if tag == "s":
                directory /= "self-contained"
            if family == f"compiler{public_std_stage}-std" and target in targets:
                admit(directory / name, source)
                same(directory / name, source)
                std_names[target].add(name)
            if family == "compiler1-rustc":
                # Assemble may isolate legitimate compiler helper versions.
                choices = [directory / name, directory / "rustc-dependencies" / name]
                matches = [p for p in choices if str(p) in retained and retained[str(p)]["sha256"] == retained[source]["sha256"]]
                require(len(matches) == 1, f"missing/ambiguous current compiler metadata: {source}")
                admit(matches[0], source)
                if tag == "t" and Path(name).suffix in {".dylib", ".so", ".dll"}:
                    runtime.setdefault(str(prefix / "lib" / name), set()).add(retained[source]["sha256"])
            if family == "compiler1-std" and target == host and tag == "t" and name.startswith("libstd-") and name.endswith(".dylib"):
                runtime.setdefault(str(prefix / "lib" / name), set()).add(retained[source]["sha256"])
    for target, names in std_names.items():
        for crate in ("core", "alloc", "std", "compiler_builtins", "test", "proc_macro", "trust_bignum"):
            require(any(name.startswith("lib" + crate + "-") and name.endswith(".rlib") for name in names), f"incomplete full Std: {target}/{crate}")
    # The native Step publishes this exact installed archive and provider DATA.
    # The receipt alone authenticates neither external input custody nor an SDK.
    native_receipt = prefix / "lib/rustlib" / host / "lib/trust-llvm-native-dev.json"
    native_binding = {"present": False, "external_input_or_provider_reauthenticated": False}
    if str(native_receipt) in retained:
        data = json.loads(read_bytes(str(native_receipt)))
        require(data.get("schema") == "trust.llvm-static-native-dev.v1"
                and data.get("library") == "zstd" and data.get("kind") == "static", "unknown native-development receipt")
        archive = prefix / "lib/rustlib" / host / "lib/libzstd.a"
        require(str(archive) in retained and retained[str(archive)]["sha256"] == data.get("sha256"), "native-development archive differs from staged provider DATA")
        allowed.setdefault(str(archive), set()).add(data["sha256"])
        native_binding.update(present=True, staged_archive_sha256=data["sha256"],
                              scope="staged provider DATA matches retained archive only; original producer input books remain required")
    seen_driver = False
    for name, row in retained.items():
        path = Path(name)
        if not path.is_relative_to(prefix / "lib") or path.suffix not in {".rlib", ".rmeta", ".dylib", ".so", ".dll", ".a", ".o"}:
            continue
        if path.parent == prefix / "lib":
            require(row["sha256"] in runtime.get(name, set()), f"unbound compiler1 runtime: {name}")
            seen_driver |= path.name.startswith("librustc_driver-")
        else:
            require(row["sha256"] in allowed.get(name, set()), f"unbound current compiler/std/native installed artifact: {name}")
    require(seen_driver, "installed development image has no current compiler runtime")
    return native_binding


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
              "verified": False, "release_ready": False, "controller_sha256": digest(Path(__file__)), "files": [], "reader_sha256": digest(_READER), "schema_name": "trust.development-emission-retention.v1"}
    with real_directory(output.parent) as parent_fd:
        os.mkdir(output.name, 0o700, dir_fd=parent_fd)
        output_fd = os.open(output.name, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=parent_fd)
        with contextlib.ExitStack() as output_cleanup:
            output_cleanup.callback(os.close, output_fd)
            try:
                emission, emission_sha, emission_physical = read_record(args.emission_result)
                owner_path = root / "scripts/recreate_bootstrap.py"
                owner = runpy.run_path(str(owner_path))
                result["surface_policy_sha256"] = digest(owner_path)
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
                # Keep external/in-tree LLVM provider bytes in a distinct
                # namespace: they are observed inputs, never compiler cache
                # artifacts or a claim about how that provider was built.
                selection = llvm_tool_sources(root, args.host)
                llvm_inputs = None
                if selection is not None:
                    os.mkdir("native-llvm-inputs", 0o700, dir_fd=output_fd)
                    native_fd = os.open("native-llvm-inputs", os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=output_fd)
                    with contextlib.ExitStack() as native_cleanup:
                        native_cleanup.callback(os.close, native_fd)
                        provider_root = Path(selection["root"])
                        native_files = [retain_file(provider_root, native_fd, path, cutoff)
                                        for path in sorted({r["resolved"] for r in selection["bindings"]})]
                        llvm_inputs = {"selection": selection, "files": native_files,
                                       "retained_directory": "native-llvm-inputs",
                                       "original_provider_build_authority": False,
                                       "scope": "post-emission provider/installed byte equality only"}
                        for row in native_files:
                            read_retained(native_fd, row["source_relative"], row)
                        require(llvm_tool_sources(root, args.host) == selection, "native LLVM selection changed during retention")
                    result["native_llvm_tool_inputs"] = llvm_inputs
                result["native_development_binding"] = verify_installed_bindings(
                    root, args.host, args.target, owner, retained, roles,
                    lambda relative: read_retained(output_fd, relative, retained[relative], collect=True),
                    llvm_inputs=llvm_inputs,
                )
                result["files"] = [{**row, "roles": roles[path]} for path, row in sorted(retained.items())]
                result["producer_stage"] = 1
                result["output_stage"] = 2
                result["public_std_stage"] = before["configuration"]["public_std_stage"]
                result["native_runtime_aliases"] = aliases
                # Re-evaluate all live selection inputs after copying. No alias or stamp
                # can silently select a different producer during this capture.
                require(build_plan(root, args.host, args.target, owner) == (plan, stamps, aliases), "producer plan/aliases changed")
                require(llvm_tool_sources(root, args.host) == selection, "native LLVM selection changed before capture completed")
                for path, _, _ in stamps:
                    require(digest(path) == retained[path.relative_to(root).as_posix()]["sha256"], "producer stamp changed")
                for relative, row in retained.items():
                    read_retained(output_fd, relative, row)
                    require(source_build_alias(root) == row["source_build_alias"], "source build alias changed before capture completed")
                    path = physical_source_path(root, Path(relative), row["source_build_alias"])
                    require(list(identity(path.lstat())) == row["source_physical_before"], f"producer changed before capture completed: {path}")
                    for directory in row["source_directory_roles"]:
                        require(list(directory_identity(Path(directory["path"]))) == directory["identity"], f"producer directory changed: {directory['path']}")
                if llvm_inputs is not None:
                    with real_directory(output / "native-llvm-inputs") as native_fd:
                        for row in llvm_inputs["files"]:
                            read_retained(native_fd, row["source_relative"], row)
                            provider = Path(selection["root"])
                            require(source_build_alias(provider) == row["source_build_alias"], "native LLVM provider build alias changed")
                            path = physical_source_path(provider, Path(row["source_relative"]), row["source_build_alias"])
                            require(list(identity(path.lstat())) == row["source_physical_before"], "native LLVM provider input changed before capture completed")
                            for directory in row["source_directory_roles"]:
                                require(list(directory_identity(Path(directory["path"]))) == directory["identity"], "native LLVM provider directory changed")
                require(read_record(args.emission_result) == (emission, emission_sha, emission_physical), "emission result changed")
                require(digest(owner_path) == result["surface_policy_sha256"], "surface policy changed")
                require(digest(Path(__file__)) == result["controller_sha256"], "retention controller changed")
                require(digest(_READER) == result["reader_sha256"], "shared strict retention reader changed")
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
