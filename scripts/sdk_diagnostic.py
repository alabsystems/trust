"""Focused complete-SDK diagnostics; never a daily-stage or publication receipt.

The public entry is ``daily_toolchain_stage.py diagnose``. The native package
lease owns the worker's lifetime. A worker result is internal data; only the
public parent records the actual lease process outcome. No result is consumed
as SDK, mint, DDC, proof, model or publication authority.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import runpy
import shutil
import stat
import subprocess
import sys
import tomllib
import types

SCHEMA = "trust.sdk-diagnostic-command.v1"
SCOPE = "actual diagnostic command only; no SDK, DDC, proof, model or publication authority"
ADMISSION = ["--cpus", "6", "--mem-gb", "34"]
MOVER_ENV = frozenset({
    "RUSTC", "RUSTDOC", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER",
    "CARGO_BUILD_RUSTC", "CARGO_BUILD_RUSTDOC", "CARGO_BUILD_RUSTC_WRAPPER",
    "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER", "TARGO_BUILD_RUSTC", "TARGO_BUILD_RUSTDOC",
    "TARGO_BUILD_RUSTC_WRAPPER", "TARGO_BUILD_RUSTC_WORKSPACE_WRAPPER",
    "TRUST_STAGE2_BIN", "RUSTFLAGS", "RUSTDOCFLAGS", "CARGO_ENCODED_RUSTFLAGS",
    "CARGO_ENCODED_RUSTDOCFLAGS", "TARGO_ENCODED_RUSTFLAGS", "TARGO_ENCODED_RUSTDOCFLAGS",
    "RUSTUP_HOME", "RUSTUP_TOOLCHAIN", "CARGO_HOME", "TARGO_HOME", "CARGO_TARGET_DIR",
    "CARGO_BUILD_TARGET_DIR", "TARGO_TARGET_DIR", "TARGO_BUILD_TARGET_DIR", "TRUST_TOOLCHAIN_HOME",
    "CARGO_BUILD_TARGET", "TARGO_BUILD_TARGET", "CARGO_BUILD_RUSTFLAGS", "TARGO_BUILD_RUSTFLAGS",
})
CONFIG_ENV = MOVER_ENV | {"PATH", "TARGO", "TRUST_TOOLCHAIN_PYTHON3", "TRUST_TOOLCHAIN_SERIAL_COMMAND"}
MOVER_BUILD = frozenset({"rustc", "rustdoc", "rustc-wrapper", "rustc-workspace-wrapper",
                         "target", "target-dir", "build-dir"})


def require(value, message):
    if not value:
        raise ValueError(message)


def unique(pairs):
    value = {}
    for key, item in pairs:
        require(key not in value, f"duplicate JSON field: {key}")
        value[key] = item
    return value


def regular(path: Path, maximum=1 << 20) -> bytes:
    descriptor = os.open(path, os.O_RDONLY | os.O_NONBLOCK | os.O_NOFOLLOW)
    try:
        before = os.fstat(descriptor)
        require(stat.S_ISREG(before.st_mode) and before.st_size <= maximum,
                f"not a bounded regular input: {path}")
        chunks = []
        total = 0
        while data := os.read(descriptor, min(1 << 20, maximum + 1 - total)):
            chunks.append(data)
            total += len(data)
            require(total <= maximum, f"input exceeds bound: {path}")
        identity = lambda info: (info.st_dev, info.st_ino, info.st_mode, info.st_size,
                                 info.st_mtime_ns, info.st_ctime_ns)
        require(identity(before) == identity(os.fstat(descriptor)) == identity(path.lstat()),
                f"input changed while read: {path}")
        return b"".join(chunks)
    finally:
        os.close(descriptor)


def command_arguments(command: list[str], work: Path) -> list[str]:
    command = command[1:] if command[:1] == ["--"] else command
    require(command[:1] == ["targo"], "diagnose requires canonical `targo` argv after --")
    require(len(command) >= 3 and command[1] in {"--unverified", "trust"}
            and command[2] in {"build", "check", "test"},
            "diagnose requires an explicit unverified or verified build/check/test lane")
    own = command[:command.index("--", 1)] if "--" in command[1:] else command
    require("--locked" in own and "--offline" in own,
            "the focused diagnostic requires owner --locked --offline flags before any test separator")
    require(own.count("--unverified") == (1 if command[1] == "--unverified" else 0),
            "diagnostic lane is ambiguous")
    for word in own:
        require("\0" not in word, "command contains NUL")
        require(not word.startswith(("--target=", "--target-dir=", "--resource-worker"))
                and word not in {"--target", "--target-dir", "-C"} and not word.startswith("-C"),
                "command overrides the host, isolated target, directory or worker profile")
        require(not (word.startswith("-") and not word.startswith("--") and "C" in word),
                "command changes its working directory through a short-option cluster")
    for index, word in enumerate(own):
        if word == "--manifest-path":
            require(index + 1 < len(own), "missing manifest path")
            path = Path(own[index + 1])
        elif word.startswith("--manifest-path="):
            path = Path(word.partition("=")[2])
        else:
            continue
        path = (work / path).resolve(strict=True) if not path.is_absolute() else path.resolve(strict=True)
        require(path.is_relative_to(work), "manifest escapes the selected source worktree")
    return command


def config_inputs(work: Path, environment: dict, command: list[str]) -> dict:
    """Read the actual Cargo walk plus declared CLI configs; refuse movers/includes.

    This is a restriction of the diagnostic profile, not a replacement Cargo
    evaluator. Unknown include graphs refuse rather than being approximated.
    """
    home = Path(environment["CARGO_HOME"])
    candidates = [directory / name for directory in
                  [home, *(parent / ".cargo" for parent in (work, *work.parents))]
                  for name in ("config", "config.toml")]
    inline = []
    own = command[:command.index("--", 1)] if "--" in command[1:] else command
    for index, word in enumerate(own):
        if word == "--config":
            require(index + 1 < len(own), "missing --config value")
            value = own[index + 1]
        elif word.startswith("--config="):
            value = word.partition("=")[2]
        else:
            continue
        if "=" in value:
            inline.append(value)
        else:
            path = Path(value)
            candidates.append(path if path.is_absolute() else work / path)
    result = {}

    def admit(data, label):
        require(isinstance(data, dict) and "include" not in data,
                f"diagnostic does not admit included Cargo config: {label}")
        build = data.get("build", {})
        require(isinstance(build, dict) and not MOVER_BUILD.intersection(build),
                f"Cargo config moves the selected compiler or target: {label}")
        target = data.get("target", {})
        require(isinstance(target, dict), f"unsupported target config: {label}")
        for settings in target.values():
            require(isinstance(settings, dict) and not {"runner", "linker"}.intersection(settings),
                    f"Cargo config replaces the native runner or linker: {label}")
        for settings in [build, *target.values()]:
            flags = settings.get("rustflags", [])
            require("--sysroot" not in str(flags), f"Cargo config replaces the SDK sysroot: {label}")
        configured_env = data.get("env", {})
        require(isinstance(configured_env, dict) and not CONFIG_ENV.intersection(configured_env),
                f"Cargo config supplies a compiler mover: {label}")
        require(not any(key.startswith(("CARGO_TARGET_", "TARGO_TARGET_"))
                        and key.endswith(("_RUNNER", "_LINKER", "_RUSTFLAGS")) for key in configured_env),
                f"Cargo config supplies a native execution override: {label}")

    for path in candidates:
        name = str(path.absolute())
        if not os.path.lexists(path):
            result[name] = None
            continue
        raw = regular(path)
        admit(tomllib.loads(raw.decode("utf-8")), name)
        result[name] = {"sha256": hashlib.sha256(raw).hexdigest(), "bytes": len(raw)}
    for index, value in enumerate(inline):
        admit(tomllib.loads(value), f"--config[{index}]")
        result[f"inline:{index}"] = {"sha256": hashlib.sha256(value.encode()).hexdigest()}
    return result


def native_record(aterm: Path, tool: str) -> dict:
    result = subprocess.run([str(aterm), "pkg", "which", "--json", tool],
                            capture_output=True, timeout=30)
    require(result.returncode == 0, f"managed native tool is unavailable: {tool}")
    value = json.loads(result.stdout, object_pairs_hook=unique)
    require(value.get("schema") == 1 and value.get("managed") is True
            and value.get("status") == "ready", f"native tool is not managed/ready: {tool}")
    return value


def managed_sdk(sdk: Path, selected: dict) -> None:
    """Constrain the public route to the native store's actual Trust namespace.

    A positional native lease accepts unmanaged paths too. A diagnostic must
    not mistake that no-op exit0 for a held SDK. The configured native lookup
    supplies this store namespace; the real lease still takes the actual lock.
    Neither this path check nor a positional lifetime lease authenticates a
    signed installation. This diagnostic never reports SDK readiness.
    """
    require(selected.get("package") == "trust", "selected Targo is not managed Trust")
    current = Path(selected["store_root"]).resolve(strict=True)
    require(current.parent.name == "trust" and current.parent.parent.name == "store",
            "native Trust store layout is unavailable")
    require(sdk.is_absolute() and not sdk.is_symlink() and sdk.resolve(strict=True) == sdk
            and sdk.parent == current.parent and re.fullmatch(r"[1-9][0-9]*(?:\.noindex)?", sdk.name),
            "SDK path is outside the native Trust lifetime namespace; an unmanaged lease supplies no standing")
    require(0 < int(sdk.name.removesuffix(".noindex")) < 1 << 64,
            "SDK build is outside the native positive u64 lease subject domain")


class GitReader:
    """The daily owner's original fixed OS Git and closed environment."""
    def __init__(self, source):
        owner = runpy.run_path(str(source / "scripts/recreate_bootstrap.py"), run_name="diagnostic_managed_git_owner")
        self.command = owner["_controlled_git_command"]([])
        self.environment = owner["_provenance_git_environment"]()
        self.executable = Path(self.command[0])

    def read(self, work, *argv):
        child = subprocess.run([*self.command, "-C", str(work), *argv],
                               env=self.environment, timeout=60, capture_output=True)
        require(child.returncode == 0 and not child.stderr,
                f"controlled Git query refused ({child.returncode}): {child.stderr.decode(errors='replace')}")
        return child.stdout


def index_entries(git: GitReader, work: Path, *paths):
    """Expand sparse tree DATA explicitly; never force a full mutable index."""
    rows = git.read(work, "ls-files", "--sparse", "--stage", "-z", "--", *paths)
    for raw in rows.split(b"\0"):
        if not raw:
            continue
        fields, name = raw.split(b"\t", 1)
        mode, blob, stage = fields.decode().split()
        require(stage == "0", "source worktree has unresolved merge stages")
        if mode == "040000":
            for item in git.read(work, "ls-tree", "-rz", blob).split(b"\0"):
                if item:
                    declaration, leaf = item.split(b"\t", 1)
                    leaf_mode, _kind, leaf_blob = declaration.decode().split()
                    yield os.fsdecode(name + leaf), leaf_mode, leaf_blob
        else:
            yield os.fsdecode(name), mode, blob


def helper_book(owner, source: Path, git: GitReader) -> dict:
    selected = {source / name for name, _mode, _blob in
                index_entries(git, source, "scripts", "tools", "src/bootstrap/stage0_identity.py")}
    selected.update({Path(__file__).resolve(), source / "scripts/daily_toolchain_stage.py"})
    return {str(path.relative_to(source)): owner["file_hash"](path)
            for path in sorted(selected) if path.is_file() and not path.is_symlink()}


def executable_book(owner, paths: dict) -> dict:
    result = {}
    for name, path in paths.items():
        path = Path(path)
        before = path.lstat()
        require(stat.S_ISREG(before.st_mode), f"executable input must be a regular file: {path}")
        digest = owner["file_hash"](path)
        identity = lambda item: (item.st_dev, item.st_ino, item.st_mode, item.st_size,
                                 item.st_mtime_ns, item.st_ctime_ns)
        require(identity(before) == identity(path.lstat()), f"executable input changed: {path}")
        result[name] = {"path": str(path), "sha256": digest, "identity": identity(before)}
    return result


def worktree_book(owner, work: Path, output: Path, git: GitReader) -> dict:
    """Bind available working DATA and absence, including dirty/untracked input.

    This is a diagnostic source book, not a source/module proof or a cache key.
    Sparse absent blobs remain explicitly absent; this never hydrates reports.
    """
    head = git.read(work, "rev-parse", "HEAD").decode().strip()
    entries = {}
    for name, mode, blob in index_entries(git, work):
        entries[name] = {"git_mode": mode, "git_blob": blob}
    other = git.read(work, "ls-files", "--sparse", "--others", "--exclude-standard", "-z")
    for name in other.split(b"\0"):
        if name:
            entries[os.fsdecode(name)] = {"untracked": True}
    digest = hashlib.sha256()
    count = 0
    with output.open("xb") as stream:
        for name, declaration in sorted(entries.items()):
            path = work / name
            row = {"path": name, **declaration}
            try:
                info = path.lstat()
                row["mode"] = stat.S_IMODE(info.st_mode)
                if stat.S_ISREG(info.st_mode):
                    row.update(kind="file", bytes=info.st_size, sha256=owner["file_hash"](path))
                elif stat.S_ISLNK(info.st_mode):
                    row.update(kind="link", target=os.readlink(path))
                elif stat.S_ISDIR(info.st_mode) and declaration.get("git_mode") == "160000":
                    if os.path.lexists(path / ".git"):
                        nested = output.with_name(output.name + f".submodule-{count}")
                        row.update(kind="submodule", working=worktree_book(owner, path, nested, git))
                    else:
                        row.update(kind="unmaterialized-submodule")
                else:
                    raise ValueError(f"source contains an unsupported special input: {path}")
            except FileNotFoundError:
                row["kind"] = "absent"
            raw = json.dumps(row, sort_keys=True, ensure_ascii=True).encode() + b"\n"
            stream.write(raw)
            digest.update(raw)
            count += 1
    return {"head": head, "sha256": digest.hexdigest(), "entries": count,
            "scope": "available tracked/untracked working DATA, links and explicit absence"}


def doctor_binding(source: Path, report: dict, sdk: Path) -> None:
    """Reuse the native frontend owner's general exact sibling binding check."""
    path = source / "scripts/sdk_frontend_component.py"
    module = types.ModuleType("diagnostic_frontend_binding")
    module.__file__ = str(path)
    exec(compile(regular(path), str(path), "exec"), module.__dict__)
    module.doctor_observation(report, sdk)


def host_triple() -> str:
    import platform
    machine = {"arm64": "aarch64", "AMD64": "x86_64"}.get(platform.machine(), platform.machine())
    suffix = {"darwin": "apple-darwin", "linux": "unknown-linux-gnu"}.get(sys.platform)
    require(suffix is not None and machine in {"aarch64", "x86_64"}, "unsupported diagnostic host")
    return f"{machine}-{suffix}"


class Diagnostic:
    def __init__(self, owner, request):
        self.owner, self.request = owner, request
        self.state = Path(request["state"])
        self.source = Path(request["source"])
        self.work = Path(request["repo"])
        self.sdk = Path(request["sdk"])
        self.cleanup = Path(request["publication"])
        self.python = Path(sys.executable).resolve(strict=True)
        self.steps = []
        self.environment = dict(os.environ)
        self.result = {"schema": SCHEMA, "scope": SCOPE, "passed": False,
                       "command_started": False, "command_attempted": False,
                       "steps": self.steps, "request": request,
                       "sdk_ready": False, "consumer_ready": False, "publication_ready": False}

    def save(self):
        self.owner["atomic_json"](self.state / "worker-result.json", self.result)

    def call(self, name, argv, cwd=None, *, heavy=False, env=None, timeout=None):
        log = self.state / f"{len(self.steps):03d}-{name}.log"
        result_path = log.with_suffix(".result.json") if heavy else None
        actual = argv
        if heavy:
            actual = self.owner["owned_step_argv"](
                self.source / "scripts/build-slot", self.python,
                self.source / "scripts/daily_toolchain_stage.py", self.cleanup,
                result_path, timeout, argv, ADMISSION)
        step = {"name": name, "command": argv, "argv": actual, "cwd": str(cwd or self.work),
                "log": str(log), "started_at": self.owner["now"](), "status": "running"}
        self.steps.append(step)
        self.save()
        try:
            output = self.owner["command"](actual, cwd or self.work, env or self.environment, log,
                         timeout=None if heavy else timeout, cleanup_owner=self.cleanup)
            if result_path is not None:
                require(result_path.is_file(), "owned command omitted its original exit result")
                detail = self.owner["read_json"](result_path)
                if detail.get("exit_code") != 0 or detail.get("timed_out") or detail.get("interrupted"):
                    raise self.owner["CommandFailed"]("owned command did not complete successfully",
                                                       detail.get("exit_code"), detail.get("timed_out", False))
            step.update(status="completed", exit_code=0)
            # Preserve the complete raw log. Like Runner.call, owner queries
            # return only the body after command()'s exact JSON header.
            return output.partition("\n")[2].strip()
        except BaseException as error:
            if result_path is not None and result_path.exists():
                self.owner["bind_owned_failure"](step, error, self.owner["read_json"](result_path))
                if isinstance(error, self.owner["CommandFailed"]):
                    step["wrapper_error"] = str(error)
                    error.args = (f"actual owned child exited {error.exit_code}, timed_out={error.timed_out}; see {log}",)
            step.update(status="failed", error=str(error))
            if isinstance(error, self.owner["CommandFailed"]):
                step.update(exit_code=error.exit_code, timed_out=error.timed_out)
            elif isinstance(error, (KeyboardInterrupt, InterruptedError)):
                step.update(exit_code=getattr(error, "child_exit_code", None), interrupted=True)
            if step.get("owned_result", {}).get("interrupted") and isinstance(error, self.owner["CommandFailed"]):
                raise InterruptedError("owned diagnostic interrupted; original cleanup completed") from error
            raise
        finally:
            if result_path is not None and result_path.exists():
                detail = self.owner["read_json"](result_path)
                step["owned_result"] = detail
                step["exit_code"] = detail["exit_code"]
                step["timed_out"] = detail["timed_out"]
                step["interrupted"] = detail["interrupted"]
            if log.exists():
                step["log_identity"] = self.owner["fingerprint"](log)
            step["finished_at"] = self.owner["now"]()
            self.save()

    def run(self):
        owner = self.owner
        try:
            command = command_arguments(self.request["command"], self.work)
            git = GitReader(self.source)
            source_before = helper_book(owner, self.source, git)
            owner["cleanup_api"](self.cleanup)
            explicit_movers = {key for key in MOVER_ENV if os.environ.get(key)} - {
                "RUSTUP_HOME", "RUSTUP_TOOLCHAIN", "CARGO_HOME", "TARGO_HOME", "CARGO_TARGET_DIR",
                "CARGO_BUILD_TARGET_DIR", "TARGO_TARGET_DIR", "TARGO_BUILD_TARGET_DIR", "TRUST_TOOLCHAIN_HOME"}
            require(not explicit_movers, "ambient compiler movers are not diagnostic inputs: "
                    + ", ".join(sorted(explicit_movers)))
            require(not any(key.startswith(("CARGO_TARGET_", "TARGO_TARGET_"))
                            and key.endswith(("_RUNNER", "_LINKER", "_RUSTFLAGS")) and value
                            for key, value in os.environ.items()), "ambient native runner/linker override")
            # These are actual environment restrictions of this focused route,
            # not changes to the original publication consumer profile.
            base = owner["bootstrap_environment"](dict(os.environ), self.source / "scripts/recreate_bootstrap.py")
            for key in list(base):
                if key.startswith(("TRUST_", "CARGO_ENCODED_", "TARGO_ENCODED_")) or key in MOVER_ENV:
                    base.pop(key)
            for key in ("BUILD_SLOT_HELD", "BUILD_SLOT_CPU_PROTOCOL", "CARGO_BUILD_JOBS", "RUSTUP_TOOLCHAIN"):
                require(not os.environ.get(key), f"diagnose requires fresh admission, not inherited {key}")
            base["CARGO_HOME"] = self.request["cargo_home"]
            # The original surface owner's alias checks require its explicit
            # interpreter even before the whole-SDK copy/private environment.
            base["TRUST_TOOLCHAIN_PYTHON3"] = str(self.python)
            tools = {"python": self.python, "cleanup": self.cleanup / "bin/pub",
                     "serial": Path(self.request["serial"]), "git": git.executable}
            if "native_aterm" in self.request:
                tools["aterm"] = Path(self.request["native_aterm"])
            tool_before = executable_book(owner, tools)
            configured = config_inputs(self.work, base, command)
            self.environment = base
            self.result["helper_identity"] = source_before
            self.result["tool_identity"] = tool_before
            self.result["cargo_configs"] = configured
            source_input = worktree_book(owner, self.work, self.state / "source-opening.jsonl", git)
            self.result["source_identity"] = source_input
            # A known-bad complete surface refuses before expensive copy, any
            # compiler-start gate or the requested command. No waiver exists.
            self.call("selected-sdk-output-contract", ["sh", str(self.source / "tools/verify-toolchain.sh"), str(self.sdk)])
            original = owner["fingerprint"](self.sdk)
            self.result["sdk_identity"] = original
            staged = self.state / "sdk"
            shutil.copytree(self.sdk, staged, symlinks=True)
            require(owner["fingerprint"](self.sdk) == original == owner["fingerprint"](staged),
                    "complete SDK copy or original changed")
            rustup = Path(shutil.which("rustup", path=base.get("PATH")) or "").resolve(strict=True)
            require(rustup.is_file() and os.access(rustup, os.X_OK), "real rustup is unavailable")
            tools["rustup"] = rustup
            require(executable_book(owner, {key: value for key, value in tools.items() if key != "rustup"})
                    == tool_before, "native inputs changed during complete SDK copy")
            tool_before = executable_book(owner, tools)
            self.result["tool_identity"] = tool_before
            rustup_home = self.state / "rustup"
            private_bin = rustup_home / "bin"
            private_bin.mkdir(parents=True)
            (private_bin / "rustup").symlink_to(rustup)
            self.environment = owner["consumer_environment"](
                base, staged, rustup_home, self.state / "target", base.get("PATH", ""))
            self.environment["TRUST_TOOLCHAIN_PYTHON3"] = str(self.python)
            self.environment["TMPDIR"] = str(self.state / "tmp")
            Path(self.environment["TMPDIR"]).mkdir(mode=0o700)
            promotion = {**self.environment, "TRUST_TOOLCHAIN_SERIAL_COMMAND": self.request["serial"]}
            owner["full_sdk_gates"](self.call, staged, self.source, host_triple(), self.python, promotion)
            self.call("scratch-trust-link", [str(rustup), "toolchain", "link", "trust", str(staged)])
            link = rustup_home / "toolchains/trust"
            require(link.is_symlink() and link.resolve(strict=True) == staged,
                    "private trust binding differs")
            sysroot = self.call("selected-sysroot", [str(rustup), "run", "trust", "trustc", "--print", "sysroot"])
            require(Path(sysroot.strip()).resolve(strict=True) == staged, "selected sysroot differs")
            raw = self.call("exact-sdk-doctor", [str(staged / "bin/targo"), "trust", "doctor", "--format", "json"])
            doctor_binding(self.source, json.loads(raw, object_pairs_hook=unique), staged)
            require(config_inputs(self.work, self.environment, command) == configured,
                    "Cargo configuration changed during SDK preflight")
            require(helper_book(owner, self.source, git) == source_before
                    and executable_book(owner, tools) == tool_before
                    and owner["fingerprint"](self.sdk) == original == owner["fingerprint"](staged)
                    and worktree_book(owner, self.work, self.state / "source-before-command.jsonl", git) == source_input,
                    "SDK, helper or source changed before command")
            self.result.update(command_attempted=True, command_started=None)
            self.save()
            try:
                self.call("diagnostic-command", [str(staged / "bin/targo"), *command[1:]],
                          heavy=True, timeout=self.request["timeout"])
            finally:
                self.result["command_result"] = self.steps[-1]
                detail = self.steps[-1].get("owned_result", {})
                if type(detail.get("exit_code")) is int:
                    # An actual original child wait proves the Targo process
                    # launched. Admission dispatch alone proves no such thing.
                    self.result["command_started"] = True
            require(helper_book(owner, self.source, git) == source_before
                    and executable_book(owner, tools) == tool_before
                    and owner["fingerprint"](self.sdk) == original == owner["fingerprint"](staged)
                    and config_inputs(self.work, self.environment, command) == configured
                    and worktree_book(owner, self.work, self.state / "source-closing.jsonl", git) == source_input,
                    "SDK, helper, source or configuration changed during command")
            require(link.is_symlink() and link.resolve(strict=True) == staged, "private trust binding changed")
            self.result.update(passed=True, inputs_stable=True)
            return 0
        except BaseException as error:
            self.result.update(refusal=str(error), inputs_stable=False)
            if isinstance(error, (KeyboardInterrupt, InterruptedError)):
                self.result["interrupted"] = True
                return 130
            return 1
        finally:
            self.save()


def worker(request_path: Path, owner) -> int:
    # Internal worker data grants no standing. The public parent owns and
    # records the actual native lease process, and accepts no `already held`
    # flag, mutable checkpoint, caller receipt or cached successful result.
    request = json.loads(regular(request_path), object_pairs_hook=unique)
    require(request.get("schema") == SCHEMA, "wrong diagnostic request")
    return Diagnostic(owner, request).run()


def parser():
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("--sdk", type=Path, required=True, help="exact installed managed full Trust SDK root")
    result.add_argument("--repo", type=Path, required=True, help="owned source worktree")
    result.add_argument("--state-root", type=Path, required=True, help="new exclusive diagnostic output directory")
    result.add_argument("--publication-repo", type=Path, required=True, help="original bounded process-cleanup owner")
    result.add_argument("--serial-command", type=Path, help="managed native serial command (default: native lookup)")
    result.add_argument("--cargo-home", type=Path, help="owned, prepared offline Cargo input/cache home")
    result.add_argument("--timeout", type=int, required=True, help="actual command bound, in seconds (1..86400)")
    result.add_argument("command", nargs=argparse.REMAINDER)
    return result


def collect_worker(state, result, request):
    """Collect only the terminal child's matching data; retain the parent's wait."""
    child = json.loads(regular(state / "worker-result.json", 16 << 20), object_pairs_hook=unique)
    require(isinstance(child, dict) and child.get("schema") == SCHEMA and child.get("scope") == SCOPE
            and child.get("request") == request
            and "command_started" in child
            and (type(child["command_started"]) is bool or child["command_started"] is None)
            and type(child.get("command_attempted")) is bool
            and all(child.get(key) is False for key in
                    ("sdk_ready", "consumer_ready", "publication_ready")),
            "native lease child omitted or changed its actual result")
    lease_fields = {key: value for key, value in result.items() if key.startswith("native_lease_")}
    result.update(child)
    result.update(lease_fields)
    result["passed"] = False
    return child


def main(argv, owner) -> int:
    args = parser().parse_args(argv)
    require(args.state_root.name not in {"", ".", ".."}, "diagnostic state needs a new leaf")
    state = args.state_root.parent.resolve(strict=True) / args.state_root.name
    require(not os.path.lexists(state), "diagnostic state must be new and unlinked")
    state.mkdir(mode=0o700)
    result = {"schema": SCHEMA, "scope": SCOPE, "passed": False, "command_started": False,
              "command_attempted": False,
              "sdk_ready": False, "consumer_ready": False, "publication_ready": False}
    try:
        require(1 <= args.timeout <= 86400, "diagnostic bound must be1..86400 seconds")
        source = Path(owner["__file__"]).resolve().parents[1]
        git = GitReader(source)
        sdk, work = args.sdk.resolve(strict=True), args.repo.resolve(strict=True)
        actual_root = git.read(work, "rev-parse", "--show-toplevel").decode().strip()
        require(Path(actual_root).resolve(strict=True) == work, "repo must name the actual source worktree root")
        require(not state.is_relative_to(sdk) and not state.is_relative_to(work)
                and not sdk.is_relative_to(state) and not work.is_relative_to(state),
                "state must be outside SDK and source")
        command = command_arguments(args.command, work)
        aterm = Path(shutil.which("aterm") or "").resolve(strict=True)
        require(aterm.is_file() and os.access(aterm, os.X_OK), "native aterm is unavailable")
        sdk_lookup = native_record(aterm, "targo")
        managed_sdk(sdk, sdk_lookup)
        serial_lookup = native_record(aterm, "trust-serial-command")
        serial = Path(serial_lookup["physical_executable"]).resolve(strict=True)
        require(args.serial_command is None or args.serial_command.resolve(strict=True) == serial,
                "serial command differs from the actual managed native tool")
        require(not serial.is_symlink() and serial.is_file() and os.access(serial, os.X_OK),
                "managed serial executable is unavailable")
        publication = args.publication_repo.resolve(strict=True)
        owner["cleanup_api"](publication)
        cargo_home = (args.cargo_home or Path(os.environ.get("CARGO_HOME", str(Path.home() / ".cargo")))).resolve(strict=True)
        request = {"schema": SCHEMA, "scope": SCOPE, "sdk": str(sdk), "repo": str(work),
                   "state": str(state), "source": str(source), "publication": str(publication),
                   "serial": str(serial), "cargo_home": str(cargo_home), "timeout": args.timeout,
                   "command": command, "native_namespace_lookup": sdk_lookup,
                   "native_serial": serial_lookup, "native_aterm": str(aterm)}
        request_path = state / "request.json"
        owner["atomic_json"](request_path, request)
        command = [str(aterm), "pkg", "lease", str(sdk), "--", str(aterm), "pkg", "lease",
                   str(Path(serial_lookup["store_root"]).resolve(strict=True)), "--", sys.executable,
                   "-I", "-S", "-B", str(source / "scripts/daily_toolchain_stage.py"),
                   "_sdk-diagnostic-worker", str(request_path)]
        result["native_lease_argv"] = command
        result["native_lease_log"] = str(state / "native-leases.log")
        # Once the worker may have started, absence of terminal evidence is
        # unknown. It is never evidence that the requested command did not run.
        result.update(command_started=None, command_attempted=None)
        try:
            owner["command"](command, state, dict(os.environ), state / "native-leases.log",
                                    cleanup_owner=publication)
            lease_exit = 0
        except owner["CommandFailed"] as error:
            lease_exit = error.exit_code
        result["native_lease_exit"] = lease_exit
        child = collect_worker(state, result, request)
        result["passed"] = child.get("passed") is True and lease_exit == 0
        return 0 if result["passed"] else 1
    except BaseException as error:
        if isinstance(error, (KeyboardInterrupt, InterruptedError)):
            if "request" in locals():
                try:
                    collect_worker(state, result, request)
                except (OSError, ValueError) as child_error:
                    result["worker_collection_refusal"] = str(child_error)
            result.update(interrupted=True, native_lease_exit=getattr(error, "child_exit_code", None))
            result.update(passed=False, refusal=str(error))
            return 130
        result.update(passed=False, refusal=str(error))
        return 1
    finally:
        owner["atomic_json"](state / "result.json", result)
