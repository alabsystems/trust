#!/usr/bin/env python3
"""Build a first Linux root candidate; never manufacture a RootSeed admission.

Run inside one bounded native owner. Its original monotonic deadline covers
input authentication, all builds, archive installation and final input checks.
The candidate is retained even on failure. A completed producer is still not a
GENESIS-ROOT: the separate admission must bind this run's actual closed owner,
commands, inputs and artifacts before any pin changes.
"""

from __future__ import annotations

import os as _floor_os
import shutil as _floor_shutil
import sys as _floor_sys

# Trust: select the TOML-capable driver before authenticating native inputs.
if __name__ == "__main__" and _floor_sys.version_info < (3, 11):
    for _floor_candidate in ("python3.14", "python3.13", "python3.12", "python3.11"):
        _floor_path = _floor_shutil.which(_floor_candidate)
        if _floor_path:
            _floor_os.execv(_floor_path, [_floor_path, "-I", "-S", "-B", _floor_os.path.abspath(__file__), *_floor_sys.argv[1:]])
    _floor_sys.exit("produce_linux_root_seed.py requires Python 3.11+ (tomllib); none found on PATH")

import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import sys
import time
import tomllib

from importlib import util


HERE = Path(__file__).resolve().parent
if "__trust_source_loader__" in globals():
    auth = __trust_source_loader__.module("trust_root_input_auth", HERE / "initialize_linux_root_seed.py")
else:
    spec = util.spec_from_file_location("trust_root_input_auth", HERE / "initialize_linux_root_seed.py")
    assert spec is not None and spec.loader is not None
    auth = util.module_from_spec(spec)
    spec.loader.exec_module(auth)
support, initialization, linux = auth.support, auth.initialization, auth.linux
cohort = auth.load("trust_root_initialization_cohort", HERE / "seed_initialization_cohort.py")
historical = auth.load("trust_root_historical_surface", HERE / "seed_historical_surface.py")
require = auth.require
PHASES = ("external-bootstrap", "candidate-targo", "candidate-self-host", "diverse-ddc", "dist",
          "full-native-build", "build-manifest", "channel-manifest", "original-trustd",
          "full-native-tools", "native-pack", "native-unpack", "packaged-native-tools", "prepare-seed", "install-seed",
          "archive-rebuild")


def encoded(value) -> bytes:
    return (json.dumps(value, sort_keys=True, indent=2) + "\n").encode()


def save(path: Path, value) -> None:
    support.write_json_exclusive(path, value)


def duration_seconds(value: str) -> float:
    units = {"d": 86400, "h": 3600, "min": 60, "s": 1, "ms": .001, "us": .000001}
    parts = re.findall(r"([0-9]+(?:\.[0-9]+)?)(min|ms|us|d|h|s)", value)
    require(parts and " ".join(n + u for n, u in parts) == value,
            "unrecognized finite systemd runtime bound")
    result = sum(float(n) * units[u] for n, u in parts)
    require(math.isfinite(result) and result > 0, "invalid finite systemd runtime bound")
    return result


def held_leases(owner: dict) -> None:
    pid, ticks = owner.get("lease_owner_pid"), owner.get("lease_owner_start_ticks")
    require(type(pid) is int and pid > 1 and linux.stat_identity(pid)[1] == ticks,
            "initialization lease owner is absent or its PID was reused")
    leases = owner.get("leases")
    require(isinstance(leases, list) and len(leases) == 4, "initialization v2 must retain all four original leases")
    paths, identities = set(), set()
    roles = {}
    kernel = Path("/proc/locks").read_text().splitlines()
    for row in leases:
        require(isinstance(row, dict) and isinstance(row.get("path"), str)
                and type(row.get("fd")) is int and row["fd"] >= 0
                and type(row.get("device")) is int and type(row.get("inode")) is int,
                "initialization original lease metadata is malformed")
        path = Path(row["path"])
        identity = path.lstat()
        fd = Path(f"/proc/{pid}/fd/{row['fd']}").stat()
        require(path.is_absolute() and stat.S_ISREG(identity.st_mode) and identity.st_uid == os.getuid()
                and identity.st_nlink == 1 and (identity.st_dev, identity.st_ino) == (fd.st_dev, fd.st_ino)
                and identity.st_dev == row["device"] and identity.st_ino == row["inode"],
                "initialization lease no longer names its original held regular file")
        key = f"{os.major(identity.st_dev):02x}:{os.minor(identity.st_dev):02x}:{identity.st_ino}"
        require(any(r.split()[1:6] == ["FLOCK", "ADVISORY", "WRITE", str(pid), key] for r in kernel),
                "initialization original lease is not exclusively held by its actual owner")
        paths.add(str(path))
        identities.add((identity.st_dev, identity.st_ino))
        require(row.get("role") in ("host", "cargo", "target", "source") and row["role"] not in roles,
                "initialization lease roles are absent or duplicated")
        roles[row["role"]] = str(path)
    require(len(paths) == len(identities) == 4 and f"/tmp/ay-oom-guard-{os.getuid()}.lock" in paths,
            "initialization is missing the actual machine-wide production lease")
    source = Path(owner.get("source_root", ""))
    require(source.is_absolute() and source.resolve(strict=True) == source,
            "initialization source root is not canonical")
    dot = source / ".git"
    if dot.is_dir() and not dot.is_symlink():
        gitdir = dot.resolve(strict=True)
    else:
        raw = auth.ledger.read_proof_file(dot).decode()
        require(raw.startswith("gitdir: ") and raw.endswith("\n") and raw.count("\n") == 1,
                "initialization source gitdir is malformed")
        named = Path(raw[8:-1])
        gitdir = (source / named).resolve(strict=True) if not named.is_absolute() else named.resolve(strict=True)
    require(roles["source"] == str(gitdir / "build-slot.lock"),
            "initialization source lease is not the canonical worktree lock")
    require(roles["host"] == f"/tmp/ay-oom-guard-{os.getuid()}.lock"
            and roles["cargo"] == owner.get("cargo_lease_path")
            and roles["target"] == owner.get("target_lease_path")
            and roles["source"] == owner.get("source_lease_path"), "initialization resource leases differ from their original owner")


def owner_binding(owner: dict, host: str) -> dict:
    """Read the running owner's real cgroup; a receipt alone grants no budget."""
    require(owner.get("schema") == "trust.linux-root-producer-owner.v2",
            "initialization needs its original bounded native owner")
    started, deadline = owner.get("started_monotonic"), owner.get("deadline_monotonic")
    require(type(started) in (int, float) and type(deadline) in (int, float)
            and math.isfinite(started) and math.isfinite(deadline)
            and 0 < deadline - started <= 86400 and started <= time.monotonic() < deadline,
            "initialization owner is expired or its original whole-run deadline is invalid")
    require(owner.get("host") == host, "initialization owner names another host")
    held_leases(owner)
    rows = Path("/proc/self/cgroup").read_text().splitlines()
    unified = [r[3:] for r in rows if r.startswith("0::")]
    require(len(unified) == 1 and unified[0] == owner.get("control_group")
            and unified[0].endswith(".scope") and Path(unified[0]).name == owner.get("unit"),
            "producer is outside its actual owned scope")
    group = Path("/sys/fs/cgroup") / unified[0].lstrip("/")
    for name, lower, upper in (("memory.max", 1, 32 * 2**30), ("memory.swap.max", 0, 0),
                               ("pids.max", 1, 256)):
        value = (group / name).read_text().strip()
        require(value.isascii() and value.isdigit() and lower <= int(value) <= upper,
                "initialization scope lacks its fixed memory/swap/task bound")
    if '__trust_source_loader__' in globals() and __trust_source_loader__.context is not None:
        live = __trust_source_loader__.context
        result = live.auxiliary('systemd-state','produce_linux_root_seed.owner_binding',
            ['/usr/bin/systemctl','--user','show',owner['unit'],'--property=InvocationID',
             '--property=ControlGroup','--property=RuntimeMaxUSec'],Path.cwd(),
            {'PATH':'/usr/bin:/bin','LC_ALL':'C','HOME':'/',
             'XDG_RUNTIME_DIR':f'/run/user/{os.getuid()}',
             'DBUS_SESSION_BUS_ADDRESS':f'unix:path=/run/user/{os.getuid()}/bus'},
            maximum=65536,seconds=min(10,deadline-time.monotonic()))
        require(result.returncode == 0, 'actual observed owner query failed')
    else:
        result = subprocess.run(["/usr/bin/systemctl", "--user", "show", owner["unit"],
                                 "--property=InvocationID", "--property=ControlGroup", "--property=RuntimeMaxUSec"],
                                env={"PATH": "/usr/bin:/bin", "LC_ALL": "C", "HOME": "/",
                                     "XDG_RUNTIME_DIR": f"/run/user/{os.getuid()}",
                                     "DBUS_SESSION_BUS_ADDRESS": f"unix:path=/run/user/{os.getuid()}/bus"},
                                capture_output=True, text=True, timeout=10, check=True)
    actual = dict(r.split("=", 1) for r in result.stdout.splitlines() if "=" in r)
    require(actual.get("InvocationID") == owner.get("invocation_id")
            and actual.get("ControlGroup") == unified[0]
            and len(actual.get("InvocationID", "")) == 32, "initialization owner identity changed")
    duration = actual.get("RuntimeMaxUSec", "")
    require(duration_seconds(duration) <= deadline - started + 60,
            "initialization scope lacks its original finite runtime bound")
    return {**owner, "actual_cgroup": unified[0], "original_deadline": deadline}


def xpy(source: Path, config: Path, build: Path, host: str, verb: str, *paths: str) -> list[str]:
    return ["/usr/bin/python3", "-I", "-S", "-B", str(source / "x.py"), "--config", str(config),
            verb, "--build-dir", str(build), "--build", host, "--host", host, "--target", host,
            "--stage", "2", "--set", "build.submodules=false", "--set", "rust.channel=trust",
            "--set", "rust.download-rustc=false", "--set", "llvm.download-ci-llvm=false", "-j", "1", *paths]


def phase_config(base: Path, output: Path, compiler: Path, driver: Path, documentation: Path) -> None:
    # The initialization-only override is never an ordinary mint configuration.
    unavailable = output.parent / "unavailable-bootstrap-tool"
    if not unavailable.exists():
        unavailable.write_text("#!/bin/sh\necho 'formatter/linter stage0 is outside this initialization phase' >&2\nexit 125\n")
        unavailable.chmod(0o700)
    formatter = compiler.parent / "trustfmt" if compiler.name == "trustc" else unavailable
    lines = ["# External-only initialization or an unadmitted native candidate.",
             f"include = [{support.toml_string(str(base))}]", "[build]",
             f"rustc = {support.toml_string(str(compiler))}",
             f"cargo = {support.toml_string(str(driver))}",
             f"rustdoc = {support.toml_string(str(documentation))}",
             f"rustfmt = {support.toml_string(str(formatter))}",
             f"cargo-clippy = {support.toml_string(str(unavailable))}", "submodules = false",
             "[rust]", 'channel = "trust"', "download-rustc = false",
             "[llvm]", "download-ci-llvm = false", ""]
    output.write_text("\n".join(lines))


def stage_comparison(work: Path) -> None:
    """Initialization owns this layout; ordinary pack-mint helpers are unchanged."""
    comparison, retained = work / "comparison-build", work / "comparison-self-host"
    require(work.resolve(strict=True) == work and comparison.is_dir() and not comparison.is_symlink()
            and not retained.exists() and not retained.is_symlink(), "initialization comparison staging path is not fresh/owned")
    os.rename(comparison, retained)
    # Both runs read the same authenticated external LLVM. No private LLVM tree
    # is fabricated, and the driver lives in the separate external-build tree.


def restore_comparison(work: Path, output: str = "comparison-ddc") -> None:
    require(output in ("comparison-ddc", "comparison-archive-rebuild"), "unknown initialization comparison output")
    comparison, retained, ddc = work / "comparison-build", work / "comparison-self-host", work / output
    require(work.resolve(strict=True) == work and retained.is_dir() and not retained.is_symlink()
            and not ddc.exists() and not ddc.is_symlink(), "initialization comparison restore path is not owned")
    if comparison.exists() or comparison.is_symlink():
        require(comparison.is_dir() and not comparison.is_symlink(), "initialization DDC output changed its kind")
        os.rename(comparison, ddc)
    os.rename(retained, comparison)


def prepared_artifacts(prepared: Path, work: Path, version: str, host: str, commit: str) -> dict:
    """Install candidates from the exact canonical archives selected by prepare.py."""
    pins_file = prepared / "src-stage0"
    pins = {}
    for line in auth.ledger.read_proof_file(pins_file).decode().splitlines():
        if not line or line.startswith("#"):
            continue
        key, separator, value = line.partition("=")
        require(separator and key not in pins, "prepared canonical pins are malformed or duplicated")
        pins[key] = value
    require(pins.get("compiler_git_commit_hash") == commit
            and pins.get("compiler_version") == version + "-trust", "prepared canonical cohort changed")
    artifacts = support.stage_artifacts(prepared / "bootstrap/trust-stage0/dist" / pins["compiler_date"],
                                        work, version, host, commit, work / "seed-artifacts.json")
    for row in artifacts["artifacts"]:
        relative = "dist/" + pins["compiler_date"] + "/" + row["filename"]
        require(pins.get(relative) == row["sha256"], "selected installer archive differs from its canonical pin")
        installer = work / "unpack" / row["component"] / row["package_root"] / "install.sh"
        row["installer_sha256"] = support.sha256_file(support.canonical_regular_file(installer, "canonical installer"))
    save(work / "canonical-seed-installation-inputs.json", {"stage0_sha256": support.sha256_file(pins_file),
                                                          "artifacts": artifacts})
    return artifacts


def input_capture(args, work: Path) -> dict:
    require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode,
            "native root producer requires Python -I -S -B isolation before input authentication")
    before = auth.check_inputs(args)
    source, orchestration = args.source_root.resolve(), HERE.parent
    commit = auth.git(orchestration, "rev-parse", "HEAD")
    result = {"schema": "trust.linux-root-producer-inputs.v1", "authenticated": before,
              "orchestration": auth.source_snapshot(orchestration, commit),
              "config": support.configuration_closure(source, args.config),
              "tool_inputs": support.mint_tool_manifest(source, args.config)}
    admission = initialization.policy(auth.ledger.read_proof_file)
    result["legacy_cohort_inputs"] = cohort.legacy_inputs(args.legacy_receipt, args.legacy_archives,
                                                         args.legacy_manifest, admission)[0]
    require(admission["source_commit"] == historical.SOURCE, "historical initialization needs its exact source epoch")
    result["bootstrap_contract"] = {"kind": historical.CONTRACT, "source_commit": historical.SOURCE,
                                    "current_toolchain_qualification": False, "modern_native_lane": "unsupported"}
    interpreter = Path(sys.executable).resolve(strict=True)
    result["producer_interpreter"] = {"path": str(interpreter), "sha256": support.sha256_file(interpreter),
                                      "version": sys.version, "isolated": sys.flags.isolated,
                                      "no_site": sys.flags.no_site}
    # The base must name LLVM and every native compiler/linker explicitly.
    config = tomllib.loads(args.config.read_text())
    require(not config.get("include"), "initialization base config must be a single explicit retained file")
    target = config.get("target", {}).get(before["host"], {})
    for key in ("llvm-config", "cc", "cxx", "ar", "ranlib", "linker"):
        named = Path(target.get(key, ""))
        require(named.is_absolute(), "native tool must be an explicit absolute path: " + key)
        path = support.canonical_regular_file(named.resolve(strict=True), "explicit native " + key)
        result.setdefault("native_tools", {})[key] = {"path": str(path), "sha256": support.sha256_file(path)}
    llvm = Path(result["native_tools"]["llvm-config"]["path"]).parent.parent
    result["llvm_tree"] = {"path": str(llvm), "records": support.tree_records(llvm, "native LLVM")}
    require(not any(support.effective_build_table(source, args.config).get(k)
                    for k in support.STAGE0_SELECTORS), "initialization base config overrides a stage0 tool")
    require(support.effective_build_table(source, args.config).get("extended") is True,
            "initialization base must request the full native toolchain")
    return result


def recheck_native_installation(manifest: dict, installed: Path) -> dict:
    actual = support.stage2_manifest(installed)
    projected, _ = initialization.native_projection(manifest)
    require(actual["records"] == projected, "unpacked native artifact differs from its authenticated payload tree")
    return actual


def external_candidate_tools(source: Path) -> tuple[str, ...]:
    paths = ("src/tools/targo", "src/tools/trustdoc", "src/tools/trustfmt")
    require(all((source / path / "Cargo.toml").is_file() for path in paths),
            "authenticated source lacks a native candidate tool producer")
    return paths


class Producer:
    def __init__(self, args, work: Path, owner: dict):
        self.args, self.work, self.owner = args, work, owner
        self.source, self.host = args.source_root.resolve(), owner["host"]
        self.events = []
        self.live = (__trust_source_loader__.context if "__trust_source_loader__" in globals()
                     else globals().get("__trust_live_context__"))
        require("__trust_source_loader__" not in globals() or self.live is not None,
                "source-bound producer has no original observed context")
        self.env = {"PATH": str(work / "safe-bin"), "HOME": str(work / "home"),
                    "TMPDIR": str(work / "tmp"), "RUSTUP_HOME": str(work / "rustup-home"),
                    "XDG_CONFIG_HOME": str(work / "config-home"), "CARGO_HOME": str(work / "cargo-home"),
                    "CARGO_NET_OFFLINE": "true", "CARGO_BUILD_JOBS": "1", "LC_ALL": "C", "LANG": "C",
                    # Exact629 explicitly supports its in-tree older-genesis
                    # shims through this existing API. Both comparison roles
                    # receive it; it creates no Trust seed/proof authority.
                    "TRUST_SEED_STAIRCASE": "1",
                    "TZ": "UTC", "GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": "/dev/null",
                    "SOURCE_DATE_EPOCH": auth.git(self.source, "show", "-s", "--format=%ct", "HEAD")}
        for name in ("home", "tmp", "rustup-home", "config-home"):
            (work / name).mkdir(mode=0o700)
        self.cache_sources = {}
        self.physical_inputs = None

    def bind_cache_sources(self, phase: str) -> None:
        current = {}
        for relative in ("registry/src", "git/checkouts"):
            path = self.work / "cargo-home" / relative
            if path.exists():
                for row in support.tree_records(path, "actual private dependency source"):
                    current[relative + "/" + str(row["path"])] = row
        require(all(current.get(p) == row for p, row in self.cache_sources.items()),
                "an existing actual private dependency source changed during producer")
        self.cache_sources = current
        save(self.work / ("dependency-sources-" + phase + ".json"), current)

    def remaining(self) -> int:
        owner_binding(self.owner, self.host)
        remaining = math.floor(self.owner["deadline_monotonic"] - time.monotonic())
        require(remaining > 0, "original initialization deadline exhausted")
        require(shutil.disk_usage(self.work).free >= 32 * 2**30, "initialization disk reserve exhausted")
        return remaining

    def completion_time(self) -> float:
        self.remaining()
        completed = time.monotonic()
        require(completed < self.owner["deadline_monotonic"], "original initialization deadline exhausted during final capture")
        return completed

    def run(self, name: str, argv: list[str], *, path: Path | None = None, overrides: dict | None = None) -> None:
        require(name in PHASES or name.startswith("install-seed-"), "unexpected initialization phase")
        env = {**self.env, **(overrides or {})}
        if path:
            env["PATH"] = str(path) + ":" + env["PATH"]
        event = {"phase": name, "argv": argv, "cwd": str(self.source), "environment": env,
                 "started_monotonic": time.monotonic(), "deadline_monotonic": self.owner["deadline_monotonic"],
                 "execution_contract": historical.CONTRACT, "current_toolchain_qualification": False}
        if self.physical_inputs is not None and name in ("candidate-self-host", "diverse-ddc"):
            self.physical_inputs.seal("common-self-host" if name == "candidate-self-host" else "common-ddc")
        log = self.work / (name + ".log")
        try:
            with log.open("xb") as output:
                if self.live is None:
                    status = subprocess.run(argv, cwd=self.source, env=env, stdout=output, stderr=subprocess.STDOUT,
                                            timeout=self.remaining(), check=False).returncode
                else:
                    status = self.live.command(name, argv, self.source, env, output, self.remaining())
            event["returncode"] = status
            require(status == 0, f"initialization phase {name} failed with status {status}; retain {log}")
            require(log.stat().st_size <= 64 * 2**20, "initialization phase log exceeded its bound")
        finally:
            event["finished_monotonic"] = time.monotonic()
            event["log"] = str(log)
            event["log_sha256"] = support.sha256_file(log) if log.exists() else None
            self.events.append(event)
            save(self.work / f"phase-{len(self.events):02d}.json", event)
        self.bind_cache_sources(name)

    def build(self, name: str, config: Path, directory: Path, verb: str = "build", *paths: str) -> None:
        self.run(name, xpy(self.source, config, directory, self.host, verb, *paths))

    def execute(self) -> dict:
        args, work, source, host = self.args, self.work, self.source, self.host
        if self.live: self.live.span_begin("inputs-before")
        before = input_capture(args, work)
        if self.live is not None:
            physical = auth.load("trust_live_input_closure", HERE / "seed_input_closure.py")
            self.physical_inputs = physical.CaptureSession(args, work, before, auth,
                self.owner["deadline_monotonic"], self.live)
            self.physical_inputs.seal("before")
        if self.live: self.live.span_end("inputs-before")
        save(work / "inputs-before.json", before)
        safe = support.create_sanitized_path("/usr/bin:/bin", work / "safe-bin")
        save(work / "safe-path.json", safe)
        cache = support.cargo_home_inputs(args.cargo_home, work / "cargo-home")
        save(work / "cargo-home-inputs.json", cache)
        base = work / "bootstrap.base.toml"
        support.copy_authenticated(args.config, base)
        if self.physical_inputs is not None:
            self.physical_inputs.seal("private-import")
        configs = {}
        genesis_build, comparison = work / "external-build", work / "comparison-build"
        genesis = args.genesis_sysroot.resolve()
        phase_config(base, work / "bootstrap.external.toml", genesis / "bin/rustc",
                     genesis / "bin/cargo", genesis / "bin/rustdoc")
        self.build("external-bootstrap", work / "bootstrap.external.toml", genesis_build, "build",
                   "compiler/rustc", "library/std", *external_candidate_tools(source))
        candidate = genesis_build / host / "stage2"
        if self.live: self.live.span_begin("candidate-identity")
        identity = support.compiler_identity(candidate, "unadmitted external-built Trust candidate")
        admission = initialization.policy(auth.ledger.read_proof_file)
        require(identity["lineage"] == "trust" and identity["commit"] == admission["source_commit"]
                and identity["host"] == host, "external bootstrap produced another compiler/source/host")
        candidate_tree = support.stage2_manifest(candidate)
        save(work / "external-candidate-tree.json", candidate_tree)
        driver = support.canonical_regular_file(candidate / "bin/cargo", "candidate's common Targo driver")
        require(support.sha256_file(driver) == support.sha256_file(candidate / "bin/targo"),
                "candidate cargo alias differs from its genuine Targo")
        # This exact source predates --unverified. Its historical identity is
        # source/producer-bound, never a claim to today's native-lane contract.
        self.remaining()
        save(work / "candidate-historical-identity.json",
             historical.candidate(candidate, host, admission["source_version"], self.env, self.owner["deadline_monotonic"]))
        if self.live: self.live.span_end("candidate-identity")
        phase_config(base, work / "bootstrap.self-host.toml", candidate / "bin/trustc", driver,
                     candidate / "bin/trustdoc")
        phase_config(base, work / "bootstrap.ddc.toml", args.ddc_sysroot.resolve() / "bin/rustc", driver,
                     args.ddc_sysroot.resolve() / "bin/rustdoc")
        for name in ("external", "self-host", "ddc"):
            configs[name] = {"path": str(work / f"bootstrap.{name}.toml"),
                             "sha256": support.sha256_file(work / f"bootstrap.{name}.toml")}
        common = {"schema": "trust.genesis-common-inputs.v1", "build_path": str(comparison),
                  "source": before["authenticated"]["source"], "driver": {"path": str(driver),
                  "sha256": support.sha256_file(driver)}, "base_config_sha256": support.sha256_file(base),
                  "cache": cache, "environment": self.env, "native_tools": before["native_tools"],
                  "llvm_tree_sha256": hashlib.sha256(encoded(before["llvm_tree"])).hexdigest()}
        save(work / "common-inputs.json", common)
        self.build("candidate-self-host", work / "bootstrap.self-host.toml", comparison, "build", "compiler/rustc", "library/std")
        left = support.stage2_manifest(comparison / host / "stage2")
        save(work / "stage2-self-host.json", left)
        stage_comparison(work)
        try:
            self.build("diverse-ddc", work / "bootstrap.ddc.toml", comparison, "build", "compiler/rustc", "library/std")
            save(work / "stage2-ddc.json", support.stage2_manifest(comparison / host / "stage2"))
        finally:
            restore_comparison(work)
        support.ddc_compare(work / "stage2-self-host.json", work / "stage2-ddc.json")
        # Dist prunes rustc_private; the following ordinary full build restores it.
        self.build("dist", work / "bootstrap.self-host.toml", comparison, "dist", *support.dist_producer_components(source))
        self.build("full-native-build", work / "bootstrap.self-host.toml", comparison)
        self.build("build-manifest", work / "bootstrap.self-host.toml", comparison, "build", "src/tools/build-manifest")
        manifest_tool = support.find_build_manifest_tool(comparison, host)
        dist = comparison / "dist"
        self.run("channel-manifest", [str(manifest_tool), str(dist), str(dist), admission["source_date"],
                                      "https://trust.invalid", "trust"])
        stage2 = comparison / host / "stage2"
        support.verify_stage2_unchanged(work / "stage2-self-host.json", stage2)
        # Original629 contains this daemon but its bootstrap does not install it.
        target = work / "original-trustd-target"
        # Initialization-only historical bootstrap: this genuine Targo's native
        # build was the non-proving path before the selector existed. Preserve
        # its actual argv and the existing old driver off transport explicitly;
        # this exception never applies to a current native or verified lane.
        self.run("original-trustd", [str(candidate / "bin/targo"), "build", "--release",
                  "--locked", "--offline", "--manifest-path", str(source / "Cargo.toml"),
                  "-p", "trust-router", "--bin", "trustd", "--target", host], path=candidate / "bin",
                 overrides={"RUSTC": str(candidate / "bin/trustc"), "RUSTDOC": str(candidate / "bin/trustdoc"),
                            "CARGO_TARGET_DIR": str(target), "TRUST_NO_VERIFY": "1"})
        if self.live: self.live.span_begin("original-trustd-copy")
        support.copy_authenticated(target / host / "release/trustd", stage2 / "bin/trustd")
        (stage2 / "bin/trustd").chmod(0o755)
        if self.live: self.live.span_end("original-trustd-copy")
        if self.live: self.live.span_begin("rustdoc-alias-copy")
        require(not (stage2 / "bin/rustdoc").exists(), "original source unexpectedly installed its rustdoc alias")
        shutil.copyfile(stage2 / "bin/trustdoc", stage2 / "bin/rustdoc")
        (stage2 / "bin/rustdoc").chmod(0o755)
        if self.live: self.live.span_end("rustdoc-alias-copy")
        self.remaining()
        if self.live: self.live.span_begin("full-native-tools")
        full_tools = historical.native_tools(stage2, initialization.FULL_TOOLS, host, admission["source_version"],
                                             self.env, self.owner["deadline_monotonic"])
        self.completion_time()
        if self.live: self.live.span_end("full-native-tools")
        tools = full_tools["tools"]
        save(work / "full-tools.json", full_tools)
        if self.live: self.live.span_begin("full-native-runtime")
        runtime = linux.closure(stage2, host, [])
        if self.live: self.live.span_end("full-native-runtime")
        require(not runtime["unresolved"], "full native artifact has unresolved ELF runtime inputs")
        save(work / "native-runtime.json", runtime)
        full_tree = support.stage2_manifest(stage2)
        _, source_snapshots = initialization.native_projection(full_tree, source)
        save(work / "full-native-tree.json", full_tree)
        save(work / "native-source-exclusions.json", {"schema": "trust.native-source-snapshots.v1",
                "source_root": str(source), "retained_unpacked_records": source_snapshots,
                "reason": "local bootstrap source-root links; exact shared trust-src ships separately"})
        # Full18 belongs to this native artifact. Stage0 intentionally has no rustdoc.
        native_pack = work / f"trust-native-{admission['source_commit'][:12]}-{host}.tar.xz"
        surface_entries = [name for name in ("bin", "lib", "libexec") if (stage2 / name).is_dir()]
        require("bin" in surface_entries and "lib" in surface_entries, "native artifact has no compiler/std surface")
        self.run("native-pack", ["/usr/bin/tar", "--create", "--xz", "--file", str(native_pack),
                  *("--exclude=" + p for p in initialization.SOURCE_SNAPSHOTS),
                  "--directory", str(stage2), *surface_entries])
        native_pack_sha256 = support.sha256_file(native_pack)
        packaged_files = initialization.native_pack_payloads(native_pack, native_pack_sha256,
                                            auth.ledger.read_proof_file(work / "full-native-tree.json"), host)
        require(all(packaged_files.get(path) == digest for path, digest in tools.items()),
                "native package differs from the actual full tool probes")
        installed_native = work / "native-installation"
        installed_native.mkdir(mode=0o700)
        self.run("native-unpack", ["/usr/bin/tar", "--extract", "--xz", "--no-same-owner", "--same-permissions",
                  "--file", str(native_pack), "--directory", str(installed_native)])
        installed_tree = recheck_native_installation(support.load_json(work / "full-native-tree.json", "full native tree"),
                                                     installed_native)
        self.remaining()
        if self.live: self.live.span_begin("packaged-native-tools")
        packaged_tools = historical.native_tools(installed_native, initialization.FULL_TOOLS, host,
                           admission["source_version"], self.env, self.owner["deadline_monotonic"])
        self.completion_time()
        if self.live: self.live.span_end("packaged-native-tools")
        require(packaged_tools["tools"] == tools, "packaged historical tools differ from their actual probes")
        save(work / "packaged-native-tools.json", packaged_tools)
        require(recheck_native_installation(support.load_json(work / "full-native-tree.json", "full native tree"),
                                             installed_native) == installed_tree, "native tool probes changed the unpacked artifact")
        if self.live: self.live.span_begin("packaged-native-runtime")
        packaged_runtime = linux.closure(installed_native, host, [])
        if self.live: self.live.span_end("packaged-native-runtime")
        require(not packaged_runtime["unresolved"], "actual native package has unresolved ELF runtime inputs")
        save(work / "packaged-native-runtime.json", packaged_runtime)
        save(work / "packaged-native-tree.json", installed_tree)
        prepared = work / "prepared-native-only"
        self.run("prepare-seed", ["/usr/bin/python3", "-I", "-S", "-B",
                 str(HERE.parent / "src/tools/trust-stage0-dist/prepare.py"),
                 "--input-dist", str(dist), "--source-channel", "trust", "--owned-channel", "trust",
                 "--archive-format", "xz", "--stage0-seed-only", "--git-commit-hash", admission["source_commit"],
                 "--date", admission["source_date"], "--dist-server", "file://repo",
                 "--output-root", str(prepared / "bootstrap/trust-stage0"),
                 "--stage0-output", str(prepared / "src-stage0")])
        self.remaining()
        if self.live: self.live.span_begin("cohort-assembly")
        cohort_started = time.monotonic()
        prepared_cohort = work / "prepared-cohort"
        cohort_result = cohort.assemble(prepared, host, args.legacy_receipt, args.legacy_archives,
                                         args.legacy_manifest, args.std_source_archive, prepared_cohort)
        cohort_completed = self.completion_time()
        if self.live: self.live.span_end("cohort-assembly")
        save(work / "cohort-assembly.json", {"started_monotonic": cohort_started,
                "completed_monotonic": cohort_completed, "deadline_monotonic": self.owner["deadline_monotonic"],
                "assembler_sha256": support.sha256_file(HERE / "seed_initialization_cohort.py"),
                "cohort": cohort_result})
        seed_work = work / "seed-installation"
        seed_work.mkdir(mode=0o700)
        artifacts = prepared_artifacts(prepared_cohort, work, admission["source_version"], host, admission["source_commit"])
        if self.physical_inputs is not None:
            self.physical_inputs.seal("installers")
        for row in artifacts["artifacts"]:
            installer = work / "unpack" / row["component"] / row["package_root"] / "install.sh"
            self.run("install-seed-" + row["component"], [str(installer), "--prefix=" + str(seed_work),
                                                         "--disable-ldconfig"])
        self.remaining()
        if self.live: self.live.span_begin("installed-seed-surface")
        surface = historical.installed_seed(seed_work, host, admission["source_version"], self.env,
                                             self.owner["deadline_monotonic"], support)
        self.completion_time()
        if self.live: self.live.span_end("installed-seed-surface")
        save(work / "seed-surface.json", surface)
        matched = support.verify_archives_carry_compared(seed_work, work / "stage2-self-host.json", host)
        if self.live: self.live.span_begin("installed-seed-runtime")
        seed_runtime = linux.closure(seed_work, host, [])
        if self.live: self.live.span_end("installed-seed-runtime")
        require(not seed_runtime["unresolved"], "installed bootstrap archives have unresolved ELF runtime inputs")
        save(work / "seed-runtime.json", seed_runtime)
        support.write_seed_config(base, work / "bootstrap.archive.toml", seed_work, work / "unavailable-tippy")
        configs["archive"] = {"path": str(work / "bootstrap.archive.toml"),
                              "sha256": support.sha256_file(work / "bootstrap.archive.toml")}
        archive_driver = {"path": str(seed_work / "bin/cargo"), "sha256": support.sha256_file(seed_work / "bin/cargo"),
                          "role": "installed archive Targo, distinct from the common DDC driver"}
        save(work / "archive-rebuild-driver.json", archive_driver)
        stage_comparison(work)
        try:
            self.build("archive-rebuild", work / "bootstrap.archive.toml", comparison, "build", "compiler/rustc", "library/std")
            rebuilt = support.stage2_manifest(comparison / host / "stage2")
            save(work / "stage2-archive-rebuild.json", rebuilt)
        finally:
            restore_comparison(work, "comparison-archive-rebuild")
        require(not support.ddc_differences(left, rebuilt), "archive-root rebuild differs from the compared native compiler/std")
        linux.unchanged(runtime)
        linux.unchanged(seed_runtime)
        linux.unchanged(packaged_runtime)
        require(recheck_native_installation(support.load_json(work / "full-native-tree.json", "full native tree"),
                                             installed_native) == installed_tree, "unpacked native package changed during producer")
        support.verify_cargo_home_source(work / "cargo-home-inputs.json")
        support.revalidate_sanitized_path(work / "safe-bin", work / "safe-path.json")
        require(support.stage2_manifest(candidate) == candidate_tree, "common candidate compiler/Targo changed during producer")
        if self.live: self.live.span_begin("inputs-after")
        after = input_capture(args, work)
        if self.physical_inputs is not None:
            self.physical_inputs.seal("after")
        if self.live: self.live.span_end("inputs-after")
        save(work / "inputs-after.json", after)
        require(after == before, "authenticated source/orchestration/oracle/config/native inputs changed during producer")
        require(support.sha256_file(native_pack) == native_pack_sha256, "full native package changed during producer")
        common_inputs_sha256 = support.sha256_file(work / "common-inputs.json")
        native_tree_sha256 = support.sha256_file(work / "full-native-tree.json")
        packaged_tree_sha256 = support.sha256_file(work / "packaged-native-tree.json")
        packaged_runtime_sha256 = support.sha256_file(work / "packaged-native-runtime.json")
        source_exclusions_sha256 = support.sha256_file(work / "native-source-exclusions.json")
        # Final capture work is inside the same original deadline and real owner.
        completed_monotonic = self.completion_time()
        return {"schema": "trust.linux-root-producer-candidate.v1", "passed": True, "host": host,
                "source_commit": admission["source_commit"], "owner": self.owner, "configs": configs,
                "phase_count": len(self.events), "stage2_tree_sha256": left["sha256"],
                "completed_monotonic": completed_monotonic,
                "native_pack": {"path": str(native_pack), "sha256": native_pack_sha256,
                                "surface_entries": surface_entries, "tree_manifest_sha256": native_tree_sha256,
                                "installed_root": str(installed_native), "installed_tree_sha256": packaged_tree_sha256,
                                "installed_runtime_sha256": packaged_runtime_sha256,
                                "source_exclusions_sha256": source_exclusions_sha256},
                "archive_rebuild_driver": archive_driver,
                "archives_carry_compared_files": matched, "common_inputs_sha256": common_inputs_sha256,
                "prepared_native_only": str(prepared),
                "prepared_cohort": str(prepared_cohort),
                "bootstrap_contract": historical.CONTRACT, "current_toolchain_qualification": False,
                "admitted_root_seed": False, "counts_as_trust_stage0_evidence": False,
                "remaining": "closed-owner/retained-command custody and initialized ledger/pin admission"}


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    for name in ("source-root", "std-source-archive", "config", "cargo-home", "work-dir", "owner"):
        result.add_argument("--" + name, type=Path, required=True)
    for name in ("legacy-receipt", "legacy-archives", "legacy-manifest"):
        result.add_argument("--" + name, type=Path, required=True)
    result.add_argument("--host")
    for role in ("genesis", "ddc"):
        for name in ("manifest", "archives", "sysroot"):
            result.add_argument(f"--{role}-{name}", type=Path, required=True)
    return result


def main(argv=None) -> int:
    args = parser().parse_args(argv)
    args.prepared_root = None
    work = args.work_dir.absolute()
    created = False
    result = {"schema": "trust.linux-root-producer-candidate.v1", "passed": False,
              "admitted_root_seed": False, "counts_as_trust_stage0_evidence": False}
    try:
        require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode,
                "native root producer requires Python -I -S -B isolation before input authentication")
        host = support.native_host(args.host)
        owner = owner_binding(json.loads(auth.ledger.read_proof_file(args.owner)), host)
        require(owner.get("cargo_home") == str(args.cargo_home.resolve(strict=True))
                and owner.get("work_dir") == str(work), "producer source-cache/target roots differ from their original owner")
        require(not work.exists() and not work.is_symlink(), "producer work directory must be fresh")
        require(work == work.resolve(strict=False), "producer work path must be canonical")
        require(work.parent.resolve(strict=True).is_relative_to(args.source_root.resolve() / "build"),
                "producer outputs must be inside the isolated authenticated source build directory")
        work.mkdir(mode=0o700)
        created = True
        result = Producer(args, work, owner).execute()
        save(work / "CANDIDATE.json", result)
        print(json.dumps({k: result[k] for k in ("passed", "source_commit", "phase_count", "admitted_root_seed")}))
        return 0
    except (OSError, ValueError, support.WorkflowError, subprocess.SubprocessError) as error:
        result["error"] = str(error)
        if created:
            save(work / "CANDIDATE-NEGATIVE.json", result)
        print(json.dumps(result), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
