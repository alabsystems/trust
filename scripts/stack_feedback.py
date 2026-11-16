#!/usr/bin/env python3
"""Measure an explicit compiler/AY/verifier feedback experiment; never promote it.

Run --help for the required immutable toolchains and owned, frozen source pair.
This is local diagnostic orchestration, not proof or release authority.
"""
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shlex
import shutil
import signal
import stat
import subprocess
import sys
import time

if sys.version_info < (3, 11):
    raise SystemExit("stack_feedback.py requires Python 3.11+; invoke python3.14 explicitly")

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent / "lib"))
import seal_content_identity as seal  # noqa: E402
import stage_receipt_provenance as receipt  # noqa: E402

TARGETS = ("ay_refutation_step_realbody", "ay_refutation_loop_realbody")
FIXTURES = {
    "AY_PB_REFUTATION_PROOF_SRC": "crates/ay-pb/proofs/trust_vc/refutation_step_realbody.rs",
    "AY_PB_REFUTATION_LOOP_PROOF_SRC": "crates/ay-pb/proofs/trust_vc/refutation_loop_realbody.rs",
}
TOOLS = ("trustc", "targo", "targo-trust", "trustd", "ay")
ATERM_CONTEXT = ("ATERM_CHILD", "ATERM_PARENT_SESSION_ID", "ATERM_SESSION_ID", "ATERM_EDGE_TOKENS")
ATERM_ROUTING = ("HOME", "XDG_RUNTIME_DIR", "XDG_STATE_HOME")
SHA = re.compile(r"[0-9a-f]{64}\Z")
COMMIT = re.compile(r"[0-9a-f]{40}\Z")


class Refused(RuntimeError):
    pass


def sha(path: Path) -> str:
    with path.open("rb") as handle:
        return hashlib.file_digest(handle, "sha256").hexdigest()


def load(path: Path):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise Refused(f"duplicate JSON key in {path}: {key}")
            result[key] = value
        return result
    return json.loads(path.read_text(), object_pairs_hook=unique,
                      parse_constant=lambda value: (_ for _ in ()).throw(Refused(value)))


def write(path: Path, value) -> None:
    temporary = path.with_suffix(".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def capture(argv, cwd=None, env=None) -> str:
    done = subprocess.run(argv, cwd=cwd, env=env, capture_output=True, text=True, timeout=60)
    if done.returncode:
        raise Refused(f"{shlex.join(map(str, argv))}: {done.stderr.strip()}")
    return done.stdout


def git(root: Path, *args) -> str:
    env = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
    env.update(GIT_OPTIONAL_LOCKS="0", GIT_NO_REPLACE_OBJECTS="1")
    return capture(["/usr/bin/git", "-c", "core.fsmonitor=false", "-c", "core.untrackedCache=false",
                    "-C", str(root), *args], env=env)


def cargo_checkout_marker(root: Path) -> dict | None:
    """Bind Cargo's empty checkout-complete marker without following a link."""
    path = root / ".cargo-ok"
    try:
        before = path.lstat()
    except FileNotFoundError:
        return None
    def fingerprint(info):
        return (info.st_dev, info.st_ino, info.st_mode, info.st_size,
                info.st_mtime_ns, info.st_ctime_ns)
    if not stat.S_ISREG(before.st_mode) or before.st_size != 0:
        raise Refused(f"invalid Cargo checkout marker: {path}")
    try:
        fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
        try:
            if fingerprint(os.fstat(fd)) != fingerprint(before) or os.read(fd, 1):
                raise Refused(f"Cargo checkout marker changed: {path}")
            if (fingerprint(os.fstat(fd)) != fingerprint(before)
                    or fingerprint(path.lstat()) != fingerprint(before)):
                raise Refused(f"Cargo checkout marker changed: {path}")
        finally:
            os.close(fd)
    except OSError as exc:
        raise Refused(f"cannot bind Cargo checkout marker: {path}: {exc}") from exc
    return {"mode": before.st_mode, "sha256": hashlib.sha256(b"").hexdigest(),
            "stat": list(fingerprint(before))}


def source_identity(root: Path, require_lock: bool = True, *, cargo_checkout: bool = False) -> dict:
    if Path(git(root, "rev-parse", "--show-toplevel").strip()).resolve() != root:
        raise Refused(f"not a repository root: {root}")
    marker = cargo_checkout_marker(root) if cargo_checkout else None
    changes = git(root, "status", "--porcelain=v1", "-z", "--untracked-files=all",
                  "--ignore-submodules=none").split("\0")
    if any(row and not (cargo_checkout and marker is not None and row == "?? .cargo-ok")
           for row in changes):
        raise Refused(f"source is dirty: {root}")
    flags = git(root, "ls-files", "-v", "-z").split("\0")
    if any(line and (line[0].islower() or line[0] == "S") for line in flags):
        raise Refused(f"source has assume-unchanged/skip-worktree paths: {root}")
    rows = [row for row in git(root, "ls-tree", "-r", "-z", "HEAD").split("\0") if row]
    bound_files = {root / row.split("\t", 1)[1] for row in rows
                   if row.split("\t", 1)[0].split()[1] == "blob"}
    digest = hashlib.sha256()
    for row in rows:
        if not row:
            continue
        header, name = row.split("\t", 1)
        mode, kind, oid = header.split()
        path = root / name
        if mode == "160000":
            child = source_identity(path.resolve(), require_lock=False)
            if child["commit"] != oid:
                raise Refused(f"source submodule disagrees with its pin: {path}")
            content = json.dumps(child, sort_keys=True).encode()
        elif mode == "120000":
            if not path.is_symlink():
                raise Refused(f"source symlink changed kind: {path}")
            content = os.fsencode(os.readlink(path))
            # Hashing link text alone does not bind bytes the compiler reads.
            # Only a regular-file target already covered by this Git closure
            # is admitted. Directory links and links into ignored files refuse.
            target = path.resolve(strict=True)
            if target not in bound_files or not target.is_file():
                raise Refused(f"source link escapes the fully bound file closure: {path}")
        elif kind == "blob" and path.is_file() and not path.is_symlink():
            content = path.read_bytes()
            actual_mode = "100755" if path.stat().st_mode & 0o111 else "100644"
            if actual_mode != mode:
                raise Refused(f"source executable mode differs from HEAD: {path}")
        else:
            raise Refused(f"missing or unsupported source input: {path}")
        if kind == "blob":
            blob = b"blob " + str(len(content)).encode() + b"\0" + content
            if hashlib.sha1(blob).hexdigest() != oid:
                raise Refused(f"working source bytes differ from HEAD: {path}")
        digest.update(os.fsencode(name) + b"\0" + content + b"\0")
    result = {"path": str(root), "commit": git(root, "rev-parse", "HEAD").strip(),
            "tree": git(root, "rev-parse", "HEAD^{tree}").strip(), "working_sha256": digest.hexdigest(),
            "lock_sha256": sha(root / "Cargo.lock") if require_lock or (root / "Cargo.lock").is_file() else None}
    if cargo_checkout:
        if cargo_checkout_marker(root) != marker:
            raise Refused(f"Cargo checkout marker changed while binding source: {root}")
        result["cargo_checkout_marker"] = marker
    return result


def path_package_bound(manifest: Path, root: Path) -> None:
    """Refuse ignored package inputs rather than silently omit their bytes."""
    tracked = set(git(root, "ls-files", "-z").split("\0"))
    if manifest.relative_to(root).as_posix() not in tracked:
        raise Refused(f"unbound path-package manifest: {manifest}")
    relative = manifest.parent.relative_to(root).as_posix()
    ignored = git(root, "ls-files", "--others", "--ignored", "--exclude-standard", "-z", "--", relative)
    allowed_configs = {".cargo/config", ".cargo/config.toml"}
    for name in ignored.split("\0"):
        # AY's existing census writes its dependency cache here. A package
        # manifest beneath target/ is still refused by the tracked check above.
        if name and not name.startswith("target/") and name not in allowed_configs:
            raise Refused(f"unbound ignored path-package input: {root / name}")


def dependency_identity(root: Path) -> str:
    """All dependency source content, including workspace peers and ignored files.

    Git administrative files are operational state, never compiler inputs. No
    seal-record exclusions apply to source packages.
    """
    digest = hashlib.sha256()
    bound_files = set()
    links = []
    for directory, dirs, files in os.walk(root, followlinks=False):
        dirs[:] = sorted(name for name in dirs if name != ".git")
        for name in sorted(dirs + [name for name in files if name != ".git"]):
            path = Path(directory) / name
            mode = path.lstat().st_mode
            if path.is_symlink():
                content = os.fsencode(os.readlink(path))
                links.append(path)
            elif stat.S_ISREG(mode):
                content = sha(path).encode()
                bound_files.add(path)
            elif stat.S_ISDIR(mode):
                content = b""
            else:
                raise Refused(f"unsupported dependency source input: {path}")
            digest.update(os.fsencode(path.relative_to(root)) + b"\0" + str(mode).encode() + b"\0" + content + b"\0")
    for path in links:
        if path.resolve(strict=True) not in bound_files:
            raise Refused(f"dependency link escapes the fully bound file closure: {path}")
    return digest.hexdigest()


def tree_stats(root: Path, exclude_git: bool = False) -> dict:
    """Cheap drift check between full seal hashes; never follow escaping links."""
    result = {}
    for directory, dirs, files in os.walk(root, followlinks=False):
        if exclude_git:
            dirs[:] = [name for name in dirs if name != ".git"]
            files = [name for name in files if name != ".git"]
        for name in dirs + files:
            path = Path(directory) / name
            relative = path.relative_to(root).as_posix()
            info = path.lstat()
            if path.is_symlink() and not path.resolve().is_relative_to(root):
                raise Refused(f"toolchain link escapes its immutable root: {path}")
            result[relative] = [info.st_mode, info.st_ino, info.st_size, info.st_mtime_ns, info.st_ctime_ns]
    return result


def process_group_live(pgid: int) -> bool:
    """Zombies are terminal; unlike killpg(0), they need not await init's reap."""
    rows = capture(["/bin/ps", "-axo", "pgid=,stat="]).splitlines()
    return any(len(parts := row.split()) == 2 and int(parts[0]) == pgid
               and not parts[1].startswith("Z") for row in rows)


def supervise(state: Path, cancel: Path, launch_lock: Path, argv: list[str]) -> int:
    """Run *inside* build-slot, retaining admission until our group is terminal.

    The gate and this supervisor are never killed while a workload is active.
    Cancellation is durable even if admission has not happened yet. The launch
    lock closes the race between a queued cancellation and starting a workload.
    """
    stopped = False

    def stop(_signal, _frame):
        nonlocal stopped
        stopped = True

    for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
        signal.signal(sig, stop)
    record = {"supervisor_pid": os.getpid(), "status": "starting", "terminal_confirmed": False}
    process = None
    try:
        with launch_lock.open("a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            if stopped or cancel.exists():
                record.update(status="cancelled_before_launch", terminal_confirmed=True)
                write(state, record)
                return 124
            process = subprocess.Popen(argv, start_new_session=True)
            record.update(status="running", workload_pid=process.pid, workload_pgid=process.pid)
            write(state, record)
        while process.poll() is None and not stopped and not cancel.exists():
            try:
                process.wait(timeout=0.1)
            except subprocess.TimeoutExpired:
                pass
        interrupted = stopped or cancel.exists()
        # Also clean descendants left by a launcher which exited early. Only
        # the new group created above is addressed, never a shared daemon PID.
        if interrupted or process_group_live(process.pid):
            record["term_sent"] = True
            try:
                os.killpg(process.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            write(state, record)
            deadline = time.monotonic() + 2
            while process_group_live(process.pid) and time.monotonic() < deadline:
                try:
                    process.wait(timeout=0.1)
                except subprocess.TimeoutExpired:
                    pass
                time.sleep(0.05)
            if process_group_live(process.pid):
                record["kill_sent"] = True
                os.killpg(process.pid, signal.SIGKILL)
            process.wait()
            # Do not let build-slot release its lease until every member of the
            # owned group is confirmed terminal, including TERM-ignoring children.
            while process_group_live(process.pid):
                time.sleep(0.05)
        rc = process.wait()
        record.update(status="interrupted" if interrupted else "completed",
                      workload_returncode=rc, terminal_confirmed=True)
        write(state, record)
        return 124 if interrupted else (128 - rc if rc < 0 else rc)
    except BaseException:
        # An internal supervisor failure must not strand admitted computation.
        if process is not None:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait()
            while process_group_live(process.pid):
                time.sleep(0.05)
        record.update(status="supervisor_failed", terminal_confirmed=True)
        write(state, record)
        raise


def properties(path: Path) -> dict:
    result = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith("#"):
            continue
        key, value = line.split("=", 1)
        if key in result:
            raise Refused(f"duplicate PROVENANCE key: {key}")
        result[key] = value
    return result


def toolchain_identity(root: Path, expected_commit: str | None, explicit_receipt: Path | None) -> dict:
    if explicit_receipt is not None and not explicit_receipt.is_file():
        raise Refused(f"candidate receipt missing: {explicit_receipt}; no completed candidate was supplied")
    if root.is_symlink() or root != root.resolve() or "build" in root.parts:
        raise Refused(f"toolchain must be an immutable canonical seal outside build/: {root}")
    provenance = properties(root / "PROVENANCE")
    commit = provenance.get("reported_commit", "")
    if not COMMIT.fullmatch(commit) or (expected_commit is not None and commit != expected_commit):
        raise Refused(f"toolchain commit does not match the requested candidate: {commit}")
    if provenance.get("sealed_by") != "scripts/promote-toolchain.sh":
        raise Refused(f"toolchain has no promoter seal record: {root}")
    if provenance.get("artifact_content_scope") != seal.SCOPE:
        raise Refused(f"toolchain lacks the complete seal-content identity: {root}")
    content = seal.identity(root)[0]
    if provenance.get("artifact_content_sha256") != content:
        raise Refused(f"toolchain content differs from sealed PROVENANCE: {root}")
    stats = tree_stats(root)
    for name in TOOLS:
        path = root / "bin" / name
        if path.is_symlink() or not path.is_file() or not os.access(path, os.X_OK):
            raise Refused(f"missing exact executable: {path}")
    if explicit_receipt is not None:
        if sha(explicit_receipt) != sha(root / receipt.RECEIPT_NAME):
            raise Refused("explicit candidate receipt differs from the receipt sealed with the candidate")
        receipt.lines(root, commit)  # canonical strict schema and executable-byte validator
        data = load(explicit_receipt)
        lineage = data.get("source_lineage", {})
        closure = lineage.get("closure_sha256", "")
        if (data.get("status") not in receipt.RELEASE_STATUSES or type(data.get("stage")) is not int
                or data["stage"] < 2
                or data.get("source_tree_clean") is not True
                or lineage.get("schema") != "trust.source-lineage.v1"
                or lineage.get("status") != "immutable_release" or lineage.get("source_tree_clean") is not True
                or lineage.get("errors") != []
                or lineage.get("stable_across_build") is not True or not SHA.fullmatch(closure)
                or lineage.get("pre_build_closure_sha256") != closure
                or lineage.get("post_build_closure_sha256") != closure):
            raise Refused("candidate receipt does not bind a clean, stable, completed Trust-from-Trust source closure")
        root_rows = [row for row in lineage.get("repositories", []) if row.get("path") == "."]
        if len(root_rows) != 1 or root_rows[0].get("head") != commit:
            raise Refused("candidate receipt source closure does not identify the compiler's root commit")
        names = {row["name"]: row for row in data["tools"]}
        for name in TOOLS[1:]:
            if names.get(name, {}).get("path") != f"{data['stage_root']}/bin/{name}":
                raise Refused(f"candidate receipt does not bind the shipped {name}")
    clean_env = {"PATH": "/usr/bin:/bin", "HOME": str(Path.home())}
    binary = root / "bin" / "trustc"
    version = capture([str(binary), "-vV"], env=clean_env)
    if re.findall(r"^commit-hash: (.+)$", version, re.M) != [commit] or "trust:" not in version:
        raise Refused("compiler does not report the sealed Trust commit")
    if Path(capture([str(binary), "--print", "sysroot"], env=clean_env).strip()).resolve() != root:
        raise Refused("compiler resolves a different sysroot")
    capture([str(root / "bin" / "targo"), "--unverified", "--version"], env=clean_env)
    if tree_stats(root) != stats:
        raise Refused("toolchain changed during identity probes")
    return {"path": str(root), "commit": commit, "content_sha256": content,
            "provenance_sha256": sha(root / "PROVENANCE"), "version": version,
            "receipt_sha256": sha(explicit_receipt) if explicit_receipt is not None else None,
            "receipt_path": str(explicit_receipt) if explicit_receipt is not None else None}


def timing(stderr: str) -> dict:
    """Per-process /usr/bin/time values, never cumulative RUSAGE_CHILDREN."""
    patterns = ({"user_seconds": r"([\d.]+)\s+user", "system_seconds": r"([\d.]+)\s+sys",
                 "peak_rss_bytes": r"(\d+)\s+maximum resident set size"}
                if sys.platform == "darwin" else
                {"user_seconds": r"User time \(seconds\): ([\d.]+)",
                 "system_seconds": r"System time \(seconds\): ([\d.]+)",
                 "peak_rss_kib": r"Maximum resident set size \(kbytes\): (\d+)"})
    result = {key: float(found.group(1)) for key, pattern in patterns.items()
              if (found := re.search(pattern, stderr))}
    if sys.platform == "darwin":
        found = re.search(r"([\d.]+)\s+real", stderr)
        if found:
            result["execution_wall_seconds"] = float(found.group(1))
    else:
        found = re.search(r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)", stderr)
        if found:
            seconds = 0.0
            for part in found.group(1).split(":"):
                seconds = seconds * 60 + float(part)
            result["execution_wall_seconds"] = seconds
    return result


def census_failures(census: dict) -> list[tuple[str, str]]:
    ledger = census.get("obligation_ledger", {})
    failures = []
    if (ledger.get("denominator_is_complete") is not True
            or type(ledger.get("vcgen_truncated_functions")) is not int
            or ledger["vcgen_truncated_functions"] != 0):
        failures.append(("census-completeness", "AY denominator is incomplete, truncated or missing completeness evidence"))
    if census.get("strict_lane", {}).get("verdict_census_matches_advisory") is not True:
        failures.append(("census-lane-agreement", "strict/advisory verdict censuses diverge or agreement evidence is missing"))
    return failures


class Feedback:
    def __init__(self, args):
        self.args = args
        self.out = args.out.resolve()
        self.sources = {"ay": args.ay.resolve(), "trust_vc": args.trust_vc.resolve()}
        self.roots = {"control": args.control, "candidate": args.candidate}
        # Admission precedes *all* filesystem writes, including refusal records.
        # Resolve existing ancestors so an output alias cannot enter an input.
        for root in [*self.sources.values(), *self.roots.values()]:
            if self.out.is_relative_to(root.resolve()):
                raise Refused("results must be outside every source/toolchain input")
        self.out.mkdir(parents=True, exist_ok=False)
        self.report = {"schema": "trust.stack-feedback.v1", "status": "preflight",
                       "claim_scope": "local diagnostic measurements; no proof, release or self-improvement claim",
                       "phases": [], "failures": [], "platform": platform.platform(),
                       "commands": {}, "inputs": {}}
        self.envs = {}
        self.frozen = {}
        self.stats = {}
        self.dependencies = {}
        self.path_packages = {}
        self.inventories = {}
        self.aterm_cli = None
        self.save()

    def save(self):
        write(self.out / "result.json", self.report)

    def fail(self, phase: str, reason: str):
        self.report["failures"].append({"phase": phase, "reason": reason})
        self.save()

    def preflight(self):
        if sys.platform not in ("linux", "darwin"):
            raise Refused("native resource measurement requires Linux or macOS /usr/bin/time")
        if not COMMIT.fullmatch(self.args.candidate_commit):
            raise Refused("--candidate-commit must be a full lowercase Git object ID")
        if not self.args.build_slot.is_absolute():
            raise Refused("--build-slot must be absolute")
        if os.environ.get("CARGO_HOME") and not Path(os.environ["CARGO_HOME"]).is_absolute():
            raise Refused("CARGO_HOME must be absolute so both source checkouts resolve the same configuration")
        if self.sources["ay"] == self.sources["trust_vc"]:
            raise Refused("AY and trust-vc must be distinct source repositories")
        if any(os.environ.get(key) for key in ATERM_CONTEXT):
            explicit_cli = "BUILD_SLOT_ATERM_CLI" in os.environ
            cli = os.environ["BUILD_SLOT_ATERM_CLI"] if explicit_cli else shutil.which("aterm")
            if cli is not None:
                path = Path(cli)
                if explicit_cli and (not path.is_absolute() or not path.is_file()
                                     or not os.access(path, os.X_OK)):
                    raise Refused("explicit aterm discovery executable unavailable")
                path = path.resolve()
                self.aterm_cli = {"path": str(path), "sha256": sha(path)}
        self.report["inputs"]["aterm_cli"] = self.aterm_cli
        # Check candidate first: a failed build must not wait for any experiment.
        for label in ("candidate", "control"):
            expected = self.args.candidate_commit if label == "candidate" else None
            explicit = self.args.candidate_receipt if label == "candidate" else None
            identity = toolchain_identity(self.roots[label], expected, explicit)
            self.report["inputs"][label] = identity
            self.stats[label] = tree_stats(self.roots[label])
            env = {key: os.environ[key] for key in (*ATERM_ROUTING, "USER", "TMPDIR", "SSH_AUTH_SOCK", "CARGO_HOME", *ATERM_CONTEXT)
                   if key in os.environ}
            env.update(PATH=f"{self.roots[label] / 'bin'}:{Path(sys.executable).parent}:/opt/homebrew/bin:/usr/bin:/bin:/usr/sbin:/sbin",
                       LC_ALL="C", RUSTC=str(self.roots[label] / "bin" / "trustc"),
                       TRUST_TOOLCHAIN_BIN=str(self.roots[label] / "bin"),
                       TRUST_VC_DISABLE_VC_CACHE="1", HEAVY_GATE="none", PYTHONDONTWRITEBYTECODE="1")
            env.update({key: str(self.sources["ay"] / path) for key, path in FIXTURES.items()})
            if self.aterm_cli is not None:
                env["BUILD_SLOT_ATERM_CLI"] = self.aterm_cli["path"]
            self.envs[label] = env
        self.frozen = {name: source_identity(path) for name, path in self.sources.items()}
        self.report["inputs"]["sources"] = self.frozen
        # Cargo also reads configuration outside the source repositories. Bind
        # those files without copying their potentially credential-bearing text.
        configs = set()
        for root in self.sources.values():
            for ancestor in (root, *root.parents):
                configs.update(ancestor / ".cargo" / name for name in ("config", "config.toml"))
        cargo_home = Path(os.environ.get("CARGO_HOME", str(Path.home() / ".cargo")))
        configs.update(cargo_home / name for name in ("config", "config.toml"))
        self.configs = sorted(configs)
        self.config_identity = {str(path): sha(path) if path.is_file() else None for path in self.configs}
        self.report["inputs"]["ambient_cargo_config_sha256"] = self.config_identity
        self.report["inputs"]["build_slot"] = {"path": str(self.args.build_slot.resolve()),
                                                "sha256": sha(self.args.build_slot.resolve())}
        if not os.access(self.args.build_slot, os.X_OK):
            raise Refused("build-slot must be executable")
        self.runner_files = [Path(__file__).resolve(), Path(seal.__file__).resolve(),
                             Path(receipt.__file__).resolve()]
        self.spec_source = self.args.trust_spec_source.resolve()
        self.spec_identity = sha(self.spec_source)
        self.report["inputs"]["trust_spec_source"] = {"path": str(self.spec_source),
                                                      "sha256": self.spec_identity}
        for env in self.envs.values():
            env["TRUST_SPEC_SRC"] = str(self.spec_source)
        self.runner_identity = {str(path): sha(path) for path in self.runner_files}
        self.report["inputs"]["runner_sha256"] = self.runner_identity
        for path in FIXTURES.values():
            if (not (self.sources["ay"] / path).is_file()
                    or path not in git(self.sources["ay"], "ls-files", "-z").split("\0")):
                raise Refused(f"missing or unbound AY proof fixture: {path}")
        self.check_inputs()

    def check_inputs(self):
        if self.aterm_cli is not None:
            path = Path(self.aterm_cli["path"])
            try:
                unchanged = os.access(path, os.X_OK) and sha(path) == self.aterm_cli["sha256"]
            except OSError:
                unchanged = False
            if not unchanged:
                raise Refused("aterm discovery executable changed")
        for label, root in self.roots.items():
            if tree_stats(root) != self.stats[label]:
                raise Refused(f"toolchain input changed: {label}")
        if sha(self.args.candidate_receipt) != self.report["inputs"]["candidate"]["receipt_sha256"]:
            raise Refused("explicit completed candidate receipt changed")
        for name, root in self.sources.items():
            if source_identity(root) != self.frozen[name]:
                raise Refused(f"frozen source changed: {name}")
        current = {str(path): sha(path) if path.is_file() else None for path in self.configs}
        if current != self.config_identity:
            raise Refused("ambient Cargo configuration changed")
        slot = self.report["inputs"]["build_slot"]
        if sha(self.args.build_slot.resolve()) != slot["sha256"]:
            raise Refused("build-slot executable changed")
        if {str(path): sha(path) for path in self.runner_files} != self.runner_identity:
            raise Refused("feedback runner or canonical identity readers changed")
        if sha(self.spec_source) != self.spec_identity:
            raise Refused("explicit trust-spec measurement scaffold changed")
        for path, info in self.dependencies.items():
            if tree_stats(Path(path), exclude_git=True) != info["stats"]:
                raise Refused(f"dependency source bytes changed: {path}")
            if info.get("git") and source_identity(Path(path), require_lock=False, cargo_checkout=True) != info["git"]:
                raise Refused(f"Git dependency source closure changed: {path}")
        for manifest, root in self.path_packages.items():
            path_package_bound(Path(manifest), root)

    def native_identity(self, executable: Path, label: str) -> dict:
        if (executable.is_symlink() or not executable.is_file()
                or not executable.resolve().is_relative_to(self.out / f"{label}-target")):
            raise Refused("consumer executable escapes its run-owned build outputs")
        return {"path": str(executable), "sha256": sha(executable)}

    def job(self, name: str, argv: list[str], cwd: Path, label: str, metric: str,
            native_executable: dict | None = None) -> dict:
        self.check_inputs()
        if native_executable is not None and self.native_identity(Path(native_executable["path"]), label) != native_executable:
            raise Refused(f"native test executable changed before phase: {name}")
        state = self.out / f"{name}.process.json"
        cancel = self.out / f"{name}.cancel"
        launch_lock = self.out / f"{name}.launch.lock"
        command = [str(self.args.build_slot), "--", sys.executable, str(Path(__file__).resolve()),
                   "_supervise", str(state), str(cancel), str(launch_lock), "--", *argv]
        record = {"name": name, "argv": command, "payload_argv": argv,
                  "process_custody": str(state), "cwd": str(cwd), "metric_scope": metric,
                  "status": "planned", "stdout": str(self.out / f"{name}.stdout"),
                  "stderr": str(self.out / f"{name}.stderr")}
        if native_executable is not None:
            record["native_executable"] = native_executable
        self.report["phases"].append(record)
        self.report["commands"][name] = shlex.join(command)
        env = {**self.envs[label], "CARGO_TARGET_DIR": str(self.out / f"{label}-target")}
        if "ratchet" in name:
            env["TRUST_RATCHET_OUT"] = str(self.out / f"{label}-ratchet")
            if label == "candidate":
                env["TRUST_RATCHET_BASELINE"] = str(self.out / "control-ratchet/current.json")
        record["environment"] = {key: value for key, value in env.items()
                                 if key not in (*ATERM_ROUTING, "USER", "SSH_AUTH_SOCK", *ATERM_CONTEXT)}
        self.save()
        if self.args.action == "plan":
            return record
        record["status"] = "running"
        self.save()
        started = time.monotonic()
        with open(record["stdout"], "wb") as stdout, open(record["stderr"], "wb") as stderr:
            process = subprocess.Popen(command, cwd=cwd, env=env, stdout=stdout, stderr=stderr,
                                       start_new_session=True)
            try:
                rc = process.wait(timeout=self.args.timeout)
                record["status"] = "passed" if rc == 0 else "failed"
            except (subprocess.TimeoutExpired, KeyboardInterrupt):
                with launch_lock.open("a") as lock:
                    fcntl.flock(lock, fcntl.LOCK_EX)
                    cancel.touch()
                    launched = state.is_file() and "workload_pid" in load(state)
                if not launched:
                    # No workload can now launch: the supervisor checks cancel
                    # under this same lock. It is safe to stop a queued gate.
                    try:
                        os.killpg(process.pid, signal.SIGTERM)
                    except ProcessLookupError:
                        pass
                    try:
                        process.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        try:
                            os.killpg(process.pid, signal.SIGKILL)
                        except ProcessLookupError:
                            pass
                # For admitted work only the inner supervisor escalates signals.
                # It holds build-slot until its workload group is terminal.
                process.wait()
                rc = process.returncode
                record["status"] = "interrupted"
            record.update(returncode=rc, orchestration_seconds_including_admission=time.monotonic() - started)
        if state.is_file():
            record["process"] = load(state)
            if record["process"].get("terminal_confirmed") is not True:
                self.fail(name, "owned workload termination was not confirmed")
        elif record["status"] != "interrupted":
            self.fail(name, "admitted job did not retain its process custody record")
        record["stdout_sha256"] = sha(Path(record["stdout"]))
        record["stderr_sha256"] = sha(Path(record["stderr"]))
        if metric == "native_test_execution":
            record["resources"] = timing(Path(record["stderr"]).read_text(errors="replace"))
            if len(record["resources"]) != 4:
                self.fail(name, "per-process CPU/wall/RSS resource measurements are incomplete")
        if record["status"] != "passed":
            self.fail(name, f"{record['status']} (actual exit {rc}); see retained stdout/stderr")
        if native_executable is not None:
            record["native_executable_after"] = self.native_identity(Path(native_executable["path"]), label)
            if record["native_executable_after"] != native_executable:
                self.save()
                raise Refused(f"native test executable changed during phase: {name}")
        self.save()
        self.check_inputs()
        if record["status"] == "interrupted":
            raise Refused(f"phase interrupted: {name}; no later jobs started")
        return record

    def metadata(self, label: str, subject: str) -> dict | None:
        root = self.sources[subject]
        row = self.job(f"{label}.{subject}.metadata", [str(self.roots[label] / "bin/targo"),
                       "metadata", "--locked", "--offline", "--format-version", "1"],
                       root, label, "dependency_resolution")
        if row["status"] != "passed":
            return None
        data = load(Path(row["stdout"]))
        for package in data["packages"]:
            if package["source"] is None:
                manifest = Path(package["manifest_path"]).resolve()
                if not any(manifest.is_relative_to(path) for path in self.sources.values()):
                    raise Refused(f"unfrozen path dependency: {manifest}")
                if package["name"].startswith("ay") and not manifest.is_relative_to(self.sources["ay"]):
                    raise Refused(f"consumer resolved a different AY source: {manifest}")
                source_root = next(path for path in self.sources.values() if manifest.is_relative_to(path))
                path_package_bound(manifest, source_root)
                self.path_packages[str(manifest)] = source_root
            elif package["name"].startswith("ay"):
                raise Refused(f"AY dependency resolved from a Git/registry source instead of the frozen AY: {package['id']}")
            if package["source"] is not None:
                path = Path(package["manifest_path"]).resolve().parent
                git_identity = None
                if package["source"].startswith("git+"):
                    path = Path(git(path, "rev-parse", "--show-toplevel").strip()).resolve()
                    git_identity = source_identity(path, require_lock=False, cargo_checkout=True)
                    if package["source"].rsplit("#", 1)[-1] != git_identity["commit"]:
                        raise Refused(f"Git dependency checkout differs from resolved revision: {path}")
                if str(path) not in self.dependencies:
                    self.dependencies[str(path)] = {"sha256": dependency_identity(path),
                                                     "stats": tree_stats(path, exclude_git=True),
                                                     "git": git_identity}
        self.report["inputs"]["dependency_source_sha256"] = {
            path: data["sha256"] for path, data in self.dependencies.items()}
        identity = {"packages": sorted(data["packages"], key=lambda row: row["id"]),
                    "resolve": data["resolve"], "workspace_members": sorted(data["workspace_members"])}
        write(self.out / f"{label}.{subject}.dependencies.json", identity)
        return identity

    def execute(self):
        metadata = {}
        for label in self.roots:
            for subject in self.sources:
                metadata[label, subject] = self.metadata(label, subject)
        if self.args.action == "run":
            for subject in self.sources:
                before, after = metadata["control", subject], metadata["candidate", subject]
                if before is None or after is None or before != after:
                    raise Refused(f"{subject}: control/candidate dependency identities are missing or differ")
        for label in self.roots:
            self.job(f"{label}.ay-ratchet", ["bash", "scripts/ci/trust_verification_ratchet_gate.sh"],
                     self.sources["ay"], label, "combined_dependency_build_and_verification")
            command = [str(self.roots[label] / "bin/targo"), "--unverified", "test", "--locked",
                       "-p", "trust-vc-core", "--no-run", "--message-format=json"]
            for target in TARGETS:
                command.extend(["--test", target])
            built = self.job(f"{label}.consumer-build", command, self.sources["trust_vc"], label,
                             "consumer_compilation_only")
            if built["status"] == "passed":
                executables = {}
                for line in Path(built["stdout"]).read_text().splitlines():
                    artifact = json.loads(line)
                    target = artifact.get("target", {}).get("name")
                    if artifact.get("reason") == "compiler-artifact" and target in TARGETS and artifact.get("executable"):
                        executable = Path(artifact["executable"])
                        identity = self.native_identity(executable, label)
                        if target in executables:
                            raise Refused(f"{label}: ambiguous native test executable for {target}")
                        if any(executable.samefile(item["path"]) for item in executables.values()):
                            raise Refused(f"{label}: proof targets identify the same native executable")
                        executables[target] = identity
                if set(executables) != set(TARGETS):
                    raise Refused(f"{label}: compiler artifacts do not identify both native test executables")
                self.report["inputs"].setdefault("native_test_executables", {})[label] = executables
                self.save()
                for target, identity in executables.items():
                    executable = Path(identity["path"])
                    listing = self.job(f"{label}.{target}.inventory", [str(executable), "--list"],
                                       self.sources["trust_vc"], label, "test_inventory", native_executable=identity)
                    cases = [line[:-6] for line in Path(listing["stdout"]).read_text().splitlines()
                             if line.endswith(": test")]
                    if listing["status"] != "passed" or not cases or len(set(cases)) != len(cases):
                        raise Refused(f"{label}: missing or ambiguous native test inventory: {target}")
                    listing["cases"] = cases
                    if target in self.inventories and sorted(cases) != self.inventories[target]:
                        raise Refused(f"control/candidate native test denominator differs: {target}")
                    self.inventories[target] = sorted(cases)
                    for repetition in range(self.args.repetitions):
                        argv = ["/usr/bin/time", "-l" if sys.platform == "darwin" else "-v",
                                str(executable), "--test-threads=1"]
                        sample = self.job(f"{label}.{target}.sample-{repetition + 1}", argv,
                                          self.sources["trust_vc"], label, "native_test_execution", native_executable=identity)
                        text = Path(sample["stdout"]).read_text()
                        expected = f"test result: ok. {len(cases)} passed; 0 failed; 0 ignored; 0 measured; 0 filtered out;"
                        if sample["status"] == "passed" and expected not in text:
                            self.fail(sample["name"], "native test count/expectations differ from the full inventory")
        if self.args.action == "run":
            expected_tree = git(self.sources["ay"], "rev-parse", "HEAD:crates/ay-proof-common").strip()
            complete_censuses = True
            for label in self.roots:
                path = self.out / f"{label}-ratchet/current.json"
                census = load(path)
                metadata = census.get("metadata", {})
                verdicts = census.get("verdicts", {})
                obligation_ledger = census.get("obligation_ledger", {})
                ledger = obligation_ledger.get("entries", {})
                strict = census.get("strict_lane", {})
                self.report.setdefault("census", {})[label] = {
                    "path": str(path), "sha256": sha(path), "verdicts": verdicts,
                    "obligation_ledger": {key: obligation_ledger.get(key) for key in (
                        "denominator_is_complete", "vcgen_truncated_functions", "vcgen_truncated_function_names")},
                    "strict_lane": {"verdict_census_matches_advisory": strict.get("verdict_census_matches_advisory")}}
                self.save()
                if (census.get("schema_version") != "ay.trust.ratchet.v3"
                        or metadata.get("crate_sources_tree") != expected_tree
                        or metadata.get("git_commit") != self.frozen["ay"]["commit"]
                        or metadata.get("crate_sources_clean_at_commit") is not True
                        or verdicts.get("obligations", 0) <= 0 or not isinstance(ledger, dict)
                        or len(ledger) != verdicts["obligations"]):
                    raise Refused(f"{label}: ratchet census is empty or bound to different AY sources")
                for phase, reason in census_failures(census):
                    self.fail(f"{label}.{phase}", reason)
                    complete_censuses = False
            if not complete_censuses:
                return  # Retain evidence, but never compare rates over incomplete censuses.
            # Use AY's own identity-aware accounting; write only a run artifact.
            code = ("import importlib.util,json,sys; "
                    "s=importlib.util.spec_from_file_location('accounting',sys.argv[1]); "
                    "m=importlib.util.module_from_spec(s); s.loader.exec_module(m); "
                    "b=json.load(open(sys.argv[2])); c=json.load(open(sys.argv[3])); "
                    "assert b['metadata']['crate_sources_tree']==c['metadata']['crate_sources_tree']; "
                    "a=m.accounting(b,c); r=m.regressions(a,b,c); "
                    "json.dump({'accounting':a,'regressions':r},open(sys.argv[4],'w'),indent=2); sys.exit(bool(r))")
            self.job("proof-comparison", [sys.executable, "-c", code,
                     str(self.sources["ay"] / "scripts/trust_ratchet_accounting.py"),
                     str(self.out / "control-ratchet/current.json"),
                     str(self.out / "candidate-ratchet/current.json"), str(self.out / "proof-comparison.json")],
                     self.sources["ay"], "candidate", "obligation_identity_accounting")

    def run(self) -> int:
        try:
            self.preflight()
            self.report["status"] = "planned" if self.args.action == "plan" else "measuring"
            self.execute()
            self.check_inputs()
            for label, root in self.roots.items():
                if seal.identity(root)[0] != self.report["inputs"][label]["content_sha256"]:
                    raise Refused(f"complete toolchain content changed: {label}")
            for path, info in self.dependencies.items():
                if dependency_identity(Path(path)) != info["sha256"]:
                    raise Refused(f"complete dependency content changed: {path}")
            self.report["status"] = ("planned" if self.args.action == "plan" else
                                     "measured_with_failures" if self.report["failures"] else "measured")
        except KeyboardInterrupt:
            self.fail("interrupted", "experiment interrupted; inspect retained phase statuses")
            self.report["status"] = "refused"
        except (Refused, receipt.StageReceiptError, seal.SealContentError, OSError, ValueError,
                KeyError, TypeError, AttributeError, subprocess.SubprocessError) as error:
            self.fail("input-admission-or-drift", str(error))
            self.report["status"] = "refused"
        self.save()
        print(f"{self.report['status']}: {self.out / 'result.json'}")
        return 1 if self.report["failures"] else 0


def main(argv=None) -> int:
    if argv is None:
        argv = sys.argv[1:]
    if argv[:1] == ["_supervise"]:
        if len(argv) < 6 or argv[4] != "--":
            raise Refused("invalid internal supervisor invocation")
        return supervise(Path(argv[1]), Path(argv[2]), Path(argv[3]), argv[5:])
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("plan", "run"))
    parser.add_argument("--control", type=Path, required=True, help="canonical immutable control sysroot")
    parser.add_argument("--candidate", type=Path, required=True, help="canonical immutable candidate sysroot")
    parser.add_argument("--candidate-receipt", type=Path, required=True, help="explicit completed recreator v2 receipt")
    parser.add_argument("--candidate-commit", required=True, help="expected clean compiler source commit")
    parser.add_argument("--ay", type=Path, required=True, help="owned frozen clean AY source checkout")
    parser.add_argument("--trust-vc", type=Path, required=True, help="owned frozen clean verifier source checkout")
    parser.add_argument("--trust-spec-source", type=Path, required=True,
                        help="explicit single-file trust-spec scaffold consumed by the AY census")
    parser.add_argument("--out", type=Path, required=True, help="new retained results directory outside inputs")
    parser.add_argument("--build-slot", type=Path, default=Path(__file__).resolve().with_name("build-slot"))
    parser.add_argument("--timeout", type=int, default=3600, help="per-phase wall containment, seconds")
    parser.add_argument("--repetitions", type=int, default=3)
    args = parser.parse_args(argv)
    if args.timeout < 1 or args.repetitions < 1:
        parser.error("timeout and repetitions must be positive")
    try:
        return Feedback(args).run()
    except (Refused, OSError) as error:
        # Forbidden output placement is refused without writing into an input.
        print(f"refused before output creation: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
