#!/bin/sh
""":"
for candidate in python3.14 python3.13 python3.12 python3.11 python3; do
    if command -v "$candidate" >/dev/null 2>&1 \
        && "$candidate" -c 'import sys; raise SystemExit(sys.version_info < (3, 11))' 2>/dev/null; then
        exec "$candidate" "$0" "$@"
    fi
done
echo "daily_toolchain_stage.py requires Python 3.11+ (tomllib)" >&2
exit 2
":"""
from __future__ import annotations
import os as _floor_os
import shutil as _floor_shutil
import sys as _floor_sys

# Trust: python floor, second half. `python3 daily_toolchain_stage.py` reads the sh block above
# as a string, so an old `python3` (3.9 on macOS CommandLineTools) re-execs here.
if __name__ == "__main__" and _floor_sys.version_info < (3, 11):
    for _floor_candidate in ("python3.14", "python3.13", "python3.12", "python3.11"):
        _floor_path = _floor_shutil.which(_floor_candidate)
        if _floor_path:
            _floor_argv = [_floor_path, _floor_os.path.abspath(__file__), *_floor_sys.argv[1:]]
            _floor_os.execv(_floor_path, _floor_argv)
    _floor_sys.exit("daily_toolchain_stage.py requires Python 3.11+ (tomllib); none found on PATH")
__doc__ = """Stage origin/main locally, or run one tick of the standing fleet train.

`run` stages origin/main in a state directory and stops there: no upload, no channel
admission, no deletion. `train` cuts main's tip with the same stage path whenever the
previous train has ended and main has moved, publishes the seed archives, lands the
re-pin, stage-uploads the signed pack and publishes it to the signed atpkg index with
trust-resource-controller from the same commit; the consumer checks and the proof
comparison run after that and are reported in docs/OPEN_ISSUES.md. Neither claims proof
completeness. See docs/DAILY_TOOLCHAIN_STAGING.md.
"""

import argparse
import ast
import contextlib
import concurrent.futures
import copy
import datetime as dt
import fcntl
import hashlib
import json
import os
from pathlib import Path
import plistlib
import re
import runpy
import shutil
import shlex
import signal
import stat
import subprocess
import sys
import threading
import time
import tempfile
import tomllib
from typing import Callable


SCHEMA = "trust.daily-local-stage.v1"
CONSUMER_RECEIPT_SCHEMA = "trust.daily-consumer-acceptance.v2"
MAX_QUERY_BYTES = 1024 * 1024
# The dependency preparation is bounded item by item, by progress, and by a ceiling
# computed from its inputs, never by one total (RL-55). An item is one tree copied into
# a Cargo home, one Git acquisition, one `targo fetch` of one manifest: it runs as long
# as it keeps moving and ends after the recreator's stall window below its floor
# (SUBMODULE_STALL_WINDOW_SECONDS, SUBMODULE_FLOOR_BYTES_PER_SECOND). The ceiling keeps
# the whole finite: PREWARM_ITEM_SECONDS for every item it counts at its start, plus
# every byte it was given, copied twice (into its home, then into the handoff), at
# PREWARM_FLOOR_BYTES_PER_SECOND. One total of 900 s, then 3600 s, ended moving
# preparations as the Git databases grew (m86, 2026-11-14: offline fetch 32 of 55).
# 30 s an item, measured on m86 on 2026-11-17 (origin/main's pins and configuration, the
# train's cache declarations, two preparations at once, load 17 to 40) once a fetch item
# no longer walked what Cargo had finished (cargo_home_progress_bytes): from an empty
# input home its 165 fetches took 6.8 s on average (online 12.9 s, the slowest 453 s;
# offline 1.2 s; handoff replay 6.2 s), and the whole 1,704 s of a 5,370 s ceiling (32%);
# from the train's input home 1,695 s of 6,092 s (28%). Before that change the empty-home
# preparation took 3,682 s (69%), its offline fetches 12.9 s each. The sum of the items
# carries the slow ones.
PREWARM_ITEM_SECONDS = 30
PREWARM_FLOOR_BYTES_PER_SECOND = 1024 * 1024
# The trees of an input Cargo home the preparation copies. Its git/db databases are
# lent as object stores and never copied: a copy carried every ancestor's bodies (28 GB
# on 2026-11-14) into the home and from it into the handoff (RL-54).
PREWARM_COPIED_TREES = ("registry/index", "registry/cache")
# How often the preparation's own waits (a tree copy) look at an item's progress.
PREWARM_POLL_SECONDS = 1.0
# x.py takes its build lease only from a manager that answers this to `--protocol`
# (x.py, _trust_build_lock_frontend). The tree's own managers, in x.py's order: the
# Bootstrap bootstrap.py builds, then the one scripts/build-tree-manager.sh builds for
# a tree that has none yet.
MANAGER_PROTOCOL = b"trust-build-tree-manager-v2\n"
TREE_MANAGERS = ("build/bootstrap/debug/bootstrap", "build/bootstrap/release/bootstrap",
                 "build-tree-manager.noindex/debug/bootstrap")
# The DDC observations a failed mint retains in its WORK, which a continuation reads from
# its evidence directory's ddc-equality-evidence/ (mint_seed_recovery.validate).
MINT_DDC_EVIDENCE = ("stage2-pinned-seed.json", "stage2-ddc-seed.json", "ddc-seed.json", "ddc-seed-post-build.json")
WP_BINS = ("trust-wp", "trust-wp-driver", "trust-wp-rustc", "targo-trust-wp", "cargo-trust-wp")
CONSUMERS = ("aterm", "ay", "ty", "clean")
REQUIREMENTS = [
    "A fleet build needs no decision entry: `train`, on a Mac whose `aterm secrets status` says release signing is ready, publishes the seed archives, lands the re-pin, stage-uploads the signed pack and publishes it to the signed atpkg index (the lab tracker's decisions RL-D14 and RL-D15).",
    "A public seal (P5b) needs the aterm, ay, ty and clean checks at their origin/main on this exact staged toolchain, with the results committed.",
    "A public seal (P5b) also needs SEAL-1's four clauses with committed evidence, the staging canary and the index publish (docs/CUTTING-A-TOOLCHAIN.md).",
]
# v2: `published` is a build an index serves. A v1 train stage-uploaded and called that
# published; load_train migrates its state (migrate_train_v1).
TRAIN_SCHEMA = "trust.toolchain-train.v2"
TRAIN_SCHEMA_V1 = "trust.toolchain-train.v1"
TRAIN_LABEL = "systems.alab.trust-train"
# Set in a tick that advanced --repo and re-executed itself, so it does not advance twice.
TRAIN_ADVANCED = "TRUST_TRAIN_ADVANCED"
# `launchctl bootout` returns while launchd is still stopping a running tick, and a
# bootstrap before the old job is gone fails (exit 5). Seconds an install waits for it.
TRAIN_BOOTOUT_WAIT = 600
TRAIN_ISSUE = "FLEET-BUILD-REPORT-1"
TRAIN_ISSUE_FILE = "docs/OPEN_ISSUES.md"
TRAIN_ISSUE_SECTION = "## Toolchain, bootstrap and release"
TRAIN_HISTORY = 8
TRAIN_SOURCE_PINS = "trust.train-source-pins.v1"
TRAIN_SOURCE_OBJECTS = "trust.train-source-objects.v1"
# What a build regenerates; the last good build is kept without it.
TRAIN_INTERMEDIATES = ("source/build", "targets", "dependencies", "consumer-targets", "consumer-rustup")
BUILD_TAG = re.compile(r"atpkg-trust-([0-9]+)")
CONTROLLER = "trust-resource-controller"
# Every publisher command a fleet train runs, word for word: (the global --host values it
# may run under, one pattern per word). Nothing else is built (fleet_publisher).
_PATH, _BUILD = r"/[^\n]*", r"[1-9][0-9]{0,15}"
_GROUP = ("publish-group", "rustc", "--seal", _PATH, "--trust-repo", _PATH, "--checkout", "trust-ir=" + _PATH,
          "--checkout", "trust-cg=" + _PATH, "--checkout", "trust-vc=" + _PATH, "--out", _PATH)
PUBLISHER_COMMANDS = {
    # Reads this Mac's agh configuration; `hosts check` takes no global --host.
    "hosts check": (("agh-staging", "agh"), ("hosts", "check")),
    "publisher preflight": (("agh-staging", "agh", "gh"), (*_GROUP, "--dry-run")),
    "stage-upload": (("agh-staging", "agh", "gh"), (*_GROUP, "--stage-upload")),
    # Installs and runs the staged pack in a scratch prefix and signs train-receipt.toml.
    "canary": (("agh",), ("canary", "trust=" + _BUILD, "--out", _PATH, "--consumer", "aterm=" + _PATH,
                          "--consumer", "ay=" + _PATH, "--consumer", "ty=" + _PATH, "--consumer", "clean=" + _PATH)),
    "publish staged": (("agh",), ("publish-group", "rustc", "--publish-staged", "--out", _PATH)),
    "status": (("agh",), ("status",)),
    "controller pack": (("agh",), ("pack", CONTROLLER, "--checkout", _PATH, "--toolchain", _PATH, "--trust-repo", _PATH,
                                   "--build", _BUILD, "--out", _PATH, "--upload")),
    "controller index": (("agh",), ("index", "--pin", f"{CONTROLLER}={_BUILD}", "--out", _PATH, "--upload")),
}
# Never a fleet train's, whatever the shape: each overrides a publisher refusal, takes a
# build back, writes outside the index's own publish, or adopts for a consumer.
PUBLISHER_NEVER = frozenset({"--force-same-build", "--allow-build-tree-seal", "mirror", "lane", "adopt",
                             "pack-bundle", "withdraw"})
# How many times one tick publishes an index again after another publisher took the
# next index number, and how many ticks try a staged build before the train moves on.
INDEX_ATTEMPTS = 3
PUBLISH_TICKS = 3
# aterm's compare-and-swap (crates/atpkg-publish/src/channel/index.rs, compare_and_swap)
# refuses with exit 1 when another publisher took the next index number; its words are
# the only signal. An orphaned draft is not a race and is not retried.
INDEX_RACE = ("another publisher took index", "(a racing publisher), re-run")
STATUS_PREFIX = "atpkg-publish status: "
STATUS_PIN = re.compile(r"  pin (?P<program>\S+) = (?P<build>[0-9]+)"
                        r"(?: on (?P<target>\S+)(?: \(not a target this client knows\))?| \[[^\]]+\])?")
_CLEANUP_APIS: dict[tuple[str, str], dict] = {}
_CLEANUP_API_LOCK = threading.Lock()


class Refused(RuntimeError):
    pass


class CommandFailed(Refused):
    def __init__(self, message: str, exit_code: int | None = None, timed_out: bool = False):
        super().__init__(message)
        self.exit_code = exit_code
        self.timed_out = timed_out


class CustodyBroken(Refused):
    """A train's build failed a custody check before publication: it is never published."""


class Unanswered(Refused):
    """GitHub did not answer for a rate limit; the question is still open."""


class _SignalLatch:
    """A monotonic main-thread flag; nested signal handlers must take no lock."""
    def __init__(self):
        self.raised = False

    def set(self) -> None:
        self.raised = True

    def is_set(self) -> bool:
        return self.raised


def now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def file_hash(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def atomic_json(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + f".{os.getpid()}.tmp")
    with temporary.open("x", encoding="utf-8") as stream:
        json.dump(value, stream, sort_keys=True, indent=2)
        stream.write("\n")
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(temporary, path)


def read_json(path: Path) -> dict:
    if path.is_symlink() or not path.is_file() or path.stat().st_size > 8 * 1024 * 1024:
        raise Refused(f"not a bounded regular status file: {path}")
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise Refused(f"not a status object: {path}")
    return value


# Bootstrap's Sysroot step links every stage sysroot's two source entries to the checkout
# that built it (upstream src/bootstrap compile.rs); promote-toolchain.sh freezes both into
# the seal. An unsealed stage tree (the mint's pack source, a prepared stage2) carries them.
BOOTSTRAP_SOURCE_LINKS = frozenset({"./lib/rustlib/src/rust", "./lib/rustlib/rustc-src/rust"})


def fingerprint(path: Path, source: Path | None = None) -> dict:
    """Hash names, kinds, modes, links and bytes, without following directory links.

    With ``source``, the tree's two bootstrap source entries may name exactly that
    checkout (the run's own commit-bound snapshot); they are bound by their link text and
    never followed. Every other link that leaves the tree is refused."""
    if path.is_symlink() or not path.exists():
        raise Refused(f"artifact absent or its root is a symlink: {path}")
    root = path.resolve()
    digest = hashlib.sha256()
    count = 0

    def visit(item: Path, name: str) -> None:
        nonlocal count
        info = item.lstat()
        mode = stat.S_IMODE(info.st_mode)
        if stat.S_ISLNK(info.st_mode):
            target = os.readlink(item)
            source_entry = source is not None and name in BOOTSTRAP_SOURCE_LINKS and target == str(source)
            if not source_entry and not item.resolve().is_relative_to(root):
                raise Refused(f"artifact link escapes its hashed tree: {item} -> {target}")
            row = [name, "link", mode, target]
        elif stat.S_ISREG(info.st_mode):
            row = [name, "file", mode, info.st_size, file_hash(item)]
        elif stat.S_ISDIR(info.st_mode):
            row = [name, "dir", mode]
        else:
            raise Refused(f"artifact contains a special file: {item}")
        digest.update(json.dumps(row, ensure_ascii=True, separators=(",", ":")).encode() + b"\n")
        count += 1
        if stat.S_ISDIR(info.st_mode):
            for child in sorted(item.iterdir(), key=lambda p: p.name):
                visit(child, f"{name}/{child.name}")

    visit(path, ".")
    return {"sha256": digest.hexdigest(), "entries": count}


def read_json_artifact(path: Path, *, unique_keys: bool = False) -> tuple[dict, dict]:
    """Bind a bounded JSON object and artifact identity to the same file bytes."""
    limit = 8 * 1024 * 1024

    def physical_identity(info: os.stat_result) -> tuple:
        return (info.st_dev, info.st_ino, info.st_mode, info.st_nlink,
                info.st_size, info.st_mtime_ns, info.st_ctime_ns)

    def unique_object(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise Refused(f"duplicate JSON artifact field {key!r}: {path}")
            result[key] = value
        return result

    try:
        descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
        with os.fdopen(descriptor, "rb") as stream:
            before = os.fstat(stream.fileno())
            if not stat.S_ISREG(before.st_mode) or before.st_size > limit:
                raise Refused(f"not a bounded regular JSON artifact: {path}")
            payload = stream.read(limit + 1)
            after = os.fstat(stream.fileno())
        if (len(payload) > limit or len(payload) != before.st_size
                or physical_identity(before) != physical_identity(after)):
            raise Refused(f"JSON artifact changed while reading: {path}")
        value = json.loads(payload.decode("utf-8"), object_pairs_hook=unique_object if unique_keys else None)
        if not isinstance(value, dict):
            raise Refused(f"not a JSON artifact object: {path}")
        row = [".", "file", stat.S_IMODE(before.st_mode), len(payload),
               hashlib.sha256(payload).hexdigest()]
        identity = {"sha256": hashlib.sha256(
            json.dumps(row, ensure_ascii=True, separators=(",", ":")).encode() + b"\n"
        ).hexdigest(), "entries": 1}
        # Refuse replacement, symlink substitution or mutation during parsing too.
        # The final artifact replay checks these same payload bytes again later.
        if physical_identity(path.lstat()) != physical_identity(after):
            raise Refused(f"JSON artifact changed while reading: {path}")
    except OSError as error:
        raise Refused(f"cannot read regular JSON artifact: {path}: {error}") from error
    return value, identity


@contextlib.contextmanager
def single_run(state: Path):
    state.mkdir(parents=True, exist_ok=True)
    with (state / "run.lock").open("a+") as stream:
        try:
            fcntl.flock(stream, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise Refused(f"another daily staging run owns {state / 'run.lock'}") from error
        stream.seek(0)
        stream.truncate()
        stream.write(f"pid={os.getpid()} started={now()}\n")
        stream.flush()
        try:
            yield
        finally:
            fcntl.flock(stream, fcntl.LOCK_UN)


def cleanup_api(engine: Path) -> dict:
    owner = engine / "bin/pub"
    if owner.is_symlink() or not owner.is_file():
        raise Refused(f"publication cleanup owner is not a regular file: {owner}")
    key = (str(owner.resolve(strict=True)), file_hash(owner))
    # runpy temporarily changes sys.modules/sys.argv. Prime one API before the
    # consumer pool, then reuse its functions without reentering the loader.
    with _CLEANUP_API_LOCK:
        if key not in _CLEANUP_APIS:
            api = runpy.run_path(str(owner), run_name="trust_daily_process_cleanup")
            if not callable(api.get("terminate_process_group")):
                raise Refused("publication owner does not expose bounded trustd-sparing cleanup")
            _CLEANUP_APIS[key] = api
        return _CLEANUP_APIS[key]


def python_search_path(state: Path, inherited: str) -> str:
    parts = inherited.split(os.pathsep)
    if any(not Path(part).is_absolute() for part in parts):
        raise Refused("daily staging PATH must contain only absolute directories")
    return os.pathsep.join(dict.fromkeys([str(state / "python-bin"), *parts]))


def selected_elan_home(explicit: Path | None) -> Path | None:
    """Capture one Lean installation root, never the caller's other settings."""
    inherited = os.environ.get("ELAN_HOME")
    path = explicit
    if path is None and inherited:
        path = Path(inherited)
    if path is None:
        return None
    try:
        selected = path.resolve(strict=True)
    except OSError as error:
        raise Refused(f"ELAN_HOME directory is unavailable: {path}: {error}") from error
    if not selected.is_dir():
        raise Refused(f"ELAN_HOME must name an existing directory: {path}")
    return selected


def selected_serial_command(explicit: Path | None, search_path: str | None) -> Path:
    """Select the executor promotion's gates start every compiler through.

    promote-toolchain.sh refuses before any gate without
    TRUST_TOOLCHAIN_SERIAL_COMMAND, and Runner removes every ambient TRUST_*
    setting, so the runner names the file itself. Select it before the mint:
    a missing executor must refuse at the start, not after hours of building.
    The file must be what promotion accepts: an absolute regular executable,
    not a link. A PATH entry that is a link is followed to its file.
    """
    if explicit is not None:
        path = explicit
    else:
        found = shutil.which("trust-serial-command", path=search_path)
        if found is None:
            raise Refused("promotion's gates start compilers through trust-serial-command and none is on PATH; "
                          "pass --serial-command /absolute/path (crates/trust-resource-controller builds it)")
        try:
            path = Path(found).resolve(strict=True)
        except OSError as error:
            raise Refused(f"trust-serial-command on PATH is unavailable: {found}: {error}") from error
    if (not path.is_absolute() or ".." in path.parts or path.is_symlink()
            or not path.is_file() or not os.access(path, os.X_OK)):
        raise Refused(f"serial command must be the absolute path of a regular executable file, not a link: {path}")
    return path


def elan_home_identity(home: Path | None) -> dict | None:
    """Bind installation bytes, including elan's explicitly linked toolchains."""
    if home is None:
        return None
    if home.is_symlink() or not home.is_dir():
        raise Refused(f"ELAN_HOME lost its selected directory: {home}")
    entries = {}
    for item in sorted(home.iterdir(), key=lambda path: path.name):
        if item.name != "toolchains":
            entries[item.name] = fingerprint(item)
            continue
        if item.is_symlink() or not item.is_dir():
            raise Refused(f"ELAN_HOME toolchains must be a directory, not a link: {item}")
        toolchains = {}
        for toolchain in sorted(item.iterdir(), key=lambda path: path.name):
            resolved = toolchain.resolve(strict=True)
            if not resolved.is_dir():
                raise Refused(f"ELAN_HOME toolchain must resolve to a directory: {toolchain}")
            toolchains[toolchain.name] = {
                "link": os.readlink(toolchain) if toolchain.is_symlink() else None,
                "resolved": str(resolved), "identity": fingerprint(resolved)}
        entries[item.name] = {"mode": stat.S_IMODE(item.stat().st_mode), "toolchains": toolchains}
    return {"path": str(home), "mode": stat.S_IMODE(home.stat().st_mode), "entries": entries}


def private_python(state: Path, interpreter: Path) -> Path:
    directory = state / "python-bin"
    if directory.is_symlink():
        raise Refused(f"private Python directory must not be a symlink: {directory}")
    directory.mkdir(exist_ok=True)
    alias = directory / "python3"
    if not alias.exists() and not alias.is_symlink():
        alias.symlink_to(interpreter)
    if not alias.is_symlink() or alias.resolve(strict=True) != interpreter:
        raise Refused(f"private python3 does not select the controller interpreter: {alias}")
    return alias


KEPT_AGH = "kept-agh"


def keep_agh(root: Path, inherited: str) -> dict | None:
    """Keep the Agh first on the PATH `inherited` under `root`/kept-agh; None when PATH names none.

    Each Agh acquisition records the identity of the Agh it selected (path, inode, bytes,
    SHA-256) and refuses when that differs at its end: "Agh source transport changed during
    acquisition". A tick's acquisitions run for an hour or more, and the Agh on PATH is a
    link into the installed aterm, which the Mac's updater replaces: three times in the 21
    hours of 2026-11-16, once inside a tick's fetch, which ended that tick. So a run selects
    its Agh once, here, and runs a kept copy to its end. The acquisitions' identity check is
    unchanged; it reads a file nothing replaces.

    macOS ends a copy of an application's executable that starts outside its bundle, whose
    Info.plist its signature binds (aterm 0.205.0: SIGKILL from every directory), so an
    executable in NAME.app/Contents/MacOS is kept with its bundle. Once any program in a
    copied bundle has run, macOS's App Management protection lets no process but the
    bundle's own signer and the programs a person allowed change or delete it, the process
    that copied and ran it included (measured on m86, macOS 27.2, 2026-11-17: EPERM on the
    bundle's directory for a process outside aterm; the train runs under launchd, outside
    aterm). Replacing the previous run's copy therefore ended every tick after the first.
    So each copy lives in a directory named by its fingerprint and is never written again:
    a run whose installed Agh is the one already kept reuses that copy, after checking it is
    still whole and still runs; a run after an update makes a new one beside it. A copy the
    run cannot remove is left where it is and named in the record (`left`), never a reason
    to stop: a session in aterm (the bundle's signer) can remove it.

    The copy must hold the selected Agh's bytes and must run: an Agh replaced while it was
    being copied, or one that does not answer `agh version` from here, refuses the run at
    its start. The caller holds `root`'s lock.
    """
    selected = shutil.which("agh", path=inherited)
    if selected is None:
        return None
    if not Path(selected).is_absolute():
        raise Refused(f"the run's Agh must come from an absolute PATH directory: {selected}")
    program = Path(selected).resolve(strict=True)
    home = root / KEPT_AGH
    if home.is_symlink() or (home.exists() and not home.is_dir()):
        raise Refused(f"the kept Agh must be this state root's own directory: {home}")
    if program.is_relative_to(home.resolve()):
        raise Refused(f"PATH already selects the Agh a run kept under {home}; start the run with the installed one")
    parents = program.parents
    bundled = (len(parents) > 3 and parents[0].name == "MacOS" and parents[1].name == "Contents"
               and parents[2].suffix == ".app")
    origin = parents[2] if bundled else program
    expected = fingerprint(origin)
    copies = home / "program"
    if copies.is_symlink() or (copies.exists() and not copies.is_dir()):
        raise Refused(f"the kept Agh copies must be this state root's own directory: {copies}")
    slot = copies / expected["sha256"]
    if slot.is_symlink() or (slot.exists() and not slot.is_dir()):
        raise Refused(f"the kept Agh slot must be this state root's own directory: {slot}")
    kept = slot / origin.name
    reused = kept.exists() and not kept.is_symlink() and fingerprint(kept) == expected
    if not reused:
        if slot.exists() or slot.is_symlink():
            try:
                remove_tree(slot)  # an unfinished copy: one that never ran can be removed
            except PermissionError as error:
                raise Refused(f"a kept Agh copy is neither whole nor removable by this run: {slot}; "
                              "remove it from a session in aterm") from error
        kept.parent.mkdir(parents=True)
        if bundled:
            shutil.copytree(origin, kept, symlinks=True)
        else:
            shutil.copy2(origin, kept)
        if fingerprint(kept) != expected:
            raise Refused(f"Agh changed while this run copied it, so the copy is no Agh: {origin}")
    executable = kept / program.relative_to(origin) if bundled else kept
    # One name on the run's PATH and nothing else of the bundle: the link chooses the
    # program by its name, as the installed one does. It sits beside the copy, outside it.
    link = slot / "bin/agh"
    if link.parent.is_symlink() or (link.parent.exists() and not link.parent.is_dir()):
        raise Refused(f"the kept Agh's link directory must be this state root's own: {link.parent}")
    if link.is_symlink() and os.readlink(link) != str(executable):
        link.unlink()
    if not link.is_symlink():
        link.parent.mkdir(exist_ok=True)
        if link.exists():
            raise Refused(f"the kept Agh's link is not a link: {link}")
        link.symlink_to(executable)
    try:
        answer = subprocess.run([str(link), "version"], capture_output=True, text=True, timeout=60,
                                stdin=subprocess.DEVNULL)
    except (OSError, subprocess.TimeoutExpired) as error:
        raise Refused(f"the Agh this run kept does not run from {link}: {error}") from error
    if answer.returncode != 0:
        raise Refused(f"the Agh this run kept does not run from {link}: `agh version` exited {answer.returncode}"
                      + (f": {answer.stderr.strip().splitlines()[-1]}" if answer.stderr.strip() else ""))
    # Earlier copies, and the single-copy layout of trust d0b7f21a61 (kept-agh/bin and
    # kept-agh/program/NAME.app): removed when this run may, named when it may not.
    left = []
    stale = [entry for entry in sorted(copies.iterdir()) if entry != slot]
    if (home / "bin").is_dir() and not (home / "bin").is_symlink():
        stale.append(home / "bin")
    for entry in stale:
        try:
            if entry.is_symlink() or not entry.is_dir():
                entry.unlink()
            else:
                remove_tree(entry)
        except PermissionError:
            left.append(str(entry))
    if left:
        print(f"train: {len(left)} earlier kept Agh cop{'y' if len(left) == 1 else 'ies'} macOS protects from "
              f"this run; remove from a session in aterm: {' '.join(left)}", file=sys.stderr)
    return {"selected": selected, "program": str(program), "kept": str(link), "directory": str(link.parent),
            "executable": str(executable), "sha256": file_hash(executable),
            "version": answer.stdout.strip().splitlines()[0] if answer.stdout.strip() else "",
            "reused": reused, "left": left}


def first_on_path(directory: str, inherited: str) -> str:
    return os.pathsep.join(dict.fromkeys([directory, *inherited.split(os.pathsep)]))


@contextlib.contextmanager
def agh_kept_in(root: Path):
    """Run a block with `root`'s kept Agh (keep_agh) first on this process's PATH.

    The process's own PATH, because the recreator's acquisitions select their Agh in this
    process; every child's environment starts from it. Yields keep_agh's record."""
    inherited = os.environ.get("PATH")
    kept = keep_agh(root, os.defpath if inherited is None else inherited)
    if kept is None:
        yield None
        return
    os.environ["PATH"] = first_on_path(kept["directory"], os.defpath if inherited is None else inherited)
    try:
        yield kept
    finally:
        if inherited is None:
            os.environ.pop("PATH", None)
        else:
            os.environ["PATH"] = inherited


def command(argv: list[str], cwd: Path, env: dict[str, str], log: Path,
            timeout: int | None = None, *, cleanup_owner: Path | None = None,
            cancel_event: threading.Event | None = None, progress=None) -> str:
    """One child, one waiter; delegate gate-tree cleanup to its established owner.

    `progress` is the recreator's _SubmoduleProgress: the child ends when the bytes arriving
    under its paths and in this log stay below its floor rate for its stall window, and runs
    however long it takes while they keep arriving. `timeout` is a total, for a step that has one.
    """
    with log.open("w", encoding="utf-8") as stream:
        stream.write(json.dumps({"argv": argv, "cwd": str(cwd)}) + "\n")
        stream.flush()
        if cancel_event is not None and cancel_event.is_set():
            raise InterruptedError("staging cancelled before command launch")
        if progress is not None:
            progress.paths = (*progress.paths, log)  # what the child prints
            progress.begin()
        child = subprocess.Popen(argv, cwd=cwd, env=env, stdout=stream,
                                 stderr=subprocess.STDOUT, start_new_session=True)
        try:
            deadline = None if timeout is None else time.monotonic() + timeout
            while True:
                if cancel_event is not None and cancel_event.is_set():
                    raise InterruptedError("staging cancelled")
                left = None if deadline is None else deadline - time.monotonic()
                if left is not None and left <= 0:
                    raise subprocess.TimeoutExpired(argv, timeout)
                try:
                    result = child.wait(timeout=min(0.2, left) if left is not None else 0.2)
                    break
                except subprocess.TimeoutExpired:
                    pass
                if progress is not None:
                    progress.check(argv)
        except BaseException as error:
            if cleanup_owner is not None:
                cleanup_api(cleanup_owner)["terminate_process_group"](child)
            else:
                # Simple short commands have no gate process tree. Never broadcast
                # to their group: a shared daemon can outlive its launching group.
                with contextlib.suppress(ProcessLookupError):
                    child.terminate()
                try:
                    child.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    child.kill()
                    child.wait(timeout=10)
            if isinstance(error, subprocess.TimeoutExpired):
                why = getattr(error, "reason", None) or f"command timed out after {timeout}s"
                raise CommandFailed(f"{why}; see {log}", child.returncode, True) from error
            if isinstance(error, (KeyboardInterrupt, InterruptedError)):
                error.child_exit_code = child.returncode
            raise
    if result:
        raise CommandFailed(f"command exited {result}; see {log}", result)
    # Only the small owner queries use the return value; build output stays on disk.
    return log.read_text(encoding="utf-8") if log.stat().st_size < MAX_QUERY_BYTES else ""


def owned_command(engine: Path, result_path: Path, timeout: int | None, argv: list[str],
                  interrupted: _SignalLatch | None = None) -> int:
    """An isolated child of build-slot; only its owner supervises the gate tree."""
    api = cleanup_api(engine)
    result = {"exit_code": None, "signal": None, "timed_out": False, "interrupted": False}
    child = None
    try:
        child = subprocess.Popen(argv, start_new_session=True)
        deadline = None if timeout is None else time.monotonic() + timeout
        while True:
            if interrupted is not None and interrupted.is_set():
                raise InterruptedError("owned command interrupted")
            left = None if deadline is None else deadline - time.monotonic()
            if left is not None and left <= 0:
                raise subprocess.TimeoutExpired(argv, timeout)
            try:
                result["exit_code"] = child.wait(timeout=min(0.2, left) if left is not None else 0.2)
                break
            except subprocess.TimeoutExpired:
                continue
        if interrupted is not None and interrupted.is_set():
            raise InterruptedError("owned command interrupted while observing exit")
        return result["exit_code"] if result["exit_code"] >= 0 else 128 - result["exit_code"]
    except BaseException as error:
        # The slot forwards TERM while the outer cleanup owner may also signal
        # this helper directly. A second interruption must not abort its drain.
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        signal.signal(signal.SIGINT, signal.SIG_IGN)
        if child is not None:
            api["terminate_process_group"](child)
        result.update(exit_code=child.returncode if child is not None else None, timed_out=isinstance(error, subprocess.TimeoutExpired),
                      interrupted=isinstance(error, (KeyboardInterrupt, InterruptedError)), error=str(error))
        return 124 if result["timed_out"] else 130
    finally:
        if interrupted is not None and interrupted.is_set():
            result["interrupted"] = True
        if child is not None and child.returncode is not None:
            result["exit_code"] = child.returncode
            result["signal"] = -child.returncode if child.returncode < 0 else None
        atomic_json(result_path, result)


def tree_build_manager(source: Path, env: dict[str, str]) -> Path | None:
    """The first of the tree's own build-tree managers that answers protocol v2, asked in
    x.py's order and as x.py asks it, or None.

    x.py's list also names an explicit TRUST_BUILD_TREE_MANAGER_TARGO and then `targo trust
    repo lock` on PATH. Neither reaches the x.py a cut runs: the runner drops every ambient
    TRUST_* setting, and the mint runs each x.py under `env -i` with a PATH of its reviewed
    helper profile, which admits no Rust-family tool (mint_seed_support.rust_family_name).
    Only the tree's own manager can serve the mint, so only it is asked: an installed Targo
    that answers v2 is no reason to skip building one."""
    for relative in TREE_MANAGERS:
        executable = source / relative
        if not executable.is_file() or not os.access(executable, os.X_OK):
            continue
        try:
            probe = subprocess.run([str(executable), "--trust-build-tree-lock", "--protocol"], cwd=source,
                                   env=env, timeout=10, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        except (OSError, subprocess.TimeoutExpired):
            continue
        if probe.returncode == 0 and probe.stdout == MANAGER_PROTOCOL:
            return executable
    return None


def bootstrap_environment(env: dict[str, str], owner: Path) -> dict[str, str]:
    """Read the owner's literal policy, without executing/importing its module."""
    policy = {}
    wanted = {"BUILD_AUTHORITY_ENV_NAMES", "BUILD_AUTHORITY_ENV_PREFIXES"}
    for node in ast.parse(owner.read_text(encoding="utf-8")).body:
        if isinstance(node, ast.Assign):
            for target in node.targets:
                if isinstance(target, ast.Name) and target.id in wanted:
                    value = ast.literal_eval(node.value)
                    if not isinstance(value, (set, tuple, list)) or not all(isinstance(v, str) for v in value):
                        raise Refused(f"recreator authority policy is not a literal string collection: {target.id}")
                    policy[target.id] = value
    if policy.keys() != wanted:
        raise Refused("recreator does not expose its literal authority environment policy")
    names = policy["BUILD_AUTHORITY_ENV_NAMES"]
    prefixes = tuple(policy["BUILD_AUTHORITY_ENV_PREFIXES"])
    return {key: value for key, value in env.items() if key not in names and not key.startswith(prefixes)}


def admitted_bootstrap(argv: list[str]) -> int:
    """Translate gate admission into a recreator option, before authority capture."""
    jobs = os.environ.get("CARGO_BUILD_JOBS", "")
    if (os.environ.get("BUILD_SLOT_HELD") != "1" or not jobs.isdecimal() or int(jobs) < 1
            or len(argv) < 2 or Path(argv[1]).name != "recreate_bootstrap.py"
            or "--jobs" in argv or "-j" in argv):
        raise Refused("admitted bootstrap needs one build-slot CPU share and an unconfigured recreator command")
    environment = bootstrap_environment(dict(os.environ), Path(argv[1]))
    os.execve(argv[0], [*argv, "--jobs", str(int(jobs))], environment)
    return 1  # execve does not return


def declared_rustup_target_step(words: list[str]) -> tuple | None:
    """Capture an explicit target installation even when its later use is opaque."""
    if len(words) < 3 or Path(words[0]).name != "rustup" or words[1:3] != ["target", "add"]:
        return None
    toolchain = None
    targets = []
    index = 3
    while index < len(words):
        word = words[index]
        if word == "--toolchain" or word.startswith("--toolchain="):
            if toolchain is not None:
                raise Refused("rustup target declaration selects a toolchain more than once")
            if word == "--toolchain":
                index += 1
                if index == len(words):
                    raise Refused("rustup target declaration lacks its toolchain value")
                toolchain = words[index]
            else:
                toolchain = word.split("=", 1)[1]
        elif word.startswith("-"):
            raise Refused("unsupported option in rustup target declaration")
        else:
            targets.append(word)
        index += 1
    return "rustup-target-add", toolchain, tuple(targets)


def consumer_policy(engine: Path, source: Path) -> dict:
    """Use the publication owner's reader/validator; never source config.sh."""
    policy_file = source / "publish/config.sh"
    if policy_file.is_symlink() or not policy_file.is_file() or policy_file.stat().st_size > 1024 * 1024:
        raise Refused(f"consumer policy is absent, linked or oversized: {policy_file}")
    owner = engine / "bin/pub"
    if owner.is_symlink() or not owner.is_file():
        raise Refused(f"publication policy reader is not a regular file: {owner}")
    api = runpy.run_path(str(owner), run_name="trust_daily_consumer_policy")
    config = api["load_config"](source / "publish")
    text = config["check"]
    if not text or config.get("check_lane") not in {"advisory", "strict", "certify"}:
        raise Refused("consumer policy must expose a supported verified Trust check/build command")
    if api["check_command_toolchain"](text) != "trust":
        raise Refused("consumer policy does not bind the scratch trust toolchain")
    oracles: dict[str, set[str]] = {}
    for words in api["check_command_steps"](text):
        names = [Path(word).name for word in words]
        if any(name in {"gh", "ssh", "scp", "rsync", "sudo", "launchctl", "osascript"} for name in names):
            raise Refused("consumer check contains an unsupported external write/control command")
        if "git" in names and "push" in words:
            raise Refused("consumer checks may not push Git refs")
        if any(word.startswith(("RUSTUP_HOME=", "CARGO_TARGET_DIR=", "HOME=", "TRUST_TOOLCHAIN_HOME=")) for word in words):
            raise Refused("consumer check overrides its isolated home or target directory")
        if any(name in {"targo", "cargo"} for name in names) and any(word in {"publish", "install"} for word in words):
            raise Refused("consumer checks may not publish or install packages")
        if "rustup" in names and "toolchain" in words and any(word in {"link", "remove", "uninstall"} for word in words):
            raise Refused("consumer check changes its toolchain binding")
        # A consumer can declare a stock target here and use it inside `sh -c`,
        # which the publication reader deliberately does not expand. Preinstall
        # and fingerprint that declared oracle instead of relying on Rustup's
        # implicit installation during the check and omitting its input identity.
        stock = api["stock_rust_step"](words) or declared_rustup_target_step(words)
        if stock:
            _tool, toolchain, targets = stock
            if (not toolchain or toolchain == "trust" or not targets
                    or not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_.-]{0,127}", toolchain)
                    or not all(re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_.-]{0,127}", target) for target in targets)):
                raise Refused("unsupported labelled cross-target oracle requirement")
            oracles.setdefault(toolchain, set()).update(targets)
    bound = api["gate_wall_clock_bound"](text, config["check_timeout"], source)
    timeout = bound.get("seconds")
    if not isinstance(timeout, int) or isinstance(timeout, bool) or not 1 <= timeout <= 86400:
        raise Refused("publication reader returned an unsupported consumer check bound")
    baseline = config.get("check_baseline")
    return {"command": text, "command_sha256": hashlib.sha256(text.encode()).hexdigest(),
            "policy_sha256": file_hash(policy_file), "reader_sha256": file_hash(owner),
            "lane": config["check_lane"], "bound": bound,
            "cross_target_oracles": {name: sorted(targets) for name, targets in sorted(oracles.items())},
            "baseline": ({key: baseline.get(key) for key in ("path", "sha256")} if baseline else None)}


def consumer_outcome(engine: Path, policy: dict, step: dict) -> dict:
    """Apply publication's outcome belt to the complete, unchanged command log.

    A committed shell may admit advisory no-verdict exit 3. Its eventual exit
    zero cannot hide a stopped run, signal death, refutation or missing census.
    Publication owns those semantics; this runner still requires shell exit zero
    and never applies its known-red baseline exception.
    """
    owner = engine / "bin/pub"
    expected_owner = policy["reader_sha256"]
    if (owner.is_symlink() or not owner.is_file()
            or file_hash(owner) != expected_owner):
        raise Refused("consumer outcome publication owner changed")
    if policy["lane"] not in {"advisory", "strict", "certify"}:
        raise Refused("consumer outcome needs a supported proof lane")
    # JSON booleans and floats are not recorded process exit statuses.
    if (step.get("status") != "passed" or type(step.get("exit_code")) is not int
            or step.get("exit_code") != 0):
        raise Refused("consumer outcome requires a completed shell exit zero")
    log = Path(step["log"])
    expected_log = step.get("log_identity")
    if expected_log is None or fingerprint(log) != expected_log:
        raise Refused("consumer full output changed or lacks its completion identity")
    raw = log.read_bytes()
    header, separator, output = raw.partition(b"\n")
    if (not separator or json.loads(header) != {"argv": step["argv"], "cwd": step["cwd"]}):
        raise Refused("consumer full output lacks its exact command header")
    # Match publication's text-mode newline/decode behavior. The JSON argv
    # header is provenance, not command output (and must not invent a death).
    text = output.decode("utf-8", errors="replace").replace("\r\n", "\n").replace("\r", "\n")
    api = cleanup_api(engine)
    if (not callable(api.get("parse_gate_census"))
            or not callable(api.get("gate_belt_contradictions"))
            or not callable(getattr(api.get("SIGNAL_DEATH_RE"), "search", None))):
        raise Refused("publication owner lacks its consumer outcome API")
    census = api["parse_gate_census"](text)
    # GateStream.line/_died counts once per matching line; ProcessPoller only
    # enriches attribution. Do not infer zero deaths from a shell exit zero.
    deaths = sum(bool(api["SIGNAL_DEATH_RE"].search(line)) for line in text.split("\n"))
    refusals = api["gate_belt_contradictions"](census, text, deaths)
    # These two checks live in publication's public_clone_check, separately
    # from its belt (reviewed at 7b0fb3165f38:7610-7628). Zero proved is allowed;
    # a positive total with no recognized result category is unreadable.
    if census is None:
        refusals.append("proof lane printed no Gate census")
    else:
        counts = census["counts"]
        accounted = sum(counts.get(kind, 0) for kind in
                        ("proved", "failed", "unknown", "runtime_checked", "assumed"))
        if counts.get("total", 0) and not accounted:
            refusals.append("positive census total accounts for no recognized outcomes")
    if fingerprint(log) != expected_log or file_hash(owner) != expected_owner:
        raise Refused("consumer full output or publication owner changed during outcome validation")
    return {"schema": "trust.daily-consumer-outcome.v1", "reader_sha256": expected_owner,
            "lane": policy["lane"], "log_identity": expected_log,
            "log_sha256": hashlib.sha256(raw).hexdigest(),
            "output_sha256": hashlib.sha256(output).hexdigest(), "output_bytes": len(output),
            "census": census, "signal_death_count": deaths,
            "accepted": not refusals, "refusals": refusals}


def require_consumer_terminal_receipt(step: dict, name: str, cwd: Path, engine: Path,
                                      command: list[str], timeout: int) -> None:
    """Check the command owner's saved shell completion against the observed step."""
    path = Path(step["log"]).with_suffix(".result.json")
    argv = step.get("argv")
    if (step.get("name") != name or step.get("cwd") != str(cwd)
            or not isinstance(argv, list) or "_owned-command" not in argv):
        raise Refused("consumer terminal receipt does not belong to its owned command")
    owner_args = [str(engine), str(path), str(timeout), "--", *command]
    if step.get("result_file") != str(path) or argv[argv.index("_owned-command") + 1:] != owner_args:
        raise Refused("consumer terminal receipt does not belong to its owned command")
    measured, identity = read_json_artifact(path, unique_keys=True)
    for result in (measured, step.get("owned_result")):
        if (not isinstance(result, dict)
                or result.keys() != {"exit_code", "signal", "timed_out", "interrupted"}
                or type(result["exit_code"]) is not int or result["exit_code"] != 0
                or result["signal"] is not None or result["timed_out"] is not False
                or result["interrupted"] is not False):
            raise Refused("consumer terminal receipt does not show a successful owned shell exit")
    if step.get("owned_result_identity") != identity:
        raise Refused("consumer terminal receipt changed or lacks its completion identity")


def consumer_mappings(values: list[str]) -> dict[str, Path]:
    result = {}
    for value in values:
        name, separator, path = value.partition("=")
        if not separator or name not in CONSUMERS or name in result or not path:
            raise Refused("--consumer needs one unique aterm|ay|ty|clean=REPO mapping")
        result[name] = Path(path).resolve(strict=True)
    return result


def cargo_config_inputs(work: Path, environment: dict[str, str]) -> dict:
    """Bind applicable config files, including absence, without retaining their text."""
    cargo_home = Path(environment.get("CARGO_HOME", str(Path(environment["HOME"]) / ".cargo")))
    directories = [cargo_home, *(parent / ".cargo" for parent in (work, *work.parents))]
    result = {}
    for directory in directories:
        for name in ("config", "config.toml"):
            candidate = directory / name
            if candidate.exists() or candidate.is_symlink():
                resolved = candidate.resolve(strict=True)
                if not resolved.is_file():
                    raise Refused(f"Cargo config is not a regular file: {candidate}")
                result[str(candidate)] = {"resolved": str(resolved), "identity": fingerprint(resolved)}
            else:
                result[str(candidate)] = None
    return result


def consumer_environment(base: dict[str, str], staged: Path, rustup_home: Path,
                         target: Path, inherited_path: str) -> dict[str, str]:
    """The ordinary consumer's explicit, private full-SDK selection.

    This constructs environment data only. It neither links a toolchain nor
    attests a compiler, SDK, command result or publication outcome.
    """
    return {**base, "RUSTUP_HOME": str(rustup_home), "CARGO_TARGET_DIR": str(target),
            "TARGO": str(staged / "bin/targo"),
            "PATH": f"{rustup_home / 'bin'}:{staged / 'bin'}:{inherited_path}"}


def full_sdk_gates(call, stage: Path, source: Path, host: str, python: Path,
                   promotion_env: dict) -> None:
    """Run the unchanged complete staged-SDK contracts, preserving their order."""
    before = fingerprint(stage, source)
    call("toolchain-output-contract", ["sh", str(source / "tools/verify-toolchain.sh"), str(stage)])
    call("sysroot-library-contract", [str(python), "-I", "-S", "-B",
         str(source / "scripts/verify_sysroot_libraries.py"),
         "--sysroot", str(stage), "--target", host])
    call("staged-ui-and-tool-start", ["bash", str(source / "scripts/promote-toolchain.sh"),
         "--gate-only", str(stage)], heavy=True, env=promotion_env)
    if fingerprint(stage, source) != before:
        raise Refused("staged tree changed while its gates were running")


def owned_step_argv(slot: Path, python: Path, driver: Path, cleanup_owner: Path,
                    result: Path, timeout: int | None, argv: list[str],
                    admission: list[str] | None = None) -> list[str]:
    """The same original process/cleanup owner, inside original admission."""
    return [str(slot), *(admission or []), "--", str(python), str(driver),
            "_owned-command", str(cleanup_owner), str(result), str(timeout or 0), "--", *argv]


# What a build-slot that takes --rank and --claim-key answers to `--capabilities`.
BUILD_SLOT_CLAIM_WORDS = "build-slot-claim-v1"
# A fetch-only step's real needs: it compiles nothing, so it asks the gate for one core
# and no memory, and an aterm ledger's ALONE claim (which stops memory claims) never
# holds it back behind compile work.
FETCH_ONLY_ADMISSION = ["--cpus", "1", "--mem-gb", "0"]


def train_claim_key(step: str) -> str:
    """The ledger key of one train step: retries of a step (`-<attempt>`) share it, so
    aterm's memory book sizes a retry by what the step has used before."""
    return "trust-train:" + re.sub(r"-[0-9]+$", "", step)


def bind_owned_failure(step: dict, error: BaseException, detail: dict) -> None:
    """Preserve the wrapper wait separately from its original actual child."""
    step["owned_result"] = detail
    if isinstance(error, CommandFailed):
        step["wrapper_exit_code"] = error.exit_code
        error.exit_code, error.timed_out = detail["exit_code"], detail["timed_out"]
    elif isinstance(error, (KeyboardInterrupt, InterruptedError)):
        step["wrapper_exit_code"] = getattr(error, "child_exit_code", None)
        error.child_exit_code = detail["exit_code"]


def bound_dependency_owner(source_owner, path: Path, name: str):
    """Use the same captured-source loader for every dependency owner."""
    module = source_owner.module(name, path)
    return module.__dict__, module.__source_sha256__


def prewarm_ceiling(source: Path, cache: Path, cargo_input: Path | None, closure, recreator,
                    transport, measure, handoff: int) -> dict:
    """The preparation's ceiling, from what it measures at its start.

    Items: each input tree it will copy, each Git commit the owner locks name, the
    source owner's acquisition/check passes and the actual handoff replay, and the handoff's
    copy of each Cargo home tree. Bytes: what its home is filled from, the input's
    registry trees or the reused home's trees, counted for both copies. Gitlink
    children are found only during acquisition and share their parents' allowance.
    """
    manifests = closure["stage0_bootstrap_manifest_roots"](source)
    _locks, roots = transport["owner_lock_roots"](source, manifests, recreator)
    # One acquisition per commit, however many locked packages it holds (trust-ir's
    # workspace locks one row per crate: 158 rows, 11 commits on 2026-11-17).
    commits = {(root["url"], root["oid"]) for root in roots}
    if cache.exists():
        copies = []
        given = measure(tuple(cache / name for name in ("registry/index", "registry/cache", "git/db")))
    else:
        copies = [name for name in PREWARM_COPIED_TREES if cargo_input is not None and (cargo_input / name).is_dir()]
        given = measure(tuple(cargo_input / name for name in copies)) if copies else 0
    passes = 2 if callable(closure.get("acquire_dependency_inputs")) else 3
    items = len(copies) + len(commits) + passes * len(manifests) + handoff
    seconds = -(-(PREWARM_ITEM_SECONDS * items * PREWARM_FLOOR_BYTES_PER_SECOND + 2 * given)
                // PREWARM_FLOOR_BYTES_PER_SECOND)
    return {"seconds": seconds, "items": items, "input_copies": len(copies), "git_commits": len(commits),
            "manifests": len(manifests), "fetch_passes": passes, "handoff_copies": handoff, "input_bytes": given,
            "item_seconds": PREWARM_ITEM_SECONDS, "floor_bytes_per_second": PREWARM_FLOOR_BYTES_PER_SECOND,
            "stall_window_seconds": recreator["SUBMODULE_STALL_WINDOW_SECONDS"],
            "stall_floor_bytes_per_second": recreator["SUBMODULE_FLOOR_BYTES_PER_SECOND"]}


def describe_ceiling(ceiling: dict) -> str:
    return (f"dependency preparation ceiling: {ceiling['seconds']} s for {ceiling['items']} items "
            f"({ceiling['input_copies']} input copies, {ceiling['git_commits']} locked Git commits, "
            f"{ceiling.get('fetch_passes', 3)} fetches of {ceiling['manifests']} manifests, "
            f"{ceiling['handoff_copies']} handoff copies) at "
            f"{ceiling['item_seconds']} s each and {ceiling['input_bytes']} input bytes, copied twice, at "
            f"{ceiling['floor_bytes_per_second']} bytes/s; each item ends after "
            f"{ceiling['stall_window_seconds']} s below {ceiling['stall_floor_bytes_per_second']} bytes/s")


def finished_cargo_directory(path: str) -> bool:
    """A directory Cargo has finished and never writes into again: a Git checkout
    (`git/checkouts/<name>/<rev>`) or an unpacked crate (`registry/src/<index>/<crate>`)
    holding `.cargo-ok`. Cargo writes that file last: after the checkout and its
    submodules (targo-core sources/git/utils.rs, CheckoutGuard::mark_ok, which removes it
    before a checkout starts again) and after the crate is unpacked (sources/registry/
    mod.rs, unpack_package)."""
    grand = os.path.dirname(os.path.dirname(path))
    kind = (os.path.basename(os.path.dirname(grand)), os.path.basename(grand))
    return kind in {("git", "checkouts"), ("registry", "src")} and os.path.lexists(os.path.join(path, ".cargo-ok"))


def cargo_home_progress_bytes(paths: tuple[Path, ...]) -> int:
    """Bytes of the regular files under ``paths``, counted as the recreator's
    _submodule_progress_bytes counts them (links not followed, a file that vanishes
    while it is read skipped), but never inside a finished_cargo_directory.

    A `targo fetch` item watches its whole Cargo home, and the home's checkouts and
    unpacked crates are most of its entries: walking them at each item's start and at
    each sample cost m86 11.5 s for ty's checkout alone (475,787 entries, load 40) and
    made every offline fetch about 13 s, not 2.4 s (2026-11-17). A finished directory
    never grows, so it is no progress. When one finishes, the count drops by what it
    held; the bound counts only growth, so that reads as no growth, never as progress.
    """
    total = 0
    pending = [os.fspath(path) for path in paths]
    while pending:
        current = pending.pop()
        try:
            metadata = os.lstat(current)
            if stat.S_ISREG(metadata.st_mode):
                total += metadata.st_size
            elif stat.S_ISDIR(metadata.st_mode) and not finished_cargo_directory(current):
                with os.scandir(current) as entries:
                    pending.extend(entry.path for entry in entries)
        except OSError:
            continue  # a fetch renames and removes its own files while it is read
    return total


class PrewarmBound:
    """The bound of one dependency preparation: its ceiling, and the bound of each item.

    ``owner`` merges into the recreator's namespace what the transport reads
    (daily_dependency_git.item_progress): the ceiling's end, its clock, its measure.
    """

    def __init__(self, recreator, transport, ceiling: dict, *, clock=time.monotonic, measure=None,
                 poll: float = PREWARM_POLL_SECONDS):
        self.recreator, self.transport, self.ceiling, self.poll = recreator, transport, ceiling, poll
        self.start = clock()
        self.end = self.start + ceiling["seconds"]
        self.owner = {**recreator, "_dependency_deadline": self.end, "_dependency_clock": clock,
                      "_dependency_ceiling": ceiling["seconds"],
                      "_dependency_measure": measure or cargo_home_progress_bytes}

    def item(self, label: str, paths=()):
        """One item's progress bound, for an owner that supervises its own child."""
        self.transport["ceiling_left"](self.owner, label)
        return self.transport["item_progress"](self.owner, label, paths)

    def run(self, label: str, function, *paths: Path):
        """Run ``function`` (an in-process tree copy) as one item, watching ``paths``."""
        watch = self.item(label, paths)
        done, outcome = threading.Event(), {}

        def work():
            try:
                outcome["value"] = function()
            except BaseException as error:  # noqa: BLE001 - re-raised by the waiter
                outcome["error"] = error
            finally:
                done.set()

        watch.begin()
        threading.Thread(target=work, name="trust-prewarm-item", daemon=True).start()
        try:
            while not done.wait(self.poll):
                watch.check(label)
        except self.recreator["_SubmoduleStalled"] as error:
            raise Refused(f"dependency preparation ended {label}: {error}") from error
        if "error" in outcome:
            raise outcome["error"]
        return outcome["value"]


def prewarm_dependencies(source: Path, work: Path, host: str, output: Path,
                         providers: list[Path], cargo_input: Path | None, policy_engine: Path, *,
                         object_caches: dict[str, Path] | None = None, ceiling_seconds: int | None = None,
                         ceiling_only: bool = False, clock=time.monotonic, measure=None,
                         poll: float = PREWARM_POLL_SECONDS, checkout_cache_specs=()) -> None:
    """Fetch only, using the archive-authenticated native seed and existing owners.

    ``object_caches`` (canonical GitHub URL -> repository) are the repositories a host
    declared for its first-party gitlinks; the locked commits they hold are taken from
    them as checkout closures. The ceiling is computed here, at the start; a caller that
    gave its supervisor ``ceiling_seconds`` must find the same number, and
    ``ceiling_only`` writes the ceiling to ``output`` and fetches nothing.
    ``checkout_cache_specs`` (URL#COMMIT=/absolute/repository) let Agh read one exact
    locked commit's checkout objects from that repository (prepare_profile).
    """
    helper = source / "scripts/daily_dependency_git.py"
    helper_bytes = helper.read_bytes()
    helper_sha256 = hashlib.sha256(helper_bytes).hexdigest()
    transport_owner = {"__file__": str(helper), "__name__": "daily_dependency_transport"}
    exec(compile(helper_bytes, str(helper), "exec"), transport_owner)
    if file_hash(helper) != helper_sha256:
        raise Refused("dependency transport source changed while loading")
    loader_path = source / "scripts/seed_custody_source.py"
    loader_owner, loader_sha256 = transport_owner["source_owner"](loader_path, "daily_dependency_source_loader")
    owner_inputs = {str(helper): helper_sha256, str(loader_path): loader_sha256}
    relative_owners = ("scripts/seed_staircase.py", "scripts/bootstrap_dependency_closure.py",
        "scripts/mint_seed_support.py", "scripts/recreate_bootstrap.py", "scripts/source_working_cache.py", "scripts/daily_registry_proxy.py",
        "src/bootstrap/stage0_identity.py", "scripts/lib/seed_linux.py", "scripts/lib/seal_content_identity.py")
    expected_owners = {name: file_hash(source / name) for name in relative_owners}
    policy_file = policy_engine / "bin/pub-relock"
    if policy_file.is_symlink() or not policy_file.is_file():
        raise Refused("dependency preparation needs publication's regular config policy owner")
    policy_file = policy_file.resolve(strict=True)
    policy_sha256 = file_hash(policy_file)
    source_loader = loader_owner["BoundSourceLoader"](source, expected_owners,
        extra_sources={str(policy_file): policy_sha256})
    def load_owner(path, name):
        namespace, actual = bound_dependency_owner(source_loader, path, name)
        owner_inputs[str(path)] = actual
        return namespace
    staircase = load_owner(source / "scripts/seed_staircase.py", "daily_seed_owner")
    closure = load_owner(source / "scripts/bootstrap_dependency_closure.py", "daily_fetch_owner")
    mint = load_owner(source / "scripts/mint_seed_support.py", "daily_cache_owner")
    recreator = load_owner(source / "scripts/recreate_bootstrap.py", "daily_transport_owner")
    identity_path = source / "src/bootstrap/stage0_identity.py"
    owner_inputs[str(identity_path)] = recreator["_IDENTITY_SOURCE_SHA256"]
    policy = load_owner(policy_file, "daily_fetch_config_policy")
    pin = source / "src/stage0"
    pins = staircase["read_stage0_pins"](pin)
    if host != staircase["host_triple"]():
        raise Refused("dependency preparation requires the actual native pinned seed host")
    seed = work / "seed"
    cache = work / "cargo-home"
    for directory in (cache, work / "home", work / "git-bin", work / "mint-inputs", work / "unused-target"):
        if directory.is_symlink() or (directory.exists() and not directory.is_dir()):
            raise Refused(f"dependency Cargo home and support directories must be owned non-symlink directories: {directory}")
    # The source's Cargo configuration is refused before anything reads the manifest graph
    # it would steer, the ceiling's census of the owner locks included.
    environment = recreator["_provenance_git_environment"]()
    home = work / "home"
    git_bin = work / "git-bin"
    environment["HOME"] = str(home)
    environment.update(CARGO_HOME=str(cache), RUSTC=str(seed / "bin/trustc"),
                       CARGO_TARGET_DIR=str(work / "unused-target"),
                       CARGO_BUILD_TARGET_DIR=str(work / "unused-target"),
                       CARGO_NET_GIT_FETCH_WITH_CLI="true", CARGO_REGISTRIES_CRATES_IO_PROTOCOL="sparse",
                       RUSTC_WRAPPER="", RUSTC_WORKSPACE_WRAPPER="",
                       CARGO_ENCODED_RUSTFLAGS="", CARGO_ENCODED_RUSTDOCFLAGS="",
                       CARGO_UNSTABLE_HOST_CONFIG="false",
                       PATH=os.pathsep.join((str(git_bin), str(seed / "bin"), environment["PATH"])))
    requested_offline = os.environ.get("CARGO_NET_OFFLINE")
    if requested_offline is not None and requested_offline not in {"true", "false"}:
        raise Refused("dependency offline environment is not an explicit Cargo boolean")
    offline = requested_offline == "true"
    configs = cargo_config_inputs(source, environment)
    for config in configs:
        if configs[config] is None:
            continue
        value = tomllib.loads(Path(config).read_text())
        http = value.get("http", {})
        net = value.get("net", {})
        if not isinstance(http, dict) or not isinstance(net, dict):
            raise Refused("dependency Cargo HTTP/network configuration is malformed")
        if any(key not in {"timeout", "low-speed-limit", "multiplexing"} for key in http):
            raise Refused("dependency Cargo configuration has unsupported HTTP routing/TLS authority")
        if net.get("offline") is True:
            offline = True
        # [env] is judged by name by the one shared policy below (publication's
        # config_refusals: loader, compiler/toolchain and credential/network
        # families refused, a malformed entry refused), never wholesale here: a
        # blanket refusal stopped every tick from 2026-11-16 22:21Z, when Trust's
        # own .cargo/config.toml gained [env] RUST_MIN_STACK (72166f7901), a
        # variable that reaches only a running Rust program and no fetch.
        if value.get("registry", {}).get("default", "crates-io") != "crates-io" or any(
                name != "crates-io" for name in value.get("registries", {})):
            raise Refused("dependency Cargo config has unsupported registry authority")
        crates_io = value.get("registries", {}).get("crates-io", {})
        if any(key not in {"protocol"} for key in crates_io):
            raise Refused("dependency Cargo config changes the canonical crates.io index")
        # Publication's export policy refuses target relocation. This lane
        # never builds, and its absolute owned target is an effective native
        # environment override checked below. Keep the original config bound.
        policy_value = value
        build = value.get("build", {})
        if not isinstance(build, dict):
            raise Refused("dependency Cargo build configuration is malformed")
        if "target-dir" in build:
            if not isinstance(build["target-dir"], str) or not build["target-dir"]:
                raise Refused("dependency Cargo target directory is malformed")
            policy_value = {**value, "build": {k: v for k, v in build.items() if k != "target-dir"}}
        refusals = policy["config_refusals"]("dependency Cargo config", policy_value)
        if refusals:
            raise Refused("dependency Cargo config contains unsupported execution/source/lock authority: "
                          + "; ".join(refusals))
    if offline:
        environment["CARGO_NET_OFFLINE"] = "true"
    ceiling = prewarm_ceiling(source, cache, cargo_input, closure, recreator, transport_owner,
                              measure or cargo_home_progress_bytes, len(mint["CARGO_HOME_INPUT_TREES"]))
    print(describe_ceiling(ceiling), file=sys.stderr, flush=True)
    if ceiling_seconds is not None and ceiling_seconds != ceiling["seconds"]:
        raise Refused(f"the dependency preparation's ceiling is {ceiling['seconds']} s, not the "
                      f"{ceiling_seconds} s its supervisor was given: an input changed in between")
    if ceiling_only:
        atomic_json(output, ceiling)
        return
    bound = PrewarmBound(recreator, transport_owner, ceiling, clock=clock, measure=measure, poll=poll)
    object_caches = {transport_owner["canonical_url"](url): Path(path)
                     for url, path in (object_caches or {}).items()}
    # Existing extractions are authenticated before executing any of their bytes.
    if not seed.exists():
        # The recreator has already materialized/validated these exact archives.
        dist = source / "bootstrap/trust-stage0/dist" / pins["compiler_date"]
        staircase["seed_sysroot"](dist, pin, seed)
    pinned = staircase["pinned_seed_record"](seed, source)
    def bind_seed_support():
        for path, actual in staircase["support_source_inputs"]().items():
            relative = Path(path).relative_to(source).as_posix()
            if expected_owners.get(relative) != actual:
                raise Refused("seed support differs from the selected source owner")
            owner_inputs[path] = actual
    bind_seed_support()
    source_loader.recheck()
    driver = seed / "bin/targo"
    for binary in (driver, seed / "bin/trustc"):
        if staircase["native_kind"](binary) not in {"macho", "elf"}:
            raise Refused("pinned dependency drivers must be their native archive binaries")
    runtime = mint["foreign_load_commands"](seed, providers)
    admission = mint["compiler_identity"](seed, "pinned dependency seed")
    if (admission.get("commit") != pins["compiler_git_commit_hash"] or admission.get("host") != host
            or admission.get("date") != pins["compiler_date"] or admission.get("lineage") != "trust"):
        raise Refused(f"pinned dependency seed identity refused: {admission}")
    if not cache.exists():
        initial = mint["cargo_home_inputs"](cargo_input, cache, trees=PREWARM_COPIED_TREES, run=bound.run)
        atomic_json(work / "initial-cache.json", initial)
    else:
        # A reused home holds the Git checkouts Cargo made in it. Cargo makes them by a local
        # clone of git/db, which hardlinks the database's objects, and validate_bare_db
        # refuses any database file with another link: a home used once could never be
        # revalidated (the 5062 relaunch, 2026-11-15). They are derived state, no tree the
        # mint imports (CARGO_HOME_INPUT_TREES) and nothing its handoff copies, so they go
        # before anything validates or uses the home. A database file linked from anywhere
        # else still refuses.
        for path in (cache / "git", cache / "git/checkouts"):
            if path.is_symlink() or (path.exists() and not path.is_dir()):
                raise Refused(f"reused dependency Cargo home has a linked or non-directory {path}")
        if (cache / "git/checkouts").exists():
            shutil.rmtree(cache / "git/checkouts")
    for name in mint["CARGO_HOME_INPUT_TREES"]:
        tree = cache / name
        if tree.exists() or tree.is_symlink():
            fingerprint(tree)  # Reject special files and escaping links before use.
    # Agh alone acquires Git source objects. The seed's Git CLI will be a
    # local-only exact source-store adapter, never a credential helper.
    recreator["_reject_local_git_execution_authority"](source)
    home.mkdir(exist_ok=True)
    git_bin.mkdir(exist_ok=True)
    fixed_git = recreator["_controlled_git_command"]([])
    git_environment = recreator["_submodule_materialization_environment"]()
    git_environment["GIT_TERMINAL_PROMPT"] = "0"
    # Cache Git configs are data, never additional transport/executable policy.
    allowed = {"core.repositoryformatversion", "core.bare", "core.filemode", "core.logallrefupdates",
               "core.ignorecase", "core.precomposeunicode", "remote.origin.url", "remote.origin.fetch",
               "extensions.objectformat"}
    git_configs = [*(cache / "git/db").glob("*/config"),
                   *(cache / "registry/index").glob("*/.git/config")]
    for config in sorted(git_configs):
        if config.is_symlink() or not config.is_file():
            raise Refused("dependency cache Git config must be a regular file")
        result = subprocess.run([fixed_git[0], "config", "--no-includes", "--file", str(config),
                                 "--null", "--list"], env=git_environment,
                                capture_output=True, check=True, timeout=30)
        for key, _value in recreator["_parse_git_config_records"](result.stdout, config.parent, "cache"):
            if key.lower() not in allowed:
                raise Refused("dependency cache Git config contains unsupported authority")
        for relative in ("objects/info/alternates", "objects/info/http-alternates", "info/grafts"):
            if (config.parent / relative).exists() or (config.parent / relative).is_symlink():
                raise Refused("dependency cache Git objects name external or replacement custody")
    if providers:
        environment["DYLD_LIBRARY_PATH"] = os.pathsep.join(str(p) for p in providers)
    version = subprocess.run([str(driver), "--unverified", "--version"], env=environment,
                             capture_output=True, text=True, timeout=60, check=True).stdout.strip()
    if not version.startswith("targo "):
        raise Refused(f"pinned dependency driver is not genuine Targo: {version!r}")
    proxy_file = source / "scripts/daily_registry_proxy.py"
    proxy_owner = load_owner(proxy_file, "daily_registry_transport")
    proxy_sha256 = owner_inputs[str(proxy_file)]
    deadline = bound.end
    # A cut can select an older source owner's helper: it is given only the options in use.
    profile_options = {name: value for name, value in (
        ("object_caches", object_caches), ("input_home", cargo_input),
        ("checkout_cache_specs", tuple(checkout_cache_specs))) if value}
    profile_path, profile = transport_owner["prepare_profile"](
        source, work, cache, closure, bound.owner, environment, deadline=deadline, **profile_options)
    shim = git_bin / "git"
    script = "#!/bin/sh\nexec " + shlex.join(
        [sys.executable, "-I", "-B", str(helper), "--policy", str(profile_path), "--"]) + ' "$@"\n'
    if shim.exists() and (shim.is_symlink() or not shim.is_file()):
        raise Refused("dependency Git shim is not an owned regular file")
    shim.write_text(script)
    shim.chmod(0o700)
    transport = {"git": fixed_git[0], "git_sha256": file_hash(Path(fixed_git[0])),
                 "shim_sha256": file_hash(shim), "helper": str(helper), "helper_sha256": helper_sha256,
                 "python": str(Path(sys.executable).resolve()), "python_sha256": file_hash(Path(sys.executable).resolve()),
                 "profile": str(profile_path), "profile_sha256": file_hash(profile_path),
                 "acquisitions": profile["acquisitions"],
                 "scope": "Agh exact-commit preacquisition; local-only Cargo Git; native sparse crates.io"}
    gate = proxy_owner["RegistryHttpGate"](deadline, offline=offline)
    try:
        with gate:
            fetch_environment = gate.environment(environment)
            configuration = subprocess.run([str(driver), "-Z", "unstable-options", "config", "get",
                "http.proxy", "--format", "json"], env=fetch_environment, cwd=source,
                capture_output=True, text=True, timeout=min(30, max(0.01, deadline - time.monotonic())), check=True)
            if json.loads(configuration.stdout) != {"http": {"proxy": gate.url}}:
                raise Refused("native pinned resolver did not retain the bound HTTP capability")
            target_configuration = subprocess.run([str(driver), "-Z", "unstable-options", "config", "get",
                "build.target-dir", "--format", "json"], env=fetch_environment, cwd=source,
                capture_output=True, text=True, timeout=min(30, max(0.01, deadline - time.monotonic())), check=True)
            if json.loads(target_configuration.stdout) != {"build": {"target-dir": str(work / "unused-target")}}:
                raise Refused("native pinned resolver did not retain its owned target directory")
            acquire = closure.get("acquire_dependency_inputs")
            acquisition = None
            if callable(acquire):
                acquisition = acquire(source, str(driver), fetch_environment,
                                      deadline=deadline, progress=bound.item).report()
                report = acquisition
            else:
                # A selected older cut owns its helper API. Preserve its preparation
                # ceremony instead of passing an unsupported new flag or forging a check.
                report = closure["dependency_closure"](source, str(driver), fetch_environment, prepare=True,
                                                       deadline=deadline, progress=bound.item)
            # Prove the exact input form mint imports, without registry/src or Git
            # checkouts left by online fetch masking an absent archive/object database.
            handoffs = work / "mint-inputs"
            handoffs.mkdir(exist_ok=True)
            handoff = Path(tempfile.mkdtemp(prefix="attempt-", dir=handoffs)) / "cargo-home"
            handoff_manifest = mint["cargo_home_inputs"](cache, handoff, run=bound.run)
            replay = closure["dependency_closure"](source, str(driver), {**fetch_environment, "CARGO_HOME": str(handoff)},
                                                 deadline=deadline, progress=bound.item)
            if closure["_snapshot"]([Path(p) for p in report["source_inputs_sha256"]]) != report["source_inputs_sha256"]:
                raise Refused("dependency source/config/driver changed during handoff replay")
            if acquisition is not None:
                # Only the actual offline handoff run carries the readiness schema.
                # Retain acquisition separately; it cannot satisfy a readiness reader.
                report = {**replay, "source_inputs_sha256": dict(replay["source_inputs_sha256"]),
                          "input_acquisition": acquisition}
            if staircase["pinned_seed_record"](seed, source) != pinned:
                raise Refused("pinned dependency seed changed during fetch")
            bind_seed_support()
            if cargo_config_inputs(source, environment) != configs:
                raise Refused("dependency Cargo configuration changed during fetch")
            if (file_hash(Path(fixed_git[0])) != transport["git_sha256"]
                    or file_hash(shim) != transport["shim_sha256"]
                    or file_hash(helper) != helper_sha256
                    or file_hash(Path(transport["python"])) != transport["python_sha256"]
                    or file_hash(profile_path) != transport["profile_sha256"]
                    or file_hash(proxy_file) != proxy_sha256
                    or file_hash(policy_file) != policy_sha256
                    or mint["foreign_load_commands"](seed, providers) != runtime):
                raise Refused("dependency transport or native runtime changed during fetch")
            source_loader.recheck()
            owner_inputs.update({str(source / path) if not Path(path).is_absolute() else path: digest
                                 for path, digest in source_loader.executed.items()})
            if any(file_hash(Path(path)) != expected for path, expected in owner_inputs.items()):
                raise Refused("a captured dependency source owner changed during fetch")
            report["source_inputs_sha256"].update(owner_inputs)
            report["source_inputs_sha256"].update(profile["source_inputs_sha256"])
            report["source_inputs_sha256"].update({str(helper): helper_sha256,
                str(profile_path): transport["profile_sha256"], str(shim): transport["shim_sha256"],
                str(proxy_file): proxy_sha256,
                transport["python"]: transport["python_sha256"]})
            report.update(seed=pinned, compiler=admission, runtime=runtime, targo_version=version,
                          transport=transport,
                          config_policy={"path": str(policy_file), "sha256": policy_sha256},
                          driver_sha256=file_hash(driver), cargo_home=str(handoff),
                          handoff_manifest=handoff_manifest, handoff_offline_replay=replay, ceiling=ceiling,
                          cache_trees={name: fingerprint(handoff / name) if (handoff / name).exists() else None
                                       for name in mint["CARGO_HOME_INPUT_TREES"]})
            validate_preparation_fetches(report)
    except BaseException as error:
        # This is an attempted transport observation, never cache readiness.
        atomic_json(profile_path.parent / "registry-http-failure.json", {
            "status": "FAILED_OR_INCOMPLETE", "error_type": type(error).__name__,
            "proxy_sha256": proxy_sha256, "profile_sha256": transport["profile_sha256"],
            "allowed_targets": sorted(proxy_owner["ALLOWED_TARGETS"]),
            "events": list(gate.events),
            "workers_settled": not gate.thread.is_alive() and not any(t.is_alive() for t in gate.workers),
            "scope": "Failed attempt only; no source/cache/compiler/proof readiness"})
        raise
    report["registry_transport"] = {"path": str(proxy_file), "sha256": proxy_sha256,
        "allowed_targets": sorted(proxy_owner["ALLOWED_TARGETS"]), "proxy_url": gate.url, "offline": offline,
        "events": list(gate.events), "workers_settled": True,
        "scope": "Native TLS CONNECT only; GitHub/plain HTTP/other hosts denied before outbound"}
    atomic_json(output, report)


def validate_preparation_fetches(report: dict) -> None:
    """Judge actual acquisition and handoff observations, including older cut replies."""
    if (report.get("schema") != "trust.bootstrap-offline-dependency-closure.v1"
            or not report.get("source_inputs_sha256")):
        raise Refused("dependency owner did not establish actual locked offline fetch readiness")
    replay = report.get("handoff_offline_replay", {})
    if replay.get("schema") != report["schema"] or not replay.get("source_inputs_sha256"):
        raise Refused("dependency handoff lacks its actual offline replay from safe cache trees")
    acquisition = report.get("input_acquisition")
    if acquisition is None:
        # Existing selected cuts and resumed receipts retain their established three-pass law.
        modes = {}
        for row in report.get("completed_fetches", []):
            modes.setdefault(row.get("manifest"), []).append(row.get("offline"))
        if not modes or any(value != [False, True] for value in modes.values()):
            raise Refused("dependency owner did not establish actual locked offline fetch readiness")
        expected = [{"manifest": name, "offline": True} for name in modes]
    else:
        manifests = acquisition.get("manifests")
        policy = acquisition.get("manifest_policy_sha256")
        if (acquisition.get("schema") != "trust.bootstrap-dependency-acquisition.v1"
                or not acquisition.get("source_inputs_sha256")
                or not isinstance(manifests, list) or not manifests
                or any(not isinstance(name, str) or not name for name in manifests)
                or len(set(manifests)) != len(manifests)
                or not isinstance(policy, str) or re.fullmatch(r"[0-9a-f]{64}", policy) is None
                or acquisition.get("completed_fetches") != [
                    {"manifest": name, "offline": False} for name in manifests]
                or any(observed.get("manifests") != manifests
                       or observed.get("manifest_policy_sha256") != policy
                       for observed in (report, replay))):
            raise Refused("dependency acquisition and handoff do not bind the same ordered manifest/policy inputs")
        expected = [{"manifest": name, "offline": True} for name in manifests]
        if report.get("completed_fetches") != expected:
            raise Refused("dependency readiness was not established by the final offline handoff")
    if replay.get("completed_fetches") != expected:
        raise Refused("dependency handoff lacks its actual offline replay from safe cache trees")


def validate_dependency_preparation(preparation: dict) -> None:
    report = read_json(Path(preparation["report"]))
    validate_preparation_fetches(report)
    inputs = {**report.get("input_acquisition", {}).get("source_inputs_sha256", {}),
              **report["source_inputs_sha256"], **report["handoff_offline_replay"]["source_inputs_sha256"]}
    inputs[report["config_policy"]["path"]] = report["config_policy"]["sha256"]
    for name, expected in inputs.items():
        path = Path(name)
        if (file_hash(path) if path.exists() else None) != expected:
            raise Refused(f"dependency preparation source/config/driver input changed: {path}")
    cache = Path(preparation["cargo_home"])
    if cache.is_symlink() or not cache.is_dir():
        raise Refused("dependency preparation cache lost its owned directory")
    for name, expected in report["cache_trees"].items():
        path = cache / name
        if (fingerprint(path) if path.exists() or path.is_symlink() else None) != expected:
            raise Refused(f"dependency preparation cache input changed: {path}")


def trust_checkout(label: str) -> bool:
    """Whether a synchronize label names a checkout of the Trust source.

    Those are the snapshot the cut builds and the train's landing worktree (`landing-<step>`),
    the only ones with the first-party gitlinks a --source-object-cache or --owned-object-cache
    declares.
    """
    return label == "source" or label.startswith("landing-")


class Runner:
    def __init__(self, args: argparse.Namespace, execute: Callable = command, train=None):
        self.args = args
        # A fleet train's two seams: before_cut(runner) and after_cut(runner, staged, mint).
        self.train = train
        self.repo = args.repo.resolve(strict=True)
        self.state = args.state_root.resolve()
        if self.state.is_relative_to(self.repo):
            raise Refused("--state-root must be outside the source checkout")
        self.source = self.state / "source"
        self.execute = execute
        self.consumer_repos = consumer_mappings(args.consumer)
        self.env = dict(os.environ)
        self.elan_home = selected_elan_home(args.elan_home)
        if self.elan_home is not None:
            self.env["ELAN_HOME"] = str(self.elan_home)
        else:
            self.env.pop("ELAN_HOME", None)
        # Ambient wrappers, flags and gate waivers do not configure a release lane.
        for key in list(self.env):
            if (key.startswith(("TRUST_", "CARGO_ENCODED_", "CARGO_TARGET_"))
                    or key in {"RUSTFLAGS", "RUSTDOCFLAGS", "RUSTC", "RUSTDOC", "CARGO",
                               "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER", "RUSTUP_TOOLCHAIN",
                               "TRUST_BUILD_LOCK_TOKEN", "BUILD_SLOT_HELD", "CARGO_BUILD_JOBS",
                               "GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE", "GIT_OBJECT_DIRECTORY",
                               "GIT_ALTERNATE_OBJECT_DIRECTORIES", "GIT_COMMON_DIR", "GIT_NAMESPACE"}):
                self.env.pop(key, None)
        self.env.update(RUSTUP_HOME=str(self.state / "rustup"),
                        TRUST_TOOLCHAIN_HOME=str(self.state / "toolchains"))
        if args.cargo_home:
            self.env["CARGO_HOME"] = str(args.cargo_home.resolve(strict=True))
        self.record: dict = {}
        self.checkpoint: dict = {}
        self.log_index = 0
        self.record_lock = threading.RLock()
        # The Agh every acquisition of this run selects (keep_agh): a train's tick keeps one
        # for its reader and each of its runs, and a run of its own keeps one in run().
        self.agh: dict | None = getattr(train, "agh", None)
        self.thread_state = threading.local()
        self.cancelled = threading.Event()
        self.publication_source: Path | None = None
        self.publication_commit: str | None = None
        # Whether each build-slot this run selects takes the train's claim words.
        self.slot_claims: dict[str, bool] = {}

    def claim_words(self, step: str, *, sized: bool = False) -> list[str]:
        """The train's Release-rank ledger claim for one build-slot step, or nothing.

        A cut runs its own snapshot's build-slot, and a resumed cut's may predate --rank,
        --claim-key and --wide: it would refuse them as unknown options and start nothing.
        So the selected build-slot is asked once (`--capabilities`, which an older copy
        refuses the same way) and given the words only when it answers build-slot-claim-v1.
        Where aterm's capacity ledger admits, the claim is a Release holder `aterm pkg
        capacity` shows as trust-train:<step>. Every unsized train step compiles (the
        publisher builds itself, the push runs the pre-push hook's builds), so it asks
        for the host's cores (--wide), as the slot pool's uncapped borrowing gives it; a
        step that declares its own size (`sized`, the fetch-only prewarm) keeps it. On
        the slot pool the words change nothing."""
        slot = str(self.slot)
        if slot not in self.slot_claims:
            try:
                probe = subprocess.run([slot, "--capabilities"], env=self.env, stdin=subprocess.DEVNULL,
                                       capture_output=True, timeout=60)
                self.slot_claims[slot] = (probe.returncode == 0
                                          and probe.stdout == (BUILD_SLOT_CLAIM_WORDS + "\n").encode())
            except (OSError, subprocess.SubprocessError):
                self.slot_claims[slot] = False
        if not self.slot_claims[slot]:
            return []
        return ["--rank", "release", "--claim-key", train_claim_key(step), *([] if sized else ["--wide"])]

    def save(self) -> None:
        with self.record_lock:
            self.record["updated_at"] = now()
            atomic_json(self.invocation / "status.json", self.record)
            atomic_json(self.state / "latest.json", self.record)

    def write_json(self, path: Path, value: dict) -> None:
        with self.record_lock:
            atomic_json(path, value)

    def save_consumer(self, name: str, value: dict) -> None:
        with self.record_lock:
            self.record["consumers"][name] = copy.deepcopy(value)
            self.save()

    def last_step(self) -> dict:
        return copy.deepcopy(getattr(self.thread_state, "step", {}))

    def publication(self) -> tuple[Path, str]:
        # Called before starting consumer threads; a run uses one immutable owner.
        if self.publication_source is None:
            repository = self.args.publication_repo or self.repo.parent / "publication"
            engine = self.state / "publication-source"
            commit = self.snapshot(repository.resolve(strict=True), engine, "publication")
            self.synchronize(engine, "publication")
            cleanup_api(engine)
            self.publication_source, self.publication_commit = engine, commit
            self.record["cleanup_policy_engine"] = {"commit": commit, "path": str(engine),
                                                     "reader_sha256": file_hash(engine / "bin/pub")}
            self.save()
        return self.publication_source, self.publication_commit

    def call(self, name: str, argv: list[str], cwd: Path | None = None,
             *, heavy: bool = False, env: dict | None = None, timeout: int | None = None,
             progress=None, admission: list[str] | None = None) -> str:
        if progress is not None and heavy:
            raise Refused(f"{name}: a build-slot step is bounded by its own owner, not by a progress bound")
        if admission and not heavy:
            raise Refused(f"{name}: admission words declare a build-slot step's needs; this step takes no build-slot")
        selected_env = env or self.env
        consumer_check = name.endswith("-consumer-check")
        bootstrap = next((Path(arg) for arg in argv if Path(arg).name == "recreate_bootstrap.py"), None)
        if bootstrap:
            selected_env = bootstrap_environment(selected_env, bootstrap)
            if heavy:
                argv = [str(self.python), str(Path(__file__).resolve()), "_admitted-bootstrap", *argv]
        cleanup_owner = self.publication_source
        if heavy:
            cleanup_owner, _ = self.publication()
        with self.record_lock:
            self.log_index += 1
            log = self.invocation / f"{self.log_index:03d}-{name}.log"
        result_file = None
        if heavy:
            result_file = log.with_suffix(".result.json")
            argv = owned_step_argv(self.slot, self.python, Path(__file__).resolve(),
                                   cleanup_owner, result_file, timeout, argv,
                                   admission=[*(admission or []),
                                              *self.claim_words(name, sized=bool(admission))])
        step = {"name": name, "argv": argv, "cwd": str(cwd or self.source),
                "log": str(log), "status": "running", "started_at": now()}
        if timeout is not None:
            step["timeout_seconds"] = timeout
        bound = {}
        if progress is not None:
            step["progress_bound"] = {"stall_window_seconds": progress.window,
                                      "floor_bytes_per_second": progress.floor}
            bound = {"progress": progress}
        if result_file:
            step["result_file"] = str(result_file)
        with self.record_lock:
            self.record["steps"].append(step)
            self.thread_state.step = step
            self.save()
        try:
            result = self.execute(argv, cwd or self.source, selected_env, log,
                                  timeout=None if heavy else timeout, cleanup_owner=cleanup_owner,
                                  cancel_event=self.cancelled, **bound)
            if result_file:
                if not result_file.exists():
                    raise Refused("owned command exited without its result receipt")
                if consumer_check:
                    detail, identity = read_json_artifact(result_file, unique_keys=True)
                    step.update(owned_result=detail, owned_result_identity=identity)
                else:
                    detail = read_json(result_file)
                if detail.get("exit_code") != 0 or detail.get("timed_out") or detail.get("interrupted"):
                    raise CommandFailed("owned command did not complete successfully", detail.get("exit_code"), detail.get("timed_out", False))
            if consumer_check:
                step["log_identity"] = fingerprint(log)
        except BaseException as error:
            with self.record_lock:
                if result_file and result_file.exists():
                    if consumer_check:
                        with contextlib.suppress(ValueError, Refused):
                            detail, _ = read_json_artifact(result_file, unique_keys=True)
                            bind_owned_failure(step, error, detail)
                    else:
                        detail = read_json(result_file)
                        bind_owned_failure(step, error, detail)
                step.update(status="failed", error=str(error), finished_at=now())
                if isinstance(error, CommandFailed):
                    step.update(exit_code=error.exit_code, timed_out=error.timed_out)
                elif isinstance(error, (KeyboardInterrupt, InterruptedError)):
                    step.update(interrupted=True, exit_code=getattr(error, "child_exit_code", None),
                                signal=getattr(error, "signal", signal.SIGINT if isinstance(error, KeyboardInterrupt) else None))
                self.thread_state.step = step
                self.save()
            if step.get("owned_result", {}).get("interrupted") and isinstance(error, CommandFailed):
                raise InterruptedError("owned gate interrupted; its process tree was cleaned by publication") from error
            raise
        with self.record_lock:
            if result_file and result_file.exists() and "owned_result" not in step:
                step["owned_result"] = read_json(result_file)
            step.update(status="passed", exit_code=0, finished_at=now())
            self.thread_state.step = step
            self.save()
        # command() puts one JSON header before the owner's stdout.
        return result.partition("\n")[2].strip()

    def git_owner(self) -> dict:
        if not hasattr(self, "_managed_git_owner"):
            self._managed_git_owner = runpy.run_path(
                str(Path(__file__).with_name("recreate_bootstrap.py")), run_name="daily_managed_git_owner")
        return self._managed_git_owner

    def git(self, name: str, cwd: Path, *argv: str, env: dict | None = None,
            git_command: list[str] | None = None) -> str:
        owner = self.git_owner()
        selected_env = owner["_provenance_git_environment"]() if env is None else env
        selected_git = owner["_controlled_git_command"]([]) if git_command is None else git_command
        result = self.call(name, [*selected_git, *argv], cwd, env=selected_env)
        log = Path(self.last_step()["log"])
        if log.stat().st_size >= MAX_QUERY_BYTES:
            raise Refused(f"Git query output exceeds the capture bound; inspect the retained log: {log}")
        return result

    def clean(self, path: Path) -> None:
        status = self.git("source-clean", path, "status", "--porcelain",
                          "--untracked-files=normal", "--ignore-submodules=none")
        if status:
            raise Refused(f"refusing to move or build a dirty managed worktree: {path}")

    def snapshot(self, repository: Path, destination: Path, label: str) -> str:
        # Source custody must not import the developer clone's execution config,
        # hooks, object alternates or live object store. Only read its origin URL;
        # fetch the selected commit into a new, independently owned repository.
        recreator = self.git_owner()
        fixed_git = recreator["_controlled_git_command"]([])
        git_env = recreator["_provenance_git_environment"]()
        def query(name: str, cwd: Path, *argv: str) -> str:
            return self.git(name, cwd, *argv, env=git_env, git_command=fixed_git)
        common = query("common-dir", repository, "rev-parse", "--git-common-dir")
        common_path = (repository / common).resolve()
        # The owner's include-free reader keeps raw caller config out of logs.
        urls = [value for _scope, key, value in recreator["_repository_git_config_records"](repository)
                if key == "remote.origin.url"]
        if len(urls) != 1 or not urls[0] or any(c in urls[0] for c in "\r\n\0"):
            raise Refused("snapshot requires one literal origin URL")
        origin = urls[0]
        if "::" in origin or origin.startswith("-"):
            raise Refused("snapshot origin must not select a Git remote helper")
        # GitHub SSH clone spellings select the same owner-routed Agh source.
        for prefix in ("git@github.com:", "ssh://git@github.com/"):
            if origin.startswith(prefix):
                origin = "https://github.com/" + origin[len(prefix):]
                break
        if "://" in origin:
            if origin.partition(":")[0] not in {"https", "file"}:
                raise Refused("snapshot origin uses an unsupported transport")
            if "?" in origin or "#" in origin:
                raise Refused("snapshot origin must not contain a query or fragment")
            if "@" in origin.partition("://")[2].partition("/")[0]:
                raise Refused("snapshot origin must not embed credentials")
        elif not Path(origin).is_absolute() and ":" not in origin:
            origin = str((repository / origin).resolve())
        elif not Path(origin).is_absolute():
            raise Refused("snapshot requires HTTPS or an explicit local origin")
        object_format = query("object-format", repository, "rev-parse", "--show-object-format")
        if object_format not in {"sha1", "sha256"}:
            raise Refused("unsupported snapshot Git object format")
        marker = destination.with_name(destination.name + ".owner.json")
        ownership = {"schema": SCHEMA, "snapshot_kind": "independent-git-v1",
                     "caller_git_common_dir": str(common_path), "origin": origin,
                     "object_format": object_format, "path": str(destination)}
        if destination.is_symlink():
            raise Refused(f"managed worktree path must not be a symlink: {destination}")
        if destination.exists():
            if not marker.exists() or read_json(marker) != ownership:
                raise Refused(f"existing worktree is not owned by this independent snapshot; use a fresh --state-root, retaining the old state: {destination}")
            self.snapshot_custody(destination, origin, query)
            if query("source-clean", destination, "status", "--porcelain", "--untracked-files=normal", "--ignore-submodules=none"):
                raise Refused(f"refusing to move or build a dirty managed worktree: {destination}")
        elif marker.exists() or marker.is_symlink():
            raise Refused("snapshot marker without its repository; use a fresh --state-root, retaining the old state")
        else:
            destination.parent.mkdir(parents=True, exist_ok=True)
            query("create-source", destination.parent, "init", "--quiet", "--template=",
                  "--object-format=" + object_format, str(destination))
            query("source-origin", destination, "remote", "add", "origin", origin)
            self.snapshot_custody(destination, origin, query)
        # Suppress origin's default refmap as well as FETCH_HEAD: an explicit
        # destination alone still updates matching remote-tracking refs.
        suffix = hashlib.sha256(str(self.state).encode()).hexdigest()[:16]
        ref = f"refs/agh/trust-daily-staging/{suffix}/{label}"
        transport = recreator["_submodule_materialization_environment"]()
        transport["GIT_TERMINAL_PROMPT"] = "0"
        if origin.startswith("https://"):
            def acquire(argv, environment):
                # Bounded by its progress, as the recreator's own acquisitions are: a fetch of
                # main that keeps receiving is not cut at a total (600 s, until 2026-11-16).
                with recreator["_agh_transfer_paths"](destination, environment, self.invocation) as (
                        child_environment, paths):
                    self.call("fetch-main", argv, destination, env=child_environment,
                              progress=recreator["_SubmoduleProgress"](f"Agh's fetch of {label} main", paths))
            acquisition = recreator["_agh_source_fetch"](
                origin, destination, "refs/heads/main", ref, execute=acquire,
            )
            self.write_json(self.invocation / f"{suffix}-{label}-source-acquisition.json", acquisition)
        else:
            # Only an explicit literal local source opens file transport;
            # config rewrites, helpers and shared object stores remain closed.
            self.git("fetch-main", destination, "fetch", "--refmap=", "--no-tags", "--no-write-fetch-head",
                     "--recurse-submodules=no", "origin", f"refs/heads/main:{ref}",
                     env=transport, git_command=[*fixed_git, "-c", "protocol.file.allow=always"])
        commit = query("latest-main", destination, "rev-parse", "--verify", ref + "^{commit}")
        if not re.fullmatch(r"[0-9a-f]{40,64}", commit):
            raise Refused("origin/main did not resolve to a commit")
        named = self.args.source_commit if label == "trust" else None
        if named is not None:
            # A cut holds the commit it started on while main moves: a restart builds
            # that commit again, with its checkpoint and prepared dependencies, and
            # not whatever main's tip has become. The fetch above is the evidence
            # that the named commit is on origin/main; nothing else is selectable.
            if len(named) != len(commit) or not re.fullmatch(r"[0-9a-f]+", named):
                raise Refused(f"--source-commit takes a full lowercase commit id of {len(commit)} hex digits")
            try:
                query("source-commit-on-main", destination, "merge-base", "--is-ancestor", named, commit)
            except CommandFailed as error:
                raise Refused(f"--source-commit {named} is not on origin/main, whose tip is {commit}") from error
            self.record["source_main"], commit = commit, named
        if marker.exists():
            old = query("previous-source", destination, "rev-parse", "HEAD")
            query("source-fast-forward", destination, "merge-base", "--is-ancestor", old, commit)
        # Git checks the snapshot out from the objects just acquired; no working file of the
        # controller or a consumer checkout is read. Its bytes are proven by the source lineage.
        fresh = not marker.exists()
        query("select-main", destination, "-c", "submodule.recurse=false", "checkout", "--detach", commit)
        # A fresh tree holds exactly Git's checkout: nothing untracked and nothing ignored, as the
        # per-file route's final audit required. A reused snapshot keeps its ignored build outputs.
        if fresh and query("snapshot-complete", destination, "status", "--porcelain=v1",
                           "--untracked-files=all", "--ignored", "--ignore-submodules=all"):
            raise Refused(f"a fresh snapshot holds untracked or ignored files after Git's checkout: {destination}")
        self.snapshot_custody(destination, origin, query)
        self.write_json(marker, ownership)
        return commit

    def snapshot_custody(self, destination: Path, origin: str, query: Callable) -> None:
        git_dir = destination / ".git"
        if git_dir.is_symlink() or not git_dir.is_dir():
            raise Refused("snapshot requires its own physical .git directory; use a fresh --state-root")
        for relative in ("commondir", "objects/info/alternates", "objects/info/http-alternates", "info/grafts"):
            if os.path.lexists(git_dir / relative):
                raise Refused("snapshot must not share Git config or live object alternates")
        hooks = git_dir / "hooks"
        if hooks.exists() and (not hooks.is_dir() or any(hooks.iterdir())):
            raise Refused("snapshot must not contain unowned Git hooks")
        for root, directories, files in os.walk(git_dir, followlinks=False):
            for name in directories + files:
                path = Path(root) / name
                info = path.lstat()
                if (not (stat.S_ISREG(info.st_mode) or stat.S_ISDIR(info.st_mode))
                        or (stat.S_ISREG(info.st_mode) and info.st_nlink != 1)
                        or (path.parts[-3:-1] == ("objects", "info") and name in {"alternates", "http-alternates"})):
                    raise Refused("snapshot Git custody contains a nonregular object or shared file")
        # Inspect without includes before status/fetch/checkout can consume config.
        config = query("snapshot-config", destination, "config", "--local", "--no-includes", "--null", "--list")
        safe_core = {"repositoryformatversion", "filemode", "bare", "logallrefupdates", "ignorecase", "precomposeunicode", "symlinks"}
        seen = set()
        for row in config.split("\0"):
            if not row:
                continue
            key, separator, value = row.partition("\n")
            if key in seen:
                raise Refused("snapshot Git configuration contains duplicate authority: " + key)
            seen.add(key)
            if not separator or not (key in {"remote.origin.url", "remote.origin.fetch", "extensions.objectformat"}
                    or (key.startswith("core.") and key[5:] in safe_core)
                    or (key.startswith("submodule.") and key.rsplit(".", 1)[-1] in {"url", "active"})):
                raise Refused("snapshot Git configuration contains unowned authority: " + key)
            if key == "remote.origin.url" and value != origin:
                raise Refused("snapshot origin changed from its ownership binding")
            if key == "remote.origin.fetch" and value != "+refs/heads/*:refs/remotes/origin/*":
                raise Refused("snapshot Git fetch map changed")
        if query("snapshot-origin", destination, "config", "--local", "--no-includes", "--get", "remote.origin.url") != origin:
            raise Refused("snapshot origin changed from its ownership binding")

    def milestone(self, name: str, outputs: list[Path], action: Callable[[], None]) -> None:
        cached = self.checkpoint.get("milestones", {}).get(name)
        # A stage tree's bootstrap source links name this run's snapshot (see fingerprint).
        if cached:
            expected = {str(p): fingerprint(p, self.source) for p in outputs}
            if cached != expected:
                raise Refused(f"{name} artifacts changed since their successful gates; retained for investigation")
            self.record["reused"].append(name)
        else:
            action()
            expected = {str(p): fingerprint(p, self.source) for p in outputs}
            self.checkpoint.setdefault("milestones", {})[name] = expected
            self.write_json(self.checkpoint_path, self.checkpoint)
        self.record["artifacts"].update(expected)
        self.save()

    @contextlib.contextmanager
    def synchronization_git_environment(self):
        # Acquisition belongs to Agh. The restoration owner only receives local
        # objects, and cannot consult a helper, a promisor remote or the network.
        owner = self.git_owner()
        private = Path(tempfile.mkdtemp(prefix="managed-git-", dir=self.invocation))
        environment = owner["_provenance_git_environment"]()
        environment.update(GIT_TERMINAL_PROMPT="0", GIT_NO_LAZY_FETCH="1", GIT_ALLOW_PROTOCOL="")
        fixed_git = owner["_controlled_git_command"]([
            "-c", "protocol.https.allow=never", "-c", "protocol.file.allow=never"])
        binary = private / "bin"; binary.mkdir(mode=0o700)
        shim = binary / "git"
        shim.write_text("#!/bin/sh\nexec /usr/bin/env -i " + shlex.join(
            [f"{key}={value}" for key, value in sorted(environment.items())]
            + fixed_git) + ' "$@"\n')
        shim.chmod(0o700)
        before = {str(file): file_hash(file) for file in [Path(fixed_git[0]), shim]}
        selected = {**self.env, "PATH": str(binary) + os.pathsep + self.env.get("PATH", ""),
                    "GIT_NO_LAZY_FETCH": "1", "GIT_ALLOW_PROTOCOL": ""}
        try:
            yield selected
        finally:
            if any(file_hash(Path(name)) != expected for name, expected in before.items()):
                raise Refused("managed Git synchronization transport changed")

    def dependency_object_caches(self) -> dict[str, Path]:
        """The declared first-party caches by their gitlink's URL in the snapshot: the
        dependency preparation takes the locked commits they hold from them (RL-54)."""
        if not self.args.source_object_cache:
            return {}
        owner = self.git_owner()
        caches = owner["_first_party_checkout_caches"](self.source, self.args.source_object_cache)
        urls = {entry.path.as_posix(): entry.url for entry in owner["_indexed_submodules"](self.source)}
        return {urls[path]: cache.resolve(strict=True) for path, cache in sorted(caches.items())}

    def acquire_submodule_pins(self, path: Path, label: str, attempt: int) -> None:
        owner = self.git_owner()
        # Only the Trust source has the first-party gitlinks a declared cache names.
        # Agh ends each of its Git transfers after 600 s (docs/OPEN_ISSUES.md
        # AGH-PIN-REPAIR-BOUND-1), which a complete fetch of the largest sibling
        # cannot meet; with a cache it takes the exact checkout closure instead and
        # reads the objects a local repository already holds.
        caches = (owner["_first_party_checkout_caches"](path, self.args.source_object_cache)
                  if trust_checkout(label) and self.args.source_object_cache else {})
        if caches and self.train is not None:
            # Read the gitlinks under this runner's admission for the linked landing worktree.
            entries = owner["_indexed_submodules"](path)
            caches = self.train.source_objects().select(entries, caches, self.train.state.get("good"))
        if trust_checkout(label) and self.args.owned_object_cache:
            owned = owner["_first_party_checkout_caches"](path, self.args.owned_object_cache)
            if caches.keys() & owned.keys():
                raise Refused("a gitlink takes one object cache, a declared or an owned one: "
                              + ", ".join(sorted(caches.keys() & owned.keys())))
            for gitlink, cache in sorted(owned.items()):
                self.refresh_object_cache(path, gitlink, cache)
            caches = {**caches, **owned}
        if caches:
            owner["ensure_submodules"](path, checkout_caches=caches)
        else:
            owner["ensure_submodules"](path)
        states = owner["_inspect_submodule_tree"](path)
        owner["refuse_dirty_submodule_lockfiles"](states)
        receipts = []
        for state in states:
            entries = owner["_indexed_submodules"](state.repository)
            entry = next((entry for entry in entries if entry.path == state.path), None)
            if entry is None or state.marker in {"-", "U"}:
                raise Refused("submodule acquisition lost its indexed declaration or materialized child")
            child = state.repository / entry.path
            original_head = self.git("submodule-original-head", child, "rev-parse", "HEAD")
            present = self.git("submodule-local-pin", child, "rev-parse", "--disambiguate=" + entry.oid)
            if entry.oid not in present.splitlines():
                def acquire(argv, environment):
                    with owner["_agh_transfer_paths"](child, environment, self.invocation) as (
                            child_environment, paths):
                        self.call("acquire-submodule-pin", argv, child, env=child_environment,
                                  progress=owner["_SubmoduleProgress"](
                                      f"Agh's fetch of the pin of {state.display_path}", paths))
                receipt = owner["_agh_source_fetch"](
                    entry.url, child, entry.oid, "refs/agh/trust-daily-staging/pins/" + entry.oid,
                    execute=acquire)
                receipts.append({"path": state.display_path, **receipt})
            if (owner["_indexed_submodules"](state.repository) != entries
                    or self.git("submodule-retained-head", child, "rev-parse", "HEAD") != original_head):
                raise Refused("submodule acquisition changed its indexed declaration or existing HEAD")
        owner["refuse_dirty_submodule_lockfiles"](owner["_inspect_submodule_tree"](path))
        self.write_json(self.invocation / f"{label}-submodule-acquisition-{attempt}.json",
                        {"schema": "trust.daily-submodule-acquisition.v1", "fetched": receipts,
                         "restoration": "separate offline ancestry/dirty/local-anchor owner"})

    def refresh_object_cache(self, path: Path, gitlink: str, cache: Path) -> None:
        """Bring an --owned-object-cache up to the pin `path` indexes for `gitlink`.

        Agh fetches what the cache lacks of that pin's history (its unfiltered fetch,
        negotiated against the cache: a day of the sibling's main costs a day's objects,
        where a closure from a stale cache took gigabytes again every cut) into a private
        ref, and the cache's HEAD then names the pin, the start Agh tries first for a
        later closure. That ref, HEAD and the fetched objects are all the runner writes
        there: no alternates, configuration or working tree, so the cache stays data that
        Agh reads and checks, never authority. A refresh that fails is recorded and the
        cache is read as it is; the closure fetches what it lacks.
        """
        owner = self.git_owner()
        entry = next(entry for entry in owner["_indexed_submodules"](path) if entry.path.as_posix() == gitlink)
        refreshed = self.record.setdefault("owned_object_caches", {})
        if refreshed.get(gitlink, {}).get("pin") == entry.oid and refreshed[gitlink]["repository"] == str(cache):
            # This run already refreshed it at this pin, or tried and failed: the landing
            # worktree reads it as the snapshot left it, and a stall is not waited out twice.
            return
        record = refreshed[gitlink] = {"repository": str(cache), "pin": entry.oid, "status": "running",
                                       "started_at": now()}
        self.save()
        ref = "refs/agh/owned-object-cache/" + entry.oid
        try:
            if self.git("object-cache-kind", cache, "rev-parse", "--is-bare-repository") != "true":
                raise Refused(f"an owned object cache is a bare repository, and {cache} is not one")

            def acquire(argv, environment):
                with owner["_agh_transfer_paths"](cache, environment, self.invocation) as (child_environment, paths):
                    self.call("refresh-object-cache", argv, cache, env=child_environment,
                              progress=owner["_SubmoduleProgress"](
                                  f"Agh's refresh of the object cache of {gitlink}", paths))
            owner["_agh_source_fetch"](entry.url, cache, entry.oid, ref, execute=acquire, native_exact=True)
            self.git("object-cache-head", cache, "update-ref", "--no-deref", "HEAD", entry.oid)
            # The pin HEAD names keeps its history; an earlier pin's ref is not needed.
            for name in self.git("object-cache-refs", cache, "for-each-ref", "--format=%(refname)",
                                 "refs/agh/owned-object-cache/").splitlines():
                if name != ref:
                    self.git("object-cache-earlier-ref", cache, "update-ref", "-d", name)
            record.update(status="refreshed", head=entry.oid,
                          pack_kib=self.object_cache_pack_kib(cache))
        except Refused as error:
            # A transfer that failed or stalled, or a Git step on the cache. Anything else (a
            # changed Agh, a ref naming another commit, a cancelled run) ends the run as it would
            # any acquisition's.
            record.update(status="failed", error=str(error))
            print(f"  the owned object cache of {gitlink} was not refreshed, and is read as it is: {error}",
                  flush=True)
        except BaseException as error:
            record.update(status="failed", error=str(error) or type(error).__name__)
            raise
        finally:
            record["finished_at"] = now()
            self.save()

    def object_cache_pack_kib(self, cache: Path) -> int | None:
        """The packed size Git counts in an owned object cache, which grows as its sibling's history does."""
        counted = self.git("object-cache-size", cache, "count-objects", "-v")
        sizes = [line.split(":", 1)[1].strip() for line in counted.splitlines() if line.startswith("size-pack:")]
        return int(sizes[0]) if sizes and sizes[0].isdecimal() else None

    def synchronize(self, path: Path, label: str) -> str:
        # This owner initializes missing modules and restores only provably safe drift;
        # no blanket submodule update, force checkout, reset or clean is used here.
        # A first pass can initialize a parent whose nested .gitmodules did not
        # exist when that pass walked the tree. Ask the owner again for that new
        # level, with a finite depth bound and a progress check.
        if not (path / ".gitmodules").exists():
            self.clean(path)
            return self.git(f"{label}-pins", path, "submodule", "status", "--recursive")
        previous = None
        with self.synchronization_git_environment() as environment:
            for attempt in range(32):
                self.acquire_submodule_pins(path, label, attempt)
                self.call("submodule-sync", ["bash", str(self.source / "scripts/submodule_sync.sh"),
                                             "--root", str(path), "--offline", "--restore"], env=environment)
                pins = self.git(f"{label}-pins", path, "submodule", "status", "--recursive")
                if not any(line.startswith(("-", "+", "U")) for line in pins.splitlines()):
                    break
                if pins == previous:
                    raise Refused("safe submodule synchronization made no progress; retained without force")
                previous = pins
            else:
                raise Refused("nested submodules exceed the staging depth bound")
        self.clean(path)
        if (self.train is not None and path == self.source and label == "source"
                and self.args.source_object_cache):
            retained = self.train.source_objects()
            caches = retained.optional(self.git_owner()["_first_party_checkout_caches"],
                                       path, self.args.source_object_cache)
            if caches:
                retained.optional(retained.capture, path, self.state, caches)
        return pins

    def pinned_source(self) -> None:
        self.record["submodules"] = self.synchronize(self.source, "source")
        self.save()

    def build_tree_manager(self, work: Path | None = None, prepared: Path | None = None) -> None:
        """Give the snapshot the build-tree manager its x.py runs take their lease from.

        A fresh snapshot has none, and until 2026-11-15 only the mint's first x.py noticed:
        "native build-tree manager v2 is unavailable". So it is asked before the first x.py,
        and built by the snapshot's own scripts/build-tree-manager.sh when none answers
        (docs/BUILD_AND_INSTALL.md).

        That build is offline (`--frozen`): it resolves src/bootstrap/Cargo.lock from its
        Cargo home alone. A stage run gives it what the dependency preparation has just
        proved for that manifest: `prepared`, the handoff its offline replay resolved,
        copied once more through the mint's safe-input owner (the build unpacks crates into
        its home, and the handoff is the mint's input), and the pinned seed's Targo in
        `work`, the driver of that replay and the compiler bootstrap.py builds Bootstrap
        with. The step then depends neither on --cargo-home, an optional input cache that
        may be partial or absent, nor on the Targo this Mac installs. Built before the
        preparation with the run's own Cargo home, it ended six of the train's ten ticks
        on 2026-11-16 in three seconds, on "no matching package named `chrono` found":
        that home held every locked archive and the index entries of 81 of Bootstrap's 194
        registry crates. A prepare run has no preparation; its manager is built with the
        run's environment, whose --cargo-home that mode requires filled."""
        manager = tree_build_manager(self.source, self.env)
        built = manager is None
        detail = {}
        if built:
            argv = ["bash", str(self.source / "scripts/build-tree-manager.sh")]
            environment = None
            if prepared is not None:
                seed = work / "seed"
                targo = seed / "bin/targo"
                if targo.is_symlink() or not targo.is_file() or not os.access(targo, os.X_OK):
                    raise Refused(f"the dependency preparation left no pinned seed Targo to build the manager with: {targo}")
                homes = work / "manager-inputs"
                if homes.is_symlink() or (homes.exists() and not homes.is_dir()):
                    raise Refused(f"the manager's Cargo homes must be an owned non-symlink directory: {homes}")
                homes.mkdir(exist_ok=True)
                # A fresh home per attempt: the safe-input owner fills only a path that does not exist.
                attempt = Path(tempfile.mkdtemp(prefix="attempt-", dir=homes))
                home, manifest = attempt / "cargo-home", attempt / "cargo-home-inputs.json"
                self.call("build-tree-manager-inputs", [
                    str(self.python), "-I", "-S", str(self.source / "scripts/mint_seed_support.py"),
                    "cargo-home-inputs", "--source", str(prepared), "--destination", str(home),
                    "--output", str(manifest)])
                argv += ["--targo", str(targo)]
                for directory in self.args.seed_dylib_path:
                    argv += ["--seed-dylib-path", str(directory.resolve(strict=True))]
                # As for the recreator and the prewarm: no ambient compiler, flag or cache override.
                environment = {**bootstrap_environment(self.env, self.source / "scripts/recreate_bootstrap.py"),
                               "CARGO_HOME": str(home)}
                detail = {"targo": str(targo), "cargo_home": str(home), "cargo_home_inputs": str(manifest)}
            try:
                self.call("build-tree-manager", argv, heavy=True, env=environment)
            except CommandFailed as error:
                raise Refused("the build-tree-manager step built no manager that answers "
                              f"{MANAGER_PROTOCOL.decode().strip()}; see {self.last_step()['log']}") from error
            manager = tree_build_manager(self.source, self.env)
            if manager is None:
                raise Refused("the build-tree-manager step left no manager that answers "
                              f"{MANAGER_PROTOCOL.decode().strip()}, so the mint's x.py would refuse "
                              f"its build lease; see {self.last_step()['log']}")
            if prepared is not None:
                # The build ran the seed the mint is about to build with. Its tree is one of the
                # preparation's bound inputs; say so now, not after the hours of a mint.
                expected = self.checkpoint["dependency_preparation"]["inputs"][str(seed)]
                if fingerprint(seed) != expected:
                    raise Refused(f"the build-tree-manager step changed the pinned seed it built with: {seed}")
        self.record["build_tree_manager"] = {"path": str(manager), "sha256": file_hash(manager), "built": built, **detail}
        self.save()

    def consumers(self, staged: Path) -> list[str]:
        if not self.consumer_repos:
            return []
        engine, engine_commit = self.publication()
        self.record["consumer_policy_engine"] = {"commit": engine_commit, "path": str(engine)}
        rustup_name = shutil.which("rustup", path=self.env.get("PATH"))
        if not rustup_name:
            raise Refused("consumer acceptance requires rustup for its isolated toolchain home")
        rustup = Path(rustup_name).resolve(strict=True)
        shell = Path("/bin/sh").resolve(strict=True)
        staged_identity = fingerprint(staged)
        if elan_home_identity(self.elan_home) != self.elan_identity:
            raise Refused("selected Lean installation changed before consumer checks")
        base_environment = bootstrap_environment(self.env, self.source / "scripts/recreate_bootstrap.py")
        if self.args.cargo_home:
            base_environment["CARGO_HOME"] = str(self.args.cargo_home.resolve(strict=True))
        environment_sha256 = hashlib.sha256(json.dumps(base_environment, sort_keys=True).encode()).hexdigest()
        errors = [f"{name}: missing --consumer {name}=REPO" for name in CONSUMERS if name not in self.consumer_repos]
        self.record["consumer_jobs"] = self.args.consumer_jobs
        for name in CONSUMERS:
            self.save_consumer(name, {"status": "queued" if name in self.consumer_repos else "not-configured",
                                      "source_commit": None})

        def check(name: str) -> str | None:
            consumer = {"status": "starting", "source_commit": None}
            self.save_consumer(name, consumer)
            if name not in self.consumer_repos:
                return f"{name}: missing --consumer {name}=REPO"
            error_text = None
            try:
                work = self.state / "consumers" / name
                commit = self.snapshot(self.consumer_repos[name], work, f"consumer-{name}")
                pins = self.synchronize(work, f"consumer-{name}")
                consumer.update(status="reading-policy", source_commit=commit, path=str(work), submodules=pins)
                self.save_consumer(name, consumer)
                blob = self.git(f"{name}-policy-blob", work, "rev-parse", "--verify", f"{commit}:publish/config.sh")
                consumer["policy_blob"] = blob
                raw = self.call(f"{name}-committed-policy", [str(self.python), str(Path(__file__).resolve()),
                                "_consumer-policy", str(engine), str(work)], work)
                policy = json.loads(raw)
                check_name = f"{name}-consumer-check"
                check_command = [str(shell), "-c", policy["command"]]
                check_timeout = policy["bound"]["seconds"]
                identity = {"consumer": name, "source_commit": commit, "submodules": pins,
                            "runner_sha256": file_hash(Path(__file__)), "environment_sha256": environment_sha256,
                            "cargo_configs": cargo_config_inputs(work, base_environment),
                            "policy_blob": blob, "policy": policy, "policy_engine_commit": engine_commit,
                            "toolchain": str(staged), "toolchain_identity": staged_identity,
                            "elan_home_identity": self.elan_identity,
                            "cross_target_oracles": {},
                            "rustup": {"path": str(rustup), "sha256": file_hash(rustup)},
                            "shell": {"path": str(shell), "sha256": file_hash(shell)}}
                key = hashlib.sha256(json.dumps(identity, sort_keys=True).encode()).hexdigest()
                consumer.update(status="running", source_commit=commit, identity=identity)
                self.save_consumer(name, consumer)
                rustup_home = self.state / "consumer-rustup" / name / key
                target = self.state / "consumer-targets" / name / key
                rustup_home.mkdir(parents=True, exist_ok=True)
                private_bin = rustup_home / "bin"
                private_bin.mkdir(exist_ok=True)
                shim = private_bin / "rustup"
                if not shim.exists() and not shim.is_symlink():
                    shim.symlink_to(rustup)
                if not shim.is_symlink() or shim.resolve(strict=True) != rustup:
                    raise Refused("consumer rustup shim changed")
                environment = consumer_environment(base_environment, staged, rustup_home,
                                                   target, self.env.get("PATH", ""))
                for oracle, targets in policy["cross_target_oracles"].items():
                    install = [str(rustup), "toolchain", "install", oracle, "--profile", "minimal", "--no-self-update"]
                    install += ["--target", ",".join(targets)]
                    self.call(f"{name}-cross-oracle-install", install, work, heavy=True, env=environment,
                              timeout=policy["bound"]["seconds"])
                    root_text = self.call(f"{name}-cross-oracle-sysroot", [str(rustup), "run", oracle,
                                          "rustc", "--print", "sysroot"], work, env=environment)
                    root = Path(root_text)
                    if root.is_symlink() or not root.resolve(strict=True).is_relative_to(rustup_home / "toolchains"):
                        raise Refused("stock cross-target oracle escaped its scratch rustup home")
                    identity["cross_target_oracles"][oracle] = {
                        "path": str(root), "targets": targets, "identity": fingerprint(root)}
                key = hashlib.sha256(json.dumps(identity, sort_keys=True).encode()).hexdigest()
                target = self.state / "consumer-targets" / name / key
                environment["CARGO_TARGET_DIR"] = str(target)
                execution_environment_sha256 = hashlib.sha256(json.dumps(environment, sort_keys=True).encode()).hexdigest()
                link = rustup_home / "toolchains/trust"
                if link.exists() or link.is_symlink():
                    if not link.is_symlink() or link.resolve(strict=True) != staged.resolve(strict=True):
                        raise Refused("consumer scratch trust binding changed")
                self.call(f"{name}-scratch-trust-link", [str(rustup), "toolchain", "link", "trust", str(staged)], work, env=environment)
                sysroot = self.call(f"{name}-candidate-sysroot", [str(rustup), "run", "trust", "trustc", "--print", "sysroot"], work, env=environment)
                if Path(sysroot).resolve(strict=True) != staged.resolve(strict=True):
                    raise Refused("consumer rustup selected a different candidate sysroot")
                self.call(f"{name}-genuine-targo", [str(rustup), "run", "trust", "targo", "--unverified", "--version"], work, env=environment)
                result_path = self.state / "consumer-results" / name / f"{key}.json"
                receipt = None
                if result_path.exists():
                    previous = read_json(result_path)
                    previous_log = Path(previous["log"])
                    log = previous_log
                    if (previous.get("schema") != CONSUMER_RECEIPT_SCHEMA
                            or previous.get("identity") != identity
                            or type(previous.get("exit_code")) is not int or previous.get("exit_code") != 0
                            or previous.get("execution_environment_sha256") != execution_environment_sha256
                            or previous.get("log_identity") != fingerprint(previous_log)
                            or previous.get("step", {}).get("log") != str(previous_log)):
                        raise Refused("consumer acceptance cache or its retained log changed")
                    check_step = previous["step"]
                    require_consumer_terminal_receipt(check_step, check_name, work, engine, check_command, check_timeout)
                    outcome = consumer_outcome(engine, policy, check_step)
                    consumer["outcome"] = outcome
                    if not outcome["accepted"] or previous.get("outcome") != outcome:
                        raise Refused("consumer cached outcome is refused or changed")
                    consumer.update(status="passed", reused=True, receipt=str(result_path),
                                    log=str(previous_log), exit_code=0)
                else:
                    self.call(check_name, check_command, work, heavy=True, env=environment, timeout=check_timeout)
                    check_step = self.last_step()
                    log = Path(check_step["log"])
                    require_consumer_terminal_receipt(check_step, check_name, work, engine, check_command, check_timeout)
                    outcome = consumer_outcome(engine, policy, check_step)
                    consumer["outcome"] = outcome
                    if not outcome["accepted"]:
                        raise Refused("consumer outcome refused: " + "; ".join(outcome["refusals"]))
                    receipt = {"schema": CONSUMER_RECEIPT_SCHEMA, "identity": identity, "exit_code": 0,
                               "execution_environment_sha256": execution_environment_sha256,
                               "completed_at": now(), "log": str(log), "log_identity": outcome["log_identity"],
                               "step": check_step, "outcome": outcome, "target_dir": str(target),
                               "rustup_home": str(rustup_home)}
                self.clean(work)
                if self.git(f"{name}-acceptance-source", work, "rev-parse", "HEAD") != commit:
                    raise Refused("consumer source changed before acceptance was recorded")
                if fingerprint(staged) != staged_identity:
                    raise Refused("consumer acceptance toolchain changed")
                if elan_home_identity(self.elan_home) != self.elan_identity:
                    raise Refused("selected Lean installation changed during consumer checks")
                if (file_hash(rustup) != identity["rustup"]["sha256"]
                        or file_hash(shell) != identity["shell"]["sha256"]
                        or cargo_config_inputs(work, base_environment) != identity["cargo_configs"]):
                    raise Refused("consumer command tool or Cargo configuration inputs changed")
                if (not link.is_symlink() or link.resolve(strict=True) != staged.resolve(strict=True)
                        or not shim.is_symlink() or shim.resolve(strict=True) != rustup):
                    raise Refused("consumer check changed its isolated toolchain binding")
                for oracle in identity["cross_target_oracles"].values():
                    if fingerprint(Path(oracle["path"])) != oracle["identity"]:
                        raise Refused("consumer check changed its stock cross-target oracle inputs")
                if (fingerprint(log) != outcome["log_identity"]
                        or file_hash(engine / "bin/pub") != outcome["reader_sha256"]):
                    raise Refused("consumer full output or publication owner changed before acceptance")
                require_consumer_terminal_receipt(check_step, check_name, work, engine, check_command, check_timeout)
                if receipt:
                    self.write_json(result_path, receipt)
                    consumer.update(status="passed", reused=False, receipt=str(result_path), log=str(log), exit_code=0)
            except (KeyboardInterrupt, InterruptedError) as error:
                consumer.update(status="interrupted", error=str(error))
                self.save_consumer(name, consumer)
                raise
            except Exception as error:
                consumer.update(status="failed", error=str(error))
                if isinstance(error, CommandFailed):
                    consumer.update(exit_code=error.exit_code, timed_out=error.timed_out)
                if self.last_step():
                    consumer["log"] = self.last_step()["log"]
                error_text = f"{name}: {error}"
            self.save_consumer(name, consumer)
            return error_text

        pool = concurrent.futures.ThreadPoolExecutor(max_workers=self.args.consumer_jobs,
                                                     thread_name_prefix="trust-consumer")
        pending = iter(name for name in CONSUMERS if name in self.consumer_repos)
        active: dict = {}

        def admit() -> None:
            while len(active) < self.args.consumer_jobs:
                name = next(pending, None)
                if name is None:
                    break
                active[pool.submit(check, name)] = name

        try:
            admit()
            while active:
                done, _ = concurrent.futures.wait(active, timeout=0.2,
                                                  return_when=concurrent.futures.FIRST_COMPLETED)
                for future in done:
                    active.pop(future)
                    error = future.result()
                    if error:
                        errors.append(error)
                admit()
        except BaseException:
            self.cancelled.set()
            for future in active:
                future.cancel()
            raise
        finally:
            pool.shutdown(wait=True, cancel_futures=True)
        self.clean(engine)
        if self.git("final-policy-engine", engine, "rev-parse", "HEAD") != engine_commit:
            errors.append("publication policy engine changed during consumer checks")
        self.record["consumer_ready"] = not errors
        self.record["consumer_failures"] = errors
        if not errors:
            self.record["deployment_requirements"][1] = "A public seal (P5b) commits these completed consumer acceptance receipts as its evidence."
        self.save()
        return errors

    def bootstrap(self, build: bool) -> list[str]:
        argv = [str(self.python), str(self.source / "scripts/recreate_bootstrap.py"),
                "--no-atpkg", "--require-seed", "--no-register", "--host", self.host]
        return argv + (["--fresh-seed", "--require-llvm-identity"] if build
                       else ["--force-config", "--no-build"])

    def verify_provenance(self, stage: Path) -> None:
        # Promotion reads the named stage's receipt. Never synthesize one from a
        # separate successful bootstrap or attach its LLVM claims to mint's bytes.
        self.call("llvm-and-build-provenance", ["bash", str(self.source / "scripts/promote-toolchain.sh"),
                  "--provenance", "--require-llvm-identity", str(stage)])

    def promotion_env(self) -> dict:
        # Only promotion's gate commands get the executor: every other owner keeps
        # the environment with no TRUST_* setting that Runner.__init__ left it.
        return {**self.env, "TRUST_TOOLCHAIN_SERIAL_COMMAND": str(self.serial)}

    def gates(self, stage: Path) -> None:
        full_sdk_gates(self.call, stage, self.source, self.host, self.python, self.promotion_env())

    def stage(self) -> None:
        helper = self.source / "scripts/mint_seed_support.py"
        if self.elan_home is None:
            raise Refused("sanctioned staging requires an explicit selected Elan home for Clean's pinned library")
        if self.train is not None:
            # What would stop the upload is asked before the hours of a mint.
            self.train.before_cut(self)
        # Mint's output guard requires this owned parent even on a fresh checkout.
        # Preserve existing objects and refuse links before creating any outputs.
        build = self.source / "build"
        build.mkdir(exist_ok=True)
        if build.is_symlink() or not build.is_dir():
            raise Refused("managed build root must be a non-symlink directory")
        # The full pinned installation exceeds the bounded command-query channel.
        # Use the owner's exclusive receipt output and the existing bounded reader.
        lean_receipt = self.invocation / "clean-lean-inputs.json"
        self.call("clean-lean-inputs", [str(self.python), "-I", "-S", str(helper),
                  "clean-lean-inputs", "--root", str(self.source),
                  "--elan-home", str(self.elan_home), "--output", str(lean_receipt)])
        lean, lean_identity = read_json_artifact(lean_receipt)
        self.record["artifacts"][str(lean_receipt)] = lean_identity
        self.record["clean_lean_inputs"] = lean
        self.save()
        version = self.call("mint-version", [str(self.python), "-I", "-S", str(helper), "version", str(self.source)])
        if not re.fullmatch(r"[0-9]+\.[0-9]+\.[0-9]+", version):
            raise Refused("mint owner returned an invalid source version")
        short = self.commit[:12]
        mint = self.source / f"build/pack-mint-{version}-{self.host}-{short}"
        stage2 = mint / self.host / "stage2"
        archives = mint / "repin/bootstrap/trust-stage0/dist"
        mint_command = ["bash", str(self.source / "scripts/mint_and_prove_seed.sh"), "--host", self.host]
        mint_command += ["--clean-lean-lib", lean["library_path"]]
        # No --jobs: the mint takes build-slot's share, and its receipt records it for a
        # continuation (mint_seed_recovery.py), which also reads a default DDC seed from
        # the kept ddc-seed.json.
        # The cache is input data. It carries no compiled artifacts or user config.
        dependency_work = self.state / "dependencies" / self.commit
        if self.args.ddc_seed:
            mint_command += ["--ddc-seed", str(self.args.ddc_seed.resolve(strict=True))]
        for directory in self.args.seed_dylib_path:
            mint_command += ["--seed-dylib-path", str(directory.resolve(strict=True))]

        def mint_action() -> None:
            prepared_cache = self.prepare_dependencies(dependency_work)
            # The mint's first x.py takes its lease from the snapshot's manager, which is
            # built from what the preparation proved available offline.
            self.build_tree_manager(dependency_work, prepared_cache)
            command = [*mint_command, "--cargo-home", str(prepared_cache)]
            self.call("mint-preflight", [*command, "--check-only"])
            try:
                self.call("sanctioned-mint-and-double-compile", command, heavy=True)
            except CommandFailed as error:
                self.keep_mint_continuation(mint, command, error)
                raise

        self.milestone("mint", [stage2, archives, mint / "trust-seed-mint"], mint_action)
        if "build_tree_manager" not in self.record:
            # A mint this state root already holds needed no manager from this run; name the
            # one its snapshot answers with, when one does.
            manager = tree_build_manager(self.source, self.env)
            if manager is not None:
                self.record["build_tree_manager"] = {"path": str(manager), "sha256": file_hash(manager), "built": False}
        preparation = self.checkpoint.get("dependency_preparation")
        if not preparation:
            raise Refused("mint checkpoint lacks its source-bound dependency preparation")
        for path, identity in preparation["inputs"].items():
            if fingerprint(Path(path)) != identity:
                raise Refused(f"dependency preparation input changed: {path}")
        validate_dependency_preparation(preparation)
        self.record["dependency_preparation"] = preparation
        self.record["artifacts"].update(preparation["inputs"])
        receipt = (mint / "trust-seed-mint").read_text(encoding="utf-8")
        fields = dict(line.split("=", 1) for line in receipt.splitlines()
                      if "=" in line and not line.startswith("#")
                      and not line.startswith(("compiler_file=", "compiler_link=")))
        if (fields.get("source_commit") != self.commit or fields.get("host") != self.host
                or fields.get("ddc_verdict") != "identical" or fields.get("self_host_proof") != "pass"):
            raise Refused("mint receipt lacks this source's successful double compile and self-host proof")
        repin = fields.get("repin_commit", "")
        branch = fields.get("repin_branch", "")
        if not re.fullmatch(r"[0-9a-f]{40,64}", repin) or not branch.startswith("seed/repin-"):
            raise Refused("mint receipt does not bind a re-pin")
        if self.git("re-pin-ref", self.source, "rev-parse", "--verify", f"refs/heads/{branch}") != repin:
            raise Refused("the mint's re-pin branch changed or disappeared")
        self.record["mint"] = {k: fields.get(k) for k in ("ddc_seed_relation", "lineage_disjoint_anchor", "repin_commit", "repin_branch")}
        self.verify_provenance(stage2)
        seal = self.state / "toolchains" / f"trust-{self.commit[:8]}"

        def seal_action() -> None:
            self.call("seal-without-admission", ["bash", str(self.source / "scripts/promote-toolchain.sh"),
                      "--no-flip", "--require-provenance", "--require-llvm-identity", str(stage2)],
                      heavy=True, env=self.promotion_env())

        self.milestone("seal", [seal, self.state / "toolchains/rustc-private-sysroots"], seal_action)
        wp = self.source / "first-party/trust-wp"
        wp_target = self.state / "targets" / self.commit / "trust-wp"
        wp_env = {**self.env, "RUSTC": str(seal / "bin/trustc"), "CARGO_TARGET_DIR": str(wp_target)}
        # trust-wp's private-sysroot owner looks beside the selected sysroot.
        staged = self.state / "toolchains" / f"stage-trust-{self.commit}"

        def wp_action() -> None:
            self.call("trust-wp-drivers", [str(seal / "bin/targo"), "--unverified", "build", "--release", "--locked",
                      "-p", "trust-wp-driver", "-p", "targo-trust-wp", "-p", "trust-wp-cli"], wp, heavy=True, env=wp_env)
            if staged.exists():
                raise Refused(f"partial staged copy retained; use a fresh state root to retry: {staged}")
            staged.parent.mkdir(parents=True, exist_ok=True)
            shutil.copytree(seal, staged, symlinks=True)
            (staged / "bin").chmod((staged / "bin").stat().st_mode | stat.S_IWUSR)
            for name in WP_BINS:
                target = wp_target / "release" / name
                if not target.is_file() or not os.access(target, os.X_OK):
                    raise Refused(f"trust-wp did not produce executable {target}")
                shutil.copy2(target, staged / "bin" / name)
            self.gates(staged)

        self.milestone("staged-toolchain", [staged], wp_action)
        # Cached artifacts get current gates too, after their complete hash check.
        self.gates(staged)
        self.record["staged_toolchain"] = str(staged)
        if self.train is not None:
            # A fleet build is published on the cut's own gates, all passed above: the
            # double compile and self-host proof at mint, and the staged tree's contract,
            # UI and tool-start gates. Its consumer checks run after the upload and are
            # reported; the unsigned rehearsal packs below are the publisher's to make.
            self.train.after_cut(self, staged, mint)
            return
        consumer_errors = self.consumers(staged)
        aterm_repository = self.args.aterm_repo or self.consumer_repos.get("aterm")
        if not aterm_repository:
            self.record["deployment_requirements"].insert(0, "Supply --aterm-repo to complete local unsigned package staging.")
            raise Refused("toolchain staged; unsigned package staging requires --aterm-repo")
        aterm = self.state / "aterm-source"
        aterm_commit = self.snapshot(aterm_repository.resolve(strict=True), aterm, "aterm")
        producer_pins = self.synchronize(aterm, "package-producer")
        self.record["package_producer"] = {"commit": aterm_commit, "path": str(aterm), "submodules": producer_pins}
        packages = self.state / "packages" / self.commit / aterm_commit
        package_env = {**self.env, "RUSTC": str(staged / "bin/trustc"),
                       "CARGO_TARGET_DIR": str(self.state / "targets" / aterm_commit / "atpkg-publish.noindex")}
        producer = [str(staged / "bin/targo"), "--unverified", "run", "--release", "--locked", "-q",
                    "--manifest-path", str(aterm / "crates/atpkg-publish/Cargo.toml"), "--"]

        def package_action() -> None:
            # Explicit --unsigned works even on a machine which possesses a key.
            # The group publisher's floor/index/admission checks still belong to deployment.
            self.call("unsigned-trust-package", [*producer, "pack-bundle", "trust", "--sysroot", str(staged),
                      "--src-repo", str(self.source), "--trust-repo", str(self.source),
                      "--out", str(packages / "trust"), "--unsigned"], aterm, heavy=True, env=package_env)
            for name in ("trust-ir", "trust-cg", "trust-vc"):
                # Plain pack appends the program name to --out; bundle does not.
                self.call(f"unsigned-{name}-package", [*producer, "pack", name,
                          "--checkout", str(self.source / "first-party" / name),
                          "--toolchain", str(staged / "bin"), "--trust-repo", str(self.source),
                          "--out", str(packages), "--unsigned"], aterm, heavy=True, env=package_env)

        self.milestone(f"unsigned-packages-{aterm_commit}", [packages], package_action)
        for name in ("trust", "trust-ir", "trust-cg", "trust-vc"):
            directory = packages / name
            if not list(directory.glob("*.tar.zst")) or not list(directory.glob("pkg-*.toml")):
                raise Refused(f"package owner produced no {name} package manifest or archive")
        self.gates(staged)
        self.clean(aterm)
        if self.git("final-producer-source", aterm, "rev-parse", "HEAD") != aterm_commit:
            raise Refused("package producer HEAD changed during staging")
        self.record["packages"] = str(packages)
        if consumer_errors:
            raise Refused("consumer acceptance incomplete: " + "; ".join(consumer_errors))

    def keep_mint_continuation(self, mint: Path, command: list[str], failure: CommandFailed) -> None:
        """Keep what continuing a mint that failed after its stage provenance reads.

        mint_seed_recovery.py continues such a mint (`--resume-after-provenance`) instead of
        rebuilding it, about 6 hours, from: the terminal result with the original argv, the
        accepted stage receipt, the saved helper profile and the DDC observations. The mint
        retains its WORK when it fails. These are copied from it into this run's directory.
        WORK is then renamed beside itself in the source's build, out of the `.mint-and-prove.*`
        name the continuation recreates and refuses to find: it stays as long as the snapshot
        does, as it would have, and never rides the run's records into the train's history/.
        Every value is read and checked before anything is written, and the evidence directory
        appears whole or not at all; on any refusal WORK stays where the mint left it.
        A mint that failed before an accepted stage receipt, timed out or did not exit 1 keeps
        nothing here; it is built again. The original failure stays the run's error."""
        receipt_path = mint / self.host / "stage2/tool-provenance.json"
        if receipt_path.is_symlink() or not receipt_path.is_file():
            return
        evidence = self.invocation / "mint-continuation"
        partial = self.invocation / ".mint-continuation.partial"

        def kept(path: Path) -> bytes:
            if path.is_symlink() or not path.is_file():
                raise Refused(f"the mint's WORK holds no regular {path.name}: {path}")
            return path.read_bytes()

        try:
            receipt_bytes = receipt_path.read_bytes()
            receipt = json.loads(receipt_bytes)
            if (receipt.get("status") != "internal-release-ready" or receipt.get("errors") != []
                    or receipt["compiler"]["source_commit"] != self.commit):
                return
            if failure.exit_code != 1 or failure.timed_out:
                # The recovery continues only a mint's terminal exit 1; a timeout or a signal is rebuilt.
                raise Refused(f"the mint exited {failure.exit_code}{' on its timeout' if failure.timed_out else ''}, "
                              "and only a terminal exit 1 is continued")
            work = Path(receipt["build_authority"]["cargo_environment"]["cargo_home"]).parent
            if (work.parent != self.source / "build" or not work.name.startswith(".mint-and-prove.")
                    or work.is_symlink() or not work.is_dir()):
                raise Refused(f"the stage receipt names no retained mint WORK in the source's build: {work}")
            safe_path = kept(work / "safe-path.json")
            manifests = {name: kept(work / name) for name in MINT_DDC_EVIDENCE}
            pinned = json.loads(manifests["stage2-pinned-seed.json"])
            oracle = json.loads(manifests["ddc-seed.json"])
            # The mint writes an accepted stage receipt only after its double compile found the
            # two stage2 trees identical (mint_and_prove_seed.sh); inspect compares them again.
            ddc_state = {"stage2_tree_sha256": pinned["sha256"], "oracle_commit": oracle["commit"],
                         "relation": oracle["relation"]}
            # What the original argv did not name, the continuation is given from what the mint
            # recorded: the job count it ran with, and the default DDC seed it chose.
            jobs = receipt["bootstrap_lineage"]["mint_configuration"]["xpy_config_overrides"].get("build.jobs")
            if type(jobs) is not int or jobs < 1:
                raise Refused("the stage receipt records no job count (build.jobs) for the continuation's --jobs")
            continuation = [str(self.slot), *self.claim_words("sanctioned-mint-and-double-compile"), "--",
                            *command[:2], "--resume-after-provenance", str(evidence),
                            "--source-root", str(self.source), "--jobs", str(jobs), *command[2:]]
            if "--ddc-seed" not in command:
                seed = oracle.get("sysroot")
                if not isinstance(seed, str) or not Path(seed).is_absolute():
                    raise Refused("the kept ddc-seed.json names no DDC seed (sysroot) for the continuation's --ddc-seed")
                continuation += ["--ddc-seed", seed]
            retained = work.with_name("retained" + work.name)
            for path in (evidence, partial, retained):
                if os.path.lexists(path):
                    raise Refused(f"a continuation output already exists: {path}")
            after = self.git("mint-source-after", self.source, "rev-parse", "HEAD")
        except (OSError, ValueError, KeyError, TypeError, AttributeError, Refused) as problem:
            self.record["mint_continuation"] = {"error": f"continuation evidence not kept: {problem}"}
            self.save()
            return
        try:
            ddc = partial / "ddc-equality-evidence"
            ddc.mkdir(parents=True)
            captured = partial / "canonical-stage-provenance-before-selfhost.json"
            captured.write_bytes(receipt_bytes)
            (partial / "safe-path-v3-initial.json").write_bytes(safe_path)
            for name, data in manifests.items():
                (ddc / name).write_bytes(data)
            atomic_json(ddc / "observation.json", {
                "state": "actual_canonical_DDC_equality_observed", "source": self.commit, **ddc_state,
                "captured_manifests": [{"file": str(work / name), "sha256": file_hash(ddc / name)}
                                       for name in MINT_DDC_EVIDENCE]})
            atomic_json(partial / "state.json", {
                "source": self.commit, "canonical_stage_provenance": {"sha256": file_hash(captured)},
                "native_profile": {"source": self.commit, "sha256": file_hash(partial / "safe-path-v3-initial.json")},
                "ddc": ddc_state})
            atomic_json(partial / "mint-result.json", {"source": self.commit, "source_after": after,
                                                       "exit": failure.exit_code, "command": command})
            partial.rename(evidence)
            try:
                work.rename(retained)
            except OSError:
                # Evidence that names a continuation the still-present WORK would refuse is not kept.
                remove_tree(evidence)
                raise
        except OSError as problem:
            if partial.is_dir() and not partial.is_symlink():
                with contextlib.suppress(OSError):
                    remove_tree(partial)
            self.record["mint_continuation"] = {"error": f"continuation evidence not kept: {problem}"}
            self.save()
            return
        self.record["mint_continuation"] = {"evidence": str(evidence), "retained_work": str(retained),
                                            "command": continuation}
        self.save()
        print(f"the mint failed after its stage provenance; its continuation evidence is {evidence}; "
              f"continue it with:\n  {shlex.join(continuation)}", file=sys.stderr)

    def prepare_dependencies(self, work: Path) -> Path:
        if work.is_symlink():
            raise Refused("dependency workspace must not be a symlink")
        work.mkdir(parents=True, exist_ok=True, mode=0o700)
        output = self.invocation / "dependency-closure.json"
        planned = self.invocation / "dependency-ceiling.json"

        def prewarm(receipt: Path) -> list[str]:
            argv = [str(self.python), "-I", "-S", str(Path(__file__).resolve()), "_prewarm-dependencies",
                    str(self.source), str(work), self.host, str(receipt)]
            argv += [str(self.args.cargo_home.resolve(strict=True)) if self.args.cargo_home else "-"]
            engine, _commit = self.publication()
            argv.append(str(engine))
            for url, cache in self.dependency_object_caches().items():
                argv += ["--object-cache", f"{url}={cache}"]
            argv += [f"--dependency-checkout-cache={declaration}"
                     for declaration in self.args.dependency_checkout_cache]
            return argv + [str(p.resolve(strict=True)) for p in self.args.seed_dylib_path]
        environment = bootstrap_environment(self.env, self.source / "scripts/recreate_bootstrap.py")
        # The ceiling is computed by the preparation's own owners from its inputs, before
        # it starts, and the same number bounds its supervisor: no constant total (RL-55).
        # Computing it reads the locks and measures the input home, and prints one line.
        owner = self.git_owner()
        self.call("locked-dependency-ceiling", [*prewarm(planned), "--ceiling-only"], env=environment,
                  progress=owner["_SubmoduleProgress"]("the dependency preparation's ceiling", (planned,)))
        seconds = read_json(planned).get("seconds")
        if not isinstance(seconds, int) or not 0 < seconds <= 86400:
            raise Refused(f"the dependency preparation's ceiling must be 1 to 86400 s, the owned step's range: {seconds!r}")
        # The enclosing supervisor's bound starts before extraction/probes. It
        # expires before the inner owner's own ceiling, which starts later,
        # retaining a live owned process tree for publication's precise cleanup. It is a
        # build-slot step for that owned supervision, and it declares its real needs.
        self.call("locked-dependency-prewarm", [*prewarm(output), "--ceiling-seconds", str(seconds)],
                  heavy=True, env=environment, timeout=seconds, admission=FETCH_ONLY_ADMISSION)
        report = read_json(output)
        validate_preparation_fetches(report)
        cache = Path(report["cargo_home"])
        if cache.is_symlink() or not cache.resolve(strict=True).is_relative_to(work / "mint-inputs"):
            raise Refused("dependency owner returned a cache outside its owned handoff directory")
        expected = report.get("cache_trees")
        if not isinstance(expected, dict) or set(expected) != {"registry/index", "registry/cache", "git/db"}:
            raise Refused("dependency receipt does not bind the safe Cargo cache inputs")
        inputs = {str(work / "seed"): fingerprint(work / "seed"), str(output): fingerprint(output),
                  str(work / "initial-cache.json"): fingerprint(work / "initial-cache.json")}
        for relative, identity in expected.items():
            path = cache / relative
            if (fingerprint(path) if path.exists() else None) != identity:
                raise Refused("dependency cache changed after fetch")
            if identity is not None:
                inputs[str(path)] = identity
        self.clean(self.source)
        self.checkpoint["dependency_preparation"] = {"report": str(output), "sha256": file_hash(output),
                                                       "cargo_home": str(cache), "inputs": inputs}
        self.write_json(self.checkpoint_path, self.checkpoint)
        self.record["dependency_preparation"] = self.checkpoint["dependency_preparation"]
        self.record["artifacts"].update(inputs)
        self.save()
        return cache

    def run_locked(self) -> int:
        self.invocation = self.state / "runs" / (dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ") + f"-{os.getpid()}")
        self.invocation.mkdir(parents=True)
        self.record = {"schema": SCHEMA, "status": "running", "mode": self.args.mode,
                       "started_at": now(), "source_commit": None, "deployment_ready": False,
                       "consumer_ready": False, "consumers": {},
                       "deployment_requirements": list(REQUIREMENTS), "steps": [], "artifacts": {}, "reused": []}
        if self.agh is not None:
            self.record["agh"] = self.agh
        self.save()
        try:
            self.python = Path(sys.executable).resolve(strict=True)
            self.python_alias = private_python(self.state, self.python)
            self.env["PATH"] = python_search_path(self.state, self.env.get("PATH", os.defpath))
            self.record["python"] = {"path": str(self.python), "sha256": file_hash(self.python),
                                     "python3_alias": str(self.python_alias)}
            self.save()
            self.commit = self.snapshot(self.repo, self.source, "trust")
            self.slot = (self.args.build_slot.resolve(strict=True) if self.args.build_slot
                         else self.source / "scripts/build-slot")
            if not self.slot.is_file() or not os.access(self.slot, os.X_OK):
                raise Refused(f"build-slot is missing or not executable: {self.slot}")
            self.serial = selected_serial_command(self.args.serial_command, self.env.get("PATH"))
            self.record["source_commit"] = self.commit
            self.pinned_source()
            helper = self.source / "scripts/mint_seed_support.py"
            self.host = self.args.host or self.call("native-host", [str(self.python), "-I", "-S", str(helper), "host"])
            if not re.fullmatch(r"(?:aarch64|x86_64)-(?:apple-darwin|unknown-linux-(?:gnu|musl))", self.host):
                raise Refused(f"unsupported native staging host: {self.host}")
            self.elan_identity = elan_home_identity(self.elan_home)
            settings = {"runner_sha256": file_hash(Path(__file__)), "source_commit": self.commit,
                        "host": self.host, "mode": self.args.mode,
                        "python": self.record["python"],
                        "build_slot_sha256": file_hash(self.slot),
                        "serial_command": {"path": str(self.serial), "sha256": file_hash(self.serial)},
                        "cargo_home": str(self.args.cargo_home.resolve()) if self.args.cargo_home else None,
                        "elan_home": str(self.elan_home) if self.elan_home is not None else None,
                        "elan_home_identity": self.elan_identity,
                        "source_object_cache": sorted(self.args.source_object_cache),
                        "ddc_seed": str(self.args.ddc_seed.resolve()) if self.args.ddc_seed else None,
                        "ddc_seed_identity": fingerprint(self.args.ddc_seed.resolve(strict=True)) if self.args.ddc_seed else None,
                        "seed_dylib_path": {str(p.resolve(strict=True)): fingerprint(p.resolve(strict=True))
                                            for p in self.args.seed_dylib_path}}
            if self.args.dependency_checkout_cache:
                settings["dependency_checkout_cache"] = sorted(self.args.dependency_checkout_cache)
            if self.args.owned_object_cache:
                settings["owned_object_cache"] = sorted(self.args.owned_object_cache)
            if self.train is not None:
                # The host a fleet build is stage-uploaded through, and where it goes after
                # its stage-upload: the index, or nowhere.
                settings["publisher_host"] = self.args.publisher_host
                settings["index_host"] = self.args.index_host
            self.checkpoint_path = self.state / "checkpoints" / f"{self.commit}-{self.args.mode}.json"
            self.checkpoint = read_json(self.checkpoint_path) if self.checkpoint_path.exists() else {"settings": settings}
            if self.checkpoint.get("settings") != settings:
                raise Refused("checkpoint settings differ; retain it and use a fresh state root")
            self.record["settings"] = settings
            self.call("pinned-bootstrap-config", self.bootstrap(False))
            if self.args.mode == "prepare":
                # A stage run builds its manager from its prepared dependencies (stage()).
                self.build_tree_manager()
                stage = self.source / "build" / self.host / "stage2"
                self.milestone("prepared-stage2", [stage], lambda: self.call("pinned-bootstrap",
                               self.bootstrap(True), heavy=True))
                self.call("prepared-provenance-recheck", [str(self.python), str(self.source / "scripts/recreate_bootstrap.py"),
                          "--verify-stage-provenance", "--require-immutable-lineage", "--require-llvm-identity",
                          "--stage", "2", "--host", self.host])
                self.verify_provenance(stage)
                self.gates(stage)
                self.record["status"] = "prepared"
                self.record["deployment_requirements"].insert(0, "Run --mode stage: preparation is not a seed mint or a deployable staging result.")
            else:
                self.stage()
                # A train's build is published only when an index serves it.
                self.record["status"] = ("published" if self.record.get("published")
                                         else "staged" if self.record.get("staged")
                                         else "consumer_ready" if self.record["consumer_ready"] else "local_staged")
            self.custody()
            self.record["finished_at"] = now()
            self.save()
            return 0
        except (Exception, KeyboardInterrupt) as error:
            # A train's build stays what it is when a later step fails: staged, or served by an index.
            self.record.update(status=("published" if self.record.get("published") else "staged"
                                       if self.record.get("staged") else "failed"),
                               consumer_ready=False, error=str(error) or "interrupted", finished_at=now(),
                               interrupted=isinstance(error, (KeyboardInterrupt, InterruptedError)))
            self.save()
            return 1

    def source_at_cut(self) -> None:
        """The source snapshot is clean and still at the cut commit."""
        self.clean(self.source)
        if self.git("final-source", self.source, "rev-parse", "HEAD") != self.commit:
            raise Refused("source HEAD changed during staging")

    def artifacts_unchanged(self, skip: tuple[Path, ...] = ()) -> None:
        """Every artifact the run recorded, but those under `skip`, hashes as recorded."""
        for path, expected in self.record["artifacts"].items():
            if any(Path(path).is_relative_to(directory) for directory in skip):
                continue
            if fingerprint(Path(path), self.source) != expected:
                raise Refused(f"artifact changed during staging: {path}")

    def custody(self) -> None:
        """A run's end checks: its source and every artifact unchanged, and its own inputs too.

        A run makes them last. A train makes them before it publishes a build it cut as well,
        so a build reaches the fleet only from a cut whose custody held through its upload.
        """
        self.source_at_cut()
        # Rehash after the final gates, including earlier milestones and packages.
        self.artifacts_unchanged()
        if self.record.get("dependency_preparation"):
            validate_dependency_preparation(self.record["dependency_preparation"])
        if elan_home_identity(self.elan_home) != self.elan_identity:
            raise Refused("selected Lean installation changed during staging")
        if (not self.python_alias.is_symlink() or self.python_alias.resolve(strict=True) != self.python
                or file_hash(self.python) != self.record["python"]["sha256"]):
            raise Refused("controller interpreter or its private python3 alias changed during staging")
        if (self.serial.is_symlink() or not self.serial.is_file()
                or file_hash(self.serial) != self.record["settings"]["serial_command"]["sha256"]):
            raise Refused("promotion's serial command changed during staging")

    def resumed_custody(self) -> None:
        """Before a resumed publication: what it reads is what the cut recorded.

        That is the source snapshot at the cut commit and each recorded artifact the train keeps
        of a build. What a build regenerates (TRAIN_INTERMEDIATES) is no input of publication,
        and the train removes it from its last good build. The cut's own inputs (the Lean
        installation, the interpreter, the serial command) were checked by the cut itself.
        """
        self.source_at_cut()
        self.artifacts_unchanged(tuple(self.state / relative for relative in TRAIN_INTERMEDIATES))

    def run(self) -> int:
        with single_run(self.state):
            if self.train is not None:
                return self.run_locked()
            with agh_kept_in(self.state) as self.agh:
                if self.agh is not None:
                    self.env["PATH"] = first_on_path(self.agh["directory"], self.env.get("PATH", os.defpath))
                return self.run_locked()

    def resume(self, action: Callable[["Runner"], None]) -> None:
        """Run `action` in a new invocation of this state root's staged cut, with its commit and host.

        A train uses it to publish a build an earlier tick stage-uploaded. Nothing is cut or
        gated again, and the Trust and aterm snapshots stay as the cut left them; `action`
        checks what it reads (resumed_custody). Its error is recorded and raised.
        """
        with single_run(self.state):
            previous = read_json(self.state / "latest.json")
            legacy = previous.get("published") or {}
            if not previous.get("staged") and legacy.get("index") == "unchanged" and BUILD_TAG.fullmatch(str(legacy.get("tag"))):
                # A v1 train (trust.toolchain-train.v1) called its stage-upload `published`
                # and wrote no index: the tag is the staging, and nothing serves the build.
                previous = {key: value for key, value in previous.items() if key != "published"}
                previous["staged"] = {key: legacy[key] for key in ("build", "tag", "repository", "at") if key in legacy}
                previous["migrated"] = "a v1 train's record: its `published` (index unchanged) is this `staged`"
            self.invocation = self.state / "runs" / (dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ") + f"-{os.getpid()}")
            self.invocation.mkdir(parents=True)
            self.record = {**previous, "status": "running", "steps": [], "resumed_at": now()}
            for key in ("error", "interrupted", "finished_at"):
                self.record.pop(key, None)
            self.save()
            try:
                if not previous.get("staged") or not previous.get("source_commit"):
                    raise Refused(f"{self.state} holds no stage-uploaded cut to resume")
                self.python = Path(sys.executable).resolve(strict=True)
                private_python(self.state, self.python)
                self.env["PATH"] = python_search_path(self.state, self.env.get("PATH", os.defpath))
                self.commit, self.host = previous["source_commit"], previous["settings"]["host"]
                self.slot = (self.args.build_slot.resolve(strict=True) if self.args.build_slot
                             else self.source / "scripts/build-slot")
                action(self)
            except (Exception, KeyboardInterrupt) as error:
                self.record.update(status="published" if self.record.get("published") else "staged",
                                   error=str(error) or type(error).__name__, finished_at=now(),
                                   interrupted=isinstance(error, (KeyboardInterrupt, InterruptedError)))
                self.save()
                raise
            self.record.update(status="published" if self.record.get("published") else "staged", finished_at=now())
            self.save()


# ----------------------------------------------------------------------------------------
# The fleet train. One tick: first publish what an earlier tick staged and no index serves
# yet; then, when the previous train has ended and main has moved, cut main's tip, publish
# the seed archives, land the re-pin through the push gate, stage-upload the signed pack,
# publish it to the signed atpkg index with trust-resource-controller from the same commit,
# then run the consumer checks and the row-count comparison and land what they found as
# one item of docs/OPEN_ISSUES.md.


def github_slug(origin: str) -> str:
    """OWNER/NAME of a GitHub origin URL."""
    for prefix in ("https://github.com/", "git@github.com:", "ssh://git@github.com/"):
        if origin.startswith(prefix):
            slug = origin[len(prefix):].removesuffix("/").removesuffix(".git")
            if re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9-]*/[A-Za-z0-9._-]+", slug):
                return slug
    raise Refused("the train reads GitHub through agh; name the repository with --github-repo OWNER/NAME")


class GitHub:
    """What the train asks GitHub, each answer one agh command under its routed identity.

    It reads main and the build tags from the Git ref advertisement, which costs no REST
    quota, and deletes the one branch a landed re-pin leaves. It has no verb for a
    release, an index or a commit: the seed archives are publish_seed_cut.sh's act, the
    pack is aterm's publisher's, and a commit reaches main by a push through the hook
    (Train.land).
    """

    def __init__(self, slug: str, agh: str, log: Path | None = None, run: Callable = subprocess.run):
        if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9-]*/[A-Za-z0-9._-]+", slug):
            raise Refused(f"not a GitHub OWNER/NAME: {slug}")
        if slug.split("/")[0].lower() == "alabsystems":
            raise Refused("a fleet train works in the development owner, never the public release owner")
        self.slug, self.agh, self.log, self.run = slug, agh, log, run

    def _agh(self, *argv: str) -> str:
        try:
            result = self.run([self.agh, *argv], capture_output=True, text=True, timeout=300)
        except (OSError, subprocess.TimeoutExpired) as error:
            raise Refused(f"agh {' '.join(argv[:2])} did not finish: {error}") from error
        if self.log is not None:
            with self.log.open("a", encoding="utf-8") as stream:
                stream.write(json.dumps({"at": now(), "argv": [self.agh, *argv], "exit": result.returncode}) + "\n")
        if result.returncode:
            why = (result.stderr.strip().splitlines() or ["no diagnostic"])[0]
            # agh's exit 11: a rate limit, GitHub's or the share agh keeps for other work.
            raise (Unanswered if result.returncode == 11 else Refused)(
                f"agh {' '.join(argv[:2])} exited {result.returncode}: {why}")
        return result.stdout

    def _json(self, *argv: str):
        try:
            return json.loads(self._agh(*argv))
        except json.JSONDecodeError as error:
            raise Refused(f"agh {' '.join(argv[:2])} did not answer JSON") from error

    def can_push(self) -> bool | None:
        """Whether agh's identity may push here; None when a rate limit left it unanswered."""
        try:
            self._agh("can", self.slug, "push")
        except Unanswered:
            return None
        return True

    def refs(self, ref: str | None = None) -> dict[str, str]:
        rows = self._json("repo", "refs", self.slug, *(["--ref", ref] if ref else []))
        if not isinstance(rows, list) or not all(isinstance(row, dict) and isinstance(row.get("ref"), str)
                                                 and isinstance(row.get("oid"), str) for row in rows):
            raise Refused("agh did not list the repository's refs")
        return {row["ref"]: row["oid"] for row in rows}

    def main(self) -> str:
        """Main's tip."""
        sha = self.refs("refs/heads/main").get("refs/heads/main", "")
        if not re.fullmatch(r"[0-9a-f]{40,64}", sha):
            raise Refused("agh did not name main's commit")
        return sha

    def builds(self) -> list[int]:
        """Every stage-uploaded trust build, oldest first: the `atpkg-trust-<N>` tags.

        A tag says a pack was staged, not that an index serves it.
        """
        return sorted({int(match[1]) for ref in self.refs()
                       if (match := BUILD_TAG.fullmatch(ref.removeprefix("refs/tags/"))) and ref.startswith("refs/tags/")})

    def ahead(self, base: str) -> int | None:
        """How many commits main holds past `base`; None when GitHub did not say or `base` is not under main."""
        try:
            answer = self._json("compare", self.slug, f"{base}...main")
        except Refused:
            return None
        if not isinstance(answer, dict) or type(answer.get("ahead_by")) is not int or answer.get("behind_by") != 0:
            return None
        return answer["ahead_by"]

    def delete_branch(self, branch: str, commit: str) -> None:
        """Delete a merged branch, only while it still names `commit`."""
        ref = f"refs/heads/{branch}"
        self._agh("ref", "delete", self.slug, ref, "--expect", commit, "--confirm", ref)


def fleet_publisher(targo: str, host: str, words: list[str]) -> list[str]:
    """aterm's publisher, for exactly the commands of PUBLISHER_COMMANDS.

    Each is matched word for word under the hosts it names, so a path is absolute, a build
    is a decimal number and no flag is added, dropped or moved; PUBLISHER_NEVER is refused
    besides. Every other command is refused here.
    """
    shape = next((name for name, (hosts, patterns) in PUBLISHER_COMMANDS.items()
                  if host in hosts and len(words) == len(patterns)
                  and all(re.fullmatch(pattern, word) for pattern, word in zip(patterns, words))), None)
    if shape is None or PUBLISHER_NEVER.intersection(words):
        raise Refused(f"not a fleet train's publisher command under --host {host}: " + " ".join(words))
    prefix = [targo, "--unverified", "run", "-q", "--locked", "-p", "atpkg-publish", "--"]
    if shape == "hosts check":
        return [*prefix, *words, "--host", host]
    return [*prefix, "--host", host, *words]


def index_pins(text: str, target: str) -> tuple[int, dict[str, int]]:
    """The channel head `atpkg-publish status` printed: its index number and each program's pin.

    A pin `on <target>` replaces the channel's pin for a client on that target, so the pins
    are the ones a client on `target` installs.
    """
    index, pins, overlay = None, {}, {}
    for line in text.splitlines():
        if not line.startswith(STATUS_PREFIX):
            continue
        line = line[len(STATUS_PREFIX):]
        if match := re.fullmatch(r"atpkg-index-([0-9]+) — signed by .*", line):
            if index is not None:
                raise Refused("the publisher's status named two channel heads")
            index = int(match[1])
        elif match := STATUS_PIN.fullmatch(line):
            if match["target"] is None:
                pins[match["program"]] = int(match["build"])
            elif match["target"] == target:
                overlay[match["program"]] = int(match["build"])
    if index is None:
        raise Refused("the publisher's status named no signed index")
    return index, {**pins, **overlay}


def publisher_refusal(log: Path) -> str | None:
    """The last refusal aterm's publisher printed (`atpkg-publish: REFUSED — …`), shortened, if any."""
    try:
        lines = log.read_text(encoding="utf-8", errors="replace").splitlines()
    except OSError:
        return None
    found = [line.removeprefix("atpkg-publish: ") for line in lines if line.startswith("atpkg-publish: ")]
    return found[-1][:500] if found else None


def lost_index_race(log: Path) -> bool:
    """Whether a refused index publish lost the next index number to another publisher."""
    try:
        text = log.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return False
    return any(marker in text for marker in INDEX_RACE)


@contextlib.contextmanager
def train_lock(root: Path):
    """Yield whether this process now owns the train. A held lock is an answer, not an error."""
    root.mkdir(parents=True, exist_ok=True)
    with (root / "train.lock").open("a+") as stream:
        try:
            fcntl.flock(stream, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            yield False
            return
        try:
            yield True
        finally:
            fcntl.flock(stream, fcntl.LOCK_UN)


def load_train(root: Path) -> dict:
    path = root / "train.json"
    if not path.exists():
        return {"schema": TRAIN_SCHEMA}
    state = read_json(path)
    if state.get("schema") == TRAIN_SCHEMA_V1:
        return migrate_train_v1(state)
    if state.get("schema") != TRAIN_SCHEMA:
        raise Refused(f"not a train's state: {path}")
    return state


def migrate_train_v1(state: dict) -> dict:
    """A v1 train's state, as v2.

    A v1 train stopped every build at its stage-upload and recorded that as `published`. Its
    last good build is staged and served by no index, so the next tick publishes it; its last
    tick's `published` status is `staged`; its reading of main named the newest staging tag
    `published`. The migration is recorded in the state.
    """
    state = {**state, "schema": TRAIN_SCHEMA, "migrated": {"from": TRAIN_SCHEMA_V1, "at": now()}}
    for key in ("good", "last"):
        if state.get(key):
            entry = state[key] = dict(state[key])
            if "published_at" in entry:
                entry["staged_at"] = entry.pop("published_at")
            if entry.get("status") == "published":
                entry["status"] = "staged"
    if state.get("main") and "published" in state["main"]:
        state["main"] = {("staged" if key == "published" else key): value for key, value in state["main"].items()}
    return state


def train_decision(state: dict, tip: str, published: int | None, count: int | None) -> tuple[bool, str]:
    """Whether main's tip is cut now, and why.

    Main has not moved when its tip is the commit the last train settled on (the commit it
    cut, or that commit under nothing but the train's own re-pin and report), or when the
    newest published build already counts every commit of main. `published` is a build an
    index serves; a build that is only staged counts for nothing here.
    """
    last = state.get("last") or {}
    if tip == state.get("settled"):
        if last.get("status") == "published":
            return False, f"main has not moved since build {last.get('build')} was published"
        return False, (f"main has not moved since the last train ended at {tip[:12]} "
                       f"({last.get('status', 'no status')}: {last.get('error', 'no error recorded')})")
    if published is not None and count is not None and count <= published:
        return False, f"main has not moved since build {published} was published"
    return True, f"main is at {tip[:12]}, past " + (f"build {published}" if published is not None else "every published build")


def remove_tree(path: Path) -> None:
    """Delete a directory the train made. A link inside it is removed, never followed."""
    for directory, _names, _files in os.walk(path):
        os.chmod(directory, stat.S_IRWXU)  # a sealed toolchain's directories are read-only
    shutil.rmtree(path)


class TrainSourceObjects:
    """One latest DATA-only donor per explicitly declared first-party child.

    Agh still admits and hashes every supplied cache. These records only bind
    train-owned directories to the selected index; they are not source proofs.
    All mutation runs under the train lock, before failed builds are retired.
    """

    def __init__(self, root: Path, owner: dict, declarations: list[str]):
        self.root, self.owner = root, owner
        self.paths = []
        for declaration in declarations:
            path, separator, _location = declaration.partition("=")
            if (not separator or not path.startswith("first-party/")
                    or any(part in {"", ".", ".."} for part in path.split("/"))
                    or path in self.paths or len(self.paths) >= 4096):
                raise Refused("train object retention requires distinct declared first-party paths")
            self.paths.append(path)

    def optional(self, operation: Callable, *args, **kwargs):
        try:
            return operation(*args, **kwargs)
        except InterruptedError:
            raise
        except (OSError, RuntimeError, ValueError, KeyError, TypeError, IndexError, subprocess.SubprocessError):
            print("train: retained child object advice unavailable; keeping the declared external source", file=sys.stderr)
            return None

    def directory(self, path: Path, *, create: bool = False) -> None:
        try:
            parts = path.relative_to(self.root).parts
        except ValueError as error:
            raise Refused("train object directory escapes its state root") from error
        current = self.root
        for part in (None, *parts):
            current = current / part if part is not None else current
            if create and not os.path.lexists(current):
                current.mkdir(mode=0o700)
            metadata = current.lstat()
            if (not stat.S_ISDIR(metadata.st_mode) or metadata.st_uid != os.getuid()
                    or stat.S_IMODE(metadata.st_mode) & 0o022):
                raise Refused("train objects require physical owned non-writable directories")

    def git(self, path: Path, *args: str) -> str:
        return self.owner["_local_submodule_git"](["-C", str(path), *args]).stdout.decode().strip()

    def repository(self, path: Path, row: dict) -> Path:
        self.directory(path)
        identity = self.owner["_submodule_file_identity"](path)
        self.owner["_validate_staged_submodule"](path, identity)
        git_dir = path / ".git"
        if (list(self.owner["_submodule_file_identity"](git_dir)[:2]) != row["git_identity"]
                or any(os.path.lexists(git_dir / name) for name in ("info/grafts", "refs/replace"))
                or self.git(path, "rev-parse", "--verify", "HEAD^{commit}") != row["pin"]
                or self.git(path, "config", "--local", "--get", "remote.origin.url") != row["url"]):
            raise Refused("train object repository no longer binds its captured repository and pin")
        return path

    def capture(self, source: Path, build: Path, caches: dict[str, Path]) -> None:
        """Only a completed, inspected acquisition produces retention advice."""
        self.directory(build)
        indexed = {entry.path.as_posix(): entry for entry in self.owner["_indexed_submodules"](source)}
        children = []
        for path in self.paths:
            if path not in caches or path not in indexed:
                raise Refused("train object acquisition lost a declared indexed child")
            entry, child = indexed[path], source / path
            row = {"path": path, "url": entry.url, "pin": entry.oid,
                   "git_identity": list(self.owner["_submodule_file_identity"](child / ".git")[:2])}
            self.repository(child, row)
            children.append(row)
        atomic_json(build / "source-object-pins.json", {
            "schema": TRAIN_SOURCE_PINS, "source": str(source),
            "source_identity": list(self.owner["_submodule_file_identity"](source)[:2]),
            "commit": self.git(source, "rev-parse", "--verify", "HEAD^{commit}"), "children": children})

    def captured(self, build: Path, *, retained_good: bool = False) -> dict[str, dict]:
        if build.parent != self.root / "builds":
            raise Refused("train object capture is not in a train build")
        self.directory(build)
        if read_json(build / "train-build.json").get("schema") != TRAIN_SCHEMA:
            raise Refused("train object capture has no train build owner")
        source = build / "source"
        self.directory(source)
        indexed = {entry.path.as_posix(): entry for entry in self.owner["_indexed_submodules"](source)}
        if retained_good and not os.path.lexists(build / "source-object-pins.json"):
            # A last-good independent snapshot predating retention is already
            # kept by retirement. Read it in place; never rewrite its metadata.
            marker = read_json(build / "source.owner.json")
            if (marker.get("schema") != SCHEMA or marker.get("snapshot_kind") != "independent-git-v1"
                    or marker.get("path") != str(source)):
                raise Refused("retained last-good source has no independent snapshot owner")
            return {path: {"path": path, "url": indexed[path].url, "pin": indexed[path].oid,
                           "git_identity": list(self.owner["_submodule_file_identity"](source / path / ".git")[:2])}
                    for path in self.paths if path in indexed}
        record = read_json(build / "source-object-pins.json")
        if (record.get("schema") != TRAIN_SOURCE_PINS or record.get("source") != str(source)
                or record.get("source_identity") != list(self.owner["_submodule_file_identity"](source)[:2])
                or record.get("commit") != self.git(source, "rev-parse", "--verify", "HEAD^{commit}")
                or not isinstance(record.get("children"), list) or len(record["children"]) > 4096):
            raise Refused("train source capture no longer binds its owned snapshot")
        children = {}
        for row in record["children"]:
            path = row.get("path") if isinstance(row, dict) else None
            if path not in self.paths or path in children or path not in indexed:
                raise Refused("train source capture contains an undeclared or repeated child")
            entry = indexed[path]
            if row.get("pin") != entry.oid or row.get("url") != entry.url:
                raise Refused("train source capture differs from its original indexed declaration")
            children[path] = row
        return children

    def slot(self, path: str, *, create: bool = False) -> Path:
        slot = self.root / "source-objects-v1" / hashlib.sha256(path.encode()).hexdigest()
        if create or os.path.lexists(slot):
            self.directory(slot, create=create)
        return slot

    def descriptor(self, slot: Path, row: dict, *, bound: bool = True) -> Path:
        if (not isinstance(row, dict) or row.get("schema") != TRAIN_SOURCE_OBJECTS
                or row.get("path") not in self.paths
                or slot != self.slot(row["path"])
                or not self.owner["_submodule_url_is_allowed"](row.get("url", ""))
                or not re.fullmatch(r"[0-9a-f]{40}", row.get("pin", ""))
                or row.get("directory") not in {"donor-0", "donor-1"}
                or not isinstance(row.get("git_identity"), list)
                or len(row["git_identity"]) != 2
                or not all(type(value) is int for value in row["git_identity"])):
            raise Refused("invalid train object donor descriptor")
        if bound and (not isinstance(row.get("directory_identity"), list)
                      or len(row["directory_identity"]) != 2
                      or not all(type(value) is int for value in row["directory_identity"])):
            raise Refused("train object donor has no physical directory binding")
        source = Path(row.get("source", ""))
        if (not source.is_absolute() or source.parts[-len(Path(row["path"]).parts):] != Path(row["path"]).parts
                or source.parents[len(Path(row["path"]).parts)].parent != self.root / "builds"):
            raise Refused("train object donor source is not a declared child of a train build")
        return slot / row["directory"]

    def entry(self, slot: Path, row: dict) -> Path:
        directory = self.descriptor(slot, row)
        self.directory(directory)
        if list(self.owner["_submodule_file_identity"](directory)[:2]) != row["directory_identity"]:
            raise Refused("train object donor directory changed")
        return directory

    def current(self, slot: Path, *, match: tuple[str, str] | None = None) -> dict | None:
        if not os.path.lexists(slot / "current.json"):
            return None
        row = read_json(slot / "current.json")
        self.descriptor(slot, row)
        if match is not None and (row["url"], row["pin"]) != match:
            return None  # No object traversal for a pin that cannot be selected.
        self.repository(self.entry(slot, row), row)
        return row

    def select(self, entries, caches: dict[str, Path], good: dict | None) -> dict[str, Path]:
        """Match donor data to gitlinks validated by the checkout's owner."""
        selected = dict(caches)
        indexed = {entry.path.as_posix(): entry for entry in entries}
        good_build, good_children = None, {}
        if good and good.get("build_dir"):
            good_build = Path(good["build_dir"])
            good_children = self.optional(self.captured, good_build, retained_good=True) or {}
        for path in self.paths:
            entry = indexed[path]
            old = good_children.get(path)
            if old and (old["url"], old["pin"]) == (entry.url, entry.oid):
                candidate = good_build / "source" / path
                if self.optional(self.repository, candidate, old) is not None:
                    selected[path] = candidate
                    continue
            candidate = self.optional(self.retained, path, entry.url, entry.oid)
            if candidate is not None:
                selected[path] = candidate
        return selected

    def retained(self, path: str, url: str, pin: str) -> Path | None:
        slot = self.slot(path)
        if os.path.lexists(slot):
            row = self.current(slot, match=(url, pin))
            if row is not None:
                return self.entry(slot, row)
        return None

    def cleanup_retiring(self, slot: Path) -> None:
        transaction = read_json(slot / "retiring.json")
        if transaction.get("schema") != TRAIN_SOURCE_OBJECTS:
            raise Refused("unknown train object retirement")
        row = transaction["entry"]
        directory = self.descriptor(slot, row)
        current = self.current(slot)
        if current is None or current["directory"] == row["directory"]:
            raise Refused("train object retirement cannot remove its current donor")
        if os.path.lexists(directory):
            # The durable intent predates deletion. Its physical binding survives
            # missing Git contents or a deleted marker after interrupted rmtree.
            self.entry(slot, row)
            remove_tree(directory)
        if read_json(slot / "retiring.json") != transaction:
            raise Refused("train object retirement intent changed")
        (slot / "retiring.json").unlink()

    def complete_transfer(self, slot: Path) -> None:
        transaction = read_json(slot / "pending.json")
        if transaction.get("schema") != TRAIN_SOURCE_OBJECTS:
            raise Refused("unknown train object transfer")
        row, previous = transaction["entry"], transaction["previous"]
        directory = self.entry(slot, row)
        child = Path(row["source"])
        current = self.current(slot)
        if current not in (None, previous, row):
            raise Refused("train object donor changed during its transfer")
        if os.path.lexists(child / ".git"):
            if os.path.lexists(directory / ".git"):
                raise Refused("train object transfer has two Git directories; retaining both")
            self.repository(child, row)
            move, close = self.owner["_source_object_exclusive_move"](child, directory)
            try:
                move(child / ".git", directory / ".git")
            finally:
                close()
        self.repository(directory, row)
        atomic_json(slot / "current.json", row)
        if previous is not None and previous != row:
            if os.path.lexists(slot / "retiring.json"):
                if read_json(slot / "retiring.json").get("entry") != previous:
                    raise Refused("another train object retirement is pending")
            elif os.path.lexists(self.descriptor(slot, previous)):
                old = self.entry(slot, previous)
                self.repository(old, previous)
                if {item.name for item in old.iterdir()} != {".git"}:
                    raise Refused("unknown files appeared in the previous train object donor")
                atomic_json(slot / "retiring.json", {"schema": TRAIN_SOURCE_OBJECTS, "entry": previous})
            if os.path.lexists(slot / "retiring.json"):
                self.cleanup_retiring(slot)
        if read_json(slot / "pending.json") != transaction:
            raise Refused("train object transfer intent changed")
        (slot / "pending.json").unlink()

    def complete_creation(self, slot: Path) -> None:
        transaction = read_json(slot / "creating.json")
        if transaction.get("schema") != TRAIN_SOURCE_OBJECTS:
            raise Refused("unknown train object creation")
        row, previous = transaction["entry"], transaction["previous"]
        directory = self.descriptor(slot, row, bound=False)
        current = self.current(slot)
        if current is not None and {key: value for key, value in current.items()
                                    if key != "directory_identity"} == row:
            (slot / "creating.json").unlink()
            return
        if current != previous:
            raise Refused("train object donor changed before its replacement was created")
        if not os.path.lexists(directory):
            directory.mkdir(mode=0o700)
        self.directory(directory)
        if list(directory.iterdir()):
            raise Refused("unknown files appeared before train object transfer; preserving them")
        # A durable creation intent precedes mkdir. After a crash, an empty
        # physical owned directory can be used without deleting/adopting files.
        bound = {**row, "directory_identity": list(self.owner["_submodule_file_identity"](directory)[:2])}
        atomic_json(slot / "pending.json", {"schema": TRAIN_SOURCE_OBJECTS,
                                           "entry": bound, "previous": previous})
        if read_json(slot / "creating.json") != transaction:
            raise Refused("train object creation intent changed")
        (slot / "creating.json").unlink()
        self.complete_transfer(slot)

    def recover(self, slot: Path) -> bool:
        if os.path.lexists(slot / "retiring.json"):
            self.cleanup_retiring(slot)
        if os.path.lexists(slot / "pending.json"):
            self.complete_transfer(slot)
        if os.path.lexists(slot / "creating.json"):
            self.complete_creation(slot)
        return True

    def retain_failed(self, last: dict | None, good: dict | None) -> None:
        """Finish an interrupted transfer before deleting any failed build."""
        blocked = set()
        for path in self.paths:
            slot = self.optional(self.slot, path)
            if slot is None or (os.path.lexists(slot) and self.optional(self.recover, slot) is None):
                blocked.add(path)
        if (not last or last.get("status") not in {"failed", "interrupted"}
                or not last.get("build_dir") or (good and last["build_dir"] == good.get("build_dir"))):
            return
        build = Path(last["build_dir"])
        if not os.path.lexists(build / "source-object-pins.json"):
            return
        children = self.optional(self.captured, build) or {}
        good_children = {}
        if good and good.get("build_dir"):
            good_children = self.optional(self.captured, Path(good["build_dir"]), retained_good=True) or {}
        for path, row in children.items():
            if path in blocked:
                continue
            good_row = good_children.get(path)
            if good_row and (good_row["url"], good_row["pin"]) == (row["url"], row["pin"]):
                if self.optional(self.repository, Path(good["build_dir"]) / "source" / path, good_row) is not None:
                    continue
            self.optional(self.retain_child, build, path, row)

    def retain_child(self, build: Path, path: str, row: dict) -> None:
        slot = self.slot(path, create=True)
        previous = self.current(slot)
        if previous and (previous["url"], previous["pin"]) == (row["url"], row["pin"]):
            return
        child = build / "source" / path
        self.repository(child, row)
        directory = "donor-1" if previous and previous["directory"] == "donor-0" else "donor-0"
        if os.path.lexists(slot / directory):
            raise Refused("inactive train object slot is unknown; preserving it")
        descriptor = {**row, "schema": TRAIN_SOURCE_OBJECTS, "source": str(child), "directory": directory}
        atomic_json(slot / "creating.json", {"schema": TRAIN_SOURCE_OBJECTS,
                                            "entry": descriptor, "previous": previous})
        self.complete_creation(slot)


def retire_builds(root: Path, keep: Path | None) -> list[str]:
    """Remove every build directory of the train but `keep`; return what could not go.

    `keep`, the last good build, loses what a build regenerates (TRAIN_INTERMEDIATES) and
    keeps its toolchain, its signed packs and its records. A removed build's status and
    command logs move to history/, the newest TRAIN_HISTORY kept.
    """
    problems = []
    builds, history = root / "builds", root / "history"
    if builds.is_symlink() or history.is_symlink():
        raise Refused(f"the train's builds and history must be its own directories: {root}")
    for build in sorted(builds.iterdir()) if builds.is_dir() else []:
        if build.is_symlink() or not (build / "train-build.json").is_file():
            problems.append(f"{build} is not a train build directory; left in place")
            continue
        try:
            if build == keep:
                for relative in TRAIN_INTERMEDIATES:
                    if (build / relative).is_dir() and not (build / relative).is_symlink():
                        remove_tree(build / relative)
                continue
            kept = history / build.name
            if not kept.exists():
                kept.mkdir(parents=True)
                for name in ("latest.json", "runs"):
                    if (build / name).exists() and not (build / name).is_symlink():
                        os.replace(build / name, kept / name)
            remove_tree(build)
        except OSError as error:
            problems.append(f"{build} was not removed: {error}")
    for old in (sorted(history.iterdir())[:-TRAIN_HISTORY] if history.is_dir() else []):
        with contextlib.suppress(OSError):
            remove_tree(old)
    return problems


def replace_issue(text: str, block: str | None) -> str:
    """docs/OPEN_ISSUES.md with the train's one item replaced by `block`, or removed."""
    lines = text.split("\n")
    start = next((index for index, line in enumerate(lines) if line.startswith(f"### {TRAIN_ISSUE} ")), None)
    if start is not None:
        end = next((index for index in range(start + 1, len(lines))
                    if lines[index].startswith(("## ", "### "))), len(lines))
        del lines[start:end]
        position = start
    elif block is None:
        return text
    else:
        if TRAIN_ISSUE_SECTION not in lines:
            raise Refused(f"{TRAIN_ISSUE_FILE} has no section {TRAIN_ISSUE_SECTION!r}")
        section = lines.index(TRAIN_ISSUE_SECTION)
        position = next((index for index in range(section + 1, len(lines)) if lines[index].startswith("## ")),
                        len(lines) - (lines[-1] == ""))
    if block is not None:
        item = block.strip("\n").split("\n")
        if position > 0 and lines[position - 1] != "":
            item.insert(0, "")
        if position == len(lines) or lines[position] != "":
            item.append("")
        lines[position:position] = item
    return "\n".join(lines)


def report_findings(rows: dict, previous: dict | None) -> list[str]:
    """What a fleet build's consumer checks and row counts show, one sentence each; none refuses it."""
    findings = []
    for name in CONSUMERS:
        row = rows.get(name) or {"status": "not-configured"}
        where = f"{name} at `{row['commit'][:12]}`" if row.get("commit") else name
        if row["status"] == "not-configured":
            findings.append(f"{name}: not run (the train was given no `--consumer {name}=REPO`).")
        elif row["status"] != "passed":
            if row.get("timed_out"):
                why = "it ran past its time bound"
            elif type(row.get("exit_code")) is int and row["exit_code"]:
                why = f"exit {row['exit_code']}"
            else:
                why = row.get("error") or row["status"]
            findings.append(f"{where}: the committed check is red ({why}).")
        before = ((previous or {}).get("consumers") or {}).get(name) or {}
        then = ""
        if previous:
            then = f"build {previous['build']}" + (f" ({name} then at `{before['commit'][:12]}`)" if before.get("commit") else "")
        for kind, worse, word in (("proved", lambda new, old: new < old, "fewer"),
                                  ("failed", lambda new, old: new > old, "more")):
            new, old = row.get(kind), before.get(kind)
            if type(new) is int and type(old) is int and worse(new, old):
                findings.append(f"{where}: {new} rows {kind}, {old} on {then}: {abs(new - old)} {word}.")
    return findings


def issue_block(build: int, commit: str, date: str, findings: list[str], previous: dict | None) -> str:
    compared = (f"Row counts are compared with fleet build {previous['build']}'s run"
                if previous else "No earlier train build's row counts exist to compare with")
    return "\n".join([
        f"### {TRAIN_ISSUE} — fleet build {build}: what the consumer checks and the proof comparison found",
        f"Written by `scripts/daily_toolchain_stage.py train` after it stage-uploaded build {build} (commit",
        f"`{commit[:12]}`, {date}). The next train replaces this item, and removes it when it finds nothing.",
        "None of this held the publication: a fleet build is published on the cut's own gates",
        f"(docs/DECISION_QUEUE.md SEAL-1, D27). {compared}, each at that",
        "consumer's main of its day; the same-tree comparison (`targo trust gate compare-seal`,",
        "docs/PLAN.md PKG-V4) is not on yet.",
        *[f"- {finding}" for finding in findings]]) + "\n"


def elapsed(started: str) -> str:
    try:
        seconds = int((dt.datetime.now(dt.timezone.utc) - dt.datetime.fromisoformat(started)).total_seconds())
    except (TypeError, ValueError):
        return "an unknown time"
    return f"{seconds // 3600}h{seconds % 3600 // 60:02d}m"


def train_activity(state: dict, running: bool) -> str:
    """What the train is doing, or how its last tick ended."""
    last = state.get("last")
    if not last:
        return "a train is starting" if running else "no train has run here"
    commit = (last.get("commit") or last.get("main") or "")[:12]
    if running:
        step = None
        with contextlib.suppress(OSError, ValueError, KeyError, Refused):
            record = read_json(Path(last["build_dir"]) / "latest.json")
            step = next((s for s in reversed(record.get("steps", [])) if s.get("status") == "running"), None)
        doing = f": step {step['name']} for {elapsed(step.get('started_at'))}" if step else ""
        return f"a train has been running for {elapsed(last.get('started_at'))}: {last.get('phase')} {commit}{doing}"
    if last.get("status") == "running":
        return (f"the train that started {last.get('started_at')} at {commit} ended without a result; the next tick "
                + ("publishes again" if last.get("kind") == "publish" else "cuts again"))
    problem = f"; {last['error']}" if last.get("error") else ""
    report = f"report: {last.get('report', 'not written')}"
    if last.get("status") == "published":
        # Found served: the train's first reading of the channel head already pinned the build,
        # so the index named is that head, not necessarily the first index that served it.
        served = "found build {} ({}) served by" if last.get("found_served") else "published build {} ({}) in"
        return (f"the last train {served.format(last.get('build'), commit)} atpkg-index-{last.get('index')} "
                f"at {last.get('published_at')}; {report}{problem}")
    if last.get("status") == "staged":
        return (f"the last train staged build {last.get('build')} ({commit}) at {last.get('staged_at')} and no index "
                f"serves it{problem}; {report}")
    return f"the last train {last.get('status')} at {commit or 'no commit'} ({last.get('finished_at')}): {last.get('error')}"


def train_publication(state: dict) -> str:
    """What is left of publishing the last build the train staged, or nothing."""
    good = state.get("good") or {}
    if not good or ("index" in good and "controller_index" in good):
        return ""
    build, why = good.get("build"), f" ({good['publish_error']})" if good.get("publish_error") else ""
    # Once an index serves the build, what is left is its controller.
    what = f"{CONTROLLER} {build}" if "index" in good else f"staged build {build}"
    if good.get("custody_error"):
        return f"; {what} is never published: {good['custody_error']}"
    if good.get("superseded_by"):
        return f"; {what} was not published: the index already pins trust {good['superseded_by']}"
    if good.get("given_up"):
        return f"; {what} was not published, given up after {good.get('publish_ticks')} ticks{why}"
    if "index" in good:
        return f"; {CONTROLLER} {build} is not yet published{why}"
    return f"; build {build} is staged and not yet published{why}"


def train_status(root: Path, read: Callable[[dict], dict] | None = None) -> str:
    """One line: the newest build an index served, how far main is past it, and what the train is doing.

    A build is published when the train saw an index serve it, never for its staging tag.
    `read` asks GitHub now (Train.read_main); without it, or when it is refused, the
    line is the last tick's reading.
    """
    state = load_train(root)
    with train_lock(root) as free:
        running = not free
    main = dict(state.get("main") or {})
    if read is not None:
        try:
            main = read(state)
        except (Refused, OSError) as error:
            main["stale"] = f"GitHub was not read now ({error})"
    published = state.get("published") or {}
    count, tip = main.get("count"), main.get("commit")
    if not published:
        head = "no published build is known"
    else:
        age = str(count - published["build"]) if count is not None else "an unknown number of"
        found = "found served by " if published.get("found_served") else ""
        head = f"last published build {published['build']} ({found}atpkg-index-{published['index']}), {age} commits behind main"
    if tip:
        head += f" ({tip[:12]}" + (f", build {count}" if count is not None else "") + f", read {main.get('read_at')})"
    if main.get("staged") is not None and main["staged"] != published.get("build"):
        head += f"; newest staged build {main['staged']}"
    if main.get("stale"):
        head += f"; {main['stale']}"
    return f"train: {head}{train_publication(state)}; {train_activity(state, running)}"


class Train:
    """One tick of the standing train. `Runner.stage` calls before_cut and after_cut."""

    BOUND = 4 * 3600  # one publisher step: pack, smoke, hello world and the upload, or a canary or index publish
    STATUS_BOUND = 1800  # one `atpkg-publish status`: building the publisher and reading the channel head
    LAND_BOUND = 2 * 3600  # one run of scripts/prewarm_push.sh: its merges and the push hook
    LAND_ATTEMPTS = 4

    def __init__(self, args: argparse.Namespace, execute: Callable = command, github=None,
                 tools: dict[str, str] | None = None):
        self.args = args
        self.root = args.state_root.resolve()
        self.execute = execute
        self.github = github
        self.tools = tools or {}
        self.state: dict = {}
        self.agh: dict | None = None

    def save(self) -> None:
        atomic_json(self.root / "train.json", self.state)

    def note(self, **fields) -> None:
        self.state["last"].update(fields)
        self.save()

    def source_objects(self) -> TrainSourceObjects:
        if not hasattr(self, "_source_objects"):
            owner = runpy.run_path(str(Path(__file__).with_name("recreate_bootstrap.py")),
                                   run_name="train_source_objects")
            self._source_objects = TrainSourceObjects(self.root, owner, self.args.source_object_cache)
        return self._source_objects

    def tool(self, name: str) -> str:
        # Not resolved: agh and the targo shim are links that choose their program by name.
        found = self.tools.get(name) or shutil.which(name)
        if not found or not Path(found).is_absolute():
            raise Refused(f"the train needs `{name}` in an absolute PATH directory")
        return found

    def remote(self):
        if self.github is None:
            slug = self.args.github_repo
            if not slug:
                origin = subprocess.run(["git", "-C", str(self.args.repo), "config", "--get", "remote.origin.url"],
                                        capture_output=True, text=True, timeout=60).stdout.strip()
                slug = github_slug(origin)
            self.github = GitHub(slug, self.tool("agh"), self.root / "github.log")
        return self.github

    def portable(self, text: str) -> str:
        """Text for a committed file: no path of this Mac."""
        return text.replace(str(self.root), "<train state>").replace(str(Path.home()), "~")

    def read_main(self, state: dict | None = None) -> dict:
        """Main's tip, its build number where that can be counted, and the newest staged build (its tag)."""
        github, state = self.remote(), self.state if state is None else state
        tip, builds = github.main(), github.builds()
        # Counted in --repo when it already holds the tip (nothing is fetched into it), else
        # from the last cut's count and GitHub's compare, which a rate limit can refuse.
        local = subprocess.run(["git", "-C", str(self.args.repo), "rev-list", "--count", tip],
                               capture_output=True, text=True, timeout=600)
        count, anchor = None, state.get("anchor")
        if local.returncode == 0 and local.stdout.strip().isdecimal():
            count = int(local.stdout)
        elif anchor:
            ahead = 0 if anchor["commit"] == tip else github.ahead(anchor["commit"])
            count = None if ahead is None else anchor["count"] + ahead
        return {"commit": tip, "count": count, "staged": builds[-1] if builds else None, "read_at": now()}

    def tick(self) -> int:
        with train_lock(self.root) as owned:
            if not owned:
                print("train: nothing started: " + train_activity(load_train(self.root), True))
                return 0
            # One Agh for the whole tick: the GitHub reader, the cut's acquisitions and the
            # publisher's steps (keep_agh), including the runner's own source update.
            kept = contextlib.nullcontext() if "agh" in self.tools else agh_kept_in(self.root)
            with kept as self.agh:
                if self.args.dry_run or TRAIN_ADVANCED in os.environ or not self.advance():
                    return self.locked()
            # Restore the installed Agh search path before exec. The new runner takes the
            # lock again and can keep or reuse Agh under its own code.
            print(f"train: {Path(__file__).name} changed on main; this tick runs the new one", flush=True)
            sys.stderr.flush()
            os.environ[TRAIN_ADVANCED] = "1"
            os.execv(sys.executable, [sys.executable, *sys.argv])

    def advance(self) -> bool:
        """Fast-forward --repo to origin's main between ticks; whether this runner's bytes changed.

        The train's agent runs this file from --repo's working tree, and nothing else moves
        that tree, so without this a fix to the runner on main never reaches a standing
        train. The caller holds the train's lock, so no tick is running. Only a clean
        checkout on main moves, and only forward; anything else is said and the tick runs
        the checkout as it is. The source a tick cuts comes from origin either way.
        """
        repo, runner = self.args.repo.resolve(strict=True), Path(__file__).resolve()
        # The private intake, with Agh's scratch inside it, is made in the state root and
        # removed after the fetch. One left here belongs to an advance whose process was
        # killed with it; the caller holds the lock, so none is running.
        for stale in sorted(self.root.glob("controller-intake-*.noindex")):
            try:
                if stale.is_dir() and not stale.is_symlink():
                    remove_tree(stale)
            except OSError as error:
                print(f"train: the controller intake {stale} was not removed: {error}")

        def git(*argv: str, directory: Path = repo, environment: dict | None = None,
                required: bool = False) -> subprocess.CompletedProcess:
            result = subprocess.run([fixed_git, "-C", str(directory), "-c", "submodule.recurse=false", *argv],
                                    env=git_environment if environment is None else environment, capture_output=True, text=True,
                                    timeout=600, stdin=subprocess.DEVNULL)
            if required and result.returncode:
                raise Refused(f"controller update: git {argv[0]} failed ({result.stderr.strip()[-500:]})")
            return result

        def clean_main() -> str:
            branch = git("symbolic-ref", "--quiet", "--short", "HEAD").stdout.strip()
            if branch != "main":
                raise Refused(f"is on {branch or 'a detached HEAD'}, not main")
            status = git("status", "--porcelain", "--untracked-files=no", "--ignore-submodules=all")
            if status.returncode:
                raise Refused("could not check whether the checkout is clean")
            if status.stdout.strip():
                raise Refused("has uncommitted changes")
            head = git("rev-parse", "--verify", "HEAD")
            if head.returncode:
                raise Refused("could not read main's local commit")
            return head.stdout.strip()

        try:
            recreator = runpy.run_path(str(runner.with_name("recreate_bootstrap.py")),
                                       run_name="daily_managed_git_owner")
            git_environment = recreator["_provenance_git_environment"]()
            git_environment.update(GIT_NO_LAZY_FETCH="1", GIT_NO_REPLACE_OBJECTS="1", GIT_ALLOW_PROTOCOL="")
            fixed_git = str(recreator["_require_fixed_git"]())
            head = clean_main()
            urls = [value for _, key, value in recreator["_repository_git_config_records"](repo)
                    if key == "remote.origin.url"]
            if len(urls) != 1:
                raise Refused("needs one literal GitHub origin for its source update")
            slug = github_slug(urls[0])
            github = self.remote()
            if github.slug.lower() != slug.lower():
                raise Refused("the selected GitHub repository differs from the checkout's origin")
            tip = github.main()
            tracking = "refs/remotes/origin/main"
            tracked = git("rev-parse", "--verify", "--quiet", tracking)
            if tracked.returncode not in (0, 1):
                raise Refused("could not read the local origin/main ref")
            previous = tracked.stdout.strip()
            if head == tip == previous:
                return False

            before = file_hash(runner)
            # The controller needs its pre-push hook. Agh admits a private intake
            # with a literal origin and negotiates complete history against local objects.
            url = f"https://github.com/{slug}.git"
            private_ref = "refs/agh/trust-train/advance"
            self.root.mkdir(parents=True, exist_ok=True)
            with tempfile.TemporaryDirectory(prefix="controller-intake-", suffix=".noindex", dir=self.root) as temp:
                intake, bundle = Path(temp) / "source", Path(temp) / "incoming.bundle"
                git("clone", "--local", "--no-checkout", "--no-recurse-submodules", "--single-branch",
                    "--branch", "main", "--no-tags", "--template=", "--", str(repo), str(intake),
                    directory=Path(temp), environment={**git_environment, "GIT_ALLOW_PROTOCOL": "file"}, required=True)
                git("remote", "set-url", "origin", url, directory=intake, required=True)
                recreator["_agh_source_fetch"](url, intake, tip, private_ref, native_exact=True,
                                               scratch_parent=Path(temp))
                if git("merge-base", "--is-ancestor", head, tip, directory=intake).returncode:
                    raise Refused("local main does not fast-forward to the authenticated origin tip")
                # NativeExact also repairs missing historical objects in its intake.
                # Excluding head from the bundle is valid only if the controller
                # already has everything reachable from that commit.
                raw_graph = {**git_environment, "GIT_GRAFT_FILE": os.devnull, "GIT_SHALLOW_FILE": os.devnull}
                graph_args = ("-c", "core.commitGraph=false")
                complete = git(*graph_args, "rev-list", "--objects", "--quiet", "--missing=error", head,
                               environment=raw_graph).returncode == 0
                if tip != head or not complete:
                    exclusions = ["^" + head] if complete else []
                    git(*graph_args, "bundle", "create", str(bundle), private_ref, *exclusions, directory=intake,
                        environment=raw_graph, required=True)
                    git("bundle", "unbundle", str(bundle), required=True)
            if clean_main() != head:
                raise Refused("local main changed during the Agh acquisition")
            if git("merge-base", "--is-ancestor", head, tip).returncode:
                raise Refused("local main does not fast-forward to the authenticated origin tip")
            if previous != tip:
                if previous and git("merge-base", "--is-ancestor", previous, tip).returncode:
                    raise Refused("local origin/main does not fast-forward to the authenticated origin tip")
                if git("update-ref", tracking, tip, previous or "0" * len(tip)).returncode:
                    raise Refused("local origin/main changed during the Agh acquisition")
            merged = git("merge", "--quiet", "--ff-only", tip)
            if merged.returncode:
                raise Refused(f"could not fast-forward local main ({merged.stderr.strip()[-300:]})")
            return file_hash(runner) != before
        except (OSError, RuntimeError, subprocess.SubprocessError) as error:
            print(f"train: {repo} {error}; the tick runs it as it is")
            return False

    def locked(self) -> int:
        if not self.args.aterm_repo:
            raise Refused("the train needs --aterm-repo: aterm's publisher signs and uploads the pack")
        self.state = load_train(self.root)
        last = self.state.get("last")
        if last and last.get("status") == "running":
            # This process holds the lock, so the train that wrote "running" is gone.
            if last.get("build") is not None:
                last["finished_at"] = now()
                self.settle()
                if last["status"] == "staged":
                    last.setdefault("error", "the train's process ended before an index served the build")
                last.setdefault("report", "not written: the train's process ended first")
            else:
                last.update(status="interrupted", finished_at=now(),
                            error="the train's process ended before it recorded a result")
            self.save()
        github = self.remote()
        self.state["main"] = self.read_main()
        self.save()
        tip, count = self.state["main"]["commit"], self.state["main"]["count"]
        # What an earlier tick staged and no index serves is published before another cut.
        pending, abandoned = self.pending(), None
        if pending and self.args.dry_run:
            print(f"train: would first publish staged build {pending['build']} ({pending['commit'][:12]}), "
                  f"tick {pending.get('publish_ticks', 0) + 1} of {PUBLISH_TICKS}:\n"
                  + "\n".join(self.publication_plan(pending["build"], "<its build>/group", True)))
        elif pending:
            ended = self.finish(pending)
            if ended is not None:
                return ended
            # This tick gave the build up, or found its custody broken: the tick has failed,
            # though a cut may follow.
            abandoned = pending.get("given_up") or pending.get("custody_error")
        published = (self.state.get("published") or {}).get("build")
        cut, reason = train_decision(self.state, tip, published, count)
        if not cut:
            print(f"train: nothing to cut: {reason}")
            return 1 if abandoned else 0
        if self.args.dry_run:
            consumers = ", ".join(sorted(consumer_mappings(self.args.consumer))) or "none configured"
            host, checked = self.args.publisher_host, self.index_hosts_check()
            print(f"train: would cut {tip[:12]}" + (f" (build {count})" if count is not None else "") + f": {reason}\n"
                  f"  1. ask first: `aterm secrets status` says release signing is ready; aterm's `atpkg-publish hosts check --host {host}`"
                  + (f" and `hosts check --host {checked}`" if checked else "") + ";\n"
                  f"     `agh repo check-local` admits the source snapshot; `agh can {github.slug} push`; --repo's pushes run scripts/hooks/pre-push;\n"
                  "     the landing worktree at the cut commit, its submodules materialized at the cut's pins\n"
                  "  2. cut: the mint (double compile, self-host proof), the seal, the trust-wp drivers, the staged tree's gates\n"
                  f"  3. aterm's `atpkg-publish --host {host} publish-group rustc --dry-run`: its preflight, before anything is published\n"
                  "  4. scripts/publish_seed_cut.sh --publish: the seed archives' release and the re-pin branch\n"
                  "  5. scripts/prewarm_push.sh from the landing worktree: the re-pin reaches main through the push hook; its branch is deleted\n"
                  f"  6. `atpkg-publish --host {host} publish-group rustc --stage-upload`: the signed packs reach the staging owner\n"
                  + "\n".join(self.publication_plan(count if count is not None else "<N>", "<build>/group", False)) + "\n"
                  f"  {9 if self.args.index_host != 'none' else 8}. then: the consumer checks ({consumers}) and the row-count "
                  f"comparison; what they find is\n     {TRAIN_ISSUE} in {TRAIN_ISSUE_FILE}, landed the same way")
            return 0
        good = self.state.get("good")
        if self.args.source_object_cache:
            self.source_objects().retain_failed(self.state.get("last"), good)
        for problem in retire_builds(self.root, Path(good["build_dir"]) if good else None):
            print(f"train: {problem}", file=sys.stderr)
        build = self.root / "builds" / (dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ") + "-" + tip[:12])
        build.mkdir(parents=True)
        atomic_json(build / "train-build.json", {"schema": TRAIN_SCHEMA, "main": tip, "started_at": now()})
        self.state["last"] = {"status": "running", "phase": "starting", "build_dir": str(build), "main": tip,
                              "commit": None, "build": None, "landed": None, "started_at": now(), "pid": os.getpid()}
        self.save()
        last = self.state["last"]
        try:
            arguments = copy.copy(self.args)
            arguments.state_root, arguments.mode = build, "stage"
            # The snapshot rechecks that the tick's chosen commit still belongs to main.
            arguments.source_commit = tip
            runner = Runner(arguments, self.execute, train=self)
            result = runner.run()
        except BaseException as error:
            if last["build"] is None:
                last.update(status="interrupted" if isinstance(error, (KeyboardInterrupt, InterruptedError)) else "failed",
                            error=str(error) or type(error).__name__)
            else:
                self.settle()
                last["error"] = "; ".join(filter(None, [last.get("error"), f"after the upload: {error}"]))
            self.note(finished_at=now())
            raise
        commit = runner.record.get("source_commit")
        last.update(commit=commit, finished_at=now())
        if last["build"] is not None:
            self.settle()
            if result:
                last["error"] = "; ".join(filter(None, [last.get("error"), f"after the upload: {runner.record.get('error')}"]))
        elif runner.record.get("interrupted"):
            last.update(status="interrupted", error=runner.record.get("error"))
        else:
            last.update(status="failed", error=runner.record.get("error", "no error recorded"))
            if last["landed"] or commit:
                # The same commit is not cut again; the next tick waits for main to move.
                self.state["settled"] = last["landed"] or commit
        self.save()
        print("train: " + train_activity(self.state, False))
        # Done is published, or staged where this train publishes nothing more (--index-host
        # none, or an index already past the build), from a run whose every check passed. A
        # publication left over is the next tick's; a build whose custody broke is never published.
        good = self.state.get("good") or {}
        refused = good.get("publish_error") or good.get("custody_error")
        done = last["status"] in ("published", "staged") and self.pending() is None and not refused
        return 0 if done and result == 0 and not abandoned else 1

    def settle(self) -> None:
        """The last tick's status from its build: published once an index serves it, else staged."""
        last, good = self.state["last"], self.state.get("good") or {}
        if good.get("build") == last.get("build") and "index" in good:
            last.update(status="published", index=good["index"], published_at=good["served_at"])
            if "trust" in good.get("found_served", []):
                last["found_served"] = True
        else:
            last["status"] = "staged"

    def pending(self) -> dict | None:
        """The last build this train staged, while an index is still to serve it or its controller."""
        good = self.state.get("good")
        if (self.args.index_host == "none" or not good or good.get("given_up") or good.get("superseded_by")
                or good.get("custody_error") or ("index" in good and "controller_index" in good)):
            return None
        return good

    def index_hosts_check(self) -> str | None:
        """The host the index is written through, when the publisher host's check does not cover it."""
        host = self.args.index_host
        return None if host in ("none", self.args.publisher_host) else host

    def publication_plan(self, build, group: str, resumed: bool) -> list[str]:
        """The dry run's lines for what follows a stage-upload, or for publishing a build an earlier tick staged."""
        host = self.args.index_host
        custody = ("  7. its custody: the source snapshot clean at the cut commit and each artifact the train keeps of a build"
                   if resumed else "  7. the run's end checks: the source snapshot clean at the cut commit; every artifact, the Lean"
                   "\n     installation, the interpreter and the serial command unchanged") + \
            " (a build that fails is never published);"
        if host == "none":
            return [custody, "     the index is not changed (--index-host none): the build stays staged"]
        return [custody, f"     then through `atpkg-publish --host {host}`: `canary trust={build} --out {group}/canary` installs and runs the",
                "     staged pack and signs its receipt; `publish-group rustc --publish-staged --out "
                f"{group}` publishes the index that pins the group,",
                f"     run again on the new head when another publisher took the next index number, at most {INDEX_ATTEMPTS} "
                f"runs; `status` then shows trust {build} served",
                f"  8. `pack {CONTROLLER} --build {build} --upload` from the cut commit, its source checked again, then "
                f"`index --pin {CONTROLLER}={build} --upload`, the same way;",
                f"     a refused publication is tried again by the next tick, at most {PUBLISH_TICKS} ticks, before another cut"]

    def finish(self, good: dict) -> int | None:
        """Publish a build an earlier tick staged and no index serves yet, before anything is cut.

        Returns the tick's exit when the tick ends here, or None to go on to the cut: the build
        is published, an index already pins a newer one, PUBLISH_TICKS ticks were refused, or
        its custody broke.
        """
        previous = self.state.get("last") or {}
        self.state["last"] = {"status": "running", "kind": "publish", "phase": f"publishing staged build {good['build']}",
                              "build_dir": good["build_dir"], "main": self.state["main"]["commit"],
                              "commit": good["commit"], "build": good["build"], "landed": None,
                              "staged_at": good.get("staged_at"), "started_at": now(), "pid": os.getpid()}
        if previous.get("build") == good["build"] and previous.get("report"):
            self.state["last"]["report"] = previous["report"]
        self.begin_publication()
        arguments = copy.copy(self.args)
        arguments.state_root, arguments.mode = Path(good["build_dir"]), "stage"
        try:
            Runner(arguments, self.execute, train=self).resume(self.publish_resumed)
        except (KeyboardInterrupt, InterruptedError) as error:
            self.settle()
            self.note(error=f"interrupted while publishing: {error}", finished_at=now())
            raise
        except Exception as error:
            self.publish_failed(error)
        self.settle()
        self.note(finished_at=now())
        print("train: " + train_activity(self.state, False))
        return None if self.pending() is None else 1

    def begin_publication(self) -> None:
        good = self.state["good"]
        good["publish_ticks"] = good.get("publish_ticks", 0) + 1
        good.pop("publish_error", None)
        self.save()

    def publish_failed(self, error: BaseException) -> None:
        """Record a refused publication; after PUBLISH_TICKS ticks the train moves on to the next cut.

        A broken custody is no refusal to try again: the build, or its controller, is never published.
        """
        good, last = self.state["good"], self.state["last"]
        what = f"{CONTROLLER} {good['build']}" if "index" in good else f"build {good['build']}"
        if isinstance(error, CustodyBroken):
            good["custody_error"] = str(error)
            last["error"] = f"{what} is never published: {error}"
            self.save()
            return
        good["publish_error"] = str(error) or type(error).__name__
        last["error"] = f"{what} was not published: {good['publish_error']}"
        if good["publish_ticks"] >= PUBLISH_TICKS:
            good["given_up"] = now()
            last["error"] += f"; given up after {good['publish_ticks']} ticks, the next cut supersedes it"
        self.save()

    def git_here(self, runner: Runner, name: str, cwd: Path, *argv: str) -> str:
        """Git as this Mac's agents run it, in a checkout of --repo with its own configuration."""
        return runner.call(name, ["git", *argv], cwd, env=self.machine, timeout=1800)

    def landing_checkout(self, runner: Runner) -> Path:
        """The train's own linked worktree of --repo, where its pushes to main are made.

        A push from it runs the pre-push hook --repo configures, as any agent's push does.
        """
        landing, repo = self.root / "landing.noindex", self.args.repo.resolve(strict=True)
        if landing.is_symlink():
            raise Refused(f"the landing worktree must not be a link: {landing}")
        if not landing.exists():
            self.git_here(runner, "landing-worktree", repo, "worktree", "add", "--detach", str(landing), "HEAD")

        def common(label: str, path: Path) -> Path:
            return Path(self.git_here(runner, label, path, "rev-parse", "--path-format=absolute", "--git-common-dir")).resolve()
        if (Path(self.git_here(runner, "landing-root", landing, "rev-parse", "--show-toplevel")).resolve() != landing
                or common("landing-owner", landing) != common("checkout-owner", repo)):
            raise Refused(f"{landing} is not the train's linked worktree of {repo}")
        try:
            hooks = Path(self.git_here(runner, "landing-hook", landing, "config", "--get", "core.hooksPath"))
        except CommandFailed as error:
            raise Refused(f"{repo} sets no core.hooksPath, so a push from this Mac runs no hook; a train lands "
                          "through the push gate (bash scripts/install-git-hooks.sh)") from error
        hook = (hooks if hooks.is_absolute() else landing / hooks) / "pre-push"
        if not hook.is_file() or not os.access(hook, os.X_OK):
            raise Refused(f"{hook} is not an executable file, so a push from this Mac runs no hook")
        return landing

    def clear_landing(self, runner: Runner, name: str, landing: Path) -> None:
        """Detach the landing worktree, clean; a landing that ended early left its branch and merge here."""
        left = subprocess.run(["git", "-C", str(landing), "symbolic-ref", "--quiet", "--short", "HEAD"],
                              capture_output=True, text=True, timeout=60).stdout.strip()
        self.git_here(runner, f"{name}-clear", landing, "reset", "--quiet", "--hard")
        self.git_here(runner, f"{name}-detach", landing, "checkout", "--quiet", "--detach")
        if left.startswith("trust-train/"):
            self.git_here(runner, f"{name}-drop-left-branch", landing, "branch", "--quiet", "-D", left)

    @staticmethod
    def landing_left_state(landing: Path) -> bool:
        """Whether the landing worktree holds a path Git does not track or a child with changed files."""
        status = subprocess.run(["git", "-C", str(landing), "status", "--porcelain=v2", "--untracked-files=normal",
                                 "--ignore-submodules=none"], capture_output=True, text=True, timeout=300)
        for line in status.stdout.splitlines():
            fields = line.split(" ")
            # `1 XY S<c><m><u> ...`: a submodule's tracked changes (m) or untracked files (u).
            if line.startswith("?") or (fields[0] in ("1", "2") and len(fields) > 2 and fields[2].startswith("S")
                                        and (fields[2][2] == "M" or fields[2][3] == "U")):
                return True
        return False

    def landing_submodules(self, runner: Runner, landing: Path, name: str) -> None:
        """The landing worktree's submodules, initialized and at the pins of its HEAD.

        A linked worktree starts with none, and on such a tree the pre-push hook's pin lanes
        are red. They are materialized by the owner that materializes the snapshots'
        (recreate_bootstrap.py's ensure_submodules, through Agh). The worktree's registrations
        are --repo's own, shared with every other worktree of that clone, so the train only
        reads them: one that is not the indexed .gitmodules URL, which that owner refuses (a
        clone made from local stores registers local paths, and Git will not clone a submodule
        from one), refuses the tick with the commands that set it.
        """
        owner = runner.git_owner()
        repo = self.args.repo.resolve(strict=True)
        # The worktree keeps --repo's hooks path: its pushes run the hook.
        with owner["admitted_trust_checkout"](landing):
            off = owner["submodule_registrations_off_index"](landing)
            if off:
                raise Refused(
                    f"{repo} registers {', '.join(module for module, _values, _url in off)} by another URL than the "
                    "indexed .gitmodules one, and the train's landing worktree shares those registrations and does "
                    "not rewrite them; to register the indexed URLs: "
                    + "; ".join(shlex.join(["git", "-C", str(repo), "config", "--replace-all", f"submodule.{module}.url", url])
                                for module, _values, url in off))
            try:
                pins = runner.synchronize(landing, f"landing-{name}")
            except Refused as error:
                # reset --hard does not reach the children: a child left dirty or past its pin
                # with commits no local ref holds (scripts/submodule_sync.sh exit 2), or a
                # staging directory a failed acquisition kept, stays in the train's tree.
                restore_refused = (isinstance(error, CommandFailed) and error.exit_code == 2
                                   and runner.record["steps"][-1]["name"] == "submodule-sync")
                if not (restore_refused or self.landing_left_state(landing)):
                    raise
                raise Refused(f"{error}; {landing} is the train's own landing worktree and holds no one else's "
                              f"work, and the next tick makes it again once it is gone: "
                              f"rm -rf {shlex.quote(str(landing))} && git -C {shlex.quote(str(repo))} worktree prune") from error
        runner.record.setdefault("landing_submodules", {})[name] = pins
        runner.save()

    def land(self, runner: Runner, name: str, branch: str, change: Callable[[Path], str | None] | None = None) -> bool:
        """Land the re-pin, and the commit `change` makes on it, on main; whether anything was pushed.

        The push is scripts/prewarm_push.sh's: it merges main into the branch and pushes
        the branch to main through the pre-push hook, never forced and never --no-verify.
        """
        landing = self.landing_checkout(runner)
        repin, source_branch = runner.record["mint"]["repin_commit"], runner.record["mint"]["repin_branch"]

        def git(step: str, *argv: str) -> str:
            return self.git_here(runner, f"{name}-{step}", landing, *argv)
        self.clear_landing(runner, name, landing)
        git("fetch-re-pin", "fetch", "--quiet", "--no-tags", "--no-write-fetch-head", "--no-recurse-submodules",
            str(runner.source), f"+refs/heads/{source_branch}:refs/trust-train/re-pin")
        if git("re-pin", "rev-parse", "--verify", "refs/trust-train/re-pin^{commit}") != repin:
            raise Refused("the source snapshot's re-pin branch is not the mint's re-pin")
        git("branch", "checkout", "--quiet", "-B", branch, repin)
        if change is not None:
            message = change(landing)
            if message is None:
                git("nothing-to-land", "checkout", "--quiet", "--detach")
                git("drop-branch", "branch", "--quiet", "-D", branch)
                return False
            git("add", "add", "--", TRAIN_ISSUE_FILE)
            git("commit", "commit", "--quiet", "-m", message)
        # What is pushed is pushed with its submodules at its own pins, which before_cut
        # showed this Mac can materialize for the cut commit.
        self.landing_submodules(runner, landing, name)
        push = ["bash", str(landing / "scripts/prewarm_push.sh"), "--max-rounds", str(self.LAND_ATTEMPTS),
                "--log-dir", str(runner.invocation / f"{name}-push")]
        # The helper takes its source lease with `targo trust repo lock`, which the Mac's
        # installed Targo can predate (the fleet's build 16387 does, and the helper then
        # refuses before it merges). The build just cut from this source has it.
        environment = {**self.machine, "TARGO": str(Path(runner.record["staged_toolchain"]) / "bin/targo")}
        for attempt in range(1, self.LAND_ATTEMPTS + 1):
            try:
                runner.call(f"{name}-push-{attempt}", push, landing, heavy=True, env=environment, timeout=self.LAND_BOUND)
                break
            except CommandFailed as error:
                # Exit 6: main moved under every round. Exit 4: the helper merged main's
                # newer compiler sources into the branch and asks for a build of them
                # before the next run. The branch's own change is a re-pin the mint
                # proved, or one documentation item: it has no source to build against
                # what main gained, and whether the pin builds main is the next cut's
                # first build (docs/CUTTING-A-TOOLCHAIN.md). So the helper runs again.
                if error.exit_code not in (4, 6):
                    raise
                # The merge the helper kept for exit 4 can move first-party gitlinks; its
                # next run only restores children offline (no `--fetch`) and stops (exit 7)
                # at a pin the landing worktree lacks. Acquire the merged pins first.
                if error.exit_code == 4:
                    self.landing_submodules(runner, landing, f"{name}-merged-{attempt}")
        else:
            raise Refused(f"main moved under {self.LAND_ATTEMPTS} runs of scripts/prewarm_push.sh for {branch}")
        # Main holds only the cut commit and the train's own commits when every commit
        # past the cut is on this branch's first-parent line; then the tip is not a move.
        head = git("landed", "rev-parse", "HEAD")
        if (git("past-the-cut", "rev-list", "--count", head, f"^{runner.commit}")
                == git("own-commits", "rev-list", "--count", "--first-parent", head, f"^{runner.commit}")):
            self.note(landed=head)
        git("landed-detach", "checkout", "--quiet", "--detach")
        git("landed-branch", "branch", "--quiet", "-D", branch)
        return True

    def before_cut(self, runner: Runner) -> None:
        """Ask what would stop the upload, before the mint."""
        self.note(phase="asking whether this Mac can publish", commit=runner.commit)
        github = self.remote()
        self.attach(runner)
        # No line of the answer is kept: the log holds the command and its exit.
        runner.call("release-signing-ready", ["/bin/sh", "-c", '"$0" secrets status | grep -q "^release signing: ready"',
                                              self.tool("aterm")], timeout=300)
        commit = runner.snapshot(self.args.aterm_repo.resolve(strict=True), self.aterm, "aterm")
        pins = runner.synchronize(self.aterm, "package-producer")
        runner.record["package_producer"] = {"commit": commit, "path": str(self.aterm), "submodules": pins}
        # The publisher is built by the Mac's own toolchain, not by the build being cut.
        self.publisher(runner, "publisher-hosts-check", ["hosts", "check"], self.args.publisher_host)
        if self.index_hosts_check():
            self.publisher(runner, "index-hosts-check", ["hosts", "check"], self.index_hosts_check())
        # The publisher reads the source snapshot as its Trust checkout, through this guard.
        runner.call("trust-repo-admitted", [self.tool("agh"), "repo", "check-local", github.slug, str(runner.source)],
                    timeout=300)
        if github.can_push() is None:
            runner.record.setdefault("train_notes", []).append("`agh can push` was not answered for a rate limit")
        # The landing worktree at the cut commit, its submodules at the cut's pins: a Mac that
        # cannot materialize them ends the tick here, before the mint and before step 4 pushes
        # the seed re-pin, rather than at a red push gate after it.
        # Source materialization can outlast the host checks, especially while
        # synchronizing large pinned children. Name that work before it starts;
        # credential readiness is already answered and does not describe it.
        self.note(phase="materializing landing source")
        landing = self.landing_checkout(runner)
        self.clear_landing(runner, "landing", landing)
        self.git_here(runner, "landing-fetch-cut", landing, "fetch", "--quiet", "--no-tags", "--no-write-fetch-head",
                      "--no-recurse-submodules", str(runner.source), "+HEAD:refs/trust-train/cut")
        if self.git_here(runner, "landing-cut", landing, "rev-parse", "--verify", "refs/trust-train/cut^{commit}") != runner.commit:
            raise Refused("the source snapshot's HEAD is not the cut commit")
        self.git_here(runner, "landing-at-cut", landing, "checkout", "--quiet", "--detach", runner.commit)
        self.landing_submodules(runner, landing, "cut")
        self.note(phase="cutting")

    def attach(self, runner: Runner) -> None:
        """The publisher's checkout and this Mac's own toolchain and Git, for a cut or a resumed publication.

        The Mac's environment is the runner's without the cut's scratch homes.
        """
        self.machine = bootstrap_environment(runner.env, runner.source / "scripts/recreate_bootstrap.py")
        self.machine["PYTHON"] = str(runner.python)
        self.aterm = runner.state / "aterm-source"

    def publisher(self, runner: Runner, name: str, words: list[str], host: str | None = None,
                  timeout: int | None = None) -> str:
        """One command of aterm's publisher (fleet_publisher), built by this Mac's targo; its output.

        A refusal carries the publisher's own last `atpkg-publish: …` line.
        """
        try:
            return runner.call(name, fleet_publisher(self.tool("targo"), host or self.args.index_host, words),
                               self.aterm, heavy=True, env=self.machine, timeout=timeout or self.BOUND)
        except CommandFailed as error:
            why = publisher_refusal(Path(runner.last_step()["log"]))
            if why is None:
                raise
            raise CommandFailed(f"{name}: {why}", error.exit_code, error.timed_out) from error

    def serving(self, runner: Runner, name: str) -> tuple[int, dict[str, int]]:
        """The channel head's index number and the pins a client on the cut's host installs."""
        return index_pins(self.publisher(runner, name, ["status"], timeout=self.STATUS_BOUND), runner.host)

    def publish_index(self, runner: Runner, name: str, words: list[str], program: str, build: int) -> tuple[int, dict[str, int]]:
        """One index publish, run again on the new channel head when another publisher took the next number.

        The publisher reads the head afresh on each run; the train reads it too between runs,
        and stops when that head already pins `program` at `build` or later. At most
        INDEX_ATTEMPTS runs; any other refusal is raised at once.
        """
        for attempt in range(1, INDEX_ATTEMPTS + 1):
            try:
                self.publisher(runner, f"{name}-{attempt}", words)
            except CommandFailed:
                if not lost_index_race(Path(runner.last_step()["log"])):
                    raise
                index, pins = self.serving(runner, f"{name}-head-{attempt}")
                if pins.get(program, 0) >= build:
                    return index, pins
                continue
            return self.serving(runner, f"{name}-served")
        raise Refused(f"another publisher took the next index number under each of {INDEX_ATTEMPTS} runs of {name}")

    def hold_custody(self, check: Callable[[], None]) -> None:
        """Run one of the runner's custody checks; a failure is CustodyBroken, and the build is never published."""
        try:
            check()
        except InterruptedError:
            raise
        except (Refused, OSError) as error:
            raise CustodyBroken(f"its custody check failed: {error}") from error

    def publish_resumed(self, runner: Runner) -> None:
        self.attach(runner)
        self.hold_custody(runner.resumed_custody)
        self.publish(runner)

    def publish(self, runner: Runner) -> None:
        """Have the signed index serve the staged build, then trust-resource-controller from its commit.

        Each part starts from the channel head that `atpkg-publish status` reads, so a tick
        after a refusal, a lost race or a restart does only what is left. The index recorded
        for a part is the head read after its own publish; a part the first reading finds
        already served records that head and says so (`found_served`), since which index
        first served it is not known. Once recorded, it is not read again.
        """
        good = self.state["good"]
        build, root = good["build"], Path(good["build_dir"])
        group = root / "group"
        if runner.commit != good["commit"]:
            raise CustodyBroken(f"its custody check failed: {root} holds a cut of {runner.commit}, not {good['commit']}")
        self.note(phase=f"publishing build {build} to the index")
        index, pins = self.serving(runner, "index-status")
        if "index" not in good:
            if pins.get("trust") == build:
                # A tick that ended after its index publish, or another publisher, got here first.
                good["found_served"] = ["trust"]
            elif pins.get("trust", 0) < build:
                canary = group / "canary"
                if not all((canary / name).is_file() for name in ("train-receipt.toml", "train-receipt.toml.sig")):
                    if canary.exists():
                        # A canary that ended early: the publisher signs only into a fresh directory.
                        canary.rename(group / ("canary." + dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")))
                    # The canary judges the installed pack's integrity. Its consumer keys get
                    # directories that do not exist, so it builds in no developer checkout; the
                    # consumers are this train's own checks, run after publication.
                    absent = root / "canary-consumers"
                    self.note(phase=f"running the canary of build {build}")
                    self.publisher(runner, "canary", ["canary", f"trust={build}", "--out", str(canary),
                                                      *[word for name in CONSUMERS
                                                        for word in ("--consumer", f"{name}={absent / name}")]])
                self.note(phase=f"publishing build {build} to the index")
                index, pins = self.publish_index(runner, "publish-staged", ["publish-group", "rustc", "--publish-staged",
                                                                            "--out", str(group)], "trust", build)
            if pins.get("trust", 0) > build:
                good["superseded_by"] = pins["trust"]
                self.note(error=f"build {build} was not published: atpkg-index-{index} already pins trust {pins['trust']}")
                return
            if pins.get("trust") != build:
                raise Refused(f"the index publish ended and atpkg-index-{index} pins trust {pins.get('trust')}, not {build}")
            good.update(index=index, served_at=now())
            self.state["published"] = {"build": build, "commit": good["commit"], "index": index, "at": good["served_at"],
                                       "found_served": "found_served" in good}
            runner.record["published"] = {"build": build, "index": f"atpkg-index-{index}", "at": good["served_at"],
                                          "found_served": list(good.get("found_served", []))}
            runner.save()
            self.note(index=index, published_at=good["served_at"])
        elif pins.get("trust", 0) > build:
            # Served earlier; an index now pins a newer trust, so this build's controller is not published.
            good["superseded_by"] = pins["trust"]
            self.note(error=f"{CONTROLLER} {build} was not published: atpkg-index-{index} already pins trust {pins['trust']}")
            return
        self.note(phase=f"publishing {CONTROLLER} {build}")
        if pins.get(CONTROLLER, 0) >= build:
            good.setdefault("found_served", []).append(CONTROLLER)
            runner.record["published"]["found_served"] = list(good["found_served"])
        else:
            if not good.get("controller_staged"):
                # What the pack reads: the source snapshot, still clean at the cut commit.
                self.hold_custody(runner.source_at_cut)
                # Packed from the cut commit with the staged toolchain, under the cut's build number.
                self.publisher(runner, "controller-pack", [
                    "pack", CONTROLLER, "--checkout", str(runner.source / "crates" / CONTROLLER),
                    "--toolchain", str(Path(runner.record["staged_toolchain"]) / "bin"), "--trust-repo", str(runner.source),
                    "--build", str(build), "--out", str(root / "controller"), "--upload"])
                good["controller_staged"] = now()
                self.save()
            index, pins = self.publish_index(runner, "controller-index", [
                "index", "--pin", f"{CONTROLLER}={build}", "--out", str(root / "controller-index"), "--upload"],
                CONTROLLER, build)
            if pins.get(CONTROLLER, 0) < build:
                raise Refused(f"the index publish ended and atpkg-index-{index} pins {CONTROLLER} "
                              f"{pins.get(CONTROLLER)}, not {build}")
        good["controller_index"] = index
        runner.record["published"][CONTROLLER] = f"atpkg-index-{index}"
        runner.save()
        self.save()

    def after_cut(self, runner: Runner, staged: Path, mint: Path) -> None:
        """Stage and publish the cut, then report on it."""
        github, commit = self.remote(), runner.commit
        build = int(runner.git("build-number", runner.source, "rev-list", "--count", commit))
        self.state["anchor"] = {"commit": commit, "count": build}
        group = ["publish-group", "rustc", "--seal", str(staged), "--trust-repo", str(runner.source)]
        for name in ("trust-ir", "trust-cg", "trust-vc"):
            # The siblings at the commits this source pins.
            group += ["--checkout", f"{name}={runner.source / 'first-party' / name}"]
        group += ["--out", str(runner.state / "group")]
        # The publisher's preflight (key, roster, receipt, floor, siblings) before any act.
        self.note(phase="asking the publisher's preflight")
        self.publisher(runner, "signed-pack-dry-run", [*group, "--dry-run"], self.args.publisher_host)

        self.note(phase="publishing the seed archives")
        seed = ["bash", str(runner.source / "scripts/publish_seed_cut.sh"),
                "--pack", str(staged), "--mint", str(mint), "--aterm", str(self.aterm)]
        runner.call("seed-cut-dry-run", seed, timeout=1800)
        runner.call("seed-archives-and-repin-branch", [*seed, "--publish"], timeout=self.BOUND)

        repin, branch = runner.record["mint"]["repin_commit"], runner.record["mint"]["repin_branch"]
        # origin now holds the re-pin's branch. It goes once a re-pin lands: this one, or a
        # later train's, which supersedes one that did not land.
        self.state.setdefault("branches", []).append({"branch": branch, "commit": repin})
        self.note(phase="landing the re-pin")
        # The helper ends 0 only after it read main back and found the pushed commit in it;
        # the publisher asks main for the re-pin again before it uploads.
        self.land(runner, "re-pin", f"trust-train/repin-{commit[:12]}")
        for left in self.state.pop("branches"):
            try:
                github.delete_branch(left["branch"], left["commit"])
            except Refused as error:
                runner.record.setdefault("train_notes", []).append(f"the branch {left['branch']} was not deleted: {error}")
        self.save()

        self.note(phase="uploading the signed pack")
        self.publisher(runner, "signed-pack-stage-upload", [*group, "--stage-upload"], self.args.publisher_host)
        if build not in github.builds():
            raise Refused(f"the stage-upload exited 0 and {github.slug} has no tag atpkg-trust-{build}")

        # Staged. Nothing after this line takes that back: a refused publication is recorded,
        # and the next tick publishes before it cuts again; a broken custody is recorded, and
        # the build is never published.
        staged_at = now()
        self.state["good"] = {"build": build, "commit": commit, "build_dir": str(runner.state), "staged_at": staged_at}
        self.state["settled"] = self.state["last"]["landed"] or commit
        self.note(build=build, staged_at=staged_at)
        runner.record["staged"] = {"build": build, "tag": f"atpkg-trust-{build}", "repository": github.slug, "at": staged_at}
        runner.save()
        try:
            # The run's end checks, now: a build reaches the fleet only from a cut whose custody
            # held through its upload. A build that fails them is never published, by this tick
            # or a later one; the run makes them again after the report.
            self.note(phase="checking the cut's custody")
            self.hold_custody(runner.custody)
        except CustodyBroken as error:
            self.publish_failed(error)
        else:
            if self.pending():
                self.begin_publication()
                try:
                    self.publish(runner)
                except InterruptedError:
                    raise
                except Exception as error:
                    self.publish_failed(error)
        self.note(phase="running the consumer checks")
        self.report(runner, staged, build, commit)

    def report(self, runner: Runner, staged: Path, build: int, commit: str) -> None:
        """After the upload: the consumer checks and the row counts, written down, never a refusal."""
        could_not_run = None
        try:
            runner.consumers(staged)
        except Refused as error:
            could_not_run = self.portable(str(error))

        def counts(entry: dict) -> dict:
            census = (entry.get("outcome") or {}).get("census")
            if census is None and entry.get("log") and runner.publication_source is not None:
                # A red check has no accepted outcome; its log may still hold its gate banners.
                with contextlib.suppress(OSError, Refused, KeyError, TypeError):
                    census = cleanup_api(runner.publication_source)["parse_gate_census"](
                        Path(entry["log"]).read_text(encoding="utf-8", errors="replace"))
            return (census or {}).get("counts") or {}

        rows = {}
        for name in CONSUMERS:
            entry = runner.record.get("consumers", {}).get(name) or {"status": "not-configured"}
            rows[name] = {"status": entry.get("status"), "commit": entry.get("source_commit"),
                          "exit_code": entry.get("exit_code"), "timed_out": bool(entry.get("timed_out")),
                          "error": self.portable(str(entry["error"])) if entry.get("error") else None,
                          "proved": counts(entry).get("proved"), "failed": counts(entry).get("failed")}
        previous = self.state.get("report")
        findings = report_findings(rows, previous)
        if could_not_run:
            findings.insert(0, f"The consumer checks could not run: {could_not_run}.")
        self.state["report"] = {"build": build, "commit": commit, "consumers": rows, "findings": findings}
        runner.record["report"] = self.state["report"]
        self.note(phase="landing the report")
        block = issue_block(build, commit, now()[:10], findings, previous) if findings else None

        def change(landing: Path) -> str | None:
            path = landing / TRAIN_ISSUE_FILE
            text = path.read_text(encoding="utf-8")
            updated = replace_issue(text, block)
            if updated == text:
                return None
            path.write_text(updated, encoding="utf-8")
            subject = (f"open issues: {TRAIN_ISSUE} for fleet build {build}" if block
                       else f"open issues: fleet build {build} has nothing to report, so {TRAIN_ISSUE} goes")
            return subject + ("\n\nWritten by scripts/daily_toolchain_stage.py train after the stage-upload; "
                              "the build was not held for it.\n")
        try:
            written = self.land(runner, "report", f"trust-train/report-{build}", change)
        except (Refused, OSError) as error:
            self.note(report=f"{len(findings)} finding(s), not landed in {TRAIN_ISSUE_FILE}: {self.portable(str(error))}")
            return
        if written and self.state["last"]["landed"]:
            self.state["settled"] = self.state["last"]["landed"]
        self.note(report=(f"{len(findings)} finding(s) in {TRAIN_ISSUE_FILE} {TRAIN_ISSUE}" if findings
                          else f"nothing found; {TRAIN_ISSUE_FILE} holds no {TRAIN_ISSUE}"))


def train_plist(args: argparse.Namespace) -> dict:
    """The train's launchd agent: one tick at load and every --interval seconds after."""
    if not 300 <= args.interval <= 86400:
        raise Refused("--interval is 300 to 86400 seconds")
    if not args.aterm_repo:
        raise Refused("the train needs --aterm-repo: aterm's publisher signs and uploads the pack")
    elan_home = selected_elan_home(args.elan_home)
    root = args.state_root.resolve()
    argv = [str(Path(sys.executable).resolve(strict=True)), str(Path(__file__).resolve()), "train", "run",
            "--repo", str(args.repo.resolve(strict=True)), "--state-root", str(root),
            "--consumer-jobs", str(args.consumer_jobs), "--publisher-host", args.publisher_host,
            "--index-host", args.index_host]
    for name in ("host", "cargo_home", "ddc_seed", "aterm_repo", "build_slot", "serial_command",
                 "publication_repo", "github_repo"):
        value = getattr(args, name)
        if value:
            argv += ["--" + name.replace("_", "-"), str(value.resolve(strict=True) if isinstance(value, Path) else value)]
    for directory in args.seed_dylib_path:
        argv += ["--seed-dylib-path", str(directory.resolve(strict=True))]
    for declaration in args.source_object_cache:
        argv += ["--source-object-cache", declaration]
    for declaration in args.owned_object_cache:
        argv += ["--owned-object-cache", declaration]
    for declaration in args.dependency_checkout_cache:
        argv += ["--dependency-checkout-cache", declaration]
    if elan_home is not None:
        argv += ["--elan-home", str(elan_home)]
    for name, repository in sorted(consumer_mappings(args.consumer).items()):
        argv += ["--consumer", f"{name}={repository}"]
    # Each tick's runner puts its own python-bin first; the agent keeps the rest of this PATH.
    path = python_search_path(root, os.environ.get("PATH", os.defpath)).split(os.pathsep, 1)[1]
    data = {"Label": TRAIN_LABEL, "ProgramArguments": argv,
            "WorkingDirectory": str(args.repo.resolve(strict=True)),
            "StartInterval": args.interval, "RunAtLoad": True,
            "StandardOutPath": str(root / "launchd.stdout.log"),
            "StandardErrorPath": str(root / "launchd.stderr.log"),
            "EnvironmentVariables": {"PATH": path}}
    if elan_home is not None:
        data["EnvironmentVariables"]["ELAN_HOME"] = str(elan_home)
    return data


def train_agent(args: argparse.Namespace) -> Path:
    return (args.launch_agents or Path.home() / "Library/LaunchAgents").resolve() / f"{TRAIN_LABEL}.plist"


def train_install(args: argparse.Namespace, launchctl: Callable = subprocess.run) -> Path:
    """Write the agent and start it. An agent already there is stopped and replaced."""
    data, agent, domain = train_plist(args), train_agent(args), f"gui/{os.getuid()}"
    args.state_root.resolve().mkdir(parents=True, exist_ok=True)
    agent.parent.mkdir(parents=True, exist_ok=True)
    if agent.exists():
        launchctl(["launchctl", "bootout", f"{domain}/{TRAIN_LABEL}"], capture_output=True, text=True)
        deadline = time.monotonic() + TRAIN_BOOTOUT_WAIT
        while launchctl(["launchctl", "print", f"{domain}/{TRAIN_LABEL}"], capture_output=True, text=True).returncode == 0:
            if time.monotonic() >= deadline:
                raise Refused(f"launchd still runs {TRAIN_LABEL} {TRAIN_BOOTOUT_WAIT} s after its bootout (a tick "
                              f"still stopping); {agent} is left as it was")
            time.sleep(1)
    temporary = agent.with_name(agent.name + f".{os.getpid()}.tmp")
    with temporary.open("xb") as stream:
        plistlib.dump(data, stream, sort_keys=True)
    os.replace(temporary, agent)
    result = launchctl(["launchctl", "bootstrap", domain, str(agent)], capture_output=True, text=True)
    if result.returncode:
        raise Refused(f"launchctl bootstrap exited {result.returncode}: {(result.stderr or '').strip()}; "
                      f"{agent} is written and not loaded")
    return agent


def train_remove(args: argparse.Namespace, launchctl: Callable = subprocess.run) -> Path:
    """Stop the agent and delete its file. The state root, its builds and its landing worktree stay."""
    agent = train_agent(args)
    launchctl(["launchctl", "bootout", f"gui/{os.getuid()}/{TRAIN_LABEL}"], capture_output=True, text=True)
    agent.unlink(missing_ok=True)
    return agent


def train_main(args: argparse.Namespace, terminate: Callable) -> int:
    verb = args.verb or "run"
    if verb == "install":
        agent = train_install(args)
        print(f"train: installed and started {agent}: one tick now and every {args.interval} s; "
              f"`{Path(__file__).name} train status --state-root {args.state_root}` says what it is doing")
        return 0
    if verb == "remove":
        agent = train_remove(args)
        print(f"train: stopped and removed {agent}; {args.state_root} is left as it is")
        return 0
    train = Train(args)
    if verb == "status":
        print(train_status(train.root, train.read_main))
        return 0
    signal.signal(signal.SIGTERM, terminate)
    return train.tick()


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("action", choices=("run", "status", "train"))
    result.add_argument("verb", nargs="?", choices=("run", "status", "install", "remove"),
                        help="train only: run one tick (the default), print its status line, or install or remove its launchd agent")
    result.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[1])
    result.add_argument("--state-root", type=Path,
                        help="required by run and status; a train's defaults to ~/trust-train.noindex")
    result.add_argument("--mode", choices=("prepare", "stage"), default="stage")
    result.add_argument("--host")
    result.add_argument("--cargo-home", type=Path)
    result.add_argument("--elan-home", type=Path,
                        help="existing Lean installation root; defaults to ELAN_HOME when set, captured explicitly in the train's agent")
    result.add_argument("--source-commit", metavar="COMMIT",
                        help="run: build this commit of origin/main (its full id) instead of main's tip, so a cut "
                             "restarted after main moved builds the commit it started on")
    result.add_argument("--ddc-seed", type=Path)
    result.add_argument("--seed-dylib-path", action="append", type=Path, default=[])
    result.add_argument("--aterm-repo", type=Path)
    result.add_argument("--consumer", action="append", default=[], metavar="NAME=REPO",
                        help="run this consumer's committed check; all aterm, ay, ty, clean must pass for consumer_ready")
    result.add_argument("--consumer-jobs", type=int, choices=range(1, 5),
                        default=min(4, max(1, (os.cpu_count() or 1) // 6)),
                        help="parallel consumers, each independently admitted by build-slot (default: one per six CPUs, at most four)")
    result.add_argument("--publication-repo", type=Path,
                        help="publication policy reader source (default: sibling publication checkout)")
    result.add_argument("--build-slot", type=Path)
    result.add_argument("--serial-command", type=Path,
                        help="trust-serial-command that promotion's gates start compilers through: an absolute regular "
                             "executable, not a link (default: the one on PATH, with a link followed)")
    result.add_argument("--source-object-cache", action="append", default=[], metavar="GITLINK=REPOSITORY",
                        help="a local repository Agh reads one first-party gitlink's exact checkout objects from "
                             "(first-party/NAME=/absolute/repository, outside the snapshot); the commit history "
                             "still comes from origin, and Git checks the child out from those objects: no working "
                             "file of the repository is read. Without one the complete sibling is fetched")
    result.add_argument("--owned-object-cache", action="append", default=[], metavar="GITLINK=REPOSITORY",
                        help="an object cache this runner owns: a bare repository (first-party/NAME=/absolute/repository, "
                             "outside the snapshot) that Agh brings up to the gitlink's pin before the snapshot acquires "
                             "it, with HEAD set to that pin, and that is then read as a --source-object-cache is. Only "
                             "objects, one refs/agh ref and HEAD are written there; a refresh that fails is recorded and "
                             "the cache is read as it is")
    result.add_argument("--dependency-checkout-cache", action="append", default=[],
                        metavar="URL#COMMIT=/absolute/repository",
                        help="stage/train: let Agh read exact checkout objects for one locked dependency or "
                             "active dependency Gitlink from this local repository")
    result.add_argument("--publisher-host", choices=("agh-staging", "agh", "gh"), default="agh-staging",
                        help="train: the host aterm's publisher stage-uploads through (default: agh-staging, all a stage-upload needs)")
    result.add_argument("--index-host", choices=("agh", "none"), default="agh",
                        help="train: the host aterm's publisher writes the canary evidence, the controller pack and the "
                             "signed index through after the stage-upload (default: agh, both owners through agh); "
                             "none stops each build at the stage-upload")
    result.add_argument("--github-repo", metavar="OWNER/NAME",
                        help="train: the Trust repository agh reads (default: --repo's origin)")
    result.add_argument("--interval", type=int, default=3600,
                        help="train install: seconds between ticks (default: 3600)")
    result.add_argument("--launch-agents", type=Path,
                        help="train install and remove: the agents directory (default: ~/Library/LaunchAgents)")
    result.add_argument("--dry-run", action="store_true",
                        help="train run: read main and the staged builds, say what this tick would do, and do none of it")
    return result


def main(argv: list[str] | None = None) -> int:
    if sys.version_info < (3, 11):
        print("daily_toolchain_stage.py requires Python >= 3.11", file=sys.stderr)
        return 2
    argv = list(sys.argv[1:] if argv is None else argv)
    def terminate(signum, _frame):
        error = InterruptedError(f"staging interrupted by signal {signum}")
        error.signal = signum
        raise error
    if argv[:1] in (["diagnose"], ["_sdk-diagnostic-worker"]):
        # This owner is lazy: the original full stage/train and four-consumer
        # capture closures do not load a diagnostic producer or change grade.
        import types
        path = Path(__file__).resolve().with_name("sdk_diagnostic.py")
        module = types.ModuleType("trust_sdk_diagnostic")
        module.__file__ = str(path)
        raw = path.read_bytes()
        exec(compile(raw, str(path), "exec"), module.__dict__)
        previous = signal.signal(signal.SIGTERM, terminate)
        try:
            if argv[0] == "_sdk-diagnostic-worker":
                if len(argv) != 2:
                    raise Refused("diagnostic worker requires its original request")
                return module.worker(Path(argv[1]), globals())
            return module.main(argv[1:], globals())
        except (OSError, ValueError, Refused) as error:
            print(f"SDK diagnostic refused: {error}", file=sys.stderr)
            return 1
        finally:
            signal.signal(signal.SIGTERM, previous)
    if argv and argv[0] == "_prewarm-dependencies":
        try:
            if len(argv) < 7:
                raise Refused("dependency prewarm needs source, work, native host, receipt, cache input and config policy owner")
            providers, caches, specs, options, rest = [], {}, [], {}, argv[7:]
            while rest:
                word = rest.pop(0)
                if word == "--object-cache" and rest:
                    url, separator, path = rest.pop(0).partition("=")
                    if not separator or url in caches or not Path(path).is_absolute():
                        raise Refused("dependency prewarm --object-cache needs one URL=ABSOLUTE-REPOSITORY per URL")
                    caches[url] = Path(path)
                elif word == "--ceiling-seconds" and rest and rest[0].isdecimal() and "ceiling_seconds" not in options:
                    options["ceiling_seconds"] = int(rest.pop(0))
                elif word.startswith("--dependency-checkout-cache="):
                    specs.append(word.partition("=")[2])
                elif word == "--dependency-checkout-cache" and rest:
                    specs.append(rest.pop(0))
                elif word == "--ceiling-only" and "ceiling_only" not in options:
                    options["ceiling_only"] = True
                elif word.startswith("-"):
                    raise Refused(f"dependency prewarm option is unsupported: {word}")
                else:
                    providers.append(Path(word))
            prewarm_dependencies(Path(argv[1]), Path(argv[2]), argv[3], Path(argv[4]), providers,
                                 None if argv[5] == "-" else Path(argv[5]), Path(argv[6]),
                                 object_caches=caches, checkout_cache_specs=specs, **options)
            return 0
        except (Exception, KeyboardInterrupt) as error:
            print(f"dependency prewarm refused: {error}", file=sys.stderr)
            return 1
    if argv and argv[0] == "_owned-command":
        try:
            if len(argv) < 6 or argv[4] != "--" or not argv[3].isdecimal() or int(argv[3]) > 86400:
                raise Refused("owned command needs cleanup owner, result file, bounded timeout and argv")
            interrupted = _SignalLatch()
            # Raising inside Popen.wait can interrupt its returncode assignment
            # after waitpid reaped the child. Latch the signal; one waiter first
            # observes exit, then enters publication's bounded cleanup.
            # Event.set takes a non-reentrant lock: direct and forwarded TERM
            # can nest inside it and prevent both cleanup and its receipt.
            def latch(_signum, _frame):
                interrupted.set()
            signal.signal(signal.SIGTERM, latch)
            signal.signal(signal.SIGINT, latch)
            return owned_command(Path(argv[1]), Path(argv[2]), int(argv[3]) or None, argv[5:], interrupted)
        except (OSError, ValueError, KeyError, Refused) as error:
            print(f"owned command refused: {error}", file=sys.stderr)
            return 2
    if argv and argv[0] == "_admitted-bootstrap":
        try:
            return admitted_bootstrap(argv[1:])
        except (OSError, ValueError, Refused) as error:
            print(f"admitted bootstrap refused: {error}", file=sys.stderr)
            return 2
    if argv and argv[0] == "_consumer-policy":
        try:
            if len(argv) != 3:
                raise Refused("consumer policy query needs publication and consumer worktrees")
            print(json.dumps(consumer_policy(Path(argv[1]), Path(argv[2])), sort_keys=True))
            return 0
        except (OSError, ValueError, KeyError, Refused) as error:
            print(f"consumer policy refused: {error}", file=sys.stderr)
            return 2
    options = parser()
    args = options.parse_args(argv)
    if args.dry_run and (args.action != "train" or args.verb not in (None, "run")):
        options.error("--dry-run belongs to train run (or train without a second word)")
    if args.action != "train" and (args.verb or args.state_root is None):
        options.error(f"{args.action} takes --state-root and no second word")
    if args.source_commit is not None and args.action != "run":
        options.error("--source-commit belongs to run: a train cuts the tip of main it read")
    try:
        if args.action == "train":
            args.state_root = args.state_root or Path.home() / "trust-train.noindex"
            return train_main(args, terminate)
        if args.action == "status":
            print(json.dumps(read_json(args.state_root / "latest.json"), indent=2, sort_keys=True))
            return 0
        runner = Runner(args)
        signal.signal(signal.SIGTERM, terminate)
        result = runner.run()
        print(f"{runner.record['status']}: {runner.state / 'latest.json'}")
        return result
    except (OSError, ValueError, Refused) as error:
        print(f"daily staging refused: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
