# Copyright 2026 Andrew Yates
"""Managed native serial transport admission shared by compiler diagnostics and land."""

import hashlib
import json
import os
import re
import shutil
import signal
import stat
import subprocess
import sys
import time
from pathlib import Path
from typing import Dict, Sequence, Tuple

import landing_targo


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    try:
        with open(path, "rb") as source:
            for chunk in iter(lambda: source.read(1 << 20), b""):
                h.update(chunk)
    except OSError as error:
        return f"unreadable:{error.__class__.__name__}"
    return h.hexdigest()


def managed_serial_executor(env: Dict[str, str]) -> Path:
    """Admit the managed native transport owner, never an arbitrary wrapper.

    This is an offline local package admission, like the bootstrap seed owner:
    the identified local atpkg verifier and its recorded tree root remain TCB.
    It is neither fresh signature replay nor evidence that a verifier ran.
    The unchanged positive/negative row still has to execute and decide.
    """
    if "TRUST_LAND_SERIAL_COMMAND" in env:
        raise RuntimeError("caller-selected TRUST_LAND_SERIAL_COMMAND wrappers are not admitted; "
                           "use the managed trust-resource-controller package")
    # Bind the installer's known local activation, not an arbitrary native
    # program which the caller put earlier on PATH. The activation itself and
    # its resolved verifier remain explicitly trusted local inputs.
    activation = Path.home() / ".local/bin/atpkg"
    routed = shutil.which("atpkg", path=env.get("PATH"))
    try:
        known = activation.resolve(strict=True)
        if routed is not None and Path(routed).resolve(strict=True) != known:
            raise RuntimeError("native transport refuses PATH shadowing of the local atpkg activation")
    except OSError as error:
        raise RuntimeError("verify.executes requires the known local atpkg activation") from error
    selected = str(activation)
    passing = landing_targo.resource_fds(env)

    def native_identity(path: Path) -> Tuple[str, int, int, str]:
        actual = path.resolve(strict=True)
        info = actual.stat()
        if not stat.S_ISREG(info.st_mode) or not info.st_mode & 0o111:
            raise RuntimeError("native transport admission requires an executable regular image")
        with actual.open("rb") as source:
            magic = source.read(4)
        if magic not in (b"\x7fELF", b"\xcf\xfa\xed\xfe", b"\xfe\xed\xfa\xcf",
                         b"\xca\xfe\xba\xbe", b"\xbe\xba\xfe\xca",
                         b"\xca\xfe\xba\xbf", b"\xbf\xba\xfe\xca"):
            raise RuntimeError("native transport admission rejects script/no-op wrapper images")
        return str(actual), info.st_dev, info.st_ino, sha256_file(actual)

    verifier_before = native_identity(Path(selected))

    def query(arguments: Sequence[str]) -> str:
        result = subprocess.run([selected, *arguments], env=env, stdin=subprocess.DEVNULL,
                                capture_output=True, text=True, timeout=120, pass_fds=passing)
        if result.returncode or result.stderr.strip():
            raise RuntimeError("native transport package admission failed: "
                               + (result.stdout + result.stderr).strip())
        return result.stdout.strip()

    def lookup() -> Dict[str, object]:
        try:
            value = json.loads(query(["which", "--json", "trust-serial-command"]))
        except (ValueError, TypeError) as error:
            raise RuntimeError("native transport package lookup is malformed") from error
        if (not isinstance(value, dict) or type(value.get("schema")) is not int or value["schema"] != 1
                or value.get("tool") != "trust-serial-command" or value.get("status") != "ready"
                or value.get("managed") is not True or value.get("package") != "trust-resource-controller"
                or type(value.get("build")) is not int or value["build"] <= 0
                or value.get("shim_env") != {}):
            raise RuntimeError("native transport requires the ready managed trust-resource-controller package")
        provenance = value.get("provenance")
        if (not isinstance(provenance, dict) or provenance.get("index_source") != "alabsystems/aterm"
                or type(provenance.get("index_build")) is not int or provenance["index_build"] <= 0
                or not re.fullmatch(r"[0-9a-f]{64}", str(provenance.get("tree_root", "")))):
            raise RuntimeError("native transport package/source identity is unavailable")
        return value

    before = lookup()
    try:
        root = Path(str(before["store_root"]))
        executable = Path(str(before["executable"]))
        if (not root.is_absolute() or root.resolve(strict=True) != root
                or root.name != str(before["build"]) or root.parent.name != "trust-resource-controller"
                or before.get("physical_root") != str(root)
                or before.get("physical_executable") != str(executable)
                or executable != root / "bin/trust-serial-command" or executable.is_symlink()):
            raise RuntimeError("native transport package does not bind its canonical store image")
        image_before = native_identity(executable)
    except (OSError, KeyError) as error:
        raise RuntimeError("native transport package image is unavailable") from error
    expected = f"atpkg: trust-resource-controller build {before['build']} OK (matches signed tree_root)"
    if query(["verify", "trust-resource-controller"]) != expected:
        raise RuntimeError("native transport package verification did not report the exact tree Match")
    if query(["tree-root", str(root)]) != before["provenance"]["tree_root"]:
        raise RuntimeError("native transport measured package tree differs from its recorded root")
    if (lookup() != before or native_identity(executable) != image_before
            or native_identity(Path(selected)) != verifier_before
            or shutil.which("atpkg", path=env.get("PATH")) != routed):
        raise RuntimeError("native transport package, activation, or local verifier changed during admission")
    return executable



def run_custodied_command(command, *, env, timeout=None, cwd=None, capture_output=True, text=True):
    """Run one maintained custody chain through actual terminal on every exit.

    Cancellation only records a request, including during launch and cleanup.
    The native owner forwards TERM and retains its children; never SIGKILL it.
    Poll slices inspect requests/deadlines, not a hard responsiveness guarantee.
    A separate session isolates the native owner from the caller's group QUIT;
    Python translates all four caller cancellations to cooperative owner TERM.
    Genuine inherited descriptors/environment and parent ancestry are retained.
    """
    if not hasattr(signal, "pthread_sigmask"):
        raise RuntimeError("native custody wait requires POSIX signal-mask support")
    cancellation = (signal.SIGINT, signal.SIGTERM, signal.SIGHUP, signal.SIGQUIT)
    if set(cancellation) & signal.pthread_sigmask(signal.SIG_BLOCK, ()):
        raise RuntimeError("native custody wait refuses inherited blocked cancellation signals")
    pending = []

    def cancelled(signum, _frame):
        if not pending:
            pending.append(signum)

    previous = {sig: signal.signal(sig, cancelled)
                for sig in cancellation}
    try:
        if pending:
            raise KeyboardInterrupt(f"seed probe interrupted by signal {pending[0]}")
        process = subprocess.Popen(command, env=env, cwd=cwd, text=text,
                                   stdout=subprocess.PIPE if capture_output else None,
                                   stderr=subprocess.PIPE if capture_output else None,
                                   start_new_session=True,
                                   pass_fds=landing_targo.resource_fds(env))
        try:
            deadline = None if timeout is None else time.monotonic() + timeout
            while True:
                if pending:
                    raise KeyboardInterrupt(f"seed probe interrupted by signal {pending[0]}")
                remaining = None if deadline is None else deadline - time.monotonic()
                if remaining is not None and remaining <= 0:
                    raise subprocess.TimeoutExpired(command, timeout)
                try:
                    output, errors = process.communicate(
                        timeout=.25 if remaining is None else min(.25, remaining))
                    if pending:
                        raise KeyboardInterrupt(f"seed probe interrupted by signal {pending[0]}")
                    break
                except subprocess.TimeoutExpired:
                    continue
        except BaseException:
            try:
                try:
                    process.terminate()
                except ProcessLookupError:
                    pass
                except OSError as error:
                    # The supported CLT entry is Python3.9, before add_note.
                    # Keep the original exception and actual retirement; a
                    # diagnostic must not replace either with AttributeError.
                    try:
                        print(f"TERM unavailable; retaining custody until actual exit: {error}",
                              file=sys.stderr)
                    except (OSError, ValueError, AttributeError):
                        # A broken/closed diagnostic stream is not allowed to
                        # replace the original failure or skip retirement.
                        pass
            finally:
                try:
                    process.communicate()
                finally:
                    # Signal/pipe/decode errors cannot bypass actual retirement.
                    process.wait()
            raise
        result = subprocess.CompletedProcess(command, process.returncode, output, errors)
    finally:
        # Restore atomically with respect to cancellation; an old handler may
        # run only after the native chain has actually retired (or no launch).
        blocked = signal.pthread_sigmask(signal.SIG_BLOCK, previous)
        try:
            for sig, handler in previous.items():
                signal.signal(sig, handler)
        finally:
            signal.pthread_sigmask(signal.SIG_SETMASK, blocked)
    if pending:
        raise KeyboardInterrupt(f"seed probe interrupted by signal {pending[0]}")
    return result
