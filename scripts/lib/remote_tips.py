#!/usr/bin/env python3
# remote_tips.py --- judge a commit against what its remote PUBLISHES, moving no ref.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# WHY THIS EXISTS
# ---------------
# Two pre-push pin lanes ask a question about a remote: `reach`
# (check_submodule_remote_reachability.py: is every pinned sibling commit on a
# branch or a refs/pins/<sha> anchor the remote publishes?) and `cohort`
# (check_ir_cohort.py: is every consumer's trust-ir revision on the
# dependency's main?). Both used to answer it from LOCAL refs ---
# refs/remotes/* and refs/pins/* in the module store --- which are only as
# fresh as that store's last fetch. On 2026-10-14/15 that turned four pushes to
# Trust main from ~/trust-b1 RED while the remote was fine: a pin newer than
# the store's stale origin/main reads exactly like an unpublished or forked
# one. The remedy each time was `git -C first-party/<m> fetch origin` (and
# `+refs/pins/*:refs/pins/*`), which WRITES refs in stores that several
# worktrees share, and after which the same push passed.
#
# So this module answers from the remote itself:
#
#   * one complete authenticated Agh refs collection per GitHub remote URL
#     per run (cached), or Git's advertisement for a literal local remote;
#   * GitHub commit reads and exact ancestor/tip questions use Agh's explicit
#     native commit-only mode. It reuses immutable local objects, SHA-checks
#     missing original commit bytes and owns complete negative ancestry. It
#     writes no worker ref/FETCH_HEAD and never promises trees or checkout
#     completeness. Literal local remotes retain Git's no-ref transport;
#   * a remote that cannot be read, or an object the remote advertised but
#     would not serve, is UNJUDGED: never a pass, and never a finding about the
#     commit either. Callers report it as COULD NOT RUN.
#
# A LOCAL ref is never evidence here. A stale refs/remotes/origin/<branch> the
# forge has since deleted, or a refs/pins/<sha> that was created locally and
# never pushed, used to make a pin "durable"; neither does now.
#
# Shared by both lanes so that they ask the remote the same way. Python 3.9+.

from __future__ import annotations

import hashlib
import errno
import io
import importlib.util
import contextlib
import json
import os
import queue
import re
import signal
import stat
import struct
import sys
import subprocess
import tempfile
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Iterable, Optional, Sequence, TypeVar

MAIN_REF = "refs/heads/main"
HEADS = "refs/heads/"
PINS = "refs/pins/"
INVENTORY_PATTERNS = ("refs/heads/*", "refs/pins/*")

# A hook must not hang on a dead network; a timed-out read is UNJUDGED.
LS_REMOTE_TIMEOUT_S = 90
FETCH_TIMEOUT_S = 600
MAX_OBJECT_READ_BYTES = 32 * 1024 * 1024
STOP_GRACE_S = 5.0
KILL_GRACE_S = 5.0
# Exact ancestry questions sent to one native read. Every (pin, tip) question a
# verdict needs goes in as few reads as this allows, never one read per tip.
# 128 is Agh's own cap (aterm crates/agh/src/git/ancestry.rs, CommitRead::new
# refuses "1-128 queries"); a larger batch would be refused on every run.
ANCESTRY_BATCH = 128
# A remote read that failed for a transient reason (Agh 3 could_not_run, 12
# server, a timeout, a spawn OSError such as EPERM) is asked again after each
# pause while the run's time bound allows; then it is UNJUDGED, never a finding.
# A refusal (6 not_found / "not our ref") and a rate limit (11, whose reset is
# minutes away) are not retried.
TRANSIENT_RETRY_DELAYS_S = (2.0, 8.0)
TRANSIENT_EXITS = frozenset({3, 12, 124, 127})
# _run_text_owned's exit 2 when remote_operation.py itself died: the read never
# finished, so it is transient like a spawn failure (Agh's own exit 2 is usage).
# A child stopped because the operator asked (SIGINT/SIGTERM/SIGHUP/SIGQUIT
# pending in _active_stop) is not that: it is _STOPPED_EXIT, never retried, and
# once a stop is pending no further read is started.
_OWNED_SESSION_LOST = "owned remote session did not finish cleanly"
_STOPPED_EXIT = 130

# Reuse the maintained nonreaping observation/group identity implementation.
# Load this sibling's exact source, independent of caller import paths.
_owner_spec = importlib.util.spec_from_file_location(
    "_remote_tip_process_owner", Path(__file__).with_name("landing_targo.py"))
_process_owner = importlib.util.module_from_spec(_owner_spec)
_owner_spec.loader.exec_module(_process_owner)
_active_stop = None


@contextlib.contextmanager
def _operation_signals():
    """Defer main-thread interruption until all owned worker operations stop."""
    global _active_stop
    if threading.current_thread() is not threading.main_thread() or _active_stop is not None:
        yield
        return
    pending = [None]
    old = {}
    def stop(signum, _frame):
        pending[0] = signum
    _active_stop = pending
    try:
        for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP, signal.SIGQUIT):
            old[sig] = signal.signal(sig, stop)
        yield
    finally:
        _active_stop = None
        for sig, handler in old.items():
            signal.signal(sig, handler)
    if pending[0] is not None:
        raise KeyboardInterrupt(f"remote operation signal {pending[0]}")


def _stop_pending() -> Optional[int]:
    """The signal an operator sent during the current operation, if any."""
    pending = _active_stop
    return None if pending is None else pending[0]


def _stopped(args: Sequence[str], signum: int) -> subprocess.CompletedProcess:
    """An operator-requested stop: not transient, so nothing retries it."""
    return subprocess.CompletedProcess(list(args), _STOPPED_EXIT, "",
                                       f"remote operation stopped by signal {signum}")

# Verdict states.
CONTAINED = "contained"  # a remote ref in scope contains the commit
NOT_CONTAINED = "not-contained"  # every ref in scope was read; none contains it (a FINDING)
ABSENT = "absent"  # no local store holds the commit and the remote will not serve it (a FINDING)
NO_MAIN = "no-main"  # scope "main": the remote publishes no refs/heads/main
UNJUDGED = "unjudged"  # the remote, or objects it named, could not be read (COULD NOT RUN)

# What a server says when it will not serve a sha (as opposed to "I could not
# reach the server"). GitHub and git's own upload-pack say "not our ref".
_REFUSAL_MARKERS = (
    "not our ref",
    "couldn't find remote ref",
    "no such remote ref",
    "unadvertised object",
)

T = TypeVar("T")
R = TypeVar("R")


def parallel_map(fn: Callable[[T], R], items: Sequence[T], workers: int = 16) -> list[R]:
    """``map`` over a thread pool, in order. Each remote read is ~1 s of
    network latency, so nine sequential reads would dominate the hook (and a
    pool narrower than the nine first-party stores costs a second round)."""
    with _operation_signals():
        if len(items) <= 1:
            return [fn(item) for item in items]
        with ThreadPoolExecutor(max_workers=min(workers, len(items))) as pool:
            return list(pool.map(fn, items))


def _env(source: Optional[dict[str, str]] = None, *, isolate_git_config: bool = False,
         git_object_directory: Optional[Path] = None) -> dict[str, str]:
    env = {k: v for k, v in (os.environ if source is None else source).items()
           if not k.startswith("GIT_")}
    # A credential prompt inside a hook waits forever; fail and say so instead.
    env["GIT_TERMINAL_PROMPT"] = "0"
    # Judge the remote's immutable objects and ancestry, not a local rewrite.
    env["GIT_NO_REPLACE_OBJECTS"] = "1"
    env["GIT_GRAFT_FILE"] = os.devnull
    # All network authority belongs to Agh. Git below only reads local objects
    # and literal local remotes, including the private Agh acquisition store.
    env["GIT_ALLOW_PROTOCOL"] = "file"
    env["GIT_NO_LAZY_FETCH"] = "1"
    if isolate_git_config:
        # A private publication repository must not inherit a template,
        # include, hook or URL rewrite from global/system configuration.
        # This fixed internal profile changes no file or ordinary caller.
        env["GIT_CONFIG_NOSYSTEM"] = "1"
        env["GIT_CONFIG_SYSTEM"] = os.devnull
        env["GIT_CONFIG_GLOBAL"] = os.devnull
    if git_object_directory is not None:
        # Only the constructed private-repository intake uses this profile.
        # Apply it after scrubbing caller Git variables; refs/config/index
        # remain in that private repository, not in this output object store.
        env["GIT_OBJECT_DIRECTORY"] = str(git_object_directory)
    return env


def _run(args: Sequence[str], *, timeout: Optional[float] = None, input_text: Optional[str] = None,
         env: Optional[dict[str, str]] = None, cwd: Optional[Path] = None,
         binary: bool = False, isolate_git_config: bool = False,
         git_object_directory: Optional[Path] = None, input_file=None) -> subprocess.CompletedProcess:
    try:
        if isolate_git_config and (not args or Path(args[0]).name != "git"):
            return subprocess.CompletedProcess(list(args), 2, "", "config isolation requires a constructed local Git operation")
        if git_object_directory is not None and (binary or not isolate_git_config or not git_object_directory.is_absolute()):
            return subprocess.CompletedProcess(list(args), 2, "", "object intake requires an isolated local Git operation and absolute object directory")
        if input_file is not None and (input_text is not None or binary or not isolate_git_config
                                       or git_object_directory is None
                                       or list(args[-2:]) != ["index-pack", "--stdin"]
                                       or not stat.S_ISREG(os.fstat(input_file.fileno()).st_mode)):
            return subprocess.CompletedProcess(list(args), 2, "", "raw pack input requires a regular descriptor for isolated object intake")
        if binary:
            return _run_binary(args, timeout=timeout, input_text=input_text, env=env, cwd=cwd,
                               isolate_git_config=isolate_git_config)
        return _run_text_owned(args, timeout=timeout, input_text=input_text, env=env, cwd=cwd,
                               isolate_git_config=isolate_git_config, git_object_directory=git_object_directory,
                               input_file=input_file)
    except subprocess.TimeoutExpired:
        return subprocess.CompletedProcess(list(args), 124, "", f"timed out after {timeout:.0f}s")
    except OSError as error:
        return subprocess.CompletedProcess(list(args), 127, "", str(error))
    except RuntimeError as error:
        return subprocess.CompletedProcess(list(args), 2, "", str(error))


def _observe_until(child: subprocess.Popen, deadline: float, *, cancellable: bool = True) -> bool:
    """Observe exit without letting a wait/poll recycle the operation group."""
    while True:
        if cancellable and _active_stop is not None and _active_stop[0] is not None:
            return False
        if _process_owner.wait_child_exit(child.pid, nohang=True):
            return True
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            return False
        time.sleep(min(0.02, remaining))


def _finish_operation(child: subprocess.Popen) -> int:
    """Give the native owner its cooperative stop before bounded escalation.

    The unreaped leader pins our session/group identity through the final
    signal. Agh owns/reaps any separate child groups via its native collectors;
    this caller never guesses or signals groups discovered from a global list.
    """
    _process_owner.signal_owned_group(child.pid, signal.SIGTERM)
    _observe_until(child, time.monotonic() + STOP_GRACE_S + KILL_GRACE_S + 3, cancellable=False)
    _process_owner.signal_owned_group(child.pid, signal.SIGKILL)
    try:
        return child.wait(timeout=KILL_GRACE_S)
    finally:
        if child.stdin is not None:
            child.stdin.close()


def _run_text_owned(args: Sequence[str], *, timeout: Optional[float], input_text: Optional[str],
                    env: Optional[dict[str, str]], cwd: Optional[Path],
                    isolate_git_config: bool = False,
                    git_object_directory: Optional[Path] = None, input_file=None) -> subprocess.CompletedProcess:
    """Retain the exact operation until stop/drain/reap on every unwind.

    Temporary streams avoid descendant-held pipe EOF deadlocks. Successful
    status is read only after group cleanup; a timeout never becomes refusal
    or containment evidence. No source-store ref/config or authority changes.
    """
    if (os.name != "posix" or not _process_owner.exit_observation_available()
            or signal.getsignal(signal.SIGCHLD) != signal.SIG_DFL):
        return subprocess.CompletedProcess(list(args), 2, "", "owned remote operation is unsupported on this host")
    signum = _stop_pending()
    if signum is not None:
        return _stopped(args, signum)  # a stop is pending: start nothing
    duration = FETCH_TIMEOUT_S if timeout is None else max(0.0, timeout)
    if args and Path(args[0]).name == "git":
        # These constructed Git calls have file-only transport. Keep their
        # simple operation group; Agh's separate native Git groups need the
        # full session owner below.
        return _run_local_git(args, duration, input_text, env, cwd, isolate_git_config=isolate_git_config,
                              git_object_directory=git_object_directory, input_file=input_file)
    deadline = time.monotonic() + duration + STOP_GRACE_S + KILL_GRACE_S + 3
    resources = _process_owner.resource_fds(_env(env))
    with _operation_signals(), tempfile.TemporaryFile() as request, \
            tempfile.TemporaryFile() as output, tempfile.TemporaryFile() as errors, contextlib.ExitStack() as descriptors:
        request.write((input_text or "").encode("utf-8", "surrogateescape"))
        request.seek(0)
        child = None
        def pipe_streams():
            read, write = os.pipe()
            reader = descriptors.enter_context(os.fdopen(read, "rb", buffering=0))
            writer = descriptors.enter_context(os.fdopen(write, "wb", buffering=0))
            return reader, writer
        custody, lease = pipe_streams()
        result, result_writer = pipe_streams()
        outer_expired = False
        try:
            command = [sys.executable, str(Path(__file__).with_name("remote_operation.py")),
                       str(custody.fileno()), str(result_writer.fileno()), str(duration), str(STOP_GRACE_S), str(KILL_GRACE_S),
                       "--", *args]
            child = subprocess.Popen(command, stdin=request, stdout=output, stderr=errors,
                                     env=_env(env), cwd=cwd, start_new_session=True,
                                     pass_fds=(*resources, custody.fileno(), result_writer.fileno()))
            custody.close()
            result_writer.close()
            outer_expired = not _observe_until(child, deadline)
        finally:
            lease.close()  # EOF also cancels an operation if its caller dies.
            if child is not None:
                status = _finish_operation(child)
            custody.close()
            result_writer.close()
        received = result.read(6)
        signum = _stop_pending()
        if signum is not None and (outer_expired or status or len(received) != 5):
            # The operator's stop ended it; only a child that died on its
            # own is a lost session (retried as transient).
            return _stopped(args, signum)
        if status or len(received) != 5:
            return subprocess.CompletedProcess(list(args), 2, "", _OWNED_SESSION_LOST)
        native_status, expired = struct.unpack("!i?", received)
        if expired or outer_expired:
            return subprocess.CompletedProcess(list(args), 124, "", f"timed out after {duration:.0f}s")
        output.seek(0)
        errors.seek(0)
        def text(stream):
            return stream.read().decode("utf-8", "surrogateescape").replace("\r\n", "\n").replace("\r", "\n")
        return subprocess.CompletedProcess(list(args), native_status, text(output), text(errors))


def _run_local_git(args, duration, input_text, env, cwd, *, isolate_git_config=False,
                   git_object_directory=None, input_file=None):
    resources = _process_owner.resource_fds(_env(env))
    with _operation_signals(), tempfile.TemporaryFile() as request, \
            tempfile.TemporaryFile() as output, tempfile.TemporaryFile() as errors:
        if input_file is None:
            request.write((input_text or "").encode("utf-8", "surrogateescape"))
            request.seek(0)
        else:
            # The constructed pack file goes straight to Git's stdin. No
            # Python text decoding, newline conversion or payload buffering.
            request = input_file
        child = None
        try:
            child = subprocess.Popen(list(args), stdin=request, stdout=output, stderr=errors,
                                     env=_env(env, isolate_git_config=isolate_git_config,
                                              git_object_directory=git_object_directory), cwd=cwd,
                                     start_new_session=True, pass_fds=resources)
            expired = not _observe_until(child, time.monotonic() + duration)
        finally:
            if child is not None:
                status = _finish_operation(child)
        if expired:
            signum = _stop_pending()
            if signum is not None:
                return _stopped(args, signum)
            return subprocess.CompletedProcess(list(args), 124, "", f"timed out after {duration:.0f}s")
        output.seek(0)
        errors.seek(0)
        def text(stream):
            return stream.read().decode("utf-8", "surrogateescape").replace("\r\n", "\n").replace("\r", "\n")
        return subprocess.CompletedProcess(list(args), status, text(output), text(errors))


def _verified_original_rows(stream, shas, *, expected=None, retain_body=True,
                            byte_budget=None, object_limit=None):
    """The shared exact cat-file framing/hash contract, with bounded body reads.

    Metadata callers retain their already bounded payloads. Snapshot reuse
    hashes each body in chunks and retains only its verified object identity.
    """
    for oid in shas:
        header = stream.readline(256)
        if not header.endswith(b"\n"):
            raise ValueError("original object header is truncated or oversized")
        fields = header[:-1].split()
        if fields == [oid.encode(), b"missing"]:
            yield oid, None, None
            continue
        if (len(fields) != 3 or fields[0] != oid.encode() or not fields[2].isdigit()
                or fields[1] not in (b"commit", b"tag", b"tree", b"blob")
                or (expected is not None and fields[1] != expected[oid][0].encode())):
            raise ValueError("original object identity/type/size differs")
        size = int(fields[2])
        if expected is not None and size != expected[oid][1]:
            raise ValueError("original object size differs from native source")
        if object_limit is not None and size > object_limit:
            raise ValueError("original object exceeds source object budget")
        if byte_budget is not None:
            if size > byte_budget:
                raise ValueError("original objects exceed source byte budget")
            byte_budget -= size
        digest = hashlib.sha1(fields[1] + b" " + str(size).encode() + b"\0")
        body = bytearray() if retain_body else None
        remaining = size
        while remaining:
            chunk = stream.read(min(65536, remaining))
            if not chunk:
                raise ValueError("original object body is truncated")
            remaining -= len(chunk)
            digest.update(chunk)
            if body is not None:
                body.extend(chunk)
        if stream.read(1) != b"\n" or digest.hexdigest() != oid:
            raise ValueError("original object framing/hash differs")
        yield oid, fields[1], bytes(body) if body is not None else None
    if stream.read(1):
        raise ValueError("original object stream has trailing bytes")


def _verified_present_objects(root, selected, *, env, timeout):
    """Read/hash every existing selected object before deciding what to import.

    Original lookup uses the same neutral, local-only Git profile as the
    surrounding intake. A missing response is usable only after a clean Git
    exit with no corruption diagnostic. The owned reader is drained/reaped on
    every path; no object body is buffered as a Python payload.
    """
    args = ["git", "-C", str(root), "cat-file", "--batch"]
    deadline = time.monotonic() + timeout
    byte_budget = sum(size for _kind, size in selected.values())
    object_limit = max((size for _kind, size in selected.values()), default=0)
    resources = _process_owner.resource_fds(_env(env))
    with _operation_signals(), tempfile.TemporaryFile() as request, tempfile.TemporaryFile() as errors:
        for oid in selected:
            request.write((oid + "\n").encode())
        request.seek(0)
        child = None
        reader = None
        reader_started = False
        finished = False
        result = queue.Queue(maxsize=1)
        try:
            child = subprocess.Popen(args, stdin=request, stdout=subprocess.PIPE, stderr=errors,
                                     env=_env(env, isolate_git_config=True), cwd=root,
                                     start_new_session=True, pass_fds=resources)
            def read():
                try:
                    held = {oid for oid, kind, _ in _verified_original_rows(
                        child.stdout, selected, expected=selected, retain_body=False,
                        byte_budget=byte_budget, object_limit=object_limit) if kind is not None}
                    result.put((held, None))
                except (OSError, ValueError) as error:
                    result.put((None, str(error)))
            reader = threading.Thread(target=read)
            reader.start()
            reader_started = True
            while True:
                if _stop_pending() is not None:
                    return _stopped(args, _stop_pending()), None
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    return subprocess.CompletedProcess(args, 124, "", "original object verification deadline exhausted"), None
                try:
                    held, problem = result.get(timeout=min(0.02, remaining))
                    break
                except queue.Empty:
                    continue
            if problem:
                return subprocess.CompletedProcess(args, 2, "", problem), None
            if not _observe_until(child, deadline):
                return subprocess.CompletedProcess(args, 124, "", "original object verification deadline exhausted"), None
            status = _finish_operation(child)
            finished = True
            errors.seek(0)
            diagnostic = errors.read(65536).decode("utf-8", "surrogateescape")
            if status or diagnostic:
                return subprocess.CompletedProcess(args, status or 2, "", diagnostic), None
            return subprocess.CompletedProcess(args, 0, "", ""), held
        except (OSError, RuntimeError) as error:
            return subprocess.CompletedProcess(args, 2, "", str(error)), None
        finally:
            if child is not None and not finished:
                _finish_operation(child)
            if reader_started:
                reader.join()
            if child is not None:
                child.stdout.close()


def _run_binary(args: Sequence[str], *, timeout: Optional[float], input_text: Optional[str],
                env: Optional[dict[str, str]], cwd: Optional[Path],
                isolate_git_config: bool = False) -> subprocess.CompletedProcess:
    """Bound the exact cat-file byte stream, owning/reaping its child on errors.

    A request file avoids stdin/stdout pipe deadlocks. A bounded reader works
    on Windows pipes as well as Unix; timeout/oversize always kills and reaps
    this local object-reader process before returning an unread result.
    """
    deadline = time.monotonic() + (FETCH_TIMEOUT_S if timeout is None else timeout)
    with tempfile.TemporaryFile() as request, tempfile.TemporaryFile() as errors:
        request.write((input_text or "").encode())
        request.seek(0)
        child = subprocess.Popen(list(args), stdin=request, stdout=subprocess.PIPE, stderr=errors,
                                 env=_env(env, isolate_git_config=isolate_git_config), cwd=cwd)
        reader = None
        reader_started = False
        try:
            result = queue.Queue(maxsize=1)
            def read():
                chunks = []
                total = 0
                try:
                    while True:
                        chunk = child.stdout.read1(min(65536, MAX_OBJECT_READ_BYTES + 1 - total))
                        if not chunk:
                            result.put((b"".join(chunks), ""))
                            return
                        chunks.append(chunk)
                        total += len(chunk)
                        if total > MAX_OBJECT_READ_BYTES:
                            result.put((b"", "object read exceeds metadata byte budget"))
                            return
                except OSError as error:
                    result.put((b"", str(error)))
            reader = threading.Thread(target=read)
            reader.start()
            reader_started = True
            try:
                output, problem = result.get(timeout=max(0.001, deadline - time.monotonic()))
                if problem:
                    return subprocess.CompletedProcess(list(args), 2, b"", problem.encode())
                status = child.wait(timeout=max(0.001, deadline - time.monotonic()))
            except (queue.Empty, subprocess.TimeoutExpired):
                return subprocess.CompletedProcess(list(args), 124, b"", b"object read deadline exhausted")
            errors.seek(0)
            return subprocess.CompletedProcess(list(args), status, output, errors.read(65536))
        except (OSError, RuntimeError) as error:
            return subprocess.CompletedProcess(list(args), 2, b"", str(error).encode())
        finally:
            if child.poll() is None:
                child.kill()
            child.wait()
            if reader_started:
                reader.join()
            child.stdout.close()


def _message(done: subprocess.CompletedProcess[str]) -> str:
    """The line that says what went wrong: git's own `fatal:`/`error:` line
    when there is one (ssh's closing "and the repository exists." is not)."""
    text = (done.stderr or "").strip() or (done.stdout or "").strip()
    lines = [line.strip() for line in text.splitlines() if line.strip()]
    for line in lines:
        if line.startswith(("fatal:", "error:")):
            return line
    return lines[-1] if lines else f"exit {done.returncode}"


def github_repository(url: str) -> Optional[str]:
    """A credential-free literal GitHub repository, or a literal local URL.

    Do not let a lookalike host, URL rewrite, query, userinfo or shell syntax
    choose transport authority. Other network transports are not a fallback.
    """
    match = re.fullmatch(
        r"(?:https://github[.]com/|git@github[.]com:|ssh://git@github[.]com/)"
        r"([A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+?)(?:[.]git)?/?", url)
    if match:
        repository = match[1]
        if all(part not in {".", ".."} and not part.startswith("-")
               for part in repository.split("/")):
            return repository
    if (url.startswith(("/", "./", "../", "file:///"))
            or (url and not re.search(r"[:\\\s]", url))):
        return None
    raise ValueError("remote must be a literal local path or credential-free GitHub URL")


def _agh(repository: str, args: Sequence[str], *, timeout: float,
         env: Optional[dict[str, str]] = None,
         cwd: Optional[Path] = None) -> subprocess.CompletedProcess[str]:
    """Use the owner's actual routed profile, never an anonymous read chain.

    Agh owns credentials. The profile name is routing metadata, not a token.
    The subprocess deadline includes routing and the operation together.
    """
    started = time.monotonic()
    route = _run(["agh", "whoami", "--for", repository, "--op", "read"], timeout=timeout, env=env, cwd=cwd)
    if route.returncode:
        return route
    try:
        profile = json.loads(route.stdout)["decision"]["send"]["profile"]
        if not isinstance(profile, str) or not re.fullmatch(r"[A-Za-z0-9_.-]+", profile):
            raise ValueError("no authenticated profile")
    except (ValueError, TypeError, KeyError):
        return subprocess.CompletedProcess(args, 4, "", "Agh has no authenticated owner-routed read profile")
    remaining = timeout - (time.monotonic() - started)
    if remaining <= 0:
        return subprocess.CompletedProcess(args, 124, "", "Agh routing exhausted the remote-read deadline")
    # Native repository reads require owner-routed credentials unless --anonymous
    # is explicitly typed, and deliberately does not admit --as. API reads
    # additionally bind the selected profile, disabling the anonymous chain.
    selection = [] if tuple(args[:2]) in (("repo", "fetch"), ("repo", "commit-ancestry"),
                                         ("repo", "refs")) else ["--as", profile]
    return _run(["agh", *args, *selection, "--no-anonymous-api"], timeout=remaining, env=env, cwd=cwd)


def _unique_json_fields(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate observation field")
        result[key] = value
    return result


# The native ancestry reply contract this module accepts (``_native_commit_read``
# refuses any other schema or scope). ``AncestryMemory.FORMAT`` names it, so a
# change in Agh's ancestry contract retires every answer remembered under the
# old one (docs/DECISION_QUEUE.md REACH-MEMO-1).
NATIVE_ANCESTRY_SCHEMA = 1
NATIVE_ANCESTRY_SCOPE = "commit-parent-ancestry-only-v1"


def _native_commit_read(repository: str, git_dir: Path, commits: Sequence[str],
                        queries: Sequence[tuple[str, str]] = (), *, timeout: float,
                        env: Optional[dict[str, str]] = None,
                        materialize: bool = False) -> subprocess.CompletedProcess[str]:
    """One exact guarded commit-only read, with its caller's remaining budget.

    Native Agh validates original commit bytes, may acquire genuinely cold
    commits through its normal authenticated service, and writes no caller ref.
    The reply must bind the complete exact request; it is not a type label.
    """
    values = list(commits) + [sha for query in queries for sha in query]
    if any(not re.fullmatch(r"[0-9a-f]{40}", sha) or sha == "0" * 40 for sha in values):
        return subprocess.CompletedProcess([], 2, "", "native commit reads require exact immutable ids")
    request = {"commits": list(commits),
               "queries": [{"ancestor": a, "descendant": d} for a, d in queries]}
    deadline = time.monotonic() + timeout
    try:
        with _commit_transport(git_dir, deadline=deadline, env=env) as (directory, view, check_current, install), \
                _canonical_commit_lending(repository, view, deadline=deadline, env=env) as canonical_current:
            requested = directory / ".ubd" / "commits.json"
            requested.write_text(json.dumps(request))
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                return subprocess.CompletedProcess([], 124, "", "native commit read deadline exhausted")
            done = _agh(repository, ["repo", "commit-ancestry", repository, str(view),
                                     "--input", str(requested)], timeout=remaining, env=env, cwd=directory)
            check_current()
            canonical_current()
            if done.returncode:
                if done.returncode == 6:
                    return subprocess.CompletedProcess(done.args, 6, "", "not our ref: " + _message(done))
                return done
            reply = json.loads(done.stdout, object_pairs_hook=_unique_json_fields)
            if (not isinstance(reply, dict) or type(reply.get("schema")) is not int
                    or reply.get("schema") != NATIVE_ANCESTRY_SCHEMA or reply.get("scope") != NATIVE_ANCESTRY_SCOPE
                    or reply.get("commits") != request["commits"]
                    or reply.get("refs_written") is not False or reply.get("checkout_complete") is not False):
                raise ValueError("native commit observation has a different scope or binding")
            for field in ("acquired_commits", "api_body_bytes"):
                if type(reply.get(field)) is not int or reply[field] < 0:
                    raise ValueError("native commit observation has invalid acquisition accounting")
            answers = reply.get("queries")
            if not isinstance(answers, list) or len(answers) != len(request["queries"]):
                raise ValueError("native ancestry observation has a different population")
            for expected, actual in zip(request["queries"], answers):
                if (not isinstance(actual, dict) or set(actual) != {"ancestor", "descendant", "contained"}
                        or actual["ancestor"] != expected["ancestor"]
                        or actual["descendant"] != expected["descendant"]
                        or not isinstance(actual["contained"], bool)):
                    raise ValueError("native ancestry observation has a different exact query")
            # Keep original DATA acquired by this successful native operation,
            # including intermediate parents. Every future relationship still
            # needs its own native query against a fresh remote advertisement.
            install(commits if materialize else ())
            check_current()
            return done
    except _PublicationSourceFailure as error:
        return error.result
    except (OSError, TimeoutError, ValueError, TypeError, AttributeError) as error:
        return subprocess.CompletedProcess([], 2, "", f"native commit read unavailable: {error}")


@contextlib.contextmanager
def _canonical_commit_source(repository: str, *, deadline: float, env=None):
    """Hold optional read-only originals, never canonical refs or checkout state.

    Only the maintained sibling names select a home path. An arbitrary remote
    name cannot cause discovery in another application or personal directory.
    Missing or unsuitable hints fall through to the normal guarded native read.
    """
    if os.name != "posix" or any(not hasattr(os, flag) for flag in
                                    ("O_DIRECTORY", "O_NOFOLLOW", "O_CLOEXEC")):
        yield None
        return
    name = repository.split("/")[-1]
    if name not in {"trust", "ay", "clean", "trust-cg", "trust-ir", "trust-mc",
                    "trust-vc", "trust-wp", "ty", "ny"}:
        yield None
        return
    root = Path.home() / name
    def remaining():
        value = deadline - time.monotonic()
        if value <= 0:
            raise TimeoutError("remote ref type deadline exhausted")
        return value
    def git(*args):
        done = _run(["git", "-C", str(root), *args], timeout=remaining(), env=env,
                    cwd=root)
        if done.returncode == 124:
            raise TimeoutError("canonical commit witness exhausted the ref deadline")
        if done.returncode:
            raise ValueError("canonical source hint is unavailable")
        return done.stdout.strip()
    descriptors = contextlib.ExitStack()
    try:
        flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_CLOEXEC
        def hold(path):
            descriptor = os.open(path, flags)
            descriptors.callback(os.close, descriptor)
            return descriptor, os.fstat(descriptor)
        root_fd, root_info = hold(root)
        if Path(git("rev-parse", "--show-toplevel")).resolve(strict=True) != root.resolve(strict=True):
            raise ValueError("canonical source root differs")
        gd = Path(git("rev-parse", "--absolute-git-dir"))
        if not gd.is_absolute():
            raise ValueError("canonical source Git directory is not absolute")
        gd_fd, gd_info = hold(gd)
        def check():
            for path, fd, original in ((root, root_fd, root_info), (gd, gd_fd, gd_info)):
                current, named = os.fstat(fd), path.lstat()
                if (not stat.S_ISDIR(named.st_mode)
                        or (current.st_dev, current.st_ino) != (original.st_dev, original.st_ino)
                        or (named.st_dev, named.st_ino) != (current.st_dev, current.st_ino)):
                    raise ValueError("canonical source directory changed")
            origins = git("config", "--get-all", "remote.origin.url").splitlines()
            if (len(origins) != 1 or github_repository(origins[0]) != repository
                    or git("rev-parse", "--absolute-git-dir") != str(gd)):
                raise ValueError("canonical source does not match the authenticated repository")
        check()
    except TimeoutError:
        descriptors.close()
        raise
    except (OSError, ValueError):
        descriptors.close()
        # Missing or unsuitable optional DATA cannot suppress native refusal.
        yield None
        return
    except BaseException:
        descriptors.close()
        raise
    try:
        yield root, gd, check
        check()
        remaining()
    finally:
        descriptors.close()


def _canonical_commit_witness(repository: str, commits: Sequence[str], *,
                              deadline: float, env=None) -> set[str]:
    try:
        with _canonical_commit_source(repository, deadline=deadline, env=env) as source:
            if source is None:
                return set()
            root, gd, check = source
            held = RemoteTips.present(gd, commits, timeout=deadline - time.monotonic(), env=env, cwd=root)
            check()
            return held
    except TimeoutError:
        raise
    except (OSError, ValueError):
        return set()


@contextlib.contextmanager
def _canonical_commit_lending(repository: str, view: Path, *, deadline: float, env=None):
    """Lend held original DATA to the SAME native raw-parent operation.

    Neither canonical refs/configuration/shallow state nor a saved verdict is
    copied. Native Agh remains the sole ancestry parser and judge; cold data
    still uses its ordinary authenticated policy and preserves every refusal.
    """
    with _canonical_commit_source(repository, deadline=deadline, env=env) as source:
        if source is None:
            yield lambda: None
            return
        _root, gd, source_current = source
        with _commit_transport(gd, deadline=deadline, env=env) as (_directory, borrowed, objects_current, _install):
            def check():
                source_current()
                objects_current()
            check()
            # Both private views and the original ODB descriptors stay live
            # until native completion, reply validation and any commit intake.
            alternates = view / "objects/info/alternates"
            alternates.write_text(alternates.read_text() + str(borrowed / "objects") + "\n")
            yield check
            check()


def remote_refs(url: str, *, git_dir: Optional[Path] = None,
                env: Optional[dict[str, str]] = None,
                cwd: Optional[Path] = None,
                timeout: float = LS_REMOTE_TIMEOUT_S,
                witness: Optional[Iterable[str]] = None) -> subprocess.CompletedProcess[str]:
    """Fresh complete authoritative heads/pins inventory, in Git TSV form.

    Native Agh reads the complete authenticated Git advertisement without
    REST. Its wire format omits object types: every durable advertised OID
    must also name an original, hash-verified commit in the caller's actual
    object store or a checked read-only same-repository canonical store. Cold
    objects use native original-commit reads against this SAME advertisement;
    their normal authenticated API budget/refusals remain in force. Local ref
    names never substitute for a fresh advertised ref.

    ``witness`` (GitHub only) names the refs a caller's predicate reads, such
    as the IR cohort's ``refs/heads/main``: every advertised entry is still
    validated, but only those refs' OIDs are witnessed as commits, and only
    they are returned, so no unwitnessed OID leaves as a durable ref.
    ``None``, the default, witnesses and returns every head and pin
    (docs/DECISION_QUEUE.md IR-COHORT-MAIN-WITNESS-1). A bare ``str`` is
    refused: it would name its characters, witness nothing and read as an
    advertisement without main.

    A GitHub result carries ``commit_witness_reads``, what each successful
    native witness read reported, also when a later step failed; a success
    also carries ``witnessed_tips``, the OIDs witnessed as commits in the
    store, the canonical store or by a native read.
    """
    if isinstance(witness, str):
        raise TypeError("remote_refs witness names refs: pass a collection, not a str")
    try:
        repository = github_repository(url)
    except ValueError as error:
        return subprocess.CompletedProcess([], 2, "", str(error))
    if repository is None:
        return _run(["git", *(["--git-dir", str(git_dir)] if git_dir else []),
                     "ls-remote", "--refs", "--", url, *INVENTORY_PATTERNS], timeout=timeout, env=env, cwd=cwd)
    deadline = time.monotonic() + timeout
    # The advertisement selects only the literal remote, not a local clone.
    # A caller's hooks/includes must neither become transport inputs nor make
    # this read adopt a configuration that native Agh correctly refuses.
    try:
        with _source_transport("trust-ref-read-") as (directory, _data, check_private):
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                return subprocess.CompletedProcess([], 124, "", "remote ref inventory deadline exhausted")
            done = _agh(repository, ["repo", "refs", repository], timeout=remaining,
                        env=env, cwd=directory)
            check_private()
    except _PublicationSourceFailure as error:
        return error.result
    except OSError as error:
        return subprocess.CompletedProcess([], 2, "", f"private remote ref read unavailable: {error}")
    if done.returncode:
        return done
    observations = []

    def carrying(result):
        # Native reads that succeeded before a later failure still acquired.
        result.commit_witness_reads = observations
        return result

    objects = []
    try:
        entries = json.loads(done.stdout, object_pairs_hook=_unique_json_fields)
        if not isinstance(entries, list):
            raise ValueError("refs collection is not a list")
        # Agh reports an annotated tag's peeled object in its row's `peeled`
        # field, where `git ls-remote` reports a separate `<ref>^{}` row. Read
        # it as those two rows, so every check below judges them as before.
        rows = []
        for entry in entries:
            if isinstance(entry, dict) and set(entry) == {"ref", "oid", "peeled"}:
                if not isinstance(entry["ref"], str) or entry["ref"].endswith("^{}"):
                    raise ValueError("invalid peeled native ref entry")
                rows += [{"ref": entry["ref"], "oid": entry["oid"]},
                         {"ref": entry["ref"] + "^{}", "oid": entry["peeled"]}]
            else:
                rows.append(entry)
        entries = rows
        refs = {}
        advertised = {}
        seen = set()
        head = None
        named = None if witness is None else frozenset(witness)
        for entry in entries:
            if not isinstance(entry, dict) or set(entry) != {"ref", "oid"}:
                raise ValueError("invalid native ref entry")
            name = entry["ref"]
            if name == "HEAD":
                # Agh lists the HEAD pseudoref with the refs; `git ls-remote
                # --refs`, the non-GitHub path above, omits it. Only one
                # well-formed row naming an advertised branch tip (checked
                # after the loop) is dropped; it is never advertised.
                oid = entry["oid"]
                if (head is not None or not isinstance(oid, str)
                        or not re.fullmatch(r"[0-9a-f]{40}", oid) or oid == "0" * 40):
                    raise ValueError("ambiguous or invalid remote HEAD")
                head = oid
                continue
            if not isinstance(name, str) or not name.startswith("refs/"):
                raise ValueError("invalid remote ref")
            oid = entry["oid"]
            if (name in seen or not isinstance(oid, str)
                    or not re.fullmatch(r"[0-9a-f]{40}", oid) or oid == "0" * 40):
                raise ValueError("ambiguous or invalid remote ref")
            seen.add(name)
            full = name[:-3] if name.endswith("^{}") else name
            if (full.endswith(("/", ".")) or any(c.isspace() or ord(c) < 32 or ord(c) == 127 for c in full)
                    or any(c in full for c in ("..", "//", "@{", "~", "^", ":", "?", "*", "[", "\\"))
                    or any(p.startswith(".") or p.endswith(".lock") for p in full.split("/"))):
                raise ValueError("invalid durable remote ref")
            advertised[name] = oid
            if not name.startswith((HEADS, PINS)):
                continue
            if full != name:
                raise ValueError("peeled objects cannot supply durable remote refs")
            if named is None or name in named:
                refs[name] = oid
        if head is not None and head not in {oid for name, oid in advertised.items() if name.startswith(HEADS)}:
            raise ValueError("remote HEAD names no advertised branch tip")
        if refs:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                return subprocess.CompletedProcess(done.args, 124, "", "remote ref inventory deadline exhausted")
            if git_dir is None:
                if cwd is None:
                    raise ValueError("durable remote ref types require the caller's actual Git store")
                found = _run(["git", "-C", str(cwd), "rev-parse", "--absolute-git-dir"],
                             timeout=remaining, env=env, cwd=cwd)
                if found.returncode:
                    return carrying(found)
                git_dir = Path(found.stdout.strip())
                if not git_dir.is_absolute():
                    raise ValueError("caller Git store is not absolute")
            # The authoritative population is captured once above. Local
            # objects only witness original types, never ref freshness.
            objects = list(dict.fromkeys(refs.values()))
            for start in range(0, len(objects), ANCESTRY_BATCH):
                batch = objects[start:start + ANCESTRY_BATCH]
                def remaining():
                    value = deadline - time.monotonic()
                    if value <= 0:
                        raise TimeoutError("remote ref type deadline exhausted")
                    return value
                held = RemoteTips.present(git_dir, batch, timeout=remaining(), env=env, cwd=cwd)
                missing = [oid for oid in batch if oid not in held]
                if missing:
                    held |= _canonical_commit_witness(repository, missing, deadline=deadline, env=env)
                    missing = [oid for oid in missing if oid not in held]
                if missing:
                    # Agh's native reader hashes and type-checks the original
                    # bodies in its private view; it returns no raw bodies and
                    # does not promise to install them in the caller store.
                    native = _native_commit_read(repository, git_dir, missing,
                                                 timeout=remaining(), env=env)
                    if native.returncode:
                        return carrying(native)
                    reply = json.loads(native.stdout)
                    observations.append({key: reply[key] for key in
                                         ("commits", "acquired_commits", "api_body_bytes")})
                remaining()
    except TimeoutError as error:
        return carrying(subprocess.CompletedProcess(done.args, 124, "", str(error)))
    except (ValueError, TypeError, KeyError) as error:
        return carrying(subprocess.CompletedProcess(done.args, 2, "", f"invalid Agh refs collection: {error}"))
    result = subprocess.CompletedProcess(done.args, 0, "".join(f"{oid}\t{name}\n" for name, oid in refs.items()), "")
    # Complete framing-validated advertisement DATA, not a type label for
    # tags/other namespaces. Destination readers verify original local bodies.
    result.advertisement_refs = tuple(advertised.items())
    # Every returned OID was witnessed as a commit, in some store or natively.
    result.witnessed_tips = len(objects)
    # Retain honest native accounting for callers collecting operation DATA.
    return carrying(result)



def _destination_commit_refs(refs, git_dir: Path, *, deadline: float, env=None):
    """Peel only original local object DATA in the maintained guarded view.

    Missing nonmain objects supply no exclusion credit. A missing/unreadable
    main, corrupt original, changed ODB or malformed tag is NOT JUDGED.
    No object is fetched/installed, and no caller config or ref is copied.
    """
    def remaining():
        value = deadline - time.monotonic()
        if value <= 0:
            raise TimeoutError("destination original-object deadline exhausted")
        return value
    result, unavailable = [], []
    with _commit_transport(git_dir, deadline=deadline, env=env) as (directory, view, current, _install):
        objects = {}
        retained_bytes = 0
        def read_originals(oids):
            nonlocal retained_bytes
            current()
            read = RemoteTips.originals(view, oids, timeout=remaining(), env=env,
                                        cwd=directory, isolate_git_config=True)
            if read is None:
                raise ValueError("destination original object bytes are unreadable or corrupt")
            for oid in oids:
                value = read.get(oid)
                if value is not None:
                    kind, body = value
                    if kind != b"tag":
                        body = b""  # Its original hash/type was checked; only tags need peeling.
                    retained_bytes += len(body)
                    if retained_bytes > MAX_OBJECT_READ_BYTES:
                        raise ValueError("destination tag metadata exceeds byte budget")
                    value = kind, body
                objects[oid] = value
            current()
        # Capture each advertised original once, including tag/peeled objects;
        # peeled observations never replace verification of their actual tag.
        oids = list(dict.fromkeys(oid for _ref, oid in refs))
        for start in range(0, len(oids), ANCESTRY_BATCH):
            read_originals(oids[start:start + ANCESTRY_BATCH])
        def original(oid):
            if oid not in objects:
                read_originals([oid])
            return objects[oid]
        for ref, oid in refs:
            if ref.endswith("^{}"):
                continue  # Never substitute a peeled observation for its original tag.
            visited, expected, commit = set(), None, None
            while True:
                if oid in visited or len(visited) >= 64:
                    raise ValueError("destination original tag chain is cyclic or exceeds bound")
                visited.add(oid)
                value = original(oid)
                if value is None:
                    break
                kind, body = value
                if expected is not None and kind != expected:
                    raise ValueError("destination original tag target has a different type")
                if kind == b"commit":
                    commit = oid
                    break
                if kind != b"tag":
                    break
                header = body.split(b"\n\n", 1)[0].split(b"\n")
                links = [line[7:] for line in header if line.startswith(b"object ")]
                types = [line[5:] for line in header if line.startswith(b"type ")]
                if (len(links) != 1 or len(types) != 1
                        or re.fullmatch(b"[0-9a-f]{40}", links[0]) is None
                        or links[0] == b"0" * 40
                        or types[0] not in (b"commit", b"tag", b"tree", b"blob")):
                    raise ValueError("malformed destination original tag")
                oid, expected = links[0].decode("ascii"), types[0]
            if commit is None:
                if ref == MAIN_REF:
                    raise ValueError("destination main original commit is unavailable; NOT JUDGED")
                unavailable.append(ref)
            else:
                result.append((ref, commit))
        current()
        remaining()
    return result, unavailable


def destination_refs(url: str, *, git_dir: Path, env=None, cwd=None,
                     timeout: float = LS_REMOTE_TIMEOUT_S):
    """Fresh native GitHub refs, resolved against this caller's actual ODB.

    The complete advertisement and durable type checks reuse remote_refs;
    caller-supplied push rows and local ref names authenticate nothing.
    """
    deadline = time.monotonic() + timeout
    done = remote_refs(url, git_dir=git_dir, env=env, cwd=cwd, timeout=timeout)
    if done.returncode:
        return done
    try:
        refs = done.advertisement_refs
        resolved, unavailable = _destination_commit_refs(refs, git_dir, deadline=deadline, env=env)
    except _PublicationSourceFailure as error:
        return error.result
    except (AttributeError, OSError, TimeoutError, ValueError) as error:
        return subprocess.CompletedProcess(done.args, 2, "", str(error))
    result = subprocess.CompletedProcess(done.args, 0,
        "".join(f"{oid}\t{ref}\n" for ref, oid in resolved), "")
    result.advertisement_refs = refs
    result.unavailable_refs = tuple(unavailable)
    return result


def fetch_exact_source(url: str, root: Path, oid: str, *,
                       env: Optional[dict[str, str]] = None,
                       timeout: float = FETCH_TIMEOUT_S) -> subprocess.CompletedProcess:
    """Materialize one authenticated snapshot for normal local composition.

    GitHub goes through the original owned Agh source transport. Literal
    local remotes use file-only Git without changing caller tracking refs.
    The caller still merges the immutable OID and validates its own checkout.
    """
    if re.fullmatch(r"[0-9a-f]{40}(?:[0-9a-f]{24})?", oid) is None:
        return subprocess.CompletedProcess([], 2, "", "source snapshot is not an exact object identity")
    try:
        repository = github_repository(url)
    except ValueError as error:
        return subprocess.CompletedProcess([], 2, "", str(error))
    if repository is not None:
        if len(oid) != 40:
            return subprocess.CompletedProcess([], 2, "", "native GitHub source intake requires SHA-1")
        return _fetch_exact_github(repository, root, oid, env=env, timeout=timeout)
    return _run(["git", "-C", str(root), "fetch", "--no-write-fetch-head", "--no-tags",
                 "--no-recurse-submodules", "--no-prune", "--no-auto-maintenance", "--refmap=",
                 "--", url, oid], timeout=timeout, env=env, cwd=root)


class _PublicationSourceFailure(Exception):
    def __init__(self, result):
        self.result = result


def _publication_parent(path: Path) -> Path:
    """The existing local-diagnostic fixed-system-temp factory profile.

    The production caller supplies canonical /tmp, not caller TMPDIR. Its
    trusted root-owned sticky namespace protects a newly made private child;
    hostile same-UID processes and privileged namespace changes are excluded.
    This is not a generic parent-adoption or release-isolation primitive.
    """
    info = path.lstat()
    if (os.name != "posix" or not hasattr(os, "getuid") or not stat.S_ISDIR(info.st_mode)
            or info.st_uid != 0 or not info.st_mode & stat.S_ISVTX):
        raise _PublicationSourceFailure(subprocess.CompletedProcess(
            [], 2, "", "publication requires the trusted root-owned sticky system temporary directory"))
    return path


@contextlib.contextmanager
def _source_transport(prefix):
    """Fresh private source transport under the fixed system-temp profile."""
    parent = _publication_parent(Path("/tmp").resolve(strict=True))
    with tempfile.TemporaryDirectory(prefix=prefix, suffix=".noindex", dir=parent) as temporary:
        directory = Path(temporary)
        created = directory.lstat()
        def check_private():
            current = directory.lstat()
            if not (stat.S_ISDIR(current.st_mode) and current.st_uid == os.getuid()
                    and stat.S_IMODE(current.st_mode) == 0o700
                    and (current.st_dev, current.st_ino) == (created.st_dev, created.st_ino)):
                raise _PublicationSourceFailure(subprocess.CompletedProcess(
                    [], 2, "", "private source transport root changed"))
        check_private()
        data = directory / ".ubd"
        data.mkdir(mode=0o700)
        yield directory, data, check_private


@contextlib.contextmanager
def _commit_transport(git_dir, *, deadline, env):
    """Lend original object DATA to a fresh, configuration-free native view.

    The caller's refs, shallow boundary, replacements and transport settings
    are not inputs to native original-parent ancestry. Agh still hashes every
    original commit and owns all genuinely cold reads under its normal policy.
    """
    original = Path(git_dir).absolute()

    def remaining():
        value = deadline - time.monotonic()
        if value <= 0:
            raise _PublicationSourceFailure(subprocess.CompletedProcess(
                [], 124, "", "native commit read deadline exhausted"))
        return value

    with _source_transport("trust-commit-read-") as (directory, data, check_private):
        def local(arguments, *, input_text=None, object_output=None):
            done = _run(["git", *arguments], timeout=remaining(), env=env,
                        cwd=directory, isolate_git_config=True, input_text=input_text,
                        git_object_directory=object_output)
            if done.returncode:
                raise _PublicationSourceFailure(done)
            return done.stdout.strip()

        def object_directory():
            value = Path(local(["--git-dir", str(original), "rev-parse",
                                "--path-format=absolute", "--git-path", "objects"]))
            if not value.is_absolute():
                raise ValueError("original commit object directory is not absolute")
            return value.resolve(strict=True)

        objects = object_directory()
        # Git's alternates file uses one pathname per line. Never reinterpret
        # a caller path containing another entry as a wider object population.
        if any(character in str(objects) for character in ("\n", "\r", "\0")):
            raise ValueError("original commit object directory has unsupported framing")
        descriptor = os.open(objects, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_CLOEXEC)
        try:
            created = os.fstat(descriptor)

            def check_current():
                check_private()
                held, named = os.fstat(descriptor), objects.lstat()
                if (not stat.S_ISDIR(named.st_mode)
                        or (held.st_dev, held.st_ino) != (created.st_dev, created.st_ino)
                        or (named.st_dev, named.st_ino) != (held.st_dev, held.st_ino)
                        or object_directory() != objects):
                    raise _PublicationSourceFailure(subprocess.CompletedProcess(
                        [], 2, "", "native commit read original object directory changed"))

            check_current()
            view = data / "commits.git"
            local(["init", "--quiet", "--bare", "--template=", str(view)])
            (view / "objects/info/alternates").write_text(str(objects) + "\n")
            check_current()

            def install(commits):
                # Enumerate ONLY this private view's owned objects; following
                # its DATA alternates would copy unrelated canonical history.
                selected = set(commits)
                for fanout in (view / "objects").iterdir():
                    if re.fullmatch(r"[0-9a-f]{2}", fanout.name):
                        if fanout.is_symlink() or not fanout.is_dir():
                            raise ValueError("native original commit cache has invalid custody")
                        for leaf in fanout.iterdir():
                            if (leaf.is_symlink() or not leaf.is_file()
                                    or re.fullmatch(r"[0-9a-f]{38}", leaf.name) is None):
                                raise ValueError("native original commit cache has invalid framing")
                            selected.add(fanout.name + leaf.name)
                    elif fanout.name == "pack":
                        if fanout.is_symlink() or not fanout.is_dir():
                            raise ValueError("native original commit pack has invalid custody")
                        for index in fanout.glob("*.idx"):
                            pack = index.with_suffix(".pack")
                            if (index.is_symlink() or not index.is_file()
                                    or re.fullmatch(r"pack-[0-9a-f]{40}\.idx", index.name) is None
                                    or pack.is_symlink() or not pack.is_file()):
                                raise ValueError("native original commit pack index has invalid custody")
                            with index.open("rb") as data:
                                done = _run(["git", "show-index"], timeout=remaining(), env=env,
                                            cwd=directory, isolate_git_config=True, input_file=data)
                            if done.returncode:
                                raise ValueError("native original commit pack index is unreadable")
                            for row in done.stdout.splitlines():
                                fields = row.split()
                                if len(fields) < 2 or re.fullmatch(r"[0-9a-f]{40}", fields[1]) is None:
                                    raise ValueError("native original commit pack index has invalid framing")
                                selected.add(fields[1])
                if not selected:
                    return
                check_current()
                ordered = sorted(selected)
                raw = _run(["git", "--git-dir", str(view), "cat-file", "--batch"],
                           timeout=remaining(), env=env, cwd=directory, binary=True,
                           input_text="".join(oid + "\n" for oid in ordered))
                if raw.returncode:
                    raise ValueError("native original commit cache is unreadable")
                stream = io.BytesIO(raw.stdout)
                for oid in ordered:
                    header = stream.readline().split()
                    if len(header) != 3 or header[0] != oid.encode() or header[1] != b"commit":
                        raise ValueError("native original commit cache contains a non-commit or missing object")
                    size = int(header[2])
                    body = stream.read(size)
                    if (size < 0 or len(body) != size or stream.read(1) != b"\n"
                            or hashlib.sha1(b"commit " + str(size).encode() + b"\0" + body).hexdigest() != oid):
                        raise ValueError("native original commit cache has a different hash")
                if stream.read():
                    raise ValueError("native original commit cache has trailing bytes")
                prefix = directory / ".ubd" / "original-commit-cache"
                pack_id = local(["--git-dir", str(view), "pack-objects", "--threads=1", str(prefix)],
                                input_text="".join(oid + "\n" for oid in ordered))
                if re.fullmatch(r"[0-9a-f]{40}", pack_id) is None:
                    raise ValueError("native original commit cache has no exact pack identity")
                intake = directory / ".ubd" / "commit-cache-output.git"
                local(["init", "--quiet", "--bare", "--template=", str(intake)])
                with Path(str(prefix) + "-" + pack_id + ".pack").open("rb") as data:
                    done = _run(["git", "--git-dir", str(intake), "index-pack", "--stdin"],
                                timeout=remaining(), env=env, cwd=directory,
                                isolate_git_config=True, input_file=data, git_object_directory=objects)
                if done.returncode:
                    raise ValueError("native original commit cache could not be imported")
                check_current()

            yield directory, view, check_current, install
        finally:
            os.close(descriptor)


def _fetch_exact_github(repository, root, oid, *, env, timeout=FETCH_TIMEOUT_S):
    """Acquire through Agh, then import objects through a private Git context.

    The original repository may have a hooks policy that native Agh refuses.
    Neither Agh nor the local object import adopts that configuration. The latter uses
    a separate private bare repository's config/refs/index, with only its object
    output directed to the original common object directory. No caller ref,
    FETCH_HEAD, index or worktree is an intake destination.
    """
    deadline = time.monotonic() + timeout
    native = None

    def remaining():
        seconds = deadline - time.monotonic()
        if seconds <= 0:
            raise _PublicationSourceFailure(subprocess.CompletedProcess(
                [], 124, "", "source intake exhausted the original deadline"))
        return seconds

    def require(condition, reason):
        if not condition:
            raise _PublicationSourceFailure(subprocess.CompletedProcess([], 2, "", reason))

    def run(arguments, directory, *, objects=None, input_text=None, input_file=None):
        return _run(["git", *arguments], timeout=remaining(), env=env, cwd=directory,
                    isolate_git_config=True, git_object_directory=objects, input_text=input_text,
                    input_file=input_file)

    def local(arguments, directory, *, objects=None, input_text=None, input_file=None):
        done = run(arguments, directory, objects=objects, input_text=input_text, input_file=input_file)
        if done.returncode:
            raise _PublicationSourceFailure(done)
        return done.stdout.strip()

    def head(directory):
        done = run(["-C", str(directory), "rev-parse", "--verify", "--quiet", "HEAD^{commit}"], directory)
        if done.returncode == 0:
            value = done.stdout.strip()
            require(re.fullmatch(r"[0-9a-f]{40}", value), "source intake HEAD is not an exact SHA-1 commit")
            return value
        # Retain the existing initialized-but-unborn repository profile. A
        # dangling/malformed existing HEAD is not an empty repository.
        named = run(["-C", str(directory), "symbolic-ref", "--quiet", "HEAD"], directory)
        if done.returncode == 1 and named.returncode == 0:
            ref = named.stdout.strip()
            missing = run(["-C", str(directory), "show-ref", "--verify", "--quiet", ref], directory)
            if ref.startswith("refs/heads/") and missing.returncode == 1:
                return None
        raise _PublicationSourceFailure(done)

    try:
        root = Path(root).resolve(strict=True)
        original_head = head(root)
        def object_directory():
            return Path(local(["-C", str(root), "rev-parse", "--path-format=absolute",
                               "--git-path", "objects"], root)).resolve(strict=True)
        objects = object_directory()
        flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_CLOEXEC
        with contextlib.ExitStack() as retained:
            descriptor = os.open(objects, flags)
            retained.callback(os.close, descriptor)
            original_objects = os.fstat(descriptor)
            def check_original():
                held, named = os.fstat(descriptor), objects.lstat()
                require(stat.S_ISDIR(named.st_mode)
                        and (held.st_dev, held.st_ino) == (original_objects.st_dev, original_objects.st_ino)
                        and (named.st_dev, named.st_ino) == (held.st_dev, held.st_ino)
                        and object_directory() == objects,
                        "source intake original object directory changed")
                require(head(root) == original_head, "source intake original HEAD changed")
            check_original()
            with _source_transport("trust-land-intake-") as (directory, data, check_private):
                acquisition = data / "source.noindex"
                # A shallow local clone can invoke upload-pack and demand old
                # blob bodies before Agh runs. Source intake requires the exact
                # selected checkout and commit ancestry, not historical bodies.
                local(["init", "--quiet", "--template=", str(acquisition)], directory)
                check_private()
                check_original()
                native = _agh(repository, ["repo", "fetch", repository, str(acquisition),
                                          "--ref", oid, "--into", "refs/agh/land-discovery",
                                          "--checkout-closure"],
                              timeout=remaining(), env=env)
                if native.returncode:
                    return native
                check_private()
                check_original()
                fetched = local(["-C", str(acquisition), "rev-parse", "--verify", "refs/agh/land-discovery"], acquisition)
                require(fetched == oid, "native source intake returned a different commit")
                check_original()
                require(local(["-C", str(acquisition), "cat-file", "-t", oid], acquisition) == "commit",
                        "native source intake did not materialize the commit")
                tree = local(["-C", str(acquisition), "rev-parse", "--verify", oid + "^{tree}"], acquisition)
                require(re.fullmatch(r"[0-9a-f]{40}", tree), "source intake tree is not an exact SHA-1 identity")
                local(["-C", str(acquisition), "rev-list", "--objects", "--missing=error", "--quiet", tree], acquisition)
                # A checkout closure may omit historical tree/blob bodies.
                # Transfer its exact commit ancestry and selected snapshot;
                # upload-pack's negotiation can revisit absent old objects.
                selected = {item: "commit" for item in local(
                    ["-C", str(acquisition), "rev-list", oid], acquisition).splitlines()}
                selected[tree] = "tree"
                rows = local(["-C", str(acquisition), "ls-tree", "-r", "-t", "--full-tree", oid], acquisition)
                for row in rows.splitlines():
                    fields = row.partition("\t")[0].split()
                    require(len(fields) == 3 and fields[1] in ("tree", "blob", "commit"),
                            "source intake has an invalid snapshot entry")
                    if fields[1] != "commit":  # Gitlinks own no objects here.
                        require(fields[2] not in selected or selected[fields[2]] == fields[1],
                                "source intake has conflicting selected object types")
                        selected[fields[2]] = fields[1]
                require(oid in selected and all(re.fullmatch(r"[0-9a-f]{40}", item) for item in selected),
                        "source intake has an invalid exact object identity")
                # The authenticated native snapshot owns the precise raw
                # sizes, including multi-GiB total source trees. Do not widen
                # the separate 32-MiB metadata reader or confuse raw size with
                # the existing compressed-pack import cap.
                inventory = local(["-C", str(acquisition), "cat-file", "--batch-check"], acquisition,
                                  input_text="".join(item + "\n" for item in selected))
                records = inventory.splitlines()
                require(len(records) == len(selected), "source intake size inventory is incomplete")
                sized = {}
                for item, record in zip(selected, records):
                    fields = record.split()
                    require(len(fields) == 3 and fields[:2] == [item, selected[item]]
                            and fields[2].isascii() and fields[2].isdigit() and len(fields[2]) <= 20,
                            "source intake size inventory differs from selected identities")
                    sized[item] = (fields[1], int(fields[2]))
                check_original()
                verified, held = _verified_present_objects(root, sized, env=env, timeout=remaining())
                if verified.returncode:
                    raise _PublicationSourceFailure(verified)
                check_private()
                check_original()
                missing = sorted(set(selected) - held)
                if missing:
                    pack_prefix = data / "snapshot"
                    pack_id = local(["-C", str(acquisition), "pack-objects", "--threads=1", str(pack_prefix)],
                                    acquisition, input_text="".join(item + "\n" for item in missing))
                    require(re.fullmatch(r"[0-9a-f]{40}", pack_id), "source intake pack has no exact identity")
                    pack = data / ("snapshot-" + pack_id + ".pack")
                    destination = data / "intake.git"
                    local(["init", "--quiet", "--bare", "--template=", str(destination)], directory)

                    check_original()
                    with os.fdopen(os.open(pack, os.O_RDONLY | os.O_NOFOLLOW | os.O_CLOEXEC), "rb") as stream:
                        before = os.fstat(stream.fileno())
                        require(stat.S_ISREG(before.st_mode), "source intake pack is not a regular file")
                        require(before.st_size <= 2 * 1024 ** 3, "source intake snapshot pack exceeds 2 GiB")
                        imported = local(["--git-dir", str(destination), "index-pack", "--stdin"], directory,
                                         objects=objects, input_file=stream)
                        require(imported == "pack\t" + pack_id, "source intake imported a different pack")
                        after, named = os.fstat(stream.fileno()), pack.lstat()
                        identity = lambda s: (s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns)
                        require(identity(before) == identity(after) == identity(named),
                                "source intake pack changed during import")
                check_private()
                check_original()
            # Check through the original repository after private stores are
            # gone: an alternate into temporary acquisition is never a result.
            require(local(["-C", str(root), "cat-file", "-t", oid], root) == "commit",
                    "source intake original store did not receive the commit")
            local(["-C", str(root), "cat-file", "-e", oid + "^{tree}"], root)
            local(["-C", str(root), "rev-list", "--objects", "--missing=error", "--quiet", tree], root)
            check_original()
        return native
    except (_PublicationSourceFailure, OSError) as error:
        result = (error.result if isinstance(error, _PublicationSourceFailure)
                  else subprocess.CompletedProcess([], 127, "", str(error)))
        if native is not None:
            return subprocess.CompletedProcess(native.args, result.returncode, native.stdout,
                                               (native.stderr or "") + "\n" + (result.stderr or ""))
        return result


def push_exact_source(url: str, root: Path, before: str, after: str, *,
                      env: Optional[dict[str, str]] = None) -> subprocess.CompletedProcess:
    """Publish exact objects through an owned clean local transport clone.

    A development checkout can have hooks that Agh correctly refuses in its
    source repository. Retain immutable object data in the transport itself,
    not its configuration or working files. A native publication reader cannot
    depend on access to the caller's object directory through Git alternates.
    The gate still checks the original checkout and remote ACK.
    """
    if any(re.fullmatch(r"[0-9a-f]{40}", oid) is None for oid in (before, after)) or before == after:
        return subprocess.CompletedProcess([], 2, "", "publication requires two distinct exact SHA-1 commits")
    try:
        repository = github_repository(url)
    except ValueError as error:
        return subprocess.CompletedProcess([], 2, "", str(error))
    if repository is None:
        return subprocess.CompletedProcess([], 2, "", "native Agh publication requires a GitHub repository")
    deadline = time.monotonic() + FETCH_TIMEOUT_S
    native = None

    def remaining():
        seconds = deadline - time.monotonic()
        if seconds <= 0:
            raise _PublicationSourceFailure(subprocess.CompletedProcess(
                [], 124, "", "publication source preparation exhausted the original deadline"))
        return seconds

    def local(arguments, directory):
        done = _run(["git", *arguments], timeout=remaining(), env=env, cwd=directory,
                    isolate_git_config=True)
        if done.returncode:
            raise _PublicationSourceFailure(done)
        return done.stdout.strip()

    def require(condition, reason):
        if not condition:
            raise _PublicationSourceFailure(subprocess.CompletedProcess([], 2, "", reason))

    def source_tree(directory):
        head = local(["-C", str(directory), "rev-parse", "--verify", "HEAD^{commit}"], directory)
        require(head == after, "publication source HEAD differs from the qualified commit")
        tree = local(["-C", str(directory), "rev-parse", "--verify", after + "^{tree}"], directory)
        require(re.fullmatch(r"[0-9a-f]{40}", tree), "publication source tree is not an exact SHA-1 identity")
        return tree

    def require_history(directory):
        # A complete selected checkout can still lack old blobs or trees.
        # Refuse that local availability failure before native strict packing;
        # this traversal is not a replacement for Agh's full connectivity,
        # shallow-source, pack validation or remote expected-ref checks.
        done = _run(["git", "-C", str(directory), "rev-list", "--quiet", "--objects",
                     "--missing=error", after], timeout=remaining(), env=env, cwd=directory,
                    isolate_git_config=True)
        if done.returncode:
            raise _PublicationSourceFailure(subprocess.CompletedProcess(
                done.args, done.returncode, done.stdout,
                "publication history is incomplete or unreadable: " + (done.stderr or "")))

    def retain_alternate_objects(transport):
        # --local owns the caller's existing objects by hardlink, but inherits
        # its alternates. Retain those same immutable DATA files too, without
        # --dissociate's full-history repack and temporary disk amplification.
        # Git resolves recursive/relative alternates; we do not parse their
        # pointer files or grant the native reader access to borrowed stores.
        def alternates():
            output = local(["-C", str(transport), "count-objects", "-v"], transport)
            return [line[len("alternate: "):] for line in output.splitlines()
                    if line.startswith("alternate: ")]

        git_dir = Path(local(["-C", str(transport), "rev-parse", "--absolute-git-dir"], transport))
        require(git_dir.resolve(strict=True) == transport / ".git",
                "publication transport object namespace escaped its owned clone")
        objects = git_dir / "objects"
        borrowed = alternates()
        if not borrowed:
            return
        with contextlib.ExitStack() as stack:
            def directory(path, lifetime=stack):
                remaining()
                fd = os.open(path, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
                lifetime.callback(os.close, fd)
                observed = os.fstat(fd)
                def current():
                    now = os.stat(path, follow_symlinks=False)
                    require(stat.S_ISDIR(now.st_mode) and
                            (now.st_dev, now.st_ino) == (observed.st_dev, observed.st_ino),
                            "publication object directory changed during retention")
                current()
                lifetime.callback(current)
                return fd

            destination = directory(objects)

            def retain(source_fd, destination_fd, name):
                remaining()
                before = os.stat(name, dir_fd=source_fd, follow_symlinks=False)
                require(stat.S_ISREG(before.st_mode),
                        "publication borrowed object is not a regular data file")
                try:
                    os.link(name, name, src_dir_fd=source_fd, dst_dir_fd=destination_fd,
                            follow_symlinks=False)
                except FileExistsError:
                    pass
                except OSError as error:
                    if error.errno != errno.EXDEV:
                        raise
                    # A borrowed store can be on another volume. Preserve that
                    # capability without recompression: copy only on EXDEV,
                    # exclusively into our owned namespace, then run the same
                    # exact-byte and source identity checks as for collisions.
                    try:
                        copied = os.open(name, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                                         0o600, dir_fd=destination_fd)
                    except FileExistsError:
                        pass
                    else:
                        with contextlib.ExitStack() as copying:
                            copying.callback(os.close, copied)
                            original = os.open(name, os.O_RDONLY | os.O_NOFOLLOW, dir_fd=source_fd)
                            copying.callback(os.close, original)
                            original_stat = os.fstat(original)
                            require(stat.S_ISREG(original_stat.st_mode) and
                                    (original_stat.st_dev, original_stat.st_ino,
                                     original_stat.st_size, original_stat.st_mtime_ns) ==
                                    (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns),
                                    "publication borrowed object changed before copying")
                            while True:
                                remaining()
                                chunk = os.read(original, 1024 * 1024)
                                if not chunk:
                                    break
                                pending = memoryview(chunk)
                                while pending:
                                    remaining()
                                    written = os.write(copied, pending)
                                    require(written > 0, "publication object copy made no progress")
                                    pending = pending[written:]
                            os.fchmod(copied, stat.S_IMODE(before.st_mode) & 0o666)
                # Pin both files while comparing; a distinct existing file is
                # accepted only when byte-identical. Never overwrite an object.
                with contextlib.ExitStack() as files:
                    def opened(parent):
                        fd = os.open(name, os.O_RDONLY | os.O_NOFOLLOW, dir_fd=parent)
                        files.callback(os.close, fd)
                        observed = os.fstat(fd)
                        require(stat.S_ISREG(observed.st_mode),
                                "publication retained object is not a regular data file")
                        return fd, observed
                    src, src_stat = opened(source_fd)
                    dst, dst_stat = opened(destination_fd)
                    identity = lambda value: (value.st_dev, value.st_ino, value.st_size, value.st_mtime_ns)
                    require(identity(src_stat) == identity(before),
                            "publication borrowed object changed before retention")
                    if (src_stat.st_dev, src_stat.st_ino) != (dst_stat.st_dev, dst_stat.st_ino):
                        require(src_stat.st_size == dst_stat.st_size,
                                "publication object data collision")
                        def digest(fd):
                            result = hashlib.sha256()
                            while True:
                                remaining()
                                chunk = os.read(fd, 1024 * 1024)
                                if not chunk:
                                    return result.digest()
                                result.update(chunk)
                        require(digest(src) == digest(dst), "publication object data collision")
                    require(identity(os.fstat(src)) == identity(src_stat) and
                            identity(os.fstat(dst)) == identity(dst_stat) and
                            identity(os.stat(name, dir_fd=source_fd, follow_symlinks=False)) == identity(src_stat) and
                            identity(os.stat(name, dir_fd=destination_fd, follow_symlinks=False)) == identity(dst_stat),
                            "publication object data changed during retention")

            for raw in borrowed:
                require(raw.startswith("/") and not any(ord(char) < 32 for char in raw),
                        "publication alternate is not an unambiguous absolute object path")
                source_path = Path(raw).resolve(strict=True)
                with contextlib.ExitStack() as source_lifetime:
                    source = directory(source_path, source_lifetime)
                    for name in os.listdir(source):
                        remaining()
                        if name != "pack" and re.fullmatch(r"[0-9a-f]{2}", name) is None:
                            continue
                        with contextlib.ExitStack() as child_lifetime:
                            source_child = directory(source_path / name, child_lifetime)
                            try:
                                os.mkdir(name, dir_fd=destination)
                            except FileExistsError:
                                pass
                            destination_child = directory(objects / name, child_lifetime)
                            pattern = (r"pack-[0-9a-f]{40}\.(?:pack|idx|rev|keep|bitmap|promisor|mtimes)"
                                       if name == "pack" else r"[0-9a-f]{38}")
                            for entry in os.listdir(source_child):
                                remaining()
                                if re.fullmatch(pattern, entry):
                                    retain(source_child, destination_child, entry)
            # Retire only the owned clone's borrowing pointer, after all data
            # is owned. Native full-history/pack/hash/custody checks still run.
            info = directory(objects / "info")
            pointer = os.stat("alternates", dir_fd=info, follow_symlinks=False)
            require(stat.S_ISREG(pointer.st_mode),
                    "publication transport alternates pointer is not regular")
            os.unlink("alternates", dir_fd=info)
            require(not alternates(), "publication transport still borrows object directories")

    try:
        root = Path(root).resolve(strict=True)
        tree = source_tree(root)
        require(local(["-C", str(root), "cat-file", "-t", before], root) == "commit",
                "publication destination is not an exact commit")
        local(["-C", str(root), "merge-base", "--is-ancestor", before, after], root)
        require_history(root)
        with _source_transport("trust-land-publication-") as (directory, data, check_private):
            transport = data / "source.noindex"
            local(["clone", "--quiet", "--local", "--no-checkout", "--single-branch", "--no-tags",
                   "--template=", "--", str(root), str(transport)], directory)
            check_private()
            retain_alternate_objects(transport)
            check_private()
            require(source_tree(transport) == tree, "publication transport tree differs from the qualified source")
            local(["-C", str(transport), "merge-base", "--is-ancestor", before, after], transport)
            require(source_tree(root) == tree, "publication source changed during transport preparation")
            require_history(transport)
            request = data / "update.json"
            request.write_text(json.dumps([{"ref": MAIN_REF, "before": before, "after": after}]))
            native = _run(["agh", "repo", "push", repository, str(transport), "--input", str(request),
                           "--no-anonymous-api"], timeout=remaining(), env=env, cwd=root)
            if native.returncode:
                return native
            check_private()
            require(source_tree(root) == tree, "publication source changed during native transport")
            require(source_tree(transport) == tree, "publication transport changed during native transport")
            return native
    except (_PublicationSourceFailure, OSError) as error:
        result = (error.result if isinstance(error, _PublicationSourceFailure)
                  else subprocess.CompletedProcess([], 127, "", str(error)))
        if native is not None:
            # A post-operation bookend failure cannot erase the actual native
            # answer or pretend the remote write had no side effect.
            return subprocess.CompletedProcess(native.args, result.returncode, native.stdout,
                                               (native.stderr or "") + "\n" + (result.stderr or ""))
        return result


@dataclass(frozen=True)
class Remote:
    """The store a question is asked in, and the remote it is asked of."""

    git_dir: Optional[Path]
    name: str
    url: str
    error: str = ""  # non-empty: no usable store or remote


@dataclass(frozen=True)
class Inventory:
    """A remote's heads and pins, in judging order: main, pins, other heads.

    A ``scope="main"`` inventory of a GitHub remote holds only
    ``refs/heads/main`` (the one ref it witnessed); ``advertised_heads``
    counts every head the advertisement named."""

    url: str
    refs: tuple[tuple[str, str], ...]
    error: str = ""
    advertised_heads: int = 0

    def get(self, ref: str) -> Optional[str]:
        for name, sha in self.refs:
            if name == ref:
                return sha
        return None

    @property
    def heads(self) -> int:
        return sum(1 for name, _ in self.refs if name.startswith(HEADS))

    @property
    def pins(self) -> int:
        return sum(1 for name, _ in self.refs if name.startswith(PINS))


@dataclass(frozen=True)
class Verdict:
    state: str
    refs: tuple[str, ...] = ()
    detail: str = ""

    @property
    def contained(self) -> bool:
        return self.state == CONTAINED


def _order(refs: Iterable[tuple[str, str]]) -> tuple[tuple[str, str], ...]:
    """main first (a pin almost always lives there, and its fetch is the
    cheapest answer), then the exact-anchor namespace, then other heads."""

    def rank(item: tuple[str, str]) -> tuple[int, str]:
        name = item[0]
        if name == MAIN_REF:
            return (0, name)
        if name.startswith(PINS):
            return (1, name)
        return (2, name)

    return tuple(sorted(refs, key=rank))


class AncestryMemory:
    """Remembered answers to "is commit A an ancestor of commit B?".

    The answer is a property of the two ids alone (a commit id names its
    parents), so it never goes stale and needs no invalidation: one file per
    question, ``<root>/<FORMAT>/<A[:2]>/<A>-<B>``, holding ``contained`` or
    ``not-contained``, written atomically. ``FORMAT`` names the answer sources
    and their rules (Agh's native ancestry; a local ``merge-base`` 0, or a 1
    only from a non-shallow store where ``rev-list`` finds every parent): a
    fix to any of them bumps its ``v1`` segment, and it carries the native
    reply contract (``NATIVE_ANCESTRY_SCHEMA``, ``NATIVE_ANCESTRY_SCOPE``), so
    a change to either retires every older answer at once (until 2026-11-15
    the segment was the bare ``v1``, which a changed Agh contract would have
    kept serving). What a remote ref points at, and
    whether a remote still serves a commit, are NOT remembered here: they can
    change, and are read fresh each run. Any unreadable or unexpected file is
    "unknown" and the question is asked again; a failed write costs only that.
    """

    _VALUES = {"contained\n": True, "not-contained\n": False}
    FORMAT = f"v1-agh{NATIVE_ANCESTRY_SCHEMA}-{NATIVE_ANCESTRY_SCOPE}"

    def __init__(self, root: Optional[Path]) -> None:
        self.root = None if root is None else root / self.FORMAT

    def _path(self, ancestor: str, descendant: str) -> Optional[Path]:
        if self.root is None or not all(re.fullmatch(r"[0-9a-f]{40}", s) for s in (ancestor, descendant)):
            return None
        return self.root / ancestor[:2] / f"{ancestor}-{descendant}"

    def get(self, ancestor: str, descendant: str) -> Optional[bool]:
        path = self._path(ancestor, descendant)
        if path is None:
            return None
        try:
            return self._VALUES.get(path.read_text(encoding="ascii"))
        except (OSError, ValueError):
            return None

    def put(self, ancestor: str, descendant: str, contained: bool) -> None:
        path = self._path(ancestor, descendant)
        if path is None:
            return
        try:
            path.parent.mkdir(parents=True, exist_ok=True)
            with tempfile.NamedTemporaryFile("w", encoding="ascii", dir=path.parent,
                                             prefix=".tmp-", delete=False) as handle:
                handle.write("contained\n" if contained else "not-contained\n")
            os.replace(handle.name, path)
        except OSError:
            with contextlib.suppress(OSError, NameError):
                os.unlink(handle.name)


def parse_ls_remote(text: str) -> tuple[tuple[str, str], ...]:
    rows: list[tuple[str, str]] = []
    for line in text.splitlines():
        sha, sep, name = line.partition("\t")
        sha, name = sha.strip().lower(), name.strip()
        if not sep or len(sha) != 40 or not name:
            continue
        if name.startswith(HEADS) or name.startswith(PINS):
            rows.append((name, sha))
    return _order(rows)


class RemoteTips:
    """One per run. Every question about a remote goes through here.

    ``ls_remote_calls`` counts network inventory reads, one per URL; tests use
    it to pin the "one call per module, cached" property. ``ancestry_calls``
    counts native ancestry reads (each carries up to ``ANCESTRY_BATCH``
    questions) and ``remote_questions`` the questions they carried.
    ``commit_fetch_calls`` counts reads that bring commits into a store
    (``ensure``'s, and a literal local remote's deepening), never an ancestry
    read: until 2026-11-15 one ``fetch_calls`` counted every read ``_fetch``
    made, so each ancestry read was counted twice and a run that fetched
    nothing reported "5 fetch(es)". ``witnessed_tips`` counts the tips the
    successful inventories witnessed as commits, however they were witnessed
    (in the store, in the canonical store or by a native read);
    ``witness_reads`` and ``native_witnessed_commits`` count the native reads
    inventories made to witness tips the stores did not hold, and the tips
    those reads witnessed (a store that holds main's tip makes none).
    ``acquired_commits`` and ``api_body_bytes`` sum what every successful
    native read (witness, commit fetch, ancestry) reported acquiring through
    Agh's API, including one whose operation failed at a later step.

    ``memory`` is a directory for ``AncestryMemory`` (immutable answers only).
    ``time_bound`` (seconds) bounds every remote read this object makes,
    together: once it is spent, a read is not started and its question is
    UNJUDGED (COULD NOT RUN), never a pass and never a finding.
    """

    def __init__(self, *, memory: Optional[Path] = None, time_bound: Optional[float] = None) -> None:
        self._lock = threading.Lock()
        self._remotes: dict[str, Remote] = {}
        # (url, scope) -> this run's inventory; see ``inventory``.
        self._inventories: dict[tuple[str, str], Inventory] = {}
        self._url_locks: dict[str, threading.Lock] = {}
        self._store_locks: dict[str, threading.Lock] = {}
        # (git dir, sha) -> (kind, message) for an object a fetch did not
        # bring, so one dead remote costs one timeout, not one per question.
        self._unfetchable: dict[tuple[str, str], tuple[str, str]] = {}
        # (path, sha, scope) -> this run's verdict (a run reads each remote once).
        self._verdicts: dict[tuple[str, str, str], Verdict] = {}
        self._executor: Optional[ThreadPoolExecutor] = None
        self.memory = AncestryMemory(memory)
        self.time_bound = time_bound
        self._deadline = None if time_bound is None else time.monotonic() + time_bound
        self.ls_remote_calls = 0
        self.commit_fetch_calls = 0
        self.ancestry_calls = 0
        self.witnessed_tips = 0
        self.witness_reads = 0
        self.native_witnessed_commits = 0
        self.acquired_commits = 0
        self.api_body_bytes = 0
        self.remote_questions = 0
        self.remembered = 0

    # ------------------------------------------------------ bound and retry
    def _remote_read(self, read: Callable[[float], subprocess.CompletedProcess], cap: float
                     ) -> subprocess.CompletedProcess:
        """Run ``read(timeout)`` inside the run's time bound, retrying a
        transient failure (``TRANSIENT_EXITS``) after each pause the bound
        still allows. The last failure is returned as it was: callers classify
        it, and only a refusal is ever a finding. Once an operator's stop is
        pending (``_active_stop``) nothing is started, retried or waited for:
        the result is ``_STOPPED_EXIT``, which every caller reads as unread."""
        delays = list(TRANSIENT_RETRY_DELAYS_S)
        while True:
            signum = _stop_pending()
            if signum is not None:
                return _stopped([], signum)
            budget = cap if self._deadline is None else min(cap, self._deadline - time.monotonic())
            if budget <= 0:
                spent = f"the {self.time_bound:.0f}s time bound" if self.time_bound is not None else "the read deadline"
                return subprocess.CompletedProcess([], 124, "", f"{spent} for this run's remote reads is spent")
            done = read(budget)
            transient = done.returncode in TRANSIENT_EXITS or (
                done.returncode == 2 and (done.stderr or "") == _OWNED_SESSION_LOST)
            if done.returncode == 0 or not transient or not delays:
                return done
            if any(marker in (done.stderr or "").lower() for marker in _REFUSAL_MARKERS):
                return done
            pause = delays.pop(0)
            if self._deadline is not None and self._deadline - time.monotonic() <= pause:
                return done
            # A stop that arrives during the pause ends it at once.
            until = time.monotonic() + pause
            while _stop_pending() is None and time.monotonic() < until:
                time.sleep(max(0.0, min(0.05, until - time.monotonic())))

    # ----------------------------------------------------------- the store
    def remote(self, path: Path) -> Remote:
        """Resolve ``path`` (a worktree or a bare git dir) to its git dir and
        preferred remote (``origin``, else the first configured)."""
        key = str(path)
        with self._lock:
            cached = self._remotes.get(key)
        if cached is not None:
            return cached
        resolved = self._resolve(path)
        with self._lock:
            self._remotes[key] = resolved
        return resolved

    @staticmethod
    def _resolve(path: Path) -> Remote:
        git_dir: Optional[Path] = None
        # A worktree (its .git a directory, a gitfile or a link) is found from
        # its .git, as git's own discovery does; only a directory with none is
        # asked as a bare store. Asked first as a bare store, two untracked
        # files in a worktree (HEAD, commondir) answered with another
        # repository's store and remote, and a pin it did not hold read as
        # contained (round 6 of LAND-GATE-EW1-FOLLOWUP-REVIEW-4, the IR reader
        # audit).
        dot_git = path / ".git"
        worktree = dot_git.exists() or dot_git.is_symlink()
        bare = None if worktree else _run(["git", "--git-dir", str(path), "rev-parse", "--absolute-git-dir"])
        if bare is not None and bare.returncode == 0 and bare.stdout.strip():
            git_dir = Path(bare.stdout.strip())
        else:
            top = _run(["git", "-C", str(path), "rev-parse", "--show-toplevel"])
            try:
                is_top = top.returncode == 0 and Path(top.stdout.strip()).resolve() == path.resolve()
            except OSError:
                is_top = False
            if is_top:
                found = _run(["git", "-C", str(path), "rev-parse", "--absolute-git-dir"])
                if found.returncode == 0 and found.stdout.strip():
                    git_dir = Path(found.stdout.strip())
        if git_dir is None:
            return Remote(None, "origin", "", error=f"{path} is not a git repository")
        names = _run(["git", "--git-dir", str(git_dir), "remote"])
        listed = [n for n in names.stdout.splitlines() if n.strip()] if names.returncode == 0 else []
        if not listed:
            return Remote(git_dir, "origin", "", error=f"no remote is configured in {git_dir}")
        name = "origin" if "origin" in listed else listed[0]
        url = _run(["git", "--git-dir", str(git_dir), "remote", "get-url", name])
        if url.returncode != 0 or not url.stdout.strip():
            return Remote(git_dir, name, "", error=f"`git remote get-url {name}` failed in {git_dir}: {_message(url)}")
        return Remote(git_dir, name, url.stdout.strip())

    def _account(self, reply: dict, *, witness: bool = False) -> None:
        """Add one successful native read's own acquisition report."""
        with self._lock:
            if witness:
                self.witness_reads += 1
                self.native_witnessed_commits += len(reply["commits"])
            self.acquired_commits += reply["acquired_commits"]
            self.api_body_bytes += reply["api_body_bytes"]

    # ------------------------------------------------------- the inventory
    def inventory(self, path: Path, *, scope: str = "durable") -> Inventory:
        """This run's one read of ``path``'s remote, for ``scope``.

        ``scope="durable"`` witnesses every advertised head and pin as a
        commit (the reach lane needs them all). ``scope="main"`` witnesses
        only ``refs/heads/main``, all a main-scope verdict reads; the other
        entries are still validated (docs/DECISION_QUEUE.md
        IR-COHORT-MAIN-WITNESS-1). A durable inventory read without error
        also serves a main request, as a witnessed superset; a main
        inventory never serves a durable one.
        """
        if scope not in ("durable", "main"):
            raise ValueError(f"unknown inventory scope {scope!r}")
        remote = self.remote(path)
        if remote.error or remote.git_dir is None:
            return Inventory(remote.url, (), error=remote.error)
        with self._lock:
            lock = self._url_locks.setdefault(remote.url, threading.Lock())
        with lock:
            with self._lock:
                cached = self._inventories.get((remote.url, scope))
                durable = self._inventories.get((remote.url, "durable"))
            if cached is None and scope == "main" and durable is not None and not durable.error:
                cached = durable
            if cached is not None:
                return cached
            with self._lock:
                self.ls_remote_calls += 1
            witness = (MAIN_REF,) if scope == "main" else None

            def read(timeout):
                done = remote_refs(remote.url, git_dir=remote.git_dir, timeout=timeout, witness=witness)
                # Every attempt's successful native reads acquired, whether or
                # not the inventory (or this attempt) succeeded. A literal
                # local remote's `git ls-remote` witnesses nothing.
                for observation in getattr(done, "commit_witness_reads", ()):
                    self._account(observation, witness=True)
                return done

            done = self._remote_read(read, LS_REMOTE_TIMEOUT_S)
            if done.returncode != 0:
                found = Inventory(remote.url, (), error=f"remote inventory {remote.url} failed: {_message(done)}")
            else:
                refs = parse_ls_remote(done.stdout)
                # A literal local remote's `git ls-remote` returns every head.
                advertised = getattr(done, "advertisement_refs", refs)
                found = Inventory(remote.url, refs,
                                  advertised_heads=sum(1 for name, _ in advertised if name.startswith(HEADS)))
                with self._lock:
                    self.witnessed_tips += getattr(done, "witnessed_tips", 0)
            with self._lock:
                self._inventories[(remote.url, scope)] = found
            return found

    def prefetch(self, paths: Iterable[Path], *, wait: bool = True) -> None:
        """Read every remote these stores name, concurrently, once each.

        ``wait=False`` starts the reads and returns: a later ``inventory`` of
        the same remote waits on that read instead of issuing its own, so a
        store discovered mid-walk is read while the walk goes on.
        """
        unique = list(dict.fromkeys(paths))
        if not unique:
            return
        with self._lock:
            if self._executor is None:
                self._executor = ThreadPoolExecutor(max_workers=16)
            pool = self._executor
        futures = [pool.submit(self.inventory, path) for path in unique]
        if wait:
            for future in futures:
                future.result()

    # --------------------------------------------------------- the objects
    @staticmethod
    def present(git_dir: Path, shas: Sequence[str], *, timeout: float = FETCH_TIMEOUT_S,
                env: Optional[dict[str, str]] = None, cwd: Optional[Path] = None) -> set[str]:
        """The subset held as hash-verified original commits, never local refs."""
        objects = RemoteTips.originals(git_dir, shas, timeout=timeout, env=env, cwd=cwd)
        return {oid for oid, (kind, _body) in (objects or {}).items() if kind == b"commit"}

    @staticmethod
    def originals(git_dir: Path, shas: Sequence[str], *, timeout: float = FETCH_TIMEOUT_S,
                  env: Optional[dict[str, str]] = None, cwd: Optional[Path] = None,
                  isolate_git_config: bool = False):
        """Original object DATA, or None for an unreadable/malformed byte stream.

        Missing names are omitted. Every present body retains the maintained
        exact framing/hash check, including annotated tag objects before peel.
        """
        if not shas:
            return {}
        if any(not re.fullmatch(r"[0-9a-f]{40}", oid) or oid == "0" * 40 for oid in shas):
            return None
        options = {"isolate_git_config": True} if isolate_git_config else {}
        done = _run(
            ["git", "--git-dir", str(git_dir), "cat-file", "--batch"],
            input_text="".join(f"{sha}\n" for sha in shas), binary=True,
            timeout=timeout, env=env, cwd=cwd, **options,
        )
        if done.returncode:
            return None
        if not isinstance(done.stdout, bytes):
            return None
        try:
            return {oid: (kind, body) for oid, kind, body in _verified_original_rows(
                io.BytesIO(done.stdout), shas) if kind is not None}
        except (ValueError, OSError):
            return None

    def _fetch(
        self,
        remote: Remote,
        shas: Sequence[str],
        *,
        unshallow: bool = False,
        deepen: Optional[int] = None,
        queries: Sequence[tuple[str, str]] = (),
    ) -> subprocess.CompletedProcess[str]:
        assert remote.git_dir is not None
        with self._lock:
            if queries:
                self.ancestry_calls += 1
                self.remote_questions += len(queries)
            else:
                self.commit_fetch_calls += 1
        try:
            repository = github_repository(remote.url)
        except ValueError as error:
            return subprocess.CompletedProcess([], 2, "", str(error))
        if repository is not None:
            done = self._remote_read(
                lambda timeout: _native_commit_read(repository, remote.git_dir, shas, queries,
                                                    timeout=timeout, materialize=True),
                FETCH_TIMEOUT_S)
            if done.returncode == 0:
                # _native_commit_read has validated both counts as ints >= 0.
                self._account(json.loads(done.stdout))
            return done

        git_dir = remote.git_dir
        return self._remote_read(
            lambda timeout: self._local_fetch(git_dir, remote.url, shas, unshallow=unshallow,
                                              deepen=deepen, timeout=timeout),
            FETCH_TIMEOUT_S)

    @staticmethod
    def _local_fetch(git_dir: Path, source: str, shas: Sequence[str], *,
                     unshallow: bool = False, deepen: Optional[int] = None,
                     timeout: float = FETCH_TIMEOUT_S) -> subprocess.CompletedProcess[str]:
        return _run(
            [
                "git",
                "--git-dir",
                str(git_dir),
                "fetch",
                "--quiet",
                "--no-write-fetch-head",
                "--no-tags",
                "--no-recurse-submodules",
                "--no-prune",
                "--no-auto-maintenance",
                "--refmap=",
                *(["--unshallow"] if unshallow else []),
                *([f"--deepen={deepen}"] if deepen else []),
                "--",
                source,
                *shas,
            ],
            timeout=timeout,
        )

    @staticmethod
    def _is_shallow(git_dir: Path, *, timeout: float = FETCH_TIMEOUT_S) -> Optional[bool]:
        done = _run(["git", "--git-dir", str(git_dir), "rev-parse", "--is-shallow-repository"], timeout=timeout)
        if done.returncode == 0:
            state = done.stdout.strip()
            if state in ("true", "false"):
                return state == "true"
        return None

    def _ancestry(self, remote: Remote, pairs: Sequence[tuple[str, str]]
                  ) -> dict[tuple[str, str], tuple[Optional[bool], str]]:
        """Answer every (ancestor, descendant) question, asking as little as possible.

        In order: ``AncestryMemory`` (an immutable answer recorded earlier);
        then, for a GitHub remote, this store, which PROVES containment when
        ``merge-base --is-ancestor`` walks a parent chain it holds (exit 0;
        replace objects and grafts are disabled by ``_env``). A local 1 is not
        taken as a refutation: a commit-only intake can leave a commit whose
        parents this store lacks. Whatever is left goes to the remote in
        batches of ``ANCESTRY_BATCH`` questions per native read (a literal
        local remote keeps ``_contained``'s per-pair deepening transport).
        Every definite answer is remembered. Values are as ``_contained``'s.
        """
        answers: dict[tuple[str, str], tuple[Optional[bool], str]] = {}
        unknown: list[tuple[str, str]] = []
        for pair in dict.fromkeys(pairs):
            known = self.memory.get(*pair)
            if known is None:
                unknown.append(pair)
            else:
                answers[pair] = (known, "")
                with self._lock:
                    self.remembered += 1
        try:
            native = github_repository(remote.url) is not None
        except ValueError as error:
            answers.update({pair: (None, str(error)) for pair in unknown})
            return answers
        if not native:
            for ancestor, descendant in unknown:
                contained, why = self._contained(remote, ancestor, descendant)
                if contained is not None:
                    self.memory.put(ancestor, descendant, contained)
                answers[(ancestor, descendant)] = (contained, why)
            return answers
        if unknown and remote.git_dir is not None:
            gd = str(remote.git_dir)
            local_git = ["git", "--git-dir", gd, "-c", "core.commitGraph=false"]
            held = self.present(remote.git_dir, sorted({sha for pair in unknown for sha in pair}))
            local = [pair for pair in unknown if pair[0] in held and pair[1] in held]
            # A 1 refutes only over a complete history: the store is not
            # shallow and every ancestor commit of every descendant asked
            # about is present (rev-list fails on a missing parent; lazy
            # fetch is off in ``_env``).
            complete = bool(local) and self._is_shallow(remote.git_dir) is False and _run(
                [*local_git, "rev-list", "--quiet", "--stdin"],
                input_text="".join(f"{d}\n" for d in sorted({d for _, d in local}))).returncode == 0
            local_set = set(local)
            remaining = [pair for pair in unknown if pair not in local_set]
            for ancestor, descendant in local:
                status = _run([*local_git, "merge-base", "--is-ancestor", ancestor, descendant]).returncode
                if status == 0 or (status == 1 and complete):
                    self.memory.put(ancestor, descendant, status == 0)
                    answers[(ancestor, descendant)] = (status == 0, "")
                else:
                    remaining.append((ancestor, descendant))
            unknown = remaining
        for start in range(0, len(unknown), ANCESTRY_BATCH):
            batch = unknown[start:start + ANCESTRY_BATCH]
            done = self._fetch(remote, [], queries=batch)
            if done.returncode:
                why = "native exact ancestry unavailable: " + _message(done)
                answers.update({pair: (None, why) for pair in batch})
                continue
            # _fetch has checked the complete exact native query/result binding.
            for pair, reply in zip(batch, json.loads(done.stdout)["queries"]):
                self.memory.put(pair[0], pair[1], reply["contained"])
                answers[pair] = (reply["contained"], "")
        return answers

    def _contained(self, remote: Remote, sha: str, tip: str) -> tuple[Optional[bool], str]:
        """(True, "") contained; (False, "") really not; (None, why) unread.

        GitHub questions delegate to native exact raw-parent ancestry.
        The remaining code is the unchanged literal-local Git transport:
        a by-sha fetch into a SHALLOW store brings the two commits but not
        the history between them, so ``merge-base --is-ancestor`` answers 1
        for a contained pin (measured 2026-10-26: twelve false OFF-MAIN
        rows from depth-1 submodule stores, every pin on its remote's
        main). A 1 from a shallow store therefore earns deepening fetches
        of the same two shas --- same no-ref discipline --- and retests;
        only a 1 from a complete store is a finding. Deepening is
        progressive (256, then x8) with `--unshallow` as the last step:
        measured the same day, every first-party pin sits <=99 commits
        behind its remote main, so the first deepen connects them, while
        a cold full unshallow of nine stores took 452s against 1.8s warm.
        """
        try:
            native = github_repository(remote.url) is not None
        except ValueError as error:
            return None, str(error)
        if native:
            return self._ancestry(remote, [(sha, tip)])[(sha, tip)]
        assert remote.git_dir is not None
        gd = str(remote.git_dir)

        def ask() -> subprocess.CompletedProcess[str]:
            return _run(["git", "--git-dir", gd, "merge-base", "--is-ancestor", sha, tip])

        done = ask()
        if done.returncode == 1:
            # Decide under the store lock: a concurrent question's unshallow
            # landing between this ask and the retest must not leave this
            # answer reading a store that no longer exists.
            with self._lock:
                lock = self._store_locks.setdefault(gd, threading.Lock())
            with lock:
                done = ask()
                deepen_failed = False
                for deepen in (256, 2048, 16384, None):
                    if done.returncode != 1 or not self._is_shallow(remote.git_dir):
                        break
                    if deepen is not None and deepen_failed:
                        # A server may refuse `--deepen` for by-sha wants
                        # while still serving `--unshallow`; spend at most
                        # one more negotiation, on the unshallow step.
                        continue
                    if deepen is None:
                        fetched = self._fetch(remote, [sha, tip], unshallow=True)
                        what = "`git fetch --unshallow"
                    else:
                        fetched = self._fetch(remote, [sha, tip], deepen=deepen)
                        what = f"`git fetch --deepen={deepen}"
                    if fetched.returncode != 0:
                        if deepen is None:
                            return None, f"{what} {remote.url}` failed: {_message(fetched)}"
                        deepen_failed = True
                        continue
                    done = ask()
        if done.returncode == 0:
            return True, ""
        if done.returncode == 1:
            # A shallow server can satisfy --unshallow without supplying
            # complete history. Only a confirmed complete store can refute
            # ancestry; a failed or malformed state query is unread too.
            shallow = self._is_shallow(remote.git_dir)
            if shallow is True:
                return None, "ancestry history remains shallow after fetch"
            if shallow is None:
                return None, "ancestry history completeness could not be read"
            return False, ""
        return None, f"`git merge-base --is-ancestor` failed: {_message(done)}"

    def ensure(self, path: Path, shas: Iterable[str]) -> dict[str, tuple[str, str]]:
        """Make ``shas`` present in ``path``'s store, writing no ref.

        Returns the shas still absent, each with ``("refused", why)`` when the
        remote answered and would not serve it, or ``("error", why)`` when the
        question could not be asked. Empty means all present.
        """
        remote = self.remote(path)
        wanted = [s.lower() for s in dict.fromkeys(shas)]
        if remote.git_dir is None:
            return {sha: ("error", remote.error) for sha in wanted}
        gd = str(remote.git_dir)
        with self._lock:
            lock = self._store_locks.setdefault(gd, threading.Lock())
        with lock:
            held_before = self.present(remote.git_dir, wanted)
            missing = [s for s in wanted if s not in held_before]
            if not missing:
                return {}
            failed: dict[str, tuple[str, str]] = {}
            with self._lock:
                for sha in missing:
                    if (gd, sha) in self._unfetchable:
                        failed[sha] = self._unfetchable[(gd, sha)]
            to_fetch = [s for s in missing if s not in failed]
            if to_fetch and remote.error:
                for sha in to_fetch:
                    failed[sha] = ("error", remote.error)
                to_fetch = []
            if to_fetch:
                # In a shallow store, deepen in the SAME fetch: a by-sha want
                # costs a full server negotiation (measured 2026-10-26:
                # 140-190s against GitHub for the large first-party repos,
                # whatever the depth), so a plain fetch here plus a deepen
                # fetch in `_contained` pays that toll twice per store.
                # `--deepen` (not `--depth`: depth bounds the NEW shas'
                # history, but the connection `merge-base` needs is the
                # already-held tip's ancestry) extends the shallow boundary
                # by 512 --- every first-party pin measured sits <=99 behind
                # its main --- and `_contained`'s deepen loop remains the
                # backstop for anything older. A GitHub remote's native
                # commit read has no boundary to extend (`_fetch` ignores
                # `deepen`), so it is never asked to: until 2026-11-15 its
                # failure was followed by the identical "plain retry" below,
                # each with its own transient retries.
                try:
                    native = github_repository(remote.url) is not None
                except ValueError:
                    native = False  # `_fetch` refuses the URL itself
                deepen = 512 if not native and self._is_shallow(remote.git_dir) else None
                done = self._fetch(remote, to_fetch, deepen=deepen)
                if done.returncode != 0 and deepen:
                    # The server may refuse `--deepen` while still serving
                    # plain by-sha wants; the objects matter here, the
                    # boundary extension was only the toll-saver (and
                    # `_contained` remains the backstop). One plain retry.
                    done = self._fetch(remote, to_fetch)
                    deepen = None
                if done.returncode != 0 and len(to_fetch) > 1:
                    # One sha the server refuses fails the whole fetch, so
                    # ask again one at a time to know which.
                    results = [(sha, self._fetch(remote, [sha], deepen=deepen)) for sha in to_fetch]
                else:
                    results = [(sha, done) for sha in to_fetch]
                held = self.present(remote.git_dir, to_fetch)
                for sha, one in results:
                    if sha in held:
                        continue
                    if one.returncode == 0:
                        failed[sha] = ("error", f"`git fetch {remote.url} {sha}` exited 0 but the commit is still absent")
                    elif any(marker in (one.stderr or "").lower() for marker in _REFUSAL_MARKERS):
                        failed[sha] = ("refused", f"{remote.url} will not serve it: {_message(one)}")
                    else:
                        failed[sha] = ("error", f"`git fetch {remote.url} {sha}` failed: {_message(one)}")
                with self._lock:
                    for sha in to_fetch:
                        if sha in failed:
                            self._unfetchable[(gd, sha)] = failed[sha]
            return failed

    def warm(self, path: Path, shas: Iterable[str], *, scope: str = "durable") -> None:
        """Batch original pinned commit reads; native ancestry owns tip intake.

        Literal local remotes retain their original combined fetch. Errors are
        left for ``judge`` to classify; this is only a batching step. ``scope``
        is the later ``judge_many``'s, so both use one inventory read.
        """
        wanted = list(shas)
        inventory = self.inventory(path, scope=scope)
        main = inventory.get(MAIN_REF) if not inventory.error else None
        if main and github_repository(inventory.url) is None:
            wanted.append(main)
        if wanted and not inventory.error:
            self.ensure(path, wanted)

    # ----------------------------------------------------------- the verdict
    def judge(self, path: Path, sha: str, *, scope: str = "durable") -> Verdict:
        """Is ``sha`` contained in a ref the remote publishes?

        ``scope="durable"``: any head or ``refs/pins/*`` anchor (the reach
        lane's predicate). ``scope="main"``: ``refs/heads/main`` only (the
        cohort's). The exact commit itself is always made readable first.
        Commit-only intake does not promise trees or a complete checkout.
        """
        return self.judge_many(path, [sha], scope=scope)[sha.lower()]

    def judge_many(self, path: Path, shas: Iterable[str], *, scope: str = "durable") -> dict[str, Verdict]:
        """``judge`` for several commits of one store, sharing the remote reads.

        Until 2026-11-13 each (commit, tip) question was one native process,
        asked serially over the remote's whole inventory (main, then every
        refs/pins anchor, then every head) until one contained the commit: a
        pin that was not on main cost one ~45 s read per published ref, and
        the reach row ran for 1h41m on a one-commit docs push. Now every
        commit is asked against main in one batch, and those main does not
        contain are asked against all the other refs in one more
        (``_ancestry``: remembered and locally proved answers are not asked at
        all), up to ``ANCESTRY_BATCH`` questions per read. The predicate is unchanged; the verdicts are memoized for the
        run, since the inventory they rest on is read once per run.
        """
        wanted = [s.lower() for s in dict.fromkeys(shas)]
        verdicts: dict[str, Verdict] = {}
        with self._lock:
            for sha in wanted:
                cached = self._verdicts.get((str(path), sha, scope))
                if cached is not None:
                    verdicts[sha] = cached
        todo = [sha for sha in wanted if sha not in verdicts]
        if todo:
            found = self._judge_many(path, todo, scope)
            with self._lock:
                for sha, verdict in found.items():
                    self._verdicts[(str(path), sha, scope)] = verdict
            verdicts.update(found)
        return verdicts

    def _judge_many(self, path: Path, shas: Sequence[str], scope: str) -> dict[str, Verdict]:
        remote = self.remote(path)
        inventory = self.inventory(path, scope=scope)
        if inventory.error:
            return {sha: Verdict(UNJUDGED, detail=f"the remote could not be read: {inventory.error}") for sha in shas}
        tips = [(ref, tip) for ref, tip in inventory.refs if scope == "durable" or ref == MAIN_REF]
        if scope == "main" and not tips:
            return {sha: Verdict(
                NO_MAIN,
                detail=f"{inventory.url} publishes no {MAIN_REF} ({inventory.advertised_heads} head(s) read)",
            ) for sha in shas}
        native = github_repository(remote.url) is not None
        advertised = {tip for _, tip in tips}
        verdicts: dict[str, Verdict] = {}
        missing = self.ensure(path, shas)
        open_shas: list[str] = []
        for sha in shas:
            absent = missing.get(sha)
            if absent is not None:
                kind, why = absent
                if kind == "refused" and sha not in advertised:
                    verdicts[sha] = Verdict(ABSENT, detail=why)
                else:
                    verdicts[sha] = Verdict(UNJUDGED, detail=f"the commit could not be fetched: {why}")
                continue
            exact = tuple(ref for ref, tip in tips if tip == sha)
            if exact:
                verdicts[sha] = Verdict(CONTAINED, refs=exact)
                continue
            open_shas.append(sha)
        if not open_shas:
            return verdicts
        assert remote.git_dir is not None
        unread: dict[str, list[tuple[str, str]]] = {sha: [] for sha in open_shas}
        # main alone first, then the other refs in inventory order, as many
        # per group as one native read carries for the pins still open, so a
        # pin an early ref contains is not asked of the later ones.
        position = 0
        while position < len(tips) and open_shas:
            width = 1 if position == 0 else max(1, ANCESTRY_BATCH // len(open_shas))
            group = tips[position:position + width]
            position += width
            failed = {} if native else self.ensure(path, [tip for _, tip in group])
            answers = self._ancestry(
                remote, [(sha, tip) for sha in open_shas for _, tip in group if tip not in failed])
            still: list[str] = []
            for sha in open_shas:
                hit = next((ref for ref, tip in group
                            if tip not in failed and answers[(sha, tip)][0]), None)
                if hit is not None:
                    verdicts[sha] = Verdict(CONTAINED, refs=(hit,))
                    continue
                for ref, tip in group:
                    if tip in failed:
                        unread[sha].append((ref, failed[tip][1]))
                    elif answers[(sha, tip)][0] is None:
                        unread[sha].append((ref, answers[(sha, tip)][1]))
                still.append(sha)
            open_shas = still
        for sha in open_shas:
            if unread[sha]:
                ref, why = unread[sha][0]
                verdicts[sha] = Verdict(
                    UNJUDGED,
                    detail=(
                        f"{len(unread[sha])} of the {len(tips)} ref(s) {inventory.url} publishes could not be "
                        f"read here (first: {ref}: {why}), so containment cannot be ruled out"
                    ),
                )
            elif scope == "main":
                verdicts[sha] = Verdict(
                    NOT_CONTAINED, detail=f"not an ancestor of {inventory.url} {MAIN_REF} {tips[0][1][:12]}")
            else:
                verdicts[sha] = Verdict(
                    NOT_CONTAINED,
                    detail=(
                        f"{inventory.url} publishes {inventory.heads} branch(es) and {inventory.pins} "
                        f"refs/pins/* anchor(s), read this run; none contains it, and there is no "
                        f"{PINS}{sha}"
                    ),
                )
        return verdicts
