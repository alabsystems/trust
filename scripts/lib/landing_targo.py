"""One ordinary push runs the selected full Targo suite, never a cached PASS.

The pinned hook records its child exit in shell-local state and refuses its
final exit unless that mandatory child succeeded. No child can supply a
completion receipt or modify that state. Git's separate porcelain output must
also attest an actual update: 'up to date' did not execute a hook.
"""
from __future__ import annotations

import hashlib
import contextlib
import errno
import json
import os
from pathlib import Path
import re
import select
import shutil
import signal
import subprocess
import sys
import threading
import time
from typing import Dict, Optional, Sequence, Set, Tuple

HEAD_ENV = "TRUST_LAND_TARGO_HEAD"
DEST_ENV = "TRUST_LAND_TARGO_DESTINATION"
INPUT_ENV = "TRUST_LAND_TARGO_ENVIRONMENT"
# The gate keys the deferred leg answers for: the suite's FAIL or NOT JUDGED
# is recorded under them, never a PASS (review of EW-21). A forged key can only
# add a row that serves nothing.
KEYS_ENV = "TRUST_LAND_TARGO_KEYS"
PROTOCOL_ENV = (HEAD_ENV, DEST_ENV, INPUT_ENV, KEYS_ENV)
# The three words after the verb are scripts/check_crates_tests_scoped.py's
# MEMBER_FEATURE_SCOPE (land_gate_test holds them equal): targo-trust's tests
# build with the features targo-trust selects, never the workspace's union,
# whatever a wrapper or config says (TARGO-MEMBER-FEATURE-SCOPE-1; aterm's
# atpkg shim widened this graph from 410 units to 590, 38 of them compiler).
COMMAND = ["targo", "--unverified", "test", "-Zfeature-unification",
           "--config", 'resolver.feature-unification="selected"', "--manifest-path",
           "targo-trust/Cargo.toml", "--locked", "--no-fail-fast",
           "--require-test-bin", "targo-trust"]
# Exact reviewed implementations, not marker strings or mutable receipts.
HOOK_SHA256 = "82422b4b0346db45fc47444f2dfa3efd331c90b0b7cfe5252cb0ec4e1202848c"
RUNNER_SHA256 = "6a051954b6cbe10998e7d44a98c708a4846f61130aa834a0e5f4bb167d4117d6"
SUMMARY = re.compile(r"^test result: ok\. (\d+) passed; (\d+) failed; (\d+) ignored;")
STOP_GRACE_S = 10

# GATE-TARGO-CAPABILITY-1. A `targo ...` command runs whatever targo its
# environment's PATH names, and a host's targo can be older than the command:
# atpkg's 0.12.0+g29ebb403d (2026-10-28) refuses COMMAND's
# `--require-test-bin` ("unexpected argument", exit 1) before building
# anything, and that exit was graded the change's FAIL. capability_gap asks
# that same targo, in the command's own environment and directory, to parse
# the command: the probe is the command itself with `--help` in place of
# whatever follows `--` (the test harness's arguments, not targo's). Targo's
# parser rejects an argument it does not know when it reaches it and prints
# its help (exit 0) only after every earlier argument parsed, so exit 0 is
# the capability itself. Nothing is built or run. Clap does not judge `-Z`
# values or `--config` keys; every targo measured (0.12.0 and 0.13.0) lists
# the `-Z` flags these commands pass (feature-unification, unstable-options).
CAPABILITY_PROBE_TIMEOUT_S = 120
REFUSED_ARGUMENT = re.compile(r"unexpected argument '([^']+)' found")
# Where an option first appeared, named in the reason only: the probe, never
# this table, decides.
OPTION_ORIGIN = {"--require-test-bin": "9f709bc793"}


def capability_probe(command: Sequence[str]) -> list:
    """`command` up to any `--`, then `--help`."""
    command = list(command)
    cut = command.index("--") if "--" in command else len(command)
    return [*command[:cut], "--help"]


def targo_version(exe: str, env: Dict[str, str], cwd) -> str:
    """`exe --version`'s first line, or why it has none."""
    try:
        proc = subprocess.run([exe, "--version"], cwd=cwd, env=env, stdin=subprocess.DEVNULL,
                              capture_output=True, text=True, errors="replace",
                              timeout=CAPABILITY_PROBE_TIMEOUT_S)
    except (OSError, subprocess.SubprocessError) as exc:
        return f"version unreadable: {exc}"
    line = (proc.stdout.strip().splitlines() or [""])[0].strip()
    if proc.returncode or not line:
        return f"version unreadable: `--version` exit {proc.returncode}"
    return line[:200]


def capability_gap(command: Sequence[str], env: Dict[str, str], cwd) -> Optional[str]:
    """Why the targo `command` would run (its first word resolved through
    `env`'s PATH, as the child resolves it) cannot run `command`, or None
    when it parses every argument. Each reason names the missing capability,
    that targo's path and its version, and says no test ran: the caller files
    it NOT JUDGED, never a FAIL of the change and never a PASS. Only a command
    whose first word is `targo` is asked."""
    command = list(command)
    if not command or command[0] != "targo":
        return None
    exe = shutil.which("targo", path=env.get("PATH"))
    if exe is None:
        return f"no `targo` on the command's PATH, so `{' '.join(command)}` cannot run here; no test ran"
    probe = capability_probe(command)
    spelled = " ".join(probe)
    try:
        proc = subprocess.run([exe, *probe[1:]], cwd=cwd, env=env, stdin=subprocess.DEVNULL,
                              capture_output=True, text=True, errors="replace",
                              timeout=CAPABILITY_PROBE_TIMEOUT_S)
    except (OSError, subprocess.SubprocessError) as exc:
        return (f"the command's targo {exe} ({targo_version(exe, env, cwd)}) could not be asked "
                f"`{spelled}`: {exc}; no test ran")
    if proc.returncode == 0:
        return None
    version = targo_version(exe, env, cwd)
    said = ((proc.stderr or "").strip() or (proc.stdout or "").strip()).splitlines()
    first = said[0].strip()[:200] if said else "no output"
    refused = REFUSED_ARGUMENT.search(proc.stderr or "") or REFUSED_ARGUMENT.search(proc.stdout or "")
    if refused:
        argument = refused.group(1)
        origin = f"; {argument} landed in {OPTION_ORIGIN[argument]}" if argument in OPTION_ORIGIN else ""
        return (f"this host's targo lacks `{argument}`, which the command passes: {exe} ({version}) refuses it "
                f"(`{spelled}`: exit {proc.returncode}, {first}{origin}). That targo would refuse the command "
                "before running a test, a gap in the host's toolchain that no change to this tree fixes; no test "
                "ran. Put a targo that accepts it first on PATH")
    return (f"the command's targo {exe} ({version}) did not accept the command (`{spelled}`: exit "
            f"{proc.returncode}, {first}); no test ran")


def hook_environment(environment):
    """Pin Bash startup semantics without changing the actual test inputs.

    BASH_ENV can exit before the reviewed hook runs; SHELLOPTS=noexec can
    parse it without executing it; imported functions can replace commands.
    The full, original canonical environment travels separately to Targo.
    """
    startup = {"BASH_ENV", "ENV", "SHELLOPTS", "BASHOPTS"}
    return {k: v for k, v in environment.items()
            if k not in startup and not k.startswith("BASH_FUNC_")}


def signal_owned_group(pid, sig):
    try:
        os.killpg(pid, sig)
    except ProcessLookupError:
        pass
    except PermissionError as exc:
        # Darwin can report EPERM for a group with only unreaped zombies.
        # Accept that case only after observing every remaining member as Z;
        # a failed census or any live member keeps the refusal.
        if exc.errno != errno.EPERM:
            raise
        census = subprocess.run(["ps", "-axo", "pgid=,stat="], capture_output=True, text=True)
        if census.returncode:
            raise
        if census.stderr:
            raise
        states = []
        for row in census.stdout.splitlines():
            fields = row.split()
            # Do not filter malformed rows: one could hide a live member of
            # the owned group beside a valid zombie row. ps can report '?'
            # for an unrelated group's unknown run state; it is valid syntax,
            # but an unknown owned-group state still cannot count as a zombie.
            if (len(fields) != 2 or not re.fullmatch(r"[0-9]+", fields[0])
                    or not re.fullmatch(r"[?DIRSTtUWXZP][+<>AELNSsVWXl]*", fields[1])):
                raise
            if int(fields[0]) == pid:
                states.append(fields[1])
        if not states or any(not state.startswith("Z") for state in states):
            raise


def exit_observation_available():
    """Can this host observe a direct child's exit without reaping it?"""
    return (all(hasattr(os, name) for name in
                ("waitid", "P_PID", "WEXITED", "WNOWAIT", "WNOHANG"))
            or all(hasattr(select, name) for name in
                   ("kqueue", "kevent", "KQ_FILTER_PROC", "KQ_EV_ADD",
                    "KQ_EV_ONESHOT", "KQ_NOTE_EXIT", "KQ_EV_ERROR")))


def wait_child_exit(pid, *, nohang=False):
    """Observe without reaping; optionally return False while still running.

    The caller remains the only reaper, so the process-group identity is held
    until its final signal on every exit, including a successful leader exit.
    """
    if all(hasattr(os, name) for name in
           ("waitid", "P_PID", "WEXITED", "WNOWAIT", "WNOHANG")):
        flags = os.WEXITED | os.WNOWAIT | (os.WNOHANG if nohang else 0)
        return os.waitid(os.P_PID, pid, flags) is not None
    if all(hasattr(select, name) for name in
           ("kqueue", "kevent", "KQ_FILTER_PROC", "KQ_EV_ADD",
            "KQ_EV_ONESHOT", "KQ_NOTE_EXIT", "KQ_EV_ERROR")):
        events = select.kqueue()
        try:
            try:
                ready = events.control([select.kevent(
                    pid, filter=select.KQ_FILTER_PROC,
                    flags=select.KQ_EV_ADD | select.KQ_EV_ONESHOT,
                    fflags=select.KQ_NOTE_EXIT)], 1, 0 if nohang else None)
            except ProcessLookupError:
                return True  # exited before registration; still unreaped
            if not ready and nohang:
                return False
            if ready and ready[0].flags & select.KQ_EV_ERROR:
                if ready[0].data == errno.ESRCH:
                    return True
                raise OSError(ready[0].data, "cannot observe owned child exit")
            if (len(ready) != 1 or ready[0].ident != pid
                    or not ready[0].fflags & select.KQ_NOTE_EXIT):
                raise RuntimeError("owned child exit notification was not established")
        finally:
            events.close()
        return True
    raise RuntimeError("landing requires nonreaping child exit observation")


class OwnedChild:
    """A narrow Popen facade: wait/communicate cannot release group custody."""

    def __init__(self, process, phase, pending):
        self.process, self.phase, self.pending = process, phase, pending
        self.reaped = False
        self.exited = threading.Event()
        self.wait_error = None
        self.observer = threading.Thread(target=self.observe_exit, daemon=True)

    def observe_exit(self):
        try:
            wait_child_exit(self.pid)
        except BaseException as exc:
            self.wait_error = exc
        finally:
            # A descendant may hold stdout open after its leader exits. Stop
            # the owned group concurrently with draining that pipe, while the
            # unreaped leader still protects the group's numeric identity.
            try:
                signal_owned_group(self.pid, signal.SIGKILL)
            except BaseException as exc:
                self.wait_error = self.wait_error or exc
            self.exited.set()

    @property
    def pid(self):
        return self.process.pid

    @property
    def stdout(self):
        return self.process.stdout

    @property
    def returncode(self):
        return self.process.returncode

    def reap_group(self):
        self.phase[0] = "reaping"
        try:
            signal_owned_group(self.pid, signal.SIGKILL)
            if self.observer.ident is not None:
                self.observer.join()
            self.process.wait()
            self.reaped = True
        finally:
            self.phase[0] = "running"
        if self.pending:
            raise KeyboardInterrupt(f"signal {self.pending[0]}")
        if self.wait_error:
            raise RuntimeError(f"cannot observe owned child exit: {self.wait_error}") from self.wait_error

    def wait(self):
        if not self.reaped:
            self.exited.wait()
            self.reap_group()
        return self.returncode

    def communicate(self):
        # Popen.communicate invokes Popen.wait, which can reap a leader inside
        # its KeyboardInterrupt handler. Never call it before group cleanup.
        output = self.stdout.read() if self.stdout is not None else None
        self.wait()
        return output, None


@contextlib.contextmanager
def owned_process(command, **kwargs):
    """Defer signals across launch and reap only this owned process group.

    On an interrupted run the leader remains unreaped during the grace
    interval, so its PID cannot be reused before the final group signal.
    """
    pending = []
    phase = ["launching"]
    process = None

    def stop(signum, frame):
        if phase[0] in ("launching", "reaping"):
            pending.append(signum)
        else:
            raise KeyboardInterrupt(f"signal {signum}")

    old = {sig: signal.signal(sig, stop) for sig in
           (signal.SIGINT, signal.SIGTERM, signal.SIGHUP, signal.SIGQUIT)}
    try:
        process = OwnedChild(subprocess.Popen(command, start_new_session=True, **kwargs), phase, pending)
        process.observer.start()
        phase[0] = "running"
        if pending:
            raise KeyboardInterrupt(f"signal {pending[0]}")
        yield process
    finally:
        # Repeated signals must not interrupt owned-child cleanup.
        for sig in old:
            signal.signal(sig, signal.SIG_IGN)
        try:
            if process is not None and not process.reaped:
                signal_owned_group(process.pid, signal.SIGTERM)
                time.sleep(STOP_GRACE_S)
                process.reap_group()
            if process is not None and process.stdout is not None:
                process.stdout.close()
        finally:
            for sig, handler in old.items():
                signal.signal(sig, handler)


def protocol_problem(root):
    for name, expected in (("scripts/hooks/pre-push", HOOK_SHA256),
                           ("scripts/check_targo_trust_unit_tests.sh", RUNNER_SHA256)):
        try:
            actual = hashlib.sha256((Path(root) / name).read_bytes()).hexdigest()
        except OSError as exc:
            return f"cannot read live landing hook implementation: {exc}"
        if actual != expected:
            return f"{name} differs from the reviewed landing implementation"
    return None


def context_problem(root, check):
    head = os.environ.get(HEAD_ENV, "")
    destination = os.environ.get(DEST_ENV, "")
    if not re.fullmatch(r"[0-9a-f]{40,64}", head) or not re.fullmatch(r"[0-9a-f]{40,64}", destination):
        return "missing exact landing HEAD/destination"
    refs = os.environ.get("TRUST_PUSHED_REFS", "").split()
    if len(refs) != 4 or refs[1:] != [head, "refs/heads/main", destination]:
        return "actual pushed refs differ from the planned landing"
    return check(head)


def valid_key(key):
    return isinstance(key, str) and re.fullmatch(r"[0-9a-f]{64}", key) is not None


def gate_keys():
    """The keys the gate handed this run (KEYS_ENV), each a key's exact form."""
    try:
        keys = json.loads(os.environ.get(KEYS_ENV, "[]"))
    except ValueError:
        return []
    return [k for k in keys if valid_key(k)] if isinstance(keys, list) else []


def judgement(code, summaries, skipped, failed_line, problem):
    """(verdict, why) as the gate judges this leg when it runs it (land_gate's
    cmd_run): None for a pass. Exit 2 and a source change are NOT JUDGED."""
    if problem:
        return "NOT JUDGED", f"the source changed: {problem}"
    if code == 2:
        return "NOT JUDGED", "exit 2"
    if code or failed_line:
        return "FAIL", f"exit {code}" + ("; a test result FAILED" if failed_line else "")
    if skipped or not summaries or any(p == 0 or f != 0 for p, f, _ in summaries):
        return "NOT JUDGED", "SKIP or empty execution"
    return None


def run_targo(root, check, record=None):
    """Run the fixed full command with the canonical leg's exact environment.
    `record(keys, verdict, why)` files an outcome that is not a PASS under the
    gate's keys for this leg (KEYS_ENV). A targo that cannot parse the command
    (capability_gap) runs nothing: NOT JUDGED, exit 1."""
    problem = context_problem(root, check)
    if problem:
        raise RuntimeError(problem)
    try:
        env = json.loads(os.environ[INPUT_ENV])
    except (KeyError, ValueError) as exc:
        raise RuntimeError("missing canonical Targo environment") from exc
    if (not isinstance(env, dict) or not all(isinstance(k, str) and isinstance(v, str)
                                            for k, v in env.items())
            or any(k in env for k in PROTOCOL_ENV)):
        raise RuntimeError("invalid canonical Targo environment")
    print("landing Targo suite: " + " ".join(COMMAND), flush=True)
    # The gate asked the same question before it deferred the suite here
    # (land_gate.targo_unready); this push's own environment is asked again,
    # since a targo the hook cannot use must not be filed as the change's FAIL.
    gap = capability_gap(COMMAND, env, root)
    if gap:
        if record is not None:
            record(gate_keys(), "NOT JUDGED", gap)
        print(f"landing Targo suite: NOT JUDGED ({gap})", flush=True)
        return 1
    summaries, skipped, failed_line = [], False, False
    with owned_process(COMMAND, cwd=root, env=env, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, text=True, errors="replace", close_fds=True) as proc:
        assert proc.stdout is not None
        for line in proc.stdout:
            print(line, end="", flush=True)
            match = SUMMARY.match(line)
            if match:
                summaries.append(tuple(map(int, match.groups())))
            if re.match(r"^\s*SKIPPED:", line):
                skipped = True
            if line.startswith("test result: FAILED."):
                failed_line = True
        code = proc.wait()
    problem = context_problem(root, check)
    judged = judgement(code, summaries, skipped, failed_line, problem)
    if judged is not None:
        if record is not None:
            record(gate_keys(), *judged)
        print(f"landing Targo suite: {judged[0]} ({judged[1]})", flush=True)
        return 1
    print("landing Targo suite: PASS (executed once inside this push)", flush=True)
    return 0


def finish_hook(root, check):
    problem = context_problem(root, check)
    if problem:
        raise RuntimeError(problem)
    return 0


def accepted_update(output):
    """Require exactly one porcelain update, never an up-to-date row.

    Git may also forward hook stdout here. A forged status line beside the
    real Git status makes two rows and refuses; it cannot replace that row.
    """
    rows = [line.split("\t") for line in output.splitlines()
            if "\t" in line and line.split("\t", 1)[0] in (" ", "*", "=", "!", "+", "-")]
    return (len(rows) == 1 and len(rows[0]) == 3 and rows[0][0] in (" ", "*")
            and rows[0][1] == "HEAD:refs/heads/main")


class Coordinator:
    def __init__(self, head, destination, environment, check, remote="origin", keys=()):
        self.head, self.destination, self.remote = head, destination, remote
        self.keys = [k for k in keys if valid_key(k)]
        self.environment = ({k: v for k, v in environment.items()
                             if k not in PROTOCOL_ENV}
                            if environment is not None else None)
        self.check = check
        self.state, self.error, self.output = "pending", None, ""

    def push(self, root, log, push_environment):
        problem = self.check(self.head) or protocol_problem(root)
        if problem:
            self.error = problem
            return 2
        env = {k: v for k, v in hook_environment(push_environment).items()
               if k not in PROTOCOL_ENV}
        if self.environment is not None:
            env.update({HEAD_ENV: self.head, DEST_ENV: self.destination,
                        INPUT_ENV: json.dumps(self.environment, separators=(",", ":")),
                        KEYS_ENV: json.dumps(list(self.keys))})
        command = ["git", "-c", f"core.hooksPath={Path(root) / 'scripts/hooks'}", "push",
                   "--porcelain", self.remote, "HEAD:refs/heads/main"]
        # No printed PASS token authorizes anything. The exact reviewed hook
        # gates Git's exit; porcelain additionally rejects an up-to-date race.
        with owned_process(command, cwd=root, env=env, stdout=subprocess.PIPE,
                           stderr=log, text=True, errors="replace") as proc:
            self.output = proc.communicate()[0]
        log.write(self.output)
        log.flush()
        print(self.output, end="", flush=True)
        if proc.returncode:
            self.error = f"ordinary push failed (exit {proc.returncode})"
            return proc.returncode
        if not accepted_update(self.output):
            self.error = "Git did not report an accepted update; no deferred execution is claimed"
            return 2
        self.state = "complete"
        return 0

    def receipt(self):
        return {"mode": "ordinary push mandatory suite" if self.environment is not None else "ordinary push",
                "head": self.head,
                "destination": self.destination, "remote": self.remote, "command": COMMAND,
                "state": self.state, "error": self.error, "git_porcelain": self.output,
                "environment_sha256": hashlib.sha256(json.dumps(self.environment, sort_keys=True).encode()).hexdigest()}


def resource_fds(env: Dict[str, str]) -> Tuple[int, ...]:
    """Preserve only advertised live transport descriptions, never grant authority.

    The native owners still authenticate GNU/SDK/CPU custody. A Python launch
    must not silently close its caller's actual descriptions or pass unrelated
    descriptors. Malformed or closed locators refuse before running a row.
    """
    descriptors: Set[int] = set()

    def add(word: str, name: str) -> None:
        if not re.fullmatch(r"[1-9][0-9]{0,9}", word) or int(word) < 3:
            raise RuntimeError(f"row custody: malformed {name} descriptor")
        descriptor = int(word)
        try:
            os.fstat(descriptor)
        except (OSError, OverflowError) as error:
            raise RuntimeError(f"row custody: {name} descriptor is not live") from error
        descriptors.add(descriptor)

    for name in ("ATERM_SDK_LEASE_V3", "ATERM_WORKLOAD_HOST_STORE_FD_V1",
                 "TRUST_CPU_IMPLICIT_FD"):
        if name in env:
            add(env[name], name)
    for name in ("ATERM_WORKLOAD_CPU_FDS_V1", "BUILD_SLOT_FENCE_FDS"):
        if name in env:
            words = env[name].split(",")
            if not 1 <= len(words) <= 128 or len(set(words)) != len(words):
                raise RuntimeError(f"row custody: malformed {name} descriptor set")
            for word in words:
                add(word, name)
    # Match vendor/jobserver's environment and find_jobserver_auth precedence:
    # first PRESENT variable, last auth substring, otherwise last legacy fds;
    # the value stops at a literal space (not shell/general whitespace).
    # Never inspect or resurrect obsolete/lower-priority pipe advertisements.
    for name in ("CARGO_MAKEFLAGS", "MAKEFLAGS", "MFLAGS"):
        if name not in env:
            continue
        flags = env[name]
        try:
            flags.encode("utf-8")
        except UnicodeError as error:
            raise RuntimeError(f"row custody: malformed {name} jobserver flags") from error
        value = None
        for option in ("--jobserver-auth=", "--jobserver-fds="):
            if option in flags:
                value = flags.rsplit(option, 1)[1].split(" ", 1)[0]
                break
        if value is None:
            break
        # Named FIFO and native handoff authentication stay with the native
        # importer. A path/advertisement never becomes numeric FD authority.
        if value.startswith("fifo:") and value != "fifo:":
            break
        pair = re.fullmatch(r"([+-]?[0-9]+),([+-]?[0-9]+)", value)
        if pair is None:
            raise RuntimeError(f"row custody: malformed {name} jobserver descriptor pair")
        numbers = []
        for word in pair.groups():
            # Rust parses signed i32 values, including + and leading zeroes.
            # Bound normalized digits before int(), including enormous inputs.
            digits = word.lstrip("+-").lstrip("0") or "0"
            if len(digits) > 10:
                raise RuntimeError(f"row custody: malformed {name} jobserver descriptor")
            number = int(digits) * (-1 if word.startswith("-") else 1)
            if not -(1 << 31) <= number < (1 << 31):
                raise RuntimeError(f"row custody: malformed {name} jobserver descriptor")
            numbers.append(number)
        # Negative descriptors disable numeric transport; native import policy
        # still decides whether that advertisement is allowed for its context.
        if all(number >= 0 for number in numbers):
            for number in numbers:
                add(str(number), name)
        break
    return tuple(sorted(descriptors))
