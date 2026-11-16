"""Internal POSIX session owner for one remote-data command.

Process groups are anchored by unreaped helper children before signaling.
Joining a group atomically requires membership in this session, so stale or
foreign census rows cannot grant kill authority. Descendants that deliberately
create a new session are outside this boundary.
"""
import os
import select
import signal
import struct
import subprocess
import sys
import time


def session_members(session):
    census = subprocess.run(["/bin/ps", "-axo", "pid=,pgid=,stat="], capture_output=True,
                            text=True, timeout=1)
    if census.returncode:
        raise RuntimeError("cannot census owned operation session")
    result = []
    for line in census.stdout.splitlines():
        words = line.split()
        if len(words) != 3 or not words[0].isdigit() or not words[1].isdigit():
            raise RuntimeError("malformed process census")
        pid, group = map(int, words[:2])
        try:
            if os.getsid(pid) == session:
                result.append((pid, group, words[2]))
        except ProcessLookupError:
            pass
    return result


def anchor_group(group):
    """Return our child pin, or None if this group cannot be safely joined."""
    read, write = os.pipe()
    child = os.fork()
    if child == 0:
        os.close(read)
        try:
            for sig in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP, signal.SIGQUIT):
                signal.signal(sig, signal.SIG_IGN)
            os.setpgid(0, group)  # atomic kernel same-session check
            os.write(write, b"1")
            os.close(write)
            # Do not retain command/custody/resource descriptors in a pin.
            os.closerange(3, int(os.sysconf("SC_OPEN_MAX")))
            while True:
                signal.pause()
        except BaseException:
            try:
                os.write(write, b"0")
            except OSError:
                pass
            os._exit(1)
    os.close(write)
    try:
        if select.select([read], [], [], 1)[0] and os.read(read, 1) == b"1":
            return child
    finally:
        os.close(read)
    try:
        os.kill(child, signal.SIGKILL)
    except ProcessLookupError:
        pass
    os.waitpid(child, 0)
    return None


def stop_session(session, native, anchors, grace, kill_grace):
    """Keep every acquired group pin through cleanup, including census errors.

    A transient observation failure can recover within the same stop budget.
    Persistent failure refuses the result after stopping all known groups;
    it cannot establish that undiscovered descendants stopped. Reaped pins
    are withdrawn in the caller's table: their numeric IDs no longer own a
    group and must not authorize a subsequent cleanup signal.
    """
    observation_error = None

    def discover():
        nonlocal observation_error
        try:
            members = session_members(session)
            for _pid, group, _state in members:
                if group != session and group not in anchors:
                    pin = anchor_group(group)
                    if pin is not None:
                        anchors[group] = pin
            observation_error = None
            return members
        except (OSError, RuntimeError, subprocess.TimeoutExpired) as error:
            observation_error = error
            return None

    def send(sig):
        errors = []
        # Only unreaped pins retain a group's identity. The native leader
        # also owns its group until our final wait, even if pinning failed.
        groups = {group for group, pin in anchors.items() if pin is not None}
        if native.returncode is None:
            groups.add(native.pid)
        for group in groups:
            try:
                owner_logic().signal_owned_group(group, sig)
            except OSError as error:
                errors.append(error)
        if errors:
            raise errors[0]

    def live(members):
        return [entry for entry in members if entry[0] not in {*anchors.values(), session}
                and not entry[2].startswith("Z")]

    try:
        deadline = time.monotonic() + grace
        # Stop already-owned work before asking for any more observations.
        send(signal.SIGTERM)
        while True:
            members = discover()
            send(signal.SIGTERM)
            if members is not None and not live(members):
                break
            if time.monotonic() >= deadline:
                break
            time.sleep(0.02)
        deadline = time.monotonic() + kill_grace
        while True:
            send(signal.SIGKILL)
            members = discover()
            if members is not None and not live(members):
                break
            if time.monotonic() >= deadline:
                raise RuntimeError("cannot confirm owned session stopped after kill") from observation_error
            time.sleep(0.02)
    finally:
        # Observation or signaling failure must not bypass known-child cleanup.
        # Signal every held group before reaping any identity that pins it.
        try:
            send(signal.SIGKILL)
        finally:
            try:
                native.kill()
                status = native.wait(timeout=kill_grace)
            finally:
                for group, pin in anchors.items():
                    if pin is None:
                        continue
                    try:
                        os.kill(pin, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    os.waitpid(pin, 0)
                    anchors[group] = None
    return status


def execute(command, custody, result, timeout, grace, kill_grace):
    session = os.getpid()
    if os.getsid(0) != session or os.getpgrp() != session:
        raise RuntimeError("remote helper does not own its session")
    pending = [False]
    def stop(_signum, _frame):
        pending[0] = True
    for sig in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP, signal.SIGQUIT):
        signal.signal(sig, stop)
    resources = owner_logic().resource_fds(dict(os.environ))
    session_members(session)  # refuse before launch when custody cannot be observed
    native = subprocess.Popen(command, preexec_fn=lambda: os.setpgid(0, 0), pass_fds=resources)
    anchors = {}
    deadline = time.monotonic() + timeout
    expired = False
    try:
        # Hold the native group's leader even when it exits before registration.
        pin = anchor_group(native.pid)
        if pin is not None:
            anchors[native.pid] = pin
        while True:
            # waitid/kqueue must not reap the leader before session cleanup.
            if owned_exit(native.pid):
                break
            if pending[0] or time.monotonic() >= deadline:
                expired = True
                break
            if select.select([custody], [], [], 0.02)[0] and not os.read(custody, 1):
                expired = True
                break
    finally:
        status = stop_session(session, native, anchors, grace, kill_grace)
    os.write(result, struct.pack("!i?", status, expired))


def owner_logic():
    # Exact sibling source: no caller Python path chooses ownership logic.
    import importlib.util
    from pathlib import Path
    global _owner
    if "_owner" not in globals():
        spec = importlib.util.spec_from_file_location("_operation_owner", Path(__file__).with_name("landing_targo.py"))
        _owner = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(_owner)
    return _owner


def owned_exit(pid):
    return owner_logic().wait_child_exit(pid, nohang=True)


def main():
    split = sys.argv.index("--")
    custody, result = map(int, sys.argv[1:3])
    timeout, grace, kill_grace = map(float, sys.argv[3:6])
    try:
        execute(sys.argv[split + 1:], custody, result, timeout, grace, kill_grace)
    except BaseException as error:
        sys.stderr.write(f"owned remote operation failed: {type(error).__name__}: {error}\n")
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
