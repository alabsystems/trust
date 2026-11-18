"""Original native tracked-input reader; every result is a fresh observation.

Package admission follows native_serial's known-local atpkg policy. Source IDs
and HMACs bind compatibility/messages, never authenticate an arbitrary program.
The native handler additionally retains HeldProgram/HeldExecutingProgram's
supported current-code custody. Their single-owner/no concurrent same-UID name
writer and system-runtime TCB boundaries remain explicit; no FD freezes code.
"""
from __future__ import annotations

import base64
import hashlib
import hmac
import json
import os
from pathlib import Path
import re
import select
import shutil
import stat
import subprocess
import tempfile
import time

import landing_targo

SCHEMA = "trust-tracked-inputs-v1"
POLICY = "held-static-closure/current-code-macos-arm64-v1"
MAX_FRAME = 32 * 1024 * 1024
MAX_REPLY = 16 * 1024 * 1024
MAX_ITEMS = 4096
NATIVE_SOURCE = "src/tools/targo/crates/targo-core/src/ops/checkout_inputs/mod.rs"
_RETAINED_FAILURES = []  # unknown retirement retains its original handles; never reused


# The native reader's working directory: the filesystem root, inside no checkout.
READER_CWD = "/"


class Unavailable(RuntimeError):
    """Discard every native observation in the current pass; run the original."""


class Corrupt(RuntimeError):
    """A protocol refusal is never an observation or an accepted fallback."""


def _key(info):
    return (info.st_dev, info.st_ino, info.st_mode, info.st_size, info.st_mtime_ns, info.st_ctime_ns)


def _digest(stream):
    stream.seek(0)
    digest = hashlib.sha256()
    for chunk in iter(lambda: stream.read(1024 * 1024), b""):
        digest.update(chunk)
    return digest.hexdigest()


def _object(pairs):
    result = {}
    for name, value in pairs:
        if name in result:
            raise Corrupt("duplicate native reader response field")
        result[name] = value
    return result


def _json(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("ascii")


def _path(path):
    return base64.b64encode(os.fsencode(path)).decode("ascii")


def physical_problem(failure, item, repo, revision, env, original):
    """Keep the original observed refusal, even if somebody repairs it now.

    The sole exception uses the captured regular-file digest and original
    physical key, never a new physical digest that could erase the refusal.
    """
    relative, _mode, oid, label = item
    kind = failure["kind"]
    messages = {
        "symlink-type": f"tracked inputs changed: symlink type differs at {label!r}",
        "regular-type": f"tracked inputs changed: regular-file type differs at {label!r}",
        "executable-mode": f"tracked inputs changed: executable mode differs at {label!r}",
        "opening-change": f"tracked input changed while opening {label!r}",
        "reading-change": f"tracked input changed while reading {label!r}",
        "inspection-change": f"tracked input changed during inspection at {label!r}",
        "parent-escape": f"cannot inspect physical tracked input {label!r} (tracked parent escapes repository)",
        "root-change": f"cannot inspect physical tracked input {label!r} (native repository root changed)",
        "inspect": f"cannot inspect physical tracked input {label!r} (native inspection refused)",
        "link-bytes": f"tracked inputs changed: raw bytes differ from the committed blob at {label!r}",
    }
    if kind != "regular-bytes":
        return messages[kind]
    before = failure["stat"]
    expected = (before["dev"], before["ino"], before["mode"], before["bytes"],
                before["mtime_sec"] * 10**9 + before["mtime_nsec"],
                before["ctime_sec"] * 10**9 + before["ctime_nsec"])
    source = Path(repo) / relative
    try:
        if original.physical_stat_key(source.lstat()) != expected:
            return f"tracked input changed during inspection at {label!r}"
        matched = original.committed_crlf_matches(repo, revision, relative, oid, failure["digest"], env)
        if original.physical_stat_key(source.lstat()) != expected:
            return f"tracked input changed during attribute inspection at {label!r}"
        if matched:
            return None
    except (OSError, RuntimeError, ValueError) as error:
        return f"cannot inspect physical tracked input {label!r} ({error})"
    return f"tracked inputs changed: raw bytes differ from the committed blob at {label!r}"


class OriginalProgram:
    """Retained original image observation, not a writer/SDK/proof capability.

    Production creates this only after managed package admission below. Direct
    engineering tests may exercise their actual newly built original image;
    that does not install it or turn a pathname into managed package authority.
    """
    def __init__(self, root, executable, expected):
        self.root, self.executable = Path(root), Path(executable)
        if (not self.root.is_absolute() or self.root.resolve(strict=True) != self.root
                or not self.executable.is_relative_to(self.root)
                or self.executable.resolve(strict=True) != self.executable
                or not re.fullmatch(r"[0-9a-f]{64}", expected)):
            raise Unavailable("native reader original image is not a canonical selected input")
        self.file = open(os.open(self.executable, os.O_RDONLY | os.O_NOFOLLOW | os.O_CLOEXEC), "rb")
        self.before = os.fstat(self.file.fileno())
        self.expected = expected
        try:
            if not stat.S_ISREG(self.before.st_mode) or not self.before.st_mode & 0o111:
                raise Unavailable("native reader requires an original executable regular image")
            if self.file.read(4) not in (b"\x7fELF", b"\xcf\xfa\xed\xfe", b"\xfe\xed\xfa\xcf",
                                        b"\xca\xfe\xba\xbe", b"\xbe\xba\xfe\xca",
                                        b"\xca\xfe\xba\xbf", b"\xbf\xba\xfe\xca"):
                raise Unavailable("native reader rejects script or no-op wrapper images")
            self.bookend()
        except BaseException:
            self.file.close()
            raise

    def bookend(self):
        if (_key(os.fstat(self.file.fileno())) != _key(self.before)
                or _key(self.executable.lstat()) != _key(self.before)
                or _digest(self.file) != self.expected
                or _key(os.fstat(self.file.fileno())) != _key(self.before)
                or _key(self.executable.lstat()) != _key(self.before)):
            raise Unavailable("native reader original executable bytes/backing changed")

    def close(self):
        self.file.close()


def selected_executable(env):
    """The managed Targo image `managed_program` would admit, by path only,
    from the one cheap package lookup (`atpkg which`): no verification and
    no digest. It names what a remembered "unavailable" answer is keyed on
    (land_gate.native_reader_key); it admits nothing. Unavailable when the
    lookup does not name a ready managed image."""
    activation = Path.home() / ".local/bin/atpkg"
    try:
        done = subprocess.run([str(activation), "which", "--json", "targo"], env=env, stdin=subprocess.DEVNULL,
                              capture_output=True, text=True, timeout=30,
                              pass_fds=landing_targo.resource_fds(env))
        value = json.loads(done.stdout) if done.returncode == 0 else None
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        raise Unavailable(f"native reader lookup failed ({error.__class__.__name__})") from error
    if (not isinstance(value, dict) or value.get("status") != "ready" or value.get("managed") is not True
            or not isinstance(value.get("physical_executable"), str)
            or not os.path.isabs(value["physical_executable"])):
        raise Unavailable("native reader lookup names no ready managed Targo image")
    return Path(value["physical_executable"])


def managed_program(env):
    """The existing offline local package verifier is disclosed trusted input.

    No caller-selected reader path, PATH JSON responder, copied tool role or
    source-hash declaration can substitute for the selected managed original.
    """
    activation = Path.home() / ".local/bin/atpkg"
    if any(value and (name.startswith("DYLD_") or name in ("LD_PRELOAD", "LD_LIBRARY_PATH"))
           for name, value in env.items()):
        raise Unavailable("native reader runtime profile excludes ambient loader overrides")
    routed = shutil.which("atpkg", path=env.get("PATH"))
    if routed is not None and Path(routed).resolve(strict=True) != activation.resolve(strict=True):
        raise Unavailable("native reader refuses PATH shadowing of the local atpkg activation")
    passing = landing_targo.resource_fds(env)

    def image(path):
        path = Path(path).resolve(strict=True)
        with open(path, "rb") as source:
            before = os.fstat(source.fileno())
            if not stat.S_ISREG(before.st_mode) or source.read(4) not in (
                    b"\x7fELF", b"\xcf\xfa\xed\xfe", b"\xfe\xed\xfa\xcf",
                    b"\xca\xfe\xba\xbe", b"\xbe\xba\xfe\xca", b"\xca\xfe\xba\xbf", b"\xbf\xba\xfe\xca"):
                raise Unavailable("native reader package verifier is not a native image")
            digest = _digest(source)
            if _key(os.fstat(source.fileno())) != _key(before) or _key(path.lstat()) != _key(before):
                raise Unavailable("native reader package verifier changed during inspection")
            return str(path), _key(before), digest

    verifier = image(activation)
    def query(arguments):
        done = subprocess.run([str(activation), *arguments], env=env, stdin=subprocess.DEVNULL,
                              capture_output=True, text=True, timeout=120, pass_fds=passing)
        if done.returncode or done.stderr.strip():
            raise Unavailable("native reader managed package admission was refused")
        return done.stdout.strip()

    def lookup():
        value = json.loads(query(["which", "--json", "targo"]), object_pairs_hook=_object)
        if (not isinstance(value, dict) or type(value.get("schema")) is not int or value["schema"] != 1
                or value.get("tool") != "targo" or value.get("status") != "ready"
                or value.get("managed") is not True or value.get("package") != "trust"
                or type(value.get("build")) is not int or value["build"] <= 0 or value.get("shim_env") != {}):
            raise Unavailable("native reader requires the ready managed Trust Targo package")
        provenance = value.get("provenance")
        if (not isinstance(provenance, dict) or provenance.get("index_source") != "alabsystems/aterm"
                or type(provenance.get("index_build")) is not int or provenance["index_build"] <= 0
                or not re.fullmatch(r"[0-9a-f]{64}", str(provenance.get("tree_root", "")))):
            raise Unavailable("native reader package source identity is unavailable")
        return value

    before = lookup()
    root = Path(before["store_root"])
    executable = Path(before["physical_executable"])
    if (root.parent.name != "trust" or root.name not in (str(before["build"]), str(before["build"]) + ".noindex")
            or before.get("physical_root") != str(root) or executable != root / "bin/targo"
            or Path(before["executable"]).resolve(strict=True) != executable):
        raise Unavailable("native reader package does not bind the original selected Targo image")
    # Like managed_serial_executor, select the fixed verifier's actual store
    # image. PATH's Targo may be its native dispatcher or a separate builder;
    # neither authenticates this reader. Hold its byte identity across BOTH
    # package verification queries rather than sampling it only afterward.
    selected = image(executable)
    expected = f"atpkg: trust build {before['build']} OK (matches signed tree_root)"
    if query(["verify", "trust"]) != expected or query(["tree-root", str(root)]) != before["provenance"]["tree_root"]:
        raise Unavailable("native reader package verification did not report the exact original tree")
    result = OriginalProgram(root, executable, selected[2])
    try:
        if (lookup() != before or image(activation) != verifier or image(executable) != selected
                or shutil.which("atpkg",path=env.get("PATH")) != routed
                or (routed is not None and Path(routed).resolve(strict=True) != activation.resolve(strict=True))):
            raise Unavailable("native reader package/verifier changed during admission")
        return result
    except BaseException:
        result.close()
        raise


class Reader:
    """One owned live native process; corruption/loss is terminal, never respawn."""
    def __init__(self, program, reader, jobs, env, owned_group, cancellation, check_cancel):
        self.program = program
        self.reader = reader
        self.jobs = jobs
        self.check_cancel = check_cancel
        self.cancellation = cancellation
        self.owned = None
        self.child = None
        self.errors = None
        self.key = os.urandom(32)
        self.buffer = bytearray()
        self.failed = False
        self.closed = False
        self.stderr_tail = b""
        try:
            self.errors = tempfile.TemporaryFile()
            if (not re.fullmatch(r"[0-9a-f]{64}", reader) or type(jobs) is not int or not 1 <= jobs <= 64
                    or not landing_targo.exit_observation_available()):
                raise Unavailable("native reader profile cannot be established")
            program.bookend()
            # The reader names every root it reads as an absolute path, so it
            # needs no working directory. It runs from READER_CWD, never from
            # the caller's: the build-tree lock counts a targo process whose
            # cwd is inside a tree as that tree's writer, so a reader started
            # from the checkout held it against every x.py leg of the same run.
            self.child = subprocess.Popen([str(program.executable), "source-check", "--tracked-inputs"],
                stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=self.errors, env=env, cwd=READER_CWD,
                start_new_session=True, pass_fds=landing_targo.resource_fds(env), bufsize=0)
            self.owned = owned_group(self.child)
            os.set_blocking(self.child.stdin.fileno(), False)
            os.set_blocking(self.child.stdout.fileno(), False)
            self._send(_json({"schema":SCHEMA, "reader":reader, "key":self.key.hex(),
                "root":_path(program.root), "executable":_path(program.executable),
                "image_sha256":program.expected, "jobs":jobs}))
            ready = self._answer()
            if (set(ready) != {"schema", "reader", "runtime_policy", "runtime_identity"}
                    or ready["schema"] != SCHEMA or ready["reader"] != reader or ready["runtime_policy"] != POLICY
                    or not re.fullmatch(r"[0-9a-f]{64}", str(ready["runtime_identity"]))):
                raise Corrupt("native reader compatibility/runtime profile differs")
            self.runtime_identity = ready["runtime_identity"]  # compatibility DATA, not admission
            program.bookend()
        except BaseException as primary:
            try:
                self.close()
            except BaseException as cleanup:
                # Unknown cleanup is terminal too. It cannot mask malformed
                # ready data and turn a protocol refusal into fallback credit.
                raise Corrupt(f"native reader setup refused: {primary}; cleanup failed: {cleanup}") from cleanup
            if isinstance(primary, Unavailable) and self.stderr_tail:
                raise Unavailable(f"{primary}: {self.stderr_tail.decode(errors='replace').strip()}") from primary
            raise

    def _send(self, body):
        if len(body) + 1 > MAX_FRAME or self.failed:
            raise Unavailable("native reader request is unavailable or exceeds its bound")
        pending = memoryview(body + b"\n")
        deadline = time.monotonic() + 120
        while pending:
            self.check_cancel()
            if time.monotonic() >= deadline:
                raise Unavailable("native reader request timed out")
            if not select.select([], [self.child.stdin], [], .1)[1]:
                continue
            try:
                count = os.write(self.child.stdin.fileno(), pending)
            except BlockingIOError:
                continue
            if count <= 0:
                raise Unavailable("native reader request made no progress")
            pending = pending[count:]

    def _answer(self):
        deadline = time.monotonic() + 120
        while b"\n" not in self.buffer:
            self.check_cancel()
            if len(self.buffer) > MAX_REPLY:
                raise Corrupt("native reader response exceeds its bound")
            if time.monotonic() >= deadline:
                raise Unavailable("native reader response deadline expired")
            if not select.select([self.child.stdout], [], [], .1)[0]:
                continue
            chunk = os.read(self.child.stdout.fileno(), MAX_REPLY + 1)
            if not chunk:
                raise Unavailable("native reader ended before its bound response")
            self.buffer.extend(chunk)
        line, _, tail = self.buffer.partition(b"\n")
        self.buffer = bytearray(tail)
        if len(line) > MAX_REPLY or tail:
            raise Corrupt("native reader sent extra or oversized response data")
        try:
            envelope = json.loads(line, object_pairs_hook=_object)
            if not isinstance(envelope, dict) or set(envelope) != {"body", "mac"}:
                raise Corrupt("malformed native reader envelope")
            body = base64.b64decode(envelope["body"], validate=True)
            if (not isinstance(envelope["mac"], str)
                    or not hmac.compare_digest(hmac.digest(self.key, body, "sha256").hex(), envelope["mac"])):
                raise Corrupt("native reader response authentication failed")
            answer = json.loads(body, object_pairs_hook=_object)
            if not isinstance(answer, dict):
                raise Corrupt("malformed native reader response")
            return answer
        except (ValueError, TypeError, KeyError) as error:
            raise Corrupt("malformed native reader response encoding") from error

    def batch(self, repo, items):
        try:
            nonce = os.urandom(32).hex()
            body = _json({"schema":SCHEMA, "nonce":nonce, "repo":_path(repo), "items":[
                {"path":_path(path), "mode":mode, "oid":oid} for path,mode,oid,_label in items]})
            self._send(body)
            answer = self._answer()
            if (set(answer) != {"schema", "nonce", "request_sha256", "checked", "bytes", "failures"}
                    or answer["schema"] != SCHEMA or answer["nonce"] != nonce
                    or answer["request_sha256"] != hashlib.sha256(body).hexdigest()
                    or type(answer["checked"]) is not int or type(answer["bytes"]) is not int
                    or not 0 <= answer["bytes"] <= 2**64-1 or not isinstance(answer["failures"], list)):
                raise Corrupt("native reader returned a malformed or differently bound batch")
            if answer["checked"] != len(items):
                raise Corrupt("native reader omitted tracked inputs")
            previous = -1
            for failure in answer["failures"]:
                if (not isinstance(failure, dict) or set(failure) != {"index", "kind", "digest", "stat"}
                        or type(failure["index"]) is not int or not previous < failure["index"] < len(items)
                        or failure["kind"] not in ("inspect", "parent-escape", "root-change", "symlink-type", "regular-type",
                            "executable-mode", "opening-change", "reading-change", "inspection-change", "link-bytes", "regular-bytes")):
                    raise Corrupt("native reader returned malformed or unordered physical refusals")
                previous = failure["index"]
                if failure["kind"] == "regular-bytes":
                    _relative, mode, oid, _label = items[previous]
                    snapshot = failure["stat"]
                    if (mode not in ("100644", "100755") or not isinstance(failure["digest"], str)
                            or not re.fullmatch(r"[0-9a-f]{" + str(len(oid)) + "}", failure["digest"])
                            or failure["digest"] == oid or not isinstance(snapshot, dict)
                            or set(snapshot) != {"dev", "ino", "mode", "bytes", "mtime_sec", "mtime_nsec", "ctime_sec", "ctime_nsec"}
                            or any(type(value) is not int for value in snapshot.values())
                            or any(not 0 <= snapshot[name] <= 2**64-1 for name in ("dev", "ino", "mode", "bytes"))
                            or not stat.S_ISREG(snapshot["mode"])
                            or bool(snapshot["mode"] & stat.S_IXUSR) != (mode == "100755")
                            or any(not 0 <= snapshot[name] < 10**9 for name in ("mtime_nsec", "ctime_nsec"))):
                        raise Corrupt("native reader returned a malformed captured digest observation")
                elif failure["digest"] is not None or failure["stat"] is not None:
                    raise Corrupt("native reader attached digest data to a different refusal")
            return answer["bytes"], answer["failures"]
        except Corrupt:
            self.failed = True
            raise
        except (ValueError, TypeError, KeyError) as error:
            self.failed = True
            raise Corrupt("malformed native reader response") from error
        except (OSError, Unavailable) as error:
            self.failed = True
            raise Unavailable(str(error)) from error

    def close(self):
        if self.closed:
            return
        self.closed = True
        try:
            if self.child is not None:
                if self.child.stdin is not None:
                    self.child.stdin.close()
                if self.owned is not None:
                    self.owned.retire(self.cancellation)
                else:
                    # Popen succeeded but owner construction failed: retain
                    # this exact unreaped original until normal group cleanup.
                    landing_targo.signal_owned_group(self.child.pid, 15)
                    landing_targo.wait_child_exit(self.child.pid)
                    landing_targo.signal_owned_group(self.child.pid, 9)
                    self.child.wait()
                self.child.stdout.close()
        finally:
            if self.child is not None and (self.owned is None or not self.owned.reaped):
                # A failed retirement cannot release the original image or
                # erase custody of a possibly live child. This poisoned owner
                # accepts no more work and is never automatically respawned.
                _RETAINED_FAILURES.append(self)
            else:
                if self.errors is not None:
                    self.errors.seek(0, os.SEEK_END)
                    self.errors.seek(max(0,self.errors.tell()-16384))
                    self.stderr_tail = self.errors.read(16384)
                    self.errors.close()
                self.program.close()
