"""The physical per-file check of land_gate's checkout_problem.

A tracked file's bytes, type and mode are compared with its committed blob
directly, without Git's conversion filters, index stat cache or hiding
configuration (raw_tracked_problem). land_gate loads this file from source
bytes it captures at import (ignoring pyc and module caches). Its checkout
worker processes are forked from the gate, compile those same bytes and
`serve` batches of files: a worker never imports gate code from the checkout it
is inspecting, so an edit to that checkout during a run cannot change the check
that judges it. That is why this module imports nothing but the standard
library.
"""
from __future__ import annotations

# The check loads nothing lazily: atexit (tempfile's finalizer) and the ascii
# codec (the attribute query's files) are what it would load on first use, so
# they are loaded here; the locale's codec, which `subprocess` decodes Git's
# output with, is loaded by prepare(). A worker imports nothing after it says
# `ready` (serve).
import atexit  # noqa: F401
import codecs
import encodings.ascii  # noqa: F401
import hashlib
import hmac
import locale
import marshal
import os
import stat
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple


def physical_stat_key(value) -> tuple:
    return (value.st_dev, value.st_ino, value.st_mode, value.st_size,
            value.st_mtime_ns, value.st_ctime_ns)


def git_ask(root: Path, env: Dict[str, str], *args: str,
            timeout: Optional[float] = None, input: Optional[str] = None) -> subprocess.CompletedProcess:
    try:
        return subprocess.run(["git", "-C", str(root), *args], capture_output=True, text=True, errors="surrogateescape", env=env,
                              timeout=timeout, input=input)
    except subprocess.TimeoutExpired:
        return subprocess.CompletedProcess(args, 124, "", f"timed out after {timeout:.0f}s")
    except OSError as exc:
        return subprocess.CompletedProcess(args, 127, "", str(exc))


def committed_crlf_matches(repo: Path, revision: str, path: str, oid: str,
                           physical_digest: str, env: Dict[str, str]) -> bool:
    """Admit only the exact CRLF form requested by HEAD's text/EOL attributes.

    Query attributes in an isolated bare Git directory sharing only read-only
    objects. Its empty info directory and explicit config cannot import local,
    global or system attributes, clean filters, encodings, or ident expansion.
    """
    objects = git_ask(repo, env, "rev-parse", "--path-format=absolute", "--git-path", "objects", timeout=10)
    if objects.returncode or not objects.stdout.strip():
        return False
    attributes = ("text", "eol", "filter", "working-tree-encoding", "ident")
    with tempfile.TemporaryDirectory(prefix="trust-head-attributes.") as temporary:
        isolated = Path(temporary)
        (isolated / "objects").mkdir()
        (isolated / "refs").mkdir()
        (isolated / "HEAD").write_text("ref: refs/heads/unused\n", encoding="ascii")
        sha256 = len(oid) == 64
        (isolated / "config").write_text(
            "[core]\nrepositoryformatversion = " + ("1" if sha256 else "0") + "\nbare = true\n"
            + ("[extensions]\nobjectformat = sha256\n" if sha256 else ""), encoding="ascii")
        query_env = dict(env, GIT_DIR=str(isolated), GIT_OBJECT_DIRECTORY=objects.stdout.strip(),
                         GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1", GIT_ATTR_NOSYSTEM="1",
                         GIT_ATTR_SOURCE=revision)
        try:
            answer = subprocess.run(
                ["git", "-c", "core.attributesFile=" + os.devnull, "check-attr", "--source=" + revision,
                 "-z", "--stdin", *attributes], input=os.fsencode(path) + b"\0",
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=query_env, timeout=10)
        except (OSError, subprocess.TimeoutExpired):
            return False
        parts = answer.stdout.split(b"\0")
        if answer.returncode or parts[-1:] != [b""] or len(parts) != 3 * len(attributes) + 1:
            return False
        actual = {}
        for offset in range(0, len(parts) - 1, 3):
            if parts[offset] != os.fsencode(path):
                return False
            actual[parts[offset + 1]] = parts[offset + 2]
        # Explicit eol=crlf also requests text conversion when text is unspecified.
        # A disabled text attribute or auto-detection is not this exact contract.
        if actual.get(b"text") not in (b"set", b"unspecified") or actual.get(b"eol") != b"crlf":
            return False
        if any(actual.get(name.encode()) not in (b"unspecified", b"unset") for name in attributes[2:]):
            return False
    try:
        blob = subprocess.run(["git", "-C", str(repo), "cat-file", "blob", oid], env=env,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=10)
    except (OSError, subprocess.TimeoutExpired):
        return False
    if blob.returncode or b"\0" in blob.stdout or b"\r\n" in blob.stdout:
        return False
    algorithm = "sha256" if len(oid) == 64 else "sha1"
    original = b"blob " + str(len(blob.stdout)).encode("ascii") + b"\0" + blob.stdout
    if hashlib.new(algorithm, original).hexdigest() != oid:
        return False
    converted = blob.stdout.replace(b"\n", b"\r\n")
    canonical = b"blob " + str(len(converted)).encode("ascii") + b"\0" + converted
    return hashlib.new(algorithm, canonical).hexdigest() == physical_digest


def raw_tracked_problem(repo: Path, revision: str, path: str, mode: str, oid: str,
                        label: str, env: Dict[str, str]) -> Optional[str]:
    """Compare physical bytes/type/mode directly, without Git conversion filters."""
    repo_path = os.fspath(repo)
    source = os.path.join(repo_path, path)
    try:
        parent = os.path.realpath(os.path.dirname(source), strict=True)
        if os.path.normcase(os.path.commonpath((parent, repo_path))) != os.path.normcase(repo_path):
            raise ValueError("tracked parent escapes repository")
        before = os.lstat(source)
        digest = hashlib.new("sha1" if len(oid) == 40 else "sha256")
        if mode == "120000":
            if not stat.S_ISLNK(before.st_mode):
                return f"tracked inputs changed: symlink type differs at {label!r}"
            data = os.fsencode(os.readlink(source))
            digest.update(b"blob " + str(len(data)).encode("ascii") + b"\0" + data)
        elif mode in ("100644", "100755"):
            if not stat.S_ISREG(before.st_mode):
                return f"tracked inputs changed: regular-file type differs at {label!r}"
            if bool(before.st_mode & stat.S_IXUSR) != (mode == "100755"):
                return f"tracked inputs changed: executable mode differs at {label!r}"
            fd = os.open(source, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0))
            with os.fdopen(fd, "rb") as stream:
                if physical_stat_key(os.fstat(stream.fileno())) != physical_stat_key(before):
                    return f"tracked input changed while opening {label!r}"
                digest.update(b"blob " + str(before.st_size).encode("ascii") + b"\0")
                # Avoid allocating a MiB for every small file. This sizes each
                # request, never the total: keep reading through EOF so growth
                # still reaches the hash and the unchanged before/after checks.
                read_size = min(1024 * 1024, before.st_size + 1)
                for chunk in iter(lambda: stream.read(read_size), b""):
                    digest.update(chunk)
                if physical_stat_key(os.fstat(stream.fileno())) != physical_stat_key(before):
                    return f"tracked input changed while reading {label!r}"
        else:
            return f"unsupported tracked file mode {mode!r} at {label!r}"
        if physical_stat_key(os.lstat(source)) != physical_stat_key(before):
            return f"tracked input changed during inspection at {label!r}"
        if digest.hexdigest() != oid:
            if mode not in ("100644", "100755") or not committed_crlf_matches(
                    repo, revision, path, oid, digest.hexdigest(), env):
                return f"tracked inputs changed: raw bytes differ from the committed blob at {label!r}"
            if physical_stat_key(os.lstat(source)) != physical_stat_key(before):
                return f"tracked input changed during attribute inspection at {label!r}"
    except (OSError, RuntimeError, ValueError) as exc:
        return f"cannot inspect physical tracked input {label!r} ({exc})"
    return None


def raw_tracked_batch(repo: str, revision: str, env: Dict[str, str],
                      items: Sequence[Tuple[str, str, str, str]]) -> List[Optional[str]]:
    """raw_tracked_problem of each (path, mode, oid, label) in order, stopping
    after the first problem."""
    results: List[Optional[str]] = []
    for path, mode, oid, label in items:
        results.append(raw_tracked_problem(Path(repo), revision, path, mode, oid, label, env))
        if results[-1]:
            break
    return results


def prepare(key: bytes = b"") -> frozenset:
    """Load everything the check and its answers run: the hash and HMAC
    implementations (with any configuration they read) and the text codec
    `subprocess` decodes Git's output with (the locale's; under a locale that
    is neither UTF-8 nor ASCII it is not loaded at start). The names of the
    modules then loaded."""
    for algorithm in ("sha1", "sha256"):
        hashlib.new(algorithm, b"").hexdigest()
    hmac.compare_digest(hmac.digest(key, b"", "sha256"), b"")
    encoding = "utf-8" if sys.flags.utf8_mode else locale.getencoding()
    codecs.getincrementaldecoder(encoding)(errors="surrogateescape").decode(b"x", final=True)
    "x".encode(encoding, "surrogateescape").decode(encoding, "surrogateescape")
    return frozenset(sys.modules)


class _NoImport:
    """A worker's first import finder once it is ready: it refuses every
    import of a module not already loaded, before any finder looks for a file,
    and notes it. No module body read after `ready` runs in a worker (a check
    after the import could only see one that had run already)."""

    def __init__(self) -> None:
        self.attempted: List[str] = []

    def find_spec(self, name, path=None, target=None):
        self.attempted.append(name)
        raise ImportError(f"a checkout worker imports nothing once it is ready: {name}")


def serve(requests, answers, key: bytes) -> None:
    """A checkout worker: once everything it runs is loaded (prepare), refuse
    every further import (_NoImport) and say `ready`; then answer each
    marshalled (nonce, request) on `requests`, where request is the marshalled
    (repo, revision, env, items), with (nonce, the request's sha256, the
    marshalled raw_tracked_batch results, an HMAC-SHA256 of those three under
    `key`) on `answers`, until EOF. A batch that tried to import anything (or
    raised) stops the worker unanswered, and the gate checks it itself."""
    loaded = prepare(key)
    refused = _NoImport()
    sys.meta_path.insert(0, refused)
    answers.write(b"ready\n")
    answers.flush()
    while True:
        try:
            nonce, request = marshal.load(requests)
        except EOFError:
            return
        repo, revision, env, items = marshal.loads(request)
        results = raw_tracked_batch(repo, revision, env, items)
        if refused.attempted or not loaded.issuperset(sys.modules):
            return
        digest, body = hashlib.sha256(request).digest(), marshal.dumps(results)
        marshal.dump((nonce, digest, body, hmac.digest(key, nonce + digest + body, "sha256")), answers)
        answers.flush()
