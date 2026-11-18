#!/usr/bin/env python3
"""Agh-only exact Git objects and local-only native Cargo Git handoff.

Cargo owns patch/version/lock resolution. Daily's separate CONNECT gate closes
its pre-CLI HTTP route; only source commits in the actual selected owner locks
or a checked exact-parent Gitlink ledger may be acquired here. No credential
extraction, raw GitHub Git/HTTP fallback or proof authority is provided.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import subprocess
import sys
import tempfile
import time
import types
from urllib.parse import parse_qsl, urljoin, urlsplit

MAX_REPOSITORIES = 512
MAX_GITLINK_DEPTH = 64
MAX_TREE_ROWS = 1000000
MAX_MODULE_BYTES = 1024 * 1024

class Refused(RuntimeError):
    pass

def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def source_owner(path: Path, name: str, expected: str | None = None):
    """Hash and execute ONE captured source buffer, never cached bytecode."""
    raw = path.read_bytes()
    actual = hashlib.sha256(raw).hexdigest()
    if expected is not None and actual != expected:
        raise Refused("dependency source owner differs from its captured identity")
    module = types.ModuleType(name)
    module.__file__ = str(path)
    module.__package__ = ""
    previous = sys.modules.get(name)
    sys.modules[name] = module
    try:
        exec(compile(raw, str(path), "exec"), module.__dict__)
    finally:
        if previous is None:
            sys.modules.pop(name, None)
        else:
            sys.modules[name] = previous
    if digest(path) != actual:
        raise Refused("dependency source owner changed while loading")
    return module.__dict__, actual

def canonical_url(value: str) -> str:
    if not isinstance(value, str) or not re.fullmatch(
            r"https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+(?:\.git)?", value):
        raise Refused("dependency Git source needs a literal HTTPS GitHub repository URL")
    owner, repo = value.removeprefix("https://github.com/").split("/")
    repo = repo.removesuffix(".git")
    if owner in {".", ".."} or repo in {".", "..", ""}:
        raise Refused("dependency Git source has an invalid repository identity")
    return f"https://github.com/{owner}/{repo}.git"

def exact_oid(value: str) -> str:
    if not isinstance(value, str) or not re.fullmatch(r"[0-9a-f]{40}", value):
        raise Refused("dependency Git source requires a full lowercase40 commit revision")
    return value

def lock_specs(document: dict, *, package_names=False):
    packages = document.get("package", [])
    if not isinstance(packages, list):
        raise Refused("dependency lock package population is malformed")
    for package in packages:
        if not isinstance(package, dict):
            raise Refused("dependency lock package row is malformed")
        source = package.get("source")
        if source is None:
            continue
        if not isinstance(source, str):
            raise Refused("dependency lock source is malformed")
        if source.startswith("git+"):
            value = urlsplit(source[4:])
            query = parse_qsl(value.query, keep_blank_values=True, strict_parsing=True)
            if len(query) > 1 or any(k not in {"rev", "branch", "tag"} for k, _ in query):
                raise Refused("dependency lock Git selector is unsupported")
            url = source[4:].split("?", 1)[0].split("#", 1)[0]
            pair = canonical_url(url), exact_oid(value.fragment)
            package_name = package.get("name")
            if not isinstance(package_name, str) or not re.fullmatch(r"[A-Za-z0-9_-]+", package_name):
                raise Refused("dependency locked Git package identity is unsupported")
            yield (*pair, package_name) if package_names else pair
        elif source != "registry+https://github.com/rust-lang/crates.io-index":
            raise Refused("dependency lock source is outside the crates.io/exact-Git profile")

def owner_api(source: Path, expected: str | None = None, identity_expected: str | None = None,
              loader_expected: str | None = None):
    path = source / "scripts/recreate_bootstrap.py"
    identity = source / "src/bootstrap/stage0_identity.py"
    identity_before = digest(identity)
    if identity_expected is not None and identity_before != identity_expected:
        raise Refused("dependency Git transitive source owner changed")
    loader_path = source / "scripts/seed_custody_source.py"
    loader_owner, _loader_digest = source_owner(loader_path, "daily_dependency_source_loader", loader_expected)
    manifest = {"scripts/recreate_bootstrap.py": expected if expected is not None else digest(path),
                "scripts/source_working_cache.py": digest(source / "scripts/source_working_cache.py"),
                "src/bootstrap/stage0_identity.py": identity_before}
    loader = loader_owner["BoundSourceLoader"](source, manifest)
    result = loader.module("daily_dependency_git_owner", path).__dict__
    loader.recheck()
    if (digest(identity) != identity_before
            or result.get("_IDENTITY_SOURCE_SHA256") != identity_before):
        raise Refused("dependency Git source owner changed while loading")
    return result

def local_acquisition_command(args):
    """Only the two fixed exact-checkout fetch forms may use the bulk limit."""
    if (len(args) == 11 and args[:5] == ["-c", "protocol.file.allow=always", "-c",
            "fetch.fsckObjects=true", "-C"] and args[6:9] == ["fetch", "--no-tags", "--depth=1"]):
        return (Path(args[5]).is_absolute() and Path(args[9]).is_absolute()
                and re.fullmatch(r"\+([0-9a-f]{40}):refs/agh/trust-daily-dependencies/\1", args[10]) is not None)
    if (len(args) == 12 and args[:3] == ["-c", "protocol.file.allow=always", "--git-dir"]
            and args[4:10] == ["fetch", "--no-tags", "--depth=1", "--force", "--update-head-ok", "--recurse-submodules=no"]):
        return (Path(args[3]).is_absolute() and Path(args[10]).is_absolute()
                and re.fullmatch(r"\+([0-9a-f]{40}):refs/commit/\1", args[11]) is not None)
    return False


def dependency_clock(owner):
    """The clock the preparation's bounds read: the owner's own, or the monotonic one."""
    return owner.get("_dependency_clock", time.monotonic)


def ceiling_left(owner, before: str) -> float:
    """Seconds left under the preparation's ceiling, refusing once it is reached."""
    left = owner["_dependency_deadline"] - dependency_clock(owner)()
    if left <= 0:
        ceiling = owner.get("_dependency_ceiling")
        named = f" of {ceiling} s, printed at its start," if ceiling is not None else ""
        raise Refused(f"dependency preparation deadline exhausted: it reached its ceiling{named} before {before}")
    return left


def item_progress(owner, label: str, paths=()):
    """The bound of ONE item of the dependency preparation.

    An item (one Agh acquisition, one local Git transfer or whole-tree read, one
    `targo fetch` of one manifest, one tree copied into a Cargo home) runs as long
    as it keeps moving: it is ended when the bytes arriving under ``paths`` and on
    its output stay under the recreator's floor for its stall window, the bound
    every submodule acquisition has. The preparation's ceiling, computed from its
    inputs at its start, ends whatever item is running when it is reached. Either
    refusal names the item.
    """
    clock = dependency_clock(owner)
    end = owner["_dependency_deadline"]
    ceiling = owner.get("_dependency_ceiling")
    stalled = owner["_SubmoduleStalled"]

    class Item(owner["_SubmoduleProgress"]):
        def begin(self):
            self.started = clock()
            super().begin()

        def check(self, command):
            now = clock()
            if now >= end:
                raise stalled(command, self.window, (
                    f"{label} was still running {now - self.started:.0f} s after it started when the "
                    f"preparation reached its ceiling" + (f" of {ceiling} s, printed at its start" if ceiling is not None else "")))
            super().check(command)

    return Item(label, tuple(paths), clock=clock,
                measure=owner.get("_dependency_measure", owner["_submodule_progress_bytes"]))


def run_item(owner, label: str, command, environment, paths=()):
    """Run one item's child under process-tree custody and its item_progress bound."""
    ceiling_left(owner, label)
    try:
        return owner["_run_submodule_update_process"](command, environment=environment,
            timeout_seconds=None, credential_gh=None, progress=item_progress(owner, label, paths))
    except owner["_SubmoduleStalled"] as error:
        raise Refused(f"dependency preparation ended {label}: {error}") from error


def local_git(owner, args, *, cwd=None, bounded=False, input_bytes=None, acquisition=False,
              label=None, paths=(), whole_tree=False):
    """One local Git command of the preparation.

    ``bounded`` is an item (a transfer or a gc): it runs under process-tree custody and
    ends for lack of progress under ``paths`` or at the ceiling, never on a constant.
    Every other call is a constant-size query with 60 s, except ``whole_tree`` (a listing
    of a whole commit tree), which has the stall window.
    """
    if acquisition and not bounded:
        raise Refused("dependency Git acquisition requires process-tree custody")
    if acquisition and not local_acquisition_command(args):
        raise Refused("dependency Git acquisition is not a fixed local source fetch")
    label = label or "local Git " + " ".join(a for a in args if not a.startswith(("-", "/", "+")))[:80]
    remaining = ceiling_left(owner, label)
    env = owner["_provenance_git_environment"]()
    env["GIT_NO_LAZY_FETCH"] = "1"
    command = owner["_controlled_git_command"](
        ["-c", "protocol.allow=never", "-c", "protocol.https.allow=never",
         "-c", "gc.autoDetach=false", "-c", "maintenance.auto=false", *args])
    if bounded:
        result = run_item(owner, label, command, env, paths)
        if result.returncode:
            raise Refused(f"fixed local dependency Git process did not complete successfully: {label}")
        return result
    limit = owner["SUBMODULE_STALL_WINDOW_SECONDS"] if whole_tree else 60
    return subprocess.run(command,
        cwd=cwd, env=env, input=input_bytes, capture_output=True, check=True, timeout=min(limit, remaining))


def watched_git(owner, args, *, label: str, output: Path):
    """A local Git read over a whole commit tree, its output kept in ``output``.

    It is an item like any other: ended for lack of progress (its output stops growing)
    or at the ceiling. Returns its exit code and the tail of what it wrote to stderr.
    """
    ceiling_left(owner, label)
    env = owner["_provenance_git_environment"]()
    env["GIT_NO_LAZY_FETCH"] = "1"
    command = owner["_controlled_git_command"](
        ["-c", "protocol.allow=never", "-c", "protocol.https.allow=never",
         "-c", "gc.autoDetach=false", "-c", "maintenance.auto=false", *args])
    errors = output.with_name(output.name + ".stderr")
    progress = item_progress(owner, label, (output, errors))
    with output.open("wb") as sink, errors.open("wb") as diagnostics:
        progress.begin()
        process = subprocess.Popen(command, env=env, stdin=subprocess.DEVNULL, stdout=sink,
                                   stderr=diagnostics, start_new_session=True)
        try:
            code = owner["_wait_submodule_process_group"](process, None, progress)
        except BaseException as error:
            owner["_terminate_submodule_process_tree"](process)
            if isinstance(error, owner["_SubmoduleStalled"]):
                raise Refused(f"dependency preparation ended {label}: {error}") from error
            raise
    return code, errors.read_bytes()[-4096:].decode("utf-8", errors="replace").strip()


def verify_checkout_closure(owner, repository: Path, oid: str, label: str, scratch: Path):
    """Every tree and blob the commit's own tree reaches is present and hashes to its name.

    This is the whole check of an acquired commit: its ancestors are not asked for, so
    a store that holds only the checkout closure (a depth-one transfer, or Agh's
    selected checkout) passes, and one that lacks any object of it refuses, naming it.
    Git reports a body that does not hash to its name on stderr and still exits zero,
    so any diagnostic refuses too.
    """
    listing = scratch / f"closure-{oid}.objects"
    code, errors = watched_git(owner, ["--git-dir", str(git_directory(repository)), "rev-list", "--objects",
                                       "--no-walk", "--verify-objects", "--missing=print", oid],
                               label=f"the checkout closure check of {label}", output=listing)
    if code or errors:
        raise Refused(f"checkout closure of {label} does not verify (exit {code}): {errors or 'no diagnostic'}")
    missing = [line[1:].strip() for line in listing.read_text().splitlines() if line.startswith("?")]
    if missing:
        names = scratch / f"closure-{oid}.paths"
        code, _errors = watched_git(owner, ["--git-dir", str(git_directory(repository)), "ls-tree", "-r", "-t",
                                            "-z", oid], label=f"the path census of {label}", output=names)
        paths = {}
        for row in names.read_bytes().split(b"\0"):
            if b"\t" in row:
                header, path = row.split(b"\t", 1)
                paths[header.split()[-1].decode()] = path.decode("utf-8", errors="replace")
        shown = ", ".join(f"{name} ({paths.get(name, 'path unknown')})" for name in missing[:5])
        raise Refused(f"checkout closure of {label} lacks {len(missing)} object(s) its tree reaches: {shown}")
    listing.unlink()


def git_directory(repository: Path) -> Path:
    """The Git directory of an owned preparation store (a stage) or a bare relay."""
    return repository / ".git" if (repository / ".git").is_dir() else repository


def declared_object_store(cache: Path) -> Path:
    """The object directory a declared repository lends, and nothing else of it.

    A declared cache (a developer checkout named by --source-object-cache, or a Cargo
    home given as input) is read only through a private relay whose alternates name
    this directory: its configuration, hooks and refs are never read or run, and what
    it lends is checked by content. A store that routes its objects elsewhere refuses.
    """
    real_directory(cache)
    store = cache / ".git" if os.path.lexists(cache / ".git") else cache
    if store.is_symlink() or not store.is_dir() or os.path.lexists(store / "commondir"):
        raise Refused(f"declared dependency object cache must be a repository with its own object store: {cache}")
    objects = store / "objects"
    real_directory(objects)
    for relative in ("info/alternates", "info/http-alternates"):
        if os.path.lexists(objects / relative):
            raise Refused(f"declared dependency object cache routes its objects elsewhere: {objects / relative}")
    return objects


def input_object_stores(home: Path | None) -> list[Path]:
    """The object directories of a Cargo home given as input: each git/db database."""
    if home is None or not os.path.lexists(home / "git/db"):
        return []
    real_directory(home / "git/db")
    return [declared_object_store(db) for db in sorted((home / "git/db").iterdir())]


def lent_commit(owner, transport: Path, url: str, stores: list[Path], oid: str):
    """The relay that lends ``oid`` when the stores hold its whole checkout closure, else None."""
    if not stores:
        return None
    relay = transport / ("relay-" + hashlib.sha256(url.encode()).hexdigest()[:16])
    if not relay.exists():
        local_git(owner, ["init", "--quiet", "--bare", "--template=", "--object-format=sha1", str(relay)])
        (relay / "objects/info").mkdir(parents=True, exist_ok=True)
        (relay / "objects/info/alternates").write_text("".join(f"{store}\n" for store in stores))
    elif (relay / "objects/info/alternates").read_text() != "".join(f"{store}\n" for store in stores):
        raise Refused("dependency object relay changed its lent stores")
    row = local_git(owner, ["--git-dir", str(relay), "cat-file", "--batch-check"],
                    input_bytes=(oid + "\n").encode()).stdout.decode().strip()
    if row == oid + " missing":
        return None
    if not re.fullmatch(oid + r" commit [0-9]+", row):
        raise Refused("declared dependency object cache has a noncommit or malformed requested object")
    census = transport / f"held-{oid}.objects"
    code, errors = watched_git(owner, ["--git-dir", str(relay), "rev-list", "--objects", "--no-walk",
                                       "--missing=print", oid],
                               label=f"the census of {url} {oid[:12]} in its declared object caches", output=census)
    if code:
        raise Refused(f"declared dependency object cache census failed (exit {code}): {errors}")
    held = not any(line.startswith("?") for line in census.read_text().splitlines())
    census.unlink()
    return relay if held else None

def regular(path: Path):
    st = path.lstat()
    if not stat.S_ISREG(st.st_mode) or st.st_nlink != 1:
        raise Refused("dependency transport input must be an independently owned regular file")
    return st.st_dev, st.st_ino, stat.S_IMODE(st.st_mode), st.st_size, digest(path)

def real_directory(path: Path):
    if not path.is_absolute():
        raise Refused("dependency directory must be absolute")
    for parent in (*reversed(path.parents), path):
        if parent.is_symlink() or not parent.is_dir():
            raise Refused("dependency directory has symbolic or missing custody")
    st = path.stat()
    return st.st_dev, st.st_ino

def committed_gitlinks(owner, stage: Path, oid: str, parent_url: str):
    """Retain exact paths/IDs/URLs from this commit, including inactive rows."""
    raw = local_git(owner, ["-C", str(stage), "ls-tree", "-r", "-z", oid], whole_tree=True).stdout
    rows = list(filter(None, raw.split(b"\0")))
    if len(rows) > MAX_TREE_ROWS:
        raise Refused("dependency Git tree exceeds its finite bound")
    links, module_blob = {}, None
    for row in rows:
        header, path = row.split(b"\t", 1)
        mode, kind, object_id = header.decode().split()
        path = path.decode("utf-8")
        if mode == "160000":
            if kind != "commit" or path in links:
                raise Refused("dependency Git tree has an ambiguous gitlink")
            links[path] = exact_oid(object_id)
        elif path == ".gitmodules":
            if mode not in {"100644", "100755"} or kind != "blob" or module_blob is not None:
                raise Refused("dependency .gitmodules must be one regular committed blob")
            module_blob = object_id
    if not links and module_blob is None:
        return []
    if module_blob is None:
        raise Refused("dependency gitlinks have no committed .gitmodules")
    size = int(local_git(owner, ["-C", str(stage), "cat-file", "-s", module_blob]).stdout)
    if size > MAX_MODULE_BYTES:
        raise Refused("dependency .gitmodules exceeds its finite bound")
    content = local_git(owner, ["-C", str(stage), "cat-file", "blob", module_blob]).stdout
    with tempfile.TemporaryDirectory(prefix="modules-", dir=stage.parent) as temp:
        path = Path(temp) / "modules"
        path.write_bytes(content)
        config = local_git(owner, ["config", "--no-includes", "--file", str(path), "--null", "--list"], cwd=path.parent).stdout
    entries = {}
    for key, value in owner["_parse_git_config_records"](config, stage, "dependency .gitmodules"):
        match = re.fullmatch(r"submodule\.(.+)\.(path|url|branch|update|ignore|shallow)", key)
        if match is None:
            raise Refused("dependency .gitmodules has unsupported authority")
        name, field = match.groups()
        entry = entries.setdefault(name, {})
        if field in entry:
            raise Refused("dependency .gitmodules repeats a field")
        entry[field] = value
    mapped, ledger = set(), []
    for name, entry in sorted(entries.items()):
        path = entry.get("path")
        if (not isinstance(path, str) or path not in links or path in mapped or "\\" in path
                or path.startswith("/") or "//" in path or any(p in {".", "..", ".git"} for p in path.split("/"))
                or any(ord(c) < 32 or ord(c) == 127 for c in path)):
            raise Refused("dependency .gitmodules/gitlink path inventory differs")
        mapped.add(path)
        url = entry.get("url", "")
        if url.startswith(("./", "../")):
            url = urljoin(parent_url.rstrip("/") + "/", url)
        url = canonical_url(url)
        update = entry.get("update", "checkout")
        if update not in {"checkout", "merge", "rebase", "none"}:
            raise Refused("dependency .gitmodules has unsupported update authority")
        ledger.append({"parent_url": parent_url, "parent_oid": oid, "gitmodules_blob": module_blob,
                       "name": name, "path": path, "url": url, "oid": links[path], "active": update != "none"})
    if mapped != set(links):
        raise Refused("dependency .gitmodules/gitlink inventory is incomplete")
    return ledger


def selected_repository(source: Path, repository: Path, owner, repositories: dict) -> None:
    relative = repository.relative_to(source).as_posix()
    if relative in repositories:
        return
    head = local_git(owner, ["-C", str(repository), "rev-parse", "HEAD"]).stdout.decode().strip()
    exact_oid(head)
    if repository != source:
        parent = Path(local_git(owner, ["-C", str(repository.parent), "rev-parse", "--show-toplevel"])
                      .stdout.decode().strip()).resolve(strict=True)
        if not parent.is_relative_to(source) or parent == repository:
            raise Refused("selected nested repository has no selected Source parent")
        selected_repository(source, parent, owner, repositories)
        child = repository.relative_to(parent)
        entries = [entry for entry in owner["_indexed_submodules"](parent) if entry.path == child]
        if len(entries) != 1 or entries[0].oid != head:
            raise Refused("selected nested repository is not the exact indexed Source gitlink")
        entry = entries[0]
        committed = local_git(owner, ["-C", str(parent), "ls-tree", "-z", "HEAD", "--", child.as_posix()]).stdout
        expected = b"160000 commit " + head.encode() + b"\t" + child.as_posix().encode() + b"\0"
        modules = local_git(owner, ["-C", str(parent), "rev-parse", "HEAD:.gitmodules"]).stdout.decode().strip()
        if committed != expected or modules != entry.modules_blob:
            raise Refused("selected nested repository differs from its committed Source gitlink declaration")
    repositories[relative] = head


def tracked_source_input(source: Path, path: Path, owner, repositories=None) -> str:
    """Bind a regular selected input to its actual owning Source index, including a child repo."""
    if path.is_symlink() or not path.is_file() or path.resolve(strict=True) != path:
        raise Refused("selected dependency input must be a regular canonical Source file")
    repository = Path(local_git(owner, ["-C", str(path.parent), "rev-parse", "--show-toplevel"])
                      .stdout.decode().strip()).resolve(strict=True)
    if not repository.is_relative_to(source):
        raise Refused("selected dependency input is not owned by the selected Source")
    selected_repository(source, repository, owner, {} if repositories is None else repositories)
    relative = path.relative_to(repository).as_posix()
    entry = local_git(owner, ["-C", str(repository), "ls-files", "--stage", "-z", "--", relative]).stdout
    match = re.fullmatch(rb"100(?:644|755) ([0-9a-f]{40}|[0-9a-f]{64}) 0\t" +
                         re.escape(relative.encode()) + rb"\0", entry)
    if match is None:
        raise Refused("selected dependency manifest/lock must be one tracked regular Source input")
    raw = path.read_bytes()
    algorithm = "sha1" if len(match[1]) == 40 else "sha256"
    actual = hashlib.new(algorithm, f"blob {len(raw)}\0".encode() + raw).hexdigest().encode()
    if actual != match[1]:
        raise Refused("selected dependency manifest/lock differs from its Source index")
    committed = local_git(owner, ["-C", str(repository), "ls-tree", "-z", "HEAD", "--", relative]).stdout
    if committed != entry[:6] + b" blob " + match[1] + b"\t" + relative.encode() + b"\0":
        raise Refused("selected dependency manifest/lock differs from committed Source HEAD")
    return path.relative_to(source).as_posix()


def selected_manifest_roots(source: Path, names, owner, repositories=None) -> list[Path]:
    """Explicit native requests, never a replacement default recipe or a Cargo resolver."""
    if not isinstance(names, (list, tuple)) or not 0 < len(names) <= 128:
        raise Refused("explicit dependency preparation needs a finite nonempty manifest selection")
    result, seen = [], set()
    for name in names:
        if (not isinstance(name, str) or not name or len(name) > 4096 or "\\" in name
                or name.startswith("/") or any(part in {"", ".", "..", ".git"} for part in name.split("/"))
                or any(ord(char) < 32 or ord(char) == 127 for char in name)
                or Path(name).name != "Cargo.toml" or name in seen):
            raise Refused("selected dependency manifests must be unique canonical Source-relative Cargo.toml paths")
        seen.add(name)
        path = source / name
        tracked_source_input(source, path, owner, repositories)
        result.append(path)
    return result


def owner_locks(source: Path, manifests: list[Path], owner) -> list[Path]:
    """The owner locks of the manifest envelope, each a committed lockfile."""
    graph = owner["_Stage0ManifestGraph"](source)
    graph.collect(manifests)
    if graph.inconclusive:
        raise Refused("dependency manifest profile is inconclusive: " + "; ".join(sorted(graph.inconclusive)))
    locks = sorted({graph.owner(entry).with_name("Cargo.lock") for entry in manifests})
    for lock in locks:
        if not lock.is_file():
            raise Refused(f"dependency owner lock is missing: no committed lockfile {lock}")
    return locks


def lock_roots(source: Path, locks: list[Path]) -> list[dict]:
    """The exact Git commits the owner locks name."""
    import tomllib
    roots = []
    for lock in locks:
        for url, oid, name in lock_specs(tomllib.loads(lock.read_text()), package_names=True):
            roots.append({"url": url, "oid": oid, "name": name, "owner_lock": str(lock.relative_to(source))})
    return roots


def owner_lock_roots(source: Path, manifests: list[Path], owner):
    """The owner locks of the manifest envelope and the exact Git commits they name."""
    locks = owner_locks(source, manifests, owner)
    return locks, lock_roots(source, locks)


def declared_checkout_caches(declarations):
    caches = {}
    for declaration in declarations:
        selection, equals, location = declaration.partition("=")
        url, fragment, oid = selection.partition("#")
        if not equals or not fragment or any(char in location for char in "\r\n\0"):
            raise Refused("dependency checkout cache requires URL#COMMIT=/absolute/repository")
        pair = canonical_url(url), exact_oid(oid)
        if pair in caches:
            raise Refused("dependency checkout cache is declared twice for one exact source")
        path = Path(location)
        caches[pair] = (path, real_directory(path))
    return caches


def prepare_profile(source: Path, work: Path, cache: Path, closure, owner, environment: dict,
                    *, deadline: float, acquire=None, object_caches=None, input_home: Path | None = None,
                    manifest_paths=None, orchestration_source=None, checkout_cache_specs=()):
    """Acquire only actual owner-lock commits and exact-parent Gitlink trees, each as
    its checkout closure: the commit and what its own tree reaches, no ancestor's body.

    Each commit comes, in order, from the first of: a database of the working Cargo
    home (an earlier preparation's, validated as Cargo's); the repositories declared
    for its URL (``object_caches``, url -> repository) and the databases of the Cargo
    home given as input (``input_home``), lent through a relay when together they hold
    the whole closure; Agh's checkout closure, given the declared repository as its
    checkout cache when there is one. The two local forms are depth-one transfers. Every
    acquisition is then checked by verify_checkout_closure. ``acquire`` replaces only the
    executor of Agh's command (a test seam); the local sources are asked first regardless.
    ``manifest_paths`` names explicit committed manifests in place of the recipe's
    (selected_manifest_roots): their manifests, owner locks and repositories are bound
    to the Source index before any lock is read, and again after the acquisitions.
    ``orchestration_source`` is the Trust checkout whose recreator, stage0 identity and
    loader judge an independent Source's selected manifests (only with ``manifest_paths``).
    ``checkout_cache_specs`` (URL#COMMIT=/absolute/repository) name one exact commit's
    checkout cache for Agh, preferred to its URL's declared repository; each must name a
    commit the preparation acquires.

    No Cargo dependency/patch resolver is reimplemented. Unknown native requests
    later fail the local-only CLI; the mandatory HTTP gate denies pre-CLI GitHub.
    """
    owner = {**owner, "_dependency_deadline": deadline}
    clock = dependency_clock(owner)
    object_caches = {canonical_url(url): Path(path) for url, path in (object_caches or {}).items()}
    lent_inputs = input_object_stores(input_home)
    cache_identity = real_directory(cache)
    checkout_caches = declared_checkout_caches(checkout_cache_specs)
    orchestration = orchestration_source or source
    if orchestration != source and manifest_paths is None:
        raise Refused("independent Source requires explicit dependency manifests")
    selected_repositories = {}
    manifests = (closure["stage0_bootstrap_manifest_roots"](source) if manifest_paths is None
                 else selected_manifest_roots(source, manifest_paths, owner, selected_repositories))
    if not manifests:
        raise Refused("dependency recipe manifest envelope is empty")
    paths = closure["_source_inputs"](source, manifests, environment,
        graph_source_root=orchestration if orchestration != source else None, require_lockfiles=True)
    identity_path = orchestration / "src/bootstrap/stage0_identity.py"
    loader_path = orchestration / "scripts/seed_custody_source.py"
    paths = [*paths, identity_path, loader_path]
    if orchestration != source:
        paths.append(orchestration / "scripts/bootstrap_dependency_closure.py")
    snapshot = closure["_snapshot"](paths)
    if snapshot[str(identity_path)] is None:
        raise Refused("dependency Git transitive source owner is missing")
    locks = owner_locks(source, manifests, owner)
    selected_inputs = None
    if manifest_paths is not None:
        selected_inputs = [tracked_source_input(source, path, owner, selected_repositories)
                           for path in sorted(set(manifests) | set(locks))]
    roots = lock_roots(source, locks)
    pending = {(root["url"], root["oid"]): 0 for root in roots}
    transport = Path(tempfile.mkdtemp(prefix="agh-git-", dir=work))
    stages, acquisitions, repositories, gitlinks = {}, [], {}, []
    while pending:
        pair = sorted(pending)[0]
        url, oid = pair
        depth = pending.pop(pair)
        key = url + "#" + oid
        if key in stages:
            continue
        if depth > MAX_GITLINK_DEPTH or len(stages) >= MAX_REPOSITORIES:
            raise Refused("dependency Gitlink closure exceeds its finite bounds")
        if closure["_snapshot"](paths) != snapshot:
            raise Refused("dependency source profile changed before acquisition")
        if url not in repositories:
            stage = Path(tempfile.mkdtemp(prefix="source-", dir=transport))
            local_git(owner, ["init", "--quiet", "--template=", "--object-format=sha1", str(stage)])
            repositories[url] = stage
        stage = repositories[url]
        identity = owner["_submodule_file_identity"](stage)
        ref = "refs/agh/trust-daily-dependencies/" + oid
        label = f"{url} {oid[:12]}"
        declared = object_caches.get(url)
        def run_agh(command, environment):
            # Its scratch is made in this preparation's transport folder, which is reclaimed with it.
            with owner["_agh_transfer_paths"](stage, environment, transport) as (child, paths):
                result = run_item(owner, f"Agh's checkout closure of {label}", command, child, paths)
                if result.returncode:
                    raise Refused("owner-routed dependency Agh acquisition failed")
        cached = cached_commit(owner, cache, oid)
        stores = ([declared_object_store(declared)] if declared is not None else []) + lent_inputs
        relay = lent_commit(owner, transport, url, stores, oid) if cached is None else None
        if cached is not None:
            local_git(owner, ["-c", "protocol.file.allow=always", "-c", "fetch.fsckObjects=true",
                "-C", str(stage), "fetch", "--no-tags", "--depth=1", str(cached), "+" + oid + ":" + ref],
                bounded=True, acquisition=True, label=f"the local transfer of {label} from {cached}", paths=(stage,))
            validate_bare_db(owner, cached)
            receipt = {"method": "exact-owned-cargo-cache", "source": oid, "private_ref": ref,
                       "commit": oid, "repository": url, "cache_db": str(cached)}
        elif relay is not None:
            local_git(owner, ["-c", "protocol.file.allow=always", "-c", "fetch.fsckObjects=true",
                "-C", str(stage), "fetch", "--no-tags", "--depth=1", str(relay), "+" + oid + ":" + ref],
                bounded=True, acquisition=True, label=f"the local transfer of {label} from its declared object caches",
                paths=(stage,))
            receipt = {"method": "exact-local-object-cache", "source": oid, "private_ref": ref,
                       "commit": oid, "repository": url, "object_stores": [str(store) for store in stores]}
        else:
            if environment.get("CARGO_NET_OFFLINE") == "true":
                raise Refused("offline dependency policy has no exact owned Git object")
            options = {"checkout_cache": declared} if declared is not None else {}
            exact = checkout_caches.get(pair)
            if exact is not None:
                path, identity_before = exact
                if real_directory(path) != identity_before:
                    raise Refused("dependency checkout cache directory changed before acquisition")
                options["checkout_cache"] = path
            receipt = owner["_agh_source_fetch"](url, stage, oid, ref, execute=acquire or run_agh, **options)
            if exact is not None and real_directory(path) != identity_before:
                raise Refused("dependency checkout cache directory changed during acquisition")
            receipt["method"] = "owner-routed-agh"
            if options:
                receipt["checkout_cache"] = str(options["checkout_cache"])
        owner["_validate_staged_submodule"](stage, identity)
        actual = local_git(owner, ["-C", str(stage), "rev-parse", "--verify", ref]).stdout.decode().strip()
        if actual != oid or local_git(owner, ["-C", str(stage), "cat-file", "-t", oid]).stdout.strip() != b"commit":
            raise Refused("dependency source ref is not the exact commit")
        verify_checkout_closure(owner, stage, oid, label, transport)
        local_git(owner, ["-C", str(stage), "config", "remote.origin.url", url])
        for prior in stages.values():
            if prior["path"] == str(stage) and local_git(owner, ["-C", str(stage), "rev-parse", "--verify", prior["ref"]]).stdout.decode().strip() != prior["oid"]:
                raise Refused("dependency acquisition changed an earlier exact source ref")
        stages[key] = {"path": str(stage), "identity": list(identity[:3]), "ref": ref, "oid": oid}
        ledger = committed_gitlinks(owner, stage, oid, url)
        gitlinks.extend(ledger)
        for entry in ledger:
            if entry["active"] and entry["url"] + "#" + entry["oid"] not in stages:
                child = entry["url"], entry["oid"]
                pending[child] = min(pending.get(child, depth + 1), depth + 1)
        acquisitions.append(receipt)
    if any(url + "#" + oid not in stages for url, oid in checkout_caches):
        raise Refused("checkout caches do not match selected dependency sources")
    if closure["_snapshot"](paths) != snapshot:
        raise Refused("dependency source profile changed during acquisition")
    ceiling_left(owner, "the end of its Git acquisitions")
    if selected_inputs is not None:
        final_repositories = {}
        if ([tracked_source_input(source, source / name, owner, final_repositories) for name in selected_inputs] != selected_inputs
                or selected_manifest_roots(source, manifest_paths, owner, final_repositories) != manifests
                or selected_repositories != final_repositories):
            raise Refused("selected dependency Source ownership changed during acquisition")
    if real_directory(cache) != cache_identity:
        raise Refused("dependency Cargo cache root changed during preparation")
    policy = {"schema": 3, "source": str(source),
              "owner_sha256": snapshot[str(orchestration / "scripts/recreate_bootstrap.py")],
              "loader_sha256": snapshot[str(loader_path)],
              "identity_owner_sha256": snapshot[str(identity_path)],
              "helper_sha256": digest(Path(__file__)), "cache": str(cache), "cache_identity": list(cache_identity),
              "stages": stages, "source_inputs_sha256": snapshot, "roots": roots, "gitlinks": gitlinks,
              "locks": [str(p.relative_to(source)) for p in locks], "acquisitions": acquisitions, "deadline": deadline,
              "ceiling_seconds": owner.get("_dependency_ceiling"),
              "object_caches": {url: str(path) for url, path in sorted(object_caches.items())},
              "input_object_stores": [str(store) for store in lent_inputs]}
    if orchestration != source:
        policy["orchestration_source"] = str(orchestration)
    if selected_inputs is not None:
        policy["manifest_selection"] = {
            "scope": "explicit-locked-inputs; Source transport only, no availability/native/proof admission",
            "manifests": [path.relative_to(source).as_posix() for path in manifests],
            "tracked_inputs": {name: snapshot[str(source / name)] for name in selected_inputs},
            "repositories": selected_repositories,
        }
    path = transport / "policy.json"
    path.write_text(json.dumps(policy, indent=2) + "\n")
    return path, policy


def parse_fetch(argv: list[str]):
    args = list(argv)
    expected = {"core.fsmonitor=false", "advice.fetchShowForcedUpdates=false", "http.maxRetries=3", "http.retryAfter=1", "http.maxRetryTime=10"}
    seen = set()
    while args[:1] == ["-c"]:
        if len(args) < 2 or (args[1] not in expected and not re.fullmatch(r"http\.maxRetries=(0|[1-9][0-9]{0,9})", args[1])) or args[1].split("=", 1)[0] in seen:
            raise Refused("dependency Git CLI configuration is outside the pinned literal profile")
        seen.add(args[1].split("=", 1)[0])
        del args[:2]
    if args[:1] != ["fetch"]:
        raise Refused("dependency Git CLI only admits version and exact fetch requests")
    args.pop(0)
    # Native Targo adds this exact depth when it reuses the shallow DB created
    # by the first selected-checkout transfer. No variable depth is admitted.
    allowed = {"--no-tags", "--depth=1", "--verbose", "--progress", "--porcelain", "--quiet", "--no-show-forced-updates", "--force", "--update-head-ok", "--recurse-submodules=no"}
    options = []
    while args and args[0].startswith("--"):
        value = args.pop(0)
        if value not in allowed or value in options:
            raise Refused("dependency Git fetch option is unsupported")
        options.append(value)
    if not {"--no-tags", "--force", "--update-head-ok", "--recurse-submodules=no"}.issubset(options) or len(args) != 2:
        raise Refused("dependency Git fetch requires one exact commit refspec")
    url, refspec = args
    match = re.fullmatch(r"\+([0-9a-f]{40}):refs/commit/([0-9a-f]{40})", refspec)
    if match is None or match[1] != match[2]:
        raise Refused("dependency Git fetch refspec is not the precise Cargo commit form")
    return canonical_url(url), match[1], refspec

def validate_bare_db(owner, db: Path):
    """Cargo's DB has no worktree; its local config is bounded data only."""
    identity = real_directory(db)
    config = db / "config"
    before = regular(config)
    for relative in ("commondir", "gitdir", "objects/info/alternates", "objects/info/http-alternates", "info/grafts", "refs/replace"):
        if os.path.lexists(db / relative):
            raise Refused("dependency Cargo-selected Git DB redirects object custody")
    population = 0
    for root, dirs, files in os.walk(db, followlinks=False):
        for name in dirs + files:
            population += 1
            path = Path(root) / name
            st = path.lstat()
            if (population > 1000000 or stat.S_ISLNK(st.st_mode)
                    or not (stat.S_ISDIR(st.st_mode) or stat.S_ISREG(st.st_mode))
                    or (stat.S_ISREG(st.st_mode) and st.st_nlink != 1)):
                raise Refused("dependency Cargo bare DB contains aliased/special or excessive files")
    raw = local_git(owner, ["config", "--no-includes", "--file", str(config), "--null", "--list"], cwd=Path(db.anchor)).stdout
    allowed = {"core.repositoryformatversion", "core.bare", "core.filemode", "core.logallrefupdates",
               "core.ignorecase", "core.precomposeunicode", "remote.origin.url", "remote.origin.fetch",
               "extensions.objectformat"}
    for key, value in owner["_parse_git_config_records"](raw, db, "Cargo bare DB"):
        key = key.lower()
        if key not in allowed:
            raise Refused("dependency Cargo bare DB config has unsupported authority")
        if key == "extensions.objectformat" and value != "sha1":
            raise Refused("dependency Cargo bare DB has unsupported object format")
        if key == "remote.origin.url":
            canonical_url(value)
    if local_git(owner, ["--git-dir", str(db), "rev-parse", "--is-bare-repository"]).stdout.strip() != b"true":
        raise Refused("dependency Cargo-selected Git DB is not bare")
    actual = local_git(owner, ["--git-dir", str(db), "rev-parse", "--absolute-git-dir"]).stdout.decode().strip()
    common = local_git(owner, ["--git-dir", str(db), "rev-parse", "--git-common-dir"]).stdout.decode().strip()
    if Path(actual) != db or Path(common) != db or regular(config) != before or real_directory(db) != identity:
        raise Refused("dependency Cargo bare DB custody changed")

def cached_commit(owner, cache: Path, oid: str):
    """Find exact content in actual owned DBs; no guessed Cargo identifiers."""
    exact_oid(oid)
    root = cache / "git/db"
    if not root.exists() and not root.is_symlink():
        return None
    real_directory(root)
    for db in sorted(root.iterdir()):
        real_directory(db)
        validate_bare_db(owner, db)
        row = local_git(owner, ["--git-dir", str(db), "cat-file", "--batch-check"], input_bytes=(oid + "\n").encode()).stdout.decode().strip()
        if row == oid + " missing":
            continue
        if not re.fullmatch(oid + r" commit [0-9]+", row):
            raise Refused("owned Cargo cache has a noncommit or malformed requested object")
        return db
    return None

def git_entry(policy_path: Path, argv: list[str]):
    before = regular(policy_path)
    policy = json.loads(policy_path.read_text())
    if policy.get("schema") != 3:
        raise Refused("dependency transport policy schema is unsupported")
    source = Path(policy["source"])
    if digest(Path(__file__)) != policy["helper_sha256"]:
        raise Refused("dependency Git transport helper changed")
    orchestration = Path(policy.get("orchestration_source", str(source)))
    if orchestration != source:
        real_directory(orchestration)
        if policy.get("manifest_selection") is None or Path(__file__).resolve().parents[1] != orchestration:
            raise Refused("independent dependency Source lost its Trust orchestration owner")
    owner = owner_api(orchestration, policy["owner_sha256"], policy["identity_owner_sha256"], policy["loader_sha256"])
    owner["_dependency_deadline"] = policy["deadline"]
    owner["_dependency_ceiling"] = policy.get("ceiling_seconds")
    if argv == ["--version"]:
        result = local_git(owner, argv)
        sys.stdout.buffer.write(result.stdout)
        return
    selection = policy.get("manifest_selection")
    if selection is not None:
        if (not isinstance(selection, dict) or set(selection) != {"scope", "manifests", "tracked_inputs", "repositories"}
                or not isinstance(selection["tracked_inputs"], dict) or not selection["tracked_inputs"]):
            raise Refused("explicit dependency manifest selection is malformed")
        for name, expected in selection["tracked_inputs"].items():
            if (not isinstance(name, str) or not isinstance(expected, str)
                    or any(part in {"", ".", "..", ".git"} for part in name.split("/"))
                    or name.startswith("/") or "\\" in name):
                raise Refused("selected dependency Source input is malformed")
            path = source / name
            if (path.is_symlink() or not path.is_file() or path.resolve(strict=True) != path
                    or digest(path) != expected):
                raise Refused("selected dependency Source input differs from its prepared policy")
    gc = argv == ["gc", "--auto"]
    if not gc:
        url, oid, refspec = parse_fetch(argv)
        key = url + "#" + oid
        if key not in policy["stages"]:
            raise Refused("dependency Git request is outside the inspected exact source closure")
    cache = Path(policy["cache"])
    if list(real_directory(cache)) != policy["cache_identity"]:
        raise Refused("dependency Cargo cache root changed")
    db_text = os.environ.get("GIT_DIR", "")
    db = Path(db_text)
    real_directory(db)
    base = cache / "git/db"
    if db.parent != base or db.name in {"", ".", ".."} or Path.cwd() != db:
        raise Refused("dependency Git request must retain its exact Cargo-selected bare DB and cwd")
    if any(name in os.environ for name in ("GIT_WORK_TREE", "GIT_COMMON_DIR", "GIT_NAMESPACE", "GIT_INDEX_FILE", "GIT_OBJECT_DIRECTORY", "GIT_ALTERNATE_OBJECT_DIRECTORIES")):
        raise Refused("dependency Git request has redirected repository custody")
    # Validate the actual DB, not a guessed Cargo URL-hash identifier.
    validate_bare_db(owner, db)
    if gc:
        local_git(owner, ["--git-dir", str(db), "gc", "--auto"], bounded=True,
                  label=f"git gc --auto of Cargo's database {db.name}", paths=(db,))
        if regular(policy_path) != before:
            raise Refused("dependency transport policy changed during local gc")
        return
    # Agh retains ancestry metadata and the selected checkout bodies, not every
    # historical body. Let native Git export that exact checkout with its own
    # fresh shallow boundary; a full-history upload-pack would demand omitted
    # obsolete objects. Missing selected bodies still make the native fetch fail.
    # Native Cargo can reinitialize a shallow DB before each requested pin.
    # Restore every already-inspected pin for this URL on each callback so its
    # final DB covers the original whole offline envelope. Fetch the requested
    # pin last to retain Cargo's precise FETCH_HEAD contract. Other URLs and
    # uninspected commits are outside this transfer, not a second resolver.
    pins = []
    for stage_key, stage in policy["stages"].items():
        if stage_key.startswith(url + "#"):
            pin = exact_oid(stage_key[len(url) + 1:])
            if stage["oid"] != pin:
                raise Refused("dependency inspected source pin differs from its policy key")
            pins.append((pin, stage))
    if not pins or len(pins) > MAX_REPOSITORIES:
        raise Refused("dependency inspected source pin set exceeds its finite bounds")
    for pin, stage in sorted(pins, key=lambda row: (row[0] == oid, row[0])):
        origin = Path(stage["path"])
        identity = owner["_submodule_file_identity"](origin)
        if list(identity[:3]) != stage["identity"]:
            raise Refused("dependency inspected source stage changed")
        owner["_validate_staged_submodule"](origin, identity)
        if local_git(owner, ["-C", str(origin), "rev-parse", "--verify", stage["ref"]]).stdout.decode().strip() != pin:
            raise Refused("dependency inspected source ref changed")
        local_git(owner, ["-c", "protocol.file.allow=always", "--git-dir", str(db), "fetch",
            "--no-tags", "--depth=1", "--force", "--update-head-ok", "--recurse-submodules=no",
            str(origin), "+" + pin + ":refs/commit/" + pin], bounded=True, acquisition=True,
            label=f"the local transfer of {url} {pin[:12]} into Cargo's database {db.name}", paths=(db,))
    for pin, _stage in pins:
        actual = local_git(owner, ["--git-dir", str(db), "rev-parse", "--verify", "refs/commit/" + pin]).stdout.decode().strip()
        if actual != pin:
            raise Refused("dependency local self-fetch did not preserve every inspected source ref")
    if not (db / "FETCH_HEAD").read_text().startswith(oid + "\t"):
        raise Refused("dependency local self-fetch did not preserve the exact Cargo ref/FETCH_HEAD")
    if regular(policy_path) != before:
        raise Refused("dependency transport policy changed during local self-fetch")

def prepare_profile_cli(argv: list[str]) -> None:
    parser = argparse.ArgumentParser(description="Prepare Agh-only Git transport for explicit locked native inputs; fetch no registry crates and compile nothing.")
    parser.add_argument("--source", required=True, type=Path)
    parser.add_argument("--orchestration-source", type=Path,
                        help="Trust checkout running this helper for an independent committed workspace")
    parser.add_argument("--work", required=True, type=Path)
    parser.add_argument("--cargo-home", required=True, type=Path)
    parser.add_argument("--manifest", required=True, action="append")
    parser.add_argument("--checkout-cache", metavar="URL#COMMIT=/absolute/repository", action="append", default=[],
                        help="lend read-only Git object data to one exact locked or active Gitlink source")
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--timeout", type=float, default=900)
    args = parser.parse_args(argv)
    if not 0 < args.timeout <= 3600:
        raise Refused("selected dependency transport requires a finite timeout of at most 3600 seconds")
    source = args.source.resolve(strict=True)
    orchestration = (args.orchestration_source or source).resolve(strict=True)
    if orchestration != source and Path(__file__).resolve().parents[1] != orchestration:
        raise Refused("independent dependency Source must use the executing Trust orchestration checkout")
    work = args.work.resolve(strict=True)
    cache = args.cargo_home.resolve(strict=True)
    for path in (source, orchestration, work, cache):
        real_directory(path)
    if args.output.exists() or args.output.is_symlink():
        raise Refused("selected dependency transport result already exists")
    owner = owner_api(orchestration)
    owner["_reject_local_git_execution_authority"](source)
    closure, _ = source_owner(orchestration / "scripts/bootstrap_dependency_closure.py",
                              "selected_dependency_source_inputs")
    environment = dict(os.environ, CARGO_HOME=str(cache))
    policy_path, policy = prepare_profile(source, work, cache, closure, owner, environment,
        manifest_paths=args.manifest, deadline=time.monotonic() + args.timeout,
        orchestration_source=orchestration, checkout_cache_specs=args.checkout_cache)
    result = {"schema": "trust.selected-dependency-git-profile.v1", "source": str(source),
              "policy": str(policy_path), "policy_sha256": digest(policy_path),
              "manifest_selection": policy["manifest_selection"],
              "source_inputs_sha256": policy["source_inputs_sha256"],
              "scope": "Source transport only. Use the same recorded manifests for ordinary native Targo requests and offline replay under the registry HTTP gate; this is not dependency availability, native/SDK/proof or release admission."}
    if orchestration != source:
        result["orchestration_source"] = str(orchestration)
    with args.output.open("x") as output:
        json.dump(result, output, indent=2)
        output.write("\n")
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    try:
        if sys.argv[1:2] == ["prepare-profile"]:
            prepare_profile_cli(sys.argv[2:])
        else:
            if len(sys.argv) < 4 or sys.argv[1] != "--policy" or sys.argv[3] != "--":
                raise Refused("dependency Git helper requires its exact policy and literal argv")
            git_entry(Path(sys.argv[2]), sys.argv[4:])
    except (RuntimeError, OSError, ValueError, subprocess.SubprocessError) as error:
        print(f"dependency Git transport refused: {error}", file=sys.stderr)
        sys.exit(2)
