#!/usr/bin/env python3
"""Agh-only exact Git objects and local-only native Cargo Git handoff.

Cargo owns patch/version/lock resolution. Daily's separate CONNECT gate closes
its pre-CLI HTTP route; only source commits in the actual selected owner locks
or a checked exact-parent Gitlink ledger may be acquired here. No credential
extraction, raw GitHub Git/HTTP fallback or proof authority is provided.
"""
from __future__ import annotations
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
                "src/bootstrap/stage0_identity.py": identity_before}
    loader = loader_owner["BoundSourceLoader"](source, manifest)
    result = loader.module("daily_dependency_git_owner", path).__dict__
    loader.recheck()
    if (digest(identity) != identity_before
            or result.get("_IDENTITY_SOURCE_SHA256") != identity_before):
        raise Refused("dependency Git source owner changed while loading")
    return result

def local_acquisition_command(args):
    """Only the two fixed local source-copy fetch forms may use the bulk limit."""
    if (len(args) == 10 and args[:5] == ["-c", "protocol.file.allow=always", "-c",
            "fetch.fsckObjects=true", "-C"] and args[6:8] == ["fetch", "--no-tags"]):
        return (Path(args[5]).is_absolute() and Path(args[8]).is_absolute()
                and re.fullmatch(r"\+([0-9a-f]{40}):refs/agh/trust-daily-dependencies/\1", args[9]) is not None)
    if (len(args) == 11 and args[:3] == ["-c", "protocol.file.allow=always", "--git-dir"]
            and args[4:9] == ["fetch", "--no-tags", "--force", "--update-head-ok", "--recurse-submodules=no"]):
        return (Path(args[3]).is_absolute() and Path(args[9]).is_absolute()
                and re.fullmatch(r"\+([0-9a-f]{40}):refs/commit/\1", args[10]) is not None)
    return False


def local_git(owner, args, *, cwd=None, bounded=False, input_bytes=None, acquisition=False):
    if acquisition and not bounded:
        raise Refused("dependency Git acquisition requires process-tree custody")
    if acquisition and not local_acquisition_command(args):
        raise Refused("dependency Git acquisition is not a fixed local source fetch")
    remaining = owner.get("_dependency_deadline", time.monotonic() + 120) - time.monotonic()
    if remaining <= 0:
        raise Refused("dependency Git transport deadline exhausted")
    env = owner["_provenance_git_environment"]()
    env["GIT_NO_LAZY_FETCH"] = "1"
    command = owner["_controlled_git_command"](
        ["-c", "protocol.allow=never", "-c", "protocol.https.allow=never",
         "-c", "gc.autoDetach=false", "-c", "maintenance.auto=false", *args])
    if bounded:
        # A local source acquisition can validate a large complete Git history.
        # Give these two fixed fetch sites the same finite ceiling as Agh, while
        # retaining the enclosing preparation deadline and process-tree cleanup.
        limit = 600 if acquisition else 120
        result = owner["_run_submodule_update_process"](command, environment=env, timeout_seconds=min(limit, remaining), credential_gh=None)
        if result.returncode:
            raise Refused("fixed local dependency Git process did not complete successfully")
        return result
    return subprocess.run(command,
        cwd=cwd, env=env, input=input_bytes, capture_output=True, check=True, timeout=min(60, remaining))

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
    raw = local_git(owner, ["-C", str(stage), "ls-tree", "-r", "-z", oid]).stdout
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


def prepare_profile(source: Path, work: Path, cache: Path, closure, owner, environment: dict,
                    *, acquire=None, deadline=None):
    """Acquire only actual owner-lock commits and exact-parent Gitlink trees.

    No Cargo dependency/patch resolver is reimplemented. Unknown native requests
    later fail the local-only CLI; the mandatory HTTP gate denies pre-CLI GitHub.
    """
    deadline = time.monotonic() + 900 if deadline is None else deadline
    owner = {**owner, "_dependency_deadline": deadline}
    manifests = closure["stage0_bootstrap_manifest_roots"](source)
    if not manifests:
        raise Refused("dependency recipe manifest envelope is empty")
    paths = closure["_source_inputs"](source, manifests, environment, require_lockfiles=True)
    paths = [*paths, source / "src/bootstrap/stage0_identity.py", source / "scripts/seed_custody_source.py"]
    snapshot = closure["_snapshot"](paths)
    if snapshot[str(source / "src/bootstrap/stage0_identity.py")] is None:
        raise Refused("dependency Git transitive source owner is missing")
    graph = owner["_Stage0ManifestGraph"](source)
    graph.collect(manifests)
    if graph.inconclusive:
        raise Refused("dependency manifest profile is inconclusive: " + "; ".join(sorted(graph.inconclusive)))
    locks = sorted({graph.owner(entry).with_name("Cargo.lock") for entry in manifests})
    pending, roots = {}, []
    for lock in locks:
        import tomllib
        for url, oid, name in lock_specs(tomllib.loads(lock.read_text()), package_names=True):
            key = url + "#" + oid
            pending[(url, oid)] = 0
            roots.append({"url": url, "oid": oid, "name": name, "owner_lock": str(lock.relative_to(source))})
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
        def run_agh(command, environment):
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise Refused("dependency Agh acquisition deadline exhausted")
            result = owner["_run_submodule_update_process"](command, environment=environment,
                timeout_seconds=min(600, remaining), credential_gh=None)
            if result.returncode:
                raise Refused("owner-routed dependency Agh acquisition failed")
        cached = cached_commit(owner, cache, oid) if acquire is None else None
        if cached is None:
            if environment.get("CARGO_NET_OFFLINE") == "true":
                raise Refused("offline dependency policy has no exact owned Git object")
            receipt = owner["_agh_source_fetch"](url, stage, oid, ref, execute=acquire or run_agh)
            receipt["method"] = "owner-routed-agh"
        else:
            local_git(owner, ["-c", "protocol.file.allow=always", "-c", "fetch.fsckObjects=true",
                "-C", str(stage), "fetch", "--no-tags", str(cached), "+" + oid + ":" + ref], bounded=True, acquisition=True)
            validate_bare_db(owner, cached)
            receipt = {"method": "exact-owned-cargo-cache", "source": oid, "private_ref": ref,
                       "commit": oid, "repository": url, "cache_db": str(cached)}
        owner["_validate_staged_submodule"](stage, identity)
        actual = local_git(owner, ["-C", str(stage), "rev-parse", "--verify", ref]).stdout.decode().strip()
        if actual != oid or local_git(owner, ["-C", str(stage), "cat-file", "-t", oid]).stdout.strip() != b"commit":
            raise Refused("dependency source ref is not the exact commit")
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
    if closure["_snapshot"](paths) != snapshot or time.monotonic() > deadline:
        raise Refused("dependency source profile changed or exceeded its deadline")
    policy = {"schema": 3, "source": str(source), "owner_sha256": digest(source / "scripts/recreate_bootstrap.py"),
              "loader_sha256": snapshot[str(source / "scripts/seed_custody_source.py")],
              "identity_owner_sha256": digest(source / "src/bootstrap/stage0_identity.py"),
              "helper_sha256": digest(Path(__file__)), "cache": str(cache), "cache_identity": list(real_directory(cache)),
              "stages": stages, "source_inputs_sha256": snapshot, "roots": roots, "gitlinks": gitlinks,
              "locks": [str(p.relative_to(source)) for p in locks], "acquisitions": acquisitions, "deadline": deadline}
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
    allowed = {"--no-tags", "--verbose", "--progress", "--porcelain", "--quiet", "--no-show-forced-updates", "--force", "--update-head-ok", "--recurse-submodules=no"}
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
    owner = owner_api(source, policy["owner_sha256"], policy["identity_owner_sha256"], policy["loader_sha256"])
    owner["_dependency_deadline"] = policy["deadline"]
    if argv == ["--version"]:
        result = local_git(owner, argv)
        sys.stdout.buffer.write(result.stdout)
        return
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
        local_git(owner, ["--git-dir", str(db), "gc", "--auto"], bounded=True)
        if regular(policy_path) != before:
            raise Refused("dependency transport policy changed during local gc")
        return
    stage = policy["stages"][key]
    origin = Path(stage["path"])
    identity = owner["_submodule_file_identity"](origin)
    if list(identity[:3]) != stage["identity"]:
        raise Refused("dependency inspected source stage changed")
    owner["_validate_staged_submodule"](origin, identity)
    if local_git(owner, ["-C", str(origin), "rev-parse", "--verify", stage["ref"]]).stdout.decode().strip() != oid:
        raise Refused("dependency inspected source ref changed")
    result = local_git(owner, ["-c", "protocol.file.allow=always", "--git-dir", str(db), "fetch",
                        "--no-tags", "--force", "--update-head-ok", "--recurse-submodules=no", str(origin), refspec], bounded=True, acquisition=True)
    actual = local_git(owner, ["--git-dir", str(db), "rev-parse", "--verify", "refs/commit/" + oid]).stdout.decode().strip()
    if actual != oid or not (db / "FETCH_HEAD").read_text().startswith(oid + "\t"):
        raise Refused("dependency local self-fetch did not preserve the exact Cargo ref/FETCH_HEAD")
    if regular(policy_path) != before:
        raise Refused("dependency transport policy changed during local self-fetch")

if __name__ == "__main__":
    try:
        if len(sys.argv) < 4 or sys.argv[1] != "--policy" or sys.argv[3] != "--":
            raise Refused("dependency Git helper requires its exact policy and literal argv")
        git_entry(Path(sys.argv[2]), sys.argv[4:])
    except (RuntimeError, OSError, ValueError, subprocess.SubprocessError) as error:
        print(f"dependency Git transport refused: {error}", file=sys.stderr)
        sys.exit(2)
