#!/usr/bin/env python3
"""check_patch_binds.py — a `[patch]` that does not BIND is worse than no patch.

Trust's root manifest redirects several git URLs to vendored first-party paths
so each patched package binding resolves exactly once, from that path:

    [patch."https://github.com/alabsystems/clean.git"]
    clean-kernel = { path = "first-party/clean/crates/clean-kernel" }

Cargo applies such an entry only when the replacement's VERSION satisfies the
dependency's version requirement. When a submodule pin moves across a version
bump, the requirement stops being satisfied, the patch silently stops applying,
and cargo reaches for the original git rev instead — producing a SECOND copy of
the crate that the patch existed to prevent. Nothing warns; `--locked` fails
with a message about updating the lock file, which reads like lock staleness.

That is what happened on 2026-08-19: `8dddf6c755` moved `first-party/clean` to
`bc0941514` as "fmt-only", but that rev carries clean's `0.1.0 -> 0.2.0`
workspace bump. `Cargo.lock` still records `clean-kernel 1.5.0`.

This gate reads only files in the superproject, so it costs milliseconds and
runs anywhere. For every `[patch.<url>] <name> = { path = P }`:

  * P/Cargo.toml's version (resolving `version.workspace = true` against the
    nearest enclosing `[workspace.package]`) must MATCH exactly one path-owned
    `[[package]]` entry of that name and version in Cargo.lock -- otherwise
    `--locked` cannot hold; and
  * Cargo.lock must not hold another entry of that name and version from the
    source named by the patch table -- otherwise that patched source still
    resolved alongside its replacement.

Cargo's package identity includes the source. A registry or unrelated-git
package with the same name and version is therefore allowed beside the path
replacement, as is another version of the same name. Only a sourced row whose
canonical source is the source being patched is the duplicate this gate is
meant to catch. Network-Git spellings outside the deliberately audited URL
subset fail closed; they are never guessed to be unrelated.

Exit 0 iff every patch entry binds. Author: Andrew Yates | Apache-2.0
"""
from __future__ import annotations

import pathlib
import re
import subprocess
import sys
from urllib.parse import urlsplit, urlunsplit

PATCH_HEADER = re.compile(r'^\[patch\.(?:crates-io|"([^"]+)")\]\s*$')
TABLE_HEADER = re.compile(r"^\[")
ENTRY = re.compile(r'^\s*([A-Za-z0-9_-]+)\s*=\s*\{(.*)\}\s*$')
PATH_FIELD = re.compile(r'path\s*=\s*"([^"]+)"')
VERSION_FIELD = re.compile(r'^\s*version\s*=\s*"([^"]+)"', re.M)
WORKSPACE_VERSION = re.compile(r'^\s*version\s*\.?\s*workspace\s*=\s*true', re.M)
DNS_LABEL = re.compile(r"[A-Za-z0-9](?:[A-Za-z0-9-]*[A-Za-z0-9])?")
DNS_FINAL_LABEL = re.compile(r"[A-Za-z](?:[A-Za-z0-9-]*[A-Za-z0-9])?")
URL_PATH_SEGMENT = re.compile(r"[A-Za-z0-9._~!$&'()*+,;=:@-]*")


def repo_root() -> pathlib.Path:
    """The workspace to check: argv[1] if given, else this script's own repo."""
    if len(sys.argv) > 1:
        return pathlib.Path(sys.argv[1]).resolve()
    out = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        cwd=pathlib.Path(__file__).resolve().parent,
        capture_output=True, text=True, check=True,
    )
    return pathlib.Path(out.stdout.strip())


def patch_entries(manifest: pathlib.Path):
    """(url, crate_name, path) for every `name = { path = ... }` under [patch.*]."""
    url = None
    for line in manifest.read_text().splitlines():
        header = PATCH_HEADER.match(line)
        if header:
            url = header.group(1) or "crates-io"
            continue
        if url is not None and TABLE_HEADER.match(line):
            url = None
            continue
        if url is None:
            continue
        entry = ENTRY.match(line)
        if not entry:
            continue
        path = PATH_FIELD.search(entry.group(2))
        if path:
            yield url, entry.group(1), path.group(1)


def manifest_version(root: pathlib.Path, rel: str) -> tuple[str | None, str]:
    """Declared version of the crate at `rel`, and where it came from."""
    crate = root / rel / "Cargo.toml"
    if not crate.is_file():
        return None, f"no manifest at {rel}/Cargo.toml"
    text = crate.read_text()
    # The crate's own `[package] version = "..."` wins over anything later in
    # the file (a `[dependencies] foo = { version = ... }` must not be read as
    # the package version), so scan only the [package] table.
    package = re.split(r"^\[", text, flags=re.M)
    for chunk in package:
        if not chunk.startswith("package]"):
            continue
        own = VERSION_FIELD.search(chunk)
        if own:
            return own.group(1), f"{rel}/Cargo.toml"
        if WORKSPACE_VERSION.search(chunk):
            break
    # `version.workspace = true`: walk up to the nearest [workspace.package].
    here = (root / rel).resolve()
    while True:
        candidate = here / "Cargo.toml"
        if candidate.is_file():
            body = candidate.read_text()
            for chunk in re.split(r"^\[", body, flags=re.M):
                if chunk.startswith("workspace.package]"):
                    ws = VERSION_FIELD.search(chunk)
                    if ws:
                        return ws.group(1), f"{candidate.relative_to(root)} [workspace.package]"
        if here == here.parent or here == root:
            return None, f"{rel}: version.workspace = true but no [workspace.package] above it"
        here = here.parent


def lock_versions(lock: pathlib.Path) -> dict[str, list[tuple[str, str | None]]]:
    """name -> [(version, source-or-None)] for every [[package]] in Cargo.lock."""
    found: dict[str, list[tuple[str, str | None]]] = {}
    name = version = source = None
    for line in lock.read_text().splitlines() + ["[[package]]"]:
        if line.strip() == "[[package]]":
            if name and version:
                found.setdefault(name, []).append((version, source))
            name = version = source = None
            continue
        key, _, raw = line.partition(" = ")
        value = raw.strip().strip('"')
        if key == "name":
            name = value
        elif key == "version":
            version = value
        elif key == "source":
            source = value
    return found


def canonical_url_path(path: str) -> str:
    """Apply the base-URL dot-segment normalization used by Cargo's URL parser."""
    normalized: list[str] = []
    for segment in path.split("/"):
        folded = segment.lower()
        if folded in {".", "%2e"}:
            continue
        if folded in {"..", ".%2e", "%2e.", "%2e%2e"}:
            # Keep the first empty component as the absolute-path root, but an
            # additional empty component is an ordinary segment and `..`
            # removes it (for example `/owner//../widget`).
            if len(normalized) > 1:
                normalized.pop()
            continue
        normalized.append(segment)
    return "/".join(normalized)


def audited_dns_hostname(hostname: str) -> bool:
    """Whether `hostname` is in the non-IP ASCII DNS subset audited below."""
    labels = hostname.split(".")
    return (
        len(labels) >= 2
        and all(DNS_LABEL.fullmatch(label) for label in labels)
        and DNS_FINAL_LABEL.fullmatch(labels[-1]) is not None
    )


def canonical_git_source(source: str) -> str | None:
    """Canonical repository URL for a Cargo git source or `[patch]` URL.

    Lock sources add a `git+` transport marker plus query/commit material;
    Cargo also treats a terminal `.git` and slash as repository spelling, not
    package identity. Cargo additionally special-cases GitHub: every supported
    transport becomes HTTPS and the repository path is lower-cased. Preserve
    transport, authority, port, and path for other hosts; HTTPS and SSH
    repositories are not generally assumed interchangeable.

    This intentionally accepts only the repository's auditable network-Git
    subset: ASCII http/https/ssh/git URLs, an optional simple username, a
    non-IP DNS hostname whose final label starts with a letter, an optional
    numeric port, and RFC path characters whose only percent escapes are
    URL-parser dot segments. Callers treat `None` as a gate error, never as
    evidence that two sources differ. That is safer than partially emulating
    WHATWG URL parsing for file URLs, IDNA, IPv4/IPv6, passwords, backslashes,
    or URL-encoded arbitrary path bytes.
    """
    raw = source.removeprefix("git+")
    base = raw.split("#", 1)[0].split("?", 1)[0]
    if not base.isascii() or "\\" in base or any(ch.isspace() for ch in base):
        return None
    parsed = urlsplit(raw)
    if parsed.scheme not in {"http", "https", "ssh", "git"} or not parsed.netloc:
        return None
    hostname = parsed.hostname
    if hostname is None or not hostname.isascii() or not audited_dns_hostname(hostname):
        return None
    if parsed.password is not None:
        return None
    if parsed.username is not None and not re.fullmatch(r"[A-Za-z0-9._~-]+", parsed.username):
        return None
    try:
        port = parsed.port
    except ValueError:
        return None

    original_scheme = parsed.scheme.lower()
    scheme = original_scheme
    for segment in parsed.path.split("/"):
        if "%" in segment:
            if segment.lower() not in {"%2e", ".%2e", "%2e.", "%2e%2e"}:
                return None
        elif URL_PATH_SEGMENT.fullmatch(segment) is None:
            return None
    path = canonical_url_path(parsed.path)
    if path.endswith("/"):
        path = path[:-1]
    if hostname.lower() == "github.com":
        # Match Cargo's CanonicalUrl GitHub rule exactly: protocol differences
        # and repository-path case do not create distinct package sources.
        scheme = "https"
        path = path.lower()
    if path.endswith(".git"):
        path = path[:-4]

    # URL schemes and DNS names are case-insensitive. Preserve raw userinfo,
    # but rebuild the host component so mixed-case host spellings compare
    # equally without accidentally rewriting matching text in the userinfo.
    userinfo, separator, _ = parsed.netloc.rpartition("@")
    prefix = f"{userinfo}@" if separator else ""
    rendered_host = hostname.lower()
    if ":" in rendered_host:
        rendered_host = f"[{rendered_host}]"
    authority = f"{prefix}{rendered_host}"
    is_default_port = (
        (original_scheme == "http" and port == 80)
        or (original_scheme == "https" and port == 443)
        or (scheme == "http" and port == 80)
        or (scheme == "https" and port == 443)
    )
    if port is not None and not is_default_port:
        authority += f":{port}"
    return urlunsplit((scheme, authority, path, "", ""))


def source_patch_relation(patch_source: str, lock_source: str) -> bool | None:
    """True=same source, False=provably distinct, None=unsupported spelling."""
    if patch_source == "crates-io":
        if lock_source in {
            "registry+https://github.com/rust-lang/crates.io-index",
            "sparse+https://index.crates.io/",
        }:
            return True
        if lock_source.startswith(("registry+", "sparse+")):
            return False
        if lock_source.startswith("git+"):
            return False if canonical_git_source(lock_source) is not None else None
        return None
    if lock_source.startswith(("registry+", "sparse+")):
        return False
    if not lock_source.startswith("git+"):
        return None
    patch = canonical_git_source(patch_source)
    locked = canonical_git_source(lock_source)
    if patch is None or locked is None:
        return None
    return patch == locked


def main() -> int:
    root = repo_root()
    manifest, lock = root / "Cargo.toml", root / "Cargo.lock"
    if not lock.is_file():
        print(f"check_patch_binds: no Cargo.lock at {lock}", file=sys.stderr)
        return 1
    locked = lock_versions(lock)

    problems: list[str] = []
    checked = 0
    skipped = 0
    coexisting = 0
    for url, name, rel in patch_entries(manifest):
        # An un-checked-out submodule is a DIFFERENT condition, owned by
        # check_pin_coherence.sh. Failing here too would only teach lanes to
        # ignore this gate in every worktree that has not run `submodule update`.
        if not (root / rel / "Cargo.toml").is_file():
            skipped += 1
            continue
        if url != "crates-io" and canonical_git_source(url) is None:
            checked += 1
            problems.append(
                f"UNSUPPORTED [patch.\"{url}\"] {name} -> {rel}\n"
                "            patch source is outside the gate's audited network-Git URL subset;\n"
                "            refusing to guess at Cargo source identity."
            )
            continue
        declared, origin = manifest_version(root, rel)
        checked += 1
        if declared is None:
            problems.append(
                f"UNREADABLE  [patch.\"{url}\"] {name} -> {rel}\n"
                f"            {origin}"
            )
            continue
        entries = locked.get(name, [])
        if not entries:
            problems.append(
                f"UNLOCKED    [patch.\"{url}\"] {name} -> {rel}\n"
                f"            manifest says {declared} ({origin}) but Cargo.lock has no\n"
                f"            [[package]] named {name} at all."
            )
            continue
        exact = [(version, source) for version, source in entries if version == declared]
        path_exact = [(version, source) for version, source in exact if source is None]
        source_relations = [
            (version, source, source_patch_relation(url, source))
            for version, source in exact
            if source is not None
        ]
        patched_source_exact = [
            (version, source) for version, source, relation in source_relations if relation is True
        ]
        unsupported_source_exact = [
            (version, source) for version, source, relation in source_relations if relation is None
        ]
        if len(path_exact) != 1:
            shown = ", ".join(f"{v} ({s or 'path'})" for v, s in entries)
            problems.append(
                f"UNBOUND     [patch.\"{url}\"] {name} -> {rel}\n"
                f"            manifest says {declared} ({origin})\n"
                f"            Cargo.lock holds: {shown}\n"
                f"            expected exactly one path-owned {name} {declared}; without it\n"
                f"            the patch is not part of the locked graph."
            )
            continue
        if unsupported_source_exact:
            shown = ", ".join(f"{v} ({s})" for v, s in unsupported_source_exact)
            problems.append(
                f"UNSUPPORTED [patch.\"{url}\"] {name} -> {rel}\n"
                f"            Cargo.lock holds exact-version source spelling(s) outside the\n"
                f"            gate's audited URL subset: {shown}\n"
                "            refusing to classify them as unrelated."
            )
            continue
        if patched_source_exact:
            shown = ", ".join(
                f"{v} ({s or 'path'})" for v, s in path_exact + patched_source_exact
            )
            problems.append(
                f"DUPLICATED  [patch.\"{url}\"] {name} -> {rel}\n"
                f"            Cargo.lock holds path-owned {name} {declared} and the source\n"
                f"            this patch replaces: {shown}\n"
                f"            The patched source still resolving beside its replacement is\n"
                f"            exactly what this gate exists to prevent."
            )
            continue
        coexisting += len(entries) - len(path_exact)

    if problems:
        print("check_patch_binds: FAIL — a [patch] entry does not bind\n", file=sys.stderr)
        if skipped:
            print(f"({skipped} further entries skipped: submodule not checked out)\n", file=sys.stderr)
        for problem in problems:
            print(problem + "\n", file=sys.stderr)
        return 1
    notes = []
    if coexisting:
        notes.append(f"{coexisting} unrelated-source/other-version package row(s) coexist")
    if skipped:
        notes.append(f"{skipped} skipped: submodule not checked out")
    note = f" ({'; '.join(notes)})" if notes else ""
    print(f"check_patch_binds: OK — {checked} path-redirecting [patch] entries bind{note}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
