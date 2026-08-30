#!/bin/sh
""":"
for candidate in python3.14 python3.13 python3.12 python3.11 python3; do
    if command -v "$candidate" >/dev/null 2>&1 \
        && "$candidate" -c 'import sys; raise SystemExit(sys.version_info < (3, 11))' 2>/dev/null; then
        exec "$candidate" "$0" "$@"
    fi
done
echo "check_dependency_cycle_anchor.py requires Python 3.11+ (tomllib)" >&2
exit 2
":"""
__doc__ = """Validate the committed first-party dependency constellation receipt.

The validator derives its authority from committed Cargo/Lake surfaces and
root gitlinks.  The receipt is an exact inventory to compare with that
independent observation; it is never used as the source of dependency edges.

Python 3.11 or newer is required because manifests are parsed with tomllib.
Normal validation is deterministic and offline.  ``--verify-remote`` adds a
non-mutating ``git ls-remote`` check that every terminal pin is remote main.
"""

import argparse
import configparser
import fnmatch
import json
import os
import posixpath
import re
import subprocess
import sys
from pathlib import Path, PurePosixPath
from typing import Any, NoReturn, Sequence
from urllib.parse import parse_qs, unquote, urlsplit, urlunsplit

try:
    import tomllib
except ModuleNotFoundError as error:  # pragma: no cover - exercised by CLI only
    raise SystemExit(
        "check_dependency_cycle_anchor.py requires Python 3.11+ (tomllib)"
    ) from error


SCHEMA = "trust.constellation.first-party.v2"
SELF_SENTINEL = "CONTAINING_COMMIT"
RECEIPT_PATH = "docs/audits/first-party-constellation-v2.json"
EXCLUSIONS_PATH = "docs/audits/first-party-constellation-exclusions-v1.json"
EXCLUSIONS_SCHEMA = "trust.constellation.exclusions.v1"
GENERATION_CUT_REASON = (
    "finite exact-SHA generation cut; dependency predates this consumer generation"
)
SHA_RE = re.compile(r"[0-9a-f]{40}\Z")

SUBMODULES = {
    "ay": ("first-party/ay", "https://github.com/alabsystems/ay.git"),
    "clean": ("first-party/clean", "https://github.com/alabsystems/clean.git"),
    "ny": ("first-party/ny", "https://github.com/alabsystems/ny.git"),
    "trust-cg": (
        "first-party/trust-cg",
        "https://github.com/alabsystems/trust-cg.git",
    ),
    "trust-ir": (
        "first-party/trust-ir",
        "https://github.com/alabsystems/trust-ir.git",
    ),
    "trust-mc": (
        "first-party/trust-mc",
        "https://github.com/alabsystems/trust-mc.git",
    ),
    "trust-vc": (
        "first-party/trust-vc",
        "https://github.com/alabsystems/trust-vc.git",
    ),
    "trust-wp": (
        "first-party/trust-wp",
        "https://github.com/alabsystems/trust-wp.git",
    ),
    "ty": ("first-party/ty", "https://github.com/alabsystems/ty.git"),
}
CONSUMERS = {"trust", *SUBMODULES}
SURFACE_KINDS = {
    "cargo-git",
    "cargo-path",
    "cargo-patch-git",
    "cargo-patch-path",
    "cargo-replace-git",
    "cargo-replace-path",
    "cargo-lock",
    "lake-require",
    "lake-lock",
    "lake-path",
    "lake-path-lock",
    "proof-identity",
}
SURFACE_KEYS = {
    "id",
    "repository",
    "scope",
    "kind",
    "path",
    "locator",
    "dependency",
    "package",
    "url",
    "rev",
    "dependency_path",
    "subdir",
    "optional",
}
NY_IDENTITY_PATHS = {
    "crates/ny-cert/SPEC.md",
    "crates/ny-cert/proofs/README.md",
    "crates/ny-cert/proofs/lean/PROVENANCE.md",
    "crates/ny-cert/src/cite_check.rs",
    "crates/ny-cert/proofs/cite-map.json",
    "crates/ny-cert/proofs/lean/lakefile.toml",
    "crates/ny-cert/proofs/lean/lake-manifest.json",
}


class AnchorError(RuntimeError):
    """A fail-closed dependency-constellation finding."""


def fail(message: str) -> NoReturn:
    raise AnchorError(message)


def run_git(repo: Path, args: Sequence[str], *, check: bool = True) -> bytes:
    command = ["git", "-C", str(repo), *args]
    completed = subprocess.run(
        command,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if check and completed.returncode != 0:
        detail = (completed.stderr or completed.stdout).decode("utf-8", "replace").strip()
        fail(f"{' '.join(command)} failed: {detail or f'exit {completed.returncode}'}")
    return completed.stdout


def strict_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            fail(f"receipt contains duplicate JSON key {key!r}")
        result[key] = value
    return result


def parse_json(raw: bytes, label: str) -> object:
    try:
        text = raw.decode("utf-8", "strict")
    except UnicodeDecodeError as error:
        fail(f"{label} is not valid UTF-8: {error}")
    try:
        return json.loads(text, object_pairs_hook=strict_object)
    except AnchorError:
        raise
    except (json.JSONDecodeError, RecursionError) as error:
        fail(f"{label} is not valid strict JSON: {error}")


def parse_toml(raw: bytes, label: str) -> dict[str, Any]:
    try:
        text = raw.decode("utf-8", "strict")
    except UnicodeDecodeError as error:
        fail(f"{label} is not valid UTF-8: {error}")
    try:
        value = tomllib.loads(text)
    except tomllib.TOMLDecodeError as error:
        fail(f"{label} is not valid TOML: {error}")
    if not isinstance(value, dict):  # tomllib currently always returns a dict
        fail(f"{label} top level must be a table")
    return value


def decode_text(raw: bytes, label: str) -> str:
    try:
        return raw.decode("utf-8", "strict")
    except UnicodeDecodeError as error:
        fail(f"{label} is not valid UTF-8: {error}")


def repeatedly_unquote(value: str) -> tuple[str, bool]:
    """Percent-decode to a bounded fixed point; flag intentionally deep encodings."""
    decoded = value
    for _ in range(8):
        next_value = unquote(decoded)
        if next_value == decoded:
            return decoded, False
        decoded = next_value
    return decoded, "%" in decoded


def might_reference_first_party(raw: bytes) -> bool:
    """Conservatively identify malformed fixtures that could hide an edge."""
    decoded, excessive = repeatedly_unquote(raw.decode("latin-1").lower())
    if excessive or "alabsystems" in decoded or "first-party/" in decoded:
        return True
    return any(("../" + name) in decoded for name in SUBMODULES)


def require_exact_keys(value: dict[str, object], expected: set[str], label: str) -> None:
    actual = set(value)
    if actual != expected:
        fail(
            f"{label} keys differ: missing={sorted(expected - actual)}, "
            f"extra={sorted(actual - expected)}"
        )


def require_nonempty_string(value: object, label: str) -> str:
    if not isinstance(value, str) or not value.strip():
        fail(f"{label} must be a non-empty string")
    return value


def require_sha(value: object, label: str) -> str:
    if not isinstance(value, str) or SHA_RE.fullmatch(value) is None:
        fail(f"{label} must be one lowercase full 40-hex commit id")
    if value == "0" * 40:
        fail(f"{label} may not be the all-zero object id")
    return value


def require_optional_string(value: object, label: str) -> str | None:
    if value is None:
        return None
    return require_nonempty_string(value, label)


def require_relative_path(value: object, label: str) -> str:
    path = require_nonempty_string(value, label)
    pure = PurePosixPath(path)
    if pure.is_absolute() or path != pure.as_posix() or any(part in {"", ".", ".."} for part in pure.parts):
        fail(f"{label} must be a normalized non-parent relative POSIX path")
    return path


def canonical_json(value: object) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def first_party_url(raw: object, label: str, *, allow_alias: bool = False) -> str | None:
    """Return a repository name, rejecting recognizable non-canonical aliases."""
    if not isinstance(raw, str):
        return None
    value = raw[4:] if raw.startswith("git+") else raw
    for name, (_path, canonical) in SUBMODULES.items():
        if value == canonical:
            return name
    parsed_locator = urlsplit(value)
    has_network_scheme = re.match(r"^[A-Za-z][A-Za-z0-9+.-]*://", value) is not None
    is_scp_locator = re.match(r"^[^/@:\\]+@[^/:\\]+:.+", value) is not None
    is_windows_path = re.match(r"^[A-Za-z]:[\\/]", value) is not None
    if (
        parsed_locator.scheme.lower() == "file"
        or is_windows_path
        or (not has_network_scheme and not is_scp_locator)
    ):
        # Rust's own Cargo fixtures contain synthetic local Git locators such
        # as `[ROOTURL]/git-package`.  They are external test data, not part of
        # the nine-repository authority graph.  Reject only local locators that
        # can name a first-party repository; treating every unrelated local
        # fixture as authority made the old checker unusable on the real tree.
        decoded_local, excessive = repeatedly_unquote(value.lower())
        normalized_local = decoded_local.replace("\\", "/").rstrip("/")
        local_name = PurePosixPath(normalized_local.removeprefix("file://")).name
        if excessive or "first-party/" in normalized_local or local_name in SUBMODULES:
            fail(
                f"{label} uses unsupported local/file Git locator {value!r}; "
                "committed first-party Git authority must use a canonical network URL"
            )
        return None
    match = re.fullmatch(
        r"(?:https?://github\.com/alabsystems/|"
        r"ssh://git@github\.com(?::22)?/alabsystems/|"
        r"git@github\.com:alabsystems/)"
        r"([A-Za-z0-9._-]+?)(?:\.git)?/?",
        value,
    )
    if match is not None and match.group(1) in SUBMODULES:
        if allow_alias:
            return match.group(1)
        expected = SUBMODULES[match.group(1)][1]
        fail(f"{label} uses first-party URL alias {value!r}; expected exactly {expected!r}")
    decoded_value, excessive = repeatedly_unquote(value)
    if excessive:
        fail(f"{label} uses excessively encoded URL authority {value!r}")
    decoded_value = decoded_value.lower()
    if "alabsystems" in decoded_value:
        fail(
            f"{label} uses malformed or out-of-policy first-party URL {value!r}; "
            "only the exact nine canonical repositories are permitted"
        )
    return None


def committed_blob(repo: Path, commit: str, path: str) -> bytes:
    return run_git(repo, ["show", f"{commit}:{path}"])


def committed_tree_entries(repo: Path, commit: str) -> dict[str, tuple[str, str, str]]:
    raw = run_git(repo, ["ls-tree", "-r", "-z", commit])
    entries: dict[str, tuple[str, str, str]] = {}
    for raw_row in raw.split(b"\0"):
        if not raw_row:
            continue
        metadata, separator, raw_path = raw_row.partition(b"\t")
        fields = metadata.split()
        if separator != b"\t" or len(fields) != 3:
            fail(f"malformed committed tree row in {repo}: {raw_row!r}")
        try:
            mode, object_type, oid = (field.decode("ascii", "strict") for field in fields)
            path = raw_path.decode("utf-8", "strict")
        except UnicodeDecodeError as error:
            fail(f"tracked tree inventory in {repo} is not valid UTF-8/ASCII: {error}")
        if path in entries:
            fail(f"committed tree in {repo} repeats path {path!r}")
        entries[path] = (mode, object_type, oid)
    return entries


def require_regular_committed_authority(
    repo: Path, commit: str, path: str, label: str
) -> None:
    entry = committed_tree_entries(repo, commit).get(path)
    if entry is None:
        fail(f"{label} is not committed")
    mode, object_type, _oid = entry
    if object_type != "blob" or mode not in {"100644", "100755"}:
        fail(f"{label} must be a regular committed blob, not mode {mode} type {object_type}")


def committed_submodules(
    repo_root: Path, root_revision: str = "HEAD"
) -> dict[str, tuple[str, str, str]]:
    raw = committed_blob(repo_root, root_revision, ".gitmodules")
    try:
        text = raw.decode("utf-8", "strict")
    except UnicodeDecodeError as error:
        fail(f"committed .gitmodules is not valid UTF-8: {error}")
    parser = configparser.RawConfigParser(strict=True)
    parser.optionxform = str
    try:
        parser.read_string(text)
    except configparser.Error as error:
        fail(f"committed .gitmodules is invalid: {error}")

    declarations: dict[str, tuple[str, str]] = {}
    for section in parser.sections():
        match = re.fullmatch(r'submodule "([^"]+)"', section)
        if match is None:
            fail(f"unexpected committed .gitmodules section {section!r}")
        values = dict(parser.items(section))
        if set(values) != {"path", "url"}:
            fail(f"submodule {section!r} must contain exactly path and url")
        logical_name = match.group(1)
        if logical_name in declarations:
            fail(f"duplicate submodule declaration {logical_name!r}")
        declarations[logical_name] = (values["path"], values["url"])

    expected = {f"first-party/{name}": details for name, details in SUBMODULES.items()}
    if declarations != expected:
        fail(
            "committed .gitmodules differs from exact nine-repository policy: "
            f"missing={sorted(set(expected) - set(declarations))}, "
            f"extra={sorted(set(declarations) - set(expected))}, "
            f"mismatched={sorted(k for k in set(expected) & set(declarations) if expected[k] != declarations[k])}"
        )

    rows: dict[str, tuple[str, str, str]] = {}
    tree = run_git(repo_root, ["ls-tree", "-r", "-z", root_revision])
    gitlinks: dict[str, str] = {}
    for raw_row in tree.split(b"\0"):
        if not raw_row:
            continue
        metadata, separator, raw_path = raw_row.partition(b"\t")
        fields = metadata.split()
        if fields and fields[0] == b"160000":
            if separator != b"\t" or len(fields) != 3 or fields[1] != b"commit":
                fail(f"malformed committed 160000 row {raw_row!r}")
            try:
                path = raw_path.decode("utf-8", "strict")
                commit = fields[2].decode("ascii", "strict")
            except UnicodeDecodeError as error:
                fail(f"malformed committed gitlink row: {error}")
            require_sha(commit, f"gitlink {path}")
            gitlinks[path] = commit
    declared_paths = {path for path, _url in declarations.values()}
    if set(gitlinks) != declared_paths:
        fail(
            "committed 160000 gitlinks differ from exact nine declarations: "
            f"missing={sorted(declared_paths - set(gitlinks))}, "
            f"extra={sorted(set(gitlinks) - declared_paths)}"
        )
    for name, (path, url) in SUBMODULES.items():
        rows[name] = (path, url, gitlinks[path])
    return rows


def validate_nested_submodules(
    repository: str,
    checkout: Path,
    commit: str,
    entries: dict[str, tuple[str, str, str]],
    roots: dict[str, Path],
    symlink_paths: set[Path],
) -> None:
    """Reject nested pins that duplicate the root's nine-repository authority."""
    gitlinks: dict[str, str] = {}
    for path, (mode, object_type, oid) in entries.items():
        if mode != "160000":
            continue
        if object_type != "commit":
            fail(f"{repository} nested gitlink {path} has type {object_type}, not commit")
        require_relative_path(path, f"{repository} nested gitlink path")
        gitlinks[path] = require_sha(oid, f"{repository} nested gitlink {path}")

    if ".gitmodules" not in entries:
        if gitlinks:
            fail(f"{repository} has nested gitlinks without committed .gitmodules")
        return

    raw = committed_blob(checkout, commit, ".gitmodules")
    text = decode_text(raw, f"{repository}:.gitmodules")
    parser = configparser.RawConfigParser(strict=True)
    try:
        parser.read_string(text)
    except configparser.Error as error:
        fail(f"{repository}:.gitmodules is invalid: {error}")
    declarations: dict[str, str] = {}
    for section in parser.sections():
        match = re.fullmatch(r'submodule "([^"]+)"', section, flags=re.IGNORECASE)
        if match is None:
            fail(f"{repository}:.gitmodules has unexpected section {section!r}")
        values = dict(parser.items(section))
        if not isinstance(values.get("path"), str) or not isinstance(values.get("url"), str):
            fail(f"{repository}:.gitmodules section {section!r} requires path and url")
        path = require_relative_path(
            values["path"], f"{repository}:.gitmodules {section}.path"
        )
        if path in declarations:
            fail(f"{repository}:.gitmodules declares duplicate path {path!r}")
        url = values["url"]
        declarations[path] = url

        dependency = first_party_url(url, f"{repository}:.gitmodules {section}.url")
        decoded_url, excessive = repeatedly_unquote(url)
        decoded_url = decoded_url.lower().rstrip("/")
        relative_name = PurePosixPath(decoded_url).name.removesuffix(".git")
        if excessive or dependency is not None or (
            decoded_url.startswith(("./", "../")) and relative_name in SUBMODULES
        ):
            target = dependency if dependency is not None else relative_name or "encoded URL"
            fail(
                f"{repository}:.gitmodules creates unsupported nested first-party "
                f"gitlink authority to {target}"
            )

        mapped = map_dependency_path(
            repository,
            ".gitmodules",
            path,
            roots,
            relative_base=".",
            symlink_paths=symlink_paths,
        )
        if mapped is not None and mapped[0] != repository:
            fail(
                f"{repository}:.gitmodules path {path!r} resolves outside its repository "
                f"into {mapped[0]}"
            )

    if set(declarations) != set(gitlinks):
        fail(
            f"{repository} nested .gitmodules/gitlink paths differ: "
            f"declared_only={sorted(set(declarations) - set(gitlinks))}, "
            f"gitlink_only={sorted(set(gitlinks) - set(declarations))}"
        )


def validate_exclusions(exclusions_value: object) -> list[dict[str, str]]:
    if not isinstance(exclusions_value, list):
        fail("exclusions must be an array")
    exclusions: list[dict[str, str]] = []
    for index, entry in enumerate(exclusions_value):
        label = f"exclusions[{index}]"
        if not isinstance(entry, dict):
            fail(f"{label} must be an object")
        require_exact_keys(entry, {"repository", "path", "reason"}, label)
        repository = require_nonempty_string(entry["repository"], f"{label}.repository")
        if repository not in CONSUMERS:
            fail(f"{label}.repository is unknown")
        reason = require_nonempty_string(entry["reason"], f"{label}.reason")
        if len(reason) < 20:
            fail(f"{label}.reason must be a substantive explanation")
        exclusions.append(
            {
                "repository": repository,
                "path": require_relative_path(entry["path"], f"{label}.path"),
                "reason": reason,
            }
        )
    exclusion_keys = [(row["repository"], row["path"]) for row in exclusions]
    if len(exclusion_keys) != len(set(exclusion_keys)):
        fail("exclusions contains a duplicate repository/path")
    for repository, path in exclusion_keys:
        protected = {"Cargo.toml", "Cargo.lock", ".gitmodules", ".cargo"}
        if repository == "trust":
            protected.update(
                {
                    RECEIPT_PATH,
                    "scripts/check_dependency_cycle_anchor.py",
                    "scripts/hooks",
                    "scripts/hooks-pin",
                    "scripts/install-git-hooks.sh",
                    "scripts/install-pin-hook.sh",
                }
            )
        if any(
            path == authority
            or path.startswith(authority + "/")
            or authority.startswith(path + "/")
            for authority in protected
        ):
            fail(
                f"exclusion {repository}:{path} overlaps repository-root dependency authority"
            )
        if repository == "ny" and any(
            proof_path == path
            or proof_path.startswith(path + "/")
            or path.startswith(proof_path + "/")
            for proof_path in NY_IDENTITY_PATHS
        ):
            fail(f"NY Clean proof identity path {path!r} may not be excluded")
        for other_repository, other_path in exclusion_keys:
            if (repository, path) != (other_repository, other_path) and repository == other_repository:
                if path.startswith(other_path + "/"):
                    fail(f"exclusions overlap in {repository}: {other_path!r} contains {path!r}")
    return sorted(exclusions, key=lambda row: (row["repository"], row["path"]))


def validate_receipt(value: object) -> dict[str, Any]:
    if not isinstance(value, dict):
        fail("receipt top level must be an object")
    require_exact_keys(
        value,
        {
            "schema",
            "self",
            "repositories",
            "root_bindings",
            "exclusions",
            "surfaces",
            "direct_edges",
            "anchors",
        },
        "receipt",
    )
    if value["schema"] != SCHEMA:
        fail(f"schema must be exactly {SCHEMA!r}")

    self_value = value["self"]
    if not isinstance(self_value, dict):
        fail("self must be an object")
    require_exact_keys(self_value, {"repository", "commit"}, "self")
    if self_value != {"repository": "trust", "commit": SELF_SENTINEL}:
        fail("self must bind trust to the literal CONTAINING_COMMIT sentinel")

    repositories = value["repositories"]
    if not isinstance(repositories, dict):
        fail("repositories must be an object")
    if set(repositories) != set(SUBMODULES):
        fail(
            "repositories must name exactly the nine first-party repositories: "
            f"missing={sorted(set(SUBMODULES) - set(repositories))}, "
            f"extra={sorted(set(repositories) - set(SUBMODULES))}"
        )
    commits: dict[str, str] = {}
    for name, entry in repositories.items():
        if not isinstance(entry, dict):
            fail(f"repositories.{name} must be an object")
        require_exact_keys(entry, {"url", "commit"}, f"repositories.{name}")
        if entry["url"] != SUBMODULES[name][1]:
            fail(f"repositories.{name}.url is not the canonical URL")
        commits[name] = require_sha(entry["commit"], f"repositories.{name}.commit")

    bindings = value["root_bindings"]
    if not isinstance(bindings, list):
        fail("root_bindings must be an array")
    normalized_bindings: list[dict[str, str]] = []
    for index, entry in enumerate(bindings):
        label = f"root_bindings[{index}]"
        if not isinstance(entry, dict):
            fail(f"{label} must be an object")
        require_exact_keys(entry, {"repository", "path", "url", "commit"}, label)
        name = require_nonempty_string(entry["repository"], f"{label}.repository")
        if name not in SUBMODULES:
            fail(f"{label}.repository is not first-party")
        normalized_bindings.append(
            {
                "repository": name,
                "path": require_relative_path(entry["path"], f"{label}.path"),
                "url": require_nonempty_string(entry["url"], f"{label}.url"),
                "commit": require_sha(entry["commit"], f"{label}.commit"),
            }
        )
    if len({row["repository"] for row in normalized_bindings}) != len(normalized_bindings):
        fail("root_bindings contains a duplicate repository")

    exclusions = validate_exclusions(value["exclusions"])

    surfaces_value = value["surfaces"]
    if not isinstance(surfaces_value, list):
        fail("surfaces must be an array")
    surfaces = [validate_surface(row, f"surfaces[{index}]") for index, row in enumerate(surfaces_value)]
    surface_ids = [row["id"] for row in surfaces]
    if len(surface_ids) != len(set(surface_ids)):
        fail("surfaces contains a duplicate id")

    edges_value = value["direct_edges"]
    if not isinstance(edges_value, list):
        fail("direct_edges must be an array")
    edges = [validate_edge(row, f"direct_edges[{index}]") for index, row in enumerate(edges_value)]
    edge_keys = [(row["consumer"], row["dependency"]) for row in edges]
    if len(edge_keys) != len(set(edge_keys)):
        fail("direct_edges contains a split or duplicate consumer/dependency pair")

    anchors_value = value["anchors"]
    if not isinstance(anchors_value, list):
        fail("anchors must be an array")
    anchors = [validate_anchor(row, f"anchors[{index}]") for index, row in enumerate(anchors_value)]
    anchor_keys = [(row["consumer"], row["dependency"]) for row in anchors]
    if len(anchor_keys) != len(set(anchor_keys)):
        fail("anchors contains a duplicate consumer/dependency pair")

    return {
        "repositories": commits,
        "root_bindings": normalized_bindings,
        "exclusions": exclusions,
        "surfaces": surfaces,
        "direct_edges": edges,
        "anchors": anchors,
    }


def validate_surface(value: object, label: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        fail(f"{label} must be an object")
    require_exact_keys(value, SURFACE_KEYS, label)
    repository = require_nonempty_string(value["repository"], f"{label}.repository")
    dependency = require_nonempty_string(value["dependency"], f"{label}.dependency")
    kind = require_nonempty_string(value["kind"], f"{label}.kind")
    scope = require_nonempty_string(value["scope"], f"{label}.scope")
    if repository not in CONSUMERS or dependency not in SUBMODULES:
        fail(f"{label} names an unknown repository")
    if kind not in SURFACE_KINDS:
        fail(f"{label}.kind is unsupported")
    if scope not in {"canonical", "excluded"}:
        fail(f"{label}.scope must be canonical or excluded")
    optional = value["optional"]
    if optional is not None and not isinstance(optional, bool):
        fail(f"{label}.optional must be boolean or null")
    rev = value["rev"]
    if rev is not None:
        rev = require_sha(rev, f"{label}.rev")
    return {
        "id": require_nonempty_string(value["id"], f"{label}.id"),
        "repository": repository,
        "scope": scope,
        "kind": kind,
        "path": require_relative_path(value["path"], f"{label}.path"),
        "locator": require_nonempty_string(value["locator"], f"{label}.locator"),
        "dependency": dependency,
        "package": require_nonempty_string(value["package"], f"{label}.package"),
        "url": require_optional_string(value["url"], f"{label}.url"),
        "rev": rev,
        "dependency_path": require_optional_string(
            value["dependency_path"], f"{label}.dependency_path"
        ),
        "subdir": require_optional_string(value["subdir"], f"{label}.subdir"),
        "optional": optional,
    }


def validate_edge(value: object, label: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        fail(f"{label} must be an object")
    require_exact_keys(value, {"consumer", "dependency", "commit", "surfaces"}, label)
    consumer = require_nonempty_string(value["consumer"], f"{label}.consumer")
    dependency = require_nonempty_string(value["dependency"], f"{label}.dependency")
    if consumer not in CONSUMERS or dependency not in SUBMODULES or consumer == dependency:
        fail(f"{label} names an invalid cross-repository edge")
    surface_ids = value["surfaces"]
    if not isinstance(surface_ids, list) or not surface_ids:
        fail(f"{label}.surfaces must be a non-empty array")
    if not all(isinstance(item, str) and item for item in surface_ids):
        fail(f"{label}.surfaces must contain non-empty strings")
    if len(surface_ids) != len(set(surface_ids)):
        fail(f"{label}.surfaces contains a duplicate")
    return {
        "consumer": consumer,
        "dependency": dependency,
        "commit": require_sha(value["commit"], f"{label}.commit"),
        "surfaces": sorted(surface_ids),
    }


def validate_anchor(value: object, label: str) -> dict[str, str]:
    if not isinstance(value, dict):
        fail(f"{label} must be an object")
    require_exact_keys(value, {"consumer", "dependency", "commit", "terminal", "reason"}, label)
    consumer = require_nonempty_string(value["consumer"], f"{label}.consumer")
    dependency = require_nonempty_string(value["dependency"], f"{label}.dependency")
    if consumer not in CONSUMERS or dependency not in SUBMODULES or consumer == dependency:
        fail(f"{label} names an invalid cross-repository edge")
    if value["reason"] != GENERATION_CUT_REASON:
        fail(f"{label}.reason must be the exact generation-cut policy text")
    commit = require_sha(value["commit"], f"{label}.commit")
    terminal = require_sha(value["terminal"], f"{label}.terminal")
    if commit == terminal:
        fail(f"{label} may not anchor a terminal edge")
    return {
        "consumer": consumer,
        "dependency": dependency,
        "commit": commit,
        "terminal": terminal,
        "reason": GENERATION_CUT_REASON,
    }


def scope_for(repository: str, path: str, exclusions: list[dict[str, str]]) -> str:
    for exclusion in exclusions:
        prefix = exclusion["path"]
        if exclusion["repository"] == repository and (path == prefix or path.startswith(prefix + "/")):
            return "excluded"
    return "canonical"


def lexical_absolute(path: Path) -> Path:
    return Path(os.path.abspath(os.path.normpath(os.fspath(path))))


def map_dependency_path(
    repository: str,
    manifest_path: str,
    raw_path: str,
    roots: dict[str, Path],
    *,
    relative_base: str | None = None,
    symlink_paths: set[Path] | None = None,
    allow_absolute_external: bool = False,
) -> tuple[str, str] | None:
    source_root = roots[repository]
    base = (
        PurePosixPath(manifest_path).parent
        if relative_base is None
        else PurePosixPath(relative_base)
    )
    authored = PurePosixPath(raw_path)
    if authored.is_absolute():
        if not allow_absolute_external:
            fail(f"{repository}:{manifest_path} path {raw_path!r} must be relative")
        target = lexical_absolute(Path(raw_path))
        if symlink_paths is not None:
            traversed = next(
                (link for link in symlink_paths if target == link or link in target.parents),
                None,
            )
            if traversed is not None:
                fail(
                    f"{repository}:{manifest_path} path {raw_path!r} traverses committed "
                    f"symlink {traversed}"
                )
    else:
        cursor = lexical_absolute(source_root / base)
        for part in authored.parts:
            if part in {"", "."}:
                continue
            cursor = cursor.parent if part == ".." else cursor / part
            if symlink_paths is not None and cursor in symlink_paths:
                fail(
                    f"{repository}:{manifest_path} path {raw_path!r} traverses committed "
                    f"symlink {cursor}"
                )
        target = lexical_absolute(source_root / base / raw_path)
    candidates = sorted(roots.items(), key=lambda item: len(os.fspath(item[1])), reverse=True)
    target_folded = os.fspath(target).casefold()
    for target_repository, root in candidates:
        absolute_root = lexical_absolute(root)
        root_folded = os.fspath(absolute_root).casefold()
        try:
            folded_common = os.path.commonpath([target_folded, root_folded])
            exact_common = Path(os.path.commonpath([target, absolute_root]))
        except ValueError:
            continue
        if folded_common == root_folded and exact_common != absolute_root:
            fail(
                f"{repository}:{manifest_path} path {raw_path!r} targets first-party "
                f"repository {target_repository!r} with noncanonical casing"
            )
    for target_repository, root in candidates:
        absolute_root = lexical_absolute(root)
        try:
            common = Path(os.path.commonpath([target, absolute_root]))
        except ValueError:
            continue
        if common == absolute_root:
            relative = target.relative_to(absolute_root).as_posix()
            return target_repository, relative or "."
    return None


def make_surface(
    *,
    repository: str,
    scope: str,
    kind: str,
    path: str,
    locator: str,
    dependency: str,
    package: str,
    url: str | None,
    rev: str | None,
    dependency_path: str | None,
    subdir: str | None,
    optional: bool | None,
) -> dict[str, Any]:
    surface_id = f"{repository}:{path}:{locator}:{kind}"
    return {
        "id": surface_id,
        "repository": repository,
        "scope": scope,
        "kind": kind,
        "path": path,
        "locator": locator,
        "dependency": dependency,
        "package": package,
        "url": url,
        "rev": rev,
        "dependency_path": dependency_path,
        "subdir": subdir,
        "optional": optional,
    }


def validate_workspace_exclusions(
    repository: str,
    files: list[str],
    root_manifest: dict[str, Any] | None,
    exclusions: list[dict[str, str]],
) -> None:
    if root_manifest is None or not isinstance(root_manifest.get("workspace"), dict):
        return
    workspace = root_manifest["workspace"]
    members = workspace.get("members", [])
    cargo_excludes = workspace.get("exclude", [])
    if not isinstance(members, list) or not all(isinstance(item, str) for item in members):
        fail(f"{repository}:Cargo.toml workspace.members must be an array of strings")
    if not isinstance(cargo_excludes, list) or not all(
        isinstance(item, str) for item in cargo_excludes
    ):
        fail(f"{repository}:Cargo.toml workspace.exclude must be an array of strings")

    def manifest_pattern(pattern: str) -> str:
        normalized = pattern.rstrip("/")
        return normalized if normalized.endswith("Cargo.toml") else normalized + "/Cargo.toml"

    member_manifests = {
        path
        for path in files
        if path.endswith("Cargo.toml")
        and any(fnmatch.fnmatchcase(path, manifest_pattern(pattern)) for pattern in members)
        and not any(fnmatch.fnmatchcase(path, manifest_pattern(pattern)) for pattern in cargo_excludes)
    }
    for exclusion in exclusions:
        if exclusion["repository"] != repository:
            continue
        hidden_members = sorted(
            path
            for path in member_manifests
            if path == exclusion["path"] or path.startswith(exclusion["path"] + "/")
        )
        if hidden_members:
            fail(
                f"exclusion {repository}:{exclusion['path']} hides Cargo workspace members "
                f"{hidden_members[:5]}"
            )


def scan_cargo_manifest(
    repository: str,
    path: str,
    data: dict[str, Any],
    scope: str,
    roots: dict[str, Path],
    *,
    config_only: bool = False,
    relative_base: str | None = None,
    symlink_paths: set[Path] | None = None,
) -> tuple[list[dict[str, Any]], list[tuple[str, str, str, str]]]:
    surfaces: list[dict[str, Any]] = []
    path_links: list[tuple[str, str, str, str]] = []

    def dependency(
        alias: str,
        spec: object,
        locator: str,
        relation: str,
        patch_source: str | None = None,
    ) -> None:
        if not isinstance(spec, dict):
            return
        git_value = spec.get("git")
        path_value = spec.get("path")
        git_repository = first_party_url(git_value, f"{repository}:{path}:{locator}.git")
        source_repository = (
            None
            if patch_source is None
            or re.fullmatch(r"[A-Za-z0-9_-]+", patch_source) is not None
            else first_party_url(
                patch_source,
                f"{repository}:{path}:{locator}.patch-source",
                allow_alias=True,
            )
        )
        mapped: tuple[str, str] | None = None
        if path_value is not None:
            if not isinstance(path_value, str):
                fail(f"{repository}:{path}:{locator}.path must be a string")
            mapped = map_dependency_path(
                repository,
                path,
                path_value,
                roots,
                relative_base=relative_base,
                symlink_paths=symlink_paths,
            )
            if mapped is not None:
                path_links.append((repository, path, mapped[0], mapped[1]))

        mapped_repository = mapped[0] if mapped is not None else None
        if mapped_repository == "trust" and repository != "trust":
            fail(
                f"{repository}:{path}:{locator} creates a subrepository-to-root Cargo path edge"
            )
        candidates = {name for name in (git_repository, source_repository, mapped_repository) if name in SUBMODULES}
        if not candidates:
            return
        if len(candidates) != 1:
            fail(
                f"{repository}:{path}:{locator} splits one dependency across first-party repositories {sorted(candidates)}"
            )
        dependency_repository = next(iter(candidates))
        if git_value is not None and path_value is not None:
            fail(f"{repository}:{path}:{locator} combines git and path authority")
        if mapped_repository == repository and source_repository is None and git_repository is None:
            return  # ordinary intra-repository path dependency
        if source_repository is not None and mapped_repository not in {None, source_repository}:
            fail(f"{repository}:{path}:{locator} patch source and target repositories differ")

        package = spec.get("package", alias)
        if not isinstance(package, str) or not package:
            fail(f"{repository}:{path}:{locator}.package must be a non-empty string")
        rev: str | None = None
        url: str | None = None
        normalized_path: str | None = None
        if git_value is not None:
            if git_repository is None:
                fail(f"{repository}:{path}:{locator} has an unsupported first-party git target")
            url = SUBMODULES[git_repository][1]
            rev = require_sha(spec.get("rev"), f"{repository}:{path}:{locator}.rev")
            kind = f"cargo-{relation}-git" if relation != "direct" else "cargo-git"
        elif path_value is not None:
            normalized_path = posixpath.normpath(path_value)
            # Cargo source identities with/without .git and via SSH are distinct.
            # Root deliberately patches each identity, so inventory the authored
            # patch key verbatim while keeping direct Git/Lake declarations strict.
            url = patch_source if source_repository is not None else None
            kind = f"cargo-{relation}-path" if relation != "direct" else "cargo-path"
        else:
            # A patch source URL without a git/path target is not reproducible.
            if source_repository is not None:
                fail(f"{repository}:{path}:{locator} first-party patch has no git/path target")
            return
        optional = spec.get("optional", False)
        if not isinstance(optional, bool):
            fail(f"{repository}:{path}:{locator}.optional must be boolean")
        surfaces.append(
            make_surface(
                repository=repository,
                scope=scope,
                kind=kind,
                path=path,
                locator=locator,
                dependency=dependency_repository,
                package=package,
                url=url,
                rev=rev,
                dependency_path=normalized_path,
                subdir=None,
                optional=optional,
            )
        )

    if not config_only:
        direct_sections: list[tuple[str, object]] = []
        for section in ("dependencies", "dev-dependencies", "build-dependencies"):
            direct_sections.append((f"/{section}", data.get(section)))
        workspace = data.get("workspace")
        if isinstance(workspace, dict):
            for section in ("dependencies", "dev-dependencies", "build-dependencies"):
                direct_sections.append((f"/workspace/{section}", workspace.get(section)))
        target = data.get("target")
        if isinstance(target, dict):
            for target_name, target_table in target.items():
                if not isinstance(target_table, dict):
                    continue
                for section in ("dependencies", "dev-dependencies", "build-dependencies"):
                    direct_sections.append(
                        (f"/target/{target_name}/{section}", target_table.get(section))
                    )
        for base, table in direct_sections:
            if not isinstance(table, dict):
                continue
            for alias, spec in table.items():
                dependency(str(alias), spec, f"{base}/{alias}", "direct")

    patches = data.get("patch")
    if isinstance(patches, dict):
        for source, table in patches.items():
            if not isinstance(table, dict):
                continue
            for alias, spec in table.items():
                dependency(
                    str(alias),
                    spec,
                    f"/patch/{source}/{alias}",
                    "patch",
                    str(source),
                )
    replacements = data.get("replace")
    if config_only and replacements is not None:
        fail(f"{repository}:{path} may not declare Cargo [replace]; inline a supported [patch]")
    if not config_only and isinstance(replacements, dict):
        for alias, spec in replacements.items():
            dependency(str(alias).split(":", 1)[0], spec, f"/replace/{alias}", "replace")
    return surfaces, path_links


def scan_cargo_config(
    repository: str,
    path: str,
    data: dict[str, Any],
    scope: str,
    roots: dict[str, Path],
    symlink_paths: set[Path],
) -> tuple[list[dict[str, Any]], list[tuple[str, str, str, str]]]:
    config_path = PurePosixPath(path)
    # Cargo resolves relative config paths from the parent of the containing
    # .cargo directory, not from .cargo itself.
    relative_base = config_path.parent.parent.as_posix()
    if "include" in data:
        fail(f"{repository}:{path} Cargo config include is unsupported; inline [patch]")
    if "paths" in data:
        fail(f"{repository}:{path} Cargo config paths overrides are unsupported; use [patch]")

    sources = data.get("source")
    if sources is not None and not isinstance(sources, dict):
        fail(f"{repository}:{path} Cargo config [source] must be a table")
    if isinstance(sources, dict):
        for source_name, source in sources.items():
            if not isinstance(source, dict):
                fail(f"{repository}:{path} source.{source_name} must be a table")
            for key in ("git", "registry"):
                if key not in source:
                    continue
                value = source[key]
                if not isinstance(value, str):
                    fail(f"{repository}:{path} source.{source_name}.{key} must be a string")
                dependency = first_party_url(
                    value,
                    f"{repository}:{path}:source.{source_name}.{key}",
                )
                if dependency is not None:
                    fail(
                        f"{repository}:{path} first-party Cargo [source] redirect to "
                        f"{dependency} is unsupported; use [patch]"
                    )
            for key in ("directory", "local-registry"):
                if key not in source:
                    continue
                value = source[key]
                if not isinstance(value, str):
                    fail(f"{repository}:{path} source.{source_name}.{key} must be a string")
                mapped = map_dependency_path(
                    repository,
                    path,
                    value,
                    roots,
                    relative_base=relative_base,
                    symlink_paths=symlink_paths,
                )
                if mapped is not None and (
                    mapped[0] in SUBMODULES or (mapped[0] == "trust" and repository != "trust")
                ):
                    fail(
                        f"{repository}:{path} first-party Cargo [source] {key} redirect "
                        f"to {mapped[0]} is unsupported; use [patch]"
                    )

    return scan_cargo_manifest(
        repository,
        path,
        data,
        scope,
        roots,
        config_only=True,
        relative_base=relative_base,
        symlink_paths=symlink_paths,
    )


def scan_cargo_lock(
    repository: str,
    path: str,
    data: dict[str, Any],
    scope: str,
) -> list[dict[str, Any]]:
    packages = data.get("package", [])
    if not isinstance(packages, list):
        fail(f"{repository}:{path}: package must be an array")
    surfaces: list[dict[str, Any]] = []
    for index, package in enumerate(packages):
        if not isinstance(package, dict):
            fail(f"{repository}:{path}:package[{index}] must be a table")
        source = package.get("source")
        if not isinstance(source, str) or not source.startswith("git+"):
            continue
        payload = source[4:]
        parsed = urlsplit(payload)
        base_url = urlunsplit((parsed.scheme, parsed.netloc, parsed.path, "", ""))
        dependency = first_party_url(
            base_url, f"{repository}:{path}:package[{index}].source"
        )
        if dependency is None:
            continue
        if base_url != SUBMODULES[dependency][1]:
            fail(f"{repository}:{path}:package[{index}] lock URL is not canonical")
        query = parse_qs(parsed.query, keep_blank_values=True)
        if set(query) != {"rev"} or len(query["rev"]) != 1:
            fail(f"{repository}:{path}:package[{index}] lock source must contain only one rev query")
        query_rev = require_sha(query["rev"][0], f"{repository}:{path}:package[{index}] query rev")
        fragment_rev = require_sha(parsed.fragment, f"{repository}:{path}:package[{index}] fragment rev")
        if query_rev != fragment_rev:
            fail(f"{repository}:{path}:package[{index}] lock query/fragment revisions split")
        name = require_nonempty_string(package.get("name"), f"{repository}:{path}:package[{index}].name")
        version = require_nonempty_string(
            package.get("version"), f"{repository}:{path}:package[{index}].version"
        )
        surfaces.append(
            make_surface(
                repository=repository,
                scope=scope,
                kind="cargo-lock",
                path=path,
                locator=f"/package/{index}:{name}@{version}",
                dependency=dependency,
                package=name,
                url=SUBMODULES[dependency][1],
                rev=query_rev,
                dependency_path=None,
                subdir=None,
                optional=None,
            )
        )
    return surfaces


def scan_lakefile(
    repository: str,
    path: str,
    data: dict[str, Any],
    scope: str,
    roots: dict[str, Path],
    symlink_paths: set[Path],
) -> tuple[list[dict[str, Any]], list[tuple[str, str, str, str]]]:
    requirements = data.get("require", [])
    if not isinstance(requirements, list):
        fail(f"{repository}:{path}: require must be an array")
    surfaces: list[dict[str, Any]] = []
    path_links: list[tuple[str, str, str, str]] = []
    for index, requirement in enumerate(requirements):
        if not isinstance(requirement, dict):
            fail(f"{repository}:{path}:require[{index}] must be a table")
        git_value = requirement.get("git")
        path_value = requirement.get("path")
        dependency = first_party_url(git_value, f"{repository}:{path}:require[{index}].git")
        mapped: tuple[str, str] | None = None
        if path_value is not None:
            if not isinstance(path_value, str):
                fail(f"{repository}:{path}:require[{index}].path must be a string")
            mapped = map_dependency_path(
                repository,
                path,
                path_value,
                roots,
                symlink_paths=symlink_paths,
                allow_absolute_external=True,
            )
            if mapped is not None:
                path_links.append((repository, path, mapped[0], mapped[1]))
        mapped_repository = mapped[0] if mapped is not None else None
        if mapped_repository == "trust" and repository != "trust":
            fail(f"{repository}:{path}:require[{index}] creates a subrepository-to-root Lake path edge")
        if git_value is not None and path_value is not None:
            fail(f"{repository}:{path}:require[{index}] combines git and path authority")
        candidates = {
            candidate
            for candidate in (dependency, mapped_repository)
            if candidate in SUBMODULES
        }
        if not candidates:
            continue
        if len(candidates) != 1:
            fail(
                f"{repository}:{path}:require[{index}] splits one Lake dependency across "
                f"first-party repositories {sorted(candidates)}"
            )
        dependency = next(iter(candidates))
        if mapped_repository == repository and git_value is None:
            continue
        package = require_nonempty_string(
            requirement.get("name"), f"{repository}:{path}:require[{index}].name"
        )
        rev = (
            require_sha(
                requirement.get("rev"), f"{repository}:{path}:require[{index}].rev"
            )
            if git_value is not None
            else None
        )
        subdir = requirement.get("subDir")
        if subdir is not None:
            subdir = require_relative_path(subdir, f"{repository}:{path}:require[{index}].subDir")
        surfaces.append(
            make_surface(
                repository=repository,
                scope=scope,
                kind="lake-require" if git_value is not None else "lake-path",
                path=path,
                locator=f"/require/{index}:{package}",
                dependency=dependency,
                package=package,
                url=SUBMODULES[dependency][1] if git_value is not None else None,
                rev=rev,
                dependency_path=(
                    None if path_value is None else posixpath.normpath(path_value)
                ),
                subdir=subdir,
                optional=None,
            )
        )
    return surfaces, path_links


def scan_lake_manifest(
    repository: str,
    path: str,
    value: object,
    scope: str,
    roots: dict[str, Path],
    symlink_paths: set[Path],
) -> tuple[list[dict[str, Any]], list[tuple[str, str, str, str]]]:
    if not isinstance(value, dict) or not isinstance(value.get("packages"), list):
        fail(f"{repository}:{path} must contain a packages array")
    surfaces: list[dict[str, Any]] = []
    path_links: list[tuple[str, str, str, str]] = []
    for index, package in enumerate(value["packages"]):
        if not isinstance(package, dict):
            fail(f"{repository}:{path}:packages[{index}] must be an object")
        package_type = package.get("type")
        path_keys = [key for key in ("path", "dir") if key in package]
        is_path_package = package_type == "path" or bool(path_keys)
        dependency: str | None = None
        dependency_path: str | None = None
        if is_path_package:
            if package_type not in {None, "path"}:
                fail(f"{repository}:{path}:packages[{index}] mixes type {package_type!r} with path/dir")
            candidate_values: list[tuple[str, str]] = []
            for key in ("path", "dir", "url"):
                raw_value = package.get(key)
                if raw_value is None:
                    continue
                if not isinstance(raw_value, str):
                    fail(f"{repository}:{path}:packages[{index}].{key} must be a string")
                candidate_values.append((key, raw_value))
            if not candidate_values:
                fail(f"{repository}:{path}:packages[{index}] path package has no path/dir/url")
            mapped_rows: list[tuple[str, str, str]] = []
            for key, raw_value in candidate_values:
                mapped = map_dependency_path(
                    repository,
                    path,
                    raw_value,
                    roots,
                    symlink_paths=symlink_paths,
                    allow_absolute_external=True,
                )
                if mapped is not None:
                    path_links.append((repository, path, mapped[0], mapped[1]))
                    if mapped[0] in SUBMODULES:
                        mapped_rows.append((mapped[0], key, raw_value))
                    elif mapped[0] == "trust" and repository != "trust":
                        fail(
                            f"{repository}:{path}:packages[{index}] creates a "
                            "subrepository-to-root Lake path edge"
                        )
            mapped_repositories = {row[0] for row in mapped_rows}
            if not mapped_repositories:
                continue
            if len(mapped_repositories) != 1:
                fail(
                    f"{repository}:{path}:packages[{index}] path/dir values split across "
                    f"first-party repositories {sorted(mapped_repositories)}"
                )
            dependency = next(iter(mapped_repositories))
            if dependency == repository:
                continue
            dependency_path = posixpath.normpath(mapped_rows[0][2])
        else:
            dependency = first_party_url(
                package.get("url"), f"{repository}:{path}:packages[{index}].url"
            )
            if dependency is None:
                continue
        name = require_nonempty_string(
            package.get("name"), f"{repository}:{path}:packages[{index}].name"
        )
        rev: str | None = None
        if not is_path_package:
            rev = require_sha(package.get("rev"), f"{repository}:{path}:packages[{index}].rev")
            input_rev = require_sha(
                package.get("inputRev"), f"{repository}:{path}:packages[{index}].inputRev"
            )
            if rev != input_rev:
                fail(f"{repository}:{path}:packages[{index}] rev/inputRev split")
        subdir = package.get("subDir")
        if subdir is not None:
            subdir = require_relative_path(subdir, f"{repository}:{path}:packages[{index}].subDir")
        surfaces.append(
            make_surface(
                repository=repository,
                scope=scope,
                kind="lake-path-lock" if is_path_package else "lake-lock",
                path=path,
                locator=f"/packages/{index}:{name}",
                dependency=dependency,
                package=name,
                url=None if is_path_package else SUBMODULES[dependency][1],
                rev=rev,
                dependency_path=dependency_path,
                subdir=subdir,
                optional=None,
            )
        )
    return surfaces, path_links


def scan_proof_identity(
    repository: str,
    path: str,
    value: object,
    scope: str,
) -> list[dict[str, Any]]:
    if not isinstance(value, dict):
        fail(f"{repository}:{path} top level must be an object")
    corpus = value.get("corpus")
    if not isinstance(corpus, dict) or corpus.get("source") != "lake-git-dependency":
        return []
    dependency = first_party_url(corpus.get("git"), f"{repository}:{path}:corpus.git")
    if dependency is None:
        return []
    package = require_nonempty_string(corpus.get("package"), f"{repository}:{path}:corpus.package")
    rev = require_sha(corpus.get("rev"), f"{repository}:{path}:corpus.rev")
    subdir = corpus.get("subDir")
    if subdir is not None:
        subdir = require_relative_path(subdir, f"{repository}:{path}:corpus.subDir")
    return [
        make_surface(
            repository=repository,
            scope=scope,
            kind="proof-identity",
            path=path,
            locator="/corpus",
            dependency=dependency,
            package=package,
            url=SUBMODULES[dependency][1],
            rev=rev,
            dependency_path=None,
            subdir=subdir,
            optional=None,
        )
    ]


def exactly_one_match(pattern: str, text: str, label: str, *, flags: int = 0) -> tuple[str, ...]:
    matches = re.findall(pattern, text, flags)
    if len(matches) != 1:
        fail(f"{label} must contain exactly one authoritative identity row; observed {len(matches)}")
    match = matches[0]
    return (match,) if isinstance(match, str) else tuple(match)


def ny_proof_surface(
    *,
    path: str,
    locator: str,
    scope: str,
    rev: str,
    url: str | None,
    subdir: str | None,
) -> dict[str, Any]:
    return make_surface(
        repository="ny",
        scope=scope,
        kind="proof-identity",
        path=path,
        locator=locator,
        dependency="clean",
        package="crownproof",
        url=url,
        rev=rev,
        dependency_path=None,
        subdir=subdir,
        optional=None,
    )


def scan_ny_spec(path: str, raw: bytes, scope: str) -> list[dict[str, Any]]:
    text = decode_text(raw, f"ny:{path}")
    (rev_value,) = exactly_one_match(
        r"uses\s+private\s+Clean\s+commit\s+`([^`]+)`\s+with",
        text,
        f"ny:{path}:private Clean commit",
        flags=re.MULTILINE,
    )
    (subdir_value,) = exactly_one_match(
        r"`subDir\s*=\s*\"([^\"]+)\"`",
        text,
        f"ny:{path}:Clean subDir",
    )
    return [
        ny_proof_surface(
            path=path,
            locator="/private-clean-commit",
            scope=scope,
            rev=require_sha(rev_value, f"ny:{path}:Clean rev"),
            url=None,
            subdir=require_relative_path(subdir_value, f"ny:{path}:Clean subDir"),
        )
    ]


def scan_ny_proof_readme(path: str, raw: bytes, scope: str) -> list[dict[str, Any]]:
    text = decode_text(raw, f"ny:{path}")
    (rev_value,) = exactly_one_match(
        r"Clean's\s+`Crownproof`\s+library[\s\S]*?at\s+exact\s+commit\s+`([^`]+)`",
        text,
        f"ny:{path}:Clean exact commit",
    )
    return [
        ny_proof_surface(
            path=path,
            locator="/clean-exact-commit",
            scope=scope,
            rev=require_sha(rev_value, f"ny:{path}:Clean rev"),
            url=None,
            subdir=None,
        )
    ]


def scan_ny_provenance(path: str, raw: bytes, scope: str) -> list[dict[str, Any]]:
    text = decode_text(raw, f"ny:{path}")
    (url_value,) = exactly_one_match(
        r"^repository:\s*(\S+)\s*$",
        text,
        f"ny:{path}:repository",
        flags=re.MULTILINE,
    )
    (rev_value,) = exactly_one_match(
        r"^revision:\s*(\S+)\s*$",
        text,
        f"ny:{path}:revision",
        flags=re.MULTILINE,
    )
    (subdir_value,) = exactly_one_match(
        r"^subDir:\s*(\S+)\s*$",
        text,
        f"ny:{path}:subDir",
        flags=re.MULTILINE,
    )
    dependency = first_party_url(url_value, f"ny:{path}:repository")
    if dependency != "clean":
        fail(f"ny:{path}:repository must be the canonical Clean URL")
    return [
        ny_proof_surface(
            path=path,
            locator="/provenance/clean",
            scope=scope,
            rev=require_sha(rev_value, f"ny:{path}:revision"),
            url=SUBMODULES["clean"][1],
            subdir=require_relative_path(subdir_value, f"ny:{path}:subDir"),
        )
    ]


def scan_ny_cite_source(path: str, raw: bytes, scope: str) -> list[dict[str, Any]]:
    text = decode_text(raw, f"ny:{path}")

    def constant(name: str) -> str:
        (value,) = exactly_one_match(
            rf'^pub\s+const\s+{re.escape(name)}:\s*&str\s*=\s*"([^"\n]*)";\s*$',
            text,
            f"ny:{path}:{name}",
            flags=re.MULTILINE,
        )
        return value

    package = constant("CLEAN_LAKE_PACKAGE")
    if package != "crownproof":
        fail(f"ny:{path}:CLEAN_LAKE_PACKAGE must be exactly 'crownproof'")
    url_value = constant("CLEAN_GIT_URL")
    dependency = first_party_url(url_value, f"ny:{path}:CLEAN_GIT_URL")
    if dependency != "clean":
        fail(f"ny:{path}:CLEAN_GIT_URL must be the canonical Clean URL")
    rev = require_sha(constant("CLEAN_GIT_REV"), f"ny:{path}:CLEAN_GIT_REV")
    subdir = require_relative_path(
        constant("CLEAN_LAKE_SUBDIR"), f"ny:{path}:CLEAN_LAKE_SUBDIR"
    )
    return [
        ny_proof_surface(
            path=path,
            locator="/const/CLEAN_GIT_IDENTITY",
            scope=scope,
            rev=rev,
            url=SUBMODULES["clean"][1],
            subdir=subdir,
        )
    ]


def validate_ny_identity_bundle(surfaces: list[dict[str, Any]]) -> None:
    rows = [
        row
        for row in surfaces
        if row["repository"] == "ny"
        and row["dependency"] == "clean"
        and row["kind"] in {"proof-identity", "lake-require", "lake-lock"}
    ]
    paths = {row["path"] for row in rows}
    if len(rows) != 7 or paths != NY_IDENTITY_PATHS:
        fail(
            "NY Clean proof identity must contain exactly seven committed surfaces: "
            f"missing={sorted(NY_IDENTITY_PATHS - paths)}, "
            f"extra={sorted(paths - NY_IDENTITY_PATHS)}, rows={len(rows)}"
        )
    revisions = {row["rev"] for row in rows}
    if len(revisions) != 1:
        fail(f"NY Clean proof identity revisions split across seven surfaces: {sorted(revisions)}")
    by_path = {row["path"]: row for row in rows}
    canonical_url_paths = NY_IDENTITY_PATHS - {
        "crates/ny-cert/SPEC.md",
        "crates/ny-cert/proofs/README.md",
    }
    subdir_paths = NY_IDENTITY_PATHS - {"crates/ny-cert/proofs/README.md"}
    for path, row in by_path.items():
        expected_url = SUBMODULES["clean"][1] if path in canonical_url_paths else None
        expected_subdir = "crown-proofs/lean" if path in subdir_paths else None
        if row["package"] != "crownproof" or row["url"] != expected_url or row["subdir"] != expected_subdir:
            fail(f"NY Clean proof identity surface {path} has malformed package/URL/subDir")


def is_committed_authority_path(repository: str, path: str) -> bool:
    pure = PurePosixPath(path)
    if path == ".gitmodules" or path.endswith(("Cargo.toml", "Cargo.lock")):
        return True
    if pure.name in {"config", "config.toml"} and pure.parent.name == ".cargo":
        return True
    if path.endswith(
        ("lakefile.toml", "lakefile.lean", "lake-manifest.json", "cite-map.json")
    ):
        return True
    if repository == "ny" and path in NY_IDENTITY_PATHS:
        return True
    if repository != "trust":
        return False
    return path in {
        RECEIPT_PATH,
        "scripts/check_dependency_cycle_anchor.py",
        "scripts/install-git-hooks.sh",
        "scripts/install-pin-hook.sh",
    } or path.startswith(("scripts/hooks/", "scripts/hooks-pin/"))


def scan_constellation(
    repo_root: Path,
    root_commit: str,
    commits: dict[str, str],
    exclusions: list[dict[str, str]],
) -> list[dict[str, Any]]:
    roots = {"trust": repo_root}
    for name, (path, _url) in SUBMODULES.items():
        checkout = repo_root / path
        if not checkout.is_dir():
            fail(f"{path} is not checked out")
        roots[name] = checkout
    scan_commits = {"trust": root_commit, **commits}
    surfaces: list[dict[str, Any]] = []
    path_links: list[tuple[str, str, str, str]] = []
    entries_by_repository: dict[str, dict[str, tuple[str, str, str]]] = {}
    symlink_paths: set[Path] = set()
    for repository in sorted(scan_commits):
        checkout = roots[repository]
        commit = scan_commits[repository]
        object_type = run_git(checkout, ["cat-file", "-t", commit]).decode("ascii", "strict").strip()
        expected_types = {"commit", "tree"} if repository == "trust" else {"commit"}
        if object_type not in expected_types:
            fail(f"{repository} terminal {commit} is not a committed tree/commit object")
        entries = committed_tree_entries(checkout, commit)
        entries_by_repository[repository] = entries
        for path, (mode, entry_type, _oid) in entries.items():
            if mode == "120000":
                symlink_paths.add(lexical_absolute(checkout / path))
            if is_committed_authority_path(repository, path) and (
                entry_type != "blob" or mode not in {"100644", "100755"}
            ):
                fail(
                    f"{repository}:{path} dependency authority must be a regular committed "
                    f"blob, not mode {mode} type {entry_type}"
                )

    for repository in sorted(scan_commits):
        checkout = roots[repository]
        commit = scan_commits[repository]
        entries = entries_by_repository[repository]
        files = sorted(entries)
        if repository != "trust":
            validate_nested_submodules(
                repository,
                checkout,
                commit,
                entries,
                roots,
                symlink_paths,
            )
        root_manifest: dict[str, Any] | None = None
        if "Cargo.toml" in files:
            raw_root_manifest = committed_blob(checkout, commit, "Cargo.toml")
            try:
                root_manifest = parse_toml(raw_root_manifest, f"{repository}:Cargo.toml")
            except AnchorError:
                if might_reference_first_party(raw_root_manifest):
                    raise
        validate_workspace_exclusions(repository, files, root_manifest, exclusions)
        for path in files:
            scope = scope_for(repository, path, exclusions)
            # An exclusion is an explicit, substantive receipt row for a
            # non-workspace fixture/spike.  Do not interpret authority syntax
            # inside it: these trees intentionally contain historical, local,
            # or symlinked locators.  Canonical manifests are still forbidden
            # from reaching an excluded path (checked through `path_links`
            # below), and workspace members cannot be excluded.
            if scope == "excluded":
                continue
            if repository == "ny" and path == "crates/ny-cert/SPEC.md":
                surfaces.extend(scan_ny_spec(path, committed_blob(checkout, commit, path), scope))
            elif repository == "ny" and path == "crates/ny-cert/proofs/README.md":
                surfaces.extend(
                    scan_ny_proof_readme(path, committed_blob(checkout, commit, path), scope)
                )
            elif repository == "ny" and path == "crates/ny-cert/proofs/lean/PROVENANCE.md":
                surfaces.extend(
                    scan_ny_provenance(path, committed_blob(checkout, commit, path), scope)
                )
            elif repository == "ny" and path == "crates/ny-cert/src/cite_check.rs":
                surfaces.extend(
                    scan_ny_cite_source(path, committed_blob(checkout, commit, path), scope)
                )
            elif (
                PurePosixPath(path).name in {"config", "config.toml"}
                and PurePosixPath(path).parent.name == ".cargo"
            ):
                found, links = scan_cargo_config(
                    repository,
                    path,
                    parse_toml(
                        committed_blob(checkout, commit, path),
                        f"{repository}:{path}",
                    ),
                    scope,
                    roots,
                    symlink_paths,
                )
                surfaces.extend(found)
                path_links.extend(links)
            elif path.endswith("Cargo.toml"):
                raw = committed_blob(checkout, commit, path)
                try:
                    manifest = parse_toml(raw, f"{repository}:{path}")
                except AnchorError:
                    if might_reference_first_party(raw):
                        raise
                    continue  # unrelated compiler/test fixture with intentionally invalid TOML
                found, links = scan_cargo_manifest(
                    repository,
                    path,
                    manifest,
                    scope,
                    roots,
                    symlink_paths=symlink_paths,
                )
                surfaces.extend(found)
                path_links.extend(links)
            elif path.endswith("Cargo.lock"):
                # Lock authority is workspace-relative.  Scanning every lock
                # in the Rust/compiler fixture corpus conflates unrelated
                # workspaces and produces thousands of false split revisions.
                # The exact nearest lock for each observed first-party Git
                # manifest is derived below after all manifests are known.
                continue
            elif path.endswith("lakefile.toml"):
                found, links = scan_lakefile(
                    repository,
                    path,
                    parse_toml(
                        committed_blob(checkout, commit, path), f"{repository}:{path}"
                    ),
                    scope,
                    roots,
                    symlink_paths,
                )
                surfaces.extend(found)
                path_links.extend(links)
            elif path.endswith("lake-manifest.json"):
                found, links = scan_lake_manifest(
                    repository,
                    path,
                    parse_json(
                        committed_blob(checkout, commit, path), f"{repository}:{path}"
                    ),
                    scope,
                    roots,
                    symlink_paths,
                )
                surfaces.extend(found)
                path_links.extend(links)
            elif path.endswith("cite-map.json"):
                surfaces.extend(
                    scan_proof_identity(
                        repository,
                        path,
                        parse_json(committed_blob(checkout, commit, path), f"{repository}:{path}"),
                        scope,
                    )
                )
            elif path.endswith("lakefile.lean"):
                raw = committed_blob(checkout, commit, path)
                text = decode_text(raw, f"{repository}:{path}")
                decoded, excessive = repeatedly_unquote(text.lower())
                local_locator = re.search(
                    r"\bfrom\s+(?:git\s+)?[\"']?(?:file:|\.{1,2}/|/)", decoded
                )
                if excessive or local_locator is not None or might_reference_first_party(raw):
                    fail(f"{repository}:{path} contains an unsupported first-party Lake declaration")

    scanned_locks: set[tuple[str, str]] = set()
    for manifest_surface in list(surfaces):
        if manifest_surface["scope"] != "canonical" or manifest_surface["kind"] != "cargo-git":
            continue
        repository = manifest_surface["repository"]
        manifest_dir = cargo_authority_dir(manifest_surface["path"])
        candidates = [
            path
            for path in entries_by_repository[repository]
            if path.endswith("Cargo.lock")
            and scope_for(repository, path, exclusions) == "canonical"
            and path_is_within(manifest_dir, PurePosixPath(path).parent)
        ]
        if not candidates:
            continue
        depth = max(len(PurePosixPath(path).parent.parts) for path in candidates)
        nearest = sorted(
            path for path in candidates if len(PurePosixPath(path).parent.parts) == depth
        )
        if len(nearest) != 1:
            fail(
                f"{repository}:{manifest_surface['path']} has ambiguous nearest Cargo.lock authority {nearest}"
            )
        lock_path = nearest[0]
        lock_key = (repository, lock_path)
        if lock_key in scanned_locks:
            continue
        scanned_locks.add(lock_key)
        checkout = roots[repository]
        commit = scan_commits[repository]
        raw = committed_blob(checkout, commit, lock_path)
        try:
            lock = parse_toml(raw, f"{repository}:{lock_path}")
        except AnchorError:
            if might_reference_first_party(raw):
                raise
            continue
        surfaces.extend(scan_cargo_lock(repository, lock_path, lock, "canonical"))

    by_id: dict[str, dict[str, Any]] = {}
    for surface in surfaces:
        if surface["id"] in by_id:
            fail(f"independent scan produced duplicate surface id {surface['id']!r}")
        by_id[surface["id"]] = surface
    validate_ny_identity_bundle(surfaces)
    if any(
        row["repository"] == "ny"
        and row["dependency"] == "clean"
        and row["kind"] in {"proof-identity", "lake-require", "lake-lock"}
        and row["scope"] != "canonical"
        for row in surfaces
    ):
        fail("NY's seven Clean proof identity surfaces may not be excluded")

    for exclusion in exclusions:
        excluded_entries = entries_by_repository[exclusion["repository"]]
        hidden_authority = [
            path
            for path in excluded_entries
            if (path == exclusion["path"] or path.startswith(exclusion["path"] + "/"))
            and is_committed_authority_path(exclusion["repository"], path)
        ]
        if not hidden_authority:
            fail(
                f"exclusion {exclusion['repository']}:{exclusion['path']} hides no committed dependency-authority file"
            )
    for source_repository, source_path, target_repository, target_path in path_links:
        if scope_for(source_repository, source_path, exclusions) != "canonical":
            continue
        for exclusion in exclusions:
            if exclusion["repository"] == target_repository and (
                target_path == exclusion["path"] or target_path.startswith(exclusion["path"] + "/")
            ):
                fail(
                    f"canonical {source_repository}:{source_path} reaches excluded "
                    f"{target_repository}:{exclusion['path']} by first-party path dependency"
                )
    return sorted(surfaces, key=lambda row: row["id"])


def patch_commit(surface: dict[str, Any], commits: dict[str, str]) -> str:
    if surface["kind"] in {"cargo-patch-path", "cargo-replace-path"}:
        return commits[surface["dependency"]]
    assert surface["rev"] is not None
    return surface["rev"]


def path_is_within(path: PurePosixPath, directory: PurePosixPath) -> bool:
    """Return whether `path` is at/below a normalized repository directory."""
    directory_parts = tuple(part for part in directory.parts if part != ".")
    path_parts = tuple(part for part in path.parts if part != ".")
    return path_parts[: len(directory_parts)] == directory_parts


def cargo_authority_dir(path: str) -> PurePosixPath:
    pure = PurePosixPath(path)
    parent = pure.parent
    if parent.name == ".cargo":
        return parent.parent
    return parent


def matching_patches(surface: dict[str, Any], surfaces: list[dict[str, Any]]) -> list[dict[str, Any]]:
    candidates = [
        candidate
        for candidate in surfaces
        if candidate["scope"] == "canonical"
        and candidate["repository"] == surface["repository"]
        and candidate["dependency"] == surface["dependency"]
        and candidate["package"] == surface["package"]
        and candidate["kind"] in {
            "cargo-patch-git",
            "cargo-patch-path",
            "cargo-replace-git",
            "cargo-replace-path",
        }
    ]
    manifest_dir = cargo_authority_dir(surface["path"])
    applicable = [
        candidate
        for candidate in candidates
        if path_is_within(manifest_dir, cargo_authority_dir(candidate["path"]))
    ]
    if not applicable:
        return []
    depth = max(len(cargo_authority_dir(row["path"]).parts) for row in applicable)
    return [
        row for row in applicable if len(cargo_authority_dir(row["path"]).parts) == depth
    ]


def validate_resolutions(surfaces: list[dict[str, Any]], commits: dict[str, str]) -> None:
    locks: dict[tuple[str, str, str], list[dict[str, Any]]] = {}
    for surface in surfaces:
        if surface["scope"] == "canonical" and surface["kind"] == "cargo-lock":
            locks.setdefault(
                (surface["repository"], surface["dependency"], surface["package"]), []
            ).append(surface)
    for surface in surfaces:
        if surface["scope"] != "canonical" or surface["kind"] != "cargo-git":
            continue
        patches = matching_patches(surface, surfaces)
        patch_revisions = {patch_commit(patch, commits) for patch in patches}
        if len(patch_revisions) > 1:
            fail(f"{surface['id']} has split patch resolutions {sorted(patch_revisions)}")
        expected = next(iter(patch_revisions), surface["rev"])
        manifest_dir = cargo_authority_dir(surface["path"])
        lock_candidates = [
            row
            for row in locks.get(
                (surface["repository"], surface["dependency"], surface["package"]), []
            )
            if path_is_within(manifest_dir, PurePosixPath(row["path"]).parent)
        ]
        if lock_candidates:
            lock_depth = max(len(PurePosixPath(row["path"]).parent.parts) for row in lock_candidates)
            observed = {
                row["rev"]
                for row in lock_candidates
                if len(PurePosixPath(row["path"]).parent.parts) == lock_depth
            }
        else:
            observed = set()
        if patches:
            # Cargo's lockfile preserves the original Git source identity when
            # a workspace `[patch]` redirects that package to a path.  The
            # effective commit is the patch target; demanding that every Git
            # lock row equal the sibling terminal incorrectly rejects the
            # normal, reproducible path-patch pattern used across Trust.
            continue
        elif expected not in observed and surface["locator"].startswith("/workspace/"):
            # Cargo resolves only workspace dependencies that a member actually
            # inherits.  An unused `[workspace.dependencies]` declaration is
            # still an authority edge, but legitimately has no lock row.
            continue
        elif expected not in observed:
            fail(
                f"{surface['id']} manifest rev {expected} is absent from its nearest Cargo.lock; "
                f"observed={sorted(observed)}"
            )

    requires = [row for row in surfaces if row["scope"] == "canonical" and row["kind"] == "lake-require"]
    lake_locks = [row for row in surfaces if row["scope"] == "canonical" and row["kind"] == "lake-lock"]
    path_requires = [
        row for row in surfaces if row["scope"] == "canonical" and row["kind"] == "lake-path"
    ]
    path_locks = [
        row
        for row in surfaces
        if row["scope"] == "canonical" and row["kind"] == "lake-path-lock"
    ]
    proofs = [row for row in surfaces if row["scope"] == "canonical" and row["kind"] == "proof-identity"]
    for requirement in requires:
        directory = PurePosixPath(requirement["path"]).parent
        matches = [
            row
            for row in lake_locks
            if row["repository"] == requirement["repository"]
            and PurePosixPath(row["path"]).parent == directory
            and row["dependency"] == requirement["dependency"]
            and row["package"] == requirement["package"]
        ]
        if len(matches) != 1:
            fail(f"{requirement['id']} must have exactly one matching first-party lake lock row")
        lock = matches[0]
        for field in ("url", "rev", "subdir"):
            if lock[field] != requirement[field]:
                fail(f"{requirement['id']} and {lock['id']} split field {field}")
    for requirement in path_requires:
        directory = PurePosixPath(requirement["path"]).parent
        matches = [
            row
            for row in path_locks
            if row["repository"] == requirement["repository"]
            and PurePosixPath(row["path"]).parent == directory
            and row["dependency"] == requirement["dependency"]
            and row["package"] == requirement["package"]
        ]
        if len(matches) != 1:
            fail(
                f"{requirement['id']} must have exactly one matching first-party "
                "Lake path lock row"
            )
    for proof in proofs:
        matches = [
            row
            for row in requires
            if row["repository"] == proof["repository"]
            and row["dependency"] == proof["dependency"]
            and row["package"] == proof["package"]
            and row["rev"] == proof["rev"]
            and (proof["url"] is None or row["url"] == proof["url"])
            and (proof["subdir"] is None or row["subdir"] == proof["subdir"])
        ]
        if not matches:
            fail(f"{proof['id']} is not bound to a matching canonical Lake requirement")


def derive_direct_edges(
    surfaces: list[dict[str, Any]], commits: dict[str, str]
) -> list[dict[str, Any]]:
    grouped: dict[tuple[str, str], dict[str, set[str]]] = {}
    for surface in surfaces:
        if surface["scope"] != "canonical" or surface["kind"] not in {
            "cargo-git",
            "cargo-path",
            "cargo-patch-git",
            "cargo-patch-path",
            "cargo-replace-git",
            "cargo-replace-path",
            "lake-require",
            "lake-path",
        }:
            continue
        consumer = surface["repository"]
        dependency = surface["dependency"]
        if consumer == dependency:
            continue
        ids = {surface["id"]}
        if surface["kind"] == "cargo-git":
            patches = matching_patches(surface, surfaces)
            revisions = {patch_commit(patch, commits) for patch in patches}
            if len(revisions) > 1:
                fail(f"{surface['id']} has split effective revisions {sorted(revisions)}")
            commit = next(iter(revisions), surface["rev"])
            ids.update(patch["id"] for patch in patches)
        elif surface["kind"] == "cargo-path":
            commit = commits[dependency]
        elif surface["kind"] in {
            "cargo-patch-git",
            "cargo-patch-path",
            "cargo-replace-git",
            "cargo-replace-path",
        }:
            commit = patch_commit(surface, commits)
        elif surface["kind"] == "lake-path":
            commit = commits[dependency]
            ids.update(
                row["id"]
                for row in surfaces
                if row["scope"] == "canonical"
                and row["repository"] == consumer
                and row["dependency"] == dependency
                and row["package"] == surface["package"]
                and row["kind"] == "lake-path-lock"
                and PurePosixPath(row["path"]).parent
                == PurePosixPath(surface["path"]).parent
            )
        else:
            commit = surface["rev"]
            ids.update(
                row["id"]
                for row in surfaces
                if row["scope"] == "canonical"
                and row["repository"] == consumer
                and row["dependency"] == dependency
                and row["rev"] == commit
                and row["kind"] in {"lake-lock", "proof-identity"}
            )
        assert isinstance(commit, str)
        grouped.setdefault((consumer, dependency), {}).setdefault(commit, set()).update(ids)

    edges: list[dict[str, Any]] = []
    for (consumer, dependency), revisions in sorted(grouped.items()):
        if len(revisions) != 1:
            fail(
                f"direct edge {consumer}->{dependency} has split revisions {sorted(revisions)}"
            )
        commit, ids = next(iter(revisions.items()))
        edges.append(
            {
                "consumer": consumer,
                "dependency": dependency,
                "commit": commit,
                "surfaces": sorted(ids),
            }
        )
    return edges


def required_anchors(
    edges: list[dict[str, Any]], commits: dict[str, str]
) -> list[dict[str, str]]:
    return [
        {
            "consumer": edge["consumer"],
            "dependency": edge["dependency"],
            "commit": edge["commit"],
            "terminal": commits[edge["dependency"]],
            "reason": GENERATION_CUT_REASON,
        }
        for edge in edges
        if edge["commit"] != commits[edge["dependency"]]
    ]


def validate_generation_graph(
    edges: list[dict[str, Any]], commits: dict[str, str]
) -> None:
    """Require terminal-generation edges to be acyclic after finite SHA cuts."""
    adjacency: dict[str, set[str]] = {name: set() for name in CONSUMERS}
    for edge in edges:
        if edge["commit"] == commits[edge["dependency"]]:
            adjacency[edge["consumer"]].add(edge["dependency"])

    visiting: list[str] = []
    visited: set[str] = set()

    def visit(node: str) -> None:
        if node in visiting:
            start = visiting.index(node)
            cycle = visiting[start:] + [node]
            fail(
                "terminal-generation first-party dependency cycle has no finite exact-SHA "
                f"cut: {' -> '.join(cycle)}"
            )
        if node in visited:
            return
        visiting.append(node)
        for dependency in sorted(adjacency[node]):
            visit(dependency)
        visiting.pop()
        visited.add(node)

    for node in sorted(adjacency):
        visit(node)


def verify_local_objects(
    repo_root: Path,
    surfaces: list[dict[str, Any]],
    edges: list[dict[str, Any]],
    commits: dict[str, str],
) -> None:
    for dependency, terminal in commits.items():
        checkout = repo_root / SUBMODULES[dependency][0]
        if run_git(checkout, ["cat-file", "-t", terminal]).decode().strip() != "commit":
            fail(f"{dependency} terminal {terminal} is not a local commit object")
    references: set[tuple[str, str]] = {
        (row["dependency"], row["rev"])
        for row in surfaces
        if row["scope"] == "canonical" and row["rev"] is not None
    }
    references.update((edge["dependency"], edge["commit"]) for edge in edges)
    for dependency, commit in sorted(references):
        checkout = repo_root / SUBMODULES[dependency][0]
        object_type = run_git(checkout, ["cat-file", "-t", commit]).decode().strip()
        if object_type != "commit":
            fail(f"{dependency} referenced object {commit} is not a commit")
        terminal = commits[dependency]
        if commit != terminal:
            ancestor = subprocess.run(
                ["git", "-C", str(checkout), "merge-base", "--is-ancestor", commit, terminal],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.PIPE,
                check=False,
            )
            if ancestor.returncode != 0:
                detail = ancestor.stderr.decode("utf-8", "replace").strip()
                fail(
                    f"{dependency} referenced commit {commit} is not an ancestor of terminal {terminal}"
                    + (f": {detail}" if detail else "")
                )


def compare_inventory(label: str, expected: list[dict[str, Any]], actual: list[dict[str, Any]]) -> None:
    expected_rows = [canonical_json(row) for row in expected]
    actual_rows = [canonical_json(row) for row in actual]
    if len(expected_rows) != len(set(expected_rows)):
        fail(f"receipt {label} contains a duplicate semantic row")
    if set(expected_rows) != set(actual_rows):
        missing = sorted(set(actual_rows) - set(expected_rows))
        extra = sorted(set(expected_rows) - set(actual_rows))
        fail(
            f"receipt {label} differs from independently observed committed state: "
            f"missing={missing[:5]}, extra={extra[:5]}"
        )


def verify_remote_main(commits: dict[str, str]) -> None:
    for name, commit in sorted(commits.items()):
        url = SUBMODULES[name][1]
        completed = subprocess.run(
            ["git", "ls-remote", "--exit-code", url, "refs/heads/main"],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
        if completed.returncode != 0:
            detail = (completed.stderr or completed.stdout).decode("utf-8", "replace").strip()
            fail(f"cannot resolve {name} remote main at {url}: {detail}")
        rows = completed.stdout.decode("ascii", "strict").splitlines()
        expected = f"{commit}\trefs/heads/main"
        if rows != [expected]:
            fail(f"{name} terminal {commit} is not exactly remote main; observed={rows}")


def load_exclusion_policy(
    repo_root: Path, root_revision: str, exclusions_path: str
) -> list[dict[str, str]]:
    require_regular_committed_authority(
        repo_root, root_revision, exclusions_path, "constellation exclusion policy"
    )
    value = parse_json(
        committed_blob(repo_root, root_revision, exclusions_path),
        "constellation exclusion policy",
    )
    if not isinstance(value, dict):
        fail("exclusion policy top level must be an object")
    require_exact_keys(value, {"schema", "exclusions"}, "exclusion policy")
    if value["schema"] != EXCLUSIONS_SCHEMA:
        fail(f"exclusion policy schema must be exactly {EXCLUSIONS_SCHEMA!r}")
    return validate_exclusions(value["exclusions"])


def derive_receipt(
    repo_root: Path,
    root_revision: str,
    exclusions: list[dict[str, str]],
    *,
    verify_remote: bool = False,
) -> dict[str, object]:
    require_regular_committed_authority(
        repo_root, root_revision, ".gitmodules", "root .gitmodules authority"
    )
    submodules = committed_submodules(repo_root, root_revision)
    commits = {name: commit for name, (_path, _url, commit) in submodules.items()}
    bindings = [
        {"repository": name, "path": path, "url": url, "commit": commit}
        for name, (path, url, commit) in sorted(submodules.items())
    ]
    surfaces = scan_constellation(repo_root, root_revision, commits, exclusions)
    edges = derive_direct_edges(surfaces, commits)
    validate_generation_graph(edges, commits)
    validate_resolutions(surfaces, commits)
    anchors = required_anchors(edges, commits)
    verify_local_objects(repo_root, surfaces, edges, commits)
    if verify_remote:
        verify_remote_main(commits)
    return {
        "schema": SCHEMA,
        "self": {"repository": "trust", "commit": SELF_SENTINEL},
        "repositories": {
            name: {"url": SUBMODULES[name][1], "commit": commits[name]}
            for name in sorted(SUBMODULES)
        },
        "root_bindings": bindings,
        "exclusions": exclusions,
        "surfaces": surfaces,
        "direct_edges": edges,
        "anchors": anchors,
    }


def index_tree(repo_root: Path) -> str:
    tree = run_git(repo_root, ["write-tree"]).decode("ascii", "strict").strip()
    return require_sha(tree, "root index tree")


def render_receipt(receipt: dict[str, object]) -> str:
    return json.dumps(receipt, indent=2, sort_keys=True, ensure_ascii=True) + "\n"


def write_receipt(repo_root: Path, receipt_path: str, content: str) -> None:
    relative = require_relative_path(receipt_path, "receipt output path")
    destination = repo_root / relative
    if destination.is_symlink():
        fail(f"receipt output {relative} may not be a symlink")
    destination.parent.mkdir(parents=True, exist_ok=True)
    temporary = destination.with_name(destination.name + ".tmp")
    temporary.write_text(content, encoding="utf-8")
    os.replace(temporary, destination)


def verify_constellation(
    repo_root: Path,
    *,
    print_observed: bool = False,
    verify_remote: bool = False,
    receipt_path: str = RECEIPT_PATH,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]], list[dict[str, str]]]:
    root_commit = run_git(repo_root, ["rev-parse", "HEAD"]).decode("ascii", "strict").strip()
    require_sha(root_commit, "root HEAD")
    require_regular_committed_authority(
        repo_root, root_commit, receipt_path, "committed constellation receipt"
    )
    require_regular_committed_authority(
        repo_root, root_commit, ".gitmodules", "committed root .gitmodules"
    )
    receipt = validate_receipt(
        parse_json(committed_blob(repo_root, root_commit, receipt_path), "committed receipt")
    )
    submodules = committed_submodules(repo_root)
    expected_bindings = [
        {"repository": name, "path": path, "url": url, "commit": commit}
        for name, (path, url, commit) in sorted(submodules.items())
    ]
    compare_inventory("root_bindings", receipt["root_bindings"], expected_bindings)
    for name, (_path, _url, commit) in submodules.items():
        if receipt["repositories"][name] != commit:
            fail(
                f"repositories.{name}.commit={receipt['repositories'][name]} does not match root gitlink {commit}"
            )

    surfaces = scan_constellation(
        repo_root, root_commit, receipt["repositories"], receipt["exclusions"]
    )
    edges = derive_direct_edges(surfaces, receipt["repositories"])
    validate_generation_graph(edges, receipt["repositories"])
    validate_resolutions(surfaces, receipt["repositories"])
    anchors = required_anchors(edges, receipt["repositories"])
    verify_local_objects(repo_root, surfaces, edges, receipt["repositories"])
    if verify_remote:
        verify_remote_main(receipt["repositories"])

    if print_observed:
        print(
            json.dumps(
                {"surfaces": surfaces, "direct_edges": edges, "anchors": anchors},
                indent=2,
                sort_keys=True,
            )
        )
        return surfaces, edges, anchors

    compare_inventory("surfaces", receipt["surfaces"], surfaces)
    compare_inventory("direct_edges", receipt["direct_edges"], edges)
    compare_inventory("anchors", receipt["anchors"], anchors)
    return surfaces, edges, anchors


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=Path(__file__).resolve().parents[1],
        help="root Trust checkout (default: script parent)",
    )
    parser.add_argument(
        "--receipt-path",
        default=RECEIPT_PATH,
        help="committed receipt path relative to root (default: %(default)s)",
    )
    parser.add_argument(
        "--print-observed",
        action="store_true",
        help="print independently derived surfaces/edges/anchors without comparing those arrays",
    )
    generation = parser.add_mutually_exclusive_group()
    generation.add_argument(
        "--print-receipt",
        action="store_true",
        help="render a complete receipt from the staged index and exclusion policy",
    )
    generation.add_argument(
        "--write-receipt",
        action="store_true",
        help="atomically regenerate --receipt-path from the staged index and exclusion policy",
    )
    parser.add_argument(
        "--exclusions-path",
        default=EXCLUSIONS_PATH,
        help="staged exclusion-policy path used by receipt generation (default: %(default)s)",
    )
    parser.add_argument(
        "--verify-remote",
        action="store_true",
        help="also require every terminal commit to equal canonical origin main (networked, non-mutating)",
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        repo_root = Path(
            run_git(args.repo_root, ["rev-parse", "--show-toplevel"])
            .decode("utf-8", "strict")
            .strip()
        )
        generating = args.print_receipt or args.write_receipt
        if generating and args.print_observed:
            fail("--print-observed cannot be combined with receipt generation")
        if generating:
            source_tree = index_tree(repo_root)
            exclusions = load_exclusion_policy(
                repo_root, source_tree, args.exclusions_path
            )
            receipt = derive_receipt(
                repo_root,
                source_tree,
                exclusions,
                verify_remote=args.verify_remote,
            )
            rendered = render_receipt(receipt)
            if args.print_receipt:
                print(rendered, end="")
            else:
                write_receipt(repo_root, args.receipt_path, rendered)
        else:
            verify_constellation(
                repo_root,
                print_observed=args.print_observed,
                verify_remote=args.verify_remote,
                receipt_path=args.receipt_path,
            )
    except (AnchorError, OSError, UnicodeDecodeError) as error:
        print("DEPENDENCY CONSTELLATION FAILED:", file=sys.stderr)
        print(f"  - CONSTELLATION-INVALID  {error}", file=sys.stderr)
        return 1
    if args.write_receipt:
        print(f"DEPENDENCY CONSTELLATION RECEIPT WRITTEN: {args.receipt_path}")
        print("  source: staged index tree (stage the receipt before committing)")
    elif not args.print_observed and not args.print_receipt:
        suffix = " + REMOTE MAIN" if args.verify_remote else ""
        print(f"DEPENDENCY CONSTELLATION OK{suffix}")
        print("  root gitlinks: 9/9 exact")
        print("  committed Cargo/Lake surfaces, direct edges, and generation cuts: exact")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
