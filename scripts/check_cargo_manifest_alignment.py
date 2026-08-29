#!/usr/bin/env python3
"""Read-only alignment checks for Trust Cargo manifests.

The Trust repository has several Cargo entry points for different developer
workflows. Four separate jobs live here, and only the second is about drift:

1. Patch-table equality across the root, `crates/` and `targo-trust`
   manifests. Cargo patches are per-workspace and not transitive, so a source
   redirect present in one entry point and missing from another lets that
   workspace resolve a sibling from its live remote instead of the checked-out
   submodule. Root is the baseline; the others must match it exactly.

2. Root/`crates/` workspace membership. The two workspaces deliberately
   overlap and deliberately do not coincide (see the header comments in both
   manifests), so this is reported and, under
   `--workspace-drift-advisory`, does not fail. Patch and fanout findings still
   fail in that mode.

3. The default dependency-fanout policy: `trust-bmc`, `trust-router`,
   `trust-types` and `trust-wp` must keep the native solver backends behind
   optional deps and non-default features, so that depending on the routing
   layer does not pull ay/trust-mc into a consumer's tree.
   `--fanout-tree-proof` proves it against a real `cargo tree` rather than the
   manifest text. This policy is independent of how many workspaces exist and
   outlives any consolidation of them.

4. Local patch integrity and the standalone temporal boundary. Every local
   patch must resolve inside this checkout to a manifest declaring the expected
   package. The fabric fixture must remain an unpatched external consumer, and
   every Git revision in its committed lock must still be declared by the local
   path-dependency closure. This catches stale locks without pretending a
   hard-coded list of optional first-party crates proves Cargo resolution.
"""

from __future__ import annotations

import argparse
import ast
import copy
import re
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Any

try:
    import tomllib
except ModuleNotFoundError:
    try:
        import tomli as tomllib  # type: ignore[no-redef]
    except ModuleNotFoundError:
        tomllib = None  # type: ignore[assignment]


REPO_ROOT = Path(__file__).resolve().parents[1]

MANIFESTS = {
    "root": REPO_ROOT / "Cargo.toml",
    "crates": REPO_ROOT / "crates" / "Cargo.toml",
    "targo-trust": REPO_ROOT / "targo-trust" / "Cargo.toml",
}

TEMPORAL_MANIFEST = REPO_ROOT / "crates" / "trust-spec-temporal" / "Cargo.toml"
TEMPORAL_FABRIC_MANIFEST = (
    REPO_ROOT / "targo-trust" / "tests" / "fixtures" / "fabric" / "Cargo.toml"
)
TEMPORAL_FABRIC_LOCK = TEMPORAL_FABRIC_MANIFEST.with_name("Cargo.lock")

LOCAL_PATCH_MANIFESTS = {
    **MANIFESTS,
    "trust-spec-temporal": TEMPORAL_MANIFEST,
}

LOCK_GIT_SOURCE_RE = re.compile(
    r'^source = "git\+(?P<url>[^"?#]+)\?rev=(?P<requested>[0-9a-f]{7,40})'
    r'#(?P<resolved>[0-9a-f]{40})"$'
)

FANOUT_POLICY_MANIFESTS = {
    "trust-bmc": REPO_ROOT / "crates" / "trust-bmc" / "Cargo.toml",
    "trust-router": REPO_ROOT / "crates" / "trust-router" / "Cargo.toml",
    "trust-types": REPO_ROOT / "crates" / "trust-types" / "Cargo.toml",
    "trust-wp": REPO_ROOT / "crates" / "trust-wp" / "Cargo.toml",
}

ROOT_WORKSPACE_ADVISORY_DETAIL = """\
workspace membership policy:
  Root Cargo.toml is also the rustc workspace. The standalone crates/Cargo.toml
  manifest intentionally exists for Trust pipeline iteration without requiring
  every Trust crate to participate in root rustc workspace commands.
  Keeping drift advisory is acceptable only if root-workspace commands are not
  expected to cover every crates/ workspace member.

  Suggested root Cargo.toml comment if the drift remains intentional:
    # trust: intentionally omitted from the root rustc workspace; covered by
    # crates/Cargo.toml and scripts/check_cargo_manifest_alignment.py.

  If fixing the drift, validate at minimum:
    cargo metadata --manifest-path Cargo.toml --no-deps --format-version 1
    cargo metadata --manifest-path crates/Cargo.toml --no-deps --format-version 1
    cargo check --manifest-path Cargo.toml -p trust-clean -p trust-upstream-compat
    cargo check --manifest-path crates/Cargo.toml -p trust-clean -p trust-upstream-compat

  Because root Cargo.toml has no default-members list, adding root members can
  broaden default root workspace commands. Validate any rustc/x.py path that
  assumes the previous root workspace membership set.
"""

ROOT_WORKSPACE_ADVISORY_SUMMARY = """\
  policy: root Cargo.toml is the rustc workspace; crates/Cargo.toml is the
  standalone Trust pipeline workspace. This advisory is acceptable while root
  workspace commands are not expected to cover every crates/ member.
  details: rerun without --workspace-drift-advisory for manifest-fix guidance.
"""

FANOUT_SPLIT_PROOF_COMMANDS = (
    "cargo tree --manifest-path crates/Cargo.toml -p trust-bmc --edges normal --prefix none "
    "| rg '^(ay-bindings|trust-mc-core|trust-mc-driver)' && false || true",
    "cargo tree --manifest-path crates/Cargo.toml -p trust-router --edges normal --prefix none "
    "| rg '^(ay-bindings|trust-mc-core|trust-mc-driver)' && false || true",
    "cargo check --manifest-path crates/Cargo.toml -p trust-bmc",
    "cargo check --manifest-path crates/Cargo.toml -p trust-router",
    "cargo check --manifest-path crates/Cargo.toml -p trust-bmc --features trust-mc-native-solver",
    "cargo test --manifest-path crates/Cargo.toml -p trust-bmc manifest --lib",
)

FANOUT_TREE_PROOF_PACKAGES = ("trust-bmc", "trust-router")
FANOUT_TREE_FORBIDDEN_DEFAULT_PACKAGES = ("ay-bindings", "trust-mc-core", "trust-mc-driver")


@dataclass(frozen=True)
class PatchEntry:
    source: str
    crate: str
    value: tuple[tuple[str, str], ...]


def load_manifest(path: Path) -> dict[str, Any]:
    if tomllib is None:
        return load_manifest_fallback(path)
    with path.open("rb") as manifest:
        return tomllib.load(manifest)


def strip_comment(line: str) -> str:
    quote: str | None = None
    escaped = False
    for index, char in enumerate(line):
        if escaped:
            escaped = False
            continue
        if char == "\\" and quote == '"':
            escaped = True
            continue
        if quote is not None:
            if char == quote:
                quote = None
            continue
        if char in ('"', "'"):
            quote = char
            continue
        if char == "#":
            return line[:index]
    return line


def split_table_name(name: str) -> list[str]:
    parts: list[str] = []
    current: list[str] = []
    quote: str | None = None
    escaped = False
    for char in name:
        if escaped:
            current.append(char)
            escaped = False
            continue
        if char == "\\" and quote == '"':
            escaped = True
            continue
        if quote is not None:
            current.append(char)
            if char == quote:
                quote = None
            continue
        if char in ('"', "'"):
            quote = char
            current.append(char)
            continue
        if char == ".":
            parts.append("".join(current))
            current = []
            continue
        current.append(char)
    parts.append("".join(current))
    return [parse_key(part) for part in parts if part.strip()]


def balance_delta(line: str, opener: str, closer: str) -> int:
    quote: str | None = None
    escaped = False
    delta = 0
    for char in line:
        if escaped:
            escaped = False
            continue
        if quote is not None:
            if char == "\\" and quote == '"':
                escaped = True
            elif char == quote:
                quote = None
            continue
        if char in ('"', "'"):
            quote = char
            continue
        if char == opener:
            delta += 1
        elif char == closer:
            delta -= 1
    return delta


def is_balanced(line: str) -> bool:
    return balance_delta(line, "[", "]") <= 0 and balance_delta(line, "{", "}") <= 0


def split_top_level(raw: str, delimiter: str = ",") -> list[str]:
    parts: list[str] = []
    current: list[str] = []
    quote: str | None = None
    escaped = False
    square_depth = 0
    curly_depth = 0

    for char in raw:
        if escaped:
            current.append(char)
            escaped = False
            continue
        if quote is not None:
            current.append(char)
            if char == "\\" and quote == '"':
                escaped = True
            elif char == quote:
                quote = None
            continue
        if char in ('"', "'"):
            quote = char
            current.append(char)
            continue
        if char == "[":
            square_depth += 1
            current.append(char)
            continue
        if char == "]":
            square_depth -= 1
            current.append(char)
            continue
        if char == "{":
            curly_depth += 1
            current.append(char)
            continue
        if char == "}":
            curly_depth -= 1
            current.append(char)
            continue
        if char == delimiter and square_depth == 0 and curly_depth == 0:
            parts.append("".join(current).strip())
            current = []
            continue
        current.append(char)

    final = "".join(current).strip()
    if final:
        parts.append(final)
    return parts


def parse_key(raw: str) -> str:
    raw = raw.strip()
    if (raw.startswith('"') and raw.endswith('"')) or (
        raw.startswith("'") and raw.endswith("'")
    ):
        return str(ast.literal_eval(raw))
    return raw


def parse_basic_value(raw: str) -> Any:
    raw = raw.strip().rstrip(",")
    if (raw.startswith('"') and raw.endswith('"')) or (
        raw.startswith("'") and raw.endswith("'")
    ):
        return ast.literal_eval(raw)
    if raw.startswith("[") and raw.endswith("]"):
        body = raw[1:-1].strip()
        if not body:
            return []
        return [parse_basic_value(item) for item in split_top_level(body)]
    if raw.startswith("{") and raw.endswith("}"):
        table: dict[str, Any] = {}
        body = raw[1:-1]
        for item in split_top_level(body):
            if "=" not in item:
                continue
            key, value = item.split("=", 1)
            table[parse_key(key)] = parse_basic_value(value)
        return table
    if raw == "true":
        return True
    if raw == "false":
        return False
    return raw


def assign_nested(manifest: dict[str, Any], table: list[str], key: str, value: Any) -> None:
    current = manifest
    for part in [*table, *split_table_name(key)[:-1]]:
        next_value = current.setdefault(part, {})
        if not isinstance(next_value, dict):
            next_value = {}
            current[part] = next_value
        current = next_value
    current[split_table_name(key)[-1]] = value


def load_manifest_fallback(path: Path) -> dict[str, Any]:
    """Parse the TOML subset this read-only checker needs on Python 3.8-3.10."""
    manifest: dict[str, Any] = {}
    table: list[str] = []
    pending = ""

    for raw_line in path.read_text(encoding="utf-8").splitlines():
        line = strip_comment(raw_line).strip()
        if not line:
            continue
        if pending:
            pending = f"{pending} {line}"
            if not is_balanced(pending):
                continue
            line = pending
            pending = ""
        elif not is_balanced(line):
            pending = line
            continue

        if line.startswith("[") and line.endswith("]"):
            table = split_table_name(line.strip("[]"))
            continue
        if "=" not in line:
            continue
        key, value = line.split("=", 1)
        assign_nested(manifest, table, key.strip(), parse_basic_value(value))

    return manifest


def normalize_path(manifest_path: Path, value: str) -> str:
    path = Path(value)
    if path.is_absolute():
        resolved = path.resolve()
        try:
            return resolved.relative_to(REPO_ROOT).as_posix()
        except ValueError:
            return resolved.as_posix()
    resolved = (manifest_path.parent / path).resolve()
    try:
        return resolved.relative_to(REPO_ROOT).as_posix()
    except ValueError:
        return resolved.as_posix()


def normalize_patch_value(manifest_path: Path, value: Any) -> tuple[tuple[str, str], ...]:
    if isinstance(value, str):
        return (("version", value),)
    if not isinstance(value, dict):
        return (("value", repr(value)),)

    normalized: list[tuple[str, str]] = []
    for key, raw in sorted(value.items()):
        if key == "path" and isinstance(raw, str):
            normalized.append((key, normalize_path(manifest_path, raw)))
        else:
            normalized.append((key, str(raw)))
    return tuple(normalized)


def patch_entries(name: str, manifest_path: Path, manifest: dict[str, Any]) -> set[PatchEntry]:
    del name
    patches = manifest.get("patch", {})
    entries: set[PatchEntry] = set()
    if not isinstance(patches, dict):
        return entries
    for source, crates in patches.items():
        if not isinstance(crates, dict):
            continue
        for crate, value in crates.items():
            entries.add(
                PatchEntry(
                    source=str(source),
                    crate=str(crate),
                    value=normalize_patch_value(manifest_path, value),
                )
            )
    return entries


def relative_display(path: Path) -> str:
    try:
        return path.relative_to(REPO_ROOT).as_posix()
    except ValueError:
        return path.as_posix()


def check_local_patch_targets(
    manifests: dict[str, dict[str, Any]], manifest_paths: dict[str, Path]
) -> list[str]:
    """Validate every local patch, without freezing a hand-written crate list."""
    errors: list[str] = []
    package_name_cache: dict[Path, str | None] = {}

    for manifest_name, manifest in manifests.items():
        patches = manifest.get("patch", {})
        if not isinstance(patches, dict):
            errors.append(f"{manifest_name} [patch] must be a table")
            continue

        for source, table in patches.items():
            if not isinstance(table, dict):
                errors.append(f"{manifest_name} patch table for {source} must be a table")
                continue
            for patch_name, value in table.items():
                if not isinstance(value, dict) or "path" not in value:
                    continue
                raw_path = value.get("path")
                if not isinstance(raw_path, str):
                    errors.append(
                        f"{manifest_name} {source} {patch_name} has no literal local path"
                    )
                    continue

                target = (manifest_paths[manifest_name].parent / raw_path).resolve()
                try:
                    target.relative_to(REPO_ROOT)
                except ValueError:
                    errors.append(
                        f"{manifest_name} {source} {patch_name} path escapes the checkout: "
                        f"{target}"
                    )
                    continue

                target_manifest = target / "Cargo.toml"
                if not target_manifest.is_file():
                    errors.append(
                        f"{manifest_name} {source} {patch_name} path has no Cargo.toml: "
                        f"{relative_display(target)}"
                    )
                    continue

                if target_manifest not in package_name_cache:
                    target_data = load_manifest(target_manifest)
                    target_package = target_data.get("package", {})
                    package_name_cache[target_manifest] = (
                        str(target_package.get("name"))
                        if isinstance(target_package, dict) and "name" in target_package
                        else None
                    )

                expected_name = value.get("package", patch_name)
                found_name = package_name_cache[target_manifest]
                if not isinstance(expected_name, str) or found_name != expected_name:
                    errors.append(
                        f"{manifest_name} {source} {patch_name} path declares package "
                        f"{found_name!r}, expected {expected_name!r}"
                    )

    return errors


def dependency_tables(manifest: dict[str, Any]) -> list[dict[str, Any]]:
    tables: list[dict[str, Any]] = []
    for section in ("dependencies", "build-dependencies"):
        values = manifest.get(section, {})
        if isinstance(values, dict):
            tables.append(values)

    targets = manifest.get("target", {})
    if isinstance(targets, dict):
        for target in targets.values():
            if not isinstance(target, dict):
                continue
            for section in ("dependencies", "build-dependencies"):
                values = target.get(section, {})
                if isinstance(values, dict):
                    tables.append(values)
    return tables


def workspace_dependency(
    dependency_name: str,
    manifest_path: Path,
    manifest_cache: dict[Path, dict[str, Any]],
) -> tuple[Any | None, Path | None]:
    """Resolve one `workspace = true` dependency at its nearest workspace root."""
    for directory in (manifest_path.parent, *manifest_path.parent.parents):
        candidate = directory / "Cargo.toml"
        if not candidate.is_file():
            if directory == REPO_ROOT:
                break
            continue
        if candidate not in manifest_cache:
            manifest_cache[candidate] = load_manifest(candidate)
        candidate_data = manifest_cache[candidate]
        if "workspace" not in candidate_data:
            if directory == REPO_ROOT:
                break
            continue
        return workspace_table(candidate_data, "dependencies").get(dependency_name), candidate
    return None, None


def reachable_git_revisions(start_manifest: Path) -> tuple[set[tuple[str, str]], list[str]]:
    """Collect pinned Git identities reachable through local path dependencies.

    Optional dependencies are included deliberately: a lock may record them, and
    accepting their current declared revision is conservative without accepting
    an obsolete revision that no reachable manifest names anymore.
    """
    allowed: set[tuple[str, str]] = set()
    errors: list[str] = []
    pending = [start_manifest.resolve()]
    visited: set[Path] = set()
    manifest_cache: dict[Path, dict[str, Any]] = {}

    while pending:
        manifest_path = pending.pop()
        if manifest_path in visited:
            continue
        visited.add(manifest_path)
        if not manifest_path.is_file():
            errors.append(
                f"reachable path dependency has no Cargo.toml: {relative_display(manifest_path)}"
            )
            continue
        if manifest_path not in manifest_cache:
            manifest_cache[manifest_path] = load_manifest(manifest_path)
        manifest = manifest_cache[manifest_path]

        for table in dependency_tables(manifest):
            for dependency_name, raw_value in table.items():
                value = raw_value
                value_manifest = manifest_path
                if isinstance(value, dict) and value.get("workspace") is True:
                    inherited, workspace_manifest = workspace_dependency(
                        str(dependency_name), manifest_path, manifest_cache
                    )
                    if inherited is None or workspace_manifest is None:
                        errors.append(
                            f"{relative_display(manifest_path)} inherits undefined workspace "
                            f"dependency {dependency_name}"
                        )
                        continue
                    if isinstance(inherited, dict):
                        merged = dict(inherited)
                        merged.update(
                            {
                                key: item
                                for key, item in value.items()
                                if key != "workspace"
                            }
                        )
                        value = merged
                    else:
                        value = inherited
                    value_manifest = workspace_manifest

                if not isinstance(value, dict):
                    continue
                git_url = value.get("git")
                if git_url is not None:
                    revision = value.get("rev")
                    if not isinstance(git_url, str) or not isinstance(revision, str):
                        errors.append(
                            f"{relative_display(value_manifest)} dependency {dependency_name} "
                            "must pin its Git source with one literal rev"
                        )
                        continue
                    if re.fullmatch(r"[0-9a-f]{7,40}", revision) is None:
                        errors.append(
                            f"{relative_display(value_manifest)} dependency {dependency_name} "
                            f"has non-canonical Git rev {revision!r}"
                        )
                        continue
                    allowed.add((git_url, revision))
                    continue

                raw_path = value.get("path")
                if not isinstance(raw_path, str):
                    continue
                target_manifest = (value_manifest.parent / raw_path / "Cargo.toml").resolve()
                try:
                    target_manifest.relative_to(REPO_ROOT)
                except ValueError:
                    errors.append(
                        f"{relative_display(manifest_path)} dependency {dependency_name} "
                        f"escapes the checkout: {target_manifest}"
                    )
                    continue
                pending.append(target_manifest)

    return allowed, errors


def check_temporal_fabric_boundary(manifest: dict[str, Any]) -> list[str]:
    """Keep the fixture an external consumer rather than a patched twin."""
    errors: list[str] = []
    patches = manifest.get("patch")
    if patches is not None:
        errors.append(
            "temporal fabric fixture must omit all [patch] tables; its external-consumer "
            "boundary depends on observing non-transitive source patches"
        )

    if "workspace" not in manifest or not isinstance(manifest.get("workspace"), dict):
        errors.append("temporal fabric fixture must remain its own workspace")

    dependency = dependency_value(manifest, "trust-spec-temporal")
    if not isinstance(dependency, dict) or not isinstance(dependency.get("path"), str):
        errors.append("temporal fabric fixture must use one local trust-spec-temporal path")
    else:
        resolved = (TEMPORAL_FABRIC_MANIFEST.parent / dependency["path"]).resolve()
        if resolved != TEMPORAL_MANIFEST.parent.resolve():
            errors.append(
                "temporal fabric fixture trust-spec-temporal path does not resolve to the "
                "canonical engine"
            )
    return errors


def check_temporal_fabric_lock_source_revs(lock_text: str | None = None) -> list[str]:
    """Reject a fixture lock whose Git identities disappeared from its path closure."""
    allowed, errors = reachable_git_revisions(TEMPORAL_FABRIC_MANIFEST)
    if lock_text is None:
        if not TEMPORAL_FABRIC_LOCK.is_file() or TEMPORAL_FABRIC_LOCK.is_symlink():
            errors.append("temporal fabric Cargo.lock must be one exact regular file")
            return errors
        lock_text = TEMPORAL_FABRIC_LOCK.read_text(encoding="utf-8")

    git_source_rows = 0
    for line_number, line in enumerate(lock_text.splitlines(), start=1):
        if not re.match(r"^\s*source\s*=", line) or "git+" not in line:
            continue
        git_source_rows += 1
        match = LOCK_GIT_SOURCE_RE.fullmatch(line)
        if match is None:
            errors.append(
                f"temporal fabric Cargo.lock:{line_number} has a malformed or unpinned "
                "Git source row"
            )
            continue
        identity = (match.group("url"), match.group("requested"))
        if identity not in allowed:
            errors.append(
                f"temporal fabric Cargo.lock:{line_number} uses Git revision "
                f"{identity[0]}@{identity[1]} not declared by its reachable manifest closure"
            )
        if not match.group("resolved").startswith(match.group("requested")):
            errors.append(
                f"temporal fabric Cargo.lock:{line_number} resolved commit does not match "
                "its requested rev"
            )

    if git_source_rows == 0:
        errors.append(
            "temporal fabric Cargo.lock has no Git source rows; the unpatched external-consumer "
            "boundary is no longer being exercised"
        )
    return errors


def workspace_list(manifest: dict[str, Any], key: str) -> set[str]:
    workspace = manifest.get("workspace", {})
    if not isinstance(workspace, dict):
        return set()
    values = workspace.get(key, [])
    if not isinstance(values, list):
        return set()
    return {str(value).rstrip("/") for value in values}


def workspace_table(manifest: dict[str, Any], key: str) -> dict[str, Any]:
    workspace = manifest.get("workspace", {})
    if not isinstance(workspace, dict):
        return {}
    values = workspace.get(key, {})
    if not isinstance(values, dict):
        return {}
    return values


def dependency_value(manifest: dict[str, Any], name: str) -> Any:
    for section in ("dependencies", "dev-dependencies", "build-dependencies"):
        values = manifest.get(section, {})
        if isinstance(values, dict) and name in values:
            return values[name]
    return None


def dependency_is_optional(manifest: dict[str, Any], name: str) -> bool:
    value = dependency_value(manifest, name)
    return isinstance(value, dict) and value.get("optional") is True


def dependency_is_declared(manifest: dict[str, Any], name: str) -> bool:
    return dependency_value(manifest, name) is not None


def set_dependency_optional(manifest: dict[str, Any], name: str, optional: bool) -> None:
    dependencies = manifest.setdefault("dependencies", {})
    if not isinstance(dependencies, dict):
        dependencies = {}
        manifest["dependencies"] = dependencies
    value = dependencies.get(name, {})
    if not isinstance(value, dict):
        value = {}
    value["optional"] = optional
    dependencies[name] = value


def remove_dependency(manifest: dict[str, Any], name: str) -> None:
    for section in ("dependencies", "dev-dependencies", "build-dependencies"):
        values = manifest.get(section, {})
        if isinstance(values, dict):
            values.pop(name, None)


def feature_edges(manifest: dict[str, Any], name: str) -> list[str]:
    features = manifest.get("features", {})
    if not isinstance(features, dict):
        return []
    values = features.get(name, [])
    if not isinstance(values, list):
        return []
    return [str(value) for value in values]


def feature_is_declared(manifest: dict[str, Any], name: str) -> bool:
    features = manifest.get("features", {})
    return isinstance(features, dict) and name in features


def feature_edges_containing(edges: list[str], needles: tuple[str, ...]) -> list[str]:
    return sorted(edge for edge in edges if any(needle in edge for needle in needles))


def fanout_split_proof_guidance() -> str:
    lines = [
        "trust-bmc default fanout split completion requires cargo tree evidence:",
    ]
    lines.extend(f"  {command}" for command in FANOUT_SPLIT_PROOF_COMMANDS)
    return "\n".join(lines)


def check_dependency_fanout_policy(manifests: dict[str, dict[str, Any]]) -> list[str]:
    """Lock default lightweight paths away from native solver fanout."""
    errors: list[str] = []

    trust_types = manifests["trust-types"]
    if not dependency_is_optional(trust_types, "ay-bindings"):
        errors.append("trust-types ay-bindings dependency must stay optional")
    if "dep:ay-bindings" not in feature_edges(trust_types, "ay-bridge"):
        errors.append("trust-types ay-bridge must be the only ay-bindings feature edge")
    if not dependency_is_optional(trust_types, "trust-wp-core"):
        errors.append("trust-types trust-wp-core dependency must stay optional")
    if "dep:trust-wp-core" not in feature_edges(trust_types, "trust-wp-bridge"):
        errors.append("trust-types trust-wp-bridge must gate trust-wp-core")

    trust_bmc = manifests["trust-bmc"]
    trust_bmc_default_edges = feature_edges(trust_bmc, "default")
    forbidden_bmc_default_edges = feature_edges_containing(
        trust_bmc_default_edges,
        (
            "trust-mc-native",
            "trust-mc-driver",
            "trust-mc-compiler",
            "trust-mc-trust-bmc",
        ),
        )
    if forbidden_bmc_default_edges:
        errors.append(
            "trust-bmc default features must not enable native trust-mc solver fanout: "
            + ", ".join(forbidden_bmc_default_edges)
            + " (trust-bmc fanout-split plan)"
        )
    if "trust-mc-core-types" in trust_bmc_default_edges:
        errors.append("trust-bmc default features must not publicly re-export trust-mc-core types")
    if not feature_is_declared(trust_bmc, "trust-mc-core-types"):
        errors.append("trust-bmc must declare a trust-mc-core-types API boundary feature")
    if not dependency_is_declared(trust_bmc, "trust-mc-core"):
        errors.append(
            "trust-bmc no longer declares trust-mc-core; update the fanout policy only "
            "after proving the default split.\n" + fanout_split_proof_guidance()
        )
    elif not dependency_is_optional(trust_bmc, "trust-mc-core"):
        errors.append("trust-bmc trust-mc-core dependency must stay optional")
    if not dependency_is_optional(trust_bmc, "ay-bindings"):
        errors.append("trust-bmc ay-bindings dependency must stay optional")
    core_type_edges = feature_edges(trust_bmc, "trust-mc-core-types")
    if "dep:trust-mc-core" not in core_type_edges:
        errors.append("trust-bmc trust-mc-core-types must gate trust-mc-core")
    if "dep:ay-bindings" not in core_type_edges:
        errors.append("trust-bmc trust-mc-core-types must gate ay-bindings")
    if not dependency_is_optional(trust_bmc, "trust-mc-driver"):
        errors.append("trust-bmc trust-mc-driver dependency must stay optional")
    if not dependency_is_optional(trust_bmc, "trust-mc-compiler"):
        errors.append("trust-bmc trust-mc-compiler dependency must stay optional")
    if "dep:trust-mc-driver" not in feature_edges(trust_bmc, "trust-mc-native-driver"):
        errors.append("trust-bmc trust-mc-native-driver must gate trust-mc-driver")
    native_solver_edges = feature_edges(trust_bmc, "trust-mc-native-solver")
    if "trust-mc-driver/native-typed-chc-pdr" not in native_solver_edges:
        errors.append(
            "trust-bmc trust-mc-native-solver must enable trust-mc-driver/native-typed-chc-pdr"
        )
    if any(edge in {"dep:trust-mc-compiler", "trust-mc-native"} for edge in native_solver_edges):
        errors.append("trust-bmc trust-mc-native-solver must not enable trust-mc-compiler")
    native_bundle_edges = feature_edges(trust_bmc, "trust-mc-native-trust-ir-bundle")
    if "trust-mc-core-types" not in native_bundle_edges:
        errors.append("trust-bmc native TrustIr bundle must expose trust-mc-core API types")
    if "trust-mc-native-solver" not in native_bundle_edges:
        errors.append("trust-bmc native TrustIr bundle must opt into the native solver explicitly")

    trust_router = manifests["trust-router"]
    router_default = set(feature_edges(trust_router, "default"))
    forbidden_router_defaults = {
        "ay-backend",
        "trust-build",
        "trust-mc-backend",
        "trust-wp-backend",
        "trust-vc-backend",
    }
    enabled_forbidden = sorted(router_default & forbidden_router_defaults)
    if enabled_forbidden:
        errors.append(
            "trust-router default features must not enable native solver backends: "
            + ", ".join(enabled_forbidden)
        )
    if feature_is_declared(trust_router, "trust-wp-backend"):
        errors.append("trust-router must not restore the retired parsed TrustWP backend feature")
    if dependency_is_declared(trust_router, "trust-wp-core"):
        errors.append(
            "trust-router must not restore the retired TrustWP backend dependency; "
            "historical wire decoding belongs to the zero-capability trust-wp adapter"
        )
    for dep in ("ay", "ay-bindings", "trust-mc-verifier", "trust-vc-core"):
        if not dependency_is_optional(trust_router, dep):
            errors.append(f"trust-router {dep} dependency must stay optional")

    trust_wp = manifests["trust-wp"]
    for dep in ("trust-wp-core", "trust-wp-ay", "trust-ir"):
        if not dependency_is_optional(trust_wp, dep):
            errors.append(f"trust-wp {dep} dependency must stay optional")

    return errors


def check_patch_alignment(manifests: dict[str, dict[str, Any]]) -> list[str]:
    errors: list[str] = []
    by_manifest = {
        name: patch_entries(name, MANIFESTS[name], manifest)
        for name, manifest in manifests.items()
    }

    baseline_name = "root"
    baseline = by_manifest[baseline_name]
    for name, entries in by_manifest.items():
        if name == baseline_name:
            continue
        missing = sorted(baseline - entries, key=lambda entry: (entry.source, entry.crate))
        extra = sorted(entries - baseline, key=lambda entry: (entry.source, entry.crate))
        if missing or extra:
            errors.append(f"{name} patch table drifts from {baseline_name}:")
            for entry in missing:
                errors.append(
                    f"  missing {entry.source} {entry.crate} = {dict(entry.value)}"
                )
            for entry in extra:
                errors.append(
                    f"  extra {entry.source} {entry.crate} = {dict(entry.value)}"
                )
    return errors


def check_workspace_membership(
    manifests: dict[str, dict[str, Any]], *, advisory_summary: bool = False
) -> list[str]:
    root_members = workspace_list(manifests["root"], "members")
    root_excludes = workspace_list(manifests["root"], "exclude")
    crates_members = workspace_list(manifests["crates"], "members")
    crates_excludes = workspace_list(manifests["crates"], "exclude")

    expected_root_members = {f"crates/{member}" for member in crates_members}
    expected_root_excludes = {f"crates/{member}" for member in crates_excludes}
    missing = sorted(
        member
        for member in expected_root_members - root_members
        if member not in root_excludes and member not in expected_root_excludes
    )

    if not missing:
        return []

    errors = ["root workspace is missing crates workspace members:"]
    errors.extend(f"  {member}" for member in missing)
    if advisory_summary:
        errors.extend(ROOT_WORKSPACE_ADVISORY_SUMMARY.rstrip().splitlines())
        return errors
    errors.extend(root_workspace_fix_guidance(manifests, missing))
    return errors


def missing_workspace_deps_for_member(member: str, root_manifest: dict[str, Any]) -> list[str]:
    manifest_path = REPO_ROOT / member / "Cargo.toml"
    if not manifest_path.exists():
        return []

    member_manifest = load_manifest(manifest_path)
    root_workspace_deps = workspace_table(root_manifest, "dependencies")
    deps: set[str] = set()
    for section in ("dependencies", "dev-dependencies", "build-dependencies"):
        raw_deps = member_manifest.get(section, {})
        if not isinstance(raw_deps, dict):
            continue
        for name, value in raw_deps.items():
            if isinstance(value, dict) and value.get("workspace") is True:
                deps.add(str(name))

    return sorted(dep for dep in deps if dep not in root_workspace_deps)


def root_workspace_fix_guidance(
    manifests: dict[str, dict[str, Any]], missing_members: list[str]
) -> list[str]:
    lines = [
        "",
        *ROOT_WORKSPACE_ADVISORY_DETAIL.rstrip().splitlines(),
        "",
        "exact root Cargo.toml changes for a manifest-fix lane:",
        "  add these entries under [workspace].members:",
    ]
    lines.extend(f'    "{member}",' for member in missing_members)

    missing_deps: dict[str, list[str]] = {
        member: missing_workspace_deps_for_member(member, manifests["root"])
        for member in missing_members
    }
    needed_deps = sorted({dep for deps in missing_deps.values() for dep in deps})
    if needed_deps:
        lines.append("  add these entries under [workspace.dependencies]:")
        for dep in needed_deps:
            crates_value = workspace_table(manifests["crates"], "dependencies").get(dep)
            if isinstance(crates_value, dict) and isinstance(crates_value.get("path"), str):
                path = normalize_path(MANIFESTS["crates"], crates_value["path"])
                lines.append(f'    {dep} = {{ path = "{path}" }}')
            else:
                lines.append(f"    {dep} = <copy from crates/Cargo.toml>")
        lines.append("  missing workspace deps by newly added member:")
        for member, deps in missing_deps.items():
            if deps:
                lines.append(f"    {member}: {', '.join(deps)}")
    else:
        lines.append("  no additional [workspace.dependencies] entries are required.")

    return lines


def self_check_error_contains(
    errors: list[str], expected: str, failures: list[str], case_name: str
) -> None:
    if not any(expected in error for error in errors):
        failures.append(f"{case_name}: expected error containing `{expected}`")


def run_self_check() -> list[str]:
    failures: list[str] = []
    local_patch_manifests = {
        name: load_manifest(path)
        for name, path in LOCAL_PATCH_MANIFESTS.items()
    }
    local_patch_errors = check_local_patch_targets(
        local_patch_manifests, LOCAL_PATCH_MANIFESTS
    )
    if local_patch_errors:
        failures.append(
            "current local patch targets should pass: " + "; ".join(local_patch_errors)
        )

    fabric_manifest = load_manifest(TEMPORAL_FABRIC_MANIFEST)
    fabric_boundary_errors = check_temporal_fabric_boundary(fabric_manifest)
    if fabric_boundary_errors:
        failures.append(
            "current temporal fabric boundary should pass: "
            + "; ".join(fabric_boundary_errors)
        )

    fabric_lock_errors = check_temporal_fabric_lock_source_revs()
    if fabric_lock_errors:
        failures.append(
            "current temporal fabric lock should pass: " + "; ".join(fabric_lock_errors)
        )

    fanout_manifests = {
        name: load_manifest(path)
        for name, path in FANOUT_POLICY_MANIFESTS.items()
    }

    baseline_errors = check_dependency_fanout_policy(fanout_manifests)
    if baseline_errors:
        failures.append("current fanout policy should pass: " + "; ".join(baseline_errors))

    case = copy.deepcopy(local_patch_manifests)
    case["root"]["patch"]["https://github.com/alabsystems/ay"]["ay"] = {
        "path": "first-party/ay/crates/ay-core"
    }
    self_check_error_contains(
        check_local_patch_targets(case, LOCAL_PATCH_MANIFESTS),
        "declares package 'ay-core', expected 'ay'",
        failures,
        "local patch wrong-package target",
    )

    case = copy.deepcopy(local_patch_manifests)
    case["root"]["patch"]["https://github.com/alabsystems/ay"]["ay"] = {
        "path": "first-party/ay/crates/does-not-exist"
    }
    self_check_error_contains(
        check_local_patch_targets(case, LOCAL_PATCH_MANIFESTS),
        "path has no Cargo.toml",
        failures,
        "local patch missing target",
    )

    case = copy.deepcopy(fabric_manifest)
    case["patch"] = {
        "https://github.com/alabsystems/ay.git": {
            "ay": {"path": "../../../../first-party/ay/crates/ay"}
        }
    }
    self_check_error_contains(
        check_temporal_fabric_boundary(case),
        "must omit all [patch] tables",
        failures,
        "temporal fabric patch regression",
    )

    case = copy.deepcopy(fabric_manifest)
    case["dependencies"]["trust-spec-temporal"] = {
        "path": "../../../../crates/trust-temporal"
    }
    self_check_error_contains(
        check_temporal_fabric_boundary(case),
        "does not resolve to the canonical engine",
        failures,
        "temporal fabric engine shadow regression",
    )

    lock_text = TEMPORAL_FABRIC_LOCK.read_text(encoding="utf-8")
    stale_lock = re.sub(
        r"\?rev=[0-9a-f]{40}#[0-9a-f]{40}",
        "?rev=0000000000000000000000000000000000000000"
        "#0000000000000000000000000000000000000000",
        lock_text,
        count=1,
    )
    self_check_error_contains(
        check_temporal_fabric_lock_source_revs(stale_lock),
        "not declared by its reachable manifest closure",
        failures,
        "temporal fabric stale Git revision",
    )

    malformed_lock = lock_text.replace('source = "git+', ' source = "git+', 1)
    self_check_error_contains(
        check_temporal_fabric_lock_source_revs(malformed_lock),
        "malformed or unpinned Git source row",
        failures,
        "temporal fabric malformed Git source",
    )

    required_proof_fragments = (
        "cargo tree --manifest-path crates/Cargo.toml -p trust-bmc",
        "cargo tree --manifest-path crates/Cargo.toml -p trust-router",
        "rg '^(ay-bindings|trust-mc-core|trust-mc-driver)'",
        "cargo check --manifest-path crates/Cargo.toml -p trust-bmc",
        "cargo check --manifest-path crates/Cargo.toml -p trust-router",
        "cargo check --manifest-path crates/Cargo.toml -p trust-bmc --features trust-mc-native-solver",
        "cargo test --manifest-path crates/Cargo.toml -p trust-bmc manifest --lib",
    )
    proof_text = "\n".join(FANOUT_SPLIT_PROOF_COMMANDS)
    for fragment in required_proof_fragments:
        if fragment not in proof_text:
            failures.append(f"fanout split proof commands missing `{fragment}`")

    guidance = fanout_split_proof_guidance()
    for command in FANOUT_SPLIT_PROOF_COMMANDS:
        if command not in guidance:
            failures.append(f"fanout split proof guidance omits `{command}`")

    case = copy.deepcopy(fanout_manifests)
    case["trust-bmc"].setdefault("features", {})["default"] = ["trust-mc-native-solver"]
    self_check_error_contains(
        check_dependency_fanout_policy(case),
        "trust-bmc default features must not enable native trust-mc solver fanout",
        failures,
        "trust-bmc default native solver regression",
    )

    case = copy.deepcopy(fanout_manifests)
    case["trust-bmc"].setdefault("features", {})["default"] = ["trust-mc-core-types"]
    self_check_error_contains(
        check_dependency_fanout_policy(case),
        "trust-bmc default features must not publicly re-export trust-mc-core types",
        failures,
        "trust-bmc default core API regression",
    )

    case = copy.deepcopy(fanout_manifests)
    case["trust-bmc"].setdefault("features", {}).pop("trust-mc-core-types", None)
    self_check_error_contains(
        check_dependency_fanout_policy(case),
        "trust-bmc must declare a trust-mc-core-types API boundary feature",
        failures,
        "trust-bmc core API feature boundary regression",
    )

    case = copy.deepcopy(fanout_manifests)
    case["trust-bmc"].setdefault("features", {})["trust-mc-native-trust-ir-bundle"] = [
        edge
        for edge in feature_edges(case["trust-bmc"], "trust-mc-native-trust-ir-bundle")
        if edge != "trust-mc-core-types"
    ]
    self_check_error_contains(
        check_dependency_fanout_policy(case),
        "trust-bmc native TrustIr bundle must expose trust-mc-core API types",
        failures,
        "trust-bmc native bundle core API regression",
    )

    case = copy.deepcopy(fanout_manifests)
    case["trust-bmc"].setdefault("features", {})["trust-mc-core-types"] = [
        edge
        for edge in feature_edges(case["trust-bmc"], "trust-mc-core-types")
        if edge != "dep:trust-mc-core"
    ]
    self_check_error_contains(
        check_dependency_fanout_policy(case),
        "trust-bmc trust-mc-core-types must gate trust-mc-core",
        failures,
        "trust-bmc optional core feature edge",
    )

    case = copy.deepcopy(fanout_manifests)
    remove_dependency(case["trust-bmc"], "trust-mc-core")
    self_check_error_contains(
        check_dependency_fanout_policy(case),
        "trust-bmc no longer declares trust-mc-core",
        failures,
        "trust-bmc missing core proof gate",
    )

    case = copy.deepcopy(fanout_manifests)
    set_dependency_optional(case["trust-bmc"], "ay-bindings", True)
    set_dependency_optional(case["trust-bmc"], "trust-mc-core", False)
    self_check_error_contains(
        check_dependency_fanout_policy(case),
        "trust-bmc trust-mc-core dependency must stay optional",
        failures,
        "trust-bmc core optionality regression",
    )

    case = copy.deepcopy(fanout_manifests)
    case["trust-router"].setdefault("features", {})["default"] = ["ay-backend"]
    self_check_error_contains(
        check_dependency_fanout_policy(case),
        "trust-router default features must not enable native solver backends",
        failures,
        "trust-router default backend regression",
    )

    case = copy.deepcopy(fanout_manifests)
    case["trust-router"].setdefault("features", {})["trust-wp-backend"] = []
    self_check_error_contains(
        check_dependency_fanout_policy(case),
        "trust-router must not restore the retired parsed TrustWP backend feature",
        failures,
        "trust-router retired TrustWP feature regression",
    )

    case = copy.deepcopy(fanout_manifests)
    set_dependency_optional(case["trust-router"], "trust-wp-core", True)
    self_check_error_contains(
        check_dependency_fanout_policy(case),
        "trust-router must not restore the retired TrustWP backend dependency",
        failures,
        "trust-router retired TrustWP dependency regression",
    )

    case = copy.deepcopy(fanout_manifests)
    set_dependency_optional(case["trust-types"], "ay-bindings", False)
    self_check_error_contains(
        check_dependency_fanout_policy(case),
        "trust-types ay-bindings dependency must stay optional",
        failures,
        "trust-types ay bridge regression",
    )

    case = copy.deepcopy(fanout_manifests)
    set_dependency_optional(case["trust-wp"], "trust-wp-core", False)
    self_check_error_contains(
        check_dependency_fanout_policy(case),
        "trust-wp trust-wp-core dependency must stay optional",
        failures,
        "trust-wp native core regression",
    )

    return failures


def cargo_tree_normal_edges(package: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [
            "cargo",
            "tree",
            "--manifest-path",
            "crates/Cargo.toml",
            "-p",
            package,
            "--edges",
            "normal",
            "--prefix",
            "none",
        ],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )


def run_fanout_tree_proof() -> list[str]:
    failures: list[str] = []
    for package in FANOUT_TREE_PROOF_PACKAGES:
        result = cargo_tree_normal_edges(package)
        if result.returncode != 0:
            failures.append(
                f"{package}: cargo tree failed with exit {result.returncode}: "
                + result.stderr.strip()
            )
            continue
        matched = [
            line
            for line in result.stdout.splitlines()
            if any(line.startswith(f"{forbidden} ") for forbidden in FANOUT_TREE_FORBIDDEN_DEFAULT_PACKAGES)
        ]
        if matched:
            failures.append(
                f"{package}: default normal dependency tree still contains forbidden fanout:\n"
                + "\n".join(f"  {line}" for line in matched)
            )
    return failures


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--workspace-drift-advisory",
        action="store_true",
        help=(
            "report root/crates workspace membership drift without failing; "
            "patch table drift still fails"
        ),
    )
    parser.add_argument(
        "--self-check",
        action="store_true",
        help="run focused regression checks for manifest alignment and fanout policy logic",
    )
    parser.add_argument(
        "--fanout-tree-proof",
        action="store_true",
        help=(
            "prove default trust-bmc/trust-router normal trees exclude "
            "ay-bindings, trust-mc-core, and trust-mc-driver"
        ),
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.self_check:
        failures = run_self_check()
        if failures:
            print("Cargo manifest alignment self-check failed:")
            for failure in failures:
                print(f"  {failure}")
            return 1
        print("Cargo manifest alignment self-check passed.")
        return 0
    if args.fanout_tree_proof:
        failures = run_fanout_tree_proof()
        if failures:
            print("Cargo default fanout tree proof failed:")
            for failure in failures:
                print(failure)
            print(fanout_split_proof_guidance())
            return 1
        print("Cargo default fanout tree proof passed.")
        return 0

    manifests = {
        name: load_manifest(path)
        for name, path in MANIFESTS.items()
    }

    patch_errors = check_patch_alignment(manifests)
    local_patch_manifests = {
        name: load_manifest(path)
        for name, path in LOCAL_PATCH_MANIFESTS.items()
    }
    local_patch_errors = check_local_patch_targets(
        local_patch_manifests, LOCAL_PATCH_MANIFESTS
    )
    fabric_manifest = load_manifest(TEMPORAL_FABRIC_MANIFEST)
    fabric_boundary_errors = check_temporal_fabric_boundary(fabric_manifest)
    fabric_lock_errors = check_temporal_fabric_lock_source_revs()
    membership_errors = check_workspace_membership(
        manifests, advisory_summary=args.workspace_drift_advisory
    )
    fanout_manifests = {
        name: load_manifest(path)
        for name, path in FANOUT_POLICY_MANIFESTS.items()
    }
    fanout_errors = check_dependency_fanout_policy(fanout_manifests)
    errors = [
        *patch_errors,
        *local_patch_errors,
        *fabric_boundary_errors,
        *fabric_lock_errors,
        *membership_errors,
        *fanout_errors,
    ]

    if errors:
        advisory_only = (
            args.workspace_drift_advisory
            and not patch_errors
            and not local_patch_errors
            and not fabric_boundary_errors
            and not fabric_lock_errors
            and not fanout_errors
        )
        if advisory_only:
            print("Cargo manifest alignment advisory:")
        else:
            print("Cargo manifest alignment check failed:")
        if not patch_errors and not local_patch_errors:
            print(
                "patch tables are aligned across root, crates, and targo-trust, "
                "and local targets are valid."
            )
        if not fabric_boundary_errors and not fabric_lock_errors:
            print("temporal fabric external boundary and lock revisions are coherent.")
        if not fanout_errors:
            print("dependency fanout manifest policy is preserved.")
        if not membership_errors:
            print("root workspace membership includes all crates workspace members.")
        for error in errors:
            print(error)
        return 0 if advisory_only else 1

    print(
        "Cargo manifest alignment, local patch integrity, temporal fabric boundary, "
        "and dependency fanout policy check passed."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
