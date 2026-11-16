#!/usr/bin/env python3
"""Audit patch targets, fabric consumers, solver fanout and codec retirement.

Targo resolves one canonical workspace. There are no parallel workspace patch
or membership tables to compare. These checks cover policies Cargo does not:
local patch identity, isolated consumer revisions and optional solver boundaries.
"""

from __future__ import annotations

import argparse
import ast
import copy
import os
import shutil
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


def prefer_real_toml_parser() -> None:
    """Re-exec under Python >= 3.11 when no real TOML parser is importable.

    The subset parser below (`load_manifest_fallback`) exists so this checker
    can run on Python 3.8-3.10, but it reads only the TOML subset the manifests
    used when it was written. They have since grown triple-quoted strings, and
    on this repo's machines the default `python3` is 3.9 — so the required
    `fast.cargo-manifest-alignment` row crashed with a SyntaxError and exited 1,
    the same code as a real finding (measured 2026-09-27: red since 2026-09-10,
    and not for any alignment reason). Same shim, same interpreter search order,
    as scripts/validate_upstream_rust_compat_summary.py.
    """
    if sys.version_info >= (3, 11):
        return
    try:
        import tomli  # noqa: F401
    except ModuleNotFoundError:
        pass
    else:
        return
    for minor in (14, 13, 12, 11):
        candidate = shutil.which(f"python3.{minor}")
        if candidate:
            os.execv(candidate, [candidate, *sys.argv])


if __name__ == "__main__":
    prefer_real_toml_parser()

try:
    import tomllib
except ModuleNotFoundError:
    try:
        import tomli as tomllib  # type: ignore[no-redef]
    except ModuleNotFoundError:
        tomllib = None  # type: ignore[assignment]


REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT / "scripts" / "lib"))
import rust_lex

MANIFESTS = {"root": REPO_ROOT / "Cargo.toml"}

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
    "root": REPO_ROOT / "Cargo.toml",
    "trust-coordinator": REPO_ROOT / "crates" / "trust-coordinator" / "Cargo.toml",
    "trust-file-lock": REPO_ROOT / "crates" / "trust-file-lock" / "Cargo.toml",
    "trust-rand": REPO_ROOT / "crates" / "trust-rand" / "Cargo.toml",
    "trust-bmc": REPO_ROOT / "crates" / "trust-bmc" / "Cargo.toml",
    "trust-router": REPO_ROOT / "crates" / "trust-router" / "Cargo.toml",
    "trust-types": REPO_ROOT / "crates" / "trust-types" / "Cargo.toml",
    "trust-semantics": REPO_ROOT / "crates" / "trust-semantics" / "Cargo.toml",
    "trust-wp": REPO_ROOT / "crates" / "trust-wp" / "Cargo.toml",
}

FANOUT_SPLIT_PROOF_COMMANDS = (
    "targo tree --manifest-path Cargo.toml -p trust-bmc --edges normal --prefix none "
    "| rg '^(ay-bindings|trust-mc-core|trust-mc-driver)' && false || true",
    "targo tree --manifest-path Cargo.toml -p trust-router --edges normal --prefix none "
    "| rg '^(ay-bindings|trust-mc-core|trust-mc-driver)' && false || true",
    "targo --unverified check --manifest-path Cargo.toml -p trust-bmc",
    "targo --unverified check --manifest-path Cargo.toml -p trust-router",
    "targo --unverified check --manifest-path Cargo.toml -p trust-bmc --features trust-mc-native-solver",
    "targo --unverified test --manifest-path Cargo.toml -p trust-bmc manifest --lib",
    "targo tree --manifest-path Cargo.toml -p trust-coordinator --edges normal,build --prefix none",
    "targo --unverified check --manifest-path Cargo.toml -p trust-coordinator",
)

FANOUT_TREE_PROOF_PACKAGES = ("trust-bmc", "trust-router", "trust-coordinator")
FANOUT_TREE_FORBIDDEN_DEFAULT_PACKAGES = ("ay-bindings", "trust-mc-core", "trust-mc-driver")


class FallbackParseRefused(Exception):
    """The subset parser met TOML it does not implement.

    Kept distinct from every alignment finding: a checker that cannot read its
    input has not run, and must not exit with the code that means "misaligned".
    """


FALLBACK_REFUSED_EXIT = 2


def load_manifest(path: Path) -> dict[str, Any]:
    if tomllib is None:
        try:
            return load_manifest_fallback(path)
        except (SyntaxError, ValueError) as exc:
            raise FallbackParseRefused(
                f"{path}: the Python 3.8-3.10 subset TOML parser cannot read this "
                f"manifest ({type(exc).__name__}: {exc}). No alignment verdict was "
                f"reached. Run under Python >= 3.11, or install tomli."
            ) from exc
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


def production_dependency_is_declared(
    manifest: dict[str, Any], workspace: dict[str, Any], name: str
) -> bool:
    """Find normal/build dependencies, including target and package aliases.

    Dev dependencies supply fixtures without adding a production backend.
    Workspace aliases inherit their package identity from the workspace owner.
    """
    scopes = [manifest]
    targets = manifest.get("target", {})
    if isinstance(targets, dict):
        scopes.extend(value for value in targets.values() if isinstance(value, dict))
    inherited = workspace_table(workspace, "dependencies")
    for scope in scopes:
        for section in ("dependencies", "build-dependencies"):
            dependencies = scope.get(section, {})
            if not isinstance(dependencies, dict):
                continue
            for alias, declaration in dependencies.items():
                identities = [alias]
                if isinstance(declaration, dict):
                    identities.append(declaration.get("package", alias))
                    if declaration.get("workspace") is True:
                        owner = inherited.get(alias, {})
                        if isinstance(owner, dict):
                            identities.append(owner.get("package", alias))
                if name in identities:
                    return True
    return False


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
        "trust-bmc default fanout split completion requires targo tree evidence:",
    ]
    lines.extend(f"  {command}" for command in FANOUT_SPLIT_PROOF_COMMANDS)
    return "\n".join(lines)


def check_dependency_fanout_policy(manifests: dict[str, dict[str, Any]]) -> list[str]:
    """Lock default lightweight paths away from native solver fanout."""
    errors: list[str] = []

    coordinator = manifests["trust-coordinator"]
    if (
        set(coordinator.get("dependencies", {}))
        != {"libc", "serde", "serde_json", "sha2", "thiserror", "trust-budget", "trust-file-lock", "trust-rand"}
        or any(
            value != {"workspace": True}
            for value in coordinator.get("dependencies", {}).values()
        )
        or coordinator.get("build-dependencies", {})
        or coordinator.get("features", {})
    ):
        errors.append("trust-coordinator must keep its fixed solver-free dependency boundary")
    if coordinator.get("target", {}):
        errors.append("trust-coordinator platform dependencies must remain in trust-file-lock")

    # Shared ownership must stay independent of daemon, cache and solver code.
    # Check the new leaf transitively rather than merely allowing its name.
    file_lock = manifests["trust-file-lock"]
    if (
        set(file_lock.get("dependencies", {})) != {"libc", "thiserror"}
        or any(value != {"workspace": True}
               for value in file_lock.get("dependencies", {}).values())
        or any(file_lock.get(table, {}) for table in
               ("build-dependencies", "target", "features"))
    ):
        errors.append("trust-file-lock must keep its fixed solver-free ownership boundary")

    # Admission incarnations use the existing OS entropy leaf. Keep that
    # dependency solver-free transitively, not merely allowed by name.
    entropy = manifests["trust-rand"]
    if any(entropy.get(table, {}) for table in (
        "dependencies", "build-dependencies", "target", "features"
    )):
        errors.append("trust-rand must remain an unconditional dependency-free entropy leaf")

    # The shared range layer must not turn a pure VC-generator dependency
    # into an implicit request for the optional Discharge Try implementation.
    semantic_types = manifests["trust-semantics"].get("dependencies", {}).get("trust-types")
    if (not isinstance(semantic_types, dict)
            or semantic_types.get("default-features") is not False
            or set(semantic_types.get("features", ())) & {"default", "try-sugar"}):
        errors.append("trust-semantics must keep trust-types default and try-sugar features disabled")

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
    # The two retired backend features stay listed, as trust-wp-backend does: a
    # name that is not declared costs nothing here, and it keeps a revival from
    # landing as a default.
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
    if production_dependency_is_declared(
        trust_router, manifests.get("root", {}), "trust-wp-core"
    ):
        errors.append(
            "trust-router must not restore the retired TrustWP backend dependency in production; "
            "historical wire decoding belongs to the zero-capability trust-wp adapter"
        )
    for dep in ("ay", "ay-bindings"):
        if not dependency_is_optional(trust_router, dep):
            errors.append(f"trust-router {dep} dependency must stay optional")
    # Retired with their features; if either comes back it must come back optional.
    for dep in ("trust-mc-verifier", "trust-vc-core"):
        if dependency_is_declared(trust_router, dep) and not dependency_is_optional(trust_router, dep):
            errors.append(f"trust-router {dep} dependency must stay optional")

    trust_wp = manifests["trust-wp"]
    for dep in ("trust-wp-core", "trust-ir"):
        if not dependency_is_optional(trust_wp, dep):
            errors.append(f"trust-wp {dep} dependency must stay optional")

    return errors


def wp_facade_sources() -> dict[str, str]:
    root = REPO_ROOT / "crates" / "trust-wp" / "src"
    return {
        path.relative_to(root).as_posix(): path.read_text(encoding="utf-8")
        for path in sorted(root.rglob("*.rs"))
    }


def check_wp_native_facade_retirement(
    manifest: dict[str, Any],
    workspace: dict[str, Any],
    sources: dict[str, str],
) -> list[str]:
    """Keep the retired request/body API out of the historical WP facade.

    This holds a concrete retirement and dependency boundary; it does not
    establish semantic equivalence or prove the absence of arbitrary decoders.
    Native body verification belongs to first-party trust-wp-lib via the router.
    """
    errors: list[str] = []
    tables = dependency_tables(manifest)
    # Tests and platform-specific aliases must not restore this solver edge.
    for owner in [manifest, *manifest.get("target", {}).values()]:
        if isinstance(owner, dict) and isinstance(owner.get("dev-dependencies"), dict):
            tables.append(owner["dev-dependencies"])
    inherited = workspace_table(workspace, "dependencies")
    for table in tables:
        for alias, value in table.items():
            resolved = value
            if isinstance(value, dict) and value.get("workspace") is True:
                resolved = inherited.get(alias, value)
            package = resolved.get("package", alias) if isinstance(resolved, dict) else alias
            if package in {"trust-wp-ay", "trust-wp-lib"}:
                errors.append(
                    f"trust-wp facade must not restore retired native solver dependency {package} "
                    f"(alias {alias}); use first-party trust-wp-lib through the router"
                )
    if "lib.rs" not in sources:
        errors.append("trust-wp facade library source is missing; retirement cannot be checked")
    if "native.rs" in sources:
        errors.append("trust-wp facade must not restore retired src/native.rs")
    retired = re.compile(
        r"\b(?:NativeTrustWpRequest|NativePureBody|NativeTrustWpMir|NativeTrustWpExpr|verify_native)\b"
    )
    for path, source in sources.items():
        if retired.search(source):
            errors.append(f"trust-wp facade {path} restores a retired native request/body API")
    return errors



FORMULA_CODEC_PATHS = {
    "trust-types": "crates/trust-types/src/trust_formula_v1.rs",
    "trust-wp-core": "first-party/trust-wp/crates/trust-wp-core/src/verify_bundle/trust_formula.rs",
}

NATIVE_SP_SOURCE_PATH = "first-party/trust-wp/crates/trust-wp-lib/src/trust_ir_native.rs"


def native_sp_source() -> str:
    path = REPO_ROOT / NATIVE_SP_SOURCE_PATH
    return path.read_text(encoding="utf-8") if path.is_file() else ""


def shared_formula_codec_inputs() -> tuple[dict[str, Any], dict[str, Any], dict[str, str]]:
    manifests, workspaces, sources = {}, {}, {}
    for owner, source in FORMULA_CODEC_PATHS.items():
        path = REPO_ROOT / source
        manifest = path.parents[1] / "Cargo.toml" if owner == "trust-types" else path.parents[2] / "Cargo.toml"
        workspace = REPO_ROOT if owner == "trust-types" else REPO_ROOT / "first-party/trust-wp"
        # An absent submodule is missing evidence, not a successful retirement.
        manifests[owner] = load_manifest(manifest) if manifest.is_file() else {}
        workspaces[owner] = load_manifest(workspace / "Cargo.toml") if (workspace / "Cargo.toml").is_file() else {}
        sources[owner] = path.read_text(encoding="utf-8") if path.is_file() else ""
    return manifests, workspaces, sources


def _production_rust(source: str) -> tuple[Any, str]:
    lexed = rust_lex.lex(source)
    code = list(lexed.code)
    for start, end in lexed.test_spans:
        code[start:end] = " " * (end - start)
    return lexed, "".join(code)


def check_native_sp_splitter_retirement(source: str) -> list[str]:
    """Hold the two retired native SP raw-JSON splitter declarations.

    Atom serialization and original-JSON pointer projection remain legitimate.
    This checks exact known declarations, not arbitrary renamed implementations.
    """
    if not source.strip():
        return ["trust-wp-lib native SP source is missing; splitter retirement cannot be checked"]
    _, code = _production_rust(source)
    retired = {"split_trust_formula_body", "flatten_trust_formula_conjunction"}
    restored = sorted(set(re.findall(r"\bfn\s+(?:r#)?(\w+)\b", code)) & retired)
    if restored:
        return ["trust-wp-lib native SP restores retired raw JSON splitters: " + ", ".join(restored)]
    return []


def native_sp_splitter_self_check() -> list[str]:
    source = native_sp_source()
    baseline = check_native_sp_splitter_retirement(source)
    if baseline:
        return ["current native SP splitter retirement should pass: " + error for error in baseline]
    failures: list[str] = []
    for name in ("split_trust_formula_body", "flatten_trust_formula_conjunction"):
        self_check_error_contains(
            check_native_sp_splitter_retirement(source + f"\nfn {name}() {{}}"),
            "retired raw JSON splitters", failures, f"native SP {name} reintroduction",
        )
    self_check_error_contains(
        check_native_sp_splitter_retirement(""), "native SP source is missing",
        failures, "native SP missing source",
    )
    return failures


def _rust_imports(code: str) -> dict[str, str]:
    """Expand bounded Rust use trees, retaining aliases and rejecting collisions."""
    bindings: dict[str, str] = {}

    def expand(tree: str, prefix: str = "") -> None:
        if "{" in tree:
            start = tree.index("{")
            if not tree.rstrip().endswith("}"):
                return
            for child in split_top_level(tree[start + 1:tree.rfind("}")]):
                expand(child.strip(), prefix + tree[:start])
            return
        parts = re.split(r"\s+as\s+", tree.strip())
        if len(parts) > 2:
            return
        path = re.sub(r"\s+", "", prefix + parts[0]).lstrip(":")
        if path.endswith("::self"):
            path = path[:-6]
        if not re.fullmatch(r"(?:r#)?\w+(?:::(?:r#)?\w+)*", path):
            return
        alias = parts[-1].strip() if len(parts) == 2 else path.split("::")[-1]
        alias = alias[2:] if alias.startswith("r#") else alias
        path = path.replace("r#", "")
        bindings[alias] = path if alias not in bindings else ""

    for statement in re.finditer(r"\buse\s+([^;]+);", code):
        expand(statement.group(1))
    return bindings


def _rust_paths(code: str, imports: dict[str, str]) -> list[tuple[str, int, int]]:
    paths = []
    for match in re.finditer(r"\b(?:r#)?[A-Za-z_]\w*(?:\s*::\s*(?:r#)?[A-Za-z_]\w*)*", code):
        path = re.sub(r"\s+", "", match.group()).replace("r#", "")
        first, *rest = path.split("::")
        if first in imports:
            path = "::".join([imports[first], *rest])
        paths.append((path, match.start(), match.end()))
    return paths


def _rust_function(code: str, name: str) -> str | None:
    functions = list(re.finditer(r"\bfn\s+" + re.escape(name) + r"\s*\(", code))
    if len(functions) != 1:
        return None
    start = code.find("{", functions[0].end())
    if start < 0 or ";" in code[functions[0].end():start]:
        return None
    depth = 1
    for end in range(start + 1, len(code)):
        depth += (code[end] == "{") - (code[end] == "}")
        if depth == 0:
            return code[start + 1:end]
    return None


def check_shared_formula_codec(
    manifests: dict[str, dict[str, Any]],
    workspaces: dict[str, dict[str, Any]],
    sources: dict[str, str],
) -> list[str]:
    """Hold the concrete shared-codec retirement in the two production adapters.

    The IR leaf owns duplicate-key JSON and the typed wire grammar. Producers,
    expression algebras and bounded serde entry policies remain local. This
    lexical boundary does not prove the absence of arbitrary alternative decoders.
    """
    errors: list[str] = []
    retired = {
        "UniqueJsonValue", "UniqueJsonVisitor", "WireSort", "TrustFormulaV1Sort", "Binding",
        "decode_expr", "decode_sort", "decode_binding", "decode_result_binding",
        "decode_quantifier_expr", "decode_let_expr", "decode_bin_op", "decode_trust_formula_v1_sort",
        "validate_arithmetic_free_trust_formula_v1", "validate_arithmetic_free_expr",
        "validate_child_expr", "validate_binding", "required_name_and_sort",
        "reject_unknown_fields",
    }
    entrypoints = {
        "trust-types": ("canonical_arithmetic_free_trust_formula_v1_payload", "validate_value", "parse_unique_proof_json_payload"),
        "trust-wp-core": ("decode_trust_formula_v1_declared_claim_and_value", "decode_value", "parse_unique_json"),
    }
    for owner, (entry, delegate, parser) in entrypoints.items():
        manifest = manifests.get(owner, {})
        workspace = workspace_table(workspaces.get(owner, {}), "dependencies")
        dependencies = []
        for alias, declaration in manifest.get("dependencies", {}).items():
            inherited = workspace.get(alias, {})
            package = inherited.get("package", alias) if isinstance(inherited, dict) else alias
            if package == "trust-ir-contract" or alias == "trust-ir-contract":
                dependencies.append((alias, declaration, inherited, package))
        if len(dependencies) != 1:
            errors.append(f"{owner} codec requires one normal workspace trust-ir-contract dependency with proof-json")
            crate = "trust_ir_contract"
        else:
            alias, declaration, inherited, package = dependencies[0]
            features = set(declaration.get("features", [])) if isinstance(declaration, dict) else set()
            if isinstance(inherited, dict):
                features.update(inherited.get("features", []))
            if (not isinstance(declaration, dict) or declaration.get("workspace") is not True
                    or declaration.get("optional") is True or package != "trust-ir-contract"
                    or not isinstance(inherited, dict) or inherited.get("optional") is True
                    or set(declaration) - {"workspace", "features", "default-features", "optional"}
                    or "proof-json" not in features):
                errors.append(f"{owner} codec requires a nonoptional normal workspace trust-ir-contract dependency with proof-json")
            crate = alias.replace("-", "_")
        source = sources.get(owner, "")
        if not source:
            errors.append(f"{owner} production codec source is missing")
            continue
        lexed, code = _production_rust(source)
        imports = _rust_imports(code)
        restored = sorted(set(re.findall(r"\b(?:struct|enum|type|fn)\s+(?:r#)?(\w+)", code)) & retired)
        if restored:
            errors.append(f"{owner} codec restores retired local grammar: {', '.join(restored)}")
        # Strings/comments cannot manufacture a delegation or a declaration.
        # Inspect actual literal positions only for the former Value.get keys.
        if any(not lexed.in_test(start) and re.search(r"\.\s*get\s*\(\s*&?\s*$", code[:start])
               for start, _end, _value in lexed.strings):
            errors.append(f"{owner} codec restores raw JSON field reads; use the shared typed grammar")
        canonical = crate + "::"
        aliases = {name for name, path in imports.items() if path.startswith(canonical)} | {crate}
        if any(re.search(r"\b(?:mod|struct|enum|type|fn|const|static|let)\s+(?:r#)?" + re.escape(name) + r"\b", code)
               for name in aliases):
            errors.append(f"{owner} codec shadows a canonical owner import")
        body = _rust_function(code, entry)
        body_paths = _rust_paths(body or "", imports)
        expected = canonical + "trust_formula_v1::" + delegate
        calls = [end for path, _start, end in body_paths if path == expected
                 and re.match(r"\s*(?:::<[^;{}]*>)?\s*\(", (body or "")[end:])]
        if body is None or not calls:
            errors.append(f"{owner} {entry} must delegate to trust-ir-contract {delegate}")
        if owner == "trust-wp-core":
            wrapper = _rust_function(code, "decode_trust_formula_v1_declared_claim")
            if wrapper is None or not re.search(r"\bdecode_trust_formula_v1_declared_claim_and_value\s*\(", wrapper):
                errors.append("trust-wp-core declared claim wrapper must delegate to the shared decoded-value entrypoint")
        policy = "CanonicalArithmeticFree" if owner == "trust-types" else "NativeReplay"
        if not any(path == canonical + "trust_formula_v1::DecodePolicy::" + policy for path, _, _ in body_paths):
            errors.append(f"{owner} {entry} must select canonical DecodePolicy::{policy}")
        parse_body = _rust_function(code, parser)
        unique = canonical + "proof_json::UniqueJsonValue"
        reads_unique = any(
            (path == unique + "::deserialize" and re.match(r"\s*\(", (parse_body or "")[end:]))
            or (path == unique and re.search(r"\bfrom_str_deep\s*::\s*<\s*$", (parse_body or "")[:start])
                and re.match(r"\s*>\s*\(", (parse_body or "")[end:]))
            for path, start, end in _rust_paths(parse_body or "", imports)
        )
        if parse_body is None or not reads_unique:
            errors.append(f"{owner} {parser} must parse with canonical proof_json::UniqueJsonValue")
    return errors


def shared_formula_codec_self_check() -> list[str]:
    manifests, workspaces, sources = shared_formula_codec_inputs()
    baseline = check_shared_formula_codec(manifests, workspaces, sources)
    if baseline:
        return ["current shared formula codec should pass: " + error for error in baseline]
    failures: list[str] = []
    for owner in FORMULA_CODEC_PATHS:
        for text, expected in (
            ("\nstruct UniqueJsonVisitor;", "retired local grammar"),
            ('\nfn old_codec() { value.get("body"); }', "raw JSON field reads"),
        ):
            self_check_error_contains(
                check_shared_formula_codec(manifests, workspaces, {**sources, owner: sources[owner] + text}),
                expected, failures, f"{owner} shared codec reintroduction",
            )
        case = copy.deepcopy(manifests)
        case[owner]["dev-dependencies"] = case[owner].pop("dependencies", {})
        self_check_error_contains(
            check_shared_formula_codec(case, workspaces, sources),
            "normal workspace trust-ir-contract dependency", failures, f"{owner} shared codec test-only dependency",
        )
    return failures


def check_shared_integer_bounds(manifest: dict[str, Any], source: str) -> list[str]:
    """Hold the concrete VC/semantics bound consolidation, not arbitrary equivalence."""
    errors: list[str] = []
    dependency = manifest.get("dependencies", {}).get("trust-semantics")
    if (not isinstance(dependency, dict) or dependency.get("workspace") is not True
            or dependency.get("optional") is True):
        errors.append("trust-vcgen must use the workspace trust-semantics production dependency")
    names = {"signed_min", "signed_max", "type_min_formula", "type_max_formula"}
    imports: set[str] = set()
    for match in re.finditer(r"\buse\s+trust_semantics\s*::\s*\{([^}]+)\}", source):
        imports.update(part.strip() for part in match.group(1).split(",") if part.strip())
    if not names <= imports:
        errors.append("trust-vcgen range must import all canonical integer bounds from trust-semantics")
    restored = re.findall(
        r"^\s*(?:pub(?:\([^)]*\))?\s+)?(?:const\s+)?fn\s+"
        r"(signed_min|signed_max|type_min_formula|type_max_formula)\s*\(",
        source, re.MULTILINE,
    )
    if restored:
        errors.append("trust-vcgen range must not restore duplicate integer bounds: "
                      + ", ".join(sorted(set(restored))))
    return errors


def shared_integer_bounds_self_check() -> list[str]:
    manifest = load_manifest(REPO_ROOT / "crates/trust-vcgen/Cargo.toml")
    source = (REPO_ROOT / "crates/trust-vcgen/src/range.rs").read_text(encoding="utf-8")
    failures = check_shared_integer_bounds(manifest, source)
    if failures:
        return ["current shared integer bounds should pass: " + "; ".join(failures)]
    for name in ("signed_min", "signed_max", "type_min_formula", "type_max_formula"):
        self_check_error_contains(
            check_shared_integer_bounds(manifest, source + f"\nfn {name}() {{}}\n"),
            "must not restore duplicate integer bounds", failures, f"restored bound {name}",
        )
    case = copy.deepcopy(manifest)
    dependency = case["dependencies"].pop("trust-semantics")
    case.setdefault("dev-dependencies", {})["trust-semantics"] = dependency
    self_check_error_contains(
        check_shared_integer_bounds(case, source), "production dependency", failures,
        "shared bounds moved back to test-only dependency",
    )
    self_check_error_contains(
        check_shared_integer_bounds(manifest, source.replace("use trust_semantics::", "use old_copy::")),
        "must import all canonical integer bounds", failures, "shared bounds import removed",
    )
    return failures

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

    for table in ("dependencies", "build-dependencies"):
        for dependency in ("ay", "trust-router"):
            case = copy.deepcopy(fanout_manifests)
            case["trust-coordinator"].setdefault(table, {})[dependency] = {"workspace": True}
            self_check_error_contains(
                check_dependency_fanout_policy(case),
                "trust-coordinator must keep its fixed solver-free dependency boundary",
                failures,
                f"coordinator {table} {dependency} fanout regression",
            )
    for table in ("dependencies", "build-dependencies", "target", "features"):
        case = copy.deepcopy(fanout_manifests)
        case["trust-file-lock"].setdefault(table, {})["ay"] = {"workspace": True}
        self_check_error_contains(
            check_dependency_fanout_policy(case),
            "trust-file-lock must keep its fixed solver-free ownership boundary",
            failures,
            f"file ownership {table} fanout regression",
        )
    for value in ({"path": "../shadow-lock"}, {"workspace": True, "package": "ay"}):
        case = copy.deepcopy(fanout_manifests)
        case["trust-file-lock"]["dependencies"]["libc"] = value
        self_check_error_contains(
            check_dependency_fanout_policy(case),
            "trust-file-lock must keep its fixed solver-free ownership boundary",
            failures,
            "file ownership workspace identity regression",
        )
    for table in ("dependencies", "build-dependencies", "target", "features"):
        case = copy.deepcopy(fanout_manifests)
        case["trust-rand"][table] = {"solver": {"workspace": True}}
        self_check_error_contains(
            check_dependency_fanout_policy(case),
            "trust-rand must remain an unconditional dependency-free entropy leaf",
            failures,
            f"entropy leaf {table} fanout regression",
        )
    case = copy.deepcopy(fanout_manifests)
    case["trust-coordinator"]["dependencies"]["trust-rand"] = {"path": "../shadow-rand"}
    self_check_error_contains(
        check_dependency_fanout_policy(case),
        "trust-coordinator must keep its fixed solver-free dependency boundary",
        failures,
        "coordinator entropy workspace identity regression",
    )
    case = copy.deepcopy(fanout_manifests)
    case["trust-coordinator"].setdefault("target", {})["cfg(unix)"] = {
        "dependencies": {"ay": {"workspace": True}}
    }
    self_check_error_contains(
        check_dependency_fanout_policy(case),
        "trust-coordinator platform dependencies must remain in trust-file-lock",
        failures,
        "coordinator platform fanout regression",
    )

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
        "targo tree --manifest-path Cargo.toml -p trust-bmc",
        "targo tree --manifest-path Cargo.toml -p trust-router",
        "rg '^(ay-bindings|trust-mc-core|trust-mc-driver)'",
        "targo --unverified check --manifest-path Cargo.toml -p trust-bmc",
        "targo --unverified check --manifest-path Cargo.toml -p trust-router",
        "targo --unverified check --manifest-path Cargo.toml -p trust-bmc --features trust-mc-native-solver",
        "targo --unverified test --manifest-path Cargo.toml -p trust-bmc manifest --lib",
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
    case["trust-router"].setdefault("dev-dependencies", {})["trust-wp-core"] = {
        "path": "../../first-party/trust-wp/crates/trust-wp-core"
    }
    if check_dependency_fanout_policy(case):
        failures.append("trust-router test-only core fixture must preserve fanout policy")

    for section, target in (
        ("dependencies", None), ("build-dependencies", None),
        ("dependencies", "cfg(unix)"), ("build-dependencies", "cfg(unix)"),
    ):
        for alias in ("trust-wp-core", "retired-wp"):
            case = copy.deepcopy(fanout_manifests)
            scope = case["trust-router"]
            if target is not None:
                scope = scope.setdefault("target", {}).setdefault(target, {})
            declaration = {"version": "1", "optional": True}
            if alias != "trust-wp-core":
                declaration["package"] = "trust-wp-core"
            scope.setdefault(section, {})[alias] = declaration
            self_check_error_contains(
                check_dependency_fanout_policy(case),
                "trust-router must not restore the retired TrustWP backend dependency",
                failures,
                f"trust-router retired core {section} target={target} alias={alias}",
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

    for dependency in (
        {"workspace": True},
        {"path": "../trust-types", "default-features": True},
        {"path": "../trust-types", "default-features": False, "features": ["try-sugar"]},
        {"path": "../trust-types", "default-features": False, "features": ["default"]},
    ):
        case = copy.deepcopy(fanout_manifests)
        case["trust-semantics"]["dependencies"]["trust-types"] = dependency
        self_check_error_contains(
            check_dependency_fanout_policy(case),
            "trust-semantics must keep trust-types default and try-sugar features disabled",
            failures, f"semantic range feature fanout {dependency}",
        )

    failures.extend(wp_retirement_self_check())
    failures.extend(shared_formula_codec_self_check())
    failures.extend(native_sp_splitter_self_check())
    failures.extend(shared_integer_bounds_self_check())

    return failures


def wp_retirement_self_check() -> list[str]:
    failures: list[str] = []
    facade = load_manifest(FANOUT_POLICY_MANIFESTS["trust-wp"])
    workspace = load_manifest(MANIFESTS["root"])
    sources = wp_facade_sources()
    baseline = check_wp_native_facade_retirement(facade, workspace, sources)
    if baseline:
        failures.append("current WP facade retirement should pass: " + "; ".join(baseline))
    for section in ("dependencies", "build-dependencies", "dev-dependencies"):
        for package in ("trust-wp-ay", "trust-wp-lib"):
            for target in (False, True):
                case = copy.deepcopy(facade)
                owner = (
                    case.setdefault("target", {}).setdefault("cfg(unix)", {}) if target else case
                )
                owner.setdefault(section, {})["renamed-native-solver"] = {
                    "package": package, "version": "0"
                }
                self_check_error_contains(
                    check_wp_native_facade_retirement(case, workspace, sources),
                    "must not restore retired native solver dependency",
                    failures, f"WP retired solver {package} {section} target={target}",
                )
    case = copy.deepcopy(facade)
    case.setdefault("dependencies", {})["renamed-native-solver"] = {"workspace": True}
    inherited = copy.deepcopy(workspace)
    inherited.setdefault("workspace", {}).setdefault("dependencies", {})[
        "renamed-native-solver"
    ] = {"package": "trust-wp-ay", "version": "0"}
    self_check_error_contains(
        check_wp_native_facade_retirement(case, inherited, sources),
        "must not restore retired native solver dependency", failures, "WP workspace solver alias",
    )
    self_check_error_contains(
        check_wp_native_facade_retirement(facade, workspace, {}),
        "library source is missing", failures, "WP missing facade source",
    )
    for path, text, expected in (
        ("native.rs", "", "must not restore retired src/native.rs"),
        ("renamed.rs", "pub struct NativePureBody {}", "restores a retired native request/body API"),
        ("lib.rs", "pub use other::NativeTrustWpRequest;", "restores a retired native request/body API"),
        ("renamed.rs", "pub fn verify_native() {}", "restores a retired native request/body API"),
    ):
        self_check_error_contains(
            check_wp_native_facade_retirement(facade, workspace, {**sources, path: text}),
            expected, failures, f"WP retired native API {path} {text}",
        )

    return failures


def cargo_tree_edges(package: str, edges: str = "normal") -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [
            # Trust toolchain, never stock cargo (CLAUDE.md "Build"); `tree`
            # takes no lane, so it is bare `targo tree`.
            "targo",
            "tree",
            "--manifest-path",
            "Cargo.toml",
            "-p",
            package,
            "--edges",
            edges,
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
        result = cargo_tree_edges(
            package, "normal,build" if package == "trust-coordinator" else "normal"
        )
        if result.returncode != 0:
            failures.append(
                f"{package}: targo tree failed with exit {result.returncode}: "
                + result.stderr.strip()
            )
            continue
        matched = [
            line
            for line in result.stdout.splitlines()
            if any(line.startswith(f"{forbidden} ") for forbidden in FANOUT_TREE_FORBIDDEN_DEFAULT_PACKAGES)
        ]
        if package == "trust-coordinator":
            matched.extend(
                line for line in result.stdout.splitlines()
                if line.strip() and line.split(maxsplit=1)[0].startswith(
                    ("ay", "clean", "trust-router", "trust-cg", "trust-mc", "trust-vc")
                )
            )
        if matched:
            failures.append(
                f"{package}: default dependency tree still contains forbidden fanout:\n"
                + "\n".join(f"  {line}" for line in matched)
            )
    return failures


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--self-check",
        action="store_true",
        help="run focused regression checks for manifest alignment and fanout policy logic",
    )
    parser.add_argument(
        "--fanout-tree-proof",
        action="store_true",
        help=(
            "prove default trust-bmc/trust-router normal and coordinator normal/build trees exclude "
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
    fanout_manifests = {
        name: load_manifest(path)
        for name, path in FANOUT_POLICY_MANIFESTS.items()
    }
    fanout_errors = check_dependency_fanout_policy(fanout_manifests)
    wp_retirement_errors = check_wp_native_facade_retirement(
        fanout_manifests["trust-wp"], local_patch_manifests["root"], wp_facade_sources()
    )
    formula_codec_errors = check_shared_formula_codec(*shared_formula_codec_inputs())
    native_sp_errors = check_native_sp_splitter_retirement(native_sp_source())
    integer_bound_errors = check_shared_integer_bounds(
        load_manifest(REPO_ROOT / "crates/trust-vcgen/Cargo.toml"),
        (REPO_ROOT / "crates/trust-vcgen/src/range.rs").read_text(encoding="utf-8"),
    )
    errors = [
        *formula_codec_errors,
        *native_sp_errors,
        *integer_bound_errors,
        *local_patch_errors,
        *fabric_boundary_errors,
        *fabric_lock_errors,
        *fanout_errors,
        *wp_retirement_errors,
    ]

    if errors:
        print("Cargo manifest policy check failed:")
        if not fabric_boundary_errors and not fabric_lock_errors:
            print("temporal fabric external boundary and lock revisions are coherent.")
        if not fanout_errors:
            print("dependency fanout manifest policy is preserved.")
        for error in errors:
            print(error)
        return 1

    print(
        "Cargo manifest alignment, local patch integrity, temporal fabric boundary, "
        "dependency fanout policy, and shared formula codec retirement check passed."
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except FallbackParseRefused as refusal:
        print(f"REFUSED: {refusal}", file=sys.stderr)
        raise SystemExit(FALLBACK_REFUSED_EXIT)
