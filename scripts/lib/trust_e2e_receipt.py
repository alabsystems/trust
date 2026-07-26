#!/usr/bin/env python3
"""Fail-closed helpers for local Trust end-to-end diagnostic records.

The shell acceptance gates build their candidate documents in private temporary
directories and call this module only after every check has passed.  Publishing
is atomic in the destination directory, so a failed run never exposes a partial
record.  No-replace publication ensures that an output argument cannot overwrite
an existing file; these local diagnostics are not release authority.
"""

from __future__ import annotations

import argparse
import errno
import hashlib
import json
import os
from pathlib import Path
import secrets
import stat
import sys
from typing import Any, Iterable, Mapping
from urllib.parse import urlsplit

try:
    import tomllib
except ImportError:  # Python 3.10 and older can still publish JSON receipts.
    tomllib = None  # type: ignore[assignment]


KNOWN_RECEIPT_SCHEMAS = frozenset(
    {
        "trust.e2e.installed-toolchain-receipt.v1",
        "trust.e2e.dist-artifact-receipt.v1",
    }
)

REQUIRED_DEFAULT_PROFILE = frozenset(
    {
        "trustc",
        "targo",
        "trust-std",
        "trust-mingw",
        "trust-docs",
        "targo-trust",
        "trustfmt-preview",
        "tippy-preview",
        "trust-analyzer-preview",
        "trust-src",
        "trust-llvm-tools-preview",
    }
)

REQUIRED_ARCHIVE_COMPONENTS = frozenset(
    {
        "trust",
        "trustc",
        "trustc-dev",
        "trust-std",
        "targo",
        "targo-trust",
        "trust-docs",
        "trustfmt",
        "tippy",
        "trust-analyzer",
        "trust-src",
        "trust-llvm-tools",
    }
)

_PREVIEW_COMPONENTS = frozenset(
    {"trustfmt", "tippy", "trust-analyzer", "trust-llvm-tools"}
)

_INSTALLED_CHECKS = frozenset(
    {
        "canonical_tool_inventory",
        "compatibility_alias_inventory",
        "relocation",
        "immutable_sysroot",
        "isolated_rustup_link",
        "implicit_targo_rejected",
        "explicit_unverified_build_test_run_doc",
        "formatter_and_linter",
        "doctor_and_native_verifier_suites",
        "analyzer_and_proc_macro_helper",
        "serde_locked_runtime_round_trip",
        "verified_proc_macro_boundary",
    }
)

_DIST_CHECKS = frozenset(
    {
        "archive_paths_and_entry_types",
        "archive_hashes_before_and_after_install",
        "source_archive_hygiene",
        "targo_trust_binary_and_docs_layout",
        "umbrella_trust_archive",
        "channel_default_profile",
        "channel_archive_urls_and_hashes",
        "channel_targo_trust_extension",
        "installed_compiler_identity",
        "immutable_installed_toolchain_child_gate",
    }
)


class ReceiptError(ValueError):
    """A candidate receipt or one of its authority inputs is invalid."""


def _object_field(value: Mapping[str, Any], field: str, context: str) -> dict[str, Any]:
    child = value.get(field)
    if not isinstance(child, dict):
        raise ReceiptError(f"{context}.{field} must be an object")
    return child


def _string_field(value: Mapping[str, Any], field: str, context: str) -> str:
    child = value.get(field)
    if not isinstance(child, str) or not child:
        raise ReceiptError(f"{context}.{field} must be a non-empty string")
    return child


def _require_sha256(value: Any, context: str) -> str:
    if (
        not isinstance(value, str)
        or len(value) != 64
        or any(character not in "0123456789abcdef" for character in value)
    ):
        raise ReceiptError(f"{context} must be a lowercase SHA-256")
    return value


def canonical_embedded_json_sha256(value: Any) -> str:
    """Digest one embedded JSON value using a stable, order-independent encoding."""

    try:
        encoded = json.dumps(
            value,
            allow_nan=False,
            ensure_ascii=False,
            separators=(",", ":"),
            sort_keys=True,
        )
    except (TypeError, ValueError) as error:
        raise ReceiptError(f"embedded value is not strict JSON: {error}") from error
    return hashlib.sha256((encoded + "\n").encode("utf-8")).hexdigest()


def _validate_source_binding(document: Mapping[str, Any]) -> None:
    source = _object_field(document, "source", "receipt")
    head = _string_field(source, "repository_head", "receipt.source")
    if len(head) not in {40, 64} or any(
        character not in "0123456789abcdef" for character in head
    ):
        raise ReceiptError("receipt.source.repository_head is not a full Git object id")
    for field in ("repository_clean_before_and_after", "inputs_stable_before_and_after"):
        if source.get(field) is not True:
            raise ReceiptError(f"receipt.source.{field} must be true")
    _require_sha256(source.get("gate_script_sha256"), "receipt.source.gate_script_sha256")
    _require_sha256(source.get("receipt_helper_sha256"), "receipt.source.receipt_helper_sha256")


def _validate_stage_binding(document: Mapping[str, Any]) -> None:
    stage = _object_field(document, "stage_provenance", "receipt")
    if stage.get("schema") != "trust.stage-tool-provenance.v2":
        raise ReceiptError("receipt Stage2 provenance schema is invalid")
    if stage.get("status") not in {"internal-release-ready", "release-ready"}:
        raise ReceiptError("receipt Stage2 provenance is not release-ready")
    if stage.get("stage") != 2:
        raise ReceiptError("receipt Stage2 provenance records another stage")
    if stage.get("verified_before_and_after") is not True:
        raise ReceiptError("receipt Stage2 provenance was not verified before and after")
    _require_sha256(stage.get("sha256"), "receipt.stage_provenance.sha256")
    source = _object_field(document, "source", "receipt")
    if stage.get("source_commit") != source.get("repository_head"):
        raise ReceiptError("receipt Stage2 provenance source commit differs from repository HEAD")


def _validate_checks(document: Mapping[str, Any], required: frozenset[str]) -> None:
    checks = _object_field(document, "checks", "receipt")
    if set(checks) != required:
        missing = sorted(required - set(checks))
        extra = sorted(set(checks) - required)
        raise ReceiptError(f"receipt checks differ from schema (missing={missing}, extra={extra})")
    failed = sorted(name for name, result in checks.items() if result != "passed")
    if failed:
        raise ReceiptError("receipt contains non-passing checks: " + ", ".join(failed))


def _validate_installed_receipt(document: Mapping[str, Any]) -> None:
    _validate_source_binding(document)
    _validate_stage_binding(document)
    sysroots = _object_field(document, "sysroots", "receipt")
    source = _object_field(sysroots, "source", "receipt.sysroots")
    installed = _object_field(sysroots, "installed", "receipt.sysroots")
    if source.get("manifest_schema") != "trust.filesystem-content-manifest.ndjson.v1":
        raise ReceiptError("receipt source sysroot manifest schema is invalid")
    if (
        source.get("manifest_scope")
        != "entry-kind-mode-symlink-target-file-bytes;excludes-owner-xattrs-flags-hardlink-topology"
    ):
        raise ReceiptError("receipt source sysroot manifest scope is invalid")
    if installed.get("manifest_schema") != "trust.filesystem-content-manifest.ndjson.v1":
        raise ReceiptError("receipt installed sysroot manifest schema is invalid")
    if (
        installed.get("manifest_scope")
        != "entry-kind-mode-symlink-target-file-bytes;excludes-owner-xattrs-flags-hardlink-topology"
    ):
        raise ReceiptError("receipt installed sysroot manifest scope is invalid")
    if (
        source.get("copy_content_manifest_schema")
        != "trust.filesystem-content-manifest.ndjson.v1"
    ):
        raise ReceiptError("receipt sysroot copy-content manifest schema is invalid")
    if (
        source.get("copy_content_manifest_scope")
        != "entry-kind-symlink-target-file-bytes;excludes-mode-owner-xattrs-flags-hardlink-topology"
    ):
        raise ReceiptError("receipt sysroot copy-content manifest scope is invalid")
    if (
        source.get("materialized_link_inputs_manifest_schema")
        != "trust.materialized-source-input-manifest.ndjson.v1"
    ):
        raise ReceiptError("receipt materialized source-input manifest schema is invalid")
    if (
        source.get("materialized_link_inputs_manifest_scope")
        != "entry-kind-symlink-target-file-bytes;excludes-mode-owner-xattrs-flags-hardlink-topology"
    ):
        raise ReceiptError("receipt materialized source-input manifest scope is invalid")
    source_manifest_sha256 = _require_sha256(
        source.get("manifest_sha256"), "receipt.sysroots.source.manifest_sha256"
    )
    copy_source_sha256 = _require_sha256(
        source.get("copy_content_manifest_sha256"),
        "receipt.sysroots.source.copy_content_manifest_sha256",
    )
    copied_content_sha256 = _require_sha256(
        source.get("copied_sysroot_content_manifest_sha256"),
        "receipt.sysroots.source.copied_sysroot_content_manifest_sha256",
    )
    if copied_content_sha256 != copy_source_sha256:
        raise ReceiptError(
            "receipt copied sysroot content manifest differs from its source content manifest"
        )
    _require_sha256(
        source.get("materialized_link_inputs_manifest_sha256"),
        "receipt.sysroots.source.materialized_link_inputs_manifest_sha256",
    )
    _require_sha256(
        installed.get("manifest_sha256"), "receipt.sysroots.installed.manifest_sha256"
    )
    if source.get("stable_before_and_after") is not True:
        raise ReceiptError("receipt source sysroot was not stable")
    if source.get("copied_sysroot_matches_source_content_manifest") is not True:
        raise ReceiptError("receipt copied sysroot did not match its source content manifest")
    if source.get("materialized_link_inputs_stable_before_and_after") is not True:
        raise ReceiptError("receipt materialized source-link inputs were not stable")
    if source.get("materialized_link_input_content_copied_exactly") is not True:
        raise ReceiptError("receipt materialized source-link content was not copied exactly")
    if source.get("materialized_link_input_files_git_tracked_only") is not True:
        raise ReceiptError("receipt materialized source-link files were not Git-tracked only")
    for field in (
        "read_only",
        "no_escaping_symlinks",
        "no_source_hardlinks",
        "unchanged_after_behavior_checks",
    ):
        if installed.get(field) is not True:
            raise ReceiptError(f"receipt installed sysroot {field} must be true")

    compiler = _object_field(document, "compiler", "receipt")
    compiler_sha = _require_sha256(compiler.get("sha256"), "receipt.compiler.sha256")
    source_compiler_sha = _require_sha256(
        compiler.get("source_sha256"), "receipt.compiler.source_sha256"
    )
    if source_compiler_sha != compiler_sha:
        raise ReceiptError("receipt installed/source compiler digests differ")
    if compiler.get("provenance_digest_match") is not True:
        raise ReceiptError("receipt compiler is not bound to Stage2 provenance")

    doctor = _object_field(document, "doctor", "receipt")
    doctor_sha256 = _require_sha256(
        doctor.get("report_sha256"), "receipt.doctor.report_sha256"
    )
    if doctor.get("ready") is not True or doctor.get("daily_driver_ready") is not True:
        raise ReceiptError("receipt doctor/daily-driver status is not ready")
    if set(doctor.get("required_verifier_suites") or []) != {"trust-mc", "trust-wp", "trust-vc"}:
        raise ReceiptError("receipt doctor verifier-suite set is incomplete")
    doctor_report = doctor.get("report")
    if not isinstance(doctor_report, dict):
        raise ReceiptError("receipt doctor report is not embedded")
    if doctor_sha256 != canonical_embedded_json_sha256(doctor_report):
        raise ReceiptError("receipt embedded doctor report digest does not match")

    serde = _object_field(document, "serde_fixture", "receipt")
    for field in ("tree_manifest_sha256", "cargo_lock_sha256", "runtime_output_sha256"):
        _require_sha256(serde.get(field), f"receipt.serde_fixture.{field}")
    runtime_output = serde.get("runtime_output")
    if not isinstance(runtime_output, dict):
        raise ReceiptError("receipt serde runtime output is not embedded")
    if serde.get("runtime_output_sha256") != canonical_embedded_json_sha256(runtime_output):
        raise ReceiptError("receipt embedded serde runtime output digest does not match")
    if serde.get("native_proc_macro_lane") != "explicitly-unverified":
        raise ReceiptError("receipt misstates the native proc-macro lane")
    if serde.get("verified_proc_macro_boundary") != "rejected-fail-closed":
        raise ReceiptError("receipt did not bind fail-closed verified proc-macro rejection")

    scope = _object_field(document, "claim_scope", "receipt")
    expected_scope_fields = {
        "kind",
        "public_rustup_channel",
        "notarized_macos_application",
        "ecosystem_superiority",
    }
    if set(scope) != expected_scope_fields:
        raise ReceiptError("receipt installed claim_scope schema is not exact")
    if scope.get("kind") != "local-installed-toolchain-rehearsal":
        raise ReceiptError("receipt installed claim_scope kind is invalid")
    for field in ("public_rustup_channel", "notarized_macos_application", "ecosystem_superiority"):
        if scope.get(field) is not False:
            raise ReceiptError(f"receipt claim_scope.{field} must be false")
    _validate_checks(document, _INSTALLED_CHECKS)


def _validate_dist_receipt(document: Mapping[str, Any]) -> None:
    _validate_source_binding(document)
    _validate_stage_binding(document)
    compiler = _object_field(document, "compiler", "receipt")
    _require_sha256(compiler.get("trustc_sha256"), "receipt.compiler.trustc_sha256")
    if compiler.get("identity_matches_installed_archives") is not True:
        raise ReceiptError("receipt compiler identity does not match installed archives")

    distribution = _object_field(document, "distribution", "receipt")
    if distribution.get("archive_manifest_schema") != "trust.dist-archive-manifest.ndjson.v1":
        raise ReceiptError("receipt distribution archive-manifest schema is invalid")
    dist_directory = _string_field(distribution, "directory", "receipt.distribution")
    if not os.path.isabs(dist_directory) or os.path.normpath(dist_directory) != dist_directory:
        raise ReceiptError("receipt distribution directory is not a normalized absolute path")
    host = _string_field(distribution, "host", "receipt.distribution")
    version = _string_field(distribution, "version", "receipt.distribution")
    for value, field in ((host, "host"), (version, "version")):
        if len(value) > 128 or any(
            character not in "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789._+-"
            for character in value
        ):
            raise ReceiptError(f"receipt distribution {field} is not a canonical token")
    _require_sha256(
        distribution.get("archive_manifest_sha256"),
        "receipt.distribution.archive_manifest_sha256",
    )
    archives = distribution.get("archives")
    if not isinstance(archives, list) or not all(isinstance(row, dict) for row in archives):
        raise ReceiptError("receipt distribution archives are not embedded")
    expected_row_fields = {
        "archive_filename",
        "archive_path",
        "archive_root",
        "component",
        "extension",
        "selected",
        "sha256",
        "size_bytes",
    }
    components = {row.get("component") for row in archives if isinstance(row.get("component"), str)}
    if components != REQUIRED_ARCHIVE_COMPONENTS:
        raise ReceiptError("receipt distribution archive component set is not exact")
    selected_by_component: dict[str, int] = {}
    seen: set[tuple[str, str]] = set()
    for index, row in enumerate(archives, 1):
        if set(row) != expected_row_fields:
            raise ReceiptError(f"receipt distribution archive row {index} has an open schema")
        _require_sha256(row.get("sha256"), "receipt distribution archive sha256")
        component = row.get("component")
        if component not in REQUIRED_ARCHIVE_COMPONENTS:
            raise ReceiptError(f"receipt distribution archive row {index} has unknown component")
        extension = row.get("extension")
        if extension not in {"tar.gz", "tar.xz"}:
            raise ReceiptError(f"receipt distribution archive row {index} has invalid extension")
        key = (component, extension)
        if key in seen:
            raise ReceiptError(f"receipt distribution repeats {component}.{extension}")
        seen.add(key)
        selected = row.get("selected")
        if not isinstance(selected, bool):
            raise ReceiptError(f"receipt distribution archive row {index} has invalid selection")
        if selected:
            selected_by_component[component] = selected_by_component.get(component, 0) + 1
        size = row.get("size_bytes")
        if not isinstance(size, int) or isinstance(size, bool) or size < 1:
            raise ReceiptError(f"receipt distribution archive row {index} has invalid size")
        expected_root = (
            f"{component}-{version}" if component == "trust-src" else f"{component}-{version}-{host}"
        )
        if row.get("archive_root") != expected_root:
            raise ReceiptError(
                f"receipt distribution archive row {index} root does not match host/version"
            )
        expected_filename = f"{expected_root}.{extension}"
        if row.get("archive_filename") != expected_filename:
            raise ReceiptError(
                f"receipt distribution archive row {index} filename does not match host/version"
            )
        archive_path = row.get("archive_path")
        expected_path = os.path.join(dist_directory, expected_filename)
        if archive_path != expected_path:
            raise ReceiptError(
                f"receipt distribution archive row {index} path is not its direct dist child"
            )
    bad_selected = sorted(
        component
        for component in REQUIRED_ARCHIVE_COMPONENTS
        if selected_by_component.get(component) != 1
    )
    if bad_selected:
        raise ReceiptError(
            "receipt must select exactly one archive for: " + ", ".join(bad_selected)
        )
    archive_manifest_payload = "".join(
        json.dumps(row, sort_keys=True, separators=(",", ":")) + "\n" for row in archives
    ).encode("utf-8")
    embedded_manifest_sha = hashlib.sha256(archive_manifest_payload).hexdigest()
    if distribution.get("archive_manifest_sha256") != embedded_manifest_sha:
        raise ReceiptError("receipt embedded archives do not match archive-manifest digest")
    if distribution.get("archives_rehashed_after_install") is not True:
        raise ReceiptError("receipt archives were not rehashed after installation")
    if distribution.get("umbrella_trust_archive_required") is not True:
        raise ReceiptError("receipt did not require the umbrella trust archive")

    channel = _object_field(document, "channel_manifest", "receipt")
    _require_sha256(channel.get("sha256"), "receipt.channel_manifest.sha256")
    _string_field(channel, "path", "receipt.channel_manifest")
    if channel.get("manifest_version") != "2":
        raise ReceiptError("receipt channel manifest version is invalid")
    if channel.get("host") != host:
        raise ReceiptError("receipt channel host differs from distribution host")
    if channel.get("archive_rows_validated") != len(archives):
        raise ReceiptError("receipt channel archive-row count differs from embedded inventory")
    if channel.get("targo_trust_available") is not True:
        raise ReceiptError("receipt channel does not make targo-trust available")
    if channel.get("umbrella_targo_trust_extension") is not True:
        raise ReceiptError("receipt channel umbrella omits targo-trust")
    if channel.get("hosting_claim") != "none-local-rehearsal-only":
        raise ReceiptError("receipt channel overstates its hosting claim")
    channel_components = channel.get("required_archive_components")
    if (
        not isinstance(channel_components, list)
        or not all(isinstance(item, str) for item in channel_components)
        or len(channel_components) != len(set(channel_components))
        or set(channel_components) != REQUIRED_ARCHIVE_COMPONENTS
    ):
        raise ReceiptError("receipt channel required archive set is incomplete")
    default_profile = channel.get("default_profile")
    if (
        not isinstance(default_profile, list)
        or not all(isinstance(item, str) for item in default_profile)
        or len(default_profile) != len(set(default_profile))
        or set(default_profile) != REQUIRED_DEFAULT_PROFILE
    ):
        raise ReceiptError("receipt channel default profile is not exact")

    child = _object_field(document, "installed_toolchain_gate", "receipt")
    child_document = _object_field(child, "receipt", "receipt.installed_toolchain_gate")
    parent_source = _object_field(document, "source", "receipt")
    child_source = _object_field(
        child_document, "source", "receipt.installed_toolchain_gate.receipt"
    )
    if child_source.get("repository_head") != parent_source.get("repository_head"):
        raise ReceiptError("embedded installed-toolchain source HEAD differs from parent receipt")

    parent_stage = _object_field(document, "stage_provenance", "receipt")
    child_stage = _object_field(
        child_document,
        "stage_provenance",
        "receipt.installed_toolchain_gate.receipt",
    )
    stage_bindings = (
        ("sha256", "digest"),
        ("source_commit", "source commit"),
        ("status", "status"),
        ("stage", "stage"),
    )
    for field, label in stage_bindings:
        if child_stage.get(field) != parent_stage.get(field):
            raise ReceiptError(
                f"embedded installed-toolchain Stage2 provenance {label} "
                "differs from parent receipt"
            )

    child_compiler = _object_field(
        child_document, "compiler", "receipt.installed_toolchain_gate.receipt"
    )
    if child_compiler.get("sha256") != compiler.get("trustc_sha256"):
        raise ReceiptError(
            "embedded installed-toolchain compiler digest differs from parent receipt"
        )

    child_payload = _serialized_receipt(child_document)
    child_sha = hashlib.sha256(child_payload).hexdigest()
    if _require_sha256(
        child.get("receipt_sha256"), "receipt.installed_toolchain_gate.receipt_sha256"
    ) != child_sha:
        raise ReceiptError("embedded installed-toolchain receipt digest does not match")
    if child.get("exact_document_embedded") is not True:
        raise ReceiptError("installed-toolchain child receipt is not embedded exactly")

    scope = _object_field(document, "claim_scope", "receipt")
    scope_false_fields = (
        "public_download_channel",
        "hosted_urls_exercised",
        "signatures_or_notarization",
        "multi_host_availability",
    )
    if set(scope) != {"kind", *scope_false_fields}:
        raise ReceiptError("receipt dist claim_scope schema is not exact")
    if scope.get("kind") != "local-pre-publication-dist-rehearsal":
        raise ReceiptError("receipt dist claim_scope kind is invalid")
    for field in scope_false_fields:
        if scope.get(field) is not False:
            raise ReceiptError(f"receipt claim_scope.{field} must be false")
    _validate_checks(document, _DIST_CHECKS)


def _validate_receipt(document: Mapping[str, Any]) -> None:
    if document.get("status") != "passed":
        raise ReceiptError("only a status=passed receipt may be published")
    schema = document.get("schema")
    if schema == "trust.e2e.installed-toolchain-receipt.v1":
        _validate_installed_receipt(document)
    elif schema == "trust.e2e.dist-artifact-receipt.v1":
        _validate_dist_receipt(document)
    else:
        raise ReceiptError(f"unrecognized receipt schema: {schema!r}")


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def validate_stage_provenance(
    provenance_path: Path,
    *,
    repository_head: str,
    trustc_path: Path,
) -> dict[str, Any]:
    """Validate the Stage2 diagnostic binding consumed by a local E2E rehearsal."""

    provenance_path = provenance_path.resolve(strict=True)
    trustc_path = trustc_path.resolve(strict=True)
    report = _load_json_object(provenance_path)
    if report.get("schema") != "trust.stage-tool-provenance.v2":
        raise ReceiptError("Stage2 provenance does not use trust.stage-tool-provenance.v2")
    if report.get("status") not in {"internal-release-ready", "release-ready"}:
        raise ReceiptError(f"Stage2 provenance is not release-ready: {report.get('status')!r}")
    if report.get("stage") != 2 or report.get("errors") != []:
        raise ReceiptError("Stage2 provenance records a rejected or non-Stage2 build")
    if report.get("tool_binding_status") != "ready":
        raise ReceiptError("Stage2 provenance tool binding is not ready")
    if report.get("source_tree_clean") is not True or report.get("trust_from_trust") is not True:
        raise ReceiptError("Stage2 provenance does not bind a clean Trust-from-Trust build")
    if (report.get("source_lineage") or {}).get("status") != "immutable_release":
        raise ReceiptError("Stage2 provenance source lineage is not immutable-release authority")
    bootstrap_lineage = report.get("bootstrap_lineage") or {}
    if bootstrap_lineage.get("status") != "trust_from_trust":
        raise ReceiptError("Stage2 provenance bootstrap lineage is not Trust-from-Trust")
    validated_seed = bootstrap_lineage.get("validated_seed") or {}
    if validated_seed.get("status") != "validated":
        raise ReceiptError("Stage2 provenance does not bind a validated seed")
    if validated_seed.get("materialization_status") != "fresh-from-validated-archives":
        raise ReceiptError("Stage2 provenance seed was not freshly materialized")
    if validated_seed.get("admission_status") not in {"internal-admitted", "public-promoted"}:
        raise ReceiptError("Stage2 provenance seed lacks release admission")
    if (report.get("build_authority") or {}).get("status") != "ready":
        raise ReceiptError("Stage2 provenance build authority is not ready")
    compiler = report.get("compiler") or {}
    if compiler.get("source_commit") != repository_head:
        raise ReceiptError("Stage2 provenance source commit does not match repository HEAD")
    compiler_sha256 = sha256_file(trustc_path)
    if compiler.get("compiler_sha256") != compiler_sha256:
        raise ReceiptError("Stage2 provenance compiler digest does not match selected trustc")
    if compiler.get("sysroot_matches") is not True:
        raise ReceiptError("Stage2 provenance compiler does not bind its recorded sysroot")
    return {
        "path": str(provenance_path),
        "sha256": sha256_file(provenance_path),
        "schema": report.get("schema"),
        "status": report.get("status"),
        "stage": 2,
        "host": report.get("host"),
        "source_commit": compiler.get("source_commit"),
        "compiler_sha256": compiler_sha256,
    }


def _serialized_receipt(document: Mapping[str, Any]) -> bytes:
    if not isinstance(document, dict):
        raise ReceiptError("receipt must be a JSON object")
    _validate_receipt(document)
    try:
        encoded = json.dumps(
            document,
            allow_nan=False,
            ensure_ascii=False,
            indent=2,
            sort_keys=True,
        )
    except (TypeError, ValueError) as error:
        raise ReceiptError(f"receipt is not strict JSON: {error}") from error
    return (encoded + "\n").encode("utf-8")


def _secure_directory_flags() -> int:
    required = ("O_DIRECTORY", "O_NOFOLLOW")
    missing = [name for name in required if not hasattr(os, name)]
    dir_fd_functions = (os.open, os.mkdir, os.stat, os.unlink, os.rename)
    unsupported = [
        function.__name__
        for function in dir_fd_functions
        if function not in os.supports_dir_fd
    ]
    if missing or unsupported:
        detail = ", ".join(missing + unsupported)
        raise ReceiptError(f"secure receipt publication is unavailable: missing {detail}")
    return os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW


def _open_secure_parent(path: Path) -> tuple[Path, int]:
    """Open/create the lexical parent without ever following a symlink."""

    absolute = Path(os.path.abspath(os.fspath(path)))
    if not absolute.name:
        raise ReceiptError("receipt destination must name a file")
    flags = _secure_directory_flags()
    if not absolute.anchor:
        raise ReceiptError(f"receipt destination has no absolute anchor: {absolute}")
    directory_fd = os.open(absolute.anchor, flags)
    try:
        for component in absolute.parent.parts[1:]:
            try:
                next_fd = os.open(component, flags, dir_fd=directory_fd)
            except FileNotFoundError:
                try:
                    # Generated evidence directories are private by default.
                    # Persist each newly created directory entry before
                    # descending so a later file fsync does not overstate
                    # crash durability across an unsynced ancestor chain.
                    os.mkdir(component, 0o700, dir_fd=directory_fd)
                    os.fsync(directory_fd)
                except FileExistsError:
                    pass
                try:
                    next_fd = os.open(component, flags, dir_fd=directory_fd)
                except OSError as error:
                    raise ReceiptError(
                        "receipt destination parent component is not a real directory: "
                        f"{absolute.parent} ({error})"
                    ) from error
            except OSError as error:
                if error.errno in {errno.ELOOP, errno.ENOTDIR}:
                    raise ReceiptError(
                        "receipt destination parent component is a symlink or not a "
                        f"directory: {absolute.parent}"
                    ) from error
                raise
            os.close(directory_fd)
            directory_fd = next_fd
        return absolute, directory_fd
    except BaseException:
        os.close(directory_fd)
        raise


def _parse_file_identity(value: str) -> tuple[int, int]:
    try:
        device_text, inode_text = value.split(":", 1)
        if not device_text.isdecimal() or not inode_text.isdecimal():
            raise ValueError
        return int(device_text), int(inode_text)
    except ValueError as error:
        raise ReceiptError(
            "temporary-root identity must use the decimal DEVICE:INODE form"
        ) from error


def _same_file_identity(left: os.stat_result, right: os.stat_result) -> bool:
    return left.st_dev == right.st_dev and left.st_ino == right.st_ino


def _remove_directory_contents(directory_fd: int) -> None:
    """Remove one already-open tree without following descendant symlinks."""

    os.fchmod(directory_fd, 0o700)
    with os.scandir(directory_fd) as entries:
        names = [entry.name for entry in entries]

    flags = _secure_directory_flags()
    for name in names:
        before = os.stat(name, dir_fd=directory_fd, follow_symlinks=False)
        if stat.S_ISDIR(before.st_mode):
            child_fd = os.open(name, flags, dir_fd=directory_fd)
            try:
                opened = os.fstat(child_fd)
                if not stat.S_ISDIR(opened.st_mode) or not _same_file_identity(
                    before, opened
                ):
                    raise ReceiptError(
                        f"temporary-tree directory changed while opening it: {name}"
                    )
                _remove_directory_contents(child_fd)
                final = os.stat(name, dir_fd=directory_fd, follow_symlinks=False)
                if not stat.S_ISDIR(final.st_mode) or not _same_file_identity(
                    opened, final
                ):
                    raise ReceiptError(
                        f"temporary-tree directory changed before removal: {name}"
                    )
                os.rmdir(name, dir_fd=directory_fd)
            finally:
                os.close(child_fd)
        else:
            final = os.stat(name, dir_fd=directory_fd, follow_symlinks=False)
            if not _same_file_identity(before, final) or stat.S_IFMT(
                before.st_mode
            ) != stat.S_IFMT(final.st_mode):
                raise ReceiptError(
                    f"temporary-tree entry changed before removal: {name}"
                )
            # Unlink the directory entry itself. Symlink targets are never opened.
            os.unlink(name, dir_fd=directory_fd)


def remove_private_temp_tree(
    path: Path,
    *,
    system_parent: Path,
    expected_prefix: str,
    expected_identity: str,
) -> None:
    """Remove an owned private /tmp child through bound directory descriptors.

    The root and every traversed directory are opened with ``O_NOFOLLOW`` and
    revalidated by device/inode. Descendant deletion is descriptor-relative;
    symlinks are unlinked and never followed. The private mode excludes other
    UIDs, but portable POSIX unlink/rmdir remain name-based operations: a
    malicious process running under this same UID can still race a final
    identity check. Canonical release lanes therefore require stronger process
    isolation and remain blocked; this helper is for local diagnostics only.
    """

    if os.name != "posix" or not hasattr(os, "fchmod"):
        raise ReceiptError("descriptor-bound temporary-tree cleanup requires POSIX")
    if os.rmdir not in os.supports_dir_fd:
        raise ReceiptError("descriptor-bound cleanup is unavailable: rmdir lacks dir_fd")
    if not expected_prefix.startswith("trust-") or not expected_prefix.endswith("."):
        raise ReceiptError("temporary-root prefix must use the trust-NAME. form")
    if any(character not in "abcdefghijklmnopqrstuvwxyz0123456789-." for character in expected_prefix):
        raise ReceiptError("temporary-root prefix contains unsafe characters")

    fixed_parent = Path("/tmp").resolve(strict=True)
    selected_parent = system_parent.resolve(strict=True)
    if selected_parent != fixed_parent:
        raise ReceiptError(
            f"temporary-root parent is not the fixed system /tmp: {selected_parent}"
        )

    raw_path = os.fspath(path)
    if not os.path.isabs(raw_path):
        raise ReceiptError(f"temporary root is not absolute: {path}")
    absolute = Path(os.path.abspath(raw_path))
    if Path(raw_path) != absolute or absolute.parent != selected_parent:
        raise ReceiptError(
            f"temporary root is not a normalized direct child of /tmp: {path}"
        )
    if not absolute.name.startswith(expected_prefix):
        raise ReceiptError(f"temporary root has an unexpected name: {absolute}")
    suffix = absolute.name[len(expected_prefix) :]
    if len(suffix) < 6 or any(
        character not in "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_"
        for character in suffix
    ):
        raise ReceiptError(f"temporary root has an unsafe random suffix: {absolute}")

    expected_device, expected_inode = _parse_file_identity(expected_identity)
    flags = _secure_directory_flags()
    parent_fd = os.open(selected_parent, flags)
    root_fd: int | None = None
    try:
        entry = os.stat(absolute.name, dir_fd=parent_fd, follow_symlinks=False)
        if not stat.S_ISDIR(entry.st_mode):
            raise ReceiptError(f"temporary root is not a real directory: {absolute}")
        if entry.st_uid != os.getuid():
            raise ReceiptError(f"temporary root is not owned by the current user: {absolute}")
        if stat.S_IMODE(entry.st_mode) != 0o700:
            raise ReceiptError(f"temporary root does not have private mode 700: {absolute}")
        if (entry.st_dev, entry.st_ino) != (expected_device, expected_inode):
            raise ReceiptError(f"temporary root identity changed before cleanup: {absolute}")

        root_fd = os.open(absolute.name, flags, dir_fd=parent_fd)
        opened = os.fstat(root_fd)
        if not _same_file_identity(entry, opened):
            raise ReceiptError(f"temporary root changed while opening it: {absolute}")
        _remove_directory_contents(root_fd)

        final = os.stat(absolute.name, dir_fd=parent_fd, follow_symlinks=False)
        if not stat.S_ISDIR(final.st_mode) or not _same_file_identity(opened, final):
            raise ReceiptError(f"temporary root changed before final removal: {absolute}")
        os.rmdir(absolute.name, dir_fd=parent_fd)
    finally:
        if root_fd is not None:
            os.close(root_fd)
        os.close(parent_fd)


def _require_publishable_destination(
    directory_fd: int, filename: str, display: Path
) -> None:
    try:
        info = os.stat(filename, dir_fd=directory_fd, follow_symlinks=False)
    except FileNotFoundError:
        return
    if stat.S_ISLNK(info.st_mode):
        raise ReceiptError(f"receipt destination is a symlink: {display}")
    if not stat.S_ISREG(info.st_mode):
        raise ReceiptError(f"receipt destination is not a regular file: {display}")


def _require_absent_destination(
    directory_fd: int, filename: str, display: Path
) -> None:
    try:
        os.stat(filename, dir_fd=directory_fd, follow_symlinks=False)
    except FileNotFoundError:
        return
    raise ReceiptError(f"receipt destination already exists; refusing to overwrite: {display}")


def _create_unique_temporary(directory_fd: int, filename: str) -> tuple[str, int]:
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW
    for _attempt in range(100):
        temporary = f".{filename}.{secrets.token_hex(16)}.tmp"
        try:
            descriptor = os.open(temporary, flags, 0o600, dir_fd=directory_fd)
        except FileExistsError:
            continue
        return temporary, descriptor
    raise ReceiptError("could not allocate a unique same-directory receipt temporary")


def prepare_new_receipt_destination(
    destination: Path, *, caller_directory: Path
) -> Path:
    """Anchor a new receipt path without resolving away symlink components.

    This is an early, diagnostic preflight.  The no-replace publication path
    repeats the absence check using directory file descriptors at commit time,
    so this function is not relied on for race safety.
    """

    try:
        caller = caller_directory.resolve(strict=True)
    except OSError as error:
        raise ReceiptError(
            f"receipt caller directory does not exist: {caller_directory}"
        ) from error
    if not caller.is_dir():
        raise ReceiptError(f"receipt caller path is not a directory: {caller}")

    raw = os.fspath(destination)
    if not raw:
        raise ReceiptError("receipt destination must name a file")
    anchored = Path(os.path.abspath(raw if os.path.isabs(raw) else caller / raw))
    if not anchored.name:
        raise ReceiptError("receipt destination must name a file")

    try:
        anchored.lstat()
    except FileNotFoundError:
        pass
    except OSError as error:
        raise ReceiptError(f"could not inspect receipt destination: {anchored}") from error
    else:
        raise ReceiptError(
            f"receipt destination already exists; refusing to overwrite: {anchored}"
        )

    # Reject existing symlink/non-directory ancestors now.  Missing ancestors
    # are allowed and will later be created through the descriptor-relative,
    # no-follow publication path.
    ancestor = anchored.parent
    while True:
        try:
            info = ancestor.lstat()
        except FileNotFoundError:
            parent = ancestor.parent
            if parent == ancestor:
                raise ReceiptError(
                    f"receipt destination has no existing absolute anchor: {anchored}"
                )
            ancestor = parent
            continue
        except OSError as error:
            raise ReceiptError(
                f"could not inspect receipt destination parent: {ancestor}"
            ) from error
        if stat.S_ISLNK(info.st_mode) or not stat.S_ISDIR(info.st_mode):
            raise ReceiptError(
                "receipt destination parent component is a symlink or not a "
                f"directory: {ancestor}"
            )
        break

    return anchored


def write_receipt(
    destination: Path,
    document: Mapping[str, Any],
    *,
    replace_existing: bool = True,
) -> None:
    """Atomically publish a validated passing receipt.

    Serialization and schema validation happen before the destination or its
    parent is touched.  The destination is checked both before creating the
    temporary file and immediately before publication.  With
    ``replace_existing=False``, a hard link publishes the fully synced
    temporary file only if the destination is still absent; this closes the
    preflight-to-publication replacement race without exposing partial bytes.
    That link is the visibility commit. A later temporary-unlink or directory-
    fsync error can report failure while the complete validated record remains
    visible; it can never expose a partial record, and these records are local
    diagnostics rather than release authority.
    """

    payload = _serialized_receipt(document)
    # Make the lexical path absolute without resolving symlinks: resolving
    # first would hide exactly the parent traversal this publication boundary
    # must reject.
    destination, directory_fd = _open_secure_parent(destination)
    temporary: str | None = None
    try:
        require_destination = (
            _require_publishable_destination
            if replace_existing
            else _require_absent_destination
        )
        require_destination(directory_fd, destination.name, destination)
        temporary, descriptor = _create_unique_temporary(directory_fd, destination.name)
        try:
            with os.fdopen(descriptor, "wb") as handle:
                os.fchmod(handle.fileno(), 0o644)
                handle.write(payload)
                handle.flush()
                os.fsync(handle.fileno())
        except BaseException:
            try:
                os.close(descriptor)
            except OSError:
                pass
            raise
        require_destination(directory_fd, destination.name, destination)
        if replace_existing:
            os.replace(
                temporary,
                destination.name,
                src_dir_fd=directory_fd,
                dst_dir_fd=directory_fd,
            )
            temporary = None
        else:
            if os.link not in os.supports_dir_fd:
                raise ReceiptError(
                    "secure no-replace receipt publication is unavailable: "
                    "link lacks dir_fd support"
                )
            try:
                os.link(
                    temporary,
                    destination.name,
                    src_dir_fd=directory_fd,
                    dst_dir_fd=directory_fd,
                    follow_symlinks=False,
                )
            except FileExistsError as error:
                raise ReceiptError(
                    "receipt destination appeared during publication; refusing "
                    f"to overwrite: {destination}"
                ) from error
            os.unlink(temporary, dir_fd=directory_fd)
            temporary = None
        os.fsync(directory_fd)
    finally:
        if temporary is not None:
            try:
                os.unlink(temporary, dir_fd=directory_fd)
            except FileNotFoundError:
                pass
        os.close(directory_fd)


def _load_json_object(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise ReceiptError(f"could not read JSON object {path}: {error}") from error
    if not isinstance(value, dict):
        raise ReceiptError(f"JSON document is not an object: {path}")
    return value


def _load_archive_manifest(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except (OSError, UnicodeError) as error:
        raise ReceiptError(f"could not read archive manifest {path}: {error}") from error
    for line_number, line in enumerate(lines, 1):
        if not line.strip():
            continue
        try:
            row = json.loads(line)
        except json.JSONDecodeError as error:
            raise ReceiptError(
                f"invalid archive manifest JSON at {path}:{line_number}: {error}"
            ) from error
        if not isinstance(row, dict):
            raise ReceiptError(f"archive manifest row {line_number} is not an object")
        rows.append(row)
    if not rows:
        raise ReceiptError("archive manifest is empty")
    return rows


def _manifest_package_name(component: str) -> str:
    if component in _PREVIEW_COMPONENTS:
        return f"{component}-preview"
    return component


def _url_filename(value: Any, *, field: str) -> str:
    if not isinstance(value, str) or not value:
        raise ReceiptError(f"channel manifest is missing {field}")
    filename = Path(urlsplit(value).path).name
    if not filename:
        raise ReceiptError(f"channel manifest {field} has no archive filename: {value!r}")
    return filename


def _component_list_contains(entries: Any, package: str, target: str) -> bool:
    if not isinstance(entries, list):
        return False
    return any(
        isinstance(entry, dict)
        and entry.get("pkg") == package
        and entry.get("target") == target
        for entry in entries
    )


def validate_channel_manifest(
    manifest_path: Path,
    archive_manifest_path: Path,
    *,
    dist_dir: Path,
    host: str,
) -> dict[str, Any]:
    """Validate Trust channel metadata against the archives on disk."""

    manifest_path = manifest_path.resolve(strict=True)
    dist_dir = dist_dir.resolve(strict=True)
    if tomllib is None:
        raise ReceiptError("channel validation requires Python 3.11+ with tomllib")
    try:
        manifest = tomllib.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, tomllib.TOMLDecodeError) as error:
        raise ReceiptError(f"could not read channel manifest {manifest_path}: {error}") from error
    if not isinstance(manifest, dict) or str(manifest.get("manifest-version")) != "2":
        raise ReceiptError("channel manifest must use manifest-version = 2")

    profiles = manifest.get("profiles")
    default_profile = profiles.get("default") if isinstance(profiles, dict) else None
    if not isinstance(default_profile, list) or not all(
        isinstance(item, str) for item in default_profile
    ):
        raise ReceiptError("channel manifest profiles.default must be a string array")
    if len(default_profile) != len(set(default_profile)):
        raise ReceiptError("channel manifest profiles.default contains duplicate components")
    missing_profile = sorted(REQUIRED_DEFAULT_PROFILE - set(default_profile))
    if missing_profile:
        raise ReceiptError(
            "channel manifest default profile is missing: " + ", ".join(missing_profile)
        )

    packages = manifest.get("pkg")
    if not isinstance(packages, dict):
        raise ReceiptError("channel manifest is missing pkg table")
    targo_trust = packages.get("targo-trust")
    targo_targets = targo_trust.get("target") if isinstance(targo_trust, dict) else None
    targo_host = targo_targets.get(host) if isinstance(targo_targets, dict) else None
    if not isinstance(targo_host, dict) or targo_host.get("available") is not True:
        raise ReceiptError(f"channel manifest targo-trust target {host} is not available")

    trust_package = packages.get("trust")
    trust_targets = trust_package.get("target") if isinstance(trust_package, dict) else None
    trust_host = trust_targets.get(host) if isinstance(trust_targets, dict) else None
    if not isinstance(trust_host, dict) or trust_host.get("available") is not True:
        raise ReceiptError(f"channel manifest umbrella trust target {host} is not available")
    if not _component_list_contains(trust_host.get("extensions"), "targo-trust", host):
        raise ReceiptError(
            f"channel manifest umbrella trust target {host} omits the targo-trust extension"
        )

    rows = _load_archive_manifest(archive_manifest_path)
    component_values = [row.get("component") for row in rows]
    if not all(isinstance(component, str) for component in component_values):
        raise ReceiptError("archive manifest contains a non-string component")
    components = set(component_values)
    missing_archives = sorted(REQUIRED_ARCHIVE_COMPONENTS - components)
    if missing_archives:
        raise ReceiptError("archive manifest is missing: " + ", ".join(missing_archives))

    seen: set[tuple[str, str]] = set()
    selected_by_component: dict[str, int] = {}
    for index, row in enumerate(rows, 1):
        component = row.get("component")
        filename = row.get("archive_filename")
        archive_path_value = row.get("archive_path")
        extension = row.get("extension")
        digest = row.get("sha256")
        size = row.get("size_bytes")
        root = row.get("archive_root")
        selected = row.get("selected")
        string_values = [component, filename, archive_path_value, extension, digest, root]
        if not all(isinstance(value, str) and value for value in string_values):
            raise ReceiptError(f"archive manifest row {index} has missing string fields")
        if extension not in {"tar.gz", "tar.xz"}:
            raise ReceiptError(
                f"archive manifest row {index} has unsupported extension {extension!r}"
            )
        if not filename.endswith(f".{extension}"):
            raise ReceiptError(
                f"archive manifest row {index} filename does not match {extension}: {filename}"
            )
        if not isinstance(size, int) or isinstance(size, bool) or size < 1:
            raise ReceiptError(f"archive manifest row {index} has invalid size")
        if not isinstance(selected, bool):
            raise ReceiptError(f"archive manifest row {index} has invalid selected flag")
        if len(digest) != 64 or any(character not in "0123456789abcdef" for character in digest):
            raise ReceiptError(f"archive manifest row {index} has invalid SHA-256")
        key = (component, extension)
        if key in seen:
            raise ReceiptError(f"archive manifest repeats {component}.{extension}")
        seen.add(key)
        if selected:
            selected_by_component[component] = selected_by_component.get(component, 0) + 1

        archive_path = Path(archive_path_value).resolve(strict=True)
        try:
            archive_path.relative_to(dist_dir)
        except ValueError as error:
            raise ReceiptError(f"archive escapes dist directory: {archive_path}") from error
        if archive_path.name != filename:
            raise ReceiptError(f"archive path/name mismatch for {component}: {archive_path}")
        info = archive_path.stat()
        if not stat.S_ISREG(info.st_mode) or info.st_size != size:
            raise ReceiptError(f"archive size/type changed for {archive_path}")
        if sha256_file(archive_path) != digest:
            raise ReceiptError(f"archive digest changed for {archive_path}")

        package_name = _manifest_package_name(component)
        package = packages.get(package_name)
        targets = package.get("target") if isinstance(package, dict) else None
        target_name = "*" if component == "trust-src" else host
        target = targets.get(target_name) if isinstance(targets, dict) else None
        if not isinstance(target, dict) or target.get("available") is not True:
            raise ReceiptError(
                f"channel manifest package {package_name} target {target_name} is not available"
            )
        if extension == "tar.gz":
            url_field, hash_field = "url", "hash"
        else:
            url_field, hash_field = "xz_url", "xz_hash"
        manifest_filename = _url_filename(
            target.get(url_field), field=f"pkg.{package_name}.target.{target_name}.{url_field}"
        )
        if manifest_filename != filename:
            raise ReceiptError(
                f"channel manifest URL names {manifest_filename}, expected {filename}"
            )
        if target.get(hash_field) != digest:
            raise ReceiptError(
                f"channel manifest hash mismatch for {package_name}/{target_name}/{extension}"
            )

    bad_selected = sorted(
        component
        for component in REQUIRED_ARCHIVE_COMPONENTS
        if selected_by_component.get(component) != 1
    )
    if bad_selected:
        raise ReceiptError(
            "archive manifest must select exactly one archive for: " + ", ".join(bad_selected)
        )

    return {
        "path": str(manifest_path),
        "sha256": sha256_file(manifest_path),
        "manifest_version": "2",
        "date": manifest.get("date"),
        "default_profile": default_profile,
        "host": host,
        "archive_rows_validated": len(rows),
        "required_archive_components": sorted(REQUIRED_ARCHIVE_COMPONENTS),
        "targo_trust_available": True,
        "umbrella_targo_trust_extension": True,
        "hosting_claim": "none-local-rehearsal-only",
    }


def _publish_command(args: argparse.Namespace) -> None:
    candidate = _load_json_object(args.input)
    write_receipt(args.output, candidate, replace_existing=not args.no_replace)


def _publish_after_cleanup_command(args: argparse.Namespace) -> None:
    cleanup_root = args.cleanup_path.resolve(strict=True)
    input_info = args.input.lstat()
    if stat.S_ISLNK(input_info.st_mode) or not stat.S_ISREG(input_info.st_mode):
        raise ReceiptError("cleanup-bound receipt candidate must be an exact regular file")
    candidate_path = args.input.resolve(strict=True)
    if candidate_path.parent != cleanup_root:
        raise ReceiptError(
            "cleanup-bound receipt candidate must be a direct child of its temporary root"
        )
    output_path = Path(os.path.abspath(os.fspath(args.output)))
    if output_path == cleanup_root or cleanup_root in output_path.parents:
        raise ReceiptError("receipt output must be outside the temporary cleanup root")

    candidate = _load_json_object(candidate_path)
    # Validate and serialize while the private candidate still exists. The
    # in-memory object remains available after its temporary tree is removed.
    _serialized_receipt(candidate)
    remove_private_temp_tree(
        cleanup_root,
        system_parent=args.system_parent,
        expected_prefix=args.expected_prefix,
        expected_identity=args.expected_identity,
    )
    # This no-replace commit is deliberately the command's final operation.
    # No cleanup, status rendering, or source check follows publication.
    write_receipt(output_path, candidate, replace_existing=False)


def _prepare_output_command(args: argparse.Namespace) -> None:
    destination = prepare_new_receipt_destination(
        args.output,
        caller_directory=args.caller_directory,
    )
    print(destination)


def _validate_channel_command(args: argparse.Namespace) -> None:
    result = validate_channel_manifest(
        args.manifest,
        args.archive_manifest,
        dist_dir=args.dist_dir,
        host=args.host,
    )
    json.dump(result, sys.stdout, indent=2, sort_keys=True)
    sys.stdout.write("\n")


def _validate_stage_command(args: argparse.Namespace) -> None:
    result = validate_stage_provenance(
        args.provenance,
        repository_head=args.repository_head,
        trustc_path=args.trustc,
    )
    json.dump(result, sys.stdout, indent=2, sort_keys=True)
    sys.stdout.write("\n")


def _remove_private_temp_command(args: argparse.Namespace) -> None:
    remove_private_temp_tree(
        args.path,
        system_parent=args.system_parent,
        expected_prefix=args.expected_prefix,
        expected_identity=args.expected_identity,
    )


def parse_args(argv: Iterable[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    publish = subparsers.add_parser("publish", help="atomically publish a passing receipt")
    publish.add_argument("--input", type=Path, required=True)
    publish.add_argument("--output", type=Path, required=True)
    publish.add_argument(
        "--no-replace",
        action="store_true",
        help="fail atomically if the output already exists",
    )
    publish.set_defaults(run=_publish_command)

    publish_after_cleanup = subparsers.add_parser(
        "publish-after-cleanup",
        help="remove a bound private gate tree, then commit its validated record",
    )
    publish_after_cleanup.add_argument("--input", type=Path, required=True)
    publish_after_cleanup.add_argument("--output", type=Path, required=True)
    publish_after_cleanup.add_argument("--cleanup-path", type=Path, required=True)
    publish_after_cleanup.add_argument("--system-parent", type=Path, required=True)
    publish_after_cleanup.add_argument("--expected-prefix", required=True)
    publish_after_cleanup.add_argument("--expected-identity", required=True)
    publish_after_cleanup.set_defaults(run=_publish_after_cleanup_command)

    prepare = subparsers.add_parser(
        "prepare-output",
        help="anchor and preflight a new receipt destination",
    )
    prepare.add_argument("--output", type=Path, required=True)
    prepare.add_argument("--caller-directory", type=Path, required=True)
    prepare.set_defaults(run=_prepare_output_command)

    channel = subparsers.add_parser(
        "validate-channel", help="validate channel TOML against a local archive manifest"
    )
    channel.add_argument("--manifest", type=Path, required=True)
    channel.add_argument("--archive-manifest", type=Path, required=True)
    channel.add_argument("--dist-dir", type=Path, required=True)
    channel.add_argument("--host", required=True)
    channel.set_defaults(run=_validate_channel_command)

    stage = subparsers.add_parser(
        "validate-stage", help="validate a local Stage2 provenance and compiler binding"
    )
    stage.add_argument("--provenance", type=Path, required=True)
    stage.add_argument("--repository-head", required=True)
    stage.add_argument("--trustc", type=Path, required=True)
    stage.set_defaults(run=_validate_stage_command)

    cleanup = subparsers.add_parser(
        "remove-private-temp",
        help="descriptor-bound removal of an owned private /tmp gate directory",
    )
    cleanup.add_argument("--path", type=Path, required=True)
    cleanup.add_argument("--system-parent", type=Path, required=True)
    cleanup.add_argument("--expected-prefix", required=True)
    cleanup.add_argument("--expected-identity", required=True)
    cleanup.set_defaults(run=_remove_private_temp_command)

    return parser.parse_args(argv)


def main(argv: Iterable[str] | None = None) -> int:
    try:
        args = parse_args(argv)
        args.run(args)
    except (OSError, ReceiptError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
