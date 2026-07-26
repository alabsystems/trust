#!/usr/bin/env python3
"""Prepare a repo-local Trust stage0 dist snapshot.

This converts an `x dist` output directory into a local dist tree whose channel
identity is `trust`, then writes a candidate `src/stage0` file for rehearsal.
It does not upload, publish, or contact any remote service.
"""

from __future__ import annotations

import argparse
import copy
import datetime as dt
import hashlib
import io
import json
import os
import re
import shlex
import sys
import tarfile
from pathlib import Path

try:
    import tomllib
except ModuleNotFoundError:  # Python < 3.11
    try:
        import tomli as tomllib  # type: ignore[import-not-found]
    except ModuleNotFoundError:
        print(
            "error: Python 3.11+ or the 'tomli' package is required to parse TOML",
            file=sys.stderr,
        )
        sys.exit(2)


SOURCE_STAGE0_COMPONENTS = (
    "trustc",
    "trustc-dev",
    "trust-std",
    "targo",
    "tippy-preview",
    "trustfmt-preview",
    "trust-docs",
    "targo-trust",
    "trust-analyzer-preview",
    "trust-src",
    "trust-llvm-tools-preview",
)
STAGE0_COMPONENT_RENAMES = {
    "miri": "trust-miri",
    "miri-preview": "trust-miri-preview",
    "rust-analyzer": "trust-analyzer",
    "rust-analyzer-preview": "trust-analyzer-preview",
    "rust-docs": "trust-docs",
    "rustc-dev": "trustc-dev",
    "rustc-docs": "trustc-docs",
    "rust-mingw": "trust-mingw",
    "rust-analysis": "trust-analysis",
    "rust-src": "trust-src",
    "rust-std": "trust-std",
    "rustc": "trustc",
    "rustdoc": "trustdoc",
    "rustfmt": "trustfmt",
    "rustfmt-preview": "trustfmt-preview",
    "llvm-tools": "trust-llvm-tools",
    "llvm-tools-preview": "trust-llvm-tools-preview",
    # Trust: the Trust-native dist producer ships the frontend as `targo`, the
    # verifier driver as `targo-trust`, and the linter as `tippy`. Map those
    # producer archive names onto the canonical stage0 component spellings the
    # admission machinery + discover audit pin (targo / targo-trust /
    # tippy). The plain rename covers the .tar filename prefix; the
    # in-archive member dirs/bins are handled in rewrite_stage0_tool_member_path.
    "targo": "targo",
    "targo-trust": "targo-trust",
    "tippy": "tippy",
    "tippy-preview": "tippy-preview",
}
DEFAULT_STAGE0_COMPONENTS = tuple(
    STAGE0_COMPONENT_RENAMES.get(component, component) for component in SOURCE_STAGE0_COMPONENTS
)
REQUIRED_MANIFEST_PACKAGES = ("trust", *SOURCE_STAGE0_COMPONENTS)
TRUST_ROOT_TOKEN = "{trust-root}"
STAGE0_ARTIFACT_ROOTS = ("artifacts", "artifacts-with-llvm-assertions")
SHA256_PATTERN = re.compile(r"[0-9a-f]{64}")
REQUIRED_ARCHIVE_ENTRYPOINTS = {
    "trustc": (
        "trustc/bin/trustc",
        "trustc/bin/rustc",
        "trustc/bin/trustdoc",
        "trustc/libexec/trust-analyzer-proc-macro-srv",
    ),
    "targo": ("targo/bin/targo", "targo/bin/cargo"),
    "targo-trust": ("targo-trust/bin/targo-trust",),
    "trustfmt": (
        "trustfmt/bin/trustfmt",
        "trustfmt/bin/targo-fmt",
    ),
    "tippy": (
        "tippy/bin/tippy",
        "tippy/bin/targo-tippy",
        "tippy/bin/tippy-driver",
    ),
    "trust-analyzer": ("trust-analyzer/bin/trust-analyzer",),
}
FORBIDDEN_ARCHIVE_ENTRYPOINTS: dict[str, tuple[str, ...]] = {
    "trustc": (
        "trustc/bin/rustdoc",
        "trustc/libexec/rust-analyzer-proc-macro-srv",
    ),
    "targo-trust": ("targo-trust/bin/cargo-trust",),
    "trustfmt": ("trustfmt/bin/rustfmt", "trustfmt/bin/cargo-fmt"),
    "tippy": (
        "tippy/bin/cargo-clippy",
        "tippy/bin/clippy-driver",
        "tippy/bin/targo-clippy",
        "tippy/bin/trust-clippy",
        "tippy/bin/trust-clippy-driver",
    ),
    "trust-analyzer": ("trust-analyzer/bin/rust-analyzer",),
}
LEGACY_TIPPY_ARCHIVE_LEAF_RENAMES = {
    "cargo-clippy": "tippy",
    "trust-clippy": "tippy",
    "targo-clippy": "targo-tippy",
    "clippy-driver": "tippy-driver",
    "trust-clippy-driver": "tippy-driver",
}
STAGE0_DIST_PRODUCER_ALIASES = (
    "trustc",
    "trustc-dev",
    "trust-std",
    "targo",  # Trust: x.py dist alias for the frontend is targo
    "targo-trust",
    "trust-docs",
    "trustfmt",
    "tippy",  # Trust: x.py dist alias for the linter is tippy
    "trust-analyzer",
    "trust-src",
    "trust-llvm-tools",
)
STAGE0_DIST_PRODUCER_DRY_RUN_COMMAND = (
    "./x.py",
    "dist",
    "--dry-run",
    "--stage",
    "2",
    *STAGE0_DIST_PRODUCER_ALIASES,
)
STAGE0_DIST_PRODUCER_COMMAND = tuple(
    part for part in STAGE0_DIST_PRODUCER_DRY_RUN_COMMAND if part != "--dry-run"
)
STAGE0_DIST_PRODUCER_ALIAS_PATTERNS = {
    "trustc": ('run.alias("trustc")', "dist::Rustc"),
    "trustc-dev": ('run.alias("trustc-dev")', "dist::RustcDev"),
    "trust-std": ('run.alias("trust-std")', "dist::Std"),
    "targo": ('run.alias("targo")', "dist::Cargo"),  # Trust: dist alias targo, step type kept
    "targo-trust": ('run.path("targo-trust")', "dist::TCargoTrust"),
    "trust-docs": ('run.alias("trust-docs")', "dist::Docs"),
    "trustfmt": ('run.alias("trustfmt")', "dist::Rustfmt"),
    "tippy": ('run.alias("tippy")', "dist::Clippy"),  # Trust: dist alias tippy, step type kept
    "trust-analyzer": ('run.alias("trust-analyzer")', "dist::RustAnalyzer"),
    "trust-src": ('run.alias("trust-src")', "dist::Src"),
    "trust-llvm-tools": ('run.alias("trust-llvm-tools")', "dist::LlvmTools"),
}
# These two producers intentionally register a source path and both the owned
# and compatibility aliases in one returned ShouldRun chain. Whole-file
# substring checks cannot authenticate that relationship: a matching comment,
# string, helper, or different Step would otherwise satisfy the audit. Keep the
# exact Step/body contract here and parse it structurally below.
STAGE0_DIST_PRODUCER_EXACT_SHOULD_RUN = {
    "trustc": (
        "Rustc",
        'run.path("compiler/rustc").alias("trustc").alias("rustc")',
    ),
    "trust-std": (
        "Std",
        'run.path("library/std").alias("trust-std").alias("rust-std")',
    ),
}
STAGE0_DIST_PRODUCER_CONFIG_PATTERNS = (
    ("bootstrap.example.toml", "#build.extended = false"),
    ("bootstrap.example.toml", "#build.tools = ["),
    ("bootstrap.example.toml", '"targo"'),
    ("bootstrap.example.toml", '"targo-trust"'),
    ("bootstrap.example.toml", '"trustdoc"'),
    ("bootstrap.example.toml", '"tippy"'),
    ("bootstrap.example.toml", '"trustfmt"'),
    ("bootstrap.example.toml", '"trust-analyzer"'),
    ("bootstrap.example.toml", '"trust-analysis"'),
    ("bootstrap.example.toml", '"src"'),
    ("bootstrap.example.toml", "#rust.channel = "),
    ("bootstrap.example.toml", "#dist.sign-folder = "),
    ("bootstrap.example.toml", "#dist.upload-addr = "),
    ("bootstrap.example.toml", '#dist.compression-formats = ["gz", "xz"]'),
    ("src/bootstrap/defaults/bootstrap.dist.toml", "extended = true"),
    ("src/bootstrap/defaults/bootstrap.dist.toml", 'channel = "auto-detect"'),
)
STAGE0_DIST_PRODUCER_ARTIFACT_PATTERNS = (
    (
        "src/bootstrap/src/core/build_steps/dist.rs",
        'Tarball::new(builder, "trust-std", &target.triple)',
        "standard-library dist step emits the Trust-owned trust-std archive",
    ),
)
STAGE0_ARCHIVE_SUFFIXES = (".tar", ".tar.gz", ".tar.xz")
STAGE0_ADMISSION_FILENAME = "trust-stage0-admission.json"
STAGE0_ADMISSION_SCHEMA = "trust.stage0-payload-root-admission.v1"


class MissingDistTarballs(FileNotFoundError):
    def __init__(
        self,
        *,
        input_dist: Path,
        date: str,
        filenames: tuple[str, ...],
    ) -> None:
        self.input_dist = input_dist
        self.date = date
        self.filenames = filenames
        super().__init__(self.format_message())

    def format_message(self) -> str:
        lines = [
            (
                "missing dist tarballs referenced by manifest for local Trust "
                f"stage0 snapshot ({len(self.filenames)}):"
            )
        ]
        for filename in self.filenames:
            checked = ", ".join(
                str(candidate) for candidate in source_tarball_candidates(
                    self.input_dist,
                    filename,
                    self.date,
                )
            )
            lines.append(f"  - {filename} (checked: {checked})")
        lines.append(
            "Materialize the Trust-owned x dist output into --input-dist, or point "
            "--input-dist at a dist root that contains these archive payloads."
        )
        return "\n".join(lines)


class Stage0PayloadPreflightBlocked(Exception):
    """Signal a nonzero JSON preflight result without adding text to stderr."""


def repo_root() -> Path:
    return Path(__file__).resolve().parents[3]


def shell_command(parts: tuple[str, ...]) -> str:
    return shlex.join(parts)


def default_dist_server(output_root: Path) -> str:
    try:
        rel_output_root = output_root.relative_to(repo_root())
    except ValueError:
        return output_root.as_uri()
    return f"file://{TRUST_ROOT_TOKEN}/{rel_output_root.as_posix()}"


def sha256_file(path: Path) -> str:
    hasher = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            hasher.update(block)
    return hasher.hexdigest()


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def quote_key(key: str) -> str:
    if key and all(ch.isalnum() or ch in "_-" for ch in key):
        return key
    return json.dumps(key)


def format_toml_value(value: object) -> str:
    if isinstance(value, str):
        return json.dumps(value)
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, int | float):
        return str(value)
    if isinstance(value, dt.date):
        return json.dumps(value.isoformat())
    if isinstance(value, dict):
        items = (
            f"{quote_key(str(key))} = {format_toml_value(item)}"
            for key, item in value.items()
        )
        return "{ " + ", ".join(items) + " }"
    if isinstance(value, list):
        return "[" + ", ".join(format_toml_value(item) for item in value) + "]"
    raise TypeError(f"unsupported TOML value: {value!r}")


def dump_toml(data: dict[str, object]) -> str:
    lines: list[str] = []

    def emit_table(prefix: tuple[str, ...], table: dict[str, object]) -> None:
        for key, value in table.items():
            if not isinstance(value, dict):
                lines.append(f"{quote_key(key)} = {format_toml_value(value)}")

        for key, value in table.items():
            if isinstance(value, dict):
                if lines and lines[-1] != "":
                    lines.append("")
                child_prefix = (*prefix, key)
                lines.append("[" + ".".join(quote_key(part) for part in child_prefix) + "]")
                emit_table(child_prefix, value)

    emit_table((), data)
    return "\n".join(lines) + "\n"


def replace_channel_token(value: str, source_channel: str, owned_channel: str) -> str:
    rewritten = (
        value.replace(f"-{source_channel}-", f"-{owned_channel}-")
        .replace(f"-{source_channel}.", f"-{owned_channel}.")
        .replace(f"-{source_channel} ", f"-{owned_channel} ")
        .replace(f"-{source_channel}\n", f"-{owned_channel}\n")
        .replace(f"-{source_channel}\r\n", f"-{owned_channel}\r\n")
    )
    source_suffix = f"-{source_channel}"
    if rewritten.endswith(source_suffix):
        return rewritten[: -len(source_suffix)] + f"-{owned_channel}"
    return rewritten


def dist_url(dist_server: str, date: str, filename: str) -> str:
    return f"{dist_server.rstrip('/')}/dist/{date}/{filename}"


def source_tarball_candidates(
    input_dist: Path,
    filename: str,
    date: str,
) -> tuple[Path, ...]:
    return (
        input_dist / filename,
        input_dist / date / filename,
    )


def source_tarball(input_dist: Path, filename: str, date: str) -> Path:
    for candidate in source_tarball_candidates(input_dist, filename, date):
        if candidate.is_file():
            return candidate
    raise FileNotFoundError(f"missing dist tarball referenced by manifest: {filename}")


def tarball_prefix(filename: str) -> str:
    for suffix in (".tar.xz", ".tar.gz"):
        if filename.endswith(suffix):
            return filename[: -len(suffix)]
    raise ValueError(f"unsupported dist tarball extension: {filename}")


def stage0_component_name(component: str) -> str:
    return STAGE0_COMPONENT_RENAMES.get(component, component)


def stage0_tarball_filename(filename: str, *, source_channel: str, owned_channel: str) -> str:
    # Trust: rename the component prefix BEFORE rewriting the channel token.
    # The channel token (e.g. "dev") can collide with a component name suffix
    # (e.g. the "trustc-dev" component on the "dev" source channel), and a
    # whole-string channel replacement would mangle "trustc-dev-" into
    # "trustc-trust-". Splitting the prefix off first makes the rename of the
    # component name and the version/channel segment independent and correct.
    # Candidate component prefixes: every rename source (mapped to its owned
    # name) plus every already-canonical component name (mapped to itself), so
    # we always split off the component name even when no rename applies. This
    # is what keeps a "-dev" inside a component name (trustc-dev) from being
    # rewritten as if it were the "dev" channel token.
    candidates: dict[str, str] = {}
    for owned in (*STAGE0_COMPONENT_RENAMES.values(), *DEFAULT_STAGE0_COMPONENTS):
        candidates.setdefault(owned.removesuffix("-preview"), owned.removesuffix("-preview"))
    for source, owned in STAGE0_COMPONENT_RENAMES.items():
        candidates[source] = owned.removesuffix("-preview")

    prefix = ""
    tail = filename
    for source in sorted(candidates, key=len, reverse=True):
        if filename.startswith(source + "-"):
            prefix = candidates[source]
            tail = filename[len(source) :]
            break
    return prefix + replace_channel_token(tail, source_channel, owned_channel)


def rewrite_member_path(path: str, old_prefix: str, new_prefix: str) -> str:
    if path == old_prefix:
        return new_prefix
    if path.startswith(old_prefix + "/"):
        return new_prefix + path[len(old_prefix) :]
    raise ValueError(
        f"tarball member {path!r} is outside expected top-level directory {old_prefix!r}"
    )


# Producer component image-dir spellings -> canonical stage0 archive dirs. The
# current Trust-native dist producer emits Trust-branded image dirs (targo/
# targo-trust/tippy-preview/trustfmt-preview/trust-analyzer-preview) rather than
# the older upstream spellings; map both onto the canonical stage0 layout the
# admission contract + discover audit pin (targo/targo-trust/tippy/trustfmt/
# trust-analyzer). Shared by the member-path rewrite (materialization) and the
# entrypoint contract check so both strip the `-preview` image dir the same way.
# Only the leading image dir is remapped here; bin leaf names are handled
# separately so the dual trust-/rust- compat entrypoints stay distinct.
STAGE0_IMAGE_DIR_RENAMES = {
    "rustc": "trustc",
    "rustc-dev": "trustc-dev",
    "rustc-docs": "trustc-docs",
    "rust-std": "trust-std",
    "rustfmt": "trustfmt",
    "rust-analyzer": "trust-analyzer",
    "rust-docs": "trust-docs",
    "rust-analysis": "trust-analysis",
    "rust-mingw": "trust-mingw",
    "rust-src": "trust-src",
    "llvm-tools": "trust-llvm-tools",
    "targo": "targo",
    "targo-trust": "targo-trust",
    "tippy-preview": "tippy",
    "tippy": "tippy",
    "trustfmt-preview": "trustfmt",
    "trust-analyzer-preview": "trust-analyzer",
}

# Trust: the produced trustc image ships both spellings of the debugger wrappers,
# but the stage0 seed forbids the inherited rust- aliases (bootstrap.py
# STAGE0_FORBIDDEN_BINS). Drop them during repack; the Trust-canonical
# trust-gdb/-gdbgui/-lldb twins are kept.
STAGE0_FORBIDDEN_DEBUGGER_BINS = ("rust-gdb", "rust-gdbgui", "rust-lldb")


def rewrite_stage0_tool_member_path(path: str) -> str:
    parts = path.split("/")
    if len(parts) < 2:
        return path

    parts[1] = STAGE0_IMAGE_DIR_RENAMES.get(parts[1], parts[1])

    tool_names = {
        "rustc": "trustc",
        "rustdoc": "trustdoc",
        "rust-analyzer": "trust-analyzer",
        "rust-analyzer-proc-macro-srv": "trust-analyzer-proc-macro-srv",
        "rustfmt": "trustfmt",
        # Trust: Trust-native producer bin spellings -> canonical stage0 names.
        "targo": "targo",
        "targo-trust": "targo-trust",
        "cargo-trust": "targo-trust",
        "targo-fmt": "targo-fmt",
        "cargo-fmt": "targo-fmt",
        "targo-tippy": "targo-tippy",
        "tippy": "tippy",
        "tippy-driver": "tippy-driver",
        # Historical aliases are accepted only as redundant copies beside a
        # canonical producer leaf. A preflight in repack_owned_tarball rejects
        # legacy-only payloads: byte-renaming cargo-clippy to tippy changes its
        # argv protocol and produces a component that drops the first user arg.
        **LEGACY_TIPPY_ARCHIVE_LEAF_RENAMES,
    }
    parts[-1] = tool_names.get(parts[-1], parts[-1])
    return "/".join(parts)


def stage0_compat_alias_member_paths(path: str) -> tuple[str, ...]:
    parts = path.split("/")
    if len(parts) < 4 or parts[-2] not in {"bin", "libexec"}:
        return ()

    aliases = {
        "trustc": ("rustc",),
        "targo": ("cargo",),
    }
    alias_names = aliases.get(parts[-1], ())
    if not alias_names:
        return ()

    alias_paths = []
    for alias_name in alias_names:
        aliased = parts.copy()
        aliased[-1] = alias_name
        alias_paths.append("/".join(aliased))
    return tuple(alias_paths)


def is_forbidden_stage0_debugger_bin(member_name: str) -> bool:
    parts = member_name.split("/")
    return (
        len(parts) >= 4
        and parts[-2] == "bin"
        and parts[-1] in STAGE0_FORBIDDEN_DEBUGGER_BINS
    )


# Trust: the wholesale sysroot copy that dist performs pulls stock secondary
# executable aliases (rustdoc, rustfmt, cargo-fmt, cargo-trust, rust-analyzer,
# the stock-named proc-macro server) into the component tarballs even though the
# Trust-only-naming policy forbids shipping them (CLAUDE.md "Toolchain naming").
# These are the FORBIDDEN_ARCHIVE_ENTRYPOINTS. Strip them during the stage0
# snapshot exactly as the debugger aliases (rust-gdb/…) above are stripped, so
# the seed carries Trust-only names by construction. The intentional `rustc` /
# `cargo` compat aliases are deliberately NOT in the forbidden set and survive.
STAGE0_STRIPPED_SECONDARY_ALIASES = frozenset(
    entry for entries in FORBIDDEN_ARCHIVE_ENTRYPOINTS.values() for entry in entries
)


def is_stripped_stage0_secondary_alias(member_name: str) -> bool:
    # `member_name` is already rewritten to its canonical stage0 path
    # (e.g. `trustc/bin/rustdoc`) by the time this is consulted.
    return member_name in STAGE0_STRIPPED_SECONDARY_ALIASES


def validate_tippy_repack_sources(
    source_tar: tarfile.TarFile,
    *,
    old_prefix: str,
    new_prefix: str,
) -> None:
    """Reject semantic byte-renames of legacy-only Tippy executables.

    A modern Tippy frontend may deliberately ship byte-identical inherited
    aliases because it dispatches on argv[0]. Those aliases are safe to remove
    only when the canonical executable is present and the normal duplicate
    fingerprint check below proves equality. An older cargo-clippy-only payload
    needs executable adapters and must stay on bootstrap's explicit legacy
    admission path; merely changing its tar member name is not equivalent.
    """
    canonical_outputs: set[str] = set()
    legacy_outputs: dict[str, str] = {}
    canonical_leaves = frozenset(LEGACY_TIPPY_ARCHIVE_LEAF_RENAMES.values())

    for member in source_tar.getmembers():
        rebased = rewrite_member_path(member.name, old_prefix, new_prefix)
        parts = rebased.split("/")
        if len(parts) < 4 or parts[-2] != "bin":
            continue
        output = rewrite_stage0_tool_member_path(rebased)
        source_leaf = parts[-1]
        if source_leaf in canonical_leaves:
            canonical_outputs.add(output)
        elif source_leaf in LEGACY_TIPPY_ARCHIVE_LEAF_RENAMES:
            legacy_outputs[output] = member.name

    missing_canonical = sorted(set(legacy_outputs).difference(canonical_outputs))
    if missing_canonical:
        sources = ", ".join(repr(legacy_outputs[path]) for path in missing_canonical)
        raise ValueError(
            "cannot byte-rename legacy-only Tippy executable(s) "
            f"{sources}: cargo-clippy and Tippy have different argv/driver-discovery "
            "protocols; use the checksum-pinned legacy bootstrap adapter or produce "
            "a native `x.py dist tippy` archive"
        )


def rewrite_owned_member_bytes(
    path: str,
    data: bytes,
    *,
    source_channel: str,
    owned_channel: str,
) -> bytes:
    parts = path.split("/")
    is_installer_components = len(parts) == 2 and parts[-1] == "components"
    should_rewrite = (
        is_installer_components
        or path.endswith("/README.md")
        or path.endswith("/install.sh")
        or path.endswith("/version")
    )
    if not should_rewrite:
        return data

    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError:
        return data

    if is_installer_components:
        # The rust-installer script resolves every token in this top-level
        # file as an image directory containing manifest.in. Keep it aligned
        # with rewrite_stage0_tool_member_path: otherwise a repacked archive
        # can carry tippy/manifest.in while install.sh still looks for
        # tippy-preview/manifest.in. Preserve whitespace verbatim because the
        # installer accepts either newline- or space-separated components.
        return re.sub(
            r"\S+",
            lambda match: STAGE0_IMAGE_DIR_RENAMES.get(match.group(0), match.group(0)),
            text,
        ).encode("utf-8")

    text = replace_channel_token(text, source_channel, owned_channel)
    text = text.replace("TEMPLATE_PRODUCT_NAME='Rust'", "TEMPLATE_PRODUCT_NAME='Trust'")
    text = text.replace(
        "rustup toolchain install nightly\nrustup component add rustc-dev --toolchain nightly\n\n",
        "",
    )
    text = text.replace(
        "rustup toolchain install nightly\nrustup component add rustc-dev --toolchain nightly\n",
        "",
    )
    text = text.replace(
        "rustup toolchain install nightly",
        "# Trust stage0 is tracked in this checkout; do not install upstream nightly "
        "for this flow.",
    )
    text = text.replace(
        "rustup component add rustc-dev --toolchain nightly",
        "# Upstream rustc-dev is not required for the Trust bootstrap flow.",
    )
    return text.encode("utf-8")


def repack_owned_tarball(
    src: Path,
    dst: Path,
    *,
    old_filename: str,
    new_filename: str,
    source_channel: str,
    owned_channel: str,
) -> None:
    old_prefix = tarball_prefix(old_filename)
    new_prefix = tarball_prefix(new_filename)

    if new_filename.endswith(".tar.xz"):
        write_mode = "w:xz"
    elif new_filename.endswith(".tar.gz"):
        write_mode = "w:gz"
    else:
        raise ValueError(f"unsupported dist tarball extension: {new_filename}")

    with tarfile.open(src, "r:*") as source_tar:
        validate_tippy_repack_sources(
            source_tar,
            old_prefix=old_prefix,
            new_prefix=new_prefix,
        )

    with tarfile.open(src, "r:*") as source_tar, tarfile.open(dst, write_mode) as output_tar:
        # Rebranding can map more than one historical input leaf to one public
        # output leaf (for example cargo-clippy and tippy). Never let archive
        # order select between conflicting executables: identical aliases may
        # deduplicate, but any content or metadata disagreement is malformed.
        emitted_members: dict[str, tuple[tuple[object, ...], str]] = {}
        for member in source_tar:
            source_member_name = member.name
            fileobj = source_tar.extractfile(member) if member.isfile() else None
            member.name = rewrite_member_path(member.name, old_prefix, new_prefix)
            member.name = rewrite_stage0_tool_member_path(member.name)
            if is_forbidden_stage0_debugger_bin(member.name) or is_stripped_stage0_secondary_alias(
                member.name
            ):
                continue
            if member.linkname and (
                member.linkname == old_prefix or member.linkname.startswith(old_prefix + "/")
            ):
                member.linkname = rewrite_member_path(member.linkname, old_prefix, new_prefix)
                member.linkname = rewrite_stage0_tool_member_path(member.linkname)
            if fileobj is not None:
                data = rewrite_owned_member_bytes(
                    member.name,
                    fileobj.read(),
                    source_channel=source_channel,
                    owned_channel=owned_channel,
                )
                member.size = len(data)
            else:
                data = None
            fingerprint = (
                member.type,
                member.mode,
                member.linkname,
                member.size,
                hashlib.sha256(data).digest() if data is not None else None,
            )
            for emitted_name in (member.name, *stage0_compat_alias_member_paths(member.name)):
                if emitted_name in emitted_members:
                    previous_fingerprint, previous_source = emitted_members[emitted_name]
                    if previous_fingerprint != fingerprint:
                        raise ValueError(
                            "conflicting archive members "
                            f"{previous_source!r} and {source_member_name!r} both normalize "
                            f"to {emitted_name!r}"
                        )
                    continue
                output_member = copy.copy(member)
                output_member.name = emitted_name
                if data is not None:
                    output_member.size = len(data)
                    output_tar.addfile(output_member, io.BytesIO(data))
                else:
                    output_tar.addfile(output_member, fileobj)
                emitted_members[emitted_name] = (fingerprint, source_member_name)

        if new_prefix.startswith("trustc-"):
            version_tail = new_prefix.removeprefix("trustc-")
            channel_marker = f"-{owned_channel}-"
            if channel_marker in version_tail:
                version = version_tail.split(channel_marker, 1)[0] + f"-{owned_channel}"
            else:
                version = version_tail
            for manpage in ("trustc.1", "trustdoc.1"):
                member_name = f"{new_prefix}/trustc/share/man/man1/{manpage}"
                if member_name in emitted_members:
                    continue
                source = repo_root() / "src" / "doc" / "man" / manpage
                text = source.read_text(encoding="utf-8").replace("<INSERT VERSION HERE>", version)
                data = text.encode("utf-8")
                member = tarfile.TarInfo(member_name)
                member.mode = 0o644
                member.size = len(data)
                output_tar.addfile(member, io.BytesIO(data))


def archive_url_keys(archive_format: str) -> tuple[tuple[str, str], ...]:
    if archive_format == "both":
        return (("url", "hash"), ("xz_url", "xz_hash"))
    if archive_format == "gz":
        return (("url", "hash"),)
    if archive_format == "xz":
        return (("xz_url", "xz_hash"),)
    raise ValueError(f"unsupported archive format: {archive_format}")


def rewrite_target_urls(
    target: dict[str, object],
    *,
    input_dist: Path,
    output_date_dir: Path,
    date: str,
    dist_server: str,
    source_channel: str,
    owned_channel: str,
    archive_format: str,
) -> None:
    kept_url_keys = set(archive_url_keys(archive_format))
    for url_key, hash_key in (("url", "hash"), ("xz_url", "xz_hash")):
        if (url_key, hash_key) not in kept_url_keys:
            target.pop(url_key, None)
            target.pop(hash_key, None)
            continue

        value = target.get(url_key)
        if not isinstance(value, str) or not value:
            continue

        old_filename = Path(value).name
        new_filename = stage0_tarball_filename(
            old_filename,
            source_channel=source_channel,
            owned_channel=owned_channel,
        )
        src = source_tarball(input_dist, old_filename, date)
        dst = output_date_dir / new_filename
        repack_owned_tarball(
            src,
            dst,
            old_filename=old_filename,
            new_filename=new_filename,
            source_channel=source_channel,
            owned_channel=owned_channel,
        )

        target[url_key] = dist_url(dist_server, date, new_filename)
        target[hash_key] = sha256_file(dst)


def target_archives_match_target_key(target_key: str, target: dict[str, object]) -> bool:
    if target_key == "*":
        return True

    suffixes = (f"-{target_key}.tar.gz", f"-{target_key}.tar.xz")
    filenames = []
    for url_key in ("url", "xz_url"):
        value = target.get(url_key)
        if isinstance(value, str) and value:
            filenames.append(Path(value).name)

    return not filenames or all(filename.endswith(suffixes) for filename in filenames)


def mark_target_unavailable(target: dict[str, object]) -> None:
    target.clear()
    target["available"] = False


def collect_missing_source_tarballs(
    packages: dict[str, object],
    *,
    input_dist: Path,
    date: str,
    archive_format: str,
    materialized_components: frozenset[str] | None = None,
    strict_target_archives: bool = False,
) -> tuple[str, ...]:
    missing: list[str] = []
    seen: set[str] = set()

    for component, package in packages.items():
        if (
            materialized_components is not None
            and component not in materialized_components
        ):
            continue
        if not isinstance(package, dict):
            continue
        targets = package.get("target")
        if not isinstance(targets, dict):
            continue
        for target_key, target in targets.items():
            if not isinstance(target_key, str) or not isinstance(target, dict):
                continue
            if strict_target_archives and not target_archives_match_target_key(
                target_key,
                target,
            ):
                continue
            for url_key, _hash_key in archive_url_keys(archive_format):
                value = target.get(url_key)
                if not isinstance(value, str) or not value:
                    continue
                filename = Path(value).name
                if filename in seen:
                    continue
                if not any(
                    candidate.is_file()
                    for candidate in source_tarball_candidates(input_dist, filename, date)
                ):
                    seen.add(filename)
                    missing.append(filename)

    return tuple(sorted(missing))


def archive_records(
    packages: dict[str, object],
    *,
    input_dist: Path,
    date: str,
    archive_format: str,
    materialized_components: frozenset[str] | None = None,
    strict_target_archives: bool = False,
) -> tuple[tuple[str, str, str, str, str, Path], ...]:
    records: list[tuple[str, str, str, str, str, Path]] = []

    for component, package in packages.items():
        if materialized_components is not None and component not in materialized_components:
            continue
        if not isinstance(package, dict):
            continue
        targets = package.get("target")
        if not isinstance(targets, dict):
            continue
        for target_key, target in targets.items():
            if not isinstance(target_key, str) or not isinstance(target, dict):
                continue
            if strict_target_archives and not target_archives_match_target_key(
                target_key,
                target,
            ):
                continue
            for url_key, hash_key in archive_url_keys(archive_format):
                value = target.get(url_key)
                if not isinstance(value, str) or not value:
                    continue
                filename = Path(value).name
                records.append(
                    (
                        component,
                        target_key,
                        url_key,
                        hash_key,
                        filename,
                        source_tarball(input_dist, filename, date),
                    )
                )

    return tuple(records)


def archive_component_prefix(component: str) -> str:
    return stage0_component_name(component).removesuffix("-preview")


def archive_stem_has_channel(stem: str, channel: str) -> bool:
    marker = f"-{channel}"
    return stem.endswith(marker) or f"{marker}-" in stem


def validate_archive_entrypoints(
    component: str,
    filename: str,
    path: Path,
) -> tuple[str, ...]:
    contract_component = archive_component_prefix(component)
    required = REQUIRED_ARCHIVE_ENTRYPOINTS.get(contract_component)
    forbidden = FORBIDDEN_ARCHIVE_ENTRYPOINTS.get(contract_component, ())
    if not required and not forbidden:
        return ()

    prefix = tarball_prefix(filename)
    try:
        with tarfile.open(path, "r:*") as archive:
            members = set()
            for member in archive.getmembers():
                if member.name == prefix:
                    continue
                if member.name.startswith(prefix + "/"):
                    rel = member.name[len(prefix) + 1 :]
                    # Normalize the producer `-preview` image dir (e.g.
                    # trust-analyzer-preview/) to its canonical stage0 dir the same
                    # way materialization does, so the contract's canonical
                    # trust-<tool>/bin/<tool> paths match. Only the leading image
                    # dir is remapped; leaf bin names stay so the dual trust-/rust-
                    # compat entrypoints remain distinct.
                    head, sep, tail = rel.partition("/")
                    if sep:
                        rel = STAGE0_IMAGE_DIR_RENAMES.get(head, head) + sep + tail
                    # Trust: forbidden stock secondary aliases are stripped by
                    # `materialize_stage0_archive`, so they are absent from the
                    # emitted seed — do not count them as present here (that is
                    # what makes the FORBIDDEN check pass and keeps the contract
                    # consistent with the materialized output).
                    if is_stripped_stage0_secondary_alias(rel):
                        continue
                    members.add(rel)
    except tarfile.TarError as exc:
        return (f"{filename} is not a readable tar archive: {exc}",)

    errors: list[str] = []
    for entrypoint in required or ():
        if entrypoint not in members:
            errors.append(f"{filename} is missing Trust entrypoint {entrypoint}")
    for entrypoint in forbidden:
        if entrypoint in members:
            errors.append(f"{filename} contains forbidden secondary entrypoint {entrypoint}")
    return tuple(errors)


def collect_archive_contract_errors(
    packages: dict[str, object],
    *,
    input_dist: Path,
    date: str,
    archive_format: str,
    source_channel: str,
    owned_channel: str,
    materialized_components: frozenset[str] | None = None,
    strict_target_archives: bool = False,
    require_owned_archive_names: bool = False,
) -> tuple[str, ...]:
    errors: list[str] = []
    checked_payloads: set[tuple[str, str]] = set()

    for (
        component,
        target_key,
        url_key,
        hash_key,
        filename,
        path,
    ) in archive_records(
        packages,
        input_dist=input_dist,
        date=date,
        archive_format=archive_format,
        materialized_components=materialized_components,
        strict_target_archives=strict_target_archives,
    ):
        if require_owned_archive_names:
            rewritten = stage0_tarball_filename(
                filename,
                source_channel=source_channel,
                owned_channel=owned_channel,
            )
            if rewritten != filename:
                errors.append(
                    f"{component} target {target_key} {url_key} uses inherited "
                    f"archive name {filename}; expected Trust-owned {rewritten}"
                )
            expected_prefix = archive_component_prefix(component)
            if not filename.startswith(expected_prefix + "-"):
                errors.append(
                    f"{component} target {target_key} {url_key} uses archive "
                    f"name {filename}; expected prefix {expected_prefix}-"
                )
            if not archive_stem_has_channel(tarball_prefix(filename), owned_channel):
                errors.append(
                    f"{component} target {target_key} {url_key} archive "
                    f"{filename} is not on the {owned_channel!r} channel"
                )

        target = packages[component]["target"][target_key]
        assert isinstance(target, dict)
        digest = target.get(hash_key)
        if not isinstance(digest, str) or not digest:
            errors.append(f"{component} target {target_key} {url_key} is missing {hash_key}")
        elif SHA256_PATTERN.fullmatch(digest) is None:
            errors.append(
                f"{component} target {target_key} {url_key} has invalid {hash_key}: {digest!r}"
            )
        else:
            actual = sha256_file(path)
            if actual != digest:
                errors.append(
                    f"{component} target {target_key} {url_key} checksum mismatch "
                    f"for {filename}: manifest {digest}, file {actual}"
                )

        payload_key = (component, filename)
        if require_owned_archive_names and payload_key not in checked_payloads:
            checked_payloads.add(payload_key)
            errors.extend(validate_archive_entrypoints(component, filename, path))

    return tuple(errors)


def archive_contract_summary(
    packages: dict[str, object],
    *,
    input_dist: Path,
    date: str,
    archive_format: str,
    materialized_components: frozenset[str] | None = None,
    strict_target_archives: bool = False,
) -> dict[str, int]:
    records = archive_records(
        packages,
        input_dist=input_dist,
        date=date,
        archive_format=archive_format,
        materialized_components=materialized_components,
        strict_target_archives=strict_target_archives,
    )
    return {
        "archive_references": len(records),
        "archive_files": len({record[4] for record in records}),
        "entrypoint_archives": len(
            {
                (component, filename)
                for component, _target_key, _url_key, _hash_key, filename, _path in records
                if component in REQUIRED_ARCHIVE_ENTRYPOINTS
            }
        ),
    }


def archive_contract_filenames(
    packages: dict[str, object],
    *,
    input_dist: Path,
    date: str,
    archive_format: str,
    materialized_components: frozenset[str] | None = None,
    strict_target_archives: bool = False,
) -> tuple[str, ...]:
    records = archive_records(
        packages,
        input_dist=input_dist,
        date=date,
        archive_format=archive_format,
        materialized_components=materialized_components,
        strict_target_archives=strict_target_archives,
    )
    return tuple(sorted({record[4] for record in records}))


def available_component_filenames(
    manifest: dict[str, object],
    *,
    component_names: tuple[str, ...],
    url_key: str,
    source_channel: str,
    owned_channel: str,
) -> dict[str, str]:
    packages = manifest.get("pkg")
    if not isinstance(packages, dict):
        return {}

    filenames: dict[str, str] = {}
    for component in component_names:
        package = packages.get(component)
        if not isinstance(package, dict):
            continue
        targets = package.get("target")
        if not isinstance(targets, dict):
            continue
        for target_key, target in targets.items():
            if not isinstance(target_key, str) or target_key == "*" or not isinstance(target, dict):
                continue
            if target.get("available") is False:
                continue
            url = target.get(url_key)
            if isinstance(url, str) and url:
                filenames[target_key] = stage0_tarball_filename(
                    Path(url).name,
                    source_channel=source_channel,
                    owned_channel=owned_channel,
                )
    return dict(sorted(filenames.items()))


def validate_rustc_dev_artifact_handoff(
    manifest: dict[str, object],
    *,
    output_root: Path | None,
    git_commit_hash: str,
    source_channel: str,
    owned_channel: str,
) -> tuple[Path, ...]:
    rustc_targets = set(
        available_component_filenames(
            manifest,
            component_names=("trustc", "rustc"),
            url_key="xz_url",
            source_channel=source_channel,
            owned_channel=owned_channel,
        )
    )
    if not rustc_targets:
        rustc_targets = set(
            available_component_filenames(
                manifest,
                component_names=("trustc", "rustc"),
                url_key="url",
                source_channel=source_channel,
                owned_channel=owned_channel,
            )
        )

    trustc_dev_filenames = available_component_filenames(
        manifest,
        component_names=("trustc-dev",),
        url_key="xz_url",
        source_channel=source_channel,
        owned_channel=owned_channel,
    )

    errors: list[str] = []
    if not trustc_dev_filenames:
        errors.append("channel manifest has no available trustc-dev xz target")

    for target in sorted(rustc_targets - set(trustc_dev_filenames)):
        errors.append(f"trustc-dev xz target is missing for trustc host target {target}")

    expected_paths: list[Path] = []
    for target, filename in trustc_dev_filenames.items():
        if rustc_targets and target not in rustc_targets:
            continue
        if not filename.startswith("trustc-dev-"):
            errors.append(
                f"trustc-dev target {target} uses non-canonical archive name {filename}"
            )
        if output_root is None:
            continue
        for root in STAGE0_ARTIFACT_ROOTS:
            artifact = output_root / root / git_commit_hash / filename
            expected_paths.append(artifact)
            if not artifact.is_file():
                errors.append(f"missing {root} trustc-dev artifact for {target}: {artifact}")

    if errors:
        details = "\n  - ".join(errors)
        examples = "\n  ".join(str(path) for path in expected_paths[:4])
        if examples:
            examples = "\n\nExpected local artifact path examples:\n  " + examples
        raise ValueError(
            "trustc-dev artifact handoff preflight failed:\n"
            f"  - {details}\n\n"
            "Action: materialize trustc-dev .tar.xz artifacts for the same "
            "stage0 seed commit and host targets, then place or symlink them "
            "under both Trust artifact roots before rerunning prepare.py."
            f"{examples}"
        )

    return tuple(expected_paths)


def file_contains(path: Path, pattern: str) -> bool:
    try:
        return pattern in path.read_text(encoding="utf-8")
    except UnicodeDecodeError:
        return False


def _rust_tokens(source: str) -> tuple[str, ...] | None:
    """Tokenize enough Rust to authenticate a small, exact method body.

    Comments and string/character contents must not become executable-looking
    tokens: producer registration is a fail-closed source audit, so a decoy in
    either must never satisfy it. This is deliberately not a general Rust
    parser; malformed or unterminated lexical constructs return ``None``.
    """

    tokens: list[str] = []
    index = 0
    length = len(source)
    while index < length:
        char = source[index]
        if char.isspace():
            index += 1
            continue

        if source.startswith("//", index):
            newline = source.find("\n", index + 2)
            index = length if newline == -1 else newline + 1
            continue
        if source.startswith("/*", index):
            depth = 1
            index += 2
            while index < length and depth:
                if source.startswith("/*", index):
                    depth += 1
                    index += 2
                elif source.startswith("*/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
            if depth:
                return None
            continue

        raw_prefix = None
        for prefix in ("br", "cr", "r"):
            if not source.startswith(prefix, index):
                continue
            cursor = index + len(prefix)
            while cursor < length and source[cursor] == "#":
                cursor += 1
            if cursor < length and source[cursor] == '"':
                raw_prefix = (cursor - index - len(prefix), cursor)
                break
        if raw_prefix is not None:
            hashes, opening_quote = raw_prefix
            terminator = '"' + "#" * hashes
            end = source.find(terminator, opening_quote + 1)
            if end == -1:
                return None
            end += len(terminator)
            tokens.append(source[index:end])
            index = end
            continue

        string_prefix = (
            1
            if char in {"b", "c"}
            and index + 1 < length
            and source[index + 1] == '"'
            else 0
        )
        if char == '"' or string_prefix:
            start = index
            index += string_prefix + 1
            while index < length:
                if source[index] == "\\":
                    index += 2
                    continue
                if source[index] == '"':
                    index += 1
                    tokens.append(source[start:index])
                    break
                index += 1
            else:
                return None
            continue

        if char == "'":
            # Preserve lifetimes as punctuation + identifier, but collapse
            # character literals so braces/comment markers inside them cannot
            # perturb structural matching.
            if index + 2 < length and source[index + 2] == "'":
                tokens.append(source[index : index + 3])
                index += 3
                continue
            if (
                index + 3 < length
                and source[index + 1] == "\\"
                and source[index + 3] == "'"
            ):
                tokens.append(source[index : index + 4])
                index += 4
                continue

        if char.isalpha() or char == "_":
            end = index + 1
            while end < length and (source[end].isalnum() or source[end] == "_"):
                end += 1
            tokens.append(source[index:end])
            index = end
            continue

        tokens.append(char)
        index += 1

    return tuple(tokens)


def _matching_rust_delimiter(tokens: tuple[str, ...], opening: int) -> int | None:
    pairs = {"(": ")", "[": "]", "{": "}"}
    if opening >= len(tokens) or tokens[opening] not in pairs:
        return None
    stack = [pairs[tokens[opening]]]
    for index in range(opening + 1, len(tokens)):
        token = tokens[index]
        if token in pairs:
            stack.append(pairs[token])
        elif token in pairs.values():
            if token != stack[-1]:
                return None
            stack.pop()
            if not stack:
                return index
    return None


def _rust_delimiter_depths(tokens: tuple[str, ...]) -> tuple[int, ...] | None:
    pairs = {"(": ")", "[": "]", "{": "}"}
    closing = set(pairs.values())
    stack: list[str] = []
    depths: list[int] = []
    for token in tokens:
        depths.append(len(stack))
        if token in pairs:
            stack.append(pairs[token])
        elif token in closing:
            if not stack or token != stack[-1]:
                return None
            stack.pop()
    return None if stack else tuple(depths)


def _rust_comma_separated_items(
    tokens: tuple[str, ...],
) -> tuple[tuple[str, ...], ...] | None:
    pairs = {"(": ")", "[": "]", "{": "}"}
    closing = set(pairs.values())
    stack: list[str] = []
    items: list[tuple[str, ...]] = []
    start = 0
    for index, token in enumerate(tokens):
        if token in pairs:
            stack.append(pairs[token])
        elif token in closing:
            if not stack or token != stack[-1]:
                return None
            stack.pop()
        elif token == "," and not stack:
            item = tokens[start:index]
            if not item:
                return None
            items.append(item)
            start = index + 1
    if stack:
        return None
    final_item = tokens[start:]
    if final_item:
        items.append(final_item)
    return tuple(items)


def _rust_is_simple_path(tokens: tuple[str, ...]) -> bool:
    if not tokens or not (tokens[0][0].isalpha() or tokens[0][0] == "_"):
        return False
    cursor = 1
    while cursor < len(tokens):
        if cursor + 2 >= len(tokens) or tokens[cursor : cursor + 2] != (":", ":"):
            return False
        segment = tokens[cursor + 2]
        if not segment or not (segment[0].isalpha() or segment[0] == "_"):
            return False
        cursor += 3
    return True


def rust_step_returns_exact_should_run(
    path: Path,
    step_type: str,
    expression: str,
) -> bool:
    """Require one Step impl whose should_run body is exactly ``expression``."""

    try:
        source_tokens = _rust_tokens(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError):
        return False
    expected_tokens = _rust_tokens(expression)
    if source_tokens is None or expected_tokens is None:
        return False
    delimiter_depths = _rust_delimiter_depths(source_tokens)
    if delimiter_depths is None:
        return False

    impl_prefix = ("impl", "Step", "for", step_type, "{")
    impl_blocks: list[tuple[int, int]] = []
    for index in range(len(source_tokens) - len(impl_prefix) + 1):
        if source_tokens[index : index + len(impl_prefix)] != impl_prefix:
            continue
        # The producer Step must be a real root item, not tokens nested in a
        # macro, function, constant, or cfg-disabled attribute. The previous
        # root token is an item terminator in the concrete source form audited
        # here; fail closed on qualifiers or attached attributes.
        if delimiter_depths[index] != 0 or (
            index > 0 and source_tokens[index - 1] not in {"}", ";"}
        ):
            continue
        opening = index + len(impl_prefix) - 1
        closing = _matching_rust_delimiter(source_tokens, opening)
        if closing is not None:
            impl_blocks.append((opening, closing))
    if len(impl_blocks) != 1:
        return False

    impl_open, impl_close = impl_blocks[0]
    method_prefix = _rust_tokens(
        "fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {"
    )
    assert method_prefix is not None
    method_blocks: list[tuple[int, int]] = []
    for index in range(impl_open + 1, impl_close - len(method_prefix) + 1):
        if source_tokens[index : index + len(method_prefix)] != method_prefix:
            continue
        if delimiter_depths[index] != 1 or source_tokens[index - 1] not in {
            "{",
            "}",
            ";",
        }:
            continue
        opening = index + len(method_prefix) - 1
        closing = _matching_rust_delimiter(source_tokens, opening)
        if (
            delimiter_depths[opening] != 1
            or closing is None
            or closing > impl_close
        ):
            return False
        method_blocks.append((opening, closing))
    if len(method_blocks) != 1:
        return False

    method_open, method_close = method_blocks[0]
    return source_tokens[method_open + 1 : method_close] == expected_tokens


def rust_kind_describes_exact_step(path: Path, kind: str, step_path: str) -> bool:
    """Require an exact step path in Builder's returned ``Kind`` match."""

    try:
        source_tokens = _rust_tokens(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError):
        return False
    step_tokens = _rust_tokens(step_path)
    if source_tokens is None or step_tokens is None:
        return False
    delimiter_depths = _rust_delimiter_depths(source_tokens)
    if delimiter_depths is None or not _rust_is_simple_path(step_tokens):
        return False

    builder_impl_prefix = _rust_tokens("impl<'a> Builder<'a> {")
    assert builder_impl_prefix is not None
    builder_impls: list[tuple[int, int]] = []
    for index in range(
        len(source_tokens) - len(builder_impl_prefix) + 1
    ):
        if (
            source_tokens[index : index + len(builder_impl_prefix)]
            != builder_impl_prefix
            or delimiter_depths[index] != 0
        ):
            continue
        if index > 0 and source_tokens[index - 1] not in {"}", ";"}:
            continue
        opening = index + len(builder_impl_prefix) - 1
        closing = _matching_rust_delimiter(source_tokens, opening)
        if closing is not None:
            builder_impls.append((opening, closing))
    if len(builder_impls) != 1:
        return False

    impl_open, impl_close = builder_impls[0]
    method_prefix = _rust_tokens(
        "fn get_step_descriptions(kind: Kind) -> Vec<StepDescription> {"
    )
    assert method_prefix is not None
    method_blocks: list[tuple[int, int]] = []
    for index in range(impl_open + 1, impl_close - len(method_prefix) + 1):
        if source_tokens[index : index + len(method_prefix)] != method_prefix:
            continue
        if delimiter_depths[index] != 1 or source_tokens[index - 1] not in {
            "{",
            "}",
            ";",
        }:
            continue
        opening = index + len(method_prefix) - 1
        closing = _matching_rust_delimiter(source_tokens, opening)
        if closing is not None and closing <= impl_close:
            method_blocks.append((opening, closing))
    if len(method_blocks) != 1:
        return False

    method_open, method_close = method_blocks[0]
    match_prefix = _rust_tokens("match kind {")
    assert match_prefix is not None
    match_blocks: list[tuple[int, int]] = []
    for index in range(method_open + 1, method_close - len(match_prefix) + 1):
        if source_tokens[index : index + len(match_prefix)] != match_prefix:
            continue
        if delimiter_depths[index] != 2 or source_tokens[index - 1] not in {
            "{",
            "}",
            ";",
        }:
            continue
        opening = index + len(match_prefix) - 1
        closing = _matching_rust_delimiter(source_tokens, opening)
        if closing == method_close - 1:
            match_blocks.append((opening, closing))
    if len(match_blocks) != 1:
        return False

    match_open, match_close = match_blocks[0]
    prefix_tokens = _rust_tokens(f"Kind::{kind} => describe!(")
    assert prefix_tokens is not None
    describe_blocks: list[tuple[int, int]] = []
    for index in range(match_open + 1, match_close - len(prefix_tokens) + 1):
        if source_tokens[index : index + len(prefix_tokens)] != prefix_tokens:
            continue
        if delimiter_depths[index] != 3 or source_tokens[index - 1] not in {
            "{",
            ",",
        }:
            continue
        opening = index + len(prefix_tokens) - 1
        closing = _matching_rust_delimiter(source_tokens, opening)
        if (
            closing is not None
            and closing + 1 < match_close
            and source_tokens[closing + 1] == ","
            and delimiter_depths[closing + 1] == 3
        ):
            describe_blocks.append((opening, closing))
    if len(describe_blocks) != 1:
        return False

    opening, closing = describe_blocks[0]
    entries = source_tokens[opening + 1 : closing]
    items = _rust_comma_separated_items(entries)
    return (
        items is not None
        and all(_rust_is_simple_path(item) for item in items)
        and items.count(step_tokens) == 1
    )


def stage0_key_values(stage0_path: Path) -> dict[str, str]:
    values: dict[str, str] = {}
    for raw_line in stage0_path.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, value = line.split("=", 1)
        values[key.strip()] = value.strip()
    return values


def stage0_payload_entries(values: dict[str, str]) -> tuple[tuple[str, str], ...]:
    return tuple(
        sorted(
            (key, value)
            for key, value in values.items()
            if key.startswith("dist/") and key.endswith(STAGE0_ARCHIVE_SUFFIXES)
        )
    )


def manifest_target_is_built(entry: object) -> bool:
    """A channel-manifest target carries a payload iff it has a non-empty
    ``xz_url`` (unbuilt hosts are recorded as ``{available = false}`` with no url)."""
    return (
        isinstance(entry, dict)
        and isinstance(entry.get("xz_url"), str)
        and bool(entry.get("xz_url"))
    )


def _manifest_release_identity(manifest: dict[str, object]) -> tuple[object, object]:
    date = manifest.get("date")
    if isinstance(date, dt.date):
        date = date.isoformat()
    trust = manifest.get("pkg", {})
    trust = trust.get("trust") if isinstance(trust, dict) else None
    commit = trust.get("git_commit_hash") if isinstance(trust, dict) else None
    return date, commit


def merge_existing_manifest_targets(
    manifest: dict[str, object], existing_manifest_path: Path
) -> int:
    """Union the *built* per-triple targets of an already-published channel
    manifest into this run's ``manifest`` in place, for a dual-host seed.

    For every triple the existing manifest built (``xz_url`` present) that this
    run did not build, adopt the existing target entry; triples this run built are
    kept fresh. Because the whole seed (payload checksums, admission record,
    src/stage0 pins, and the manifest hash) is derived downstream from this single
    ``manifest`` dict, unioning here makes all of them dual-host by construction —
    which is exactly what the ``stage0-metadata-coherence-smoke`` bijection gate
    requires. Returns the number of foreign targets adopted.

    Refuses if the existing manifest is a *different* release (top-level ``date``
    or ``pkg.trust.git_commit_hash`` differ): bootstrap resolves a host's payload
    under the single ``compiler_date`` and would not find it under another date.
    """
    existing = tomllib.loads(existing_manifest_path.read_text(encoding="utf-8"))
    (new_date, new_commit) = _manifest_release_identity(manifest)
    (old_date, old_commit) = _manifest_release_identity(existing)
    for label, old, new in (
        ("date", old_date, new_date),
        ("git_commit_hash", old_commit, new_commit),
    ):
        if old is not None and new is not None and old != new:
            raise ValueError(
                f"--merge-existing: existing manifest {existing_manifest_path} has "
                f"{label} {old!r} but this run has {new!r}; both hosts' seeds must be "
                f"minted from the same committed source (identical date and commit)"
            )
    existing_pkgs = existing.get("pkg")
    packages = manifest.get("pkg")
    if not isinstance(existing_pkgs, dict) or not isinstance(packages, dict):
        return 0
    adopted = 0
    for component, package in packages.items():
        if not isinstance(package, dict):
            continue
        targets = package.get("target")
        existing_pkg = existing_pkgs.get(component)
        existing_targets = existing_pkg.get("target") if isinstance(existing_pkg, dict) else None
        if not isinstance(targets, dict) or not isinstance(existing_targets, dict):
            continue
        for triple, existing_entry in existing_targets.items():
            if not manifest_target_is_built(existing_entry):
                continue
            if manifest_target_is_built(targets.get(triple)):
                continue  # this run built the same triple -> keep the fresh entry
            targets[triple] = existing_entry
            adopted += 1
    return adopted


def local_stage0_dist_root(root: Path, dist_server: str) -> Path | None:
    if not dist_server.startswith("file://"):
        return None

    local = dist_server[len("file://") :]
    local = local.replace(TRUST_ROOT_TOKEN, str(root))
    local = local.replace("$PWD", str(root))
    return Path(local)


def producer_stage0_admission_report(
    *,
    dist_root: Path | None,
    entries: tuple[tuple[str, str], ...],
) -> dict[str, object]:
    path = dist_root / STAGE0_ADMISSION_FILENAME if dist_root is not None else None
    report: dict[str, object] = {
        "schema": STAGE0_ADMISSION_SCHEMA,
        "status": "blocked",
        "path": str(path) if path is not None else None,
        "required_payloads": len(entries),
        "admitted_payloads": 0,
        "findings": [],
        "missing_payloads": [],
        "checksum_mismatches": [],
        "extra_payloads": [],
    }
    findings = report["findings"]
    assert isinstance(findings, list)

    if dist_root is None:
        findings.append("non-local dist_server roots cannot be admitted by this local preflight")
        return report
    if path is None or not path.is_file():
        findings.append(
            f"missing internal admission manifest at dist root: {STAGE0_ADMISSION_FILENAME}"
        )
        return report

    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        findings.append(f"internal admission manifest is unreadable: {exc}")
        return report
    if not isinstance(data, dict):
        findings.append("internal admission manifest must be a JSON object")
        return report

    if data.get("schema") != STAGE0_ADMISSION_SCHEMA:
        findings.append(
            "internal admission manifest has unexpected schema: "
            f"{data.get('schema')!r}"
        )
    if data.get("admission") != "internal":
        findings.append("internal admission manifest must set admission=internal")
    if data.get("public_upload") is not False:
        findings.append("internal admission manifest must set public_upload=false")
    decision = data.get("promotion_decision")
    if decision not in ("admit-internal", "hold-internal"):
        findings.append(
            "internal admission manifest must set promotion_decision to "
            "admit-internal or hold-internal"
        )
    if decision == "hold-internal":
        findings.append("internal admission manifest is hold-internal, not admitted")

    payloads = data.get("payloads")
    if not isinstance(payloads, list):
        findings.append("internal admission manifest must contain a payloads list")
        payloads = []

    admitted: dict[str, str] = {}
    for item in payloads:
        if not isinstance(item, dict):
            findings.append("internal admission payload entries must be JSON objects")
            continue
        rel = item.get("relative_path")
        digest = item.get("sha256")
        if not isinstance(rel, str) or not isinstance(digest, str):
            findings.append("internal admission payload entries need relative_path and sha256")
            continue
        admitted[rel] = digest

    report["admitted_payloads"] = len(admitted)
    required = dict(entries)
    missing = sorted(set(required) - set(admitted))
    extra = sorted(set(admitted) - set(required))
    mismatched = [
        {
            "relative_path": rel,
            "expected_sha256": required[rel],
            "admitted_sha256": admitted[rel],
        }
        for rel in sorted(set(required) & set(admitted))
        if admitted[rel] != required[rel]
    ]
    report["missing_payloads"] = missing
    report["checksum_mismatches"] = mismatched
    report["extra_payloads"] = extra
    if missing:
        findings.append(
            f"internal admission manifest is missing {len(missing)} stage0 payload pin(s)"
        )
    if mismatched:
        findings.append(
            "internal admission manifest has checksum pin(s) that differ from src/stage0"
        )
    if extra:
        findings.append(
            f"internal admission manifest contains {len(extra)} payload pin(s) not in src/stage0"
        )

    if not findings:
        report["status"] = "ready"
    return report


def producer_stage0_payload_preflight_report(root: Path) -> dict[str, object]:
    stage0_path = root / "src" / "stage0"
    dist_server = ""
    dist_server_source = "unset"
    payload_mode = "<unavailable>"
    dist_root: Path | None = None
    values: dict[str, str] = {}
    entries: tuple[tuple[str, str], ...] = ()
    payloads: list[dict[str, str | None]] = []
    missing: list[dict[str, str]] = []
    mismatched: list[dict[str, str]] = []
    invalid: list[dict[str, str]] = []
    errors: list[str] = []

    if not stage0_path.is_file():
        errors.append("missing Trust stage0 metadata file: src/stage0")
    else:
        values = stage0_key_values(stage0_path)
        env_dist_server = os.environ.get("TRUST_DIST_SERVER", "")
        if env_dist_server:
            dist_server = env_dist_server
            dist_server_source = "TRUST_DIST_SERVER"
        else:
            dist_server = values.get("dist_server", "")
            dist_server_source = "src/stage0" if dist_server else "unset"
        payload_mode = values.get("dist_payload_mode", "<unset>")
        entries = stage0_payload_entries(values)
        if not dist_server:
            errors.append("src/stage0 does not define a Trust stage0 dist_server")
        if not entries:
            errors.append("src/stage0 has no checksum-pinned dist archive payload entries")
        for rel, expected in entries:
            if not SHA256_PATTERN.fullmatch(expected):
                invalid.append({"relative_path": rel, "value": expected})

    if dist_server:
        dist_root = local_stage0_dist_root(root, dist_server)
        if dist_root is not None:
            for rel, expected in entries:
                path = dist_root / rel
                payloads.append(
                    {
                        "relative_path": rel,
                        "expected_sha256": expected,
                        "checked_path": str(path),
                    }
                )
                if not path.is_file():
                    missing.append(
                        {
                            "relative_path": rel,
                            "expected_sha256": expected,
                            "checked_path": str(path),
                        }
                    )
                    continue
                if SHA256_PATTERN.fullmatch(expected):
                    actual = sha256_file(path)
                    if actual != expected:
                        mismatched.append(
                            {
                                "relative_path": rel,
                                "expected_sha256": expected,
                                "actual_sha256": actual,
                                "checked_path": str(path),
                            }
                        )
        else:
            payloads.extend(
                {
                    "relative_path": rel,
                    "expected_sha256": expected,
                    "checked_path": None,
                }
                for rel, expected in entries
            )

    admission = producer_stage0_admission_report(dist_root=dist_root, entries=entries)
    admission_blocked = admission["status"] != "ready"
    blocked = bool(errors or missing or mismatched or invalid)
    if entries and not missing and not mismatched and not invalid:
        blocked = blocked or admission_blocked
    seed_commit = (
        values.get("compiler_git_commit_hash")
        or values.get("rustfmt_git_commit_hash")
        or "<seed-commit-that-produced-input-dist>"
    )
    source_channel = values.get("compiler_dist_channel") or "trust"
    materialize_command = (
        "python3",
        "src/tools/trust-stage0-dist/prepare.py",
        "--input-dist",
        "build/dist",
        "--source-channel",
        source_channel,
        "--owned-channel",
        "trust",
        "--archive-format",
        "xz",
        "--stage0-seed-only",
        "--metadata-only-checkout",
        "--git-commit-hash",
        seed_commit,
        "--output-root",
        "bootstrap/trust-stage0",
        "--stage0-output",
        "build/stage0-materialization/src-stage0",
    )
    existing_root_check = (
        "TRUST_DIST_SERVER=file:///ABS/PATH/TO/TRUST-STAGE0 "
        "python3 src/tools/trust-stage0-dist/prepare.py "
        "--check-producer-stage0-payloads-only"
    )
    return {
        "schema": "trust.stage0-producer-payload-preflight.v1",
        "status": "blocked" if blocked else "ready",
        "repo_root": str(root),
        "stage0": str(stage0_path),
        "dist_server": dist_server or None,
        "dist_server_source": dist_server_source,
        "dist_payload_mode": payload_mode,
        "resolved_dist_root": str(dist_root) if dist_root is not None else None,
        "local_payload_check": dist_root is not None,
        "stage0_payload_refs": len(entries),
        "payloads": payloads,
        "errors": errors,
        "invalid_payload_checksums": invalid,
        "missing_payloads": missing,
        "checksum_mismatches": mismatched,
        "internal_admission": admission,
        "actions": {
            "materialize_command": list(materialize_command),
            "existing_root_check": existing_root_check,
        },
        "producer_dry_run": shell_command(STAGE0_DIST_PRODUCER_DRY_RUN_COMMAND),
        "producer_dist": shell_command(STAGE0_DIST_PRODUCER_COMMAND),
        "writes": "none",
    }


def producer_stage0_payload_preflight_report_lines(root: Path) -> tuple[bool, list[str]]:
    report = producer_stage0_payload_preflight_report(root)
    blocked = report["status"] == "blocked"
    lines = [
        f"producer_stage0_payload_preflight: {report['status']}",
        f"repo_root:            {report['repo_root']}",
        f"stage0:               {report['stage0']}",
        f"dist_server:          {report['dist_server'] or '<unset>'}",
        f"dist_payload_mode:    {report['dist_payload_mode']}",
        (
            f"resolved_dist_root:   {report['resolved_dist_root']}"
            if report["resolved_dist_root"] is not None
            else "resolved_dist_root:   <non-local; not checked>"
        ),
        f"stage0_payload_refs:  {report['stage0_payload_refs']}",
    ]
    errors = report["errors"]
    if errors:
        lines.append("errors:")
        lines.extend(f"  - {error}" for error in errors)
    invalid = report["invalid_payload_checksums"]
    if invalid:
        lines.append("invalid stage0 payload checksum pin(s):")
        lines.extend(
            f"  - {item['relative_path']}={item['value']}" for item in invalid
        )
    missing = report["missing_payloads"]
    if missing:
        lines.append("missing checksum-pinned stage0 payload(s):")
        lines.extend(f"  - {item['relative_path']}" for item in missing)
    mismatched = report["checksum_mismatches"]
    if mismatched:
        lines.append("checksum mismatch in stage0 payload(s):")
        lines.extend(
            "  - {relative_path} expected={expected_sha256} actual={actual_sha256}".format(
                **item
            )
            for item in mismatched
        )
    admission = report["internal_admission"]
    assert isinstance(admission, dict)
    lines.append(f"internal_admission: {admission['status']}")
    if admission.get("path") is not None:
        lines.append(f"internal_admission_path: {admission['path']}")
    admission_findings = admission.get("findings")
    if isinstance(admission_findings, list) and admission_findings:
        lines.append("internal admission findings:")
        lines.extend(f"  - {finding}" for finding in admission_findings)
    if blocked:
        actions = report["actions"]
        assert isinstance(actions, dict)
        materialize_command = actions["materialize_command"]
        assert isinstance(materialize_command, list)
        lines.extend(
            [
                "Action: materialize the Trust-owned stage0 artifact root or set",
                "TRUST_DIST_SERVER to an admitted Trust artifact root before running",
                "the producer dry-run or full producer dist command.",
                "stage0_materialize_command: "
                + shell_command(tuple(str(part) for part in materialize_command)),
                f"stage0_existing_root_check: {actions['existing_root_check']}",
            ]
        )
    lines.extend(
        [
            f"producer_dry_run:    {report['producer_dry_run']}",
            f"producer_dist:       {report['producer_dist']}",
            f"writes:              {report['writes']}",
        ]
    )
    return blocked, lines


def producer_command_preflight_errors(root: Path) -> tuple[str, ...]:
    errors: list[str] = []
    required_files = (
        Path("x.py"),
        Path("src/bootstrap/src/core/config/flags.rs"),
        Path("src/bootstrap/src/core/builder/mod.rs"),
        Path("src/bootstrap/src/core/build_steps/dist.rs"),
        Path("bootstrap.example.toml"),
        Path("src/bootstrap/defaults/bootstrap.dist.toml"),
    )
    for relative in required_files:
        path = root / relative
        if not path.is_file():
            errors.append(f"missing producer preflight input: {relative}")

    flags = root / "src/bootstrap/src/core/config/flags.rs"
    if flags.is_file() and not file_contains(flags, "pub dry_run: bool"):
        errors.append("bootstrap CLI no longer exposes the global --dry-run flag")

    dist_steps = root / "src/bootstrap/src/core/build_steps/dist.rs"
    builder = root / "src/bootstrap/src/core/builder/mod.rs"
    for alias, (step_pattern, builder_pattern) in STAGE0_DIST_PRODUCER_ALIAS_PATTERNS.items():
        exact_should_run = STAGE0_DIST_PRODUCER_EXACT_SHOULD_RUN.get(alias)
        if not dist_steps.is_file():
            step_registered = False
        elif exact_should_run is None:
            step_registered = file_contains(dist_steps, step_pattern)
        else:
            step_type, expression = exact_should_run
            step_registered = rust_step_returns_exact_should_run(
                dist_steps,
                step_type,
                expression,
            )
        if dist_steps.is_file() and not step_registered:
            errors.append(f"stage0 dist producer alias is not registered for x.py dist: {alias}")
        if builder.is_file() and not rust_kind_describes_exact_step(
            builder,
            "Dist",
            builder_pattern,
        ):
            errors.append(f"x.py dist does not describe the step for producer alias {alias}")

    for relative, pattern in STAGE0_DIST_PRODUCER_CONFIG_PATTERNS:
        path = root / relative
        if path.is_file() and not file_contains(path, pattern):
            errors.append(
                "x.py config docs/defaults are missing producer cue "
                f"{pattern!r} in {relative}"
            )

    for relative, pattern, description in STAGE0_DIST_PRODUCER_ARTIFACT_PATTERNS:
        path = root / relative
        if path.is_file() and not file_contains(path, pattern):
            errors.append(
                f"x.py dist producer is missing {description}: "
                f"{pattern!r} in {relative}"
            )

    return tuple(errors)


def producer_command_preflight_report_lines(root: Path) -> list[str]:
    return [
        "producer_command_preflight: static-ready",
        f"repo_root:             {root}",
        f"producer_dry_run:     {shell_command(STAGE0_DIST_PRODUCER_DRY_RUN_COMMAND)}",
        f"producer_dist:        {shell_command(STAGE0_DIST_PRODUCER_COMMAND)}",
        "executable_precondition:",
        (
            "  - the Trust stage0 payload/admission preflight must pass before "
            "x.py can hydrate stage0 and execute the producer dry-run"
        ),
        (
            "  - run: python3 src/tools/trust-stage0-dist/prepare.py "
            "--check-producer-stage0-payloads-only"
        ),
        "verified_surface:",
        "  - bootstrap global --dry-run flag is declared",
        "  - requested x.py dist aliases are registered or path-addressable",
        "  - requested dist steps are described under Kind::Dist",
        "  - trust-std producer emits a Trust-owned archive name",
        (
            "  - bootstrap config docs/defaults cover channel, extended tools, "
            "sign-folder, upload-addr, and compression formats"
        ),
        "writes:               none",
    ]


def producer_report_lines(
    *,
    input_dist: Path,
    source_manifest_path: Path,
    date: str,
    source_channel: str,
    owned_channel: str,
    archive_format: str,
    filenames: tuple[str, ...],
) -> list[str]:
    source_manifest = f"channel-rust-{source_channel}.toml"
    output_manifest = f"channel-rust-{owned_channel}.toml"
    try:
        rel_input_dist = input_dist.relative_to(repo_root()).as_posix()
        upload_addr = f"file://$PWD/{rel_input_dist}"
    except ValueError:
        upload_addr = input_dist.as_uri()
    return [
        "producer_dry_run_command:",
        f"  {shell_command(STAGE0_DIST_PRODUCER_DRY_RUN_COMMAND)}",
        "producer_dist_command:",
        f"  {shell_command(STAGE0_DIST_PRODUCER_COMMAND)}",
        "producer_dist_config:",
        "  [rust].channel = \"trust\"",
        "  [build].extended = true",
        (
            "  [build].tools uses bootstrap-internal selectors for targo, "
            "targo-trust, trustdoc, tippy, trustfmt, trust-analyzer, "
            "src, trust-llvm-tools"
        ),
        "  [dist].compression-formats includes xz for stage0 seed inputs",
        "producer_manifest_command:",
        "  ./x.py run src/tools/build-manifest",
        "producer_manifest_config:",
        f"  [dist].sign-folder = \"{input_dist}\"",
        f"  [dist].upload-addr = \"{upload_addr}\"",
        "direct_manifest_equivalent:",
        f"  build-manifest {input_dist} {input_dist} {date} {upload_addr} {source_channel}",
        f"expected_source_manifest: {source_manifest_path}",
        f"expected_manifest_name:   {source_manifest}",
        f"owned_manifest_name:      {output_manifest}",
        f"archive_format:          {archive_format}",
        "required_stage0_archives:",
        *(
            [f"  - {filename}" for filename in filenames]
            if filenames
            else ["  (unavailable until the expected source manifest exists)"]
        ),
        "prepare_stage0_command:  python3 src/tools/trust-stage0-dist/prepare.py "
        + f"--input-dist {input_dist} --archive-format xz --stage0-seed-only "
        + "--check-inputs-only",
    ]


def rename_stage0_manifest_packages(packages: dict[str, object]) -> None:
    renames = sorted(
        STAGE0_COMPONENT_RENAMES.items(), key=lambda item: len(item[0]), reverse=True
    )
    for source, owned in renames:
        if source in packages:
            if owned in packages and owned != source:
                raise ValueError(f"manifest already contains both {source!r} and {owned!r}")
            packages[owned] = packages.pop(source)


def rewrite_stage0_profile_components(manifest: dict[str, object]) -> None:
    profiles = manifest.get("profiles")
    if not isinstance(profiles, dict):
        return
    for profile in profiles.values():
        if not isinstance(profile, dict):
            continue
        components = profile.get("components")
        if isinstance(components, list):
            profile["components"] = [
                stage0_component_name(component) if isinstance(component, str) else component
                for component in components
            ]


def rewrite_stage0_renames(manifest: dict[str, object]) -> None:
    renames = manifest.get("renames")
    if not isinstance(renames, dict):
        return

    for source, owned in sorted(
        STAGE0_COMPONENT_RENAMES.items(),
        key=lambda item: len(item[0]),
        reverse=True,
    ):
        if source not in renames:
            continue
        if owned in renames and owned != source:
            # A Trust-native manifest (from our own build-manifest) already carries
            # the owned rename key next to the legacy source alias, both pointing at
            # the owned target — the rename is effectively already applied. Keep BOTH
            # (the source alias is a valid backward-compat entry) instead of erroring;
            # the `to`-target rewrite below normalizes each key independently. This
            # keeps rewrite_stage0_renames idempotent on already-branded manifests.
            continue
        renames[owned] = renames.pop(source)

    for rename in renames.values():
        if not isinstance(rename, dict):
            continue
        target = rename.get("to")
        if isinstance(target, str):
            rename["to"] = stage0_component_name(target)


def rewrite_manifest(
    manifest: dict[str, object],
    *,
    input_dist: Path,
    output_date_dir: Path,
    date: str,
    dist_server: str,
    source_channel: str,
    owned_channel: str,
    archive_format: str,
    materialized_components: frozenset[str] | None = None,
    strict_target_archives: bool = False,
) -> None:
    packages = manifest.get("pkg")
    if not isinstance(packages, dict):
        raise ValueError("manifest is missing [pkg] table")

    validate_manifest_inputs(
        packages,
        input_dist=input_dist,
        date=date,
        archive_format=archive_format,
        source_channel=source_channel,
        owned_channel=owned_channel,
        materialized_components=materialized_components,
        strict_target_archives=strict_target_archives,
        require_owned_archive_names=source_channel == owned_channel,
    )

    manifest["date"] = date
    for component, package in packages.items():
        if not isinstance(package, dict):
            continue
        version = package.get("version")
        if isinstance(version, str):
            package["version"] = replace_channel_token(version, source_channel, owned_channel)
        if materialized_components is not None and component not in materialized_components:
            package.pop("target", None)
            continue
        targets = package.get("target")
        if not isinstance(targets, dict):
            continue
        for target_key, target in targets.items():
            if isinstance(target_key, str) and isinstance(target, dict):
                if strict_target_archives and not target_archives_match_target_key(
                    target_key, target
                ):
                    mark_target_unavailable(target)
                    continue
                rewrite_target_urls(
                    target,
                    input_dist=input_dist,
                    output_date_dir=output_date_dir,
                    date=date,
                    dist_server=dist_server,
                    source_channel=source_channel,
                    owned_channel=owned_channel,
                    archive_format=archive_format,
                )
    rename_stage0_manifest_packages(packages)
    rewrite_stage0_profile_components(manifest)
    rewrite_stage0_renames(manifest)


def validate_manifest_inputs(
    packages: dict[str, object],
    *,
    input_dist: Path,
    date: str,
    archive_format: str,
    source_channel: str,
    owned_channel: str,
    materialized_components: frozenset[str] | None = None,
    strict_target_archives: bool = False,
    require_owned_archive_names: bool = False,
) -> None:
    missing = [component for component in REQUIRED_MANIFEST_PACKAGES if component not in packages]
    if missing:
        raise ValueError("manifest is missing required trust components: " + ", ".join(missing))

    missing_tarballs = collect_missing_source_tarballs(
        packages,
        input_dist=input_dist,
        date=date,
        archive_format=archive_format,
        materialized_components=materialized_components,
        strict_target_archives=strict_target_archives,
    )
    if missing_tarballs:
        raise MissingDistTarballs(
            input_dist=input_dist,
            date=date,
            filenames=missing_tarballs,
        )

    contract_errors = collect_archive_contract_errors(
        packages,
        input_dist=input_dist,
        date=date,
        archive_format=archive_format,
        source_channel=source_channel,
        owned_channel=owned_channel,
        materialized_components=materialized_components,
        strict_target_archives=strict_target_archives,
        require_owned_archive_names=require_owned_archive_names,
    )
    if contract_errors:
        raise ValueError(
            "manifest/archive contract failed:\n  - " + "\n  - ".join(contract_errors)
        )


def checksum_entries(
    manifest: dict[str, object],
    *,
    dist_server: str,
    components: tuple[str, ...],
) -> dict[str, str]:
    prefix = f"{dist_server.rstrip('/')}/"
    packages = manifest["pkg"]
    assert isinstance(packages, dict)

    checksums: dict[str, str] = {}
    for component in components:
        package = packages[component]
        assert isinstance(package, dict)
        targets = package["target"]
        assert isinstance(targets, dict)
        for target in targets.values():
            if not isinstance(target, dict):
                continue
            for url_key, hash_key in (("url", "hash"), ("xz_url", "xz_hash")):
                url = target.get(url_key)
                digest = target.get(hash_key)
                if isinstance(url, str) and isinstance(digest, str):
                    if not url.startswith(prefix):
                        raise ValueError(f"url does not start with dist server: {url}")
                    checksums[url[len(prefix) :]] = digest
    return dict(sorted(checksums.items()))


def stage0_content(
    *,
    manifest: dict[str, object],
    manifest_hash: str,
    git_commit_hash: str,
    dist_server: str,
    owned_channel: str,
    compiler_version: str,
    rustfmt_version: str,
    checksums: dict[str, str],
    metadata_only_checkout: bool,
) -> str:
    date = manifest["date"]
    if isinstance(date, dt.date):
        date = date.isoformat()
    if not isinstance(date, str):
        raise ValueError("manifest date must be a string")

    dist_root = dist_server.rstrip("/")
    lines = [
        f"dist_server={dist_root}",
        *(
            ["dist_payload_mode=metadata-only"]
            if metadata_only_checkout
            else []
        ),
        f"artifacts_server={dist_root}/artifacts",
        f"artifacts_with_llvm_assertions_server={dist_root}/artifacts-with-llvm-assertions",
        "git_merge_commit_email=trust@local",
        "nightly_branch=main",
        f"compiler_dist_channel={owned_channel}",
        f"rustfmt_dist_channel={owned_channel}",
        "",
        "# The configuration above this comment is editable, and can be changed",
        "# by forks of the repository if they have alternate values.",
        "#",
        "# The section below was generated by src/tools/trust-stage0-dist/prepare.py",
        "# from a repo-local dist snapshot.",
        "",
        f"compiler_channel_manifest_hash={manifest_hash}",
        f"compiler_git_commit_hash={git_commit_hash}",
        f"compiler_date={date}",
        f"compiler_version={compiler_version}",
        f"rustfmt_channel_manifest_hash={manifest_hash}",
        f"rustfmt_git_commit_hash={git_commit_hash}",
        f"rustfmt_date={date}",
        f"rustfmt_version={rustfmt_version}",
        "",
    ]
    lines.extend(f"{key}={value}" for key, value in checksums.items())
    lines.append("")
    return "\n".join(lines)


def write_stage0_admission_manifest(
    *,
    output_root: Path,
    checksums: dict[str, str],
    git_commit_hash: str,
    date: str,
    source_channel: str,
    owned_channel: str,
    manifest_hash: str,
    metadata_only_checkout: bool,
) -> Path:
    path = output_root / STAGE0_ADMISSION_FILENAME
    path.write_text(
        json.dumps(
            {
                "schema": STAGE0_ADMISSION_SCHEMA,
                "admission": "internal",
                "promotion_decision": "admit-internal",
                "public_upload": False,
                "date": date,
                "git_commit_hash": git_commit_hash,
                "source_channel": source_channel,
                "owned_channel": owned_channel,
                "manifest_hash": manifest_hash,
                "dist_payload_mode": "metadata-only"
                if metadata_only_checkout
                else "full",
                "payloads": [
                    {"relative_path": path, "sha256": digest}
                    for path, digest in sorted(checksums.items())
                ],
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    return path


def manifest_git_commit_hash(manifest: dict[str, object]) -> str | None:
    packages = manifest["pkg"]
    assert isinstance(packages, dict)
    trust_package = packages.get("trust")
    assert isinstance(trust_package, dict)
    value = trust_package.get("git_commit_hash") or trust_package.get("git-commit-hash")
    return value if isinstance(value, str) and value else None


def component_archive_version(
    manifest: dict[str, object],
    *,
    component: str,
    fallback: str,
) -> str:
    packages = manifest["pkg"]
    assert isinstance(packages, dict)
    package = packages[component]
    assert isinstance(package, dict)
    targets = package["target"]
    assert isinstance(targets, dict)

    for target_key, target in targets.items():
        if not isinstance(target_key, str) or not isinstance(target, dict):
            continue
        if target_key == "*":
            continue
        for url_key in ("xz_url", "url"):
            url = target.get(url_key)
            if not isinstance(url, str) or not url:
                continue
            filename = Path(url).name
            prefix = f"{component.removesuffix('-preview')}-"
            for suffix in (f"-{target_key}.tar.xz", f"-{target_key}.tar.gz"):
                if filename.startswith(prefix) and filename.endswith(suffix):
                    return filename[len(prefix) : -len(suffix)]
    return fallback


def prepare(args: argparse.Namespace) -> None:
    if args.check_producer_command_only:
        root = repo_root()
        errors = producer_command_preflight_errors(root)
        if errors:
            raise ValueError(
                "stage0 dist producer command preflight failed:\n  - "
                + "\n  - ".join(errors)
            )
        for line in producer_command_preflight_report_lines(root):
            print(line)
        return

    if args.check_producer_stage0_payloads_only:
        root = repo_root()
        if args.json:
            report = producer_stage0_payload_preflight_report(root)
            print(json.dumps(report, indent=2, sort_keys=True))
            blocked = report["status"] == "blocked"
        else:
            blocked, lines = producer_stage0_payload_preflight_report_lines(root)
            for line in lines:
                print(line, file=sys.stderr if blocked else sys.stdout)
        if blocked:
            if args.json:
                raise Stage0PayloadPreflightBlocked()
            raise ValueError("stage0 producer payload preflight failed")
        return

    input_dist = args.input_dist.resolve()
    output_root = args.output_root.resolve()
    dist_server = args.dist_server or default_dist_server(output_root)

    source_manifest_path = input_dist / f"channel-rust-{args.source_channel}.toml"
    if not source_manifest_path.is_file():
        if args.check_inputs_only and args.report_producer_plan:
            print("trust stage0 input dist preflight: missing source manifest", file=sys.stderr)
            for line in producer_report_lines(
                input_dist=input_dist,
                source_manifest_path=source_manifest_path,
                date=args.date or "<YYYY-MM-DD>",
                source_channel=args.source_channel,
                owned_channel=args.owned_channel,
                archive_format=args.archive_format,
                filenames=(),
            ):
                print(line, file=sys.stderr)
        raise FileNotFoundError(f"missing source manifest: {source_manifest_path}")

    manifest = tomllib.loads(source_manifest_path.read_text(encoding="utf-8"))
    raw_date = manifest.get("date")
    date = args.date or (raw_date.isoformat() if isinstance(raw_date, dt.date) else raw_date)
    if not isinstance(date, str) or not date:
        raise ValueError("manifest is missing a date; pass --date explicitly")

    packages = manifest.get("pkg")
    if not isinstance(packages, dict):
        raise ValueError("manifest is missing [pkg] table")
    materialized_components = (
        frozenset(SOURCE_STAGE0_COMPONENTS) if args.stage0_seed_only else None
    )
    validate_manifest_inputs(
        packages,
        input_dist=input_dist,
        date=date,
        archive_format=args.archive_format,
        source_channel=args.source_channel,
        owned_channel=args.owned_channel,
        materialized_components=materialized_components,
        strict_target_archives=args.stage0_seed_only,
        require_owned_archive_names=args.source_channel == args.owned_channel,
    )
    if args.check_inputs_only:
        validate_rustc_dev_artifact_handoff(
            manifest,
            output_root=None,
            git_commit_hash=(
                args.git_commit_hash
                or manifest_git_commit_hash(manifest)
                or "<stage0-seed-commit>"
            ),
            source_channel=args.source_channel,
            owned_channel=args.owned_channel,
        )
        summary = archive_contract_summary(
            packages,
            input_dist=input_dist,
            date=date,
            archive_format=args.archive_format,
            materialized_components=materialized_components,
            strict_target_archives=args.stage0_seed_only,
        )
        print("trust stage0 input dist preflight: ready")
        print(f"input_dist:       {input_dist}")
        print(f"source_channel:   {args.source_channel}")
        print(f"archive_format:   {args.archive_format}")
        print(f"stage0_seed_only: {args.stage0_seed_only}")
        print(f"archive_refs:     {summary['archive_references']}")
        print(f"archive_files:    {summary['archive_files']}")
        print(f"entrypoint_files: {summary['entrypoint_archives']}")
        print("writes:           none")
        if args.report_producer_plan:
            filenames = archive_contract_filenames(
                packages,
                input_dist=input_dist,
                date=date,
                archive_format=args.archive_format,
                materialized_components=materialized_components,
                strict_target_archives=args.stage0_seed_only,
            )
            for line in producer_report_lines(
                input_dist=input_dist,
                source_manifest_path=source_manifest_path,
                date=date,
                source_channel=args.source_channel,
                owned_channel=args.owned_channel,
                archive_format=args.archive_format,
                filenames=filenames,
            ):
                print(line)
        return

    git_commit_hash = args.git_commit_hash or manifest_git_commit_hash(manifest)
    if not git_commit_hash:
        raise ValueError(
            "manifest [pkg.trust] is missing git_commit_hash; "
            "pass --git-commit-hash for local single-host dist snapshots"
        )
    rustc_dev_artifacts = validate_rustc_dev_artifact_handoff(
        manifest,
        output_root=output_root,
        git_commit_hash=git_commit_hash,
        source_channel=args.source_channel,
        owned_channel=args.owned_channel,
    )

    output_dist = output_root / "dist"
    output_date_dir = output_dist / date
    output_date_dir.mkdir(parents=True, exist_ok=True)
    rewrite_manifest(
        manifest,
        input_dist=input_dist,
        output_date_dir=output_date_dir,
        date=date,
        dist_server=dist_server,
        source_channel=args.source_channel,
        owned_channel=args.owned_channel,
        archive_format=args.archive_format,
        materialized_components=materialized_components,
        strict_target_archives=args.stage0_seed_only,
    )
    if args.stage0_seed_only:
        manifest.pop("artifacts", None)

    if args.merge_existing:
        existing_manifest = output_dist / f"channel-rust-{args.owned_channel}.toml"
        if existing_manifest.is_file() and existing_manifest.read_text(encoding="utf-8").strip():
            adopted = merge_existing_manifest_targets(manifest, existing_manifest)
            if adopted:
                print(
                    f"stage0 merge:    adopted {adopted} foreign-host manifest target(s) "
                    f"from {existing_manifest}"
                )
                print(
                    "stage0 merge:    manifest, admission, checksums, and manifest_hash "
                    "now cover both hosts"
                )

    manifest_text = dump_toml(manifest)
    manifest_bytes = manifest_text.encode("utf-8")
    manifest_hash = sha256_bytes(manifest_bytes)
    latest_manifest = output_dist / f"channel-rust-{args.owned_channel}.toml"
    dated_manifest = output_date_dir / f"channel-rust-{args.owned_channel}.toml"
    latest_manifest.write_bytes(manifest_bytes)
    dated_manifest.write_bytes(manifest_bytes)
    latest_manifest.with_suffix(latest_manifest.suffix + ".sha256").write_text(
        manifest_hash + "\n",
        encoding="utf-8",
    )
    dated_manifest.with_suffix(dated_manifest.suffix + ".sha256").write_text(
        manifest_hash + "\n",
        encoding="utf-8",
    )

    checksums = checksum_entries(
        manifest,
        dist_server=dist_server,
        components=DEFAULT_STAGE0_COMPONENTS,
    )
    admission_manifest = write_stage0_admission_manifest(
        output_root=output_root,
        checksums=checksums,
        git_commit_hash=git_commit_hash,
        date=date,
        source_channel=args.source_channel,
        owned_channel=args.owned_channel,
        manifest_hash=manifest_hash,
        metadata_only_checkout=args.metadata_only_checkout,
    )
    if args.stage0_output is not None:
        args.stage0_output.parent.mkdir(parents=True, exist_ok=True)
        # With --merge-existing the manifest above already covers both hosts, so
        # `checksums`, the admission record, and this stage0 file are dual-host by
        # construction (no separate stage0 merge needed).
        args.stage0_output.write_text(
            stage0_content(
                manifest=manifest,
                manifest_hash=manifest_hash,
                git_commit_hash=git_commit_hash,
                dist_server=dist_server,
                owned_channel=args.owned_channel,
                compiler_version=component_archive_version(
                    manifest,
                    component="trustc",
                    fallback=args.owned_channel,
                ),
                rustfmt_version=component_archive_version(
                    manifest,
                    component="trustfmt-preview",
                    fallback=args.owned_channel,
                ),
                checksums=checksums,
                metadata_only_checkout=args.metadata_only_checkout,
            ),
            encoding="utf-8",
        )

    print(f"trust dist root: {output_root}")
    print(f"trust channel:   {args.owned_channel}")
    print(f"manifest:        {latest_manifest}")
    print(f"admission:       {admission_manifest}")
    print(f"trustc-dev artifacts checked: {len(rustc_dev_artifacts)}")
    if args.stage0_output is not None:
        print(f"stage0 candidate:{args.stage0_output}")


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-dist", type=Path, default=Path("build/dist"))
    parser.add_argument("--output-root", type=Path, default=Path("bootstrap/trust-stage0"))
    parser.add_argument("--source-channel", default="trust")
    parser.add_argument("--owned-channel", default="trust")
    parser.add_argument(
        "--archive-format",
        choices=("xz", "gz", "both"),
        default="both",
        help=(
            "Archive formats to materialize in the owned stage0 snapshot. "
            "Use xz for the tracked minimal bootstrap seed; use both for a full "
            "local rustup mirror."
        ),
    )
    parser.add_argument(
        "--stage0-seed-only",
        action="store_true",
        help=(
            "Materialize only the components that bootstrap consumes from src/stage0 "
            "and remove auxiliary installer/source-code artifact metadata."
        ),
    )
    parser.add_argument(
        "--check-inputs-only",
        action="store_true",
        help=(
            "Validate that --input-dist has the source manifest, required Trust "
            "packages, and referenced archive payloads, then exit without writing "
            "the output root or stage0 candidate."
        ),
    )
    parser.add_argument(
        "--check-producer-command-only",
        action="store_true",
        help=(
            "Validate the static CI-safe stage0 producer dry-run surface from "
            "bootstrap source registrations and config docs, then exit without "
            "running x.py or reading dist payloads. This does not prove the "
            "producer dry-run can execute; run --check-producer-stage0-payloads-only "
            "for the required stage0 payload/admission gate."
        ),
    )
    parser.add_argument(
        "--check-producer-stage0-payloads-only",
        action="store_true",
        help=(
            "Validate that the current src/stage0 file points at locally present "
            "checksum-pinned archive payloads needed before the producer dry-run "
            "can start, then exit without running x.py or writing outputs."
        ),
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help=(
            "With --check-producer-stage0-payloads-only, emit the payload "
            "preflight result as machine-readable JSON."
        ),
    )
    parser.add_argument(
        "--report-producer-plan",
        action="store_true",
        help=(
            "With --check-inputs-only, print the x.py dist/build-manifest producer "
            "path and archive filenames that satisfy the stage0 input contract."
        ),
    )
    parser.add_argument(
        "--metadata-only-checkout",
        action="store_true",
        help=(
            "Emit dist_payload_mode=metadata-only in the generated stage0 file. "
            "Use this when archive payloads are admitted outside Git."
        ),
    )
    parser.add_argument("--date")
    parser.add_argument("--dist-server")
    parser.add_argument("--git-commit-hash")
    parser.add_argument(
        "--stage0-output",
        type=Path,
        default=Path("bootstrap/trust-stage0/src-stage0"),
    )
    parser.add_argument(
        "--merge-existing",
        action="store_true",
        help=(
            "Union this run's payload lines into an existing --stage0-output "
            "instead of overwriting it, preserving other-host (foreign-triple) "
            "payload pins. Use to build a dual-host src/stage0: mint each host's "
            "seed from the SAME committed source, then merge. Refuses if the "
            "existing file's compiler/rustfmt version, date, or commit differ."
        ),
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        prepare(args)
    except Stage0PayloadPreflightBlocked:
        return 1
    except MissingDistTarballs as exc:
        print(exc, file=sys.stderr)
        return 1
    except FileNotFoundError as exc:
        print(exc, file=sys.stderr)
        return 1
    except ValueError as exc:
        print(exc, file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
