# Copyright 2026 Andrew Yates
"""Archive-bound compiler identity, independent of command/transport ownership."""

from __future__ import annotations

import hashlib
import importlib.util
import os
import stat
import subprocess
import tarfile
import time
from pathlib import Path


class SeedIdentityError(RuntimeError):
    """A known mismatch in the selected compiler's immutable input binding."""


def _key(info):
    return (
        info.st_dev,
        info.st_ino,
        info.st_mode,
        info.st_size,
        info.st_mtime_ns,
        info.st_ctime_ns,
    )


def _open_regular(path: Path):
    named = path.lstat()
    if not stat.S_ISREG(named.st_mode):
        raise SeedIdentityError(f"not an exact regular seed input: {path}")
    fd = os.open(
        path,
        os.O_RDONLY
        | getattr(os, "O_CLOEXEC", 0)
        | getattr(os, "O_NONBLOCK", 0)
        | getattr(os, "O_NOFOLLOW", 0),
    )
    source = os.fdopen(fd, "rb")
    if _key(os.fstat(source.fileno())) != _key(named):
        source.close()
        raise SeedIdentityError(f"seed input changed before opening: {path}")
    return source


def _canonical_under(base: Path, relative: str) -> Path:
    parts = relative.split("/")
    if (
        not relative
        or relative.startswith("/")
        or "\\" in relative
        or any(part in ("", ".", "..") for part in parts)
    ):
        raise SeedIdentityError("noncanonical seed input path")
    path = base
    for index, part in enumerate(parts):
        path /= part
        mode = path.lstat().st_mode
        expected = stat.S_ISREG if index == len(parts) - 1 else stat.S_ISDIR
        if not expected(mode):
            raise SeedIdentityError(f"symlink or wrong-type seed component: {path}")
    return path


_LAYOUT_OWNER = None


def _layout_owner():
    global _LAYOUT_OWNER
    if _LAYOUT_OWNER is None:
        # Bind policy to this source file, never ambient sys.path or a fixture's
        # data root. mint_seed_support has no import-time filesystem mutation
        # and does not import this module; its script entry is __main__ guarded.
        path = Path(__file__).resolve().parents[1] / "mint_seed_support.py"
        if "__trust_source_loader__" in globals():
            # Preserve the caller's authenticated transitive source closure,
            # matching the policy owner's own stage0-identity import contract.
            _LAYOUT_OWNER = __trust_source_loader__.module("trust_seed_identity_layout", path)
        else:
            spec = importlib.util.spec_from_file_location("trust_seed_identity_layout", path)
            if spec is None or spec.loader is None:
                raise SeedIdentityError("source build-layout policy is unavailable")
            owner = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(owner)
            _LAYOUT_OWNER = owner
    return _LAYOUT_OWNER


def _materialized_relative(root: Path, compiler: Path):
    """Default materialization role, retaining the literal invocation name.

    Custom/external/genesis build roots are outside this helper's pin-selection
    contract. Only the maintained build and host aliases add physical spellings.
    """
    try:
        return compiler.relative_to(root / "build")
    except ValueError:
        try:
            relative = compiler.relative_to(root / "build.noindex")
        except ValueError:
            return None
        # Reserved default materialization spelling remains applicable even
        # when its required alias is invalid. Validation must refuse, not skip.
        return relative


def _alias_identity(path: Path, *, owned=False):
    info = path.lstat()
    euid = getattr(os, "geteuid", None)
    if not stat.S_ISLNK(info.st_mode) or (owned and (euid is None or info.st_uid != euid())):
        raise SeedIdentityError(f"seed alias must be an owned symlink: {path}")
    return path, _key(info), info.st_uid, os.readlink(path)


def _host_alias_relative(root: Path, build: Path, relative: Path, aliases):
    # Bootstrap's Session::new creates only this reserved host alias. Map
    # its directory role, never an arbitrary inner link or compiler name.
    alias = build / "host"
    original = _alias_identity(alias, owned=True)
    raw_target = original[3]
    target = Path(raw_target)
    if any(part in ("", ".", "..") for part in raw_target.split("/")[1 if target.is_absolute() else 0:]):
        raise SeedIdentityError("seed host alias target is not canonical")
    host = target.name
    if (host == "host" or ".." in host or not host
            or not all(c.isascii() and (c.isalnum() or c in "_.-") for c in host)):
        raise SeedIdentityError("seed host alias has an invalid canonical host")
    canonical_host = build / host
    if target.is_absolute():
        # A source checkout may itself have the maintained .ubd spelling;
        # both source-root spellings must still name this exact build root.
        if (target.parent.name not in ("build", "build.noindex")
                or target.parent.parent.resolve(strict=True) != root.resolve(strict=True)
                or target.parent.resolve(strict=True) != build.resolve(strict=True)):
            raise SeedIdentityError("seed host alias escapes the default build tree")
    elif target.parts != (host,):
        raise SeedIdentityError("seed host alias target is not a direct host child")
    if (not stat.S_ISDIR(canonical_host.lstat().st_mode)
            or _key((alias.parent / target).lstat()) != _key(canonical_host.lstat())):
        raise SeedIdentityError("seed host alias target is not a real host directory")
    if _alias_identity(alias, owned=True) != original:
        raise SeedIdentityError("seed host alias changed during selection")
    if aliases is not None:
        aliases.append(original)
    return Path(host, *relative.parts[1:])


def _materialized_compiler(root: Path, compiler: Path, *, aliases=None) -> Path:
    relative = _materialized_relative(root, compiler)
    if relative is None:
        raise SeedIdentityError("seed compiler is outside this source's default build tree")
    build = root / "build"
    if compiler.is_relative_to(root / "build.noindex"):
        owner = _layout_owner()
        if not owner.is_sanctioned_build_link(root):
            raise SeedIdentityError("physical seed spelling requires the sanctioned build.noindex alias")
        build = owner.physical_build_directory(root)
    elif build.is_symlink():
        owner = _layout_owner()
        if not owner.is_sanctioned_build_link(root):
            raise SeedIdentityError("seed build root is not the sanctioned build.noindex alias")
        build = owner.physical_build_directory(root)
    if (root / "build").is_symlink() and aliases is not None:
        aliases.append(_alias_identity(root / "build"))
    if not stat.S_ISDIR(build.lstat().st_mode):
        raise SeedIdentityError("seed build root is not a real directory")
    if relative.parts[0] == "host":
        try:
            relative = _host_alias_relative(root, build, relative, aliases)
        except SeedIdentityError:
            raise
        except (OSError, RuntimeError) as error:
            raise SeedIdentityError("seed host alias has no exact real host target") from error
    return _canonical_under(build, relative.as_posix())


class _AuthenticatedBinding(tuple):
    """Retain the existing (stat, digest) API plus its authenticated path role."""

    def __new__(cls, snapshot, root, compiler, selected, aliases):
        binding = super().__new__(cls, snapshot)
        binding.root = root
        binding.compiler = compiler
        binding.selected = selected
        binding.aliases = tuple(aliases)
        return binding


def _check_materialized_binding(compiler: Path, binding):
    if not isinstance(binding, _AuthenticatedBinding):
        return
    aliases = []
    try:
        selected = _materialized_compiler(binding.root, compiler, aliases=aliases)
        if (compiler != binding.compiler or selected != binding.selected
                or tuple(aliases) != binding.aliases):
            raise SeedIdentityError("selected seed compiler path changed during the query")
    except (OSError, RuntimeError) as error:
        raise SeedIdentityError("selected seed compiler path changed during the query") from error


def _digest(source, deadline=None):
    value = hashlib.sha256()
    for block in iter(lambda: source.read(1 << 20), b""):
        if deadline is not None and time.monotonic() >= deadline:
            raise subprocess.TimeoutExpired(["seed-archive-authentication"], 0)
        value.update(block)
    return value.hexdigest()


def compiler_snapshot(compiler: Path, *, deadline=None):
    """Observe one regular launcher; this alone grants no pin/seed authority."""
    with _open_regular(compiler) as source:
        original = os.fstat(source.fileno())
        digest = _digest(source, deadline)
        if _key(os.fstat(source.fileno())) != _key(original) or _key(
            compiler.lstat()
        ) != _key(original):
            raise SeedIdentityError("selected seed compiler changed during observation")
    return original, digest


def check_compiler_snapshot(compiler: Path, binding):
    _check_materialized_binding(compiler, binding)
    original, expected = binding
    try:
        with _open_regular(compiler) as source:
            if (
                _key(os.fstat(source.fileno())) != _key(original)
                or _digest(source) != expected
                or _key(os.fstat(source.fileno())) != _key(original)
                or _key(compiler.lstat()) != _key(original)
            ):
                raise SeedIdentityError(
                    "selected seed compiler changed during the query"
                )
    except OSError as error:
        raise SeedIdentityError(
            "selected seed compiler identity was lost during the query"
        ) from error
    _check_materialized_binding(compiler, binding)


def authenticate_compiler(root: Path, compiler: Path, stage0, *, deadline=None):
    """Bind the literal invocation to one exact regular trustc archive member.

    This binds launcher bytes, not every loaded dylib/system input or a proof
    verdict. It neither selects nor executes a transport, Targo or compiler.
    """
    if (
        compiler.parent.name != "bin"
        or compiler.parent.parent.name != "stage0"
        or compiler.name not in ("rustc", "trustc")
    ):
        raise SeedIdentityError("seed compiler is outside a materialized stage0")
    aliases = []
    selected = _materialized_compiler(root, compiler, aliases=aliases)
    host = selected.parent.parent.parent.name
    if not stage0.get("compiler_version") or not stage0.get("compiler_date"):
        raise SeedIdentityError("selected seed lacks compiler version/date identity")
    stem = f"trustc-{stage0['compiler_version']}-{host}"
    relative = f"dist/{stage0['compiler_date']}/{stem}.tar.xz"
    expected = stage0.get(relative, "")
    if len(expected) != 64 or any(c not in "0123456789abcdef" for c in expected):
        raise SeedIdentityError("selected seed has no exact trustc archive pin")
    archive = _canonical_under(root / "bootstrap/trust-stage0", relative)
    # Every inner component remains strict; only the maintained first build
    # alias is mapped. The actual command still uses the literal invocation.
    with _open_regular(archive) as payload:
        original = os.fstat(payload.fileno())
        if _digest(payload, deadline) != expected:
            raise SeedIdentityError(
                "seed trustc archive SHA-256 differs from src/stage0"
            )
        payload.seek(0)
        count = 0
        try:
            with tarfile.open(fileobj=payload, mode="r|xz") as image:
                for member in image:
                    if deadline is not None and time.monotonic() >= deadline:
                        raise subprocess.TimeoutExpired(
                            ["seed-archive-authentication"], 0
                        )
                    if member.name != f"{stem}/trustc/bin/trustc":
                        continue
                    count += 1
                    if count != 1 or not member.isfile():
                        raise SeedIdentityError(
                            "seed archive lacks one regular trustc member"
                        )
                    content = image.extractfile(member)
                    if content is None:
                        raise SeedIdentityError("seed compiler member cannot be read")
                    with content:
                        member_digest = _digest(content, deadline)
        except tarfile.TarError as error:
            raise SeedIdentityError("seed trustc archive is malformed") from error
        if count != 1:
            raise SeedIdentityError("seed archive lacks one regular trustc member")
        if _key(os.fstat(payload.fileno())) != _key(original) or _key(
            archive.lstat()
        ) != _key(original):
            raise SeedIdentityError("seed trustc archive changed during authentication")
    binding = compiler_snapshot(selected, deadline=deadline)
    if not binding[0].st_mode & 0o111 or binding[1] != member_digest:
        raise SeedIdentityError("seed compiler differs from its pinned archive member")
    bound = _AuthenticatedBinding(binding, root, compiler, selected, aliases)
    _check_materialized_binding(compiler, bound)
    return bound


def pinned_compiler_binding(root: Path, compiler: Path, *, timeout):
    """None only outside the pinned-stage0 path; applicable refusals propagate."""
    if _materialized_relative(root, compiler) is None:
        return None
    if compiler.parent.name != "bin" or compiler.parent.parent.name != "stage0":
        return None
    fields = {}
    for number, line in enumerate((root / "src/stage0").read_text().splitlines(), 1):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        key, separator, value = line.partition("=")
        key, value = key.strip(), value.strip()
        if not separator or not key or not value or key in fields:
            raise SeedIdentityError(f"src/stage0:{number}: malformed identity record")
        fields[key] = value
    return authenticate_compiler(
        root, compiler, fields, deadline=time.monotonic() + timeout
    )
