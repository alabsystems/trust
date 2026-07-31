#!/usr/bin/env python3
"""Recreate the Trust bootstrap — seed-first, genesis fallback.

Preferred path (SEED): materialize the checksum-pinned Trust stage0 seed that
`src/stage0` declares (fetching it from the `trust-stage0-<date>` release via
an authenticated `gh` when absent), validate every payload against the pins
(`scripts/check_seed_freshness.py --require-payloads`, fail-closed), write a
`bootstrap.toml` with NO stage0 override, and drive `./x.py build`. The result
is **trust-from-trust** — stock Rust nowhere in the loop — and no system
`rustc`/`cargo` is required at all.

Fallback path (GENESIS, `--genesis` or when the seed cannot be materialized):
wrap an installed `rustc`/`cargo` into a Trust-named local genesis stage0
adapter and point the stage0 tool keys at it. This is a developer /
first-build convenience only. The produced adapter is *not* release evidence —
see `scripts/create_local_genesis_stage0.py` for the admission boundary.

After a successful build, optionally re-seed `bootstrap/trust-stage0` via the
canonical `prepare.py` so future checkouts skip even the fetch.

For an immutable internal-lineage receipt, pass `--fresh-seed`.
That option safely quarantines any previously extracted `build/<host>/stage0`
before bootstrap-lineage capture so x.py must hydrate the compiler from the
validated archives during the recorded build. A normal retry keeps the honest
`candidate-ready` classification because a pre-existing extracted compiler is
not, by itself, proof of fresh archive materialization.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import shlex
import shutil
import signal
import stat
import subprocess
import sys
import tarfile
import tempfile
import threading
import time
from dataclasses import dataclass
from pathlib import Path
from types import SimpleNamespace

REEXEC_GUARD_ENV = "TRUST_RECREATE_BOOTSTRAP_REEXEC"

BOOTSTRAP_COMPILER_VERIFICATION = {
    "mode": "disabled",
    "flag": "-Ztrust-verify=off",
    "reason": "bootstrap stability",
    "counts_as_self_proof": False,
}

BUILD_AUTHORITY_ENV_NAMES = {
    "AR",
    "CC",
    "CFLAGS",
    "CPP",
    "CPPFLAGS",
    "CXX",
    "CXXFLAGS",
    "LD",
    "LDFLAGS",
    "LIBRARY_PATH",
    "CPATH",
    "C_INCLUDE_PATH",
    "CPLUS_INCLUDE_PATH",
    "OBJC_INCLUDE_PATH",
    "NM",
    "RANLIB",
    "STRIP",
    "MAKE",
    "MAKEFLAGS",
    "MFLAGS",
    "PKG_CONFIG",
    "PKG_CONFIG_PATH",
    "PKG_CONFIG_LIBDIR",
    "PKG_CONFIG_SYSROOT_DIR",
    "CMAKE_GENERATOR",
    "CMAKE_GENERATOR_TOOLSET",
    "CMAKE_GENERATOR_PLATFORM",
    "CMAKE_PREFIX_PATH",
    "CMAKE_TOOLCHAIN_FILE",
    "NINJA_STATUS",
    "LLVM_CONFIG",
    "LLVM_SYS_191_PREFIX",
    "LIBCLANG_PATH",
    "SDKROOT",
    "DEVELOPER_DIR",
    "MACOSX_DEPLOYMENT_TARGET",
    "IPHONEOS_DEPLOYMENT_TARGET",
    "RUSTC",
    "RUSTDOC",
    "RUSTFLAGS",
    "RUSTDOCFLAGS",
    "RUSTC_BOOTSTRAP",
    "RUSTC_WRAPPER",
    "RUSTC_WORKSPACE_WRAPPER",
    "CARGO",
    "CARGO_HOME",
    "CARGO_BUILD_RUSTC",
    "CARGO_BUILD_RUSTDOC",
    "CARGO_BUILD_RUSTFLAGS",
    "CARGO_ENCODED_RUSTFLAGS",
    "CARGO_TARGET_DIR",
    "RUSTUP_TOOLCHAIN",
    "RUSTUP_HOME",
    "DYLD_LIBRARY_PATH",
    "DYLD_FALLBACK_LIBRARY_PATH",
    "LD_LIBRARY_PATH",
    "SOURCE_DATE_EPOCH",
    "ZERO_AR_DATE",
    # Python, shell, dynamic-loader, and Git repository-discovery injection can
    # replace code or configuration before x.py reaches the compiler.  The Git
    # reads used by provenance are already separately sanitized; the build child
    # must not inherit a different authority surface.
    "PYTHONHOME",
    "PYTHONPATH",
    "VIRTUAL_ENV",
    "BASH_ENV",
    "ENV",
    "LD_PRELOAD",
    "DYLD_INSERT_LIBRARIES",
    "GIT_DIR",
    "GIT_WORK_TREE",
    "GIT_INDEX_FILE",
    "GIT_OBJECT_DIRECTORY",
    "GIT_ALTERNATE_OBJECT_DIRECTORIES",
    "GIT_COMMON_DIR",
    "GIT_NAMESPACE",
}

BUILD_AUTHORITY_ENV_PREFIXES = (
    "AR_",
    "CC_",
    "CFLAGS_",
    "CXX_",
    "CXXFLAGS_",
    "LDFLAGS_",
    "CARGO_TARGET_",
    "CCACHE_",
    "SCCACHE_",
    "DISTCC_",
    "GIT_CONFIG_",
    # Bootstrap, rustc, and Targo all have behavior-changing environment
    # switches beyond the small legacy allowlist above.  Release provenance
    # rejects the whole namespaces rather than letting a newly added switch
    # silently escape the receipt.
    "RUST",
    "CARGO_",
    "CARGOFLAGS_",
    "TRUST_",
    "BOOTSTRAP_",
    "DUMP_BOOTSTRAP_",
)


def ensure_python_311() -> None:
    """Re-exec under a python >= 3.11 when invoked with an older interpreter.

    The recreator itself parses fine on 3.9 (stock macOS python3), but the
    sub-scripts it drives with sys.executable (check_seed_freshness.py, x.py)
    need `tomllib`. Re-execing here — the same pattern as
    fetch_trust_stage0_payloads.py — beats crashing minutes into the run.
    """
    # Apple's /usr/bin/python3 launcher injects these broad search roots before
    # user code starts. They are not user-selected build authority and must not
    # leak through the verified re-exec into native compilation. Normalize only
    # the exact documented CLT defaults; any differing/extended value remains
    # present and is rejected by capture_build_authority.
    executable_text = str(Path(sys.executable))
    apple_clt_python = executable_text in {
        "/usr/bin/python3",
        "/Library/Developer/CommandLineTools/usr/bin/python3",
        "/Applications/Xcode.app/Contents/Developer/usr/bin/python3",
    }
    if platform.system().lower() == "darwin" and apple_clt_python:
        clt_launcher_defaults = {
            "CPATH": "/usr/local/include",
            "LIBRARY_PATH": "/usr/local/lib",
            "SDKROOT": "/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk",
        }
        for name, expected in clt_launcher_defaults.items():
            if os.environ.get(name) == expected:
                os.environ.pop(name, None)

    if sys.version_info >= (3, 11):
        return
    if os.environ.get(REEXEC_GUARD_ENV) != "1":
        newer = find_python_ge_311()
        if newer and Path(newer) != Path(sys.executable):
            os.environ[REEXEC_GUARD_ENV] = "1"
            os.execv(newer, [newer, *sys.argv])
    raise SystemExit(
        "recreate-bootstrap needs python >= 3.11 (tomllib) and found "
        f"{sys.version.split()[0]} with no newer interpreter on PATH. "
        "Install one (e.g. `brew install python@3.12`) and re-run."
    )


def line_buffer_output() -> None:
    """Keep parent prints ordered with child-process output when piped.

    Without this, python block-buffers our status lines while subprocesses
    write straight through, so a piped/logged run shows children first and
    the narration at the end.
    """
    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(line_buffering=True)
        except (AttributeError, ValueError, OSError):
            pass


def repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def host_triple() -> str:
    machine = platform.machine().lower()
    system = platform.system().lower()
    if machine in {"arm64", "aarch64"}:
        arch = "aarch64"
    elif machine in {"amd64", "x64", "x86_64"}:
        arch = "x86_64"
    else:
        arch = machine
    if system == "darwin":
        return f"{arch}-apple-darwin"
    if system == "linux":
        return f"{arch}-unknown-linux-gnu"
    # Trust: Windows host support for the pure-bootstrap flow (machine() is
    # "AMD64" on x86_64 Windows, normalized to x86_64 above).
    if system == "windows":
        return f"{arch}-pc-windows-msvc"
    raise SystemExit(f"unsupported host platform: {system}/{machine}")


@dataclass
class Prereq:
    name: str
    path: str | None
    detail: str
    required: bool
    ok: bool


def which(name: str) -> str | None:
    return shutil.which(name)


CONTROLLED_GIT_PATH = "/usr/bin:/bin:/usr/sbin:/sbin"
SUBMODULE_UPDATE_TIMEOUT_SECONDS = 10 * 60
SUBMODULE_UPDATE_OUTPUT_LIMIT_BYTES = 4 * 1024 * 1024
CONTROLLED_GIT_CONFIG_OVERRIDES = (
    f"core.hooksPath={os.devnull}",
    "core.fsmonitor=false",
    "core.untrackedCache=false",
    f"core.attributesFile={os.devnull}",
    f"core.excludesFile={os.devnull}",
    "credential.helper=",
    "credential.interactive=never",
    "http.extraHeader=",
    "http.cookieFile=",
    "http.saveCookies=false",
    "http.proxy=",
    "http.sslVerify=true",
    "protocol.allow=never",
    "protocol.ext.allow=never",
    "protocol.file.allow=never",
    "protocol.git.allow=never",
    "protocol.http.allow=never",
    "protocol.https.allow=always",
    "protocol.ssh.allow=never",
)


def _root_owned_executable_path_chain(path: Path) -> bool:
    """Require root ownership and cross-user immutability for a fixed OS tool."""
    if os.name == "nt" or not path.is_absolute():
        return os.name == "nt"
    current = Path(path.anchor)
    components = path.parts[1:]
    try:
        root_metadata = current.lstat()
    except OSError:
        return False
    if (
        not stat.S_ISDIR(root_metadata.st_mode)
        or root_metadata.st_uid != 0
        or stat.S_IMODE(root_metadata.st_mode) & 0o022
    ):
        return False
    for index, component in enumerate(components):
        current /= component
        try:
            metadata = current.lstat()
        except OSError:
            return False
        if metadata.st_uid != 0:
            return False
        leaf = index + 1 == len(components)
        if stat.S_ISLNK(metadata.st_mode):
            continue
        if leaf:
            if not stat.S_ISREG(metadata.st_mode):
                return False
        elif not stat.S_ISDIR(metadata.st_mode):
            return False
        if stat.S_IMODE(metadata.st_mode) & 0o022:
            return False
    return True


def fixed_git_executable() -> Path | None:
    """Resolve a fixed, OS-owned Git without consulting PATH or Git config.

    On Darwin, ``/usr/bin/git`` is an ``xcrun`` dispatcher whose selected
    developer directory can vary independently of the path being recorded.  Use
    the real CLT/Xcode binary instead.  Linux distributions install the real
    binary at one of the two fixed paths below.  Windows support is limited to
    the standard system-wide Git for Windows installation roots; a PATH-only
    installation is deliberately not provenance authority.
    """
    system = platform.system().lower()
    if system == "darwin":
        candidates = (
            Path("/Library/Developer/CommandLineTools/usr/bin/git"),
            Path("/Applications/Xcode.app/Contents/Developer/usr/bin/git"),
        )
    elif system == "linux":
        candidates = (Path("/usr/bin/git"), Path("/bin/git"))
    elif system == "windows":
        candidates = (
            Path("C:/Program Files/Git/cmd/git.exe"),
            Path("C:/Program Files/Git/bin/git.exe"),
            Path("C:/Program Files (x86)/Git/cmd/git.exe"),
        )
    else:
        candidates = ()

    for candidate in candidates:
        try:
            resolved = candidate.resolve(strict=True)
            metadata = resolved.stat()
        except OSError:
            continue
        if not stat.S_ISREG(metadata.st_mode) or not os.access(resolved, os.X_OK):
            continue
        if os.name != "nt" and (
            metadata.st_uid != 0 or stat.S_IMODE(metadata.st_mode) & 0o022
        ):
            continue
        if os.name != "nt" and (
            not _root_owned_executable_path_chain(candidate)
            or not _root_owned_executable_path_chain(resolved)
        ):
            continue
        if system == "darwin" and resolved == Path("/usr/bin/git"):
            continue
        return resolved
    return None


def _require_fixed_git() -> Path:
    git = fixed_git_executable()
    if git is None:
        raise RuntimeError(
            "no fixed OS-owned Git is available (PATH-selected Git is not "
            "bootstrap/provenance authority)"
        )
    return git


def _controlled_git_command(arguments: list[str] | tuple[str, ...]) -> list[str]:
    command = [str(_require_fixed_git())]
    for override in CONTROLLED_GIT_CONFIG_OVERRIDES:
        command.extend(("-c", override))
    command.extend(arguments)
    return command


def tool_version(
    path: str,
    args: tuple[str, ...] = ("--version",),
    *,
    environment: dict[str, str] | None = None,
) -> str:
    try:
        out = subprocess.run(
            [path, *args],
            text=True,
            capture_output=True,
            check=False,
            env=environment,
            timeout=10,
        )
        return (out.stdout or out.stderr).splitlines()[0] if (out.stdout or out.stderr) else ""
    except (FileNotFoundError, subprocess.TimeoutExpired):
        return ""


def find_python_ge_311() -> str | None:
    """Find a python interpreter >= 3.11 (needed for tomllib)."""
    candidates = [
        sys.executable,
        which("python3.14"),
        which("python3.13"),
        which("python3.12"),
        which("python3.11"),
        which("python3"),
    ]
    for cand in candidates:
        if not cand:
            continue
        try:
            out = subprocess.run(
                [cand, "-c", "import sys; print(sys.version_info[:2])"],
                text=True,
                capture_output=True,
                check=True,
                timeout=5,
            ).stdout.strip()
            if out and tuple(int(x) for x in out.strip("()").split(",")) >= (3, 11):
                return cand
        except (FileNotFoundError, subprocess.CalledProcessError, subprocess.TimeoutExpired):
            continue
    return None


def check_prereqs(
    llvm_config: str | None = None,
    seed_mode: bool = False,
    require_rustup: bool = False,
) -> list[Prereq]:
    rustc = which("rustc")
    cargo = which("cargo")
    cmake = which("cmake")
    ninja = which("ninja")
    # `cl` is MSVC's C/C++ compiler; on Windows it is the canonical toolchain
    # (put on PATH by a VS/Build-Tools environment, e.g. the portable envrun).
    cc = which("cc") or which("clang") or which("gcc") or which("cl")
    fixed_git = fixed_git_executable()
    git = str(fixed_git) if fixed_git is not None else None
    py = find_python_ge_311()
    # cmake/ninja are only needed to build LLVM in-tree; an external --llvm-config
    # skips that, so they are not required in that mode.
    llvm_external = bool(llvm_config)
    # A system Rust toolchain is only needed to mint the GENESIS adapter. Do
    # not even present stock rustc/cargo as prerequisites in seed mode: the
    # pinned Trust seed is the complete stage0 authority.
    checks = []
    if not seed_mode:
        checks.extend(
            [
                Prereq("rustc", rustc, tool_version(rustc) if rustc else "missing", True, bool(rustc)),
                Prereq("cargo", cargo, tool_version(cargo) if cargo else "missing", True, bool(cargo)),
            ]
        )
    checks.extend([
        Prereq("cmake", cmake, (tool_version(cmake) if cmake else ("not needed (external LLVM)" if llvm_external else "missing — `brew install cmake`")), not llvm_external, bool(cmake) or llvm_external),
        Prereq("ninja", ninja, (tool_version(ninja) if ninja else ("not needed (external LLVM)" if llvm_external else "missing — `brew install ninja`")), not llvm_external, bool(ninja) or llvm_external),
        Prereq("C compiler", cc, tool_version(cc) if cc else "missing", True, bool(cc)),
        Prereq(
            "git",
            git,
            tool_version(git, environment=_provenance_git_environment())
            if git
            else "missing",
            True,
            bool(git),
        ),
        Prereq(
            "python ≥ 3.11",
            py,
            tool_version(py) if py else "missing — install python@3.11 or newer",
            True,
            bool(py),
        ),
    ])
    rustup = find_rustup()
    checks.append(
        Prereq(
            "rustup",
            rustup,
            tool_version(rustup)
            if rustup
            else (
                "missing — `brew install rustup` (required for toolchain registration)"
                if require_rustup
                else "not needed for this non-registering invocation"
            ),
            require_rustup,
            bool(rustup) or not require_rustup,
        )
    )
    if platform.system().lower() == "darwin":
        # The seed's targo dynamically links Homebrew's libgit2 (and libssh2
        # via it): on a bare machine the seed stage0 crashes on first use with
        # a dyld "Library not loaded" abort without it. Learned the hard way —
        # uninstalling stock rust cascaded libgit2 away mid-build.
        libgit2 = next(
            (p for p in ("/opt/homebrew/opt/libgit2", "/usr/local/opt/libgit2") if Path(p).is_dir()),
            None,
        )
        checks.append(
            Prereq(
                "libgit2",
                libgit2,
                "present" if libgit2 else "missing — `brew install libgit2` (the seed targo links it)",
                seed_mode,
                bool(libgit2) or not seed_mode,
            )
        )
    return checks


def print_prereqs(prereqs: list[Prereq]) -> None:
    width = max(len(p.name) for p in prereqs)
    for p in prereqs:
        mark = "✓" if p.ok else "✗"
        path = p.path or "(not found)"
        print(f"  {mark} {p.name:<{width}} {path}  — {p.detail}")


def ensure_local_genesis_stage0(root: Path, host: str, force: bool) -> Path:
    """Run create_local_genesis_stage0.py to materialize build/<host>/genesis-stage0.

    The adapter must live OUTSIDE bootstrap.py's managed bin_root
    (build/<host>/stage0): download_toolchain() wipes and re-downloads any
    configured stage0 rustc/cargo under that root whenever the pinned stage0
    date advances (rustc-stamp mismatch), which deletes the genesis adapter
    and reintroduces the missing-payload failure this script exists to solve.
    A stamped-empty stage0 dir also makes the no-force "reuse" path a trap, so
    reuse only a root that actually contains bin/trustc.
    """
    out = root / "build" / host / "genesis-stage0"
    if (out / "bin" / "trustc").exists() and not force:
        print(f"  reusing existing genesis stage0 at {out}")
        return out
    script = root / "scripts" / "create_local_genesis_stage0.py"
    args = [
        sys.executable, str(script), "--repo-root", str(root), "--host", host,
        "--out", str(out), "--force",
    ]
    subprocess.run(args, check=True)
    return out


def parse_stage0_pins(root: Path) -> tuple[dict[str, str], dict[str, str]]:
    """Parse `src/stage0` into (scalar pins, payload-path -> sha256 map)."""
    pins: dict[str, str] = {}
    payloads: dict[str, str] = {}
    stage0 = root / "src" / "stage0"
    if not stage0.is_file():
        return pins, payloads
    for line in stage0.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        key, _, value = line.partition("=")
        if key.startswith("dist/"):
            payloads[key] = value
        else:
            pins[key] = value
    return pins, payloads


def missing_seed_payloads(root: Path, payloads: dict[str, str]) -> list[str]:
    base = root / "bootstrap" / "trust-stage0"
    return [rel for rel in payloads if not (base / rel).is_file()]


def seed_ledger_release(root: Path) -> tuple[str, str] | None:
    """Read (repo, tag) from the seed ledger's `[release]` block.

    `bootstrap/trust-stage0/seed-ledger.toml` is the checked-in declaration of
    where the admitted-internal seed lives (the same source
    scripts/fetch_trust_stage0_payloads.py consumes), so fetching from it
    invents nothing.
    """
    import tomllib  # main() re-execs onto python >= 3.11 before this runs

    ledger = root / "bootstrap" / "trust-stage0" / "seed-ledger.toml"
    if not ledger.is_file():
        return None
    try:
        data = tomllib.loads(ledger.read_text(encoding="utf-8"))
    except (OSError, tomllib.TOMLDecodeError):
        return None
    release = data.get("release")
    if not isinstance(release, dict):
        return None
    repo, tag = release.get("repo"), release.get("tag")
    if not isinstance(repo, str) or not isinstance(tag, str) or not repo or not tag:
        return None
    return repo, tag


def fetch_seed_payloads(root: Path, date: str, attempts: int = 2) -> bool:
    """Fetch the pinned seed release into the canonical dist dir via `gh`.

    The release coordinates come from the seed ledger
    (`bootstrap/trust-stage0/seed-ledger.toml` `[release]`), so the download
    rides the caller's `gh` auth. Integrity does NOT depend on this transport:
    every payload is re-hashed against the `src/stage0` SHA-256 pins by
    `validate_seed` afterwards.
    """
    gh = which("gh")
    if not gh:
        print("  gh not found — cannot fetch the pinned Trust seed release")
        return False
    release = seed_ledger_release(root)
    if release is None:
        print("  seed ledger declares no [release]; cannot fetch the pinned seed")
        return False
    repo, tag = release
    dest = root / "bootstrap" / "trust-stage0" / "dist" / date
    dest.mkdir(parents=True, exist_ok=True)
    for attempt in range(1, attempts + 1):
        rc = subprocess.run(
            [
                gh, "release", "download", tag, "--repo", repo,
                "--dir", str(dest), "--pattern", "*.tar.xz", "--clobber",
            ],
            cwd=str(root),
        ).returncode
        if rc == 0:
            return True
        print(f"  gh release download {tag} failed (attempt {attempt}/{attempts})")
    return False


def validate_seed(root: Path) -> bool:
    """Fail-closed digest validation of the materialized seed payloads."""
    rc = subprocess.run(
        [sys.executable, str(root / "scripts" / "check_seed_freshness.py"), "--require-payloads"],
        cwd=str(root),
    ).returncode
    return rc == 0


def resolve_seed(root: Path, allow_fetch: bool) -> bool:
    """Materialize + validate the pinned Trust stage0 seed. True = usable."""
    pins, payloads = parse_stage0_pins(root)
    date = pins.get("compiler_date")
    if not date or not payloads:
        print("  src/stage0 declares no pinned Trust seed payloads")
        return False
    missing = missing_seed_payloads(root, payloads)
    if missing:
        print(f"  {len(missing)}/{len(payloads)} pinned payloads not materialized")
        if not allow_fetch:
            return False
        print("  fetching the seed release declared in the seed ledger ...")
        if not fetch_seed_payloads(root, date):
            return False
        missing = missing_seed_payloads(root, payloads)
        if missing:
            print(f"  still missing after fetch: {missing}")
            return False
    print("  validating payload digests against src/stage0 (fail-closed) ...")
    return validate_seed(root)


def quarantine_seed_stage0(root: Path, host: str) -> Path | None:
    """Move an extracted seed aside so provenance can observe fresh hydration.

    The move is same-filesystem and recoverable.  It deliberately targets only
    the exact generated `build/<host>/stage0` directory; pinned archives remain
    untouched.  The caller removes the quarantine only after the stage-tool
    receipt passes direct immutable-lineage verification.
    """
    host_component = Path(host)
    if (
        not host
        or host_component.is_absolute()
        or host_component.parts != (host,)
        or host in {".", ".."}
    ):
        raise RuntimeError(f"unsafe host component for fresh seed materialization: {host!r}")
    build_root = root / "build"
    if build_root.is_symlink():
        raise RuntimeError(f"fresh seed build directory must not be a symlink: {build_root}")
    host_root = build_root / host
    if host_root.is_symlink():
        raise RuntimeError(f"fresh seed host directory must not be a symlink: {host_root}")
    try:
        host_root.resolve(strict=False).relative_to(build_root.resolve(strict=False))
    except (OSError, ValueError) as error:
        raise RuntimeError(
            f"fresh seed host directory escapes the checkout build root: {host_root}"
        ) from error
    stage0 = host_root / "stage0"
    quarantine = stage0.with_name("stage0.preexisting-fresh-seed")
    if os.path.lexists(quarantine):
        if quarantine.is_symlink() or not quarantine.is_dir():
            raise RuntimeError(f"fresh seed backup is not a real directory: {quarantine}")
        if os.path.lexists(stage0):
            raise RuntimeError(
                "an interrupted fresh-seed run left both the replacement and backup; "
                f"refusing to choose or delete either: {stage0}, {quarantine}"
            )
        print(f"  resuming interrupted fresh-seed quarantine -> {quarantine}")
        print("  x.py must now hydrate stage0 from the checksum-validated archives")
        return quarantine
    if not os.path.lexists(stage0):
        print(f"  fresh seed requested; {stage0} is already absent")
        return None
    if stage0.is_symlink() or not stage0.is_dir():
        raise RuntimeError(f"fresh seed target must be a real directory: {stage0}")

    try:
        os.replace(stage0, quarantine)
    except OSError as error:
        raise RuntimeError(
            f"could not quarantine pre-existing seed compiler {stage0}: {error}"
        ) from error
    print(f"  quarantined pre-existing seed compiler -> {quarantine}")
    print("  x.py must now hydrate stage0 from the checksum-validated archives")
    return quarantine


def recover_seed_stage0_quarantine(
    root: Path,
    host: str,
    quarantine: Path | None,
) -> None:
    """Restore the quarantine only when no replacement stage0 was materialized."""
    if quarantine is None or not os.path.lexists(quarantine):
        return
    stage0 = root / "build" / host / "stage0"
    if os.path.lexists(stage0):
        print(f"  preserved failed-run seed backup at {quarantine}")
        return
    try:
        os.replace(quarantine, stage0)
    except OSError as error:
        print(f"  WARNING: could not restore seed backup {quarantine}: {error}")
        return
    print(f"  restored pre-existing seed compiler after failed setup -> {stage0}")


def discard_seed_stage0_quarantine(
    root: Path,
    host: str,
    quarantine: Path | None,
) -> None:
    """Remove the generated backup after fresh hydration passes provenance."""
    if quarantine is None or not os.path.lexists(quarantine):
        return
    stage0 = root / "build" / host / "stage0"
    expected_parent = stage0.parent
    if (
        quarantine.parent != expected_parent
        or quarantine.name != "stage0.preexisting-fresh-seed"
        or quarantine.is_symlink()
        or not quarantine.is_dir()
    ):
        raise RuntimeError(f"refusing unsafe seed backup cleanup target: {quarantine}")
    if not stage0.is_dir() or stage0.is_symlink():
        raise RuntimeError(
            f"refusing seed backup cleanup without a fresh real stage0 directory: {stage0}"
        )
    try:
        shutil.rmtree(quarantine)
    except OSError as error:
        raise RuntimeError(
            f"could not remove superseded seed backup {quarantine}: {error}"
        ) from error
    print(f"  removed superseded seed backup -> {quarantine}")


@dataclass(frozen=True)
class SubmoduleState:
    """One direct gitlink, resolved relative to its containing repository."""

    repository: Path
    path: Path
    display_path: str
    marker: str


@dataclass(frozen=True)
class IndexedSubmodule:
    """One submodule declaration read from the indexed .gitmodules blob."""

    name: str
    path: Path
    url: str


def _submodule_url_is_allowed(value: str) -> bool:
    """Admit only canonical, credential-free GitHub repository URLs.

    The first-party graph and its currently indexed recursive dependencies are
    all hosted on github.com.  Keeping this grammar deliberately smaller than a
    general URL parser prevents userinfo, query/fragment credentials, alternate
    ports, percent-decoding ambiguities, and command-scoped URL rewrites from
    becoming pre-verification transport authority.
    """
    prefix = "https://github.com/"
    suffix = ".git"
    if not value.startswith(prefix) or not value.endswith(suffix):
        return False
    repository = value[len(prefix) : -len(suffix)]
    parts = repository.split("/")
    if len(parts) != 2 or any(not part for part in parts):
        return False
    allowed = frozenset(
        "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789-_."
    )
    return all(
        part not in {".", ".."} and all(character in allowed for character in part)
        for part in parts
    )


def _credential_gh_executable(
    snapshot_directory: Path | None = None,
) -> Path | None:
    """Resolve the caller's explicit GitHub CLI credential facility.

    ``gh`` is not source/provenance authority: the fixed OS Git and pinned
    gitlinks remain the integrity boundary.  It is allowed only as a scoped
    credential reader for the one materialization operation below.  Resolve
    its path before entering the closed Git environment so a helper cannot be
    selected through the controlled PATH.
    """
    candidate = which("gh")
    if not candidate:
        return None
    candidate_path = Path(candidate)
    trusted = _trusted_credential_executable(candidate_path)
    if trusted is not None and not _homebrew_credential_layout(
        candidate_path, trusted
    ):
        return trusted
    if snapshot_directory is None or os.name == "nt":
        return trusted
    return _snapshot_homebrew_credential_executable(
        candidate_path, snapshot_directory
    )


_ROOT_CREDENTIAL_EXECUTABLE_PREFIXES = (
    Path("/usr"),
    Path("/bin"),
    Path("/sbin"),
)

_HOMEBREW_CREDENTIAL_LAYOUTS = (
    (Path("/opt/homebrew/bin/gh"), Path("/opt/homebrew/Cellar/gh")),
    (Path("/usr/local/bin/gh"), Path("/usr/local/Cellar/gh")),
)
_MAX_CREDENTIAL_HELPER_BYTES = 256 * 1024 * 1024


def _path_is_within(path: Path, prefix: Path) -> bool:
    return path == prefix or prefix in path.parents


def _trusted_posix_path_chain(path: Path, effective_uid: int) -> bool:
    """Validate every lexical component without silently following an alias.

    Directory write authority controls whether another user can redirect a
    later path lookup.  Symlink mode bits are not meaningful on macOS, so a
    symlink is admitted only when its owner is the current euid or root; both
    its lexical containing chain and its fully resolved target chain are
    validated separately by ``_trusted_credential_executable``.
    """
    if not path.is_absolute():
        return False
    current = Path(path.anchor)
    try:
        root_metadata = current.lstat()
    except OSError:
        return False
    root_mode = stat.S_IMODE(root_metadata.st_mode)
    if (
        not stat.S_ISDIR(root_metadata.st_mode)
        or root_metadata.st_uid not in {0, effective_uid}
        or (
            root_mode & 0o022
            and not (
                root_metadata.st_uid == 0
                and root_mode & stat.S_ISVTX
                and root_mode & 0o002
            )
        )
    ):
        return False
    components = path.parts[1:]
    for index, component in enumerate(components):
        current /= component
        try:
            metadata = current.lstat()
        except OSError:
            return False
        recognized_owner = metadata.st_uid in {0, effective_uid}
        if not recognized_owner:
            return False
        leaf = index + 1 == len(components)
        if stat.S_ISLNK(metadata.st_mode):
            continue
        if leaf:
            if not stat.S_ISREG(metadata.st_mode):
                return False
        elif not stat.S_ISDIR(metadata.st_mode):
            return False
        mode = stat.S_IMODE(metadata.st_mode)
        if mode & 0o022:
            # A root-owned sticky temporary directory (normally /tmp) does not
            # let another uid rename or unlink our private child.  This narrow
            # exception is needed for the 0700 helper snapshot below; ordinary
            # group-writable Homebrew directories remain untrusted.
            root_sticky_directory = (
                not leaf
                and stat.S_ISDIR(metadata.st_mode)
                and metadata.st_uid == 0
                and mode & stat.S_ISVTX
                and mode & 0o002
            )
            if not root_sticky_directory:
                return False
    return True


def _homebrew_credential_layout(candidate: Path, resolved: Path) -> bool:
    """Recognize only the fixed Homebrew gh alias-to-Cellar shape."""
    try:
        lexical = Path(os.path.abspath(os.fspath(candidate)))
    except (OSError, TypeError, ValueError):
        return False
    for alias, cellar in _HOMEBREW_CREDENTIAL_LAYOUTS:
        if lexical != alias:
            continue
        try:
            relative = resolved.relative_to(cellar)
        except ValueError:
            continue
        parts = relative.parts
        if (
            len(parts) == 3
            and parts[0] not in {"", ".", ".."}
            and parts[1:] == ("bin", "gh")
        ):
            return True
    return False


def _credential_source_metadata_is_allowed(
    metadata: os.stat_result, resolved: Path, effective_uid: int
) -> bool:
    """Admit an opened helper leaf, independently of mutable ancestors."""
    mode = stat.S_IMODE(metadata.st_mode)
    if (
        not stat.S_ISREG(metadata.st_mode)
        or metadata.st_nlink != 1
        or metadata.st_size <= 0
        or metadata.st_size > _MAX_CREDENTIAL_HELPER_BYTES
        or mode & 0o022
        or mode & 0o111 == 0
    ):
        return False
    if metadata.st_uid == effective_uid:
        return True
    return metadata.st_uid == 0 and any(
        _path_is_within(resolved, prefix)
        for prefix in _ROOT_CREDENTIAL_EXECUTABLE_PREFIXES
    )


def _credential_source_identity(metadata: os.stat_result) -> tuple[int, ...]:
    """Fields that must remain stable for the duration of an fd copy."""
    return (
        metadata.st_dev,
        metadata.st_ino,
        metadata.st_uid,
        metadata.st_gid,
        metadata.st_mode,
        metadata.st_nlink,
        metadata.st_size,
        metadata.st_mtime_ns,
        metadata.st_ctime_ns,
    )


def _snapshot_homebrew_credential_executable(
    candidate: Path, snapshot_directory: Path
) -> Path | None:
    """Copy an opened Homebrew gh inode into a private executable snapshot.

    Homebrew's top-level ``bin`` and ``Cellar`` directories are commonly 0775.
    They therefore cannot remain execution authority even when the gh leaf is
    owned by this uid.  Resolve only the fixed gh layout, open its leaf with
    ``O_NOFOLLOW``, validate the opened inode, and execute a 0700 copy beneath
    a freshly-created 0700 directory.  A later alias or Cellar swap cannot
    change the bytes Git runs.
    """
    try:
        effective_uid = os.geteuid()
        lexical = Path(os.path.abspath(os.fspath(candidate)))
        resolved = lexical.resolve(strict=True)
        if not _homebrew_credential_layout(lexical, resolved):
            return None

        directory_metadata = snapshot_directory.lstat()
        if (
            not stat.S_ISDIR(directory_metadata.st_mode)
            or directory_metadata.st_uid != effective_uid
            or stat.S_IMODE(directory_metadata.st_mode) != 0o700
            or snapshot_directory.resolve(strict=True) != snapshot_directory
        ):
            return None
    except (AttributeError, OSError, TypeError, ValueError):
        return None

    source_flags = os.O_RDONLY
    source_flags |= getattr(os, "O_CLOEXEC", 0)
    source_flags |= getattr(os, "O_NOFOLLOW", 0)
    destination = snapshot_directory / "gh-credential-helper"
    destination_flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
    destination_flags |= getattr(os, "O_CLOEXEC", 0)
    destination_flags |= getattr(os, "O_NOFOLLOW", 0)
    source_descriptor: int | None = None
    destination_descriptor: int | None = None
    directory_descriptor: int | None = None
    destination_created = False
    snapshot_complete = False
    try:
        source_descriptor = os.open(resolved, source_flags)
        before = os.fstat(source_descriptor)
        if not _credential_source_metadata_is_allowed(
            before, resolved, effective_uid
        ):
            return None

        destination_descriptor = os.open(
            destination, destination_flags, 0o700
        )
        destination_created = True
        os.fchmod(destination_descriptor, 0o700)
        copied = 0
        while True:
            chunk = os.read(source_descriptor, 1024 * 1024)
            if not chunk:
                break
            copied += len(chunk)
            if copied > before.st_size or copied > _MAX_CREDENTIAL_HELPER_BYTES:
                return None
            view = memoryview(chunk)
            while view:
                written = os.write(destination_descriptor, view)
                if written <= 0:
                    raise OSError("short credential helper snapshot write")
                view = view[written:]
        os.fsync(destination_descriptor)

        after = os.fstat(source_descriptor)
        snapshot_metadata = os.fstat(destination_descriptor)
        if (
            copied != before.st_size
            or _credential_source_identity(after)
            != _credential_source_identity(before)
            or not stat.S_ISREG(snapshot_metadata.st_mode)
            or snapshot_metadata.st_uid != effective_uid
            or snapshot_metadata.st_nlink != 1
            or snapshot_metadata.st_size != copied
            or stat.S_IMODE(snapshot_metadata.st_mode) != 0o700
        ):
            return None

        directory_flags = os.O_RDONLY
        directory_flags |= getattr(os, "O_CLOEXEC", 0)
        directory_flags |= getattr(os, "O_DIRECTORY", 0)
        directory_flags |= getattr(os, "O_NOFOLLOW", 0)
        directory_descriptor = os.open(snapshot_directory, directory_flags)
        os.fsync(directory_descriptor)
        snapshot_complete = True
    except OSError:
        return None
    finally:
        for descriptor in (
            directory_descriptor,
            destination_descriptor,
            source_descriptor,
        ):
            if descriptor is not None:
                try:
                    os.close(descriptor)
                except OSError:
                    pass
        if destination_created and not snapshot_complete:
            try:
                destination.unlink(missing_ok=True)
            except OSError:
                pass

    trusted_snapshot = _trusted_credential_executable(destination)
    if trusted_snapshot != destination:
        try:
            destination.unlink(missing_ok=True)
        except OSError:
            pass
        return None
    return trusted_snapshot


def _trusted_credential_executable(candidate: Path) -> Path | None:
    """Return one canonical, cross-user-immutable credential helper path.

    Check the complete lexical alias chain, resolve it, then check the complete
    canonical chain and the opened leaf.  Homebrew's commonly group-writable
    top-level directories intentionally fail this direct-path gate and are
    handled by the private fd-bound snapshot above.  The returned canonical
    path is what Git executes, so replacing a trusted alias afterward has no
    effect.

    Same-euid replacement is the local-principal boundary.  A root-owned leaf
    is accepted only in the conventional immutable system prefixes; an
    attacker-owned mode-0755 binary is not made trustworthy by lacking write
    bits for group/other.
    """
    if os.name == "nt":
        # Windows ownership/ACL validation is not expressible through st_uid.
        # Accept only the standard system-wide GitHub CLI installation, never a
        # PATH-only executable in a caller-controlled directory.
        standard = (
            Path("C:/Program Files/GitHub CLI/gh.exe"),
            Path("C:/Program Files (x86)/GitHub CLI/gh.exe"),
        )
        try:
            resolved = candidate.resolve(strict=True)
        except OSError:
            return None
        if not any(resolved == path.resolve(strict=False) for path in standard):
            return None
        try:
            metadata = resolved.stat()
        except OSError:
            return None
        return resolved if stat.S_ISREG(metadata.st_mode) and os.access(resolved, os.X_OK) else None

    try:
        effective_uid = os.geteuid()
        lexical = Path(os.path.abspath(os.fspath(candidate)))
        if not _trusted_posix_path_chain(lexical, effective_uid):
            return None
        resolved = lexical.resolve(strict=True)
        if not _trusted_posix_path_chain(resolved, effective_uid):
            return None
        metadata = resolved.lstat()
    except (AttributeError, OSError, ValueError):
        return None

    if (
        not stat.S_ISREG(metadata.st_mode)
        or not os.access(resolved, os.X_OK)
        or stat.S_IMODE(metadata.st_mode) & 0o111 == 0
        or stat.S_IMODE(metadata.st_mode) & 0o022
    ):
        return None
    if metadata.st_uid != effective_uid:
        root_system_leaf = metadata.st_uid == 0 and any(
            _path_is_within(resolved, prefix)
            for prefix in _ROOT_CREDENTIAL_EXECUTABLE_PREFIXES
        )
        if not root_system_leaf:
            return None

    flags = os.O_RDONLY
    flags |= getattr(os, "O_CLOEXEC", 0)
    flags |= getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(resolved, flags)
        try:
            opened = os.fstat(descriptor)
        finally:
            os.close(descriptor)
    except OSError:
        return None
    if (
        not stat.S_ISREG(opened.st_mode)
        or opened.st_dev != metadata.st_dev
        or opened.st_ino != metadata.st_ino
        or opened.st_uid != metadata.st_uid
        or stat.S_IMODE(opened.st_mode) & 0o111 == 0
        or stat.S_IMODE(opened.st_mode) & 0o022
    ):
        return None
    return resolved


def _revalidate_credential_gh_executable(path: Path) -> None:
    """Recheck the canonical helper immediately before Git may execute it."""
    if _trusted_credential_executable(path) != path:
        raise RuntimeError(
            f"GitHub credential helper lost executable authority before use: {path}"
        )


def _read_only_gh_credential_helper(gh: Path) -> str:
    """Return a command-scoped helper that forwards only credential ``get``.

    Git calls helpers again with ``store`` after a successful authentication.
    Deliberately ignoring every operation except ``get`` keeps this bootstrap
    path unable to persist a prompted token or mutate ``gh`` authentication.
    """
    executable = shlex.quote(gh.as_posix())
    scoped_environment = " ".join(
        f"{name}={shlex.quote(value)}"
        for name, value in _credential_gh_environment().items()
    )
    if scoped_environment:
        scoped_environment += " "
    return (
        "credential.helper=!f() { if test \"$1\" = get; then "
        f"{scoped_environment}exec {executable} auth git-credential get; fi; "
        "exit 0; }; f"
    )


def _caller_gh_config_directory() -> str | None:
    """Resolve gh's config directory without exposing the caller's HOME to Git."""
    explicit = os.environ.get("GH_CONFIG_DIR")
    if explicit:
        candidate = Path(explicit)
    elif os.environ.get("XDG_CONFIG_HOME"):
        candidate = Path(os.environ["XDG_CONFIG_HOME"]) / "gh"
    elif os.name == "nt" and os.environ.get("APPDATA"):
        candidate = Path(os.environ["APPDATA"]) / "GitHub CLI"
    elif os.environ.get("HOME"):
        candidate = Path(os.environ["HOME"]) / ".config" / "gh"
    else:
        return None
    rendered = os.fspath(candidate)
    if "\0" in rendered or not candidate.is_absolute():
        return None
    return rendered


def _credential_gh_environment() -> dict[str, str]:
    """Ambient paths visible to gh itself, never to the transport Git child."""
    scoped: dict[str, str] = {}
    gh_config_directory = _caller_gh_config_directory()
    if gh_config_directory is not None:
        scoped["GH_CONFIG_DIR"] = gh_config_directory
    names = ["HOME"]
    if os.name == "nt":
        names.extend(("APPDATA", "LOCALAPPDATA", "USERPROFILE"))
    for name in names:
        value = os.environ.get(name)
        if not value or "\0" in value:
            continue
        candidate = Path(value)
        if candidate.is_absolute():
            scoped[name] = value
    return scoped


def _submodule_materialization_environment() -> dict[str, str]:
    """Open only the user credential lookup needed by submodule transport.

    All Git config, executable, protocol, proxy, and repository controls stay
    closed exactly as they are for provenance reads.  The caller's home/config
    configuration and home paths are embedded only as shell assignments on the
    absolute ``gh`` helper command, so the Git child keeps this closed mapping
    and libcurl cannot consult the caller's ``~/.netrc``. Ambient tokens,
    askpass programs, Git config, proxies, and dynamic-loader settings are never
    inherited.
    """
    env = _provenance_git_environment()
    env.pop("GIT_ASKPASS", None)
    env["GIT_TERMINAL_PROMPT"] = "1" if sys.stdin.isatty() else "0"
    return env


def _submodule_auth_config(
    snapshot_directory: Path,
) -> tuple[list[str], Path | None]:
    """Return late ``-c`` options for read-only gh/terminal authentication."""
    gh = _credential_gh_executable(snapshot_directory)
    options = ["-c", "credential.interactive=always"]
    if gh is not None:
        options.extend(("-c", _read_only_gh_credential_helper(gh)))
    return options, gh


def _credential_snapshot_parent() -> Path | None:
    """Return a fixed parent where another uid cannot replace our temp dir."""
    if os.name == "nt":
        return None
    candidates = (
        (Path("/private/tmp"), Path("/tmp"))
        if platform.system().lower() == "darwin"
        else (Path("/tmp"), Path("/var/tmp"))
    )
    for candidate in candidates:
        try:
            resolved = candidate.resolve(strict=True)
            metadata = resolved.lstat()
        except OSError:
            continue
        mode = stat.S_IMODE(metadata.st_mode)
        immutable_parent = mode & 0o022 == 0
        sticky_world_parent = mode & 0o002 and mode & stat.S_ISVTX
        if (
            stat.S_ISDIR(metadata.st_mode)
            and metadata.st_uid == 0
            and (immutable_parent or sticky_world_parent)
        ):
            return resolved
    raise RuntimeError(
        "no fixed root-owned immutable or sticky temporary directory is "
        "available for the private GitHub credential-helper snapshot"
    )


def _terminate_submodule_process_tree(
    process: subprocess.Popen[bytes], *, leader_already_exited: bool = False
) -> None:
    """Hard-stop the transport/helper process group and confirm it is gone."""
    tree_signal_succeeded = False
    if os.name == "nt":
        taskkill = Path("C:/Windows/System32/taskkill.exe")
        if taskkill.is_file():
            try:
                result = subprocess.run(
                    [str(taskkill), "/PID", str(process.pid), "/T", "/F"],
                    check=False,
                    stdin=subprocess.DEVNULL,
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL,
                    timeout=10,
                )
                tree_signal_succeeded = result.returncode == 0
            except (OSError, subprocess.TimeoutExpired):
                pass
    else:
        try:
            os.killpg(process.pid, signal.SIGKILL)
            tree_signal_succeeded = True
        except (ProcessLookupError, PermissionError, OSError):
            pass
    if process.poll() is None:
        try:
            process.kill()
        except OSError:
            pass
    try:
        process.wait(timeout=10)
    except (OSError, subprocess.TimeoutExpired):
        pass
    if process.poll() is None:
        raise RuntimeError(
            f"submodule Git process {process.pid} survived forced termination"
        )
    if os.name == "nt":
        if not tree_signal_succeeded:
            if leader_already_exited:
                # taskkill cannot reliably rediscover a descendant after its
                # parent has already exited. Fixed Git is expected to wait for
                # normal transports; deliberately detached same-user helpers
                # remain the documented non-Job-Object Windows boundary.
                return
            raise RuntimeError(
                "could not confirm Windows submodule descendant-tree termination"
            )
        return

    # The session/process-group leader can exit before its descendants. Probe
    # the original group for a short bounded interval instead of equating a
    # reaped leader with complete transport/helper cleanup.
    deadline = time.monotonic() + 2
    while True:
        try:
            os.killpg(process.pid, 0)
        except ProcessLookupError:
            return
        except PermissionError:
            # Darwin can report EPERM briefly while a killed descendant is a
            # reparented zombie. Treat it as "not yet confirmed" and require
            # ESRCH before the bounded deadline rather than accepting it.
            pass
        if time.monotonic() >= deadline:
            raise RuntimeError(
                f"submodule process group {process.pid} survived forced termination"
            )
        time.sleep(0.02)


def _wait_submodule_process_group(
    process: subprocess.Popen[bytes], timeout_seconds: int | float
) -> int:
    """Observe a POSIX leader without reaping it, then retire its whole group.

    ``Popen.wait`` reaps the leader immediately, allowing its PID/process-group
    identifier to be reused before a post-success descendant check. POSIX
    ``waitid(..., WNOWAIT)`` keeps the exited leader waitable until the group is
    killed and confirmed. Windows has no equivalent in the standard library;
    its fixed Git is expected to wait for normal transports and taskkill is
    attempted after the leader returns.
    """
    if os.name == "nt" or not all(
        hasattr(os, name)
        for name in ("waitid", "P_PID", "WEXITED", "WNOWAIT", "WNOHANG")
    ):
        return_code = process.wait(timeout=timeout_seconds)
        _terminate_submodule_process_tree(
            process, leader_already_exited=True
        )
        return return_code

    deadline = time.monotonic() + timeout_seconds
    while True:
        result = os.waitid(
            os.P_PID,
            process.pid,
            os.WEXITED | os.WNOWAIT | os.WNOHANG,
        )
        if result is not None:
            _terminate_submodule_process_tree(
                process, leader_already_exited=True
            )
            if process.returncode is None:
                raise RuntimeError(
                    "submodule Git leader was not reaped after group termination"
                )
            return process.returncode
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise subprocess.TimeoutExpired(process.args, timeout_seconds)
        time.sleep(min(0.02, remaining))


def _relay_bounded_submodule_output(stream: object) -> None:
    """Drain child output completely while bounding terminal/CI disclosure."""
    emitted = 0
    truncated = False

    def write_diagnostic(data: bytes) -> None:
        try:
            binary = getattr(sys.stderr, "buffer", None)
            if binary is not None:
                binary.write(data)
                binary.flush()
            else:
                sys.stderr.write(data.decode("utf-8", errors="replace"))
                sys.stderr.flush()
        except (BrokenPipeError, OSError, ValueError):
            pass

    try:
        while True:
            chunk = stream.read(64 * 1024)  # type: ignore[attr-defined]
            if not chunk:
                break
            remaining = max(0, SUBMODULE_UPDATE_OUTPUT_LIMIT_BYTES - emitted)
            if remaining:
                visible = chunk[:remaining]
                write_diagnostic(visible)
                emitted += len(visible)
            if len(chunk) > remaining and not truncated:
                truncated = True
                write_diagnostic(
                    b"\n[trust bootstrap: submodule diagnostic output truncated "
                    + f"after {SUBMODULE_UPDATE_OUTPUT_LIMIT_BYTES} bytes]\n".encode()
                )
    except (OSError, ValueError):
        pass
    finally:
        try:
            stream.close()  # type: ignore[attr-defined]
        except (OSError, ValueError):
            pass


def _run_submodule_update_process(
    command: list[str],
    *,
    environment: dict[str, str],
    timeout_seconds: int | float,
    credential_gh: Path | None,
) -> subprocess.CompletedProcess[bytes]:
    """Run one targeted update with a process-tree deadline.

    Output is drained concurrently and relayed to the invoking terminal/CI log
    up to a fixed byte ceiling.  It is never accumulated in Python memory or a
    temporary file, while stdin remains attached for the explicitly enabled
    terminal credential prompt.
    """
    if credential_gh is not None:
        _revalidate_credential_gh_executable(credential_gh)
    options: dict[str, object] = {
        "env": environment,
        "stdin": None,
        "stdout": subprocess.PIPE,
        "stderr": subprocess.STDOUT,
    }
    if os.name == "nt":
        options["creationflags"] = getattr(subprocess, "CREATE_NEW_PROCESS_GROUP", 0)
    else:
        options["start_new_session"] = True
    process: subprocess.Popen[bytes] = subprocess.Popen(command, **options)
    assert process.stdout is not None
    relay = threading.Thread(
        target=_relay_bounded_submodule_output,
        args=(process.stdout,),
        name="trust-submodule-output",
        daemon=True,
    )
    relay.start()
    try:
        return_code = _wait_submodule_process_group(process, timeout_seconds)
    except subprocess.TimeoutExpired as error:
        _terminate_submodule_process_tree(process)
        raise subprocess.TimeoutExpired(command, timeout_seconds) from error
    except BaseException as error:
        try:
            _terminate_submodule_process_tree(process)
        except BaseException as termination_error:
            error.add_note(
                f"submodule process-tree termination also failed: {termination_error}"
            )
        raise
    finally:
        relay.join(timeout=10)
        if relay.is_alive():
            # An escaped descendant may still hold the inherited pipe. Closing
            # our read end keeps cleanup bounded; the relay thread is daemonized.
            try:
                process.stdout.close()
            except (OSError, ValueError):
                pass
            relay.join(timeout=1)
    if credential_gh is not None:
        _revalidate_credential_gh_executable(credential_gh)
    return subprocess.CompletedProcess(command, return_code)


def _parse_git_config_records(
    raw: bytes, repository: Path, scope: str
) -> list[tuple[str, str]]:
    """Decode one NUL-framed Git config scope without exposing its values."""
    records: list[tuple[str, str]] = []
    for raw_record in raw.split(b"\0"):
        if not raw_record:
            continue
        raw_key, separator, raw_value = raw_record.partition(b"\n")
        if not separator:
            raise RuntimeError(
                f"malformed {scope} Git config record in {repository}"
            )
        try:
            key = raw_key.decode("utf-8", errors="strict").lower()
            value = raw_value.decode("utf-8", errors="strict").strip()
        except UnicodeDecodeError as error:
            raise RuntimeError(
                f"non-UTF-8 {scope} Git config in {repository}"
            ) from error
        records.append((key, value))
    return records


def _read_repository_git_config_scope(
    repository: Path, scope: str
) -> list[tuple[str, str]]:
    """Read exactly one repository-owned config scope with includes disabled."""
    if scope not in {"local", "worktree"}:
        raise ValueError(f"unsupported Git config scope: {scope}")
    command = _controlled_git_command(
        [
            "-C",
            str(repository),
            "config",
            f"--{scope}",
            "--no-includes",
            "--null",
            "--list",
        ]
    )
    try:
        result = subprocess.run(
            command,
            capture_output=True,
            check=False,
            env=_provenance_git_environment(),
            timeout=30,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        raise RuntimeError(
            f"could not inspect {scope} Git authority in {repository}: {error}"
        ) from error
    if result.returncode != 0:
        detail = (
            result.stderr.decode("utf-8", errors="replace").strip()
            or "unknown Git error"
        )
        raise RuntimeError(
            f"could not inspect {scope} Git authority in {repository}: {detail}"
        )
    return _parse_git_config_records(result.stdout, repository, scope)


def _git_config_bool(value: str) -> bool | None:
    lowered = value.lower()
    if lowered in {"", "true", "yes", "on", "1"}:
        return True
    if lowered in {"false", "no", "off", "0"}:
        return False
    return None


def _repository_git_config_records(
    repository: Path,
) -> list[tuple[str, str, str]]:
    """Return every effective repository-owned scope, excluding includes."""
    local = _read_repository_git_config_scope(repository, "local")
    records = [("local", key, value) for key, value in local]
    worktree_values = [
        value for key, value in local if key == "extensions.worktreeconfig"
    ]
    if worktree_values:
        enabled = _git_config_bool(worktree_values[-1])
        if enabled is None:
            raise RuntimeError(
                f"invalid extensions.worktreeConfig value in {repository}"
            )
        if enabled:
            records.extend(
                ("worktree", key, value)
                for key, value in _read_repository_git_config_scope(
                    repository, "worktree"
                )
            )
    return records


def _git_config_key_for_diagnostic(key: str) -> str:
    """Render a config key without echoing URL-subsection credentials."""
    if not any(token in key for token in ("://", "@", "?", "#")):
        return key
    parts = key.split(".")
    if len(parts) < 2:
        return "<redacted-config-key>"
    return f"{parts[0]}.<redacted>.{parts[-1]}"


def _reject_local_git_execution_authority(
    repository: Path, *, require_https_submodules: bool = False
) -> None:
    """Reject repo-local Git settings that can execute or redirect code.

    Global/system configuration and the process environment are removed by
    `_provenance_git_environment`. Local config is required for worktree and
    submodule bookkeeping, so inspect it with includes disabled before any
    status/update/provenance command can consume it. A repository that enables
    the separate worktree config scope is rejected after that scope is also
    inspected; command-line overrides remain the final boundary.
    """
    hostile: list[str] = []
    for scope, key, value in _repository_git_config_records(repository):
        lowered = value.lower()
        section = key.split(".", 1)[0]

        executable_setting = (
            key.startswith("include.")
            or key.startswith("includeif.")
            or key == "core.sshcommand"
            or key == "core.gitproxy"
            or key == "core.askpass"
            or key == "core.attributesfile"
            or (
                key == "extensions.worktreeconfig"
                and _git_config_bool(value) is not False
            )
            or (key == "core.fsmonitor" and lowered not in {"", "false"})
            or (key == "core.hookspath" and value not in {"", "/dev/null"})
            # Git gives URL-specific HTTP/credential keys precedence over a
            # generic command-line value.  Reject the complete sections in
            # both local and worktree scope; enumerating suffixes is unsafe.
            or section in {"credential", "http", "https", "protocol", "url"}
            or key in {"core.alternaterefscommand", "diff.external", "gc.recentobjectshook"}
            or (
                key.startswith("filter.")
                and key.rsplit(".", 1)[-1] in {"clean", "smudge", "process"}
            )
            or (
                key.startswith("diff.")
                and key.rsplit(".", 1)[-1] in {"command", "textconv"}
            )
            or (key.startswith("merge.") and key.endswith(".driver"))
            or (
                key.startswith("remote.")
                and key.rsplit(".", 1)[-1]
                in {"uploadpack", "receivepack", "vcs", "proxy"}
            )
            or key == "init.templatedir"
        )
        hostile_update = (
            key.startswith("submodule.")
            and key.endswith(".update")
            and lowered != "checkout"
        )
        unsafe_submodule_url = (
            require_https_submodules
            and key.startswith("submodule.")
            and key.endswith(".url")
            and not _submodule_url_is_allowed(value)
        )
        if executable_setting or hostile_update or unsafe_submodule_url:
            hostile.append(
                f"{scope}:{_git_config_key_for_diagnostic(key)}"
            )

    if hostile:
        raise RuntimeError(
            "repository-local Git configuration contains hidden execution, update, "
            f"or transport authority in {repository}: {', '.join(sorted(set(hostile)))}"
        )

    top = subprocess.run(
        _controlled_git_command(["-C", str(repository), "rev-parse", "--show-toplevel"]),
        capture_output=True,
        check=False,
        env=_provenance_git_environment(),
        timeout=30,
    )
    if top.returncode != 0:
        detail = top.stderr.decode("utf-8", errors="replace").strip() or "unknown Git error"
        raise RuntimeError(f"could not resolve repository worktree {repository}: {detail}")
    try:
        resolved_top = Path(os.fsdecode(top.stdout).strip()).resolve(strict=True)
        resolved_repository = repository.resolve(strict=True)
    except OSError as error:
        raise RuntimeError(f"could not resolve repository worktree {repository}: {error}") from error
    if resolved_top != resolved_repository:
        raise RuntimeError(
            f"local Git worktree authority redirects {repository} to {resolved_top}"
        )


def _run_git_read(
    repository: Path, arguments: list[str]
) -> subprocess.CompletedProcess[str]:
    _reject_local_git_execution_authority(
        repository, require_https_submodules=True
    )
    result = subprocess.run(
        _controlled_git_command(["-C", str(repository), *arguments]),
        capture_output=True,
        text=True,
        check=False,
        env=_provenance_git_environment(),
        timeout=30,
    )
    if result.returncode != 0:
        detail = result.stderr.strip() or result.stdout.strip() or "unknown Git error"
        raise RuntimeError(
            f"could not inspect submodules in {repository}: {detail}"
        )
    return result


def _indexed_submodules(repository: Path) -> list[IndexedSubmodule]:
    """Validate and return direct declarations from the indexed blob.

    This gate intentionally reads ``:.gitmodules``, not the working-tree file,
    and runs before any credential helper or network process.  Git otherwise
    copies an indexed URL into local config during ``submodule update --init``;
    validating it afterward is too late to prevent credential persistence and
    diagnostic disclosure.
    """
    indexed_modules = _run_git_read(
        repository, ["ls-files", "--stage", "--", ".gitmodules"]
    )
    if not indexed_modules.stdout.strip():
        # This also fails closed if the index contains an unmapped gitlink.
        direct_status = _run_git_read(repository, ["submodule", "status"])
        if direct_status.stdout.strip():
            raise RuntimeError(
                f"indexed submodules in {repository} have no indexed "
                ".gitmodules mapping"
            )
        return []

    try:
        configured = subprocess.run(
            _controlled_git_command(
                [
                    "-C",
                    str(repository),
                    "config",
                    "--no-includes",
                    "-z",
                    "--blob",
                    ":.gitmodules",
                    "--list",
                ]
            ),
            capture_output=True,
            check=False,
            env=_provenance_git_environment(),
            timeout=30,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        raise RuntimeError(
            f"could not inspect indexed .gitmodules in {repository}"
        ) from error
    if configured.returncode != 0:
        raise RuntimeError(
            f"could not inspect indexed .gitmodules in {repository}; "
            "its contents were not printed because they may contain credentials"
        )

    declarations: dict[str, dict[str, str]] = {}
    for record_number, record in enumerate(configured.stdout.split(b"\0"), start=1):
        if not record:
            continue
        raw_key, separator, raw_value = record.partition(b"\n")
        if not separator:
            raise RuntimeError(
                f"invalid indexed .gitmodules record {record_number} in {repository}"
            )
        try:
            key = raw_key.decode("utf-8", errors="strict").lower()
            value = raw_value.decode("utf-8", errors="strict").strip()
        except UnicodeDecodeError as error:
            raise RuntimeError(
                f"non-UTF-8 indexed .gitmodules record {record_number} in {repository}"
            ) from error
        if not key.startswith("submodule.") or "." not in key[len("submodule.") :]:
            raise RuntimeError(
                f"unsupported indexed .gitmodules record {record_number} in {repository}"
            )
        declaration, variable = key.rsplit(".", 1)
        name = declaration[len("submodule.") :]
        if not name or any(ord(character) < 32 or ord(character) == 127 for character in name):
            raise RuntimeError(
                f"unsafe indexed .gitmodules name in record {record_number} of {repository}"
            )
        if variable not in {"path", "url", "update"}:
            raise RuntimeError(
                f"unsupported indexed .gitmodules key in record {record_number} of {repository}"
            )
        if variable == "update" and value.lower() != "checkout":
            raise RuntimeError(
                f"custom indexed submodule update authority is forbidden in {repository}"
            )
        fields = declarations.setdefault(name, {})
        if variable in fields:
            raise RuntimeError(
                f"duplicate indexed .gitmodules {variable} record in {repository}"
            )
        fields[variable] = value

    entries: list[IndexedSubmodule] = []
    seen_paths: set[str] = set()
    for declaration_number, (name, fields) in enumerate(
        declarations.items(), start=1
    ):
        value = fields.get("path", "")
        url = fields.get("url", "")
        if not value or not url:
            raise RuntimeError(
                f"indexed submodule declaration {declaration_number} in {repository} "
                "must have exactly one path and one URL"
            )
        path = Path(value)
        if (
            path.is_absolute()
            or ".." in path.parts
            or path == Path(".")
            or any(
                ord(character) < 32 or ord(character) == 127
                for character in value
            )
        ):
            raise RuntimeError(
                f"unsafe indexed submodule path in declaration "
                f"{declaration_number} of {repository}"
            )
        if value in seen_paths:
            raise RuntimeError(
                f"duplicate indexed submodule path in {repository}"
            )
        seen_paths.add(value)
        if not _submodule_url_is_allowed(url):
            raise RuntimeError(
                f"unsafe indexed submodule URL in declaration "
                f"{declaration_number} of {repository}; expected a canonical, "
                "credential-free https://github.com/<owner>/<repo>.git URL"
            )

        gitlink = _run_git_read(
            repository, ["ls-files", "--stage", "--", value]
        ).stdout.splitlines()
        if len(gitlink) != 1 or not gitlink[0].startswith("160000 "):
            raise RuntimeError(
                f"indexed .gitmodules path is not one gitlink in {repository}: {value}"
            )
        entries.append(IndexedSubmodule(name=name, path=path, url=url))

    # Ask Git to cross-check that no indexed gitlink lacks a declaration.
    _run_git_read(repository, ["submodule", "status"])
    return entries


def _direct_submodule_states(
    repository: Path, display_prefix: str = ""
) -> list[SubmoduleState]:
    states: list[SubmoduleState] = []
    for indexed in _indexed_submodules(repository):
        path = indexed.path
        result = _run_git_read(
            repository, ["submodule", "status", "--", path.as_posix()]
        )
        lines = result.stdout.splitlines()
        if len(lines) != 1 or not lines[0]:
            raise RuntimeError(
                f"could not determine indexed submodule state for "
                f"{repository / path}"
            )
        marker = lines[0][0]
        if marker not in {" ", "+", "-", "U"}:
            raise RuntimeError(
                f"unrecognized indexed submodule state for {repository / path}: "
                f"{lines[0]!r}"
            )
        display_path = (
            f"{display_prefix}/{path.as_posix()}"
            if display_prefix
            else path.as_posix()
        )
        states.append(SubmoduleState(repository, path, display_path, marker))
    return states


def _inspect_submodule_tree(root: Path) -> list[SubmoduleState]:
    states: list[SubmoduleState] = []

    def inspect(repository: Path, display_prefix: str) -> None:
        for state in _direct_submodule_states(repository, display_prefix):
            states.append(state)
            if state.marker == "U":
                raise RuntimeError(
                    f"unmerged indexed submodule state at {state.display_path}; "
                    "resolve the gitlink conflict before recreating bootstrap"
                )
            if state.marker != "-":
                inspect(repository / state.path, state.display_path)

    inspect(root, "")
    return states


def refuse_dirty_submodule_lockfiles(states: list[SubmoduleState]) -> None:
    """Refuse tracked lockfile loss; this gate never changes a worktree."""
    dirty: list[str] = []
    for state in states:
        if state.marker == "-":
            continue
        result = _run_git_read(
            state.repository / state.path,
            ["status", "--porcelain=v1", "--untracked-files=no", "--", "Cargo.lock"],
        )
        if result.stdout.strip():
            dirty.append(state.display_path)
    if dirty:
        locations = "\n".join(f"    - {path}/Cargo.lock" for path in dirty)
        raise RuntimeError(
            "refusing to initialize submodules because tracked Cargo.lock changes "
            "would make the source state ambiguous. No lockfile was changed.\n"
            f"{locations}\n"
            "Commit the changes, stash them with `git -C <submodule> stash push -- "
            "Cargo.lock`, or deliberately discard them with `git -C <submodule> "
            "restore -- Cargo.lock`; then rerun this command."
        )


def _initialize_missing_submodules(
    repository: Path,
    env: dict[str, str],
    auth_config: list[str],
    credential_gh: Path | None,
    display_prefix: str = "",
) -> int:
    """Initialize missing gitlinks without moving any materialized sibling."""
    initialized = 0
    for state in _direct_submodule_states(repository, display_prefix):
        if state.marker == "U":
            raise RuntimeError(
                f"unmerged indexed submodule state at {state.display_path}; "
                "resolve the gitlink conflict before recreating bootstrap"
            )
        if state.marker == "-":
            print(f"  initializing {state.display_path}")
            command = _controlled_git_command(
                [
                    *auth_config,
                    "-C",
                    str(repository),
                    "submodule",
                    "update",
                    "--checkout",
                    "--init",
                    "--",
                    state.path.as_posix(),
                ]
            )
            try:
                result = _run_submodule_update_process(
                    command,
                    environment=env,
                    timeout_seconds=SUBMODULE_UPDATE_TIMEOUT_SECONDS,
                    credential_gh=credential_gh,
                )
            except subprocess.TimeoutExpired as error:
                raise RuntimeError(
                    f"submodule materialization timed out after "
                    f"{SUBMODULE_UPDATE_TIMEOUT_SECONDS}s at {state.display_path}; "
                    "Git was terminated. Check network access and `gh auth status`, "
                    "then rerun; no existing materialized sibling was moved."
                ) from error
            except OSError as error:
                raise RuntimeError(
                    f"could not launch fixed Git to materialize "
                    f"{state.display_path}: {error}"
                ) from error
            if result.returncode != 0:
                raise RuntimeError(
                    f"submodule materialization failed for {state.display_path} "
                    f"(Git exit {result.returncode}). Run `gh auth login` with access "
                    "to the private first-party repositories, confirm `gh auth status`, "
                    "and rerun. Authentication was scoped to this update and was not "
                    "written to Git config."
                )
            initialized += 1
        initialized += _initialize_missing_submodules(
            repository / state.path,
            env,
            auth_config,
            credential_gh,
            state.display_path,
        )
    return initialized


def ensure_submodules(root: Path) -> None:
    """Materialize the complete indexed recursive submodule graph safely.

    bootstrap's own `git submodule update` is disabled in the generated config
    (`submodules = false`) so it cannot reset deliberately-advanced pins. This
    routine inspects every indexed gitlink recursively and targets only missing
    children; already-materialized siblings (including `+` states) are never
    passed to `git submodule update`.

    Every indexed URL is validated as canonical, credential-free github.com
    HTTPS before Git may initialize it. User SSH config, ProxyCommand, askpass,
    PATH, and repo-local/worktree transport or update commands are never
    bootstrap authority. Only this targeted update may read an existing ``gh
    auth login`` through a read-only command-scoped helper or prompt on the
    controlling terminal. The helper ignores Git's ``store`` operation, and
    the update has hard time and diagnostic-output bounds.
    """
    before = _inspect_submodule_tree(root)
    refuse_dirty_submodule_lockfiles(before)
    missing = [state for state in before if state.marker == "-"]
    if not missing:
        print("  complete indexed recursive submodule graph already materialized")
        scrub_pat_from_remotes(root)
        return

    snapshot_parent = _credential_snapshot_parent()
    with tempfile.TemporaryDirectory(
        prefix="trust-gh-helper-", dir=snapshot_parent
    ) as temporary_directory:
        snapshot_directory = Path(temporary_directory)
        if os.name != "nt":
            snapshot_directory.chmod(0o700)
        _materialize_missing_submodules(root, snapshot_directory)


def _materialize_missing_submodules(
    root: Path, snapshot_directory: Path
) -> None:
    """Run missing updates while the private credential snapshot exists."""

    env = _submodule_materialization_environment()
    auth_config, gh = _submodule_auth_config(snapshot_directory)
    terminal_fallback = env["GIT_TERMINAL_PROMPT"] == "1"
    credential_source = (
        f"read-only gh helper ({gh})"
        if gh is not None
        else "no gh credential helper"
    )
    credential_source += (
        " with terminal fallback"
        if terminal_fallback
        else "; terminal prompting disabled (no controlling stdin)"
    )
    print("  using fixed OS Git with HTTPS-only submodule transport")
    print(f"  authentication scope: this update only; {credential_source}")
    try:
        initialized = _initialize_missing_submodules(root, env, auth_config, gh)
    except BaseException as materialization_error:
        try:
            scrub_pat_from_remotes(root)
        except BaseException as scrub_error:
            materialization_error.add_note(
                "post-failure credential cleanup also failed closed: "
                f"{scrub_error}"
            )
        raise
    scrub_pat_from_remotes(root)
    after = _inspect_submodule_tree(root)
    still_missing = [state.display_path for state in after if state.marker == "-"]
    if still_missing:
        raise RuntimeError(
            "recursive submodule initialization completed without materializing: "
            + ", ".join(still_missing)
        )
    print(f"  materialized {initialized} missing indexed submodule(s)")


def _clean_remote_url_credentials(url: str) -> str:
    """Remove HTTP userinfo without reproducing it in a diagnostic."""
    if any(ord(character) < 32 or ord(character) == 127 for character in url):
        raise RuntimeError("origin remote URL contains control characters")
    lowered = url.lower()
    if not (lowered.startswith("https://") or lowered.startswith("http://")):
        return url
    if "?" in url or "#" in url:
        raise RuntimeError(
            "origin HTTP remote URL contains a query or fragment that may carry "
            "credentials; replace it with a credential-free URL"
        )
    scheme_end = url.index("://") + 3
    path_start = url.find("/", scheme_end)
    if path_start < 0:
        path_start = len(url)
    authority = url[scheme_end:path_start]
    if "@" not in authority:
        return url
    clean_authority = authority.rsplit("@", 1)[1]
    if not clean_authority:
        raise RuntimeError("origin HTTP remote URL has an invalid authority")
    return url[:scheme_end] + clean_authority + url[path_start:]


def _replace_git_config_values(
    repository: Path, scope: str, key: str, values: list[str]
) -> None:
    """Replace every value for one known key in one audited config scope."""
    if not values:
        return
    commands = [
        ["config", f"--{scope}", "--replace-all", key, values[0]],
        *(
            ["config", f"--{scope}", "--add", key, value]
            for value in values[1:]
        ),
    ]
    for arguments in commands:
        try:
            result = subprocess.run(
                _controlled_git_command(["-C", str(repository), *arguments]),
                capture_output=True,
                check=False,
                env=_provenance_git_environment(),
                timeout=30,
            )
        except (OSError, subprocess.TimeoutExpired) as error:
            raise RuntimeError(
                f"could not scrub embedded credentials from {repository}/origin"
            ) from error
        if result.returncode != 0:
            raise RuntimeError(
                f"could not scrub embedded credentials from {repository}/origin "
                f"(Git exit {result.returncode})"
            )


def _scrub_repository_origin_credentials(repository: Path) -> None:
    """Scrub every fetch/push URL in the accepted local config, or fail."""
    _reject_local_git_execution_authority(
        repository, require_https_submodules=True
    )
    grouped: dict[tuple[str, str], list[str]] = {}
    for scope, key, value in _repository_git_config_records(repository):
        if key in {"remote.origin.url", "remote.origin.pushurl"}:
            grouped.setdefault((scope, key), []).append(value)

    changed = False
    for (scope, key), values in grouped.items():
        cleaned = [_clean_remote_url_credentials(value) for value in values]
        if cleaned != values:
            _replace_git_config_values(repository, scope, key, cleaned)
            changed = True
    if changed:
        print(f"  scrubbed embedded credentials from {repository}/origin")

    # Re-read the edited scopes and reapply the complete authority gate. Any
    # read/edit failure is fatal; absence of an origin is represented by no key,
    # not by swallowing an arbitrary Git error.
    for _scope, key, value in _repository_git_config_records(repository):
        if key in {"remote.origin.url", "remote.origin.pushurl"}:
            if _clean_remote_url_credentials(value) != value:
                raise RuntimeError(
                    f"embedded credentials remain in {repository}/origin"
                )
    _reject_local_git_execution_authority(
        repository, require_https_submodules=True
    )


def scrub_pat_from_remotes(root: Path) -> None:
    """Scrub embedded HTTP credentials from every materialized origin.

    Visit and scrub a repository before asking Git to inspect its children. This
    ordering prevents a partial/promisor checkout from consuming an embedded
    origin credential while discovering its indexed submodules.
    """

    def scrub_tree(repository: Path, display_prefix: str) -> None:
        _scrub_repository_origin_credentials(repository)
        for state in _direct_submodule_states(repository, display_prefix):
            if state.marker == "U":
                raise RuntimeError(
                    f"unmerged indexed submodule state at {state.display_path}; "
                    "resolve the gitlink conflict before recreating bootstrap"
                )
            if state.marker != "-":
                scrub_tree(repository / state.path, state.display_path)

    scrub_tree(root, "")


CONFIG_TEMPLATE = """\
# Generated by scripts/recreate_bootstrap.py ({mode} stage0 mode).
# Edit freely; rerunning the recreator will not overwrite an existing
# config.toml / bootstrap.toml unless you pass --force-config.

profile = "compiler"
change-id = "ignore"

[build]
python = "{python}"
# Trust: first-party/ submodules are managed by this script / the developer
# ("most pulled forward" toolchain policy). Disable bootstrap's unconditional
# `git submodule update` so it can never reset deliberately-advanced pins back
# to the committed gitlink SHA. Standard upstream submodules are vendored as
# plain source trees (not in .gitmodules), so nothing else is affected;
# recreate_bootstrap.py materializes first-party/ itself on a fresh clone.
submodules = false
docs = false
compiler-docs = false
extended = true
tools = [
    "targo",
    "targo-trust",
    "trustdoc",
    "trustfmt",
    "trust-analyzer",
    "tippy",
    "targo-tippy",
    "tippy-driver",
    "trust-analyzer-proc-macro-srv",
    # Trust: THE PROOF BACKENDS ARE PART OF THE TOOLCHAIN (2026-07-31). `clean`
    # and `ty` were absent from this list while the stage tool provenance audit
    # required them, so every seed-mode build ended with
    #   ERROR: missing public stage tools: clean, ty
    # for binaries no build could ever install. The name->source mapping below
    # already carried both entries; only the request was missing.
    #
    # This is not cosmetic. `clean` is the CIC kernel, and per docs/TCB.md only a
    # Clean kernel re-check earns `Certified` — with it absent from the sysroot,
    # solver discovery falls through to `solver_detect.rs`'s `/opt/homebrew/bin`
    # and `/usr/local/bin` search, i.e. it looks for the proof root in a package
    # manager's directory. That is a wrong-verdict-source hazard, not a crash.
    # `ty` owns concurrency (DataRace, InsufficientOrdering) per v6/D2.
    #
    # COST, stated plainly because it cuts against slimming the build: these are
    # the two largest tools in the set — 134 MB and 192 MB as last built — and
    # they are now built on every bootstrap. That trade was made deliberately:
    # a toolchain that cannot reach its own trust root is not smaller, it is
    # incomplete. Remove `solver_detect.rs`'s brew fallback only AFTER this
    # lands and both binaries are present, never before.
    "clean",
    # Trust: `ty` RESTORED (2026-07-31). It was briefly gated out because building
    # it broke the bootstrap with
    #     error: cannot update the lock file first-party/ty/Cargo.lock
    #            because --locked was passed to prevent this
    # — a coherence failure between two sibling submodules, not a defect in ty's
    # own manifest. first-party/ty path-depends into first-party/clean, whose
    # clean-auto inherits ay 0.4.0 pinned at rev 286c85566; ty's lock recorded
    # that edge at the stale 04539379. Fixed at the source with `cargo update -p
    # ay` in the ty repo (only the ay 0.4.0 set moved; tla-ay's own ay 0.3.0 at
    # 035e84f2 is untouched), landed as fix/ty-lock-ay-286c8556 and the
    # first-party/ty gitlink moved to it. `cargo metadata --locked` now exits 0.
    "ty",
    # Trust: THE TRUST-NATIVE TOOLCHAIN REGISTRY (2026-07-31). trustup is a
    # workspace member with tests, and until now had ZERO references in
    # src/bootstrap and was absent from stage2/bin — so the only way to select
    # the Trust toolchain was a PATH prepend, and aterm's rust-toolchain.toml
    # (`channel = "trust"`) was inert because rustup is not installed. It is the
    # Trust-native answer to that, and it was sitting unwired.
    # Its bootstrap steps are gated on this list naming it, so removing this
    # entry disables the wiring rather than breaking the build.
    "trustup",
]
{stage0_block}
[llvm]
download-ci-llvm = false
ninja = true
optimize = true
# Cut LLVM build time roughly in half on M-series — drop targets we don't ship.
targets = "AArch64;X86;WebAssembly"

[rust]
download-rustc = false
channel = "trust"
# Production-shaped std paths: panic locations and diagnostics embed
# /rustc/<ver>/library/... exactly like upstream dist builds, so upstream ui
# test expectations (library/core/src/... after test normalization) match
# without local blessing.
remap-debuginfo = true
# Trust: build the verified trust-cg codegen backend alongside LLVM so
# `-Zcodegen-backend=trust_cg` works out of the box. Without this the shipped
# trustc fails with "failed to find a codegen-backends folder" — the backend's
# availability must never silently depend on a machine-local config.
codegen-backends = ["llvm", "trust-cg"]
# Submodules under first-party/ drift behind current nightly and surface
# legitimate warnings (deprecated hidden lifetimes, non-camel-case enum
# variants from a rust_mc → trust_mc rename, dead code). Trust's release
# build enforces zero warnings via a ratchet; for a fresh-checkout dev
# build we relax to warn-only so the toolchain comes up. Fix the warnings
# in the affected submodules, then flip this back on.
deny-warnings = false

[install]
prefix = "{prefix}"
sysconfdir = "etc"
"""


GENESIS_STAGE0_BLOCK = """\
# Point each stage0 tool at the genesis adapter so bootstrap never tries to
# download a `trust-*` tarball from the empty local dist server.
# Trust: config KEYS keep their upstream-compatible names. Bootstrap uses the
# Cargo-compatible identity because branded Targo accepts only authenticated
# verification or a human-visible --unverified argument.
rustc = "{stage0}/bin/trustc"
cargo = "{stage0}/bin/cargo"
rustdoc = "{stage0}/bin/trustdoc"
rustfmt = "{stage0}/bin/trustfmt"
cargo-clippy = "{stage0}/bin/targo-tippy"
"""

SEED_STAGE0_BLOCK = """\
# No stage0 override: x.py resolves the checksum-pinned Trust seed declared in
# src/stage0 from the repo-local bootstrap/trust-stage0 dist (trust-from-trust;
# stock rust nowhere in the loop). Both bootstrap layers select the seed's
# sibling bin/cargo compatibility identity, never branded Targo authority.
"""


def write_config(
    root: Path, host: str, force: bool, llvm_config: str | None = None, seed_mode: bool = False
) -> Path:
    # Trust uses upstream's bootstrap which accepts either name.
    target = root / "bootstrap.toml"
    legacy = root / "config.toml"
    existing = target if target.exists() else (legacy if legacy.exists() else None)
    if existing and not force:
        # Reliability ratchet: a stale genesis-mode config silently drags stock
        # rust back into a seed-mode build. Refuse the mismatch loudly instead.
        if seed_mode and "genesis-stage0" in existing.read_text(encoding="utf-8"):
            raise SystemExit(
                f"{existing} still pins the stock-rust genesis adapter as stage0, but the "
                "pinned Trust seed is materialized and valid. Rerun with --force-config to "
                "switch the config to the seed (recommended), or pass --genesis to keep the "
                "stock-rust path deliberately."
            )
        print(f"  reusing existing config at {existing}")
        return existing
    py = find_python_ge_311() or sys.executable
    stage0_block = (
        SEED_STAGE0_BLOCK
        if seed_mode
        else GENESIS_STAGE0_BLOCK.format(stage0=str(root / "build" / host / "genesis-stage0"))
    )
    content = CONFIG_TEMPLATE.format(
        mode="seed" if seed_mode else "genesis",
        python=py,
        prefix=str(root / "install"),
        stage0_block=stage0_block,
    )
    if llvm_config:
        # Link an external LLVM instead of building it in-tree (no cmake/ninja,
        # ~26 min saved). The major version must match what rustc_llvm expects.
        content += (
            f'\n[target.{host}]\n'
            f'llvm-config = "{llvm_config}"\n'
        )
    target.write_text(content, encoding="utf-8")
    print(f"  wrote {target}")
    return target


def install_ay_solver(root: Path, host: str, stage: int) -> bool:
    """Ensure the x.py-built `ay` (trust-from-trust) sits beside `trustc`.

    The compiler's solver dispatch probes for an `ay` executable in trustc's OWN
    bin directory (`sibling_solver` in trust_verify.rs). Without it EVERY source
    obligation degrades to `unknown`/`runtime_checked` and verification proves
    nothing — i.e. the toolchain is not "batteries on". `./x.py build` already
    builds `ay` as an in-tree tool (`--no-default-features --features
    cli,unsafe-bcp`; `ensure_default_verifier_tool_bins` in
    src/bootstrap/src/core/build_steps/tool.rs) and installs it in the sysroot,
    so the job here is only to restore that artifact if anything displaced it.
    Rebuilding with a PATH `cargo` — what this function once did — silently
    replaced the trust-from-trust binary with a stock-Rust build carrying
    different features. If the artifact is somehow absent, fall back to
    building with the just-built targo/trustc; stock rust is never used.
    Returns false when installation cannot be completed; the one-command
    caller treats that as an installation failure even if x.py itself built.
    """
    bindir = root / "build" / host / f"stage{stage}" / "bin"
    trustc = bindir / "trustc"
    if not trustc.exists():
        print(f"  (skip ay install: no {trustc})")
        return False
    installed = bindir / "ay"
    # bootstrap's tools_dir is stage{build_compiler.stage + 1}-tools-bin, and
    # the tools accompanying the stage-N sysroot are built by the stage-(N-1)
    # compiler — so the stage-N sysroot's ay artifact lives in
    # stage{N+1}-tools-bin/<target>/. (stage{N}-tools-bin holds the PREVIOUS
    # sysroot's ay: one compiler generation older, stock-rust-built in genesis
    # mode. Using it here corrupted the real artifact once — see below.)
    tool_artifact = root / "build" / host / f"stage{stage + 1}-tools-bin" / host / "ay"
    if tool_artifact.is_file():
        if installed.exists() and os.path.samefile(tool_artifact, installed):
            # bootstrap installs via hard link; the common post-build state is
            # already correct and copying a file onto itself would fail.
            print(f"  x.py-built ay already installed at {installed}  (trust-from-trust)")
            return True
        # Never write THROUGH the destination: bootstrap hard-links the sysroot
        # bin to its tools-bin cache and cargo's output, and an in-place copy
        # truncates every path sharing the inode. Unlink first.
        installed.unlink(missing_ok=True)
        shutil.copy2(tool_artifact, installed)
        print(f"  installed x.py-built ay -> {installed}  (trust-from-trust)")
        return True
    if installed.exists():
        print(f"  keeping x.py-installed ay at {installed}")
        return True
    targo = bindir / "targo"
    if not targo.exists():
        print(
            "  ERROR: no x.py-built ay artifact and no targo to rebuild one — "
            "verification will report `unknown` until `ay` is beside trustc "
            "(run scripts/install-ay-beside-trustc.sh)."
        )
        return False
    ay_dir = root / "first-party" / "ay"
    print("\n  building ay with the just-built toolchain (release, cli,unsafe-bcp) ...")
    env = os.environ.copy()
    env.pop("RUSTC_BOOTSTRAP", None)
    env["RUSTC"] = str(trustc)
    env["PATH"] = f"{bindir}:{env.get('PATH', '')}"
    add_homebrew_library_path(env)
    rc = subprocess.run(
        [
            str(targo), "--unverified", "build", "--locked", "--release", "--bin", "ay",
            "--no-default-features", "--features", "cli,unsafe-bcp",
        ],
        cwd=str(ay_dir),
        env=env,
    ).returncode
    ay_bin = ay_dir / "target" / "release" / "ay"
    if rc != 0 or not ay_bin.exists():
        print(
            "  ERROR: ay build failed — verification will report `unknown` until "
            "`ay` is beside trustc (run scripts/install-ay-beside-trustc.sh)."
        )
        return False
    installed.unlink(missing_ok=True)  # never write through bootstrap's hard links
    shutil.copy2(ay_bin, installed)
    print(
        f"  installed ay -> {installed}  "
        "(targo trust front doors activate verification explicitly)"
    )
    return True


# Public stage-N entrypoint -> x.py stage-(N+1) tools-bin producer.  Trust's
# branded front doors intentionally replace most inherited public spellings;
# rustc/cargo remain same-sysroot compatibility aliases only.  Keeping this
# map beside the post-build installer makes it impossible to silently add a
# public tool without naming the exact bootstrap artifact that produced it.
STAGE_TOOL_PRODUCERS = {
    "cargo": "cargo",
    "targo": "cargo",
    # Trust: NOT OPTIONAL (2026-07-31). A public tool named in `tools = [...]`
    # must also name the bootstrap artifact that produced it, or the post-build
    # installer cannot place it and the stage tool provenance audit reports it
    # missing — exactly the failure `clean` and `ty` hit in fef5414c1fa.
    "trustup": "trustup",
    "targo-trust": "targo-trust",
    "trustd": "trustd",
    "ay": "ay",
    "ty": "ty",
    "clean": "clean",
    "trustdoc": "rustdoc_tool_binary",
    "trustfmt": "rustfmt",
    "targo-fmt": "cargo-fmt",
    "tippy": "cargo-clippy",
    "targo-tippy": "cargo-clippy",
    "tippy-driver": "clippy-driver",
    "trust-analyzer": "rust-analyzer",
}

SEED_STAGE0_REQUIRED_BINS = (
    "trustc",
    "rustc",
    "trustdoc",
    "targo",
    "cargo",
    "targo-trust",
    "trustfmt",
    "targo-fmt",
    "tippy",
    "targo-tippy",
    "tippy-driver",
    "trust-analyzer",
)

SEED_STAGE0_REQUIRED_LIBEXEC_BINS = ("trust-analyzer-proc-macro-srv",)

SEED_STAGE0_FORBIDDEN_BINS = (
    "cargo-trust",
    "tcargo",
    "tcargo-trust",
    "tcargo-fmt",
    "rustdoc",
    "rustfmt",
    "cargo-fmt",
    "cargo-clippy",
    "clippy-driver",
    "targo-clippy",
    "trust-clippy",
    "trust-clippy-driver",
    "rust-analyzer",
    "miri",
    "trust-miri",
    "cargo-miri",
    "targo-miri",
    "rust-gdb",
    "rust-gdbgui",
    "rust-lldb",
    "rust-windbg.cmd",
)

SEED_STAGE0_FORBIDDEN_LIBEXEC_BINS = ("rust-analyzer-proc-macro-srv",)

GENESIS_WRAPPER_SOURCES = {
    "trustc": "rustc",
    "rustc": "rustc",
    "trustdoc": "rustdoc",
    "targo": "cargo",
    "cargo": "cargo",
    "trustfmt": "rustfmt",
    "targo-fmt": "cargo-fmt",
    "tippy": "cargo-clippy",
    "targo-tippy": "cargo-clippy",
    "tippy-driver": "clippy-driver",
    "trust-analyzer": "rust-analyzer",
}

GENESIS_STUB_BINS = ("targo-trust",)
GENESIS_STUB_LIBEXEC_BINS = ("trust-analyzer-proc-macro-srv",)


def _host_executable(name: str, host: str) -> str:
    return f"{name}.exe" if "windows" in host else name


def _stage0_bin_filename(name: str, host: str) -> str:
    return name if name.endswith(".cmd") else _host_executable(name, host)


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _capture_identity(path: Path, args: tuple[str, ...]) -> tuple[bool, str]:
    try:
        completed = subprocess.run(
            [str(path), *args],
            capture_output=True,
            text=True,
            check=False,
            timeout=30,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        return False, str(error)
    output = (completed.stdout or completed.stderr).strip()
    return completed.returncode == 0, output


def _repository_relative_path(root: Path, path: Path) -> str:
    """Return a portable repository-root-relative path or fail closed."""
    try:
        relative = path.resolve().relative_to(root.resolve())
    except (OSError, ValueError) as error:
        raise ValueError(f"path is outside the Trust repository: {path}: {error}") from error
    rendered = relative.as_posix()
    return rendered if rendered else "."


def _repository_lexical_relative_path(root: Path, path: Path) -> str:
    """Record an in-tree symlink entry without resolving its external target."""
    root_absolute = Path(os.path.abspath(root))
    path_absolute = Path(os.path.abspath(path))
    try:
        relative = path_absolute.relative_to(root_absolute)
    except ValueError as error:
        raise ValueError(f"lexical path is outside the Trust repository: {path}") from error
    rendered = relative.as_posix()
    return rendered if rendered else "."


def _provenance_git_environment() -> dict[str, str]:
    """Return a closed environment for source/provenance Git operations.

    Constructing this mapping from scratch is intentional.  Git and its
    transports honor a large execution surface (`GIT_EXEC_PATH`, askpass/SSH
    commands, dynamic-loader variables, proxy variables, repository redirects,
    and counted config in the environment).  A deny-list is therefore not a
    stable authority boundary.
    """
    if os.name == "nt":
        controlled_path = r"C:\Windows\System32;C:\Windows"
        empty_home = r"C:\Windows\Temp"
        false_program = None
    else:
        controlled_path = CONTROLLED_GIT_PATH
        empty_home = "/var/empty" if Path("/var/empty").is_dir() else "/"
        false_program = (
            "/usr/bin/false" if Path("/usr/bin/false").is_file() else "/bin/false"
        )

    env = {
        "PATH": controlled_path,
        "HOME": empty_home,
        "LANG": "C",
        "LC_ALL": "C",
        "TZ": "UTC",
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_CONFIG_SYSTEM": os.devnull,
        "GIT_CONFIG_GLOBAL": os.devnull,
        "GIT_ATTR_NOSYSTEM": "1",
        "GIT_NO_REPLACE_OBJECTS": "1",
        "GIT_OPTIONAL_LOCKS": "0",
        "GIT_TERMINAL_PROMPT": "0",
        "GIT_PAGER": "",
        "PAGER": "",
    }
    if false_program is not None:
        env.update(
            {
                "GIT_ASKPASS": false_program,
                "SSH_ASKPASS": false_program,
                "SSH_ASKPASS_REQUIRE": "never",
            }
        )
    return env


def _git_bytes(
    repository: Path,
    args: tuple[str, ...],
    errors: list[str],
    label: str,
) -> bytes | None:
    env = _provenance_git_environment()
    try:
        _reject_local_git_execution_authority(repository)
        completed = subprocess.run(
            _controlled_git_command(["-C", str(repository), *args]),
            capture_output=True,
            check=False,
            env=env,
            timeout=30,
        )
    except (OSError, RuntimeError, subprocess.TimeoutExpired) as error:
        errors.append(f"could not record {label}: {error}")
        return None
    if completed.returncode != 0:
        stderr = completed.stderr.decode("utf-8", errors="replace").strip()
        errors.append(
            f"could not record {label} (git exit {completed.returncode}): "
            f"{stderr or 'no diagnostic'}"
        )
        return None
    return completed.stdout


def _git_oid(
    repository: Path,
    args: tuple[str, ...],
    errors: list[str],
    label: str,
) -> str | None:
    raw = _git_bytes(repository, args, errors, label)
    if raw is None:
        return None
    value = raw.decode("ascii", errors="replace").strip()
    if len(value) not in (40, 64) or any(
        byte not in "0123456789abcdef" for byte in value
    ):
        errors.append(f"{label} did not produce one canonical Git object ID")
        return None
    return value


def _git_has_changes(
    repository: Path,
    args: tuple[str, ...],
    errors: list[str],
    label: str,
) -> bool:
    """Run a quiet Git plumbing comparison (0 = same, 1 = changed)."""
    env = _provenance_git_environment()
    try:
        _reject_local_git_execution_authority(repository)
        completed = subprocess.run(
            _controlled_git_command(["-C", str(repository), *args]),
            capture_output=True,
            check=False,
            env=env,
            timeout=30,
        )
    except (OSError, RuntimeError, subprocess.TimeoutExpired) as error:
        errors.append(f"could not record {label}: {error}")
        return False
    if completed.returncode in (0, 1):
        return completed.returncode == 1
    stderr = completed.stderr.decode("utf-8", errors="replace").strip()
    errors.append(
        f"could not record {label} (git exit {completed.returncode}): "
        f"{stderr or 'no diagnostic'}"
    )
    return False


def _git_optional_config(
    repository: Path,
    key: str,
    errors: list[str],
    label: str,
) -> str | None:
    try:
        _reject_local_git_execution_authority(repository)
        completed = subprocess.run(
            _controlled_git_command(
                [
                    "-C",
                    str(repository),
                    "config",
                    "--local",
                    "--no-includes",
                    "--get",
                    key,
                ]
            ),
            capture_output=True,
            check=False,
            env=_provenance_git_environment(),
            timeout=30,
        )
    except (OSError, RuntimeError, subprocess.TimeoutExpired) as error:
        errors.append(f"could not record {label}: {error}")
        return None
    if completed.returncode == 1:
        return None
    if completed.returncode != 0:
        stderr = completed.stderr.decode("utf-8", errors="replace").strip()
        errors.append(
            f"could not record {label} (git exit {completed.returncode}): "
            f"{stderr or 'no diagnostic'}"
        )
        return None
    try:
        return completed.stdout.decode("utf-8").strip().lower()
    except UnicodeError:
        errors.append(f"{label} is not valid UTF-8")
        return None


def _parse_index_entries(
    raw: bytes | None,
    errors: list[str],
    label: str,
) -> list[dict[str, object]]:
    """Parse canonical `git ls-files --stage -z` rows without path quoting."""
    if raw is None:
        return []
    if raw and not raw.endswith(b"\0"):
        errors.append(f"{label} did not use a complete NUL-delimited index")
        return []
    entries: list[dict[str, object]] = []
    for raw_entry in raw.split(b"\0"):
        if not raw_entry:
            continue
        metadata, separator, raw_path = raw_entry.partition(b"\t")
        fields = metadata.split()
        if not separator or len(fields) != 3 or not raw_path:
            errors.append(f"{label} contains a malformed index row")
            continue
        mode_raw, oid_raw, stage_raw = fields
        try:
            mode = mode_raw.decode("ascii")
            oid = oid_raw.decode("ascii")
            stage = int(stage_raw)
        except (UnicodeError, ValueError):
            errors.append(f"{label} contains non-canonical index metadata")
            continue
        relative = Path(os.fsdecode(raw_path))
        if (
            mode not in {"100644", "100755", "120000", "160000"}
            or len(oid) not in (40, 64)
            or any(character not in "0123456789abcdef" for character in oid)
            or stage not in (0, 1, 2, 3)
            or relative.is_absolute()
            or ".." in relative.parts
        ):
            errors.append(f"{label} contains a non-canonical index row")
            continue
        entries.append(
            {
                "mode": mode,
                "oid": oid,
                "stage": stage,
                "path": relative,
                "raw_path": raw_path,
            }
        )
    return entries


def _discover_repository_graph(
    root: Path,
    errors: list[str],
) -> dict[Path, dict[str, object]]:
    """Discover every recursive gitlink from canonical indexes, not local config."""
    graph: dict[Path, dict[str, object]] = {
        Path("."): {
            "parent": None,
            "child_from_parent": None,
            "parent_index_gitlink": None,
        }
    }
    queue = [Path(".")]
    while queue:
        relative_repository = queue.pop(0)
        repository = root if relative_repository == Path(".") else root / relative_repository
        repository_id = relative_repository.as_posix()
        index_snapshot = _git_bytes(
            repository,
            ("ls-files", "--stage", "-z"),
            errors,
            f"{repository_id} index snapshot",
        )
        entries = _parse_index_entries(
            index_snapshot, errors, f"{repository_id} index snapshot"
        )
        graph[relative_repository]["index_snapshot"] = index_snapshot
        graph[relative_repository]["index_entries"] = entries
        for entry in entries:
            if entry["mode"] != "160000" or entry["stage"] != 0:
                continue
            child_from_parent = entry["path"]
            assert isinstance(child_from_parent, Path)
            child = (
                child_from_parent
                if relative_repository == Path(".")
                else relative_repository / child_from_parent
            )
            if child in graph:
                errors.append(f"recursive gitlink discovery repeats {child.as_posix()}")
                continue
            child_repository = root / child
            top_level = _git_bytes(
                child_repository,
                ("rev-parse", "--show-toplevel"),
                errors,
                f"{child.as_posix()} initialized repository root",
            )
            initialized = False
            if top_level is not None:
                try:
                    initialized = (
                        Path(os.fsdecode(top_level).strip()).resolve()
                        == child_repository.resolve()
                    )
                except OSError:
                    initialized = False
            if not initialized:
                errors.append(f"recursive gitlink is not initialized: {child.as_posix()}")
                continue
            graph[child] = {
                "parent": relative_repository,
                "child_from_parent": child_from_parent,
                "parent_index_gitlink": entry["oid"],
            }
            queue.append(child)
    return graph


def _parse_index_tags(
    raw: bytes | None,
    errors: list[str],
    label: str,
) -> dict[Path, str]:
    """Parse the one-byte tags from `git ls-files -v/-f -z`."""
    if raw is None:
        return {}
    if raw and not raw.endswith(b"\0"):
        errors.append(f"{label} did not use a complete NUL-delimited path list")
        return {}
    tags: dict[Path, str] = {}
    for item in raw.split(b"\0"):
        if not item:
            continue
        if len(item) < 3 or item[1:2] != b" ":
            errors.append(f"{label} contains a malformed tagged path")
            continue
        try:
            tag = item[:1].decode("ascii")
        except UnicodeError:
            errors.append(f"{label} contains a non-ASCII tag")
            continue
        path = Path(os.fsdecode(item[2:]))
        if path.is_absolute() or ".." in path.parts or path in tags:
            errors.append(f"{label} contains a duplicate or unsafe path")
            continue
        tags[path] = tag
    return tags


def _git_blob_identities(
    path: Path,
    index_mode: str,
    object_format: str,
) -> tuple[str, str, str]:
    """Return (Git blob OID, SHA-256, working mode) for exact consumed bytes."""
    before = path.lstat()
    if stat.S_ISLNK(before.st_mode):
        content = os.fsencode(os.readlink(path))
        actual_mode = "120000"
        git_digest = hashlib.new(object_format)
        git_digest.update(f"blob {len(content)}\0".encode("ascii"))
        git_digest.update(content)
        return git_digest.hexdigest(), hashlib.sha256(content).hexdigest(), actual_mode
    if not stat.S_ISREG(before.st_mode):
        raise OSError("tracked path is not a regular file or symlink")
    actual_mode = "100755" if before.st_mode & 0o111 else "100644"
    git_digest = hashlib.new(object_format)
    git_digest.update(f"blob {before.st_size}\0".encode("ascii"))
    content_digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            git_digest.update(chunk)
            content_digest.update(chunk)
    after = path.lstat()
    if (
        before.st_dev,
        before.st_ino,
        before.st_size,
        before.st_mtime_ns,
        before.st_mode,
    ) != (
        after.st_dev,
        after.st_ino,
        after.st_size,
        after.st_mtime_ns,
        after.st_mode,
    ):
        raise OSError("tracked file changed while it was being hashed")
    return git_digest.hexdigest(), content_digest.hexdigest(), actual_mode


def _capture_working_tree_snapshot(
    repository: Path,
    entries: list[dict[str, object]],
    object_format: str,
    errors: list[str],
    repository_id: str,
) -> tuple[str, list[str], list[str]]:
    """Hash and compare every tracked working-tree byte independently of index flags."""
    snapshot = hashlib.sha256()
    mismatches: list[str] = []
    attribute_normalized_paths: list[str] = []
    seen_stage0_paths: set[Path] = set()
    for entry in entries:
        mode = str(entry["mode"])
        oid = str(entry["oid"])
        stage = int(entry["stage"])
        relative = entry["path"]
        raw_path = entry["raw_path"]
        assert isinstance(relative, Path) and isinstance(raw_path, bytes)
        snapshot.update(mode.encode("ascii") + b"\0")
        snapshot.update(oid.encode("ascii") + b"\0")
        snapshot.update(str(stage).encode("ascii") + b"\0")
        snapshot.update(len(raw_path).to_bytes(8, "big") + raw_path)
        if stage != 0:
            mismatches.append(relative.as_posix())
            snapshot.update(b"unmerged\0")
            continue
        if relative in seen_stage0_paths:
            errors.append(f"{repository_id} index repeats stage-0 path {relative.as_posix()}")
            mismatches.append(relative.as_posix())
            continue
        seen_stage0_paths.add(relative)
        if mode == "160000":
            snapshot.update(b"gitlink\0")
            continue
        candidate = repository / relative
        try:
            actual_oid, content_sha256, actual_mode = _git_blob_identities(
                candidate, mode, object_format
            )
        except OSError as error:
            errors.append(
                f"could not bind tracked path in {repository_id} "
                f"{relative.as_posix()}: {error}"
            )
            mismatches.append(relative.as_posix())
            snapshot.update(b"unreadable\0")
            continue
        snapshot.update(actual_mode.encode("ascii") + b"\0")
        snapshot.update(actual_oid.encode("ascii") + b"\0")
        snapshot.update(content_sha256.encode("ascii") + b"\0")
        if actual_mode != mode:
            mismatches.append(relative.as_posix())
            continue
        if actual_oid != oid:
            attributes_raw = _git_bytes(
                repository,
                (
                    "check-attr",
                    "-z",
                    "text",
                    "eol",
                    "filter",
                    "working-tree-encoding",
                    "--",
                    relative.as_posix(),
                ),
                errors,
                f"{repository_id} checkout attributes for {relative.as_posix()}",
            )
            attributes: dict[str, str] = {}
            if attributes_raw is not None:
                fields = attributes_raw.split(b"\0")
                if fields and fields[-1] == b"":
                    fields.pop()
                if len(fields) % 3 != 0:
                    errors.append(
                        f"{repository_id} checkout attributes are malformed for "
                        f"{relative.as_posix()}"
                    )
                else:
                    for offset in range(0, len(fields), 3):
                        path_field, attribute_field, value_field = fields[offset : offset + 3]
                        if os.fsdecode(path_field) != relative.as_posix():
                            errors.append(
                                f"{repository_id} checkout attributes returned a foreign path"
                            )
                            continue
                        attributes[attribute_field.decode("ascii", errors="replace")] = (
                            value_field.decode("utf-8", errors="replace")
                        )
            unsafe_attribute = any(
                attributes.get(name) not in {None, "unspecified", "unset"}
                for name in ("filter", "working-tree-encoding")
            )
            if unsafe_attribute:
                errors.append(
                    f"{repository_id} tracked path uses unsupported checkout filters: "
                    f"{relative.as_posix()}"
                )
            normalized_raw = (
                None
                if unsafe_attribute
                else _git_bytes(
                    repository,
                    (
                        "hash-object",
                        f"--path={relative.as_posix()}",
                        "--",
                        relative.as_posix(),
                    ),
                    errors,
                    f"{repository_id} attribute-normalized bytes for "
                    f"{relative.as_posix()}",
                )
            )
            normalized_oid = (
                normalized_raw.decode("ascii", errors="replace").strip()
                if normalized_raw is not None
                else ""
            )
            try:
                repeated_oid, repeated_sha256, repeated_mode = _git_blob_identities(
                    candidate, mode, object_format
                )
            except OSError as error:
                errors.append(
                    f"could not rebind attribute-normalized path in {repository_id} "
                    f"{relative.as_posix()}: {error}"
                )
                repeated_oid = repeated_sha256 = repeated_mode = ""
            stable_bytes = (
                repeated_oid == actual_oid
                and repeated_sha256 == content_sha256
                and repeated_mode == actual_mode
            )
            snapshot.update(
                json.dumps(
                    {
                        "attributes": dict(sorted(attributes.items())),
                        "normalized_oid": normalized_oid,
                        "stable_bytes": stable_bytes,
                    },
                    sort_keys=True,
                    separators=(",", ":"),
                ).encode("utf-8")
                + b"\0"
            )
            if normalized_oid == oid and not unsafe_attribute and stable_bytes:
                attribute_normalized_paths.append(relative.as_posix())
            else:
                mismatches.append(relative.as_posix())
    return (
        snapshot.hexdigest(),
        sorted(set(mismatches)),
        sorted(set(attribute_normalized_paths)),
    )


def _nul_paths(raw: bytes | None, errors: list[str], label: str) -> list[Path]:
    if raw is None:
        return []
    if raw and not raw.endswith(b"\0"):
        errors.append(f"{label} did not use a complete NUL-delimited path list")
        return []
    paths: list[Path] = []
    for item in raw.split(b"\0"):
        if not item:
            continue
        path = Path(os.fsdecode(item))
        if path.is_absolute() or ".." in path.parts:
            errors.append(f"{label} returned a non-repository-relative path")
            continue
        paths.append(path)
    return paths


def _untracked_file_records(
    repository: Path,
    paths: list[Path],
    errors: list[str],
    repository_id: str,
) -> list[dict[str, str]]:
    records: list[dict[str, str]] = []
    for relative in sorted(paths, key=lambda path: path.as_posix()):
        candidate = repository / relative
        try:
            if candidate.is_symlink():
                target = os.fsencode(os.readlink(candidate))
                digest = hashlib.sha256(target).hexdigest()
                kind = "symlink-target"
            elif candidate.is_file():
                digest = _sha256_file(candidate)
                kind = "file"
            else:
                errors.append(
                    f"untracked path in {repository_id} is not a regular file or symlink: "
                    f"{relative.as_posix()}"
                )
                continue
        except OSError as error:
            errors.append(
                f"could not hash untracked path in {repository_id} "
                f"{relative.as_posix()}: {error}"
            )
            continue
        records.append({"path": relative.as_posix(), "kind": kind, "sha256": digest})
    return records


def _index_gitlink(
    parent: Path,
    relative: Path,
    errors: list[str],
    label: str,
) -> str | None:
    raw = _git_bytes(
        parent,
        ("ls-files", "--stage", "-z", "--", relative.as_posix()),
        errors,
        label,
    )
    if raw is None:
        return None
    matches: list[str] = []
    for entry in raw.split(b"\0"):
        if not entry:
            continue
        metadata, separator, _path = entry.partition(b"\t")
        fields = metadata.split()
        if separator and len(fields) == 3 and fields[0] == b"160000" and fields[2] == b"0":
            matches.append(fields[1].decode("ascii", errors="replace"))
    if len(matches) != 1:
        errors.append(f"{label} did not resolve exactly one stage-0 gitlink")
        return None
    value = matches[0]
    if len(value) not in (40, 64) or any(
        byte not in "0123456789abcdef" for byte in value
    ):
        errors.append(f"{label} returned a non-canonical Git object ID")
        return None
    return value


def capture_source_lineage(root: Path) -> dict[str, object]:
    """Capture the exact recursive Git state used by a bootstrap build.

    Clean committed trees are eligible for immutable release lineage. A tree
    whose only changes are staged is recorded as a non-release proposal.
    Unstaged, untracked, conflicted, uninitialized, ambiguous, or mismatched
    recursive state is rejected instead of being summarized optimistically.
    """
    errors: list[str] = []
    root = root.resolve()
    repository_graph = _discover_repository_graph(root, errors)
    repository_paths = list(repository_graph)

    repositories: list[dict[str, object]] = []
    for relative_repository in sorted(
        repository_paths, key=lambda path: (path.as_posix() != ".", path.as_posix())
    ):
        repository = root if relative_repository == Path(".") else root / relative_repository
        repository_id = relative_repository.as_posix()
        head = _git_oid(
            repository,
            ("rev-parse", "--verify", "HEAD"),
            errors,
            f"{repository_id} HEAD",
        )
        head_tree = _git_oid(
            repository,
            ("rev-parse", "--verify", "HEAD^{tree}"),
            errors,
            f"{repository_id} HEAD tree",
        )
        graph_row = repository_graph[relative_repository]
        index_snapshot = graph_row.get("index_snapshot")
        index_entries = graph_row.get("index_entries")
        if not isinstance(index_entries, list):
            errors.append(f"{repository_id} has no canonical index snapshot")
            index_entries = []
        object_format_raw = _git_bytes(
            repository,
            ("rev-parse", "--show-object-format"),
            errors,
            f"{repository_id} object format",
        )
        object_format = (
            object_format_raw.decode("ascii", errors="replace").strip()
            if object_format_raw is not None
            else ""
        )
        if object_format not in {"sha1", "sha256"}:
            errors.append(f"{repository_id} uses an unsupported Git object format")
            object_format = "sha256"
        checkout_policy = {
            key: _git_optional_config(
                repository,
                key,
                errors,
                f"{repository_id} {key}",
            )
            for key in (
                "core.autocrlf",
                "core.symlinks",
                "core.filemode",
                "core.ignorestat",
                "core.sparsecheckout",
                "core.attributesfile",
            )
        }
        if checkout_policy["core.autocrlf"] not in (None, "false"):
            errors.append(f"{repository_id} enables unsupported core.autocrlf")
        if checkout_policy["core.symlinks"] == "false":
            errors.append(f"{repository_id} disables tracked symlink materialization")
        if checkout_policy["core.filemode"] == "false":
            errors.append(f"{repository_id} disables tracked executable-mode authority")
        if checkout_policy["core.ignorestat"] not in (None, "false"):
            errors.append(f"{repository_id} enables unsupported core.ignoreStat")
        if checkout_policy["core.sparsecheckout"] not in (None, "false"):
            errors.append(f"{repository_id} enables unsupported sparse checkout")
        if checkout_policy["core.attributesfile"] is not None:
            errors.append(f"{repository_id} configures an external attributes file")
        info_attributes_raw = _git_bytes(
            repository,
            ("rev-parse", "--git-path", "info/attributes"),
            errors,
            f"{repository_id} repository-local attributes path",
        )
        info_attributes_value = (
            os.fsdecode(info_attributes_raw).strip()
            if info_attributes_raw is not None
            else ""
        )
        info_attributes_path = Path(info_attributes_value)
        if not info_attributes_path.is_absolute():
            info_attributes_path = repository / info_attributes_path
        info_attributes_present = os.path.lexists(info_attributes_path)
        if info_attributes_present:
            errors.append(f"{repository_id} has untracked repository-local attributes")
        index_tags = _parse_index_tags(
            _git_bytes(
                repository,
                ("ls-files", "-v", "-z"),
                errors,
                f"{repository_id} index flags",
            ),
            errors,
            f"{repository_id} index flags",
        )
        fsmonitor_tags = _parse_index_tags(
            _git_bytes(
                repository,
                ("ls-files", "-f", "-z"),
                errors,
                f"{repository_id} fsmonitor flags",
            ),
            errors,
            f"{repository_id} fsmonitor flags",
        )
        assume_unchanged_paths = sorted(
            path.as_posix() for path, tag in index_tags.items() if tag.islower()
        )
        skip_worktree_paths = sorted(
            path.as_posix() for path, tag in index_tags.items() if tag.upper() == "S"
        )
        fsmonitor_valid_paths = sorted(
            path.as_posix() for path, tag in fsmonitor_tags.items() if tag.islower()
        )
        if assume_unchanged_paths:
            errors.append(f"{repository_id} has assume-unchanged index entries")
        if skip_worktree_paths:
            errors.append(f"{repository_id} has skip-worktree index entries")
        if fsmonitor_valid_paths:
            errors.append(f"{repository_id} has fsmonitor-valid index entries")
        has_staged_changes = _git_has_changes(
            repository,
            (
                "diff-index",
                "--cached",
                "--quiet",
                "--ignore-submodules=dirty",
                "HEAD",
                "--",
            ),
            errors,
            f"{repository_id} staged state",
        )
        (
            working_tree_snapshot_sha256,
            working_tree_mismatch_paths,
            attribute_normalized_paths,
        ) = (
            _capture_working_tree_snapshot(
                repository,
                index_entries,
                object_format,
                errors,
                repository_id,
            )
        )
        has_unstaged_changes = bool(working_tree_mismatch_paths)
        untracked_paths = _nul_paths(
            _git_bytes(
                repository,
                (
                    "ls-files",
                    "--others",
                    "--exclude-per-directory=.gitignore",
                    "-z",
                ),
                errors,
                f"{repository_id} untracked paths",
            ),
            errors,
            f"{repository_id} untracked paths",
        )
        conflict_paths = sorted(
            {
                entry["path"]
                for entry in index_entries
                if int(entry["stage"]) != 0 and isinstance(entry["path"], Path)
            },
            key=lambda path: path.as_posix(),
        )
        untracked_files = _untracked_file_records(
            repository, untracked_paths, errors, repository_id
        )

        parent_repository: str | None = None
        parent_head_gitlink: str | None = None
        parent_index_gitlink: str | None = None
        head_matches_parent_head: bool | None = None
        head_matches_parent_index: bool | None = None
        if relative_repository != Path("."):
            parent_relative = graph_row.get("parent")
            child_from_parent = graph_row.get("child_from_parent")
            parent_index_value = graph_row.get("parent_index_gitlink")
            if not isinstance(parent_relative, Path) or not isinstance(
                child_from_parent, Path
            ) or not isinstance(parent_index_value, str):
                errors.append(f"could not resolve parent gitlink for {repository_id}")
            else:
                parent = root if parent_relative == Path(".") else root / parent_relative
                parent_repository = parent_relative.as_posix()
                parent_head_gitlink = _git_oid(
                    parent,
                    ("rev-parse", "--verify", f"HEAD:{child_from_parent.as_posix()}"),
                    errors,
                    f"{repository_id} parent HEAD gitlink",
                )
                parent_index_gitlink = parent_index_value
                if head is not None and parent_head_gitlink is not None:
                    head_matches_parent_head = head == parent_head_gitlink
                if head is not None:
                    head_matches_parent_index = head == parent_index_gitlink
                    if not head_matches_parent_index:
                        errors.append(
                            f"{repository_id} HEAD does not match its parent index gitlink"
                        )

        repositories.append(
            {
                "path": repository_id,
                "head": head,
                "head_tree": head_tree,
                "object_format": object_format,
                "checkout_policy": checkout_policy,
                "info_attributes_present": info_attributes_present,
                "index_snapshot_sha256": hashlib.sha256(index_snapshot or b"").hexdigest(),
                "working_tree_snapshot_sha256": working_tree_snapshot_sha256,
                "has_staged_changes": has_staged_changes,
                "has_unstaged_changes": has_unstaged_changes,
                "working_tree_mismatch_paths": working_tree_mismatch_paths,
                "attribute_normalized_paths": attribute_normalized_paths,
                "assume_unchanged_paths": assume_unchanged_paths,
                "skip_worktree_paths": skip_worktree_paths,
                "fsmonitor_valid_paths": fsmonitor_valid_paths,
                "untracked_files": untracked_files,
                "conflict_paths": [path.as_posix() for path in conflict_paths],
                "parent_repository": parent_repository,
                "parent_head_gitlink": parent_head_gitlink,
                "parent_index_gitlink": parent_index_gitlink,
                "head_matches_parent_head": head_matches_parent_head,
                "head_matches_parent_index": head_matches_parent_index,
            }
        )

    for repository in repositories:
        repository_id = str(repository["path"])
        if repository["has_unstaged_changes"]:
            errors.append(f"{repository_id} has unstaged tracked changes")
        if repository["untracked_files"]:
            errors.append(f"{repository_id} has untracked files")
        if repository["conflict_paths"]:
            errors.append(f"{repository_id} has unresolved conflicts")

    closure = {
        "schema": "trust.source-lineage-closure.v1",
        "repositories": repositories,
    }
    closure_sha256 = hashlib.sha256(
        json.dumps(closure, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()
    has_staged_changes = any(bool(repository["has_staged_changes"]) for repository in repositories)
    parent_head_mismatch = any(
        repository["head_matches_parent_head"] is False for repository in repositories
    )
    if errors:
        status = "rejected"
    elif has_staged_changes or parent_head_mismatch:
        status = "staged_proposal"
    else:
        status = "immutable_release"
    return {
        "schema": "trust.source-lineage.v1",
        "status": status,
        "source_tree_clean": status == "immutable_release",
        "closure_sha256": closure_sha256,
        "repositories": repositories,
        "errors": sorted(set(errors)),
    }


def _bind_source_lineage(
    before: dict[str, object] | None,
    after: dict[str, object],
) -> dict[str, object]:
    lineage = dict(after)
    errors = [str(error) for error in after.get("errors", [])]
    before_sha = before.get("closure_sha256") if before is not None else None
    after_sha = after.get("closure_sha256")
    stable = before is not None and before_sha == after_sha
    if before is None:
        errors.append("missing pre-build source-lineage snapshot")
    else:
        errors.extend(str(error) for error in before.get("errors", []))
        if before.get("status") == "rejected":
            errors.append("pre-build source lineage was rejected")
        if not stable:
            errors.append("recursive source lineage changed during the bootstrap build")
    if errors:
        status = "rejected"
    else:
        status = str(after.get("status"))
    lineage.update(
        {
            "status": status,
            "source_tree_clean": status == "immutable_release",
            "stable_across_build": stable,
            "pre_build_closure_sha256": before_sha,
            "post_build_closure_sha256": after_sha,
            "errors": sorted(set(errors)),
        }
    )
    return lineage


def _capture_seed_archive_members(
    root: Path,
    host: str,
    pins: dict[str, str],
    payloads: list[dict[str, object]],
    errors: list[str],
) -> tuple[list[dict[str, object]], dict[str, dict[str, object]]]:
    """Hash every required stage0 entrypoint in its exact pinned archive."""
    compiler_version = pins.get("compiler_version", "")
    rustfmt_version = pins.get("rustfmt_version", "")
    date = pins.get("compiler_date", "")
    archive_specs = (
        (
            "trustc",
            compiler_version,
            (
                ("bin", "trustc"),
                ("bin", "rustc"),
                ("bin", "trustdoc"),
                ("libexec", "trust-analyzer-proc-macro-srv"),
            ),
        ),
        ("targo", compiler_version, (("bin", "targo"), ("bin", "cargo"))),
        ("targo-trust", compiler_version, (("bin", "targo-trust"),)),
        (
            "trustfmt",
            rustfmt_version,
            (("bin", "trustfmt"), ("bin", "targo-fmt")),
        ),
        (
            "tippy",
            compiler_version,
            (("bin", "tippy"), ("bin", "targo-tippy"), ("bin", "tippy-driver")),
        ),
        (
            "trust-analyzer",
            compiler_version,
            (("bin", "trust-analyzer"),),
        ),
    )
    declared_payload_paths = [str(payload.get("path", "")) for payload in payloads]
    records: list[dict[str, object]] = []
    member_bindings: dict[str, dict[str, object]] = {}
    for component, version, wanted_members in archive_specs:
        if not date or not version:
            errors.append(f"seed pins cannot name the exact {component} archive")
            continue
        filename = f"{component}-{version}-{host}.tar.xz"
        archive_relative = Path("bootstrap") / "trust-stage0" / "dist" / date / filename
        if declared_payload_paths.count(archive_relative.as_posix()) != 1:
            errors.append(
                f"src/stage0 does not declare the exact required archive: "
                f"{archive_relative.as_posix()}"
            )
            continue
        archive = root / archive_relative
        try:
            with tarfile.open(archive, mode="r:xz") as bundle:
                archive_prefix = filename.removesuffix(".tar.xz")
                all_members = bundle.getmembers()
                for destination_dir, tool in wanted_members:
                    executable = _host_executable(tool, host)
                    member_path = (
                        f"{archive_prefix}/{component}/{destination_dir}/{executable}"
                    )
                    matches = [member for member in all_members if member.name == member_path]
                    if len(matches) != 1:
                        errors.append(
                            f"seed {component} archive does not contain exactly one "
                            f"{component}/{destination_dir}/{executable} member"
                        )
                        continue
                    member = matches[0]
                    if not (member.isfile() or member.islnk() or member.issym()):
                        errors.append(
                            f"seed archive member is not a file or link: {member.name}"
                        )
                        continue
                    extracted = bundle.extractfile(member)
                    if extracted is None:
                        errors.append(f"seed archive member could not be read: {member.name}")
                        continue
                    digest = hashlib.sha256()
                    for chunk in iter(lambda: extracted.read(1024 * 1024), b""):
                        digest.update(chunk)
                    sha256 = digest.hexdigest()
                    destination = f"{destination_dir}/{executable}"
                    member_type = (
                        "regular"
                        if member.isfile()
                        else "hardlink"
                        if member.islnk()
                        else "symlink"
                    )
                    archive_record = {
                        "tool": tool,
                        "destination": destination,
                        "archive_path": archive_relative.as_posix(),
                        "member_path": member.name,
                        "member_type": member_type,
                        "member_mode": member.mode,
                        "member_linkname": member.linkname or None,
                        "member_sha256": sha256,
                    }
                    records.append(archive_record)
                    if destination in member_bindings:
                        errors.append(f"duplicate seed destination across archives: {destination}")
                    member_bindings[destination] = archive_record
        except (OSError, KeyError, tarfile.TarError) as error:
            errors.append(f"could not inspect seed {component} archive: {error}")
            continue
    return sorted(records, key=lambda record: str(record["destination"])), member_bindings


def _capture_stage0_tree(root: Path, stage0: Path) -> dict[str, object]:
    """Hash the complete hydrated stage0 tree without following directory links."""
    entries: list[dict[str, object]] = []
    errors: list[str] = []
    stage0_resolved = stage0.resolve()
    walk_errors: list[OSError] = []
    for current_root, directory_names, file_names in os.walk(
        stage0,
        followlinks=False,
        onerror=walk_errors.append,
    ):
        current = Path(current_root)
        for name in sorted((*directory_names, *file_names)):
            path = current / name
            relative = path.relative_to(stage0).as_posix()
            try:
                metadata = path.lstat()
            except OSError as error:
                errors.append(f"could not stat hydrated stage0 entry {relative}: {error}")
                continue
            row: dict[str, object] = {
                "path": relative,
                "mode": stat.S_IMODE(metadata.st_mode),
            }
            if stat.S_ISDIR(metadata.st_mode):
                row["type"] = "directory"
            elif stat.S_ISREG(metadata.st_mode):
                try:
                    sha256 = _sha256_file(path)
                except OSError as error:
                    errors.append(f"could not hash hydrated stage0 entry {relative}: {error}")
                    sha256 = None
                row.update(
                    {
                        "type": "regular",
                        "size": metadata.st_size,
                        "sha256": sha256,
                    }
                )
            elif stat.S_ISLNK(metadata.st_mode):
                link_target: str | None = None
                try:
                    link_target = os.readlink(path)
                    resolved_target = path.resolve(strict=True)
                    resolved_target.relative_to(stage0_resolved)
                except (OSError, ValueError) as error:
                    errors.append(
                        f"hydrated seed stage0 link escapes or is unreadable: {relative}: {error}"
                    )
                    resolved_target_text = None
                else:
                    resolved_target_text = _repository_relative_path(root, resolved_target)
                row.update(
                    {
                        "type": "symlink",
                        "link_target": link_target,
                        "resolved_target": resolved_target_text,
                    }
                )
            else:
                row["type"] = "unsupported"
                errors.append(f"hydrated seed stage0 has unsupported entry type: {relative}")
            entries.append(row)
    errors.extend(f"could not walk hydrated stage0 tree: {error}" for error in walk_errors)
    closure = {
        "schema": "trust.seed-stage0-tree.v1",
        "root": _repository_relative_path(root, stage0),
        "entries": sorted(entries, key=lambda row: str(row["path"])),
    }
    closure_sha256 = hashlib.sha256(
        json.dumps(closure, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()
    return {
        **closure,
        "status": "validated" if not errors else "rejected",
        "closure_sha256": closure_sha256,
        "errors": sorted(set(errors)),
    }


def _capture_external_tree(
    tree: Path,
    allowed_root: Path,
    *,
    bind_external_symlink_targets: bool = False,
) -> dict[str, object]:
    """Canonical byte manifest for an external producer tree on this machine."""
    errors: list[str] = []
    entries: list[dict[str, object]] = []
    try:
        tree_real = tree.resolve(strict=True)
        allowed_real = allowed_root.resolve(strict=True)
        tree_real.relative_to(allowed_real)
    except (OSError, ValueError) as error:
        return {
            "schema": "trust.external-producer-tree.v1",
            "selected_local_path": str(tree),
            "real_path": None,
            "status": "rejected",
            "closure_sha256": None,
            "entries": [],
            "errors": [f"external producer tree is outside its admitted root: {error}"],
        }
    if tree.is_symlink() or not tree.is_dir():
        errors.append("external producer tree root is not a real directory")

    walk_errors: list[OSError] = []
    for current_root, directory_names, file_names in os.walk(
        tree_real,
        followlinks=False,
        onerror=walk_errors.append,
    ):
        current = Path(current_root)
        for name in sorted((*directory_names, *file_names)):
            path = current / name
            relative = path.relative_to(tree_real).as_posix()
            try:
                metadata = path.lstat()
            except OSError as error:
                errors.append(f"could not stat external producer entry {relative}: {error}")
                continue
            row: dict[str, object] = {
                "path": relative,
                "mode": stat.S_IMODE(metadata.st_mode),
            }
            if stat.S_ISDIR(metadata.st_mode):
                row["type"] = "directory"
            elif stat.S_ISREG(metadata.st_mode):
                try:
                    sha256 = _sha256_file(path)
                except OSError as error:
                    errors.append(f"could not hash external producer entry {relative}: {error}")
                    sha256 = None
                row.update(
                    {
                        "type": "regular",
                        "size": metadata.st_size,
                        "sha256": sha256,
                    }
                )
            elif stat.S_ISLNK(metadata.st_mode):
                link_target: str | None = None
                try:
                    link_target = os.readlink(path)
                    resolved_target = path.resolve(strict=True)
                    resolved_target.relative_to(allowed_real)
                except (OSError, ValueError) as error:
                    errors.append(
                        f"external producer link escapes or is unreadable: {relative}: {error}"
                    )
                    resolved_target_text = None
                else:
                    resolved_target_text = str(resolved_target)
                    try:
                        resolved_target.relative_to(tree_real)
                    except ValueError:
                        if bind_external_symlink_targets and resolved_target.is_file():
                            try:
                                target_metadata = resolved_target.lstat()
                                row.update(
                                    {
                                        "resolved_target_type": "regular",
                                        "resolved_target_mode": stat.S_IMODE(
                                            target_metadata.st_mode
                                        ),
                                        "resolved_target_size": target_metadata.st_size,
                                        "resolved_target_sha256": _sha256_file(
                                            resolved_target
                                        ),
                                    }
                                )
                            except OSError as error:
                                errors.append(
                                    f"could not bind external producer link target "
                                    f"{relative}: {error}"
                                )
                        else:
                            errors.append(
                                "external producer link target is outside the walked tree: "
                                f"{relative}"
                            )
                row.update(
                    {
                        "type": "symlink",
                        "link_target": link_target,
                        "resolved_target": resolved_target_text,
                    }
                )
            else:
                row["type"] = "unsupported"
                errors.append(f"external producer tree has unsupported entry: {relative}")
            entries.append(row)
    errors.extend(f"could not walk external producer tree: {error}" for error in walk_errors)
    closure = {
        "schema": "trust.external-producer-tree.v1",
        "selected_local_path": str(tree),
        "real_path": str(tree_real),
        "entries": sorted(entries, key=lambda row: str(row["path"])),
    }
    closure_sha256 = hashlib.sha256(
        json.dumps(closure, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()
    return {
        **closure,
        "status": "validated" if not errors else "rejected",
        "closure_sha256": closure_sha256,
        "errors": sorted(set(errors)),
    }


def _capture_seed_compiler_identity(
    root: Path,
    host: str,
    pins: dict[str, str],
    archive_member_bindings: dict[str, dict[str, object]],
    reported_product_identities: dict[str, str],
) -> dict[str, object]:
    """Bind the complete hydrated stage0 tree and canonical entrypoint surface.

    ``compiler_version`` and ``rustfmt_version`` in ``src/stage0`` are archive
    labels used by rustup's distribution protocol.  They are not necessarily
    the versions printed by the products inside those archives (for example,
    a ``1.99.0-trust`` archive can contain a compiler reporting
    ``1.99.0-dev``).  The exact product identities are admitted separately in
    the seed ledger so neither namespace is silently conflated here.
    """
    stage0 = root / "build" / host / "stage0"
    bin_dir = stage0 / "bin"
    stage0_root_present = os.path.lexists(stage0)
    if not stage0_root_present:
        return {
            "schema": "trust.seed-compiler-identity.v1",
            "status": "not-materialized",
            "stage0_root": _repository_relative_path(root, stage0),
            "stage0_root_present": False,
            "tools": [],
            "forbidden_paths_present": [],
            "stage0_tree": None,
            "errors": [],
        }

    errors: list[str] = []
    if stage0.is_symlink() or not stage0.is_dir():
        errors.append("hydrated seed stage0 root is not a real directory")
        stage0_tree: dict[str, object] | None = None
    else:
        stage0_tree = _capture_stage0_tree(root, stage0)
        errors.extend(str(error) for error in stage0_tree.get("errors", []))

    required_paths = [
        (name, "bin", bin_dir / _host_executable(name, host))
        for name in SEED_STAGE0_REQUIRED_BINS
    ] + [
        (
            name,
            "libexec",
            stage0 / "libexec" / _host_executable(name, host),
        )
        for name in SEED_STAGE0_REQUIRED_LIBEXEC_BINS
    ]
    tools: list[dict[str, object]] = []
    paths: dict[str, Path] = {}
    for name, destination_dir, path in required_paths:
        paths[name] = path
        destination = f"{destination_dir}/{path.name}"
        archive_binding = archive_member_bindings.get(destination)
        row: dict[str, object] = {
            "name": name,
            "path": _repository_relative_path(root, path),
            "destination": destination,
            "archive_member_sha256": (
                archive_binding.get("member_sha256")
                if archive_binding is not None
                else None
            ),
            "archive_member_type": (
                archive_binding.get("member_type")
                if archive_binding is not None
                else None
            ),
            "archive_member_mode": (
                archive_binding.get("member_mode")
                if archive_binding is not None
                else None
            ),
        }
        if path.is_file():
            metadata = path.lstat()
            row["destination_type"] = (
                "symlink" if stat.S_ISLNK(metadata.st_mode) else "regular"
            )
            row["destination_mode"] = stat.S_IMODE(metadata.st_mode)
            row["executable"] = os.access(path, os.X_OK)
            row["sha256"] = _sha256_file(path)
            if row["archive_member_sha256"] != row["sha256"]:
                errors.append(
                    f"hydrated seed {destination} does not match its pinned archive member"
                )
            archive_type = row["archive_member_type"]
            if archive_type == "symlink":
                if row["destination_type"] != "symlink":
                    errors.append(
                        f"hydrated seed {destination} is not the archived symlink type"
                    )
                else:
                    destination_linkname = os.readlink(path)
                    row["destination_linkname"] = destination_linkname
                    if destination_linkname != archive_binding.get("member_linkname"):
                        errors.append(
                            f"hydrated seed {destination} link target differs from its archive"
                        )
            elif archive_type in {"regular", "hardlink"}:
                if row["destination_type"] != "regular":
                    errors.append(
                        f"hydrated seed {destination} is not a regular extracted file"
                    )
                elif (
                    "windows" not in host
                    and row["destination_mode"] != row["archive_member_mode"]
                ):
                    errors.append(
                        f"hydrated seed {destination} mode differs from its archive member"
                    )
            if not row["executable"]:
                errors.append(f"hydrated seed {destination} is not executable")
            if name in {"trustc", "targo", "trustfmt"}:
                args = ("-Vv",) if name == "trustc" else ("--version",)
                ok, identity = _capture_identity(path, args)
                row["identity"] = identity
                row["identity_probe_ok"] = ok
                if not ok:
                    errors.append(f"hydrated seed {name} identity probe failed")
        else:
            errors.append(f"hydrated seed stage0 is missing required {destination}")
        if archive_binding is None:
            errors.append(f"pinned seed archive member is missing for {destination}")
        tools.append(row)

    rows = {str(row["name"]): row for row in tools}
    for owned, compatibility in (
        ("trustc", "rustc"),
        ("targo", "cargo"),
    ):
        if paths[owned].is_file() and paths[compatibility].is_file():
            if rows[owned].get("sha256") != rows[compatibility].get("sha256"):
                errors.append(f"hydrated seed {compatibility} alias differs from {owned}")
            rows[compatibility]["same_inode_as_owned"] = os.path.samefile(
                paths[owned], paths[compatibility]
            )

    forbidden_paths = [
        bin_dir / _stage0_bin_filename(name, host)
        for name in SEED_STAGE0_FORBIDDEN_BINS
    ] + [
        stage0 / "libexec" / _host_executable(name, host)
        for name in SEED_STAGE0_FORBIDDEN_LIBEXEC_BINS
    ]
    forbidden_present = sorted(
        _repository_relative_path(root, path)
        for path in forbidden_paths
        if os.path.lexists(path)
    )
    if forbidden_present:
        errors.append(
            "hydrated seed stage0 contains forbidden entrypoints: "
            + ", ".join(forbidden_present)
        )

    expected_identity_keys = {"trustc", "targo", "trustfmt"}
    if set(reported_product_identities) != expected_identity_keys:
        errors.append(
            "seed admission ledger does not declare the exact reported product identity set"
        )

    compiler_identity = str(rows.get("trustc", {}).get("identity", ""))
    compiler_commit = pins.get("compiler_git_commit_hash", "")
    if not compiler_commit or f"commit-hash: {compiler_commit}" not in compiler_identity:
        errors.append("hydrated seed trustc is not bound to compiler_git_commit_hash")
    compiler_first_line = compiler_identity.splitlines()[0] if compiler_identity else ""
    if compiler_first_line != reported_product_identities.get("trustc"):
        errors.append("hydrated seed trustc does not match its admitted product identity")
    targo_identity = str(rows.get("targo", {}).get("identity", ""))
    if targo_identity != reported_product_identities.get("targo"):
        errors.append("hydrated seed targo does not match its admitted product identity")
    trustfmt_identity = str(rows.get("trustfmt", {}).get("identity", ""))
    if trustfmt_identity != reported_product_identities.get("trustfmt"):
        errors.append("hydrated seed trustfmt does not match its admitted product identity")
    trustc = paths["trustc"]
    sysroot_matches = False
    if trustc.is_file():
        sysroot_ok, reported_sysroot = _capture_identity(trustc, ("--print", "sysroot"))
        try:
            sysroot_matches = sysroot_ok and Path(reported_sysroot).resolve() == stage0.resolve()
        except OSError:
            sysroot_matches = False
        if not sysroot_matches:
            errors.append("hydrated seed trustc reports a foreign sysroot")

    return {
        "schema": "trust.seed-compiler-identity.v1",
        "status": "validated" if not errors else "rejected",
        "stage0_root": _repository_relative_path(root, stage0),
        "stage0_root_present": stage0_root_present,
        "tools": tools,
        "reported_product_identities": dict(sorted(reported_product_identities.items())),
        "forbidden_paths_present": forbidden_present,
        "stage0_tree": stage0_tree,
        "reported_sysroot_matches": sysroot_matches,
        "errors": sorted(set(errors)),
    }


def capture_validated_seed_lineage(root: Path, host: str) -> dict[str, object]:
    """Bind seed pins, payload bytes, admission ledger, and hydrated compiler."""
    try:
        import tomllib
    except ModuleNotFoundError:
        tomllib = None

    root = root.resolve()
    errors: list[str] = []
    stage0_path = root / "src" / "stage0"
    ledger_path = root / "bootstrap" / "trust-stage0" / "seed-ledger.toml"
    pins, payload_pins = parse_stage0_pins(root)
    required_pins = {
        "compiler_channel_manifest_hash",
        "compiler_git_commit_hash",
        "compiler_date",
        "compiler_version",
        "rustfmt_channel_manifest_hash",
        "rustfmt_git_commit_hash",
        "rustfmt_date",
        "rustfmt_version",
    }
    missing_pins = sorted(required_pins - set(pins))
    if missing_pins:
        errors.append(f"src/stage0 is missing seed pins: {', '.join(missing_pins)}")
    if not payload_pins:
        errors.append("src/stage0 declares no seed payloads")
    if pins.get("compiler_date") != pins.get("rustfmt_date"):
        errors.append("compiler and rustfmt seed dates disagree")
    if pins.get("compiler_channel_manifest_hash") != pins.get(
        "rustfmt_channel_manifest_hash"
    ):
        errors.append("compiler and rustfmt channel-manifest pins disagree")
    try:
        stage0_sha256 = _sha256_file(stage0_path)
    except OSError as error:
        errors.append(f"could not hash src/stage0: {error}")
        stage0_sha256 = None

    payloads: list[dict[str, object]] = []
    seed_root = root / "bootstrap" / "trust-stage0"
    for declared_path, pinned_sha256 in sorted(payload_pins.items()):
        relative = Path(declared_path)
        safe = (
            not relative.is_absolute()
            and ".." not in relative.parts
            and relative.parts[:1] == ("dist",)
        )
        if not safe:
            errors.append(f"unsafe seed payload path in src/stage0: {declared_path}")
            continue
        if len(pinned_sha256) != 64 or any(
            character not in "0123456789abcdef" for character in pinned_sha256
        ):
            errors.append(f"non-canonical seed payload SHA-256: {declared_path}")
        payload = seed_root / relative
        actual_sha256: str | None = None
        if not payload.is_file() or payload.is_symlink():
            errors.append(f"seed payload is missing or not a regular file: {declared_path}")
        else:
            try:
                actual_sha256 = _sha256_file(payload)
            except OSError as error:
                errors.append(f"could not hash seed payload {declared_path}: {error}")
        matches = actual_sha256 == pinned_sha256
        if not matches:
            errors.append(f"seed payload does not match src/stage0 pin: {declared_path}")
        payloads.append(
            {
                "path": _repository_relative_path(root, payload),
                "pinned_sha256": pinned_sha256,
                "actual_sha256": actual_sha256,
                "matches_pin": matches,
            }
        )

    manifest_date = pins.get("compiler_date", "")
    manifest_path = seed_root / "dist" / manifest_date / "channel-rust-trust.toml"
    manifest_sha256: str | None = None
    if not manifest_path.is_file() or manifest_path.is_symlink():
        errors.append("pinned Trust channel manifest is missing or not a regular file")
    else:
        try:
            manifest_sha256 = _sha256_file(manifest_path)
        except OSError as error:
            errors.append(f"could not hash pinned Trust channel manifest: {error}")
    for pin_name in (
        "compiler_channel_manifest_hash",
        "rustfmt_channel_manifest_hash",
    ):
        if manifest_sha256 != pins.get(pin_name):
            errors.append(f"Trust channel manifest does not match {pin_name}")

    freshness_script = root / "scripts" / "check_seed_freshness.py"
    freshness_record: dict[str, object] = {
        "script_path": _repository_relative_path(root, freshness_script),
    }
    try:
        freshness_record["script_sha256"] = _sha256_file(freshness_script)
        freshness = subprocess.run(
            [sys.executable, str(freshness_script), "--require-payloads"],
            cwd=str(root),
            capture_output=True,
            check=False,
            timeout=300,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        errors.append(f"canonical seed freshness check could not run: {error}")
        freshness_record.update({"status": "rejected", "exit_code": None})
    else:
        freshness_record.update(
            {
                "status": "validated" if freshness.returncode == 0 else "rejected",
                "exit_code": freshness.returncode,
            }
        )
        if freshness.returncode != 0:
            errors.append("canonical seed freshness/required-component check failed")

    ledger_sha256: str | None = None
    ledger_document: dict[str, object] = {}
    if not ledger_path.is_file() or ledger_path.is_symlink():
        errors.append("seed admission ledger is missing or not a regular file")
    else:
        try:
            ledger_bytes = ledger_path.read_bytes()
            ledger_sha256 = hashlib.sha256(ledger_bytes).hexdigest()
        except OSError as error:
            errors.append(f"could not read seed admission ledger: {error}")
            ledger_bytes = b""
        if tomllib is None:
            errors.append("Python 3.11+ tomllib is required to validate seed admission")
        else:
            try:
                parsed_ledger = tomllib.loads(ledger_bytes.decode("utf-8"))
            except (UnicodeError, tomllib.TOMLDecodeError) as error:
                errors.append(f"seed admission ledger is not valid UTF-8 TOML: {error}")
            else:
                if isinstance(parsed_ledger, dict):
                    ledger_document = parsed_ledger
                else:
                    errors.append("seed admission ledger is not a TOML table")

    scope = ledger_document.get("scope")
    promotion_decision = ledger_document.get("promotion_decision")
    signatures = ledger_document.get("signatures")
    checksums = ledger_document.get("checksums")
    release = ledger_document.get("release")
    artifact_root = ledger_document.get("artifact_root")
    if not isinstance(signatures, list) or not all(isinstance(item, str) for item in signatures):
        errors.append("seed admission ledger signatures are malformed")
        signatures = []
    if not isinstance(checksums, list) or not all(isinstance(item, str) for item in checksums):
        errors.append("seed admission ledger checksums are malformed")
        checksums = []
    if not isinstance(release, dict):
        errors.append("seed admission ledger release table is missing")
        release = {}
    if not isinstance(artifact_root, dict):
        errors.append("seed admission ledger artifact_root table is missing")
        artifact_root = {}
    declared_checksums = set(checksums)
    for payload in payloads:
        if f"sha256:{payload['pinned_sha256']}" not in declared_checksums:
            errors.append(f"seed admission ledger omits payload {payload['path']}")
    ledger_pin_fields = {
        "date": "compiler_date",
        "compiler_version": "compiler_version",
        "compiler_git_commit_hash": "compiler_git_commit_hash",
        "channel_manifest_hash": "compiler_channel_manifest_hash",
    }
    for ledger_field, pin_field in ledger_pin_fields.items():
        if release.get(ledger_field) != pins.get(pin_field):
            errors.append(f"seed admission ledger {ledger_field} disagrees with src/stage0")
    if release.get("host_triple") != host:
        errors.append("seed admission ledger host_triple does not match the build host")

    reported_product_identities = release.get("reported_product_identities")
    if not isinstance(reported_product_identities, dict) or not all(
        isinstance(key, str) and isinstance(value, str) and value
        for key, value in (
            reported_product_identities.items()
            if isinstance(reported_product_identities, dict)
            else ()
        )
    ):
        errors.append("seed admission ledger reported product identities are malformed")
        reported_product_identities = {}
    else:
        reported_product_identities = dict(reported_product_identities)

    placeholder_signature = any(
        marker in signature.lower()
        for signature in signatures
        for marker in ("placeholder", "not-public", "internal-admission-only")
    )
    visibility = release.get("visibility")
    if (
        scope == "public"
        and promotion_decision == "promote"
        and visibility == "public"
        and signatures
        and not placeholder_signature
    ):
        admission_status = "rejected"
        errors.append(
            "public seed promotion lacks an implemented pinned-key cryptographic verifier"
        )
    elif scope == "internal" and promotion_decision == "admit-internal":
        admission_status = "internal-admitted"
    else:
        admission_status = "rejected"
        errors.append("seed admission ledger does not declare an accepted admission class")

    admission = {
        "scope": scope,
        "promotion_decision": promotion_decision,
        "signatures": signatures,
        "checksums": checksums,
        "release": dict(sorted(release.items())),
        "artifact_root": dict(sorted(artifact_root.items())),
        "status": admission_status,
    }
    authority = {
        "schema": "trust.seed-authority.v1",
        "src_stage0": {
            "path": _repository_relative_path(root, stage0_path),
            "sha256": stage0_sha256,
        },
        "pins": dict(sorted(pins.items())),
        "payloads": payloads,
        "channel_manifest": {
            "path": _repository_relative_path(root, manifest_path),
            "sha256": manifest_sha256,
            "compiler_pin": pins.get("compiler_channel_manifest_hash"),
            "rustfmt_pin": pins.get("rustfmt_channel_manifest_hash"),
        },
        "freshness_check": freshness_record,
        "seed_ledger": {
            "path": _repository_relative_path(root, ledger_path),
            "sha256": ledger_sha256,
            "admission": admission,
        },
    }
    archive_members, archive_member_bindings = _capture_seed_archive_members(
        root, host, pins, payloads, errors
    )
    authority["archive_members"] = archive_members
    authority_sha256 = hashlib.sha256(
        json.dumps(authority, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()
    compiler = _capture_seed_compiler_identity(
        root,
        host,
        pins,
        archive_member_bindings,
        reported_product_identities,
    )
    errors.extend(str(error) for error in compiler.get("errors", []))
    if errors:
        status = "rejected"
    elif compiler.get("status") == "validated":
        status = "validated"
    else:
        status = "validated-payloads"
    return {
        "schema": "trust.validated-seed-lineage.v1",
        "status": status,
        "admission_status": admission_status,
        "authority_sha256": authority_sha256,
        "authority": authority,
        "compiler": compiler,
        "errors": sorted(set(errors)),
    }


def _parse_verbose_identity(identity: str) -> dict[str, str]:
    fields: dict[str, str] = {}
    for line in identity.splitlines():
        key, separator, value = line.partition(": ")
        if separator and key not in fields:
            fields[key] = value
    return fields


def _load_genesis_adapter_generator(root: Path) -> object:
    script = root / "scripts" / "create_local_genesis_stage0.py"
    source = script.read_text(encoding="utf-8")
    namespace: dict[str, object] = {
        "__file__": str(script),
        "__name__": "trust_genesis_adapter_generator",
    }
    exec(compile(source, str(script), "exec"), namespace)
    return SimpleNamespace(**namespace)


def _capture_genesis_adapter_authority(
    root: Path,
    host: str,
    build_table: dict[str, object],
) -> dict[str, object]:
    """Bind the complete local-genesis adapter and its external producer root."""
    errors: list[str] = []
    adapter = root / "build" / host / "genesis-stage0"
    bin_dir = adapter / "bin"
    libexec_dir = adapter / "libexec"
    manifest_path = adapter / "trust-local-genesis-stage0.json"
    expected_config_paths = {
        "rustc": adapter / "bin" / _host_executable("trustc", host),
        "cargo": adapter / "bin" / _host_executable("cargo", host),
        "rustdoc": adapter / "bin" / _host_executable("trustdoc", host),
        "rustfmt": adapter / "bin" / _host_executable("trustfmt", host),
        "cargo-clippy": adapter / "bin" / _host_executable("targo-tippy", host),
    }
    config_bindings: dict[str, object] = {}
    for key, expected_path in expected_config_paths.items():
        value = build_table.get(key)
        config_bindings[key] = value
        if value != str(expected_path):
            errors.append(f"genesis bootstrap config {key} does not name the exact adapter")
    if set(key for key in build_table if key in expected_config_paths) != set(
        expected_config_paths
    ):
        errors.append("genesis bootstrap config does not declare the exact stage0 key set")
    if "windows" in host:
        errors.append("Windows genesis adapter authority requires the native Windows schema")

    expected_root_names = {
        "bin",
        "lib",
        "libexec",
        ".trustc-stamp",
        ".rustc-stamp",
        "trust-local-genesis-stage0.json",
    }
    expected_bin_names = {
        _host_executable(name, host) for name in SEED_STAGE0_REQUIRED_BINS
    }
    expected_libexec_names = {
        _host_executable(name, host) for name in SEED_STAGE0_REQUIRED_LIBEXEC_BINS
    }
    surface_rows: list[dict[str, object]] = []
    if adapter.is_symlink() or not adapter.is_dir():
        errors.append("genesis adapter root is not a real directory")
        root_names: set[str] = set()
    else:
        root_names = {path.name for path in adapter.iterdir()}
    if root_names != expected_root_names:
        errors.append("genesis adapter root inventory is not closed")
    for directory, expected_names in (
        (bin_dir, expected_bin_names),
        (libexec_dir, expected_libexec_names),
    ):
        if directory.is_symlink() or not directory.is_dir():
            errors.append(f"genesis adapter directory is missing or symlinked: {directory.name}")
            actual_names: set[str] = set()
        else:
            actual_names = {path.name for path in directory.iterdir()}
        if actual_names != expected_names:
            errors.append(f"genesis adapter {directory.name} inventory is not closed")
        for name in sorted(expected_names):
            path = directory / name
            row: dict[str, object] = {
                "path": _repository_lexical_relative_path(root, path),
            }
            if not os.path.lexists(path):
                errors.append(f"genesis adapter entry is missing: {path}")
                row["type"] = "missing"
            else:
                metadata = path.lstat()
                row.update(
                    {
                        "type": "regular" if stat.S_ISREG(metadata.st_mode) else "invalid",
                        "mode": stat.S_IMODE(metadata.st_mode),
                        "nlink": metadata.st_nlink,
                        "executable": os.access(path, os.X_OK),
                    }
                )
                if not stat.S_ISREG(metadata.st_mode) or path.is_symlink():
                    errors.append(f"genesis adapter entry is not an independent regular file: {path}")
                else:
                    try:
                        row["sha256"] = _sha256_file(path)
                    except OSError as error:
                        errors.append(f"could not hash genesis adapter entry {path}: {error}")
                if metadata.st_nlink != 1:
                    errors.append(f"genesis adapter entry is hard-linked: {path}")
                if stat.S_IMODE(metadata.st_mode) != 0o755 or not os.access(path, os.X_OK):
                    errors.append(f"genesis adapter entry is not executable mode 0755: {path}")
            surface_rows.append(row)

    for name in (".trustc-stamp", ".rustc-stamp", "trust-local-genesis-stage0.json"):
        path = adapter / name
        row = {"path": _repository_lexical_relative_path(root, path)}
        if not path.is_file() or path.is_symlink():
            errors.append(f"genesis adapter metadata is not a regular file: {path}")
            row["type"] = "missing-or-invalid"
        else:
            metadata = path.lstat()
            row.update(
                {
                    "type": "regular",
                    "mode": stat.S_IMODE(metadata.st_mode),
                    "nlink": metadata.st_nlink,
                    "size": metadata.st_size,
                    "sha256": _sha256_file(path),
                }
            )
            if metadata.st_nlink != 1:
                errors.append(f"genesis adapter metadata is hard-linked: {path}")
        surface_rows.append(row)

    lib_link = adapter / "lib"
    lib_link_target: str | None = None
    lib_real: Path | None = None
    lib_row: dict[str, object] = {
        "path": _repository_lexical_relative_path(root, lib_link)
    }
    if not lib_link.is_symlink():
        errors.append("genesis adapter lib is not the designated sysroot symlink")
        lib_row["type"] = "missing-or-invalid"
    else:
        try:
            lib_link_target = os.readlink(lib_link)
            lib_real = lib_link.resolve(strict=True)
        except OSError as error:
            errors.append(f"genesis adapter lib link is unreadable: {error}")
        lib_row.update(
            {
                "type": "symlink",
                "link_target": lib_link_target,
                "resolved_local_path": str(lib_real) if lib_real is not None else None,
            }
        )
    surface_rows.append(lib_row)
    surface = {
        "schema": "trust.genesis-adapter-surface.v1",
        "entries": sorted(surface_rows, key=lambda row: str(row["path"])),
    }
    surface["closure_sha256"] = hashlib.sha256(
        json.dumps(surface, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()

    pins, _payloads = parse_stage0_pins(root)
    expected_stamp = pins.get("compiler_date")
    stamp_values: dict[str, str | None] = {}
    for name in (".trustc-stamp", ".rustc-stamp"):
        path = adapter / name
        try:
            value = path.read_text(encoding="utf-8")
        except (OSError, UnicodeError) as error:
            errors.append(f"could not read genesis adapter stamp {name}: {error}")
            value = None
        stamp_values[name] = value
        if value != expected_stamp:
            errors.append(f"genesis adapter {name} does not equal compiler_date")

    manifest: dict[str, object] = {}
    manifest_sha256: str | None = None
    if manifest_path.is_file() and not manifest_path.is_symlink():
        try:
            manifest_bytes = manifest_path.read_bytes()
            manifest_sha256 = hashlib.sha256(manifest_bytes).hexdigest()
            parsed_manifest = json.loads(manifest_bytes.decode("utf-8"))
        except (OSError, UnicodeError, json.JSONDecodeError) as error:
            errors.append(f"could not parse genesis adapter manifest: {error}")
        else:
            if isinstance(parsed_manifest, dict):
                manifest = parsed_manifest
            else:
                errors.append("genesis adapter manifest is not a JSON object")
    manifest_identity = {
        "schema": manifest.get("schema"),
        "admission": manifest.get("admission"),
        "public_upload": manifest.get("public_upload"),
        "counts_as_trust_stage0_evidence": manifest.get(
            "counts_as_trust_stage0_evidence"
        ),
        "repo_root": manifest.get("repo_root"),
        "stage0_root": manifest.get("stage0_root"),
        "host": manifest.get("host"),
        "stamp": manifest.get("stamp"),
        "compiler_version_target": manifest.get("compiler_version_target"),
    }
    expected_manifest_identity = {
        "schema": "trust.local-genesis-stage0-adapter.v1",
        "admission": "local-genesis-only",
        "public_upload": False,
        "counts_as_trust_stage0_evidence": False,
        "repo_root": str(root),
        "stage0_root": str(adapter),
        "host": host,
        "stamp": expected_stamp,
        "compiler_version_target": pins.get("compiler_version"),
    }
    if manifest_identity != expected_manifest_identity:
        errors.append("genesis adapter manifest identity fields are not canonical")
    expected_generated_bins = {
        name: str(bin_dir / _host_executable(name, host))
        for name in SEED_STAGE0_REQUIRED_BINS
    }
    expected_generated_libexec = {
        name: str(libexec_dir / _host_executable(name, host))
        for name in SEED_STAGE0_REQUIRED_LIBEXEC_BINS
    }
    if manifest.get("generated_bins") != expected_generated_bins:
        errors.append("genesis adapter manifest generated_bins is not exact")
    if manifest.get("generated_libexec_bins") != expected_generated_libexec:
        errors.append("genesis adapter manifest generated_libexec_bins is not exact")

    source_values = manifest.get("wrapper_sources")
    if not isinstance(source_values, dict):
        errors.append("genesis adapter manifest wrapper_sources is missing")
        source_values = {}
    expected_source_keys = (
        set(GENESIS_WRAPPER_SOURCES)
        | set(GENESIS_STUB_BINS)
        | set(GENESIS_STUB_LIBEXEC_BINS)
    )
    if set(source_values) != expected_source_keys:
        errors.append("genesis adapter wrapper_sources key set is not exact")
    for name in (*GENESIS_STUB_BINS, *GENESIS_STUB_LIBEXEC_BINS):
        if source_values.get(name) is not None:
            errors.append(f"genesis adapter always-stub {name} unexpectedly names a producer")

    root_manifest_path = root / "bootstrap" / "trust-genesis-roots.json"
    root_manifest: dict[str, object] = {}
    root_manifest_sha256: str | None = None
    if not root_manifest_path.is_file() or root_manifest_path.is_symlink():
        errors.append("genesis root-pin manifest is missing, non-regular, or symlinked")
    else:
        try:
            root_manifest_bytes = root_manifest_path.read_bytes()
            root_manifest_sha256 = hashlib.sha256(root_manifest_bytes).hexdigest()
            parsed_root_manifest = json.loads(root_manifest_bytes.decode("utf-8"))
        except (OSError, UnicodeError, json.JSONDecodeError) as error:
            errors.append(f"could not parse genesis root-pin manifest: {error}")
        else:
            if isinstance(parsed_root_manifest, dict):
                root_manifest = parsed_root_manifest
            else:
                errors.append("genesis root-pin manifest is not a JSON object")
    if (
        root_manifest.get("schema") != "trust.genesis-roots.v1"
        or root_manifest.get("admission") != "external-bootstrap-root-only"
        or root_manifest.get("counts_as_trust_stage0_evidence") is not False
    ):
        errors.append("genesis root-pin manifest admission is not canonical")
    channel_manifest = root_manifest.get("channel_manifest")
    roots = root_manifest.get("roots")
    selected_pin = roots.get(host) if isinstance(roots, dict) else None
    if not isinstance(channel_manifest, dict) or not isinstance(selected_pin, dict):
        errors.append("genesis root-pin manifest lacks channel or selected host authority")
        channel_manifest = {}
        selected_pin = {}
    if selected_pin.get("host") != host:
        errors.append("genesis selected host pin does not match the build host")
    if selected_pin.get("rustup_toolchain") != f"nightly-{channel_manifest.get('date')}":
        errors.append("genesis root pin does not match its channel date")

    rustc_value = source_values.get("trustc")
    rustc_path = Path(rustc_value) if isinstance(rustc_value, str) else None
    rustc_identity = ""
    rustc_fields: dict[str, str] = {}
    rustc_sha256: str | None = None
    sysroot_selected: Path | None = None
    sysroot_real: Path | None = None
    if rustc_path is None or not rustc_path.is_absolute() or not rustc_path.is_file():
        errors.append("genesis adapter does not name a usable direct backing rustc")
    else:
        try:
            rustc_path = rustc_path.resolve(strict=True)
            rustc_sha256 = _sha256_file(rustc_path)
        except OSError as error:
            errors.append(f"could not bind backing rustc: {error}")
        identity_ok, rustc_identity = _capture_identity(rustc_path, ("-Vv",))
        if not identity_ok:
            errors.append("backing genesis rustc rejected -Vv")
        rustc_fields = _parse_verbose_identity(rustc_identity)
        sysroot_ok, sysroot_value = _capture_identity(
            rustc_path, ("--print", "sysroot")
        )
        if not sysroot_ok:
            errors.append("backing genesis rustc rejected --print sysroot")
        else:
            sysroot_selected = Path(sysroot_value)
            try:
                sysroot_real = sysroot_selected.resolve(strict=True)
            except OSError as error:
                errors.append(f"could not resolve backing rustc sysroot: {error}")
    pin_identity = {
        "binary": "rustc",
        "release": selected_pin.get("release"),
        "commit-hash": selected_pin.get("commit_hash"),
        "commit-date": selected_pin.get("commit_date"),
        "host": selected_pin.get("host"),
    }
    if any(rustc_fields.get(field) != value for field, value in pin_identity.items()):
        errors.append("backing rustc identity does not match the selected genesis root pin")

    producers: list[dict[str, object]] = []
    producer_by_program: dict[str, dict[str, object]] = {}
    if sysroot_real is not None:
        for wrapper_name, program in GENESIS_WRAPPER_SOURCES.items():
            declared = source_values.get(wrapper_name)
            expected_candidate = sysroot_real / "bin" / _host_executable(program, host)
            expected_real: Path | None = None
            if expected_candidate.is_file():
                try:
                    expected_real = expected_candidate.resolve(strict=True)
                except OSError as error:
                    errors.append(f"could not resolve backing genesis {program}: {error}")
            if declared is None:
                if wrapper_name in {"trustc", "rustc", "trustdoc", "targo", "cargo"}:
                    errors.append(f"core genesis wrapper {wrapper_name} has no producer")
                if expected_real is not None:
                    errors.append(
                        f"genesis wrapper {wrapper_name} is stubbed despite an installed producer"
                    )
                continue
            if not isinstance(declared, str) or expected_real is None or declared != str(
                expected_real
            ):
                errors.append(
                    f"genesis wrapper {wrapper_name} does not name canonical sysroot {program}"
                )
                continue
            producer = producer_by_program.get(program)
            if producer is None:
                metadata = expected_real.lstat()
                producer = {
                    "name": program,
                    "path_scope": "local-diagnostic",
                    "selected_local_path": declared,
                    "resolved_real_path": str(expected_real),
                    "mode": stat.S_IMODE(metadata.st_mode),
                    "nlink": metadata.st_nlink,
                    "executable": os.access(expected_real, os.X_OK),
                    "referenced_by": [],
                }
                if not stat.S_ISREG(metadata.st_mode) or not os.access(expected_real, os.X_OK):
                    errors.append(f"backing genesis producer is not regular/executable: {program}")
                try:
                    before_sha256 = _sha256_file(expected_real)
                except OSError as error:
                    errors.append(f"could not hash backing genesis producer {program}: {error}")
                    before_sha256 = None
                args = ("-Vv",) if program in {"rustc", "rustdoc", "cargo"} else ("--version",)
                identity_ok, identity = _capture_identity(expected_real, args)
                try:
                    after_sha256 = _sha256_file(expected_real)
                except OSError as error:
                    errors.append(f"could not rehash backing genesis producer {program}: {error}")
                    after_sha256 = None
                producer.update(
                    {
                        "sha256": after_sha256,
                        "stable_during_probe": before_sha256 == after_sha256,
                        "identity_probe_ok": identity_ok,
                        "identity": identity,
                        "identity_fields": _parse_verbose_identity(identity),
                    }
                )
                if before_sha256 != after_sha256:
                    errors.append(f"backing genesis producer changed during capture: {program}")
                if not identity_ok:
                    errors.append(f"backing genesis producer identity probe failed: {program}")
                producer_by_program[program] = producer
                producers.append(producer)
            referenced_by = producer["referenced_by"]
            if isinstance(referenced_by, list):
                referenced_by.append(wrapper_name)
    producers.sort(key=lambda row: str(row["name"]))
    for producer in producers:
        referenced_by = producer.get("referenced_by")
        if isinstance(referenced_by, list):
            referenced_by.sort()
    producer_rows = {str(row["name"]): row for row in producers}
    rustdoc_fields = producer_rows.get("rustdoc", {}).get("identity_fields", {})
    if isinstance(rustdoc_fields, dict):
        expected_rustdoc = {**pin_identity, "binary": "rustdoc"}
        if any(rustdoc_fields.get(field) != value for field, value in expected_rustdoc.items()):
            errors.append("backing rustdoc identity does not match the genesis compiler root")
    cargo_fields = producer_rows.get("cargo", {}).get("identity_fields", {})
    if isinstance(cargo_fields, dict):
        for field in ("release", "host"):
            if cargo_fields.get(field) != rustc_fields.get(field):
                errors.append(f"backing cargo {field} differs from backing rustc")

    if sysroot_real is not None:
        expected_lib_real = (sysroot_real / "lib").resolve()
        if lib_real != expected_lib_real:
            errors.append("genesis adapter lib link does not resolve to backing sysroot/lib")
        lib_tree = _capture_external_tree(expected_lib_real, sysroot_real)
        errors.extend(str(error) for error in lib_tree.get("errors", []))
    else:
        expected_lib_real = None
        lib_tree = {
            "schema": "trust.external-producer-tree.v1",
            "status": "rejected",
            "entries": [],
            "closure_sha256": None,
            "errors": ["backing sysroot is unavailable"],
        }
        errors.extend(str(error) for error in lib_tree["errors"])

    if rustc_path is not None and rustc_sha256 is not None:
        reconstructed_genesis_root = {
            "manifest": "bootstrap/trust-genesis-roots.json",
            "channel_manifest": channel_manifest,
            "pin": selected_pin,
            "observed": rustc_fields,
            "rustc_path": str(rustc_path),
            "rustc_sha256": rustc_sha256,
        }
        if manifest.get("genesis_root") != reconstructed_genesis_root:
            errors.append("genesis adapter manifest root evidence differs from current authority")
    source_tools = manifest.get("source_tools")
    if not isinstance(source_tools, dict):
        errors.append("genesis adapter manifest source_tools is missing")
        source_tools = {}
    rustc_version_ok, rustc_version = (
        _capture_identity(rustc_path, ("--version",))
        if rustc_path is not None and rustc_path.is_file()
        else (False, "")
    )
    cargo_path_value = source_values.get("targo")
    cargo_path = Path(cargo_path_value) if isinstance(cargo_path_value, str) else None
    cargo_version_ok, cargo_version = (
        _capture_identity(cargo_path, ("--version",))
        if cargo_path is not None and cargo_path.is_file()
        else (False, "")
    )
    expected_source_tools = {
        "rustc": str(rustc_path) if rustc_path is not None else None,
        "rustc_version": rustc_version.splitlines()[0] if rustc_version_ok else None,
        "rustc_sysroot": str(sysroot_real) if sysroot_real is not None else None,
        "cargo": str(cargo_path) if cargo_path is not None else None,
        "cargo_version": cargo_version.splitlines()[0] if cargo_version_ok else None,
    }
    if source_tools != expected_source_tools:
        errors.append("genesis adapter manifest source_tools differs from current producers")

    try:
        generator = _load_genesis_adapter_generator(root)
    except (ImportError, OSError) as error:
        errors.append(f"could not load genesis adapter generator for byte validation: {error}")
        generator = None
    if generator is not None:
        if (
            tuple(generator.REQUIRED_BINS) != SEED_STAGE0_REQUIRED_BINS
            or tuple(generator.REQUIRED_LIBEXEC_BINS) != SEED_STAGE0_REQUIRED_LIBEXEC_BINS
            or set(generator.FORBIDDEN_BINS) != set(SEED_STAGE0_FORBIDDEN_BINS)
            or set(generator.FORBIDDEN_LIBEXEC_BINS)
            != set(SEED_STAGE0_FORBIDDEN_LIBEXEC_BINS)
        ):
            errors.append("genesis generator and provenance surface contracts disagree")
        for trust_name, (source_program, source_name) in generator.WRAPPER_SOURCES.items():
            real = source_values.get(trust_name)
            if real is None:
                expected_text = generator.stub_script(
                    name=trust_name,
                    message=f"{source_program} was not found in PATH",
                )
            elif isinstance(real, str):
                expected_text = generator.wrapper_script(
                    real=real,
                    source_name=source_name,
                    trust_name=trust_name,
                    argument_prefix=generator.WRAPPER_ARG_PREFIXES.get(trust_name),
                    argument_marker=generator.WRAPPER_ARG_MARKERS.get(trust_name),
                    version_name=generator.TIPPY_VERSION_NAMES.get(trust_name),
                    version_argument_prefix=generator.TIPPY_VERSION_ARG_PREFIXES.get(
                        trust_name
                    ),
                    argument_rename=generator.WRAPPER_ARG_RENAMES.get(trust_name),
                )
            else:
                errors.append(f"genesis wrapper source is malformed: {trust_name}")
                continue
            wrapper = bin_dir / _host_executable(trust_name, host)
            try:
                actual_bytes = wrapper.read_bytes()
            except OSError as error:
                errors.append(f"could not read genesis wrapper {trust_name}: {error}")
            else:
                if actual_bytes != expected_text.encode("utf-8"):
                    errors.append(f"genesis wrapper bytes do not match generator: {trust_name}")
        for name, message in generator.STUB_BINS.items():
            expected_text = generator.stub_script(name=name, message=message)
            path = bin_dir / _host_executable(name, host)
            if path.is_file() and path.read_bytes() != expected_text.encode("utf-8"):
                errors.append(f"genesis stub bytes do not match generator: {name}")
        for name, message in generator.STUB_LIBEXEC_BINS.items():
            expected_text = generator.stub_script(name=name, message=message)
            path = libexec_dir / _host_executable(name, host)
            if path.is_file() and path.read_bytes() != expected_text.encode("utf-8"):
                errors.append(f"genesis libexec stub bytes do not match generator: {name}")

    authority = {
        "schema": "trust.genesis-adapter-authority.v1",
        "admission": "local-genesis-only",
        "counts_as_trust_stage0_evidence": False,
        "host": host,
        "adapter_root": _repository_lexical_relative_path(root, adapter),
        "config_bindings": dict(sorted(config_bindings.items())),
        "root_pin": {
            "manifest_path": _repository_relative_path(root, root_manifest_path),
            "manifest_sha256": root_manifest_sha256,
            "channel_manifest": channel_manifest,
            "selected_host_pin": selected_pin,
        },
        "adapter_manifest": {
            "path": _repository_lexical_relative_path(root, manifest_path),
            "sha256": manifest_sha256,
            "identity": manifest_identity,
        },
        "stamps": stamp_values,
        "surface": surface,
        "backing_sysroot": {
            "path_scope": "local-diagnostic",
            "selected_local_path": str(sysroot_selected) if sysroot_selected else None,
            "resolved_real_path": str(sysroot_real) if sysroot_real else None,
            "lib_link_target": lib_link_target,
            "lib_resolved_local_path": (
                str(expected_lib_real) if expected_lib_real is not None else None
            ),
            "lib_tree": lib_tree,
        },
        "producers": producers,
    }
    authority_sha256 = hashlib.sha256(
        json.dumps(authority, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()
    return {
        "schema": "trust.genesis-adapter-authority.v1",
        "status": "ready" if not errors else "rejected",
        "authority_sha256": authority_sha256,
        "authority": authority,
        "errors": sorted(set(errors)),
    }


def _nixos_host() -> bool:
    try:
        os_release = Path("/etc/os-release").read_text(encoding="utf-8")
    except (OSError, UnicodeError):
        return False
    return any(
        line.strip() in {"ID=nixos", "ID='nixos'", 'ID="nixos"'}
        for line in os_release.splitlines()
    )


def capture_bootstrap_lineage(root: Path, host: str | None = None) -> dict[str, object]:
    """Record the generated bootstrap config without embedding host-local paths."""
    try:
        import tomllib
    except ModuleNotFoundError:
        tomllib = None

    candidates = [path for path in (root / "bootstrap.toml", root / "config.toml") if path.is_file()]
    errors: list[str] = []
    if len(candidates) != 1:
        errors.append("expected exactly one bootstrap.toml or config.toml")
        return {
            "schema": "trust.bootstrap-lineage.v1",
            "status": "rejected",
            "mode": "unknown",
            "trust_from_trust": False,
            "config_path": None,
            "config_sha256": None,
            "declared_stage0_overrides": [],
            "validated_seed": None,
            "genesis_adapter": None,
            "errors": errors,
        }
    config = candidates[0]
    try:
        content = config.read_bytes()
    except OSError as error:
        errors.append(f"could not read bootstrap config: {error}")
        content = b""
    if tomllib is None:
        errors.append("Python 3.11+ tomllib is required to classify bootstrap lineage")
        parsed = {}
    else:
        try:
            parsed = tomllib.loads(content.decode("utf-8"))
        except (UnicodeError, tomllib.TOMLDecodeError) as error:
            errors.append(f"bootstrap config is not valid UTF-8 TOML: {error}")
            parsed = {}
    build_table = parsed.get("build", {})
    if not isinstance(build_table, dict):
        errors.append("bootstrap config [build] value is not a table")
        build_table = {}
    stage0_override_keys = {
        "rustc",
        "cargo",
        "rustdoc",
        "rustfmt",
        "cargo-clippy",
    }
    declared_stage0_overrides = sorted(stage0_override_keys & set(build_table))
    seed_marker = b"(seed stage0 mode)" in content
    genesis_marker = b"(genesis stage0 mode)" in content
    genesis_override = b"genesis-stage0" in content
    validated_seed: dict[str, object] | None = None
    genesis_adapter: dict[str, object] | None = None
    if (
        seed_marker
        and not genesis_marker
        and not genesis_override
        and not declared_stage0_overrides
    ):
        mode = "seed"
        if host is None:
            errors.append("host triple is required to validate seed lineage")
            status = "rejected"
        else:
            validated_seed = capture_validated_seed_lineage(root, host)
            errors.extend(str(error) for error in validated_seed.get("errors", []))
            nix_patch_setting = build_table.get("patch-binaries-for-nix")
            if nix_patch_setting is True or (
                nix_patch_setting is None and _nixos_host()
            ):
                errors.append(
                    "immutable seed release provenance does not model bootstrap's "
                    "Nix patchelf transformation"
                )
            if validated_seed.get("status") == "validated":
                status = "trust_from_trust"
            elif validated_seed.get("status") == "validated-payloads":
                status = "seed-validated-pending-hydration"
            else:
                status = "rejected"
    elif genesis_marker and not seed_marker and genesis_override:
        mode = "genesis"
        if host is None:
            errors.append("host triple is required to validate genesis authority")
            status = "rejected"
        else:
            genesis_adapter = _capture_genesis_adapter_authority(root, host, build_table)
            errors.extend(str(error) for error in genesis_adapter.get("errors", []))
            status = (
                "local_genesis"
                if genesis_adapter.get("status") == "ready"
                else "rejected"
            )
    else:
        mode = "unknown"
        status = "rejected"
        errors.append("bootstrap config does not unambiguously declare seed or genesis mode")
    return {
        "schema": "trust.bootstrap-lineage.v1",
        "status": status if not errors else "rejected",
        "mode": mode,
        "trust_from_trust": status == "trust_from_trust" and not errors,
        "config_path": _repository_relative_path(root, config),
        "config_sha256": hashlib.sha256(content).hexdigest(),
        "declared_stage0_overrides": declared_stage0_overrides,
        "validated_seed": validated_seed,
        "genesis_adapter": genesis_adapter,
        "errors": sorted(set(errors)),
    }


def _bind_bootstrap_lineage(
    before: dict[str, object] | None,
    after: dict[str, object],
) -> dict[str, object]:
    lineage = dict(after)
    errors = [str(error) for error in after.get("errors", [])]
    config_stable = before is not None and all(
        before.get(field) == after.get(field)
        for field in (
            "schema",
            "mode",
            "config_path",
            "config_sha256",
            "declared_stage0_overrides",
        )
    )
    if before is None:
        errors.append("missing pre-build bootstrap-lineage snapshot")
    else:
        errors.extend(str(error) for error in before.get("errors", []))
        if before.get("status") == "rejected":
            errors.append("pre-build bootstrap lineage was rejected")
        if not config_stable:
            errors.append("bootstrap configuration changed during the build")
    stable = config_stable
    mode = after.get("mode")
    if before is not None and before.get("mode") != mode:
        errors.append("bootstrap mode changed during the build")
    if mode == "seed":
        if before is not None and (
            before.get("genesis_adapter") is not None
            or after.get("genesis_adapter") is not None
        ):
            errors.append("seed bootstrap unexpectedly carries genesis adapter authority")
        before_seed = before.get("validated_seed") if before is not None else None
        after_seed = after.get("validated_seed")
        if not isinstance(before_seed, dict) or not isinstance(after_seed, dict):
            errors.append("validated seed lineage is missing")
            stable = False
        else:
            before_errors = before_seed.get("errors")
            after_errors = after_seed.get("errors")
            if before_errors != [] or after_errors != []:
                errors.append("validated seed lineage contains errors")
            before_authority = before_seed.get("authority_sha256")
            after_authority = after_seed.get("authority_sha256")
            authority_stable = before_authority == after_authority
            if not authority_stable:
                errors.append("seed pins, payloads, or admission changed during the build")
            before_compiler = before_seed.get("compiler")
            after_compiler = after_seed.get("compiler")
            if not isinstance(before_compiler, dict) or not isinstance(after_compiler, dict):
                errors.append("seed compiler identity is missing")
                compiler_stable: bool | None = False
                compiler_materialized = False
            else:
                before_compiler_status = before_compiler.get("status")
                after_compiler_status = after_compiler.get("status")
                compiler_materialized = before_compiler_status == "not-materialized"
                before_compiler_sha256 = (
                    None
                    if compiler_materialized
                    else hashlib.sha256(
                        json.dumps(
                            before_compiler,
                            sort_keys=True,
                            separators=(",", ":"),
                        ).encode("utf-8")
                    ).hexdigest()
                )
                after_compiler_sha256 = hashlib.sha256(
                    json.dumps(
                        after_compiler,
                        sort_keys=True,
                        separators=(",", ":"),
                    ).encode("utf-8")
                ).hexdigest()
                compiler_stable = (
                    None
                    if compiler_materialized
                    else before_compiler == after_compiler
                )
                if before_compiler_status not in {"not-materialized", "validated"}:
                    errors.append("pre-build seed compiler identity was rejected")
                if after_compiler_status != "validated":
                    errors.append("post-build seed compiler identity is not validated")
                if compiler_stable is False:
                    errors.append("hydrated seed compiler changed during the build")
            bound_seed = dict(after_seed)
            bound_seed.update(
                {
                    "stable_across_build": authority_stable
                    and compiler_stable is not False,
                    "pre_build_authority_sha256": before_authority,
                    "post_build_authority_sha256": after_authority,
                    "compiler_materialized_during_build": compiler_materialized,
                    "compiler_stable_across_build": compiler_stable,
                    "materialization_status": (
                        "fresh-from-validated-archives"
                        if compiler_materialized
                        else "preexisting-unproven"
                    ),
                    "pre_build_compiler_identity_sha256": before_compiler_sha256,
                    "post_build_compiler_identity_sha256": after_compiler_sha256,
                }
            )
            lineage["validated_seed"] = bound_seed
            stable = stable and bool(bound_seed["stable_across_build"])
        if after.get("status") != "trust_from_trust":
            errors.append("post-build bootstrap is not bound to a validated seed compiler")
    elif mode == "genesis":
        if before is None or before.get("status") != "local_genesis" or after.get(
            "status"
        ) != "local_genesis":
            errors.append("genesis bootstrap classification changed during the build")
        if before is not None and (
            before.get("validated_seed") is not None or after.get("validated_seed") is not None
        ):
            errors.append("genesis bootstrap unexpectedly carries validated seed authority")
        before_genesis = before.get("genesis_adapter") if before is not None else None
        after_genesis = after.get("genesis_adapter")
        if not isinstance(before_genesis, dict) or not isinstance(after_genesis, dict):
            errors.append("genesis adapter authority is missing")
            genesis_stable = False
        else:
            if (
                before_genesis.get("schema") != "trust.genesis-adapter-authority.v1"
                or after_genesis.get("schema") != "trust.genesis-adapter-authority.v1"
                or before_genesis.get("status") != "ready"
                or after_genesis.get("status") != "ready"
                or before_genesis.get("errors") != []
                or after_genesis.get("errors") != []
            ):
                errors.append("genesis adapter authority is not canonical and ready")
            before_genesis_sha = before_genesis.get("authority_sha256")
            after_genesis_sha = after_genesis.get("authority_sha256")
            genesis_stable = (
                before_genesis_sha == after_genesis_sha
                and before_genesis.get("authority") == after_genesis.get("authority")
            )
            if not genesis_stable:
                errors.append("genesis adapter or backing producer authority changed during build")
            bound_genesis = dict(after_genesis)
            bound_genesis.update(
                {
                    "stable_across_build": genesis_stable,
                    "pre_build_authority_sha256": before_genesis_sha,
                    "post_build_authority_sha256": after_genesis_sha,
                }
            )
            lineage["genesis_adapter"] = bound_genesis
        stable = stable and genesis_stable
    else:
        errors.append("bootstrap mode is neither seed nor genesis")
    if errors:
        lineage["status"] = "rejected"
        lineage["trust_from_trust"] = False
    elif mode == "seed":
        lineage["status"] = "trust_from_trust"
        lineage["trust_from_trust"] = True
    else:
        lineage["status"] = "local_genesis"
        lineage["trust_from_trust"] = False
    lineage["stable_across_build"] = stable
    lineage["pre_build_config_sha256"] = (
        before.get("config_sha256") if before is not None else None
    )
    lineage["post_build_config_sha256"] = after.get("config_sha256")
    lineage["errors"] = sorted(set(errors))
    return lineage


def _classify_receipt_status(
    source_status: object,
    bootstrap_lineage: dict[str, object],
) -> str:
    if source_status != "immutable_release" or bootstrap_lineage.get(
        "status"
    ) != "trust_from_trust":
        return "candidate-ready"
    validated_seed = bootstrap_lineage.get("validated_seed")
    if not isinstance(validated_seed, dict) or validated_seed.get("status") != "validated":
        return "rejected"
    if validated_seed.get("materialization_status") != "fresh-from-validated-archives":
        return "candidate-ready"
    admission_status = validated_seed.get("admission_status")
    if admission_status == "public-promoted":
        return "release-ready"
    if admission_status == "internal-admitted":
        return "internal-release-ready"
    return "rejected"


def _ambient_build_authority_overrides(
    env: dict[str, str] | os._Environ[str],
) -> dict[str, str]:
    overrides: dict[str, str] = {}
    for name, value in env.items():
        # This private marker only prevents an old-Python re-exec loop.  It is
        # consumed by this driver and scrubbed before x.py; treating it as build
        # authority would make the supported interpreter upgrade path unusable.
        if name == REEXEC_GUARD_ENV:
            continue
        if name in BUILD_AUTHORITY_ENV_NAMES or any(
            name.startswith(prefix) for prefix in BUILD_AUTHORITY_ENV_PREFIXES
        ):
            overrides[name] = hashlib.sha256(value.encode("utf-8")).hexdigest()
    return dict(sorted(overrides.items()))


def _native_tool_record(name: str, path: str | None, args: tuple[str, ...]) -> dict[str, object]:
    record: dict[str, object] = {"name": name, "resolved_local_path": path}
    if path is None:
        record["status"] = "missing"
        return record
    candidate = Path(path)
    try:
        record.update(
            {
                "status": "bound",
                "resolved_real_path": str(candidate.resolve()),
                "sha256": _sha256_file(candidate),
                "identity": tool_version(
                    path,
                    args,
                    environment=(
                        _provenance_git_environment() if name == "git" else None
                    ),
                ),
            }
        )
    except OSError as error:
        record.update({"status": "rejected", "error": str(error)})
    return record


def _darwin_platform_toolchain() -> tuple[dict[str, object], list[str]]:
    """Resolve the actual Apple toolchain selected behind /usr/bin dispatchers."""
    errors: list[str] = []
    xcrun = which("xcrun")
    xcode_select = which("xcode-select")
    record: dict[str, object] = {
        "schema": "trust.darwin-platform-toolchain.v1",
        "xcrun": _native_tool_record("xcrun", xcrun, ("--version",)),
        "xcode_select": _native_tool_record(
            "xcode-select", xcode_select, ("--version",)
        ),
    }
    if xcrun is None or xcode_select is None:
        errors.append("xcrun or xcode-select is missing")
        record.update({"status": "rejected", "tools": [], "errors": errors})
        return record, errors

    developer_ok, developer_value = _capture_identity(Path(xcode_select), ("-p",))
    developer_path = Path(developer_value) if developer_ok else None
    developer_real: Path | None = None
    if developer_path is None or not developer_path.is_absolute() or not developer_path.is_dir():
        errors.append("xcode-select did not identify an absolute developer directory")
    else:
        try:
            developer_real = developer_path.resolve(strict=True)
        except OSError as error:
            errors.append(f"could not resolve the active developer directory: {error}")
    allowed_developer_roots = {
        Path("/Applications/Xcode.app/Contents/Developer"),
        Path("/Library/Developer/CommandLineTools"),
    }
    if developer_real not in allowed_developer_roots:
        errors.append("active Apple developer directory is outside the admitted roots")
    record.update(
        {
            "developer_selected_path": str(developer_path) if developer_path else None,
            "developer_real_path": str(developer_real) if developer_real else None,
        }
    )

    selected_tools: list[dict[str, object]] = []
    identity_args = {
        "clang": ("--version",),
        "clang++": ("--version",),
        "ar": ("-V",),
        "ld": ("-v",),
        "nm": ("--version",),
        "ranlib": ("-V",),
        "strip": ("-V",),
        "git": ("--version",),
        "make": ("--version",),
        "otool": ("--version",),
        "python3": ("--version",),
    }
    for name, args in identity_args.items():
        selected_ok, selected_value = _capture_identity(
            Path(xcrun), ("--find", name)
        )
        selected_path = Path(selected_value) if selected_ok else None
        tool_record = _native_tool_record(
            name,
            str(selected_path) if selected_path is not None else None,
            args,
        )
        tool_record["xcrun_selected_path"] = (
            str(selected_path) if selected_path is not None else None
        )
        selected_real_value = tool_record.get("resolved_real_path")
        selected_within_developer = False
        if developer_real is not None and isinstance(selected_real_value, str):
            try:
                Path(selected_real_value).relative_to(developer_real)
            except ValueError:
                selected_within_developer = False
            else:
                selected_within_developer = True
        tool_record["within_active_developer_dir"] = selected_within_developer
        if tool_record.get("status") != "bound" or not selected_within_developer:
            errors.append(f"xcrun-selected {name} is not bound inside the developer directory")
        selected_tools.append(tool_record)
    record["tools"] = selected_tools

    sdk_ok, sdk_value = _capture_identity(Path(xcrun), ("--show-sdk-path",))
    version_ok, sdk_version = _capture_identity(Path(xcrun), ("--show-sdk-version",))
    sdk_selected = Path(sdk_value) if sdk_ok else None
    sdk_real: Path | None = None
    if sdk_selected is None or not sdk_selected.is_absolute() or not sdk_selected.is_dir():
        errors.append("xcrun did not identify an absolute SDK directory")
    else:
        try:
            sdk_real = sdk_selected.resolve(strict=True)
        except OSError as error:
            errors.append(f"could not resolve the selected Darwin SDK: {error}")
    sdk_within_developer = False
    if developer_real is not None and sdk_real is not None:
        try:
            sdk_real.relative_to(developer_real)
        except ValueError:
            sdk_within_developer = False
        else:
            sdk_within_developer = True
    if not sdk_within_developer:
        errors.append("selected Darwin SDK is outside the active developer directory")
    settings = sdk_real / "SDKSettings.json" if sdk_real is not None else None
    settings_sha256: str | None = None
    if settings is None or not settings.is_file() or settings.is_symlink():
        errors.append("Darwin SDKSettings.json is missing, non-regular, or a symlink")
    else:
        try:
            settings_sha256 = _sha256_file(settings)
        except OSError as error:
            errors.append(f"could not hash Darwin SDK settings: {error}")
    sdk_link_target: str | None = None
    if sdk_selected is not None and sdk_selected.is_symlink():
        try:
            sdk_link_target = os.readlink(sdk_selected)
        except OSError as error:
            errors.append(f"could not read selected Darwin SDK symlink: {error}")
    record["sdk"] = {
        "selected_path": str(sdk_selected) if sdk_selected is not None else None,
        "selected_link_target": sdk_link_target,
        "real_path": str(sdk_real) if sdk_real is not None else None,
        "within_active_developer_dir": sdk_within_developer,
        "version": sdk_version if version_ok else None,
        "settings_path": str(settings) if settings is not None else None,
        "settings_sha256": settings_sha256,
    }
    if not version_ok:
        errors.append("Darwin SDK version is unavailable")
    record["status"] = "bound" if not errors else "rejected"
    record["errors"] = sorted(set(errors))
    return record, errors


def _is_macho(path: Path) -> bool:
    try:
        with path.open("rb") as stream:
            magic = stream.read(4)
    except OSError:
        return False
    return magic in {
        b"\xfe\xed\xfa\xce",
        b"\xce\xfa\xed\xfe",
        b"\xfe\xed\xfa\xcf",
        b"\xcf\xfa\xed\xfe",
        b"\xca\xfe\xba\xbe",
        b"\xbe\xba\xfe\xca",
        b"\xca\xfe\xba\xbf",
        b"\xbf\xba\xfe\xca",
    }


def _darwin_rpaths(otool: Path, binary: Path) -> tuple[list[str], str | None]:
    try:
        completed = subprocess.run(
            [str(otool), "-l", str(binary)],
            capture_output=True,
            text=True,
            check=False,
            timeout=30,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        return [], str(error)
    if completed.returncode != 0:
        return [], (completed.stderr or completed.stdout).strip()
    rpaths: list[str] = []
    expecting_path = False
    for line in completed.stdout.splitlines():
        stripped = line.strip()
        if stripped == "cmd LC_RPATH":
            expecting_path = True
            continue
        if expecting_path and stripped.startswith("path "):
            rpaths.append(stripped[5:].split(" (offset ", 1)[0])
            expecting_path = False
    return rpaths, None


def _darwin_install_id(otool: Path, binary: Path) -> str | None:
    try:
        completed = subprocess.run(
            [str(otool), "-D", str(binary)],
            capture_output=True,
            text=True,
            check=False,
            timeout=30,
        )
    except (OSError, subprocess.TimeoutExpired):
        return None
    if completed.returncode != 0:
        return None
    identifiers = [
        line.strip()
        for line in completed.stdout.splitlines()
        if line.strip()
        and not line.strip().endswith(":")
        and " (architecture " not in line
    ]
    return identifiers[0] if len(set(identifiers)) == 1 else None


def _resolve_darwin_dependency(
    raw: str,
    *,
    loader: Path,
    executable: Path,
    otool: Path,
) -> tuple[Path | None, str | None]:
    def expand(value: str) -> Path | None:
        if value == "@loader_path":
            return loader.parent
        if value.startswith("@loader_path/"):
            return loader.parent / value.removeprefix("@loader_path/")
        if value == "@executable_path":
            return executable.parent
        if value.startswith("@executable_path/"):
            return executable.parent / value.removeprefix("@executable_path/")
        if value.startswith("/"):
            return Path(value)
        return None

    direct = expand(raw)
    if direct is not None:
        return direct, None
    if not raw.startswith("@rpath/"):
        return None, f"unsupported Darwin dependency spelling: {raw}"
    suffix = raw.removeprefix("@rpath/")
    loader_rpaths, loader_error = _darwin_rpaths(otool, loader)
    executable_rpaths, executable_error = _darwin_rpaths(otool, executable)
    if loader_error is not None and executable_error is not None:
        return None, f"could not inspect Darwin rpaths for {raw}"
    candidates: list[Path] = []
    for rpath in dict.fromkeys([*loader_rpaths, *executable_rpaths]):
        expanded = expand(rpath)
        if expanded is not None:
            candidate = expanded / suffix
            if candidate.is_file():
                candidates.append(candidate)
    real_candidates = sorted({str(candidate.resolve()) for candidate in candidates})
    if len(real_candidates) != 1:
        return None, f"Darwin @rpath dependency is missing or ambiguous: {raw}"
    return Path(real_candidates[0]), None


def _capture_darwin_dynamic_dependencies(
    roots: list[Path],
    otool: Path,
) -> dict[str, object]:
    """Hash the recursive non-system Mach-O dependency closure of build tools."""
    errors: list[str] = []
    root_paths = sorted({str(path.resolve()) for path in roots if path.is_file()})
    queue: list[tuple[Path, Path]] = [
        (Path(path), Path(path)) for path in root_paths if _is_macho(Path(path))
    ]
    inspected: set[tuple[str, str]] = set()
    dependencies: dict[str, dict[str, object]] = {}
    while queue:
        binary, executable = queue.pop(0)
        state = (str(binary), str(executable))
        if state in inspected:
            continue
        inspected.add(state)
        try:
            completed = subprocess.run(
                [str(otool), "-L", str(binary)],
                capture_output=True,
                text=True,
                check=False,
                timeout=30,
            )
        except (OSError, subprocess.TimeoutExpired) as error:
            errors.append(f"could not inspect Mach-O dependencies for {binary}: {error}")
            continue
        if completed.returncode != 0:
            errors.append(f"otool rejected Mach-O dependency query for {binary}")
            continue
        install_id = _darwin_install_id(otool, binary)
        for line in completed.stdout.splitlines()[1:]:
            if not line[:1].isspace() or " (compatibility version " not in line:
                continue
            raw = line.strip().split(" (compatibility version ", 1)[0]
            if not raw:
                continue
            if install_id is not None and raw == install_id:
                continue
            if raw.startswith("/usr/lib/") or raw.startswith("/System/Library/"):
                continue
            selected, resolution_error = _resolve_darwin_dependency(
                raw,
                loader=binary,
                executable=executable,
                otool=otool,
            )
            if resolution_error is not None or selected is None:
                errors.append(
                    resolution_error
                    or f"could not resolve Darwin dependency {raw} for {binary}"
                )
                continue
            if not selected.is_file():
                errors.append(f"non-system Darwin dependency is missing: {selected}")
                continue
            try:
                real = selected.resolve(strict=True)
                sha256 = _sha256_file(real)
                metadata = real.lstat()
            except OSError as error:
                errors.append(f"could not bind Darwin dependency {selected}: {error}")
                continue
            selected_record = {
                "path": str(selected),
                "link_target": os.readlink(selected) if selected.is_symlink() else None,
            }
            record = {
                "resolved_real_path": str(real),
                "mode": stat.S_IMODE(metadata.st_mode),
                "size": metadata.st_size,
                "sha256": sha256,
                "selected_paths": [selected_record],
            }
            existing = dependencies.get(str(real))
            if existing is None:
                dependencies[str(real)] = record
            else:
                for field in ("resolved_real_path", "mode", "size", "sha256"):
                    if existing.get(field) != record.get(field):
                        errors.append(f"Darwin dependency identity changed: {real}")
                selected_paths = existing.get("selected_paths")
                if isinstance(selected_paths, list) and selected_record not in selected_paths:
                    selected_paths.append(selected_record)
                    selected_paths.sort(key=lambda row: str(row["path"]))
            if _is_macho(real):
                queue.append((real, executable))
    closure = {
        "schema": "trust.darwin-dynamic-dependency-closure.v1",
        "roots": root_paths,
        "otool_path": str(otool),
        "dependencies": sorted(
            dependencies.values(), key=lambda row: str(row["resolved_real_path"])
        ),
    }
    closure_sha256 = hashlib.sha256(
        json.dumps(closure, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()
    return {
        **closure,
        "status": "ready" if not errors else "rejected",
        "closure_sha256": closure_sha256,
        "errors": sorted(set(errors)),
    }


def capture_build_authority(
    root: Path,
    host: str,
    llvm_config: str | None,
) -> dict[str, object]:
    """Bind ambient build authority, native tools, and the selected SDK."""
    errors: list[str] = []
    overrides = _ambient_build_authority_overrides(os.environ)
    if overrides:
        errors.append(
            "ambient build-authority overrides are set: " + ", ".join(overrides)
        )

    cargo_home = Path(os.environ.get("CARGO_HOME", str(Path.home() / ".cargo")))
    ambient_cargo_configs = [
        path.name
        for path in (cargo_home / "config.toml", cargo_home / "config")
        if path.is_file()
    ]
    if ambient_cargo_configs:
        errors.append("ambient Cargo configuration is present")

    cc = which("cc") or which("clang") or which("gcc")
    cxx = which("c++") or which("clang++") or which("g++")
    fixed_git = fixed_git_executable()
    tool_specs: list[tuple[str, str | None, tuple[str, ...], bool]] = [
        ("cc", cc, ("--version",), True),
        ("c++", cxx, ("--version",), True),
        ("ar", which("ar"), ("--version",), True),
        ("ld", which("ld"), ("-v",), True),
        ("nm", which("nm"), ("--version",), True),
        ("ranlib", which("ranlib"), ("--version",), True),
        ("strip", which("strip"), ("--version",), True),
        ("make", which("make"), ("--version",), True),
        ("perl", which("perl"), ("-v",), True),
        ("cmake", which("cmake"), ("--version",), llvm_config is None),
        ("ninja", which("ninja"), ("--version",), llvm_config is None),
        ("pkg-config", which("pkg-config"), ("--version",), True),
        ("sh", which("sh"), ("--version",), True),
        (
            "git",
            str(fixed_git) if fixed_git is not None else None,
            ("--version",),
            True,
        ),
        ("python", sys.executable, ("--version",), True),
        ("brew", which("brew"), ("--version",), False),
    ]
    tools: list[dict[str, object]] = []
    for name, path, args, required in tool_specs:
        record = _native_tool_record(name, path, args)
        record["required"] = required
        tools.append(record)
        if required and record.get("status") != "bound":
            errors.append(f"required native build tool is not bound: {name}")

    selected_llvm: dict[str, object] | None = None
    if llvm_config is not None:
        selected_llvm = _native_tool_record("llvm-config", llvm_config, ("--version",))
        if selected_llvm.get("status") != "bound":
            errors.append("explicit llvm-config is not bound")

    platform_toolchain: dict[str, object] | None = None
    sdk: dict[str, object]
    if platform.system().lower() == "darwin":
        platform_toolchain, darwin_errors = _darwin_platform_toolchain()
        errors.extend(darwin_errors)
        sdk = {
            "platform": "darwin",
            "status": platform_toolchain.get("status"),
            **dict(platform_toolchain.get("sdk", {})),
        }
    else:
        sdk = {
            "platform": platform.system().lower(),
            "status": "system-native",
        }

    derived_library_paths: list[dict[str, object]] = []
    homebrew_library: Path | None = None
    if platform.system().lower() == "darwin":
        homebrew_prefix, homebrew_library = _selected_homebrew_library_path()
        if homebrew_prefix is not None and homebrew_library is not None:
            library_tree = _capture_external_tree(
                homebrew_library,
                homebrew_prefix,
                bind_external_symlink_targets=True,
            )
            derived_library_paths.append(library_tree)
            errors.extend(str(error) for error in library_tree.get("errors", []))

    dynamic_dependencies: dict[str, object] | None = None
    if platform.system().lower() == "darwin" and platform_toolchain is not None:
        selected_platform_tools = platform_toolchain.get("tools")
        selected_platform_rows = (
            selected_platform_tools if isinstance(selected_platform_tools, list) else []
        )
        selected_platform_names = {
            str(row.get("name"))
            for row in selected_platform_rows
            if isinstance(row, dict) and row.get("status") == "bound"
        }
        dispatcher_replacements = {
            "cc": "clang",
            "c++": "clang++",
            "ar": "ar",
            "ld": "ld",
            "nm": "nm",
            "ranlib": "ranlib",
            "strip": "strip",
            "git": "git",
            "make": "make",
            "python": "python3",
        }
        otool_path_value = next(
            (
                row.get("resolved_real_path")
                for row in selected_platform_rows
                if isinstance(row, dict) and row.get("name") == "otool"
            ),
            None,
        )
        xcrun_record = platform_toolchain.get("xcrun")
        xcrun_sha256 = (
            xcrun_record.get("sha256") if isinstance(xcrun_record, dict) else None
        )
        dependency_roots: list[Path] = []
        for row in tools:
            resolved_value = row.get("resolved_real_path")
            if not isinstance(resolved_value, str):
                continue
            replacement = dispatcher_replacements.get(str(row.get("name")))
            selected_replacement = replacement in selected_platform_names
            looks_like_dispatcher = (
                str(row.get("resolved_local_path", "")).startswith("/usr/bin/")
                and row.get("sha256") == xcrun_sha256
            )
            if selected_replacement and looks_like_dispatcher:
                continue
            dependency_roots.append(Path(resolved_value))
        dependency_roots.extend(
            Path(str(row["resolved_real_path"]))
            for row in selected_platform_rows
            if isinstance(row, dict)
            and isinstance(row.get("resolved_real_path"), str)
        )
        for dispatcher_key in ("xcrun", "xcode_select"):
            dispatcher = platform_toolchain.get(dispatcher_key)
            if isinstance(dispatcher, dict) and isinstance(
                dispatcher.get("resolved_real_path"), str
            ):
                dependency_roots.append(Path(str(dispatcher["resolved_real_path"])))
        if selected_llvm is not None and isinstance(
            selected_llvm.get("resolved_real_path"), str
        ):
            dependency_roots.append(Path(str(selected_llvm["resolved_real_path"])))
        if homebrew_library is not None:
            try:
                homebrew_library_real = homebrew_library.resolve(strict=True)
            except OSError as error:
                errors.append(f"could not resolve admitted Homebrew library tree: {error}")
            else:
                for current_root, _directory_names, file_names in os.walk(
                    homebrew_library_real,
                    followlinks=False,
                ):
                    current = Path(current_root)
                    for name in file_names:
                        candidate = current / name
                        if candidate.is_file() and _is_macho(candidate):
                            dependency_roots.append(candidate)
        if not isinstance(otool_path_value, str):
            errors.append("xcrun-selected otool is unavailable for dependency binding")
            dynamic_dependencies = {
                "schema": "trust.darwin-dynamic-dependency-closure.v1",
                "status": "rejected",
                "errors": ["xcrun-selected otool is unavailable"],
            }
        else:
            dynamic_dependencies = _capture_darwin_dynamic_dependencies(
                dependency_roots,
                Path(otool_path_value),
            )
            errors.extend(
                str(error) for error in dynamic_dependencies.get("errors", [])
            )

    authority = {
        "schema": "trust.build-authority.v1",
        "host": host,
        "ambient_overrides": overrides,
        "ambient_cargo_configs": ambient_cargo_configs,
        "native_tools": tools,
        "selected_llvm": selected_llvm,
        "platform_toolchain": platform_toolchain,
        "sdk": sdk,
        "dynamic_dependencies": dynamic_dependencies,
        "derived_library_paths": derived_library_paths,
    }
    authority_sha256 = hashlib.sha256(
        json.dumps(authority, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()
    return {
        **authority,
        "status": "ready" if not errors else "rejected",
        "authority_sha256": authority_sha256,
        "errors": sorted(set(errors)),
    }


def _bind_build_authority(
    before: dict[str, object] | None,
    after: dict[str, object],
) -> dict[str, object]:
    authority = dict(after)
    errors = [str(error) for error in after.get("errors", [])]
    before_sha = before.get("authority_sha256") if before is not None else None
    after_sha = after.get("authority_sha256")
    stable = before is not None and before_sha == after_sha
    if before is None:
        errors.append("missing pre-build native authority snapshot")
    else:
        errors.extend(str(error) for error in before.get("errors", []))
        if before.get("status") != "ready":
            errors.append("pre-build native authority was rejected")
        if not stable:
            errors.append("native tools, SDK, PATH, or ambient authority changed during the build")
    authority.update(
        {
            "status": "ready" if not errors else "rejected",
            "stable_across_build": stable,
            "pre_build_authority_sha256": before_sha,
            "post_build_authority_sha256": after_sha,
            "errors": sorted(set(errors)),
        }
    )
    return authority


def audit_stage_tool_provenance(
    root: Path,
    host: str,
    stage: int,
    source_lineage_before: dict[str, object] | None = None,
    bootstrap_lineage_before: dict[str, object] | None = None,
    build_authority_before: dict[str, object] | None = None,
    llvm_config: str | None = None,
) -> bool:
    """Bind every release-facing stage tool to its x.py producer.

    The audit is intentionally structural, not a PATH/version-name heuristic:
    every public tool must hash to the exact stage-(N+1) tools-bin artifact
    built for the stage-N sysroot.  The receipt additionally binds the stage1
    producer compiler and final compiler to the repository commit and records
    whether bootstrap installed each tool by hard link or content-preserving
    copy.  A missing/unmapped tool, changed producer, stock public alias, or
    compiler/sysroot mismatch fails the one-command bootstrap.
    """
    stage_root = root / "build" / host / f"stage{stage}"
    bin_dir = stage_root / "bin"
    tools_dir = root / "build" / host / f"stage{stage + 1}-tools-bin" / host
    receipt_path = stage_root / "tool-provenance.json"
    errors: list[str] = []
    tools: list[dict[str, object]] = []
    source_lineage = _bind_source_lineage(
        source_lineage_before, capture_source_lineage(root)
    )
    bootstrap_lineage = _bind_bootstrap_lineage(
        bootstrap_lineage_before, capture_bootstrap_lineage(root, host)
    )
    build_authority = _bind_build_authority(
        build_authority_before,
        capture_build_authority(root, host, llvm_config),
    )

    expected_public = set(STAGE_TOOL_PRODUCERS) | {"rustc", "trustc"}
    if not bin_dir.is_dir():
        errors.append(f"missing stage tool directory: {bin_dir}")
        actual_public: set[str] = set()
    else:
        actual_public = {
            path.name.removesuffix(".exe")
            for path in bin_dir.iterdir()
            if path.is_file() and os.access(path, os.X_OK)
        }
    missing = sorted(expected_public - actual_public)
    unexpected = sorted(actual_public - expected_public)
    if missing:
        errors.append(f"missing public stage tools: {', '.join(missing)}")
    if unexpected:
        errors.append(f"unmapped public stage tools: {', '.join(unexpected)}")

    for public_name, producer_name in STAGE_TOOL_PRODUCERS.items():
        installed = bin_dir / _host_executable(public_name, host)
        producer = tools_dir / _host_executable(producer_name, host)
        record: dict[str, object] = {
            "name": public_name,
            "path": _repository_relative_path(root, installed),
            "producer_path": _repository_relative_path(root, producer),
            "producer_stage": stage + 1,
            "producer_compiler_stage": stage,
        }
        if not installed.is_file():
            errors.append(f"missing public tool {public_name}: {installed}")
            record["status"] = "missing"
            tools.append(record)
            continue
        if not producer.is_file():
            errors.append(f"missing x.py producer for {public_name}: {producer}")
            record["status"] = "producer_missing"
            tools.append(record)
            continue
        installed_sha = _sha256_file(installed)
        producer_sha = _sha256_file(producer)
        record.update(
            {
                "sha256": installed_sha,
                "producer_sha256": producer_sha,
                "same_inode": os.path.samefile(installed, producer),
                "status": "bound" if installed_sha == producer_sha else "mismatch",
            }
        )
        ok, version = _capture_identity(installed, ("--version",))
        record["version"] = version.splitlines()[0] if version else ""
        record["version_probe_ok"] = ok
        if installed_sha != producer_sha:
            errors.append(
                f"public tool {public_name} does not match its x.py producer: "
                f"{installed_sha} != {producer_sha}"
            )
        if not ok:
            errors.append(f"public tool {public_name} rejected --version: {version}")
        tools.append(record)

    trustc = bin_dir / _host_executable("trustc", host)
    rustc = bin_dir / _host_executable("rustc", host)
    builder = root / "build" / host / f"stage{stage - 1}" / "bin" / _host_executable(
        "trustc", host
    )
    compiler: dict[str, object] = {
        "path": _repository_relative_path(root, trustc),
        "compatibility_alias": _repository_relative_path(root, rustc),
        "producer_compiler": _repository_relative_path(root, builder),
        "producer_compiler_stage": stage - 1,
    }
    for label, path in (("compiler", trustc), ("producer compiler", builder)):
        if not path.is_file():
            errors.append(f"missing {label}: {path}")
            continue
        compiler[f"{label.replace(' ', '_')}_sha256"] = _sha256_file(path)
        ok, verbose = _capture_identity(path, ("-Vv",))
        compiler[f"{label.replace(' ', '_')}_verbose"] = verbose
        if not ok:
            errors.append(f"{label} rejected -Vv: {verbose}")
    if trustc.is_file() and rustc.is_file():
        trustc_sha = _sha256_file(trustc)
        rustc_sha = _sha256_file(rustc)
        compiler["compatibility_alias_same_inode"] = os.path.samefile(trustc, rustc)
        compiler["compatibility_alias_sha256"] = rustc_sha
        if trustc_sha != rustc_sha:
            errors.append("stage rustc compatibility alias differs from trustc")
    elif not rustc.is_file():
        errors.append(f"missing rustc compatibility alias: {rustc}")

    commit = next(
        (
            str(repository.get("head") or "")
            for repository in source_lineage.get("repositories", [])
            if repository.get("path") == "."
        ),
        "",
    )
    compiler["source_commit"] = commit
    verbose = str(compiler.get("compiler_verbose", ""))
    producer_verbose = str(compiler.get("producer_compiler_verbose", ""))
    if not commit:
        errors.append("could not resolve the source commit for compiler binding")
    else:
        for label, value in (("compiler", verbose), ("producer compiler", producer_verbose)):
            if f"commit-hash: {commit}" not in value:
                errors.append(f"{label} is not bound to source commit {commit}")
    if trustc.is_file():
        ok, sysroot = _capture_identity(trustc, ("--print", "sysroot"))
        compiler["reported_sysroot_local_path"] = sysroot
        compiler["reported_sysroot_path_scope"] = "local-diagnostic"
        try:
            sysroot_matches = ok and Path(sysroot).resolve() == stage_root.resolve()
        except OSError:
            sysroot_matches = False
        compiler["sysroot_matches"] = sysroot_matches
        if not sysroot_matches:
            errors.append(f"stage compiler reports foreign sysroot: {sysroot}")

    libexec = stage_root / "libexec"
    owned_helper = libexec / _host_executable("trust-analyzer-proc-macro-srv", host)
    retired_helper = libexec / _host_executable("rust-analyzer-proc-macro-srv", host)
    helper_producer = tools_dir / _host_executable("rust-analyzer-proc-macro-srv", host)
    helper: dict[str, object] = {
        "path": _repository_relative_path(root, owned_helper),
        "producer_path": _repository_relative_path(root, helper_producer),
        "producer_stage": stage + 1,
        "producer_compiler_stage": stage,
        "retired_public_path": _repository_relative_path(root, retired_helper),
        "retired_public_path_absent": not retired_helper.exists(),
    }
    if retired_helper.exists():
        errors.append(f"retired public proc-macro helper shipped: {retired_helper}")
    if not owned_helper.is_file() or not helper_producer.is_file():
        errors.append("Trust-owned proc-macro helper or its x.py producer is missing")
    else:
        helper_sha = _sha256_file(owned_helper)
        helper_producer_sha = _sha256_file(helper_producer)
        helper.update(
            {
                "sha256": helper_sha,
                "producer_sha256": helper_producer_sha,
                "same_inode": os.path.samefile(owned_helper, helper_producer),
                "status": "bound" if helper_sha == helper_producer_sha else "mismatch",
            }
        )
        if helper_sha != helper_producer_sha:
            errors.append("Trust-owned proc-macro helper does not match its x.py producer")

    tool_binding_status = "ready" if not errors else "rejected"
    lineage_status = source_lineage["status"]
    bootstrap_status = bootstrap_lineage["status"]
    if (
        tool_binding_status == "rejected"
        or lineage_status == "rejected"
        or bootstrap_status == "rejected"
        or build_authority["status"] == "rejected"
    ):
        status = "rejected"
    else:
        status = _classify_receipt_status(lineage_status, bootstrap_lineage)
    receipt = {
        "schema": "trust.stage-tool-provenance.v2",
        "status": status,
        "tool_binding_status": tool_binding_status,
        "source_tree_clean": source_lineage["source_tree_clean"],
        "trust_from_trust": bootstrap_lineage["trust_from_trust"],
        "stage": stage,
        "host": host,
        "path_scope": "repository-root-relative",
        "stage_root": _repository_relative_path(root, stage_root),
        "tools_dir": _repository_relative_path(root, tools_dir),
        "bootstrap_compiler_verification": dict(BOOTSTRAP_COMPILER_VERIFICATION),
        "compiler": compiler,
        "tools": tools,
        "proc_macro_helper": helper,
        "source_lineage": source_lineage,
        "bootstrap_lineage": bootstrap_lineage,
        "build_authority": build_authority,
        "errors": sorted(
            set(
                errors
                + list(source_lineage["errors"])
                + list(bootstrap_lineage["errors"])
                + list(build_authority["errors"])
            )
        ),
    }
    stage_root.mkdir(parents=True, exist_ok=True)
    temporary = receipt_path.with_suffix(".json.tmp")
    temporary.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(receipt_path)
    if status == "rejected":
        for error in receipt["errors"]:
            print(f"  ERROR: {error}")
        print(f"  rejected stage tool provenance -> {receipt_path}")
        return False
    print(f"  audited stage tool provenance ({status}) -> {receipt_path}")
    return True


def _require_receipt_path(
    root: Path,
    value: object,
    expected: Path,
    errors: list[str],
    label: str,
) -> None:
    expected_value = _repository_relative_path(root, expected)
    if value != expected_value:
        errors.append(f"{label} is not the expected repository-relative path {expected_value}")


def verify_stage_tool_provenance(
    root: Path,
    host: str,
    stage: int,
    *,
    require_immutable_lineage: bool = False,
    require_public_release: bool = False,
) -> bool:
    """Read-only verification of a previously written stage provenance receipt."""
    stage_root = root / "build" / host / f"stage{stage}"
    bin_dir = stage_root / "bin"
    tools_dir = root / "build" / host / f"stage{stage + 1}-tools-bin" / host
    receipt_path = stage_root / "tool-provenance.json"
    errors: list[str] = []
    try:
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        print(f"  ERROR: could not read stage provenance receipt {receipt_path}: {error}")
        return False
    if not isinstance(receipt, dict):
        print(f"  ERROR: stage provenance receipt is not a JSON object: {receipt_path}")
        return False

    if receipt.get("schema") != "trust.stage-tool-provenance.v2":
        errors.append("stage provenance receipt does not use schema v2")
    if receipt.get("stage") != stage or receipt.get("host") != host:
        errors.append("stage provenance receipt stage/host does not match the requested sysroot")
    if receipt.get("path_scope") != "repository-root-relative":
        errors.append("stage provenance receipt path scope is not repository-root-relative")
    if receipt.get("bootstrap_compiler_verification") != BOOTSTRAP_COMPILER_VERIFICATION:
        errors.append(
            "stage provenance receipt does not declare the exact non-self-proving "
            "bootstrap compiler verification mode"
        )
    _require_receipt_path(root, receipt.get("stage_root"), stage_root, errors, "stage_root")
    _require_receipt_path(root, receipt.get("tools_dir"), tools_dir, errors, "tools_dir")

    current_lineage = capture_source_lineage(root)
    recorded_lineage = receipt.get("source_lineage")
    if not isinstance(recorded_lineage, dict):
        errors.append("stage provenance receipt is missing source_lineage")
        recorded_lineage = {}
    if recorded_lineage.get("schema") != "trust.source-lineage.v1":
        errors.append("recorded source lineage does not use the canonical schema")
    if recorded_lineage.get("errors") != []:
        errors.append("recorded source lineage contains errors")
    if current_lineage["status"] == "rejected":
        errors.extend(str(error) for error in current_lineage["errors"])
    if current_lineage.get("schema") != "trust.source-lineage.v1" or current_lineage.get(
        "errors"
    ) != []:
        errors.append("current source lineage is not canonical and error-free")
    current_sha = current_lineage.get("closure_sha256")
    pre_sha = recorded_lineage.get("pre_build_closure_sha256")
    post_sha = recorded_lineage.get("post_build_closure_sha256")
    if recorded_lineage.get("stable_across_build") is not True or pre_sha != post_sha:
        errors.append("receipt does not bind a source closure stable across the build")
    if post_sha != current_sha or recorded_lineage.get("closure_sha256") != current_sha:
        errors.append("current recursive source closure differs from the receipt")
    if recorded_lineage.get("repositories") != current_lineage.get("repositories"):
        errors.append("current recursive repository rows differ from the receipt")
    current_lineage_status = current_lineage.get("status")
    if recorded_lineage.get("status") != current_lineage_status:
        errors.append("current source-lineage classification differs from the receipt")
    expected_source_clean = current_lineage_status == "immutable_release"
    if recorded_lineage.get("source_tree_clean") != expected_source_clean:
        errors.append("recorded source_tree_clean disagrees with current source lineage")
    if receipt.get("source_tree_clean") != expected_source_clean:
        errors.append("top-level source_tree_clean disagrees with current source lineage")

    current_bootstrap = capture_bootstrap_lineage(root, host)
    recorded_bootstrap = receipt.get("bootstrap_lineage")
    if not isinstance(recorded_bootstrap, dict):
        errors.append("stage provenance receipt is missing bootstrap_lineage")
        recorded_bootstrap = {}
    if recorded_bootstrap.get("schema") != "trust.bootstrap-lineage.v1":
        errors.append("recorded bootstrap lineage does not use the canonical schema")
    if recorded_bootstrap.get("errors") != []:
        errors.append("recorded bootstrap lineage contains errors")
    if current_bootstrap["status"] == "rejected":
        errors.extend(str(error) for error in current_bootstrap["errors"])
    if current_bootstrap.get("schema") != "trust.bootstrap-lineage.v1" or current_bootstrap.get(
        "errors"
    ) != []:
        errors.append("current bootstrap lineage is not canonical and error-free")
    if recorded_bootstrap.get("stable_across_build") is not True:
        errors.append("receipt does not bind a stable bootstrap configuration")
    current_config_sha256 = current_bootstrap.get("config_sha256")
    if (
        recorded_bootstrap.get("pre_build_config_sha256") != current_config_sha256
        or recorded_bootstrap.get("post_build_config_sha256") != current_config_sha256
    ):
        errors.append("bootstrap config pre/post digests do not match current config")
    for field in (
        "status",
        "mode",
        "trust_from_trust",
        "config_path",
        "config_sha256",
        "declared_stage0_overrides",
    ):
        if recorded_bootstrap.get(field) != current_bootstrap.get(field):
            errors.append(f"current bootstrap {field} differs from the receipt")
    current_trust_from_trust = current_bootstrap.get("status") == "trust_from_trust"
    if receipt.get("trust_from_trust") != current_trust_from_trust:
        errors.append("top-level trust_from_trust disagrees with current bootstrap lineage")
    recorded_seed = recorded_bootstrap.get("validated_seed")
    current_seed = current_bootstrap.get("validated_seed")
    recorded_genesis = recorded_bootstrap.get("genesis_adapter")
    current_genesis = current_bootstrap.get("genesis_adapter")
    if current_bootstrap.get("mode") == "seed":
        if recorded_genesis is not None or current_genesis is not None:
            errors.append("seed-mode bootstrap unexpectedly carries genesis authority")
        if not isinstance(recorded_seed, dict) or not isinstance(current_seed, dict):
            errors.append("seed-mode receipt is missing validated seed authority")
        else:
            if recorded_seed.get("schema") != "trust.validated-seed-lineage.v1":
                errors.append("recorded validated seed does not use the canonical schema")
            if recorded_seed.get("status") != "validated" or current_seed.get(
                "status"
            ) != "validated":
                errors.append("validated seed status is not validated")
            if recorded_seed.get("errors") != [] or current_seed.get("errors") != []:
                errors.append("validated seed lineage contains errors")
            if recorded_seed.get("stable_across_build") is not True:
                errors.append("receipt does not bind seed authority stable across the build")
            seed_sha = current_seed.get("authority_sha256")
            if (
                recorded_seed.get("pre_build_authority_sha256") != seed_sha
                or recorded_seed.get("post_build_authority_sha256") != seed_sha
                or recorded_seed.get("authority_sha256") != seed_sha
                or recorded_seed.get("authority") != current_seed.get("authority")
            ):
                errors.append("current seed pins, payloads, or admission differ from the receipt")
            if recorded_seed.get("admission_status") != current_seed.get(
                "admission_status"
            ):
                errors.append("current seed admission class differs from the receipt")
            if recorded_seed.get("compiler") != current_seed.get("compiler"):
                errors.append("current hydrated seed compiler differs from the receipt")
            compiler = current_seed.get("compiler")
            if not isinstance(compiler, dict) or compiler.get(
                "schema"
            ) != "trust.seed-compiler-identity.v1" or compiler.get("status") != "validated" or compiler.get(
                "errors"
            ) != []:
                errors.append("current hydrated seed compiler identity is not canonical")
            current_compiler_sha256 = (
                hashlib.sha256(
                    json.dumps(
                        compiler,
                        sort_keys=True,
                        separators=(",", ":"),
                    ).encode("utf-8")
                ).hexdigest()
                if isinstance(compiler, dict)
                else None
            )
            materialized = recorded_seed.get("compiler_materialized_during_build")
            compiler_stable = recorded_seed.get("compiler_stable_across_build")
            materialization_status = recorded_seed.get("materialization_status")
            pre_compiler_sha256 = recorded_seed.get(
                "pre_build_compiler_identity_sha256"
            )
            post_compiler_sha256 = recorded_seed.get(
                "post_build_compiler_identity_sha256"
            )
            if materialized is True:
                valid_history = (
                    compiler_stable is None
                    and materialization_status == "fresh-from-validated-archives"
                    and pre_compiler_sha256 is None
                    and post_compiler_sha256 == current_compiler_sha256
                )
            elif materialized is False:
                valid_history = (
                    compiler_stable is True
                    and materialization_status == "preexisting-unproven"
                    and pre_compiler_sha256 == current_compiler_sha256
                    and post_compiler_sha256 == current_compiler_sha256
                )
            else:
                valid_history = False
            if not valid_history:
                errors.append("seed compiler materialization history is contradictory")
    elif recorded_seed is not None or current_seed is not None:
        errors.append("non-seed bootstrap unexpectedly carries validated seed authority")

    if current_bootstrap.get("mode") == "genesis":
        if not isinstance(recorded_genesis, dict) or not isinstance(current_genesis, dict):
            errors.append("genesis-mode receipt is missing adapter authority")
        else:
            if (
                recorded_genesis.get("schema")
                != "trust.genesis-adapter-authority.v1"
                or current_genesis.get("schema")
                != "trust.genesis-adapter-authority.v1"
                or recorded_genesis.get("status") != "ready"
                or current_genesis.get("status") != "ready"
                or recorded_genesis.get("errors") != []
                or current_genesis.get("errors") != []
            ):
                errors.append("genesis adapter authority is not canonical and ready")
            current_genesis_sha = current_genesis.get("authority_sha256")
            if (
                recorded_genesis.get("stable_across_build") is not True
                or recorded_genesis.get("pre_build_authority_sha256")
                != current_genesis_sha
                or recorded_genesis.get("post_build_authority_sha256")
                != current_genesis_sha
                or recorded_genesis.get("authority_sha256") != current_genesis_sha
                or recorded_genesis.get("authority")
                != current_genesis.get("authority")
            ):
                errors.append("current genesis adapter authority differs from the receipt")
    elif recorded_genesis is not None or current_genesis is not None:
        errors.append("non-genesis bootstrap unexpectedly carries genesis authority")

    recorded_build_authority = receipt.get("build_authority")
    if not isinstance(recorded_build_authority, dict):
        errors.append("stage provenance receipt is missing build_authority")
        recorded_build_authority = {}
    recorded_llvm = recorded_build_authority.get("selected_llvm")
    verifier_llvm_config = (
        str(recorded_llvm.get("resolved_local_path"))
        if isinstance(recorded_llvm, dict)
        and isinstance(recorded_llvm.get("resolved_local_path"), str)
        else None
    )
    current_build_authority = capture_build_authority(root, host, verifier_llvm_config)
    if recorded_build_authority.get("schema") != "trust.build-authority.v1":
        errors.append("recorded build authority does not use the canonical schema")
    if recorded_build_authority.get("status") != "ready" or recorded_build_authority.get(
        "errors"
    ) != []:
        errors.append("recorded build authority is not ready and error-free")
    if current_build_authority.get("status") != "ready" or current_build_authority.get(
        "errors"
    ) != []:
        errors.append("current build authority is not ready and error-free")
    authority_sha = current_build_authority.get("authority_sha256")
    if (
        recorded_build_authority.get("stable_across_build") is not True
        or recorded_build_authority.get("pre_build_authority_sha256") != authority_sha
        or recorded_build_authority.get("post_build_authority_sha256") != authority_sha
        or recorded_build_authority.get("authority_sha256") != authority_sha
    ):
        errors.append("current native tool/SDK authority differs from the receipt")
    for field in (
        "host",
        "ambient_overrides",
        "ambient_cargo_configs",
        "native_tools",
        "selected_llvm",
        "platform_toolchain",
        "sdk",
        "dynamic_dependencies",
        "derived_library_paths",
    ):
        if recorded_build_authority.get(field) != current_build_authority.get(field):
            errors.append(f"current build authority {field} differs from the receipt")

    expected_public = set(STAGE_TOOL_PRODUCERS) | {"rustc", "trustc"}
    if not bin_dir.is_dir():
        errors.append(f"missing stage tool directory: {bin_dir}")
        actual_public: set[str] = set()
    else:
        actual_public = {
            path.name.removesuffix(".exe")
            for path in bin_dir.iterdir()
            if path.is_file() and os.access(path, os.X_OK)
        }
    if actual_public != expected_public:
        errors.append("current public stage tool inventory differs from the closed producer map")

    receipt_tools = receipt.get("tools")
    if not isinstance(receipt_tools, list):
        errors.append("receipt tools field is not a list")
        receipt_tools = []
    tool_rows: dict[str, dict[str, object]] = {}
    for row in receipt_tools:
        if not isinstance(row, dict) or not isinstance(row.get("name"), str):
            errors.append("receipt contains a malformed tool row")
            continue
        name = str(row["name"])
        if name in tool_rows:
            errors.append(f"receipt contains duplicate tool row {name}")
            continue
        tool_rows[name] = row
    if set(tool_rows) != set(STAGE_TOOL_PRODUCERS):
        errors.append("receipt tool rows do not exactly cover the closed producer map")

    for public_name, producer_name in STAGE_TOOL_PRODUCERS.items():
        row = tool_rows.get(public_name, {})
        installed = bin_dir / _host_executable(public_name, host)
        producer = tools_dir / _host_executable(producer_name, host)
        _require_receipt_path(root, row.get("path"), installed, errors, f"{public_name} path")
        _require_receipt_path(
            root, row.get("producer_path"), producer, errors, f"{public_name} producer_path"
        )
        if row.get("producer_stage") != stage + 1:
            errors.append(f"{public_name} producer_stage is not stage {stage + 1}")
        if row.get("producer_compiler_stage") != stage:
            errors.append(f"{public_name} producer_compiler_stage is not stage {stage}")
        if not installed.is_file() or not producer.is_file():
            errors.append(f"{public_name} or its exact producer is missing")
            continue
        installed_sha = _sha256_file(installed)
        producer_sha = _sha256_file(producer)
        if installed_sha != producer_sha:
            errors.append(f"{public_name} no longer matches its x.py producer")
        if row.get("sha256") != installed_sha or row.get("producer_sha256") != producer_sha:
            errors.append(f"{public_name} hashes differ from the receipt")
        same_inode = os.path.samefile(installed, producer)
        if row.get("same_inode") != same_inode or row.get("status") != "bound":
            errors.append(f"{public_name} binding metadata differs from the receipt")
        version_ok, version = _capture_identity(installed, ("--version",))
        current_version = version.splitlines()[0] if version else ""
        if not version_ok or row.get("version_probe_ok") is not True:
            errors.append(f"{public_name} version identity probe failed")
        if row.get("version") != current_version:
            errors.append(f"{public_name} version identity differs from the receipt")

    trustc = bin_dir / _host_executable("trustc", host)
    rustc = bin_dir / _host_executable("rustc", host)
    builder = root / "build" / host / f"stage{stage - 1}" / "bin" / _host_executable(
        "trustc", host
    )
    compiler = receipt.get("compiler")
    if not isinstance(compiler, dict):
        errors.append("receipt compiler field is not an object")
        compiler = {}
    _require_receipt_path(root, compiler.get("path"), trustc, errors, "compiler path")
    _require_receipt_path(
        root, compiler.get("compatibility_alias"), rustc, errors, "compiler alias"
    )
    _require_receipt_path(
        root, compiler.get("producer_compiler"), builder, errors, "producer compiler"
    )
    if compiler.get("producer_compiler_stage") != stage - 1:
        errors.append("compiler producer stage differs from the receipt")
    root_head = next(
        (
            str(repository.get("head") or "")
            for repository in current_lineage.get("repositories", [])
            if repository.get("path") == "."
        ),
        "",
    )
    if compiler.get("source_commit") != root_head:
        errors.append("compiler source commit differs from current root HEAD")
    for label, path, digest_field, verbose_field in (
        ("compiler", trustc, "compiler_sha256", "compiler_verbose"),
        (
            "producer compiler",
            builder,
            "producer_compiler_sha256",
            "producer_compiler_verbose",
        ),
    ):
        if not path.is_file():
            errors.append(f"missing {label}: {path}")
            continue
        digest = _sha256_file(path)
        if compiler.get(digest_field) != digest:
            errors.append(f"{label} hash differs from the receipt")
        version_ok, verbose = _capture_identity(path, ("-Vv",))
        if not version_ok or f"commit-hash: {root_head}" not in verbose:
            errors.append(f"{label} is not bound to current root HEAD")
        if compiler.get(verbose_field) != verbose:
            errors.append(f"{label} verbose identity differs from the receipt")
    if trustc.is_file() and rustc.is_file():
        alias_sha = _sha256_file(rustc)
        if alias_sha != _sha256_file(trustc):
            errors.append("rustc compatibility alias differs from trustc")
        if compiler.get("compatibility_alias_sha256") != alias_sha:
            errors.append("rustc compatibility alias hash differs from the receipt")
        if compiler.get("compatibility_alias_same_inode") != os.path.samefile(trustc, rustc):
            errors.append("rustc compatibility alias inode identity differs from the receipt")
        sysroot_ok, reported_sysroot = _capture_identity(trustc, ("--print", "sysroot"))
        try:
            sysroot_matches = sysroot_ok and Path(reported_sysroot).resolve() == stage_root.resolve()
        except OSError:
            sysroot_matches = False
        if not sysroot_matches or compiler.get("sysroot_matches") is not True:
            errors.append("compiler no longer reports the expected stage sysroot")
        if compiler.get("reported_sysroot_local_path") != reported_sysroot:
            errors.append("compiler-reported local sysroot differs from the receipt")
        if compiler.get("reported_sysroot_path_scope") != "local-diagnostic":
            errors.append("compiler-reported sysroot path scope is not local-diagnostic")

    helper = receipt.get("proc_macro_helper")
    if not isinstance(helper, dict):
        errors.append("receipt proc_macro_helper field is not an object")
        helper = {}
    owned_helper = stage_root / "libexec" / _host_executable(
        "trust-analyzer-proc-macro-srv", host
    )
    retired_helper = stage_root / "libexec" / _host_executable(
        "rust-analyzer-proc-macro-srv", host
    )
    helper_producer = tools_dir / _host_executable("rust-analyzer-proc-macro-srv", host)
    _require_receipt_path(root, helper.get("path"), owned_helper, errors, "proc-macro helper")
    _require_receipt_path(
        root, helper.get("producer_path"), helper_producer, errors, "proc-macro producer"
    )
    _require_receipt_path(
        root,
        helper.get("retired_public_path"),
        retired_helper,
        errors,
        "retired proc-macro helper",
    )
    if helper.get("producer_stage") != stage + 1 or helper.get(
        "producer_compiler_stage"
    ) != stage:
        errors.append("proc-macro helper producer stage metadata is incorrect")
    if retired_helper.exists() or helper.get("retired_public_path_absent") is not True:
        errors.append("retired public proc-macro helper is present or misreported")
    if not owned_helper.is_file() or not helper_producer.is_file():
        errors.append("Trust-owned proc-macro helper or producer is missing")
    else:
        helper_sha = _sha256_file(owned_helper)
        producer_sha = _sha256_file(helper_producer)
        if helper_sha != producer_sha:
            errors.append("Trust-owned proc-macro helper differs from its producer")
        if helper.get("sha256") != helper_sha or helper.get("producer_sha256") != producer_sha:
            errors.append("proc-macro helper hashes differ from the receipt")
        if helper.get("same_inode") != os.path.samefile(owned_helper, helper_producer):
            errors.append("proc-macro helper inode identity differs from the receipt")
        if helper.get("status") != "bound":
            errors.append("proc-macro helper binding status differs from the receipt")

    expected_status = _classify_receipt_status(current_lineage_status, recorded_bootstrap)
    if receipt.get("tool_binding_status") != "ready" or receipt.get("status") != expected_status:
        errors.append("receipt readiness classification disagrees with current binding/lineage")
    if receipt.get("errors") != []:
        errors.append("ready receipt contains errors")
    if require_immutable_lineage and (
        expected_status not in {"release-ready", "internal-release-ready"}
        or not expected_source_clean
        or not current_trust_from_trust
    ):
        errors.append(
            "immutable Trust-from-Trust lineage is required but this receipt is not an "
            "immutable internal/public release"
        )
    if require_public_release and expected_status != "release-ready":
        errors.append(
            "cryptographically admitted public release provenance is required but unavailable"
        )

    if errors:
        for error in sorted(set(errors)):
            print(f"  ERROR: {error}")
        print(f"  rejected existing stage provenance -> {receipt_path}")
        return False
    print(f"  verified existing stage provenance ({expected_status}) -> {receipt_path}")
    return True


def find_rustup() -> str | None:
    """Find rustup, including Homebrew's keg-only installation paths."""
    direct = which("rustup")
    if direct:
        return direct

    candidates: list[Path] = []
    brew = which("brew")
    if brew:
        try:
            prefix = subprocess.run(
                [brew, "--prefix", "rustup"],
                capture_output=True,
                text=True,
                check=False,
                timeout=10,
            )
            if prefix.returncode == 0 and prefix.stdout.strip():
                candidates.append(Path(prefix.stdout.strip()) / "bin" / "rustup")
        except (FileNotFoundError, subprocess.TimeoutExpired):
            pass
    candidates.extend(
        [
            Path("/opt/homebrew/opt/rustup/bin/rustup"),
            Path("/usr/local/opt/rustup/bin/rustup"),
        ]
    )
    for candidate in candidates:
        if candidate.is_file() and os.access(candidate, os.X_OK):
            return str(candidate)
    return None


def register_rustup_toolchain(root: Path, host: str, stage: int) -> bool:
    """Register the built sysroot as rustup's `trust` toolchain (batteries-on).

    `rustup toolchain link` re-points an existing name safely, so every
    successful build refreshes the link. The machine default is only claimed
    when rustup has none yet — an explicitly chosen default is never silently
    displaced (switch with `rustup default trust`).
    """
    sysroot = root / "build" / host / f"stage{stage}"
    rustup = find_rustup()
    if not rustup:
        print("\n  ERROR: rustup not found — register the toolchain later with:")
        print(f"    rustup toolchain link trust {sysroot}")
        return False
    print("\n  registering rustup toolchain:")
    link = subprocess.run(
        [rustup, "toolchain", "link", "trust", str(sysroot)],
        capture_output=True,
        text=True,
    )
    if link.returncode != 0:
        print(f"  ERROR: rustup toolchain link failed: {(link.stderr or link.stdout).strip()}")
        return False
    print(f"  rustup toolchain `trust` -> {sysroot}")
    current = subprocess.run([rustup, "default"], capture_output=True, text=True)
    default_name = (current.stdout or "").strip()
    if current.returncode != 0 or not default_name:
        set_default = subprocess.run(
            [rustup, "default", "trust"], capture_output=True, text=True
        )
        if set_default.returncode == 0:
            print("  rustup default -> trust")
        else:
            print(
                "  ERROR: rustup could not select the newly linked trust toolchain: "
                f"{(set_default.stderr or set_default.stdout).strip()}"
            )
            return False
    elif not default_name.startswith("trust"):
        print(f"  rustup default stays `{default_name}` — run `rustup default trust` to switch")
    return True


def maybe_register_rustup_toolchain(
    root: Path,
    host: str,
    stage: int,
    *,
    allow_non_stage2: bool = False,
) -> bool:
    """Register stage2 only, unless the caller explicitly opts into another stage."""
    if stage != 2 and not allow_non_stage2:
        print(
            f"\n  stage{stage} build: not re-pointing the global rustup `trust` toolchain "
            "(use --register-non-stage2 to opt in)."
        )
        return True
    return register_rustup_toolchain(root, host, stage)


def _selected_homebrew_library_path() -> tuple[Path | None, Path | None]:
    """Return the exact libgit2 keg/lib pair used by the build child."""
    brew = which("brew")
    prefix: Path | None = None
    if brew:
        try:
            prefix_value = subprocess.run(
                [brew, "--prefix", "libgit2"],
                text=True,
                capture_output=True,
                check=True,
                timeout=10,
            ).stdout.strip()
        except (OSError, subprocess.CalledProcessError, subprocess.TimeoutExpired):
            prefix_value = ""
        if prefix_value:
            prefix = Path(prefix_value)
    for candidate in filter(
        None,
        [
            prefix,
            Path("/opt/homebrew/opt/libgit2"),
            Path("/usr/local/opt/libgit2"),
        ],
    ):
        library = candidate / "lib"
        if library.is_dir():
            return candidate, library
    return None, None


def add_homebrew_library_path(env: dict[str, str]) -> None:
    """macOS: put the exact Homebrew libgit2 keg on LIBRARY_PATH.

    Targo's libgit2 binding needs this keg-only search path. Avoid exposing the
    broad mutable Homebrew lib directory to every native link.
    """
    if platform.system().lower() != "darwin":
        return
    _prefix, library = _selected_homebrew_library_path()
    if library is not None:
        existing = env.get("LIBRARY_PATH", "")
        if str(library) not in existing.split(":"):
            env["LIBRARY_PATH"] = (
                f"{library}:{existing}" if existing else str(library)
            )


def _advertises_z_option(help_text: str, name: str) -> bool:
    """Whether `-Z help` lists exactly this unstable option.

    Mirrors the matching bootstrap.py performs (`^\\s*-Z\\s+<name>(?:=|\\s|$)`)
    without taking a regex dependency: the name must be followed by `=`,
    whitespace, or end of line, so `trust-verify` does not match
    `trust-verify-survey` and `no-trust-verify` does not match `trust-verify`.
    """
    for line in help_text.splitlines():
        stripped = line.strip()
        if not stripped.startswith("-Z"):
            continue
        rest = stripped[2:].lstrip()
        if rest == name:
            return True
        if rest.startswith(name) and rest[len(name) : len(name) + 1] in ("=", " ", "\t"):
            return True
    return False


def seed_verification_off_switch(root: Path, host: str, env: dict) -> str | None:
    """Which verification off-switch the MATERIALIZED seed actually speaks.

    The checksum-pinned seed can predate the wave-2 flag-surface consolidation
    (576db732cd) that renamed the off-switch to `-Ztrust-verify=off`. Such a
    seed advertises only the retired `-Zno-trust-verify` and aborts the very
    first bootstrap Cargo invocation with `unknown unstable option:
    trust-verify` when handed the current spelling — which is exactly what a
    hardcoded flag did here, defeating the pre-rename bridge bootstrap.py
    already carries (2149dc74774). Probe the concrete driver instead of
    assuming a vintage.

    Returns "flag" for a post-rename seed, "env" for a pre-rename one, and
    None when the driver advertises neither spelling (a stock/genesis
    compiler has no Trust machinery to disable and must never receive the
    Trust-specific unstable flag).
    """
    trustc = root / "build" / host / "stage0" / "bin" / "trustc"
    if not trustc.is_file():
        return None
    try:
        result = subprocess.run(
            [str(trustc), "-Z", "help"],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            env=env,
            timeout=30,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired):
        return None
    if result.returncode != 0:
        return None
    help_text = result.stdout.decode("utf-8", "replace")
    if _advertises_z_option(help_text, "trust-verify"):
        return "flag"
    if _advertises_z_option(help_text, "no-trust-verify"):
        return "env"
    return None


def run_xpy_build(
    root: Path,
    host: str,
    stage: int,
    jobs: int | None,
    extra: list[str],
    *,
    seed_mode: bool,
) -> int:
    cmd = [sys.executable, str(root / "x.py"), "build", "--stage", str(stage), *extra]
    if jobs is not None:
        cmd += ["-j", str(jobs)]
    env = os.environ.copy()
    env.pop(REEXEC_GUARD_ENV, None)
    # Pre-build authority capture rejects these; scrub again at the process
    # boundary so a concurrent caller cannot smuggle compiler/linker overrides.
    for name in _ambient_build_authority_overrides(env):
        env.pop(name, None)
    # The Trust seed is batteries-on: without the exact bootstrap-only compiler
    # off-switch, its first Cargo invocation tries to strictly verify bootstrap's
    # third-party dependencies before the Rust bootstrap shims exist.  Besides
    # being unsupported, that contradicted the mode recorded in every stage
    # provenance receipt.  Install the recorded flag only after ambient authority
    # has been scrubbed and only for the checksum/admission-bound Trust seed.  A
    # stock/genesis compiler must never receive this Trust-specific unstable flag.
    if seed_mode:
        off_switch = seed_verification_off_switch(root, host, env)
        if off_switch == "flag":
            env["RUSTFLAGS_BOOTSTRAP"] = BOOTSTRAP_COMPILER_VERIFICATION["flag"]
        elif off_switch == "env":
            # A PRE-RENAME seed gets the version-invariant nested-process
            # transport instead of a flag it cannot parse. Every Trust vintage
            # translates TRUST_NO_VERIFY before option parsing, so the recorded
            # policy is identical — only the spelling differs. Setting the flag
            # here would abort the build before a single bootstrap crate
            # compiles; see bootstrap.py's apply_trust_bootstrap_compiler_policy,
            # which reaches the same conclusion from the same probe.
            env["TRUST_NO_VERIFY"] = "1"
    add_homebrew_library_path(env)
    print(f"\n$ {' '.join(cmd)}\n")
    return subprocess.run(cmd, env=env, cwd=str(root)).returncode


def normalized_xpy_extra(extra: list[str]) -> list[str]:
    """Normalize argparse.REMAINDER's optional separator."""
    out = list(extra)
    if out and out[0] == "--":
        out = out[1:]
    return out


def rustup_registration_required(
    stage: int,
    *,
    no_build: bool,
    no_register: bool,
    register_non_stage2: bool,
) -> bool:
    return (
        not no_build
        and not no_register
        and (stage == 2 or register_non_stage2)
    )


def parse_args(argv: list[str]) -> argparse.Namespace:
    p = argparse.ArgumentParser(
        prog="recreate-bootstrap",
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    p.add_argument(
        "--check",
        action="store_true",
        help="Only report prerequisites and detected state; do not write anything or build.",
    )
    p.add_argument(
        "--verify-stage-provenance",
        action="store_true",
        help="Read-only: recompute source/tool state and verify the existing stage receipt.",
    )
    p.add_argument(
        "--require-immutable-lineage",
        action="store_true",
        help="With --verify-stage-provenance, require immutable internal or public seed lineage.",
    )
    p.add_argument(
        "--require-public-release",
        action="store_true",
        help="With --verify-stage-provenance, require cryptographically admitted public release status.",
    )
    p.add_argument(
        "--stage",
        type=int,
        default=2,
        help="x.py build stage (default: 2).",
    )
    p.add_argument(
        "--register-non-stage2",
        action="store_true",
        help="Explicitly allow a non-stage2 build to re-point rustup's global `trust` toolchain.",
    )
    p.add_argument(
        "--no-register",
        action="store_true",
        help="Build and audit the sysroot without requiring rustup or registering a global "
        "toolchain name. The resulting stage directory remains directly runnable/installable.",
    )
    p.add_argument(
        "--host",
        default=None,
        help="Host triple override (default: auto-detected, e.g. aarch64-apple-darwin).",
    )
    p.add_argument(
        "--force",
        action="store_true",
        help="Recreate the build/<host>/stage0 genesis adapter even if present.",
    )
    p.add_argument(
        "--genesis",
        action="store_true",
        help="Force the stock-rust genesis adapter path even if the pinned Trust "
        "seed is available (dev convenience; not release evidence).",
    )
    p.add_argument(
        "--require-seed",
        action="store_true",
        help="Fail instead of falling back to the genesis adapter when the pinned "
        "Trust seed cannot be materialized/validated.",
    )
    p.add_argument(
        "--fresh-seed",
        action="store_true",
        help="For Stage2+ immutable provenance, safely quarantine an existing extracted "
        "build/<host>/stage0 before bootstrap-lineage capture so x.py must rehydrate it "
        "from the checksum-validated archives. The backup is removed only after the "
        "provenance receipt passes direct immutable-lineage verification.",
    )
    p.add_argument(
        "--no-fetch",
        action="store_true",
        help="Do not fetch missing seed payloads via gh; use only what is on disk.",
    )
    p.add_argument(
        "--force-config",
        action="store_true",
        help="Overwrite an existing bootstrap.toml/config.toml.",
    )
    p.add_argument(
        "--no-build",
        action="store_true",
        help="Set up genesis + config but do not invoke `./x.py build`.",
    )
    p.add_argument(
        "-j",
        "--jobs",
        type=int,
        default=None,
        help="Parallel build jobs to forward to `./x.py build`.",
    )
    p.add_argument(
        "--llvm-config",
        default=None,
        help="Path to an external `llvm-config` (e.g. /opt/homebrew/opt/llvm/bin/"
        "llvm-config). Links that LLVM instead of building it in-tree, so cmake/"
        "ninja are not required and ~26 min is saved. The major version must "
        "match what rustc_llvm expects.",
    )
    p.add_argument(
        "extra",
        nargs=argparse.REMAINDER,
        help="Extra args after `--` are forwarded to `./x.py build` for non-provenance "
        "stage0/stage1 builds only. Stage2+ rejects them because x.py overrides can "
        "replace the compiler/config authority outside the provenance receipt.",
    )
    return p.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ensure_python_311()
    line_buffer_output()
    args = parse_args(sys.argv[1:] if argv is None else argv)
    root = repo_root()
    host = args.host or host_triple()

    print(f"Trust bootstrap recreator")
    print(f"  repo:  {root}")
    print(f"  host:  {host}")

    if (
        args.require_immutable_lineage or args.require_public_release
    ) and not args.verify_stage_provenance:
        print("\nlineage/release requirements require --verify-stage-provenance.")
        return 2
    if args.fresh_seed and args.verify_stage_provenance:
        print(
            "\n--fresh-seed changes build inputs and conflicts with read-only "
            "provenance verification."
        )
        return 2
    if args.fresh_seed and (args.check or args.no_build or args.stage < 2):
        print("\n--fresh-seed requires a Stage2+ build; it cannot be combined with "
              "--check, --no-build, or --stage 0/1.")
        return 2
    if args.fresh_seed and args.genesis:
        print("\n--fresh-seed requires seed mode and conflicts with --genesis.")
        return 2
    if args.fresh_seed and not args.require_seed:
        print("\n--fresh-seed requires --require-seed so it can never fall back to genesis.")
        return 2
    if args.verify_stage_provenance:
        if args.stage < 2:
            print("\n--verify-stage-provenance requires --stage 2 or newer.")
            return 2
        return 0 if verify_stage_tool_provenance(
            root,
            host,
            args.stage,
            require_immutable_lineage=args.require_immutable_lineage,
            require_public_release=args.require_public_release,
        ) else 1

    if args.no_register and args.register_non_stage2:
        print("\n--no-register conflicts with --register-non-stage2.")
        return 2

    extra = normalized_xpy_extra(args.extra)
    if args.stage >= 2 and not args.no_build and extra:
        print(
            "\nStage2+ provenance builds refuse forwarded x.py arguments: "
            + " ".join(extra)
        )
        print(
            "Forwarded --set/config/compiler overrides are not bound by the stage receipt. "
            "Use the recreator's explicit options or run x.py directly without making a "
            "provenance claim."
        )
        return 2

    # Resolve the stage0 mode first: seed (trust-from-trust, preferred) or
    # genesis (stock-rust wrap, dev fallback). Seed resolution is cheap when
    # the payloads are already on disk, and prereqs depend on the mode (a
    # system rustc/cargo is only a hard requirement for genesis).
    seed_mode = False
    if not args.genesis:
        print("\nResolving pinned Trust stage0 seed (src/stage0):")
        seed_mode = resolve_seed(root, allow_fetch=not args.no_fetch and not args.check)
        if seed_mode:
            print("  seed OK — bootstrapping trust-from-trust (no stock rust)")
        elif args.require_seed:
            print("\n--require-seed: pinned Trust seed unavailable; refusing genesis fallback.")
            return 1
        else:
            print("  seed unavailable — falling back to the stock-rust genesis adapter")
            print("  (dev/first-build convenience only; NOT release evidence)")

    print()
    print("Prerequisites:")
    registration_required = rustup_registration_required(
        args.stage,
        no_build=args.no_build,
        no_register=args.no_register,
        register_non_stage2=args.register_non_stage2,
    )
    prereqs = check_prereqs(
        args.llvm_config,
        seed_mode=seed_mode,
        require_rustup=registration_required,
    )
    print_prereqs(prereqs)
    missing = [p for p in prereqs if p.required and not p.ok]
    if missing:
        print(f"\n{len(missing)} required prerequisite(s) missing. Install them and re-run.")
        return 1

    if args.check:
        print(f"\n--check: prerequisites OK (stage0 mode: {'seed' if seed_mode else 'genesis'}).")
        return 0

    print("\nEnsuring first-party submodules are materialized:")
    ensure_submodules(root)

    if not seed_mode:
        print("\nMaterializing local genesis stage0 adapter:")
        ensure_local_genesis_stage0(root, host, args.force)

    print("\nWriting bootstrap config:")
    write_config(root, host, args.force_config, args.llvm_config, seed_mode=seed_mode)

    if args.no_build:
        print("\n--no-build: setup complete. Run `./x.py build --stage 2` when ready.")
        return 0

    source_lineage_before: dict[str, object] | None = None
    bootstrap_lineage_before: dict[str, object] | None = None
    build_authority_before: dict[str, object] | None = None
    seed_stage0_quarantine: Path | None = None
    if args.stage >= 2:
        print("\nCapturing recursive pre-build source lineage:")
        source_lineage_before = capture_source_lineage(root)
        print(f"  status: {source_lineage_before['status']}")
        print(f"  closure: {source_lineage_before['closure_sha256']}")
        if source_lineage_before["status"] == "rejected":
            for error in source_lineage_before["errors"]:
                print(f"  ERROR: {error}")
            print("\nRefusing to build from ambiguous recursive source state.")
            return 1
        if args.fresh_seed:
            print("\nPreparing fresh seed materialization for immutable provenance:")
            try:
                seed_stage0_quarantine = quarantine_seed_stage0(root, host)
            except RuntimeError as error:
                print(f"  ERROR: {error}")
                return 1
        print("\nCapturing pre-build bootstrap lineage:")
        bootstrap_lineage_before = capture_bootstrap_lineage(root, host)
        print(f"  status: {bootstrap_lineage_before['status']}")
        print(f"  config: {bootstrap_lineage_before['config_sha256']}")
        expected_bootstrap_mode = "seed" if seed_mode else "genesis"
        if (
            bootstrap_lineage_before["status"] == "rejected"
            or bootstrap_lineage_before["mode"] != expected_bootstrap_mode
        ):
            for error in bootstrap_lineage_before["errors"]:
                print(f"  ERROR: {error}")
            print("\nRefusing to build with ambiguous or mismatched bootstrap lineage.")
            recover_seed_stage0_quarantine(root, host, seed_stage0_quarantine)
            return 1
        print("\nCapturing pre-build native tool and SDK authority:")
        build_authority_before = capture_build_authority(root, host, args.llvm_config)
        print(f"  status: {build_authority_before['status']}")
        print(f"  authority: {build_authority_before['authority_sha256']}")
        if build_authority_before["status"] == "rejected":
            for error in build_authority_before["errors"]:
                print(f"  ERROR: {error}")
            print("\nRefusing to build with ambiguous ambient native authority.")
            recover_seed_stage0_quarantine(root, host, seed_stage0_quarantine)
            return 1
    print("\nBuilding stage", args.stage, "(this is the long part)...")
    rc = run_xpy_build(root, host, args.stage, args.jobs, extra, seed_mode=seed_mode)
    if rc != 0:
        print(f"\n`./x.py build` failed (exit {rc}).")
        recover_seed_stage0_quarantine(root, host, seed_stage0_quarantine)
        return rc

    print()
    print("Build succeeded.")
    print(f"  stage{args.stage} sysroot: build/{host}/stage{args.stage}/bin/")

    # Batteries-on: installation is incomplete if the solver is absent. Do not
    # register a compiler that would silently downgrade every solver row to
    # Unknown while the one-command path reports success.
    if not install_ay_solver(root, host, args.stage):
        print("\nBuild succeeded, but required ay installation failed.")
        recover_seed_stage0_quarantine(root, host, seed_stage0_quarantine)
        return 1

    # A successful compilation is not a usable stage2 result until every
    # release-facing executable is byte-bound to the x.py artifact built by
    # the immediately preceding Trust compiler generation.  This catches
    # ambient post-build replacements and hardlink-cache contamination.
    if args.stage >= 2 and not audit_stage_tool_provenance(
        root,
        host,
        args.stage,
        source_lineage_before,
        bootstrap_lineage_before,
        build_authority_before,
        args.llvm_config,
    ):
        print("\nBuild succeeded, but stage tool provenance audit failed.")
        recover_seed_stage0_quarantine(root, host, seed_stage0_quarantine)
        return 1

    if args.fresh_seed and not verify_stage_tool_provenance(
        root,
        host,
        args.stage,
        require_immutable_lineage=True,
    ):
        print("\nFresh seed build completed, but immutable provenance verification failed.")
        recover_seed_stage0_quarantine(root, host, seed_stage0_quarantine)
        return 1

    try:
        discard_seed_stage0_quarantine(root, host, seed_stage0_quarantine)
    except RuntimeError as error:
        print(f"\nFresh seed receipt passed, but backup cleanup failed: {error}")
        return 1

    # Batteries-on for the release-facing stage2 sysroot. A stage1 convenience
    # build must not silently replace the machine-global `trust` toolchain.
    if args.no_register:
        print("\n  --no-register: leaving rustup/global toolchain state unchanged.")
    elif not maybe_register_rustup_toolchain(
        root,
        host,
        args.stage,
        allow_non_stage2=args.register_non_stage2,
    ):
        print("\nBuild succeeded, but required rustup registration failed.")
        return 1

    print("  next: re-seed bootstrap/trust-stage0 from this build by running")
    print("        python3 src/tools/trust-stage0-dist/prepare.py --help")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
