from __future__ import absolute_import, division, print_function
import argparse
import contextlib
import datetime
import hashlib
import importlib.util
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import sysconfig
import tarfile
import tempfile

from time import time
from multiprocessing import Pool, cpu_count

# Trust: by-file imports and isolated Python cannot rely on sys.path containing
# this directory. Load the pure extraction-identity owner beside this script.
_identity_spec = importlib.util.spec_from_file_location(
    "trust_stage0_identity", os.path.join(os.path.dirname(__file__), "stage0_identity.py")
)
_identity_owner = importlib.util.module_from_spec(_identity_spec)
_identity_spec.loader.exec_module(_identity_owner)
stage0_extraction_stamp = _identity_owner.extraction_stamp

try:
    from urllib.parse import urlparse
    from urllib.request import url2pathname
except ImportError:
    from urlparse import urlparse
    from urllib import url2pathname

try:
    import lzma
except ImportError:
    lzma = None


def platform_is_win32():
    return sys.platform == "win32"


# Trust: capability queries borrow the same native transport/custody owner as
# the seed checker. No caller-selected executor or fabricated admission exists.
def bootstrap_serial_owner():
    library = os.path.join(os.path.dirname(__file__), "..", "..", "scripts", "lib")
    if library not in sys.path:
        sys.path.insert(0, library)
    import native_serial
    return native_serial


def bootstrap_capability_routes_through_serial_owner(env, serial):
    """Whether a capability query borrows the managed serial owner.

    Trust (BOOTSTRAP-SEED-PROBE-ADMISSION-1): `trust-serial-command` lends an
    ALREADY-ADMITTED caller's one implicit execution and refuses every other
    caller ("command requires an already-admitted caller", exit 75): it grants
    no CPU or memory itself. Only a caller inside build-slot admission
    (`BUILD_SLOT_HELD=1`, the exact marker the borrower checks) has an
    execution to lend. Outside admission nothing in bootstrap borrows one:
    this script runs its own Stage0 `targo build` of bootstrap directly, and
    the Rust driver lends its own implicit execution to its compiler queries
    (`metadata_scheduler`). So the query runs directly too, through the same
    custody wait and with every advertised descriptor kept. The route is
    chosen from the caller's admission before the query runs; it is never a
    second attempt after a refused one. Routing an unadmitted caller through
    the borrower made every plain `x.py` read that refusal as "could not
    probe" and take the fallback policy.
    """
    return serial and sys.platform in ("linux", "darwin") and env.get("BUILD_SLOT_HELD") == "1"


def bootstrap_capability_command(command, env, timeout, serial=False):
    native_serial = bootstrap_serial_owner()
    # Trust: the managed native transport exists only on Linux/macOS. Other
    # supported bootstrap hosts retain their direct read-only query, never a
    # fallback after managed admission failed. Windows cannot inherit POSIX FDs.
    if platform_is_win32():
        if native_serial.landing_targo.resource_fds(env):
            raise RuntimeError("Windows capability query cannot inherit native POSIX custody")
        result = subprocess.run(command, env=env, timeout=timeout, capture_output=True, text=True)
    else:
        if bootstrap_capability_routes_through_serial_owner(env, serial):
            command = [str(native_serial.managed_serial_executor(env)), "--", *command]
        result = native_serial.run_custodied_command(command, env=env, timeout=timeout)
    return subprocess.CompletedProcess(result.args, result.returncode,
                                       (result.stdout or "") + (result.stderr or ""))


if platform_is_win32():
    EXE_SUFFIX = ".exe"
else:
    EXE_SUFFIX = ""

STAGE0_PROGRAM_NAMES = {
    "rustc": "trustc",
    # Bootstrap is a compatibility build, not a proof workflow. The `cargo`
    # and `targo` names are the same payload, but branded Targo intentionally
    # requires authenticated verification or a visible --unverified opt-in.
    "cargo": "cargo",
    "rustdoc": "trustdoc",
    "rustfmt": "trustfmt",
}

STAGE0_REQUIRED_BINS = (
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
STAGE0_REQUIRED_LIBEXEC_BINS = (
    "trust-analyzer-proc-macro-srv",
)
# (fetch-filename component, unpack image-dir). The stage0 seed is materialized by
# trust-stage0-dist/prepare.py, which renames the produced `-preview` image dirs to
# their bare canonical names; unpack() matches on that dir, so the match must be bare
# (a `-preview` match skips every member -> empty bin/). The CI-download path in
# download.rs keeps `-preview` because it consumes raw x.py-produced tarballs.
STAGE0_EXTRA_COMPONENTS = _identity_owner.STAGE0_EXTRA_COMPONENTS
STAGE0_LEGACY_EXTRA_COMPONENTS = _identity_owner.STAGE0_LEGACY_EXTRA_COMPONENTS
STAGE0_LEGACY_TARGO_COMPONENTS = _identity_owner.STAGE0_LEGACY_TARGO_COMPONENTS
STAGE0_LEGACY_TARGO_BACKEND_DIR = "libexec"
STAGE0_LEGACY_TIPPY_FRONTENDS = ("trust-clippy", "cargo-clippy", "targo-clippy")
STAGE0_LEGACY_TIPPY_DRIVERS = ("trust-clippy-driver", "clippy-driver")
STAGE0_TIPPY_BACKEND = "tippy-stage0-backend"
STAGE0_TIPPY_DRIVER_BACKEND = "tippy-driver-stage0-backend"
STAGE0_FORBIDDEN_BINS = (
    "cargo-trust",
    "tcargo",
    "tcargo-trust",
    "tcargo-fmt",
    # Forbidden in a stage0 SEED only. The seed translates the stock rustdoc to
    # `trustdoc` (STAGE0_PROGRAM_NAMES above), so the inherited leaf must never
    # survive into a seed tree -- assert_stage0_tool_surface and
    # stage0_tool_surface_needs_refresh below apply this list to the seed and to
    # nothing else. A COMPLETE stage1/stage2/installed root is the opposite
    # case: it deliberately ships `rustdoc` as a same-surface alias of
    # `trustdoc` (76d408e1cd -- cargo spawns a binary named `rustdoc` for its
    # doctest phase and rustup's proxy refuses a linked toolchain without it).
    # scripts/check_toolchain_coherence.py derives the complete-root inventory
    # by subtracting that carve-out from this authority, the same way it
    # subtracts the optional Miri tools, so this entry must stay here.
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
    # Trust: forbid the miri targo-subcommand under its Trust spelling (was the
    # inherited cargo-miri); miri is not part of the default stage0 surface.
    "targo-miri",
    "rust-gdb",
    "rust-gdbgui",
    "rust-lldb",
    "rust-windbg.cmd",
)
STAGE0_FORBIDDEN_LIBEXEC_BINS = ("rust-analyzer-proc-macro-srv",)


def inherited_upstream_rust_download_host(url):
    parsed = urlparse(url)
    if parsed.scheme not in ("http", "https"):
        return None
    host = parsed.hostname
    if host is None:
        return None
    host = host.lower().rstrip(".")
    if host == "rust-lang.org" or host.endswith(".rust-lang.org"):
        return host
    return None


def reject_inherited_upstream_rust_download_url(url, context):
    host = inherited_upstream_rust_download_host(url)
    if host is not None:
        raise RuntimeError(
            "{} uses inherited upstream Rust download host {}: {}".format(
                context, host, url
            )
        )


def get_cpus():
    if hasattr(os, "sched_getaffinity"):
        return len(os.sched_getaffinity(0))
    if hasattr(os, "cpu_count"):
        cpus = os.cpu_count()
        if cpus is not None:
            return cpus
    try:
        return cpu_count()
    except NotImplementedError:
        return 1


def bootstrap_jobs(configured_jobs, cli_jobs, env):
    """Trust: keep the pre-driver Cargo build within an admitted CPU share.

    Outside build-slot preserve the existing TOML/default Cargo argument. The
    Rust driver owns CLI precedence; inside admission also respect a smaller
    explicit CLI request while capping both phases by the same positive share.
    """
    if env.get("BUILD_SLOT_HELD") != "1":
        return configured_jobs
    share = env.get("CARGO_BUILD_JOBS", "")
    if not re.fullmatch(r"[0-9]+", share) or not 0 < int(share) <= 0xFFFFFFFF:
        raise RuntimeError(
            "BUILD_SLOT_HELD=1 requires a positive u32 CARGO_BUILD_JOBS share"
        )
    requested = str(cli_jobs) if cli_jobs is not None else configured_jobs
    if requested in ("default", "0"):
        jobs = get_cpus()
    elif re.fullmatch(r"[0-9]+", requested) and int(requested) <= 0xFFFFFFFF:
        jobs = int(requested)
    else:
        raise RuntimeError("invalid bootstrap jobs within build-slot admission")
    return str(min(jobs, int(share)))


def eprint(*args, **kwargs):
    kwargs["file"] = sys.stderr
    print(*args, **kwargs)


def trust_repo_root():
    return os.path.abspath(os.path.join(__file__, "../../.."))


def trust_seed_ledger_release(repo_root=None):
    """Parse (repo, tag) out of the seed ledger's [release] block.

    Trust: bootstrap/trust-stage0/seed-ledger.toml is the checked-in
    declaration of where the admitted-internal seed payloads live (the same
    source scripts/fetch_trust_stage0_payloads.py consumes). Minimal
    line-based parsing keeps this runnable on every python bootstrap
    supports (no tomllib dependency).
    """
    ledger = os.path.join(
        repo_root or trust_repo_root(), "bootstrap", "trust-stage0", "seed-ledger.toml"
    )
    if not os.path.isfile(ledger):
        return None
    section = ""
    values = {}
    with open(ledger, encoding="utf-8") as handle:
        for line in handle:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            if line.startswith("[") and line.endswith("]"):
                section = line[1:-1].strip()
                continue
            key, sep, value = line.partition("=")
            if sep:
                values[(section, key.strip())] = value.strip().strip('"')
    repo = values.get(("release", "repo"))
    tag = values.get(("release", "tag"))
    if not repo or not tag:
        return None
    return repo, tag


def try_materialize_trust_seed_payload(
    resolved_payload, sha256, verbose=0, agh=None, repo_root=None
):
    """Fetch one missing checksum-pinned seed payload from the declared release.

    Trust: a fresh checkout tracks only the src/stage0 digest pins; the
    archive payloads live in the private GitHub release the seed ledger
    declares. Riding the caller's authenticated `agh` keeps the transport out
    of the trust story: the download lands in a temp staging dir, is verified
    against the src/stage0 SHA-256 pin THERE, and only verified bytes are
    os.replace()d into the pinned path — so neither an interrupted transfer
    nor a wrong-digest asset ever occupies the digest-pinned dist root (a
    mismatching file there would wedge every later run, since get() only
    materializes missing files). get() re-verifies after this returns, as for
    every other payload lane.

    Returns True when the payload now exists on disk. Never raises: the
    caller owns the (remedy-bearing) missing-payload error.
    """
    root = repo_root or trust_repo_root()
    seed_root = os.path.join(root, "bootstrap", "trust-stage0")
    resolved = os.path.abspath(resolved_payload)
    # Only self-materialize into the repo-local seed dist root. Anything else
    # (tests, custom dist servers) keeps the strict missing-payload behavior.
    if not resolved.startswith(seed_root + os.sep):
        return False
    release = trust_seed_ledger_release(root)
    if release is None:
        return False
    repo, tag = release
    filename = os.path.basename(resolved)
    agh = agh or shutil.which("agh")
    if agh is None:
        eprint(
            "note: the seed ledger declares release {} on {}, but the `agh` CLI is "
            "not installed; cannot fetch the pinned stage0 seed payload".format(
                tag, repo
            )
        )
        return False
    dest_dir = os.path.dirname(resolved)
    if not os.path.isdir(dest_dir):
        os.makedirs(dest_dir)
    eprint(
        "fetching pinned Trust stage0 seed payload {} from release {} ({})".format(
            filename, tag, repo
        )
    )
    staging = tempfile.mkdtemp(prefix=".seed-fetch-", dir=dest_dir)
    try:
        try:
            result = subprocess.run(
                [
                    agh,
                    "release",
                    "download",
                    repo,
                    tag,
                    "--asset",
                    filename,
                    "--dir",
                    staging,
                ],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                universal_newlines=True,
                timeout=600,
            )
        except subprocess.TimeoutExpired:
            eprint("note: agh release download {} timed out".format(tag))
            return False
        if result.returncode != 0:
            eprint(
                "note: agh release download {} failed: {}".format(
                    tag, (result.stderr or result.stdout or "").strip()
                )
            )
            return False
        fetched = os.path.join(staging, filename)
        if not os.path.isfile(fetched):
            return False
        if not verify(fetched, sha256, verbose > 0):
            eprint(
                "note: release {} asset {} does not match the src/stage0 pin "
                "{}; refusing to install it into the digest-pinned dist root".format(
                    tag, filename, sha256
                )
            )
            return False
        os.replace(fetched, resolved)
        return True
    finally:
        shutil.rmtree(staging, ignore_errors=True)


def get(base, url, path, checksums, verbose=0):
    payload_url = "{}/{}".format(base.rstrip("/"), url)
    reject_inherited_upstream_rust_download_url(payload_url, "bootstrap download")
    with tempfile.NamedTemporaryFile(delete=False) as temp_file:
        temp_path = temp_file.name

    try:
        if url not in checksums:
            raise RuntimeError(
                "src/stage0 does not contain a checksum for Trust stage0 payload:\n"
                "  dist_server={}\n"
                "  payload={}".format(base, url)
            )
        sha256 = checksums[url]
        if os.path.exists(path):
            if verify(path, sha256, False):
                if verbose > 0:
                    eprint("using already-download file", path)
                return
            else:
                if verbose > 0:
                    eprint(
                        "ignoring already-download file",
                        path,
                        "due to failed verification",
                    )
                os.unlink(path)
        if payload_url.startswith("file://"):
            resolved_payload = file_url_to_path(payload_url)
            if not os.path.isfile(resolved_payload):
                # Trust: self-materialize the pinned seed from the
                # ledger-declared release before failing (only pin-verified
                # bytes are placed; the sha256 gate below re-checks anyway).
                try_materialize_trust_seed_payload(resolved_payload, sha256, verbose)
            if not os.path.isfile(resolved_payload):
                raise RuntimeError(
                    "missing checksum-pinned Trust stage0 payload:\n"
                    "  dist_server={}\n"
                    "  payload={}\n"
                    "  resolved_payload={}\n"
                    "  expected_sha256={}\n"
                    "repair (fetches the admitted-internal seed via agh and"
                    " verifies every byte against src/stage0):\n"
                    "  python3 scripts/fetch_trust_stage0_payloads.py --fetch".format(
                        base, url, resolved_payload, sha256
                    )
                )
        download(temp_path, payload_url, True, verbose)
        if not verify(temp_path, sha256, verbose):
            raise RuntimeError("failed verification")
        if verbose > 0:
            eprint("moving {} to {}".format(temp_path, path))
        shutil.move(temp_path, path)
    finally:
        if os.path.isfile(temp_path):
            if verbose > 0:
                eprint("removing", temp_path)
            os.unlink(temp_path)


def curl_version():
    m = re.match(bytes("^curl ([0-9]+)\\.([0-9]+)", "utf8"), require(["curl", "-V"]))
    if m is None:
        return (0, 0)
    return (int(m[1]), int(m[2]))


def download(path, url, probably_big, verbose):
    reject_inherited_upstream_rust_download_url(url, "bootstrap download")
    for _ in range(4):
        try:
            _download(path, url, probably_big, verbose, True)
            return
        except RuntimeError:
            eprint("\nspurious failure, trying again")
    _download(path, url, probably_big, verbose, False)


def file_url_to_path(url):
    parsed = urlparse(url)
    if parsed.scheme != "file":
        raise RuntimeError("not a file URL: {}".format(url))
    if parsed.netloc == "{trust-root}":
        # Trust: strip leading slashes AND backslashes. On Windows url2pathname
        # returns a "\"-rooted path (e.g. "\bootstrap\..."); lstrip("/") alone
        # leaves that leading backslash, which makes the os.path.join() below
        # treat it as drive-absolute and silently drop the repo root (resolving
        # to C:\bootstrap\... instead of <repo-root>\bootstrap\...).
        repo_relative_path = url2pathname(parsed.path).lstrip("/\\")
        return os.path.join(
            os.path.abspath(os.path.join(__file__, "../../..")),
            repo_relative_path,
        )
    if parsed.netloc not in ("", "localhost"):
        raise RuntimeError("unsupported file URL host: {}".format(parsed.netloc))
    return url2pathname(parsed.path)


def _download(path, url, probably_big, verbose, exception):
    # Try to use curl (potentially available on win32
    #    https://devblogs.microsoft.com/commandline/tar-and-curl-come-to-windows/)
    # If an error occurs:
    #  - If we are on win32 fallback to powershell
    #  - Otherwise raise the error if appropriate
    if probably_big or verbose > 0:
        eprint("downloading {}".format(url))

    if url.startswith("file://"):
        shutil.copyfile(file_url_to_path(url), path)
        return

    try:
        if (probably_big or verbose > 0) and "GITHUB_ACTIONS" not in os.environ:
            option = "--progress-bar"
        else:
            option = "--silent"
        # If curl is not present on Win32, we should not sys.exit
        #   but raise `CalledProcessError` or `OSError` instead
        require(["curl", "--version"], exception=platform_is_win32())
        extra_flags = []
        if curl_version() > (7, 70):
            extra_flags = ["--retry-all-errors"]
        # options should be kept in sync with
        # src/bootstrap/src/core/download.rs
        # for consistency.
        # they are also more compreprensivly explained in that file.
        run(
            ["curl", option]
            + extra_flags
            + [
                # Follow redirect.
                "--location",
                # timeout if speed is < 10 bytes/sec for > 30 seconds
                "--speed-time",
                "30",
                "--speed-limit",
                "10",
                # timeout if cannot connect within 30 seconds
                "--connect-timeout",
                "30",
                "--output",
                path,
                "--continue-at",
                "-",
                "--retry",
                "3",
                "--show-error",
                "--remote-time",
                "--fail",
                url,
            ],
            verbose=verbose,
            exception=True,  # Will raise RuntimeError on failure
        )
    except (subprocess.CalledProcessError, OSError, RuntimeError):
        # see http://serverfault.com/questions/301128/how-to-download
        script = "[Net.ServicePointManager]::SecurityProtocol = [Net.SecurityProtocolType]::Tls12;"
        if platform_is_win32():
            run_powershell(
                [
                    script,
                    "(New-Object System.Net.WebClient).DownloadFile('{}', '{}')".format(
                        url, path
                    ),
                ],
                verbose=verbose,
                exception=exception,
            )
        # Check if the RuntimeError raised by run(curl) should be silenced
        elif verbose or exception:
            raise


def verify(path, expected, verbose):
    """Check if the sha256 sum of the given path is valid"""
    if verbose > 0:
        eprint("verifying", path)
    with open(path, "rb") as source:
        found = hashlib.sha256(source.read()).hexdigest()
    verified = found == expected
    if not verified:
        eprint(
            "invalid checksum:\n" "    found:    {}\n" "    expected: {}".format(
                found, expected
            )
        )
    return verified


def unpack(tarball, tarball_suffix, dst, verbose=0, match=None):
    """Unpack the given tarball file"""
    eprint("extracting", tarball)
    fname = os.path.basename(tarball).replace(tarball_suffix, "")
    with contextlib.closing(tarfile.open(tarball)) as tar:
        for member in tar.getnames():
            # Trust: share the exact segment projection with the retained
            # descriptor preparation route; a prefix is not a component.
            name = _identity_owner.component_projection(member, fname, match)
            if not name:
                continue

            dst_path = os.path.join(dst, name)
            if verbose > 0:
                eprint("  extracting", member)
            tar.extract(member, dst)
            src_path = os.path.join(dst, member)
            if os.path.isdir(src_path) and os.path.exists(dst_path):
                continue
            os.makedirs(os.path.dirname(dst_path), exist_ok=True)
            shutil.move(src_path, dst_path)
    try:
        shutil.rmtree(os.path.join(dst, fname))
    except FileNotFoundError:
        pass


def run(args, verbose=0, exception=False, is_bootstrap=False, **kwargs):
    """Run a child program in a new process"""
    if verbose > 0:
        eprint("running: " + " ".join(args))
    sys.stdout.flush()
    # Ensure that the .exe is used on Windows just in case a Linux ELF has been
    # compiled in the same directory.
    if os.name == "nt" and not args[0].endswith(".exe"):
        args[0] += ".exe"
    # Use Popen here instead of call() as it apparently allows powershell on
    # Windows to not lock up waiting for input presumably.
    ret = subprocess.Popen(args, **kwargs)
    code = ret.wait()
    if code != 0:
        err = "failed to run: " + " ".join(args)
        if verbose > 0 or exception:
            raise RuntimeError(err)
        # For most failures, we definitely do want to print this error, or the user will have no
        # idea what went wrong. But when we've successfully built bootstrap and it failed, it will
        # have already printed an error above, so there's no need to print the exact command we're
        # running.
        if is_bootstrap:
            sys.exit(1)
        else:
            sys.exit(err)


def run_powershell(script, *args, **kwargs):
    """Run a powershell script"""
    run(["PowerShell.exe", "/nologo", "-Command"] + script, *args, **kwargs)


def require(cmd, exit=True, exception=False):
    """Run a command, returning its output.
    On error,
        If `exception` is `True`, raise the error
        Otherwise If `exit` is `True`, exit the process
        Else return None."""
    try:
        return subprocess.check_output(cmd).strip()
    except (subprocess.CalledProcessError, OSError) as exc:
        if exception:
            raise
        elif exit:
            eprint("ERROR: unable to run `{}`: {}".format(" ".join(cmd), exc))
            eprint("Please make sure it's installed and in the path.")
            sys.exit(1)
        return None


def format_build_time(duration):
    """Return a nicer format for build time

    >>> format_build_time('300')
    '0:05:00'
    """
    return str(datetime.timedelta(seconds=int(duration)))


def default_build_triple(verbose):
    """Build triple as in LLVM"""
    # If we're on Windows and have an existing `rustc` toolchain, use `rustc --version --verbose`
    # to find our host target triple. This fixes an issue with Windows builds being detected
    # as GNU instead of MSVC.
    # Otherwise, detect it via `uname`
    default_encoding = sys.getdefaultencoding()

    if platform_is_win32():
        try:
            version = subprocess.check_output(
                ["rustc", "--version", "--verbose"], stderr=subprocess.DEVNULL
            )
            version = version.decode(default_encoding)
            host = next(x for x in version.split("\n") if x.startswith("host: "))
            triple = host.split("host: ")[1]
            if verbose > 0:
                eprint(
                    "detected default triple {} from pre-installed rustc".format(triple)
                )
            return triple
        except Exception as e:
            if verbose > 0:
                eprint("pre-installed rustc not detected: {}".format(e))
                eprint("falling back to auto-detect")

    required = not platform_is_win32()
    uname = require(["uname", "-smp"], exit=required)

    # If we do not have `uname`, assume Windows.
    if uname is None:
        return "x86_64-pc-windows-msvc"

    kernel, cputype, processor = uname.decode(default_encoding).split(maxsplit=2)

    # ON NetBSD, use `uname -p` to set the CPU type
    if kernel == "NetBSD":
        cputype = (
            subprocess.check_output(["uname", "-p"]).strip().decode(default_encoding)
        )

    # The goal here is to come up with the same triple as LLVM would,
    # at least for the subset of platforms we're willing to target.
    kerneltype_mapper = {
        "Darwin": "apple-darwin",
        "DragonFly": "unknown-dragonfly",
        "FreeBSD": "unknown-freebsd",
        "Haiku": "unknown-haiku",
        "NetBSD": "unknown-netbsd",
        "OpenBSD": "unknown-openbsd",
        "GNU": "unknown-hurd",
    }

    # Consider the direct transformation first and then the special cases
    if kernel in kerneltype_mapper:
        kernel = kerneltype_mapper[kernel]
    elif kernel == "Linux":
        # Apple doesn't support `-o` so this can't be used in the combined
        # uname invocation above
        ostype = require(["uname", "-o"], exit=required).decode(default_encoding)
        if ostype == "Android":
            kernel = "linux-android"
        else:
            python_soabi = sysconfig.get_config_var("SOABI")
            if python_soabi is not None and "musl" in python_soabi:
                kernel = "unknown-linux-musl"
            else:
                kernel = "unknown-linux-gnu"
    elif kernel == "SunOS":
        kernel = "pc-solaris"
        # On Solaris, uname -m will return a machine classification instead
        # of a cpu type, so uname -p is recommended instead.  However, the
        # output from that option is too generic for our purposes (it will
        # always emit 'i386' on x86/amd64 systems).  As such, isainfo -k
        # must be used instead.
        cputype = require(["isainfo", "-k"]).decode(default_encoding)
        # sparc cpus have sun as a target vendor
        if "sparc" in cputype:
            kernel = "sun-solaris"
    elif kernel.startswith("MINGW"):
        # msys' `uname` does not print gcc configuration, but prints msys
        # configuration. so we cannot believe `uname -m`:
        # msys1 is always i686 and msys2 is always x86_64.
        # instead, msys defines $MSYSTEM which is MINGW32 on i686 and
        # MINGW64 on x86_64.
        kernel = "pc-windows-gnu"
        cputype = "i686"
        if os.environ.get("MSYSTEM") == "MINGW64":
            cputype = "x86_64"
    elif kernel.startswith("MSYS"):
        kernel = "pc-windows-gnu"
    elif kernel.startswith("CYGWIN_NT"):
        cputype = "i686"
        if kernel.endswith("WOW64"):
            cputype = "x86_64"
        kernel = "pc-windows-gnu"
    elif platform_is_win32():
        # Some Windows platforms might have a `uname` command that returns a
        # non-standard string (e.g. gnuwin32 tools returns `windows32`). In
        # these cases, fall back to using sys.platform.
        return "x86_64-pc-windows-msvc"
    elif kernel == "AIX":
        # `uname -m` returns the machine ID rather than machine hardware on AIX,
        # so we are unable to use cputype to form triple. AIX 7.2 and
        # above supports 32-bit and 64-bit mode simultaneously and `uname -p`
        # returns `powerpc`, however we only supports `powerpc64-ibm-aix` in
        # rust on AIX. For above reasons, kerneltype_mapper and cputype_mapper
        # are not used to infer AIX's triple.
        return "powerpc64-ibm-aix"
    else:
        err = "unknown OS type: {}".format(kernel)
        sys.exit(err)

    if cputype in ["powerpc", "riscv"] and kernel == "unknown-freebsd":
        cputype = (
            subprocess.check_output(["uname", "-p"]).strip().decode(default_encoding)
        )
    cputype_mapper = {
        "BePC": "i686",
        "aarch64": "aarch64",
        "aarch64eb": "aarch64",
        "amd64": "x86_64",
        "arm64": "aarch64",
        "i386": "i686",
        "i486": "i686",
        "i686": "i686",
        "i686-AT386": "i686",
        "i786": "i686",
        "loongarch32": "loongarch32",
        "loongarch64": "loongarch64",
        "m68k": "m68k",
        "csky": "csky",
        "powerpc": "powerpc",
        "powerpc64": "powerpc64",
        "powerpc64le": "powerpc64le",
        "ppc": "powerpc",
        "ppc64": "powerpc64",
        "ppc64le": "powerpc64le",
        "riscv64": "riscv64gc",
        "s390x": "s390x",
        "x64": "x86_64",
        "x86": "i686",
        "x86-64": "x86_64",
        "x86_64": "x86_64",
    }

    # Consider the direct transformation first and then the special cases
    if cputype in cputype_mapper:
        cputype = cputype_mapper[cputype]
    elif cputype in {"xscale", "arm"}:
        cputype = "arm"
        if kernel == "linux-android":
            kernel = "linux-androideabi"
        elif kernel == "unknown-freebsd":
            cputype = processor
            kernel = "unknown-freebsd"
    elif cputype == "armv6l":
        cputype = "arm"
        if kernel == "linux-android":
            kernel = "linux-androideabi"
        else:
            kernel += "eabihf"
    elif cputype in {"armv6hf", "earmv6hf"}:
        cputype = "armv6"
        if kernel == "unknown-netbsd":
            kernel += "-eabihf"
    elif cputype in {"armv7l", "earmv7hf", "armv8l"}:
        cputype = "armv7"
        if kernel == "linux-android":
            kernel = "linux-androideabi"
        elif kernel == "unknown-netbsd":
            kernel += "-eabihf"
        else:
            kernel += "eabihf"
    elif cputype == "mips":
        if sys.byteorder == "big":
            cputype = "mips"
        elif sys.byteorder == "little":
            cputype = "mipsel"
        else:
            raise ValueError("unknown byteorder: {}".format(sys.byteorder))
    elif cputype == "mips64":
        if sys.byteorder == "big":
            cputype = "mips64"
        elif sys.byteorder == "little":
            cputype = "mips64el"
        else:
            raise ValueError("unknown byteorder: {}".format(sys.byteorder))
        # only the n64 ABI is supported, indicate it
        kernel += "abi64"
    elif cputype == "sparc" or cputype == "sparcv9" or cputype == "sparc64":
        pass
    else:
        err = "unknown cpu type: {}".format(cputype)
        sys.exit(err)

    return "{}-{}".format(cputype, kernel)


@contextlib.contextmanager
def output(filepath):
    tmp = filepath + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        yield f
    try:
        if os.path.exists(filepath):
            os.remove(filepath)  # PermissionError/OSError on Win32 if in use
    except OSError:
        shutil.copy2(tmp, filepath)
        os.remove(tmp)
        return
    os.rename(tmp, filepath)


class Stage0Toolchain:
    def __init__(self, date, version):
        self.date = date
        self.version = version

    def channel(self):
        return self.version + "-" + self.date


class DownloadInfo:
    """A helper class that can be pickled into a parallel subprocess"""

    def __init__(
        self,
        base_download_url,
        download_path,
        bin_root,
        tarball_path,
        tarball_suffix,
        stage0_data,
        pattern,
        verbose,
    ):
        self.base_download_url = base_download_url
        self.download_path = download_path
        self.bin_root = bin_root
        self.tarball_path = tarball_path
        self.tarball_suffix = tarball_suffix
        self.stage0_data = stage0_data
        self.pattern = pattern
        self.verbose = verbose


def download_component(download_info):
    # Trust: get verifies cached bytes too. A same-day re-pin can keep the same
    # URL/filename while changing its admitted checksum; existence is no authority.
    get(
        download_info.base_download_url,
        download_info.download_path,
        download_info.tarball_path,
        download_info.stage0_data,
        verbose=download_info.verbose,
    )


def unpack_component(download_info):
    unpack(
        download_info.tarball_path,
        download_info.tarball_suffix,
        download_info.bin_root,
        match=download_info.pattern,
        verbose=download_info.verbose,
    )


select_stage0_extra_component = _identity_owner.select_stage0_extra_component
select_stage0_targo_component = _identity_owner.select_stage0_targo_component


def translate_legacy_targo_stage0_surface(bin_root, legacy_components):
    """Adapt admitted tcargo payloads to the canonical public Targo surface."""
    legacy_components = set(legacy_components)
    if not legacy_components:
        return
    if not legacy_components.issubset(STAGE0_LEGACY_TARGO_COMPONENTS):
        raise RuntimeError("unknown legacy Targo component selection")
    if platform_is_win32():
        raise RuntimeError(
            "legacy Trust stage0 tcargo pins require a native canonical regeneration on Windows"
        )

    bin_dir = os.path.join(bin_root, "bin")
    # Keep the old executable one level below the sysroot. Its published rpath
    # was built for bin/<tool> -> ../lib; libexec/<tool> has the same depth and
    # therefore preserves dynamic-library discovery.
    backend_dir = os.path.join(bin_root, STAGE0_LEGACY_TARGO_BACKEND_DIR)
    os.makedirs(backend_dir, exist_ok=True)

    def copy_executable(source, destination):
        if not os.path.exists(source):
            raise RuntimeError(
                "legacy Trust stage0 Targo payload lacks {}".format(source)
            )
        shutil.copy2(source, destination)
        os.chmod(destination, os.stat(destination).st_mode | 0o111)

    def write_executable(destination, contents):
        with open(destination, "w", encoding="utf-8", newline="\n") as adapter:
            adapter.write(contents)
        os.chmod(destination, 0o755)

    if "targo" in legacy_components:
        legacy_targo = os.path.join(bin_dir, "tcargo" + EXE_SUFFIX)
        if not os.path.exists(os.path.join(bin_dir, "cargo" + EXE_SUFFIX)):
            raise RuntimeError("legacy Trust stage0 tcargo payload lacks bin/cargo")
        copy_executable(legacy_targo, os.path.join(backend_dir, "tcargo"))
        write_executable(
            os.path.join(bin_dir, "targo"),
            """#!/bin/sh
backend="$(dirname "$0")/../{backend_dir}/tcargo"
rewrite_version() {{
    output=$("$backend" "$@")
    status=$?
    printf '%s\n' "$output" | sed -e '1s/^tcargo /targo /' -e 's/^binary: tcargo$/binary: targo/'
    return "$status"
}}
if [ "$#" -eq 1 ]; then
    case "$1" in --version|-V|-vV) rewrite_version "$@"; exit $? ;; esac
fi
if [ "$#" -eq 2 ] &&
    {{ [ "$1" = "--version" ] && [ "$2" = "--verbose" ] ||
        [ "$1" = "--verbose" ] && [ "$2" = "--version" ]; }}; then
    rewrite_version "$@"
    exit $?
fi
if [ "${{TRUST_BOOTSTRAP_NO_VERIFY+x}}" = x ] ||
    [ "${{TRUST_BOOTSTRAP_NO_VERIFY_TARGET_ONLY+x}}" = x ]; then
    echo "error: legacy TRUST_BOOTSTRAP_NO_VERIFY markers do not authorize branded Targo" >&2
    exit 101
fi
is_native_command() {{
    case "${{1-}}" in
        build|b|check|c|fix|clippy|test|t|run|r|bench|doc|rustc|rustdoc|install|package|publish)
            return 0
            ;;
        *)
            return 1
            ;;
    esac
}}
run_explicit_unverified() {{
    note="warning: UNVERIFIED: legacy Targo native compatibility was"
    note="$note explicitly authorized; this run emits no proof claim"
    echo "$note" >&2
    exec "$backend" "$@"
}}
if [ "${{1-}}" = "--unverified" ]; then
    shift
    if ! is_native_command "${{1-}}"; then
        echo "error: --unverified is valid only for a Targo compilation command" >&2
        exit 101
    fi
    run_explicit_unverified "$@"
fi
if is_native_command "${{1-}}"; then
    command=$1
    if [ "${{2-}}" = "--unverified" ]; then
        shift
        shift
        set -- "$command" "$@"
        run_explicit_unverified "$@"
    fi
    note="error: targo $command refuses to create an implicitly"
    note="$note unverified artifact; use targo --unverified $command"
    echo "$note" >&2
    exit 101
fi
for argument in "$@"; do
    if is_native_command "$argument"; then
        note="error: legacy Targo requires --unverified immediately"
        note="$note before or after the compilation command"
        echo "$note" >&2
        exit 101
    fi
    if [ "$argument" = "--unverified" ]; then
        echo "error: --unverified is valid only for a Targo compilation command" >&2
        exit 101
    fi
done
exec "$backend" "$@"
""".format(backend_dir=STAGE0_LEGACY_TARGO_BACKEND_DIR),
        )
        for canonical_tool, retired_tool in (
            ("trustdoc", "rustdoc"),
            ("trustfmt", "rustfmt"),
            ("trust-analyzer", "rust-analyzer"),
        ):
            canonical_path = os.path.join(bin_dir, canonical_tool + EXE_SUFFIX)
            retired_path = os.path.join(bin_dir, retired_tool + EXE_SUFFIX)
            if not os.path.exists(canonical_path) and os.path.exists(retired_path):
                copy_executable(retired_path, canonical_path)
        # The legacy frontend resolves trustc/trustdoc next to its own
        # executable. Private forwarding shims preserve that behavior after
        # moving tcargo out of the public bin surface.
        for compiler_tool in ("trustc", "trustdoc"):
            if not os.path.exists(os.path.join(bin_dir, compiler_tool + EXE_SUFFIX)):
                raise RuntimeError(
                    "legacy Trust stage0 tcargo adapter lacks bin/{}".format(
                        compiler_tool
                    )
                )
            write_executable(
                os.path.join(backend_dir, compiler_tool),
                "#!/bin/sh\nexec \"$(dirname \"$0\")/../bin/{tool}\" \"$@\"\n".format(
                    tool=compiler_tool
                ),
            )

        # Companion archives in the same admitted seed predate the public
        # alias purge. Normalize only under the checksum-pinned tcargo gate so
        # a newly produced canonical archive with stale leaves still fails.
        legacy_fmt = os.path.join(bin_dir, "tcargo-fmt" + EXE_SUFFIX)
        canonical_fmt = os.path.join(bin_dir, "targo-fmt" + EXE_SUFFIX)
        if not os.path.exists(canonical_fmt) and os.path.exists(legacy_fmt):
            copy_executable(legacy_fmt, canonical_fmt)
        for retired in (
            "tcargo-fmt",
            "cargo-fmt",
            "rustfmt",
            "rustdoc",
            "rust-analyzer",
        ):
            path = os.path.join(bin_dir, retired + EXE_SUFFIX)
            if os.path.exists(path):
                os.remove(path)
        retired_analyzer_helper = os.path.join(
            bin_root, "libexec", "rust-analyzer-proc-macro-srv" + EXE_SUFFIX
        )
        canonical_analyzer_helper = os.path.join(
            bin_root, "libexec", "trust-analyzer-proc-macro-srv" + EXE_SUFFIX
        )
        if not os.path.exists(canonical_analyzer_helper) and os.path.exists(
            retired_analyzer_helper
        ):
            copy_executable(retired_analyzer_helper, canonical_analyzer_helper)
        if os.path.exists(retired_analyzer_helper):
            os.remove(retired_analyzer_helper)

    if "targo-trust" in legacy_components:
        legacy_trust = os.path.join(bin_dir, "tcargo-trust" + EXE_SUFFIX)
        trust_backend = os.path.join(backend_dir, "tcargo-trust-stage0-backend")
        copy_executable(legacy_trust, trust_backend)
        write_executable(
            os.path.join(bin_dir, "targo-trust"),
            """#!/bin/sh
backend="$(dirname "$0")/../{backend_dir}/tcargo-trust-stage0-backend"
rewrite_version=0
if [ "$#" -eq 1 ] && {{ [ "$1" = "--version" ] || [ "$1" = "-V" ]; }}; then
    rewrite_version=1
fi
if [ "$#" -eq 2 ] && [ "$1" = "trust" ] && {{ [ "$2" = "--version" ] || [ "$2" = "-V" ]; }}; then
    rewrite_version=1
fi
if [ "$rewrite_version" -eq 1 ]; then
    output=$("$backend" "$@")
    status=$?
    printf '%s\n' "$output" | sed 's/tcargo/targo/g'
    exit "$status"
fi
exec "$backend" "$@"
""".format(backend_dir=STAGE0_LEGACY_TARGO_BACKEND_DIR),
        )

    # A legacy tcargo frontend searches its own directory for tcargo-trust.
    # Keep that compatibility name private and route it through the canonical
    # public adapter (or canonical binary when only tcargo itself was legacy).
    if "targo" in legacy_components:
        for legacy_subcommand, canonical_subcommand in (
            ("tcargo-trust", "targo-trust"),
            ("tcargo-fmt", "targo-fmt"),
            ("tcargo-tippy", "targo-tippy"),
        ):
            write_executable(
                os.path.join(backend_dir, legacy_subcommand),
                "#!/bin/sh\nexec \"$(dirname \"$0\")/../bin/{tool}\" \"$@\"\n".format(
                    tool=canonical_subcommand
                ),
            )

    for legacy in ("tcargo", "tcargo-trust", "tcargo-fmt", "cargo-trust"):
        path = os.path.join(bin_dir, legacy + EXE_SUFFIX)
        if os.path.exists(path):
            os.remove(path)


def legacy_tippy_adapter_script(backend, public_name, prelude="", inject_marker=False):
    """Create a forwarding adapter with canonical version identity."""
    command = '"$backend"{} "$@"'.format(" clippy" if inject_marker else "")
    version_command = '"$backend"{} --version'.format(
        " clippy" if inject_marker else ""
    )
    version_flags = "--version|-V" if public_name == "tippy-driver" else "--version|-V|-vV|-Vv"
    canonical_cargo = (
        'CARGO="$adapter_dir/targo"\nexport CARGO\n' if inject_marker else ""
    )
    return (
        "#!/bin/sh\n"
        + prelude
        + 'case "$0" in\n'
        + '    */*) adapter_dir=${0%/*} ;;\n'
        + '    *) adapter_dir=. ;;\n'
        + 'esac\n'
        + 'backend="$adapter_dir/../libexec/{}"\n'.format(backend)
        + canonical_cargo
        + "version_query=0\n"
        + 'if [ "$#" -eq 1 ]; then\n'
        + '    case "$1" in {}) version_query=1 ;; esac\n'.format(version_flags)
        + 'elif [ "$#" -eq 2 ]; then\n'
        + '    if { [ "$1" = "--version" ] && [ "$2" = "--verbose" ]; } || '
        + '{ [ "$1" = "--verbose" ] && [ "$2" = "--version" ]; }; then\n'
        + "        version_query=1\n"
        + "    fi\n"
        + "fi\n"
        + 'if [ "$version_query" -eq 1 ]; then\n'
        + "    output=$({})\n".format(version_command)
        + "    status=$?\n"
        + "    printf '%s\\n' \"$output\" | command -p sed "
        + "-e '1s/^[^ ][^ ]*/tippy/' "
        + "-e 's/^binary: .*/binary: {}/'\n".format(public_name)
        + '    exit "$status"\n'
        + "fi\n"
        + "exec {}\n".format(command)
    )


def translate_legacy_tippy_stage0_surface(bin_root):
    """Materialize semantic canonical Tippy adapters from an admitted legacy payload."""
    if platform_is_win32():
        raise RuntimeError(
            "legacy Trust stage0 Tippy pins require a native canonical regeneration on Windows"
        )

    bin_dir = os.path.join(bin_root, "bin")
    libexec_dir = os.path.join(bin_root, "libexec")
    os.makedirs(libexec_dir, exist_ok=True)

    frontend = next(
        (
            os.path.join(bin_dir, name + EXE_SUFFIX)
            for name in STAGE0_LEGACY_TIPPY_FRONTENDS
            if os.path.exists(os.path.join(bin_dir, name + EXE_SUFFIX))
        ),
        None,
    )
    driver = next(
        (
            os.path.join(bin_dir, name + EXE_SUFFIX)
            for name in STAGE0_LEGACY_TIPPY_DRIVERS
            if os.path.exists(os.path.join(bin_dir, name + EXE_SUFFIX))
        ),
        None,
    )
    if frontend is None or driver is None:
        raise RuntimeError(
            "legacy Trust stage0 Tippy payload lacks a frontend or compiler driver"
        )

    backend = os.path.join(libexec_dir, STAGE0_TIPPY_BACKEND)
    driver_backend = os.path.join(libexec_dir, STAGE0_TIPPY_DRIVER_BACKEND)
    for source, destination in ((frontend, backend), (driver, driver_backend)):
        shutil.copy2(source, destination)
        os.chmod(destination, os.stat(destination).st_mode | 0o111)

    # The admitted frontend is an old cargo-clippy-style executable. It does
    # not merely accept a driver path from its caller: it derives either
    # `trust-clippy-driver` or `clippy-driver` beside its own executable and
    # installs that path as Cargo's rustc wrapper. Moving only the frontend and
    # driver payloads to canonically named private backends therefore leaves a
    # frontend that starts successfully but cannot lint anything. Keep those
    # inherited discovery names strictly inside libexec as forwarding protocol
    # shims; no retired name is restored to the public bin directory.
    for legacy_driver in STAGE0_LEGACY_TIPPY_DRIVERS:
        destination = os.path.join(libexec_dir, legacy_driver + EXE_SUFFIX)
        with open(destination, "w", encoding="utf-8", newline="\n") as adapter:
            adapter.write(
                "#!/bin/sh\n"
                'case "$0" in\n'
                '    */*) adapter_dir=${{0%/*}} ;;\n'
                '    *) adapter_dir=. ;;\n'
                "esac\n"
                'exec "$adapter_dir/{}" "$@"\n'.format(
                    STAGE0_TIPPY_DRIVER_BACKEND
                )
            )
        os.chmod(destination, 0o755)

    # cargo-clippy-style frontends unconditionally discard their first
    # argument as Cargo's external-subcommand marker. Direct `tippy` has no
    # marker, so a byte copy would lose the user's first option. These adapters
    # normalize both public invocation forms before entering the legacy binary.
    adapters = (
        ("tippy", STAGE0_TIPPY_BACKEND, "", True),
        (
            "targo-tippy",
            STAGE0_TIPPY_BACKEND,
            'if [ "${1-}" = "tippy" ]; then\n    shift\nfi\n',
            True,
        ),
        ("tippy-driver", STAGE0_TIPPY_DRIVER_BACKEND, "", False),
    )
    for canonical, adapter_backend, prelude, inject_marker in adapters:
        destination = os.path.join(bin_dir, canonical)
        with open(destination, "w", encoding="utf-8", newline="\n") as adapter:
            adapter.write(
                legacy_tippy_adapter_script(
                    adapter_backend,
                    canonical,
                    prelude=prelude,
                    inject_marker=inject_marker,
                )
            )
        os.chmod(destination, 0o755)

    legacy_paths = [
        os.path.join(bin_dir, name + EXE_SUFFIX)
        for name in (*STAGE0_LEGACY_TIPPY_FRONTENDS, *STAGE0_LEGACY_TIPPY_DRIVERS)
    ]
    for path in set(legacy_paths):
        if os.path.exists(path):
            os.remove(path)


class FakeArgs:
    """Used for unit tests to avoid updating all call sites"""

    def __init__(self):
        self.build = ""
        self.build_dir = ""
        self.clean = False
        self.verbose = False
        self.json_output = False
        self.color = "auto"
        self.warnings = "default"
        self.jobs = None


TRUST_BOOTSTRAP_NO_VERIFY_FLAG = "-Ztrust-verify=off"

# Trust: the unstable Trust std features that bootstrap's own dependency graph
# enables, each only under the `trust_std` cfg its build script derives from a
# `trust:` line in the compiler's `-vV`. `crates/trust-resource-controller`
# (`features = ["client"]`) selects `trust_process_inherit_fds`, std's
# per-child descriptor inheritance. The initial bootstrap build's otherwise
# empty `-Zallow-features=` names these and nothing else, as the Rust driver's
# `TARGO_ALLOW_FEATURES` does for the tools that enable the same client.
# `bootstrap_test.py` re-derives the set from the dependency sources.
TRUST_BOOTSTRAP_STD_FEATURES = ("trust_process_inherit_fds",)


def trust_verifier_controls(value, encoded=False):
    """Return Trust-verifier `-Z` options present in a rustflags value.

    Initial bootstrap runs before the Rust bootstrap shim exists, so this small
    parser mirrors the shim's fail-closed control detection for both ordinary
    shell-style flags and Cargo's unit-separator encoded form.
    """
    if not value:
        return []
    if encoded:
        tokens = value.split("\x1f")
    else:
        try:
            tokens = shlex.split(value)
        except ValueError as error:
            raise RuntimeError("malformed bootstrap rustflags: {}".format(error))

    controls = []
    index = 0
    while index < len(tokens):
        token = tokens[index]
        option = None
        if token == "-Z":
            index += 1
            if index < len(tokens):
                option = tokens[index]
        elif token.startswith("-Z") and len(token) > 2:
            option = token[2:]
        if option:
            name = option.split("=", 1)[0].replace("_", "-")
            if name in ("trust-verify", "trust-policy") or name.startswith("trust-verify-"):
                controls.append(option)
        index += 1
    return controls


# Per-attempt timeouts (seconds) for the Stage0 `-Z help` capability probe.
# The first attempt is short so a warm driver answers without delay. A retry is
# made ONCE, with a timeout long enough to outlast a macOS first-exec scan of a
# freshly extracted `trustc` (measured ~40s) or a concurrent extraction. Only if
# every attempt fails is the probe "unanswerable" -- and an unanswerable probe
# is costly even though it fails closed (see `apply_trust_bootstrap_compiler_policy`).
STAGE0_Z_HELP_TIMEOUTS = (10, 120)

# Memo of `stage0_z_help` answers, keyed by (driver path, environment).
# A process asks each driver ONCE: independent probes of the same driver can
# disagree (the first times out on a cold binary, a later one answers), and a
# policy assembled from disagreeing probes is incoherent. Measured 2026-09-28:
# three separate 10s probes of a freshly extracted stage0 `trustc` returned
# None, None, text -- the policy read that as "asked, no off-switch: stock
# upstream" and applied NO policy, a fail-open that sent the whole bootstrap
# dependency tree through batteries-on verification (regex-syntax E0391 cycle,
# memchr strict-verify errors). `None` answers are memoized too, so "could not
# ask" stays "could not ask" for every decision this process makes.
_STAGE0_Z_HELP_CACHE = {}

# Why a memoized `None` answer is unavailable, under the same key: the last
# attempt's refusal (status and first output line) or exception. Diagnostic
# data for the fallback warning only; no decision reads it.
_STAGE0_Z_HELP_UNAVAILABLE = {}


# Variables `apply_trust_bootstrap_compiler_policy` itself writes. They are not
# part of the memo key: the policy's own output must not turn a later question
# about the same driver into a fresh (possibly different) probe. None of them
# changes what a driver lists under `-Z help` -- the RUSTFLAGS lanes are read by
# Cargo, not rustc, and the TRUST_* transports act after option parsing.
_STAGE0_Z_HELP_POLICY_OUTPUTS = frozenset(
    (
        "TRUST_NO_VERIFY",
        "TRUST_VANILLA_ANNOUNCED",
        "RUSTFLAGS_BOOTSTRAP",
        "CARGO_ENCODED_RUSTFLAGS",
    )
)


def _stage0_z_help_cache_key(rustc, env):
    if env is None:
        return (rustc, None)
    return (
        rustc,
        tuple(
            sorted(
                (name, value)
                for name, value in env.items()
                if name not in _STAGE0_Z_HELP_POLICY_OUTPUTS
            )
        ),
    )


def clear_stage0_z_help_cache():
    """Forget every memoized Stage0 probe answer (tests; a replaced driver)."""
    _STAGE0_Z_HELP_CACHE.clear()
    _STAGE0_Z_HELP_UNAVAILABLE.clear()


def stage0_z_help_unavailable_reason(rustc, env):
    """Why the memoized probe of this driver did not answer, or None."""
    return _STAGE0_Z_HELP_UNAVAILABLE.get(_stage0_z_help_cache_key(rustc, env))


def stage0_z_help(rustc, env):
    """`rustc -Z help` output for the concrete Stage0 driver, or None.

    Memoized per (driver, environment) for the life of the process: see
    `_STAGE0_Z_HELP_CACHE`. Every capability decision about one driver must be
    made from ONE answer.

    `None` means no usable capability answer: execution/admission failed or the
    response was empty or refused. It does NOT mean "no Trust surface"; that is
    a positive answer and is returned as text, even when the driver delivers it
    by exiting non-zero.

    That distinction is this function's contract, stated in
    `stage0_trust_surface_available`, whose docstring calls collapsing the two
    "a FAIL-OPEN, and an expensive one". This function used to collapse them: a
    non-zero exit returned `None`. A STABLE rustc answers `-Z help` by rejecting
    it outright --

        $ rustc -Z help; echo $?
        error: the option `Z` is only accepted on the nightly compiler
        1

    -- which is a DEFINITIVE "no Trust surface here", not an unanswerable probe.
    Reading it as unanswerable made the caller's fail-closed branch fire on every
    machine whose stage0 is a stock stable rustc (the common case), planting
    `TRUST_NO_VERIFY=1` in the bootstrap driver's environment. That variable then
    leaks to compiletest and every stage1 `trustc` the ui suite spawns, where the
    driver applies it as a post-parse override that BEATS each test's explicit
    `-Ztrust-verify=on`. Measured consequence: the whole tests/ui/trust suite ran
    with verification silently OFF -- 145 of 304 failing, 127 of them "an expected
    failure signal was not produced" (monitors not aborting, expected errors not
    emitted). See reports/red-145-root-cause-2026-08-08.md.

    Execution exceptions retain the existing bounded attempt policy. An
    infrastructure refusal (including status 75), blank output or other failed
    response is unavailable; only the known stable rejection is a nonzero
    capability answer. Cached unavailability never becomes a stock answer.
    """
    key = _stage0_z_help_cache_key(rustc, env)
    if key in _STAGE0_Z_HELP_CACHE:
        return _STAGE0_Z_HELP_CACHE[key]
    reasons = []
    answer = _probe_stage0_z_help(rustc, env, reasons)
    _STAGE0_Z_HELP_CACHE[key] = answer
    if answer is None and reasons:
        _STAGE0_Z_HELP_UNAVAILABLE[key] = reasons[-1]
    return answer


def _probe_refusal_reason(result):
    """`exit N: <first output line>` for a probe response that is no answer."""
    first = next((line.strip() for line in (result.stdout or "").splitlines() if line.strip()),
                 "no output")
    return "exit {}: {}".format(result.returncode, first[:240])


def _probe_stage0_z_help(rustc, env, reasons=None):
    """Run the uncached `-Z help` probe, retrying an unanswered attempt.

    `reasons`, when given, receives one line per unanswered attempt.
    """
    if reasons is None:
        reasons = []
    # Trust: compiler identity is independent of the shared native transport.
    # Only a materialized compiler under this source's pinned stage0 is bound;
    # explicit non-pinned stock/genesis drivers keep their existing query path.
    from pathlib import Path
    bootstrap_serial_owner()  # Select only this source's scripts/lib imports.
    import seed_compiler_identity
    compiler = Path(rustc)
    root = Path(__file__).resolve().parents[2]
    try:
        # Windows retains its existing direct, read-only query path. Producing
        # materialized-seed checks there remain unavailable, not POSIX custody.
        binding = None if platform_is_win32() else seed_compiler_identity.pinned_compiler_binding(
            root, compiler, timeout=max(STAGE0_Z_HELP_TIMEOUTS)
        )
    except (OSError, seed_compiler_identity.SeedIdentityError, subprocess.TimeoutExpired) as error:
        raise RuntimeError(f"pinned Stage0 identity unavailable: {error}") from error
    for attempt, timeout in enumerate(STAGE0_Z_HELP_TIMEOUTS):
        try:
            if binding is not None:
                seed_compiler_identity.check_compiler_snapshot(compiler, binding)
            result = bootstrap_capability_command(
                [rustc, "-Z", "help"],
                env=env,
                timeout=timeout,
                serial=True,
            )
            if binding is not None:
                seed_compiler_identity.check_compiler_snapshot(compiler, binding)
        except seed_compiler_identity.SeedIdentityError:
            # A changed applicable pin is not a cold-start timeout or a reason
            # to query a different driver/owner.
            raise
        except (OSError, RuntimeError, subprocess.TimeoutExpired) as error:
            reasons.append("{}: {}".format(type(error).__name__, str(error)[:240]))
            if attempt + 1 < len(STAGE0_Z_HELP_TIMEOUTS):
                eprint(
                    "note: the Stage0 driver's Trust flag-surface probe ({}) did not "
                    "answer ({}); retrying once with a {}s timeout (a freshly "
                    "extracted driver can take ~40s on its first exec)".format(
                        rustc,
                        type(error).__name__,
                        STAGE0_Z_HELP_TIMEOUTS[attempt + 1],
                    )
                )
            continue
        # Trust: infrastructure refusals and empty output cannot establish that
        # this compiler lacks Trust. Preserve the genuine stable -Z rejection.
        stable_rejection = (
            result.returncode == 1
            and "the option `Z` is only accepted on the nightly compiler" in result.stdout
        )
        if (result.returncode == 0 and result.stdout.strip()) or stable_rejection:
            return result.stdout
        reasons.append(_probe_refusal_reason(result))
        return None
    return None


def help_advertises_trust_bootstrap_no_verify(help_text):
    """Whether answered `-Z help` text advertises the current off-switch."""
    return help_text is not None and any(
        re.match(r"^\s*-Z\s+trust-verify(?:=|\s|$)", line)
        for line in help_text.splitlines()
    )


def help_advertises_retired_no_verify(help_text):
    """Whether answered `-Z help` text advertises the retired off-switch."""
    return help_text is not None and any(
        re.match(r"^\s*-Z\s+no-trust-verify(?:=|\s|$)", line)
        for line in help_text.splitlines()
    )


def rustc_supports_trust_bootstrap_no_verify(rustc, env):
    """Capability-probe the concrete Stage0 driver without compiling input."""
    return help_advertises_trust_bootstrap_no_verify(stage0_z_help(rustc, env))


def stage0_trust_surface_available(rustc, env):
    """Whether the capability probe could answer AT ALL.

    Separated from the two spelling detectors because `None` from
    `stage0_z_help` means "I could not ask", which is NOT the same fact as
    "asked, and this driver has no Trust off-switch". Collapsing the two is a
    FAIL-OPEN, and an expensive one: see the caller.
    """
    return stage0_z_help(rustc, env) is not None


def rustc_advertises_retired_no_verify(rustc, env):
    """Detect a PRE-RENAME Trust Stage0 by its retired off-switch spelling.

    A driver that advertises neither spelling is stock upstream (no Trust
    machinery; nothing to disable). One that advertises only the retired
    `-Zno-trust-verify` is a Trust seed older than the flag-surface
    consolidation that renamed the off-switch — its batteries-on default
    would otherwise verify the whole bootstrap dependency tree and abort on
    the first verification-refused dep (memchr's SIMD paths, ~700 errors).
    """
    return help_advertises_retired_no_verify(stage0_z_help(rustc, env))


def apply_trust_bootstrap_compiler_policy(rustc, env):
    """Disable batteries-on verification only for a capable Trust Stage0.

    Bootstrap establishes compiler lineage; it is deliberately not a self-proof
    session. A stock upstream driver advertises no Trust off-switch spelling
    and is left untouched; a PRE-RENAME Trust seed (advertises only the
    retired `-Zno-trust-verify`) is addressed through the version-invariant
    nested-process transport `TRUST_NO_VERIFY=1`, which every Trust vintage
    translates before option parsing — appending the current flag spelling
    would abort it with `unknown unstable option`, and appending the retired
    spelling would abort every post-rename seed. Conflicting verifier controls
    fail closed instead of relying on unstable-option ordering.

    The driver is asked ONCE and every branch below reads that one answer.
    Three independent probes used to make the three decisions; a cold driver
    answered None, None, text, and the mixed answers selected the stock
    upstream branch -- no policy at all. `help_text is None` ("could not ask")
    now always reaches the fail-closed transport.
    """
    help_text = stage0_z_help(rustc, env)
    current_surface = help_advertises_trust_bootstrap_no_verify(help_text)
    retired_surface = help_advertises_retired_no_verify(help_text)
    if help_text is not None and not current_surface and not retired_surface:
        return False

    # Trust: every path that selects the bootstrap policy must reject
    # conflicting caller controls before changing the environment. An unknown
    # surface or an older Trust seed still selects that policy via transport.
    flag_sources = (
        ("RUSTFLAGS", False),
        ("RUSTFLAGS_BOOTSTRAP", False),
        ("CARGO_ENCODED_RUSTFLAGS", True),
    )
    for name, encoded in flag_sources:
        for option in trust_verifier_controls(env.get(name, ""), encoded=encoded):
            if option != "trust-verify=off":
                raise RuntimeError(
                    "bootstrap compiler verification control `{}` in {} conflicts with the "
                    "recorded non-self-proving bootstrap policy".format(option, name)
                )

    if not current_surface:
        if retired_surface:
            env["TRUST_NO_VERIFY"] = "1"
            return False
        if help_text is None:
            # FAIL CLOSED. An unanswerable probe used to fall through here to
            # "stock upstream, nothing to disable", which is the wrong default
            # in the wrong direction: if the driver IS a batteries-on Trust
            # seed, applying no policy verifies the ENTIRE third-party
            # bootstrap dependency tree and aborts the build. Measured
            # 2026-08-04: a `--stage 2` run whose probe did not answer spent
            # 1:18:20 and 582,226 log lines inside "Building bootstrap" before
            # dying on `memchr` with 694 verification errors, having never
            # reached a single compiler step. The probe is a subprocess with a
            # bounded timeout (retried once; `STAGE0_Z_HELP_TIMEOUTS`) against a
            # binary x.py may be extracting concurrently or macOS may be
            # first-exec scanning, so "could not ask" is a real, transient,
            # load-dependent state — not a hypothetical.
            #
            # The env transport is the safe fallback precisely because it
            # cannot abort anything: `TRUST_NO_VERIFY` is read before option
            # parsing by every Trust vintage, and a stock upstream rustc
            # ignores an unknown environment variable. Appending an argv
            # spelling here could not be safe — the two spellings abort each
            # other's vintage with `unknown unstable option`.
            #
            # Trust (BOOTSTRAP-SEED-PROBE-ADMISSION-1): say WHY the probe did
            # not answer and what to do. A status-75 refusal is native custody
            # or admission refusing the query, not a slow driver, and the env
            # transport does not change it, so the warning names the fix.
            reason = stage0_z_help_unavailable_reason(rustc, env) or "no attempt answered"
            eprint(
                "warning: could not probe the Stage0 driver's Trust flag surface "
                "({}: {}); assuming a batteries-on Trust seed and disabling "
                "verification for the bootstrap build via TRUST_NO_VERIFY=1. "
                "Bootstrap establishes compiler lineage and is deliberately not "
                "a self-proving session, so this is safe for a stock driver "
                "too.".format(rustc, reason)
            )
            if reason.startswith("exit 75:"):
                eprint(
                    "help: exit 75 is a native custody or admission refusal, not a "
                    "capability answer. Inside a managed context run x.py under "
                    "scripts/build-slot, which admits the probe; otherwise remove the "
                    "custody advertisement the refusal names from the environment."
                )
            env["TRUST_NO_VERIFY"] = "1"
        return False

    bootstrap_flags = env.get("RUSTFLAGS_BOOTSTRAP", "").strip()
    if "trust-verify=off" not in trust_verifier_controls(bootstrap_flags):
        env["RUSTFLAGS_BOOTSTRAP"] = "{}{}".format(
            bootstrap_flags + " " if bootstrap_flags else "",
            TRUST_BOOTSTRAP_NO_VERIFY_FLAG,
        )

    # Cargo ignores RUSTFLAGS when its encoded form is present. Preserve the
    # caller's unrelated encoded flags while ensuring the same exact policy is
    # effective in that precedence lane too.
    if "CARGO_ENCODED_RUSTFLAGS" in env:
        encoded_flags = env["CARGO_ENCODED_RUSTFLAGS"]
        if "trust-verify=off" not in trust_verifier_controls(encoded_flags, encoded=True):
            env["CARGO_ENCODED_RUSTFLAGS"] = "{}{}{}".format(
                encoded_flags,
                "\x1f" if encoded_flags else "",
                TRUST_BOOTSTRAP_NO_VERIFY_FLAG,
            )
    # The off-switch above is bootstrap's announced, recorded policy; quiet a
    # note-capable seed's once-per-crate vanilla note (diagnostic-only, and
    # older seeds ignore the variable).
    env["TRUST_VANILLA_ANNOUNCED"] = "1"
    return True


def bootstrap_runtime_env(rustc, environ=None):
    """Construct the environment inherited by the Rust bootstrap driver.

    The initial Cargo build and the Rust bootstrap process must share the same
    seed-compiler policy. Otherwise direct `x.py test`/`build` commands compile
    the Python-built driver successfully and then re-enable batteries-on Trust
    verification for that driver's dependency builds.
    """
    env = os.environ.copy() if environ is None else environ.copy()
    env["BOOTSTRAP_PYTHON"] = sys.executable
    apply_trust_bootstrap_compiler_policy(rustc, env)
    return env


class RustBuild(object):
    """Provide all the methods required to build Rust"""

    def __init__(self, config_toml="", args=None):
        if args is None:
            args = FakeArgs()
        self.git_version = None
        self.nix_deps_dir = None
        self._should_fix_bins_and_dylibs = None
        self.rust_root = os.path.abspath(os.path.join(__file__, "../../.."))

        self.config_toml = config_toml

        self.clean = args.clean
        self.json_output = args.json_output
        self.verbose = args.verbose
        self.color = args.color
        self.warnings = args.warnings

        config_verbose_count = self.get_toml("verbose", "build")
        if config_verbose_count is not None:
            self.verbose = max(self.verbose, int(config_verbose_count))

        self.use_vendored_sources = self.get_toml("vendor", "build") == "true"
        self.use_locked_deps = self.get_toml("locked-deps", "build") == "true"

        build_dir = args.build_dir or self.get_toml("build-dir", "build") or "build"
        self.build_dir = os.path.abspath(build_dir)

        self.stage0_data = parse_stage0_file(
            os.path.join(self.rust_root, "src", "stage0")
        )
        self.stage0_compiler = Stage0Toolchain(
            self.stage0_data["compiler_date"], self.stage0_data["compiler_version"]
        )
        self.download_url = self.stage0_data["dist_server"]
        reject_inherited_upstream_rust_download_url(
            self.download_url, "Trust stage0 dist_server"
        )
        self.jobs = self.get_toml("jobs", "build") or "default"
        self.cli_jobs = args.jobs

        self.build = args.build or self.build_triple()

    def download_toolchain(self):
        """Fetch the build system for Rust, written in Rust

        This method will build a cache directory, then it will fetch the
        tarball which has the stage0 compiler used to then bootstrap the Rust
        compiler itself.

        Fail-closed contract (2026-07-29 seed-destruction incident): the live
        stage0 seed is only ever replaced by an atomic rename of a fully
        downloaded, extracted, and surface-verified staging tree. Any failure
        to download, unpack, or validate aborts BEFORE the existing seed is
        touched. A refresh always re-images the complete component surface:
        the old code deleted the whole seed but downloaded only the
        need-scoped half, so a Targo-only trigger deleted trustc/trust-std
        and never reinstalled them.
        """
        rustc_channel = self.stage0_compiler.version
        bin_root = self.bin_root()

        # Trust: date is a reproducible dist location, not a seed identity.
        key = stage0_extraction_stamp(self.stage0_data)
        is_outdated = self.program_out_of_date(self.rustc_stamp(), key)
        surface_needs_refresh = self.stage0_tool_surface_needs_refresh()
        need_rustc = self.rustc().startswith(bin_root) and (
            not os.path.exists(self.rustc()) or is_outdated or surface_needs_refresh
        )
        need_cargo = self.cargo().startswith(bin_root) and (
            not os.path.exists(self.cargo()) or is_outdated or surface_needs_refresh
        )

        if not (need_rustc or need_cargo):
            return

        # A configured tool path under bin_root whose basename is a FORBIDDEN
        # stage0 name (e.g. a stale `cargo = .../bin/tcargo` pin left in
        # bootstrap.toml from before the tcargo->targo rename) can never be
        # satisfied by a refresh: assert_stage0_tool_surface guarantees the
        # canonical surface does not contain it, so the trigger would re-fire
        # on every run, re-imaging the seed forever. This exact loop is what
        # destroyed the 2026-07-13 seed on 2026-07-29. Reject with guidance
        # instead of refreshing.
        for config_key, tool_path in (("rustc", self.rustc()), ("cargo", self.cargo())):
            if not tool_path.startswith(bin_root):
                continue
            basename = os.path.basename(tool_path)
            if EXE_SUFFIX and basename.endswith(EXE_SUFFIX):
                basename = basename[: -len(EXE_SUFFIX)]
            if basename in STAGE0_FORBIDDEN_BINS:
                raise RuntimeError(
                    "bootstrap.toml [build] {} points at {}, but `{}` is a "
                    "forbidden legacy stage0 name that a refresh can never "
                    "produce; update the pin to the canonical binary "
                    "(e.g. bin/targo) instead of re-imaging the seed on "
                    "every run.".format(config_key, tool_path, basename)
                )

        cache_dst = self.get_toml("bootstrap-cache-path", "build") or os.path.join(
            self.build_dir, "cache"
        )

        # Trust: retain date-based cache paths; get() verifies the current pin.
        rustc_cache = os.path.join(cache_dst, self.stage0_compiler.date)
        if not os.path.exists(rustc_cache):
            os.makedirs(rustc_cache)

        tarball_suffix = ".tar.gz" if lzma is None else ".tar.xz"

        # This SAME pure selection also feeds the retained native planner.
        # Only the download/extraction owner admits the selected payload bytes.
        (tarballs_to_download, legacy_targo_components,
         translate_legacy_tippy) = _identity_owner.component_archives(
            self.stage0_data, self.stage0_compiler.date, rustc_channel,
            self.build, tarball_suffix)

        # Stage the replacement seed NEXT TO the live one (same filesystem,
        # so the final swap is a rename) and only touch bin_root once the
        # staged tree has passed the full surface assertion.
        staging_root = bin_root + ".staging"
        if os.path.exists(staging_root):
            shutil.rmtree(staging_root)
        os.makedirs(staging_root)

        tarballs_download_info = [
            DownloadInfo(
                base_download_url=self.download_url,
                download_path="dist/{}/{}".format(
                    self.stage0_compiler.date, filename
                ),
                bin_root=staging_root,
                tarball_path=os.path.join(rustc_cache, filename),
                tarball_suffix=tarball_suffix,
                stage0_data=self.stage0_data,
                pattern=pattern,
                verbose=self.verbose,
            )
            for filename, pattern in tarballs_to_download
        ]

        try:
            # Download the components serially to show the progress bars
            # properly. A missing or checksum-failing archive raises HERE,
            # before the live seed has been touched.
            for download_info in tarballs_download_info:
                download_component(download_info)

            # Unpack the tarballs in parallel.
            # In Python 2.7, Pool cannot be used as a context manager.
            pool_size = min(len(tarballs_download_info), get_cpus())
            if self.verbose > 0:
                print(
                    "Choosing a pool size of",
                    pool_size,
                    "for the unpacking of the tarballs",
                )
            p = Pool(pool_size)
            try:
                # FIXME: A cheap workaround for https://github.com/rust-lang/rust/issues/125578,
                # remove this once the issue is closed.
                bootstrap_build_artifacts = os.path.join(self.bootstrap_out(), "debug")
                if os.path.exists(bootstrap_build_artifacts):
                    shutil.rmtree(bootstrap_build_artifacts)

                p.map(unpack_component, tarballs_download_info)
            finally:
                p.close()
            p.join()

            if legacy_targo_components:
                translate_legacy_targo_stage0_surface(
                    staging_root, legacy_targo_components
                )
            if translate_legacy_tippy:
                translate_legacy_tippy_stage0_surface(staging_root)

            # Trust: the closed native profile selects SDK/bin/rust-lld. Older
            # authenticated distributions shipped only the same host image in
            # rustlib; materialize its explicit role before the atomic swap.
            _identity_owner.paired_linker(staging_root, self.build, materialize=True)

            # Verify the replacement surface is complete BEFORE swapping it
            # in. An incomplete extraction aborts with the working seed
            # still in place.
            self.assert_stage0_tool_surface(staging_root)

            if self.should_fix_bins_and_dylibs():
                for name in STAGE0_REQUIRED_BINS:
                    self.fix_bin_or_dylib(
                        "{}/bin/{}{}".format(staging_root, name, EXE_SUFFIX)
                    )
                for name in STAGE0_REQUIRED_LIBEXEC_BINS:
                    self.fix_bin_or_dylib(
                        "{}/libexec/{}{}".format(staging_root, name, EXE_SUFFIX)
                    )
                lib_dir = "{}/lib".format(staging_root)
                rustlib_bin_dir = "{}/rustlib/{}/bin".format(lib_dir, self.build)
                self.fix_bin_or_dylib("{}/rust-lld".format(rustlib_bin_dir))
                self.fix_bin_or_dylib("{}/gcc-ld/ld.lld".format(rustlib_bin_dir))
                for lib in os.listdir(lib_dir):
                    # .so is not necessarily the suffix, there can be version numbers afterwards.
                    if ".so" in lib:
                        elf_path = os.path.join(lib_dir, lib)
                        with open(elf_path, "rb") as f:
                            magic = f.read(4)
                            # Patchelf will skip non-ELF files, but issue a warning.
                            if magic == b"\x7fELF":
                                self.fix_bin_or_dylib(elf_path)
        except BaseException:
            shutil.rmtree(staging_root, ignore_errors=True)
            raise

        # Swap the verified staging tree into place. This is the only block
        # that touches the existing seed, and it rolls back on failure.
        if os.path.exists(bin_root):
            # HACK: On Windows, we can't rename the proc-macro server's tree
            # while it's running. Kill it.
            if platform_is_win32():
                print(
                    "Killing trust-analyzer-proc-macro-srv before replacing stage0 toolchain"
                )
                regex = "{}\\\\(host|{})\\\\stage0\\\\libexec".format(
                    os.path.basename(self.build_dir), self.build
                )
                script = (
                    # NOTE: can't use `taskkill` or `Get-Process -Name` because they error if
                    # the server isn't running.
                    "Get-Process | "
                    + 'Where-Object {$_.Name -eq "trust-analyzer-proc-macro-srv" '
                    + '-or $_.Name -eq "rust-analyzer-proc-macro-srv"} |'
                    + 'Where-Object {{$_.Path -match "{}"}} |'.format(regex)
                    + "Stop-Process"
                )
                run_powershell([script])
            previous_root = bin_root + ".previous"
            if os.path.exists(previous_root):
                shutil.rmtree(previous_root)
            os.rename(bin_root, previous_root)
            try:
                os.rename(staging_root, bin_root)
            except BaseException:
                # Roll the working seed back; never leave the tree seedless.
                os.rename(previous_root, bin_root)
                raise
            shutil.rmtree(previous_root)
        else:
            os.rename(staging_root, bin_root)
        # A different driver now answers at the same path: no probe answer
        # memoized for the old one may decide policy for the new one.
        clear_stage0_z_help_cache()

        with output(self.rustc_stamp()) as rust_stamp:
            rust_stamp.write(key)

    def stage0_tool_surface_needs_refresh(self, bin_root=None):
        if bin_root is None:
            bin_root = self.bin_root()
        bin_dir = os.path.join(bin_root, "bin")
        for name in STAGE0_REQUIRED_BINS:
            if not os.path.exists(os.path.join(bin_dir, name + EXE_SUFFIX)):
                return True
        for name in STAGE0_REQUIRED_LIBEXEC_BINS:
            if not os.path.exists(os.path.join(bin_root, "libexec", name + EXE_SUFFIX)):
                return True
        for name in STAGE0_FORBIDDEN_BINS:
            filename = name if name.endswith(".cmd") else name + EXE_SUFFIX
            if os.path.lexists(os.path.join(bin_dir, filename)):
                return True
        for name in STAGE0_FORBIDDEN_LIBEXEC_BINS:
            if os.path.lexists(os.path.join(bin_root, "libexec", name + EXE_SUFFIX)):
                return True
        return False

    def assert_stage0_tool_surface(self, bin_root=None):
        """Validate a stage0 surface tree (the live seed by default).

        download_toolchain also runs this against the STAGING tree before the
        atomic swap, so an incomplete replacement can never displace a
        working seed.
        """
        if bin_root is None:
            bin_root = self.bin_root()
        bin_dir = os.path.join(bin_root, "bin")
        for name in STAGE0_REQUIRED_BINS:
            path = os.path.join(bin_dir, name + EXE_SUFFIX)
            if not os.path.exists(path):
                raise RuntimeError("Trust stage0 seed is missing required {}".format(path))
        for name in STAGE0_REQUIRED_LIBEXEC_BINS:
            path = os.path.join(bin_root, "libexec", name + EXE_SUFFIX)
            if not os.path.exists(path):
                raise RuntimeError("Trust stage0 seed is missing required {}".format(path))
        for name in STAGE0_FORBIDDEN_BINS:
            filename = name if name.endswith(".cmd") else name + EXE_SUFFIX
            path = os.path.join(bin_dir, filename)
            if os.path.lexists(path):
                raise RuntimeError("Trust stage0 seed must not contain {}".format(path))
        _identity_owner.paired_linker(bin_root, self.build)
        for name in STAGE0_FORBIDDEN_LIBEXEC_BINS:
            path = os.path.join(bin_root, "libexec", name + EXE_SUFFIX)
            if os.path.lexists(path):
                raise RuntimeError("Trust stage0 seed must not contain {}".format(path))
    def should_fix_bins_and_dylibs(self):
        """Whether or not `fix_bin_or_dylib` needs to be run; can only be True
        on NixOS or if bootstrap.toml has `build.patch-binaries-for-nix` set.
        """
        if self._should_fix_bins_and_dylibs is not None:
            return self._should_fix_bins_and_dylibs

        def get_answer():
            default_encoding = sys.getdefaultencoding()
            try:
                ostype = (
                    subprocess.check_output(["uname", "-s"])
                    .strip()
                    .decode(default_encoding)
                )
            except subprocess.CalledProcessError:
                return False
            except OSError as reason:
                if getattr(reason, "winerror", None) is not None:
                    return False
                raise reason

            if ostype != "Linux":
                return False

            # If the user has explicitly indicated whether binaries should be
            # patched for Nix, then don't check for NixOS.
            if self.get_toml("patch-binaries-for-nix", "build") == "true":
                return True
            if self.get_toml("patch-binaries-for-nix", "build") == "false":
                return False

            # Use `/etc/os-release` instead of `/etc/NIXOS`.
            # The latter one does not exist on NixOS when using tmpfs as root.
            try:
                with open("/etc/os-release", "r", encoding="utf-8") as f:
                    is_nixos = any(
                        ln.strip() in ("ID=nixos", "ID='nixos'", 'ID="nixos"')
                        for ln in f
                    )
            except FileNotFoundError:
                is_nixos = False

            # If not on NixOS, then warn if user seems to be atop Nix shell
            if not is_nixos:
                in_nix_shell = os.getenv("IN_NIX_SHELL")
                if in_nix_shell:
                    eprint(
                        "The IN_NIX_SHELL environment variable is `{}`;".format(
                            in_nix_shell
                        ),
                        "you may need to set `patch-binaries-for-nix=true` in bootstrap.toml",
                    )

            return is_nixos

        answer = self._should_fix_bins_and_dylibs = get_answer()
        if answer:
            eprint("INFO: You seem to be using Nix.")
        return answer

    def fix_bin_or_dylib(self, fname):
        """Modifies the interpreter section of 'fname' to fix the dynamic linker,
        or the RPATH section, to fix the dynamic library search path

        This method is only required on NixOS and uses the PatchELF utility to
        change the interpreter/RPATH of ELF executables.

        Please see https://nixos.org/patchelf.html for more information
        """
        assert self._should_fix_bins_and_dylibs is True
        eprint("attempting to patch", fname)

        # Only build `.nix-deps` once.
        nix_deps_dir = self.nix_deps_dir
        if not nix_deps_dir:
            # Run `nix-build` to "build" each dependency (which will likely reuse
            # the existing `/nix/store` copy, or at most download a pre-built copy).
            #
            # Importantly, we create a gc-root called `.nix-deps` in the `build/`
            # directory, but still reference the actual `/nix/store` path in the rpath
            # as it makes it significantly more robust against changes to the location of
            # the `.nix-deps` location.
            #
            # bintools: Needed for the path of `ld-linux.so` (via `nix-support/dynamic-linker`).
            # zlib: Needed as a system dependency of `libLLVM-*.so`.
            # patchelf: Needed for patching ELF binaries (see doc comment above).
            nix_deps_dir = "{}/{}".format(self.build_dir, ".nix-deps")
            nix_expr = """
            with (import <nixpkgs> {});
            symlinkJoin {
              name = "rust-stage0-dependencies";
              paths = [
                zlib
                patchelf
                stdenv.cc.bintools
              ];
            }
            """
            try:
                subprocess.check_output(
                    [
                        "nix-build",
                        "-E",
                        nix_expr,
                        "-o",
                        nix_deps_dir,
                    ]
                )
            except subprocess.CalledProcessError as reason:
                eprint("WARNING: failed to call nix-build:", reason)
                return
            self.nix_deps_dir = nix_deps_dir

        patchelf = "{}/bin/patchelf".format(nix_deps_dir)
        rpath_entries = [os.path.join(os.path.realpath(nix_deps_dir), "lib")]
        patchelf_args = ["--add-rpath", ":".join(rpath_entries)]
        if ".so" not in fname:
            # Finally, set the correct .interp for binaries
            with open(
                "{}/nix-support/dynamic-linker".format(nix_deps_dir),
                encoding="utf-8",
            ) as dynamic_linker:
                patchelf_args += ["--set-interpreter", dynamic_linker.read().rstrip()]

        try:
            subprocess.check_output([patchelf] + patchelf_args + [fname])
        except subprocess.CalledProcessError as reason:
            eprint("WARNING: failed to call patchelf:", reason)
            return

    def rustc_stamp(self):
        """Return the path for .rustc-stamp at the given stage

        >>> rb = RustBuild()
        >>> rb.build = "host"
        >>> rb.build_dir = "build"
        >>> expected = os.path.join("build", "host", "stage0", ".rustc-stamp")
        >>> assert rb.rustc_stamp() == expected, rb.rustc_stamp()
        """
        return os.path.join(self.bin_root(), ".rustc-stamp")

    def program_out_of_date(self, stamp_path, key):
        """Check if the given program stamp is out of date"""
        if not os.path.exists(stamp_path) or self.clean:
            return True
        with open(stamp_path, "r", encoding="utf-8") as stamp:
            return key != stamp.read()

    def bin_root(self):
        """Return the binary root directory for the given stage

        >>> rb = RustBuild()
        >>> rb.build = "devel"
        >>> expected = os.path.abspath(os.path.join("build", "devel", "stage0"))
        >>> assert rb.bin_root() == expected, rb.bin_root()
        """
        subdir = "stage0"
        return os.path.join(self.build_dir, self.build, subdir)

    def get_toml(self, key, section=None):
        """Returns the value of the given key in bootstrap.toml, otherwise returns None

        >>> rb = RustBuild()
        >>> rb.config_toml = 'key1 = "value1"\\nkey2 = "value2"'
        >>> rb.get_toml("key2")
        'value2'

        If the key does not exist, the result is None:

        >>> rb.get_toml("key3") is None
        True

        Optionally also matches the section the key appears in

        >>> rb.config_toml = '[a]\\nkey = "value1"\\n[b]\\nkey = "value2"'
        >>> rb.get_toml('key', 'a')
        'value1'
        >>> rb.get_toml('key', 'b')
        'value2'
        >>> rb.get_toml('key', 'c') is None
        True

        A dotted key names a table relative to its enclosing section, so the
        full table path must match for the key to be found:

        >>> rb.config_toml = 'build.cargo = "/path/to/cargo"'
        >>> rb.get_toml('cargo', 'build')
        '/path/to/cargo'
        >>> rb.get_toml('cargo', 'other') is None
        True

        A dotted key inside a section composes with that section's name:

        >>> rb.config_toml = '[target]\\nx86_64-unknown-linux-gnu.cc = "gcc"'
        >>> rb.get_toml('cc', 'target.x86_64-unknown-linux-gnu')
        'gcc'

        >>> rb.config_toml = 'key1 = true'
        >>> rb.get_toml("key1")
        'true'
        """
        return RustBuild.get_toml_static(self.config_toml, key, section)

    @staticmethod
    def get_toml_static(config_toml, key, section=None):
        cur_section = None
        for line in config_toml.splitlines():
            section_match = re.match(r"^\s*\[(.*)\]\s*$", line)
            if section_match is not None:
                cur_section = section_match.group(1)

            # Match the key, optionally preceded by a dotted-table prefix (the
            # `build.` in `build.cargo`), which names a table relative to the
            # current `[section]` and is appended to `cur_section`. This is a
            # subset parser, not full TOML: quoted names (e.g. the `'a.b'` that
            # configure.py emits for dotted targets) are not matched here.
            match = re.match(
                r"^\s*(?:([\w.-]+)\.)?{}\s*=(.*)$".format(re.escape(key)), line
            )
            if match is not None:
                prefix = match.group(1)
                if prefix is None:
                    line_section = cur_section
                elif cur_section is None:
                    line_section = prefix
                else:
                    line_section = "{}.{}".format(cur_section, prefix)
                value = match.group(2)
                if section is None or section == line_section:
                    return RustBuild.get_string(value) or value.strip()
        return None

    def cargo(self):
        """Return config path for cargo"""
        return self.program_config("cargo")

    def rustc(self):
        """Return config path for rustc"""
        return self.program_config("rustc")

    def bootstrap_rustc(self):
        """Return an internal stage0 compiler adapter for building bootstrap.

        The public stage0 compiler is `trustc`, but some third-party build
        scripts query `$RUSTC --version` and parse the legacy `rustc` prefix.
        Keep that compatibility inside bootstrap without exposing a public
        `rustc` binary in the Trust toolchain.
        """
        rustc = self.rustc()
        if platform_is_win32():
            return rustc

        wrapper_dir = os.path.join(self.bootstrap_out(), "trust-stage0-tools")
        os.makedirs(wrapper_dir, exist_ok=True)
        wrapper = os.path.join(wrapper_dir, "trust-bootstrap-rustc")
        script = """#!/bin/sh
trustc={trustc}
rewrite_version() {{
    "$trustc" "$@" | sed -e '1s/^trustc /rustc /' -e 's/^binary: trustc$/binary: rustc/'
    exit $?
}}
if [ "$#" -eq 1 ] && {{ [ "$1" = "--version" ] || [ "$1" = "-V" ] || [ "$1" = "-vV" ]; }}; then
    rewrite_version "$@"
fi
if [ "$#" -eq 2 ] && {{ [ "$1" = "--version" ] && [ "$2" = "--verbose" ]; }}; then
    rewrite_version "$@"
fi
if [ "$#" -eq 2 ] && {{ [ "$1" = "--verbose" ] && [ "$2" = "--version" ]; }}; then
    rewrite_version "$@"
fi
exec "$trustc" "$@"
""".format(trustc=shlex.quote(rustc))
        current = None
        if os.path.exists(wrapper):
            with open(wrapper, "r") as existing:
                current = existing.read()
        if current != script:
            with open(wrapper, "w") as out:
                out.write(script)
            os.chmod(wrapper, 0o755)
        return wrapper

    def program_config(self, program):
        """Return config path for the given program at the given stage

        >>> rb = RustBuild()
        >>> rb.config_toml = 'build.rustc = "rustc"\\n'
        >>> rb.program_config('rustc')
        'rustc'
        >>> rb.config_toml = '[build]\\nrustc = "rustc"\\n'
        >>> rb.program_config('rustc')
        'rustc'
        >>> rb.config_toml = ''
        >>> cargo_path = rb.program_config('cargo')
        >>> cargo_path.rstrip(".exe") == os.path.join(rb.bin_root(),
        ... "bin", "cargo")
        True
        """
        config = self.get_toml(program, "build")
        if config:
            return os.path.expanduser(config)
        stage0_program = STAGE0_PROGRAM_NAMES.get(program, program)
        return os.path.join(self.bin_root(), "bin", "{}{}".format(stage0_program, EXE_SUFFIX))

    @staticmethod
    def get_string(line):
        """Return the value between double quotes

        >>> RustBuild.get_string('    "devel"   ')
        'devel'
        >>> RustBuild.get_string("    'devel'   ")
        'devel'
        >>> RustBuild.get_string('devel') is None
        True
        >>> RustBuild.get_string('    "devel   ')
        ''
        """
        start = line.find('"')
        if start != -1:
            end = start + 1 + line[start + 1 :].find('"')
            return line[start + 1 : end]
        start = line.find("'")
        if start != -1:
            end = start + 1 + line[start + 1 :].find("'")
            return line[start + 1 : end]
        return None

    def bootstrap_out(self):
        """Return the path of the bootstrap build artifacts

        >>> rb = RustBuild()
        >>> rb.build_dir = "build"
        >>> rb.bootstrap_binary() == os.path.join("build", "bootstrap")
        True
        """
        return os.path.join(self.build_dir, "bootstrap")

    def bootstrap_binary(self):
        """Return the path of the bootstrap binary

        >>> rb = RustBuild()
        >>> rb.build_dir = "build"
        >>> rb.bootstrap_binary() == os.path.join("build", "bootstrap",
        ... "debug", "bootstrap")
        True
        """
        return os.path.join(self.bootstrap_out(), "debug", "bootstrap")

    def build_bootstrap(self):
        """Build bootstrap"""
        env = os.environ.copy()
        if "GITHUB_ACTIONS" in env:
            print("::group::Building bootstrap")
        else:
            eprint("Building bootstrap")

        args = self.build_bootstrap_cmd(env)
        # Trust: materialize the frozen metatool, then let its canonical native
        # parser choose readiness before metadata, seeding or requested units.
        # No partial Python CLI parse can classify a native request safely.
        # Run this from the source directory so cargo finds .cargo/config
        try:
            run(args, env=env, verbose=self.verbose, cwd=self.rust_root,
                exception=True)
        except RuntimeError as error:
            # Trust: the producer is --frozen and never fetches, so on a machine
            # whose Cargo home lacks the locked sources Cargo says only "no
            # matching package". Name the explicit preparation operation.
            eprint(self.frozen_source_hint(env))
            sys.exit(str(error))

        if "GITHUB_ACTIONS" in env:
            print("::endgroup::")

    def frozen_source_hint(self, env):
        """The preparation command for a frozen bootstrap build's missing sources.

        Trust: printed only after the bootstrap producer failed. It runs
        nothing: fetching stays the operator's explicit, separate operation.
        Only the bootstrap producer's manifest is selected here; readiness for
        the native request remains the native parser's responsibility. Use the
        same driver, source directory, Cargo home and warning/offline policy.
        """
        lead = ("note: the bootstrap build is --frozen and never fetches. If "
                "Cargo reported a missing package or source above, ")
        if self.use_vendored_sources:
            # A vendored build resolves from vendor/, never the Cargo home.
            return lead + ("vendor/ does not hold the locked sources: refresh "
                           "it with `x.py vendor`, or build without "
                           "build.vendor after preparing the Cargo home.")
        root = os.path.abspath(self.rust_root)
        # Cargo's own default when CARGO_HOME is unset; the failed build used it.
        cargo_home = env.get("CARGO_HOME") or os.path.join(
            os.path.expanduser("~"), ".cargo")
        if not os.path.isabs(cargo_home):
            cargo_home = os.path.join(root, cargo_home)
        driver = self.cargo()
        # A bare configured program uses PATH in the actual producer too.
        # Only relative paths with a directory component are source-relative.
        if not os.path.isabs(driver) and os.path.dirname(driver):
            driver = os.path.join(root, driver)
        # Absence is policy too: a pasted command must not acquire a new
        # warning override or turn an explicitly offline caller online.
        policy_keys = ("CARGO_BUILD_WARNINGS", "TARGO_BUILD_WARNINGS",
                       "CARGO_NET_OFFLINE")
        command = ["env", "-u", "CARGO_BUILD_WARNINGS", "-u",
                   "TARGO_BUILD_WARNINGS", "-u", "CARGO_NET_OFFLINE",
                   "CARGO_HOME=" + cargo_home]
        command.extend(key + "=" + env[key]
                       for key in policy_keys if key in env)
        command += [driver, "fetch", "--locked", "--manifest-path",
                    os.path.join(root, "src", "bootstrap", "Cargo.toml")]
        # Fetch is a source-only native operation, not a compilation lane or a
        # full dependency-envelope check. Other network policy is inherited.
        offline_command = command + ["--offline"]
        prefix = "cd " + shlex.quote(root) + " && "
        return lead + (
            "prepare ONLY the bootstrap producer's locked sources in the SAME "
            "Cargo home under the caller's network policy, check them offline, "
            "then retry bootstrap. This does not prepare the full toolchain "
            "dependency closure:\n  "
            + prefix + " ".join(shlex.quote(part) for part in command)
            + "\n  " + prefix
            + " ".join(shlex.quote(part) for part in offline_command))

    def targo_supports_unverified_lane(self):
        """Does the configured cargo implement Targo's two-lane policy?

        Asks the binary rather than sniffing a version, so the check stays
        correct across seed refreshes. Cached per invocation.
        """
        cached = getattr(self, "_targo_unverified_lane", None)
        if cached is not None:
            return cached
        supported = False
        try:
            result = bootstrap_capability_command(
                [self.cargo(), "--help"],
                env=dict(os.environ),
                timeout=60,
            )
        except (OSError, RuntimeError, subprocess.TimeoutExpired) as error:
            raise RuntimeError("cannot establish bootstrap Targo lane capability") from error
        if result.returncode != 0 or not result.stdout.strip():
            raise RuntimeError("bootstrap Targo lane capability did not answer")
        supported = "--unverified" in result.stdout
        self._targo_unverified_lane = supported
        return supported

    def build_bootstrap_cmd(self, env):
        """For tests."""
        # Trust: refuse an invalid admission before cleaning directories,
        # opening the compiler adapter, or probing any stage0 tool.
        jobs = bootstrap_jobs(self.jobs, self.cli_jobs, env)
        build_dir = os.path.join(self.build_dir, "bootstrap")
        if self.clean and os.path.exists(build_dir):
            shutil.rmtree(build_dir)
        # `CARGO_BUILD_TARGET` breaks bootstrap build.
        # See also: <https://github.com/rust-lang/rust/issues/70208>.
        if "CARGO_BUILD_TARGET" in env:
            del env["CARGO_BUILD_TARGET"]
        # if in CI, don't use incremental build when building bootstrap.
        if "GITHUB_ACTIONS" in env:
            env["CARGO_INCREMENTAL"] = "0"
        env["CARGO_TARGET_DIR"] = build_dir
        env["RUSTC"] = self.bootstrap_rustc()
        # Trust's Stage0 compiler is batteries-on, but this pre-shim Cargo phase
        # is explicitly non-self-proving. Capability-gate the exact recorded
        # compiler off-switch here so direct `x.py` invocations and the
        # provenance-aware recreator share the same bootstrap boundary.
        apply_trust_bootstrap_compiler_policy(self.rustc(), env)
        env["LD_LIBRARY_PATH"] = (
            os.path.join(self.bin_root(), "lib") + (os.pathsep + env["LD_LIBRARY_PATH"])
            if "LD_LIBRARY_PATH" in env
            else ""
        )
        env["DYLD_LIBRARY_PATH"] = (
            os.path.join(self.bin_root(), "lib")
            + (os.pathsep + env["DYLD_LIBRARY_PATH"])
            if "DYLD_LIBRARY_PATH" in env
            else ""
        )
        env["LIBRARY_PATH"] = (
            os.path.join(self.bin_root(), "lib") + (os.pathsep + env["LIBRARY_PATH"])
            if "LIBRARY_PATH" in env
            else ""
        )
        env["LIBPATH"] = (
            os.path.join(self.bin_root(), "lib") + (os.pathsep + env["LIBPATH"])
            if "LIBPATH" in env
            else ""
        )

        # Export Stage0 snapshot compiler related env variables
        build_section = "target.{}".format(self.build)
        host_triple_sanitized = self.build.replace("-", "_")
        var_data = {
            "CC": "cc",
            "CXX": "cxx",
            "LD": "linker",
            "AR": "ar",
            "RANLIB": "ranlib",
        }
        for var_name, toml_key in var_data.items():
            toml_val = self.get_toml(toml_key, build_section)
            if toml_val is not None:
                env["{}_{}".format(var_name, host_triple_sanitized)] = toml_val

        # In src/etc/rust_analyzer_settings.json, we configure rust-analyzer to
        # pass RUSTC_BOOTSTRAP=1 to all cargo invocations because the standard
        # library uses unstable Cargo features. Without RUSTC_BOOTSTRAP,
        # rust-analyzer would fail to fetch workspace layout when the system's
        # default toolchain is not nightly.
        #
        # But that setting has the collateral effect of rust-analyzer also
        # passing RUSTC_BOOTSTRAP=1 to all x.py invocations too (the various
        # overrideCommand).
        #
        # Set a consistent RUSTC_BOOTSTRAP=1 here to prevent spurious rebuilds
        # of bootstrap when rust-analyzer x.py invocations are interleaved with
        # handwritten ones on the command line.
        env["RUSTC_BOOTSTRAP"] = "1"

        # If any of RUSTFLAGS or RUSTFLAGS_BOOTSTRAP are present and nonempty,
        # we allow arbitrary compiler flags in there, including unstable ones
        # such as `-Zthreads=8`.
        #
        # But if there aren't custom flags being passed to bootstrap, then we
        # cancel the RUSTC_BOOTSTRAP=1 from above by passing `-Zallow-features=`
        # to ensure unstable language or library features do not accidentally
        # get introduced into bootstrap over time. Distros rely on being able to
        # compile bootstrap with a variety of their toolchains, not necessarily
        # the same as Rust's CI uses.
        #
        # Trust: the allow-list names exactly the Trust std features bootstrap's
        # own dependency graph selects (`TRUST_BOOTSTRAP_STD_FEATURES`). Each is
        # requested only when the compiler's `-vV` reports a Trust std, so a
        # stock driver uses none of them, while an empty list fails a Trust
        # seed with E0725 (BOOTSTRAP-SEED-PROBE-ADMISSION-1).
        if env.get("RUSTFLAGS", "") or env.get("RUSTFLAGS_BOOTSTRAP", ""):
            # Preserve existing RUSTFLAGS.
            env.setdefault("RUSTFLAGS", "")
        else:
            env["RUSTFLAGS"] = "-Zallow-features=" + ",".join(TRUST_BOOTSTRAP_STD_FEATURES)

        if not os.path.isfile(self.cargo()):
            raise Exception(
                "no targo executable found at `{}`. "
                "Run `python3 scripts/create_local_genesis_stage0.py` first to "
                "create a Trust-named stage0 wrapper around your installed Rust "
                "toolchain (see README.md Build section).".format(self.cargo())
            )
        args = [self.cargo()]
        # Targo's two-lane policy: a targo new enough to have it REFUSES a bare
        # `targo build`, because that would mint an artifact carrying no proof
        # claim while looking like it might. Bootstrap builds compiler tooling,
        # which is unverified by definition, so `--unverified` is the honest
        # lane — and stating it explicitly is the point of the policy.
        #
        # Probed rather than assumed, so a seed targo predating the policy keeps
        # working: an unknown global flag would be a hard error there.
        if self.targo_supports_unverified_lane():
            args.append("--unverified")
        args += [
            "build",
            "--jobs=" + jobs,
            "--manifest-path",
            os.path.join(self.rust_root, "src/bootstrap/Cargo.toml"),
            "-Zroot-dir=" + self.rust_root,
        ]
        # verbose cargo output is very noisy, so only enable it with -vv
        args.extend("--verbose" for _ in range(self.verbose - 1))
        if self.verbose < 0:
            args.append("--quiet")

        target_features = []
        if self.get_toml("crt-static", build_section) == "true":
            target_features += ["+crt-static"]
        elif self.get_toml("crt-static", build_section) == "false":
            target_features += ["-crt-static"]
        if target_features:
            env["RUSTFLAGS"] += " -C target-feature=" + (",".join(target_features))
        target_linker = self.get_toml("linker", build_section)
        if target_linker is not None:
            env["RUSTFLAGS"] += " -C linker=" + target_linker
        # When changing this list, also update the corresponding list in `Builder::cargo`
        # in `src/bootstrap/src/core/builder.rs`.
        env["RUSTFLAGS"] += " -Wrust_2018_idioms -Wunused_lifetimes"
        if self.warnings == "default":
            deny_warnings = self.get_toml("deny-warnings", "rust") != "false"
        else:
            deny_warnings = self.warnings == "deny"
        if deny_warnings:
            env["CARGO_BUILD_WARNINGS"] = "deny"

        # Add RUSTFLAGS_BOOTSTRAP to RUSTFLAGS for bootstrap compilation.
        # Note that RUSTFLAGS_BOOTSTRAP should always be added to the end of
        # RUSTFLAGS, since that causes RUSTFLAGS_BOOTSTRAP to override RUSTFLAGS.
        if "RUSTFLAGS_BOOTSTRAP" in env:
            env["RUSTFLAGS"] += " " + env["RUSTFLAGS_BOOTSTRAP"]

        if "BOOTSTRAP_TRACING" in env:
            args.append("--features=tracing")

        if self.use_locked_deps:
            args.append("--locked")
        # Trust: the actual producer may neither update locks nor fetch. Native
        # Cargo resolves/downloads this request's sources before executing units;
        # online source preparation remains an explicit separate operation.
        args.append("--frozen")
        if self.get_toml("metrics", "build"):
            args.append("--features")
            args.append("build-metrics")
        if self.json_output:
            args.append("--message-format=json")
        if self.color == "always":
            args.append("--color=always")
        elif self.color == "never":
            args.append("--color=never")
        try:
            args += env["CARGOFLAGS"].split()
        except KeyError:
            pass

        return args

    def build_triple(self):
        """Build triple as in LLVM

        Note that `default_build_triple` is moderately expensive,
        so use `self.build` where possible.
        """
        config = self.get_toml("build")
        return config or default_build_triple(self.verbose)

    def is_git_repository(self, repo_path):
        return os.path.isdir(os.path.join(repo_path, ".git"))

    def get_latest_commit(self):
        repo_path = self.rust_root
        author_email = self.stage0_data.get("git_merge_commit_email")
        if not self.is_git_repository(repo_path):
            return "<commit>"
        cmd = [
            "git",
            "rev-list",
            "--author",
            author_email,
            "-n1",
            "HEAD",
        ]
        try:
            commit = subprocess.check_output(
                cmd, universal_newlines=True, cwd=repo_path
            ).strip()
            return commit or "<commit>"
        except subprocess.CalledProcessError:
            return "<commit>"

    def check_vendored_status(self):
        """Check that vendoring is configured properly"""
        # Keep this consistent with bootstrap's vendoring behavior, but keep the
        # recovery path Trust-local instead of pointing at upstream Rust hosts.
        if "SUDO_USER" in os.environ and not self.use_vendored_sources:
            if os.getuid() == 0:
                self.use_vendored_sources = True
                eprint("INFO: looks like you're trying to run this command as root")
                eprint("      and so in order to preserve your $HOME this will now")
                eprint("      use vendored sources by default.")

        cargo_dir = os.path.join(self.rust_root, ".cargo")
        if self.use_vendored_sources:
            vendor_dir = os.path.join(self.rust_root, "vendor")
            if not os.path.exists(vendor_dir):
                eprint(
                    "ERROR: vendoring required, but vendor directory does not exist."
                )
                eprint("       Run `x.py vendor` to initialize the vendor directory.")
                eprint(
                    "       Alternatively, build the repo-local Trust source package with:"
                )
                eprint("       ./x dist trust-source")
                eprint(
                    "       Then use the matching build/dist/rustc-*-src.tar.* artifact,"
                )
                eprint(
                    "       and place the vendor directory from that archive in the Trust root."
                )
                raise Exception("{} not found".format(vendor_dir))

            if not os.path.exists(cargo_dir):
                eprint("ERROR: vendoring required, but .cargo/config does not exist.")
                raise Exception("{} not found".format(cargo_dir))


_TOML_STRING_RE = r'"((?:[^"\\\n]|\\.)*)"|\'([^\'\n]*)\''


def _toml_top_level_include(config_toml):
    """The strings of a config's top-level `include = [...]`, in order ([] if none).

    A subset parser like get_toml_static: basic ("...", with the usual escapes) and
    literal ('...') strings in a one-line or multi-line array, read only above the
    first `[section]` header.
    """
    value = None
    for line in config_toml.splitlines():
        if value is None:
            stripped = line.strip()
            if stripped.startswith("["):
                return []
            match = re.match(r"^include\s*=\s*(.*)$", stripped)
            if match is None:
                continue
            value = match.group(1)
        else:
            value += "\n" + line
        # The array ends at the first `]` outside a string and a comment.
        bare = "\n".join(
            part.split("#", 1)[0]
            for part in re.sub(_TOML_STRING_RE, "", value).splitlines()
        )
        if "]" in bare:
            break
    if value is None:
        return []
    items = []
    # Trust: consume comments as tokens so quoted commentary is never a path;
    # matching complete strings first keeps '#' inside real filenames intact.
    for match in re.finditer(_TOML_STRING_RE + r"|#[^\n]*", value):
        basic, literal = match.group(1), match.group(2)
        if basic is not None:
            items.append(json.loads('"' + basic + '"'))
        elif literal is not None:
            items.append(literal)
    return items


def config_with_includes(config_toml, toml_path, chain=()):
    """`config_toml` followed by every file its `include` names, as config.rs merges them.

    Trust: the Rust loader (src/bootstrap/src/core/config/toml/mod.rs) merges each
    included file beneath the config that names it, but this script read the named file
    alone. A generated config that overrides a few keys and includes the checkout's
    bootstrap.toml (the pack cut's DDC and proof-build configs,
    scripts/mint_seed_support.py) then built bootstrap with settings x.py does not
    read: measured on the cut of dd6cd894cf (2026-10-22), the DDC build saw no
    `rust.deny-warnings = false`, denied bootstrap's ten warnings that the pinned-seed
    build had allowed reading that key from bootstrap.toml itself, and the cut stopped.

    get_toml returns the first match, so the precedence is the loader's when each
    included file follows the text that names it: the config's own keys first, the
    last include before an earlier one, and a file's own keys before its includes.
    Paths resolve against the including file's directory. A `[]` line before each
    included file puts its top-level keys back at the top level for get_toml_static.
    """
    real = os.path.realpath(toml_path)
    if real in chain:
        raise Exception(
            "cyclic config include: '{}' is included again".format(toml_path)
        )
    chain = chain + (real,)
    parent = os.path.dirname(real)
    for name in reversed(_toml_top_level_include(config_toml)):
        path = os.path.join(parent, name)
        with open(path, encoding="utf-8") as included:
            text = included.read()
        config_toml += os.linesep + "[]" + os.linesep + config_with_includes(
            text, path, chain
        )
    return config_toml


def parse_args(args):
    """Parse the command line arguments that the python script needs."""

    # Pass allow_abbrev=False to remove support for inexact matches (e.g.,
    # `--json` turning on `--json-output`). The argument list here is partial,
    # most flags are matched in the Rust bootstrap code. This prevents the
    # default ambiguity checks in argparse from functioning correctly.
    parser = argparse.ArgumentParser(add_help=False, allow_abbrev=False)
    parser.add_argument("-h", "--help", action="store_true")
    parser.add_argument("--config")
    parser.add_argument("--build-dir")
    parser.add_argument("--build")
    parser.add_argument("-j", "--jobs", type=int)
    parser.add_argument("--color", choices=["always", "never", "auto"])
    parser.add_argument("--clean", action="store_true")
    parser.add_argument("--json-output", action="store_true")
    parser.add_argument(
        "--warnings", choices=["deny", "warn", "default"], default="default"
    )
    group = parser.add_mutually_exclusive_group()
    group.add_argument("-v", "--verbose", action="count", default=0)
    # Note that we're storing the `--quiet` value in `verbose`. That way we don't need to thread
    # `self.quiet` throughout the code. That could be error prone, which could let some output
    # through that should have been suppressed.
    group.add_argument("-q", "--quiet", action="store_const", const=-1, dest="verbose")

    parsed, _ = parser.parse_known_args(args)
    return parsed


def parse_stage0_file(path):
    result = {}
    with open(path, "r", encoding="utf-8") as file:
        for line in file:
            line = line.strip()
            if line and not line.startswith("#"):
                key, value = line.split("=", 1)
                result[key.strip()] = value.strip()
    return result


def bootstrap(args):
    """Configure, fetch, build and run the initial bootstrap"""
    rust_root = os.path.abspath(os.path.join(__file__, "../../.."))

    if not os.path.exists(os.path.join(rust_root, ".git")) and os.path.exists(
        os.path.join(rust_root, ".github")
    ):
        eprint(
            "warn: Looks like you are trying to bootstrap Rust from a source that is neither a "
            "git clone nor distributed tarball.\nThis build may fail due to missing submodules "
            "unless you put them in place manually."
        )

    # Read from `--config` first, followed by `RUST_BOOTSTRAP_CONFIG`.
    # If neither is set, check `./bootstrap.toml`, then `bootstrap.toml` in the root directory.
    # If those are unavailable, fall back to `./config.toml`, then `config.toml` for
    # backward compatibility.
    toml_path = args.config or os.getenv("RUST_BOOTSTRAP_CONFIG")
    using_default_path = toml_path is None
    if using_default_path:
        toml_path = "bootstrap.toml"
        if not os.path.exists(toml_path):
            toml_path = os.path.join(rust_root, "bootstrap.toml")
            if not os.path.exists(toml_path):
                toml_path = "config.toml"
                if not os.path.exists(toml_path):
                    toml_path = os.path.join(rust_root, "config.toml")

    # Give a hard error if `--config` or `RUST_BOOTSTRAP_CONFIG` are set to a missing path,
    # but not if `bootstrap.toml` hasn't been created.
    if not using_default_path or os.path.exists(toml_path):
        with open(toml_path, encoding="utf-8") as config:
            config_toml = config.read()
        config_toml = config_with_includes(config_toml, toml_path)
    else:
        config_toml = ""

    profile = RustBuild.get_toml_static(config_toml, "profile")
    is_non_git_source = not os.path.exists(os.path.join(rust_root, ".git"))

    if profile is None and is_non_git_source:
        profile = "dist"

    if profile is not None:
        # Allows creating alias for profile names, allowing
        # profiles to be renamed while maintaining back compatibility
        # Keep in sync with `profile_aliases` in config.rs
        profile_aliases = {"user": "dist"}
        include_file = "bootstrap.{}.toml".format(
            profile_aliases.get(profile) or profile
        )
        include_dir = os.path.join(rust_root, "src", "bootstrap", "defaults")
        include_path = os.path.join(include_dir, include_file)

        if not os.path.exists(include_path):
            raise Exception(
                "Unrecognized config profile '{}'. Check src/bootstrap/defaults"
                " for available options.".format(profile)
            )

        # HACK: This works because `self.get_toml()` returns the first match it finds for a
        # specific key, so appending our defaults at the end allows the user to override them
        with open(include_path, encoding="utf-8") as included_toml:
            config_toml += os.linesep + included_toml.read()

    # Configure initial bootstrap
    build = RustBuild(config_toml, args)
    build.check_vendored_status()

    if not os.path.exists(build.build_dir):
        os.makedirs(os.path.realpath(build.build_dir))

    # Fetch/build the bootstrap
    build.download_toolchain()
    sys.stdout.flush()
    build.build_bootstrap()
    sys.stdout.flush()

    # Run the bootstrap
    args = [build.bootstrap_binary()]
    args.extend(sys.argv[1:])
    env = bootstrap_runtime_env(build.rustc())
    run(args, env=env, verbose=build.verbose, is_bootstrap=True)


def main():
    """Entry point for the bootstrap process"""
    start_time = time()

    # x.py help <cmd> ...
    if len(sys.argv) > 1 and sys.argv[1] == "help":
        sys.argv[1] = "-h"

    args = parse_args(sys.argv)

    # Root help (e.g., x.py --help) prints help from the saved file to save the time
    if len(sys.argv) == 1 or sys.argv[1] in ["-h", "--help"]:
        try:
            with open(
                os.path.join(os.path.dirname(__file__), "../etc/xhelp"),
                "r",
                encoding="utf-8",
            ) as f:
                # The file from bootstrap func already has newline.
                print(f.read(), end="")
                sys.exit(0)
        except Exception as error:
            eprint(
                f"ERROR: unable to run help: {error}\n",
                "x.py run generate-help may solve the problem.",
            )
            sys.exit(1)

    # If the user is asking for other helps, let them know that the whole download-and-build
    # process has to happen before anything is printed out.
    if args.help:
        eprint(
            "INFO: Downloading and building bootstrap before processing --help command.\n"
            "      See src/bootstrap/README.md for help with common commands."
        )

    exit_code = 0
    success_word = "successfully"
    try:
        bootstrap(args)
    except (SystemExit, KeyboardInterrupt) as error:
        if hasattr(error, "code") and isinstance(error.code, int):
            exit_code = error.code
        else:
            exit_code = 1
            eprint(error)
        success_word = "unsuccessfully"

    if not args.help:
        eprint(
            "Build completed",
            success_word,
            "in",
            format_build_time(time() - start_time),
        )

    sys.exit(exit_code)


if __name__ == "__main__":
    main()
