#!/usr/bin/env python3
# Some systems don't have `python3` in their PATH. This isn't supported by x.py directly;
# they should use `x` or `x.ps1` instead.

# This file is only a "symlink" to bootstrap.py, all logic should go there.

# Parts of `bootstrap.py` use the `multiprocessing` module, so this entry point
# must use the normal `if __name__ == '__main__':` convention to avoid problems.


def _trust_preflight_config_args(argv, invocation_cwd):
    """Translate bootstrap config selectors for the preflight subprocess."""
    import os

    config = None
    overrides = []
    i = 0
    while i < len(argv):
        arg = argv[i]
        if arg == "--":
            break
        if arg == "--config" and i + 1 < len(argv):
            config = argv[i + 1]
            i += 2
            continue
        if arg.startswith("--config="):
            config = arg.split("=", 1)[1]
        elif arg == "--set" and i + 1 < len(argv):
            overrides.append(argv[i + 1])
            i += 2
            continue
        elif arg.startswith("--set="):
            overrides.append(arg.split("=", 1)[1])
        i += 1

    forwarded = ["--bootstrap-cwd", invocation_cwd]
    if config is not None:
        if not os.path.isabs(config):
            config = os.path.normpath(os.path.join(invocation_cwd, config))
        forwarded.extend(["--bootstrap-toml", config])
    for override in overrides:
        forwarded.extend(["--set", override])
    return forwarded


def _trust_preflight_tool_args(argv, rust_dir):
    """Only the exact standalone frontend recipe has a deferred source scope.

    Unknown flags, compiler targets, mixed targets and install/dist remain full.
    This is not a general preflight suppression switch.
    """
    import os
    import re
    # Trust: a normal full preparation must retain ordinary full preflight,
    # even when it requests exactly this tool. A present but invalid deferred
    # record is still sent to the validator and refused, never ignored.
    marker = os.path.join(rust_dir, "build", "tool-source-preparation", "targo-build-tool.json")
    if not os.path.lexists(marker):
        return []
    if (len(argv) == 6 and argv[:3] == ["build", "--stage", "1"]
            and argv[3] == "-j" and re.fullmatch(r"[1-9][0-9]*", argv[4])
            and argv[5] == "targo-build-tool"):
        return ["--selected-tool", "targo-build-tool"]
    return []


# Trust: the obligatory source-manifest census needs stdlib tomllib. Select its
# interpreter before preflight, seed extraction or acquisition of the build lease.
def _trust_ensure_python():
    import os
    import sys

    guard = "TRUST_XPY_PYTHON_REEXEC"
    if sys.version_info >= (3, 11):
        try:
            import tomllib
        except ImportError:
            pass
        else:
            os.environ.pop(guard, None)
            return
    message = "x.py: Trust bootstrap requires Python 3.11 or newer with tomllib; install one and retry."
    if os.environ.get(guard) == "1" or sys.version_info < (3, 5):
        raise SystemExit(message)

    import shutil
    import subprocess

    flags = []
    for name, option in (("dont_write_bytecode", "B"), ("isolated", "I"), ("no_site", "S"),
                         ("ignore_environment", "E"), ("no_user_site", "s"), ("optimize", "O"),
                         ("debug", "d"), ("verbose", "v"), ("bytes_warning", "b"), ("quiet", "q")):
        count = getattr(sys.flags, name, 0)
        if count:
            flags.append("-" + option * count)
    if getattr(sys.stdout, "write_through", False):
        flags.append("-u")
    for option in sys.warnoptions:
        flags.extend(["-W", option])
    for name, value in getattr(sys, "_xoptions", {}).items():
        flags.extend(["-X", name if value is True else "%s=%s" % (name, value)])

    candidates = [(name, []) for name in ("python3.14", "python3.13", "python3.12", "python3.11",
                                        "python3", "python")]
    if os.name == "nt":
        candidates.append(("py", ["-3"]))
    for name, prefix in candidates:
        path = shutil.which(name)
        if path is None:
            continue
        try:
            probe = subprocess.run([path] + prefix + ["-I", "-S", "-c",
                                   "import sys, tomllib; raise SystemExit(sys.version_info < (3, 11))"],
                                   stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
                                   stderr=subprocess.DEVNULL, timeout=5)
            if probe.returncode == 0:
                os.environ[guard] = "1"
                os.execv(path, [path] + prefix + flags + sys.argv)
        except (OSError, subprocess.TimeoutExpired):
            os.environ.pop(guard, None)
    raise SystemExit(message)

def _trust_namespace_guard(root, descriptor):
    """Cold-bootstrap syscall compatibility for the inherited facade FD only."""
    import fcntl
    import os
    import stat
    import time

    fd = int(descriptor)
    if fd < 3:
        raise ValueError("invalid namespace guard descriptor")
    path = os.path.join(os.path.realpath(root), ".trust-build-lock.guard")

    def validate():
        opened, named = os.fstat(fd), os.lstat(path)
        if (not stat.S_ISREG(opened.st_mode) or not stat.S_ISREG(named.st_mode)
                or (opened.st_dev, opened.st_ino) != (named.st_dev, named.st_ino)
                or opened.st_nlink != 1 or named.st_nlink != 1
                or opened.st_uid != os.geteuid() or opened.st_mode & 0o022
                or opened.st_size != 0):
            raise ValueError("namespace guard must be the persistent owned regular inode")

    validate()
    deadline = time.monotonic() + 30
    while True:
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
            break
        except BlockingIOError:
            if time.monotonic() >= deadline:
                raise TimeoutError("build namespace guard is busy")
            time.sleep(0.01)
    validate()
    # No LOCK_UN: the facade retains this same open description after exit.


if __name__ == "__main__":
    import os
    import sys
    import warnings
    from inspect import cleandoc

    if sys.argv[1:2] == ["--trust-build-lock-guard"]:
        try:
            if len(sys.argv) != 4:
                raise ValueError("expected root and inherited descriptor")
            _trust_namespace_guard(sys.argv[2], sys.argv[3])
            print("trust-build-namespace-held-v1")
        except Exception as error:
            sys.stderr.write("x.py: build namespace guard: %s\n" % error)
            sys.exit(2)
        sys.exit(0)

    major = sys.version_info.major
    minor = sys.version_info.minor

    # If this is python2, check if python3 is available and re-execute with that
    # interpreter. Only python3 allows downloading CI LLVM.
    #
    # This matters if someone's system `python` is python2.
    if major < 3:
        try:
            os.execvp("py", ["py", "-3"] + sys.argv)
        except OSError:
            try:
                os.execvp("python3", ["python3"] + sys.argv)
            except OSError:
                # Python 3 isn't available, fall back to python 2
                pass

    # Trust: native bootstrap's dependency census must not inherit an old python3.
    _trust_ensure_python()

    # soft deprecation of old python versions
    skip_check = os.environ.get("RUST_IGNORE_OLD_PYTHON") == "1"
    if not skip_check and (major < 3 or (major == 3 and minor < 6)):
        msg = cleandoc(
            """
            Using python {}.{} but >= 3.6 is recommended. Your python version
            should continue to work for the near future, but this will
            eventually change. If python >= 3.6 is not available on your system,
            please file an issue to help us understand timelines.

            This message can be suppressed by setting `RUST_IGNORE_OLD_PYTHON=1`
        """.format(major, minor)
        )
        warnings.warn(msg, stacklevel=1)

    rust_dir = os.path.dirname(os.path.abspath(__file__))

    # PREFLIGHT GATE (tools/preflight.sh). This file is the one choke point every
    # entry point funnels through -- `x`, `x.ps1` and `python3 x.py` alike -- which
    # is why the check lives here and not in a git hook (unversioned, absent on a
    # fresh clone) or in bootstrap itself (it must COMPILE before it can warn, and
    # it is the very artifact under audit: the `tools` allowlist is bootstrap's own
    # config).
    #
    # It exists because six consecutive stage2 failures in one day cost ~4 hours,
    # and five were diagnosable in seconds: stale lockfiles fixed one per attempt,
    # drifted submodules whose stale APIs read as source bugs, and -- worst -- a
    # build that SUCCEEDED while silently shipping no `ty`/`ay`/`clean`, i.e. a
    # compiler that cannot verify anything, reported as success.
    #
    # FAIL-SAFE, deliberately: any problem reaching the checker itself (missing,
    # unreadable, crashing, wrong interpreter) lets the build proceed. A checker
    # that can brick x.py is worse than no checker -- the first time it does, it
    # gets disabled permanently and takes its real findings with it.
    #
    # A build is stopped ONLY by the checker's own explicit VERDICT, never by a
    # bare exit code. That distinction is not theoretical: while testing this
    # hook, a deliberately-crashed preflight.py exited non-zero and the first
    # version of this code reported "blocking problems" -- claiming a finding
    # that did not exist. Reporting a broken checker as a real finding is how
    # people learn to reach for the override, and then it is off for the run
    # that finds something true. `TRUST_SKIP_PREFLIGHT=1` overrides.
    #
    # The verdict travels in a file (`--verdict-file`), written only after a
    # report has actually been emitted, so a crash leaves NO verdict at all.
    # That also lets the checker's output stream straight to the terminal
    # instead of being buffered and replayed at the end -- during a deep run
    # a silent 20s pause reads as a hang.
    def _trust_preflight(rust_dir, argv):
        if os.environ.get("TRUST_SKIP_PREFLIGHT") == "1":
            return
        # bootstrap's own test suite shells out to a nested x.py; the outer
        # invocation already paid for this.
        if os.environ.get("TRUST_PREFLIGHT_ACTIVE") == "1":
            return
        if sys.version_info < (3, 5):
            return  # no subprocess.run/timeout; the python2 fallback stays working

        # Subcommands that actually compile something, with clap's short
        # aliases (`x b`, `x c`, `x d`, `x t`, `x r`). `fmt`, `clean`, `setup`
        # and `vendor` never pay for a bad tree, and `--help` stays instant.
        buildish = frozenset((
            "build", "b", "check", "c", "clippy", "fix", "doc", "d",
            "test", "t", "miri", "bench", "run", "r", "dist", "install",
        ))
        # TIERING. Fast tier ~2s, deep (resolver-backed) tier ~20s and it needs
        # the network. `dist`/`install` produce artifacts other machines
        # consume and cost tens of minutes, so they alone pay for a cold deep
        # run. Everything else gets the fast tier plus any deep verdict already
        # cached and still valid, which costs nothing and means an ordinary
        # `x build` still refuses on skew once the cache is warm. A 20s tax on
        # the edit/`x check` loop would simply get TRUST_SKIP_PREFLIGHT=1
        # exported in a shell profile, and a disabled checker protects nothing.
        deep = frozenset(("dist", "install"))

        # Scan for the subcommand rather than trusting argv[1]: `x.py --stage 1
        # build` is ordinary usage and argv[1] is `--stage` there.
        sub = None
        for arg in argv:
            if arg == "--":
                break
            if arg in buildish:
                sub = arg
                break
        if sub is None:
            return

        script_sh = os.path.join(rust_dir, "tools", "preflight.sh")
        script_py = os.path.join(rust_dir, "tools", "preflight.py")
        if os.name != "nt" and os.path.isfile(script_sh) and os.path.exists("/bin/sh"):
            cmd = ["/bin/sh", script_sh]
        elif os.path.isfile(script_py):
            # Trust: preflight needs only stdlib; preserve startup isolation.
            cmd = [sys.executable, "-I", "-S", script_py]
        else:
            return  # no checker in this tree; not a reason to refuse to build

        import signal
        import subprocess
        import tempfile

        fd, verdict_path = tempfile.mkstemp(prefix="trust-preflight-")
        os.close(fd)
        cmd += ["--for-build", "--verdict-file", verdict_path,
                "--deep" if sub in deep else "--deep-if-cached"]
        cmd += _trust_preflight_config_args(argv, os.getcwd())
        cmd += _trust_preflight_tool_args(argv, rust_dir)
        env = dict(os.environ)
        env["TRUST_PREFLIGHT_ACTIVE"] = "1"

        # Own process group, so a checker that wedges can be reaped WHOLE.
        # Killing just the direct child leaves grandchildren holding the
        # terminal, and a "preflight timed out, continuing" message followed by
        # a silent hang is indistinguishable from the bug it is reporting.
        def _reap(proc):
            try:
                if os.name != "nt":
                    os.killpg(proc.pid, signal.SIGKILL)
                else:
                    proc.kill()
            except Exception:
                pass
            try:
                proc.wait(timeout=10)
            except Exception:
                pass

        try:
            try:
                proc = subprocess.Popen(
                    cmd, cwd=rust_dir, env=env, start_new_session=(os.name != "nt")
                )
            except Exception as _e:
                sys.stderr.write(
                    "x.py: preflight did not run (%s: %s) -- continuing.\n"
                    % (_e.__class__.__name__, _e)
                )
                return
            try:
                rc = proc.wait(timeout=(900 if sub in deep else 300))
            except BaseException as _e:  # TimeoutExpired, KeyboardInterrupt, ...
                _reap(proc)
                if isinstance(_e, KeyboardInterrupt):
                    raise
                sys.stderr.write(
                    "x.py: preflight did not run (%s: %s) -- continuing.\n"
                    % (_e.__class__.__name__, _e)
                )
                return
            try:
                with open(verdict_path) as _fh:
                    verdict = _fh.read().strip()
            except OSError:
                verdict = ""
        finally:
            try:
                os.unlink(verdict_path)
            except OSError:
                pass

        if verdict == "BLOCKED":
            sys.stderr.write(
                "\nx.py: preflight found blocking problems; refusing to start a build.\n"
                "      Each item above prints its own fix command.\n"
                "      Override with TRUST_SKIP_PREFLIGHT=1 if you know better.\n"
            )
            sys.exit(1)
        if verdict != "CLEAR":
            # No verdict at all: the checker broke, hung, or never got that far.
            # That is a statement about the CHECKER, not about the tree.
            sys.stderr.write(
                "x.py: preflight did not reach a verdict (exit %s) -- continuing.\n"
                "      This is NOT a finding about your tree; the checker itself failed.\n"
                % rc
            )

    # Trust: cold Bootstrap construction must share the same native build-tree
    # manager as the compiled child and measurements. Ownership, recovery,
    # waiting and writer discovery are implemented only by the native manager.
    _lock_token = [None]
    _lock_frontend = [None]

    def _trust_build_lock_frontend(rust_dir):
        import shutil
        import subprocess

        if _lock_frontend[0] is not None:
            return _lock_frontend[0]
        candidates = []
        selected_manager = os.environ.get("TRUST_BUILD_TREE_MANAGER_TARGO")
        if selected_manager is not None:
            if (not os.path.isabs(selected_manager)
                    or os.path.realpath(selected_manager) != selected_manager
                    or not os.path.isfile(selected_manager)
                    or not os.access(selected_manager, os.X_OK)):
                raise RuntimeError("explicit build-tree manager must be a physical executable path")
            candidates.append([selected_manager, "trust", "repo", "lock"])
        else:
            # Trust: this tree's own Bootstrap first: the one bootstrap.py
            # builds under the lease, then the one scripts/build-tree-manager.sh
            # builds for a tree that has none yet (FRESH-TREE-LOCK-FRONTEND-1).
            # That script compiles the same Bootstrap source with an installed
            # Trust Targo, before any x.py run and outside build/, so a fresh
            # tree gets its native owner without x.py constructing anything.
            for executable in (
                os.path.join(rust_dir, "build", "bootstrap", "debug", "bootstrap"),
                os.path.join(rust_dir, "build", "bootstrap", "release", "bootstrap"),
                os.path.join(rust_dir, "build-tree-manager.noindex", "debug", "bootstrap"),
            ):
                if os.path.isfile(executable) and os.access(executable, os.X_OK):
                    candidates.append([executable, "--trust-build-tree-lock"])
            targo = shutil.which("targo")
            if targo is not None:
                candidates.append([targo, "trust", "repo", "lock"])
        for command in candidates:
            try:
                probe = subprocess.run(
                    command + ["--protocol"], cwd=rust_dir, timeout=10,
                    stdout=subprocess.PIPE, stderr=subprocess.PIPE, close_fds=False,
                )
            except (OSError, subprocess.TimeoutExpired):
                continue
            if probe.returncode == 0 and probe.stdout == b"trust-build-tree-manager-v2\n":
                _lock_frontend[0] = command
                return command
        if selected_manager is not None:
            raise RuntimeError("explicit build-tree manager refused protocol v2; no fallback")
        # Trust: current Targo embeds this native owner before project/sidecar
        # resolution, including for a fresh source tree with no Bootstrap yet.
        # Never build a second administrative helper from a Python fallback:
        # x.py refuses here, before any build-tree write, and names the
        # explicit step that builds this tree's own Bootstrap instead.
        raise RuntimeError(
            "native build-tree manager v2 is unavailable; use current Targo or current Bootstrap "
            "(a tree with no Bootstrap yet: run scripts/build-tree-manager.sh, which builds this "
            "tree's own Bootstrap with the installed Targo outside build/)"
        )

    def _trust_build_lock_acquire(rust_dir, argv):
        import subprocess

        # Every real request can construct Bootstrap before Rust parses its
        # command kind. Protect that construction, including a bare default
        # build; the compiled child classifies commands using its typed parser.
        if argv in (["--help"], ["-h"], ["--version"], ["-V"]):
            return

        frontend = _trust_build_lock_frontend(rust_dir)
        if os.environ.get("TRUST_BUILD_LOCK_BREAK"):
            raise RuntimeError(
                "build-tree recovery requires explicit `targo trust repo lock break --reason TEXT`"
            )

        # A nested x.py (bootstrap's own test suite shells out to one) inherits
        # this and must not block on its own parent. The lock verifies the token
        # against what is actually on disk rather than believing the variable.
        inherited_token = os.environ.get("TRUST_BUILD_LOCK_TOKEN")
        cmd = frontend + [
            "acquire", "--repo-root", rust_dir, "--kind", "build",
            "--purpose", "x.py %s" % " ".join(argv[:6]),
            "--pid", str(os.getpid()),
            "--wait", os.environ.get("TRUST_BUILD_LOCK_WAIT", "0"),
            "--contract", "a build is rewriting stage1/; do not measure against it",
        ]
        proc = None
        try:
            # stderr is inherited so the refusal streams to the terminal as it is
            # produced; stdout carries only the token.
            proc = subprocess.Popen(cmd, cwd=rust_dir, stdout=subprocess.PIPE, close_fds=False)
            out, _ = proc.communicate(timeout=86400)
            rc = proc.returncode
        except Exception as _e:
            if proc is not None:
                proc.kill()
                proc.wait()
            sys.stderr.write(
                "x.py: build lock did not run (%s: %s) -- refusing unlocked build.\n"
                % (_e.__class__.__name__, _e)
            )
            sys.exit(1)

        if rc == 3:
            sys.stderr.write(
                "x.py: refusing to build while the build tree is held (see above).\n"
            )
            sys.exit(1)
        token = (out or b"").decode("utf-8", "replace").strip()
        if rc != 0 or not token:
            sys.stderr.write(
                "x.py: build lock failed (exit %s) -- refusing unlocked build.\n" % rc
            )
            sys.exit(1)
        # Trust: a validated inherited token remains the parent's lock. Only a
        # fresh acquisition owns a release; retain existing ownership on reentry.
        if token != inherited_token:
            _lock_token[0] = token
        os.environ["TRUST_BUILD_LOCK_TOKEN"] = token
        if token != inherited_token:
            _trust_incremental_reclaim(rust_dir, frontend)

    def _trust_incremental_reclaim(rust_dir, frontend):
        # Trust: keep the former acquisition hook as a thin native-command
        # caller. Selection, thresholds, locks and deletion live in Rust.
        # Redirect all standard streams: token delivery must not wait for the
        # background deletion's inherited output pipes to close.
        import glob
        import subprocess

        if not glob.glob(os.path.join(rust_dir, "crates", "target*", "debug")):
            return
        try:
            protocol = subprocess.run(
                frontend + ["reclaim-incremental", "--protocol"],
                cwd=rust_dir,
                stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                close_fds=False, timeout=30,
            )
            if protocol.returncode != 0 or protocol.stdout.strip() != b"trust-incremental-reclamation-v1":
                return
            flags = os.O_WRONLY | os.O_APPEND | os.O_CREAT | getattr(os, "O_NOFOLLOW", 0)
            descriptor = os.open(os.path.join(rust_dir, ".trust-build-lock.reclaim.log"), flags, 0o600)
            with os.fdopen(descriptor, "ab") as log:
                subprocess.Popen(
                    frontend + ["reclaim-incremental", "--repo-root", rust_dir, "--apply", "--quiet"],
                    cwd=rust_dir, stdin=subprocess.DEVNULL, stdout=log, stderr=subprocess.STDOUT,
                    start_new_session=True, close_fds=False,
                )
        except (OSError, subprocess.SubprocessError):
            # Optional cache maintenance never releases or bypasses the actual
            # acquired build-tree holder. An older native frontend may lack it.
            pass

    def _trust_build_lock_release(*_a):
        token = _lock_token[0]
        if not token:
            return
        _lock_token[0] = None
        import subprocess

        try:
            subprocess.run(
                _lock_frontend[0] + ["release", token, "--repo-root", rust_dir],
                cwd=rust_dir, timeout=60,
                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, close_fds=False,
            )
        except Exception:
            pass  # a leaked lock is reclaimable by pid; a crash here is not

    # Trust: BUILD-TREE PROVENANCE STAMP (read by scripts/promote-toolchain.sh).
    #
    # WHY. A compiler binary's self-reported revision -- `CFG_VERSION`, which
    # `trustc --version` prints and which the sealing script used to derive a
    # seal's WHOLE identity from -- is `git rev-parse HEAD` at build time and
    # NOTHING ELSE. Bootstrap's `GitInfo::new` (src/bootstrap/src/utils/
    # channel.rs) never asks whether the working tree was clean at that commit,
    # so an artifact built from a tree carrying uncommitted work is stamped with
    # the commit the work was not yet in. That is the NORMAL state of an active
    # compiler checkout, not an exception. (That holds for stage 2, which is what
    # promote seals. A dev stage-1 build names its sources instead, uncommitted
    # work included: src/bootstrap/src/utils/trust_source_identity.rs, TB1.)
    #
    # MEASURED, 2026-08-31. `~/toolchains/trust-3ae9948d` reports commit
    # `3ae9948d1f3f...`; `945a8fbff5` (the elision-prefix soundness fix) is NOT
    # an ancestor of it; and its `librustc_driver` contains that fix's
    # `span_warn` text verbatim, which `git log -S` places at `945a8fbff5` and
    # nowhere earlier. It was built from a tree that already carried the patch,
    # hours before the patch was committed. Every ancestry-based blast-radius
    # answer over that seal was therefore wrong, in the direction of claiming a
    # fix was ABSENT when it was present -- and the same hole fails the other
    # way, which is the dangerous one: a seal whose HEAD contains a fix proves
    # nothing if the tree had it stashed, reverted, or not yet rebuilt.
    #
    # WHAT THIS FIXES. Promotion runs AFTER the build, so it can never
    # retroactively observe the build tree's state -- by then the tree has moved
    # on, and a tree that is clean at seal time is equally consistent with a
    # clean build and with a dirty build whose diff was stashed. Only the build
    # itself is in a position to say. This records, at build START, the facts
    # promote cannot reconstruct: HEAD, whether the tree was dirty, a digest of
    # the actual uncommitted diff, and the submodule pins. It re-reads the same
    # facts at build END, so a tree edited DURING a 90-minute build is reported
    # rather than silently averaged.
    #
    # WHY HERE AND NOT IN BOOTSTRAP. `x.py` is the choke point every entry point
    # funnels through, it already carries two Trust blocks on this exact
    # discipline, and it is PYTHON -- so this cannot destabilise a stage2 build
    # the way an edit to bootstrap's Rust would. `GitInfo` is also merged from
    # upstream constantly; this file's merge surface is one more hunk in a
    # region that already has two.
    #
    # SCOPED TO BUILDS. Only subcommands that can produce a stage2 pay for it
    # (`git status` is ~1.4s in this repo, ~3.2s counting untracked files); a
    # `check`/`test`/`fmt` run stamps nothing, because it seals nothing.
    #
    # Trust: v2 records explicit recursive scope. Census failure leaves an
    # incomplete record; inability to invalidate an old completed record stops
    # the build, because otherwise new output could inherit stale provenance.
    _prov = {"owner": None}

    def _trust_build_provenance_stamp(rust_dir, argv):
        # Trust: only build-producing commands own a record. Invalidate a prior
        # completed record before any fallible census; an unrecorded new build
        # must never inherit its predecessor's source authority.
        buildish = frozenset(("build", "b", "dist", "install"))
        selected = False
        for argument in argv:
            if argument == "--":
                break
            if argument in buildish:
                selected = True
                break
        if not selected or os.environ.get("TRUST_PREFLIGHT_ACTIVE") == "1":
            return
        try:
            from pathlib import Path

            # The record writer lives in this checkout's scripts/ package. A plain
            # `python x.py` finds it through sys.path[0] (x.py's directory); an
            # isolated interpreter (`python -I`, as scripts/mint_and_prove_seed.sh
            # runs x.py) puts no script directory on sys.path, so name the
            # checkout explicitly, as the `import bootstrap` below does for
            # src/bootstrap. Measured 2026-10-09: the first real mint stopped here
            # with "No module named 'scripts'".
            if rust_dir not in sys.path:
                sys.path.insert(0, rust_dir)
            from scripts.lib.trust_build_provenance import BuildStamp

            directory = os.environ.get("TRUST_BUILD_PROVENANCE_DIR") or os.path.join(
                rust_dir, "build"
            )
            owner = BuildStamp(Path(rust_dir), Path(directory), list(argv))
        except Exception as error:
            raise SystemExit(
                "x.py: cannot invalidate the previous build provenance record; "
                "refusing to build with possible stale authority: %s" % error
            )
        _prov["owner"] = owner
        fields = owner.start()
        if fields["tree_state"] == "dirty":
            sys.stderr.write(
                "x.py: NOTE -- building from a DIRTY recursive source tree at %s.\n"
                "      %s tracked + %s untracked Git-status entries across repositories.\n"
                "      The build stamp records this as dirty, never clean.\n"
                % (fields["head_short"], fields["dirty_tracked"], fields["dirty_untracked"])
            )

    def _trust_build_provenance_finish(status="unknown"):
        owner = _prov["owner"]
        if owner is not None:
            try:
                owner.finish(status)
            except Exception:
                # The atomic start-only record stays incomplete on failure.
                # It cannot become completed clean evidence by truncation.
                pass

    try:
        _trust_build_lock_acquire(rust_dir, sys.argv[1:])
    except SystemExit:
        raise
    except KeyboardInterrupt:
        raise
    except Exception as _e:
        sys.stderr.write(
            "x.py: build lock hook error (%s: %s) -- refusing unlocked build.\n"
            % (_e.__class__.__name__, _e)
        )
        sys.exit(1)

    try:
        _trust_preflight(rust_dir, sys.argv[1:])
    except SystemExit:
        _trust_build_lock_release()
        raise
    except KeyboardInterrupt:
        _trust_build_lock_release()
        raise
    except Exception as _e:  # never let the guard itself break the build
        sys.stderr.write(
            "x.py: preflight hook error (%s: %s) -- continuing.\n"
            % (_e.__class__.__name__, _e)
        )

    # Trust: stamp AFTER preflight, so a build refused before it starts leaves no
    # record claiming to describe one.
    try:
        _trust_build_provenance_stamp(rust_dir, sys.argv[1:])
    except SystemExit:
        _trust_build_lock_release()
        raise
    except Exception as _e:  # incomplete evidence cannot qualify a later seal
        sys.stderr.write(
            "x.py: build provenance stamp error (%s: %s) -- continuing WITHOUT a\n"
            "      usable provenance record. A seal made from this build is\n"
            "      UNVERIFIED-PROVENANCE.\n" % (_e.__class__.__name__, _e)
        )

    # Trust: release on every path out. SIGTERM does NOT run `finally` or atexit
    # handlers -- the default action terminates the process -- so it needs an
    # explicit handler. SIGINT arrives as KeyboardInterrupt and is covered by the
    # `finally`; atexit is the backstop for an exit path neither of them sees.
    # A lock that survives its holder is reclaimable by pid, so none of this is
    # load-bearing for correctness -- it is what stops the next lane having to
    # read a stale-lock banner to find that out.
    import atexit
    import signal

    atexit.register(_trust_build_lock_release)
    # Backstop only: if an exit path neither the `finally` nor the signal handler
    # sees gets there first, the record still closes -- as `interrupted`, never as
    # a success it did not observe.
    atexit.register(lambda: _trust_build_provenance_finish("interrupted"))
    for _sig in ("SIGTERM", "SIGHUP"):
        _num = getattr(signal, _sig, None)
        if _num is None:
            continue
        try:
            signal.signal(_num, lambda s, f: (_trust_build_provenance_finish("signal-%d" % s),
                                              _trust_build_lock_release(),
                                              sys.exit(128 + s)))
        except (ValueError, OSError, RuntimeError):
            pass  # not the main thread, or the platform disallows it

    # For the import below, have Python search in src/bootstrap first.
    sys.path.insert(0, os.path.join(rust_dir, "src", "bootstrap"))

    import bootstrap

    try:
        bootstrap.main()
    except SystemExit as _e:
        # `--help` and friends leave through SystemExit(0). That is a successful
        # run that built nothing, not a failure -- recording it as `failed` would
        # teach promote to distrust a record that is simply uninteresting.
        _code = _e.code
        _trust_build_provenance_finish(
            "ok" if _code in (0, None) else "exit-%s" % _code
        )
        raise
    except BaseException:
        _trust_build_provenance_finish("failed")
        raise
    else:
        _trust_build_provenance_finish("ok")
    finally:
        _trust_build_lock_release()
