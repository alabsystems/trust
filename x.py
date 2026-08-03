#!/usr/bin/env python3
# Some systems don't have `python3` in their PATH. This isn't supported by x.py directly;
# they should use `x` or `x.ps1` instead.

# This file is only a "symlink" to bootstrap.py, all logic should go there.

# Parts of `bootstrap.py` use the `multiprocessing` module, so this entry point
# must use the normal `if __name__ == '__main__':` convention to avoid problems.
if __name__ == "__main__":
    import os
    import sys
    import warnings
    from inspect import cleandoc

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
            cmd = [sys.executable, script_py]
        else:
            return  # no checker in this tree; not a reason to refuse to build

        import signal
        import subprocess
        import tempfile

        fd, verdict_path = tempfile.mkstemp(prefix="trust-preflight-")
        os.close(fd)
        cmd += ["--for-build", "--verdict-file", verdict_path,
                "--deep" if sub in deep else "--deep-if-cached"]
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

    try:
        _trust_preflight(rust_dir, sys.argv[1:])
    except SystemExit:
        raise
    except KeyboardInterrupt:
        raise
    except Exception as _e:  # never let the guard itself break the build
        sys.stderr.write(
            "x.py: preflight hook error (%s: %s) -- continuing.\n"
            % (_e.__class__.__name__, _e)
        )

    # For the import below, have Python search in src/bootstrap first.
    sys.path.insert(0, os.path.join(rust_dir, "src", "bootstrap"))

    import bootstrap

    bootstrap.main()
