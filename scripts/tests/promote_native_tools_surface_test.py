#!/usr/bin/env python3
"""Inert shell-boundary controls, not SDK runtime qualification.

Subjects of scripts/promote-toolchain.sh, each run against shell fixtures
in a temporary directory (no compiler, no admission, no channel):

  * NativeSurfaceTests: the paired native-tool surface of a Darwin host.
  * OneRefusalBeforeAnyGate: without TRUST_TOOLCHAIN_SERIAL_COMMAND, or with one
    that is not the executor, promotion and --gate-only stop ONCE, before any
    gate, in words that name the variable and how to build what it names.
    Until 2026-11-12 every UI-gate row printed FAIL and the run ended "FAILS
    this tree's named UI tests ... Fix the compiler" (measured on aarch64
    Linux, on a stage2 of 6762badf3c whose compiler was fine).
  * AFailRowSaysWhatItsCommandPrinted: each of those rows read `got exit 1: `
    with nothing after the colon, because the reason was the command's first
    line beginning `error` and it had none. A FAIL row always shows what its
    command printed.
  * AQuotedLineKeepsItsReason: the three functions that do the quoting, alone.
    A long line keeps its end (a loader's line opens with the program's whole
    path), a file grep would call binary is still quoted, and a UTF-8 locale
    adds no warning of an awk's own to what is quoted.
  * AFileThatCannotBeRunSaysWhy: a file the compiler wrote and this run may not
    execute is not "no executable": a TMPDIR mounted noexec is not the compiler's.
  * AScratchDirectoryThatMayNotRunAProgramIsOneRefusal: and such a TMPDIR, or
    one that is not there, is one refusal before any gate, not rows marked FAIL.
  * AnExecutorRefusalIsNotAVerdict, AProgramTheOsWillNotStartIsItsOwnFailure:
    a row the executor refused to start is NOT RUN, and a program the OS could
    not start is that program's FAIL.

The long suite is scripts/tests/promote_toolchain_test.sh (two minutes and more,
run by scripts/check_bootstrap_script_tests.sh). These classes are
here because the landing gate selects this module for a change to the script,
and that suite stopped at its first case from 2026-11-07 to 2026-11-12 with no
gate running it.
"""
from pathlib import Path
import locale
import os
import re
import subprocess
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / 'promote-toolchain.sh'
FUNCTION = re.search(r'(?ms)^native_linker_surface\(\) \{\n.*?^\}', SCRIPT.read_text()).group()


class NativeSurfaceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='inert native surface ')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / 'bin').mkdir()
        self.compiler('host: aarch64-apple-darwin\\n')

    def compiler(self, output):
        p = self.root / 'bin/trustc'
        p.write_text("#!/bin/sh\nprintf '" + output + "'\n")
        p.chmod(0o755)

    def helpers(self):
        for name in ('rust-lld', 'dsymutil'):
            p = self.root / 'bin' / name
            p.write_text('#!/bin/sh\n# Inert startup fixture only.\nexit 0\n')
            p.chmod(0o755)

    def run_surface(self):
        return subprocess.run(['/bin/bash','-c',
            'set -euo pipefail\ndie(){ printf "%s\\n" "$*" >&2; exit 1; }\n' +
            FUNCTION + '\nnative_linker_surface "$1" fixture\n','fixture',str(self.root)],
            text=True,capture_output=True)

    def test_a_darwin_sdk_with_neither_helper_is_recorded_not_refused(self):
        # Until 2026-11-14 this refused ("lacks paired"), which stopped every
        # macOS seal: nothing produces the tools (DARWIN-NATIVE-TOOLS-PRODUCER-1).
        # The line says nothing was checked; it never reads as a pass.
        r=self.run_surface();self.assertEqual(r.returncode,0,r.stderr)
        self.assertIn('    RECORDED  fixture publishes no paired bin/rust-lld and bin/dsymutil',r.stderr)
        self.assertIn('Not checked, not passed (DARWIN-NATIVE-TOOLS-PRODUCER-1).',r.stderr)
        self.assertNotIn('lacks paired',r.stderr)

    def test_a_complete_surface_records_nothing(self):
        self.helpers();r=self.run_surface();self.assertEqual(r.returncode,0);self.assertNotIn('RECORDED',r.stderr)

    def test_dsymutil_without_rust_lld_is_refused(self):
        # Nothing produces dsymutil, so a dsymutil with no linker is a broken producer.
        self.helpers();(self.root/'bin/rust-lld').unlink()
        r=self.run_surface();self.assertNotEqual(r.returncode,0)
        self.assertIn('lacks paired',r.stderr);self.assertNotIn('RECORDED',r.stderr)

    def test_rust_lld_without_dsymutil_is_refused(self):
        self.helpers();(self.root/'bin/dsymutil').unlink()
        r=self.run_surface();self.assertNotEqual(r.returncode,0,r.stderr)
        self.assertIn('lacks paired',r.stderr)
        self.assertNotIn('RECORDED',r.stderr)

    def test_rust_lld_alone_that_cannot_start_is_refused(self):
        self.helpers();(self.root/'bin/dsymutil').unlink()
        (self.root/'bin/rust-lld').write_text('#!/bin/sh\nexit 1\n')
        r=self.run_surface();self.assertNotEqual(r.returncode,0);self.assertIn('lacks paired',r.stderr)
        self.assertNotIn('RECORDED',r.stderr)

    def test_a_dangling_helper_link_is_refused(self):
        # A link is an entry: the SDK names a tool it does not carry.
        (self.root/'bin/rust-lld').symlink_to(self.root/'nowhere')
        r=self.run_surface();self.assertNotEqual(r.returncode,0)
        self.assertIn('lacks paired',r.stderr);self.assertNotIn('RECORDED',r.stderr)

    def test_a_helper_that_cannot_start_is_refused(self):
        self.helpers();(self.root/'bin/rust-lld').write_text('#!/bin/sh\nexit 1\n')
        r=self.run_surface();self.assertNotEqual(r.returncode,0);self.assertIn('paired rust-lld cannot start',r.stderr)

    def test_complete_regular_surface_can_start(self):
        self.helpers();self.assertEqual(self.run_surface().returncode,0)

    def test_external_helper_symlink_is_not_paired(self):
        self.helpers();p=self.root/'bin/rust-lld';p.rename(self.root/'ambient');p.symlink_to(self.root/'ambient')
        self.assertNotEqual(self.run_surface().returncode,0)

    def test_missing_host_refused(self):
        self.compiler('commit-hash: fixture\\n');self.assertNotEqual(self.run_surface().returncode,0)

    def test_ambiguous_host_refused(self):
        self.compiler('host: aarch64-apple-darwin\\nhost: test-host\\n')
        r=self.run_surface();self.assertNotEqual(r.returncode,0)
        self.assertIn('has 2 `host:` lines where one is required',r.stderr)

    def test_a_compiler_that_cannot_answer_is_quoted(self):
        # The refusal was "cannot report its compiler host" and nothing else.
        p=self.root/'bin/trustc'
        p.write_text("#!/bin/sh\necho 'trustc: error while loading shared libraries: librustc_driver-fixture.so' >&2\nexit 127\n")
        r=self.run_surface();self.assertNotEqual(r.returncode,0)
        self.assertIn('fixture cannot report its compiler host: `trustc -vV` exited 127. It said:',r.stderr)
        self.assertIn('        | trustc: error while loading shared libraries: librustc_driver-fixture.so',r.stderr)
        p.write_text('#!/bin/sh\nexit 3\n')
        r=self.run_surface();self.assertNotEqual(r.returncode,0)
        self.assertIn('exited 3. It said:\n        | (it printed nothing)',r.stderr)

    def test_another_host_has_no_paired_surface(self):
        # Nothing is checked, so the function passes with no helper present;
        # the caller that reports it says "not applicable" (GatePassSaysWhatItChecked).
        self.compiler('host: aarch64-unknown-linux-gnu\\n');self.assertEqual(self.run_surface().returncode,0)


# The real helper's refusal of a caller that holds no admission, word for word
# (crates/trust-resource-controller/src/bin/trust-serial-command.rs), exit 75.
UNADMITTED = "command requires an already-admitted caller; this launcher grants no CPU/memory"
EXECUTOR = f"""#!/bin/sh
# Inert stand-in for trust-serial-command: its argv contract, its refusal words
# and status, no GNU transport and no admission.
refuse() {{ printf 'trust-serial-command: refused: %s\\n' "$1" >&2; exit 75; }}
[ "$#" -ge 2 ] && [ "$1" = -- ] || refuse 'use -- /absolute/program [arguments...]'
case "$2" in /*) ;; *) refuse 'use -- /absolute/program [arguments...]' ;; esac
[ "${{BUILD_SLOT_HELD:-}}" = 1 ] || refuse '{UNADMITTED}'
shift
exec "$@"
"""

# What a compiler that cannot start prints (glibc's loader, exit 127): the line
# begins with the program's path, never with `error`.
LOADER = "error while loading shared libraries"
LOADER_LINE = ("/srv/trust/build/aarch64-unknown-linux-gnu/stage2/bin/trustc: " + LOADER
               + ": librustc_driver-0123456789abcdef.so: cannot open shared object file: No such file or directory")
COMPILERS = {
    # (what every compile prints on stderr, its exit status)
    "loader": ("printf '%s\\n' '{}' >&2".format(LOADER_LINE), 127),
    "silent": (":", 3),
    "error-line": ("printf 'error: synthetic compile failure\\n' >&2", 1),
}

BLAME = (
    "FAILS this tree's named UI tests",
    "Fix the compiler",
    "CANNOT START",
    "x.py build",
    "gate-only: REFUSED",
    "rustc_private consumer",
)


class GateFixture(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="promote-gate-refusal-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        self.toolchain = self.root / "build" / "test-host" / "stage2"
        (self.toolchain / "bin").mkdir(parents=True)
        for name in ("home", "sealed", "rustup"):
            (self.root / name).mkdir()
        self.executor = self.root / "trust-serial-command"
        self.executor.write_text(EXECUTOR)
        self.executor.chmod(0o755)
        self.compiler("error-line")

    def compiler(self, kind):
        says, status = COMPILERS[kind]
        trustc = self.toolchain / "bin" / "trustc"
        trustc.write_text(
            "#!/bin/sh\n"
            "# Inert fixture: answers the host query, then fails every compile one way.\n"
            'case "${1:-}" in -vV) printf \'commit-hash: fixture\\nhost: test-host\\n\'; exit 0 ;; esac\n'
            f"{says}\nexit {status}\n")
        trustc.chmod(0o755)

    def promote(self, *options, executor="stand-in", admitted=True, tmpdir=None):
        env = {
            "PATH": "/usr/bin:/bin", "HOME": str(self.root / "home"), "TMPDIR": str(tmpdir or self.root),
            "LC_ALL": "C", "TRUST_TOOLCHAIN_HOME": str(self.root / "sealed"),
            "RUSTUP_HOME": str(self.root / "rustup"),
        }
        if executor == "stand-in":
            env["TRUST_TOOLCHAIN_SERIAL_COMMAND"] = str(self.executor)
        elif executor is not None:
            env["TRUST_TOOLCHAIN_SERIAL_COMMAND"] = executor
        if admitted:
            env["BUILD_SLOT_HELD"] = "1"
        result = subprocess.run(
            ["/bin/bash", str(SCRIPT), *options, str(self.toolchain)], env=env, cwd=self.root,
            stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            text=True, timeout=120)
        self.assertEqual(sorted(p.name for p in (self.root / "sealed").iterdir()), [], "something was sealed")
        self.assertEqual(sorted(p.name for p in (self.root / "rustup").iterdir()), [], "the channel was touched")
        return result


class OneRefusalBeforeAnyGate(GateFixture):
    """(i) The executor is asked for once, before the first gate."""

    def assert_one_refusal(self, result, problem):
        out = result.stdout
        self.assertNotEqual(result.returncode, 0, out)
        lines = [line for line in out.splitlines() if line.strip()]
        self.assertTrue(lines, "nothing was printed")
        # The refusal is the first thing said, and it names the variable and what is wrong with it.
        self.assertTrue(lines[0].startswith("promote: "), out)
        self.assertIn("TRUST_TOOLCHAIN_SERIAL_COMMAND", lines[0], out)
        self.assertIn(problem, lines[0], out)
        # Once: no second refusal, of this or of anything else.
        self.assertEqual([line for line in lines if line.startswith("promote: ")], [lines[0]], out)
        # How to build the helper.
        self.assertIn("crates/trust-resource-controller", out)
        self.assertIn("--features serial-command --bin trust-serial-command", out)
        # No gate ran: no step header, no row, no surface check.
        self.assertIsNone(re.search(r"(?m)^==> ", out), out)
        self.assertIsNone(re.search(r"(?m)^    (FAIL|ok|n/a|NOT RUN) ", out), out)
        self.assertNotIn("verify-toolchain:", out)
        # And nothing blames the toolchain for it.
        for words in BLAME:
            self.assertNotIn(words, out)

    def test_unset_under_gate_only(self):
        self.assert_one_refusal(self.promote("--gate-only", executor=None), "not set")

    def test_unset_on_the_seal_path(self):
        self.assert_one_refusal(self.promote("--no-flip", executor=None), "not set")

    def test_set_and_empty_is_unset(self):
        self.assert_one_refusal(self.promote("--gate-only", executor=""), "not set")

    def test_a_file_that_is_not_there(self):
        missing = self.root / "absent" / "trust-serial-command"
        for mode in ("--gate-only", "--no-flip"):
            with self.subTest(mode=mode):
                self.assert_one_refusal(self.promote(mode, executor=str(missing)), str(missing))

    def test_every_other_thing_that_is_not_the_executor(self):
        link = self.root / "link"
        link.symlink_to(self.executor)
        plain = self.root / "not-executable"
        plain.write_text(EXECUTOR)
        plain.chmod(0o644)
        for label, value in (("relative", "trust-serial-command"), ("symlink", str(link)),
                             ("not executable", str(plain)), ("directory", str(self.root / "home"))):
            with self.subTest(label):
                self.assert_one_refusal(self.promote("--gate-only", executor=value), value)

    def test_help_documents_it_and_needs_none(self):
        result = subprocess.run(["/bin/bash", str(SCRIPT), "--help"], env={"PATH": "/usr/bin:/bin"},
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=60)
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn("TRUST_TOOLCHAIN_SERIAL_COMMAND", result.stdout)
        self.assertIn("--features serial-command --bin trust-serial-command", result.stdout)

    def test_provenance_of_a_seal_needs_none(self):
        # --provenance starts no compiler through the executor: the refusal is
        # of the gates, not of every mode.
        (self.toolchain / "PROVENANCE").write_text("sealed_by=scripts/promote-toolchain.sh\n")
        result = self.promote("--provenance", executor=None)
        self.assertEqual((result.returncode, result.stdout), (0, "sealed_by=scripts/promote-toolchain.sh\n"))


class AFailRowSaysWhatItsCommandPrinted(GateFixture):
    """(ii) No FAIL row of the UI gate ends at its colon."""

    EMPTY = re.compile(r"(?m)(got exit \d+|\(exit \d+\)|got instead|stdout began):[ \t]*$")

    def ui_rows(self, out):
        """{row: the lines printed under its FAIL line} for the UI gate's rows."""
        section = out.split("==> UI gate:", 1)[1].split("==> tool-start gate:", 1)[0]
        rows, current = {}, None
        for line in section.splitlines()[1:]:
            if line.startswith("    FAIL  "):
                current = line[len("    FAIL  "):]
                rows[current] = []
            elif line.startswith("    ok    "):
                current = None
            elif current is not None and line.startswith("          "):
                rows[current].append(line)
        return rows

    def failed_rows(self, kind, **how):
        self.compiler(kind)
        result = self.promote("--gate-only", **how)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("==> UI gate:", result.stdout, result.stdout)
        rows = self.ui_rows(result.stdout)
        # The instrument: every row of the gate ran and failed (8 on 2026-11-12).
        self.assertGreaterEqual(len(rows), 8, result.stdout)
        self.assertIsNone(re.search(r"(?m)^    ok    tests/ui/", result.stdout), result.stdout)
        return result.stdout, rows

    def test_control_an_error_line_is_the_reason_as_before(self):
        out, rows = self.failed_rows("error-line")
        for row, reason in rows.items():
            with self.subTest(row=row):
                self.assertIn("error: synthetic compile failure", "\n".join(reason))
        self.assertIsNone(self.EMPTY.search(out), out)

    def test_a_compiler_the_loader_cannot_start_is_quoted_in_every_row(self):
        out, rows = self.failed_rows("loader")
        for row, reason in rows.items():
            with self.subTest(row=row):
                self.assertIn(LOADER, "\n".join(reason))
        self.assertIsNone(self.EMPTY.search(out), out)

    def test_a_command_that_prints_nothing_is_said_to_have_printed_nothing(self):
        out, rows = self.failed_rows("silent")
        for row, reason in rows.items():
            with self.subTest(row=row):
                self.assertIn("printed nothing", "\n".join(reason))
        self.assertIsNone(self.EMPTY.search(out), out)

    def test_a_refusal_of_the_executor_itself_is_quoted(self):
        # The file is there and the caller holds no admission: the real helper
        # exits 75 in these words. Whether promotion says so once before the
        # gates or in every row, the helper's words are in what it prints.
        self.compiler("error-line")
        result = self.promote("--gate-only", admitted=False)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn(UNADMITTED, result.stdout)
        self.assertIsNone(self.EMPTY.search(result.stdout), result.stdout)
        self.assertNotIn("Fix the compiler", result.stdout)


def utf8_locale():
    """The name of a UTF-8 locale this host has, or None."""
    saved = locale.setlocale(locale.LC_CTYPE)
    try:
        for name in ("C.UTF-8", "en_US.UTF-8", "C.utf8", "en_US.utf8"):
            try:
                locale.setlocale(locale.LC_CTYPE, name)
            except locale.Error:
                continue
            return name
        return None
    finally:
        locale.setlocale(locale.LC_CTYPE, saved)


class AQuotedLineKeepsItsReason(unittest.TestCase):
    """gate_said (one line, in a row), said_block (up to twelve, under one) and
    tool_start_excerpt (up to two, which its caller prefixes)."""

    REASON = LOADER + ": librustc_driver-0123456789abcdef.so: cannot open shared object file: No such file or directory"
    QUOTERS = ("gate_said", "said_block", "tool_start_excerpt")

    def quote(self, function, data, lc_all=None):
        source = re.search(r"(?ms)^%s\(\) \{\n.*?^\}" % function, SCRIPT.read_text()).group()
        with tempfile.TemporaryDirectory(prefix="promote-quoted-line-") as scratch:
            said = Path(scratch) / "said"
            if data is not None:
                said.write_bytes(data)
            result = subprocess.run(
                ["/bin/bash", "-c", "set -euo pipefail\n" + source + "\n" + function + ' "$1"\n', "fixture", str(said)],
                env={"PATH": "/usr/bin:/bin", **({"LC_ALL": lc_all} if lc_all else {})}, capture_output=True, timeout=60)
        self.assertEqual((result.returncode, result.stderr), (0, b""))
        return result.stdout.decode("utf-8", "replace")

    def test_a_long_program_path_does_not_push_the_reason_out(self):
        # Cut from the left at a fixed column, the row kept the path and lost
        # the reason: the suite itself failed under a TMPDIR of 107 characters.
        for depth in (1, 4, 12, 40):
            program = "/" + "/".join(["a-directory-of-some-length"] * depth) + "/stage2/bin/trustc"
            line = program + ": " + self.REASON
            for function in self.QUOTERS:
                with self.subTest(function=function, columns=len(line)):
                    said = self.quote(function, (line + "\n").encode())
                    self.assertIn(self.REASON, said)
                    self.assertEqual(" ... " in said, len(line) > 240, said)
                    self.assertLessEqual(max(map(len, said.splitlines())), 240 + len("        | "))

    def test_a_file_grep_calls_binary_is_still_quoted(self):
        # A NUL, or a byte that is not UTF-8, made grep print "Binary file ...
        # matches" on stdout or nothing at all, and the row quoted that.
        data = b"\x00\xff\xfe not text\nerror: the reason, after a \x00 byte\n"
        for function in self.QUOTERS:
            with self.subTest(function=function):
                said = self.quote(function, data)
                self.assertIn("error: the reason, after a", said)  # an awk may end the line at the NUL
                self.assertNotIn("\x00", said)
                self.assertNotIn("Binary file", said)

    def test_a_utf8_locale_adds_no_line_of_an_awks_own(self):
        # A seal runs in its caller's locale, and every other fixture here runs
        # in C. In a UTF-8 locale gawk's length() answers a byte that is not
        # UTF-8 with a warning on stderr ("Invalid multibyte data detected"),
        # which stood between a tool-start FAIL row and the excerpt under it
        # (measured 2026-11-12, gawk 5.2.1, en_US.utf8). quote() refuses any
        # stderr, so each function must end with none of its own.
        name = utf8_locale()
        if name is None:
            self.skipTest("this host has no UTF-8 locale to measure in (asked for C.UTF-8, en_US.UTF-8, C.utf8, en_US.utf8)")
        tail = b"\xff\xfe" + b"x" * 180 + b" the reason, at the end\n"
        for kind, data in (("any line", b"/p/" + b"a" * 120 + tail),
                           ("an error", b"note: before\nerror: /p/" + b"a" * 120 + tail),
                           ("a panic", b"thread 'rustc' panicked at /p/" + b"a" * 120 + tail + b"\xff the message\n")):
            for function in self.QUOTERS:
                with self.subTest(function=function, kind=kind, locale=name):
                    said = self.quote(function, data, lc_all=name)
                    self.assertIn(" ... ", said)
                    self.assertIn("the reason, at the end", said)

    def test_the_first_error_line_is_the_reason_and_otherwise_the_first_line(self):
        self.assertEqual(self.quote("gate_said", b"note: before\nerror: this one\nerror: not this one\n"), "error: this one")
        self.assertEqual(self.quote("gate_said", b"\n   \nthe first line that is not blank\nthe second\n"),
                         "the first line that is not blank")
        self.assertEqual(self.quote("said_block", b"note: before\nerror: this one\nafter it\n"),
                         "        | error: this one\n        | after it\n")

    def test_a_tool_start_excerpt_is_two_lines_of_the_panic_the_errors_or_anything(self):
        self.assertEqual(self.quote("tool_start_excerpt", b"note: before\nthread 'rustc' panicked at symbol.rs:1:2:\n"
                                                          b"the message\nerror: after the panic\n"),
                         "thread 'rustc' panicked at symbol.rs:1:2:\nthe message\n")
        self.assertEqual(self.quote("tool_start_excerpt", b"note: before\nerror: one\n --> x.rs\nerror: two\nerror: three\n"),
                         "error: one\nerror: two\n")
        self.assertEqual(self.quote("tool_start_excerpt", b"\n  \nthe first line that is not blank\nthe second\nthe third\n"),
                         "the first line that is not blank\nthe second\n")

    def test_nothing_is_said_to_be_nothing(self):
        for data in (b"", b"\n \t\n", None):
            with self.subTest(data=data):
                self.assertEqual(self.quote("gate_said", data), "(it printed nothing)")
                self.assertEqual(self.quote("said_block", data), "        | (it printed nothing)\n")
                self.assertEqual(self.quote("tool_start_excerpt", data), "(it printed nothing)\n")


def noexec_scratch(test):
    """A scratch directory on a filesystem mounted noexec, removed with the test.

    A host has such a filesystem or it does not (the aarch64 Linux host of
    2026-11-12 has /run/lock, a writable tmpfs mounted noexec)."""
    mounts = Path("/proc/self/mounts")
    for line in mounts.read_text().splitlines() if mounts.is_file() else ():
        fields = line.split()
        if len(fields) >= 4 and "noexec" in fields[3].split(",") and os.access(fields[1], os.W_OK | os.X_OK):
            try:
                scratch = tempfile.TemporaryDirectory(prefix="promote-cannot-run-", dir=fields[1])
            except OSError:
                continue
            test.addCleanup(scratch.cleanup)
            return scratch
    test.skipTest("this host has no writable filesystem mounted noexec to measure on")


class AFileThatCannotBeRunSaysWhy(unittest.TestCase):
    """cannot_run_why, alone: three answers where there was one sentence."""

    def why(self, path):
        source = re.search(r"(?ms)^cannot_run_why\(\) \{\n.*?^\}", SCRIPT.read_text()).group()
        result = subprocess.run(
            ["/bin/bash", "-c", "set -euo pipefail\n" + source + '\ncannot_run_why "$1"\n', "fixture", str(path)],
            env={"PATH": "/usr/bin:/bin"}, capture_output=True, text=True, timeout=60)
        self.assertEqual((result.returncode, result.stderr), (0, ""))
        return result.stdout

    def test_nothing_written_and_written_without_an_execute_bit(self):
        with tempfile.TemporaryDirectory(prefix="promote-cannot-run-") as scratch:
            plain = Path(scratch) / "plain"
            plain.write_text("x")
            plain.chmod(0o644)
            self.assertEqual(self.why(Path(scratch) / "absent"), "the compiler exited 0 and wrote no absent")
            self.assertRegex(self.why(plain), r"^the compiler exited 0 and wrote plain as something that is not a file "
                                              r"with an execute bit \(-rw-r--r--[.+@]?\)$")
            self.assertRegex(self.why(scratch), r"is not a file with an execute bit \(d")

    def test_an_execute_bit_the_filesystem_does_not_honour_is_not_the_compilers(self):
        scratch = noexec_scratch(self)
        program = Path(scratch.name) / "program"
        program.write_text("#!/bin/sh\n")
        program.chmod(0o755)
        self.assertFalse(os.access(program, os.X_OK), "the instrument: this filesystem lets the file be executed")
        said = self.why(program)
        self.assertIn("wrote program with an execute bit and this run still may not execute it, "
                      "which says nothing about the compiler", said)
        self.assertIn("is " + scratch.name + " on a filesystem mounted noexec? Set TMPDIR", said)


class AScratchDirectoryThatMayNotRunAProgramIsOneRefusal(GateFixture):
    """A TMPDIR mounted noexec is refused once, before any gate. Two UI rows and
    the rustc-dev probe used to print FAIL under "which says nothing about the
    compiler", and the run ended "UI gate FAILED" / "FAILS this tree's named UI
    tests"."""

    def test_a_tmpdir_mounted_noexec_is_one_refusal_before_any_gate(self):
        scratch = noexec_scratch(self)
        for mode in ("--gate-only", "--no-flip"):
            with self.subTest(mode=mode):
                result = self.promote(mode, tmpdir=scratch.name)
                out = result.stdout
                self.assertNotEqual(result.returncode, 0, out)
                self.assertEqual(len(re.findall(r"(?m)^promote: ", out)), 1, out)
                self.assertIn("promote: REFUSED before any gate: a file written under " + scratch.name
                              + " with an execute bit may not be executed there", out)
                self.assertIn("TMPDIR to a directory on a filesystem that allows execution, and run again.", out)
                self.assertIn("No gate ran. This says nothing about the toolchain.", out)
                self.assertIsNone(re.search(r"(?m)^==> ", out), out)
                self.assertIsNone(re.search(r"(?m)^    (FAIL|ok|n/a|NOT RUN) ", out), out)
                for words in BLAME + ("FAILED",):
                    self.assertNotIn(words, out)
                self.assertEqual(os.listdir(scratch.name), [], "the question left something in TMPDIR")

    def test_a_tmpdir_that_runs_programs_is_asked_and_leaves_nothing(self):
        # The fixture compiler fails every compile, so the run goes on to its
        # gates: the question passed, and its scratch directory is gone.
        asked = self.root / "asked"
        asked.mkdir()
        out = self.promote("--gate-only", tmpdir=asked).stdout
        self.assertNotIn("REFUSED before any gate", out)
        self.assertIn("==> UI gate:", out)
        self.assertEqual([p for p in asked.rglob("program")], [], out)

    def test_a_relative_tmpdir_is_not_refused(self):
        # The question is whether a program written there may be executed, not
        # how the directory is spelled: `mktemp -d` answers a relative TMPDIR
        # with a relative path, and the gates run under it.
        (self.root / "relative").mkdir()
        out = self.promote("--gate-only", tmpdir="relative").stdout
        self.assertNotIn("REFUSED before any gate", out)
        self.assertIn("==> UI gate:", out)
        self.assertEqual([p for p in (self.root / "relative").rglob("program")], [], out)

    def test_a_tmpdir_that_is_not_there_is_one_refusal_in_words(self):
        # The instrument: a bare `mktemp -d` that makes its directory somewhere
        # other than TMPDIR cannot be made to fail this way, so the host is
        # asked (not measured on macOS, whose mktemp has its own default).
        asked = subprocess.run(["mktemp", "-d"], env={**os.environ, "TMPDIR": str(self.root)},
                               capture_output=True, text=True)
        made = asked.stdout.strip()
        if made:
            os.rmdir(made)
        if asked.returncode or not made.startswith(str(self.root) + os.sep):
            self.skipTest("this host's bare `mktemp -d` does not make its directory under TMPDIR")
        absent = self.root / "absent"
        for mode in ("--gate-only", "--no-flip"):
            with self.subTest(mode=mode):
                out = self.promote(mode, tmpdir=absent).stdout
                self.assertEqual(len(re.findall(r"(?m)^promote: ", out)), 1, out)
                self.assertIn("promote: REFUSED before any gate: could not create a scratch directory under "
                              + str(absent) + " (what `mktemp -d` said is above).", out)
                # What mktemp itself said is on the page, above the refusal.
                self.assertRegex(out.split("promote: ")[0], r"(?m)^mktemp: .*" + re.escape(str(absent)))
                self.assertIn("No gate ran. This says nothing about the toolchain.", out)
                self.assertIsNone(re.search(r"(?m)^==> ", out), out)
                for words in BLAME + ("FAILED",):
                    self.assertNotIn(words, out)

    def test_the_executor_is_asked_for_first_and_provenance_asks_neither(self):
        # One refusal, not two: a run with no executor says so and stops, and
        # --provenance starts no program anywhere.
        absent = self.root / "absent"
        out = self.promote("--gate-only", tmpdir=absent, executor=None).stdout
        self.assertEqual(len(re.findall(r"(?m)^promote: ", out)), 1, out)
        self.assertIn("promote: REFUSED before any gate: TRUST_TOOLCHAIN_SERIAL_COMMAND is not set.", out)
        self.assertNotIn("scratch directory", out)
        (self.toolchain / "PROVENANCE").write_text("sealed_by=scripts/promote-toolchain.sh\n")
        result = self.promote("--provenance", tmpdir=absent, executor=None)
        self.assertEqual((result.returncode, result.stdout), (0, "sealed_by=scripts/promote-toolchain.sh\n"))


class AnExecutorRefusalIsNotAVerdict(GateFixture):
    """(iii) The executor's own refusal: once before any gate, or NOT RUN after it."""

    def test_an_executor_that_refuses_the_no_op_is_one_refusal_before_any_gate(self):
        out = self.promote("--gate-only", admitted=False).stdout
        self.assertEqual(out.count("promote: REFUSED before any gate: the serial executor would not start a no-op (exit 75)."), 1, out)
        self.assertIn("    said: trust-serial-command: refused: " + UNADMITTED, out)
        self.assertEqual(len(re.findall(r"(?m)^promote: ", out)), 1, out)
        self.assertIsNone(re.search(r"(?m)^==> ", out), out)
        self.assertIsNone(re.search(r"(?m)^    (FAIL|ok|n/a|NOT RUN) ", out), out)
        for words in BLAME:
            self.assertNotIn(words, out)

    def test_a_refusal_that_begins_after_the_question_is_not_run_never_fail(self):
        # The slot is lost once the run is under way: only the no-op starts.
        self.executor.write_text(EXECUTOR.replace('[ "${BUILD_SLOT_HELD:-}" = 1 ]', '[ "${2##*/}" = true ]'))
        result = self.promote("--gate-only")
        out = result.stdout
        self.assertNotEqual(result.returncode, 0, out)
        section = out.split("==> UI gate:", 1)[1].split("==> tool-start gate:", 1)[0]
        self.assertEqual(len(re.findall(r"(?m)^    NOT RUN  tests/ui/trust/", section)), 8, out)
        self.assertEqual(section.count("the serial executor refused to start the compiler, so this row says nothing "
                                       "about it: trust-serial-command: refused: " + UNADMITTED), 8, out)
        self.assertIsNone(re.search(r"(?m)^    (FAIL|ok)  ", section), out)
        self.assertIn("UI gate NOT RUN (the serial executor refused), ", out)
        self.assertIn("native rustc-dev gate NOT RUN (the serial executor refused), ", out)
        self.assertNotIn("UI gate FAILED", out)


class AProgramTheOsWillNotStartIsItsOwnFailure(GateFixture):
    """The real helper reports a failed spawn in its refusal shape (exit 75,
    `refused: command launch: <OS error>`) and still starts a no-op: the row is
    a FAIL that quotes the error, never NOT RUN."""

    LAUNCH = "trust-serial-command: refused: command launch: No such file or directory (os error 2)"

    def test_a_compiler_that_cannot_be_launched_fails_every_row(self):
        self.executor.write_text(EXECUTOR.replace(
            'shift\n', 'shift\ncase "$1" in */bin/trustc) refuse "command launch: No such file or directory (os error 2)" ;; esac\n'))
        result = self.promote("--gate-only")
        out = result.stdout
        self.assertNotEqual(result.returncode, 0, out)
        section = out.split("==> UI gate:", 1)[1].split("==> tool-start gate:", 1)[0]
        self.assertEqual(len(re.findall(r"(?m)^    FAIL  tests/ui/trust/", section)), 8, out)
        self.assertEqual(section.count(self.LAUNCH), 8, out)
        self.assertNotIn("NOT RUN", out)
        self.assertIn("UI gate FAILED, ", out)
        self.assertIn("native rustc-dev gate FAILED, ", out)


class GatePassSaysWhatItChecked(GateFixture):
    """What --gate-only reports for the paired native-tool surface, per host."""

    def test_a_host_that_is_not_darwin_is_not_applicable(self):
        # The compile-failing fixture: every gate that ran is FAILED, and the
        # surface, which had nothing to check on this host, is neither.
        result = self.promote("--gate-only")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("paired native-tool surface not applicable (host test-host is not Darwin; nothing was checked)",
                      result.stdout)
        self.assertNotIn("paired native-tool surface passed", result.stdout)

    def test_a_darwin_sdk_with_neither_tool_is_absent_never_passed(self):
        # The same compile-failing fixture on a Darwin host: the other gates are
        # FAILED and refuse; the surface is the recorded gap, in its own words.
        trustc = self.toolchain / "bin" / "trustc"
        trustc.write_text(trustc.read_text().replace("host: test-host", "host: aarch64-apple-darwin"))
        result = self.promote("--gate-only")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("    RECORDED  gate-only SDK publishes no paired bin/rust-lld and bin/dsymutil", result.stdout)
        self.assertIn("paired native-tool surface ABSENT (recorded, not refused: this SDK has no bin/rust-lld "
                      "and no bin/dsymutil; nothing was checked)", result.stdout)
        self.assertNotIn("paired native-tool surface passed", result.stdout)
        self.assertNotIn("paired native-tool surface FAILED", result.stdout)

    def test_a_darwin_sdk_with_rust_lld_alone_is_refused(self):
        trustc = self.toolchain / "bin" / "trustc"
        trustc.write_text(trustc.read_text().replace("host: test-host", "host: aarch64-apple-darwin"))
        lld = self.toolchain / "bin" / "rust-lld"
        lld.write_text("#!/bin/sh\n# Inert startup fixture only.\nexit 0\n")
        lld.chmod(0o755)
        result = self.promote("--gate-only")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("native Darwin SDK lacks paired bin/rust-lld or bin/dsymutil", result.stdout)
        self.assertIn("paired native-tool surface FAILED", result.stdout)
        self.assertNotIn("paired native-tool surface PARTIAL", result.stdout)
        self.assertNotIn("gate-only: PASS", result.stdout)


if __name__ == '__main__':
    unittest.main()
