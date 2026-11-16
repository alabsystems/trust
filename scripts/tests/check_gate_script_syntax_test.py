"""Tests for scripts/check_gate_script_syntax.sh (the `manifest.syntax.gate-scripts` row).

The checker parses every gate script and hook without running one. It used to
hand every file under `scripts/hooks/` to `bash -n`, so the Perl helper
`scripts/hooks/_ssh_probe.pl` (b2c6fa0712, 2026-10-25) failed it while `perl -c`
accepted the file. Each fixture case copies the real checker into a scratch tree
(where it parses itself, so each count includes it): a valid Perl helper that
`bash -n` rejects parses (and its main program does not run), and a Perl syntax
error and a shell syntax error are each still named. The last case runs the
checker on this checkout.

    python3 -B -m unittest scripts.tests.check_gate_script_syntax_test

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""
from __future__ import annotations

import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
CHECKER = REPO / "scripts" / "check_gate_script_syntax.sh"

# Valid Perl whose `qw(...)` line `bash -n` rejects, as the real helper's does.
# Its main program writes $MARKER, so a parse that ran it is visible.
VALID_PERL = """\
use strict;
use warnings;
use Errno qw(EAGAIN EINTR ESRCH);
open(my $fh, '>', $ENV{MARKER}) or die "marker: $!";
print $fh "ran\\n";
close($fh);
"""
BROKEN_PERL = "use strict;\nmy $x = ;\n"
VALID_HOOK = "#!/usr/bin/env bash\nset -euo pipefail\necho ok\n"
BROKEN_HOOK = "#!/usr/bin/env bash\nif then\n"


class GateScriptSyntaxTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix="gate-script-syntax-")
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        self.marker = self.root / "perl-main-ran"
        (self.root / "scripts" / "hooks").mkdir(parents=True)
        shutil.copy2(CHECKER, self.root / "scripts" / "check_gate_script_syntax.sh")

    def write(self, rel: str, text: str) -> Path:
        path = self.root / rel
        path.write_text(text)
        return path

    def run_checker(self, root: Path) -> subprocess.CompletedProcess:
        env = dict(os.environ, MARKER=str(self.marker))
        return subprocess.run(["bash", str(root / "scripts" / "check_gate_script_syntax.sh")],
                              capture_output=True, text=True, env=env, timeout=120)

    def test_a_valid_perl_helper_parses_as_perl_without_running(self):
        helper = self.write("scripts/hooks/_probe.pl", VALID_PERL)
        self.write("scripts/hooks/pre-push", VALID_HOOK)
        # Control: the fixture is one `bash -n` rejects, as it rejected the real helper.
        as_shell = subprocess.run(["bash", "-n", str(helper)], capture_output=True, text=True)
        self.assertNotEqual(as_shell.returncode, 0)
        self.assertIn("syntax error", as_shell.stderr)
        done = self.run_checker(self.root)
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertIn("gate script syntax: 3 scripts parse", done.stdout)
        self.assertFalse(self.marker.exists(), "parsing the Perl helper ran its main program")

    def test_a_perl_syntax_error_is_still_named(self):
        self.write("scripts/hooks/_probe.pl", BROKEN_PERL)
        self.write("scripts/hooks/pre-push", VALID_HOOK)
        done = self.run_checker(self.root)
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        self.assertIn("gate script syntax FAIL (1/3): scripts/hooks/_probe.pl", done.stderr)

    def test_a_shell_syntax_error_beside_a_valid_perl_helper_is_named(self):
        self.write("scripts/hooks/_probe.pl", VALID_PERL)
        self.write("scripts/hooks/pre-push", BROKEN_HOOK)
        done = self.run_checker(self.root)
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        self.assertIn("gate script syntax FAIL (1/3): scripts/hooks/pre-push", done.stderr)
        self.assertFalse(self.marker.exists())

    def test_this_checkout_parses_including_its_perl_helper(self):
        self.assertTrue((REPO / "scripts" / "hooks" / "_ssh_probe.pl").is_file())
        done = self.run_checker(REPO)
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertRegex(done.stdout, r"gate script syntax: \d+ scripts parse")


if __name__ == "__main__":
    unittest.main()
