#!/usr/bin/env python3
"""Real canonical Bash entrypoint, private Git fixtures, no Rust/Lean build."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "regen-trustir-oleans.sh"


class ProducerToolSelectionTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="bridge-tool-selection-")
        self.root = Path(self.tmp.name)
        (self.root / "scripts").mkdir()
        shutil.copyfile(SCRIPT, self.root / "scripts" / SCRIPT.name)
        self.trace = self.root / "calls.jsonl"
        self.bin = self.root / "bin"
        self.bin.mkdir()
        (self.root / ".ubd").mkdir()
        for name in ("trust-ir", "clean"):
            repo = self.root / "first-party" / name
            repo.mkdir(parents=True)
            subprocess.run(["/usr/bin/git", "init", "-q", str(repo)], check=True)
            subprocess.run(["/usr/bin/git", "-C", str(repo), "-c", "user.name=fixture",
                            "-c", "user.email=fixture@invalid", "commit", "--allow-empty", "-qm", "fixture"], check=True)

    def tearDown(self):
        self.tmp.cleanup()

    def tool(self, relative, mode):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        # A `#!{sys.executable}` shebang cannot carry an interpreter path with spaces
        # (atpkg's python lives under `Application Support/`): exec splits it, the fake
        # never runs and every test errors on a missing trace. The sh/python polyglot
        # keeps argv[0] as this file, which the traces record, under any interpreter path.
        path.write_text(f'#!/bin/sh\n""":"\nexec "{sys.executable}" "$0" "$@"\n":"""\n' +
            "import json,os,sys\n" +
            f"mode={mode!r}\n" +
            "with open(os.environ['FIXTURE_CALLS'],'a') as f: f.write(json.dumps(dict(tool=sys.argv[0],args=sys.argv[1:]))+'\\n')\n" +
            "if sys.argv[1:]==['--unverified','--version']:\n" +
            " if mode=='stale': sys.exit(2)\n" +
            " print('cargo 1.101.0' if mode=='cargo-brand' else 'targo 1.101.0 (fixture)'); sys.exit(0)\n" +
            "if sys.argv[1:2]==['metadata']: sys.exit(0)\n" +
            "if sys.argv[1:3]==['--unverified','run']: sys.exit(91)\n" +
            "if sys.argv[1:2]==['run']: sys.exit(92)\n" +
            "sys.exit(93)\n")
        path.chmod(0o700)
        return path

    def run_producer(self, selected=None, args=()):
        env = {k: v for k, v in os.environ.items()
               if not k.startswith(('GIT_', 'TRUST_REGEN_', 'BUILD_SLOT'))}
        env.update(PATH=str(self.bin)+':/usr/bin:/bin', FIXTURE_CALLS=str(self.trace), TMPDIR=str(self.root / '.ubd'))
        if selected is not None:
            env['TRUST_REGEN_TARGO'] = str(selected)
        result = subprocess.run(['/bin/bash', str(self.root / 'scripts' / SCRIPT.name), *args],
                                env=env, cwd=self.root, capture_output=True, text=True, timeout=5)
        calls = [json.loads(line) for line in self.trace.read_text().splitlines()]
        return result, calls

    def test_explicit_stale_tool_refuses_before_any_rust_command(self):
        selected = self.tool('bin/targo', 'stale')
        result, calls = self.run_producer(selected, ['--write'])
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn('genuine', result.stderr)
        self.assertEqual([row['args'] for row in calls], [['--unverified', '--version']])

    def test_explicit_cargo_brand_refuses_even_when_flag_is_accepted(self):
        selected = self.tool('bin/targo', 'cargo-brand')
        result, calls = self.run_producer(selected)
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn('genuine', result.stderr)
        self.assertEqual([row['args'] for row in calls], [['--unverified', '--version']])

    def test_discovery_skips_newer_stale_tool_before_metadata(self):
        stale = self.tool('build/host/stage2/bin/targo', 'stale')
        good = self.tool('build/host/stage1/bin/targo', 'genuine')
        os.utime(stale, (200, 200))
        os.utime(good, (100, 100))
        result, calls = self.run_producer()
        self.assertEqual(result.returncode, 91, result.stderr)
        self.assertEqual([row['args'] for row in calls if row['tool'] == str(stale)],
                         [['--unverified', '--version']])
        self.assertTrue(any(row['tool'] == str(good) and row['args'][0] == 'metadata' for row in calls))
        self.assertEqual(calls[-1]['args'][:2], ['--unverified', 'run'])
        self.assertFalse(any(row['args'][0] == 'run' for row in calls))

    def test_genuine_explicit_tool_keeps_lane_in_every_mode(self):
        selected = self.tool('bin/targo', 'genuine')
        for args in ([], ['--write'], ['--reuse-source-inputs', '0'*40]):
            with self.subTest(args=args):
                self.trace.unlink(missing_ok=True)
                result, calls = self.run_producer(selected, args)
                self.assertEqual(result.returncode, 91, result.stderr)
                self.assertEqual(calls[-1]['args'][:2], ['--unverified', 'run'])
                self.assertFalse(any(row['args'][0] == 'run' for row in calls))
                self.assertIn('failed scratch retained', result.stderr)


if __name__ == '__main__':
    unittest.main()
