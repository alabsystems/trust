"""Actual production hook + real local Git pushes, with a synthetic Targo."""
from __future__ import annotations
import contextlib
import errno
import importlib.util
import io
import json
import os
from pathlib import Path
import shlex
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
from types import SimpleNamespace
import unittest
from unittest import mock
REPO = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(REPO / 'scripts/lib'), str(REPO / 'scripts')]
import landing_targo as handoff
import land_gate
from test_python import fixture_shebang

FIXTURE_TARGO_VERSION = 'targo 1.101.0-dev (fixture 2026-11-10) (targo 0.13.0+gfixture)'
OLD_TARGO_VERSION = 'targo 1.101.0-dev (29ebb403d 2026-10-28) (targo 0.12.0+g29ebb403d)'
# The `--options` of handoff.COMMAND that 0.12.0+g29ebb403d accepts (measured:
# all but --require-test-bin), and a targo that has every one.
OLD_TARGO_OPTIONS = ('--manifest-path', '--locked', '--no-fail-fast', '--config')
TARGO_OPTIONS = OLD_TARGO_OPTIONS + ('--require-test-bin',)


def clap_targo(path, options, *, version=FIXTURE_TARGO_VERSION, counter=None, run='sys.exit(0)\n'):
    """A fake targo at `path` that parses as Targo's parser (clap) does.
    `--version` prints `version`. Arguments are read in order up to `--`: the
    first `--option` outside `options` (and `--unverified`) is refused in
    clap's words, exit 1, and reaching `--help` before `--` prints a help,
    exit 0 (landing_targo.capability_gap's probe). Anything else is a suite
    run: its argv is appended to `counter` before parsing, then `run` (Python
    source) runs. `options=None` is cargo under the name: it knows no
    `--unverified`."""
    known = sorted({'--unverified', *options}) if options is not None else []
    count = ('if not probe:\n'
             f' with Path({str(counter)!r}).open("a") as f: f.write(json.dumps({{"argv":sys.argv[1:],'
             '"env":os.environ.get("BOUND_INPUT"),"bash_env":os.environ.get("BASH_ENV"),'
             f'"request":os.environ.get({handoff.HEAD_ENV!r})}})+"\\n")\n') if counter else ''
    path = Path(path)
    path.write_text(
        fixture_shebang() + 'import os,sys,json\nfrom pathlib import Path\n'
        f"if sys.argv[1:]==['--version']:\n print({version!r}); sys.exit(0)\n"
        "end=sys.argv.index('--') if '--' in sys.argv[1:] else len(sys.argv)\n"
        "probe='--help' in sys.argv[1:end]\n" + count +
        "for a in sys.argv[1:end]:\n"
        " if a=='--help': break\n"
        f" if a.startswith('--') and a.split('=',1)[0] not in {known!r}:\n"
        "  sys.stderr.write(\"error: unexpected argument '\"+a+\"' found\\n\"); sys.exit(1)\n"
        "if probe:\n print('Usage: targo test [OPTIONS] [TESTNAME] [-- [ARGS]...]'); sys.exit(0)\n" + run)
    path.chmod(0o755)
    return str(path)


class ReviewedPinTests(unittest.TestCase):
    def test_the_checkout_matches_its_reviewed_landing_pins(self):
        # The pins went stale unnoticed after 9f709bc793 (every land then
        # refused before its push): an edit to the hook or the runner must
        # move its pin in the same change, after review.
        self.assertIsNone(handoff.protocol_problem(REPO))

    def test_the_suite_builds_with_targo_trusts_own_features(self):
        # TARGO-MEMBER-FEATURE-SCOPE-1: under aterm's atpkg `targo` shim, which puts
        # `--config resolver.feature-unification="workspace"` before the verb of an
        # unverified test, this suite's graph was the root workspace's union (590
        # units, 38 of them compiler crates whose build scripts refuse to run
        # outside bootstrap) where targo-trust selects 410. The words right after
        # the verb are the crates lane's scope, whose live test measures them.
        spec = importlib.util.spec_from_file_location(
            "check_crates_tests_scoped", REPO / "scripts/check_crates_tests_scoped.py")
        lane = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(lane)
        self.assertEqual(handoff.COMMAND[:3], ["targo", "--unverified", "test"])
        self.assertEqual(handoff.COMMAND[3:6], lane.MEMBER_FEATURE_SCOPE)
        self.assertEqual(lane.MEMBER_FEATURE_SCOPE,
                         ["-Zfeature-unification", "--config", 'resolver.feature-unification="selected"'])


class ChildExitObservationTests(unittest.TestCase):
    def test_native_nonblocking_observation_keeps_child_waitable(self):
        self.assertTrue(handoff.exit_observation_available())
        process = subprocess.Popen(
            [sys.executable, '-c', 'import sys; sys.stdin.buffer.read(1)'],
            stdin=subprocess.PIPE)
        try:
            self.assertFalse(handoff.wait_child_exit(process.pid, nohang=True))
            process.stdin.close()
            self.assertTrue(handoff.wait_child_exit(process.pid))
            self.assertTrue(handoff.wait_child_exit(process.pid, nohang=True))
            # This exact PID is still our waitable child, not a cached return
            # code or a PID whose custody was released by the observer.
            pid, status = os.waitpid(process.pid, os.WNOHANG)
            self.assertEqual(pid, process.pid)
            process.returncode = os.waitstatus_to_exitcode(status)
            self.assertEqual(process.returncode, 0)
        finally:
            if process.returncode is None:
                process.kill()
                process.wait()

    def kqueue_observation(self, ready=None, error=None):
        queue = mock.Mock()
        queue.control.return_value = [] if ready is None else ready
        queue.control.side_effect = error
        backend = SimpleNamespace(
            kqueue=mock.Mock(return_value=queue), kevent=mock.Mock(),
            KQ_FILTER_PROC=1, KQ_EV_ADD=2, KQ_EV_ONESHOT=4,
            KQ_NOTE_EXIT=8, KQ_EV_ERROR=16)
        return queue, backend

    def test_kqueue_live_poll_is_nonblocking_and_closes_the_observer(self):
        queue, backend = self.kqueue_observation()
        with mock.patch.object(handoff, 'os', SimpleNamespace()), \
                mock.patch.object(handoff, 'select', backend):
            self.assertTrue(handoff.exit_observation_available())
            self.assertFalse(handoff.wait_child_exit(42, nohang=True))
        self.assertEqual(queue.control.call_args.args[1:], (1, 0))
        queue.close.assert_called_once_with()

    def test_kqueue_raced_exit_keeps_the_same_nonreaping_result(self):
        for ready, error in ((None, ProcessLookupError()),
                             ([SimpleNamespace(flags=16, data=errno.ESRCH)], None),
                             ([SimpleNamespace(flags=0, ident=42, fflags=8)], None)):
            with self.subTest(ready=ready, error=error):
                queue, backend = self.kqueue_observation(ready, error)
                with mock.patch.object(handoff, 'os', SimpleNamespace()), \
                        mock.patch.object(handoff, 'select', backend):
                    self.assertTrue(handoff.wait_child_exit(42, nohang=True))
                queue.close.assert_called_once_with()

    def test_kqueue_does_not_accept_another_pid_or_an_observation_error(self):
        for event, exception in ((SimpleNamespace(flags=0, ident=43, fflags=8), RuntimeError),
                                 (SimpleNamespace(flags=16, data=errno.EPERM), OSError)):
            with self.subTest(event=event):
                queue, backend = self.kqueue_observation([event])
                with mock.patch.object(handoff, 'os', SimpleNamespace()), \
                        mock.patch.object(handoff, 'select', backend):
                    with self.assertRaises(exception):
                        handoff.wait_child_exit(42, nohang=True)
                queue.close.assert_called_once_with()

    def test_unsupported_observation_refuses_before_spawning(self):
        with mock.patch.object(handoff, 'os', SimpleNamespace()), \
                mock.patch.object(handoff, 'select', SimpleNamespace()), \
                mock.patch.object(land_gate.subprocess, 'Popen') as launch:
            self.assertFalse(handoff.exit_observation_available())
            with self.assertRaisesRegex(RuntimeError, 'nonreaping exit observation'):
                land_gate._run_one(None, ['unreachable'], None, {}, (1, 2), None)
            launch.assert_not_called()


class OwnedGroupSignalTests(unittest.TestCase):
    def census(self, output, *, status=0, stderr=''):
        return SimpleNamespace(returncode=status, stdout=output, stderr=stderr)

    def test_eperm_accepts_only_a_complete_positive_zombie_group(self):
        for output in ('42 Z\n', '42 Zs+\n42 ZN<\n7 S\n', '0 S\n42 Z\n',
                       '7 ?NE\n42 Z\n'):
            with self.subTest(output=output), \
                    mock.patch.object(handoff.os, 'killpg', side_effect=PermissionError(errno.EPERM, 'fixture')), \
                    mock.patch.object(handoff.subprocess, 'run', return_value=self.census(output)):
                handoff.signal_owned_group(42, signal.SIGTERM)

    def test_live_unknown_failed_and_malformed_census_preserve_permission_refusal(self):
        cases = [(1, '', ''), (0, '', ''), (0, '7 Z\n', ''),
                 (0, '42 S\n', ''), (0, '42 Z\n42 R\n', ''),
                 (0, '42 ?\n', ''), (0, '42 ?NE\n', ''),
                 (0, '7 ?NE\n42 Z\n42 R\n', ''),
                 (0, '42 Z\n42 S extra\n', ''),
                 (0, '42 Z\n42\n', ''), (0, '42 Z\nbad S\n', ''),
                 (0, '42 Z\n\n', ''), (0, '42 Zombie\n', ''),
                 (0, '42 ZZ\n', ''), (0, '42 Z\n', 'partial census\n')]
        for status, output, stderr in cases:
            error = PermissionError(errno.EPERM, 'fixture')
            with self.subTest(status=status, output=output, stderr=stderr), \
                    mock.patch.object(handoff.os, 'killpg', side_effect=error), \
                    mock.patch.object(handoff.subprocess, 'run', return_value=self.census(output, status=status, stderr=stderr)):
                with self.assertRaises(PermissionError) as refused:
                    handoff.signal_owned_group(42, signal.SIGTERM)
                self.assertIs(refused.exception, error)

    def test_other_errors_do_not_run_the_zombie_exception(self):
        for error in (PermissionError(errno.EACCES, 'fixture'), OSError(errno.EIO, 'fixture')):
            with self.subTest(error=error), mock.patch.object(handoff.os, 'killpg', side_effect=error), \
                    mock.patch.object(handoff.subprocess, 'run') as census:
                with self.assertRaises(type(error)) as refused:
                    handoff.signal_owned_group(42, signal.SIGTERM)
                self.assertIs(refused.exception, error)
                census.assert_not_called()
        with mock.patch.object(handoff.os, 'killpg', side_effect=ProcessLookupError()), \
                mock.patch.object(handoff.subprocess, 'run') as census:
            handoff.signal_owned_group(42, signal.SIGTERM)
            census.assert_not_called()

    def test_unreadable_census_keeps_its_real_error(self):
        error = OSError(errno.EIO, 'ps unavailable')
        with mock.patch.object(handoff.os, 'killpg', side_effect=PermissionError(errno.EPERM, 'fixture')), \
                mock.patch.object(handoff.subprocess, 'run', side_effect=error):
            with self.assertRaises(OSError) as refused:
                handoff.signal_owned_group(42, signal.SIGTERM)
            self.assertIs(refused.exception, error)

    def test_real_owned_group_signal_is_observed_before_its_only_reap(self):
        child = subprocess.Popen([sys.executable, '-I', '-B', '-c',
                                  'import sys; sys.stdin.buffer.read(1)'],
                                 stdin=subprocess.PIPE, start_new_session=True)
        try:
            handoff.signal_owned_group(child.pid, signal.SIGTERM)
            self.assertTrue(handoff.wait_child_exit(child.pid))
            self.assertIsNone(child.returncode, 'nonreaping observer must retain the original group')
            self.assertEqual(child.wait(timeout=5), -signal.SIGTERM)
        finally:
            if child.returncode is None:
                handoff.signal_owned_group(child.pid, signal.SIGKILL)
                child.wait(timeout=5)
            child.stdin.close()

    def test_real_unreaped_zombie_is_positively_identified_by_native_ps(self):
        child = subprocess.Popen([sys.executable, '-I', '-B', '-c', 'pass'], start_new_session=True)
        try:
            self.assertTrue(handoff.wait_child_exit(child.pid))
            self.assertIsNone(child.returncode)
            with mock.patch.object(handoff.os, 'killpg', side_effect=PermissionError(errno.EPERM, 'fixture')):
                handoff.signal_owned_group(child.pid, signal.SIGTERM)
            self.assertEqual(child.wait(timeout=5), 0)
        finally:
            if child.returncode is None:
                handoff.signal_owned_group(child.pid, signal.SIGKILL)
                child.wait(timeout=5)


class CapabilityGapTests(unittest.TestCase):
    """GATE-TARGO-CAPABILITY-1: the targo a command would run is asked to parse
    that command. One that cannot is named, with its path and version, and
    nothing runs; one that can is ready, and the probe ran no suite."""

    def targo(self, options, **kw):
        d = Path(tempfile.mkdtemp(prefix='targo-capability.'))
        self.addCleanup(shutil.rmtree, d, True)
        self.counter = d / 'calls.jsonl'
        clap_targo(d / 'targo', options, counter=self.counter,
                   run='print("test result: ok. 3 passed; 0 failed; 0 ignored;")\n', **kw)
        return str(d)

    def gap(self, bindir, command=handoff.COMMAND):
        env = dict(os.environ, PATH=bindir + os.pathsep + os.environ['PATH'])
        return handoff.capability_gap(command, env, REPO)

    def test_fixture_uses_exact_interpreter_with_spaces_and_quotes_in_its_path(self):
        with tempfile.TemporaryDirectory(prefix="exact python ' path ") as directory:
            root = Path(directory)
            interpreter = root / "original python ' executable"
            interpreter.symlink_to(Path(sys.executable).resolve())
            with mock.patch.object(sys, "executable", str(interpreter)):
                clap_targo(root / "targo", TARGO_OPTIONS,
                           run="print(json.dumps([str(Path(sys.executable).resolve()), os.environ.get('DYLD_LIBRARY_PATH')]))\n")
            environment = dict(os.environ, DYLD_LIBRARY_PATH="exact-original-search-path")
            result = subprocess.run([str(root / "targo"), "--unverified", "test"], env=environment, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(json.loads(result.stdout), [str(interpreter.resolve()), "exact-original-search-path"])
            selected = Path((root / "targo").read_text().splitlines()[0][2:])
            self.assertFalse(any(character.isspace() for character in str(selected)))
            self.assertEqual(selected.resolve(), interpreter.resolve())

    def test_the_probe_is_the_command_itself_with_help_before_any_double_dash(self):
        self.assertEqual(handoff.capability_probe(handoff.COMMAND), handoff.COMMAND + ['--help'])
        self.assertEqual(handoff.capability_probe(handoff.COMMAND + ['--', '--exact', '--help']),
                         handoff.COMMAND + ['--help'])

    def test_an_old_targo_is_named_with_its_path_and_version_and_runs_nothing(self):
        old = self.targo(OLD_TARGO_OPTIONS, version=OLD_TARGO_VERSION)
        why = self.gap(old)
        self.assertIsNotNone(why)
        for part in ('lacks `--require-test-bin`', str(Path(old) / 'targo'), OLD_TARGO_VERSION,
                     'exit 1', '9f709bc793', 'no test ran'):
            self.assertIn(part, why)
        self.assertFalse(self.counter.exists(), 'the probe ran no suite')
        # Another missing option is named, and the --require-test-bin origin is not.
        noconfig = self.targo(('--manifest-path', '--locked', '--no-fail-fast', '--require-test-bin'))
        why = self.gap(noconfig)
        self.assertIn('lacks `--config`', why)
        self.assertNotIn('9f709bc793', why)

    def test_a_targo_that_parses_the_command_is_ready_and_the_probe_runs_no_suite(self):
        new = self.targo(TARGO_OPTIONS)
        self.assertIsNone(self.gap(new))
        # A harness's own arguments after `--` are not targo's and are not asked;
        # a `--help` there is the harness's, so it must never reach the targo.
        self.assertIsNone(self.gap(new, handoff.COMMAND + ['--', '--exact', '--help']))
        self.assertFalse(self.counter.exists(), 'the probe ran no suite')

    def test_cargo_under_the_name_a_refusal_naming_no_argument_and_no_targo(self):
        cargo = self.targo(None, version='cargo 1.91.0 (fixture)')
        why = self.gap(cargo)
        self.assertIn('lacks `--unverified`', why)
        self.assertIn('cargo 1.91.0 (fixture)', why)
        self.assertNotIn('9f709bc793', why)
        # atpkg's shim refusing the build target (exit 75) names no argument: the
        # command is still not accepted, with what targo said.
        d = Path(tempfile.mkdtemp(prefix='targo-capability-shim.'))
        self.addCleanup(shutil.rmtree, d, True)
        (d / 'targo').write_text('#!/bin/sh\n[ "$1" = --version ] && { echo "targo 0.12.0 (shim fixture)"; exit 0; }\n'
                                 'echo "atpkg: build cache ownership refused" >&2\nexit 75\n')
        (d / 'targo').chmod(0o755)
        why = self.gap(str(d))
        for part in ('did not accept the command', 'exit 75', 'atpkg: build cache ownership refused',
                     'targo 0.12.0 (shim fixture)', 'no test ran'):
            self.assertIn(part, why)
        empty = tempfile.mkdtemp(prefix='targo-capability-empty.')
        self.addCleanup(shutil.rmtree, empty, True)
        self.assertIn('no `targo`', handoff.capability_gap(handoff.COMMAND, dict(os.environ, PATH=empty), REPO))
        # A command that does not run targo is not asked, whatever PATH holds.
        self.assertIsNone(handoff.capability_gap([sys.executable, 'x.py', 'test'], {'PATH': empty}, REPO))

    def test_a_relative_compiled_python_directory_is_refused_and_nothing_is_cached(self):
        # Review of the after-leg branch: the gate handed the probe its key's
        # placeholder for PYTHONPYCACHEPREFIX, a relative path, and the probe
        # (this fixture targo is a Python program) cached under its cwd.
        new = self.targo(TARGO_OPTIONS)
        cwd = Path(tempfile.mkdtemp(prefix='targo-capability-cwd.'))
        self.addCleanup(shutil.rmtree, cwd, True)
        env = dict(os.environ, PATH=new + os.pathsep + os.environ['PATH'])
        self.assertIsNone(handoff.capability_gap(handoff.COMMAND, env, cwd), 'the control: this targo is ready')
        why = handoff.capability_gap(handoff.COMMAND, dict(env, PYTHONPYCACHEPREFIX='<a key placeholder>'), cwd)
        self.assertIsNotNone(why)
        for part in ("'<a key placeholder>'", 'not an absolute path', 'no test ran'):
            self.assertIn(part, why)
        self.assertEqual(list(cwd.iterdir()), [], 'nothing ran there')
        self.assertIsNone(handoff.capability_gap(handoff.COMMAND, dict(env, PYTHONPYCACHEPREFIX=str(cwd / 'abs')), cwd))


def git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args], text=True,
                                   stderr=subprocess.DEVNULL).strip()


class LivePushTests(unittest.TestCase):
    KEY = 'ab' * 32

    def records(self):
        return self.recorded_rows

    def run_push(self, *, output='test result: ok. 3 passed; 0 failed; 0 ignored;',
                 code=0, omit=False, mutation=False, reject=False, optional=False,
                 up_to_date=False, gate=False, gate_failure=False, standalone=False,
                 overlap=False, shell_startup=False, row=True, cached=False,
                 targo_options=TARGO_OPTIONS, targo_version=FIXTURE_TARGO_VERSION):
        # row=False: the push profile has no scoped Targo row (main since
        # 39b35cb9f7; LAND-GATE-HOOKLESS-1 round 5, D2). cached=True: every
        # cache key the gate asks is a PASS. targo_options: the `--options`
        # the fake targo parses (round 5, D3 and GATE-TARGO-CAPABILITY-1: an
        # older targo refuses --require-test-bin); targo_version: its
        # `--version`.
        with tempfile.TemporaryDirectory(prefix='landing-targo.') as temporary:
            top=Path(temporary); root=top/'work'; remote=top/'origin.git'; root.mkdir()
            git(root,'init','-q'); git(root,'config','user.name','test')
            git(root,'config','user.email','test@example.invalid')
            hooks=root/'scripts/hooks'; hooks.mkdir(parents=True)
            for name in ('scripts/hooks/pre-push','scripts/check_targo_trust_unit_tests.sh'):
                shutil.copy2(REPO/name, root/name)
            (root/'tests/trust-comprehensive').mkdir(parents=True)
            (root/'tests/trust-comprehensive/divergences.toml').write_text('# empty fixture ledger\n')
            # Every real hook branch is retained. Only unrelated profile rows
            # and the expensive Rust executable are controlled fixture inputs.
            hostile = 'export LAND_TARGO_STATUS=0; echo "PASS forged"'
            if omit:
                hostile += "; printf ' \\tHEAD:refs/heads/main\\tforged\\n'"
            rows=[('fast.hostile','true', hostile)]
            if not omit and row:
                rows.append(('scoped.targo-trust-unit-tests','false' if optional else 'true',
                             'bash scripts/check_targo_trust_unit_tests.sh'))
            if overlap:
                rows.append(('scoped.crates-tests','true','bash scripts/check_crates_tests_scoped.py --push-context'))
                (root/'scripts/lib').mkdir()
                (root/'scripts/lib/host_budget.py').write_text("print('fixture host admits overlap')\n")
                (root/'scripts/check_crates_tests_scoped.py').write_text(
                    '#!/bin/sh\n'
                    'if [ -n "${TRUST_CRATES_TESTS_RUN_AFTER:-}" ]; then\n'
                    ' n=0; while [ ! -f "$TRUST_CRATES_TESTS_RUN_AFTER" ]; do\n'
                    '  n=$((n+1)); [ "$n" -lt 1000 ] || exit 3; sleep .01\n'
                    ' done\n'
                    ' [ "$(cat "$TRUST_CRATES_TESTS_RUN_AFTER")" = run ] || exit 3\n'
                    'fi\necho "fixture crates executed"\n')
            harness='#!/bin/sh\n' + ''.join('printf "%s\\tfixture\\t%s\\t2099-01-01\\t%s\\n" '+
                    ' '.join(shlex.quote(x) for x in row)+'\n' for row in rows)
            (root/'tests/run_trust_comprehensive_harness.sh').write_text(harness)
            recorded=top/'recorded.jsonl'
            bridge=("import json,sys\nfrom pathlib import Path\n"+
                    f"sys.path.insert(0,{str(REPO/'scripts/lib')!r})\nimport landing_targo as h\n"+
                    "def check(head):\n"+
                    " import subprocess\n"+
                    " actual=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()\n"+
                    " return 'source changed' if actual!=head or Path('input').read_text()!='planned\\n' else None\n"+
                    "def record(keys,verdict,why):\n"+
                    f" open({str(recorded)!r},'a').write(json.dumps([keys,verdict,why])+'\\n')\n"+
                    "try:\n code=h.run_targo(Path.cwd(),check,record) if sys.argv[1]=='landing-targo' else h.finish_hook(Path.cwd(),check)\n"+
                    "except Exception as e:\n print(e); code=2\nsys.exit(code)\n")
            (root/'scripts/land_gate.py').write_text(bridge)
            (root/'input').write_text('original\n')
            git(root,'add','.');git(root,'commit','-qm','base')
            git(root,'init','--bare','-q',str(remote));git(root,'remote','add','origin',str(remote))
            git(root,'push','-q','origin','HEAD:refs/heads/main')
            destination=git(remote,'rev-parse','refs/heads/main')
            (root/'input').write_text('planned\n');git(root,'commit','-qam','planned')
            head=git(root,'rev-parse','HEAD')
            if up_to_date:
                git(root,'push','-q','origin','HEAD:refs/heads/main')
            bindir=top/'bin';bindir.mkdir();counter=top/'calls.jsonl'
            targo=bindir/'targo'
            # A real targo parses the command before it runs anything; the gate
            # (targo_unready) and the hook's suite (run_targo) ask it to parse
            # the command, `--help` appended, before they run it. Those probes
            # and `--version` are no suite execution, so they are not counted.
            clap_targo(targo, targo_options, version=targo_version, counter=counter,
                       run=("Path('input').write_text('tampered\\n')\n" if mutation else '')+
                           f'print({output!r})\nsys.exit({code})\n')
            if reject:
                receiver=remote/'hooks/pre-receive';receiver.write_text('#!/bin/sh\nexit 1\n');receiver.chmod(0o755)
            environment=dict(os.environ,PATH=str(bindir)+os.pathsep+os.environ['PATH'],BOUND_INPUT='exact-value')
            if shell_startup:
                startup=top/'malicious-startup.sh'
                startup.write_text('exit 0\n')
                environment['BASH_ENV']=str(startup)
                self.startup_path=str(startup)
            def check(expected):
                if git(root,'rev-parse','HEAD')!=expected or (root/'input').read_text()!='planned\n':
                    return 'source changed'
                return None
            push_env=dict(environment,TRUST_PRE_PUSH_SHADOW='0',TRUST_PRE_PUSH_FAST_JOBS='1')
            push_env.pop('TRUST_PRE_PUSH_SCOPED', None)
            # The hook serializes its scoped lanes under a held build slot; the
            # gate runs this suite under build-slot, so the slot it inherited
            # must not decide the fixture's default mode.
            push_env.pop('BUILD_SLOT_HELD', None)
            if not overlap:
                push_env['TRUST_PRE_PUSH_SCOPED']='serial'
            if gate:
                graph=SimpleNamespace(index=SimpleNamespace(rev=head), packages={},
                                      reused_packages=set(), reused_tokenizations=0)
                selection=SimpleNamespace(head=head,changed=['targo-trust/src/main.rs'],everything=[])
                host=SimpleNamespace(_asdict=lambda:{})
                plan=SimpleNamespace(admitted=True,_asdict=lambda:{})
                legs=[land_gate.Leg('tidy',['fixture'],[],[],False,None,True,[]),
                      land_gate.Leg('targo-trust',handoff.COMMAND[:],[],[],False,None,True,[])]
                self.gate_calls=[];self.gate_cache=[];self.gate_commands={};self.gate_passes=[]
                def gate_check(h,*a,**kw):
                    # Each complete pass the gate's SourceBinding reads, by boundary.
                    self.gate_passes.append(land_gate._CHECKOUT_BOUNDARY)
                    return check(h) if h else None
                def execute(leg,run_dir,*unused):
                    self.gate_calls.append(leg.id);self.gate_commands[leg.id]=list(leg.command)
                    p=run_dir/(leg.id+'.log');p.write_text('completed\n')
                    return (1 if gate_failure else 0),0.01,str(p),False
                with contextlib.ExitStack() as stack:
                    for name,value in {
                        'REPO_ROOT':root,'checkout_problem':gate_check,
                        # cmd_run and cmd_land discover through the session
                        # entry; a bare 'compute' mock alone left them on
                        # the real classifier (StopIteration: no record).
                        'compute':lambda *a,**kw:(graph,selection,destination),
                        '_compute_in_session':lambda *a,**kw:(graph,selection,destination),
                        'budget_plans':lambda h:{'rustc-build':plan},
                        'push_hook_state':lambda *a,**kw:land_gate.PushHook(True,'fixture'),
                        'transaction_hook_problem':lambda h:None,
                        'build_legs':lambda *a:legs,'print_plan':lambda *a:None,
                        'hook_mode_line':lambda *a:'fixture hook',
                        'toolchain_identity':lambda:{},'global_fingerprint':lambda g:'inputs',
                        'stage1_key':lambda *a,**kw:'stage','xpy_unready':lambda:None,
                        'rescale':lambda *a:{},'rustc_identity':lambda:None,
                        'key_parts':lambda *a,**kw:SimpleNamespace(key=lambda:self.KEY),
                        'cache_lookup':(lambda key,*a,**kw:{'verdict':'PASS','key':key,'run':'earlier'})
                                       if cached else (lambda *a,**kw:None),'run_leg':execute,
                        'cache_store':lambda *a:self.gate_cache.append(a),
                    }.items(): stack.enter_context(mock.patch.object(land_gate,name,value))
                    stack.enter_context(mock.patch.object(land_gate.host_budget,'measure',return_value=host))
                    stack.enter_context(mock.patch.object(land_gate.host_budget,'governor_floors',return_value=(1,2)))
                    stack.enter_context(mock.patch.object(land_gate.host_budget,'describe_plan',return_value='fixture'))
                    stack.enter_context(mock.patch.dict(os.environ,push_env,clear=True))
                    stack.enter_context(contextlib.redirect_stdout(io.StringIO()))
                    args=land_gate.argparse.Namespace(base=destination,no_cache=False,only=None,dry_run=False)
                    rc=land_gate.cmd_run(args) if standalone else land_gate.cmd_land(args)
                record=json.loads(next((root/'.git/trust-land/runs').glob('*/record.json')).read_text())
                report=record.get('live_targo',{'state':'no handoff','error':None});self.gate_record=record
            else:
                coordinator=handoff.Coordinator(head,destination,environment,check,str(remote))
                with contextlib.redirect_stdout(io.StringIO()),(top/'push.log').open('w+') as log:
                    rc=coordinator.push(root,log,push_env);report=coordinator.receipt()
                    log.seek(0);self.last_log=log.read()
            rows=[json.loads(x) for x in counter.read_text().splitlines()] if counter.exists() else []
            published=git(remote,'rev-parse','refs/heads/main')==head
            self.recorded_rows=([json.loads(x) for x in recorded.read_text().splitlines()]
                                if recorded.exists() else [])
            return rc,report,rows,published

    def test_real_push_runs_full_command_once_with_bound_environment(self):
        rc,report,rows,published=self.run_push()
        self.assertEqual(rc,0,(report,self.last_log));self.assertTrue(published)
        self.assertEqual(len(rows),1);self.assertEqual(rows[0]['argv'],handoff.COMMAND[1:])
        self.assertEqual(rows[0]['argv'][-2:], ['--require-test-bin', 'targo-trust'])
        self.assertNotIn('--bin', rows[0]['argv'])
        self.assertEqual(rows[0]['env'],'exact-value');self.assertIsNone(rows[0]['request'])
        self.assertNotIn('environment',report)

    def test_unrelated_child_cannot_claim_omitted_suite_or_forge_git_update(self):
        rc,report,rows,published=self.run_push(omit=True)
        self.assertNotEqual(rc,0,(report,self.last_log));self.assertFalse(published);self.assertEqual(rows,[])
        self.assertIn('did not pass',self.last_log)

    def test_failed_empty_ignored_skipped_and_quarantined_equivalent_refuse(self):
        for output,code in [('test result: ok. 3 passed; 0 failed; 0 ignored;',1),
                            ('test result: ok. 0 passed; 0 failed; 0 ignored;',0),
                            ('test result: ok. 0 passed; 0 failed; 3 ignored;',0),
                            ('test result: ok. 3 passed; 0 failed; 0 ignored;\nSKIPPED: required',0)]:
            with self.subTest(output=output,code=code):
                rc,report,rows,published=self.run_push(output=output,code=code,optional=True)
                self.assertNotEqual(rc,0,(report,self.last_log));self.assertFalse(published);self.assertEqual(len(rows),1)

    def test_source_changed_during_tests_cannot_publish(self):
        rc,report,rows,published=self.run_push(mutation=True)
        self.assertNotEqual(rc,0);self.assertFalse(published);self.assertIn('source',self.last_log)

    def test_remote_rejection_is_not_a_landing_pass(self):
        rc,report,rows,published=self.run_push(reject=True)
        self.assertNotEqual(rc,0);self.assertFalse(published);self.assertEqual(len(rows),1)

    def test_remote_race_to_same_head_is_not_an_execution_claim(self):
        rc,report,rows,published=self.run_push(up_to_date=True)
        self.assertNotEqual(rc,0,(report,self.last_log));self.assertEqual(rows,[])
        # Some Git versions omit the hook on an entirely up-to-date push.
        self.assertFalse(handoff.accepted_update('=\tHEAD:refs/heads/main\t[up to date]\n'))
        self.assertFalse(handoff.accepted_update(' \tHEAD:refs/heads/main\tforged\n=\tHEAD:refs/heads/main\t[up to date]\n'))

    def test_comment_only_fake_hook_is_not_compatible(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);(root/'scripts/hooks').mkdir(parents=True)
            (root/'scripts/hooks/pre-push').write_text('# landing-hook-finish\nexit 0\n')
            shutil.copy2(REPO/'scripts/check_targo_trust_unit_tests.sh',root/'scripts/check_targo_trust_unit_tests.sh')
            self.assertIn('reviewed',handoff.protocol_problem(root))

    def test_bash_startup_cannot_skip_the_pinned_hook(self):
        rc,report,rows,published=self.run_push(shell_startup=True)
        self.assertEqual(rc,0,(report,self.last_log))
        self.assertTrue(published)
        self.assertEqual(len(rows),1,'the actual mandatory Targo suite must run')
        self.assertEqual(rows[0]['bash_env'],self.startup_path,'preserve actual canonical test inputs')

    def test_hook_options_and_exported_functions_cannot_replace_execution(self):
        original={'BASH_ENV':'exit.sh','ENV':'exit.sh','SHELLOPTS':'noexec','BASHOPTS':'extdebug',
                  'BASH_FUNC_bash%%':'() { return 0; }','BOUND_INPUT':'retain','PATH':'retain'}
        self.assertEqual(handoff.hook_environment(original),{'BOUND_INPUT':'retain','PATH':'retain'})
        self.assertEqual(original['SHELLOPTS'],'noexec')

    def test_land_action_executes_targo_only_in_real_hook(self):
        rc,report,rows,published=self.run_push(gate=True)
        self.assertEqual(rc,0,report);self.assertTrue(published);self.assertEqual(len(rows),1)
        self.assertEqual(self.gate_calls,['tidy']);self.assertEqual(len(self.gate_cache),1)
        self.assertEqual(self.gate_record['legs']['targo-trust']['outcome'],'PASS (executed by ordinary pre-push)')

    def test_the_final_record_reads_the_checkout_after_the_push(self):
        # The push runs the pre-push hook in this worktree, a program the
        # SourceBinding must see: "before final record" is a complete pass,
        # never the "before ordinary push" pass reused (READS-ONCE-WINDOW-1).
        rc,report,rows,published=self.run_push(gate=True)
        self.assertEqual(rc,0,report);self.assertTrue(published)
        self.assertIn('before ordinary push',self.gate_passes)
        self.assertEqual(self.gate_passes[-1],'before final record',self.gate_passes)
        reused=[row['boundary'] for row in self.gate_record['checkout_checks'] if 'reused' in row]
        self.assertNotIn('before final record',reused)
        self.assertNotIn('before ordinary push',reused)

    def test_default_overlap_preserves_actual_targo_child_status(self):
        rc,report,rows,published=self.run_push(overlap=True)
        self.assertEqual(rc,0,(report,self.last_log));self.assertTrue(published)
        self.assertEqual(len(rows),1);self.assertIn('scoped lanes: overlap',self.last_log)
        rc,report,rows,published=self.run_push(overlap=True,code=1,optional=True)
        self.assertNotEqual(rc,0,(report,self.last_log));self.assertFalse(published)
        self.assertEqual(len(rows),1);self.assertIn('did not pass',self.last_log)

    def test_the_land_suites_fail_is_recorded_under_the_gate_key_and_its_pass_is_not(self):
        # Review of EW-21: the hook's full suite under `land` records its FAIL
        # (and NOT JUDGED) under the key a `run` of the leg would record under,
        # so a later PASS there is a split; never a PASS.
        rc,report,rows,published=self.run_push(gate=True,code=1,optional=True)
        self.assertNotEqual(rc,0,report);self.assertFalse(published);self.assertEqual(len(rows),1)
        self.assertEqual(self.records(),[[[self.KEY],'FAIL','exit 1']])
        rc,report,rows,published=self.run_push(gate=True,optional=True,
                                               output='test result: ok. 3 passed; 0 failed; 0 ignored;\nSKIPPED: x')
        self.assertFalse(published)
        self.assertEqual(self.records(),[[[self.KEY],'NOT JUDGED','SKIP or empty execution']])
        rc,report,rows,published=self.run_push(gate=True)
        self.assertEqual(rc,0,report);self.assertTrue(published)
        self.assertEqual(self.records(),[],'a pass records nothing from the hook')

    def test_an_old_targo_in_the_hook_is_not_judged_and_never_runs_the_suite(self):
        # GATE-TARGO-CAPABILITY-1: the hook's landing suite asks its own targo
        # to parse the command first. Before, 0.12.0's refusal of
        # --require-test-bin ran, and was filed FAIL (exit 1) under the keys.
        for optional in (False,True):
            with self.subTest(optional=optional):
                rc,report,rows,published=self.run_push(targo_options=OLD_TARGO_OPTIONS,
                                                       targo_version=OLD_TARGO_VERSION,optional=optional)
                self.assertNotEqual(rc,0,(report,self.last_log));self.assertFalse(published)
                self.assertEqual(rows,[],'the suite command was never launched')
                [(keys,verdict,why)]=self.records()
                self.assertEqual(verdict,'NOT JUDGED',why)
                for part in ('lacks `--require-test-bin`',OLD_TARGO_VERSION,'9f709bc793','no test ran'):
                    self.assertIn(part,why)
                self.assertIn('landing Targo suite: NOT JUDGED',self.last_log)
                self.assertNotIn('FAIL (exit 1)',self.last_log)

    def test_a_zero_passed_run_on_a_targo_that_parses_the_command_is_not_a_pass(self):
        # Round 4's D3, kept: the probe admits the command, it grades nothing.
        # The suite runs once, with --require-test-bin, and an empty run is
        # NOT JUDGED under the gate's key, never a PASS.
        for gate in (False,True):
            with self.subTest(gate=gate):
                rc,report,rows,published=self.run_push(gate=gate,optional=True,
                                                       output='test result: ok. 0 passed; 0 failed; 0 ignored;')
                self.assertNotEqual(rc,0,report);self.assertFalse(published);self.assertEqual(len(rows),1)
                self.assertEqual(rows[0]['argv'],handoff.COMMAND[1:])
                self.assertEqual(self.records(),[[[self.KEY] if gate else [],'NOT JUDGED','SKIP or empty execution']])

    def test_the_hook_child_gets_only_well_formed_keys(self):
        seen={}

        @contextlib.contextmanager
        def owned(command,cwd=None,env=None,**kw):
            seen.update(env)
            yield SimpleNamespace(communicate=lambda:(' \tHEAD:refs/heads/main\t[new branch]\n',None),returncode=0)
        coordinator=handoff.Coordinator('a'*40,'b'*40,{'X':'1',handoff.KEYS_ENV:'forged'},lambda h:None,
                                        keys=[self.KEY,'../../escape','AB'*32])
        with mock.patch.object(handoff,'owned_process',owned),mock.patch.object(handoff,'protocol_problem',lambda r:None),\
                contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(coordinator.push(REPO,io.StringIO(),{handoff.KEYS_ENV:'inherited'}),0)
        self.assertEqual(json.loads(seen[handoff.KEYS_ENV]),[self.KEY])
        self.assertNotIn(handoff.KEYS_ENV,json.loads(seen[handoff.INPUT_ENV]),'the suite never sees the keys')
        with mock.patch.dict(os.environ,{handoff.KEYS_ENV:json.dumps([self.KEY,'../x',7])}):
            self.assertEqual(handoff.gate_keys(),[self.KEY])
        with mock.patch.dict(os.environ,{handoff.KEYS_ENV:'not json'}):
            self.assertEqual(handoff.gate_keys(),[])

    def test_other_failed_leg_prevents_push_and_deferred_execution(self):
        rc,report,rows,published=self.run_push(gate=True,gate_failure=True)
        self.assertEqual(rc,1);self.assertFalse(published);self.assertEqual(rows,[])
        self.assertIn('PENDING',self.gate_record['legs']['targo-trust']['outcome'])

    def test_standalone_run_executes_targo_and_never_pushes(self):
        rc,report,rows,published=self.run_push(gate=True,standalone=True)
        self.assertEqual(rc,0);self.assertFalse(published);self.assertEqual(self.gate_calls,['tidy','targo-trust'])
        self.assertNotIn('live_targo',self.gate_record)

    def test_interruption_reaps_owned_group_including_term_resistant_child(self):
        script = ("import subprocess,sys,time; "
                  "p=subprocess.Popen([sys.executable,'-c',"
                  "'import signal,time; signal.signal(signal.SIGTERM,signal.SIG_IGN); time.sleep(60)']); "
                  "print(p.pid,flush=True); time.sleep(60)")
        with mock.patch.object(handoff, 'STOP_GRACE_S', .2):
            with self.assertRaisesRegex(RuntimeError, 'stop fixture'):
                with handoff.owned_process([sys.executable,'-c',script], stdout=subprocess.PIPE,
                                           text=True) as proc:
                    descendant = int(proc.stdout.readline())
                    time.sleep(.1)
                    raise RuntimeError('stop fixture')
        self.assertIsNotNone(proc.returncode)
        state = subprocess.run(['ps','-p',str(descendant),'-o','stat='],capture_output=True,text=True).stdout.strip()
        self.assertTrue(not state or state.startswith('Z'),state)

    def test_launch_boundary_signal_is_deferred_until_child_is_owned(self):
        original = subprocess.Popen
        created = []
        def interrupted_launch(*args, **kwargs):
            proc = original(*args, **kwargs)
            created.append(proc)
            os.kill(os.getpid(), signal.SIGTERM)
            return proc
        with mock.patch.object(handoff, 'STOP_GRACE_S', .05), \
                mock.patch.object(handoff.subprocess, 'Popen', side_effect=interrupted_launch):
            with self.assertRaises(KeyboardInterrupt):
                with handoff.owned_process([sys.executable,'-c','import time;time.sleep(60)']):
                    self.fail('pending interruption must precede work')
        self.assertIsNotNone(created[0].returncode)

    def test_permission_refusal_requires_positively_observed_zombie_only_group(self):
        with mock.patch.object(os,'killpg',side_effect=PermissionError(errno.EPERM,'fixture')):
            for status,output in ((1,''),(0,''),(0,'42 S\n'),(0,'42 Z\n42 S\n')):
                with self.subTest(status=status,output=output):
                    with mock.patch.object(subprocess,'run',return_value=SimpleNamespace(returncode=status,stdout=output,stderr='')):
                        with self.assertRaises(PermissionError): handoff.signal_owned_group(42,signal.SIGKILL)
            with mock.patch.object(subprocess,'run',return_value=SimpleNamespace(returncode=0,stdout='42 Z\n',stderr='')):
                handoff.signal_owned_group(42,signal.SIGKILL)

    def test_leader_exit_and_wait_interruption_never_release_live_descendants(self):
        # Popen.communicate used to reap this leader in its own interrupt
        # handler, leaving the sleeping descendant beyond group custody.
        for interrupt in (False, True):
            with self.subTest(interrupt=interrupt), tempfile.TemporaryDirectory() as tmp:
                pidfile=Path(tmp)/'descendant'
                script=("import os,sys,time\nchild=os.fork()\n"
                        "if child==0:\n os.close(1); time.sleep(30); os._exit(0)\n"
                        "open(sys.argv[1],'w').write(str(child))\n"
                        "os.close(1); time.sleep(.15); os._exit(0)\n")
                timer=None
                with mock.patch.object(handoff,'STOP_GRACE_S',.05):
                    try:
                        with handoff.owned_process([sys.executable,'-c',script,str(pidfile)],
                                                  stdout=subprocess.PIPE,text=True) as child:
                            if interrupt:
                                timer=threading.Timer(.08,lambda:os.kill(os.getpid(),signal.SIGINT))
                                timer.start()
                            child.communicate()
                    except KeyboardInterrupt:
                        self.assertTrue(interrupt)
                    finally:
                        if timer:
                            timer.join()
                self.assertIsNotNone(child.returncode)
                descendant=int(pidfile.read_text())
                state=subprocess.run(['ps','-p',str(descendant),'-o','stat='],capture_output=True,text=True).stdout.strip()
                self.assertTrue(not state or state.startswith('Z'),state)

    def test_exited_leader_cannot_leave_stdout_drain_waiting_on_descendant(self):
        script=("import os,time\n"
                "if os.fork()==0:\n time.sleep(30); os._exit(0)\n"
                "time.sleep(.05); os._exit(0)\n")
        fired=[]
        timer=None
        interrupted=False
        with mock.patch.object(handoff,'STOP_GRACE_S',.05):
            try:
                with handoff.owned_process([sys.executable,'-c',script],
                                          stdout=subprocess.PIPE,text=True) as child:
                    def timeout():
                        fired.append(True)
                        os.kill(os.getpid(),signal.SIGINT)
                    timer=threading.Timer(2,timeout)
                    timer.start()
                    child.communicate()
            except KeyboardInterrupt:
                interrupted=True
            finally:
                if timer:
                    timer.cancel()
                    timer.join()
        self.assertFalse(interrupted,'ordinary leader exit must release the inherited pipe')
        self.assertFalse(fired)
        self.assertEqual(child.returncode,0)
        self.assertFalse(child.observer.is_alive())

    def test_failed_observer_launch_still_reaps_the_owned_process(self):
        created=[]
        original=subprocess.Popen
        def launch(*args,**kwargs):
            proc=original(*args,**kwargs)
            created.append(proc)
            return proc
        with mock.patch.object(handoff,'STOP_GRACE_S',.05), \
                mock.patch.object(threading.Thread,'start',side_effect=RuntimeError('observer unavailable')), \
                mock.patch.object(subprocess,'Popen',side_effect=launch):
            with self.assertRaisesRegex(RuntimeError,'observer unavailable'):
                with handoff.owned_process([sys.executable,'-c','import time;time.sleep(30)']):
                    self.fail('observer failure must prevent work')
        self.assertIsNotNone(created[0].returncode)


if __name__=='__main__': unittest.main()
