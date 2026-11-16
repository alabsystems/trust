#!/usr/bin/env python3
"""Actual-process cancellation regressions; all children belong to each fixture."""
from __future__ import annotations

import json
import os
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]

CHILD = r'''
import json,os,signal,sys,time
from pathlib import Path
root=Path(sys.argv[1]);role=sys.argv[2];mode=sys.argv[3]
def stop(sig,frame):
 (root/(role+'-signal.json')).write_text(json.dumps({'signal':sig}))
 sys.exit(0)
for sig in (signal.SIGINT,signal.SIGTERM,signal.SIGHUP):
 signal.signal(sig,signal.SIG_IGN if mode=='ignore' else stop)
identity=root/(role+'-identity.json');temporary=root/(role+'-identity.tmp')
temporary.write_text(json.dumps({'pid':os.getpid(),'pgid':os.getpgid(0),'role':role,'blocked':list(signal.pthread_sigmask(signal.SIG_BLOCK, []))}));temporary.replace(identity)
if role=='leg' and mode in ('flood','blocked-output','merged-output'):
 while True:os.write(1,b'sustained output\n'*128)
if role=='leg' and mode=='partial':os.write(1,b'partial without newline')
if role=='leg' and mode=='output-error':print('a complete output line',flush=True)
if role=='leg' and mode=='leftover':
 import subprocess
 subprocess.Popen([sys.executable,'-B',str(root/'child.py'),str(root),'grandchild','quiet'])
 deadline=time.monotonic()+3
 while not (root/'grandchild-identity.json').exists():
  if time.monotonic()>deadline:raise TimeoutError('grandchild readiness')
  time.sleep(.01)
 sys.exit(0)
if role=='leg' and mode=='normal':
 os.write(1,b'first\r\nsecond\rpartial\xff');sys.exit(0)
while True:time.sleep(.05)
'''

DRIVER = r'''
import io,json,os,signal,subprocess,sys,time,types
from pathlib import Path
root=Path(sys.argv[1]);source=Path(sys.argv[2]);mode=sys.argv[3]
sys.path[:0]=[str(source/'scripts'),str(source/'scripts/lib')]
import land_gate
land_gate.REPO_ROOT=root
real_popen=subprocess.Popen;spawned=[]
def spawn(*args,**kwargs):
 if mode=='governor-error' and args[0][0]=='bash':
  deadline=time.monotonic()+3
  while not (root/'leg-identity.json').exists():
   if time.monotonic()>deadline:raise TimeoutError('leg readiness')
   time.sleep(.01)
  raise OSError('fixture governor start failure')
 child=real_popen(*args,**kwargs)
 if kwargs.get('start_new_session'):spawned.append(child)
 if mode=='spawn-signal' and len(spawned)==1:os.kill(os.getpid(),signal.SIGTERM)
 return child
land_gate.subprocess.Popen=spawn
class BrokenLog(io.StringIO):
 def write(self,data):
  if not data.startswith('$ '):raise OSError('fixture output write failure')
  return super().write(data)
old={sig:signal.getsignal(sig) for sig in (signal.SIGINT,signal.SIGTERM,signal.SIGHUP)}
old_stdout_blocking=os.get_blocking(sys.stdout.fileno())
race_injected=False
if mode=='getpgid-race':
 original_getpgid=os.getpgid
 def exit_before_getpgid(pid):
  global race_injected
  if spawned and pid==spawned[0].pid and not race_injected:
   race_injected=True;os.kill(pid,signal.SIGTERM)
   deadline=time.monotonic()+3
   while not land_gate.landing_targo.wait_child_exit(pid,nohang=True):
    if time.monotonic()>deadline:raise TimeoutError('own race child terminal')
    time.sleep(.01)
   raise ProcessLookupError('forced live-to-terminal Darwin getpgid race')
  return original_getpgid(pid)
 os.getpgid=exit_before_getpgid
if mode in ('blocked-output','merged-output','outer-output'):
 original_write=os.write
 def record_backpressure(fd,data):
  try:return original_write(fd,data)
  except BlockingIOError:
   if fd==sys.stdout.fileno():(root/'output-blocked').write_text('actual EAGAIN')
   raise
 os.write=record_backpressure
if mode=='restore-signal':
 original_signal=signal.signal;injected=False
 def signal_while_restoring(sig,handler):
  global injected
  result=original_signal(sig,handler)
  if not injected and sig==signal.SIGINT and handler==old[sig]:
   injected=True;os.kill(os.getpid(),signal.SIGINT)
  return result
 signal.signal=signal_while_restoring
if mode=='selector-error':
 original=land_gate.selectors.DefaultSelector
 class BrokenSelector(original):
  def register(self,*args,**kwargs):raise OSError('fixture selector registration failure')
 land_gate.selectors.DefaultSelector=BrokenSelector
if mode=='handler-error':
 original_signal=signal.signal;refused=False
 def refuse_once(sig,handler):
  global refused
  if sig==signal.SIGTERM and not refused:
   refused=True;raise OSError('fixture handler install failure')
  return original_signal(sig,handler)
 signal.signal=refuse_once
if mode=='group-observer-error':
 def failed_members(self):raise OSError('fixture process-group observation failure')
 land_gate._OwnedGroup.members=failed_members
 def body_failure(*args,**kwargs):raise OSError('fixture body failure before group observation failure')
 land_gate._stream_leg=body_failure
leg=land_gate.Leg('fixture',[],[],[],False,None,True,[])
code=2;result={}
try:
 with (root/'leg.log').open('w') as raw:
  log=BrokenLog() if mode=='output-error' else raw
  def run_fixture(_args=None):
   return land_gate._run_one(leg,[sys.executable,'-B',str(root/'child.py'),str(root),'leg',mode],log,{},(1,2),root)
  if mode=='outer-output':
   land_gate.git=lambda *args,**kwargs:''
   # This synthetic root has no Git inputs. Exercise the real outer stdout
   # cancellation scope after the separately tested checkout boundary.
   land_gate.checkout_problem=lambda *args,**kwargs:None
   land_gate.host_budget.measure=lambda:types.SimpleNamespace()
   land_gate.host_budget.plan=lambda *args,**kwargs:types.SimpleNamespace(admitted=True)
   land_gate.host_budget.describe_plan=lambda *args:'buffered-looking plan prefix '*4096
   rc=land_gate.main(['run'])
  else:
   land_gate.cmd_run=run_fixture
   rc=land_gate.main(['run']) if mode=='merged-output' else run_fixture()
  result={'return_code':rc};code=rc
  if rc==0:(root/'would-credit-pass').write_text('PASS')
except BaseException as error:
 sig=getattr(error,'signum',None)
 result={'exception':type(error).__name__,'signum':sig,'message':str(error)}
 code=128+sig if sig is not None else 2
finally:
 result['race_injected']=race_injected
 result['stdout_blocking_restored']=os.get_blocking(sys.stdout.fileno())==old_stdout_blocking
 result['handlers_restored']=all(signal.getsignal(sig)==value for sig,value in old.items())
 result['children']=[{'pid':p.pid,'returncode':p.returncode,'pipe_closed':p.stdout is None or p.stdout.closed,'argv':[str(a) for a in p.args]} for p in spawned]
 (root/'driver-result.json').write_text(json.dumps(result))
sys.exit(code)
'''


# How long the driver may take to reach the point the test signals it at: a
# new interpreter imports the gate and, in the mode that runs the real `run`,
# its checkout scope asks atpkg to verify the managed pack before the native
# reader starts. That is the fixture's start-up, not the property under test:
# what is asserted is what happens after the signal, and those bounds are
# unchanged. At 5 s this wait failed on aarch64-apple-darwin (2026-11-14, load
# 30 to 80 on 18 CPUs: readiness by hand after 6.84 s, 10.43 s and 12.9 s).
FIXTURE_READINESS_SECONDS = 60


class CancellationProcesses(unittest.TestCase):
    def live(self, root, role):
        path = root / (role + '-identity.json')
        if not path.exists():
            return None
        identity = json.loads(path.read_text())
        observed = subprocess.run(['/bin/ps', '-p', str(identity['pid']), '-o', 'pid=,stat=,command='],
                                  capture_output=True, text=True, timeout=2)
        if observed.returncode == 1 and not observed.stdout.strip():
            return None
        self.assertEqual(observed.returncode, 0, observed.stderr)
        self.assertIn(str(root / 'child.py'), observed.stdout)
        self.assertEqual(int(observed.stdout.split()[0]), identity['pid'])
        identity['observed_ps'] = observed.stdout
        return identity

    def exercise(self, mode='quiet', sig=signal.SIGTERM, repeat=False, governor=True):
        with tempfile.TemporaryDirectory(prefix='land-gate-cancel.') as tmp:
            root = Path(tmp)
            (root / 'child.py').write_text(CHILD)
            (root / 'driver.py').write_text(DRIVER)
            if governor:
                scripts = root / 'scripts'
                scripts.mkdir()
                (scripts / 'build-mem-governor.sh').write_text(
                    'exec "' + sys.executable + '" -B "' + str(root / 'child.py') + '" "' + str(root) + '" governor quiet\n')
            driver = None
            sentinel = subprocess.Popen([sys.executable, '-B', str(root / 'child.py'), str(root),
                                         'sentinel', 'quiet'], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                                        start_new_session=True)
            try:
                with (root / 'driver.stdout').open('w') as out, (root / 'driver.stderr').open('w') as err:
                    driver = subprocess.Popen([sys.executable, '-B', str(root / 'driver.py'), str(root),
                                               str(REPO), mode], stdout=subprocess.PIPE if mode in ('blocked-output', 'merged-output', 'outer-output') else out,
                                               stderr=subprocess.STDOUT if mode in ('merged-output', 'outer-output') else err, start_new_session=True)
                    if mode in ('quiet', 'partial', 'ignore', 'flood', 'blocked-output', 'merged-output', 'outer-output', 'restore-signal', 'getpgid-race'):
                        deadline = time.monotonic() + FIXTURE_READINESS_SECONDS
                        wanted = [] if mode == 'outer-output' else ['leg'] + (['governor'] if governor else [])
                        while not (all((root / (role + '-identity.json')).exists() for role in wanted)
                                   and (mode not in ('blocked-output', 'merged-output', 'outer-output') or (root / 'output-blocked').exists())):
                            self.assertIsNone(driver.poll(), {
                                'stderr': (root / 'driver.stderr').read_text(),
                                'result': ((root / 'driver-result.json').read_text()
                                           if (root / 'driver-result.json').exists() else None),
                            })
                            self.assertLess(time.monotonic(), deadline, 'fixture readiness')
                            time.sleep(.01)
                        os.kill(driver.pid, sig)
                        if repeat:
                            time.sleep(.1)
                            os.kill(driver.pid, signal.SIGINT)
                    code = driver.wait(timeout=12)
                    if driver.stdout is not None:
                        driver.stdout.close()
                result_path = root / 'driver-result.json'
                result = json.loads(result_path.read_text()) if result_path.exists() else {}
                live_children = {role: self.live(root, role) for role in ('leg', 'governor', 'grandchild')}
                self.assertIsNone(sentinel.poll(), 'unrelated fixture sentinel was signaled')
                self.assertFalse((root / 'sentinel-signal.json').exists())
                self.assertEqual(result.get('handlers_restored'), True,
                                 {'code': code, 'result': result, 'live_children': live_children,
                                  'stderr': (root / 'driver.stderr').read_text()})
                self.assertTrue(result['stdout_blocking_restored'])
                if mode == 'getpgid-race':
                    self.assertTrue(result['race_injected'])
                for role, identity in live_children.items():
                    self.assertIsNone(identity, {'role': role, 'identity': identity, 'driver': result})
                for child in result['children']:
                    self.assertIsNotNone(child['returncode'], 'direct child not reaped')
                    self.assertTrue(child['pipe_closed'])
                if mode in ('quiet', 'partial', 'ignore', 'flood', 'blocked-output', 'merged-output', 'outer-output', 'restore-signal', 'getpgid-race', 'spawn-signal'):
                    self.assertEqual(code, 128 + sig)
                    if mode not in ('merged-output', 'outer-output'):
                        self.assertEqual(result.get('signum'), sig)
                    self.assertFalse((root / 'would-credit-pass').exists(), 'cancellation credited PASS')
                    if mode != 'ignore' and (root / 'leg-signal.json').exists():
                        self.assertEqual(json.loads((root / 'leg-signal.json').read_text())['signal'], sig)
                elif mode in ('governor-error', 'output-error', 'selector-error', 'handler-error'):
                    self.assertEqual(code, 2)
                    self.assertEqual(result.get('exception'), 'OSError')
                    self.assertFalse((root / 'would-credit-pass').exists())
                elif mode in ('leftover', 'group-observer-error'):
                    self.assertEqual(code, 2, result)
                    # A pipe a descendant retains after the leader's observed
                    # exit is a cleanup failure after that exit (review of
                    # EW-1): still a refusal, never a PASS for exit 0.
                    self.assertEqual(result.get('exception'),
                                     'LegCleanupFailed' if mode == 'leftover' else 'RuntimeError')
                    self.assertFalse((root / 'would-credit-pass').exists())
                else:
                    self.assertEqual(code, 0, result)
                    self.assertEqual((root / 'leg.log').read_text().split('\n', 1)[1], 'first\nsecond\npartial\ufffd')
                    self.assertEqual((root / 'driver.stdout').read_text(),
                                     '  [fixture] first\n  [fixture] second\n  [fixture] partial\ufffd')
                return result
            finally:
                # Baseline failures deliberately leak. Stop only exact fixture
                # identities, while their unique argv still authenticates them.
                if driver is not None and driver.poll() is None:
                    driver.kill()
                    driver.wait(timeout=3)
                if sentinel.poll() is None:
                    sentinel.terminate()
                    sentinel.wait(timeout=3)
                for role in ('governor', 'leg', 'grandchild'):
                    identity = self.live(root, role)
                    if identity is not None:
                        os.kill(identity['pid'], signal.SIGKILL)
                        deadline = time.monotonic() + 3
                        while self.live(root, role) is not None:
                            self.assertLess(time.monotonic(), deadline, 'own fixture cleanup')
                            time.sleep(.02)

    def test_quiet_term_reaps_leg_and_governor_without_pass_credit(self):
        self.exercise()

    def test_quiet_int_and_hup_forward_first_signal(self):
        for sig in (signal.SIGINT, signal.SIGHUP):
            with self.subTest(signal=sig):
                self.exercise(sig=sig)

    def test_unread_stdout_backpressure_does_not_block_cleanup(self):
        self.exercise(mode='blocked-output')

    def test_real_cmd_run_plan_output_is_cancellable_before_any_child(self):
        result = self.exercise(mode='outer-output')
        # A run's checkout scope starts its native tracked-input reader where
        # the host has one (ac0bd4793d; Darwin arm64 with a managed Trust
        # pack). It is that scope's own child and is retired with it, which
        # exercise() has checked for every child. Nothing else may start before
        # the plan is printed: no leg, no governor.
        reader = ['source-check', '--tracked-inputs']
        self.assertEqual([child for child in result['children'] if child['argv'][1:] != reader], [])

    def test_merged_unread_stdout_stderr_still_allows_main_to_exit(self):
        self.exercise(mode='merged-output')

    def test_group_observation_failure_still_reaps_both_children(self):
        self.exercise(mode='group-observer-error')

    def test_pending_signal_cannot_interrupt_handler_restoration(self):
        self.exercise(mode='restore-signal')

    def test_continuous_output_does_not_starve_cancellation(self):
        self.exercise(mode='flood')

    def test_partial_line_does_not_block_cancellation(self):
        self.exercise(mode='partial')

    def test_second_signal_preserves_first_and_bounds_ignoring_child_cleanup(self):
        self.exercise(mode='ignore', repeat=True)

    def test_terminal_transition_during_getpgid_does_not_skip_cleanup(self):
        self.exercise(mode='getpgid-race')

    def test_signal_before_popen_returns_does_not_lose_child(self):
        self.exercise(mode='spawn-signal')

    def test_governor_launch_failure_cleans_started_leg(self):
        self.exercise(mode='governor-error')

    def test_log_write_failure_cleans_both_children(self):
        self.exercise(mode='output-error')

    def test_selector_registration_failure_cleans_both_children(self):
        self.exercise(mode='selector-error')

    def test_handler_install_failure_restores_handlers_without_spawning(self):
        result = self.exercise(mode='handler-error')
        self.assertEqual(result['children'], [])

    def test_zero_exit_with_live_pipe_holder_cannot_credit_pass(self):
        self.exercise(mode='leftover')

    def test_normal_newlines_partial_utf8_and_handlers_are_preserved(self):
        self.exercise(mode='normal')


class CancellationCredit(unittest.TestCase):
    def test_recorded_cancellation_refuses_cache_credit_and_restores_handlers(self):
        sys.path[:0] = [str(REPO / 'scripts'), str(REPO / 'scripts/lib')]
        import land_gate
        from unittest.mock import patch
        before = {sig: signal.getsignal(sig) for sig in land_gate._CANCEL_SIGNALS}
        with tempfile.TemporaryDirectory(prefix='land-cancel-cache.') as tmp:
            root = Path(tmp)
            with patch.object(land_gate, 'cache_dir', return_value=root):
                with self.assertRaises(land_gate.GateCancelled):
                    with land_gate._cancellation_scope() as cancellation:
                        cancellation.record(signal.SIGTERM, None)
                        land_gate.cache_store('fixture', {'run': 'cancelled'})
            self.assertEqual(list(root.iterdir()), [])
        self.assertEqual(before, {sig: signal.getsignal(sig) for sig in before})


if __name__ == '__main__':
    unittest.main()
