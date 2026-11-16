#!/usr/bin/env python3
"""Pipe-advertisement and inert lifetime controls; no scheduler or SDK."""
import importlib.util
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest import mock

SCRIPT = Path(__file__).resolve().parents[1] / 'sdk_targo_transport_witness.py'
spec = importlib.util.spec_from_file_location('native_transport_lifetime_tested', SCRIPT)
helper = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helper)


class ParserAPI:
    @staticmethod
    def require(condition, message):
        if not condition:
            raise ValueError(message)


@unittest.skipUnless(os.name == 'posix', 'actual FIFO descriptor checks require Unix')
class PipeAdvertisements(unittest.TestCase):
    def setUp(self):
        self.read, self.write = os.pipe()
        self.addCleanup(os.close, self.read)
        self.addCleanup(os.close, self.write)
        self.pair = f'{self.read},{self.write}'

    def check_flags(self, flags):
        # These inert empty pipes carry no scheduler credits or SDK authority.
        with mock.patch.dict(os.environ, {'CARGO_MAKEFLAGS': flags}, clear=True):
            return helper.inherited_pipe(ParserAPI)

    def test_actual_helper_auth_and_fds_aliases_select_the_same_live_pipe(self):
        descriptors, identity = self.check_flags(
            f'-j --jobserver-fds={self.pair} --jobserver-auth={self.pair}')
        self.assertEqual(descriptors, (self.read, self.write))
        expected = []
        for fd in descriptors:
            info = os.fstat(fd)
            expected.extend((info.st_dev, info.st_ino))
        self.assertEqual(identity, expected)

    def test_one_alias_and_repeated_identical_aliases_remain_supported(self):
        for flags in (f'--jobserver-auth={self.pair}', f'--jobserver-fds={self.pair}',
                      f'--jobserver-auth={self.pair} --jobserver-auth={self.pair}'):
            with self.subTest(flags=flags):
                self.assertEqual(self.check_flags(flags)[0], (self.read, self.write))

    def test_conflicting_real_pipe_advertisements_refuse(self):
        other_read, other_write = os.pipe()
        try:
            with self.assertRaisesRegex(ValueError, 'consistent'):
                self.check_flags(f'--jobserver-fds={self.pair} '
                                 f'--jobserver-auth={other_read},{other_write}')
        finally:
            os.close(other_read)
            os.close(other_write)

    def test_missing_empty_and_malformed_advertisements_refuse(self):
        for flags in ('', '-j', '--jobserver-auth=broken', '--jobserver-fds=3,x'):
            with self.subTest(flags=flags), self.assertRaisesRegex(ValueError, 'advertisement'):
                self.check_flags(flags)

    def test_makeflags_alone_cannot_expand_the_selected_route(self):
        with mock.patch.dict(os.environ, {'MAKEFLAGS': f'--jobserver-auth={self.pair}'}, clear=True):
            with self.assertRaisesRegex(ValueError, 'advertisement'):
                helper.inherited_pipe(ParserAPI)

    def test_aliasing_descriptor_roles_still_refuses(self):
        with self.assertRaisesRegex(ValueError, 'roles alias'):
            self.check_flags(f'--jobserver-auth={self.read},{self.read}')

    def test_closed_descriptors_still_refuse(self):
        read, write = os.pipe()
        os.close(read)
        os.close(write)
        with self.assertRaises(OSError):
            self.check_flags(f'--jobserver-auth={read},{write}')

    def test_regular_file_descriptors_cannot_become_scheduler_pipes(self):
        with tempfile.TemporaryFile() as stream:
            other = os.dup(stream.fileno())
            try:
                with self.assertRaisesRegex(ValueError, 'live pipe'):
                    self.check_flags(f'--jobserver-auth={stream.fileno()},{other}')
            finally:
                os.close(other)


class Lifetime(unittest.TestCase):
    def test_signalled_or_normalized_exit_cannot_become_normal_refusal(self):
        helper.require_normal_retirement(0, [])
        helper.require_normal_retirement(75, [])
        for status, pending, expected in ((-15, [], 143), (130, [], 130), (0, [15], 143)):
            with self.assertRaises(helper.InterruptedCustody) as refused:
                helper.require_normal_retirement(status, pending)
            self.assertEqual(refused.exception.code, expected)

    @unittest.skipUnless(os.name == 'posix', 'actual owned process groups require Unix')
    def test_cooperative_signal_waits_for_child_retirement_before_return(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp).resolve()
            child = root / 'child.py'
            child.write_text('import os,signal,time\nfrom pathlib import Path\n'
                             'def done(*_):\n time.sleep(.1)\n Path(' + repr(str(root / 'retired'))
                             + ').write_text("retired")\n raise SystemExit(0)\n'
                             'signal.signal(signal.SIGTERM,done)\nPath(' + repr(str(root / 'ready'))
                             + ').write_text(str(os.getpid()))\nwhile True: time.sleep(.02)\n')
            driver = root / 'driver.py'
            driver.write_text('import importlib.util,json,os,sys\nfrom pathlib import Path\n'
                              'spec=importlib.util.spec_from_file_location("inert_helper",' + repr(str(SCRIPT)) + ')\n'
                              'm=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)\n'
                              'code,out,err,pending=m.observe_child(None,[sys.executable,"-I","-B",'
                              + repr(str(child)) + '],dict(os.environ),())\n'
                              'assert Path(' + repr(str(root / 'retired')) + ').is_file()\n'
                              'try:m.require_normal_retirement(code,pending)\n'
                              'except m.InterruptedCustody as e: print(json.dumps({"raw_child_exit":code,"outer_exit":e.code,"retired":True}));raise SystemExit(e.code)\n'
                              'raise AssertionError("interruption was normalized into success")\n')
            process = subprocess.Popen([sys.executable, '-I', '-B', str(driver)], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            try:
                deadline = time.monotonic() + 5
                while not (root / 'ready').exists() and time.monotonic() < deadline:
                    time.sleep(.01)
                self.assertTrue((root / 'ready').exists(), 'inert child never became ready')
                process.send_signal(signal.SIGTERM)
                out, err = process.communicate(timeout=5)
                self.assertEqual(process.returncode, 143, err.decode())
                self.assertEqual(json.loads(out), {'raw_child_exit': 0, 'outer_exit': 143, 'retired': True})
            finally:
                if process.poll() is None:
                    process.terminate(); process.wait(timeout=5)


if __name__ == '__main__':
    unittest.main()
