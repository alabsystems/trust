#!/usr/bin/env python3
"""Actual native manager selection, distinct from the build compiler/frontend."""
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[2]
class ExplicitManager(unittest.TestCase):
    def fixture(self):
        temp=tempfile.TemporaryDirectory(prefix='xpy-explicit-manager-');self.addCleanup(temp.cleanup)
        root=Path(temp.name).resolve();(root/'src/bootstrap').mkdir(parents=True)
        shutil.copyfile(ROOT/'x.py',root/'x.py')
        (root/'src/bootstrap/bootstrap.py').write_text("from pathlib import Path\ndef main(): Path('ran').write_text('actual leased bootstrap body')\n")
        native=root/'build/bootstrap/debug/bootstrap';native.parent.mkdir(parents=True)
        native.write_text('#!/bin/sh\ntouch unexpected-fallback\nexit 97\n');native.chmod(0o755)
        return root
    def launch(self,root,manager):
        env=os.environ.copy();env['TRUST_BUILD_TREE_MANAGER_TARGO']=manager
        env['TRUST_BUILD_LOCK_WAIT']='0';env.pop('TRUST_BUILD_LOCK_TOKEN',None)
        return subprocess.run([sys.executable,'-B',str(root/'x.py'),'test'],cwd=root,env=env,capture_output=True,timeout=30)
    def test_actual_v2_manager_owns_and_retires_the_build(self):
        manager=os.environ.get('TARGO_COMPONENT_MANAGER')
        self.assertTrue(manager,'explicit actual manager needed')
        root=self.fixture();result=self.launch(root,str(Path(manager).resolve()))
        self.assertEqual(result.returncode,0,result.stderr)
        self.assertTrue((root/'ran').is_file());self.assertFalse((root/'unexpected-fallback').exists())
        status=subprocess.run([manager,'trust','repo','lock','status','--repo-root',str(root)],capture_output=True,timeout=10)
        self.assertEqual(status.returncode,0,status.stderr)
    def test_explicit_unavailable_manager_does_not_fall_back(self):
        root=self.fixture();result=self.launch(root,str(root/'absent'))
        self.assertNotEqual(result.returncode,0);self.assertFalse((root/'ran').exists())
        self.assertFalse((root/'unexpected-fallback').exists())
    def test_actual_v1_manager_does_not_fall_back(self):
        manager=os.environ.get('TARGO_COMPONENT_V1_MANAGER')
        self.assertTrue(manager,'explicit actual v1 manager needed')
        root=self.fixture();result=self.launch(root,str(Path(manager).resolve()))
        self.assertNotEqual(result.returncode,0);self.assertIn(b'no fallback',result.stderr)
        self.assertFalse((root/'ran').exists());self.assertFalse((root/'unexpected-fallback').exists())
if __name__=='__main__':unittest.main()
