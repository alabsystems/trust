"""Real fixed-query transport controls, never an SDK/proof capability claim."""
from pathlib import Path
import fcntl, json, os, re, select, stat, subprocess, sys, tempfile, unittest

if len(sys.argv)>1 and sys.argv[1]=='--probe-child':
    try:
        auth=re.search(r'--jobserver-auth=(\d+),(\d+)',os.environ['CARGO_MAKEFLAGS'])
        assert auth is not None
        r,w=map(int,auth.groups()); a,b=os.fstat(r),os.fstat(w)
        assert stat.S_ISFIFO(a.st_mode) and stat.S_ISFIFO(b.st_mode)
        assert fcntl.fcntl(r,fcntl.F_GETFL)&os.O_ACCMODE==os.O_RDONLY
        assert fcntl.fcntl(w,fcntl.F_GETFL)&os.O_ACCMODE==os.O_WRONLY
        poll=select.poll();poll.register(r,select.POLLIN);assert not poll.poll(0)
        sdk=os.environ.get('ATERM_SDK_LEASE_V3')
        if sdk: assert stat.S_ISREG(os.fstat(int(sdk)).st_mode)
        sentinel=os.environ.get('PROBE_UNRELATED_FD')
        if sentinel:
            expected=tuple(map(int,os.environ['PROBE_UNRELATED_ID'].split(':')))
            try: actual=os.fstat(int(sentinel));assert (actual.st_dev,actual.st_ino)!=expected
            except OSError: pass
        print(json.dumps({'gnu_pipe':True,'gnu_extra_tokens':0,'sdk_present':bool(sdk),'sentinel_absent':True}))
    except (OSError,ValueError,KeyError,AssertionError):sys.exit(75)
    sys.exit(0)

EXE=Path(os.environ['TRUST_PROBE_SCHEDULER_TEST_BIN'])
PY=Path(sys.executable)
class ProbeTransport(unittest.TestCase):
    def command(self,env=None,plain=False,prefix=()):
        base=dict(os.environ)
        for key in ('CARGO_MAKEFLAGS','MAKEFLAGS','MFLAGS','CARGO_JOBSERVER_HANDOFF','ATERM_SDK_LEASE_V3'):base.pop(key,None)
        if env:base.update(env)
        return subprocess.run([str(EXE),*(['--plain'] if plain else []),*map(str,prefix),str(PY),'-I','-B',str(Path(__file__).resolve()),'--probe-child'],env=base,capture_output=True,close_fds=False)

    def test_old_plain_child_refuses_then_real_explicit_pipe_succeeds(self):
        before=self.command(plain=True);self.assertEqual(before.returncode,75,before.stderr)
        after=self.command();self.assertEqual(after.returncode,0,after.stderr)
        self.assertEqual(json.loads(after.stdout)['gnu_extra_tokens'],0)

    def test_nested_original_gnu_transport_stays_live(self):
        result=self.command(prefix=(EXE,));self.assertEqual(result.returncode,0,result.stderr)
        self.assertTrue(json.loads(result.stdout)['gnu_pipe'])

    def test_sdk_present_unrelated_sentinel_absent_and_parent_flags_unchanged(self):
        with tempfile.TemporaryDirectory() as root:
            sdk=os.open(str(Path(root)/'sdk'),os.O_CREAT|os.O_EXCL|os.O_RDWR,0o600)
            sentinel=os.open(str(Path(root)/'sentinel'),os.O_CREAT|os.O_EXCL|os.O_RDWR,0o600)
            try:
                os.set_inheritable(sdk,True);os.set_inheritable(sentinel,True)
                info=os.fstat(sentinel);before=[fcntl.fcntl(fd,fcntl.F_GETFD) for fd in (sdk,sentinel)]
                result=self.command({'ATERM_SDK_LEASE_V3':str(sdk),'PROBE_UNRELATED_FD':str(sentinel),'PROBE_UNRELATED_ID':f'{info.st_dev}:{info.st_ino}','PROBE_SET_SDK_CLOEXEC':'1'})
                self.assertEqual(result.returncode,0,result.stderr)
                row=json.loads(result.stdout);self.assertTrue(row['sdk_present']);self.assertTrue(row['sentinel_absent'])
                self.assertIn(b'PARENT_FD_FLAGS_UNCHANGED=true',result.stderr)
                self.assertEqual(before,[fcntl.fcntl(fd,fcntl.F_GETFD) for fd in (sdk,sentinel)])
            finally:os.close(sdk);os.close(sentinel)

    def test_malformed_or_partial_gnu_and_sdk_fail_before_probe(self):
        for env in ({'CARGO_MAKEFLAGS':'--jobserver-auth=not-a-transport'}, {'CARGO_JOBSERVER_HANDOFF':'malformed-no-gnu'}, {'ATERM_SDK_LEASE_V3':'999999'}):
            with self.subTest(env=env):
                result=self.command(env);self.assertEqual(result.returncode,75,result.stderr);self.assertEqual(result.stdout,b'')

if __name__=='__main__':unittest.main()
