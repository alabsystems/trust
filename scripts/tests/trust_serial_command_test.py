#!/usr/bin/env python3
"""Real owned GNU/descriptor/lifecycle controls, never a compiler or resource grant."""
from pathlib import Path
import fcntl,json,os,select,shlex,signal,stat,subprocess,sys,tempfile,time,unittest

EXECUTOR=Path(os.environ['TRUST_SERIAL_COMMAND_TEST_BIN'])
PROBE=r"""
import fcntl,json,os,re,select,stat,sys
flags=os.environ['CARGO_MAKEFLAGS'];pair=re.search(r'--jobserver-auth=(\d+),(\d+)',flags)
assert pair,flags
r,w=map(int,pair.groups());a,b=os.fstat(r),os.fstat(w)
assert stat.S_ISFIFO(a.st_mode) and stat.S_ISFIFO(b.st_mode)
assert fcntl.fcntl(r,fcntl.F_GETFL)&os.O_ACCMODE==os.O_RDONLY
assert fcntl.fcntl(w,fcntl.F_GETFL)&os.O_ACCMODE==os.O_WRONLY
assert not select.select([r],[],[],0)[0], 'zero-extra owner must have no token bytes'
identity=[a.st_dev,a.st_ino,b.st_dev,b.st_ino]
if len(sys.argv)>1:
 assert identity==json.loads(sys.argv[1]),'nested owner replaced the actual inherited transport'
print(json.dumps(identity),flush=True)
"""

class SerialCommandTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup);self.root=Path(self.tmp.name)
        self.env={k:v for k,v in os.environ.items() if k not in ('CARGO_MAKEFLAGS','MAKEFLAGS','MFLAGS','CARGO_JOBSERVER_HANDOFF','ATERM_SDK_LEASE_V3')}
        # The test itself runs inside actual canonical admission. Never turn a
        # string into a global resource grant or execute an SDK/compiler here.
        self.assertEqual(self.env.get('BUILD_SLOT_HELD'),'1')
        self.env['TMPDIR']=str(self.root)

    def command(self,argv,env,**kw):
        child=subprocess.Popen(argv,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,**kw)
        try:stdout,stderr=child.communicate(timeout=60)
        except subprocess.TimeoutExpired:
            child.send_signal(signal.SIGTERM)
            # Never force-kill the resource owner or drop its actual grant.
            stdout,stderr=child.communicate()
            self.fail('Owned control exceeded its hang detector; cooperative terminal '+str(child.returncode)+': '+stderr)
        return subprocess.CompletedProcess(argv,child.returncode,stdout,stderr)

    def run_child(self,args,env=None,**kw):
        return self.command([str(EXECUTOR),'--',*args],env or self.env,**kw)

    def test_real_empty_transport_and_exact_argv_exit_output(self):
        result=self.run_child([sys.executable,'-c',PROBE]);self.assertEqual(result.returncode,0,result.stderr)
        self.assertEqual(len(json.loads(result.stdout)),4)
        result=self.run_child(['/bin/bash','-c','printf "%s" "$1"; printf err >&2; exit 23','fixture','literal space;$value'])
        self.assertEqual((result.returncode,result.stdout,result.stderr),(23,'literal space;$value','err'))

    def test_nested_launcher_retains_the_actual_inherited_empty_transport(self):
        code=PROBE+"\nidentity=json.dumps(identity)\nos.execv(sys.argv[1],[sys.argv[1],'--',sys.executable,'-c',sys.argv[2],identity])\n"
        # Pass the inner executable/probe outside the first probe's optional
        # comparison slot, preserving the actual environment and descriptor pair.
        code=PROBE.replace("if len(sys.argv)>1:","if False:")+"\nos.execv(sys.argv[1],[sys.argv[1],'--',sys.executable,'-c',sys.argv[2],json.dumps(identity)])\n"
        result=self.run_child([sys.executable,'-c',code,str(EXECUTOR),PROBE])
        self.assertEqual(result.returncode,0,result.stderr)
        lines=result.stdout.splitlines();self.assertEqual(len(lines),2);self.assertEqual(lines[0],lines[1])

    def test_malformed_inherited_transport_refuses_before_command(self):
        marker=self.root/'ran'
        for key,value in [('CARGO_MAKEFLAGS','-j --jobserver-auth=not-a-pair'),('MAKEFLAGS','-j --jobserver-auth=9000,9001'),('CARGO_JOBSERVER_HANDOFF','partial-without-GNU-auth')]:
            with self.subTest(key=key):
                result=self.run_child(['/usr/bin/touch',str(marker)],dict(self.env,**{key:value}))
                self.assertEqual(result.returncode,75,result.stderr);self.assertFalse(marker.exists())

    def test_invalid_sdk_locator_and_unadmitted_invocation_refuse(self):
        marker=self.root/'ran'
        for extra in [{'ATERM_SDK_LEASE_V3':'invalid'},{'ATERM_SDK_LEASE_V3':'9000'},{'BUILD_SLOT_HELD':'0'}]:
            with self.subTest(extra=extra):
                result=self.run_child(['/usr/bin/touch',str(marker)],dict(self.env,**extra))
                self.assertEqual(result.returncode,75,result.stderr);self.assertFalse(marker.exists())

    def test_transparent_original_sdk_descriptor_through_bash(self):
        # Disposable regular0600 descriptor metadata: tests inheritance only,
        # not authenticated SDK custody or compiler acceptance.
        lease=self.root/'lease';lease.write_text('owned descriptor');lease.chmod(0o600)
        with lease.open('rb') as stream:
            fd=stream.fileno();before=os.fstat(fd)
            code="import os,sys; s=os.fstat(int(sys.argv[1])); print(s.st_dev,s.st_ino); assert os.read(int(sys.argv[1]),99)==b'owned descriptor'"
            result=self.run_child(['/bin/bash','-c','exec "$@"','fixture',sys.executable,'-c',code,str(fd)],dict(self.env,ATERM_SDK_LEASE_V3=str(fd)),pass_fds=(fd,))
            self.assertEqual(result.returncode,0,result.stderr);self.assertEqual(result.stdout.strip(),f'{before.st_dev} {before.st_ino}')

    def test_term_waits_for_child_and_cannot_convert_interruption_to_zero(self):
        ready=self.root/'ready';noted=self.root/'noted';release=self.root/'release'
        code="import pathlib,signal,time,sys; ready,noted,release=map(pathlib.Path,sys.argv[1:]); signal.signal(signal.SIGTERM,lambda *_:noted.write_text('TERM')); ready.write_text('ready');\nwhile not release.exists(): time.sleep(.01)\n"
        child=subprocess.Popen([str(EXECUTOR),'--',sys.executable,'-c',code,str(ready),str(noted),str(release)],env=self.env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
        self.addCleanup(lambda: child.wait(timeout=10))
        try:
            deadline=time.monotonic()+10
            while not ready.exists() and time.monotonic()<deadline:time.sleep(.01)
            self.assertTrue(ready.exists());child.send_signal(signal.SIGTERM)
            while not noted.exists() and time.monotonic()<deadline:time.sleep(.01)
            self.assertTrue(noted.exists());self.assertIsNone(child.poll(),'owner dropped before child terminal')
        finally:release.write_text('finish')
        stdout,stderr=child.communicate();self.assertEqual(child.returncode,143,stderr)

    def test_term_retains_owner_until_same_group_delayed_descendant_is_gone(self):
        ready=self.root/'descendant-ready';noted=self.root/'descendant-noted';release=self.root/'release-descendant'
        descendant="import pathlib,signal,time,sys; ready,noted,release=map(pathlib.Path,sys.argv[1:]); signal.signal(signal.SIGTERM,lambda *_:noted.write_text('TERM')); ready.write_text('ready');\nwhile not release.exists(): time.sleep(.01)\n"
        leader="import os,pathlib,subprocess,sys,time; pathlib.Path(sys.argv[-1]).write_text(str(os.getpid())); subprocess.Popen([sys.executable,'-c',sys.argv[1],*sys.argv[2:-1]]); time.sleep(60)"
        child=subprocess.Popen([str(EXECUTOR),'--',sys.executable,'-c',leader,descendant,str(ready),str(noted),str(release),str(self.root/'leader.pid')],env=self.env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
        try:
            deadline=time.monotonic()+10
            while not ready.exists() and time.monotonic()<deadline:time.sleep(.01)
            self.assertTrue(ready.exists());child.send_signal(signal.SIGTERM)
            while not noted.exists() and time.monotonic()<deadline:time.sleep(.01)
            self.assertTrue(noted.exists())
            leader_pid=int((self.root/'leader.pid').read_text())
            while time.monotonic()<deadline:
                try:os.kill(leader_pid,0)
                except ProcessLookupError:break
                time.sleep(.01)
            else:self.fail('Foreground child was not actually reaped')
            self.assertIsNone(child.poll(),'GNU owner dropped while same-PG descendant outlived reaped leader')
        finally:release.write_text('finish')
        stdout,stderr=child.communicate();self.assertEqual(child.returncode,143,stderr)

    def test_real_owner_survives_all_seven_hermetic_tool_start_environments(self):
        source=Path(__file__).resolve().parents[1]/'promote-toolchain.sh';text=source.read_text()
        def function(name):
            body=text[text.index(name+'() {'):];return body[:body.index('\n}\n')+3]
        script='die() { exit 1; }\n'+'\n'.join(function(n) for n in ('serial_executor','serial_command','tool_start_run'))+'\ntool_start_run "$@"\n'
        driver=self.root/'tool-start.sh';driver.write_text(script)
        tc=self.root/'sdk';(tc/'bin').mkdir(parents=True)
        observe=PROBE.replace("if len(sys.argv)>1:","if False:")+"\nassert 'RUSTFLAGS' not in os.environ and 'RUSTC' not in os.environ\nassert os.environ['BUILD_SLOT_CPU_PROTOCOL']==sys.argv[1]\nassert os.environ['CARGO_BUILD_JOBS']==sys.argv[2]\n"
        for name in ('tippy-driver','tippy','trust-miri','trustdoc','trustfmt'):
            path=tc/'bin'/name
            path.write_text('#!/bin/sh\nexec '+shlex.quote(sys.executable)+' -c '+shlex.quote(observe)+' '+shlex.quote(self.env['BUILD_SLOT_CPU_PROTOCOL'])+' '+shlex.quote(self.env['CARGO_BUILD_JOBS'])+'\n');path.chmod(0o700)
        work=self.root/'work'
        for path in ('home','tmp','cargo-home','pkg','pkg-lint','out'):(work/path).mkdir(parents=True,exist_ok=True)
        for row in ('tippy-driver.clean','tippy-driver.lint','tippy.frontend','tippy.frontend-lint','trust-miri.session','trustdoc.session','trustfmt.format'):
            with self.subTest(row=row):
                env=dict(self.env,TRUST_TOOLCHAIN_SERIAL_COMMAND=str(EXECUTOR),RUSTFLAGS='inert-must-not-leak',RUSTC='inert-must-not-leak')
                result=self.command(['/bin/bash',str(driver),row,str(tc),str(work),str(work/'out')],env)
                self.assertEqual(result.returncode,0,result.stderr)
                self.assertEqual(len(json.loads(result.stdout.splitlines()[0])),4)

if __name__=='__main__':unittest.main()
