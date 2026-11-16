#!/usr/bin/env python3
"""Tiny real flock/process controls; never use the global gate or host probes."""

import fcntl
import importlib.machinery
import importlib.util
import json
import os
from pathlib import Path
import py_compile
import select
import shlex
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import time
import unittest
from unittest import mock
from urllib.parse import quote


SCRIPT = Path(__file__).resolve().parents[1] / "build-slot"


def isolate_resource_environment(test):
    """Private OS models do not import an enclosing native owner's transport.

    Explicit fixture advertisements are added after this isolation. Genuine
    owner coverage belongs to resource_fds_test's separate native controls.
    """
    names = {"ATERM_SDK_LEASE_V3", "ATERM_WORKLOAD_HOST_STORE_FD_V1",
             "TRUST_CPU_IMPLICIT_FD", "ATERM_WORKLOAD_CPU_FDS_V1",
             "BUILD_SLOT_FENCE_FDS", "CARGO_MAKEFLAGS", "MAKEFLAGS", "MFLAGS",
             "CARGO_JOBSERVER_HANDOFF"}
    patcher = mock.patch.dict(os.environ, {key: value for key, value in os.environ.items()
                                          if key not in names}, clear=True)
    patcher.start()
    test.addCleanup(patcher.stop)


def launcher_directories(path, mode=0o755):
    """Make `path` and its missing parents exactly `mode`, whatever this runner's umask.

    These stand in for a namespace an older launcher made: 0755 under umask 022
    (its admission directory 0700). The launcher refuses a namespace writable by
    its group or others, so a fixture must not inherit a runner's umask 002.
    """
    path = Path(path)
    missing = []
    while not path.exists():
        missing.append(path)
        path = path.parent
    for directory in reversed(missing):
        directory.mkdir()
        directory.chmod(mode)


def made_mode(path):
    """The mode bits of a directory the launcher made, less what mkdir(2) itself added.

    On Linux a directory made under a set-group-ID parent gets S_ISGID; macOS
    never sets it. The launcher neither asks for nor judges it, so a runner whose
    temporary directory is set-group-ID must not fail an exact-mode assertion.
    """
    path = Path(path)
    inherited = path.parent.lstat().st_mode & stat.S_ISGID
    return stat.S_IMODE(path.lstat().st_mode) & ~inherited


def write_python_program(path, source, interpreter=None):
    """Run selected fixture Python without shebang whitespace interpretation."""
    body = path.with_name(path.name + ".py")
    body.write_text(source)
    selected = sys.executable if interpreter is None else os.fspath(interpreter)
    path.write_text("#!/bin/sh\nexec " + shlex.quote(selected) + " -I -B "
                    + shlex.quote(str(body)) + ' "$@"\n')
    path.chmod(0o700)


WRAPPER = r"""
import importlib.machinery
import importlib.util
import os
import pwd
import sys
from types import SimpleNamespace

# Substitute only the account-home provider before loading production code.
# Its UID-based mapping must still ignore arbitrary ambient HOME values.
fixture_home = os.environ["FIXTURE_USER_HOME"]
missing_home = os.environ.get("FIXTURE_USER_HOME_MISSING") == "1"
def fixture_account(uid):
    assert uid == os.geteuid()
    if missing_home:
        raise KeyError(uid)
    return SimpleNamespace(pw_dir=fixture_home)
pwd.getpwuid = fixture_account

loader = importlib.machinery.SourceFileLoader("private_build_slot", sys.argv[1])
spec = importlib.util.spec_from_loader(loader.name, loader)
gate = importlib.util.module_from_spec(spec)
loader.exec_module(gate)
if os.environ.get("FIXTURE_IGNORE_SIGCHLD"):
    import signal
    signal.signal(signal.SIGCHLD, signal.SIG_IGN)
if "FIXTURE_GATE_REEXEC" in os.environ:
    gate._REEXEC = [sys.executable, "-I", "-B", "-c",
                    os.environ["FIXTURE_GATE_REEXEC"], sys.argv[1]]
if os.environ.get("FIXTURE_CANCEL_MEMORY_SPAWN"):
    real_popen = gate.subprocess.Popen
    def cancel_memory_spawn(command, *args, **kwargs):
        child = real_popen(command, *args, **kwargs)
        if os.path.basename(command[0]) == "heavy_gate.sh":
            os.kill(os.getpid(), signal.SIGTERM)
        return child
    import signal
    gate.subprocess.Popen = cancel_memory_spawn
if os.environ.get("FIXTURE_SIGNAL_AFTER_REAP"):
    # Schedule the handler after a real owning wait has reaped its child.
    # Record attempted dispatch instead of ever signaling a recycled identity.
    import signal
    real_popen = gate.subprocess.Popen
    def observe_reap(command, *args, **kwargs):
        child = real_popen(command, *args, **kwargs)
        original_wait = child.wait
        def interrupted_wait(*wait_args, **wait_kwargs):
            result = original_wait(*wait_args, **wait_kwargs)
            handler = signal.getsignal(signal.SIGTERM)
            if callable(handler):
                handler(signal.SIGTERM, None)
            return result
        child.wait = interrupted_wait
        return child
    def record_late_signal(pid, sig):
        with open(os.environ["FIXTURE_SIGNAL_AFTER_REAP"], "a") as output:
            output.write(str(pid) + ":" + str(sig) + "\n")
    gate.subprocess.Popen = observe_reap
    gate.os.killpg = record_late_signal
if os.environ.get("FIXTURE_FORWARD_CENSUS"):
    # A real child has exited but its original identity is still unreaped.
    # Inject only Darwin's killpg EPERM and the ps census, then deliver a
    # real signal to exercise each installed production forward handler.
    from unittest import mock
    import errno, signal
    actual_observer = gate.original_child_exit_observer
    def observer_with_forward():
        observe = actual_observer()
        if observe is None:
            return None
        def after_exit(pid):
            observe(pid)
            def eperm(target, sig):
                assert target == pid
                with open(os.environ["FIXTURE_FORWARD_RECORD"], "a") as output:
                    output.write(str(target) + ":" + str(sig) + "\n")
                raise PermissionError(errno.EPERM, "Darwin zombie fixture")
            def census(command, **kwargs):
                assert command == ["ps", "-axo", "pgid=,stat="]
                state = os.environ["FIXTURE_FORWARD_CENSUS"]
                return SimpleNamespace(returncode=0, stdout=str(pid)+" "+state+"\n", stderr="")
            with mock.patch.object(gate.os, "killpg", side_effect=eperm), \
                    mock.patch.object(gate.subprocess, "run", side_effect=census):
                os.kill(os.getpid(), signal.SIGTERM)
        return after_exit
    gate.original_child_exit_observer = observer_with_forward
expected_registry = None if missing_home else os.path.join(
    os.path.realpath(fixture_home), ".cache", "build-slot", "adopted")
assert gate.ADOPTION_DIR == expected_registry, "registry did not use the canonical UID home"
# Discovery is deterministic; locking, subprocess execution, nesting and the
# production main/CPU-share calculation remain real. All state is private.
gate.MEASURED_NCPU = int(os.environ.get("FIXTURE_CPU_COUNT", "28"))
gate.NCPU = gate.MEASURED_NCPU
gate.load1 = lambda: 0.0
gate.build_processes = lambda: []
gate.QUIET_SECONDS = 0.0
gate.available_gib = lambda: float(os.environ.get("FIXTURE_AVAILABLE_GIB", "128"))
if os.environ.get("FIXTURE_AVAILABLE_GIB_FILE"):
    def available_from_file():
        with open(os.environ["FIXTURE_AVAILABLE_GIB_FILE"]) as stream:
            return float(stream.read())
    gate.available_gib = available_from_file
gate.worktree_lock_path = lambda: os.environ.get("FIXTURE_WORKTREE_LOCK")
parked = os.environ.get("FIXTURE_PARKED")
release = os.environ.get("FIXTURE_RELEASE")
if parked:
    from pathlib import Path
    real_sleep = gate.time.sleep
    def controlled_sleep(seconds):
        if seconds in (2, 10) and not Path(release).exists():
            Path(parked).touch()
            while not Path(release).exists():
                real_sleep(0.005)
        else:
            real_sleep(seconds)
    gate.time.sleep = controlled_sleep
identity_mode = os.environ.get("FIXTURE_IDENTITY_MODE")
if identity_mode:
    real_identity = gate.process_identity
    def fixture_identity(pid):
        if identity_mode == "uncertain":
            raise gate.IdentityError("fixture identity query unavailable")
        identity = real_identity(pid)
        if identity is not None and identity_mode == "foreign":
            identity["uid"] += 1
        return identity
    gate.process_identity = fixture_identity
publication_fault = os.environ.get("FIXTURE_PUBLICATION_FAULT")
if publication_fault:
    real_write = gate.write_adoption
    def fixture_write(path, info):
        if publication_fault == "before":
            def fail_replace(*_):
                raise OSError("fixture atomic publication failure")
            gate.os.replace = fail_replace
        real_write(path, info)
        if publication_fault == "after":
            os._exit(91)
    gate.write_adoption = fixture_write
try:
    raise SystemExit(gate.main(sys.argv[2:]))
except gate.AdmissionUnavailable:
    raise SystemExit(75)
except gate.AdmissionTimeout:
    print("admission wait timed out; no command was started", file=sys.stderr)
    raise SystemExit(2)
"""
CHILD = r"""
import json
import os
from pathlib import Path
import sys

marker = Path(sys.argv[1])
pending = Path(sys.argv[1] + ".pending")
pending.write_text(json.dumps({
    "pid": os.getpid(),
    "jobs": os.environ.get("CARGO_BUILD_JOBS"),
    "held": os.environ.get("BUILD_SLOT_HELD"),
    "exclusive": os.environ.get("BUILD_SLOT_EXCLUSIVE"),
}))
pending.replace(marker)
sys.stdin.buffer.read(1)
Path(sys.argv[1] + ".finished").write_text(str(os.getpid()))
raise SystemExit(int(sys.argv[2]))
"""

# Descriptor DATA only: these fixtures never grant native resource authority.
RESOURCE_PROBE = r"""
import json,os,sys
def identity(fd):
    try:
        info=os.fstat(fd)
        return [info.st_dev,info.st_ino,info.st_mode,info.st_rdev]
    except OSError:
        return None
expected=json.loads(os.environ['FIXTURE_RESOURCE_IDENTITIES'])
missing=[word for word,expected_identity in expected.items() if identity(int(word))!=expected_identity]
other=json.loads(os.environ['FIXTURE_UNDECLARED_IDENTITY'])
undeclared=identity(int(other[0]))==other[1]
row={'missing':missing,'undeclared':undeclared,'jobs':os.environ.get('CARGO_BUILD_JOBS'),
     'argv':sys.argv[1:],'cwd':os.getcwd()}
print(json.dumps(row),flush=True)
if os.environ.get('FIXTURE_CAPABILITY_RECORD'):
    from pathlib import Path
    Path(os.environ['FIXTURE_CAPABILITY_RECORD']).write_text(json.dumps(row))
    print('{"version":3,"cpu_workers":true,"supports_invocation":true}' if not missing else '{}')
raise SystemExit(97 if missing or undeclared else 0)
"""


class PythonProgramTests(unittest.TestCase):
    def test_private_admission_fixture_isolates_enclosing_resource_transport(self):
        environment={"CARGO_MAKEFLAGS":"--jobserver-auth=2147483646,2147483647",
                     "TRUST_CPU_IMPLICIT_FD":"2147483647"}
        with mock.patch.dict(os.environ,environment):
            fixture=PrivateAdmissionTests('test_caller_job_request_is_capped_to_the_admitted_share')
            try:
                fixture.setUp()
                result=fixture.invoke('--cpus','1','--',sys.executable,'-c','print("private only")')
                self.assertEqual(result.returncode,0,result.stderr)
                self.assertEqual(result.stdout,b'private only\n')
            finally:
                fixture.tearDown()
                fixture.doCleanups()
            # Isolation changes only the private fixture, not its caller.
            self.assertEqual(os.environ['CARGO_MAKEFLAGS'],environment['CARGO_MAKEFLAGS'])
            self.assertEqual(os.environ['TRUST_CPU_IMPLICIT_FD'],environment['TRUST_CPU_IMPLICIT_FD'])

    def test_selected_interpreter_and_arguments_survive_spaces_and_quotes(self):
        with tempfile.TemporaryDirectory(prefix="python fixture ") as temporary:
            root = Path(temporary)
            selected = root / "selected interpreter with spaces"
            selected.symlink_to(sys.executable)
            program = root / "program with spaces"
            write_python_program(program, "import json,sys\nprint(json.dumps([sys.executable,sys.argv[1:]]))\n", selected)
            arguments = ["", "two words", "quote'\"", "back\\slash", "line\nbreak", "--resource-capabilities"]
            result = subprocess.run([str(program), *arguments], capture_output=True,
                                    text=True, timeout=60, check=True)
            executable, observed = json.loads(result.stdout)
            self.assertEqual(Path(executable).resolve(), Path(sys.executable).resolve())
            self.assertEqual(observed, arguments)


class PrivateAdmissionTests(unittest.TestCase):
    def setUp(self):
        isolate_resource_environment(self)
        self.temporary = tempfile.TemporaryDirectory(prefix="build-slot-private-")
        self.root = Path(self.temporary.name)
        self.pool = self.root / "pool"
        self.processes = []
        self.serial = 0

    def tearDown(self):
        # Only our tiny children/wrappers exist here. Release via their private
        # stdin first, then terminate only a wrapper we created if still queued.
        for process, _ in reversed(self.processes):
            try:
                release = b"x" if process.stdin and not process.stdin.closed else None
                process.communicate(release, timeout=0.2)
            except subprocess.TimeoutExpired:
                if process.poll() is None:
                    process.terminate()
                process.communicate(timeout=5)
            for stream in (process.stdin, process.stdout, process.stderr):
                if stream:
                    stream.close()
        self.temporary.cleanup()

    def environment(self, overrides=None):
        environment = {
            key: value for key, value in os.environ.items()
            if not key.startswith(("GIT_", "BUILD_SLOT", "BUILD_SLOTS", "FIXTURE_", "ATERM_"))
            and key not in ("CARGO_BUILD_JOBS", "TARGO_PLANNED_JOBS", "TARGO_CALLER_JOBS")
        }
        environment["BUILD_SLOT_DIR"] = str(self.pool)
        # The loader supplies a private canonical account home to production's
        # UID lookup. Ambient HOME remains independent of that registry.
        environment["FIXTURE_USER_HOME"] = str(self.root / "home")
        environment["FIXTURE_GATE_REEXEC"] = WRAPPER
        environment.update(overrides or {})
        return environment

    def test_private_budget_inputs_ignore_parent_provenance_but_keep_explicit_caps(self):
        # Only private marker children run; no native tool or global pool is used.
        with mock.patch.dict(os.environ, {"CARGO_BUILD_JOBS": "1",
                                         "TARGO_PLANNED_JOBS": "1",
                                         "TARGO_CALLER_JOBS": "1"}):
            process, marker = self.spawn("--cpus", "14")
            self.assertEqual(self.started(process, marker)["jobs"], "14")
            self.finish(process)
            process, marker = self.spawn("--cpus", "14", env={"TARGO_CALLER_JOBS": "3"})
            self.assertEqual(self.started(process, marker)["jobs"], "3")
            self.finish(process)

    def invoke(self, *arguments, env=None, cwd=None, pass_fds=()):
        return subprocess.run(
            [sys.executable, "-I", "-B", "-c", WRAPPER, str(SCRIPT), *arguments],
            cwd=cwd or self.root, env=self.environment(env), capture_output=True, timeout=5,
            pass_fds=pass_fds,
        )

    def memory_gate(self):
        gate = self.root / "heavy_gate.sh"
        write_python_program(gate, r'''
import fcntl,os,signal,subprocess,sys,time
from pathlib import Path
_,weight,label,*command=sys.argv[1:]
if command[:1]==['--']:command=command[1:]
root=Path(os.environ['FIXTURE_MEMORY_ROOT'])
with (root/'attempts').open('a')as f:f.write('attempt\n')
if os.environ.get('FIXTURE_MEMORY_REFUSE'):raise SystemExit(75)
Path(os.environ['FIXTURE_MEMORY_WAITING']).touch()
before=os.environ.get('FIXTURE_MEMORY_BEFORE')
while before and not Path(before).exists():time.sleep(.005)
with (root/'memory').open('a+')as token:
 fcntl.flock(token,fcntl.LOCK_EX)
 (root/'held').touch()
 env=dict(os.environ,HEAVY_GATE_HELD=weight+':'+label)
 passed=[int(command[command.index('--_memory-attempt')+1])]if '--_memory-attempt'in command else[]
 if os.environ.get('FIXTURE_MEMORY_TRANSPORT_FDS'):
  passed.extend(map(int,os.environ['FIXTURE_MEMORY_TRANSPORT_FDS'].split(',')))
 try:rc=subprocess.call(command,env=env,pass_fds=passed)
 finally:
  (root/'held').unlink(missing_ok=True)
  with(root/'released').open('a')as f:f.write(str(locals().get('rc',-1))+'\n')
 raise SystemExit(rc)
''')
        return gate

    def spawn_memory(self, *, legacy=False, env=None, payload=None, slots=1, pass_fds=()):
        self.serial += 1
        marker = self.root / f"memory-child-{self.serial}.json"
        gate = self.memory_gate() if not (self.root / "heavy_gate.sh").exists() else self.root / "heavy_gate.sh"
        command = payload or [sys.executable, "-I", "-B", "-c", CHILD, str(marker), "0"]
        prefix = [str(gate)] if not legacy else [sys.executable, "-I", "-B", str(gate) + ".py"]
        values = {"FIXTURE_MEMORY_ROOT": str(self.root),
                  "FIXTURE_MEMORY_WAITING": str(marker) + ".waiting"}
        values.update(env or {})
        process = subprocess.Popen(
            [sys.executable, "-I", "-B", "-c", WRAPPER, str(SCRIPT),
             "--slots", str(slots), "--cpus", str(28 // slots), "--", *prefix,
             "run", "1", "fixture-memory", "--", *command],
            cwd=self.root, env=self.environment(values), stdin=subprocess.PIPE,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True,
            pass_fds=pass_fds)
        self.processes.append((process, marker))
        return process, marker

    def wait_file(self, path):
        deadline = time.monotonic() + 5
        while not path.exists() and time.monotonic() < deadline:
            time.sleep(.01)
        self.assertTrue(path.exists(), str(path))

    def resource_fixture(self):
        descriptors=[]
        for index in range(6):
            path=self.root/f'resource-{index}'
            path.write_text(str(index))
            descriptor=os.open(path,os.O_RDONLY)
            self.addCleanup(os.close,descriptor)
            descriptors.append(descriptor)
        read,write=os.pipe()
        self.addCleanup(os.close,read)
        self.addCleanup(os.close,write)
        def identity(fd):
            info=os.fstat(fd)
            return [info.st_dev,info.st_ino,info.st_mode,info.st_rdev]
        sdk,host,implicit,cpu_a,cpu_b,other=descriptors
        advertised=[sdk,host,implicit,cpu_a,cpu_b,read,write]
        environment={
            'ATERM_SDK_LEASE_V3':str(sdk),'ATERM_WORKLOAD_HOST_STORE_FD_V1':str(host),
            'TRUST_CPU_IMPLICIT_FD':str(implicit),'ATERM_WORKLOAD_CPU_FDS_V1':f'{cpu_a},{cpu_b}',
            'CARGO_MAKEFLAGS':f'--jobserver-auth={read},{write}',
            'FIXTURE_RESOURCE_IDENTITIES':json.dumps({str(fd):identity(fd)for fd in advertised}),
            'FIXTURE_UNDECLARED_IDENTITY':json.dumps([other,identity(other)]),
        }
        return environment,tuple([*advertised,other]),advertised

    def test_declared_resources_survive_fixed_child(self):
        environment,passed,_=self.resource_fixture()
        result=self.invoke('--cpus','3','--',sys.executable,'-I','-B','-c',RESOURCE_PROBE,
                           '', 'two words', 'line\nbreak',env=environment,pass_fds=passed)
        self.assertEqual(result.returncode,0,result.stderr)
        row=json.loads(result.stdout)
        self.assertEqual(row['missing'],[])
        self.assertFalse(row['undeclared'])
        self.assertEqual(row['jobs'],'3')
        self.assertEqual(row['argv'],['','two words','line\nbreak'])

    def test_declared_resources_survive_memory_coordinator(self):
        environment,passed,advertised=self.resource_fixture()
        environment['FIXTURE_MEMORY_TRANSPORT_FDS']=','.join(map(str,advertised))
        process,_=self.spawn_memory(env=environment,pass_fds=passed,
            payload=[sys.executable,'-I','-B','-c',RESOURCE_PROBE])
        stdout,stderr=process.communicate(timeout=5)
        self.assertEqual(process.returncode,0,stderr)
        self.assertEqual(json.loads(stdout)['missing'],[])
        self.assertFalse((self.root/'held').exists())
        self.assertEqual((self.root/'released').read_text(),'0\n')

    def test_declared_resources_reach_capability_probe(self):
        environment,_,_=self.resource_fixture()
        record=self.root/'capability.json'
        # Only the exact JSON line is stdout; retain the transport observation separately.
        source=RESOURCE_PROBE.replace('print(json.dumps(row),flush=True)','')
        tool=self.root/'targo'
        write_python_program(tool,source)
        loader=importlib.machinery.SourceFileLoader('resource_probe_gate',str(SCRIPT))
        spec=importlib.util.spec_from_loader(loader.name,loader)
        gate=importlib.util.module_from_spec(spec)
        loader.exec_module(gate)
        environment.update(PATH=os.defpath,FIXTURE_CAPABILITY_RECORD=str(record))
        with mock.patch.dict(os.environ,environment,clear=True):
            self.assertTrue(gate.worker_capability([str(tool),'--unverified','build']))
        self.assertEqual(json.loads(record.read_text())['missing'],[])

    def test_selected_native_runtime_refusal_cannot_downgrade_to_fixed(self):
        tool = self.root / 'targo'
        write_python_program(tool, '''
import json
print(json.dumps({"version":3,"cpu_workers":True,"supports_invocation":True,
                  "runtime_refusal":"selected SDK lacks its native debug helper"}))
''')
        loader = importlib.machinery.SourceFileLoader('runtime_refusal_gate', str(SCRIPT))
        spec = importlib.util.spec_from_loader(loader.name, loader)
        gate = importlib.util.module_from_spec(spec)
        loader.exec_module(gate)
        with mock.patch.dict(os.environ, {'PATH': os.defpath}, clear=True):
            with self.assertRaisesRegex(gate.CpuBridgeUnavailable, 'native debug helper'):
                gate.worker_capability([str(tool), '--unverified', 'build'])

    def test_unsupported_frontend_capability_remains_distinct_from_runtime_refusal(self):
        tool = self.root / 'targo'
        write_python_program(tool, '''
import json
print(json.dumps({"version":3,"cpu_workers":False,"supports_invocation":False}))
''')
        loader = importlib.machinery.SourceFileLoader('unsupported_native_gate', str(SCRIPT))
        spec = importlib.util.spec_from_loader(loader.name, loader)
        gate = importlib.util.module_from_spec(spec)
        loader.exec_module(gate)
        with mock.patch.dict(os.environ, {'PATH': os.defpath}, clear=True):
            self.assertFalse(gate.worker_capability([str(tool), '--unverified', 'build']))

    def test_resource_transport_preserves_binary_streams_and_payload_status(self):
        environment,passed,_=self.resource_fixture()
        prefix=RESOURCE_PROBE[:RESOURCE_PROBE.index('print(json.dumps(row),flush=True)')]
        source=prefix+"\nassert not missing and not undeclared\nos.write(1,b'raw\\x00\\xff\\n')\nos.write(2,b'error\\xfe\\n')\nsys.exit(75)\n"
        environment['FIXTURE_MEMORY_TRANSPORT_FDS']=','.join(map(str,passed[:-1]))
        process,_=self.spawn_memory(env=environment,pass_fds=passed,
            payload=[sys.executable,'-I','-B','-c',source])
        stdout,stderr=process.communicate(timeout=5)
        self.assertEqual((process.returncode,stdout,stderr),(75,b'raw\x00\xff\n',b'error\xfe\n'))
        self.assertEqual((self.root/'attempts').read_text(),'attempt\n')
        self.assertEqual((self.root/'released').read_text(),'75\n')

    def test_resource_transport_keeps_caller_cap_and_does_not_consume_gnu_tokens(self):
        environment,passed,advertised=self.resource_fixture()
        environment['CARGO_BUILD_JOBS']='1'
        os.write(advertised[-1],b'tokens')
        result=self.invoke('--cpus','3','--',sys.executable,'-I','-B','-c',RESOURCE_PROBE,
                           env=environment,pass_fds=passed)
        self.assertEqual(result.returncode,0,result.stderr)
        self.assertEqual(json.loads(result.stdout)['jobs'],'1')
        self.assertEqual(os.read(advertised[-2],6),b'tokens')

    def resource_lifetime(self, sig):
        path=self.root/'caller-resource.lock'
        descriptor=os.open(path,os.O_CREAT|os.O_RDWR,0o600)
        try:
            fcntl.flock(descriptor,fcntl.LOCK_EX|fcntl.LOCK_NB)
            process,marker=self.spawn('--slots','1',env={'ATERM_SDK_LEASE_V3':str(descriptor)},
                                      pass_fds=(descriptor,))
            self.started(process,marker)
            os.close(descriptor)
            descriptor=None
            self.assert_path_held(path)
            process.send_signal(sig)
            if sig==signal.SIGKILL:
                process.wait(timeout=5)
                self.assert_path_held(path)
                self.finish(process,-sig)
            else:
                process.communicate(timeout=5)
                self.assertEqual(process.returncode,128+sig)
            with path.open('r+')as probe:
                fcntl.flock(probe,fcntl.LOCK_EX|fcntl.LOCK_NB)
            self.assert_free(0)
        finally:
            if descriptor is not None:
                os.close(descriptor)

    def test_declared_resource_survives_supervisor_death_until_child_exit(self):
        self.resource_lifetime(signal.SIGKILL)

    def test_cancellation_releases_declared_resource_and_slot(self):
        self.resource_lifetime(signal.SIGTERM)

    def test_memory_waiter_does_not_reserve_cpu(self):
        with (self.root / "memory").open('a+') as token:
            fcntl.flock(token, fcntl.LOCK_EX)
            waiter, marker = self.spawn_memory()
            self.wait_file(Path(str(marker) + ".waiting"))
            small, small_marker = self.spawn("--slots", "1", "--cpus", "28")
            self.started(small, small_marker)
            self.finish(small)
            self.assertFalse(marker.exists())
        self.started(waiter, marker)
        self.finish(waiter)

    def test_two_memory_waiters_leave_cpu_for_small_job(self):
        with (self.root / "memory").open('a+') as token:
            fcntl.flock(token, fcntl.LOCK_EX)
            waiters = [self.spawn_memory(slots=2) for _ in range(2)]
            for _, marker in waiters:
                self.wait_file(Path(str(marker) + ".waiting"))
            small, marker = self.spawn("--slots", "2", "--cpus", "14")
            self.started(small, marker)
            self.finish(small)
            self.assertTrue(all(not marker.exists() for _, marker in waiters))
        for process, _ in waiters:
            process.stdin.write(b"x")
            process.stdin.flush()
        for process, marker in waiters:
            stdout, stderr = process.communicate(timeout=5)
            self.assertEqual(process.returncode, 0, (stdout, stderr))
            self.assertTrue(marker.exists())

    def test_old_cpu_first_claimant_cannot_deadlock_new_memory_holder(self):
        # Force the valid migration interleaving: old caller has CPU but has
        # not yet entered memory admission when the new caller obtains memory.
        release_old = self.root / "old-enters-memory"
        old, old_marker = self.spawn_memory(legacy=True,
            env={"FIXTURE_MEMORY_BEFORE": str(release_old)})
        self.wait_file(Path(str(old_marker) + ".waiting"))
        new, new_marker = self.spawn_memory()
        self.wait_file(self.root / "released")
        self.assertIn("75", (self.root / "released").read_text())
        self.assertFalse(new_marker.exists())
        release_old.touch()
        self.started(old, old_marker)
        self.finish(old)
        self.started(new, new_marker)
        self.finish(new)

    def test_coordinated_payload_exit_75_is_not_retried(self):
        count = self.root / "payload-count"
        payload = [sys.executable, "-I", "-B", "-c",
                   "from pathlib import Path;import sys;"
                   f"p=Path({str(count)!r});p.open('a').write('x');sys.exit(75)"]
        process, _ = self.spawn_memory(payload=payload)
        stdout, stderr = process.communicate(timeout=5)
        self.assertEqual(process.returncode, 75, (stdout, stderr))
        self.assertEqual(count.read_text(), "x")
        self.assertEqual((self.root / "attempts").read_text().count("attempt"), 1)

    def test_memory_refusal_75_is_not_retried(self):
        process, marker = self.spawn_memory(env={"FIXTURE_MEMORY_REFUSE": "1"})
        stdout, stderr = process.communicate(timeout=5)
        self.assertEqual(process.returncode, 75, (stdout, stderr))
        self.assertFalse(marker.exists())
        self.assertEqual((self.root / "attempts").read_text().count("attempt"), 1)

    def test_cancel_memory_waiter_releases_resources(self):
        with (self.root / "memory").open('a+') as token:
            fcntl.flock(token, fcntl.LOCK_EX)
            process, marker = self.spawn_memory()
            self.wait_file(Path(str(marker) + ".waiting"))
            process.terminate()
            stdout, stderr = process.communicate(timeout=5)
            self.assertEqual(process.returncode, 143, (stdout, stderr))
            self.assertFalse(marker.exists())
        small, marker = self.spawn("--slots", "1", "--cpus", "28")
        self.started(small, marker)
        self.finish(small)
        with (self.root / "memory").open('a+') as token:
            fcntl.flock(token, fcntl.LOCK_EX | fcntl.LOCK_NB)

    def test_cancel_cpu_retry_releases_memory_without_releasing_other_cpu_job(self):
        holder, holder_marker = self.spawn("--slots", "1", "--cpus", "28")
        self.started(holder, holder_marker)
        process, marker = self.spawn_memory()
        self.wait_file(self.root / "released")
        process.terminate()
        stdout, stderr = process.communicate(timeout=5)
        self.assertEqual(process.returncode, 143, (stdout, stderr))
        self.assertFalse(marker.exists())
        self.assertIsNone(holder.poll())
        with (self.root / "memory").open('a+') as token:
            fcntl.flock(token, fcntl.LOCK_EX | fcntl.LOCK_NB)
        self.finish(holder)
        small, marker = self.spawn("--slots", "1", "--cpus", "28")
        self.started(small, marker)
        self.finish(small)

    def test_cancel_during_memory_spawn_does_not_lose_the_signal(self):
        with (self.root / "memory").open('a+') as token:
            fcntl.flock(token, fcntl.LOCK_EX)
            process, marker = self.spawn_memory(env={"FIXTURE_CANCEL_MEMORY_SPAWN": "1"})
            stdout, stderr = process.communicate(timeout=5)
            self.assertEqual(process.returncode, 143, (stdout, stderr))
            self.assertFalse(marker.exists())
        small, marker = self.spawn("--slots", "1", "--cpus", "28")
        self.started(small, marker)
        self.finish(small)

    def test_coordinated_arrival_survives_retries_and_small_job_stream(self):
        holder, marker = self.spawn("--slots", "1", "--cpus", "28")
        self.started(holder, marker)
        older, older_marker = self.spawn_memory()
        self.wait_file(self.root / "released")
        stream = [self.spawn("--slots", "1", "--cpus", "28") for _ in range(8)]
        for process, marker in stream:
            self.waiting(process, marker, "waiting")
        # Several rollbacks must retain the original arrival, rather than
        # moving this command behind the continuing small-job backlog.
        deadline = time.monotonic() + 5
        while (self.root / "released").read_text().count("75") < 3 and time.monotonic() < deadline:
            time.sleep(.01)
        self.assertGreaterEqual((self.root / "released").read_text().count("75"), 3)
        self.finish(holder)
        self.started(older, older_marker)
        self.assertTrue(all(not marker.exists() for _, marker in stream),
                        "later CPU-only arrivals overtook the older eligible command")
        self.finish(older)
        deadline = time.monotonic() + 5
        while not any(marker.exists() for _, marker in stream) and time.monotonic() < deadline:
            time.sleep(.01)
        first, first_marker = next((process, marker) for process, marker in stream if marker.exists())
        self.started(first, first_marker)
        self.finish(first)
        for process, marker in stream:
            if process is first:
                continue
            process.terminate()
            process.communicate(timeout=5)

    def test_shared_memory_wrapper_retains_wait_timeout_refusal(self):
        gate = self.memory_gate()
        result = self.invoke("--wait-timeout", ".1", "--", str(gate),
                             "run", "1", "bounded", "--", sys.executable, "-c", "pass")
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertIn(b"--wait-timeout requires a new --exclusive command", result.stderr)
        self.assertFalse((self.root / "attempts").exists())
        self.assertFalse(self.pool.exists())

    def test_exclusive_memory_wrapper_retains_bounded_admission(self):
        gate = self.memory_gate()
        result = self.invoke("--exclusive", "--wait-timeout", ".1", "--", str(gate),
                             "run", "1", "bounded", "--", sys.executable, "-c", "pass",
                             env={"FIXTURE_AVAILABLE_GIB": "0"})
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertIn(b"admission wait timed out", result.stderr)
        self.assertFalse((self.root / "attempts").exists())

    def test_unknown_option_refuses_before_admission_or_command(self):
        marker = self.root / "must-not-run"
        command = [sys.executable, "-c", "from pathlib import Path; "
                   f"Path({str(marker)!r}).touch()"]
        for option in ("--mem-gb24", "--mem-gb1", "--cpus=2", "--unknown", "-x", "-"):
            for held in (None, "1"):
                with self.subTest(option=option, held=held):
                    result = self.invoke("--mem-gb", "1", option, *command,
                                         env={"BUILD_SLOT_HELD": held} if held else None)
                    self.assertEqual(result.returncode, 2, result.stderr)
                    self.assertIn(f"unknown option {option!r}".encode(), result.stderr)
                    self.assertIn(b"no command was started", result.stderr)
                    self.assertIn(b"usage: build-slot", result.stderr)
                    self.assertNotIn(b"Traceback", result.stderr)
                    self.assertFalse(marker.exists())
                    self.assertFalse(self.pool.exists(), "refuse before slot/ticket creation")

    def test_known_option_value_errors_keep_their_diagnostics(self):
        for arguments, diagnostic in (
            (("--cpus",), b"--cpus requires an integer"),
            (("--cpus", "bad"), b"--cpus requires an integer"),
            (("--wait-timeout",), b"--wait-timeout needs positive finite seconds"),
            (("--wait-timeout", "nan"), b"--wait-timeout needs positive finite seconds"),
        ):
            with self.subTest(arguments=arguments):
                result = self.invoke(*arguments)
                self.assertEqual(result.returncode, 2, result.stderr)
                self.assertIn(diagnostic, result.stderr)
                self.assertNotIn(b"unknown option", result.stderr)
                self.assertFalse(self.pool.exists())

    def test_command_options_pass_through_after_bare_program_or_separator(self):
        # Execute a real native printf through the real private admission. A
        # dash-leading invocation name requires --, but its argv stays intact.
        native_printf = shutil.which("printf", path=os.defpath)
        self.assertIsNotNone(native_printf)
        dash_command = self.root / "--mem-gb24"
        dash_command.symlink_to(native_printf)
        values = ["--mem-gb24", "--cpus", "-h", "--", "space value", "line\nbreak", "λ"]
        expected = b"\0".join(os.fsencode(value) for value in values) + b"\0"
        for command in ([native_printf], ["printf"], ["--", dash_command.name]):
            with self.subTest(command=command):
                result = self.invoke("--slots", "1", "--mem-gb", "24", "--no-worktree-lock", *command,
                                     "%s\\000", *values,
                                     env={"PATH": os.pathsep.join((str(self.root), str(Path(native_printf).parent), os.defpath))})
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stdout, expected)

    def legacy(self):
        self.serial += 1
        marker = self.root / f"child-{self.serial}.json"
        process = subprocess.Popen(
            [sys.executable, "-I", "-B", "-c", CHILD, str(marker), "0"],
            cwd=self.root, env=self.environment(), stdin=subprocess.PIPE,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True,
        )
        self.processes.append((process, marker))
        self.started(process, marker)
        return process

    def adoption_records(self):
        return sorted((self.root / "home/.cache/build-slot/adopted").glob("*.json"))

    def adopt(self, process, *options, env=None, expected=0, cwd=None):
        result = self.invoke(*options, "adopt", str(process.pid), env=env, cwd=cwd)
        self.assertEqual(result.returncode, expected, (result.stdout, result.stderr))
        return result

    def spawn(self, *options, env=None, code=0, nested=None, pass_fds=()):
        self.serial += 1
        marker = self.root / f"child-{self.serial}.json"
        command = [sys.executable, "-I", "-B", "-c", CHILD, str(marker), str(code)]
        if nested is not None:
            command = [sys.executable, "-I", "-B", "-c", WRAPPER, str(SCRIPT),
                       *nested, "--", *command]
        process = subprocess.Popen(
            [sys.executable, "-I", "-B", "-c", WRAPPER, str(SCRIPT), *options,
             "--", *command],
            cwd=self.root, env=self.environment(env), stdin=subprocess.PIPE,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True,
            pass_fds=pass_fds,
        )
        self.processes.append((process, marker))
        return process, marker

    def started(self, process, marker):
        deadline = time.monotonic() + 5
        while time.monotonic() < deadline:
            if marker.exists():
                return json.loads(marker.read_text())
            if process.poll() is not None:
                self.fail(f"gate exited before child start: {process.communicate()}")
            time.sleep(0.01)
        self.fail("tiny child did not start within its private-control deadline")

    def waiting(self, process, marker, fragment):
        ready, _, _ = select.select([process.stderr], [], [], 5)
        self.assertTrue(ready, "gate did not announce its actual wait")
        line = process.stderr.readline().decode()
        self.assertIn(fragment, line)
        self.assertIsNone(process.poll())
        self.assertFalse(marker.exists(), "waiting gate must not execute child")

    def finish(self, process, expected=0):
        stdout, stderr = process.communicate(b"x", timeout=5)
        self.assertEqual(process.returncode, expected, (stdout, stderr))

    def hold(self, index):
        launcher_directories(self.pool)
        descriptor = os.open(self.pool / f"slot-{index}", os.O_CREAT | os.O_RDWR, 0o600)
        fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
        self.addCleanup(os.close, descriptor)
        return descriptor

    def hold_worktree(self):
        path = self.root / "held-worktree.lock"
        descriptor = os.open(path, os.O_CREAT | os.O_RDWR, 0o600)
        fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
        self.addCleanup(os.close, descriptor)
        return descriptor, path

    def assert_free(self, index):
        descriptor = os.open(self.pool / f"slot-{index}", os.O_CREAT | os.O_RDWR, 0o600)
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
            fcntl.flock(descriptor, fcntl.LOCK_UN)
        finally:
            os.close(descriptor)

    def assert_held(self, index):
        self.assert_path_held(self.pool / f"slot-{index}")

    def assert_path_held(self, path):
        descriptor = os.open(path, os.O_RDWR)
        try:
            with self.assertRaises(BlockingIOError):
                fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
        finally:
            os.close(descriptor)

    def supervisor_death_retains_leases(self, *options, env=None, slots=1, wait_fragment=None):
        first, marker = self.spawn(*options, env=env)
        child = self.started(first, marker)
        # Child execution and the supervisor's post-spawn metadata write can
        # run in either order. Kill after that write, without a timing sleep.
        deadline = time.monotonic() + 5
        while time.monotonic() < deadline:
            try:
                published = json.loads((self.pool / f"slot-{slots - 1}").read_text())
            except json.JSONDecodeError:
                published = {}
            if published.get("pid") == child["pid"]:
                break
            self.assertIsNone(first.poll(), "supervisor exited before publishing its child")
            time.sleep(0.01)
        else:
            self.fail("supervisor did not publish its actual child within the control deadline")
        first.kill()  # Kill only this test's supervisor; its real child stays alive.
        self.assertEqual(first.wait(timeout=5), -signal.SIGKILL)
        for index in range(slots):
            self.assert_held(index)
            holder = json.loads((self.pool / f"slot-{index}").read_text())
            self.assertEqual(holder["pid"], child["pid"])
            self.assertEqual(holder["supervisor_pid"], first.pid)
        if env and "FIXTURE_WORKTREE_LOCK" in env:
            self.assert_path_held(env["FIXTURE_WORKTREE_LOCK"])
        status = subprocess.run(
            [sys.executable, "-I", "-B", "-c", WRAPPER, str(SCRIPT), "status"],
            cwd=self.root, env=self.environment(), capture_output=True, timeout=5,
        )
        self.assertEqual(status.returncode, 0, status.stderr)
        self.assertIn(f"slot 0: HELD pid={child['pid']} ".encode(), status.stdout)
        second, next_marker = self.spawn("--slots", "1", env=env)
        fragment = wait_fragment or (
            "exclusive reservation owns admission" if "--exclusive" in options
            else "waiting for one of 1 slots"
        )
        self.waiting(second, next_marker, fragment)
        # communicate releases and observes EOF from the surviving direct child,
        # even though its supervisor has already been killed and reaped.
        self.finish(first, -signal.SIGKILL)
        self.assertEqual(Path(str(marker) + ".finished").read_text(), str(child["pid"]))
        self.started(second, next_marker)
        self.finish(second)
        for index in range(slots):
            self.assert_free(index)

    def test_shared_job_keeps_its_slot_after_supervisor_death(self):
        self.supervisor_death_retains_leases("--slots", "1")

    def parked_waiter(self, *options, env=None):
        parked = self.root / f"parked-{self.serial}"
        release = self.root / f"release-{self.serial}"
        process, marker = self.spawn(*options, env={
            **(env or {}),
            "FIXTURE_PARKED": str(parked), "FIXTURE_RELEASE": str(release),
        })
        deadline = time.monotonic() + 5
        while not parked.exists() and time.monotonic() < deadline:
            self.assertIsNone(process.poll(), "waiter exited before its controlled wait")
            time.sleep(0.005)
        self.assertTrue(parked.exists(), "waiter must reach the real admission wait")
        return process, marker, release

    def test_older_waiter_precedes_new_arrival_after_a_slot_opens(self):
        holder = self.hold(0)
        first, first_marker, release = self.parked_waiter("--slots", "1")
        fcntl.flock(holder, fcntl.LOCK_UN)
        second, second_marker = self.spawn("--slots", "1")
        self.waiting(second, second_marker, "older eligible admission waiter first")
        release.touch()
        self.started(first, first_marker)
        self.assertFalse(second_marker.exists())
        self.finish(first)
        self.started(second, second_marker)
        self.finish(second)

    def test_weighted_waiter_reserves_cpu_drain_without_quiet_exclusivity(self):
        holders = [self.hold(index) for index in (0, 1)]
        weighted, weighted_marker, release = self.parked_waiter("--cpus", "21")
        # Later small arrivals must not continually refill the two free slots
        # and starve this older wide claim. Reservation creates no slot grant.
        small, small_marker = self.spawn()
        self.waiting(small, small_marker, "older eligible admission waiter first")
        self.assertFalse(weighted_marker.exists())
        self.assert_free(2)
        self.assert_free(3)
        fcntl.flock(holders[1], fcntl.LOCK_UN)
        # Three slots now fit: a later one-slot peer must not overtake it.
        later, later_marker = self.spawn()
        self.waiting(later, later_marker, "older eligible admission waiter first")
        release.touch()
        self.assertEqual(self.started(weighted, weighted_marker)["jobs"], "21")
        self.assertFalse(later_marker.exists())
        for index in (1, 2, 3):
            self.assert_held(index)
        self.finish(weighted)
        self.started(small, small_marker)
        self.finish(small)
        self.started(later, later_marker)
        self.finish(later)

    def test_exclusive_waiter_precedes_new_shared_arrival(self):
        holder = self.hold(3)
        first, first_marker, release = self.parked_waiter("--exclusive")
        second, second_marker = self.spawn()
        self.waiting(second, second_marker, "exclusive reservation owns admission")
        fcntl.flock(holder, fcntl.LOCK_UN)
        release.touch()
        self.started(first, first_marker)
        for index in range(4):
            self.assert_held(index)
        self.assertFalse(second_marker.exists())
        self.finish(first)
        self.started(second, second_marker)
        self.finish(second)

    def test_crashed_oldest_waiter_does_not_block_its_successor(self):
        holder = self.hold(0)
        first, _, _ = self.parked_waiter("--slots", "1")
        second, second_marker = self.spawn("--slots", "1")
        self.waiting(second, second_marker, "waiting for one of 1 slots")
        first.kill()
        self.assertEqual(first.wait(timeout=5), -signal.SIGKILL)
        fcntl.flock(holder, fcntl.LOCK_UN)
        self.started(second, second_marker)
        self.finish(second)
        self.assertEqual(list((self.pool / "admission").glob("wait-*")), [])

    def test_status_explains_exclusive_reservation_with_free_slots(self):
        holder = self.hold(3)
        first, first_marker, first_release = self.parked_waiter("--exclusive")
        second, second_marker, second_release = self.parked_waiter()
        tickets = sorted((self.pool / "admission").glob("wait-*"))
        before = {path: (path.stat().st_ino, path.read_bytes()) for path in tickets}
        result = self.invoke("status")
        self.assertEqual(result.returncode, 0, result.stderr)
        output = result.stdout.decode()
        self.assertIn("slot 0: free", output)
        self.assertIn("queue: 1 pending request(s)", output)
        self.assertIn("eligible exclusive requests reserve the whole pool", output)
        self.assertIn(f"reservation: exclusive=1 claim=all pid={first.pid}", output)
        self.assertIn(f"wait 0: pid={second.pid} exclusive=0 claim=one pool_slots=4", output)
        self.assertIn(f"cwd={json.dumps(str(self.root.resolve()))}", output)
        self.assertEqual(before, {path: (path.stat().st_ino, path.read_bytes()) for path in tickets})
        self.assertFalse(first_marker.exists())
        self.assertFalse(second_marker.exists())
        self.assert_path_held(self.pool / "admission.lock")
        self.assert_path_held(tickets[0])
        fcntl.flock(holder, fcntl.LOCK_UN)
        first_release.touch()
        self.started(first, first_marker)
        self.finish(first)
        second_release.touch()
        self.started(second, second_marker)
        self.finish(second)

    def test_status_does_not_guess_legacy_cpu_budget(self):
        self.hold(0)
        result = self.invoke("status")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn(b"cpu_budget=unknown", result.stdout)
        self.assertIn(b"free_slots=3 pool_slots=4", result.stdout)

    def test_shared_epoch_fence_never_reattributes_the_previous_legacy_record(self):
        held = self.hold(0)
        previous = {"pid": 999999991, "cmd": "finished-legacy-command",
                    "cwd": "finished-worktree", "started": 1, "cpu_budget": 28}
        data = json.dumps(previous).encode()
        os.write(held, data)
        fcntl.flock(held, fcntl.LOCK_SH)
        result = self.invoke("status")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn(b"slot 0: HELD mode=shared-exclusion pid=None", result.stdout)
        self.assertIn(b"cpu_budget=unknown", result.stdout)
        self.assertIn(b"free_slots=3 pool_slots=4", result.stdout)
        self.assertNotIn(b"999999991", result.stdout)
        self.assertNotIn(b"finished-legacy-command", result.stdout)
        self.assertEqual(os.pread(held, len(data), 0), data)
        # The status probe cannot release somebody else's actual SH fence.
        contender = os.open(self.pool / "slot-0", os.O_RDWR)
        try:
            with self.assertRaises(BlockingIOError):
                fcntl.flock(contender, fcntl.LOCK_EX | fcntl.LOCK_NB)
        finally:
            os.close(contender)

    def test_status_does_not_invent_a_fence_when_holder_retires_between_probes(self):
        import io
        held = self.hold(0)
        loader = importlib.machinery.SourceFileLoader("retiring_status_gate", str(SCRIPT))
        spec = importlib.util.spec_from_loader(loader.name, loader)
        gate = importlib.util.module_from_spec(spec)
        loader.exec_module(gate)
        gate.ADOPTION_DIR = str(self.root / "adopted")
        real_flock = fcntl.flock
        retired = False
        def retiring_flock(descriptor, operation):
            nonlocal retired
            try:
                return real_flock(descriptor, operation)
            except BlockingIOError:
                if not retired and operation == fcntl.LOCK_EX | fcntl.LOCK_NB:
                    real_flock(held, fcntl.LOCK_UN)
                    retired = True
                raise
        with mock.patch.object(gate.fcntl, "flock", side_effect=retiring_flock), \
             mock.patch.object(gate, "available_gib", return_value=None), \
             mock.patch.object(gate, "load1", return_value=0), \
             mock.patch("sys.stdout", new_callable=io.StringIO) as output:
            self.assertEqual(gate.status(4, str(self.pool)), 0)
        self.assertTrue(retired)
        self.assertIn("free_slots=4 pool_slots=4", output.getvalue())
        self.assertNotIn("mode=shared-exclusion", output.getvalue())

    def test_status_distinguishes_cpu_budget_from_observed_use(self):
        process, marker = self.spawn(env={"CARGO_BUILD_JOBS": "2"})
        child = self.started(process, marker)
        deadline = time.monotonic() + 5
        while time.monotonic() < deadline:
            result = self.invoke("status")
            if b"cpu_budget=2" in result.stdout:
                break
            time.sleep(0.01)
        self.assertIn(f"slot 0: HELD pid={child['pid']} ".encode(), result.stdout)
        self.assertIn(b"cpu_budget=2", result.stdout)
        self.assertIn(b"capacity: free_slots=3 pool_slots=4 default_cpu_budget=7 observed_cpu_use=unknown", result.stdout)
        self.finish(process)

    def test_fixed_command_never_signals_its_group_after_owning_reap(self):
        attempts = self.root / "late-signals"
        result = self.invoke("--", sys.executable, "-I", "-B", "-c", "pass",
                             env={"FIXTURE_SIGNAL_AFTER_REAP": str(attempts)})
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertFalse(attempts.exists(), "reaped child cannot authorize a group signal")

    def test_memory_coordinator_never_signals_its_group_after_owning_reap(self):
        attempts = self.root / "late-signals"
        process, _ = self.spawn_memory(
            payload=[sys.executable, "-I", "-B", "-c", "pass"],
            env={"FIXTURE_SIGNAL_AFTER_REAP": str(attempts)})
        output, error = process.communicate(timeout=5)
        self.assertIn(process.returncode, (0, 128 + signal.SIGTERM), (output, error))
        self.assertFalse(attempts.exists(), "reaped memory wrapper cannot authorize a group signal")

    def test_fixed_and_memory_forwarding_share_zombie_only_eperm_policy(self):
        for memory in (False, True):
            for state in ('Zs+', 'S', '?', 'Z extra'):
                with self.subTest(memory=memory, state=state):
                    record = self.root / f'forward-{memory}-{state.replace(" ", "_")}'
                    env = dict(FIXTURE_FORWARD_CENSUS=state, FIXTURE_FORWARD_RECORD=str(record))
                    payload = [sys.executable, '-I', '-B', '-c', 'pass']
                    if memory:
                        process, _ = self.spawn_memory(payload=payload, env=env)
                        output, error = process.communicate(timeout=5)
                        status = process.returncode
                    else:
                        result = self.invoke('--', *payload, env=env)
                        status, output, error = result.returncode, result.stdout, result.stderr
                    self.assertTrue(record.exists(), 'the real signal must reach the original child group')
                    if state == 'Zs+':
                        self.assertEqual(status, 128 + signal.SIGTERM if memory else 0, (output, error))
                        self.assertNotIn(b'PermissionError', error)
                    else:
                        self.assertNotEqual(status, 0, (output, error))
                        self.assertIn(b'PermissionError', error)

    def test_automatic_reaping_refuses_before_a_command_or_memory_wrapper_starts(self):
        marker = self.root / "must-not-start"
        payload = [sys.executable, "-I", "-B", "-c",
                   "from pathlib import Path; " + f"Path({str(marker)!r}).touch()"]
        for memory in (False, True):
            with self.subTest(memory=memory):
                if memory:
                    process, _ = self.spawn_memory(payload=payload,
                        env={"FIXTURE_IGNORE_SIGCHLD": "1"})
                    _, error = process.communicate(timeout=5)
                    status = process.returncode
                    self.assertFalse((self.root / "attempts").exists())
                else:
                    result = self.invoke("--", *payload,
                        env={"FIXTURE_IGNORE_SIGCHLD": "1"})
                    status, error = result.returncode, result.stderr
                self.assertEqual(status, 2, error)
                self.assertIn(b"SIGCHLD must retain the original child", error)
                self.assertFalse(marker.exists())

    def test_status_reports_weighted_shared_slot_claim_without_admitting_it(self):
        holder = self.hold(2)
        self.hold(3)
        process, marker, release = self.parked_waiter("--cpus", "15")
        ticket, = (self.pool / "admission").glob("wait-*")
        before = (ticket.stat().st_ino, ticket.read_bytes())
        result = self.invoke("status")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn(
            f"wait 0: pid={process.pid} exclusive=0 claim=3 pool_slots=4".encode(),
            result.stdout,
        )
        self.assertEqual(before, (ticket.stat().st_ino, ticket.read_bytes()))
        self.assertFalse(marker.exists())
        self.assert_path_held(ticket)
        fcntl.flock(holder, fcntl.LOCK_UN)
        release.touch()
        self.assertEqual(self.started(process, marker)["jobs"], "15")
        self.assertNotIn(b"reservation: exclusive=1", self.invoke("status").stdout)
        self.finish(process)

    def test_status_preserves_malformed_exclusive_reservation(self):
        holder = self.hold(3)
        first, marker, release = self.parked_waiter("--exclusive")
        reservation = self.pool / "admission.lock"
        original = reservation.read_bytes()
        for payload in (b"{", b"x" * 65537, b"\xff"):
            with self.subTest(bytes=len(payload)):
                reservation.write_bytes(payload)
                before = (reservation.stat().st_ino, reservation.read_bytes())
                result = self.invoke("status")
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn(b"reservation: observation unavailable", result.stdout)
                self.assertEqual(before, (reservation.stat().st_ino, reservation.read_bytes()))
                self.assertFalse(marker.exists())
                self.assert_path_held(reservation)
        reservation.write_bytes(original)
        fcntl.flock(holder, fcntl.LOCK_UN)
        release.touch()
        self.started(first, marker)
        self.finish(first)

    def test_status_does_not_block_on_nonregular_reservation(self):
        launcher_directories(self.pool)
        reservation = self.pool / "admission.lock"
        os.mkfifo(reservation)
        result = self.invoke("status")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn(b"reservation: observation unavailable", result.stdout)
        self.assertTrue(reservation.exists())

    def test_status_ignores_but_does_not_retire_unleased_ticket(self):
        _, worktree = self.hold_worktree()
        first, _, _ = self.parked_waiter(
            "--exclusive", env={"FIXTURE_WORKTREE_LOCK": str(worktree)})
        ticket, = (self.pool / "admission").glob("wait-*")
        before = (ticket.stat().st_ino, ticket.read_bytes())
        first.kill()
        first.wait(timeout=5)
        result = self.invoke("status")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn(b"queue: 0 pending request(s), 1 stale ticket(s) ignored", result.stdout)
        self.assertEqual(before, (ticket.stat().st_ino, ticket.read_bytes()))

    def test_status_reports_unreadable_live_requirements_without_touching_them(self):
        holder, worktree = self.hold_worktree()
        first, marker, release = self.parked_waiter(
            "--exclusive", env={"FIXTURE_WORKTREE_LOCK": str(worktree)})
        ticket, = (self.pool / "admission").glob("wait-*")
        original = ticket.read_bytes()
        ticket.write_bytes(b"{")
        result = self.invoke("status")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn(b"wait 0: requirements unavailable", result.stdout)
        self.assertEqual(ticket.read_bytes(), b"{")
        self.assertFalse(marker.exists())
        self.assert_path_held(ticket)
        ticket.write_bytes(original)
        fcntl.flock(holder, fcntl.LOCK_UN)
        release.touch()
        self.started(first, marker)
        self.finish(first)

    def test_status_does_not_create_an_admission_registry(self):
        result = self.invoke("status")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn(b"queue: 0 pending request(s)", result.stdout)
        self.assertFalse((self.pool / "admission").exists())

    def test_status_does_not_block_on_a_nonregular_ticket(self):
        directory = self.pool / "admission"
        launcher_directories(directory)
        (directory / "registry.lock").touch()
        ticket = directory / "wait-1"
        os.mkfifo(ticket)
        result = self.invoke("status")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn(b"wait 0: requirements unavailable", result.stdout)
        self.assertTrue(ticket.exists())

    def test_status_returns_while_the_registry_is_busy(self):
        directory = self.pool / "admission"
        launcher_directories(directory)
        registry = directory / "registry.lock"
        fd = os.open(registry, os.O_CREAT | os.O_RDWR, 0o600)
        self.addCleanup(os.close, fd)
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        before = registry.stat().st_ino
        result = self.invoke("status")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn(b"admission registry is busy", result.stdout)
        self.assertEqual(registry.stat().st_ino, before)
        self.assert_path_held(registry)

    def test_status_bounds_and_preserves_unreadable_live_records(self):
        holder, worktree = self.hold_worktree()
        first, marker, release = self.parked_waiter(
            "--exclusive", env={"FIXTURE_WORKTREE_LOCK": str(worktree)})
        ticket, = (self.pool / "admission").glob("wait-*")
        original = ticket.read_bytes()
        for payload in (b"x" * 65537, b"\xff", b"[" * 32700 + b"0" + b"]" * 32700):
            with self.subTest(bytes=len(payload)):
                ticket.write_bytes(payload)
                result = self.invoke("status")
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn(b"requirements unavailable", result.stdout)
                self.assertEqual(ticket.read_bytes(), payload)
                self.assertFalse(marker.exists())
                self.assert_path_held(ticket)
        ticket.write_bytes(original)
        fcntl.flock(holder, fcntl.LOCK_UN)
        release.touch()
        self.started(first, marker)
        self.finish(first)

    def test_status_ignores_noncanonical_ticket_names(self):
        directory = self.pool / "admission"
        launcher_directories(directory)
        (directory / "registry.lock").touch()
        ticket = directory / "wait-\N{SUPERSCRIPT TWO}"
        ticket.write_text("{}")
        fd = os.open(ticket, os.O_RDWR)
        self.addCleanup(os.close, fd)
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        result = self.invoke("status")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn(b"queue: 0 pending request(s)", result.stdout)
        self.assertEqual(ticket.read_text(), "{}")
        self.assert_path_held(ticket)

    def test_adoption_cannot_overtake_an_older_normal_waiter(self):
        holder = self.hold(0)
        first, first_marker, release = self.parked_waiter("--slots", "1")
        legacy = self.legacy()
        fcntl.flock(holder, fcntl.LOCK_UN)
        adopter = subprocess.Popen(
            [sys.executable, "-I", "-B", "-c", WRAPPER, str(SCRIPT),
             "--slots", "1", "adopt", str(legacy.pid)],
            cwd=self.root, env=self.environment(), stdin=subprocess.PIPE,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True,
        )
        self.processes.append((adopter, None))
        self.waiting(adopter, self.root / "no-adoption-child", "normal adoption admission")
        release.touch()
        self.started(first, first_marker)
        self.assertIsNone(adopter.poll())
        self.finish(first)
        stdout, stderr = adopter.communicate(timeout=5)
        self.assertEqual(adopter.returncode, 0, (stdout, stderr))
        self.assertEqual(len(self.adoption_records()), 1)
        self.finish(legacy)

    def test_repeated_adoption_still_returns_while_a_waiter_is_queued(self):
        legacy = self.legacy()
        self.adopt(legacy, "--slots", "1")
        contender, marker, release = self.parked_waiter("--slots", "1")
        result = self.adopt(legacy, "--slots", "1")
        self.assertIn(b"already adopted", result.stdout)
        release.touch()
        self.finish(legacy)
        self.started(contender, marker)
        self.finish(contender)

    def test_older_adoption_and_newer_job_share_a_worktree_without_deadlock(self):
        holder = self.hold(0)
        legacy = self.legacy()
        parked = self.root / "adopter-parked"
        release = self.root / "adopter-release"
        worktree = {"FIXTURE_WORKTREE_LOCK": str(self.root / "worktree.lock")}
        adopter = subprocess.Popen(
            [sys.executable, "-I", "-B", "-c", WRAPPER, str(SCRIPT),
             "--slots", "1", "adopt", str(legacy.pid)],
            cwd=self.root, env=self.environment({**worktree,
                "FIXTURE_PARKED": str(parked), "FIXTURE_RELEASE": str(release),
            }), stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            start_new_session=True,
        )
        self.processes.append((adopter, None))
        self.waiting(adopter, self.root / "no-adoption-child", "normal adoption admission")
        deadline = time.monotonic() + 5
        while not parked.exists() and time.monotonic() < deadline:
            time.sleep(0.005)
        self.assertTrue(parked.exists(), "adopter reached its controlled wait")
        contender, marker = self.spawn("--slots", "1", env=worktree)
        self.waiting(contender, marker, "waiting for one of 1 slots")
        fcntl.flock(holder, fcntl.LOCK_UN)
        release.touch()
        stdout, stderr = adopter.communicate(timeout=5)
        self.assertEqual(adopter.returncode, 0, (stdout, stderr))
        self.assertFalse(marker.exists())
        self.finish(legacy)
        self.started(contender, marker)
        self.finish(contender)

    def test_busy_worktree_waiter_does_not_idle_another_free_slot(self):
        worktree = {"FIXTURE_WORKTREE_LOCK": str(self.root / "worktree-a.lock"),
                    "CARGO_BUILD_JOBS": "7"}
        active, active_marker = self.spawn(env=worktree)
        self.started(active, active_marker)
        queued, queued_marker = self.spawn("--cpus", "21", env={
            **worktree, "CARGO_BUILD_JOBS": "21",
        })
        self.waiting(queued, queued_marker, "another build-slot job runs in this worktree")
        unrelated, unrelated_marker = self.spawn(env={
            "FIXTURE_WORKTREE_LOCK": str(self.root / "worktree-b.lock"),
        })
        self.started(unrelated, unrelated_marker)
        self.assertFalse(queued_marker.exists())
        self.finish(unrelated)
        self.finish(active)
        self.started(queued, queued_marker)
        self.finish(queued)

    def test_initial_memory_wait_is_visible_resource_free_and_keeps_arrival(self):
        available = self.root / "available-gib"
        available.write_text("32")
        parked = self.root / "memory-parked"
        release = self.root / "memory-release"
        first, first_marker = self.spawn("--slots", "1", "--mem-gb", "64", env={
            "FIXTURE_AVAILABLE_GIB_FILE": str(available),
            "FIXTURE_PARKED": str(parked), "FIXTURE_RELEASE": str(release),
        })
        self.waiting(first, first_marker, "GiB available < 64 GiB needed")
        self.wait_file(parked)
        status = self.invoke("status")
        self.assertEqual(status.returncode, 0, status.stderr)
        self.assertIn(b"queue: 1 pending request(s)", status.stdout)
        self.assertIn(f"pid={first.pid} ".encode(), status.stdout)
        self.assertIn(b"mem_gib=64.0", status.stdout)
        self.assert_free(0)
        ticket, = (self.pool / "admission").glob("wait-*")
        before = (ticket.stat().st_ino, ticket.read_bytes())
        self.assert_path_held(ticket)
        self.assertEqual(self.invoke("status").returncode, 0)
        self.assertEqual(before, (ticket.stat().st_ino, ticket.read_bytes()))

        # A smaller eligible job can use the otherwise free machine.
        small, small_marker = self.spawn("--slots", "1", "--mem-gb", "8", env={
            "FIXTURE_AVAILABLE_GIB": "32",
        })
        self.started(small, small_marker)
        self.assertFalse(first_marker.exists())
        self.finish(small)

        # Once memory is available, a fresh arrival must not overtake the
        # original waiter. Both compete through actual production flock leases.
        held = self.hold(0)
        available.write_text("128")
        release.touch()
        newer, newer_marker = self.spawn("--slots", "1", "--mem-gb", "8")
        self.waiting(newer, newer_marker, "waiting")
        fcntl.flock(held, fcntl.LOCK_UN)
        self.started(first, first_marker)
        self.assertFalse(newer_marker.exists())
        self.finish(first)
        self.started(newer, newer_marker)
        self.finish(newer)

    def test_memory_ineligible_registered_waiter_does_not_idle_a_free_slot(self):
        holders = [self.hold(index) for index in (0, 1)]
        first, first_marker, release = self.parked_waiter("--cpus", "21", "--mem-gb", "64")
        for holder in holders:
            fcntl.flock(holder, fcntl.LOCK_UN)
        second, second_marker = self.spawn("--slots", "1", "--mem-gb", "8", env={
            "FIXTURE_AVAILABLE_GIB": "32",
        })
        self.started(second, second_marker)
        self.assertFalse(first_marker.exists())
        self.finish(second)
        release.touch()
        self.started(first, first_marker)
        self.finish(first)

    def test_exclusive_job_keeps_every_slot_after_supervisor_death(self):
        self.supervisor_death_retains_leases("--exclusive", slots=4)

    def test_job_keeps_worktree_lease_after_supervisor_death(self):
        self.supervisor_death_retains_leases(
            env={"FIXTURE_WORKTREE_LOCK": str(self.root / "worktree.lock")},
            wait_fragment="another build-slot job runs in this worktree",
        )

    def test_adopted_unleased_child_holds_slot_after_adopter_exits(self):
        legacy = self.legacy()
        self.adopt(legacy, "--slots", "1")
        self.assert_free(0)  # No watcher or adopter retains a kernel flock.
        status = self.invoke("status")
        self.assertEqual(status.returncode, 0, status.stderr)
        self.assertIn(f"slot 0: HELD pid={legacy.pid} ".encode(), status.stdout)
        self.assertIn(b"adopted=1", status.stdout)
        contender, marker = self.spawn("--slots", "1")
        self.waiting(contender, marker, "waiting for one of 1 slots")
        self.finish(legacy)
        self.started(contender, marker)
        self.finish(contender)
        self.assertEqual(self.adoption_records(), [])

    def test_repeated_adoption_does_not_take_another_slot(self):
        legacy = self.legacy()
        self.adopt(legacy)
        record = self.adoption_records()[0].read_bytes()
        result = self.adopt(legacy)
        self.assertIn(b"already adopted", result.stdout)
        self.assertEqual(len(self.adoption_records()), 1)
        self.assertEqual(self.adoption_records()[0].read_bytes(), record)
        self.assertIn(b"slot 1: free", self.invoke("status").stdout)
        self.finish(legacy)

    def test_changed_ambient_home_cannot_hide_an_adopted_job(self):
        legacy = self.legacy()
        self.adopt(legacy, "--slots", "1")
        changed_home = {"HOME": str(self.root / "different-ambient-home")}
        self.assertIn(b"slot 0: HELD", self.invoke("status", env=changed_home).stdout)
        job, marker = self.spawn("--slots", "1", env=changed_home)
        self.waiting(job, marker, "waiting for one of 1 slots")
        self.finish(legacy)
        self.started(job, marker)
        self.finish(job)

    def test_unknown_canonical_user_home_refuses_admission(self):
        missing_home = {"FIXTURE_USER_HOME_MISSING": "1"}
        self.assertEqual(self.invoke("status", env=missing_home).returncode, 2)
        legacy = self.legacy()
        self.adopt(legacy, env=missing_home, expected=2)
        self.finish(legacy)
        job, marker = self.spawn(env=missing_home)
        stdout, stderr = job.communicate(timeout=5)
        self.assertEqual(job.returncode, 2, (stdout, stderr))
        self.assertFalse(marker.exists())
        self.assertFalse(self.pool.exists())
        self.assertEqual(self.adoption_records(), [])

    def test_adopted_shared_job_blocks_exclusive_admission(self):
        legacy = self.legacy()
        self.adopt(legacy)
        contender, marker = self.spawn("--exclusive")
        self.waiting(contender, marker, "waiting for all 4 canonical slots")
        self.assert_free(1)
        self.finish(legacy)
        self.started(contender, marker)
        self.finish(contender)

    def test_adoption_worktree_lease_is_shared_across_different_pools(self):
        legacy = self.legacy()
        worktree = {"FIXTURE_WORKTREE_LOCK": str(self.root / "worktree.lock")}
        self.adopt(legacy, env=worktree)
        contender, marker = self.spawn(env={
            **worktree, "BUILD_SLOT_DIR": str(self.root / "another-pool"),
        })
        self.waiting(contender, marker, "another build-slot job runs in this worktree")
        self.finish(legacy)
        self.started(contender, marker)
        self.finish(contender)

    def test_crash_after_atomic_publication_preserves_all_claims(self):
        legacy = self.legacy()
        worktree = {"FIXTURE_WORKTREE_LOCK": str(self.root / "worktree.lock")}
        self.adopt(legacy, "--exclusive", env={
            **worktree, "FIXTURE_PUBLICATION_FAULT": "after",
        }, expected=91)
        for index in range(4):
            self.assert_free(index)
        self.assertEqual(self.invoke("status").stdout.count(b": HELD "), 4)
        self.assertEqual(len(json.loads(self.adoption_records()[0].read_text())["leases"]), 5)
        slot_job, slot_marker = self.spawn("--slots", "1")
        self.waiting(slot_job, slot_marker, "waiting for one of 1 slots")
        worktree_job, worktree_marker = self.spawn(env={
            **worktree, "BUILD_SLOT_DIR": str(self.root / "another-pool"),
        })
        self.waiting(worktree_job, worktree_marker, "another build-slot job runs in this worktree")
        self.adopt(legacy, "--exclusive", env=worktree)
        self.assertEqual(len(self.adoption_records()), 1)
        self.finish(legacy)
        self.started(slot_job, slot_marker)
        self.finish(slot_job)
        self.started(worktree_job, worktree_marker)
        self.finish(worktree_job)

    def test_failed_publication_leaves_no_partial_adoption(self):
        legacy = self.legacy()
        worktree = {"FIXTURE_WORKTREE_LOCK": str(self.root / "worktree.lock")}
        self.adopt(legacy, "--exclusive", env={
            **worktree, "FIXTURE_PUBLICATION_FAULT": "before",
        }, expected=2)
        self.assertEqual(self.adoption_records(), [])
        for index in range(4):
            self.assert_free(index)
        job, marker = self.spawn("--exclusive", env=worktree)
        self.started(job, marker)
        self.finish(job)
        self.adopt(legacy, "--exclusive", env=worktree)
        self.assertEqual(self.invoke("status").stdout.count(b": HELD "), 4)
        self.finish(legacy)

    def test_pid_birth_mismatch_reclaims_adoption(self):
        legacy = self.legacy()
        self.adopt(legacy, "--slots", "1")
        record = self.adoption_records()[0]
        info = json.loads(record.read_text())
        info["identity"]["birth"] = "a-different-native-process-birth"
        record.write_text(json.dumps(info))
        job, marker = self.spawn("--slots", "1")
        self.started(job, marker)
        self.finish(job)
        self.assertEqual(self.adoption_records(), [])
        self.finish(legacy)

    def test_same_birth_executable_change_keeps_adoption_held(self):
        legacy = self.legacy()
        self.adopt(legacy, "--slots", "1")
        record = self.adoption_records()[0]
        info = json.loads(record.read_text())
        info["identity"]["executable"] = "/previous-executable-before-exec"
        record.write_text(json.dumps(info))
        job, marker = self.spawn("--slots", "1")
        self.waiting(job, marker, "waiting for one of 1 slots")
        self.finish(legacy)
        self.started(job, marker)
        self.finish(job)

    def test_uncertain_existing_identity_is_held_even_after_exit(self):
        legacy = self.legacy()
        self.adopt(legacy, "--slots", "1")
        uncertain = {"FIXTURE_IDENTITY_MODE": "uncertain"}
        self.assertIn(b"slot 0: HELD", self.invoke("status", env=uncertain).stdout)
        job, marker = self.spawn("--slots", "1", env=uncertain)
        self.waiting(job, marker, "waiting for one of 1 slots")
        self.finish(legacy)
        self.assertIn(b"slot 0: HELD", self.invoke("status", env=uncertain).stdout)

    def test_adoption_refuses_invalid_foreign_gone_or_unqueryable_identity(self):
        for pid in ("0", "-1", "not-a-pid"):
            self.assertEqual(self.invoke("adopt", pid).returncode, 2)
        legacy = self.legacy()
        self.adopt(legacy, env={"FIXTURE_IDENTITY_MODE": "foreign"}, expected=2)
        self.adopt(legacy, env={"FIXTURE_IDENTITY_MODE": "uncertain"}, expected=2)
        self.adopt(legacy, env={"BUILD_SLOT_HELD": "1"}, expected=2)
        other_directory = self.root / "other-directory"
        other_directory.mkdir()
        self.adopt(legacy, cwd=other_directory, expected=2)
        self.finish(legacy)
        self.adopt(legacy, expected=2)
        self.assertEqual(self.adoption_records(), [])

    def test_slots_one_does_not_exclude_default_workers(self):
        first, one = self.spawn("--slots", "1")
        self.started(first, one)
        second, two = self.spawn()
        self.assertEqual(self.started(second, two)["jobs"], "21")
        self.assert_held(0)
        self.assert_held(1)
        self.finish(second)
        self.finish(first)

    def test_exclusive_covers_host_pool_even_with_smaller_configuration(self):
        blocker = self.hold(3)
        exclusive, marker = self.spawn(
            "--exclusive", "--slots", "1",
            env={"BUILD_SLOTS": "1", "CARGO_BUILD_JOBS": "2"},
        )
        self.waiting(exclusive, marker, "waiting for all 4 canonical slots")
        self.assert_free(0)  # failed acquisition must not retain partial locks
        fcntl.flock(blocker, fcntl.LOCK_UN)
        self.assertEqual(self.started(exclusive, marker)["jobs"], "2")
        for index in range(4):
            self.assert_held(index)
        default, neighbor = self.spawn()
        self.waiting(default, neighbor, "exclusive reservation owns admission")
        self.finish(exclusive)
        self.started(default, neighbor)
        self.finish(default)

    def test_exclusive_uses_reserved_host_cpus_and_marks_admission(self):
        process, marker = self.spawn("--exclusive")
        info = self.started(process, marker)
        self.assertEqual(info["jobs"], "28")
        self.assertEqual(info["held"], "1")
        self.assertEqual(info["exclusive"], "1")
        self.finish(process)
        for index in range(4):
            self.assert_free(index)

    def test_cpu_budget_reserves_matching_slots_and_leaves_room_for_a_peer(self):
        process, marker = self.spawn("--cpus", "14")
        self.assertEqual(self.started(process, marker)["jobs"], "14")
        self.assert_held(0)
        self.assert_held(1)
        self.assert_free(2)
        self.assert_free(3)
        peer, peer_marker = self.spawn()
        self.assertEqual(self.started(peer, peer_marker)["jobs"], "14")
        self.finish(peer)
        self.finish(process)

    def test_cpu_reservation_releases_partial_leases_while_waiting(self):
        blockers = [self.hold(i) for i in (0, 1, 2)]
        process, marker = self.spawn("--cpus", "14")
        self.waiting(process, marker, "waiting for 2 of 4 slots")
        self.assert_free(3)
        fcntl.flock(blockers[-1], fcntl.LOCK_UN)
        self.assertEqual(self.started(process, marker)["jobs"], "14")
        self.assert_held(2)
        self.assert_held(3)
        self.finish(process)

    def test_cpu_budget_uses_host_pool_even_with_a_small_slots_override(self):
        process, marker = self.spawn("--cpus", "28", "--slots", "1", env={"BUILD_SLOTS": "1"})
        self.assertEqual(self.started(process, marker)["jobs"], "28")
        for index in range(4):
            self.assert_held(index)
        self.finish(process)

    def test_cpu_budget_preserves_smaller_explicit_cap(self):
        process, marker = self.spawn("--cpus", "14", env={"CARGO_BUILD_JOBS": "3"})
        self.assertEqual(self.started(process, marker)["jobs"], "3")
        self.finish(process)

    def test_automatic_cpu_budget_borrows_free_slots_with_measured_memory(self):
        self.hold(0)
        process, marker = self.spawn()
        self.assertEqual(self.started(process, marker)["jobs"], "21")
        for index in range(4):
            self.assert_held(index)
        self.finish(process)

    def test_already_queued_automatic_children_share_real_free_slots(self):
        blockers = [self.hold(index) for index in range(4)]
        children = [self.spawn() for _ in range(4)]
        for process, marker in children:
            self.waiting(process, marker, "waiting")
        # Release all capacity under the actual registry lock. Every pending
        # ticket is already live before the first child can claim its shares.
        registry = os.open(self.pool / "admission/registry.lock", os.O_RDWR)
        try:
            fcntl.flock(registry, fcntl.LOCK_EX)
            for fd in blockers:
                fcntl.flock(fd, fcntl.LOCK_UN)
        finally:
            os.close(registry)
        rows = [self.started(process, marker) for process, marker in children]
        self.assertEqual([row["jobs"] for row in rows], ["7"] * 4)
        for index in range(4):
            self.assert_held(index)
        for process, _ in children:
            self.finish(process)

    def test_automatic_cpu_budget_does_not_borrow_without_memory_headroom(self):
        process, marker = self.spawn(env={"FIXTURE_AVAILABLE_GIB": "16"})
        self.assertEqual(self.started(process, marker)["jobs"], "14")
        self.assert_held(0)
        self.assert_held(1)
        self.assert_free(2)
        self.assert_free(3)
        self.finish(process)

    def test_automatic_full_pool_uses_remainder_cpus(self):
        process, marker = self.spawn(env={"FIXTURE_CPU_COUNT": "20"})
        self.assertEqual(self.started(process, marker)["jobs"], "20")
        for index in range(3):
            self.assert_held(index)
        self.finish(process)

    def test_automatic_borrowed_slots_survive_supervisor_death(self):
        self.supervisor_death_retains_leases(slots=4)

    def test_invalid_cpu_budget_never_starts_a_child(self):
        for options, environment in ((["--cpus", "0"], {}),
                                     (["--cpus", "29"], {}),
                                     (["--cpus", "x"], {}),
                                     (["--cpus", "²"], {}),
                                     (["--cpus", "14"], {"CARGO_BUILD_JOBS": "15"}),
                                     (["--cpus", "14"], {"BUILD_SLOT_HELD": "1", "CARGO_BUILD_JOBS": "7"})):
            with self.subTest(options=options, environment=environment):
                process, marker = self.spawn(*options, env=environment)
                self.assertEqual(process.wait(timeout=5), 2)
                self.assertFalse(marker.exists())

    def test_exclusive_covers_larger_configured_pool_despite_cli_override(self):
        blocker = self.hold(7)
        process, marker = self.spawn("--exclusive", "--slots", "6", env={"BUILD_SLOTS": "8"})
        self.waiting(process, marker, "waiting for all 8 canonical slots")
        self.assert_free(0)
        fcntl.flock(blocker, fcntl.LOCK_UN)
        self.assertEqual(self.started(process, marker)["jobs"], "28")
        for index in range(8):
            self.assert_held(index)
        self.finish(process)

    def test_exclusive_preserves_memory_refusal_before_any_slot_or_child(self):
        process, marker = self.spawn("--exclusive", env={"FIXTURE_AVAILABLE_GIB": "0"})
        self.waiting(process, marker, "GiB available < 8 GiB needed")
        self.assertEqual(list(self.pool.iterdir()), [])

    def test_ordinary_nested_admission_is_immediate_and_retains_share(self):
        process, marker = self.spawn(env={"BUILD_SLOT_HELD": "1", "CARGO_BUILD_JOBS": "2"})
        info = self.started(process, marker)
        self.assertEqual(info["jobs"], "2")
        self.assertIsNone(info["exclusive"])
        self.assertFalse(self.pool.exists())
        self.finish(process)

    def test_nested_exclusive_refuses_shared_upgrade_before_child_or_state(self):
        process, marker = self.spawn("--exclusive", env={"BUILD_SLOT_HELD": "1"})
        stdout, stderr = process.communicate(timeout=5)
        self.assertEqual(process.returncode, 2, (stdout, stderr))
        self.assertIn(b"cannot upgrade shared admission", stderr)
        self.assertFalse(marker.exists())
        self.assertFalse(self.pool.exists())

    def test_exclusive_rejects_nonpositive_slot_count_before_child_or_state(self):
        process, marker = self.spawn("--exclusive", "--slots", "0")
        stdout, stderr = process.communicate(timeout=5)
        self.assertEqual(process.returncode, 2, (stdout, stderr))
        self.assertIn(b"requires a positive slot count", stderr)
        self.assertFalse(marker.exists())
        self.assertFalse(self.pool.exists())

    def test_nested_exclusive_reuses_explicit_exclusive_parent(self):
        process, marker = self.spawn("--exclusive", env={
            "BUILD_SLOT_HELD": "1", "BUILD_SLOT_EXCLUSIVE": "1", "CARGO_BUILD_JOBS": "2",
        })
        info = self.started(process, marker)
        self.assertEqual((info["jobs"], info["exclusive"]), ("2", "1"))
        self.assertFalse(self.pool.exists())
        self.finish(process)

    def test_actual_exclusive_parent_allows_nested_exclusive_without_deadlock(self):
        process, marker = self.spawn("--exclusive", nested=["--exclusive"])
        info = self.started(process, marker)
        self.assertEqual((info["jobs"], info["exclusive"]), ("28", "1"))
        for index in range(4):
            self.assert_held(index)
        self.finish(process)

    def test_actual_shared_parent_cannot_be_upgraded_by_nested_command(self):
        process, marker = self.spawn(nested=["--exclusive"])
        stdout, stderr = process.communicate(timeout=5)
        self.assertEqual(process.returncode, 2, (stdout, stderr))
        self.assertIn(b"cannot upgrade shared admission", stderr)
        self.assertFalse(marker.exists())
        for index in range(4):
            self.assert_free(index)

    def test_fresh_default_admission_clears_stale_exclusive_marker(self):
        process, marker = self.spawn(env={"BUILD_SLOT_EXCLUSIVE": "1"})
        self.assertIsNone(self.started(process, marker)["exclusive"])
        self.finish(process)

    def test_exclusive_preserves_one_job_per_private_worktree(self):
        environment = {"FIXTURE_WORKTREE_LOCK": str(self.root / "worktree.lock")}
        first, one = self.spawn(env=environment)
        self.started(first, one)
        second, two = self.spawn("--exclusive", env=environment)
        self.waiting(second, two, "another build-slot job runs in this worktree")
        self.finish(first)
        self.started(second, two)
        self.finish(second)

    def test_child_exit_and_signal_release_every_exclusive_lock(self):
        process, marker = self.spawn("--exclusive", code=7)
        self.started(process, marker)
        self.finish(process, 7)
        process, marker = self.spawn("--exclusive")
        self.started(process, marker)
        process.send_signal(signal.SIGTERM)
        stdout, stderr = process.communicate(timeout=5)
        self.assertEqual(process.returncode, 128 + signal.SIGTERM, (stdout, stderr))
        for index in range(4):
            self.assert_free(index)


    def test_caller_job_request_is_capped_to_the_admitted_share(self):
        process, marker = self.spawn(env={"CARGO_BUILD_JOBS": "99"})
        self.assertEqual(self.started(process, marker)["jobs"], "7")
        self.finish(process)
        process, marker = self.spawn(env={"CARGO_BUILD_JOBS": "3"})
        self.assertEqual(self.started(process, marker)["jobs"], "3")
        self.finish(process)

    def test_malformed_job_request_refuses_before_any_slot_or_child(self):
        for request in ("0", "-1", "two", "", "9" * 5000):
            with self.subTest(request=request[:8]):
                result = self.invoke("--", sys.executable, "-c", "raise SystemExit(7)",
                                     env={"CARGO_BUILD_JOBS": request})
                self.assertEqual(result.returncode, 2, result)
                self.assertIn(b"REFUSED", result.stderr)
                self.assertFalse(self.pool.exists() and any(self.pool.iterdir()))

class ResourceHelperSourceTests(unittest.TestCase):
    """Load actual gate code against private source/PYC DATA, never a pool."""

    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="build-slot-helper-source-")
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name)
        self.helper = root / "scripts/lib/landing_targo.py"
        self.helper.parent.mkdir(parents=True)
        loader = importlib.machinery.SourceFileLoader("source_reader_gate", str(SCRIPT))
        spec = importlib.util.spec_from_loader(loader.name, loader)
        self.gate = importlib.util.module_from_spec(spec)
        exec(compile(SCRIPT.read_bytes(), str(SCRIPT), "exec", dont_inherit=True),
             self.gate.__dict__)
        self.gate.__file__ = str(root / "scripts/build-slot")
        self.current = b"def resource_fds(env): return (11,)\n"

    def cached(self, previous, current):
        self.assertEqual(len(previous), len(current))
        self.helper.write_bytes(previous)
        stamp = self.helper.stat()
        py_compile.compile(str(self.helper), doraise=True,
                           invalidation_mode=py_compile.PycInvalidationMode.TIMESTAMP)
        self.helper.write_bytes(current)
        os.utime(self.helper, ns=(stamp.st_atime_ns, stamp.st_mtime_ns))
        self.assertEqual(self.helper.stat().st_size, stamp.st_size)
        self.assertEqual(self.helper.stat().st_mtime_ns, stamp.st_mtime_ns)

    def test_current_helper_source_is_loaded_once_and_reused_in_process(self):
        self.helper.write_bytes(self.current)
        first = self.gate.resource_transport_owner()
        self.assertEqual(first.resource_fds({}), (11,))
        self.helper.write_bytes(b"raise RuntimeError('a second load is not allowed')\n")
        self.assertIs(self.gate.resource_transport_owner(), first)
        self.assertEqual(first.resource_fds({}), (11,))

    def test_matching_timestamp_bytecode_cannot_replace_current_helper_source(self):
        self.cached(self.current.replace(b"11", b"99"), self.current)
        self.assertEqual(self.gate.resource_transport_owner().resource_fds({}), (11,))
        self.assertEqual(self.helper.read_bytes(), self.current)

    def test_current_syntax_error_cannot_fall_back_to_matching_valid_bytecode(self):
        broken = b"return 11".ljust(len(self.current) - 1) + b"\n"
        self.cached(self.current, broken)
        with self.assertRaises(SyntaxError):
            self.gate.resource_transport_owner()
        self.assertIsNone(self.gate._EXIT_OWNER)


class ResourceTransportTests(unittest.TestCase):
    def setUp(self):
        isolate_resource_environment(self)
        loader=importlib.machinery.SourceFileLoader('resource_transport_gate',str(SCRIPT))
        spec=importlib.util.spec_from_loader(loader.name,loader)
        self.gate=importlib.util.module_from_spec(spec)
        loader.exec_module(self.gate)
        self.read,self.write=os.pipe()
        self.addCleanup(os.close,self.read)
        self.addCleanup(os.close,self.write)

    def test_five_locator_fields_keep_only_declared_live_descriptors(self):
        for name in ('ATERM_SDK_LEASE_V3','ATERM_WORKLOAD_HOST_STORE_FD_V1',
                     'TRUST_CPU_IMPLICIT_FD','ATERM_WORKLOAD_CPU_FDS_V1','BUILD_SLOT_FENCE_FDS'):
            with self.subTest(name=name):
                self.assertEqual(self.gate.inherited_resource_fds({name:str(self.read)}),(self.read,))
        self.assertEqual(self.gate.inherited_resource_fds({}),())

    def test_gnu_transport_uses_only_effective_advertisement(self):
        closed=os.dup(self.read)
        os.close(closed)
        obsolete=f'{closed},{closed}'
        live=f'{self.read},{self.write}'
        for flags in (f'--jobserver-auth={obsolete} --jobserver-auth={live}',
                      f'--jobserver-auth={live} --jobserver-fds={obsolete}',
                      f'--jobserver-fds={obsolete} --jobserver-fds={live}'):
            self.assertEqual(self.gate.inherited_resource_fds({
                'CARGO_MAKEFLAGS':flags,'MAKEFLAGS':f'--jobserver-auth={obsolete}'}),
                (self.read,self.write))
        for first in ('','-j3',f'--jobserver-auth=-1,-1',f'--jobserver-auth=fifo:/not-opened'):
            self.assertEqual(self.gate.inherited_resource_fds({
                'CARGO_MAKEFLAGS':first,'MAKEFLAGS':f'--jobserver-auth={obsolete}'}),())

    def test_invalid_locators_refuse_before_any_claim_or_child(self):
        closed=os.dup(self.read)
        os.close(closed)
        for name,value in (('ATERM_SDK_LEASE_V3',str(closed)),
                           ('ATERM_WORKLOAD_HOST_STORE_FD_V1','2'),
                           ('TRUST_CPU_IMPLICIT_FD','9999999999'),
                           ('ATERM_WORKLOAD_CPU_FDS_V1',f'{self.read},{self.read}'),
                           ('BUILD_SLOT_FENCE_FDS',''),
                           ('CARGO_MAKEFLAGS','--jobserver-auth=broken')):
            with self.subTest(name=name),mock.patch.dict(os.environ,{name:value},clear=True), \
                 mock.patch.object(self.gate,'slot_directory')as directory, \
                 mock.patch.object(self.gate.subprocess,'Popen')as child:
                with self.assertRaises(self.gate.NamespaceError):
                    self.gate.main(['--','/unreachable'])
                directory.assert_not_called()
                child.assert_not_called()

    def test_invalid_capability_transport_never_downgrades_to_fixed(self):
        with mock.patch.dict(os.environ,{'ATERM_SDK_LEASE_V3':'2147483647'},clear=True), \
             mock.patch.object(self.gate.shutil,'which',return_value='/unreachable/targo'), \
             mock.patch.object(self.gate.subprocess,'Popen')as child:
            with self.assertRaises(self.gate.NamespaceError):
                self.gate.worker_capability(['/unreachable/targo','--unverified','build'])
            child.assert_not_called()

    def test_fresh_or_fixed_admission_cannot_drop_or_mix_ancestor_fences(self):
        for held,protocol in ((None,None),('0','2'),('1','1')):
            env={'BUILD_SLOT_FENCE_FDS':str(self.read)}
            if held is not None:env['BUILD_SLOT_HELD']=held
            if protocol is not None:env['BUILD_SLOT_CPU_PROTOCOL']=protocol
            with self.subTest(held=held,protocol=protocol),mock.patch.dict(os.environ,env,clear=True), \
                 mock.patch.object(self.gate,'slot_directory')as directory, \
                 mock.patch.object(self.gate.os,'execvp')as execute:
                with self.assertRaisesRegex(self.gate.NamespaceError,'existing native epoch'):
                    self.gate.main(['--','/unreachable'])
                directory.assert_not_called()
                execute.assert_not_called()

    def test_existing_native_epoch_keeps_its_fences_and_cpu_cap(self):
        class Executed(Exception):pass
        env={'BUILD_SLOT_FENCE_FDS':str(self.read),'BUILD_SLOT_HELD':'1',
             'BUILD_SLOT_CPU_PROTOCOL':'2','CARGO_BUILD_JOBS':'3'}
        with mock.patch.dict(os.environ,env,clear=True), \
             mock.patch.object(self.gate,'worker_capability',return_value=True), \
             mock.patch.object(self.gate.os,'execvp',side_effect=Executed)as execute, \
             mock.patch.object(self.gate,'slot_directory')as directory:
            with self.assertRaises(Executed):
                self.gate.main(['--','/selected/targo','--unverified','build'])
            self.assertEqual(os.environ['BUILD_SLOT_FENCE_FDS'],str(self.read))
            self.assertEqual(os.environ['CARGO_BUILD_JOBS'],'3')
            self.assertEqual(execute.call_args.args,
                ('/selected/targo',['/selected/targo','--resource-worker-v2','--unverified','build']))
            directory.assert_not_called()


class AdmissionLeaseTests(unittest.TestCase):
    def setUp(self):
        isolate_resource_environment(self)
        loader = importlib.machinery.SourceFileLoader("queue_build_slot", str(SCRIPT))
        spec = importlib.util.spec_from_loader(loader.name, loader)
        self.gate = importlib.util.module_from_spec(spec)
        loader.exec_module(self.gate)
        self.temporary = tempfile.TemporaryDirectory(prefix="build-slot-queue-")
        self.addCleanup(self.temporary.cleanup)
        self.gate.DIR = self.temporary.name

    def test_queue_lease_not_recorded_pid_proves_waiter_liveness(self):
        directory = Path(self.gate.DIR) / "admission"
        launcher_directories(directory, mode=0o700)
        path = directory / "wait-1"
        held = os.open(path, os.O_CREAT | os.O_RDWR, 0o600)
        try:
            fcntl.flock(held, fcntl.LOCK_EX)
            os.write(held, b'{"pid": -1, "arbitrary": "not authority"}')
            with self.gate.AdmissionWaiter("new waiter") as waiter:
                self.assertIsNone(waiter.attempt(lambda: True, 128))
                self.assertFalse(os.get_inheritable(waiter.fd))
                fcntl.flock(held, fcntl.LOCK_UN)
                own_fd = waiter.fd
                self.assertTrue(waiter.attempt(lambda: True, 128))
                self.assertFalse(path.exists())
            with self.assertRaises(OSError):
                os.fstat(own_fd)
            self.assertEqual(list(directory.glob("wait-*")), [])
        finally:
            os.close(held)


class NamespaceDirectoryTests(unittest.TestCase):
    """The launcher's own namespace creation, independent of the caller's umask."""

    def setUp(self):
        isolate_resource_environment(self)
        loader = importlib.machinery.SourceFileLoader("namespace_build_slot", str(SCRIPT))
        spec = importlib.util.spec_from_loader(loader.name, loader)
        self.gate = importlib.util.module_from_spec(spec)
        loader.exec_module(self.gate)
        temporary = tempfile.TemporaryDirectory(prefix="build-slot-namespace-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.gate.ADOPTION_DIR = str(self.root / "adopted")

    def under_group_writable_umask(self, action):
        previous = os.umask(0o002)
        try:
            return action()
        finally:
            os.umask(previous)

    def test_legacy_fence_admits_the_namespace_it_makes_under_a_group_writable_umask(self):
        home = self.root / "home"
        home.mkdir()
        directory = home / ".cache" / "build-slot"
        fences = self.under_group_writable_umask(
            lambda: self.gate.try_legacy_fence(str(directory), 2, priority=True))
        self.assertIsNotNone(fences)
        for fd in fences:
            os.close(fd)
        for path in (home / ".cache", directory):
            self.assertEqual(oct(made_mode(path)), oct(0o700), path)

    def set_group_id_mkdir(self, extra=0):
        """os.mkdir as Linux runs it under a set-group-ID parent: the new directory gets S_ISGID.

        `extra` adds permission bits to stand in for a default ACL that widens it.
        """
        real_mkdir = os.mkdir
        made = []

        def inherited(path, mode=0o777):
            real_mkdir(path, mode)
            # chmod keeps S_ISGID only on a group this process is in: give it our own.
            os.chown(path, -1, os.getegid())
            os.chmod(path, stat.S_IMODE(os.lstat(path).st_mode) | stat.S_ISGID | extra)
            made.append(path)

        return mock.patch.object(self.gate.os, "mkdir", side_effect=inherited), made

    def test_a_created_directory_that_inherits_set_group_id_is_admitted(self):
        # S_ISGID names the group of what is made inside; with no group
        # permission bits it grants that group nothing, so 02700 is the private
        # directory the launcher asked for.
        patch, made = self.set_group_id_mkdir()
        target = self.root / "inherited" / "pool"
        with patch:
            self.gate.namespace_directory(str(target))
        self.assertEqual(made, [str(self.root / "inherited"), str(target)])
        for path in made:
            self.assertEqual(oct(stat.S_IMODE(os.lstat(path).st_mode)), oct(0o2700), path)

    def test_a_created_set_group_id_directory_open_to_its_group_or_others_is_refused(self):
        for serial, (extra, shown) in enumerate([(0o020, "2720"), (0o040, "2740"), (0o001, "2701")]):
            with self.subTest(mode=shown):
                patch, made = self.set_group_id_mkdir(extra)
                parent = self.root / f"shared-{serial}"
                target = parent / "pool"
                with patch:
                    with self.assertRaises(self.gate.NamespaceError) as refused:
                        self.gate.namespace_directory(str(target))
                self.assertIn(f"build-slot created {parent} but found mode {shown}",
                              str(refused.exception))
                self.assertEqual(made, [str(parent)])
                self.assertFalse(target.exists())

    def test_a_created_directory_whose_mode_is_not_0700_is_refused(self):
        # A default ACL or filesystem can override the requested mode; the
        # launcher verifies what it made instead of trusting the request.
        real_mkdir = os.mkdir

        def widened(path, mode=0o777):
            real_mkdir(path, mode)
            os.chmod(path, 0o775)

        target = self.root / "made" / "pool"
        with mock.patch.object(self.gate.os, "mkdir", side_effect=widened):
            with self.assertRaises(self.gate.NamespaceError) as refused:
                self.gate.namespace_directory(str(target))
        self.assertIn(f"build-slot created {self.root / 'made'} but found mode 0775", str(refused.exception))
        self.assertFalse(target.exists())

    def test_an_existing_parent_is_never_changed_and_the_new_leaf_is_owner_only(self):
        parent = self.root / "existing"
        parent.mkdir()
        parent.chmod(0o755)
        target = parent / "pool"
        self.under_group_writable_umask(lambda: self.gate.namespace_directory(str(target)))
        self.assertEqual(stat.S_IMODE(parent.stat().st_mode), 0o755)
        self.assertEqual(stat.S_IMODE(target.stat().st_mode), 0o700)


class NativeIdentityFailureTests(unittest.TestCase):
    def setUp(self):
        isolate_resource_environment(self)
        loader = importlib.machinery.SourceFileLoader("identity_build_slot", str(SCRIPT))
        spec = importlib.util.spec_from_loader(loader.name, loader)
        self.gate = importlib.util.module_from_spec(spec)
        loader.exec_module(self.gate)

    def test_hidden_linux_procfs_requires_independent_kernel_absence(self):
        # Synthetic native-query failures; this does not claim a Linux run.
        for probe, absent in ((None, False), (PermissionError(), False),
                              (ProcessLookupError(), True)):
            with self.subTest(probe=type(probe).__name__):
                with mock.patch.object(self.gate.sys, "platform", "linux"), \
                     mock.patch("builtins.open", side_effect=FileNotFoundError()), \
                     mock.patch.object(self.gate.os, "kill", side_effect=probe):
                    if absent:
                        self.assertIsNone(self.gate.process_identity(12345))
                    else:
                        with self.assertRaises(self.gate.IdentityError):
                            self.gate.process_identity(12345)

    def test_unavailable_mac_identity_requires_independent_kernel_absence(self):
        import ctypes
        import errno
        from types import SimpleNamespace

        def missing_info(*_):
            ctypes.set_errno(errno.ESRCH)
            return 0

        lib = SimpleNamespace(proc_pidinfo=missing_info, proc_pidpath=lambda *_: 0)
        for probe, absent in ((None, False), (PermissionError(), False),
                              (ProcessLookupError(), True)):
            with self.subTest(probe=type(probe).__name__):
                with mock.patch.object(self.gate.sys, "platform", "darwin"), \
                     mock.patch.object(ctypes, "CDLL", return_value=lib), \
                     mock.patch.object(self.gate.os, "kill", side_effect=probe):
                    if absent:
                        self.assertIsNone(self.gate.process_identity(12345))
                    else:
                        with self.assertRaises(self.gate.IdentityError):
                            self.gate.process_identity(12345)




ACCOUNT_WRAPPER = r"""
import pwd, runpy, sys, types
script, account, *arguments = sys.argv[1:]
def account_record(uid):
    if account == "missing-account":
        raise KeyError(uid)
    return types.SimpleNamespace(pw_dir=account)
pwd.getpwuid = account_record
sys.argv = [script, *arguments]
runpy.run_path(script, run_name="__main__")
"""


LEAF = r"""
import json, os, pathlib, sys, time
ready, release = map(pathlib.Path, sys.argv[1:])
ready.write_text(json.dumps({"pid": os.getpid(), "parent_pid": os.getppid(),
                            "directory": os.environ.get("BUILD_SLOT_DIR"),
                            "jobs": os.environ.get("CARGO_BUILD_JOBS"),
                            "held": os.environ.get("BUILD_SLOT_HELD")}))
deadline = time.monotonic() + 30
while not release.exists():
    if time.monotonic() >= deadline:
        raise RuntimeError("fixture owner did not release its child")
    time.sleep(0.01)
ready.with_suffix(".done").write_text("released")
"""


SUBPROCESS_OWNER = r"""
import json, os, pathlib, subprocess, sys, time
ready, release = map(pathlib.Path, sys.argv[1:3])
worker_ready = ready.with_suffix(".worker-ready")
# Match an admitted Python orchestrator that waits for a subprocess. The worker
# gets Popen's normal close_fds behavior; the orchestrator retains admission.
worker = subprocess.Popen([sys.executable, "-I", "-S", "-B", "-c", sys.argv[3],
                           str(worker_ready), str(release)])
deadline = time.monotonic() + 10
while not worker_ready.exists():
    if time.monotonic() >= deadline:
        raise RuntimeError("fixture subprocess did not become ready")
    time.sleep(0.01)
ready.write_text(json.dumps({"pid": os.getpid(), "parent_pid": os.getppid(),
                            "worker_pid": worker.pid}))
code = worker.wait()
ready.with_suffix(".done").write_text("released")
raise SystemExit(code)
"""


class BuildSlotTests(unittest.TestCase):
    def setUp(self):
        isolate_resource_environment(self)
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        self.account = self.root / "account"
        self.account.mkdir()
        self.directory = self.account / ".cache/build-slot"
        self.processes = []
        self.releases = []
        self.completions = []
        self.addCleanup(self.close_children)

    def environment(self, name="a"):
        home = self.root / ("private-home-" + name)
        tmp = self.root / ("private-tmp-" + name)
        home.mkdir(exist_ok=True)
        tmp.mkdir(exist_ok=True)
        return {"HOME": str(home), "TMPDIR": str(tmp), "XDG_CACHE_HOME": str(home / "xdg"),
                "PATH": "/usr/bin:/bin:/usr/sbin:/sbin", "LANG": "C", "LC_ALL": "C",
                "GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": os.devnull,
                "BUILD_SLOTS": "1", "BUILD_SLOT_MEM_GB": "0"}

    def arguments(self, *arguments, account=None):
        return [sys.executable, "-I", "-S", "-B", "-c", ACCOUNT_WRAPPER, str(SCRIPT),
                str(self.account) if account is None else str(account), *arguments]

    def query(self, *arguments, env=None, account=None, cwd=None, umask=-1):
        child = subprocess.Popen(self.arguments(*arguments, account=account),
                                 cwd=cwd or self.root, env=env or self.environment(),
                                 stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                                 stderr=subprocess.PIPE, text=True, start_new_session=True,
                                 umask=umask)
        self.processes.append(child)
        out, err = child.communicate(timeout=10)
        return child.returncode, out, err

    def close_children(self):
        # Release every fixture child first, including ones whose gates are still
        # queued. Termination is a bounded fallback for these exact own Popen objects.
        for release in self.releases:
            release.touch(exist_ok=True)
        for child in self.processes:
            try:
                child.communicate(timeout=10)
            except subprocess.TimeoutExpired:
                child.terminate()
                try:
                    child.communicate(timeout=5)
                except subprocess.TimeoutExpired:
                    child.kill()
                    child.communicate(timeout=5)
        # A killed wrapper cannot reap its surviving admitted command. Keep
        # release markers present until those fixtures acknowledge them, so
        # TemporaryDirectory cleanup cannot race away the wake-up condition.
        for ready, completed in self.completions:
            if ready.exists():
                self.until(completed.exists, "orphaned fixture release acknowledgment")

    def until(self, condition, label):
        deadline = time.monotonic() + 10
        while not condition():
            if time.monotonic() >= deadline:
                self.fail("timed out waiting for " + label)
            time.sleep(0.01)

    def start_waiter(self, name, cwd=None, program=LEAF, extra_arguments=()):
        cwd = cwd or self.root / ("cwd-" + name)
        cwd.mkdir(exist_ok=True)
        ready, release = self.root / (name + ".ready"), self.root / (name + ".release")
        self.releases.append(release)
        self.completions.append((ready, ready.with_suffix(".done")))
        log = self.root / (name + ".stderr")
        with log.open("w") as errors:
            child = subprocess.Popen(self.arguments("--", sys.executable, "-I", "-S", "-B", "-c",
                                                   program, str(ready), str(release),
                                                   *extra_arguments),
                                     cwd=cwd, env=self.environment(name), stdin=subprocess.DEVNULL,
                                     stdout=subprocess.DEVNULL, stderr=errors, start_new_session=True)
        self.processes.append(child)
        return child, ready, release, log

    def assert_holder(self, pid, env):
        code, out, err = self.query("status", env=env)
        self.assertEqual(code, 0, err)
        self.assertIn("dir=" + str(self.directory), out)
        self.assertIn("slot 0: HELD pid=" + str(pid) + " ", out)

    def test_two_private_homes_share_one_slot_across_distinct_cwds(self):
        launcher_directories(self.directory)
        with (self.directory / "slot-0").open("w+") as holder:
            fcntl.flock(holder, fcntl.LOCK_EX | fcntl.LOCK_NB)
            json.dump({"pid": os.getpid(), "started": time.time(), "cmd": "fixture holder"}, holder)
            holder.flush()
            a, b = self.start_waiter("a"), self.start_waiter("b")
            self.until(lambda: any(w[1].exists() for w in (a, b)) or all(
                "waiting for one of 1 slots" in w[3].read_text() for w in (a, b)), "both gate waiters")
            self.assertFalse(any(w[1].exists() for w in (a, b)),
                             "a private-HOME gate entered while the canonical slot was held")
            for name in ("a", "b"):
                self.assert_holder(os.getpid(), self.environment(name))
            fcntl.flock(holder, fcntl.LOCK_UN)

            self.until(lambda: any(w[1].exists() for w in (a, b)), "one admitted child")
            entered = [w for w in (a, b) if w[1].exists()]
            self.assertEqual(len(entered), 1, "both gates entered a one-slot pool")
            first = entered[0]
            second = b if first is a else a
            self.assert_holder(json.loads(first[1].read_text())["pid"], self.environment("a"))
            with self.assertRaises(BlockingIOError):
                fcntl.flock(holder, fcntl.LOCK_EX | fcntl.LOCK_NB)
            self.assertFalse(second[1].exists(), "second child entered while the first owned the slot")
            first[2].touch()
            first[0].communicate(timeout=10)
            self.assertEqual(first[0].returncode, 0)
            self.until(second[1].exists, "second admitted child")
            self.assert_holder(json.loads(second[1].read_text())["pid"], self.environment("b"))
            second[2].touch()
            second[0].communicate(timeout=10)
            self.assertEqual(second[0].returncode, 0)

        for waiter in (a, b):
            child = json.loads(waiter[1].read_text())
            self.assertEqual(child["directory"], str(self.directory))
            self.assertEqual(child["held"], "1")
        code, out, err = self.query("status")
        self.assertEqual(code, 0, err)
        self.assertIn("slot 0: free", out)
        self.assertFalse((self.root / "private-home-a/.cache/build-slot").exists())
        self.assertFalse((self.root / "private-home-b/.cache/build-slot").exists())

    def test_default_ignores_home_tmpdir_and_xdg_cache_home(self):
        for env in (self.environment("a"), self.environment("b")):
            code, out, err = self.query("status", env=env)
            self.assertEqual(code, 0, err)
            self.assertIn("dir=" + str(self.directory), out)

    def test_same_worktree_still_serializes_before_machine_admission(self):
        cwd = self.root / "worktree"
        cwd.mkdir()
        git = subprocess.Popen(["git", "init", "--quiet", str(cwd)], env=self.environment(),
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        self.processes.append(git)
        out, err = git.communicate(timeout=10)
        self.assertEqual(git.returncode, 0, (out, err))
        first = self.start_waiter("a", cwd)
        self.until(first[1].exists, "first worktree child")
        second = self.start_waiter("b", cwd)
        self.until(lambda: second[1].exists() or "another build-slot job runs in this worktree"
                   in second[3].read_text(), "worktree waiter")
        self.assertFalse(second[1].exists())
        self.assertIn("pid=" + str(json.loads(first[1].read_text())["pid"]), second[3].read_text())
        first[2].touch()
        first[0].communicate(timeout=10)
        self.assertEqual(first[0].returncode, 0)
        self.until(second[1].exists, "second worktree child")
        second[2].touch()
        second[0].communicate(timeout=10)
        self.assertEqual(second[0].returncode, 0)

    def assert_wrapper_death_retains_admission(self, program, extra_arguments=()):
        cwd = self.root / "worktree"
        cwd.mkdir()
        subprocess.run(["git", "init", "--quiet", str(cwd)], env=self.environment(),
                       check=True, capture_output=True, timeout=10)
        first = self.start_waiter("a", cwd, program, extra_arguments)
        self.until(first[1].exists, "first admitted command")
        owner = json.loads(first[1].read_text())
        self.assertEqual(owner["parent_pid"], first[0].pid,
                         "the ready marker must name this wrapper's own command")
        self.assert_holder(owner["pid"], self.environment())

        # Kill only our Popen-owned wrapper, leaving its separately sessioned
        # command running exactly as a lost tool session can do.
        first[0].kill()
        first[0].communicate(timeout=10)
        self.assertEqual(first[0].returncode, -9)
        os.kill(owner["pid"], 0)
        if "worker_pid" in owner:
            os.kill(owner["worker_pid"], 0)
        self.assert_holder(owner["pid"], self.environment())
        for lock in (self.directory / "slot-0", cwd / ".git/build-slot.lock"):
            with lock.open("r+") as handle:
                with self.assertRaises(BlockingIOError, msg=str(lock)):
                    fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)

        # A different worktree reaches the global slot rather than stopping
        # at the first command's worktree lock. Neither reservation was lost.
        second = self.start_waiter("b")
        self.until(lambda: second[1].exists() or "waiting for one of 1 slots"
                   in second[3].read_text(), "second global-slot waiter")
        self.assertFalse(second[1].exists(), "wrapper death admitted concurrent heavy work")
        first[2].touch()
        self.until(second[1].exists, "second command after first owner exits")
        with (cwd / ".git/build-slot.lock").open("r+") as handle:
            fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
            fcntl.flock(handle, fcntl.LOCK_UN)
        second[2].touch()
        second[0].communicate(timeout=10)
        self.assertEqual(second[0].returncode, 0)
        for lock in (self.directory / "slot-0", cwd / ".git/build-slot.lock"):
            with lock.open("r+") as handle:
                fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
                fcntl.flock(handle, fcntl.LOCK_UN)

    def test_wrapper_death_keeps_direct_command_admitted(self):
        self.assert_wrapper_death_retains_admission(LEAF)

    def test_wrapper_death_keeps_python_subprocess_owner_admitted(self):
        self.assert_wrapper_death_retains_admission(SUBPROCESS_OWNER, (LEAF,))

    def test_default_with_absent_home_uses_account_directory(self):
        env = self.environment()
        env.pop("HOME")
        code, out, err = self.query("status", env=env)
        self.assertEqual(code, 0, err)
        self.assertIn("dir=" + str(self.directory), out)

    def test_unusable_account_directory_refuses_without_private_fallback(self):
        file = self.root / "account-file"
        file.write_text("not a directory")
        for account in ("missing-account", "", "relative-home", str(self.root / "absent"), str(file)):
            with self.subTest(account=account):
                code, out, err = self.query("status", account=account)
                self.assertEqual(code, 2, (out, err))
                self.assertIn("namespace", err)
                self.assertFalse((self.root / "private-home-a/.cache/build-slot").exists())

    def test_explicit_relative_directory_is_propagated_but_cannot_hide_unknown_registry(self):
        env = self.environment()
        env.update(BUILD_SLOT_DIR="configured-pool", CARGO_BUILD_JOBS="3")
        leaf = "import json,os; print(json.dumps({k:os.environ[k] for k in ('BUILD_SLOT_DIR','BUILD_SLOT_HELD','CARGO_BUILD_JOBS')}))"
        code, out, err = self.query("--", sys.executable, "-I", "-S", "-B", "-c", leaf,
                                    env=env)
        self.assertEqual(code, 0, err)
        self.assertEqual(json.loads(out), {"BUILD_SLOT_DIR": str(self.root / "configured-pool"),
                                          "BUILD_SLOT_HELD": "1", "CARGO_BUILD_JOBS": "3"})
        code, out, err = self.query("status", env=env)
        self.assertEqual(code, 0, err)
        self.assertIn("dir=" + str(self.root / "configured-pool"), out)

        # The incoming global adoption registry must remain discoverable even
        # when a caller selects a different pool. An unknown account refuses.
        for arguments in [("status",), ("--", sys.executable, "-c", "print('must not run')")]:
            code, out, err = self.query(*arguments, env=env, account="missing-account")
            self.assertEqual(code, 2, (out, err))
            self.assertEqual(out, "")
            self.assertIn("canonical user home is unavailable", err)

    def test_admitted_child_status_keeps_directory_after_home_change(self):
        env = self.environment()
        env["BUILD_SLOT_DIR"] = str(self.root / "configured-pool")
        leaf = r"""
import os, subprocess, sys
os.environ['HOME'] = sys.argv[1]
child = subprocess.Popen(sys.argv[2:], env=os.environ, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
out, err = child.communicate(timeout=10)
print(out, end='')
sys.stderr.write(err)
raise SystemExit(child.returncode)
"""
        inner = self.arguments("status")
        code, out, err = self.query("--", sys.executable, "-I", "-S", "-B", "-c", leaf,
                                    str(self.root / "another-home"), *inner, env=env)
        self.assertEqual(code, 0, err)
        self.assertIn("dir=" + env["BUILD_SLOT_DIR"], out)
        self.assertIn("slot 0: HELD", out)

    def test_nested_admission_remains_free_and_preserves_child_exit(self):
        env = self.environment()
        env.update(BUILD_SLOT_HELD="1", BUILD_SLOT_DIR=str(self.root / "configured-pool"))
        code, out, err = self.query("--", sys.executable, "-I", "-S", "-B", "-c", "raise SystemExit(7)",
                                    env=env, account="missing-account")
        self.assertEqual(code, 7, err)
        self.assertFalse((self.root / "configured-pool").exists())

    def test_help_does_not_need_account_resolution(self):
        code, out, err = self.query("--help", account="missing-account")
        self.assertEqual(code, 0, err)
        self.assertIn("build-slot", out)
        self.assertFalse(self.directory.exists())

    def capacity_pool(self):
        """A private trust-build-cpu pool, so fixed admission judges the namespace."""
        suffix = ("Library/Caches/aterm/capacity" if sys.platform == "darwin"
                  else ".cache/aterm/capacity")
        pool = self.account / suffix / "build-cpu-v1"
        pool.mkdir(parents=True)
        pool.chmod(0o700)
        cpus = os.cpu_count()
        rows = [f"trust-build-cpu-v1 slots={cpus}"]
        for index in range(cpus):
            slot = pool / f"slot-{index:08x}"
            slot.touch()
            slot.chmod(0o600)
            meta = slot.stat()
            rows.append(f"slot={index} dev={meta.st_dev} ino={meta.st_ino}")
        manifest = pool / "pool"
        manifest.write_text("\n".join(rows) + "\n")
        manifest.chmod(0o600)

    def assert_owner_only(self, *paths):
        for path in paths:
            meta = os.lstat(path)
            self.assertTrue(stat.S_ISDIR(meta.st_mode), path)
            self.assertEqual(meta.st_uid, os.geteuid(), path)
            self.assertEqual(oct(made_mode(path)), oct(0o700), path)

    def admitted(self, env=None):
        code, out, err = self.query("--", sys.executable, "-I", "-S", "-B", "-c",
                                    "print('admitted')", env=env, umask=0o002)
        self.assertEqual((code, out), (0, "admitted\n"), err)

    def test_namespace_made_under_a_group_writable_umask_is_owner_only_and_admitted(self):
        # The account home exists, as the launcher requires; everything below it
        # is made by the launcher itself under the umask a login shell here uses.
        cache = self.account / ".cache"
        self.assertFalse(cache.exists())
        code, out, err = self.query("status", umask=0o002)
        self.assertEqual(code, 0, err)
        self.assertIn("dir=" + str(self.directory), out)
        self.assert_owner_only(cache, self.directory)
        # A native CPU pool makes fixed admission judge the namespace's mode.
        self.capacity_pool()
        self.admitted()

    def test_configured_namespace_and_its_missing_ancestors_are_made_owner_only(self):
        self.capacity_pool()
        fresh = self.root / "fresh"
        pool = fresh / "nested" / "pool"
        env = self.environment()
        env["BUILD_SLOT_DIR"] = str(pool)
        self.admitted(env)
        self.assert_owner_only(fresh, fresh / "nested", pool)

    def test_adoption_makes_its_registry_and_namespace_owner_only(self):
        cwd = self.root / "adopted-cwd"
        cwd.mkdir()
        job = subprocess.Popen([sys.executable, "-I", "-S", "-B", "-c", "import sys; sys.stdin.read()"],
                               cwd=cwd, stdin=subprocess.PIPE, start_new_session=True)
        try:
            code, out, err = self.query("adopt", str(job.pid), cwd=cwd, umask=0o002)
            self.assertEqual(code, 0, err)
            self.assertIn("adopted pid=" + str(job.pid), out)
        finally:
            job.communicate(timeout=10)
        self.assert_owner_only(self.account / ".cache", self.directory, self.directory / "adopted")
        self.capacity_pool()
        self.admitted()

    def test_existing_group_writable_namespace_is_refused_and_left_unchanged(self):
        (self.account / ".cache").mkdir(mode=0o700)
        self.directory.mkdir()
        self.directory.chmod(0o775)
        expected = (f"{self.directory} has mode 0775, writable by its group or others; "
                    f"build-slot never changes an existing directory: run chmod go-w {self.directory}")
        for arguments in [("status",), ("--", sys.executable, "-c", "print('must not run')")]:
            with self.subTest(arguments=arguments[0]):
                code, out, err = self.query(*arguments)
                self.assertEqual(code, 2, (out, err))
                self.assertNotIn("must not run", out)
                self.assertIn("build-slot: namespace refused: " + expected, err)
                self.assertEqual(stat.S_IMODE(self.directory.stat().st_mode), 0o775)
        self.assertEqual(list(self.directory.iterdir()), [])

    def assert_modes(self, mode, *paths):
        for path in paths:
            self.assertEqual(oct(stat.S_IMODE(path.lstat().st_mode)), oct(mode), path)

    def test_status_never_changes_an_admitted_existing_namespace(self):
        # 0755 is the namespace an older launcher made under umask 022. It is
        # admitted as it is: build-slot never chmods a directory that existed.
        launcher_directories(self.directory)
        code, out, err = self.query("status", umask=0o002)
        self.assertEqual(code, 0, err)
        self.assertIn("dir=" + str(self.directory), out)
        self.assert_modes(0o755, self.account / ".cache", self.directory)

    def test_a_fixed_run_never_changes_an_admitted_existing_namespace(self):
        launcher_directories(self.directory)
        self.admitted()
        self.assert_modes(0o755, self.account / ".cache", self.directory)
        # A native CPU pool makes fixed admission open and judge the namespace too.
        self.capacity_pool()
        self.admitted()
        self.assert_modes(0o755, self.account / ".cache", self.directory)
        # What the run made inside it is the launcher's own, and owner-only.
        self.assert_owner_only(self.directory / "admission")


class ResourceCommandTest(unittest.TestCase):
    def setUp(self):
        isolate_resource_environment(self)
        temporary = tempfile.TemporaryDirectory(prefix="resource-command.")
        self.addCleanup(temporary.cleanup)
        self.runner = Path(temporary.name) / "aterm runner"
        self.runner.touch()
        self.runner.chmod(0o755)
        loader = importlib.machinery.SourceFileLoader("resource_gate", str(SCRIPT))
        spec = importlib.util.spec_from_loader(loader.name, loader)
        self.gate = importlib.util.module_from_spec(spec)
        loader.exec_module(self.gate)
        self.command = ["native-compiler", "--argument=must-not-be-in-job-label"]
        self.env = {"ATERM_CHILD": "1", "PATH": "/tool/bin"}

    def capability(self, text, returncode=0):
        return subprocess.CompletedProcess([], returncode, stdout=text, stderr="")

    def test_no_aterm_context_performs_no_probe(self):
        with mock.patch.object(self.gate.subprocess, "run") as run:
            self.assertEqual(self.gate.resource_command(self.command, {}), self.command)
        run.assert_not_called()

    def test_explicit_discovery_cli_does_not_need_the_compiler_path(self):
        env = dict(self.env, BUILD_SLOT_ATERM_CLI=str(self.runner))
        record = "OK resources version=1 runner=" + quote(str(self.runner), safe="")
        with mock.patch.object(self.gate.shutil, "which", return_value=None) as which, \
                mock.patch.object(self.gate.subprocess, "run", return_value=self.capability(record)) as run:
            result = self.gate.resource_command(self.command, env)
        which.assert_not_called()
        self.assertEqual(run.call_args.args[0],
                         [str(self.runner), "ctl", "@self", "resources", "capabilities"])
        self.assertEqual(result[result.index("--") + 1:], self.command)

    def test_invalid_explicit_discovery_cli_never_falls_back_to_path(self):
        for cli in ("relative/aterm", str(self.runner.parent), str(self.runner.parent / "missing")):
            with self.subTest(cli=cli), \
                    mock.patch.object(self.gate.shutil, "which", return_value=str(self.runner)) as which, \
                    mock.patch.object(self.gate.subprocess, "run") as run:
                result = self.gate.resource_command(self.command, dict(self.env, BUILD_SLOT_ATERM_CLI=cli))
            self.assertEqual(result, self.command)
            which.assert_not_called()
            run.assert_not_called()

    def test_malformed_or_unsupported_capabilities_never_launch_a_runner(self):
        path = quote(str(self.runner), safe="")
        records = ["", "OK version=1", "OK resources version=2 runner=" + path,
                   "OK resources version=1 version=1 runner=" + path,
                   "OK resources version=1 available=0 runner=" + path,
                   "OK resources version=1 available=unknown runner=" + path,
                   "OK resources capabilities capabilities version=1 runner=" + path,
                   "OK resources version=1 runner=relative",
                   "OK resources version=1 runner=%GG",
                   "OK resources version=1 runner=%00",
                   "OK resources version=1 runner=" + quote(str(self.runner.parent / "missing"), safe="")]
        for record in records:
            with self.subTest(record=record), \
                    mock.patch.object(self.gate.shutil, "which", return_value="/cli/aterm"), \
                    mock.patch.object(self.gate.subprocess, "run", return_value=self.capability(record)):
                self.assertEqual(self.gate.resource_command(self.command, self.env), self.command)

    def test_control_errors_are_unreported_without_an_unknown_command_probe(self):
        for error in (subprocess.TimeoutExpired("ctl", 5), OSError("control unavailable"),
                      UnicodeDecodeError("utf8", b"\xff", 0, 1, "invalid response")):
            with self.subTest(error=type(error).__name__), \
                    mock.patch.object(self.gate.shutil, "which", return_value="/cli/aterm"), \
                    mock.patch.object(self.gate.subprocess, "run", side_effect=error) as run:
                self.assertEqual(self.gate.resource_command(self.command, self.env), self.command)
            self.assertEqual(run.call_args.args[0],
                             ["/cli/aterm", "ctl", "@self", "resources", "capabilities"])

    def test_reported_runner_and_host_ai_default_preserve_original_arguments(self):
        record = "OK resources version=1 runner=" + quote(str(self.runner), safe="") + " ai=claude"
        for env in (self.env, {"ATERM_PARENT_SESSION_ID": "s-parent", "PATH": "/tool/bin"}):
            with self.subTest(context=env), \
                    mock.patch.object(self.gate.shutil, "which", return_value="/older/client/aterm"), \
                    mock.patch.object(self.gate.subprocess, "run", return_value=self.capability(record)):
                result = self.gate.resource_command(self.command, env)
            self.assertEqual(result[:4], [str(self.runner), "resource-run", "--session", "@self"])
            self.assertNotIn("--ai", result, "authenticated target derives the AI default")
            self.assertEqual(result[result.index("--") + 1:], self.command)
            self.assertNotIn(self.command[1], result[result.index("--job") + 1])

    def test_valid_native_path_names_fit_the_host_job_label_contract(self):
        record = "OK resources version=1 runner=" + quote(str(self.runner), safe="")
        cases = [("a" * 255, "compiler"), ("λ" * 120, "compiler"),
                 ("work\n\x1bdir", "compiler\tname"), ("bytes-\udcff", "compiler"),
                 (" " * 240 + "x", "compiler"), ("a" * 199, "🦀" * 40)]
        for directory, executable in cases:
            command = ["/bin/" + executable, "", "--argument=kept-exactly"]
            with self.subTest(directory=repr(directory), executable=executable), \
                    mock.patch.object(self.gate.os, "getcwd", return_value="/tmp/" + directory), \
                    mock.patch.object(self.gate.shutil, "which", return_value="/cli/aterm"), \
                    mock.patch.object(self.gate.subprocess, "run", return_value=self.capability(record)):
                result = self.gate.resource_command(command, self.env)
            label = result[result.index("--job") + 1]
            self.assertTrue(label.strip(), "the host refuses an empty job label")
            self.assertLessEqual(len(label.encode("utf-8")), 200, "the host's byte limit")
            self.assertFalse(any(ord(c) < 32 or 0x7f <= ord(c) <= 0x9f for c in label),
                             "the host refuses control characters")
            self.assertEqual(result[result.index("--") + 1:], command)




# Additional real-process exclusive-window controls from the recursive branch.
EXCLUSIVE_GATE = Path(__file__).resolve().parents[1] / "build-slot"

EXCLUSIVE_LAUNCHER = r'''
import importlib.machinery, importlib.util, json, pathlib, sys, time, pwd
from types import SimpleNamespace
fixture_home = pathlib.Path(sys.argv[2]).parent
pwd.getpwuid = lambda uid: SimpleNamespace(pw_dir=str(fixture_home))
loader = importlib.machinery.SourceFileLoader("gate", sys.argv[1])
spec = importlib.util.spec_from_loader(loader.name, loader)
gate = importlib.util.module_from_spec(spec)
loader.exec_module(gate)
state = pathlib.Path(sys.argv[2])
def read(key):
    return json.loads(state.read_text())[key]
gate.MEASURED_NCPU = read("cpus")
gate.NCPU = gate.MEASURED_NCPU or 4
gate.available_gib = lambda: read("memory")
gate.load1 = lambda: read("load")
gate.build_processes = lambda: read("builds")
gate.QUIET_SECONDS = 0.12
sleep = time.sleep
gate.time.sleep = lambda seconds: sleep(min(seconds, 0.02))
try:
    sys.exit(gate.main(sys.argv[3:]))
except gate.AdmissionTimeout:
    print("admission wait timed out; no command was started", file=sys.stderr)
    sys.exit(2)
'''

EXCLUSIVE_LEGACY = r'''
import fcntl, os, pathlib, sys, time
pool, count, started = sys.argv[1:]
while True:
    for i in range(int(count)):
        fd = os.open(os.path.join(pool, "slot-" + str(i)), os.O_RDWR | os.O_CREAT, 0o644)
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
            pathlib.Path(started).write_text(str(i))
            while True: time.sleep(1)
        except BlockingIOError:
            os.close(fd)
    time.sleep(0.02)
'''

EXCLUSIVE_CHILD = r'''
import json, os, pathlib, signal, sys, time
if len(sys.argv) > 2:
    def delayed_exit(sig, frame):
        pathlib.Path(sys.argv[1] + ".term").touch()
        time.sleep(0.2)
        sys.exit(128 + sig)
    signal.signal(signal.SIGTERM, delayed_exit)
pathlib.Path(sys.argv[1]).write_text(json.dumps({k: os.environ.get(k) for k in ("BUILD_SLOT_HELD", "CARGO_BUILD_JOBS")}))
if len(sys.argv) > 2:
    while True: time.sleep(1)
'''

class BuildSlotTest(unittest.TestCase):
    def setUp(self):
        isolate_resource_environment(self)
        self.tmp = tempfile.TemporaryDirectory(prefix="build-slot-test.")
        self.root = Path(self.tmp.name)
        self.pool = self.root / "locks"
        launcher_directories(self.pool)
        self.state = self.root / "host.json"
        self.host()
        self.env = dict(os.environ, BUILD_SLOT_DIR=str(self.pool), BUILD_SLOTS="3",
                        BUILD_SLOT_HELD="0", BUILD_SLOT_MEM_GB="8")
        for key in ("CARGO_BUILD_JOBS", "TARGO_PLANNED_JOBS", "TARGO_CALLER_JOBS"):
            self.env.pop(key, None)
        # This fixture owns a private pool; resource routing has separate tests.
        for key in ("ATERM_CHILD", "ATERM_PARENT_SESSION_ID", "ATERM_SESSION_ID", "ATERM_EDGE_TOKENS"):
            self.env.pop(key, None)
        self.processes = []
        self.logs = []

    def tearDown(self):
        # Only these owned processes, each with one bounded wait after TERM.
        for proc in self.processes:
            if proc.poll() is None:
                proc.terminate()
                try:
                    proc.wait(timeout=3)
                except subprocess.TimeoutExpired:
                    proc.kill()
                    proc.wait(timeout=3)
        for log in self.logs:
            log.close()
        self.tmp.cleanup()

    def host(self, memory=100, load=0, builds=None, cpus=32):
        pending = self.state.with_suffix(".next")
        pending.write_text(json.dumps({"memory": memory, "load": load, "builds": [] if builds is None else builds, "cpus": cpus}))
        pending.replace(self.state)

    def spawn(self, cmd, env=None):
        log = (self.root / f"process-{len(self.processes)}.log").open("w+")
        proc = subprocess.Popen(cmd, cwd=self.root, env=env or self.env, stdout=log, stderr=log)
        self.processes.append(proc)
        self.logs.append(log)
        return proc

    def gate(self, name, *options, hold=False, env=None, worktree=False):
        marker = self.root / name
        cmd = [sys.executable, "-c", EXCLUSIVE_LAUNCHER, str(EXCLUSIVE_GATE), str(self.state),
               *([] if worktree else ["--no-worktree-lock"]), *options,
               "--", sys.executable, "-c", EXCLUSIVE_CHILD, str(marker)]
        if hold:
            cmd.append("hold")
        return self.spawn(cmd, env), marker

    def until(self, predicate, timeout=3):
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            if predicate():
                return
            time.sleep(0.01)
        self.fail("bounded condition timed out: " + "\n".join(self.output(p) for p in self.processes))

    def output(self, proc):
        log = self.logs[self.processes.index(proc)]
        log.flush()
        return Path(log.name).read_text()

    def held(self, slot):
        fd = os.open(self.pool / f"slot-{slot}", os.O_RDWR | os.O_CREAT, 0o644)
        try:
            try:
                fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
                return False
            except BlockingIOError:
                return True
        finally:
            os.close(fd)

    def test_exclusive_drains_legacy_and_excludes_legacy_and_new_jobs(self):
        legacy_marker = self.root / "legacy-start"
        legacy = self.spawn([sys.executable, "-c", EXCLUSIVE_LEGACY, str(self.pool), "3", str(legacy_marker)])
        self.until(legacy_marker.exists)
        exclusive, marker = self.gate("exclusive", "--exclusive", "--wait-timeout", "3", hold=True)
        self.until(lambda: "draining legacy" in self.output(exclusive))
        self.assertFalse(marker.exists())
        legacy.terminate()
        legacy.wait(timeout=3)
        self.until(marker.exists)
        self.assertTrue(all(self.held(i) for i in range(3)))
        old_marker = self.root / "old-waiter"
        old = self.spawn([sys.executable, "-c", EXCLUSIVE_LEGACY, str(self.pool), "3", str(old_marker)])
        new, new_marker = self.gate("new-waiter")
        self.until(lambda: "exclusive reservation owns admission" in self.output(new))
        time.sleep(0.08)
        self.assertFalse(old_marker.exists())
        self.assertFalse(new_marker.exists())
        exclusive.terminate()
        self.until(lambda: marker.with_suffix(".term").exists())
        self.assertTrue(all(self.held(i) for i in range(3)), "retain reservation while child handles TERM")
        self.assertEqual(exclusive.wait(timeout=3), 143)
        self.until(old_marker.exists)
        self.until(new_marker.exists)
        self.assertEqual(new.wait(timeout=3), 0)
        old.terminate()
        old.wait(timeout=3)
        self.assertFalse(any(self.held(i) for i in range(3)))

    def test_historic_larger_pool_is_reserved(self):
        fd = os.open(self.pool / "slot-7", os.O_RDWR | os.O_CREAT, 0o644)
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
            proc, marker = self.gate("historic", "--exclusive", "--wait-timeout", "3", hold=True)
            self.until(lambda: "draining legacy" in self.output(proc))
            self.assertFalse(marker.exists())
        finally:
            os.close(fd)
        self.until(marker.exists)
        self.assertTrue(self.held(7))

    def test_second_exclusive_times_out_without_launching_or_releasing_first(self):
        first, marker = self.gate("first-exclusive", "--exclusive", hold=True)
        self.until(marker.exists)
        second, second_marker = self.gate("second-exclusive", "--exclusive", "--wait-timeout", "0.3")
        self.until(lambda: "exclusive reservation owns admission" in self.output(second))
        self.assertEqual(second.wait(timeout=3), 2)
        self.assertFalse(second_marker.exists())
        self.assertTrue(all(self.held(i) for i in range(3)))
        first.terminate()
        self.assertEqual(first.wait(timeout=3), 143)
        self.assertFalse(any(self.held(i) for i in range(3)))

    def test_cancel_during_drain_releases_partial_and_admission_locks(self):
        fd = os.open(self.pool / "slot-1", os.O_RDWR | os.O_CREAT, 0o644)
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
            proc, marker = self.gate("cancel", "--exclusive")
            self.until(lambda: "draining legacy" in self.output(proc))
            # Current admission acquires all slots atomically; a failed attempt
            # releases its partial set. The exclusive admission barrier itself
            # must remain held while the legacy slot drains.
            admission = os.open(self.pool / "admission.lock", os.O_RDWR)
            try:
                with self.assertRaises(BlockingIOError):
                    fcntl.flock(admission, fcntl.LOCK_EX | fcntl.LOCK_NB)
            finally:
                os.close(admission)
            self.assertTrue(self.held(1), "the legacy holder remains alive")
            proc.terminate()
            self.assertEqual(proc.wait(timeout=3), -signal.SIGTERM)
            self.assertFalse(marker.exists())
            self.assertFalse(self.held(0))
            self.assertTrue(self.held(1), "cancellation must not release a legacy owner's slot")
            for slot in self.pool.glob("slot-*"):
                number = int(slot.name.removeprefix("slot-"))
                if number != 1:
                    self.assertFalse(self.held(number), "no partial reservation survives cancellation")
            admission = os.open(self.pool / "admission.lock", os.O_RDWR)
            try:
                fcntl.flock(admission, fcntl.LOCK_EX | fcntl.LOCK_NB)
            finally:
                os.close(admission)
            normal, started = self.gate("after-cancel")
            self.until(started.exists)
            self.assertEqual(normal.wait(timeout=3), 0)
        finally:
            os.close(fd)

    def test_unknown_and_busy_host_never_launch_then_ready_launches(self):
        for i, host in enumerate((
                {"memory": None}, {"memory": 7.9}, {"load": -1}, {"load": 11.21},
                {"load": float("nan")}, {"builds": [[999, "rustc"]]}, {"memory": float("nan")})):
            with self.subTest(host=host):
                self.host(**host)
                proc, marker = self.gate(f"host-{i}", "--exclusive", "--wait-timeout", "3")
                self.until(lambda: "waiting:" in self.output(proc))
                time.sleep(0.15)
                self.assertFalse(marker.exists())
                self.host(load=11.2, memory=8)
                self.until(marker.exists)
                self.assertEqual(proc.wait(timeout=3), 0)
                self.assertIn("quiet for", self.output(proc))

    def test_unmeasurable_process_scan_times_out_without_launch(self):
        self.state.write_text('{"memory":100,"load":0,"builds":null,"cpus":32}')
        proc, marker = self.gate("unknown-builds", "--exclusive", "--wait-timeout", "0.3")
        self.assertEqual(proc.wait(timeout=3), 2)
        self.assertFalse(marker.exists())
        self.assertIn("timed out", self.output(proc))
        self.assertFalse(any(self.held(i) for i in range(3)))

    def test_busy_sample_resets_quiet_interval(self):
        proc, marker = self.gate("reset", "--exclusive", "--wait-timeout", "3")
        self.until(lambda: "waiting for host readiness" in self.output(proc))
        time.sleep(0.05)
        self.host(load=100)
        self.until(lambda: "load1 100" in self.output(proc))
        self.host()
        time.sleep(0.08)
        self.assertFalse(marker.exists())
        self.until(marker.exists)
        self.assertEqual(proc.wait(timeout=3), 0)

    def test_timeout_and_cancel_while_host_busy_release_every_slot(self):
        self.host(load=100)
        for cancel in (False, True):
            with self.subTest(cancel=cancel):
                proc, marker = self.gate(f"busy-{cancel}", "--exclusive", "--wait-timeout", "0.3")
                self.until(lambda: "load1 100" in self.output(proc))
                self.assertTrue(all(self.held(i) for i in range(3)))
                if cancel:
                    proc.terminate()
                self.assertEqual(proc.wait(timeout=3), -signal.SIGTERM if cancel else 2)
                self.assertFalse(marker.exists())
                self.assertFalse(any(self.held(i) for i in range(3)))

    def test_default_memory_wait_and_per_worktree_serialization_remain(self):
        subprocess.run(["git", "init", "--quiet", str(self.root)], check=True, capture_output=True)
        self.host(memory=1)
        first, marker = self.gate("worktree-first", hold=True, worktree=True)
        self.until(lambda: "GiB needed" in self.output(first))
        self.assertFalse(marker.exists())
        self.host()
        self.until(marker.exists)
        second, second_marker = self.gate("worktree-second", worktree=True)
        self.until(lambda: "another build-slot job runs in this worktree" in self.output(second))
        self.assertFalse(second_marker.exists())
        first.terminate()
        self.assertEqual(first.wait(timeout=3), 143)
        self.until(second_marker.exists)
        self.assertEqual(second.wait(timeout=3), 0)

    def test_nested_cpu_request_shrinks_actual_child_budget(self):
        environment = dict(self.env, BUILD_SLOT_HELD="1", CARGO_BUILD_JOBS="6")
        process, marker = self.gate("nested-cpu-shrink", "--cpus", "3", env=environment)
        self.assertEqual(process.wait(timeout=3), 0, self.output(process))
        self.assertEqual(json.loads(marker.read_text())["CARGO_BUILD_JOBS"], "3")
        self.assertFalse(any(self.held(i) for i in range(5)))
        process, marker = self.gate("nested-cpu-grow", "--cpus", "7", env=environment)
        self.assertEqual(process.wait(timeout=3), 2, self.output(process))
        self.assertFalse(marker.exists())

    def test_weighted_waiter_releases_physical_admission_without_yielding_queue_order(self):
        blocker = os.open(self.pool / "slot-0", os.O_RDWR | os.O_CREAT, 0o644)
        fcntl.flock(blocker, fcntl.LOCK_EX | fcntl.LOCK_NB)
        try:
            weighted, weighted_marker = self.gate("weighted-waiter", "--cpus", "32")
            self.until(lambda: "waiting for 5 of 5 slots" in self.output(weighted))
            self.assertFalse(weighted_marker.exists())
            # A CPU-only queue reservation must not retain the physical
            # admission lock while existing holders drain.
            admission = os.open(self.pool / "admission.lock", os.O_RDWR)
            try:
                fcntl.flock(admission, fcntl.LOCK_EX | fcntl.LOCK_NB)
                fcntl.flock(admission, fcntl.LOCK_UN)
            finally:
                os.close(admission)
            self.host(load=100)
            exclusive, marker = self.gate("weighted-reservation", "--exclusive", "--wait-timeout", "3")
            self.until(lambda: "older eligible admission waiter first" in self.output(exclusive))
            self.assertFalse(marker.exists())
            fcntl.flock(blocker, fcntl.LOCK_UN)
            self.until(weighted_marker.exists)
            self.assertEqual(weighted.wait(timeout=3), 0, self.output(weighted))
            self.until(lambda: "slots exclusively; waiting for host readiness" in self.output(exclusive))
            self.assertFalse(marker.exists())
            self.host()
            self.until(marker.exists)
            self.assertEqual(exclusive.wait(timeout=3), 0, self.output(exclusive))
        finally:
            os.close(blocker)

    def test_waiting_ordinary_does_not_block_exclusive_reservation(self):
        # The ordinary payload needs 8 GiB; this smaller exclusive fixture needs
        # 1 GiB. Keep load busy after reservation to expose the barrier ownership
        # without asking admission to ignore its initial memory precondition.
        self.host(memory=1, load=100)
        ordinary, ordinary_marker = self.gate("memory-waiter")
        self.until(lambda: "GiB needed" in self.output(ordinary))
        exclusive, marker = self.gate("reservation", "--exclusive", "--mem-gb", "1",
                                      "--wait-timeout", "0.3")
        self.until(lambda: "slots exclusively; waiting for host readiness" in self.output(exclusive))
        for slot in self.pool.glob("slot-*"):
            self.assertTrue(self.held(int(slot.name.removeprefix("slot-"))))
        self.assertFalse(marker.exists())
        self.assertFalse(ordinary_marker.exists())
        self.assertEqual(exclusive.wait(timeout=3), 2)

    def test_actual_cli_times_out_before_launch_with_unmodified_probes(self):
        marker = self.root / "real-cli"
        # Real CLI/host probes, with only the account-home provider isolated so
        # the private pool never reads or prunes the host's adoption registry.
        account = """import os, pwd, runpy, sys
from types import SimpleNamespace
fixture_home, script = sys.argv[1:3]
pwd.getpwuid = lambda uid: SimpleNamespace(pw_dir=fixture_home)
sys.argv = [script, *sys.argv[3:]]
runpy.run_path(script, run_name='__main__')
"""
        proc = self.spawn([sys.executable, "-c", account, str(self.root), str(EXCLUSIVE_GATE),
                           "--exclusive", "--no-worktree-lock", "--wait-timeout", "0.15",
                           "--", sys.executable, "-c", EXCLUSIVE_CHILD, str(marker)])
        self.assertEqual(proc.wait(timeout=15), 2)
        self.assertFalse(marker.exists())
        self.assertIn("admission wait timed out", self.output(proc))
        self.assertFalse(any(self.held(i) for i in range(3)))

    def test_default_keeps_parallel_slots_cpu_share_and_unknown_memory_policy(self):
        self.host(memory=None, load=100, builds=[[999, "trustc"]])
        for raw, jobs in ((None, "10"), ("100", "10"), ("2", "2")):
            env = dict(self.env)
            if raw is not None:
                env["CARGO_BUILD_JOBS"] = raw
            proc, marker = self.gate(f"ordinary-{raw}", hold=True, env=env)
            self.until(marker.exists)
            self.assertEqual(json.loads(marker.read_text()), {"BUILD_SLOT_HELD": "1", "CARGO_BUILD_JOBS": jobs})
        self.assertTrue(all(self.held(i) for i in range(3)))
        fourth, marker = self.gate("fourth")
        self.until(lambda: "waiting for one of 3 slots" in self.output(fourth))
        self.assertFalse(marker.exists())
        self.processes[0].terminate()
        self.assertEqual(self.processes[0].wait(timeout=3), 143)
        self.until(marker.exists)
        self.assertEqual(fourth.wait(timeout=3), 0)

    def test_nested_default_executes_but_exclusive_and_bad_requests_refuse(self):
        for exclusive in (False, True):
            env = dict(self.env, BUILD_SLOT_HELD="1")
            env.pop("CARGO_BUILD_JOBS", None)
            options = ("--exclusive",) if exclusive else ()
            proc, marker = self.gate(f"nested-{exclusive}", *options, env=env)
            self.assertEqual(proc.wait(timeout=3), 2 if exclusive else 0)
            self.assertEqual(marker.exists(), not exclusive)
        for i, options in enumerate((("--exclusive", "--wait-timeout", "nan"),
                                     ("--exclusive", "--wait-timeout", "0"), ("--exclusive", "--wait-timeout"),
                                     ("--exclusive", "--mem-gb", "nan"))):
            proc, marker = self.gate(f"bad-{i}", *options)
            self.assertEqual(proc.wait(timeout=3), 2)
            self.assertFalse(marker.exists())
        self.assertFalse(list(self.pool.iterdir()), "refuse before any admission")

    def test_process_probe_exact_names_and_fail_closed_errors(self):
        loader = importlib.machinery.SourceFileLoader("slot_probe", str(EXCLUSIVE_GATE))
        spec = importlib.util.spec_from_loader(loader.name, loader)
        gate = importlib.util.module_from_spec(spec)
        loader.exec_module(gate)
        self.assertEqual((gate.QUIET_LOAD_FRACTION, gate.QUIET_SECONDS), (0.35, 10))
        out = "1 S /bin/python\n2 S /opt/trust/bin/trustc\n3 Z rustc\n4 T cargo\n5 S rustc-wrapper\n"
        with mock.patch.object(gate.subprocess, "run", return_value=mock.Mock(stdout=out)):
            self.assertEqual(gate.build_processes(), [(2, "/opt/trust/bin/trustc"), (4, "cargo")])
        for out in ("", "malformed\n"):
            with mock.patch.object(gate.subprocess, "run", return_value=mock.Mock(stdout=out)):
                self.assertIsNone(gate.build_processes())
        with mock.patch.object(gate.subprocess, "run", side_effect=subprocess.TimeoutExpired("ps", 10)):
            self.assertIsNone(gate.build_processes())

    def test_unknown_cpu_refuses_exclusive_but_default_retains_fallback(self):
        for cpus in (None, 0, -1):
            with self.subTest(cpus=cpus):
                self.host(cpus=cpus, load=0.5, memory=16)
                proc, marker = self.gate(f"cpu-{cpus}", "--exclusive", "--wait-timeout", "1")
                self.assertEqual(proc.wait(timeout=3), 2)
                self.assertFalse(marker.exists())
                self.assertIn("measured positive CPU count", self.output(proc))
                self.assertFalse(list(self.pool.iterdir()), "refuse before any lease")
        self.host(cpus=None, load=0.5, memory=16)
        proc, marker = self.gate("cpu-default")
        self.assertEqual(proc.wait(timeout=3), 0)
        self.assertEqual(json.loads(marker.read_text())["CARGO_BUILD_JOBS"], "1")

    def test_deadline_crossing_between_wait_samples_is_a_timeout(self):
        loader = importlib.machinery.SourceFileLoader("slot_deadline", str(EXCLUSIVE_GATE))
        spec = importlib.util.spec_from_loader(loader.name, loader)
        gate = importlib.util.module_from_spec(spec)
        loader.exec_module(gate)
        gate.ADOPTION_DIR = str(self.root / "adopted")
        opened = set()
        real_open = os.open
        real_close = os.close
        def track_open(*args, **kwargs):
            fd = real_open(*args, **kwargs)
            opened.add(fd)
            return fd
        def track_close(fd):
            real_close(fd)
            opened.discard(fd)
        try:
            with mock.patch.dict(os.environ, self.env), mock.patch.object(gate, "DIR", str(self.pool)), \
                    mock.patch.object(gate, "available_gib", return_value=16), \
                    mock.patch.object(gate, "load1", return_value=100), \
                    mock.patch.object(gate, "build_processes", return_value=[]), \
                    mock.patch.object(gate.os, "open", side_effect=track_open), \
                    mock.patch.object(gate.os, "close", side_effect=track_close), \
                    mock.patch.object(gate.time, "monotonic", side_effect=[0, .1, .2, .3, .999999, 1.000001]), \
                    mock.patch.object(gate.subprocess, "Popen") as child:
                with self.assertRaises(gate.AdmissionTimeout):
                    gate.main(["--exclusive", "--wait-timeout", "1", "--no-worktree-lock", "--", "never-start"])
                child.assert_not_called()
        finally:
            for fd in opened:
                real_close(fd)
        self.assertFalse(any(self.held(i) for i in range(3)))

if __name__ == "__main__":
    unittest.main()
