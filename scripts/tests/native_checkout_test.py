"""Native protocol unit controls and actual original-reader refusal boundaries.

Synthetic response bodies below are non-authoritative parser controls. Genuine
Targo/native-handler execution is exercised by native_checkout_inputs.rs.
"""
import base64
import contextlib
import hashlib
import hmac
import importlib.util
import json
import os
from pathlib import Path
import stat
import signal
import subprocess
import sys
import tempfile
import types
import time
import unittest
from unittest.mock import patch

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))
sys.path.insert(0, str(SCRIPTS / "lib"))
import native_checkout as native

spec = importlib.util.spec_from_file_location("native_checkout_gate_tests", SCRIPTS / "land_gate.py")
gate = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = gate
spec.loader.exec_module(gate)


class ProtocolTests(unittest.TestCase):
    def reader(self, mutate=lambda value: None):
        reader = native.Reader.__new__(native.Reader)
        reader.failed = False
        def sent(body):
            reader.body = body
        def answer():
            request = json.loads(reader.body)
            value = {"schema":native.SCHEMA, "nonce":request["nonce"],
                "request_sha256":hashlib.sha256(reader.body).hexdigest(),
                "checked":len(request["items"]), "bytes":4, "failures":[]}
            mutate(value)
            return value
        reader._send, reader._answer = sent, answer
        return reader

    def test_exact_response_is_bound_to_fresh_request_and_every_input(self):
        reader = self.reader()
        items = [("body", "100644", "ab" * 20, "./body")]
        self.assertEqual(reader.batch(Path("/source"), items), (4, []))
        first = json.loads(reader.body)["nonce"]
        reader.batch(Path("/source"), items)
        self.assertNotEqual(first, json.loads(reader.body)["nonce"])

    def test_wrong_binding_partial_bool_extra_fields_and_unordered_refusals_are_corrupt(self):
        def set_value(name, value):
            return lambda body: body.__setitem__(name, value)
        for change in (set_value("nonce", "00" * 32), set_value("request_sha256", "00" * 32),
                       set_value("checked", 0), set_value("checked", True), set_value("bytes", True),
                       set_value("extra", True), set_value("failures", [{"index":0,"kind":"inspect","digest":None,"stat":None}]*2)):
            with self.subTest(change=change), self.assertRaises(native.Corrupt):
                self.reader(change).batch(Path("/source"), [("body", "100644", "ab"*20, "./body")])

    def test_response_mac_duplicates_and_extra_frames_refuse(self):
        reader = native.Reader.__new__(native.Reader)
        reader.key = bytes(range(32))
        body = b'{"schema":"test"}'
        envelope = {"body":base64.b64encode(body).decode(), "mac":hmac.digest(reader.key,body,"sha256").hex()}
        reader.buffer = bytearray(json.dumps(envelope).encode()+b"\n")
        self.assertEqual(reader._answer(), {"schema":"test"})
        for encoded in (json.dumps(dict(envelope,mac="00"*32)).encode()+b"\n",
                        b'{"body":"e30=","body":"e30=","mac":"00"}\n',
                        json.dumps(envelope).encode()+b"\n{}\n"):
            reader.buffer = bytearray(encoded)
            with self.subTest(encoded=encoded), self.assertRaises(native.Corrupt):
                reader._answer()

    def test_malformed_ready_encoding_is_corruption_not_capability_loss(self):
        reader = native.Reader.__new__(native.Reader)
        reader.key = bytes(range(32))
        for line in (b"{", b'{"body":false,"mac":"x"}',
                     b'{"body":"!","mac":"x"}', b'{"body":"/w==","mac":"x"}'):
            reader.buffer = bytearray(line+b"\n")
            with self.subTest(line=line), self.assertRaises(native.Corrupt):
                reader._answer()
        body = b"false"
        reader.buffer = bytearray(native._json({"body":base64.b64encode(body).decode(),
            "mac":hmac.digest(reader.key,body,"sha256").hex()})+b"\n")
        with self.assertRaises(native.Corrupt):
            reader._answer()

    def test_ready_corruption_survives_a_cleanup_error(self):
        # Parser controls only: no substitute executable is ever started.
        with tempfile.TemporaryFile() as requests, tempfile.TemporaryFile() as answers:
            child = types.SimpleNamespace(stdin=requests,stdout=answers)
            program = types.SimpleNamespace(bookend=lambda:None,root=Path("/source"),
                executable=Path("/source/targo"),expected="00"*32)
            with patch.object(native.landing_targo,"exit_observation_available",return_value=True), \
                    patch.object(native.landing_targo,"resource_fds",return_value=()), \
                    patch.object(native.tempfile,"TemporaryFile",return_value=requests), \
                    patch.object(native.subprocess,"Popen",return_value=child), \
                    patch.object(native.Reader,"_send"), \
                    patch.object(native.Reader,"_answer",side_effect=native.Corrupt("malformed ready")), \
                    patch.object(native.Reader,"close",side_effect=RuntimeError("retirement failed")), \
                    self.assertRaisesRegex(native.Corrupt,"malformed ready.*retirement failed"):
                native.Reader(program,"00"*32,1,{},lambda _:object(),None,lambda:None)


class CleanupTests(unittest.TestCase):
    def test_native_cleanup_failure_still_retires_original_ready_workers(self):
        workers = gate._CheckoutWorkers(2)
        try:
            # The actual frozen-source workers say ready before injected
            # native cleanup fails. Their original PIDs must be reaped.
            workers._start()
            original = list(workers._procs)
            self.assertEqual(workers._ready,2)
            workers.native = types.SimpleNamespace(close=lambda:(_ for _ in ()).throw(
                RuntimeError("native retirement refused")))
            with self.assertRaisesRegex(RuntimeError,"native retirement refused"):
                workers.close()
            self.assertEqual(workers._procs,[])
            for child in original:
                self.assertEqual(child.poll(),0)
                with self.assertRaises(ChildProcessError):
                    os.waitpid(child.pid,os.WNOHANG)
        finally:
            workers.native = None
            workers.close()


class ManagedSelectionTests(unittest.TestCase):
    """Synthetic package/image rows are selector controls, never native credit.

    No fixture image below is executed. Genuine image/runtime custody is
    required separately by the actual all-static integration harness.
    """
    @contextlib.contextmanager
    def fixture(self, *, shadow=False, edit_after_verify=False):
        with tempfile.TemporaryDirectory(prefix="native-selector-") as temporary:
            home=Path(temporary).resolve()
            activation=home/".local/bin/atpkg"
            executable=home/"store/trust/7.noindex/bin/targo"
            for path in (activation,executable):
                path.parent.mkdir(parents=True,exist_ok=True)
                path.write_bytes(b"\xcf\xfa\xed\xfe"+b"synthetic selector DATA, never executed")
                path.chmod(0o755)
            root=executable.parent.parent
            (root.parent/"7").symlink_to(root.name,target_is_directory=True)
            row={"schema":1,"tool":"targo","status":"ready","managed":True,"package":"trust",
                "build":7,"shim_env":{},"store_root":str(root),"physical_root":str(root),
                "executable":str(root.parent/"7/bin/targo"),"physical_executable":str(executable),
                "provenance":{"index_source":"alabsystems/aterm","index_build":1,"tree_root":"ab"*32}}
            calls=[]
            def which(tool,**_):
                self.assertEqual(tool,"atpkg","PATH's Targo dispatcher must not authenticate the reader")
                return str(home/"shadow-atpkg") if shadow else str(activation)
            def query(argv,**_):
                calls.append(argv)
                self.assertEqual(argv[0],str(activation))
                args=argv[1:]
                if args==["which","--json","targo"]:
                    out=json.dumps(row)
                elif args==["verify","trust"]:
                    out="atpkg: trust build 7 OK (matches signed tree_root)"
                    if edit_after_verify:
                        executable.write_bytes(executable.read_bytes()+b"changed after verification")
                elif args==["tree-root",str(root)]:
                    out="ab"*32
                else:
                    self.fail(f"unexpected verifier query {args}")
                return subprocess.CompletedProcess(argv,0,out,"")
            with patch.object(native.Path,"home",return_value=home), \
                    patch.object(native.shutil,"which",side_effect=which), \
                    patch.object(native.subprocess,"run",side_effect=query), \
                    patch.object(native.landing_targo,"resource_fds",return_value=()):
                yield executable,calls

    def test_fixed_managed_image_does_not_require_a_direct_store_path_on_path(self):
        with self.fixture() as (executable,calls):
            program=native.managed_program({"PATH":"native-dispatcher-profile"})
            try:
                self.assertEqual(program.executable,executable)
                self.assertEqual(len(calls),4)
            finally:
                program.close()

    def test_verifier_shadow_and_image_edit_during_verification_refuse(self):
        for options in ({"shadow":True},{"edit_after_verify":True}):
            with self.subTest(options=options), self.fixture(**options) as (_executable,calls):
                with self.assertRaises((native.Unavailable,FileNotFoundError)):
                    native.managed_program({"PATH":"fixture-only"})
                if options.get("shadow"):
                    self.assertEqual(calls,[])


class PhysicalBoundaryTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="native-checkout-boundary-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.git("init", "-q", "-b", "main")
        self.git("config", "user.email", "fixture@example.invalid")
        self.git("config", "user.name", "Native checkout fixture")
        (self.root/"body").write_bytes(b"original\n")
        self.git("add", ".")
        self.git("commit", "-qm", "original")
        self.head = self.git("rev-parse", "HEAD")
        self.oid = self.git("rev-parse", "HEAD:body")
        self.item = ("body", "100644", self.oid, "./body")

    def git(self, *args):
        return subprocess.check_output(["git","-C",str(self.root),*args],text=True,stderr=subprocess.DEVNULL).strip()

    def captured(self):
        info = (self.root/"body").lstat()
        data = (self.root/"body").read_bytes()
        return {"index":0,"kind":"regular-bytes",
            "digest":hashlib.sha1(b"blob "+str(len(data)).encode()+b"\0"+data).hexdigest(),
            "stat":{"dev":info.st_dev,"ino":info.st_ino,"mode":info.st_mode,"bytes":info.st_size,
                "mtime_sec":info.st_mtime_ns//10**9,"mtime_nsec":info.st_mtime_ns%10**9,
                "ctime_sec":info.st_ctime_ns//10**9,"ctime_nsec":info.st_ctime_ns%10**9}}

    def problem(self, failure):
        return native.physical_problem(failure,self.item,self.root,self.head,gate.git_query_env(),gate.checkout_inputs)

    def test_definite_refusal_survives_repair_before_consumer_validation(self):
        (self.root/"body").chmod(0o755)
        observed = {"index":0,"kind":"executable-mode","digest":None,"stat":None}
        (self.root/"body").chmod(0o644)
        self.assertIsNone(gate.checkout_problem(self.head,self.root))
        self.assertIn("executable mode differs",self.problem(observed))

    def test_only_exact_committed_crlf_can_accept_the_captured_digest(self):
        (self.root/".gitattributes").write_text("body text eol=crlf\n")
        self.git("add", ".gitattributes")
        self.git("commit", "-qm", "committed CRLF policy")
        self.head = self.git("rev-parse", "HEAD")
        (self.root/"body").write_bytes(b"original\r\n")
        observed = self.captured()
        self.assertIsNone(self.problem(observed))
        (self.root/"body").write_bytes(b"original\n")
        self.assertIsNone(gate.checkout_problem(self.head,self.root))
        self.assertIn("changed", self.problem(observed))

    def test_raw_mismatch_is_not_replaced_by_a_later_clean_digest(self):
        (self.root/"body").write_bytes(b"modified\n")
        observed = self.captured()
        (self.root/"body").write_bytes(b"original\n")
        self.assertIsNone(gate.checkout_problem(self.head,self.root))
        self.assertIn("changed", self.problem(observed))

    def test_terminal_loss_rereads_the_entire_pass_and_never_respawns(self):
        workers = gate._CheckoutWorkers(1)
        reader = types.SimpleNamespace(program=types.SimpleNamespace(bookend=lambda:None),jobs=2,
                                       close=lambda:None)
        reader.batch = lambda *_: (_ for _ in ()).throw(native.Unavailable("original process ended"))
        # Gate captures its own exact module namespace; use that exception class.
        reader.batch = lambda *_: (_ for _ in ()).throw(gate.native_checkout.Unavailable("original process ended"))
        workers.native = reader
        reads = []
        original = gate._raw_tracked_problem
        def tracked(repo, revision, path, *rest):
            reads.append(path)
            return original(repo,revision,path,*rest)
        tally = gate.CheckoutTally()
        with patch.object(gate,"_raw_tracked_problem",side_effect=tracked):
            self.assertIsNone(gate.checkout_problem(self.head,self.root,workers=workers,tally=tally))
        self.assertEqual(reads,["body"])
        self.assertIsNone(workers.native)
        self.assertEqual(tally.backend,"python-fallback")
        self.assertIn("original process ended",tally.fallback)

    def test_corruption_refuses_without_accepting_a_python_repair(self):
        workers = gate._CheckoutWorkers(1)
        workers.native = types.SimpleNamespace(program=types.SimpleNamespace(bookend=lambda:None),jobs=2)
        workers.native.batch = lambda *_: (_ for _ in ()).throw(gate.native_checkout.Corrupt("wrong nonce"))
        with patch.object(gate,"_raw_tracked_problem",side_effect=AssertionError("corruption cannot grant a fallback PASS")):
            problem = gate.checkout_problem(self.head,self.root,workers=workers)
        self.assertIn("native checkout protocol refused",problem)

    def test_observed_gitlink_refusal_survives_repair_during_native_loss(self):
        source = self.root / "donor"
        source.mkdir()
        subprocess.run(["git","init","-q","-b","main",str(source)],check=True)
        for key,value in (("user.name","Child fixture"),("user.email","child@example.invalid")):
            subprocess.run(["git","-C",str(source),"config",key,value],check=True)
        (source/"child").write_text("original child\n")
        subprocess.run(["git","-C",str(source),"add","."],check=True)
        subprocess.run(["git","-C",str(source),"commit","-qm","original"],check=True)
        subprocess.run(["git","-C",str(self.root),"-c","protocol.file.allow=always",
                        "submodule","add","-q",str(source),"sub"],check=True)
        self.git("commit","-qm","pinned child")
        self.head = self.git("rev-parse","HEAD")
        child = self.root / "sub"
        expected = subprocess.check_output(["git","-C",str(child),"rev-parse","HEAD"],text=True).strip()
        subprocess.run(["git","-C",str(child),"config","user.name","Child fixture"],check=True)
        subprocess.run(["git","-C",str(child),"config","user.email","child@example.invalid"],check=True)
        (child/"child").write_text("wrong child\n")
        subprocess.run(["git","-C",str(child),"commit","-qam","moved"],check=True)
        workers = gate._CheckoutWorkers(1)
        reader = types.SimpleNamespace(program=types.SimpleNamespace(bookend=lambda:None),jobs=1,close=lambda:None)
        def lost(*_):
            subprocess.run(["git","-C",str(child),"reset","--hard","-q",expected],check=True)
            raise gate.native_checkout.Unavailable("native reader ended after gitlink observation")
        reader.batch = lost
        workers.native = reader
        problem = gate.checkout_problem(self.head,self.root,workers=workers)
        self.assertIn("tracked inputs changed at populated gitlink",problem)
        self.assertIsNone(workers.native)
        self.assertIsNone(gate.checkout_problem(self.head,self.root))


def run_native_controls(executable, world, builder):
    """Actual Targo integration entry, called by its native test harness.

    Direct OriginalProgram selection here qualifies this new engineering
    executable, never installs/adopts it or replaces managed product admission.
    No synthetic responder supplies a native physical verdict.
    """
    executable, world, builder = Path(executable).resolve(strict=True), Path(world).resolve(strict=True), Path(builder).resolve(strict=True)
    source = SCRIPTS.parent / native.NATIVE_SOURCE
    reader_hash = hashlib.sha256(source.read_bytes()).hexdigest()
    image_hash = hashlib.sha256(executable.read_bytes()).hexdigest()
    binding = {"executable":str(executable),"image_sha256":image_hash,"reader_sha256":reader_hash,
        "builder":str(builder),"builder_sha256":hashlib.sha256(builder.read_bytes()).hexdigest(),
        "scope":"actual unverified engineering reader, no managed adoption or source-to-binary proof"}
    (world/"inputs.json").write_text(json.dumps(binding,indent=2))
    version=subprocess.run([str(builder),"--unverified","--version","--verbose"],capture_output=True,timeout=120,
        pass_fds=gate.landing_targo.resource_fds(dict(os.environ)))
    (world/"builder-version.stdout").write_bytes(version.stdout)
    (world/"builder-version.stderr").write_bytes(version.stderr)
    if version.returncode or not version.stdout.startswith(b"targo "):
        raise RuntimeError("the actual selected builder did not report genuine Targo; no native controls ran")
    N = gate.native_checkout

    class RuntimeControls(unittest.TestCase):
        def setUp(self):
            self.case = world / self._testMethodName
            self.case.mkdir()
            self.root = self.case / "source"
            self.root.mkdir()
            self.git("init","-q","-b","main")
            self.git("config","user.name","Native reader actual fixture")
            self.git("config","user.email","actual@example.invalid")
            (self.root/"body").write_bytes(b"original\n")
            self.commit()

        def git(self,*args):
            return subprocess.check_output(["git","-C",str(self.root),*args],text=True).strip()

        def commit(self):
            self.git("add",".")
            self.git("commit","-qm","actual reader inputs")
            self.head = self.git("rev-parse","HEAD")
            self.item = ("body","100644",self.git("rev-parse","HEAD:body"),"./body")

        @contextlib.contextmanager
        def reader(self, label="reader"):
            with gate._cancellation_scope() as cancellation:
                # Custody contract: executable lives directly inside root/bin
                # (as production's store_root/bin/targo), so root is two up.
                program = N.OriginalProgram(executable.parent.parent,executable,image_hash)
                reader = N.Reader(program,reader_hash,2,dict(os.environ),gate._OwnedGroup,cancellation,gate._check_cancellation)
                try:
                    yield reader
                finally:
                    reader.close()
                    (self.case/(label+".stderr")).write_bytes(reader.stderr_tail)
                    (self.case/(label+".json")).write_text(json.dumps({"pid":reader.child.pid,
                        "status":reader.child.returncode,"runtime_identity_report":reader.runtime_identity},indent=2))

        def test_actual_batches_reread_bytes_and_keep_a_repaired_refusal(self):
            with self.reader() as reader:
                count,failures = reader.batch(self.root,[self.item])
                self.assertEqual((count,failures),(9,[]))
                (self.root/"body").write_bytes(b"modified\n")
                count,failures = reader.batch(self.root,[self.item])
                self.assertEqual(count,0)
                self.assertEqual(failures[0]["kind"],"regular-bytes")
                (self.root/"body").write_bytes(b"original\n")
                self.assertIsNotNone(N.physical_problem(failures[0],self.item,self.root,self.head,
                    gate.git_query_env(),gate.checkout_inputs))
                self.assertEqual(reader.batch(self.root,[self.item]),(9,[]))

        def test_actual_mode_link_and_committed_crlf_match_original_reader(self):
            (self.root/".gitattributes").write_text("body text eol=crlf\n")
            os.symlink("body",self.root/"link")
            self.commit()
            (self.root/"body").write_bytes(b"original\r\n")
            link=("link","120000",self.git("rev-parse","HEAD:link"),"./link")
            with self.reader() as reader:
                _count,failures=reader.batch(self.root,[self.item,link])
                self.assertEqual(len(failures),1)
                self.assertIsNone(N.physical_problem(failures[0],self.item,self.root,self.head,
                    gate.git_query_env(),gate.checkout_inputs))
                (self.root/"body").chmod(0o755)
                _count,failures=reader.batch(self.root,[self.item])
                self.assertEqual(failures[0]["kind"],"executable-mode")
                (self.root/"body").chmod(0o644)
                self.assertIn("executable mode differs",N.physical_problem(failures[0],self.item,
                    self.root,self.head,gate.git_query_env(),gate.checkout_inputs))

        def test_actual_terminal_loss_discards_an_already_read_batch(self):
            for index in range(N.MAX_ITEMS+3):
                (self.root/f"f{index:05}").write_bytes(b"file\n")
            self.commit()
            with self.reader() as reader:
                original=reader.batch
                calls=[]
                def loss(repo,items):
                    calls.append(len(items))
                    if len(calls)==2:
                        reader.close()  # original process EOF, owned drain and positive reap
                        (self.root/"body").write_bytes(b"modified\n")
                        raise N.Unavailable("actual original reader ended between batches")
                    return original(repo,items)
                reader.batch=loss
                workers=gate._CheckoutWorkers(1)
                workers.native=reader
                tally=gate.CheckoutTally()
                problem=gate.checkout_problem(self.head,self.root,workers=workers,tally=tally)
                self.assertEqual(len(calls),2)
                self.assertIn("./body",problem)
                self.assertEqual(tally.backend,"python-fallback")
                self.assertIsNone(workers.native)
                self.assertIsNotNone(reader.child.poll())

        def test_actual_native_and_python_complete_pass_agree(self):
            (self.root/"extra").write_bytes(b"more actual bytes\n")
            self.commit()
            with self.reader() as reader:
                workers=gate._CheckoutWorkers(1)
                workers.native=reader
                for changed in (False,True):
                    if changed:
                        (self.root/"body").write_bytes(b"modified\n")
                    actual=gate.checkout_problem(self.head,self.root,workers=workers)
                    original=gate.checkout_problem(self.head,self.root,workers=gate._CheckoutWorkers(1))
                    self.assertEqual(bool(actual),bool(original))
                    if changed:
                        self.assertIn("./body",actual)
                        self.assertIn("./body",original)

        def test_same_reported_source_never_allows_an_original_image_swap(self):
            # These native malicious-claim DATA fixtures are never compilers,
            # native readers, managed packages or accepted physical verdicts.
            claim=self.case/"claims"
            (claim/"src").mkdir(parents=True)
            (claim/"Cargo.toml").write_text('[package]\nname="reader-claim"\nversion="0.0.0"\nedition="2021"\n[workspace]\n[[bin]]\nname="claim-a"\npath="src/a.rs"\n[[bin]]\nname="claim-b"\npath="src/b.rs"\n')
            (claim/"Cargo.lock").write_text('version = 4\n[[package]]\nname = "reader-claim"\nversion = "0.0.0"\n')
            report=json.dumps({"schema":N.SCHEMA,"reader":reader_hash},separators=(",",":"))
            for variant in ("a","b"):
                (claim/f"src/{variant}.rs").write_text('fn main(){std::hint::black_box("'+variant+'");println!("{}",r#"'+report+'"#);}\n')
            environment=dict(os.environ,CARGO_HOME=str(self.case/"home"),CARGO_TARGET_DIR=str(self.case/"claim-target"),CARGO_INCREMENTAL="0")
            argv=[str(builder),"--unverified","build","--locked","--offline","--manifest-path",str(claim/"Cargo.toml"),
                "--config",'build.build-dir="'+str(self.case/"claim-target")+'"',"--config","profile.dev.debug=0","--config","profile.dev.incremental=false"]
            (self.case/"claim-build.json").write_text(json.dumps(argv))
            with gate._cancellation_scope() as cancellation, \
                    (self.case/"claim-build.stdout").open("wb") as stdout, \
                    (self.case/"claim-build.stderr").open("wb") as stderr:
                child=subprocess.Popen(argv,cwd=claim,env=environment,stdout=stdout,stderr=stderr,
                    start_new_session=True,pass_fds=gate.landing_targo.resource_fds(environment))
                owned=gate._OwnedGroup(child)
                stop=signal.SIGTERM
                try:
                    deadline=time.monotonic()+120
                    while not owned.exited():
                        cancellation.check()
                        if time.monotonic()>=deadline:
                            raise TimeoutError("owned malicious-claim fixture compilation timed out")
                        time.sleep(.02)
                    stop=None
                finally:
                    owned.retire(cancellation,stop_signal=stop)
            self.assertEqual(child.returncode,0,(self.case/"claim-build.stderr").read_text(errors="replace"))
            first=self.case/"claim-target/debug/claim-a"
            other=self.case/"claim-target/debug/claim-b"
            for path in (first,other):
                self.assertEqual(json.loads(subprocess.check_output([str(path)])),json.loads(report))
            self.assertNotEqual(first.read_bytes(),other.read_bytes())
            program=N.OriginalProgram(first.parent,first,hashlib.sha256(first.read_bytes()).hexdigest())
            try:
                first.rename(first.with_suffix(".original"))
                other.rename(first)
                with self.assertRaises(N.Unavailable):
                    program.bookend()
            finally:
                program.close()
            # A same-inode edit also refuses despite restoring its mtime. No
            # fixture here is an accepted reader or a held qualification tool.
            program=N.OriginalProgram(first.parent,first,hashlib.sha256(first.read_bytes()).hexdigest())
            try:
                before=first.stat()
                with first.open("r+b") as changed:
                    byte=changed.read(1)
                    changed.seek(0)
                    changed.write(bytes([byte[0]^1]))
                os.utime(first,ns=(before.st_atime_ns,before.st_mtime_ns))
                self.assertEqual(first.stat().st_ino,before.st_ino)
                with self.assertRaises(N.Unavailable):
                    program.bookend()
            finally:
                program.close()

    suite=unittest.defaultTestLoader.loadTestsFromTestCase(RuntimeControls)
    result=unittest.TextTestRunner(verbosity=2).run(suite)
    after=hashlib.sha256(executable.read_bytes()).hexdigest()
    (world/"result.json").write_text(json.dumps({"tests":result.testsRun,"failures":len(result.failures),
        "errors":len(result.errors),"skipped":len(result.skipped),"image_sha256_after":after},indent=2))
    return int(not result.wasSuccessful() or result.testsRun!=5 or bool(result.skipped) or after!=image_hash)


if __name__ == "__main__":
    if len(sys.argv)==5 and sys.argv[1]=="--native":
        raise SystemExit(run_native_controls(*sys.argv[2:]))
    unittest.main()
