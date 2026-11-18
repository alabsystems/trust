#!/usr/bin/env python3
"""Exercise x.py with the real native manager and a Python bootstrap stub."""

from __future__ import annotations

import json
import os
import shlex
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
MODES = ("success", "error", "exit", "term", "hup", "int", "reenter")
# Where scripts/build-tree-manager.sh puts a fresh tree's own Bootstrap, and the
# third native frontend x.py probes (FRESH-TREE-LOCK-FRONTEND-1).
CONSTRUCTED = "build-tree-manager.noindex/debug/bootstrap"
# The answer of the 2026-11-07 Stage0 seed's Targo: an older manager protocol.
V1_TARGO = '''#!/bin/sh
if [ "$1 $2 $3 $4" = "trust repo lock --protocol" ]; then
  echo trust-build-tree-manager-v1
  exit 0
fi
echo "unexpected fixture targo call: $*" >&2
exit 2
'''
V1_BOOTSTRAP = "#!/bin/sh\necho trust-build-tree-manager-v1\n"
CONSTRUCTION_TARGO = r'''#!/bin/sh
if [ "$1 $2" = "--unverified --version" ]; then echo "targo 0.0.0-fixture"; exit 0; fi
if [ "$1 $2 $3 $4" = "trust repo lock --protocol" ]; then echo trust-build-tree-manager-v1; exit 0; fi
mkdir -p @RECORD@
printf '%s\n' "$@" > @RECORD@/argv
for v in CARGO_TARGET_DIR RUSTC RUSTC_WRAPPER RUSTFLAGS CARGO_BUILD_TARGET CARGO_INCREMENTAL RUSTC_BOOTSTRAP; do
  eval "given=\${$v+set} value=\${$v-}"
  printf '%s=%s|%s\n' "$v" "$given" "$value" >> @RECORD@/env
done
out="$CARGO_TARGET_DIR/debug/bootstrap"
mkdir -p "$CARGO_TARGET_DIR/debug"
@PRODUCE@
'''
BOOTSTRAP = '''
import __main__
import json
import os
import signal
from pathlib import Path

def main():
    mode = os.environ["LOCK_TEST_MODE"]
    if mode == "reenter":
        __main__._trust_build_lock_acquire(os.getcwd(), ["test"])
    if mode == "hold":
        # A cold start's first write into the build tree, made under the lease.
        Path("build").mkdir(exist_ok=True)
        Path("build/writer-%d" % os.getpid()).write_text("written under the lease")
    Path("observed-%d.json" % os.getpid() if mode == "hold" else "observed.json").write_text(json.dumps({
        "token": os.environ["TRUST_BUILD_LOCK_TOKEN"],
        "pid": os.getpid(),
        "info": Path(".trust-build-lock/info").read_text(),
        "frontend": __main__._lock_frontend[0],
        "incremental": Path("crates/target.noindex/debug/incremental").exists(),
    }))
    if mode == "hold":
        import time
        until = time.monotonic() + 60
        while not Path("go").exists() and time.monotonic() < until:
            time.sleep(0.02)
    if mode == "error":
        raise RuntimeError("intentional bootstrap failure")
    if mode == "exit":
        raise SystemExit(7)
    if mode in ("term", "hup", "int"):
        os.kill(os.getpid(), getattr(signal, "SIG" + mode.upper()))
'''

PYTHON_PROBE = '''
import json
import os
import sys
from pathlib import Path

def main():
    Path("observed.json").write_text(json.dumps({
        "version": list(sys.version_info[:2]),
        "argv": sys.argv[1:],
        "flags": [sys.flags.isolated, sys.flags.no_site, sys.flags.ignore_environment,
                  sys.flags.no_user_site, sys.flags.optimize, sys.flags.dont_write_bytecode],
        "pid": os.getpid(),
        "info": Path(".trust-build-lock/info").read_text(),
        "reexec_guard": os.environ.get("TRUST_XPY_PYTHON_REEXEC"),
    }))
    import tomllib
    assert tomllib.loads("ready = true") == {"ready": True}
    Path("ready").write_text("yes")
'''


@unittest.skipUnless(os.name == "posix" and Path("/bin/sh").is_file(), "POSIX build lock")
class XpyBuildLockOwnershipTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="trust-xpy-lock-test-")
        self.addCleanup(temporary.cleanup)
        self.scratch = Path(temporary.name).resolve()
        self.env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
        for key in list(self.env):
            if key.startswith("TRUST_BUILD_LOCK_") or key in ("TRUST_REPO", "TRUST_SKIP_PREFLIGHT",
                                                              "TRUST_BUILD_TREE_MANAGER_TARGO"):
                self.env.pop(key)
        self.env["TRUST_BUILD_LOCK_WAIT"] = "0"
        selected = self.env.get("TRUST_BUILD_TREE_BOOTSTRAP")
        # This checkout's own Bootstrap: the normal one, else a fresh tree's
        # (scripts/build-tree-manager.sh), the same order x.py probes them in.
        normal = REPO_ROOT / "build/bootstrap/debug/bootstrap"
        self.native_bootstrap = (Path(selected) if selected else normal if normal.is_file()
                                 else REPO_ROOT / CONSTRUCTED).resolve()
        self.assertTrue(self.native_bootstrap.is_file(),
                        "requires actual current Bootstrap via TRUST_BUILD_TREE_BOOTSTRAP")
        protocol = subprocess.run(
            [str(self.native_bootstrap), "--trust-build-tree-lock", "--protocol"],
            capture_output=True, timeout=10,
        )
        self.assertEqual(protocol.returncode, 0, protocol.stderr)
        self.assertEqual(protocol.stdout, b"trust-build-tree-manager-v2\n")

    def fixture(self, label, native="build/bootstrap/debug/bootstrap"):
        root = self.scratch / label
        (root / "scripts").mkdir(parents=True)
        (root / "src/bootstrap").mkdir(parents=True)
        shutil.copyfile(REPO_ROOT / "x.py", root / "x.py")
        if native is not None:
            native = root / native
            native.parent.mkdir(parents=True)
            native.symlink_to(self.native_bootstrap)
        (root / "src/bootstrap/bootstrap.py").write_text(BOOTSTRAP)
        return root

    def v1_path(self, root):
        """A PATH whose only Targo answers the older manager protocol."""
        bindir = root.parent / (root.name + "-bin")
        bindir.mkdir()
        targo = bindir / "targo"
        targo.write_text(V1_TARGO)
        targo.chmod(0o755)
        return str(bindir) + ":/usr/bin:/bin:/usr/sbin:/sbin"

    @staticmethod
    def tree(root):
        """Every path under root with its type and bytes: a write shows up here."""
        state = {}
        for path in sorted(root.rglob("*")):
            if path.is_symlink():
                state[str(path)] = ("link", os.readlink(path))
            elif path.is_file():
                state[str(path)] = ("file", path.read_bytes())
            else:
                state[str(path)] = ("dir", None)
        return state

    def lock(self, root, *args):
        return subprocess.run(
            [str(self.native_bootstrap), "--trust-build-tree-lock", *args,
             "--repo-root", str(root)],
            cwd=root, env=dict(self.env, TRUST_REPO=str(root)),
            text=True, capture_output=True, timeout=15,
        )

    def hold(self, root):
        acquired = self.lock(root, "acquire", "--kind", "measurement", "--purpose",
                             "parent regression owner", "--pid", str(os.getpid()))
        self.assertEqual(acquired.returncode, 0, acquired.stderr)
        token = acquired.stdout.strip()
        self.assertTrue(token)
        self.addCleanup(self.lock, root, "release", token)
        return token, (root / ".trust-build-lock/info").read_bytes()

    def launch(self, root, mode, token=None, argv=None, path=None, wait=True):
        env = dict(self.env, TRUST_REPO=str(root), LOCK_TEST_MODE=mode)
        if token is not None:
            env["TRUST_BUILD_LOCK_TOKEN"] = token
        if path is not None:
            env["PATH"] = path
        command = [sys.executable, "-B", str(root / "x.py"), *(["test"] if argv is None else argv)]
        if not wait:
            return subprocess.Popen(command, cwd=root, env=env, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        return subprocess.run(command, cwd=root, env=env, text=True, capture_output=True, timeout=15)

    def assert_outcome(self, child, mode):
        expected = {"success": 0, "reenter": 0, "error": 1, "exit": 7,
                    "term": 143, "hup": 129}
        if mode == "int":
            self.assertIn(child.returncode, (130, -2), child.stderr)
        else:
            self.assertEqual(child.returncode, expected[mode], child.stderr)

    def test_borrowed_lock_survives_all_bootstrap_exits(self):
        for mode in MODES:
            with self.subTest(mode=mode):
                root = self.fixture(mode)
                token, original = self.hold(root)
                child = self.launch(root, mode, token)
                self.assert_outcome(child, mode)
                observed = json.loads((root / "observed.json").read_text())
                self.assertEqual(observed["token"], token)
                self.assertEqual((root / ".trust-build-lock/info").read_bytes(), original)

    def test_owned_lock_releases_all_bootstrap_exits(self):
        for mode in MODES:
            with self.subTest(mode=mode):
                root = self.fixture(mode)
                child = self.launch(root, mode)
                self.assert_outcome(child, mode)
                observed = json.loads((root / "observed.json").read_text())
                self.assertIn("pid=%s\n" % observed["pid"], observed["info"])
                self.assertFalse((root / ".trust-build-lock/info").exists())

    def test_fresh_acquisition_runs_real_native_reclaimer_without_pipe_leaks(self):
        root = self.fixture("native-reclaim")
        cache = root / "crates/target.noindex/debug/incremental"
        cache.mkdir(parents=True)
        (cache / "compiler-cache").write_bytes(b"cache" * 16384)
        # The protocol query is exact and intentionally takes no root argument.
        protocol = subprocess.run(
            [str(self.native_bootstrap), "--trust-build-tree-lock", "reclaim-incremental", "--protocol"],
            capture_output=True, timeout=10,
        )
        self.assertEqual(protocol.returncode, 0, protocol.stderr)
        self.assertEqual(protocol.stdout, b"trust-incremental-reclamation-v1\n")
        self.env["TRUST_INCREMENTAL_MAX_GIB"] = "0"
        self.env["TRUST_INCREMENTAL_MIN_FREE_GIB"] = "0"
        child = self.launch(root, "success")
        self.assert_outcome(child, "success")
        # The native owner reclaims inside acquisition, before it delivers the
        # token (98744ba225), and reports on the acquiring process's stderr,
        # which x.py inherits; the build starts with the cache already gone.
        # A detached helper holding x.py's output pipes would time out launch().
        observed = json.loads((root / "observed.json").read_text())
        self.assertFalse(observed["incremental"], "the build began before native reclamation")
        self.assertFalse(cache.exists(), child.stderr)
        self.assertIn("Reclaimed", child.stderr)
        self.assertFalse((root / ".trust-build-lock").exists())

    def test_default_build_still_takes_native_ownership(self):
        root = self.fixture("default-build")
        child = self.launch(root, "success", argv=[])
        self.assert_outcome(child, "success")
        observed = json.loads((root / "observed.json").read_text())
        self.assertIn("pid=%s\n" % observed["pid"], observed["info"])
        self.assertFalse((root / ".trust-build-lock").exists())

    def test_stale_inherited_token_still_releases_a_new_lock(self):
        root = self.fixture("stale")
        child = self.launch(root, "exit", "stale-token")
        self.assert_outcome(child, "exit")
        observed = json.loads((root / "observed.json").read_text())
        self.assertNotEqual(observed["token"], "stale-token")
        self.assertFalse((root / ".trust-build-lock/info").exists())

    def test_other_root_token_still_releases_a_new_lock(self):
        other = self.fixture("other")
        token, original = self.hold(other)
        root = self.fixture("current")
        child = self.launch(root, "success", token)
        self.assert_outcome(child, "success")
        self.assertFalse((root / ".trust-build-lock/info").exists())
        self.assertEqual((other / ".trust-build-lock/info").read_bytes(), original)

    def test_parent_lock_refuses_an_unrelated_child(self):
        root = self.fixture("unrelated")
        _, original = self.hold(root)
        child = self.launch(root, "success")
        self.assertEqual(child.returncode, 1, child.stderr)
        self.assertFalse((root / "observed.json").exists())
        self.assertEqual((root / ".trust-build-lock/info").read_bytes(), original)

    def test_parent_lock_refuses_a_forged_inherited_token(self):
        root = self.fixture("forged")
        _, original = self.hold(root)
        child = self.launch(root, "success", "forged-token")
        self.assertEqual(child.returncode, 1, child.stderr)
        self.assertFalse((root / "observed.json").exists())
        self.assertEqual((root / ".trust-build-lock/info").read_bytes(), original)

    # FRESH-TREE-LOCK-FRONTEND-1: a tree with no build/ yet, on a host whose
    # Targo predates manager v2 (here the Stage0 seed's v1 answer on PATH).

    def test_fresh_tree_takes_native_ownership_through_its_constructed_bootstrap(self):
        root = self.fixture("fresh", native=CONSTRUCTED)
        child = self.launch(root, "success", path=self.v1_path(root))
        self.assert_outcome(child, "success")
        observed = json.loads((root / "observed.json").read_text())
        self.assertEqual(observed["frontend"], [str(root / CONSTRUCTED), "--trust-build-tree-lock"])
        self.assertIn("pid=%s\n" % observed["pid"], observed["info"])
        self.assertFalse((root / ".trust-build-lock").exists())
        self.assertFalse((root / "build").exists(), "x.py itself wrote into build/")

    def test_no_v2_manager_refuses_before_any_write(self):
        cases = {
            "no-frontend": None,
            "v1-bootstrap": "build/bootstrap/debug/bootstrap",
            "v1-constructed": CONSTRUCTED,
        }
        for label, v1 in cases.items():
            with self.subTest(case=label):
                root = self.fixture("refused-" + label, native=None)
                if v1 is not None:
                    frontend = root / v1
                    frontend.parent.mkdir(parents=True)
                    frontend.write_text(V1_BOOTSTRAP)
                    frontend.chmod(0o755)
                path = self.v1_path(root)
                before = self.tree(root)
                child = self.launch(root, "success", path=path)
                self.assertEqual(child.returncode, 1, child.stderr)
                self.assertIn("native build-tree manager v2 is unavailable", child.stderr)
                self.assertIn("scripts/build-tree-manager.sh", child.stderr)
                self.assertIn("refusing unlocked build", child.stderr)
                self.assertEqual(self.tree(root), before)

    def test_two_cold_starts_on_one_fresh_tree_admit_one_writer(self):
        root = self.fixture("cold-race", native=CONSTRUCTED)
        path = self.v1_path(root)
        children = [self.launch(root, "hold", path=path, wait=False) for _ in range(2)]
        try:
            until = time.monotonic() + 30
            while all(child.poll() is None for child in children) and time.monotonic() < until:
                time.sleep(0.02)
            refused = [child for child in children if child.poll() is not None]
            self.assertEqual(len(refused), 1, "expected exactly one cold start to stop while the other holds")
            out, err = refused[0].communicate(timeout=15)
            self.assertEqual(refused[0].returncode, 1, out + err)
            self.assertIn("refusing to build while the build tree is held", err)
            (root / "go").write_text("release the holder")
            holder = next(child for child in children if child is not refused[0])
            out, err = holder.communicate(timeout=30)
            self.assertEqual(holder.returncode, 0, out + err)
        finally:
            for child in children:
                if child.poll() is None:
                    child.kill()
                    child.communicate()
        writers = sorted(p.name for p in (root / "build").iterdir())
        self.assertEqual(writers, ["writer-%d" % holder.pid])
        observed = json.loads((root / ("observed-%d.json" % holder.pid)).read_text())
        self.assertEqual(observed["frontend"], [str(root / CONSTRUCTED), "--trust-build-tree-lock"])
        self.assertFalse((root / ".trust-build-lock").exists())

    def construction_fixture(self, label, answer):
        """A tree holding the real construction script, and a Targo that records it."""
        root = self.fixture(label, native=None)
        shutil.copyfile(REPO_ROOT / "scripts/build-tree-manager.sh", root / "scripts/build-tree-manager.sh")
        (root / "src/bootstrap/Cargo.toml").write_text("")
        bindir = root.parent / (label + "-bin")
        bindir.mkdir()
        record = root.parent / (label + "-record")
        if answer == "v2":
            produce = "ln -s %s \"$out\"" % shlex.quote(str(self.native_bootstrap))
        else:
            produce = "printf '#!/bin/sh\\necho trust-build-tree-manager-v1\\n' > \"$out\"; chmod 755 \"$out\""
        # --unverified --version is the genuine-Targo probe. The build records its
        # argv and the variables it was given, then leaves a binary where Cargo
        # would: the real native Bootstrap, or one answering the v1 protocol.
        targo = bindir / "targo"
        targo.write_text(CONSTRUCTION_TARGO.replace("@RECORD@", shlex.quote(str(record)))
                         .replace("@PRODUCE@", produce))
        targo.chmod(0o755)
        return root, str(bindir) + ":/usr/bin:/bin:/usr/sbin:/sbin", record

    def construct(self, root, path, *args):
        return subprocess.run(
            ["/bin/bash", str(root / "scripts/build-tree-manager.sh"), *args], cwd=root,
            env=dict(self.env, PATH=path, RUSTC="/inherited/bootstrap-shim", RUSTC_WRAPPER="/inherited/wrapper",
                     RUSTFLAGS="-Cinherited", CARGO_BUILD_TARGET="inherited-triple",
                     CARGO_TARGET_DIR=str(root.parent / "inherited-target")),
            text=True, capture_output=True, timeout=30,
        )

    def test_construction_builds_the_frontend_x_py_names_and_nothing_under_build(self):
        root, path, record = self.construction_fixture("construct", "v2")
        built = self.construct(root, path)
        self.assertEqual(built.returncode, 0, built.stdout + built.stderr)
        self.assertEqual(built.stdout.strip().splitlines()[-1], str(root / CONSTRUCTED))
        self.assertEqual((record / "argv").read_text().splitlines(),
                         ["--unverified", "build", "--frozen", "--manifest-path",
                          str(root / "src/bootstrap/Cargo.toml"), "--bin", "bootstrap"])
        selected = dict(line.split("=", 1) for line in (record / "env").read_text().splitlines())
        self.assertEqual(selected, {
            "CARGO_TARGET_DIR": "set|%s" % (root / "build-tree-manager.noindex"),
            "RUSTC": "|", "RUSTC_WRAPPER": "|", "RUSTFLAGS": "|", "CARGO_BUILD_TARGET": "|",
            "CARGO_INCREMENTAL": "set|0", "RUSTC_BOOTSTRAP": "set|1",
        })
        self.assertFalse((root / "build").exists())
        self.assertFalse((root.parent / "inherited-target").exists())
        child = self.launch(root, "success", path=path)
        self.assert_outcome(child, "success")
        observed = json.loads((root / "observed.json").read_text())
        self.assertEqual(observed["frontend"], [str(root / CONSTRUCTED), "--trust-build-tree-lock"])
        self.assertFalse((root / ".trust-build-lock").exists())

    def test_construction_refuses_a_stock_cargo_and_a_v1_result(self):
        root, path, record = self.construction_fixture("construct-stock", "v2")
        stock = Path(path.split(":", 1)[0]) / "targo"
        stock.write_text("#!/bin/sh\necho \"error: unexpected argument '--unverified' found\" >&2\nexit 1\n")
        refused = self.construct(root, path)
        self.assertEqual(refused.returncode, 2, refused.stdout + refused.stderr)
        self.assertIn("is not a Trust Targo", refused.stderr)
        self.assertFalse(record.exists())
        self.assertFalse((root / "build-tree-manager.noindex").exists())

        root, path, record = self.construction_fixture("construct-v1", "v1")
        refused = self.construct(root, path)
        self.assertEqual(refused.returncode, 1, refused.stdout + refused.stderr)
        self.assertIn("does not answer trust-build-tree-manager-v2", refused.stderr)
        # x.py refuses that result too, before any write.
        before = self.tree(root)
        child = self.launch(root, "success", path=path)
        self.assertEqual(child.returncode, 1, child.stderr)
        self.assertIn("native build-tree manager v2 is unavailable", child.stderr)
        self.assertEqual(self.tree(root), before)

    def test_construction_fails_as_cargo_does_when_its_offline_home_lacks_a_locked_crate(self):
        # 2026-11-16: the daily runner ran this step with a Cargo home that held Bootstrap's
        # archives and too few registry index entries, and --frozen fetches nothing. The
        # script adds nothing to Cargo's refusal: its exit, no manager path, nothing built.
        root, path, record = self.construction_fixture("construct-offline", "v2")
        offline = Path(path.split(":", 1)[0]) / "targo"
        offline.write_text('#!/bin/sh\n'
                           'if [ "$1 $2" = "--unverified --version" ]; then echo "targo 0.0.0-fixture"; exit 0; fi\n'
                           'echo "error: no matching package named \\`chrono\\` found" >&2\nexit 101\n')
        refused = self.construct(root, path)
        self.assertEqual(refused.returncode, 101, refused.stdout + refused.stderr)
        self.assertIn("no matching package named `chrono` found", refused.stderr)
        self.assertEqual(refused.stdout, "")
        self.assertFalse((root / CONSTRUCTED).exists())

    def test_construction_puts_each_seed_dylib_path_first_for_the_targo_it_runs(self):
        # macOS drops dyld's variables at the launch of a system-protected program, /bin/sh
        # included, so the Targo that reports what it was given is this interpreter, through
        # a link beside the fixture.
        root, path, record = self.construction_fixture("construct-dylibs", "v2")
        if any(character.isspace() for character in str(root)):
            self.skipTest("a script's interpreter line cannot name a path with white space")
        python = root.parent / "construct-dylibs-python"
        python.symlink_to(Path(sys.executable).resolve())
        probe = subprocess.run(["/usr/bin/env", "DYLD_LIBRARY_PATH=/probe", str(python), "-I", "-c",
                                "import os; print(os.environ.get('DYLD_LIBRARY_PATH'))"],
                               env=self.env, capture_output=True, text=True, timeout=30)
        if probe.stdout.strip() != "/probe":
            self.skipTest("this interpreter is launched without dyld's variables, so it cannot report them")
        targo = Path(path.split(":", 1)[0]) / "targo"
        targo.write_text(f"#!{python} -I\n" + f"""import os, sys
if sys.argv[1:] == ["--unverified", "--version"]:
    print("targo 0.0.0-fixture")
    raise SystemExit(0)
os.makedirs({str(record)!r}, exist_ok=True)
open({str(record / "dyld")!r}, "w").write(os.environ.get("DYLD_LIBRARY_PATH", "<unset>"))
out = os.path.join(os.environ["CARGO_TARGET_DIR"], "debug", "bootstrap")
os.makedirs(os.path.dirname(out), exist_ok=True)
os.symlink({str(self.native_bootstrap)!r}, out)
""")
        first, second = root.parent / "dylibs one", root.parent / "dylibs-two"
        first.mkdir()
        second.mkdir()
        built = self.construct(root, path, "--targo", str(targo),
                               "--seed-dylib-path", str(first), "--seed-dylib-path", str(second))
        self.assertEqual(built.returncode, 0, built.stdout + built.stderr)
        self.assertEqual((record / "dyld").read_text(), f"{first}:{second}")
        # Without a provider the variable is not set at all, not set empty.
        (root / CONSTRUCTED).unlink()
        plain = self.construct(root, path, "--targo", str(targo))
        self.assertEqual(plain.returncode, 0, plain.stdout + plain.stderr)
        self.assertEqual((record / "dyld").read_text(), "<unset>")
        colon = root.parent / "dylibs:three"  # dyld would read it as two directories
        colon.mkdir()
        for words, why in ((["--seed-dylib-path", "relative"], "takes an absolute directory"),
                           (["--seed-dylib-path", str(root.parent / "absent")], "is not a directory"),
                           (["--seed-dylib-path", str(colon)], "cannot hold a colon"),
                           (["--seed-dylib-path"], "needs a directory")):
            with self.subTest(words=words):
                refused = self.construct(root, path, *words)
                self.assertEqual(refused.returncode, 2, refused.stdout + refused.stderr)
                self.assertIn(why, refused.stderr)

    def python_pair(self):
        old = new = None
        for name in (sys.executable, "/usr/bin/python3", "python3.9", "python3.10",
                     "python3.14", "python3.13", "python3.12", "python3.11", "python3"):
            path = shutil.which(name)
            if path is None:
                continue
            probe = subprocess.run([path, "-I", "-S", "-c", "import sys; print(sys.version_info[:2])"],
                                   capture_output=True, text=True, timeout=10)
            if probe.returncode:
                continue
            if probe.stdout.strip() in ("(3, 9)", "(3, 10)"):
                old = old or path
            elif subprocess.run([path, "-I", "-S", "-c", "import tomllib"],
                                capture_output=True, timeout=10).returncode == 0:
                new = new or path
        if old is None or new is None:
            self.skipTest("requires actual Python 3.9/3.10 and Python 3.11+ with tomllib")
        return old, new

    def python_fixture(self, label):
        root = self.fixture(label)
        (root / "src/bootstrap/bootstrap.py").write_text(PYTHON_PROBE)
        bindir = root / "bin"
        bindir.mkdir()
        return root, bindir

    def test_old_python_reexecs_before_bootstrap_with_arguments_and_flags(self):
        old, new = self.python_pair()
        cases = (([], [0, 0, 0, 0, 0, 1]),
                 (["-I", "-S", "-B"], [1, 1, 1, 1, 0, 1]),
                 (["-OO", "-B", "-E", "-s"], [0, 0, 1, 1, 2, 1]))
        for index, (flags, expected) in enumerate(cases):
            with self.subTest(flags=flags):
                root, bindir = self.python_fixture("python-path-%s" % index)
                incompatible = bindir / "python3.14"
                incompatible.write_text("#!/bin/sh\nexit 79\n")
                incompatible.chmod(0o755)
                compatible = bindir / "python3.12"
                compatible.write_text("#!/bin/sh\nexec %s \"$@\"\n" % shlex.quote(new))
                compatible.chmod(0o755)
                argv = ["test", "--set", "build.description=path with spaces"]
                env = dict(self.env, TRUST_REPO=str(root), PATH=str(bindir) + ":/usr/bin:/bin:/usr/sbin:/sbin")
                child = subprocess.run([old, *flags, str(root / "x.py"), *argv], cwd=root,
                                       env=env, capture_output=True, text=True, timeout=30)
                self.assertEqual(child.returncode, 0, child.stdout + child.stderr)
                observed = json.loads((root / "observed.json").read_text())
                self.assertGreaterEqual(tuple(observed["version"]), (3, 11))
                self.assertEqual(observed["argv"], argv)
                self.assertEqual(observed["flags"], expected)
                self.assertIsNone(observed["reexec_guard"])
                self.assertIn("pid=%s\n" % observed["pid"], observed["info"])
                self.assertEqual((root / "ready").read_text(), "yes")
                self.assertFalse((root / ".trust-build-lock").exists())

    def test_no_capable_python_refuses_before_bootstrap_or_lock(self):
        old, _ = self.python_pair()
        root, bindir = self.python_fixture("python-unavailable")
        for name in ("python3.14", "python3.13", "python3.12", "python3.11", "python3", "python"):
            path = bindir / name
            path.write_text("#!/bin/sh\nexit 79\n")
            path.chmod(0o755)
        child = subprocess.run([old, str(root / "x.py"), "test"], cwd=root,
                               env=dict(self.env, TRUST_REPO=str(root), PATH=str(bindir) + ":/usr/bin:/bin:/usr/sbin:/sbin"),
                               capture_output=True, text=True, timeout=30)
        self.assertNotEqual(child.returncode, 0)
        self.assertIn("requires Python 3.11", child.stderr)
        self.assertNotIn("Traceback", child.stderr)
        self.assertFalse((root / "observed.json").exists())
        self.assertFalse((root / ".trust-build-lock").exists())

    def test_a_different_runtime_after_a_successful_probe_cannot_loop(self):
        old, new = self.python_pair()
        root, bindir = self.python_fixture("python-changed")
        wrapper = bindir / "python3.14"
        wrapper.write_text("#!/bin/sh\ncase \" $* \" in\n"
                           " *\" -c \"*) exec %s \"$@\" ;;\n"
                           " *) exec %s \"$@\" ;;\nesac\n" % (shlex.quote(new), shlex.quote(old)))
        wrapper.chmod(0o755)
        child = subprocess.run([old, str(root / "x.py"), "test"], cwd=root,
                               env=dict(self.env, TRUST_REPO=str(root), PATH=str(bindir) + ":/usr/bin:/bin:/usr/sbin:/sbin"),
                               capture_output=True, text=True, timeout=30)
        self.assertNotEqual(child.returncode, 0)
        self.assertIn("requires Python 3.11", child.stderr)
        self.assertNotIn("Traceback", child.stderr)
        self.assertFalse((root / "observed.json").exists())
        self.assertFalse((root / ".trust-build-lock").exists())

    def test_capable_python_does_not_probe_path_or_change_flags(self):
        _, new = self.python_pair()
        root, bindir = self.python_fixture("python-already-ready")
        wrapper = bindir / "python3.14"
        marker = root / "unexpected-probe"
        wrapper.write_text("#!/bin/sh\nprintf probe > %s\nexit 79\n" % shlex.quote(str(marker)))
        wrapper.chmod(0o755)
        child = subprocess.run([new, "-I", "-S", "-B", str(root / "x.py"), "test"], cwd=root,
                               env=dict(self.env, TRUST_REPO=str(root), PATH=str(bindir) + ":/usr/bin:/bin:/usr/sbin:/sbin"),
                               capture_output=True, text=True, timeout=30)
        self.assertEqual(child.returncode, 0, child.stdout + child.stderr)
        self.assertFalse(marker.exists())
        observed = json.loads((root / "observed.json").read_text())
        self.assertEqual(observed["flags"], [1, 1, 1, 1, 0, 1])
        self.assertIsNone(observed["reexec_guard"])
        self.assertFalse((root / ".trust-build-lock").exists())


if __name__ == "__main__":
    unittest.main()
