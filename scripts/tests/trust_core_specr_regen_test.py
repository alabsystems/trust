#!/usr/bin/env python3
"""Controls for scripts/trust_core/specr/regen.py (RM1: the specr → Clean translator v2 regenerates
byte for byte).

* The REAL driver on the REAL tree: every committed output is regenerated from the pinned inputs by the
  committed translator, and it is byte-identical; the manifest matches.
* Negative controls, each on a temporary copy of the translator directory beside the unmutated control:
  one changed byte of a committed output, one changed emission in the translator, and one changed pinned
  input each make the check exit 1 and name exactly what drifted.
* `write` on a mutated copy regenerates it, and the check then passes on that copy (the driver repairs
  what it reports, so a red is never a stuck red).
* The pinned gzip encoding is deterministic.
* The rest of the driver has negative controls too: a stray file in generated/, an edit to the driver
  itself, the `--from-source` front-end comparison, pin check and `write`, and every acceptance
  condition of `--clean` (a fake `clean` prints canned reports; one never exits and is killed by the
  timeout; a conformance theorem the report never names is not accepted).
* The sibling copies are judged AT THE GITLINKS of a Trust repository (fake git repositories here):
  identical at the pinned revision even when the sibling's own HEAD moved on, DRIFT for different
  bytes, a pinned revision without the file or a missing gitlink, NOT RUN for an object the store does
  not hold (exit 2 under --require-siblings, exit 0 without), the default store is first-party/NAME
  only when it is its own work tree, and `copies` writes exactly the bytes the check then accepts.
* The translator's monomorphization guards, each on a synthetic syn AST beside an accepted control:
  declared generic defaults are filled (a missing argument without one, or a surplus one, is
  refused); an ADT reference that is not the configured instance, `Self::X`/`M::X` outside the
  configured impl, and an impl of a bound trait for another owner are refused, never mis-typed.

Needs Python 3.11 or later; run with /opt/homebrew/bin/python3 (3.14).

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

import contextlib
import gzip
import importlib.util
import io
import json
import os
import shlex
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SPECR = ROOT / "scripts" / "trust_core" / "specr"
SCRIPT = SPECR / "regen.py"
SPEC = importlib.util.spec_from_file_location("trust_core_specr_regen", SCRIPT)
regen = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(regen)


def own_repo(root: Path, extra: tuple) -> tuple:
    """A temporary copy is judged against the Trust repository its test names, never one that
    happens to hold the temporary directory: without `--repo` it names a path that is no
    repository, so its sibling comparisons are NOT RUN (exit 0 without --require-siblings)."""
    if Path(root).resolve() == SPECR.resolve() or "--repo" in extra:
        return extra
    return (*extra, "--repo", str(Path(root).parent / "no-trust-repo"))


def check(root: Path, *extra: str) -> subprocess.CompletedProcess:
    return subprocess.run([sys.executable, "-B", str(SCRIPT), "check", "--root", str(root), *own_repo(root, extra)],
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=False)


def write(root: Path, *extra: str) -> subprocess.CompletedProcess:
    return subprocess.run([sys.executable, "-B", str(SCRIPT), "write", "--root", str(root), *extra],
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=False)


def copies(root: Path, *extra: str) -> subprocess.CompletedProcess:
    return subprocess.run([sys.executable, "-B", str(SCRIPT), "copies", "--root", str(root), *extra],
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=False)


GIT_ENV = {**{k: v for k, v in os.environ.items() if not k.startswith("GIT_")}, "GIT_AUTHOR_NAME": "t",
           "GIT_AUTHOR_EMAIL": "t@t", "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@t"}


def git(repo: Path, *args: str) -> str:
    return subprocess.run(["git", "-C", str(repo), *args], check=True, env=GIT_ENV, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, text=True).stdout.strip()


def git_repo(d: Path, files: dict) -> str:
    """A fresh git repository at `d` whose one commit holds `files` (path -> bytes); its sha."""
    d.mkdir(parents=True, exist_ok=True)
    git(d, "init", "-q")
    return commit(d, files)


def commit(d: Path, files: dict, drop: tuple = ()) -> str:
    for rel, data in files.items():
        (d / rel).parent.mkdir(parents=True, exist_ok=True)
        (d / rel).write_bytes(data)
    for rel in drop:
        git(d, "rm", "-q", rel)
    git(d, "add", "-A")
    git(d, "commit", "-q", "--allow-empty", "-m", "c")
    return git(d, "rev-parse", "HEAD")


def pin(trust: Path, **revs: str) -> None:
    """Commit gitlinks first-party/<name> = rev in the fake Trust repository `trust`."""
    if not (trust / ".git").exists():
        trust.mkdir(parents=True, exist_ok=True)
        git(trust, "init", "-q")
    for name, rev in revs.items():
        git(trust, "update-index", "--add", "--cacheinfo", f"160000,{rev},first-party/{name.replace('_', '-')}")
    git(trust, "commit", "-q", "--allow-empty", "-m", "pin")


def sibling_files(root: Path, name: str, **override: bytes) -> dict:
    """The files sibling `name` must hold for the copy `root`, as regen.py states them."""
    out = {path: regen.copy_source(root, what)[0] for sib, path, what in regen.SIBLING_COPIES if sib == name}
    out.update(override)
    return out


def executable(path: Path, body: str, interpreter: str | Path = sys.executable) -> Path:
    """A fake program at `path` that runs the Python `body` with `interpreter`.

    The program is a /bin/sh stub that execs the quoted interpreter on `body`, written beside it
    as `<path>.py`. A `#!<interpreter>` line cannot do this: the kernel ends the interpreter path
    at the first space, and atpkg's python3.14 (which land_gate.py re-executes into) lives under
    `~/Library/Application Support/`, so every fake program failed to start with ENOENT. `exec`
    keeps the stub's pid, so a timeout's kill reaches the Python process."""
    script = path.with_name(path.name + ".py")
    script.write_text(body)
    path.write_text(f'#!/bin/sh\nexec {shlex.quote(str(interpreter))} {shlex.quote(str(script))} "$@"\n')
    path.chmod(0o755)
    return path


def drifted(out: str) -> set[str]:
    return {line.split(None, 1)[1].strip() for line in out.splitlines() if line.startswith("DRIFT    ")}


class SpecrRegenTest(unittest.TestCase):
    def copy(self) -> Path:
        tmp = Path(tempfile.mkdtemp(prefix="specr-regen-test-"))
        self.addCleanup(shutil.rmtree, tmp, True)
        dst = tmp / "specr"
        shutil.copytree(SPECR, dst, ignore=shutil.ignore_patterns("__pycache__", "target"))
        # the copy's `--from-source` would import trust_core/common.py from its parent
        return dst

    def test_committed_tree_regenerates_byte_for_byte(self):
        proc = check(SPECR)
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.assertIn("regen: byte-identical", proc.stdout)
        self.assertEqual(drifted(proc.stdout), set())
        for f in regen.OUTPUTS:
            self.assertIn(f"identical  {f}", proc.stdout)

    def test_one_changed_output_byte_drifts(self):
        root = self.copy()
        self.assertEqual(check(root).returncode, 0, "control: the unmutated copy is identical")
        p = root / "generated" / "MiniRustSlice.lean"
        data = bytearray(p.read_bytes())
        i = data.index(b"SPick.choose")
        data[i + 6] = ord("K")  # SPick.choose -> SPick.Khoose
        p.write_bytes(bytes(data))
        proc = check(root)
        self.assertEqual(proc.returncode, 1, proc.stdout)
        self.assertEqual(drifted(proc.stdout), {"generated/MiniRustSlice.lean"})

    def test_one_changed_translator_emission_drifts(self):
        root = self.copy()
        p = root / "specr2clean" / "calls.py"
        src = p.read_text()
        self.assertIn("call = f'SPick.choose (σ := ", src)
        p.write_text(src.replace("call = f'SPick.choose (σ := ", "call = f'SPick.int (σ := ", 1))
        proc = check(root)
        self.assertEqual(proc.returncode, 1, proc.stdout)
        # the census counts the library constructs each emission reaches
        self.assertEqual(drifted(proc.stdout),
                         {"generated/MiniRustSlice.lean", "generated/census.json",
                          "generated/MANIFEST.json [translator]", "generated/MANIFEST.json [outputs]"})

    def test_one_changed_pinned_input_drifts(self):
        root = self.copy()
        p = root / "pinned" / "ast.json.gz"
        ast = gzip.decompress(p.read_bytes())
        needle = b'asking for a too large allocation'
        self.assertIn(needle, ast)
        p.write_bytes(regen.gz_bytes(ast.replace(needle, b'asking for a too big allocation', 1)))
        proc = check(root)
        self.assertEqual(proc.returncode, 1, proc.stdout)
        self.assertEqual(drifted(proc.stdout),
                         {"generated/MiniRustSlice.lean", "generated/census.json",
                          "generated/MANIFEST.json [pinned]", "generated/MANIFEST.json [outputs]"})

    def test_write_repairs_what_check_reports(self):
        root = self.copy()
        p = root / "specr2clean" / "calls.py"
        p.write_text(p.read_text().replace("call = f'SPick.choose (σ := ", "call = f'SPick.int (σ := ", 1))
        self.assertEqual(check(root).returncode, 1)
        w = subprocess.run([sys.executable, "-B", str(SCRIPT), "write", "--root", str(root)],
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=False)
        self.assertEqual(w.returncode, 0, w.stdout + w.stderr)
        self.assertEqual(check(root).returncode, 0)
        self.assertIn(b"SPick.int (", (root / "generated" / "MiniRustSlice.lean").read_bytes())

    def test_gzip_encoding_is_deterministic(self):
        data = b"specr\n" * 1000
        self.assertEqual(regen.gz_bytes(data), regen.gz_bytes(data))
        self.assertEqual(gzip.decompress(regen.gz_bytes(data)), data)
        self.assertEqual((SPECR / "pinned" / "ast.json.gz").read_bytes(),
                         regen.gz_bytes(gzip.decompress((SPECR / "pinned" / "ast.json.gz").read_bytes())))

    # ---- the rest of the driver ----

    def tmpdir(self) -> Path:
        tmp = Path(tempfile.mkdtemp(prefix="specr-regen-aux-"))
        self.addCleanup(shutil.rmtree, tmp, True)
        return tmp

    def test_a_fake_program_runs_under_an_interpreter_path_with_a_space(self):
        # the fake front end and fake clean below are such programs; a `#!` line naming an
        # interpreter under a directory with a space (atpkg's `Application Support`) never ran
        tmp = self.tmpdir()
        spaced = tmp / "interpreter dir"
        spaced.mkdir()
        (spaced / "python").symlink_to(sys.executable)
        prog = executable(tmp / "prog", "import sys\nsys.stdout.write('ran ' + '|'.join(sys.argv[1:]))\n",
                          interpreter=spaced / "python")
        proc = subprocess.run([str(prog), "a b", "c"], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                              check=False)
        self.assertEqual((proc.returncode, proc.stdout), (0, "ran a b|c"), proc.stderr)

    def test_a_stray_file_in_generated_drifts(self):
        root = self.copy()
        (root / "generated" / "Stale.lean").write_text("-- left over\n")
        proc = check(root)
        self.assertEqual(proc.returncode, 1, proc.stdout)
        self.assertEqual(drifted(proc.stdout), {"generated/Stale.lean  (not an output of this translator)"})

    def test_an_edit_to_the_driver_drifts(self):
        root = self.copy()
        p = root / "regen.py"
        p.write_text(p.read_text().replace("STEPS, FUEL = 200000, 2000", "STEPS, FUEL = 200000, 2000  # edited", 1))
        proc = check(root)
        self.assertEqual(proc.returncode, 1, proc.stdout)
        self.assertEqual(drifted(proc.stdout), {"generated/MANIFEST.json [translator]"})

    # ---- sibling copies, judged at the gitlinks

    def siblings(self, root: Path) -> dict:
        """Fake Clean and trust-ir repositories holding `root`'s copies, and a fake Trust repository
        pinning them; the check arguments that name all three."""
        tmp = self.tmpdir()
        c = tmp / "clean"
        t = tmp / "trust-ir"
        crev = git_repo(c, sibling_files(root, "clean"))
        trev = git_repo(t, sibling_files(root, "trust-ir"))
        trust = tmp / "trust"
        pin(trust, clean=crev, trust_ir=trev)
        args = ("--repo", str(trust), "--sibling-git", f"clean={c}", "--sibling-git", f"trust-ir={t}")
        return {"clean": c, "trust-ir": t, "trust": trust, "crev": crev, "trev": trev, "args": args}

    def test_siblings_are_identical_at_their_gitlinks(self):
        root = self.copy()
        sb = self.siblings(root)
        proc = check(root, *sb["args"], "--require-siblings")
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        for sib, path, _ in regen.SIBLING_COPIES:
            rev = sb["crev"] if sib == "clean" else sb["trev"]
            self.assertIn(f"identical  {sib}@{rev[:10]} {path}  (=", proc.stdout)
        self.assertNotIn("NOT RUN", proc.stdout)
        self.assertEqual(drifted(proc.stdout), set())

    def test_a_prelude_edit_drifts_against_every_sibling_copy_of_it(self):
        root = self.copy()
        sb = self.siblings(root)
        # a semantic edit to the runtime, with the manifest refreshed so only the copies can see it
        p = root / "SpecrPrelude.lean"
        src = p.read_text()
        self.assertIn("    (fun _ ih => SOut.searchNat bound 0 ih)\n    (fun _ ih => SOut.searchNat bound 0 ih)", src)
        p.write_text(src.replace("    (fun _ ih => SOut.searchNat bound 0 ih)\n    (fun _ ih => SOut.searchNat bound 0 ih)",
                                 "    (fun _ ih => SOut.searchNat bound 0 ih)\n    (fun _ ih => SOut.searchNat bound 1 ih)", 1))
        self.assertEqual(write(root).returncode, 0)
        self.assertEqual(check(root).returncode, 0, "without the siblings, the refreshed manifest hides the edit")
        proc = check(root, *sb["args"])
        self.assertEqual(proc.returncode, 1, proc.stdout)
        c, t = sb["crev"][:10], sb["trev"][:10]
        self.assertEqual({d.split("  (")[0] for d in drifted(proc.stdout)},
                         {f"clean@{c} {regen.CLEAN_FIXTURES}/trust_sem/SpecrPrelude.lean",
                          f"clean@{c} {regen.CLEAN_FIXTURES}/semr/MiniRust.lean",
                          f"trust-ir@{t} lean/semr/MiniRust.lean"})
        self.assertIn(f"identical  clean@{c} {regen.CLEAN_FIXTURES}/trust_sem/MiniRustSlice.lean", proc.stdout)

    def test_the_copies_are_read_at_the_gitlink_not_at_the_siblings_head(self):
        root = self.copy()
        sb = self.siblings(root)
        prelude = f"{regen.CLEAN_FIXTURES}/trust_sem/SpecrPrelude.lean"
        # the sibling's own HEAD moves on to a drifted copy; the pin still names the identical one
        later = commit(sb["clean"], {prelude: b"-- moved on\n"})
        proc = check(root, *sb["args"], "--require-siblings")
        self.assertEqual(proc.returncode, 0, "the pinned revision is identical " + proc.stdout)
        # moving the gitlink to that commit makes the same comparison drift
        pin(sb["trust"], clean=later)
        proc = check(root, *sb["args"], "--require-siblings")
        self.assertEqual(proc.returncode, 1, proc.stdout)
        self.assertEqual({d.split("  (")[0] for d in drifted(proc.stdout)}, {f"clean@{later[:10]} {prelude}"})

    def test_a_pinned_revision_without_a_copy_drifts(self):
        root = self.copy()
        sb = self.siblings(root)
        wrapper = f"{regen.CLEAN_FIXTURES}/semr/MiniRust.lean"
        pin(sb["trust"], clean=commit(sb["clean"], {}, drop=(wrapper,)))
        proc = check(root, *sb["args"])
        self.assertEqual(proc.returncode, 1, proc.stdout)
        self.assertEqual(len(drifted(proc.stdout)), 1, proc.stdout)
        self.assertIn(f"{wrapper}  (no such file at ", proc.stdout)

    def test_a_missing_gitlink_drifts(self):
        root = self.copy()
        sb = self.siblings(root)
        git(sb["trust"], "rm", "-q", "--cached", "first-party/trust-ir")
        git(sb["trust"], "commit", "-q", "-m", "unpin")
        proc = check(root, *sb["args"])
        self.assertEqual(proc.returncode, 1, proc.stdout)
        self.assertIn("lean/semr/MiniRust.lean  (HEAD of", proc.stdout)
        self.assertIn("has no gitlink first-party/trust-ir)", proc.stdout)

    def test_an_absent_object_is_not_run_and_fails_only_under_require_siblings(self):
        root = self.copy()
        sb = self.siblings(root)
        empty = self.tmpdir() / "empty-clean"
        git_repo(empty, {"README": b"no pinned commit here\n"})
        args = ("--repo", str(sb["trust"]), "--sibling-git", f"clean={empty}", "--sibling-git", f"trust-ir={sb['trust-ir']}")
        proc = check(root, *args)
        self.assertEqual(proc.returncode, 0, "NOT RUN alone does not fail " + proc.stdout)
        not_run = [line for line in proc.stdout.splitlines() if line.startswith("NOT RUN")]
        self.assertEqual(len(not_run), 3, proc.stdout)
        self.assertTrue(all(f"does not hold commit {sb['crev']}" in line for line in not_run), not_run)
        self.assertIn("identical  trust-ir@", proc.stdout)
        proc = check(root, *args, "--require-siblings")
        self.assertEqual(proc.returncode, 2, proc.stdout)
        # no Trust repository at all: every comparison is NOT RUN, never identical
        proc = check(root, "--require-siblings")
        self.assertEqual(proc.returncode, 2, proc.stdout)
        self.assertEqual(sum(line.startswith("NOT RUN") for line in proc.stdout.splitlines()), len(regen.SIBLING_COPIES))
        self.assertNotIn("identical  clean@", proc.stdout)

    def test_drift_outranks_not_run(self):
        root = self.copy()
        sb = self.siblings(root)
        pin(sb["trust"], clean=commit(sb["clean"], {f"{regen.CLEAN_FIXTURES}/trust_sem/MiniRustSlice.lean": b"x\n"}))
        proc = check(root, "--repo", str(sb["trust"]), "--sibling-git", f"clean={sb['clean']}", "--require-siblings")
        self.assertEqual(proc.returncode, 1, proc.stdout)
        self.assertIn("NOT RUN    trust-ir@", proc.stdout)

    def test_the_default_store_is_first_party_only_when_checked_out(self):
        root = self.copy()
        sb = self.siblings(root)
        # an empty first-party/clean inside the Trust repository is not Clean's object store
        (sb["trust"] / "first-party" / "clean").mkdir(parents=True)
        proc = check(root, "--repo", str(sb["trust"]), "--sibling-git", f"trust-ir={sb['trust-ir']}")
        self.assertEqual(sum(line.startswith("NOT RUN    clean@") for line in proc.stdout.splitlines()), 3, proc.stdout)
        self.assertIn("first-party/clean is not checked out", proc.stdout)
        # a checked-out first-party/clean (its own work tree) is read without --sibling-git
        shutil.rmtree(sb["trust"] / "first-party" / "clean")
        git(sb["trust"], "-c", "protocol.file.allow=always", "clone", "-q", str(sb["clean"]), "first-party/clean")
        proc = check(root, "--repo", str(sb["trust"]), "--sibling-git", f"trust-ir={sb['trust-ir']}", "--require-siblings")
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.assertEqual(sum(line.startswith(f"identical  clean@{sb['crev'][:10]}") for line in proc.stdout.splitlines()), 3)

    def test_sibling_git_names_a_known_sibling_once(self):
        root = self.copy()
        for bad in (["--sibling-git", "ay=/tmp"], ["--sibling-git", "clean"],
                    ["--sibling-git", "clean=/a", "--sibling-git", "clean=/b"]):
            proc = check(root, *bad)
            self.assertNotEqual(proc.returncode, 0, bad)
            self.assertIn("--sibling-git", proc.stderr, bad)

    def test_copies_writes_what_the_check_then_accepts(self):
        root = self.copy()
        tmp = self.tmpdir()
        c, t = tmp / "clean", tmp / "trust-ir"
        stale = {path: b"stale\n" for sib, path, _ in regen.SIBLING_COPIES}
        git_repo(c, {k: v for k, v in stale.items() if not k.startswith("lean/")})
        git_repo(t, {k: v for k, v in stale.items() if k.startswith("lean/")})
        w = copies(root, "--clean", str(c), "--trust-ir", str(t))
        self.assertEqual(w.returncode, 0, w.stdout + w.stderr)
        self.assertEqual(w.stdout.count("wrote "), len(regen.SIBLING_COPIES), w.stdout)
        for sib, path, what in regen.SIBLING_COPIES:
            self.assertEqual(((c if sib == "clean" else t) / path).read_bytes(), regen.copy_source(root, what)[0])
        again = copies(root, "--clean", str(c), "--trust-ir", str(t))
        self.assertEqual(again.stdout.count("unchanged"), len(regen.SIBLING_COPIES), again.stdout)
        trust = tmp / "trust"
        pin(trust, clean=commit(c, {}), trust_ir=commit(t, {}))
        proc = check(root, "--repo", str(trust), "--sibling-git", f"clean={c}", "--sibling-git", f"trust-ir={t}",
                     "--require-siblings")
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)

    def test_copies_refuses_a_wrong_tree_and_an_unrecorded_source(self):
        root = self.copy()
        tmp = self.tmpdir()
        self.assertNotEqual(copies(root).returncode, 0, "no destination")
        proc = copies(root, "--trust-ir", str(tmp))  # no lean/semr/ there
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn("is " + str(tmp) + " a trust-ir checkout", proc.stderr)
        (tmp / "lean" / "semr").mkdir(parents=True)
        p = root / "SpecrPrelude.lean"
        p.write_text(p.read_text() + "-- unrecorded\n")
        proc = copies(root, "--trust-ir", str(tmp))
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn("differs from generated/MANIFEST.json [translator]", proc.stderr)
        self.assertFalse((tmp / "lean" / "semr" / "MiniRust.lean").exists(), "nothing is written on a refusal")

    def fake_minirust(self) -> Path:
        """A git checkout with a `spec/` directory; returns it (its HEAD is not the real pin)."""
        mr = self.tmpdir() / "minirust"
        (mr / "spec").mkdir(parents=True)
        (mr / "spec" / "README.md").write_text("fake\n")
        env = {**os.environ, "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@t", "GIT_COMMITTER_NAME": "t",
               "GIT_COMMITTER_EMAIL": "t@t"}
        for cmd in (["init", "-q"], ["add", "."], ["commit", "-q", "-m", "fake"]):
            subprocess.run(["git", "-C", str(mr), *cmd], check=True, env=env, stdout=subprocess.PIPE)
        return mr

    def fake_frontend(self, ast: bytes) -> Path:
        tmp = self.tmpdir()
        (tmp / "ast.json").write_bytes(ast)
        return executable(tmp / "frontend", f"import sys\nsys.stdout.buffer.write(open({str(tmp / 'ast.json')!r}, 'rb').read())\n")

    def pin_copy_to(self, root: Path, mr: Path) -> None:
        rev = subprocess.run(["git", "-C", str(mr), "rev-parse", "HEAD"], stdout=subprocess.PIPE, text=True,
                             check=True).stdout.strip()
        p = root / "slice.json"
        cfg = json.loads(p.read_text())
        cfg["minirust_revision"] = rev
        p.write_text(json.dumps(cfg, indent=2) + "\n")

    def test_from_source_compares_the_front_end_ast(self):
        root = self.copy()
        mr = self.fake_minirust()
        self.pin_copy_to(root, mr)
        pinned = gzip.decompress((root / "pinned" / "ast.json.gz").read_bytes())
        same = check(root, "--from-source", "--frontend", str(self.fake_frontend(pinned)), "--minirust", str(mr))
        self.assertIn("identical  pinned/ast.json.gz", same.stdout, "control: the same AST " + same.stdout + same.stderr)
        other = pinned.replace(b"asking for a too large allocation", b"asking for a too big allocation", 1)
        self.assertNotEqual(other, pinned)
        proc = check(root, "--from-source", "--frontend", str(self.fake_frontend(other)), "--minirust", str(mr))
        self.assertEqual(proc.returncode, 1, proc.stdout)
        self.assertIn(f"pinned/ast.json.gz  (front end on {mr})", drifted(proc.stdout))

    def test_from_source_refuses_a_checkout_off_the_pin(self):
        root = self.copy()
        mr = self.fake_minirust()  # its HEAD is not slice.json's pin
        pinned = gzip.decompress((root / "pinned" / "ast.json.gz").read_bytes())
        proc = check(root, "--from-source", "--frontend", str(self.fake_frontend(pinned)), "--minirust", str(mr))
        self.assertNotEqual(proc.returncode, 0, proc.stdout)
        self.assertIn("not the pin", proc.stderr)
        self.assertNotIn("identical  pinned/ast.json.gz", proc.stdout)

    def test_write_from_source_rewrites_the_pinned_ast(self):
        root = self.copy()
        mr = self.fake_minirust()
        self.pin_copy_to(root, mr)
        pinned = gzip.decompress((root / "pinned" / "ast.json.gz").read_bytes())
        other = pinned.replace(b"asking for a too large allocation", b"asking for a too big allocation", 1)
        w = write(root, "--from-source", "--frontend", str(self.fake_frontend(other)), "--minirust", str(mr))
        self.assertEqual(w.returncode, 0, w.stdout + w.stderr)
        self.assertEqual(gzip.decompress((root / "pinned" / "ast.json.gz").read_bytes()), other)
        self.assertEqual(check(root).returncode, 0, "write left a consistent tree")

    # `--clean`: each acceptance condition, judged on a canned report

    THEOREMS = [t["theorem"] for t in json.loads((SPECR / "generated" / "conformance_index.json").read_text())["theorems"]]
    GOOD = {"failed_count": 0, "success_count": 1, "decl_count": 1, "errors": [], "assumptions": [],
            "diverged": False, "trust_summary": {"sorry_axioms": 0, "sorry_terms_minted": 0,
                                                 "kernel_check_failures": 0},
            "timing": {"per_declaration": [{"name": t, "line": 1, "elapsed_ms": 1.0} for t in THEOREMS]}}

    def fake_clean(self, report: dict, sleep: float = 0) -> Path:
        tmp = self.tmpdir()
        (tmp / "report.json").write_text(json.dumps(report))
        return executable(tmp / "clean", f"import sys, time\ntime.sleep({sleep})\n"
                                         f"sys.stdout.write(open({str(tmp / 'report.json')!r}).read())\n")

    def clean_ok(self, report, timeout: float = 60, sleep: float = 0) -> bool:
        return regen.clean_check(SPECR, self.fake_clean(report, sleep), timeout)

    def with_(self, **changes) -> dict:
        rep = json.loads(json.dumps(self.GOOD))
        for k, v in changes.items():
            if k in rep["trust_summary"]:
                rep["trust_summary"][k] = v
            else:
                rep[k] = v
        return rep

    def test_clean_accepts_only_a_clean_report(self):
        self.assertTrue(self.clean_ok(self.GOOD), "control: the clean report is accepted")
        theorem = json.loads((SPECR / "generated" / "conformance_index.json").read_text())["theorems"][0]["theorem"]
        for name, rep in [("a failed declaration", self.with_(failed_count=1)),
                          ("a sorry axiom", self.with_(sorry_axioms=1)),
                          ("a sorry term", self.with_(sorry_terms_minted=1)),
                          ("a kernel-check failure", self.with_(kernel_check_failures=1)),
                          ("an assumption", self.with_(assumptions=["Classical.em"])),
                          ("a divergence", self.with_(diverged=True)),
                          ("a failed conformance theorem", self.with_(errors=[f"{theorem}: type mismatch"]))]:
            with self.subTest(name):
                self.assertFalse(self.clean_ok(rep), name)

    def test_a_conformance_theorem_absent_from_the_report_is_not_accepted(self):
        # the report counts no failure, yet one theorem is missing from it: not accepted (it used to be)
        for drop in (self.THEOREMS[0], self.THEOREMS[-1]):
            rep = self.with_()
            rep["timing"]["per_declaration"] = [d for d in rep["timing"]["per_declaration"] if d["name"] != drop]
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                self.assertFalse(self.clean_ok(rep), drop)
            self.assertIn(f"{len(self.THEOREMS) - 1}/{len(self.THEOREMS)} conformance theorems", out.getvalue())
            self.assertIn("1 absent from the report", out.getvalue())
        rep = self.with_()
        del rep["timing"]
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertFalse(self.clean_ok(rep), "a report with no per-declaration timing names no theorem")

    def test_clean_without_the_sorry_counter_fails_closed(self):
        for drop in ("sorry_terms_minted", "trust_summary"):
            rep = self.with_()
            if drop == "trust_summary":
                del rep["trust_summary"]
            else:
                del rep["trust_summary"][drop]
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                self.assertFalse(self.clean_ok(rep), drop)
            # the refusal names why, so an old clean is not mistaken for a red proof
            self.assertIn("older than this check needs", out.getvalue(), drop)

    def test_clean_with_no_report_fails(self):
        self.assertFalse(regen.clean_check(SPECR, executable(self.tmpdir() / "clean", "print('not json')\n"), 60))

    def test_a_clean_that_never_finishes_is_killed(self):
        self.assertTrue(self.clean_ok(self.GOOD, timeout=60, sleep=0.1), "control: a slow but finishing run")
        self.assertFalse(self.clean_ok(self.GOOD, timeout=1, sleep=30))



# ---- the translator's monomorphization guards, on synthetic syn ASTs

TRANSLATOR = SPECR / "specr2clean"

# Runs in its own interpreter (the translator's modules are named `common`, `items`, `tyres`):
# builds the Program, resolves every ADT's fields and every function's return type, and prints
# what was accepted (the type, as the translator spells it) and what was refused (the construct).
DRIVER = r"""
import json, sys
sys.path.insert(0, sys.argv[1])
from common import Refusal, show_ty
from items import Program
from tyres import resolve, resolve_adts
ast, cfg = json.load(open(sys.argv[2]))
prog = Program(ast, cfg)
resolve_adts(prog)
out = {"refused_items": sorted({(i.split(": ", 1)[1], c) for i, c, _ in prog.refused_items}),
       "adts": {n: (a.refused.construct if getattr(a, "refused", None) else "ok") for n, a in sorted(prog.adts.items())},
       "fns": {}}
for fd in prog.fns:
    try:
        out["fns"][fd.display] = "ok " + show_ty(resolve(prog, fd.output, fd.generics, fd.owner))
    except Refusal as r:
        out["fns"][fd.display] = "refused " + r.construct
print(json.dumps(out))
"""

# The slice's monomorphization, cut down: Memory at BasicMemory, Target at x86_64.
CFG = {"monomorphization": {
    "bound": {"Memory": ["adt", "BasicMemory"], "Target": ["adt", "x86_64"]},
    "param": {"Provenance": ["unit"], "ProvExtra": ["unit"], "AllocExtra": ["unit"], "A": ["int"], "B": ["int"]},
    "polymorphic": ["O"],
    "assoc_type": {"Provenance": ["unit"], "T": ["adt", "x86_64"]}}}


def ty(name, *args):
    seg = {"ident": name}
    if args:
        seg["arguments"] = {"angle_bracketed": {"args": [{"type": a} for a in args]}}
    return {"path": {"segments": [seg]}}


def path_ty(*names):
    return {"path": {"segments": [{"ident": n} for n in names]}}


def qself_ty(self_ty, trait, name):
    return {"path": {"qself": {"as_token": True, "position": 1, "ty": self_ty},
                     "segments": [{"ident": trait}, {"ident": name}]}}


UNIT_TY = {"tuple": {"elems": []}}


def tparam(name, *bounds, default=None):
    p = {"ident": name}
    if bounds:
        p["bounds"] = [{"trait": {"path": {"segments": [{"ident": b}]}}} for b in bounds]
        p["colon_token"] = True
    if default is not None:
        p["default"], p["eq_token"] = default, True
    return {"type": p}


def generics(*params):
    return {"params": list(params)} if params else None


def struct(name, *params, fields=()):
    v = {"ident": name, "fields": {"named": [{"ident": f, "ty": t} for f, t in fields]} if fields else "unit"}
    if params:
        v["generics"] = generics(*params)
    return {"struct": v}


def fn(name, output, *params, default=False):
    v = {"ident": name, "inputs": [], "output": output}
    v["default" if default else "stmts"] = []
    if params:
        v["generics"] = generics(*params)
    return {"fn": v}


def trait(name, *assoc, fns=()):
    return {"trait": {"ident": name, "items": [{"type": {"ident": a}} for a in assoc] + list(fns)}}


def impl(self_ty, *items, params=(), of=None):
    v = {"self_ty": self_ty, "items": list(items)}
    if params:
        v["generics"] = generics(*params)
    if of:
        v["trait"] = [False, {"segments": [{"ident": of}]}]
    return {"impl": v}


def alias(name, body, *params):
    v = {"ident": name, "ty": body}
    if params:
        v["generics"] = generics(*params)
    return {"type": v}


BASE = [struct("x86_64"), struct("Path"), trait("Target"),
        trait("Memory", "Provenance", "T", fns=[fn("retag", UNIT_TY, default=True)]),
        struct("BasicMemory", tparam("T", "Target"), tparam("ProvExtra", default=UNIT_TY),
               tparam("AllocExtra", default=UNIT_TY))]


class TranslatorGuardTest(unittest.TestCase):
    def translate(self, *items) -> dict:
        tmp = Path(tempfile.mkdtemp(prefix="specr-guard-test-"))
        self.addCleanup(shutil.rmtree, tmp, True)
        ast = {"files": [{"path": "synthetic.md", "code_lines": 1, "prelude_macros": [],
                          "ast": {"items": [*BASE, *items]}}]}
        (tmp / "in.json").write_text(json.dumps([ast, CFG]))
        proc = subprocess.run([sys.executable, "-B", "-c", DRIVER, str(TRANSLATOR), str(tmp / "in.json")],
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=False)
        self.assertEqual(proc.returncode, 0, proc.stderr)
        return json.loads(proc.stdout)

    def test_declared_defaults_fill_missing_arguments(self):
        out = self.translate(
            struct("Allocation", tparam("ProvExtra", default=UNIT_TY), tparam("AllocExtra", default=UNIT_TY)),
            struct("Thin", tparam("Provenance")),
            alias("Pair", {"tuple": {"elems": [ty("A"), ty("B")]}}, tparam("A"), tparam("B", default=ty("A"))),
            fn("none_given", ty("Allocation")),
            fn("one_given", ty("Allocation", UNIT_TY)),
            fn("all_given", ty("Allocation", UNIT_TY, UNIT_TY)),
            fn("defaults_after_t", ty("BasicMemory", ty("T")), tparam("T", "Target")),
            fn("too_many", ty("Allocation", UNIT_TY, UNIT_TY, UNIT_TY)),
            fn("no_default", ty("Thin")),
            fn("thin", ty("Thin", UNIT_TY)),
            fn("alias_default_names_earlier", ty("Pair", ty("bool"))),
        )["fns"]
        self.assertEqual(out["none_given"], "ok Allocation")
        self.assertEqual(out["one_given"], "ok Allocation")
        self.assertEqual(out["all_given"], "ok Allocation")
        self.assertEqual(out["defaults_after_t"], "ok BasicMemory")
        self.assertEqual(out["thin"], "ok Thin")
        self.assertEqual(out["too_many"], "refused type-argument-count")
        self.assertEqual(out["no_default"], "refused missing-type-argument")
        # `type Pair<A, B = A>`: `Pair<bool>` is `(bool, bool)`, B's default read with A bound
        self.assertEqual(out["alias_default_names_earlier"], "ok (bool, bool)")

    def test_guard_a_refuses_an_adt_reference_off_the_configured_instance(self):
        out = self.translate(
            struct("TreeBorrowsMemory", tparam("T", "Target"),
                   fields=[("mem", ty("BasicMemory", ty("T"), ty("Path"), UNIT_TY))]),
            struct("Wrapper", tparam("T", "Target"), fields=[("mem", ty("BasicMemory", ty("T")))]),
            fn("configured", ty("BasicMemory", ty("T")), tparam("T", "Target")),
            fn("configured_explicit", ty("BasicMemory", ty("x86_64"), UNIT_TY, UNIT_TY)),
            fn("other_extra", ty("BasicMemory", ty("T"), ty("Path")), tparam("T", "Target")),
            fn("other_target", ty("BasicMemory", ty("Path"))),
            fn("qualified_other", {"path": {"segments": [
                {"ident": "crate"}, {"ident": "mem"},
                {"ident": "BasicMemory", "arguments": {"angle_bracketed": {"args": [
                    {"type": ty("x86_64")}, {"type": ty("Path")}]}}}]}}),
            fn("qualified_configured", {"path": {"segments": [
                {"ident": "crate"}, {"ident": "mem"},
                {"ident": "BasicMemory", "arguments": {"angle_bracketed": {"args": [{"type": ty("x86_64")}]}}}]}}),
            impl(ty("BasicMemory", ty("T"), ty("Path"), UNIT_TY), fn("off_instance", ty("Self")),
                 params=(tparam("T", "Target"),)),
            impl(ty("BasicMemory", ty("T")), fn("on_instance", ty("Self")), params=(tparam("T", "Target"),)),
        )
        self.assertEqual(out["adts"]["TreeBorrowsMemory"], "adt-instance-not-configured")
        self.assertEqual(out["adts"]["Wrapper"], "ok")
        self.assertEqual(out["fns"]["configured"], "ok BasicMemory")
        self.assertEqual(out["fns"]["configured_explicit"], "ok BasicMemory")
        self.assertEqual(out["fns"]["other_extra"], "refused adt-instance-not-configured")
        self.assertEqual(out["fns"]["other_target"], "refused adt-instance-not-configured")
        self.assertEqual(out["fns"]["qualified_other"], "refused adt-instance-not-configured")
        self.assertEqual(out["fns"]["qualified_configured"], "ok BasicMemory")
        self.assertEqual(out["fns"]["BasicMemory::on_instance"], "ok BasicMemory")
        self.assertNotIn("BasicMemory::off_instance", out["fns"])
        self.assertIn(["impl  for BasicMemory::off_instance", "adt-instance-not-configured"], out["refused_items"])

    def test_guard_b_refuses_associated_types_outside_the_configured_impl(self):
        out = self.translate(
            struct("TreeBorrowsMemory", tparam("T", "Target")),
            impl(ty("BasicMemory", ty("T")), fn("in_configured", path_ty("Self", "Provenance")),
                 params=(tparam("T", "Target"),), of="Memory"),
            impl(ty("BasicMemory", ty("T")), fn("inherent_configured", path_ty("Self", "Provenance")),
                 params=(tparam("T", "Target"),)),
            impl(ty("TreeBorrowsMemory", ty("T")), fn("in_other", path_ty("Self", "Provenance")),
                 params=(tparam("T", "Target"),)),
            fn("bound_m", path_ty("M", "Provenance"), tparam("M", "Memory")),
            fn("poly_o", path_ty("O", "Provenance"), tparam("O")),
            fn("target_t", path_ty("T", "Provenance"), tparam("T", "Target")),
            fn("qualified_m", qself_ty(ty("M"), "Memory", "Provenance"), tparam("M", "Memory")),
            fn("qualified_wrong_trait", qself_ty(ty("M"), "Target", "Provenance"), tparam("M", "Memory")),
            fn("qualified_compound", qself_ty(ty("List", ty("M")), "Memory", "Provenance"), tparam("M", "Memory")),
        )["fns"]
        self.assertEqual(out["<BasicMemory as Memory>::in_configured"], "ok unit")
        self.assertEqual(out["BasicMemory::inherent_configured"], "ok unit")
        self.assertEqual(out["bound_m"], "ok unit")
        self.assertEqual(out["qualified_m"], "ok unit")
        self.assertEqual(out["TreeBorrowsMemory::in_other"], "refused associated-type-outside-configured-impl")
        self.assertEqual(out["poly_o"], "refused associated-type-outside-configured-impl")
        self.assertEqual(out["target_t"], "refused associated-type-outside-configured-impl")
        self.assertEqual(out["qualified_wrong_trait"], "refused associated-type-outside-configured-impl")
        self.assertEqual(out["qualified_compound"], "refused qualified-self-type")

    def test_guard_c_refuses_an_impl_of_a_bound_trait_for_another_owner(self):
        out = self.translate(
            struct("TreeBorrowsMemory", tparam("T", "Target")),
            trait("Allocator", fns=[fn("by_default", UNIT_TY, default=True)]),
            impl(ty("BasicMemory", ty("T")), fn("new", ty("Self")), params=(tparam("T", "Target"),), of="Memory"),
            impl(ty("TreeBorrowsMemory", ty("T")), fn("new", ty("Self")), {"type": {"ident": "Provenance", "ty": UNIT_TY}},
                 params=(tparam("T", "Target"),), of="Memory"),
            impl(ty("x86_64"), fn("bits", ty("Int")), of="Target"),
            impl(ty("Path"), fn("bits", ty("Int")), of="Target"),
            impl(ty("TreeBorrowsMemory", ty("T")), fn("own", UNIT_TY), params=(tparam("T", "Target"),), of="Allocator"),
        )
        self.assertEqual(out["fns"]["<BasicMemory as Memory>::new"], "ok BasicMemory")
        self.assertEqual(out["fns"]["<x86_64 as Target>::bits"], "ok int")
        # the configured impl gets the trait's default method; the refused one gets nothing
        self.assertEqual(out["fns"]["<BasicMemory as Memory>::retag"], "ok unit")
        self.assertEqual([f for f in out["fns"] if f.startswith("<TreeBorrowsMemory as Memory>")], [])
        self.assertNotIn("<Path as Target>::bits", out["fns"])
        self.assertIn(["impl Memory for TreeBorrowsMemory::new", "impl-of-bound-trait-for-unconfigured-owner"],
                      out["refused_items"])
        self.assertIn(["impl Memory for TreeBorrowsMemory::Provenance", "impl-of-bound-trait-for-unconfigured-owner"],
                      out["refused_items"])
        self.assertIn(["impl Target for Path::bits", "impl-of-bound-trait-for-unconfigured-owner"], out["refused_items"])
        # a trait that is not bound by the monomorphization is not this guard's
        self.assertEqual(out["fns"]["<TreeBorrowsMemory as Allocator>::by_default"], "ok unit")


if __name__ == "__main__":
    unittest.main()
