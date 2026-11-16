#!/usr/bin/env python3
"""Real Git counterexamples for the lattice's immutable ancestry reader."""
import importlib.util
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

SOURCE = Path(__file__).resolve().parents[1] / "check_first_party_pin_lattice.py"
spec = importlib.util.spec_from_file_location("lattice_isolation_subject", SOURCE)
lattice = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = lattice
spec.loader.exec_module(lattice)


class GitIsolation(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="lattice-git-isolation-")
        self.addCleanup(self.temp.cleanup)
        self.addCleanup(lattice._close_batches)
        self.root = Path(self.temp.name)
        self.env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
        self.env.update(GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1",
                        GIT_NO_REPLACE_OBJECTS="1", GIT_GRAFT_FILE=os.devnull,
                        GIT_AUTHOR_NAME="Fixture", GIT_AUTHOR_EMAIL="fixture@example.invalid",
                        GIT_COMMITTER_NAME="Fixture", GIT_COMMITTER_EMAIL="fixture@example.invalid")
        self.git("init", "--quiet", "--template=", "--object-format=sha1")
        tree = self.git("mktree", data="")
        self.a = self.git("commit-tree", tree, "-m", "root A")
        self.b = self.git("commit-tree", tree, "-m", "independent root B")
        self.git("update-ref", "refs/heads/main", self.a)
        self.store = lattice.Store("clean", [self.root / ".git"])

    def git(self, *args, data=None, env=None, check=True):
        done = subprocess.run(["git", "-C", str(self.root), *args], input=data,
                              text=True, capture_output=True, env=env or self.env)
        if check:
            self.assertEqual(done.returncode, 0, done.stderr)
            return done.stdout.strip()
        return done

    def assert_graft_control(self, env):
        control = self.git("merge-base", "--is-ancestor", self.b, self.a,
                           env=env, check=False)
        self.assertEqual(control.returncode, 0, control.stderr)
        self.assertEqual(env["GIT_NO_REPLACE_OBJECTS"], "1")

    def test_inherited_graft_cannot_make_an_unrelated_kernel_an_ancestor(self):
        self.assertFalse(self.store.is_ancestor(self.b, self.a))
        graft = self.root / "external-grafts"
        graft.write_text(f"{self.a} {self.b}\n")
        hostile = dict(self.env, GIT_GRAFT_FILE=str(graft))
        self.assert_graft_control(hostile)
        with patch.dict(os.environ, hostile, clear=True):
            self.assertFalse(self.store.is_ancestor(self.b, self.a))

    def test_cached_info_grafts_cannot_make_an_unrelated_kernel_an_ancestor(self):
        (self.root / ".git/info").mkdir(exist_ok=True)
        (self.root / ".git/info/grafts").write_text(f"{self.a} {self.b}\n")
        hostile = dict(self.env)
        hostile.pop("GIT_GRAFT_FILE")
        self.assert_graft_control(hostile)
        with patch.dict(os.environ, hostile, clear=True):
            self.assertFalse(self.store.is_ancestor(self.b, self.a))

    def test_ambient_namespace_and_configuration_are_not_authority_inputs(self):
        hostile = {name: "untrusted" for name in (
            "GIT_NAMESPACE", "GIT_CONFIG_GLOBAL", "GIT_CONFIG_SYSTEM", "GIT_CONFIG_COUNT",
            "GIT_CONFIG_KEY_0", "GIT_CONFIG_VALUE_0", "GIT_CONFIG_PARAMETERS",
            "GIT_TEMPLATE_DIR", "GIT_SHALLOW_FILE", "GIT_DEFAULT_HASH",
            "GIT_OBJECT_DIRECTORY", "GIT_ALTERNATE_OBJECT_DIRECTORIES")}
        with patch.dict(os.environ, hostile):
            env = lattice._git_env()
        self.assertEqual(env["GIT_CONFIG_GLOBAL"], os.devnull)
        self.assertEqual(env["GIT_CONFIG_NOSYSTEM"], "1")
        self.assertEqual(env["GIT_GRAFT_FILE"], os.devnull)
        self.assertEqual(env["GIT_NO_REPLACE_OBJECTS"], "1")
        self.assertEqual(env["GIT_NO_LAZY_FETCH"], "1")
        for name in hostile.keys() - {"GIT_CONFIG_GLOBAL"}:
            self.assertNotIn(name, env)


if __name__ == "__main__":
    unittest.main()
