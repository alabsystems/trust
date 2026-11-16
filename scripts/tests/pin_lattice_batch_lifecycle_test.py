#!/usr/bin/env python3
"""Owned Git subprocess pipes must close even after their child has exited."""

import importlib.util
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock


SCRIPT = Path(__file__).resolve().parents[1] / "check_first_party_pin_lattice.py"
SPEC = importlib.util.spec_from_file_location("pin_lattice_batch_lifecycle", SCRIPT)
lattice = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = lattice
with mock.patch("atexit.register") as register_exit:
    SPEC.loader.exec_module(lattice)
EXIT_CLEANUP = register_exit.call_args.args[0]


class BatchLifecycleTests(unittest.TestCase):
    def setUp(self):
        batches = mock.patch.object(lattice, "_OPEN_BATCHES", [])
        batches.start()
        self.addCleanup(batches.stop)
        scratch = Path(tempfile.gettempdir()) / ".ubd"
        scratch.mkdir(exist_ok=True)
        temp = tempfile.TemporaryDirectory(prefix="pin-lattice-pipes-", dir=scratch)
        self.addCleanup(temp.cleanup)
        self.repo = Path(temp.name) / "objects.git"
        env = lattice._git_env()
        env.update(GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1")
        subprocess.run(["git", "init", "--bare", "-q", str(self.repo)],
                       env=env, check=True, capture_output=True)
        self.payload = b"the actual object read through the owned Git pipe\n"
        self.blob = subprocess.run(
            ["git", "--git-dir", str(self.repo), "hash-object", "-w", "--stdin"],
            input=self.payload, env=env, check=True, capture_output=True,
        ).stdout.decode().strip()
        self.batch = lattice._Batch(self.repo)
        self.addCleanup(self.batch.close)
        self.assertEqual(self.batch.read(self.blob), ("blob", self.payload))

    def assertPipesReleased(self, stdin_fd, stdout_fd):
        self.assertTrue(self.batch.proc.stdin.closed)
        self.assertTrue(self.batch.proc.stdout.closed)
        for fd in (stdin_fd, stdout_fd):
            with self.assertRaises(OSError):
                os.fstat(fd)
        self.assertEqual(self.batch.proc.poll(), 0)

    def test_live_child_pipes_close_and_cleanup_is_idempotent(self):
        stdin_fd = self.batch.proc.stdin.fileno()
        stdout_fd = self.batch.proc.stdout.fileno()
        self.assertIsNone(self.batch.proc.poll())
        self.batch.close()
        self.assertPipesReleased(stdin_fd, stdout_fd)
        self.batch.close()
        self.assertPipesReleased(stdin_fd, stdout_fd)

    def test_already_exited_child_still_releases_its_output_pipe(self):
        stdin_fd = self.batch.proc.stdin.fileno()
        stdout_fd = self.batch.proc.stdout.fileno()
        self.batch.proc.stdin.close()
        self.assertEqual(self.batch.proc.wait(timeout=5), 0)
        self.assertFalse(self.batch.proc.stdout.closed)
        self.batch.close()
        self.assertPipesReleased(stdin_fd, stdout_fd)

    def test_exit_cleanup_reaps_later_reader_after_a_real_broken_pipe(self):
        later = lattice._Batch(self.repo)
        self.addCleanup(later.close)
        self.assertEqual(later.read(self.blob), ("blob", self.payload))
        later_fds = (later.proc.stdin.fileno(), later.proc.stdout.fileno())
        # Leave bytes buffered until close, then remove the real pipe reader.
        self.batch.proc.stdin.write(b"pending unflushed request")
        self.batch.proc.terminate()
        self.batch.proc.wait(timeout=5)
        with self.assertRaises(ExceptionGroup) as raised:
            EXIT_CLEANUP()
        self.assertEqual(len(raised.exception.exceptions), 1)
        self.assertIsInstance(raised.exception.exceptions[0], BrokenPipeError)
        self.assertTrue(later.proc.stdin.closed)
        self.assertTrue(later.proc.stdout.closed)
        self.assertEqual(later.proc.poll(), 0)
        for fd in later_fds:
            with self.assertRaises(OSError):
                os.fstat(fd)
        self.assertEqual(lattice._OPEN_BATCHES, [])

    def test_scoped_cleanup_keeps_earlier_reader_and_reports_each_failure(self):
        failed = [lattice._Batch(self.repo), lattice._Batch(self.repo)]
        for batch in failed:
            self.addCleanup(batch.close)
            self.assertEqual(batch.read(self.blob), ("blob", self.payload))
            batch.proc.stdin.write(b"pending unflushed request")
            batch.proc.terminate()
            batch.proc.wait(timeout=5)
        with self.assertRaises(ExceptionGroup) as raised:
            lattice._close_batches(1)
        self.assertEqual(len(raised.exception.exceptions), 2)
        self.assertTrue(all(isinstance(error, BrokenPipeError)
                            for error in raised.exception.exceptions))
        self.assertEqual(lattice._OPEN_BATCHES, [self.batch])
        self.assertIsNone(self.batch.proc.poll())
        self.assertEqual(self.batch.read(self.blob), ("blob", self.payload))
        for batch in failed:
            self.assertTrue(batch.proc.stdin.closed)
            self.assertTrue(batch.proc.stdout.closed)
            self.assertIsNotNone(batch.proc.poll())
        lattice._close_batches()
        self.assertEqual(lattice._OPEN_BATCHES, [])
        EXIT_CLEANUP()

    def test_git_child_dying_during_a_blob_refuses_the_partial_response(self):
        payload = b"[workspace]\n" + b"# padding before dependencies\n" * 65536
        blob = subprocess.run(
            ["git", "--git-dir", str(self.repo), "hash-object", "-w", "--stdin"],
            input=payload, env=lattice._git_env(), check=True, capture_output=True,
        ).stdout.decode().strip()
        stdout = self.batch.proc.stdout
        proc = self.batch.proc

        class StopAfterRealHeader:
            def read(self, size=-1):
                data = stdout.read(size)
                if size == 1 and data == b"\0":
                    proc.terminate()
                    proc.wait(timeout=5)
                return data

            def readline(self):
                header = stdout.readline()
                # The real Git child cannot fit this blob into its pipe.
                # Kill only this owned child after its actual header arrives.
                proc.terminate()
                proc.wait(timeout=5)
                return header

            def __getattr__(self, name):
                return getattr(stdout, name)

        with mock.patch.object(proc, "stdout", StopAfterRealHeader()):
            with self.assertRaisesRegex(lattice.GitError, "truncated"):
                self.batch.read(blob)

    def test_newline_paths_and_missing_queries_keep_the_batch_in_sync(self):
        env = lattice._git_env()
        env.update(GIT_AUTHOR_NAME="Batch Test", GIT_AUTHOR_EMAIL="batch@example.invalid",
                   GIT_COMMITTER_NAME="Batch Test", GIT_COMMITTER_EMAIL="batch@example.invalid")

        def git(*args, data):
            return subprocess.run(["git", "--git-dir", str(self.repo), *args],
                                  input=data, env=env, check=True, capture_output=True).stdout.decode().strip()

        leaf = git("mktree", "-z", data=f"100644 blob {self.blob}\tCargo.toml\0".encode())
        tree = git("mktree", "-z", data=f"040000 tree {leaf}\tnew\nline\0".encode())
        commit = git("commit-tree", tree, data=b"newline path fixture\n")
        self.assertEqual(self.batch.read(f"{commit}:new\nline/Cargo.toml"), ("blob", self.payload))
        self.assertIsNone(self.batch.read(f"{commit}:new\nline/missing.toml"))
        self.assertEqual(self.batch.read(self.blob), ("blob", self.payload))

    def test_empty_and_binary_blobs_round_trip_exactly(self):
        for payload in (b"", b"\0binary\xff\n\0"):
            with self.subTest(payload=payload):
                blob = subprocess.run(
                    ["git", "--git-dir", str(self.repo), "hash-object", "-w", "--stdin"],
                    input=payload, env=lattice._git_env(), check=True, capture_output=True,
                ).stdout.decode().strip()
                self.assertEqual(self.batch.read(blob), ("blob", payload))

    def test_nul_query_is_refused_without_touching_the_next_response(self):
        with self.assertRaisesRegex(lattice.GitError, "NUL"):
            self.batch.read("missing\0" + self.blob)
        self.assertEqual(self.batch.read(self.blob), ("blob", self.payload))


if __name__ == "__main__":
    unittest.main()
