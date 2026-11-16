#!/usr/bin/env python3
"""Real local advertisements/objects and mocked authenticated Agh service DATA.

No Git/provider is faked and no GitHub request is made by these controls.
The existing three lane suites exercise the same shell helper in their real
throwaway repository subject tests. This is reader qualification, not proof.
"""
import json
import importlib.util
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
import zlib
from unittest import mock


SCRIPTS = Path(__file__).resolve().parents[1]
HELPER = SCRIPTS / "lib/push_destination.sh"

# Reuse the already maintained real-selector owner controls, specializing
# only the exact input/module population. Loading their class runs no tests.
_owner_spec = importlib.util.spec_from_file_location(
    "push_destination_owner_controls", SCRIPTS / "tests/trust_soundness_corpus_test.py",
)
owner_controls = importlib.util.module_from_spec(_owner_spec)
_owner_spec.loader.exec_module(owner_controls)


class SourceOwnership(owner_controls.SelectorOwnership):
    module = "scripts.tests.push_destination_test"
    paths = ("scripts/lib/push_destination.sh", "scripts/lib/remote_tips.py",
             "scripts/tests/push_destination_test.py")
    neighbours = ("scripts/lib/push_destination-extra.sh", "scripts/tests/push_destination_extra_test.py")

    shared_modules = (
        "scripts.tests.remote_tips_agh_test", "scripts.tests.remote_tips_shallow_test",
        "scripts.tests.remote_tips_process_test", "scripts.tests.remote_tips_advertisement_test",
    )
    # Rows gates/land.toml lists after this module for remote_tips.py (the
    # owner-routed source transport control, registered 2026-11-15).
    trailing_modules = ("scripts.tests.github_source_transport_test",)

    def expected_modules(self, paths):
        shared = (*self.shared_modules, *self.trailing_modules) if "scripts/lib/remote_tips.py" in paths else ()
        return sorted({self.module, *shared})

    def test_each_exact_reader_input_selects_the_fresh_control_module(self):
        for paths in [(path,) for path in self.paths] + [self.paths]:
            with self.subTest(paths=paths):
                graph, selected = self.changed(paths)
                expected = self.expected_modules(paths)
                self.assertEqual(self.selection.validation_test_modules(paths), expected)
                scoped = self.development.scope(graph, selected)
                self.assertFalse(scoped.errors)
                self.assertEqual(scoped.tests, expected)
                self.assertTrue(self.development.has_declared_source_ownership(graph.index, paths))
                leg, = self.gate.development_legs(graph, selected, [], 1)
                self.assertEqual(leg.id, "development-validation-tests")
                self.assertEqual(leg.command, [sys.executable, "scripts/land_gate.py",
                                               "validation-tests", *expected])
                self.assertTrue(leg.force_run)
                self.assertFalse(leg.cache_members)

    def test_full_script_diagnostics_stay_global_and_exact_readme_has_a_validation_owner(self):
        graph, _ = self.changed(self.paths)
        for path in self.paths:
            with self.subTest(path=path):
                with mock.patch.dict(self.selection.VALIDATION_TEST_SUBJECTS, clear=True):
                    ordinary = self.selection.classify(graph, path)
                self.assertEqual(self.selection.classify(graph, path), ordinary)
                if path == "scripts/lib/remote_tips.py":
                    self.assertNotIn(path, self.selection.VALIDATION_TEST_SUBJECTS)
                    self.assertEqual(self.selection.VALIDATION_PROGRAM_TESTS[path],
                                     (*self.shared_modules, self.module, *self.trailing_modules))
                    self.assertEqual(ordinary[0], "validation")
                else:
                    self.assertEqual(self.selection.VALIDATION_TEST_SUBJECTS[path], (self.module,))
                    self.assertNotIn(path, self.selection.VALIDATION_PROGRAM_TESTS)
                    self.assertEqual(ordinary[0], "everything")
                    self.assertTrue(self.selection.select(graph, self.base, [path]).everything)


def embedded_reader():
    text = HELPER.read_text()
    code = text.split("<<'TRUST_DESTINATION_PY'\n", 1)[1].split("\nTRUST_DESTINATION_PY\n", 1)[0]
    namespace = {"__name__": "push_destination_embedded_test"}
    exec(compile(code, str(HELPER) + ":TRUST_DESTINATION_PY", "exec"), namespace)
    return namespace


class DestinationRefs(unittest.TestCase):
    def test_ssh_options_are_scoped_only_to_explicit_non_github_advertisement(self):
        namespace = embedded_reader()
        supplied = {"GIT_SSH": "/explicit/ssh", "GIT_SSH_COMMAND": "ssh -o BatchMode=yes",
                    "GIT_SSH_VARIANT": "ssh", "GIT_OBJECT_DIRECTORY": "/foreign/objects",
                    "GIT_CONFIG_COUNT": "1", "GIT_CONFIG_KEY_0": "core.hooksPath",
                    "GIT_CONFIG_VALUE_0": "/foreign/hooks"}
        with mock.patch.dict(os.environ, supplied), mock.patch.object(subprocess, "run") as run:
            for advertisement in (False, True):
                namespace["git_read"]("ls-remote", "--refs", "--", "ssh://example.invalid/repo",
                                      ssh_advertisement=advertisement)
                env = run.call_args.kwargs["env"]
                for name in ("GIT_SSH", "GIT_SSH_COMMAND", "GIT_SSH_VARIANT"):
                    self.assertEqual(env.get(name), supplied[name] if advertisement else None)
                for name in ("GIT_OBJECT_DIRECTORY", "GIT_CONFIG_COUNT", "GIT_CONFIG_KEY_0",
                             "GIT_CONFIG_VALUE_0"):
                    self.assertNotIn(name, env)
                self.assertEqual(env["GIT_NO_LAZY_FETCH"], "1")
                self.assertEqual(env["GIT_NO_REPLACE_OBJECTS"], "1")

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="push-destination-controls-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.repo, self.remote = self.root / "repo", self.root / "destination.git"
        self.env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
        self.env.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull)
        environment = mock.patch.dict(os.environ, self.env, clear=True)
        environment.start()
        self.addCleanup(environment.stop)
        self.git("init", "-q", "-b", "main", str(self.repo))
        self.git("init", "-q", "--bare", "-b", "main", str(self.remote))
        for name, value in (("user.name", "Test"), ("user.email", "test@example.invalid"),
                            ("commit.gpgsign", "false"), ("tag.gpgsign", "false")):
            self.git("-C", str(self.repo), "config", name, value)
        (self.repo / "source").write_text("genuine local fixture source\n")
        self.git("-C", str(self.repo), "add", "source")
        self.git("-C", str(self.repo), "commit", "-qm", "local fixture")
        self.commit = self.git("-C", str(self.repo), "rev-parse", "HEAD")
        self.git("-C", str(self.repo), "tag", "-a", "local-tag", "-m", "actual tag")
        self.tag = self.git("-C", str(self.repo), "rev-parse", "local-tag")
        self.git("-C", str(self.repo), "push", "-q", str(self.remote), "main", "refs/tags/local-tag")
        previous = Path.cwd()
        os.chdir(self.repo)
        self.addCleanup(os.chdir, previous)
        paths = mock.patch.object(sys, "path", [str(SCRIPTS / "lib"), *sys.path])
        paths.start()
        self.addCleanup(paths.stop)
        import remote_tips
        self.reader = remote_tips
        self.actual_run = remote_tips._run
        self.core = embedded_reader()
        self.calls = []
        self.api_exit, self.route_exit = 0, 0
        self.route = {"decision": {"send": {"profile": "private-owner-DATA"}}}
        self.entries = [
            {"ref": "refs/heads/main", "oid": self.commit},
            {"ref": "refs/tags/local-tag", "oid": self.tag},
        ]
        self.response = None

    def git(self, *args):
        return subprocess.check_output(["git", *args], env=self.env, text=True,
                                       stderr=subprocess.DEVNULL).strip()

    def service(self, args, **kwargs):
        if args[0] != "agh":
            return self.actual_run(args, **kwargs)
        self.calls.append(list(args))
        if args[1] == "whoami":
            self.assertEqual(args[2:], ["--for", "Owner/Private", "--op", "read"])
            return subprocess.CompletedProcess(args, self.route_exit, json.dumps(self.route), "")
        self.assertEqual(args[:4], ["agh", "repo", "refs", "Owner/Private"])
        self.assertNotIn("--as", args, "native service retains its routed profile")
        directory = kwargs.get("cwd")
        self.assertIsNotNone(directory)
        self.assertNotEqual(Path(directory), self.repo)
        self.assertEqual(Path(directory).stat().st_mode & 0o777, 0o700)
        self.assertFalse((Path(directory) / ".git").exists())
        self.assertIn("--no-anonymous-api", args)
        self.assertNotIn("--anonymous", args)
        data = json.dumps(self.entries) if self.response is None else self.response
        return subprocess.CompletedProcess(args, self.api_exit, data,
            '{"error":{"kind":"rate_limited","sub":"pre_refused","reset":1794648849}}'
            if self.api_exit == 11 else "service DATA refusal")

    def github(self, url="https://github.com/Owner/Private.git"):
        with mock.patch.object(self.reader, "_run", side_effect=self.service):
            return self.core["advertised_refs"](url, SCRIPTS / "lib")

    def test_real_bare_refs_peel_actual_tag_and_never_fetch_missing_commit(self):
        other = self.root / "other"
        self.git("clone", "-q", str(self.remote), str(other))
        for name, value in (("user.name", "Test"), ("user.email", "test@example.invalid"),
                            ("commit.gpgsign", "false")):
            self.git("-C", str(other), "config", name, value)
        (other / "source").write_text("only the real destination has this child\n")
        self.git("-C", str(other), "commit", "-qam", "unacquired child")
        missing = self.git("-C", str(other), "rev-parse", "HEAD")
        self.git("-C", str(other), "push", "-q", "origin", "HEAD:refs/heads/unacquired")
        tree = self.git("-C", str(self.repo), "rev-parse", "HEAD^{tree}")
        self.git("--git-dir", str(self.remote), "update-ref", "refs/tags/tree", tree)
        def absent():
            return subprocess.run(["git", "cat-file", "-e", missing], cwd=self.repo,
                                  env=self.env, stdout=subprocess.PIPE, stderr=subprocess.PIPE).returncode != 0
        self.assertTrue(absent())
        result = subprocess.run(["bash", str(HELPER), str(self.remote)], cwd=self.repo,
                                env=self.env, text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(set(result.stdout.splitlines()), {
            f"{self.commit} refs/heads/main", f"{self.commit} refs/tags/local-tag",
        })
        self.assertTrue(absent(), "advertisement must not acquire missing original objects")

    def test_private_github_uses_native_owner_route_complete_refs_and_actual_objects(self):
        result = self.github()
        self.assertEqual(set(result.splitlines()), {
            f"{self.commit}\trefs/heads/main", f"{self.commit}\trefs/tags/local-tag",
        })
        self.assertEqual(len(self.calls), 2)

    def test_named_remote_uses_actual_push_url_not_its_local_fetch_url(self):
        self.git("remote", "add", "publish", str(self.remote))
        self.git("remote", "set-url", "--push", "publish", "https://GitHub.com/Owner/Private.git")
        self.assertEqual(self.github("publish"), self.github())
        self.git("remote", "set-url", "--add", "--push", "publish", str(self.remote))
        with self.assertRaisesRegex(ValueError, "exactly one URL"):
            self.github("publish")

    def test_github_ssh_and_named_push_rewrite_use_same_repository(self):
        self.assertEqual(self.github("git@github.com:Owner/Private.git"), self.github())
        self.assertEqual(self.github("ssh://git@github.com/Owner/Private.git"), self.github())
        self.git("config", "url.https://github.com/.pushInsteadOf", "private:")
        self.git("remote", "add", "publish", "private:Owner/Private.git")
        self.assertEqual(self.github("publish"), self.github())
        with self.assertRaisesRegex(ValueError, "literal pushInsteadOf"):
            self.github("private:Owner/Private.git")

    def test_failed_private_routing_or_api_never_uses_raw_or_anonymous_fallback(self):
        for route_exit, route, api_exit in [
            (4, self.route, 0), (0, {}, 0), (0, self.route, 4), (0, self.route, 11), (0, self.route, 14),
        ]:
            with self.subTest(route_exit=route_exit, api_exit=api_exit, route=route):
                self.route_exit, self.route, self.api_exit = route_exit, route, api_exit
                with self.assertRaisesRegex(ValueError, "authenticated Agh"):
                    self.github()

    def test_malformed_duplicate_or_nonfinite_collection_refuses_whole_advertisement(self):
        good = self.entries[0]
        for invalid in [None, {}, [good, good],
                        [{"ref": "refs/heads/bad.lock", "oid": self.commit}],
                        [{"ref": "refs/heads/main", "oid": "0" * 40}],
                        [{"ref": "refs/heads/main", "object": {"sha": self.commit, "type": "commit"}}],
                        [good, {"ref": "refs/tags/bad", "oid": []}]]:
            with self.subTest(invalid=invalid):
                self.response = json.dumps(invalid)
                with self.assertRaises(ValueError):
                    self.github()
        for malformed in ['[{"ref":"refs/heads/a","ref":"refs/heads/b"}]',
                          json.dumps([good])[:-1],
                          '[{"ref":"refs/heads/a","extra":NaN}]',
                          '[{"ref":"refs/heads/a","extra":1e309}]']:
            with self.subTest(malformed=malformed):
                self.response = malformed
                with self.assertRaises(ValueError):
                    self.github()

    def test_native_quota_refusal_preserves_raw_reset_without_rest_or_fallback(self):
        self.api_exit = 11
        with self.assertRaisesRegex(ValueError, "rate_limited.*1794648849"):
            self.github()
        self.assertEqual([call[1:3] for call in self.calls], [["whoami", "--for"], ["repo", "refs"]])

    def test_fresh_native_inventory_never_trusts_push_rows_or_stale_local_refs(self):
        with mock.patch.dict(os.environ, {"TRUST_PUSHED_REFS": "forged", "TRUST_PUSH_REMOTE": "forged"}):
            first = self.github()
            self.entries = []
            second = self.github()
        self.assertTrue(first)
        self.assertEqual(second, "")
        self.assertEqual(sum(call[1:3] == ["repo", "refs"] for call in self.calls), 2)

    def test_actual_odb_borrow_ignores_caller_git_overrides_and_hooks(self):
        self.git("config", "core.hooksPath", "scripts/hooks")
        config = (self.repo / ".git/config").read_bytes()
        with mock.patch.dict(os.environ, {"GIT_DIR": str(self.remote),
                                          "GIT_OBJECT_DIRECTORY": str(self.remote / "objects")}):
            result = self.github()
        self.assertIn(f"{self.commit}\trefs/heads/main", result)
        self.assertEqual((self.repo / ".git/config").read_bytes(), config)
        self.assertFalse((self.repo / ".git/objects/info/alternates").exists())

    def test_main_disappearing_after_authentication_is_not_judged(self):
        original = self.reader.remote_refs
        def disappear(*args, **kwargs):
            done = original(*args, **kwargs)
            self.assertEqual(done.returncode, 0, done.stderr)
            (self.repo / ".git/objects" / self.commit[:2] / self.commit[2:]).unlink()
            return done
        with mock.patch.object(self.reader, "remote_refs", side_effect=disappear):
            with self.assertRaisesRegex(ValueError, "main original commit is unavailable; NOT JUDGED"):
                self.github()

    def test_corrupt_original_tag_bytes_cannot_supply_exclusion_credit(self):
        path = self.repo / ".git/objects" / self.tag[:2] / self.tag[2:]
        body = zlib.decompress(path.read_bytes())
        path.chmod(0o600)  # Deliberately corrupt this owned loose-object fixture.
        path.write_bytes(zlib.compress(body.replace(b"actual tag", b"forged tag")))
        with self.assertRaisesRegex(ValueError, "original object bytes are unreadable or corrupt"):
            self.github()

    def test_changed_actual_odb_refuses_after_original_byte_read(self):
        original = self.actual_run
        changed = []
        def replace(args, **kwargs):
            done = original(args, **kwargs)
            if kwargs.get("binary") and kwargs.get("isolate_git_config") and not changed:
                objects = self.repo / ".git/objects"
                objects.rename(self.repo / ".git/old-objects")
                objects.mkdir()
                changed.append(True)
            return done
        self.actual_run = replace
        with self.assertRaisesRegex(ValueError, "original object directory changed"):
            self.github()
        self.assertEqual(changed, [True])

    def test_unsupported_github_authority_syntax_refuses_before_service(self):
        for url in ["https://user@github.com/Owner/Private.git",
                    "https://github.com/Owner/Private.git?other=repo",
                    "ssh://different@github.com/Owner/Private.git",
                    "http://github.com/Owner/Private.git",
                    "https://git\thub.com/Owner/Private.git",
                    "https://github.com/Owner/Private.git\t"]:
            with self.subTest(url=url), self.assertRaises(ValueError):
                self.github(url)
        self.assertEqual(self.calls, [])


class ExistingLaneSubjects(unittest.TestCase):
    """Existing local-Git subject tests; these scripts launch no Rust."""
    def check(self, name):
        # A stop for a script that hangs, not a speed requirement: at load 66 on an 18-core host
        # the two longest subjects took 182 s and 224 s and passed (2026-11-14).
        result = subprocess.run(["bash", str(SCRIPTS / "tests" / name)],
                                cwd=SCRIPTS.parent, text=True, capture_output=True, timeout=1800)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_cfg_test_caller_skew_subjects(self):
        self.check("check_cfg_test_caller_skew_test.sh")

    def test_revert_rationale_subjects(self):
        self.check("check_revert_rationale_test.sh")

    def test_measurement_provenance_subjects(self):
        self.check("check_measurement_provenance_test.sh")


if __name__ == "__main__":
    unittest.main()
