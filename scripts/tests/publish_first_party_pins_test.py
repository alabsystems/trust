#!/usr/bin/env python3
"""Regression tests for publish/transforms.sh T5 (first-party/PINS.txt).

RL-129: trust's root workspace names clean-reflect by path
(`first-party/clean/crates/clean-reflect`), and clean's bootstrap projection
omits crates/clean-reflect from its publication. Nothing said so until T5c's
re-lock ("no matching package named `clean-reflect` found"), long after T5 had
written a PINS.txt that could not resolve. T5 now runs the engine's
check_sibling_publication_paths on the export with the receipts it projected,
and refuses with `[omits]` before PINS.txt is written.

The T5 block runs exactly as the engine runs it (its `pub-python` heredoc, cut
from transforms.sh), against the real engine module (publication's
bin/pub_projection.py, found where publish/publish.sh finds the engine). The
fixture engine directory holds that module, the engine's pub-python, a ledger
and a registry, and one test double: the GitHub transport (pub_github), which
serves the fixture's public clean repository for its alabsystems URL and logs
each fetch, so nothing reaches the network.
"""
from __future__ import annotations

import hashlib
import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
TRANSFORMS = REPO / "publish" / "transforms.sh"
# publish/publish.sh: ENGINE="${PUBLICATION_DIR:-$HERE/../publication}"
ENGINE = Path(os.environ.get("PUBLICATION_DIR") or REPO.parent / "publication")
T5_START = '"$ENGINE_DIR/bin/pub-python" - "$ROOT" "$ENGINE_DIR" "$EXPORT" <<\'PY\''

PUBLIC_URL = "https://github.com/alabsystems/clean.git"
GIT_ENV = {
    "GIT_AUTHOR_NAME": "T5 Test",
    "GIT_AUTHOR_EMAIL": "t5-test@example.invalid",
    "GIT_COMMITTER_NAME": "T5 Test",
    "GIT_COMMITTER_EMAIL": "t5-test@example.invalid",
    "GIT_CONFIG_GLOBAL": os.devnull,
    "GIT_CONFIG_NOSYSTEM": "1",
}

# The consumer as T5 sees it: trust's shape, a workspace dependency by path into
# first-party/clean, and the first-party/trust self-symlink.
EXPORT_FILES = {
    "Cargo.toml": (
        '[workspace]\nmembers = ["crates/app"]\nexclude = ["first-party/clean"]\n\n'
        "[workspace.dependencies]\n"
        'clean-kernel = { path = "first-party/clean/crates/clean-kernel" }\n'
        'clean-reflect = { path = "first-party/clean/crates/clean-reflect" }\n'),
    "crates/app/Cargo.toml": (
        '[package]\nname = "app"\nversion = "0.1.0"\n\n'
        "[dependencies]\nclean-reflect = { workspace = true }\n"),
}

TRANSPORT_DOUBLE = '''\
"""Test double for the engine's GitHub transport: one anonymous fetch per call,
served from the local repository transport.json maps the public URL to."""
import json
import os
import subprocess
from pathlib import Path

_CONFIG = json.loads((Path(__file__).resolve().parent / "transport.json").read_text())


def run_git(argv, *, cwd=None, timeout=600, anonymous=False, env=None):
    words = [str(word) for word in argv]
    urls = [word for word in words if word.startswith("https://")]
    with open(_CONFIG["log"], "a", encoding="utf-8") as log:
        log.write(json.dumps({"argv": words, "anonymous": anonymous}) + "\\n")
    if words[:1] != ["git"] or len(urls) != 1 or not anonymous:
        return 2, "", "transport double: expected one anonymous public fetch"
    local = _CONFIG["remotes"].get(urls[0])
    if local is None:
        return 128, "", f"transport double: no fixture repository for {urls[0]}"
    words[words.index(urls[0])] = local
    plain = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
    proc = subprocess.run(words, cwd=cwd, env=plain, capture_output=True, text=True,
                          timeout=timeout)
    return proc.returncode, proc.stdout, proc.stderr
'''


def git(repo: Path, *args: str) -> str:
    return subprocess.run(["git", "-C", str(repo), *args], check=True, capture_output=True,
                          text=True, env={**os.environ, **GIT_ENV}).stdout.strip()


def sha1(seed: str) -> str:
    return hashlib.sha1(seed.encode()).hexdigest()


def t5_block() -> str:
    """The T5 command and its heredoc, as transforms.sh holds them."""
    lines = TRANSFORMS.read_text(encoding="utf-8").split("\n")
    starts = [i for i, line in enumerate(lines) if line == T5_START]
    if len(starts) != 1:
        raise AssertionError(f"{TRANSFORMS}: expected one T5 pub-python heredoc, found {len(starts)}")
    end = lines.index("PY", starts[0] + 1)
    return "\n".join(lines[starts[0]:end + 1]) + "\n"


# publish/ is not part of the public snapshot, so the suite skips there. In the
# private tree publish/ exists, and a missing transforms.sh must fail, not skip.
@unittest.skipUnless((REPO / "publish").is_dir(), "publish/ is not part of the public snapshot")
class T5SiblingPublicationPathTests(unittest.TestCase):
    def setUp(self) -> None:
        if not (ENGINE / "bin" / "pub_projection.py").is_file():
            self.skipTest(f"no publication engine at {ENGINE} (set PUBLICATION_DIR, as "
                          "publish/publish.sh reads it); T5 cannot run without it")
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.base = Path(self.tmp.name)

        # clean's development history: the pin c1, then the published source c2.
        self.dev = self.base / "clean-dev"
        self.dev.mkdir()
        git(self.dev, "init", "-q", "-b", "main")
        self.c1 = self.commit_clean(self.dev, "0.9.0", ("clean-kernel", "clean-reflect"))
        self.c2 = self.commit_clean(self.dev, "0.9.1", ("clean-kernel", "clean-reflect"))

        # trust's captured commit: first-party/clean pinned at c1.
        self.root = self.base / "trust"
        self.root.mkdir()
        git(self.root, "init", "-q", "-b", "main")
        (self.root / "Cargo.toml").write_text(EXPORT_FILES["Cargo.toml"], encoding="utf-8")
        (self.root / "first-party").mkdir()
        (self.root / "first-party" / "trust").symlink_to("..")
        git(self.root, "add", "-A")
        git(self.root, "update-index", "--add", "--cacheinfo", f"160000,{self.c1},first-party/clean")
        git(self.root, "commit", "-q", "-m", "pin clean at c1")
        self.captured = git(self.root, "rev-parse", "HEAD")

        self.export = self.base / "export"
        for rel, text in EXPORT_FILES.items():
            (self.export / rel).parent.mkdir(parents=True, exist_ok=True)
            (self.export / rel).write_text(text, encoding="utf-8")
        (self.export / "first-party").mkdir()
        (self.export / "first-party" / "trust").symlink_to("..")

    def commit_clean(self, repo: Path, version: str, crates: tuple[str, ...]) -> str:
        (repo / "Cargo.toml").write_text(
            f'[workspace]\nmembers = ["crates/*"]\n\n[workspace.package]\nversion = "{version}"\n',
            encoding="utf-8")
        for crate in crates:
            (repo / "crates" / crate).mkdir(parents=True, exist_ok=True)
            (repo / "crates" / crate / "Cargo.toml").write_text(
                f'[package]\nname = "{crate}"\nversion.workspace = true\n', encoding="utf-8")
        git(repo, "add", "-A")
        git(repo, "commit", "-q", "-m", f"clean {version}")
        return git(repo, "rev-parse", "HEAD")

    def run_t5(self, *published: str) -> tuple[subprocess.CompletedProcess[str], str, list[dict]]:
        """T5 against a clean publication (source c2) holding `published`."""
        public = self.base / "clean-public"
        public.mkdir()
        git(public, "init", "-q", "-b", "main")
        release = self.commit_clean(public, "0.9.1", published)
        tree = git(public, "rev-parse", "HEAD^{tree}")

        engine = self.base / "engine"
        (engine / "bin").mkdir(parents=True)
        (engine / "registry").mkdir()
        for name in ("pub-python", "pub_projection.py"):
            (engine / "bin" / name).symlink_to(ENGINE / "bin" / name)
        (engine / "bin" / "pub_github.py").write_text(TRANSPORT_DOUBLE, encoding="utf-8")
        log = self.base / "transport.log"
        (engine / "bin" / "transport.json").write_text(json.dumps(
            {"remotes": {PUBLIC_URL: str(public)}, "log": str(log)}), encoding="utf-8")
        (engine / "registry" / "repos.toml").write_text(
            f"[repos.clean]\npath = {json.dumps(str(self.dev))}\n", encoding="utf-8")
        (engine / "mappings.json").write_text(json.dumps({"schema": 1, "mappings": {"clean": {
            self.c2: {
                "engine_sha": sha1("engine"),
                "export_tree": tree,
                "policy_sha": hashlib.sha256(b"policy").hexdigest(),
                "release_rev": release,
                "release_tree": tree,
                "release_url": "git@github.com:alabsystems/clean.git",
                "staging_rev": sha1("staging"),
                "verified_at": "2026-11-15T00:00:00Z",
            }}}}), encoding="utf-8")

        env = {k: v for k, v in os.environ.items()
               if not k.startswith("GIT_") and k != "PUBLISH_DEPENDENCY_CHECKOUTS"}
        env.update(ROOT=str(self.root), ENGINE_DIR=str(engine), EXPORT=str(self.export),
                   CAPTURED_COMMIT=self.captured)
        result = subprocess.run(["bash", "-c", t5_block()], capture_output=True, text=True,
                                env=env, timeout=300)
        calls = ([json.loads(line) for line in log.read_text(encoding="utf-8").splitlines()]
                 if log.exists() else [])
        return result, release, calls

    def assert_one_anonymous_public_fetch(self, calls: list[dict], release: str) -> None:
        self.assertEqual(len(calls), 1, calls)
        self.assertTrue(calls[0]["anonymous"], calls)
        self.assertIn(PUBLIC_URL, calls[0]["argv"])
        self.assertTrue(any(word.startswith(f"{release}:") for word in calls[0]["argv"]), calls)

    def test_a_path_into_a_crate_the_sibling_publication_omits_refuses_with_omits(self) -> None:
        result, release, calls = self.run_t5("clean-kernel")  # the bootstrap shape: no clean-reflect
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        refusal = result.stderr
        self.assertIn("transform T5: [omits] ", refusal)
        self.assertIn("Cargo.toml workspace.dependencies.clean-reflect.path names "
                      "first-party/clean/crates/clean-reflect", refusal)
        self.assertIn(f"clean 0.9.1 (release {release[:12]}) omits crates/clean-reflect", refusal)
        self.assertNotIn("crates/clean-kernel", refusal)  # a held path is no finding
        self.assertEqual(refusal.strip().splitlines()[-1],
                         f"blocked by clean 0.9.1 (release {release[:12]}): omits crates/clean-reflect")
        self.assertFalse((self.export / "first-party" / "PINS.txt").exists(),
                         "T5 wrote PINS.txt although a sibling path is missing")
        self.assert_one_anonymous_public_fetch(calls, release)

    def test_paths_the_sibling_publication_holds_pass_and_pins_are_written(self) -> None:
        result, release, calls = self.run_t5("clean-kernel", "clean-reflect")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn(f"==   clean: pin {self.c1[:12]} -> release {release[:12]} "
                      f"(source {self.c2[:12]}, forward 1 commit(s))", result.stdout)
        self.assertIn("== T5: 2 manifest path(s) into 1 first-party sibling(s) exist in their "
                      "mapped publications (clean 0.9.1)", result.stdout)
        pins = (self.export / "first-party" / "PINS.txt").read_text(encoding="utf-8")
        self.assertEqual([line for line in pins.splitlines() if not line.startswith("#")],
                         [f"clean {PUBLIC_URL} {release}"])
        self.assertIn(self.captured, pins)
        self.assert_one_anonymous_public_fetch(calls, release)


if __name__ == "__main__":
    unittest.main()
