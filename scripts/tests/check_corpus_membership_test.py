"""Tests for scripts/check_corpus_membership.py (CORPUS-MEMBERSHIP-AT-LANDING-1).

The row implements each corpus membership rule once, in Python. These tests
tie that rule to the rule each manifest's header documents: the REGENERATE
command, read from the header, runs in bash on the same tree as the Python rule
(this checkout's, and adversarial trees built here), and the two must select
the same set. The Rust membership tests compare the Rust rule against the body
that command printed, so the three cannot drift apart silently. The rest pins
what the row refuses where a git-object reading cannot answer for a checkout,
the manifest as the Rust tests read it, the CLI's push contract (keys,
`FINDINGS: complete`, SKIPPED, exit 2) and `--write`. The row as push-rows
grades it (INHERITED vs FAIL) is land_gate_test's
CorpusMembershipInheritedRedTests.

    python3 -B scripts/tests/check_corpus_membership_test.py

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""
from __future__ import annotations

import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Tuple
from unittest import mock

REPO = Path(__file__).resolve().parents[2]
SCRIPT = REPO / "scripts" / "check_corpus_membership.py"
sys.path.insert(0, str(REPO / "scripts"))

import check_corpus_membership as ccm  # noqa: E402

JSON, TOML = ccm.CORPORA
CAP = ccm.SIZE_CAP
# Fixture git: no host configuration (core.quotepath and the attributes file
# among it), a fixed identity, and no background maintenance.
ISOLATED = {"GIT_CONFIG_GLOBAL": "/dev/null", "GIT_CONFIG_NOSYSTEM": "1"}
FIXTURE_ENV = {**ISOLATED, "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@t", "GIT_COMMITTER_NAME": "t",
               "GIT_COMMITTER_EMAIL": "t@t", "GIT_CONFIG_COUNT": "1", "GIT_CONFIG_KEY_0": "maintenance.auto",
               "GIT_CONFIG_VALUE_0": "false"}


def clean_env(extra: Optional[Dict[str, str]] = None) -> Dict[str, str]:
    env = {k: v for k, v in os.environ.items() if k not in ccm.GIT_ENV_DROPPED and k != "TRUST_PUSHED_REFS"}
    env.update(extra or {})
    return env


def header(corpus: ccm.Corpus, documented: Optional[str] = None) -> str:
    """A manifest header documenting `documented` (default: the row's rule),
    with the blank lines inside and after it that the real headers have."""
    command = corpus.documented if documented is None else documented
    lines = [f"# {corpus.name} test manifest", "#", ccm.REGENERATE_MARK, "#",
             *("#   " + line for line in command.split("\n")), "#", "", "# A later section.", "#", ""]
    return "\n".join(lines) + "\n"


def manifest(corpus: ccm.Corpus, paths: Iterable[str], documented: Optional[str] = None) -> bytes:
    return (header(corpus, documented) + "".join(p + "\n" for p in sorted(paths))).encode("utf-8")


class Fixture:
    """A git repository in a temp dir: files written to disk and committed, or
    trees built in a scratch index (for names a file system refuses)."""

    def __init__(self, test: unittest.TestCase):
        tmp = tempfile.TemporaryDirectory(prefix="corpus-membership.")
        test.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name).resolve() / "repo"
        self.root.mkdir()
        self.scratch = Path(tmp.name).resolve() / "scratch.index"
        self.blobs: Dict[bytes, str] = {}
        self.git("init", "-q", "-b", "main")

    def git(self, *args: str, stdin: Optional[bytes] = None, index: Optional[Path] = None) -> bytes:
        env = clean_env(FIXTURE_ENV)
        if index is not None:
            env["GIT_INDEX_FILE"] = str(index)
        proc = subprocess.run(["git", "-C", str(self.root), *args], input=stdin, capture_output=True, env=env)
        if proc.returncode != 0:
            raise AssertionError(f"git {args}: {proc.stderr.decode('utf-8', 'replace')}")
        return proc.stdout

    def write(self, rel: str, data: bytes, executable: bool = False) -> None:
        path = self.root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
        if executable:
            path.chmod(0o755)

    def commit_worktree(self, message: str = "fixture") -> str:
        self.git("add", "-A")
        self.git("commit", "-q", "--allow-empty", "-m", message)
        return self.git("rev-parse", "HEAD").decode().strip()

    def blob(self, data: bytes) -> str:
        if data not in self.blobs:
            self.blobs[data] = self.git("hash-object", "-w", "--stdin", stdin=data).decode().strip()
        return self.blobs[data]

    def tree(self, entries: Dict[bytes, Tuple[str, bytes]], parent: Optional[str] = None) -> str:
        """A tree (or, with `parent`, a commit on it) holding `entries`
        {path: (mode, blob bytes | commit sha for 160000)}, built in a scratch
        index so the checkout and its index are never touched."""
        self.scratch.unlink(missing_ok=True)
        if parent:
            self.git("read-tree", parent, index=self.scratch)
        else:
            self.git("read-tree", "--empty", index=self.scratch)
        lines = []
        for path, (mode, data) in entries.items():
            oid = data.decode() if mode == "160000" else self.blob(data)
            lines.append(f"{mode} {oid}\t".encode() + path + b"\0")
        if lines:
            self.git("update-index", "--add", "-z", "--index-info", stdin=b"".join(lines), index=self.scratch)
        tree = self.git("write-tree", index=self.scratch).decode().strip()
        if parent is None:
            return tree
        return self.git("commit-tree", tree, "-p", parent, "-m", "case").decode().strip()


def judge(root: Path, rev: str) -> Dict[str, ccm.Verdict]:
    with mock.patch.dict(os.environ, ISOLATED):
        return {v.corpus.name: v for v in ccm.judge_tree(root, ccm.resolve_tree(root, rev))}


def rule(root: Path, rev: str) -> Dict[str, Tuple[List[str], List[str]]]:
    """{corpus: (members, findings)} of `rev`'s tree under the Python rule."""
    with mock.patch.dict(os.environ, ISOLATED):
        tree = ccm.resolve_tree(root, rev)
        entries = ccm.tree_entries(root, tree)
        capped = [e.path for e in entries if e.path.endswith(b".json")
                  and not e.path.startswith(ccm.EXCLUDED_PREFIXES)]
        attrs = ccm.converting_attributes(root, tree, capped)
        out = {}
        for corpus in ccm.CORPORA:
            members, findings, _notes, _undecided = ccm.members_and_findings(corpus, entries, attrs)
            out[corpus.name] = (members, findings)
        return out


def documented_output(corpus: ccm.Corpus, cwd: Path, env: Optional[Dict[str, str]] = None) -> List[str]:
    """The lines the header's documented command prints in `cwd`."""
    proc = subprocess.run(["bash", "-c", corpus.documented], cwd=cwd, capture_output=True, env=env or clean_env())
    if proc.returncode != 0:
        raise AssertionError(f"{corpus.name}'s documented command failed: {proc.stderr.decode('utf-8', 'replace')}")
    text = proc.stdout.decode("utf-8")
    return [line for line in text.split("\n") if line]


def bsd_stat() -> bool:
    proc = subprocess.run(["stat", "-f", "%z", "/dev/null"], capture_output=True, text=True)
    return proc.returncode == 0 and proc.stdout.strip().isdigit()


class DocumentedRuleTests(unittest.TestCase):
    """The Python rule IS the documented rule: same set, same trees."""

    def test_the_row_applies_the_command_this_checkouts_headers_document(self):
        for corpus in ccm.CORPORA:
            with self.subTest(corpus.name):
                text = (REPO / corpus.manifest).read_text(encoding="utf-8")
                self.assertEqual(ccm.documented_command(text), corpus.documented,
                                 f"{corpus.manifest}'s REGENERATE block is not the rule CORPORA applies")

    def test_rule_selects_what_the_documented_command_prints_on_this_checkout(self):
        moved = subprocess.run(["git", "-C", str(REPO), "diff", "--quiet", "HEAD", "--", "*.json", "*.toml"],
                               env=clean_env())
        self.assertEqual(moved.returncode, 0, "this checkout's *.json/*.toml differ from HEAD; the documented "
                                              "commands read the checkout and the rule reads HEAD, so commit "
                                              "first: the two are compared on the same tree")
        by_rule = rule(REPO, "HEAD")
        for corpus in ccm.CORPORA:
            with self.subTest(corpus.name):
                if corpus.size_cap is not None and not bsd_stat():
                    self.skipTest("the documented JSON command uses BSD `stat -f %z`, which this host lacks")
                printed = documented_output(corpus, REPO)
                members, findings = by_rule[corpus.name]
                self.assertEqual(findings, [], "this checkout carries a path the row cannot answer for")
                self.assertEqual(len(printed), len(set(printed)), "the documented command printed a path twice")
                self.assertGreater(len(members), 1000, "a suspiciously small selection: the instrument")
                self.assertEqual(sorted(set(printed) ^ set(members)), [],
                                 f"{corpus.name}: the rule and its documented command disagree on this checkout")

    def test_rule_selects_what_the_documented_command_prints_on_adversarial_trees(self):
        if not bsd_stat():
            self.skipTest("the documented JSON command uses BSD `stat -f %z`, which this host lacks")
        fx = Fixture(self)
        small = b'{"k": 1}\n'
        json_files = {
            "plain.json": small, "a b.json": small, ".json": small, "dir.json/inner.json": small,
            "dir.json/inner.txt": small, "X.JSON": small, "a.json.bak": small, "first-party/x.json": small,
            "vendor/x.json": small, "first-partyx/y.json": small, "vendorx/y.json": small,
            "sub/vendor/x.json": small, "sub/first-party/x.json": small, "données.json": small,
            "back\\slash.json": small, 'quote".json': small, "tab\tinside.json": small, "empty.json": b"",
            "under-cap.json": b" " * (CAP - 1), "at-cap.json": b" " * CAP, "over-cap.json": b" " * (CAP + 1),
            "vendor/big.json": b" " * (CAP + 1), "\x1cleading-fs.json": small,
        }
        toml_files = {
            "Cargo.toml": b"[package]\n", "a b.toml": b"", ".toml": b"", "dir.toml/x.txt": b"",
            "X.TOML": b"", "first-party/x.toml": b"", "vendor/x.toml": b"", "first-partyx/y.toml": b"",
            "sub/vendor/z.toml": b"", "big.toml": b"#" * (2 * CAP),
        }
        for rel, data in {**json_files, **toml_files}.items():
            fx.write(rel, data)
        fx.write("exec.json", small, executable=True)
        (fx.root / "link.toml").symlink_to("Cargo.toml")
        sha = fx.commit_worktree("adversarial")
        # A gitlink with no worktree: committed from the index (`add -A` would drop it).
        fx.git("update-index", "--add", "--cacheinfo", f"160000,{sha},gitlink.toml")
        fx.git("commit", "-q", "-m", "a gitlink named *.toml")
        head = fx.git("rev-parse", "HEAD").decode().strip()
        by_rule = rule(fx.root, head)
        env = clean_env(ISOLATED)
        expected = {
            "trust-json": {"plain.json", "a b.json", ".json", "dir.json/inner.json", "first-partyx/y.json",
                           "vendorx/y.json", "sub/vendor/x.json", "sub/first-party/x.json", "données.json",
                           "back\\slash.json", 'quote".json', "tab\tinside.json", "empty.json", "under-cap.json",
                           "exec.json", "\x1cleading-fs.json"},
            "trust-toml": {"Cargo.toml", "a b.toml", ".toml", "first-partyx/y.toml", "sub/vendor/z.toml",
                           "big.toml", "link.toml", "gitlink.toml"},
        }
        for corpus in ccm.CORPORA:
            with self.subTest(corpus.name):
                printed = documented_output(corpus, fx.root, env)
                members, findings = by_rule[corpus.name]
                self.assertEqual(findings, [])
                self.assertEqual(set(printed), expected[corpus.name], "the documented command (the oracle)")
                self.assertEqual(set(members), set(printed))


class RefusalTests(unittest.TestCase):
    """Where a git-object reading cannot answer for the checkout, a key."""

    def keys(self, tree_entries: Dict[bytes, Tuple[str, bytes]]) -> Dict[str, Tuple[List[str], List[str]]]:
        fx = Fixture(self)
        self.fx = fx
        return rule(fx.root, fx.tree(tree_entries))

    def test_paths_the_manifest_cannot_carry_are_keyed(self):
        b = ("100644", b"{}")
        got = self.keys({
            b"#c.json": b, b" lead.json": b, "　wide.json".encode(): b, b"a\nb.json": b, b"x\ry.json": b,
            b"\xff.json": b, b"first-party/\xfe.json": b, b"first-party/#x.json": b, b"\x1cfs.json": b,
            "données.toml".encode(): b, b'q".toml': b, "first-party/données.toml".encode(): b,
            b"#c.toml": b, b" lead.toml": b, b"first-party/#c.toml": b, b"ok.toml": b,
        })
        members, findings = got["trust-json"]
        self.assertEqual(members, ["\x1cfs.json"], "U+001C is not Rust white space: the manifest carries it")
        self.assertEqual(sorted(findings), sorted([
            "trust-json UNPINNABLE comment-mark #c.json", "trust-json UNPINNABLE edge-white-space  lead.json",
            "trust-json UNPINNABLE edge-white-space 　wide.json", "trust-json UNPINNABLE line-break a\\x0ab.json",
            "trust-json UNPINNABLE line-break x\\x0dy.json", "trust-json UNPINNABLE not-utf-8 \\xff.json",
            "trust-json UNPINNABLE not-utf-8 first-party/\\xfe.json"]))
        members, findings = got["trust-toml"]
        self.assertEqual(members, ["ok.toml"])
        self.assertEqual(sorted(findings), sorted([
            "trust-toml UNPINNABLE quoted-by-git données.toml", 'trust-toml UNPINNABLE quoted-by-git q".toml',
            "trust-toml UNPINNABLE quoted-by-git first-party/données.toml",
            "trust-toml UNPINNABLE comment-mark #c.toml", "trust-toml UNPINNABLE edge-white-space  lead.toml"]))

    def test_git_really_quotes_what_the_toml_rule_refuses(self):
        # The premise of quoted-by-git, measured: the documented TOML command
        # lists with `git ls-files` and no -z, and git spells these names in C
        # quotes, so a first-party/ prefix filter does not see the prefix.
        fx = Fixture(self)
        fx.tree({"données.toml".encode(): ("100644", b""), "first-party/données.toml".encode(): ("100644", b""),
                 b'q".toml': ("100644", b""), b"plain.toml": ("100644", b"")})
        listed = fx.git("ls-files", "--", "*.toml", index=fx.scratch).decode().split("\n")
        self.assertIn('"donn\\303\\251es.toml"', listed)
        self.assertIn('"first-party/donn\\303\\251es.toml"', listed)
        self.assertIn('"q\\".toml"', listed)
        self.assertIn("plain.toml", listed)

    def test_json_links_and_gitlinks_have_no_single_size(self):
        fx = Fixture(self)
        sha = fx.tree({b"seed": ("100644", b"x")}, parent=None)
        commit = fx.git("commit-tree", sha, "-m", "seed").decode().strip()
        got = rule(fx.root, fx.tree({b"s.json": ("120000", b"target.json"), b"target.json": ("100644", b"{}"),
                                     b"g.json": ("160000", commit.encode()),
                                     b"first-party/s.json": ("120000", b"x"), b"s.toml": ("120000", b"x.toml"),
                                     b"g.toml": ("160000", commit.encode())}))
        members, findings = got["trust-json"]
        self.assertEqual(members, ["target.json"])
        self.assertEqual(sorted(findings), ["trust-json NON-REGULAR 120000 s.json",
                                            "trust-json NON-REGULAR 160000 g.json"])
        self.assertEqual(got["trust-toml"], (["g.toml", "s.toml"], []), "the TOML rule has no size: both list")

    def test_checkout_conversion_is_keyed_only_where_it_can_move_the_cap(self):
        attrs = (b"conv/*.json eol=crlf\nfilt/*.json filter=lfs\nenc/*.json working-tree-encoding=UTF-16\n"
                 b"id/*.json ident\nbin/*.json -text eol=crlf\nvendor/*.json filter=lfs\n")
        half = b"x" * (CAP // 2)
        got = self.keys({b".gitattributes": ("100644", attrs), b"conv/small.json": ("100644", b"{}"),
                         b"conv/half.json": ("100644", half), b"conv/at-cap.json": ("100644", b"x" * CAP),
                         b"filt/a.json": ("100644", b"{}"), b"enc/a.json": ("100644", b"{}"),
                         b"id/a.json": ("100644", b"{}"), b"bin/half.json": ("100644", half),
                         b"vendor/a.json": ("100644", b"{}")})
        members, findings = got["trust-json"]
        self.assertEqual(members, ["bin/half.json", "conv/small.json"])
        self.assertEqual(sorted(findings), sorted([
            "trust-json CHECKOUT-CONVERTED eol=crlf conv/half.json",
            "trust-json CHECKOUT-CONVERTED filter=lfs filt/a.json",
            "trust-json CHECKOUT-CONVERTED working-tree-encoding=UTF-16 enc/a.json",
            "trust-json CHECKOUT-CONVERTED ident id/a.json"]))


class ManifestTests(unittest.TestCase):
    """The manifest as the Rust tests read it, and the header's rule."""

    def verdicts(self, json_manifest: Optional[Tuple[str, bytes]], docs: Dict[bytes, bytes],
                 toml_count: int = 1001) -> Dict[str, ccm.Verdict]:
        fx = Fixture(self)
        entries: Dict[bytes, Tuple[str, bytes]] = {p: ("100644", d) for p, d in docs.items()}
        tomls = [f"t/{i:04d}.toml" for i in range(toml_count)]
        entries.update({p.encode(): ("100644", b"") for p in tomls})
        entries[TOML.manifest.encode()] = ("100644", manifest(TOML, tomls))
        if json_manifest is not None:
            entries[JSON.manifest.encode()] = json_manifest
        return judge(fx.root, fx.tree(entries))

    def test_lines_are_read_as_rust_reads_them(self):
        body = b"  plain.json\r\nplain.json\n\n\tother.json  \n# comment.json\n\xe3\x80\x80wide.json\n"
        got = self.verdicts(("100644", header(JSON).encode() + body),
                            {b"plain.json": b"{}", b"other.json": b"{}", b"wide.json": b"{}"})
        v = got["trust-json"]
        self.assertEqual((v.pinned, v.findings), (3, []))
        self.assertEqual(got["trust-toml"].findings, [])

    def test_new_and_gone_are_keyed_by_path(self):
        got = self.verdicts(("100644", manifest(JSON, ["kept.json", "gone.json"])),
                            {b"kept.json": b"{}", b"new.json": b"{}"})["trust-json"]
        self.assertEqual((got.new, got.gone), (["new.json"], ["gone.json"]))
        self.assertEqual(sorted(got.findings), ["trust-json GONE gone.json", "trust-json NEW new.json"])
        self.assertEqual(got.blocking, [])

    def test_a_manifest_the_rust_test_cannot_read(self):
        cases = (
            ("absent", None, "trust-json MANIFEST-ABSENT"),
            ("a symlink", ("120000", b"elsewhere.txt"), "trust-json MANIFEST-NOT-A-FILE 120000"),
            ("not UTF-8", ("100644", header(JSON).encode() + b"\xff.json\n"), "trust-json MANIFEST-NOT-UTF-8"),
        )
        for name, blob, key in cases:
            with self.subTest(name):
                v = self.verdicts(blob, {b"a.json": b"{}"})["trust-json"]
                self.assertEqual(v.findings, [key])
                self.assertEqual(v.blocking, [key])

    def test_the_header_must_document_this_rule(self):
        undocumented = header(JSON).replace(ccm.REGENERATE_MARK, "# HOW TO REGENERATE:")
        changed = JSON.documented.replace("| sort", "| LC_ALL=C sort")
        for name, text, key in (
            ("no REGENERATE block", undocumented.encode() + b"a.json\n", "trust-json RULE-UNDOCUMENTED"),
            ("another command", manifest(JSON, ["a.json"], documented=changed), "trust-json RULE-DOCUMENTED-DIFFERENTLY"),
        ):
            with self.subTest(name):
                v = self.verdicts(("100644", text), {b"a.json": b"{}", b"b.json": b"{}"})["trust-json"]
                rule_keys = [k for k in v.findings if " RULE-" in k]
                self.assertEqual(len(rule_keys), 1)
                self.assertTrue(rule_keys[0].startswith(key), v.findings)
                self.assertIn("trust-json NEW b.json", v.findings, "the membership is still judged beside it")

    def test_the_toml_floor_of_the_rust_membership_test(self):
        v = self.verdicts(("100644", manifest(JSON, [])), {}, toml_count=1000)["trust-toml"]
        self.assertEqual(v.findings, ["trust-toml PINNED-AT-MOST 1000 1000"])
        self.assertEqual(self.verdicts(("100644", manifest(JSON, [])), {}, toml_count=1001)["trust-toml"].findings, [])


class CommandLineTests(unittest.TestCase):
    """The script as a row runs it: from the root, on TRUST_PUSHED_REFS."""

    def setUp(self):
        fx = self.fx = Fixture(self)
        (fx.root / "scripts").mkdir()
        shutil.copy2(SCRIPT, fx.root / "scripts" / SCRIPT.name)
        tomls = [f"t/{i:04d}.toml" for i in range(1001)]
        for rel in tomls:
            fx.write(rel, b"")
        for rel in ("a.json", "b.json"):
            fx.write(rel, b"{}")
        fx.write(JSON.manifest, manifest(JSON, ["a.json", "b.json"]))
        fx.write(TOML.manifest, manifest(TOML, tomls))
        self.good = fx.commit_worktree("good")
        self.red = fx.tree({b"c.json": ("100644", b"{}"), b"a.json": ("100644", b"[]")}, parent=self.good)

    def run_script(self, *args: str, refs: Optional[str] = None, python: str = sys.executable) -> Tuple[int, str]:
        env = clean_env(ISOLATED)
        if refs is not None:
            env["TRUST_PUSHED_REFS"] = refs
        proc = subprocess.run([python, f"scripts/{SCRIPT.name}", *args], cwd=self.fx.root, env=env,
                              capture_output=True, text=True)
        return proc.returncode, proc.stdout + proc.stderr

    @staticmethod
    def refs(*shas: str) -> str:
        return "\n".join(f"refs/heads/b{i} {sha} refs/heads/main {'0' * 40}" for i, sha in enumerate(shas))

    def test_green_red_and_the_repair_line(self):
        interpreters = [sys.executable]
        if Path("/usr/bin/python3").is_file():
            interpreters.append("/usr/bin/python3")  # the oldest a row runs under here (3.9)
        for python in interpreters:
            with self.subTest(python):
                rc, out = self.run_script(refs=self.refs(self.good), python=python)
                self.assertEqual(rc, 0, out)
                self.assertIn("PASS: every pinned corpus membership matches its tree", out)
                self.assertNotIn("FINDING", out)
                rc, out = self.run_script(refs=self.refs(self.red), python=python)
                self.assertEqual(rc, 1, out)
                self.assertIn("trust-json: NEW in the tree, not pinned (1):", out)
                self.assertIn(f"      {ccm.WRITE_COMMAND}\n", out)
                tail = out[out.index("FINDING: "):].split("\n")
                self.assertEqual(tail[:2], ["FINDING: trust-json NEW c.json", "FINDINGS: complete"])

    def test_one_verdict_per_tree_and_unreadable_is_unkeyed(self):
        rc, out = self.run_script(refs=self.refs(self.red, self.red))
        self.assertEqual((rc, out.count("trust-json: NEW in the tree")), (1, 1), out)
        self.assertIn("refs/heads/b0 ", out)
        self.assertIn("refs/heads/b1 ", out)
        ghost = "1234567890abcdef1234567890abcdef12345678"
        rc, out = self.run_script(refs=self.refs(self.red, ghost))
        self.assertEqual(rc, 1, out)
        self.assertIn("CORPUS MEMBERSHIP UNREADABLE", out)
        self.assertIn("FINDING: trust-json NEW c.json", out)
        self.assertNotIn("FINDINGS: complete", out, "an unreadable tree is a cause no key names")

    def test_deletions_malformed_refs_and_the_standing_reading(self):
        rc, out = self.run_script(refs=self.refs("0" * 40))
        self.assertEqual(rc, 0, out)
        self.assertIn("SKIPPED: deletion(s) only", out)
        for bad in ("HEAD", f"HEAD {self.good} refs/heads/main", f"HEAD {self.good[:12]} refs/heads/main {'0' * 40}"):
            with self.subTest(bad):
                self.assertEqual(self.run_script(refs=bad)[0], 2)
        self.assertEqual(self.run_script()[0], 0, "unset: HEAD, which is good")
        self.assertEqual(self.run_script("--rev", self.red, refs=self.refs(self.good))[0], 1, "--rev wins")


class WriteTests(unittest.TestCase):
    """`--write`: the re-pin the red row prints."""

    def setUp(self):
        fx = self.fx = Fixture(self)
        (fx.root / "scripts").mkdir()
        shutil.copy2(SCRIPT, fx.root / "scripts" / SCRIPT.name)
        self.tomls = [f"t/{i:04d}.toml" for i in range(1001)]
        for rel in self.tomls:
            fx.write(rel, b"")
        for rel in ("old.json", "z.json"):
            fx.write(rel, b"{}")
        fx.write(JSON.manifest, manifest(JSON, ["old.json", "z.json"]))
        fx.write(TOML.manifest, manifest(TOML, self.tomls))
        fx.commit_worktree("good")

    def write(self) -> Tuple[int, str]:
        proc = subprocess.run([sys.executable, f"scripts/{SCRIPT.name}", "--write"], cwd=self.fx.root,
                              env=clean_env(ISOLATED), capture_output=True, text=True)
        return proc.returncode, proc.stdout + proc.stderr

    def test_repins_from_the_index_keeping_the_header(self):
        fx = self.fx
        (fx.root / "old.json").unlink()
        fx.write("new dir/é.json", b"{}")
        fx.write("B.json", b"{}")
        fx.git("add", "-A")
        rc, out = self.write()
        self.assertEqual(rc, 0, out)
        self.assertIn("re-pinned 2 -> 3 (+2 -1)", out)
        self.assertIn(f"{TOML.manifest}: 1001 pinned, exact; unchanged", out)
        data = (fx.root / JSON.manifest).read_bytes()
        head = header(JSON).encode()
        self.assertTrue(data.startswith(head), "the header, its blank lines included, byte for byte")
        self.assertEqual(data[len(head):], "B.json\nnew dir/é.json\nz.json\n".encode(), "byte order")
        fx.git("add", "-A")
        self.assertEqual(judge(fx.root, fx.git("write-tree").decode().strip())["trust-json"].findings, [])

    def test_refuses_what_a_repin_cannot_clear(self):
        fx = self.fx
        before = (fx.root / JSON.manifest).read_bytes()
        cases = (
            ("an unpinnable path", lambda: fx.write("#bad.json", b"{}"), "UNPINNABLE comment-mark #bad.json"),
            ("another documented rule", lambda: fx.write(
                JSON.manifest, manifest(JSON, ["old.json"], documented=JSON.documented + " -u")),
             "RULE-DOCUMENTED-DIFFERENTLY"),
            ("a path above the header's last comment", lambda: fx.write(
                JSON.manifest, b"old.json\n" + manifest(JSON, ["z.json"])), "above the header's last comment line"),
        )
        for name, damage, needle in cases:
            with self.subTest(name):
                fx.git("reset", "-q", "--hard")
                fx.git("clean", "-qfd")
                damage()
                fx.write("added.json", b"{}")
                fx.git("add", "-A")
                written = (fx.root / JSON.manifest).read_bytes()
                rc, out = self.write()
                self.assertEqual(rc, 1, out)
                self.assertIn("REFUSED", out)
                self.assertIn(needle, out)
                self.assertEqual((fx.root / JSON.manifest).read_bytes(), written, "nothing written")
        fx.git("reset", "-q", "--hard")
        self.assertEqual((fx.root / JSON.manifest).read_bytes(), before)


if __name__ == "__main__":
    unittest.main()
