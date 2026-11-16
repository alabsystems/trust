#!/usr/bin/env python3
"""Controls for scripts/trust_core/reanchor_citations.py.

The tool rewrites ledger citations and registers the judgments that rewrite changed, so what
matters most is what it REFUSES: a citation whose text changed, or whose lines became ambiguous,
must never be moved, and a judgment that was already unreviewed, or that changed for any other
reason, must never be registered as a move. Most tests exercise the pure functions — `classify`,
`rewrite`, `parse_finding`, `moved_judgments`, `register` and `choose_base` — with synthetic inputs, so they need
no git and no real ledger. CommandStatus runs the real CLI in an isolated Git fixture with
checker processes returning success, violations and environment errors. The registry test reads
the real registries only to check the format.
"""

from __future__ import annotations

import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "trust_core"))
import reanchor_citations as tool  # noqa: E402  (its common import guards the Python floor)

tomllib = tool.C.tomllib

BASE = {
    "tests/h.sh": ["# header", "run_gate alpha", "run_gate beta", "shared line", "tail"],
    "scripts/x.sh": ["one", "mapfile -t TESTS < <(list)", "three"],
}
A, B, C = ("sha256:" + c * 64 for c in "abc")


def at(files):
    return lambda source, path: files.get(path)


class Classify(unittest.TestCase):
    def test_a_whole_line_moved_to_exactly_one_place_is_a_move(self) -> None:
        head = {"tests/h.sh": ["# header", "# inserted", "# inserted", "run_gate alpha", "run_gate beta", "shared line", "tail"]}
        moves, substantive = tool.classify(
            [("worktree", "tests/h.sh", 2, 2, "run_gate alpha"), ("worktree", "tests/h.sh", 3, 3, "beta")],
            at(BASE), at(head),
        )
        self.assertEqual(moves, {("worktree", "tests/h.sh", 2, 2): (4, 4), ("worktree", "tests/h.sh", 3, 3): (5, 5)})
        self.assertEqual(substantive, [])

    def test_a_range_moves_only_as_a_whole(self) -> None:
        head = {"tests/h.sh": ["# inserted", "# header", "run_gate alpha", "run_gate beta", "shared line", "tail"]}
        moves, substantive = tool.classify([("worktree", "tests/h.sh", 2, 3, "run_gate alpha run_gate beta")], at(BASE), at(head))
        self.assertEqual((moves, substantive), ({("worktree", "tests/h.sh", 2, 3): (3, 4)}, []))
        # The two lines still exist, but no longer together: not a move.
        split = {"tests/h.sh": ["# header", "run_gate alpha", "# between", "run_gate beta", "shared line", "tail"]}
        moves, substantive = tool.classify([("worktree", "tests/h.sh", 2, 3, "run_gate alpha run_gate beta")], at(BASE), at(split))
        self.assertEqual(moves, {})
        self.assertIn("text changed", substantive[0])

    def test_changed_text_is_refused_even_when_the_quote_survives_elsewhere(self) -> None:
        # The quoted substring still exists at HEAD, but the WHOLE cited line does
        # not: the surrounding text changed, so this is a judgment, not a move.
        head = {"scripts/x.sh": ["one", "mapfile -t TESTS < <(list) || true  # changed", "three"]}
        moves, substantive = tool.classify(
            [("worktree", "scripts/x.sh", 2, 2, "mapfile -t TESTS")], at(BASE), at(head)
        )
        self.assertEqual(moves, {})
        self.assertEqual(len(substantive), 1)
        self.assertIn("text changed", substantive[0])

    def test_a_line_that_now_occurs_twice_is_ambiguous_and_refused(self) -> None:
        head = {"tests/h.sh": ["shared line", "# header", "run_gate alpha", "run_gate beta", "shared line", "tail"]}
        moves, substantive = tool.classify(
            [("worktree", "tests/h.sh", 4, 4, "shared line")], at(BASE), at(head)
        )
        self.assertEqual(moves, {})
        self.assertIn("ambiguous", substantive[0])

    def test_a_citation_past_a_shrunken_files_end_takes_its_quote_from_the_ledger(self) -> None:
        lines = ["  CITE: table.gate_source[24].evidence[1]: worktree:CLAUDE.md:356: the file has 312 lines"]
        table = 'x = [{ ref = "worktree:CLAUDE.md:356", quote = "does **not** source \\"it\\"" }]'
        prose = "see worktree:CLAUDE.md:356 «does **not** source»"
        self.assertEqual(
            tool.beyond_end_findings(lines, [table, prose]),
            [("worktree", "CLAUDE.md", 356, 356, 'does **not** source "it"'),
             ("worktree", "CLAUDE.md", 356, 356, "does **not** source")],
        )

    def test_a_line_with_a_twin_at_the_base_is_refused(self) -> None:
        # The cited copy (line 2) is deleted; its twin survives. Re-pointing the
        # citation at the twin would silently change what it cites.
        base = {"x.rs": ["fn a() {", "return Err(Refusal::Unsound);", "}", "fn b() {", "return Err(Refusal::Unsound);", "}"]}
        head = {"x.rs": ["fn b() {", "", "", "return Err(Refusal::Unsound);", "}"]}
        moves, substantive = tool.classify(
            [("worktree", "x.rs", 2, 2, "return Err(Refusal::Unsound);")], at(base), at(head)
        )
        self.assertEqual(moves, {})
        self.assertIn("2 times at base", substantive[0])

    def test_a_citation_already_wrong_at_the_base_is_not_papered_over(self) -> None:
        moves, substantive = tool.classify(
            [("worktree", "tests/h.sh", 2, 2, "a quote that was never there")], at(BASE), at(BASE)
        )
        self.assertEqual(moves, {})
        self.assertIn("already did not contain", substantive[0])

    def test_a_line_moves_only_when_every_quote_cited_there_held_at_the_base(self) -> None:
        head = {"tests/h.sh": ["# inserted", "# header", "run_gate alpha", "run_gate beta", "shared line", "tail"]}
        findings = [("worktree", "tests/h.sh", 2, 2, "alpha"), ("worktree", "tests/h.sh", 2, 2, "alpha"),
                    ("worktree", "tests/h.sh", 2, 2, "never there")]
        moves, substantive = tool.classify(findings, at(BASE), at(head))
        self.assertEqual(moves, {})
        self.assertEqual(len(substantive), 1)
        self.assertIn("never there", substantive[0])

    def test_a_missing_file_or_line_is_refused(self) -> None:
        moves, substantive = tool.classify(
            [("worktree", "gone.sh", 1, 1, "x"), ("worktree", "tests/h.sh", 99, 99, "x")], at(BASE), at(BASE)
        )
        self.assertEqual(moves, {})
        self.assertEqual(len(substantive), 2)


class Rewrite(unittest.TestCase):
    def test_moves_apply_simultaneously_so_a_chain_is_not_rewritten_twice(self) -> None:
        text = 'a "worktree:tests/h.sh:2" b "worktree:tests/h.sh:3" c'
        out = tool.rewrite(text, {("worktree", "tests/h.sh", 2, 2): (3, 3), ("worktree", "tests/h.sh", 3, 3): (4, 4)})
        self.assertEqual(out, 'a "worktree:tests/h.sh:3" b "worktree:tests/h.sh:4" c')

    def test_only_the_named_file_and_line_move(self) -> None:
        text = ("worktree:tests/h.sh:2 worktree:tests/h.sh:20 worktree:other.sh:2 "
                "rustc:tests/h.sh:2 (worktree:tests/h.sh:2 «q»)")
        out = tool.rewrite(text, {("worktree", "tests/h.sh", 2, 2): (9, 9)})
        self.assertEqual(out, ("worktree:tests/h.sh:9 worktree:tests/h.sh:20 worktree:other.sh:2 "
                               "rustc:tests/h.sh:2 (worktree:tests/h.sh:9 «q»)"))

    def test_a_line_move_leaves_a_range_that_starts_there_and_a_range_moves_whole(self) -> None:
        text = 'ref = "worktree:tests/h.sh:2-3" x worktree:tests/h.sh:2 y trust-test:tests/ui/a.rs:5-6'
        out = tool.rewrite(text, {("worktree", "tests/h.sh", 2, 2): (7, 7), ("trust-test", "tests/ui/a.rs", 5, 6): (8, 9)})
        self.assertEqual(out, 'ref = "worktree:tests/h.sh:2-3" x worktree:tests/h.sh:7 y trust-test:tests/ui/a.rs:8-9')
        self.assertEqual(tool.rewrite(text, {("worktree", "tests/h.sh", 2, 3): (4, 5)}),
                         'ref = "worktree:tests/h.sh:4-5" x worktree:tests/h.sh:2 y trust-test:tests/ui/a.rs:5-6')

    def test_a_first_party_citation_moves_and_the_bare_word_does_not(self) -> None:
        text = ('ref = "first-party:trust-cg/src/a.rs:198" '
                'x-first-party:trust-cg/src/a.rs:198 worktree:first-party:1')
        out = tool.rewrite(text, {("first-party", "trust-cg/src/a.rs", 198, 198): (211, 211)})
        self.assertEqual(out, ('ref = "first-party:trust-cg/src/a.rs:211" '
                               'x-first-party:trust-cg/src/a.rs:198 worktree:first-party:1'))

    def test_no_moves_changes_nothing(self) -> None:
        text = '{ ref = "worktree:tests/h.sh:2", quote = "run_gate alpha" }'
        self.assertEqual(tool.rewrite(text, {}), text)


class ChooseBase(unittest.TestCase):
    def test_the_base_proving_the_most_moves_wins(self) -> None:
        self.assertEqual(tool.choose_base([("newest", 0), ("mid", 30), ("oldest", 6)]), "mid")

    def test_a_tie_keeps_the_newer_base(self) -> None:
        self.assertEqual(tool.choose_base([("newest", 3), ("older", 3)]), "newest")

    def test_zero_everywhere_keeps_the_default_base(self) -> None:
        # Candidates arrive newest first, so the all-zero case is the table's last commit:
        # exactly what the default (no --base) would have used.
        self.assertEqual(tool.choose_base([("newest", 0), ("older", 0)]), "newest")

    def test_no_candidates_is_none(self) -> None:
        self.assertIsNone(tool.choose_base([]))


class FindingsParser(unittest.TestCase):
    def test_external_and_std_citations_keep_their_source_identity(self) -> None:
        for source in (*tool.EXTERNAL, "std"):
            with self.subTest(source=source):
                ref = f"{source}:src/example.rs:2"
                self.assertEqual(tool.parse_finding(f"  CITE: row: {ref} does not contain 'x'"),
                                 (source, "src/example.rs", 2, 2, "x"))
                self.assertEqual(tool.rewrite(ref, {(source, "src/example.rs", 2, 2): (4, 4)}),
                                 f"{source}:src/example.rs:4")

    def test_every_finding_kind_and_quote_spelling_is_read(self) -> None:
        lines = [
            "  CITE: table.search[0].evidence[0]: worktree:tests/h.sh:469 does not contain 'run x'",
            "  DOC: prose:gates: worktree:tests/h.sh:819 does not contain 'cd \"$ROOT\" || exit 2'",
            "  REVIEW: judgment search:S1: its content changed",
            "  CITE: table.semantics[0].x: first-party:trust-ir/docs/p.md:156 does not contain 'q'",
            '  CITE: table.semantics[5].y: first-party:trust-ir/docs/S.md:160 does not contain "the interpreter\'s behavior"',
            "  TABLE: table.semantics[1].role: worktree:crates/p.rs:20810 does not contain 'via_model'",
            "  ROW: rows[3].rustc: trust-test:tests/ui/a.rs:22-23 does not contain the word 'borrow'",
            "  CITE: rows[4]: worktree:a.rs:9: the file has 5 lines",
            # The checker prints the quote with repr, so a backslash in it arrives doubled.
            "  CITE: e[6]: first-party:trust-cg/s.sh:688-689 does not contain " + repr("set -- test \\ --lib"),
        ]
        found = [parsed for line in lines if (parsed := tool.parse_finding(line))]
        self.assertEqual(found, [
            ("worktree", "tests/h.sh", 469, 469, "run x"),
            ("worktree", "tests/h.sh", 819, 819, 'cd "$ROOT" || exit 2'),
            ("first-party", "trust-ir/docs/p.md", 156, 156, "q"),
            ("first-party", "trust-ir/docs/S.md", 160, 160, "the interpreter's behavior"),
            ("worktree", "crates/p.rs", 20810, 20810, "via_model"),
            ("trust-test", "tests/ui/a.rs", 22, 23, "borrow"),
            ("first-party", "trust-cg/s.sh", 688, 689, "set -- test \\ --lib"),
        ])


class HistoricalPins(unittest.TestCase):
    def test_external_lines_follow_each_committed_pin_and_never_the_checkout(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            repo, cache = root / "repo", root / "cache"

            def git(path, *args):
                return subprocess.run(["git", "-C", str(path), *args], check=True,
                                      capture_output=True, text=True).stdout.strip()

            def initialize(path):
                path.mkdir(parents=True)
                git(path, "init", "-q")
                git(path, "config", "user.name", "Fixture")
                git(path, "config", "user.email", "fixture@example.invalid")
                git(path, "config", "commit.gpgsign", "false")
                git(path, "config", "core.hooksPath", "/dev/null")

            def commit(path):
                git(path, "add", ".")
                git(path, "commit", "-q", "-m", "fixture")
                return git(path, "rev-parse", "HEAD")

            initialize(repo)
            initialize(cache / "minirust")
            external = cache / "minirust"
            (external / "x.rs").write_text("heading\nunique quoted line\n")
            old = commit(external)
            (external / "x.rs").write_text("heading\ninserted\nunique quoted line\n")
            new = commit(external)
            subprocess.run(["git", "clone", "-q", str(external), str(cache / "rust")], check=True)
            pins_path = repo / tool.C.PINS_REL
            pins_path.parent.mkdir(parents=True)

            def pin(revision):
                pins_path.write_text('schema = "trust.core.external-pins.v1"\n'
                                     '[alignment]\n' + f'rust_revision = "{revision}"\n'
                                     '[sources.minirust]\n' + f'revision = "{revision}"\n')
                return commit(repo)

            before, after = pin(old), pin(new)
            # Neither the current checkout nor uncommitted pin changes can redirect a read.
            (external / "x.rs").write_text("dirty checkout\n")
            pins_path.write_text("invalid uncommitted pins\n")
            with mock.patch.object(tool, "REPO", repo), mock.patch.object(tool.C, "sources_root", return_value=cache):
                self.assertEqual(tool.lines_at(before, "minirust", "x.rs"),
                                 ["heading", "unique quoted line", ""])
                self.assertEqual(tool.lines_at(after, "minirust", "x.rs"),
                                 ["heading", "inserted", "unique quoted line", ""])
                self.assertEqual(tool.lines_at(before, "std", "x.rs"),
                                 ["heading", "unique quoted line", ""])
                self.assertEqual(tool.lines_at(after, "std", "x.rs"),
                                 ["heading", "inserted", "unique quoted line", ""])
                moves, refused = tool.classify([("minirust", "x.rs", 2, 2, "quoted")],
                    lambda s, p: tool.lines_at(before, s, p), lambda s, p: tool.lines_at(after, s, p))
                self.assertEqual((moves, refused), ({("minirust", "x.rs", 2, 2): (3, 3)}, []))
                self.assertIsNone(tool.lines_at(after, "reference", "x.rs"))  # absent historical pin
                absent = pin("0" * 40)
                self.assertIsNone(tool.lines_at(absent, "minirust", "x.rs"))  # absent object


class CommandStatus(unittest.TestCase):
    def test_write_without_eligible_moves_preserves_checker_status_and_files(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            scripts = repo / "scripts" / "trust_core"
            scripts.mkdir(parents=True)
            for name in ("common.py", "reanchor_citations.py"):
                shutil.copyfile(Path(tool.__file__).parent / name, scripts / name)
            core = repo / "docs" / "trust-core"
            (core / "reviews").mkdir(parents=True)
            protected = [core / "static-semantics-source-map.toml",
                         core / "STATIC_SEMANTICS_SOURCE_MAP.md",
                         core / "reviews" / "static_semantics_source_map.toml"]
            for path in protected:
                path.write_text("unchanged ledger or review\n", encoding="utf-8")
            checker = scripts / "static_semantics_source_map.py"
            subprocess.run(["git", "init", "--quiet", str(repo)], check=True)
            subprocess.run(["git", "-C", str(repo), "add", "docs"], check=True)
            subprocess.run(["git", "-C", str(repo), "-c", "user.name=Fixture",
                            "-c", "user.email=fixture@example.invalid", "-c", "commit.gpgsign=false",
                            "-c", "core.hooksPath=/dev/null", "commit", "--quiet", "-m", "fixture"],
                           check=True)
            for status, diagnostic in [(0, "audit passed"),
                                       (1, "UNIVERSE: unmapped Reference rule abi.no_mangle.ascii-only"),
                                       (2, "source clone missing")]:
                with self.subTest(checker_status=status):
                    checker.write_text(f"print({diagnostic!r})\nraise SystemExit({status})\n",
                                       encoding="utf-8")
                    run = subprocess.run([sys.executable, str(scripts / "reanchor_citations.py"),
                                          "static_semantics_source_map", "--write"],
                                         cwd=repo, capture_output=True, text=True)
                    self.assertEqual(run.returncode, status, run.stdout + run.stderr)
                    self.assertIn(diagnostic, run.stdout + run.stderr)
                    for path in protected:
                        self.assertEqual(path.read_text(encoding="utf-8"), "unchanged ledger or review\n")


def changed(jid, new, old):
    return f"  REVIEW: judgment {jid}: its content changed since it was registered (content {new}, registered {old}); a changed judgment takes its new digest and a review by a new record"


class Registration(unittest.TestCase):
    def test_only_a_judgment_reviewed_before_the_rewrite_is_registered(self) -> None:
        before = [
            "  CITE: table.semantics[0].x: worktree:a.rs:3 does not contain 'q'",
            changed("semantics:S2", C, A),
            "  REVIEW: judgment prose:gates: its last review record (r) reviewed x, not the content y; append a review",
        ]
        after = [
            changed("semantics:S1", B, A),              # changed by the rewrite alone: registered
            changed("semantics:S2", B, A),              # already unreviewed before: a person's
            changed("prose:gates", B, A),               # named before under another finding: a person's
            "  REVIEW: judgment semantics:S9 is not registered in r.toml; register it with a review record",
            "  REVIEW: judgment prose:gates: its last review record (r) reviewed x, not the content y; append a review",
        ]
        moved, other = tool.moved_judgments(before, after)
        self.assertEqual(moved, {"semantics:S1": (A, B)})
        self.assertEqual(len(other), 3)
        self.assertTrue(all("S1" not in line for line in other))

    def registry(self) -> str:
        return ('schema = "trust.core.reviews.v1"\ndeliverable = "d"\n\n[record.first]\nround = "r"\ndate = "2026-09-01"\n'
                'evidence = ["e"]\nreason = "r"\n\n[judgment]\n'
                f'"semantics:S1" = {{ digest = "{A}", reviews = [["first", "{A}"]] }}\n'
                f'"prose:gates" = {{ digest = "{C}", reviews = [["first", "{C}"]] }}\n')

    def test_register_appends_one_record_and_one_review_per_moved_judgment(self) -> None:
        record = {"round": "moves", "date": "2026-09-29", "evidence": ["worktree:a.rs:3 -> 5: pure move: whole line byte-identical and unique at HEAD"],
                  "reason": "Only cited line numbers move."}
        text = tool.register(self.registry(), "pure-moves-x", record, {"semantics:S1": (A, B)})
        data = tomllib.loads(text)
        self.assertEqual(data["record"]["pure-moves-x"], record)
        self.assertEqual(data["judgment"]["semantics:S1"], {"digest": B, "reviews": [["first", A], ["pure-moves-x", B]]})
        self.assertEqual(data["judgment"]["prose:gates"], {"digest": C, "reviews": [["first", C]]})
        self.assertTrue(text.startswith(self.registry().rstrip("\n").split('"semantics:S1"')[0]))

    def test_register_refuses_a_stale_digest_an_unknown_judgment_and_a_taken_record_id(self) -> None:
        record = {"round": "r", "date": "2026-09-29", "evidence": ["e"], "reason": "r"}
        for moved, record_id in (({"semantics:S1": (C, B)}, "new"), ({"semantics:S7": (A, B)}, "new"), ({"semantics:S1": (A, B)}, "first")):
            with self.subTest(moved=moved, record_id=record_id), self.assertRaises(ValueError):
                tool.register(self.registry(), record_id, record, moved)

    def test_the_entry_format_is_the_registries_own(self) -> None:
        for path in sorted((Path(__file__).resolve().parents[2] / "docs" / "trust-core" / "reviews").glob("*.toml")):
            text = path.read_text(encoding="utf-8")
            lines = set(text.split("\n"))
            for jid, entry in tomllib.loads(text)["judgment"].items():
                if "retired" not in entry:
                    self.assertIn(tool._entry_line(json.dumps(jid, ensure_ascii=False), entry), lines, (path.name, jid))


if __name__ == "__main__":
    unittest.main()
