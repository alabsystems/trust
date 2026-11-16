"""Historical pin evidence retains exact original custody and no current authority."""

import hashlib
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "trust_core"))
import static_semantics_source_map as S


class HistoricalPinBinding(unittest.TestCase):
    def setUp(self):
        self.scratch = tempfile.TemporaryDirectory()
        self.addCleanup(self.scratch.cleanup)
        self.repo = Path(self.scratch.name)
        self.git("init", "-q")
        self.git("config", "user.name", "Fixture")
        self.git("config", "user.email", "fixture@example.invalid")
        self.git("config", "commit.gpgsign", "false")
        self.git("config", "core.hooksPath", "/dev/null")
        self.path = S.SNAPSHOT_DIR + "/pin.json"
        self.exception = {
            "source": "fls", "snapshot": self.path, "decision": "Original decision",
            "default_branch": "main", "default_branch_state": "e" * 40,
            "state_committer_date": "2026-06-01T00:00:00Z", "successor": "f" * 40,
            "successor_committer_date": "2026-07-09T00:00:00Z",
            "merged_into_default_branch_by": "b" * 40,
            "merged_at": "2026-07-09T00:00:00Z", "commits_after_state": 1,
        }
        self.snapshot = {
            "schema": S.PIN_DERIVATION, "repo": "rust-lang/fls",
            "compare": {"base": "e" * 40, "head": "b" * 40, "commits": ["b" * 40],
                        "status": "ahead", "ahead_by": 1, "behind_by": 0, "files": []},
            "default_branch_state": {"sha": "e" * 40, "committer_date": "2026-06-01T00:00:00Z"},
            "successor": {"sha": "f" * 40, "committer_date": "2026-07-09T00:00:00Z", "parents": ["e" * 40]},
            "merged_into_default_branch_by": {"sha": "b" * 40, "committer_date": "2026-07-09T00:00:00Z"},
        }
        payload = json.dumps(self.snapshot).encode()
        self.write(self.path, payload)
        self.descriptor = {"file": self.path, "kind": "pin-derivation", "url": "https://example.invalid/snapshot",
                           "retrieved": "2026-07-10", "sha256": "sha256:" + hashlib.sha256(payload).hexdigest()}
        ledger = 'schema = ' + json.dumps(S.SCHEMA) + '\n[[pin_exception]]\n'
        ledger += ''.join(k + ' = ' + json.dumps(v) + '\n' for k, v in self.exception.items())
        ledger += '\n[[snapshot]]\n' + ''.join(k + ' = ' + json.dumps(v) + '\n' for k, v in self.descriptor.items())
        self.write(S.LEDGER_REL, ledger.encode())
        self.write(S.C.PINS_REL, self.pins_text("b", "2026-07-08T00:00:00Z").encode())
        self.original = self.commit()
        self.exception["historical_at"] = self.original
        self.write(S.C.PINS_REL, self.pins_text("d", "2026-11-02T00:00:00Z").encode())
        self.commit()
        self.current = S.C.load_pins(self.repo / S.C.PINS_REL)

    def git(self, *args):
        return subprocess.check_output(["git", "-C", str(self.repo), *args], text=True).strip()

    def write(self, path, payload):
        p = self.repo / path
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_bytes(payload)

    def commit(self):
        self.git("add", ".")
        self.git("commit", "-q", "-m", "fixture")
        return self.git("rev-parse", "HEAD")

    @staticmethod
    def pins_text(digit, date):
        return ('schema = "trust.core.external-pins.v1"\n[alignment]\n'
                f'rust_revision = "{digit * 40}"\nrust_committer_date = "{date}"\n'
                '[sources.fls]\nrepo = "https://github.com/rust-lang/fls"\n'
                f'revision = "{digit * 40}"\ncommitter_date = "2026-06-01T00:00:00Z"\n')

    def bound(self, exception=None, descriptor=None, current=None):
        return S.historical_exception_pins(self.repo, exception or self.exception,
                                          descriptor or self.descriptor, current or self.current)

    def test_original_binding_passes_but_does_not_enter_current_delta(self):
        self.assertEqual(self.bound().sources["fls"].revision, "b" * 40)
        checker = S.Checker(S.Options(repo=self.repo))
        checker.pins = self.current
        checker.snapshots = {self.path: self.snapshot}
        checker.t = {"pin_exception": {"fls": self.exception}, "snapshot": {self.path: self.descriptor}}
        checker.trees = {"fls": S.C.DirTree(self.repo)}
        checker.sel = {"predicates": {"formality_note": "$^"}}
        checker.pin_delta()
        self.assertEqual(checker.f.violations, [])
        self.assertEqual(checker.delta, {"added": {}, "removed": {}, "changed": {}, "formality": []})

    def test_changed_exception_descriptor_and_payload_all_refuse(self):
        for key, value in [("decision", "A new decision"), ("merged_at", "2026-07-10T00:00:00Z")]:
            with self.subTest(exception_field=key), self.assertRaisesRegex(ValueError, "committed original"):
                self.bound({**self.exception, key: value})
        with self.assertRaisesRegex(ValueError, "descriptor"):
            self.bound(descriptor={**self.descriptor, "sha256": "sha256:" + "0" * 64})
        original = (self.repo / self.path).read_bytes()
        for payload in [original + b"\n", original.replace(b",", b",\r\n", 1)]:
            self.write(self.path, payload)
            with self.assertRaisesRegex(ValueError, "payload"):
                self.bound()
        self.write(self.path, original)

    def test_missing_nonancestor_relabelled_and_current_inputs_refuse(self):
        for revision in ["0" * 40, self.original[:12]]:
            with self.subTest(revision=revision), self.assertRaisesRegex(ValueError, "ancestor"):
                self.bound({**self.exception, "historical_at": revision})
        tip = self.git("rev-parse", "HEAD")
        self.git("checkout", "-q", "--detach", self.original)
        self.write("sibling", b"separate history")
        sibling = self.commit()
        self.git("checkout", "-q", "--detach", tip)
        with self.assertRaisesRegex(ValueError, "ancestor"):
            self.bound({**self.exception, "historical_at": sibling})
        with self.assertRaisesRegex(ValueError, "older alignment"):
            self.bound(current=S.C.Pins("a" * 40, "2026-11-02T00:00:00Z",
                {"fls": S.C.Source("fls", "https://github.com/rust-lang/fls", "b" * 40, "2026-06-01T00:00:00Z")}))
        # Same bytes at an arbitrary ancestor are insufficient if its pins are current.
        with self.assertRaisesRegex(ValueError, "older alignment"):
            self.bound({**self.exception, "historical_at": tip})


if __name__ == "__main__":
    unittest.main()
