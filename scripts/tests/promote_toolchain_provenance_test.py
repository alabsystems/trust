#!/usr/bin/env python3
"""Exercise the real promotion classifier without running the promotion CLI."""

# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

import hashlib
import importlib.util
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


SCRIPT = Path(__file__).parents[1] / "promote-toolchain.sh"
LIBRARY = SCRIPT.parent / "lib" / "trust_build_provenance.py"
SPEC = importlib.util.spec_from_file_location("trust_provenance", LIBRARY)
provenance = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = provenance
SPEC.loader.exec_module(provenance)


def fingerprint(fields):
    """Form fixture data using x.py's documented start-fingerprint format."""
    return provenance.fingerprint(fields)


def record(fields):
    return "".join(f"{key}={value}\n" for key, value in fields.items())


class PromotionProvenanceTests(unittest.TestCase):
    observations = []

    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory(prefix="trust-prov-helper-")
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root = Path(cls.temporary.name)
        cls.repo = cls.root / "repo"
        cls.repo.mkdir()
        cls.environment = os.environ.copy()
        for key in list(cls.environment):
            if key.startswith("GIT_"):
                del cls.environment[key]
        cls.environment.update(GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_SYSTEM=os.devnull)
        cls.run_command(["git", "init", "-q", str(cls.repo)])
        # The real classifier invokes the repository's shared schema reader.
        library = cls.repo / "scripts/lib/trust_build_provenance.py"
        library.parent.mkdir(parents=True)
        shutil.copyfile(LIBRARY, library)
        cls.run_command(["git", "-C", str(cls.repo), "add", "scripts"])
        cls.run_command(["git", "-C", str(cls.repo), "-c", "user.name=Fixture",
                         "-c", "user.email=fixture@example.invalid", "-c",
                         f"core.hooksPath={os.devnull}", "commit", "-qm", "fixture",
                         "--allow-empty"])
        cls.head = cls.run_command(["git", "-C", str(cls.repo), "rev-parse", "HEAD"]).stdout.strip()
        # This exact contiguous source slice contains globals and all classifier
        # helpers, ending before reporting or any CLI action. No copied logic.
        source = SCRIPT.read_text()
        begin = source.index('\nPROV_CLASS=""') + 1
        end = source.index("\nprov_report() {", begin)
        cls.helpers = cls.root / "helpers.sh"
        cls.helpers.write_text(source[begin:end] + "\n")
        cls.stage = cls.root / "artifacts" / "host" / "stage2"
        cls.stage.mkdir(parents=True)

    @classmethod
    def run_command(cls, command):
        return subprocess.run(command, env=cls.environment, text=True,
                              capture_output=True, timeout=10, check=True)

    def completed(self, state="clean", tracked=0, untracked=0, changed=False):
        empty = hashlib.sha256(b"").hexdigest()
        fields, _ = provenance.source_facts(self.repo)
        del fields["head_short"]  # Diagnostic, not a required authority field.
        fields.update(record_kind="build-stamp", head=self.head,
                      started_at="1700000000", completed_at="1700000010", exit_status="ok",
                      tree_state=state, dirty_tracked=str(tracked), dirty_untracked=str(untracked),
                      diff_sha256=hashlib.sha256(b"diff").hexdigest() if tracked else empty,
                      status_sha256=hashlib.sha256(b"status").hexdigest() if state == "dirty" else empty,
                      )
        fields["tree_fingerprint"] = fingerprint(fields)
        fields["end_tree_fingerprint"] = (
            hashlib.sha256(b"different end tree").hexdigest() if changed
            else fields["tree_fingerprint"])
        fields["tree_changed_during_build"] = "YES" if changed else "no"
        return fields

    def classify(self, text, expected, label, commit=None, directory=False):
        with tempfile.TemporaryDirectory(dir=self.root) as temporary:
            stamp_dir = Path(temporary)
            stamp = stamp_dir / "trust-build-provenance"
            if directory:
                stamp.mkdir()
            elif text is not None:
                stamp.write_text(text)
            shell = '''set -euo pipefail
source "$1"
REPO="$2"; COMMIT="$3"; TRUST_BUILD_PROVENANCE_DIR="$4"
prov_classify "$5"
printf '%s\\n' "$PROV_CLASS" "$PROV_RECORD" "$PROV_REASON"
'''
            result = self.run_command(["bash", "-c", shell, "classifier", str(self.helpers),
                                       str(self.repo), self.head if commit is None else commit,
                                       str(stamp_dir), str(self.stage)])
            lines = result.stdout.splitlines()
            self.observations.append(dict(label=label, expected=expected, actual=lines[0],
                                          reason=lines[2], stdout=result.stdout, stderr=result.stderr))
            if text is not None and not directory:
                self.assertEqual(stamp.read_text(), text, "classification must not alter the stamp")
            self.assertEqual(lines[0], expected, label + ": " + result.stdout)
            # A valid historical v1 record is retained verbatim for historical
            # reading, but cannot acquire recursive clean admission.
            historical = text is not None and "record_version=1\n" in text and "historical v1" in lines[2]
            self.assertEqual(lines[1], "" if expected == "UNVERIFIED-PROVENANCE" and not historical else str(stamp))
            return lines[2]

    def test_completed_clean(self):
        reason = self.classify(record(self.completed()), "BUILD-STAMPED-CLEAN", "completed clean")
        self.assertIn("unchanged when it finished", reason)

    def test_selected_receipt_destination_preflight_refuses_before_any_write(self):
        receipt = self.root / 'accepted-audit.json'
        receipt.write_text('path preflight does not read or accept audit content')
        alias = self.root / 'stage-alias'
        alias.symlink_to(self.stage, target_is_directory=True)
        nested = self.stage / 'must-not-create' / 'trust-fixture'
        good = self.root / 'independent-seal' / 'trust-fixture'
        shell = '''set -euo pipefail
source "$1"
PROMOTER_ROOT="$2"; REPO="$2"; SRC="$3"; COMMIT=""; STAGE_PROVENANCE_RECEIPT="$4"
STAGE_PROVENANCE_SHA=""; DEST="$5"
prov_selected_receipt_action check
'''
        for destination, expected in ((nested, 1), (self.stage.parent, 1),
                                      (alias / 'nested', 1), (good, 0)):
            with self.subTest(destination=destination):
                result = subprocess.run(['bash','-c',shell,'preflight',str(self.helpers),
                    str(SCRIPT.parent.parent),str(self.stage),str(receipt),str(destination)],
                    env=self.environment,text=True,capture_output=True,timeout=10)
                self.assertEqual(result.returncode,expected,result.stderr)
                if expected:
                    self.assertIn('not a distinct new seal',result.stderr)
        self.assertFalse(nested.exists())
        self.assertFalse(good.exists(), 'preflight creates nothing, even on success')
        alias.unlink()

    def test_completed_dirty(self):
        for tracked, untracked in ((1, 0), (0, 2), (3, 4)):
            with self.subTest(tracked=tracked, untracked=untracked):
                reason = self.classify(record(self.completed("dirty", tracked, untracked)),
                                       "BUILD-STAMPED-DIRTY", f"dirty {tracked}/{untracked}")
                self.assertIn(f"{tracked} tracked + {untracked} untracked", reason)

    def test_completed_changed_tree(self):
        for state, tracked in (("clean", 0), ("dirty", 1)):
            with self.subTest(state=state):
                reason = self.classify(record(self.completed(state, tracked, changed=True)),
                                       "BUILD-STAMPED-DIRTY", "changed " + state)
                self.assertIn("CHANGED while the build was running", reason)

    def test_start_only_is_unverified(self):
        fields = self.completed()
        for key in ("completed_at", "exit_status", "end_tree_fingerprint", "tree_changed_during_build"):
            del fields[key]
        self.classify(record(fields), "UNVERIFIED-PROVENANCE", "START only")

    def test_each_required_field_is_required(self):
        for key in self.completed():
            with self.subTest(key=key):
                fields = self.completed()
                del fields[key]
                self.classify(record(fields), "UNVERIFIED-PROVENANCE", "missing " + key)

    def test_failed_or_unknown_completion(self):
        for status in ("failed", "interrupted", "unknown", "signal-15", "exit-101", ""):
            with self.subTest(status=status):
                fields = self.completed()
                fields["exit_status"] = status
                self.classify(record(fields), "UNVERIFIED-PROVENANCE", "exit " + status)

    def test_fingerprint_and_endpoint_contradictions(self):
        mutations = [
            ("tree_fingerprint", "0" * 64),
            ("tree_fingerprint", "short"),
            ("end_tree_fingerprint", "unreadable"),
            ("end_tree_fingerprint", "1" * 64),
            ("diff_sha256", "A" * 64),
            ("status_sha256", "not-a-digest"),
            ("submodule_sha256", ""),
            ("tree_changed_during_build", "YES"),
            ("tree_changed_during_build", "unknown"),
            ("tree_changed_during_build", ""),
        ]
        for key, value in mutations:
            with self.subTest(key=key, value=value):
                fields = self.completed()
                fields[key] = value
                self.classify(record(fields), "UNVERIFIED-PROVENANCE", key + "=" + value)
        fields = self.completed(changed=True)
        fields["tree_changed_during_build"] = "no"
        self.classify(record(fields), "UNVERIFIED-PROVENANCE", "different endpoints/no")

    def test_malformed_and_inconsistent_records(self):
        for key, value in (("record_version", "3"), ("record_kind", "seal"),
                           ("started_at", "x"), ("completed_at", "1699999999"),
                           ("completed_at", "-1"), ("dirty_tracked", "-1"),
                           ("dirty_untracked", "1"), ("tree_state", "unknown")):
            with self.subTest(key=key, value=value):
                fields = self.completed()
                fields[key] = value
                self.classify(record(fields), "UNVERIFIED-PROVENANCE", key + "=" + value)
        with self.subTest(case="dirty with zero counts"):
            fields = self.completed("dirty", 0, 0)
            self.classify(record(fields), "UNVERIFIED-PROVENANCE", "dirty with zero counts")
        with self.subTest(case="coherent hash but dirty clean facts"):
            fields = self.completed()
            fields["diff_sha256"] = hashlib.sha256(b"unreported change").hexdigest()
            fields["tree_fingerprint"] = fingerprint(fields)
            fields["end_tree_fingerprint"] = fields["tree_fingerprint"]
            self.classify(record(fields), "UNVERIFIED-PROVENANCE", "coherent hash but dirty clean facts")
        for suffix in ("head=" + self.head + "\n", "exit_status=ok\n", "broken-line\n"):
            with self.subTest(suffix=suffix):
                self.classify(record(self.completed()) + suffix, "UNVERIFIED-PROVENANCE", suffix.strip())

    def test_missing_unreadable_and_mismatched_record(self):
        self.classify(None, "UNVERIFIED-PROVENANCE", "missing file")
        self.classify(None, "UNVERIFIED-PROVENANCE", "directory at stamp path", directory=True)
        self.classify(record(self.completed()), "UNVERIFIED-PROVENANCE", "different artifact HEAD",
                      commit="0" * 40)
        for head in ("", "short", "A" * 40):
            with self.subTest(head=head):
                fields = self.completed()
                fields["head"] = head
                fields["tree_fingerprint"] = fingerprint(fields)
                fields["end_tree_fingerprint"] = fields["tree_fingerprint"]
                self.classify(record(fields), "UNVERIFIED-PROVENANCE", "invalid matched HEAD " + head,
                              commit=head)

    def test_reused_classifier_does_not_retain_previous_record(self):
        with tempfile.TemporaryDirectory(dir=self.root) as temporary:
            directory = Path(temporary)
            stamp = directory / "trust-build-provenance"
            stamp.write_text(record(self.completed()))
            shell = '''set -euo pipefail
source "$1"
REPO="$2"; COMMIT="$3"; TRUST_BUILD_PROVENANCE_DIR="$4"
prov_classify "$5"
test "$PROV_CLASS" = BUILD-STAMPED-CLEAN
rm "$4/trust-build-provenance"
prov_classify "$5"
printf '%s\\n' "$PROV_CLASS" "$PROV_RECORD"
'''
            result = self.run_command(["bash", "-c", shell, "classifier", str(self.helpers),
                                       str(self.repo), self.head, str(directory), str(self.stage)])
            self.assertEqual(result.stdout, "UNVERIFIED-PROVENANCE\n\n")

    def legacy(self, **kwargs):
        fields = self.completed(**kwargs)
        fields["record_version"] = "1"
        for key in provenance.RECURSIVE_IDENTITY[:3]:
            del fields[key]
        fields["tree_fingerprint"] = fingerprint(fields)
        fields["end_tree_fingerprint"] = fields["tree_fingerprint"]
        return fields

    def test_historical_v1_is_readable_without_recursive_admission(self):
        fields = self.legacy()
        self.assertEqual(provenance.validate_record(record(fields), self.head), fields)
        reason = self.classify(record(fields), "UNVERIFIED-PROVENANCE", "historical v1")
        self.assertIn("only top-level", reason)
        with self.assertRaisesRegex(provenance.ProvenanceError, "only top-level"):
            provenance.require_recursive_source(fields, self.repo)

    def test_legacy_dirty_evidence_keeps_dirty_refusal(self):
        fields = self.legacy(state="dirty", tracked=1)
        self.classify(record(fields), "BUILD-STAMPED-DIRTY", "historical dirty v1")
        with self.assertRaisesRegex(provenance.ProvenanceError, "only top-level"):
            provenance.require_recursive_source(fields, self.repo)

    def test_v1_cannot_claim_v2_scope(self):
        fields = self.legacy()
        fields["submodule_census_scope"] = provenance.CENSUS_SCOPE
        self.classify(record(fields), "UNVERIFIED-PROVENANCE", "forged v1 scope")

    def test_recursive_metadata_mutations_and_rebound_foreign_census_refuse(self):
        for key, value in (("submodule_census_scope", "top-level-only/v1"),
                           ("recursive_submodule_count", "1"),
                           ("recursive_submodule_sha256", "0" * 64)):
            with self.subTest(key=key):
                fields = self.completed()
                fields[key] = value
                self.classify(record(fields), "UNVERIFIED-PROVENANCE", "changed " + key)
                fields["tree_fingerprint"] = fingerprint(fields)
                fields["end_tree_fingerprint"] = fields["tree_fingerprint"]
                self.classify(record(fields), "UNVERIFIED-PROVENANCE", "rebound " + key)

    def test_promotion_requires_live_recursive_source_match(self):
        fields = self.completed()
        changed = self.repo / "changed-after-build"
        changed.write_text("not part of the completed build\n")
        try:
            self.classify(record(fields), "UNVERIFIED-PROVENANCE", "changed live source")
        finally:
            changed.unlink()


if __name__ == "__main__":
    unittest.main()
