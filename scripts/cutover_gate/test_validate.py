"""Adversarial test suite for the trust-ir-cutover gate validator.

Requirement (Track W2): AT LEAST one red fixture per defect in the OPEN
DEFECT REGISTER of docs/plans/2026-07-27-trust-ir-first-cutover.md (rev 4),
plus green fixtures proving SATISFIABILITY — register defect 1's headline is
that the gate as previously written could never turn green, so the green
fixtures here are the proof this one can.

Every test names the register defect (D1-D9) it exercises.

Run:  python3 -m unittest discover -s scripts/cutover_gate -p 'test_*.py'
"""

import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import gate_schema as S  # noqa: E402
import validate  # noqa: E402

# Probe answers for the pre-authority world (phases 0-6): no authority
# capability in the tree, shadow not severed, shadow present.
PROBES_EARLY = {
    "authority_capability_present": "no",
    "shadow_severed": "no",
    "shadow_present": "yes",
}
# Phase-7 world: authority granted, shadow still required.
PROBES_PHASE7 = {
    "authority_capability_present": "yes",
    "shadow_severed": "no",
    "shadow_present": "yes",
}


def sha256_bytes(data):
    return hashlib.sha256(data).hexdigest()


class Repo(object):
    """A throwaway git repository for fixture artifacts."""

    def __init__(self):
        self.dir = tempfile.mkdtemp(prefix="cutover-gate-test-")

        def g(*args):
            subprocess.run(
                ["git", "-C", self.dir] + list(args),
                check=True,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
            )

        self._g = g
        g("init", "-q")
        g("config", "user.email", "gate@test.invalid")
        g("config", "user.name", "gate-test")
        g("config", "commit.gpgsign", "false")

    def write(self, rel, content):
        path = os.path.join(self.dir, rel)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        mode = "wb" if isinstance(content, bytes) else "w"
        with open(path, mode) as fh:
            fh.write(content)
        return path

    def commit(self, msg):
        self._g("add", "-A")
        self._g("commit", "-q", "--allow-empty", "-m", msg)
        out = subprocess.run(
            ["git", "-C", self.dir, "rev-parse", "HEAD"],
            check=True,
            stdout=subprocess.PIPE,
        )
        return out.stdout.decode().strip()

    def cleanup(self):
        shutil.rmtree(self.dir, ignore_errors=True)


def field_desc(repo, rel, content):
    """Write an artifact-field file and return its schema descriptor."""
    repo.write(rel, content)
    data = content if isinstance(content, bytes) else content.encode()
    return {
        "path": rel,
        "sha256": sha256_bytes(data),
        "line_count": len(data.splitlines()),
    }


def make_artifact(repo, phase=0, with_conformance=None, keys=None):
    """The canonical GREEN artifact.  Deliberately includes the exact shape
    rev 4's register proved unsatisfiable: an EMPTY artifact field (the
    lane-a golden) whose floor is 0 and whose recorded digest is the
    empty-file digest [D1]."""
    if with_conformance is None:
        with_conformance = phase >= 2
    if keys is None:
        keys = {
            # D2: the join-residue bound exists only as a MEASURED creation.
            "max_join_residue": {
                "value": 3,
                "first_seen_commit": None,
                "origin": "measured",
            },
            "max_divergences": {
                "value": 1,
                "first_seen_commit": None,
                "origin": "measured",
            },
            "baseline_positive_set": {
                "value": 2,
                "first_seen_commit": None,
                "origin": "measured",
            },
            "fixed_per_function_budget_s": {
                "value": 30,
                "first_seen_commit": None,
                "origin": "declared",
            },
        }
    art = {
        "schema": S.SCHEMA_VERSION,
        "phase_reached": phase,
        "ratchet_base_commit": None,
        "runs_log_head": None,
        "shadow_lane_state": "required" if phase < S.SHADOW_SEVERED_PHASE else "severed",
        "lane_minimums": {
            "A": {"count": 1, "required_from": 0},
            "B": {"count": 1, "required_from": 0},
        },
        "keys": keys,
        "corpora": [
            {
                "id": "lane-a.ui-600",
                "lane": "A",
                "kind": "curated-regression",
                # D1's satisfiability proof: empty field, floor 0, green.
                "artifact_fields": {
                    "golden": field_desc(repo, "ledgers/lane-a.ui-600.golden.jsonl", b"")
                },
                "floors": {"golden": 0},
            },
            {
                "id": "lane-a.realcode",
                "lane": "A",
                "kind": "uncurated-real-code",
                "artifact_fields": {
                    "golden": field_desc(
                        repo, "ledgers/lane-a.realcode.golden.jsonl", '{"row": 1}\n'
                    )
                },
                "floors": {"golden": 1},
            },
            {
                "id": "lane-b.real-spec",
                "lane": "B",
                "kind": "curated-regression",
                "artifact_fields": {
                    "positive_set": field_desc(
                        repo,
                        "ledgers/lane-b.positive.jsonl",
                        '{"fn": "a"}\n{"fn": "b"}\n',
                    )
                },
                "floors": {"positive_set": 2},
            },
        ],
        "oracles": {
            "differential": field_desc(
                repo, "ledgers/differential.cases", '{"case": "issue-43806"}\n'
            )
        },
    }
    if with_conformance:
        art["oracles"]["conformance"] = field_desc(
            repo, "ledgers/conformance.cases", '{"expect": "pre-authored"}\n'
        )
    return art


def write_log(path, entries):
    """Fabricate a correctly hash-chained runner's log."""
    raw = []
    prev = "genesis"
    for i, entry in enumerate(entries):
        rec = {
            "seq": i,
            "prev": prev,
            "commit": entry.get("commit", "deadbeef"),
            "utc": entry.get("utc", "2026-07-28T00:00:00Z"),
            "verdict": entry.get("verdict", "green"),
            "failed": entry.get("failed", []),
        }
        line = json.dumps(rec, sort_keys=True).encode()
        raw.append(line)
        prev = sha256_bytes(line)
    with open(path, "wb") as fh:
        for line in raw:
            fh.write(line + b"\n")


class GateCase(unittest.TestCase):
    def setUp(self):
        self.repo = Repo()
        self.addCleanup(self.repo.cleanup)
        self.aux = tempfile.mkdtemp(prefix="cutover-gate-aux-")
        self.addCleanup(shutil.rmtree, self.aux, True)
        self.log = os.path.join(self.aux, "runs.log")

    # -- driver ---------------------------------------------------------
    def run_gate(self, artifact, previous=None, probes=PROBES_EARLY,
                 artifact_rel="gate.json", log=None):
        art_path = self.repo.write(artifact_rel, json.dumps(artifact, indent=1))
        argv = [
            "--artifact", art_path,
            "--repo", self.repo.dir,
            "--runs-log", log or self.log,
            "--verdict-file", os.path.join(self.aux, "verdict.json"),
        ]
        if previous is not None:
            prev_path = os.path.join(self.aux, "previous.json")
            with open(prev_path, "w") as fh:
                json.dump(previous, fh)
            argv += ["--previous", prev_path]
        if probes is not None:
            probes_path = os.path.join(self.aux, "probes.json")
            with open(probes_path, "w") as fh:
                json.dump(probes, fh)
            argv += ["--probes", probes_path]
        rc = validate.main(argv)
        with open(os.path.join(self.aux, "verdict.json")) as fh:
            verdict = json.load(fh)
        return rc, verdict

    def status_of(self, verdict, cid):
        for row in verdict["conjuncts"]:
            if row["id"] == cid:
                return row["status"], row["detail"]
        raise AssertionError("conjunct %s missing from verdict" % cid)

    def assert_red(self, rc, verdict, cid, detail_contains=None):
        self.assertEqual(rc, 1, "expected gate RED")
        status, detail = self.status_of(verdict, cid)
        self.assertNotEqual(status, "green",
                            "%s expected red/unevaluable, got green: %s" % (cid, detail))
        if detail_contains:
            self.assertIn(detail_contains, detail)

    def two_run_green(self):
        """Genesis green run at C1, then a pinned second green run at C2.
        Returns (v1, v2, c1, c2, head1) with the log holding two green
        records."""
        v1 = make_artifact(self.repo)
        self.repo.write("gate.json", json.dumps(v1, indent=1))
        c1 = self.repo.commit("genesis gate artifact")
        rc, verdict = self.run_gate(v1)
        self.assertEqual(rc, 0, "genesis run must be green: %s"
                         % [r for r in verdict["conjuncts"] if r["status"] != "green"])
        head1 = verdict["new_log_head"]
        v2 = json.loads(json.dumps(v1))
        for key in v2["keys"]:
            v2["keys"][key]["first_seen_commit"] = c1
        v2["ratchet_base_commit"] = c1
        v2["runs_log_head"] = head1
        self.repo.write("gate.json", json.dumps(v2, indent=1))
        c2 = self.repo.commit("second gate artifact: pins + base + log head")
        rc2, verdict2 = self.run_gate(v2, previous=v1)
        self.assertEqual(rc2, 0, "second run must be green: %s"
                         % [r for r in verdict2["conjuncts"] if r["status"] != "green"])
        return v1, v2, c1, c2, head1


# =======================================================================
# GREEN — satisfiability (register defect 1's meta-point: the prose gate
# was UNSATISFIABLE; these prove the executable gate is not)
# =======================================================================

class TestGreen(GateCase):
    def test_green_genesis_including_required_empty_field(self):
        """[D1 green] The exact shape rev 4 proved unsatisfiable — a
        required-EMPTY artifact field — is green here: exists, hash-matches
        the empty-file digest, floor 0."""
        art = make_artifact(self.repo)
        self.repo.write("gate.json", json.dumps(art, indent=1))
        self.repo.commit("genesis")
        rc, verdict = self.run_gate(art)
        self.assertEqual(rc, 0, [r for r in verdict["conjuncts"] if r["status"] != "green"])
        self.assertEqual(verdict["verdict"], "green")
        # the empty golden really is empty and really is the empty digest
        golden = art["corpora"][0]["artifact_fields"]["golden"]
        self.assertEqual(golden["line_count"], 0)
        self.assertEqual(golden["sha256"], S.EMPTY_SHA256)

    def test_green_second_run_with_pins_base_and_log_head(self):
        """[D4/D5/D6 green] Pinned first_seen commits, ratchet base = last
        green run's commit, and the recorded log head all validate."""
        self.two_run_green()

    def test_green_phase7_authority_present(self):
        """[D3 green] The biconditional's satisfied side: authority in the
        tree AND phase_reached == 7."""
        art = make_artifact(self.repo, phase=7)
        self.repo.write("gate.json", json.dumps(art, indent=1))
        self.repo.commit("phase 7 world")
        rc, verdict = self.run_gate(art, probes=PROBES_PHASE7)
        self.assertEqual(rc, 0, [r for r in verdict["conjuncts"] if r["status"] != "green"])

    def test_green_conformance_present_at_phase2(self):
        """[D9 green] The A18 oracle live in its window."""
        art = make_artifact(self.repo, phase=2, with_conformance=True)
        self.repo.write("gate.json", json.dumps(art, indent=1))
        self.repo.commit("phase 2 world")
        rc, verdict = self.run_gate(art)
        self.assertEqual(rc, 0, [r for r in verdict["conjuncts"] if r["status"] != "green"])


# =======================================================================
# D1 — A15 vs zero-targets (exists-and-hash-matches; non-empty only where
# a floor > 0)
# =======================================================================

class TestD1ArtifactFields(GateCase):
    def test_red_artifact_field_file_missing(self):
        art = make_artifact(self.repo)
        os.remove(os.path.join(self.repo.dir, "ledgers/lane-b.positive.jsonl"))
        rc, verdict = self.run_gate(art)
        self.assert_red(rc, verdict, "V-A15", "file missing")

    def test_red_artifact_field_hash_mismatch(self):
        art = make_artifact(self.repo)
        self.repo.write("ledgers/lane-b.positive.jsonl", '{"fn": "swapped"}\n{"fn": "b"}\n')
        rc, verdict = self.run_gate(art)
        self.assert_red(rc, verdict, "V-A15", "sha256 mismatch")

    def test_red_empty_file_under_positive_floor(self):
        """Non-empty IS demanded where the floor is > 0."""
        art = make_artifact(self.repo)
        self.repo.write("ledgers/lane-a.realcode.golden.jsonl", b"")
        art["corpora"][1]["artifact_fields"]["golden"]["sha256"] = S.EMPTY_SHA256
        art["corpora"][1]["artifact_fields"]["golden"]["line_count"] = 0
        rc, verdict = self.run_gate(art)
        self.assert_red(rc, verdict, "V-A15", "below floor")


# =======================================================================
# D2 — max_join_residue must be created from the MEASURED residue
# =======================================================================

class TestD2JoinResidue(GateCase):
    def test_red_hardcoded_zero_before_measurement(self):
        art = make_artifact(self.repo)
        art["keys"]["max_join_residue"] = {
            "value": 0, "first_seen_commit": None, "origin": "declared",
        }
        rc, verdict = self.run_gate(art)
        self.assert_red(rc, verdict, "V-JOIN-RESIDUE", "measured")

    def test_red_join_residue_bound_raised(self):
        """The ratchet direction: once created it only goes down."""
        prev = make_artifact(self.repo)
        art = make_artifact(self.repo)
        art["keys"]["max_join_residue"]["value"] = 5  # prev was 3
        rc, verdict = self.run_gate(art, previous=prev)
        self.assert_red(rc, verdict, "V-POLARITY", "max_* raised")


# =======================================================================
# D3 — phase_reached is a structural biconditional against tree state
# =======================================================================

class TestD3PhaseTree(GateCase):
    def test_red_phase7_with_authority_probe_absent(self):
        art = make_artifact(self.repo, phase=7)
        probes = dict(PROBES_PHASE7, authority_capability_present="no")
        rc, verdict = self.run_gate(art, probes=probes)
        self.assert_red(rc, verdict, "V-PHASE-TREE", "authority capability absent")

    def test_red_authority_landed_while_phase_says_6(self):
        """The register's own scenario: authority-granting code lands while
        the field says 6."""
        art = make_artifact(self.repo, phase=6, with_conformance=True)
        rc, verdict = self.run_gate(art, probes=PROBES_PHASE7)
        self.assert_red(rc, verdict, "V-PHASE-TREE", "phase_reached 6")

    def test_red_probe_unavailable_is_fail_closed(self):
        art = make_artifact(self.repo)
        rc, verdict = self.run_gate(art, probes={})
        self.assertEqual(rc, 1)
        status, detail = self.status_of(verdict, "V-PHASE-TREE")
        self.assertEqual(status, "unevaluable")
        self.assertIn("fail-closed", detail)


# =======================================================================
# D4 — first_seen_commit immutability + absence-at-parent
# =======================================================================

class TestD4KeyCensus(GateCase):
    def test_red_first_seen_commit_mutated(self):
        _, v2, c1, c2, _ = self.two_run_green()
        v3 = json.loads(json.dumps(v2))
        v3["keys"]["max_divergences"]["first_seen_commit"] = c2  # relabel
        v3["ratchet_base_commit"] = c2  # keep base honest so only D4 fires
        rc, verdict = self.run_gate(v3, previous=v2)
        self.assert_red(rc, verdict, "V-KEY-CENSUS", "mutated")

    def test_red_new_pin_but_key_present_at_parent(self):
        """A pin claiming creation at C2 while the key already existed at C1
        relabels a relaxation as a creation — RED via the git check."""
        v1 = make_artifact(self.repo)
        self.repo.write("gate.json", json.dumps(v1, indent=1))
        self.repo.commit("artifact with key, pin still null")  # C1
        self.repo.write("unrelated.txt", "x\n")
        c2 = self.repo.commit("unrelated change")  # C2 (parent C1 has the key)
        v2 = json.loads(json.dumps(v1))
        for key in v2["keys"]:
            v2["keys"][key]["first_seen_commit"] = c2
        rc, verdict = self.run_gate(v2, previous=v1)
        self.assert_red(rc, verdict, "V-KEY-CENSUS", "already present")


# =======================================================================
# D5 — ratchet_base_commit: descendant of prior base, equal to the last
# green run's commit
# =======================================================================

class TestD5RatchetBase(GateCase):
    def test_red_base_not_last_green_runs_commit(self):
        v1 = make_artifact(self.repo)
        self.repo.write("gate.json", json.dumps(v1, indent=1))
        c1 = self.repo.commit("genesis")
        rc0, _ = self.run_gate(v1)
        self.assertEqual(rc0, 0)
        v2 = json.loads(json.dumps(v1))
        for key in v2["keys"]:
            v2["keys"][key]["first_seen_commit"] = c1
        v2["ratchet_base_commit"] = None  # log says the last green was c1
        rc, verdict = self.run_gate(v2, previous=v1)
        self.assert_red(rc, verdict, "V-RATCHET-BASE", "last green run")

    def test_red_base_moved_backwards(self):
        self.repo.write("f.txt", "1\n")
        c1 = self.repo.commit("c1")
        self.repo.write("f.txt", "2\n")
        c2 = self.repo.commit("c2")
        art = make_artifact(self.repo, keys={})
        prev = json.loads(json.dumps(art))
        prev["ratchet_base_commit"] = c2  # previously accepted base
        art["ratchet_base_commit"] = c1  # attacker rolls it back
        write_log(self.log, [
            {"commit": c2, "verdict": "green"},
            {"commit": c1, "verdict": "green"},  # replayed old run
        ])
        rc, verdict = self.run_gate(art, previous=prev)
        self.assert_red(rc, verdict, "V-RATCHET-BASE", "backwards")


# =======================================================================
# D6 — the soak reads the runner's own append-only log
# =======================================================================

class TestD6SoakLog(GateCase):
    def test_red_author_provided_soak_list_rejected(self):
        art = make_artifact(self.repo)
        art["soak_runs"] = [{"verdict": "green"}] * 8  # a typed-in soak
        rc, verdict = self.run_gate(art)
        self.assert_red(rc, verdict, "V-SOAK-LOG", "REJECTED")

    def test_red_log_chain_tampered(self):
        _, v2, _, _, _ = self.two_run_green()
        with open(self.log, "rb") as fh:
            lines = fh.read().splitlines()
        lines[0] = lines[0].replace(b'"green"', b'"greee"', 1)  # edit history
        with open(self.log, "wb") as fh:
            fh.write(b"\n".join(lines) + b"\n")
        rc, verdict = self.run_gate(v2, previous=v2)
        self.assert_red(rc, verdict, "V-SOAK-LOG", "log integrity")

    def test_red_log_truncated_below_recorded_head(self):
        _, v2, _, _, _ = self.two_run_green()
        with open(self.log, "wb"):
            pass  # delete every recorded run
        rc, verdict = self.run_gate(v2, previous=v2)
        self.assert_red(rc, verdict, "V-SOAK-LOG", "truncated")

    def test_red_run_is_recorded_too(self):
        """The discipline itself: EVERY run — red included — appends a
        record.  'Only green runs get recorded' was the defect."""
        art = make_artifact(self.repo)
        os.remove(os.path.join(self.repo.dir, "ledgers/differential.cases"))
        rc, _ = self.run_gate(art)
        self.assertEqual(rc, 1)
        with open(self.log, "rb") as fh:
            lines = fh.read().splitlines()
        self.assertEqual(len(lines), 1)
        rec = json.loads(lines[0])
        self.assertEqual(rec["verdict"], "red")
        self.assertIn("V-ORACLE", rec["failed"])


# =======================================================================
# D7 — lane vacuation: a never-zero lane-A floor + lane/kind immutability
# =======================================================================

class TestD7LaneFloor(GateCase):
    def test_red_flip_both_lane_a_entries_to_b(self):
        art = make_artifact(self.repo)
        for corpus in art["corpora"]:
            if corpus["lane"] == "A":
                corpus["lane"] = "B"  # the one-word relabel attack
        rc, verdict = self.run_gate(art)
        self.assert_red(rc, verdict, "V-LANE-FLOOR", "bound minimum")

    def test_red_lane_relabel_against_previous_census(self):
        prev = make_artifact(self.repo)
        art = make_artifact(self.repo)
        art["corpora"][0]["lane"] = "B"
        rc, verdict = self.run_gate(art, previous=prev)
        self.assert_red(rc, verdict, "V-LANE-FLOOR", "immutable")

    def test_red_lane_a_minimum_zeroed(self):
        art = make_artifact(self.repo)
        art["lane_minimums"]["A"]["count"] = 0  # "configurable" abused to 0
        rc, verdict = self.run_gate(art)
        self.assert_red(rc, verdict, "V-LANE-FLOOR", "never zero")


# =======================================================================
# D8 — the shadow obligation is phase-conditioned, not deletable
# =======================================================================

class TestD8Shadow(GateCase):
    def test_red_severed_before_licensing_phase(self):
        art = make_artifact(self.repo)
        art["shadow_lane_state"] = "severed"  # at phase 0
        rc, verdict = self.run_gate(art)
        self.assert_red(rc, verdict, "V-SHADOW", "licensed only at phase")

    def test_red_shadow_deleted_pre_phase8(self):
        """Deleting the shadow does NOT discharge the obligation vacuously —
        the register's H2 attack."""
        art = make_artifact(self.repo)
        probes = dict(PROBES_EARLY, shadow_present="no")
        rc, verdict = self.run_gate(art, probes=probes)
        self.assert_red(rc, verdict, "V-SHADOW", "deleted")


# =======================================================================
# D9 — the oracle is a REQUIRED artifact until the phase that retires it
# =======================================================================

class TestD9Oracle(GateCase):
    def test_red_differential_oracle_dropped(self):
        art = make_artifact(self.repo)
        del art["oracles"]["differential"]
        rc, verdict = self.run_gate(art)
        self.assert_red(rc, verdict, "V-ORACLE", "REQUIRED")

    def test_red_conformance_missing_inside_its_window(self):
        art = make_artifact(self.repo, phase=2, with_conformance=False)
        rc, verdict = self.run_gate(art)
        self.assert_red(rc, verdict, "V-ORACLE", "conformance")

    def test_red_conformance_gone_trivial(self):
        """Section 6 row 16: nobody notices the last oracle going trivial —
        here an emptied conformance corpus is RED, not quiet."""
        art = make_artifact(self.repo, phase=2, with_conformance=True)
        self.repo.write("ledgers/conformance.cases", b"")
        art["oracles"]["conformance"]["sha256"] = S.EMPTY_SHA256
        art["oracles"]["conformance"]["line_count"] = 0
        rc, verdict = self.run_gate(art)
        self.assert_red(rc, verdict, "V-ORACLE", "empty")


# =======================================================================
# check 7 / vacuity_floor class — polarity by pinned prefix
# =======================================================================

class TestPolarityAndSchema(GateCase):
    def test_red_key_matching_no_prefix(self):
        """rev 3's vacuity_floor: a numeric key matching no polarity prefix
        was audited by nothing.  Here it FAILS outright."""
        art = make_artifact(self.repo)
        art["keys"]["vacuity_floor"] = {
            "value": 20, "first_seen_commit": None, "origin": "declared",
        }
        rc, verdict = self.run_gate(art)
        self.assert_red(rc, verdict, "V-POLARITY", "no polarity prefix")

    def test_red_baseline_lowered(self):
        prev = make_artifact(self.repo)
        art = make_artifact(self.repo)
        art["keys"]["baseline_positive_set"]["value"] = 1  # 2 -> 1
        rc, verdict = self.run_gate(art, previous=prev)
        self.assert_red(rc, verdict, "V-POLARITY", "lowered")

    def test_red_unknown_top_level_key(self):
        art = make_artifact(self.repo)
        art["surprise_extension"] = {}
        rc, verdict = self.run_gate(art)
        self.assert_red(rc, verdict, "V-SCHEMA", "unknown top-level keys")


# =======================================================================
# census meta-test: every register defect has a mapped conjunct and every
# conjunct id in the schema census is implemented (X7's spirit)
# =======================================================================

class TestCensus(unittest.TestCase):
    def test_every_register_defect_is_mapped(self):
        mapped = set()
        for meta in S.CONJUNCTS.values():
            mapped.update(meta["defects"])
        self.assertEqual(
            {"D%d" % i for i in range(1, 10)} - mapped, set(),
            "register defects with no owning conjunct",
        )

    def test_conjunct_census_matches_implementation(self):
        implemented = {cid for cid, _ in validate.CONJUNCT_FNS}
        self.assertEqual(implemented, set(S.CONJUNCTS))


if __name__ == "__main__":
    unittest.main()
