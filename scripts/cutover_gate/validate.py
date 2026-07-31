#!/usr/bin/env python3
"""trust-ir-cutover gate validator.

Executable form of the gate demanded by the OPEN DEFECT REGISTER of
docs/plans/2026-07-27-trust-ir-first-cutover.md (rev 4).  See gate_schema.py
for the full documented schema and the conjunct -> defect / plan-conjunct
census.

Usage:
  python3 validate.py --artifact GATE.json --repo REPO --runs-log runs.log \
      [--previous PREV.json] [--probes probes.json] \
      [--artifact-relpath PATH] [--verdict-file OUT.json]

Exit 0 iff every conjunct is green; 1 otherwise.  One row is printed per
conjunct: id, status (green | red | unevaluable), detail, and the register
defect / plan ids it maps to.  Per section 3.-0.5 rule 1, "unevaluable" is a
reported status but a RED outcome — never a skip.

Run discipline (register defect D6): this validator appends a record to the
runner's append-only, hash-chained log on EVERY run — red or green — before
emitting its decision.  The soak is computed only from that log.
"""

import argparse
import datetime
import hashlib
import json
import os
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gate_schema as S  # noqa: E402

GREEN = "green"
RED = "red"
UNEVALUABLE = "unevaluable"  # reported distinctly; a RED outcome (rule 1)


# ---------------------------------------------------------------------------
# small helpers
# ---------------------------------------------------------------------------

def sha256_bytes(data):
    return hashlib.sha256(data).hexdigest()


def sha256_file(path):
    with open(path, "rb") as fh:
        return sha256_bytes(fh.read())


def line_count_file(path):
    with open(path, "rb") as fh:
        return len(fh.read().splitlines())


def git(repo, *args):
    proc = subprocess.run(
        ["git", "-C", repo] + list(args),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    return proc.returncode, proc.stdout.decode("utf-8", "replace").strip()


def git_head(repo):
    rc, out = git(repo, "rev-parse", "HEAD")
    return out if rc == 0 else None


def git_is_ancestor(repo, ancestor, descendant):
    rc, _ = git(repo, "merge-base", "--is-ancestor", ancestor, descendant)
    return rc == 0


def git_show_json(repo, rev, relpath):
    """Artifact JSON at rev:relpath, or None if absent/unparseable."""
    rc, out = git(repo, "show", "%s:%s" % (rev, relpath))
    if rc != 0:
        return None
    try:
        return json.loads(out)
    except ValueError:
        return None


def is_number(v):
    return isinstance(v, (int, float)) and not isinstance(v, bool)


# ---------------------------------------------------------------------------
# runner's log (D6): hash-chained, append-only, appended on every run
# ---------------------------------------------------------------------------

def read_log(path):
    """Return (records, raw_lines, chain_ok, detail)."""
    if not os.path.exists(path):
        return [], [], True, "log absent (genesis)"
    with open(path, "rb") as fh:
        raw = fh.read().splitlines()
    records = []
    prev_hash = "genesis"
    for i, line in enumerate(raw):
        try:
            rec = json.loads(line.decode("utf-8"))
        except ValueError:
            return records, raw, False, "line %d is not JSON" % i
        if rec.get("seq") != i:
            return records, raw, False, "line %d carries seq %r" % (i, rec.get("seq"))
        if rec.get("prev") != prev_hash:
            return records, raw, False, "line %d breaks the hash chain" % i
        prev_hash = sha256_bytes(line)
        records.append(rec)
    return records, raw, True, "chain intact (%d records)" % len(records)


def append_log(path, raw_lines, commit, verdict, failed):
    prev_hash = sha256_bytes(raw_lines[-1]) if raw_lines else "genesis"
    rec = {
        "seq": len(raw_lines),
        "prev": prev_hash,
        "commit": commit,
        "utc": datetime.datetime.utcnow().replace(microsecond=0).isoformat() + "Z",
        "verdict": verdict,
        "failed": sorted(failed),
    }
    line = json.dumps(rec, sort_keys=True)
    with open(path, "ab") as fh:
        fh.write(line.encode("utf-8") + b"\n")
    return {"seq": rec["seq"], "sha256": sha256_bytes(line.encode("utf-8"))}


def trailing_green(records):
    """Soak status: trailing consecutive green runs on distinct commits.
    Computed ONLY from the runner's log (D6); informational — consumed by
    phase gates, never by a conjunct (section 3.8.1 acyclicity)."""
    n = 0
    commits = set()
    for rec in reversed(records):
        if rec.get("verdict") != GREEN:
            break
        if rec.get("commit") in commits:
            continue
        commits.add(rec.get("commit"))
        n += 1
    return n


# ---------------------------------------------------------------------------
# conjuncts — each returns (status, detail) and names its ids in comments
# ---------------------------------------------------------------------------

def c_schema(ctx):
    """V-SCHEMA [section 5.4 check 1]: closed schema, exact version."""
    art = ctx["artifact"]
    if not isinstance(art, dict):
        return RED, "artifact is not a JSON object"
    if art.get("schema") != S.SCHEMA_VERSION:
        return RED, "schema %r != %r" % (art.get("schema"), S.SCHEMA_VERSION)
    # D6's author-soak rejection is reported by V-SOAK-LOG; here the closed
    # key set catches EVERY unknown key, soak-shaped or otherwise.
    unknown = set(art) - S.TOP_LEVEL_KEYS
    unknown_non_soak = unknown - S.FORBIDDEN_SOAK_KEYS
    if unknown_non_soak:
        return RED, "unknown top-level keys: %s" % sorted(unknown_non_soak)
    if unknown & S.FORBIDDEN_SOAK_KEYS:
        # leave the named failure to V-SOAK-LOG [D6]
        pass
    for req in ("phase_reached", "shadow_lane_state", "lane_minimums", "keys",
                "corpora", "oracles"):
        if req not in art:
            return RED, "missing required key %r" % req
    if not isinstance(art["phase_reached"], int) or art["phase_reached"] < 0:
        return RED, "phase_reached must be a non-negative integer"
    if art["shadow_lane_state"] not in ("required", "severed"):
        return RED, "shadow_lane_state %r invalid" % art["shadow_lane_state"]
    return GREEN, "schema %s; keys closed" % S.SCHEMA_VERSION


def c_a15(ctx):
    """V-A15 [D1; A15/B1.13/section 3.1.1/check 9]: artifact-field integrity.

    Register defect 1's fix shape, verbatim: "exists and hash-matches" for
    ALL fields; "non-empty" only where a baseline floor > 0; an empty
    artifact hashes to the empty-file digest rather than failing.
    """
    art = ctx["artifact"]
    repo = ctx["repo"]
    problems = []
    for corpus in art.get("corpora", []):
        cid = corpus.get("id", "<no id>")
        floors = corpus.get("floors", {})
        fields = corpus.get("artifact_fields", {})
        for fname, fdesc in sorted(fields.items()):
            path = os.path.join(repo, fdesc.get("path", ""))
            if not os.path.isfile(path):
                problems.append("%s.%s: file missing (%s)" % (cid, fname, fdesc.get("path")))
                continue
            actual_sha = sha256_file(path)
            if actual_sha != fdesc.get("sha256"):
                problems.append("%s.%s: sha256 mismatch (recorded %s, actual %s)"
                                % (cid, fname, fdesc.get("sha256"), actual_sha))
            actual_lines = line_count_file(path)
            if actual_lines != fdesc.get("line_count"):
                problems.append("%s.%s: line_count mismatch (recorded %r, actual %d)"
                                % (cid, fname, fdesc.get("line_count"), actual_lines))
            floor = floors.get(fname, 0)
            if actual_lines < floor:
                # non-empty / floor demand ONLY where floor > 0 [D1]
                problems.append("%s.%s: %d lines below floor %d"
                                % (cid, fname, actual_lines, floor))
            if actual_lines == 0 and actual_sha != S.EMPTY_SHA256:
                problems.append("%s.%s: empty by lines but not the empty-file digest"
                                % (cid, fname))
    if problems:
        return RED, "; ".join(problems)
    return GREEN, "all artifact fields exist and hash-match (empty-with-zero-floor is green)"


def c_join_residue(ctx):
    """V-JOIN-RESIDUE [D2; section 3.0.1 / item 0.12]: max_join_residue is
    created at item 0.12 from the MEASURED residue and only then ratchets
    down.  A pre-measurement hardcoded value (origin != "measured") is RED —
    never a typed-in 0."""
    keys = ctx["artifact"].get("keys", {})
    problems = []
    for name in sorted(S.MEASURED_CREATION_KEYS & set(keys)):
        origin = keys[name].get("origin")
        if origin != "measured":
            problems.append("%s: origin %r — the bound must be CREATED from a "
                            "measured residue, not declared" % (name, origin))
    if problems:
        return RED, "; ".join(problems)
    present = sorted(S.MEASURED_CREATION_KEYS & set(keys))
    if present:
        return GREEN, "measured-creation keys carry origin=measured: %s" % present
    return GREEN, "no measured-creation key exists yet (legal before item 0.12)"


def c_phase_tree(ctx):
    """V-PHASE-TREE [D3; section 3.-0.5 rule 4 / P7.3]: phase_reached is a
    structural biconditional against tree state, monotone, fail-closed on an
    unavailable probe."""
    art = ctx["artifact"]
    prev = ctx["previous"]
    probes = ctx["probes"]
    phase = art["phase_reached"]
    problems = []
    if prev is not None and phase < prev.get("phase_reached", 0):
        problems.append("phase_reached %d < previous %d (may only increase)"
                        % (phase, prev.get("phase_reached", 0)))

    def probe(name):
        ans = probes.get(name, "unavailable")
        if ans not in S.PROBE_ANSWERS:
            return "unavailable"
        return ans

    auth = probe("authority_capability_present")
    sev = probe("shadow_severed")
    if auth == "unavailable":
        problems.append("probe authority_capability_present unavailable => RED (fail-closed)")
    if sev == "unavailable":
        problems.append("probe shadow_severed unavailable => RED (fail-closed)")
    # authority capability present <=> phase >= 7  [D3 fix shape, verbatim]
    if auth == "yes" and phase < S.AUTHORITY_PHASE:
        problems.append("authority capability present in tree but phase_reached "
                        "%d < %d" % (phase, S.AUTHORITY_PHASE))
    if auth == "no" and phase >= S.AUTHORITY_PHASE:
        problems.append("phase_reached %d >= %d but authority capability absent "
                        "from tree" % (phase, S.AUTHORITY_PHASE))
    # shadow severed <=> phase >= 8  [D3 fix shape, verbatim]
    if sev == "yes" and phase < S.SHADOW_SEVERED_PHASE:
        problems.append("shadow severed in tree but phase_reached %d < %d"
                        % (phase, S.SHADOW_SEVERED_PHASE))
    if sev == "no" and phase >= S.SHADOW_SEVERED_PHASE:
        problems.append("phase_reached %d >= %d but shadow not severed"
                        % (phase, S.SHADOW_SEVERED_PHASE))
    if problems:
        status = UNEVALUABLE if any("unavailable" in p for p in problems) else RED
        return status, "; ".join(problems)
    return GREEN, "phase %d consistent with tree probes (auth=%s, severed=%s)" % (phase, auth, sev)


def c_key_census(ctx):
    """V-KEY-CENSUS [D4; section 3.5 item 2 / check 12]: first_seen_commit is
    immutable against the prior census; a new pin is verified by git —
    present at the pinned commit, ABSENT at its parent; the key set may only
    grow (a rename is a removal plus an addition)."""
    art = ctx["artifact"]
    prev = ctx["previous"]
    repo = ctx["repo"]
    relpath = ctx["artifact_relpath"]
    head = ctx["head"]
    keys = art.get("keys", {})
    prev_keys = (prev or {}).get("keys", {})
    problems = []

    missing = set(prev_keys) - set(keys)
    if missing:
        problems.append("keys removed from census (needs retirement, none modeled "
                        "in v1): %s" % sorted(missing))

    for name in sorted(keys):
        fsc = keys[name].get("first_seen_commit")
        in_prev = name in prev_keys
        if in_prev:
            prev_fsc = prev_keys[name].get("first_seen_commit")
            if prev_fsc is not None:
                if fsc != prev_fsc:
                    problems.append("%s: first_seen_commit mutated %r -> %r"
                                    % (name, prev_fsc, fsc))
                continue
            # previously null: THIS run must pin it (creation record overdue
            # otherwise), and the pin is git-verified below.
            if fsc is None:
                problems.append("%s: first_seen_commit still null one run after "
                                "creation (pin overdue)" % name)
                continue
        else:
            # brand-new key: null allowed for exactly one run.
            if fsc is None:
                continue
        # verify a (newly) pinned first_seen_commit against git [D4]
        if head is None:
            problems.append("%s: git HEAD unavailable, pin unverifiable" % name)
            continue
        rc, _ = git(repo, "rev-parse", "--verify", "%s^{commit}" % fsc)
        if rc != 0:
            problems.append("%s: first_seen_commit %r is not a commit" % (name, fsc))
            continue
        if not git_is_ancestor(repo, fsc, head):
            problems.append("%s: first_seen_commit %s is not an ancestor of HEAD"
                            % (name, fsc))
            continue
        at_c = git_show_json(repo, fsc, relpath)
        if at_c is None or name not in at_c.get("keys", {}):
            problems.append("%s: absent from the artifact at its claimed "
                            "first_seen_commit %s" % (name, fsc))
            continue
        at_parent = git_show_json(repo, "%s^" % fsc, relpath)
        if at_parent is not None and name in at_parent.get("keys", {}):
            problems.append("%s: already present at %s^ — claimed creation "
                            "relabels history (the polarity-exemption laundering "
                            "attack)" % (name, fsc))
    if problems:
        return RED, "; ".join(problems)
    return GREEN, "census intact: %d keys, pins immutable and git-verified" % len(keys)


def c_ratchet_base(ctx):
    """V-RATCHET-BASE [D5; section 3.5 item 1 / check 3]: ratchet_base_commit
    equals the last green run's commit (from the runner's log) and descends
    from the previously recorded base."""
    art = ctx["artifact"]
    prev = ctx["previous"]
    repo = ctx["repo"]
    base = art.get("ratchet_base_commit")
    prev_base = (prev or {}).get("ratchet_base_commit")
    if not ctx["log_chain_ok"]:
        return UNEVALUABLE, "runner's log unreadable — base cannot be established"
    greens = [r for r in ctx["log_records"] if r.get("verdict") == GREEN]
    problems = []
    if greens:
        last_green_commit = greens[-1].get("commit")
        if base != last_green_commit:
            problems.append("ratchet_base_commit %r != last green run's commit %r"
                            % (base, last_green_commit))
    else:
        if base != prev_base:
            problems.append("no green run recorded; base must carry forward "
                            "previous value %r, got %r" % (prev_base, base))
    if prev_base is not None:
        if base is None:
            problems.append("base regressed to null from %r" % prev_base)
        elif base != prev_base and not git_is_ancestor(repo, prev_base, base):
            problems.append("base %r is not a descendant of previously recorded "
                            "base %r (backwards move)" % (base, prev_base))
    if problems:
        return RED, "; ".join(problems)
    return GREEN, "base %r consistent with log and prior base" % base


def c_soak_log(ctx):
    """V-SOAK-LOG [D6; section 3.8.1 / section 3.5 item 8 / check 13]: the
    soak reads the RUNNER's append-only hash-chained log; the previously
    recorded head must still be present (prefix rule); an author-provided
    soak list is rejected."""
    art = ctx["artifact"]
    prev = ctx["previous"]
    problems = []
    soak_keys = set(art) & S.FORBIDDEN_SOAK_KEYS
    if soak_keys:
        problems.append("author-provided soak field(s) REJECTED: %s — the soak "
                        "is computed from the runner's log only" % sorted(soak_keys))
    if not ctx["log_chain_ok"]:
        problems.append("log integrity: %s" % ctx["log_chain_detail"])
    # both the previous and the current recorded heads must still resolve in
    # the log — deleting or rewriting history below either is detected.
    for label, rec in (("previous", (prev or {}).get("runs_log_head")),
                       ("current", art.get("runs_log_head"))):
        if rec is None:
            continue
        seq = rec.get("seq")
        want = rec.get("sha256")
        raw = ctx["log_raw"]
        if not isinstance(seq, int) or seq < 0 or seq >= len(raw):
            problems.append("%s runs_log_head seq %r not present in log "
                            "(truncated or rewritten)" % (label, seq))
            continue
        if sha256_bytes(raw[seq]) != want:
            problems.append("%s runs_log_head hash mismatch at seq %d "
                            "(history edited)" % (label, seq))
    if problems:
        return RED, "; ".join(problems)
    return GREEN, "log append-only and chain-intact; trailing green (distinct " \
                  "commits): %d of %d needed" % (ctx["soak_trailing_green"], S.SOAK_RUNS)


def c_lane_floor(ctx):
    """V-LANE-FLOOR [D7; section 3.1.2 / X4 / X4a]: a configurable, never-zero
    lane-A floor; bound minimums are met; lane/kind immutable once accepted.
    Closes the one-word relabel attack: flipping lane-A entries to B is a
    shortfall FAILURE, never an empty quantification."""
    art = ctx["artifact"]
    prev = ctx["previous"]
    phase = art["phase_reached"]
    minimums = art.get("lane_minimums", {})
    corpora = art.get("corpora", [])
    problems = []
    a_min = minimums.get("A")
    if not a_min:
        problems.append("lane_minimums has no 'A' entry (the floor may be "
                        "configured, never removed)")
    elif not isinstance(a_min.get("count"), int) or a_min["count"] < 1:
        problems.append("lane_minimums['A'].count %r < 1 (configurable but "
                        "never zero)" % a_min.get("count"))
    counts = {}
    for c in corpora:
        counts[c.get("lane")] = counts.get(c.get("lane"), 0) + 1
    for lane, entry in sorted(minimums.items()):
        need = entry.get("count", 0)
        binds_from = entry.get("required_from", 0)
        have = counts.get(lane, 0)
        if phase >= binds_from and have < need:
            problems.append("lane %r: %d corpora < bound minimum %d" % (lane, have, need))
    prev_min = (prev or {}).get("lane_minimums", {})
    for lane, entry in sorted(prev_min.items()):
        cur = minimums.get(lane)
        if cur is None:
            problems.append("lane_minimums[%r] deleted" % lane)
            continue
        if cur.get("count", 0) < entry.get("count", 0):
            problems.append("lane_minimums[%r].count lowered %r -> %r"
                            % (lane, entry.get("count"), cur.get("count")))
        if cur.get("required_from", 0) > entry.get("required_from", 0):
            problems.append("lane_minimums[%r].required_from raised %r -> %r"
                            % (lane, entry.get("required_from"), cur.get("required_from")))
    prev_corpora = {c.get("id"): c for c in (prev or {}).get("corpora", [])}
    for c in corpora:
        pc = prev_corpora.get(c.get("id"))
        if pc is None:
            continue
        for attr in ("lane", "kind"):
            if c.get(attr) != pc.get(attr):
                problems.append("corpus %r: %s mutated %r -> %r (lane/kind are "
                                "immutable once measured)" %
                                (c.get("id"), attr, pc.get(attr), c.get(attr)))
    missing_ids = set(prev_corpora) - {c.get("id") for c in corpora}
    if missing_ids:
        problems.append("corpora removed without retirement: %s" % sorted(missing_ids))
    if problems:
        return RED, "; ".join(problems)
    return GREEN, "lane floors met (%s); lane/kind stable" % (
        ", ".join("%s=%d" % kv for kv in sorted(counts.items())) or "no corpora")


def c_shadow(ctx):
    """V-SHADOW [D8; A14a/A14c]: the shadow obligation is phase-conditioned
    and cannot be vacuously discharged by deleting the shadow before the
    phase that licenses deletion.  state 'required' + shadow present while
    phase < 8; 'severed' only at phase >= 8."""
    art = ctx["artifact"]
    probes = ctx["probes"]
    phase = art["phase_reached"]
    state = art["shadow_lane_state"]
    present = probes.get("shadow_present", "unavailable")
    problems = []
    if present not in S.PROBE_ANSWERS:
        present = "unavailable"
    if phase < S.SHADOW_SEVERED_PHASE:
        if state != "required":
            problems.append("shadow_lane_state %r at phase %d — severance is "
                            "licensed only at phase >= %d"
                            % (state, phase, S.SHADOW_SEVERED_PHASE))
        if present == "no":
            problems.append("shadow deleted from the tree at phase %d < %d — the "
                            "obligation does not go vacuous on deletion, it FAILS"
                            % (phase, S.SHADOW_SEVERED_PHASE))
        if present == "unavailable":
            problems.append("probe shadow_present unavailable => RED (fail-closed)")
    else:
        if state != "severed":
            problems.append("phase %d >= %d but shadow_lane_state is %r"
                            % (phase, S.SHADOW_SEVERED_PHASE, state))
    if problems:
        status = UNEVALUABLE if any("unavailable" in p for p in problems) else RED
        return status, "; ".join(problems)
    return GREEN, "shadow obligation consistent (state=%s, phase=%d)" % (state, phase)


def c_oracle(ctx):
    """V-ORACLE [D9; A18/A11c/section 6 row 16]: the differential/conformance
    suite is a REQUIRED artifact with its own liveness conjunct until the
    phase that formally retires it (windows are schema-pinned, never
    author-editable)."""
    art = ctx["artifact"]
    repo = ctx["repo"]
    phase = art["phase_reached"]
    oracles = art.get("oracles", {})
    problems = []
    unknown = set(oracles) - set(S.ORACLES)
    if unknown:
        problems.append("unknown oracle(s) declared: %s" % sorted(unknown))
    for name, window in sorted(S.ORACLES.items()):
        start = window["required_from_phase"]
        until = window["required_until_phase"]
        required = phase >= start and (until is None or phase < until)
        entry = oracles.get(name)
        if entry is None:
            if required:
                problems.append("oracle %r REQUIRED at phase %d (window [%s, %s)) "
                                "but not declared — deletion does not retire an "
                                "oracle, a phase does" %
                                (name, phase, start, "inf" if until is None else until))
            continue
        path = os.path.join(repo, entry.get("path", ""))
        if not os.path.isfile(path):
            if required:
                problems.append("oracle %r file missing: %s" % (name, entry.get("path")))
            continue
        actual_sha = sha256_file(path)
        if actual_sha != entry.get("sha256"):
            problems.append("oracle %r sha256 mismatch" % name)
        actual_lines = line_count_file(path)
        if actual_lines != entry.get("line_count"):
            problems.append("oracle %r line_count mismatch (recorded %r, actual %d)"
                            % (name, entry.get("line_count"), actual_lines))
        if required and actual_lines < 1:
            problems.append("oracle %r is empty — liveness requires >= 1 case "
                            "(baseline_preauthored_expectations)" % name)
    if problems:
        return RED, "; ".join(problems)
    live = [n for n, w in S.ORACLES.items()
            if phase >= w["required_from_phase"]
            and (w["required_until_phase"] is None or phase < w["required_until_phase"])]
    return GREEN, "required oracles live at phase %d: %s" % (phase, sorted(live))


def c_polarity(ctx):
    """V-POLARITY [check 7 / section 3.1; also D2's ratchet direction]: prefix
    polarity over the key census and corpus floors.  A numeric key matching
    no prefix FAILS (rev 3's vacuity_floor was audited by nothing).  Creation
    is not relaxation: a key absent from the previous census is exempt from
    comparison; every subsequent change obeys its prefix."""
    art = ctx["artifact"]
    prev = ctx["previous"]
    keys = art.get("keys", {})
    prev_keys = (prev or {}).get("keys", {})
    problems = []
    for name in sorted(keys):
        value = keys[name].get("value")
        if not is_number(value):
            problems.append("%s: value %r is not numeric" % (name, value))
            continue
        prefix = next((p for p in S.POLARITY_PREFIXES if name.startswith(p)), None)
        if prefix is None:
            problems.append("%s: matches no polarity prefix %s — audited by "
                            "nothing, therefore FAILS" %
                            (name, list(S.POLARITY_PREFIXES)))
            continue
        if name not in prev_keys:
            continue  # creation, not relaxation (section 3.1)
        prev_value = prev_keys[name].get("value")
        if not is_number(prev_value):
            continue
        if prefix == "max_" and value > prev_value:
            problems.append("%s: max_* raised %r -> %r" % (name, prev_value, value))
        elif prefix in ("baseline_", "min_") and value < prev_value:
            problems.append("%s: %s* lowered %r -> %r" % (name, prefix, prev_value, value))
        elif prefix == "fixed_" and value != prev_value:
            problems.append("%s: fixed_* changed %r -> %r" % (name, prev_value, value))
    prev_corpora = {c.get("id"): c for c in (prev or {}).get("corpora", [])}
    for c in art.get("corpora", []):
        pc = prev_corpora.get(c.get("id"))
        if pc is None:
            continue
        for fname, floor in sorted(c.get("floors", {}).items()):
            prev_floor = pc.get("floors", {}).get(fname)
            if is_number(prev_floor) and is_number(floor) and floor < prev_floor:
                problems.append("corpus %r floor %s lowered %r -> %r"
                                % (c.get("id"), fname, prev_floor, floor))
    if problems:
        return RED, "; ".join(problems)
    return GREEN, "polarity holds for %d keys" % len(keys)


CONJUNCT_FNS = [
    ("V-SCHEMA", c_schema),
    ("V-A15", c_a15),
    ("V-JOIN-RESIDUE", c_join_residue),
    ("V-PHASE-TREE", c_phase_tree),
    ("V-KEY-CENSUS", c_key_census),
    ("V-RATCHET-BASE", c_ratchet_base),
    ("V-SOAK-LOG", c_soak_log),
    ("V-LANE-FLOOR", c_lane_floor),
    ("V-SHADOW", c_shadow),
    ("V-ORACLE", c_oracle),
    ("V-POLARITY", c_polarity),
]

# X7-style census integrity: the implemented conjunct set must equal the
# schema's declared census, or the gate itself has drifted.
assert {cid for cid, _ in CONJUNCT_FNS} == set(S.CONJUNCTS), \
    "conjunct census mismatch between gate_schema.CONJUNCTS and validate.py"


# ---------------------------------------------------------------------------
# driver
# ---------------------------------------------------------------------------

def load_json_file(path, what):
    try:
        with open(path, "r") as fh:
            return json.load(fh)
    except (OSError, ValueError) as exc:
        raise SystemExit("cannot read %s %r: %s" % (what, path, exc))


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--artifact", required=True, help="current gate artifact (JSON)")
    ap.add_argument("--previous", help="previously ACCEPTED gate artifact (JSON)")
    ap.add_argument("--repo", required=True, help="git repository the artifact describes")
    ap.add_argument("--runs-log", required=True, help="runner's append-only log")
    ap.add_argument("--probes", help="tree-probe answers (JSON); missing => fail-closed")
    ap.add_argument("--artifact-relpath",
                    help="repo-relative path of the artifact (default: derived)")
    ap.add_argument("--verdict-file", help="write the machine-readable verdict here")
    args = ap.parse_args(argv)

    artifact = load_json_file(args.artifact, "artifact")
    previous = load_json_file(args.previous, "previous artifact") if args.previous else None
    probes = {}
    if args.probes and os.path.exists(args.probes):
        probes = load_json_file(args.probes, "probes")

    relpath = args.artifact_relpath
    if relpath is None:
        try:
            relpath = os.path.relpath(os.path.abspath(args.artifact),
                                      os.path.abspath(args.repo))
        except ValueError:
            relpath = os.path.basename(args.artifact)

    log_records, log_raw, chain_ok, chain_detail = read_log(args.runs_log)
    head = git_head(args.repo)

    ctx = {
        "artifact": artifact,
        "previous": previous,
        "probes": probes,
        "repo": args.repo,
        "artifact_relpath": relpath,
        "head": head,
        "log_records": log_records,
        "log_raw": log_raw,
        "log_chain_ok": chain_ok,
        "log_chain_detail": chain_detail,
        "soak_trailing_green": trailing_green(log_records),
    }

    rows = []
    for cid, fn in CONJUNCT_FNS:
        try:
            status, detail = fn(ctx)
        except Exception as exc:  # rule 1: an unevaluable conjunct is RED
            status, detail = UNEVALUABLE, "raised %s: %s" % (type(exc).__name__, exc)
        rows.append({"id": cid, "status": status, "detail": detail,
                     "maps_to": S.CONJUNCTS[cid]})

    failed = [r["id"] for r in rows if r["status"] != GREEN]
    verdict = GREEN if not failed else RED

    # D6 discipline: the validator itself records EVERY run — red or green —
    # in the append-only log, before emitting its decision.
    new_head = append_log(args.runs_log, log_raw,
                          head or "<no-head>", verdict, failed)

    for r in rows:
        tags = ",".join(r["maps_to"]["defects"] + r["maps_to"]["plan"])
        print("CONJ %-14s %-11s [%s] %s" % (r["id"], r["status"], tags, r["detail"]))
    print("SOAK trailing green runs (distinct commits): %d / %d over >= %d days "
          "(informational; consumed by phase gates only)"
          % (ctx["soak_trailing_green"], S.SOAK_RUNS, S.SOAK_DAYS))
    print("LOG  appended run record seq=%d sha256=%s (record this as "
          "runs_log_head in the next artifact)" % (new_head["seq"], new_head["sha256"]))
    print("GATE %s%s" % (verdict.upper(),
                         "" if not failed else " — failed: " + ", ".join(failed)))

    if args.verdict_file:
        with open(args.verdict_file, "w") as fh:
            json.dump({"verdict": verdict, "conjuncts": rows,
                       "soak_trailing_green": ctx["soak_trailing_green"],
                       "new_log_head": new_head}, fh, indent=1, sort_keys=True)

    return 0 if verdict == GREEN else 1


if __name__ == "__main__":
    sys.exit(main())
