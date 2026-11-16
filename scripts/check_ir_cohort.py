#!/usr/bin/env python3
# check_ir_cohort.py --- the M0 pin protocol: one IR semantics per cohort.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# WHAT THIS GATES, AND WHY THE TWO EXISTING PIN CHECKERS DO NOT
# -------------------------------------------------------------
# `check_pin_coherence.sh` asks whether each SUBMODULE GITLINK resolves and
# whether the worktree sits at it. `audit_first_party_pins.py` asks whether a
# historical gitlink is still FETCHABLE. Both are about gitlinks.
#
# But the cohort does not consume trust-ir through the gitlink. It consumes it
# through cargo git dependencies --- `trust-ir = { git = ..., rev = "..." }` ---
# and no gate in this repository has ever looked at one. Measured 2026-08-27 at
# superproject gitlink 7435e2eb, the tracked Cargo.tomls declare SIX distinct
# trust-ir revisions across 24 declarations:
#
#   22754291  2026-08-21  ay-jit, trust-cg     3 decl   <-- gitlink's semantics
#   ad8d257f  2026-08-21  trust-mc             3 decl
#   1541c0e5  2026-08-21  ty                   1 decl
#   a4e81b6b  2026-08-19  clean                6 decl
#   b4a50f14  2026-08-17  trust-vc             1 decl
#   64b7b7b1  2026-08-13  trust-wp             1 decl
#
# Every one of them reports `binary::VERSION == 37`. The wire version is a
# DECODING FLOOR --- it says a reader can parse the bytes, and says nothing
# whatever about whether two crates agree on what those bytes MEAN. Hashing the
# semantic surface at each of those six revisions collapses them to FIVE
# distinct schemas. So on the day this was written the cohort was running five
# different IR semantics behind one version number, and the only reason nothing
# had corrupted is that no two of the disagreeing pairs had yet exchanged a
# `.tmbc` across a construct where they differ.
#
# All six are contained in origin/main --- this is an eleven-day staleness
# gradient (2026-08-13 .. 2026-08-21), not a fork. That is the benign end of the
# failure mode, and it is the reason to build the gate NOW rather than after the
# first corrupted module.
#
# THE COHERENCE CRITERION IS THE DIGEST, NOT THE REVISION
# -------------------------------------------------------
# Requiring one revision across the cohort is too strict: pins churn for
# unrelated reasons, and 7435e2eb and 22754291 are DIFFERENT commits with
# IDENTICAL semantic surfaces --- gating on revision equality would have flagged
# a pair that is in fact perfectly safe to mix, and taught the next lane to
# waive. Requiring one wire version is too loose, by the measurement above.
# Hashing the surface is the criterion that separates "different commit, same
# meaning" (fine) from "same version number, different meaning" (the bug).
#
# WHAT IS NEVER WAIVABLE
# ----------------------
# A revision that does not resolve, and a revision that is not contained in the
# dependency's main as its remote publishes it. The second is the fork case:
# two consumers on divergent branches can disagree arbitrarily while both look
# current, and no expiry date makes that safe to ship. A containment verdict
# needs a main to be contained IN: a remote that publishes none gets
# CONTAINMENT UNRESOLVED, and one that cannot be read gets COULD NOT RUN ---
# both refuse, neither is called a fork (see on_main). Digest divergence IS
# waivable, per group, with an owner and an
# expiry (scripts/hooks-pin/ir-cohort-waivers.txt); it closes when the lagging
# consumer moves forward to the ratified schema.
#
# CONTAINMENT IS JUDGED AGAINST THE REMOTE'S MAIN, NOT THE STORE'S COPY OF IT
# --------------------------------------------------------------------------
# Until 2026-10-15 "contained in origin/main" meant the store's
# refs/remotes/origin/main, which is only as current as its last fetch, so a
# pin newer than a stale ref read exactly like a fork (six false OFF-MAIN rows
# on 2026-09-27; RED pushes from ~/trust-b1 on 2026-10-14/15), and `--fetch`,
# the only cure, wrote refs in module stores several worktrees share. Now the
# basis is `refs/heads/main` as `git ls-remote` reads it this run, and the
# objects that ancestry needs (the pinned revision, the remote's main tip) are
# fetched BY SHA with no destination: no ref and no FETCH_HEAD is written
# (scripts/lib/remote_tips.py; docs/DECISION_QUEUE.md
# "HOOKS-PIN-REMOTE-TIPS-1"). A remote that cannot be read is COULD NOT RUN,
# exit 2: never a pass, and never called a fork. `--fetch` is gone; it has
# nothing left to refresh.
#
# Cost: git plumbing plus one inventory read per first-party remote (read
# concurrently) and, only when this store lacks them, the objects of the judged
# revisions. No build. The inventory reads each tracked gitlink's worktree index
# explicitly, independent of local activation settings. It does not walk the
# compiler source tree to discover manifests.
#
# ONE BATCHED, REMEMBERED, BOUNDED JUDGMENT PER STORE (2026-11-15)
# ---------------------------------------------------------------
# Until 2026-11-15 the report loop judged one revision at a time (`on_main` ->
# `RemoteTips.judge` -> one native `agh repo commit-ancestry` read each), one
# store after another, remembered nothing between runs and had no bound: the
# landing gate's development run 20261114T134816 spent 378.8 s here on 15
# judgments, about 25 s each, while the October runs of the same local work took
# 3.1-6.1 s. Now every store's revisions and the trust-ir gitlink are judged in
# one `judge_many(scope="main")` per store, stores in parallel, right after the
# warm step; `on_main` then reads that run's verdicts. The predicate and the
# report are unchanged. Answers to "is A an ancestor of B?" are remembered by
# commit ids under `<git common dir>/trust-land/commit-ancestry`, the directory
# check_submodule_remote_reachability.py uses (`rt.AncestryMemory`, trusted as
# docs/DECISION_QUEUE.md REACH-MEMO-1 says); the remote's main is still read
# every run, so a rewound main is asked afresh. Every remote read shares one
# bound (`--time-bound`, DEFAULT_TIME_BOUND_S): past it a revision is COULD NOT
# RUN (exit 2), never a pass and never a finding. The phases' times go to
# stderr (`IR COHORT PHASES:`), so a run record shows where the time went.
# Measured after this change (2026-11-15, one cold run, docs/STATUS.md): 9
# questions in 5 ancestry reads instead of 15, but 355.6 s of 392.2 s was still
# remote judgment: per-store inventory reads (each witnessing the advertised
# tips as commits) and the ancestry reads. No commit was fetched in that run:
# its "5 fetch(es)" were the 5 ancestry reads counted a second time. Since
# then the phase line counts commit fetches apart from ancestry reads, and
# reports the tips the inventories witnessed as commits (and how many of them
# needed a native read, since a store that holds main's tip needs none), the
# commits and API body bytes native reads acquired, and the revisions left
# UNJUDGED (with a finding, exit 1 alone does not say some were COULD NOT RUN).
#
# THE INVENTORY WITNESSES ONLY MAIN (2026-11-15)
# ----------------------------------------------
# The warm step and `judge_many` share one `scope="main"` inventory per store.
# For a GitHub remote it still reads and validates the whole fresh
# advertisement, but witnesses only `refs/heads/main` as an original commit:
# claims/*, goals/*, side heads and pins cost no witness read, and one that
# cannot be served no longer leaves the store's revisions UNJUDGED. A main that
# is not a commit is still UNJUDGED. The reach lane keeps the full witness
# (docs/DECISION_QUEUE.md IR-COHORT-MAIN-WITNESS-1). How much remote time this
# saves is NOT measured yet.
#
# THE DATE IS NEVER EARLIER THAN TODAY IN UTC (2026-11-15)
# --------------------------------------------------------
# Waiver expiry was judged against `date.today()`, the LOCAL date (TZ,
# /etc/localtime), which near midnight disagrees with the landing gate's UTC
# date. Now it is max(`--date`, the current UTC date): the gate passes its
# declared date (land_gate.gate_date) with `--date`, and a later UTC date (a run
# that crosses midnight) wins. The date is read when each waiver is judged,
# after the remote phase, so it is never earlier than the gate's declared date
# or the UTC date at that moment. No environment variable is read for the date: an exported
# TRUST_GATE_DATE left from reproducing an old run could only make the check
# more lenient.
#
#   scripts/check_ir_cohort.py             # gate: exit 1 on incoherence, 2 when a remote could not be read
#   scripts/check_ir_cohort.py --report    # inventory only; unreadable inventory still refuses
#   scripts/check_ir_cohort.py --date YYYY-MM-DD   # the caller's declared date (never lowers today's UTC date)

from __future__ import annotations

import argparse
import math
import datetime as _dt
import hashlib
import json
import os
import re
import stat
import subprocess
import sys
import time
from pathlib import Path
from typing import NamedTuple, Optional

sys.path.insert(0, str(Path(__file__).resolve().parent / "lib"))

import remote_tips as rt  # noqa: E402  (scripts/lib/remote_tips.py)

# The semantic surface of each first-party IR dependency: the root files whose
# content DEFINES what a module means, together with their same-name split
# implementation directories (for example `ty.rs` and `ty/`). This list is semantics, not
# configuration --- widening it makes the gate stricter, narrowing it makes the
# gate lie, and either change belongs in review. A dependency absent from this
# table is inventoried and reported but NOT gated, loudly, so that a new
# first-party IR cannot slip in under a gate that silently ignores it.
SEMANTIC_SURFACE: dict[str, tuple[str, ...]] = {
    "trust-ir": (
        "crates/trust-ir/src/ty.rs",
        "crates/trust-ir/src/inst.rs",
        "crates/trust-ir/src/binary.rs",
        "crates/trust-ir/src/node.rs",
        "crates/trust-ir/src/value.rs",
        "crates/trust-ir/src/constant.rs",
    ),
}

# Where each gated dependency's object store lives, relative to the superproject.
OBJECT_STORE: dict[str, str] = {
    "trust-ir": "first-party/trust-ir",
}

# First-party dependencies this gate INVENTORIES but does not yet gate on
# semantics, each with the reason it is deferred. This is a named deferral, not
# an allowlist, and the difference is enforced by the output: every run still
# prints the full revision spread for these repos, and the summary still counts
# them as ungated. Nothing here is hidden --- it is scheduled.
#
# The first measurement (2026-08-27) found drift in ALL of them, which is why
# the reasons below are about sequencing rather than about safety:
UNGATED_BY_DECISION: dict[str, str] = {
    "ay": "solver/JIT surface; drift is real but the exchange format is not the IR",
    "clean": "L5IR producer; its surface is the THIR->L5IR lowering, and naming it "
    "correctly needs the producer census that M1 schedules",
    "trust-cg": "IR CONSUMER, not a format: two trust-cg revisions cannot disagree "
    "about a `.tmbc` they both merely read. Gated instead by its own differentials",
    "trust-vc": "VC surface; belongs with the condition-generator work, not with M0",
    "trust-wp": "WP consumer, not an IR format; its canonical trust-ir dependency remains "
    "in the semantic cohort and WP rule correctness is checked separately",
    "ty": "model checker; consumes IR, does not define it",
}

DEP_RE = re.compile(
    r'git\s*=\s*"https://github\.com/alabsystems/(?P<repo>[a-z0-9-]+?)(?:\.git)?"'
    r"[^\n]*?"
    r'rev\s*=\s*"(?P<rev>[0-9a-f]{40})"'
)

WAIVER_PATH = "scripts/hooks-pin/ir-cohort-waivers.txt"

# Every remote read of one run shares this bound (rt.RemoteTips.time_bound), as
# check_submodule_remote_reachability.py's DEFAULT_TIME_BOUND_S bounds its row.
# Past it a revision is COULD NOT RUN (exit 2). Until 2026-11-15 there was none,
# and each read could take FETCH_TIMEOUT_S with two retries.
DEFAULT_TIME_BOUND_S = 900.0


EXCLUDED_MANIFESTS: list[str] = []


class Decl(NamedTuple):
    repo: str
    rev: str
    where: str  # path of the Cargo.toml, relative to the superproject


class Waiver(NamedTuple):
    repo: str
    digest: str
    expires: _dt.date
    owner: str
    reason: str
    line_no: int


def run(args: list[str], cwd: Path, *, env: Optional[dict[str, str]] = None) -> tuple[int, str]:
    p = subprocess.run(args, cwd=cwd, capture_output=True, text=True, env=env)
    return p.returncode, p.stdout


# Trust: the constellation gate's VERIFIED exclusion list — archived manifest
# snapshots that declare their own `[workspace]`, are no member of the sibling
# that carries them, and are never built (docs/audits/first-party-constellation-
# exclusions-v1.json, one reason per row). This gate scans every tracked
# Cargo.toml, so without honouring the same list it reads a byte-preserved OLD
# manifest under `first-party/ty/reports/perf/.../originals/` as a live
# dependency edge and reports an off-main FORK that no build can reach (measured
# 2026-09-16 after the ty pin moved 535 commits: `clean@f14d9f45 OFF-MAIN` and a
# trust-ir schema divergence, both "consumed by" that archive alone). One list,
# one rationale, two gates: an exclusion earned there applies here. Fail-closed:
# a missing or differently-versioned file excludes NOTHING.
#
# SCOPE after the merge with the 2026-09-17 `reports` artifact skip (see
# find_declarations): that fail-closed reading governs THIS mechanism only. A
# manifest whose path carries a `reports` segment is skipped by the path-shape
# rule whatever this file says, so for that shape an audited row is NOT what
# decides. The two mechanisms are pinned separately over their own populations in
# scripts/tests/check_ir_cohort_test.sh — case 12 over a `spikes/` fixture (40 of
# the 43 live rows are trust-wp spikes, which no `reports` segment reaches), case
# 13 over the unconditional path-shape skip.
EXCLUSIONS_PATH = "docs/audits/first-party-constellation-exclusions-v1.json"
EXCLUSIONS_SCHEMA = "trust.constellation.exclusions.v1"


def load_snapshot_exclusions(root: Path) -> list[str]:
    """Superproject-relative prefixes (`first-party/<repo>/<path>/`) to skip."""
    try:
        doc = json.loads((root / EXCLUSIONS_PATH).read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return []
    if not isinstance(doc, dict) or doc.get("schema") != EXCLUSIONS_SCHEMA:
        return []
    prefixes: list[str] = []
    for row in doc.get("exclusions", []):
        repo, path = row.get("repository"), row.get("path")
        if isinstance(repo, str) and isinstance(path, str) and repo and path:
            prefixes.append(f"first-party/{repo}/{path.strip('/')}/")
    return prefixes


class InventoryError(RuntimeError):
    """A required tracked inventory or manifest could not be read."""


def inventory_environment(root: Path) -> dict[str, str]:
    """Explicit roots must not inherit another repository/index from a hook."""
    try:
        code, names = run(["git", "rev-parse", "--local-env-vars"], root)
    except OSError as error:
        raise InventoryError(f"cannot inspect Git inventory environment: {error}") from error
    local = set(names.splitlines())
    if code != 0 or not {"GIT_DIR", "GIT_INDEX_FILE"} <= local:
        raise InventoryError("cannot identify repository-local Git environment")
    env = {key: value for key, value in os.environ.items()
           if key not in local and not key.startswith("GIT_CONFIG_")}
    env["GIT_NO_REPLACE_OBJECTS"] = "1"
    return env


def ancestry_memory_dir(root: Path) -> Optional[Path]:
    """`<git common dir>/trust-land/commit-ancestry`, as
    check_submodule_remote_reachability.ancestry_memory_dir computes it, but
    under inventory_environment so a hook's exported GIT_DIR cannot choose it.
    None (nothing remembered, everything asked) when Git cannot say."""
    try:
        code, out = run(["git", "rev-parse", "--path-format=absolute", "--git-common-dir"], root,
                        env=inventory_environment(root))
    except (OSError, InventoryError):
        return None
    common = out.strip()
    return Path(common) / "trust-land" / "commit-ancestry" if code == 0 and common else None


def time_bound_seconds(text: str) -> float:
    """A finite, non-negative number of seconds: nan or inf would leave the
    run unbounded (min(cap, nan - now) is cap), a negative one is no bound."""
    try:
        value = float(text)
    except ValueError:
        raise argparse.ArgumentTypeError(f"{text!r} is not a number of seconds") from None
    if not math.isfinite(value) or value < 0:
        raise argparse.ArgumentTypeError(f"{text!r} is not a finite, non-negative number of seconds")
    return value


def utc_today() -> _dt.date:
    return _dt.datetime.now(_dt.timezone.utc).date()


def judged_date(declared: Optional[_dt.date]) -> _dt.date:
    """The date waivers are judged on: max(declared, the current UTC date), or
    the UTC date alone. Never the local date, never an environment variable:
    the result is never earlier than the gate's outcome window or the time of
    publication, so it can only make the check stricter."""
    today = utc_today()
    return today if declared is None else max(declared, today)


def iso_date(text: str) -> _dt.date:
    if re.fullmatch(r"[0-9]{4}-[0-9]{2}-[0-9]{2}", text) is None:
        raise argparse.ArgumentTypeError(f"`{text}` is not a YYYY-MM-DD date")
    try:
        return _dt.date.fromisoformat(text)
    except ValueError as error:
        raise argparse.ArgumentTypeError(f"`{text}` is not a date: {error}") from error


def tracked_manifest_paths(root: Path) -> list[str]:
    """Enumerate every populated tracked gitlink, independent of activation.

    Git's --recurse-submodules follows local initialization/active settings and
    can silently omit an existing consumer. Read each actual worktree index
    explicitly instead. A missing repository is unknown, never an empty set.
    """
    root = root.resolve()
    env = inventory_environment(root)
    pending = [(root, "")]
    seen: set[Path] = set()
    manifests: list[str] = []
    while pending:
        repo, prefix = pending.pop()
        try:
            actual = repo.resolve(strict=True)
            actual.relative_to(root)
        except (OSError, ValueError, RuntimeError) as error:
            raise InventoryError(f"cannot read tracked repository {prefix or '.'}: {error}") from error
        if actual in seen or len(seen) >= 1024:
            raise InventoryError(f"repeated or excessive tracked repository at {prefix or '.'}")
        seen.add(actual)
        try:
            code, top = run(["git", "rev-parse", "--show-toplevel"], actual, env=env)
            if code != 0 or not top.strip() or Path(top.strip()).resolve() != actual:
                raise InventoryError(f"tracked gitlink {prefix or '.'} has no independent worktree index")
            code, head = run(["git", "rev-parse", "--verify", "HEAD^{commit}"], actual, env=env)
            if code != 0 or not head.strip():
                raise InventoryError(f"tracked repository {prefix or '.'} has no resolvable HEAD")
            code, index = run(["git", "rev-parse", "--path-format=absolute", "--git-path", "index"], actual, env=env)
            if code != 0 or not index.strip() or not stat.S_ISREG(Path(index.strip()).lstat().st_mode):
                raise InventoryError(f"tracked repository {prefix or '.'} has no regular index")
            code, out = run(["git", "ls-files", "--cached", "--stage", "-z"], actual, env=env)
        except OSError as error:
            raise InventoryError(f"cannot inspect tracked repository {prefix or '.'}: {error}") from error
        if code != 0:
            raise InventoryError(f"cannot enumerate tracked repository {prefix or '.'}")
        children = []
        paths: set[str] = set()
        for row in out.split("\0"):
            if not row:
                continue
            header, tab, path = row.partition("\t")
            fields = header.split()
            if (not tab or not path or len(fields) != 3 or fields[2] != "0"
                    or fields[0] not in {"100644", "100755", "120000", "160000"}
                    or not re.fullmatch(r"[0-9a-f]{40}(?:[0-9a-f]{24})?", fields[1])
                    or path in paths or Path(path).is_absolute() or ".." in Path(path).parts):
                raise InventoryError(f"unreadable or unmerged index record at {prefix or '.'}")
            paths.add(path)
            relative = f"{prefix}/{path}" if prefix else path
            if fields[0] == "160000":
                children.append((actual / path, relative))
            elif path.endswith("Cargo.toml"):
                manifests.append(relative)
        pending.extend(reversed(sorted(children, key=lambda child: child[1])))
    return sorted(manifests)


def find_declarations(root: Path) -> list[Decl]:
    """Every first-party cargo git dependency on disk, submodule worktrees included.

    Reads the WORKTREE rather than HEAD on purpose: the worktree is what cargo
    will actually build, and a gitlink that disagrees with it is precisely
    check_pin_coherence.sh's business, not this gate's.
    """
    decls: list[Decl] = []
    skipped_report_artifacts: list[str] = []
    # The two skips this loop applies accumulate into stores of DIFFERENT
    # lifetimes, and the asymmetry is deliberate but fragile, so it is cleared
    # rather than left to luck. `skipped_report_artifacts` is local and reported
    # a few lines below; `EXCLUDED_MANIFESTS` is module-level because the
    # exclusion report is printed by the caller, at the end of the run, next to
    # the verdict it qualifies. A module-level list that is only ever appended
    # to is correct for exactly one call and silently double-counts on a second
    # one, and this function is called once today — which is the kind of fact
    # that stops being true without anyone noticing. Clearing here makes the
    # function idempotent in its own right.
    EXCLUDED_MANIFESTS.clear()
    # Explicit index traversal preserves the tracked-only boundary without
    # letting local submodule initialization/active settings hide consumers.
    manifests = tracked_manifest_paths(root)
    excluded_prefixes = load_snapshot_exclusions(root)
    for rel in manifests:
        if not rel:
            continue
        parts = Path(rel).parts
        # Skip vendored/registry copies: those are third-party trees that may
        # legitimately carry their own pins we do not govern.
        if any(p in ("target", "vendor", "node_modules") for p in parts):
            continue
        # Skip archived manifest snapshots the constellation gate has verified
        # are no build input (see EXCLUSIONS_PATH above).
        if any(rel.startswith(prefix) for prefix in excluded_prefixes):
            EXCLUDED_MANIFESTS.append(rel)
            continue
        # Skip REPORT ARTIFACTS. A `Cargo.toml` preserved under a `reports/`
        # directory is EVIDENCE OF A PAST STATE, not a build input: no workspace
        # reaches it, nothing resolves it, and no build can experience a
        # divergence it declares. Counting one as a live consumer makes this gate
        # report a disagreement that cannot happen, and a gate that cries wolf is
        # a gate people learn to push past.
        #
        # Measured 2026-09-17 over `git ls-files --recurse-submodules '*Cargo.toml'`:
        # 8 of 1,108 tracked manifests carry a `reports` path segment, every one an
        # artifact — ty's perf controls/fixtures, trust-cg's two `historical/
        # exporter-Cargo.toml` copies, and a 191 KB verbatim SNAPSHOT of ty's own
        # root manifest at `ty/reports/perf/2026-09-15-core-library-replay/
        # ty-cohort-f902-observed/originals/Cargo.toml`. That snapshot alone was
        # producing two of this gate's three problems, against pins nothing builds.
        # `reports` never appears in `first-party/ty/Cargo.toml`.
        #
        # This NARROWS the scan, so it is disclosed rather than silent: every skip
        # is counted and printed with the scan's own report, a few lines below
        # (the audited-exclusion skip above is the one the CALLER prints, beside
        # the verdict). A real crate that ever needs to live
        # under a `reports/` directory would be skipped and SAID SO, which is the
        # failure mode a reader can act on.
        #
        # ORDERING after the merge with the 2026-09-16 audited-exclusion skip
        # above: that skip runs FIRST, so the 191 KB ty snapshot named in the
        # measurement above no longer reaches this rule — it is adjudicated and
        # reported THERE, under EXCLUSIONS_PATH, and counted exactly once.
        # Re-measured 2026-09-18 on the merged tree: 13 tracked manifests carry a
        # `reports` segment, 1 (that snapshot) is on the audited list, and the 12
        # that reach this rule declare no first-party git dependency at all — so
        # today this rule removes no dependency edge, and the gate is
        # `IR COHORT COHERENT` with it disabled. The 2026-09-17 measurement above
        # stands as taken; this records only what the merged order does with it.
        if "reports" in parts:
            skipped_report_artifacts.append(rel)
            continue
        toml = root / rel
        try:
            text = toml.read_text(encoding="utf-8", errors="replace")
        except OSError as error:
            raise InventoryError(f"cannot read tracked manifest {rel}: {error}") from error
        for m in DEP_RE.finditer(text):
            repo = m.group("repo")
            # trust-ir-contract, trust-ir-build etc. all live in the trust-ir repo.
            decls.append(
                Decl(repo=repo, rev=m.group("rev"), where=str(toml.relative_to(root)))
            )
    if skipped_report_artifacts:
        # Disclosed, never silent — see the skip above.
        print(
            f"  note: skipped {len(skipped_report_artifacts)} Cargo.toml under a "
            f"`reports/` path as ARTIFACTS, not consumers:"
        )
        for rel in sorted(skipped_report_artifacts):
            print(f"          {rel}")
    return decls


def semantic_digest(store: Path, rev: str, surface: tuple[str, ...]) -> str | None:
    """Hash the dependency's meaning-defining sources AT `rev`.

    Returns None if the revision or any required tree/blob cannot be read.
    A file that does not exist at that revision hashes as its absence, which is
    itself semantic: adding or deleting a surface file changes the meaning.

    The declared Rust roots include their split implementation directories.
    Otherwise moving `impl Type` from `ty.rs` to `ty/observed_*.rs` makes later
    changes invisible, although every consumer still compiles those changes.
    Read each directory from the same immutable tree as the root, not the
    worktree; include all tracked files because Rust can include data as well
    as modules. This is a conservative source-coherence check, not a proof that
    these are all the program's semantics or that two implementations agree.
    """
    split_dirs = [path[:-3] + "/" for path in surface if path.endswith(".rs")]
    split_paths: set[str] = set()
    if split_dirs:
        code, out = run(
            ["git", "--no-replace-objects", "ls-tree", "-r", "--name-only", "-z", rev, "--", *split_dirs],
            cwd=store,
        )
        if code != 0:
            return None
        split_paths.update(path for path in out.split("\x00") if path)

    h = hashlib.sha256()
    # Preserve the root order (and old digest when there are no split files).
    # A sorted suffix makes each added, removed or changed child participate.
    for path in (*surface, *sorted(split_paths.difference(surface))):
        # Only a readable tree can prove a path absent. A present commit does
        # not make a missing blob (or an unreadable parent tree) an absence.
        code, entry = run(
            ["git", "--no-replace-objects", "--literal-pathspecs", "ls-tree", "-z", rev, "--", path],
            cwd=store,
        )
        if code != 0:
            return None
        if not entry:
            h.update(b"\x00ABSENT\x00" + path.encode())
            continue
        records = entry.split("\x00")
        if len(records) != 2 or records[1]:
            return None
        header, separator, actual_path = records[0].partition("\t")
        fields = header.split()
        if not separator or actual_path != path or len(fields) != 3 or fields[1] != "blob":
            return None
        content = subprocess.run(
            ["git", "--no-replace-objects", "cat-file", "blob", fields[2]], cwd=store, capture_output=True,
        )
        if content.returncode != 0:
            return None
        h.update(b"\x00FILE\x00" + path.encode() + b"\x00")
        h.update(content.stdout)
    return h.hexdigest()[:12]


class Unjudged:
    """on_main()'s fourth answer: the remote, or an object it named, could not
    be read. FALSY for the same reason NO_BASIS is: a caller that forgets this
    state reads it as "not on main", never as "on main". Reported as COULD NOT
    RUN (exit 2), never as a fork."""

    def __init__(self, detail: str) -> None:
        self.detail = detail

    def __bool__(self) -> bool:
        return False

    def __repr__(self) -> str:
        return f"UNJUDGED({self.detail})"


class _NoBasis:
    """on_main()'s third answer: the remote publishes no main at all.

    FALSY ON PURPOSE. A caller that forgets this state reads it as "not on
    main" --- the old, over-strict verdict --- and never as "on main", so
    omitting the branch can make the gate lie about WHY it is red but can never
    turn it green.
    """

    def __bool__(self) -> bool:
        return False

    def __repr__(self) -> str:
        return "NO_BASIS"


NO_BASIS = _NoBasis()

# The comparison basis: the dependency's main as its REMOTE publishes it, read
# with `git ls-remote` this run (never the store's refs/remotes/origin/main).
MAIN_REF = rt.MAIN_REF


def on_main(store: Path, rev: str, tips: rt.RemoteTips) -> bool | None | _NoBasis | Unjudged:
    """True/False if decided against the remote's main; None if the revision
    is in no local store and the remote will not serve it; NO_BASIS if the
    remote publishes no main; an (falsy) Unjudged if the remote, or an object
    it named, could not be read. main() judges every store's revisions in one
    batch first, so this reads that run's verdict (``tips.judge`` memoizes per
    (store, revision, scope)); called alone, it asks.

    NO_BASIS is split out from False because they are different facts: "there
    is nothing to compare against" is not "I compared and it is a fork".
    Reproduced 2026-09-27 with the ref deleted: a resolving revision on the
    only history there is, reported as the gate's harshest verdict.

    STALENESS IS GONE AS A CLASS (2026-10-15). The old basis was the store's
    refs/remotes/origin/main, and a present-but-stale ref was indistinguishable
    from a current one, so a pin newer than it read OFF-MAIN: six such rows on
    2026-09-27, every one false, and RED pushes on 2026-10-14/15. The basis is
    now the remote's own `refs/heads/main`, and its objects (and `rev`'s, when
    this store lacks them) are fetched by sha with no ref written, so a False
    here means the remote's main really does not contain `rev`.
    """
    verdict = tips.judge(store, rev, scope="main")
    if verdict.state == rt.CONTAINED:
        return True
    if verdict.state == rt.NOT_CONTAINED:
        return False
    if verdict.state == rt.ABSENT:
        return None
    if verdict.state == rt.NO_MAIN:
        return NO_BASIS
    return Unjudged(verdict.detail)


def no_basis_hint(store_rel: str) -> str:
    """The operator instruction for a NO_BASIS row."""
    return (
        f"The remote was read and publishes no `main`; check "
        f"`git -C {store_rel} ls-remote origin` before touching any pin."
    )


def gitlink_rev(root: Path, store_rel: str) -> Optional[str]:
    """Read the recorded gitlink; only a proven absent entry returns None."""
    code_gl, gl_out = run(
        ["git", "--no-replace-objects", "--literal-pathspecs", "ls-tree", "-z", "HEAD", "--", store_rel],
        cwd=root,
    )
    if code_gl != 0:
        raise InventoryError(f"RATIFIED ANCHOR UNREADABLE: cannot read HEAD tree for {store_rel} (Git exit {code_gl})")
    if not gl_out:
        return None
    records = gl_out.split("\x00")
    header, separator, path = records[0].partition("\t")
    fields = header.split()
    if (len(records) != 2 or records[1] or not separator or path != store_rel
            or len(fields) != 3 or fields[:2] != ["160000", "commit"]
            or re.fullmatch(r"[0-9a-f]{40}", fields[2]) is None):
        raise InventoryError(f"RATIFIED ANCHOR INVALID: {store_rel} is not an exact recorded gitlink")
    return fields[2]


def has_store(store: Path) -> bool:
    return (store / ".git").exists() or (store / "HEAD").exists()


def load_waivers(root: Path) -> tuple[list[Waiver], list[str]]:
    path = root / WAIVER_PATH
    waivers: list[Waiver] = []
    errors: list[str] = []
    if not path.exists():
        return waivers, errors
    for i, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        fields = [f.strip() for f in line.split("|")]
        if len(fields) != 5:
            errors.append(f"{WAIVER_PATH}:{i}: expected 5 `|`-separated fields, got {len(fields)}")
            continue
        repo, digest, expires_s, owner, reason = fields
        try:
            expires = _dt.date.fromisoformat(expires_s)
        except ValueError:
            errors.append(f"{WAIVER_PATH}:{i}: `{expires_s}` is not an ISO date")
            continue
        if not owner or not reason:
            errors.append(f"{WAIVER_PATH}:{i}: owner and reason are mandatory")
            continue
        waivers.append(Waiver(repo, digest, expires, owner, reason, i))
    return waivers, errors


def main() -> int:
    ap = argparse.ArgumentParser(description="M0: one IR semantics per cohort")
    ap.add_argument("--report", action="store_true", help="inventory only; unreadable inventory still refuses")
    ap.add_argument(
        "--root",
        default=None,
        help="superproject to inspect (default: the repository containing this "
        "script, so a hook is unaffected by the cwd it fires in)",
    )
    ap.add_argument(
        "--date",
        type=iso_date,
        default=None,
        metavar="YYYY-MM-DD",
        help="the caller's declared date (the landing gate passes its own); waivers are "
        "judged on max(this, the current UTC date), on the UTC date without it",
    )
    ap.add_argument(
        "--time-bound",
        type=time_bound_seconds,
        default=DEFAULT_TIME_BOUND_S,
        metavar="SECONDS",
        help="bound every remote read of this run together; a revision still unjudged when "
        f"it is spent is COULD NOT RUN (exit 2) (default {DEFAULT_TIME_BOUND_S:.0f})",
    )
    args = ap.parse_args()
    started = time.monotonic()

    anchor_dir = Path(args.root).resolve() if args.root else Path(__file__).resolve().parent
    try:
        code, out = run(["git", "rev-parse", "--show-toplevel"], anchor_dir,
                        env=inventory_environment(anchor_dir))
    except InventoryError as error:
        print(f"IR COHORT COULD NOT RUN: manifest inventory: {error}", file=sys.stderr)
        return 2
    if code != 0:
        print("not inside a git repository", file=sys.stderr)
        return 2
    root = Path(out.strip())

    try:
        decls = find_declarations(root)
    except InventoryError as error:
        print(f"IR COHORT COULD NOT RUN: manifest inventory: {error}", file=sys.stderr)
        return 2
    if not decls:
        print("IR-COHORT-EMPTY: no first-party cargo git dependencies found at all.")
        print("  A gate that inventories nothing is a gate that proves nothing.")
        return 1

    waivers, waiver_errors = load_waivers(root)
    problems: list[str] = list(waiver_errors)
    # Revisions whose containment could not be JUDGED (a remote could not be
    # read). Kept apart from `problems` so the exit says COULD NOT RUN (2)
    # rather than a finding (1); either one refuses.
    unjudged: list[str] = []
    used_waivers: set[int] = set()
    ungated_repos: list[str] = []
    ungated_drift: list[str] = []

    by_repo: dict[str, list[Decl]] = {}
    for d in decls:
        by_repo.setdefault(d.repo, []).append(d)

    # One inventory read per first-party remote, all at once, and each store's
    # missing objects (the declared revisions, the ratified gitlink and the
    # remote's main tip) in one fetch that writes no ref. Remembered ancestry
    # answers are read from, and new ones written to, the clone's memory; every
    # remote read shares the run's bound.
    tips = rt.RemoteTips(memory=ancestry_memory_dir(root), time_bound=args.time_bound)
    warm: list[tuple[Path, list[str]]] = []
    ratified_anchors: dict[str, str] = {}
    try:
        for repo, rows in by_repo.items():
            rel = OBJECT_STORE.get(repo) or f"first-party/{repo}"
            if not has_store(root / rel):
                continue
            shas = sorted({d.rev for d in rows})
            gl = None
            if repo in SEMANTIC_SURFACE:
                gl = gitlink_rev(root, rel)
                if gl is None:
                    raise InventoryError(f"RATIFIED ANCHOR MISSING: HEAD records no gitlink for {rel}")
                ratified_anchors[repo] = gl
            warm.append((root / rel, shas + ([gl] if gl else [])))
    except InventoryError as error:
        print(f"IR COHORT COULD NOT RUN: {error}", file=sys.stderr)
        return 2
    inventoried = time.monotonic()

    def judge_store(item: tuple[Path, list[str]]) -> None:
        # Every revision of the store and its gitlink in one batch, so the
        # loop below asks nothing (2026-11-15; see the header).
        store, shas = item
        tips.warm(store, shas, scope="main")
        tips.judge_many(store, shas, scope="main")

    rt.parallel_map(judge_store, warm)
    judged = time.monotonic()

    for repo in sorted(by_repo):
        rows = by_repo[repo]
        revs = sorted({d.rev for d in rows})
        surface = SEMANTIC_SURFACE.get(repo)
        store_rel = OBJECT_STORE.get(repo)
        print(f"\n== {repo}: {len(rows)} declaration(s), {len(revs)} revision(s)")

        if surface is None or store_rel is None:
            why = UNGATED_BY_DECISION.get(repo)
            if why is None:
                problems.append(
                    f"{repo}: consumed as a first-party dependency but absent from BOTH "
                    f"SEMANTIC_SURFACE and UNGATED_BY_DECISION --- a new first-party "
                    f"dependency must not enter under a gate that silently ignores it. "
                    f"Declare its surface, or record why it is deferred."
                )
                print(f"   UNDECLARED: `{repo}` is in neither table.")
            else:
                ungated_repos.append(repo)
                print(f"   NOT SEMANTICALLY GATED (deferred): {why}")
            # Print the spread either way. A deferral that stops showing the
            # drift it defers has become an allowlist.
            for r in revs:
                who = sorted({d.where for d in rows if d.rev == r})
                print(
                    f"     {r[:8]}  {len(who)} decl  {who[0]}"
                    f"{f' (+{len(who) - 1})' if len(who) > 1 else ''}"
                )
            if len(revs) > 1:
                ungated_drift.append(f"{repo} ({len(revs)} revisions)")

        # THE NEVER-WAIVABLE CHECKS RUN FOR EVERY FIRST-PARTY DEPENDENCY,
        # gated or not. The first cut of this gate `continue`d here for anything
        # without a declared surface, which quietly exempted ay, clean,
        # trust-cg, trust-vc and ty from resolvability and containment too --- a
        # much bigger exemption than the one that was actually decided. Those
        # two checks have nothing to do with SEMANTICS: an unfetchable pin makes
        # a build unreproducible and an off-main pin can disagree arbitrarily,
        # whatever the dependency is. Only the digest comparison is deferred.
        store_rel = store_rel or f"first-party/{repo}"
        store = root / store_rel
        if not has_store(store):
            problems.append(
                f"{repo}: object store {store_rel} is not checked out, so its "
                f"{len(revs)} pinned revision(s) cannot be resolved at all"
            )
            continue

        # (digest -> revs), plus the hard, never-waivable failures.
        groups: dict[str, list[str]] = {}
        for rev in revs:
            consumers = ", ".join(sorted({d.where for d in rows if d.rev == rev}))
            main_state = on_main(store, rev, tips)
            if isinstance(main_state, Unjudged):
                # "I could not look" is not "the pin is missing" (measured
                # 2026-08-27: a dead GITHUB_TOKEN failed every HTTPS read) and
                # not "the pin is a fork". It refuses all the same: exit 2.
                unjudged.append(
                    f"{repo}@{rev[:8]}: COULD NOT RUN --- containment in the remote's main "
                    f"was not judged: {main_state.detail} (consumed by {consumers}). "
                    f"Not a finding about the pin, and not a pass; check the network and "
                    f"`git -C {store_rel} ls-remote origin`, then re-run."
                )
                continue
            if main_state is None:
                problems.append(
                    f"{repo}@{rev[:8]}: UNRESOLVABLE --- in no local store at {store_rel}, "
                    f"and its remote will not serve it by sha (consumed by {consumers}). "
                    f"Never waivable: an unfetchable pin makes the build unreproducible."
                )
                continue
            if main_state is NO_BASIS:
                # A problem row and exit 1; "there is no main to compare
                # against" is not "I compared and it is a fork". No `continue`:
                # the revision resolves, so its semantic digest is still
                # computable and still judged below --- skipping it would also
                # have turned every live waiver into a false "STALE waiver ...
                # Delete the row".
                problems.append(
                    f"{repo}@{rev[:8]}: CONTAINMENT UNRESOLVED --- the remote publishes no "
                    f"{MAIN_REF}, so there is no basis for a containment verdict "
                    f"(consumed by {consumers}). The revision resolves; what is missing is "
                    f"the main it would be contained in, so this is NOT a finding that the "
                    f"pin is off main. Not waivable either: a containment verdict needs a "
                    f"main. {no_basis_hint(store_rel)}"
                )
            elif not main_state:
                problems.append(
                    f"{repo}@{rev[:8]}: OFF-MAIN --- not contained in the remote's main, "
                    f"read with ls-remote this run (consumed by {consumers}). Never "
                    f"waivable: this is the fork case, where two consumers can disagree "
                    f"arbitrarily while both look current."
                )
                continue
            if surface is None:
                continue  # resolvability/containment checked; digest deferred
            digest = semantic_digest(store, rev, surface)
            if digest is None:
                problems.append(f"{repo}@{rev[:8]}: revision resolved but surface unreadable")
                continue
            groups.setdefault(digest, []).append(rev)

        for digest in sorted(groups):
            revs_here = sorted(groups[digest])
            who = sorted({d.where for d in rows if d.rev in set(revs_here)})
            marker = "" if len(groups) == 1 else "  <-- one of several"
            print(f"   schema {digest}{marker}")
            for r in revs_here:
                rw = sorted({d.where for d in rows if d.rev == r})
                print(f"     {r[:8]}  {len(rw)} decl  {rw[0]}{' …' if len(rw) > 1 else ''}")

        if groups:
            # The RATIFIED semantics is the one at the superproject's own
            # recorded gitlink --- that is what "one tagged release the cohort
            # rides" means, and it is a stable anchor rather than a popularity
            # contest that moves whenever a lane adds a crate. The exact
            # gitlink was required and read before any remote question. A
            # most-declared group is only diagnostic if its source is unreadable.
            #
            # This runs even when the cohort is INTERNALLY uniform. The first
            # version of this gate only compared groups against each other, and
            # a fixture where every consumer had drifted together, away from the
            # gitlink, reported COHERENT --- the cohort agreed with itself and
            # with nothing else. Uniform drift is still drift: it is precisely
            # how the ratified pin becomes a fiction that nothing builds against.
            centre = None
            anchor = ""
            anchor_unreadable = False
            gl_rev = ratified_anchors[repo]
            if gl_rev:
                # THE ANCHOR IS SUBJECT TO THE FORK RULE TOO.
                #
                # Every consumer-declared revision above is refused, never
                # waivably, when it is not contained in the dependency's
                # origin/main. The gitlink was exempt from that same test while
                # being the thing all of them are judged AGAINST — the strictest
                # position in the gate had the weakest check. A superproject that
                # pins the cohort head to a feature branch then gets a ratified
                # semantics that no release can reproduce, and if every consumer
                # happens to match it the gate prints COHERENT.
                #
                # Found 2026-08-31, not hypothetically: `d24c671211` ("Land
                # b62-merge-redo") pinned first-party/trust-ir to 0f56107f, which
                # lives only on origin/b62-merge-redo — 18 behind main and 7
                # ahead of it, i.e. genuinely divergent, not merely stale. The
                # gate did report a problem, but it named trust-mc, whose
                # revision IS on main and which was therefore the one repository
                # in the cohort that had done nothing wrong. Diagnosis pointed
                # away from the cause, and the obvious repair — waive trust-mc —
                # would have been keyed on the correct repo's schema to
                # accommodate an unreproducible anchor.
                gl_main = on_main(store, gl_rev, tips)
                if isinstance(gl_main, Unjudged):
                    # Checked FIRST: Unjudged is falsy, and must never be
                    # rendered as the "RATIFIED ANCHOR IS OFF-MAIN" below.
                    unjudged.append(
                        f"{repo}@{gl_rev[:8]}: RATIFIED ANCHOR COULD NOT RUN --- the "
                        f"superproject gitlink's containment in the remote's main was not "
                        f"judged: {gl_main.detail}. Not a finding, and not a pass."
                    )
                elif gl_main is None:
                    problems.append(
                        f"{repo}@{gl_rev[:8]}: RATIFIED ANCHOR UNRESOLVABLE --- in no local "
                        f"store at {store_rel}, and its remote will not serve it (the "
                        f"superproject gitlink). Never waivable: the cohort head must be "
                        f"fetchable for the pin to mean anything."
                    )
                elif gl_main is NO_BASIS:
                    # Checked BEFORE `not gl_main`: NO_BASIS is falsy, and without
                    # this branch it would be rendered as the false "RATIFIED
                    # ANCHOR IS OFF-MAIN" below --- pointing the reader at a branch
                    # merge that nothing calls for.
                    problems.append(
                        f"{repo}@{gl_rev[:8]}: RATIFIED ANCHOR CONTAINMENT UNRESOLVED --- "
                        f"the remote publishes no {MAIN_REF}, so there is no basis for a "
                        f"containment verdict on the superproject gitlink. This is NOT a "
                        f"finding that the anchor is on a branch. Not waivable either: a "
                        f"containment verdict needs a main. {no_basis_hint(store_rel)}"
                    )
                elif not gl_main:
                    problems.append(
                        f"{repo}@{gl_rev[:8]}: RATIFIED ANCHOR IS OFF-MAIN --- the "
                        f"superproject gitlink is not contained in {repo}'s origin/main, so "
                        f"the semantics the whole cohort is judged against is a branch. "
                        f"Never waivable, for the same reason a consumer on a branch is not: "
                        f"nothing reproduces it from the dependency's published history. Fix "
                        f"the ANCHOR — merge that branch to {repo}'s main, or move the "
                        f"gitlink to a main revision. Waiving a consumer here would be "
                        f"keying a waiver on a repository that is correctly on main."
                    )
                gl_digest = semantic_digest(store, gl_rev, surface)
                if gl_digest is None:
                    anchor_unreadable = True
                    problems.append(
                        f"{repo}@{gl_rev[:8]}: RATIFIED SURFACE UNREADABLE --- restore the "
                        f"gitlink's real semantic trees and blobs before judging the cohort; "
                        f"a most-declared group is diagnostic only and cannot replace the anchor."
                    )
                else:
                    centre = gl_digest
                    anchor = f"superproject gitlink {gl_rev[:8]}"
                    if gl_digest not in groups:
                        print(
                            f"   ratified schema {gl_digest} ({anchor}) is consumed by "
                            f"NO cargo declaration --- the cohort head is a pin nothing "
                            f"actually builds against."
                        )
            if centre is None:
                centre = max(groups, key=lambda d: (len(groups[d]), d))
                anchor = "most-declared group (gitlink unreadable)"
            label = "diagnostic group" if anchor_unreadable else "ratified"
            print(f"   {label}: {centre}  [{anchor}]")
            diverged = 0
            for digest in sorted(groups):
                if digest == centre:
                    continue
                diverged += 1
                w = next(
                    (x for x in waivers if x.repo == repo and x.digest == digest), None
                )
                who = sorted({d.where for d in rows if d.rev in set(groups[digest])})
                if w is None:
                    problems.append(
                        f"{repo}: schema {digest} diverges from the cohort schema "
                        f"{centre} (revisions {', '.join(r[:8] for r in groups[digest])}; "
                        f"consumed by {', '.join(who)}). Five semantics behind one wire "
                        f"version is the bug this gate exists to catch. Move the lagging "
                        f"consumer onto the ratified schema (commit in the consumer, then "
                        f"move its pin)."
                    )
                # Read when the waiver is judged, after the remote phase (up to
                # the time bound), never at the run's start.
                elif w.expires < judged_date(args.date):
                    used_waivers.add(w.line_no)
                    problems.append(
                        f"{repo}: waiver for schema {digest} EXPIRED {w.expires} "
                        f"(owner {w.owner}). {w.reason}"
                    )
                else:
                    used_waivers.add(w.line_no)
                    print(
                        f"   waived  {digest} until {w.expires} ({w.owner}): {w.reason}"
                    )
            if diverged == 0 and not anchor_unreadable:
                print(
                    f"   COHERENT: {len(rows)} declaration(s), all on the ratified surface."
                )

    # A waiver that no longer applies must be deleted, not left to rot --- the
    # same rule pin-waivers.txt enforces.
    for w in waivers:
        if w.line_no not in used_waivers:
            problems.append(
                f"{WAIVER_PATH}:{w.line_no}: STALE waiver for {w.repo} schema "
                f"{w.digest} --- the divergence it covers is gone. Delete the row."
            )

    finished = time.monotonic()
    print(
        f"IR COHORT PHASES: inventory {inventoried - started:.1f}s; remote judgment "
        f"{judged - inventoried:.1f}s over {len(warm)} store(s) ({tips.ls_remote_calls} inventory "
        f"read(s) witnessing {tips.witnessed_tips} tip(s) as commits ({tips.native_witnessed_commits} "
        f"of them by {tips.witness_reads} native read(s)), "
        f"{tips.ancestry_calls} native ancestry read(s) carrying {tips.remote_questions} "
        f"question(s), {tips.remembered} remembered answer(s), {tips.commit_fetch_calls} commit "
        f"fetch(es); native reads acquired {tips.acquired_commits} commit(s), "
        f"{tips.api_body_bytes} API body byte(s)); local {finished - judged:.1f}s; "
        f"{len(unjudged)} revision(s) UNJUDGED; time bound {args.time_bound:g}s",
        file=sys.stderr,
    )

    print()
    if ungated_repos:
        print(
            f"{len(ungated_repos)} first-party dependenc(ies) inventoried but NOT "
            f"semantically gated: {', '.join(sorted(ungated_repos))}"
        )
        if ungated_drift:
            print(f"  of which these are ALREADY drifting: {', '.join(sorted(ungated_drift))}")
        print("  (deferred by decision, printed every run so the deferral cannot rot)")

    if EXCLUDED_MANIFESTS:
        print(
            f"{len(EXCLUDED_MANIFESTS)} archived manifest snapshot(s) excluded from dependency "
            f"authority per {EXCLUSIONS_PATH} (declares its own [workspace], no member, never built):"
        )
        for rel in EXCLUDED_MANIFESTS:
            print(f"     {rel}")
    if not problems and not unjudged:
        print("IR COHORT COHERENT")
        return 0

    if problems:
        print(f"IR COHORT INCOHERENT --- {len(problems)} problem(s):")
        for p in problems:
            print(f"  * {p}")
    if unjudged:
        print(
            f"IR COHORT COULD NOT RUN --- {len(unjudged)} revision(s) not judged, because "
            f"a remote could not be read (not a pass, and not a finding):"
        )
        for p in unjudged:
            print(f"  * {p}")
    if args.report:
        print("\n(--report: exiting 0 regardless)")
        return 0
    return 1 if problems else 2


if __name__ == "__main__":
    sys.exit(main())
