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
# dependency's `origin/main`. The second is the fork case: two consumers on
# divergent branches can disagree arbitrarily while both look current, and no
# expiry date makes that safe to ship. Digest divergence IS waivable, per group,
# with an owner and an expiry --- because burning it down means moving other
# lanes' pins, which is a coordinated act, never a unilateral one.
#
# Cost: pure git plumbing, no build, no network unless --fetch. Measured 0.84s
# wall over the 9-submodule superproject (24 trust-ir declarations, 6 revisions
# hashed). The inventory uses `git ls-files --recurse-submodules`; the naive
# filesystem walk of the same tree measured 36s, because the superproject
# carries a full rustc source tree.
#
#   scripts/check_ir_cohort.py             # gate (exit nonzero on incoherence)
#   scripts/check_ir_cohort.py --report    # inventory only, always exit 0
#   scripts/check_ir_cohort.py --fetch     # refresh remotes before resolving

from __future__ import annotations

import argparse
import datetime as _dt
import hashlib
import re
import subprocess
import sys
from pathlib import Path
from typing import NamedTuple

# The semantic surface of each first-party IR dependency: the files whose
# content DEFINES what a module means. This list is semantics, not
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
    "ty": "model checker; consumes IR, does not define it",
}

DEP_RE = re.compile(
    r'git\s*=\s*"https://github\.com/alabsystems/(?P<repo>[a-z0-9-]+?)(?:\.git)?"'
    r"[^\n]*?"
    r'rev\s*=\s*"(?P<rev>[0-9a-f]{40})"'
)

WAIVER_PATH = "scripts/hooks-pin/ir-cohort-waivers.txt"


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


def run(args: list[str], cwd: Path) -> tuple[int, str]:
    p = subprocess.run(args, cwd=cwd, capture_output=True, text=True)
    return p.returncode, p.stdout


def find_declarations(root: Path) -> list[Decl]:
    """Every first-party cargo git dependency on disk, submodule worktrees included.

    Reads the WORKTREE rather than HEAD on purpose: the worktree is what cargo
    will actually build, and a gitlink that disagrees with it is precisely
    check_pin_coherence.sh's business, not this gate's.
    """
    decls: list[Decl] = []
    # `git ls-files --recurse-submodules` rather than rglob: the superproject
    # carries a full rustc tree, and walking it cost 36s measured against 0.9s
    # for the git plumbing. It also confines the inventory to TRACKED files, so
    # a stray build artifact cannot inject a phantom pin.
    code, out = run(
        ["git", "ls-files", "--recurse-submodules", "-z", "*Cargo.toml"], cwd=root
    )
    if code != 0:
        return decls
    for rel in out.split("\0"):
        if not rel:
            continue
        parts = Path(rel).parts
        # Skip vendored/registry copies: those are third-party trees that may
        # legitimately carry their own pins we do not govern.
        if any(p in ("target", "vendor", "node_modules") for p in parts):
            continue
        toml = root / rel
        try:
            text = toml.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        for m in DEP_RE.finditer(text):
            repo = m.group("repo")
            # trust-ir-contract, trust-ir-build etc. all live in the trust-ir repo.
            decls.append(
                Decl(repo=repo, rev=m.group("rev"), where=str(toml.relative_to(root)))
            )
    return decls


def semantic_digest(store: Path, rev: str, surface: tuple[str, ...]) -> str | None:
    """Hash the dependency's meaning-defining sources AT `rev`.

    Returns None if the revision is not resolvable in the local object store.
    A file that does not exist at that revision hashes as its absence, which is
    itself semantic: adding or deleting a surface file changes the meaning.
    """
    h = hashlib.sha256()
    for path in surface:
        code, out = run(["git", "show", f"{rev}:{path}"], cwd=store)
        if code != 0:
            code2, _ = run(["git", "cat-file", "-e", f"{rev}^{{commit}}"], cwd=store)
            if code2 != 0:
                return None
            h.update(b"\x00ABSENT\x00" + path.encode())
            continue
        h.update(b"\x00FILE\x00" + path.encode() + b"\x00")
        h.update(out.encode())
    return h.hexdigest()[:12]


def on_main(store: Path, rev: str) -> bool | None:
    """True/False if decidable; None if the revision does not resolve at all."""
    code, _ = run(["git", "cat-file", "-e", f"{rev}^{{commit}}"], cwd=store)
    if code != 0:
        return None
    code, _ = run(["git", "merge-base", "--is-ancestor", rev, "origin/main"], cwd=store)
    return code == 0


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
    ap.add_argument("--report", action="store_true", help="inventory only; always exit 0")
    ap.add_argument("--fetch", action="store_true", help="refresh remotes before resolving")
    ap.add_argument(
        "--root",
        default=None,
        help="superproject to inspect (default: the repository containing this "
        "script, so a hook is unaffected by the cwd it fires in)",
    )
    args = ap.parse_args()

    anchor_dir = Path(args.root).resolve() if args.root else Path(__file__).resolve().parent
    code, out = run(["git", "rev-parse", "--show-toplevel"], anchor_dir)
    if code != 0:
        print("not inside a git repository", file=sys.stderr)
        return 2
    root = Path(out.strip())

    decls = find_declarations(root)
    if not decls:
        print("IR-COHORT-EMPTY: no first-party cargo git dependencies found at all.")
        print("  A gate that inventories nothing is a gate that proves nothing.")
        return 1

    today = _dt.date.today()
    waivers, waiver_errors = load_waivers(root)
    problems: list[str] = list(waiver_errors)
    used_waivers: set[int] = set()
    ungated_repos: list[str] = []
    ungated_drift: list[str] = []

    by_repo: dict[str, list[Decl]] = {}
    for d in decls:
        by_repo.setdefault(d.repo, []).append(d)

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
        if not (store / ".git").exists() and not (store / "HEAD").exists():
            problems.append(
                f"{repo}: object store {store_rel} is not checked out, so its "
                f"{len(revs)} pinned revision(s) cannot be resolved at all"
            )
            continue
        if args.fetch:
            code_f, _ = run(["git", "fetch", "-q", "origin"], cwd=store)
            if code_f != 0:
                # A failed fetch must NOT be reported downstream as "this pin does
                # not exist". Measured 2026-08-27: a dead GITHUB_TOKEN in the
                # session environment made every HTTPS fetch fail with "Invalid
                # username or token", and the honest reading of that is "I could
                # not look", not "the pin is missing".
                problems.append(
                    f"{repo}: `git fetch origin` FAILED in {store_rel} --- refusing to "
                    f"report on revisions I could not look up. This is usually a dead "
                    f"credential rather than a bad pin; check `git ls-remote` and a "
                    f"stale GITHUB_TOKEN in the environment before touching any pin."
                )
                continue

        # (digest -> revs), plus the hard, never-waivable failures.
        groups: dict[str, list[str]] = {}
        for rev in revs:
            main_state = on_main(store, rev)
            if main_state is None:
                problems.append(
                    f"{repo}@{rev[:8]}: UNRESOLVABLE in {store_rel} "
                    f"(consumed by {', '.join(sorted({d.where for d in rows if d.rev == rev}))}). "
                    f"Never waivable: an unfetchable pin makes the build unreproducible."
                )
                continue
            if not main_state:
                problems.append(
                    f"{repo}@{rev[:8]}: OFF-MAIN --- not contained in origin/main "
                    f"(consumed by {', '.join(sorted({d.where for d in rows if d.rev == rev}))}). "
                    f"Never waivable: this is the fork case, where two consumers can "
                    f"disagree arbitrarily while both look current."
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
            # contest that moves whenever a lane adds a crate. Falling back to
            # the most-declared group keeps the gate usable if the gitlink is
            # unreadable, but says so.
            #
            # This runs even when the cohort is INTERNALLY uniform. The first
            # version of this gate only compared groups against each other, and
            # a fixture where every consumer had drifted together, away from the
            # gitlink, reported COHERENT --- the cohort agreed with itself and
            # with nothing else. Uniform drift is still drift: it is precisely
            # how the ratified pin becomes a fiction that nothing builds against.
            centre = None
            anchor = ""
            code_gl, gl_out = run(["git", "ls-tree", "HEAD", store_rel], cwd=root)
            gl_rev = gl_out.split()[2] if code_gl == 0 and len(gl_out.split()) >= 3 else None
            if gl_rev:
                gl_digest = semantic_digest(store, gl_rev, surface)
                if gl_digest is not None:
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
            print(f"   ratified: {centre}  [{anchor}]")
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
                        f"version is the bug this gate exists to catch. Coordinate a pin "
                        f"bump, or add an owned, expiring row to {WAIVER_PATH}."
                    )
                elif w.expires < today:
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
            if diverged == 0:
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

    print()
    if ungated_repos:
        print(
            f"{len(ungated_repos)} first-party dependenc(ies) inventoried but NOT "
            f"semantically gated: {', '.join(sorted(ungated_repos))}"
        )
        if ungated_drift:
            print(f"  of which these are ALREADY drifting: {', '.join(sorted(ungated_drift))}")
        print("  (deferred by decision, printed every run so the deferral cannot rot)")

    if not problems:
        print("IR COHORT COHERENT")
        return 0

    print(f"IR COHORT INCOHERENT --- {len(problems)} problem(s):")
    for p in problems:
        print(f"  * {p}")
    if args.report:
        print("\n(--report: exiting 0 regardless)")
        return 0
    return 1


if __name__ == "__main__":
    sys.exit(main())
