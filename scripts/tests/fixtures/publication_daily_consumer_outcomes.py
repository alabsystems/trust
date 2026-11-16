# Verbatim declarations from publication bin/pub at
# 7b0fb3165f38ed9ab379d26ac0b981ae853c5c2d, SHA256
# 099a2c0b23365d1b470f1983b9495645c6da84db35cf8528acc0b948645124e9.
# A portable test owner, never a production policy fallback. Runtime uses its
# actual snapshotted publication owner. Missing/unaccounted checks are in that
# owner's public_clone_check at lines 7610-7628, outside these declarations.
import re


SIGNAL_DEATH_RE = re.compile(
    r"process didn't exit successfully: `(?P<command>[^`]*)` \(signal: (?P<signal>\d+)")


GATE_LINE_RE = re.compile(
    r"^\s*Gate:\s*(?P<status>[A-Z-]+)\s*\[(?P<lane>[a-z-]+) lane, exit (?P<exit>\d+)\]"
    r"\s*\((?P<counts>[^)]*)\)\s*$", re.M)


GATE_COUNT_RE = re.compile(r"(?P<n>\d+)\s+(?P<kind>[a-z-]+)")


PROOF_LANES = ("advisory", "strict", "certify")


GATE_STATUS_ORDER = ("FAIL", "COULD-NOT-RUN", "CONDITIONAL-PASS", "PASS")


def parse_gate_census(text):
    """The proof census of a check log, aggregated over every gate banner.

    None means the run printed no banner at all — which for a targo lane is a
    broken gate, not a pass (see public_clone_check).

    A committed command may carry more than one verified step, and each prints
    its own banner over its own crate set. Counts are SUMMED across them, so a
    second step cannot hide behind the first and neither can be dropped;
    `banners` says how many were read, and `status` is the worst of them. Counts
    are otherwise verbatim, `total` included, so coverage is visible beside the
    verdicts."""
    matches = list(GATE_LINE_RE.finditer(text or ""))
    if not matches:
        return None
    counts = {}
    for match in matches:
        for found in GATE_COUNT_RE.finditer(match.group("counts")):
            key = found.group("kind").replace("-", "_")
            counts[key] = counts.get(key, 0) + int(found.group("n"))
    statuses = [m.group("status") for m in matches]
    worst = min(statuses,
                key=lambda s: (GATE_STATUS_ORDER.index(s)
                               if s in GATE_STATUS_ORDER else -1))
    lanes = {m.group("lane") for m in matches}
    return {
        "status": worst,
        "lane": lanes.pop() if len(lanes) == 1 else "mixed",
        "exit": max(int(m.group("exit")) for m in matches),
        "counts": counts,
        "banners": len(matches),
    }


ANSI_ESCAPE_RE = re.compile(r"\x1b\[[0-9;?]*[ -/]*[@-~]")


GATE_PASSING_STATUSES = ("PASS", "CONDITIONAL-PASS")


GATE_NO_VERDICT = ("COULD-NOT-RUN", 3)


TARGO_STOPPED_RE = re.compile(r"^targo trust: COULD NOT RUN: ", re.M)


def no_verdict_refusal(census, text, deaths=0):
    """Why an exit 3 is not an admissible no verdict, or None. Admissible is a
    census whose worst banner is `Gate: COULD-NOT-RUN [advisory lane, exit 3]`,
    no refutation, no unit killed by a signal, and no line saying targo
    stopped before its report. Only the advisory lane: there exit 3 means the
    compiler exited 0, while on strict and certify trustc's own fail-closed
    errors exit 3 too, beside which a real compile error cannot be told apart
    (targo-trust pipeline/run.rs, failure_is_verifications)."""
    if not census or (census["status"], census["exit"]) != GATE_NO_VERDICT:
        return "its census is not `Gate: COULD-NOT-RUN [.., exit 3]`"
    if census.get("lane") != "advisory":
        return (f"its banner is on the {census.get('lane')} lane, where a compile error "
                "can exit 3 as well")
    if census["counts"].get("failed", 0):
        return f"its banner counts {census['counts']['failed']} refutation(s)"
    if deaths:
        return f"{deaths} gate unit(s) died of a signal"
    if TARGO_STOPPED_RE.search(ANSI_ESCAPE_RE.sub("", text or "")):
        return "targo stopped before its report (`targo trust: COULD NOT RUN:`)"
    return None


def gate_belt_contradictions(census, text="", deaths=0):
    """Why a census contradicts an exit 0 — each reason its own clause — or
    [] when it does not (or there is no census to contradict it). A no
    verdict is held to no_verdict_refusal, whoever turned its 3 into a 0."""
    if not census:
        return []
    found = []
    failed = census["counts"].get("failed", 0)
    if failed > 0:
        found.append(f"{failed} reported refutation(s)")
    if (census["status"], census["exit"]) == GATE_NO_VERDICT and not failed:
        why = no_verdict_refusal(census, text, deaths)
        return [f"no verdict, but {why}"] if why else found
    if census["status"] not in GATE_PASSING_STATUSES:
        found.append(f"the banner's own verdict is {census['status']}")
    if census["exit"] != 0:
        found.append(f"the banner's own exit is {census['exit']}")
    return found
