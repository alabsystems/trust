#!/usr/bin/env python3
"""targo trust cite-discharge — compose the proof-carrying certificate (Trust = Clean fusion).

Composes two `targo trust survey` results + a cite-map + the Clean corpus into the honest
per-function ProofCarryingStatus. This is the *toolchain* realization of the cite-discharge:
where tRustc's solver cannot discharge a function's L1 #[ensures] postcondition over an
opaque type, but the soundness link is proved in Clean by a cited theorem, the function is
recorded Certified-modulo-that-kernel-checked-theorem.

SOUND by construction: it only *composes already-verified evidence* (it does not verify
anything itself and cannot make the verifier unsound), and it is FAIL-CLOSED — a captured-
but-undischarged postcondition reaches CertifiedModuloCite only when its cited theorem is
declared AND sorry-free in the corpus; anything else degrades to Incomplete / L0OnlyL1Open.

L0/L1 separation is derived from typed obligation kinds in each full survey:
non-postcondition obligations are L0 and postcondition obligations are L1. The
historical structural/contracts pair is retained as an independent replay
cross-check; `cfg(trust_verify)` is active in both runs, so `--contracts` is a
workflow label rather than a compiler-policy toggle.

Usage:
  trust_cite_discharge.py --structural S.json --contracts C.json --cite-map M.json --corpus DIR
"""
import argparse, glob, json, os, re, sys


def strip_lean_comments(src: str) -> str:
    """Blank nestable block /- ... -/ and line -- ... comments (preserve newlines)."""
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        two = src[i:i + 2]
        if depth > 0:
            if two == "/-":
                depth += 1; out.append("  "); i += 2
            elif two == "-/":
                depth -= 1; out.append("  "); i += 2
            else:
                out.append("\n" if src[i] == "\n" else " "); i += 1
        elif two == "/-":
            depth = 1; out.append("  "); i += 2
        elif two == "--":
            while i < n and src[i] != "\n":
                out.append(" "); i += 1
        else:
            out.append(src[i]); i += 1
    return "".join(out)


def has_token(hay: str, word: str) -> bool:
    return re.search(r"(?<![A-Za-z0-9_])" + re.escape(word) + r"(?![A-Za-z0-9_])", hay) is not None


_DECL = r"(?m)^\s*(theorem|lemma|def|instance|abbrev|structure|inductive|example|end|@\[)"


def theorem_status(corpus_dir: str, thm: str) -> str:
    """'Grounded' (declared + sorry-free), 'HasSorry', or 'NotFound'."""
    found = False
    for path in sorted(glob.glob(os.path.join(corpus_dir, "*.lean"))):
        try:
            src = strip_lean_comments(open(path, encoding="utf-8").read())
        except OSError:
            continue
        m = re.search(r"(?m)^\s*(theorem|lemma)\s+" + re.escape(thm) + r"(?![A-Za-z0-9_])", src)
        if not m:
            continue
        found = True
        body = src[m.start():]
        nxt = re.search(_DECL, body[1:])
        if nxt:
            body = body[: nxt.start() + 1]
        if has_token(body, "sorry") or has_token(body, "admit"):
            return "HasSorry"
    return "Grounded" if found else "NotFound"


def _ob_status(o: dict) -> str:
    return (o.get("outcome") or {}).get("status", "")


def _is_postcondition(o: dict) -> bool:
    # The L1 functional postcondition VC. Trust-verify is ON by default so it appears at
    # every level; we separate L0 from L1 by obligation KIND (the verifier now accounts it
    # as a first-class `postcondition` VC, not `unsupported MIR FullVerification::Postcondition`).
    return o.get("kind") == "Postcondition" or "postcondition" in str(o.get("description", "")).lower()


def analyze(survey: dict) -> dict:
    """Per-function (l0_proved, l1_captured, l1_discharged) from the OBLIGATIONS, not the
    (no-longer-clean) structural verdict. L0-proved = no failed obligation AND every
    non-postcondition (safety/L0) obligation is proved — the safety part is clean, only the
    functional postcondition may be open. L1-captured = >=1 postcondition obligation;
    L1-discharged = every postcondition obligation proved. Fail-closed: any failed or
    unknown SAFETY obligation drops L0-proved to False."""
    out = {}
    for f in survey.get("functions", []):
        obls = f.get("obligations", [])
        post = [o for o in obls if _is_postcondition(o)]
        nonpost = [o for o in obls if not _is_postcondition(o)]
        any_failed = any(_ob_status(o) == "failed" for o in obls)
        l0_proved = (not any_failed) and all(_ob_status(o) == "proved" for o in nonpost)
        l1_captured = len(post) > 0
        l1_discharged = l1_captured and all(_ob_status(o) == "proved" for o in post)
        out[f["function"]] = (l0_proved, l1_captured, l1_discharged)
    return out


def classify(l0_proved, l1_captured, l1_discharged, thm, corpus):
    if not l0_proved:
        return {"status": "Incomplete", "reason": "L0 safety not proved (a non-postcondition obligation failed or is unknown)"}
    if l1_discharged:
        return {"status": "CertifiedToAxioms"}
    if l1_captured and thm:
        g = theorem_status(corpus, thm)
        if g == "Grounded":
            return {"status": "CertifiedModuloCite", "theorem": thm}
        return {"status": "Incomplete", "reason": f"cited theorem `{thm}`: {g}"}
    return {"status": "L0OnlyL1Open"}


def main() -> int:
    ap = argparse.ArgumentParser(description="compose the proof-carrying certificate")
    ap.add_argument("--structural", required=True)
    ap.add_argument("--contracts", required=True)
    ap.add_argument("--cite-map", required=True)
    ap.add_argument("--corpus", required=True)
    a = ap.parse_args()
    # Trust-verify is ON by default, so the structural survey is no longer L0-only; classify
    # from the contracts survey's per-obligation kinds (the structural survey is kept as a
    # fail-closed cross-check — a cited function must not FAIL structurally either).
    structural = analyze(json.load(open(a.structural)))
    contracts = analyze(json.load(open(a.contracts)))
    cite_map = json.load(open(a.cite_map))
    cert = []
    for c in cite_map.get("citations", []):
        fn, thm = c["function"], c["theorem"]
        l0c, capt, disch = contracts.get(fn, (False, False, False))
        l0s = structural.get(fn, (False, False, False))[0]
        cert.append({"function": fn, "theorem": thm,
                     **classify(l0c and l0s, capt, disch, thm, a.corpus)})
    certified = sum(1 for e in cert if e["status"] in ("CertifiedToAxioms", "CertifiedModuloCite"))
    out = {
        "_doc": "Proof-carrying certificate (cite-discharge, Trust = Clean fusion). "
                "Fail-closed composition of structural+contracts surveys + cite-map + Clean corpus.",
        "summary": {"functions": len(cert), "certified": certified},
        "certificate": cert,
    }
    print(json.dumps(out, indent=2))
    # Exit nonzero if any cited function is Incomplete (a broken grounding).
    return 0 if all(e["status"] != "Incomplete" for e in cert) else 1


if __name__ == "__main__":
    sys.exit(main())
