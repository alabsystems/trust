#!/usr/bin/env python3
"""Mechanically extract the RFC 8032 section 7.1 Ed25519 test vectors.

Provenance tooling for crates/trust-ed25519/tests/kat_rfc8032.rs. The vectors
are PUBLISHED (RFC 8032, Josefsson & Liusvaara, January 2017); this script
exists so that no human retypes them. Input is the verbatim RFC text from
https://www.rfc-editor.org/rfc/rfc8032.txt.
"""
import re, sys, json, hashlib

HEX = re.compile(r"^[0-9a-f]+$")
LABEL = re.compile(r"^([A-Z][A-Z0-9 ()]*?)(?: \(length (\d+) bytes?\))?:$")

def extract(path):
    t = open(path).read()
    i = t.rindex("7.1.  Test Vectors for Ed25519")
    j = t.index("7.2.  Test Vectors for Ed25519ctx", i)
    tests, cur, label = [], None, None
    for ln in t[i:j].split("\n"):
        s = ln.strip()
        if s.startswith("\x0c") or "Josefsson & Liusvaara" in ln or ln.startswith("RFC 8032 "):
            continue                                    # page furniture
        if s.startswith("-----TEST "):
            cur = {"name": s[len("-----TEST "):].strip(), "f": {}, "len": {}}
            tests.append(cur); label = None; continue
        if cur is None or set(s) == {"-"}:
            continue
        m = LABEL.match(s)
        if m:
            label = m.group(1); cur["f"].setdefault(label, "")
            if m.group(2) is not None: cur["len"][label] = int(m.group(2))
            continue
        if label and HEX.match(s):
            cur["f"][label] += s
        elif s and label and label != "ALGORITHM":
            sys.exit("unparsed line in %s/%s: %r" % (cur["name"], label, s))
    out = []
    for c in tests:
        f = c["f"]
        sk, pk, sig, msg = f["SECRET KEY"], f["PUBLIC KEY"], f["SIGNATURE"], f["MESSAGE"]
        assert f["ALGORITHM"] == "" and len(sk) == 64 and len(pk) == 64 and len(sig) == 128, c["name"]
        assert len(msg) == 2 * c["len"]["MESSAGE"], (c["name"], len(msg), c["len"]["MESSAGE"])
        out.append({"name": c["name"], "sk": sk, "pk": pk, "msg": msg, "sig": sig})
    return out

if __name__ == "__main__":
    path = sys.argv[1]
    print("source sha256:", hashlib.sha256(open(path,'rb').read()).hexdigest())
    v = extract(path)
    for x in v:
        print("TEST %-10s msg=%4d B  pk=%s…" % (x["name"], len(x["msg"])//2, x["pk"][:16]))
    json.dump(v, open(sys.argv[2], "w"))
    print("extracted", len(v), "vectors ->", sys.argv[2])
