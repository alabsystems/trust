#!/bin/sh
""":"
for candidate in python3.14 python3.13 python3.12 python3.11 python3; do
    if command -v "$candidate" >/dev/null 2>&1 \
        && "$candidate" -c 'import sys; raise SystemExit(sys.version_info < (3, 11))' 2>/dev/null; then
        exec "$candidate" "$0" "$@"
    fi
done
echo "odt.py requires Python 3.11+ (tomllib)" >&2
exit 2
":"""
from __future__ import annotations
import os as _floor_os
import shutil as _floor_shutil
import sys as _floor_sys

# Trust: python floor, second half. `python3 odt.py` reads the sh block above
# as a string, so an old `python3` (3.9 on macOS CommandLineTools) re-execs here.
if __name__ == "__main__" and _floor_sys.version_info < (3, 11):
    for _floor_candidate in ("python3.14", "python3.13", "python3.12", "python3.11"):
        _floor_path = _floor_shutil.which(_floor_candidate)
        if _floor_path:
            _floor_argv = [_floor_path, _floor_os.path.abspath(__file__), *_floor_sys.argv[1:]]
            _floor_os.execv(_floor_path, _floor_argv)
    _floor_sys.exit("odt.py requires Python 3.11+ (tomllib); none found on PATH")
__doc__ = """The ODT census, Clean side and Rust side (Stage 0.5 denominator key `odt`).

Design of record: docs/design/2026-09-16-trust-core-architecture.md, §3.2 D-2 (the One
Definition Table: C2's logical views, C6's overrides, C7's identification table) and §5.2
Stage 0.5 ("The ODT census, Clean side and Rust side"; exit E0.12). Its consumers are E2.5.1
("the flat, Box-recursive and generic ADT denominator in `core` and `alloc`"), E2.5.6 ("every
Clean type former in the census"), E3.3.2 ("ODT entries used by Checkpoint A's std"), V12
("C7 row count") and §8.2 question 10 (finite-image large eliminations, polymorphic
recursion, `Type`-valued existentials).

Every number below is recomputed from pinned inputs on every run; nothing is copied from the
design. The inputs, each checked before it is read (fail closed):

  TARGETS     core and alloc for x86_64-apple-darwin, x86_64-unknown-linux-gnu and
              aarch64-unknown-linux-gnu: expanded with an EMPTY sysroot from the same library/,
              core's and compiler_builtins' metadata built for the target first; the procedure
              must reproduce the host's sysroot expansion of both crates byte for byte. std for
              those targets: expanded with an empty sysroot against the metadata of its dependency
              graph for the target, which cargo's -Zbuild-std builds (`targo --unverified check
              --frozen`, a measurement tool) over a `git archive` export at --rev of library/,
              normalized crates/ directories library/'s manifests name, with a fresh
              CARGO_HOME holding only crates.io archives whose sha256 is library/Cargo.lock's
              checksum; std's build-script cfgs and env for the target are replayed. The procedure
              runs for the host too and must reproduce the host's sysroot expansion of std byte for
              byte. A host whose cargo cache lacks a pinned crates.io archive exits 3.
  RUST SIDE   the struct/enum/union definitions of `core`, `alloc` and `std` AFTER macro
              expansion and cfg evaluation for aarch64-apple-darwin (Checkpoint A's host),
              printed by an installed `trustc -Zunpretty=expanded` from library/ as git objects
              record it at --rev (extracted to a temporary directory; never the working tree),
              with std's build-script cfg/env (backtrace_in_libstd, STD_ENV_ARCH) and
              bootstrap's default std features (backtrace, panic-unwind). The toolchain is the
              first of --trustc, the `trustc` on PATH and every atpkg store generation whose
              own commit has the same library/ tree as --rev (ignoring library/Cargo.lock), so
              the sysroot metadata the alloc/std expansion reads is the source being expanded;
              none is refused.
  CLEAN SIDE  (a) the imported Lean 4.8 Init: every inductive in vendor/lean-core-oleans at
              --rev, read from git objects, sha256-checked against its MANIFEST.toml (shared
              set plus each platform set), parsed by the olean reader below, and required to
              give the same census for both platform sets;
              (b) Clean's island prelude (`Environment::with_prelude()`): the D0.5 inventory's
              committed dump (reports/2026-09-17-phase0-d05-one-env-plan/data/prelude.tsv.gz),
              admitted only when the first-party/clean gitlink's `crates/` tree is identical
              to the tree at the clean pin that dump records (so the prelude code is the same);
              (c) the prelude's KERNEL DECLARATIONS: docs/trust-core/denominators/
              odt-prelude-decls.json.gz, the output of this record's probe
              (scripts/trust_core/denominators/odt_prelude_probe, linked to clean-kernel at the
              gitlink), admitted only when its header names the gitlink's crates/ and data/ trees
              and the probe's blobs at --rev; D0.5's structural hashes recomputed from its terms
              must equal prelude.tsv's for every declaration (the two probes read one
              environment). `--probe-prelude` rebuilds the probe and requires it to reproduce the
              dump byte for byte; `--probe-prelude --write` publishes a new one.
  PAIRING     C7's identification rows and C6's override rows, as the design writes them;
              each spelling is quote-checked against the design at --rev.

Every git read is at --rev (default HEAD); scripts/trust_core/denominators.py passes the
record's measured_at_commit, so the pinned re-measurement does not move with HEAD.

Controls, every run, each able to fail (and shown to: it is run once on a perturbed input):
  * Lean 4.8.0's own reader and MetaM re-read the same oleans (LEAN_CONTROL): constant count,
    every inductive's shape, and every constructor field's isProp / isTypeFormerType / sort class
    must equal what this script's olean reader and inferencer derive;
  * trustdoc's JSON of each crate (rustc's resolver) must list every module-level census ADT at
    the same definition path with the same kind, variant/field count and generic parameter
    counts; its extra ADTs must lie in modules holding no census ADT (rustdoc sets cfg(doc));
  * a line regex over the expanded source must count the parsed ADTs plus the ADT keywords
    left inside unexpanded macro bodies;
  * the self-test's literal fixtures (parser traps, recursion, the Freeze analysis, aliases).

Usage:
  odt.py                  measure and print the rows
  odt.py --write          also write docs/trust-core/denominators/odt.toml
  odt.py --check          re-measure and compare with the committed odt.toml (exit 1 on a diff;
                          only the recorded superproject sha may differ)
  odt.py --rev REV        measure at REV (default HEAD)
  odt.py --record F       the record to write or check (default docs/trust-core/denominators/odt.toml)
  odt.py --trustc PATH    the toolchain to expand with (default: see RUST SIDE)
  odt.py --emit-items F   also write the per-item census (one TSV row per ADT, inductive and
                          quotient type former, whose sha256 odt.toml records) to F. --write publishes it as
                          docs/trust-core/denominators/odt-items.tsv.gz beside the record, and
                          --check fails unless that file decompresses to this measurement's census
  odt.py --self-test      run the literal-fixture self-test only
  odt.py --probe-prelude [--write]
                          rebuild the prelude probe with `targo --unverified` against a `git archive`
                          of first-party/clean at --rev's gitlink (cached under the artifact cache)
                          and require it to reproduce the committed dump (--write: publish it)
Exit status 2: an input or a control refused; nothing is published. Exit status 3: a pinned input this
host does not hold (no Trust toolchain built from the pinned library/ tree, or no targo of its build; no
Lean 4.8.0; a crates.io archive library/Cargo.lock pins for std's graph missing from the cargo cache), so
the record cannot be re-measured here: not drift, and never a pass.

Python 3.9+ standard library only.
"""

import argparse
import collections
import gzip
import hashlib
import json
import os
import re
import shutil
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]
TOML_REL = "docs/trust-core/denominators/odt.toml"
ITEMS_REL = "docs/trust-core/denominators/odt-items.tsv.gz"
SCRIPT_REL = "scripts/trust_core/denominators/odt.py"
DESIGN_REL = "docs/design/2026-09-16-trust-core-architecture.md"
OLEANS_REL = "vendor/lean-core-oleans"
D05_REL = "reports/2026-09-17-phase0-d05-one-env-plan/data"
BIGNUM_REL = "crates/trust-bignum/src/lib.rs"
# The prelude's kernel declarations: the probe that dumps them and the committed dump (gzip, a JSON header
# line naming the clean trees and the probe's blobs, then the probe's stdout).
PRELUDE_DECLS_REL = "docs/trust-core/denominators/odt-prelude-decls.json.gz"
PROBE_REL = "scripts/trust_core/denominators/odt_prelude_probe"
PROBE_FILES = ("Cargo.toml.in", "src/main.rs")
PRELUDE_SCHEMA = "trust.core.odt-prelude-decls.v1"
HOST = "aarch64-apple-darwin"
SCHEMA = "trust.core.denominator.v1"
# The superproject revision every git read is at (--rev). main() resolves it to a commit.
REV = "HEAD"
# --trustc, when given: the only toolchain tried.
TRUSTC = None


class Refusal(Exception):
    """An input failed its check; the measurement is not published."""


class Unavailable(Refusal):
    """A pinned input this host does not hold (a Trust toolchain built from the pinned library/ tree,
    Lean 4.8.0): the record cannot be re-measured here. Exit 3, which is neither drift nor a pass."""


# ---------------------------------------------------------------------------
# git
# ---------------------------------------------------------------------------


def git(*args, repo=REPO, binary=False, ok=(0,)):
    env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
    run = subprocess.run(["git", "--no-replace-objects", "-C", str(repo), *args],
                         capture_output=True, env=env)
    if run.returncode not in ok:
        raise Refusal(f"git {' '.join(args)} failed: {run.stderr.decode(errors='replace').strip()}")
    return run.stdout if binary else run.stdout.decode()


def git_blob(rev_path, repo=REPO):
    return git("cat-file", "blob", rev_path, repo=repo, binary=True)


def git_blobs(paths, rev=None, repo=REPO):
    """Many blobs in one `git cat-file --batch` call; returns {path: bytes}."""
    rev = REV if rev is None else rev
    env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
    req = "".join(f"{rev}:{p}\n" for p in paths).encode()
    run = subprocess.run(["git", "--no-replace-objects", "-C", str(repo), "cat-file", "--batch"],
                         input=req, capture_output=True, env=env)
    if run.returncode != 0:
        raise Refusal("git cat-file --batch failed")
    out, pos, res = run.stdout, 0, {}
    for p in paths:
        nl = out.index(b"\n", pos)
        header = out[pos:nl].decode()
        if header.endswith("missing"):
            raise Refusal(f"{rev}:{p} is not in git objects")
        size = int(header.split()[2])
        res[p] = out[nl + 1:nl + 1 + size]
        pos = nl + 1 + size + 1
    return res


def sha256(b):
    return hashlib.sha256(b).hexdigest()


# ---------------------------------------------------------------------------
# Lean 4.8 .olean reader (compacted region; Lean 4 `olean_header` + object graph)
# ---------------------------------------------------------------------------

KINDS = ("axiom", "definition", "theorem", "opaque", "quot", "inductive", "constructor", "recursor")
# Lean 4.8's QuotKind, in declaration order (the scalar a QuotVal carries).
QUOT_KINDS = ("type", "ctor", "lift", "ind")
# clean-kernel's QuotKind as the prelude probe prints it (Type, Mk, Lift, Ind, Sound), in Lean's spelling.
CLEAN_QUOT_KINDS = {"type": "type", "mk": "ctor", "lift": "lift", "ind": "ind", "sound": "sound"}
# The four quotient constants the kernel's quotient extension declares, by kind; the type former is the one of
# kind `type`. Both environments must name them so, or the quotient rows are not published.
QUOT_NAMES = {"type": "Quot", "ctor": "Quot.mk", "lift": "Quot.lift", "ind": "Quot.ind"}


def quot_type_formers(consts, label):
    """The names of `consts` (kind `quot`) whose quotient kind is `type`: the quotient type formers. Every
    quotient constant of a kind QUOT_NAMES names must carry that name (fail closed: a misread kind or a renamed
    constant stops the count). Clean's kernel also declares `Quot.sound` as a quotient constant of kind
    `sound`, where Lean 4.8 has an axiom; that kind is not a type former and is not in QUOT_NAMES."""
    formers = []
    for name, rec in sorted(consts.items()):
        if rec["kind"] != "quot":
            continue
        kind = rec.get("quot_kind")
        if kind in QUOT_NAMES and QUOT_NAMES[kind] != name:
            raise Refusal(f"{label}: the quotient constant of kind {kind} is {name}, not {QUOT_NAMES[kind]}")
        if kind not in QUOT_NAMES and kind != "sound":
            raise Refusal(f"{label}: quotient constant {name} has kind {kind!r}")
        if kind == "type":
            formers.append(name)
    return formers


def opaque_type_formers(env, inf, label):
    """Type formers declared WITHOUT a definition the census could unfold: the `axiom` and `opaque` constants
    whose type, after its Pi telescope (each step read through whnf), ends in a sort other than `Prop`
    (`Sort (l+1)`, or `Sort u` for a universe parameter). `IO : Type -> Type`, `Monad`, `StateM` declared as
    axioms in Clean's island prelude are such type formers: no inductive row counts them, so E2.5.6's
    "every Clean type former" needs this row. Returns (sorted [(name, sort class)], sorted unclassified names):
    a type whose end the reader cannot reach is unclassified, never silently not-a-type-former."""
    formers, unclassified = [], []
    for name, rec in sorted(env.consts.items()):
        if rec["kind"] not in ("axiom", "opaque"):
            continue
        t = env.type_of(name)
        for _ in range(10_000):
            if t is None or t[0] == "S":
                break
            if t[0] == "P":
                t = t[3]
                continue
            w = inf.whnf(t)
            if w is None or w == t:
                break
            t = w
        if t is None:
            unclassified.append(name)
        elif t[0] == "S":
            cls = sort_class(t[1])
            if cls != "prop":
                formers.append((name, cls))
    return formers, unclassified


class Olean:
    """One .olean file. Pointers are absolute addresses in the region mapped at `base`;
    scalars are boxed (odd). Layouts are Lean 4.8's: header 48 bytes + base + root."""

    def __init__(self, data, label):
        if data[:5] != b"olean" or data[5] != 1:
            raise Refusal(f"{label}: not a version-1 olean")
        self.data, self.label = data, label
        self.githash = data[6:48].rstrip(b"\0").decode()
        self.base, self.root = struct.unpack_from("<QQ", data, 48)
        self._names, self._exprs, self._levels = {}, {}, {}

    def _off(self, p):
        o = p - self.base
        if o < 64 or o + 8 > len(self.data):
            raise Refusal(f"{self.label}: pointer {p:#x} outside the region")
        return o

    def ctor(self, p):
        if p & 1:
            return p >> 1, (), None
        o = self._off(p)
        _rc, _cs, other, tag = struct.unpack_from("<iHBB", self.data, o)
        if tag > 244:
            raise Refusal(f"{self.label}: expected a constructor object, got tag {tag}")
        return tag, struct.unpack_from(f"<{other}Q", self.data, o + 8), o + 8 + 8 * other

    def string(self, p):
        o = self._off(p)
        if self.data[o + 7] != 249:
            raise Refusal(f"{self.label}: expected a string")
        size = struct.unpack_from("<Q", self.data, o + 8)[0]
        return self.data[o + 32:o + 32 + size - 1].decode("utf-8")

    def array(self, p):
        o = self._off(p)
        if self.data[o + 7] != 246:
            raise Refusal(f"{self.label}: expected an array")
        size = struct.unpack_from("<Q", self.data, o + 8)[0]
        return struct.unpack_from(f"<{size}Q", self.data, o + 24)

    def nat(self, p):
        if p & 1:
            return p >> 1
        if self.data[self._off(p) + 7] == 250:
            return "bignum"
        raise Refusal(f"{self.label}: expected a Nat")

    def name(self, p):
        if p in self._names:
            return self._names[p]
        if p & 1:
            if p != 1:
                raise Refusal(f"{self.label}: bad Name scalar")
            return ""
        tag, f, _ = self.ctor(p)
        pre = self.name(f[0])
        if tag == 1:
            comp = self.string(f[1])
        elif tag == 2:
            comp = str(self.nat(f[1]))
        else:
            raise Refusal(f"{self.label}: bad Name tag {tag}")
        r = comp if pre == "" else pre + "." + comp
        self._names[p] = r
        return r

    def lst(self, p):
        out = []
        while not (p & 1):
            tag, f, _ = self.ctor(p)
            if tag != 1:
                raise Refusal(f"{self.label}: bad List")
            out.append(f[0])
            p = f[1]
        return out

    def u8(self, scalar_off, i):
        return self.data[scalar_off + i]

    def level(self, p):
        if p in self._levels:
            return self._levels[p]
        tag, f, _ = self.ctor(p)
        if tag == 0:
            r = ("0",)
        elif tag == 1:
            r = ("+", self.level(f[0]))
        elif tag == 2:
            r = ("max", self.level(f[0]), self.level(f[1]))
        elif tag == 3:
            r = ("imax", self.level(f[0]), self.level(f[1]))
        elif tag == 4:
            r = ("p", self.name(f[0]))
        else:
            r = ("m",)
        self._levels[p] = r
        return r

    def expr(self, p):
        """Expr as nested tuples: B bvar, S sort, C const, A app, L lam, P pi, Z let,
        N/T literals, J proj; mdata is transparent."""
        memo = self._exprs
        if p in memo:
            return memo[p]
        tag, f, so = self.ctor(p)
        if tag == 0:
            r = ("B", self.nat(f[0]))
        elif tag == 3:
            r = ("S", self.level(f[0]))
        elif tag == 4:
            r = ("C", self.name(f[0]), tuple(self.level(x) for x in self.lst(f[1])))
        elif tag == 5:
            r = ("A", self.expr(f[0]), self.expr(f[1]))
        elif tag in (6, 7):
            r = ("L" if tag == 6 else "P", self.name(f[0]), self.expr(f[1]), self.expr(f[2]))
        elif tag == 8:
            r = ("Z", self.name(f[0]), self.expr(f[1]), self.expr(f[2]), self.expr(f[3]))
        elif tag == 9:
            lt, lf, _ = self.ctor(f[0])
            r = ("N", self.nat(lf[0])) if lt == 0 else ("T", self.string(lf[0]))
        elif tag == 10:
            r = self.expr(f[1])
        elif tag == 11:
            r = ("J", self.name(f[0]), self.nat(f[1]), self.expr(f[2]))
        else:
            r = ("?", tag)
        memo[p] = r
        return r


class LeanEnv:
    """All constants of an Init closure, decoded lazily."""

    def __init__(self, files):
        self.consts = {}
        self.structures, self.classes = set(), set()
        self.records = collections.Counter()
        for label, data in sorted(files.items()):
            o = Olean(data, label)
            _t, root, _ = o.ctor(o.root)
            if len(root) != 5:
                raise Refusal(f"{label}: ModuleData has {len(root)} fields, expected 5 (Lean 4.8)")
            for c in o.array(root[2]):
                ktag, kf, _ = o.ctor(c)
                if ktag > 7:
                    raise Refusal(f"{label}: ConstantInfo tag {ktag}")
                vtag, vf, vso = o.ctor(kf[0])
                _ct, cvf, _ = o.ctor(vf[0])
                name = o.name(cvf[0])
                self.records[KINDS[ktag]] += 1
                rec = {"kind": KINDS[ktag], "o": o, "lparams": [o.name(x) for x in o.lst(cvf[1])],
                       "type": cvf[2], "value": None, "module": label}
                if ktag in (1, 2, 3):
                    rec["value"] = vf[1]
                if ktag == 5:
                    if len(vf) != 5:
                        raise Refusal(f"{label}: InductiveVal has {len(vf)} object fields; the "
                                      "Lean 4.8 layout (isNested as a Bool) has 5")
                    rec.update(nparams=o.nat(vf[1]), nindices=o.nat(vf[2]),
                               all=[o.name(x) for x in o.lst(vf[3])],
                               ctors=[o.name(x) for x in o.lst(vf[4])],
                               is_rec=o.u8(vso, 0), is_unsafe=o.u8(vso, 1),
                               is_reflexive=o.u8(vso, 2), is_nested=o.u8(vso, 3))
                elif ktag == 6:
                    rec.update(induct=o.name(vf[1]), cidx=o.nat(vf[2]), nparams=o.nat(vf[3]),
                               nfields=o.nat(vf[4]))
                elif ktag == 4:
                    # QuotVal: toConstantVal, then `kind : QuotKind` (type | ctor | lift | ind) as a scalar
                    if len(vf) != 1 or o.u8(vso, 0) >= len(QUOT_KINDS):
                        raise Refusal(f"{label}: QuotVal of {name} is not the Lean 4.8 layout")
                    rec["quot_kind"] = QUOT_KINDS[o.u8(vso, 0)]
                if name in self.consts and self.consts[name]["kind"] != rec["kind"]:
                    raise Refusal(f"{name} declared twice with different kinds")
                self.consts.setdefault(name, rec)
            for e in o.array(root[4]):
                _et, ef, _ = o.ctor(e)
                ext = o.name(ef[0])
                if ext == "Lean.structureExt":
                    for s in o.array(ef[1]):
                        self.structures.add(o.name(o.ctor(s)[1][0]))
                elif ext == "Lean.classExtension":
                    for s in o.array(ef[1]):
                        self.classes.add(o.name(o.ctor(s)[1][0]))

    def type_of(self, name):
        r = self.consts[name]
        if "_type" not in r:
            r["_type"] = r["o"].expr(r["type"])
        return r["_type"]

    def value_of(self, name):
        r = self.consts.get(name)
        if not r or r["kind"] != "definition" or r["value"] is None:
            return None
        if "_value" not in r:
            r["_value"] = r["o"].expr(r["value"])
        return r["_value"]


# --- a small, conservative type inferencer (enough to find a field's sort) ------------------


def lift(e, n, k=0):
    if n == 0:
        return e
    t = e[0]
    if t == "B":
        return ("B", e[1] + n) if e[1] >= k else e
    if t == "A":
        return ("A", lift(e[1], n, k), lift(e[2], n, k))
    if t in ("L", "P"):
        return (t, e[1], lift(e[2], n, k), lift(e[3], n, k + 1))
    if t == "Z":
        return ("Z", e[1], lift(e[2], n, k), lift(e[3], n, k), lift(e[4], n, k + 1))
    if t == "J":
        return ("J", e[1], e[2], lift(e[3], n, k))
    return e


def subst(e, v, k=0):
    """body[bvar k := v], v closed relative to the binder being removed."""
    t = e[0]
    if t == "B":
        i = e[1]
        if i == k:
            return lift(v, k)
        return ("B", i - 1) if i > k else e
    if t == "A":
        return ("A", subst(e[1], v, k), subst(e[2], v, k))
    if t in ("L", "P"):
        return (t, e[1], subst(e[2], v, k), subst(e[3], v, k + 1))
    if t == "Z":
        return ("Z", e[1], subst(e[2], v, k), subst(e[3], v, k), subst(e[4], v, k + 1))
    if t == "J":
        return ("J", e[1], e[2], subst(e[3], v, k))
    return e


def inst_level(l, m):
    t = l[0]
    if t == "p":
        return m.get(l[1], l)
    if t == "+":
        return ("+", inst_level(l[1], m))
    if t in ("max", "imax"):
        return (t, inst_level(l[1], m), inst_level(l[2], m))
    return l


def inst_levels(e, m):
    if not m:
        return e
    t = e[0]
    if t == "S":
        return ("S", inst_level(e[1], m))
    if t == "C":
        return ("C", e[1], tuple(inst_level(x, m) for x in e[2]))
    if t == "A":
        return ("A", inst_levels(e[1], m), inst_levels(e[2], m))
    if t in ("L", "P"):
        return (t, e[1], inst_levels(e[2], m), inst_levels(e[3], m))
    if t == "Z":
        return ("Z", e[1], inst_levels(e[2], m), inst_levels(e[3], m), inst_levels(e[4], m))
    if t == "J":
        return ("J", e[1], e[2], inst_levels(e[3], m))
    return e


def level_zero(l):
    """True: surely 0; False: surely >= 1; None: depends on a universe parameter."""
    t = l[0]
    if t == "0":
        return True
    if t == "+":
        return False
    if t == "max":
        a, b = level_zero(l[1]), level_zero(l[2])
        if a is False or b is False:
            return False
        return True if (a and b) else None
    if t == "imax":
        return level_zero(l[2])
    return None


def spine(e):
    args = []
    while e[0] == "A":
        args.append(e[2])
        e = e[1]
    args.reverse()
    return e, args


def mk_app(h, args):
    for a in args:
        h = ("A", h, a)
    return h


class Infer:
    FUEL = 64

    def __init__(self, env):
        self.env = env

    def const_type(self, c):
        r = self.env.consts.get(c[1])
        if r is None:
            return None
        return inst_levels(self.env.type_of(c[1]), dict(zip(r["lparams"], c[2])))

    def whnf(self, e, fuel=FUEL):
        while fuel > 0:
            fuel -= 1
            t = e[0]
            if t == "Z":
                e = subst(e[4], e[3])
                continue
            h, args = spine(e)
            if h[0] == "L" and args:
                e = mk_app(subst(h[3], args[0]), args[1:])
                continue
            if h[0] == "C":
                v = self.env.value_of(h[1])
                if v is not None:
                    r = self.env.consts[h[1]]
                    e = mk_app(inst_levels(v, dict(zip(r["lparams"], h[2]))), args)
                    continue
            return e
        return None

    def infer(self, e, ctx):
        t = e[0]
        if t == "B":
            return lift(ctx[-1 - e[1]], e[1] + 1) if e[1] < len(ctx) else None
        if t == "S":
            return ("S", ("+", e[1]))
        if t == "C":
            return self.const_type(e)
        if t == "N":
            return ("C", "Nat", ())
        if t == "T":
            return ("C", "String", ())
        if t == "P":
            la = self.sort_level(e[2], ctx)
            lb = self.sort_level(e[3], ctx + [e[2]])
            if la is None or lb is None:
                return None
            return ("S", ("imax", la, lb))
        if t == "L":
            b = self.infer(e[3], ctx + [e[2]])
            return None if b is None else ("P", e[1], e[2], b)
        if t == "Z":
            return self.infer(subst(e[4], e[3]), ctx)
        if t == "A":
            h, args = spine(e)
            ty = self.infer(h, ctx)
            for a in args:
                if ty is None:
                    return None
                if ty[0] != "P":
                    ty = self.whnf(ty)
                    if ty is None or ty[0] != "P":
                        return None
                ty = subst(ty[3], a)
            return ty
        return None

    def sort_level(self, e, ctx):
        ty = self.infer(e, ctx)
        if ty is None:
            return None
        if ty[0] != "S":
            ty = self.whnf(ty)
        return ty[1] if ty is not None and ty[0] == "S" else None

    def type_former(self, e):
        """None, or the class of the Sort that ends the field's type when that type is a Sort or a
        telescope ending in one: "prop-family" (a proposition or predicate/relation: `Prop`,
        `α → α → Prop`) or "type-family" (a type or type family: `Type u`, `Type u → Type u`, `Sort v`)."""
        for _ in range(self.FUEL):
            if e is None:
                return None
            if e[0] == "S":
                return "prop-family" if level_zero(e[1]) is True else "type-family"
            if e[0] == "P":
                e = e[3]
                continue
            w = self.whnf(e)
            if w is None or w == e:
                return None
            e = w
        return None


def bvars_free(e, depth=0, acc=None):
    """Free bvar indices of e, relative to the context e sits in."""
    if acc is None:
        acc = set()
    t = e[0]
    if t == "B":
        if e[1] >= depth:
            acc.add(e[1] - depth)
    elif t == "A":
        bvars_free(e[1], depth, acc)
        bvars_free(e[2], depth, acc)
    elif t in ("L", "P"):
        bvars_free(e[2], depth, acc)
        bvars_free(e[3], depth + 1, acc)
    elif t == "Z":
        bvars_free(e[2], depth, acc)
        bvars_free(e[3], depth, acc)
        bvars_free(e[4], depth + 1, acc)
    elif t == "J":
        bvars_free(e[3], depth, acc)
    return acc


def occurrences(e, targets, depth=0, out=None):
    """(name, args, depth) for each application of a target constant inside e."""
    if out is None:
        out = []
    h, args = spine(e)
    if h[0] == "C" and h[1] in targets:
        out.append((h[1], args, depth))
    elif h[0] in ("L", "P"):
        occurrences(h[2], targets, depth, out)
        occurrences(h[3], targets, depth + 1, out)
    elif h[0] == "Z":
        occurrences(h[2], targets, depth, out)
        occurrences(h[3], targets, depth, out)
        occurrences(h[4], targets, depth + 1, out)
    elif h[0] == "J":
        occurrences(h[3], targets, depth, out)
    for a in args:
        occurrences(a, targets, depth, out)
    return out


def sort_class(level):
    z = level_zero(level)
    return "prop" if z is True else ("type" if z is False else "sort-poly")


# E2.5.6's rows ("How far the pillar goes under that line", design §3.2), as this census
# assigns them. The first matching rule wins; each is a mechanical predicate on the kernel data.
E256 = (
    ("prop", "Prop-sorted: erased (C5), no representation needed"),
    ("unsafe", "unsafe inductive: outside the kernel's logic"),
    ("class", "class: C3 maps class bounds to trait bounds and P6 monomorphizes classes, so no runtime representation is asked of it"),
    ("indexed-family", "Indexed family (numIndices > 0): ODT M7, needs OD-9"),
    ("type-valued-existential", "a field that is a type or type family (`Type u`, `Type u → Type v`, not Prop-valued): `Type`-valued existential without a class, refused"),
    ("polymorphic-recursion", "recursive occurrence at other parameters: polymorphic recursion, refused"),
    ("reflexive", "reflexive (a function-typed field returning the type): no row in the design table"),
    ("large-elim-field", "data field whose type is a definition applied to an earlier data field: large elimination (finite or infinite image not decided here), ODT M7 or refused"),
    ("dependent-data-field", "data field whose type depends on an earlier data field (dependent pair / literal-index form): ODT M7"),
    ("recursive", "recursive, mutual or nested: `trust::Edge` positions, ODT M5"),
    ("invariant-bearing", "non-recursive with a Prop field or a Prop-valued-family field (erased; a subtype-like invariant): ODT M4"),
    ("non-recursive", "non-recursive inductive or structure with carrier fields: first slice, ODT M3"),
)


def classify_inductive(env, inf, name):
    r = env.consts[name]
    np_, ni = r["nparams"], r["nindices"]
    ty = env.type_of(name)
    t = ty
    ctx = []
    for _ in range(np_ + ni):
        if t[0] != "P":
            t = inf.whnf(t)
        ctx.append(t[2])
        t = t[3]
    if t[0] != "S":
        t = inf.whnf(t)
    sort = sort_class(t[1]) if t is not None and t[0] == "S" else "unknown"
    info = {"name": name, "module": r["module"], "sort": sort, "nparams": np_, "nindices": ni,
            "nctors": len(r["ctors"]), "mutual": len(r["all"]), "is_rec": bool(r["is_rec"]),
            "is_nested": bool(r["is_nested"]), "is_reflexive": bool(r["is_reflexive"]),
            "is_unsafe": bool(r["is_unsafe"]), "structure": name in env.structures,
            "class": name in env.classes, "fields": 0, "prop_fields": 0, "data_fields": 0,
            "poly_fields": 0, "type_fields": 0, "prop_family_fields": 0, "unclassified_fields": 0,
            "poly_rec": [], "dep_fields": [], "large_elim_fields": [], "ctor_names": [],
            "field_classes": []}
    targets = set(r["all"])
    for cname in r["ctors"]:
        c = env.consts[cname]
        info["ctor_names"].append(cname[len(name) + 1:] if cname.startswith(name + ".") else cname)
        ct = env.type_of(cname)
        ctx = []
        data_binders = set()
        classes = []
        info["field_classes"].append(classes)
        for i in range(c["nparams"] + c["nfields"]):
            if ct[0] != "P":
                ct = inf.whnf(ct)
                if ct is None or ct[0] != "P":
                    raise Refusal(f"{cname}: constructor telescope shorter than its arity")
            fty = ct[2]
            if i >= c["nparams"]:
                info["fields"] += 1
                lvl = inf.sort_level(fty, ctx)
                cls = "unclassified" if lvl is None else sort_class(lvl)
                former = inf.type_former(fty) if cls != "prop" else None
                classes.append(former or cls)
                if former == "type-family":
                    info["type_fields"] += 1
                    cls = "type-former"
                elif former == "prop-family":
                    info["prop_family_fields"] += 1
                    cls = "type-former"
                elif cls == "prop":
                    info["prop_fields"] += 1
                elif cls == "type":
                    info["data_fields"] += 1
                elif cls == "sort-poly":
                    info["poly_fields"] += 1
                else:
                    info["unclassified_fields"] += 1
                if cls in ("type", "sort-poly"):
                    depth = len(ctx)
                    free = bvars_free(fty)
                    earlier = {depth - 1 - b for b in free}
                    if earlier & data_binders:
                        h, _a = spine(fty)
                        kind = "family-param"
                        if h[0] == "C":
                            hk = env.consts.get(h[1], {}).get("kind")
                            kind = "inductive-index" if hk == "inductive" else (
                                "definition" if hk == "definition" else str(hk))
                        field_no = i - c["nparams"]
                        if kind == "definition":
                            info["large_elim_fields"].append(f"{cname}#{field_no}:{h[1]}")
                        info["dep_fields"].append(f"{cname}#{field_no}:{kind}")
                    data_binders.add(len(ctx))
                for (_n, args, d) in occurrences(fty, targets):
                    here = len(ctx) + d
                    want = [("B", here - 1 - j) for j in range(np_)]
                    if list(args[:np_]) != want:
                        info["poly_rec"].append(f"{cname}#{i - c['nparams']}")
            ctx.append(fty)
            ct = ct[3]
    if info["sort"] == "prop":
        cat = "prop"
    elif info["is_unsafe"]:
        cat = "unsafe"
    elif info["class"]:
        cat = "class"
    elif ni > 0:
        cat = "indexed-family"
    elif info["type_fields"]:
        cat = "type-valued-existential"
    elif info["poly_rec"]:
        cat = "polymorphic-recursion"
    elif info["is_reflexive"]:
        cat = "reflexive"
    elif info["large_elim_fields"]:
        cat = "large-elim-field"
    elif info["dep_fields"]:
        cat = "dependent-data-field"
    elif info["is_rec"] or info["mutual"] > 1 or info["is_nested"]:
        cat = "recursive"
    elif info["prop_fields"] or info["prop_family_fields"]:
        cat = "invariant-bearing"
    else:
        cat = "non-recursive"
    info["e256"] = cat
    return info


# The Lean-side control: Lean 4.8's own reader and elaborator (MetaM) over the same oleans. For
# every inductive it prints the kernel shape and, for every constructor field, `isProp` /
# `isTypeFormerType` / the sort of its type: the facts this script's reader and inferencer derive.
LEAN_CONTROL = r"""import Lean
open Lean Meta

def fieldClass (x : Expr) : MetaM String := do
  let t ← inferType x
  if (← isProp t) then return "prop"
  if (← isTypeFormerType t) then
    -- a type or type family: does the telescope end in Prop?
    let r ← forallTelescopeReducing t fun _ b => do
      let b ← whnf b
      match b with
      | .sort l => return (if l.isZero then "prop-family" else "type-family")
      | _ => return "type-family"
    return r
  let s ← whnf (← inferType t)
  match s with
  | .sort l =>
    let l := l.normalize
    if l.isZero then return "prop"
    else if l.isNeverZero then return "type"
    else return "sort-poly"
  | _ => return "unclassified"

def ctorFields (env : Environment) (c : Name) : MetaM (List String) := do
  let some (.ctorInfo cv) := env.find? c | return ["missing"]
  forallTelescopeReducing cv.type fun xs _ => do
    let mut out := #[]
    for i in [cv.numParams:xs.size] do
      out := out.push (← fieldClass xs[i]!)
    return out.toList

def runMeta (env : Environment) (x : MetaM α) : IO α := do
  let ctx : Core.Context := { fileName := "", fileMap := default, maxHeartbeats := 0 }
  let st : Core.State := { env := env }
  let r ← (x.run' {} {}).toIO ctx st
  return r.1

def main (args : List String) : IO UInt32 := do
  match args with
  | out :: dirs@(_ :: _) =>
    searchPathRef.set (dirs.map System.FilePath.mk)
    let env ← importModules #[{module := `Init}] {} 0
    let h ← IO.FS.Handle.mk out .write
    let mut n := 0
    for (name, c) in env.constants.toList do
      match c with
      | .inductInfo v =>
        let fields ← try
            let fs ← runMeta env (v.ctors.mapM (ctorFields env))
            pure ("|".intercalate (fs.map (",".intercalate ·)))
          catch e => pure s!"ERROR {e}"
        h.putStrLn s!"{name.toString (escape := false)}\t{v.numParams}\t{v.numIndices}\t{v.all.length}\t{",".intercalate (v.ctors.map (·.toString (escape := false)))}\t{v.isRec}\t{v.isNested}\t{v.isReflexive}\t{v.isUnsafe}\t{isStructure env name}\t{isClass env name}\t{fields}"
        n := n + 1
      | _ => pure ()
    h.putStrLn s!"#constants\t{env.constants.toList.length}"
    h.flush
    IO.println s!"[odt-census] {n} inductives"
    return 0
  | _ =>
    IO.eprintln "usage: lean --run OdtCensus.lean OUT DIR [DIR...]"
    return 2
"""


def lean48():
    """The Lean 4.8.0 binary the Clean-side control runs, and its version line."""
    cands = [os.environ.get("LEAN48_BIN", ""),
             str(Path.home() / ".elan" / "toolchains" / "leanprover--lean4---v4.8.0" / "bin" / "lean")]
    exe = next((c for c in cands if c and Path(c).is_file()), None)
    if exe is None:
        raise Unavailable("Lean 4.8.0 is not installed (elan toolchain leanprover/lean4:v4.8.0, or $LEAN48_BIN); "
                          "the Clean-side control needs it")
    ver = subprocess.run([exe, "--version"], capture_output=True, text=True).stdout
    if "version 4.8.0" not in ver:
        raise Unavailable(f"{exe} is not Lean 4.8.0: {ver.strip()}")
    return exe, ver


def lean_control(env, inds, files):
    """Run LEAN_CONTROL with Lean 4.8.0 over a tree holding exactly `files`; require agreement."""
    exe, ver = lean48()
    work = tempfile.mkdtemp(prefix="odt-lean-")
    try:
        for rel, data in files.items():
            dest = Path(work, "oleans", rel)
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(data)
        Path(work, "OdtCensus.lean").write_text(LEAN_CONTROL)
        out = Path(work, "out.tsv")
        run = subprocess.run([exe, "--run", "OdtCensus.lean", str(out), str(Path(work, "oleans"))],
                             cwd=work, capture_output=True, text=True)
        if run.returncode != 0:
            raise Refusal(f"the Lean control failed: {(run.stderr or run.stdout).strip()[:300]}")
        rows = {}
        total = None
        for line in out.read_text().splitlines():
            c = line.split("\t")
            if c[0] == "#constants":
                total = int(c[1])
            else:
                rows[c[0]] = c[1:]
    finally:
        shutil.rmtree(work, ignore_errors=True)
    if total != len(env.consts):
        raise Refusal(f"Lean control: Lean reads {total} constants, this reader {len(env.consts)}")
    if set(rows) != set(inds):
        raise Refusal(f"Lean control: inductive sets differ ({len(set(rows) ^ set(inds))} names)")
    def compare(view):
        shape_diff, field_diff = [], []
        for n, (shape, fields) in view.items():
            if shape != rows[n][:10]:
                shape_diff.append(n)
            if fields != rows[n][10]:
                field_diff.append(n)
        return shape_diff, field_diff

    view = {}
    for n, i in inds.items():
        r = env.consts[n]
        view[n] = ([str(r["nparams"]), str(r["nindices"]), str(len(r["all"])), ",".join(r["ctors"]),
                    str(bool(r["is_rec"])).lower(), str(bool(r["is_nested"])).lower(),
                    str(bool(r["is_reflexive"])).lower(), str(bool(r["is_unsafe"])).lower(),
                    str(i["structure"]).lower(), str(i["class"]).lower()],
                   "|".join(",".join(cs) for cs in i["field_classes"]))
    shape_diff, field_diff = compare(view)
    # the comparison must be able to fail: one parameter count and one field class, perturbed
    probe = sorted(n for n in view if view[n][1])[0]
    bad = dict(view)
    bad[probe] = ([str(int(view[probe][0][0]) + 1)] + view[probe][0][1:], view[probe][1])
    first = re.match(r"[^,|]*", view[probe][1]).group(0)
    bad2 = dict(view)
    bad2[probe] = (view[probe][0], ("prop" if first != "prop" else "type") + view[probe][1][len(first):])
    if compare(bad) == ([], []) or compare(bad2) == ([], []):
        raise Refusal("Lean control: the comparison does not detect a perturbed shape or field class")
    if shape_diff or field_diff:
        raise Refusal(f"Lean control: {len(shape_diff)} inductives differ in shape ({shape_diff[:3]}), "
                      f"{len(field_diff)} in their field classes ({field_diff[:3]})")
    return {"lean": ver.strip(), "constants": total, "inductives": len(rows),
            "fields": sum(len(cs) for i in inds.values() for cs in i["field_classes"])}


def parse_manifest(text):
    """{None: {path: sha}, triple: {path: sha}} from the v2 MANIFEST.toml (flat string pairs)."""
    sets, cur = {}, None
    for line in text.splitlines():
        line = line.strip()
        m = re.fullmatch(r'\[(files|platforms\."([^"]+)"\.files)\]', line)
        if m:
            cur = m.group(2)
            sets[cur] = {}
            continue
        if line.startswith("["):
            cur = "__other__"
            continue
        m = re.fullmatch(r'"([^"]+\.olean)"\s*=\s*"([0-9a-f]{64})"', line)
        if m and cur != "__other__" and cur in sets:
            sets[cur][m.group(1)] = m.group(2)
    if None not in sets:
        raise Refusal("MANIFEST.toml has no [files] table")
    return sets


def lean48_census():
    man_text = git_blob(f"{REV}:{OLEANS_REL}/MANIFEST.toml").decode()
    if 'lean_toolchain = "leanprover/lean4:v4.8.0"' not in man_text:
        raise Refusal("vendor/lean-core-oleans is not the Lean 4.8.0 closure")
    sets = parse_manifest(man_text)
    triples = sorted(k for k in sets if k)
    if HOST not in triples:
        raise Refusal(f"MANIFEST.toml has no platform set for {HOST}")
    shared = sets[None]
    paths = [f"{OLEANS_REL}/{p}" for p in shared]
    for t in triples:
        paths += [f"{OLEANS_REL}/platform/{t}/{p}" for p in sets[t]]
    blobs = git_blobs(paths)
    for p, h in shared.items():
        if sha256(blobs[f"{OLEANS_REL}/{p}"]) != h:
            raise Refusal(f"{p}: sha256 differs from MANIFEST.toml")
    results = {}
    for t in triples:
        files = {p: blobs[f"{OLEANS_REL}/{p}"] for p in shared}
        for p, h in sets[t].items():
            b = blobs[f"{OLEANS_REL}/platform/{t}/{p}"]
            if sha256(b) != h:
                raise Refusal(f"platform/{t}/{p}: sha256 differs from MANIFEST.toml")
            if p in files:
                raise Refusal(f"{p} is in both the shared and the {t} set")
            files[p] = b
        env = LeanEnv(files)
        inf = Infer(env)
        inds = {n: classify_inductive(env, inf, n) for n, r in env.consts.items() if r["kind"] == "inductive"}
        results[t] = (env, inds, files)
    ref = results[HOST]
    for t, (env, inds, _files) in results.items():
        a = {n: {k: v for k, v in i.items() if k != "module"} for n, i in inds.items()}
        b = {n: {k: v for k, v in i.items() if k != "module"} for n, i in ref[1].items()}
        if a != b:
            raise Refusal(f"the Init census differs between the {t} and {HOST} platform sets")
    manifest_digest = sha256(man_text.encode())
    control = lean_control(ref[0], ref[1], ref[2])
    return ref[0], ref[1], {"triples": triples, "files": len(shared) + len(sets[HOST]),
                            "manifest_sha256": manifest_digest, "lean_control": control}


# ---------------------------------------------------------------------------
# Clean's island prelude, from the D0.5 committed dump
# ---------------------------------------------------------------------------


def clean_object_store(pin):
    common = Path(git("rev-parse", "--path-format=absolute", "--git-common-dir").strip())
    for cand in (REPO / "first-party" / "clean", common.parent / "first-party" / "clean",
                 common / "modules" / "first-party" / "clean"):
        if cand.exists():
            env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
            ok = subprocess.run(["git", "-C", str(cand), "cat-file", "-e", f"{pin}^{{commit}}"],
                                capture_output=True, env=env).returncode == 0
            if ok:
                return cand
    raise Refusal(f"no object store holds clean {pin}")


def prelude_census():
    prov_b = git_blob(f"{REV}:{D05_REL}/provenance.json")
    prov = json.loads(prov_b)
    d05_pin = prov["clean_pin"]
    gitlink = git("ls-tree", REV, "first-party/clean").split()[2]
    store = clean_object_store(gitlink)
    clean_object_store(d05_pin)
    t_now = git("rev-parse", f"{gitlink}:crates", repo=store).strip()
    t_d05 = git("rev-parse", f"{d05_pin}:crates", repo=store).strip()
    if t_now != t_d05:
        raise Refusal(f"first-party/clean's crates/ tree at the gitlink {gitlink[:10]} ({t_now[:10]}) "
                      f"differs from the D0.5 dump's pin {d05_pin[:10]} ({t_d05[:10]}): re-run "
                      "reports/2026-09-17-phase0-d05-one-env-plan/run.sh")
    blobs = git_blobs([f"{D05_REL}/prelude.tsv.gz", f"{D05_REL}/prelude_vs_init.tsv.gz"])
    rows = list(csvrows(gzip.decompress(blobs[f"{D05_REL}/prelude.tsv.gz"]).decode()))
    cmp_rows = {r["name"]: r for r in csvrows(gzip.decompress(blobs[f"{D05_REL}/prelude_vs_init.tsv.gz"]).decode())}
    forms = collections.Counter(r["form"] for r in rows)
    inds = {}
    ctors = collections.defaultdict(list)
    ind_names = {r["name"] for r in rows if r["form"] == "inductive"}
    for r in rows:
        if r["form"] == "constructor":
            owner = r["name"].rsplit(".", 1)[0]
            if owner not in ind_names:
                raise Refusal(f"prelude constructor {r['name']} has no inductive named {owner}")
            ctors[owner].append(r["name"].rsplit(".", 1)[1])
    for r in rows:
        if r["form"] != "inductive":
            continue
        ty = r["type"]
        if "…[truncated]" in ty:
            raise Refusal(f"prelude inductive {r['name']}: truncated type string")
        sort = prelude_sort(ty)
        result = split_arrows(ty)[-1].strip()
        c = cmp_rows.get(r["name"])
        if c is None:
            raise Refusal(f"prelude inductive {r['name']} is missing from prelude_vs_init.tsv")
        inds[r["name"]] = {"name": r["name"], "universe_arity": int(r["universe_arity"]), "sort": sort,
                           "result": result, "ctor_names": sorted(ctors[r["name"]]),
                           "vs_lean48": c["class_lean48"], "vs_lean430": c["class_lean430"],
                           "reason_lean48": c["reason_lean48"]}
    return inds, forms, cmp_rows, {"d05_pin": d05_pin, "gitlink": gitlink, "crates_tree": t_now,
                                   "provenance_sha256": sha256(prov_b),
                                   "prelude_tsv_sha256": sha256(blobs[f"{D05_REL}/prelude.tsv.gz"]),
                                   "prelude_vs_init_sha256": sha256(blobs[f"{D05_REL}/prelude_vs_init.tsv.gz"]),
                                   "d05_superproject_head": prov.get("superproject_head", ""), "_d05_rows": rows}


# ---------------------------------------------------------------------------
# Clean's island prelude, from its kernel declarations (the probe dump)
# ---------------------------------------------------------------------------


def clean_trees(gitlink):
    """The crates/ and data/ trees of first-party/clean at `gitlink`: what the prelude is built from."""
    store = clean_object_store(gitlink)
    return {"crates": git("rev-parse", f"{gitlink}:crates", repo=store).strip(),
            "data": git("rev-parse", f"{gitlink}:data", repo=store).strip()}


def probe_blobs():
    return {f: git("rev-parse", f"{REV}:{PROBE_REL}/{f}").strip() for f in PROBE_FILES}


def prelude_header(gitlink):
    trees = clean_trees(gitlink)
    return json.dumps({"schema": PRELUDE_SCHEMA, "clean_gitlink": gitlink, "clean_crates_tree": trees["crates"],
                       "clean_data_tree": trees["data"], "probe": probe_blobs()}, sort_keys=True)


def _mix(h, x):
    M = (1 << 64) - 1
    for b in (x & M).to_bytes(8, "little"):
        h = ((h ^ b) * 0x100000001B3) & M
    h ^= h >> 33
    h = (h * 0xFF51AFD7ED558CCD) & M
    return h ^ (h >> 33)


def _hash_str(text):
    M, h = (1 << 64) - 1, 0xCBF29CE484222325
    data = text.encode("utf-8")
    for b in data:
        h = ((h ^ b) * 0x100000001B3) & M
    return _mix(h, len(data))


def d05_hash(nodes, root, lparams, with_binder_info):
    """D0.5's structural hash (reports/2026-09-17-phase0-d05-one-env-plan/probe/src/main.rs StructHasher),
    recomputed from the dump's nodes: level parameters positional, binder info only when asked."""
    pos = {n: i for i, n in enumerate(lparams)}

    def level(l):
        t = l[0]
        if t == "0":
            return 0x10
        if t == "+":
            return _mix(0x11, level(l[1]))
        if t in ("max", "imax"):
            return _mix(_mix(0x12 if t == "max" else 0x13, level(l[1])), level(l[2]))
        return _mix(0x14, pos[l[1]]) if l[1] in pos else _mix(0x15, _hash_str(l[1]))

    memo = {}
    for i in _postorder(nodes, root):
        n = nodes[i]
        t = n[0]
        if t == "B":
            v = _mix(0x20, n[1])
        elif t == "F":
            v = _mix(0x21, _hash_str(n[1]))
        elif t == "S":
            v = _mix(0x22, level(n[1]))
        elif t == "C":
            v = _mix(_mix(0x23, _hash_str(n[1])), len(n[2]))
            for l in n[2]:
                v = _mix(v, level(l))
        elif t == "A":
            v = _mix(_mix(0x24, memo[n[1]]), memo[n[2]])
        elif t in ("L", "P"):
            v = _mix(_mix(0x25 if t == "L" else 0x26, memo[n[2]]), memo[n[3]])
            if with_binder_info:
                v = _mix(v, _hash_str(n[1]))
        elif t == "Z":
            v = _mix(_mix(_mix(0x27, memo[n[2]]), memo[n[3]]), memo[n[4]])
        elif t == "N":
            v = _mix(0x28, _hash_str(n[1]))
        elif t == "T":
            v = _mix(0x29, _hash_str(n[1]))
        elif t == "J":
            v = _mix(_mix(_mix(0x2A, _hash_str(n[1])), n[2]), memo[n[3]])
        else:
            v = _mix(0x2F, _hash_str(n[1]))
        memo[i] = v
    return memo[root]


CHILDREN = {"A": (1, 2), "L": (2, 3), "P": (2, 3), "Z": (2, 3, 4), "J": (3,)}


def _postorder(nodes, root):
    """Node ids reachable from root, children first: the probe interns a node after its children, so a
    child's id is always smaller than its parent's and sorting the ids is a post-order."""
    seen, stack = set(), [root]
    while stack:
        i = stack.pop()
        if i in seen:
            continue
        seen.add(i)
        stack.extend(nodes[i][k] for k in CHILDREN.get(nodes[i][0], ()))
    return sorted(seen)


def _level_tuple(l):
    t = l[0]
    if t == "0":
        return ("0",)
    if t == "+":
        return ("+", _level_tuple(l[1]))
    if t in ("max", "imax"):
        return (t, _level_tuple(l[1]), _level_tuple(l[2]))
    return ("p", l[1])


class PreludeEnv:
    """Clean's island prelude from the probe dump, shaped like LeanEnv so classify_inductive and Infer read
    it unchanged. Inductives and constructors use the kernel's own recorded types; Clean's InductiveVal has
    no unsafe flag (the kernel admits no unsafe declaration), so is_unsafe is 0 for every one."""

    def __init__(self, dump):
        self.nodes = dump["exprs"]
        built = []
        for n in self.nodes:
            t = n[0]
            if t == "B":
                e = ("B", n[1])
            elif t == "S":
                e = ("S", _level_tuple(n[1]))
            elif t == "C":
                e = ("C", n[1], tuple(_level_tuple(l) for l in n[2]))
            elif t == "A":
                e = ("A", built[n[1]], built[n[2]])
            elif t in ("L", "P"):
                e = (t, "", built[n[2]], built[n[3]])
            elif t == "Z":
                e = ("Z", n[1], built[n[2]], built[n[3]], built[n[4]])
            elif t == "N":
                e = ("N", int(n[1], 0))
            elif t == "T":
                e = ("T", n[1])
            elif t == "J":
                e = ("J", n[1], n[2], built[n[3]])
            elif t in ("F", "?"):
                e = (t, n[1])
            else:
                raise Refusal(f"prelude dump: unknown node tag {t!r}")
            built.append(e)
        self.built = built
        self.decls = {d["name"]: d for d in dump["decls"]}
        if len(self.decls) != len(dump["decls"]):
            raise Refusal("prelude dump: a name is declared twice")
        self.consts, self.structures, self.classes = {}, set(), set(dump["classes"])
        self.records = collections.Counter()
        for name, d in self.decls.items():
            kind = d["form"]
            self.records[kind] += 1
            rec = {"kind": kind, "lparams": d["lparams"], "module": "prelude", "_type": built[d["type"]],
                   "value": d.get("value")}
            if kind == "inductive":
                rec.update(nparams=d["nparams"], nindices=d["nindices"], all=d["all"], ctors=d["ctors"],
                           is_rec=int(d["is_rec"]), is_unsafe=0, is_reflexive=int(d["is_reflexive"]),
                           is_nested=int(d["is_nested"]))
                rec["_type"] = built[d["inductive_type"]]
                if d["structure"]:
                    self.structures.add(name)
            elif kind == "constructor":
                rec.update(induct=d["induct"], cidx=d["cidx"], nparams=d["nparams"], nfields=d["nfields"])
                rec["_type"] = built[d["constructor_type"]]
            elif kind == "quot":
                if d.get("quot_kind") not in CLEAN_QUOT_KINDS:
                    raise Refusal(f"prelude dump: quotient constant {name} has kind {d.get('quot_kind')!r}")
                rec["quot_kind"] = CLEAN_QUOT_KINDS[d["quot_kind"]]
            self.consts[name] = rec
        for c in self.classes:
            if c not in self.consts:
                raise Refusal(f"prelude dump: class {c} is not a declaration")

    def type_of(self, name):
        return self.consts[name]["_type"]

    def value_of(self, name):
        r = self.consts.get(name)
        if not r or r["kind"] != "definition" or r["value"] is None:
            return None
        return self.built[r["value"]]


def d05_hash_rows(env):
    """name -> (form, universe arity, type hash, type hash with binder info, value hash) as D0.5's
    prelude.tsv prints them, recomputed from the dump."""
    out = {}
    for name, d in env.decls.items():
        hx = lambda root, bi: f"{d05_hash(env.nodes, root, d['lparams'], bi):016x}"  # noqa: E731
        value = hx(d["value"], False) if d.get("value") is not None else "-"
        out[name] = (d["form"], str(len(d["lparams"])), hx(d["type"], False), hx(d["type"], True), value)
    return out


def hash_control(env, d05_rows):
    """Every declaration of the dump must be a row of D0.5's prelude.tsv with the same form, universe arity,
    type hashes and value hash, and every row a declaration: the two probes read one kernel environment.
    The comparison is shown to fail on a perturbed term before its verdict counts."""
    want = {r["name"]: (r["form"], r["universe_arity"], r["type_hash"], r["type_hash_binderinfo"], r["value_hash"])
            for r in d05_rows}

    def compare(have):
        return sorted(set(have) ^ set(want)), sorted(n for n in set(have) & set(want) if have[n] != want[n])

    have = d05_hash_rows(env)
    victim = next(n for n, d in sorted(env.decls.items()) if env.nodes[d["type"]][0] == "P")
    saved = env.nodes[env.decls[victim]["type"]]
    env.nodes[env.decls[victim]["type"]] = ["P", saved[1], saved[3], saved[2]]  # swap domain and body
    try:
        perturbed = d05_hash_rows(env)
    finally:
        env.nodes[env.decls[victim]["type"]] = saved
    if compare(perturbed) == ([], []):
        raise Refusal("prelude hash control: the comparison does not detect a perturbed term")
    names, differ = compare(have)
    if names or differ:
        raise Refusal(f"prelude hash control: {len(names)} names in only one of the dump and D0.5's prelude.tsv "
                      f"({names[:3]}), {len(differ)} declarations differ ({differ[:3]})")
    return {"declarations": len(have), "values": sum(1 for v in have.values() if v[4] != "-")}


# The facts classify_inductive derives from a kernel declaration alone (no environment registry).
KERNEL_FACTS = ("sort", "nparams", "nindices", "nctors", "mutual", "is_rec", "is_nested", "is_reflexive",
                "ctor_names", "field_classes", "poly_rec", "dep_fields", "large_elim_fields")


def prelude_kernel_census(gitlink, prelude, ind48, d05_rows):
    """Classify every prelude inductive into E2.5.6's rows from its kernel declaration."""
    blob = git_blobs([PRELUDE_DECLS_REL])[PRELUDE_DECLS_REL]
    text = gzip.decompress(blob).decode("utf-8")
    header_line, _, body = text.partition("\n")
    header = json.loads(header_line)
    want = json.loads(prelude_header(gitlink))
    for k in ("schema", "clean_crates_tree", "clean_data_tree", "probe"):
        if header.get(k) != want[k]:
            raise Refusal(f"{PRELUDE_DECLS_REL}: its {k} is {header.get(k)!r}, but at {REV[:10]} it is {want[k]!r}: "
                          "re-run `odt.py --probe-prelude --write`")
    env = PreludeEnv(json.loads(body))
    hc = hash_control(env, d05_rows)
    inf = Infer(env)
    kinds = {n: classify_inductive(env, inf, n) for n, r in env.consts.items() if r["kind"] == "inductive"}
    if set(kinds) != set(prelude):
        raise Refusal("prelude kernel census: the dump's inductives are not D0.5's")
    transfer, registry, row_by_registry, sort_diff = 0, {}, [], []
    for n, i in kinds.items():
        p = prelude[n]
        if i["sort"] != p["sort"]:
            sort_diff.append(n)
        if p["decl_identical_lean48"]:
            # The kernel facts of a declaration-identical inductive must be Lean 4.8's, fact for fact.
            differ = [k for k in KERNEL_FACTS if i[k] != ind48[n][k]]
            if differ:
                raise Refusal(f"prelude transfer control: {n} is declaration-identical to Lean 4.8 but its kernel "
                              f"facts {differ} differ between the prelude kernel and Lean 4.8's")
            # Clean's class and structure registries are environment data, not kernel declarations.
            reg = [k for k in ("class", "structure") if i[k] != ind48[n][k]]
            if reg:
                registry[n] = ",".join(f"{k}:clean={int(i[k])},lean48={int(ind48[n][k])}" for k in reg)
            if i["e256"] == ind48[n]["e256"]:
                transfer += 1
            elif reg:
                row_by_registry.append(n)
            else:
                raise Refusal(f"prelude transfer control: {n} has Lean 4.8's kernel facts and registrations but "
                              f"classifies as {i['e256']}, not {ind48[n]['e256']}")
    if sort_diff:
        raise Refusal(f"prelude sort control: the kernel sort differs from D0.5's printed type for {sort_diff[:5]}")
    return kinds, {"header": header, "sha256": sha256(text.encode()), "blob": git("rev-parse", f"{REV}:{PRELUDE_DECLS_REL}").strip(),
                   "hash_control": hc, "transfer": transfer, "registry": registry,
                   "row_by_registry": sorted(row_by_registry), "sorts_agree": len(kinds),
                   "records": dict(sorted(env.records.items())),
                   "quot_type_formers": quot_type_formers(env.consts, PRELUDE_DECLS_REL),
                   "opaque_type_formers": opaque_type_formers(env, inf, PRELUDE_DECLS_REL)}


def probe_prelude(write):
    """Build the probe against a `git archive` export of first-party/clean at REV's gitlink with
    `targo --unverified` (a measurement tool, no proof claim), run it, and compare its output with the
    committed dump (or, with write, publish it). Exit 0 reproduced/written, 1 differs."""
    gitlink = git("ls-tree", REV, "first-party/clean").split()[2]
    store = clean_object_store(gitlink)
    root = Path(os.environ.get("TRUST_CORE_ARTIFACTS") or Path(os.environ.get("XDG_CACHE_HOME") or Path.home() / ".cache")
                / "trust" / "trust-core-artifacts") / "odt-prelude-probe"
    export, build = root / "clean-export", root / "build"
    marker = export / ".odt-export-pin"
    if not marker.is_file() or marker.read_text() != gitlink:
        shutil.rmtree(export, ignore_errors=True)
        export.mkdir(parents=True)
        arc = subprocess.run(["git", "-C", str(store), "archive", gitlink, "Cargo.toml", "Cargo.lock",
                              "rust-toolchain.toml", "lean-toolchain", "crates", "data"], capture_output=True)
        if arc.returncode != 0:
            raise Refusal(f"git archive of clean {gitlink[:10]} failed")
        subprocess.run(["tar", "-x", "-C", str(export)], input=arc.stdout, check=True)
        marker.write_text(gitlink)
    (build / "src").mkdir(parents=True, exist_ok=True)
    files = git_blobs([f"{PROBE_REL}/{f}" for f in PROBE_FILES])
    (build / "Cargo.toml").write_text(files[f"{PROBE_REL}/Cargo.toml.in"].decode().replace("@CLEAN@", str(export)))
    (build / "src" / "main.rs").write_bytes(files[f"{PROBE_REL}/src/main.rs"])
    shutil.copyfile(export / "Cargo.lock", build / "Cargo.lock")
    targo = shutil.which("targo")
    if targo is None or subprocess.run([targo, "--unverified", "--version"], capture_output=True).returncode != 0:
        raise Unavailable("no targo on PATH that accepts --unverified (cargo-in-disguise refuses it)")
    env = dict(os.environ, CARGO_TARGET_DIR=str(root / "target"))
    done = subprocess.run([targo, "--unverified", "build", "--release"], cwd=build, env=env,
                          capture_output=True, text=True)
    if done.returncode != 0:
        raise Refusal(f"building the prelude probe failed: {done.stderr.strip()[-500:]}")
    run = subprocess.run([str(root / "target" / "release" / "odt-prelude-probe")], capture_output=True)
    if run.returncode != 0:
        raise Refusal(f"the prelude probe failed: {run.stderr.decode(errors='replace').strip()[:300]}")
    text = prelude_header(gitlink) + "\n" + run.stdout.decode("utf-8")
    target = REPO / PRELUDE_DECLS_REL
    if write:
        target.write_bytes(gzip.compress(text.encode("utf-8"), compresslevel=9, mtime=0))
        print(f"odt: wrote {PRELUDE_DECLS_REL} (sha256 of the text {sha256(text.encode())})")
        return 0
    committed = gzip.decompress(git_blobs([PRELUDE_DECLS_REL])[PRELUDE_DECLS_REL]).decode("utf-8")
    if committed != text:
        print(f"odt: --probe-prelude: the probe's output differs from the committed {PRELUDE_DECLS_REL}",
              file=sys.stderr)
        return 1
    print(f"odt: --probe-prelude: the probe reproduces {PRELUDE_DECLS_REL} byte for byte "
          f"(sha256 of the text {sha256(text.encode())})")
    return 0


def _level_str(s):
    """Parse a printed universe level (`u`, `3`, `u + 1`, `max(a, b)`, `imax(a, b)`) into the
    tuple form `level_zero` reads."""
    s = s.strip()
    m = re.fullmatch(r"(.*\S)\s*\+\s*(\d+)", s)
    if m and _balanced(m.group(1)):
        base = _level_str(m.group(1))
        return base if m.group(2) == "0" else ("+", base)
    if re.fullmatch(r"\d+", s):
        return ("0",) if s == "0" else ("+", ("0",))
    for op in ("imax", "max"):
        if s.startswith(op + "(") and s.endswith(")"):
            inner, depth = s[len(op) + 1:-1], 0
            for i, ch in enumerate(inner):
                depth += ch == "("
                depth -= ch == ")"
                if ch == "," and depth == 0:
                    return (op, _level_str(inner[:i]), _level_str(inner[i + 1:]))
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", s):
        return ("p", s)
    raise Refusal(f"cannot read the universe level {s!r}")


def _balanced(s):
    depth = 0
    for ch in s:
        depth += ch == "("
        depth -= ch == ")"
        if depth < 0:
            return False
    return depth == 0


def prelude_sort(ty):
    """The sort class of a printed inductive type: its last top-level ` -> ` segment, with a
    fully parenthesized telescope re-split."""
    res = split_arrows(ty)[-1].strip()
    while res.startswith("(") and res.endswith(")") and _balanced(res[1:-1]):
        res = split_arrows(res[1:-1])[-1].strip()
    if res == "Prop":
        return "prop"
    if res == "Type" or re.fullmatch(r"Type \d+", res):
        return "type"
    if res.startswith("Sort "):
        return sort_class(_level_str(res[5:]))
    raise Refusal(f"cannot read the result sort of {ty!r}")


def csvrows(text):
    lines = text.splitlines()
    head = lines[0].split("\t")
    for line in lines[1:]:
        cells = line.split("\t")
        if len(cells) != len(head):
            raise Refusal("malformed TSV row")
        yield dict(zip(head, cells))


def split_arrows(ty):
    parts, depth, cur, i = [], 0, "", 0
    while i < len(ty):
        ch = ty[i]
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        if depth == 0 and ty.startswith(" -> ", i):
            parts.append(cur)
            cur, i = "", i + 4
            continue
        cur += ch
        i += 1
    parts.append(cur)
    return parts


# ---------------------------------------------------------------------------
# Rust: expansion, lexer, item parser
# ---------------------------------------------------------------------------

STD_EXTERNS = ("core", "alloc", "hashbrown", "libc", "std_detect", "unwind", "panic_unwind",
               "panic_abort", "cfg_if", "rustc_demangle", "addr2line", "miniz_oxide", "object")
STD_CFGS = ('feature="backtrace"', 'feature="panic-unwind"', "backtrace_in_libstd")


def atpkg_store():
    if os.environ.get("ATPKG_BIN"):
        return Path(os.environ["ATPKG_BIN"]).parent / "store"
    return Path.home() / "Library/Application Support/aterm/pkg/store"


def trustc_info(exe):
    vv = subprocess.run([exe, "-Vv"], capture_output=True, text=True)
    if vv.returncode != 0 or "trust:" not in vv.stdout:
        return None
    return dict(l.split(": ", 1) for l in vv.stdout.splitlines() if ": " in l)


def library_differs(commit):
    """The library/ files (Cargo.lock aside) whose content differs between `commit` and REV, or None
    when `commit` is not in this repository."""
    run = subprocess.run(["git", "--no-replace-objects", "-C", str(REPO), "cat-file", "-e", f"{commit}^{{commit}}"],
                         capture_output=True, env={k: v for k, v in os.environ.items() if not k.startswith("GIT_")})
    if run.returncode != 0:
        return None
    diff = git("diff", "--name-only", commit, REV, "--", "library").split()
    return [d for d in diff if d != "library/Cargo.lock"]


def toolchain():
    """The first Trust toolchain for HOST whose own commit has REV's library/ tree: --trustc if given,
    else the `trustc` on PATH, else each atpkg store generation (newest first)."""
    if TRUSTC:
        cands = [str(TRUSTC)]
    else:
        store = atpkg_store() / "trust"
        gens = sorted((d for d in store.iterdir() if d.is_dir() and d.name.isdigit()), key=lambda d: -int(d.name)) \
            if store.is_dir() else []
        cands = [c for c in [shutil.which("trustc")] + [str(g / "bin" / "trustc") for g in gens] if c]
    tried = []
    for exe in dict.fromkeys(cands):
        if not Path(exe).is_file():
            continue
        info = trustc_info(exe)
        if info is None:
            tried.append(f"{exe}: `-Vv` does not identify a Trust compiler")
            continue
        commit = info.get("commit-hash", "")
        if info.get("host") != HOST or not re.fullmatch(r"[0-9a-f]{40}", commit):
            tried.append(f"{exe}: host {info.get('host')}, commit-hash {commit or 'none'}")
            continue
        diff = library_differs(commit)
        if diff is None:
            tried.append(f"{exe}: its commit {commit[:10]} is not in this repository")
            continue
        if diff:
            tried.append(f"{exe}: its commit {commit[:10]} has a library/ that differs from {REV[:10]} in "
                         f"{len(diff)} files (first: {diff[0]})")
            continue
        sysroot = subprocess.run([exe, "--print", "sysroot"], capture_output=True, text=True).stdout.strip()
        return exe, info, Path(sysroot)
    raise Unavailable(f"no Trust toolchain for {HOST} was built from a commit whose library/ equals {REV[:10]}'s "
                      f"(tried: {'; '.join(tried) or 'none found'}); install one, or pass --trustc")


def extract_library(dest):
    """library/ at REV, from git objects, into `dest` (the expansion's working directory)."""
    extract_paths(dest, ["library"])


def extract_paths(dest, paths):
    """`paths` at REV, from git objects (`git archive`), into `dest`."""
    env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
    archive = subprocess.run(["git", "--no-replace-objects", "-C", str(REPO), "archive", "--format=tar", REV, *paths],
                             capture_output=True, env=env)
    if archive.returncode != 0:
        raise Refusal(f"git archive {REV} {' '.join(paths)} failed: {archive.stderr.decode(errors='replace').strip()}")
    Path(dest).mkdir(parents=True, exist_ok=True)
    untar = subprocess.run(["tar", "-x", "-f", "-", "-C", str(dest)], input=archive.stdout, capture_output=True)
    if untar.returncode != 0:
        raise Refusal(f"extracting {' '.join(paths)} at {REV} failed: {untar.stderr.decode(errors='replace').strip()}")


def expand(work):
    exe, info, sysroot = toolchain()
    commit = info["commit-hash"]
    src = Path(work) / "src"
    extract_library(src)
    lib = sysroot / "lib" / "rustlib" / HOST / "lib"
    externs, extern_digests = [], {}
    for c in STD_EXTERNS:
        rl = sorted(lib.glob(f"lib{c}-*.rlib"))
        if len(rl) != 1:
            raise Refusal(f"sysroot has {len(rl)} lib{c}-*.rlib, expected 1")
        meta = rl[0].with_suffix(".rmeta")
        if not meta.exists():
            raise Refusal(f"{meta.name} is missing")
        externs += ["--extern", f"{c}={meta}"]
        extern_digests[c] = sha256(meta.read_bytes())
    out = {}
    base = [exe, "--edition", "2024", "--crate-type", "rlib", "-Zforce-unstable-if-unmarked",
            "-Zunpretty=expanded"]
    plan = crate_plan(externs)
    for crate, root, extra, env_add in plan:
        dest = Path(work) / f"{crate}.expanded.rs"
        env = {k: v for k, v in os.environ.items() if not k.startswith(("RUSTFLAGS", "RUSTC_", "CARGO"))}
        env.update(env_add)
        run = subprocess.run(base + ["--crate-name", crate] + extra + [root, "-o", str(dest)],
                             cwd=src, capture_output=True, text=True, env=env)
        errs = [l for l in run.stderr.splitlines() if l.startswith("error")]
        if run.returncode != 0 or errs:
            raise Refusal(f"expanding {crate} failed: {(errs or [run.stderr.strip()[:300]])[0]}")
        data = dest.read_bytes()
        out[crate] = data.decode("utf-8")
        out[crate + "#sha256"] = sha256(data)
    return out, {"trustc": exe, "release": info.get("release", ""), "commit": commit,
                 "trust": info.get("trust", ""), "sysroot_std_rmeta_sha256": extern_digests,
                 "_plan": plan, "_src": src}


def crate_plan(externs):
    """(crate, root, extra flags, extra env) for core, alloc and std, as bootstrap builds them for
    the host: std's build script sets `backtrace_in_libstd` and STD_ENV_ARCH; bootstrap's default
    std features are `backtrace` and `panic-unwind`."""
    return [("core", "library/core/src/lib.rs", [], {}),
            ("alloc", "library/alloc/src/lib.rs", [], {}),
            ("std", "library/std/src/lib.rs",
             [a for c in STD_CFGS for a in ("--cfg", c)] + externs, {"STD_ENV_ARCH": "aarch64"})]


# The targets besides HOST whose core and alloc are expanded without a sysroot for that target (the
# installed toolchain carries only HOST's): the x86-64 and Linux targets the design's later stages need.
OTHER_TARGETS = ("x86_64-apple-darwin", "x86_64-unknown-linux-gnu", "aarch64-unknown-linux-gnu")
CB_ROOT = "library/compiler-builtins/compiler-builtins/src/lib.rs"
# compiler_builtins' Cargo features as alloc's dependency enables them (library/alloc/Cargo.toml:
# features = ["compiler-builtins"], which enables "unmangled-names"; "arch" is its default).
CB_FEATURES = ("compiler-builtins", "unmangled-names", "arch")


def direct_expand(exe, src, work, target):
    """core and alloc of library/ at REV, `-Zunpretty=expanded` for `target` with an EMPTY sysroot: core's
    metadata and compiler_builtins' are built here from the same library/ (`--emit=metadata`, a measurement
    compile: `-Ztrust-verify=off`, no proof claim). alloc names nothing of compiler_builtins (rustc injects
    `extern crate compiler_builtins` into a no_std crate), so its build-script cfgs are not modelled. The
    procedure is controlled on HOST: it must reproduce the sysroot expansion of core and alloc byte for byte.
    Returns {crate: expanded text}."""
    sysroot = Path(work) / "empty-sysroot"
    sysroot.mkdir(exist_ok=True)
    meta = Path(work) / f"meta-{target}"
    meta.mkdir(exist_ok=True)
    env = {k: v for k, v in os.environ.items() if not k.startswith(("RUSTFLAGS", "RUSTC_", "CARGO"))}
    base = [exe, "--edition", "2024", "--crate-type", "rlib", "-Zforce-unstable-if-unmarked", "--sysroot",
            str(sysroot), "--target", target]
    core_meta, cb_meta = meta / "libcore.rmeta", meta / "libcompiler_builtins.rmeta"

    def run(argv, what):
        done = subprocess.run(base + argv, cwd=src, capture_output=True, text=True, env=env)
        errs = [l for l in done.stderr.splitlines() if l.startswith("error")]
        if done.returncode != 0 or errs:
            raise Refusal(f"{what} for {target} failed: {(errs or [done.stderr.strip()[:300]])[0]}")

    run(["--crate-name", "core", "--emit=metadata", "-Ztrust-verify=off", "-o", str(core_meta),
         "library/core/src/lib.rs"], "core's metadata")
    run(["--crate-name", "compiler_builtins", "--emit=metadata", "-Ztrust-verify=off",
         *[a for f in CB_FEATURES for a in ("--cfg", f'feature="{f}"')], "--extern", f"core={core_meta}",
         "-o", str(cb_meta), CB_ROOT], "compiler_builtins' metadata")
    out = {}
    for crate, extra in (("core", []),
                         ("alloc", ["--extern", f"core={core_meta}", "--extern", f"compiler_builtins={cb_meta}"])):
        dest = Path(work) / f"{crate}.{target}.expanded.rs"
        run(["-Zunpretty=expanded", "--crate-name", crate, *extra, f"library/{crate}/src/lib.rs", "-o", str(dest)],
            f"expanding {crate}")
        out[crate] = dest.read_bytes().decode("utf-8")
    return out


# std for a target needs the metadata of its whole dependency graph for that target (libc, hashbrown, cfg-if,
# addr2line, object, ...), built from library/Cargo.lock with each crate's build script. cargo's -Zbuild-std
# builds exactly that graph; it runs here as a measurement tool (`targo --unverified check`, no proof claim)
# over a `git archive` export at REV, with a fresh CARGO_HOME holding only crates.io archives whose sha256 is
# library/Cargo.lock's checksum, and --frozen (the lock is not re-resolved, nothing is fetched).
BUILD_STD_CRATES = "std,panic_unwind"
BUILD_STD_FEATURES = tuple(c[len('feature="'):-1] for c in STD_CFGS if c.startswith('feature="'))
BUILD_STD_TIMEOUT = 1800
# The build-script directives std's build.rs may print that the expansion replays (cfg, env) or that change
# nothing it reads; any other directive refuses the run.
BS_REPLAYED = ("rustc-cfg", "rustc-env")
BS_INERT = ("rerun-if-changed", "rerun-if-env-changed", "rustc-check-cfg")


def library_external_paths():
    """The directories outside library/ that library/'s manifests name with `path =` at REV (path dependencies
    and [patch] entries: cargo loads them to resolve std's graph), as {dir: [manifests naming it]}. Each must be
    a crates/<name> directory (whose manifest inherits from root Cargo.toml); any other refuses."""
    names = [n for n in git("ls-tree", "-r", "--name-only", REV, "library").split("\n")
             if n == "library/Cargo.toml" or n.endswith("/Cargo.toml")]
    out = {}
    for manifest, blob in sorted(git_blobs(names).items()):
        for p in re.findall(r"""^[^#\n]*?\bpath\s*=\s*['"]([^'"]+)['"]""", blob.decode("utf-8"), re.M):
            full = os.path.normpath(os.path.join(os.path.dirname(manifest), p))
            if full == "library" or full.startswith("library/"):
                continue
            if not re.fullmatch(r"crates/[A-Za-z0-9_.-]+", full):
                raise Refusal(f"{manifest} names path {p!r} ({full}), outside library/ and not a crates/ crate: the "
                              "-Zbuild-std export does not know to include it")
            out.setdefault(full, []).append(manifest)
    return out


def lock_packages(text):
    """[(name, version, source, checksum)] of a Cargo.lock (v3/v4), without a TOML library (Python 3.9)."""
    out = []
    for block in text.split("[[package]]")[1:]:
        fields = dict(re.findall(r'^(name|version|source|checksum) = "([^"]*)"$', block, re.M))
        if "name" not in fields or "version" not in fields:
            raise Refusal("library/Cargo.lock: a [[package]] without name and version")
        out.append((fields["name"], fields["version"], fields.get("source", ""), fields.get("checksum", "")))
    return out


def index_path(name):
    """A crate's path in cargo's sparse-index layout (also its registry/index/<dir>/.cache layout)."""
    n = name.lower()
    if len(n) <= 2:
        return f"{len(n)}/{n}"
    if len(n) == 3:
        return f"3/{n[0]}/{n}"
    return f"{n[:2]}/{n[2:4]}/{n}"


def cargo_index_dirs():
    """The host cargo registry's crates.io index caches ($CARGO_HOME, else ~/.cargo): where seed_cargo_home copies
    from. None holds no pinned input; the record cannot be re-measured here (Unavailable)."""
    reg = Path(os.environ.get("CARGO_HOME") or Path.home() / ".cargo") / "registry"
    dirs = sorted(d for d in (reg / "index").glob("index.crates.io-*") if d.is_dir()) if (reg / "index").is_dir() else []
    if not dirs:
        raise Unavailable(f"{reg}/index holds no crates.io index cache, so std's graph (the crates.io packages "
                          "library/Cargo.lock pins) cannot be resolved offline here")
    return reg, dirs


def build_std_targo(exe, commit):
    """The targo beside trustc `exe`, required to be the same build (its `--unverified -Vv` commit is trustc's:
    real targo accepts `--unverified`, cargo under targo's name does not). Returns (path, its -Vv facts)."""
    targo = Path(exe).with_name("targo")
    if not targo.is_file():
        raise Unavailable(f"no targo beside {exe} (the -Zbuild-std run needs the targo of trustc's own build)")
    vv = subprocess.run([str(targo), "--unverified", "-Vv"], capture_output=True, text=True)
    info = dict(l.split(": ", 1) for l in vv.stdout.splitlines() if ": " in l)
    if vv.returncode != 0 or info.get("commit-hash") != commit:
        raise Unavailable(f"{targo} is not the targo of trustc's build {commit[:10]} (it answers `--unverified -Vv` "
                          f"with exit {vv.returncode}, commit {info.get('commit-hash')})")
    return targo, info


def seed_cargo_home(home, lock):
    """A fresh CARGO_HOME for the -Zbuild-std run, from this host's cargo registry: the crates.io index entries of
    every registry package library/Cargo.lock names (cargo resolves the whole locked graph, every target's), and
    each such package's .crate archive the host's cache holds, copied only when its sha256 is the lock's checksum
    (a cached archive with any other digest refuses the run). cargo extracts what it builds from these archives
    into `home`; nothing of the host's extracted registry sources is read. Returns {(name, version): checksum}
    of the registry packages."""
    pkgs = {(n, v): c for n, v, s, c in lock if s.startswith("registry+")}
    if any(not re.fullmatch(r"[0-9a-f]{64}", c) for c in pkgs.values()):
        raise Refusal("library/Cargo.lock: a registry package without a sha256 checksum")
    reg, index_dirs = cargo_index_dirs()
    for d in index_dirs:
        dest = Path(home) / "registry" / "index" / d.name
        dest.mkdir(parents=True, exist_ok=True)
        if (d / "config.json").is_file():
            shutil.copyfile(d / "config.json", dest / "config.json")
        for name, _v in pkgs:
            entry = d / ".cache" / index_path(name)
            if entry.is_file():
                (dest / ".cache" / index_path(name)).parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(entry, dest / ".cache" / index_path(name))
        cache = reg / "cache" / d.name
        (Path(home) / "registry" / "cache" / d.name).mkdir(parents=True, exist_ok=True)
        for (name, version), checksum in pkgs.items():
            crate = cache / f"{name}-{version}.crate"
            if crate.is_file():
                data = crate.read_bytes()
                if sha256(data) != checksum:
                    raise Refusal(f"{crate} has sha256 {sha256(data)}, not library/Cargo.lock's {checksum}")
                (Path(home) / "registry" / "cache" / d.name / crate.name).write_bytes(data)
    return pkgs


def build_script_directives(path):
    """(cfgs, env) std's build script printed (its `output` file), refusing any directive not in BS_REPLAYED
    or BS_INERT."""
    cfgs, env = [], {}
    for line in Path(path).read_text().splitlines():
        m = re.fullmatch(r"cargo::?([a-z-]+)=(.*)", line)
        if not m:
            raise Refusal(f"{path}: {line!r} is not a cargo directive")
        key, val = m.groups()
        if key == "rustc-cfg":
            cfgs.append(val)
        elif key == "rustc-env":
            k, _, v = val.partition("=")
            env[k] = v
        elif key not in BS_INERT:
            raise Refusal(f"{path}: directive {key} is not one the expansion replays or may ignore")
    return cfgs, env


def build_std_expand(tool, work, targets):
    """std of library/ at REV, `-Zunpretty=expanded` for each of `targets`, with the metadata of std's dependency
    graph that cargo's -Zbuild-std builds for that target. The export is library/ and every
    crates/ directory library/'s manifests name (library_external_paths); the run is `targo --unverified check
    --frozen -Z build-std` (targo of trustc's own build, RUSTC = that trustc) against an empty crate, with
    `__CARGO_TESTS_ONLY_SRC_ROOT` naming the export's library/ (cargo's source-root override for -Zbuild-std)
    and the fresh CARGO_HOME of seed_cargo_home. std is then expanded as crate_plan expands it for HOST, but with
    an empty sysroot, `-L dependency=` the target's deps and `--extern` each STD_EXTERNS crate's .rmeta there, and
    the cfgs and env std's build script printed for that target. The caller requires the HOST expansion to equal
    the sysroot expansion byte for byte. Returns ({target: text}, facts)."""
    exe = tool["trustc"]
    targo, targo_info = build_std_targo(exe, tool["commit"])
    work = Path(work)
    src, home, target_dir, crate = work / "src", work / "cargo-home", work / "target", work / "harness"
    ext = library_external_paths()
    exported = ["library"] + sorted(ext)
    extract_paths(src, exported)
    # Use the distribution source normalizer; exporting the full development
    # workspace would require compiler/tool members absent from a std export.
    import runpy
    import tomllib
    source_root = Path(__file__).resolve().parents[3]
    normalizer = runpy.run_path(str(source_root / "scripts/freeze_toolchain_sources.py"))
    writer = runpy.run_path(str(source_root / "src/tools/trust-stage0-dist/prepare.py"))["dump_toml"]
    defaults = tomllib.loads(git_blob(f"{REV}:Cargo.toml").decode())["workspace"]["package"]
    for directory in ext:
        manifest = src / directory / "Cargo.toml"
        manifest.write_text(normalizer["normalize_manifest"](manifest.read_text(), defaults, writer))
    lock_rel = "library/Cargo.lock"
    lock = lock_packages((src / lock_rel).read_text())
    pkgs = seed_cargo_home(home, lock)
    (crate / "src").mkdir(parents=True)
    (crate / "Cargo.toml").write_text('[package]\nname = "odt-build-std"\nversion = "0.0.0"\nedition = "2021"\n'
                                      "publish = false\n\n[workspace]\n")
    (crate / "src" / "lib.rs").write_text("")
    (crate / "Cargo.lock").write_text("# This file is automatically @generated by Cargo.\n# It is not intended for "
                                      'manual editing.\nversion = 4\n\n[[package]]\nname = "odt-build-std"\n'
                                      'version = "0.0.0"\n')
    env = {k: v for k, v in os.environ.items() if not k.startswith(("RUSTFLAGS", "RUSTC", "RUSTDOC", "CARGO", "__CARGO"))}
    env.update(CARGO_HOME=str(home), CARGO_TARGET_DIR=str(target_dir), RUSTC=str(exe),
               __CARGO_TESTS_ONLY_SRC_ROOT=str(src / "library"))
    argv = [str(targo), "--unverified", "check", "--frozen", f"-Zbuild-std={BUILD_STD_CRATES}",
            f"-Zbuild-std-features={','.join(BUILD_STD_FEATURES)}"] + [a for t in targets for a in ("--target", t)]
    try:
        done = subprocess.run(argv, cwd=crate, env=env, capture_output=True, text=True, timeout=BUILD_STD_TIMEOUT)
    except subprocess.TimeoutExpired:
        raise Refusal(f"the -Zbuild-std run did not finish in {BUILD_STD_TIMEOUT} s")
    if done.returncode != 0:
        errs = [l for l in done.stderr.splitlines() if l.startswith("error")] or [done.stderr.strip()[-300:]]
        if re.search(r"attempting to make an HTTP request|failed to download|no matching package|failed to get `",
                     done.stderr):
            raise Unavailable(f"the -Zbuild-std run needs a crates.io package library/Cargo.lock pins that this host's "
                              f"cargo cache does not hold ({errs[0]})")
        raise Refusal(f"the -Zbuild-std run failed: {errs[0]}")
    unpacked = sorted(p.name for p in (home / "registry" / "src").glob("*/*") if p.is_dir())
    extracted = []
    for name, version in sorted(pkgs):
        if f"{name}-{version}" in unpacked:
            extracted.append(f"{name} {version} sha256:{pkgs[(name, version)]}")
    if len(extracted) != len(unpacked):
        raise Refusal(f"cargo extracted registry sources that are not library/Cargo.lock packages: {unpacked}")
    texts, facts = {}, {"targets": {}, "extracted_crates_io": extracted, "exported": exported,
                        "external_paths": {k: v for k, v in sorted(ext.items())},
                        "lock_blob": git("rev-parse", f"{REV}:{lock_rel}").strip(),
                        "export_objects": {p: git("rev-parse", f"{REV}:{p}").strip() for p in exported},
                        "targo": f"targo {targo_info.get('release', '')} commit {targo_info.get('commit-hash')}",
                        "argv": " ".join(["targo"] + argv[1:])}
    sysroot = work / "empty-sysroot"
    sysroot.mkdir(exist_ok=True)
    for t in targets:
        deps = target_dir / t / "debug" / "deps"
        outputs = sorted((target_dir / t / "debug" / "build").glob("std-*/output"))
        if len(outputs) != 1:
            raise Refusal(f"-Zbuild-std left {len(outputs)} std build-script outputs for {t}, expected 1")
        cfgs, bs_env = build_script_directives(outputs[0])
        externs = []
        for c in STD_EXTERNS:
            meta = sorted(deps.glob(f"lib{c}-*.rmeta"))
            if len(meta) != 1:
                raise Refusal(f"-Zbuild-std left {len(meta)} lib{c}-*.rmeta for {t}, expected 1")
            externs += ["--extern", f"{c}={meta[0]}"]
        dest = work / f"std.{t}.expanded.rs"
        run_env = {k: v for k, v in os.environ.items() if not k.startswith(("RUSTFLAGS", "RUSTC_", "CARGO"))}
        run_env.update(bs_env)
        run = subprocess.run([exe, "--edition", "2024", "--crate-type", "rlib", "-Zforce-unstable-if-unmarked",
                              "--sysroot", str(sysroot), "--target", t, "-L", f"dependency={deps}",
                              "-Zunpretty=expanded", "--crate-name", "std"]
                             + [a for c in STD_CFGS if c.startswith("feature=") for a in ("--cfg", c)]
                             + [a for c in cfgs for a in ("--cfg", c)] + externs
                             + ["library/std/src/lib.rs", "-o", str(dest)],
                             cwd=src, capture_output=True, text=True, env=run_env)
        errs = [l for l in run.stderr.splitlines() if l.startswith("error")]
        if run.returncode != 0 or errs:
            raise Refusal(f"expanding std for {t} failed: {(errs or [run.stderr.strip()[:300]])[0]}")
        data = dest.read_bytes()
        texts[t] = data.decode("utf-8")
        facts["targets"][t] = {"cfgs": cfgs, "env": bs_env, "sha256": sha256(data)}
    return texts, facts


def target_censuses(srcs, tool, work):
    """The core, alloc and std census of every OTHER_TARGETS target, after the HOST control of each procedure
    (core and alloc: the empty-sysroot procedure; std: the -Zbuild-std procedure).
    Returns ({target: {crate: [adt]}}, control facts)."""
    from concurrent.futures import ThreadPoolExecutor
    exe, src = tool["trustc"], tool["_src"]
    for t in (HOST,) + OTHER_TARGETS:
        (Path(work) / f"direct-{t}").mkdir(exist_ok=True)
    with ThreadPoolExecutor(max_workers=len(OTHER_TARGETS) + 2) as pool:
        std_job = pool.submit(build_std_expand, tool, Path(work) / "build-std", (HOST,) + OTHER_TARGETS)
        jobs = {t: pool.submit(direct_expand, exe, src, Path(work) / f"direct-{t}", t)
                for t in (HOST,) + OTHER_TARGETS}
        texts = {t: j.result() for t, j in jobs.items()}
        std_texts, std_facts = std_job.result()
    for crate in ("core", "alloc"):
        if texts[HOST][crate] != srcs[crate]:
            raise Refusal(f"the empty-sysroot procedure does not reproduce the {HOST} sysroot expansion of {crate}; "
                          "its per-target counts would not be the same predicate")
    host_plan = next(p for p in tool["_plan"] if p[0] == "std")
    host_cfgs = [a for i, a in enumerate(host_plan[2]) if i and host_plan[2][i - 1] == "--cfg"]
    if (std_facts["targets"][HOST]["cfgs"] != [c for c in host_cfgs if not c.startswith("feature=")]
            or std_facts["targets"][HOST]["env"] != host_plan[3]):
        raise Refusal(f"std's build script under -Zbuild-std gives {HOST} cfgs {std_facts['targets'][HOST]['cfgs']} "
                      f"and env {std_facts['targets'][HOST]['env']}, not the host plan's")
    if std_texts[HOST] != srcs["std"]:
        raise Refusal(f"the -Zbuild-std procedure does not reproduce the {HOST} sysroot expansion of std; its "
                      "per-target counts would not be the same predicate")
    for t in OTHER_TARGETS:
        texts[t]["std"] = std_texts[t]
    out, facts = {}, {"host_reproduced": ["core", "alloc"], "build_std": std_facts}
    for t in OTHER_TARGETS:
        out[t] = {}
        for crate in ("core", "alloc", "std"):
            c = RustCensus(crate, texts[t][crate])
            ctrl = adt_line_control(texts[t][crate])
            if c.parsed_at_line_start != len(c.adts) or ctrl != c.parsed_at_line_start + c.skipped_at_line_start:
                raise Refusal(f"{crate} for {t}: the item parser found {len(c.adts)} ADTs; the line control finds {ctrl}")
            seen = collections.Counter()
            for a in c.adts:
                key = f"{a['crate']}::{a['path']}::{a['name']}" if a["path"] else f"{a['crate']}::{a['name']}"
                seen[key] += 1
                a["key"] = key if seen[key] == 1 else f"{key}#{seen[key]}"
            out[t][crate] = c.adts
            facts[f"{t}.{crate}"] = {"sha256": sha256(texts[t][crate].encode()), "line_control": ctrl,
                                     "skipped_in_macro_bodies": c.skipped_macro_adt_keywords}
    return out, facts


def rustdoc_control(adts, tool):
    """An independent enumeration: `trustdoc --output-format json --document-private-items
    --document-hidden-items` over the same roots and flags lists every module-level ADT by its
    full definition path, as rustc's resolver sees it. Required: every module-level census ADT is
    there at the same path with the same kind, variant count, field count and lifetime / type /
    const parameter counts; every rustdoc ADT the census lacks lies in a module holding no census
    ADT (rustdoc sets cfg(doc), which admits other targets' modules). Local ADTs (in bodies and
    const blocks) are not documented and are not compared."""
    exe = str(Path(tool["trustc"]).with_name("trustdoc"))
    if not Path(exe).is_file():
        raise Refusal(f"{exe} does not exist (the rustdoc control needs the trustdoc beside trustc)")
    ver = subprocess.run([exe, "-Vv"], capture_output=True, text=True).stdout
    if f"commit-hash: {tool['commit']}" not in ver:
        raise Refusal("trustdoc is not the same build as trustc")
    stats = {}
    work = tempfile.mkdtemp(prefix="odt-rustdoc-")
    try:
        for crate, root, extra, env_add in tool["_plan"]:
            env = {k: v for k, v in os.environ.items() if not k.startswith(("RUSTFLAGS", "RUSTC_", "CARGO", "RUSTDOC"))}
            env.update(env_add)
            run = subprocess.run([exe, "--edition", "2024", "--crate-type", "lib", "--crate-name", crate,
                                  "-Zunstable-options", "--output-format", "json", "--document-private-items",
                                  "--document-hidden-items", "-Zforce-unstable-if-unmarked"] + extra
                                 + [root, "-o", work], cwd=tool["_src"], capture_output=True, text=True, env=env)
            if run.returncode != 0 or any(l.startswith("error") for l in run.stderr.splitlines()):
                raise Refusal(f"trustdoc JSON for {crate} failed: {run.stderr.strip()[:300]}")
            doc = json.loads(Path(work, f"{crate}.json").read_bytes())
            rd = {}
            for iid, it in doc["index"].items():
                if it.get("crate_id") != 0:
                    continue
                inner = it["inner"]
                kind = next(iter(inner)) if isinstance(inner, dict) else inner
                if kind not in ("struct", "enum", "union"):
                    continue
                path = doc["paths"].get(iid)
                if path is None:
                    raise Refusal(f"rustdoc {crate}: ADT {it.get('name')} has no path entry")
                v = inner[kind]
                gp = collections.Counter(next(iter(g["kind"])) for g in v["generics"]["params"])
                if kind == "enum":
                    shape = len(v["variants"])
                elif kind == "union":
                    shape = len(v["fields"])
                else:
                    sk = v["kind"]
                    shape = 0 if sk == "unit" else len(sk.get("plain", {}).get("fields", sk.get("tuple", [])))
                rd["::".join(path["path"])] = (kind, shape, gp["lifetime"], gp["type"], gp["const"])
            mine = {}
            for a in adts:
                if a["crate"] == crate and not a["local"]:
                    shape = len(a["variants"]) if a["kind"] == "enum" else len(a["fields"])
                    mine[a["key"]] = (a["kind"], shape, len(a["lifetimes"]), len(a["tparams"]), len(a["cparams"]))
            def diff(mine, rd):
                missing = sorted(set(mine) - set(rd))
                differ = sorted(k for k in set(mine) & set(rd) if mine[k] != rd[k])
                mods = {k.rsplit("::", 1)[0] for k in mine}
                extras = sorted(set(rd) - set(mine))
                return missing, differ, extras, [k for k in extras if k.rsplit("::", 1)[0] in mods]

            missing, differ, extras, bad_extras = diff(mine, rd)
            # the comparison must be able to fail: a census ADT with one variant/field too many, and one
            # census ADT dropped (its rustdoc twin then sits in a module the census covers)
            per_mod = collections.Counter(k.rsplit("::", 1)[0] for k in mine)
            some = sorted(k for k in mine if per_mod[k.rsplit("::", 1)[0]] > 1)[0]
            plus = dict(mine)
            plus[some] = mine[some][:1] + (mine[some][1] + 1,) + mine[some][2:]
            minus = {k: v for k, v in mine.items() if k != some}
            if not diff(plus, rd)[1] or not diff(minus, rd)[3]:
                raise Refusal(f"rustdoc control, {crate}: the comparison does not detect a perturbed census")
            if missing or differ or bad_extras:
                raise Refusal(f"rustdoc control, {crate}: {len(missing)} census ADTs absent from rustdoc "
                              f"({missing[:3]}), {len(differ)} differ in kind/shape/generics "
                              f"({[(k, mine[k], rd[k]) for k in differ[:3]]}), {len(bad_extras)} rustdoc-only "
                              f"ADTs in a module the census covers ({bad_extras[:3]})")
            stats[crate] = {"compared": len(mine), "rustdoc_only_cfg_doc": len(extras),
                            "rustdoc_only_modules": sorted({k.rsplit("::", 1)[0].split("::")[1] if k.count("::") > 1 else "" for k in extras})}
    finally:
        shutil.rmtree(work, ignore_errors=True)
    return stats


_LEX = re.compile(r"""
 (?P<ws>\s+)
|(?P<lc>//[^\n]*)
|(?P<bc>/\*)
|(?P<raw>(?:br|cr|r)\#*")
|(?P<str>(?:b|c)?"(?:[^"\\]|\\.)*")
|(?P<bchar>b'(?:[^'\\\n]|\\[^\n]+?)')
|(?P<rid>r\#[A-Za-z_][A-Za-z0-9_]*)
|(?P<id>[A-Za-z_][A-Za-z0-9_]*)
|(?P<char>'(?:[^'\\\n]|\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F_]+\}|[nrt\\0'"]))')
|(?P<lt>'[A-Za-z_][A-Za-z0-9_]*)
|(?P<num>[0-9][0-9_]*(?:\.[0-9][0-9_]*)?(?:[eE][+-]?[0-9_]+)?[A-Za-z0-9_]*)
|(?P<p>::|->|=>|\.\.=|\.\.\.|\.\.|==|!=|&&|\|\||[-+*/%^!&|=<>@.,;:\#$?~(){}\[\]])
""", re.X | re.S)


def lex(src):
    toks, pos, line, n = [], 0, 1, len(src)
    m = _LEX.match
    while pos < n:
        mm = m(src, pos)
        if mm is None:
            raise Refusal(f"lexer: unexpected {src[pos]!r} at line {line}")
        kind = mm.lastgroup
        end = mm.end()
        if kind == "bc":
            depth, j = 1, end
            while depth:
                a, b = src.find("/*", j), src.find("*/", j)
                if b < 0:
                    raise Refusal("lexer: unterminated block comment")
                if 0 <= a < b:
                    depth, j = depth + 1, a + 2
                else:
                    depth, j = depth - 1, b + 2
            end = j
        elif kind == "raw":
            hashes = mm.group("raw").count("#")
            close = '"' + "#" * hashes
            j = src.find(close, end)
            if j < 0:
                raise Refusal("lexer: unterminated raw string")
            end = j + len(close)
            toks.append(("lit", "\"raw\"", line))
        elif kind in ("str", "bchar", "char", "num"):
            toks.append(("lit", mm.group(kind) if kind in ("num", "str") else kind, line))
        elif kind == "rid":
            toks.append(("id", mm.group(kind)[2:], line))
        elif kind == "id":
            toks.append(("id", mm.group(kind), line))
        elif kind == "lt":
            toks.append(("lt", mm.group(kind), line))
        elif kind == "p":
            toks.append(("p", mm.group(kind), line))
        line += src.count("\n", pos, end)
        pos = end
    return toks


OPEN = {"(": ")", "[": "]", "{": "}"}


def match_groups(toks):
    stack, match = [], [-1] * len(toks)
    for i, (k, t, _l) in enumerate(toks):
        if k != "p":
            continue
        if t in OPEN:
            stack.append(i)
        elif t in (")", "]", "}"):
            if not stack or OPEN[toks[stack[-1]][1]] != t:
                raise Refusal(f"unbalanced {t!r} at line {toks[i][2]}")
            j = stack.pop()
            match[i], match[j] = j, i
    if stack:
        raise Refusal("unbalanced brackets at end of file")
    return match


def split_top(toks, match, a, b, angles, stop_angles_after_eq):
    """Split toks[a:b] at top-level commas; angle depth counted when `angles`."""
    parts, start, depth, i, eq = [], a, 0, a, False
    while i < b:
        k, t, _ = toks[i]
        if k == "p":
            if t in OPEN:
                i = match[i] + 1
                continue
            if t == "=" and depth == 0 and stop_angles_after_eq:
                eq = True
            elif angles and not eq and t == "<":
                depth += 1
            elif angles and not eq and t == ">" and depth > 0:
                depth -= 1
            elif t == "," and depth == 0:
                parts.append((start, i))
                start, eq = i + 1, False
        i += 1
    if start < b:
        parts.append((start, b))
    return parts


def skip_attrs_vis(toks, match, i, b):
    attrs = []
    while i < b:
        if toks[i][1] == "#" and i + 1 < b and toks[i + 1][1] == "[":
            attrs.append((i + 2, match[i + 1]))
            i = match[i + 1] + 1
            continue
        if toks[i] == ("id", "pub", toks[i][2]):
            i += 1
            if i < b and toks[i][1] == "(" and toks[i + 1][1] in ("crate", "self", "super", "in"):
                i = match[i] + 1
            continue
        if toks[i][0] == "id" and toks[i][1] == "unsafe" and i + 1 < b and toks[i + 1][0] == "id" \
                and i + 2 < b and toks[i + 2][1] == ":":
            i += 1
            continue
        break
    return i, attrs


ITEM_PREV = {";", "{", "}", "]"}


class RustCensus:
    def __init__(self, crate, src):
        self.crate = crate
        self.toks = lex(src)
        self.match = match_groups(self.toks)
        self.adts = []
        self.aliases = []
        self.skipped_macro_adt_keywords = 0
        self.skipped_at_line_start = 0
        self.parsed_at_line_start = 0
        self._walk(0, len(self.toks), [], False)

    def _starts_line(self, k):
        """The item beginning at keyword k (or at its `pub` / `pub(..)`) is the first token on its line."""
        t, j = self.toks, k
        if j >= 1 and t[j - 1][1] == ")" and self.match[j - 1] > 0 and t[self.match[j - 1] - 1][1] == "pub":
            j = self.match[j - 1] - 1
        elif j >= 1 and t[j - 1][1] == "pub":
            j -= 1
        return j == 0 or t[j - 1][2] != t[j][2]

    def _item_pos(self, k):
        if k == 0:
            return True
        pk, pt, _ = self.toks[k - 1]
        if pk == "p" and pt in ITEM_PREV:
            return True
        if pk == "id" and pt == "pub":
            return True
        if pk == "p" and pt == ")":
            o = self.match[k - 1]
            return o > 0 and self.toks[o - 1][1] == "pub"
        return False

    def _is_adt(self, k, end):
        t = self.toks
        if t[k][0] != "id" or t[k][1] not in ("struct", "enum", "union"):
            return False
        if k + 2 >= end or t[k + 1][0] != "id" or not self._item_pos(k):
            return False
        nxt = t[k + 2][1]
        return nxt in ("<", "{", "(", ";", "where")

    def _body_start(self, j, end):
        """Index of the `{` that opens the body of the item header starting at j (angle depth 0),
        or of the `;` that ends a body-less item."""
        t, match, angle = self.toks, self.match, 0
        while j < end and not (t[j][0] == "p" and t[j][1] in ("{", ";") and angle == 0):
            if t[j][0] == "p" and t[j][1] in OPEN:
                j = match[j]
            elif t[j][1] == "<":
                angle += 1
            elif t[j][1] == ">" and angle > 0:
                angle -= 1
            j += 1
        return j

    def _walk(self, i, end, path, local, in_impl=False):
        t, match = self.toks, self.match
        while i < end:
            k, v, _ = t[i]
            if k == "id" and v in ("impl", "trait") and self._item_pos_kw(i):
                j = self._body_start(i + 1, end)
                if j < end and t[j][1] == "{":
                    self._walk(j + 1, match[j], path, local, True)
                    i = match[j] + 1
                else:
                    i = j + 1
                continue
            if k == "id" and v == "type" and not in_impl and self._item_pos(i) and i + 2 < end \
                    and t[i + 1][0] == "id":
                i = self._alias(i, end, path, local)
                continue
            if k == "id":
                if v == "macro_rules" and i + 2 < end and t[i + 1][1] == "!":
                    j = i + 3
                    while j < end and not (t[j][0] == "p" and t[j][1] in OPEN):
                        j += 1
                    self._count_skipped(j, match[j])
                    i = match[j] + 1
                    continue
                if v == "macro" and i + 1 < end and t[i + 1][0] == "id" and self._item_pos_macro(i):
                    j = i + 2
                    if t[j][1] == "(":
                        j = match[j] + 1
                    if t[j][1] == "{":
                        self._count_skipped(j, match[j])
                        i = match[j] + 1
                        continue
                if i + 2 < end and t[i + 1][1] == "!" and t[i + 2][0] == "p" and t[i + 2][1] in OPEN:
                    self._count_skipped(i + 2, match[i + 2])
                    i = match[i + 2] + 1
                    continue
                if v == "mod" and i + 2 < end and t[i + 1][0] == "id" and t[i + 2][1] == "{":
                    self._walk(i + 3, match[i + 2], path + [t[i + 1][1]], local, False)
                    i = match[i + 2] + 1
                    continue
                if self._is_adt(i, end):
                    i = self._adt(i, end, path, local)
                    continue
                if v == "fn" and i + 1 < end and t[i + 1][0] == "id":
                    j = self._body_start(i + 2, end)
                    if j < end and t[j][1] == "{":
                        self._walk(j + 1, match[j], path + ["{fn " + t[i + 1][1] + "}"], True)
                        i = match[j] + 1
                        continue
                    i = j + 1
                    continue
            if k == "p" and v == "{":
                # a block that is not a module, impl, trait or fn body: a const/static initializer,
                # a use tree or a foreign block. Items inside a block are local (rustc nests their
                # DefPath under the enclosing anonymous const or body).
                inner = path if local else path + ["{block}"]
                self._walk(i + 1, match[i], inner, True, in_impl)
                i = match[i] + 1
                continue
            i += 1

    def _item_pos_macro(self, i):
        return self._item_pos(i)

    def _item_pos_kw(self, i):
        """`impl`/`trait` at item position, allowing `unsafe`, `auto`, `default`, `const` before it."""
        j = i
        while j > 0 and self.toks[j - 1][0] == "id" and self.toks[j - 1][1] in ("unsafe", "auto", "default", "const"):
            j -= 1
        return self._item_pos(j)

    def _alias(self, k, end, path, local):
        """`type Name<..> (where ..)? = Type;` recorded as an alias node (not an ADT)."""
        t, match = self.toks, self.match
        name, i = t[k + 1][1], k + 2
        tparams, cparams = [], []
        if t[i][1] == "<":
            depth, j = 1, i + 1
            while depth:
                if t[j][0] == "p" and t[j][1] in OPEN:
                    j = match[j] + 1
                    continue
                depth += (t[j][1] == "<") - (t[j][1] == ">")
                j += 1
            for a, b in split_top(t, match, i + 1, j - 1, True, False):
                a, _at = skip_attrs_vis(t, match, a, b)
                if a < b and t[a][0] != "lt":
                    (cparams if t[a][1] == "const" else tparams).append(t[a + 1][1] if t[a][1] == "const" else t[a][1])
            i = j
        j = i
        while j < end and not (t[j][0] == "p" and t[j][1] in ("=", ";")):
            if t[j][0] == "p" and t[j][1] in OPEN:
                j = match[j]
            j += 1
        if j >= end or t[j][1] == ";":
            return j + 1
        e = j + 1
        while e < end and t[e][1] != ";":
            if t[e][0] == "p" and t[e][1] in OPEN:
                e = match[e]
            e += 1
        self.aliases.append({"crate": self.crate, "path": "::".join(path), "name": name, "kind": "alias",
                             "local": local, "tparams": tparams, "cparams": cparams, "lifetimes": [],
                             "fields": [("", [(tk[0], tk[1]) for tk in t[j + 1:e]])], "variants": []})
        return e + 1

    def _count_skipped(self, a, b):
        for j in range(a, b):
            if self._is_adt(j, b):
                self.skipped_macro_adt_keywords += 1
                self.skipped_at_line_start += self._starts_line(j)

    def _adt(self, k, end, path, local):
        t, match = self.toks, self.match
        kind, name, line = t[k][1], t[k + 1][1], t[k][2]
        self.parsed_at_line_start += self._starts_line(k)
        # attributes, collected backwards over the visibility and `#[...]` groups
        attrs, j = [], k - 1
        if j >= 0 and t[j][1] == ")" and self.match[j] > 0 and t[self.match[j] - 1][1] == "pub":
            j = self.match[j] - 2
        elif j >= 0 and t[j][1] == "pub":
            j -= 1
        while j >= 1 and t[j][1] == "]" and t[match[j] - 1][1] == "#":
            attrs.append(" ".join(x[1] for x in t[match[j] + 1:j]))
            j = match[j] - 2
        attrs.reverse()
        i = k + 2
        lifetimes, tparams, cparams = [], [], []
        if t[i][1] == "<":
            depth, j = 1, i + 1
            while depth:
                if t[j][0] == "p" and t[j][1] in OPEN:
                    j = match[j] + 1
                    continue
                if t[j][1] == "<":
                    depth += 1
                elif t[j][1] == ">":
                    depth -= 1
                j += 1
            for a, b in split_top(t, match, i + 1, j - 1, True, False):
                a, _at = skip_attrs_vis(t, match, a, b)
                if a >= b:
                    continue
                if t[a][0] == "lt":
                    lifetimes.append(t[a][1])
                elif t[a][1] == "const":
                    cparams.append(t[a + 1][1])
                else:
                    tparams.append(t[a][1])
            i = j
        fields, variants, shape = [], [], ""

        def skip_where(i):
            depth = 0
            while i < end:
                k2, v2, _ = t[i]
                if k2 == "p":
                    if v2 in ("(", "["):
                        i = match[i] + 1
                        continue
                    if v2 == "{" and depth == 0:
                        return i
                    if v2 == "{":
                        i = match[i] + 1
                        continue
                    if v2 == ";" and depth == 0:
                        return i
                    if v2 == "<":
                        depth += 1
                    elif v2 == ">":
                        depth -= 1
                i += 1
            raise Refusal(f"{self.crate}:{line}: where clause never ends")

        if kind == "struct" and t[i][1] == "(":
            shape = "tuple"
            fields = self._fields(i + 1, match[i], named=False)
            i = match[i] + 1
            if t[i][1] == "where":
                i = skip_where(i + 1)
            if t[i][1] != ";":
                raise Refusal(f"{self.crate}:{line}: tuple struct {name} not closed by ';'")
            i += 1
        else:
            if t[i][1] == "where":
                i = skip_where(i + 1)
            if t[i][1] == ";" and kind == "struct":
                shape = "unit"
                i += 1
            elif t[i][1] == "{":
                if kind == "enum":
                    shape = "enum"
                    variants = self._variants(i + 1, match[i])
                else:
                    shape = "named"
                    fields = self._fields(i + 1, match[i], named=True)
                i = match[i] + 1
            else:
                raise Refusal(f"{self.crate}:{line}: cannot parse {kind} {name}")
        self.adts.append({"crate": self.crate, "path": "::".join(path), "name": name, "kind": kind,
                          "shape": shape, "line": line, "local": local, "attrs": attrs,
                          "lifetimes": lifetimes, "tparams": tparams, "cparams": cparams,
                          "fields": fields, "variants": variants})
        return i

    def _fields(self, a, b, named):
        t, out = self.toks, []
        for x, y in split_top(t, self.match, a, b, True, True):
            x, _attrs = skip_attrs_vis(t, self.match, x, y)
            if x >= y:
                continue
            fname = ""
            if named:
                if t[x][0] != "id" or t[x + 1][1] != ":":
                    raise Refusal(f"{self.crate}:{t[x][2]}: expected `name:` in a field")
                fname, x = t[x][1], x + 2
            ty_end = y
            depth = 0
            for z in range(x, y):
                if t[z][1] == "=" and depth == 0:
                    ty_end = z
                    break
                if t[z][1] in OPEN:
                    depth += 1
                elif t[z][1] in (")", "]", "}"):
                    depth -= 1
                elif t[z][1] == "<":
                    depth += 1
                elif t[z][1] == ">":
                    depth -= 1
            out.append((fname, [(tk[0], tk[1]) for tk in t[x:ty_end]]))
        return out

    def _variants(self, a, b):
        t, out = self.toks, []
        for x, y in split_top(t, self.match, a, b, True, True):
            x, _attrs = skip_attrs_vis(t, self.match, x, y)
            if x >= y:
                continue
            if t[x][0] != "id":
                raise Refusal(f"{self.crate}:{t[x][2]}: expected a variant name")
            vname = t[x][1]
            fields = []
            if x + 1 < y and t[x + 1][1] in ("(", "{"):
                fields = self._fields(x + 2, self.match[x + 1], named=t[x + 1][1] == "{")
            out.append((vname, fields))
        return out


def adt_line_control(src):
    """A second count by other means: lines whose first tokens are `[pub[(..)]] struct|enum|union
    Name` followed by `<`, `{`, `(`, `;`, `where` or the line end (a plain line regex)."""
    rx = re.compile(r"^\s*(?:pub(?:\((?:crate|self|super|in [^)]*)\))?\s+)?(?:struct|enum|union)\s+"
                    r"(?:r#)?[A-Za-z_][A-Za-z0-9_]*\s*(?:<|\{|\(|;|where\b|$)", re.M)
    return len(rx.findall(src))


# --- Rust type-token analysis --------------------------------------------------------------

POINTERS = {"NonNull", "Unique"}
RCS = {"Rc", "Arc", "Weak"}
CONTAINERS = {"Vec", "VecDeque", "LinkedList", "BTreeMap", "BTreeSet", "HashMap", "HashSet",
              "BinaryHeap", "RawVec", "RawTable", "Box"}


def type_occurrences(toks, want):
    """For each ident in `want` inside a field's type tokens: the innermost enclosing
    indirection ("box", "pointer", "rc", "phantom", "container", "fnptr" or "direct"),
    and its path prefix (the idents before it joined by ::)."""
    res = []
    frames = []   # (kind, closer) : kind of the enclosing construct
    prefix = []
    i, n = 0, len(toks)
    while i < n:
        k, v = toks[i]
        if k == "p" and v == "<":
            head = toks[i - 1][1] if i and toks[i - 1][0] == "id" else ""
            frames.append(("angle", head))
        elif k == "p" and v == ">":
            while frames and frames[-1][0] in ("ptr", "ref"):
                frames.pop()
            if frames and frames[-1][0] == "angle":
                frames.pop()
        elif k == "p" and v in ("(", "["):
            head = "fn" if i and toks[i - 1][1] in ("fn", "Fn", "FnMut", "FnOnce") else v
            frames.append(("group", head))
        elif k == "p" and v in (")", "]"):
            while frames and frames[-1][0] in ("ptr", "ref"):
                frames.pop()
            if frames and frames[-1][0] == "group":
                frames.pop()
        elif k == "p" and v == ",":
            while frames and frames[-1][0] in ("ptr", "ref"):
                frames.pop()
        elif k == "p" and v == "*" and i + 1 < n and toks[i + 1][1] in ("const", "mut"):
            frames.append(("ptr", "*"))
        elif k == "p" and v == "&":
            frames.append(("ref", "&"))
        elif k == "p" and v == "->":
            frames.append(("ref", "->"))
        elif k == "id" and v in want and not (i + 1 < n and toks[i + 1][1] == "::"):
            pre = []
            j = i - 1
            while j >= 1 and toks[j][1] == "::" and toks[j - 1][0] == "id":
                pre.insert(0, toks[j - 1][1])
                j -= 2
            if j >= 0 and toks[j][1] == "::":
                pre.insert(0, "<qself>")   # `<T as Trait>::Name` or `::Name`: not a nominal path
            ind = "direct"
            for fk, fh in reversed(frames):
                if fk == "ref" and fh == "->":
                    ind = "fnptr"
                elif fk in ("ptr", "ref") or (fk == "angle" and fh in POINTERS):
                    ind = "pointer"
                elif fk == "angle" and fh == "Box":
                    ind = "box"
                elif fk == "angle" and fh in RCS:
                    ind = "rc"
                elif fk == "angle" and fh == "PhantomData":
                    ind = "phantom"
                elif fk == "angle" and fh in CONTAINERS:
                    ind = "container"
                elif fk == "group" and fh == "fn":
                    ind = "fnptr"
                if ind != "direct":
                    break
            res.append((v, "::".join(pre), ind))
        i += 1
    return res


PRIMS = ("bool", "char", "u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64",
         "i128", "isize", "f16", "f32", "f64", "f128", "str")


def all_field_types(adt):
    for _n, ty in adt["fields"]:
        yield ty
    for _v, fs in adt["variants"]:
        for _n, ty in fs:
            yield ty


def rust_census():
    work = tempfile.mkdtemp(prefix="odt-expand-")
    try:
        return _rust_census(work)
    finally:
        shutil.rmtree(work, ignore_errors=True)


def _rust_census(work):
    srcs, tool = expand(work)
    censuses = {}
    for crate in ("core", "alloc", "std"):
        c = RustCensus(crate, srcs[crate])
        ctrl = adt_line_control(srcs[crate])
        if c.parsed_at_line_start != len(c.adts) or ctrl != c.parsed_at_line_start + c.skipped_at_line_start:
            raise Refusal(f"{crate}: the item parser found {len(c.adts)} ADTs ({c.parsed_at_line_start} "
                          f"starting their line) + {c.skipped_at_line_start} line-starting ADT keywords "
                          f"inside unexpanded macro bodies; the line control finds {ctrl}")
        censuses[crate] = c
        tool[f"{crate}_expanded_sha256"] = srcs[crate + "#sha256"]
        tool[f"{crate}_line_control"] = ctrl
        tool[f"{crate}_skipped_in_macro_bodies"] = c.skipped_macro_adt_keywords
    adts = [a for c in censuses.values() for a in c.adts]
    aliases = [a for c in censuses.values() for a in c.aliases]
    seen = collections.Counter()
    for a in adts:
        key = f"{a['crate']}::{a['path']}::{a['name']}" if a["path"] else f"{a['crate']}::{a['name']}"
        seen[key] += 1
        # two local ADTs of one name in same-named fns of one module (e.g. two `impl Debug` bodies):
        # rustc tells them apart by the impl in the DefPath, this source reader by order.
        a["key"] = key if seen[key] == 1 else f"{key}#{seen[key]}"
    classify_rust(adts, aliases)
    tool["aliases"] = len(aliases)
    tool["rustdoc_control"] = rustdoc_control(adts, tool)
    tool["targets"], tool["target_control"] = target_censuses(srcs, tool, work)
    del tool["_plan"], tool["_src"]
    return adts, tool


def classify_rust(adts, aliases=()):
    by_name = collections.defaultdict(list)
    for a in adts:
        by_name[a["name"]].append(a)
    for a in adts:
        a["generic"] = bool(a["tparams"] or a["cparams"])
        a["lifetime_only"] = bool(a["lifetimes"]) and not a["generic"]
        a["variant_count"] = len(a["variants"])
        a["field_count"] = len(a["fields"]) + sum(len(fs) for _v, fs in a["variants"])
        rec = set()
        mentions = collections.Counter()
        for ty in all_field_types(a):
            ids = {v for k, v in ty if k == "id"}
            for occ, pre, ind in type_occurrences(ty, {a["name"], "Self"}):
                if occ == "Self" and pre == "":
                    rec.add(ind)
                elif occ == a["name"] and (pre == "" or pre == "self"
                                           or pre == "::".join(["crate"] + a["path"].split("::"))):
                    rec.add(ind)
            for p in PRIMS:
                if p in ids:
                    mentions[p] += 1
            if "dyn" in ids:
                mentions["dyn"] += 1
            if "fn" in ids or {"Fn", "FnMut", "FnOnce"} & ids:
                mentions["fn"] += 1
            if any(k == "p" and v == "*" for k, v in ty) or "NonNull" in ids:
                mentions["rawptr"] += 1
            if "UnsafeCell" in ids or "SyncUnsafeCell" in ids:
                mentions["UnsafeCell"] += 1
        rec.discard("phantom")
        if not rec:
            a["recursion"] = "none"
        elif rec == {"box"}:
            a["recursion"] = "box"
        elif rec <= {"pointer"}:
            a["recursion"] = "pointer"
        else:
            a["recursion"] = "+".join(sorted(rec))
        a["mentions"] = dict(mentions)
        a["lang"] = next((m.group(1) for s in a["attrs"] for m in [re.fullmatch(r'lang = "([^"]+)"', s)] if m), "")
        a["repr"] = sorted({r for s in a["attrs"] if s.startswith("repr (") for r in
                            re.findall(r"[A-Za-z_][A-Za-z0-9_]*", s[6:])})
    freeze_analysis(adts, aliases)
    owned_cycles(adts, aliases)


def owned_cycles(adts, aliases):
    """Recursion through other ADTs too: the strongly connected components of the graph whose edge
    A -> B means a field of A (or of an alias) names B, resolved as resolve_path does, and the
    occurrence is owned: by value, in a Box, an Rc/Arc/Weak or a container. Raw pointers,
    references, NonNull/Unique, fn pointers and PhantomData are not edges (C2 reads a raw pointer as
    a `RawPtr τ` leaf). Each ADT on a cycle gets `owned_cycle` = the sorted edge kinds on its cycle."""
    nodes = list(adts) + list(aliases)
    by_crate_name = collections.defaultdict(list)
    for a in nodes:
        by_crate_name[(a["crate"], a["name"])].append(a)
    visible = {"core": ("core",), "alloc": ("core", "alloc"), "std": ("core", "alloc", "std")}
    names = {a["name"] for a in nodes}
    edges = collections.defaultdict(set)
    for a in nodes:
        for ty in all_field_types(a):
            for occ, pre, ind in type_occurrences(ty, names - set(a["tparams"])):
                if ind in ("pointer", "phantom", "fnptr"):
                    continue
                segs = (pre.split("::") if pre else []) + [occ]
                if segs[0] == "<qself>":
                    continue
                target, _c = resolve_path(a, segs, by_crate_name, visible)
                if target is not None:
                    edges[id(a)].add((id(target), ind))
    index, low, stack, on, comps = {}, {}, [], set(), []
    counter = [0]

    def strong(v):   # Tarjan, iterative over an explicit work stack
        work = [(v, iter(sorted(edges.get(v, ()))))]
        index[v] = low[v] = counter[0]
        counter[0] += 1
        stack.append(v)
        on.add(v)
        while work:
            node, it = work[-1]
            advanced = False
            for w, _k in it:
                if w not in index:
                    index[w] = low[w] = counter[0]
                    counter[0] += 1
                    stack.append(w)
                    on.add(w)
                    work.append((w, iter(sorted(edges.get(w, ())))))
                    advanced = True
                    break
                if w in on:
                    low[node] = min(low[node], index[w])
            if advanced:
                continue
            work.pop()
            if work:
                low[work[-1][0]] = min(low[work[-1][0]], low[node])
            if low[node] == index[node]:
                comp = []
                while True:
                    w = stack.pop()
                    on.discard(w)
                    comp.append(w)
                    if w == node:
                        break
                comps.append(comp)

    for a in nodes:
        if id(a) not in index:
            strong(id(a))
    cycle = {}
    for comp in comps:
        members = set(comp)
        kinds = {k for v in comp for w, k in edges.get(v, ()) if w in members}
        if len(comp) > 1 or any(w == comp[0] for w, _k in edges.get(comp[0], ())):
            for v in comp:
                cycle[v] = "+".join(sorted(kinds))
    for a in adts:
        a["owned_cycle"] = cycle.get(id(a), "")


class TypeParseError(Exception):
    pass


def parse_type(toks, i=0):
    """parse_type1, plus a pattern type `T is <pattern>` (core's niche types), read as T."""
    t, i = parse_type1(toks, i)
    if i < len(toks) and toks[i] == ("id", "is"):
        return ("pattern", t), skip_bounds(toks, i + 1)
    return t, i


def parse_type1(toks, i=0):
    """One Rust type from pretty-printed tokens [(kind, text)]; returns (node, next index).
    Nodes: ("path", [segment names], [type args of the last segment]), ("proj",) for a qualified
    `<T as Tr>::X`, ("ref", T), ("ptr", T), ("tuple", [T]), ("array", T), ("fn",), ("dyn",),
    ("never",), ("infer",)."""
    n = len(toks)
    if i >= n:
        raise TypeParseError("empty type")
    k, v = toks[i]
    if v in ("&", "&&"):
        i += 1
        if i < n and toks[i][0] == "lt":
            i += 1
        if i < n and toks[i][1] == "mut":
            i += 1
        inner, i = parse_type(toks, i)
        return ("ref", ("ref", inner) if v == "&&" else inner), i
    if v == "*":
        if i + 1 >= n or toks[i + 1][1] not in ("const", "mut"):
            raise TypeParseError("raw pointer without const/mut")
        inner, i = parse_type(toks, i + 2)
        return ("ptr", inner), i
    if v == "(":
        items, i = [], i + 1
        while toks[i][1] != ")":
            t, i = parse_type(toks, i)
            items.append(t)
            if toks[i][1] == ",":
                i += 1
            elif toks[i][1] != ")":
                raise TypeParseError(f"tuple: unexpected {toks[i][1]!r}")
        return ("tuple", items), i + 1
    if v == "[":
        inner, i = parse_type(toks, i + 1)
        if toks[i][1] == ";":
            depth = 1
            while depth:
                i += 1
                depth += (toks[i][1] in ("(", "[", "{")) - (toks[i][1] in (")", "]", "}"))
        if toks[i][1] != "]":
            raise TypeParseError("array: missing ]")
        return ("array", inner), i + 1
    if v == "!":
        return ("never",), i + 1
    if v == "_":
        return ("infer",), i + 1
    if v in ("fn", "unsafe", "extern", "for") or (k == "id" and v in ("Fn", "FnMut", "FnOnce")
                                                   and i + 1 < n and toks[i + 1][1] == "("):
        return ("fn",), skip_bounds(toks, i)
    if v in ("dyn", "impl"):
        return ("dyn",), skip_bounds(toks, i + 1)
    if v == "<":
        depth, i = 1, i + 1
        while depth:
            depth += (toks[i][1] == "<") - (toks[i][1] == ">")
            i += 1
        while i < n and toks[i][1] == "::" and i + 1 < n and toks[i + 1][0] == "id":
            i += 2
            if i < n and toks[i][1] == "<":
                _args, i = parse_args(toks, i)
        return ("proj",), i
    if v == "::":
        i += 1
    segs, args = [], []
    while True:
        if i >= n or toks[i][0] != "id":
            raise TypeParseError(f"path: expected an identifier, got {toks[i][1] if i < n else 'end'!r}")
        segs.append(toks[i][1])
        i += 1
        args = []
        if i < n and toks[i][1] == "::" and i + 1 < n and toks[i + 1][1] == "<":
            i += 1
        if i < n and toks[i][1] == "<":
            args, i = parse_args(toks, i)
        elif i < n and toks[i][1] == "(" and segs[-1] in ("Fn", "FnMut", "FnOnce"):
            return ("fn",), skip_bounds(toks, i - 1)
        if i < n and toks[i][1] == "::" and i + 1 < n and toks[i + 1][0] == "id":
            i += 1
            continue
        break
    return ("path", segs, args), i


def parse_args(toks, i):
    """`<` args `>` starting at toks[i] == "<"; returns (type args only, index after `>`)."""
    args, i = [], i + 1
    while toks[i][1] != ">":
        k, v = toks[i]
        if k == "lt":
            i += 1
        elif v == "{":
            depth = 1
            while depth:
                i += 1
                depth += (toks[i][1] in ("(", "[", "{")) - (toks[i][1] in (")", "]", "}"))
            i += 1
        elif k == "lit" or (v == "-" and toks[i + 1][0] == "lit"):
            i += 1 if k == "lit" else 2
        elif k == "id" and i + 1 < len(toks) and toks[i + 1][1] == "=" :
            _t, i = parse_type(toks, i + 2)
        elif k == "id" and i + 1 < len(toks) and toks[i + 1][1] == ":":
            i = skip_bounds(toks, i + 2)
        else:
            t, i = parse_type(toks, i)
            args.append(t)
        if toks[i][1] == ",":
            i += 1
        elif toks[i][1] != ">":
            raise TypeParseError(f"generic args: unexpected {toks[i][1]!r}")
    return args, i + 1


def skip_bounds(toks, i):
    """Skip a bound list / fn-pointer type up to a top-level `,` `>` `)` `]` `;` `=` or the end."""
    depth, n = 0, len(toks)
    while i < n:
        v = toks[i][1]
        if v in ("(", "[", "{", "<"):
            depth += 1
        elif v in (")", "]", "}", ">"):
            if depth == 0:
                return i
            depth -= 1
        elif v in (",", ";", "=") and depth == 0:
            return i
        i += 1
    return i


RUST_PRIMS = set(PRIMS) | {"Self"}
ORDER = {"no": 0, "maybe": 1, "yes": 2}


def freeze_analysis(adts, aliases):
    """rustc's `Freeze` question, answered from source: does an ADT contain `UnsafeCell` by value?
    Per node (ADT or type alias): `own` in {no, maybe, yes} and the set of its type parameters it
    holds by value. A path resolved to a node contributes that node's `own`, plus the evaluation of
    each argument in a by-value parameter position; pointers, references, fn pointers, trait objects
    and qualified projections contribute nothing; a type parameter contributes itself. A path this
    reader cannot resolve to one node contributes `maybe` when some visible node of that name is not
    `no` or when an argument is not `no` (a conservative reading, never `yes`)."""
    nodes = list(adts) + list(aliases)
    by_crate_name = collections.defaultdict(list)
    for a in nodes:
        by_crate_name[(a["crate"], a["name"])].append(a)
    seeds = [a for a in adts if a["crate"] == "core" and a["path"] == "cell"
             and a["name"] in ("UnsafeCell", "SyncUnsafeCell") and not a["local"]]
    if len(seeds) != 2:
        raise Refusal("core::cell::{UnsafeCell, SyncUnsafeCell} not found exactly once each")
    parse_failures = []
    for a in nodes:
        trees = []
        for ty in all_field_types(a):
            try:
                tree, j = parse_type(ty, 0)
                if j != len(ty):
                    raise TypeParseError(f"trailing tokens after the type: {ty[j:j + 3]}")
                trees.append(tree)
            except (TypeParseError, IndexError) as e:
                parse_failures.append(f"{a['crate']}::{a['path']}::{a['name']}: {e}")
                trees.append(None)
        a["_trees"] = trees
    if parse_failures:
        raise Refusal(f"{len(parse_failures)} field types did not parse: " + " | ".join(parse_failures[:25]))
    info = {id(a): ["no", frozenset()] for a in nodes}
    for a in seeds:
        info[id(a)][0] = "yes"
    visible = {"core": ("core",), "alloc": ("core", "alloc"), "std": ("core", "alloc", "std")}
    resolved_cache = {}

    def resolve(a, segs):
        key = (id(a), tuple(segs))
        if key not in resolved_cache:
            resolved_cache[key] = resolve_path(a, segs, by_crate_name, visible)
        return resolved_cache[key]

    def ev(tree, a):
        tag = tree[0]
        if tag == "path":
            segs, args = tree[1], tree[2]
            if len(segs) == 1 and segs[0] in a["tparams"]:
                return "no", {segs[0]}
            if segs[0] in a["tparams"] or segs[0] == "Self" or (len(segs) == 1 and segs[0] in RUST_PRIMS):
                return "no", set()
            target, cands = resolve(a, segs)
            if target is not None:
                st, byval = info[id(target)]
                params = set()
                for pos, arg in enumerate(args):
                    if pos < len(target["tparams"]) and target["tparams"][pos] in byval:
                        s2, p2 = ev(arg, a)
                        st = max(st, s2, key=ORDER.get)
                        params |= p2
                return st, params
            st, params = "no", set()
            if any(info[id(c)][0] != "no" for c in cands):
                st = "maybe"
            for arg in args:
                s2, p2 = ev(arg, a)
                if s2 != "no":
                    st = max(st, "maybe", key=ORDER.get)
                params |= p2
            return st, params
        if tag in ("tuple",):
            st, params = "no", set()
            for x in tree[1]:
                s2, p2 = ev(x, a)
                st, params = max(st, s2, key=ORDER.get), params | p2
            return st, params
        if tag in ("array", "pattern"):
            return ev(tree[1], a)
        return "no", set()

    changed = True
    while changed:
        changed = False
        for a in nodes:
            st, params = info[id(a)][0], set(info[id(a)][1])
            for tree in a["_trees"]:
                s2, p2 = ev(tree, a)
                st, params = max(st, s2, key=ORDER.get), params | p2
            params = frozenset(params)
            if st != info[id(a)][0] or params != info[id(a)][1]:
                info[id(a)] = [st, params]
                changed = True
    for a in adts:
        a["interior"] = info[id(a)][0]
        a["interior_mutable"] = a["interior"] == "yes"
        a["byvalue_params"] = sorted(info[id(a)][1])
    for a in nodes:
        del a["_trees"]


# Crates outside the census that std's paths name (its dependencies and their re-exports): a path
# through one of them is an external type, never a census node, whatever a local module is called.
EXTERNAL_CRATES = frozenset(set(STD_EXTERNS) - {"core", "alloc"}) | {"gimli", "adler2", "memchr",
                                                                    "compiler_builtins"}


def resolve_path(a, segs, by_crate_name, visible):
    """(the node `segs` names from inside ADT/alias `a`, or None; the visible same-named candidates).
    Conservative: a qualified path is resolved only by an exact module, a unique node under the named
    module, or a unique node whose module path contains the qualifier; anything else is None."""
    name, parts = segs[-1], segs[:-1]
    if parts and parts[0] in EXTERNAL_CRATES:
        return None, []
    crates = visible[a["crate"]]
    cands = [c for cr in crates for c in by_crate_name[(cr, name)]]
    here = a["path"].split("::") if a["path"] else []
    crate = a["crate"]
    if parts and parts[0] in ("core", "alloc", "std"):
        crate, mod = parts[0], parts[1:]
    elif parts and parts[0] == "crate":
        mod = parts[1:]
    elif parts and parts[0] in ("self", "super"):
        mod = list(here)
        for p in parts:
            if p == "super":
                mod = mod[:-1]
            elif p != "self":
                mod.append(p)
    elif parts:
        mod = None
    else:
        same = [c for c in by_crate_name[(crate, name)] if c["path"] == a["path"]]
        if len(same) == 1:
            return same[0], cands
        in_crate = by_crate_name[(crate, name)]
        if len(in_crate) == 1:
            return in_crate[0], cands
        return (cands[0] if len(cands) == 1 else None), cands
    pool = [c for c in by_crate_name[(crate, name)] if not c["local"]]
    if mod is not None:
        exact = [c for c in pool if c["path"] == "::".join(mod)]
        if len(exact) == 1:
            return exact[0], cands
        under = [c for c in pool if (c["path"] + "::").startswith("::".join(mod) + "::")]
        return (under[0] if len(under) == 1 else None), cands
    inner = [c for c in pool if any(c["path"].split("::")[i:i + len(parts)] == parts
                                    for i in range(len(c["path"].split("::"))))]
    return (inner[0] if len(inner) == 1 else None), cands


# ---------------------------------------------------------------------------
# C7 / C6 pairing
# ---------------------------------------------------------------------------

# Each row: (row id, design spelling that must appear in the C7 bullet, class,
#            Lean names, Rust side: ("adt", crate, path, name) | ("prim", spelling) | ("crate", path, item))
C7_ROWS = (
    ("Option", "`Option`;", "structural", ("Option",), ("adt", "core", "option", "Option")),
    ("Bool", "`Bool`/`bool`", "structural", ("Bool",), ("prim", "bool")),
    ("Unit", "`Unit`/`()`", "structural", ("PUnit",), ("prim", "()")),
    ("Prod", "`Prod`/2-tuple", "structural", ("Prod",), ("prim", "(A, B)")),
    ("Except", "`Except ε α`/`Result<α, ε>`", "structural", ("Except",), ("adt", "core", "result", "Result")),
    ("Ordering", "`Ordering`/`cmp::Ordering`", "structural", ("Ordering",), ("adt", "core", "cmp", "Ordering")),
    ("Empty", "`Empty`/`Infallible`", "structural", ("Empty",), ("adt", "core", "convert", "Infallible")),
    ("UInt8", "`UIntN`/`IntN` with `uN`/`iN`", "structural", ("UInt8",), ("prim", "u8")),
    ("UInt16", "`UIntN`/`IntN` with `uN`/`iN`", "structural", ("UInt16",), ("prim", "u16")),
    ("UInt32", "`UIntN`/`IntN` with `uN`/`iN`", "structural", ("UInt32",), ("prim", "u32")),
    ("UInt64", "`UIntN`/`IntN` with `uN`/`iN`", "structural", ("UInt64",), ("prim", "u64")),
    ("Int8", "`UIntN`/`IntN` with `uN`/`iN`", "structural", ("Int8",), ("prim", "i8")),
    ("Int16", "`UIntN`/`IntN` with `uN`/`iN`", "structural", ("Int16",), ("prim", "i16")),
    ("Int32", "`UIntN`/`IntN` with `uN`/`iN`", "structural", ("Int32",), ("prim", "i32")),
    ("Int64", "`UIntN`/`IntN` with `uN`/`iN`", "structural", ("Int64",), ("prim", "i64")),
    ("Char", "`Char`/`char`", "structural", ("Char",), ("prim", "char")),
    ("Nat", "`Nat`/`trust_bignum::Nat`", "override", ("Nat",), ("crate", BIGNUM_REL, "Nat")),
    ("Int", "`Int`/a new", "override", ("Int",), ("crate", BIGNUM_REL, "Int")),
    ("Array", "`Array`/`Vec`", "override", ("Array",), ("adt", "alloc", "vec", "Vec")),
    ("ByteArray", "`ByteArray`/`Vec<u8>`", "override", ("ByteArray",), ("adt", "alloc", "vec", "Vec")),
    ("String", "`String`/`String`", "override", ("String",), ("adt", "alloc", "string", "String")),
    ("USize", "`USize`/`usize` per target", "override", ("USize",), ("prim", "usize")),
    ("Float", "`Float`/`f64`", "override", ("Float",), ("prim", "f64")),
    ("n-tuples", "n-tuples.", "override", ("Prod",), ("prim", "(A, B, C, ...)")),
)
# C6's own list of override types (design: "such as `Vec`, `String`, `Rc`, `HashMap`, `Cell`
# and `RefCell`").
C6_TYPES = (("alloc", "vec", "Vec"), ("alloc", "string", "String"), ("alloc", "rc", "Rc"),
            ("std", "collections::hash::map", "HashMap"), ("core", "cell", "Cell"),
            ("core", "cell", "RefCell"))
C6_SENTENCE = "such as `Vec`, `String`, `Rc`, `HashMap`, `Cell` and `RefCell`"


# Where the design names what this census measures: (line, exact text on that line, note). Each is
# checked against the design at --rev; a moved line refuses the run instead of publishing a stale cite.
DESIGN_CITES = {
    "census": (4019, "* The ODT census, Clean side and Rust side.",
               "design:4019 (Stage 0.5) names the ODT census; the design gives no number for it"),
    "e251": (4424, "100% of the flat, Box-recursive and generic ADT denominator in",
             "design:4424 E2.5.1 consumes 'the flat, Box-recursive and generic ADT denominator in `core` and "
             "`alloc`' (no number is given)"),
    "k4": (3963, "p2: B1 by `decide` for 20 core ADTs",
           "design:3963 K4 p2's '20 core ADTs' is a purposive probe selection (reports/2026-09-17-phase0-k4-odt.md), "
           "not a census; all 20 are in this census"),
    "e256": (4448, "A table maps every Clean type former in the census to",
             "design:4448 E2.5.6 consumes 'every Clean type former in the census' (no number is given)"),
    "q10": (5074, "recursion or `Type`-valued existentials appear in them? (the ODT census,",
            "design:5073-5075 §8.2 question 10 asks whether finite-image large eliminations, polymorphic "
            "recursion or `Type`-valued existentials appear in real corpora; the clean.lean48 field rows answer "
            "it for Lean 4.8 Init"),
    "v12": (4957, "C7 row count with the by-name growth ban",
            "design:4957 V12 counts C7 rows; design:1351-1358 lists them (no count is written)"),
    "e332": (4575, "100% of ODT entries used by Checkpoint A's std and the",
             "design:4575 E3.3.2 consumes the ODT entries used by Checkpoint A's std (no number is given)"),
}


def design_quotes():
    text = git_blob(f"{REV}:{DESIGN_REL}").decode()
    lines = text.splitlines()
    for key, (ln, quote, _note) in DESIGN_CITES.items():
        if ln > len(lines) or quote not in lines[ln - 1]:
            raise Refusal(f"design:{ln} no longer holds {quote!r} (cite {key}); update DESIGN_CITES")
    start = [i for i, l in enumerate(lines) if l.startswith("* **C7. The identification table**")]
    if len(start) != 1:
        raise Refusal("design: the C7 bullet is not found exactly once")
    s = start[0]
    block = "\n".join(lines[s:s + 9])
    flat = " ".join(block.split())
    for _rid, spelling, _c, _l, _r in C7_ROWS:
        if spelling not in flat:
            raise Refusal(f"design: C7 no longer spells {spelling!r}")
    c6 = [i for i, l in enumerate(lines) if C6_SENTENCE.split(",")[0] in l]
    joined = " ".join(" ".join(" ".join(lines[max(0, i - 1):i + 2]).split()) for i in c6)
    if C6_SENTENCE not in joined:
        raise Refusal("design: C6's list of override types changed")
    return {"c7_line": s + 1, "c7_lines": f"{s + 1}-{s + 9}", "c6_line": c6[0] + 1 if c6 else 0}


def bignum_items():
    src = git_blob(f"{REV}:{BIGNUM_REL}").decode()
    return {m.group(2) for m in re.finditer(r"^pub (struct|enum) ([A-Za-z_][A-Za-z0-9_]*)", src, re.M)}, sha256(src.encode())


# ---------------------------------------------------------------------------
# rows
# ---------------------------------------------------------------------------


def measure():
    # The host-bound inputs first, so a host without them says so at once (exit 3) instead of after the
    # git-only work: a Trust toolchain built from REV's library/ tree and the targo of its build, Lean 4.8.0,
    # and a cargo registry cache to seed the -Zbuild-std run from.
    exe, info, _sysroot = toolchain()
    lean48()
    build_std_targo(exe, info["commit-hash"])
    cargo_index_dirs()
    quotes = design_quotes()
    env48, ind48, meta48 = lean48_census()
    prelude, pforms, _cmp, pmeta = prelude_census()
    adts, tool = rust_census()
    bignum, bignum_sha = bignum_items()
    head = git("rev-parse", "--verify", f"{REV}^{{commit}}").strip()
    rows = []

    def row(name, value, predicate, inputs, status="measured", consumers="", design=()):
        rows.append({"name": name, "value": value, "predicate": predicate, "inputs": inputs,
                     "status": status, "consumers": consumers,
                     "design": [DESIGN_CITES[d][2] for d in design]})

    sets = {
        "head": [f"superproject {head}"],
        "rust": [f"superproject {head}: library/ (git objects; its tree equals trustc's commit "
                 f"{tool['commit'][:10]} except library/Cargo.lock)",
                 f"trustc {tool['release']} commit {tool['commit']} (trust {tool['trust']}): -Zunpretty=expanded "
                 f"for {HOST}; trustdoc of the same build for the rustdoc control"]
                + [f"{c} expanded sha256:{tool[c + '_expanded_sha256']}" for c in ("core", "alloc", "std")]
                + ["std flags: --cfg feature=\"backtrace\" --cfg feature=\"panic-unwind\" --cfg backtrace_in_libstd, "
                   "STD_ENV_ARCH=aarch64, --extern <sysroot .rmeta>: " + ", ".join(
                       f"{c} sha256:{d[:16]}" for c, d in sorted(tool["sysroot_std_rmeta_sha256"].items()))],
        "lean48": [f"superproject {head}: {OLEANS_REL} (Lean 4.8.0; MANIFEST.toml sha256:{meta48['manifest_sha256']}; "
                   f"{meta48['files']} files for {HOST}; census identical for platform sets "
                   f"{', '.join(meta48['triples'])})", f"control: {meta48['lean_control']['lean']}"],
        "prelude": [f"superproject {head}: {D05_REL}/prelude.tsv.gz sha256:{pmeta['prelude_tsv_sha256']}",
                    f"{D05_REL}/prelude_vs_init.tsv.gz sha256:{pmeta['prelude_vs_init_sha256']}",
                    f"{D05_REL}/provenance.json sha256:{pmeta['provenance_sha256']} (dump measured at clean "
                    f"{pmeta['d05_pin']})",
                    f"first-party/clean gitlink {pmeta['gitlink']}: crates/ tree {pmeta['crates_tree']}, identical "
                    f"to the tree at {pmeta['d05_pin']}"],
        "design": [f"superproject {head}: {DESIGN_REL}:{quotes['c7_lines']} (C7 rows, quote-checked) and "
                   f":{quotes['c6_line']} (C6's override list)"],
        "bignum": [f"superproject {head}: {BIGNUM_REL} sha256:{bignum_sha}"],
    }
    tc = tool["target_control"]
    sets["targets"] = ([f"superproject {head}: library/ (git objects), expanded by trustc commit {tool['commit']} with an "
                        "empty sysroot: core's and compiler_builtins' metadata built from the same library/"]
                       + [f"{t} {c} expanded sha256:{tc[t + '.' + c]['sha256']}" for t in OTHER_TARGETS
                          for c in ("core", "alloc")])
    bs = tc["build_std"]
    sets["build_std"] = (
        [f"superproject {head}: {p} {'tree' if not p.endswith('.toml') else 'blob'} {oid} (git objects, exported with "
         "`git archive`)" for p, oid in bs["export_objects"].items()]
        + [f"superproject {head}: library/Cargo.lock blob {bs['lock_blob']} (the std graph's versions and crates.io "
           "checksums; --frozen)",
           f"{bs['targo']} (trustc {tool['commit']} as RUSTC): `{bs['argv']}`, CARGO_HOME fresh, "
           "__CARGO_TESTS_ONLY_SRC_ROOT = the export's library/",
           "library/'s manifests name outside library/: " + "; ".join(
               f"{d} (by {', '.join(m)})" for d, m in bs["external_paths"].items())]
        + [f"crates.io package cargo extracted for the run: {c} (library/Cargo.lock's checksum; the .crate "
           "archive's sha256 is checked against it before cargo sees it)" for c in bs["extracted_crates_io"]]
        + [f"{t} std: build-script cfgs {', '.join(f['cfgs']) or 'none'}, env "
           f"{', '.join(k + '=' + v for k, v in sorted(f['env'].items())) or 'none'}; expanded sha256:{f['sha256']}"
           for t, f in bs["targets"].items()])
    rust_in, lean_in, prel_in, design_in = ["rust"], ["lean48"], ["prelude"], ["design"]

    # ---- Rust side --------------------------------------------------------------------
    rust_pred = ("every `struct`, `enum` and `union` item (module-level, or local inside a fn body or block) "
                 "in the `-Zunpretty=expanded` output of the crate for aarch64-apple-darwin, found by this "
                 "script's Rust lexer and item parser; items inside unexpanded macro bodies (`macro_rules!`, "
                 "`macro`, and builtin invocations) are not items. Control: a line regex counting "
                 "`[pub[(..)]] struct|enum|union Name` lines must equal parsed items plus the ADT keywords "
                 "the parser skipped inside macro bodies; and trustdoc's JSON of the same crate must list every "
                 "module-level ADT at the same definition path with the same kind, variant/field count and "
                 "generic parameter counts ([controls])")
    for crate in ("core", "alloc", "std"):
        cs = [a for a in adts if a["crate"] == crate]
        kinds = collections.Counter(a["kind"] for a in cs)
        row(f"rust.{crate}.adts", len(cs), rust_pred, rust_in,
            consumers="E2.5.1 (core, alloc); E3.3.2 (std)",
            design=("census", "e251", "k4") if crate == "core" else ("census", "e251") if crate == "alloc"
            else ("census", "e332"))
        row(f"rust.{crate}.structs", kinds["struct"], "rust.%s.adts restricted to `struct`" % crate, rust_in)
        row(f"rust.{crate}.enums", kinds["enum"], "rust.%s.adts restricted to `enum`" % crate, rust_in)
        row(f"rust.{crate}.unions", kinds["union"], "rust.%s.adts restricted to `union` (C2: bytes plus "
            "per-field partial decoders)" % crate, rust_in)
        row(f"rust.{crate}.enum_variants", sum(a["variant_count"] for a in cs),
            "sum over rust.%s.adts enums of their variants" % crate, rust_in)
        row(f"rust.{crate}.local_adts", sum(a["local"] for a in cs),
            "rust.%s.adts defined inside a fn body or block (not at module level)" % crate, rust_in)
        row(f"rust.{crate}.generic", sum(a["generic"] for a in cs),
            "rust.%s.adts with at least one type or const parameter" % crate, rust_in, consumers="E2.5.1")
    cora = [a for a in adts if a["crate"] in ("core", "alloc")]

    def adt_at(crate, path, name):
        m = [a for a in adts if a["crate"] == crate and a["path"] == path and a["name"] == name and not a["local"]]
        if len(m) != 1:
            raise Refusal(f"{crate}::{path}::{name} found {len(m)} times in the expansion")
        return m[0]

    c7_rust = {}
    for rid, _sp, cls, _ln, rs in C7_ROWS:
        if rs[0] == "adt":
            c7_rust[rid] = adt_at(*rs[1:])
    c6_rust = [adt_at(*t) for t in C6_TYPES]
    pair_ids = {id(a) for a in c7_rust.values()}
    override_ids = {id(a) for a in c6_rust} | {id(c7_rust[r]) for r in ("Array", "ByteArray", "String")}
    structural_ids = {id(c7_rust[r]) for r in ("Option", "Except", "Ordering", "Empty")}

    def e251_class(a):
        if a["kind"] == "union":
            return "union"
        if id(a) in structural_ids:
            return "c7-structural"
        if id(a) in override_ids:
            return "c6-override"
        if a["interior"] == "yes":
            return "interior-mutable"
        if a["interior"] == "maybe":
            return "interior-undetermined"
        return "generated-view"

    for a in adts:
        a["e251"] = e251_class(a)
    e251_pred = ("core ∪ alloc ADTs (rust.core.adts + rust.alloc.adts), each placed in the first class it meets: "
                 "`union` (C2: bytes, no value inductive); a C7 structural row's Rust side (Option, Result, "
                 "cmp::Ordering, Infallible: the logical view is the Lean inductive); a C6 override (C6's list "
                 "Vec, String, Rc, HashMap, Cell, RefCell, plus C7's override rows' Rust sides); "
                 "`interior-mutable` (contains `core::cell::UnsafeCell`/`SyncUnsafeCell` by value, rustc's "
                 "`Freeze` question, answered structurally: a field's type contributes a named ADT or type alias "
                 "that contains it by value, and a generic one contributes its arguments only in the parameter "
                 "positions it itself holds by value; raw pointers, references, fn pointers, trait objects and "
                 "associated-type projections contribute nothing, so Box, Vec, Rc, NonNull and PhantomData "
                 "contribute nothing either, since they hold T behind a pointer or not at all: C2 gives these "
                 "types a resource, not a value inductive); `interior-undetermined` (not proven so, but a field "
                 "names a type this source reader cannot resolve to one ADT or alias, and some visible candidate "
                 "of that name, or one of its arguments, is not known Freeze); else `generated-view` (C2 "
                 "generates its logical view). Name resolution: `crate::`/`self::`/`super::`/`core::`/`alloc::` "
                 "paths by module (exact, then a unique ADT under that module), other qualified paths by a "
                 "unique module-suffix match, unqualified names in the same module, then unique in the crate, "
                 "then unique in the census")
    e251 = collections.Counter(a["e251"] for a in cora)
    for n, cls in enumerate(("generated-view", "interior-mutable", "interior-undetermined", "c6-override",
                             "c7-structural", "union")):
        pred = (e251_pred if n == 0 else "the partition defined by row rust.core_alloc.e2_5_1.generated-view's "
                "predicate") + f"; this row counts class `{cls}`"
        row(f"rust.core_alloc.e2_5_1.{cls}", e251[cls], pred, rust_in, consumers="E2.5.1",
            design=("e251",) if n == 0 else ())
    gv = [a for a in cora if a["e251"] == "generated-view"]
    rec = collections.Counter(a["recursion"] for a in gv)
    row("rust.core_alloc.generated_view.flat", sum(1 for a in gv if not a["generic"] and a["recursion"] == "none"),
        "rust.core_alloc.e2_5_1.generated-view ADTs with no type/const parameter and no self-reference in a "
        "field (a field type naming the ADT itself, unqualified, via `Self`, `self::` or its `crate::` path; "
        "PhantomData mentions ignored)", rust_in, consumers="E2.5.1 (the design's 'flat')")
    row("rust.core_alloc.generated_view.nongeneric_self_reference",
        sum(1 for a in gv if not a["generic"] and a["recursion"] != "none"),
        "rust.core_alloc.e2_5_1.generated-view ADTs with no type/const parameter and a self-reference; with "
        "the flat and generic rows it partitions the generated-view class", rust_in, consumers="E2.5.1")
    row("rust.core_alloc.generated_view.generic", sum(1 for a in gv if a["generic"]),
        "rust.core_alloc.e2_5_1.generated-view ADTs with at least one type or const parameter",
        rust_in, consumers="E2.5.1 (the design's 'generic')")
    row("rust.core_alloc.generated_view.box_recursive", rec["box"],
        "rust.core_alloc.e2_5_1.generated-view ADTs every one of whose self-references sits inside a `Box<..>` "
        "(the innermost indirection around the occurrence)", rust_in,
        consumers="E2.5.1 (the design's 'Box-recursive')")
    row("rust.core_alloc.generated_view.pointer_self_reference", rec["pointer"],
        "rust.core_alloc.e2_5_1.generated-view ADTs whose self-references all sit behind a raw pointer, "
        "`NonNull`/`Unique` or a reference (C2: `RawPtr τ`, not a recursive position)", rust_in,
        consumers="E2.5.1")
    other_rec = sum(v for k, v in rec.items() if k not in ("none", "box", "pointer"))
    row("rust.core_alloc.generated_view.other_self_reference", other_rec,
        "rust.core_alloc.e2_5_1.generated-view ADTs with a self-reference that is neither only-Box nor "
        "only-pointer (direct, Rc/Arc, a container, a fn pointer, or a mix)", rust_in, consumers="E2.5.1")
    row("rust.core_alloc.generated_view.owned_cycle_members", sum(1 for a in gv if a["owned_cycle"]),
        "rust.core_alloc.e2_5_1.generated-view ADTs on a cycle of owned references, mutual recursion included: "
        "a strongly connected component (or self-loop) of the graph whose edge A -> B means a field of A (or of "
        "a type alias) names B by value, in a Box, an Rc/Arc/Weak or a container; raw pointers, references, "
        "NonNull/Unique, fn pointers and PhantomData are not edges", rust_in, consumers="E2.5.1")
    row("rust.core_alloc.generated_view.box_cycle_members",
        sum(1 for a in gv if "box" in a["owned_cycle"].split("+")),
        "rust.core_alloc.generated_view.owned_cycle_members whose cycle has a Box edge (Box-recursive, "
        "mutual recursion included)", rust_in, consumers="E2.5.1 (the design's 'Box-recursive')")
    row("rust.std.owned_cycle_members", sum(1 for a in adts if a["crate"] == "std" and a["owned_cycle"]),
        "rust.std.adts on a cycle of owned references (the owned_cycle_members predicate applied to std)",
        rust_in, consumers="E3.3.2")
    row("rust.core_alloc.generated_view.dyn_or_fn_field",
        sum(1 for a in gv if a["mentions"].get("dyn") or a["mentions"].get("fn")),
        "rust.core_alloc.e2_5_1.generated-view ADTs with a field type mentioning `dyn` or a fn-pointer / "
        "`Fn*` type (C2's list names no rule for either)", rust_in, consumers="E2.5.1; D-2 C2")
    for p in ("u128", "i128", "isize", "f16", "f32", "f128", "str"):
        row(f"rust.core_alloc.generated_view.field_mentions_{p}",
            sum(1 for a in gv if a["mentions"].get(p)),
            f"rust.core_alloc.e2_5_1.generated-view ADTs with a field type mentioning the primitive `{p}` "
            "(no C7 row names it)", rust_in, consumers="D-2 C2/C7 scalar sub-table")
    for st, label in (("yes", "interior_mutable"), ("maybe", "interior_undetermined")):
        row(f"rust.std.{label}", sum(1 for a in adts if a["crate"] == "std" and a["interior"] == st),
            f"rust.std.adts in the E2.5.1 predicate's `{label.replace('_', '-')}` class (the same "
            "three-valued UnsafeCell closure, applied to std)", rust_in, consumers="E3.3.2")

    # ---- Clean side: Lean 4.8 Init ------------------------------------------------------
    inds = list(ind48.values())
    lean_pred = ("every `inductInfo` constant of the Lean 4.8 Init closure vendored at "
                 f"{OLEANS_REL} ({meta48['files']} .olean files), read by this script's olean reader "
                 "(Lean 4.8 layouts), checked every run against Lean 4.8.0's own reader and MetaM "
                 "([controls].lean_reader)")
    row("clean.lean48.inductives", len(inds), lean_pred, lean_in, consumers="E2.5.6; C7 rows",
        design=("census", "e256", "q10"))
    row("clean.lean48.constructors", sum(i["nctors"] for i in inds), "constructors of clean.lean48.inductives", lean_in)
    row("clean.lean48.structures", sum(i["structure"] for i in inds),
        "clean.lean48.inductives registered in `Lean.structureExt` (structure-declared classes included)", lean_in)
    row("clean.lean48.classes", sum(i["class"] for i in inds),
        "clean.lean48.inductives registered in `Lean.classExtension` (the ODT key covers classes: D-2)", lean_in)
    for s in ("prop", "type", "sort-poly"):
        row(f"clean.lean48.sort_{s.replace('-', '_')}", sum(1 for i in inds if i["sort"] == s),
            f"clean.lean48.inductives whose type, after its parameters and indices, is "
            + {"prop": "`Prop` (erased under C5)", "type": "`Sort (l+1)` for some l (data)",
               "sort-poly": "`Sort u` with u a universe parameter (Prop or data by instance)"}[s], lean_in)
    row("clean.lean48.indexed_type_families", sum(1 for i in inds if i["nindices"] and i["sort"] != "prop"),
        "clean.lean48.inductives with numIndices > 0 not sorted in Prop (the design's indexed family, ODT M7)",
        lean_in, consumers="E2.5.6; OD-9")
    row("clean.lean48.recursive", sum(1 for i in inds if i["is_rec"] and i["sort"] != "prop"),
        "non-Prop clean.lean48.inductives with isRec", lean_in, consumers="ODT M5")
    row("clean.lean48.mutual_or_nested", sum(1 for i in inds if (i["mutual"] > 1 or i["is_nested"]) and i["sort"] != "prop"),
        "non-Prop clean.lean48.inductives in a mutual block (|all| > 1) or with isNested", lean_in)
    row("clean.lean48.polymorphic_recursion", sum(1 for i in inds if i["poly_rec"]),
        "clean.lean48.inductives with a constructor field in which a member of its mutual block is applied to "
        "parameters other than the constructor's own parameter variables", lean_in,
        consumers="§8.2 question 10; E2.5.6 (refused row)")
    row("clean.lean48.type_valued_fields_nonclass", sum(1 for i in inds if i["type_fields"] and not i["class"] and i["sort"] != "prop"),
        "non-Prop, non-class clean.lean48.inductives with a constructor field whose type is `Sort l` with l "
        "not surely 0, or a telescope ending in one (a field that is a type or a type family: a `Type`-valued "
        "existential)", lean_in, consumers="§8.2 question 10; E2.5.6 (refused row)")
    row("clean.lean48.type_valued_fields_class", sum(1 for i in inds if i["type_fields"] and i["class"]),
        "clean.lean48 classes with a field that is a type or type family (an associated type under C3)",
        lean_in, consumers="§8.2 question 10")
    row("clean.lean48.prop_valued_family_fields", sum(i["prop_family_fields"] for i in inds if i["sort"] != "prop"),
        "constructor fields (non-Prop inductives) whose type is `Prop` or a telescope ending in `Prop` (a "
        "proposition, predicate or relation held as a field; erased with types under C5)", lean_in)
    row("clean.lean48.large_elim_fields", sum(len(i["large_elim_fields"]) for i in inds if i["sort"] != "prop"),
        "constructor fields (non-Prop inductives) that are data and whose type is a *definition* applied to "
        "an earlier data field (a type computed by large elimination; finite vs infinite image is not decided "
        "by this predicate)", lean_in, consumers="§8.2 question 10; E2.5.6")
    row("clean.lean48.dependent_data_fields", sum(len(i["dep_fields"]) for i in inds if i["sort"] != "prop"),
        "constructor fields (non-Prop inductives) that are data and whose type mentions an earlier data field",
        lean_in, consumers="E2.5.6 (ODT M7)")
    row("clean.lean48.unclassified_fields", sum(i["unclassified_fields"] for i in inds),
        "constructor fields whose sort this script's inferencer could not determine (must be 0 for the field "
        "rows above to be complete)", lean_in)
    quot_pred = ("quotient constants (`quotInfo`) of the environment whose kernel QuotKind is `type`: the quotient "
                 "type former `Quot` (its `mk`, `lift` and `ind` are a constructor, an eliminator and an induction "
                 "principle, not type formers); each quotient kind must carry the kernel's name for it, or nothing "
                 "is published. E2.5.6 names `Quot` as a fixture, and the design's Quotient row maps it")
    q48 = quot_type_formers(env48.consts, OLEANS_REL)
    row("clean.lean48.quot_type_formers", len(q48), quot_pred + ". Read from the Lean 4.8 oleans (QuotVal.kind)",
        lean_in, consumers="E2.5.6 (the `Quot` fixture)")
    ax_pred = ("`axiom` and `opaque` constants whose type, after its Pi telescope (read through whnf), ends in a "
               "sort other than `Prop` (`Sort (l+1)` or `Sort u`): type formers declared without an unfoldable "
               "definition, which no inductive row counts (E2.5.6 must map or refuse each). Type-valued "
               "DEFINITIONS are not type formers here: each unfolds to a term built from the counted formers")
    ax48, ax48_un = opaque_type_formers(env48, Infer(env48), OLEANS_REL)
    row("clean.lean48.opaque_type_formers", len(ax48), ax_pred + ". Read from the Lean 4.8 oleans: "
        + ", ".join(n for n, _c in ax48), lean_in, consumers="E2.5.6")
    row("clean.lean48.opaque_type_formers_unclassified", len(ax48_un), "axiom and opaque constants of the Lean 4.8 "
        "Init closure whose type's end the reader could not reach (must be 0 for clean.lean48.opaque_type_formers "
        "to be complete)", lean_in)
    row("clean.lean48.type_formers", len(inds) + len(q48) + len(ax48),
        "clean.lean48.inductives + clean.lean48.quot_type_formers + clean.lean48.opaque_type_formers: every type "
        "former of the Lean 4.8 Init closure (E2.5.6's 'every Clean type former in the census'; the "
        "clean.lean48.e2_5_6.* rows partition the inductives, and `Quot` and the axiom/opaque formers are their "
        "own rows)", lean_in, consumers="E2.5.6", design=("e256",))
    cats = collections.Counter(i["e256"] for i in inds)
    for n, (cat, desc) in enumerate(E256):
        head_pred = ("clean.lean48.inductives, each placed in the first rule it meets, in order: "
                     + "; ".join(f"`{c}`: {d}" for c, d in E256)) if n == 0 else (
            "the partition defined by row clean.lean48.e2_5_6.prop's predicate")
        row(f"clean.lean48.e2_5_6.{cat}", cats[cat], head_pred + f". This row counts `{cat}`", lean_in,
            consumers="E2.5.6")

    # ---- Clean side: island prelude -----------------------------------------------------
    pl = list(prelude.values())
    prel_pred = ("every row with form `inductive` in D0.5's dump of `Environment::with_prelude()` "
                 "(the island prelude, 2,061 constants), admitted because the clean gitlink's crates/ tree equals "
                 "the dumped pin's")
    row("clean.prelude.inductives", len(pl), prel_pred, prel_in, consumers="C7 rows (islands' environment today)",
        design=("census",))
    row("clean.prelude.constructors", pforms["constructor"], "rows with form `constructor` in the same dump", prel_in)
    decl_ident = []
    for p in pl:
        ind = ind48.get(p["name"])
        ok = p["vs_lean48"] == "identical" and ind is not None and all(
            _cmp.get(f"{p['name']}.{c}", {}).get("class_lean48") == "identical" for c in ind["ctor_names"])
        p["decl_identical_lean48"] = ok
        if ok:
            decl_ident.append(p)
    kinds, kmeta = prelude_kernel_census(pmeta["gitlink"], prelude, ind48, pmeta.pop("_d05_rows"))
    for p in pl:
        p["kernel"] = kinds[p["name"]]
        p["e256"] = kinds[p["name"]]["e256"]
    pk = [p["kernel"] for p in pl]
    kh = kmeta["header"]
    sets["prelude_decls"] = [
        f"superproject {head}: {PRELUDE_DECLS_REL} blob {kmeta['blob']}, sha256 of the text {kmeta['sha256']}",
        f"its header: clean gitlink {kh['clean_gitlink']}, crates/ tree {kh['clean_crates_tree']}, data/ tree "
        f"{kh['clean_data_tree']} (equal to the trees at the measured gitlink {pmeta['gitlink']})",
        "produced by " + ", ".join(f"{PROBE_REL}/{f} blob {b}" for f, b in sorted(kh["probe"].items()))
        + " (odt.py --probe-prelude rebuilds it and must reproduce the text byte for byte)"]
    kern_in = ["prelude_decls"]
    row("clean.prelude.identical_to_lean48", len(decl_ident),
        "clean.prelude.inductives whose D0.5 class vs Lean 4.8 is `identical` (type, universe arity and shape: "
        "parameters, indices, constructors in order, rec, nested) AND each of whose constructors is `identical`; "
        "their E2.5.6 row is the Lean 4.8 one", prel_in + lean_in)
    for cls in ("differs", "absent"):
        row(f"clean.prelude.{cls}_vs_lean48", sum(1 for p in pl if p["vs_lean48"] == cls),
            f"clean.prelude.inductives whose D0.5 class vs Lean 4.8 is `{cls}`", prel_in)
    row("clean.prelude.ctor_differs_vs_lean48",
        sum(1 for p in pl if p["vs_lean48"] == "identical" and not p["decl_identical_lean48"]),
        "clean.prelude.inductives `identical` vs Lean 4.8 as a type but with a constructor that is not", prel_in)
    row("clean.prelude.not_decl_identical_lean48", sum(1 for p in pl if not p["decl_identical_lean48"]),
        "clean.prelude.inductives not in clean.prelude.identical_to_lean48 (their E2.5.6 row cannot be "
        "transferred from Lean 4.8; clean.prelude.e2_5_6.* classifies them from the prelude's own kernel "
        "declarations)", prel_in)
    kern_pred = ("every clean.prelude.inductives classified from its own kernel declaration (the probe dump "
                 f"{PRELUDE_DECLS_REL}: parameters, indices, mutual block, constructor types, the kernel's "
                 "rec/reflexive/nested flags, Clean's structure and class registries) by the rule list of row "
                 "clean.lean48.e2_5_6.prop's predicate, with the same classifier and inferencer that read the Lean "
                 "4.8 oleans. Clean's InductiveVal carries no unsafe flag (the kernel admits no unsafe "
                 "declaration), so `unsafe` is 0 by construction. Controls ([controls]): the dump's type and value "
                 "hashes equal D0.5's prelude.tsv for every declaration; each declaration-identical inductive has "
                 "its Lean 4.8 kernel facts (its E2.5.6 row can still differ through Clean's class registry: "
                 "clean.prelude.e2_5_6.registry_only_differs); every kernel sort equals D0.5's printed one")
    kcats = collections.Counter(i["e256"] for i in pk)
    for n, (cat, _desc) in enumerate(E256):
        row(f"clean.prelude.e2_5_6.{cat}", kcats[cat], (kern_pred if n == 0 else
            "the partition defined by row clean.prelude.e2_5_6.prop's predicate") + f". This row counts `{cat}`",
            prel_in + kern_in, consumers="E2.5.6", design=("e256",) if n == 0 else ())
    qp = kmeta["quot_type_formers"]
    row("clean.prelude.quot_type_formers", len(qp), quot_pred + ". Read from the prelude's kernel declarations "
        f"(the probe dump's `quot_kind`; the dump's quotient declarations equal D0.5's `quot` rows by the hash "
        "control)", kern_in, consumers="E2.5.6 (the `Quot` fixture)")
    axp, axp_un = kmeta["opaque_type_formers"]
    row("clean.prelude.opaque_type_formers", len(axp), ax_pred + ". Read from the prelude's kernel declarations",
        kern_in, consumers="E2.5.6")
    row("clean.prelude.opaque_type_formers_unclassified", len(axp_un), "axiom and opaque constants of the prelude "
        "whose type's end the reader could not reach (must be 0 for clean.prelude.opaque_type_formers to be "
        "complete)", kern_in)
    row("clean.prelude.type_formers", len(pl) + len(qp) + len(axp),
        "clean.prelude.inductives + clean.prelude.quot_type_formers + clean.prelude.opaque_type_formers: every type "
        "former of Clean's island prelude (E2.5.6's 'every Clean type former in the census'; the "
        "clean.prelude.e2_5_6.* rows partition the inductives, and `Quot` and the axiom/opaque formers are their "
        "own rows)", prel_in + kern_in, consumers="E2.5.6", design=("e256",))
    row("clean.prelude.e2_5_6_of_not_identical",
        sum(1 for p in pl if not p["decl_identical_lean48"] and p["e256"] in dict(E256)),
        "clean.prelude.not_decl_identical_lean48 inductives that clean.prelude.e2_5_6.* places in a row (each is "
        "listed with its row in the items census)", prel_in + kern_in, consumers="E2.5.6")
    row("clean.prelude.e2_5_6.transfer_agrees", kmeta["transfer"],
        "clean.prelude.identical_to_lean48 inductives whose E2.5.6 row from the prelude kernel equals their Lean "
        "4.8 row. A control stands behind it: every declaration-identical inductive has Lean 4.8's kernel facts "
        "(sort, parameters, indices, constructors, recursion flags, every field's class), or nothing is "
        "published", prel_in + kern_in + lean_in)
    row("clean.prelude.registry_differs_lean48", len(kmeta["registry"]),
        "clean.prelude.identical_to_lean48 inductives that Clean's class or structure registry records "
        "differently from Lean 4.8's classExtension/structureExt (environment data, not the kernel declaration; "
        "each listed in the items census with both flags)", prel_in + kern_in + lean_in, consumers="E2.5.6; C3")
    row("clean.prelude.e2_5_6.registry_only_differs", len(kmeta["row_by_registry"]),
        "clean.prelude.identical_to_lean48 inductives whose E2.5.6 row differs from their Lean 4.8 row only "
        "because of that registry difference (kernel facts identical): Lean 4.8 registers them as classes and "
        "Clean's island prelude does not, so the prelude row is not `class` ("
        + ", ".join(kmeta["row_by_registry"]) + ")", prel_in + kern_in + lean_in, consumers="E2.5.6; C3")
    row("clean.prelude.indexed_type_families", sum(1 for i in pk if i["nindices"] and i["sort"] != "prop"),
        "clean.prelude.inductives with numIndices > 0 not sorted in Prop (kernel declaration)", kern_in,
        consumers="E2.5.6; OD-9")
    row("clean.prelude.recursive", sum(1 for i in pk if i["is_rec"] and i["sort"] != "prop"),
        "non-Prop clean.prelude.inductives the kernel marks recursive", kern_in, consumers="ODT M5")
    row("clean.prelude.polymorphic_recursion", sum(1 for i in pk if i["poly_rec"]),
        "clean.lean48.polymorphic_recursion's predicate over the prelude's kernel declarations", kern_in,
        consumers="§8.2 question 10; E2.5.6 (refused row)")
    row("clean.prelude.type_valued_fields_nonclass",
        sum(1 for i in pk if i["type_fields"] and not i["class"] and i["sort"] != "prop"),
        "clean.lean48.type_valued_fields_nonclass's predicate over the prelude's kernel declarations", kern_in,
        consumers="§8.2 question 10; E2.5.6 (refused row)")
    row("clean.prelude.large_elim_fields", sum(len(i["large_elim_fields"]) for i in pk if i["sort"] != "prop"),
        "clean.lean48.large_elim_fields' predicate over the prelude's kernel declarations", kern_in,
        consumers="§8.2 question 10; E2.5.6")
    row("clean.prelude.dependent_data_fields", sum(len(i["dep_fields"]) for i in pk if i["sort"] != "prop"),
        "clean.lean48.dependent_data_fields' predicate over the prelude's kernel declarations", kern_in,
        consumers="E2.5.6 (ODT M7)")
    row("clean.prelude.unclassified_fields", sum(i["unclassified_fields"] for i in pk),
        "constructor fields of clean.prelude.inductives whose sort the inferencer could not determine (must be 0 "
        "for the field rows above to be complete)", kern_in)
    for s in ("prop", "type", "sort-poly"):
        row(f"clean.prelude.sort_{s.replace('-', '_')}", sum(1 for p in pl if p["sort"] == s),
            "clean.prelude.inductives whose printed type ends (after the last top-level ` -> `) in "
            + {"prop": "`Prop`", "type": "`Type`, `Type n`, or `Sort … + n`",
               "sort-poly": "anything else (`Sort u`, `Sort max(…)`)"}[s], prel_in)

    # ---- pairing --------------------------------------------------------------------------
    pairing, pair_rows = pairing_table(ind48, prelude, adts, c7_rust, bignum)
    n_struct = len({sp for _r, sp, c, _l, _rs in C7_ROWS if c == "structural"})
    n_over = len({sp for _r, sp, c, _l, _rs in C7_ROWS if c == "override"})
    row("pairing.c7_rows_as_written", n_struct, "structural rows the C7 bullet lists, as written (Option; Bool/bool; "
        "Unit/(); Prod/2-tuple; Except/Result; Ordering/cmp::Ordering; Empty/Infallible; UIntN/IntN; Char/char), "
        "quote-checked", design_in, consumers="V12 (C7 row count)", design=("v12",))
    row("pairing.c6_rows_as_written", n_over, "override rows the C7 bullet lists, as written (Nat; Int; Array; "
        "ByteArray; String; USize; Float; n-tuples), quote-checked", design_in, consumers="V12 (C6 registry)")
    row("pairing.name_pairs", len(pair_rows),
        "the rows above expanded to one Lean name per pair (UIntN/IntN for N in 8, 16, 32, 64: the widths Lean "
        "defines)", design_in)
    for env_name in ("lean48", "prelude"):
        pr = pairing[env_name]
        rust_side = ("an ADT in the Rust census, a Rust primitive, or an item of crates/trust-bignum at the measured commit")
        texts = {"both_sides": f"name pairs whose Lean side is an inductive in clean.{env_name} and whose Rust side "
                               f"exists ({rust_side})",
                 "lean_side_absent": f"name pairs whose Lean side is not an inductive in clean.{env_name}",
                 "rust_side_absent": f"name pairs whose Rust side does not exist ({rust_side})"}
        for k in ("both_sides", "lean_side_absent", "rust_side_absent"):
            row(f"pairing.{env_name}.{k}", pr[k], texts[k],
                design_in + (lean_in if env_name == "lean48" else prel_in) + rust_in + ["bignum"],
                consumers="C7; V12")
        for k in ("paired", "clean_only"):
            row(f"census.{env_name}.clean_{k}", pr["clean_" + k],
                f"clean.{env_name}.inductives that are " + (
                    "the Lean side of a name pair whose Rust side exists" if k == "paired" else
                    "not the Lean side of any name pair with an existing Rust side (Clean-only: F_rust would be "
                    "synthesized by C3)"),
                (lean_in if env_name == "lean48" else prel_in) + design_in)
    rust_paired = sum(1 for a in adts if a.get("paired"))
    row("census.rust.paired", rust_paired,
        "ADTs of core ∪ alloc ∪ std that are the Rust side of a name pair whose Lean side is an inductive in "
        "clean.lean48 or clean.prelude", rust_in + design_in)
    row("census.rust.rust_only", len(adts) - rust_paired,
        "ADTs of core ∪ alloc ∪ std that are not (Rust-only: F_logic is generated by C2, or a C6 override "
        "still to be written)", rust_in + design_in)

    # ---- blocked --------------------------------------------------------------------------
    row("rust.std.adts_used_by_checkpoint_a", None,
        "ADTs that appear in the monomorphized items of Checkpoint A's std build and of the two-language "
        "battery (E3.3.2's 'ODT entries used by Checkpoint A's std and the two-language battery')",
        ["head"], status="blocked", consumers="E3.3.2", design=("e332",))
    host_keys = {c: {a["key"] for a in adts if a["crate"] == c} for c in ("core", "alloc", "std")}
    for t in OTHER_TARGETS:
        for crate in ("core", "alloc", "std"):
            tk = {a["key"] for a in tool["targets"][t][crate]}
            t_in = ["targets"] if crate != "std" else ["build_std"]
            how = ("with an empty sysroot (core's and compiler_builtins' metadata built here from library/ for the "
                   f"target; the procedure reproduces the {HOST} sysroot expansion byte for byte, [controls]"
                   ".target_procedure)") if crate != "std" else (
                   "with an empty sysroot and the metadata of std's dependency graph for the target, built by cargo's "
                   "-Zbuild-std from library/Cargo.lock over a git export at the measured commit, and the cfgs and "
                   "env std's build script printed for the target (the procedure reproduces the "
                   f"{HOST} sysroot expansion byte for byte, and its build-script cfgs and env equal the host plan's, "
                   "[controls].build_std_procedure)")
            row(f"rust.{crate}.adts@{t}", len(tk),
                f"rust.{crate}.adts' predicate for {t}: the crate expanded for that target from the same library/ "
                f"{how}; line-regex control as for the host", t_in,
                consumers="Stage 2.7 (x86-64); the Linux targets")
            row(f"rust.{crate}.adts@{t}.not_on_host", len(tk - host_keys[crate]),
                f"rust.{crate}.adts@{t} whose key (crate::module path::name) is not a key of rust.{crate}.adts "
                "(listed in the items census as side `rust@<target>`)", t_in + ["rust"])
            row(f"rust.{crate}.adts@{t}.host_only", len(host_keys[crate] - tk),
                f"rust.{crate}.adts whose key is not a key of rust.{crate}.adts@{t} (listed in the items census)",
                t_in + ["rust"])
    for r in rows:
        for name in r["inputs"]:
            if name not in sets:
                raise Refusal(f"row {r['name']} names an unknown input set {name!r}")
    return rows, {"adts": adts, "ind48": ind48, "prelude": prelude, "pair_rows": pair_rows,
                  "tool": tool, "meta48": meta48, "pmeta": pmeta, "kmeta": kmeta, "head": head, "sets": sets,
                  "quot": {"lean48": q48, "prelude": qp}}


BLOCKED_REASONS = {
    "rust.std.adts_used_by_checkpoint_a": (
        "Which ADTs a build uses is a property of its monomorphized items (a rustc query over the compiled "
        "crate), not of the source or its expansion. No artifact on this host lists the ADT keys of Checkpoint "
        "A's mono items, and making one is a measurement build of Checkpoint A itself (`x.py build --stage 1 "
        "library/std` carrying the compiler-side dump the unblock condition names, under "
        "native Targo build-tree ownership), which the build owner runs.",
        "A compiler-side dump of Adt DefPathHashes reachable from Checkpoint A's mono items (e.g. the "
        "trust-ir module of stage-1 std, once ODT M1 interns nominal definitions by `origin: TypeKey`), "
        "published with its build's provenance."),
}


def pairing_table(ind48, prelude, adts, c7_rust, bignum):
    pair_rows = []
    for rid, _sp, cls, lean_names, rs in C7_ROWS:
        for ln in lean_names:
            if rs[0] == "adt":
                rust_present, rust_desc = rid in c7_rust, f"{rs[1]}::{rs[2]}::{rs[3]}"
            elif rs[0] == "prim":
                rust_present, rust_desc = True, f"primitive {rs[1]}"
            else:
                rust_present, rust_desc = rs[2] in bignum, f"trust_bignum::{rs[2]}"
            rv = ""
            if rs[0] == "adt" and rid in c7_rust:
                a = c7_rust[rid]
                rv = ",".join(v for v, _f in a["variants"]) if a["kind"] == "enum" else f"({a['kind']})"
            pr = {"row": rid, "class": cls, "lean": ln, "rust": rust_desc, "rust_present": rust_present,
                  "rust_variants": rv, "lean48": ln in ind48, "prelude": ln in prelude,
                  "lean48_ctors": ",".join(ind48[ln]["ctor_names"]) if ln in ind48 else "",
                  "prelude_decl_identical_lean48": bool(prelude.get(ln, {}).get("decl_identical_lean48")),
                  "prelude_ctors_sorted": ",".join(prelude[ln]["ctor_names"]) if ln in prelude else ""}
            for env_name in ("lean48", "prelude"):
                pr["status_" + env_name] = ("paired" if pr[env_name] and rust_present else
                                            "lean-side-absent" if not pr[env_name] else "rust-side-absent")
            pair_rows.append(pr)
    for rid, a in c7_rust.items():
        for pr in pair_rows:
            if pr["row"] == rid and pr["rust_present"] and (pr["lean48"] or pr["prelude"]):
                a["paired"] = True
    out = {}
    for env_name, pop in (("lean48", ind48), ("prelude", prelude)):
        both = sum(1 for p in pair_rows if p[env_name] and p["rust_present"])
        la = sum(1 for p in pair_rows if not p[env_name])
        ra = sum(1 for p in pair_rows if not p["rust_present"])
        paired_names = {p["lean"] for p in pair_rows if p[env_name] and p["rust_present"]}
        out[env_name] = {"both_sides": both, "lean_side_absent": la, "rust_side_absent": ra,
                         "clean_paired": len(paired_names), "clean_clean_only": len(pop) - len(paired_names)}
    return out, pair_rows


# ---------------------------------------------------------------------------
# output
# ---------------------------------------------------------------------------


def q(s):
    return json.dumps(s, ensure_ascii=False)


SET_WHAT = {
    "head": "the superproject commit the record was measured at",
    "rust": "core, alloc and std for aarch64-apple-darwin, macro-expanded by an installed trustc from library/ at the measured commit (git objects)",
    "lean48": "the imported Lean 4.8 Init: vendor/lean-core-oleans at the measured commit (git objects), MANIFEST-verified",
    "prelude": "Clean's island prelude (Environment::with_prelude()) as D0.5's committed dump records it",
    "prelude_decls": "Clean's island prelude's kernel declarations, dumped by this record's probe at the clean gitlink",
    "design": "the C7 identification table and C6's override list, quote-checked in the design at the measured commit",
    "bignum": "crates/trust-bignum at the measured commit (the Rust side of C7's Nat and Int override rows)",
    "targets": "core and alloc for the other targets, macro-expanded from library/ at the measured commit with an empty sysroot",
    "build_std": "std for every target, macro-expanded from library/ at the measured commit against the metadata cargo's -Zbuild-std builds for std's dependency graph",
}


def render_toml(rows, ctx):
    head = ctx["head"]
    out = ["# Stage 0.5 denominator: the ODT census, Clean side and Rust side (E0.12).",
           "# GENERATED by `python3 scripts/trust_core/denominators/odt.py --write`; `--check` re-measures from the",
           "# pinned inputs and fails on any difference. Do not hand-edit: change the script and regenerate.",
           "# Design of record: docs/design/2026-09-16-trust-core-architecture.md §3.2 D-2 (C2, C6, C7) and §5.2",
           "# Stage 0.5. The design gives no number for this census, so no row reproduces an [M†] value.",
           "", f"schema = {q(SCHEMA)}", 'key = "odt"', f"design = {q(DESIGN_REL)}", f"script = {q(SCRIPT_REL)}",
           'exit = "E0.12"',
           "consumers = [",
           '  "E2.5.1 (M2): the flat, Box-recursive and generic ADT denominator in core and alloc",',
           '  "E2.5.6 (M7): every Clean type former in the census, mapped to a representation or a refusal",',
           '  "E3.3.2 (M8): ODT entries used by Checkpoint A\'s std (blocked here: a usage population)",',
           '  "V12: the C7 row count and the C6 registry",',
           '  "§8.2 question 10: large eliminations, polymorphic recursion, Type-valued existentials",',
           "]",
           "# The pin: the superproject commit this record was measured at (every git read is at it).",
           "# scripts/trust_core/denominators.py re-measures at it (--rev); this script's own --check",
           "# measures at --rev (default HEAD) and ignores this line.",
           f"measured_at_commit = {q(head)}",
           "# The per-item census: one TSV row per Rust ADT, per Clean inductive and per quotient type former,",
           "# with its classes and pairing status (paired, rust-only, clean-only; `-` for a quotient), and one",
           "# row per ADT key that differs between a target and the host; published gzip-compressed as `items`",
           "# (the digest is of the decompressed text; --check compares the text, not the compressed bytes).",
           f"items = {q(ITEMS_REL)}",
           f"items_sha256 = {q(ctx['items_sha256'])}", f"items_rows = {ctx['items_rows']}", ""]
    for name, entries in ctx["sets"].items():
        out.append(f"[inputs.{name}]")
        out.append(f"what = {q(SET_WHAT[name])}")
        out.append("pins = [")
        for e in entries:
            out.append(f"  {q(e)},")
        out.append("]")
        out.append("")
    for r in rows:
        out.append("[[row]]")
        out.append(f"name = {q(r['name'])}")
        if r["value"] is not None:
            out.append(f"value = {r['value']}")
        out.append(f"status = {q(r['status'])}")
        out.append(f"predicate = {q(r['predicate'])}")
        out.append("inputs = [" + ", ".join(q(i) for i in dict.fromkeys(r["inputs"])) + "]")
        if r["consumers"]:
            out.append(f"consumers = {q(r['consumers'])}")
        if r["design"]:
            out.append("design = [" + ", ".join(q(d) for d in r["design"]) + "]")
        if r["status"] == "blocked":
            why, unblock = BLOCKED_REASONS[r["name"]]
            out.append(f"blocked = {q(why)}")
            out.append(f"unblock = {q(unblock)}")
        out.append("")
    out.append("# Controls every run must pass before any row is published (fail closed); each is also shown")
    out.append("# to fail on a perturbed input.")
    out.append("[controls]")
    tool, m48, pm = ctx["tool"], ctx["meta48"], ctx["pmeta"]
    lc = m48["lean_control"]
    out.append(f"lean_reader = {q('Lean 4.8.0 itself (' + lc['lean'] + ') re-reads the same oleans: ' + str(lc['constants']) + ' constants, ' + str(lc['inductives']) + ' inductives with identical shape (params, indices, mutual block, constructors in order, rec/nested/reflexive/unsafe, structure, class) and ' + str(lc['fields']) + ' constructor fields with identical isProp / isTypeFormerType / sort class; the comparison detects a perturbed parameter count and a perturbed field class')}")
    out.append(f"lean_platform_sets = {q('the Init census is identical for the platform sets ' + ', '.join(m48['triples']))}")
    for crate in ("core", "alloc", "std"):
        rc = tool["rustdoc_control"][crate]
        extra = (f"; {rc['rustdoc_only_cfg_doc']} rustdoc-only ADTs, all in modules holding no census ADT (cfg(doc) "
                 f"admits them), under {crate}::" + ", ".join(m or "(root)" for m in rc["rustdoc_only_modules"])
                 if rc["rustdoc_only_cfg_doc"] else "; no rustdoc-only ADT")
        out.append(f"{crate}_rustdoc = {q(str(rc['compared']) + ' module-level ADTs, each found by rustdoc JSON at the same definition path with the same kind, variant/field count and lifetime/type/const parameter counts' + extra + '; the comparison detects a perturbed count and a dropped ADT')}")
        out.append(f"{crate}_line_regex = {q(str(tool[crate + '_line_control']) + ' lines match the ADT line regex = the ADTs parsed (every one starts its line) + ' + str(tool[crate + '_skipped_in_macro_bodies']) + ' ADT keywords inside unexpanded macro bodies (not items; line-starting ones counted)')}")
    out.append(f"type_aliases = {q(str(tool['aliases']) + ' module- and body-level `type` aliases read as nodes of the Freeze analysis (not counted as ADTs); every field type of every ADT and alias parsed')}")
    out.append(f"prelude_currency = {q('the D0.5 dump was measured at clean ' + pm['d05_pin'] + '; the gitlink ' + pm['gitlink'] + ' has the identical crates/ tree ' + pm['crates_tree'])}")
    km = ctx["kmeta"]
    hc = km["hash_control"]
    kernel_hashes = (f"the probe dump and D0.5's prelude.tsv name the same {hc['declarations']} declarations, and "
                     "D0.5's structural hashes recomputed from the dumped terms equal its type hash, binder-info "
                     f"type hash and (for {hc['values']} definitions and opaques) value hash for every one; the "
                     "comparison detects a perturbed term")
    transfer = ("every declaration-identical inductive has Lean 4.8's kernel facts (sort, parameters, indices, "
                f"constructors, recursion flags, every field's class); {km['transfer']} classify exactly as their "
                "Lean 4.8 rows and the rest differ only through Clean's class registry ("
                + ", ".join(km["row_by_registry"]) + ")")
    sorts = (f"the kernel sort of all {km['sorts_agree']} prelude inductives equals the sort read from D0.5's "
             "printed type")
    out.append(f"prelude_kernel_hashes = {q(kernel_hashes)}")
    out.append(f"prelude_transfer = {q(transfer)}")
    out.append(f"prelude_sorts = {q(sorts)}")
    tcl = tool["target_control"]
    out.append(f"target_procedure = {q('the empty-sysroot procedure (core and compiler_builtins metadata built from library/ for the target) reproduces the ' + HOST + ' sysroot expansion of ' + ' and '.join(tcl['host_reproduced']) + ' byte for byte; per target, the line-regex control holds: ' + '; '.join(t + ' ' + c + ' ' + str(tcl[t + '.' + c]['line_control']) + ' lines' for t in OTHER_TARGETS for c in ('core', 'alloc')))}")
    bsh = tcl["build_std"]["targets"][HOST]
    build_std = (f"the -Zbuild-std procedure is run for {HOST} too: std expanded against the metadata it builds "
                 f"reproduces the {HOST} sysroot expansion of std byte for byte (sha256:{bsh['sha256']}), and the "
                 f"cfgs ({', '.join(bsh['cfgs'])}) and env ({', '.join(k + '=' + v for k, v in sorted(bsh['env'].items()))}) "
                 "std's build script prints under it equal the host plan's; every crates.io archive cargo can read has "
                 "library/Cargo.lock's sha256 (checked before the run), and cargo runs --frozen; per target, the "
                 "line-regex control holds: " + "; ".join(f"{t} std {tcl[t + '.std']['line_control']} lines"
                                                           for t in OTHER_TARGETS))
    out.append(f"build_std_procedure = {q(build_std)}")
    out.append("")
    out.append("# C7/C6 name pairs, one per Lean name. lean48_ctors is kernel order; the D0.5 dump gives the")
    out.append("# prelude's constructor names only (sorted), whose kernel order equals Lean 4.8's exactly when")
    out.append("# prelude_decl_identical_lean48. rust_variants is declaration order.")
    for p in ctx["pair_rows"]:
        out.append("[[pair]]")
        for k in ("row", "class", "lean", "rust", "rust_variants", "status_lean48", "status_prelude"):
            out.append(f"{k} = {q(p[k])}")
        for k in ("rust_present", "lean48", "prelude", "prelude_decl_identical_lean48"):
            out.append(f"{k} = {'true' if p[k] else 'false'}")
        for k in ("lean48_ctors", "prelude_ctors_sorted"):
            out.append(f"{k} = {q(p[k])}")
        out.append("")
    return "\n".join(out).rstrip() + "\n"


def items_tsv(ctx):
    lines = ["side\tkey\tkind\tclasses\tpairing"]
    for a in sorted(ctx["adts"], key=lambda a: (a["key"], a["line"])):
        cls = (f"shape={a['shape']};generic={int(a['generic'])};lifetimes={len(a['lifetimes'])};"
               f"recursion={a['recursion']};owned_cycle={a['owned_cycle'] or 'none'};"
               f"interior={a['interior']};local={int(a['local'])};"
               f"variants={a['variant_count']};fields={a['field_count']};e2_5_1={a['e251']};"
               f"lang={a['lang']};repr={','.join(a['repr'])}")
        lines.append(f"rust\t{a['key']}\t{a['kind']}\t{cls}\t{'paired' if a.get('paired') else 'rust-only'}")
    paired48 = {p["lean"] for p in ctx["pair_rows"] if p["lean48"] and p["rust_present"]}
    pairedp = {p["lean"] for p in ctx["pair_rows"] if p["prelude"] and p["rust_present"]}
    for n, i in sorted(ctx["ind48"].items()):
        cls = (f"sort={i['sort']};params={i['nparams']};indices={i['nindices']};ctors={i['nctors']};"
               f"structure={int(i['structure'])};class={int(i['class'])};rec={int(i['is_rec'])};"
               f"mutual={i['mutual']};nested={int(i['is_nested'])};reflexive={int(i['is_reflexive'])};"
               f"fields={i['fields']};prop_fields={i['prop_fields']};type_fields={i['type_fields']};"
               f"prop_family_fields={i['prop_family_fields']};"
               f"poly_rec={len(i['poly_rec'])};dep_fields={len(i['dep_fields'])};e2_5_6={i['e256']};"
               f"module={i['module']}")
        lines.append(f"clean.lean48\t{n}\tinductive\t{cls}\t{'paired' if n in paired48 else 'clean-only'}")
    host_keys = {c: {a["key"] for a in ctx["adts"] if a["crate"] == c} for c in ("core", "alloc", "std")}
    for t in OTHER_TARGETS:
        for crate in ("core", "alloc", "std"):
            tk = {a["key"]: a for a in ctx["tool"]["targets"][t][crate]}
            for k in sorted(set(tk) - host_keys[crate]):
                lines.append(f"rust@{t}\t{k}\t{tk[k]['kind']}\t-\tnot-on-host")
            for k in sorted(host_keys[crate] - set(tk)):
                lines.append(f"rust@{t}\t{k}\t-\t-\thost-only")
    for n, p in sorted(ctx["prelude"].items()):
        k = p["kernel"]
        cls = (f"sort={p['sort']};universes={p['universe_arity']};ctors={','.join(p['ctor_names'])};"
               f"vs_lean48={p['vs_lean48']};vs_lean430={p['vs_lean430']};"
               f"decl_identical_lean48={int(p['decl_identical_lean48'])};params={k['nparams']};"
               f"indices={k['nindices']};structure={int(k['structure'])};class={int(k['class'])};"
               f"rec={int(k['is_rec'])};mutual={k['mutual']};nested={int(k['is_nested'])};"
               f"reflexive={int(k['is_reflexive'])};fields={k['fields']};prop_fields={k['prop_fields']};"
               f"type_fields={k['type_fields']};poly_rec={len(k['poly_rec'])};dep_fields={len(k['dep_fields'])};"
               f"registry_vs_lean48={ctx['kmeta']['registry'].get(n, 'same' if p['decl_identical_lean48'] else '-')};"
               f"e2_5_6={p['e256']}")
        lines.append(f"clean.prelude\t{n}\tinductive\t{cls}\t{'paired' if n in pairedp else 'clean-only'}")
    for env_name in ("lean48", "prelude"):
        for n in ctx["quot"][env_name]:
            lines.append(f"clean.{env_name}\t{n}\tquot\tquot_kind=type\t-")
    return "\n".join(lines) + "\n"


def summary(rows):
    w = max(len(r["name"]) for r in rows)
    return "\n".join(f"{r['name']:<{w}}  {'BLOCKED' if r['value'] is None else r['value']}" for r in rows)


def need(cond, detail):
    if not cond:
        raise Refusal(f"self-test failed: {detail}")


def self_test():
    """Parser controls on literal inputs, including the traps the census meets."""
    src = """
    #[lang = "x"] pub struct A<'a, T: Tr<X = u8>, const N: usize = { 1 << 2 }>(pub(crate) [T; N], &'a u8);
    pub(crate) enum B { X = 1 << 3, Y(Box<B>), Z { n: Option<Box<Self>> } }
    union U { a: u8, b: f32 }
    fn union(x: u8) { struct Local; let u = a.union(b); }
    macro_rules! m { ($n:ident) => { struct $n; struct Fixed; } }
    m!{ struct NotAnItem; }
    struct W where T: Fn(u8) -> u8 { f: fn(W) -> u8, p: *const W, q: NonNull<W> }
    mod inner { pub struct D; }
    const _: () = { struct InBlock; };
    """
    c = RustCensus("t", src)
    got = [(a["path"], a["name"], a["kind"], a["shape"]) for a in c.adts]
    want = [("", "A", "struct", "tuple"), ("", "B", "enum", "enum"), ("", "U", "union", "named"),
            ("{fn union}", "Local", "struct", "unit"), ("", "W", "struct", "named"), ("inner", "D", "struct", "unit"),
            ("{block}", "InBlock", "struct", "unit")]
    need(got == want, got)
    # `struct Fixed` in the macro_rules body and `struct NotAnItem` in the invocation are not items
    need(c.skipped_macro_adt_keywords == 2, c.skipped_macro_adt_keywords)
    need(c.skipped_at_line_start == 0 and c.parsed_at_line_start == 3,
         (c.skipped_at_line_start, c.parsed_at_line_start))
    a = c.adts[0]
    need((a["lifetimes"], a["tparams"], a["cparams"]) == (["'a"], ["T"], ["N"]), a)
    need(len(a["fields"]) == 2 and a["attrs"] == ['lang = "x"'], a)
    need([v[0] for v in c.adts[1]["variants"]] == ["X", "Y", "Z"], c.adts[1]["variants"])
    classify_rust_stub = [dict(x, crate="core", key=x["name"]) for x in c.adts]
    stub_cells = [dict(crate="core", path="cell", name=n, kind="struct", shape="named", line=0, local=False,
                       attrs=[], lifetimes=[], tparams=["T"], cparams=[], fields=[("v", [("id", "T")])],
                       variants=[]) for n in ("UnsafeCell", "SyncUnsafeCell")]
    classify_rust(classify_rust_stub + stub_cells)
    rec = {x["name"]: x["recursion"] for x in classify_rust_stub}
    need(rec["B"] == "box", rec)
    need(rec["W"] == "fnptr+pointer", rec)
    need(adt_line_control(src) == 3, adt_line_control(src))   # B, U and W start their lines
    freeze_src = """
    pub mod cell {
        pub struct UnsafeCell<T: ?Sized> { value: T }
        pub struct SyncUnsafeCell<T: ?Sized> { value: UnsafeCell<T> }
        pub struct Cell<T: ?Sized> { value: UnsafeCell<T> }
    }
    pub type Alias = cell::Cell<u8>;
    impl Foo { type Assoc = cell::Cell<u8>; }
    pub struct ViaAlias { a: Alias }
    pub struct Ptr<T> { p: *const T }
    pub struct ViaPtr { x: Ptr<cell::Cell<u8>> }
    pub struct Wrap<T> { t: T }
    pub struct ViaWrap { w: Wrap<crate::cell::Cell<u8>> }
    pub struct Proj<I: Iterator> { x: I::Item, y: <I as Iterator>::Item }
    pub struct Niche(u32 is const 0..=const 9);
    pub struct Fns { f: fn(cell::Cell<u8>) -> u8, g: &'static cell::Cell<u8> }
    """
    fc = RustCensus("core", freeze_src)
    need([a["name"] for a in fc.aliases] == ["Alias"], fc.aliases)   # not the impl's `type Assoc`
    for a in fc.adts:
        a["key"] = a["name"]
    classify_rust(fc.adts, fc.aliases)
    got = {a["name"]: a["interior"] for a in fc.adts}
    want = {"UnsafeCell": "yes", "SyncUnsafeCell": "yes", "Cell": "yes", "ViaAlias": "yes", "Ptr": "no",
            "ViaPtr": "no", "Wrap": "no", "ViaWrap": "yes", "Proj": "no", "Niche": "no", "Fns": "no"}
    need(got == want, got)
    need({a["name"]: a["byvalue_params"] for a in fc.adts}["Wrap"] == ["T"], "Wrap holds T by value")
    for ty, want_sort in (("(u : Sort u) -> u -> ((u1 : Sort u) -> u1 -> Prop)", "prop"),
                          ("Sort u -> Sort max(1, u)", "type"),
                          ("(u : Sort u) -> (u -> u -> Sort v) -> Sort max(u, v + 1)", "type"),
                          ("Sort u -> Sort u", "sort-poly"), ("Prop -> Type", "type")):
        need(prelude_sort(ty) == want_sort, (ty, prelude_sort(ty)))
    # D0.5's structural hash, known answers from its prelude.tsv (Nat.succ : Nat -> Nat; id's type
    # {u} (α : Sort u) -> α -> α with an implicit binder; Nat : Type).
    nodes = [["C", "Nat", []], ["P", "Default", 0, 0], ["S", ["p", "u"]], ["B", 0], ["B", 1],
             ["P", "Default", 3, 4], ["P", "Implicit", 2, 5], ["S", ["+", ["0"]]]]
    for root, lps, want_k, want_e in ((1, [], "8b3ede3160224f3c", "00ac4af08343b155"),
                                      (6, ["u"], "d7dd4f6877d24fc3", "fd43bb115e889fc3"),
                                      (7, [], "2f42b8c0f53f4fa1", "2f42b8c0f53f4fa1")):
        got = (f"{d05_hash(nodes, root, lps, False):016x}", f"{d05_hash(nodes, root, lps, True):016x}")
        need(got == (want_k, want_e), (root, got))
    # The quotient type-former count: by kernel kind, and refused when a kind carries another name.
    quots = {"Quot": {"kind": "quot", "quot_kind": "type"}, "Quot.mk": {"kind": "quot", "quot_kind": "ctor"},
             "Quot.lift": {"kind": "quot", "quot_kind": "lift"}, "Quot.ind": {"kind": "quot", "quot_kind": "ind"},
             "Quot.sound": {"kind": "quot", "quot_kind": "sound"}, "Quotient": {"kind": "definition"}}
    need(quot_type_formers(quots, "fixture") == ["Quot"], "Quot is the one quotient type former")
    need(quot_type_formers({k: v for k, v in quots.items() if k != "Quot"}, "fixture") == [], "no Quot, none")
    for bad in ({"Quot2": {"kind": "quot", "quot_kind": "type"}}, {"Quot": {"kind": "quot", "quot_kind": "mk"}}):
        try:
            quot_type_formers(bad, "fixture")
            need(False, f"quot_type_formers accepted {bad}")
        except Refusal as e:
            need("self-test" not in str(e), e)
    # The axiom/opaque type-former count: a Pi telescope ending in Sort (l+1) or Sort u is a type former,
    # one ending in Prop or in a non-sort is not, and a type the reader cannot reach is unclassified.
    class _Env:
        def __init__(self, types, kinds):
            self.types, self.consts = types, {n: {"kind": k} for n, k in kinds.items()}

        def type_of(self, name):
            return self.types[name]

    class _Inf:
        def whnf(self, e):
            return ("S", ("+", ("0",))) if e == ("C", "TypeAbbrev") else e
    one, zero = ("+", ("0",)), ("0",)
    fx = _Env({"IO": ("P", "a", ("S", one), ("S", one)), "Pp": ("P", "a", ("S", one), ("S", zero)),
               "Ax": ("C", "Nat"), "Poly": ("S", ("p", "u")), "Viaw": ("C", "TypeAbbrev"), "Lost": None,
               "Def": ("S", one)},
              {"IO": "axiom", "Pp": "axiom", "Ax": "axiom", "Poly": "opaque", "Viaw": "axiom", "Lost": "axiom",
               "Def": "definition"})
    need(opaque_type_formers(fx, _Inf(), "fixture") == ([("IO", "type"), ("Poly", "sort-poly"), ("Viaw", "type")],
                                                         ["Lost"]), opaque_type_formers(fx, _Inf(), "fixture"))
    # The -Zbuild-std helpers: cargo's index layout, the lock reader, and the build-script directive filter.
    need([index_path(n) for n in ("a", "cc", "Syn", "Serde")] == ["1/a", "2/cc", "3/s/syn", "se/rd/serde"], "index path")
    lock = ('version = 4\n\n[[package]]\nname = "libc"\nversion = "0.2.1"\nsource = "registry+https://github.com/'
            'rust-lang/crates.io-index"\nchecksum = "' + "a" * 64 + '"\n\n[[package]]\nname = "std"\nversion = "0.0.0"\n')
    need(lock_packages(lock) == [("libc", "0.2.1", "registry+https://github.com/rust-lang/crates.io-index", "a" * 64),
                                 ("std", "0.0.0", "", "")], lock_packages(lock))
    with tempfile.TemporaryDirectory() as d:
        out = Path(d) / "output"
        out.write_text("cargo:rerun-if-changed=build.rs\ncargo:rustc-check-cfg=cfg(x)\ncargo:rustc-cfg=backtrace_in_libstd\n"
                       "cargo::rustc-env=STD_ENV_ARCH=x86_64\n")
        need(build_script_directives(out) == (["backtrace_in_libstd"], {"STD_ENV_ARCH": "x86_64"}), "directives")
        for bad in ("cargo:rustc-link-lib=c\n", "not a directive\n"):
            out.write_text(bad)
            try:
                build_script_directives(out)
                need(False, f"build_script_directives accepted {bad!r}")
            except Refusal as e:
                need("self-test" not in str(e), e)
    return ("self-test: parser, recursion and Freeze classifiers, aliases, line control, D0.5's hash, the quotient "
            "count and the -Zbuild-std helpers pass")


def main(argv=None):
    global REV, TRUSTC
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--write", action="store_true")
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--emit-items")
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--rev", default="HEAD", help="the superproject revision every git read is at (default HEAD)")
    ap.add_argument("--record", type=Path, help=f"the record (default {TOML_REL})")
    ap.add_argument("--trustc", type=Path, help="the toolchain to expand with (default: PATH, then the atpkg store)")
    ap.add_argument("--probe-prelude", action="store_true",
                    help=f"rebuild the prelude probe at --rev's clean gitlink and require it to reproduce "
                         f"{PRELUDE_DECLS_REL} (with --write: publish its output there)")
    args = ap.parse_args(argv)
    if args.probe_prelude:
        try:
            REV = git("rev-parse", "--verify", f"{args.rev}^{{commit}}").strip()
            return probe_prelude(args.write)
        except Unavailable as e:
            print(f"odt: UNAVAILABLE: {e}", file=sys.stderr)
            return 3
        except Refusal as e:
            print(f"odt: REFUSED: {e}", file=sys.stderr)
            return 2
    try:
        print(self_test())
        if args.self_test:
            return 0
        REV = git("rev-parse", "--verify", f"{args.rev}^{{commit}}").strip()
        TRUSTC = args.trustc
        rows, ctx = measure()
        items = items_tsv(ctx)
        ctx["items_sha256"] = "sha256:" + sha256(items.encode())
        ctx["items_rows"] = items.count("\n") - 1
        text = render_toml(rows, ctx)
    except Unavailable as e:
        print(f"odt: UNAVAILABLE: {e}; the record cannot be re-measured on this host (not drift, not a pass)",
              file=sys.stderr)
        return 3
    except Refusal as e:
        print(f"odt: REFUSED: {e}", file=sys.stderr)
        return 2
    print(summary(rows))
    if args.emit_items:
        Path(args.emit_items).write_text(items)
    target = args.record or REPO / TOML_REL
    items_file = target.with_name(Path(ITEMS_REL).name)
    if args.write:
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)
        items_file.write_bytes(gzip.compress(items.encode(), compresslevel=9, mtime=0))
    if args.check:
        old = target.read_text() if target.exists() else ""
        # A later commit that changes none of the inputs re-measures the same record: the superproject
        # sha is the only text allowed to differ; every digest, pin and value must match.
        rec = re.search(r'^measured_at_commit = "([0-9a-f]{40})"$', old, re.M)
        if rec:
            old = old.replace(rec.group(1), ctx["head"])
        if old != text:
            print("odt: --check: the committed odt.toml differs from this measurement", file=sys.stderr)
            return 1
        try:
            published = gzip.decompress(items_file.read_bytes()).decode("utf-8")
        except (OSError, EOFError, UnicodeDecodeError) as e:
            print(f"odt: --check: {items_file}: {e}", file=sys.stderr)
            return 1
        if published != items:
            print(f"odt: --check: {items_file} differs from this measurement's per-item census", file=sys.stderr)
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
