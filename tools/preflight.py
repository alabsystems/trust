#!/usr/bin/env python3
"""Trust build preflight checker.

Fails fast, in seconds, on the failure classes that have historically only
surfaced *after* paying for a full `x.py build` (up to 60 minutes each):

  1. submodule drift        -> stale first-party/ trees, bogus E0599/E0432
  2. lockfile skew          -> `cannot update the lock file ... --locked`
  3. tools allowlist holes  -> a stage2 that COMPILES but cannot VERIFY
  4. assorted cheap guards  -> concurrent builds, already-broken sysroots

Design rules this file obeys:

  * NOTHING here mutates the working tree.  Not a lockfile, not a submodule,
    not a config.  A checker that "helpfully" fixes things is precisely how a
    `cargo update` manufactured an unsatisfiable futures-core conflict.  The
    deep probe hashes every lockfile before and after and screams if one moved.
  * Facts about bootstrap's behaviour are PARSED OUT OF bootstrap's source at
    runtime (tool names, backend source-manifest paths, allowlist semantics),
    never hardcoded, so this checker cannot quietly drift from the thing it
    is auditing.
  * Every finding carries a copy-pasteable fix.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path

try:
    import tomllib
except ModuleNotFoundError:  # pragma: no cover - the .sh launcher prevents this
    sys.stderr.write(
        "preflight: needs python >= 3.11 for tomllib; run tools/preflight.sh instead\n"
    )
    raise SystemExit(2)

FAIL, WARN, INFO, OK = "FAIL", "WARN", "INFO", "OK"
_ORDER = {FAIL: 0, WARN: 1, INFO: 2, OK: 3}

PRUNE_DIRS = {".git", "build", "target", "node_modules", ".cargo", "__pycache__"}
DEP_TABLES = ("dependencies", "dev-dependencies", "build-dependencies")
TOOL_RS = "src/bootstrap/src/core/build_steps/tool.rs"
DIST_RS = "src/bootstrap/src/core/build_steps/dist.rs"

# The function that actually decides which binaries a finished sysroot carries.
SYSROOT_BINS_FN = "restored_sysroot_bins_for_tool_settings"
# The two DIFFERENT selectors a `[build] tools` entry is matched through. Which
# one applies depends on the call site, and conflating them is what made this
# audit report tools that are demonstrably present in build/host/stage2/bin.
USER_TOOL_SELECTOR = "tool_config_entry_selects_user_tool"  # entry -> Trust name
STEP_SELECTOR = "tool_matches_config_entry"                 # entry -> upstream name

# The marker cargo/targo emits when a resolve WOULD have rewritten the lock.
# Classifying on this string (not on the exit code) is what separates real
# skew from "the registry cache is cold" / "--offline blocked a download".
LOCKED_MARKERS = (
    "because --locked was passed",
    "--locked was passed",
    "the lock file .* needs to be updated",
    "lock file is out of date",
)


# --------------------------------------------------------------------------
# reporting
# --------------------------------------------------------------------------
@dataclass
class Finding:
    severity: str
    check: str
    title: str
    detail: list[str] = field(default_factory=list)
    fix: list[str] = field(default_factory=list)


class Report:
    def __init__(self, color: bool) -> None:
        self.findings: list[Finding] = []
        self.color = color

    def add(self, *a, **kw) -> None:
        self.findings.append(Finding(*a, **kw))

    def _c(self, s: str, code: str) -> str:
        return f"\033[{code}m{s}\033[0m" if self.color else s

    def tag(self, sev: str) -> str:
        return {
            FAIL: self._c(" FAIL ", "1;37;41"),
            WARN: self._c(" WARN ", "1;30;43"),
            INFO: self._c(" INFO ", "1;37;44"),
            OK: self._c("  OK  ", "1;30;42"),
        }[sev]

    def emit(self, elapsed: float, checks_run: list[str]) -> int:
        by_check: dict[str, list[Finding]] = {}
        for f in self.findings:
            by_check.setdefault(f.check, []).append(f)

        print()
        print(self._c("=" * 78, "1"))
        print(self._c("  TRUST BUILD PREFLIGHT", "1"))
        print(self._c("=" * 78, "1"))

        for check in checks_run:
            items = sorted(by_check.get(check, []), key=lambda f: _ORDER[f.severity])
            print(f"\n{self._c('--- ' + check + ' ' + '-' * max(0, 70 - len(check)), '1')}")
            if not items:
                print(f"  {self.tag(OK)} nothing to report")
                continue
            for f in items:
                print(f"  {self.tag(f.severity)} {f.title}")
                for d in f.detail:
                    print(f"         {d}")
                for i, cmd in enumerate(f.fix):
                    label = "fix:" if i == 0 else "    "
                    print(f"         {self._c(label, '1;36')} {cmd}")

        fails = [f for f in self.findings if f.severity == FAIL]
        warns = [f for f in self.findings if f.severity == WARN]

        plan, seen = [], set()
        for f in fails:
            for cmd in f.fix:
                if cmd not in seen and not cmd.lstrip().startswith("#"):
                    seen.add(cmd)
                    plan.append(cmd)
        if plan:
            print(f"\n{self._c('--- REMEDIATION PLAN (one paste, in order) ' + '-' * 34, '1')}")
            for cmd in plan:
                print(f"  {cmd}")

        print()
        print(self._c("=" * 78, "1"))
        if fails:
            print(
                f"  {self.tag(FAIL)} {len(fails)} blocking, {len(warns)} warning(s)"
                f"   [{elapsed:.1f}s]  DO NOT START A BUILD."
            )
            rc = 1
        else:
            print(
                f"  {self.tag(OK)} 0 blocking, {len(warns)} warning(s)"
                f"   [{elapsed:.1f}s]  cleared for x.py."
            )
            rc = 0
        print(self._c("=" * 78, "1"))
        return rc


# --------------------------------------------------------------------------
# helpers
# --------------------------------------------------------------------------
def run(cmd: list[str], cwd: Path | None = None, timeout: int = 60) -> tuple[int, str, str]:
    try:
        p = subprocess.run(
            cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout, check=False
        )
        return p.returncode, p.stdout, p.stderr
    except (subprocess.TimeoutExpired, FileNotFoundError, OSError) as e:
        return 127, "", str(e)


_TOML_CACHE: dict[str, tuple] = {}


def load_toml(path: Path):
    """Parse a TOML file, memoized for the lifetime of the run.

    Nothing here mutates the tree, so a file cannot change under us mid-run;
    and the same manifests get read many times over (once per workspace whose
    graph reaches them). Measured on this tree: 1030 distinct manifests behind
    ~1140 lookups from the lockfile tier alone, so the cache is what pays for
    the cascade probe below instead of the cascade probe costing extra.
    """
    key = str(path)
    hit = _TOML_CACHE.get(key)
    if hit is not None:
        return hit
    try:
        with path.open("rb") as fh:
            res = (tomllib.load(fh), None)
    except Exception as e:  # malformed TOML is itself a finding
        res = (None, f"{type(e).__name__}: {e}")
    _TOML_CACHE[key] = res
    return res


def sha256(path: Path) -> str:
    try:
        return hashlib.sha256(path.read_bytes()).hexdigest()
    except OSError:
        return "<unreadable>"


def rel(root: Path, p: Path) -> str:
    try:
        return str(p.relative_to(root))
    except ValueError:
        return str(p)


# --------------------------------------------------------------------------
# bootstrap-source facts (parsed, never hardcoded)
# --------------------------------------------------------------------------
def strip_line_comments(s: str) -> str:
    """Blank out `//` comments without disturbing string literals.

    Every parser below brace-matches, and a `{` inside a comment would derail
    it. Doc comments in tool.rs contain plenty of prose braces.
    """
    out: list[str] = []
    i, n, in_str = 0, len(s), False
    while i < n:
        c = s[i]
        if in_str:
            if c == "\\" and i + 1 < n:
                out.append(s[i:i + 2])
                i += 2
                continue
            if c == '"':
                in_str = False
            out.append(c)
            i += 1
            continue
        if c == '"':
            in_str = True
            out.append(c)
            i += 1
            continue
        if c == "/" and i + 1 < n and s[i + 1] == "/":
            while i < n and s[i] != "\n":
                out.append(" ")
                i += 1
            continue
        out.append(c)
        i += 1
    return "".join(out)


def _match_brace(s: str, start: int) -> int:
    """Index of the `}` closing the `{` at `start`, or -1."""
    depth = 0
    for i in range(start, len(s)):
        if s[i] == "{":
            depth += 1
        elif s[i] == "}":
            depth -= 1
            if depth == 0:
                return i
    return -1


def fn_body(s: str, name: str) -> str | None:
    """Text between the outermost braces of `fn <name>(..)`."""
    m = re.search(r"\bfn\s+" + re.escape(name) + r"\s*\(", s)
    if not m:
        return None
    depth, i = 0, m.end() - 1
    while i < len(s):  # walk past the argument list
        if s[i] == "(":
            depth += 1
        elif s[i] == ")":
            depth -= 1
            if depth == 0:
                break
        i += 1
    j = s.find("{", i)
    if j < 0:
        return None
    k = _match_brace(s, j)
    return s[j + 1:k] if k > 0 else None


@dataclass
class AliasTable:
    """A parsed `match <entry> { .. }` selector out of tool.rs.

    Parsed, not transcribed: a table copied into this file is a table that
    silently rots, and the whole value of this audit is that it agrees with
    bootstrap about what a config selects.
    """

    name: str
    arms: dict[str, frozenset[str]]
    identity_fallback: bool

    def selects(self, entry: str, target: str) -> bool:
        if entry in self.arms:
            return target in self.arms[entry]
        return self.identity_fallback and entry == target

    @property
    def entries(self) -> set[str]:
        return set(self.arms)

    @property
    def targets(self) -> set[str]:
        return {t for v in self.arms.values() for t in v}


def parse_alias_table(s: str, fn_name: str) -> AliasTable | None:
    body = fn_body(s, fn_name)
    if body is None:
        return None
    m = re.search(r"\bmatch\s+\w+\s*\{", body)
    if not m:
        return None
    close = _match_brace(body, m.end() - 1)
    if close < 0:
        return None
    inner = body[m.end():close]

    arms: dict[str, frozenset[str]] = {}
    identity = False
    i, n = 0, len(inner)
    while True:
        a = inner.find("=>", i)
        if a < 0:
            break
        lhs = inner[i:a]
        j = a + 2
        while j < n and inner[j].isspace():
            j += 1
        if j < n and inner[j] == "{":  # block-bodied arm
            k = _match_brace(inner, j)
            if k < 0:
                return None
            rhs, end = inner[j:k + 1], k + 1
            while end < n and (inner[end].isspace() or inner[end] == ","):
                end += 1
        else:
            depth, k = 0, j
            while k < n:
                ch = inner[k]
                if ch in "([{":
                    depth += 1
                elif ch in ")]}":
                    depth -= 1
                elif ch == "," and depth == 0:
                    break
                k += 1
            rhs, end = inner[j:k], k + 1
        names = re.findall(r'"([^"]+)"', lhs)
        if names:
            targets = frozenset(re.findall(r'"([^"]+)"', rhs))
            for nm in names:
                arms[nm] = targets
        elif re.search(r"\w+\s*==\s*\w+", rhs):
            identity = True  # `_ => config_tool == tool`
        i = end
    return AliasTable(fn_name, arms, identity) if arms else None


@dataclass
class SysrootBin:
    src: str  # upstream cargo source-binary name (what `--bin` selects)
    install: str  # Trust-canonical name the sysroot actually carries
    guards: tuple[str, ...]


def parse_sysroot_bins(s: str) -> tuple[list[SysrootBin], bool] | None:
    """`restored_sysroot_bins_for_tool_settings` as (guards -> installed name).

    This function, not the allowlist alone, decides what a finished sysroot
    contains, and modelling the allowlist without it is precisely why this
    audit used to report `targo-fmt` as unselected while stage2/bin held a
    `targo-fmt`. Two things it captures that a flat allowlist model cannot:

      * SIDE-EFFECT INSTALLS. One selection can push several binaries -
        `cargo-clippy` installs BOTH `tippy` and `targo-tippy`. Nothing in
        `[build] tools` names `targo-tippy` for that to happen.
      * THE SECOND SELECTOR. The fmt/clippy/miri families are gated by
        `extended_rustc_tool_is_default_step_for_tool_settings`, which matches
        entries through `tool_matches_config_entry` against UPSTREAM source
        names - so the entry `trustfmt` selects the `cargo-fmt` step, which
        installs `targo-fmt`. Under the other selector (`..selects_user_tool`)
        `trustfmt` does NOT select `targo-fmt`, which is the mismatch.
    """
    body = fn_body(s, SYSROOT_BINS_FN)
    if body is None:
        return None
    bins: list[SysrootBin] = []
    stack: list[str | None] = []
    pending: list[str] = []
    modelled = True
    for ch in body:
        if ch == "{":
            header = "".join(pending).strip()
            pending = []
            mm = re.search(r"(?s).*\bif\s+(.+)$", header)
            if mm:
                stack.append(" ".join(mm.group(1).split()))
            else:
                if re.search(r"\belse\s*$", header) or re.search(r"\bmatch\b", header):
                    modelled = False  # control flow this model does not describe
                stack.append(None)
        elif ch == "}":
            pending = []
            if stack:
                stack.pop()
        elif ch == ";":
            pm = re.search(
                r'bins\.push\(\(\s*"([^"]+)"\s*,\s*"([^"]+)"\s*\)\)', "".join(pending)
            )
            if pm:
                bins.append(
                    SysrootBin(pm.group(1), pm.group(2), tuple(g for g in stack if g))
                )
            pending = []
        else:
            pending.append(ch)
    return bins, modelled


def _or_terms(body: str) -> list[str] | None:
    """Terms of a helper that is a flat `a || b || c` chain - and nothing else.

    Returning None (rather than guessing) on anything with `&&`, `!`, `if` or
    `match` is the point: an unmodellable gate must degrade to "unknown", never
    to a confident answer.
    """
    b = " ".join(body.split())
    if "&&" in b or "!" in b or re.search(r"\b(if|match|return)\b", b):
        return None
    calls = [m.group(0) for m in re.finditer(r"\w+\s*\([^()]*\)", b)]
    rest = re.sub(r"\w+\s*\([^()]*\)", " ", b)
    idents = re.findall(r"[A-Za-z_]\w*", rest)
    return calls + idents


@dataclass
class BootstrapFacts:
    gated_tools: list[str]
    l2_backends: list[str]
    source_manifests: dict[str, str]
    tool_paths: list[str]
    allowlist_semantics_ok: bool
    tool_rs_found: bool
    user_sel: AliasTable | None = None
    step_sel: AliasTable | None = None
    sysroot_bins: list[SysrootBin] = field(default_factory=list)
    sysroot_bins_modelled: bool = False
    compat_aliases: set[str] = field(default_factory=set)
    dist_components: list[str] = field(default_factory=list)
    src: str = ""


def read_bootstrap_facts(root: Path) -> BootstrapFacts:
    src = root / TOOL_RS
    if not src.exists():
        return BootstrapFacts([], [], {}, [], False, False)
    s = strip_line_comments(src.read_text(errors="replace"))

    gated = sorted(
        set(
            re.findall(
                r'tool_enabled_for_tool_settings\([^,]+,\s*[^,]+,\s*"([^"]+)"\s*\)', s
            )
        )
    )
    l2 = sorted(set(re.findall(r'l2_backend_enabled\(\s*tools\s*,\s*"([^"]+)"\s*\)', s)))
    consts = dict(
        (m[0].split("_SOURCE_MANIFEST")[0].lower(), m[1])
        for m in re.findall(r'const\s+(\w+_SOURCE_MANIFEST)\s*:\s*&str\s*=\s*"([^"]+)"', s)
    )
    tool_paths = sorted(set(re.findall(r'path:\s*"([^"]+)"', s)))

    # `l2_backend_enabled` must still mean "absent => all, present => only these".
    l2_body = fn_body(s, "l2_backend_enabled") or ""
    semantics_ok = "None => true" in l2_body and "Some(set)" in l2_body

    parsed = parse_sysroot_bins(s)
    bins, bins_ok = parsed if parsed else ([], False)

    compat_body = fn_body(s, "upstream_compat_bin_for_tool_source") or ""
    # `rustc`/`trustc` are materialised on the Assemble path, not here.
    compat = set(re.findall(r'"([^"]+)"', compat_body)) | {"rustc", "trustc"}

    dist_src = root / DIST_RS
    dist_components: list[str] = []
    if dist_src.exists():
        ds = strip_line_comments(dist_src.read_text(errors="replace"))
        dist_components = sorted(
            set(
                re.findall(
                    r'should_build_extended_tool\(\s*builder\s*,\s*"([^"]+)"\s*\)', ds
                )
            )
        )

    return BootstrapFacts(
        gated_tools=gated,
        l2_backends=l2,
        source_manifests=consts,
        tool_paths=tool_paths,
        allowlist_semantics_ok=semantics_ok,
        tool_rs_found=True,
        user_sel=parse_alias_table(s, USER_TOOL_SELECTOR),
        step_sel=parse_alias_table(s, STEP_SELECTOR),
        sysroot_bins=bins,
        sysroot_bins_modelled=bins_ok,
        compat_aliases=compat,
        dist_components=dist_components,
        src=s,
    )


class ToolModel:
    """Evaluates bootstrap's real tool gates for one concrete config.

    `installs(name)` answers True / False / None, and None genuinely means
    "this checker cannot tell" - reported as a WARN, never silently coerced.
    """

    def __init__(self, facts: BootstrapFacts, extended: bool,
                 tools: list[str] | None, unstable: bool, ay_present: bool) -> None:
        self.f = facts
        self.extended = extended
        self.tools = tools
        self.unstable = unstable
        self.ay_present = ay_present
        self._helpers: dict[str, list[str] | None] = {}

    @property
    def usable(self) -> bool:
        return bool(
            self.f.tool_rs_found
            and self.f.sysroot_bins
            and self.f.sysroot_bins_modelled
            and self.f.user_sel
            and self.f.step_sel
        )

    # --- the three primitive gates ---------------------------------------
    def tool_enabled(self, tool: str) -> bool | None:
        if not self.extended:
            return False
        if self.tools is None:
            return True
        if self.f.user_sel is None:
            return None
        return any(self.f.user_sel.selects(e, tool) for e in self.tools)

    def l2_enabled(self, backend: str) -> bool | None:
        if self.tools is None:
            return True
        if self.f.user_sel is None:
            return None
        return any(self.f.user_sel.selects(e, backend) for e in self.tools)

    def step_enabled(self, upstream: str, stable: bool) -> bool | None:
        if not self.extended:
            return False
        if self.tools is None:
            return stable or self.unstable
        if self.f.step_sel is None:
            return None
        return any(self.f.step_sel.selects(e, upstream) for e in self.tools)

    # --- guard expressions ------------------------------------------------
    def _helper(self, name: str) -> list[str] | None:
        if name not in self._helpers:
            body = fn_body(self.f.src, name)
            self._helpers[name] = _or_terms(body) if body is not None else None
        return self._helpers[name]

    def eval_guard(self, expr: str, depth: int = 0) -> bool | None:
        if depth > 6:
            return None
        expr = " ".join(expr.split())
        m = re.fullmatch(r"(\w+)\s*\((.*)\)", expr)
        if not m:
            return None
        fn, argstr = m.group(1), m.group(2)
        lits = re.findall(r'"([^"]+)"', argstr)
        parts = [p.strip() for p in argstr.split(",") if p.strip()]

        if fn == "tool_enabled_for_tool_settings":
            return self.tool_enabled(lits[0]) if lits else None
        if fn == "l2_backend_enabled":
            return self.l2_enabled(lits[0]) if lits else None
        if fn == "extended_rustc_tool_is_default_step_for_tool_settings":
            if not lits or not parts or parts[-1] not in ("true", "false"):
                return None
            return self.step_enabled(lits[0], parts[-1] == "true")

        terms = self._helper(fn)  # an `a || b || c` wrapper helper
        if terms is None:
            return None
        result = False
        for t in terms:
            v = self.eval_guard(t, depth + 1) if "(" in t else self._ident(t)
            if v is None:
                return None
            result = result or v
        return result

    def _ident(self, name: str) -> bool | None:
        return {
            "ay_source_present": self.ay_present,
            "extended": self.extended,
            "unstable_features": self.unstable,
        }.get(name)

    # --- the answer -------------------------------------------------------
    @staticmethod
    def _pretty_gate(expr: str) -> str:
        """`fn(extended, tools, unstable, "x", false,)` -> `fn("x", stable=false)`."""
        e = " ".join(expr.split())
        m = re.fullmatch(r"(\w+)\s*\((.*)\)", e)
        if not m:
            return e
        fn, argstr = m.group(1), m.group(2)
        lits = re.findall(r'"([^"]+)"', argstr)
        parts = [p.strip() for p in argstr.split(",") if p.strip()]
        if not lits:
            return f"{fn}(..)"
        tail = f", stable={parts[-1]}" if parts and parts[-1] in ("true", "false") else ""
        return f'{fn}("{lits[0]}"{tail})'

    def gate_of(self, install: str) -> str:
        for b in self.f.sysroot_bins:
            if b.install == install:
                return (" AND ".join(self._pretty_gate(g) for g in b.guards)
                        if b.guards else "<unconditional>")
        return "<no install site>"

    def selected(self, install: str) -> bool | None:
        """Does this config select `install`, ignoring source availability?"""
        sites = [b for b in self.f.sysroot_bins if b.install == install]
        if not sites:
            return None
        unknown = False
        for b in sites:
            vals = [self.eval_guard(g) for g in b.guards]
            if any(v is None for v in vals):
                unknown = True
                continue
            if all(vals):
                return True
        return None if unknown else False

    def installs(self, root: Path, install: str) -> tuple[bool | None, str]:
        """(will this binary be in the sysroot, why)."""
        sel = self.selected(install)
        gate = self.gate_of(install)
        if sel is None:
            return None, f"gate not modellable: {gate}"
        if not sel:
            return False, f"not selected by [build] tools (gate: {gate})"
        man = self.f.source_manifests.get(install)
        if man and not (root / man).exists():
            return False, f"selected, but its source manifest is MISSING ({man})"
        return True, f"selected (gate: {gate})" + (
            f", source present ({man})" if man else ""
        )

    def all_install_names(self) -> list[str]:
        seen: list[str] = []
        for b in self.f.sysroot_bins:
            if b.install not in seen:
                seen.append(b.install)
        return sorted(seen)

    def known_entry_names(self) -> set[str]:
        """Every string a `[build] tools` entry could legitimately be."""
        known = set(self.all_install_names()) | set(self.f.gated_tools)
        known |= set(self.f.l2_backends) | set(self.f.dist_components)
        for tbl in (self.f.user_sel, self.f.step_sel):
            if tbl:
                known |= tbl.entries | tbl.targets
        for b in self.f.sysroot_bins:
            known.add(b.src)
        return known


# --------------------------------------------------------------------------
# CHECK 1 - submodule drift
# --------------------------------------------------------------------------
def check_submodules(root: Path, rep: Report) -> None:
    check = "1. SUBMODULE DRIFT"
    rc, out, err = run(["git", "submodule", "status"], cwd=root)
    if rc != 0:
        rep.add(WARN, check, "could not run `git submodule status`", [err.strip()[:200]])
        return

    drifted: list[str] = []
    uninit: list[str] = []
    conflicted: list[str] = []

    for line in out.splitlines():
        if not line.strip():
            continue
        prefix, rest = line[0], line[1:]
        parts = rest.split()
        if len(parts) < 2:
            continue
        sha, path = parts[0], parts[1]
        described = " ".join(parts[2:]).strip("()") if len(parts) > 2 else ""
        sub = root / path

        # `git submodule status` diffs the worktree against the INDEX, not HEAD.
        # `git add -A` on a drifted tree stages the stale gitlink and the `+`
        # silently disappears while the submodule is still weeks behind the
        # committed pin - which is exactly the shape of the E0599/E0432 hunt.
        # So the committed pin is compared explicitly, prefix or no prefix.
        pinned = ""
        prc, pout, _ = run(["git", "rev-parse", f"HEAD:{path}"], cwd=root)
        if prc == 0:
            pinned = pout.strip()
        # Only ask git about the submodule if it really is one. On an emptied or
        # never-initialised path `git -C <sub>` silently walks UP and answers
        # for the SUPERPROJECT, which reports a confident, wrong SHA/branch.
        initialised = (sub / ".git").exists()
        actual = ""
        if initialised:
            arc, aout, _ = run(["git", "rev-parse", "HEAD"], cwd=sub)
            if arc == 0:
                actual = aout.strip()
        staged_drift = bool(pinned and actual and actual != pinned and prefix == " ")

        if prefix == " " and not staged_drift:
            continue

        branch = "<not checked out>"
        if initialised:
            brc, bout, _ = run(["git", "symbolic-ref", "--short", "-q", "HEAD"], cwd=sub)
            if brc == 0:
                branch = bout.strip()
            else:
                drc, dout, _ = run(["git", "describe", "--all", "--always"], cwd=sub)
                branch = dout.strip() if drc == 0 else "(detached, undescribed)"

        detail = [
            f"module        : {path}",
            f"checked out   : {actual or '<none>' if not initialised else actual or sha}"
            f" ({described or 'n/a'})",
            f"parked on     : {branch}",
            f"pinned by repo: {pinned or '<unknown>'}  (HEAD:{path})",
        ]

        if staged_drift:
            drifted.append(path)
            rep.add(
                FAIL,
                check,
                f"{path} is off the COMMITTED pin, and the drift is STAGED "
                f"(git submodule status shows no `+`)",
                detail + [
                    "the stale gitlink is in the index, so `git submodule update`",
                    "alone would re-apply the STALE sha. Unstage it first.",
                ],
                [
                    f"git restore --staged -- {path}",
                    "git submodule update --init --recursive",
                ],
            )
        elif prefix == "+":
            drifted.append(path)
            rep.add(
                FAIL,
                check,
                f"{path} is AHEAD/BEHIND its pin (`+`) - stale APIs will look like source bugs",
                detail,
                ["git submodule update --init --recursive"],
            )
        elif prefix == "-":
            uninit.append(path)
            rep.add(
                FAIL,
                check,
                f"{path} is NOT INITIALISED (`-`) - its crates cannot build",
                detail,
                ["git submodule update --init --recursive"],
            )
        elif prefix == "U":
            conflicted.append(path)
            rep.add(
                FAIL,
                check,
                f"{path} has MERGE CONFLICTS (`U`) - resolve before any build",
                detail,
                [f"git -C {path} status", "# resolve conflicts, then:",
                 "git submodule update --init --recursive"],
            )

    # The measured trap: dirty tracked files inside a submodule make
    # `git submodule update` abort with "local changes would be overwritten",
    # so the wrong fix (cargo update) actively blocks the right one.
    for path in drifted + conflicted:
        sub = root / path
        if not (sub / ".git").exists():
            continue  # else git answers for the superproject
        drc, dout, _ = run(["git", "status", "--porcelain", "--untracked-files=no"], cwd=sub)
        if drc == 0 and dout.strip():
            # NB: porcelain lines start with the two status columns (' M path').
            # Stripping the whole blob first would eat the leading column and
            # shear the first character off every path.
            files = [ln[2:].strip() for ln in dout.splitlines() if ln.strip()][:8]
            rep.add(
                FAIL,
                check,
                f"{path} has LOCAL CHANGES that will BLOCK `git submodule update`",
                [f"dirty: {f}" for f in files]
                + ["('local changes to the following files would be overwritten')"],
                [
                    f"git -C {path} diff > /tmp/{Path(path).name}-local.patch   "
                    f"# keep a copy first",
                    f"git -C {path} checkout -- .",
                    "git submodule update --init --recursive",
                ],
            )

    # Even with zero drift, an uncommitted lockfile inside a submodule is a
    # loaded gun: the day drift appears, `git submodule update` refuses with
    # "local changes would be overwritten" and the correct fix is unavailable
    # until the edit is rescued. Surface it while it is still cheap.
    for line in out.splitlines():
        if not line.strip():
            continue
        parts = line[1:].split()
        if len(parts) < 2 or parts[1] in drifted + conflicted:
            continue
        path = parts[1]
        if not (root / path / ".git").exists():
            continue
        drc, dout, _ = run(["git", "status", "--porcelain", "--untracked-files=no",
                            "--", "*Cargo.lock"], cwd=root / path)
        if drc == 0 and dout.strip():
            files = [ln[2:].strip() for ln in dout.splitlines() if ln.strip()][:5]
            rep.add(
                WARN, check,
                f"{path} has UNCOMMITTED lockfile edits (no drift today, but they "
                f"will block the fix the day there is)",
                [f"dirty: {f}" for f in files]
                + ["these are unreviewed build inputs; commit or revert them"],
                [f"git -C {path} diff -- {files[0] if files else 'Cargo.lock'}"
                 "   # review, then commit in the submodule"],
            )

    if not (drifted or uninit or conflicted):
        n = len([ln for ln in out.splitlines() if ln.strip()])
        rep.add(INFO, check, f"all {n} submodules match their pinned gitlink SHA")


def check_bootstrap_submodule_policy(root: Path, cfg: dict, rep: Report) -> None:
    check = "1. SUBMODULE DRIFT"
    if (cfg.get("build") or {}).get("submodules") is False:
        rep.add(
            INFO,
            check,
            "bootstrap.toml sets `submodules = false` - x.py will NOT self-heal drift",
            ["submodule sync is entirely on you; this check is the only guard"],
        )


# --------------------------------------------------------------------------
# CHECK 2 - lockfile skew (strictly non-mutating)
# --------------------------------------------------------------------------
def discover_workspaces(root: Path, facts: BootstrapFacts, depth: int, all_ws: bool) -> list[Path]:
    """Build-relevant workspace roots, derived - never hardcoded.

    Three independent sources so the set cannot rot:
      * a shallow scan of the repo (the same `find -maxdepth 3` that found the
        13+ lockfiles by hand),
      * every submodule root declared in .gitmodules,
      * the nearest lock-bearing ancestor of every `path:` bootstrap builds.
    """
    found: set[Path] = set()

    # Only lockfiles git actually tracks are build inputs. Generated trees
    # (publish/.out/**, vendored tool fixtures) carry locks that nobody pins
    # and that no build ever resolves; auditing them is pure noise.
    tracked: set[Path] | None = None
    rc, out, _ = run(["git", "ls-files", "-z", "--", "*Cargo.lock"], cwd=root, timeout=60)
    if rc == 0:
        tracked = {(root / p).parent.resolve() for p in out.split("\0") if p}

    def scan(base: Path, max_depth: int) -> None:
        base_parts = len(base.parts)
        for dirpath, dirnames, filenames in os.walk(base):
            d = Path(dirpath)
            dirnames[:] = [x for x in dirnames if x not in PRUNE_DIRS]
            if len(d.parts) - base_parts >= max_depth:
                dirnames[:] = []
            if "Cargo.lock" in filenames and "Cargo.toml" in filenames:
                found.add(d)

    scan(root, 10**6 if all_ws else depth)

    gm = root / ".gitmodules"
    if gm.exists():
        for path in re.findall(r"^\s*path\s*=\s*(.+)$", gm.read_text(errors="replace"), re.M):
            sub = root / path.strip()
            if (sub / "Cargo.lock").exists() and (sub / "Cargo.toml").exists():
                found.add(sub)

    for tp in facts.tool_paths:
        cur = (root / tp).resolve()
        while cur != root and root in cur.parents:
            if (cur / "Cargo.lock").exists() and (cur / "Cargo.toml").exists():
                found.add(cur)
                break
            cur = cur.parent

    if tracked is not None:
        # Submodule locks are tracked inside the submodule, not by the
        # superproject, so keep anything git-ls-files knows about in EITHER.
        keep = set()
        for ws in found:
            if ws.resolve() in tracked:
                keep.add(ws)
                continue
            srn, sout, _ = run(["git", "ls-files", "--error-unmatch", "Cargo.lock"],
                               cwd=ws, timeout=20)
            if srn == 0:
                keep.add(ws)
        found = keep

    return sorted(found)


_BUILD_CRITICAL: dict[Path, set[Path]] = {}


def build_critical_workspaces(root: Path) -> set[Path]:
    """Workspaces bootstrap actually resolves - the only ones that can fail a build.

    Every bootstrap step names the crate it builds by PATH (`path: "..."` on a
    ToolBuild, `.path("library")` on a ShouldRun). Mapping each of those to its
    nearest lock-bearing ancestor derives, from bootstrap's own source, the set
    of lockfiles a build will hand to cargo with `--locked`.

    Everything else in the tree is skew that is real but INERT: no bootstrap
    step ever resolves `first-party/clean/bench-runner`, so its lock cannot
    fail `x.py dist` no matter how stale it is. Reporting those at FAIL is the
    cry-wolf failure mode - the day a genuine one appears it is item seven in a
    list of six that never mattered, and the whole report gets skipped.
    """
    cached = _BUILD_CRITICAL.get(root)
    if cached is not None:
        return cached
    lits: set[str] = set()
    src_dir = root / "src" / "bootstrap" / "src"
    if src_dir.is_dir():
        for p in src_dir.rglob("*.rs"):
            if p.name.endswith("tests.rs") or f"{os.sep}tests{os.sep}" in str(p):
                continue
            try:
                s = strip_line_comments(p.read_text(errors="replace"))
            except OSError:
                continue
            lits |= set(re.findall(r'\bpath:\s*"([^"]+)"', s))
            lits |= set(re.findall(r'\.path\(\s*"([^"]+)"\s*\)', s))
            for grp in re.findall(r"\.paths\(&\[([^\]]*)\]", s):
                lits |= set(re.findall(r'"([^"]+)"', grp))

    crit: set[Path] = set()
    for tp in lits:
        try:
            cur = (root / tp).resolve()
        except (ValueError, OSError):
            continue
        if root != cur and root not in cur.parents:
            continue
        while True:
            if (cur / "Cargo.lock").exists() and (cur / "Cargo.toml").exists():
                crit.add(cur)
                break
            if cur == root or cur.parent == cur:
                break
            cur = cur.parent
    _BUILD_CRITICAL[root] = crit
    return crit


def lock_severity(root: Path, ws: Path) -> tuple[str, str]:
    """(severity, why) for skew in `ws`."""
    if ws.resolve() in build_critical_workspaces(root):
        return FAIL, "a bootstrap step resolves this workspace with --locked"
    return WARN, ("no bootstrap step names this workspace, so its lock cannot "
                  "fail a build - real skew, but inert")


def parse_git_source(source: str) -> tuple[str, str | None]:
    """'git+URL?rev=R#SHA' -> (URL, R)."""
    s = source[len("git+"):]
    s = s.split("#", 1)[0]
    if "?" in s:
        url, query = s.split("?", 1)
        for kv in query.split("&"):
            if kv.startswith("rev="):
                return url, kv[4:]
        return url, None
    return s, None


def norm_url(u: str) -> str:
    return u[:-4] if u.endswith(".git") else u


def canon_git(url: str) -> str:
    """Collapse the spellings of one git remote to a single key.

    `[patch]` tables in this tree key the same repo five ways (https, https+.git,
    ssh://git@, ssh://git@host:22/, ...). Comparing raw strings would make the
    patch lookup miss and resurrect the false positives it exists to suppress.
    """
    u = url.strip()
    if u.startswith("git+"):
        u = u[4:]
    u = re.sub(r"^[a-z0-9+.-]+://", "", u, flags=re.I)
    u = re.sub(r"^[^/@]+@", "", u)
    u = u.replace(":22/", "/", 1)
    u = u.replace(":", "/", 1) if "/" not in u.split(":", 1)[0] else u
    if u.endswith(".git"):
        u = u[:-4]
    return u.rstrip("/").lower()


def collect_patches(root_man: dict | None) -> dict[str, set[str]]:
    """canonical-remote -> {crate names redirected away from it}."""
    out: dict[str, set[str]] = {}
    for src, tbl in ((root_man or {}).get("patch") or {}).items():
        if not isinstance(tbl, dict):
            continue
        out.setdefault(canon_git(src), set()).update(tbl.keys())
    return out


def owning_workspace_is(candidate: Path, ws: Path) -> bool:
    """True iff `candidate` is governed by workspace root `ws`.

    A path dependency that lands inside ANOTHER workspace (its own `[workspace]`
    table, or an explicit `package.workspace =`) is not a member here. Without
    this, the root workspace's closure swallowed every first-party/* member and
    reported all of them against the wrong lockfile.
    """
    cur = candidate
    while True:
        man = cur / "Cargo.toml"
        if man.exists():
            m, _ = load_toml(man)
            if m is not None:
                pw = (m.get("package") or {}).get("workspace")
                if isinstance(pw, str):
                    try:
                        return (cur / pw).resolve() == ws
                    except (ValueError, OSError):
                        return False
                if "workspace" in m and cur != candidate:
                    return cur == ws
        if cur == ws or cur.parent == cur:
            return cur == ws
        cur = cur.parent


def iter_dep_specs(man: dict):
    for t in DEP_TABLES:
        for name, spec in (man.get(t) or {}).items():
            yield name, spec
    for _cfg, tbl in (man.get("target") or {}).items():
        if isinstance(tbl, dict):
            for t in DEP_TABLES:
                for name, spec in (tbl.get(t) or {}).items():
                    yield name, spec
    for name, spec in ((man.get("workspace") or {}).get("dependencies") or {}).items():
        yield name, spec


def workspace_manifests(ws: Path) -> list[Path]:
    """Manifests of the ACTUAL members of this workspace.

    Membership is cargo's rule - `[workspace] members` globs minus `exclude`,
    plus the transitive closure of intra-workspace `path` dependencies - not
    "every Cargo.toml under here". The difference is not cosmetic: a naive walk
    sweeps up cargo's own test fixtures (`foo`, `bar`, `enclave`, ...) and
    `fuzz/` sub-workspaces, none of which appear in the lock, and reports each
    as skew. That is a checker nobody would keep running.
    """
    ws = ws.resolve()
    memo = _WS_MANIFESTS.get(ws)
    if memo is not None:
        return memo
    result = _workspace_manifests(ws)
    _WS_MANIFESTS[ws] = result
    return result


_WS_MANIFESTS: dict[Path, list[Path]] = {}


def _workspace_manifests(ws: Path) -> list[Path]:
    root_man, _ = load_toml(ws / "Cargo.toml")
    if root_man is None:
        return []
    w = root_man.get("workspace") or {}

    excluded: set[Path] = set()
    for pat in (w.get("exclude") or []):
        try:
            excluded.update(p.resolve() for p in ws.glob(pat))
        except (ValueError, OSError):
            continue

    members: set[Path] = set()
    if "package" in root_man:
        members.add(ws)
    for pat in (w.get("members") or []):
        try:
            for p in ws.glob(pat):
                if p.is_dir() and (p / "Cargo.toml").exists():
                    members.add(p.resolve())
        except (ValueError, OSError):
            continue

    # cargo pulls path dependencies of members into the workspace too.
    queue, seen = list(members), set()
    while queue:
        m = queue.pop()
        if m in seen:
            continue
        seen.add(m)
        man, _ = load_toml(m / "Cargo.toml")
        if man is None:
            continue
        for _name, spec in iter_dep_specs(man):
            if not isinstance(spec, dict) or "path" not in spec:
                continue
            try:
                t = (m / spec["path"]).resolve()
            except (ValueError, OSError):
                continue
            if t in excluded or t in members or not (t / "Cargo.toml").exists():
                continue
            if ws != t and ws not in t.parents:
                continue
            if (t / "Cargo.lock").exists():
                continue  # its own workspace
            tm, _ = load_toml(t / "Cargo.toml")
            if tm is not None and "workspace" in tm and "package" not in tm:
                continue
            if not owning_workspace_is(t, ws):
                continue
            members.add(t)
            queue.append(t)

    return sorted((m / "Cargo.toml") for m in members if m not in excluded)


def check_lockfiles_fast(root: Path, workspaces: list[Path], rep: Report) -> None:
    check = "2. LOCKFILE SKEW (non-mutating)"
    clean = 0

    for ws in workspaces:
        wsname = rel(root, ws) or "."
        lock, lerr = load_toml(ws / "Cargo.lock")
        if lock is None:
            rep.add(FAIL, check, f"{wsname}: Cargo.lock does not parse", [lerr or ""],
                    [f"git -C {root} diff -- {wsname}/Cargo.lock"])
            continue

        pkgs = lock.get("package") or []
        lock_git: set[tuple[str, str]] = set()
        for p in pkgs:
            src = p.get("source") or ""
            if src.startswith("git+"):
                u, r = parse_git_source(src)
                if r:
                    lock_git.add((canon_git(u), r))
        lock_names = {p.get("name") for p in pkgs}
        lock_local: dict[str, set[str]] = {}
        for p in pkgs:
            if "source" not in p:
                lock_local.setdefault(p.get("name", ""), set()).add(p.get("version", ""))

        git_bad: dict[tuple[str, str], set[str]] = {}
        ver_bad: list[tuple[str, str, str]] = []
        missing_dep: dict[str, set[str]] = {}
        floating: set[str] = set()
        ws_deps = {}

        manifests = workspace_manifests(ws)
        rman, _ = load_toml(ws / "Cargo.toml")
        if rman:
            ws_deps = (rman.get("workspace") or {}).get("dependencies") or {}
        # A `[patch]`ed crate is resolved from a local path, so the lock holds NO
        # git source for it. Comparing its manifest rev against the lock's git
        # sources is guaranteed to "find skew" that does not exist.
        patches = collect_patches(rman)

        for mp in manifests:
            man, merr = load_toml(mp)
            if man is None:
                rep.add(FAIL, check, f"{wsname}: {rel(ws, mp)} does not parse", [merr or ""], [])
                continue

            pkg = man.get("package") or {}
            name, version = pkg.get("name"), pkg.get("version")
            if isinstance(name, str) and isinstance(version, str):
                have = lock_local.get(name)
                if have is None:
                    if name in lock_names:
                        pass  # same name from a registry/git source; not conclusive
                    else:
                        ver_bad.append((name, version, "<absent from lock>"))
                elif version not in have:
                    ver_bad.append((name, version, "/".join(sorted(have))))

            for dname, spec in iter_dep_specs(man):
                if not isinstance(spec, dict):
                    real = dname
                    if real not in lock_names:
                        missing_dep.setdefault(real, set()).add(rel(ws, mp))
                    continue
                if spec.get("workspace") is True:
                    spec = ws_deps.get(dname, {}) if isinstance(ws_deps.get(dname), dict) else {}
                real = spec.get("package", dname) if isinstance(spec, dict) else dname
                if isinstance(spec, dict) and "git" in spec:
                    url = canon_git(spec["git"])
                    revv = spec.get("rev")
                    if real in patches.get(url, set()):
                        continue  # redirected to a local path by [patch]
                    if revv:
                        if (url, revv) not in lock_git:
                            git_bad.setdefault((url, revv), set()).add(real)
                    else:
                        floating.add(f"{real} ({spec['git']} @ "
                                     f"{spec.get('branch') or spec.get('tag') or 'default'})")
                if isinstance(real, str) and real and real not in lock_names \
                        and not (isinstance(spec, dict) and spec.get("path")):
                    missing_dep.setdefault(real, set()).add(rel(ws, mp))

        skewed = bool(git_bad or ver_bad or missing_dep)
        if not skewed:
            clean += 1
            continue

        detail: list[str] = []
        fixes: list[str] = []
        touched: set[str] = set()

        for (url, revv), names in sorted(git_bad.items()):
            have = sorted({r for u, r in lock_git if u == url}) or ["<none>"]
            detail.append(f"git pin  : {url}")
            detail.append(f"  manifest wants rev {revv}")
            detail.append(f"  lock has rev       {', '.join(h[:16] + '...' for h in have)}")
            detail.append(f"  crates             {', '.join(sorted(names)[:6])}"
                          + (" ..." if len(names) > 6 else ""))
            touched.update(names)
        for name, want, have in ver_bad[:8]:
            detail.append(f"version  : {name} manifest={want} lock={have}")
            touched.add(name)
        for name, where in sorted(missing_dep.items())[:8]:
            detail.append(f"absent   : `{name}` required by {sorted(where)[0]} but not in lock")
            touched.add(name)
        if floating:
            detail.append(f"note     : {len(floating)} unpinned git dep(s), e.g. "
                          f"{sorted(floating)[0]}")

        specs = " ".join(f"-p {n}" for n in sorted(touched)[:12])
        fixes.append(
            f"targo update --manifest-path {wsname}/Cargo.toml {specs}".strip()
        )
        if ver_bad:
            fixes.append(f"targo update --workspace --manifest-path {wsname}/Cargo.toml")
        fixes.append("# NEVER a bare `targo update` / `cargo update`: it downgraded ay "
                     "0.4.0->0.3.0 and manufactured a futures-core conflict.")

        sev, why = lock_severity(root, ws)
        rep.add(sev, check,
                f"{wsname}: lock is behind its manifests "
                f"({'--locked WILL fail' if sev == FAIL else 'not on any build path'})",
                detail + [why], fixes)

    rep.add(INFO, check,
            f"{clean}/{len(workspaces)} build-relevant workspaces textually consistent",
            [f"probed: {', '.join(rel(root, w) or '.' for w in workspaces[:12])}"
             + (" ..." if len(workspaces) > 12 else "")])


# --------------------------------------------------------------------------
# CHECK 2a - GIT-PIN CASCADE  (a SUBMODULE's manifest vs a PARENT's lockfile)
#
# WHY THIS EXISTS - the failure it was written against, measured:
#
#     $ sh tools/preflight.sh --no-color
#         OK   0 blocking, 1 warning(s)   [2.1s]  cleared for x.py.
#     $ python3 x.py build --stage 2
#       error: cannot update the lock file targo-trust/Cargo.lock
#              because --locked was passed to prevent this
#       Build completed unsuccessfully in 0:02:11
#
# A checker that clears a build which then dies, two minutes later, on the
# exact failure class the checker exists to catch is WORSE than no checker: it
# teaches people to ignore it, and then it is ignored for the run that finds
# something true. So: the two reasons it was blind, both confirmed by reading
# the code rather than guessing.
#
#   (1) The resolver-backed (deep) tier is gated to `dist`/`install` in x.py,
#       so a plain `x.py build` only ever ran the fast textual tier. That
#       gating is CORRECT and stays - a 20s tax on the edit/build loop is how
#       TRUST_SKIP_PREFLIGHT=1 ends up in a shell profile. The fast tier has to
#       grow the specific probe instead.
#
#   (2) The fast tier compared each manifest's pinned git revs against ITS OWN
#       workspace's lock - and `workspace_manifests()` deliberately stops at
#       the workspace boundary (`ws not in t.parents`) and at any directory
#       carrying its own Cargo.lock. Measured on this tree, that made the
#       manifest closure of `targo-trust` exactly ONE file: its own Cargo.toml.
#       Every crate it actually builds lives in `../crates/*` and
#       `../first-party/*`, so the moving part - a SUBMODULE manifest feeding a
#       DIFFERENT workspace's lock - was outside the compared set by
#       construction. That is the cascade, and nothing modelled it.
#
# The real event: `first-party/trust-ir` moved to a rev whose
# crates/trust-ir-build/Cargo.toml advanced its `clean` pin (88f9c2c3 ->
# 02e0aa0f), targo-trust's lock still had no such git source, and
# targo-trust/Cargo.toml only reaches that manifest through
# `../crates/trust-bmc` -> `trust-ir-build = { workspace = true }`.
#
# A THIRD blindfold, which the first two hid: targo-trust DOES carry
# `[patch."https://github.com/alabsystems/clean.git"] clean-kernel = { path
# = ... }`, and the fast tier treats "name appears in a patch table" as proof
# the dep resolves locally. It does not. A `[patch]` only replaces a source if
# the replacement's VERSION also satisfies the requirement - the local
# submodule is clean-kernel 1.2.0, the pin wants "1.3.0", so cargo fell back to
# the git source and the entry the lock lacked was real. `patch_serves()`
# below is version-aware for exactly that reason.
#
# COST. This probe re-walks path dependencies ACROSS workspace and submodule
# boundaries, which sounds expensive and is not: the walk is pure TOML parsing
# of files the run already touches, and `load_toml` is memoized, so the tier
# stays inside its ~2s budget. No subprocess, no resolver, no network.
# --------------------------------------------------------------------------
_WS_ROOT: dict[Path, Path | None] = {}


def nearest_workspace_root(d: Path) -> Path | None:
    """The workspace root whose `[workspace.*]` tables crate `d` inherits.

    Needed because `{ workspace = true }` inside a SUBMODULE member inherits
    from that submodule's root, not from whatever workspace happens to be
    building it. Resolving it against the wrong root is how
    `trust-ir-build = { workspace = true }` (in crates/trust-bmc) silently
    resolved to nothing and took the `clean` pin with it.
    """
    if d in _WS_ROOT:
        return _WS_ROOT[d]
    res: Path | None = None
    cur = d
    while True:
        man, _ = load_toml(cur / "Cargo.toml")
        if man is not None:
            pw = (man.get("package") or {}).get("workspace")
            if isinstance(pw, str):
                try:
                    res = (cur / pw).resolve()
                except (ValueError, OSError):
                    res = None
                break
            if "workspace" in man:
                res = cur
                break
        if cur.parent == cur:
            break
        cur = cur.parent
    _WS_ROOT[d] = res
    return res


def inherit_dep(d: Path, name: str, spec):
    """`(base dir, resolved spec)` with `{ workspace = true }` expanded.

    The base dir matters: an inherited `path` is relative to the WORKSPACE
    ROOT, not to the member that wrote `workspace = true`.
    """
    if not (isinstance(spec, dict) and spec.get("workspace") is True):
        return d, spec
    wr = nearest_workspace_root(d)
    if wr is None:
        return d, {}
    man, _ = load_toml(wr / "Cargo.toml")
    inh = (((man or {}).get("workspace") or {}).get("dependencies") or {}).get(name)
    if isinstance(inh, str):
        inh = {"version": inh}
    if not isinstance(inh, dict):
        return d, {}
    merged = dict(inh)
    if spec.get("optional") is True:  # the member may narrow, never widen
        merged["optional"] = True
    return wr, merged


def iter_graph_dep_specs(man: dict, with_dev: bool):
    """Dependency tables that put a crate IN THE RESOLVED GRAPH.

    `dev-dependencies` count only for workspace MEMBERS: a member's dev-deps
    are in the lock, a transitively-reached outside crate's are not, and
    walking those would invent findings for crates no build ever resolves.
    """
    tables = ["dependencies", "build-dependencies"]
    if with_dev:
        tables.append("dev-dependencies")
    for t in tables:
        for name, spec in (man.get(t) or {}).items():
            yield name, spec
    for _cfg, tbl in (man.get("target") or {}).items():
        if isinstance(tbl, dict):
            for t in tables:
                for name, spec in (tbl.get(t) or {}).items():
                    yield name, spec


_GRAPH: dict[Path, list[tuple[Path, bool]]] = {}
GRAPH_CAP = 4000  # a runaway walk must degrade to "less coverage", never to a hang


def graph_manifests(ws: Path) -> list[tuple[Path, bool]]:
    """`(crate dir, is-a-member)` for every crate ws's resolver graph reaches.

    Deliberately the OPPOSITE of `workspace_manifests()` on the two axes that
    made the cascade invisible: it follows `path` dependencies OUT of the
    workspace directory and INTO directories that carry their own Cargo.lock
    (i.e. submodules). Those crates are still resolved against THIS lock -
    their own lockfile is not consulted by this build at all - so their pins
    are this lock's problem.

    Optional path deps are not followed: they are absent from the graph until a
    feature turns them on, so their pins are legitimately absent from the lock.
    """
    ws = ws.resolve()
    memo = _GRAPH.get(ws)
    if memo is not None:
        return memo
    seen: set[Path] = set()
    out: list[tuple[Path, bool]] = []
    queue: list[tuple[Path, bool]] = [(Path(m).parent, True) for m in workspace_manifests(ws)]
    while queue and len(out) < GRAPH_CAP:
        d, is_member = queue.pop()
        if d in seen:
            continue
        seen.add(d)
        man, _ = load_toml(d / "Cargo.toml")
        if man is None:
            continue
        out.append((d, is_member))
        for name, spec in iter_graph_dep_specs(man, with_dev=is_member):
            base, rspec = inherit_dep(d, name, spec)
            if not isinstance(rspec, dict) or "path" not in rspec:
                continue
            if rspec.get("optional") is True:
                continue
            try:
                t = (base / rspec["path"]).resolve()
            except (ValueError, OSError):
                continue
            if (t / "Cargo.toml").exists():
                queue.append((t, False))
    _GRAPH[ws] = out
    return out


def crate_version(d: Path) -> str | None:
    """`package.version`, following `version.workspace = true`."""
    man, _ = load_toml(d / "Cargo.toml")
    if man is None:
        return None
    v = (man.get("package") or {}).get("version")
    if isinstance(v, str):
        return v
    if isinstance(v, dict) and v.get("workspace") is True:
        wr = nearest_workspace_root(d)
        if wr is None:
            return None
        wm, _ = load_toml(wr / "Cargo.toml")
        wv = (((wm or {}).get("workspace") or {}).get("package") or {}).get("version")
        return wv if isinstance(wv, str) else None
    return None


def _semver(v: str) -> tuple[int, int, int] | None:
    """`1.2.3` -> (1,2,3). Anything pre-release or unparseable -> None."""
    s = v.strip()
    if "-" in s.split("+", 1)[0]:
        return None  # pre-release ordering is subtle; refuse rather than guess
    core = s.split("+", 1)[0]
    parts = core.split(".")
    if not 1 <= len(parts) <= 3:
        return None
    try:
        nums = [int(p) for p in parts]
    except ValueError:
        return None
    while len(nums) < 3:
        nums.append(0)
    return (nums[0], nums[1], nums[2])


def _caret_upper(b: tuple[int, int, int], n: int) -> tuple[int, int, int]:
    major, minor, patch = b
    if major > 0 or n == 1:
        return (major + 1, 0, 0)
    if minor > 0 or n == 2:
        return (0, minor + 1, 0)
    return (0, 0, patch + 1)


def _tilde_upper(b: tuple[int, int, int], n: int) -> tuple[int, int, int]:
    major, minor, _patch = b
    if n == 1:
        return (major + 1, 0, 0)
    return (major, minor + 1, 0)


def req_allows(req, ver: str) -> bool:
    """Does `ver` satisfy cargo requirement `req`?

    UNPARSEABLE INPUT RETURNS True, on purpose and in one direction only. The
    single caller uses this to SUPPRESS a finding ("can this [patch] actually
    serve this dependency?"), so "not sure" has to mean "stay quiet", never
    "accuse". Every wrong answer this can give is a missed finding, which is
    the status quo, rather than a false FAIL, which is what gets a checker
    switched off.
    """
    v = _semver(ver)
    if v is None or not isinstance(req, str):
        return True
    for clause in req.split(","):
        c = clause.strip()
        if not c or c == "*":
            continue
        m = re.match(r"^(\^|~|>=|<=|=|>|<)?\s*v?(\d+)(?:\.(\d+))?(?:\.(\d+))?", c)
        if not m:
            return True
        op = m.group(1) or "^"
        given = [g for g in (m.group(2), m.group(3), m.group(4)) if g is not None]
        n = len(given)
        nums = [int(g) for g in given] + [0] * (3 - n)
        base = (nums[0], nums[1], nums[2])
        if op == "^":
            if not (base <= v < _caret_upper(base, n)):
                return False
        elif op == "~":
            if not (base <= v < _tilde_upper(base, n)):
                return False
        elif op == "=":
            if v[:n] != base[:n]:
                return False
        elif op == ">=":
            if v < base:
                return False
        elif op == ">":
            if v <= base:
                return False
        elif op == "<=":
            if v > base:
                return False
        elif op == "<":
            if v >= base:
                return False
        else:
            return True
    return True


def patch_serves(ws: Path, url: str, name: str, req, lock_local: dict[str, set[str]]) -> bool:
    """Would ws's `[patch]` table ACTUALLY replace this git dependency?

    "The name appears in a patch table" is not the same statement, and the
    difference is the whole bug: targo-trust patches `clean-kernel` away from
    clean.git to a local 1.2.0 checkout, while the pin that skewed the lock
    wanted "1.3.0". Cargo declines the patch and resolves from git; a
    patch-blind check declares the dependency local and says nothing.
    """
    rman, _ = load_toml(ws / "Cargo.toml")
    entry = None
    for src, tbl in ((rman or {}).get("patch") or {}).items():
        if isinstance(tbl, dict) and canon_git(src) == url and name in tbl:
            entry = tbl[name]
            break
    if entry is None:
        return False
    # The LOCK settles it better than any re-derivation can: a patched name
    # already present as a source-less (path) package at a version the
    # requirement accepts is a recording of the patch having resolved. Without
    # this, first-party/trust-ir gets accused - it patches clean-kernel to a
    # sibling checkout and its lock duly says `clean-kernel 1.3.0 <local>`,
    # while the superproject's `first-party/clean` submodule sits at 1.2.0. The
    # pin is absent from that lock for a legitimate reason, and reporting it as
    # cascade skew would be a confidently wrong diagnosis - the exact thing
    # that trains people to skip the report.
    if isinstance(req, str):
        for have in lock_local.get(name, ()):
            if req_allows(req, have):
                return True
    if not isinstance(entry, dict) or not isinstance(req, str):
        return True  # no version requirement to fail: any replacement serves
    p = entry.get("path")
    if not isinstance(p, str):
        return True  # patched to another git/registry source; not this check's business
    try:
        target = (ws / p).resolve()
    except (ValueError, OSError):
        return True
    have = crate_version(target)
    if have is None:
        return True
    return req_allows(req, have)


def check_git_pin_cascade(root: Path, workspaces: list[Path], rep: Report) -> None:
    check = "2a. GIT-PIN CASCADE (submodule manifest -> parent lock)"
    probed = 0
    reached = 0

    for ws in workspaces:
        wsname = rel(root, ws) or "."
        lock, _ = load_toml(ws / "Cargo.lock")
        if lock is None:
            continue  # already a FAIL from the fast tier; do not double-report
        lock_git: set[tuple[str, str]] = set()
        lock_local: dict[str, set[str]] = {}
        for p in lock.get("package") or []:
            src = p.get("source") or ""
            if src.startswith("git+"):
                u, r = parse_git_source(src)
                if r:
                    lock_git.add((canon_git(u), r))
            elif "source" not in p:
                lock_local.setdefault(p.get("name", ""), set()).add(p.get("version", ""))

        rman, _ = load_toml(ws / "Cargo.toml")
        patches = collect_patches(rman)
        members = {Path(m).parent for m in workspace_manifests(ws)}

        graph = graph_manifests(ws)
        probed += 1
        reached += len(graph)

        # (url, rev) -> {(crate, declaring dir, from-outside-the-workspace)}
        bad: dict[tuple[str, str], set[tuple[str, str, bool]]] = {}
        for d, is_member in graph:
            man, _ = load_toml(d / "Cargo.toml")
            if man is None:
                continue
            for name, spec in iter_graph_dep_specs(man, with_dev=is_member):
                base, rspec = inherit_dep(d, name, spec)
                if not isinstance(rspec, dict) or "git" not in rspec:
                    continue
                if rspec.get("optional") is True:
                    continue
                revv = rspec.get("rev")
                if not revv:
                    continue  # branch/tag: no rev to compare, already noted as floating
                real = rspec.get("package", name)
                if not isinstance(real, str):
                    continue
                url = canon_git(rspec["git"])
                if (url, revv) in lock_git:
                    continue
                # Anything the FAST tier already reports stays its finding. It
                # flags member-declared pins unless the name is patched, so the
                # only member pins left for this probe are the patch-suppressed
                # ones - precisely the case the fast tier gets wrong.
                outside = d not in members
                if not outside and real not in patches.get(url, set()):
                    continue
                if patch_serves(ws, url, real, rspec.get("version"), lock_local):
                    continue
                bad.setdefault((url, revv), set()).add((real, rel(root, d), outside))

        if not bad:
            continue

        detail: list[str] = []
        cascade = False
        stale = False
        for (url, revv), who in sorted(bad.items()):
            have = sorted({r for u, r in lock_git if u == url})
            stale = stale or bool(have)
            detail.append(f"git pin  : {url}")
            detail.append(f"  a manifest IN THIS GRAPH pins rev {revv}")
            detail.append("  this lock has            "
                          + (", ".join(h[:16] + "..." for h in have) if have
                             else "NO git source for that remote at all"))
            for crate, where, outside in sorted(who)[:6]:
                mark = "OUTSIDE this workspace" if outside else "patched, but the patch " \
                                                               "cannot serve this version"
                detail.append(f"  {crate}: declared by {where}/Cargo.toml  ({mark})")
                cascade = cascade or outside

        sev, why = lock_severity(root, ws)
        detail.append(why)
        if cascade:
            detail.append("this is the submodule-rev -> parent-lock cascade: the manifest "
                          "that moved is NOT a member of this workspace, so comparing this "
                          "workspace against its own members can never see it.")

        what = ("records a STALE rev for" if stale else "has NO entry for")
        rep.add(sev, check,
                f"{wsname}: lock {what} a git pin in its dependency GRAPH "
                f"({'--locked WILL fail' if sev == FAIL else 'not on any build path'})",
                detail,
                [f"targo metadata --manifest-path {wsname}/Cargo.toml --format-version 1 "
                 f">/dev/null   # MINIMAL resolve: writes only the moved revs",
                 f"git -C {root} diff --stat -- {wsname}/Cargo.lock"
                 f"   # CONFIRM it is minimal: git revs only, no version changes, nothing removed",
                 "# NEVER a bare `targo update` / `cargo update`: it downgraded ay "
                 "0.4.0->0.3.0 and manufactured a futures-core conflict."])

    rep.add(INFO, check,
            f"{probed} workspace(s) probed across {reached} graph manifests "
            f"(path deps followed THROUGH workspace and submodule boundaries)")


# --------------------------------------------------------------------------
# deep-tier result cache
#
# The deep probe is authoritative and expensive: 13-35s on this tree against
# ~2s for the fast tier, and it needs the network. Paying that on every
# `x.py build` is how `TRUST_SKIP_PREFLIGHT=1` ends up exported in a shell
# profile, at which point the checker protects nothing at all. So the verdict
# is cached against the exact inputs that determine it - each lockfile's
# CONTENT hash plus the size+mtime of every member manifest - and a hit costs
# a few hundred stat(2)s.
#
# Two deliberate restrictions:
#   * INCONCLUSIVE results (cold registry, no network) are never cached. They
#     are a property of the moment, not of the tree, and a sticky one would
#     turn a transient offline run into permanent blindness.
#   * the cache lives under build/ (gitignored, wiped by `x.py clean`), never
#     in the source tree. This file does not mutate the working tree.
# --------------------------------------------------------------------------
# v2: the key used to cover only workspace_manifests(ws) - the MEMBER manifests.
# That is the same blind spot check 2a exists to close, sitting in the caching
# layer: targo-trust has exactly one member manifest, so a submodule advancing
# its `clean` pin left a cached "clean" verdict fully VALID, and the next
# `x.py build` (which runs --deep-if-cached) would have replayed it. The key now
# covers every manifest in the resolver GRAPH, which is what the verdict is
# actually about. Costs nothing: check 2a already memoized that walk this run.
DEEP_CACHE_VERSION = 2


def _deep_cache_path(root: Path) -> Path:
    return root / "build" / "preflight-deep-cache.json"


def _deep_cache_key(ws: Path, targo: str) -> str:
    h = hashlib.sha256()
    h.update(f"v{DEEP_CACHE_VERSION}\0{targo}\0".encode())
    try:
        h.update(hashlib.sha256((ws / "Cargo.lock").read_bytes()).digest())
        if targo:
            st = Path(targo).stat()
            h.update(f"{st.st_size}:{st.st_mtime_ns}\0".encode())
    except OSError:
        return ""
    for d, _is_member in sorted(graph_manifests(ws)):
        mp = d / "Cargo.toml"
        try:
            ms = mp.stat()
        except OSError:
            return ""
        h.update(f"{mp}\0{ms.st_size}\0{ms.st_mtime_ns}\0".encode())
    return h.hexdigest()


def load_deep_cache(root: Path) -> dict:
    try:
        with _deep_cache_path(root).open() as fh:
            d = json.load(fh)
        return d if isinstance(d, dict) else {}
    except Exception:
        return {}


def save_deep_cache(root: Path, cache: dict) -> None:
    try:
        p = _deep_cache_path(root)
        p.parent.mkdir(parents=True, exist_ok=True)
        tmp = p.with_name(p.name + f".tmp{os.getpid()}")
        tmp.write_text(json.dumps(cache, sort_keys=True))
        os.replace(tmp, p)
    except Exception:
        pass  # a cache we cannot write is never a reason to fail a preflight


def check_lockfiles_deep(
    root: Path, workspaces: list[Path], rep: Report, targo: str, timeout: int, jobs: int,
    cached_only: bool = False,
) -> None:
    check = "2b. LOCKFILE SKEW (deep, `metadata --locked`)"
    if not targo:
        rep.add(WARN, check, "no targo binary found; deep probe skipped",
                ["a stage0-sysroot targo always exists mid-build:",
                 "build/<host>/stage0-sysroot/bin/targo"],
                ["tools/preflight.sh --deep --targo /path/to/targo"])
        return

    cache = load_deep_cache(root)
    keys = {ws: _deep_cache_key(ws, targo) for ws in workspaces}
    hits: dict[Path, dict] = {}
    todo: list[Path] = []
    for ws in workspaces:
        ent = cache.get(rel(root, ws) or ".")
        if (keys[ws] and isinstance(ent, dict) and ent.get("key") == keys[ws]
                and ent.get("verdict") in ("clean", "skew")):
            hits[ws] = ent
        else:
            todo.append(ws)

    skipped = 0
    if cached_only:
        # `--deep-if-cached`: reuse deep verdicts already paid for and still
        # valid; never spend a second earning new ones. This is what lets an
        # ordinary `x.py build` inherit resolver-grade coverage for free once
        # `x.py dist` (or a manual `--deep`) has warmed the cache.
        skipped = len(todo)
        todo = []

    for ws, ent in sorted(hits.items()):
        if ent.get("verdict") != "skew":
            continue
        wsname = rel(root, ws) or "."
        sev, why = lock_severity(root, ws)
        rep.add(sev, check,
                f"{wsname}: resolver CONFIRMS the lock must change  [cached verdict]",
                [str(ent.get("msg", ""))[:200], why,
                 "cached: lockfile content and every member manifest are unchanged",
                 "since the probe that produced this. Re-run with --deep to re-probe."],
                [f"targo update --manifest-path {wsname}/Cargo.toml -p <only-the-moved-crate>",
                 "# identify it from the error above; do not re-resolve the whole graph"])

    cached_clean = sum(1 for e in hits.values() if e.get("verdict") == "clean")
    rep.add(INFO, check,
            f"deep tier: {len(hits)} cached ({cached_clean} clean, "
            f"{len(hits) - cached_clean} skewed), {len(todo)} probed, {skipped} not probed")
    if skipped and not hits:
        rep.add(INFO, check, "no cached deep verdicts yet for this tree",
                ["the fast tier still ran; the resolver-backed tier has nothing cached"],
                ["tools/preflight.sh --deep   # ~20s once, then free until a lock moves"])
    if not todo:
        return

    workspaces = todo
    before = {ws: sha256(ws / "Cargo.lock") for ws in workspaces}

    env = dict(os.environ)
    # Never let a probe scribble in the real build tree.
    env["CARGO_TARGET_DIR"] = str(Path(os.environ.get("TMPDIR", "/tmp")) / "preflight-metadata")

    def probe(ws: Path):
        t0 = time.time()
        rc, _out, err = run(
            [targo, "metadata", "--locked", "--format-version", "1",
             "--manifest-path", str(ws / "Cargo.toml")],
            cwd=ws, timeout=timeout,
        )
        return ws, rc, err, time.time() - t0

    results = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool:
        for r in pool.map(probe, workspaces):
            results.append(r)

    inconclusive: list[str] = []
    clean = 0
    for ws, rc, err, dt in results:
        wsname = rel(root, ws) or "."
        if rc == 0:
            clean += 1
            if keys[ws]:
                cache[wsname] = {"key": keys[ws], "verdict": "clean"}
            continue
        if any(re.search(m, err) for m in LOCKED_MARKERS):
            # Prefer the real `error:` line. cargo's `help:` blurb also says
            # "lock file", and quoting that instead tells the reader to run
            # `cargo update` - the one command we know is the wrong tool.
            lines = err.splitlines()
            first = next(
                (ln for ln in lines if ln.lstrip().startswith("error") and "lock" in ln),
                next((ln for ln in lines if ln.lstrip().startswith("error")),
                     err.strip()[:160]),
            )
            sev, why = lock_severity(root, ws)
            rep.add(sev, check, f"{wsname}: resolver CONFIRMS the lock must change",
                    [first.strip(), why, f"({dt:.1f}s)"],
                    [f"targo update --manifest-path {wsname}/Cargo.toml -p <only-the-moved-crate>",
                     "# identify it from the error above; do not re-resolve the whole graph"])
            if keys[ws]:
                cache[wsname] = {"key": keys[ws], "verdict": "skew", "msg": first.strip()}
        else:
            head = err.strip().splitlines()
            head = [ln for ln in head if ln.startswith("error")][:1] or head[-1:]
            inconclusive.append(f"{wsname}: rc={rc} {(head[0] if head else '')[:110]}")
            # NOT cached: "the registry was cold" is a property of the moment.
            cache.pop(wsname, None)

    if inconclusive:
        rep.add(WARN, check,
                f"{len(inconclusive)} workspace(s) INCONCLUSIVE (not skew: network/registry)",
                inconclusive[:10],
                ["# warm the cache, then re-run; --offline reliably false-positives here"])
    rep.add(INFO, check, f"{clean}/{len(workspaces)} workspaces resolve clean under --locked")

    after = {ws: sha256(ws / "Cargo.lock") for ws in workspaces}
    moved = [rel(root, ws) for ws in workspaces if before[ws] != after[ws]]
    if moved:
        # A lockfile that moved is not necessarily OUR doing - a parallel
        # session or editor can touch one mid-probe - but preflight is the only
        # suspect it can rule in or out, so it accuses itself and says how to
        # check. Measured: `targo metadata --locked` leaves the hash untouched.
        rep.add(FAIL, check, "A LOCKFILE MOVED DURING PREFLIGHT",
                [f"changed: {m}" for m in moved]
                + ["preflight never writes one, so either this is a bug here or",
                   "something else (another session, an editor) wrote concurrently."],
                [f"git -C {root} diff -- " + " ".join(f"{m}/Cargo.lock" for m in moved)
                 + "   # inspect BEFORE reverting anything"])
        for m in moved:
            cache.pop(m, None)
    else:
        rep.add(INFO, check, f"non-mutation verified: {len(workspaces)} lockfile hashes unchanged")

    save_deep_cache(root, cache)


# --------------------------------------------------------------------------
# CHECK 3 - tools allowlist audit
# --------------------------------------------------------------------------
def build_tool_model(root: Path, cfg: dict, facts: BootstrapFacts) -> ToolModel:
    build = cfg.get("build") or {}
    tools = build.get("tools")
    ay_man = facts.source_manifests.get("ay")
    return ToolModel(
        facts,
        extended=bool(build.get("extended", False)),
        tools=tools if isinstance(tools, list) else (None if tools is None else []),
        # `Build::unstable_features()` == channel is neither stable nor beta.
        unstable=(cfg.get("rust") or {}).get("channel", "dev") not in ("stable", "beta"),
        ay_present=bool(ay_man) and (root / ay_man).exists(),
    )


def check_tools_allowlist(root: Path, cfg: dict, facts: BootstrapFacts, rep: Report,
                          cfg_path: Path, model: ToolModel) -> None:
    check = "3. TOOLS ALLOWLIST AUDIT"
    build = cfg.get("build") or {}
    tools = build.get("tools")
    extended = model.extended

    if not facts.tool_rs_found:
        rep.add(WARN, check, f"{TOOL_RS} not found; audit degraded to a literal read", [])
        return
    for missing, what in (
        (facts.user_sel is None, f"`{USER_TOOL_SELECTOR}` (entry -> Trust tool name)"),
        (facts.step_sel is None, f"`{STEP_SELECTOR}` (entry -> upstream source name)"),
        (not facts.sysroot_bins, f"`{SYSROOT_BINS_FN}` (what a sysroot ends up with)"),
        (facts.sysroot_bins and not facts.sysroot_bins_modelled,
         f"`{SYSROOT_BINS_FN}` grew control flow this model does not describe"),
    ):
        if missing:
            rep.add(WARN, check, f"could not parse {what} out of {TOOL_RS}",
                    ["the audit below is degraded; treat its tool list as advisory"],
                    [f"$EDITOR {TOOL_RS}  # then re-check tools/preflight.py's parser"])
    if not facts.allowlist_semantics_ok:
        rep.add(WARN, check,
                "`l2_backend_enabled` no longer looks like absent=>all / present=>only-these",
                ["this checker's model of bootstrap may be stale"],
                [f"$EDITOR {TOOL_RS}  # re-read l2_backend_enabled, update tools/preflight.py"])

    rep.add(INFO, check, f"config: {rel(root, cfg_path)}",
            [f"[build] extended = {extended}",
             f"[build] tools    = {'<absent -> ALL tools>' if tools is None else tools}",
             f"[rust]  channel  = {(cfg.get('rust') or {}).get('channel', 'dev')}"
             f"  -> unstable_features = {model.unstable}"])

    if tools is None:
        rep.add(INFO, check, "no `tools` allowlist: every tool bootstrap knows how to build ships")
    elif not isinstance(tools, list):
        rep.add(FAIL, check, "`[build] tools` is not a list", [repr(tools)],
                [f"$EDITOR {rel(root, cfg_path)}"])
        return

    # --- the verification backends: the one class of hole that ships quietly
    backends = ["ay"] + [b for b in (facts.l2_backends or ["ty", "clean"]) if b != "ay"]
    for backend in backends:
        installed, reason = model.installs(root, backend)
        if installed:
            rep.add(OK, check, f"`{backend}` WILL be built and installed", [reason])
            continue
        if installed is None:
            rep.add(WARN, check, f"cannot decide whether `{backend}` ships", [reason],
                    [f"$EDITOR {TOOL_RS}", "tools/preflight.sh --only tools"])
            continue

        role = {
            "ty": "temporal model checker - every derived-model obligation",
            "ay": "SAT/SMT solver - the native verifier's proof authority",
            "clean": "CIC kernel - higher-order theorem prover",
        }.get(backend, "verification backend")
        man_rel = facts.source_manifests.get(backend)
        fix = []
        if man_rel and not (root / man_rel).exists():
            fix.append("git submodule update --init --recursive"
                       f"   # materialise {man_rel}")
        if isinstance(tools, list) and not model.selected(backend):
            fix.append(f'$EDITOR {rel(root, cfg_path)}   # add "{backend}" to [build] tools')
        rep.add(
            FAIL, check,
            f"VERIFICATION BACKEND `{backend}` WILL BE SILENTLY OMITTED from the sysroot",
            [reason,
             f"role: {role}",
             "the build will SUCCEED and ship a toolchain that compiles but cannot verify;",
             "nothing that merely compiles will ever notice the hole."],
            fix,
        )

    if not model.usable:
        return

    # --- the full sysroot bin manifest this config implies -----------------
    will, wont, unknown_gate = [], [], []
    for name in model.all_install_names():
        installed, reason = model.installs(root, name)
        (will if installed else unknown_gate if installed is None else wont).append(
            (name, reason)
        )

    rep.add(INFO, check,
            f"this config installs {len(will)} tool binaries into the sysroot",
            [", ".join(n for n, _ in will) or "<none>"])
    if wont:
        # Deliberately INFO, and deliberately NOT phrased as "not in the
        # allowlist": several of these ARE reachable from an entry that does
        # not spell them (a `cargo-clippy` step installs `targo-tippy`), which
        # is exactly the false alarm this list used to raise. Only names whose
        # gate really evaluates false appear here.
        rep.add(INFO, check,
                f"{len(wont)} tool binary/binaries bootstrap can install are NOT selected",
                [f"{n:<16} {r}" for n, r in wont],
                [f'$EDITOR {rel(root, cfg_path)}  # add any you actually need'])
    if unknown_gate:
        rep.add(WARN, check,
                f"{len(unknown_gate)} tool binary/binaries have a gate this model cannot evaluate",
                [f"{n:<16} {r}" for n, r in unknown_gate],
                [f"$EDITOR {TOOL_RS}"])

    dist_only = [c for c in facts.dist_components if c not in model.all_install_names()]
    if dist_only and isinstance(tools, list) and facts.user_sel:
        unsel = [c for c in dist_only
                 if not any(facts.user_sel.selects(e, c) for e in tools)]
        if unsel:
            # These are `x.py dist` tarball components, not sysroot binaries.
            # Listing them beside the bin manifest is how `trust-analysis` and
            # `trust-llvm-tools` used to read as missing tools.
            rep.add(INFO, check,
                    f"{len(unsel)} DIST component(s) (not sysroot binaries) are not selected",
                    [", ".join(unsel), "these only matter for `x.py dist` / `x.py install`"])

    if isinstance(tools, list):
        known = model.known_entry_names()
        unknown = [e for e in tools if e not in known]
        if unknown:
            rep.add(WARN, check, "allowlist entries that match no known tool (typo?)",
                    [", ".join(unknown)],
                    [f"$EDITOR {rel(root, cfg_path)}"])
        if not extended:
            rep.add(WARN, check, "`extended = false`: user tools are all disabled regardless",
                    ["only the L2 backends ignore `extended`"],
                    [f"$EDITOR {rel(root, cfg_path)}  # set extended = true"])


def check_model_vs_sysroot(root: Path, facts: BootstrapFacts, model: ToolModel,
                           rep: Report) -> None:
    """Hold the model against a sysroot that bootstrap actually produced.

    This is the check that would have caught the bug it replaces: the old audit
    claimed `targo-fmt` was unselected while `build/host/stage2/bin/targo-fmt`
    sat on disk. If the model and a finished sysroot disagree, the model is
    wrong until proven otherwise - so this reports on the CHECKER, not the tree.
    """
    check = "3. TOOLS ALLOWLIST AUDIT"
    if not model.usable:
        return
    predicted = {n for n in model.all_install_names() if model.installs(root, n)[0]}
    if not predicted:
        return
    # `ensure_user_facing_tools` - the consumer of the list this model parses -
    # is itself gated on `target_compiler.stage >= N && extended` in compile.rs.
    # A stage1 sysroot never goes through tool assembly, so comparing against
    # one would manufacture exactly the kind of false alarm this file exists to
    # stop. Read N out of compile.rs rather than assuming it.
    min_stage = 2
    cs = root / "src/bootstrap/src/core/build_steps/compile.rs"
    if cs.exists():
        s = strip_line_comments(cs.read_text(errors="replace"))
        m = re.search(r"stage\s*>=\s*(\d+)[^;{]*?\{[^{}]*?ensure_user_facing_tools", s, re.S)
        if m:
            min_stage = int(m.group(1))
    if not model.extended:
        return  # tool assembly is skipped entirely

    for stage_bin in sorted((root / "build").glob("*/stage*/bin")):
        if not stage_bin.is_dir():
            continue
        sm = re.search(r"/stage(\d+)(-sysroot)?/bin$", str(stage_bin))
        if not sm or int(sm.group(1)) < min_stage:
            continue
        try:
            names = {p.name for p in stage_bin.iterdir()}
        except OSError:
            continue
        if not ({"trustc", "rustc"} & names):
            continue
        missing = sorted(predicted - names)
        extra = sorted(names - predicted - facts.compat_aliases)
        label = rel(root, stage_bin)
        if missing or extra:
            rep.add(WARN, check,
                    f"this checker's model DISAGREES with the built sysroot {label}",
                    ([f"predicted but ABSENT : {', '.join(missing)}"] if missing else [])
                    + ([f"present but UNPREDICTED: {', '.join(extra)}"] if extra else [])
                    + ["if that sysroot predates the current bootstrap.toml this is stale,",
                       "otherwise tools/preflight.py's model of tool.rs is wrong."],
                    [f"ls {label}", f"$EDITOR {TOOL_RS}"])
        else:
            rep.add(OK, check,
                    f"model checked against {label}: {len(predicted)} predicted binaries "
                    f"all present, none unpredicted")


# --------------------------------------------------------------------------
# CHECK 4 - cheap guards
# --------------------------------------------------------------------------
def check_concurrent_build(root: Path, rep: Report, for_build: bool) -> None:
    check = "4. BUILD ENVIRONMENT"
    rc, out, _ = run(["ps", "-axo", "pid=,ppid=,command="], timeout=20)
    if rc != 0:
        return
    me = os.getpid()

    # The x.py that LAUNCHED this preflight is an ancestor process whose command
    # line is, necessarily, `python .../x.py build ...` in this very checkout -
    # i.e. an exact match for what this check hunts for. Without the ancestry
    # filter the hook reports the build it is gating as a competing build and
    # refuses EVERY `x.py build` in the repo, permanently. Measured: it did.
    # The parent pid chain is taken from the same `ps` output, so a hand-run
    # `sh tools/preflight.sh` under a shell wrapper is excluded too, and no
    # cooperation from the caller is required.
    ppid_of: dict[int, int] = {}
    rows: list[tuple[int, str]] = []
    for line in out.splitlines():
        parts = line.strip().split(None, 2)
        if len(parts) < 3:
            continue
        try:
            pid, ppid = int(parts[0]), int(parts[1])
        except ValueError:
            continue
        ppid_of[pid] = ppid
        rows.append((pid, parts[2]))

    mine = {me}
    cur, guard = me, 0
    while cur in ppid_of and guard < 64:
        cur = ppid_of[cur]
        if cur <= 0 or cur in mine:
            break
        mine.add(cur)
        guard += 1

    hits = []
    for pid, cmd in rows:
        if pid in mine or "preflight" in cmd:
            continue
        # Must look like bootstrap AND be this checkout's bootstrap. Matching
        # loosely here caught an unrelated shell snapshot on the first run.
        looks_like_bootstrap = re.search(
            r"(/x\.py|/bootstrap\.py|build/bootstrap/[^/]+/bootstrap)(\s|$)", cmd
        )
        subcmd = re.search(r"\b(build|check|test|dist|install|doc)\b", cmd)
        if looks_like_bootstrap and str(root) in cmd and subcmd:
            hits.append(f"pid {pid}: {cmd[:120]}")
    if hits:
        rep.add(
            FAIL if for_build else WARN, check,
            "AN x.py BUILD IS ALREADY RUNNING - a second one corrupts both",
            hits[:5],
            ["# wait for it, or: kill the other build. Do not start a parallel x.py."],
        )
    else:
        rep.add(INFO, check, "no concurrent x.py build detected")


def check_existing_sysroot(root: Path, cfg: dict, facts: BootstrapFacts, rep: Report) -> None:
    check = "4. BUILD ENVIRONMENT"
    backends = ["ay"] + (facts.l2_backends or ["ty", "clean"])
    for stage_bin in sorted((root / "build").glob("*/stage*/bin")):
        if not stage_bin.is_dir():
            continue
        # stage0 is the downloaded seed toolchain; it never carries the
        # locally-built backends and complaining about it is noise.
        if re.search(r"/stage0(-sysroot)?/bin$", str(stage_bin)):
            continue
        names = {p.name for p in stage_bin.iterdir()}
        if "trustc" not in names and "rustc" not in names:
            continue
        missing = [b for b in backends if b not in names]
        label = rel(root, stage_bin)
        if missing:
            rep.add(WARN, check,
                    f"existing sysroot {label} has NO {', '.join(missing)}",
                    ["this is failure-mode 6 already materialised: it compiles, cannot verify",
                     f"present: {', '.join(sorted(n for n in names if n in backends)) or 'none'}"],
                    ["# rebuild after fixing [build] tools; then re-check this path"])
        else:
            rep.add(OK, check, f"existing sysroot {label} has all backends: {', '.join(backends)}")


def check_misc(root: Path, cfg: dict, rep: Report) -> None:
    check = "4. BUILD ENVIRONMENT"
    build = cfg.get("build") or {}
    py = build.get("python")
    if py and not Path(py).exists():
        rep.add(FAIL, check, "[build] python points at a missing interpreter", [str(py)],
                [f"$EDITOR {rel(root, root / 'bootstrap.toml')}  # fix [build] python"])

    rust = cfg.get("rust") or {}
    if rust.get("deny-warnings") is False:
        rep.add(INFO, check, "`deny-warnings = false` - warnings will not stop the build", [])

    for backend in (rust.get("codegen-backends") or []):
        if backend == "trust-cg" and not (root / "first-party/trust-cg/Cargo.toml").exists():
            rep.add(FAIL, check, "codegen-backends lists trust-cg but its source is absent", [],
                    ["git submodule update --init --recursive"])

    free = shutil.disk_usage(root).free / 1e9
    if free < 25:
        rep.add(FAIL if free < 10 else WARN, check,
                f"only {free:.1f} GB free - a stage2 build needs ~25-40 GB", [],
                [f"# free space under {root}/build before starting"])
    else:
        rep.add(INFO, check, f"{free:.0f} GB free on the build volume")


def check_lock_mtimes(root: Path, workspaces: list[Path], rep: Report) -> None:
    check = "2. LOCKFILE SKEW (non-mutating)"
    stale = []
    for ws in workspaces:
        lk, mn = ws / "Cargo.lock", ws / "Cargo.toml"
        try:
            if mn.stat().st_mtime > lk.stat().st_mtime + 1:
                stale.append(rel(root, ws) or ".")
        except OSError:
            continue
    if stale:
        rep.add(INFO, check, f"{len(stale)} workspace(s) have a manifest newer than their lock",
                [", ".join(stale[:10])],
                ["# advisory only - mtime is not proof of skew"])


# --------------------------------------------------------------------------
def find_targo(root: Path, override: str | None) -> str:
    if override:
        return override
    cands = list((root / "build").glob("*/stage0-sysroot/bin/targo"))
    cands += list((root / "build").glob("host/stage*/bin/targo"))
    for c in cands:
        if c.is_file() and os.access(c, os.X_OK):
            return str(c)
    return shutil.which("targo") or ""


def main() -> int:
    ap = argparse.ArgumentParser(prog="preflight", description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--repo-root", default=str(Path(__file__).resolve().parent.parent))
    ap.add_argument("--bootstrap-toml", default=None,
                    help="audit a candidate config instead of <repo>/bootstrap.toml")
    ap.add_argument("--deep", action="store_true",
                    help="also run the authoritative `targo metadata --locked` probe")
    ap.add_argument("--deep-if-cached", action="store_true",
                    help="report deep verdicts that are already cached and still valid, "
                         "but never spend time earning new ones (adds no latency)")
    ap.add_argument("--all-workspaces", action="store_true",
                    help="scan every workspace in the tree, not just build-relevant ones")
    ap.add_argument("--for-build", action="store_true",
                    help="invoked immediately before a build (concurrent build becomes fatal)")
    ap.add_argument("--verdict-file", default=None,
                    help="write CLEAR/BLOCKED here after emitting the report. The x.py hook "
                         "uses this so a crashed checker can never be read as a verdict.")
    ap.add_argument("--depth", type=int, default=3, help="shallow workspace scan depth")
    ap.add_argument("--timeout", type=int, default=120, help="per-workspace deep probe timeout")
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--targo", default=None)
    ap.add_argument("--no-color", action="store_true")
    ap.add_argument("--only", default=None,
                    help="comma-separated subset: submodules,lockfiles,tools,env")
    args = ap.parse_args()

    t0 = time.time()
    root = Path(args.repo_root).resolve()
    color = (not args.no_color) and sys.stdout.isatty() and os.environ.get("NO_COLOR") is None
    rep = Report(color)

    only = set(args.only.split(",")) if args.only else {"submodules", "lockfiles", "tools", "env"}
    checks_run: list[str] = []

    cfg_path = Path(args.bootstrap_toml) if args.bootstrap_toml else root / "bootstrap.toml"
    cfg, cfg_err = ({}, None)
    if cfg_path.exists():
        cfg, cfg_err = load_toml(cfg_path)
        cfg = cfg or {}
    else:
        cfg_err = "file not found"

    facts = read_bootstrap_facts(root)

    if "submodules" in only:
        checks_run.append("1. SUBMODULE DRIFT")
        check_submodules(root, rep)
        check_bootstrap_submodule_policy(root, cfg, rep)

    workspaces: list[Path] = []
    if "lockfiles" in only:
        checks_run.append("2. LOCKFILE SKEW (non-mutating)")
        workspaces = discover_workspaces(root, facts, args.depth, args.all_workspaces)
        check_lockfiles_fast(root, workspaces, rep)
        checks_run.append("2a. GIT-PIN CASCADE (submodule manifest -> parent lock)")
        check_git_pin_cascade(root, workspaces, rep)
        check_lock_mtimes(root, workspaces, rep)
        if args.deep or args.deep_if_cached:
            checks_run.append("2b. LOCKFILE SKEW (deep, `metadata --locked`)")
            check_lockfiles_deep(root, workspaces, rep,
                                 find_targo(root, args.targo), args.timeout, args.jobs,
                                 cached_only=not args.deep)

    if "tools" in only:
        checks_run.append("3. TOOLS ALLOWLIST AUDIT")
        if cfg_err:
            rep.add(FAIL, "3. TOOLS ALLOWLIST AUDIT",
                    f"cannot read {cfg_path}: {cfg_err}", [],
                    ["cp bootstrap.example.toml bootstrap.toml  # then edit"])
        else:
            model = build_tool_model(root, cfg, facts)
            check_tools_allowlist(root, cfg, facts, rep, cfg_path, model)
            check_model_vs_sysroot(root, facts, model, rep)

    if "env" in only:
        checks_run.append("4. BUILD ENVIRONMENT")
        check_concurrent_build(root, rep, args.for_build)
        check_existing_sysroot(root, cfg, facts, rep)
        check_misc(root, cfg, rep)

    rc = rep.emit(time.time() - t0, checks_run)
    if args.verdict_file:
        # Written only once a report has actually been emitted, so a crash
        # leaves NO verdict rather than a stale or half-formed one.
        try:
            Path(args.verdict_file).write_text("BLOCKED\n" if rc else "CLEAR\n")
        except OSError:
            pass
    return rc


if __name__ == "__main__":
    # EXIT CODE CONTRACT, and the reason this wrapper exists:
    #   0 = ran, cleared      1 = ran, found a blocking problem      2 = BROKE
    # An unhandled exception in a python script exits 1 by default - the same
    # code as a real finding. x.py refuses to build on 1, so without this a
    # typo in this file would brick every build in the repo while claiming the
    # TREE was at fault. Crashes are forced to 2 and stay non-blocking.
    try:
        raise SystemExit(main())
    except SystemExit:
        raise
    except KeyboardInterrupt:
        sys.stderr.write("\npreflight: interrupted\n")
        raise SystemExit(2)
    except BaseException:
        import traceback

        traceback.print_exc()
        sys.stderr.write(
            "\npreflight: the CHECKER ITSELF crashed (traceback above).\n"
            "preflight: exiting 2 = 'preflight broke', NOT 1 = 'your tree is broken',\n"
            "preflight: so x.py will warn and continue rather than block on a bug here.\n"
        )
        raise SystemExit(2)
