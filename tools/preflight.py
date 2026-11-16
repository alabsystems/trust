#!/bin/sh
""":"
# Trust: python floor. POSIX sh runs this block when the file is EXECUTED and
# re-execs under a >=3.11 interpreter; Python reads it as a string.
for candidate in python3.14 python3.13 python3.12 python3.11 python3; do
    if command -v "$candidate" >/dev/null 2>&1 \
        && "$candidate" -I -S -c 'import sys; raise SystemExit(sys.version_info < (3, 11))' 2>/dev/null; then
        exec "$candidate" -I -S "$0" "$@"
    fi
done
echo "preflight.py requires Python 3.11+ (tomllib)" >&2
exit 2
":"""
from __future__ import annotations

import os as _floor_os
import shutil as _floor_shutil
import sys as _floor_sys

# Trust: python floor, second half. `python3 preflight.py` reads the sh block above
# as a string, so an old `python3` (3.9 on macOS CommandLineTools) re-execs here.
if __name__ == "__main__" and _floor_sys.version_info < (3, 11):
    for _floor_candidate in ("python3.14", "python3.13", "python3.12", "python3.11"):
        _floor_path = _floor_shutil.which(_floor_candidate)
        if _floor_path:
            _floor_argv = [_floor_path, "-I", "-S", _floor_os.path.abspath(__file__), *_floor_sys.argv[1:]]
            _floor_os.execv(_floor_path, _floor_argv)
    _floor_sys.exit("preflight.py requires Python 3.11+ (tomllib); none found on PATH")

__doc__ = """Trust build preflight checker.

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

import argparse
import copy
import concurrent.futures
import hashlib
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import time
from contextlib import contextmanager
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

# `build.noindex` is the Spotlight-excluded home that `build` may link to
# (docs/BUILD_AND_INSTALL.md). os.walk never follows the `build` link, but it
# WOULD descend the real directory beside it: hundreds of GiB of build output.
PRUNE_DIRS = {".git", "build", "build.noindex", "target", "node_modules", ".cargo", "__pycache__"}
DEP_TABLES = ("dependencies", "dev-dependencies", "build-dependencies")
TOOL_RS = "src/bootstrap/src/core/build_steps/tool.rs"
# The only submodule repair preflight prints. A blanket `git submodule update`
# cannot tell a BEHIND worktree from an AHEAD one and moves off unlanded work;
# the sync script moves only the provably lossless modules and names the rest.
SUBMODULE_RESTORE = "bash scripts/submodule_sync.sh --fetch --restore"
DIST_RS = "src/bootstrap/src/core/build_steps/dist.rs"
INSTALL_RS = "src/bootstrap/src/core/build_steps/install.rs"

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

        # A finding whose `check` is not in `checks_run` was never rendered by the
        # loop above, yet it still counts below -- which produced the worst
        # possible gate output: "N blocking ... DO NOT START A BUILD" with no FAIL
        # line anywhere and a REMEDIATION PLAN whose commands belong to an item
        # the operator cannot see. That is indistinguishable from a broken gate,
        # and it is what got this preflight overridden with TRUST_SKIP_PREFLIGHT=1
        # on a day its demand was CORRECT (the first-party/clean gitlink was stale
        # and trust's own rustc_parse would not compile without the bump).
        # Render them rather than counting them silently.
        rendered = set(checks_run)
        orphans = [f for f in self.findings if f.check not in rendered]
        if orphans:
            title = "--- FINDINGS OUTSIDE THE CHECKS THAT RAN "
            print(f"\n{self._c(title + '-' * max(0, 78 - len(title)), '1')}")
            print("         these were recorded by a check that is not in this run's")
            print("         check list; they still COUNT below, so they are shown here")
            print("         instead of vanishing.")
            for f in sorted(orphans, key=lambda f: _ORDER[f.severity]):
                print(f"  {self.tag(f.severity)} [{f.check}] {f.title}")
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
def run(cmd: list[str], cwd: Path | None = None, timeout: int = 60,
        env: dict[str, str] | None = None) -> tuple[int, str, str]:
    try:
        p = subprocess.run(
            cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout, check=False, env=env
        )
        return p.returncode, p.stdout, p.stderr
    except (subprocess.TimeoutExpired, FileNotFoundError, OSError) as e:
        return 127, "", str(e)


_TOML_CACHE: dict[str, tuple] = {}


class BootstrapConfigError(Exception):
    """The effective bootstrap configuration could not be resolved exactly."""


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


def _merge_missing(current: dict, fallback: dict) -> None:
    """Merge `fallback` as bootstrap's `IgnoreDuplicate` merge does."""
    for key, value in fallback.items():
        if key not in current:
            current[key] = copy.deepcopy(value)
        elif isinstance(current[key], dict) and isinstance(value, dict):
            _merge_missing(current[key], value)


def _merge_override(current: dict, override: dict) -> None:
    """Merge `override` as bootstrap's final `--set` merge does."""
    for key, value in override.items():
        if isinstance(current.get(key), dict) and isinstance(value, dict):
            _merge_override(current[key], value)
        else:
            current[key] = copy.deepcopy(value)


def _merge_unique(current: dict, addition: dict, prefix: str = "") -> None:
    """Collect repeated `--set`s while rejecting duplicate leaf settings."""
    for key, value in addition.items():
        dotted = f"{prefix}.{key}" if prefix else key
        if key not in current:
            current[key] = copy.deepcopy(value)
        elif isinstance(current[key], dict) and isinstance(value, dict):
            _merge_unique(current[key], value, dotted)
        else:
            raise BootstrapConfigError(f"duplicate --set value for {dotted}")


def _read_bootstrap_toml(path: Path) -> dict:
    cfg, err = load_toml(path)
    if err:
        raise BootstrapConfigError(f"cannot read {path}: {err}")
    if not isinstance(cfg, dict):
        raise BootstrapConfigError(f"{path} does not contain a TOML table")
    return copy.deepcopy(cfg)


def _canonical_bootstrap_path(path: Path) -> Path:
    """Canonicalize a config path exactly where bootstrap does."""
    try:
        return path.resolve(strict=True)
    except (OSError, RuntimeError) as error:
        raise BootstrapConfigError(f"cannot canonicalize {path}: {error}") from error


def _with_includes(
    cfg: dict,
    cfg_path: Path,
    stack: tuple[Path, ...],
    *,
    canonicalize_children: bool,
) -> dict:
    """Apply includes with bootstrap's top-level/recursive path asymmetry."""
    includes = cfg.get("include", [])
    if not isinstance(includes, list) or not all(isinstance(path, str) for path in includes):
        raise BootstrapConfigError(f"{cfg_path}: `include` must be a list of paths")

    effective = copy.deepcopy(cfg)
    for include in reversed(includes):
        include_path = Path(include)
        if not include_path.is_absolute():
            include_path = cfg_path.parent / include_path
        child_stack = stack
        if canonicalize_children:
            include_path = _canonical_bootstrap_path(include_path)
            if include_path in stack:
                chain = " -> ".join(str(path) for path in (*stack, include_path))
                raise BootstrapConfigError(f"cyclic bootstrap include: {chain}")
            child_stack = (*stack, include_path)
        included = _with_includes(
            _read_bootstrap_toml(include_path),
            include_path,
            child_stack,
            canonicalize_children=True,
        )
        _merge_missing(effective, included)
    return effective


def _parse_bootstrap_set(option: str) -> dict:
    try:
        value = tomllib.loads(option)
    except Exception as first_error:
        if "=" in option:
            key, raw = option.split("=", 1)
            if '"' not in raw:
                try:
                    value = tomllib.loads(f'{key}="{raw}"')
                except Exception:
                    raise BootstrapConfigError(
                        f"failed to parse --set {option!r}: {first_error}"
                    ) from first_error
            else:
                raise BootstrapConfigError(
                    f"failed to parse --set {option!r}: {first_error}"
                ) from first_error
        else:
            raise BootstrapConfigError(
                f"failed to parse --set {option!r}: {first_error}"
            ) from first_error
    if not isinstance(value, dict):
        raise BootstrapConfigError(f"--set {option!r} does not describe a TOML setting")
    return value


def resolve_bootstrap_config(
    root: Path,
    explicit_path: str | None,
    override_set: list[str],
    invocation_cwd: Path,
    environment: dict[str, str] | None = None,
) -> tuple[dict, Path, str | None]:
    """Resolve the config sources in the same precedence order as bootstrap."""
    environment = os.environ if environment is None else environment
    selected = explicit_path or environment.get("RUST_BOOTSTRAP_CONFIG")
    required = selected is not None
    if selected is not None:
        cfg_path = Path(selected)
        if not cfg_path.is_absolute():
            cfg_path = invocation_cwd / cfg_path
    else:
        candidates = [
            invocation_cwd / "bootstrap.toml",
            root / "bootstrap.toml",
            invocation_cwd / "config.toml",
            root / "config.toml",
        ]
        cfg_path = next((path for path in candidates if path.exists()), candidates[1])

    if not cfg_path.exists():
        # Preserve preflight's existing fail-closed local-config requirement.
        why = "explicit config file not found" if required else "file not found"
        return {}, cfg_path, why

    try:
        cfg_path = _canonical_bootstrap_path(cfg_path)
        effective = _with_includes(
            _read_bootstrap_toml(cfg_path),
            cfg_path,
            (),
            canonicalize_children=False,
        )
        profile = effective.get("profile")
        if profile is not None:
            if not isinstance(profile, str):
                raise BootstrapConfigError("`profile` must be a string")
            profile = {"user": "dist"}.get(profile, profile)
            profile_path = root / "src" / "bootstrap" / "defaults" / f"bootstrap.{profile}.toml"
            profile_cfg = _with_includes(
                _read_bootstrap_toml(profile_path),
                profile_path,
                (),
                canonicalize_children=False,
            )
            _merge_missing(effective, profile_cfg)

        overrides: dict = {}
        for option in override_set:
            _merge_unique(overrides, _parse_bootstrap_set(option))
        _merge_override(effective, overrides)
    except BootstrapConfigError as error:
        return {}, cfg_path, str(error)
    return effective, cfg_path, None


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
    # `[build] tools` entries that install.rs consults directly: an `install!`
    # step gated by `Self::should_build` (which matches its alias, e.g.
    # `trustc-dev`), and literal `tools.contains("rust-src")` gates. Neither is
    # a sysroot binary, so without these the audit called the committed
    # `compiler`/`tools` profiles' `trustc-dev` and `rust-src` entries typos.
    # Both are read from install.rs, never listed here: when upstream 162423
    # renamed `src` to `rust-src`, a profile still naming `src` drew the typo
    # warning because `src` had stopped selecting anything.
    install_selectors: list[str] = field(default_factory=list)
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

    install_src = root / INSTALL_RS
    install_selectors: list[str] = []
    if install_src.exists():
        ins = strip_line_comments(install_src.read_text(errors="replace"))
        install_selectors = sorted(
            set(
                re.findall(
                    r'\b[A-Z]\w*,\s*(?:alias|path)\s*=\s*"([^"]+)",\s*Self::should_build\(_config\)',
                    ins,
                )
            )
            | set(re.findall(r'tools\.as_ref\(\)[^;{]*?\.contains\("([^"]+)"\)', ins))
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
        install_selectors=install_selectors,
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
        known |= set(self.f.install_selectors)
        for tbl in (self.f.user_sel, self.f.step_sel):
            if tbl:
                known |= tbl.entries | tbl.targets
        for b in self.f.sysroot_bins:
            known.add(b.src)
        return known


# --------------------------------------------------------------------------
# CHECK 1 - submodule drift
# --------------------------------------------------------------------------
def check_submodules(root: Path, rep: Report, *, deferred_first_party: bool = False) -> None:
    check = "1. SUBMODULE DRIFT"
    rc, out, err = run(["git", "submodule", "status", "--recursive"], cwd=root)
    if rc != 0:
        rep.add(FAIL, check, "could not enumerate recursive submodule status",
                [err.strip()[:200]])
        return

    drifted: list[str] = []
    uninit: list[str] = []
    conflicted: list[str] = []
    unresolved: list[str] = []
    records: list[tuple[str, str, str, str]] = []
    paths: set[str] = set()

    for line in out.splitlines():
        if not line.strip():
            continue
        prefix, rest = line[0], line[1:]
        parts = rest.split()
        if (len(parts) < 2 or prefix not in " +-U"
                or re.fullmatch(r"[0-9a-f]{40}|[0-9a-f]{64}", parts[0]) is None):
            rep.add(FAIL, check, "malformed recursive submodule status", [line[:200]])
            unresolved.append(line)
            continue
        sha, path = parts[0], parts[1]
        described = " ".join(parts[2:]).strip("()") if len(parts) > 2 else ""
        relative = Path(path)
        if (relative.is_absolute() or any(part in (".", "..") for part in path.split("/"))
                or relative.as_posix() != path or path in paths
                or (len(parts) > 2 and not (parts[2].startswith("(") and parts[-1].endswith(")")))):
            rep.add(FAIL, check, "ambiguous recursive submodule path", [line[:200]])
            unresolved.append(path)
            continue
        paths.add(path)
        records.append((prefix, sha, path, described))

    for prefix, sha, path, described in records:
        if deferred_first_party and prefix == "-" and path.startswith("first-party/"):
            rep.add(INFO, check, f"{path}: unrelated source deferred for standalone tool only", [])
            continue
        sub = root / path
        # A nested gitlink belongs to its immediate repository, not to the
        # outer tree: HEAD:first-party/parent/child cannot cross a gitlink.
        parent_path = next(
            (parent for parent in Path(path).parents if parent.as_posix() in paths),
            Path("."),
        )
        parent = root / parent_path
        pin_path = Path(path).relative_to(parent_path).as_posix()
        if parent_path != Path(".") and not (parent / ".git").exists():
            unresolved.append(path)
            rep.add(FAIL, check, f"{path} has an uninitialised pin-owning repository",
                    [parent_path.as_posix()])
            continue

        # `git submodule status` diffs the worktree against the INDEX, not HEAD.
        # `git add -A` on a drifted tree stages the stale gitlink and the `+`
        # silently disappears while the submodule is still weeks behind the
        # committed pin - which is exactly the shape of the E0599/E0432 hunt.
        # So the committed pin is compared explicitly, prefix or no prefix.
        pinned = ""
        prc, pout, _ = run(["git", "rev-parse", f"HEAD:{pin_path}"], cwd=parent)
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
        if (re.fullmatch(r"[0-9a-f]{40}|[0-9a-f]{64}", pinned) is None
                or (prefix != "-" and
                    (not initialised or re.fullmatch(r"[0-9a-f]{40}|[0-9a-f]{64}", actual) is None))):
            unresolved.append(path)
            rep.add(FAIL, check, f"{path} has unreadable committed pin or checkout identity",
                    [f"pin owner: {parent_path.as_posix()} (HEAD:{pin_path})",
                     f"pinned: {pinned or '<unknown>'}; actual: {actual or '<none>'}"])
            continue
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
            f"pinned by repo: {pinned}  ({parent_path.as_posix()}:HEAD:{pin_path})",
        ]

        if staged_drift:
            drifted.append(path)
            rep.add(
                FAIL,
                check,
                f"{path} is off the COMMITTED pin, and the drift is STAGED "
                f"(git submodule status shows no `+`)",
                detail + [
                    "the stale gitlink is in the index, so a restore to the index",
                    "would re-apply the STALE sha. Unstage it first.",
                ],
                [
                    f"git -C {parent_path.as_posix()} restore --staged -- {pin_path}",
                    f"{SUBMODULE_RESTORE}   # moves only lossless modules; prints the rest",
                ],
            )
        elif prefix == "+":
            drifted.append(path)
            rep.add(
                FAIL,
                check,
                f"{path} is AHEAD/BEHIND its pin (`+`) - stale APIs will look like source bugs",
                detail,
                [f"{SUBMODULE_RESTORE}   # BEHIND moves; AHEAD/DIVERGENT is someone's work: it says"],
            )
        elif prefix == "-":
            uninit.append(path)
            rep.add(
                FAIL,
                check,
                f"{path} is NOT INITIALISED (`-`) - the pinned source closure is incomplete",
                detail,
                [SUBMODULE_RESTORE],
            )
        elif prefix == "U":
            conflicted.append(path)
            rep.add(
                FAIL,
                check,
                f"{path} has MERGE CONFLICTS (`U`) - resolve before any build",
                detail,
                [f"git -C {path} status", "# resolve conflicts, then:",
                 SUBMODULE_RESTORE],
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
                f"{path} has LOCAL CHANGES that will BLOCK restoring its pin",
                [f"dirty: {f}" for f in files]
                + ["('local changes to the following files would be overwritten')"],
                [
                    f"git -C {path} status   # these edits may be someone's work: "
                    "commit or stash them there, never discard them",
                    SUBMODULE_RESTORE,
                ],
            )

    # Even with zero drift, an uncommitted lockfile inside a submodule is a
    # loaded gun: the day drift appears, `git submodule update` refuses with
    # "local changes would be overwritten" and the correct fix is unavailable
    # until the edit is rescued. Surface it while it is still cheap.
    for _, _, path, _ in records:
        if path in drifted + conflicted:
            continue
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

    if not (drifted or uninit or conflicted or unresolved):
        rep.add(INFO, check, f"all {len(records)} recursive submodules match their pinned gitlink SHA")


def build_pin_ranges(root: Path) -> tuple[str, list[str], list[str]]:
    """Snapshot build ancestry, not the net change of a hypothetical push.

    A newer remote tip is not an ancestor of a historical build. Comparing its
    pins directly against HEAD mistakes unchanged old pins for a rollback.
    Resolve refs once, then judge every best common ancestor against that exact
    build commit. Publication still uses check_pin_regression.sh's destination
    range; this function does not select or authorize a push range.
    """
    def git(*args: str, absent_ok: bool = False) -> str | None:
        proc = subprocess.run(
            ["git", *args], cwd=root, capture_output=True, text=True, timeout=30,
        )
        if absent_ok and proc.returncode == 1:
            return None
        proc.check_returncode()
        return proc.stdout.strip()

    def oid(value: str | None) -> str:
        if value is None or re.fullmatch(r"(?:[0-9a-f]{40}|[0-9a-f]{64})", value) is None:
            raise ValueError(f"invalid Git commit identity: {value!r}")
        return value

    tip = oid(git("rev-parse", "--verify", "HEAD^{commit}"))
    # --quiet distinguishes a missing ref (1) from a Git failure; non-quiet
    # `show-ref --verify` instead exits 128 for absence. Read the identity only
    # after that distinction, and never pass a moving ref into a comparison.
    remote_present = git("show-ref", "--verify", "--quiet", "refs/remotes/origin/main",
                         absent_ok=True)
    remote = (None if remote_present is None else
              oid(git("rev-parse", "--verify", "refs/remotes/origin/main^{commit}")))
    notes = [f"build commit: {tip}"]
    shallow = git("rev-parse", "--is-shallow-repository")
    if shallow not in ("true", "false"):
        raise ValueError("cannot determine whether build history is shallow")
    if shallow == "true":
        notes.append("shallow history: ancestry comparisons cover only available commits")
    bases: list[str] = []
    if remote is not None:
        notes.append(f"observed origin/main: {remote}")
        common = git("merge-base", "--all", tip, remote, absent_ok=True)
        if common is not None:
            bases = [oid(base) for base in common.splitlines()]
            if not bases:
                raise ValueError("Git returned no best common ancestors with a success exit")
        else:
            notes.append("origin/main has no common ancestry; checking available build parents")
    else:
        notes.append("origin/main is absent; checking available build parents (no fetch required)")
    if not bases:
        parents = git("rev-list", "--parents", "--max-count=1", tip)
        if not parents or parents.split()[0] != tip:
            raise ValueError("cannot enumerate build parents")
        bases = [oid(parent) for parent in parents.split()[1:]]
        if not bases:
            notes.append("no available parent: no build-ancestry pin transition to compare")
    ranges = [f"{base}..{tip}" for base in sorted(set(bases))]
    notes.extend(f"build ancestry range: {span}" for span in ranges)
    notes.append("publication is separate: the push guard compares the actual destination tip")
    return tip, ranges, notes


def check_pin_regression(root: Path, rep: Report) -> None:
    """Refuse a SILENT BACKWARD move of a `first-party/*` pin.

    `check_submodules` catches WORKTREE drift — the checkout differing from the
    recorded gitlink. It cannot catch the case where the RECORDED PIN ITSELF moved
    backward and the worktree faithfully matches it: everything reports OK while
    the tree no longer builds.

    That case is neither hypothetical nor rare. A submodule gitlink has no textual
    content, so a merge picks a side and reports NO CONFLICT, while the consumer
    source merges forward cleanly — the two drift apart silently. On 2026-08-25/26
    this reverted `first-party/clean` from `0b3b94e5b3` to `99e2128ef2` FOUR times
    across successive merges. Each time `rustc_parse` still referenced
    `SurfaceDecl::IncludeVars`/`OmitVars`, which exist only at the newer pin, so
    the tree failed with three E0599s in the PARSER — nowhere near the change under
    test — after a full 90-minute build had already been spent.

    Use the build's own ancestry, never a newer remote tip as the build's base.
    The standalone script's default and actual pre-push semantics are unchanged.
    """
    check = "pin_regression"
    script = root / "scripts" / "check_pin_regression.sh"
    if not script.is_file():
        rep.add(FAIL, check, "pin regression checker is missing", [str(script)])
        return
    try:
        tip, ranges, notes = build_pin_ranges(root)
        rep.add(INFO, check, "checking build ancestry, not a proposed publication", notes)
        for span in ranges:
            proc = subprocess.run(
                ["bash", str(script), span],
                cwd=root, capture_output=True, text=True, timeout=60,
            )
            if proc.returncode == 0:
                continue
            detail = (proc.stdout + proc.stderr).strip().splitlines()
            rep.add(
                FAIL, check,
                ("a first-party pin regression was refused in the build ancestry"
                 if proc.returncode == 1 else "pin regression checker did not complete"),
                [f"range: {span}", f"checker exit: {proc.returncode}", *detail[:12]],
                [f"bash scripts/check_pin_regression.sh {span}",
                 "# inspect the reported pin and reconcile it with its consumers"],
            )
        after = subprocess.run(
            ["git", "rev-parse", "--verify", "HEAD^{commit}"],
            cwd=root, capture_output=True, text=True, timeout=30, check=True,
        ).stdout.strip()
        if after != tip:
            raise ValueError(f"build HEAD changed during pin audit: {tip} -> {after}")
    except (OSError, subprocess.SubprocessError, ValueError) as error:
        rep.add(FAIL, check, "pin regression ancestry check could not be completed",
                [str(error)], ["git status", "git log --oneline --parents -5"])


def _pin_rollback_disclosed(root: Path, path: str, since: str) -> str:
    """Return the `pin-rollback:` line that DISCLOSES a backward move, or "".

    `scripts/check_pin_regression.sh` states the repo's convention for this in
    full: "THE ESCAPE HATCH IS DISCLOSURE, NOT SUPPRESSION" — a deliberate
    rollback is legitimate, you just have to say so in the commit message as

        pin-rollback: <path> <why>

    and there is deliberately no env-var off switch. `check_pin_behind_history`
    shipped without that hatch, which made a deliberate rollback INEXPRESSIBLE:
    the check hard-FAILs and prints, as its fix, the very checkout that restores
    the pin whose adoption broke the build. Measured 2026-08-28: `first-party/clean`
    at ac4874697 requires ay 0.18.0 while six sibling first-party repos require
    0.17.0 through the same patched source URL, so adopting it splits every ay
    crate in two and stage2 stops compiling — and the only in-repo repair is a
    backward walk of that one pin. Without a hatch the repair could not be built
    at all, and following the printed fix re-breaks the tree.

    The window searched is `<since>..HEAD` restricted to this gitlink, where
    `<since>` is the commit that recorded the NEWER pin. That is exactly the set
    of commits that could have performed or re-affirmed the rollback, so a
    disclosure written once keeps holding as later commits land, and a pin that
    walks backward again LATER — past a newer high-water mark, with no fresh
    disclosure — still fails.
    """
    try:
        msgs = subprocess.run(
            ["git", "--literal-pathspecs", "log", "--format=%B", f"{since}..HEAD", "--", path],
            cwd=root, capture_output=True, text=True, timeout=30,
        ).stdout
    except Exception:
        return ""
    pat = re.compile(
        rf"^[ \t]*pin-rollback:[ \t]*.*{re.escape(path)}.*$",
        re.IGNORECASE | re.MULTILINE,
    )
    m = pat.search(msgs)
    return m.group(0).strip() if m else ""


PIN_HISTORY_LIMIT = 40


def _history_git_objects(repo: Path, specs: list[str], *, contents: bool = True
                         ) -> list[tuple[str, bytes, bytes] | None]:
    """Bounded native object reads; requests contain only Git object identities."""
    if not specs:
        return []
    if any(re.fullmatch(r"(?:[0-9a-f]{40}|[0-9a-f]{64})(?:\^\{(?:tree|commit)\})?", spec)
           is None for spec in specs):
        raise ValueError("invalid Git batch object identity")
    proc = subprocess.run(
        ["git", "cat-file", "--batch" if contents else "--batch-check"], cwd=repo,
        input="".join(f"{spec}\n" for spec in specs).encode("ascii"),
        capture_output=True, timeout=30,
    )
    proc.check_returncode()
    result = []
    position = 0
    for _spec in specs:
        end = proc.stdout.index(b"\n", position)
        fields = proc.stdout[position:end].split()
        position = end + 1
        if len(fields) == 2 and fields[1] == b"missing":
            result.append(None)
            continue
        if (len(fields) != 3 or not re.fullmatch(rb"[0-9a-f]{40}|[0-9a-f]{64}", fields[0])
                or not fields[2].isdigit()):
            raise ValueError("invalid Git batch object header")
        size = int(fields[2]) if contents else 0
        body = proc.stdout[position:position + size]
        if contents:
            if len(body) != size or proc.stdout[position + size:position + size + 1] != b"\n":
                raise ValueError("incomplete Git batch object body")
            position += size + 1
        result.append((fields[0].decode("ascii"), fields[1], body))
    if position != len(proc.stdout):
        raise ValueError("unexpected trailing Git batch output")
    return result


def _history_tree_pins(root: Path, queries: list[tuple[str, str]]) -> dict[tuple[str, str], str]:
    """Read exact gitlinks, batching immutable trees instead of spawning per pin."""
    if not queries:
        return {}
    result = {query: "" for query in queries}

    def native(query):
        rev, path = query
        if re.fullmatch(r"[0-9a-f]{40}|[0-9a-f]{64}", rev) is None:
            return ""
        try:
            proc = subprocess.run(
                ["git", "--literal-pathspecs", "ls-tree", "-z", rev, "--", path],
                cwd=root, capture_output=True, timeout=30,
            )
            fields = proc.stdout.partition(b"\t")[0].split()
            return fields[2].decode("ascii") if len(fields) == 3 and fields[0] == b"160000" else ""
        except Exception:
            return ""

    try:
        revisions = sorted({rev for rev, _path in queries})
        roots = dict(zip(revisions, _history_git_objects(
            root, [f"{rev}^{{tree}}" for rev in revisions])))
        trees = {}

        def remember(record):
            oid, kind, body = record
            if kind != b"tree":
                raise ValueError("Git returned a non-tree for a tree request")
            entries = {}
            position = 0
            width = len(oid) // 2
            while position < len(body):
                space = body.index(b" ", position)
                end = body.index(b"\0", space)
                last = end + 1 + width
                if last > len(body):
                    raise ValueError("incomplete Git tree entry")
                entries[body[space + 1:end]] = (int(body[position:space], 8), body[end + 1:last].hex())
                position = last
            trees[oid] = entries

        for record in roots.values():
            if record is not None:
                remember(record)
        pending = {}
        for query in result:
            parts = os.fsencode(query[1]).split(b"/")
            if any(part in (b"", b".", b"..") for part in parts):
                result[query] = native(query)  # retain Git's unusual path-shape behavior
            elif roots[query[0]] is not None:
                pending[query] = (roots[query[0]][0], parts)
        while pending:
            needed = sorted({oid for oid, _parts in pending.values()} - trees.keys())
            for oid, record in zip(needed, _history_git_objects(root, needed)):
                if record is None:
                    raise ValueError(f"missing Git tree {oid}")
                remember(record)
            following = {}
            for query, (oid, parts) in pending.items():
                mode, child = trees[oid].get(parts[0], (0, ""))
                if len(parts) == 1:
                    if mode == 0o160000:
                        result[query] = child
                elif mode == 0o40000:
                    following[query] = (child, parts[1:])
            pending = following
        return result
    except Exception:
        # A batch failure must not lose independently readable historical pins.
        return {query: native(query) for query in result}


def _historical_descendants(repo: Path, current: str, candidates: list[str]) -> set[str]:
    """Native ancestry-path membership equals current<=candidate, including tags."""
    if not candidates:
        return set()
    try:
        names = [current, *dict.fromkeys(candidates)]
        records = _history_git_objects(repo, [f"{oid}^{{commit}}" for oid in names], contents=False)
        peeled = {name: record[0] for name, record in zip(names, records)
                  if record is not None and record[1] == b"commit"}
        if current not in peeled:
            return set()
        bottom = peeled[current]
        tips = sorted(set(peeled.values()) - {bottom})
        descendants = set()
        if tips:
            proc = subprocess.run(
                ["git", "rev-list", "--ancestry-path", "--stdin"], cwd=repo,
                input="".join(f"{oid}\n" for oid in [*tips, f"^{bottom}"]),
                capture_output=True, text=True, timeout=30,
            )
            proc.check_returncode()
            descendants = set(proc.stdout.split())
        return {old for old in candidates if old in peeled
                and (peeled[old] == bottom or peeled[old] in descendants)}
    except Exception:
        result = set()
        for old in candidates:
            try:
                proc = subprocess.run(
                    ["git", "merge-base", "--is-ancestor", current, old],
                    cwd=repo, capture_output=True, timeout=30,
                )
                if proc.returncode == 0:
                    result.add(old)
            except Exception:
                continue
        return result


def check_pin_behind_history(root: Path, rep: Report) -> None:
    """Refuse a pin that is STRICTLY OLDER than one this repo already recorded.

    This is the half `check_pin_regression` cannot see. The build guard judges
    the branch's net change since its common ancestry, so it catches a
    regression a branch INTRODUCES and is
    blind to one it INHERITS — and on 2026-08-26 `origin/main` itself carried the
    stale `first-party/clean` gitlink, so nothing fired while the tree did not
    build.

    The question here is history-relative rather than branch-relative: for each
    submodule, did some earlier superproject commit record a pin that the CURRENT
    pin is a strict ancestor of? If so the pin moved backward at some point and
    was never repaired, no matter who did it or on which branch.

    Ancestry, not recency, is the test — a legitimate pin move to a sibling branch
    is not an ancestor of what it replaced, so it is not flagged. Only a strict
    walk-backward is.
    """
    check = "pin_behind_history"
    try:
        paths = subprocess.run(
            ["git", "config", "-z", "-f", ".gitmodules", "--get-regexp", r"^submodule\..*\.path$"],
            cwd=root, capture_output=True, timeout=30,
        ).stdout.split(b"\0")
        subs = [os.fsdecode(record.partition(b"\n")[2]) for record in paths
                if record.partition(b"\n")[2].startswith(b"first-party/")]
        if not subs:
            return
        tip = subprocess.run(
            ["git", "rev-parse", "--verify", "HEAD^{commit}"],
            cwd=root, capture_output=True, text=True, timeout=30, check=True,
        ).stdout.strip()
    except Exception:
        return
    current = _history_tree_pins(root, [(tip, path) for path in subs])
    histories = {}
    for path in subs:
        cur = current[tip, path]
        if not cur or not (root / path / ".git").exists():
            continue
        try:
            histories[path] = subprocess.run(
                ["git", "--literal-pathspecs", "log", f"-{PIN_HISTORY_LIMIT}",
                 "--format=%H", tip, "--", path],
                cwd=root, capture_output=True, text=True, timeout=30,
            ).stdout.split()
        except Exception:
            continue
    historical = _history_tree_pins(root, [(rev, path) for path, revs in histories.items() for rev in revs])
    for path in subs:
        if path not in histories:
            continue
        revs = histories[path]
        cur = current[tip, path]
        candidates = list(dict.fromkeys(historical[rev, path] for rev in revs
                                        if historical[rev, path] not in ("", cur)))
        descendants = _historical_descendants(root / path, cur, candidates)
        seen: set[str] = set()
        for rev in revs:
            old = historical[rev, path]
            if not old or old == cur or old in seen:
                continue
            seen.add(old)
            if old in descendants:
                disclosure = _pin_rollback_disclosed(root, path, rev)
                if disclosure:
                    rep.add(
                        INFO,
                        check,
                        f"{path} pin {cur[:10]} is behind {old[:10]} DELIBERATELY - disclosed",
                        [
                            f"current : {cur}",
                            f"earlier : {old}  (recorded by {rev[:10]})",
                            disclosure,
                        ],
                    )
                    break
                rep.add(
                    FAIL,
                    check,
                    f"{path} pin {cur[:10]} is a STRICT ANCESTOR of {old[:10]}, "
                    f"which this repo recorded earlier - the pin walked BACKWARD",
                    [
                        f"current : {cur}",
                        f"earlier : {old}  (recorded by {rev[:10]})",
                        "a gitlink has no textual content, so a merge picks a side and",
                        "reports NO CONFLICT while the consumer source merges forward",
                    ],
                    [
                        f"git -C {shlex.quote(path)} checkout {old[:12]} && git add {shlex.quote(path)}",
                        "# ...unless the rollback is DELIBERATE. Then say so, in the",
                        "# commit message that moves the pin (same convention as",
                        "# scripts/check_pin_regression.sh - disclosure, not suppression):",
                        f"#     pin-rollback: {path} <why>",
                    ],
                )
                break


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


def locked_config_path_patch(ws: Path, url: str, name: str, req,
                             owner: str | None, packages: list[dict]) -> bool:
    """Whether this member's locked edge uses its workspace-local config patch.

    A second Git version of the same crate can legitimately remain in the lock
    through a transitive dependency. Require the actual member edge to resolve
    uniquely to the path package; the presence of a patch or local package alone
    is insufficient. Unknown version syntax retains the existing finding.
    This is a textual consistency check, not a replacement for --locked replay.
    """
    if not isinstance(req, str) or not all(
        re.fullmatch(r"\s*(?:\^|~|>=|<=|=|>|<)?\s*\d+(?:\.\d+){0,2}\s*", part)
        for part in req.split(",")
    ):
        return False
    # Cargo gives the legacy extensionless file precedence when both exist.
    config = ws / ".cargo/config"
    if not config.exists():
        config = ws / ".cargo/config.toml"
    content, _ = load_toml(config)
    candidates = []
    for source, table in ((content or {}).get("patch") or {}).items():
        if canon_git(source) != url or not isinstance(table, dict):
            continue
        for key, entry in table.items():
            if isinstance(entry, dict) and entry.get("package", key) == name:
                candidates.append(entry)
    if len(candidates) != 1 or not isinstance(candidates[0].get("path"), str):
        return False
    try:
        target = (ws / candidates[0]["path"]).resolve()
    except (OSError, ValueError):
        return False
    manifest, _ = load_toml(target / "Cargo.toml")
    if ((manifest or {}).get("package") or {}).get("name") != name:
        return False
    version = crate_version(target)
    if version is None or _semver(version) is None or not req_allows(req, version):
        return False
    owners = [package for package in packages
              if owner and package.get("name") == owner and "source" not in package]
    if len(owners) != 1:
        return False
    for dependency in owners[0].get("dependencies") or []:
        if not isinstance(dependency, str):
            continue
        fields = dependency.split()
        if not fields or fields[0] != name or len(fields) > 2:
            continue  # an explicit source cannot denote our local path package
        matches = [package for package in packages if package.get("name") == name
                   and (len(fields) == 1 or package.get("version") == fields[1])]
        if (len(matches) == 1 and "source" not in matches[0]
                and matches[0].get("version") == version):
            return True
    return False


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
                    if locked_config_path_patch(ws, url, real, spec.get("version"),
                                                name, pkgs):
                        continue  # this member's locked edge uses a config path patch
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


# The VERSION half of the same cascade. `check_git_pin_cascade` compares only
# the git revs a graph manifest pins, and the fast tier compares versions only
# for workspace MEMBERS, so a submodule crate that this lock resolves from a
# local path - a path dependency outside the workspace, or a `[patch]` target -
# could bump its `package.version` with no textual finding anywhere. The lock
# records that version, so `--locked` refuses the moved one.
#
# Measured 2026-09-17: first-party pins moved ay 0.22->0.26, clean 0.8->0.9,
# ty 0.14->0.15 and trust-ir 0.13->0.14, and the standalone
# `crates/trust-spec-temporal` lock still recorded the old versions. The fast
# tier said "39/40 textually consistent" and counted it clean; only the
# network-bound deep tier noticed.
def crate_version_candidates(d: Path, repo_root: Path) -> set[str]:
    """Every version cargo could give crate `d`.

    A literal `package.version` is one answer. `version.workspace = true` is
    ambiguous for crates that overlapping workspaces both build: the repository
    root resolves `crates/trust-budget` against ITS `[workspace.package]`
    (0.9.0), not against `crates/Cargo.toml` (0.1.0) above the crate. So every
    ancestor workspace's version is accepted, and the caller reports only when
    NONE of them is in the lock; an unsure answer stays quiet.
    """
    man, _ = load_toml(d / "Cargo.toml")
    v = ((man or {}).get("package") or {}).get("version")
    if isinstance(v, str):
        return {v}
    if not (isinstance(v, dict) and v.get("workspace") is True):
        return set()
    out: set[str] = set()
    one = crate_version(d)
    if one is not None:
        out.add(one)
    cur = d.parent
    while True:
        wm, _ = load_toml(cur / "Cargo.toml")
        wv = (((wm or {}).get("workspace") or {}).get("package") or {}).get("version")
        if isinstance(wv, str):
            out.add(wv)
        if cur == repo_root or cur.parent == cur:
            break
        cur = cur.parent
    return out


def declared_local_dependency_names(root: Path, directory: Path, manifest: dict) -> set[str] | None:
    """A conservative union, not a resolved dependency graph.

    Include optional/dev/all-target declarations even when this invocation does not select them.
    A name absent from this superset cannot be a direct Cargo dependency. Missing or ambiguous
    workspace inheritance stays unknown rather than manufacturing an orphan finding.
    """
    if not isinstance(manifest, dict):
        return None
    package = manifest.get("package", {})
    if not isinstance(package, dict):
        return None
    tables = [manifest]
    targets = manifest.get("target", {})
    if not isinstance(targets, dict) or not all(isinstance(value, dict) for value in targets.values()):
        return None
    tables.extend(targets.values())
    names: set[str] = set()
    for table in tables:
        for kind in ("dependencies", "build-dependencies", "dev-dependencies",
                     "build_dependencies", "dev_dependencies"):
            deps = table.get(kind, {})
            if not isinstance(deps, dict):
                return None
            for alias, spec in deps.items():
                if not isinstance(alias, str) or not isinstance(spec, (str, dict)):
                    return None
                if isinstance(spec, dict) and spec.get("workspace") is True:
                    # Overlapping workspaces can supply different inherited specs. Only a
                    # complete, unanimous package-name association supports this fast finding.
                    explicit = package.get("workspace")
                    if explicit is not None and not isinstance(explicit, str):
                        return None
                    owners = []
                    if isinstance(explicit, str):
                        owners = [(directory / explicit).resolve()]
                    else:
                        current = directory
                        while True:
                            content, _ = load_toml(current / "Cargo.toml")
                            if isinstance((content or {}).get("workspace"), dict):
                                owners.append(current)
                            if current == root or current.parent == current:
                                break
                            current = current.parent
                    inherited_names = set()
                    if not owners:
                        return None
                    for owner in owners:
                        content, _ = load_toml(owner / "Cargo.toml")
                        workspace = content.get("workspace") if isinstance(content, dict) else None
                        if not isinstance(workspace, dict):
                            return None
                        dependencies = workspace.get("dependencies", {})
                        if not isinstance(dependencies, dict):
                            return None
                        inherited = dependencies.get(alias)
                        if isinstance(inherited, str):
                            inherited_names.add(alias)
                        elif isinstance(inherited, dict) and isinstance(inherited.get("package", alias), str):
                            inherited_names.add(inherited.get("package", alias))
                        else:
                            return None
                    if len(inherited_names) != 1:
                        return None
                    names.update(inherited_names)
                else:
                    name = spec.get("package", alias) if isinstance(spec, dict) else alias
                    if not isinstance(name, str):
                        return None
                    names.add(name)
    # Cargo accepts underscore/hyphen spellings in several name contexts. Equating them here
    # only widens the declared superset; it cannot invent an orphan refusal.
    return {name.replace("_", "-") for name in names}


def orphaned_local_lock_edges(root: Path, ws: Path, lock: dict) -> list[tuple[str, str, str]]:
    """Definite extra direct edges of unambiguously associated local package rows only.

    Reuse the conservative resolver-input walk (optional paths and config patches included).
    An incomplete walk or conflicting local owner is unknown. Sourced package rows are never
    judged from a local manifest. This does not establish overall lock freshness or replace
    Cargo's deep/--frozen resolution.
    """
    try:
        paths = _resolver_manifests(ws, _resolver_configs(ws))
    except (OSError, ValueError, TypeError, AttributeError):
        return []
    candidates: dict[tuple[str, str], dict[Path, set[str] | None]] = {}
    for path in paths:
        manifest, _ = load_toml(path)
        package = (manifest or {}).get("package") or {}
        if not isinstance(package, dict):
            continue
        name = package.get("name")
        if not isinstance(name, str):
            continue
        directory = path.parent.resolve()
        declared = declared_local_dependency_names(root, directory, manifest)
        for version in crate_version_candidates(directory, root):
            candidates.setdefault((name, version), {})[directory] = declared
    bad = []
    for package in lock.get("package") or []:
        if not isinstance(package, dict) or "source" in package:
            continue
        owners = candidates.get((package.get("name"), package.get("version")), {})
        if len(owners) != 1:
            continue
        directory, declared = next(iter(owners.items()))
        edges = package.get("dependencies", [])
        if declared is None or not isinstance(edges, list) or not all(isinstance(edge, str) for edge in edges):
            continue
        for edge in edges:
            parts = edge.split()
            if parts and parts[0].replace("_", "-") not in declared:
                bad.append((package["name"], edge, rel(root, directory)))
    return sorted(set(bad))


def check_path_version_cascade(root: Path, workspaces: list[Path], rep: Report) -> None:
    check = "2a. GIT-PIN CASCADE (submodule manifest -> parent lock)"

    for ws in workspaces:
        wsname = rel(root, ws) or "."
        lock, _ = load_toml(ws / "Cargo.lock")
        if lock is None:
            continue  # already a FAIL from the fast tier
        lock_local: dict[str, set[str]] = {}
        lock_sourced: set[str] = set()
        for p in lock.get("package") or []:
            if "source" in p:
                lock_sourced.add(p.get("name", ""))
            else:
                lock_local.setdefault(p.get("name", ""), set()).add(p.get("version", ""))
        unused: dict[str, set[str]] = {}
        for p in ((lock.get("patch") or {}).get("unused") or []):
            if isinstance(p, dict) and "source" not in p:
                unused.setdefault(p.get("name", ""), set()).add(p.get("version", ""))

        members = {Path(m).parent.resolve() for m in workspace_manifests(ws)}
        # (crate, local version, lock versions, declared at, how it is reached)
        bad: set[tuple[str, str, str, str, str]] = set()

        # (1) Non-optional path dependencies reached from outside the workspace.
        for d, _is_member in graph_manifests(ws):
            if d.resolve() in members:
                continue  # the fast tier owns member versions
            man, _ = load_toml(d / "Cargo.toml")
            name = ((man or {}).get("package") or {}).get("name")
            vers = crate_version_candidates(d, root)
            if not isinstance(name, str) or not vers:
                continue
            have = lock_local.get(name)
            if have is None or vers & have:
                continue  # absent: not provably in this graph; present: consistent
            bad.add((name, "/".join(sorted(vers)), "/".join(sorted(have)), rel(root, d),
                     "path dependency"))

        # (2) Path `[patch]` targets. A patch that cargo APPLIED leaves the name
        # only as a source-less package, and an unused one leaves a
        # `[[patch.unused]]` row; either records the target's version. A name
        # that also has a git/registry package may be a DECLINED patch, whose
        # local version legitimately differs, so it is left alone.
        rman, _ = load_toml(ws / "Cargo.toml")
        for _src, tbl in ((rman or {}).get("patch") or {}).items():
            if not isinstance(tbl, dict):
                continue
            for key, entry in tbl.items():
                if not isinstance(entry, dict) or not isinstance(entry.get("path"), str):
                    continue
                real = entry.get("package", key)
                if not isinstance(real, str) or real in lock_sourced:
                    continue
                try:
                    target = (ws / entry["path"]).resolve()
                except (ValueError, OSError):
                    continue
                vers = crate_version_candidates(target, root)
                if not vers:
                    continue
                for have, how in ((lock_local.get(real), "[patch] target"),
                                  (unused.get(real), "unused [patch] target")):
                    if have is not None and not vers & have:
                        bad.add((real, "/".join(sorted(vers)), "/".join(sorted(have)),
                                 rel(root, target), how))

        orphaned = orphaned_local_lock_edges(root, ws, lock)
        if orphaned:
            sev, why = lock_severity(root, ws)
            rep.add(sev, check,
                    f"{wsname}: lock records {len(orphaned)} ORPHANED local-package dependency edge(s)",
                    [f"edge     : {name} -> {edge}  ({where})" for name, edge, where in orphaned[:8]]
                    + [why, "no normal/build/dev/target declaration or unambiguous inherited alias names this dependency; "
                       "this is a definite stale edge, not a complete lock-freshness proof"],
                    [f"targo metadata --offline --manifest-path {wsname}/Cargo.toml --format-version 1 >/dev/null",
                     f"git -C {root} diff -- {wsname}/Cargo.lock  # inspect the minimal local dependency-edge change"])
        if not bad:
            continue

        sev, why = lock_severity(root, ws)
        detail = [f"version  : {name} local={ver} lock={have}  ({how}, {where})"
                  for name, ver, have, where, how in sorted(bad)[:8]]
        if len(bad) > 8:
            detail.append(f"... and {len(bad) - 8} more")
        detail.append(why)
        detail.append("the crate that moved is resolved from a local path but is NOT a "
                      "member of this workspace, so the member-version check cannot see it.")
        rep.add(sev, check,
                f"{wsname}: lock records a STALE version for {len(bad)} local-path crate(s) "
                f"({'--locked WILL fail' if sev == FAIL else 'not on any build path'})",
                detail,
                [f"targo metadata --offline --manifest-path {wsname}/Cargo.toml "
                 f"--format-version 1 >/dev/null   # MINIMAL resolve",
                 f"git -C {root} diff --stat -- {wsname}/Cargo.lock"
                 f"   # CONFIRM only local-path versions/edges moved",
                 "# an `unused [patch] target` row is better deleted from the manifest "
                 "(docs/KNOWN_HAZARDS.md, `[[patch.unused]]`)",
                 "# NEVER a bare `targo update` / `cargo update`: it downgraded ay "
                 "0.4.0->0.3.0 and manufactured a futures-core conflict."])


# --------------------------------------------------------------------------
# deep-tier result cache
#
# The deep probe is authoritative and expensive: 13-35s on this tree against
# ~2s for the fast tier, and it needs the network. Paying that on every
# `x.py build` is how `TRUST_SKIP_PREFLIGHT=1` ends up exported in a shell
# profile, at which point the checker protects nothing at all. So the verdict
# is cached against resolver lockfiles, local manifests and Cargo configuration
# contents. Explicit --deep always re-probes; only --deep-if-cached replays.
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
#
# v3: v2 fixed the MANIFEST half of that blind spot and left the LOCK half.
# The key hashed `ws / "Cargo.lock"` - the lock sitting in the workspace's own
# directory - but a workspace that is a MEMBER of a larger one is resolved by
# cargo against its workspace ROOT's lock, and that is the file the verdict is
# actually about. The failure text says so in as many words:
#
#     FAIL  src/tools/miri: resolver CONFIRMS the lock must change
#           error: cannot update the lock file Cargo.lock
#
# Fixing the ROOT lock therefore left three cached FAILs fully "valid", and
# --deep re-reported three already-fixed workspaces as blocking - sending the
# reader to hunt a build breakage that no longer existed. (Observed 2026-08-08
# after a 316-commit submodule pull; the three cleared instantly when probed by
# hand.) The key now covers every lock from `ws` up to the repo root, so a
# change to any lock the resolver could consult invalidates the verdict.
#
# The version bump is load-bearing: it retires every v2 entry, including the
# stale ones this fixes.
# v4: include Cargo's discovered configuration and local patch/dependency
# closure, including virtual/inherited workspace manifests and optional paths.
# Hash contents: preserved timestamps must not preserve an obsolete verdict.
# v5: compiled native Targo now discovers home config through TARGO_HOME when
# the compatibility spelling is absent. Match that input/precedence contract.
# v6: the selected resolver may still be an older seed or the Cargo identity.
# With no explicit CARGO_HOME, key both default and native home candidates.
DEEP_CACHE_VERSION = 6


def _deep_cache_path(root: Path) -> Path:
    return root / "build" / "preflight-deep-cache.json"


def _resolver_locks(ws: Path) -> list[Path]:
    """Every lockfile the resolver could consult when resolving `ws`.

    `ws` upward to the repo root. A workspace that is a MEMBER of a larger one
    has no lock of its own that cargo honours - it is resolved against its
    workspace root's - so hashing only `ws / "Cargo.lock"` keys the verdict on
    a file that had nothing to do with it. Walking up costs a handful of
    stat(2)s and catches both: the workspace's own lock when it has one, and
    the ancestor lock cargo actually used when it does not.
    """
    out: list[Path] = []
    seen: set[Path] = set()
    try:
        d = ws.resolve()
        root = Path(__file__).resolve().parent.parent
    except OSError:
        return out
    while True:
        lp = d / "Cargo.lock"
        if lp.is_file() and lp not in seen:
            seen.add(lp)
            out.append(lp)
        if d == root or d.parent == d:
            break
        d = d.parent
    return sorted(out)


def _resolver_configs(ws: Path) -> list[Path]:
    """Conservative cwd/home discovery across seed and native frontends."""
    home_value = os.environ.get("CARGO_HOME")
    if home_value is None:
        # Older seeds and the compatibility identity ignore TARGO_HOME, while
        # the current native frontend honors it. Neither interpretation may
        # reuse a verdict after one of its resolver inputs has changed.
        homes = [Path.home() / ".cargo"]
        native_home = os.environ.get("TARGO_HOME")
        if native_home:
            homes.append(Path(native_home))
    else:
        # Presence wins, including empty: it selects the default OS home and
        # suppresses the native spelling for every supported generation.
        homes = [Path(home_value) if home_value else Path.home() / ".cargo"]
    directories = [d / ".cargo" for d in (ws, *ws.parents)] + [
        home if home.is_absolute() else ws / home for home in homes
    ]
    found: set[Path] = set()

    def visit(path: Path, active: set[Path]) -> None:
        # Cargo keeps the discovered filename as the relative-value anchor,
        # even when the configuration itself is a symlink.
        path = Path(os.path.abspath(path))
        if path in active:
            raise ValueError("incomplete Cargo config walk")
        if path in found:
            return
        if len(found) >= GRAPH_CAP:
            raise ValueError("incomplete Cargo config walk")
        content, error = load_toml(path)
        if error:
            raise ValueError(error)
        found.add(path)
        includes = content.get("include", [])
        if not isinstance(includes, list):
            raise ValueError("unknown Cargo config include")
        for entry in includes:
            name = entry.get("path") if isinstance(entry, dict) else entry
            if not isinstance(name, str):
                raise ValueError("unknown Cargo config include path")
            target = path.parent / name
            if isinstance(entry, dict) and entry.get("optional") is True and not target.exists():
                continue
            visit(target, active | {path})

    for directory in directories:
        legacy = directory / "config"
        path = legacy if legacy.exists() else directory / "config.toml"
        if path.exists():
            visit(path, set())
    return sorted(found)


def _resolver_manifests(ws: Path, configs: list[Path]) -> set[Path]:
    """Conservative local resolver inputs, separate from textual-check coverage."""
    owner = nearest_workspace_root(ws) or ws
    members = {m.parent.resolve() for m in workspace_manifests(owner)}
    queue = [ws, owner, *members]
    found: set[Path] = set()
    seen: set[Path] = set()

    def patches(content: dict, base: Path) -> None:
        patch = content.get("patch") or {}
        if not isinstance(patch, dict):
            raise ValueError("unknown Cargo patch table")
        tables = list(patch.values())
        tables.append(content.get("replace") or {})
        for table in tables:
            if not isinstance(table, dict):
                raise ValueError("unknown Cargo patch/replace table")
            for entry in table.values():
                if isinstance(entry, dict) and isinstance(entry.get("path"), str):
                    queue.append((base / entry["path"]).resolve())

    for path in configs:
        content, _ = load_toml(path)
        # Cargo's Definition::root resolves config values from its grandparent,
        # including values introduced by an included configuration file.
        patches(content, path.parent.parent)
        overrides = content.get("paths", [])
        if not isinstance(overrides, list):
            raise ValueError("unknown Cargo path overrides")
        for override in overrides:
            if not isinstance(override, str):
                raise ValueError("unknown Cargo path override")
            queue.append((path.parent.parent / override).resolve())

    while queue:
        d = queue.pop().resolve()
        if d in seen:
            continue
        if len(seen) >= GRAPH_CAP:
            raise ValueError("incomplete local resolver manifest walk")
        seen.add(d)
        path = d / "Cargo.toml"
        content, error = load_toml(path)
        if error:
            raise ValueError(error)
        found.add(path)
        inherited = nearest_workspace_root(d)
        if inherited is not None:
            found.add(inherited / "Cargo.toml")
        patches(content, d)
        for name, spec in iter_graph_dep_specs(content, with_dev=d in members):
            base, spec = inherit_dep(d, name, spec)
            if isinstance(spec, dict) and isinstance(spec.get("path"), str):
                if "base" in spec:
                    raise ValueError("unmodeled Cargo path base")
                queue.append((base / spec["path"]).resolve())
    return found


def _deep_cache_key(ws: Path, targo: str) -> str:
    h = hashlib.sha256()
    h.update(f"v{DEEP_CACHE_VERSION}\0{targo}\0".encode())
    try:
        locks = _resolver_locks(ws)
        if not locks:
            return ""
        configs = _resolver_configs(ws)
        inputs = set(locks) | set(configs) | _resolver_manifests(ws, configs)
        for path in sorted(inputs):
            h.update(f"{path}\0".encode())
            h.update(hashlib.sha256(path.read_bytes()).digest())
        if targo:
            st = Path(targo).stat()
            h.update(f"{st.st_size}:{st.st_mtime_ns}\0".encode())
    except (OSError, ValueError, TypeError, AttributeError):
        # An incomplete/unrecognized input walk may cost a fresh deep probe,
        # never authorize replay of an incompletely keyed verdict.
        return ""
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
        if (cached_only and keys[ws] and isinstance(ent, dict) and ent.get("key") == keys[ws]
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
                 "cached: resolver locks, local manifests and Cargo configs are unchanged",
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
            cwd=ws, timeout=timeout, env=env,
        )
        return ws, rc, err, time.time() - t0

    results = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool:
        for r in pool.map(probe, workspaces):
            results.append(r)

    inconclusive: list[list[str]] = []
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
            # A wrapper's first error may only name the failed command. Keep
            # the final cause too, without guessing that every failure was a
            # network problem or claiming that lock coherence was established.
            diagnostic = err.strip() or "metadata probe returned no stderr"
            if len(diagnostic) > 4096:
                diagnostic = (diagnostic[:2048] + "\n... stderr middle omitted ...\n"
                              + diagnostic[-2048:])
            inconclusive.append([f"{wsname}: rc={rc} ({dt:.1f}s)"]
                                + [f"  {line}" for line in diagnostic.splitlines()])
            # NOT cached: a failed probe establishes neither clean nor skewed.
            cache.pop(wsname, None)

    if inconclusive:
        rep.add(WARN, check,
                f"{len(inconclusive)} workspace(s) INCONCLUSIVE (metadata probe failed)",
                [line for workspace in inconclusive[:10] for line in workspace],
                ["# resolve the reported error, then re-run tools/preflight.sh --deep"])
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
            fix.append(f"{SUBMODULE_RESTORE}   # materialise {man_rel}")
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
def names_this_checkout(cmd: str, root: Path) -> bool:
    """True when `cmd` names `root` itself or a path INSIDE it.

    A bare substring test (`str(root) in cmd`) also matched every SIBLING
    checkout whose path merely starts with this one: with worktrees named
    `trust-wt` and `trust-wt-b2`, a `.../trust-wt-b2/build/bootstrap/debug/bootstrap
    test ...` running in the sibling was reported as a build of `trust-wt`, and
    `x.py build` in `trust-wt` refused with "AN x.py BUILD IS ALREADY RUNNING"
    although the two checkouts share no build directory (measured 2026-09-23).

    The root is named when the line ends after it or the next character is one
    a directory NAME cannot continue with -- anything but `[A-Za-z0-9._-]`. That
    is `/`, whitespace and quotes, and equally `=`, `:` and `,`
    (`--remap-path-prefix=<root>=/src`, `native=<root>:/opt/lib`,
    `<root>,/elsewhere`), which a LIST of separators misses (review 2026-09-29,
    the same boundary as `scripts/submodule_sync.sh`). A sibling checkout never
    matches: its path continues the root with a name character (`-b2`, `.old`,
    `_old`, `x`).
    """
    return re.search(re.escape(str(root)) + r"(?![A-Za-z0-9._-])", cmd) is not None


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
        #
        # 2026-08-28: it caught a second one, and the ancestor walk above cannot
        # help. Searching the WHOLE command line cannot tell a process that IS a
        # build from one that merely QUOTES the invocation -- `zsh -c '... x.py
        # build ...'` and `daemonize.py -- ... x.py build ...` both contain the
        # pattern and the root path. The ancestor exclusion misses them whenever
        # the launcher is not an ancestor, which is exactly what a fork+setsid
        # daemonizer produces: the daemon reparents to PID 1, so its launching
        # shell is a SIBLING, still alive, still carrying the text. A stale
        # launcher then blocks every future build with "ALREADY RUNNING" while
        # `pgrep -x bootstrap` shows nothing.
        #
        # Anchor on argv[0] -- the thing actually executing -- instead of on the
        # line. A real build is `.../bootstrap`, `.../x.py`, or a Python
        # interpreter whose argv[1] is x.py/bootstrap.py. It is never a shell,
        # and never a wrapper that happens to mention them.
        argv = cmd.split()
        argv0 = argv[0] if argv else ""
        argv1 = argv[1] if len(argv) > 1 else ""
        exe_is_bootstrap = re.search(
            r"(x\.py|bootstrap\.py|build/bootstrap/[^/]+/bootstrap)$", argv0
        )
        exe_is_python_running_bootstrap = bool(
            re.search(r"/(python[0-9.]*|Python)$", argv0)
            and re.search(r"(x\.py|bootstrap\.py)$", argv1)
        )
        looks_like_bootstrap = exe_is_bootstrap or exe_is_python_running_bootstrap
        subcmd = re.search(r"\b(build|check|test|dist|install|doc)\b", cmd)
        # The root must appear as a WHOLE path component (`names_this_checkout`).
        # A bare substring test matched every sibling checkout whose path merely
        # starts with this one (2026-09-24: a stage-2 build in `<home>/
        # trust-land/toolchain-build` — its own build dir and lock — blocked every
        # build of `<home>/trust`; 2026-09-23: `trust-wt-b2` blocked
        # `trust-wt`).
        if looks_like_bootstrap and names_this_checkout(cmd, root) and subcmd:
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
        label = rel(root, stage_bin)
        if "trustc" not in names and "rustc" not in names:
            # A sysroot bin/ that exists but carries NO COMPILER is an
            # INTERRUPTED BUILD, not an absent one. `x.py build --stage 2`
            # empties this directory and refills it at the end, so a crash or a
            # ^C in between leaves exactly this shape.
            #
            # This used to `continue`, which made the most expensive failure in
            # the tree invisible: every downstream gate resolves the toolchain
            # through $TRUST_STAGE2_BIN (default build/host/stage2/bin), so an
            # empty stage2 silently demotes them to stock cargo, which then dies
            # at flag-parse on `-Ztrust-verify=*`. The consumer sees a wall of
            # toolchain text listing several hypotheses; the one fact that
            # settles it -- "your stage2 has no compiler in it" -- was known
            # here and thrown away. (Cost a real incident on 2026-08-03: a crash
            # mid-bootstrap emptied stage2/bin, and every aterm push was blocked
            # with no single command that named the cause.)
            rep.add(WARN, check,
                    f"sysroot {label} exists but carries NO COMPILER - INTERRUPTED BUILD",
                    [f"contains {len(names)} entr{'y' if len(names) == 1 else 'ies'}"
                     + (f": {', '.join(sorted(names)[:6])}" if names else " (empty)"),
                     "this is the shape a crashed/^C'd `x.py build` leaves behind",
                     "anything resolving the toolchain through this path (push hooks,",
                     "  targo, TRUST_STAGE2_BIN) silently falls back to stock cargo and",
                     "  then fails at flag-parse on -Ztrust-verify - a confusing error",
                     "  whose real cause is this directory"],
                    ["python3 x.py build --stage 2   # finish the interrupted build"])
            continue
        missing = [b for b in backends if b not in names]
        if missing:
            rep.add(WARN, check,
                    f"existing sysroot {label} has NO {', '.join(missing)}",
                    ["this is failure-mode 6 already materialised: it compiles, cannot verify",
                     f"present: {', '.join(sorted(n for n in names if n in backends)) or 'none'}"],
                    ["# rebuild after fixing [build] tools; then re-check this path"])
        else:
            rep.add(OK, check, f"existing sysroot {label} has all backends: {', '.join(backends)}")


def check_config_drift(root: Path, cfg: dict, rep: Report) -> None:
    """bootstrap.toml is gitignored, so it silently rots.

    It CANNOT be committed: it carries absolute, machine-local paths (the
    genesis-stage0 driver paths, [build] python, [install] prefix). Checking in
    one developer's /Users/... would break every other clone, which is exactly
    why upstream gitignores config.toml too.

    But gitignored means no diff, no review, and no signal when the generator
    moves — and `recreate_bootstrap.py` deliberately WILL NOT overwrite an
    existing bootstrap.toml without --force-config. So a config written months
    ago keeps being used forever while the canonical list gains entries. That is
    not hypothetical: the 2026-07-31 commit that added `clean` and `ty` to the
    generator never reached this machine's config, and the resulting toolchain
    would have compiled but not verified (failure-mode 6) had the tools audit
    above not caught it independently.

    So: keep the file gitignored, and make the DRIFT visible instead. We compare
    only [build] tools — the field whose omissions are load-bearing. Paths are
    supposed to differ per machine and are not compared.
    """
    check = "3. TOOLS ALLOWLIST AUDIT"
    gen = root / "scripts/recreate_bootstrap.py"
    if not gen.exists():
        return
    try:
        src = gen.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return
    m = re.search(r'^CONFIG_TEMPLATE = """\\\n(.*?)^"""', src, re.S | re.M)
    if not m:
        # Template moved or was restructured. Stay SILENT rather than guess:
        # this file's own rule is that a checker which can lie is worse than no
        # checker, and a bad regex here would report false drift on every run.
        return
    tm = re.search(r"^tools = \[(.*?)^\]", m.group(1), re.S | re.M)
    if not tm:
        return
    canonical = [t for t in re.findall(r'"([^"]+)"', tm.group(1))]
    live = (cfg.get("build") or {}).get("tools")
    if not isinstance(live, list) or not canonical:
        return
    missing = [t for t in canonical if t not in live]
    extra = [t for t in live if t not in canonical]
    if not missing and not extra:
        rep.add(OK, check, "bootstrap.toml [build] tools matches scripts/recreate_bootstrap.py")
        return
    detail = []
    if missing:
        detail.append(f"MISSING vs generator: {', '.join(missing)}")
    if extra:
        detail.append(f"present but NOT in generator: {', '.join(extra)}")
    detail.append("bootstrap.toml is gitignored (machine-local paths), so this drift is")
    detail.append("  invisible to git; the recreator will not overwrite it without --force-config")
    rep.add(WARN, check, "bootstrap.toml [build] tools has DRIFTED from the generator", detail,
            ["python3 scripts/recreate_bootstrap.py --force-config"
             "   # regenerate (rewrites machine paths too - re-check them after)"])


def check_misc(root: Path, cfg: dict, rep: Report, *, standalone_tool: bool = False) -> None:
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
        if not standalone_tool and backend == "trust-cg" and not (root / "first-party/trust-cg/Cargo.toml").exists():
            rep.add(FAIL, check, "codegen-backends lists trust-cg but its source is absent", [],
                    [SUBMODULE_RESTORE])

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
@contextmanager
def build_phase(name: str, enabled: bool):
    """Disclose build-check latency without changing a check's verdict."""
    if not enabled:
        yield
        return

    def progress(message: str) -> None:
        try:
            print(f"preflight: phase {name} {message}", file=sys.stderr, flush=True)
        except (OSError, ValueError):
            # Progress is best effort, including when stderr has been closed.
            # It must neither change a verdict nor mask the check's exception.
            pass

    started = time.monotonic()
    progress("start")
    try:
        yield
    finally:
        # END is a timing boundary, not a successful-check verdict.
        progress(f"end elapsed={time.monotonic() - started:.3f}s")


def find_targo(root: Path, override: str | None) -> str:
    if override:
        return override
    cands = list((root / "build").glob("*/stage0-sysroot/bin/targo"))
    cands += list((root / "build").glob("host/stage*/bin/targo"))
    for c in cands:
        if c.is_file() and os.access(c, os.X_OK):
            return str(c)
    return shutil.which("targo") or ""



def validate_standalone_tool_sources(root: Path, rep: Report) -> bool:
    """Reinspect locked selected graphs; a saved preparation verdict grants nothing."""
    check = "SELECTED STANDALONE TOOL SOURCES"
    try:
        state = json.loads((root / "build/tool-source-preparation/targo-build-tool.json").read_text())
        if (state["schema"] != "trust.tool-source-preparation.v1"
                or state["tool"] != "targo-build-tool" or state["scope"] != "tool-only"
                or state["compiler_sources_ready"] is not False or state["first_party"] != "deferred"):
            raise ValueError("invalid deferred tool-source scope")
        inspector = Path(state["inspector_path"])
        if not inspector.is_absolute() or inspector.resolve(strict=True) != inspector:
            raise ValueError("source inspector must be a physical absolute executable")
        if hashlib.sha256(inspector.read_bytes()).hexdigest() != state["inspector_sha256"]:
            raise ValueError("source inspector changed")
        expected = ["src/bootstrap/Cargo.toml", "src/tools/targo/Cargo.toml"]
        if [g["manifest"] for g in state["graphs"]] != expected:
            raise ValueError("selected source graph census differs")
        for graph in state["graphs"]:
            manifest = root / graph["manifest"]
            inputs = (manifest, manifest.with_name("Cargo.lock"))
            before = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}
            if before != graph["inputs_sha256"]:
                raise ValueError("selected manifest/lock changed since preparation")
            command = [str(inspector), "metadata", "--locked", "--offline", "--format-version", "1",
                       "--manifest-path", str(manifest)]
            environment = os.environ.copy()
            environment["RUSTC"] = str(inspector.with_name("trustc"))
            result = subprocess.run(command, cwd=root, env=environment, capture_output=True, timeout=120)
            if result.returncode:
                raise ValueError("selected locked metadata refused: " + result.stderr.decode(errors="replace")[:500])
            document = json.loads(result.stdout)
            if document.get("version") != 1 or not document.get("packages"):
                raise ValueError("unsupported or empty selected graph")
            for package in document["packages"]:
                actual = Path(package["manifest_path"]).resolve(strict=True)
                if actual.is_relative_to(root / "first-party"):
                    raise ValueError("selected tool requires deferred first-party source")
            if before != {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}:
                raise ValueError("selected inputs changed during inspection")
        rep.add(OK, check, "locked bootstrap/frontend graphs inspected; full compiler sources remain deferred", [])
        return True
    except (OSError, ValueError, KeyError, TypeError, subprocess.TimeoutExpired) as error:
        rep.add(FAIL, check, "standalone tool-source validation refused", [str(error)])
        return False


def main() -> int:
    ap = argparse.ArgumentParser(prog="preflight", description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--repo-root", default=str(Path(__file__).resolve().parent.parent))
    ap.add_argument("--bootstrap-toml", default=None,
                    help="audit a candidate config instead of <repo>/bootstrap.toml")
    ap.add_argument("--bootstrap-cwd", default=None,
                    help=argparse.SUPPRESS)
    ap.add_argument("--set", dest="bootstrap_set", action="append", default=[],
                    help="apply a bootstrap --set override before auditing")
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
    ap.add_argument("--selected-tool", choices=("targo-build-tool",), default=None,
                    help="Standalone build-tool graph only; never compiler/sysroot readiness")
    ap.add_argument("--only", default=None,
                    help="comma-separated subset: submodules,lockfiles,tools,env")
    args = ap.parse_args()

    t0 = time.time()
    root = Path(args.repo_root).resolve()
    color = (not args.no_color) and sys.stdout.isatty() and os.environ.get("NO_COLOR") is None
    rep = Report(color)

    only = set(args.only.split(",")) if args.only else {"submodules", "lockfiles", "tools", "env"}
    checks_run: list[str] = []

    standalone_tool = False
    if args.selected_tool:
        checks_run.append("SELECTED STANDALONE TOOL SOURCES")
        standalone_tool = validate_standalone_tool_sources(root, rep)

    bootstrap_cwd = Path(args.bootstrap_cwd).resolve() if args.bootstrap_cwd else Path.cwd()
    with build_phase("bootstrap-config", args.for_build):
        cfg, cfg_path, cfg_err = resolve_bootstrap_config(
            root,
            args.bootstrap_toml,
            args.bootstrap_set,
            bootstrap_cwd,
        )

    with build_phase("bootstrap-facts", args.for_build):
        facts = read_bootstrap_facts(root)

    if "submodules" in only:
        checks_run.append("1. SUBMODULE DRIFT")
        with build_phase("submodules", args.for_build):
            check_submodules(root, rep, deferred_first_party=standalone_tool)
        with build_phase("bootstrap-submodule-policy", args.for_build):
            check_bootstrap_submodule_policy(root, cfg, rep)
        with build_phase("pin-regression", args.for_build):
            check_pin_regression(root, rep)
        with build_phase("pin-behind-history", args.for_build):
            check_pin_behind_history(root, rep)

    workspaces: list[Path] = []
    if "lockfiles" in only:
        checks_run.append("2. LOCKFILE SKEW (non-mutating)")
        with build_phase("workspace-discovery", args.for_build):
            workspaces = discover_workspaces(root, facts, args.depth, args.all_workspaces)
        with build_phase("lockfiles-fast", args.for_build):
            check_lockfiles_fast(root, workspaces, rep)
        checks_run.append("2a. GIT-PIN CASCADE (submodule manifest -> parent lock)")
        with build_phase("git-pin-cascade", args.for_build):
            check_git_pin_cascade(root, workspaces, rep)
        with build_phase("path-version-cascade", args.for_build):
            check_path_version_cascade(root, workspaces, rep)
        with build_phase("lock-mtimes", args.for_build):
            check_lock_mtimes(root, workspaces, rep)
        if args.deep or args.deep_if_cached:
            checks_run.append("2b. LOCKFILE SKEW (deep, `metadata --locked`)")
            with build_phase("lockfiles-deep", args.for_build):
                check_lockfiles_deep(root, workspaces, rep,
                                     find_targo(root, args.targo), args.timeout, args.jobs,
                                     cached_only=not args.deep)

    if "tools" in only and not standalone_tool:
        checks_run.append("3. TOOLS ALLOWLIST AUDIT")
        if cfg_err:
            rep.add(FAIL, "3. TOOLS ALLOWLIST AUDIT",
                    f"cannot read {cfg_path}: {cfg_err}", [],
                    ["cp bootstrap.example.toml bootstrap.toml  # then edit"])
        else:
            with build_phase("tool-model", args.for_build):
                model = build_tool_model(root, cfg, facts)
            with build_phase("tools-allowlist", args.for_build):
                check_tools_allowlist(root, cfg, facts, rep, cfg_path, model)
            with build_phase("model-vs-sysroot", args.for_build):
                check_model_vs_sysroot(root, facts, model, rep)

    if "env" in only:
        checks_run.append("4. BUILD ENVIRONMENT")
        with build_phase("concurrent-build", args.for_build):
            check_concurrent_build(root, rep, args.for_build)
        with build_phase("existing-sysroot", args.for_build):
            check_existing_sysroot(root, cfg, facts, rep)
        with build_phase("config-drift", args.for_build):
            check_config_drift(root, cfg, rep)
        with build_phase("misc", args.for_build):
            check_misc(root, cfg, rep, standalone_tool=standalone_tool)

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
