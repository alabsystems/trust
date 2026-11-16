#!/usr/bin/env python3
"""trust_ir_cg_census.py — what the trust-ir → trust-cg backend REFUSES in a real crate.

The self-host campaign (docs/campaigns/2026-09-10-selfhost-trust-ir-cg.md, gate
G3) steers by data: before widening the backend, measure every refusal it
reports over a real library crate and rank them. This script is that
instrument. It compiles one library crate (default: `library/core`) with an
EXISTING trustc, selecting the `trust-ir-cg` backend explicitly, and harvests
the backend's refusal surfaces — the crate-level fatal that lists every FAILED
ROOT, the per-function "skipped Rust-internal function" notes, and (with
`--diag-json`, which passes the tracked `-Ztrust-ir-cg-args=diag-json`) the typed
JSON stream — into

    <out-dir>/refusals.jsonl      every refusal, verbatim
    <out-dir>/gap_table.md        ranked: diagnostic code -> count, examples
    <out-dir>/provenance.json     compiler identity, backend, flags, exit code
    <out-dir>/stderr.log          the complete compiler stderr

Honesty rules:
  * The compiler's exit code is recorded and printed. A crate that compiles is
    NOT evidence of a correct object — only that no gate refused it.
  * A non-JSON `error:` line (an ICE, a fatal outside the backend, a missing
    dylib) is a HARNESS failure, reported first-class as `harness_errors`,
    never folded into the gap table.
  * Nothing here builds anything. Point it at a stage compiler that already
    carries `codegen-backends/librustc_codegen_trust-ir-cg-<release>.dylib`
    (bootstrap installs it when `rust.codegen-backends` lists `trust-ir-cg`),
    or pass `--backend /path/to/dylib` to load one by path.

Usage:
  python3 scripts/trust_ir_cg_census.py \
      --trustc build/host/stage1/bin/trustc \
      --crate core --out-dir reports/trust-ir-cg-census/$(date +%F)-core
  # `--crate alloc` needs `core` and `compiler_builtins`; the census resolves
  # them from the trustc's own sysroot and records how in provenance `deps`.

Author: Andrew Yates | Copyright 2026 | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import argparse
import collections
import datetime as _dt
import json
import os
import re
import shlex
import subprocess
import sys
import time
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]

# Standalone-compile recipes for the library crates. `core` is a leaf; the
# others depend on the crates below them. `deps` is READ: every entry must
# resolve, either from the driven trustc's own sysroot (an rlib under
# `<sysroot>/lib/rustlib/<host>/lib/lib<dep>-*.rlib`, which needs no flag —
# rustc finds it by name) or from an explicit `--extern <dep>=<path>` on this
# script's command line, which is forwarded verbatim. A dep that resolves
# neither way is a refusal naming both fixes, never a silent compile that
# fails deep inside name resolution. The resolution of each dep is recorded
# in `provenance.json` under `deps` (omitted for a leaf crate, whose
# provenance is therefore unchanged by this field).
#
# `compiler_builtins` is listed for `alloc` because rustc injects
# `extern crate compiler_builtins` into every `#![no_std]` crate that is not
# `#![no_core]`; the census emits no `--extern` for it as long as the sysroot
# resolves it, exactly like `core`.
CRATES: dict[str, dict] = {
    "core": {
        "path": "library/core/src/lib.rs",
        "edition": "2024",
        "deps": [],
    },
    "alloc": {
        "path": "library/alloc/src/lib.rs",
        "edition": "2024",
        "deps": ["core", "compiler_builtins"],
    },
}


TAG_RE = re.compile(r"\[TCG-[A-Z0-9-]+\]")
SKIPPED_PREFIX = (
    "rustc_codegen_trust_cg: skipped Rust-internal function with unsupported MIR "
    "(not an external root; must be unreachable from the program for the link to succeed): "
)
TRAP_STUB_PREFIX = "rustc_codegen_trust_cg: emitted trapping stub for dynamic-dispatch shim `"


def md(text: str, width: int) -> str:
    """Escape a cell for a markdown table and clip it."""
    return text.replace("|", "\\|").replace("\n", " ")[:width]


def reason_key(message: str) -> str:
    """The stable, rankable reason of one refusal message.

    Prefer the backend's own `[TCG-...]` tag when the message carries one;
    otherwise fold the free text to its first clause with numbers, hashes and
    quoted names elided, so two instances of the same gap rank together.
    """
    tag = TAG_RE.search(message)
    if tag:
        return tag.group(0)
    text = message.split("\n", 1)[0]
    text = re.sub(r"`[^`]*`", "`_`", text)
    text = re.sub(r"\b[0-9a-f]{8,}\b", "<hash>", text)
    text = re.sub(r"\d+", "<n>", text)
    for sep in (" (", ": ", "; "):
        if sep in text:
            text = text.split(sep, 1)[0]
    return text.strip()[:100]


ROOT_RE = re.compile(r"^(?P<symbol>\S+)(?: \((?P<class>[^)]*)\))?: (?P<message>.*)$")
# A refused STATIC is reported in a different shape from a refused function:
#   static `sync::STATIC_INNER_SLICE` (symbol `_RNv...`, defined at path:L:C: L:C (#0)): message
# The class parenthetical nests `(#0)`, so `[^)]*` cannot span it; the lazy
# `.*?\): ` stops at the first `): ` that follows the nested group. Without
# this the root landed as symbol `<unknown>` with reason "static `_`".
STATIC_ROOT_RE = re.compile(
    r"^static `(?P<path>[^`]*)` \(symbol `(?P<symbol>[^`]*)`, (?P<class>.*?)\): (?P<message>.*)$"
)


def split_root(entry: str) -> dict:
    """`{symbol} ({class}): {message}` -> {symbol, class, message, reason}.

    The class is the backend's own root classification, e.g. "reachable
    Rust-internal monomorphization, not a std-internal shim"; it is kept but
    is not part of the reason key. A static root (`STATIC_ROOT_RE`) keys on
    its mangled symbol and carries "static `path`, defined at ..." as its
    class.
    """
    m = STATIC_ROOT_RE.match(entry.strip())
    if m:
        message = m.group("message").strip()
        return {
            "symbol": m.group("symbol"),
            "class": f"static `{m.group('path')}`, {m.group('class')}",
            "message": message,
            "reason": reason_key(message),
        }
    m = ROOT_RE.match(entry.strip())
    if not m:
        return {"symbol": "<unknown>", "class": "", "message": entry.strip(), "reason": reason_key(entry)}
    message = m.group("message").strip()
    return {
        "symbol": m.group("symbol"),
        "class": m.group("class") or "",
        "message": message,
        "reason": reason_key(message),
    }


def parse_backend_stderr(stderr: str) -> tuple[list[dict], list[dict], list[dict], list[dict], list[str]]:
    """Harvest the backend's refusal surfaces from one compile's stderr.

    Returns (typed JSON refusals, failed roots, skipped internal functions,
    harness error lines). The failed roots come out of the crate-level
    `TCG-MIR-UNSUPPORTED` object's `fields.failed_roots` (one string, roots
    joined by "\\n  - "); when JSON is absent they are recovered from the human
    fatal's bullet list instead, so the census never silently reports zero.
    """
    refusals: list[dict] = []
    roots: list[dict] = []
    skipped: list[dict] = []
    trap_stubs: list[dict] = []
    harness_errors: list[str] = []
    saw_root_json = False
    for line in stderr.splitlines():
        stripped = line.strip()
        if stripped.startswith("{") and stripped.endswith("}"):
            try:
                obj = json.loads(stripped)
            except json.JSONDecodeError:
                obj = None
            if isinstance(obj, dict) and "code" in obj:
                refusals.append(obj)
                fields = obj.get("fields") or {}
                joined = fields.get("failed_roots") if isinstance(fields, dict) else None
                if isinstance(joined, str) and joined:
                    saw_root_json = True
                    for entry in joined.split("\n  - "):
                        if entry.strip():
                            roots.append(split_root(entry.strip()))
                continue
        if stripped.startswith(SKIPPED_PREFIX):
            skipped.append(split_root(stripped[len(SKIPPED_PREFIX):]))
            continue
        if stripped.startswith(TRAP_STUB_PREFIX):
            # "...shim `SYMBOL` (unlowered body: REASON); reachable only via ..."
            rest = stripped[len(TRAP_STUB_PREFIX):]
            symbol, _, tail = rest.partition("` (unlowered body: ")
            reason = tail.split("); reachable only", 1)[0]
            trap_stubs.append({"symbol": symbol.strip("`"), "message": reason, "reason": reason_key(reason)})
            continue
        if (
            stripped.startswith("error")
            and "TCG-" not in stripped
            and "aborting due to" not in stripped
            and "could not compile" not in stripped
        ):
            harness_errors.append(stripped)
    if not saw_root_json:
        # Human fatal: indented "- {symbol} ({class}): {message}" bullets
        # after the wrapper line, until the next non-bullet line.
        in_list = False
        for line in stderr.splitlines():
            if "cannot compile required function with unsupported MIR" in line:
                in_list = True
                continue
            if in_list:
                stripped = line.strip()
                if stripped.startswith("- "):
                    roots.append(split_root(stripped[2:]))
                else:
                    in_list = False
    return refusals, roots, skipped, trap_stubs, harness_errors


def parse_args(argv: list[str]) -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--trustc", required=True, help="the trustc to drive (a stage sysroot's bin/trustc)")
    p.add_argument("--crate", default="core", choices=sorted(CRATES), help="library crate to compile")
    p.add_argument("--out-dir", required=True, help="directory to write the census into")
    p.add_argument(
        "--backend",
        default=None,
        help="value for -Zcodegen-backend: the installed backend name `trust-ir-cg` (default when "
        "compiling) or a dylib path. Under --reparse there is no default: the provenance records "
        "the value you give, or `reparse: unknown`, never a backend the reparse did not run.",
    )
    p.add_argument(
        "--extern",
        action="append",
        default=[],
        metavar="DEP=PATH",
        help="resolve one of the crate recipe's `deps` from this rlib instead of the sysroot "
        "(repeatable; forwarded verbatim as `--extern DEP=PATH`). Only accepted for a dep the "
        "recipe declares; a dep the sysroot already resolves needs no entry.",
    )
    p.add_argument("--opt-level", default="0", help="-Copt-level (default 0)")
    p.add_argument(
        "--panic",
        default="abort",
        choices=["abort", "unwind"],
        help="-Cpanic strategy (default abort; the self-host needs unwind eventually)",
    )
    p.add_argument(
        "--src",
        default=None,
        help="override the crate's lib.rs (e.g. an installed toolchain's rust-src copy of core, "
        "when the trustc under test predates this tree's library sources)",
    )
    p.add_argument("--edition", default=None, help="override the crate's edition")
    p.add_argument("--timeout", type=int, default=3600, help="seconds before the compile is killed")
    p.add_argument(
        "--extra-flag",
        action="append",
        default=[],
        help=(
            "extra trustc flag (repeatable). Every trustc flag begins with `-`, which\n"
            "argparse reads as another option, so this one MUST use the `=` form:\n"
            "  --extra-flag=-Ztrust-ir-cg-args=no-proof-certs\n"
            "The space-separated spelling fails with `expected one argument`."
        ),
    )
    p.add_argument(
        "--reparse",
        default=None,
        metavar="STDERR_LOG",
        help="do not compile; re-analyze this stderr.log (e.g. after a parser change)",
    )
    p.add_argument(
        "--diag-json",
        action="store_true",
        help="also request the backend's typed JSON refusal stream, via the TRACKED compiler "
        "option `-Ztrust-ir-cg-args=diag-json`. It used to export TCG_DIAG_JSON=1, which every "
        "current trustc REFUSES as an untracked codegen control "
        "(rustc_session::config::UNTRACKED_TRUST_CODEGEN_ENV_PREFIXES) -- measured 2026-09-14, "
        "the census then recorded a harness error and an EMPTY 0-root artifact in 0s, which "
        "reads like a clean crate. The failed-root list and the skipped-internal notes are "
        "harvested from the human stderr regardless.",
    )
    return p.parse_args(argv)


def compiler_identity(trustc: Path) -> dict:
    out = subprocess.run([str(trustc), "-vV"], capture_output=True, text=True, check=False)
    fields = {}
    for line in out.stdout.splitlines():
        if ":" in line:
            k, v = line.split(":", 1)
            fields[k.strip()] = v.strip()
    fields["first_line"] = out.stdout.splitlines()[0] if out.stdout else ""
    fields["exit"] = out.returncode
    return fields


def git_rev(path: Path) -> str:
    out = subprocess.run(["git", "-C", str(path), "rev-parse", "HEAD"], capture_output=True, text=True, check=False)
    return out.stdout.strip() if out.returncode == 0 else "unknown"


def sysroot_rlibs(trustc: Path, env: dict[str, str]) -> tuple[Path | None, dict[str, Path]]:
    """The driven trustc's own sysroot and the rlibs it resolves by crate name.

    Returns (sysroot, {crate_name: rlib}) for `<sysroot>/lib/rustlib/<host>/lib`.
    rustc finds these without any `--extern`; a recipe dep that is here needs
    no flag, and emitting one anyway would only shadow the sysroot copy.
    """
    out = subprocess.run([str(trustc), "--print", "sysroot"], env=env, capture_output=True, text=True, check=False)
    if out.returncode != 0 or not out.stdout.strip():
        return None, {}
    sysroot = Path(out.stdout.strip())
    host = compiler_identity(trustc).get("host", "")
    libdir = sysroot / "lib" / "rustlib" / host / "lib"
    found: dict[str, Path] = {}
    for rlib in sorted(libdir.glob("lib*-*.rlib")) if libdir.is_dir() else []:
        name = rlib.name[len("lib") :].rsplit("-", 1)[0]
        found.setdefault(name, rlib)
    return sysroot, found


SEARCH_PATH_FLAGS = ("--sysroot", "--extern", "-L", "--target")


def extra_flags_override_search_path(extra_flags: list[str]) -> bool:
    """True when `--extra-flag` carries anything that changes which rlib the
    compiler loads for a dep it resolves itself. Those flags are appended AFTER
    this script's own dep flags, so they win."""
    return any(f.startswith(SEARCH_PATH_FLAGS) for f in extra_flags)


def resolve_deps(
    recipe_deps: list[str],
    externs: list[str],
    trustc: Path,
    env: dict[str, str],
    extra_flags: list[str],
) -> tuple[list[str], dict[str, dict], list[str]]:
    """Turn a recipe's `deps` into (`--extern` flags, provenance record, errors).

    Each dep resolves from an explicit `--extern DEP=PATH` first (recorded as
    `explicit`, with the path — true by construction, this script passed it),
    else it is left to the COMPILER's own search path (recorded as
    `compiler`), else it is an error naming both fixes. An `--extern` for a dep
    the recipe does not declare is also an error: the recipe is the statement
    of what the crate needs.

    A `compiler`-resolved record NAMES NO PATH AS FACT. The default sysroot's
    rlib is probed only as a fail-closed precheck and recorded as
    `default_sysroot_candidate`, because `--extra-flag` can carry `--sysroot=`,
    `--extern=`, `-L` or `--target` — appended after this script's flags — and
    then the compiler loads something else. Measured: a VALID=yes alloc census
    with `--extra-flag=--sysroot=<clone>` produced the exact 76-root headline
    while an earlier version of this record asserted the stage1 path. When such
    a flag is present the record says so (`search_path_overridden_by_extra_flags`),
    and the full command is in provenance for the reader to check.
    """
    explicit: dict[str, str] = {}
    errors: list[str] = []
    for spec in externs:
        name, sep, path = spec.partition("=")
        if not sep or not name or not path:
            errors.append(f"--extern must be DEP=PATH, got `{spec}`")
            continue
        if name not in recipe_deps:
            errors.append(f"--extern {name}: not a declared dep of this crate (declared: {recipe_deps or 'none'})")
            continue
        if not Path(path).is_file():
            errors.append(f"--extern {name}={path}: no such file")
            continue
        explicit[name] = path
    if not recipe_deps:
        return [], {}, errors
    sysroot, rlibs = sysroot_rlibs(trustc, env)
    flags: list[str] = []
    record: dict[str, dict] = {}
    for dep in recipe_deps:
        if dep in explicit:
            flags += ["--extern", f"{dep}={explicit[dep]}"]
            record[dep] = {"resolved_by": "explicit", "path": explicit[dep]}
        elif dep in rlibs:
            record[dep] = {
                "resolved_by": "compiler",
                "default_sysroot_candidate": str(rlibs[dep]),
            }
            if extra_flags_override_search_path(extra_flags):
                record[dep]["search_path_overridden_by_extra_flags"] = True
        else:
            errors.append(
                f"dep `{dep}` resolves neither from the sysroot ({sysroot or 'unreadable'}: no lib{dep}-*.rlib) "
                f"nor from an explicit flag; fix: pass `--extern {dep}=/path/to/lib{dep}-<hash>.rlib`, "
                f"or point --trustc at a stage sysroot that ships `{dep}`"
            )
    return flags, record, errors


def main(argv: list[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    trustc = Path(args.trustc).resolve()
    if not trustc.is_file():
        print(f"error: trustc not found: {trustc}", file=sys.stderr)
        return 2
    recipe = CRATES[args.crate]
    src = Path(args.src).resolve() if args.src else REPO / recipe["path"]
    edition = args.edition or recipe["edition"]
    if not src.is_file():
        print(f"error: crate source not found: {src}", file=sys.stderr)
        return 2
    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    backend = args.backend if args.backend is not None else ("reparse: unknown" if args.reparse else "trust-ir-cg")

    env = {k: v for k, v in os.environ.items() if not (k.startswith("TCG_") or k.startswith("TRUST_CG_"))}
    env["RUSTC_BOOTSTRAP"] = "1"
    env_note = "RUSTC_BOOTSTRAP=1"

    if args.reparse:
        # A reparse compiles nothing, so it resolves nothing: recording how the
        # CURRENT sysroot would satisfy the deps would describe a run that did
        # not happen. `--extern` has no meaning here either.
        dep_flags, dep_record = [], {}
        dep_errors = ["--extern is meaningless under --reparse (nothing is compiled)"] if args.extern else []
    else:
        dep_flags, dep_record, dep_errors = resolve_deps(
            list(recipe["deps"]), args.extern, trustc, env, list(args.extra_flag)
        )
    if dep_errors:
        for e in dep_errors:
            print(f"error: {e}", file=sys.stderr)
        return 2

    cmd = [
        str(trustc),
        "--edition",
        edition,
        "--crate-type",
        "lib",
        "--crate-name",
        args.crate,
        "--emit=obj",
        f"-Zcodegen-backend={backend}",
        "-Ccodegen-units=1",
        f"-Cpanic={args.panic}",
        f"-Copt-level={args.opt_level}",
        # This census measures CODEGEN refusals. The verifier is a separate
        # instrument (and `core` with the verifier on is an E0391 cycle today,
        # docs/design/2026-08-20-core-slice-blocker-histogram.md §6).
        "-Ztrust-verify=off",
        "--out-dir",
        str(out_dir / "obj"),
        *dep_flags,
        # The typed JSON refusal stream is requested through the TRACKED option,
        # never through TCG_DIAG_JSON: trustc refuses every `TCG_*`/`TRUST_CG_*`
        # environment variable as an untracked semantic/codegen control, and the
        # refusal aborts the compile before a single root is measured.
        *(["-Ztrust-ir-cg-args=diag-json"] if args.diag_json else []),
        *args.extra_flag,
        str(src),
    ]

    started = time.monotonic()
    if args.reparse:
        # Nothing ran. Every run-shaped fact (exit code, wall, emitted objects,
        # timeout, the compile command, the source) is UNKNOWN to a reparse and
        # is recorded as null below — never as the record of a run that did
        # not happen.
        stderr = Path(args.reparse).read_text()
        timed_out = None
        rc = None
        print(f"(reparse of {args.reparse}; nothing compiled)")
    else:
        (out_dir / "obj").mkdir(exist_ok=True)
        print(f"$ {env_note} {shlex.join(cmd)}")
        try:
            proc = subprocess.run(cmd, env=env, capture_output=True, text=True, timeout=args.timeout, check=False)
            timed_out = False
            stderr = proc.stderr
            rc = proc.returncode
        except subprocess.TimeoutExpired as exc:
            timed_out = True
            stderr = (exc.stderr or b"").decode("utf-8", "replace") if isinstance(exc.stderr, bytes) else (exc.stderr or "")
            rc = None
    elapsed = time.monotonic() - started
    if not args.reparse:
        (out_dir / "stderr.log").write_text(stderr)

    refusals, roots, skipped, trap_stubs, harness_errors = parse_backend_stderr(stderr)

    with (out_dir / "refusals.jsonl").open("w") as f:
        for r in refusals:
            f.write(json.dumps(r, sort_keys=True) + "\n")
    with (out_dir / "failed_roots.jsonl").open("w") as f:
        for r in roots:
            f.write(json.dumps(r, sort_keys=True) + "\n")
    with (out_dir / "skipped_internal.jsonl").open("w") as f:
        for r in skipped:
            f.write(json.dumps(r, sort_keys=True) + "\n")
    with (out_dir / "trap_stubs.jsonl").open("w") as f:
        for r in trap_stubs:
            f.write(json.dumps(r, sort_keys=True) + "\n")

    by_code: dict[str, list[dict]] = collections.defaultdict(list)
    for r in refusals:
        by_code[str(r.get("code"))].append(r)
    functions = {str(r.get("function")) for r in refusals if r.get("function")}
    # Per-root reasons: the crate-level TCG-MIR-UNSUPPORTED object carries every
    # failed root in one string; the ad-hoc `[TCG-...]` tags live inside those
    # messages, not in the typed `code`. Rank by tag so one wrapper code does
    # not hide forty distinct gaps.
    by_reason: dict[str, list[dict]] = collections.defaultdict(list)
    for root in roots:
        by_reason[root["reason"]].append(root)
    by_skip_reason: dict[str, list[dict]] = collections.defaultdict(list)
    for row in skipped:
        by_skip_reason[row["reason"]].append(row)
    by_trap_reason: dict[str, list[dict]] = collections.defaultdict(list)
    for row in trap_stubs:
        by_trap_reason[row["reason"]].append(row)

    lines = [
        f"# trust-ir-cg census: `{args.crate}`",
        "",
        f"* compiler: `{compiler_identity(trustc).get('first_line', '')}` at `{trustc}`",
        f"* backend: `{backend}`; panic={args.panic}; opt-level={args.opt_level}",
        f"* repo rev: `{git_rev(REPO)}`; trust-cg rev: `{git_rev(REPO / 'first-party' / 'trust-cg')}`",
        (
            f"* REPARSE of `{args.reparse}`: nothing compiled; exit code, wall, emitted objects unknown"
            if args.reparse
            else f"* exit code: `{rc}`" + (" (TIMED OUT)" if timed_out else "") + f"; wall: {elapsed:.0f}s"
        ),
        f"* typed refusals (JSON): **{len(refusals)}** across **{len(functions)}** functions; distinct codes: {len(by_code)}",
        f"* failed roots (externally required, fail-closed): **{len(roots)}**; distinct reasons: {len(by_reason)}",
        f"* skipped internal functions (dropped as unreachable — for a LIBRARY every one is a missing symbol downstream): **{len(skipped)}**; distinct reasons: {len(by_skip_reason)}",
        f"* trapping stubs emitted for dynamic-dispatch shims (link, but TRAP if reached): **{len(trap_stubs)}**; distinct reasons: {len(by_trap_reason)}",
        f"* harness errors (non-backend `error:` lines): {len(harness_errors)}",
        "",
        "## Failed roots by reason",
        "",
        "| rank | reason | count | example symbol |",
        "|---:|---|---:|---|",
    ]
    ranked_roots = sorted(by_reason.items(), key=lambda kv: (-len(kv[1]), kv[0]))
    for i, (reason, rows) in enumerate(ranked_roots, 1):
        lines.append(f"| {i} | `{md(reason, 110)}` | {len(rows)} | `{md(rows[0]['symbol'], 80)}` |")
    lines += ["", "## Skipped internal functions by reason", "", "| rank | reason | count | example symbol |", "|---:|---|---:|---|"]
    ranked_skips = sorted(by_skip_reason.items(), key=lambda kv: (-len(kv[1]), kv[0]))
    for i, (reason, rows) in enumerate(ranked_skips, 1):
        lines.append(f"| {i} | `{md(reason, 110)}` | {len(rows)} | `{md(rows[0]['symbol'], 80)}` |")
    lines += ["", "## Trapping stubs by reason", "", "| rank | reason | count | example symbol |", "|---:|---|---:|---|"]
    for i, (reason, rows) in enumerate(sorted(by_trap_reason.items(), key=lambda kv: (-len(kv[1]), kv[0])), 1):
        lines.append(f"| {i} | `{md(reason, 110)}` | {len(rows)} | `{md(rows[0]['symbol'], 80)}` |")
    lines += ["", "## Typed diagnostic codes", "", "| rank | code | count | example function | example why |", "|---:|---|---:|---|---|"]
    ranked = sorted(by_code.items(), key=lambda kv: (-len(kv[1]), kv[0]))
    for i, (code, rows) in enumerate(ranked, 1):
        ex = rows[0]
        lines.append(
            f"| {i} | `{code}` | {len(rows)} | `{md(str(ex.get('function', '')), 80)}` | {md(str(ex.get('why', '')), 120)} |"
        )
    if harness_errors:
        lines += ["", "## Harness errors (not gap rows)", ""]
        lines += [f"* `{e[:200]}`" for e in harness_errors[:50]]
    if args.reparse:
        emitted_objects = None
    else:
        emitted_objects = sum(1 for f in (out_dir / "obj").glob("*.o")) if (out_dir / "obj").is_dir() else 0
    lines.insert(
        lines.index("") if "" in lines else len(lines),
        "* emitted objects: unknown (reparse; nothing compiled)"
        if args.reparse
        else f"* emitted objects in `obj/`: {emitted_objects} (per-function/per-batch objects the backend DID produce; not a success count of mono items)",
    )
    (out_dir / "gap_table.md").write_text("\n".join(lines) + "\n")

    provenance = {
        "schema": "trust.trust-ir-cg-census.v1",
        "generated": _dt.datetime.now(_dt.timezone.utc).isoformat(),
        # Under --reparse the only input was the log: `command` is its path,
        # and the run-shaped fields are null. A reparse must never carry the
        # record of a compile it did not perform.
        "command": str(Path(args.reparse).resolve()) if args.reparse else cmd,
        "source": None if args.reparse else str(src),
        "env": {k: env[k] for k in ("RUSTC_BOOTSTRAP",) if k in env},
        "compiler": compiler_identity(trustc),
        "repo_rev": git_rev(REPO),
        "trust_cg_rev": git_rev(REPO / "first-party" / "trust-cg"),
        "exit_code": rc,
        "timed_out": timed_out,
        "wall_seconds": None if args.reparse else round(elapsed, 1),
        "refusal_count": len(refusals),
        "function_count": len(functions),
        "distinct_codes": len(by_code),
        "failed_root_count": len(roots),
        "failed_root_reasons": len(by_reason),
        "skipped_internal_count": len(skipped),
        "skipped_internal_reasons": len(by_skip_reason),
        "trap_stub_count": len(trap_stubs),
        "emitted_objects": emitted_objects,
        "trap_stub_reasons": len(by_trap_reason),
        "harness_error_count": len(harness_errors),
    }
    if args.reparse:
        provenance["reparsed"] = True
        provenance["reparsed_log"] = str(Path(args.reparse).resolve())
        provenance["crate"] = args.crate
        provenance["backend"] = backend
    if dep_record:
        # Only a crate with declared deps carries this; a leaf's provenance is
        # byte-for-byte what it was before deps were resolved at all.
        provenance["deps"] = dep_record
    (out_dir / "provenance.json").write_text(json.dumps(provenance, indent=2, sort_keys=True) + "\n")

    print("\n".join(lines[:16]))
    print(f"\nwrote {out_dir}/gap_table.md, refusals.jsonl, provenance.json, stderr.log")
    if timed_out:
        return 124
    if harness_errors and not refusals:
        return 3
    return 0


if __name__ == "__main__":
    sys.exit(main())
