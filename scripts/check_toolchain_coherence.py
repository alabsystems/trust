#!/usr/bin/env python3
"""Mechanical toolchain-coherence checker (drift tripwire).

Three classes of silent drift have broken Trust, the first two caused by the
targo/tippy/trustc rebrand changing one source of truth while hand-copied
duplicates lagged, the third by a Cargo workspace-manifest inheritance gap:

  1. TOOLCHAIN BIN SURFACE. The POSIX and Windows genesis adapters, seed
     discovery, compiled Rust bootstrap, stage2 shell gates, and targo-trust
     release detection must agree with bootstrap.py's authoritative
     required/forbidden bin and libexec sets. When a rebrand changed one copy
     but not another, `stage0_tool_surface_needs_refresh()` fired forever ->
     every fresh `./x.py build` wiped the adapter and tried to fetch an
     unmaterialized trust-std payload. Silent until a fresh checkout.

  2. -Z FLAG SURFACE. Shell/py scripts hardcode `-Z trust-*` flags. A prior
     compiler flag change left seven soundness gates, the dual oracle, and the
     differential fuzzer passing a rejected option, so trustc aborted during
     argument parsing BEFORE verifying. Probe every live script flag against
     the selected compiler so either side of the protocol cannot drift again.

  3. WORKSPACE MANIFEST INHERITANCE. A member's `dep = { workspace = true }`
     must resolve to a `[workspace.dependencies]` entry in the workspace root it
     is built under. `crates/trust-cg-bridge` inherits `ay-proof`, and
     rustc_codegen_trust_cg pulls it into the ROOT build, but the root
     `[workspace.dependencies]` lacked `ay-proof` -> `targo metadata` failed to
     load the `compiler/rustc` manifest and `./x.py build` died on a fresh
     checkout. We re-run that exact `metadata` command so the gap fails here.

This checker ties both duplicates back to their authority so the next such
drift fails LOUD here instead of silently in production. Wire into
`scripts/check_all.sh`. Author: Andrew Yates. Copyright 2026 Andrew Yates.

Exit 0 = coherent; 1 = drift detected; 2 = could not run a check (reported, not
fatal unless --strict).
"""

from __future__ import annotations

import argparse
import ast
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


def repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def _assignment_literal(text: str, var: str) -> object | None:
    """Evaluate one top-level literal assignment without executing the file."""
    try:
        tree = ast.parse(text)
    except SyntaxError:
        return None
    for node in tree.body:
        if not isinstance(node, ast.Assign):
            continue
        if not any(isinstance(target, ast.Name) and target.id == var for target in node.targets):
            continue
        try:
            return ast.literal_eval(node.value)
        except (ValueError, TypeError):
            return None
    return None


def _tuple_strings(text: str, var: str) -> set[str] | None:
    """Extract a top-level tuple/list of strings without parsing comments as code.

    The old non-greedy regex stopped at the first ``)`` even when it occurred in
    a comment inside the tuple, silently omitting every later entry from the
    coherence authority. Python's AST is both simpler and exact here.
    """
    value = _assignment_literal(text, var)
    if isinstance(value, (tuple, list)) and all(isinstance(item, str) for item in value):
        return set(value)
    return None


def _dict_keys(text: str, var: str) -> set[str] | None:
    value = _assignment_literal(text, var)
    if isinstance(value, dict) and all(isinstance(key, str) for key in value):
        return set(value)
    return None


def _rust_fn_string_array(text: str, function: str) -> set[str] | None:
    """Extract the string-only array returned by a small Rust authority helper."""
    match = re.search(
        rf"fn\s+{re.escape(function)}\s*\([^)]*\)[^{{]*\{{\s*&\[(.*?)\]\s*\}}",
        text,
        flags=re.DOTALL,
    )
    if match is None:
        return None
    body = match.group(1)
    values = re.findall(r'"([^"\\]*)"', body)
    return set(values) if values or not body.strip() else None


def _rust_const_string_array(text: str, constant: str) -> set[str] | None:
    """Extract a string-only Rust slice constant without compiling the crate."""
    match = re.search(
        rf"const\s+{re.escape(constant)}\s*:[^=]+?=\s*&\[(.*?)\]\s*;",
        text,
        flags=re.DOTALL,
    )
    if match is None:
        return None
    body = match.group(1)
    values = re.findall(r'"([^"\\]*)"', body)
    return set(values) if values or not body.strip() else None


def _shell_single_quoted_words(text: str, variable: str) -> set[str] | None:
    """Extract a top-level shell `NAME='space separated words'` assignment."""
    match = re.search(rf"^{re.escape(variable)}='([^']*)'$", text, flags=re.MULTILINE)
    if match is None:
        return None
    return set(match.group(1).split())


def _report_surface_difference(
    errors: list[str], label: str, authority_name: str, authority: set[str], mirror: set[str]
) -> None:
    missing = authority - mirror
    extra = mirror - authority
    if missing or extra:
        errors.append(
            f"stage0: {label} != bootstrap {authority_name} "
            f"(missing {sorted(missing) or 'none'}; extra {sorted(extra) or 'none'}) -- "
            "stage0 surface drift can make bootstrap erase a valid seed or admit retired aliases"
        )


def check_stage0_bin_surface(root: Path) -> list[str]:
    """Every stage0 producer/consumer must equal bootstrap.py's authority."""
    errors: list[str] = []
    boot = (root / "src/bootstrap/bootstrap.py").read_text(encoding="utf-8")
    gen = (root / "scripts/create_local_genesis_stage0.py").read_text(encoding="utf-8")
    discover = (root / "scripts/discover_trust_stage0_seed.py").read_text(encoding="utf-8")
    windows = (root / "scripts/win-genesis/win_genesis.py").read_text(encoding="utf-8")
    download = (root / "src/bootstrap/src/core/download.rs").read_text(encoding="utf-8")
    stage2_shell = (root / "scripts/lib/trust_toolchain_surface.sh").read_text(encoding="utf-8")
    targo_surface = (root / "targo-trust/src/pipeline/surface.rs").read_text(encoding="utf-8")

    # (authority var, POSIX genesis var, discovery var, compiled Rust helper)
    surfaces = [
        ("STAGE0_REQUIRED_BINS", "REQUIRED_BINS", "REQUIRED_STAGE0_BIN_ENTRYPOINTS", "stage0_required_bins"),
        (
            "STAGE0_REQUIRED_LIBEXEC_BINS",
            "REQUIRED_LIBEXEC_BINS",
            "REQUIRED_STAGE0_LIBEXEC_ENTRYPOINTS",
            "stage0_required_libexec_bins",
        ),
        ("STAGE0_FORBIDDEN_BINS", "FORBIDDEN_BINS", "FORBIDDEN_STAGE0_BIN_ENTRYPOINTS", "stage0_forbidden_bins"),
        (
            "STAGE0_FORBIDDEN_LIBEXEC_BINS",
            "FORBIDDEN_LIBEXEC_BINS",
            "FORBIDDEN_STAGE0_LIBEXEC_ENTRYPOINTS",
            "stage0_forbidden_libexec_bins",
        ),
    ]
    authorities: dict[str, set[str]] = {}
    for auth_var, gen_var, discover_var, rust_fn in surfaces:
        auth = _tuple_strings(boot, auth_var)
        if auth is None:
            errors.append(f"stage0: could not parse {auth_var} in bootstrap.py")
            continue
        authorities[auth_var] = auth
        mirrors = (
            (f"create_local_genesis_stage0.py:{gen_var}", _tuple_strings(gen, gen_var)),
            (f"discover_trust_stage0_seed.py:{discover_var}", _tuple_strings(discover, discover_var)),
            (f"download.rs::{rust_fn}()", _rust_fn_string_array(download, rust_fn)),
        )
        for label, mirror in mirrors:
            if mirror is None:
                errors.append(f"stage0: could not parse {label}")
            else:
                _report_surface_difference(errors, label, auth_var, auth, mirror)

    required_bins = authorities.get("STAGE0_REQUIRED_BINS")
    required_libexec = authorities.get("STAGE0_REQUIRED_LIBEXEC_BINS")
    forbidden_bins = authorities.get("STAGE0_FORBIDDEN_BINS", set())
    forbidden_libexec = authorities.get("STAGE0_FORBIDDEN_LIBEXEC_BINS", set())

    # Complete stage2 roots may expose the two canonical optional Miri tools,
    # and they deliberately ship `rustdoc` as a same-surface alias of `trustdoc`
    # (76d408e1cd: cargo spawns a binary named `rustdoc` for its doctest phase
    # and rustup's proxy refuses a linked toolchain without it, so
    # tool.rs:1676 rustdoc_sysroot_bins installs both names at every stage >= 1
    # and dist packages both). Its identity is enforced as an ALIAS -- the same
    # byte-identity check that admits `rustc` and `cargo` -- not by absence, so
    # a stock rustdoc still cannot pass as Trust surface. Every other
    # inherited/retired spelling stays forbidden, and a stage0 SEED still
    # forbids `rustdoc` outright, which is why the carve-out is derived here
    # rather than removed from the authority. Keep the Rust release detector and
    # shell front doors on exactly that derived inventory.
    stage2_optional_bins = {"trust-miri", "targo-miri"}
    stage2_forbidden_bins = forbidden_bins - stage2_optional_bins - {"rustdoc"}
    # The recreator's stage tool audit admits exactly these optional tools beside
    # its required producers; a different set there either fails a complete
    # stage2 after its build (2026-09-30: "unmapped public stage tools:
    # targo-miri, trust-miri") or admits a forbidden name.
    recreate = (root / "scripts/recreate_bootstrap.py").read_text(encoding="utf-8")
    recreate_optional = _dict_keys(recreate, "OPTIONAL_STAGE_TOOL_PRODUCERS")
    if recreate_optional is None:
        errors.append("stage0: could not parse recreate_bootstrap.py:OPTIONAL_STAGE_TOOL_PRODUCERS")
    else:
        _report_surface_difference(
            errors,
            "recreate_bootstrap.py:OPTIONAL_STAGE_TOOL_PRODUCERS",
            "derived complete-stage2 optional bin surface",
            stage2_optional_bins,
            recreate_optional,
        )
    stage2_forbidden_mirrors = (
        (
            "scripts/lib/trust_toolchain_surface.sh:TRUST_TOOLCHAIN_FORBIDDEN_PUBLIC_BINS",
            _shell_single_quoted_words(
                stage2_shell, "TRUST_TOOLCHAIN_FORBIDDEN_PUBLIC_BINS"
            ),
        ),
        (
            "targo-trust surface::FORBIDDEN_TRUST_PUBLIC_BIN_NAMES",
            _rust_const_string_array(targo_surface, "FORBIDDEN_TRUST_PUBLIC_BIN_NAMES"),
        ),
    )
    for label, mirror in stage2_forbidden_mirrors:
        if mirror is None:
            errors.append(f"stage0: could not parse {label}")
        else:
            _report_surface_difference(
                errors,
                label,
                "derived complete-stage2 forbidden bin surface",
                stage2_forbidden_bins,
                mirror,
            )

    stage2_forbidden_libexec_mirrors = (
        (
            "scripts/lib/trust_toolchain_surface.sh:TRUST_TOOLCHAIN_FORBIDDEN_PUBLIC_LIBEXEC_BINS",
            _shell_single_quoted_words(
                stage2_shell, "TRUST_TOOLCHAIN_FORBIDDEN_PUBLIC_LIBEXEC_BINS"
            ),
        ),
        (
            "targo-trust surface::FORBIDDEN_TRUST_PUBLIC_LIBEXEC_NAMES",
            _rust_const_string_array(targo_surface, "FORBIDDEN_TRUST_PUBLIC_LIBEXEC_NAMES"),
        ),
    )
    for label, mirror in stage2_forbidden_libexec_mirrors:
        if mirror is None:
            errors.append(f"stage0: could not parse {label}")
        else:
            _report_surface_difference(
                errors,
                label,
                "complete-stage2 forbidden libexec surface",
                forbidden_libexec,
                mirror,
            )

    def generated_surface(
        label: str, text: str, wrapped_var: str, stub_var: str, expected: set[str] | None
    ) -> set[str] | None:
        wrapped = _dict_keys(text, wrapped_var)
        stubbed = _dict_keys(text, stub_var)
        if wrapped is None or stubbed is None:
            errors.append(f"stage0: could not parse {label} generated tool mappings")
            return None
        overlap = wrapped & stubbed
        if overlap:
            errors.append(f"stage0: {label} wraps and stubs the same tools: {sorted(overlap)}")
        actual = wrapped | stubbed
        if expected is not None:
            _report_surface_difference(errors, label, "required tool surface", expected, actual)
        return actual

    posix_bins = generated_surface(
        "POSIX genesis emitted bins", gen, "WRAPPER_SOURCES", "STUB_BINS", required_bins
    )
    # The POSIX libexec producer currently has only stubs, not wrapped tools.
    posix_libexec = _dict_keys(gen, "STUB_LIBEXEC_BINS")
    if posix_libexec is None:
        errors.append("stage0: could not parse POSIX genesis STUB_LIBEXEC_BINS mapping")
    elif required_libexec is not None:
        _report_surface_difference(
            errors,
            "POSIX genesis emitted libexec",
            "required tool surface",
            required_libexec,
            posix_libexec,
        )

    windows_bins = generated_surface("Windows genesis emitted bins", windows, "WRAP", "STUB", required_bins)
    windows_libexec = _dict_keys(windows, "LIBWRAP")
    if windows_libexec is None:
        errors.append("stage0: could not parse Windows genesis LIBWRAP mapping")
    elif required_libexec is not None:
        _report_surface_difference(
            errors, "Windows genesis emitted libexec", "required tool surface", required_libexec, windows_libexec
        )

    for label, actual, forbidden in (
        ("POSIX genesis bins", posix_bins, forbidden_bins),
        ("POSIX genesis libexec", posix_libexec, forbidden_libexec),
        ("Windows genesis bins", windows_bins, forbidden_bins),
        ("Windows genesis libexec", windows_libexec, forbidden_libexec),
    ):
        if actual is not None and actual & forbidden:
            errors.append(f"stage0: {label} emits forbidden aliases {sorted(actual & forbidden)}")
    return errors


def _scripts_z_flags(root: Path) -> dict[str, list[str]]:
    """Map each `-Z trust-*` flag token -> the script files that use it (in a command,
    not a comment). Skips obvious doc/comment lines.

    BOTH spellings, and the space is optional on purpose. `-Z` takes its value
    joined (`-Ztrust-dump=...`) or separated (`-Z trust-dump=...`), and this repo
    writes the JOINED form 5x more often (measured 2026-09-27 over scripts/: 307
    joined vs 60 separated). A `\\s+` here saw 7 of the 20 flags scripts actually
    pass -- `-Ztrust-dump` (16 files), the whole `-Ztrust-cg-*` and
    `-Ztrust-verify-{level,session,timeout-ms}` families, and the rest were
    invisible, so the check this gate advertises ("every `-Z trust-*` flag used in
    scripts/ still present in the source option table") was green on a third of
    the surface and could not report a renamed flag in the other two thirds.
    The trailing `[a-z0-9]` requires the token to end in a name character, which
    drops the shell case-glob `-Ztrust-*` (create_local_genesis_stage0.py) rather
    than reporting `trust-` as a removed flag."""
    flags: dict[str, list[str]] = {}
    flag_re = re.compile(r"-Z\s*(trust[a-z0-9-]*[a-z0-9])")
    for sub in ("scripts",):
        for p in sorted((root / sub).rglob("*")):
            if p.suffix not in (".sh", ".py") or not p.is_file():
                continue
            if p.name == Path(__file__).name:
                continue
            for line in p.read_text(encoding="utf-8", errors="ignore").splitlines():
                stripped = line.lstrip()
                # Skip comment-only lines and obvious doc echoes / box-drawing help.
                if stripped.startswith(("#", "//", "*", "│")):
                    continue
                for flag in flag_re.findall(line):
                    if flag in ("trust", "trust-"):
                        continue
                    flags.setdefault(flag, [])
                    rel = str(p.relative_to(root))
                    if rel not in flags[flag]:
                        flags[flag].append(rel)
    return flags


def _declared_z_flags(root: Path) -> set[str] | None:
    """The `-Z` names the compiler SOURCE declares, spelled as the CLI spells them.

    Read out of the `options!` tables in `rustc_session::options`. Returns None
    when the file cannot be parsed, so a parse failure degrades to "no source
    authority" rather than to a false accusation of drift.
    """
    path = root / "compiler/rustc_session/src/options.rs"
    try:
        text = path.read_text(encoding="utf-8")
    except OSError:
        return None
    # Scan only inside the `options! { ... }` tables so a same-shaped struct
    # field elsewhere in the file cannot enlarge the declared set — an
    # over-large set would turn this check into a false pass. Each entry opens
    # a line `    name: Type = (`, and the CLI spells `_` as `-`.
    entry_re = re.compile(r"^    ([a-z][a-z0-9_]*)\s*:\s*[^=\n]+=\s*\(")
    names: set[str] = set()
    in_table = False
    for line in text.splitlines():
        if not in_table:
            in_table = line.startswith("options! {")
            continue
        if line == "}":
            in_table = False
            continue
        match = entry_re.match(line)
        if match:
            names.add(match.group(1).replace("_", "-"))
    return names or None


def check_z_flag_surface(root: Path, trustc: Path) -> tuple[list[str], list[str]]:
    """Every `-Z trust-*` flag a script passes must still exist in the compiler.

    The SOURCE option table is the authority, not whichever `trustc` happens to
    be lying around in `build/`. A built compiler is always some commit behind
    the tree it was built from, and treating it as the authority reported every
    freshly landed flag as removed — which trains everyone to ignore this gate
    exactly when it is telling the truth. The binary is still probed, but a
    binary that rejects a flag the source declares is a STALE BINARY, and that
    is reported as such.
    """
    errors: list[str] = []
    notes: list[str] = []
    flags = _scripts_z_flags(root)
    if not flags:
        notes.append("flags: no `-Z trust-*` flags found in scripts/ (nothing to check)")
        return errors, notes

    declared = _declared_z_flags(root)
    if declared is None:
        notes.append(
            "flags: could not read the option table in "
            "compiler/rustc_session/src/options.rs -- no source authority for this run"
        )
    else:
        for flag, users in sorted(flags.items()):
            if flag not in declared:
                errors.append(
                    f"flags: `-Z {flag}` is not declared by the compiler source but is "
                    f"still passed in: {', '.join(users)} -- a removed/renamed flag; "
                    f"trustc aborts before doing its job (this is how the soundness "
                    f"gates were silently neutered)"
                )

    if not trustc.exists() or not os.access(trustc, os.X_OK):
        notes.append(
            f"flags: trustc not built at {trustc} -- source-table check only for "
            f"{len(flags)} flag(s). Build with ./x.py build --stage 2 to corroborate."
        )
        return errors, notes

    env = dict(os.environ, RUSTC_BOOTSTRAP="1")
    stale: list[str] = []
    with tempfile.TemporaryDirectory() as td:
        src = Path(td) / "probe.rs"
        src.write_text("#![crate_type=\"lib\"]\n", encoding="utf-8")
        for flag in sorted(flags):
            r = subprocess.run(
                [str(trustc), "--edition", "2021", "--crate-type", "lib",
                 "-Z", flag, str(src), "-o", str(Path(td) / "probe.rlib")],
                env=env, capture_output=True, text=True, timeout=120,
            )
            out = r.stdout + r.stderr
            if not re.search(r"unknown unstable option|is not an? (accepted|recognized)", out):
                continue
            if declared is None or flag in declared:
                stale.append(flag)
            else:
                # Already reported against the source table; the binary agreeing
                # adds nothing.
                continue
    if stale:
        notes.append(
            f"flags: the probed {trustc} rejects {len(stale)} flag(s) the source "
            f"declares ({', '.join(sorted(stale))}) -- that binary predates the tree; "
            f"rebuild before treating its behavior as evidence"
        )
    return errors, notes


def _find_targos(root: Path, trustc: Path) -> list[Path]:
    """Every targo binary that could run `metadata`, in preference order:
    the stage2 build next to the configured trustc, then any stage0 genesis
    targo, then the other build stages, then `targo` on PATH. A PATH `cargo` is
    never a candidate: in aterm it is the reroute
    stub (exit 127), elsewhere rustup's default, usually stock.

    A LIST, not the first hit: a targo older than a manifest key the tree now
    uses refuses that manifest with `unknown field ...` — the 2026-09-10 note
    below — and on 2026-09-16 the same thing recurred INSIDE the build tree
    (a Sep-1 stage2 beside a tree whose `first-party/ty` manifest carries
    `compiler_timeout_secs`, while the freshly built stage1 loads it). A stale
    toolchain is a NOTE the flag check already prints; only a manifest that no
    candidate loads is a manifest defect."""
    candidates: list[Path] = [trustc.parent / "targo"]
    # scripts/create_local_genesis_stage0.py writes its adapter to
    # build/<host>/genesis-stage0 ON PURPOSE (bootstrap.py wipes build/<host>/stage0
    # on any stage0 pin-date advance), and bootstrap.toml points `cargo` at it, so
    # `targo metadata` there IS the command `./x.py build` runs on such a machine.
    # Without this glob the search fell through to whatever `targo` PATH carried —
    # measured 2026-09-10: an atpkg store targo two weeks older than targo-trust's
    # `[trust] compiler_timeout_secs`, which then refused first-party/ty's manifest
    # and reported a drift the build itself would never see.
    # GENESIS ADAPTER (developer adapter, never release evidence; its retirement
    # is decided separately): this `targo` wraps a host Rust, and it is kept only
    # because it IS what `./x.py build` runs on a genesis-seeded machine.
    candidates += sorted(root.glob("build/*/genesis-stage0/bin/targo"))
    candidates += sorted(root.glob("build/*/stage0/bin/targo"))
    candidates += sorted(root.glob("build/host/stage*/bin/targo"))
    found = shutil.which("targo")
    if found:
        candidates.append(Path(found))
    seen: set[Path] = set()
    usable: list[Path] = []
    for c in candidates:
        if c.exists() and os.access(c, os.X_OK):
            key = c.resolve()
            if key not in seen:
                seen.add(key)
                usable.append(c)
    return usable


def _find_targo(root: Path, trustc: Path) -> Path | None:
    """The single preferred candidate (kept for callers that want one binary)."""
    found = _find_targos(root, trustc)
    return found[0] if found else None


def _is_schema_age_failure(lines: list[str]) -> bool:
    """A manifest refusal that names a KEY the binary does not know is the binary
    predating the tree, not the tree being broken."""
    return any("unknown field" in ln for ln in lines)


def check_workspace_manifests_load(
    root: Path, targos: "Path | list[Path] | None"
) -> tuple[list[str], list[str]]:
    """`targo metadata --no-deps` must load every workspace member manifest.

    This is the EXACT command bootstrap runs (src/core/metadata.rs). It fails when a
    member's `dep = { workspace = true }` has no matching `[workspace.dependencies]`
    entry in the workspace root it resolves against — the class that broke
    `./x.py build` when `ay-proof` was missing from the root `[workspace.dependencies]`
    (crates/trust-cg-bridge inherits it; rustc_codegen_trust_cg pulls trust-cg-bridge
    into the root build, so its inheritance resolves against the ROOT workspace). A
    pure-TOML check can't see that cross-workspace pull, so we let cargo's own resolver
    be the authority — if it can't load the manifests, neither can `./x.py build`.

    Cheap (no compilation; `--no-deps` is offline manifest parsing only).
    """
    errors: list[str] = []
    notes: list[str] = []
    if targos is None:
        candidates: list[Path] = []
    elif isinstance(targos, Path):
        candidates = [targos]
    else:
        candidates = list(targos)
    if not candidates:
        notes.append(
            "manifests: no targo on PATH or in build/ -- skipped the "
            "`metadata` manifest-load probe (build the toolchain to enable)"
        )
        return errors, notes
    env = dict(os.environ, RUSTC_BOOTSTRAP="1")
    for manifest in ("Cargo.toml", "targo-trust/Cargo.toml"):
        mpath = root / manifest
        if not mpath.exists():
            continue
        # Try every candidate in preference order. The FIRST that loads the
        # manifests settles the question the probe asks (can the resolver load
        # them); a candidate that fails only because it predates a manifest key
        # is a stale-toolchain NOTE, never a manifest drift. A drift is reported
        # only when NO candidate loads them, with the most specific detail seen.
        loaded_by: Path | None = None
        stale: list[str] = []
        real_failures: list[str] = []
        for targo in candidates:
            try:
                r = subprocess.run(
                    [str(targo), "metadata", "--no-deps", "--format-version", "1",
                     "--manifest-path", str(mpath)],
                    env=env, capture_output=True, text=True, timeout=180, cwd=str(root),
                )
            except (OSError, subprocess.TimeoutExpired) as exc:
                real_failures.append(f"{targo}: could not run `metadata`: {exc}")
                continue
            if r.returncode == 0:
                loaded_by = targo
                break
            lines = [ln.strip() for ln in (r.stdout + r.stderr).splitlines() if ln.strip()]
            detail = next(
                (ln for ln in lines if "inherit" in ln or "failed to load" in ln),
                next((ln for ln in lines if ln.lower().startswith("error")), lines[-1] if lines else "metadata failed"),
            )
            if _is_schema_age_failure(lines):
                key = next((ln for ln in lines if "unknown field" in ln), detail)
                stale.append(f"{targo}: {key}")
            else:
                real_failures.append(f"{targo} (exit {r.returncode}): {detail}")
        if loaded_by is not None:
            if stale:
                notes.append(
                    f"manifests: {manifest} loads with {loaded_by}; "
                    f"{len(stale)} older candidate(s) predate a manifest key the tree uses "
                    f"and were skipped ({'; '.join(stale)}) -- rebuild or re-seal that "
                    f"toolchain before treating its behavior as evidence"
                )
            continue
        if real_failures:
            errors.append(
                f"manifests: `targo metadata --no-deps` failed for {manifest} with every "
                f"candidate: {'; '.join(real_failures)} -- a workspace member manifest does not "
                f"load (e.g. a `{{ workspace = true }}` dep missing from "
                f"[workspace.dependencies]); `./x.py build` fails the same way on a fresh checkout"
            )
        else:
            errors.append(
                f"manifests: no candidate targo could load {manifest} -- every one predates "
                f"a manifest key the tree uses ({'; '.join(stale)}); build a current stage "
                f"(`./x.py build --stage 1`) so the probe has a toolchain that matches the tree"
            )
    return errors, notes


_SELFTEST_OPTIONS_RS = """\
// A miniature stand-in for compiler/rustc_session/src/options.rs.
options! {
    trust_verify: bool = (false, parse_bool, [TRACKED],
        "verify (default: no)"),
    trust_dump: TrustDump = (TrustDump::default(), parse_trust_dump, [TRACKED],
        "publish one artifact"),
}
"""

_SELFTEST_SCRIPT_SH = """\
#!/bin/sh
# -Ztrust-bogus-in-a-comment=on   <- prose, not a command line
trustc -Ztrust-verify=on probe.rs          # declared, joined
trustc -Z trust-dump=mir:/tmp/d probe.rs   # declared, separated
trustc -Ztrust-bogus-joined=on probe.rs    # UNDECLARED, joined
trustc -Z trust-bogus-spaced=on probe.rs   # UNDECLARED, separated
case "$flag" in -Ztrust-*) ;; esac         # a glob, not a flag name
"""


def selftest() -> int:
    """Prove the -Z flag check FIRES, in BOTH spellings.

    From the tripwire's first commit until 2026-09-27 it could not: the scanner
    required a space after `-Z`, so the joined `-Ztrust-*` form -- the one this repo
    writes 5x more often -- was invisible, and the gate printed OK while seeing 7 of
    20 flags. Renaming `trust_dump` in the option table, which 16 scripts pass as
    `-Ztrust-dump=...`, produced no drift at all. A guard nobody has watched fail is
    a guard nobody has, so plant the mutation here in BOTH spellings.
    """
    cases: list[tuple[str, bool]] = []
    with tempfile.TemporaryDirectory() as temporary:
        root = Path(temporary)
        (root / "scripts").mkdir()
        (root / "scripts/probe_lane.sh").write_text(_SELFTEST_SCRIPT_SH, encoding="utf-8")
        (root / "compiler/rustc_session/src").mkdir(parents=True)
        (root / "compiler/rustc_session/src/options.rs").write_text(
            _SELFTEST_OPTIONS_RS, encoding="utf-8"
        )

        found = _scripts_z_flags(root)
        errors, _notes = check_z_flag_surface(root, root / "no-such-trustc")
        blob = "\n".join(errors)

        cases.append(("an UNDECLARED joined `-Ztrust-...` flag is reported",
                      "`-Z trust-bogus-joined`" in blob))
        cases.append(("an UNDECLARED separated `-Z trust-...` flag is reported",
                      "`-Z trust-bogus-spaced`" in blob))
        cases.append(("the reporting names the script that passes it",
                      all("scripts/probe_lane.sh" in e for e in errors)))
        cases.append(("a declared joined flag is NOT reported",
                      "trust-verify`" not in blob and "trust-verify=" not in blob))
        cases.append(("a declared separated flag is NOT reported",
                      "trust-dump" not in blob))
        cases.append(("both spellings reach the scanned set",
                      {"trust-verify", "trust-dump", "trust-bogus-joined",
                       "trust-bogus-spaced"} <= set(found)))
        cases.append(("a commented-out flag is not scanned",
                      "trust-bogus-in-a-comment" not in found and
                      "trust-bogus-in-a-comment" not in blob))
        cases.append(("the `-Ztrust-*` shell glob yields no phantom flag",
                      not any(f in found for f in ("trust", "trust-"))))
        cases.append(("exactly the two planted flags are reported",
                      len(errors) == 2))

    bad = [name for name, ok in cases if not ok]
    for name, ok in cases:
        print(f"  {'ok  ' if ok else 'FAIL'} {name}")
    if bad:
        print(f"check_toolchain_coherence --selftest: FAIL ({len(bad)})", file=sys.stderr)
        return 1
    print(f"check_toolchain_coherence --selftest: OK ({len(cases)} cases)")
    return 0


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--trustc", default=None, help="path to trustc (default: build/host/stage2/bin/trustc)")
    p.add_argument("--strict", action="store_true", help="treat skipped checks (exit 2) as failures")
    p.add_argument("--selftest", action="store_true",
                   help="prove the -Z flag check fires in both spellings, on a synthetic tree")
    args = p.parse_args(argv)
    if args.selftest:
        return selftest()
    root = repo_root()
    trustc = Path(args.trustc) if args.trustc else root / "build/host/stage2/bin/trustc"

    print("Trust toolchain-coherence check")
    errors: list[str] = []
    notes: list[str] = []

    errors += check_stage0_bin_surface(root)
    fe, fn = check_z_flag_surface(root, trustc)
    errors += fe
    notes += fn
    me, mn = check_workspace_manifests_load(root, _find_targos(root, trustc))
    errors += me
    notes += mn

    for n in notes:
        print(f"  NOTE  {n}")
    if not errors:
        print(
            "  OK    toolchain bin surface, -Z flag surface, and workspace manifests are coherent"
        )
        return 2 if (args.strict and notes) else 0
    for e in errors:
        print(f"  DRIFT {e}")
    print(f"\nTOOLCHAIN COHERENCE: {len(errors)} drift(s) detected.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
