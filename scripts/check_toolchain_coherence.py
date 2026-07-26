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

    # Complete stage2 roots may expose the two canonical optional Miri tools;
    # every inherited/retired spelling stays forbidden. Keep the Rust release
    # detector and shell front doors on exactly that derived inventory.
    stage2_forbidden_bins = forbidden_bins - {"trust-miri", "targo-miri"}
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
    not a comment). Skips obvious doc/comment lines."""
    flags: dict[str, list[str]] = {}
    flag_re = re.compile(r"-Z\s+(trust[a-z0-9-]*)")
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


def _find_targo(root: Path, trustc: Path) -> Path | None:
    """A targo/cargo binary to run `metadata` with: prefer the stage2 build next to
    the configured trustc, then any stage0 genesis targo, then PATH."""
    candidates: list[Path] = [trustc.parent / "targo"]
    candidates += sorted(root.glob("build/*/stage0/bin/targo"))
    candidates += sorted(root.glob("build/host/stage*/bin/targo"))
    for c in candidates:
        if c.exists() and os.access(c, os.X_OK):
            return c
    for name in ("targo", "cargo"):
        found = shutil.which(name)
        if found:
            return Path(found)
    return None


def check_workspace_manifests_load(root: Path, targo: Path | None) -> tuple[list[str], list[str]]:
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
    if targo is None:
        notes.append(
            "manifests: no targo/cargo on PATH or in build/ -- skipped the "
            "`metadata` manifest-load probe (build the toolchain to enable)"
        )
        return errors, notes
    env = dict(os.environ, RUSTC_BOOTSTRAP="1")
    for manifest in ("Cargo.toml", "crates/Cargo.toml", "targo-trust/Cargo.toml"):
        mpath = root / manifest
        if not mpath.exists():
            continue
        try:
            r = subprocess.run(
                [str(targo), "metadata", "--no-deps", "--format-version", "1",
                 "--manifest-path", str(mpath)],
                env=env, capture_output=True, text=True, timeout=180, cwd=str(root),
            )
        except (OSError, subprocess.TimeoutExpired) as exc:
            notes.append(f"manifests: could not run `metadata` for {manifest}: {exc}")
            continue
        if r.returncode != 0:
            lines = [ln.strip() for ln in (r.stdout + r.stderr).splitlines() if ln.strip()]
            detail = next(
                (ln for ln in lines if "inherit" in ln or "failed to load" in ln),
                next((ln for ln in lines if ln.lower().startswith("error")), lines[-1] if lines else "metadata failed"),
            )
            errors.append(
                f"manifests: `targo metadata --no-deps` failed for {manifest} "
                f"(exit {r.returncode}): {detail} -- a workspace member manifest does not "
                f"load (e.g. a `{{ workspace = true }}` dep missing from "
                f"[workspace.dependencies]); `./x.py build` fails the same way on a fresh checkout"
            )
    return errors, notes


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--trustc", default=None, help="path to trustc (default: build/host/stage2/bin/trustc)")
    p.add_argument("--strict", action="store_true", help="treat skipped checks (exit 2) as failures")
    args = p.parse_args(argv)
    root = repo_root()
    trustc = Path(args.trustc) if args.trustc else root / "build/host/stage2/bin/trustc"

    print("Trust toolchain-coherence check")
    errors: list[str] = []
    notes: list[str] = []

    errors += check_stage0_bin_surface(root)
    fe, fn = check_z_flag_surface(root, trustc)
    errors += fe
    notes += fn
    me, mn = check_workspace_manifests_load(root, _find_targo(root, trustc))
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
