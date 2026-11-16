#!/usr/bin/env python3
"""`build/` may be a symlink to `build.noindex/`: every walker and guard must say so.

WHY: Spotlight indexes the checkout's `build/` (568 GiB on the maintainer box,
measured 2026-09-24) and only a `.noindex` directory NAME excludes it. The
sanctioned layout is therefore `mv build build.noindex && ln -s build.noindex build`
(docs/BUILD_AND_INSTALL.md, "Keeping Spotlight out of build/"). Three classes of
code break silently under that layout, and this file pins each one:

1. WALKERS. BSD and GNU `find` default to `-P`: a symlinked START path is not
   descended, so `find "$ROOT/build" -name trustc` prints NOTHING and the caller
   reports "no compiler". `du build` reports the 0-byte link. The fix is `-H`
   (follow command-line links only). `test_no_build_root_walker_without_H` lints
   every tracked shell surface; the behavioural tests run the real functions.
2. CONTAINMENT. `resolved_path.is_relative_to(root / "build")` is False for every
   path resolved through the link, because `root / "build"` is lexical.
3. GUARDS. Checks that refuse a symlinked `build` (they exist so output cannot be
   redirected outside the checkout) must admit exactly the sanctioned link and
   nothing else.

Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import contextlib
import importlib.util
import io
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
HOST = "aarch64-apple-darwin"


def load(name: str):
    path = REPO_ROOT / "scripts" / f"{name}.py"
    spec = importlib.util.spec_from_file_location(f"build_dir_symlink_{name}", path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


MINT = load("mint_seed_support")
RECREATE = load("recreate_bootstrap")
OFF_STOCK = load("off_stock_rust_audit")
LAMBDA = load("collect_lambda_calculus_diagnostic")
PREFLIGHT_SPEC = importlib.util.spec_from_file_location(
    "build_dir_symlink_preflight", REPO_ROOT / "tools" / "preflight.py"
)
VERSION_SYNC = load("trust_version_sync")

# Every inlined copy of the sanctioned-layout predicate. They are copies on
# purpose (off_stock_rust_audit.py runs under `python -I -S` and authenticates
# only itself); this matrix keeps them from drifting apart.
PREDICATES = {
    "mint_seed_support": getattr(MINT, "is_sanctioned_build_link", None),
    "recreate_bootstrap": getattr(RECREATE, "is_sanctioned_build_link", None),
    "off_stock_rust_audit": getattr(OFF_STOCK, "is_sanctioned_build_link", None),
    "collect_lambda_calculus_diagnostic": getattr(LAMBDA, "is_sanctioned_build_link", None),
}


def executable(path: Path, body: str = "#!/bin/sh\nexit 0\n") -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(body, encoding="utf-8")
    path.chmod(0o755)
    return path


def noindex_checkout(parent: Path) -> Path:
    """A checkout whose `build` is the sanctioned link to a real `build.noindex`."""
    root = parent / "checkout"
    (root / "build.noindex").mkdir(mode=0o700, parents=True)
    (root / "build").symlink_to("build.noindex", target_is_directory=True)
    return root.resolve()


def stage2(root: Path, tools: tuple[str, ...] = ("trustc", "targo", "targo-trust", "trustd")) -> Path:
    sysroot = root / "build.noindex" / HOST / "stage2"
    for tool in tools:
        executable(sysroot / "bin" / tool, f"#!/bin/sh\necho '{tool} 9.9.9-fixture'\n")
    return sysroot


def shell_function(path: Path, name: str) -> str:
    """The exact text of one top-level bash function, as the script defines it."""
    lines = path.read_text(encoding="utf-8").splitlines()
    start = next(i for i, line in enumerate(lines) if line.startswith(f"{name}() {{"))
    end = next(i for i in range(start + 1, len(lines)) if lines[i] == "}")
    return "\n".join(lines[start : end + 1]) + "\n"


# --------------------------------------------------------------------------
# 1. walkers
# --------------------------------------------------------------------------
LINT_EXCLUDED = (
    "vendor/", "compiler/", "library/", "src/", "first-party/", "reports/",
    "tests/ui/", "tests/run-make/", "scripts/frozen-waivers.txt",
)
WALKER = re.compile(r"(?:^|[\s;|&(`])(find|du)((?:\s+-[A-Za-z]+)*)\s+(\S+)")
# A start operand that NAMES the build root itself (not a path beneath it):
# build, ./build, "$ROOT/build", "${REPO}/build", '.../build'. A trailing slash
# (`build/`) is already followed by every find and du, so it is not flagged.
BUILD_ROOT_OPERAND = re.compile(r"""^["']?(?:\.?/)?(?:[^"'\s]*/)?build["']?\)?$""")


def logical_lines(text: str):
    """(first physical line number, line) with backslash continuations joined."""
    pending, start = "", 0
    for number, physical in enumerate(text.splitlines(), 1):
        if not pending:
            start = number
        if physical.endswith("\\"):
            pending += physical[:-1] + " "
            continue
        yield start, pending + physical
        pending = ""
    if pending:
        yield start, pending


def fenced_code_only(markdown: str) -> str:
    """Blank every line outside a ``` fence, keeping line numbers.

    A recipe someone will paste is code; prose that QUOTES the broken spelling
    to explain it (as KNOWN_HAZARDS.md does) is not.
    """
    kept, inside = [], False
    for line in markdown.splitlines():
        if line.lstrip().startswith("```"):
            inside = not inside
            kept.append("")
        else:
            kept.append(line if inside else "")
    return "\n".join(kept)


def build_root_walkers(text: str) -> list[tuple[int, str]]:
    offenders = []
    for number, line in logical_lines(text):
        if line.lstrip().startswith("#"):
            continue
        for match in WALKER.finditer(line):
            _tool, flags, operand = match.groups()
            if not BUILD_ROOT_OPERAND.match(operand):
                continue
            if re.search(r"-[A-Za-z]*[HL]", flags):
                continue
            offenders.append((number, line.strip()))
    return offenders


class WalkerTests(unittest.TestCase):
    def test_premise_find_and_du_do_not_descend_a_symlinked_start_path(self):
        # If this ever fails, the platform's find/du changed and the lint below
        # is guarding a hazard that no longer exists -- re-measure, do not delete.
        with tempfile.TemporaryDirectory() as tmp:
            root = noindex_checkout(Path(tmp))
            stage2(root, ("trustc",))
            (root / "build.noindex" / "payload").write_bytes(b"\0" * 65536)
            run = lambda *argv: subprocess.run(  # noqa: E731
                argv, cwd=root, capture_output=True, text=True, check=False
            ).stdout
            self.assertEqual(run("find", "build", "-name", "trustc"), "")
            self.assertEqual(
                run("find", "-H", "build", "-name", "trustc").strip(),
                f"build/{HOST}/stage2/bin/trustc",
            )
            self.assertEqual(int(run("du", "-sk", "build").split()[0]), 0)
            self.assertGreaterEqual(int(run("du", "-skH", "build").split()[0]), 64)

    def test_lint_flags_exactly_the_build_root_walkers(self):
        flagged = [
            'x=$(find build -name trustc)',
            'done < <(find "${REPO}/build" -path "*/stage2/bin/x" -type f)',
            'find "$TRUST_ROOT/build" \\\n  -name trustc',
            "du -sh build",
        ]
        clean = [
            'x=$(find -H build -name trustc)',
            'find -H "${REPO}/build" -type f',
            'find "$ROOT/build/host/stage2" -type f',  # the link is mid-path: resolved
            'find build/ -name trustc',
            "du -shH build",
            "# find build -name trustc   (a comment)",
            'find "$STAGE" -name build',  # `build` is a -name argument, not a start
        ]
        for text in flagged:
            self.assertTrue(build_root_walkers(text), text)
        recipe = "Prose quoting `find build -name x`.\n```bash\nfind build -name x\n```\n"
        self.assertEqual([n for n, _ in build_root_walkers(fenced_code_only(recipe))], [3])
        for text in clean:
            self.assertEqual(build_root_walkers(text), [], text)

    def test_no_build_root_walker_without_H(self):
        listed = subprocess.run(
            ["git", "-C", str(REPO_ROOT), "ls-files", "-z", "--",
             "*.sh", "*.bash", "*.md", "Makefile", "*/Makefile", "scripts/hooks/*"],
            capture_output=True, check=True,
        ).stdout.decode("utf-8").split("\0")
        offenders = []
        for relative in filter(None, listed):
            if relative.startswith(LINT_EXCLUDED):
                continue
            path = REPO_ROOT / relative
            if not path.is_file():
                continue
            text = path.read_text(encoding="utf-8", errors="replace")
            if relative.endswith(".md"):
                text = fenced_code_only(text)
            offenders += [f"{relative}:{n}: {line}" for n, line in build_root_walkers(text)]
        self.assertEqual(
            offenders, [],
            "find/du started AT the build root without -H: nothing is found once "
            "`build` is the build.noindex symlink (docs/KNOWN_HAZARDS.md)\n"
            + "\n".join(offenders),
        )

    def test_build_sh_status_names_the_compiler_behind_the_link(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = noindex_checkout(Path(tmp))
            stage2(root, ("trustc",))
            (root / "scripts" / "lib").mkdir(parents=True)
            shutil.copy2(REPO_ROOT / "scripts" / "build.sh", root / "scripts" / "build.sh")
            shutil.copy2(
                REPO_ROOT / "scripts" / "lib" / "trust_toolchain_surface.sh",
                root / "scripts" / "lib" / "trust_toolchain_surface.sh",
            )
            result = subprocess.run(
                ["bash", "scripts/build.sh", "status"], cwd=root,
                capture_output=True, text=True, check=False,
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn(f"Compiler:  build/{HOST}/stage2/bin/trustc", result.stdout)
            self.assertIn("trustc 9.9.9-fixture", result.stdout)

    def test_stage2_tool_discovery_functions_see_through_the_link(self):
        cases = [
            ("scripts/run_tests_after_build.sh", "find_stage2_tool", "REPO", "trustd"),
            ("tests/e2e_basic_contracts_smoke.sh", "find_standalone_targo", "TRUST_ROOT", ""),
            ("tests/e2e_targo_trust_cli.sh", "find_standalone_targo", "TRUST_ROOT", ""),
            ("tests/e2e_targo_trust_root_resolution.sh", "find_standalone_targo", "TRUST_ROOT", ""),
        ]
        with tempfile.TemporaryDirectory() as tmp:
            root = noindex_checkout(Path(tmp))
            sysroot = stage2(root)
            for script, function, variable, argument in cases:
                with self.subTest(script=script):
                    body = shell_function(REPO_ROOT / script, function)
                    program = f'{variable}="$1"\n{body}{function} {argument}\n'
                    result = subprocess.run(
                        ["bash", "-c", program, "bash", str(root)],
                        capture_output=True, text=True, check=False,
                    )
                    self.assertEqual(result.returncode, 0, result.stderr)
                    found = Path(result.stdout.strip())
                    self.assertEqual(found.parent.resolve(), (sysroot / "bin").resolve())
                    # The lexical `build/` spelling survives: -H follows only the
                    # start path, so reports still read `build/<host>/...`.
                    self.assertIn("/build/", result.stdout)


# --------------------------------------------------------------------------
# 2 + 3. containment and guards
# --------------------------------------------------------------------------
class SanctionedLayoutPredicateTests(unittest.TestCase):
    def layouts(self, tmp: Path):
        """(name, root, expected) for every shape `build` can take."""
        outside = tmp / "outside"
        outside.mkdir()
        rows = []

        def checkout(name: str) -> Path:
            root = tmp / name
            root.mkdir()
            return root.resolve()

        root = checkout("real-dir")
        (root / "build").mkdir()
        rows.append(("real directory", root, False))

        root = checkout("sanctioned")
        (root / "build.noindex").mkdir()
        (root / "build").symlink_to("build.noindex", target_is_directory=True)
        rows.append(("relative link to build.noindex", root, True))

        root = checkout("sanctioned-absolute")
        (root / "build.noindex").mkdir()
        (root / "build").symlink_to(root / "build.noindex", target_is_directory=True)
        rows.append(("absolute link to build.noindex", root, True))

        root = checkout("outside-link")
        (root / "build").symlink_to(outside, target_is_directory=True)
        rows.append(("link outside the checkout", root, False))

        root = checkout("inside-other")
        (root / "elsewhere").mkdir()
        (root / "build").symlink_to("elsewhere", target_is_directory=True)
        rows.append(("link to another in-checkout directory", root, False))

        root = checkout("noindex-is-link")
        (root / "build.noindex").symlink_to(outside, target_is_directory=True)
        (root / "build").symlink_to("build.noindex", target_is_directory=True)
        rows.append(("build.noindex is itself a link", root, False))

        root = checkout("dangling")
        (root / "build").symlink_to("build.noindex", target_is_directory=True)
        rows.append(("dangling link", root, False))

        root = checkout("absent")
        rows.append(("no build at all", root, False))
        return rows

    def test_every_inlined_copy_admits_exactly_the_sanctioned_link(self):
        with tempfile.TemporaryDirectory() as tmp:
            for label, root, expected in self.layouts(Path(tmp)):
                for name, predicate in PREDICATES.items():
                    with self.subTest(layout=label, copy=name):
                        self.assertIsNotNone(predicate, f"{name} has no is_sanctioned_build_link")
                        self.assertIs(predicate(root), expected)


class MintSeedSupportTests(unittest.TestCase):
    def test_work_directory_publish_and_cleanup_through_the_link(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = noindex_checkout(Path(tmp))
            work = MINT.make_work_directory(root)
            self.assertEqual(work.parent, root / "build.noindex")
            candidate = work / "seed"
            candidate.mkdir()
            (candidate / "proof").write_text("exact")
            final = root / "build" / "published-seed"
            MINT.verify_output_path(root, final, "test seed")
            MINT.publish_directory(root, candidate, final, "test seed")
            self.assertEqual((root / "build.noindex" / "published-seed" / "proof").read_text(), "exact")
            MINT.cleanup_work_directory(root, work)
            self.assertFalse(work.exists())

    def test_any_other_build_link_is_still_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            outside = Path(tmp) / "outside"
            outside.mkdir()
            root = (Path(tmp) / "checkout")
            root.mkdir()
            root = root.resolve()
            (root / "build").symlink_to(outside, target_is_directory=True)
            for call in (
                lambda: MINT.make_work_directory(root),
                lambda: MINT.verify_output_path(root, root / "build" / "x", "test seed"),
            ):
                with self.assertRaisesRegex(MINT.WorkflowError, "non-symlink directory"):
                    call()
            self.assertEqual(list(outside.iterdir()), [])


class RecreateBootstrapTests(unittest.TestCase):
    def test_cargo_authority_admits_the_sanctioned_link_only(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = noindex_checkout(Path(tmp))
            _authority, errors = RECREATE.bootstrap_cargo_authority(root)
            self.assertFalse([e for e in errors if "real directory" in e], errors)
            (root / "build").unlink()
            outside = Path(tmp) / "outside"
            outside.mkdir()
            (root / "build").symlink_to(outside, target_is_directory=True)
            _authority, errors = RECREATE.bootstrap_cargo_authority(root)
            self.assertTrue([e for e in errors if "real directory" in e], errors)

    def test_fresh_seed_quarantine_works_through_the_link(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = noindex_checkout(Path(tmp))
            stage0 = root / "build.noindex" / HOST / "stage0"
            executable(stage0 / "bin" / "trustc")
            with contextlib.redirect_stdout(io.StringIO()):
                quarantine = RECREATE.quarantine_seed_stage0(root, HOST)
            self.assertIsNotNone(quarantine)
            self.assertFalse(stage0.exists())
            self.assertTrue((root / "build.noindex" / HOST / "stage0.preexisting-fresh-seed").is_dir())


class OffStockAuditTests(unittest.TestCase):
    def test_writable_audit_parent_is_refused_behind_the_sanctioned_link(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = noindex_checkout(Path(tmp))
            parent = root / "build.noindex"
            parent.chmod(0o770)
            with contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(OFF_STOCK.make_audit_dir(str(root / "build")), 1)
            self.assertEqual(list(parent.iterdir()), [])

    def test_stage2_output_and_trace_accept_a_build_root_resolved_through_the_link(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = noindex_checkout(Path(tmp))
            stage2(root, ("trustc",))
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                status = OFF_STOCK.stage2_output(str(root), str(root / "build"))
            self.assertEqual(status, 0, out.getvalue())
            self.assertIn("fresh stage2 compiler output", out.getvalue())
            trace = root / "exec.trace"
            trace.write_text("", encoding="utf-8")
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                OFF_STOCK.trace_audit(str(root), str(root / "build"), str(trace))
            self.assertNotIn("outside the checkout build directory", out.getvalue())

    def test_audit_dir_is_created_behind_the_link_and_other_links_are_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = noindex_checkout(Path(tmp))
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                status = OFF_STOCK.make_audit_dir(str(root / "build"))
            self.assertEqual(status, 0)
            self.assertEqual(Path(out.getvalue().strip()).parent, root / "build.noindex")

            outside = Path(tmp) / "outside"
            outside.mkdir()
            elsewhere = root / "elsewhere-link"
            elsewhere.symlink_to(outside, target_is_directory=True)
            with contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(OFF_STOCK.make_audit_dir(str(elsewhere)), 1)
            self.assertEqual(list(outside.iterdir()), [])


class LambdaDiagnosticTests(unittest.TestCase):
    def test_stage_root_selection_through_the_link(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = noindex_checkout(Path(tmp))
            sysroot = stage2(root)
            self.assertEqual(LAMBDA.resolve_stage_root(root, None), sysroot)
            self.assertEqual(
                LAMBDA.resolve_stage_root(root, str(root / "build.noindex" / HOST / "stage2")),
                sysroot,
            )

    def test_an_unsanctioned_in_checkout_link_is_still_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = (Path(tmp) / "checkout")
            (root / "elsewhere" / HOST / "stage2").mkdir(parents=True)
            root = root.resolve()
            (root / "build").symlink_to("elsewhere", target_is_directory=True)
            with self.assertRaises(LAMBDA.EvidenceError):
                LAMBDA.resolve_stage_root(root, None)


class StrictSuperiorityMetadataTests(unittest.TestCase):
    def embedded_validator(self) -> str:
        text = (REPO_ROOT / "scripts" / "collect_strict_superiority_artifacts.sh").read_text()
        opener = 'STAGE2_SYSROOT="$("$PYTHON_BIN" - "$STAGE2_INFO" "$ROOT" "$REVIEWED_COMMIT" <<\'PY\'\n'
        start = text.index(opener) + len(opener)
        return text[start : text.index("\nPY\n", start)] + "\n"

    def test_validated_stage2_metadata_accepts_a_sysroot_behind_the_link(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = noindex_checkout(Path(tmp))
            sysroot = stage2(root, ("trustc", "targo-trust"))
            info = Path(tmp) / "stage2.json"
            info.write_text(json.dumps({
                "schema_version": "trust.stage2-preflight.v1",
                "toolchain_checkout_match": True,
                "trustc_commit": "c0ffee",
                "sysroot": str(root / "build" / HOST / "stage2"),
                "trustc": str(root / "build" / HOST / "stage2" / "bin" / "trustc"),
                "host_triple": HOST,
            }))
            result = subprocess.run(
                [sys.executable, "-", str(info), str(root), "c0ffee"],
                input=self.embedded_validator(), capture_output=True, text=True, check=False,
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(Path(result.stdout.strip()), sysroot)


class RepositoryWalkerPruneTests(unittest.TestCase):
    """os.walk never follows the `build` link, but WOULD descend `build.noindex`."""

    def test_repo_wide_walkers_prune_the_noindex_directory(self):
        spec = PREFLIGHT_SPEC
        assert spec is not None and spec.loader is not None
        preflight = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = preflight
        spec.loader.exec_module(preflight)
        for label, prune in (
            ("tools/preflight.py PRUNE_DIRS", preflight.PRUNE_DIRS),
            ("scripts/trust_version_sync.py WALK_PRUNE", VERSION_SYNC.WALK_PRUNE),
        ):
            with self.subTest(label):
                self.assertIn("build", prune)
                self.assertIn("build.noindex", prune)

    def test_gitignore_and_rustfmt_ignore_the_noindex_directory(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = noindex_checkout(Path(tmp))
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            shutil.copy2(REPO_ROOT / ".gitignore", root / ".gitignore")
            (root / "build.noindex" / "artifact").write_text("x")
            status = subprocess.run(
                ["git", "-C", str(root), "status", "--porcelain", "--untracked-files=all"],
                capture_output=True, text=True, check=True,
            ).stdout
            self.assertEqual(status.strip(), "?? .gitignore")
        rustfmt = (REPO_ROOT / "rustfmt.toml").read_text(encoding="utf-8")
        self.assertIn('"/build.noindex/"', rustfmt)


if __name__ == "__main__":
    unittest.main()
