#!/usr/bin/env python3
"""Mutation tests for the committed first-party constellation validator.

Fixtures contain real Cargo manifests, lockfiles, Lake manifests, proof identity,
Git history, and nine committed gitlinks.  No state-file stand-in is used.

ONE THING IS STUBBED, and only in the tests that judge a synthetic constellation:
the live ``git ls-remote`` of trust-wp's canonical main becomes an ``ls-remote``
of the fixture's LOCAL remote repository (or the sha a test names), and the
ruling's W0/B constants are bound to the fixture's own base and floor commits
so the fixture's byte-exact v3 marker can spell them.  Every other read is the
real one.  The real-history test, which stubs the same sample with the
submodule's remote-tracking ``origin/main``, is dependency_cycle_anchor_history_test.
"""

from __future__ import annotations

import copy
import contextlib
import importlib.util
import io
import json
import os
import re
import subprocess
import sys
import tempfile
import unittest
from dataclasses import dataclass
from datetime import date
from pathlib import Path
from typing import Callable
from unittest import mock


REPO_ROOT = Path(__file__).resolve().parents[2]
SCRIPT = REPO_ROOT / "scripts" / "check_dependency_cycle_anchor.py"
SPEC = importlib.util.spec_from_file_location("dependency_cycle_anchor", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
anchor = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(anchor)


def git(repo: Path, *args: str, check: bool = True) -> str:
    result = subprocess.run(
        ["git", "-C", str(repo), *args],
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if check and result.returncode != 0:
        raise AssertionError(result.stderr or result.stdout)
    return result.stdout.strip()


def init_repo(path: Path) -> None:
    path.mkdir(parents=True)
    git(path, "init", "-q", "-b", "main")
    git(path, "config", "user.name", "constellation-test")
    git(path, "config", "user.email", "constellation-test@example.invalid")


def write(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def commit_all(repo: Path, message: str) -> str:
    git(repo, "add", "-A")
    git(repo, "commit", "-qm", message)
    return git(repo, "rev-parse", "HEAD")


def commit_tree(repo: Path, tree: str, parents: list[str], message: str) -> str:
    command = ["git", "-C", str(repo), "commit-tree", tree]
    for parent in parents:
        command.extend(["-p", parent])
    return subprocess.run(
        command,
        input=message + "\n",
        check=True,
        text=True,
        stdout=subprocess.PIPE,
    ).stdout.strip()


def derived_tree(
    repo: Path,
    base: str,
    updates: dict[str, tuple[str, str] | None],
) -> str:
    """Build a literal tree from ``base`` without changing the worktree."""
    try:
        git(repo, "read-tree", f"{base}^{{tree}}")
        for path, entry in updates.items():
            if entry is None:
                git(repo, "update-index", "--force-remove", "--", path)
            else:
                mode, oid = entry
                git(
                    repo,
                    "update-index",
                    "--add",
                    "--cacheinfo",
                    f"{mode},{oid},{path}",
                )
        return git(repo, "write-tree")
    finally:
        git(repo, "read-tree", "HEAD")


def write_blob(repo: Path, content: bytes) -> str:
    result = subprocess.run(
        ["git", "-C", str(repo), "hash-object", "-w", "--stdin"],
        input=content,
        check=True,
        stdout=subprocess.PIPE,
    )
    return result.stdout.decode("ascii", "strict").strip()


def missing_objects_without_lazy_fetch(repo: Path) -> set[str]:
    """Inventory promised objects without allowing the inventory to fetch them."""
    environment = os.environ.copy()
    environment["GIT_NO_LAZY_FETCH"] = "1"
    result = subprocess.run(
        [
            "git",
            "-C",
            str(repo),
            "rev-list",
            "--objects",
            "--missing=print",
            "HEAD",
        ],
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        env=environment,
    )
    if result.returncode != 0:
        raise AssertionError(result.stderr or result.stdout)
    return {
        row[1:].split(" ", 1)[0]
        for row in result.stdout.splitlines()
        if row.startswith("?")
    }


def package_manifest(name: str, extra: str = "") -> str:
    return (
        "[package]\n"
        f'name = "{name}"\n'
        'version = "0.1.0"\n'
        'edition = "2021"\n'
        + extra
    )


def lockfile(package: str, dependency: str, rev: str) -> str:
    url = anchor.SUBMODULES[dependency][1]
    return (
        "version = 4\n\n"
        "[[package]]\n"
        f'name = "{package}"\n'
        'version = "0.1.0"\n'
        f'source = "git+{url}?rev={rev}#{rev}"\n'
    )


@contextlib.contextmanager
def synthetic_v3_policy(fixture: "Fixture"):
    """Bind the ruling's W0/B constants and marker bytes to the fixture's commits.

    The real constants name commits of the real trust-wp; a synthetic
    constellation carries its own W0 (trust-wp's base) and B (its published
    floor), and the marker the fixture committed spells those.  Nothing else
    about the policy is altered.
    """
    marker = anchor.render_terminal_policy_v3_marker(fixture.wp_w0, fixture.wp_floor)
    remote = str(fixture.remotes["trust-wp"])
    with mock.patch.multiple(
        anchor,
        TRUST_WP_W0=fixture.wp_w0,
        TRUST_WP_PRESERVATION_FLOOR=fixture.wp_floor,
        TERMINAL_POLICY_V3_MARKER=marker,
        # An absent TrustWP commit is fetched by sha from the fixture's own
        # remote, never from github.com.
        trust_wp_fetch_url=lambda: remote,
    ):
        yield


def is_ancestor(repo: Path, ancestor: str, descendant: str) -> bool:
    return (
        subprocess.run(
            ["git", "-C", str(repo), "merge-base", "--is-ancestor", ancestor, descendant],
            check=False,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        ).returncode
        == 0
    )


def wp_child(wp: Path, parent: str, message: str, updates: dict | None = None) -> str:
    """A trust-wp commit on top of ``parent``: its tree plus ``updates``."""
    tree = (
        derived_tree(wp, parent, updates)
        if updates
        else git(wp, "rev-parse", f"{parent}^{{tree}}")
    )
    return commit_tree(wp, tree, [parent], message)


def root_child(
    root: Path,
    parent: str,
    message: str,
    updates: dict | None = None,
    parents: list[str] | None = None,
) -> str:
    """A root commit on top of ``parent`` (or ``parents``) with ``parent``'s tree plus ``updates``."""
    tree = (
        derived_tree(root, parent, updates)
        if updates
        else git(root, "rev-parse", f"{parent}^{{tree}}")
    )
    return commit_tree(root, tree, parents or [parent], message)


def pin_wp(
    root: Path, parent: str, wp_commit: str, message: str, extra: dict | None = None
) -> str:
    """A single-parent root commit that moves the trust-wp gitlink to ``wp_commit``."""
    updates: dict = {anchor.WP_ROOT_DELTA_PATH: ("160000", wp_commit)}
    if extra:
        updates.update(extra)
    return root_child(root, parent, message, updates)


def retire_receipt(root: Path, parent: str) -> str:
    """Drop the tracked legacy receipt so a moved pin is judged by derivation."""
    return root_child(root, parent, "retire the tracked receipt", {anchor.RECEIPT_PATH: None})


def wp_depends_lock(rows: dict[str, str]) -> str:
    return "# Format: <repository> main <full-40-character-commit>\n" + "".join(
        f"{name} main {rows[name]}\n" for name in ("clean", "trust-ir", "trust-cg", "trust", "ay")
    )


def untracked_files_tree(repo: Path) -> str:
    """The tree of a ``git stash -u`` untracked-files commit: only untracked
    files, no ``first-party/`` entry."""
    blob = write_blob(repo, b"fn untracked() {}\n")

    def mktree(entry: str) -> str:
        return subprocess.run(["git", "-C", str(repo), "mktree"], input=entry, check=True, text=True,
                              stdout=subprocess.PIPE).stdout.strip()

    source = mktree(f"100644 blob {blob}\tlib.rs\n")
    return mktree(f"040000 tree {source}\tcrates\n")


def committed_bytes(repo: Path, commit: str, path: str) -> bytes:
    return subprocess.run(
        ["git", "-C", str(repo), "show", f"{commit}:{path}"],
        check=True,
        stdout=subprocess.PIPE,
    ).stdout


@dataclass
class Fixture:
    root: Path
    remotes: dict[str, Path]
    commits: dict[str, str]
    ancestors: dict[str, str]
    receipt: dict[str, object]
    root_genesis: str
    wp_w0: str
    wp_floor: str
    policy_parent: str | None = None
    policy_activation: str | None = None

    def wp_remote_main(self) -> str:
        """The stand-in for the live sample: ``ls-remote`` of the LOCAL remote.

        Same command, same ref, a local path instead of github.com.  This is
        the only thing these tests stub about the policy.
        """
        result = subprocess.run(
            ["git", "ls-remote", "--exit-code", str(self.remotes["trust-wp"]), "refs/heads/main"],
            check=True,
            text=True,
            stdout=subprocess.PIPE,
        )
        sha, _tab, ref = result.stdout.strip().partition("\t")
        assert ref == "refs/heads/main", result.stdout
        return sha

    def lock_rows(self) -> dict[str, str]:
        """The coherent lock rows the fixture's trust-wp W0 was committed with."""
        return {
            "clean": self.ancestors["clean"],
            "trust-ir": self.commits["trust-ir"],
            "trust-cg": self.ancestors["trust-cg"],
            "trust": self.root_genesis,
            "ay": self.commits["ay"],
        }

    def checkout(self, name: str) -> Path:
        return self.root / anchor.SUBMODULES[name][0]

    def commit_receipt(self, receipt: dict[str, object], message: str = "mutate receipt") -> None:
        write(
            self.root / anchor.RECEIPT_PATH,
            json.dumps(receipt, indent=2, sort_keys=True) + "\n",
        )
        commit_all(self.root, message)
        self.receipt = receipt

    def advance_consumer(
        self,
        name: str,
        mutate: Callable[[Path], None],
        message: str,
    ) -> str:
        checkout = self.checkout(name)
        mutate(checkout)
        commit = commit_all(checkout, message)
        self.commits[name] = commit
        repositories = self.receipt["repositories"]
        assert isinstance(repositories, dict)
        entry = repositories[name]
        assert isinstance(entry, dict)
        entry["commit"] = commit
        bindings = self.receipt["root_bindings"]
        assert isinstance(bindings, list)
        for binding in bindings:
            assert isinstance(binding, dict)
            if binding["repository"] == name:
                binding["commit"] = commit
        write(
            self.root / anchor.RECEIPT_PATH,
            json.dumps(self.receipt, indent=2, sort_keys=True) + "\n",
        )
        git(self.root, "add", anchor.SUBMODULES[name][0], anchor.RECEIPT_PATH)
        git(self.root, "commit", "-qm", f"bind {message}")
        return commit

    def refresh_observed_receipt(self, message: str) -> list[dict[str, object]]:
        exclusions = self.receipt["exclusions"]
        assert isinstance(exclusions, list)
        surfaces = anchor.scan_constellation(
            self.root,
            git(self.root, "rev-parse", "HEAD"),
            self.commits,
            exclusions,
        )
        anchor.validate_resolutions(surfaces, self.commits)
        edges = anchor.derive_direct_edges(surfaces, self.commits)
        anchor.validate_generation_graph(edges, self.commits)
        anchors = anchor.required_anchors(edges, self.commits)
        self.receipt["surfaces"] = surfaces
        self.receipt["direct_edges"] = edges
        self.receipt["anchors"] = anchors
        self.commit_receipt(self.receipt, message)
        return edges


def make_fixture(base: Path, *, v3_marker: bool = True) -> Fixture:
    remotes: dict[str, Path] = {}
    commits: dict[str, str] = {}
    ancestors: dict[str, str] = {}

    # The root first, with a genesis commit: trust-wp's lock names a Trust
    # commit, and P3 needs that row to be an ancestor of every judged revision.
    root = base / "root"
    init_repo(root)
    git(root, "commit", "-q", "--allow-empty", "-m", "trust genesis")
    genesis = git(root, "rev-parse", "HEAD")

    # Dependency repositories with actual ancestor cuts.
    for name in ("clean", "trust-cg"):
        repo = base / "remotes" / name
        init_repo(repo)
        write(repo / "Cargo.toml", package_manifest(name))
        ancestors[name] = commit_all(repo, f"{name} bootstrap")
        write(repo / "README.md", f"{name} terminal\n")
        commits[name] = commit_all(repo, f"{name} terminal")
        remotes[name] = repo

    # Leaf repositories first, so consumers can pin real commits.
    for name in ("trust-vc", "ty"):
        repo = base / "remotes" / name
        init_repo(repo)
        write(repo / "Cargo.toml", package_manifest(name))
        commits[name] = commit_all(repo, f"{name} terminal")
        remotes[name] = repo

    ay = base / "remotes" / "ay"
    init_repo(ay)
    cg_url = anchor.SUBMODULES["trust-cg"][1]
    write(
        ay / "Cargo.toml",
        package_manifest(
            "ay",
            '\n[workspace]\nmembers = ["fixtures"]\nexclude = ["fixtures"]\n'
            '\n[workspace.package]\nversion = "0.1.0"\n'
            "\n[dependencies]\n"
            f'cg-core = {{ package = "trust-cg", git = "{cg_url}", '
            f'rev = "{ancestors["trust-cg"]}", optional = true }}\n',
        ),
    )
    write(ay / "Cargo.lock", lockfile("trust-cg", "trust-cg", ancestors["trust-cg"]))
    clean_url = anchor.SUBMODULES["clean"][1]
    write(
        ay / "fixtures" / "Cargo.toml",
        package_manifest(
            "ay-fixture",
            "\n[dependencies]\n"
            f'clean = {{ git = "{clean_url}", rev = "{ancestors["clean"]}" }}\n',
        ),
    )
    write(
        ay / "fixtures" / "Cargo.lock",
        lockfile("clean", "clean", ancestors["clean"]),
    )
    commits["ay"] = commit_all(ay, "AY manifest and excluded fixture")
    remotes["ay"] = ay

    ir = base / "remotes" / "trust-ir"
    init_repo(ir)
    write(
        ir / "Cargo.toml",
        package_manifest(
            "trust-ir",
            "\n[dependencies]\n"
            f'clean = {{ git = "{clean_url}", rev = "{ancestors["clean"]}" }}\n\n'
            f'[patch."{clean_url}"]\n'
            'clean = { path = "../clean" }\n',
        ),
    )
    commits["trust-ir"] = commit_all(ir, "IR path-patched Clean authority")
    remotes["trust-ir"] = ir

    mc = base / "remotes" / "trust-mc"
    init_repo(mc)
    vc_url = anchor.SUBMODULES["trust-vc"][1]
    write(
        mc / "Cargo.toml",
        package_manifest(
            "trust-mc",
            "\n[dependencies]\n"
            f'trust-vc = {{ git = "{vc_url}", rev = "{commits["trust-vc"]}" }}\n',
        ),
    )
    write(
        mc / "Cargo.lock",
        lockfile("trust-vc", "trust-vc", commits["trust-vc"])
        + "\n[[package]]\n"
        + 'name = "clean"\n'
        + 'version = "0.1.0"\n'
        + f'source = "git+{clean_url}?rev={commits["clean"]}#{commits["clean"]}"\n',
    )
    commits["trust-mc"] = commit_all(mc, "MC pins VC")
    remotes["trust-mc"] = mc

    # trust-wp last: its lock binds every cohort row to a real sibling commit
    # (each an ancestor-or-equal of the gitlink, P3) and the trust row to
    # genesis.  Its base commit plays W0 and is what the root pins; its
    # published floor B is W0's child and is where the remote's main stays,
    # so the fixture's remote main contains B (P1) and W0 is on the canonical
    # line.
    wp = base / "remotes" / "trust-wp"
    init_repo(wp)
    write(wp / "Cargo.toml", package_manifest("trust-wp"))
    write(wp / "Cargo.lock", "version = 4\n")
    write(
        wp / anchor.WP_DEPENDS_PATH,
        wp_depends_lock(
            {
                "clean": ancestors["clean"],
                "trust-ir": commits["trust-ir"],
                "trust-cg": ancestors["trust-cg"],
                "trust": genesis,
                "ay": commits["ay"],
            }
        ),
    )
    wp_w0 = commit_all(wp, "trust-wp W0")
    write(wp / "published.txt", "published floor B\n")
    wp_floor = commit_all(wp, "published floor B")
    commits["trust-wp"] = wp_w0
    remotes["trust-wp"] = wp

    ny = base / "remotes" / "ny"
    init_repo(ny)
    write(ny / "Cargo.toml", package_manifest("ny"))
    cert_dir = ny / "crates" / "ny-cert"
    proof_dir = cert_dir / "proofs" / "lean"
    write(
        cert_dir / "SPEC.md",
        "Clean is pinned proof authority. The Lake file uses private Clean commit "
        f"`{commits['clean']}` with `subDir = \"crown-proofs/lean\"`; "
        "the dependency supplies Crownproof.\n",
    )
    write(
        cert_dir / "proofs" / "README.md",
        "Clean's `Crownproof` library supplies the checked theorems at exact commit "
        f"`{commits['clean']}`.\n",
    )
    write(
        proof_dir / "PROVENANCE.md",
        "```text\n"
        f"repository: {clean_url}\n"
        f"revision:   {commits['clean']}\n"
        "subDir:     crown-proofs/lean\n"
        "```\n",
    )
    write(
        proof_dir / "lakefile.toml",
        'name = "nyproof"\nversion = "0.1.0"\n\n'
        "[[require]]\n"
        'name = "crownproof"\n'
        f'git = "{clean_url}"\n'
        f'rev = "{commits["clean"]}"\n'
        'subDir = "crown-proofs/lean"\n',
    )
    lake_package = {
        "url": clean_url,
        "type": "git",
        "subDir": "crown-proofs/lean",
        "scope": "",
        "rev": commits["clean"],
        "name": "crownproof",
        "manifestFile": "lake-manifest.json",
        "inputRev": commits["clean"],
        "inherited": False,
        "configFile": "lakefile.toml",
    }
    write(
        proof_dir / "lake-manifest.json",
        json.dumps({"version": "1.2.0", "packages": [lake_package]}) + "\n",
    )
    write(
        cert_dir / "proofs" / "cite-map.json",
        json.dumps(
            {
                "corpus": {
                    "source": "lake-git-dependency",
                    "package": "crownproof",
                    "git": clean_url,
                    "rev": commits["clean"],
                    "subDir": "crown-proofs/lean",
                }
            }
        )
        + "\n",
    )
    write(
        cert_dir / "src" / "cite_check.rs",
        'pub const CLEAN_LAKE_PACKAGE: &str = "crownproof";\n'
        f'pub const CLEAN_GIT_URL: &str = "{clean_url}";\n'
        f'pub const CLEAN_GIT_REV: &str = "{commits["clean"]}";\n'
        'pub const CLEAN_LAKE_SUBDIR: &str = "crown-proofs/lean";\n',
    )
    commits["ny"] = commit_all(ny, "NY Lake proof identity")
    remotes["ny"] = ny

    dependencies = ["[package]", 'name = "trust-root-fixture"', 'version = "0.1.0"', 'edition = "2021"', "", "[dependencies]"]
    for name, (path, _url) in sorted(anchor.SUBMODULES.items()):
        dependencies.append(f'{name} = {{ path = "{path}" }}')
    dependencies.extend(
        [
            "",
            f'[patch."{anchor.SUBMODULES["trust-ir"][1].removesuffix(".git")}"]',
            'trust-ir = { path = "first-party/trust-ir" }',
        ]
    )
    write(root / "Cargo.toml", "\n".join(dependencies) + "\n")
    for name, (path, canonical_url) in anchor.SUBMODULES.items():
        subprocess.run(
            [
                "git",
                "-C",
                str(root),
                "-c",
                "protocol.file.allow=always",
                "submodule",
                "add",
                "-q",
                str(remotes[name]),
                path,
            ],
            check=True,
        )
        git(root, "config", "-f", ".gitmodules", f"submodule.{path}.url", canonical_url)
    # The clone of trust-wp checked out its main (B); the root pins W0.
    git(root / anchor.SUBMODULES["trust-wp"][0], "checkout", "-q", "--detach", wp_w0)
    git(root, "add", anchor.SUBMODULES["trust-wp"][0])
    # The v2 marker is carried as history, as real main carries it.
    (root / anchor.TERMINAL_POLICY_V2_MARKER_PATH).write_bytes(
        anchor.TERMINAL_POLICY_V2_PRE_MARKER
    )
    if v3_marker:
        (root / anchor.TERMINAL_POLICY_V3_MARKER_PATH).write_bytes(
            anchor.render_terminal_policy_v3_marker(wp_w0, wp_floor)
        )
    commit_all(root, "root terminal tuple")

    exclusions = [
        {
            "repository": "ay",
            "path": "fixtures",
            "reason": "non-workspace regression fixture with deliberately historical dependency pins",
        }
    ]
    surfaces = anchor.scan_constellation(root, git(root, "rev-parse", "HEAD"), commits, exclusions)
    anchor.validate_resolutions(surfaces, commits)
    edges = anchor.derive_direct_edges(surfaces, commits)
    anchors = anchor.required_anchors(edges, commits)
    bindings = [
        {
            "repository": name,
            "path": path,
            "url": url,
            "commit": commits[name],
        }
        for name, (path, url) in sorted(anchor.SUBMODULES.items())
    ]
    receipt: dict[str, object] = {
        "schema": anchor.SCHEMA,
        "self": {"repository": "trust", "commit": anchor.SELF_SENTINEL},
        "repositories": {
            name: {"url": anchor.SUBMODULES[name][1], "commit": commits[name]}
            for name in sorted(anchor.SUBMODULES)
        },
        "root_bindings": bindings,
        "exclusions": exclusions,
        "surfaces": surfaces,
        "direct_edges": edges,
        "anchors": anchors,
    }
    write(
        root / anchor.EXCLUSIONS_PATH,
        json.dumps(
            {"schema": anchor.EXCLUSIONS_SCHEMA, "exclusions": exclusions},
            indent=2,
            sort_keys=True,
        )
        + "\n",
    )
    write(
        root / anchor.RECEIPT_PATH,
        json.dumps(receipt, indent=2, sort_keys=True) + "\n",
    )
    commit_all(root, "committed constellation receipt")
    policy_parent = git(root, "rev-parse", "HEAD")
    write(
        root / anchor.TERMINAL_POLICY_MARKER_PATH,
        anchor.TERMINAL_POLICY_MARKER.decode("ascii"),
    )
    policy_activation = commit_all(root, "activate immutable terminal policy")
    return Fixture(
        root,
        remotes,
        commits,
        ancestors,
        receipt,
        root_genesis=genesis,
        wp_w0=wp_w0,
        wp_floor=wp_floor,
        policy_parent=policy_parent,
        policy_activation=policy_activation,
    )


class StrictShapeTests(unittest.TestCase):
    def test_duplicate_json_key_is_rejected(self) -> None:
        with self.assertRaisesRegex(anchor.AnchorError, "duplicate JSON key"):
            anchor.parse_json(b'{"schema":"a","schema":"b"}', "receipt")

    def test_invalid_utf8_is_rejected(self) -> None:
        with self.assertRaisesRegex(anchor.AnchorError, "valid UTF-8"):
            anchor.parse_json(b"\xff", "receipt")

    def test_short_uppercase_and_zero_shas_are_rejected(self) -> None:
        for value in ("abc", "A" * 40, "0" * 40):
            with self.subTest(value=value), self.assertRaises(anchor.AnchorError):
                anchor.require_sha(value, "pin")

    def test_v3_marker_parser_names_each_malformation(self) -> None:
        canonical = anchor.TERMINAL_POLICY_V3_MARKER
        anchor.parse_terminal_policy_v3(canonical)
        rows = canonical.decode("ascii")[:-1].split("\n")
        cases = {
            "not-terminated": (canonical[:-1], "not newline-terminated"),
            "uppercase": (canonical.upper(), "row 1 differs"),
            "extra-row": (canonical + b"extra=authority\n", "row count differs"),
            "short": (b"\n".join(canonical.split(b"\n")[:-2]) + b"\n", "row count differs"),
            "reordered": (
                ("\n".join([rows[1], rows[0], *rows[2:]]) + "\n").encode("ascii"),
                "row 1 differs",
            ),
            "duplicate": (("\n".join([*rows[:5], rows[4]]) + "\n").encode("ascii"), "row 6 differs"),
            "edited-date": (canonical.replace(b"ruled=2026-09-21", b"ruled=2026-09-22"), "row 6 differs"),
            "edited-w0": (canonical.replace(anchor.TRUST_WP_W0.encode("ascii"), b"0" * 40), "row 4 differs"),
            "non-ascii": (canonical.replace(b"policy=", "policy=\u00e9".encode("utf-8")), "not ASCII"),
            "crlf": (canonical.replace(b"\n", b"\r\n"), "row 1 differs"),
            "empty": (b"", "not newline-terminated"),
        }
        for label, (raw, needle) in cases.items():
            with self.subTest(label=label), self.assertRaisesRegex(anchor.AnchorError, needle):
                anchor.parse_terminal_policy_v3(raw)

    def test_first_party_url_aliases_are_rejected(self) -> None:
        for value in (
            "https://github.com/alabsystems/ay",
            "git@github.com:alabsystems/ay.git",
            "ssh://git@github.com/alabsystems/ay.git",
        ):
            with self.subTest(value=value), self.assertRaisesRegex(anchor.AnchorError, "alias"):
                anchor.first_party_url(value, "test")
        self.assertEqual(
            anchor.first_party_url(
                "ssh://git@github.com:22/alabsystems/trust-ir.git",
                "patch",
                allow_alias=True,
            ),
            "trust-ir",
        )

    def test_malformed_and_unknown_first_party_urls_are_never_externalized(self) -> None:
        for value in (
            "https://github.com/alabsystems/ay.git?branch=x",
            "https://github.com/alabsystems/ay.git#x",
            "https://github.com/alabsystems/ay.git/extra",
            "https://github.com/alabsystems/new-repo.git",
            "https://github.com/alabsystems/ay.git",
            "https://github.com/%61ndrewyatesai/ay.git",
            "https://github.com/%2561ndrewyatesai/ay.git",
        ):
            with self.subTest(value=value), self.assertRaisesRegex(
                anchor.AnchorError, "malformed or out-of-policy"
            ):
                anchor.first_party_url(value, "test")

    def test_malformed_surface_marker_detection_is_case_insensitive(self) -> None:
        self.assertTrue(
            anchor.might_reference_first_party(
                b'git = "https://github.com/alabsystems/ay.git"\ninvalid = ['
            )
        )

    def test_local_and_file_git_locators_are_rejected(self) -> None:
        for value in ("file:///tmp/first-party/ay", "../ay", "repos/ay"):
            with self.subTest(value=value), self.assertRaisesRegex(
                anchor.AnchorError, "unsupported local/file Git locator"
            ):
                anchor.first_party_url(value, "test")

    def test_lock_resolution_allows_coexisting_and_unused_workspace_revisions(self) -> None:
        expected = "1" * 40
        historical = "2" * 40

        def manifest(locator: str) -> dict[str, object]:
            return anchor.make_surface(
                repository="trust",
                scope="canonical",
                kind="cargo-git",
                path="Cargo.toml",
                locator=locator,
                dependency="ay",
                package="ay",
                url=anchor.SUBMODULES["ay"][1],
                rev=expected,
                dependency_path=None,
                subdir=None,
                optional=False,
            )

        def lock(rev: str, index: int) -> dict[str, object]:
            return anchor.make_surface(
                repository="trust",
                scope="canonical",
                kind="cargo-lock",
                path="Cargo.lock",
                locator=f"/package/{index}:ay@0.1.0",
                dependency="ay",
                package="ay",
                url=anchor.SUBMODULES["ay"][1],
                rev=rev,
                dependency_path=None,
                subdir=None,
                optional=None,
            )

        anchor.validate_resolutions(
            [manifest("/dependencies/ay"), lock(historical, 0), lock(expected, 1)],
            {},
        )
        anchor.validate_resolutions(
            [manifest("/workspace/dependencies/ay"), lock(historical, 0)],
            {},
        )
        with self.assertRaisesRegex(
            anchor.AnchorError, "absent from its nearest Cargo.lock"
        ):
            anchor.validate_resolutions(
                [manifest("/dependencies/ay"), lock(historical, 0)],
                {},
            )


class CommittedConstellationTests(unittest.TestCase):
    def fixture(self, temporary: str, **options: bool) -> Fixture:
        return make_fixture(Path(temporary), **options)

    def run_checker(
        self,
        fixture: Fixture,
        *arguments: str,
        env: dict[str, str] | None = None,
        wp_remote_main: str | None = None,
    ) -> subprocess.CompletedProcess[str]:
        """Run the real CLI in-process.

        Exactly one thing is replaced: the live ``ls-remote`` of trust-wp's
        canonical main becomes an ``ls-remote`` of the fixture's local remote
        (or the sha a test names), and the ruling's W0/B are bound to the
        fixture's own commits.  Every other read is the real one.
        """
        remote = fixture.wp_remote_main() if wp_remote_main is None else wp_remote_main
        stdout, stderr = io.StringIO(), io.StringIO()
        with contextlib.ExitStack() as stack:
            if env is not None:
                stack.enter_context(mock.patch.dict(os.environ, env, clear=True))
            stack.enter_context(synthetic_v3_policy(fixture))
            stack.enter_context(
                mock.patch.object(anchor, "sample_trust_wp_remote_main", return_value=remote)
            )
            stack.enter_context(contextlib.redirect_stdout(stdout))
            stack.enter_context(contextlib.redirect_stderr(stderr))
            returncode = anchor.main(["--repo-root", str(fixture.root), *arguments])
        return subprocess.CompletedProcess(
            [str(SCRIPT), "--repo-root", str(fixture.root), *arguments],
            returncode,
            stdout.getvalue(),
            stderr.getvalue(),
        )

    def policy(
        self,
        fixture: Fixture,
        revision: str,
        commits: dict[str, str],
        remote: str | None = None,
    ) -> dict[str, object]:
        """P1/P2/P4 on one revision, with the same single stub as run_checker."""
        remote = fixture.wp_remote_main() if remote is None else remote
        with synthetic_v3_policy(fixture), contextlib.redirect_stderr(io.StringIO()):
            return anchor.validate_trust_wp_policy(fixture.root, revision, commits, remote)

    def policy_with_diagnostic(
        self, fixture: Fixture, revision: str, commits: dict[str, str]
    ) -> tuple[dict[str, object], list[dict[str, object]]]:
        stderr = io.StringIO()
        with synthetic_v3_policy(fixture), contextlib.redirect_stderr(stderr):
            verdict = anchor.validate_trust_wp_policy(
                fixture.root, revision, commits, fixture.wp_remote_main()
            )
        prefix = "DEPENDENCY CONSTELLATION SAME-LOCK RECOVERY "
        reports = [
            json.loads(line[len(prefix):])
            for line in stderr.getvalue().splitlines()
            if line.startswith(prefix)
        ]
        return verdict, reports

    def assert_policy_refuses(
        self,
        fixture: Fixture,
        revision: str,
        commits: dict[str, str],
        needle: str,
        remote: str | None = None,
    ) -> str:
        remote = fixture.wp_remote_main() if remote is None else remote
        with synthetic_v3_policy(fixture), contextlib.redirect_stderr(io.StringIO()):
            with self.assertRaises(anchor.AnchorError) as raised:
                anchor.validate_trust_wp_policy(fixture.root, revision, commits, remote)
        message = str(raised.exception)
        self.assertIn(needle, message)
        return message

    def assert_failure(self, result: subprocess.CompletedProcess[str], needle: str) -> None:
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn(needle, result.stderr)

    def test_checked_in_v3_marker_binds_ratified_real_constants(self) -> None:
        self.assertEqual(anchor.TRUST_WP_W0, "e7c353690e1b58a4e830edc9facb0e4396164585")
        self.assertEqual(
            anchor.TRUST_WP_PRESERVATION_FLOOR, "1de995e192aabec74646d4d53642df05fa59466f"
        )
        checked_in = (REPO_ROOT / anchor.TERMINAL_POLICY_V3_MARKER_PATH).read_bytes()
        self.assertEqual(checked_in, anchor.TERMINAL_POLICY_V3_MARKER)
        anchor.parse_terminal_policy_v3(checked_in)
        self.assertEqual(
            checked_in.decode("ascii").split("\n")[:3],
            [
                "trust.constellation.terminal-policy.v3",
                "policy=trust-wp-cohort-forward",
                "supersedes=trust-wp-root-cycle-forward",
            ],
        )
        self.assertTrue(checked_in.endswith(b"ruled=2026-09-21\n"))
        # The v1 and v2 markers are untouched history.
        self.assertEqual(
            (REPO_ROOT / anchor.TERMINAL_POLICY_MARKER_PATH).read_bytes(),
            anchor.TERMINAL_POLICY_MARKER,
        )
        self.assertEqual(
            (REPO_ROOT / anchor.TERMINAL_POLICY_V2_MARKER_PATH).read_bytes(),
            anchor.TERMINAL_POLICY_V2_PRE_MARKER,
        )

    def test_receipt_schema_is_exact_at_every_level(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            for mutation in ("missing-top", "extra-top", "extra-surface", "duplicate-id"):
                with self.subTest(mutation=mutation):
                    receipt = copy.deepcopy(fixture.receipt)
                    if mutation == "missing-top":
                        del receipt["anchors"]
                    elif mutation == "extra-top":
                        receipt["waiver"] = True
                    elif mutation == "extra-surface":
                        surfaces = receipt["surfaces"]
                        assert isinstance(surfaces, list) and isinstance(surfaces[0], dict)
                        surfaces[0]["note"] = "not in schema"
                    else:
                        surfaces = receipt["surfaces"]
                        assert isinstance(surfaces, list)
                        surfaces.append(copy.deepcopy(surfaces[0]))
                    with self.assertRaises(anchor.AnchorError):
                        anchor.validate_receipt(receipt)

    def test_real_committed_surfaces_pass_and_inventory_mode_is_deterministic(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            result = self.run_checker(fixture)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("DEPENDENCY CONSTELLATION OK", result.stdout)

            first = self.run_checker(fixture, "--print-observed")
            second = self.run_checker(fixture, "--print-observed")
            self.assertEqual(first.returncode, 0, first.stderr)
            self.assertEqual(first.stdout, second.stdout)
            observed = json.loads(first.stdout)
            self.assertEqual(observed["surfaces"], fixture.receipt["surfaces"])
            self.assertEqual(observed["direct_edges"], fixture.receipt["direct_edges"])
            self.assertTrue(
                any(row["kind"] == "cargo-git" and row["optional"] is True for row in observed["surfaces"])
            )
            ir_edge = next(
                row
                for row in observed["direct_edges"]
                if row["consumer"] == "trust-ir" and row["dependency"] == "clean"
            )
            self.assertEqual(ir_edge["commit"], fixture.commits["clean"])
            self.assertTrue(any("cargo-patch-path" in item for item in ir_edge["surfaces"]))
            ny_edge = next(
                row
                for row in observed["direct_edges"]
                if row["consumer"] == "ny" and row["dependency"] == "clean"
            )
            self.assertEqual(len(ny_edge["surfaces"]), 7)
            self.assertEqual(
                {
                    row["path"]
                    for row in observed["surfaces"]
                    if row["id"] in ny_edge["surfaces"]
                },
                anchor.NY_IDENTITY_PATHS,
            )
            self.assertTrue(
                any(
                    row["kind"] == "cargo-patch-path"
                    and row["url"] == anchor.SUBMODULES["trust-ir"][1].removesuffix(".git")
                    for row in observed["surfaces"]
                )
            )

    def test_dirty_receipt_and_manifests_cannot_forge_committed_authority(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            write(fixture.root / anchor.RECEIPT_PATH, "not JSON\n")
            write(fixture.checkout("ay") / "Cargo.toml", "not TOML\n")
            result = self.run_checker(fixture)
            self.assertEqual(result.returncode, 0, result.stderr)

    def test_receipt_surface_omission_extra_and_transitive_as_direct_fail(self) -> None:
        for mutation in ("omission", "extra", "transitive-direct"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as temporary:
                fixture = self.fixture(temporary)
                receipt = copy.deepcopy(fixture.receipt)
                surfaces = receipt["surfaces"]
                edges = receipt["direct_edges"]
                assert isinstance(surfaces, list) and isinstance(edges, list)
                if mutation == "omission":
                    surfaces.pop()
                elif mutation == "extra":
                    bogus = copy.deepcopy(surfaces[0])
                    assert isinstance(bogus, dict)
                    bogus["id"] = str(bogus["id"]) + ":invented"
                    surfaces.append(bogus)
                else:
                    transitive_lock = next(
                        row
                        for row in surfaces
                        if isinstance(row, dict)
                        and row["repository"] == "trust-mc"
                        and row["kind"] == "cargo-lock"
                        and row["dependency"] == "clean"
                    )
                    edges.append(
                        {
                            "consumer": "trust-mc",
                            "dependency": "clean",
                            "commit": transitive_lock["rev"],
                            "surfaces": [transitive_lock["id"]],
                        }
                    )
                fixture.commit_receipt(receipt)
                result = self.run_checker(fixture)
                self.assert_failure(result, "independently observed committed state")

    def test_split_direct_manifest_revisions_fail_before_receipt_comparison(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)

            def mutate(checkout: Path) -> None:
                with (checkout / "Cargo.toml").open("a", encoding="utf-8") as handle:
                    handle.write(
                        f'cg-new = {{ package = "trust-cg", git = "{anchor.SUBMODULES["trust-cg"][1]}", '
                        f'rev = "{fixture.commits["trust-cg"]}" }}\n'
                    )

            fixture.advance_consumer("ay", mutate, "split CG revisions")
            result = self.run_checker(fixture)
            self.assert_failure(result, "split revisions")

    def test_manifest_lock_staleness_and_query_fragment_split_fail(self) -> None:
        for mutation in ("stale", "fragment"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as temporary:
                fixture = self.fixture(temporary)

                def mutate(checkout: Path) -> None:
                    content = (checkout / "Cargo.lock").read_text(encoding="utf-8")
                    if mutation == "stale":
                        content = content.replace(
                            fixture.ancestors["trust-cg"], fixture.commits["trust-cg"]
                        )
                    else:
                        content = content.replace(
                            "#" + fixture.ancestors["trust-cg"],
                            "#" + fixture.commits["trust-cg"],
                        )
                    write(checkout / "Cargo.lock", content)

                fixture.advance_consumer("ay", mutate, f"{mutation} Cargo lock")
                result = self.run_checker(fixture)
                needle = "absent from its nearest Cargo.lock" if mutation == "stale" else "query/fragment"
                self.assert_failure(result, needle)

    def test_path_patch_to_wrong_sibling_fails(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)

            def mutate(checkout: Path) -> None:
                content = (checkout / "Cargo.toml").read_text(encoding="utf-8")
                write(checkout / "Cargo.toml", content.replace('path = "../clean"', 'path = "../ay"'))

            fixture.advance_consumer("trust-ir", mutate, "misdirect Clean patch")
            result = self.run_checker(fixture)
            self.assert_failure(result, "splits one dependency")

    def test_casefold_path_alias_and_subrepo_to_root_edge_fail_closed(self) -> None:
        cases = {
            "casefold": ("../clean", "../CLEAN", "noncanonical casing"),
            "root-casefold": (
                '[patch."https://example.invalid/root-case"]\n'
                'root = { path = "../../../ROOT" }\n',
                "",
                "noncanonical casing",
            ),
            "root-edge": (
                '[patch."https://example.invalid/root"]\nroot = { path = "../.." }\n',
                "",
                "subrepository-to-root Cargo path edge",
            ),
        }
        for mutation, (old, new, needle) in cases.items():
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as temporary:
                fixture = self.fixture(temporary)

                def mutate(checkout: Path) -> None:
                    manifest = checkout / "Cargo.toml"
                    content = manifest.read_text(encoding="utf-8")
                    if mutation == "casefold":
                        content = content.replace(old, new)
                    else:
                        content += "\n" + old
                    write(manifest, content)

                fixture.advance_consumer("trust-ir", mutate, mutation)
                self.assert_failure(self.run_checker(fixture), needle)

    def test_valid_uppercase_and_percent_encoded_org_urls_cannot_be_externalized(self) -> None:
        authored_urls = (
            "https://github.com/alabsystems/trust-cg.git",
            "https://github.com/%61ndrewyatesai/trust-cg.git",
            "https://github.com/%2561ndrewyatesai/trust-cg.git",
        )
        for authored in authored_urls:
            with self.subTest(authored=authored), tempfile.TemporaryDirectory() as temporary:
                fixture = self.fixture(temporary)

                def mutate(checkout: Path) -> None:
                    manifest = checkout / "Cargo.toml"
                    write(
                        manifest,
                        manifest.read_text(encoding="utf-8").replace(
                            anchor.SUBMODULES["trust-cg"][1], authored
                        ),
                    )

                fixture.advance_consumer("ay", mutate, "concealed first-party URL")
                self.assert_failure(
                    self.run_checker(fixture), "malformed or out-of-policy first-party URL"
                )

    def test_malformed_toml_and_json_with_uppercase_org_fail_closed(self) -> None:
        cases = {
            "Cargo.toml": ("not valid TOML", '[dependencies\nurl = "https://github.com/alabsystems/ay.git"\n'),
            "lake-manifest.json": (
                "not valid strict JSON",
                '{"url":"https://github.com/alabsystems/ay.git",',
            ),
        }
        for filename, (needle, content) in cases.items():
            with self.subTest(filename=filename), tempfile.TemporaryDirectory() as temporary:
                fixture = self.fixture(temporary)

                def mutate(checkout: Path) -> None:
                    write(checkout / "concealed" / filename, content)

                fixture.advance_consumer("ay", mutate, f"malformed uppercase {filename}")
                self.assert_failure(self.run_checker(fixture), needle)

    def test_patch_only_manifest_target_derives_a_direct_edge(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)

            def mutate(checkout: Path) -> None:
                manifest = checkout / "Cargo.toml"
                write(
                    manifest,
                    manifest.read_text(encoding="utf-8")
                    + '\n[patch.crates-io]\nay = { path = "../ay" }\n',
                )

            fixture.advance_consumer("trust-vc", mutate, "patch-only AY authority")
            self.assert_failure(
                self.run_checker(fixture), "independently observed committed state"
            )
            edges = fixture.refresh_observed_receipt("receipt patch-only edge")
            edge = next(
                row
                for row in edges
                if row["consumer"] == "trust-vc" and row["dependency"] == "ay"
            )
            self.assertTrue(any("cargo-patch-path" in item for item in edge["surfaces"]))
            result = self.run_checker(fixture)
            self.assertEqual(result.returncode, 0, result.stderr)

    def test_terminal_path_cycle_requires_a_finite_generation_cut(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)

            def patch_to(package: str, relative: str) -> Callable[[Path], None]:
                def mutate(checkout: Path) -> None:
                    manifest = checkout / "Cargo.toml"
                    write(
                        manifest,
                        manifest.read_text(encoding="utf-8")
                        + f'\n[patch.crates-io]\n{package} = {{ path = "{relative}" }}\n',
                    )

                return mutate

            fixture.advance_consumer(
                "trust-vc", patch_to("ay", "../ay"), "VC terminal path to AY"
            )
            fixture.advance_consumer(
                "ay", patch_to("trust-vc", "../trust-vc"), "AY terminal path to VC"
            )
            self.assert_failure(
                self.run_checker(fixture),
                "terminal-generation first-party dependency cycle has no finite exact-SHA cut",
            )

    def test_cargo_config_patch_uses_parent_of_dot_cargo_and_derives_edge(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)

            def mutate(checkout: Path) -> None:
                write(
                    checkout / ".cargo" / "config.toml",
                    '[patch.crates-io]\nay = { path = "../ay" }\n',
                )

            fixture.advance_consumer("trust-vc", mutate, "config patch AY authority")
            self.assert_failure(
                self.run_checker(fixture), "independently observed committed state"
            )
            edges = fixture.refresh_observed_receipt("receipt config patch edge")
            edge = next(
                row
                for row in edges
                if row["consumer"] == "trust-vc" and row["dependency"] == "ay"
            )
            self.assertTrue(
                any(
                    item.startswith("trust-vc:.cargo/config.toml:")
                    and "cargo-patch-path" in item
                    for item in edge["surfaces"]
                )
            )
            result = self.run_checker(fixture)
            self.assertEqual(result.returncode, 0, result.stderr)

    def test_lake_path_requirement_and_manifest_dir_derive_a_direct_edge(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)

            def mutate(checkout: Path) -> None:
                lake = checkout / "proof"
                write(
                    lake / "lakefile.toml",
                    'name = "path-proof"\nversion = "0.1.0"\n\n'
                    '[[require]]\nname = "ay"\npath = "../../ay"\n',
                )
                write(
                    lake / "lake-manifest.json",
                    json.dumps(
                        {
                            "version": "1.2.0",
                            "packages": [
                                {
                                    "type": "path",
                                    "name": "ay",
                                    "dir": "../../ay",
                                    "manifestFile": "lake-manifest.json",
                                    "inherited": False,
                                    "configFile": "lakefile.toml",
                                }
                            ],
                        }
                    )
                    + "\n",
                )

            fixture.advance_consumer("trust-vc", mutate, "Lake path AY authority")
            self.assert_failure(
                self.run_checker(fixture), "independently observed committed state"
            )
            edges = fixture.refresh_observed_receipt("receipt Lake path edge")
            edge = next(
                row
                for row in edges
                if row["consumer"] == "trust-vc" and row["dependency"] == "ay"
            )
            self.assertTrue(any("lake-path" in item for item in edge["surfaces"]))
            self.assertEqual(len(edge["surfaces"]), 2)
            result = self.run_checker(fixture)
            self.assertEqual(result.returncode, 0, result.stderr)

    def test_cargo_and_lake_file_git_locators_fail_closed(self) -> None:
        for surface in ("cargo-file", "cargo-relative", "lake-file"):
            with self.subTest(surface=surface), tempfile.TemporaryDirectory() as temporary:
                fixture = self.fixture(temporary)
                consumer = "ny" if surface == "lake-file" else "ay"

                def mutate(checkout: Path) -> None:
                    if surface == "lake-file":
                        target = (
                            checkout
                            / "crates"
                            / "ny-cert"
                            / "proofs"
                            / "lean"
                            / "lakefile.toml"
                        )
                        replacement = "file:///tmp/first-party/clean"
                        write(
                            target,
                            target.read_text(encoding="utf-8").replace(
                                anchor.SUBMODULES["clean"][1], replacement
                            ),
                        )
                    else:
                        target = checkout / "Cargo.toml"
                        replacement = (
                            "file:///tmp/first-party/trust-cg"
                            if surface == "cargo-file"
                            else "../trust-cg"
                        )
                        write(
                            target,
                            target.read_text(encoding="utf-8").replace(
                                anchor.SUBMODULES["trust-cg"][1], replacement
                            ),
                        )

                fixture.advance_consumer(consumer, mutate, surface)
                self.assert_failure(
                    self.run_checker(fixture), "unsupported local/file Git locator"
                )

    def test_unsupported_cargo_config_closure_fails_closed(self) -> None:
        configs = {
            "source-git": (
                '[source.crates-io]\nreplace-with = "ay"\n\n[source.ay]\n'
                f'git = "{anchor.SUBMODULES["ay"][1]}"\n',
                "first-party Cargo [source] redirect",
            ),
            "source-directory": (
                '[source.crates-io]\nreplace-with = "ay"\n\n[source.ay]\n'
                'directory = "../ay"\n',
                "first-party Cargo [source] directory redirect",
            ),
            "include": ('include = "../shared.toml"\n', "config include is unsupported"),
            "paths": ('paths = ["../ay"]\n', "paths overrides are unsupported"),
        }
        for mutation, (content, needle) in configs.items():
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as temporary:
                fixture = self.fixture(temporary)

                def mutate(checkout: Path) -> None:
                    write(checkout / ".cargo" / "config.toml", content)

                fixture.advance_consumer("trust-vc", mutate, mutation)
                self.assert_failure(self.run_checker(fixture), needle)

    def test_nested_first_party_gitlink_authority_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)

            def mutate(checkout: Path) -> None:
                subprocess.run(
                    [
                        "git",
                        "-C",
                        str(checkout),
                        "-c",
                        "protocol.file.allow=always",
                        "submodule",
                        "add",
                        "-q",
                        str(fixture.checkout("ay")),
                        "nested/ay",
                    ],
                    check=True,
                )
                git(
                    checkout,
                    "config",
                    "-f",
                    ".gitmodules",
                    "submodule.nested/ay.url",
                    anchor.SUBMODULES["ay"][1],
                )

            fixture.advance_consumer("trust-vc", mutate, "nested AY gitlink")
            self.assert_failure(
                self.run_checker(fixture), "unsupported nested first-party gitlink authority"
            )

    def test_cargo_path_cannot_traverse_committed_symlink(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)

            def mutate(checkout: Path) -> None:
                os.symlink("../ay", checkout / "dep")
                manifest = checkout / "Cargo.toml"
                write(
                    manifest,
                    manifest.read_text(encoding="utf-8")
                    + '\n[patch.crates-io]\nay = { path = "dep" }\n',
                )

            fixture.advance_consumer("trust-vc", mutate, "symlink-concealed AY path")
            self.assert_failure(self.run_checker(fixture), "traverses committed symlink")

    def test_authority_manifest_may_not_be_a_committed_symlink(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)

            def mutate(checkout: Path) -> None:
                manifest = checkout / "Cargo.toml"
                content = manifest.read_text(encoding="utf-8")
                manifest.unlink()
                write(checkout / "real-Cargo.toml", content)
                os.symlink("real-Cargo.toml", manifest)

            fixture.advance_consumer("trust-vc", mutate, "symlink Cargo authority")
            self.assert_failure(
                self.run_checker(fixture),
                "dependency authority must be a regular committed blob",
            )

    def test_lake_rev_inputrev_and_proof_identity_splits_fail(self) -> None:
        for mutation in ("lake-lock", "proof", "subdir"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as temporary:
                fixture = self.fixture(temporary)

                def mutate(checkout: Path) -> None:
                    if mutation == "lake-lock":
                        path = (
                            checkout
                            / "crates"
                            / "ny-cert"
                            / "proofs"
                            / "lean"
                            / "lake-manifest.json"
                        )
                        value = json.loads(path.read_text(encoding="utf-8"))
                        value["packages"][0]["inputRev"] = fixture.ancestors["clean"]
                    elif mutation == "proof":
                        path = checkout / "crates" / "ny-cert" / "proofs" / "cite-map.json"
                        value = json.loads(path.read_text(encoding="utf-8"))
                        value["corpus"]["rev"] = fixture.ancestors["clean"]
                    else:
                        path = (
                            checkout
                            / "crates"
                            / "ny-cert"
                            / "proofs"
                            / "lean"
                            / "lake-manifest.json"
                        )
                        value = json.loads(path.read_text(encoding="utf-8"))
                        value["packages"][0]["subDir"] = "wrong/subdir"
                    write(path, json.dumps(value) + "\n")

                fixture.advance_consumer("ny", mutate, f"split {mutation}")
                result = self.run_checker(fixture)
                needle = (
                    "rev/inputRev split"
                    if mutation == "lake-lock"
                    else "malformed package/URL/subDir"
                    if mutation == "subdir"
                    else "revisions split across seven surfaces"
                )
                self.assert_failure(result, needle)

    def test_all_four_additional_ny_identity_surfaces_fail_closed(self) -> None:
        cases = {
            "missing-spec": "exactly seven committed surfaces",
            "duplicate-readme": "exactly one authoritative identity row",
            "malformed-provenance": "full 40-hex",
            "split-rust": "revisions split across seven surfaces",
        }
        for mutation, needle in cases.items():
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as temporary:
                fixture = self.fixture(temporary)

                def mutate(checkout: Path) -> None:
                    base = checkout / "crates" / "ny-cert"
                    if mutation == "missing-spec":
                        (base / "SPEC.md").unlink()
                    elif mutation == "duplicate-readme":
                        path = base / "proofs" / "README.md"
                        with path.open("a", encoding="utf-8") as handle:
                            handle.write(
                                "Clean's `Crownproof` library supplies duplicates at exact commit "
                                f"`{fixture.commits['clean']}`.\n"
                            )
                    elif mutation == "malformed-provenance":
                        path = base / "proofs" / "lean" / "PROVENANCE.md"
                        write(
                            path,
                            path.read_text(encoding="utf-8").replace(
                                fixture.commits["clean"], "not-a-full-sha"
                            ),
                        )
                    else:
                        path = base / "src" / "cite_check.rs"
                        write(
                            path,
                            path.read_text(encoding="utf-8").replace(
                                fixture.commits["clean"], fixture.ancestors["clean"]
                            ),
                        )

                fixture.advance_consumer("ny", mutate, mutation)
                result = self.run_checker(fixture)
                self.assert_failure(result, needle)

    def test_alias_url_and_missing_local_object_fail_closed(self) -> None:
        for mutation in ("alias", "missing-object"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as temporary:
                fixture = self.fixture(temporary)

                def mutate(checkout: Path) -> None:
                    manifest = checkout / "Cargo.toml"
                    content = manifest.read_text(encoding="utf-8")
                    if mutation == "alias":
                        content = content.replace(
                            anchor.SUBMODULES["trust-cg"][1],
                            anchor.SUBMODULES["trust-cg"][1].removesuffix(".git"),
                        )
                    else:
                        content = content.replace(fixture.ancestors["trust-cg"], "1" * 40)
                        lock = checkout / "Cargo.lock"
                        write(
                            lock,
                            lock.read_text(encoding="utf-8").replace(
                                fixture.ancestors["trust-cg"], "1" * 40
                            ),
                        )
                    write(manifest, content)

                fixture.advance_consumer("ay", mutate, mutation)
                result = self.run_checker(fixture)
                needle = "alias" if mutation == "alias" else "cat-file"
                self.assert_failure(result, needle)

    def test_unsupported_lean_lake_first_party_url_is_not_silently_external(self) -> None:
        locators = (
            "https://github.com/alabsystems/new-repo.git",
            "https://github.com/%2561ndrewyatesai/new-repo.git",
            "../clean",
        )
        for locator in locators:
            with self.subTest(locator=locator), tempfile.TemporaryDirectory() as temporary:
                fixture = self.fixture(temporary)

                def mutate(checkout: Path) -> None:
                    write(
                        checkout / "lakefile.lean",
                        f'require unknown from git "{locator}" @ "main"\n',
                    )

                fixture.advance_consumer("ay", mutate, "unsupported Lake first-party URL")
                result = self.run_checker(fixture)
                self.assert_failure(result, "unsupported first-party Lake declaration")

    def test_generation_cut_must_be_ancestor_and_exactly_receipted(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            cg = fixture.checkout("trust-cg")
            terminal = fixture.commits["trust-cg"]
            git(cg, "switch", "--orphan", "unrelated")
            write(cg / "orphan", "unrelated\n")
            unrelated = commit_all(cg, "unrelated CG object")
            git(cg, "switch", "--detach", terminal)

            def mutate(checkout: Path) -> None:
                for relative in ("Cargo.toml", "Cargo.lock"):
                    path = checkout / relative
                    write(
                        path,
                        path.read_text(encoding="utf-8").replace(
                            fixture.ancestors["trust-cg"], unrelated
                        ),
                    )

            fixture.advance_consumer("ay", mutate, "pin unrelated CG")
            result = self.run_checker(fixture)
            self.assert_failure(result, "is not an ancestor")

        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            receipt = copy.deepcopy(fixture.receipt)
            anchors = receipt["anchors"]
            assert isinstance(anchors, list) and anchors
            anchors[0]["reason"] = "generic waiver that is deliberately long but semantically empty"
            fixture.commit_receipt(receipt)
            result = self.run_checker(fixture)
            self.assert_failure(result, "exact generation-cut policy text")

    def test_exclusion_omission_and_canonical_reachability_fail(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            receipt = copy.deepcopy(fixture.receipt)
            receipt["exclusions"] = []
            fixture.commit_receipt(receipt)
            result = self.run_checker(fixture)
            self.assert_failure(result, "independently observed committed state")

        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)

            def mutate(checkout: Path) -> None:
                manifest = checkout / "Cargo.toml"
                with manifest.open("a", encoding="utf-8") as handle:
                    handle.write('\nfixture = { path = "fixtures" }\n')

            fixture.advance_consumer("ay", mutate, "reach excluded fixture")
            result = self.run_checker(fixture)
            self.assert_failure(result, "reaches excluded")

        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)

            def mutate_workspace(checkout: Path) -> None:
                manifest = checkout / "Cargo.toml"
                content = manifest.read_text(encoding="utf-8")
                write(manifest, content.replace('exclude = ["fixtures"]\n', ""))

            fixture.advance_consumer("ay", mutate_workspace, "hide active workspace member")
            result = self.run_checker(fixture)
            self.assert_failure(result, "hides Cargo workspace members")

        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            receipt = copy.deepcopy(fixture.receipt)
            exclusions = receipt["exclusions"]
            assert isinstance(exclusions, list)
            exclusions.append(
                {
                    "repository": "ny",
                    "path": "crates/ny-cert/SPEC.md",
                    "reason": "attempt to hide one required proof identity authority surface",
                }
            )
            fixture.commit_receipt(receipt)
            result = self.run_checker(fixture)
            self.assert_failure(result, "may not be excluded")

        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            receipt = copy.deepcopy(fixture.receipt)
            exclusions = receipt["exclusions"]
            assert isinstance(exclusions, list)
            exclusions.append(
                {
                    "repository": "trust",
                    "path": "Cargo.toml",
                    "reason": "attempt to exclude the repository-root dependency authority manifest",
                }
            )
            fixture.commit_receipt(receipt)
            result = self.run_checker(fixture)
            self.assert_failure(result, "overlaps repository-root dependency authority")

    def test_hidden_gitlink_and_repository_binding_drift_fail(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            git(
                fixture.root,
                "update-index",
                "--add",
                "--cacheinfo",
                f"160000,{fixture.commits['clean']},first-party/hidden",
            )
            git(fixture.root, "commit", "-qm", "hidden gitlink")
            result = self.run_checker(fixture)
            self.assert_failure(result, "gitlinks differ")

        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            receipt = copy.deepcopy(fixture.receipt)
            repositories = receipt["repositories"]
            assert isinstance(repositories, dict) and isinstance(repositories["clean"], dict)
            repositories["clean"]["commit"] = fixture.ancestors["clean"]
            fixture.commit_receipt(receipt)
            result = self.run_checker(fixture)
            self.assert_failure(result, "does not match root gitlink")

    def test_external_receipt_refuses_staged_gitlinks_and_binds_committed_head(self) -> None:
        for dependency in ("clean", "trust-wp"):
            with self.subTest(dependency=dependency), tempfile.TemporaryDirectory() as temporary:
                fixture = self.fixture(temporary)
                checkout = fixture.checkout(dependency)
                write(checkout / "generation.txt", "new terminal generation\n")
                terminal = commit_all(checkout, f"advance {dependency} terminal")
                git(fixture.root, "add", anchor.SUBMODULES[dependency][0])

                staged = self.run_checker(fixture, "--print-receipt")
                self.assert_failure(staged, "staged index to equal committed HEAD")

                root_terminal = commit_all(fixture.root, f"bind {dependency} terminal")
                generated = self.run_checker(fixture, "--print-receipt")
                # A freshly committed WP-gitlink advance whose
                # spikes/DEPENDS.lock is unchanged and whose new commit
                # descends from the old one is an ORDINARY pin advance, judged
                # exactly like the Clean one (2026-09-12).  Only a
                # binding-changing or non-forward move is a terminal claim.
                self.assertEqual(generated.returncode, 0, generated.stderr)
                receipt = json.loads(generated.stdout)
                self.assertEqual(receipt["schema"], anchor.EXTERNAL_SCHEMA)
                self.assertEqual(receipt["self"]["commit"], root_terminal)
                self.assertEqual(receipt["repositories"][dependency]["commit"], terminal)
                self.assertNotIn("wp_trust_anchor", receipt)

    def test_external_receipt_refuses_dirty_or_untracked_worktree(self) -> None:
        for mutation in ("tracked", "untracked"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as temporary:
                fixture = self.fixture(temporary)
                if mutation == "tracked":
                    write(fixture.root / "Cargo.toml", "dirty tracked root\n")
                else:
                    write(fixture.root / "untracked-evidence", "must not be ignored\n")
                result = self.run_checker(fixture, "--print-receipt")
                self.assert_failure(result, "index and worktree to equal committed HEAD")

    def test_external_receipt_rejects_hidden_index_flags_in_root_and_submodule(self) -> None:
        for repository in ("trust", "trust-wp"):
            for flag in ("--assume-unchanged", "--skip-worktree"):
                with (
                    self.subTest(repository=repository, flag=flag),
                    tempfile.TemporaryDirectory() as temporary,
                ):
                    fixture = self.fixture(temporary)
                    checkout = (
                        fixture.root
                        if repository == "trust"
                        else fixture.checkout("trust-wp")
                    )
                    git(checkout, "update-index", flag, "Cargo.toml")
                    result = self.run_checker(fixture, "--print-receipt")
                    self.assert_failure(
                        result, "forbidden assume-unchanged/skip-worktree index flags"
                    )

    def test_external_receipt_allows_ignored_untracked_non_authority(self) -> None:
        for repository in ("trust", "trust-wp"):
            with self.subTest(repository=repository), tempfile.TemporaryDirectory() as temporary:
                fixture = self.fixture(temporary)
                checkout = (
                    fixture.root
                    if repository == "trust"
                    else fixture.checkout("trust-wp")
                )
                git_dir = Path(
                    git(
                        checkout,
                        "rev-parse",
                        "--path-format=absolute",
                        "--git-common-dir",
                    )
                )
                with (git_dir / "info" / "exclude").open(
                    "a", encoding="utf-8"
                ) as policy:
                    policy.write("/ignored-local-scratch\n")
                write(checkout / "ignored-local-scratch", "not authority\n")
                result = self.run_checker(fixture, "--print-receipt")
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(
                    json.loads(result.stdout)["schema"], anchor.EXTERNAL_SCHEMA
                )

    def test_external_receipt_default_output_remains_ignored_and_repeatable(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            write(
                fixture.root / ".gitignore",
                f"/{anchor.EXTERNAL_RECEIPT_PATH}\n",
            )
            commit_all(fixture.root, "ignore external constellation evidence")
            for _attempt in range(2):
                result = self.run_checker(fixture, "--write-receipt")
                self.assertEqual(result.returncode, 0, result.stderr)
            output = fixture.root / anchor.EXTERNAL_RECEIPT_PATH
            self.assertTrue(output.is_file())
            self.assertEqual(json.loads(output.read_text())["schema"], anchor.EXTERNAL_SCHEMA)
            self.assertEqual(git(fixture.root, "status", "--short"), "")

    def test_terminal_policy_marker_lifecycle_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            marker = fixture.root / anchor.TERMINAL_POLICY_MARKER_PATH
            marker.unlink()
            commit_all(fixture.root, "illicit terminal-policy marker deletion")
            missing = self.run_checker(fixture, "--print-receipt")
            self.assert_failure(missing, "missing required committed marker")

            write(marker, anchor.TERMINAL_POLICY_MARKER.decode("ascii"))
            commit_all(fixture.root, "illicit terminal-policy marker reintroduction")
            reintroduced = self.run_checker(fixture, "--print-receipt")
            self.assert_failure(reintroduced, "deleted on a raw DAG edge")

        for mutation in ("content", "mode"):
            with (
                self.subTest(mutation=mutation),
                tempfile.TemporaryDirectory() as temporary,
            ):
                fixture = self.fixture(temporary)
                marker = fixture.root / anchor.TERMINAL_POLICY_MARKER_PATH
                if mutation == "content":
                    write(marker, "trust.constellation.terminal-policy.v1\npolicy=off\n")
                    expected = "content differs"
                else:
                    marker.chmod(0o755)
                    expected = "mode 100644"
                commit_all(fixture.root, f"malform marker {mutation}")
                malformed = self.run_checker(fixture, "--print-receipt")
                self.assert_failure(malformed, expected)

    # ------------------------------------------------------------------
    # P4: the v3 marker, and the v2 marker as history.
    # ------------------------------------------------------------------

    def test_v3_marker_lifecycle_fails_closed(self) -> None:
        # Absent everywhere in history: refused with the fix; landing it on the
        # same tree is what turns the lane green (the real landing order).
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary, v3_marker=False)
            missing = self.run_checker(fixture, "--print-receipt")
            self.assert_failure(
                missing,
                "terminal-policy v3 marker '.trust-terminal-policy-v3' is missing at the "
                "judged revision",
            )
            self.assertIn("--rev origin/main", missing.stderr)
            self.assertIn("must merge main first", missing.stderr)
            (fixture.root / anchor.TERMINAL_POLICY_V3_MARKER_PATH).write_bytes(
                anchor.render_terminal_policy_v3_marker(fixture.wp_w0, fixture.wp_floor)
            )
            commit_all(fixture.root, "declare terminal-policy v3")
            landed = self.run_checker(fixture, "--print-receipt")
            self.assertEqual(landed.returncode, 0, landed.stderr)
            self.assertNotIn("wp_trust_anchor", json.loads(landed.stdout))

        # Forged or malformed at the judged revision: the row or the mode.
        for mutation, expected in (
            ("row", "terminal-policy v3 marker row 6 differs from canonical"),
            ("uppercase", "terminal-policy v3 marker row 1 differs from canonical"),
            ("truncated", "terminal-policy v3 marker is not newline-terminated"),
            ("mode", "v3 marker must be a non-executable regular blob (mode 100644)"),
        ):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as temporary:
                fixture = self.fixture(temporary)
                marker = fixture.root / anchor.TERMINAL_POLICY_V3_MARKER_PATH
                canonical = marker.read_bytes()
                if mutation == "row":
                    marker.write_bytes(canonical.replace(b"ruled=2026-09-21", b"ruled=2026-09-22"))
                elif mutation == "uppercase":
                    marker.write_bytes(canonical.upper())
                elif mutation == "truncated":
                    marker.write_bytes(canonical[:-1])
                else:
                    marker.chmod(0o755)
                commit_all(fixture.root, f"malform v3 marker {mutation}")
                self.assert_failure(self.run_checker(fixture, "--print-receipt"), expected)

        # Deleted on a raw DAG edge, and re-adding it does not launder that.
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            marker = fixture.root / anchor.TERMINAL_POLICY_V3_MARKER_PATH
            canonical = marker.read_bytes()
            marker.unlink()
            commit_all(fixture.root, "illicit v3 marker deletion")
            self.assert_failure(
                self.run_checker(fixture, "--print-receipt"),
                "terminal-policy v3 marker '.trust-terminal-policy-v3' is missing",
            )
            marker.write_bytes(canonical)
            commit_all(fixture.root, "illicit v3 marker reintroduction")
            self.assert_failure(
                self.run_checker(fixture, "--print-receipt"),
                "v3 marker was deleted on a raw DAG edge",
            )

        # Edited in an ancestor and restored later: still refused.
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            marker = fixture.root / anchor.TERMINAL_POLICY_V3_MARKER_PATH
            canonical = marker.read_bytes()
            marker.write_bytes(canonical.replace(b"cohort-forward", b"cohort-backward"))
            commit_all(fixture.root, "edit the v3 marker")
            marker.write_bytes(canonical)
            commit_all(fixture.root, "restore the v3 marker")
            self.assert_failure(
                self.run_checker(fixture, "--print-receipt"),
                "v3 raw DAG contains a forged or edited marker",
            )

    def test_armed_or_edited_v2_marker_is_refused_outright(self) -> None:
        def armed_bytes(fixture: Fixture) -> bytes:
            return (
                b"trust.constellation.terminal-policy.v2\nstate=armed\n"
                b"policy=trust-wp-root-cycle-forward\n"
                + f"w0={fixture.wp_w0}\npreservation-floor={fixture.wp_floor}\n"
                f"predecessor={fixture.wp_floor}\n".encode("ascii")
                + b"".join(
                    f"root.{name}={sha}\n".encode("ascii")
                    for name, sha in sorted(fixture.commits.items())
                )
            )

        # The fixture carries the historical pre-v2 bytes from its first commit,
        # as real main does since 80a5ca7f00f; that is the one green shape.
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            self.assertEqual(
                (fixture.root / anchor.TERMINAL_POLICY_V2_MARKER_PATH).read_bytes(),
                anchor.TERMINAL_POLICY_V2_PRE_MARKER,
            )
            carried = self.run_checker(fixture, "--print-receipt")
            self.assertEqual(carried.returncode, 0, carried.stderr)

        for mutation in (
            "armed", "armed-in-ancestor", "edited", "executable", "deleted", "deleted-then-readded",
        ):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as temporary:
                fixture = self.fixture(temporary)
                marker = fixture.root / anchor.TERMINAL_POLICY_V2_MARKER_PATH
                if mutation in {"armed", "armed-in-ancestor"}:
                    marker.write_bytes(armed_bytes(fixture))
                elif mutation == "edited":
                    marker.write_bytes(
                        anchor.TERMINAL_POLICY_V2_PRE_MARKER.replace(
                            b"e7c353690e1b58a4e830edc9facb0e4396164585", b"0" * 40
                        )
                    )
                elif mutation == "executable":
                    marker.chmod(0o755)
                else:
                    marker.unlink()
                commit_all(fixture.root, f"v2 marker {mutation}")
                if mutation == "armed-in-ancestor":
                    marker.write_bytes(anchor.TERMINAL_POLICY_V2_PRE_MARKER)
                    commit_all(fixture.root, "downgrade the armed v2 marker again")
                if mutation == "deleted-then-readded":
                    marker.write_bytes(anchor.TERMINAL_POLICY_V2_PRE_MARKER)
                    commit_all(fixture.root, "re-add the v2 marker")
                result = self.run_checker(fixture, "--print-receipt")
                if mutation in {"armed", "armed-in-ancestor"}:
                    self.assert_failure(result, "v2 marker at")
                    self.assertIn("is ARMED", result.stderr)
                    self.assertIn("refused outright (P4", result.stderr)
                elif mutation in {"deleted", "deleted-then-readded"}:
                    self.assert_failure(result, "v2 marker was deleted on a raw DAG edge")
                    self.assertIn("(P4)", result.stderr)
                else:
                    self.assert_failure(result, "is not the historical pre-v2 bytes")

        # The verifier's probe g4: a root commit whose ONLY change deletes the
        # v2 marker after a pre-v2 one, judged directly.
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            assert fixture.policy_activation is not None
            deleted = root_child(
                fixture.root, fixture.policy_activation, "delete the v2 marker",
                {anchor.TERMINAL_POLICY_V2_MARKER_PATH: None},
            )
            self.assert_policy_refuses(
                fixture, deleted, fixture.commits,
                f"v2 marker was deleted on a raw DAG edge: child={deleted}, "
                f"marked_parents=['{fixture.policy_activation}']",
            )
            readded = root_child(
                fixture.root, deleted, "re-add the v2 marker",
                {anchor.TERMINAL_POLICY_V2_MARKER_PATH: (
                    "100644", write_blob(fixture.root, anchor.TERMINAL_POLICY_V2_PRE_MARKER))},
            )
            self.assert_policy_refuses(
                fixture, readded, fixture.commits, "v2 marker was deleted on a raw DAG edge"
            )

    # ------------------------------------------------------------------
    # P1: the preservation floor against the live sample.
    # ------------------------------------------------------------------

    def test_p1_preservation_floor_is_judged_against_the_live_sample(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            head = git(fixture.root, "rev-parse", "HEAD")
            wp = fixture.checkout("trust-wp")
            commits = dict(fixture.commits)

            # B itself, and a main that advanced past B: both contain B.
            self.policy(fixture, head, commits, remote=fixture.wp_floor)
            later = wp_child(wp, fixture.wp_floor, "main advances past B")
            verdict = self.policy(fixture, head, commits, remote=later)
            self.assertEqual(verdict["wp_remote_main"], later)

            # A main that does not contain B: rewritten published history.
            self.assert_policy_refuses(
                fixture, head, commits,
                "does not contain the preservation floor B", remote=fixture.wp_w0,
            )
            orphan = commit_tree(
                wp, git(wp, "rev-parse", f"{fixture.wp_w0}^{{tree}}"), [], "foreign main"
            )
            self.assert_policy_refuses(
                fixture, head, commits,
                "does not contain the preservation floor B", remote=orphan,
            )

            # A main whose object is absent locally AND that the remote will
            # not serve: the by-sha fetch is tried, then refuse and name the fetch.
            message = self.assert_policy_refuses(
                fixture, head, commits,
                "is not present in the bound first-party/trust-wp object store",
                remote="f" * 40,
            )
            self.assertIn("git -C first-party/trust-wp fetch origin main", message)
            self.assertIn("a by-sha fetch from", message)
            self.assertIn("ffffffffffff", message)

            # The same through the CLI, and the sample is taken once per judged
            # revision -- this is where the lane touches the network.
            self.assert_failure(
                self.run_checker(fixture, wp_remote_main=fixture.wp_w0),
                "does not contain the preservation floor B",
            )
            stdout, stderr = io.StringIO(), io.StringIO()
            with synthetic_v3_policy(fixture), mock.patch.object(
                anchor, "sample_trust_wp_remote_main", return_value=fixture.wp_floor
            ) as sample:
                with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
                    code = anchor.main(["--repo-root", str(fixture.root)])
            self.assertEqual(code, 0, stderr.getvalue())
            sample.assert_called_once_with()
            self.assertIn(
                f"trust-wp terminal-policy v3: remote main {fixture.wp_floor[:12]} contains B (P1)",
                stdout.getvalue(),
            )

    # ------------------------------------------------------------------
    # P2: single-parent moves.
    # ------------------------------------------------------------------

    def test_p2_forward_moves_are_admissible_whatever_the_lock_did(self) -> None:
        """Clause (a): Y contains X.  The lock is P3's question, not P2's.

        Two successive same-lock forward moves, one sharing its commit with a
        lockfile (the 2026-09-12 shape); a forward move that REWRITES the lock
        (admissible under P2, and coherent under P3 because its rows still
        point behind the pins); and forward moves whose target has no regular
        lock at all, which P2 admits and P3 then refuses.
        """
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            assert fixture.policy_activation is not None
            root = fixture.root
            wp = fixture.checkout("trust-wp")
            w0 = fixture.commits["trust-wp"]
            lock_oid = git(wp, "rev-parse", f"{w0}:{anchor.WP_DEPENDS_PATH}")
            retired = retire_receipt(root, fixture.policy_activation)
            commits = dict(fixture.commits)

            w1 = wp_child(wp, w0, "ordinary forward TrustWP generation",
                          {"forward-one.txt": ("100644", write_blob(wp, b"ordinary work\n"))})
            w2 = wp_child(wp, w1, "second ordinary forward TrustWP generation",
                          {"forward-two.txt": ("100644", write_blob(wp, b"more work\n"))})
            for candidate in (w1, w2):
                self.assertEqual(git(wp, "rev-parse", f"{candidate}:{anchor.WP_DEPENDS_PATH}"), lock_oid)
            first = pin_wp(root, retired, w1, "forward move W0 -> W1")
            second = pin_wp(
                root, first, w2, "forward move W1 -> W2 sharing its commit with a lock",
                {"Cargo.lock": ("100644", write_blob(root, b"version = 4\n"))},
            )
            commits["trust-wp"] = w1
            self.assertEqual(self.policy(fixture, first, commits)["moves"], 1)
            commits["trust-wp"] = w2
            self.assertEqual(self.policy(fixture, second, commits)["moves"], 2)
            explicit = self.run_checker(fixture, "--rev", second, "--derive-when-receipt-absent")
            self.assertEqual(explicit.returncode, 0, explicit.stderr)
            self.assertIn("2 gitlink move(s) since v1 activation admissible (P2)", explicit.stdout)

            # A forward move whose lock is rewritten: rows re-bound to the
            # activation commit and the current sibling pins -- still behind
            # or at every gitlink, so P3 holds too.
            rebound = wp_depends_lock(
                {**fixture.lock_rows(), "trust": fixture.policy_activation,
                 "clean": fixture.commits["clean"], "trust-cg": fixture.commits["trust-cg"]}
            ).encode("ascii")
            relocked = wp_child(wp, w2, "forward move that refreshes the lock",
                                {anchor.WP_DEPENDS_PATH: ("100644", write_blob(wp, rebound))})
            self.assertNotEqual(git(wp, "rev-parse", f"{relocked}:{anchor.WP_DEPENDS_PATH}"), lock_oid)
            third = pin_wp(root, second, relocked, "forward move with a changed lock")
            commits["trust-wp"] = relocked
            self.assertEqual(self.policy(fixture, third, commits)["moves"], 3)
            refreshed = self.run_checker(fixture, "--rev", third, "--derive-when-receipt-absent")
            self.assertEqual(refreshed.returncode, 0, refreshed.stderr)

            # No regular lock at the target: P2 admits the forward move, P3
            # refuses the pin.
            for mutation, entry, needle in (
                ("deleted", None, "at the pinned TrustWP commit"),
                ("symlinked", ("120000", write_blob(wp, b"missing-DEPENDS.lock")),
                 "must be a regular committed blob"),
            ):
                with self.subTest(mutation=mutation):
                    target = wp_child(wp, w2, f"lock {mutation}", {anchor.WP_DEPENDS_PATH: entry})
                    tip = pin_wp(root, second, target, f"forward move to a {mutation}-lock target")
                    commits["trust-wp"] = target
                    self.assertEqual(self.policy(fixture, tip, commits)["moves"], 3)
                    result = self.run_checker(fixture, "--rev", tip, "--derive-when-receipt-absent")
                    self.assert_failure(result, needle)
                    self.assertIn("spikes/DEPENDS.lock", result.stderr)

        # The harness's exact invocation on one real commit that moves the
        # gitlink TOGETHER with a lockfile, and the receipt it prints.
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            root = fixture.root
            wp = fixture.checkout("trust-wp")
            w0 = fixture.commits["trust-wp"]
            (root / anchor.RECEIPT_PATH).unlink()
            write(root / "Cargo.lock", "version = 4\n")
            base = commit_all(root, "retire the tracked receipt; track the root lock")
            write(wp / "forward.txt", "ordinary TrustWP work that leaves the cycle binding alone\n")
            w1 = commit_all(wp, "ordinary forward TrustWP generation")
            self.assertEqual(git(wp, "show", "-s", "--format=%P", w1), w0)
            write(root / "Cargo.lock", 'version = 4\n\n[[package]]\nname = "trust-wp"\nversion = "0.2.0"\n')
            git(root, "add", anchor.WP_ROOT_DELTA_PATH, "Cargo.lock")
            git(root, "commit", "-qm", "pins: trust-wp forward; its lock rows follow in the same commit")
            move = git(root, "rev-parse", "HEAD")
            fixture.commits["trust-wp"] = w1
            self.assertEqual(self.policy(fixture, move, fixture.commits)["moves"], 1)

            environment = os.environ.copy()
            environment[anchor.PUSH_REFS_ENV] = f"refs/heads/main {move} refs/heads/main {base}"
            lane = self.run_checker(fixture, "--push-context", "--derive-when-receipt-absent", env=environment)
            self.assertEqual(lane.returncode, 0, lane.stderr)
            self.assertIn("DEPENDENCY CONSTELLATION OK", lane.stdout)
            self.assertIn("no committed receipt", lane.stdout)
            self.assertIn("marker exact (P4)", lane.stdout)
            generated = self.run_checker(fixture, "--print-receipt")
            self.assertEqual(generated.returncode, 0, generated.stderr)
            receipt = json.loads(generated.stdout)
            self.assertNotIn("wp_trust_anchor", receipt)
            self.assertEqual(receipt["repositories"]["trust-wp"]["commit"], w1)

    def test_p2_non_forward_moves_need_a_canonical_target_or_a_recovery(self) -> None:
        """Clauses (b) and (c), and the refusal that names X, Y and each clause.

        From a pin on an off-main line: a backward move without restoration, a
        sideways move whose lock differs, a divergent same-lock target, an
        unrelated parentless target, and a target without a regular lock are
        each refused with X, Y and the clause verdicts.  The ``8325008ba62``
        shape -- sideways onto canonical main with the lock byte-identical --
        is admissible, and so is a same-lock move back onto the canonical
        line (W0 is an ancestor of main): backward moves are
        ``fast.pin-regression``'s business, not this gate's.
        """
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            assert fixture.policy_activation is not None
            root = fixture.root
            wp = fixture.checkout("trust-wp")
            w0 = fixture.commits["trust-wp"]
            lock_oid = git(wp, "rev-parse", f"{w0}:{anchor.WP_DEPENDS_PATH}")
            lock_bytes = committed_bytes(wp, w0, anchor.WP_DEPENDS_PATH)
            retired = retire_receipt(root, fixture.policy_activation)
            commits = dict(fixture.commits)

            side_one = wp_child(wp, w0, "off-main line one")
            side_two = wp_child(wp, side_one, "off-main line two")
            relocked = wp_child(
                wp, w0, "lock blob differs (same rows)",
                {anchor.WP_DEPENDS_PATH: ("100644", write_blob(wp, b"# refreshed\n" + lock_bytes))},
            )
            relocked_oid = git(wp, "rev-parse", f"{relocked}:{anchor.WP_DEPENDS_PATH}")
            sibling = wp_child(wp, w0, "sibling off main")
            unrelated = commit_tree(wp, git(wp, "rev-parse", f"{w0}^{{tree}}"), [], "unrelated history")
            no_lock = wp_child(wp, w0, "no regular lock", {anchor.WP_DEPENDS_PATH: None})
            self.assertFalse(is_ancestor(wp, side_two, fixture.wp_floor))

            base = pin_wp(root, retired, side_two, "forward move W0 -> side_two")
            commits["trust-wp"] = side_two
            self.assertEqual(self.policy(fixture, base, commits)["moves"], 1)

            refusals = (
                ("backward, no restoration", side_one, (
                    "(a) not forward: X is not a raw ancestor of Y",
                    "(b) not a canonical re-anchoring: Y is not an ancestor-or-equal of "
                    f"trust-wp remote main {fixture.wp_floor}",
                    "(c) not a recovered same-lock backward move: no immediate single-parent child of",
                )),
                ("sideways, differing lock", relocked, (
                    f"(b) not a canonical re-anchoring: spikes/DEPENDS.lock differs (X={lock_oid}, Y={relocked_oid})",
                    "(c) not a recovered same-lock backward move: spikes/DEPENDS.lock differs",
                )),
                ("divergent, same lock", sibling, (
                    "(b) not a canonical re-anchoring: Y is not an ancestor-or-equal",
                    "(c) not a recovered same-lock backward move: Y is not a strict raw ancestor of X",
                )),
                ("unrelated parentless", unrelated, (
                    "(a) not forward",
                    "(c) not a recovered same-lock backward move: Y is not a strict raw ancestor of X",
                )),
                ("no regular lock at the target", no_lock, (
                    f"spikes/DEPENDS.lock differs (X={lock_oid}, Y=absent-or-non-regular)",
                )),
            )
            for label, target, needles in refusals:
                with self.subTest(label=label):
                    tip = pin_wp(root, base, target, f"{label} move")
                    commits["trust-wp"] = target
                    message = self.assert_policy_refuses(
                        fixture, tip, commits,
                        f"refuses the first-party/trust-wp gitlink move at {tip}: X={side_two} -> Y={target}",
                    )
                    for needle in needles:
                        self.assertIn(needle, message)
                    self.assertTrue(message.endswith("(P2)"), message)
                    result = self.run_checker(fixture, "--rev", tip, "--derive-when-receipt-absent")
                    self.assert_failure(result, f"X={side_two} -> Y={target}")

            # (b): the 8325008ba62 shape.
            reanchored = pin_wp(root, base, fixture.wp_floor, "re-anchor onto canonical main")
            commits["trust-wp"] = fixture.wp_floor
            verdict = self.policy(fixture, reanchored, commits)
            self.assertEqual((verdict["moves"], verdict["recovered"]), (2, 0))
            result = self.run_checker(fixture, "--rev", reanchored, "--derive-when-receipt-absent")
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("2 gitlink move(s) since v1 activation admissible (P2)", result.stdout)

            # (b) again: back onto the canonical line, same lock -- admissible
            # here, disclosed by fast.pin-regression.
            back_on_main = pin_wp(root, base, w0, "back to W0, which main contains")
            commits["trust-wp"] = w0
            verdict = self.policy(fixture, back_on_main, commits)
            self.assertEqual((verdict["moves"], verdict["recovered"]), (2, 0))

            # (b) is stated against the LIVE sample: with a main that has
            # moved on, the same target stays admissible as long as it is
            # still on that line.
            later = wp_child(wp, fixture.wp_floor, "main advances again")
            commits["trust-wp"] = fixture.wp_floor
            self.policy(fixture, reanchored, commits, remote=later)

    def same_lock_recovery_fixture(self, temporary: str) -> tuple[Fixture, dict[str, str]]:
        """W0 -> w1 -> w2 -> w3 on an OFF-main line, so a rollback is not (b)."""
        fixture = self.fixture(temporary)
        assert fixture.policy_activation is not None
        root = fixture.root
        wp = fixture.checkout("trust-wp")
        w0 = fixture.commits["trust-wp"]
        w1 = wp_child(wp, w0, "off-main advance one")
        w2 = wp_child(wp, w1, "off-main advance two")
        w3 = wp_child(wp, w2, "off-main advance three")
        retired = retire_receipt(root, fixture.policy_activation)
        good = pin_wp(root, retired, w3, "bind the off-main advance")
        bad = pin_wp(root, good, w1, "accidentally roll WP back")
        restored = commit_tree(
            root, git(root, "rev-parse", f"{good}^{{tree}}"), [bad], "restore the exact prior WP pin"
        )
        return fixture, dict(w0=w0, w1=w1, w2=w2, w3=w3, good=good, bad=bad, restored=restored)

    def test_p2_same_lock_backward_recovery(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture, n = self.same_lock_recovery_fixture(temporary)
            root = fixture.root
            wp = fixture.checkout("trust-wp")

            def judge(revision: str, pin: str) -> tuple[dict[str, object], list[dict[str, object]]]:
                return self.policy_with_diagnostic(
                    fixture, revision, {**fixture.commits, "trust-wp": pin}
                )

            verdict, reports = judge(n["good"], n["w3"])
            self.assertEqual((verdict["moves"], verdict["recovered"], reports), (1, 0, []))
            self.assert_policy_refuses(
                fixture, n["bad"], {**fixture.commits, "trust-wp": n["w1"]},
                "(c) not a recovered same-lock backward move: no immediate single-parent child of",
            )
            # The restoration is itself a (forward) move: W0 -> w3, w3 -> w1, w1 -> w3.
            verdict, reports = judge(n["restored"], n["w3"])
            self.assertEqual((verdict["moves"], verdict["recovered"]), (3, 1))
            self.assertEqual(reports, [{
                "root_commit": n["restored"],
                "recovered_edges": [{
                    "backward_root_commit": n["bad"],
                    "before_wp": n["w3"], "after_wp": n["w1"],
                    "restoration_root_commits": [n["restored"]],
                    "regular_identical_depends_lock": True,
                }],
            }])
            self.assertNotIn("terminal_claim_remaining", json.dumps(reports))

            # Full CLI judgement changes only at the repaired revision.
            bad = self.run_checker(fixture, "--rev", n["bad"], "--derive-when-receipt-absent")
            self.assert_failure(bad, "(P2)")
            repaired = self.run_checker(fixture, "--rev", n["restored"], "--derive-when-receipt-absent")
            self.assertEqual(repaired.returncode, 0, repaired.stderr)
            self.assertIn("1 by same-lock recovery (P2)", repaired.stdout)
            git(wp, "checkout", "-q", "--detach", n["w3"])
            git(root, "checkout", "-q", "--detach", n["restored"])
            receipt = self.run_checker(fixture, "--rev", n["restored"], "--print-receipt")
            self.assertEqual(receipt.returncode, 0, receipt.stderr)
            self.assertNotIn("wp_trust_anchor", json.loads(receipt.stdout))

            # Two independently authored immediate repairs may both be in the
            # literal DAG.  Their ordinary merge retains both witnesses.
            second = commit_tree(root, git(root, "rev-parse", f'{n["good"]}^{{tree}}'),
                                 [n["bad"]], "independent exact restoration")
            merged = commit_tree(root, git(root, "rev-parse", f'{second}^{{tree}}'),
                                 [n["restored"], second], "merge exact restorations")
            verdict, reports = judge(merged, n["w3"])
            self.assertEqual(verdict["recovered"], 1)
            self.assertEqual(reports[0]["recovered_edges"][0]["restoration_root_commits"],
                             sorted([n["restored"], second]))
            w4 = wp_child(wp, n["w3"], "later ordinary WP advance")
            advanced = pin_wp(root, merged, w4, "ordinary forward work after both restorations")
            self.assertEqual(judge(advanced, w4)[0]["recovered"], 1)

            # A later forward move that CHANGES the lock is admissible after
            # the recovery: the recovered edge is judged where it occurred,
            # not against whatever the binding later became.
            refreshed = wp_child(
                wp, w4, "refresh the lock after the recovery",
                {anchor.WP_DEPENDS_PATH: ("100644", write_blob(
                    wp, b"# refreshed\n" + committed_bytes(wp, w4, anchor.WP_DEPENDS_PATH)))},
            )
            judged = pin_wp(root, advanced, refreshed, "forward lock refresh")
            verdict, _reports = judge(judged, refreshed)
            # ... plus the second restoration, w3 -> w4 and w4 -> refreshed.
            self.assertEqual((verdict["moves"], verdict["recovered"]), (6, 1))

    def test_p2_recovery_requires_the_exact_immediate_root_edge(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture, n = self.same_lock_recovery_fixture(temporary)
            root = fixture.root

            def node(parents: list[str], pin: str, label: str) -> str:
                return pin_wp(root, parents[0], pin, label) if len(parents) == 1 else root_child(
                    root, parents[0], label, {anchor.WP_ROOT_DELTA_PATH: ("160000", pin)}, parents
                )

            unchanged = node([n["bad"]], n["w1"], "postpone restoring WP")
            delayed = node([unchanged], n["w3"], "delayed exact restoration")
            partial = node([n["bad"]], n["w2"], "restore only part of the rollback")
            partial_then_exact = node([partial], n["w3"], "finish partial restoration")
            fake_side = node([n["good"]], n["w3"], "unrelated side says restored")
            merge_only = node([n["bad"], fake_side], n["w3"], "merge-only restoration")
            repeated = node([n["restored"]], n["w1"], "repeat the same rollback pair")
            delayed_again = node([repeated], n["w1"], "leave second rollback uncorrected")
            second_delayed = node([delayed_again], n["w3"], "delayed second restoration")
            for label, revision, pin in (
                ("no restoration", n["bad"], n["w1"]),
                ("unreachable exact side restoration", unchanged, n["w1"]),
                ("delayed restoration", delayed, n["w3"]),
                ("partial restoration", partial, n["w2"]),
                ("partial then exact", partial_then_exact, n["w3"]),
                ("fake/merge restoration", merge_only, n["w3"]),
                ("subsequent rollback", repeated, n["w1"]),
                ("same pair must not clear later edge", second_delayed, n["w3"]),
            ):
                with self.subTest(label=label):
                    self.assert_policy_refuses(
                        fixture, revision, {**fixture.commits, "trust-wp": pin},
                        "(c) not a recovered same-lock backward move: no immediate single-parent child of",
                    )
            # Recovery does not make a merge that drops a marked binding legal.
            dropped = node([n["restored"], n["bad"]], n["w1"], "drop restored binding")
            self.assert_policy_refuses(
                fixture, dropped, {**fixture.commits, "trust-wp": n["w1"]}, "did not retain"
            )

    def test_p2_recovery_preserves_lock_ancestry_and_marker_refusals(self) -> None:
        """Only a same-lock, strictly backward edge can be recovered.

        Each source is reached by a forward move first (so the setup itself
        is admissible); the bad edge is then refused on its clause, and an
        "exact restoration" commit does not recover it -- for the divergent
        and unrelated targets the restoration is itself a non-forward move,
        which v3 judges too.
        """
        with tempfile.TemporaryDirectory() as temporary:
            fixture, n = self.same_lock_recovery_fixture(temporary)
            assert fixture.policy_activation is not None
            root = fixture.root
            wp = fixture.checkout("trust-wp")
            retired = retire_receipt(root, fixture.policy_activation)
            sibling = wp_child(wp, n["w0"], "divergent WP sibling")
            unrelated = commit_tree(wp, git(wp, "rev-parse", f'{n["w0"]}^{{tree}}'), [], "unrelated WP source")
            changed = wp_child(wp, n["w0"], "changed-lock WP predecessor",
                               {anchor.WP_DEPENDS_PATH: ("100644", write_blob(wp, b"changed lock\n"))})
            missing = wp_child(wp, n["w0"], "WP predecessor without lock", {anchor.WP_DEPENDS_PATH: None})
            nonregular = wp_child(wp, n["w0"], "WP predecessor with symlink lock",
                                  {anchor.WP_DEPENDS_PATH: ("120000", write_blob(wp, b"elsewhere"))})
            for label, source_root, before, after, clause in (
                ("divergent", n["good"], n["w3"], sibling, "Y is not a strict raw ancestor of X"),
                ("unrelated", n["good"], n["w3"], unrelated, "Y is not a strict raw ancestor of X"),
                # W0 is on the canonical line, so only the lock keeps these out of (b).
                ("changed lock", retired, changed, n["w0"], "spikes/DEPENDS.lock differs"),
                ("missing lock", retired, missing, n["w0"], "spikes/DEPENDS.lock differs"),
                ("nonregular lock", retired, nonregular, n["w0"], "spikes/DEPENDS.lock differs"),
            ):
                with self.subTest(label=label):
                    parent = pin_wp(root, source_root, before, label + " source")
                    self.policy(fixture, parent, {**fixture.commits, "trust-wp": before})
                    bad = pin_wp(root, parent, after, label + " move")
                    message = self.assert_policy_refuses(
                        fixture, bad, {**fixture.commits, "trust-wp": after},
                        f"X={before} -> Y={after}",
                    )
                    self.assertIn(clause, message)
                    restored = commit_tree(root, git(root, "rev-parse", f"{parent}^{{tree}}"),
                                           [bad], label + " exact restoration")
                    self.assert_policy_refuses(
                        fixture, restored, {**fixture.commits, "trust-wp": before}, "(P2)"
                    )

            for marker, expected in ((None, "marker was deleted"),
                                     (("100644", write_blob(root, b"forged recovery\n")),
                                      "malformed marker state")):
                with self.subTest(marker=marker):
                    invalid = commit_tree(root, derived_tree(root, n["restored"], {
                        anchor.TERMINAL_POLICY_MARKER_PATH: marker}), [n["bad"]], "bad restoration marker")
                    hidden = commit_tree(root, git(root, "rev-parse", f'{n["restored"]}^{{tree}}'),
                                         [invalid], "restore marker after invalid recovery")
                    self.assert_policy_refuses(
                        fixture, hidden, {**fixture.commits, "trust-wp": n["w3"]}, expected
                    )

    # ------------------------------------------------------------------
    # P2: merges, and the marked subgraph.
    # ------------------------------------------------------------------

    def test_p2_accepts_straddling_merge_after_an_admissible_move(self) -> None:
        """A branch forked before an admissible move, merged with main after it.

        Main advances the TrustWP pin (lock byte-identical) in a commit shared
        with a lockfile.  A marked branch forked before that move still binds
        W0.  Merging in EITHER direction yields a marked merge whose marked
        parents bind W0 and W1 and which adopts W1: main's binding is retained
        and the branch's is (a)-admissible away from it.  That is the shape
        every merge-based push after such a move takes on a merge-heavy main,
        and the harness row prints DEPENDENCY CONSTELLATION OK on the merge
        itself.
        """
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            root = fixture.root
            wp = fixture.checkout("trust-wp")
            w0 = fixture.commits["trust-wp"]
            (root / anchor.RECEIPT_PATH).unlink()
            write(root / "Cargo.lock", "version = 4\n")
            base = commit_all(root, "retire the tracked receipt; track the root lock")
            write(wp / "forward.txt", "ordinary TrustWP work that leaves the cycle binding alone\n")
            w1 = commit_all(wp, "ordinary forward TrustWP generation")
            write(root / "Cargo.lock", 'version = 4\n\n[[package]]\nname = "trust-wp"\nversion = "0.2.0"\n')
            git(root, "add", anchor.WP_ROOT_DELTA_PATH, "Cargo.lock")
            git(root, "commit", "-qm", "pins: trust-wp forward with its lock rows")
            main_move = git(root, "rev-parse", "HEAD")

            topic_blob = write_blob(root, b"topic work\n")
            branch = root_child(root, base, "marked topic branch forked before the move",
                                {"topic.txt": ("100644", topic_blob)})
            self.assertEqual(git(root, "rev-parse", f"{branch}:{anchor.WP_ROOT_DELTA_PATH}"), w0)
            merged_tree = derived_tree(root, main_move, {"topic.txt": ("100644", topic_blob)})
            fixture.commits["trust-wp"] = w1
            for direction, parents in (
                ("branch into main", [main_move, branch]),
                ("main into branch", [branch, main_move]),
            ):
                with self.subTest(direction=direction):
                    merge = commit_tree(root, merged_tree, parents, f"merge {direction} after the move")
                    self.assertEqual(git(root, "rev-parse", f"{merge}:{anchor.WP_ROOT_DELTA_PATH}"), w1)
                    self.assertEqual(self.policy(fixture, merge, fixture.commits)["moves"], 1)
                    environment = os.environ.copy()
                    environment[anchor.PUSH_REFS_ENV] = f"refs/heads/main {merge} refs/heads/main {main_move}"
                    lane = self.run_checker(fixture, "--push-context", "--derive-when-receipt-absent", env=environment)
                    self.assertEqual(lane.returncode, 0, lane.stderr)
                    self.assertIn("DEPENDENCY CONSTELLATION OK", lane.stdout)

    def test_p2_merge_may_adopt_an_admissible_binding_and_nothing_else(self) -> None:
        """A marked merge may retain, or (a)/(b)-advance, a binding.

        After main's move W0 -> w1 (off main): a merge that adopts w1 over a
        branch that had moved to x1 (another off-main line) drops x1's
        binding; a merge that resolves to w2, a descendant no marked parent
        carried, mints; and a merge that keeps w1 while its other parent
        refreshed the lock discards that refresh.  Each is refused.  A merge
        that adopts canonical B over a parent carrying off-main w1 is the
        ``8325008ba62`` shape merged with an older branch, and is retained.
        """
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            assert fixture.policy_activation is not None
            root = fixture.root
            wp = fixture.checkout("trust-wp")
            activation = fixture.policy_activation
            w0 = fixture.commits["trust-wp"]
            w1 = wp_child(wp, w0, "main's off-main advance")
            w2 = wp_child(wp, w1, "a further off-main advance")
            x1 = wp_child(wp, w0, "a branch's own off-main advance")
            refreshed = wp_child(wp, w0, "lock refresh on a side line",
                                 {anchor.WP_DEPENDS_PATH: ("100644", write_blob(
                                     wp, b"# refreshed\n" + committed_bytes(wp, w0, anchor.WP_DEPENDS_PATH)))})
            main_move = pin_wp(root, activation, w1, "main moves W0 -> w1")
            stale = root_child(root, activation, "marked branch still binding W0")
            diverged = pin_wp(root, activation, x1, "marked branch moves W0 -> x1")
            refreshing = pin_wp(root, activation, refreshed, "marked branch refreshes the lock")
            commits = dict(fixture.commits)
            for revision, pin in ((main_move, w1), (diverged, x1), (refreshing, refreshed)):
                commits["trust-wp"] = pin
                self.assertEqual(self.policy(fixture, revision, commits)["moves"], 1)

            for shape, other, binding, needle in (
                ("drops the branch's off-main binding", diverged, w1,
                 "did not retain every marked-parent TrustWP binding"),
                ("mints a binding no marked parent published", stale, w2,
                 "no marked parent published child_wp"),
                ("discards a side line's lock refresh", refreshing, w1,
                 "did not retain every marked-parent TrustWP binding"),
            ):
                with self.subTest(shape=shape):
                    merge = root_child(root, main_move, f"merge that {shape}",
                                       {anchor.WP_ROOT_DELTA_PATH: ("160000", binding)},
                                       [main_move, other])
                    commits["trust-wp"] = binding
                    self.assert_policy_refuses(fixture, merge, commits, needle)

            # Retained through (b): the merge adopts canonical B while the
            # other marked parent carries off-main w1 with the same lock.
            reanchor = pin_wp(root, activation, fixture.wp_floor, "re-anchor onto canonical main")
            merge = root_child(root, reanchor, "merge an older branch after the re-anchoring",
                               {anchor.WP_ROOT_DELTA_PATH: ("160000", fixture.wp_floor)},
                               [reanchor, main_move])
            commits["trust-wp"] = fixture.wp_floor
            self.assertEqual(self.policy(fixture, merge, commits)["moves"], 2)

    def test_p2_admitted_merge_mint_is_the_exact_pair_judged_for_retention(self) -> None:
        """TRUSTWP-MERGE-MINT-ADMITTED admits one exact (merge, binding) pair.

        A merge binding w2, which neither marked parent carried, mints and is
        refused.  Admitted with w2, it is judged as an adoption of w2 instead:
        w2 contains both parents' bindings (W0 and w1), so it is retained and
        accepted.  The admission reaches nothing else: the same merge admitted
        with another binding still mints, another merge minting the admitted
        binding still mints, and an admitted merge whose binding does not
        contain a parent's off-main binding x1 is refused for retention.
        """
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            assert fixture.policy_activation is not None
            root = fixture.root
            wp = fixture.checkout("trust-wp")
            activation = fixture.policy_activation
            w0 = fixture.commits["trust-wp"]
            w1 = wp_child(wp, w0, "main's off-main advance")
            w2 = wp_child(wp, w1, "a further off-main advance")
            x1 = wp_child(wp, w0, "a branch's own off-main advance")
            main_move = pin_wp(root, activation, w1, "main moves W0 -> w1")
            stale = root_child(root, activation, "marked branch still binding W0")
            diverged = pin_wp(root, activation, x1, "marked branch moves W0 -> x1")
            minted = root_child(root, main_move, "merge that mints w2",
                                {anchor.WP_ROOT_DELTA_PATH: ("160000", w2)},
                                [main_move, stale])
            dropping = root_child(root, main_move, "merge that mints w2 over x1",
                                  {anchor.WP_ROOT_DELTA_PATH: ("160000", w2)},
                                  [main_move, diverged])
            commits = dict(fixture.commits)
            commits["trust-wp"] = w2

            mint = "no marked parent published child_wp"
            self.assert_policy_refuses(fixture, minted, commits, mint)
            with mock.patch.dict(anchor.TRUST_WP_ADMITTED_MERGE_MINTS, {minted: w2}):
                self.assertEqual(self.policy(fixture, minted, commits)["moves"], 1)
            with mock.patch.dict(anchor.TRUST_WP_ADMITTED_MERGE_MINTS, {minted: w1}):
                self.assert_policy_refuses(fixture, minted, commits, mint)
            with mock.patch.dict(anchor.TRUST_WP_ADMITTED_MERGE_MINTS, {dropping: w2}):
                message = self.assert_policy_refuses(
                    fixture, dropping, commits, "retained means equal to child_wp"
                )
                self.assertIn(x1, message)
                self.assertNotIn(mint, message)
                # The admission names a merge, not a binding: another merge
                # that mints the admitted binding w2 is still a mint.
                self.assert_policy_refuses(fixture, minted, commits, mint)

    def test_p2_forward_ancestry_is_any_parent_containment(self) -> None:
        """Forward means the target CONTAINS the source, through any parent.

        That is how fast.pin-regression reads every other gitlink, and it is
        the shape TrustWP's own integration produces: main is merged into a
        topic and the topic is published, so the new pin contains the old one
        only through its second parent.  A merge whose OTHER parent is a
        foreign, parentless line is forward once it contains W0; whether such
        a commit is published is fast.submodule-remote-reachability's
        question.
        """
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            assert fixture.policy_activation is not None
            root = fixture.root
            wp = fixture.checkout("trust-wp")
            w0 = fixture.commits["trust-wp"]
            retired = retire_receipt(root, fixture.policy_activation)
            commits = dict(fixture.commits)

            main_blob = write_blob(wp, b"main work\n")
            wm = wp_child(wp, w0, "TrustWP main advances", {"main.txt": ("100644", main_blob)})
            topic = wp_child(wp, w0, "TrustWP topic forked at W0",
                             {"topic.txt": ("100644", write_blob(wp, b"topic work\n"))})
            published = commit_tree(wp, derived_tree(wp, topic, {"main.txt": ("100644", main_blob)}),
                                    [topic, wm], "merge main into the topic; publish the topic as main")
            self.assertNotIn(wm, git(wp, "rev-list", "--first-parent", published).split())
            first = pin_wp(root, retired, wm, "move W0 -> wm")
            second = pin_wp(root, first, published, "move wm -> merge(topic, wm)")
            commits["trust-wp"] = wm
            self.assertEqual(self.policy(fixture, first, commits)["moves"], 1)
            commits["trust-wp"] = published
            self.assertEqual(self.policy(fixture, second, commits)["moves"], 2)
            explicit = self.run_checker(fixture, "--rev", second, "--derive-when-receipt-absent")
            self.assertEqual(explicit.returncode, 0, explicit.stderr)

            foreign_tree = derived_tree(wp, w0, {"hijacked.txt": ("100644", write_blob(wp, b"foreign\n"))})
            foreign = commit_tree(wp, foreign_tree, [], "foreign parentless TrustWP history")
            contains_w0 = commit_tree(wp, foreign_tree, [foreign, w0], "foreign line merges W0 in")
            plain_child = commit_tree(wp, foreign_tree, [w0], "plain child of W0 with the same tree")
            for target in (contains_w0, plain_child):
                with self.subTest(target=git(wp, "show", "-s", "--format=%s", target)):
                    tip = pin_wp(root, retired, target, "move to a foreign-tree commit that contains W0")
                    commits["trust-wp"] = target
                    self.assertEqual(self.policy(fixture, tip, commits)["moves"], 1)

    def test_p2_judges_a_move_made_by_the_activation_commit_itself(self) -> None:
        """The v1 introduction may move the gitlink too, and that move is judged.

        An activation commit that both introduces the v1 marker and moves the
        pin to a parentless same-lock commit is refused on (a); one that moves
        it forward is admitted as one move.  (Verifier probe M15.)
        """
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            assert fixture.policy_parent is not None
            root = fixture.root
            wp = fixture.checkout("trust-wp")
            w0 = fixture.commits["trust-wp"]
            v1 = ("100644", write_blob(root, anchor.TERMINAL_POLICY_MARKER))
            orphan = commit_tree(
                wp, git(wp, "rev-parse", f"{w0}^{{tree}}"), [], "parentless wp commit, same tree/lock as W0"
            )
            refused = root_child(
                root, fixture.policy_parent, "activate v1 AND move W0 -> orphan",
                {anchor.TERMINAL_POLICY_MARKER_PATH: v1,
                 anchor.WP_ROOT_DELTA_PATH: ("160000", orphan),
                 anchor.RECEIPT_PATH: None},
            )
            message = self.assert_policy_refuses(
                fixture, refused, {**fixture.commits, "trust-wp": orphan},
                f"refuses the first-party/trust-wp gitlink move at {refused}: X={w0} -> Y={orphan}",
            )
            self.assertIn("(a) not forward", message)
            self.assert_failure(
                self.run_checker(fixture, "--rev", refused, "--derive-when-receipt-absent"),
                "(a) not forward",
            )

            child = wp_child(wp, w0, "forward TrustWP generation")
            admitted = root_child(
                root, fixture.policy_parent, "activate v1 AND move W0 -> child",
                {anchor.TERMINAL_POLICY_MARKER_PATH: v1,
                 anchor.WP_ROOT_DELTA_PATH: ("160000", child),
                 anchor.RECEIPT_PATH: None},
            )
            verdict = self.policy(fixture, admitted, {**fixture.commits, "trust-wp": child})
            self.assertEqual((verdict["activation_commit"], verdict["moves"]), (admitted, 1))

    def test_marked_subgraph_accepts_stale_first_parent_and_repeated_propagation(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            assert fixture.policy_parent is not None
            assert fixture.policy_activation is not None
            root = fixture.root
            wp = fixture.checkout("trust-wp")
            old_wp = fixture.commits["trust-wp"]
            active_wp = wp_child(wp, old_wp, "pre-activation active WP generation")

            base = fixture.policy_parent
            preactivation = pin_wp(root, base, active_wp, "pre-activation root advances WP")
            marker_oid = git(root, "rev-parse", f"{fixture.policy_activation}:{anchor.TERMINAL_POLICY_MARKER_PATH}")
            marked_tree = derived_tree(root, preactivation, {anchor.TERMINAL_POLICY_MARKER_PATH: ("100644", marker_oid)})
            activation = commit_tree(root, marked_tree, [preactivation], "unique policy activation")
            marked = commit_tree(root, marked_tree, [activation], "marked parent")
            stale_one = root_child(root, base, "stable stale first parent")
            merge_one = commit_tree(root, marked_tree, [stale_one, marked], "propagate marker from second parent")
            stale_two = root_child(root, base, "second stable stale branch")
            merge_two = commit_tree(root, marked_tree, [stale_two, merge_one], "repeat propagation with marked second parent")
            commits = dict(fixture.commits)
            commits["trust-wp"] = active_wp
            self.assertEqual(self.policy(fixture, merge_one, commits)["moves"], 0)
            self.assertEqual(self.policy(fixture, merge_two, commits)["moves"], 0)

    def test_marked_subgraph_accepts_same_origin_marked_parent_merge(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            assert fixture.policy_activation is not None
            root = fixture.root
            left = root_child(root, fixture.policy_activation, "marked left branch")
            right = root_child(root, fixture.policy_activation, "marked right branch")
            merge = commit_tree(root, git(root, "rev-parse", f"{left}^{{tree}}"), [left, right],
                                "same-origin marked-parent merge")
            self.assertEqual(self.policy(fixture, merge, fixture.commits)["moves"], 0)

    def test_marked_subgraph_rejects_ambiguous_origins_and_marker_mismatch(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            assert fixture.policy_parent is not None
            assert fixture.policy_activation is not None
            root = fixture.root
            tree = git(root, "rev-parse", f"{fixture.policy_activation}^{{tree}}")
            second_origin = commit_tree(root, tree, [fixture.policy_parent], "independent marker origin")
            ambiguous = commit_tree(root, tree, [fixture.policy_activation, second_origin],
                                    "merge independent marker origins")
            self.assert_policy_refuses(
                fixture, ambiguous, fixture.commits, "one unique raw single-parent introduction"
            )

        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            assert fixture.policy_parent is not None
            assert fixture.policy_activation is not None
            root = fixture.root
            invalid_oid = write_blob(root, b"trust.constellation.terminal-policy.v1\npolicy=wrong\n")
            invalid_parent = root_child(root, fixture.policy_parent, "malformed marker side parent",
                                        {anchor.TERMINAL_POLICY_MARKER_PATH: ("100644", invalid_oid)})
            merge = commit_tree(root, git(root, "rev-parse", f"{fixture.policy_activation}^{{tree}}"),
                                [invalid_parent, fixture.policy_activation], "merge malformed marker lineage")
            self.assert_policy_refuses(fixture, merge, fixture.commits, "malformed marker state")

    def test_marked_subgraph_rejects_inactive_wp_move_revert_and_import(self) -> None:
        for mutation in ("move", "move-revert", "import"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as temporary:
                fixture = self.fixture(temporary)
                assert fixture.policy_parent is not None
                assert fixture.policy_activation is not None
                root = fixture.root
                wp = fixture.checkout("trust-wp")
                old_wp = fixture.commits["trust-wp"]
                active_wp = wp_child(wp, old_wp, "active WP generation")
                side_wp = wp_child(wp, old_wp, "inactive WP mutation")

                base = fixture.policy_parent
                preactivation = pin_wp(root, base, active_wp, "pre-activation WP advance")
                marker_oid = git(root, "rev-parse", f"{fixture.policy_activation}:{anchor.TERMINAL_POLICY_MARKER_PATH}")
                marked_tree = derived_tree(root, preactivation, {anchor.TERMINAL_POLICY_MARKER_PATH: ("100644", marker_oid)})
                activation = commit_tree(root, marked_tree, [preactivation], "policy activation")
                marked = commit_tree(root, marked_tree, [activation], "marked parent")

                if mutation == "import":
                    inactive = root_child(root, base, "inactive side preserves stale WP")
                else:
                    inactive = pin_wp(root, base, side_wp, "inactive side moves WP")
                if mutation == "move-revert":
                    inactive = commit_tree(root, git(root, "rev-parse", f"{base}^{{tree}}"), [inactive],
                                           "inactive side reverts WP")
                merge_tree = (
                    derived_tree(root, marked, {anchor.WP_ROOT_DELTA_PATH: ("160000", old_wp)})
                    if mutation == "import"
                    else marked_tree
                )
                merge = commit_tree(root, merge_tree, [inactive, marked], f"propagation {mutation}")
                commits = dict(fixture.commits)
                commits["trust-wp"] = old_wp if mutation == "import" else active_wp
                expected = (
                    "did not retain every marked-parent TrustWP binding"
                    if mutation == "import"
                    else "minted a TrustWP gitlink no raw parent published"
                )
                self.assert_policy_refuses(fixture, merge, commits, expected)

    def test_marked_subgraph_rejects_delete_readd_marker_lineage(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            assert fixture.policy_activation is not None
            root = fixture.root
            marked_tree = git(root, "rev-parse", f"{fixture.policy_activation}^{{tree}}")
            deleted = root_child(root, fixture.policy_activation, "delete marker",
                                 {anchor.TERMINAL_POLICY_MARKER_PATH: None})
            readded = commit_tree(root, marked_tree, [deleted], "readd marker")
            marked = commit_tree(root, marked_tree, [fixture.policy_activation], "marked sibling")
            merge = commit_tree(root, marked_tree, [readded, marked], "merge delete-readd lineage")
            self.assert_policy_refuses(fixture, merge, fixture.commits, "deleted on a raw DAG edge")

    def test_marked_subgraph_accepts_inactive_branch_that_took_a_newer_main(self) -> None:
        """The shape that refused every push on 2026-08-30, in miniature.

        A feature branch forks while the root pins WP0, main advances the pin
        in a pre-activation commit, the branch merges that newer main, and the
        whole branch is merged into the marked line long after activation.
        The branch has TWO pre-activation frontiers whose bindings differ, and
        one of its internal edges changes the binding -- yet it publishes
        nothing new.  The marked line retains its own binding throughout.
        """
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            assert fixture.policy_parent is not None
            root = fixture.root
            wp = fixture.checkout("trust-wp")
            wp0 = fixture.commits["trust-wp"]
            wp1 = wp_child(wp, wp0, "main advances WP")
            wp2 = wp_child(wp, wp1, "main advances WP again")

            fork = fixture.policy_parent
            fork_tree = git(root, "rev-parse", f"{fork}^{{tree}}")
            newer_main = pin_wp(root, fork, wp1, "pre-activation main advances WP")
            newer_main_tree = git(root, "rev-parse", f"{newer_main}^{{tree}}")
            newest_main = pin_wp(root, newer_main, wp2, "pre-activation main advances WP again")
            marker_oid = git(root, "rev-parse", f"HEAD:{anchor.TERMINAL_POLICY_MARKER_PATH}")
            activation_tree = derived_tree(root, newest_main, {anchor.TERMINAL_POLICY_MARKER_PATH: ("100644", marker_oid)})
            activation = commit_tree(root, activation_tree, [newest_main], "policy activation")
            marked = commit_tree(root, activation_tree, [activation], "marked parent")

            branch = commit_tree(root, fork_tree, [fork], "feature work on the old pin")
            branch_merge = commit_tree(root, newer_main_tree, [newer_main, branch],
                                       "merge newer main into the feature branch")
            merge = commit_tree(root, activation_tree, [branch_merge, marked], "land the branch on the marked line")
            self.assertNotEqual(git(root, "rev-parse", f"{branch_merge}:{anchor.WP_ROOT_DELTA_PATH}"),
                                git(root, "rev-parse", f"{branch}:{anchor.WP_ROOT_DELTA_PATH}"))
            commits = dict(fixture.commits)
            commits["trust-wp"] = wp2
            self.assertEqual(self.policy(fixture, merge, commits)["moves"], 0)

    def test_marked_subgraph_rejects_minted_and_unrooted_inactive_lineage(self) -> None:
        for mutation in ("merge-mint", "orphan"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as temporary:
                fixture = self.fixture(temporary)
                assert fixture.policy_parent is not None
                assert fixture.policy_activation is not None
                root = fixture.root
                wp = fixture.checkout("trust-wp")
                wp0 = fixture.commits["trust-wp"]
                wp1 = wp_child(wp, wp0, "main advances WP")
                minted_wp = wp_child(wp, wp0, "unpublished WP")

                fork = fixture.policy_parent
                fork_tree = git(root, "rev-parse", f"{fork}^{{tree}}")
                newer_main = pin_wp(root, fork, wp1, "pre-activation main advances WP")
                marker_oid = git(root, "rev-parse", f"{fixture.policy_activation}:{anchor.TERMINAL_POLICY_MARKER_PATH}")
                activation_tree = derived_tree(root, newer_main, {anchor.TERMINAL_POLICY_MARKER_PATH: ("100644", marker_oid)})
                activation = commit_tree(root, activation_tree, [newer_main], "policy activation")
                marked = commit_tree(root, activation_tree, [activation], "marked parent")

                if mutation == "merge-mint":
                    branch = commit_tree(root, fork_tree, [fork], "feature work on the old pin")
                    inactive = commit_tree(root, derived_tree(root, fork, {anchor.WP_ROOT_DELTA_PATH: ("160000", minted_wp)}),
                                           [newer_main, branch], "merge resolution mints a third WP binding")
                else:
                    inactive = commit_tree(root, fork_tree, [], "unrooted inactive lineage")
                merge = commit_tree(root, activation_tree, [inactive, marked], f"land the {mutation} lineage")
                commits = dict(fixture.commits)
                commits["trust-wp"] = wp1
                self.assert_policy_refuses(
                    fixture, merge, commits, "minted a TrustWP gitlink no raw parent published"
                )

    def test_marked_subgraph_stash_shaped_lineage_restores_only_its_own_published_binding(self) -> None:
        """The 1fedcff19d shape, in miniature, and the mints it must still refuse.

        A `git stash` taken on a pre-activation commit P (binding wp1) whose
        submodule checkout sat at an OLDER binding wp0 that P's own ancestry
        published: the index commit I (parent P) carries wp0, the WIP commit W
        (parents P, I) carries I's tree, and a preservation merge records W on
        the marked line long after activation with the marked tree (-s ours).
        I changes the binding relative to its only parent, yet introduces
        nothing the regime never saw -- that is a restoration, admitted.  The
        same shape carrying a binding P's pre-activation ancestry never
        published is a mint, refused: a fresh unpublished commit, one only a
        parallel pre-activation line pinned, and one only the marked line
        pinned after activation.
        """
        for mutation in ("restore", "unpublished", "parallel-line", "post-activation"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as temporary:
                fixture = self.fixture(temporary)
                assert fixture.policy_parent is not None
                assert fixture.policy_activation is not None
                root = fixture.root
                wp = fixture.checkout("trust-wp")
                wp0 = fixture.commits["trust-wp"]
                wp1 = wp_child(wp, wp0, "main advances WP")
                wp_parallel = wp_child(wp, wp0, "parallel line pins WP")
                wp_marked = wp_child(wp, wp1, "marked line advances WP")
                wp_fresh = wp_child(wp, wp0, "never pinned anywhere")

                fork = fixture.policy_parent
                stash_base = pin_wp(root, fork, wp1, "pre-activation main advances WP")
                parallel = pin_wp(root, fork, wp_parallel, "pre-activation parallel line")
                joined = commit_tree(root, git(root, "rev-parse", f"{stash_base}^{{tree}}"),
                                     [stash_base, parallel], "pre-activation merge keeps wp1")
                marker_oid = git(root, "rev-parse", f"{fixture.policy_activation}:{anchor.TERMINAL_POLICY_MARKER_PATH}")
                activation_tree = derived_tree(root, joined, {anchor.TERMINAL_POLICY_MARKER_PATH: ("100644", marker_oid)})
                activation = commit_tree(root, activation_tree, [joined], "policy activation")
                marked = pin_wp(root, activation, wp_marked, "marked line advances WP (forward)")
                marked_tree = git(root, "rev-parse", f"{marked}^{{tree}}")

                index_wp = {
                    "restore": wp0,
                    "unpublished": wp_fresh,
                    "parallel-line": wp_parallel,
                    "post-activation": wp_marked,
                }[mutation]
                index = root_child(root, stash_base, "index on b62: stash base",
                                   {anchor.WP_ROOT_DELTA_PATH: ("160000", index_wp)})
                wip = commit_tree(root, git(root, "rev-parse", f"{index}^{{tree}}"),
                                  [stash_base, index], "WIP on b62: stash base")
                merge = commit_tree(root, marked_tree, [marked, wip],
                                    "Merge preserve/stash (ancestry only, -s ours)")
                commits = dict(fixture.commits)
                commits["trust-wp"] = wp_marked
                if mutation == "restore":
                    self.assertEqual(self.policy(fixture, merge, commits)["moves"], 1)
                else:
                    message = self.assert_policy_refuses(
                        fixture, merge, commits, "minted a TrustWP gitlink no raw parent published"
                    )
                    self.assertIn(f"commit={index}", message)
                    self.assertIn(f"commit_wp={index_wp}", message)

    def test_absent_trust_wp_commits_are_fetched_by_sha_and_no_ref_is_written(self) -> None:
        """Clone state is not a finding: what the judgement reads is fetched first.

        The shapes every fresh clone hit (2026-10-24, PUSH-PATH-CLONE-STATE):
        trust-wp's remote main has moved past this store's last fetch, and a
        judged move names a TrustWP commit that only a ``refs/pins/*`` anchor
        on the remote holds.  Both are fetched by sha from the remote before
        any read; no ref and no FETCH_HEAD is written.  A commit the remote
        will not serve is still refused, naming the fetch.
        """
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            root = fixture.root
            remote = fixture.remotes["trust-wp"]
            store = fixture.checkout("trust-wp")
            # Commits only the remote holds: main advanced past the store's
            # fetch, and a pin anchored under refs/pins/ on no branch.
            remote_main = wp_child(remote, fixture.wp_remote_main(), "remote main advances")
            git(remote, "update-ref", "refs/heads/main", remote_main)
            pinned = wp_child(remote, fixture.wp_w0, "pinned only under refs/pins")
            git(remote, "update-ref", f"refs/pins/{pinned}", pinned)
            for sha in (remote_main, pinned):
                self.assertNotEqual(git(store, "cat-file", "-t", sha, check=False), "commit")
            refs_before = git(store, "for-each-ref")
            assert fixture.policy_activation is not None
            retired = retire_receipt(root, fixture.policy_activation)
            # W0 -> pinned is forward (P2a), so the verdict turns only on the
            # judgement being able to read both ends.
            moved = pin_wp(root, retired, pinned, "pin a commit only refs/pins holds")
            commits = dict(fixture.commits)
            commits["trust-wp"] = pinned
            verdict = self.policy(fixture, moved, commits, remote=remote_main)
            self.assertEqual(verdict["wp_remote_main"], remote_main)
            for sha in (remote_main, pinned):
                self.assertEqual(git(store, "cat-file", "-t", sha), "commit", sha)
            self.assertEqual(git(store, "for-each-ref"), refs_before)
            git_dir = Path(git(store, "rev-parse", "--absolute-git-dir"))
            self.assertFalse((git_dir / "FETCH_HEAD").exists())

            # Present now: a second judgement fetches nothing.
            with synthetic_v3_policy(fixture):
                absent, detail = anchor.fetch_absent_trust_wp_objects(store, [remote_main, pinned])
            self.assertEqual((absent, detail), ([], ""))

            # A sha the remote does not serve: tried, still refused.
            with synthetic_v3_policy(fixture):
                absent, detail = anchor.fetch_absent_trust_wp_objects(store, ["e" * 40])
            self.assertEqual(absent, ["e" * 40])
            self.assertIn("did not bring eeeeeeeeeeee", detail)

    def _stash_preserved_by_ours_merge(
        self, fixture: Fixture, wp1: str, staged_wp: str, marked_moves_to: str | None = None
    ) -> tuple[str, str, str, str]:
        """The 1fedcff19d shape (MAIN-REDS-1), in miniature.

        Pre-activation main pins WP0 at the fork and then moves to WP1.  A
        ``git stash`` taken on WP1 has an index commit staging ``staged_wp``
        -- a binding its only raw parent does not carry -- and the stash is
        kept reachable by an ``-s ours`` merge into the marked line, which
        keeps the marked parent's binding (moved forward to
        ``marked_moves_to`` after activation, when given).  Returns
        (merge, index, index parent, judged WP).
        """
        assert fixture.policy_parent is not None
        assert fixture.policy_activation is not None
        root = fixture.root
        newer_main = pin_wp(root, fixture.policy_parent, wp1, "pre-activation main advances WP")
        marker_oid = git(root, "rev-parse", f"{fixture.policy_activation}:{anchor.TERMINAL_POLICY_MARKER_PATH}")
        activation_tree = derived_tree(root, newer_main, {anchor.TERMINAL_POLICY_MARKER_PATH: ("100644", marker_oid)})
        activation = commit_tree(root, activation_tree, [newer_main], "policy activation")
        marked = commit_tree(root, activation_tree, [activation], "marked parent")
        judged_wp = wp1
        if marked_moves_to is not None:
            marked = pin_wp(root, marked, marked_moves_to, "marked line moves WP forward after activation")
            judged_wp = marked_moves_to
        index = pin_wp(root, newer_main, staged_wp, "index on newer main")
        stash = commit_tree(root, git(root, "rev-parse", f"{newer_main}^{{tree}}"), [newer_main, index],
                            "WIP on newer main")
        merge = commit_tree(root, git(root, "rev-parse", f"{marked}^{{tree}}"), [marked, stash],
                            "keep the stash reachable (-s ours)")
        return merge, index, newer_main, judged_wp

    def test_marked_subgraph_unbound_root_carries_no_binding_and_nothing_else_does(self) -> None:
        """A parentless inactive commit with no TrustWP entry mints nothing (CONSTELLATION-UNBOUND-ROOT).

        ``unbound``: a ``git stash -u`` taken ON the marked line, the shape
        3ca41eb1a3 keeps reachable: the stash commit is marked, and its
        untracked-files parent is a lone parentless commit with no
        ``first-party/`` tree. It carries no binding, so it mints none and
        needs no frontier. ``bound``: the same position, but the parentless
        parent carries a binding nobody published, so it mints and never
        rejoins. ``dropped``: an inactive commit WITH a parent that drops the
        gitlink is refused before any mint test; only a parentless commit may
        carry no binding.
        """
        for shape in ("unbound", "bound", "dropped"):
            with self.subTest(shape=shape), tempfile.TemporaryDirectory() as temporary:
                fixture = self.fixture(temporary)
                assert fixture.policy_parent is not None
                assert fixture.policy_activation is not None
                root = fixture.root
                wp = fixture.checkout("trust-wp")
                wp1 = wp_child(wp, fixture.commits["trust-wp"], "main advances WP")
                newer_main = pin_wp(root, fixture.policy_parent, wp1, "pre-activation main advances WP")
                marker_oid = git(root, "rev-parse", f"{fixture.policy_activation}:{anchor.TERMINAL_POLICY_MARKER_PATH}")
                marked_tree = derived_tree(root, newer_main, {anchor.TERMINAL_POLICY_MARKER_PATH: ("100644", marker_oid)})
                activation = commit_tree(root, marked_tree, [newer_main], "policy activation")
                marked = commit_tree(root, marked_tree, [activation], "marked parent")
                commits = {**fixture.commits, "trust-wp": wp1}
                if shape == "dropped":
                    dropped = root_child(root, newer_main, "side drops the TrustWP gitlink",
                                         {anchor.WP_ROOT_DELTA_PATH: None})
                    merge = commit_tree(root, marked_tree, [marked, dropped], "merge the side (-s ours)")
                    self.assert_policy_refuses(
                        fixture, merge, commits, f"inactive child {dropped} is missing committed TrustWP gitlink"
                    )
                    continue
                index = commit_tree(root, marked_tree, [marked], "index on main: nothing staged")
                if shape == "unbound":
                    untracked = commit_tree(root, untracked_files_tree(root), [], "untracked files on main")
                else:
                    unpublished = wp_child(wp, fixture.commits["trust-wp"], "WP no Trust commit ever pinned")
                    bound_tree = derived_tree(root, newer_main, {anchor.WP_ROOT_DELTA_PATH: ("160000", unpublished)})
                    untracked = commit_tree(root, bound_tree, [], "parentless commit carrying a binding")
                stash = commit_tree(root, marked_tree, [marked, index, untracked], "WIP on main: stash -u")
                if shape == "unbound":
                    self.assertEqual(git(root, "ls-tree", untracked, "first-party"), "")
                    self.assertEqual(self.policy(fixture, stash, commits)["moves"], 0)
                else:
                    message = self.assert_policy_refuses(
                        fixture, stash, commits, "minted a TrustWP gitlink no raw parent published"
                    )
                    self.assertIn(f"commit={untracked}", message)
                    self.assertIn("never rejoins pre-activation ancestry", message)

    def test_marked_subgraph_accepts_inactive_commit_restaging_a_preactivation_pin(self) -> None:
        """An inactive commit may stage back a binding pre-activation history published.

        The index commit stages WP0, which no raw parent of it carries but
        which the pre-activation fork commit had already published -- the
        ``1b0fe79fc1`` stash staging ``eb18c75702`` back (MAIN-REDS-1).  The
        lineage introduces no pin the regime never saw, so it mints nothing.
        """
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            assert fixture.policy_parent is not None
            wp0 = fixture.commits["trust-wp"]
            wp1 = wp_child(fixture.checkout("trust-wp"), wp0, "main advances WP")
            self.assertEqual(git(fixture.root, "rev-parse", f"{fixture.policy_parent}:{anchor.WP_ROOT_DELTA_PATH}"), wp0)
            merge, index, index_parent, judged_wp = self._stash_preserved_by_ours_merge(fixture, wp1, wp0)
            self.assertEqual(git(fixture.root, "rev-parse", f"{index_parent}:{anchor.WP_ROOT_DELTA_PATH}"), wp1)
            self.assertEqual(git(fixture.root, "rev-parse", f"{index}:{anchor.WP_ROOT_DELTA_PATH}"), wp0)
            self.assertEqual(git(fixture.root, "rev-parse", f"{index}^@"), index_parent)
            commits = {**fixture.commits, "trust-wp": judged_wp}
            self.assertEqual(self.policy(fixture, merge, commits)["moves"], 0)

    def test_marked_subgraph_rejects_inactive_mint_of_a_pin_preactivation_never_published(self) -> None:
        """The allowance never reaches past the pre-activation history's bindings.

        The index commit stages a WP binding that neither its raw parent nor
        any pre-activation commit carried: once a binding nothing published
        (``never``), once one the marked line published only AFTER activation
        by an admissible forward move (``after-activation``).  Both mint, and
        both are refused with the message the per-commit rule always gave.
        The second is the shape an allowance read from the whole raw DAG, or
        from the inactive lineage itself, would wrongly admit.
        """
        for published in ("never", "after-activation"):
            with self.subTest(published=published), tempfile.TemporaryDirectory() as temporary:
                fixture = self.fixture(temporary)
                wp = fixture.checkout("trust-wp")
                wp1 = wp_child(wp, fixture.commits["trust-wp"], "main advances WP")
                if published == "never":
                    unpublished = wp_child(wp, fixture.commits["trust-wp"], "WP no Trust commit ever pinned")
                    merge, index, index_parent, judged_wp = self._stash_preserved_by_ours_merge(
                        fixture, wp1, unpublished
                    )
                else:
                    unpublished = wp_child(wp, wp1, "WP pinned only after activation, forward from WP1")
                    merge, index, index_parent, judged_wp = self._stash_preserved_by_ours_merge(
                        fixture, wp1, unpublished, marked_moves_to=unpublished
                    )
                commits = {**fixture.commits, "trust-wp": judged_wp}
                message = self.assert_policy_refuses(
                    fixture, merge, commits, "minted a TrustWP gitlink no raw parent published"
                )
                self.assertIn(
                    "Trust terminal-policy inactive merge lineage minted a TrustWP gitlink no raw "
                    f"parent published: merge={merge}, commit={index}, commit_wp={unpublished}, "
                    f"parent_wps={{'{index_parent}': '{wp1}'}}",
                    message,
                )

    def test_marked_subgraph_rejects_marked_parent_wp_divergence(self) -> None:
        """A merge whose first-parent diff hides a side branch's move is judged.

        Main moved W0 -> w1 and the side branch W0 -> x1, both off the
        canonical line; the merge keeps w1, so the first-parent diff shows no
        gitlink change at all, yet x1's binding was dropped.  (Had the merge
        dropped back to W0 itself it would be admissible: W0 is on canonical
        main, clause (b) -- see ``test_p2_merge_may_adopt...``.)
        """
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            assert fixture.policy_activation is not None
            wp = fixture.checkout("trust-wp")
            w0 = fixture.commits["trust-wp"]
            w1 = wp_child(wp, w0, "main's off-main WP move")
            x1 = wp_child(wp, w0, "side-branch WP move")
            main_move = pin_wp(fixture.root, fixture.policy_activation, w1, "main moves WP")
            side = pin_wp(fixture.root, fixture.policy_activation, x1, "root side branch moves WP")
            merge = commit_tree(fixture.root, git(fixture.root, "rev-parse", f"{main_move}^{{tree}}"),
                                [main_move, side], "merge hides side-branch WP move from first-parent diff")
            self.assertEqual(
                git(fixture.root, "diff-tree", "--no-commit-id", "--name-only", "-r", main_move, merge), ""
            )
            self.assert_policy_refuses(
                fixture, merge, {**fixture.commits, "trust-wp": w1},
                "did not retain every marked-parent TrustWP binding",
            )

    def test_marked_subgraph_raw_walk_is_bounded_and_intro_is_unambiguous(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            root_commit = git(fixture.root, "rev-parse", "HEAD")
            with mock.patch.object(anchor, "TERMINAL_POLICY_HISTORY_LIMIT", 2):
                self.assert_policy_refuses(fixture, root_commit, fixture.commits, "bounded limit")

        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            assert fixture.policy_parent is not None
            assert fixture.policy_activation is not None
            side = root_child(fixture.root, fixture.policy_parent, "pre-policy side parent")
            ambiguous = commit_tree(fixture.root, git(fixture.root, "rev-parse", f"{fixture.policy_activation}^{{tree}}"),
                                    [fixture.policy_parent, side], "ambiguous merge marker introduction")
            self.assert_policy_refuses(fixture, ambiguous, fixture.commits, "single-parent commit")

    def test_marked_subgraph_partial_clone_never_lazy_fetches_authority(self) -> None:
        """A missing promised marker stays missing and no upload-pack is invoked."""
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            fixture = self.fixture(str(base / "fixture"))
            marker_oid = git(fixture.root, "rev-parse", f"HEAD:{anchor.TERMINAL_POLICY_MARKER_PATH}")

            remote = base / "authority.git"
            subprocess.run(["git", "clone", "--bare", "-q", str(fixture.root), str(remote)], check=True)
            git(remote, "config", "uploadpack.allowFilter", "true")
            git(remote, "config", "uploadpack.allowAnySHA1InWant", "true")

            partial = base / "partial"
            subprocess.run(
                ["git", "clone", "--no-checkout", "--filter=blob:none", "-q", remote.resolve().as_uri(), str(partial)],
                check=True,
            )
            self.assertEqual(git(partial, "rev-parse", "--is-shallow-repository"), "false")
            before = missing_objects_without_lazy_fetch(partial)
            self.assertIn(marker_oid, before)

            sentinel = base / "upload-pack-invoked"
            upload_pack = base / "recording-upload-pack"
            write(upload_pack, "#!/bin/sh\n: > \"$GIT_UPLOAD_PACK_SENTINEL\"\nexec git-upload-pack \"$@\"\n")
            upload_pack.chmod(0o755)
            git(partial, "config", "remote.origin.uploadpack", str(upload_pack))

            with mock.patch.dict(os.environ, {"GIT_UPLOAD_PACK_SENTINEL": str(sentinel)}, clear=False):
                with synthetic_v3_policy(fixture):
                    with self.assertRaisesRegex(anchor.AnchorError, rf"HEAD marker object {marker_oid} is missing"):
                        anchor.validate_trust_wp_policy(
                            partial, git(partial, "rev-parse", "HEAD"), fixture.commits, fixture.wp_remote_main()
                        )
            self.assertFalse(sentinel.exists())
            self.assertEqual(missing_objects_without_lazy_fetch(partial), before)

            lazy_environment = os.environ.copy()
            lazy_environment.pop("GIT_NO_LAZY_FETCH", None)
            lazy_environment["GIT_UPLOAD_PACK_SENTINEL"] = str(sentinel)
            control = subprocess.run(
                ["git", "-C", str(partial), "cat-file", "blob", marker_oid],
                check=False, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=lazy_environment,
            )
            self.assertEqual(control.returncode, 0, control.stderr.decode("utf-8", "replace"))
            self.assertTrue(sentinel.is_file())

    def test_v3_policy_rejects_replacements_grafts_and_shallow_history(self) -> None:
        for mechanism in ("replacement", "graft", "shallow"):
            for repository in ("trust", "trust-wp"):
                with self.subTest(mechanism=mechanism, repository=repository), tempfile.TemporaryDirectory() as temporary:
                    fixture = self.fixture(temporary)
                    assert fixture.policy_parent is not None
                    assert fixture.policy_activation is not None
                    checkout = fixture.root if repository == "trust" else fixture.checkout("trust-wp")
                    terminal = fixture.policy_activation if repository == "trust" else fixture.wp_floor
                    parent = fixture.policy_parent if repository == "trust" else fixture.wp_w0
                    if mechanism == "replacement":
                        git(checkout, "replace", terminal, parent)
                        # The raw reader itself must still see the literal
                        # object rather than Git's replacement view.
                        with anchor.RawObjectReader(checkout, f"{repository} replacement probe") as reader:
                            _tree, parents = anchor.parse_raw_commit(reader, terminal, "probe")
                        self.assertEqual(parents, [parent])
                        message = "forbidden replacement refs"
                    elif mechanism == "graft":
                        common_dir = Path(git(checkout, "rev-parse", "--path-format=absolute", "--git-common-dir"))
                        write(common_dir / "info" / "grafts", f"{terminal} {parent}\n")
                        message = "forbidden legacy graft authority"
                    else:
                        shallow_path = Path(git(checkout, "rev-parse", "--path-format=absolute", "--git-path", "shallow"))
                        write(shallow_path, f"{terminal}\n")
                        message = "is shallow"
                    self.assert_policy_refuses(
                        fixture, git(fixture.root, "rev-parse", "HEAD"), fixture.commits, message
                    )

    # ------------------------------------------------------------------
    # P3: the lock's cohort bindings.
    # ------------------------------------------------------------------

    def pin_lock(self, fixture: Fixture, content: str | bytes | None, message: str,
                 *, symlink: bool = False) -> tuple[str, dict[str, str]]:
        """Pin (by a forward move) a trust-wp child of W0 carrying ``content`` as its lock."""
        assert fixture.policy_activation is not None
        wp = fixture.checkout("trust-wp")
        if symlink:
            entry: tuple[str, str] | None = ("120000", write_blob(wp, b"missing-DEPENDS.lock"))
        elif content is None:
            entry = None
        else:
            raw = content.encode("ascii") if isinstance(content, str) else content
            entry = ("100644", write_blob(wp, raw))
        target = wp_child(wp, fixture.commits["trust-wp"], message, {anchor.WP_DEPENDS_PATH: entry})
        retired = retire_receipt(fixture.root, fixture.policy_activation)
        tip = pin_wp(fixture.root, retired, target, f"pin: {message}")
        return tip, {**fixture.commits, "trust-wp": target}

    def test_p3_lock_shape_and_committed_blob_fail_closed(self) -> None:
        def rows(fixture: Fixture, trust_row: str) -> str:
            base = fixture.lock_rows()
            return (
                f"clean main {base['clean']}\ntrust-ir main {base['trust-ir']}\n"
                f"trust-cg main {base['trust-cg']}\n{trust_row}\nay main {base['ay']}\n"
            )

        cases = {
            "missing-trust": lambda fixture: rows(fixture, "").replace("\n\n", "\n"),
            "duplicate-trust": lambda fixture: rows(
                fixture, f"trust main {fixture.root_genesis}\ntrust main {fixture.root_genesis}"),
            "wrong-branch": lambda fixture: rows(fixture, f"trust trunk {fixture.root_genesis}"),
            "short-sha": lambda fixture: rows(fixture, "trust main abc"),
            "uppercase-sha": lambda fixture: rows(fixture, f"trust main {fixture.root_genesis.upper()}"),
            "unknown-row": lambda fixture: rows(
                fixture, f"trust main {fixture.root_genesis}\nunknown main {'1' * 40}"),
            "not-a-lock": lambda fixture: "not a lock\n",
        }
        for mutation, content in cases.items():
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as temporary:
                fixture = self.fixture(temporary)
                tip, commits = self.pin_lock(fixture, content(fixture), mutation)
                self.assertEqual(self.policy(fixture, tip, commits)["moves"], 1)
                with self.assertRaises(anchor.AnchorError) as raised:
                    anchor.validate_trust_wp_binding_coherence(fixture.root, tip, commits)
                self.assertIn("trust-wp:spikes/DEPENDS.lock", str(raised.exception))
                result = self.run_checker(fixture, "--rev", tip, "--derive-when-receipt-absent")
                self.assert_failure(result, "trust-wp:spikes/DEPENDS.lock")

        for mutation, needle in (("missing", "is not committed"), ("symlink", "must be a regular committed blob")):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as temporary:
                fixture = self.fixture(temporary)
                tip, commits = self.pin_lock(fixture, None, mutation, symlink=mutation == "symlink")
                result = self.run_checker(fixture, "--rev", tip, "--derive-when-receipt-absent")
                self.assert_failure(result, "spikes/DEPENDS.lock at the pinned TrustWP commit")
                self.assertIn(needle, result.stderr)

    def test_p3_each_row_must_be_an_ancestor_or_equal_of_its_gitlink(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            assert fixture.policy_parent is not None
            root = fixture.root
            # Commits that exist but are not behind the pins: ay AHEAD of its
            # gitlink, clean OFF its line, and a Trust commit the judged
            # revision does not contain.
            ay = fixture.checkout("ay")
            write(ay / "ahead.txt", "ay advanced past its pin\n")
            ay_ahead = commit_all(ay, "ay ahead of the root pin")
            git(ay, "checkout", "-q", "--detach", fixture.commits["ay"])
            clean = fixture.checkout("clean")
            git(clean, "switch", "-q", "--orphan", "elsewhere")
            write(clean / "orphan.txt", "off the pinned line\n")
            clean_orphan = commit_all(clean, "clean commit off the pinned line")
            git(clean, "switch", "-q", "--detach", fixture.commits["clean"])
            trust_side = root_child(root, fixture.policy_parent, "a Trust commit the judged revision does not contain")

            base = fixture.lock_rows()
            cases = (
                ("ay ahead of its gitlink", {**base, "ay": ay_ahead},
                 f"trust-wp:spikes/DEPENDS.lock ay row {ay_ahead} is not an ancestor-or-equal of the "
                 f"first-party/ay gitlink {fixture.commits['ay']} (P3 binding coherence"),
                ("clean off its line", {**base, "clean": clean_orphan},
                 f"trust-wp:spikes/DEPENDS.lock clean row {clean_orphan} is not an ancestor-or-equal of the "
                 f"first-party/clean gitlink {fixture.commits['clean']}"),
                ("trust row not contained by the judged commit", {**base, "trust": trust_side},
                 f"trust-wp:spikes/DEPENDS.lock trust row {trust_side} is not an ancestor-or-equal of the "
                 "judged Trust commit"),
                ("row names no local object", {**base, "trust-cg": "f" * 40},
                 f"trust-wp:spikes/DEPENDS.lock trust-cg row {'f' * 40} is not a local commit object in "
                 "first-party/trust-cg"),
            )
            for label, lock_rows, needle in cases:
                with self.subTest(label=label):
                    tip, commits = self.pin_lock(fixture, wp_depends_lock(lock_rows), label)
                    with self.assertRaises(anchor.AnchorError) as raised:
                        anchor.validate_trust_wp_binding_coherence(root, tip, commits)
                    self.assertIn(needle, str(raised.exception))
                    self.assert_failure(
                        self.run_checker(fixture, "--rev", tip, "--derive-when-receipt-absent"),
                        needle.split(" (P3")[0],
                    )

            # Equality is coherent, and so is a row strictly behind (the
            # fixture's default): siblings advance between trust-wp refreshes.
            equal_rows = {**base, "clean": fixture.commits["clean"], "trust-cg": fixture.commits["trust-cg"],
                          "trust": fixture.policy_activation}
            tip, commits = self.pin_lock(fixture, wp_depends_lock(equal_rows), "rows equal to their pins")
            pins = anchor.validate_trust_wp_binding_coherence(root, tip, commits)
            self.assertEqual(pins["trust"], fixture.policy_activation)
            result = self.run_checker(fixture, "--rev", tip, "--derive-when-receipt-absent")
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("spikes/DEPENDS.lock rows 5/5 ancestor-or-equal (P3)", result.stdout)

            # A legacy graft in the ay store that makes the gitlink descend
            # from ay_ahead is live for plain git and would turn the ahead row
            # into an ancestor; the sibling store is read with grafts refused,
            # exactly as the trust-wp store is.
            tip, commits = self.pin_lock(fixture, wp_depends_lock({**base, "ay": ay_ahead}), "ay ahead, grafted")
            grafts = Path(git(ay, "rev-parse", "--path-format=absolute", "--git-common-dir")) / "info" / "grafts"
            write(grafts, f"{fixture.commits['ay']} {ay_ahead}\n")
            try:
                self.assertTrue(is_ancestor(ay, ay_ahead, fixture.commits["ay"]), "the graft is live for plain git")
                with self.assertRaises(anchor.AnchorError) as raised:
                    anchor.validate_trust_wp_binding_coherence(root, tip, commits)
                self.assertIn(
                    "ay binding-coherence store carries forbidden legacy graft authority",
                    str(raised.exception),
                )
                self.assert_failure(
                    self.run_checker(fixture, "--rev", tip, "--derive-when-receipt-absent"),
                    "ay binding-coherence store carries forbidden legacy graft authority",
                )
            finally:
                grafts.unlink()
            with self.assertRaises(anchor.AnchorError) as raised:
                anchor.validate_trust_wp_binding_coherence(root, tip, commits)
            self.assertIn("ay row", str(raised.exception))

    # ------------------------------------------------------------------
    # The lane, the receipt, and the real history.
    # ------------------------------------------------------------------

    def test_harness_lane_row_and_push_context_judge_the_pushed_revision(self) -> None:
        manifest = (REPO_ROOT / "tests" / "run_trust_comprehensive_harness.sh").read_text(encoding="utf-8")
        rows = [
            line.split("|", 5)
            for line in manifest.splitlines()
            if line.startswith("fast.dependency-constellation|")
        ]
        self.assertEqual(len(rows), 1)
        identity, scopes, category, required, last_checked, command = rows[0]
        # Not a `push` row since 39b35cb9f7 (DEV-MAIN-FOCUSED-VALIDATION-20261102,
        # 2026-11-02): the push profile keeps only its eight
        # live-verifier rows. The row still judges a push's refs under --push-context.
        self.assertEqual(
            (identity, scopes, category, required, command),
            ("fast.dependency-constellation", "fast,release", "supply-chain", "true",
             "scripts/check_dependency_cycle_anchor.py --push-context --derive-when-receipt-absent"),
        )
        if last_checked != "never":
            self.assertEqual(date.fromisoformat(last_checked).isoformat(), last_checked)
        self.assertIn('UNQUARANTINABLE_GATE_IDS = {"fast.dependency-constellation"}', manifest)

        def run_harness(fixture: Fixture, revision: str, old: str) -> subprocess.CompletedProcess[str]:
            environment = os.environ.copy()
            environment[anchor.PUSH_REFS_ENV] = f"refs/heads/main {revision} refs/heads/main {old}"
            return self.run_checker(fixture, "--push-context", "--derive-when-receipt-absent", env=environment)

        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            assert fixture.policy_activation is not None
            root = fixture.root
            wp = fixture.checkout("trust-wp")
            w0 = fixture.commits["trust-wp"]
            side_one = wp_child(wp, w0, "off-main one")
            side_two = wp_child(wp, side_one, "off-main two")
            retired = retire_receipt(root, fixture.policy_activation)
            off_main = pin_wp(root, retired, side_two, "forward off main")
            rolled_back = pin_wp(root, off_main, side_one, "backward, no restoration")
            reanchored = pin_wp(root, off_main, fixture.wp_floor, "re-anchor onto canonical main")
            forged = root_child(root, reanchored, "forge the v3 marker", {
                anchor.TERMINAL_POLICY_V3_MARKER_PATH: ("100644", write_blob(
                    root, anchor.render_terminal_policy_v3_marker(fixture.wp_w0, fixture.wp_floor)
                    .replace(b"ruled=2026-09-21", b"ruled=2026-09-22")))})
            ahead_lock = wp_depends_lock({**fixture.lock_rows(), "trust": rolled_back})
            ahead_wp = wp_child(wp, fixture.wp_floor, "lock trust row off the judged line",
                                {anchor.WP_DEPENDS_PATH: ("100644", write_blob(wp, ahead_lock.encode("ascii")))})
            ahead = pin_wp(root, reanchored, ahead_wp, "pin a lock whose trust row is off the judged line")

            # HEAD stays at activation throughout: the judged revision is the
            # one being pushed, green and red alike.
            self.assertEqual(git(root, "rev-parse", "HEAD"), fixture.policy_activation)
            green = run_harness(fixture, reanchored, off_main)
            self.assertEqual(green.returncode, 0, green.stderr)
            self.assertIn("SUBJECT: push (1 ref update(s))", green.stdout)
            self.assertIn("2 gitlink move(s) since v1 activation admissible (P2)", green.stdout)
            self.assert_failure(run_harness(fixture, rolled_back, off_main), "(a) not forward")
            self.assert_failure(run_harness(fixture, forged, reanchored), "terminal-policy v3 marker row 6 differs")
            self.assert_failure(run_harness(fixture, ahead, reanchored), "is not an ancestor-or-equal of the judged Trust commit")
            # A branch push (the hook's other shape) is judged the same way.
            environment = os.environ.copy()
            environment[anchor.PUSH_REFS_ENV] = f"refs/heads/topic {rolled_back} refs/heads/topic {'0' * 40}"
            self.assert_failure(
                self.run_checker(fixture, "--push-context", "--derive-when-receipt-absent", env=environment),
                "(a) not forward",
            )

    def test_external_receipt_has_no_wp_trust_anchor_member(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            generated = self.run_checker(fixture, "--print-receipt")
            self.assertEqual(generated.returncode, 0, generated.stderr)
            receipt = json.loads(generated.stdout)
            self.assertNotIn("wp_trust_anchor", receipt)
            self.assertEqual(receipt["schema"], anchor.EXTERNAL_SCHEMA)
            anchor.validate_external_receipt(receipt)
            legacy = dict(receipt)
            legacy["wp_trust_anchor"] = None
            with self.assertRaisesRegex(anchor.AnchorError, "keys differ"):
                anchor.validate_external_receipt(legacy)

    def test_verify_remote_main_probes_all_nine_and_trust(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            root_commit = git(fixture.root, "rev-parse", "HEAD")
            with mock.patch.object(anchor, "verify_one_remote_main") as verify_one:
                anchor.verify_remote_main(fixture.commits, root_commit=root_commit)
            expected_calls = [
                mock.call(name, anchor.SUBMODULES[name][1], fixture.commits[name])
                for name in sorted(anchor.SUBMODULES)
            ] + [mock.call("trust", anchor.ROOT_URL, root_commit)]
            self.assertEqual(verify_one.call_args_list, expected_calls)

    def test_remote_main_probe_scrubs_redirecting_git_configuration(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            source = base / "source"
            init_repo(source)
            write(source / "authority", "real remote main\n")
            commit = commit_all(source, "remote main")
            remote = base / "redirect-target.git"
            subprocess.run(
                ["git", "clone", "--bare", "-q", str(source), str(remote)],
                check=True,
            )
            missing = base / "canonical-name" / "repository.git"
            canonical = missing.resolve().as_uri()
            config = base / "attacker.gitconfig"
            git(
                source,
                "config",
                "-f",
                str(config),
                "--add",
                f"url.{remote.resolve().as_uri()}.insteadOf",
                canonical,
            )
            hostile = os.environ.copy()
            hostile["GIT_CONFIG_GLOBAL"] = str(config)
            hostile["GIT_CONFIG_NOSYSTEM"] = "1"

            redirected = subprocess.run(
                ["git", "ls-remote", "--exit-code", canonical, "refs/heads/main"],
                check=False,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                env=hostile,
            )
            self.assertEqual(redirected.returncode, 0, redirected.stderr)
            self.assertEqual(
                redirected.stdout.splitlines(), [f"{commit}\trefs/heads/main"]
            )

            with mock.patch.dict(os.environ, hostile, clear=True):
                with self.assertRaisesRegex(anchor.AnchorError, "cannot resolve probe"):
                    anchor.verify_one_remote_main("probe", canonical, commit)

    def test_github_main_uses_shared_inventory_and_scrubs_configuration(self) -> None:
        commit = "1" * 40
        inventory = subprocess.CompletedProcess(
            ["agh", "repo", "refs"], 0,
            stdout=f"{'2' * 40}\trefs/heads/other\n{commit}\trefs/heads/main\n{'3' * 40}\trefs/pins/source\n",
            stderr="",
        )
        hostile = {
            "GIT_CONFIG": "/tmp/attacker-config", "GIT_CONFIG_COUNT": "1",
            "GIT_CONFIG_KEY_0": "url.file:///tmp/attacker.insteadOf",
            "GIT_CONFIG_VALUE_0": anchor.ROOT_URL,
            "GIT_CONFIG_PARAMETERS": "'url.file:///tmp/attacker.insteadOf'='x'",
            "GIT_DIR": "/tmp/attacker.git", "GIT_CURL_VERBOSE": "1",
            "GIT_EXEC_PATH": "/tmp/attacker-git-helpers", "GIT_SSL_NO_VERIFY": "1",
            "GIT_TRACE_CURL": "1", "SSL_CERT_FILE": "/tmp/attacker-ca.pem",
        }
        original_run = subprocess.run
        with mock.patch.dict(os.environ, hostile, clear=False):
            with mock.patch.object(anchor.rt, "remote_refs", return_value=inventory) as advertised:
                with mock.patch.object(anchor.subprocess, "run", wraps=original_run) as local:
                    anchor.verify_one_remote_main("trust", anchor.ROOT_URL, commit)
        self.assertEqual(advertised.call_count, 1)
        self.assertEqual(advertised.call_args.args, (anchor.ROOT_URL,))
        kwargs = advertised.call_args.kwargs
        environment = kwargs["env"]
        self.assertEqual(environment["GIT_CONFIG_NOSYSTEM"], "1")
        self.assertEqual(environment["GIT_CONFIG_GLOBAL"], os.devnull)
        self.assertEqual(environment["GIT_CONFIG_SYSTEM"], os.devnull)
        self.assertEqual(Path(environment["GIT_CEILING_DIRECTORIES"]), kwargs["cwd"].resolve())
        self.assertEqual(kwargs["git_dir"], kwargs["cwd"] / "witness.git")
        self.assertEqual(kwargs["timeout"], anchor.rt.LS_REMOTE_TIMEOUT_S)
        for key in hostile:
            self.assertNotIn(key, environment)
        self.assertEqual(local.call_count, 1)
        self.assertEqual(local.call_args.args[0][:5], ["git", "init", "--quiet", "--bare", "--template="])
        self.assertTrue(Path(local.call_args.kwargs["cwd"]).name.startswith("trust-remote-main-"))
        self.assertFalse(kwargs["cwd"].exists(), "the private witness view is removed")

    def test_github_route_refuses_without_credential_or_git_fallback(self) -> None:
        refused = subprocess.CompletedProcess(
            ["agh", "repo", "refs"], 11, "", "native authenticated route unavailable"
        )
        original_run = subprocess.run
        with mock.patch.object(anchor.rt, "remote_refs", return_value=refused) as advertised:
            with mock.patch.object(anchor.subprocess, "run", wraps=original_run) as local:
                with self.assertRaisesRegex(anchor.AnchorError, "authenticated route unavailable"):
                    anchor.sample_trust_wp_remote_main()
        self.assertEqual(advertised.call_count, 1)
        self.assertEqual(local.call_count, 1)
        self.assertEqual(local.call_args.args[0][:2], ["git", "init"])

    def test_github_main_requires_exact_single_live_main(self) -> None:
        cases = {
            "missing": "",
            "master only": f"{'1' * 40}\trefs/heads/master\n",
            "duplicate": f"{'1' * 40}\trefs/heads/main\n{'2' * 40}\trefs/heads/main\n",
            "malformed identity": "not-an-oid\trefs/heads/main\n",
        }
        for label, rows in cases.items():
            with self.subTest(label=label):
                done = subprocess.CompletedProcess(["agh", "repo", "refs"], 0, rows, "")
                with mock.patch.object(anchor.rt, "remote_refs", return_value=done):
                    with self.assertRaises(anchor.AnchorError):
                        anchor.sample_trust_wp_remote_main()
        current = subprocess.CompletedProcess(
            ["agh", "repo", "refs"], 0, f"{'2' * 40}\trefs/heads/main\n", ""
        )
        with mock.patch.object(anchor.rt, "remote_refs", return_value=current):
            with mock.patch.object(anchor, "run_git", side_effect=AssertionError("no local tracking-ref authority")):
                with self.assertRaisesRegex(anchor.AnchorError, "not exactly remote main"):
                    anchor.verify_one_remote_main("trust", anchor.ROOT_URL, "1" * 40)

    def test_github_source_intake_keeps_exact_blobs_and_reports_missing_oids(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            store = base / "caller"
            init_repo(store)
            write(store / "source", "original\n")
            before = commit_all(store, "original caller")
            provider = base / "native source provider"
            subprocess.run(["git", "clone", "-q", str(store), str(provider)], check=True)
            git(provider, "config", "user.name", "source-provider")
            git(provider, "config", "user.email", "source-provider@example.invalid")
            write(provider / "spikes/DEPENDS.lock", "actual source blob needed by P2\n")
            wanted = commit_all(provider, "remote source")
            missing = "e" * 40
            refs = git(store, "for-each-ref")
            config = (store / ".git/config").read_bytes()
            fetch_head = store / ".git/FETCH_HEAD"
            fetch_head.write_text("preserve caller fetch head\n")
            calls = []

            def native_source(url, checkout, oid, *, env, timeout):
                self.assertEqual(url, anchor.SUBMODULES["trust-wp"][1])
                self.assertEqual(checkout, store)
                self.assertEqual(timeout, anchor.TRUST_WP_FETCH_TIMEOUT_S)
                calls.append(oid)
                if oid == missing:
                    return subprocess.CompletedProcess(["agh", "repo", "fetch"], 1, "", "source unavailable")
                # Only the service boundary is substituted: transfer real full
                # Git objects from a literal local provider, with no ref update.
                return subprocess.run(
                    ["git", "-C", str(store), "fetch", "--no-write-fetch-head", "--no-tags", "--refmap=",
                     "--", str(provider), oid],
                    capture_output=True, text=True, env=env, timeout=timeout,
                )

            with mock.patch.object(anchor.rt, "fetch_exact_source", side_effect=native_source):
                requested, detail = anchor.fetch_absent_trust_wp_objects(
                    store, [before, wanted, wanted, missing]
                )
            self.assertEqual(requested, [wanted, missing])
            self.assertEqual(calls, [wanted, missing])
            self.assertIn("did not bring eeeeeeeeeeee", detail)
            self.assertEqual(git(store, "show", wanted + ":spikes/DEPENDS.lock"), "actual source blob needed by P2")
            self.assertEqual(git(store, "rev-parse", "HEAD"), before)
            self.assertEqual(git(store, "for-each-ref"), refs)
            self.assertEqual((store / ".git/config").read_bytes(), config)
            self.assertEqual(fetch_head.read_text(), "preserve caller fetch head\n")
            with mock.patch.object(anchor.rt, "fetch_exact_source") as no_intake:
                self.assertEqual(anchor.fetch_absent_trust_wp_objects(store, [wanted, before, wanted]), ([], ""))
                no_intake.assert_not_called()
            success_without_objects = subprocess.CompletedProcess(["agh", "repo", "fetch"], 0, "", "")
            with mock.patch.object(anchor.rt, "fetch_exact_source", return_value=success_without_objects):
                requested, detail = anchor.fetch_absent_trust_wp_objects(store, [missing])
            self.assertEqual(requested, [missing])
            self.assertIn("complete source still unavailable", detail)


if __name__ == "__main__":
    unittest.main()
