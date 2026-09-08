#!/usr/bin/env python3
"""Mutation tests for the committed first-party constellation validator.

Fixtures contain real Cargo manifests, lockfiles, Lake manifests, proof identity,
Git history, and nine committed gitlinks.  No state-file stand-in is used.
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
def synthetic_v2_policy(w0: str, preservation_floor: str):
    """Bind production's fixed identities to real synthetic commit objects."""
    pre_marker = (
        "trust.constellation.terminal-policy.v2\n"
        "state=pre-v2\n"
        "policy=trust-wp-root-cycle-forward\n"
        f"w0={w0}\n"
        f"preservation-floor={preservation_floor}\n"
    ).encode("ascii")
    with mock.patch.multiple(
        anchor,
        TERMINAL_POLICY_V2_W0=w0,
        TERMINAL_POLICY_V2_PRESERVATION_FLOOR=preservation_floor,
        TERMINAL_POLICY_V2_PRE_MARKER=pre_marker,
    ):
        yield


@dataclass
class Fixture:
    root: Path
    remotes: dict[str, Path]
    commits: dict[str, str]
    ancestors: dict[str, str]
    receipt: dict[str, object]
    root_anchor: str | None = None
    root_terminal: str | None = None
    anchor_wp: str | None = None
    policy_parent: str | None = None
    policy_activation: str | None = None

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

    def prepare_wp_root_cycle(
        self,
        *,
        depends_content: str | None = None,
        extra_root_delta: bool = False,
        extra_root_gitlink: str | None = None,
        extra_wp_delta: bool = False,
        allowed_lock_delta: bool = False,
        omit_required_delta: str | None = None,
        new_lock_delta: bool = False,
        wp_intermediate: bool = False,
        partial_wp_delta: bool = False,
    ) -> tuple[str, str]:
        """Cut synthetic R0 -> W1 -> R1 in the production ordering."""
        legacy_receipt = self.root / anchor.RECEIPT_PATH
        if legacy_receipt.exists() or legacy_receipt.is_symlink():
            legacy_receipt.unlink()
            commit_all(self.root, "R0 removes the obsolete tracked receipt")
        self.root_anchor = git(self.root, "rev-parse", "HEAD")
        self.anchor_wp = self.commits["trust-wp"]
        if extra_root_gitlink is not None:
            checkout = self.checkout(extra_root_gitlink)
            write(
                checkout / "terminal-cycle-extra.txt",
                "extra root gitlink mutation hidden by local diff config\n",
            )
            self.commits[extra_root_gitlink] = commit_all(
                checkout, f"advance {extra_root_gitlink} during terminal cut"
            )
            git(self.root, "add", anchor.SUBMODULES[extra_root_gitlink][0])
        if depends_content is None:
            depends_content = (
                "# Format: <repository> main <full-40-character-commit>\n"
                f"clean main {self.commits['clean']}\n"
                f"trust-ir main {self.commits['trust-ir']}\n"
                f"trust-cg main {self.commits['trust-cg']}\n"
                f"trust main {self.root_anchor}\n"
                f"ay main {self.commits['ay']}\n"
            )
        wp = self.checkout("trust-wp")
        if wp_intermediate:
            write(wp / "intermediate.txt", "W0 must be W1's immediate parent\n")
            commit_all(wp, "intermediate TrustWP generation")
        if not partial_wp_delta and omit_required_delta != "Cargo.toml":
            cargo_manifest = wp / "Cargo.toml"
            cargo_text = cargo_manifest.read_text(encoding="utf-8")
            cargo_text = re.sub(
                r"^# Current AY authority: version=\S+ commit=[0-9a-f]{40}$",
                "# Current AY authority: "
                f"version=0.1.0 commit={self.commits['ay']}",
                cargo_text,
                flags=re.MULTILINE,
            )
            write(
                cargo_manifest,
                cargo_text
                + "\n[dependencies]\n"
                + 'trust-ir = { git = "'
                + anchor.SUBMODULES["trust-ir"][1]
                + f'", rev = "{self.commits["trust-ir"]}" }}\n',
            )
        if not partial_wp_delta and omit_required_delta != "VISION.md":
            vision = wp / "VISION.md"
            vision_text = re.sub(
                r"^\| trust-wp-ay \|.*$",
                "| trust-wp-ay | Building | See current review artifacts | "
                "AYEncoder with native ADT theory, "
                f"AY v0.1.0 backend at `{self.commits['ay'][:8]}` "
                "on current `main`, separation logic encoding |",
                vision.read_text(encoding="utf-8"),
                flags=re.MULTILINE,
            )
            write(
                vision,
                vision_text,
            )
        if not partial_wp_delta and omit_required_delta != anchor.WP_DEPENDS_PATH:
            write(wp / anchor.WP_DEPENDS_PATH, depends_content)
        cargo_lock = wp / "Cargo.lock"
        if partial_wp_delta:
            write(
                cargo_lock,
                cargo_lock.read_text(encoding="utf-8")
                + "# partial W1 lock mutation with restored authorities\n",
            )
            write(wp / "illicit-terminal-file.txt", "not on the W1 checklist\n")
        else:
            write(
                cargo_lock,
                lockfile("trust-ir", "trust-ir", self.commits["trust-ir"]),
            )
        if allowed_lock_delta:
            write(
                cargo_lock,
                cargo_lock.read_text(encoding="utf-8")
                + "# mechanically refreshed terminal lock\n",
            )
        if new_lock_delta:
            write(wp / "invented" / "Cargo.lock", "version = 4\n")
        if extra_wp_delta:
            write(wp / "illicit-terminal-file.txt", "not on the W1 checklist\n")
        terminal_wp = commit_all(wp, "W1 pins Trust root anchor")
        self.commits["trust-wp"] = terminal_wp
        git(self.root, "add", anchor.WP_ROOT_DELTA_PATH)
        if extra_root_delta:
            write(self.root / "unexpected-root-delta", "not part of the cycle break\n")
            git(self.root, "add", "unexpected-root-delta")
        self.root_terminal = commit_all(self.root, "R1 binds terminal TrustWP")
        return self.root_anchor, self.root_terminal

    def amend_wp_terminal(self, mutate: Callable[[Path], None]) -> None:
        """Rewrite synthetic W1 and then rewrite R1 to bind that exact W1."""
        wp = self.checkout("trust-wp")
        mutate(wp)
        git(wp, "add", "-A")
        git(wp, "commit", "--amend", "-qm", "mutated W1 authority")
        self.commits["trust-wp"] = git(wp, "rev-parse", "HEAD")
        git(self.root, "add", anchor.WP_ROOT_DELTA_PATH)
        git(self.root, "commit", "--amend", "-qm", "mutated R1 binding")
        self.root_terminal = git(self.root, "rev-parse", "HEAD")

    def advance_wp_v2_predecessor(self) -> tuple[str, str]:
        wp = self.checkout("trust-wp")
        write(wp / "published-floor.txt", "published history must survive\n")
        preservation_floor = commit_all(wp, "published preservation floor B")
        write(wp / "publication-predecessor.txt", "forward migration predecessor\n")
        predecessor = commit_all(wp, "publication predecessor P")
        return preservation_floor, predecessor

    def prepare_wp_root_cycle_v2(
        self, preservation_floor: str, predecessor: str
    ) -> dict[str, object]:
        """Build W0 -> B -> P -> W1 and PreV2 -> R0 -> R1 literally.

        The caller patches the module's production W0/B constants to this
        fixture's synthetic commits.  R0/R1 are made with ``commit-tree`` so
        the root worktree may keep TrustWP checked out at P/W1 while R0's
        committed gitlink remains exact W0.
        """
        w0 = self.commits["trust-wp"]
        if anchor.TERMINAL_POLICY_V2_W0 != w0:
            raise AssertionError("synthetic v2 policy must bind fixture W0")

        wp = self.checkout("trust-wp")
        if anchor.TERMINAL_POLICY_V2_PRESERVATION_FLOOR != preservation_floor:
            raise AssertionError("synthetic v2 policy must bind fixture floor B")
        if git(wp, "rev-parse", "HEAD") != predecessor:
            raise AssertionError("TrustWP checkout must be at synthetic predecessor P")

        write(
            self.root / anchor.TERMINAL_POLICY_V2_MARKER_PATH,
            anchor.TERMINAL_POLICY_V2_PRE_MARKER.decode("ascii"),
        )
        # Keep the root gitlink at W0 while the nested checkout is already at P.
        pre_blob = write_blob(self.root, anchor.TERMINAL_POLICY_V2_PRE_MARKER)
        pre_tree = derived_tree(
            self.root,
            git(self.root, "rev-parse", "HEAD"),
            {anchor.TERMINAL_POLICY_V2_MARKER_PATH: ("100644", pre_blob)},
        )
        pre = commit_tree(
            self.root,
            pre_tree,
            [git(self.root, "rev-parse", "HEAD")],
            "introduce terminal-policy v2 PreV2 marker",
        )

        root_bindings = dict(self.commits)
        armed_blob = write_blob(
            self.root,
            anchor.render_terminal_policy_v2_armed(predecessor, root_bindings),
        )
        r0_tree = derived_tree(
            self.root,
            pre,
            {
                anchor.RECEIPT_PATH: None,
                anchor.TERMINAL_POLICY_V2_MARKER_PATH: ("100644", armed_blob),
            },
        )
        r0 = commit_tree(self.root, r0_tree, [pre], "arm exact v2 R0 policy")

        cargo_manifest = wp / "Cargo.toml"
        cargo_text = re.sub(
            r"^# Current AY authority: version=\S+ commit=[0-9a-f]{40}$",
            "# Current AY authority: "
            f"version=0.1.0 commit={root_bindings['ay']}",
            cargo_manifest.read_text(encoding="utf-8"),
            flags=re.MULTILINE,
        )
        write(
            cargo_manifest,
            cargo_text
            + "\n[dependencies]\n"
            + 'trust-ir = { git = "'
            + anchor.SUBMODULES["trust-ir"][1]
            + f'", rev = "{root_bindings["trust-ir"]}" }}\n',
        )
        vision = wp / "VISION.md"
        write(
            vision,
            re.sub(
                r"^\| trust-wp-ay \|.*$",
                "| trust-wp-ay | Building | See current review artifacts | "
                "AYEncoder with native ADT theory, "
                f"AY v0.1.0 backend at `{root_bindings['ay'][:8]}` "
                "on current `main`, separation logic encoding |",
                vision.read_text(encoding="utf-8"),
                flags=re.MULTILINE,
            ),
        )
        write(
            wp / anchor.WP_DEPENDS_PATH,
            "# Format: <repository> main <full-40-character-commit>\n"
            f"clean main {root_bindings['clean']}\n"
            f"trust-ir main {root_bindings['trust-ir']}\n"
            f"trust-cg main {root_bindings['trust-cg']}\n"
            f"trust main {r0}\n"
            f"ay main {root_bindings['ay']}\n",
        )
        write(
            wp / "Cargo.lock",
            lockfile("trust-ir", "trust-ir", root_bindings["trust-ir"]),
        )
        w1 = commit_all(wp, "W1 publishes exact v2 Trust root anchor")

        r1_tree = derived_tree(
            self.root, r0, {anchor.WP_ROOT_DELTA_PATH: ("160000", w1)}
        )
        r1 = commit_tree(self.root, r1_tree, [r0], "R1 binds v2 terminal TrustWP")
        self.root_anchor = r0
        self.root_terminal = r1
        self.anchor_wp = w0
        self.commits["trust-wp"] = w1
        return {
            "pre": pre,
            "w0": w0,
            "preservation_floor": preservation_floor,
            "predecessor": predecessor,
            "root_bindings": root_bindings,
            "r0": r0,
            "w1": w1,
            "r1": r1,
        }


def make_fixture(base: Path) -> Fixture:
    remotes: dict[str, Path] = {}
    commits: dict[str, str] = {}
    ancestors: dict[str, str] = {}

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
    for name in ("trust-vc", "trust-wp", "ty"):
        repo = base / "remotes" / name
        init_repo(repo)
        write(repo / "Cargo.toml", package_manifest(name))
        if name == "trust-wp":
            write(
                repo / "Cargo.toml",
                package_manifest(name)
                + "# Current AY authority: version=0.0.0 commit="
                + "6" * 40
                + "\n",
            )
            write(
                repo / "VISION.md",
                "# TrustWP fixture vision\n"
                "| trust-wp-ay | Building | See current review artifacts | "
                "AYEncoder with native ADT theory, "
                "AY v0.0.0 backend at `66666666` on current `main`, "
                "separation logic encoding |\n",
            )
            write(repo / "Cargo.lock", "version = 4\n")
            write(
                repo / anchor.WP_DEPENDS_PATH,
                "clean main " + "1" * 40 + "\n"
                "trust-ir main " + "2" * 40 + "\n"
                "trust-cg main " + "3" * 40 + "\n"
                "trust main " + "4" * 40 + "\n"
                "ay main " + "5" * 40 + "\n",
            )
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

    root = base / "root"
    init_repo(root)
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

    def test_v2_armed_marker_fixed_fields_and_bytes_are_exact(self) -> None:
        bindings = {name: "1" * 40 for name in anchor.SUBMODULES}
        bindings["trust-wp"] = anchor.TERMINAL_POLICY_V2_W0
        marker = anchor.render_terminal_policy_v2_armed("2" * 40, bindings)
        parsed = anchor.parse_terminal_policy_v2_armed(marker)
        self.assertEqual(parsed["predecessor_commit"], "2" * 40)
        self.assertEqual(parsed["root_bindings"], bindings)
        mutations = (
            marker.replace(
                f"w0={anchor.TERMINAL_POLICY_V2_W0}".encode(),
                f"w0={'3' * 40}".encode(),
            ),
            marker.replace(
                f"preservation-floor={anchor.TERMINAL_POLICY_V2_PRESERVATION_FLOOR}".encode(),
                f"preservation-floor={'4' * 40}".encode(),
            ),
            marker.rstrip(b"\n"),
            marker + b"extra=authority\n",
        )
        for mutation in mutations:
            with self.subTest(mutation=mutation[-48:]), self.assertRaises(
                anchor.AnchorError
            ):
                anchor.parse_terminal_policy_v2_armed(mutation)

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
    def fixture(self, temporary: str) -> Fixture:
        return make_fixture(Path(temporary))

    def run_checker(
        self,
        fixture: Fixture,
        *arguments: str,
        env: dict[str, str] | None = None,
    ) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [sys.executable, str(SCRIPT), "--repo-root", str(fixture.root), *arguments],
            check=False,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=env,
        )

    def run_terminal_checker_with_remote_witness(
        self, fixture: Fixture, *arguments: str
    ) -> tuple[subprocess.CompletedProcess[str], list[object]]:
        """Exercise the real CLI while replacing only the network witness."""
        stdout = io.StringIO()
        stderr = io.StringIO()
        cli_arguments = ["--repo-root", str(fixture.root)]
        cli_arguments.extend(
            arguments
            or (
                "--print-receipt",
                "--require-wp-trust-anchor",
                "--verify-remote",
            )
        )
        with mock.patch.object(anchor, "verify_remote_main") as verify_remote:
            with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
                returncode = anchor.main(cli_arguments)
            calls = list(verify_remote.call_args_list)
        return (
            subprocess.CompletedProcess(
                [str(SCRIPT), *cli_arguments],
                returncode,
                stdout.getvalue(),
                stderr.getvalue(),
            ),
            calls,
        )

    def assert_failure(self, result: subprocess.CompletedProcess[str], needle: str) -> None:
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn(needle, result.stderr)

    def test_checked_in_v2_pre_marker_binds_ratified_real_constants(self) -> None:
        self.assertEqual(
            anchor.TERMINAL_POLICY_V2_W0,
            "e7c353690e1b58a4e830edc9facb0e4396164585",
        )
        self.assertEqual(
            anchor.TERMINAL_POLICY_V2_PRESERVATION_FLOOR,
            "1de995e192aabec74646d4d53642df05fa59466f",
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
                if dependency == "trust-wp":
                    # Any freshly committed WP-gitlink advance is a terminal
                    # claim until the exact W1/R1 validator proves otherwise.
                    self.assert_failure(
                        generated, "external/untracked in terminal TrustWP anchor mode"
                    )
                    continue
                self.assertEqual(generated.returncode, 0, generated.stderr)
                receipt = json.loads(generated.stdout)
                self.assertEqual(receipt["schema"], anchor.EXTERNAL_SCHEMA)
                self.assertEqual(receipt["self"]["commit"], root_terminal)
                self.assertEqual(receipt["repositories"][dependency]["commit"], terminal)
                self.assertIsNone(receipt["wp_trust_anchor"])

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

    def test_checked_in_policy_marker_keeps_real_wp0_preterminal(self) -> None:
        root_commit = git(REPO_ROOT, "rev-parse", "HEAD")
        submodules = anchor.committed_submodules(REPO_ROOT, root_commit)
        commits = {
            name: commit for name, (_path, _url, commit) in submodules.items()
        }
        # Permanent regression for the merge that exposed the first-parent
        # bug: the unmarked parent is first and carries an older WP binding;
        # the marked second parent and merge result carry the active binding.
        propagation = "3c2c11e530bb5e0253f8a412f4a0892528915091"
        parents = git(REPO_ROOT, "show", "-s", "--format=%P", propagation).split()
        self.assertEqual(
            parents,
            [
                "0e831c4100ca2fc54c40ca77877af74a2e9b4cdd",
                "7f67d33f2207838198b6d1b903f204cdf0fa24b6",
            ],
        )
        self.assertEqual(
            git(REPO_ROOT, "ls-tree", parents[0], "--", anchor.TERMINAL_POLICY_MARKER_PATH),
            "",
        )
        self.assertEqual(
            git(REPO_ROOT, "rev-parse", f"{propagation}:{anchor.WP_ROOT_DELTA_PATH}"),
            git(REPO_ROOT, "rev-parse", f"{parents[1]}:{anchor.WP_ROOT_DELTA_PATH}"),
        )
        self.assertNotEqual(
            git(REPO_ROOT, "rev-parse", f"{propagation}:{anchor.WP_ROOT_DELTA_PATH}"),
            git(REPO_ROOT, "rev-parse", f"{parents[0]}:{anchor.WP_ROOT_DELTA_PATH}"),
        )
        inactive_path = [
            "0e831c4100ca2fc54c40ca77877af74a2e9b4cdd",
            "600cfafd1a83f33e5d19f10d31f1324b43f25581",
            "f2d4a3ceb2a6406f03f0af6d7130dc6e0314935e",
            "e612f2a9a092cd805e618cfde4f3c14aff3d847b",
            "8da804d258cbde972b91891660be0311cd572a4d",
        ]
        inactive_wps = [
            git(REPO_ROOT, "rev-parse", f"{commit}:{anchor.WP_ROOT_DELTA_PATH}")
            for commit in inactive_path
        ]
        self.assertEqual(len(set(inactive_wps)), 1)
        for child, parent in zip(inactive_path, inactive_path[1:]):
            self.assertIn(
                parent,
                git(REPO_ROOT, "show", "-s", "--format=%P", child).split(),
            )
        self.assertFalse(
            anchor.terminal_wp_policy_claimed(REPO_ROOT, root_commit, commits)
        )

    def test_v2_exact_forward_cut_and_remote_transition_accepts(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            w0 = fixture.commits["trust-wp"]
            preservation_floor, predecessor = fixture.advance_wp_v2_predecessor()
            with synthetic_v2_policy(w0, preservation_floor):
                cut = fixture.prepare_wp_root_cycle_v2(
                    preservation_floor, predecessor
                )
                r0 = str(cut["r0"])
                r1 = str(cut["r1"])
                root_bindings = dict(cut["root_bindings"])

                armed = anchor.terminal_wp_policy_v2_state(
                    fixture.root, r0, root_bindings
                )
                self.assertEqual(armed["state"], "Armed")
                self.assertEqual(armed["r0"], r0)

                terminal = anchor.terminal_wp_policy_v2_state(
                    fixture.root, r1, fixture.commits
                )
                self.assertEqual(terminal["state"], "Terminal")
                observed = anchor.derive_wp_root_anchor_v2(
                    fixture.root, r1, fixture.commits, terminal
                )
                self.assertEqual(observed["anchor_commit"], r0)
                self.assertEqual(observed["anchor_gitlink"], w0)
                self.assertEqual(observed["preservation_floor"], preservation_floor)
                self.assertEqual(observed["predecessor_commit"], predecessor)
                self.assertEqual(observed["root_bindings"], root_bindings)
                self.assertEqual(
                    anchor.validate_wp_root_anchor(observed), observed
                )

                exclusions = fixture.receipt["exclusions"]
                assert isinstance(exclusions, list)
                with mock.patch.object(anchor, "verify_one_remote_main") as remote:
                    receipt = anchor.derive_receipt(
                        fixture.root,
                        r1,
                        exclusions,
                        external_evidence=False,
                        prospective_root_old=r0,
                    )
                self.assertEqual(receipt["wp_trust_anchor"], observed)
                self.assertIn(
                    mock.call("trust", anchor.ROOT_URL, r0),
                    remote.call_args_list,
                )
                self.assertIn(
                    mock.call(
                        "trust-wp",
                        anchor.SUBMODULES["trust-wp"][1],
                        str(cut["w1"]),
                    ),
                    remote.call_args_list,
                )

                with mock.patch.object(anchor, "verify_one_remote_main") as post_remote:
                    anchor.verify_terminal_policy_v2_remote_main(
                        fixture.root,
                        terminal,
                        fixture.commits,
                        root_commit=r1,
                        prospective_root_old=None,
                    )
                self.assertIn(
                    mock.call("trust", anchor.ROOT_URL, r1),
                    post_remote.call_args_list,
                )
                with (
                    mock.patch.object(anchor, "verify_one_remote_main"),
                    self.assertRaisesRegex(
                        anchor.AnchorError,
                        "advertised old Trust remote main differs",
                    ),
                ):
                    anchor.verify_terminal_policy_v2_remote_main(
                        fixture.root,
                        terminal,
                        fixture.commits,
                        root_commit=r1,
                        prospective_root_old=str(cut["pre"]),
                    )

                push_env = {
                    anchor.PUSH_REFS_ENV: (
                        f"refs/heads/local {r1} refs/heads/main {r0}"
                    )
                }
                with mock.patch.dict(os.environ, push_env, clear=False):
                    self.assertEqual(anchor.pushed_main_old_for_source(r1), r0)

    def test_v2_main_push_authenticates_old_state_and_refuses_rollback(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            w0 = fixture.commits["trust-wp"]
            preservation_floor, predecessor = fixture.advance_wp_v2_predecessor()
            with synthetic_v2_policy(w0, preservation_floor):
                cut = fixture.prepare_wp_root_cycle_v2(
                    preservation_floor, predecessor
                )
                r1 = str(cut["r1"])
                pre = str(cut["pre"])
                unmarked = git(fixture.root, "rev-parse", f"{pre}^")
                inactive_commits = {
                    name: commit
                    for name, (_path, _url, commit) in anchor.committed_submodules(
                        fixture.root, unmarked
                    ).items()
                }
                inactive = anchor.terminal_wp_policy_v2_state(
                    fixture.root, unmarked, inactive_commits
                )
                with (
                    mock.patch.object(anchor, "verify_one_remote_main") as remote,
                    self.assertRaisesRegex(anchor.AnchorError, "may not downgrade"),
                ):
                    anchor.authenticate_terminal_policy_v2_main_transition(
                        fixture.root, unmarked, inactive, r1
                    )
                remote.assert_called_once_with("trust", anchor.ROOT_URL, r1)

                stdout = io.StringIO()
                stderr = io.StringIO()
                push_env = {
                    anchor.PUSH_REFS_ENV: (
                        f"refs/heads/local {unmarked} refs/heads/main {r1}"
                    )
                }
                with (
                    mock.patch.dict(os.environ, push_env, clear=False),
                    mock.patch.object(anchor, "verify_one_remote_main"),
                    contextlib.redirect_stdout(stdout),
                    contextlib.redirect_stderr(stderr),
                ):
                    returncode = anchor.main(
                        [
                            "--repo-root",
                            str(fixture.root),
                            "--push-context",
                            "--derive-when-receipt-absent",
                        ]
                    )
                self.assertNotEqual(returncode, 0, stdout.getvalue())
                self.assertIn("may not downgrade", stderr.getvalue())

                terminal = anchor.terminal_wp_policy_v2_state(
                    fixture.root, r1, fixture.commits
                )
                with (
                    mock.patch.object(
                        anchor,
                        "verify_one_remote_main",
                        side_effect=anchor.AnchorError("remote main raced"),
                    ),
                    self.assertRaisesRegex(anchor.AnchorError, "remote main raced"),
                ):
                    anchor.authenticate_terminal_policy_v2_main_transition(
                        fixture.root, r1, terminal, r1
                    )

    def test_v2_main_push_refuses_marker_reintroduction_lineage(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            w0 = fixture.commits["trust-wp"]
            preservation_floor, predecessor = fixture.advance_wp_v2_predecessor()
            with synthetic_v2_policy(w0, preservation_floor):
                cut = fixture.prepare_wp_root_cycle_v2(
                    preservation_floor, predecessor
                )
                pre = str(cut["pre"])
                unmarked = git(fixture.root, "rev-parse", f"{pre}^")
                marker = write_blob(
                    fixture.root, anchor.TERMINAL_POLICY_V2_PRE_MARKER
                )
                replacement_tree = derived_tree(
                    fixture.root,
                    unmarked,
                    {anchor.TERMINAL_POLICY_V2_MARKER_PATH: ("100644", marker)},
                )
                replacement = commit_tree(
                    fixture.root,
                    replacement_tree,
                    [unmarked],
                    "re-add v2 marker on replacement lineage",
                )
                replacement_commits = {
                    name: commit
                    for name, (_path, _url, commit) in anchor.committed_submodules(
                        fixture.root, replacement
                    ).items()
                }
                replacement_state = anchor.terminal_wp_policy_v2_state(
                    fixture.root, replacement, replacement_commits
                )
                with (
                    mock.patch.object(anchor, "verify_one_remote_main"),
                    self.assertRaisesRegex(anchor.AnchorError, "replace, or re-add"),
                ):
                    anchor.authenticate_terminal_policy_v2_main_transition(
                        fixture.root, replacement, replacement_state, pre
                    )

    def test_v2_terminal_receipt_mutation_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            w0 = fixture.commits["trust-wp"]
            preservation_floor, predecessor = fixture.advance_wp_v2_predecessor()
            with synthetic_v2_policy(w0, preservation_floor):
                cut = fixture.prepare_wp_root_cycle_v2(
                    preservation_floor, predecessor
                )
                exclusions = fixture.receipt["exclusions"]
                assert isinstance(exclusions, list)
                with mock.patch.object(anchor, "verify_one_remote_main"):
                    receipt = anchor.derive_receipt(
                        fixture.root,
                        str(cut["r1"]),
                        exclusions,
                        external_evidence=False,
                        prospective_root_old=str(cut["r0"]),
                    )
                mutated = json.loads(json.dumps(receipt))
                mutated["wp_trust_anchor"]["root_bindings"]["ay"] = "f" * 40
                with self.assertRaisesRegex(
                    anchor.AnchorError, "armed R0 vector differs"
                ):
                    anchor.validate_external_receipt(mutated)

    def test_v2_terminal_rechecks_no_prior_v1_move_at_r0(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            w0 = fixture.commits["trust-wp"]
            preservation_floor, predecessor = fixture.advance_wp_v2_predecessor()
            with synthetic_v2_policy(w0, preservation_floor):
                base = git(fixture.root, "rev-parse", "HEAD")
                moved_tree = derived_tree(
                    fixture.root,
                    base,
                    {anchor.WP_ROOT_DELTA_PATH: ("160000", preservation_floor)},
                )
                moved = commit_tree(
                    fixture.root, moved_tree, [base], "pre-v2 illicit W0 to X"
                )
                reverted_tree = derived_tree(
                    fixture.root,
                    moved,
                    {anchor.WP_ROOT_DELTA_PATH: ("160000", w0)},
                )
                reverted = commit_tree(
                    fixture.root, reverted_tree, [moved], "pre-v2 illicit X to W0"
                )
                git(fixture.root, "update-ref", "HEAD", reverted)
                cut = fixture.prepare_wp_root_cycle_v2(
                    preservation_floor, predecessor
                )
                with self.assertRaisesRegex(
                    anchor.AnchorError, "moved and later returned|prior v1"
                ):
                    anchor.terminal_wp_policy_v2_state(
                        fixture.root, str(cut["r1"]), fixture.commits
                    )

    def test_v2_every_r0_vector_member_is_policy_bound(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            w0 = fixture.commits["trust-wp"]
            preservation_floor, predecessor = fixture.advance_wp_v2_predecessor()
            with synthetic_v2_policy(w0, preservation_floor):
                cut = fixture.prepare_wp_root_cycle_v2(
                    preservation_floor, predecessor
                )
                pre = str(cut["pre"])
                correct = dict(cut["root_bindings"])
                canonical = anchor.render_terminal_policy_v2_armed(
                    predecessor, correct
                )
                wrong_sha = "f" * 40
                for repository in sorted(anchor.SUBMODULES):
                    with self.subTest(repository=repository):
                        if repository == "trust-wp":
                            wrong_marker = canonical.replace(
                                f"root.{repository}={correct[repository]}".encode(),
                                f"root.{repository}={wrong_sha}".encode(),
                            )
                        else:
                            wrong = dict(correct)
                            wrong[repository] = wrong_sha
                            wrong_marker = anchor.render_terminal_policy_v2_armed(
                                predecessor, wrong
                            )
                        marker_blob = write_blob(fixture.root, wrong_marker)
                        candidate_tree = derived_tree(
                            fixture.root,
                            pre,
                            {
                                anchor.RECEIPT_PATH: None,
                                anchor.TERMINAL_POLICY_V2_MARKER_PATH: (
                                    "100644",
                                    marker_blob,
                                ),
                            },
                        )
                        candidate = commit_tree(
                            fixture.root,
                            candidate_tree,
                            [pre],
                            f"wrong armed {repository} binding",
                        )
                        with self.assertRaises(anchor.AnchorError):
                            anchor.terminal_wp_policy_v2_state(
                                fixture.root, candidate, correct
                            )

    def test_v2_rejects_intermediate_second_merge_and_non_direct_w1(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            w0 = fixture.commits["trust-wp"]
            preservation_floor, predecessor = fixture.advance_wp_v2_predecessor()
            with synthetic_v2_policy(w0, preservation_floor):
                cut = fixture.prepare_wp_root_cycle_v2(
                    preservation_floor, predecessor
                )
                r0 = str(cut["r0"])
                r1 = str(cut["r1"])
                pre = str(cut["pre"])
                r0_tree = git(fixture.root, "rev-parse", f"{r0}^{{tree}}")
                r1_tree = git(fixture.root, "rev-parse", f"{r1}^{{tree}}")

                intermediate = commit_tree(
                    fixture.root, r0_tree, [r0], "forbidden commit between R0 and R1"
                )
                delayed_r1 = commit_tree(
                    fixture.root, r1_tree, [intermediate], "delayed R1"
                )
                second_cut = commit_tree(
                    fixture.root, r1_tree, [r1], "forbidden R2 second cut"
                )
                merge_r1 = commit_tree(
                    fixture.root, r1_tree, [r0, pre], "forbidden merge R1"
                )
                for name, candidate in (
                    ("intermediate", delayed_r1),
                    ("second-cut", second_cut),
                    ("merge", merge_r1),
                ):
                    with self.subTest(name=name), self.assertRaises(anchor.AnchorError):
                        anchor.terminal_wp_policy_v2_state(
                            fixture.root, candidate, fixture.commits
                        )

                wp = fixture.checkout("trust-wp")
                extra_blob = write_blob(wp, b"unauthorized intermediate source\n")
                q_tree = derived_tree(
                    wp,
                    predecessor,
                    {"illicit-intermediate.txt": ("100644", extra_blob)},
                )
                q = commit_tree(wp, q_tree, [predecessor], "P to illicit Q")
                baseline_w1_tree = git(
                    wp, "rev-parse", f"{cut['w1']}^{{tree}}"
                )
                q_revert = commit_tree(
                    wp,
                    git(wp, "rev-parse", f"{predecessor}^{{tree}}"),
                    [q],
                    "revert illicit Q tree",
                )
                variants = {
                    "P-Q-W1": commit_tree(
                        wp, baseline_w1_tree, [q], "W1 after illicit Q"
                    ),
                    "move-revert": commit_tree(
                        wp, baseline_w1_tree, [q_revert], "W1 after Q revert"
                    ),
                    "merge-W1": commit_tree(
                        wp, baseline_w1_tree, [predecessor, q], "merged W1"
                    ),
                }
                for name, bad_w1 in variants.items():
                    with self.subTest(name=name):
                        bad_tree = derived_tree(
                            fixture.root,
                            r0,
                            {anchor.WP_ROOT_DELTA_PATH: ("160000", bad_w1)},
                        )
                        bad_r1 = commit_tree(
                            fixture.root, bad_tree, [r0], f"R1 with {name}"
                        )
                        bad_commits = dict(fixture.commits)
                        bad_commits["trust-wp"] = bad_w1
                        state = anchor.terminal_wp_policy_v2_state(
                            fixture.root, bad_r1, bad_commits
                        )
                        with self.assertRaisesRegex(
                            anchor.AnchorError, "exact raw sole parent P"
                        ):
                            anchor.derive_wp_root_anchor_v2(
                                fixture.root, bad_r1, bad_commits, state
                            )

    def test_v2_marker_lifecycle_and_floor_ancestry_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            w0 = fixture.commits["trust-wp"]
            preservation_floor, predecessor = fixture.advance_wp_v2_predecessor()
            with synthetic_v2_policy(w0, preservation_floor):
                cut = fixture.prepare_wp_root_cycle_v2(
                    preservation_floor, predecessor
                )
                pre = str(cut["pre"])
                r0 = str(cut["r0"])
                pre_parent = git(fixture.root, "show", "-s", "--format=%P", pre)

                deleted_tree = derived_tree(
                    fixture.root,
                    pre,
                    {anchor.TERMINAL_POLICY_V2_MARKER_PATH: None},
                )
                deleted = commit_tree(
                    fixture.root, deleted_tree, [pre], "delete v2 marker"
                )
                with self.assertRaisesRegex(anchor.AnchorError, "marker was deleted"):
                    anchor.terminal_wp_policy_v2_state(
                        fixture.root, deleted, dict(cut["root_bindings"])
                    )

                marker_blob = write_blob(
                    fixture.root, anchor.TERMINAL_POLICY_V2_PRE_MARKER
                )
                symlink_tree = derived_tree(
                    fixture.root,
                    pre_parent,
                    {
                        anchor.TERMINAL_POLICY_V2_MARKER_PATH: (
                            "120000",
                            marker_blob,
                        )
                    },
                )
                symlink = commit_tree(
                    fixture.root, symlink_tree, [pre_parent], "symlink v2 marker"
                )
                with self.assertRaisesRegex(anchor.AnchorError, "mode 100644"):
                    anchor.terminal_wp_policy_v2_state(
                        fixture.root, symlink, dict(cut["root_bindings"])
                    )

                wrong_predecessor = w0
                changed_marker = write_blob(
                    fixture.root,
                    anchor.render_terminal_policy_v2_armed(
                        wrong_predecessor, dict(cut["root_bindings"])
                    ),
                )
                changed_tree = derived_tree(
                    fixture.root,
                    r0,
                    {
                        anchor.TERMINAL_POLICY_V2_MARKER_PATH: (
                            "100644",
                            changed_marker,
                        )
                    },
                )
                changed = commit_tree(
                    fixture.root, changed_tree, [r0], "change armed v2 marker"
                )
                with self.assertRaises(anchor.AnchorError):
                    anchor.terminal_wp_policy_v2_state(
                        fixture.root, changed, dict(cut["root_bindings"])
                    )

                bad_r0_tree = derived_tree(
                    fixture.root,
                    pre,
                    {
                        anchor.RECEIPT_PATH: None,
                        anchor.TERMINAL_POLICY_V2_MARKER_PATH: (
                            "100644",
                            changed_marker,
                        ),
                    },
                )
                bad_r0 = commit_tree(
                    fixture.root, bad_r0_tree, [pre], "P predates preserved B"
                )
                with self.assertRaisesRegex(
                    anchor.AnchorError, "does not preserve published floor B"
                ):
                    anchor.terminal_wp_policy_v2_state(
                        fixture.root, bad_r0, dict(cut["root_bindings"])
                    )

    def test_v2_rejects_replacement_graft_shallow_and_alternate_authority(self) -> None:
        for mechanism in ("replacement", "graft", "shallow", "alternates"):
            with self.subTest(mechanism=mechanism), tempfile.TemporaryDirectory() as temporary:
                fixture = self.fixture(temporary)
                w0 = fixture.commits["trust-wp"]
                preservation_floor, predecessor = fixture.advance_wp_v2_predecessor()
                with synthetic_v2_policy(w0, preservation_floor):
                    cut = fixture.prepare_wp_root_cycle_v2(
                        preservation_floor, predecessor
                    )
                    r0 = str(cut["r0"])
                    r1 = str(cut["r1"])
                    if mechanism == "replacement":
                        git(fixture.root, "replace", r1, r0)
                        message = "forbidden replacement refs"
                    elif mechanism == "graft":
                        common_dir = Path(
                            git(
                                fixture.root,
                                "rev-parse",
                                "--path-format=absolute",
                                "--git-common-dir",
                            )
                        )
                        write(common_dir / "info" / "grafts", f"{r1} {r0}\n")
                        message = "forbidden legacy graft authority"
                    elif mechanism == "shallow":
                        shallow = Path(
                            git(
                                fixture.root,
                                "rev-parse",
                                "--path-format=absolute",
                                "--git-path",
                                "shallow",
                            )
                        )
                        write(shallow, f"{r1}\n")
                        message = "is shallow"
                    else:
                        common_dir = Path(
                            git(
                                fixture.root,
                                "rev-parse",
                                "--path-format=absolute",
                                "--git-common-dir",
                            )
                        )
                        alternates = common_dir / "objects" / "info" / "alternates"
                        wp_objects = Path(
                            git(
                                fixture.checkout("trust-wp"),
                                "rev-parse",
                                "--path-format=absolute",
                                "--git-path",
                                "objects",
                            )
                        )
                        write(alternates, f"{wp_objects}\n")
                        message = "forbidden repository-local alternate object authority"
                    with self.assertRaisesRegex(anchor.AnchorError, message):
                        anchor.terminal_wp_policy_v2_state(
                            fixture.root, r1, fixture.commits
                        )

    def test_v2_partial_clone_never_lazy_fetches_marker_authority(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            fixture = self.fixture(str(base / "fixture"))
            w0 = fixture.commits["trust-wp"]
            preservation_floor, predecessor = fixture.advance_wp_v2_predecessor()
            with synthetic_v2_policy(w0, preservation_floor):
                cut = fixture.prepare_wp_root_cycle_v2(
                    preservation_floor, predecessor
                )
                pre = str(cut["pre"])
                git(fixture.root, "update-ref", "refs/heads/v2-pre", pre)
                marker_oid = git(
                    fixture.root,
                    "rev-parse",
                    f"{pre}:{anchor.TERMINAL_POLICY_V2_MARKER_PATH}",
                )

                remote = base / "authority.git"
                subprocess.run(
                    ["git", "clone", "--bare", "-q", str(fixture.root), str(remote)],
                    check=True,
                )
                git(remote, "config", "uploadpack.allowFilter", "true")
                git(remote, "config", "uploadpack.allowAnySHA1InWant", "true")
                partial = base / "partial"
                subprocess.run(
                    [
                        "git",
                        "clone",
                        "--no-checkout",
                        "--filter=blob:none",
                        "--branch",
                        "v2-pre",
                        "-q",
                        remote.resolve().as_uri(),
                        str(partial),
                    ],
                    check=True,
                )
                before = missing_objects_without_lazy_fetch(partial)
                self.assertIn(marker_oid, before)

                sentinel = base / "upload-pack-invoked"
                upload_pack = base / "recording-upload-pack"
                write(
                    upload_pack,
                    "#!/bin/sh\n"
                    ': > "$GIT_UPLOAD_PACK_SENTINEL"\n'
                    'exec git-upload-pack "$@"\n',
                )
                upload_pack.chmod(0o755)
                git(partial, "config", "remote.origin.uploadpack", str(upload_pack))
                with mock.patch.dict(
                    os.environ,
                    {"GIT_UPLOAD_PACK_SENTINEL": str(sentinel)},
                    clear=False,
                ):
                    with self.assertRaisesRegex(
                        anchor.AnchorError,
                        rf"marker object {marker_oid} is missing",
                    ):
                        anchor.terminal_wp_policy_v2_state(
                            partial, pre, dict(cut["root_bindings"])
                        )
                self.assertFalse(sentinel.exists())
                self.assertEqual(missing_objects_without_lazy_fetch(partial), before)

    def test_checked_in_policy_marker_accepts_the_real_rebased_branch_landing(
        self,
    ) -> None:
        """Permanent regression for the merge that blocked every push.

        b387a4c0e5 brought in e42bba0a61, whose unmarked parent 2abd0cffd6 is
        itself a merge of a feature branch that was BEHIND on the TrustWP pin
        with an origin/main that had already advanced it.  The per-edge rule
        read that adoption as a side-branch move and refused the repository;
        the per-commit rule reads it as what it is -- a binding main had
        already published.  Nothing on that lineage reached the marked line.
        """
        root_commit = git(REPO_ROOT, "rev-parse", "HEAD")
        submodules = anchor.committed_submodules(REPO_ROOT, root_commit)
        commits = {
            name: commit for name, (_path, _url, commit) in submodules.items()
        }
        landing = "e42bba0a61bbd72d97ebf9e27205bb0c58febb15"
        inactive = "2abd0cffd6387a5ed1355c79dd2eb7fc3514fc84"
        main_side = "47eadec422fc895f4470425defd5785c1cf8a47f"
        branch_side = "b7d204a8703ed8c897df060a6c9a4c2f81aded04"

        landing_parents = git(REPO_ROOT, "show", "-s", "--format=%P", landing).split()
        self.assertEqual(
            landing_parents,
            [inactive, "7341ad628363ae4e77049359d73a018c1fcae702"],
        )
        self.assertEqual(
            git(REPO_ROOT, "ls-tree", inactive, "--", anchor.TERMINAL_POLICY_MARKER_PATH),
            "",
        )
        self.assertEqual(
            git(REPO_ROOT, "show", "-s", "--format=%P", inactive).split(),
            [main_side, branch_side],
        )

        def wp(commit: str) -> str:
            return git(REPO_ROOT, "rev-parse", f"{commit}:{anchor.WP_ROOT_DELTA_PATH}")

        # The edge the old rule refused really does change the binding ...
        self.assertNotEqual(wp(inactive), wp(branch_side))
        # ... and the value it lands on is exactly the one main had published.
        self.assertEqual(wp(inactive), wp(main_side))
        # The marked line keeps its own binding across the landing.
        self.assertEqual(wp(landing), wp(landing_parents[1]))
        self.assertNotEqual(wp(landing), wp(inactive))
        self.assertFalse(
            anchor.terminal_wp_policy_claimed(REPO_ROOT, root_commit, commits)
        )

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

    def test_terminal_policy_accepts_stale_first_parent_and_repeated_propagation(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            assert fixture.policy_parent is not None
            assert fixture.policy_activation is not None
            root = fixture.root
            wp = fixture.checkout("trust-wp")
            old_wp = fixture.commits["trust-wp"]
            old_wp_tree = git(wp, "rev-parse", f"{old_wp}^{{tree}}")
            active_wp = commit_tree(
                wp, old_wp_tree, [old_wp], "pre-activation active WP generation"
            )

            base = fixture.policy_parent
            active_tree = derived_tree(
                root,
                base,
                {anchor.WP_ROOT_DELTA_PATH: ("160000", active_wp)},
            )
            preactivation = commit_tree(
                root, active_tree, [base], "pre-activation root advances WP"
            )
            marker_oid = git(
                root,
                "rev-parse",
                f"{fixture.policy_activation}:{anchor.TERMINAL_POLICY_MARKER_PATH}",
            )
            marked_tree = derived_tree(
                root,
                preactivation,
                {anchor.TERMINAL_POLICY_MARKER_PATH: ("100644", marker_oid)},
            )
            activation = commit_tree(
                root, marked_tree, [preactivation], "unique policy activation"
            )
            marked = commit_tree(root, marked_tree, [activation], "marked parent")

            stale_one = commit_tree(
                root,
                git(root, "rev-parse", f"{base}^{{tree}}"),
                [base],
                "stable stale first parent",
            )
            merge_one = commit_tree(
                root,
                marked_tree,
                [stale_one, marked],
                "propagate marker from second parent",
            )
            stale_two = commit_tree(
                root,
                git(root, "rev-parse", f"{base}^{{tree}}"),
                [base],
                "second stable stale branch",
            )
            merge_two = commit_tree(
                root,
                marked_tree,
                [stale_two, merge_one],
                "repeat propagation with marked second parent",
            )
            commits = dict(fixture.commits)
            commits["trust-wp"] = active_wp
            self.assertFalse(
                anchor.terminal_wp_policy_claimed(root, merge_one, commits)
            )
            self.assertFalse(
                anchor.terminal_wp_policy_claimed(root, merge_two, commits)
            )

    def test_terminal_policy_accepts_same_origin_marked_parent_merge(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            assert fixture.policy_activation is not None
            root = fixture.root
            tree = git(
                root, "rev-parse", f"{fixture.policy_activation}^{{tree}}"
            )
            left = commit_tree(
                root, tree, [fixture.policy_activation], "marked left branch"
            )
            right = commit_tree(
                root, tree, [fixture.policy_activation], "marked right branch"
            )
            merge = commit_tree(
                root, tree, [left, right], "same-origin marked-parent merge"
            )
            self.assertFalse(
                anchor.terminal_wp_policy_claimed(
                    root, merge, fixture.commits
                )
            )

    def test_terminal_policy_rejects_ambiguous_origins_and_marker_mismatch(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            assert fixture.policy_parent is not None
            assert fixture.policy_activation is not None
            root = fixture.root
            tree = git(
                root, "rev-parse", f"{fixture.policy_activation}^{{tree}}"
            )
            second_origin = commit_tree(
                root, tree, [fixture.policy_parent], "independent marker origin"
            )
            ambiguous = commit_tree(
                root,
                tree,
                [fixture.policy_activation, second_origin],
                "merge independent marker origins",
            )
            with self.assertRaisesRegex(
                anchor.AnchorError, "one unique raw single-parent introduction"
            ):
                anchor.terminal_wp_policy_claimed(
                    root, ambiguous, fixture.commits
                )

        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            assert fixture.policy_parent is not None
            assert fixture.policy_activation is not None
            root = fixture.root
            invalid_oid = write_blob(
                root,
                b"trust.constellation.terminal-policy.v1\npolicy=wrong\n",
            )
            invalid_tree = derived_tree(
                root,
                fixture.policy_parent,
                {anchor.TERMINAL_POLICY_MARKER_PATH: ("100644", invalid_oid)},
            )
            invalid_parent = commit_tree(
                root,
                invalid_tree,
                [fixture.policy_parent],
                "malformed marker side parent",
            )
            marked_tree = git(
                root, "rev-parse", f"{fixture.policy_activation}^{{tree}}"
            )
            merge = commit_tree(
                root,
                marked_tree,
                [invalid_parent, fixture.policy_activation],
                "merge malformed marker lineage",
            )
            with self.assertRaisesRegex(
                anchor.AnchorError, "malformed marker state"
            ):
                anchor.terminal_wp_policy_claimed(root, merge, fixture.commits)

    def test_terminal_policy_rejects_inactive_wp_move_revert_and_import(self) -> None:
        for mutation in ("move", "move-revert", "import"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as temporary:
                fixture = self.fixture(temporary)
                assert fixture.policy_parent is not None
                assert fixture.policy_activation is not None
                root = fixture.root
                wp = fixture.checkout("trust-wp")
                old_wp = fixture.commits["trust-wp"]
                old_wp_tree = git(wp, "rev-parse", f"{old_wp}^{{tree}}")
                active_wp = commit_tree(
                    wp, old_wp_tree, [old_wp], "active WP generation"
                )
                side_wp = commit_tree(
                    wp, old_wp_tree, [old_wp], "inactive WP mutation"
                )

                base = fixture.policy_parent
                active_tree = derived_tree(
                    root,
                    base,
                    {anchor.WP_ROOT_DELTA_PATH: ("160000", active_wp)},
                )
                preactivation = commit_tree(
                    root, active_tree, [base], "pre-activation WP advance"
                )
                marker_oid = git(
                    root,
                    "rev-parse",
                    f"{fixture.policy_activation}:{anchor.TERMINAL_POLICY_MARKER_PATH}",
                )
                marked_tree = derived_tree(
                    root,
                    preactivation,
                    {anchor.TERMINAL_POLICY_MARKER_PATH: ("100644", marker_oid)},
                )
                activation = commit_tree(
                    root, marked_tree, [preactivation], "policy activation"
                )
                marked = commit_tree(root, marked_tree, [activation], "marked parent")

                side_tree = (
                    git(root, "rev-parse", f"{base}^{{tree}}")
                    if mutation == "import"
                    else derived_tree(
                        root,
                        base,
                        {anchor.WP_ROOT_DELTA_PATH: ("160000", side_wp)},
                    )
                )
                inactive = commit_tree(
                    root,
                    side_tree,
                    [base],
                    (
                        "inactive side preserves stale WP"
                        if mutation == "import"
                        else "inactive side moves WP"
                    ),
                )
                if mutation == "move-revert":
                    inactive = commit_tree(
                        root,
                        git(root, "rev-parse", f"{base}^{{tree}}"),
                        [inactive],
                        "inactive side reverts WP",
                    )
                merge_tree = (
                    derived_tree(
                        root,
                        marked,
                        {anchor.WP_ROOT_DELTA_PATH: ("160000", old_wp)},
                    )
                    if mutation == "import"
                    else marked_tree
                )
                merge = commit_tree(
                    root,
                    merge_tree,
                    [inactive, marked],
                    f"propagation {mutation}",
                )
                commits = dict(fixture.commits)
                commits["trust-wp"] = old_wp if mutation == "import" else active_wp
                expected = (
                    "did not retain every marked-parent TrustWP binding"
                    if mutation == "import"
                    else "minted a TrustWP gitlink no raw parent published"
                )
                with self.assertRaisesRegex(anchor.AnchorError, expected):
                    anchor.terminal_wp_policy_claimed(root, merge, commits)

    def test_terminal_policy_rejects_delete_readd_marker_lineage(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            assert fixture.policy_parent is not None
            assert fixture.policy_activation is not None
            root = fixture.root
            marked_tree = git(
                root, "rev-parse", f"{fixture.policy_activation}^{{tree}}"
            )
            deleted_tree = derived_tree(
                root,
                fixture.policy_activation,
                {anchor.TERMINAL_POLICY_MARKER_PATH: None},
            )
            deleted = commit_tree(
                root, deleted_tree, [fixture.policy_activation], "delete marker"
            )
            readded = commit_tree(root, marked_tree, [deleted], "readd marker")
            marked = commit_tree(
                root, marked_tree, [fixture.policy_activation], "marked sibling"
            )
            merge = commit_tree(
                root,
                marked_tree,
                [readded, marked],
                "merge delete-readd lineage",
            )
            with self.assertRaisesRegex(anchor.AnchorError, "deleted on a raw DAG edge"):
                anchor.terminal_wp_policy_claimed(root, merge, fixture.commits)

    def test_terminal_policy_accepts_inactive_branch_that_took_a_newer_main(self) -> None:
        """The shape that refused every push on 2026-08-30, in miniature.

        A feature branch forks while the root pins WP0, main advances the pin to
        WP1 in a pre-activation commit, the branch merges that newer main, and
        the whole branch is merged into the marked line long after activation.
        The branch therefore has TWO pre-activation frontiers whose bindings
        differ, and one of its internal edges changes the binding -- yet it
        publishes nothing new: the merge adopted a value main had already
        published.  The marked line retains its own binding throughout.
        """
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            assert fixture.policy_parent is not None
            root = fixture.root
            wp = fixture.checkout("trust-wp")
            wp0 = fixture.commits["trust-wp"]
            wp0_tree = git(wp, "rev-parse", f"{wp0}^{{tree}}")
            wp1 = commit_tree(wp, wp0_tree, [wp0], "main advances WP")
            wp2 = commit_tree(wp, wp0_tree, [wp1], "main advances WP again")

            fork = fixture.policy_parent
            fork_tree = git(root, "rev-parse", f"{fork}^{{tree}}")
            newer_main_tree = derived_tree(
                root, fork, {anchor.WP_ROOT_DELTA_PATH: ("160000", wp1)}
            )
            newer_main = commit_tree(
                root, newer_main_tree, [fork], "pre-activation main advances WP"
            )
            # The marked line carries a third binding, taken BEFORE activation
            # so that activation itself claims nothing: what the branch does
            # may not reach it either way.
            newest_main = commit_tree(
                root,
                derived_tree(
                    root, newer_main, {anchor.WP_ROOT_DELTA_PATH: ("160000", wp2)}
                ),
                [newer_main],
                "pre-activation main advances WP again",
            )
            activation_tree = derived_tree(
                root,
                newest_main,
                {
                    anchor.TERMINAL_POLICY_MARKER_PATH: (
                        "100644",
                        git(
                            root,
                            "rev-parse",
                            f"HEAD:{anchor.TERMINAL_POLICY_MARKER_PATH}",
                        ),
                    ),
                },
            )
            activation = commit_tree(
                root, activation_tree, [newest_main], "policy activation"
            )
            marked = commit_tree(root, activation_tree, [activation], "marked parent")

            branch = commit_tree(root, fork_tree, [fork], "feature work on the old pin")
            branch_merge = commit_tree(
                root,
                newer_main_tree,
                [newer_main, branch],
                "merge newer main into the feature branch",
            )
            merge = commit_tree(
                root,
                activation_tree,
                [branch_merge, marked],
                "land the branch on the marked line",
            )

            # The refused edge and the two differing frontiers are really there.
            self.assertNotEqual(
                git(root, "rev-parse", f"{branch_merge}:{anchor.WP_ROOT_DELTA_PATH}"),
                git(root, "rev-parse", f"{branch}:{anchor.WP_ROOT_DELTA_PATH}"),
            )
            self.assertNotEqual(
                git(root, "rev-parse", f"{fork}:{anchor.WP_ROOT_DELTA_PATH}"),
                git(root, "rev-parse", f"{newer_main}:{anchor.WP_ROOT_DELTA_PATH}"),
            )
            commits = dict(fixture.commits)
            commits["trust-wp"] = wp2
            self.assertFalse(
                anchor.terminal_wp_policy_claimed(root, merge, commits)
            )

    def test_terminal_policy_rejects_minted_and_unrooted_inactive_lineage(self) -> None:
        """The defect the inactive-lineage audit exists for, in both shapes.

        ``merge-mint`` is the case a per-EDGE rule caught only by accident: an
        exclusive merge whose binding equals NEITHER parent, i.e. a pin authored
        inside the merge resolution.  ``orphan`` is an inactive lineage with no
        ancestry in common with the pre-activation history at all.
        """
        for mutation in ("merge-mint", "orphan"):
            with (
                self.subTest(mutation=mutation),
                tempfile.TemporaryDirectory() as temporary,
            ):
                fixture = self.fixture(temporary)
                assert fixture.policy_parent is not None
                assert fixture.policy_activation is not None
                root = fixture.root
                wp = fixture.checkout("trust-wp")
                wp0 = fixture.commits["trust-wp"]
                wp0_tree = git(wp, "rev-parse", f"{wp0}^{{tree}}")
                wp1 = commit_tree(wp, wp0_tree, [wp0], "main advances WP")
                minted_wp = commit_tree(wp, wp0_tree, [wp0], "unpublished WP")

                fork = fixture.policy_parent
                fork_tree = git(root, "rev-parse", f"{fork}^{{tree}}")
                newer_main_tree = derived_tree(
                    root, fork, {anchor.WP_ROOT_DELTA_PATH: ("160000", wp1)}
                )
                newer_main = commit_tree(
                    root, newer_main_tree, [fork], "pre-activation main advances WP"
                )
                marker_oid = git(
                    root,
                    "rev-parse",
                    f"{fixture.policy_activation}:"
                    f"{anchor.TERMINAL_POLICY_MARKER_PATH}",
                )
                activation_tree = derived_tree(
                    root,
                    newer_main,
                    {
                        anchor.TERMINAL_POLICY_MARKER_PATH: ("100644", marker_oid),
                    },
                )
                activation = commit_tree(
                    root, activation_tree, [newer_main], "policy activation"
                )
                marked = commit_tree(
                    root, activation_tree, [activation], "marked parent"
                )

                if mutation == "merge-mint":
                    branch = commit_tree(
                        root, fork_tree, [fork], "feature work on the old pin"
                    )
                    minted_tree = derived_tree(
                        root,
                        fork,
                        {anchor.WP_ROOT_DELTA_PATH: ("160000", minted_wp)},
                    )
                    inactive = commit_tree(
                        root,
                        minted_tree,
                        [newer_main, branch],
                        "merge resolution mints a third WP binding",
                    )
                else:
                    inactive = commit_tree(
                        root, fork_tree, [], "unrooted inactive lineage"
                    )

                merge = commit_tree(
                    root,
                    activation_tree,
                    [inactive, marked],
                    f"land the {mutation} lineage on the marked line",
                )
                commits = dict(fixture.commits)
                commits["trust-wp"] = wp1
                with self.assertRaisesRegex(
                    anchor.AnchorError,
                    "minted a TrustWP gitlink no raw parent published",
                ):
                    anchor.terminal_wp_policy_claimed(root, merge, commits)

    def test_terminal_policy_partial_clone_never_lazy_fetches_authority(self) -> None:
        """A missing promised marker stays missing and no upload-pack is invoked."""
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            fixture = self.fixture(str(base / "fixture"))
            marker_oid = git(
                fixture.root,
                "rev-parse",
                f"HEAD:{anchor.TERMINAL_POLICY_MARKER_PATH}",
            )

            remote = base / "authority.git"
            subprocess.run(
                ["git", "clone", "--bare", "-q", str(fixture.root), str(remote)],
                check=True,
            )
            git(remote, "config", "uploadpack.allowFilter", "true")
            git(remote, "config", "uploadpack.allowAnySHA1InWant", "true")

            partial = base / "partial"
            subprocess.run(
                [
                    "git",
                    "clone",
                    "--no-checkout",
                    "--filter=blob:none",
                    "-q",
                    remote.resolve().as_uri(),
                    str(partial),
                ],
                check=True,
            )
            self.assertEqual(
                git(partial, "rev-parse", "--is-shallow-repository"), "false"
            )
            self.assertEqual(git(partial, "config", "--bool", "remote.origin.promisor"), "true")
            self.assertEqual(
                git(partial, "config", "remote.origin.partialclonefilter"),
                "blob:none",
            )

            before = missing_objects_without_lazy_fetch(partial)
            self.assertIn(marker_oid, before)

            sentinel = base / "upload-pack-invoked"
            upload_pack = base / "recording-upload-pack"
            write(
                upload_pack,
                "#!/bin/sh\n"
                ': > "$GIT_UPLOAD_PACK_SENTINEL"\n'
                'exec git-upload-pack "$@"\n',
            )
            upload_pack.chmod(0o755)
            git(partial, "config", "remote.origin.uploadpack", str(upload_pack))

            with mock.patch.dict(
                os.environ,
                {"GIT_UPLOAD_PACK_SENTINEL": str(sentinel)},
                clear=False,
            ):
                with self.assertRaisesRegex(
                    anchor.AnchorError,
                    rf"HEAD marker object {marker_oid} is missing",
                ):
                    anchor.terminal_wp_policy_claimed(
                        partial,
                        git(partial, "rev-parse", "HEAD"),
                        fixture.commits,
                    )

            self.assertFalse(sentinel.exists())
            self.assertEqual(missing_objects_without_lazy_fetch(partial), before)

            # Prove the recorder is on the exact lazy-fetch transport path: an
            # otherwise identical unprotected read invokes upload-pack and
            # materializes the promised marker object.
            lazy_environment = os.environ.copy()
            lazy_environment.pop("GIT_NO_LAZY_FETCH", None)
            lazy_environment["GIT_UPLOAD_PACK_SENTINEL"] = str(sentinel)
            control = subprocess.run(
                ["git", "-C", str(partial), "cat-file", "blob", marker_oid],
                check=False,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                env=lazy_environment,
            )
            self.assertEqual(control.returncode, 0, control.stderr.decode("utf-8", "replace"))
            self.assertTrue(sentinel.is_file())
            self.assertNotIn(marker_oid, missing_objects_without_lazy_fetch(partial))

    def test_terminal_policy_raw_walk_is_bounded_and_intro_is_unambiguous(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            root_commit = git(fixture.root, "rev-parse", "HEAD")
            with mock.patch.object(anchor, "TERMINAL_POLICY_HISTORY_LIMIT", 2):
                with self.assertRaisesRegex(anchor.AnchorError, "bounded limit"):
                    anchor.terminal_wp_policy_claimed(
                        fixture.root, root_commit, fixture.commits
                    )

        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            assert fixture.policy_parent is not None
            assert fixture.policy_activation is not None
            parent_tree = git(
                fixture.root, "rev-parse", f"{fixture.policy_parent}^{{tree}}"
            )
            side = commit_tree(
                fixture.root,
                parent_tree,
                [fixture.policy_parent],
                "pre-policy side parent",
            )
            activation_tree = git(
                fixture.root, "rev-parse", f"{fixture.policy_activation}^{{tree}}"
            )
            ambiguous = commit_tree(
                fixture.root,
                activation_tree,
                [fixture.policy_parent, side],
                "ambiguous merge marker introduction",
            )
            with self.assertRaisesRegex(anchor.AnchorError, "single-parent commit"):
                anchor.terminal_wp_policy_claimed(
                    fixture.root, ambiguous, fixture.commits
                )

    def test_terminal_policy_rejects_marked_parent_wp_divergence(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            assert fixture.policy_activation is not None
            wp = fixture.checkout("trust-wp")
            w0 = fixture.commits["trust-wp"]
            w0_tree = git(wp, "rev-parse", f"{w0}^{{tree}}")
            side_wp = commit_tree(wp, w0_tree, [w0], "side-branch WP move")

            git(
                fixture.root,
                "update-index",
                "--cacheinfo",
                f"160000,{side_wp},{anchor.WP_ROOT_DELTA_PATH}",
            )
            side_tree = git(fixture.root, "write-tree")
            git(fixture.root, "reset", "-q", "HEAD", "--", anchor.WP_ROOT_DELTA_PATH)
            side = commit_tree(
                fixture.root,
                side_tree,
                [fixture.policy_activation],
                "root side branch moves WP",
            )
            unchanged_tree = git(
                fixture.root, "rev-parse", f"{fixture.policy_activation}^{{tree}}"
            )
            merge = commit_tree(
                fixture.root,
                unchanged_tree,
                [fixture.policy_activation, side],
                "merge hides side-branch WP move from first-parent diff",
            )
            with self.assertRaisesRegex(
                anchor.AnchorError,
                "did not retain every marked-parent TrustWP binding",
            ):
                anchor.terminal_wp_policy_claimed(
                    fixture.root, merge, fixture.commits
                )

    def test_terminal_policy_marked_single_parent_wp_move_forces_terminal(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            assert fixture.policy_activation is not None
            root = fixture.root
            wp = fixture.checkout("trust-wp")
            old_wp = fixture.commits["trust-wp"]
            wp_tree = git(wp, "rev-parse", f"{old_wp}^{{tree}}")
            terminal_wp = commit_tree(
                wp, wp_tree, [old_wp], "terminal WP generation"
            )
            terminal_tree = derived_tree(
                root,
                fixture.policy_activation,
                {anchor.WP_ROOT_DELTA_PATH: ("160000", terminal_wp)},
            )
            terminal = commit_tree(
                root,
                terminal_tree,
                [fixture.policy_activation],
                "single-parent terminal WP move",
            )
            commits = dict(fixture.commits)
            commits["trust-wp"] = terminal_wp
            self.assertTrue(
                anchor.terminal_wp_policy_claimed(root, terminal, commits)
            )

    def test_wp_root_anchor_positive_shape_and_explicit_mode(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            preterminal = self.run_checker(fixture, "--print-receipt")
            self.assertEqual(preterminal.returncode, 0, preterminal.stderr)
            self.assertIsNone(json.loads(preterminal.stdout)["wp_trust_anchor"])

            root_anchor, root_terminal = fixture.prepare_wp_root_cycle(
                allowed_lock_delta=True
            )

            ordinary, ordinary_remote_calls = (
                self.run_terminal_checker_with_remote_witness(
                    fixture, "--print-receipt"
                )
            )
            self.assertEqual(ordinary.returncode, 0, ordinary.stderr)
            self.assertEqual(len(ordinary_remote_calls), 1)
            self.assertIsNotNone(json.loads(ordinary.stdout)["wp_trust_anchor"])

            missing_remote = self.run_checker(
                fixture, "--print-receipt", "--require-wp-trust-anchor"
            )
            self.assert_failure(missing_remote, "also requires --verify-remote")

            exclusions = fixture.receipt["exclusions"]
            assert isinstance(exclusions, list)
            with self.assertRaisesRegex(
                anchor.AnchorError, "requires remote-main verification"
            ):
                anchor.derive_receipt(
                    fixture.root,
                    root_terminal,
                    exclusions,
                    require_wp_trust_anchor=True,
                    verify_remote=False,
                )

            with mock.patch.object(anchor, "verify_remote_main") as api_remote:
                auto_receipt = anchor.derive_receipt(
                    fixture.root,
                    root_terminal,
                    exclusions,
                )
            api_remote.assert_called_once()
            self.assertIsNotNone(auto_receipt["wp_trust_anchor"])

            required, remote_calls = self.run_terminal_checker_with_remote_witness(
                fixture
            )
            self.assertEqual(required.returncode, 0, required.stderr)
            self.assertEqual(len(remote_calls), 1)
            self.assertEqual(remote_calls[0].kwargs["root_commit"], root_terminal)
            self.assertEqual(
                remote_calls[0].args[0]["trust-wp"], fixture.commits["trust-wp"]
            )
            receipt = json.loads(required.stdout)
            observed = receipt["wp_trust_anchor"]
            self.assertEqual(observed["anchor_commit"], root_anchor)
            self.assertEqual(observed["terminal_commit"], root_terminal)
            self.assertEqual(observed["anchor_gitlink"], fixture.anchor_wp)
            self.assertEqual(observed["terminal_gitlink"], fixture.commits["trust-wp"])
            self.assertEqual(observed["authority_commit"], fixture.commits["trust-wp"])
            self.assertEqual(
                git(
                    fixture.root,
                    "ls-tree",
                    root_terminal,
                    "--",
                    anchor.RECEIPT_PATH,
                    anchor.EXTERNAL_RECEIPT_PATH,
                ),
                "",
            )
            anchor.validate_external_receipt(receipt, require_wp_trust_anchor=True)

            wrong_mode = self.run_checker(fixture, "--require-wp-trust-anchor")
            self.assert_failure(
                wrong_mode,
                "--require-wp-trust-anchor requires --print-receipt or --write-receipt",
            )

            write(fixture.root / anchor.EXTERNAL_RECEIPT_PATH, required.stdout)
            commit_all(fixture.root, "illegally track external cycle evidence")
            tracked = self.run_checker(
                fixture,
                "--print-receipt",
                "--require-wp-trust-anchor",
                "--verify-remote",
            )
            self.assert_failure(tracked, "must remain external/untracked")

    def test_wp_terminal_auto_mode_rejects_each_stale_sibling_pin(self) -> None:
        for repository in ("ay", "clean", "trust-cg", "trust-ir"):
            with (
                self.subTest(repository=repository),
                tempfile.TemporaryDirectory() as temporary,
            ):
                fixture = self.fixture(temporary)
                # prepare_wp_root_cycle first removes the legacy receipt, so
                # predict the resulting R0 only after performing that same
                # committed transition explicitly here.
                (fixture.root / anchor.RECEIPT_PATH).unlink()
                root_anchor = commit_all(fixture.root, "R0 removes tracked receipt")
                rows = {
                    name: fixture.commits[name]
                    for name in ("ay", "clean", "trust-cg", "trust-ir")
                }
                rows[repository] = "f" * 40
                depends = (
                    f"clean main {rows['clean']}\n"
                    f"trust-ir main {rows['trust-ir']}\n"
                    f"trust-cg main {rows['trust-cg']}\n"
                    f"trust main {root_anchor}\n"
                    f"ay main {rows['ay']}\n"
                )
                # The helper accepts an already-established R0 when the
                # tracked legacy receipt has gone.
                fixture.prepare_wp_root_cycle(depends_content=depends)
                result = self.run_checker(fixture, "--print-receipt")
                self.assert_failure(result, f"root terminal binding for {repository}")

    def test_wp_w1_tree_policy_rejects_illicit_missing_and_new_lock_paths(self) -> None:
        cases = (
            ({"extra_wp_delta": True}, "disallowed=['illicit-terminal-file.txt']"),
            ({"omit_required_delta": "Cargo.toml"}, "missing_required=['Cargo.toml']"),
            ({"omit_required_delta": "VISION.md"}, "missing_required=['VISION.md']"),
            (
                {"omit_required_delta": anchor.WP_DEPENDS_PATH},
                "missing_required=['spikes/DEPENDS.lock']",
            ),
            ({"new_lock_delta": True}, "W0 tracked lock invented/Cargo.lock is not committed"),
        )
        for options, message in cases:
            with (
                self.subTest(options=options),
                tempfile.TemporaryDirectory() as temporary,
            ):
                fixture = self.fixture(temporary)
                fixture.prepare_wp_root_cycle(**options)
                result = self.run_checker(fixture, "--print-receipt")
                self.assert_failure(result, message)

    def test_wp_w1_cargo_and_vision_content_bindings_reject_stale_or_punctuated_claims(self) -> None:
        def replace_text(path: Path, old: str, new: str) -> None:
            text = path.read_text(encoding="utf-8")
            self.assertIn(old, text)
            write(path, text.replace(old, new, 1))

        def append_text(path: Path, addition: str) -> None:
            write(path, path.read_text(encoding="utf-8") + addition)

        mutations: tuple[tuple[str, Callable[[Fixture, Path], None], str], ...] = (
            (
                "cargo-stale-trust-ir",
                lambda fixture, wp: replace_text(
                    wp / "Cargo.toml", fixture.commits["trust-ir"], "f" * 40
                ),
                "active TrustIR Git revisions must all equal",
            ),
            (
                "cargo-punctuation-only",
                lambda _fixture, wp: replace_text(
                    wp / "Cargo.toml",
                    "# Current AY authority:",
                    "# Current AY authority :",
                ),
                "must use the exact case, punctuation, and two-field shape",
            ),
            (
                "cargo-stale-ay-marker",
                lambda fixture, wp: replace_text(
                    wp / "Cargo.toml", fixture.commits["ay"], "e" * 40
                ),
                "Current AY authority marker differs",
            ),
            (
                "cargo-case-lookalike",
                lambda _fixture, wp: append_text(
                    wp / "Cargo.toml",
                    "# current-ay-authority: version=9.9.9 commit="
                    + "d" * 40
                    + "\n",
                ),
                "no case/punctuation lookalikes",
            ),
            (
                "vision-stale-ay",
                lambda fixture, wp: replace_text(
                    wp / "VISION.md", fixture.commits["ay"][:8], "ffffffff"
                ),
                "VISION.md trust-wp-ay row must exactly bind",
            ),
            (
                "vision-punctuation-only",
                lambda fixture, wp: replace_text(
                    wp / "VISION.md",
                    f"`{fixture.commits['ay'][:8]}`",
                    fixture.commits["ay"][:8],
                ),
                "VISION.md trust-wp-ay row must exactly bind",
            ),
            (
                "vision-contradictory-suffix",
                lambda _fixture, wp: replace_text(
                    wp / "VISION.md",
                    "separation logic encoding |",
                    "separation logic encoding; AY v9.9.9 backend at "
                    "`deadbeef` on current `main` |",
                ),
                "VISION.md trust-wp-ay row must exactly bind",
            ),
        )
        for mutation, mutate, message in mutations:
            with (
                self.subTest(mutation=mutation),
                tempfile.TemporaryDirectory() as temporary,
            ):
                fixture = self.fixture(temporary)
                fixture.prepare_wp_root_cycle()
                fixture.amend_wp_terminal(lambda wp: mutate(fixture, wp))
                assert fixture.root_terminal is not None
                with self.assertRaisesRegex(anchor.AnchorError, message):
                    anchor.derive_wp_root_anchor(
                        fixture.root, fixture.root_terminal, fixture.commits
                    )

    def test_raw_root_tree_map_rejects_config_hidden_clean_gitlink_delta(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            root_anchor, root_terminal = fixture.prepare_wp_root_cycle(
                extra_root_gitlink="clean"
            )
            git(
                fixture.root,
                "config",
                "submodule.first-party/clean.ignore",
                "all",
            )
            self.assertEqual(
                git(
                    fixture.root,
                    "diff-tree",
                    "--no-commit-id",
                    "--name-only",
                    "-r",
                    root_anchor,
                    root_terminal,
                ).splitlines(),
                [anchor.WP_ROOT_DELTA_PATH],
            )
            # Unlike that config-sensitive legacy query, the two literal
            # committed entry maps must still expose the Clean gitlink.
            self.assertIn(
                "first-party/clean",
                anchor.changed_committed_tree_paths(
                    fixture.root, root_anchor, root_terminal
                ),
            )
            result = self.run_checker(fixture, "--print-receipt")
            self.assert_failure(result, "only tree delta")

    def test_harness_ordinary_lane_fails_closed_on_malformed_terminal_cut(self) -> None:
        manifest = (
            REPO_ROOT / "tests" / "run_trust_comprehensive_harness.sh"
        ).read_text(encoding="utf-8")
        self.assertIn(
            "fast.dependency-constellation|fast,push,release|supply-chain|true|never|"
            "scripts/check_dependency_cycle_anchor.py --push-context "
            "--derive-when-receipt-absent",
            manifest,
        )
        self.assertIn(
            'UNQUARANTINABLE_GATE_IDS = {"fast.dependency-constellation"}',
            manifest,
        )

        def run_harness(
            fixture: Fixture, revision: str | None = None
        ) -> subprocess.CompletedProcess[str]:
            selected = revision or git(fixture.root, "rev-parse", "HEAD")
            advertised_old = git(fixture.root, "rev-parse", f"{selected}^")
            environment = os.environ.copy()
            environment[anchor.PUSH_REFS_ENV] = (
                f"refs/heads/main {selected} refs/heads/main {advertised_old}"
            )
            return self.run_checker(
                fixture,
                "--push-context",
                "--derive-when-receipt-absent",
                env=environment,
            )

        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            fixture.prepare_wp_root_cycle(extra_root_delta=True)
            # This is the harness's exact ordinary invocation: no explicit
            # terminal flag exists to forget or quarantine.
            result = run_harness(fixture)
            self.assert_failure(result, "only tree delta")

        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            (fixture.root / anchor.RECEIPT_PATH).unlink()
            root_anchor = commit_all(fixture.root, "R0 removes tracked receipt")
            wrong_trust = git(fixture.root, "rev-parse", f"{root_anchor}^")
            depends = (
                f"clean main {fixture.commits['clean']}\n"
                f"trust-ir main {fixture.commits['trust-ir']}\n"
                f"trust-cg main {fixture.commits['trust-cg']}\n"
                f"trust main {wrong_trust}\n"
                f"ay main {fixture.commits['ay']}\n"
            )
            fixture.prepare_wp_root_cycle(depends_content=depends)
            wrong_row = run_harness(fixture)
            self.assert_failure(wrong_row, "Trust pin must exactly equal")

        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            fixture.prepare_wp_root_cycle()
            write(fixture.root / "post-terminal-R2", "must not downgrade evidence\n")
            commit_all(fixture.root, "R2 after a valid terminal cut")
            later_root = run_harness(fixture)
            self.assert_failure(later_root, "only tree delta")

        for later_root in (False, True):
            with (
                self.subTest(partial_w1_later_root=later_root),
                tempfile.TemporaryDirectory() as temporary,
            ):
                fixture = self.fixture(temporary)
                fixture.prepare_wp_root_cycle(partial_wp_delta=True)
                if later_root:
                    write(
                        fixture.root / "post-partial-W1-R2",
                        "partial W1 must remain a terminal claim\n",
                    )
                    commit_all(fixture.root, "R2 after malformed partial W1")
                partial = run_harness(fixture)
                self.assert_failure(
                    partial,
                    "only tree delta" if later_root else "missing_required",
                )

    def test_push_context_terminal_judgement_ignores_stale_preterminal_head(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            root_anchor, root_terminal = fixture.prepare_wp_root_cycle(
                partial_wp_delta=True
            )
            git(fixture.root, "reset", "--hard", "-q", root_anchor)
            environment = os.environ.copy()
            environment[anchor.PUSH_REFS_ENV] = (
                f"refs/heads/main {root_terminal} refs/heads/main {root_anchor}"
            )
            result = self.run_checker(
                fixture,
                "--push-context",
                "--derive-when-receipt-absent",
                env=environment,
            )
            self.assert_failure(result, "missing_required")

        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            root_anchor, root_terminal = fixture.prepare_wp_root_cycle()
            git(fixture.root, "reset", "--hard", "-q", root_anchor)
            pushed = (
                f"refs/heads/main {root_terminal} refs/heads/main {root_anchor}"
            )
            with mock.patch.dict(
                os.environ, {anchor.PUSH_REFS_ENV: pushed}, clear=False
            ):
                result, remote_calls = self.run_terminal_checker_with_remote_witness(
                    fixture,
                    "--push-context",
                    "--derive-when-receipt-absent",
                )
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("immutable terminal policy", result.stdout)
            self.assertEqual(len(remote_calls), 1)
            self.assertEqual(remote_calls[0].kwargs["root_commit"], root_terminal)

    def test_wp_depends_lock_shape_and_committed_blob_fail_closed(self) -> None:
        valid_rows = lambda fixture, trust_row: (
            f"clean main {fixture.commits['clean']}\n"
            f"trust-ir main {fixture.commits['trust-ir']}\n"
            f"trust-cg main {fixture.commits['trust-cg']}\n"
            f"{trust_row}\n"
            f"ay main {fixture.commits['ay']}\n"
        )
        cases = {
            "missing-trust": lambda fixture, root: valid_rows(fixture, "").replace("\n\n", "\n"),
            "duplicate-trust": lambda fixture, root: valid_rows(
                fixture, f"trust main {root}\ntrust main {root}"
            ),
            "wrong-branch": lambda fixture, root: valid_rows(fixture, f"trust trunk {root}"),
            "short-sha": lambda fixture, root: valid_rows(fixture, "trust main abc"),
            "unknown-row": lambda fixture, root: valid_rows(
                fixture, f"trust main {root}\nunknown main {'1' * 40}"
            ),
        }
        for mutation, content in cases.items():
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as temporary:
                fixture = self.fixture(temporary)
                root = git(fixture.root, "rev-parse", "HEAD")
                fixture.prepare_wp_root_cycle(depends_content=content(fixture, root))
                result = self.run_checker(
                    fixture,
                    "--print-receipt",
                    "--require-wp-trust-anchor",
                    "--verify-remote",
                )
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("spikes/DEPENDS.lock", result.stderr)

        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            fixture.prepare_wp_root_cycle()

            def symlink_depends(wp: Path) -> None:
                target = wp / anchor.WP_DEPENDS_PATH
                target.unlink()
                os.symlink("missing-DEPENDS.lock", target)

            fixture.amend_wp_terminal(symlink_depends)
            result = self.run_checker(
                fixture,
                "--print-receipt",
                "--require-wp-trust-anchor",
                "--verify-remote",
            )
            self.assert_failure(result, "must be a regular committed blob")

    def test_wp_root_anchor_rejects_wrong_parent_merge_grandchild_and_extra_delta(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            wrong_anchor = git(fixture.root, "rev-parse", "HEAD^")
            rows = (
                f"clean main {fixture.commits['clean']}\n"
                f"trust-ir main {fixture.commits['trust-ir']}\n"
                f"trust-cg main {fixture.commits['trust-cg']}\n"
                f"trust main {wrong_anchor}\n"
                f"ay main {fixture.commits['ay']}\n"
            )
            fixture.prepare_wp_root_cycle(depends_content=rows)
            self.assert_failure(
                self.run_checker(
                    fixture,
                    "--print-receipt",
                    "--require-wp-trust-anchor",
                    "--verify-remote",
                ),
                "Trust pin must exactly equal",
            )

        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            fixture.prepare_wp_root_cycle(extra_root_delta=True)
            self.assert_failure(
                self.run_checker(
                    fixture,
                    "--print-receipt",
                    "--require-wp-trust-anchor",
                    "--verify-remote",
                ),
                "only tree delta",
            )

        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            fixture.prepare_wp_root_cycle(wp_intermediate=True)
            self.assert_failure(
                self.run_checker(
                    fixture,
                    "--print-receipt",
                    "--require-wp-trust-anchor",
                    "--verify-remote",
                ),
                "TrustWP W1 must be the root anchor gitlink W0's direct single-parent child",
            )

        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            fixture.prepare_wp_root_cycle()
            write(fixture.root / "grandchild", "not R1\n")
            commit_all(fixture.root, "grandchild after cycle break")
            self.assert_failure(
                self.run_checker(
                    fixture,
                    "--print-receipt",
                    "--require-wp-trust-anchor",
                    "--verify-remote",
                ),
                "only tree delta",
            )

        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            root_anchor, root_terminal = fixture.prepare_wp_root_cycle()
            tree = git(fixture.root, "rev-parse", f"{root_terminal}^{{tree}}")
            merge = subprocess.run(
                [
                    "git",
                    "-C",
                    str(fixture.root),
                    "commit-tree",
                    tree,
                    "-p",
                    root_anchor,
                    "-p",
                    root_terminal,
                ],
                input="synthetic merge terminal\n",
                check=True,
                text=True,
                stdout=subprocess.PIPE,
            ).stdout.strip()
            with self.assertRaisesRegex(anchor.AnchorError, "exactly one raw parent"):
                anchor.derive_wp_root_anchor(fixture.root, merge, fixture.commits)

        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            (fixture.root / anchor.RECEIPT_PATH).unlink()
            root_anchor = commit_all(fixture.root, "R0 removes tracked receipt")
            wp = fixture.checkout("trust-wp")
            w0 = fixture.commits["trust-wp"]
            write(
                wp / anchor.WP_DEPENDS_PATH,
                f"clean main {fixture.commits['clean']}\n"
                f"trust-ir main {fixture.commits['trust-ir']}\n"
                f"trust-cg main {fixture.commits['trust-cg']}\n"
                f"trust main {root_anchor}\n"
                f"ay main {fixture.commits['ay']}\n",
            )
            git(wp, "add", anchor.WP_DEPENDS_PATH)
            wp_tree = git(wp, "write-tree")
            w0_tree = git(wp, "rev-parse", f"{w0}^{{tree}}")

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

            side = commit_tree(wp, w0_tree, [w0], "synthetic WP side parent")
            merge_wp = commit_tree(
                wp, wp_tree, [w0, side], "synthetic merge TrustWP terminal"
            )
            git(
                fixture.root,
                "update-index",
                "--cacheinfo",
                f"160000,{merge_wp},{anchor.WP_ROOT_DELTA_PATH}",
            )
            root_tree = git(fixture.root, "write-tree")
            root_terminal = commit_tree(
                fixture.root, root_tree, [root_anchor], "synthetic R1"
            )
            commits = dict(fixture.commits)
            commits["trust-wp"] = merge_wp
            with self.assertRaisesRegex(anchor.AnchorError, "terminal TrustWP W1"):
                anchor.derive_wp_root_anchor(
                    fixture.root, root_terminal, commits
                )

    def test_wp_root_anchor_rejects_replacements_grafts_and_shallow_history(self) -> None:
        for mechanism in ("replacement", "graft", "shallow"):
            for repository in ("trust", "trust-wp"):
                with (
                    self.subTest(mechanism=mechanism, repository=repository),
                    tempfile.TemporaryDirectory() as temporary,
                ):
                    fixture = self.fixture(temporary)
                    fixture.prepare_wp_root_cycle()
                    assert fixture.root_anchor is not None
                    assert fixture.root_terminal is not None
                    assert fixture.anchor_wp is not None
                    checkout = (
                        fixture.root
                        if repository == "trust"
                        else fixture.checkout("trust-wp")
                    )
                    terminal = (
                        fixture.root_terminal
                        if repository == "trust"
                        else fixture.commits["trust-wp"]
                    )
                    parent = (
                        fixture.root_anchor
                        if repository == "trust"
                        else fixture.anchor_wp
                    )

                    if mechanism == "replacement":
                        git(checkout, "replace", terminal, parent)
                        # The raw reader itself must still see the literal
                        # terminal object rather than Git's replacement view.
                        self.assertEqual(
                            anchor.raw_commit_parents(
                                checkout, terminal, f"{repository} replacement probe"
                            ),
                            [parent],
                        )
                        message = "forbidden replacement refs"
                    elif mechanism == "graft":
                        common_dir = Path(
                            git(
                                checkout,
                                "rev-parse",
                                "--path-format=absolute",
                                "--git-common-dir",
                            )
                        )
                        write(common_dir / "info" / "grafts", f"{terminal} {parent}\n")
                        message = "forbidden legacy graft authority"
                    else:
                        shallow_path = Path(
                            git(
                                checkout,
                                "rev-parse",
                                "--path-format=absolute",
                                "--git-path",
                                "shallow",
                            )
                        )
                        write(shallow_path, f"{terminal}\n")
                        message = "is shallow"

                    with self.assertRaisesRegex(anchor.AnchorError, message):
                        anchor.derive_wp_root_anchor(
                            fixture.root,
                            fixture.root_terminal,
                            fixture.commits,
                        )

    def test_wp_root_anchor_binds_terminal_gitlink_and_both_remote_mains(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            fixture.prepare_wp_root_cycle()

            mismatched = dict(fixture.commits)
            assert fixture.anchor_wp is not None
            mismatched["trust-wp"] = fixture.anchor_wp
            with self.assertRaisesRegex(anchor.AnchorError, "differs from the terminal repository binding"):
                assert fixture.root_terminal is not None
                anchor.derive_wp_root_anchor(
                    fixture.root, fixture.root_terminal, mismatched
                )

            assert fixture.root_terminal is not None
            with mock.patch.object(anchor, "verify_one_remote_main") as verify_one:
                anchor.verify_remote_main(
                    fixture.commits, root_commit=fixture.root_terminal
                )
            expected_calls = [
                mock.call(name, anchor.SUBMODULES[name][1], fixture.commits[name])
                for name in sorted(anchor.SUBMODULES)
            ] + [mock.call("trust", anchor.ROOT_URL, fixture.root_terminal)]
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

    def test_remote_main_probe_environment_and_exact_row_fail_closed(self) -> None:
        commit = "1" * 40
        completed = subprocess.CompletedProcess(
            ["git", "ls-remote"],
            0,
            stdout=f"{commit}\trefs/heads/main\n".encode("ascii"),
            stderr=b"",
        )
        hostile = {
            "GIT_CONFIG": "/tmp/attacker-config",
            "GIT_CONFIG_COUNT": "1",
            "GIT_CONFIG_KEY_0": "url.file:///tmp/attacker.insteadOf",
            "GIT_CONFIG_VALUE_0": anchor.ROOT_URL,
            "GIT_CONFIG_PARAMETERS": "'url.file:///tmp/attacker.insteadOf'='x'",
            "GIT_DIR": "/tmp/attacker.git",
            "GIT_CURL_VERBOSE": "1",
            "GIT_EXEC_PATH": "/tmp/attacker-git-helpers",
            "GIT_SSL_NO_VERIFY": "1",
            "GIT_TRACE_CURL": "1",
            "SSL_CERT_FILE": "/tmp/attacker-ca.pem",
        }
        with mock.patch.dict(os.environ, hostile, clear=False):
            with mock.patch.object(
                anchor.subprocess, "run", return_value=completed
            ) as run:
                anchor.verify_one_remote_main("trust", anchor.ROOT_URL, commit)
        _args, kwargs = run.call_args
        environment = kwargs["env"]
        self.assertEqual(environment["GIT_CONFIG_NOSYSTEM"], "1")
        self.assertEqual(environment["GIT_CONFIG_GLOBAL"], os.devnull)
        self.assertEqual(environment["GIT_CONFIG_SYSTEM"], os.devnull)
        self.assertEqual(
            Path(environment["GIT_CEILING_DIRECTORIES"]),
            Path(kwargs["cwd"]).resolve(),
        )
        for key in hostile:
            self.assertNotIn(key, environment)
        self.assertTrue(Path(kwargs["cwd"]).name.startswith("trust-remote-main-"))
        self.assertEqual(
            run.call_args.args[0],
            [
                "git",
                "ls-remote",
                "--exit-code",
                anchor.ROOT_URL,
                "refs/heads/main",
            ],
        )

        stale = subprocess.CompletedProcess(
            ["git", "ls-remote"],
            0,
            stdout=f"{'2' * 40}\trefs/heads/main\n".encode("ascii"),
            stderr=b"",
        )
        with mock.patch.object(anchor.subprocess, "run", return_value=stale):
            with self.assertRaisesRegex(anchor.AnchorError, "not exactly remote main"):
                anchor.verify_one_remote_main("trust", anchor.ROOT_URL, commit)

    def test_remote_main_private_credential_retry_is_host_scoped_and_redacted(self) -> None:
        commit = "1" * 40
        unauthenticated = subprocess.CompletedProcess(
            ["git", "ls-remote"], 128, stdout=b"", stderr=b"authentication required"
        )
        success = subprocess.CompletedProcess(
            ["git", "ls-remote"],
            0,
            stdout=f"{commit}\trefs/heads/main\n".encode("ascii"),
            stderr=b"",
        )
        header = "Authorization: Basic dXNlcjpzZWNyZXQ="
        with mock.patch.object(
            anchor, "github_authorization_header", return_value=header
        ) as credential:
            with mock.patch.object(
                anchor.subprocess, "run", side_effect=[unauthenticated, success]
            ) as run:
                anchor.verify_one_remote_main("trust", anchor.ROOT_URL, commit)
        self.assertEqual(credential.call_count, 1)
        self.assertEqual(run.call_count, 2)
        first, second = run.call_args_list
        self.assertNotIn("GIT_CONFIG_COUNT", first.kwargs["env"])
        self.assertEqual(second.kwargs["env"]["GIT_CONFIG_COUNT"], "1")
        self.assertEqual(
            second.kwargs["env"]["GIT_CONFIG_KEY_0"],
            "http.https://github.com/.extraHeader",
        )
        self.assertEqual(second.kwargs["env"]["GIT_CONFIG_VALUE_0"], header)
        self.assertNotIn(header, " ".join(second.args[0]))

        leaked = subprocess.CompletedProcess(
            ["git", "ls-remote"],
            128,
            stdout=b"",
            stderr=f"transport echoed {header} dXNlcjpzZWNyZXQ=\n".encode("ascii"),
        )
        with mock.patch.object(
            anchor, "github_authorization_header", return_value=header
        ):
            with mock.patch.object(
                anchor.subprocess, "run", side_effect=[unauthenticated, leaked]
            ):
                with self.assertRaises(anchor.AnchorError) as raised:
                    anchor.verify_one_remote_main("trust", anchor.ROOT_URL, commit)
        diagnostic = str(raised.exception)
        self.assertNotIn(header, diagnostic)
        self.assertNotIn("dXNlcjpzZWNyZXQ=", diagnostic)
        self.assertIn("<redacted>", diagnostic)

    def test_github_credential_protocol_rejects_duplicate_or_conflicting_sources(self) -> None:
        cases = {
            "duplicate": (
                b"protocol=https\nhost=github.com\nusername=user\n"
                b"password=one\npassword=two\n"
            ),
            "conflicting": (
                b"protocol=https\nhost=github.com\nusername=user\n"
                b"password=secret\nauthtype=Bearer\ncredential=token\n"
            ),
        }
        for mutation, output in cases.items():
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as temporary:
                completed = subprocess.CompletedProcess(
                    ["git", "credential", "fill"],
                    0,
                    stdout=output,
                    stderr=b"",
                )
                with mock.patch.object(anchor.subprocess, "run", return_value=completed):
                    with self.assertRaises(anchor.AnchorError):
                        anchor.github_authorization_header(
                            anchor.ROOT_URL, Path(temporary)
                        )


if __name__ == "__main__":
    unittest.main()
