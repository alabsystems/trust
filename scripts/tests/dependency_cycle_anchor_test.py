#!/usr/bin/env python3
"""Mutation tests for the committed first-party constellation validator.

Fixtures contain real Cargo manifests, lockfiles, Lake manifests, proof identity,
Git history, and nine committed gitlinks.  No state-file stand-in is used.
"""

from __future__ import annotations

import copy
import importlib.util
import json
import os
import subprocess
import sys
import tempfile
import unittest
from dataclasses import dataclass
from pathlib import Path
from typing import Callable


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


@dataclass
class Fixture:
    root: Path
    remotes: dict[str, Path]
    commits: dict[str, str]
    ancestors: dict[str, str]
    receipt: dict[str, object]

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
    return Fixture(root, remotes, commits, ancestors, receipt)


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

    def run_checker(self, fixture: Fixture, *arguments: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [sys.executable, str(SCRIPT), "--repo-root", str(fixture.root), *arguments],
            check=False,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )

    def assert_failure(self, result: subprocess.CompletedProcess[str], needle: str) -> None:
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn(needle, result.stderr)

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

    def test_receipt_regeneration_binds_the_staged_future_tree(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(temporary)
            clean = fixture.checkout("clean")
            write(clean / "README.md", "new terminal generation\n")
            new_clean = commit_all(clean, "advance clean terminal")
            git(fixture.root, "add", anchor.SUBMODULES["clean"][0])

            generated = self.run_checker(fixture, "--write-receipt")
            self.assertEqual(generated.returncode, 0, generated.stderr)
            receipt = json.loads(
                (fixture.root / anchor.RECEIPT_PATH).read_text(encoding="utf-8")
            )
            self.assertEqual(
                receipt["repositories"]["clean"]["commit"], new_clean
            )
            clean_binding = next(
                row
                for row in receipt["root_bindings"]
                if row["repository"] == "clean"
            )
            self.assertEqual(clean_binding["commit"], new_clean)
            self.assertTrue(
                all(
                    row["terminal"] == new_clean
                    for row in receipt["anchors"]
                    if row["dependency"] == "clean"
                )
            )

            git(fixture.root, "add", anchor.RECEIPT_PATH)
            git(fixture.root, "commit", "-qm", "publish regenerated receipt")
            checked = self.run_checker(fixture)
            self.assertEqual(checked.returncode, 0, checked.stderr)


if __name__ == "__main__":
    unittest.main()
