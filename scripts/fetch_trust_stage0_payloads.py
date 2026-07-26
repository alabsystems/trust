#!/usr/bin/env python3
"""Materialize Trust stage0 payloads from declared metadata only.

This helper is intentionally conservative:

* It reads the checksum-pinned archive list from ``src/stage0``.
* It reads candidate ``xz_url`` values from checked-in channel manifests.
* It never invents a URL or falls back to upstream Rust metadata.
* It writes payloads only with ``--fetch`` and only after the downloaded bytes
  match the SHA-256 pinned in ``src/stage0``.

When the checkout only declares repo-local ``file://{trust-root}/...`` URLs and
the archive payloads are missing, this command reports that no fetchable source
exists. That is a real release-evidence blocker, not a condition to bypass.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass, field
from pathlib import Path
from urllib.error import URLError
from urllib.parse import unquote, urlparse
from urllib.request import urlopen


def ensure_tomllib() -> object:
    try:
        import tomllib

        return tomllib
    except ModuleNotFoundError:
        try:
            import tomli as tomllib  # type: ignore[import-not-found]

            return tomllib
        except ModuleNotFoundError:
            pass

    if os.environ.get("TRUST_STAGE0_FETCH_PYTHON_REEXEC") != "1":
        for name in ("python3.14", "python3.13", "python3.12", "python3.11"):
            candidate = shutil.which(name)
            if not candidate or Path(candidate) == Path(sys.executable):
                continue
            probe = subprocess.run(
                [candidate, "-c", "import tomllib"],
                check=False,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
            )
            if probe.returncode == 0:
                os.environ["TRUST_STAGE0_FETCH_PYTHON_REEXEC"] = "1"
                os.execv(candidate, [candidate, *sys.argv])

    print(
        "error: Python 3.11+ or the 'tomli' package is required to parse Trust stage0 manifests",
        file=sys.stderr,
    )
    sys.exit(2)


tomllib = ensure_tomllib()


TRUST_ROOT_TOKEN = "{trust-root}"
ARCHIVE_SUFFIXES = (".tar", ".tar.gz", ".tar.xz")


@dataclass(frozen=True)
class Stage0Entry:
    relative_path: str
    expected_sha256: str


@dataclass
class DeclaredSource:
    url: str
    manifest: str
    manifest_sha256: str | None
    status: str


@dataclass
class PayloadReport:
    relative_path: str
    expected_sha256: str
    target_path: str | None
    status: str
    existing_sha256: str | None = None
    declared_sources: list[DeclaredSource] = field(default_factory=list)
    selected_url: str | None = None
    message: str | None = None


def repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def stage0_values(path: Path) -> dict[str, str]:
    values: dict[str, str] = {}
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, value = line.split("=", 1)
        values[key.strip()] = value.strip()
    return values


def is_archive_path(value: str) -> bool:
    return value.startswith("dist/") and value.endswith(ARCHIVE_SUFFIXES)


def stage0_entries(values: dict[str, str]) -> list[Stage0Entry]:
    return [
        Stage0Entry(relative_path=key, expected_sha256=value)
        for key, value in sorted(values.items())
        if is_archive_path(key)
    ]


def resolve_file_url(value: str, root: Path) -> Path | None:
    if not value.startswith("file://"):
        return None
    raw = unquote(value.removeprefix("file://"))
    raw = raw.replace(TRUST_ROOT_TOKEN, str(root))
    raw = raw.replace("$PWD", str(root))
    if raw.startswith("localhost/"):
        raw = "/" + raw.removeprefix("localhost/")
    return Path(raw)


def default_dist_root(root: Path, values: dict[str, str]) -> Path | None:
    dist_server = values.get("dist_server", "")
    if not dist_server:
        return None
    return resolve_file_url(dist_server, root)


def default_manifests(root: Path, dist_root: Path | None, values: dict[str, str]) -> list[Path]:
    manifests: list[Path] = []
    if dist_root is not None:
        manifests.append(dist_root / "dist" / "channel-rust-trust.toml")
        date = values.get("compiler_date") or values.get("rustfmt_date")
        if date:
            manifests.append(dist_root / "dist" / date / "channel-rust-trust.toml")
        manifests.extend(sorted((dist_root / "dist").glob("*/channel-rust-trust.toml")))
    manifests.append(root / "bootstrap" / "trust-stage0" / "dist" / "channel-rust-trust.toml")
    return sorted(dict.fromkeys(manifests))


@dataclass
class InternalRelease:
    """The seed ledger's `[release]` block: where the admitted-internal seed
    payloads actually live (a private GitHub release). Authenticated `gh`
    access to it is a DECLARED source — the ledger names it — so fetching from
    it invents nothing; every byte is still verified against the src/stage0
    SHA-256 pin before installation."""

    repo: str
    tag: str
    scope: str


def read_internal_release(root: Path) -> InternalRelease | None:
    ledger = root / "bootstrap" / "trust-stage0" / "seed-ledger.toml"
    if not ledger.is_file():
        return None
    try:
        data = tomllib.loads(ledger.read_text(encoding="utf-8"))
    except Exception:
        return None
    release = data.get("release")
    scope = data.get("scope")
    if not isinstance(release, dict) or not isinstance(scope, str):
        return None
    repo = release.get("repo")
    tag = release.get("tag")
    if not isinstance(repo, str) or not isinstance(tag, str) or not repo or not tag:
        return None
    return InternalRelease(repo=repo, tag=tag, scope=scope)


def gh_available() -> bool:
    gh = shutil.which("gh")
    if gh is None:
        return False
    try:
        probe = subprocess.run(
            [gh, "auth", "status"], capture_output=True, timeout=30, check=False
        )
    except (OSError, subprocess.TimeoutExpired):
        return False
    return probe.returncode == 0


def gh_release_fetch(release: InternalRelease, asset: str, destination: Path, timeout: float) -> None:
    """Download ONE named asset from the ledger's internal release into
    `destination` via authenticated `gh`. The caller verifies the src/stage0
    checksum before accepting the bytes (identical posture to every other
    lane)."""
    destination.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=str(destination.parent)) as tmp_dir:
        subprocess.run(
            [
                "gh",
                "release",
                "download",
                release.tag,
                "-R",
                release.repo,
                "--pattern",
                asset,
                "-D",
                tmp_dir,
            ],
            check=True,
            capture_output=True,
            timeout=timeout,
        )
        fetched = Path(tmp_dir) / asset
        if not fetched.is_file():
            raise FileNotFoundError(f"gh release download produced no {asset}")
        os.replace(fetched, destination)


def walk_manifest_targets(value: object) -> list[dict[str, object]]:
    targets: list[dict[str, object]] = []
    if isinstance(value, dict):
        if "xz_url" in value:
            targets.append(value)
        for child in value.values():
            targets.extend(walk_manifest_targets(child))
    return targets


def declared_sources(manifests: list[Path], root: Path) -> dict[str, list[DeclaredSource]]:
    sources: dict[str, list[DeclaredSource]] = {}
    for manifest in manifests:
        if not manifest.is_file():
            continue
        try:
            data = tomllib.loads(manifest.read_text(encoding="utf-8"))
        except Exception as exc:  # TOML parser types differ across implementations.
            sources.setdefault("<manifest-error>", []).append(
                DeclaredSource(
                    url=str(manifest),
                    manifest=str(manifest),
                    manifest_sha256=None,
                    status=f"unreadable: {exc}",
                )
            )
            continue
        for target in walk_manifest_targets(data):
            url = target.get("xz_url")
            if not isinstance(url, str) or not url:
                continue
            digest = target.get("xz_hash")
            parsed = urlparse(url)
            filename = Path(unquote(parsed.path)).name
            if not filename:
                continue
            source_status = "declared"
            if parsed.scheme == "file":
                local = resolve_file_url(url, root)
                if local is None:
                    source_status = "unresolved-file-url"
                elif not local.is_file():
                    source_status = "missing-local-file"
                else:
                    source_status = "local-file"
            elif parsed.scheme != "https":
                source_status = f"unsupported-scheme:{parsed.scheme or '<none>'}"
            sources.setdefault(filename, []).append(
                DeclaredSource(
                    url=url,
                    manifest=str(manifest),
                    manifest_sha256=digest if isinstance(digest, str) else None,
                    status=source_status,
                )
            )
    return sources


def source_is_fetchable(source: DeclaredSource) -> bool:
    parsed = urlparse(source.url)
    return parsed.scheme == "https" or source.status == "local-file"


def copy_or_fetch(source: DeclaredSource, root: Path, destination: Path, timeout: float) -> None:
    parsed = urlparse(source.url)
    destination.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        prefix=f".{destination.name}.", suffix=".tmp", dir=str(destination.parent), delete=False
    ) as tmp:
        tmp_path = Path(tmp.name)
        try:
            if parsed.scheme == "file":
                local = resolve_file_url(source.url, root)
                if local is None or not local.is_file():
                    raise FileNotFoundError(source.url)
                with local.open("rb") as handle:
                    shutil.copyfileobj(handle, tmp)
            elif parsed.scheme == "https":
                with urlopen(source.url, timeout=timeout) as response:  # nosec: URL must be declared.
                    shutil.copyfileobj(response, tmp)
            else:
                raise ValueError(f"unsupported URL scheme: {parsed.scheme or '<none>'}")
            tmp.flush()
            os.fsync(tmp.fileno())
        except Exception:
            tmp_path.unlink(missing_ok=True)
            raise
    os.replace(tmp_path, destination)


def evaluate_payload(
    entry: Stage0Entry,
    *,
    root: Path,
    dist_root: Path | None,
    sources_by_name: dict[str, list[DeclaredSource]],
    fetch: bool,
    timeout: float,
) -> PayloadReport:
    target = dist_root / entry.relative_path if dist_root is not None else None
    report = PayloadReport(
        relative_path=entry.relative_path,
        expected_sha256=entry.expected_sha256,
        target_path=str(target) if target is not None else None,
        status="blocked",
        declared_sources=sources_by_name.get(Path(entry.relative_path).name, []),
    )
    if target is None:
        report.message = "src/stage0 dist_server is not a local file URL; no safe write target is available"
        return report
    if target.is_file():
        actual = sha256_file(target)
        report.existing_sha256 = actual
        if actual == entry.expected_sha256:
            report.status = "present"
            return report
        report.status = "checksum-mismatch"
        report.message = "existing payload digest does not match src/stage0; refusing to overwrite"
        return report

    fetchable = [
        source
        for source in report.declared_sources
        if source_is_fetchable(source)
        and (source.manifest_sha256 is None or source.manifest_sha256 == entry.expected_sha256)
    ]
    if not fetchable:
        # THE INTERNAL-RELEASE LANE (the daily-breakage fix): the seed ledger
        # DECLARES where the admitted-internal seed is published (a private
        # GitHub release). When the checkout's file:// payloads are missing —
        # every fresh pull on a machine that didn't mint the seed — fetch the
        # named asset via authenticated `gh` and verify it against the
        # src/stage0 pin exactly like any other source. No gh / no auth ⇒ the
        # report stays blocked and names the exact command to run.
        release = read_internal_release(root)
        if release is not None and release.scope == "internal":
            asset = Path(entry.relative_path).name
            if not fetch:
                report.status = "fetchable"
                report.selected_url = f"gh-release://{release.repo}@{release.tag}/{asset}"
                report.message = (
                    "rerun with --fetch to download the admitted-internal seed asset "
                    f"via `gh release download {release.tag} -R {release.repo}`"
                )
                return report
            if not gh_available():
                report.message = (
                    "the seed ledger publishes this payload at the internal release "
                    f"{release.repo}@{release.tag}, but `gh` is missing or unauthenticated; "
                    f"run: gh release download {release.tag} -R {release.repo} "
                    f"-D {target.parent}"
                )
                return report
            try:
                gh_release_fetch(release, asset, target, max(timeout, 300.0))
            except (OSError, subprocess.SubprocessError) as exc:
                report.status = "fetch-failed"
                report.message = f"gh release download failed: {exc}"
                return report
            actual = sha256_file(target)
            report.existing_sha256 = actual
            if actual != entry.expected_sha256:
                target.unlink(missing_ok=True)
                report.status = "download-checksum-mismatch"
                report.message = (
                    f"internal-release bytes failed src/stage0 checksum validation: "
                    f"expected {entry.expected_sha256}, actual {actual}"
                )
                return report
            report.status = "fetched"
            report.selected_url = f"gh-release://{release.repo}@{release.tag}/{asset}"
            return report
        if report.declared_sources:
            report.message = (
                "metadata declares no fetchable source with the src/stage0 SHA-256; "
                "repo-local missing file URLs and unsupported schemes are not enough"
            )
        else:
            report.message = "no checked-in channel manifest declares an xz_url for this payload"
        return report

    selected = fetchable[0]
    report.selected_url = selected.url
    if not fetch:
        report.status = "fetchable"
        report.message = "rerun with --fetch to materialize this checksum-pinned payload"
        return report

    try:
        copy_or_fetch(selected, root, target, timeout)
    except (OSError, ValueError, URLError) as exc:
        report.status = "fetch-failed"
        report.message = str(exc)
        return report
    actual = sha256_file(target)
    report.existing_sha256 = actual
    if actual != entry.expected_sha256:
        target.unlink(missing_ok=True)
        report.status = "download-checksum-mismatch"
        report.message = (
            f"fetched bytes failed src/stage0 checksum validation: "
            f"expected {entry.expected_sha256}, actual {actual}"
        )
        return report
    report.status = "fetched"
    return report


def report_as_dict(
    *,
    root: Path,
    stage0_path: Path,
    dist_root: Path | None,
    manifests: list[Path],
    payloads: list[PayloadReport],
    fetch: bool,
) -> dict[str, object]:
    blocked = [
        item
        for item in payloads
        if item.status
        not in {
            "present",
            "fetchable",
            "fetched",
        }
    ]
    fetchable = [item for item in payloads if item.status == "fetchable"]
    fetched = [item for item in payloads if item.status == "fetched"]
    missing_without_source = [item for item in payloads if item.status == "blocked"]
    if blocked:
        status = "blocked"
    elif fetchable and not fetch:
        status = "fetchable"
    else:
        status = "ready"
    return {
        "schema": "trust.stage0-payload-fetch-report.v1",
        "generated_at_epoch": int(time.time()),
        "status": status,
        "writes": bool(fetch),
        "repo_root": str(root),
        "stage0": str(stage0_path),
        "resolved_dist_root": str(dist_root) if dist_root is not None else None,
        "manifests": [str(path) for path in manifests],
        "payload_count": len(payloads),
        "fetchable_count": len(fetchable),
        "fetched_count": len(fetched),
        "blocked_count": len(blocked),
        "missing_without_declared_fetchable_source_count": len(missing_without_source),
        "payloads": [
            {
                "relative_path": item.relative_path,
                "expected_sha256": item.expected_sha256,
                "target_path": item.target_path,
                "status": item.status,
                "existing_sha256": item.existing_sha256,
                "selected_url": item.selected_url,
                "message": item.message,
                "declared_sources": [source.__dict__ for source in item.declared_sources],
            }
            for item in payloads
        ],
    }


def print_text_report(report: dict[str, object]) -> None:
    print(f"stage0_payload_fetch: {report['status']}")
    print(f"repo_root:            {report['repo_root']}")
    print(f"stage0:               {report['stage0']}")
    print(f"resolved_dist_root:   {report['resolved_dist_root'] or '<non-local>'}")
    print(f"payload_count:        {report['payload_count']}")
    print(f"fetchable_count:      {report['fetchable_count']}")
    print(f"fetched_count:        {report['fetched_count']}")
    print(f"blocked_count:        {report['blocked_count']}")
    print("manifests:")
    for manifest in report["manifests"]:
        print(f"  - {manifest}")
    print("payloads:")
    for item in report["payloads"]:
        assert isinstance(item, dict)
        print(f"  - {item['relative_path']}: {item['status']}")
        if item.get("message"):
            print(f"    {item['message']}")
        if item.get("selected_url"):
            print(f"    selected_url={item['selected_url']}")
        sources = item.get("declared_sources") or []
        if isinstance(sources, list) and sources:
            for source in sources:
                if isinstance(source, dict):
                    print(f"    declared_source={source.get('status')} {source.get('url')}")
    if report["status"] == "blocked":
        print()
        print("No payload URL was invented. Materialize a Trust-owned dist root with")
        print("`./x.py dist` and `src/tools/trust-stage0-dist/prepare.py`, or update")
        print("the checked-in Trust channel metadata to declare canonical payload URLs.")
    elif report["status"] == "fetchable":
        print()
        print("Rerun with --fetch to write only the payloads whose declared source")
        print("matches the SHA-256 pinned in src/stage0.")


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=repo_root())
    parser.add_argument("--stage0", type=Path, default=None)
    parser.add_argument("--dist-root", type=Path, default=None)
    parser.add_argument(
        "--manifest",
        action="append",
        type=Path,
        default=[],
        help="Additional channel manifest to inspect for declared xz_url values.",
    )
    parser.add_argument(
        "--fetch",
        action="store_true",
        help="Materialize missing payloads. Without this flag the command is audit-only.",
    )
    parser.add_argument("--json", action="store_true", help="Emit JSON instead of text.")
    parser.add_argument("--timeout", type=float, default=60.0)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    root = args.repo_root.resolve()
    stage0_path = (args.stage0 or root / "src" / "stage0").resolve()
    if not stage0_path.is_file():
        print(f"error: missing Trust stage0 metadata file: {stage0_path}", file=sys.stderr)
        return 2
    values = stage0_values(stage0_path)
    entries = stage0_entries(values)
    if not entries:
        print(f"error: {stage0_path} has no checksum-pinned dist archive entries", file=sys.stderr)
        return 2
    dist_root = args.dist_root.resolve() if args.dist_root else default_dist_root(root, values)
    manifests = default_manifests(root, dist_root, values)
    manifests.extend(path.resolve() for path in args.manifest)
    manifests = sorted(dict.fromkeys(manifests))
    sources = declared_sources(manifests, root)
    payloads = [
        evaluate_payload(
            entry,
            root=root,
            dist_root=dist_root,
            sources_by_name=sources,
            fetch=args.fetch,
            timeout=args.timeout,
        )
        for entry in entries
    ]
    report = report_as_dict(
        root=root,
        stage0_path=stage0_path,
        dist_root=dist_root,
        manifests=manifests,
        payloads=payloads,
        fetch=args.fetch,
    )
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print_text_report(report)
    return 0 if report["status"] in {"ready", "fetchable"} else 1


if __name__ == "__main__":
    raise SystemExit(main())
