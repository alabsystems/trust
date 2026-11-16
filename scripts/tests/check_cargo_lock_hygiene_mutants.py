#!/usr/bin/env python3
"""Mutants of scripts/check_cargo_lock_hygiene.py: each must fail its --selftest.

Each mutant is applied to a copy of the script (and of scripts/land_gate.py,
whose offline call and refusal pattern the check uses) in a temporary tree
with scripts/lib linked in. No tracked file is written. Each selftest runs
under a fresh, empty TMPDIR, and anything left there fails it. The run fails
if the unmutated copy fails its selftest, if an anchor is not unique, or if
any mutant survives.

`main()`'s reads of the real tree (its file list, its files and its drift)
are not reachable from --selftest, which reads none of this tree's locks;
the fast.cargo-lock-hygiene row runs them on the real tree. What main() hands
run_checks (the resolver, by_order and the sweep) is `tree_wiring`, which the
selftest runs on a temporary root.

    python3 scripts/tests/check_cargo_lock_hygiene_mutants.py
"""
from __future__ import annotations

import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
H = "scripts/check_cargo_lock_hygiene.py"
L = "scripts/land_gate.py"

MUTANTS = [
    (H, "refusal read as uncached", '        return "stale", said\n', '        return "uncached", said\n'),
    (H, "download checked before refusal",
     '    if lg.locked_metadata_refusal(stderr):\n        return "stale", said\n'
     '    if DOWNLOAD_MISS_RE.search(stderr):\n        return "uncached", said\n',
     '    if DOWNLOAD_MISS_RE.search(stderr):\n        return "uncached", said\n'
     '    if lg.locked_metadata_refusal(stderr):\n        return "stale", said\n'),
    (H, "download pattern: any failed to", 'r"^error: failed to download `"', 'r"^error: failed to "'),
    (H, "download pattern unanchored", 'r"^error: failed to download `", re.MULTILINE',
     'r"failed to download `", re.MULTILINE'),
    (H, "download pattern without backtick", 'r"^error: failed to download `"',
     'r"^error: failed to download"'),
    (H, "timeout passes", '    if returncode is None:\n        return "undecided", stderr\n',
     '    if returncode is None:\n        return "current", stderr\n'),
    (H, "fixture names kept", '                or "fixtures" in parts):\n            continue\n        try:\n            parsed',
     '                ):\n            continue\n        try:\n            parsed'),
    (H, "targo-trust names dropped", 'TRUST_TOPS = ("crates", "targo-trust")', 'TRUST_TOPS = ("crates",)'),
    (H, "registry entries read as path packages", '            and "source" not in entry}', '            }'),
    (H, "unparsable lock skipped", '        if listed is None or gits is None or listed & names:',
     '        if listed is not None and gits is not None and listed & names:'),
    (H, "no manifest needed", '        if in_workspace(directory, "Cargo.toml") not in present:\n            continue\n', ''),
    (H, "directory rule dropped",
     '        if directory == "." or (lock.parts[0] in TRUST_TOPS and "fixtures" not in lock.parts):',
     '        if directory == ".":'),
    (H, "vendor judged", 'FOREIGN_TOPS = ("vendor",)', 'FOREIGN_TOPS = ()'),
    (H, "unparsable Trust manifest skipped",
     '            problems.append(f"{path} does not parse, so Cargo cannot read it: {error}")',
     '            pass'),
    (H, "lockless standalone workspace allowed", '        if "workspace" in document and lock not in present:',
     '        if False:'),
    (H, "stale ignored", '        if verdict == "stale":\n            stale.append((directory, line))\n',
     '        if verdict == "stale":\n            pass\n'),
    (H, "undecided passes", '        elif verdict == "undecided":\n            undecided.append((directory, line))\n',
     '        elif verdict == "undecided":\n            pass\n'),
    (H, "empty list passes", '"FAIL: no committed workspace lock found to resolve; nothing was judged",\n              file=sys.stderr)\n        return 1\n',
     '"FAIL: no committed workspace lock found to resolve; nothing was judged",\n              file=sys.stderr)\n        return 0\n'),
    (H, "drift ignored", '    if drifted or unknown:\n        print("FAIL: the committed locks were not judged',
     '    if False:\n        print("FAIL: the committed locks were not judged'),
    (H, "unreadable drift ignored", '    if drifted or unknown:\n', '    if drifted:\n'),
    (H, "git+ rule dropped", '    return sources_rc or locked_rc or (1 if problems else 0)\n',
     '    return locked_rc or (1 if problems else 0)\n'),
    (H, "git+ sources never found", '        if source.startswith("git+"):',
     '        if source.startswith("git+NEVER"):'),
    (H, "root not required", '    if "." not in workspaces:', '    if False:'),
    (H, "selection problems pass", '    return sources_rc or locked_rc or (1 if problems else 0)\n',
     '    return sources_rc or locked_rc\n'),
    (H, "no file list passes", '        return sources_rc or 1\n    workspaces, problems',
     '        return sources_rc\n    workspaces, problems'),
    (H, "file list by pathspec", '["git", "-C", str(root), "ls-files", "-z"]',
     '["git", "-C", str(root), "ls-files", "-z", "--", "Cargo.lock", "crates/*Cargo.lock"]'),
    (H, "file list in the caller's git env", 'text=True, env=lg.git_query_env(), check=False, timeout=60)',
     'text=True, check=False, timeout=60)'),
    (H, "targo that cannot start passes", '            return 127, f"error: cannot run targo: {error}"',
     '            return 0, f"error: cannot run targo: {error}"'),
    (H, "stale remedy is a fresh resolution", '    relock = (f"targo metadata --offline --format-version 1 --manifest-path "',
     '    relock = (f"targo update --manifest-path "'),
    (H, "git-sourced wording lost", '        if git_sourced:\n            return "undecided", (f"{said} (this lock keeps',
     '        if False:\n            return "undecided", (f"{said} (this lock keeps'),
    (H, "git-sourced remedy note dropped", '            if directory in git_sourced:\n                print("    (this lock keeps',
     '            if False:\n                print("    (this lock keeps'),
    (H, "resolver ignores the root", '            proc, hung = ask(str(root / directory / "Cargo.toml"))',
     '            proc, hung = ask(str(Path(directory) / "Cargo.toml"))'),
    (H, "git+ rule exempts every judged lock", '        if directory == "." or directory in KEEPS_GIT:',
     '        if True:'),
    (H, "nothing keeps git+ on purpose", 'KEEPS_GIT = frozenset({"targo-trust/tests/fixtures/fabric"})',
     'KEEPS_GIT = frozenset()'),
    (H, "unreadable lock passes the git+ rule",
     '            problems.append(f"{lock} could not be read for git+ sources: {error}")',
     '            pass'),
    (H, "judged git+ problems dropped", '    problems += judged_git_sources(workspaces, read)\n', ''),
    (H, "fabric wording lost in run_checks",
     'locked_check(workspaces, resolve, drift, KEEPS_GIT & set(workspaces), by_order)',
     'locked_check(workspaces, resolve, drift, by_order=by_order)'),
    (H, "git+ exemption: every fixture", '        if directory == "." or directory in KEEPS_GIT:',
     '        if directory == "." or "fixtures" in directory:'),
    (H, "git+ exemption: any targo-trust fixture", '        if directory == "." or directory in KEEPS_GIT:',
     '        if directory == "." or directory.startswith("targo-trust/tests/fixtures/"):'),
    (H, "git+ exemption: any directory named fabric", '        if directory == "." or directory in KEEPS_GIT:',
     '        if directory == "." or Path(directory).name == "fabric":'),
    (H, "git+ rule on crates/ only", '        if directory == "." or directory in KEEPS_GIT:',
     '        if directory == "." or directory in KEEPS_GIT or not directory.startswith("crates/"):'),
    (H, "git+ rule on first-party URLs only", '        if source.startswith("git+"):',
     '        if source.startswith("git+") and "alabsystems/" in source:'),
    (H, "only [[package]] read", '    for group in groups:\n        if not isinstance(group, list):',
     '    for group in groups[:1]:\n        if not isinstance(group, list):'),
    (H, "[root] not read", '[root] if root is not None else []', '[]'),
    (H, "patch.unused not read", '              patch.get("unused", [])]', '              []]'),
    (H, "unknown top-level key allowed", '    if not set(document) <= LOCK_KEYS:\n        return None\n',
     '    if False:\n        return None\n'),
    (H, "unknown [patch] key allowed", '    if not isinstance(patch, dict) or not set(patch) <= {"unused"}:',
     '    if not isinstance(patch, dict):'),
    (H, "non-list package group skipped", '        if not isinstance(group, list):\n            return None\n',
     '        if not isinstance(group, list):\n            continue\n'),
    (H, "non-table entry skipped", '            if not isinstance(entry, dict):\n                return None\n',
     '            if not isinstance(entry, dict):\n                continue\n'),
    (H, "first party: host read with user and port", '        host = parsed.hostname or ""',
     '        host = parsed.netloc.lower()'),
    (H, "first party: www. kept", '    if host.startswith("www."):\n        host = host[len("www."):]\n', ''),
    (H, "first party: empty path segments kept",
     '    segments = [segment for segment in path.split("/") if segment]',
     '    segments = path.split("/")[1:]'),
    (H, "first party: path letter case kept",
     'unicodedata.normalize("NFKC", urllib.parse.unquote(parsed.path)).casefold()',
     'unicodedata.normalize("NFKC", urllib.parse.unquote(parsed.path))'),
    (H, "first party: path percent-encoding kept",
     'unicodedata.normalize("NFKC", urllib.parse.unquote(parsed.path)).casefold()',
     'unicodedata.normalize("NFKC", parsed.path).casefold()'),
    (H, "first party: host percent-encoding kept",
     'unicodedata.normalize("NFKC", urllib.parse.unquote(host)).casefold().rstrip(".")',
     'unicodedata.normalize("NFKC", host).casefold().rstrip(".")'),
    (H, "first party: host compatibility forms kept",
     'unicodedata.normalize("NFKC", urllib.parse.unquote(host)).casefold().rstrip(".")',
     'urllib.parse.unquote(host).casefold().rstrip(".")'),
    (H, "first party: host trailing dot kept",
     'unicodedata.normalize("NFKC", urllib.parse.unquote(host)).casefold().rstrip(".")',
     'unicodedata.normalize("NFKC", urllib.parse.unquote(host)).casefold()'),
    (H, "first party: SSH-over-443 host dropped",
     'FIRST_PARTY_HOSTS = frozenset({"github.com", "ssh.github.com"})',
     'FIRST_PARTY_HOSTS = frozenset({"github.com"})'),
    (H, "first party: an unparsable URL is skipped", '    except ValueError:\n        return True\n',
     '    except ValueError:\n        return False\n'),
    (H, "first party: any GitHub organization", 'and bool(segments) and segments[0] == FIRST_PARTY_ORG',
     'and bool(segments)'),
    (H, "first party: organization as a prefix", 'segments[0] == FIRST_PARTY_ORG',
     'segments[0].startswith(FIRST_PARTY_ORG)'),
    (H, "first party: only the first git source", 'for _, _, source in gits):',
     'for _, _, source in gits[:1]):'),
    (H, "v1 [metadata] lock refused",
     'LOCK_KEYS = frozenset({"version", "package", "root", "metadata", "patch"})',
     'LOCK_KEYS = frozenset({"version", "package", "root", "patch"})'),
    (H, "closing count ignores the root rule", '{len(problems) + (1 if sources_rc else 0)} problem(s)',
     '{max(len(problems), 1)} problem(s)'),
    (H, "selftest leaks its tracked_files directory", '        repo = Path(tmp) / "repo"\n',
     '        tmp = tempfile.mkdtemp(prefix="lock-hygiene-selftest-")\n        repo = Path(tmp) / "repo"\n'),
    (H, "selftest leaks a directory of its own", '    no_drift: Drift = lambda: ([], [])\n',
     '    tempfile.mkdtemp(prefix="lock-hygiene-leak-")\n    no_drift: Drift = lambda: ([], [])\n'),
    (L, "land_gate: metadata inherits a lockfile redirect",
     '            if var not in METADATA_ENV_DROP and not var.startswith(', '            if not var.startswith('),
    (L, "land_gate: metadata keeps the TARGO_ twin",
     'METADATA_ENV_DROP = ("CARGO_RESOLVER_LOCKFILE_PATH", "TARGO_RESOLVER_LOCKFILE_PATH")',
     'METADATA_ENV_DROP = ("CARGO_RESOLVER_LOCKFILE_PATH",)'),
    (L, "land_gate: an include is not a redirect", 'if "include" in config or (', 'if ('),
    (L, "land_gate: offline metadata runs despite a config redirect",
     '        return None, f"offline targo metadata was not run: {redirect}"\n', '        pass\n'),
    (L, "land_gate: the network fill runs despite a config redirect",
     '        return None, f"not run: {redirect}"\n', '        pass\n'),
    (L, "land_gate: one config name per directory", 'LOCK_CONFIG_NAMES = ("config.toml", "config")',
     'LOCK_CONFIG_NAMES = ("config.toml",)'),
    (L, "land_gate: the nearest config hides the others",
     '        why = lock_config_reason(path, outside)\n        if why:\n            return why\n',
     '        if path.exists():\n            return lock_config_reason(path, outside)\n'),
    (L, "land_gate: a host [patch] is not refused", '    if outside and "patch" in config:\n',
     '    if False:\n'),
    (L, "land_gate: a host paths is not refused", '    if outside and "paths" in config:\n',
     '    if False:\n'),
    (L, "land_gate: the tree's own [patch] is refused", '    if outside and "patch" in config:\n',
     '    if "patch" in config:\n'),
    (L, "land_gate: the tree's own paths is refused", '    if outside and "paths" in config:\n',
     '    if "paths" in config:\n'),
    (L, "land_gate: a home other than the last ignored",
     '            for directory in [base / ".cargo" for base in (cwd, *cwd.parents)] + homes\n',
     '            for directory in [base / ".cargo" for base in (cwd, *cwd.parents)] + homes[-1:]\n'),
    (L, "land_gate: metadata keeps the [unstable] variables",
     'METADATA_ENV_DROP_PREFIXES = ("CARGO_UNSTABLE_", "TARGO_UNSTABLE_")', 'METADATA_ENV_DROP_PREFIXES = ()'),
    (L, "land_gate: an [unstable] table is not refused", '    if "unstable" in config:\n',
     '    if False:\n'),
    (L, "land_gate: an untracked .cargo/config beside the committed file is read as harmless",
     '    if shadow.is_symlink() or shadow.exists():\n', '    if False:\n'),
    (L, "land_gate: a .cargo file above is unreadable config",
     '    except (FileNotFoundError, NotADirectoryError):\n        return None\n',
     '    except FileNotFoundError:\n        return None\n'),
    (H, "a host redirect still judges every lock", '    if redirect:\n        print(f"FAIL: no lock was judged',
     '    if False:\n        print(f"FAIL: no lock was judged'),
    (H, "reports/ judged", 'in FOREIGN_TOPS + EVIDENCE_TOPS:', 'in FOREIGN_TOPS:'),
    (H, "unreadable lock outside crates/ not judged",
     '        except (OSError, UnicodeDecodeError):\n            chosen.add(directory)\n            continue\n',
     '        except (OSError, UnicodeDecodeError):\n            continue\n'),
    (H, "git_url keeps the #sha", '    return source[len("git+"):].split("?")[0].split("#")[0]',
     '    return source[len("git+"):].split("?")[0]'),
    (H, "git fill: network asked again", '                and manifest in fills_git and state["no_network"] is None',
     '                and manifest in fills_git'),
    (H, "git fill: failed fill replaces the offline answer",
     '                if filled is not None and lg.locked_metadata_refusal(filled.stderr):',
     '                if filled is not None:'),
    (H, "git fill: success not re-asked offline",
     '            if why is None:\n                proc, hung = lg.offline_metadata(manifest)\n',
     '            if why is None:\n                pass\n'),
    (H, "git fill: failure not remembered", '                state["no_network"] = why\n', ''),
    (H, "git fill: for any failure", 'proc.returncode != 0 and lg.escaped_git_source(proc.stderr)\n',
     'proc.returncode != 0\n'),
    (H, "git fill: under drift", '                and not drift()[0]):', '                ):'),
    (H, "closing FAIL line only for selection problems", '    if problems or sources_rc:\n',
     '    if problems:\n'),
    (H, "every judged lock worded as keeping git",
     'locked_check(workspaces, resolve, drift, KEEPS_GIT & set(workspaces), by_order)',
     'locked_check(workspaces, resolve, drift, frozenset(workspaces), by_order)'),
    (H, "undecodable lock not caught",
     '        except (OSError, UnicodeDecodeError) as error:\n            problems.append(f"{lock} could not be read for git+',
     '        except OSError as error:\n            problems.append(f"{lock} could not be read for git+'),
    (H, "no continue after an unreadable lock",
     'problems.append(f"{lock} could not be read for git+ sources: {error}")\n            continue\n',
     'problems.append(f"{lock} could not be read for git+ sources: {error}")\n'),
    (H, "unparsable judged lock passes the git+ rule",
     '            problems.append(f"{lock} does not parse as a Cargo lock (read as TOML 1.0), so its "\n'
     '                            "git+ sources cannot be read")\n',
     '            pass\n'),
    (H, "unparsable root lock passes",
     '              "sources cannot be read", file=sys.stderr)\n        return 1\n',
     '              "sources cannot be read", file=sys.stderr)\n        return 0\n'),
    (H, "git-only first-party consumer not judged",
     '        elif any(first_party_git(source) for _, _, source in gits):',
     '        elif False:'),
    (H, "git fill for any lock", '                and manifest in fills_git and state["no_network"] is None',
     '                and state["no_network"] is None'),
    (H, "unused-order copy for any failure",
     '        if (proc is not None and proc.returncode != 0 and lg.locked_metadata_refusal(proc.stderr)\n',
     '        if (proc is not None and proc.returncode != 0\n'),
    (H, "unused-order copy under drift", '                and not any(drift())):\n            # A PATH',
     '                ):\n            # A PATH'),
    (H, "unused-order copy asked with an absolute path", '                    str(rel), committed,',
     '                    manifest, committed,'),
    (H, "unused-order copy given the manifest", '                committed = (Path(manifest).parent / "Cargo.lock")',
     '                committed = (Path(manifest).parent / "Cargo.toml")'),
    (H, "unused-order copy never fills", 'state["no_network"], may_fill=True)',
     'state["no_network"], may_fill=False)'),
    (H, "unused-order network verdict dropped", '                copied, state["no_network"] = lg.unused_order_answer(',
     '                copied, _ = lg.unused_order_answer('),
    (H, "unused-order None replaces the refusal", '                if copied is not None:\n                    proc, hung = copied, None',
     '                if True:\n                    proc, hung = copied, None'),
    (H, "unused-order copy outside the root", '                rel = Path(manifest).resolve().relative_to(lg.REPO_ROOT.resolve())',
     '                rel = Path(manifest).resolve()'),
    (H, "copy-answered manifest not marked", '                        by_order.add(manifest)',
     '                        pass'),
    (H, "copy-answered lock counted as --locked", '        elif verdict == "current" and by_order(directory):',
     '        elif False:'),
    (H, "judged without the sweep", '        sweep(workspaces)\n', '        pass\n'),
    (H, "main sweeps only the default parents",
     '            parents=sorted({(lg.REPO_ROOT / d).parent for d in workspaces if d != "."}))',
     '            parents=None)'),
    (H, "copy-answered set not shared with the PASS line",
     'for d in KEEPS_GIT), copied))', 'for d in KEEPS_GIT), set()))'),
    (L, "land_gate: sweep ignores the parents it is given",
     'for parent in (unused_order_copy_parents() if parents is None else parents):',
     'for parent in unused_order_copy_parents():'),
    (H, "fabric remedy worded as git-free", '    if keeps_git:\n        return relock',
     '    if False:\n        return relock'),
    (H, "missing patch row not named", '                f"{in_workspace(directory, \'Cargo.toml\')} ({rows}) and relock.',
     '                f"{in_workspace(directory, \'Cargo.toml\')} and relock.'),
    (L, "land_gate: missing-lock spelling dropped", 'r"(?:cannot (?:update|create) the lock file',
     'r"(?:cannot (?:update) the lock file'),
    (L, "land_gate: --offline dropped", '*(["--offline"] if offline else [])', '*([] if offline else [])'),
    (L, "land_gate: --locked dropped", '*(["--locked"] if locked else [])', '*([] if locked else [])'),
]


def farm(tmp: Path) -> None:
    """A tree where the two mutable files are copies and every other entry of
    the checkout (and of scripts/, which land_gate imports from) is a link."""
    for entry in REPO.iterdir():
        if entry.name != "scripts":
            os.symlink(entry, tmp / entry.name)
    (tmp / "scripts").mkdir()
    for entry in (REPO / "scripts").iterdir():
        target = tmp / "scripts" / entry.name
        if f"scripts/{entry.name}" in (H, L):
            shutil.copy2(entry, target)
        else:
            os.symlink(entry, target)


def selftest(tmp: Path) -> subprocess.CompletedProcess:
    """The copy's --selftest under a fresh, empty TMPDIR. Anything it leaves
    there fails the run, so a selftest that leaks (LOCK-STALE-2's third review)
    fails the baseline."""
    scratch = tmp / ".selftest-tmpdir"
    scratch.mkdir()
    run = subprocess.run([sys.executable, "-B", str(tmp / H), "--selftest"], capture_output=True,
                         text=True, timeout=900, env=dict(os.environ, TMPDIR=str(scratch)))
    left = sorted(entry.name for entry in scratch.iterdir())
    if left:
        return subprocess.CompletedProcess(run.args, run.returncode or 1, run.stdout,
                                           f"{run.stderr}SELFTEST FAIL: left {left} under TMPDIR\n")
    return run


def main() -> int:
    texts = {path: (REPO / path).read_text(encoding="utf-8") for path in (H, L)}
    with tempfile.TemporaryDirectory(prefix="lock-hygiene-mutants-") as tmp:
        farm(Path(tmp))
        baseline = selftest(Path(tmp))
    if baseline.returncode != 0:
        print(f"BASELINE FAIL: the unmutated copy's --selftest exited {baseline.returncode}\n"
              f"{(baseline.stdout + baseline.stderr)[-2000:]}", file=sys.stderr)
        return 1
    print("BASELINE: the unmutated copy's --selftest passes")
    survived = []
    for path, name, old, new in MUTANTS:
        if texts[path].count(old) != 1:
            print(f"ANCHOR: {name}: found {texts[path].count(old)} times in {path}", file=sys.stderr)
            return 1
        with tempfile.TemporaryDirectory(prefix="lock-hygiene-mutants-") as tmp:
            farm(Path(tmp))
            (Path(tmp) / path).write_text(texts[path].replace(old, new), encoding="utf-8")
            run = selftest(Path(tmp))
        if run.returncode == 0:
            survived.append(name)
            print(f"SURVIVED {name}")
        else:
            why = next((line for line in (run.stderr + run.stdout).splitlines()
                        if "SELFTEST FAIL" in line or "Error" in line), f"exit {run.returncode}")
            print(f"KILLED {name}: {why[:140]}")
    if survived:
        print(f"MUTANTS: {len(survived)} of {len(MUTANTS)} survived: {', '.join(survived)}",
              file=sys.stderr)
        return 1
    print(f"MUTANTS: all {len(MUTANTS)} killed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
