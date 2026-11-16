#!/usr/bin/env bash
# publish_seed_cut.sh — publish a minted trust cut's seed (the archives' release and the
# re-pin branch) once the pack is shown to be the mint's (docs/CUTTING-A-TOOLCHAIN.md §3.9).
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# WHY. A cut (scripts/mint_and_prove_seed.sh, then scripts/promote-toolchain.sh) ends with
# three publishing acts: the stage0 archives' release, the push of the re-pin branch
# `seed/repin-<C>`, and the pack (aterm's staged rustc-group upload, canary and
# `atpkg-publish publish-group rustc --publish-staged`).
# The re-pin makes the new compiler every checkout's stage0 once it lands, so the two acts
# here publish only the archives the re-pin's seed ledger pins, for the pack that mint
# sealed. The cut's other gates run before this script and are not repeated here: the
# double compile at mint (D12), promotion's UI gate and `--gate-only` on the staged pack,
# for a public seal SEAL-1's clauses (for P5a, SEAL-1-P5A's: the seal-line audit and the
# consumer check; for P5A2, SEAL-1-P5A2's, the same against the deployed 15698; for P5A3,
# SEAL-1-P5A3's, the same against the deployed 16387 with aterm's check widened), and aterm's
# pack smoke and hello world at publish. A fleet build, which the train cuts
# (scripts/daily_toolchain_stage.py train, docs/DAILY_TOOLCHAIN_STAGING.md), has no SEAL-1
# entry: docs/DECISION_QUEUE.md SEAL-1. No proof-count comparison gates a cut
# (docs/DECISION_QUEUE.md D27, amended 2026-10-17): this script asks no candidate gate.
#
# WHAT IT DOES, in order; anything wrong stops it before the first act:
#   1. THE PACK IS THE MINT'S: --pack is the staged seal (the promoted toolchain's copy
#      with the five trust-wp drivers in bin/, the directory aterm's publisher packs); its
#      SEED-MINT is --mint's trust-seed-mint, byte for byte; the re-pin branch the receipt
#      names is here and points at the receipt's re-pin commit; that commit's seed ledger
#      names the release ([release] repo, tag, date), the tag is the receipt's, and the
#      archives under the mint's repin/bootstrap/trust-stage0/dist/<date>/ exactly
#      match that commit's src/stage0 paths and hashes and its ledger checksums.
#   2. Without --publish (a dry run): print the two acts and stop. With --publish: create
#      the archives' release, then push the re-pin branch (a fast-forward push of a new
#      branch; never forced). agh routes the release repository to its registered
#      identity; Git routes the push to its configured remote. The agent running the cut
#      performs them on a Mac with the required credentials (any Mac whose
#      `aterm secrets status` says release signing is ready),
#      after the gates above pass (the owner, 2026-10-16: "AGENTS DO PERFORM THEM!", docs/OWNER_RULINGS.md OW-39;
#      docs/CUTTING-A-TOOLCHAIN.md §3.9, its Credential paragraph).
#
# usage: scripts/publish_seed_cut.sh --pack DIR --mint DIR [--aterm DIR]
#            [--remote NAME] [--publish]
#
#   --aterm DIR      the aterm checkout the printed pack step runs in (default $ATERM_ROOT,
#                    else ~/aterm); it is named, not read
#   --remote NAME    where the re-pin branch is pushed (default origin)
#
# Exit: 0 checked (and, with --publish, published); 1 a publishing act failed; 2 an input
# is wrong.
set -euo pipefail

me="publish_seed_cut"
die2() { printf '%s: REFUSED — %s; nothing is published\n' "$me" "$*" >&2; exit 2; }

PACK=""
MINT=""
ATERM="${ATERM_ROOT:-$HOME/aterm}"
REMOTE="origin"
PUBLISH=0
need() { [ "$#" -ge 2 ] && [ -n "$2" ] || die2 "$1 needs a value"; }
while [ "$#" -gt 0 ]; do
    case "$1" in
        --pack) need "$@"; PACK="$2"; shift 2 ;;
        --mint) need "$@"; MINT="$2"; shift 2 ;;
        --aterm) need "$@"; ATERM="$2"; shift 2 ;;
        --remote) need "$@"; REMOTE="$2"; shift 2 ;;
        --publish) PUBLISH=1; shift ;;
        -h|--help) sed -n '2,/^set -euo pipefail/p' "$0" | sed '$d'; exit 0 ;;
        *) die2 "unknown argument $1 (see --help)" ;;
    esac
done
[ -n "$PACK" ] || die2 "--pack <the staged seal> is required"
[ -n "$MINT" ] || die2 "--mint <build/pack-mint-<v>-<host>-<C>> is required"

ROOT=$(cd -P "$(dirname "$0")/.." && pwd -P) || die2 "cannot resolve the repository root"

# Python >= 3.11 (tomllib, for the seed ledger below), chosen the way
# scripts/mint_and_prove_seed.sh chooses it.
PYTHON_BIN=""
for candidate in python3.14 python3.13 python3.12 python3.11 python3; do
    p=$(type -P "$candidate" || true)
    if [ -n "$p" ] && "$p" -I -S -c 'import sys; raise SystemExit(sys.version_info < (3, 11))' 2>/dev/null; then
        PYTHON_BIN="$p"
        break
    fi
done
[ -n "$PYTHON_BIN" ] || die2 "python >= 3.11 is required (tomllib); tried python3.14 python3.13 python3.12 python3.11 python3"

# 1. THE PACK IS THE MINT'S.
[ -d "$PACK" ] || die2 "--pack $PACK is not a directory"
PACK=$(cd -P "$PACK" && pwd -P)
[ -x "$PACK/bin/trustc" ] || die2 "--pack $PACK has no bin/trustc: not a toolchain"
[ -f "$PACK/SEED-MINT" ] || die2 "--pack $PACK carries no SEED-MINT receipt: it is no minted cut (scripts/promote-toolchain.sh copies the mint's receipt in)"
[ -d "$MINT" ] || die2 "--mint $MINT is not a directory"
MINT=$(cd -P "$MINT" && pwd -P)
[ -f "$MINT/trust-seed-mint" ] || die2 "--mint $MINT holds no trust-seed-mint receipt"
cmp -s "$MINT/trust-seed-mint" "$PACK/SEED-MINT" || die2 "the pack's SEED-MINT is not $MINT/trust-seed-mint: the pack was not sealed from this mint"
field() { sed -n "s/^$1=//p" "$PACK/SEED-MINT" | head -n 1; }
REPIN_COMMIT=$(field repin_commit)
REPIN_BRANCH=$(field repin_branch)
REPIN_TAG=$(field repin_release_tag)
[[ "$REPIN_COMMIT" =~ ^[0-9a-f]{40}$ ]] || die2 "the SEED-MINT names no re-pin commit (repin_commit=$REPIN_COMMIT)"
[ -n "$REPIN_BRANCH" ] && [ -n "$REPIN_TAG" ] || die2 "the SEED-MINT names no re-pin branch or release tag"
got=$(git -C "$ROOT" rev-parse --verify -q "refs/heads/$REPIN_BRANCH" || true)
[ "$got" = "$REPIN_COMMIT" ] || die2 "branch $REPIN_BRANCH is ${got:-absent} here, not the re-pin ${REPIN_COMMIT:0:12} the receipt names"
LEDGER=$(git -C "$ROOT" show "$REPIN_COMMIT:bootstrap/trust-stage0/seed-ledger.toml" 2>/dev/null) ||
    die2 "the re-pin ${REPIN_COMMIT:0:12} has no bootstrap/trust-stage0/seed-ledger.toml"
DIST_ROOT="$MINT/repin/bootstrap/trust-stage0/dist"
# Bind filenames as well as bytes to the committed re-pin. A checksum set alone
# admits a missing component, a renamed archive, or an extra copy of pinned bytes.
RELEASE=$(printf '%s' "$LEDGER" | "$PYTHON_BIN" -I -S -c '
import hashlib, os, pathlib, re, stat, subprocess, sys, tomllib
ledger = tomllib.loads(sys.stdin.read())
release = ledger.get("release")
if not isinstance(release, dict):
    sys.exit("the re-pin seed ledger has no [release] table")
fields = [release.get(k) for k in ("repo", "tag", "title", "date")]
if not all(isinstance(v, str) and v and "\t" not in v and "\n" not in v for v in fields):
    sys.exit("the re-pin seed ledger [release] lacks repo, tag, title or date")
repo, tag, title, date = fields
if tag != sys.argv[2]:
    sys.exit(f"the re-pin seed ledger releases {tag}, the SEED-MINT receipt {sys.argv[2]}")
if not re.fullmatch(r"[0-9]{4}-[0-9]{2}-[0-9]{2}", date):
    sys.exit("the re-pin seed ledger date is not YYYY-MM-DD")
source = subprocess.run(["git", "-C", sys.argv[3], "show", f"{sys.argv[4]}:src/stage0"],
                        capture_output=True, text=True)
if source.returncode:
    sys.exit("the re-pin has no readable src/stage0")
stage0 = {}
for number, line in enumerate(source.stdout.splitlines(), 1):
    line = line.strip()
    if not line or line.startswith("#"):
        continue
    key, separator, value = line.partition("=")
    if not separator or key in stage0:
        sys.exit(f"the re-pin src/stage0:{number} is malformed or repeats a key")
    stage0[key] = value
if stage0.get("compiler_date") != date:
    sys.exit("the re-pin src/stage0 compiler_date differs from the seed ledger date")
pinned = {}
for key, digest in stage0.items():
    if not key.startswith("dist/") or not key.endswith(".tar.xz"):
        continue
    parts = pathlib.PurePosixPath(key).parts
    if (len(parts) != 3 or parts[:2] != ("dist", date)
            or key != "/".join(parts)
            or not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._+-]*\.tar\.xz", parts[2])
            or not re.fullmatch(r"[0-9a-f]{64}", digest)):
        sys.exit(f"the re-pin src/stage0 has a noncanonical archive pin: {key}")
    pinned[key] = digest
if not pinned:
    sys.exit("the re-pin src/stage0 pins no archives")
checksums = ledger.get("checksums")
if (not isinstance(checksums, list) or not checksums
        or not all(isinstance(c, str) and re.fullmatch(r"sha256:[0-9a-f]{64}", c)
                   for c in checksums)
        or set(checksums) != {"sha256:" + d for d in pinned.values()}):
    sys.exit("the re-pin seed ledger checksums do not match its src/stage0 archive pins")
if "hosts" in release:
    hosts = release["hosts"]
    if not isinstance(hosts, dict) or not hosts:
        sys.exit("the re-pin seed ledger host tables are malformed")
    covered = set()
    for host, record in hosts.items():
        if (not isinstance(record, dict) or record.get("host") != host
                or not re.fullmatch(r"[A-Za-z0-9_][A-Za-z0-9_.-]{2,127}", host)):
            sys.exit(f"the re-pin seed ledger host record is malformed: {host}")
        expected = {p: d for p, d in pinned.items() if p.endswith(f"-{host}.tar.xz")}
        if not expected:
            sys.exit(f"the re-pin seed ledger declares an unpinned host: {host}")
        expected.update({p: d for p, d in pinned.items()
                         if pathlib.PurePosixPath(p).name.startswith("trust-src-")})
        if record.get("payloads") != expected:
            sys.exit(f"the re-pin seed ledger host payloads differ from src/stage0: {host}")
        covered.update(expected)
    if covered != set(pinned):
        sys.exit("the re-pin seed ledger host payloads do not cover src/stage0")
dist = pathlib.Path(sys.argv[1]) / date
# Resolve no symlink inside the mint, including an archive directory.
for directory in (dist.parent.parent.parent.parent, dist.parent.parent.parent,
                  dist.parent.parent, dist.parent, dist):
    if directory.is_symlink() or not directory.is_dir():
        sys.exit(f"archive directory is not a regular directory: {directory}")
try:
    names = {n for n in os.listdir(dist)
             if ".tar." in n or n.endswith((".tgz", ".txz", ".tbz2", ".tzst"))}
except OSError as e:
    sys.exit(f"no archives at {dist}: {e.strerror}")
expected_names = {pathlib.PurePosixPath(p).name for p in pinned}
if names != expected_names:
    sys.exit(f"archive inventory differs from re-pin src/stage0: "
             f"missing={sorted(expected_names - names)}, extra={sorted(names - expected_names)}")
archives = []
for relative, expected_digest in sorted(pinned.items()):
    path = dist / pathlib.PurePosixPath(relative).name
    try:
        fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    except OSError as e:
        sys.exit(f"{path} is not a readable regular file: {e.strerror}")
    with os.fdopen(fd, "rb") as f:
        if not stat.S_ISREG(os.fstat(f.fileno()).st_mode):
            sys.exit(f"{path} is not a regular file")
        digest = hashlib.file_digest(f, "sha256").hexdigest()
    if digest != expected_digest:
        sys.exit(f"{path} sha256 {digest} differs from its re-pin src/stage0 pin {expected_digest}")
    archives.append(str(path))
print("\t".join([repo, tag, title, str(dist)]))
print("\n".join(archives))
' "$DIST_ROOT" "$REPIN_TAG" "$ROOT" "$REPIN_COMMIT") || die2 "the mint's archives do not match its re-pin (above)"
IFS=$'\t' read -r REPO TAG TITLE DIST <<<"$RELEASE"
ARCHIVES=()
while IFS= read -r f; do ARCHIVES+=("$f"); done <<<"${RELEASE#*$'\n'}"

# 2. THE TWO ACTS: the archives first (a fresh checkout of the re-pin fetches them), then
# the re-pin branch, which the superproject lander merges into main.
release_cmd=(agh release ensure "$REPO" "$TAG" --title "$TITLE"
    --notes "Trust stage0 seed archives for re-pin $REPIN_COMMIT (branch $REPIN_BRANCH), published by scripts/publish_seed_cut.sh.")
for archive in "${ARCHIVES[@]}"; do release_cmd+=(--file "$archive"); done
release_cmd+=(--publish)
push_cmd=(env -u GITHUB_TOKEN git -C "$ROOT" push "$REMOTE" "refs/heads/$REPIN_BRANCH:refs/heads/$REPIN_BRANCH")
# The pack, aterm's act once trust main contains the re-pin (its publisher refuses before).
group_cmd="targo --unverified run -q -p atpkg-publish -- --host agh publish-group rustc --seal $PACK --trust-repo $ROOT --out $PACK.atpkg-group"
if [ "$PUBLISH" -ne 1 ]; then
    printf '%s: DRY RUN — %s is sealed from this mint and its archives are the ones the re-pin pins; --publish would run, in order:\n' "$me" "$PACK"
    printf '  1. %s\n' "${release_cmd[*]}"
    printf '  2. %s\n' "${push_cmd[*]}"
    printf '  then, once main contains the re-pin, in %s: %s --dry-run, then the same with --stage-upload; run its staging canary, then the same with --publish-staged\n' "$ATERM" "$group_cmd"
    exit 0
fi
printf '%s: publishing %s (%d archives) to %s\n' "$me" "$TAG" "${#ARCHIVES[@]}" "$REPO"
# agh routes the named repository to its registered identity. Preflight that exact
# act before uploading; ensure publishes only after all checked assets are present.
"${release_cmd[@]}" --dry-run || { printf '%s: the release dry run failed; the re-pin is not pushed\n' "$me" >&2; exit 1; }
"${release_cmd[@]}" || { printf '%s: the release did not publish; the re-pin is not pushed\n' "$me" >&2; exit 1; }
"${push_cmd[@]}" || { printf '%s: the archives are released as %s, and the re-pin push failed: push %s again\n' "$me" "$TAG" "$REPIN_BRANCH" >&2; exit 1; }
printf '%s: published %s and pushed %s; next, once main contains the re-pin, in %s: %s --dry-run, then the same with --stage-upload; run its staging canary, then the same with --publish-staged\n' \
    "$me" "$TAG" "$REPIN_BRANCH" "$ATERM" "$group_cmd"
