#!/usr/bin/env bash
# What a push destination ALREADY HAS: the one reader of its advertised refs.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# A pre-push lane judges what a push INTRODUCES, never what the destination
# already holds. A branch that merges main carries main's already-published
# history in `old..new`, and judging it refused updates over commits and files
# the push did not introduce (c6eb148a34 for the revert-rationale lane; the
# cfg(test) caller-skew lane re-read every file such a merge brought in). So
# every lane that narrows its subject that way needs the same fact: which
# commits does the destination itself advertise. This file is the only place
# that reads it. The lanes differ in their UNIT — revert-rationale and
# measurement-provenance exclude commits, check_cfg_test_caller_skew.py
# excludes files whose content a destination commit already carries — but not
# in their evidence, so the evidence is read once, here, one way.
#
# THE RULES, each of which a lane's self-test holds in both directions:
#   * Only the destination's own live advertisement counts: authenticated,
#     complete native Agh Git refs for GitHub, `git ls-remote --refs` elsewhere.
#     A local branch, a remote-tracking ref, or a remote configured AT the
#     destination whose tracking ref was forged is local state and excludes
#     nothing.
#   * An advertised object missing from this object store supplies no
#     evidence. A missing main refuses; other missing objects are skipped,
#     never acquired for exclusion credit and never replaced by a
#     similarly named local ref; the caller then judges MORE, not less.
#   * A tag is peeled to its commit; an object that peels to no commit is
#     skipped.
#   * A destination that cannot be read, or whose advertisement is malformed,
#     is exit status 2 with the reason on stderr. The caller fails closed on
#     it; there is no fallback that guesses published history.
#
# Output: one `<commit> <advertised-ref>` line per usable ref.
#
# Usage:
#   . scripts/lib/push_destination.sh           # bash lanes: source, then call
#   trust_push_destination_refs DESTINATION     #   the function
#   bash scripts/lib/push_destination.sh DEST   # any other lane: execute it

trust_push_destination_refs() {
  local destination="${1:-}" advertised object ref extra commit
  if [ -z "$destination" ]; then
    echo "push-destination: no destination named" >&2
    return 2
  fi
  advertised="$(python3 - "$destination" "${BASH_SOURCE[0]%/*}" <<'TRUST_DESTINATION_PY'
import os
from pathlib import Path
import re
import subprocess
import sys
import time
from urllib.parse import urlsplit


def git_read(*args, ssh_advertisement=False):
    env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
    env.update(GIT_NO_LAZY_FETCH="1", GIT_NO_REPLACE_OBJECTS="1", GIT_GRAFT_FILE=os.devnull)
    if ssh_advertisement:
        # Only the already classified non-GitHub public advertisement may use
        # explicit caller SSH transport. Local object reads never do.
        for name in ("GIT_SSH", "GIT_SSH_COMMAND", "GIT_SSH_VARIANT"):
            if name in os.environ:
                env[name] = os.environ[name]
    return subprocess.run(["git", *args], text=True, errors="surrogateescape",
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=env)


def single_url(done):
    lines = done.stdout.splitlines()
    if done.returncode or len(lines) != 1 or not lines[0]:
        raise ValueError("destination does not resolve to exactly one URL")
    return lines[0]


def destination_url(destination):
    # Named remotes may have a different push URL. Ask Git, including its
    # normal URL rewriting; tracking refs supply no destination evidence.
    named = git_read("remote", "get-url", "--push", "--all", destination)
    if named.returncode == 0:
        return single_url(named)
    resolved = single_url(git_read("ls-remote", "--get-url", "--", destination))
    # Git's --get-url is a read/fetch resolver, not a literal-push resolver.
    # Do not guess a destination if pushInsteadOf would select another one.
    # A configured remote's --push resolver above supports that case exactly.
    rewrites = git_read("config", "--null", "--get-regexp", r"^url\..*\.pushinsteadof$")
    if rewrites.returncode not in (0, 1):
        raise ValueError("cannot read destination URL rewriting")
    for record in rewrites.stdout.split("\0"):
        if not record:
            continue
        key, separator, prefix = record.partition("\n")
        if not separator:
            raise ValueError("malformed destination URL rewriting")
        if destination.startswith(prefix):
            raise ValueError("literal pushInsteadOf destination requires a named remote's exact push URL")
    return resolved


def github_url(url):
    # Detect GitHub before considering a raw Git path, including mixed-case
    # hostnames. Unsupported GitHub syntax refuses; it never falls through to
    # credential-bearing/userinfo, anonymous API, or raw GitHub transport.
    parsed = urlsplit(url)
    if parsed.hostname and parsed.hostname.lower() == "github.com":
        if (any(ord(character) < 32 or ord(character) == 127 for character in url)
                or parsed.scheme not in ("https", "ssh") or parsed.port is not None
                or parsed.query or parsed.fragment or parsed.password is not None
                or parsed.username != ("git" if parsed.scheme == "ssh" else None)):
            raise ValueError("unsupported credential-free GitHub destination syntax")
        return "https://github.com/" + parsed.path.lstrip("/")
    scp = re.fullmatch(r"(?:(?P<user>[^/@\s]+)@)?(?P<host>[^/:\s]+):(?P<path>.+)", url)
    if scp and scp["host"].lower() == "github.com":
        if (scp["user"] != "git"
                or any(ord(character) < 32 or ord(character) == 127 for character in url)):
            raise ValueError("unsupported GitHub SSH destination identity")
        return "https://github.com/" + scp["path"]
    return None


def github_refs(reader, repository):
    found = git_read("rev-parse", "--absolute-git-dir")
    directory = Path(single_url(found))
    if not directory.is_absolute():
        raise ValueError("destination requires the actual caller object store")
    done = reader.destination_refs("https://github.com/" + repository + ".git",
                                   git_dir=directory, cwd=Path.cwd())
    if done.returncode:
        raise ValueError(f"authenticated Agh destination refs failed (exit {done.returncode}): "
                         + reader._message(done))
    if done.unavailable_refs:
        print(f"push-destination: {len(done.unavailable_refs)} non-main advertised refs "
              "supply no local commit exclusion evidence", file=sys.stderr)
    return done.stdout


def advertised_refs(destination, library):
    url = destination_url(destination)
    github = github_url(url)
    if github is not None:
        sys.path.insert(0, str(library.resolve()))
        import remote_tips
        repository = remote_tips.github_repository(github)
        if repository is None:
            raise ValueError("GitHub destination has no canonical repository")
        return github_refs(remote_tips, repository)
    # Keep genuine Git advertisement for local and non-GitHub destinations.
    # Refuse recursive rewrites rather than accidentally read another remote.
    if single_url(git_read("ls-remote", "--get-url", "--", url)) != url:
        raise ValueError("destination URL rewrites again after push resolution")
    done = git_read("ls-remote", "--refs", "--", url, ssh_advertisement=True)
    if done.returncode:
        raise ValueError("cannot read the destination's Git ref advertisement")
    sys.path.insert(0, str(library.resolve()))
    import remote_tips
    directory = Path(single_url(git_read("rev-parse", "--absolute-git-dir")))
    refs = []
    seen = set()
    for line in done.stdout.splitlines():
        fields = line.split()
        if (len(fields) != 2 or not re.fullmatch(r"[0-9a-f]{40}", fields[0])
                or fields[0] == "0" * 40 or fields[1] in seen
                or git_read("check-ref-format", fields[1]).returncode):
            raise ValueError("malformed destination ref advertisement")
        seen.add(fields[1])
        refs.append((fields[1], fields[0]))
    try:
        resolved, _unavailable = remote_tips._destination_commit_refs(
            refs, directory, deadline=time.monotonic() + remote_tips.LS_REMOTE_TIMEOUT_S)
    except remote_tips._PublicationSourceFailure as error:
        raise ValueError(remote_tips._message(error.result)) from error
    return "".join(f"{oid}\t{ref}\n" for ref, oid in resolved)


if __name__ == "__main__":
    try:
        sys.stdout.write(advertised_refs(sys.argv[1], Path(sys.argv[2])))
    except (OSError, UnicodeError, ValueError, TypeError, KeyError, ImportError) as error:
        print(f"push-destination: {error}", file=sys.stderr)
        sys.exit(2)
TRUST_DESTINATION_PY
)" || {
    echo "push-destination: cannot read the destination's advertised refs" >&2
    return 2
  }
  while read -r object ref extra; do
    [ -n "${object:-}" ] || continue
    if ! { [[ "$object" =~ ^[0-9a-f]{40}$ ]] && [[ "${ref:-}" == refs/* ]] && [ -z "${extra:-}" ]; }; then
      echo "push-destination: malformed ref advertisement from $destination" >&2
      return 2
    fi
    # Python already checked original hashes/types in the actual ODB borrow.
    # Re-peeling here could re-adopt caller GIT_* overrides after that check.
    printf '%s %s\n' "$object" "$ref"
  done <<< "$advertised"
  return 0
}

if [ "${BASH_SOURCE[0]}" = "$0" ]; then
  set -uo pipefail
  trust_push_destination_refs "$@"
  exit $?
fi
