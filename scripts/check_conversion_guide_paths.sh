#!/bin/bash
# Negative control for docs/TWO_LANGUAGE_CONVERSION_GUIDE.md.
#
# The guide's stated contract with its reader is "Every example below is a file
# that exists on this branch; the path is beside it, and you can run it". Two
# ways that has already been broken, both caught by review rather than by a
# check, and both cheap to pin:
#
#   1. a path that does not exist (one invented fixture name shipped in draft);
#   2. a path that exists but says the OPPOSITE of what the guide claims about
#      it — `r15_citation_by_theorem` was offered as the fixture for the CITED
#      `by theorem` route and contains no citation at all. A path-existence
#      sweep cannot see this, so the CITED section's fixtures are additionally
#      required to contain a ` by ` clause token.
#
# No toolchain needed. Exits non-zero on the first class of failure it finds.
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
GUIDE="$ROOT/docs/TWO_LANGUAGE_CONVERSION_GUIDE.md"
fails=0

if [ ! -f "$GUIDE" ]; then
    echo "ERROR: guide missing: $GUIDE" >&2
    exit 2
fi

# ---- 1. every in-repo path the guide names must exist -----------------------
# `crates/a`, `crates/b` are illustrative snippets in the §8 code block and
# `~/`-rooted external paths lose their prefix to this regex; both are skipped
# by name rather than by loosening the pattern.
while read -r p; do
    case "$p" in
        crates/a/*|crates/b/*) continue ;;
        crates/a3d-kernel/*|crates/aterm-spec-models/*|crates/aterm-gui/*) continue ;;
        # The remap example (WS8.9) quotes rustc's REMAPPED names under the absolute prefix `/src`
        # (`--remap-path-prefix=<checkout>=/src`, measured by tests/run-make/trust-ir-remap-path-identity):
        # `/src/lib.rs` and `/src/m.rs` are what the build artifact records, not repo paths. The regex
        # drops the leading `/`, so they are skipped by name, like the illustrative crates/a|b above.
        src/lib.rs|src/m.rs) continue ;;
    esac
    if [ ! -e "$ROOT/$p" ]; then
        echo "MISSING PATH: $p" >&2
        fails=$((fails + 1))
    fi
done < <(grep -oE '(tests|docs|compiler|crates|scripts|src)/[A-Za-z0-9_./-]+\.(rs|lean|clean|md|py|sh|toml)' "$GUIDE" | sort -u)

# ---- 2. every fixture offered for the CITED route must carry a citation -----
# The §3b block runs from its heading to the next one. A fixture cited there as
# evidence for `by theorem` has to contain the token.
cited_block="$(awk '/^### 3b\./{f=1} /^### 3c\./{f=0} f' "$GUIDE")"
if [ -z "$cited_block" ]; then
    echo "ERROR: could not locate guide section 3b (CITED) — has it been renumbered?" >&2
    exit 2
fi
while read -r p; do
    [ -e "$ROOT/$p" ] || continue          # class 1 already reported it
    if ! grep -qE '^\s*(ensures|//~|//!).*\bby\b|\bensures\b.*\bby\b' "$ROOT/$p"; then
        echo "NOT A CITATION FIXTURE: $p is offered under §3b (CITED) but contains no \`by\` clause" >&2
        fails=$((fails + 1))
    fi
done < <(printf '%s\n' "$cited_block" | grep -oE 'tests/[A-Za-z0-9_./-]+\.rs' | sort -u)

if [ "$fails" != 0 ]; then
    echo "check_conversion_guide_paths: $fails problem(s)" >&2
    exit 1
fi
echo "check_conversion_guide_paths: OK (paths exist; §3b fixtures carry citations)"
exit 0
