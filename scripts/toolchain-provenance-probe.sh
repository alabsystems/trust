#!/usr/bin/env bash
# Ask a SEALED toolchain's binary what is in it, instead of asking its name.
#
# WHY THIS EXISTS
# ---------------
# A seal is named `trust-<rev>` after the compiler's own `CFG_VERSION`, which is
# `git rev-parse HEAD` at build time and NOTHING ELSE. Bootstrap never records
# whether the working tree was CLEAN at that commit, so the name describes the
# HEAD the build started from, never the tree it compiled.
#
# Measured 2026-08-31: a blast-radius assessment concluded that "not one of the
# eight sealed toolchains contains fix `945a8fbff5`", derived by
# `git merge-base --is-ancestor` against each seal's self-reported revision.
# Read at the binary, `trust-3ae9948d`'s `librustc_driver` CONTAINS that fix's
# `span_warn` text verbatim. It was built from a working tree that already
# carried the patch, hours before the patch was committed.
#
# **Ancestry BOUNDS what could be in an artifact; it never establishes what is.**
# And it fails in the dangerous direction too: a seal whose HEAD contains a fix
# proves nothing if the tree had that fix stashed, reverted, or not yet rebuilt.
#
# THE TECHNIQUE, AND ITS HONEST BOUND
# -----------------------------------
# For a marker string S and a seal whose recorded revision is R, ask two
# independent questions and compare:
#
#   TREE   -- does the source tree AT R contain S?      (`git grep S R`)
#   BINARY -- does the sealed driver contain S?         (`grep -a S <driver>`)
#
# They must agree. A disagreement is PROOF the artifact was not built from the
# tree at its own recorded revision:
#
#   tree absent  / binary present -> AHEAD-OF-REV. The build tree carried source
#                                    the revision does not have. This is the
#                                    `trust-3ae9948d` case.
#   tree present / binary absent  -> BEHIND-REV. The artifact lacks source its
#                                    revision has: reverted, stashed, or the
#                                    driver was not rebuilt.
#
# WHAT AGREEMENT DOES **NOT** PROVE. Agreement on every marker means only that
# no probed marker caught a discrepancy. It is CONSISTENCY, never a clean-build
# certificate:
#   * a marker proves a STRING compiled in, not that every half of a change is
#     present -- a patch can add a diagnostic and a soundness fix, and be
#     applied in part;
#   * local work that never landed upstream has no marker at all and is
#     invisible to this method BY CONSTRUCTION;
#   * markers are sparse in time, so drift between two adjacent markers is not
#     tested.
# For a build-time answer rather than an after-the-fact inference, read the
# seal's own `PROVENANCE` file (written by scripts/promote-toolchain.sh from the
# stamp x.py writes while the build tree is still the build tree).
#
# ANTI-VACUITY. A seal in which NO marker is found at all is reported UNUSABLE,
# not CONSISTENT -- that is a statement about the probe (wrong binary, stripped
# symbols, unreadable file), not about the artifact. Two markers below are
# present in every seal measured and exist to be exactly that control.
#
#   scripts/toolchain-provenance-probe.sh                 # every seal
#   scripts/toolchain-provenance-probe.sh <toolchain-dir> # just one
set -uo pipefail

REPO="$(cd "$(dirname "$0")/.." && pwd)"
ROOT="${TRUST_TOOLCHAIN_HOME:-$HOME/toolchains}"

# Rows are `<tree pattern>|<binary pattern>|<git-grep paths>|<what it witnesses>`.
# The two patterns differ only where the source spelling and the compiled
# spelling differ -- a `-Z` flag is `trust_ctfe_trivial_probe` in options.rs and
# `trust-ctfe-trivial-probe` in the option table the driver ships.
MARKERS=(
	"trust_ctfe_trivial_probe|trust-ctfe-trivial-probe|compiler/rustc_session/src/options.rs|-Z flag added between 2026-08-20 and 2026-08-26"
	"is not a Trust attribute|is not a Trust attribute|compiler/ crates/|the reserved trust:: namespace refusal (9a243492fa, 2026-08-30)"
	"elision is DECLINED for this function|elision is DECLINED for this function|compiler/ crates/|THE NAMED CASE: the elision-prefix soundness fix (945a8fbff5, 2026-08-31)"
	# Controls. Present in every seal measured; they discriminate nothing and are
	# here so that "no anomaly" cannot mean "the probe never saw anything".
	"Trust verification exceeded its per-function budget|Trust verification exceeded its per-function budget|compiler/ crates/|CONTROL — expected present in every seal"
	"carries #\[trust::assume_total\]|carries #[trust::assume_total]|compiler/ crates/|CONTROL — expected present in every seal"
)

probe_one() {
	local dir="$1" name rev lib anomalies=0 found=0 row tpat bpat paths what tree bin verdict
	name="$(basename "$dir")"
	[[ -x "$dir/bin/trustc" ]] || { printf '%s: no trustc — skipped\n' "$name"; return 0; }
	rev="$("$dir/bin/trustc" -vV 2>/dev/null | sed -n 's/^commit-hash: //p' | head -1)"
	lib="$(ls "$dir"/lib/librustc_driver-*.dylib "$dir"/lib/librustc_driver-*.so 2>/dev/null | head -1)"

	printf '\n=== %s  (self-reported rev %s)\n' "$name" "${rev:0:9}"
	if ! git -C "$REPO" cat-file -e "${rev}^{commit}" 2>/dev/null; then
		printf '    rev is NOT a commit in %s — every tree-side answer below is unavailable\n' "$REPO"
		return 0
	fi
	[[ -n "$lib" ]] || { printf '    no librustc_driver — cannot probe\n'; return 0; }
	printf '    %-42s %-8s %-8s %s\n' MARKER TREE BINARY VERDICT

	for row in "${MARKERS[@]}"; do
		tpat="${row%%|*}"; row="${row#*|}"
		bpat="${row%%|*}"; row="${row#*|}"
		paths="${row%%|*}"; what="${row#*|}"

		# shellcheck disable=SC2086  # $paths is a deliberate multi-path list
		if git -C "$REPO" grep -q -E "$tpat" "$rev" -- $paths 2>/dev/null; then tree=present; else tree=absent; fi
		if LC_ALL=C grep -a -q -F "$bpat" "$lib" 2>/dev/null; then bin=present; found=$((found + 1)); else bin=absent; fi

		if [[ "$tree" == "$bin" ]]; then
			verdict=consistent
		elif [[ "$tree" == absent ]]; then
			verdict="AHEAD-OF-REV"; anomalies=$((anomalies + 1))
		else
			verdict="BEHIND-REV"; anomalies=$((anomalies + 1))
		fi
		printf '    %-42s %-8s %-8s %s\n' "${bpat:0:42}" "$tree" "$bin" "$verdict"
		[[ "$verdict" != consistent ]] && printf '        ^ %s\n' "$what"
	done

	if [[ "$found" -eq 0 ]]; then
		printf '    VERDICT: UNUSABLE — no marker was found in this binary at all.\n'
		printf '             That is a statement about the PROBE, not the artifact.\n'
	elif [[ "$anomalies" -gt 0 ]]; then
		printf '    VERDICT: ANOMALY (%d) — PROVEN not built from the tree at its own rev.\n' "$anomalies"
		printf '             Its name, and every ancestry answer derived from it, is unsound.\n'
	else
		printf '    VERDICT: CONSISTENT on %d/%d markers — no probed marker caught a\n' "$found" "${#MARKERS[@]}"
		printf '             discrepancy. NOT a clean-build certificate; see the header.\n'
	fi
}

if [[ $# -gt 0 ]]; then
	probe_one "$1"
else
	for d in "$ROOT"/trust-????????; do
		[[ -d "$d" ]] && probe_one "$d"
	done
fi
