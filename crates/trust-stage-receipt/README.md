# Native stage receipt validation

This library reads the existing `trust.stage-tool-provenance.v2` format for
native paired qualification. It checks the receipt's vocabulary and internal
consistency and compares every listed stage executable hash with actual bytes.
It does not establish who wrote a receipt, reconstruct its build, cover the
stage's unlisted files or standard libraries, or grant proof, execution or
publication authority. The separate complete seal identity remains necessary.

`inventory::capture_directory` provides a separate bounded content observation
for a compiler-reported directory tree. On Unix it records all regular files
and directories, including metadata and empty directories, without suffix
filtering. It rejects descendant links and special files, uses no-follow
directory handles, and verifies observed metadata again across the whole tree.
Other platforms refuse this strict API. Names and bytes are bounded; parent
namespaces must be trusted. Matching observations are neither immutable
snapshots nor complete loaded-runtime or provenance attestations. Existing
receipt alias handling retains its original behavior.

`read_required_regular_file` is a separate strict Unix intake API. Required
absence refuses. It rejects non-regular leaves, uses no-follow/nonblocking
handles, reserves the admitted length fallibly, reads with one-byte growth
lookahead, and compares exact length plus descriptor/path metadata before
returning owned bytes. It does not canonicalize the leaf or change optional
receipt and compatibility-alias behavior. Parent namespaces must be trusted;
observations are sequential, not immutable snapshots. Other platforms refuse.

LLVM source, output and build records are statements in the receipt. An external
LLVM is never promoted to a stated in-tree identity. A completed candidate's
stable source-closure statements are checked for consistency, not re-created
from a build directory this reader does not own. These distinctions are part
of the API, not conditions that a successful parse removes.

The Python reader remains until equivalent native behavior and all callers
are qualified and migrated. Source qualification does not qualify a release.

Receipt JSON uses a native lossless data model. Numeric tokens remain exact,
including integers larger than machine words; insertion order is retained while
the LLVM source-row digest explicitly sorts keys. Parsing, clone, comparison,
printing and destruction use explicit stacks. The reader accepts at most 16 MiB
and 1000 nested containers. Decimal integer tokens retain the original reader's
4300-digit default bound; floating tokens are not subject to that integer limit.
Only isolated quoted string tokens use `trust-json`'s
decoder; the stage library enables no global serde parsing features and has no
normal serde dependency.

Python-style refusal diagnostics use the original qualification host's Python
3.13.18 / Unicode 15.1 printability vocabulary, frozen as native numeric ranges.
This affects diagnostic escaping only. Receipt acceptance uses the existing
explicit control-code ranges. A separate frozen 7586-case oracle covers object
order, scalar syntax, Unicode boundaries and binary-float diagnostic formatting.
Floating tokens remain exact in the native data model; binary-float conversion
is confined to reproducing Python's diagnostic representation of lexical floats.
Integer diagnostics never pass through floating point.
