# Stage receipt reference inputs

`reference.json.gz` retains observations from six existing production-reader
tests in `scripts/tests/recreate_bootstrap_test.py`. Both the original run and
the instrumented run passed. The instrumented run recorded each actual input
tree, exact receipt bytes, byte limit, commit, and return/refusal; it also
recorded the original LLVM and invocation validators' inputs and errors.

The archive has 204 filesystem cases, 58 LLVM cases and 36 invocation cases.
Its embedded source SHA-256 identities name the reader and test source. The
raw JSON SHA-256 is
`f563c189186c6b9ef0a16bf473e8caec61b774be9ad10d05eeeea68a83a39cfd`.
Compression uses gzip with zero mtime. No fixture executable is run by the
native reader tests. These controls validate the narrow receipt reader, not
the recorded build, its writer, unlisted stage files or proof authority.

Source methods on `StageToolProvenanceTests`:

- `test_promotion_reads_the_receipt_this_script_writes`
- `test_promotion_refuses_a_receipt_it_must_not_record`
- `test_promotion_knows_the_words_this_script_gives_a_receipt`
- `test_promotion_names_the_llvm_a_receipt_says_its_stage_carries`
- `test_a_malformed_llvm_record_is_refused_by_both_of_its_readers`
- `test_a_malformed_invocation_record_is_refused_by_both_of_its_readers`

Historical unpaired-surrogate invocation inputs cannot form Rust
strings; native strict JSON must refuse them. Their original rejection is
retained, rather than replaced with a lossy character. File/parse error prose
is observational; successful PROVENANCE lines and LLVM/valid-text invocation
error inventories must match exactly.

The original coordinator's six-control run and capture used
`<home>/.local/share/uv/python/cpython-3.13-macos-aarch64-none/bin/python3.13`
(as retained in `python-receipt-baseline.log` and `golden-capture.log`). The
additional diagnostic and integer-boundary controls below use that same
interpreter, without changing `sys.set_int_max_str_digits` or any global setting.
The measured executable resolves to
`<home>/.local/share/uv/python/cpython-3.13.18-macos-aarch64-none/bin/python3.13`,
reports Python 3.13.18 and Unicode 15.1.0, and has SHA-256
`747ca8797fea0949368e9e39d0f75b1eeadbae6c24edadda792ae22299e47a01`.
This records the observation interpreter, not a complete runtime seal.

`python-repr.json.gz` freezes 7586 exact input/`repr` pairs. It includes
nonempty insertion-order objects, Python scalar syntax, every Unicode
printability-range boundary plus selected combining/private/new characters,
and finite samples from 4096 seeded IEEE-754 bit patterns (seed 20261106).
The native diagnostic printability ranges use that Unicode 15.1 vocabulary;
they do not control receipt acceptance. Its raw JSON SHA-256 is
`0e3a6fe6a227f638566a6c5196fa80b2e64b96ae8c095e0ab7c1be3c54e9ec55`.

`integer-boundary.json.gz` freezes 16 actual calls to the original reader's
`read()` on receipt files, including signed 4300/4301-digit integers, machine-word
overflow, long floating significands/exponents, integer `-0`, and float `-0.0`.
The interpreter's unchanged default integer limit was 4300. Accepted floats
retain their original tokens in native data; only their diagnostic `repr`
uses Python-compatible floating interpretation. Its raw JSON SHA-256 is
`bab4da9671f5db09e4122c7dcf0beb0dc3b64757e211f123c2cd496dad32554e`.
Both new archives embed the interpreter image identity; the integer archive
also embeds the unchanged original reader source SHA-256. Both gzip files
have zero mtime. The original `reference.json.gz` above is unchanged.

`fixed-point-cases.json` is plain JSON and is not a recording. It holds 98
receipts (13 accepted, 85 refused), each described as edits to reference file
case 0, with its exact PROVENANCE lines or its exact refusal. 61 of them (9
accepted, 52 refused) test the seed host record rules (docs/PLAN.md PKG-S6).
They port the Python reader's fixed-point tests in
`scripts/tests/recreate_bootstrap_test.py` and add their edges: null or empty
host records, a Linux capture with no record graded `candidate-ready`, atpkg and
genesis lineages on Linux hosts, a seed capture whose host is not a string, a
JSON boolean disclosure, and disclosures with surrounding spaces. The other 37 (4
accepted, 33 refused) port the `native_stage_tools` branch of the Python reader's
`_recorded_files`: a `native_stage_tools` that is not a list, a tool other than
`rust-lld` or a repeated one, a `rust-lld` row that is not bound to the stated
in-tree LLVM in each way that reader checks (a stated LLVM identity whose mode is
not `in-tree` among them), a bound row hashed and counted in
`stage_receipt_files_verified` (and one whose file has other bytes, is missing,
is a directory, or is a symbolic link to its bytes, to nothing or to itself), Windows'
`.exe` names, and the two places where that reader's own semantics decide: a
host that is not a string is read through its `str()`, and the LLVM identities a
row repeats are compared with Python's `==` (an integer equals the float and the
boolean of its value). Their start, `native-lld`, carries the in-tree LLVM
identity reference file case 131 states, with lld's output directory beside
LLVM's; the bound file's bytes come from the case's own `files`, and its links from
its own `links`. A refusal that names a file the reader could not read ends in the
operating system's words for why (Python's `strerror`), so those cases hold on any
host whose C library words the error as this one does. Cases labelled
`first refusal:` hold two faults, each of which is refused alone, and pin which
one each reader names first. Both readers are held to every verdict:
`src/tests/fixed_point.rs` holds the native reader, and
`scripts/tests/stage_receipt_reader_parity_test.py` holds
`scripts/lib/stage_receipt_provenance.py`. That Python test also replays the 204
file cases above and checks that the Python reader still gives each recorded
verdict. On 2026-11-13 it gave all 204, and all 98 fixed-point cases.
