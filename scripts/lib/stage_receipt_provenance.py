#!/usr/bin/env python3
"""The stage receipt of a toolchain being sealed, checked and rendered as PROVENANCE lines.

WHY. scripts/recreate_bootstrap.py leaves a receipt in the stage it builds,
`tool-provenance.json` (schema trust.stage-tool-provenance.v2): which stage0 the build
started from (its bootstrap lineage: seed, atpkg or genesis), every shipped tool bound to
the x.py artifact it was copied from, and the source and native-tool state of the build.
It is stage content, so promotion's `cp -a` carries it into the seal and
`artifact_content_sha256` covers it. Until 2026-10-12 promotion never opened it. Three
seals cut that day with the documented seed command (`recreate_bootstrap.py --stage 2
--require-seed --fresh-seed --no-register`, then `promote-toolchain.sh --no-flip
--require-provenance`) each carried a receipt saying `mode: seed`, `trust_from_trust:
true`, `internal-release-ready`, and each PROVENANCE said `stage0_lineage=absent` ("promote
was given no --lineage record"), because `--lineage` takes a seed-STAIRCASE record and
nothing read the receipt. A reader of PROVENANCE could not tell that the seal was
seed-built by the recreator.

WHAT IS ESTABLISHED HERE, AND WHAT IS NOT. Two things are checked against the tree being
sealed, and a receipt that fails either is a REFUSAL, never a line:

* the receipt names this stage's files: each hash it records FOR A FILE OF THIS STAGE
  that is read here (the `sha256` of each tool row, the compiler's and its `rustc`
  name's, the `rustdoc` name's, the proc-macro helper's) equals the sha256 of that file
  in the tree, and the commit it names is the one the tree's compiler reports;
* the receipt is well formed: strict JSON (no repeated key, no NaN), the one schema this
  reads, statuses and lineage words from the recreator's own vocabulary, and no
  contradiction among the fields recorded below (a release-ready status without a
  freshly materialized Trust seed, a `bound` row whose two hashes differ).

THE REACH OF THAT BINDING. Those hashes are the only ones compared with a file, and the
recreator writes them for executables only: its tool rows, `bin/trustc` with its two
stock names, and the helper under `libexec/`. Of THIS STAGE'S files it records no hash
for anything under `lib/`, where the compiler itself lives (in `trust-f22fc270`,
`bin/trustc` is a 51,560-byte launcher and `lib/librustc_driver-*.dylib` is 787,511,336
bytes) and the standard library with it. So a tree whose `lib/` changed after its
receipt was written still passes here, as it passes the recreator's own verifier; so
does an executable the receipt does not list, and a receipt that lists one tool is
checked for one tool (`stage_receipt_files_verified` is the count, so a reader sees how
many). Nor is the writer established: any file of this form is read, whoever wrote it.
What identifies every byte of a seal is `artifact_content_sha256`, in the same
PROVENANCE.

THE RECEIPT'S OTHER HASHES are not compared with any file, and most of what a receipt
records is of that kind. Measured 2026-10-13 on the receipt sealed in `trust-f22fc270`
(a seed build): 351 sha256 values, of which the 21 above are compared. Of the other
330, 154 are the files of the SEED's stage0 tree, 62 of them under that tree's own
`lib/` (a `librustc_driver` and a `libstd` among them: the seed's, not this stage's);
the rest include seed archives, native tools, dynamic dependencies, source snapshots,
and the x.py artifact each tool was copied from (a tool row's `producer_sha256` is
compared with the row's own `sha256`, and with no file). No path the receipt records
lies under this stage's `lib/`. So "a receipt records hashes of executables only" is
true of this stage's files and false of the receipt as a whole, and a seal says the
first (section (f) of PROVENANCE, written by scripts/promote-toolchain.sh).

What the receipt SAYS about the build (its lineage and its status) is the receipt's own
statement. Re-deriving it needs the build tree and the seed archives: that is
`recreate_bootstrap.py --verify-stage-provenance`, run where the stage was built. The
PROVENANCE lines say which is which. A receipt the recreator itself marked `rejected` is
refused too: its writer exited nonzero on that stage, and quoting its lineage in a seal
would turn a refusal into a record.

A stage with no receipt (a plain `x.py build`) is not an error: `stage_receipt=absent`.
The sanctioned seed mint uses the same capture/writer owner with its explicit build
layout. Its receipt names `scripts/mint_and_prove_seed.sh` as writer and contains no
`recreator_invocation`; its specific `build/pack-mint-*/<host>/stage2` paths are accepted
here with that writer, and the file/lineage/LLVM checks below apply unchanged.

THE LINES, for a stage that carries one:

    stage_receipt=tool-provenance.json
    stage_receipt_sha256=<sha256 of the file in the tree named on the command line>
    stage_receipt_schema=trust.stage-tool-provenance.v2
    stage_receipt_status=<candidate-ready | internal-release-ready | release-ready |
                          unpinned-root-seed-ready>
    stage_receipt_lineage_mode=<seed | atpkg | genesis>
    stage_receipt_trust_from_trust=<true | false>
    stage_receipt_seed_materialization=<fresh-from-validated-archives |
                                        preexisting-unproven | not-applicable>
    stage_receipt_seed_admission=fixed-point-unpinned-root          (that kind only)
    stage_receipt_seed_root_disclosure=root=unpinned-host-chain predecessor_pin=none
        double_compile_diverse=false stock_built_ancestor=inferred-no-receipt
                                                                    (that kind only; one line)
    stage_receipt_files_verified=<how many recorded file hashes were compared; all equal>
    stage_receipt_llvm=<in-tree | external | unknown | not-recorded>
    stage_receipt_llvm_identity=<stated | not-stated>
    stage_receipt_llvm_provenance=<built-in-this-run | reused | changed-in-this-run |
                                   external | unknown>
    stage_receipt_llvm_source_sha256=<the LLVM source identity | not-recorded>
    stage_receipt_llvm_source_tree=<git tree id of src/llvm-project | not-recorded>
    stage_receipt_llvm_built_at_commit=<commit the LLVM was built at | not-recorded>
    stage_receipt_llvm_output_sha256=<fingerprint of what LLVM's build installed |
                                      not-recorded>
    stage_receipt_recreator_argv=<the recreator's arguments, shell-quoted | not-recorded>

THE SEED ADMISSION LINES. `unpinned-root-seed-ready` and the two seed admission lines
belong to a build from a seed whose selected host record is the fixed-point kind (a first
Linux seed with no pinned predecessor and no diverse double compile, docs/PLAN.md PKG-S6).
That status is never a release status, and a receipt that pairs that kind with one is
refused, as is the status with any other kind. The selected host record is the receipt's
own host's, or the receipt is refused; a record of another kind that carries the
fixed-point kind's disclosure or admission is refused; and a seed lineage on a Linux host
with no host record at all (a single-host ledger, which never admitted a Linux host) is
refused. Every other receipt's lines are what they were.

THE LLVM LINES are the receipt's `llvm_identity` record: which LLVM the stage carries.
Until 2026-10-13 x.py did not rebuild the in-tree LLVM for a committed change to it
(docs/KNOWN_HAZARDS.md, LLVM-STAMP-COMMITTED-1), and two of the three seals of 2026-10-12
carried an LLVM built at another commit, in a reused build directory, with nothing sealed
saying so. Since then x.py rebuilds it when HEAD:src/llvm-project moves from the tree
recorded beside it, but it keeps an LLVM that cannot say what it was built from (one built
before that record, whose own build header names no commit this checkout has), and a change
to src/bootstrap, src/version, the bootstrap config or the native tools rebuilds none; so a
seal still needs the receipt's own record, and cannot take x.py's for it. A receipt without
the record (every one written before 2026-10-13, those three among them) gives the one line
`stage_receipt_llvm=not-recorded` and is otherwise read as it was. With the
record, all seven lines are written: `_identity=stated` means the build could say which
sources its LLVM was built from (it watched build/<host>/llvm come into being, or that
directory carried the record of such a build for the same LLVM sources, bootstrap config
and native tools, and its installed files had not changed); `_source_sha256` is one sha256
over the git object ids of the LLVM inputs in the source tree, `_source_tree` the id of
src/llvm-project among them; `_built_at_commit` is the commit of the build the LLVM comes
from, which for `reused` may be an earlier one; `_output_sha256` is one sha256 over every
file and link that build installed under build/<host>/llvm (and build/<host>/lld, where
x.py builds LLD). A value is `not-recorded` where the record holds none, and those four
are written for `stage_receipt_llvm=in-tree` only: of any other mode they say
`not-recorded` whatever the record holds (below).

`stage_receipt_llvm=external` IS NEVER `_identity=stated`. The stage links an LLVM through
the recreator's `--llvm-config`: one the build did not watch being built and has no
record of such a build for; what the receipt's build authority binds of it is the
llvm-config executable (path, sha256, version) and that file's dylib closure, not the
libraries it points at. So its lines are `_identity=not-stated`, `_provenance=external`,
and `not-recorded` for all four of `_source_sha256`, `_source_tree`, `_built_at_commit`
and `_output_sha256`: the checkout's own src/llvm-project is not what that LLVM was built
from, and its ids are not written beside it as if they described it. A record that says
otherwise (an external LLVM stated, or carrying a source identity, an output or a build
record) is malformed, and refused. (Until the independent re-read of 2026-10-13 such a
record was stated whenever the authority had bound the llvm-config, with the checkout's
ids beside it; no seal was cut from one.)

`stage_receipt_llvm=unknown` IS NEVER `_identity=stated` EITHER. The build could not tell
which LLVM x.py links: the bootstrap config x.py obeys does not itself say (it names an
llvm-config other than the recreator's `--llvm-config`, or none where one was given; it
has an `include` key; it does not set `llvm.download-ci-llvm = false`), or it could not
be read, or the LLVM could not be observed or its record formed. The record's `reasons`
say which. Its lines are `_identity=not-stated`, `_provenance=unknown` and `not-recorded`
for the other four: neither the checkout's src/llvm-project nor its build directory is
known to be what the stage links. The recreator writes no source identity into such a
record since the follow-up of 2026-10-13; one it wrote from 381ac1ea0d until then holds
the checkout's, and that record is still accepted (refusing it would make a stage that
was sealed by default a refusal), but its ids are not written here. (Recording a config
that names another llvm-config as `external` instead was considered and not taken:
`external` says the llvm-config executable is the one the receipt's build authority
binds, and of that one it is not; DECISION_QUEUE, "a seal knows which LLVM it carries".)

CHECKED here: the record's form, and that
it does not contradict itself or the receipt it is in (a stated in-tree identity quotes a
build record for this receipt's host, bootstrap config and native authority). NOT CHECKED:
any file. The seal holds no build directory to compare with, so these lines are the
receipt's own statement, like its lineage; `recreate_bootstrap.py --verify-stage-provenance`
recomputes the source identity and the output fingerprint in the build tree.

THE STATUS WORD DOES NOT DEPEND ON THE LLVM. A receipt is `internal-release-ready` on its
source and seed lineage exactly as it was before the record existed, whether its LLVM
identity is stated or not: `_status=internal-release-ready` beside `_llvm_identity=not-stated`
is a receipt the recreator writes (a build in a build directory whose LLVM it did not watch
being built), and it is recorded, not refused. Requiring the identity is a separate,
explicit question: `--require-llvm-identity` here, which `promote-toolchain.sh
--require-llvm-identity` asks before it seals. It fails for a stage without a receipt, a
receipt without the record, and a record that does not state the identity (every record of
an external LLVM among them), and says which.

`recreator_argv` is the receipt's `recreator_invocation` record (the arguments
`recreate_bootstrap.py` was started with; a receipt without the record gives
`not-recorded`: one written before the recreator recorded it, or one the recreator did
not write). It is self-reported: nothing can re-derive a command line after the build.
The value is printable ASCII on one line, whatever the arguments were:

* each argument is one shell word (`shlex.quote`); one holding a non-ASCII character is
  written in the shell's `$'...'` form with those characters as their UTF-8 bytes
  (a backslash, `x` and two hex digits each), so bash reads the line back as the same
  arguments (the committed tests read it back with bash; measured on bash 3.2.57). zsh
  does not always: `shlex.quote` leaves a word beginning with `=` bare, and zsh expands
  such a word (measured, zsh 5.9: `=ls` reads back as `/bin/ls`, `=a` is an error);
* a value in parentheses is this file's own word and never an argument (a quoted
  argument cannot begin with `(`): `(no arguments)`, and `(not quoted here: ...)` when
  the quoted arguments are longer than ARGV_QUOTED_MAX characters, in which case they
  are read from the sealed receipt itself;
* the single argument `not-recorded` is written `'not-recorded'`, so the bare word, when
  it is the whole value, always means the receipt has no record. It is this file's own
  word too, though not in parentheses, and section (f) of a seal's PROVENANCE says so.

WHO READS A SEAL'S PROVENANCE, and why the lines are bounded. In this repository only
tests do, but the first-party checkouts pinned under it parse the file: trust-mc
(`scripts/development_seal.py`, `scripts/tuple_check.py`, its backend build script and
driver) and trust-cg (`scripts/check_trust_default_authority.py`). They take the keys
they name and ignore the rest; `development_seal.py` is strict about the form of every
line: `key=value` with a value, no key twice, a line of at most 8192 characters, at
most 128 fields, 65536 bytes. `trust-f22fc270` as it would be sealed today has 66
fields in 10824 bytes, its longest line 144 characters (measured 2026-10-13 after the
follow-up, with what section (f) says of the LLVM lines, `external` and `unknown`
included; its receipt records no LLVM, so it gets the one line. With a recorded in-tree
LLVM the same seal would have 72 fields in at most 11246 bytes, with an external one 72
in 11082, and with one of unknown mode 72 in 11080, four of the seven lines of either
saying `not-recorded`; trust-mc's reader accepts each, trust-cg's finds in each nothing
it did not find in the record of the same kind before the follow-up, and
`development_seal.py` refuses the same record with one empty value. Before the
follow-up: 66 fields in 10088 bytes; before the LLVM lines: 65 fields in 8031). Every
line here has a value, no key repeats, and the only line whose length the build decides
is bounded.

Usage: stage_receipt_provenance.py [--require-llvm-identity] TOOLCHAIN_DIRECTORY REPORTED_COMMIT
  Prints the lines and exits 0; exits 1 with the reason on stderr for a receipt that is
  present and unusable. With --require-llvm-identity it exits 3, with the reason on stderr
  and nothing on stdout, for a stage that is recordable and does not state which LLVM it
  carries (no receipt, no record, or an identity that is not stated). It exits 2 with
  this usage for any other argument list, an operand that begins with `-` among them
  (the flag goes first; typed after the directory it was read as the commit until
  2026-10-13). Read-only: it opens the receipt and the files it names, and runs nothing.
  Python 3.9 or newer (promotion runs it under whatever `python3` is on PATH).
"""

# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shlex
import stat
import sys

RECEIPT_NAME = "tool-provenance.json"
RECEIPT_SCHEMA = "trust.stage-tool-provenance.v2"
LINEAGE_SCHEMA = "trust.bootstrap-lineage.v1"
INVOCATION_SCHEMA = "trust.recreator-invocation.v1"
INVOCATION_KEYS = frozenset({"schema", "scope", "argv"})
INVOCATION_SCOPE = "self-reported"

# The receipt's `llvm_identity` record: which LLVM the stage carries. The words, the key
# sets and the rules below are recreate_bootstrap.py's (LLVM_* and `_llvm_identity_errors`
# there), kept in step by scripts/tests/recreate_bootstrap_test.py, which runs both on the
# same records.
LLVM_IDENTITY_SCHEMA = "trust.llvm-identity.v1"
LLVM_SOURCE_IDENTITY_SCHEMA = "trust.llvm-source-identity.v1"
LLVM_BUILD_RECORD_SCHEMA = "trust.llvm-build-record.v1"
LLVM_SOURCE_TREE = "src/llvm-project"
LLVM_PROVENANCE_OF_MODE = {
    "in-tree": ("built-in-this-run", "reused", "changed-in-this-run", "unknown"),
    "external": ("external",),
    "unknown": ("unknown",),
}
LLVM_IDENTITY_KEYS = frozenset({
    "schema", "mode", "provenance", "identity_stated", "reasons", "source_identity_sha256",
    "source_paths", "output_dirs", "output_fingerprint_sha256", "build_record",
})
LLVM_BUILD_RECORD_KEYS = frozenset({
    "schema", "built_at_commit", "host", "source_identity_sha256", "source_paths",
    "bootstrap_config_sha256", "native_authority_sha256", "output_fingerprint_sha256",
})
LLVM_NOT_RECORDED = "not-recorded"

# What recreate_bootstrap.py `_classify_receipt_status` gives a receipt it did not reject,
# and the word it writes when it did. scripts/tests/recreate_bootstrap_test.py holds this
# list to that function. `unpinned-root-seed-ready` is the grade of a build from a seed
# whose selected host record is the fixed-point kind (docs/PLAN.md PKG-S6): accepted, and
# never a release status.
ACCEPTED_STATUSES = ("candidate-ready", "internal-release-ready", "release-ready", "unpinned-root-seed-ready")
RELEASE_STATUSES = ("internal-release-ready", "release-ready")
REJECTED_STATUS = "rejected"
UNPINNED_ROOT_STATUS = "unpinned-root-seed-ready"

# The selected host record of a seed lineage, as the recreator's seed capture records it
# (bootstrap_lineage.validated_seed.authority.seed_ledger.host_records). Of the fixed-point
# kind (scripts/seed_host_ledger.py FIXED_POINT_SCHEMA) the reader writes what its
# root_disclosure says in four fixed words, which are the only values its validator admits
# (scripts/seed_fixed_point.py DISCLOSURE and STOCK_ANCESTOR; recreate_bootstrap_test holds
# them equal). A receipt that says anything else of them contradicts its own record.
FIXED_POINT_HOST_RECORD_SCHEMA = "trust-seed-fixed-point-host-record-v1"
FIXED_POINT_ADMISSION_KIND = "fixed-point-unpinned-root"
FIXED_POINT_DISCLOSED = (
    ("root", "unpinned-host-chain"),
    ("predecessor_pin", "none"),
    ("double_compile_diverse", "false"),
    ("stock_built_ancestor", "inferred-no-receipt"),
)
# scripts/seed_root_initialization.py LINUX_HOSTS (recreate_bootstrap_test holds the two
# equal, and recreate_bootstrap.py's LINUX_SEED_HOSTS to them). A single-host seed ledger
# never admitted one of these hosts; the recreator refuses one that tries.
LINUX_SEED_HOSTS = frozenset({"aarch64-unknown-linux-gnu", "x86_64-unknown-linux-gnu"})

# Bootstrap lineage: mode -> (status, trust_from_trust), as `_bind_bootstrap_lineage`
# writes them for a lineage without errors.
LINEAGE_OF_MODE = {
    "seed": ("trust_from_trust", True),
    "atpkg": ("local_atpkg", True),
    "genesis": ("local_genesis", False),
}
SEED_MATERIALIZATIONS = ("fresh-from-validated-archives", "preexisting-unproven")
FRESH_SEED = "fresh-from-validated-archives"
NO_SEED = "not-applicable"
ARGV_NOT_RECORDED = "not-recorded"
ARGV_NONE = "(no arguments)"
# The quoted arguments on the stage_receipt_recreator_argv line: half of the 8192
# characters the strictest reader of PROVENANCE allows a line (see the docstring).
ARGV_QUOTED_MAX = 4096

# The three receipts this was written against are 126 KB each.
MAX_RECEIPT_BYTES = 16 * 1024 * 1024
# The most containers a receipt nests: a rule of this reader and of its Rust twin
# (crates/trust-stage-receipt/src/json.rs MAX_NESTING), which words a deeper one the same.
# It is not left to the interpreter: CPython 3.12.3's json module decodes 9997 levels, and
# that limit moves with the version and the build, so a verdict would follow whichever
# Python ran.
MAX_JSON_NESTING = 1000
# The most digits a decimal integer in a receipt has, by the same rule (json.rs
# MAX_INTEGER_DIGITS): CPython's default int conversion bound. A PYTHONINTMAXSTRDIGITS or
# -X int_max_str_digits that raises or lifts that bound does not move this one; one that
# lowers it still refuses a shorter integer.
MAX_JSON_INTEGER_DIGITS = 4300
# The bytes nesting is counted over: a bracket, a quote or a backslash.
_JSON_NESTING_BYTE = re.compile(rb'[\[\]{}"\\]')
_CHUNK = 1 << 20
_SHA256 = re.compile(r"[0-9a-f]{64}")
_COMMIT = re.compile(r"[0-9a-f]{40}(?:[0-9a-f]{24})?")
_STAGE_ROOT = re.compile(r"build/[A-Za-z0-9_.-]+/stage[0-9]+")
_MINT_STAGE_ROOT = re.compile(r"build/pack-mint-[A-Za-z0-9_.+-]+/[A-Za-z0-9_.-]+/stage2")


class StageReceiptError(Exception):
    """The stage carries a receipt that promotion must not record."""


def _file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with open(path, "rb") as handle:
        for block in iter(lambda: handle.read(_CHUNK), b""):
            digest.update(block)
    return digest.hexdigest()


def _unique_keys(pairs: list) -> dict:
    out: dict = {}
    for key, value in pairs:
        if key in out:
            raise StageReceiptError(f"it repeats the key {key!r}")
        out[key] = value
    return out


def _no_constant(name: str) -> None:
    raise StageReceiptError(f"it holds {name}, which is not JSON")


def _nesting_error(raw: bytes) -> str | None:
    """Where `raw` opens a container past MAX_JSON_NESTING, in its Rust twin's words."""
    depth = 0
    in_string = False
    escaped = -1
    for match in _JSON_NESTING_BYTE.finditer(raw):
        at = match.start()
        byte = raw[at]
        if at == escaped:
            continue
        if byte == 0x5C:
            escaped = at + 1
        elif byte == 0x22:
            in_string = not in_string
        elif in_string:
            continue
        elif byte in b"[{":
            if depth >= MAX_JSON_NESTING:
                return f"JSON nesting exceeds {MAX_JSON_NESTING} containers at byte {at}"
            depth += 1
        else:
            depth -= 1
    return None


def _bounded_int(token: str) -> int:
    """A JSON integer token's value, refused past MAX_JSON_INTEGER_DIGITS digits."""
    if len(token) - token.startswith("-") > MAX_JSON_INTEGER_DIGITS:
        raise ValueError(f"decimal integer exceeds the original {MAX_JSON_INTEGER_DIGITS}-digit limit")
    return int(token)


def _receipt_identity(value):
    return (value.st_dev, value.st_ino, value.st_mode, value.st_size,
            value.st_mtime_ns, value.st_ctime_ns)


def read(toolchain: Path, *, receipt_path: Path | None = None,
         receipt_sha256: str | None = None):
    """(bytes, parsed object) of the receipt in `toolchain`, or None when it has none."""
    selected = receipt_path is not None or receipt_sha256 is not None
    if selected and (receipt_path is None or not receipt_path.is_absolute()
                     or not isinstance(receipt_sha256, str)
                     or not _SHA256.fullmatch(receipt_sha256)):
        raise StageReceiptError("an explicit receipt needs an absolute path and exact sha256")
    path = receipt_path if selected else toolchain / RECEIPT_NAME
    try:
        metadata = os.lstat(path)
    except FileNotFoundError:
        if selected:
            raise StageReceiptError("the explicitly selected receipt is absent")
        return None
    except OSError as error:
        raise StageReceiptError(f"it cannot be inspected: {error}") from error
    if not stat.S_ISREG(metadata.st_mode):
        raise StageReceiptError(
            f"it is not a regular file (mode {stat.filemode(metadata.st_mode)}); "
            "a seal cannot carry a receipt it only points at"
        )
    if metadata.st_size > MAX_RECEIPT_BYTES:
        raise StageReceiptError(f"it is {metadata.st_size} bytes, more than {MAX_RECEIPT_BYTES}")
    try:
        fd = os.open(path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0))
        with os.fdopen(fd, "rb") as stream:
            opened = os.fstat(stream.fileno())
            if not stat.S_ISREG(opened.st_mode) or _receipt_identity(opened) != _receipt_identity(metadata):
                raise StageReceiptError("the receipt changed before it was opened")
            raw = stream.read(MAX_RECEIPT_BYTES + 1)
            if len(raw) > MAX_RECEIPT_BYTES:
                raise StageReceiptError("the receipt grew past its size limit")
            if (_receipt_identity(os.fstat(stream.fileno())) != _receipt_identity(opened)
                    or _receipt_identity(os.lstat(path)) != _receipt_identity(opened)):
                raise StageReceiptError("the receipt changed while it was read")
        if selected and hashlib.sha256(raw).hexdigest() != receipt_sha256:
            raise StageReceiptError("the explicitly selected receipt sha256 differs")
        nesting = _nesting_error(raw)
        if nesting is not None:
            raise StageReceiptError(f"it is not JSON: {nesting}")
        value = json.loads(
            raw.decode("utf-8"), object_pairs_hook=_unique_keys, parse_constant=_no_constant,
            parse_int=_bounded_int,
        )
    except OSError as error:
        raise StageReceiptError(f"it cannot be read: {error}") from error
    except (UnicodeDecodeError, ValueError, RecursionError) as error:
        raise StageReceiptError(f"it is not JSON: {error}") from error
    if not isinstance(value, dict):
        raise StageReceiptError("it is not a JSON object")
    return raw, value


def _object(parent: dict, key: str, where: str) -> dict:
    value = parent.get(key)
    if not isinstance(value, dict):
        raise StageReceiptError(f"{where}{key} is not an object")
    return value


def _digest(parent: dict, key: str, where: str) -> str:
    value = parent.get(key)
    if not isinstance(value, str) or not _SHA256.fullmatch(value):
        raise StageReceiptError(f"{where}{key} is not a sha256: {value!r}")
    return value


def release_status_holds(mode: object, trust_from_trust: object, materialization: object) -> bool:
    """What a release-ready status requires of the three lineage facts recorded with it."""
    return mode == "seed" and trust_from_trust is True and materialization == FRESH_SEED


def selected_host_record(seed: object, host: object) -> dict | None:
    """The host record a seed lineage's capture selected for `host` (the receipt's own
    host), or None when the capture holds no host records (a single-host ledger in the
    legacy format).

    Raises StageReceiptError when it holds them and names no readable selected record, or
    one that is not `host`'s: the kind of the seed would then be unknown, and a status
    could not be checked against it. The capture selects the build host's record and no
    other (recreate_bootstrap.py capture_validated_seed_lineage). It also raises for a
    record of another kind that carries the fixed-point kind's admission or disclosure,
    which only that kind is admitted with."""
    authority = seed.get("authority") if isinstance(seed, dict) else None
    ledger = authority.get("seed_ledger") if isinstance(authority, dict) else None
    host_records = ledger.get("host_records") if isinstance(ledger, dict) else None
    if host_records is None:
        return None
    where = "bootstrap_lineage.validated_seed.authority.seed_ledger.host_records"
    records = host_records.get("records") if isinstance(host_records, dict) else None
    selected = host_records.get("selected_host") if isinstance(host_records, dict) else None
    record = records.get(selected) if isinstance(records, dict) and isinstance(selected, str) else None
    if not isinstance(record, dict) or not isinstance(record.get("schema"), str):
        raise StageReceiptError(f"{where} names no selected host record with a schema")
    if selected != host:
        raise StageReceiptError(
            f"{where}.selected_host is {selected!r}, not this receipt's host {host!r}: a seed capture "
            "selects its own build host's record and no other"
        )
    if record.get("host") != selected:
        raise StageReceiptError(
            f"{where}.records[{selected!r}] says host {record.get('host')!r}: the selected record is "
            "not that host's"
        )
    if record["schema"] != FIXED_POINT_HOST_RECORD_SCHEMA and (
        "root_disclosure" in record or record.get("admission_kind") == FIXED_POINT_ADMISSION_KIND
    ):
        raise StageReceiptError(
            f"{where}.records[{selected!r}] is a {record['schema']} record and carries the fixed-point "
            "kind's root_disclosure or admission_kind, which only that kind is admitted with"
        )
    return record


def fixed_point_lines(record: dict) -> list:
    """The two PROVENANCE lines of a seed whose selected host record is the fixed-point
    kind: its admission, and what its root_disclosure says of the root."""
    if record.get("admission_kind") != FIXED_POINT_ADMISSION_KIND:
        raise StageReceiptError(
            f"its seed's fixed-point host record has admission_kind {record.get('admission_kind')!r}, "
            f"not {FIXED_POINT_ADMISSION_KIND}"
        )
    disclosure = record.get("root_disclosure")
    if not isinstance(disclosure, dict):
        raise StageReceiptError("its seed's fixed-point host record carries no root_disclosure table")
    for key, value in FIXED_POINT_DISCLOSED:
        if disclosure.get(key) != value:
            raise StageReceiptError(
                f"its seed's fixed-point host record discloses {key} {disclosure.get(key)!r}; "
                f"the only value a fixed point is admitted with is {value}"
            )
    return [
        f"stage_receipt_seed_admission={FIXED_POINT_ADMISSION_KIND}",
        "stage_receipt_seed_root_disclosure="
        + " ".join(f"{key}={value}" for key, value in FIXED_POINT_DISCLOSED),
    ]


def unrecordable_character(text: str) -> bool:
    """Whether `text` holds a control character or an unpaired surrogate.

    By code point, never `str.isprintable()`: that asks the Unicode tables of whichever
    interpreter runs it, and promotion runs this file under the `python3` on PATH while
    the recreator needs 3.11 or newer. Measured 2026-10-12 on U+1FAE8 (assigned in
    Unicode 14): printable to python3.14, unprintable to /usr/bin/python3 3.9.6, so a
    build the recreator had accepted and stamped would have been refused by promotion
    after the whole build. These two sets are closed: General_Category Cc (U+0000-001F,
    U+007F-009F) and Cs (U+D800-DFFF) are immutable under the Unicode stability policy.
    recreate_bootstrap.py `_unrecordable_character` is the same three ranges.
    """
    return any(
        code < 0x20 or 0x7F <= code <= 0x9F or 0xD800 <= code <= 0xDFFF
        for code in map(ord, text)
    )


def invocation_errors(value: object) -> list:
    """Why `value` is not a `recreator_invocation` record (empty when it is one).

    The same rule as recreate_bootstrap.py `_recreator_invocation_errors`, which is the
    writer's; scripts/tests/recreate_bootstrap_test.py runs both on the same records.
    """
    if not isinstance(value, dict):
        return ["recreator_invocation is not an object"]
    errors = []
    if set(value) != INVOCATION_KEYS:
        errors.append(
            "recreator_invocation does not hold exactly the keys " + ", ".join(sorted(INVOCATION_KEYS))
        )
    if value.get("schema") != INVOCATION_SCHEMA:
        errors.append(f"recreator_invocation.schema is not {INVOCATION_SCHEMA}")
    if value.get("scope") != INVOCATION_SCOPE:
        errors.append(f"recreator_invocation.scope is not {INVOCATION_SCOPE}")
    argv = value.get("argv")
    if not isinstance(argv, list) or not all(isinstance(item, str) for item in argv):
        errors.append("recreator_invocation.argv is not a list of strings")
    elif any(unrecordable_character(item) for item in argv):
        errors.append("recreator_invocation.argv holds a control or unprintable character")
    return errors


def _is_hex(value: object, pattern) -> bool:
    return isinstance(value, str) and pattern.fullmatch(value) is not None


def llvm_source_identity_sha256(rows: object) -> str:
    """The one sha256 that stands for the LLVM source rows `rows`."""
    return hashlib.sha256(
        json.dumps(
            {"schema": LLVM_SOURCE_IDENTITY_SCHEMA, "paths": rows},
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ).hexdigest()


def _llvm_source_rows_errors(rows: object, where: str) -> list:
    if not isinstance(rows, list) or not rows:
        return [f"{where} is not a non-empty list"]
    paths = []
    for row in rows:
        if (
            not isinstance(row, dict)
            or set(row) != {"path", "type", "oid"}
            or not isinstance(row["path"], str)
            or not row["path"]
            or row["type"] not in ("tree", "blob", "commit")
            or not _is_hex(row["oid"], _COMMIT)
        ):
            return [f"{where} holds a row that is not a path, an object type and an object id"]
        paths.append(row["path"])
    if paths != sorted(set(paths)):
        return [f"{where} is not sorted by path without a repeat"]
    if LLVM_SOURCE_TREE not in paths:
        return [f"{where} does not name {LLVM_SOURCE_TREE}"]
    return []


def llvm_build_record_errors(value: object) -> list:
    """Why `value` is not an LLVM build record (empty when it is one).

    The same rule as recreate_bootstrap.py `_llvm_build_record_errors`, the writer's.
    """
    if not isinstance(value, dict):
        return ["the LLVM build record is not an object"]
    errors = []
    if set(value) != LLVM_BUILD_RECORD_KEYS:
        errors.append(
            "the LLVM build record does not hold exactly the keys "
            + ", ".join(sorted(LLVM_BUILD_RECORD_KEYS))
        )
    if value.get("schema") != LLVM_BUILD_RECORD_SCHEMA:
        errors.append(f"the LLVM build record's schema is not {LLVM_BUILD_RECORD_SCHEMA}")
    if not _is_hex(value.get("built_at_commit"), _COMMIT):
        errors.append("the LLVM build record's built_at_commit is not a full commit id")
    if not isinstance(value.get("host"), str) or not value.get("host"):
        errors.append("the LLVM build record's host is not a host triple")
    for key in (
        "source_identity_sha256",
        "bootstrap_config_sha256",
        "native_authority_sha256",
        "output_fingerprint_sha256",
    ):
        if not _is_hex(value.get(key), _SHA256):
            errors.append(f"the LLVM build record's {key} is not a sha256")
    row_errors = _llvm_source_rows_errors(
        value.get("source_paths"), "the LLVM build record's source_paths"
    )
    errors.extend(row_errors)
    if not row_errors and value.get("source_identity_sha256") != llvm_source_identity_sha256(
        value["source_paths"]
    ):
        errors.append(
            "the LLVM build record's source_identity_sha256 is not the identity of its source_paths"
        )
    return errors


def llvm_identity_errors(value: object, receipt: dict) -> list:
    """Why `value` is not the `llvm_identity` record of `receipt` (empty when it is).

    Its form and vocabulary, then its agreement with itself and with the receipt it is
    in. The same rule as recreate_bootstrap.py `_llvm_identity_errors`, the writer's.
    Nothing is compared with a file: what the record says of the build is the receipt's
    own statement, like its lineage.
    """
    if not isinstance(value, dict):
        return ["llvm_identity is not an object"]
    errors = []
    if set(value) != LLVM_IDENTITY_KEYS:
        errors.append(
            "llvm_identity does not hold exactly the keys " + ", ".join(sorted(LLVM_IDENTITY_KEYS))
        )
    if value.get("schema") != LLVM_IDENTITY_SCHEMA:
        errors.append(f"llvm_identity.schema is not {LLVM_IDENTITY_SCHEMA}")
    mode, provenance = value.get("mode"), value.get("provenance")
    if not isinstance(mode, str) or mode not in LLVM_PROVENANCE_OF_MODE:
        errors.append(
            f"llvm_identity.mode is {mode!r}, not one of " + ", ".join(LLVM_PROVENANCE_OF_MODE)
        )
    elif not isinstance(provenance, str) or provenance not in LLVM_PROVENANCE_OF_MODE[mode]:
        errors.append(
            f"llvm_identity.provenance is {provenance!r}; a record of mode {mode} says one of "
            + ", ".join(LLVM_PROVENANCE_OF_MODE[mode])
        )
    stated, reasons = value.get("identity_stated"), value.get("reasons")
    if not isinstance(stated, bool):
        errors.append("llvm_identity.identity_stated is neither true nor false")
    if not isinstance(reasons, list) or not all(isinstance(item, str) and item for item in reasons):
        errors.append("llvm_identity.reasons is not a list of sentences")
    elif isinstance(stated, bool) and stated == bool(reasons):
        errors.append(
            "llvm_identity.identity_stated and llvm_identity.reasons disagree: an identity is "
            "stated exactly when no reason against it is given"
        )
    rows, identity = value.get("source_paths"), value.get("source_identity_sha256")
    if rows == [] and identity is None:
        if stated is True:
            errors.append("llvm_identity states an identity without a source identity")
    else:
        row_errors = _llvm_source_rows_errors(rows, "llvm_identity.source_paths")
        errors.extend(row_errors)
        if not row_errors and identity != llvm_source_identity_sha256(rows):
            errors.append(
                "llvm_identity.source_identity_sha256 is not the identity of llvm_identity.source_paths"
            )
    output_dirs, fingerprint = value.get("output_dirs"), value.get("output_fingerprint_sha256")
    if not isinstance(output_dirs, list) or not all(
        isinstance(item, str) and item for item in output_dirs
    ):
        errors.append("llvm_identity.output_dirs is not a list of paths")
    if fingerprint is not None and not _is_hex(fingerprint, _SHA256):
        errors.append("llvm_identity.output_fingerprint_sha256 is neither null nor a sha256")
    record = value.get("build_record")
    if record is not None:
        errors.extend(llvm_build_record_errors(record))
    if errors:
        return errors

    def of_receipt(section: str, key: str) -> object:
        table = receipt.get(section)
        return table.get(key) if isinstance(table, dict) else None

    if mode == "external":
        # Never stated, and nothing of the checkout or its build directory stands beside
        # it as if it described that LLVM (see THE LLVM LINES in the module text).
        if stated:
            errors.append(
                "llvm_identity states the identity of an external LLVM: which sources an LLVM "
                "linked through --llvm-config was built from is never established"
            )
        if record is not None or fingerprint is not None or output_dirs:
            errors.append("llvm_identity of an external LLVM carries an in-tree output or build record")
        if rows != [] or identity is not None:
            errors.append(
                "llvm_identity of an external LLVM carries a source identity: this checkout's LLVM "
                "sources do not describe an LLVM linked through --llvm-config"
            )
    elif not stated:
        if record is not None:
            errors.append("llvm_identity quotes a build record for an identity it does not state")
    elif mode == "in-tree":
        if provenance not in ("built-in-this-run", "reused"):
            errors.append(f"llvm_identity states the identity of an LLVM whose provenance is {provenance}")
        if not output_dirs or fingerprint is None:
            errors.append("llvm_identity states the identity of an in-tree LLVM without its output")
        if record is None:
            errors.append("llvm_identity states the identity of an in-tree LLVM without a build record")
        else:
            for what, mine, recorded in (
                ("source identity", identity, record["source_identity_sha256"]),
                ("output", fingerprint, record["output_fingerprint_sha256"]),
                ("host", receipt.get("host"), record["host"]),
                (
                    "bootstrap config",
                    of_receipt("bootstrap_lineage", "config_sha256"),
                    record["bootstrap_config_sha256"],
                ),
                (
                    "native tool and SDK authority",
                    of_receipt("build_authority", "authority_sha256"),
                    record["native_authority_sha256"],
                ),
            ):
                if mine != recorded:
                    errors.append(f"llvm_identity's build record is for another {what} than this receipt's")
            if provenance == "built-in-this-run" and record["built_at_commit"] != of_receipt(
                "compiler", "source_commit"
            ):
                errors.append(
                    "llvm_identity says LLVM was built in this run, and its build record names "
                    "another commit than this receipt's"
                )
    else:
        errors.append("llvm_identity states the identity of an LLVM of unknown mode")
    return errors


def llvm_identity_unstated(toolchain: Path, *, receipt_path: Path | None = None,
                          receipt_sha256: str | None = None) -> str:
    """Why the stage at `toolchain` does not state which LLVM it carries; "" when it does.

    For a stage whose receipt `lines` accepted (or that has none). The three answers are
    the three things `--require-llvm-identity` refuses.
    """
    loaded = read(toolchain, receipt_path=receipt_path, receipt_sha256=receipt_sha256)
    if loaded is None:
        return (
            f"it carries no {RECEIPT_NAME}: no build-time stage evidence was recorded, "
            "or the receipt was removed"
        )
    receipt = loaded[1]
    if "llvm_identity" not in receipt:
        return (
            f"its {RECEIPT_NAME} holds no llvm_identity record: it was written by a recreator "
            "from before 2026-10-13"
        )
    record = receipt["llvm_identity"]
    if record["identity_stated"]:
        return ""
    return (
        f"its {RECEIPT_NAME} says the identity is not stated (mode {record['mode']}, provenance "
        f"{record['provenance']}): " + "; ".join(record["reasons"])
    )


def llvm_lines(receipt: dict) -> list:
    """The `stage_receipt_llvm*` lines for an accepted receipt.

    One line, `stage_receipt_llvm=not-recorded`, for a receipt without the record. Raises
    StageReceiptError for a record that is malformed or that contradicts itself or the
    receipt. An identity that is not stated is recorded as that, under any status word:
    the word does not depend on the LLVM (see the module text).
    """
    if "llvm_identity" not in receipt:
        return [f"stage_receipt_llvm={LLVM_NOT_RECORDED}"]
    record = receipt["llvm_identity"]
    problems = llvm_identity_errors(record, receipt)
    if problems:
        raise StageReceiptError("; ".join(problems))
    # What the source tree and the build directory say is written beside an in-tree LLVM
    # only (THE LLVM LINES in the module text). An external record holds none of it
    # (llvm_identity_errors); a record of mode unknown that the recreator wrote from
    # 381ac1ea0d until the follow-up of 2026-10-13 holds the checkout's source ids, which
    # may not describe the LLVM the stage links, and they are not carried into a seal.
    of_tree = record if record["mode"] == "in-tree" else {}
    rows = of_tree.get("source_paths") or []
    build_record = of_tree.get("build_record")
    return [
        f"stage_receipt_llvm={record['mode']}",
        "stage_receipt_llvm_identity=" + ("stated" if record["identity_stated"] else "not-stated"),
        f"stage_receipt_llvm_provenance={record['provenance']}",
        f"stage_receipt_llvm_source_sha256={of_tree.get('source_identity_sha256') or LLVM_NOT_RECORDED}",
        "stage_receipt_llvm_source_tree="
        + next((row["oid"] for row in rows if row["path"] == LLVM_SOURCE_TREE), LLVM_NOT_RECORDED),
        "stage_receipt_llvm_built_at_commit="
        + (build_record["built_at_commit"] if build_record is not None else LLVM_NOT_RECORDED),
        f"stage_receipt_llvm_output_sha256={of_tree.get('output_fingerprint_sha256') or LLVM_NOT_RECORDED}",
    ]


def _quoted_argument(argument: str) -> str:
    """One recordable argument as one shell word of printable ASCII."""
    if argument.isascii():
        return shlex.quote(argument)
    # $'...': a backslash and a quote are escaped, every non-ASCII character is its
    # UTF-8 bytes. `\xNN` takes at most two digits, so a digit after it is itself.
    word = []
    for character in argument:
        if character in "\\'":
            word.append("\\" + character)
        elif character.isascii():
            word.append(character)
        else:
            word.extend(f"\\x{byte:02x}" for byte in character.encode("utf-8"))
    return "$'" + "".join(word) + "'"


def quoted_arguments(argv: list) -> str:
    """The value of `stage_receipt_recreator_argv=` for a recorded argument list.

    `argv` has passed `invocation_errors`. See the docstring for the three forms.
    """
    if not argv:
        return ARGV_NONE
    quoted = " ".join(_quoted_argument(argument) for argument in argv)
    if quoted == ARGV_NOT_RECORDED:
        quoted = f"'{quoted}'"
    if len(quoted) > ARGV_QUOTED_MAX:
        return (
            f"(not quoted here: {len(quoted)} characters when quoted, more than "
            f"{ARGV_QUOTED_MAX}; read recreator_invocation.argv in {RECEIPT_NAME})"
        )
    return quoted


def _recorded_files(receipt: dict) -> list:
    """(what, recorded path, recorded sha256) for every file an accepted receipt binds."""
    rows = receipt.get("tools")
    if not isinstance(rows, list) or not rows:
        raise StageReceiptError("tools is not a non-empty list")
    out = []
    names = set()
    for index, row in enumerate(rows):
        if not isinstance(row, dict) or not isinstance(row.get("name"), str) or not row["name"]:
            raise StageReceiptError(f"tools[{index}] is not a named tool row")
        name = row["name"]
        if name in names:
            raise StageReceiptError(f"tools names {name} twice")
        names.add(name)
        where = f"tools[{name}]."
        sha = _digest(row, "sha256", where)
        if row.get("status") != "bound" or row.get("producer_sha256") != sha:
            raise StageReceiptError(
                f"{where}status is {row.get('status')!r} with producer_sha256 "
                f"{row.get('producer_sha256')!r}: not a tool bound to its producer"
            )
        out.append((f"tool {name}", row.get("path"), sha))
    compiler = _object(receipt, "compiler", "")
    out.append(("the compiler", compiler.get("path"), _digest(compiler, "compiler_sha256", "compiler.")))
    out.append((
        "the compiler's rustc name",
        compiler.get("compatibility_alias"),
        _digest(compiler, "compatibility_alias_sha256", "compiler."),
    ))
    alias = _object(receipt, "rustdoc_alias", "")
    out.append(("the rustdoc name", alias.get("path"), _digest(alias, "sha256", "rustdoc_alias.")))
    helper = _object(receipt, "proc_macro_helper", "")
    out.append(("the proc-macro helper", helper.get("path"), _digest(helper, "sha256", "proc_macro_helper.")))
    native = receipt.get("native_stage_tools", [])
    if not isinstance(native, list):
        raise StageReceiptError("native_stage_tools is not a list")
    for row in native:
        if not isinstance(row, dict) or row.get("name") != "rust-lld" or row["name"] in names:
            raise StageReceiptError("native_stage_tools has an unknown or duplicate tool")
        names.add(row["name"])
        sha = _digest(row, "sha256", "native_stage_tools.rust-lld.")
        llvm = receipt.get("llvm_identity", {})
        suffix = ".exe" if "windows" in str(receipt.get("host")) else ""
        prefix = str(PurePosixPath(receipt["stage_root"]).parent / "lld")
        if (row.get("status") != "bound" or row.get("producer_sha256") != sha
                or row.get("producer_kind") != "in-tree-llvm-project"
                or row.get("version_probe_ok") is not True
                or not isinstance(llvm, dict) or llvm.get("mode") != "in-tree"
                or llvm.get("identity_stated") is not True
                or row.get("llvm_source_identity_sha256") != llvm.get("source_identity_sha256")
                or row.get("llvm_output_fingerprint_sha256") != llvm.get("output_fingerprint_sha256")
                or row.get("path") != f"{receipt['stage_root']}/bin/rust-lld{suffix}"
                or row.get("producer_path") != f"{prefix}/bin/lld{suffix}"
                or not isinstance(llvm.get("output_dirs"), list) or prefix not in llvm["output_dirs"]):
            raise StageReceiptError("native stage tool rust-lld is not bound to its stated LLVM producer")
        out.append(("native tool rust-lld", row.get("path"), sha))
    return out


def _file_in_tree(toolchain: Path, stage_root: str, what: str, recorded: object) -> Path:
    """Where a path the receipt recorded (repository-root-relative) lies in `toolchain`."""
    prefix = stage_root + "/"
    if not isinstance(recorded, str) or not recorded.startswith(prefix):
        raise StageReceiptError(
            f"the path of {what} is not under the receipt's stage_root {stage_root}: {recorded!r}"
        )
    tail = recorded[len(prefix):]
    relative = PurePosixPath(tail)
    if (
        not tail
        or relative.is_absolute()
        or relative.as_posix() != tail
        or any(part in ("", ".", "..") for part in relative.parts)
        or "\\" in tail
        or unrecordable_character(tail)
    ):
        raise StageReceiptError(f"the path of {what} is not a plain relative path: {recorded!r}")
    return toolchain.joinpath(*relative.parts)


def lines(toolchain: Path, commit: str, *, receipt_path: Path | None = None,
          receipt_sha256: str | None = None, source_root: Path | None = None,
          frontend_component_path: Path | None = None,
          frontend_component_sha256: str | None = None) -> list:
    """The PROVENANCE lines for the stage receipt of `toolchain`, built at `commit`.

    Raises StageReceiptError for a receipt that is present and malformed, rejected by its
    own writer, or not this tree's.
    """
    selected = receipt_path is not None or receipt_sha256 is not None
    if selected and (source_root is None or not source_root.is_absolute()):
        raise StageReceiptError("an explicit receipt requires its original absolute source root")
    if not selected and source_root is not None:
        raise StageReceiptError("an original source root is only used with an explicit receipt")
    loaded = read(toolchain, receipt_path=receipt_path, receipt_sha256=receipt_sha256)
    if loaded is None:
        if frontend_component_path is not None or frontend_component_sha256 is not None:
            raise StageReceiptError("an explicit frontend component requires its original stage receipt")
        return ["stage_receipt=absent"]
    raw, receipt = loaded

    if receipt.get("schema") != RECEIPT_SCHEMA:
        raise StageReceiptError(f"schema is {receipt.get('schema')!r}, not {RECEIPT_SCHEMA}")
    status = receipt.get("status")
    if status == REJECTED_STATUS:
        errors = receipt.get("errors")
        first = f": {errors[0]}" if isinstance(errors, list) and errors and isinstance(errors[0], str) else ""
        raise StageReceiptError(
            "its own writer rejected this stage (status rejected" + first[:200] + "); "
            "a rejected receipt is not recorded as provenance"
        )
    if status not in ACCEPTED_STATUSES:
        raise StageReceiptError(
            f"status is {status!r}, not one of {', '.join(ACCEPTED_STATUSES)}"
        )
    if receipt.get("tool_binding_status") != "ready":
        raise StageReceiptError(
            f"status is {status} while tool_binding_status is {receipt.get('tool_binding_status')!r}"
        )
    if receipt.get("errors") != []:
        raise StageReceiptError(f"status is {status} while errors is not the empty list")
    if receipt.get("path_scope") != "repository-root-relative":
        raise StageReceiptError("path_scope is not repository-root-relative")
    stage_root = receipt.get("stage_root")
    mint_writer = receipt.get("writer") == "scripts/mint_and_prove_seed.sh"
    if not isinstance(stage_root, str) or not (
        _STAGE_ROOT.fullmatch(stage_root) or (mint_writer and _MINT_STAGE_ROOT.fullmatch(stage_root))
    ):
        raise StageReceiptError(f"stage_root is not build/<host>/stage<N>: {stage_root!r}")
    if selected:
        if toolchain.resolve(strict=True) != (source_root / stage_root).resolve(strict=True):
            raise StageReceiptError("selected receipt is not for this original producer stage")
        if receipt.get("host") != Path(stage_root).parent.name:
            raise StageReceiptError("selected receipt host differs from its original producer stage")

    lineage = _object(receipt, "bootstrap_lineage", "")
    if lineage.get("schema") != LINEAGE_SCHEMA:
        raise StageReceiptError(f"bootstrap_lineage.schema is not {LINEAGE_SCHEMA}")
    mode = lineage.get("mode")
    if not isinstance(mode, str) or mode not in LINEAGE_OF_MODE:
        raise StageReceiptError(
            f"bootstrap_lineage.mode is {mode!r}, not one of {', '.join(LINEAGE_OF_MODE)}"
        )
    trust_from_trust = lineage.get("trust_from_trust")
    wanted_status, wanted_trust = LINEAGE_OF_MODE[mode]
    if (
        not isinstance(trust_from_trust, bool)
        or (lineage.get("status"), trust_from_trust) != (wanted_status, wanted_trust)
    ):
        raise StageReceiptError(
            f"bootstrap_lineage says mode {mode} with status {lineage.get('status')!r} and "
            f"trust_from_trust {trust_from_trust!r}; a {mode} lineage is {wanted_status} with "
            f"trust_from_trust {wanted_trust}"
        )
    if lineage.get("errors") != []:
        raise StageReceiptError("bootstrap_lineage.errors is not the empty list")
    if receipt.get("trust_from_trust") is not trust_from_trust:
        raise StageReceiptError("trust_from_trust disagrees with bootstrap_lineage.trust_from_trust")
    seed = lineage.get("validated_seed")
    if mode == "seed":
        materialization = seed.get("materialization_status") if isinstance(seed, dict) else None
        if materialization not in SEED_MATERIALIZATIONS:
            raise StageReceiptError(
                "bootstrap_lineage.validated_seed.materialization_status is "
                f"{materialization!r}, not one of {', '.join(SEED_MATERIALIZATIONS)}"
            )
    elif seed is not None:
        raise StageReceiptError(f"a {mode} bootstrap_lineage carries a validated_seed")
    else:
        materialization = NO_SEED
    if status in RELEASE_STATUSES and not release_status_holds(mode, trust_from_trust, materialization):
        raise StageReceiptError(
            f"status is {status}, which needs a freshly materialized Trust seed, while its "
            f"lineage says mode {mode}, trust_from_trust {str(trust_from_trust).lower()}, "
            f"seed materialization {materialization}"
        )
    # The grade of a fixed-point seed: never a release status, and given to nothing else.
    host = receipt.get("host")
    host_record = selected_host_record(seed, host) if mode == "seed" else None
    # A host that is not a name cannot be told from a Linux one, so its seed is refused,
    # never read as from some other host (and a list is not hashable: `in` would raise).
    if mode == "seed" and host_record is None and not isinstance(host, str):
        raise StageReceiptError(
            f"its seed lineage holds no host record and its host is {host!r}, not a host name: "
            "whether only its own host record could admit that seed cannot be told"
        )
    if mode == "seed" and host_record is None and host in LINUX_SEED_HOSTS:
        raise StageReceiptError(
            f"its seed lineage on {host} holds no host record (a single-host seed "
            "ledger), which never admits a Linux host: a Linux seed is admitted only through its own "
            "host record (docs/PLAN.md PKG-S6), and the recreator refuses this one"
        )
    fixed_point = host_record is not None and host_record.get("schema") == FIXED_POINT_HOST_RECORD_SCHEMA
    if fixed_point and status in RELEASE_STATUSES:
        raise StageReceiptError(
            f"status is {status}, a release status, while its seed's selected host record is the "
            f"fixed-point kind, which is graded {UNPINNED_ROOT_STATUS} and never a release"
        )
    if status == UNPINNED_ROOT_STATUS and not fixed_point:
        raise StageReceiptError(
            f"status is {status}, which only a build from a seed whose selected host record is the "
            f"fixed-point kind is given; this receipt's seed is "
            + (f"a {host_record.get('schema')} record" if host_record is not None else "no such record")
        )
    if status == UNPINNED_ROOT_STATUS and not release_status_holds(mode, trust_from_trust, materialization):
        raise StageReceiptError(
            f"status is {status}, which needs a freshly materialized Trust seed, while its "
            f"lineage says mode {mode}, trust_from_trust {str(trust_from_trust).lower()}, "
            f"seed materialization {materialization}"
        )
    seed_admission = fixed_point_lines(host_record) if fixed_point else []

    if not _COMMIT.fullmatch(commit):
        raise StageReceiptError(f"the commit this tree's compiler reports is not a full object id: {commit!r}")
    recorded_commit = _object(receipt, "compiler", "").get("source_commit")
    if recorded_commit != commit:
        raise StageReceiptError(
            f"it names source commit {recorded_commit!r}; this tree's compiler reports {commit}"
        )
    frontend = None
    if frontend_component_path is not None or frontend_component_sha256 is not None:
        if (selected or frontend_component_path is None or frontend_component_sha256 is None
                or not frontend_component_path.is_absolute()
                or frontend_component_path != toolchain / "FRONTEND-COMPONENT.json"):
            raise StageReceiptError("frontend selection must name this derived seal's explicit component and hash")
        helper = Path(__file__).resolve().parents[1] / "sdk_frontend_component.py"
        namespace = {"__name__": "stage_receipt_frontend_component", "__file__": str(helper)}
        exec(compile(helper.read_bytes(), str(helper), "exec"), namespace)
        try:
            frontend = namespace["installed_binding"](toolchain, commit, frontend_component_sha256)
        except (ValueError, OSError, KeyError, TypeError) as error:
            raise StageReceiptError(f"frontend component refused: {error}") from error
    files = _recorded_files(receipt)
    frontend_recorded = False
    files_verified = 0
    for what, recorded, sha in files:
        path = _file_in_tree(toolchain, stage_root, what, recorded)
        if frontend is not None and what == "tool targo-trust":
            if sha != frontend["original_sha256"] or path != toolchain / "bin/targo-trust":
                raise StageReceiptError("original receipt frontend differs from explicit component base")
            # This ONE original entry is attested as replaced, not claimed
            # to hash the installed bytes. Original bytes stay private with
            # MINT; explicit component authority checks the replacement.
            frontend_recorded = True
            continue
        try:
            if not stat.S_ISREG(os.stat(path).st_mode):
                raise StageReceiptError(f"{what} ({recorded}) is not a regular file in {toolchain}")
            actual = _file_sha256(path)
        except OSError as error:
            raise StageReceiptError(
                f"{what} ({recorded}) cannot be read in {toolchain}: {error.strerror or error}"
            ) from error
        if actual != sha:
            raise StageReceiptError(
                f"it records sha256 {sha} for {what} ({recorded}); the file in {toolchain} has {actual}"
            )
        files_verified += 1

    if frontend is not None and not frontend_recorded:
        raise StageReceiptError("component has no matching original frontend in stage receipt")

    if "recreator_invocation" in receipt:
        problems = invocation_errors(receipt["recreator_invocation"])
        if problems:
            raise StageReceiptError("; ".join(problems))
        argv = quoted_arguments(receipt["recreator_invocation"]["argv"])
    else:
        argv = ARGV_NOT_RECORDED
    llvm = llvm_lines(receipt)

    return [
        f"stage_receipt={RECEIPT_NAME}",
        f"stage_receipt_sha256={hashlib.sha256(raw).hexdigest()}",
        f"stage_receipt_schema={RECEIPT_SCHEMA}",
        f"stage_receipt_status={status}",
        f"stage_receipt_lineage_mode={mode}",
        f"stage_receipt_trust_from_trust={str(trust_from_trust).lower()}",
        f"stage_receipt_seed_materialization={materialization}",
        *seed_admission,
        f"stage_receipt_files_verified={files_verified}",
        *llvm,
        f"stage_receipt_recreator_argv={argv}",
        *(["stage_receipt_writer=scripts/mint_and_prove_seed.sh"] if mint_writer else []),
        *([f"stage_frontend_component_sha256={frontend['component_sha256']}",
           f"stage_frontend_qualification_sha256={frontend['qualification_sha256']}",
           f"stage_frontend_source={frontend['source']}",
           f"stage_frontend_original_sha256={frontend['original_sha256']}",
           f"stage_frontend_replacement_sha256={frontend['replacement_sha256']}",
           "stage_frontend_original_entry=attested-replaced-not-installed",
           "stage_frontend_replacement_files_verified=1"]
          if frontend is not None else []),
    ]


def check_receipt_destination(toolchain: Path, receipt_path: Path, destination: Path) -> None:
    """Refuse overlap before promotion creates or copies anything into its destination."""
    if (destination.is_symlink() or (os.path.lexists(destination) and not destination.is_dir())
            or destination.resolve().is_relative_to(toolchain.resolve())
            or toolchain.resolve().is_relative_to(destination.resolve())
            or receipt_path.resolve().is_relative_to(destination.resolve())):
        raise StageReceiptError("accepted receipt destination is not a distinct new seal")


def copy_selected_receipt(toolchain: Path, commit: str, source_root: Path,
                          receipt_path: Path, receipt_sha256: str, destination: Path) -> None:
    """Carry an accepted external audit only into a new seal, preserving the producer."""
    check_receipt_destination(toolchain, receipt_path, destination)
    if not destination.is_dir():
        raise StageReceiptError("new seal destination is absent")
    lines(toolchain, commit, receipt_path=receipt_path,
          receipt_sha256=receipt_sha256, source_root=source_root)
    raw, _ = read(toolchain, receipt_path=receipt_path, receipt_sha256=receipt_sha256)
    target = destination / RECEIPT_NAME
    if os.path.lexists(target) and not stat.S_ISREG(target.lstat().st_mode):
        raise StageReceiptError("copied stage receipt is not a regular file")
    # A new destination belongs exclusively to promotion. Do not follow a copied
    # link or open/truncate the original stage's hardlinked receipt in place.
    import tempfile
    fd, temporary = tempfile.mkstemp(prefix=".accepted-stage-receipt-", dir=destination)
    try:
        with os.fdopen(fd, "wb") as stream:
            stream.write(raw)
            os.fchmod(stream.fileno(), 0o644)
        os.replace(temporary, target)
    finally:
        if os.path.lexists(temporary):
            os.unlink(temporary)
    if read(destination)[0] != raw:
        raise StageReceiptError("accepted receipt changed while copying into the new seal")
    read(toolchain, receipt_path=receipt_path, receipt_sha256=receipt_sha256)


def main(argv: list) -> int:
    require_llvm_identity = False
    selected = {}
    usage = ("usage: stage_receipt_provenance.py [--require-llvm-identity] "
             "[--stage-provenance-receipt ABS --stage-provenance-sha256 SHA --source-root ABS] "
             "[--frontend-component ABS --frontend-component-sha256 SHA] "
             "TOOLCHAIN_DIRECTORY REPORTED_COMMIT")
    while argv and argv[0].startswith("-"):
        option = argv[0]
        if option == "--require-llvm-identity" and not require_llvm_identity:
            require_llvm_identity = True
            argv = argv[1:]
        elif option in ("--stage-provenance-receipt", "--stage-provenance-sha256", "--source-root", "--frontend-component", "--frontend-component-sha256"):
            if (option in selected or len(argv) < 2 or not argv[1] or argv[1].startswith("-")):
                print(usage, file=sys.stderr)
                return 2
            selected[option] = argv[1]
            argv = argv[2:]
        else:
            print(usage, file=sys.stderr)
            return 2
    # Options precede the operands. Anywhere else they are refused, never taken for an operand: in
    # the commit's place it was read as a commit, which a stage without a receipt never
    # compares, so `DIRECTORY --require-llvm-identity` printed `stage_receipt=absent` and
    # exited 0 without the check it names. An empty operand is refused too: as the
    # directory it was read as the current one (the review of the follow-up, 2026-10-13).
    if len(argv) != 2 or any(not operand or operand.startswith("-") for operand in argv):
        print(usage, file=sys.stderr)
        return 2
    original_keys = {"--stage-provenance-receipt", "--stage-provenance-sha256", "--source-root"}
    frontend_keys = {"--frontend-component", "--frontend-component-sha256"}
    if selected and set(selected) not in (original_keys, frontend_keys):
        print(usage, file=sys.stderr)
        return 2
    original_selected = bool(set(selected) & original_keys)
    frontend_selected = bool(set(selected) & frontend_keys)
    selection = ({"receipt_path": Path(selected["--stage-provenance-receipt"]),
                  "receipt_sha256": selected["--stage-provenance-sha256"]} if original_selected else {})
    original = {"source_root": Path(selected["--source-root"])} if original_selected else {}
    frontend = ({"frontend_component_path": Path(selected["--frontend-component"]),
                 "frontend_component_sha256": selected["--frontend-component-sha256"]} if frontend_selected else {})
    toolchain = Path(argv[0])
    if not toolchain.is_dir():
        print(f"stage_receipt_provenance: not a directory: {toolchain}", file=sys.stderr)
        return 2
    try:
        rendered = "\n".join(lines(toolchain, argv[1], **selection, **original, **frontend)) + "\n"
        unstated = llvm_identity_unstated(toolchain, **selection) if require_llvm_identity else ""
    except (StageReceiptError, OSError) as error:
        print(
            f"stage_receipt_provenance: {toolchain / RECEIPT_NAME} is not a receipt to record: {error}",
            file=sys.stderr,
        )
        return 1
    if unstated:
        print(
            f"stage_receipt_provenance: {toolchain} does not state which LLVM it carries: {unstated}",
            file=sys.stderr,
        )
        return 3
    # Bytes, so no locale decides how a recorded argument is written.
    sys.stdout.buffer.write(rendered.encode("utf-8"))
    sys.stdout.buffer.flush()
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
