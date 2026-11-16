# cargo-fetch(1)
{{~*set command="fetch"}}
{{~*set actionverb="Fetch"}}
{{~*set target-default-to-all-arch=true}}
{{~*set multitarget=true}}

## NAME

cargo-fetch --- Fetch dependencies of a package from the network

## SYNOPSIS

`cargo fetch` [_options_]

## DESCRIPTION

If a `Cargo.lock` file is available, this command will ensure that all of the
git dependencies and/or registry dependencies are downloaded and locally
available. Subsequent Cargo commands will be able to run offline after a `cargo
fetch` unless the lock file changes.

If the lock file is not available, then this command will generate the lock
file before fetching the dependencies.

If `--target` is not specified, then all target dependencies are fetched.

## OPTIONS

### Fetch options

`--local-git-source-cache` _PATH_ seeds an absent, private Cargo home using only
the exact Git sources in an existing lockfile. It requires `--locked --offline`.
The donor must be an absolute canonical Cargo-home directory with its original
cache locks available. Repository configuration, refs, hooks, alternates,
checkouts, compiler tools and targets are not copied. Ordinary offline fetching
still validates and materializes the imported data.

Repeatable `--local-git-object-source` _URL_ _OBJECTS_DIR_ selects an absolute,
canonical standalone object directory for a locked or selected-submodule source
URL. It may be used alone or with the Cargo-cache option as a fallback for other
sources. Duplicate canonical URL bindings and unused bindings refuse. Enclosing
repository configuration, refs, grafts, hooks and checkouts are never read or
copied; object-directory alternates refuse. The standalone profile holds native
directory/read observations, not a repository or Cargo garbage-collection lock.
Object deletion, replacement or namespace changes detected by the capture/copy
bookends refuse before publication. All explicit input namespaces must be disjoint from the destination
before staging writes begin.

`--local-git-source-copy-budget` _BYTES_ limits cumulative streaming fallback
across all imported databases. It requires a source-data provider option and
accepts zero through 34359738368 (32 GiB); the default is 32 GiB, preserving the
existing profile. Zero requires successful native cloning for nonempty data.
Successful native clones do not consume the stream budget. The operation reports
observed clone file/byte and stream byte counts. These are logical data-transfer
counts, not physical-space accounting, a COW guarantee or a storage reservation;
private view metadata and output objects still need space. Original logical-view
and uncompressed-closure ceilings remain separate and unchanged.

`--local-git-source-preflight` requires a source-data provider and `--locked
--offline`. It runs the same expected-OID/type/hash/history and selected-submodule
traversal against private object views, without creating output object databases,
publishing the destination home or running ordinary fetch. Its JSON report names
observed counts and resolved child requirements; URL credentials are redacted.
The report is not reusable source validity, GC, SDK, execution or storage authority.
All ODB owners are dropped and final original-input/cache bookends checked before
the original producer removes its tracked private view entries. Small private
state metadata remains; the destination home stays absent. Failed validation
retains the existing quarantined evidence. Unknown/replaced entries or uncertain
cleanup refuse and retain remaining data. Cleanup supports only the fresh private
single-producer namespace, not arbitrary concurrent same-UID namespace replacement
or atomic unlink-by-inode.

This initial native macOS/Linux profile accepts full-revision sources with
complete commit ancestry, trees and blobs. Selected-tree submodules are derived
from regular `.gitmodules` blobs and exact gitlinks, recursively into the same
unpublished transaction. `update=none` skips child data; historical gitlinks stay
tree data. Both input profiles share limits of 64 source databases, one million
objects, 64 MiB per uncompressed object and 32 GiB each of object-view data and
uncompressed closure data. Includes, ambiguous declarations, unsupported paths, source cycles,
branch/tag/short-revision requests, unsupported Git indirections and changed or
unreadable inputs refuse before publishing the home. Registry data is not imported. Failed or
interrupted transactions retain private staging data; no restart adoption is
provided. The destination parent must be owner-private with no ACL grants. Errors
after the atomic publication explicitly report that the home was already published;
they do not roll it back. This operation grants no source provenance, SDK or execution authority.

{{#options}}
{{> options-target-tuple }}
{{/options}}

### Display Options

{{#options}}
{{> options-display }}
{{/options}}

### Manifest Options

{{#options}}
{{> options-manifest-path }}

{{> options-locked }}

{{/options}}

{{> section-options-common }}

{{> section-environment }}

{{> section-exit-status }}

## EXAMPLES

1. Fetch all dependencies:

       cargo fetch

## SEE ALSO
{{man "cargo" 1}}, {{man "cargo-update" 1}}, {{man "cargo-generate-lockfile" 1}}
