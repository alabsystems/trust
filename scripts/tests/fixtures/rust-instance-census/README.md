# Concrete-instance diagnostic census

`-Ztrust-instance-census=NEW.jsonl -Zchecksum-hash-algorithm=sha256` observes
the compiler's normal mono-item collection, independently of direct Trust-IR
lowering. It does not force collection on a metadata-only path. The separate
HIR census and scorecard remain unchanged.

The report keeps concrete generic instances, every current shim class, statics
and global assembly; actual collector roots and usage edges; CGU placements and
explicit unplaced items. The latter are real: an optimized unused public async
body may be collected without placement, as may eager drop glue. Neither
population is silently discarded. The 128-bit compiler fingerprint covers the
whole `MonoItem`, including instance kind and substitutions, but is a diagnostic
identity, not a cryptographic body/refinement certificate.

Version 2 also records dependencies encountered during the existing collector
visits: constant allocations and their provenance edges, static initializers,
vtable requests and every observed slot, symbolic-to-physical vtable allocations,
and resolved references retained before local-codegen filtering. Typed records
travel in the cached `items_of_instance` result; an enabled observer refuses a
missing payload. Used and mentioned passes have separate owners, and required
constants stay mentioned even during a used pass. Empty observed visits are
recorded explicitly. These diagnostic tables do not affect collection or CGU
placement.

Version 3 adds a separate owner and ordered occurrence population for the
collector's existing successful eager free-constant value scans. The typed
owner is the actual local constant definition, identified by its DefPathHash;
it is not a function instance, static, collected mono item or CGU member. An
observed scalar constant keeps an owner with zero dependency occurrences.
Root scans share allocation nodes with recursive visits, retaining distinct
scan occurrences even when multiple constants reference the same allocation.
The recursive used-owner population must still equal all collected mono items.
No additional constant evaluation, filtering, insertion or codegen decision is
performed for observation. A lazy collector has explicit empty root tables.

Allocation IDs are local to one compiler invocation. Distinct allocations with
equal contents remain distinct, and aliases retain the same ID. Instances and
vtables use full typed compiler fingerprints; their printed type descriptions
are not identity inputs. `collector_direct_call` reports the collector's dispatch
policy, which is not a count or classification of actual runtime calls.

The consumer checks both graphs, exact owner membership and placement populations,
typed endpoints, provenance flags, complete vtable slot populations, the raw
snapshot digest, source hashes, lane, footer and actual process exit. It still
accepts the exact version 1 and version 2 formats for historical reports, with
their original fields and gaps; version 3 fields are refused under old headers.
It always reports whole-program completeness as false. Allocation bytes and
codegen semantics, CTFE execution, eager-constant root dependencies, unvisited
allocations/vtables, expanded intrinsics, external implementations, indirect
runtime targets, backend synthesis, runtime/linker inputs, pre-optimization bodies
and full dependency/build input closure remain unmeasured. The broad eager-root
residual is retained pending actual validation of the bounded v3 increment;
type/generic skips, failed evaluations, associated constants, ADT/drop and
default-implementation root discovery remain outside these successful scans.
None of these versions can
supply G1 or replace the full admitted denominator.

Run structural and mocked orchestration tests:

```sh
python3 -B scripts/tests/rust_instance_census_test.py
python3 -B scripts/tests/rust_instance_census_live_test.py
```

After rebuilding the compiler containing the observer, run the retained live
controls in an owned aterm with an explicit Trust binary and new external output:

```sh
python3 -B scripts/tests/rust_instance_census_live.py \
  --trustc /ABSOLUTE/CANDIDATE/build/host/stage2/bin/trustc \
  --out /ABSOLUTE/EXTERNAL/NEW_DIRECTORY
```

Nine cases cover the unchanged-output control, lowering on/off, metadata-only
non-collection, optimized/eager unplaced roots, create-only output collision,
missing checksum requirement and a real type error. All requested artifacts and
raw diagnostics are retained. Empty, interrupted, failed or missing cases cannot
pass. The harness binds its launcher, local drivers, sources and checker, not the
complete dynamic/sysroot closure; use a separately sealed toolchain harness for
acceptance evidence. Mock tests invoke no compiler and establish no live count.

Version 2 and 3 comparisons rename allocation IDs by first occurrence through a
bijection, preserving distinct nodes and aliasing. They never deduplicate by
contents. A warm-cache control must reuse the exact census path, options and
incremental directory: preserve the previous report elsewhere and remove only
that owned report before rerunning. Changing the census path invalidates the
incremental cache and cannot demonstrate cached-query replay. Structural and
mocked tests alone do not establish that a rebuilt compiler captured or replayed
these dependencies.

`eager-const.rs` is a separate unexecuted root-discovery fixture for the v3
increment. Compile it as an rlib, explicitly selecting `-Clink-dead-code=no`
(lazy) or `-Clink-dead-code=yes` (eager), with census observation on and off.
The unused generic `identity::<u8>` should be a root only in eager collection;
the `ROOT` owner must describe its actual value scan without changing selected
items, roots, placement or code. `--cfg empty_root` adds a successful scalar
scan with no dependencies, `--cfg alias_root` adds a second distinct constant
owner, and `--cfg use_root` supplies an ordinary use for the lazy comparison.
These are source-derived expectations pending a bound rebuilt compiler run,
including existing cold/warm recursive-query controls. They are not a claim
that the reader can recover omitted whole constant owners from missing data.
