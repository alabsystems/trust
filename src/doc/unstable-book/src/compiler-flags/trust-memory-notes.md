# `trust-memory-notes`

The tracking issue for this feature is internal to Trust.

------------------------

`-Z trust-memory-notes` (default: off) makes the Trust verifier report what it
retains while it verifies a crate:

- `trust: memory checkpoint after N compacted artifact slots: resident X GiB`,
  each time the resident size read at a body boundary crosses another 4 GiB;
- `trust: memory census: ...` once at crate end: how many bodies' cached
  verification artifacts were compacted after their verify pass, how many of
  those compactions came after the pass had already dropped its own handle
  (expected 0), how many compacted slots a later pass had to recompute
  (expected 0; the cache's `compacted_rehits`), how many of the compacted
  slots' VC contexts have been released, with the ones still alive as
  `context_alive_after_compaction=N` (expected 0: a compacted slot holds no
  context), how many bodies' contexts a pending import citation held past
  their verify pass, with the ones still held as `contexts_held_for_citation=N`
  (expected 0: every citation is amended, and its hold released, before the
  census) and the most held at once, the resident size then, and the highest
  resident size read at a body boundary. That figure is sampled, not the kernel's peak: a spike inside
  one body that is gone by its end is not seen.

The notes are a measurement, never a verdict. They are off by default because
the resident size is a property of the host (its allocator, its page size, what
else the process mapped), so a compile's diagnostics would otherwise depend on
the machine that ran it: a ui test that happened to cross 4 GiB would print a
note on one box and not on another. Nothing about verification changes with the
flag; the per-body compaction it reports on always runs.

The option is dependency-tracked but does not enter the crate hash: it changes
what this compiler invocation prints, never what gets proved or what code is
emitted. There is no environment-variable spelling.
