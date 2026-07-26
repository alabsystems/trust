# cmp-mono-allwidths-2026-07-16 — full-int-width breadth of the sentinel-select lane

The W-ORD-MIN-VIA-CMP sentinel-select lane (1ac9552249) is
width-GENERIC (the kernel witness carries the unbounded `Int`, width-agnostic).
This corpus records breadth observations for `core::cmp::{min,max}` monomorphized over EVERY
primitive int width — including the 9 widths absent from the seed corpus
`cmp-mono-select-2026-07-16` (i8, i16, i128, isize, u16, u32, u64, u128, usize).

48 instances, ALL fully_faithful (see results.tsv):
- 24 leaves: `<{i8,i16,i32,i64,i128,isize,u8,u16,u32,u64,u128,usize} as Ord>::{min,max}`
- 24 forwarders: `std::cmp::{min,max}::<each width>` (via the existing tail-call lane)

Dumped by the W16 mono hook (TRUST_DUMP_MONO=1, no -O so the #[inline] leaf
bodies survive as standalone instances), graded by the release
`ff-gate-diagnose-2026-07-10` built WITH the sentinel-select lane. Pure
computation — no new recognizer/LLM clause; the landed width-generic lane
certifies the whole primitive-int min/max surface. Doubles as a soundness
stress-test: i8/u128/isize (widths unseen at authoring) all receive the same
classification, which is consistent with the width-agnostic witness. Honesty tier unchanged:
uninterpreted-but-total, shape-faithful (returns one of {self,other}), NEVER
value-faithful.

The table is an observational analyzer output, not proof authority. This
directory does not retain a source manifest, generator identity, or analyzer
receipt. Run `./validate-results.sh` with a freshly built current grader to
require exact 48-row reproduction before relying on it as regression evidence.
The validator does not fill the missing historical generation receipt. Nothing
in this directory may discharge a verification condition or mint a verdict by
itself.
