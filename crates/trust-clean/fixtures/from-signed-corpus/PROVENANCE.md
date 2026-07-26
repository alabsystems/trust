# from-signed-corpus — provenance

Twenty-eight files, copied byte-for-byte (never hand-transcribed) from
`crates/trust-clean/fixtures/census-rung2-2026-07-07/cast/` — itself real
`TRUST_DUMP_MIR` output from the real, unmodified `cast` 0.3.0 crates.io
source (see that directory's own `PROVENANCE.md`/`regenerate.sh` for the full
compile provenance: `~/.cargo/registry/src/**/cast-0.3.0/src/lib.rs`,
`--edition 2018`, prebuilt stage2 `trustc`).

This is the mission's gap-queue #2 follow-up #1 (`reports/honesty-and-ladder-2026-07-07.md`,
`fixtures/adt-return-corpus/PROVENANCE.md`'s own "out of scope" accounting): the
genuinely 3-OUTCOME `from_signed!` shape —

```rust
// cast-0.3.0/src/lib.rs, from_signed! macro body:
fn cast(src: $src) -> Result<$dst, Error> {
    Err(if src < $dst::MIN as $src {
        Error::Underflow
    } else if src > $dst::MAX as $src {
        Error::Overflow
    } else {
        return Ok(src as $dst);
    })
}
```

which lowers to a CHAINED guard (two sequential single-target `SwitchInt`s, the
first's FALSE edge feeding the second switch — an if/else-if/else ladder, not
the flat 2-arm `if/else` the ORIGINAL `adt-return-corpus` gap closure covers)
rather than the flat 2-arm `if/else` `sem_adt_return_shape_of` recognizes. The
new sibling recognizer `mirsem::sem_adt_return_shape_of_chain` +
`SemAdtReturn3` + the kernel-checked witness `trustir_adt::check_adt_return3_refinement`
close this shape: each real MIR arm resolves WALK-LOCALLY (module doc in
`mirsem.rs` above `sem_adt_return_shape_of_chain`) since the Underflow/Overflow
arms both funnel through a SHARED "wrap in `Err`" sink block, writing a common
payload temp differently per incoming edge — a shape the ORIGINAL 2-arm
recognizer's whole-body single-writer payload search would (rightly) decline
as multiply-assigned.

## Selection — a structural scan, independent of the macro's own source text

A Python scan of the full `census-rung2-2026-07-07/cast/` dump set (202 real
functions) for the EXACT structural shape (exactly TWO single-target
`SwitchInt` terminators — `targets == [(0, _)]` — anywhere in the function)
found these 28 files: 18 in `mod _64` + 10 in `mod _x128`, matching
`adt-return-corpus/PROVENANCE.md`'s own independent macro-arrow count
("the genuinely 3-outcome `from_signed!` shapes... 18+10=28 across
`_64`+`_x128`... OUT OF SCOPE for \[the ORIGINAL 2-arm\] increment"). Every
file spans a DISTINCT `(src, dst)` integer-width pair the crate ships,
`from_signed!`'s own real invocation list (`i16⇒{i8,u8}`, `i32⇒{i8,i16,u8,u16}`,
`isize⇒{…}`, `i64⇒{…}` for `_64`; `i128⇒{i8,i16,i32,i64,isize,u8,u16,u32,u64,usize}`
for `_x128`) — both signed-to-narrower-signed AND signed-to-unsigned
destinations (both need the SAME double-bound-check shape against
`$dst::MIN`/`$dst::MAX` cast up to `$src`).

All twenty-eight measured `fully_faithful=1, via_trustir=1, kernel_rejected=0`
through the real production `prove_dump_dir` gate (see
`tests/from_signed_corpus.rs`).

See `reports/honesty-and-ladder-2026-07-07.md` (queue item #2) and
`fixtures/adt-return-corpus/PROVENANCE.md`'s "genuinely 3-outcome" accounting
for the gap this fixture closes.
