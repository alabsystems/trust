# nonzero2 — provenance

Harvested 2026-07-21 (`probe.rs`, this directory — compiled `--crate-type bin
--crate-name main` with `TRUST_DUMP_MONO=1`, which is what captures the core
`NonZero` monomorphizations alongside the probe's own wrappers).

## Re-frozen 2026-08-18 — the transparent-unwrap regeneration

All 29 dumps re-dumped from the SAME probe source with the stage1 `trustc` built
at the transparent-unwrap HEAD (`TRUST_SKIP_PREFLIGHT=1 python3 x.py build`,
then `trustc --edition 2021 --crate-type bin --crate-name main
-Ztrust-dump=mir:<dir> -Ztrust-policy=advisory probe.rs` with
`TRUST_DUMP_MONO=1`). The SELECTION is unchanged — the same 29 def_paths,
matched by the `def_path` inside each JSON (content-keyed filenames changed).

THE INTENDED DELTA, and the extractor's empirical control
(reports/r4-transparent-unwrap-2026-08-18.md): the four `NonZero::<W>::get`
bodies previously extracted as `Unsupported{CastKind::Transmute}` ("the
transmute gap" this directory's own header recorded). They now extract as the
value-exact field-projection read (`_0 := Copy(_1.0.0)`) under the
transparent-unwrap leg's evidence gates. Everything else is byte-equivalent
modulo spans/hashes.
