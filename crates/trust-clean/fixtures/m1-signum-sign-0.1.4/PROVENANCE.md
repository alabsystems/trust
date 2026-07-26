# signum-sign 0.1.4 — M1 wrapper-micro hunt fixture (2026-07-07)

**The find: a REAL published crates.io crate whose ENTIRE public API (1/1
public functions) certifies FULLY-FAITHFUL modulo 3 axioms through the real
`trust_clean::prove_dump_dir` pipeline, spec-free, TODAY.**

## Crate provenance (real, published, fetchable)

| field | value |
|---|---|
| crate | `signum-sign` |
| version | `0.1.4` (latest; not yanked) |
| source | `https://static.crates.io/crates/signum-sign/signum-sign-0.1.4.crate` |
| sha256 (verified against the crates.io API `version.checksum` field) | `887a8345877c4c1454d35034fcaf040fdebfe86688362674739824e12077ac9f` |
| downloads | 9,751 all-versions / 1,319 for 0.1.4 (crates.io API, 2026-07-07) |
| edition | 2021 (from the published Cargo.toml) |
| repository | <https://github.com/mangopanda455/signum> |
| description | "Adds the signum function to Rust" |

The published `src/lib.rs` is 11 lines — ONE public function, the whole
public API:

```rust
pub fn sgn(x: i128) -> i128 {
    if x > 0 {
        return 1;
    } else if x < 0 {
        return -1;
    } else if x == 0 {
        return 0;
    } else {
        return -256;
    }
}
```

Purity: no `unsafe`, no heap, no traits, no generics, no `std` usage at all
(trivially `no_std`-able source), zero dependencies. Branch-and-const-return
over `i128` — the `sign.json`-class nested-branch shape, one arm deeper.

## Pipeline verdict (REAL gate, unbounded, spec-free)

`sgn.json` is the real, unmodified `TRUST_DUMP_MIR` dump (never
hand-transcribed): `preconditions: []`, `postconditions: []`,
`contracts: []`, empty `spec` — NO annotation of any kind was added.
8 MIR blocks.

Measured with the checked-in isolation harness
(`crates/trust-clean/src/bin/census-2026-07-06.rs`, prebuilt
`crates/target/debug/census-2026-07-06` of 2026-07-06) over the production
`prove_dump_dir` gate, `TRUST_CENSUS_BUDGET_SECS=0` (UNBOUNDED — no
timeout-budget false negatives possible; the verdict ran to completion):

```
def_path  total inhabited ... safety_obligations safety_discharged fully_faithful via_trustir mirsem_fallback declined
sgn       1     1             0                  0                 1              1           0               0
```

**fully_faithful = 1, via_trustir = 1** — the live modulo-3 kernel gate, not
a structural classification. Run twice end-to-end (fresh compile each time;
the two dumps are byte-identical after JSON normalization — see
`VERDICTS.tsv` for both rows). Wall-clock was tens of minutes per run purely
from host contention (load ~155 on 12 cores at measurement time); the
verdict is a completed proof, not a timing artifact.

Scoreboard: **public_fns = 1, fully_faithful_now = 1 → 100% of the crate's
public API, pipeline-verified, spec-free.**

## Regeneration

`./regenerate.sh` — re-downloads the published tarball, verifies the sha256
against the pin above, recompiles with the prebuilt stage2 `trustc`
(`TRUST_DUMP_MIR`, `--edition 2021 --crate-type lib`),
and refreshes `sgn.json`. Method: the census method of
`reports/flagship-crate-census-2026-07-06.md`.

Historical provenance: the checked-in 2026-07-07 dump was originally made
with `-Zcontract-checks=yes`. That inherited exec-projection flag is now
retired for Trust-active compilations and did not affect this spec-free body;
the live script intentionally omits it.
