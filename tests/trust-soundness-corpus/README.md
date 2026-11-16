<!-- Copyright 2026 Andrew Yates -->
<!-- Author: Andrew Yates <andrewyates.name@gmail.com> -->
<!-- Licensed under the Apache License, Version 2.0 -->

# trust-soundness-corpus (SBC M0.5)

The adversarial corpus of
`docs/plans/2026-10-08-soundness-by-construction.md`
(M0.5, rule R8). Every entry is a program whose claimed property is **false**,
shown false by running it, beside a correct twin. The runner asks every
verdict-issuing verifier it can find for a verdict on both.

```sh
python3 scripts/trust-soundness-corpus.py                      # every entry, every verifier found
python3 scripts/trust-soundness-corpus.py --filter '^h[123]-' --verifiers trustc-default,trustc-certify
python3 scripts/trust-soundness-corpus.py --json out.json      # the full table, machine-readable
```

**The gate is NON-BLOCKING until it judges 0 proved reproducers.** The M0.1 row is
recorded (`docs/DECISION_QUEUE.md`, 2026-10-15): the corpus joins the pre-push hook
the day it is green, which is SBC M0's exit, and not before. Its one `--strict` caller is the advisory (`required=false`) `slow`
row `oracle.soundness-corpus` in `tests/run_trust_comprehensive_harness.sh`, in no
push profile. A run that reports a FALSE-PROVED is still a false proof.

**The runner fails closed.** A verdict is *refused* only when the verifier answered
and said no: a trustc row that carries the claim and is not proved, Clean's
`verification: FAILED`, a trust-vc or trust-wp verdict read from its own output. A
missing, crashing or timed-out verifier, a compile with no rows for the function, and
an obligation anchor that matches no row (anchor-miss) or rows at two places
(ambiguous) are ERROR, never a refusal. So is a verifier that prints an answer and
then crashes: whatever it printed is no verdict, except that a proof a reproducer was
claimed to have stays a proof (a crashed twin is never one). For modes that read
rows, a trustc record set with malformed `TRUST_JSON`, repeated function envelopes,
missing row arrays or inconsistent declared row totals is also ERROR, never a
refusal or a twin proof; an already observed reproducer proof remains a false
proof. Live row outcomes must use Trust's canonical wire spelling, and JSON must
contain no nonfinite numeric constants. A `trust-vc-driver` record set requires
one trailing `TRUST_VC_DRIVER_SUMMARY` with exact total and per-verdict counts,
the six declared wire outcomes and unique function records. The normal exit must
also match those records: 1 with any Refuted, Unknown or Error, otherwise 0.
Missing, malformed,
duplicate, contradictory or ambiguous target records are ERROR, never a refusal
or twin proof. An individually identified reproducer's observed `Verified` claim
remains a false-proof observation even if another record, the summary or a later
crash makes the complete output unusable. Under `--strict` the exit status is 1
when any requested cell is

* FALSE-PROVED or KNOWN-FALSE-PROVED (a reproducer proved, including one with a `known_open` marker),
* XFIXED (a `known_open` reproducer cleanly REFUSED: retire the marker; an ERROR never
  counts as fixed, it is `ERROR(known-open)` and also fails),
* SKIPPED (a requested verifier that could not run),
* ERROR, unless it is a refusal of an unsupported construct that the entry whitelists
  for that verifier and side in `expected_refusal`, with the refusal's exact text,
  and that the verifier gave as its answer (exit 0, verdict `error`): the same text
  in the output of a verifier that crashed does not count,
* TWIN-LOST not recorded in `known_twin_lost` (a twin expected proved and not proved,
  at EVERY opt level the entry runs), or
* a witness that is not confirmed,

and when no verifier judged any reproducer (every cell skipped or n/a): a run that
judged nothing is not a pass (VACUOUS).

KNOWN-FALSE-PROVED remains a distinct diagnostic label but always fails `--strict`.
A recorded TWIN-LOST retains its precision-loss policy and is tolerated by `--strict`;
it is an open bug with a pointer, never a passing cell.

```sh
python3 scripts/trust-soundness-corpus.py --strict --timeout 600   # exit 1 on any of the above
python3 scripts/trust-soundness-corpus.py --self-test              # the runner against fake verifiers
```

`--self-test` (`selftest/fake_verifier.py`) plays every verifier in turn as missing,
`/usr/bin/false`, crashing (SIGSEGV), crashing after it has printed the oracle's
answer, hanging (ended by `--timeout`), always-proved, always-refused and an oracle
that answers what each entry records; trustc also as `anchor-miss` (rows for every
function, none of them the anchored one). It asserts that the first five, and
anchor-miss, exit 1 with no passing cell, that always-proved turns every reproducer
FALSE-PROVED, that always-refused turns every twin expected proved TWIN-LOST (so every
entry without a `no_control` reason has a real control), and that the oracle exits 0.
It checks the witnesses with a compiler whose witness binaries print the wrong text and
an `ay` whose models are perturbed or that answers `unsat`. With a real trustc it
proves the anchors live: a wrapper that rewrites only each entry's anchored row (to
proved for a reproducer, failed for a twin) must turn every reproducer FALSE-PROVED and
every twin TWIN-LOST, and one that makes every other row proved and the anchored
reproducer row failed must leave the reproducer not proved and the twin proved.

This corpus is not `tests/trust-falsification/`. That gate checks that buggy
*variants* of proved fixtures are refuted under `certify`. This one holds the false
proofs that were actually found, each with a witness, and runs them against every
verifier, not only trustc.

## What an entry is

One directory per entry, `entries/<id>/`, with `entry.json` and its files.

| File | What it holds |
|---|---|
| `entry.json` | the claim, the origin, what to ask each verifier, the witness, and the expected verdicts |
| `src.rs` | the reproducer and the twin, as two functions in one crate (Rust and trust-wp entries) |
| `witness.rs` | a `main` that runs the reproducer on the witness input, compiled by trustc with `-Ztrust-verify=off` (no verification claim) |
| `repro.json`, `twin.json` | Alethe certificates (`clean cert verify-external` format) for SMT entries |
| `dep.rs`, `twin.rs` | extra crates or a separate twin source, where an entry needs them |

`entry.json` fields:

* `id` (the directory name), `class` (the hazard or DQ row), `title`, `origin` (the
  commits, tests and KNOWN_HAZARDS or DECISION_QUEUE rows it comes from).
* `lang`: `rust` (trustc lanes, trust-vc-syn, trust-vc-mir), `creusot` (trust-wp),
  `trust-vc` (trust-vc's own contract surface) or `smt` (Clean).
* `reproducer`, `twin`: `function` names the function in `src.rs`. For the trustc
  lanes, `obligation` is the anchor that selects the rows carrying the claim: `kind`
  (a row kind or its prefix, such as `overflow` for `overflow:add`) and `at` (the
  first source line at or after `fn <function>` that contains this text) or
  `message` (text of the row's assertion message, for a row trustc places outside the
  entry's source, such as the per-panic row at `core/src/panic.rs:62`). Every
  obligation side needs `kind` and an anchor. No matching row is ERROR (anchor-miss)
  and matching rows at two places are ERROR (ambiguous), never a refusal; a twin is
  proved only when every matching row is. `mode` is `obligation` (the default),
  `assumption-kept` (an `#[trust::assume_total]` skip is honoured: its rows are the
  assumption alone and nothing revokes it; an empty row set is ERROR) or
  `build-accepted` (the compile exits 0; exit 1 is a refusal only with an `error:`
  diagnostic, otherwise ERROR). SMT entries name `cert` instead, and `construct`, the
  triggering construct, which both problems must contain.
* `witness`: `main`, `input`, `observed` (text the run must print; it may not be
  empty), `exit` (its status, required; 101 is a Rust panic, -11 a SIGSEGV). The
  entry check refuses a witness without them, since an empty `observed` is in every
  output and a missing `exit` matches any status. An SMT witness (`solver: ay`,
  `expect: sat`) is AY's model after every
  `check-sat` of the reproducer's problem, evaluated against every assertion and
  assumption by the runner's own evaluator (`smt_model_check`, no code shared with
  AY); `sat` alone confirms nothing.
* `expect`: per verifier, `reproducer` is always `not-proved`. `twin` is `proved`
  (the default) or `not-in-fragment` where that verifier cannot express the twin.
  `{"n/a": "<reason>"}` takes the entry away from a verifier that cannot read it.
* `expected_refusal`: per verifier and side, the exact text of a construct refusal
  (an ERROR that is the verifier saying "I do not support this"), which then counts
  as a refusal. Any other ERROR fails `--strict`.
* `known_open`: per verifier, a pointer to the open bug. A known-open reproducer that
  is proved is reported as KNOWN-FALSE-PROVED, which is still a false proof and
  always fails `--strict`. One that is cleanly REFUSED is reported as XFIXED, so the marker gets
  retired; an ERROR is `ERROR(known-open)`, never a fix.
* `known_twin_lost`: per verifier, a recorded precision loss on the twin (reported,
  tolerated by `--strict`). `no_control`: why no verifier can prove the twin (every
  other entry must have one that does).
* Optional: `opt_levels` (default `["0"]`; a reproducer is proved if ANY level
  proves it, a twin only if EVERY level does), `edition`, `rustc_flags`, `aux`
  (dependency crates built with verification off).

## Adding an entry

1. Copy an entry of the same `lang` to `entries/<new-id>/` and set `id` to the
   directory name.
2. Put the reproducer and a correct twin in `src.rs`. Write `witness.rs`, run it, and
   copy what it prints into `witness.observed` and its exit status into `exit`.
3. Point `reproducer` and `twin` at the rows that carry the claim.
4. Run `python3 scripts/trust-soundness-corpus.py --filter '^<new-id>$'`. A twin that a
   verifier cannot express gets `not-in-fragment` for that verifier, with the reason
   in the entry. A false proof that is open today gets a `known_open` pointer.

## Verifiers

| Name | What it runs | Configure |
|---|---|---|
| `trustc-default` | `trustc -Ztrust-verify=on -Ztrust-verify-output=json` (default policy), rows read from `TRUST_JSON` | `TRUSTC`; default the atpkg store's `current` trustc |
| `trustc-advisory` | the same with `-Ztrust-policy=advisory`, the lane that elides checks | |
| `trustc-certify` | the same with `-Ztrust-policy=certify`. `targo trust check` and `targo trust certify` drive these compiler lanes | |
| `trust-wp` | trust-wp's own adversarial harness, through `adapters/trust_wp_adapter.py`, which reads credits with trust-wp's own parsers | `TRUST_WP_DIR` (default `first-party/trust-wp`), `TRUST_WP_PYTHON` (3.11 or later), `TRUST_WP_HARNESS_TARGET_DIR` |
| `trust-vc-syn` | `trust_vc_core::verify_function_from_file`, through `adapters/trust-vc-syn` | `TRUST_VC_DIR` (default `first-party/trust-vc`), or a built adapter in `TRUST_VC_SYN_ADAPTER` |
| `trust-vc-mir` | `trust-vc-driver` (the THIR lane), from its `TRUST_VC_DRIVER_RESULT` lines | `TRUST_VC_MIR_DRIVER`, `TRUST_VC_MACROS` |
| `clean-external` | `clean cert verify-external` | `CLEAN_BIN` (a `clean` built with `--features clean/carcara-verify`); default `clean` on PATH |

A verifier that cannot be found or built is SKIPPED, with the reason. A skip is never
a pass.

## Census, 2026-10-14

35 entries: 18 plain Rust, 1 in trust-vc's contract surface, 8 trust-wp (Creusot), 8
SMT. Measured with the fail-closed runner on trust `origin/main` (2026-10-14), with
these verifiers:

* trustc: the atpkg store toolchain 9192 (`rustc 1.99.0-dev (321aaeda7 2026-09-17)`),
  the sealed toolchain users install. No compiler built from main was available to
  this run.
* trust-wp: `origin/main` `3501a180` (D-240 `7726ea81` is the last fix in it), its
  harness built with the same store toolchain.
* trust-vc: trust's pin `a224165545` (the syn adapter). No `trust-vc-driver` was built.
* Clean: trust's pin `46d887ef9`, built with `--features clean/carcara-verify`.

| Verifier | Entries it reads | Reproducers proved (false / known-open) | Refused | Construct refusals (whitelisted ERROR) | Other ERROR | Skipped | Twins proved | Twins not-in-fragment | Twins lost |
|---|---|---|---|---|---|---|---|---|---|
| trustc-default | 18 | 14 (14 / 0) | 4 | 0 | 0 | 0 | 17 | 0 | 1 (known) |
| trustc-advisory | 18 | 14 (14 / 0) | 4 | 0 | 0 | 0 | 17 | 0 | 1 (known) |
| trustc-certify | 18 | 14 (14 / 0) | 4 | 0 | 0 | 0 | 17 | 0 | 1 (known) |
| trust-wp | 8 | 0 | 8 | 0 | 0 | 0 | 8 | 0 | 0 |
| trust-vc-syn | 17 | 0 | 7 | 10 | 0 | 0 | 4 | 13 (7 of them refusals) | 0 |
| trust-vc-mir | 1 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0 |
| clean-external | 8 | 0 | 8 | 0 | 0 | 0 | 4 | 4 (no-control) | 0 |

All 35 witnesses are confirmed (27 native runs, 8 AY models checked). `--strict` exits
1: the 42 FALSE-PROVED trustc cells and the SKIPPED trust-vc-mir lane.

How to read it:

* **trustc (store 9192) proves 14 reproducers that panic natively**, in all three
  lanes: vac, A and A′ (`path-guard-value`, `-range`), H1, H2, H3, al02,
  LAUNDERED-ALIAS-ELIDE-1, CONTRACT-NS-1, CAST-SIGNED-CLAMP-UB-1, TRIP-ZERO-PRODUCT-1,
  TRIP-DRIVER-1, B (OPAQUE-SCALAR-ID-1) and INSTANCE-WALK-1. In 12 the proved row is
  kernel-certified; vac's is not, and INSTANCE-WALK-1's claim is an
  `assume_total` assumption the compiler keeps. Each is fixed on main after the seal
  was cut (2026-09-17; INSTANCE-WALK-1 by `da8ff46046` on 2026-10-14), so this is the
  state of the toolchain users install, not of main, and no entry is marked known-open
  for it. To measure main, run with `TRUSTC=<a stage 1 built from main>`.
* **B was reported refused by the first census, wrongly.** Its anchor named the
  `panic!` line, while trustc puts the per-panic row at `core/src/panic.rs:62`; the old
  runner counted the anchor-miss as a refusal. Anchored at that row's message, the
  store proves and kernel-certifies it while noting the opaque scalars as unsupported
  MIR. That is the false proof `crates/trust-vcgen/tests/opaque_scalar_identity_realmir.rs`
  pins.
* trustc refuses TRIP-INIT-CYCLE-1, TRIP-MID-TEST-1, UNION-SIBLING-WRITE-1 and the
  trust-vc untyped-literal shape. `cast-signed-clamp-ub`'s twin is proved at -O0 and
  refused at -O1 (a recorded precision loss; a twin must be proved at every level).
* trust-vc-syn's 10 construct refusals are recorded per entry with their text: writes
  through dereferenced and raw pointers, `asm!`, `panic!`, unions, the ambiguous
  multi-path return, and the native `ensures` grammar of a sibling helper. vac and
  INSTANCE-WALK-1 are n/a to it (trustc's native `ensures` syntax is not Rust, and
  INSTANCE-WALK-1's claim is an `assume_total` assumption kept, for which trust-vc has
  no verdict).
* trust-vc-mir verifies only functions that carry `trust_vc` contract markers, so the
  17 plain-Rust entries are statically n/a. The one `trust-vc` entry is SKIPPED: no
  `trust-vc-driver` was built (`TRUST_VC_MIR_DRIVER`).
* Clean main proves 4 of the 8 SMT twins. The other 4 constructs (a declared `and`,
  `ite` or `|false|`; `push`/`pop`) are refused outright by Clean main, twin
  included, so those entries carry `no_control`. Every SMT twin contains its entry's
  construct, and no two are byte-identical.
* trust-wp main refutes all 8 reproducers and verifies all 8 twins: D-238 (`2f3738026`)
  and D-239 (`08ce51305`) closed the six entries that were known-open when the corpus
  was written (macro hygiene mh1, mh2, mh4, mh5; closure contracts cc1, cs1), so their
  markers are retired. cc1 and cs1 are refused as an ambiguous clause (verdict
  `unknown`), not refuted. Their twins were rewritten to capture `x` (`let _c = x;`):
  written the reproducer's way (`let _ = x;`, which does not capture), trust-wp main
  refused the twin for the same reason.

The same SMT entries against the store Clean (`store/clean/8606`, built 2026-09-16)
show that the runner catches a pre-fix reader: it certifies 4 of the 8 satisfiable
problems (`clean-q04-push-pop`, `clean-b09-check-sat-assuming`,
`clean-r1-named-reuses-declared`, `ay-mirror-false-quoted`) and loses 2 twins. Clean
main refuses all 8.

The runner's output is in `evidence/2026-10-14-{final,store-clean,mutation,selftest}.txt`,
with home and temporary paths rewritten to `<home>` and `<tmp>`.

## Self-test, 2026-10-14

`--self-test` passed: 206 checks. The verdict rules on synthetic entries (a
known-open reproducer proved, refused, errored or skipped; the build-accepted exits;
an empty assumption-kept result), which no corpus entry reaches today. Every fake
family (trustc for the three lanes, trust-vc-syn, trust-vc-mir, Clean, trust-wp) in
each of the eight modes, and trustc as `anchor-miss` too; 31 entries lose their twin
under an always-refusing verifier (the other 4 are `no_control`); a run that judges
nothing is VACUOUS; a wrong witness and a perturbed AY model are both rejected; and
against the store trustc, all 17 obligation-anchored Rust entries pass both liveness
rewrites. `late-crash` has teeth: under the earlier rule, which matched a whitelisted
refusal's text anywhere in an ERROR's detail, a trust-vc-syn adapter that printed
al02's whitelisted refusal and then died on SIGSEGV read `ok(refusal)` on both sides.

## Known open (KNOWN-FALSE-PROVED today)

None. Every proved reproducer in this census is a FALSE-PROVED of the store toolchain
that main has fixed (above).

## Mutation check: the runner flags a reverted fix

trust-wp `aee6e8f2` (D-237) was reverted on top of `04c2aed927`, the trust-wp commit
right after it, on a private scratch branch that was never pushed and was deleted
after the run (`scratch/sbc-mutation-revert-aee6e8f2`, commit `8ad1e13ee`). That tree was
the trust-wp verifier (`TRUST_WP_DIR`, harness on the store toolchain 9192), and
`--filter '^wp-'` was run on 2026-10-14. The run was then repeated in a fresh tree
(the same base with the same revert left uncommitted in the working tree), with the
harness toolchain set only by the runner (`$CARGO`, `$RUSTC`), and gave the same
table:

```sh
git -C <trust-wp clone> worktree add --detach <tree> 04c2aed927
git -C <tree> revert --no-commit aee6e8f2      # <tree>/../ay and ../clean: trust's first-party/ay, clean
TRUST_WP_DIR=<tree> python3 scripts/trust-soundness-corpus.py --verifiers trust-wp --no-witness --filter '^wp-'
```

| Entry | trust-wp main `3501a180` | aee6e8f2 reverted on `04c2aed927` |
|---|---|---|
| `wp-d237-shadowed-namesake` (rs1) | refused; twin va2 proved | **FALSE-PROVED** (`rs1: 1 proof_assert verified`); twin va2 lost |
| `wp-d237-shadowed-param-copy` (pa2) | refused; twin va1 proved | **FALSE-PROVED** (`pa2: function verified, 1 proof_assert verified`); twin proved |
| `wp-open-macro-hygiene-mh1`, `-mh2`, `-mh4`, `-mh5` | refused; twins proved | **FALSE-PROVED**; twins lost |
| `wp-open-closure-contract-cc1`, `-cs1` | refused (ambiguous clause); twins proved | **FALSE-PROVED** (`function verified`); twins proved |

The two D-237 entries match the teeth aee6e8f2 itself recorded: before D-237, rs1 and
pa2 VERIFIED and the control va2 FAILED. The other six need D-238 and D-239, which that
tree lacks too.

A single revert on main does not reopen them. With D-239 (`08ce513054`) alone reverted
on trust-wp main `3501a180`, all 8 reproducers are still refused and all 8 twins
proved: main also carries D-240 (`7726ea81`, after D-239), and which of the two refuses
each shape was not isolated. Both runs are in `evidence/2026-10-14-mutation.txt`.

## Not in the corpus yet

These shapes from the SBC §2 list and from the M0.5 brief were not reconstructed:

* **vac's residuals** (KH:29294 R-a..R-e). `vac-field-read-before-write` is the program
  fix `f1ec77ab75` closes; the residuals that KH entry leaves open are other programs
  (R-a and R-d precision losses, R-b a per-row overstatement, R-e a counterexample
  that is not an execution; R-c's field-store member was closed by `7f118dfc1f`). None
  has an entry yet.

* **def-path termination** (KH:23769, OPEN). The probes (`chain_ng`, `binlib_ng`,
  `alias`) need two crates that share one name, or a bin+lib layout, plus
  `-Ztrust-verify-level=2`. Their sources are not in the tree, and the single-crate
  "twin impl differing only in a lifetime" form could not be rebuilt faithfully.
* **OVF-ASSERT-XCRATE-1** (KH:5332, OPEN). The claim is about a dependency proved
  with overflow checks on and then linked into a checks-off binary. That is a
  configuration-binding property of a two-build pipeline, not a verdict on one
  program. It needs a `pipeline` entry kind.
* **trust-wp match_exit** (D-237's `list_match_exit`, aee6e8f2). It needs a
  Creusot list program whose post-loop `get` goal reaches the match-exit lane with
  `enum L { Cons(..), Nil }`. No such case exists in trust-wp's corpus, and one built
  blind could not be shown to reach the lane.
* **Clean fix 39** (`define-fun-rec`, R01 and R03). AY answers `sat` by lazy
  unfolding, while the SMT-LIB reading is an axiom that need not be consistent, so
  "satisfiable" is not settled for these scripts. Clean refuses both readings.
* The **trust-vc MIR lane** has no entry in its own contract surface
  (`#[trust_vc::contract(..)]`).
* Further KNOWN_HAZARDS shapes beyond the M0.5 list (summary-key collisions, std
  recognised by name, facts minted from a parameter's name, interposable callees,
  open-world trait dispatch, false loop facts KH:21555/21642/21728, KH:22996,
  KH:21108).
