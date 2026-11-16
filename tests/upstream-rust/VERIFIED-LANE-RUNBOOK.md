# The verified lane — scaffolding and runbook

Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0

Status (2026-09-01): **the lane is WIRED and has NEVER BEEN RUN.** The
mechanism described in §2 landed; `test-exception-lanes.toml` now carries
`verified_lane_available = true`, cross-checked against the source by
`check_exception_lanes.py` on every run. No verified suite run exists yet,
because `x.py test --stage 2` needs a stage2 build and is not read-only. §3 is
what a maintainer executes to produce one; until they do, there is no verified
evidence and no `lane = "verified"` row may cite any.

    ./x.py test --stage 2 --trust-verified --no-fail-fast tests/ui

What is proven today is the MECHANISM, by unit test, not by a suite run:

| Claim | Test |
|---|---|
| the verified lane appends exactly `-Ztrust-verify=on -Ztrust-policy=strict`, and never `-Ztrust-verify=off` | `compiletest/src/common/tests.rs::trust_verified_lane_is_opt_in_and_default_is_unchanged` |
| the DEFAULT lane's flag vector is byte-identical with the flag absent | same test + `::trust_lane_selection_truth_table_preserves_the_default` |
| argv in → rustc flag vector out, through a real `Config` | `::trust_lane_reaches_rustc_argv_from_the_command_line` |
| `--trust-vanilla --trust-verified` is refused; `--trust-verified` without a verifier-capable driver is refused | `::trust_vanilla_and_trust_verified_are_refused_together`, `::trust_verified_without_a_capable_driver_is_refused`, bootstrap `flags.rs::trust_lane_flag_tests` |
| the verified lane gets its own result stamp, and the two old lanes' stamps are bit-identical to the pre-lane formula | `::trust_verified_lane_has_a_distinct_stamp` |

Run them with
`targo --unverified test -p compiletest --lib trust` and
`targo --unverified test --manifest-path src/bootstrap/Cargo.toml --lib trust_lane_flag_tests`.
Neither needs a stage2 build.

---

## 1. What the two-language plan promises, and what is actually measured

> "vanilla Rust is valid input; unannotated Rust gets the default verification
> and compiles as ever."

That sentence has two halves and the tree measures only one of them.

**The half that is measured.** `tests/upstream-rust/` accounts for
`./x.py test --stage 2 --trust-vanilla`. Three claims about that lane were
re-derived from source on 2026-09-01 and all three hold:

| Claim | Where | Verdict |
|---|---|---|
| `--trust-vanilla` implies `-Ztrust-verify=off` | `src/tools/compiletest/src/lib.rs:418` pushes `TRUST_VANILLA_SENTINEL`; `common.rs:813` reads it; `common.rs:851` calls `configure_trust_verification_isolation`; `common.rs:1009` appends `TRUST_VANILLA_RUSTC_FLAG`, defined at `common.rs:15` as `-Ztrust-verify=off` | **holds** |
| every `needs-trust-verify` test is auto-ignored | `src/tools/compiletest/src/directives/needs.rs:204-208`, `condition: !config.trust_vanilla()` | **holds** |
| `TRUST_NO_VERIFY=1` propagates into nested compilations | `src/tools/compiletest/src/runtest.rs:1098-1100` sets it on the **run** environment of the test binary, applied last so per-test `exec-env`/`unset-exec-env` cannot re-enable verification in the subtree. Compile commands are the opposite: `common.rs:1004` strips `TRUST_NO_VERIFY` **unconditionally**, because the driver applies it as a post-parse override that beats a test's explicit `-Ztrust-verify=on`. run-make gets the same effect through a generated wrapper (`runtest/run_make.rs:379-412`) that execs the real rustc with `-Ztrust-verify=off` | **holds, with that scope** |

**The half that was not — the world before 2026-09-01.** Kept in the present
tense of its own measurement, because every `vanilla` row in the ledger is a
claim about it. Until 2026-09-01 no lane ran the inherited upstream corpus with
verification **on**, and the reason was stronger than "nobody passes the flag" —
there was no flag to pass:

```rust
// src/tools/compiletest/src/common.rs:851
pub(crate) fn configure_compiletest_rustc(&self, command: &mut Command) {
    configure_trust_verification_isolation(
        command,
        self.rustc_supports_trust_verification || self.trust_vanilla(),
    );
}
```

```rust
// src/bootstrap/src/core/build_steps/test.rs:2581
let rustc_supports_trust_verification =
    test_compiler.stage > 0 && !builder.download_rustc();
```

On any `x.py test --stage 2`, `rustc_supports_trust_verification` is true, so
the disjunction is true **with or without `--trust-vanilla`**, and every test
compile gets `-Ztrust-verify=off` appended. Dropping `--trust-vanilla` gives you
the *branded* lane, not a verified one: it swaps the driver hardlink from
`rustc` to `trustc` (`test.rs:2403-2418`), un-ignores `needs-trust-verify`
tests, and stops exporting `TRUST_NO_VERIFY=1` into the run environment — but
the compile is still verification-off. The only opt-back-in today is a test's
own `//@ compile-flags: -Ztrust-verify=on` (argv last-wins; see
`common/tests.rs::trust_isolation_is_capability_scoped_and_overridable`).

The consequence was the whole point of gap G11: the shipping default is
`-Ztrust-verify=on` with `TrustPolicy::Strict`, where a refutation carrying a
counterexample **hard-fails the build**, and false refutations are a real,
repeatedly-shipped class in this tree. Under that default, every vanilla Rust
program in the inherited corpus was **unwitnessed**.

`--trust-verified` (§2) supplies the missing negative arm. Note precisely what
that changes and what it does not: the corpus is unwitnessed **until someone
runs the lane**. Landing the flag moves the obstacle from "impossible" to
"unexecuted", and §3 is the execution.

---

## 2. The code change this needed — **LANDED 2026-09-01**

`src/tools/compiletest/` and `src/bootstrap/` are compiler-owned. This section
was the specification; every item below is now in the tree, and
`check_exception_lanes.py` re-derives each one from source on every run
(`VERIFIED_LANE_CHAIN`) so a later refactor that folds the third state back into
the disjunction fails the ledger gate instead of silently un-witnessing a lane.

1. **`src/tools/compiletest/src/common.rs`** — add
   `TRUST_VERIFIED_SENTINEL: &str = "--compiletest-trust-verified"` and a
   `Config::trust_verified()` beside `trust_vanilla()`, and give
   `configure_trust_verification_isolation` a third state. Concretely, on the
   verified lane it must:
   * **not** append `TRUST_VANILLA_RUSTC_FLAG`;
   * append `-Ztrust-verify=on -Ztrust-policy=strict` instead, so the lane
     states its own contract in argv rather than inheriting a default that can
     move under it;
   * **keep** the unconditional `command.env_remove("TRUST_NO_VERIFY")`. This is
     load-bearing in the *opposite* direction from the vanilla lane: the driver
     applies that variable as a post-parse override that beats an explicit
     `-Ztrust-verify=on` wherever it sits in argv, so an inherited one turns the
     verified lane into a silent no-op. The measured precedent is in that
     function's own comment — a leaked `TRUST_NO_VERIFY` once ran the entire
     `tests/ui/trust` suite with verification off, 145 of 304 failing;
   * **not** set `TRUST_VANILLA_ANNOUNCED`, which exists only to quiet the
     compiler's once-per-crate "compiled WITHOUT Trust verification" note.
2. **`src/tools/compiletest/src/lib.rs`** — register a `--trust-verified` option
   next to `--trust-vanilla` (`lib.rs:138`, `lib.rs:418`) and push the new
   sentinel. Make `--trust-vanilla --trust-verified` a hard argument error; the
   two lanes make contradictory claims and a run that quietly picked one would
   mislabel every row it produced.
3. **`src/tools/compiletest/src/directives/needs.rs`** — `needs-trust-verify`
   already runs whenever `!config.trust_vanilla()`, so it needs no change. Audit
   it in the same PR anyway: on the verified lane those tests are the *positive
   control*, and if they are ignored the lane is not running.
4. **`src/bootstrap/src/core/config/flags.rs`** — add `trust_verified: bool` to
   `Subcommand::Test` (mirroring `trust_vanilla` at `flags.rs:388` and its
   accessor at `flags.rs:577`).
5. **`src/bootstrap/src/core/build_steps/test.rs`** — forward it beside
   `--trust-vanilla` (`test.rs:2807`). Leave `compiletest_rustc_path`
   (`test.rs:2403`) alone: the verified lane wants the branded `trustc`, which
   is what `vanilla == false` already selects.
6. **`src/tools/compiletest/src/runtest/run_make.rs`** — `run-make` recipes
   receive `RUSTC` and spawn their own compilations. On the vanilla lane that is
   the generated wrapper; on the verified lane it must be the real branded
   driver with no injected flag, so that recipe-spawned compiles inherit the
   lane instead of silently opting out.

Add a unit test alongside
`common/tests.rs::trust_isolation_is_capability_scoped_and_overridable` that
asserts the verified lane appends `-Ztrust-verify=on -Ztrust-policy=strict` and
appends **no** `-Ztrust-verify=off`. That test is cheap and it is the only thing
that will notice if a later refactor folds the third state back into the
disjunction.

**One item the specification missed, found while implementing it.**
`runtest.rs::compute_stamp_hash` hashes `config.trust_vanilla()` — it decides
whether a previous result can be REUSED. Left alone, a `--trust-verified` run
following an ordinary run would find every stamp current, **skip every test**,
and report green having verified nothing: the exact silent no-op §3's positive
controls exist to catch, except invisible because the run does not even reach a
compiler. The lane is now hashed too, and only **when set**, so the two
pre-existing lanes' stamps are bit-identical to what they were before
(asserted in `::trust_verified_lane_has_a_distinct_stamp` against a full
reproduction of the pre-lane formula).

**Scope limit, stated so it is not mistaken for coverage.** `--trust-verified`
reaches **compiletest-managed compiles only**. Cargo-based tool and library
tests (`prepare_cargo_test`, `builder/cargo.rs`) keep
`apply_bootstrap_trust_verification_default` on every lane: rustflags there are
invocation-wide, so turning verification on would aim it at std's entire
third-party dependency graph with no unit named anywhere — which
`bootstrap_verification_request_refusal` refuses outright, for every `Mode`.

---

## 3. The runbook — what a maintainer executes

Nothing below is run by the change that landed this file. `x.py test --stage 2`
is **not read-only** (it has wiped stage2 binaries), so it is never invoked from
a validator, a hook, or an agent session.

### Step 0 — ledger preflight (read-only, run this first, run it anywhere)

```sh
tests/upstream-rust/check_exception_lanes.py            # every row has a lane
tests/upstream-rust/check_exception_lanes.py --self-test # the gate's own refusals
scripts/check_ledger_expirations.py --warn-days 14      # nothing waived is stale
```

All three are pure reads. `check_exception_lanes.py` also re-derives the §1
premise from `common.rs` on every run: if `configure_compiletest_rustc` stops
gating on `rustc_supports_trust_verification || trust_vanilla()`, it fails and
tells you to re-measure rather than keep asserting a stale answer.

### Step 1 — build a coherent stage2

```sh
./x.py build --stage 2
```

Both lanes must be measured on the **same** stage2 and the same pinned upstream
revision (`baseline.toml [upstream] revision`; read it there, a copy here goes
stale at the next upstream merge). A cross-stage
comparison is not a lane difference, it is two unrelated runs.

### Step 2 — the vanilla lane (the existing baseline)

```sh
./x.py test --stage 2 --trust-vanilla --no-fail-fast tests/ui 2>&1 \
  | tee reports/artifacts/$(date +%F)-lane-vanilla-ui.log
```

Positive control: the summary must report a non-zero `ignored` count, and
`needs-trust-verify` tests must be among them. If nothing is ignored, the
sentinel did not reach `Config::trust_vanilla()` and the run is not the vanilla
lane.

### Step 3 — the verified lane


```sh
./x.py test --stage 2 --trust-verified --no-fail-fast tests/ui 2>&1 \
  | tee reports/artifacts/$(date +%F)-lane-verified-ui.log
```

Two positive controls, both required, because the failure mode of this lane is
that it silently does nothing:

* `needs-trust-verify` tests must **run**, not be ignored — they assert verifier
  diagnostics and can only pass with verification on;
* a scratch file containing `fn divide(x: i32, y: i32) -> i32 { x / y }` must be
  **refused** with `Trust verification:` evidence under the same flags. This is
  the same canary
  `scripts/check_trust_default_authority.py` uses. A verified lane that compiles
  it is a lane with verification off.

If either control fails, **do not record any row from that run.** A run that
did not verify produces vanilla evidence wearing a verified label, which is
precisely the confusion the `lane` field exists to prevent.

### Step 4 — classify, then write rows

Every failure that appears **only** in the step-3 log is a verified-lane
finding. It is not automatically a waiver: under `TrustPolicy::Strict` the
likeliest cause is a *false refutation*, which is a compiler defect to fix, not
a test to waive. Triage each one before writing anything.

For a failure that genuinely warrants a waiver:

1. add the `[[exceptions]]` row to `test-exceptions.toml` as usual;
2. add the matching `[[lanes]]` row with `lane = "verified"`, `measured_on` set
   to the run date, and `evidence` naming the step-3 log path **and both
   positive controls as they appear in it**. `verified_lane_available` is
   already `true` (the lane exists); the row's own `evidence` is where the
   measurement claim lives, and it is the only place it lives.

`check_exception_lanes.py` refuses a `verified` row while
`verified_lane_available = false`, and refuses a `true` the source does not
support — a partially-wired lane is refused outright rather than resolved either
way, because a lane that accepts the flag and still does not verify is the one
state that produces vanilla evidence under a verified label.

### Step 5 — keep the lanes distinguishable in the ledger

A waiver applies *on the lanes it was observed on*. If the same test fails on
two lanes, that is two observations: two `[[lanes]]` rows (one per lane, each
with its own `measured_on` and `evidence`) for its one `[[exceptions]]` row,
never one observation cited by both. The default lane (no lane flag, what the
`suite.*` harness rows run) is a third lane, not the vanilla one; see the
sidecar's lane table. The pre-lane ledger had
no way to say that, and every one of its six rows turns out to be vanilla-lane
(all six trace to `--trust-vanilla` replays or to domination runs, which invoke
`bootstrap test --trust-vanilla` — `crates/trust-upstream-compat/src/porting.rs:6166`).

---

## 4. Known defects a verified lane will walk into

Recorded here so they are triaged rather than rediscovered:

* **Revision-keyed failures can never be waived.**
  `parse_compiletest_fail_line` (`crates/trust-upstream-compat/src/porting.rs`)
  takes the failing path verbatim, so a `//@ revisions:` test arrives as
  `<path>.rs#<revision>`, while `failure_covering_exception` compares against a
  row's `path` with no revision handling. A row for a revisioned test parses,
  validates, and silently never nets. This blocks the `char-3` restoration and
  it will block verified-lane rows the same way. Fix in `porting.rs`, not by
  pasting `#rev` into `path`.
* **The ledger never reports a row that covered nothing.**
  `failure_covering_exception` only ever asks whether a row covers a failure, so
  a stale row stays invisible until its expiry fires — the mechanism that let 71
  `sysroot-skew` rows waive a defect fixed thirteen days before they were
  written. On a lane whose failure population is expected to *shrink* as false
  refutations get fixed, this matters more, not less.
* **`-Ztrust-policy` has no per-unit scoping in this harness.** The sanctioned
  pattern elsewhere in the constellation is first-party units at `advisory`
  ratcheting toward `strict`, with third-party units scoped off per unit. The
  verified lane as specified above is all-or-nothing at `strict`. If the first
  run is unusably red, add `-Ztrust-policy=advisory` as an explicit *third*
  lane rather than weakening this one — an advisory run does not witness the
  shipping default, and a row measured on it must not be labeled `verified`.
