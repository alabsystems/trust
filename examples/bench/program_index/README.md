# Compile/Verify Program Index

This directory defines the small single-file benchmark corpus used to compare:

- upstream `rustc`
- Trust with verification disabled (`-Z trust-verify=off`)
- Trust with verification disabled and the explicit LLVM backend
- Trust with native verification enabled
- Trust with experimental trust-cg codegen (`-Z codegen-backend=trust_cg`)

The corpus is declarative. `index.json` records paired `good` and `flawed`
programs, their source paths, the proof obligations each pair is meant to
exercise, and declarative expectations for Rust parity, Trust verification,
derived backward-pass evidence, explicit LLVM execution, trust-cg execution, and
documented exception hooks. The canonical runner is the Rust-owned
`targo trust benchmark program-index` command.

## Run

List the corpus without invoking a compiler:

```sh
targo trust benchmark program-index --list
```

Run trust-cg report mode with the canonical subcommand spelling:

```sh
targo trust benchmark program-index --slots=trust-cg --trust-cg-mode=report --list
```

Run with fake or explicit tool slots:

```sh
targo trust benchmark program-index \
  --slot-bin upstream-rustc=/path/to/rustc \
  --slot-bin trust-noverify=/path/to/trustc \
  --slot-bin trust-verify=/path/to/trustc \
  --slot-bin llvm=/path/to/trustc \
  --slot-bin trust-cg=/path/to/trustc \
  --require-slots
```

If a slot binary is not found, that slot is skipped unless `--require-slots` is
set. By default the runner never executes produced binaries; it only invokes
compiler commands, captures stdout/stderr into a report directory, and writes a
JSON summary. Executed rows include elapsed wall time and structured resource
usage; on POSIX hosts the runner uses `os.wait4` to record normalized
`peak_rss_bytes` without parsing external timing-tool output. Rows also include
program metadata, object hashes, object byte counts, and stdout/stderr byte
counts for output comparison. Compile/verify rows additionally record the
canonical slot binary name, resolved binary basename, Trust-owned binary name
for Trust slots, a best-effort `--print sysroot` probe, execution phase,
pre-exception failure phase, and stderr category labels such as sysroot,
missing-core/std, backend, object-emission, verifier, panic, linker, timeout,
or uncategorized compiler stderr. The sysroot probe is evidence only; a failed
probe is recorded in `sysroot_query` and does not mask the actual compile or
verification outcome. The report summary includes compile duration, peak RSS
rollups by slot, aggregate stderr categories, and `hello_world_gate` evidence
for the hello-world pair when selected. `trust_unlock_path` marks Trust-owned
slots as public Trust evidence only when they resolve to a canonical `trustc`
entrypoint; explicit overrides with other basenames can still run but are
reported as noncanonical evidence.

Use `--repetitions N` when collecting release-quality timing/resource evidence.
Repeated samples are aggregated inside the same `(program, variant, slot)` row.
Executed rows include `requested_repetitions`, `sample_count`,
`sample_aggregation`, and `samples`; planned or skipped rows carry zero samples.
The representative row values are aggregate-compatible, so domination compares
one row per program/slot instead of treating repetitions as duplicate evidence.

Opt into a separate runtime-output parity pass:

```sh
targo trust benchmark program-index \
  --suite proof-design \
  --slots upstream-rustc trust-noverify llvm trust-cg \
  --repetitions 3 \
  --runtime-parity \
  --slot-bin upstream-rustc=/path/to/rustc \
  --slot-bin trust-noverify=/path/to/trustc \
  --slot-bin llvm=/path/to/trustc \
  --slot-bin trust-cg=/path/to/trustc \
  --require-slots
```

`--runtime-parity` performs an extra link/run pass for compile-mode slots only,
using `upstream-rustc` as the per-program baseline. It records executable hashes,
runtime stdout/stderr hashes and byte counts, exit status, build/run duration,
and runtime resource usage under `runtime_parity` in `report.json`.
Runtime stderr comparison uses a normalized hash that removes nondeterministic
Rust panic thread IDs while preserving raw stderr hashes in each row.
Divergences fail the command. A baseline-only run also fails; runtime parity is
reported as `baseline_only` until at least one non-upstream compile slot matches
the upstream baseline. The existing compile/verify result rows remain
object-only and are still reported separately.

## Expected Outcomes

Compile-only slots should compile both `good` and `flawed` programs. Flawedness
is a proof property, not a Rust type-checking property.

The index carries an `expectation_model` with `default_by_variant` expectations
and `program_exception_hooks`. The expected baseline is:

- `rust_parity.compile = pass` and `rust_parity.runtime = parity_when_executed`
- `trust_verify.expected = verify_pass` for known-good variants
- `trust_verify.expected = verify_fail` for known-flawed variants
- `backward_pass.expected = no_repair_needed` for known-good variants
- `backward_pass.expected = counterexample_or_repair_candidate` for known-flawed
  variants
- `llvm.compile = pass` and `llvm.execution = parity_when_executed`
- `trust_cg.compile = pass_or_report_mode_exception` and
  `trust_cg.execution = parity_when_emit_ready`

`program_exception_hooks` names the `expected_known_gaps` IDs that currently
explain non-trust-cg deviations from those expectations. trust-cg deviations are
hooked through the shared `trust_cg_exception_model` because the backend is still
experimental and report-only by default.
Unhooked non-trust-cg gap IDs and hook references to unknown gap IDs are rejected.
Expected known gaps should be hooked only to the rows they cover; a matching
stderr signature on an unhooked row is still a regression.

The `trust-verify` slot should prove every `good` program and report failed
obligations for every `flawed` program. The runner reads `TRUST_JSON:` transport
when available and also treats fail-closed compiler exits as verification
failures for flawed programs. Backward-pass rows are conservative derived
evidence: a flawed row is reported as `counterexample_or_repair_candidate` only
when verifier transport includes a counterexample, counterexample model, or
explicit repair-candidate payload. A bare failed count is recorded as
`missing_backward_payload` and makes `summary.backward_pass.status` partial.
That field is not a substitute for full backprop instrumentation with source
attribution and iteration traces.

trust-cg is experimental. Its default mode is `report`: trust-cg-specific failures are
classified and counted as exceptions, not as corpus failures. Use
`--trust-cg-mode enforce` when trust-cg parity should be a hard gate.

Every result row records a `classification`. Passing rows are `as-expected`,
trust-cg report-mode exceptions are `expected-known-gap`, hard mismatches are
`regression`, skipped slots are `not-run`, and dry-run rows are `planned`.
Non-trust-cg known gaps must be declared in `index.json` with an stderr signature
or transport-counter signature so they remain visible in the report rather than
disappearing into the pass count.
Known-gap matching searches both the head and tail stderr excerpts because
formatter diagnostics can precede the decisive verifier result.
The report summary also includes `known_good_pass`,
`known_flawed_rejection`, `trust_cg_exceptions`, `codegen_output_evidence`, and
`runtime_parity` fields so known-good proof/compile coverage, flawed-program
verification rejection, trust-cg exception classes, explicit LLVM/trust-cg object
output presence, runtime parity status, and runtime duration/memory evidence are
visible without scanning every row. `hello_world_gate` preserves raw failed
counts before exceptions plus the failure phase, stderr categories, Trust-owned
binary name, and sysroot path for hello-world gate rows, so expected-gap
accounting remains visible instead of hiding stage2/sysroot regressions.
`codegen_output_evidence` records non-empty object output by slot and variant;
it is not an LLVM-vs-trust-cg object parity claim.

## Coverage

The default index covers 50 good/flawed pairs and 100 Rust files across simple
classic examples, hello world, leetcode-style two-sum, valid-parentheses,
binary-search/midpoint/statistics cases, overflow, division/remainder by zero,
floating-point exceptional values, bounds, assertion, unreachable, minimal
proof-design examples, and low-cost candidate fixtures for ADT/enum control
flow, iterator bounds, borrow-transfer invariants, recursion/termination, and
adversarial fixtures for path, loop, interprocedural, data-model,
memory/fat-pointer/provenance, std/format, and backprop/proof-strengthening
behavior. `index.json` records a `coverage_model` that separates the
simple-classic, verification-targeted, proof-design-candidates, and
adversarial-target tiers while keeping every program in an explicit
known-good/known-flawed pair.

The `proof-design` suite is the formatter-free repair ladder. Each row carries
explicit `metadata` marking it as `proof_design`, `formatter_free`, and
`runtime_safe_main`, plus a ladder step and obligation family. The current
ladder covers scalar assertion, narrowing cast, integer add/div/rem, signed div
overflow, mul/sub/neg/shift overflow, short-circuit path guards,
interprocedural callee guards, floating-point div/overflow, array/range/slice
bounds, and unreachable control flow.

The `proof-design-candidates` suite is separate non-gating evidence for
candidate ADT/enum, iterator, borrow-state, and recursion fixtures before they
graduate into the proof-grade ladder. Do not pass candidate-suite rows as
functional proof domination evidence.

Legacy `#![feature(contracts)]` fixtures and the unpaired signed-gauntlet stress
case are listed as exclusions so benchmark accounting stays explicit.

## Adversarial Audit Status

The corpus is useful as a compile/verify smoke matrix, but it is not yet a
complete proof-quality corpus. As of
`reports/bench/program-index/lane-f-program-index-20260501T152934Z/report.json`,
all upstream and Trust noverify compile rows pass, but only the minimal
`proof_div_zero.good` fixture proves in the `trust-verify` slot. Most remaining
good rows are expected-known-gap exceptions caused by formatter/std MIR, and all
trust-cg rows are report-mode exceptions.

The proof-design expansion now gives every major formatter-heavy obligation a
local good/flawed fixture pair. Keep future ladder movement explicit: scalar
proof fixtures first, then path-sensitive branches, loops/slices,
interprocedural calls, generics/ADTs, and finally println!/std-heavy demos.

The adversarial-target tier is explicitly gap-accounted. Each target group names
the pair IDs and expected gap IDs that currently explain non-trust-cg trust-verify
deviations. Flawed rows remain known-flawed: a verifier pass on one of those
rows is still a regression, not an expected gap.

Detailed Lane F audit notes, exact next commands, and the missing-fixture list
are tracked in
`reports/bench/program-index/lane-f-adversarial-coverage-plan-2026-05-01.md`.

Second-pass Lane H runtime/parity and next-run matrix notes are tracked in
`reports/bench/program-index/lane-h-second-pass-coverage-2026-05-01.md`.

## Repair Evidence E2E

`crates/trust-backprop/tests/program_index_real_verifier_repair_e2e.rs` is an
ignored real-compiler evidence test for the `proof_div_zero.flawed` fixture. Set
`TRUST_REPAIR_E2E_TRUSTC` to a stage2 `trustc` and
`TRUST_REPAIR_E2E_REPORT_DIR` to an evidence directory, then run:

```sh
cargo test -p trust-backprop --test program_index_real_verifier_repair_e2e \
  -- --ignored --nocapture
```

The test copies the flawed fixture to a temp file, requires real stage2
`TRUST_JSON` divzero failure and counterexample evidence, applies a deterministic
guarded-division repair only to the temp copy, reruns stage2 verification, and
archives `before.stderr`, `after.stderr`, `repaired.rs`, `patch.diff`,
`repair-proof-improvement.json`, and `repair-proof-improvement.md` in the report
directory. It fails closed when transport diagnostics are missing or the proved
and failed proof counts do not improve.
