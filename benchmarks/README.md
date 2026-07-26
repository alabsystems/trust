# Benchmarks

Benchmark evidence for Trust should flow through Trust-owned commands or native
tests. The old Docker/run-eval template surface has been removed.

## Program Index

Use the Rust CLI program-index runner for the single-file compile/verify corpus:

```bash
targo trust benchmark program-index --list
targo trust benchmark program-index --suite proof-design --limit 2 --dry-run
targo trust benchmark program-index --suite proof-design --limit 2 --repetitions 3
targo trust benchmark program-index --runtime-parity --slots upstream-rustc trust-noverify --slot-bin upstream-rustc=/path/to/external/rustc --require-slots
```

Reports are written under `reports/bench/program-index/<run-id>/` unless
`--report-dir` is supplied. Release comparison evidence must bind
`upstream-rustc` to an external upstream Rust compiler and report
`summary.upstream_baseline.status = "passed"`. The baseline probe must also
pass `upstream-rustc -vV` and `upstream-rustc --print sysroot`, with `-vV`
declaring `binary: rustc`, full `commit-hash`, `host`, and `release`, and
without Trust identity or repo-local stage2 paths. That is the evidence
contract in full; `targo trust benchmark program-index --help` lists the
common options.

Use `--repetitions N` for release-quality sampling. The runner keeps repeated
samples inside one result row with `sample_count`, `sample_aggregation`, and
`samples`, so domination does not treat repeated samples as duplicate programs.

## SWE-Bench Baseline

Tracked in #2147. SWE-bench measures AI agent performance on real software
engineering tasks.

These Python template commands are eval/development baselines only; they are
not Trust release benchmark evidence and do not reintroduce removed verifier
aliases.

| Date | Run ID | Model | Instances | Resolved | Accuracy | Notes |
|------|--------|-------|-----------|----------|----------|-------|
| 2026-02-03 | baseline-10-final | opus | 10 | 0 | 0% | All timed out (300s) |

Current state: 0% baseline. Results are stored in
`evals/results/swe-bench/baseline-*/`.

```bash
python -m evals.templates.swe_bench --spec evals/registry/swe-bench.yaml
python -m evals.templates.swe_bench --max-instances 5 --run-id my-test
python -m evals.templates.swe_bench --dry-run
```

See `evals/registry/swe-bench.yaml` for configuration.
