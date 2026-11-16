# Test Plans (Trust)

A test plan is a TOML file that names several test requests, each what one
`targo test -p ..` command would select. One invocation resolves every request
it performs on its own, builds them in one graph, and runs each test
executable in the build's queue:

```console
targo --unverified test --plan <FILE> \
      (--changed-range <RANGE>... | --changed-pushed-refs <FILE|-> |
       --changed-paths <FILE|-> | --whole-plan) [--reached <DIR>]... [-p <SPEC>]... \
      [--request <ID>]... \
      [--no-run | --select-only | --unit-graph-parity | --unit-graph -Zunstable-options] \
      --locked --no-fail-fast
```

That one command is a whole lane. What changed is named on the command line;
everything else a gate would otherwise have to remember is in the file: which
packages are tested and how, the pool the tests run in, what each harness is
counted for, how long the run and a silent harness may take, and what is
expected to fail. The exit status says how the run ended.

This page lists every key of the file. How a run is selected, scheduled,
judged and recorded is described under
[`build.test-jobs`](config.md#buildtest-jobs-trust).

A plan is a named file and never Cargo configuration: configuration merges the
home directory, the environment and `--config`, and a gate reads one source.
An unknown key is an error at every level. Paths in a plan are relative to the
workspace root and written with `/`.

Trust's own plan is `tests/test-plans/crates.toml`. Targo's test
`ops::cargo_test::plan_checked_in` holds every name in it to the tree.

## The command line

| Flag | With a plan |
|------|-------------|
| `--plan <FILE>` | The plan. Native unverified Targo only. |
| `--changed-range <RANGE>` | Paths git says the range changed, diffed by Targo itself (`git diff --no-renames --name-only`, submodule pointers included, so a rename is its old path and its new one, and a deletion is the deleted path). `A..B` compares the two trees; `A...B` compares `B` with its merge base with `A`. Repeat it for several ranges. A range git cannot diff is refused, never read as no change. Members a changed path lies in are *touched*. |
| `--changed-pushed-refs <FILE>` | The refs being pushed, as git writes them to a pre-push hook (`<local ref> <local sha> <remote ref> <remote sha>` per line), `-` for standard input. An updated branch is the range `<remote sha>..<local sha>`; a branch the remote does not have is `<base>...<local sha>` with `[select] base`; a deleted branch pushes no tree. Input that names no pushed tree (no line at all, or deletions only) is judged as the standing change `<base>...HEAD`, as the script lane judged it, and never as a push that changes nothing: a hook that lost its standard input does not exit 0. |
| `--changed-paths <FILE>` | Paths that changed, NUL- or newline-separated, `-` for standard input. |
| `--reached <DIR>` | A plan member, or a `[[workspace]]` of the plan, that the change *reaches* without touching, by its directory from the workspace root. A directory the plan does not test is refused. Repeat it for several. |
| `-p <SPEC>` | A plan member the change reaches, by package name. It has no other meaning with a plan. |
| `--whole-plan` | Every request and phase, whatever changed. Refused beside any of the flags above. |
| `--request <ID>` | Narrow the run to this request. It never adds one the selection left out. |
| `--run-after <FILE>` | Hold every test executable of the run at a barrier: see [The barrier](#the-barrier). |
| `--run-after-owner <PID>` | The process that is to write the barrier file. |
| `--no-run` | Build every performed request and phase; run nothing. |
| `--select-only` | Say what the plan selects for the change and stop: see [The selection alone](#the-selection-alone). |
| `--unit-graph-parity` | Check that the plan's one unit graph is the union of its requests' standalone graphs and stop: see [Graph parity](#graph-parity). |
| `--unit-graph` | Print the requests' one unit graph. Phases are left out, with a warning. |

A run says what it judges: an invocation that names no change and does not
say `--whole-plan` is refused, so that a caller who lost its range does not
run everything, or nothing, by accident. A change that touches and reaches
nothing selects nothing: the run exits 0 and its closing record says
`nothing-selected`.

A caller that moves from `scripts/check_crates_tests_scoped.py` must respell
its range: that script read `--range A..B` as `A...B` (the changes since the
merge base), and `--changed-range A..B` is the two trees, as git reads it.
The merge-base form is `--changed-range A...B`.

### The selection alone

A gate that plans around the lane (which members it hands it, which of them
the lane tests on this host, which instruments a change moves) asks the lane
and keeps no copy of its rules:

```console
targo --unverified test --plan <FILE> --changed-paths - --reached <DIR> --select-only
```

The whole standard output is one line: the `test-plan` record a run of the
same arguments begins with (the touched, reached and selected members, and for
every request of the file whether the run performs it and why), with one key
more, `phases`: what that run would do with each `[[tool]]` and `[[workspace]]`
entry, in the plan's order. A tool is `selected` or `not-needed`; a workspace
is `selected`, `not-selected`, `left-out` (by `--request`) or `not-applicable`
(its `cfg` does not hold for the target, with the reason in `why`). Nothing is
built, bounded or judged, and no result record follows. What a run refuses
the listing refuses, with the same status: a changed path nothing accounts for
exits 2 after the record that lists it, and a reached directory the plan does
not test exits 2 with no record. `--select-only` is refused beside `--no-run`,
`--unit-graph`, `--unit-graph-parity` and `--run-after`. A Targo without the
flag refuses it as it refuses any argument it does not know (exit status 1),
which is how a caller learns that this Targo cannot answer.

### Graph parity

A plan run builds every request in one graph, and is sound only if each
request gets the units its own `targo test -p ..` command gets.
`--unit-graph-parity` holds the plan to that on the tree at hand:

```console
targo --unverified test --plan <FILE> --whole-plan --unit-graph-parity --locked
```

It makes the plan's graph and, by the ordinary plan-free route of the same
invocation, the graph of each performed request alone (its packages, features
and targets under `resolver.feature-unification = "selected"`), and compares
them as the units they are: every unit, every dependency edge and every root
of the plan must be those of the union, and no root twice; and each request's
own graph must test its own packages, so that a graph that is not the
request's (one still shaped by the plan) is never what the plan is compared
with. It builds and runs
nothing and leaves the `[[tool]]` and `[[workspace]]` phases out, which are
built under their own manifests. Equal graphs exit 0 with a line that counts
them; a difference exits 101 and names the units (a feature of one request
that reached another shows as a unit only one side builds); a selection that
performs no request exits 2. Run it when the plan, a manifest or lockfile of
the workspace, or Targo's plan code changes.

The plan owns package, feature, target and argument selection, so these are
refused beside it: `--features`, `--all-features`, `--no-default-features`,
`--lib`, `--bin`, `--bins`, `--example`, `--examples`, `--test`, `--tests`,
`--bench`, `--benches`, `--all-targets`, `--doc`, a test name, arguments after
`--`, `--require-test-bin`, `--workspace`, `--all` and `--exclude`. `-j` stays
the caller's, and the `build.test-*` settings stand over the plan's `[run]`
table. A plan run sets
`resolver.feature-unification = "selected"` itself and requires feature
resolver 2 or later.

## The file

### `schema`

Required. The string `"targo.test-plan.v1"`; any other is refused.

### `[select]`

Required. Which packages the plan tests and which changed paths it must
account for.

| Key | Type | Meaning |
|-----|------|---------|
| `members` | string, required | `"default-members"`: the workspace's default members are the plan's members. No other value exists. |
| `attribute-under` | array of strings | Path prefixes. A changed path under one that no plan member, `elsewhere` member, `[[workspace]]` or `[[tool]]` owns is refused with exit status 2. |
| `whole-plan-when-changed` | array of strings | Path prefixes of the lane's own policy. A changed path under one runs every request and phase, as `--whole-plan` does, and the `test-plan` record says which path. The plan file and its `known-red` file belong here: a dropped variant, a raised bound or a new known-red row changes what every request's result means, and no single request tests that. |
| `elsewhere` | table | `<member> = "<command>"`: workspace members this plan does not test, each with the command that does. They are no plan members; a change to one is reported with its command. No variant, instrument, `[harness]` entry or `needed-by` may name one. |
| `base` | string | The revision a pushed branch the remote does not have is compared with (`--changed-pushed-refs`), such as `origin/main`. Without it such a push is refused. |

### `[default]`

Optional. The run of the selected members under default features, as one
command over all of them. Its request id is `default`. Without it the plan
tests only the members its variants name.

| Key | Type | Meaning |
|-----|------|---------|
| `targets` | string, required | `"tests"`: what `--tests` selects. No other value exists. |
| `min-tests` | integer of 1 or more | Tests (passed plus failed) each selected member must report, summed over this run and the member's variants. Instruments count toward no member. |

### `[expect]`

Optional.

| Key | Type | Meaning |
|-----|------|---------|
| `known-red` | string | A file of tests expected to fail, one `<test binary>::<test path>` per line. `#` starts a comment; a comment containing `[flaky]` marks a test that may pass or fail. It is a ratchet: an unlisted failure fails the run, and so does a listed test that passes unless it is `[flaky]`. A run with it requires `--no-fail-fast`. |

### `[run]`

Optional. The pool, the memory count and the bounds of a run: the lane's
policy, where a script lane had host knobs and constants. Each key has a
configuration setting that stands over it on a host that needs another
figure; a value of 0 is refused.

| Key | Type | Meaning | Over it |
|-----|------|---------|---------|
| `test-jobs` | integer | Credits the run's test executables may hold together. Bounded by `-j`, and by a build-slot job's `CARGO_BUILD_JOBS` share. | `build.test-jobs` |
| `test-weight` | integer | Credits, and libtest threads, of each harness with no `weight` of its own. On a pool that grants one credit at a time (an inherited jobserver, native worker admission) it lowers to 1, with a note, and the pool lowers with it to `test-jobs / test-weight` test executables at once: sixteen credits at four a harness are four harnesses there, not sixteen. | `build.test-weight` |
| `harness-memory-mib` | integer | Mebibytes each running test executable is counted for, unless its `[harness]` entry says otherwise. | |
| `wall-seconds` | integer | Seconds the whole invocation may take, from the moment the plan is selected: phases, build and tests. | `build.test-wall-seconds` |
| `wall-seconds-per-member` | integer | Seconds per crate the run tests: each package a request of the run tests (a member, an instrument's host that is no selected member) and each `[[workspace]]` it runs. The wall bound is the larger of this product and `wall-seconds`. | `build.test-wall-seconds` |
| `run-after-seconds` | integer | Seconds a run held at a barrier (`--run-after`) waits for it with nothing else to do. Required for such a run. | |
| `stall-seconds` | integer | Seconds a running test executable may go without printing a line on either stream. A build is exempt. | `build.test-stall-seconds` |

**Memory.** Where the plan counts any harness for memory, the queue admits a
test executable by memory as well as by credits: the counts of the running
ones never sum past the budget. The budget is `build.test-memory-mib`, or
else what the host has available when the run begins less a reserve of an
eighth of its memory (at least 1 GiB), read by Targo itself (on macOS the
free, speculative, inactive and purgeable pages; on Linux `MemAvailable`) and
printed. A test executable counted for more than the whole budget still
runs, with no other test beside it; so does every counted one on a host
that cannot be measured.

**Time.** The run prints its bounds once, when it is selected (`Bounded test
plan time bound: ...`). A bound that ran out stops the run: nothing more
starts, and everything the run started is killed with its descendants: every
running test executable, and every compiler, build script and linker in
flight (each child of a plan run is started in a process group of its own, in
a `[[tool]]` or `[[workspace]]` phase as in the plan's own build). So a build
that never ends (a hung build script, proc macro or compiler) ends at the
wall bound too. Each stopped harness is reported by its target with the
reason, and the invocation exits 3. The closing record's `why` names the bound
and every test executable running then, each with how long it had run and how
long ago it last printed, or says that the build was running.

The stall bound is each test executable's own: one that prints nothing for
that long is stopped whatever the others print. (The script lane stopped only
when nothing in the whole lane progressed; this is stricter.)

`SIGINT`, `SIGTERM`, `SIGHUP` and `SIGQUIT` to Targo stop the run the same
way, with exit status 2 and outcome `interrupted`, from the moment the plan
is selected: in a `[[tool]]` build, a `[[workspace]]` phase, the build and
the tests alike, the children are killed at once and the closing record is
written. A queue that starts after a stop admits nothing.

A stop that comes while no job queue drains (the run waiting for a lock
another process holds, on a build directory or the package cache; selecting,
resolving, or between phases) is recorded the same way, and every child is
killed. A run still going 2 s later with no queue draining is ended there,
with the stop's exit status and closing record, each open phase's record
closed `failed` and its tool copies removed. A run whose work finished after
a stop (a `--unit-graph-parity` check, a `--no-run` build, a run of nothing)
still ends as the stop says, never 0. A run that has its verdict when the
stop comes keeps it: the stop is not the run's.

Whatever a plan run starts ends with it: when a compiler, build script or
test executable exits, what it left running in its process group (a build
script's or a `RUSTC_WRAPPER`'s background process) is killed with the group,
where a run without a plan leaves it running. `SIGKILL` cannot be caught: a
run killed with it leaves running whatever it had started (each child leads a
process group of its own) and leaves its tool copies in place. A caller that
kills a run that way owns what the run started.

### The barrier

`--run-after <FILE>` is for a caller that overlaps this run's build with work
its tests depend on, as a push hook does whose earlier lanes rebuild the
compiler some tests execute. The run builds, and starts no test executable (in
a `[[workspace]]` phase or of its own) until the file exists:

| The file | The run |
|----------|---------|
| says `run` (white space aside) | starts its tests. |
| says anything else | stops: exit 2, `interrupted`, no test executable started. |
| is absent and the `--run-after-owner` process is gone | the same. |
| is absent for `[run] run-after-seconds` while the run has nothing left to do but wait | stops: exit 3, `out-of-time`. |

The time the run spends with nothing left to do but wait is not charged to
the wall bound. A plan run with `--run-after` and no `[run]
run-after-seconds` is refused. The writer puts the file in place whole (write
beside it, then rename). A `[[workspace]]` phase waits at the barrier when
its own tests are ready, before the plan's own build starts.

### `[harness.<package>.<kind>]`

Optional. The harness policy of the run, and its only source: a non-empty
`build.test-harnesses` beside a plan is an error. `<kind>` is `lib`, or
`bin.<name>`, `test.<name>`, `bench.<name>` or `example.<name>`, and must name
a target the package has.

| Key | Type | Meaning |
|-----|------|---------|
| `weight` | integer | Overrides `[run] test-weight` and `build.test-weight` for that target. A pool that grants one credit at a time refuses a weight above 1 asked here. |
| `exclusive` | boolean | The harness runs with no other harness beside it, after the others. |
| `memory-mib` | integer | Mebibytes the harness is counted for, over `[run] harness-memory-mib`. |
| `seconds` | integer | How long the harness is expected to run. Among the test executables ready to start, the longest expected one starts first, and what it waits for is built first; without it harnesses start in package order, and a long one that happens to be last holds the whole run open. It orders the queue and nothing else: a wrong figure costs time, never a verdict. |

### `[[variant]]`

A second run of one plan member under other features. It is performed when
its package is selected, counts toward that member's `min-tests`, and must
itself report a test.

| Key | Type | Meaning |
|-----|------|---------|
| `id` | string, required | The request id: ASCII letters, digits, `_`, `.`, `-`, not starting with `-`, unique in the file and not `default`. |
| `package` | string, required | A plan member. |
| `features` | array of strings | The features of the run, as after `--features`. Default features stay on. |
| `lib` | boolean | Test the lib target, as `--lib`. |
| `test` | array of strings | Integration test targets by exact name, as `--test <name>` each. No glob. |

At least one of `lib` and `test` is required.

### `[[instrument]]`

A run that judges something outside its host package. It counts toward no
member's `min-tests`, and each of its actions must report a passing test.

| Key | Type | Meaning |
|-----|------|---------|
| `id` | string, required | As for a variant. |
| `package` | string, required | The host: any workspace member `elsewhere` does not name. |
| `lib` | boolean | As for a variant. |
| `test` | array of strings | As for a variant. |
| `args` | array of strings | Arguments for the harness, as after `--`. `--list`, `--help`, `-h` and a `--format` other than `pretty` or `terse` are refused. |
| `when-changed` | array of strings | Path prefixes; the instrument is selected when a changed path starts with one. |
| `when-changed-suffix` | string | The instrument is selected when a changed path ends with it. |
| `not-under` | array of strings | Path prefixes whose paths never select the instrument. |
| `require-pass` | array of strings | Test names that must each print `test <name> ... ok` in this instrument's output. |

At least one of `lib` and `test` is required. An instrument with neither
`when-changed` nor `when-changed-suffix` runs under every selection. A selected
instrument is left out when its host is touched and the default run of that
host already performs everything it would judge.

### `[[tool]]`

A binary that some members' tests run, built under its own manifest before
the requests whenever a performed request tests one of those members.

| Key | Type | Meaning |
|-----|------|---------|
| `manifest` | string, required | The manifest that builds it: another workspace's, or a member's. |
| `bin` | string, required | The bin target, built as `targo build --bin <bin>` builds it. |
| `env` | string, required | The variable that names a private copy of the built file to the test executables of the `needed-by` members. Every other test executable of the run has it removed. Not a variable the build or the system reads: none that starts with `CARGO`, `RUST`, `TARGO`, `DYLD_` or `LD_`, and not `PATH`, `HOME` or `TMPDIR`. |
| `needed-by` | array of strings, at least one | The workspace members whose tests run the tool: any that `elsewhere` does not name. A change in the tool's directory selects them. |

### `[[workspace]]`

A crate that is its own workspace, tested as `targo test --tests` under its
manifest tests it: a phase before the requests, with its own lockfile, patches
and profiles. It is performed when a changed path lies in its directory, or
when the invocation names no change. Its test executables run in the plan's
pool: `[run] test-jobs`, `test-weight` and `harness-memory-mib` are theirs as
they are the members'. The `[harness]` table names members only.

| Key | Type | Meaning |
|-----|------|---------|
| `manifest` | string, required | Its root manifest, not the invocation's own. Listed once. |
| `cfg` | string | A cfg expression its tests need of the target; where it does not hold, the workspace is neither built nor run and is reported `not-applicable`. Only `unix`, `windows` and the `target_*` keys the target decides, with values the compiler knows. It is the crate-level `#![cfg(..)]` its libraries carry at the head of their root file, and absent where they carry none: an entry that states anything else is refused (exit 2), since a stale one reports a crate `not-applicable` that the target tests, or runs one that compiles to nothing. |

## Exit status

A gate reads one number, and three different answers must not look alike:

| Status | `outcome` | Meaning |
|--------|-----------|---------|
| 0 | `passed` | Every performed request and phase passed and every requirement of the plan was met. |
| 0 | `nothing-selected` | The selection performs nothing. The run also prints a line that starts `SKIPPED: ` on standard error, by which a hook or gate that reads only the status and the text tells a run of nothing from a pass. |
| 101 | `failed` | Red: a test failed that the known-red file does not list, a test executable or a build failed, a phase failed, or a known-red row is stale. A test executable's own exit status is never the run's: one that exits 2 or 3 is red. |
| 2 | `cannot-judge` | No verdict: the invocation or the plan was refused (a changed path under `attribute-under` that nothing accounts for, a range git cannot diff, a reached directory the plan does not test, a section this Targo does not perform, a pool that cannot grant a harness its weight), or a requirement that is no failed test was not met (`min-tests`, `require-pass`, a variant or instrument that judged nothing, known-red rows nobody could check). |
| 2 | `interrupted` | No verdict: a signal stopped the run, or its barrier did (`--run-after`: the file says something other than `run`, or its writer is gone). |
| 3 | `out-of-time` | No verdict: the run's wall bound or a harness's stall bound ran out, or its barrier did not appear in `[run] run-after-seconds`. |
| 1 | none | The command line itself was not understood (an unknown flag, a missing value): the argument parser's status, before any plan is read, with no record. No run of a plan exits 1. |

Red wins where a run shows both a failure and an unmet requirement. A stop
wins over everything: a run Targo stopped has no verdict, whatever had failed
by then.

Against the script lane these classes moved, and every one still blocks: an
instrument that judged nothing was red there (1) and is `cannot-judge` (2)
here, since no test failed; an unmet `min-tests` was 3 there and is 2 here,
since 3 now means time alone.

With `--message-format=json` the last record of every plan invocation is
`reason="test-plan-result"`, and it carries the same `outcome` and
`exit_status`. A run that ran to its end writes its verdict there; one that
ended before it had a verdict (a refusal, a failed build, a stop at the first
failure, a stop by Targo) writes the short form `schema`, `plan`, `phase`,
`passed` (`false`), `outcome`, `exit_status` and `why`. `plan` is spelled the
same in every record of a run: the path from the working directory, made
absolute. A stream that does not end in that record was cut off.
