# cargo-test(1)
{{~*set command="test"}}
{{~*set actionverb="Test"}}
{{~*set nouns="tests"}}
{{~*set multitarget=true}}

## NAME

cargo-test --- Execute unit and integration tests of a package

## SYNOPSIS

`cargo test` [_options_] [_testname_] [`--` _test-options_]

## DESCRIPTION

Compile and execute unit, integration, and documentation tests.

The test filtering argument `TESTNAME` and all the arguments following the two
dashes (`--`) are passed to the test binaries and thus to _libtest_ (rustc's
built in unit-test and micro-benchmarking framework).  If you're passing
arguments to both Cargo and the binary, the ones after `--` go to the binary,
the ones before go to Cargo.  For details about libtest's arguments see the
output of `cargo test -- --help` and check out the rustc book's chapter on
how tests work at <https://doc.rust-lang.org/rustc/tests/index.html>.

As an example, this will filter for tests with `foo` in their name and run them
on 3 threads in parallel:

    cargo test foo -- --test-threads 3

Tests are built with the `--test` option to `rustc` which creates a special
executable by linking your code with libtest. The executable automatically
runs all functions annotated with the `#[test]` attribute in multiple threads.
`#[bench]` annotated functions will also be run with one iteration to verify
that they are functional.

If the package contains multiple test targets, each target compiles to a
special executable as aforementioned, and then is run serially.

The libtest harness may be disabled by setting `harness = false` in the target
manifest settings, in which case your code will need to provide its own `main`
function to handle running tests.

By default, `cargo test` uses the [`test` profile], which enables
some optimizations and disables debugging information for fast feedback. If you need to debug a
test, you can use the `--profile=debug` command-line option to switch to
the debug profile. You can then run the debug-enabled test within a
debugger.

[`test` profile]: ../reference/profiles.html#test

### Documentation tests

Documentation tests are also run by default, which is handled by `rustdoc`. It
extracts code samples from documentation comments of the library target, and
then executes them.

Different from normal test targets, each code block compiles to a doctest
executable on the fly with `rustc`. These executables run in parallel in
separate processes. The compilation of a code block is in fact a part of test
function controlled by libtest, so some options such as `--jobs` might not
take effect. Note that this execution model of doctests is not guaranteed
and may change in the future; beware of depending on it.

See the [rustdoc book](https://doc.rust-lang.org/rustdoc/) for more information
on writing doc tests.

### Working directory of tests

The working directory when running each unit and integration test is set to the
root directory of the package the test belongs to.
Setting the working directory of tests to the package's root directory makes it
possible for tests to reliably access the package's files using relative paths,
regardless from where `cargo test` was executed from.

For documentation tests, the working directory when invoking `rustdoc` is set to
the workspace root directory, and is also the directory `rustdoc` uses as the
compilation directory of each documentation test.
The working directory when running each documentation test is set to the root
directory of the package the test belongs to, and is controlled via `rustdoc`'s
`--test-run-directory` option.

## OPTIONS

### Test Options

{{> options-test }}

### Test Plan Options

These options exist in `targo` only. A test plan is a TOML file that names
several test requests, each what one `targo test -p` command would select; one
invocation builds them in one graph and runs every test executable in the
build's queue. The plan also states the pool its tests run in, what each
harness is counted for, how long the run may take and which tests are expected
to fail, so that one command is a whole test lane. The file, and how a run
is selected, bounded and judged, are described in the test plan reference
(`src/doc/src/reference/test-plan.md` in the Targo sources).

A plan run names what changed with `--changed-range`, `--changed-pushed-refs`
or `--changed-paths` (and what the change reaches with `--reached` or `-p`),
or asks for everything with `--whole-plan`. An invocation that does neither is
refused.

{{#options}}

{{#option "`--plan` _file_" }}
Build and run the requests of the test plan _file_. The plan owns package,
feature, target and harness-argument selection: the options that select those
are refused beside it. It requires `--unverified`.
{{/option}}

{{#option "`--changed-range` _range_" }}
Select the plan's requests from the paths git says _range_ changed. `A..B`
compares the two trees and `A...B` compares `B` with its merge base with `A`,
as `git diff` reads them. Targo runs git itself, without rename detection and
with submodule pointers included, so a renamed file counts as its old path and
its new one and a deleted file as its path. A range git cannot diff is an
error, never an empty change. This flag may be specified multiple times. A
range that changes nothing the plan tests selects nothing: the run exits 0.
{{/option}}

{{#option "`--changed-pushed-refs` _file_" }}
Select the plan's requests from the refs being pushed, as git writes them to a
pre-push hook: one `<local ref> <local sha> <remote ref> <remote sha>` line
per ref, in _file_, or on standard input for `-`. An updated branch is the
range from its remote commit to its local one, a new branch is compared with
the plan's `[select] base`, and a deleted branch pushes no tree. Input that
names no pushed tree at all (no line, or deletions only) is judged as the
standing change, `<base>...HEAD`, never as a push that changes nothing: a hook
that lost its standard input does not exit 0.
{{/option}}

{{#option "`--changed-paths` _file_" }}
Select the plan's requests from the changed paths listed in _file_, or on
standard input for `-`: NUL- or newline-separated, relative to the workspace
root.
{{/option}}

{{#option "`--reached` _dir_" }}
Also test the plan member, or the `[[workspace]]` of the plan, in the directory
_dir_ (from the workspace root): something the change reaches without touching
it. A directory the plan does not test is an error. This flag may be specified
multiple times. With a plan, `-p` names a reached member by package name.
{{/option}}

{{#option "`--whole-plan`" }}
Run every request and phase of the plan, whatever changed. It cannot be
combined with an option that names a change.
{{/option}}

{{#option "`--run-after` _file_" }}
Build, and start no test executable until _file_ exists and says `run`. Any
other content stops the run with exit status 2 and no test run. The plan must
state `[run] run-after-seconds`, how long the run waits with nothing else to
do before it ends with exit status 3; that wait is not charged to the run's
wall bound. A caller that overlaps this run's build with work its tests depend
on writes the file, whole and by rename, when that work has ended.
{{/option}}

{{#option "`--run-after-owner` _pid_" }}
The process that is to write the `--run-after` file. Once it is gone and the
file is not there, the run stops with exit status 2.
{{/option}}

{{#option "`--request` _id_" }}
Narrow the run to the request _id_ of the plan, as a failure's rerun line
gives it. It never adds a request the selection left out. This flag may be
specified multiple times.
{{/option}}

{{/options}}

{{> section-package-selection }}

### Target Selection

Targo also accepts `--require-test-bin NAME`. It keeps the normal target
selection and requires exactly one selected binary test harness with that name
to run and report passing tests. A missing, disabled, feature-ineligible, or
ambiguous binary is an error, even if other test targets pass. The required
binary must use the Rust test harness and cannot use a custom target runner.
This option currently requires Linux or macOS process supervision and a plain
Rust test-harness summary on stdout. It cannot be combined with `--no-run`;
authenticated test execution does not yet support its output check.

When no target selection options are given, `cargo test` will build the
following targets of the selected packages:

- lib --- used to link with binaries, examples, integration tests, and doc tests
- bins (only if integration tests are built and required features are
  available)
- examples --- to ensure they compile
- lib as a unit test
- bins as unit tests
- integration tests
- doc tests for the lib target

The default behavior can be changed by setting the `test` flag for the target
in the manifest settings. Setting examples to `test = true` will build and run
the example as a test, replacing the example's `main` function with the
libtest harness. If you don't want the `main` function replaced, also include
`harness = false`, in which case the example will be built and executed as-is.

Setting targets to `test = false` will stop them from being tested by default.
Target selection options that take a target by name (such as `--example foo`)
ignore the `test` flag and will always test the given target.

Doc tests for libraries may be disabled by setting `doctest = false` for the
library in the manifest.

See [Configuring a target](../reference/cargo-targets.html#configuring-a-target)
for more information on per-target settings.

{{> options-targets-bin-auto-built }}

{{> options-targets }}

{{#options}}

{{#option "`--doc`" }}
Test only the library's documentation. This cannot be mixed with other
target options.
{{/option}}

{{/options}}

{{> section-features }}

### Compilation Options

{{#options}}

{{> options-target-tuple }}

{{> options-release }}

{{> options-profile }}

{{> options-timings }}

{{/options}}

### Output Options

{{#options}}
{{> options-target-dir }}
{{/options}}

### Display Options

By default the Rust test harness hides output from test execution to keep
results readable. Test output can be recovered (e.g., for debugging) by passing
`--no-capture` to the test binaries:

    cargo test -- --no-capture

{{#options}}

{{> options-display }}

{{> options-message-format }}

{{/options}}

### Manifest Options

{{#options}}

{{> options-manifest-path }}

{{> options-ignore-rust-version }}

{{> options-locked }}


{{/options}}

{{> section-options-common }}

### Miscellaneous Options

The `--jobs` argument affects the building of the test executable but does not
affect how many threads are used when running the tests. The Rust test harness
includes an option to control the number of threads used:

    cargo test -j 2 -- --test-threads=2

{{#options}}

{{> options-jobs }}
{{> options-future-incompat }}

{{/options}}

While `cargo test` involves compilation, it does not provide a `--keep-going`
flag. Use `--no-fail-fast` to run as many tests as possible without stopping at
the first failure. To "compile" as many tests as possible, use `--tests` to
build test binaries separately. For example:

    cargo build --tests --keep-going
    cargo test --tests --no-fail-fast

{{> section-environment }}

{{> section-exit-status }}

With `--plan` the exit status says how the run ended, and with
`--message-format=json` the last record, `reason="test-plan-result"`, says the
same in `outcome` and `exit_status`:

* `0`: Every performed request passed and every requirement of the plan was
  met; or the selection performs nothing.
* `101`: Red: a test, a test executable or a build failed, or a test the plan
  expects to fail passed.
* `2`: No verdict: the invocation or the plan was refused, a requirement that
  is no failed test was not met, or a signal interrupted the run.
* `3`: No verdict: the plan's bound on the run's time, or on the time a test
  executable prints nothing, ran out, and Targo stopped the run.

## EXAMPLES

1. Execute all the unit and integration tests of the current package:

       cargo test

2. Run only tests whose names match against a filter string:

       cargo test name_filter

3. Run only a specific test within a specific integration test:

       cargo test --test int_test_name -- modname::test_name

4. Run a test plan over what a commit range changed, as a gate does:

       targo --unverified test --plan tests/test-plans/crates.toml \
           --changed-range origin/main...HEAD --locked --no-fail-fast

5. Run a test plan from a pre-push hook, which receives the pushed refs on
   standard input:

       targo --unverified test --plan tests/test-plans/crates.toml \
           --changed-pushed-refs - --locked --no-fail-fast

## SEE ALSO
{{man "cargo" 1}}, {{man "cargo-bench" 1}}, [types of tests](../reference/cargo-targets.html#tests), [how to write tests](https://doc.rust-lang.org/rustc/tests/index.html)
