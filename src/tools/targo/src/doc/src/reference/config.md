# Configuration

This document explains how Cargo’s configuration system works, as well as
available keys or configuration. For configuration of a package through its
manifest, see the [manifest format](manifest.md).

## Hierarchical structure

Cargo allows local configuration for a particular package as well as global
configuration. It looks for configuration files in the current directory and
all parent directories. If, for example, Cargo were invoked in
`/projects/foo/bar/baz`, then the following configuration files would be
probed for and unified in this order:

* `/projects/foo/bar/baz/.cargo/config.toml`
* `/projects/foo/bar/.cargo/config.toml`
* `/projects/foo/.cargo/config.toml`
* `/projects/.cargo/config.toml`
* `/.cargo/config.toml`
* `$CARGO_HOME/config.toml` which defaults to:
    * Windows: `%USERPROFILE%\.cargo\config.toml`
    * Unix: `$HOME/.cargo/config.toml`

With this structure, you can specify configuration per-package, and even
possibly check it into version control. You can also specify personal defaults
with a configuration file in your home directory.

If a key is specified in multiple config files, the values will get merged
together. Numbers, strings, and booleans will use the value in the deeper
config directory taking precedence over ancestor directories, where the
home directory is the lowest priority. Arrays will be joined together
with higher precedence items being placed later in the merged array.

At present, when being invoked from a workspace, Cargo does not read config
files from crates within the workspace. i.e. if a workspace has two crates in
it, named `/projects/foo/bar/baz/mylib` and `/projects/foo/bar/baz/mybin`, and
there are Cargo configs at `/projects/foo/bar/baz/mylib/.cargo/config.toml`
and `/projects/foo/bar/baz/mybin/.cargo/config.toml`, Cargo does not read
those configuration files if it is invoked from the workspace root
(`/projects/foo/bar/baz/`).

> **Note:** Cargo also reads config files without the `.toml` extension, such as
> `.cargo/config`. Support for the `.toml` extension was added in version 1.39
> and is the preferred form. If both files exist, Cargo will use the file
> without the extension.

## Configuration format

Configuration files are written in the [TOML format][toml] (like the
manifest), with simple key-value pairs inside of sections (tables). The
following is a quick overview of all settings, with detailed descriptions
found below.

```toml
paths = ["/path/to/override"] # path dependency overrides

[alias]     # command aliases
b = "build"
c = "check"
t = "test"
r = "run"
rr = "run --release"
recursive_example = "rr --example recursions"
space_example = ["run", "--release", "--", "\"command list\""]

[build]
warnings = "warn"             # adjust the effective lint level for warnings
jobs = 1                      # number of parallel jobs, defaults to # of CPUs
rustc = "rustc"               # the rust compiler tool
rustc-wrapper = "…"           # run this wrapper instead of `rustc`
rustc-workspace-wrapper = "…" # run this wrapper instead of `rustc` for workspace members
rustdoc = "rustdoc"           # the doc generator tool
target = "triple"             # build for the target triple (ignored by `cargo install`)
target-dir = "target"         # path of where to place generated artifacts
build-dir = "target"          # path of where to place intermediate build artifacts
rustflags = ["…", "…"]        # custom flags to pass to all compiler invocations
rustdocflags = ["…", "…"]     # custom flags to pass to rustdoc
incremental = true            # whether or not to enable incremental compilation
dep-info-basedir = "…"        # path for the base directory for targets in depfiles

[credential-alias]
# Provides a way to define aliases for credential providers.
my-alias = ["/usr/bin/cargo-credential-example", "--argument", "value", "--flag"]

[doc]
browser = "chromium"          # browser to use with `cargo doc --open`,
                              # overrides the `BROWSER` environment variable

[env]
# Set ENV_VAR_NAME=value for any process run by Cargo
ENV_VAR_NAME = "value"
# Set even if already present in environment
ENV_VAR_NAME_2 = { value = "value", force = true }
# `value` is relative to the parent of `.cargo/config.toml`, env var will be the full absolute path
ENV_VAR_NAME_3 = { value = "relative/path", relative = true }

[future-incompat-report]
frequency = 'always' # when to display a notification about a future incompat report

[cache]
auto-clean-frequency = "1 day"   # How often to perform automatic cache cleaning

[cargo-new]
vcs = "none"              # VCS to use ('git', 'hg', 'pijul', 'fossil', 'none')

[http]
debug = false               # HTTP debugging
proxy = "host:port"         # HTTP proxy in libcurl format
ssl-version = "tlsv1.3"     # TLS version to use
ssl-version.max = "tlsv1.3" # maximum TLS version
ssl-version.min = "tlsv1.1" # minimum TLS version
timeout = 30                # timeout for each HTTP request, in seconds
low-speed-limit = 10        # network timeout threshold (bytes/sec)
cainfo = "cert.pem"         # path to Certificate Authority (CA) bundle
proxy-cainfo = "cert.pem"   # path to proxy Certificate Authority (CA) bundle
check-revoke = true         # check for SSL certificate revocation
multiplexing = true         # HTTP/2 multiplexing
user-agent = "…"            # the user-agent header

[install]
root = "/some/path"         # `cargo install` destination directory

[net]
retry = 3                   # network retries
git-fetch-with-cli = true   # use the `git` executable for git operations
offline = true              # do not access the network

[net.ssh]
known-hosts = ["..."]       # known SSH host keys

[patch.<registry>]
# Same keys as for [patch] in Cargo.toml

[profile.<name>]         # Modify profile settings via config.
inherits = "dev"         # Inherits settings from [profile.dev].
opt-level = 0            # Optimization level.
debug = true             # Include debug info.
split-debuginfo = '...'  # Debug info splitting behavior.
strip = "none"           # Removes symbols or debuginfo.
debug-assertions = true  # Enables debug assertions.
overflow-checks = true   # Enables runtime integer overflow checks.
lto = false              # Sets link-time optimization.
panic = 'unwind'         # The panic strategy.
incremental = true       # Incremental compilation.
codegen-units = 16       # Number of code generation units.
rpath = false            # Sets the rpath linking option.
[profile.<name>.build-override]  # Overrides build-script settings.
# Same keys for a normal profile.
[profile.<name>.package.<name>]  # Override profile for a package.
# Same keys for a normal profile (minus `panic`, `lto`, and `rpath`).

[resolver]
lockfile-path = "…"  # Overrides the path used for
incompatible-rust-versions = "allow"  # Specifies how resolver reacts to these

[registries.<name>]  # registries other than crates.io
index = "…"          # URL of the registry index
token = "…"          # authentication token for the registry
credential-provider = "cargo:token" # The credential provider for this registry.

[registries.crates-io]
protocol = "sparse"  # The protocol to use to access crates.io.

[registry]
default = "…"        # name of the default registry
token = "…"          # authentication token for crates.io
credential-provider = "cargo:token"           # The credential provider for crates.io.
global-credential-providers = ["cargo:token"] # The credential providers to use by default.

[source.<name>]      # source definition and replacement
replace-with = "…"   # replace this source with the given named source
directory = "…"      # path to a directory source
registry = "…"       # URL to a registry source
local-registry = "…" # path to a local registry source
git = "…"            # URL of a git repository source
branch = "…"         # branch name for the git repository
tag = "…"            # tag name for the git repository
rev = "…"            # revision for the git repository

[target.<triple>]
linker = "…"              # linker to use
runner = "…"              # wrapper to run executables
rustflags = ["…", "…"]    # custom flags for `rustc`
rustdocflags = ["…", "…"] # custom flags for `rustdoc`

[target.<cfg>]
linker = "…"            # linker to use
runner = "…"            # wrapper to run executables
rustflags = ["…", "…"]  # custom flags for `rustc`

[target.<triple>.<links>] # `links` build script override
rustc-link-lib = ["foo"]
rustc-link-search = ["/path/to/foo"]
rustc-flags = "-L /some/path"
rustc-cfg = ['key="value"']
rustc-env = {key = "value"}
rustc-cdylib-link-arg = ["…"]
metadata_key1 = "value"
metadata_key2 = "value"

[term]
quiet = false                    # whether cargo output is quiet
verbose = false                  # whether cargo provides verbose output
color = 'auto'                   # whether cargo colorizes output
hyperlinks = true                # whether cargo inserts links into output
unicode = true                   # whether cargo can render output using non-ASCII unicode characters
progress.when = 'auto'           # whether cargo shows progress bar
progress.width = 80              # width of progress bar
progress.term-integration = true # whether cargo reports progress to terminal emulator
```

## Environment variables

Cargo can also be configured through environment variables in addition to the
TOML configuration files. For each configuration key of the form `foo.bar` the
environment variable `CARGO_FOO_BAR` can also be used to define the value.
Keys are converted to uppercase, dots and dashes are converted to underscores.
For example the `target.x86_64-unknown-linux-gnu.runner` key can also be
defined by the `CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUNNER` environment
variable.

Environment variables will take precedence over TOML configuration files.
Currently only integer, boolean, string and some array values are supported to
be defined by environment variables. [Descriptions below](#configuration-keys)
indicate which keys support environment variables and otherwise they are not
supported due to [technical issues](https://github.com/rust-lang/cargo/issues/5416).

In addition to the system above, Cargo recognizes a few other specific
[environment variables][env].

## Command-line overrides

Cargo also accepts arbitrary configuration overrides through the
`--config` command-line option. The argument should be in TOML syntax of
`KEY=VALUE` or provided as a path to an extra configuration file:

```console
# With `KEY=VALUE` in TOML syntax
cargo --config net.git-fetch-with-cli=true fetch

# With a path to a configuration file
cargo --config ./path/to/my/extra-config.toml fetch
```

The `--config` option may be specified multiple times, in which case the
values are merged in left-to-right order, using the same merging logic
that is used when multiple configuration files apply. Configuration
values specified this way take precedence over environment variables,
which take precedence over configuration files.

When the `--config` option is provided as an extra configuration file,
The configuration file loaded this way follow the same precedence rules
as other options specified directly with `--config`.

Some examples of what it looks like using Bourne shell syntax:

```console
# Most shells will require escaping.
cargo --config http.proxy=\"http://example.com\" …

# Spaces may be used.
cargo --config "net.git-fetch-with-cli = true" …

# TOML array example. Single quotes make it easier to read and write.
cargo --config 'build.rustdocflags = ["--html-in-header", "header.html"]' …

# Example of a complex TOML key.
cargo --config "target.'cfg(all(target_arch = \"arm\", target_os = \"none\"))'.runner = 'my-runner'" …

# Example of overriding a profile setting.
cargo --config profile.dev.package.image.opt-level=3 …
```

## Including extra configuration files

Configuration can include other configuration files using the top-level `include` key.
This allows sharing configuration across multiple projects
or splitting complex configurations into multiple files.

### `include`

* Type: array of strings or tables
* Default: none
* Environment: not supported

Loads additional configuration files.
Paths are relative to the configuration file that includes them.
Only paths ending with `.toml` are accepted.

Supports the following formats:

```toml
# array of paths
include = [
    "frodo.toml",
    "samwise.toml",
]

# inline tables for more control
include = [
    { path = "required.toml" },
    { path = "optional.toml", optional = true },
]
```

> **Note:** For better readability and to avoid confusion, it is recommended to:
> - Place `include` at the top of the configuration file
> - Put one include per line for clearer version control diffs
> - Use inline table syntax when optional includes are needed

When using table syntax, the following fields are supported:

* `path` (string, required): Path to the config file to include.
* `optional` (boolean, default: false): If `true`, missing files are silently
  skipped instead of causing an error.

The merge behavior of `include` is different from other config values:

1. Config values are first loaded from the `include` paths.
    * Included files are loaded left to right,
      with values from later files taking precedence over earlier ones.
    * This step recurses if included config files also contain `include` keys.
2. Then, the config file's own values are merged on top of the included config,
   taking highest precedence.

## Config-relative paths

Paths in config files may be absolute, relative, or a bare name without any path separators.
Paths for executables without a path separator will use the `PATH` environment variable to search for the executable.
Paths for non-executables will be relative to where the config value is defined.

In particular, rules are:

* For environment variables, paths are relative to the current working directory.
* For config values loaded directly from the [`--config KEY=VALUE`](#command-line-overrides) option,
  paths are relative to the current working directory.
* For config files, paths are relative to the parent directory of the directory where the config files were defined,
  no matter those files are from either the [hierarchical probing](#hierarchical-structure)
  or the [`--config <path>`](#command-line-overrides) option.

> **Note:** To maintain consistency with existing `.cargo/config.toml` probing behavior,
> it is by design that a path in a config file passed via `--config <path>`
> is also relative to two levels up from the config file itself.
>
> To avoid unexpected results, the rule of thumb is putting your extra config files
> at the same level of discovered `.cargo/config.toml` in your project.
> For instance, given a project `/my/project`,
> it is recommended to put config files under `/my/project/.cargo`
> or a new directory at the same level, such as `/my/project/.config`.

```toml
# Relative path examples.

[target.x86_64-unknown-linux-gnu]
runner = "foo"  # Searches `PATH` for `foo`.

[source.vendored-sources]
# Directory is relative to the parent where `.cargo/config.toml` is located.
# For example, `/my/project/.cargo/config.toml` would result in `/my/project/vendor`.
directory = "vendor"
```

## Executable paths with arguments

Some Cargo commands invoke external programs, which can be configured as a path
and some number of arguments.

The value may be an array of strings like `['/path/to/program', 'somearg']` or
a space-separated string like `'/path/to/program somearg'`. If the path to the
executable contains a space, the list form must be used.

If Cargo is passing other arguments to the program such as a path to open or
run, they will be passed after the last specified argument in the value of an
option of this format. If the specified program does not have path separators,
Cargo will search `PATH` for its executable.

## Credentials

Configuration values with sensitive information are stored in the
`$CARGO_HOME/credentials.toml` file. This file is automatically created and updated
by [`cargo login`] and [`cargo logout`] when using the [`cargo:token`] credential provider.

Tokens are used by some Cargo commands such as [`cargo publish`] for
authenticating with remote registries. Care should be taken to protect the
tokens and to keep them secret.

It follows the same format as Cargo config files.

```toml
[registry]
token = "…"   # Access token for crates.io

[registries.<name>]
token = "…"   # Access token for the named registry
```

As with most other config values, tokens may be specified with environment
variables. The token for [crates.io] may be specified with the
`CARGO_REGISTRY_TOKEN` environment variable. Tokens for other registries may
be specified with environment variables of the form
`CARGO_REGISTRIES_<name>_TOKEN` where `<name>` is the name of the registry in
all capital letters.

> **Note:** Cargo also reads and writes credential files without the `.toml`
> extension, such as `.cargo/credentials`. Support for the `.toml` extension
> was added in version 1.39. In version 1.68, Cargo writes to the file with the
> extension by default. However, for backward compatibility reason, when both
> files exist, Cargo will read and write the file without the extension.

## Configuration keys

This section documents all configuration keys. The description for keys with
variable parts are annotated with angled brackets like `target.<triple>` where
the `<triple>` part can be any [target triple] like
`target.x86_64-pc-windows-msvc`.

### `paths`
* Type: array of strings (paths)
* Default: none
* Environment: not supported

An array of paths to local packages which are to be used as overrides for
dependencies. For more information see the [Overriding Dependencies
guide](overriding-dependencies.md#paths-overrides).

### `[alias]`
* Type: string or array of strings
* Default: see below
* Environment: `CARGO_ALIAS_<name>`

The `[alias]` table defines CLI command aliases. For example, running `cargo
b` is an alias for running `cargo build`. Each key in the table is the
subcommand, and the value is the actual command to run. The value may be an
array of strings, where the first element is the command and the following are
arguments. It may also be a string, which will be split on spaces into
subcommand and arguments. The following aliases are built-in to Cargo:

```toml
[alias]
b = "build"
c = "check"
d = "doc"
t = "test"
r = "run"
rm = "remove"
```

Aliases are not allowed to redefine existing built-in commands.

Aliases are recursive:

```toml
[alias]
rr = "run --release"
recursive_example = "rr --example recursions"
```

### `[build]`

The `[build]` table controls build-time operations and compiler settings.

#### `build.warnings`
* Type: string
* Default: `"warn"`
* Environment: `CARGO_BUILD_WARNINGS`

Adjust the effective level of lint warnings for local packages.
Allowed levels are:
* `"warn"`: continue to emit the lints as warnings (default).
* `"allow"`: hide the lints.
* `"deny"`: emit an error for a crate that has lint warnings.
  Use `--keep-going` to see the lint warnings for all dependent crates.

Only warnings that are lints (i.e. level is adjustable) are affected,
e.g. leaving as-is non-lint warnings or warnings from dependencies visible through `--verbose --verbose`.

> **MSRV:** Respected as of 1.97.

#### `build.jobs`
* Type: integer or string
* Default: number of logical CPUs
* Environment: `CARGO_BUILD_JOBS`

Sets the maximum number of compiler processes to run in parallel. If negative,
it sets the maximum number of compiler processes to the number of logical CPUs
plus provided value. Should not be 0. If a string `default` is provided, it sets
the value back to defaults.

Can be overridden with the `--jobs` CLI option.

#### `build.rustc`
* Type: string (program path)
* Default: `"rustc"`
* Environment: `CARGO_BUILD_RUSTC` or `RUSTC`

Sets the executable to use for `rustc`.

#### `build.rustc-wrapper`
* Type: string (program path)
* Default: none
* Environment: `CARGO_BUILD_RUSTC_WRAPPER` or `RUSTC_WRAPPER`

Sets a wrapper to execute instead of `rustc`. The first argument passed to the
wrapper is the path to the actual executable to use
(i.e., `build.rustc`, if that is set, or `"rustc"` otherwise).

#### `build.rustc-workspace-wrapper`
* Type: string (program path)
* Default: none
* Environment: `CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER` or `RUSTC_WORKSPACE_WRAPPER`

Sets a wrapper to execute instead of `rustc`, for workspace members only. When building a
single-package project without workspaces, that package is considered to be the workspace. The first
argument passed to the wrapper is the path to the actual executable to use (i.e., `build.rustc`, if
that is set, or `"rustc"` otherwise). It affects the filename hash so that artifacts produced by the
wrapper are cached separately.

If both `rustc-wrapper` and `rustc-workspace-wrapper` are set, then they will be nested:
the final invocation is `$RUSTC_WRAPPER $RUSTC_WORKSPACE_WRAPPER $RUSTC`.

#### `build.rustdoc`
* Type: string (program path)
* Default: `"rustdoc"`
* Environment: `CARGO_BUILD_RUSTDOC` or `RUSTDOC`

Sets the executable to use for `rustdoc`.

#### `build.target`
* Type: string or array of strings
* Default: host platform
* Environment: `CARGO_BUILD_TARGET`

The default [target platform triples][target triple] to compile to.

Possible values:
- Any supported target in `rustc --print target-list`.
- `"host-tuple"`, which will internally be substituted by the host's target. This can be particularly useful if you're cross-compiling some crates, and don't want to specify your host's machine as a target (for instance, an `xtask` in a shared project that may be worked on by many hosts).
- A path to a custom target specification. See [Custom Target Lookup Path](../../rustc/targets/custom.html#custom-target-lookup-path) for more information.

Can be overridden with the `--target` CLI option.

```toml
[build]
target = ["x86_64-unknown-linux-gnu", "i686-unknown-linux-gnu"]
```

#### `build.target-dir`
* Type: string (path)
* Default: `"target"`
* Environment: `CARGO_BUILD_TARGET_DIR` or `CARGO_TARGET_DIR`

The path to where all compiler output is placed. The default if not specified
is a directory named `target` located at the root of the workspace.

Can be overridden with the `--target-dir` CLI option.

For more information see the [build cache documentation](../reference/build-cache.md).

#### `build.build-dir`

* Type: string (path)
* Default: Defaults to the value of `build.target-dir`
* Environment: `CARGO_BUILD_BUILD_DIR`

The directory where intermediate build artifacts will be stored.
Intermediate artifacts are produced by Rustc/Cargo during the build process.

This option supports path templating.

Available template variables:
* `{workspace-root}` resolves to root of the current workspace.
* `{cargo-cache-home}` resolves to `CARGO_HOME`
* `{workspace-path-hash}` resolves to a hash of the manifest path

For more information see the [build cache documentation](../reference/build-cache.md).

#### `build.action-sandbox` (Trust)

* Type: boolean
* Default: `false`

Native Targo can confine unverified compiler actions on macOS:

```sh
targo --unverified build -Zbuild-dir-new-layout --config build.action-sandbox=true
```

This currently admits Rust library builds and checks without build scripts,
proc macros or compiler wrappers. The compiler and Targo must use the same
native host architecture. Undeclared file reads, writes outside the unit's
output directory and network access are denied. An unsupported action fails;
it does not retry without confinement.

Compiler stdin is an empty stream. The prepared command's arguments, working
directory and final environment participate in cache validation. Scheduler and
subprocess-broker addresses are transport; when Rust source reads such a value
through `env!` or `option_env!`, its actual value is still checked for freshness.

The inherited compiler environment is also declared. Targo captures `PATH`,
`HOME`, locale variables (`LANG`, `LC_ALL`, `LC_CTYPE`, `LC_MESSAGES`, `TZ`),
`RUSTUP_HOME`, `RUSTUP_TOOLCHAIN`, `RUSTC_BOOTSTRAP`, Apple deployment-target
variables, `SDKROOT`, `DEVELOPER_DIR`, and the platform library-search variable.
Declare additional variables with the existing `[env]` configuration:

```toml
[env]
MY_BUILD_INPUT = { value = "default", force = false }
```

With `force = false`, an existing caller value takes precedence. These resolved
values enter the confined fingerprint and are captured for compiler execution.
Other ambient variables are absent from the compiler environment and cannot
invalidate its artifacts. Targo still supplies package metadata, per-action
paths and the selected jobserver separately. Unconfined builds retain their
normal environment inheritance.

This boundary does not yet enable cross-project artifact sharing or certify a
complete hermetic action identity. Process-local state, final per-unit overlays,
input immutability and shared publication require their own checks.

#### `build.test-jobs` (Trust)

* Type: integer, at least 1
* Default: `build.jobs` for native unverified worker admission; `1` otherwise

Maximum number of credits running test harnesses hold together:

```sh
targo --unverified test --config build.test-jobs=4 -j 4
```

Native Targo retains the compilation jobserver for execution. A harness of
weight `w` (see `build.test-weight`) holds `w` tokens of that same pool while it
runs, all taken when it starts or none, and receives `RUST_TEST_THREADS=w`; this
setting creates no second CPU pool. The bound is also capped by `build.jobs` and
by the worker budget. A weight above the bound is lowered to it, so libtest's
threads always equal the credits held. Explicit `--test-threads` arguments,
custom runners and authenticated test execution are not supported by this
opt-in mode. It currently requires Linux or macOS. Without a test plan (see
below), the non-native default preserves
sequential harness execution and its existing libtest thread configuration;
`build.test-weight` and `build.test-harnesses` are checked there but shape
nothing. Documentation tests retain their existing path.

Under native unverified worker admission, an unset value uses `build.jobs` as
the ceiling for independent test executables. An explicit configuration value
or a plan's `test-jobs` takes precedence. Each action still requires its own
actual CPU lease and passes the existing memory admission; each native harness
gets one thread. This ceiling supplies no capacity and does not make a single
harness parallel. Fixed and retained execution keep their existing defaults.

Harnesses start in the queue's priority order, heaviest first among those
ready: one that cannot take its credits yet holds back the harnesses behind it
rather than being starved by lighter ones. Ready compilation is never held back
by a waiting harness, and with no compiler running, ready compilation starts
before any harness. Credits a harness of weight above 1 collects are idle until
it has them all, so Targo asks for them only once the harness fits in the pool
beside the compilation running or ready; until then a running rustc keeps the
pool's free tokens for its own parallel work. A target with `harness = false`
runs at weight 1 and passes or fails by its exit status alone; a weight above 1
on it is refused.

Targo assembles each scheduled command through the ordinary Cargo test path.
Repository `[env]` values (including `force` and `relative`), the package working
directory, dynamic-library search paths and test arguments therefore survive
this compile/execution phase boundary. Use this mode for independent harnesses
instead of extracting `--no-run` executable paths and launching them directly:
those paths alone are not execution recipes. In particular, direct execution
can lose a repository's `RUST_MIN_STACK` and change whether a test completes.

A harness starts only after its own compilation prerequisites succeed. With
fail-fast enabled, a failed harness prevents pending harnesses from starting;
already-running independent harnesses finish. With `--no-fail-fast`, remaining
harnesses run. Parallel jobs use Targo's bounded-output process supervisor;
interruption cancels and reaps the owned process groups.

JSON output adds `test-execution` records with schema
`targo.test-execution.v2`. Each identifies an invocation-local index, total
inventory size, prerequisite artifact, `package_id`, `package`, `target`,
target `kind` (`lib`, `bin`, `test`, `bench` or `example`), `harness`,
`weight`, `exclusive`, state and execution time. States are `ready`,
`running`, `passed`, `failed` and `blocked`. A `passed` or `failed` record
carries the process's `exit_code`, or the `signal` that ended it; both are
`null` when Targo ended the action itself (its cancellation, an output
overflow or an interruption) or never started it. A process that exited by
itself and that Targo then judged failed (a `--require-test-bin` harness that
reported no passing test) keeps its `exit_code`. Each line a harness writes
becomes a `test-output` record with schema `targo.test-output.v1`, naming the
action's `index`, its `stream` (`stdout` or `stderr`) and the `line`, so
concurrent harnesses never share an unattributed line on Targo's standard
output. A line longer than 1 MiB is cut, not refused: it is written once, as
`[line cut: it is longer than 1048576 bytes] ` followed by its first bytes,
1 MiB together, and the harness runs on and is judged by its tests. All a
harness writes to one stream still counts against that stream's limit (512
MiB, more on a machine with more memory), past which Targo ends the action.
Documentation tests keep their existing path and output.

A test plan (`targo --unverified test --plan <FILE>`, narrowed by `--request
<ID>`; [Test Plans](test-plan.md) lists every key of the file) always runs in
this queue, also with `build.test-jobs` unset or 1: each request has its own
harness arguments, and the sequential runner has one argument list. A test executable runs once per distinct argument list of the
requests that selected it; requests with equal arguments share that one action.
The actions of one test target (the runs of one executable, and the builds of
that target under other features) never overlap: each starts after the one
before it ended. A failed one releases the next unless the failure stopped the
run (fail-fast), in which case the rest are reported `blocked`. Without JSON,
each `Running` line ends with the action's request ids in brackets.

Which requests a plan run performs follows from what the invocation says
changed; Targo runs no version-control command. `--changed-paths <FILE>` (`-`
for standard input) names paths relative to the workspace root, separated by
NUL when the input holds one and by newlines otherwise; each is a normal
relative path (no leading `/`, no `.`, `..` or empty component). A
newline-separated line that is quoted, holds a control character (the `\r` of a
CRLF file) or starts or ends with white space is an error, since a tool that
printed it may have altered the name: pass such paths NUL-separated. A plan
whose member lies outside the workspace root takes no `--changed-paths`, since
no such path can name that member's files. A plan member
is *touched* when its directory is the longest member directory a changed path
lies under, so a nested member keeps its own paths. `-p <SPEC>` names a plan
member the change *reaches* without touching; with a plan it has no other
meaning, and a spec that names no plan member is an error. `[default]` tests
the touched and reached members, a `[[variant]]` runs iff its package is one of
them, and an `[[instrument]]` runs iff a changed path starts with one of its
`when-changed` entries or ends with its `when-changed-suffix` (paths under a
`not-under` entry never count), unless its host is touched and the `[default]`
run of that host performs everything the instrument would judge. It does only
when the instrument has no `require-pass`, passes no harness option (an
argument starting with `-`), and names only targets `--tests` runs under default
features (no `test = false`, no `required-features`); otherwise the instrument
runs beside the default run. An instrument with neither condition runs under
every selection. With neither `--changed-paths` nor `-p`, every request runs.
A plan without `[default]` tests only the members its variants name: `-p` of
another member is an error, and its paths are not accounted for.
`--request` then narrows the performed requests and never adds one.

A changed path that starts with a `select.attribute-under` entry must be
accounted for: owned by a plan member, by a member `select.elsewhere` names
another lane for (reported, with that lane's command), or by the directory of a
`[[workspace]]` manifest or of a `[[tool]]` manifest that no member owns.
Otherwise the invocation exits with status 2 before
resolving or building anything, listing each such path. A selection that
performs no request and no phase (below) exits 0 having resolved and built
nothing (so `--locked` checks no lockfile), after the plan passed the checks
every other route makes. Each request's harness arguments are checked whether
or not the selection performs it.

`[[tool]]` and `[[workspace]]` entries name builds outside the plan's graph.
Each is a phase under its own manifest, performed in this process before the
plan's requests, one after another, tools first; `--unit-graph` performs none
and says so. A `[[workspace]]` manifest is the root of a workspace of its own
(its own lockfile, patches and profiles); a `[[tool]]` manifest may also be a
member of the invocation's workspace. A manifest is written one way, as a
changed path is: relative to the workspace root with `/`, with no `.`, `..` or
empty part.

* `[[tool]]` (`manifest`, `bin`, `env`, `needed-by`) is built as `targo build
  --bin <bin>` under `manifest` builds it (the `dev` profile, the invocation's
  jobs and `--target`), when a request this run performs tests a member
  `needed-by` names; otherwise it is not built. The built file is copied into a
  private directory beside it, and the copy's path is set as the variable `env`
  for the test executables of the `needed-by` members and for no other: every
  other test executable of the run, a `[[workspace]]`'s included, has the
  variable removed, whatever the invocation's environment holds. The copy is
  deleted when the invocation ends. A changed path in the tool's directory
  selects the `needed-by` members as `-p` would, so the tool is built and the
  tests that run it run; a conditional instrument hosted on one of them runs
  too where no default run tests that host. If no request of the plan tests a
  `needed-by` member, a run with such a path is refused (status 2). A tool that fails to build ends the
  invocation with status 101 before any test, with or without
  `--no-fail-fast`. `--no-run` builds the tool and makes no copy. `needed-by`
  names members this plan can test, and `env` is a plain variable name that is
  not one Cargo, rustc or the loader reads.
* `[[workspace]]` (`manifest`, optional `cfg`) names the root manifest of a
  crate that is its own workspace. It is tested as `targo test --tests` under
  that manifest tests it, when a changed path lies in its directory or when the
  invocation names no change (`-p` alone selects none). The phase is a plan run
  of that workspace's default members: every harness is held to its closing
  line and counted, and `[default] min-tests` is asked of each of those
  members. A run that reports no test at all fails the phase, with or without
  a `min-tests`. `[harness]` and `[expect] known-red` do not apply to it. The
  phase reads configuration as the invocation does, from its own directory
  upwards: a `.cargo/config.toml` between the workspace root and the
  `[[workspace]]`'s directory would be read only by a run inside that
  directory, so a selected workspace that has one is refused. A `cfg`
  expression is held against the build's target first; where it does not hold
  the workspace is neither built nor run and is reported as `not-applicable`.
  It may test only what the target decides: `unix`, `windows`, and
  `target_abi`, `target_arch`, `target_endian`, `target_env`, `target_family`,
  `target_os`, `target_pointer_width` or `target_vendor` with a value the
  compiler knows for some target (asked of `rustc --print=check-cfg`). Any
  other name or key, a constant, or an unknown value is refused on every run:
  it would report the workspace as not for this target on every host.
  `--request` leaves a selected workspace out (`left-out`) and sets `narrowed`.
  A failed workspace fails the run: without `--no-fail-fast` the invocation
  stops there; with it, the phases and requests after it still run and the
  result record lists it in `unmet`. A phase that does not run to its end (a
  build failure, an interruption) ends the invocation.

With JSON messages each phase that builds anything is bracketed by two
`reason="test-plan-phase"` records with schema `targo.test-plan-phase.v1`
(`plan`, `kind`, `manifest`, `state`, `why`, `env`, `tests`): one with `state`
`started` and one with its outcome (`built`, `passed`, `failed`); a phase that
builds nothing writes the outcome alone (`not-needed`, `not-selected`,
`left-out`, `not-applicable`). A phase the invocation ends in (a tool that does
not build, a workspace that fails without `--no-fail-fast`) still writes its
closing `failed` record, which is then the last record: a `started` with no
closing record is a run that was cut off. Every record between the two is that phase's,
and a test action's `index` is counted within its phase. A workspace's run that
ran to its end writes `reason="test-plan-phase-result"`, the result record's
shape with `phase` set to its manifest.

With JSON messages, the first record of a plan invocation is
`reason="test-plan"` with schema `targo.test-plan-selection.v1`: the `plan`
path, the `sha256` of the file's bytes, `selection` (`changed_paths`: every
changed path the run read, from `--changed-paths`, `--changed-range` and
`--changed-pushed-refs` together, or `null` where none was given;
`changed_ranges`, the ranges diffed; the `-p` values as `packages`; the
`--reached` directories as `reached`; `whole_plan`; the `--request` ids as
`requests`), `members` (`touched`, `reached`, `selected`), one `requests` row
per request of the file (`id`, `role`, `packages`, `active`, `why`),
`elsewhere` (`member`, `command`, `paths`), `workspaces` (the `[[workspace]]`
manifests a changed path lies under; every one of the plan when neither
selection input is given), `tools` (the `[[tool]]`s a changed path lies under:
`manifest`, `members`, `paths`) and `unattributed` (`path`, `why`). It is
written before a status 2 refusal and left out under `--unit-graph`, whose
output is one document of its own. A run that performs no request still ends
with the `test-plan-result` record.

A plan's `test-execution` records have schema `targo.test-execution.v3`: the v2
keys, then `requests` (the ids of the requests the action runs for, in plan
order), `features` (the features the executable was built with, which is the
built unit's activated set and not the request's list), `args` (the harness
arguments of this action), `memory_mib` (what the action is counted for
against the run's memory budget, 0 where the plan counts none),
`expected_seconds` (the plan's `[harness] seconds` for it, 0 where it states
none) and `tests`. On a terminal record `tests` is what the
harness reported, `{passed, failed, ignored, filtered_out}`, read from libtest's
closing `test result:` line (the last one printed); it is `null` before the
action ends, for an action that never ran, and wherever the exit and the
closing line disagree. A target with `harness = false` prints no summary and
counts as one test, passed on exit 0 and failed otherwise. Runs without a plan
keep v2, key for key.

A harness that exits 0 is held to its closing line: without a complete
`test result: ok.` line as the last one (it exited from inside a test, or a
`FAILED` line closed the run) the action is recorded `failed` with its own
`exit_code` of 0. The closing line must close the run the harness announced:
its passed, failed, ignored and measured numbers add up to the N of the first
`running N tests` line, and only blank lines follow it. A harness's stdout also
carries whatever its tests write past libtest's capture and whatever a child
process they start prints, so a closing line that fails this is not taken for
the harness's own. A request's `args` may not select another output format
(`--format json`, `--format junit`), which prints none of these lines. A plan
run that ran to its end then asks what the plan asks.
With `[default] min-tests = N`, each member of `[default]` must have reported at
least N tests (passed plus failed; ignored and filtered-out tests judge
nothing), summed over the default run and the member's `[[variant]]` runs; an
instrument's run credits no member. `min-tests = 0` is refused. A run from which
`--request` left out `[default]` or a variant has only part of that sum, so it
does not judge `min-tests` and warns that it does not; leaving out only
instruments takes nothing from the sum, and `min-tests` is judged. Each
`[[variant]]` must itself report a test over its executables: one whose feature
set compiles no test in fails, even where its member's `min-tests` is met
elsewhere. Each name in an instrument's `require-pass` must appear as
`test <name> ... ok` in the output of one of that instrument's test
executables: an ignored, filtered-out, renamed or failed test does not. A
`#[should_panic]` test is named by its path alone; its line
`test <name> - should panic ... ok` is that test passing. A harness's result
lines are read only where they number what its closing line says passed, and a
name that also printed another result (`ignored`, `FAILED`) did not pass; a
harness run with `--quiet` prints no result lines and satisfies no
`require-pass`. These checks catch output on a harness's stdout that is not
libtest's by its disagreement with libtest's own lines; test code written to
forge every line consistently is not detected. A requirement that is not met
ends the run with one error listing each, and with exit status 2 (the run
could not judge) unless something else it judged is red, which is 101
([the plan's exit status](test-plan.md#exit-status)).

With JSON messages, such a run's last record is `reason="test-plan-result"`
with schema `targo.test-plan-result.v1`: the `plan` path, `passed`, `outcome`
and `exit_status` (how the run ended, as its exit status says it), `narrowed`
(`--request` left out a request the selection performs, so `passed` is not that
selection's verdict), `min_tests_skipped` (the plan sets `min-tests` and this run did not
judge it), one `requests` row per request (`id`, `actions`, `failed`, `excused`, `tests`,
`passed`), one `members` row per member `min-tests` was judged for (`package`,
`tests`, `min_tests`, `passed`), `unmet`, the requirements not met, and
`known_red` (`null` without `[expect] known-red`), `phase` (`null`) and
`phases`, one row per `[[tool]]` and `[[workspace]]` entry in the shape of its
closing `test-plan-phase` record. A run that ended before it had a verdict (a
refused invocation, a failed build, a stop at its first failure without
`--no-fail-fast`, a run Targo stopped for time or for a signal) closes with
the short form of the same record: `schema`, `plan`, `phase`, `passed`
(`false`), `outcome`, `exit_status` and `why`. Every plan invocation's JSON
therefore ends in one `test-plan-result` record, and a stream without one was
cut off.

A plan's `[harness.<package>.<kind>[.<name>]]` tables are the harness policy of
its run, with the keys of `build.test-harnesses` (`weight`, `exclusive`,
`memory-mib`, `seconds`). They are its only source: a non-empty
`build.test-harnesses` beside a plan is an error on every route, including
`--no-run` and a selection that performs nothing. A plan's `[run]` table
states its pool, its memory count and its bounds
([reference](test-plan.md#run)); `build.test-jobs`, `build.test-weight`,
`build.test-memory-mib`, `build.test-wall-seconds` and
`build.test-stall-seconds` stand over it, and `-j` stays the caller's.

What a script lane took from its caller's environment maps onto this:

| Script lane | Targo |
|-------------|-------|
| `TRUST_CRATES_TESTS_JOBS=N` binaries at once, `RUST_TEST_THREADS=T` each | `[run] test-jobs = N×T` and `test-weight = T`; on one host, `CARGO_BUILD_TEST_JOBS` and `CARGO_BUILD_TEST_WEIGHT` (or `--config`). A harness gets as many libtest threads as credits: Targo sets `RUST_TEST_THREADS` for each, and one the caller exported is replaced. |
| `CARGO_BUILD_JOBS` | Unchanged: the size of the one pool compilers and tests share (`-j`). Test credits never exceed it. |
| A build-slot job (`BUILD_SLOT_HELD=1`, `CARGO_BUILD_JOBS=<share>`) | Read as before: the share bounds the test credits and each weight, and must be a positive decimal. No flag is needed. |
| 16 GiB per binary against the memory available | `[run] harness-memory-mib`; the budget is measured by Targo, or `CARGO_BUILD_TEST_MEMORY_MIB`. |
| `TRUST_CRATES_TESTS_BUDGET_S`, `TRUST_CRATES_TESTS_STALL_S` | `[run] wall-seconds` and `stall-seconds`; `CARGO_BUILD_TEST_WALL_SECONDS`, `CARGO_BUILD_TEST_STALL_SECONDS`. |
| `TRUST_RUSTC` | Not Targo's: the tests that need a Trust compiler read it from the environment Targo passes on. Targo compiles with `RUSTC`. |
| `--range A..B`, `--push-context`, `--also-members` | `--changed-range`, `--changed-pushed-refs -`, `--reached`. Note `--changed-range A..B` is git's own two-tree diff; the script read `A..B` as git's `A...B`. |
| exit 1 red, 2 cannot judge, 3 out of time | 101, 2, 3. |

`[expect] known-red = "<file>"` names a file under the workspace root that
lists the tests the plan expects to fail, one `<test binary>::<test path>` per
line: the test target's crate name (its executable's file name without the
hash) and the name libtest prints. `#` starts a comment, and a comment
containing `[flaky]` marks a test that may pass or fail. A missing file, a path
that a symlink leads out of the workspace, a row of another shape and a key
listed twice are errors on every route. A key names its binary by crate name
alone, so a row whose binary name more than one test target of the workspace
has (two packages with a `tests/it.rs`, or a lib and an integration test of
its name; packages `select.elsewhere` names are not counted) is also an error
on every route, whatever the run selects: it would excuse the test in each of
them. A row applies to its test under every request that runs the binary. The
file is a ratchet:

* A harness that failed only in listed tests is *excused*. Its record stays
  `failed` with its own exit code, its request counts it under `excused`, and
  it does not fail the run.
* A failed test the file does not list is a new failure, and its harness
  fails the run as without the file.
* A listed test that passed is a stale row. It is an unmet requirement (exit
  status 101) until the row is deleted, unless the row is `[flaky]`.
* A row is judged by its harness's result lines. A harness with listed tests
  that passed while its result lines were not read (it printed `ok` lines its
  closing line does not count, as a child process writing to stdout or
  `--format terse` does, or its target has `harness = false`) is *unjudged*,
  and an unmet requirement: a listed test that passed there would go unseen.

Only a failure libtest reported test by test is excused: the harness exited
with a code, closed the run it announced with `test result: FAILED.`, and
printed as many `FAILED` and `ok` result lines as that line counts. A crash, a
signal, a harness that exited 0 and was judged failed, and a target with
`harness = false` name no failed test, so no row excuses them; where such a
harness has listed tests, a note and the result record say why nothing was
excused. The file is judged over a run that ran to its end, so a run of a plan
with `known-red` requires `--no-fail-fast`, and so does a selection that
performs nothing. The result record's `known_red` holds the `file`, its
`sha256`, and five lists: `excused` (listed tests that failed in an excused
harness), `not_excused` (listed tests that failed in a harness that also
failed in an unlisted test), `new_failures` (failed tests the file does not
list), `stale`, and `unjudged` (one `package`, `binary`, `failed`, `why` row
per harness with listed tests whose result lines were not read).

A plan run fails, whatever its harnesses exit with, when a request selected no
test executable, and when an action that runs for an `[[instrument]]` reported
no passing test (a filter that matched nothing, or only ignored tests); such
an action is recorded `failed` with the harness's own `exit_code` of 0. A
target with `harness = false` is judged by its exit status alone. An
instrument's `args` may not contain `--list`, `--help` or `-h`, and request ids
are plain words (ASCII letters, digits, `_`, `.`, `-`, not starting with `-`).
A failed action is reported with the target that failed and the arguments that
rerun it: the plan and one of its requests, a single-package request where
there is one. A failure inside a `[[workspace]]` phase is reported with the
command that reruns that workspace (`targo --unverified test --manifest-path
<its manifest> --tests`, without `--plan`), and the phase's `Running` lines are
labelled `[workspace <manifest>]`.

With nothing running, a pool Targo created returns its tokens at once. If a
harness still lacks its credits after 30 seconds of that, the pool lost
tokens (a client that exited or was killed while holding them; rustc's
parallel frontend, `-Zthreads`, sometimes exits holding one): the run fails
and the tests still pending are reported `blocked` rather than waited for
forever. A lost token is never minted again, since Targo cannot tell it from
one a surviving process still holds.

These are process-execution observations, not proof or test-result cache
authority. Arbitrary test code can consume resources outside the cooperative
CPU budget, including more threads than its weight; this setting is not an RSS
limit or a filesystem sandbox.

#### `build.test-weight` (Trust)

* Type: integer, at least 1
* Default: `1`

The credits, and libtest threads, each libtest harness holds under
`build.test-jobs` unless `build.test-harnesses` sets its own. Targets with
`harness = false` always hold 1.

When Targo runs under an inherited jobserver (another `make` or Cargo) or
native worker admission is requested, a weight still above 1 after the
`build.test-jobs` bound is refused before anything is built: neither can
promise a harness all of its credits at once.

#### `build.test-memory-mib` (Trust)

* Type: integer
* Default: measured: the memory available when the run begins, less an eighth
  of the host's (at least 1 GiB)
* Environment: `CARGO_BUILD_TEST_MEMORY_MIB`

The mebibytes running test executables may be counted for together, where a
harness policy counts any (`memory-mib` of a `build.test-harnesses` or
`[harness]` entry, or a test plan's `[run] harness-memory-mib`). A test
executable starts only while the counts of the running ones and its own fit;
one counted for more than the whole budget runs with no other test beside it.
This is admission by a stated figure, not a limit on what a test may use.

#### `build.test-wall-seconds` (Trust)

* Type: integer, at least 1
* Default: none
* Environment: `CARGO_BUILD_TEST_WALL_SECONDS`

Seconds a test plan's whole invocation may take, over the plan's `[run]
wall-seconds` and `wall-seconds-per-member`. A run past it is stopped, with its build if that is what is running, and
exits 3. It has no effect without `--plan`.

#### `build.test-stall-seconds` (Trust)

* Type: integer, at least 1
* Default: none
* Environment: `CARGO_BUILD_TEST_STALL_SECONDS`

Seconds a running test executable of a test plan may print nothing, over the
plan's `[run] stall-seconds`. A run with one silent for longer is stopped and
exits 3.

Without a plan, this is the inactivity window of each actual test executable
and its current descendants on Linux and macOS. Output bytes or measured
process-tree CPU/disk-I/O activity keep that executable active. Incomplete
native observations never count as zero activity; persistent observation loss
refuses execution. The existing owner stops and retires its original process
group on expiry. This policy grants no CPU or memory resources and does not
reinterpret a harness's expected `seconds` or reserved `memory-mib` as limits.
Configured activity supervision refuses retained execution, unsupported hosted
executors and rustdoc-owned generated test processes instead of omitting the
requested supervision. Ordinary execution without this policy is unchanged.

The native ordinary-test API can also carry an independent child policy. The
actual receiver combines each bound with its effective configuration using the
minimum; a caller cannot widen a configured inactivity window or remove a
resident-byte ceiling. These are execution limits, not expected durations,
memory reservations or CPU grants. Plans, prepared sessions and retained test
execution refuse this ordinary-only request rather than ignoring it.

#### `build.test-harnesses` (Trust)

* Type: table
* Default: none

Admission for individual test targets under `build.test-jobs`, keyed by package
and then by the target selector's kind (`lib`, `bin`, `test`, `bench`,
`example`) and, except for `lib`, the target's name:

```toml
[build.test-harnesses.my-package.test.integration]
weight = 4

[build.test-harnesses.my-package.test.uses-global-state]
exclusive = true

[build.test-harnesses.my-package.lib]
weight = 2
```

`weight` overrides `build.test-weight` for that target. `memory-mib` counts
the harness against `build.test-memory-mib` while it runs, and `seconds`
says how long it is expected to run: among the harnesses ready to start, the
longest expected one starts first. An `exclusive` harness
starts only once no compilation is running or ready and nothing else runs, and
nothing starts beside it; it is scheduled after the other harnesses, so it must
not be one another test waits for. Unknown kinds and settings, a zero weight,
`memory-mib` or `seconds`, and a target a workspace member does not have are refused before anything is
built. An entry for a package outside the workspace is checked the same way,
before any test body runs, for every version of that package the run tests,
whether through its harnesses or only its doctests. With `build.test-jobs`
above 1, an entry for a package the run does not test draws a warning; the
sequential runner, which applies none of this table, says nothing. Environment
variables cannot spell this table and are refused; use a config file or
`--config`.

#### `build.shared-dependency-cache` (Trust)

* Type: boolean
* Default: `false`

Share eligible dependency compilations between projects on the same
machine and under the same `CARGO_HOME`. A repository can check the key in:

```toml
# .cargo/config.toml
[build]
shared-dependency-cache = true
```

The key takes effect only for a native `targo --unverified` build on macOS
whose compiler reports the native host triple and runs without a compiler
wrapper (`build.rustc-wrapper` or `build.rustc-workspace-wrapper`). Such a
build turns on the fine-grain locking the shared store needs by itself, as
`-Zfine-grain-locking` would, with no `-Z` flag on the command line. Every
other lane (`targo trust`, a host that is not macOS, a cargo-named invocation,
a compiler wrapper, a foreign host architecture) runs exactly as with the key
unset and never reads or writes the store; its `shared-dependency-policy`
record says `enabled: false`. `enabled: true` says the key applies to the
build, not that a unit was shared: where no unit is eligible, the build still
creates the store and uses fine-grain locking, and each unit's decision record
says why it stayed private.

Targo selects registry library units and external path dependencies outside
the current workspace whose entire dependency graph can be compiled without
build scripts or proc macros, and the library units of workspace members whose
dependencies are shared too, apart from their own build script and the proc
macros they load. Selected units use the confinement and declared environment
contract described above, except that an ambient deployment target, `SDKROOT`
or `DEVELOPER_DIR` reaches a shared unit's compiler only where `[env]`
declares it. Other units retain ordinary private build directories and
execution, so a project can still use build scripts and proc macros without
placing their results in this shared store. A library outside the workspace
that links a member with a build script stays private
(`member-script-dependency`): that script's output reaches its command.

A workspace member's library (needing a compiler that takes
`-Ztrust-path-free`) is compiled with the workspace directory remapped to `.`
in every scope, without incremental state, and under `-Ztrust-path-free`, so
its bytes name no checkout. Its slot is named by its unit, its sources
digested without the checkout's path, the platform its compiler sees, the
compiler, its prepared command (environment and arguments, with the
checkout's and the slot's own paths read as tokens), and each dependency's
slot; it records the SHA-256 of every library it consumed through `--extern`
and is fresh only while those bytes are unchanged. A second checkout at the
same commit reads the slots in place; a member built another way (as a
requested package or as a dependency only, say) takes another slot. A shared
unit's compiler is not given the terminal's width (`--diagnostic-width`), so
its command does not follow the terminal a build runs in.

In a git work tree only committed sources are shared: a member with a change
git reports at or below its package directory (modified, staged, untracked)
is compiled privately with its incremental state (`member-uncommitted`), and
so is each member that depends on it. A member also stays private, compiled in
the project's build directory as without the key, where its package directory
holds or sits in a build output, the cargo home or the store, or would write a
trim-paths unremap file; where the caller's flags remap paths
(`--remap-path-prefix`, `--remap-path-scope`, `-Zremap-cwd-prefix`), under
`targo fix` and under a forced rebuild (all `member-not-confined`); and where
its package tree cannot be captured, as when it holds a link
(`member-source-uncaptured`). A shared compile that fails is not reported: the
build is planned again in the same invocation with the member private, whose
compile reports what it reports. The checkout records why in its build
directory, under `.targo-member-private`: `path-bound` where the compiler
refused the member's metadata because it needs its real path (held while the
environment, compiler, lockfile and member manifest are unchanged), and
`member-compile-failed` for any other failure, such as a read outside the
package that its confinement denies (held while its sources, environment and
compiler are unchanged). A slot that holds a unit recorded for other bytes is
never written over (`member-slot-differs`, recorded the same way), and a
member whose sources move during the build is private for that invocation.
Under the remap, `file!()` and panic locations in a shared member read as
workspace-relative paths.

Build scripts and proc macros themselves stay in each checkout: a member's
build script runs there, and a proc macro, from the workspace or not, is
compiled there. A member with a build script, or that loads a proc macro, is
shared keyed on what they produced in this checkout: the stdout of each build
script whose directives reach its command (its own, and those of the
libraries it links and the proc macros it loads), its own script's `OUT_DIR`
tree, and the bytes of each proc macro's library. These name its slot, so two
checkouts whose scripts print the same and whose macros are the same bytes
share it, and any difference (a script that prints its checkout's path, say)
names another slot. The member's compile may read its own script's `OUT_DIR`
and each macro's library directory, and nothing else of theirs. They are read
when the build is planned and again before the member's job uses its slot; a
member whose script has not yet run in this checkout, or whose macro is not
yet built, waits: the build is planned again in the same invocation once they
have run. A waiting member stops only its dependents: the scripts, macros and
members that do not depend on it still run, so a checkout's first build is
usually planned twice. A member whose inputs change after that, or cannot be
read whole (a link in `OUT_DIR`), is private for the invocation
(`member-inputs-moved`). A script whose output a `links` override in
configuration replaces prints nothing, so its member waits, is renamed, and is
then private for the invocation. The whole stdout is the key, `cargo::warning`
and `rerun-if` lines included, so a script that prints a changing warning
shares nothing. Code that reads `OUT_DIR` with `include!(concat!(env!("OUT_DIR"),
…))` reads a host path through `env!`, which `-Ztrust-path-free` refuses: such a
member is path-bound. `OUT_DIR` keys a member mostly through what it bundles
from there, a native library a script built.

A proc macro runs inside the member's compile and may read what no key holds:
an environment variable or a file with `std::env::var` or `std::fs`, the
working directory, a span's file. `-Ztrust-path-free` judges only the
member's metadata. Before a shared member's job ends, its library and metadata
are searched for the checkout's directories, as spelled and canonical: the
workspace, the member's package, and the target and build directories. A
member whose outputs name one is path-bound, and its outputs leave the store
but for metadata that names none. The compiler's dep-info is not searched: it
names what the compile read, a macro's library and the files of `OUT_DIR`
among them, at the compiling checkout's path, and the key holds those bytes. Directories every
checkout sharing the store has in common (the store, `CARGO_HOME`, `HOME`)
bind no slot to a checkout and are not searched for. What a macro reads that
is not a path of the checkout (a file outside it, the time) is not keyed; the
member's compile can read only its sources, its dependencies' outputs, its own
script's `OUT_DIR` and its macros' library directories.

Shared unit files live under `CARGO_HOME/trust/native-dependencies-v1`. Targo
requires a local filesystem and owned directories that other users cannot write, checks recorded
inputs and output digests, and coordinates readers and writers through a
per-unit lock. A waiting builder checks freshness again after obtaining its
lock. This is a local development cache, not a verified verdict or a remote
artifact trust policy. `targo clean` remains scoped to project build outputs.

A build that shares can also name a unit source, a program that may hold
shared units staged elsewhere, in the Targo-internal environment variable
`TRUST_TARGO_UNIT_SOURCE`. No process the build starts sees it: not the
compiler, a build script, a test or a run. Where the check of a shared unit
misses under its lock, the unit's worker asks the source, which Targo starts
once per build at its first ask, with one JSON line on its standard input:
`{"key":…,"staging":…,"version":1}`. The key is the SHA-256 of the fingerprint
record this build computed for the unit; the staging folder is a new private
folder inside the store. The source may send `working` lines while it stages,
then answers with one line, `staged` (it laid the unit out in that folder as
the unit's own `fingerprint/` and `out/` folders, each file a copy or clone it
owns alone, never a hard link) or `none`. Targo renames only the unit's
planned files into the unit's directory, and only where the staged
fingerprint record is the computed one, every planned file is a plain file
with one link and no folder on the way is a link; placed files get the
store's mode. It then checks the unit again: it takes the unit where the
fingerprint and the outputs' receipt hold, and otherwise removes what it
placed, refuses the unit and compiles it. A unit whose dependency this build
compiled is compiled, as it would be with no source. A unit's
`shared-dependency-decision` record says `taken`, or `refused` with its reason
(`fingerprint-differs`, `output-integrity`, `incomplete` or `stale`). Asks are
answered one at a time. A source that stays silent for 2 seconds (a `working`
line breaks the silence), takes more than 120 seconds over one ask, exits, or
sends any other line, or a line before it is asked, is killed and passed over
for the rest of the build. When the build ends the source's input is closed,
it has 2 seconds to exit before it is killed, and the build's staging folder
is removed. The key and the receipt bind the store's absolute path and the
keyed environment, so a unit is taken only where the cargo home path and that
environment match. The source is trusted as far as it sends a fingerprint
record and receipt: name only a program that serves units from builders
allowed to run here.

#### `build.rustflags`
* Type: string or array of strings
* Default: none
* Environment: `CARGO_BUILD_RUSTFLAGS` or `CARGO_ENCODED_RUSTFLAGS` or `RUSTFLAGS`

Extra command-line flags to pass to `rustc`. The value may be an array of
strings or a space-separated string.

There are four mutually exclusive sources of extra flags. They are checked in
order, with the first one being used:

1. `CARGO_ENCODED_RUSTFLAGS` environment variable.
2. `RUSTFLAGS` environment variable.
3. All matching `target.<triple>.rustflags` and `target.<cfg>.rustflags`
   config entries joined together.
4. `build.rustflags` config value.

Additional flags may also be passed with the [`cargo rustc`] command.

If the `--target` flag (or [`build.target`](#buildtarget)) is used, then the
flags will only be passed to the compiler for the target. Things being built
for the host, such as build scripts or proc macros, will not receive the args.
Without `--target`, the flags will be passed to all compiler invocations
(including build scripts and proc macros) because dependencies are shared. If
you have args that you do not want to pass to build scripts or proc macros and
are building for the host, pass `--target` with the [host triple][target triple].

It is not recommended to pass in flags that Cargo itself usually manages. For
example, the flags driven by [profiles](profiles.md) are best handled by setting the
appropriate profile setting.

> **Caution**: Due to the low-level nature of passing flags directly to the
> compiler, this may cause a conflict with future versions of Cargo which may
> issue the same or similar flags on its own which may interfere with the
> flags you specify. This is an area where Cargo may not always be backwards
> compatible.

#### `build.rustdocflags`
* Type: string or array of strings
* Default: none
* Environment: `CARGO_BUILD_RUSTDOCFLAGS` or `CARGO_ENCODED_RUSTDOCFLAGS` or `RUSTDOCFLAGS`

Extra command-line flags to pass to `rustdoc`. The value may be an array of
strings or a space-separated string.

There are four mutually exclusive sources of extra flags. They are checked in
order, with the first one being used:

1. `CARGO_ENCODED_RUSTDOCFLAGS` environment variable.
2. `RUSTDOCFLAGS` environment variable.
3. All matching `target.<triple>.rustdocflags` and `target.<cfg>.rustdocflags`
  config entries joined together.
4. `build.rustdocflags` config value.

Additional flags may also be passed with the [`cargo rustdoc`] command.

> **Caution**: Due to the low-level nature of passing flags directly to the
> compiler, this may cause a conflict with future versions of Cargo which may
> issue the same or similar flags on its own which may interfere with the
> flags you specify. This is an area where Cargo may not always be backwards
> compatible.

#### `build.incremental`
* Type: bool
* Default: from profile
* Environment: `CARGO_BUILD_INCREMENTAL` or `CARGO_INCREMENTAL`

Whether or not to perform [incremental compilation]. The default if not set is
to use the value from the [profile](profiles.md#incremental). Otherwise this overrides the setting of
all profiles.

The `CARGO_INCREMENTAL` environment variable can be set to `1` to force enable
incremental compilation for all profiles, or `0` to disable it. This env var
overrides the config setting.

#### `build.dep-info-basedir`
* Type: string (path)
* Default: none
* Environment: `CARGO_BUILD_DEP_INFO_BASEDIR`

Strips the given path prefix from [dep
info](../reference/build-cache.md#dep-info-files) file paths. This config setting
is intended to convert absolute paths to relative paths for tools that require
relative paths.

The setting itself is a config-relative path. So, for example, a value of
`"."` would strip all paths starting with the parent directory of the `.cargo`
directory.

#### `build.pipelining`

This option is deprecated and unused. Cargo always has pipelining enabled.

### `[credential-alias]`
* Type: string or array of strings
* Default: empty
* Environment: `CARGO_CREDENTIAL_ALIAS_<name>`

The `[credential-alias]` table defines credential provider aliases.
These aliases can be referenced as an element of the `registry.global-credential-providers`
array, or as a credential provider for a specific registry
under `registries.<NAME>.credential-provider`.

If specified as a string, the value will be split on spaces into path and arguments.

For example, to define an alias called `my-alias`:

```toml
[credential-alias]
my-alias = ["/usr/bin/cargo-credential-example", "--argument", "value", "--flag"]
```
See [Registry Authentication](registry-authentication.md) for more information.

### `[doc]`

The `[doc]` table defines options for the [`cargo doc`] command.

#### `doc.browser`

* Type: string or array of strings ([program path with args])
* Default: `BROWSER` environment variable, or, if that is missing,
  opening the link in a system specific way

This option sets the browser to be used by [`cargo doc`], overriding the
`BROWSER` environment variable when opening documentation with the `--open`
option.

### `[cargo-new]`

The `[cargo-new]` table defines defaults for the [`cargo new`] command.

#### `cargo-new.name`

This option is deprecated and unused.

#### `cargo-new.email`

This option is deprecated and unused.

#### `cargo-new.vcs`
* Type: string
* Default: `"git"` or `"none"`
* Environment: `CARGO_CARGO_NEW_VCS`

Specifies the source control system to use for initializing a new repository.
Valid values are `git`, `hg` (for Mercurial), `pijul`, `fossil` or `none` to
disable this behavior. Defaults to `git`, or `none` if already inside a VCS
repository. Can be overridden with the `--vcs` CLI option.

### `[env]`

The `[env]` section allows you to set additional environment variables for
build scripts, rustc invocations, `cargo run` and `cargo build`.

```toml
[env]
OPENSSL_DIR = "/opt/openssl"
```

By default, the variables specified will not override values that already exist
in the environment. This behavior can be changed by setting the `force` flag.

Setting the `relative` flag evaluates the value as a config-relative path that
is relative to the parent directory of the `.cargo` directory that contains the
`config.toml` file. The value of the environment variable will be the full
absolute path.

```toml
[env]
TMPDIR = { value = "/home/tmp", force = true }
OPENSSL_DIR = { value = "vendor/openssl", relative = true }
```

### `[future-incompat-report]`

The `[future-incompat-report]` table controls setting for [future incompat reporting](future-incompat-report.md)

#### `future-incompat-report.frequency`
* Type: string
* Default: `"always"`
* Environment: `CARGO_FUTURE_INCOMPAT_REPORT_FREQUENCY`

Controls how often we display a notification to the terminal when a future incompat report is available. Possible values:

* `always` (default): Always display a notification when a command (e.g. `cargo build`) produces a future incompat report
* `never`: Never display a notification

### `[cache]`

The `[cache]` table defines settings for cargo's caches.

#### Global caches

When running `cargo` commands, Cargo will automatically track which files you are using within the global cache.
Periodically, Cargo will delete files that have not been used for some period of time.
It will delete files that have to be downloaded from the network if they have not been used in 3 months. Files that can be generated without network access will be deleted if they have not been used in 1 month.

The automatic deletion of files only occurs when running commands that are already doing a significant amount of work, such as all of the build commands (`cargo build`, `cargo test`, `cargo check`, etc.), and `cargo fetch`.

Automatic deletion is disabled if cargo is offline such as with `--offline` or `--frozen` to avoid deleting artifacts that may need to be used if you are offline for a long period of time.

> **Note**: This tracking is currently only implemented for the global cache in Cargo's home directory.
> This includes registry indexes and source files downloaded from registries and git dependencies.
> Support for tracking build artifacts is not yet implemented, and tracked in [cargo#13136](https://github.com/rust-lang/cargo/issues/13136).
>
> Additionally, there is an unstable feature to support *manually* triggering cache cleaning, and to further customize the configuration options.
> See the [Unstable chapter](unstable.md#gc) for more information.

#### `cache.auto-clean-frequency`
* Type: string
* Default: `"1 day"`
* Environment: `CARGO_CACHE_AUTO_CLEAN_FREQUENCY`

This option defines how often Cargo will automatically delete unused files in the global cache.
This does *not* define how old the files must be, those thresholds are described [above](#global-caches).

It supports the following settings:

* `"never"` --- Never deletes old files.
* `"always"` --- Checks to delete old files every time Cargo runs.
* An integer followed by "seconds", "minutes", "hours", "days", "weeks", or "months" --- Checks to delete old files at most the given time frame.

### `[http]`

The `[http]` table defines settings for HTTP behavior. This includes fetching
crate dependencies and accessing remote git repositories.

#### `http.debug`
* Type: boolean
* Default: false
* Environment: `CARGO_HTTP_DEBUG`

If `true`, enables debugging of HTTP requests. The debug information can be
seen by setting the `CARGO_LOG=network=debug` environment
variable (or use `network=trace` for even more information).

Be wary when posting logs from this output in a public location. The output
may include headers with authentication tokens which you don't want to leak!
Be sure to review logs before posting them.

#### `http.proxy`
* Type: string
* Default: none
* Environment: `CARGO_HTTP_PROXY` or `HTTPS_PROXY` or `https_proxy` or `http_proxy`

Sets an HTTP and HTTPS proxy to use. The format is in [libcurl format] as in
`[protocol://]host[:port]`. If not set, Cargo will also check the `http.proxy`
setting in your global git configuration. If none of those are set, the
`HTTPS_PROXY` or `https_proxy` environment variables set the proxy for HTTPS
requests, and `http_proxy` sets it for HTTP requests.

#### `http.timeout`
* Type: integer
* Default: 30
* Environment: `CARGO_HTTP_TIMEOUT` or `HTTP_TIMEOUT`

Sets the timeout for each HTTP request, in seconds.

#### `http.cainfo`
* Type: string (path)
* Default: none
* Environment: `CARGO_HTTP_CAINFO`

Path to a Certificate Authority (CA) bundle file, used to verify TLS
certificates. If not specified, Cargo attempts to use the system certificates.

#### `http.proxy-cainfo`
* Type: string (path)
* Default: falls back to `http.cainfo` if not set
* Environment: `CARGO_HTTP_PROXY_CAINFO`

Path to a Certificate Authority (CA) bundle file, used to verify proxy TLS
certificates.

#### `http.check-revoke`
* Type: boolean
* Default: true (Windows) false (all others)
* Environment: `CARGO_HTTP_CHECK_REVOKE`

This determines whether or not TLS certificate revocation checks should be
performed. This only works on Windows.

#### `http.ssl-version`
* Type: string or min/max table
* Default: none
* Environment: `CARGO_HTTP_SSL_VERSION`

This sets the minimum TLS version to use. It takes a string, with one of the
possible values of `"default"`, `"tlsv1"`, `"tlsv1.0"`, `"tlsv1.1"`, `"tlsv1.2"`, or
`"tlsv1.3"`.

This may alternatively take a table with two keys, `min` and `max`, which each
take a string value of the same kind that specifies the minimum and maximum
range of TLS versions to use.

The default is a minimum version of `"tlsv1.0"` and a max of the newest version
supported on your platform, typically `"tlsv1.3"`.

#### `http.low-speed-limit`
* Type: integer
* Default: 10
* Environment: `CARGO_HTTP_LOW_SPEED_LIMIT`

This setting controls timeout behavior for slow connections. If the average
transfer speed in bytes per second is below the given value for
[`http.timeout`](#httptimeout) seconds (default 30 seconds), then the
connection is considered too slow and Cargo will abort and retry.

#### `http.multiplexing`
* Type: boolean
* Default: true
* Environment: `CARGO_HTTP_MULTIPLEXING`

When `true`, Cargo will attempt to use the HTTP2 protocol with multiplexing.
This allows multiple requests to use the same connection, usually improving
performance when fetching multiple files. If `false`, Cargo will use HTTP 1.1
without pipelining.

#### `http.user-agent`
* Type: string
* Default: Cargo's version
* Environment: `CARGO_HTTP_USER_AGENT`

Specifies a custom user-agent header to use. The default if not specified is a
string that includes Cargo's version.

### `[install]`

The `[install]` table defines defaults for the [`cargo install`] command.

#### `install.root`
* Type: string (path)
* Default: Cargo's home directory
* Environment: `CARGO_INSTALL_ROOT`

Sets the path to the root directory for installing executables for [`cargo
install`]. Executables go into a `bin` directory underneath the root.

To track information of installed executables, some extra files, such as
`.crates.toml` and `.crates2.json`, are also created under this root.

The default if not specified is Cargo's home directory (default `.cargo` in
your home directory).

Can be overridden with the `--root` command-line option.

### `[net]`

The `[net]` table controls networking configuration.

#### `net.retry`
* Type: integer
* Default: 3
* Environment: `CARGO_NET_RETRY`

Number of times to retry possibly spurious network errors.

#### `net.git-fetch-with-cli`
* Type: boolean
* Default: false
* Environment: `CARGO_NET_GIT_FETCH_WITH_CLI`

If this is `true`, then Cargo will use the `git` executable to fetch registry
indexes and git dependencies. If `false`, then it uses a built-in `git`
library.

Setting this to `true` can be helpful if you have special authentication
requirements that Cargo does not support. See [Git
Authentication](../appendix/git-authentication.md) for more information about
setting up git authentication.

#### `net.offline`
* Type: boolean
* Default: false
* Environment: `CARGO_NET_OFFLINE`

If this is `true`, then Cargo will avoid accessing the network, and attempt to
proceed with locally cached data. If `false`, Cargo will access the network as
needed, and generate an error if it encounters a network error.

Can be overridden with the `--offline` command-line option.

#### `net.ssh`

The `[net.ssh]` table contains settings for SSH connections.

#### `net.ssh.known-hosts`
* Type: array of strings
* Default: see description
* Environment: not supported

The `known-hosts` array contains a list of SSH host keys that should be
accepted as valid when connecting to an SSH server (such as for SSH git
dependencies). Each entry should be a string in a format similar to OpenSSH
`known_hosts` files. Each string should start with one or more hostnames
separated by commas, a space, the key type name, a space, and the
base64-encoded key. For example:

```toml
[net.ssh]
known-hosts = [
    "example.com ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIFO4Q5T0UV0SQevair9PFwoxY9dl4pQl3u5phoqJH3cF"
]
```

Cargo will attempt to load known hosts keys from common locations supported in
OpenSSH, and will join those with any listed in a Cargo configuration file.
If any matching entry has the correct key, the connection will be allowed.

Cargo comes with the host keys for [github.com][github-keys] built-in. If
those ever change, you can add the new keys to the config or known_hosts file.

See [Git Authentication](../appendix/git-authentication.md#ssh-known-hosts)
for more details.

[github-keys]: https://docs.github.com/en/authentication/keeping-your-account-and-data-secure/githubs-ssh-key-fingerprints

### `[patch]`

Just as you can override dependencies using [`[patch]` in
`Cargo.toml`](overriding-dependencies.md#the-patch-section), you can
override them in the cargo configuration file to apply those patches to
any affected build. The format is identical to the one used in
`Cargo.toml`.

Since `.cargo/config.toml` files are not usually checked into source
control, you should prefer patching using `Cargo.toml` where possible to
ensure that other developers can compile your crate in their own
environments. Patching through cargo configuration files is generally
only appropriate when the patch section is automatically generated by an
external build tool.

If a given dependency is patched both in a cargo configuration file and
a `Cargo.toml` file, the patch in the configuration file is used. If
multiple configuration files patch the same dependency, standard cargo
configuration merging is used, which prefers the value defined closest
to the current directory, with `$HOME/.cargo/config.toml` taking the
lowest precedence.

Relative `path` dependencies in such a `[patch]` section are resolved
relative to the configuration file they appear in.

### `[profile]`

The `[profile]` table can be used to globally change profile settings, and
override settings specified in `Cargo.toml`. It has the same syntax and
options as profiles specified in `Cargo.toml`. See the [Profiles chapter] for
details about the options.

[Profiles chapter]: profiles.md

#### `[profile.<name>.build-override]`
* Environment: `CARGO_PROFILE_<name>_BUILD_OVERRIDE_<key>`

The build-override table overrides settings for build scripts, proc macros,
and their dependencies. It has the same keys as a normal profile. See the
[overrides section](profiles.md#overrides) for more details.

#### `[profile.<name>.package.<name>]`
* Environment: not supported

The package table overrides settings for specific packages. It has the same
keys as a normal profile, minus the `panic`, `lto`, and `rpath` settings. See
the [overrides section](profiles.md#overrides) for more details.

#### `profile.<name>.codegen-units`
* Type: integer
* Default: See profile docs.
* Environment: `CARGO_PROFILE_<name>_CODEGEN_UNITS`

See [codegen-units](profiles.md#codegen-units).

#### `profile.<name>.debug`
* Type: integer or boolean
* Default: See profile docs.
* Environment: `CARGO_PROFILE_<name>_DEBUG`

See [debug](profiles.md#debug).

#### `profile.<name>.split-debuginfo`
* Type: string
* Default: See profile docs.
* Environment: `CARGO_PROFILE_<name>_SPLIT_DEBUGINFO`

See [split-debuginfo](profiles.md#split-debuginfo).

#### `profile.<name>.debug-assertions`
* Type: boolean
* Default: See profile docs.
* Environment: `CARGO_PROFILE_<name>_DEBUG_ASSERTIONS`

See [debug-assertions](profiles.md#debug-assertions).

#### `profile.<name>.incremental`
* Type: boolean
* Default: See profile docs.
* Environment: `CARGO_PROFILE_<name>_INCREMENTAL`

See [incremental](profiles.md#incremental).

#### `profile.<name>.lto`
* Type: string or boolean
* Default: See profile docs.
* Environment: `CARGO_PROFILE_<name>_LTO`

See [lto](profiles.md#lto).

#### `profile.<name>.overflow-checks`
* Type: boolean
* Default: See profile docs.
* Environment: `CARGO_PROFILE_<name>_OVERFLOW_CHECKS`

See [overflow-checks](profiles.md#overflow-checks).

#### `profile.<name>.opt-level`
* Type: integer or string
* Default: See profile docs.
* Environment: `CARGO_PROFILE_<name>_OPT_LEVEL`

See [opt-level](profiles.md#opt-level).

#### `profile.<name>.panic`
* Type: string
* Default: See profile docs.
* Environment: `CARGO_PROFILE_<name>_PANIC`

See [panic](profiles.md#panic).

#### `profile.<name>.rpath`
* Type: boolean
* Default: See profile docs.
* Environment: `CARGO_PROFILE_<name>_RPATH`

See [rpath](profiles.md#rpath).

#### `profile.<name>.strip`
* Type: string or boolean
* Default: See profile docs.
* Environment: `CARGO_PROFILE_<name>_STRIP`

See [strip](profiles.md#strip).

### `[resolver]`

The `[resolver]` table overrides [dependency resolution behavior](resolver.md) for local development (e.g. excludes `cargo install`).

#### `resolver.lockfile-path`
* Type: string (path)
* Default: `<workspace_root>/Cargo.lock`
* Environment: `CARGO_RESOLVER_LOCKFILE_PATH`

Specifies the path to the lockfile to use when resolving dependencies.
This option is useful when working with read-only source directories.

The path must end with `Cargo.lock`.

> **MSRV:** Requires 1.97+

#### `resolver.incompatible-rust-versions`
* Type: string
* Default: See [`resolver`](resolver.md#resolver-versions) docs
* Environment: `CARGO_RESOLVER_INCOMPATIBLE_RUST_VERSIONS`

When resolving which version of a dependency to use, select how versions with incompatible `package.rust-version`s are treated.
Values include:
- `allow`: treat `rust-version`-incompatible versions like any other version
- `fallback`: only consider `rust-version`-incompatible versions if no other version matched

Can be overridden with
- `--ignore-rust-version` CLI option
- Setting the dependency's version requirement higher than any version with a compatible `rust-version`
- Specifying the version to `cargo update` with `--precise`

See the [resolver](resolver.md#rust-version) chapter for more details.

> **MSRV:**
> - `allow` is supported on any version
> - `fallback` is respected as of 1.84

### `[registries]`

The `[registries]` table is used for specifying additional [registries]. It
consists of a sub-table for each named registry.

#### `registries.<name>.index`
* Type: string (url)
* Default: none
* Environment: `CARGO_REGISTRIES_<name>_INDEX`

Specifies the URL of the index for the registry.

#### `registries.<name>.token`
* Type: string
* Default: none
* Environment: `CARGO_REGISTRIES_<name>_TOKEN`

Specifies the authentication token for the given registry. This value should
only appear in the [credentials](#credentials) file. This is used for registry
commands like [`cargo publish`] that require authentication.

Can be overridden with the `--token` command-line option.

#### `registries.<name>.credential-provider`
* Type: string or array of path and arguments
* Default: none
* Environment: `CARGO_REGISTRIES_<name>_CREDENTIAL_PROVIDER`

Specifies the credential provider for the given registry. If not set, the
providers in [`registry.global-credential-providers`](#registryglobal-credential-providers)
will be used.

If specified as a string, path and arguments will be split on spaces. For
paths or arguments that contain spaces, use an array.

If the value exists in the [`[credential-alias]`](#credential-alias) table, the alias will be used.

See [Registry Authentication](registry-authentication.md) for more information.

#### `registries.crates-io.protocol`
* Type: string
* Default: `"sparse"`
* Environment: `CARGO_REGISTRIES_CRATES_IO_PROTOCOL`

Specifies the protocol used to access crates.io. Allowed values are `git` or `sparse`.

`git` causes Cargo to clone the entire index of all packages ever published to [crates.io] from <https://github.com/rust-lang/crates.io-index/>.
This can have performance implications due to the size of the index.
`sparse` is a newer protocol which uses HTTPS to download only what is necessary from <https://index.crates.io/>.
This can result in a significant performance improvement for resolving new dependencies in most situations.

More information about registry protocols may be found in the [Registries chapter](registries.md).

### `[registry]`

The `[registry]` table controls the default registry used when one is not
specified.

#### `registry.index`

This value is no longer accepted and should not be used.

#### `registry.default`
* Type: string
* Default: `"crates-io"`
* Environment: `CARGO_REGISTRY_DEFAULT`

The name of the registry (from the [`registries` table](#registries)) to use
by default for registry commands like [`cargo publish`].

Can be overridden with the `--registry` command-line option.

#### `registry.credential-provider`
* Type: string or array of path and arguments
* Default: none
* Environment: `CARGO_REGISTRY_CREDENTIAL_PROVIDER`

Specifies the credential provider for [crates.io]. If not set, the
providers in [`registry.global-credential-providers`](#registryglobal-credential-providers)
will be used.

If specified as a string, path and arguments will be split on spaces. For
paths or arguments that contain spaces, use an array.

If the value exists in the `[credential-alias]` table, the alias will be used.

See [Registry Authentication](registry-authentication.md) for more information.

#### `registry.token`
* Type: string
* Default: none
* Environment: `CARGO_REGISTRY_TOKEN`

Specifies the authentication token for [crates.io]. This value should only
appear in the [credentials](#credentials) file. This is used for registry
commands like [`cargo publish`] that require authentication.

Can be overridden with the `--token` command-line option.

#### `registry.global-credential-providers`
* Type: array
* Default: `["cargo:token"]`
* Environment: `CARGO_REGISTRY_GLOBAL_CREDENTIAL_PROVIDERS`

Specifies the list of global credential providers. If credential provider is not set
for a specific registry using `registries.<name>.credential-provider`, Cargo will use
the credential providers in this list. Providers toward the end of the list have precedence.

Path and arguments are split on spaces. If the path or arguments contains spaces, the credential
provider should be defined in the [`[credential-alias]`](#credential-alias) table and
referenced here by its alias.

See [Registry Authentication](registry-authentication.md) for more information.

### `[source]`

The `[source]` table defines the registry sources available. See [Source
Replacement] for more information. It consists of a sub-table for each named
source. A source should only define one kind (directory, registry,
local-registry, or git).

#### `source.<name>.replace-with`
* Type: string
* Default: none
* Environment: not supported

If set, replace this source with the given named source or named registry.

#### `source.<name>.directory`
* Type: string (path)
* Default: none
* Environment: not supported

Sets the path to a directory to use as a directory source.

#### `source.<name>.registry`
* Type: string (url)
* Default: none
* Environment: not supported

Sets the URL to use for a registry source.

#### `source.<name>.local-registry`
* Type: string (path)
* Default: none
* Environment: not supported

Sets the path to a directory to use as a local registry source.

#### `source.<name>.git`
* Type: string (url)
* Default: none
* Environment: not supported

Sets the URL to use for a git repository source.

#### `source.<name>.branch`
* Type: string
* Default: none
* Environment: not supported

Sets the branch name to use for a git repository.

If none of `branch`, `tag`, or `rev` is set, defaults to the `master` branch.

#### `source.<name>.tag`
* Type: string
* Default: none
* Environment: not supported

Sets the tag name to use for a git repository.

If none of `branch`, `tag`, or `rev` is set, defaults to the `master` branch.

#### `source.<name>.rev`
* Type: string
* Default: none
* Environment: not supported

Sets the [revision] to use for a git repository.

If none of `branch`, `tag`, or `rev` is set, defaults to the `master` branch.


### `[target]`

The `[target]` table is used for specifying settings for specific platform
targets. It consists of a sub-table which is either a [platform triple][target triple] 
or a [`cfg()` expression]. The given values will be used if the target platform
matches either the `<triple>` value or the `<cfg>` expression.

```toml
[target.thumbv7m-none-eabi]
linker = "arm-none-eabi-gcc"
runner = "my-emulator"
rustflags = ["…", "…"]

[target.'cfg(all(target_arch = "arm", target_os = "none"))']
runner = "my-arm-wrapper"
rustflags = ["…", "…"]
```

`cfg` values come from those built-in to the compiler (run `rustc --print=cfg`
to view) and extra `--cfg` flags passed to `rustc` (such as those defined in
`RUSTFLAGS`). Do not try to match on `debug_assertions`, `test`, Cargo features
like `feature="foo"`, or values set by [build scripts].

If using a target spec JSON file, the [`<triple>`] value is the filename stem.
For example `--target foo/bar.json` would match `[target.bar]`.

#### `target.<triple>.ar`

This option is deprecated and unused.

#### `target.<triple>.linker`
* Type: string (program path)
* Default: none
* Environment: `CARGO_TARGET_<triple>_LINKER`

Specifies the linker which is passed to `rustc` (via [`-C linker`]) when the
[`<triple>`] is being compiled for. By default, the linker is not overridden.

#### `target.<cfg>.linker`
This is similar to the [target linker](#targettriplelinker), but using
a [`cfg()` expression]. If both a [`<triple>`] and `<cfg>` linker match,
the `<triple>` will take precedence. It is an error if more than one
`<cfg>` linker matches the current target.

#### `target.<triple>.runner`
* Type: string or array of strings ([program path with args])
* Default: none
* Environment: `CARGO_TARGET_<triple>_RUNNER`

If a runner is provided, executables for the target [`<triple>`] will be
executed by invoking the specified runner with the actual executable passed as
an argument. This applies to [`cargo run`], [`cargo test`] and [`cargo bench`]
commands. By default, compiled executables are executed directly.

#### `target.<cfg>.runner`

This is similar to the [target runner](#targettriplerunner), but using
a [`cfg()` expression]. If both a [`<triple>`] and `<cfg>` runner match,
the `<triple>` will take precedence. It is an error if more than one
`<cfg>` runner matches the current target.

#### `target.<triple>.rustflags`
* Type: string or array of strings
* Default: none
* Environment: `CARGO_TARGET_<triple>_RUSTFLAGS`

Passes a set of custom flags to the compiler for this [`<triple>`]. 
The value may be an array of strings or a space-separated string.

See [`build.rustflags`](#buildrustflags) for more details on the different
ways to specific extra flags.

#### `target.<cfg>.rustflags`

This is similar to the [target rustflags](#targettriplerustflags), but
using a [`cfg()` expression]. If several `<cfg>` and [`<triple>`] entries
match the current target, the flags are joined together.

#### `target.<triple>.rustdocflags`
* Type: string or array of strings
* Default: none
* Environment: `CARGO_TARGET_<triple>_RUSTDOCFLAGS`

Passes a set of custom flags to the compiler for this [`<triple>`].
The value may be an array of strings or a space-separated string.

See [`build.rustdocflags`](#buildrustdocflags) for more details on the different
ways to specific extra flags.

#### `target.<cfg>.rustdocflags`

This is similar to the [target rustdocflags](#targettriplerustdocflags), but
using a [`cfg()` expression]. If several `<cfg>` and [`<triple>`] entries
match the current target, the flags are joined together.

#### `target.<triple>.<links>`

The links sub-table provides a way to [override a build script]. When
specified, the build script for the given `links` library will not be
run, and the given values will be used instead.

```toml
[target.x86_64-unknown-linux-gnu.foo]
rustc-link-lib = ["foo"]
rustc-link-search = ["/path/to/foo"]
rustc-flags = "-L /some/path"
rustc-cfg = ['key="value"']
rustc-env = {key = "value"}
rustc-cdylib-link-arg = ["…"]
metadata_key1 = "value"
metadata_key2 = "value"
```

### `[term]`

The `[term]` table controls terminal output and interaction.

#### `term.quiet`
* Type: boolean
* Default: false
* Environment: `CARGO_TERM_QUIET`

Controls whether or not log messages are displayed by Cargo.

Specifying the `--quiet` flag will override and force quiet output.
Specifying the `--verbose` flag will override and disable quiet output.

#### `term.verbose`
* Type: boolean
* Default: false
* Environment: `CARGO_TERM_VERBOSE`

Controls whether or not extra detailed messages are displayed by Cargo.

Specifying the `--quiet` flag will override and disable verbose output.
Specifying the `--verbose` flag will override and force verbose output.

#### `term.color`
* Type: string
* Default: `"auto"`
* Environment: `CARGO_TERM_COLOR`

Controls whether or not colored output is used in the terminal. Possible values:

* `auto` (default): Automatically detect if color support is available on the
  terminal.
* `always`: Always display colors.
* `never`: Never display colors.

Can be overridden with the `--color` command-line option.

#### `term.hyperlinks`
* Type: bool
* Default: auto-detect
* Environment: `CARGO_TERM_HYPERLINKS`

Controls whether or not hyperlinks are used in the terminal.

#### `term.unicode`
* Type: bool
* Default: auto-detect
* Environment: `CARGO_TERM_UNICODE`

Control whether output can be rendered using non-ASCII unicode characters.

#### `term.progress.when`
* Type: string
* Default: `"auto"`
* Environment: `CARGO_TERM_PROGRESS_WHEN`

Controls whether or not progress bar is shown in the terminal. Possible values:

* `auto` (default): Intelligently guess whether to show progress bar.
* `always`: Always show progress bar.
* `never`: Never show progress bar.

#### `term.progress.width`
* Type: integer
* Default: none
* Environment: `CARGO_TERM_PROGRESS_WIDTH`

Sets the width for progress bar.

#### `term.progress.term-integration`
* Type: bool
* Default: auto-detect
* Environment: `CARGO_TERM_PROGRESS_TERM_INTEGRATION`

Report progress to the terminal emulator for display in places like the task bar.

[`cargo bench`]: ../commands/cargo-bench.md
[`cargo login`]: ../commands/cargo-login.md
[`cargo logout`]: ../commands/cargo-logout.md
[`cargo doc`]: ../commands/cargo-doc.md
[`cargo new`]: ../commands/cargo-new.md
[`cargo publish`]: ../commands/cargo-publish.md
[`cargo run`]: ../commands/cargo-run.md
[`cargo rustc`]: ../commands/cargo-rustc.md
[`cargo test`]: ../commands/cargo-test.md
[`cargo rustdoc`]: ../commands/cargo-rustdoc.md
[`cargo install`]: ../commands/cargo-install.md
[env]: environment-variables.md
[`cfg()` expression]: ../../reference/conditional-compilation.html
[build scripts]: build-scripts.md
[`-C linker`]: ../../rustc/codegen-options/index.md#linker
[override a build script]: build-scripts.md#overriding-build-scripts
[toml]: https://toml.io/
[incremental compilation]: profiles.md#incremental
[program path with args]: #executable-paths-with-arguments
[libcurl format]: https://everything.curl.dev/transfers/conn/proxies#proxy-types
[source replacement]: source-replacement.md
[revision]: https://git-scm.com/docs/gitrevisions
[registries]: registries.md
[`cargo:token`]: registry-authentication.md#cargotoken
[crates.io]: https://crates.io/
[target triple]: ../appendix/glossary.md#target '"target" (glossary)'
[`<triple>`]: ../appendix/glossary.md#target '"target" (glossary)'
