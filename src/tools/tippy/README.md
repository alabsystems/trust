# Tippy

[![License: MIT OR Apache-2.0](https://img.shields.io/crates/l/clippy.svg)](#license)

Tippy is Trust's lint checker. It carries the Rust Clippy lint suite in-tree so
the Trust toolchain owns and builds its linter instead of installing a separate
upstream component.

The public commands are `tippy`, `targo tippy`, and `tippy-driver`. The
inherited `cargo-clippy` and `clippy-driver` names remain internal Cargo build
selectors only; a completed Trust sysroot does not install them. Tippy retains
the `clippy::` lint namespace so existing Rust source attributes and lint flags
remain compatible.

[There are over 800 lints included in this crate!](https://rust-lang.github.io/rust-clippy/master/index.html)

Lints are divided into categories, each with a default [lint level](https://doc.rust-lang.org/rustc/lints/levels.html).
You can choose how much Tippy is supposed to help by changing the lint level by category.

| Category              | Description                                                                         | Default level |
|-----------------------|-------------------------------------------------------------------------------------|---------------|
| `clippy::all`         | all lints that are on by default (correctness, suspicious, style, complexity, perf) | **warn/deny** |
| `clippy::correctness` | code that is outright wrong or useless                                              | **deny**      |
| `clippy::suspicious`  | code that is most likely wrong or useless                                           | **warn**      |
| `clippy::style`       | code that should be written in a more idiomatic way                                 | **warn**      |
| `clippy::complexity`  | code that does something simple but in a complex way                                | **warn**      |
| `clippy::perf`        | code that can be written to run faster                                              | **warn**      |
| `clippy::pedantic`    | lints which are rather strict or have occasional false positives                    | allow         |
| `clippy::restriction` | lints which prevent the use of language and library features[^restrict]             | allow         |
| `clippy::nursery`     | new lints that are still under development                                          | allow         |
| `clippy::cargo`       | lints for the cargo manifest                                                        | allow         |

Report Trust-specific integration bugs to the Trust issue tracker. The upstream
lint documentation remains useful for the retained `clippy::` namespace.

The `restriction` category should, *emphatically*, not be enabled as a whole. The contained
lints may lint against perfectly reasonable code, may not have an alternative suggestion,
and may contradict any other lints (including other categories). Lints should be considered
on a case-by-case basis before enabling.

[^restrict]: Some use cases for `restriction` lints include:
    - Strict coding styles (e.g. [`clippy::else_if_without_else`]).
    - Additional restrictions on CI (e.g. [`clippy::todo`]).
    - Preventing panicking in certain functions (e.g. [`clippy::unwrap_used`]).
    - Running a lint only on a subset of code (e.g. `#[forbid(clippy::float_arithmetic)]` on a module).

[`clippy::else_if_without_else`]: https://rust-lang.github.io/rust-clippy/master/index.html#else_if_without_else
[`clippy::todo`]: https://rust-lang.github.io/rust-clippy/master/index.html#todo
[`clippy::unwrap_used`]: https://rust-lang.github.io/rust-clippy/master/index.html#unwrap_used

---

Table of contents:

* [Usage instructions](#usage)
* [Configuration](#configuration)
* [Contributing](#contributing)
* [License](#license)

## Usage

Tippy can run directly, through Targo's external-subcommand dispatch, or as a
compiler driver for projects that do not use Targo.

### As a Trust command

Tippy is part of the local `trust` toolchain built from this
checkout. Use the Trust toolchain instead of installing an upstream component.

#### Step 1: Build and Link Trust

```terminal
CARGO_NET_OFFLINE=true ./x.py build --set llvm.ninja=false --stage 2
rustup toolchain link trust ./build/host/stage2
```

#### Step 2: Run Tippy

Run the direct frontend or Targo subcommand:

```terminal
tippy
targo tippy
```

#### Automatically applying Tippy suggestions

Tippy can automatically apply some lint suggestions, just like the compiler. Note that `--fix` implies
`--all-targets`, so it can fix as much code as it can.

```terminal
targo tippy --fix
```

#### Workspaces

All the usual workspace options work with Tippy. For example:

```terminal
targo tippy -p example
```

As with `targo --unverified check`, this includes dependencies that are members of the workspace, like path dependencies.
If you want to run Tippy **only** on the given crate, use the `--no-deps` option like this:

```terminal
targo tippy -p example -- --no-deps
```

### Using `tippy-driver`

Tippy can also be used in projects that do not use Targo. Run `tippy-driver`
with the same arguments you use for `rustc`. For example:

```terminal
tippy-driver --edition 2024 -Cpanic=abort foo.rs
```

Note that `tippy-driver` is designed for running Tippy only and should not be used as a general
replacement for `trustc`. `tippy-driver` may produce artifacts that are not optimized as expected,
for example.

### CI

Put the validated Trust sysroot first on `PATH` and run the same canonical
commands used locally:

```terminal
export PATH="$PWD/build/host/stage2/bin:$PATH"
targo tippy --all-targets --all-features -- -D warnings
targo --unverified test
```

Note that adding `-D warnings` will cause your build to fail if **any** warnings are found in your code.
That includes warnings found by rustc (e.g. `dead_code`, etc.). If you want to avoid this and only cause
an error for Tippy warnings, use `#![deny(clippy::all)]` in your code or `-D clippy::all` on the command
line. (You can swap `clippy::all` with the specific lint category you are targeting.)

## Configuration

### Allowing/denying lints

You can add options to your code to `allow`/`warn`/`deny` Clippy lints:

* the whole set of `Warn` lints using the `clippy` lint group (`#![deny(clippy::all)]`).
  Note that `rustc` has additional [lint groups](https://doc.rust-lang.org/rustc/lints/groups.html).

* all lints using both the `clippy` and `clippy::pedantic` lint groups (`#![deny(clippy::all)]`,
  `#![deny(clippy::pedantic)]`). Note that `clippy::pedantic` contains some very aggressive
  lints prone to false positives.

* only some lints (`#![deny(clippy::single_match, clippy::box_vec)]`, etc.)

* `allow`/`warn`/`deny` can be limited to a single function or module using `#[allow(...)]`, etc.

Note: `allow` means to suppress the lint for your code. With `warn` the lint
will only emit a warning, while with `deny` the lint will emit an error, when
triggering for your code. An error causes Clippy to exit with an error code, so
is useful in scripts like CI/CD.

If you do not want to include your lint levels in your code, you can globally
enable/disable lints by passing extra flags to Clippy during the run:

To allow `lint_name`, run

```terminal
targo tippy -- -A clippy::lint_name
```

And to warn on `lint_name`, run

```terminal
targo tippy -- -W clippy::lint_name
```

This also works with lint groups. For example, you
can run Clippy with warnings for all lints enabled:

```terminal
targo tippy -- -W clippy::pedantic
```

If you care only about a single lint, you can allow all others and then explicitly warn on
the lint(s) you are interested in:

```terminal
targo tippy -- -A clippy::all -W clippy::useless_format -W clippy::...
```

### Configure the behavior of some lints

Some lints can be configured in a TOML file named `clippy.toml` or `.clippy.toml`. It contains a basic `variable =
value` mapping e.g.

```toml
avoid-breaking-exported-api = false
disallowed-names = ["toto", "tata", "titi"]
```

The [table of configurations](https://doc.rust-lang.org/nightly/clippy/lint_configuration.html)
contains all config values, their default, and a list of lints they affect.
Each [configurable lint](https://rust-lang.github.io/rust-clippy/master/index.html#Configuration)
, also contains information about these values.

For configurations that are a list type with default values such as
[disallowed-names](https://rust-lang.github.io/rust-clippy/master/index.html#disallowed_names),
you can use the unique value `".."` to extend the default values instead of replacing them.

```toml
# default of disallowed-names is ["foo", "baz", "quux"]
disallowed-names = ["bar", ".."] # -> ["bar", "foo", "baz", "quux"]
```

> **Note**
>
> `clippy.toml` or `.clippy.toml` cannot be used to allow/deny lints.

To deactivate the “for further information visit *lint-link*” message you can
define the `CLIPPY_DISABLE_DOCS_LINKS` environment variable.

### Specifying the minimum supported Rust version

Projects that intend to support old versions of Rust can disable lints pertaining to newer features by
specifying the minimum supported Rust version (MSRV) in the Clippy configuration file.

```toml
msrv = "1.30.0"
```

Alternatively, the [`rust-version` field](https://doc.rust-lang.org/cargo/reference/manifest.html#the-rust-version-field)
in the `Cargo.toml` can be used.

```toml
# Cargo.toml
rust-version = "1.30"
```

The MSRV can also be specified as an attribute, like below.

```rust,ignore
#![feature(custom_inner_attributes)]
#![clippy::msrv = "1.30.0"]

fn main() {
  ...
}
```

You can also omit the patch version when specifying the MSRV, so `msrv = 1.30`
is equivalent to `msrv = 1.30.0`.

Note: `custom_inner_attributes` is an unstable feature, so it has to be enabled explicitly.

Lints that recognize this configuration option can be found [here](https://rust-lang.github.io/rust-clippy/master/index.html#msrv)

## Contributing

If you want to contribute to Clippy, you can find more information in [CONTRIBUTING.md](https://github.com/rust-lang/rust-clippy/blob/master/CONTRIBUTING.md).

## License

<!-- REUSE-IgnoreStart -->

Copyright (c) The Rust Project Contributors

Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
[https://www.apache.org/licenses/LICENSE-2.0](https://www.apache.org/licenses/LICENSE-2.0)> or the MIT license
<LICENSE-MIT or [https://opensource.org/licenses/MIT](https://opensource.org/licenses/MIT)>, at your
option. Files in the project may not be
copied, modified, or distributed except according to those terms.

<!-- REUSE-IgnoreEnd -->
