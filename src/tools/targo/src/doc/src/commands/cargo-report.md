# cargo-report(1)

## NAME

cargo-report --- Generate and display various kinds of reports

## SYNOPSIS

`cargo report` _type_ [_options_]

## DESCRIPTION

Displays a report of the given _type_: `future-incompat`, or the unstable
`timings`, `sessions`, `rebuilds`, `cache-work`, and `execution` reports.

### Native rebuild classifications (unstable)

`targo -Zbuild-analysis report rebuilds --id RUN --json` prints one
`targo-rebuilds-v1` JSON object. Sessions are produced with `-Zbuild-analysis`
and `build.analysis.enabled = true`. Omit `--id` to select the latest matching
workspace session. Without `--json`, the human report keeps its existing format.
Expanded impact traversal is bounded and excessive expansion is an error before
report output. Use `--json` to inspect the compact dependency graph in that case.

The JSON scope is `observed-fingerprint-classifications`. It records
`registered_units`, `classified_units`, `unclassified_units`, and
`observed_counts` (`cached`, `dirty`, `new`). These are fingerprint observations,
not compiler process counts or proof grades. A `new` classification does not
establish that the cache has never contained that unit.

`stream_completeness` is `complete` only for a validated closed stream, otherwise
`unavailable` for legacy logs. `input_accounting` is `finalized` only when the
input-finalization record was observed, otherwise `unavailable`. Neither a closed
stream nor finalized accounting establishes complete unit classification.

`units` are sorted by their session-local numeric `index`. Each row keeps its
`package_id`, `target` (`name` and `kind`), `mode`, `platform`, sorted `features`,
`requested`, and sorted `dependencies`. The index is not a cross-run cache
identity. A missing classification is `fingerprint: null`; an observed one has
`status` (`new`, `dirty`, or `fresh`), a payload-free `reason` category or `null`,
and `rechecked`. A marked post-lock recheck replaces the classification without
adding a unit to the counts. Reason categories reuse the existing typed producer
projection; paths, flags, environment names and values, and other diagnostic
payloads are not exported. `rustc-changed` reports that classification, without
claiming that a physical compiler file changed.

`non_cached_dependency_frontier_roots` contains sorted indices from the existing
rebuild topology, including both new and dirty units without a non-cached
dependency. Exact edges remain in each unit's `dependencies`. JSON does not
compute or export transitive impact lists. These relations do not establish
causal CPU costs, actual compiler execution, cache validity, or proof authority.
Malformed or incomplete current log protocols remain errors before JSON output.

## OPTIONS

### Display Options

<dl>
<dt class="option-term" id="option-cargo-report--v"><a class="option-anchor" href="#option-cargo-report--v"><code>-v</code></a></dt>
<dt class="option-term" id="option-cargo-report---verbose"><a class="option-anchor" href="#option-cargo-report---verbose"><code>--verbose</code></a></dt>
<dd class="option-desc"><p>Use verbose output. May be specified twice for “very verbose” output which
includes extra output such as dependency warnings and build script output.
May also be specified with the <code>term.verbose</code>
<a href="../reference/config.html">config value</a>.</p>
</dd>


<dt class="option-term" id="option-cargo-report--q"><a class="option-anchor" href="#option-cargo-report--q"><code>-q</code></a></dt>
<dt class="option-term" id="option-cargo-report---quiet"><a class="option-anchor" href="#option-cargo-report---quiet"><code>--quiet</code></a></dt>
<dd class="option-desc"><p>Do not print cargo log messages.
May also be specified with the <code>term.quiet</code>
<a href="../reference/config.html">config value</a>.</p>
</dd>


<dt class="option-term" id="option-cargo-report---color"><a class="option-anchor" href="#option-cargo-report---color"><code>--color</code> <em>when</em></a></dt>
<dd class="option-desc"><p>Control when colored output is used. Valid values:</p>
<ul>
<li><code>auto</code> (default): Automatically detect if color support is available on the
terminal.</li>
<li><code>always</code>: Always display colors.</li>
<li><code>never</code>: Never display colors.</li>
</ul>
<p>May also be specified with the <code>term.color</code>
<a href="../reference/config.html">config value</a>.</p>
</dd>

</dl>

### Manifest Options

<dl>
<dt class="option-term" id="option-cargo-report---locked"><a class="option-anchor" href="#option-cargo-report---locked"><code>--locked</code></a></dt>
<dd class="option-desc"><p>Asserts that the exact same dependencies and versions are used as when the
existing <code>Cargo.lock</code> file was originally generated. Cargo will exit with an
error when either of the following scenarios arises:</p>
<ul>
<li>The lock file is missing.</li>
<li>Cargo attempted to change the lock file due to a different dependency resolution.</li>
</ul>
<p>It may be used in environments where deterministic builds are desired,
such as in CI pipelines.</p>
</dd>


<dt class="option-term" id="option-cargo-report---offline"><a class="option-anchor" href="#option-cargo-report---offline"><code>--offline</code></a></dt>
<dd class="option-desc"><p>Prevents Cargo from accessing the network for any reason. Without this
flag, Cargo will stop with an error if it needs to access the network and
the network is not available. With this flag, Cargo will attempt to
proceed without the network if possible.</p>
<p>Beware that this may result in different dependency resolution than online
mode. Cargo will restrict itself to crates that are downloaded locally, even
if there might be a newer version as indicated in the local copy of the index.
See the <a href="cargo-fetch.html">cargo-fetch(1)</a> command to download dependencies before going
offline.</p>
<p>May also be specified with the <code>net.offline</code> <a href="../reference/config.html">config value</a>.</p>
</dd>


<dt class="option-term" id="option-cargo-report---frozen"><a class="option-anchor" href="#option-cargo-report---frozen"><code>--frozen</code></a></dt>
<dd class="option-desc"><p>Equivalent to specifying both <code>--locked</code> and <code>--offline</code>.</p>
</dd>

</dl>

### Common Options

<dl>

<dt class="option-term" id="option-cargo-report-+toolchain"><a class="option-anchor" href="#option-cargo-report-+toolchain"><code>+</code><em>toolchain</em></a></dt>
<dd class="option-desc"><p>If Cargo has been installed with rustup, and the first argument to <code>cargo</code>
begins with <code>+</code>, it will be interpreted as a rustup toolchain name (such
as <code>+stable</code> or <code>+nightly</code>).
See the <a href="https://rust-lang.github.io/rustup/overrides.html">rustup documentation</a>
for more information about how toolchain overrides work.</p>
</dd>


<dt class="option-term" id="option-cargo-report---config"><a class="option-anchor" href="#option-cargo-report---config"><code>--config</code> <em>KEY=VALUE</em> or <em>PATH</em></a></dt>
<dd class="option-desc"><p>Overrides a Cargo configuration value. The argument should be in TOML syntax of <code>KEY=VALUE</code>,
or provided as a path to an extra configuration file. This flag may be specified multiple times.
See the <a href="../reference/config.html#command-line-overrides">command-line overrides section</a> for more information.</p>
</dd>


<dt class="option-term" id="option-cargo-report--C"><a class="option-anchor" href="#option-cargo-report--C"><code>-C</code> <em>PATH</em></a></dt>
<dd class="option-desc"><p>Changes the current working directory before executing any specified operations. This affects
things like where cargo looks by default for the project manifest (<code>Cargo.toml</code>), as well as
the directories searched for discovering <code>.cargo/config.toml</code>, for example. This option must
appear before the command name, for example <code>cargo -C path/to/my-project build</code>.</p>
<p>This option is only available on the <a href="https://doc.rust-lang.org/book/appendix-07-nightly-rust.html">nightly
channel</a> and
requires the <code>-Z unstable-options</code> flag to enable (see
<a href="https://github.com/rust-lang/cargo/issues/10098">#10098</a>).</p>
</dd>


<dt class="option-term" id="option-cargo-report--h"><a class="option-anchor" href="#option-cargo-report--h"><code>-h</code></a></dt>
<dt class="option-term" id="option-cargo-report---help"><a class="option-anchor" href="#option-cargo-report---help"><code>--help</code></a></dt>
<dd class="option-desc"><p>Prints help information.</p>
</dd>


<dt class="option-term" id="option-cargo-report--Z"><a class="option-anchor" href="#option-cargo-report--Z"><code>-Z</code> <em>flag</em></a></dt>
<dd class="option-desc"><p>Unstable (nightly-only) flags to Cargo. Run <code>cargo -Z help</code> for details.</p>
</dd>


</dl>

## ENVIRONMENT

See [the reference](../reference/environment-variables.html) for
details on environment variables that Cargo reads.

## EXIT STATUS

* `0`: Cargo succeeded.
* `101`: Cargo failed to complete.

## EXAMPLES

1. Display the available kinds of reports:

       cargo report --help

## SEE ALSO

[cargo(1)](cargo.html), [cargo-report-future-incompatibilities(1)](cargo-report-future-incompatibilities.html)
