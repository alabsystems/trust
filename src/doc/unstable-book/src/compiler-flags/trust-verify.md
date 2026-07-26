# Trust verification policy

The tracking issue for this feature is internal to Trust.

------------------------

Trust's native typed verification is batteries-on. `trustc` and its same-sysroot
`rustc` alias run the native typed verifier without an activation flag. Raw,
unscoped invocations are strict; Targo supplies each Cargo unit's reserved
role/package/session metadata envelope so only the intended scope is enforced.
Non-`unscoped` roles are rejected unless both package and session are present.
Dependencies are boundary-only unless explicitly included, and build scripts
are outside proof scope.

The architecture is source-first: the Rust THIR frontend and the Lean/Clean
frontend lower directly to canonical typed TrustIR. Authenticated MIR-derived
evidence temporarily preserves compatibility and differential coverage while
the direct Rust producer is brought to exact obligation, semantic, and
proof-replay parity. MIR is neither the canonical semantics nor the end-state
frontend, and structural lowering success alone never earns proof credit.

The role and package options are Targo protocol fields, not user-facing scope
switches. A direct invocation stays `unscoped` and strict. It may set only
`-Z trust-verify-session=<nonce>` to force fresh proof execution; attaching a
package without a session, or a non-`unscoped` role without the full tuple, is
rejected.

For normal verifier use, start with the public `targo trust` front door:

```text
targo trust check
targo trust check --format json
```

`rustc ...` is the lower-level compiler transport used by `targo-trust` and by
compiler-facing tests. It is useful for compiler work and transport debugging,
not as the primary user-facing verifier command.

```text
trustc your_file.rs
trustc -Z trust-verify-output=json your_file.rs
```

Strict means every in-scope outcome must be
statically proved: failed, unknown, timed-out, runtime-checked, unsupported, and
skipped outcomes all fail the compilation. `#[trust::skip]` is therefore rejected
in this lane; under the nonfatal advisory policy it is emitted as an
`assumption:user-opt-out` structured row instead of disappearing. The public
`targo trust` verifier front doors use strict primary-crate verification by
default; `--allow-l0-gaps` is their explicit nonfatal development lane.

Structured transport output is selected with
`-Z trust-verify-output=json` or `both`.

Availability of this native/stage1 path is still tracked work in Trust's
current from-source flow, so direct compiler use should not be treated as a universally
shipped guarantee across all builds or environments.

Use `-Z trust-verify-level` to control how deep verification should go.
The default is level `2` (domain/maximal). The tracked per-obligation timeout
defaults to 5000 ms; the cooperative per-function budget defaults to 120000 ms.
`-Z trust-verify=on|off` is the sole verification activation control. `on` is
the default and needs no spelling; `off` is what bootstrap and explicit
vanilla-compatibility lanes use internally. A value is mandatory, so a shell
that swallows one cannot turn a request to stop verifying into a request to
keep verifying.

`-Z trust-policy` selects how an active run enforces its verdicts and is
documented on its own page. The three settings are one domain rather than
separate switches, so a row's authenticated policy source is unambiguous by
construction.

`#[trust::contract_panic(message_contains = "...")]` documents an intentional
reachable panic; it does not prove panic-freedom. Strict and memory-safe builds
therefore fail on a matched reachable contract panic. The advisory policy may
publish it as visible `contract-panic:*` conditional evidence, without proof
credit. An
intentional-panic API must explicitly select one of those nonfatal policies;
the annotation is not a hidden strict-mode exception.

Corpus workflows may combine `-Z trust-dump=mir-only:<directory>` with
`-Z trust-policy=advisory`. That tracked mode publishes MIR inputs without
solver/certifier dispatch and records them as unproved; the retired
`TRUST_DUMP_ONLY` environment variable has no effect.

The old activation and "full" switches are retired. Strict native verification
is now the default, so callers must remove those spellings rather than trying to
recreate the old two-lane activation model.

Proven-check elision has no switch. Wherever verification runs, a runtime
overflow check whose obligation the clean CIC kernel independently certified is
removed from the emitted code; every weaker outcome keeps its check. The former
`TRUST_ELIDE_CERTIFIED_CHECKS` environment switch is intentionally unsupported
because hidden process state cannot safely select generated code or incremental
reuse.

For most users and automation, prefer `targo trust check` and
`targo trust check --format json`.
