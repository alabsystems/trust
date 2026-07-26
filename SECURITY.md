# Security Policy

Trust is a verification tool, so its threat model is unusual: the most serious
bug class is not a crash but a **false assurance** — the verifier reporting that
an unsafe program is `proved`/`Trusted`. Soundness holes are treated as security
vulnerabilities here.

## Supported versions

Development happens on `main`. Only `main` (built from the reviewed commit)
receives fixes; there are no long-lived release branches at this stage.

| Branch | Receives fixes |
|--------|----------------|
| `main` | Yes |
| anything else | No |

## What counts as a vulnerability

- A verdict of `proved`, `Trusted`, or `Certified` for a program that actually
  violates the claimed property (the highest-severity class).
- A way to make the verifier silently skip obligations it should have checked.
- Tampering with the proof/result cache, provenance, or attestation artifacts
  so that stale or forged evidence is accepted as current.
- Conventional memory-safety or denial-of-service issues in the Trust-owned
  crates and the `targo-trust` driver.

## Reporting

Please report privately — **never** through a public issue or pull request.

1. **Preferred:** open a private
   [GitHub Security Advisory](https://github.com/alabsystems/trust/security/advisories/new).
2. **Fallback:** email andrewyates.name@gmail.com.

A useful report includes a description, a minimal reproducer, the affected
commit, the observed impact, and — if you have one — a suggested fix.

## Scope

In scope: the Trust verification crates under `crates/`, the Trust-authored
compiler hooks (the MIR verification pass and the surrounding plumbing, marked
in source with the `Trust:` annotation), and the `targo-trust` subcommand.

Out of scope: defects in unmodified upstream `rustc`/`std`. Those belong
upstream at <https://github.com/rust-lang/rust>.

## After a fix

Resolved issues are written up in a GitHub Security Advisory once a fix lands; a
CVE may be requested when the impact warrants it.
