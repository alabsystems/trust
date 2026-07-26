# Getting Support

Trust is developed and maintained by Andrew Yates. The fastest way to reach the
project is through the issue tracker on the
[alabsystems/trust](https://github.com/alabsystems/trust) repository.

## Where to start

| You want to… | Do this |
|---|---|
| Report a defect or miscompile | File an issue and tag it `bug`. Include the input crate/function, the `trustc`/`targo trust` invocation, and what you expected versus what happened. |
| Propose a capability | File an issue tagged `feature`. Describe the verification property or workflow you need and why the current pipeline cannot express it. |
| Ask how something works | File an issue tagged `question`, or open a thread under Discussions if the repository has them enabled. |
| Report a security or soundness hole | Do **not** open a public issue. Follow [SECURITY.md](SECURITY.md). A verifier that reports a false `proved` is a security defect, not a feature request. |

## Triage and turnaround

Reports are triaged by severity. Because Trust is a verification tool, anything
that lets an unsound program pass — or a sound program be rejected without an
explainable reason — jumps the queue regardless of label.

| Severity | What it means | Aim |
|---|---|---|
| Critical | Unsound `proved` / `Trusted` verdict, or a build that cannot bootstrap | Looked at the same day |
| High | Wrong rejection, crash, or regression on previously accepted Rust | Within a couple of days |
| Normal | Missing feature, ergonomics, unclear diagnostics | As capacity allows |
| Low | Docs, cosmetics, nice-to-haves | Batched |

These are intentions, not contractual SLAs — this is a research-grade compiler
under active development, and timelines move with it.

## Before you file

A good report is reproducible. Pin the commit you built (`trustc -vV` /
`build/<host>/stage2/bin/trustc`), attach the smallest input that triggers the
behavior, and paste the verifier output verbatim. Reproductions against a fresh
stage2 of the reviewed commit are worth far more than prose.
