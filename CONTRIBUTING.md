# Contributing to Trust

Trust is its own verification-oriented compiler toolchain. It grew from a fork of `rust-lang/rust` and still merges upstream, because drop-in compatibility with the Rust ecosystem is a release gate — but Trust is not downstream of Rust's roadmap, and inherited surface that serves no Trust purpose gets deleted rather than preserved. The project's design principles — verification by default, no flags-heavy designs, trust-ir as the target universal IR, drop-in by construction, own the supply chain — are non-negotiable and every plan, PR, and design doc is held to them. This guide covers contributing to the verification pipeline.

**Author:** Andrew Yates
**Copyright:** 2026 Andrew Yates | **License:** Apache 2.0
**Repo:** local Trust checkout. Do not assume a public source mirror is
available for local development or release evidence.

---

## 1. Workspace Layout

```
trust/
├── compiler/               # Upstream rustc crates (modify surgically)
├── crates/                 # Trust verification crates (build freely)
│   ├── trust-mir-extract/  #   MIR -> logical model extraction
│   ├── trust-vcgen/        #   Logical model -> verification conditions
│   ├── trust-router/       #   VC dispatch to solver backends
│   ├── trust-types/        #   Shared types (VcKind, Formula, etc.)
│   ├── trust-report/       #   Proof report generation (HTML/text)
│   ├── trust-strengthen/   #   AI spec inference (Idea 2)
│   ├── trust-backprop/     #   Source rewriting (Idea 3)
│   ├── trust-convergence/  #   Fixed-point detection
│   ├── trust-proof-cert/   #   Proof certificates
│   ├── trust-cache/        #   Formula hash and result caching
│   ├── trust-loop/         #   Prove-strengthen-backprop driver — NOT in the
│   │                       #     compiler path; see the note below
│   └── ...                 #   57 crate directories; 52 workspace members
├── targo-trust/           # `targo trust` verifier subcommand implementation
├── library/                # Rust standard library (upstream, read-only)
└── x.py                    # Upstream build system
```

Key dependency graph of the crates the compiler actually calls:

```
rustc_mir_transform (trust_verify pass)
  -> trust-mir-extract -> trust-types
  -> trust-vcgen       -> trust-types
  -> trust-router      -> trust-types
```

`trust-loop` is the iterative prove -> strengthen -> backprop driver and it is
**not** part of that pass. It has no compiler call site, and the only manifest
outside its own that depends on it is `trust-integration-tests`. `trust-backprop`
is reached from `targo trust loop`, outside the compiler. Do not add a diagram
that puts either inside the MIR pass.

---

## 2. Building

### The full compiler (rarely needed for crate work)

```bash
./x.py build --stage 2  # Builds the full stage2 rustc + verification pass
./x.py test --stage 2   # Runs all upstream rustc tests with stage2
```

### Trust verification crates (the common workflow)

```bash
# Check all workspace crates compile
targo --unverified check --all

# Test specific crates (preferred over --all which hits upstream crate issues)
targo --unverified test -p trust-types -p trust-vcgen -p trust-router -p trust-loop

# Test a single crate
targo --unverified test -p trust-vcgen

# Clippy (hard gate -- must pass)
targo tippy --all-targets -- -D warnings

# Format check
targo fmt --check
```

### Prerequisites

- Local Trust toolchain built from this checkout with its `bin` directory on `PATH`
- Python 3.11+ for bootstrap and repository helper scripts
- **ay SMT solver** on `PATH` (for real proof verification): use the controlled
  local/private ay checkout or admitted source snapshot.
- Standard compiler build dependencies for this fork; see [INSTALL.md](INSTALL.md)

---

## 3. Running The Verification Pipeline

### Supported local install from this checkout

```bash
./x.py build --stage 2
export PATH="$PWD/build/host/stage2/bin:$PATH"
targo trust doctor
targo trust --help
```

If `targo trust` cannot find the built compiler automatically, run it from the Trust root that contains sibling `targo`, `targo-trust`, and `trustc` binaries.

### Public human-facing CLI

```bash
targo trust check examples/midpoint.rs
```

### Public machine-facing CLI

```bash
targo trust check --format json examples/midpoint.rs
```

### Developer transport

```bash
targo --unverified run --manifest-path targo-trust/Cargo.toml -- trust check examples/midpoint.rs
```

### Low-level compiler transport

```bash
./build/host/stage2/bin/trustc \
  -Z trust-verify-output=json \
  --edition 2021 \
  examples/midpoint.rs
```

The public front door for contributors and automation is `targo trust check` and `targo trust check --format json`. The repo-local `targo --unverified run --manifest-path targo-trust/Cargo.toml -- trust ...` path is an explicitly unverified build of the developer CLI transport; the nested `trust ...` command still selects its own verification workflow. Raw `trustc ...` is separate developer transport and verifies fail-closed by default; pass `-Z trust-verify=off` only for an explicit vanilla-compatibility run. Per-unit role, package, and freshness-session options are reserved Targo-to-trustc transport and must not be supplied manually.

The pipeline flow is: **MIR extraction -> VC generation -> backend dispatch -> proof report**.

---

## 4. Upstream Discipline (compiler/ modifications)

The `compiler/` directory contains inherited compiler code plus Trust-owned verification changes. Keep modifications surgical: it is what keeps review, bisecting, and the periodic upstream merge tractable. That merge exists to hold drop-in compatibility, which is a release gate — it is not a reason to defer a rename or inherit a design decision.

### Rules

1. **Read the inherited code first.** Understand what exists before changing it.
2. **Surgical modifications only.** Add verification hooks; do not restructure upstream code.
3. **Mark all Trust additions** with `// Trust:` comments. Example:

   ```rust
   // Trust: Hook into MIR for verification condition generation
   if tcx.sess.opts.unstable_opts.trust_verify {
       trust_mir_extract::extract(tcx, body);
   }
   ```

4. **Never break existing behavior.** All valid Rust must compile identically under Trust. Verification is additive.
5. **Compatibility tests must pass.** `./x.py test` and the Trust gates must pass with your modifications.

### Source ownership

Do not add a new dependency on a live upstream Rust checkout, submodule, or bootstrap endpoint. Third-party proof tools and former submodules must be checked in as local source snapshots or explicitly vendored before they are part of the default Trust path.

---

## 5. Adding a New VC Kind

Verification condition kinds are defined in `crates/trust-types/src/formula/vc_kind.rs` as variants of `VcKind`:

```rust
pub enum VcKind {
    ArithmeticOverflow { op: BinOp, operand_tys: (Ty, Ty) },
    ShiftOverflow { op: BinOp, operand_ty: Ty, shift_ty: Ty },
    DivisionByZero,
    RemainderByZero,
    IndexOutOfBounds,
    // ... 70+ variants
}
```

Steps to add a new kind:

1. **Add the variant** to `VcKind` in `crates/trust-types/src/formula/vc_kind.rs`.
2. **Update `VcKind::description()`** to return a human-readable name.
3. **Generate VCs** in `crates/trust-vcgen/` -- the vcgen module creates `VerificationCondition` values with your new kind from the logical model.
4. **Route the VC** -- ensure `crates/trust-router/` backends can handle it. The router calls `backend.can_handle(vc)` to decide dispatch.
5. **Add tests** -- at minimum: a unit test in trust-vcgen that generates the new VC kind, and an integration test showing the router dispatches it correctly.

---

## 6. Adding a New Solver Backend

Solver backends live in `crates/trust-router/src/` and implement the `VerificationBackend` trait declared in `crates/trust-router/src/backend_trait.rs`:

```rust
pub trait VerificationBackend: Send + Sync {
    fn name(&self) -> &str;
    fn role(&self) -> BackendRole { BackendRole::General }
    fn can_handle(&self, vc: &VerificationCondition) -> bool;
    fn verify(&self, vc: &VerificationCondition) -> VerificationResult;
}
```

The `*_backend.rs` files that exist in `crates/trust-router/src/` and the
`name()`/`role()` each reports:

| `name()` | File | `role()` |
|---|---|---|
| `ay-in-process` | `in_process_ay_backend.rs` | `SmtSolver` |
| `trust-wp` | `trust_wp_backend.rs` | `Deductive` |
| `ty` | `ty_backend.rs` | `Temporal` |
| `interval` | `interval_backend.rs` | `AbstractInterpretation` |
| `trust_cg-router` | `trust_cg_backend.rs` | `General` (codegen is not a solver role) |

`smtlib_backend.rs` is **not** a backend: the subprocess `SmtLibBackend` struct
was removed in favour of direct library calls, and the file now holds the
SMT-LIB2 serialization and result-parsing utilities. trust-mc and trust-vc are
reached through the full-verification engine, not through a `*_backend.rs` file
here. Read the current directory before citing this table — a stale backend list
was one of the errors that made this file untrustworthy.

Steps to add a new backend:

1. **Create** `crates/trust-router/src/my_backend.rs`.
2. **Implement** `VerificationBackend`. Choose the appropriate `BackendRole`.
3. **Register** in `crates/trust-router/src/lib.rs` (add module declaration, re-export).
4. **Add the git dependency** (if external) to `Cargo.toml` at both workspace root and `crates/Cargo.toml`, with rev pinning.
5. **Write tests** -- use `mock_backend.rs` as a template. Test `can_handle`, `verify`, and error paths.

The router dispatches VCs to backends via `can_handle()`. Backends that return `false` are skipped. The fallback chain and portfolio racing logic handle timeouts and errors automatically.

---

## 7. Testing Conventions

### Test naming

```
test_<unit>_<scenario>_<expected>
```

Example: `test_vcgen_division_by_zero_generates_vc`, `test_router_timeout_falls_back`.

### Property-based testing

We use `proptest` for roundtrip and fuzz testing. Example crates: trust-types, trust-vcgen, trust-cache, trust-proof-cert.

```rust
proptest! {
    #[test]
    fn roundtrip_serialize(formula in arb_formula()) {
        let bytes = serialize(&formula);
        let recovered = deserialize(&bytes).unwrap();
        prop_assert_eq!(formula, recovered);
    }
}
```

### Integration tests

End-to-end pipeline tests live in `crates/trust-integration-tests/`. These exercise the full MIR -> vcgen -> router -> result path.

### Rules

- **No `#[ignore]`** -- tests must PASS, FAIL, or be DELETED.
- **No `todo!()` / `unimplemented!()` in production code.**
- **`.unwrap()` is fine in tests** but forbidden in production (use `?` or `.expect("reason")`).
- Tests must be deterministic and isolated. Use `tempdir()` for filesystem state.

### Running tests

```bash
# All Trust crates (recommended)
targo --unverified test -p trust-types -p trust-vcgen -p trust-router -p trust-loop \
    -p trust-mir-extract -p trust-report -p trust-cache -p trust-proof-cert

# Single crate with output
targo --unverified test -p trust-vcgen -- --nocapture

# Just one test
targo --unverified test -p trust-vcgen -- test_vcgen_overflow
```

---

## 8. MIR Extraction Gotchas

The `trust-mir-extract` crate converts Rust MIR into a logical model (`LiftedFunction`). Common pitfalls:

- **SSA form**: MIR is not in SSA. The extractor builds SSA (`LiftedFunction.ssa: Option<SsaForm>`) via a separate pass. Not all functions have SSA yet.
- **Terminators with side effects**: `Terminator::Call` carries an `atomic: Option<AtomicOperation>` field. Be aware of it when pattern-matching terminators.
- **Proof annotations**: `LiftedFunction.annotations: Vec<ProofAnnotation>` carries the contract clauses parsed from source. The front door is first-class signature grammar (`fn f(..) requires P ensures Q decreases e`), stored as native clauses on `ast::FnContract`; `trust-spec`'s `#[trust::*]` attributes are passthrough shims for stable-Rust builds and carry no proof meaning. These feed into vcgen.
- **Generic functions**: Monomorphization means the same source function yields different MIR bodies. Extraction handles each monomorphized instance independently.
- **Cleanup blocks**: MIR panic/unwind paths generate cleanup blocks. The extractor currently skips these for VC generation but preserves them in the model.

---

## 9. Issue Workflow

Track work through this repository's GitHub issue tracker
(`github.com/alabsystems/trust/issues`). The repository is private; `gh auth login` first.

### Priorities

| Label | Meaning |
|-------|---------|
| `P0` | System compromised -- postmortem required |
| `P1` | Blocks critical path |
| `P2` | Normal work |
| `P3` | Low priority |
| `urgent` | Work immediately (orthogonal to P-level) |

### Labels

- `bug`, `feature`, `documentation` -- type
- `in-progress` + ownership label (e.g., `W1`) -- claimed
- `blocked` -- waiting on dependency
- `designing` -- design in progress, not ready for implementation
- `do-audit` / `needs-review` -- ready for review
- `epic` -- tracking issue with `## Tasks` checklist

### Commit messages

Reference the issue: `Part of #N` for partial work, `Fixes #N` for complete resolution (with proof in `## Verified`).

### Filing issues

Use `gh issue create` against this repository:

```bash
gh issue create --title "Bug: description" --label "bug,P2" --body-file - <<'EOF'
## Description
What happened vs. what was expected.

## Reproduction
Steps to reproduce.

## Acceptance Criteria
- [ ] Specific verifiable outcome
EOF
```

---

## Quick Reference

| Task | Command |
|------|---------|
| Check compilation | `targo --unverified check --all` |
| Run tests | `targo --unverified test -p trust-vcgen -p trust-types ...` |
| Lint | `targo tippy --all-targets -- -D warnings` |
| Format | `targo fmt --check` |
| Build full compiler | `./x.py build --stage 2` |
| Run verification (human) | `targo trust check file.rs` |
| Run verification (json) | `targo trust check --format json file.rs` |
| View issue | `gh issue view N` |
