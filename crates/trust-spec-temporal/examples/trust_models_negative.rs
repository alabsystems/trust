// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 The Trust Authors

//! NEGATIVE fixture: a model whose committed invariant is genuinely violated.
//! Running this example MUST exit nonzero — it is the acceptance proof that the
//! build-time gate fails the build on a real counterexample (not a tautology).
//!
//! `Stuck: x = 0` claims the head never advances, but `Bump` sets `x = 1` from
//! the initial state, so ty finds the counterexample → `check_model` returns
//! `Failed` → `check_models_or_exit` exits 1.

use trust_spec_temporal::{Action, Invariant, Model, StateVar, Update, eq, int, var};

fn broken_model() -> Model {
    Model {
        name: "BrokenStuck",
        consts: vec![],
        vars: vec![StateVar { name: "x", init: 0 }],
        fn_vars: vec![],
        actions: vec![Action {
            name: "Bump",
            guard: Some(eq(var("x"), int(0))),
            updates: vec![Update { var: "x", expr: int(1) }],
        }],
        // FALSE after Bump — a genuine reachable violation.
        invariants: vec![Invariant { name: "Stuck", expr: eq(var("x"), int(0)) }],
    }
}

fn main() {
    trust_spec_temporal::check_models_or_exit(&[broken_model()]);
}
