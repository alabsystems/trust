// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0 or the MIT license.

//! EXHAUSTIVE kernel agreement: the emitted body IS the declaration, at `u8`.
//!
//! The crate has had two half-gates, and this file is the conjunction of them.
//!
//! * `clean_reaches_trust_ir.rs` sweeps the WHOLE domain of a `u8`/`u16` carrier
//!   — but the expected value is written by the same hand that wrote the
//!   emitter, so an emitter that is wrong in the way its author was wrong
//!   passes.
//! * `kernel_agreement.rs` and `all_widths_kernel_agreement.rs` remove the
//!   author entirely and let the CIC kernel decide — but pointwise, at the
//!   inputs the test chose. A body that agrees at those inputs and diverges
//!   elsewhere passes.
//!
//! Neither is a faithfulness gate on its own. Together they are, at a finite
//! carrier: **exhaustive agreement over the entire domain, decided by the
//! kernel, IS extensional equality at that carrier.** For a `u8` unary function
//! there are 256 inputs and this file checks all 256; for a `u8` binary function
//! there are 65 536 pairs and it checks all 65 536. There is no untried input
//! left for a divergence to hide in.
//!
//! # What this closes, and what it does not
//!
//! What it closes: for the shapes and carriers below, "the emitted TrustIR
//! computes the Clean `def`" is no longer a sample. Two total functions on a
//! finite domain that agree everywhere ARE the same function, and the kernel —
//! not this file — decided every one of those agreements.
//!
//! What it does NOT close: this is extensional equality at `u8`, established by
//! enumeration. It is not a proof for `u32`/`u64`, whose domains are not
//! enumerable (2^64 pairs); those carriers keep the pointwise gate in
//! `all_widths_kernel_agreement.rs`. And enumeration is not the same artifact as
//! the MIR lane's `admit_lowering`, which REFLECTS an emitted body back into a
//! Clean term and puts that term to the kernel — a symbolic result that holds at
//! every width at once. The crate's `GATING` section stands: this lane is still
//! not proof-carrying, and a TrustIR-side reflector is still the missing piece.
//!
//! It does mean a width-confusion, an inverted predicate, a swapped select arm,
//! a dropped literal, or an off-by-one projection cannot survive at `u8` —
//! because there is no input at which such a body agrees with the declaration
//! everywhere.
//!
//! # Why `u8` and not `u16`
//!
//! Cost. The env and the plan are built ONCE per declaration; the per-input work
//! is a kernel `unfold_island_application` plus an `is_def_eq`. At `u8` binary
//! that is 65 536 kernel round trips per declaration, which is already the
//! dominant cost in this crate's test time. `u16` binary would be 4 294 967 296.

use clean_kernel::{Environment, Expr, Name, TypeChecker};
use trust_certify::clean_island::unfold_island_application;
use trust_clean_ir::emit_clean_origin_function;
use trust_clean_origin::plan_clean_origin_body;
use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_ir::ty::Ty;
use trust_ir::value::{FuncId, FuncTyId};

/// `UInt8.ofNat n` — the carrier-typed Clean value.
fn uint8(n: u128) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("UInt8.ofNat"), vec![]),
        Expr::nat_lit(u64::try_from(n).expect("a u8 value fits a u64 literal")),
    )
}

fn env_with(decl: &str) -> Environment {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(&[decl]);
    assert!(!batch.is_rejected(), "the island must kernel-check `{decl}`: {batch:?}");
    session.environment().expect("an untainted session has an environment").clone()
}

/// Sweep EVERY input of a `u8` declaration of `arity` arguments and require the
/// kernel to agree at each one.
///
/// Returns the number of inputs checked, so a caller can assert the domain was
/// actually covered rather than trusting the loop bounds — a sweep that silently
/// checked nothing would otherwise be indistinguishable from a passing one.
fn kernel_agrees_everywhere(decl: &str, name: &str, arity: usize) -> usize {
    let env = env_with(decl);
    let plan =
        plan_clean_origin_body(&env, name).unwrap_or_else(|e| panic!("`{decl}` must plan: {e:?}"));
    let f = emit_clean_origin_function(&plan, FuncId::new(0), FuncTyId::new(0))
        .unwrap_or_else(|e| panic!("`{decl}` must emit: {e}"));
    let interp = Interpreter::new();
    let tc = TypeChecker::new(&env);

    let total: u32 = 1 << (8 * arity as u32);
    let mut checked = 0usize;
    for encoded in 0..total {
        let args: Vec<u128> =
            (0..arity).map(|i| u128::from((encoded >> (8 * i as u32)) & 0xff)).collect();

        let values: Vec<_> = args
            .iter()
            .map(|a| {
                InterpretValue::int(Ty::U8, i128::try_from(*a).expect("u8 fits i128"))
                    .unwrap_or_else(|e| panic!("{a} must be a valid u8 argument: {e:?}"))
            })
            .collect();
        let outcome = interp
            .execute_function(&f, values)
            .unwrap_or_else(|e| panic!("the emitted TrustIR must execute at {args:?}: {e:?}"));
        let produced = outcome.returns[0].as_int().expect("an integer result").as_unsigned();
        assert!(
            produced <= 0xff,
            "the emitted body produced {produced} at {args:?}, which does not fit the u8 \
             carrier -- it was emitted at the wrong width",
        );

        let kernel_args: Vec<Expr> = args.iter().copied().map(uint8).collect();
        let reduced = unfold_island_application(&env, name, &kernel_args)
            .unwrap_or_else(|| panic!("the application must unfold at {args:?}"));
        assert!(
            tc.is_def_eq(&reduced, &uint8(produced)),
            "KERNEL DISAGREEMENT for `{name}` at {args:?}: the emitted TrustIR computed \
             {produced}, and the kernel reduced the Clean application to a term not \
             definitionally equal to `UInt8.ofNat {produced}`. Exhaustive sweep, so this is \
             not a corner the test missed -- the two functions differ.\n  decl: {decl}\n  \
             reduced: {reduced:?}"
        );
        checked += 1;
    }
    checked
}

#[test]
fn every_unary_input_agrees_with_the_kernel() {
    for (decl, name) in [
        ("def ident (a : UInt8) : UInt8 := a", "ident"),
        ("def seven (a : UInt8) : UInt8 := 7", "seven"),
        ("def dbl (a : UInt8) : UInt8 := a + a", "dbl"),
        ("def inc (a : UInt8) : UInt8 := a + 1", "inc"),
        ("def dec (a : UInt8) : UInt8 := a - 1", "dec"),
        ("def sq (a : UInt8) : UInt8 := a * a", "sq"),
    ] {
        assert_eq!(
            kernel_agrees_everywhere(decl, name, 1),
            256,
            "the whole u8 domain must be swept for `{name}`",
        );
    }
}

/// The binary sweep — 65 536 kernel-decided agreements per declaration.
///
/// This is where a wrap, a borrow, a signedness confusion or a swapped arm has
/// nowhere left to hide: every pair is tried, including both carrier boundaries
/// and the whole interior.
#[test]
fn every_binary_input_agrees_with_the_kernel() {
    for (decl, name) in [
        ("def pick (a : UInt8) (b : UInt8) : UInt8 := a", "pick"),
        ("def snd (a : UInt8) (b : UInt8) : UInt8 := b", "snd"),
        ("def sum (a : UInt8) (b : UInt8) : UInt8 := a + b", "sum"),
        ("def diff (a : UInt8) (b : UInt8) : UInt8 := a - b", "diff"),
        ("def prod (a : UInt8) (b : UInt8) : UInt8 := a * b", "prod"),
        ("def minu (a : UInt8) (b : UInt8) : UInt8 := if a < b then a else b", "minu"),
    ] {
        assert_eq!(
            kernel_agrees_everywhere(decl, name, 2),
            65_536,
            "the whole u8 x u8 domain must be swept for `{name}`",
        );
    }
}
