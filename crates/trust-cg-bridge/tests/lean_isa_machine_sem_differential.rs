// Trust: RUNG 4 — F3 (TCB-MACHINE-SEM) retirement via a trust_machine_sem <-> Lean
// ISA DIFFERENTIAL. GRADE: [VALIDATED] / execution-validated equivalence. NOT [PROVED].
//
// =============================================================================
//  WHAT THIS GATE ESTABLISHES (and what it does NOT).
// =============================================================================
//
//  F3 = TCB-MACHINE-SEM is the floor item: the proven-output gate
//  (trust-cg-bridge/src/verify_output.rs) decodes the EMITTED machine bytes via
//  the RUST `trust_machine_sem::Aarch64Semantics` model to obtain the
//  machine-side effect it compares against the IR auto-spec. Until now that Rust
//  model was "execution-validated, not formally verified" — and crucially the
//  gate used the RUST model, NOT the kernel-validated Lean ISA
//  (`first-party/clean/proofs/aarch64_isa.lean`), which is backed by the ~65k
//  on-chip M4 hardware-differential `:= rfl` theorems. That left an UNPROVEN
//  Rust-vs-Lean gap in F3.
//
//  This test closes that gap at the achievable grade: a DIFFERENTIAL equivalence
//  between the two models over the COVERED linear-ALU opcodes (the ops the gate
//  decodes). For each opcode and each sampled input pair (a, b):
//
//    route-(R) RUST MODEL : decode a real AArch64 instruction word with
//                           `trust_disasm::decode_aarch64` (the SAME decoder F3
//                           uses), seed a `ConcreteState`, run
//                           `Aarch64Semantics::effects`, apply, read the dest GPR.
//    route-(L) LEAN ISA   : register the corresponding `aarch64_isa.lean` B-def
//                           as a reducible kernel `Definition` and reduce the
//                           application `<op> a b` to a closed `Nat` literal with
//                           the clean-kernel WHNF reducer (the SAME def bodies the
//                           65k-theorem on-chip hardware differential validates,
//                           and that the micro-diversity gate re-checks).
//
//  assert route-(R) == route-(L) for every sampled input. Agreement over the
//  whole sample means: the Rust gate-side model and the kernel-validated Lean ISA
//  AGREE on the covered opcodes + the AArch64 decoder for those ops. This backs
//  F3 with the hardware-oracle Lean model.
//
//  HONESTY (load-bearing). This is [VALIDATED]/differential — execution-validated
//  equivalence over a SAMPLED (not exhaustive over 2^128) input set. It is NOT a
//  kernel [PROVED] Rust=Lean executable-semantics equivalence: that would require
//  embedding `trust_types::Formula` evaluation into the Clean kernel and proving
//  per-opcode congruence (CompCert-scale, the long horizon). We claim ONLY the
//  differential grade. The Lean DEFS themselves are kernel-reducible with zero
//  domain axioms; this test does not re-prove that — it consumes it.
//
//  NEGATIVE CONTROL (`negative_control_*`): inject a WRONG machine-sem effect for
//  one opcode (decode an ADD word but compare it against the Lean SUB def) and
//  confirm the differential CATCHES the disagreement — proving the gate has teeth
//  and a flipped semantic arm could not slip through.

#![cfg(target_arch = "aarch64")]

use clean_kernel::env::Declaration;
use clean_kernel::expr::{BinderInfo, Expr, ExprKind};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::Environment;

use trust_disasm::decode_aarch64;
use trust_machine_sem::{Aarch64Semantics, ConcreteState, MachineState, Semantics};

// ===========================================================================
//  route-(L): the Lean ISA side — register aarch64_isa.lean B-defs in a kernel
//  Environment and reduce `<op> a b` (or `<op> a`) to a closed Nat via WHNF.
//  Def bodies mirror proofs/aarch64_isa.lean VERBATIM (cross-checked against the
//  clean-kernel micro_diversity_gate corpus which mirrors the same file).
// ===========================================================================

fn c(s: &str) -> Expr {
    Expr::const_(Name::from_string(s), vec![])
}
fn lit(n: u64) -> Expr {
    Expr::nat_lit(n)
}
/// Literal for a value that may exceed u64 (we never need >2^64 here, but stay total).
fn big_lit(n: u128) -> Expr {
    if let Ok(small) = u64::try_from(n) {
        Expr::nat_lit(small)
    } else {
        use clean_kernel::expr::{BigNat, Literal};
        let lo = (n & u128::from(u64::MAX)) as u64;
        let hi = (n >> 64) as u64;
        Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::from_limbs(vec![lo, hi]))))
    }
}
fn bvar(i: u32) -> Expr {
    Expr::bvar(i)
}
fn nat_add(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Nat.add"), [a, b])
}
fn nat_sub(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Nat.sub"), [a, b])
}
fn nat_mul(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Nat.mul"), [a, b])
}
fn nat_mod(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Nat.mod"), [a, b])
}
fn nat_div(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Nat.div"), [a, b])
}
fn nat_pow(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Nat.pow"), [a, b])
}
fn nat_land(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Nat.land"), [a, b])
}
fn nat_lor(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Nat.lor"), [a, b])
}
fn nat_xor(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Nat.xor"), [a, b])
}
fn nat_shl(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Nat.shiftLeft"), [a, b])
}
fn nat_shr(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Nat.shiftRight"), [a, b])
}
fn nat_beq(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Nat.beq"), [a, b])
}
fn nat_ble(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Nat.ble"), [a, b])
}

fn def2(env: &mut Environment, name: &str, body: Expr) {
    let nat = c("Nat");
    let ty = Expr::pi(
        BinderInfo::Default,
        nat.clone(),
        Expr::pi(BinderInfo::Default, nat.clone(), nat.clone()),
    );
    let value = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(BinderInfo::Default, nat.clone(), body),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_: ty,
        value,
        is_reducible: true,
    })
    .unwrap_or_else(|e| panic!("register {name}: {e}"));
}
fn def1(env: &mut Environment, name: &str, body: Expr) {
    let nat = c("Nat");
    let ty = Expr::pi(BinderInfo::Default, nat.clone(), nat.clone());
    let value = Expr::lam(BinderInfo::Default, nat.clone(), body);
    env.add_decl(Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_: ty,
        value,
        is_reducible: true,
    })
    .unwrap_or_else(|e| panic!("register {name}: {e}"));
}
fn def3(env: &mut Environment, name: &str, body: Expr) {
    let nat = c("Nat");
    let ty = Expr::pi(
        BinderInfo::Default,
        nat.clone(),
        Expr::pi(
            BinderInfo::Default,
            nat.clone(),
            Expr::pi(BinderInfo::Default, nat.clone(), nat.clone()),
        ),
    );
    let value = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(
            BinderInfo::Default,
            nat.clone(),
            Expr::lam(BinderInfo::Default, nat.clone(), body),
        ),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_: ty,
        value,
        is_reducible: true,
    })
    .unwrap_or_else(|e| panic!("register {name}: {e}"));
}
fn def1_bool(env: &mut Environment, name: &str, body: Expr) {
    let nat = c("Nat");
    let ty = Expr::pi(BinderInfo::Default, nat.clone(), c("Bool"));
    let value = Expr::lam(BinderInfo::Default, nat.clone(), body);
    env.add_decl(Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_: ty,
        value,
        is_reducible: true,
    })
    .unwrap_or_else(|e| panic!("register {name}: {e}"));
}

/// `if (cond : Bool) then then_ else else_` at result type `Nat`, mirrored as the
/// kernel-reducible `@Bool.rec.{1} (fun _ : Bool => Nat) else_ then_ cond` (the
/// same form micro_diversity_gate / the prelude `cond` use).
fn cond_nat(cond: Expr, then_: Expr, else_: Expr) -> Expr {
    let type1 = Level::succ(Level::zero());
    let motive = Expr::lam(BinderInfo::Default, c("Bool"), c("Nat"));
    Expr::apps(
        Expr::const_(Name::from_string("Bool.rec"), vec![type1]),
        [motive, else_, then_, cond],
    )
}

/// Build the kernel environment with the covered aarch64_isa.lean B-defs.
fn build_lean_isa_env() -> Environment {
    let mut env = Environment::with_prelude();
    let a = || bvar(1);
    let b = || bvar(0);

    // Word-size constants.
    def0(&mut env, "AArch64.W", nat_pow(lit(2), lit(64)));
    def0(&mut env, "AArch64.SignBit", nat_pow(lit(2), lit(63)));
    def0(&mut env, "AArch64.AllOnes", nat_sub(c("AArch64.W"), lit(1)));
    def0(&mut env, "AArch64.Ww", nat_pow(lit(2), lit(32)));
    def0(&mut env, "AArch64.SignBitW", nat_pow(lit(2), lit(31)));
    def0(&mut env, "AArch64.AllOnesW", nat_sub(c("AArch64.Ww"), lit(1)));

    // ---- 64-bit (X-form) ----
    def2(&mut env, "AArch64.bvAdd", nat_mod(nat_add(a(), b()), c("AArch64.W")));
    def2(
        &mut env,
        "AArch64.bvSub",
        nat_mod(
            nat_add(a(), nat_sub(c("AArch64.W"), nat_mod(b(), c("AArch64.W")))),
            c("AArch64.W"),
        ),
    );
    def2(&mut env, "AArch64.bvMul", nat_mod(nat_mul(a(), b()), c("AArch64.W")));
    def1(&mut env, "AArch64.bvNeg", Expr::apps(c("AArch64.bvSub"), [lit(0), bvar(0)]));
    def2(&mut env, "AArch64.bvAnd", nat_land(a(), b()));
    def2(&mut env, "AArch64.bvOr", nat_lor(a(), b()));
    def2(&mut env, "AArch64.bvXor", nat_xor(a(), b()));
    def1(
        &mut env,
        "AArch64.bvNot",
        nat_xor(nat_mod(bvar(0), c("AArch64.W")), c("AArch64.AllOnes")),
    );
    def2(
        &mut env,
        "AArch64.bvBic",
        nat_land(a(), Expr::app(c("AArch64.bvNot"), b())),
    );
    def2(
        &mut env,
        "AArch64.bvOrn",
        nat_lor(a(), Expr::app(c("AArch64.bvNot"), b())),
    );
    def2(
        &mut env,
        "AArch64.bvShl",
        nat_mod(nat_shl(a(), nat_mod(b(), lit(64))), c("AArch64.W")),
    );
    def2(
        &mut env,
        "AArch64.bvLshr",
        nat_shr(nat_mod(a(), c("AArch64.W")), nat_mod(b(), lit(64))),
    );
    // topSet / signFill / bvAsr (Bool.rec branch).
    def1_bool(
        &mut env,
        "AArch64.topSet",
        nat_ble(c("AArch64.SignBit"), nat_mod(bvar(0), c("AArch64.W"))),
    );
    def1(
        &mut env,
        "AArch64.signFill",
        nat_sub(c("AArch64.W"), nat_pow(lit(2), nat_sub(lit(64), bvar(0)))),
    );
    {
        let s = || nat_mod(bvar(0), lit(64));
        let logical = || nat_shr(nat_mod(bvar(1), c("AArch64.W")), s());
        let filled = nat_mod(
            nat_lor(logical(), Expr::app(c("AArch64.signFill"), s())),
            c("AArch64.W"),
        );
        let body = cond_nat(Expr::app(c("AArch64.topSet"), bvar(1)), filled, logical());
        def2(&mut env, "AArch64.bvAsr", body);
    }
    // UDIV / SDIV (no-trap).
    def2(&mut env, "AArch64.bvUdiv", {
        let bb = || nat_mod(bvar(0), c("AArch64.W"));
        cond_nat(
            nat_beq(bb(), lit(0)),
            lit(0),
            nat_div(nat_mod(bvar(1), c("AArch64.W")), bb()),
        )
    });
    // sMag — signed magnitude |x| (aarch64_isa.lean:332): 2^64 - x for negative x.
    def1(
        &mut env,
        "AArch64.sMag",
        cond_nat(
            Expr::app(c("AArch64.topSet"), bvar(0)),
            nat_sub(c("AArch64.W"), nat_mod(bvar(0), c("AArch64.W"))),
            nat_mod(bvar(0), c("AArch64.W")),
        ),
    );
    {
        // bvSdiv (aarch64_isa.lean:340) — Xm==0 -> 0 (NO trap); else quotient
        // magnitude |a|/|b| (Nat floor div == truncation toward zero), negative
        // iff the operand signs DIFFER; a negative quotient re-encodes as
        // (2^64 - qm) mod 2^64 (INT_MIN/-1 wraps to INT_MIN). The .lean def
        // computes `neg := (beq (topSet a) (topSet b)).not` then branches once;
        // here we branch on topSet(a)/topSet(b) directly with the same two
        // result expressions — VALUE-identical (the differential compares fully
        // reduced Nat values), avoiding Bool.beq/Bool.not kernel plumbing.
        let qm = || {
            nat_div(
                Expr::app(c("AArch64.sMag"), bvar(1)),
                Expr::app(c("AArch64.sMag"), bvar(0)),
            )
        };
        let pos = || nat_mod(qm(), c("AArch64.W"));
        let neg = || nat_mod(nat_sub(c("AArch64.W"), nat_mod(qm(), c("AArch64.W"))), c("AArch64.W"));
        let signed_branch = cond_nat(
            Expr::app(c("AArch64.topSet"), bvar(1)),
            cond_nat(Expr::app(c("AArch64.topSet"), bvar(0)), pos(), neg()),
            cond_nat(Expr::app(c("AArch64.topSet"), bvar(0)), neg(), pos()),
        );
        let body = cond_nat(
            nat_beq(nat_mod(bvar(0), c("AArch64.W")), lit(0)),
            lit(0),
            signed_branch,
        );
        def2(&mut env, "AArch64.bvSdiv", body);
    }

    // ---- 32-bit (W-form) ----
    def2(
        &mut env,
        "AArch64.bvAddW",
        nat_mod(
            nat_add(nat_mod(a(), c("AArch64.Ww")), nat_mod(b(), c("AArch64.Ww"))),
            c("AArch64.Ww"),
        ),
    );
    def2(
        &mut env,
        "AArch64.bvSubW",
        nat_mod(
            nat_add(
                nat_mod(a(), c("AArch64.Ww")),
                nat_sub(c("AArch64.Ww"), nat_mod(b(), c("AArch64.Ww"))),
            ),
            c("AArch64.Ww"),
        ),
    );
    def2(
        &mut env,
        "AArch64.bvMulW",
        nat_mod(
            nat_mul(nat_mod(a(), c("AArch64.Ww")), nat_mod(b(), c("AArch64.Ww"))),
            c("AArch64.Ww"),
        ),
    );
    def1(&mut env, "AArch64.bvNegW", Expr::apps(c("AArch64.bvSubW"), [lit(0), bvar(0)]));
    def2(
        &mut env,
        "AArch64.bvAndW",
        nat_land(nat_mod(a(), c("AArch64.Ww")), nat_mod(b(), c("AArch64.Ww"))),
    );
    def2(
        &mut env,
        "AArch64.bvOrW",
        nat_lor(nat_mod(a(), c("AArch64.Ww")), nat_mod(b(), c("AArch64.Ww"))),
    );
    def2(
        &mut env,
        "AArch64.bvXorW",
        nat_xor(nat_mod(a(), c("AArch64.Ww")), nat_mod(b(), c("AArch64.Ww"))),
    );
    def1(
        &mut env,
        "AArch64.bvNotW",
        nat_xor(nat_mod(bvar(0), c("AArch64.Ww")), c("AArch64.AllOnesW")),
    );
    def2(
        &mut env,
        "AArch64.bvShlW",
        nat_mod(nat_shl(nat_mod(a(), c("AArch64.Ww")), nat_mod(b(), lit(32))), c("AArch64.Ww")),
    );
    def2(
        &mut env,
        "AArch64.bvLshrW",
        nat_shr(nat_mod(a(), c("AArch64.Ww")), nat_mod(b(), lit(32))),
    );
    def1_bool(
        &mut env,
        "AArch64.topSetW",
        nat_ble(c("AArch64.SignBitW"), nat_mod(bvar(0), c("AArch64.Ww"))),
    );
    def1(
        &mut env,
        "AArch64.signFillW",
        nat_sub(c("AArch64.Ww"), nat_pow(lit(2), nat_sub(lit(32), bvar(0)))),
    );
    {
        let s = || nat_mod(bvar(0), lit(32));
        let logical = || nat_shr(nat_mod(bvar(1), c("AArch64.Ww")), s());
        let filled = nat_mod(
            nat_lor(logical(), Expr::app(c("AArch64.signFillW"), s())),
            c("AArch64.Ww"),
        );
        let body = cond_nat(Expr::app(c("AArch64.topSetW"), bvar(1)), filled, logical());
        def2(&mut env, "AArch64.bvAsrW", body);
    }
    // UDIV (W) — 32-bit no-trap unsigned divide (aarch64_isa.lean:349).
    def2(&mut env, "AArch64.bvUdivW", {
        let bb = || nat_mod(bvar(0), c("AArch64.Ww"));
        cond_nat(
            nat_beq(bb(), lit(0)),
            lit(0),
            nat_div(nat_mod(bvar(1), c("AArch64.Ww")), bb()),
        )
    });
    // sMagW / bvSdivW — 32-bit analogs (aarch64_isa.lean:355,359); same
    // value-identical branch reformulation as bvSdiv above.
    def1(
        &mut env,
        "AArch64.sMagW",
        cond_nat(
            Expr::app(c("AArch64.topSetW"), bvar(0)),
            nat_sub(c("AArch64.Ww"), nat_mod(bvar(0), c("AArch64.Ww"))),
            nat_mod(bvar(0), c("AArch64.Ww")),
        ),
    );
    {
        let qm = || {
            nat_div(
                Expr::app(c("AArch64.sMagW"), bvar(1)),
                Expr::app(c("AArch64.sMagW"), bvar(0)),
            )
        };
        let pos = || nat_mod(qm(), c("AArch64.Ww"));
        let neg =
            || nat_mod(nat_sub(c("AArch64.Ww"), nat_mod(qm(), c("AArch64.Ww"))), c("AArch64.Ww"));
        let signed_branch = cond_nat(
            Expr::app(c("AArch64.topSetW"), bvar(1)),
            cond_nat(Expr::app(c("AArch64.topSetW"), bvar(0)), pos(), neg()),
            cond_nat(Expr::app(c("AArch64.topSetW"), bvar(0)), neg(), pos()),
        );
        let body = cond_nat(
            nat_beq(nat_mod(bvar(0), c("AArch64.Ww")), lit(0)),
            lit(0),
            signed_branch,
        );
        def2(&mut env, "AArch64.bvSdivW", body);
    }

    // ---- MADD / MSUB (3-ary): Rd = Ra +/- Rn*Rm ----
    def3(
        &mut env,
        "AArch64.bvMadd",
        nat_mod(nat_add(bvar(2), nat_mul(bvar(1), bvar(0))), c("AArch64.W")),
    );
    def3(
        &mut env,
        "AArch64.bvMsub",
        nat_mod(
            nat_add(bvar(2), nat_sub(c("AArch64.W"), nat_mod(nat_mul(bvar(1), bvar(0)), c("AArch64.W")))),
            c("AArch64.W"),
        ),
    );
    // MADD/MSUB (W) — operands narrowed to the low 32 bits, upper 32 zeroed
    // (aarch64_isa.lean:305,308).
    def3(
        &mut env,
        "AArch64.bvMaddW",
        nat_mod(
            nat_add(
                nat_mod(bvar(2), c("AArch64.Ww")),
                nat_mul(nat_mod(bvar(1), c("AArch64.Ww")), nat_mod(bvar(0), c("AArch64.Ww"))),
            ),
            c("AArch64.Ww"),
        ),
    );
    def3(
        &mut env,
        "AArch64.bvMsubW",
        nat_mod(
            nat_add(
                nat_mod(bvar(2), c("AArch64.Ww")),
                nat_sub(
                    c("AArch64.Ww"),
                    nat_mod(
                        nat_mul(nat_mod(bvar(1), c("AArch64.Ww")), nat_mod(bvar(0), c("AArch64.Ww"))),
                        c("AArch64.Ww"),
                    ),
                ),
            ),
            c("AArch64.Ww"),
        ),
    );

    env
}

/// 0-ary Nat constant def (local helper; mirrors micro_diversity_gate's def0).
fn def0(env: &mut Environment, name: &str, body: Expr) {
    env.add_decl(Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_: c("Nat"),
        value: body,
        is_reducible: true,
    })
    .unwrap_or_else(|e| panic!("register {name}: {e}"));
}

/// Read a reduced closed `Nat` literal back to u128 (64-bit results -> <= 2 limbs).
fn nat_lit_to_u128(e: &Expr) -> Option<u128> {
    use clean_kernel::expr::Literal;
    if let ExprKind::Lit(Literal::Nat(bn)) = e.kind() {
        let limbs = bn.limbs();
        let lo = u128::from(*limbs.first().unwrap_or(&0));
        let hi = u128::from(*limbs.get(1).unwrap_or(&0));
        Some((hi << 64) | lo)
    } else {
        None
    }
}

/// The Lean ISA evaluator: reduce a fully-applied B-def application to a u128.
struct LeanIsa {
    env: Environment,
}
impl LeanIsa {
    fn new() -> Self {
        Self { env: build_lean_isa_env() }
    }
    /// Reduce `<op> a b` to its closed Nat value via the kernel WHNF reducer.
    fn eval2(&self, op: &str, a: u128, b: u128) -> u128 {
        let app = Expr::apps(c(op), [big_lit(a), big_lit(b)]);
        let tc = clean_kernel::tc::TypeChecker::new(&self.env);
        let reduced = tc.whnf(&app);
        nat_lit_to_u128(&reduced)
            .unwrap_or_else(|| panic!("Lean def {op} did not reduce to a Nat literal: {reduced:?}"))
    }
    /// Reduce `<op> a` to its closed Nat value.
    fn eval1(&self, op: &str, a: u128) -> u128 {
        let app = Expr::app(c(op), big_lit(a));
        let tc = clean_kernel::tc::TypeChecker::new(&self.env);
        let reduced = tc.whnf(&app);
        nat_lit_to_u128(&reduced)
            .unwrap_or_else(|| panic!("Lean def {op} did not reduce to a Nat literal: {reduced:?}"))
    }
    /// Reduce `<op> ra rn rm` (3-ary MADD/MSUB form).
    fn eval3(&self, op: &str, ra: u128, rn: u128, rm: u128) -> u128 {
        let app = Expr::apps(c(op), [big_lit(ra), big_lit(rn), big_lit(rm)]);
        let tc = clean_kernel::tc::TypeChecker::new(&self.env);
        let reduced = tc.whnf(&app);
        nat_lit_to_u128(&reduced)
            .unwrap_or_else(|| panic!("Lean def {op} did not reduce to a Nat literal: {reduced:?}"))
    }
}

// ===========================================================================
//  route-(R): the Rust trust_machine_sem side — decode a real instruction word
//  and run its effect over a ConcreteState, returning the destination GPR.
// ===========================================================================

/// Run one decoded AArch64 instruction `word` whose source operands are X1, X2
/// (and X3 for 3-ary madd/msub) seeded to `inputs`, and read the `dst` GPR at
/// `width` bits. The instruction must be straight-line (the covered ALU ops are).
fn run_machine_sem(word: u32, inputs: &[(u8, u64)], dst: u8, width: u32) -> u128 {
    let insn = decode_aarch64(&word.to_le_bytes(), 0x1000)
        .unwrap_or_else(|e| panic!("decode {word:#010x}: {e:?}"));
    let mut cs = ConcreteState::new();
    for &(reg, val) in inputs {
        cs.gpr[reg as usize] = val;
    }
    let sem = Aarch64Semantics;
    let ms = MachineState::symbolic();
    let effects = sem
        .effects(&ms, &insn)
        .unwrap_or_else(|e| panic!("effects for {word:#010x} ({:?}): {e:?}", insn.opcode));
    let pre = cs.clone();
    for eff in &effects {
        // Skip PC advances / flag updates for the value comparison; apply the
        // architectural register write against the instruction pre-state.
        use trust_machine_sem::Effect;
        match eff {
            Effect::RegWrite { .. } | Effect::SpWrite { .. } => {
                cs.apply_effect_with_eval_state(&pre, eff)
                    .unwrap_or_else(|e| panic!("apply {word:#010x}: {e:?}"));
            }
            _ => {}
        }
    }
    cs.read_gpr(dst, width)
}

// ===========================================================================
//  THE COVERED OPCODE TABLE.  Each entry pairs a real AArch64 instruction word
//  (dst=x0/w0, srcs as noted) with the matching Lean ISA def. Encodings are the
//  C6 register/extract forms the linear-ALU fragment emits.
// ===========================================================================

#[derive(Clone, Copy)]
enum Arity {
    /// binary X1,X2 -> X0; Lean `op a b`.
    Bin2,
    /// unary X1 -> X0; Lean `op a`.
    Un1,
    /// ternary madd/msub: Lean `op(ra=X3, rn=X1, rm=X2)`, asm Rd,Rn,Rm,Ra.
    Madd,
}

struct OpCase {
    name: &'static str,
    word: u32,
    lean: &'static str,
    arity: Arity,
    width: u32,
}

/// The covered linear-ALU opcodes, 64-bit and 32-bit. dst = x0/w0.
/// 64-bit register forms use Rn=x1, Rm=x2; W-forms use w1/w2.
fn covered_ops() -> Vec<OpCase> {
    use Arity::*;
    vec![
        // ---- 64-bit (X) ----
        OpCase { name: "add",  word: 0x8B02_0020, lean: "AArch64.bvAdd",  arity: Bin2, width: 64 },
        OpCase { name: "sub",  word: 0xCB02_0020, lean: "AArch64.bvSub",  arity: Bin2, width: 64 },
        OpCase { name: "mul",  word: 0x9B02_7C20, lean: "AArch64.bvMul",  arity: Bin2, width: 64 }, // MADD x0,x1,x2,xzr
        OpCase { name: "and",  word: 0x8A02_0020, lean: "AArch64.bvAnd",  arity: Bin2, width: 64 },
        OpCase { name: "orr",  word: 0xAA02_0020, lean: "AArch64.bvOr",   arity: Bin2, width: 64 },
        OpCase { name: "eor",  word: 0xCA02_0020, lean: "AArch64.bvXor",  arity: Bin2, width: 64 },
        OpCase { name: "bic",  word: 0x8A22_0020, lean: "AArch64.bvBic",  arity: Bin2, width: 64 },
        OpCase { name: "orn",  word: 0xAA22_0020, lean: "AArch64.bvOrn",  arity: Bin2, width: 64 },
        OpCase { name: "lslv", word: 0x9AC2_2020, lean: "AArch64.bvShl",  arity: Bin2, width: 64 },
        OpCase { name: "lsrv", word: 0x9AC2_2420, lean: "AArch64.bvLshr", arity: Bin2, width: 64 },
        OpCase { name: "asrv", word: 0x9AC2_2820, lean: "AArch64.bvAsr",  arity: Bin2, width: 64 },
        OpCase { name: "udiv", word: 0x9AC2_0820, lean: "AArch64.bvUdiv", arity: Bin2, width: 64 },
        OpCase { name: "sdiv", word: 0x9AC2_0C20, lean: "AArch64.bvSdiv", arity: Bin2, width: 64 },
        OpCase { name: "neg",  word: 0xCB01_03E0, lean: "AArch64.bvNeg",  arity: Un1,  width: 64 }, // SUB x0,xzr,x1
        OpCase { name: "mvn",  word: 0xAA21_03E0, lean: "AArch64.bvNot",  arity: Un1,  width: 64 }, // ORN x0,xzr,x1
        OpCase { name: "madd", word: 0x9B02_0C20, lean: "AArch64.bvMadd", arity: Madd, width: 64 }, // MADD x0,x1,x2,x3
        OpCase { name: "msub", word: 0x9B02_8C20, lean: "AArch64.bvMsub", arity: Madd, width: 64 }, // MSUB x0,x1,x2,x3
        // ---- 32-bit (W) ----
        OpCase { name: "addw", word: 0x0B02_0020, lean: "AArch64.bvAddW", arity: Bin2, width: 32 },
        OpCase { name: "subw", word: 0x4B02_0020, lean: "AArch64.bvSubW", arity: Bin2, width: 32 },
        OpCase { name: "mulw", word: 0x1B02_7C20, lean: "AArch64.bvMulW", arity: Bin2, width: 32 },
        OpCase { name: "andw", word: 0x0A02_0020, lean: "AArch64.bvAndW", arity: Bin2, width: 32 },
        OpCase { name: "orrw", word: 0x2A02_0020, lean: "AArch64.bvOrW",  arity: Bin2, width: 32 },
        OpCase { name: "eorw", word: 0x4A02_0020, lean: "AArch64.bvXorW", arity: Bin2, width: 32 },
        OpCase { name: "lslvw", word: 0x1AC2_2020, lean: "AArch64.bvShlW", arity: Bin2, width: 32 },
        OpCase { name: "lsrvw", word: 0x1AC2_2420, lean: "AArch64.bvLshrW", arity: Bin2, width: 32 },
        OpCase { name: "asrvw", word: 0x1AC2_2820, lean: "AArch64.bvAsrW", arity: Bin2, width: 32 },
        OpCase { name: "negw", word: 0x4B01_03E0, lean: "AArch64.bvNegW", arity: Un1,  width: 32 },
        OpCase { name: "mvnw", word: 0x2A21_03E0, lean: "AArch64.bvNotW", arity: Un1,  width: 32 },
        OpCase { name: "udivw", word: 0x1AC2_0820, lean: "AArch64.bvUdivW", arity: Bin2, width: 32 },
        OpCase { name: "sdivw", word: 0x1AC2_0C20, lean: "AArch64.bvSdivW", arity: Bin2, width: 32 },
        OpCase { name: "maddw", word: 0x1B02_0C20, lean: "AArch64.bvMaddW", arity: Madd, width: 32 },
        OpCase { name: "msubw", word: 0x1B02_8C20, lean: "AArch64.bvMsubW", arity: Madd, width: 32 },
    ]
}

// ---- deterministic input generation: edges + fixed-seed xorshift spread. ----

struct XorShift(u64);
impl XorShift {
    fn new(seed: u64) -> Self {
        XorShift(seed | 1)
    }
    fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
}

const EDGES: &[u64] = &[
    0,
    1,
    2,
    3,
    4,
    63,
    64,
    65,
    0xFF,
    0x8000_0000,
    0xFFFF_FFFF,
    0x1_0000_0000,
    0x7FFF_FFFF_FFFF_FFFF,
    0x8000_0000_0000_0000,
    0xFFFF_FFFF_FFFF_FFFF,
];

/// Build (a, b) pairs: full edge x edge, edges x random, random x random.
fn input_pairs(seed: u64) -> Vec<(u64, u64)> {
    let mut rng = XorShift::new(seed);
    let mut pairs = Vec::new();
    for &a in EDGES {
        for &b in EDGES {
            pairs.push((a, b));
        }
    }
    for &e in EDGES {
        for _ in 0..20 {
            pairs.push((e, rng.next_u64()));
            pairs.push((rng.next_u64(), e));
        }
    }
    while pairs.len() < 1200 {
        pairs.push((rng.next_u64(), rng.next_u64()));
    }
    pairs
}

/// Lean-side value for a case, given (a, b) seeded into X1, X2 (and X3=a for madd).
fn lean_value(lean: &LeanIsa, case: &OpCase, a: u64, b: u64) -> u128 {
    match case.arity {
        // For Bin2 the Lean defs canonicalize their inputs (W-forms mask to 32),
        // so feeding the full 64-bit register value is correct: bvAddW etc. take
        // (a % 2^32). For shifts the def masks the amount; for X-forms the inputs
        // are already canonical 64-bit. We pass the raw register values.
        Arity::Bin2 => lean.eval2(case.lean, u128::from(a), u128::from(b)),
        Arity::Un1 => lean.eval1(case.lean, u128::from(a)),
        // MADD/MSUB: Lean op(ra, rn, rm); we seed X1=rn=a, X2=rm=b, X3=ra=a.
        Arity::Madd => lean.eval3(case.lean, u128::from(a), u128::from(a), u128::from(b)),
    }
}

/// Rust-side value for a case, seeding X1=a, X2=b, X3=a (for madd).
fn machine_value(case: &OpCase, a: u64, b: u64) -> u128 {
    match case.arity {
        Arity::Bin2 => run_machine_sem(case.word, &[(1, a), (2, b)], 0, case.width),
        Arity::Un1 => run_machine_sem(case.word, &[(1, a)], 0, case.width),
        Arity::Madd => run_machine_sem(case.word, &[(1, a), (2, b), (3, a)], 0, case.width),
    }
}

// ===========================================================================
//  THE DIFFERENTIAL: trust_machine_sem == Lean ISA over the covered opcodes.
//  GRADE: [VALIDATED] / execution-validated equivalence (sampled).
// ===========================================================================

#[test]
fn machine_sem_matches_lean_isa_over_covered_opcodes() {
    let lean = LeanIsa::new();
    let cases = covered_ops();
    let mut report: Vec<(&str, usize, usize)> = Vec::new();

    for (i, case) in cases.iter().enumerate() {
        let pairs = input_pairs(0xA1u64.wrapping_mul(i as u64 + 1).wrapping_add(0xDEAD_BEEF));
        let mut mism: Vec<(u64, u64, u128, u128)> = Vec::new();
        for &(a, b) in &pairs {
            let rust = machine_value(case, a, b);
            let lean_v = lean_value(&lean, case, a, b);
            if rust != lean_v {
                mism.push((a, b, rust, lean_v));
            }
        }
        report.push((case.name, pairs.len(), mism.len()));
        assert!(
            mism.is_empty(),
            "op {} ({}): trust_machine_sem DISAGREES with Lean ISA def {} at {} of {} sampled \
             inputs (a, b, rust, lean): {:?}",
            case.name,
            case.word,
            case.lean,
            mism.len(),
            pairs.len(),
            &mism[..mism.len().min(8)]
        );
    }

    for (name, n, m) in &report {
        println!("op {name}: {n} samples, {m} mismatches (machine_sem == lean_isa)");
    }
    let total: usize = report.iter().map(|(_, n, _)| n).sum();
    println!(
        "RUNG 4 [VALIDATED]/differential: {total} samples across {} covered opcodes, \
         trust_machine_sem == aarch64_isa.lean on ALL.",
        cases.len()
    );
}

// ===========================================================================
//  NEGATIVE CONTROL: inject a WRONG machine-sem effect for one opcode and prove
//  the differential CATCHES it. We decode the real ADD word (route-R = add) but
//  compare it against the Lean SUB def (route-L = sub) — i.e. a flipped semantic
//  arm. The differential MUST report a mismatch on at least one sampled input.
// ===========================================================================

#[test]
fn negative_control_flipped_add_sub_arm_is_detected() {
    let lean = LeanIsa::new();
    let pairs = input_pairs(0x1234_5678);

    let add_word = 0x8B02_0020u32; // ADD x0,x1,x2
    let sub_word = 0xCB02_0020u32; // SUB x0,x1,x2

    // Direction A: a WRONG machine-sem EFFECT. trust_machine_sem genuinely
    // computes the SUB effect (route-R = decode+effects of the SUB word) but the
    // gate expects the ADD opcode's Lean semantics (route-L = bvAdd). This is
    // EXACTLY the shape of a model bug where the machine-sem arm for `add` were
    // mis-wired to subtract: the differential MUST catch it.
    let mut caught_wrong_effect = false;
    // Direction B: a WRONG Lean pairing (real ADD word vs Lean bvSub) — the dual.
    let mut caught_wrong_lean = false;
    // Sanity: the correctly-paired ADD must agree everywhere.
    let mut sanity_add_agrees = true;

    for &(a, b) in &pairs {
        let rust_add = run_machine_sem(add_word, &[(1, a), (2, b)], 0, 64);
        let rust_sub = run_machine_sem(sub_word, &[(1, a), (2, b)], 0, 64);
        let lean_add = lean.eval2("AArch64.bvAdd", u128::from(a), u128::from(b));
        let lean_sub = lean.eval2("AArch64.bvSub", u128::from(a), u128::from(b));

        if rust_add != lean_add {
            sanity_add_agrees = false;
        }
        if rust_sub != lean_add {
            caught_wrong_effect = true; // wrong machine-sem effect (sub) vs correct Lean (add)
        }
        if rust_add != lean_sub {
            caught_wrong_lean = true; // correct machine-sem (add) vs wrong Lean (sub)
        }
    }

    assert!(
        sanity_add_agrees,
        "sanity: the real ADD word must agree with the Lean bvAdd def everywhere"
    );
    assert!(
        caught_wrong_effect,
        "NEGATIVE CONTROL FAILED: a flipped machine-sem EFFECT (SUB computed where ADD expected) \
         was NOT detected against the Lean bvAdd def — the differential would be toothless."
    );
    assert!(
        caught_wrong_lean,
        "NEGATIVE CONTROL FAILED: the dual (ADD effect vs Lean bvSub) was NOT detected."
    );
    println!(
        "negative control: a flipped machine-sem effect (add<->sub) is detected as a \
         Rust-vs-Lean mismatch in BOTH directions."
    );
}
