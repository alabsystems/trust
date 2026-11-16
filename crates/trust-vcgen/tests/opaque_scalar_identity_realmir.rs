// Real-MIR cover for OPAQUE-SCALAR-ID-1: kernel-certified FALSE PROOFS from one solver
// symbol per width, and the identity that closes them.
//
//   pub fn cc_two_addrs(a: &u8, b: &u8) -> usize {     // safe, non-generic
//       let x = a as *const u8 as usize;
//       let y = b as *const u8 as usize;
//       if x != y { panic!("R1 addresses differ"); }    // cc_two_addrs(&1, &2) panics
//       x
//   }
//
// THE DEFECT. The extractor lowers runtime values it does not model (`ptr as usize`,
// `f32 -> u32` / `f64 -> u64`, `[u8; N] -> uN`, `MaybeUninit<uN> -> uN`) and integer
// constants it cannot evaluate in a generic body (`const { size_of::<T>() }`, associated
// consts, `const { N + 1 }`) to `ConstValue::OpaqueScalar { width, signed }`, and every
// renderer named that carrier `__trust_opaque_scalar_u64` — ONE symbol per width. The
// panic row above became `x == S ∧ y == S ∧ x != y`: UNSAT, PROVED, and `certify_vc`
// certified it; the compiler reported `proved` and the native trust-mc lane replayed the
// same shared name. Measured on origin/main 41893f5e7c (2026-10-07), and on 2b946b5458
// before it: 27 panic rows PROVED (26 certified) and 3 overflow rows PROVED, every one
// of them a program that panics (or wraps) when run.
//
// THE FIX. `OpaqueScalar` carries an `origin` (`trust_types::OpaqueOrigin`): the
// operand's MIR site, placed on every body load and at the end of extraction, or — for
// an unevaluated constant the extractor keyed — its item and normalized generic
// arguments. `ConstValue::opaque_scalar_smt_var_name` spells one symbol per origin, so
// two values share a symbol only when they provably are one value.
//
// Fixtures: `tests/fixtures/opaque_scalar_identity/{name}_{o0,o1d}.json`, extracted by
// the d36c551fa stage2 compiler
//
//   rustc -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-dump=mir-only:<dir> \
//         --edition 2024 --crate-type lib -Copt-level=0 --emit metadata <src>
//   (`o1d`: -Copt-level=1 -Cdebug-assertions=on, so rustc's UB checks are present)
//
// from `rr_chc.rs`, `rr_chc_d.rs`, `rr_chc_e.rs` (the hunt) and `cc_rt.rs`,
// `cc_const.rs`, `cc_ovf.rs` (the independent confirmation) beside them, probe source
// paths made relative. Each `_bug`-class function's comment names an input on which it
// panics; the reproductions ran at -O0 and -O3.
use trust_types::{
    BinOp, ConstValue, Formula, OpaqueOrigin, Operand, Rvalue, Statement, VcKind,
    VerifiableFunction, VerificationCondition, VerificationResult,
};

#[path = "support/test_router.rs"]
mod test_router;

const LEVELS: [&str; 2] = ["o0", "o1d"];

fn load(name: &str, level: &str) -> VerifiableFunction {
    let path = format!(
        "{}/tests/fixtures/opaque_scalar_identity/{name}_{level}.json",
        env!("CARGO_MANIFEST_DIR")
    );
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json)
        .unwrap_or_else(|e| panic!("{path}: fixture MIR must deserialize: {e}"))
}

/// Which row of a function is under test.
#[derive(Clone, Copy)]
enum Row {
    /// The function's one `panic!` call row.
    Panic,
    /// The arithmetic-overflow row of `op` at source line `line`.
    Overflow(BinOp, u32),
}

impl Row {
    fn matches(self, vc: &VerificationCondition) -> bool {
        match (self, &vc.kind) {
            (Row::Panic, VcKind::Assertion { message }) => message.starts_with("panic call"),
            (Row::Overflow(op, line), VcKind::ArithmeticOverflow { op: kind_op, .. }) => {
                *kind_op == op && vc.location.line_start == line
            }
            _ => false,
        }
    }
}

/// The deterministic in-process ay router the reproducers were measured with.
fn router() -> trust_router::Router {
    test_router::deterministic_test_router()
}

/// Generate `func`'s VCs on a big stack (debug builds of the generator recurse deeply).
fn generate(func: VerifiableFunction) -> Vec<VerificationCondition> {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || trust_vcgen::generate_vcs(&func))
        .expect("spawn")
        .join()
        .expect("generation must not panic")
}

/// The single `row` of `func`, its verdict, and whether the kernel certifies it. `None`
/// when generation emitted no such row (a declined body).
fn verdict_of(
    func: VerifiableFunction,
    row: Row,
    what: &str,
) -> Option<(VerificationCondition, VerificationResult, bool)> {
    let vcs: Vec<VerificationCondition> =
        generate(func).into_iter().filter(|vc| row.matches(vc)).collect();
    assert!(vcs.len() <= 1, "{what}: at most one such row, got {}", vcs.len());
    let vc = vcs.into_iter().next()?;
    let what = what.to_string();
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let result = router()
                .verify_all(std::slice::from_ref(&vc))
                .into_iter()
                .next()
                .map(|(_, result)| result)
                .unwrap_or_else(|| panic!("{what}: one verdict"));
            let certified = trust_certify::certify_vc(&vc).is_some();
            (vc, result, certified)
        })
        .expect("spawn")
        .join()
        .ok()
}

fn verdict(name: &str, level: &str, row: Row) -> (VerificationCondition, VerificationResult, bool) {
    let what = format!("{name} {level}");
    verdict_of(load(name, level), row, &what)
        .unwrap_or_else(|| panic!("{what}: the row under test must be generated"))
}

fn assert_not_proved(name: &str, level: &str, row: Row) {
    let (vc, result, certified) = verdict(name, level, row);
    assert!(
        !matches!(result, VerificationResult::Proved { .. }) && !certified,
        "{name} {level}: a program that panics must be neither PROVED nor certified; \
         got {result:?}, certified={certified}, formula {:?}",
        vc.formula
    );
}

/// Every free variable name of `f`.
fn var_names(f: &Formula) -> Vec<String> {
    let mut out = Vec::new();
    f.visit(&mut |node| {
        if let Some(name) = node.var_name() {
            out.push(name.to_string());
        }
    });
    out
}

/// A width-only opaque symbol: the pre-fix spelling (`__trust_opaque_scalar_u64`) or an
/// unplaced one. Neither may reach a formula built from a loaded body.
fn is_width_only_opaque(name: &str) -> bool {
    let Some(rest) = name.strip_prefix(trust_types::OPAQUE_SCALAR_SYMBOL_PREFIX) else {
        return false;
    };
    let rest = rest.strip_prefix(['u', 'i']).unwrap_or(rest);
    rest.ends_with("_unplaced") || (!rest.is_empty() && rest.bytes().all(|b| b.is_ascii_digit()))
}

/// THE FALSE PROOFS (panic rows), closed. PROVED on origin/main 41893f5e7c, every one
/// certified except `align_check_into_user`; each function panics when run.
const PANIC_FALSE_PROOFS: &[&str] = &[
    // runtime values (hunt `rr_chc_e.rs`, `rr_chc_d.rs`)
    "two_addrs",
    "float_bits",
    "byte_packs",
    "mu_vs_addr",
    "addr_vs_size",
    "check_into_user",
    "align_check_into_user",
    // unevaluated constants (hunt `rr_chc.rs`, `rr_chc_d.rs`)
    "user_sizes_alias",
    "align_vs_size",
    "const_expr_nm",
    "assoc_consts",
    "const_fn_result",
    "user_size_vs_check",
    "u32_assoc",
    "nested_sizes",
    // independent confirmation (`cc_rt.rs`, `cc_const.rs`)
    "cc_two_addrs",
    "cc_assert_same_addr",
    "cc_f32_bits",
    "cc_f64_vs_addr",
    "cc_bytes",
    "cc_mu_vs_f64",
    "cc_addr_vs_size",
    "cc_k_sizes",
    "cc_k_align_size",
    "cc_k_cexpr",
    "cc_k_nested",
    "cc_k_into_user",
];

/// THE FALSE PROOFS (overflow rows, `cc_ovf.rs`), closed: PROVED on origin/main; each
/// subtraction underflows (debug panics, release wraps).
const OVERFLOW_FALSE_PROOFS: &[(&str, Row)] = &[
    ("cc_span_rev", Row::Overflow(BinOp::Sub, 9)),
    ("cc_bits_sub", Row::Overflow(BinOp::Sub, 16)),
    ("cc_k_sub", Row::Overflow(BinOp::Sub, 23)),
];

#[test]
fn runtime_value_false_proofs_are_closed() {
    for name in &PANIC_FALSE_PROOFS[..7] {
        for level in LEVELS {
            assert_not_proved(name, level, Row::Panic);
        }
    }
}

#[test]
fn unevaluated_constant_false_proofs_are_closed() {
    for name in &PANIC_FALSE_PROOFS[7..15] {
        for level in LEVELS {
            assert_not_proved(name, level, Row::Panic);
        }
    }
}

#[test]
fn confirmation_false_proofs_are_closed() {
    for name in &PANIC_FALSE_PROOFS[15..] {
        for level in LEVELS {
            assert_not_proved(name, level, Row::Panic);
        }
    }
    for (name, row) in OVERFLOW_FALSE_PROOFS {
        for level in LEVELS {
            assert_not_proved(name, level, *row);
        }
    }
}

/// No row of any fixture names a width-only opaque symbol: every occurrence carries its
/// own identity once the body is loaded.
#[test]
fn no_formula_names_a_width_only_opaque_symbol() {
    let dir = format!("{}/tests/fixtures/opaque_scalar_identity", env!("CARGO_MANIFEST_DIR"));
    let mut checked = 0usize;
    let mut entries: Vec<_> = std::fs::read_dir(&dir)
        .expect("fixture dir")
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|e| e == "json"))
        .collect();
    entries.sort();
    for path in entries {
        let func: VerifiableFunction =
            serde_json::from_str(&std::fs::read_to_string(&path).expect("read")).expect("parse");
        assert!(
            !func.body.opaque_values_need_placement(),
            "{}: a loaded body is placed",
            path.display()
        );
        for vc in generate(func) {
            for name in var_names(&vc.formula) {
                assert!(
                    !is_width_only_opaque(&name),
                    "{}: {:?} names width-only symbol {name}",
                    path.display(),
                    vc.kind
                );
            }
            checked += 1;
        }
    }
    assert!(checked > 0);
}

/// Programs main already refuted or declined stay unproved: the fail-closed paths are
/// not disturbed (`i64_assoc`/`cc_k_i64` are declined as MalformedTrustIr, so they may
/// have no panic row at all).
#[test]
fn refuted_and_declined_shapes_stay_unproved() {
    for name in ["cg_len", "cc_ctl_param", "cc_k_param_ctl", "one_addr", "i64_assoc", "cc_k_i64"] {
        for level in LEVELS {
            let what = format!("{name} {level}");
            if let Some((vc, result, certified)) = verdict_of(load(name, level), Row::Panic, &what)
            {
                assert!(
                    !matches!(result, VerificationResult::Proved { .. }) && !certified,
                    "{what}: must stay unproved; got {result:?} on {:?}",
                    vc.formula
                );
            }
        }
    }
}

/// Correct programs that remain REFUTED. These are precision gaps, not soundness bugs, and
/// the fix does not claim them; it does change WHY they fail, which is what this pins.
///
/// * `span_nonempty` / `cc_span` (the end of a 4-byte array is never its start): main's
///   counterexample was `s = e = S`, both addresses the one shared symbol. Now `s` and `e`
///   are two distinct symbols and the row fails only because `wrapping_add(4)` on an
///   address is not modeled.
/// * `user_sizes_alias` / `cc_k_succ` `a + 1` (`a = size_of::<T>()`): fails with
///   `a = 2^64 - 1`, impossible since a size is at most `isize::MAX`. The carrier has no
///   range bound; identity does not give it one.
#[test]
fn known_false_refutations_are_pinned_with_distinct_symbols() {
    for name in ["span_nonempty", "cc_span"] {
        for level in LEVELS {
            let (vc, result, _) = verdict(name, level, Row::Panic);
            assert!(
                matches!(result, VerificationResult::Failed { .. }),
                "{name} {level}: known false refutation moved; got {result:?}. If it now \
                 proves, check the proof is certified and update this pin."
            );
            let mut opaque: Vec<String> = var_names(&vc.formula)
                .into_iter()
                .filter(|n| n.starts_with(trust_types::OPAQUE_SCALAR_SYMBOL_PREFIX))
                .collect();
            opaque.sort();
            opaque.dedup();
            assert!(
                opaque.len() >= 2,
                "{name} {level}: the two addresses must be two symbols, got {opaque:?}"
            );
        }
    }
    for (name, line) in [("user_sizes_alias", 34), ("cc_k_succ", 119)] {
        for level in LEVELS {
            let (_, result, _) = verdict(name, level, Row::Overflow(BinOp::Add, line));
            assert!(
                matches!(result, VerificationResult::Failed { .. }),
                "{name} {level}: known false refutation (no size_of range bound) moved; \
                 got {result:?}"
            );
        }
    }
}

/// THE KNOWN LOSS. `cc_span`'s `e - s` overflow row: main PROVED and certified it only
/// because `e` and `s` were the one shared symbol (`x - x`). The program is correct
/// (`e = s + 4`), but nothing in the model relates the two addresses, so the row now
/// fails. Pinned so a later precision gain is visible.
#[test]
fn cc_span_subtraction_is_the_known_proof_loss() {
    for level in LEVELS {
        let (_, result, certified) = verdict("cc_span", level, Row::Overflow(BinOp::Sub, 106));
        assert!(
            !matches!(result, VerificationResult::Proved { .. }) && !certified,
            "cc_span {level}: expected the measured loss, got {result:?}"
        );
    }
}

/// The two whole-rvalue opaque assignments of `cc_two_addrs` (`x = a as usize`,
/// `y = b as usize`), as `(block, stmt)`.
fn address_assignments(func: &VerifiableFunction) -> Vec<(usize, usize)> {
    let mut out = Vec::new();
    for (b, block) in func.body.blocks.iter().enumerate() {
        for (s, stmt) in block.stmts.iter().enumerate() {
            if let Statement::Assign {
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::OpaqueScalar { .. })),
                ..
            } = stmt
            {
                out.push((b, s));
            }
        }
    }
    out
}

fn panic_verdict(func: VerifiableFunction, what: &str) -> (VerificationResult, bool) {
    let (_, result, certified) =
        verdict_of(func, Row::Panic, what).unwrap_or_else(|| panic!("{what}: panic row"));
    (result, certified)
}

/// WHAT IDENTITY KEEPS, on the real `cc_two_addrs` body: a value tied by a copy, or two
/// occurrences of the same keyed constant, still prove `x == y`; two different keys
/// never do.
#[test]
fn identity_keeps_true_ties_and_never_invents_one() {
    for level in LEVELS {
        let base = load("cc_two_addrs", level);
        let sites = address_assignments(&base);
        assert_eq!(sites.len(), 2, "cc_two_addrs {level}: two exposed addresses");
        let (first, second) = (sites[0], sites[1]);
        let Statement::Assign { place: x, .. } = &base.body.blocks[first.0].stmts[first.1] else {
            unreachable!()
        };
        let x = x.clone();

        // `y = x`: one value, so `x != y` is unreachable.
        let mut copied = base.clone();
        let Statement::Assign { rvalue, .. } = &mut copied.body.blocks[second.0].stmts[second.1]
        else {
            unreachable!()
        };
        *rvalue = Rvalue::Use(Operand::Copy(x));
        let (result, certified) = panic_verdict(copied, &format!("copy {level}"));
        assert!(
            matches!(result, VerificationResult::Proved { .. }) && certified,
            "cc_two_addrs {level}: a copied value is still one value; got {result:?}"
        );

        let keyed = |k1: &str, k2: &str| {
            let mut f = base.clone();
            for ((b, s), key) in [(first, k1), (second, k2)] {
                let Statement::Assign {
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::OpaqueScalar { origin, .. })),
                    ..
                } = &mut f.body.blocks[b].stmts[s]
                else {
                    unreachable!()
                };
                *origin = OpaqueOrigin::Const { key: key.to_string() };
            }
            f
        };
        let (result, certified) = panic_verdict(keyed("K", "K"), &format!("same key {level}"));
        assert!(
            matches!(result, VerificationResult::Proved { .. }) && certified,
            "cc_two_addrs {level}: one keyed constant read twice is one value; got {result:?}"
        );
        let (result, certified) = panic_verdict(keyed("K1", "K2"), &format!("two keys {level}"));
        assert!(
            !matches!(result, VerificationResult::Proved { .. }) && !certified,
            "cc_two_addrs {level}: two different keys must never be tied; got {result:?}"
        );
    }
}

/// B' (latent on the CHC-carry branch): rustc's alignment check follows projections, so
/// one pointer local is checked against `align_of::<T>()` for `&(*p).v` and against
/// `align_of::<S<T>>()` for `(*p).flag`. Each check's `ALIGN - 1` constant must be its own
/// symbol — never one per pointer local, never one per width.
#[test]
fn alignment_checks_of_one_pointer_keep_distinct_constants() {
    let func = load("field_vs_whole", "o1d");
    let mut names = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign {
                rvalue:
                    Rvalue::BinaryOp(
                        BinOp::Sub,
                        Operand::Constant(ConstValue::OpaqueScalar { width, signed, origin }),
                        _,
                    ),
                ..
            } = stmt
            {
                names.push(ConstValue::opaque_scalar_smt_var_name(*width, *signed, origin));
            }
        }
    }
    assert!(names.len() >= 2, "field_vs_whole: two alignment checks, got {names:?}");
    let mut unique = names.clone();
    unique.sort();
    unique.dedup();
    assert_eq!(unique.len(), names.len(), "each alignment constant is its own symbol: {names:?}");
}
