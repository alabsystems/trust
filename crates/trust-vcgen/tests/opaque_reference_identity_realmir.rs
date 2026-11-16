// Real-MIR cover for OPAQUE-REF-ID-1: the opaque-REFERENCE half of the "one solver symbol
// for many runtime values" class (OPAQUE-SCALAR-ID-1 closed the integer half), plus
// regression pins for the integer half.
//
//   pub fn q1_int_to_ptr(x: usize, y: usize) {       // safe, non-generic
//       let p = x as *const u8;
//       let q = y as *const u8;
//       if p != q { panic!("Q1 recovered pointers differ"); }   // q1_int_to_ptr(1, 2) panics
//   }
//
// THE DEFECT (CLOSED). The extractor lowers `usize as *const T`
// (`CastKind::PointerWithExposedProvenance`, `trust-mir-extract/src/convert.rs`) to
// `Rvalue::Use(Constant(ConstValue::OpaqueConst))`, and trust-vcgen's renderer
// (`operand_to_formula_with_array_ctx`, its `_ =>` arm) spelled EVERY `OpaqueConst` — and
// every `UnitVariantRef` / `StructScalarFieldsRef` — as the one symbol `__unknown_const`.
// The panic row above was `p == __unknown_const ∧ q == __unknown_const ∧ p != q`: UNSAT,
// PROVED, and `certify_vc` certified it, on fix/opaque-scalar-identity 2860070ef3 and on
// origin/main 41893f5e7c, at -O0 and -O1 with debug assertions. No `UnsupportedMir` row
// accompanies this carrier, so the false proof was not contained at function level:
// `q8_index` / `q9_div` below have no panic call and no unsupported row, and the
// d36c551fa stage2 compiler reported both functions verified (`functions_verified: 2`)
// and ACCEPTED them under `-Ztrust-policy=strict`, `memory-safe` and `certify` (exit 0)
// at -O0 and -O1; run, they panic with "index out of bounds: the len is 4 but the index
// is 9" and "attempt to divide by zero". The stage2 compiler also reported `proved` for
// every panic row below, the native trust-mc lane included (`solver:
// trust-full-verifier`), because that lane replays the vcgen formula's names verbatim.
//
// THE FIX. Every reference carrier (and every `Operand::Unsupported`) carries an
// `OpaqueOrigin` placed at its MIR site on load, and every renderer names it
// `__trust_opaque_ref_b{block}_s{stmt}_o{slot}` (`ConstValue::unmodeled_value_smt_var_name`).
// Two different sites are two terms; one site is tied to its own copies, so the controls
// below still prove. Found by the adversarial verification of 2860070ef3 (branch
// verify/opaque-reference-identity-holes 6edc639131, whose failing tests these are).
//
// Fixtures: `tests/fixtures/opaque_reference_identity/{name}_{o0,o1d}.json`, extracted by
// the d36c551fa stage2 compiler exactly as `opaque_scalar_identity_realmir.rs` documents
//
//   rustc -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-dump=mir-only:<dir> \
//         --edition 2024 --crate-type lib -Copt-level=0 --emit metadata <src>
//   (`o1d`: -Copt-level=1 -Cdebug-assertions=on)
//
// from `q.rs`, `q8.rs`, `vb.rs`, `vb2.rs` and `vb2a.rs` (the round-2 verification of
// 685267f885) beside them, source paths made relative. Each
// `_bug` / `q*` / `r16` function's comment names an input on which it panics; every one
// was run at -O0 and -O3 and panicked, and every control returned normally.
use trust_types::{
    ConstValue, Formula, OPAQUE_REF_SYMBOL_PREFIX, Operand, Rvalue, Statement,
    UNSUPPORTED_OPERAND_SYMBOL_PREFIX, VcKind, VerifiableFunction, VerificationCondition,
    VerificationResult,
};

#[path = "support/test_router.rs"]
mod test_router;

const LEVELS: [&str; 2] = ["o0", "o1d"];

fn load(name: &str, level: &str) -> VerifiableFunction {
    let path = format!(
        "{}/tests/fixtures/opaque_reference_identity/{name}_{level}.json",
        env!("CARGO_MANIFEST_DIR")
    );
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json)
        .unwrap_or_else(|e| panic!("{path}: fixture MIR must deserialize: {e}"))
}

/// Which row of a function is under test.
#[derive(Clone, Copy, Debug)]
enum Row {
    /// The function's one `panic!` / `assert!` panic-call row.
    Panic,
    /// The function's one `IndexOutOfBounds` row.
    Index,
    /// The function's one `DivisionByZero` row.
    DivZero,
}

impl Row {
    fn matches(self, vc: &VerificationCondition) -> bool {
        match (self, &vc.kind) {
            (Row::Panic, VcKind::Assertion { message }) => message.starts_with("panic call"),
            (Row::Index, VcKind::IndexOutOfBounds) => true,
            (Row::DivZero, VcKind::DivisionByZero) => true,
            _ => false,
        }
    }
}

fn router() -> trust_router::Router {
    test_router::deterministic_test_router()
}

fn generate(func: VerifiableFunction) -> Vec<VerificationCondition> {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || trust_vcgen::generate_vcs(&func))
        .expect("spawn")
        .join()
        .expect("generation must not panic")
}

/// The single `row` of `name` at `level`, its verdict, and whether the kernel certifies it.
fn verdict(name: &str, level: &str, row: Row) -> (VerificationCondition, VerificationResult, bool) {
    verdict_of(load(name, level), &format!("{name} {level} {row:?}"), row)
}

/// [`verdict`] for an already-loaded (possibly edited) function.
fn verdict_of(
    func: VerifiableFunction,
    what: &str,
    row: Row,
) -> (VerificationCondition, VerificationResult, bool) {
    let what = what.to_string();
    let vcs: Vec<VerificationCondition> =
        generate(func).into_iter().filter(|vc| row.matches(vc)).collect();
    assert_eq!(vcs.len(), 1, "{what}: exactly one row under test");
    let vc = vcs.into_iter().next().expect("one row");
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
        .expect("verification must not panic")
}

/// Collect every violation instead of stopping at the first, so one run reports the
/// whole set.
fn not_proved_violations(cases: &[(&str, Row)]) -> Vec<String> {
    let mut out = Vec::new();
    for (name, row) in cases {
        for level in LEVELS {
            let (vc, result, certified) = verdict(name, level, *row);
            if matches!(result, VerificationResult::Proved { .. }) || certified {
                out.push(format!(
                    "{name} {level} {row:?}: PROVED={} certified={certified}; formula {:?}",
                    matches!(result, VerificationResult::Proved { .. }),
                    vc.formula
                ));
            }
        }
    }
    out
}

fn assert_none_proved(cases: &[(&str, Row)], what: &str) {
    let violations = not_proved_violations(cases);
    assert!(
        violations.is_empty(),
        "{what}: {} row(s) of programs that panic are PROVED or certified:\n{}",
        violations.len(),
        violations.join("\n")
    );
}

fn assert_all_proved(cases: &[(&str, Row)], what: &str) {
    for (name, row) in cases {
        for level in LEVELS {
            let (vc, result, _) = verdict(name, level, *row);
            assert!(
                matches!(result, VerificationResult::Proved { .. }),
                "{what}: {name} {level} {row:?} is a correct program PROVED on origin/main; \
                 got {result:?}, formula {:?}",
                vc.formula
            );
        }
    }
}

fn var_names(f: &Formula) -> Vec<String> {
    let mut out = Vec::new();
    f.visit(&mut |node| {
        if let Some(name) = node.var_name() {
            out.push(name.to_string());
        }
    });
    out
}

/// CLOSED (OPAQUE-REF-ID-1): the panic row of each recovered-pointer comparison. Was PROVED
/// and certified on 2860070ef3 and on origin/main 41893f5e7c at -O0 and -O1d; each panics.
const RECOVERED_POINTER_PANICS: &[(&str, Row)] = &[
    ("q1_int_to_ptr", Row::Panic),        // (1, 2)
    ("q4_recovered_vs_ref", Row::Panic),  // (&v, 0): a live reference is never null
    ("q6_assert_ptr", Row::Panic),        // (1, 2), assert! form
    ("q7_null_vs_recovered", Row::Panic), // (5): `0 as *const u8` vs `5 as *const u8`
    ("r16_offset", Row::Panic),           // (5): `x` vs `x + 1`
];

/// CLOSED (OPAQUE-REF-ID-1): rows with no panic call and no UnsupportedMir row. Were
/// PROVED; the d36c551fa stage2 compiler reported the functions verified and strict /
/// memory-safe / certify accepted them.
const RECOVERED_POINTER_UNCONTAINED: &[(&str, Row)] = &[
    ("q8_index", Row::Index), // (1, 2, &[0; 4]): index 9 out of bounds
    ("q9_div", Row::DivZero), // (1, 2): divides by zero
];

#[test]
fn recovered_pointer_panic_rows_are_not_proved() {
    assert_none_proved(RECOVERED_POINTER_PANICS, "recovered-pointer panic rows");
}

#[test]
fn recovered_pointer_ties_do_not_discharge_index_or_divisor_rows() {
    assert_none_proved(RECOVERED_POINTER_UNCONTAINED, "uncontained recovered-pointer rows");
}

/// The mechanism, stated directly: two DIFFERENT recovered pointers must not be defined
/// as one solver term. Failed on `__unknown_const` before OPAQUE-REF-ID-1; now each is
/// its own site's `__trust_opaque_ref_*` symbol.
#[test]
fn two_recovered_pointers_are_two_terms() {
    for level in LEVELS {
        let (vc, _, _) = verdict("q1_int_to_ptr", level, Row::Panic);
        let names = var_names(&vc.formula);
        assert!(
            !names.iter().any(|n| n == "__unknown_const"),
            "q1_int_to_ptr {level}: an opaque reference still renders as `__unknown_const`: {:?}",
            vc.formula
        );
        let mut refs: Vec<&String> =
            names.iter().filter(|n| n.starts_with(OPAQUE_REF_SYMBOL_PREFIX)).collect();
        refs.sort();
        refs.dedup();
        assert_eq!(
            refs.len(),
            2,
            "q1_int_to_ptr {level}: `p` and `q` must be two distinct site symbols: {:?}",
            vc.formula
        );
    }
}

/// The same identity holds for EVERY carrier with no modeled value, not only the
/// `usize as *const T` one: on the real `q1_int_to_ptr` body, `p` and `q` are rebuilt as
/// two occurrences of each other reference carrier (`&None`-style `UnitVariantRef`,
/// `&Struct(..)`-style `StructScalarFieldsRef`) and as two `Operand::Unsupported`s with
/// IDENTICAL kind and detail (two `f16` constants are exactly that). Before
/// OPAQUE-REF-ID-1 the first two rendered as `__unknown_const` and the last as
/// `__trust_unsupported_operand_{kind}_{detail}` — one term each — and the panic row
/// `p != q` was PROVED. Now each occurrence is its own site's term.
#[test]
fn every_unmodeled_carrier_kind_is_two_terms_at_two_sites() {
    let carriers: [(&str, fn() -> Operand); 4] = [
        ("opaque_const", || Operand::Constant(ConstValue::opaque_const())),
        ("unit_variant_ref", || {
            Operand::Constant(ConstValue::unit_variant_ref("core::option::Option", 0))
        }),
        ("struct_scalar_fields_ref", || {
            Operand::Constant(ConstValue::struct_scalar_fields_ref(
                "probe::S",
                vec![ConstValue::Uint(7, 8)],
            ))
        }),
        ("unsupported", || {
            Operand::unsupported("Const::F16", "float constant width 16 needs dedicated encoding")
        }),
    ];
    for level in LEVELS {
        for (label, carrier) in carriers {
            let mut func = load("q1_int_to_ptr", level);
            let mut rebuilt = 0;
            for block in &mut func.body.blocks {
                for stmt in &mut block.stmts {
                    if let Statement::Assign { rvalue, .. } = stmt
                        && matches!(
                            rvalue,
                            Rvalue::Use(Operand::Constant(ConstValue::OpaqueConst(_)))
                        )
                    {
                        // Built unplaced, as an in-code pass would; generation places it.
                        *rvalue = Rvalue::Use(carrier());
                        rebuilt += 1;
                    }
                }
            }
            assert_eq!(rebuilt, 2, "{label} {level}: q1 has exactly two recovered pointers");
            let what = format!("q1_int_to_ptr[{label}] {level} Panic");
            let (vc, result, certified) = verdict_of(func, &what, Row::Panic);
            assert!(
                !matches!(result, VerificationResult::Proved { .. }) && !certified,
                "{what}: two occurrences of one carrier kind tied as one value: \
                 {result:?} certified={certified}; formula {:?}",
                vc.formula
            );
            let prefix = if label == "unsupported" {
                UNSUPPORTED_OPERAND_SYMBOL_PREFIX
            } else {
                OPAQUE_REF_SYMBOL_PREFIX
            };
            let mut names: Vec<String> =
                var_names(&vc.formula).into_iter().filter(|n| n.starts_with(prefix)).collect();
            names.sort();
            names.dedup();
            assert_eq!(names.len(), 2, "{what}: two site symbols expected: {:?}", vc.formula);
        }
    }
}

/// Control: a recovered pointer equals its own copy (correct; PROVED on origin/main).
#[test]
fn recovered_pointer_control_still_proves() {
    assert_all_proved(&[("vb_c6_ptr_self", Row::Panic)], "recovered-pointer control");
}

/// PIN (passes on the fix): one MIR site executed on two loop iterations is two values.
/// FAILED (not proved) on the fix and on origin/main; each panics.
#[test]
fn per_execution_sites_never_tie_two_iterations() {
    assert_none_proved(
        &[
            ("vb_l1_prev_addr_bug", Row::Panic),
            ("vb_l2_first_addr_bug", Row::Panic),
            ("vb_l3_prev_bits_bug", Row::Panic),
            ("vb_l4_array_fill_bug", Row::Panic),
            ("vb_l5_last_vs_first_bug", Row::Panic),
            ("vb_l6_two_slots_bug", Row::Panic),
        ],
        "loop-carried site values",
    );
}

/// PIN (passes on the fix): one helper / closure / generic body's site or constant at two
/// call sites. `vb_h4_assoc_bug` (`T::C` vs `U::C` through locals) was PROVED and
/// certified on origin/main.
#[test]
fn helper_closure_and_generic_sites_never_tie() {
    assert_none_proved(
        &[
            ("vb_h1_helper_twice_bug", Row::Panic),
            ("vb_h2_closure_twice_bug", Row::Panic),
            ("vb_h3_generic_size_bug", Row::Panic),
            ("vb_h4_assoc_bug", Row::Panic),
            ("vb_h5_assoc_helper_bug", Row::Panic),
        ],
        "cross-call site values",
    );
}

/// Controls (correct programs PROVED on origin/main): a site's value is tied to its own
/// copies, inside a loop too.
#[test]
fn site_copy_controls_still_prove() {
    assert_all_proved(
        &[
            ("vb_c1_copy_tie", Row::Panic),
            ("vb_c2_loop_copy_tie", Row::Panic),
            ("vb_c7_loop_bits_self", Row::Panic),
        ],
        "site copy controls",
    );
}

/// THE DECLARED LOSSES (correct programs origin/main PROVED and certified only through the
/// shared symbol; measured by the round-2 verification of 685267f885 at -O0/-O1/-O1d).
/// Pinned so a later precision gain shows up here instead of passing silently:
///
/// * `vb_c5_assoc_twice::<T>` — `let a = T::C; let b = T::C; if a != b { panic!() }`. One
///   associated constant read twice is one value, but these fixtures come from the
///   d36c551fa extractor, which mints no constant keys, so each read is its own site.
///   An extractor that keys both reads (`OpaqueOrigin::Const`, same item and generic
///   arguments) ties them again and recovers the proof; that needs a stage build.
/// * `n_c1_two_exposes_same_ptr_ctl(r)` — `r as *const u8 as usize` at two sites. Two
///   expose casts of one pointer are equal, but nothing in the model relates two
///   runtime values minted at two sites (the address-to-integer twin of the declared
///   `(x as *const u8) == (x as *const u8)` cost). Recovering it needs the extractor to
///   keep the cast's source operand.
#[test]
fn declared_proof_losses_are_pinned() {
    for name in ["vb_c5_assoc_twice", "n_c1_two_exposes_same_ptr_ctl"] {
        for level in LEVELS {
            let (vc, result, certified) = verdict(name, level, Row::Panic);
            assert!(
                !matches!(result, VerificationResult::Proved { .. }) && !certified,
                "{name} {level}: the declared loss was recovered (PROVED={} certified={certified}); \
                 if that is a real precision gain, move this case to a control that asserts \
                 PROVED. Formula {:?}",
                matches!(result, VerificationResult::Proved { .. }),
                vc.formula
            );
        }
    }
}
