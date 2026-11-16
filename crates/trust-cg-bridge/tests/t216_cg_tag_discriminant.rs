// t216_cg_tag_discriminant.rs — a flat enum's tag slot holds the DECLARED
// discriminant in the MIR codegen lane (`lower.rs`), and executes that way.
//
// Trust (ticket 216 cg-bridge): the verification bridge's fix (9b600982ec) made
// a flat enum's `__tag` hold `Ty::variant_tag` — the decoded declared
// discriminant — instead of the variant index. The codegen twin in
// `trust-cg-bridge/src/lower.rs` still wrote the INDEX, and here that is a
// MISCOMPILE, not a proof gap: MIR's `SwitchInt` over `discriminant(e)` compares
// against the DECLARED values, so `enum E { A = 5, B = 9 }` built as `E::B`
// stored `1` and `match e { E::B => .. }` took the wrong arm. Three sites:
//
//   * `AggregateKind::Adt` construction wrote the index, and only when field 0
//     was spelled `tag` — the extractor's `__tag` spelling wrote NO tag at all;
//   * `SetDiscriminant` wrote the index;
//   * `Rvalue::Discriminant` loaded an `I64` from field 0 whatever the tag
//     field's index, width and sign.
//
// Every executing test here lowers a `VerifiableFunction` through the real
// backend, emits a Mach-O object, links it against a C driver and runs it on
// the host CPU (aarch64-apple-darwin; elsewhere the native step is skipped and
// says so). The structural and fail-closed pins below them need no host.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fs;
use std::process::Command;

use trust_cg_bridge::codegen_backend::TrustCgCodegenBackend;
use trust_cg_lower::function::Function as LirFunction;
use trust_cg_lower::instructions::Opcode;
use trust_cg_lower::types::Type as LirType;
use trust_types::{
    AdtKind, AggregateKind, BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place,
    Projection, Rvalue, SourceSpan, Statement, Terminator, Ty, VariantDef, VerifiableBody,
    VerifiableFunction,
};

// ---------------------------------------------------------------------------
// Shapes.
// ---------------------------------------------------------------------------

/// A flat enum `Ty::Adt` with one tag slot `tag_name: tag_ty` and a variant
/// descriptor carrying the DECLARED (decoded) discriminants.
fn flat_enum(name: &str, tag_name: &str, tag_ty: Ty, discriminants: &[(&str, i128)]) -> Ty {
    Ty::Adt {
        adt_kind: Some(AdtKind::Enum),
        layout: None,
        name: name.into(),
        fields: vec![(tag_name.to_string(), tag_ty)].into(),
        variants: discriminants
            .iter()
            .map(|(variant, discriminant)| VariantDef {
                name: (*variant).into(),
                discriminant: *discriminant,
                fields: vec![],
            })
            .collect::<Vec<_>>()
            .into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    }
}

/// `enum E { A = 5, B = 9 }` (default repr: the discriminant type is `isize`).
fn enum_e(tag_name: &str) -> Ty {
    flat_enum("t216::E", tag_name, Ty::i64(), &[("A", 5), ("B", 9)])
}

/// `enum C { A, B }`: discriminants equal the indices — the control.
fn enum_c(tag_name: &str) -> Ty {
    flat_enum("t216::C", tag_name, Ty::i64(), &[("A", 0), ("B", 1)])
}

/// `#[repr(i8)] enum N { N = -1, P = 5 }` with a tag slot of `tag_ty`.
fn enum_n(tag_ty: Ty) -> Ty {
    flat_enum("t216::N", "__tag", tag_ty, &[("N", -1), ("P", 5)])
}

/// `#[repr(u8)] enum U { A = 0, B = 200 }`: 200 must zero-extend, never read -56.
fn enum_u() -> Ty {
    flat_enum("t216::U", "__tag", Ty::u8(), &[("A", 0), ("B", 200)])
}

fn adt_name(ty: &Ty) -> String {
    match ty {
        Ty::Adt { name, .. } => name.clone(),
        other => panic!("an ADT, got {other:?}"),
    }
}

fn build(enum_ty: &Ty, variant: usize) -> Statement {
    Statement::Assign {
        place: Place::local(1),
        rvalue: Rvalue::Aggregate(
            AggregateKind::Adt { name: adt_name(enum_ty), variant, active_field: None, args: None },
            vec![],
        ),
        span: SourceSpan::default(),
    }
}

fn function(name: &str, locals: Vec<Ty>, blocks: Vec<BasicBlock>) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("t216::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: locals
                .into_iter()
                .enumerate()
                .map(|(index, ty)| LocalDecl { index, ty, name: None })
                .collect(),
            blocks,
            arg_count: 0,
            return_ty: Ty::u64(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// ```text
/// fn name() -> u64 {
///     let e = <enum_ty>::<variant>;          // Aggregate
///     [SetDiscriminant(e, then)]             // when `set_to` is Some
///     match discriminant(e) as <discr_ty> { arm_0 => v_0, .., _ => default }
/// }
/// ```
/// `arms` carry MIR's labels: the zero-extended bit pattern at `discr_ty`'s width.
fn switch_on_discriminant(
    name: &str,
    enum_ty: &Ty,
    variant: usize,
    set_to: Option<usize>,
    discr_ty: Ty,
    arms: &[(u128, u64)],
    default: u64,
) -> VerifiableFunction {
    let mut stmts = vec![build(enum_ty, variant)];
    if let Some(variant_index) = set_to {
        stmts.push(Statement::SetDiscriminant { place: Place::local(1), variant_index });
    }
    stmts.push(Statement::Assign {
        place: Place::local(2),
        rvalue: Rvalue::Discriminant(Place::local(1)),
        span: SourceSpan::default(),
    });
    let ret = |value: u64, id: usize| BasicBlock {
        id: BlockId(id),
        stmts: vec![Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(u128::from(value), 64))),
            span: SourceSpan::default(),
        }],
        terminator: Terminator::Return,
    };
    let mut blocks = vec![BasicBlock {
        id: BlockId(0),
        stmts,
        terminator: Terminator::SwitchInt {
            discr: Operand::Copy(Place::local(2)),
            targets: arms
                .iter()
                .enumerate()
                .map(|(i, (label, _))| (*label, BlockId(i + 1)))
                .collect(),
            otherwise: BlockId(arms.len() + 1),
            exhaustive_enum_unreachable: false,
            span: SourceSpan::default(),
        },
    }];
    for (i, (_, value)) in arms.iter().enumerate() {
        blocks.push(ret(*value, i + 1));
    }
    blocks.push(ret(default, arms.len() + 1));
    function(name, vec![Ty::u64(), enum_ty.clone(), discr_ty], blocks)
}

/// `fn name() -> u64 { discriminant(<enum_ty>::<variant>) as u64 }` — the read
/// value itself, widened by Rust's `as` rule for `discr_ty`.
fn discriminant_as_u64(
    name: &str,
    enum_ty: &Ty,
    variant: usize,
    discr_ty: Ty,
) -> VerifiableFunction {
    let stmts = vec![
        build(enum_ty, variant),
        Statement::Assign {
            place: Place::local(2),
            rvalue: Rvalue::Discriminant(Place::local(1)),
            span: SourceSpan::default(),
        },
        Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Cast(Operand::Copy(Place::local(2)), Ty::u64()),
            span: SourceSpan::default(),
        },
    ];
    let blocks = vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }];
    function(name, vec![Ty::u64(), enum_ty.clone(), discr_ty], blocks)
}

// ---------------------------------------------------------------------------
// Native execution.
// ---------------------------------------------------------------------------

fn backend() -> TrustCgCodegenBackend {
    TrustCgCodegenBackend::host()
}

/// Lower every probe, emit one object per probe, link them against a C driver that prints
/// each `name value` line, run it, and compare every value with the Rust
/// semantics in `probes`. All mismatches are reported together.
fn run_native(probes: &[(VerifiableFunction, u64)]) {
    let lirs: Vec<LirFunction> = probes
        .iter()
        .map(|(f, _)| {
            backend().lower_function(f).unwrap_or_else(|e| panic!("{} must lower: {e:?}", f.name))
        })
        .collect();
    if !cfg!(all(target_os = "macos", target_arch = "aarch64")) {
        eprintln!("SKIP native execution: requires an aarch64-apple-darwin host");
        return;
    }
    let objects = backend().emit_objects(&lirs).expect("emit the probe objects");
    let directory = tempfile::TempDir::new().expect("temporary link directory");
    let driver_path = directory.path().join("driver.c");
    let executable_path = directory.path().join("t216");
    let mut object_paths = Vec::new();
    for (name, object) in objects {
        let path = directory.path().join(format!("{name}.o"));
        fs::write(&path, object).expect("write object");
        object_paths.push(path);
    }
    let mut decls = String::new();
    let mut calls = String::new();
    for (f, _) in probes {
        decls.push_str(&format!("extern uint64_t {}(void);\n", f.name));
        calls.push_str(&format!("  printf(\"{0} %llu\\n\", (unsigned long long){0}());\n", f.name));
    }
    fs::write(
        &driver_path,
        format!(
            "#include <stdint.h>\n#include <stdio.h>\n{decls}\
             int main(void) {{\n{calls}  return 0;\n}}\n"
        ),
    )
    .expect("write C driver");
    let linked = Command::new("cc")
        .arg(&driver_path)
        .args(&object_paths)
        .arg("-o")
        .arg(&executable_path)
        .output()
        .expect("invoke cc");
    assert!(
        linked.status.success(),
        "native link failed: {}",
        String::from_utf8_lossy(&linked.stderr)
    );
    let ran = Command::new(&executable_path).output().expect("run the linked probes");
    assert!(ran.status.success(), "the probe driver failed: {:?}", ran.status);
    let stdout = String::from_utf8_lossy(&ran.stdout);
    let got: Vec<(String, u64)> = stdout
        .lines()
        .map(|line| {
            let (name, value) = line.split_once(' ').expect("`name value`");
            (name.to_string(), value.parse().expect("u64"))
        })
        .collect();
    assert_eq!(got.len(), probes.len(), "one line per probe: {stdout}");
    let mismatches: Vec<String> = probes
        .iter()
        .zip(&got)
        .filter(|((_, want), (_, value))| value != want)
        .map(|((f, want), (_, value))| format!("{}() = {value}, Rust says {want}", f.name))
        .collect();
    assert!(
        mismatches.is_empty(),
        "the emitted code disagrees with Rust:\n  {}",
        mismatches.join("\n  ")
    );
}

// ---------------------------------------------------------------------------
// Executing tests.
// ---------------------------------------------------------------------------

/// `match e { E::B => 100, E::A => 200 }` on `enum E { A = 5, B = 9 }`, whose MIR
/// switches on the DECLARED values 9 and 5. On main: `E::B` stored its index 1
/// (field spelled `tag`) or no tag at all (the extractor's `__tag`), so neither
/// arm matched.
#[test]
fn declared_discriminants_route_the_switch() {
    let arms = [(9, 100), (5, 200)];
    let mut probes = Vec::new();
    for (spelling, tag_name) in [("tag", "tag"), ("dunder", "__tag")] {
        let e = enum_e(tag_name);
        probes.push((
            switch_on_discriminant(
                &format!("e_b_{spelling}"),
                &e,
                1,
                None,
                Ty::isize(),
                &arms,
                300,
            ),
            100,
        ));
        probes.push((
            switch_on_discriminant(
                &format!("e_a_{spelling}"),
                &e,
                0,
                None,
                Ty::isize(),
                &arms,
                300,
            ),
            200,
        ));
        probes.push((discriminant_as_u64(&format!("e_b_value_{spelling}"), &e, 1, Ty::isize()), 9));
    }
    run_native(&probes);
}

/// `#[repr(i8)] enum N { N = -1, P = 5 }`: MIR's label for `N::N` is 255 (the
/// zero-extended i8 pattern), and `discriminant(N::N) as u64` is `u64::MAX` (an
/// i8 widens by sign). Both tag-slot widths: the i8 slot a layout-faithful shape
/// carries, and the i64 slot the MIR extractor mints for every repr (the read
/// truncates it to the i8 discriminant).
#[test]
fn a_negative_repr_i8_tag_is_written_read_and_widened_by_sign() {
    let arms = [(255, 100), (5, 200)];
    let mut probes = Vec::new();
    for (slot, tag_ty) in [("i8slot", Ty::i8()), ("i64slot", Ty::i64())] {
        let n = enum_n(tag_ty);
        probes.push((
            switch_on_discriminant(&format!("n_n_{slot}"), &n, 0, None, Ty::i8(), &arms, 300),
            100,
        ));
        probes.push((
            switch_on_discriminant(&format!("n_p_{slot}"), &n, 1, None, Ty::i8(), &arms, 300),
            200,
        ));
        probes.push((discriminant_as_u64(&format!("n_n_value_{slot}"), &n, 0, Ty::i8()), u64::MAX));
        probes.push((discriminant_as_u64(&format!("n_p_value_{slot}"), &n, 1, Ty::i8()), 5));
    }
    run_native(&probes);
}

/// `#[repr(u8)] enum U { A = 0, B = 200 }`: `discriminant(U::B) as u64` is 200 —
/// an unsigned tag widens by zero.
#[test]
fn an_unsigned_repr_u8_tag_widens_by_zero() {
    let u = enum_u();
    run_native(&[
        (discriminant_as_u64("u_b_value", &u, 1, Ty::u8()), 200),
        (switch_on_discriminant("u_b", &u, 1, None, Ty::u8(), &[(200, 100), (0, 200)], 300), 100),
    ]);
}

/// MIR's two-phase construction: build one variant, then `SetDiscriminant` to
/// the other. The slot must hold the TARGET variant's declared value.
#[test]
fn set_discriminant_after_construction_writes_the_declared_value() {
    let arms = [(9, 100), (5, 200)];
    let e = enum_e("__tag");
    let n = enum_n(Ty::i8());
    run_native(&[
        (switch_on_discriminant("e_a_set_b", &e, 0, Some(1), Ty::isize(), &arms, 300), 100),
        (switch_on_discriminant("e_b_set_a", &e, 1, Some(0), Ty::isize(), &arms, 300), 200),
        (
            switch_on_discriminant(
                "n_p_set_n",
                &n,
                1,
                Some(0),
                Ty::i8(),
                &[(255, 100), (5, 200)],
                300,
            ),
            100,
        ),
    ]);
}

/// CONTROL: `enum C { A, B }` (discriminant == index), field spelled `tag` —
/// the one shape main already got right. It must stay right.
#[test]
fn control_dense_discriminants_spelled_tag_stay_green() {
    let c = enum_c("tag");
    let arms = [(1, 100), (0, 200)];
    run_native(&[
        (switch_on_discriminant("c_b", &c, 1, None, Ty::isize(), &arms, 300), 100),
        (switch_on_discriminant("c_a", &c, 0, None, Ty::isize(), &arms, 300), 200),
        (switch_on_discriminant("c_a_set_b", &c, 0, Some(1), Ty::isize(), &arms, 300), 100),
        (discriminant_as_u64("c_b_value", &c, 1, Ty::isize()), 1),
    ]);
}

/// The same dense control on the extractor's `__tag` spelling.
#[test]
fn control_dense_discriminants_spelled_dunder_tag() {
    let c = enum_c("__tag");
    let arms = [(1, 100), (0, 200)];
    run_native(&[
        (switch_on_discriminant("cd_b", &c, 1, None, Ty::isize(), &arms, 300), 100),
        (switch_on_discriminant("cd_a", &c, 0, None, Ty::isize(), &arms, 300), 200),
    ]);
}

/// `fn name() -> <dest_ty> { discriminant(<enum_ty>::<variant>) }` — the read
/// lands DIRECTLY in `dest_ty`, with no `Rvalue::Cast` after it, so the
/// extension the read itself emits is what the caller sees.
fn discriminant_direct(
    name: &str,
    enum_ty: &Ty,
    variant: usize,
    dest_ty: Ty,
) -> VerifiableFunction {
    let stmts = vec![
        build(enum_ty, variant),
        Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Discriminant(Place::local(1)),
            span: SourceSpan::default(),
        },
    ];
    let blocks = vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }];
    let mut f = function(name, vec![dest_ty.clone(), enum_ty.clone()], blocks);
    f.body.return_ty = dest_ty;
    f
}

/// The read's OWN extension, pinned in both directions: a narrow slot read
/// straight into a wider destination is extended by the SLOT's sign, whatever
/// the destination's. `N::N` (-1 in an i8 slot) is all ones in an i64 and in a
/// u64 destination; `U::B` (200 in a u8 slot) is 200 in both. Every other
/// executing test here reads into the discriminant's own type or through an
/// `Rvalue::Cast`, where a flipped `Sextend`/`Uextend` in the read is invisible.
#[test]
fn the_read_extends_by_the_slots_sign_into_a_wider_destination() {
    let n = enum_n(Ty::i8());
    let u = enum_u();
    run_native(&[
        (discriminant_direct("n_n_into_i64", &n, 0, Ty::i64()), u64::MAX),
        (discriminant_direct("n_n_into_u64", &n, 0, Ty::u64()), u64::MAX),
        (discriminant_direct("n_p_into_u64", &n, 1, Ty::u64()), 5),
        (discriminant_direct("u_b_into_i64", &u, 1, Ty::i64()), 200),
        (discriminant_direct("u_b_into_u64", &u, 1, Ty::u64()), 200),
    ]);
}

/// `if let M::A = m` on `#[repr(i32)] enum M { A = -1, B = 5 }` and on
/// `#[repr(u32)] enum Q { A = u32::MAX, B = 1 }`: MIR's ONE label is
/// `0xFFFF_FFFF`, so the switch lowers as `Icmp` + `Brif`, not a `Switch`. On
/// 50b0bfe77a that single-label arm materialized the label as an `I64` against
/// the 32-bit selector and the AArch64 encoder refused every one of these
/// functions ("CMP register widths must agree"). Both slot widths: the 32-bit
/// slot of a layout-faithful shape and the extractor's i64 `__tag`.
#[test]
fn a_32_bit_if_let_on_a_high_declared_discriminant_routes() {
    let mut probes = Vec::new();
    for (slot, m_slot, q_slot) in [("s32", Ty::i32(), Ty::u32()), ("s64", Ty::i64(), Ty::i64())] {
        let m = flat_enum("t216::M", "__tag", m_slot, &[("A", -1), ("B", 5)]);
        let q = flat_enum("t216::Q", "__tag", q_slot, &[("A", 0xFFFF_FFFF), ("B", 1)]);
        let if_let_a = [(0xFFFF_FFFF, 100)];
        for (tag, ty, discr_ty) in [("m", &m, Ty::i32()), ("q", &q, Ty::u32())] {
            probes.push((
                switch_on_discriminant(
                    &format!("{tag}_a_iflet_{slot}"),
                    ty,
                    0,
                    None,
                    discr_ty.clone(),
                    &if_let_a,
                    300,
                ),
                100,
            ));
            probes.push((
                switch_on_discriminant(
                    &format!("{tag}_b_iflet_{slot}"),
                    ty,
                    1,
                    None,
                    discr_ty,
                    &if_let_a,
                    300,
                ),
                300,
            ));
        }
    }
    run_native(&probes);
}

/// ONE slot rule at all three sites. A DECLARED struct has no slot, even with
/// a field spelled `tag` and even carrying a one-variant descriptor:
/// * `discriminant(s)` is 0, rustc's `discriminant_value` for a non-enum;
///   before, the read took `tag` for a slot and returned the DATA, 40;
/// * `SetDiscriminant(s, 0)` is refused by name; before, it wrote the declared
///   value 0 into `tag` (with a descriptor) or refused for want of one.
#[test]
fn a_declared_struct_has_no_slot_at_any_site() {
    let struct_s = |variants: Vec<VariantDef>| Ty::Adt {
        adt_kind: Some(AdtKind::Struct),
        layout: None,
        name: "t216::S".into(),
        fields: vec![("tag".to_string(), Ty::u64()), ("x".to_string(), Ty::u64())].into(),
        variants: variants.into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    };
    let bare = struct_s(Vec::new());
    let described = struct_s(vec![VariantDef {
        name: "S".into(),
        discriminant: 0,
        fields: vec![("tag".into(), Ty::u64()), ("x".into(), Ty::u64())],
    }]);
    run_native(&[
        (build_with_operands("s_discriminant", &bare, 0, &[40, 2], None), 0),
        (build_with_operands("s_described_discriminant", &described, 0, &[40, 2], None), 0),
    ]);
    for (label, s) in [("bare", &bare), ("described", &described)] {
        let blocks = vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![
                aggregate(s, 0, &[40, 2]),
                Statement::SetDiscriminant { place: Place::local(1), variant_index: 0 },
                return_place(Place::field(1, 0)),
            ],
            terminator: Terminator::Return,
        }];
        let f = function(&format!("s_set_{label}"), vec![Ty::u64(), s.clone()], blocks);
        let err = lowering_error(&f);
        assert!(
            err.contains("SetDiscriminant") && err.contains("declared struct/union"),
            "{label}: {err}"
        );
    }
    // An ADT NOT declared a struct and carrying no slot stays refused: it may be
    // an enum whose slot the lane cannot see, and 0 would be a guess.
    let undeclared = Ty::Adt {
        adt_kind: None,
        layout: None,
        name: "t216::Undeclared".into(),
        fields: vec![("x".to_string(), Ty::u64())].into(),
        variants: Vec::new().into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    };
    let err = lowering_error(&build_with_operands("undeclared", &undeclared, 0, &[4], None));
    assert!(err.contains("no explicit discriminant/tag field"), "{err}");
}

// ---------------------------------------------------------------------------
// Structural pins (no host needed): the constant stored, the load width.
// ---------------------------------------------------------------------------

fn opcodes(lir: &LirFunction) -> Vec<Opcode> {
    let mut blocks: Vec<_> = lir.blocks.iter().collect();
    blocks.sort_by_key(|(block, _)| block.0);
    blocks.into_iter().flat_map(|(_, b)| b.instructions.iter().map(|i| i.opcode.clone())).collect()
}

#[test]
fn construction_materializes_the_declared_constant_not_the_index() {
    let f = discriminant_as_u64("e_b_shape", &enum_e("__tag"), 1, Ty::isize());
    let ops = opcodes(&backend().lower_function(&f).expect("lowers"));
    assert!(
        ops.iter().any(|op| matches!(op, Opcode::Iconst { ty: LirType::I64, imm: 9 })),
        "E::B must store 9: {ops:?}"
    );
    assert!(
        !ops.iter().any(|op| matches!(op, Opcode::Iconst { ty: LirType::I64, imm: 1 })),
        "E::B must not store its index 1: {ops:?}"
    );
}

#[test]
fn the_read_loads_the_tag_at_its_own_width() {
    let f = discriminant_as_u64("n_shape", &enum_n(Ty::i8()), 0, Ty::i8());
    let ops = opcodes(&backend().lower_function(&f).expect("lowers"));
    assert!(
        ops.iter().any(|op| matches!(op, Opcode::Iconst { ty: LirType::I8, imm: -1 })),
        "N::N stores -1 into the i8 slot: {ops:?}"
    );
    assert!(
        ops.iter().any(|op| matches!(op, Opcode::Load { ty: LirType::I8, .. })),
        "the read loads an i8 slot as i8: {ops:?}"
    );
    assert!(
        !ops.iter().any(|op| matches!(op, Opcode::Load { ty: LirType::I64, .. })),
        "the read never loads 8 bytes from a 1-byte slot: {ops:?}"
    );
}

// ---------------------------------------------------------------------------
// Fail-closed pins: a tag the lane cannot state exactly is a refusal.
// ---------------------------------------------------------------------------

fn lowering_error(f: &VerifiableFunction) -> String {
    match backend().lower_function(f) {
        Ok(_) => panic!("{} must be refused", f.name),
        Err(e) => format!("{e:?}"),
    }
}

#[test]
fn a_declared_tag_the_slot_cannot_hold_is_refused() {
    // `#[repr(u16)] enum W { A = 1, B = 300 }` with a u8 slot: 300 has no u8 spelling.
    let w = flat_enum("t216::W", "__tag", Ty::u8(), &[("A", 1), ("B", 300)]);
    let err = lowering_error(&discriminant_as_u64("w_b", &w, 1, Ty::u16()));
    assert!(err.contains("300") && err.contains("does not fit"), "{err}");
    let err =
        lowering_error(&switch_on_discriminant("w_a_set_b", &w, 0, Some(1), Ty::u16(), &[], 0));
    assert!(err.contains("300") && err.contains("does not fit"), "{err}");
    // A negative tag in an unsigned slot.
    let n = enum_n(Ty::u8());
    let err = lowering_error(&discriminant_as_u64("n_u8", &n, 0, Ty::i8()));
    assert!(err.contains("-1") && err.contains("does not fit"), "{err}");
}

#[test]
fn a_variant_the_descriptor_does_not_have_is_refused() {
    let e = enum_e("__tag");
    let err = lowering_error(&discriminant_as_u64("e_2", &e, 2, Ty::isize()));
    assert!(err.contains("variant 2"), "{err}");
    let err =
        lowering_error(&switch_on_discriminant("e_set_2", &e, 0, Some(2), Ty::isize(), &[], 0));
    assert!(err.contains("variant 2"), "{err}");
}

#[test]
fn a_tagged_adt_without_a_variant_descriptor_is_refused() {
    // The index is a guess at the declared value; in codegen a wrong guess is a
    // miscompile, so the lane needs the descriptor.
    let bare = Ty::Adt {
        adt_kind: None,
        layout: None,
        name: "t216::Bare".into(),
        fields: vec![("tag".to_string(), Ty::i64())].into(),
        variants: Vec::new().into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    };
    let err = lowering_error(&discriminant_as_u64("bare_1", &bare, 1, Ty::isize()));
    assert!(err.contains("variant descriptor"), "{err}");
    // `SetDiscriminant` alone, on a parameter, so the refusal is its own.
    let mut set_only = function(
        "bare_set",
        vec![Ty::Unit, bare.clone()],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::SetDiscriminant { place: Place::local(1), variant_index: 1 }],
            terminator: Terminator::Return,
        }],
    );
    set_only.body.arg_count = 1;
    set_only.body.return_ty = Ty::Unit;
    let err = lowering_error(&set_only);
    assert!(err.contains("SetDiscriminant") && err.contains("variant descriptor"), "{err}");
    // The same body on a described twin lowers: the refusal is the descriptor's.
    set_only.body.locals[1].ty = enum_c("tag");
    backend().lower_function(&set_only).expect("a described SetDiscriminant lowers");
}

// ---------------------------------------------------------------------------
// The payload lanes around the slot.
// ---------------------------------------------------------------------------

/// `fn name() -> u64 { let o = <adt_ty>::<variant>(operands..); <read> }` where
/// `read` is `discriminant(o) as u64` (`None`) or `o.<field>` (`Some(field)`, a
/// u64 field of the flat layout, read without a downcast).
fn build_with_operands(
    name: &str,
    adt_ty: &Ty,
    variant: usize,
    operands: &[u64],
    read: Option<usize>,
) -> VerifiableFunction {
    let mut stmts = vec![Statement::Assign {
        place: Place::local(1),
        rvalue: Rvalue::Aggregate(
            AggregateKind::Adt { name: adt_name(adt_ty), variant, active_field: None, args: None },
            operands
                .iter()
                .map(|value| Operand::Constant(ConstValue::Uint(u128::from(*value), 64)))
                .collect(),
        ),
        span: SourceSpan::default(),
    }];
    match read {
        None => {
            stmts.push(Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::Discriminant(Place::local(1)),
                span: SourceSpan::default(),
            });
            stmts.push(Statement::Assign {
                place: Place::local(0),
                rvalue: Rvalue::Cast(Operand::Copy(Place::local(2)), Ty::u64()),
                span: SourceSpan::default(),
            });
        }
        Some(field) => stmts.push(Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(Operand::Copy(Place::field(1, field))),
            span: SourceSpan::default(),
        }),
    }
    let blocks = vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }];
    function(name, vec![Ty::u64(), adt_ty.clone(), Ty::isize()], blocks)
}

/// `Option<u64>` as the extractor shapes it: `__tag` at 0, then `__v1_0`.
/// `Some(7)` puts 1 in the slot and 7 in the lane. On main the `__tag` spelling
/// was not recognised, so the operand went into field 0 — the slot — and
/// `discriminant(Some(7))` read 7.
#[test]
fn a_payload_operand_lands_in_its_lane_not_in_the_dunder_tag_slot() {
    let option = Ty::Adt {
        adt_kind: Some(AdtKind::Enum),
        layout: None,
        name: "t216::Option".into(),
        fields: vec![("__tag".to_string(), Ty::i64()), ("__v1_0".to_string(), Ty::u64())].into(),
        variants: vec![
            VariantDef { name: "None".into(), discriminant: 0, fields: vec![] },
            VariantDef {
                name: "Some".into(),
                discriminant: 1,
                fields: vec![("0".into(), Ty::u64())],
            },
        ]
        .into(),
        disc_index_safe: true,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    };
    run_native(&[
        (build_with_operands("some7_discriminant", &option, 1, &[7], None), 1),
        (build_with_operands("some7_payload", &option, 1, &[7], Some(1)), 7),
    ]);
}

/// A declared STRUCT has no tag slot: its field spelled `tag` is data, and the
/// aggregate stores both operands where they belong. On main field 0 spelled
/// `tag` was taken for a discriminant, so `S { tag: 40, x: 2 }` did not lower.
#[test]
fn a_struct_field_spelled_tag_is_data() {
    let s = Ty::Adt {
        adt_kind: Some(AdtKind::Struct),
        layout: None,
        name: "t216::S".into(),
        fields: vec![("tag".to_string(), Ty::u64()), ("x".to_string(), Ty::u64())].into(),
        variants: Vec::new().into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    };
    run_native(&[
        (build_with_operands("s_tag", &s, 0, &[40, 2], Some(0)), 40),
        (build_with_operands("s_x", &s, 0, &[40, 2], Some(1)), 2),
    ]);
}

// ---------------------------------------------------------------------------
// Payload lanes addressed by VARIANT: the aggregate write, the `Downcast`
// read and the `Downcast` write must agree on the extractor's `__v{v}_{name}`
// lane (review of 95382e6164).
// ---------------------------------------------------------------------------

/// A flat enum as `trust_mir_extract::ty_convert::lower_enum_adt` shapes it:
/// `__tag: i64` at index 0, then one `__v{v}_{name}` lane per variant field,
/// with the per-variant descriptor naming each field.
fn extractor_enum(name: &str, variants: &[(&str, i128, &[(&str, Ty)])]) -> Ty {
    let mut fields = vec![("__tag".to_string(), Ty::i64())];
    for (variant_index, (_, _, variant_fields)) in variants.iter().enumerate() {
        for (field_name, field_ty) in variant_fields.iter() {
            fields.push((format!("__v{variant_index}_{field_name}"), field_ty.clone()));
        }
    }
    Ty::Adt {
        adt_kind: Some(AdtKind::Enum),
        layout: None,
        name: name.into(),
        fields: fields.into(),
        variants: variants
            .iter()
            .map(|(variant, discriminant, variant_fields)| VariantDef {
                name: (*variant).into(),
                discriminant: *discriminant,
                fields: variant_fields
                    .iter()
                    .map(|(field_name, field_ty)| ((*field_name).into(), field_ty.clone()))
                    .collect(),
            })
            .collect::<Vec<_>>()
            .into(),
        disc_index_safe: true,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    }
}

/// `Result<u64, u64>`: `[__tag, __v0_0, __v1_0]`, `Ok = 0`, `Err = 1`.
fn result_u64() -> Ty {
    extractor_enum(
        "t216::Result",
        &[("Ok", 0, &[("0", Ty::u64())]), ("Err", 1, &[("0", Ty::u64())])],
    )
}

/// `Option<u64>`: `[__tag, __v1_0]`, `None = 0`, `Some = 1`.
fn option_u64() -> Ty {
    extractor_enum("t216::Option", &[("None", 0, &[]), ("Some", 1, &[("0", Ty::u64())])])
}

/// `enum W { V(u64) }`: `[__tag, __v0_0]`.
fn single_variant_w() -> Ty {
    extractor_enum("t216::W", &[("V", 0, &[("0", Ty::u64())])])
}

/// `(_1 as <variant>).<field>` — rustc's MIR spelling of a payload place.
fn downcast_field(variant: usize, field: usize) -> Place {
    Place { local: 1, projections: vec![Projection::Downcast(variant), Projection::Field(field)] }
}

fn aggregate(adt_ty: &Ty, variant: usize, operands: &[u64]) -> Statement {
    Statement::Assign {
        place: Place::local(1),
        rvalue: Rvalue::Aggregate(
            AggregateKind::Adt { name: adt_name(adt_ty), variant, active_field: None, args: None },
            operands
                .iter()
                .map(|value| Operand::Constant(ConstValue::Uint(u128::from(*value), 64)))
                .collect(),
        ),
        span: SourceSpan::default(),
    }
}

fn return_place(place: Place) -> Statement {
    Statement::Assign {
        place: Place::local(0),
        rvalue: Rvalue::Use(Operand::Copy(place)),
        span: SourceSpan::default(),
    }
}

/// `fn name() -> u64 { let e = <adt_ty>::<variant>(operands..); <read> }`.
fn build_then_read(
    name: &str,
    adt_ty: &Ty,
    variant: usize,
    operands: &[u64],
    read: Place,
) -> VerifiableFunction {
    let blocks = vec![BasicBlock {
        id: BlockId(0),
        stmts: vec![aggregate(adt_ty, variant, operands), return_place(read)],
        terminator: Terminator::Return,
    }];
    function(name, vec![Ty::u64(), adt_ty.clone(), Ty::isize()], blocks)
}

/// `Err(5)` of `Result<u64, u64>`: the operand lands in `__v1_0` (flat field 2),
/// never in `Ok`'s `__v0_0`. At 95382e6164 the aggregate mapped operands onto
/// the non-slot fields IN ORDER, so `Err(5)` wrote Ok's lane and left `__v1_0`
/// uninitialised (a read returned stack garbage).
#[test]
fn a_payload_operand_lands_in_its_own_variants_lane() {
    let result = result_u64();
    run_native(&[
        (build_then_read("err5_flat_v1_0", &result, 1, &[5], Place::field(1, 2)), 5),
        (build_then_read("ok3_flat_v0_0", &result, 0, &[3], Place::field(1, 1)), 3),
    ]);
}

/// `(e as V).k` reads variant V's own lane. At 95382e6164 `Downcast` was a
/// type-only no-op, so `(r as Err).0` read flat field 0 — the TAG.
#[test]
fn a_downcast_payload_read_reads_the_variants_lane() {
    let result = result_u64();
    let w = single_variant_w();
    let option = option_u64();
    run_native(&[
        (build_then_read("err7_as_err", &result, 1, &[7], downcast_field(1, 0)), 7),
        (build_then_read("ok3_as_ok", &result, 0, &[3], downcast_field(0, 0)), 3),
        (build_then_read("w7_as_v", &w, 0, &[7], downcast_field(0, 0)), 7),
        (build_then_read("some7_as_some", &option, 1, &[7], downcast_field(1, 0)), 7),
    ]);
}

/// rustc's own MIR for `match Some(7u64) { Some(x) => x, None => 0 }`:
/// ```text
/// bb0: _1 = Option::Some(7); _2 = discriminant(_1);
///      switchInt(move _2) -> [0: bb2, 1: bb1, otherwise: bb3]
/// bb1: _0 = copy ((_1 as Some).0); return
/// bb2: _0 = 0; return
/// bb3: unreachable (here: return 300)
/// ```
/// At 95382e6164 the switch routed to bb1 and bb1 returned the tag, 1.
#[test]
fn rustcs_option_match_returns_the_payload() {
    let option = option_u64();
    let constant = |value: u64, id: usize| BasicBlock {
        id: BlockId(id),
        stmts: vec![Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(u128::from(value), 64))),
            span: SourceSpan::default(),
        }],
        terminator: Terminator::Return,
    };
    let probe = |name: &str, variant: usize, operands: &[u64]| {
        function(
            name,
            vec![Ty::u64(), option.clone(), Ty::isize()],
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        aggregate(&option, variant, operands),
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Discriminant(Place::local(1)),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Move(Place::local(2)),
                        targets: vec![(0, BlockId(2)), (1, BlockId(1))],
                        otherwise: BlockId(3),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![return_place(downcast_field(1, 0))],
                    terminator: Terminator::Return,
                },
                constant(0, 2),
                constant(300, 3),
            ],
        )
    };
    run_native(&[(probe("match_some7", 1, &[7]), 7), (probe("match_none", 0, &[]), 0)]);
}

/// The WRITE through `Downcast` addresses the same lane the read does: build
/// `Ok(3)`, write `(r as Err).0 = 5`, set the discriminant to `Err`, read
/// `(r as Err).0`. At 95382e6164 the write landed in flat field 0 (the slot),
/// `SetDiscriminant` overwrote it, and the read returned the tag, 1.
#[test]
fn a_downcast_payload_write_lands_in_the_lane_the_read_reads() {
    let result = result_u64();
    let blocks = vec![BasicBlock {
        id: BlockId(0),
        stmts: vec![
            aggregate(&result, 0, &[3]),
            Statement::Assign {
                place: downcast_field(1, 0),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(5, 64))),
                span: SourceSpan::default(),
            },
            Statement::SetDiscriminant { place: Place::local(1), variant_index: 1 },
            return_place(downcast_field(1, 0)),
        ],
        terminator: Terminator::Return,
    }];
    let write = function("ok3_write_err5", vec![Ty::u64(), result.clone(), Ty::isize()], blocks);
    run_native(&[(write, 5)]);
}

/// A tagged enum whose variant has no `__v{v}_{name}` lane cannot place a
/// payload: the aggregate and the `Downcast` read both refuse, never guess a
/// field by position.
#[test]
fn a_payload_with_no_lane_is_refused() {
    // `[__tag, value]` with a descriptor naming Some's field `0`: no `__v1_0`.
    let unlaned = Ty::Adt {
        adt_kind: Some(AdtKind::Enum),
        layout: None,
        name: "t216::Unlaned".into(),
        fields: vec![("__tag".to_string(), Ty::i64()), ("value".to_string(), Ty::u64())].into(),
        variants: vec![
            VariantDef { name: "None".into(), discriminant: 0, fields: vec![] },
            VariantDef {
                name: "Some".into(),
                discriminant: 1,
                fields: vec![("0".into(), Ty::u64())],
            },
        ]
        .into(),
        disc_index_safe: true,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    };
    let err =
        lowering_error(&build_then_read("unlaned_some", &unlaned, 1, &[7], Place::field(1, 1)));
    assert!(err.contains("__v1_0"), "{err}");
    let err =
        lowering_error(&build_then_read("unlaned_read", &unlaned, 0, &[], downcast_field(1, 0)));
    assert!(err.contains("__v1_0"), "{err}");
    // More operands than the variant declares fields.
    let err =
        lowering_error(&build_then_read("some_two", &option_u64(), 1, &[7, 8], Place::field(1, 1)));
    assert!(err.contains("operand"), "{err}");
    // A field the variant does not have, read through its downcast.
    let err =
        lowering_error(&build_then_read("none_field", &option_u64(), 0, &[], downcast_field(0, 0)));
    assert!(err.contains("variant 0"), "{err}");
}

// ---------------------------------------------------------------------------
// A value BUILT into a projected destination (review of 80c222a42a).
//
// rustc lowers `s.e = E::B(3)` with a no-drop lhs straight into the place:
// `(_1.1: E) = E::B(const 3)`. The aggregate took `local_ty(_1)` — the whole
// local's type — for the value it built, laid the tag and operands out in the
// OUTER type's lanes, and rebound all of `_1` to that slot. `Repeat` and
// `CheckedBinaryOp` did the same.
// ---------------------------------------------------------------------------

fn at(local: usize, projections: Vec<Projection>) -> Place {
    Place { local, projections }
}

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}

fn adt_at(place: Place, adt_ty: &Ty, variant: usize, operands: Vec<Operand>) -> Statement {
    assign(
        place,
        Rvalue::Aggregate(
            AggregateKind::Adt { name: adt_name(adt_ty), variant, active_field: None, args: None },
            operands,
        ),
    )
}

fn u64_const(value: u64) -> Operand {
    Operand::Constant(ConstValue::Uint(u128::from(value), 64))
}

/// `enum E { A = 5, B(u64) = 9 }` as the extractor shapes it: `[__tag, __v1_0]`.
fn payload_enum_e() -> Ty {
    extractor_enum("t216::PE", &[("A", 5, &[]), ("B", 9, &[("0", Ty::u64())])])
}

/// `struct S { a: u64, e: E }`.
fn struct_with_enum() -> Ty {
    Ty::Adt {
        adt_kind: Some(AdtKind::Struct),
        layout: None,
        name: "t216::SE".into(),
        fields: vec![("a".to_string(), Ty::u64()), ("e".to_string(), payload_enum_e())].into(),
        variants: Vec::new().into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    }
}

/// How a probe turns a place into its answer in `_0: u64`.
#[derive(Clone, Copy)]
enum How {
    /// `_0 = copy place`.
    Value,
    /// `_0 = copy place as u64`.
    Cast,
    /// `_t = discriminant(place); _0 = _t as u64`.
    Discriminant,
}

/// A probe's read: a place read directly, or read through its ADDRESS
/// (`_p = &raw const place; _0 = copy *_p`). Both walk any depth since the
/// home rule (review 4): a read walk keeps an aggregate step at its address.
/// Before it, `resolve_place` read ONE field level per place and a
/// `Load`/`Store` of a struct moved one machine word on AArch64, so nested
/// lanes were read through the address only.
enum Read {
    Direct(How, Place),
    /// `_p = &raw const place` (`_p: *const pointee`), then `how` on `*_p`.
    Addr {
        place: Place,
        pointee: Ty,
        how: How,
    },
}

fn read_answer(read: Read, locals: &mut Vec<Ty>, stmts: &mut Vec<Statement>) {
    let (how, place) = match read {
        Read::Direct(how, place) => (how, place),
        Read::Addr { place, pointee, how } => {
            locals.push(Ty::RawPtr { mutable: false, pointee: Box::new(pointee) });
            let p = locals.len() - 1;
            stmts.push(assign(Place::local(p), Rvalue::AddressOf(false, place)));
            (how, at(p, vec![Projection::Deref]))
        }
    };
    match how {
        How::Value => stmts.push(return_place(place)),
        How::Cast => {
            stmts.push(assign(Place::local(0), Rvalue::Cast(Operand::Copy(place), Ty::u64())))
        }
        How::Discriminant => {
            locals.push(Ty::isize());
            let t = locals.len() - 1;
            stmts.push(assign(Place::local(t), Rvalue::Discriminant(place)));
            stmts.push(assign(
                Place::local(0),
                Rvalue::Cast(Operand::Copy(Place::local(t)), Ty::u64()),
            ));
        }
    }
}

fn one_block(
    name: &str,
    mut locals: Vec<Ty>,
    mut stmts: Vec<Statement>,
    read: Read,
) -> VerifiableFunction {
    read_answer(read, &mut locals, &mut stmts);
    let blocks = vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }];
    function(name, locals, blocks)
}

/// `let mut s = S { a: 7, e: E::A }; s.e = E::B(3); <read>`:
/// `_2 = E::A; _1 = S { 7, move _2 }; (_1.1) = E::B(3)`.
fn struct_field_aggregate(name: &str, read: Read) -> VerifiableFunction {
    let e = payload_enum_e();
    let s = struct_with_enum();
    let stmts = vec![
        adt_at(Place::local(2), &e, 0, vec![]),
        adt_at(Place::local(1), &s, 0, vec![u64_const(7), Operand::Move(Place::local(2))]),
        adt_at(Place::field(1, 1), &e, 1, vec![u64_const(3)]),
    ];
    one_block(name, vec![Ty::u64(), s, e], stmts, read)
}

/// `s.e = E::B(3)` writes `s.e` and only `s.e`: `s.a` stays 7, `s.e` reads
/// `B` (9) with payload 3. At 80c222a42a the aggregate laid `E::B(3)` out in
/// `S`'s lanes and rebound all of `s` to that slot: `s.a` read 3 and
/// `discriminant(s.e)` read stack garbage (a different value per run).
#[test]
fn an_aggregate_into_a_struct_field_writes_that_field() {
    let e_payload =
        at(1, vec![Projection::Field(1), Projection::Downcast(1), Projection::Field(0)]);
    run_native(&[
        (struct_field_aggregate("se_a", Read::Direct(How::Value, Place::field(1, 0))), 7),
        (
            struct_field_aggregate(
                "se_e_discriminant",
                Read::Direct(How::Discriminant, Place::field(1, 1)),
            ),
            9,
        ),
        (
            struct_field_aggregate(
                "se_e_discriminant_by_address",
                Read::Addr {
                    place: Place::field(1, 1),
                    pointee: payload_enum_e(),
                    how: How::Discriminant,
                },
            ),
            9,
        ),
        (
            struct_field_aggregate(
                "se_e_payload",
                Read::Addr { place: e_payload, pointee: Ty::u64(), how: How::Value },
            ),
            3,
        ),
    ]);
}

/// `O = Option<E>` shaped `[__tag, __v1_0: E]`.
fn option_of_payload_enum() -> Ty {
    extractor_enum("t216::OE", &[("None", 0, &[]), ("Some", 1, &[("0", payload_enum_e())])])
}

/// `let mut o = Some(E::A); if let Some(inner) = &mut o { *inner = E::B(3) }`
/// after inlining: `_2 = E::A; _1 = O::Some(move _2); ((_1 as Some).0) = E::B(3)`.
fn downcast_payload_aggregate(name: &str, read: Read) -> VerifiableFunction {
    let e = payload_enum_e();
    let o = option_of_payload_enum();
    let stmts = vec![
        adt_at(Place::local(2), &e, 0, vec![]),
        adt_at(Place::local(1), &o, 1, vec![Operand::Move(Place::local(2))]),
        adt_at(downcast_field(1, 0), &e, 1, vec![u64_const(3)]),
    ];
    one_block(name, vec![Ty::u64(), o, e], stmts, read)
}

/// The payload of `Some` becomes `E::B(3)`; `o` stays `Some`. At 80c222a42a
/// `discriminant((o as Some).0)` read 3 — the operand had gone into `O`'s
/// payload lane, where `E`'s slot sits.
#[test]
fn an_aggregate_into_a_downcast_payload_writes_that_payload() {
    let mut inner_payload = downcast_field(1, 0);
    inner_payload.projections.extend([Projection::Downcast(1), Projection::Field(0)]);
    run_native(&[
        (
            downcast_payload_aggregate(
                "oe_inner_discriminant",
                Read::Direct(How::Discriminant, downcast_field(1, 0)),
            ),
            9,
        ),
        (
            downcast_payload_aggregate(
                "oe_outer_discriminant",
                Read::Direct(How::Discriminant, Place::local(1)),
            ),
            1,
        ),
        (
            downcast_payload_aggregate(
                "oe_inner_discriminant_by_address",
                Read::Addr {
                    place: downcast_field(1, 0),
                    pointee: payload_enum_e(),
                    how: How::Discriminant,
                },
            ),
            9,
        ),
        (
            downcast_payload_aggregate(
                "oe_inner_payload",
                Read::Addr { place: inner_payload, pointee: Ty::u64(), how: How::Value },
            ),
            3,
        ),
    ]);
}

/// An `Adt` aggregate naming another ADT than the place it builds into is
/// invalid MIR, and the lanes it would pick belong to the wrong type: refused.
#[test]
fn an_aggregate_naming_another_adt_than_its_destination_is_refused() {
    let e = payload_enum_e();
    let s = struct_with_enum();
    // `_1: S`, built as `E::B(3)`.
    let whole = one_block(
        "adt_name_mismatch",
        vec![Ty::u64(), s.clone()],
        vec![adt_at(Place::local(1), &e, 1, vec![u64_const(3)])],
        Read::Direct(How::Value, Place::field(1, 0)),
    );
    let err = lowering_error(&whole);
    assert!(err.contains("t216::PE") && err.contains("t216::SE"), "{err}");
    // `(_1.0: u64) = E::B(3)` — the projected place is not the ADT either.
    let projected = one_block(
        "adt_into_u64_field",
        vec![Ty::u64(), s],
        vec![adt_at(Place::field(1, 0), &e, 1, vec![u64_const(3)])],
        Read::Direct(How::Value, Place::field(1, 0)),
    );
    let err = lowering_error(&projected);
    assert!(err.contains("t216::PE"), "{err}");
}

/// `let mut t = (1u64, 2u64); let r = &mut t; *r = (7, 8); t.<field>`:
/// `(*_2) = (7, 8)` builds a tuple and writes it through the reference. At
/// 80c222a42a the aggregate took `_2`'s type (`&mut (u64, u64)`) for the
/// tuple and refused ("aggregate kind Tuple does not match destination type").
fn aggregate_through_reference(name: &str, field: usize) -> VerifiableFunction {
    let pair = Ty::Tuple(vec![Ty::u64(), Ty::u64()]);
    let reference = Ty::Ref { mutable: true, inner: Box::new(pair.clone()) };
    let stmts = vec![
        assign(
            Place::local(1),
            Rvalue::Aggregate(AggregateKind::Tuple, vec![u64_const(1), u64_const(2)]),
        ),
        assign(Place::local(2), Rvalue::Ref { mutable: true, place: Place::local(1) }),
        assign(
            at(2, vec![Projection::Deref]),
            Rvalue::Aggregate(AggregateKind::Tuple, vec![u64_const(7), u64_const(8)]),
        ),
    ];
    one_block(
        name,
        vec![Ty::u64(), pair, reference],
        stmts,
        Read::Direct(How::Value, Place::field(1, field)),
    )
}

#[test]
fn an_aggregate_through_a_reference_writes_the_referent() {
    run_native(&[
        (aggregate_through_reference("deref_t0", 0), 7),
        (aggregate_through_reference("deref_t1", 1), 8),
    ]);
}

fn u64_array4() -> Ty {
    Ty::Array { elem: Box::new(Ty::u64()), len: 4 }
}

/// `let mut t = (7u64, [0u64; 4]); t.1 = [5; 4]; <read>`:
/// `_2 = [0; 4]; _1 = (7, move _2); (_1.1) = [5; 4]`.
fn repeat_into_tuple_field(name: &str, read: Read) -> VerifiableFunction {
    let array = u64_array4();
    let tuple = Ty::Tuple(vec![Ty::u64(), array.clone()]);
    let stmts = vec![
        assign(Place::local(2), Rvalue::Repeat(u64_const(0), 4)),
        assign(
            Place::local(1),
            Rvalue::Aggregate(
                AggregateKind::Tuple,
                vec![u64_const(7), Operand::Move(Place::local(2))],
            ),
        ),
        assign(Place::field(1, 1), Rvalue::Repeat(u64_const(5), 4)),
    ];
    one_block(name, vec![Ty::u64(), tuple, array], stmts, read)
}

/// `t.1 = [5; 4]` fills `t.1` and leaves `t.0` alone. At 80c222a42a the
/// `Repeat` took the tuple for its destination and refused ("Repeat on
/// non-array type").
#[test]
fn a_repeat_into_a_tuple_field_writes_that_field() {
    let element = |offset| Read::Addr {
        place: at(
            1,
            vec![
                Projection::Field(1),
                Projection::ConstantIndex { offset, min_length: 4, from_end: false },
            ],
        ),
        pointee: Ty::u64(),
        how: How::Value,
    };
    run_native(&[
        (repeat_into_tuple_field("rep_t0", Read::Direct(How::Value, Place::field(1, 0))), 7),
        (repeat_into_tuple_field("rep_t1_0", element(0)), 5),
        (repeat_into_tuple_field("rep_t1_3", element(3)), 5),
    ]);
}

fn u64_bool() -> Ty {
    Ty::Tuple(vec![Ty::u64(), Ty::Bool])
}

/// `_2 = (0, false); _1 = (move _2, 7); (_1.0) = CheckedAdd(u64::MAX, 2); <read>`.
fn checked_into_tuple_field(name: &str, read: Read) -> VerifiableFunction {
    let pair = u64_bool();
    let outer = Ty::Tuple(vec![pair.clone(), Ty::u64()]);
    let stmts = vec![
        assign(
            Place::local(2),
            Rvalue::Aggregate(
                AggregateKind::Tuple,
                vec![u64_const(0), Operand::Constant(ConstValue::Bool(false))],
            ),
        ),
        assign(
            Place::local(1),
            Rvalue::Aggregate(
                AggregateKind::Tuple,
                vec![Operand::Move(Place::local(2)), u64_const(7)],
            ),
        ),
        assign(
            Place::field(1, 0),
            Rvalue::CheckedBinaryOp(BinOp::Add, u64_const(u64::MAX), u64_const(2)),
        ),
    ];
    one_block(name, vec![Ty::u64(), outer, pair], stmts, read)
}

/// `t.0 = <u64::MAX + 2, checked>` writes `t.0 = (1, true)` and leaves `t.1` 7.
#[test]
fn a_checked_op_into_a_tuple_field_writes_that_field() {
    let lane = |index, pointee, how| Read::Addr {
        place: at(1, vec![Projection::Field(0), Projection::Field(index)]),
        pointee,
        how,
    };
    run_native(&[
        (checked_into_tuple_field("chk_t1", Read::Direct(How::Value, Place::field(1, 1))), 7),
        (checked_into_tuple_field("chk_t0_0", lane(0, Ty::u64(), How::Value)), 1),
        (checked_into_tuple_field("chk_t0_1", lane(1, Ty::Bool, How::Cast)), 1),
    ]);
}

// ---------------------------------------------------------------------------
// The same root cause at the sites that READ a projected place's type: each
// took `local_ty(place.local)` — the whole local's type — for `s.x`.
// ---------------------------------------------------------------------------

fn const_bits(bits: u128, width: u32) -> Operand {
    Operand::Constant(ConstValue::Uint(bits, width))
}

/// `let mut t = (0i64, 0u64); let x: i64 = -7; t.0 = x <op> 2; t.0 as u64`.
/// The signedness of `Div`/`Rem`/`Shr` is the DESTINATION's: `t.0` is an i64.
/// At 80c222a42a it was the tuple's (`is_signed` false), so the division was
/// unsigned.
fn signed_op_into_tuple_field(name: &str, op: BinOp, rhs: u64) -> VerifiableFunction {
    let tuple = Ty::Tuple(vec![Ty::i64(), Ty::u64()]);
    let stmts = vec![
        assign(
            Place::local(1),
            Rvalue::Aggregate(AggregateKind::Tuple, vec![const_bits(0, 64), u64_const(0)]),
        ),
        assign(Place::local(2), Rvalue::Use(const_bits((-7i64 as u64).into(), 64))),
        assign(
            Place::field(1, 0),
            Rvalue::BinaryOp(op, Operand::Copy(Place::local(2)), u64_const(rhs)),
        ),
    ];
    one_block(
        name,
        vec![Ty::u64(), tuple, Ty::i64()],
        stmts,
        Read::Direct(How::Cast, Place::field(1, 0)),
    )
}

#[test]
fn a_signed_op_into_a_tuple_field_is_signed() {
    run_native(&[
        (signed_op_into_tuple_field("sdiv_t0", BinOp::Div, 2), -3i64 as u64),
        (signed_op_into_tuple_field("srem_t0", BinOp::Rem, 2), -1i64 as u64),
        (signed_op_into_tuple_field("sshr_t0", BinOp::Shr, 1), -4i64 as u64),
    ]);
}

/// `let t = (-1i8, 200u8); t.<field> as u64`: the cast widens by the FIELD's
/// sign. At 80c222a42a the cast took the tuple for its source, found no width,
/// and passed the 8-bit value through (the emitted return then mismatched).
fn cast_of_tuple_field(name: &str, field: usize) -> VerifiableFunction {
    let tuple = Ty::Tuple(vec![Ty::i8(), Ty::u8()]);
    let stmts = vec![assign(
        Place::local(1),
        Rvalue::Aggregate(AggregateKind::Tuple, vec![const_bits(0xFF, 8), const_bits(200, 8)]),
    )];
    one_block(name, vec![Ty::u64(), tuple], stmts, Read::Direct(How::Cast, Place::field(1, field)))
}

#[test]
fn a_cast_widens_a_tuple_field_by_the_fields_sign() {
    run_native(&[
        (cast_of_tuple_field("cast_t0_i8", 0), u64::MAX),
        (cast_of_tuple_field("cast_t1_u8", 1), 200),
    ]);
}

/// `let t = (1.5f64, 2.25f64); let s = t.0 + t.1; s as u64` = 3. At 80c222a42a
/// an operand's float-ness was its base local's, so the add was an INTEGER add
/// of two f64 bit patterns.
#[test]
fn a_float_op_on_tuple_fields_is_a_float_op() {
    let tuple = Ty::Tuple(vec![Ty::f64_ty(), Ty::f64_ty()]);
    let float = |value| Operand::Constant(ConstValue::Float(value));
    let stmts = vec![
        assign(
            Place::local(1),
            Rvalue::Aggregate(AggregateKind::Tuple, vec![float(1.5), float(2.25)]),
        ),
        assign(
            Place::local(2),
            Rvalue::BinaryOp(
                BinOp::Add,
                Operand::Copy(Place::field(1, 0)),
                Operand::Copy(Place::field(1, 1)),
            ),
        ),
    ];
    let f = one_block(
        "fadd_t",
        vec![Ty::u64(), tuple, Ty::f64_ty()],
        stmts,
        Read::Direct(How::Cast, Place::local(2)),
    );
    run_native(&[(f, 3)]);
}

// ---------------------------------------------------------------------------
// A tag slot that is NOT field 0 (review of 80c222a42a): every fixture above
// puts the slot at index 0, so a site that addressed field 0 instead of the
// slot's own index stayed green. A library producer may order the slot last.
// ---------------------------------------------------------------------------

/// `Option<u64>` laid out `[__v1_0: u64, __tag: i64]`, `None = 5`, `Some = 9`.
fn option_slot_last() -> Ty {
    Ty::Adt {
        adt_kind: Some(AdtKind::Enum),
        layout: None,
        name: "t216::OptionSlotLast".into(),
        fields: vec![("__v1_0".to_string(), Ty::u64()), ("__tag".to_string(), Ty::i64())].into(),
        variants: vec![
            VariantDef { name: "None".into(), discriminant: 5, fields: vec![] },
            VariantDef {
                name: "Some".into(),
                discriminant: 9,
                fields: vec![("0".into(), Ty::u64())],
            },
        ]
        .into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    }
}

/// `let o = <variant>(operands..); [SetDiscriminant(o, set_to);] <read>`, where
/// `read` is `discriminant(o) as u64` (`None`) or a place of `o`.
fn slot_last_probe(
    name: &str,
    variant: usize,
    operands: &[u64],
    set_to: Option<usize>,
    read: Option<Place>,
) -> VerifiableFunction {
    let option = option_slot_last();
    let mut stmts = vec![aggregate(&option, variant, operands)];
    if let Some(variant_index) = set_to {
        stmts.push(Statement::SetDiscriminant { place: Place::local(1), variant_index });
    }
    match read {
        None => {
            stmts.push(assign(Place::local(2), Rvalue::Discriminant(Place::local(1))));
            stmts.push(assign(
                Place::local(0),
                Rvalue::Cast(Operand::Copy(Place::local(2)), Ty::u64()),
            ));
        }
        Some(place) => stmts.push(return_place(place)),
    }
    let blocks = vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }];
    function(name, vec![Ty::u64(), option, Ty::isize()], blocks)
}

/// Construction, the read and `SetDiscriminant` each address the slot at its
/// own index (1), and the payload lane (0) round-trips beside it.
#[test]
fn a_tag_slot_after_the_payload_lane_round_trips() {
    run_native(&[
        (slot_last_probe("sl_some7_discriminant", 1, &[7], None, None), 9),
        (slot_last_probe("sl_some7_payload", 1, &[7], None, Some(downcast_field(1, 0))), 7),
        (slot_last_probe("sl_none_discriminant", 0, &[], None, None), 5),
        (slot_last_probe("sl_some7_set_none_discriminant", 1, &[7], Some(0), None), 5),
        (slot_last_probe("sl_some7_set_none_lane", 1, &[7], Some(0), Some(Place::field(1, 0))), 7),
        (slot_last_probe("sl_some7_set_some_discriminant", 1, &[7], Some(1), None), 9),
    ]);
}

// ---------------------------------------------------------------------------
// Review of bed6567522. A place written THROUGH a pointer must land in the
// pointer's CURRENT referent, a drop is typed by its PLACE, and a whole local
// keeps ONE home once its address has been taken.
// ---------------------------------------------------------------------------

fn pair() -> Ty {
    Ty::Tuple(vec![Ty::u64(), Ty::u64()])
}

fn raw_mut(pointee: Ty) -> Ty {
    Ty::RawPtr { mutable: true, pointee: Box::new(pointee) }
}

fn tuple_of(values: &[u64]) -> Rvalue {
    Rvalue::Aggregate(AggregateKind::Tuple, values.iter().map(|v| u64_const(*v)).collect())
}

/// `let mut a = (1, 2); let mut b = (3, 4); let mut p = &raw mut a;
/// *p = (5, 6); p = &raw mut b; *p = (7, 8); <read>`.
fn aggregate_through_a_reassigned_pointer(name: &str, read: Read) -> VerifiableFunction {
    let stmts = vec![
        assign(Place::local(1), tuple_of(&[1, 2])),
        assign(Place::local(2), tuple_of(&[3, 4])),
        assign(Place::local(3), Rvalue::AddressOf(true, Place::local(1))),
        assign(at(3, vec![Projection::Deref]), tuple_of(&[5, 6])),
        assign(Place::local(3), Rvalue::AddressOf(true, Place::local(2))),
        assign(at(3, vec![Projection::Deref]), tuple_of(&[7, 8])),
    ];
    one_block(name, vec![Ty::u64(), pair(), pair(), raw_mut(pair())], stmts, read)
}

/// `let mut a = 10u64; let mut b = 20u64; let mut p = &raw mut a;
/// *p = 1; p = &raw mut b; *p = 2; <read of k through its address>`.
fn scalar_through_a_reassigned_pointer(name: &str, k: usize) -> VerifiableFunction {
    let stmts = vec![
        assign(Place::local(1), Rvalue::Use(u64_const(10))),
        assign(Place::local(2), Rvalue::Use(u64_const(20))),
        assign(Place::local(3), Rvalue::AddressOf(true, Place::local(1))),
        assign(at(3, vec![Projection::Deref]), Rvalue::Use(u64_const(1))),
        assign(Place::local(3), Rvalue::AddressOf(true, Place::local(2))),
        assign(at(3, vec![Projection::Deref]), Rvalue::Use(u64_const(2))),
    ];
    one_block(
        name,
        vec![Ty::u64(), Ty::u64(), Ty::u64(), raw_mut(Ty::u64())],
        stmts,
        Read::Addr { place: Place::local(k), pointee: Ty::u64(), how: How::Value },
    )
}

/// `let mut a = (1, 2); let mut b = (3, 4); let mut p = &raw mut a;
/// let q = &raw const (*p).1; p = &raw mut b; &raw const (*p).0` — the second
/// address is b's, not a's.
fn address_through_a_reassigned_pointer(name: &str) -> VerifiableFunction {
    let stmts = vec![
        assign(Place::local(1), tuple_of(&[1, 2])),
        assign(Place::local(2), tuple_of(&[3, 4])),
        assign(Place::local(3), Rvalue::AddressOf(true, Place::local(1))),
        assign(
            Place::local(4),
            Rvalue::AddressOf(false, at(3, vec![Projection::Deref, Projection::Field(1)])),
        ),
        assign(Place::local(3), Rvalue::AddressOf(true, Place::local(2))),
    ];
    one_block(
        name,
        vec![
            Ty::u64(),
            pair(),
            pair(),
            raw_mut(pair()),
            Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u64()) },
        ],
        stmts,
        Read::Addr {
            place: at(3, vec![Projection::Deref, Projection::Field(0)]),
            pointee: Ty::u64(),
            how: How::Value,
        },
    )
}

/// Every write and address through `p` follows p's CURRENT value. At
/// bed6567522 `resolve_place_addr` started from p's spill slot, written once
/// when p's address was first needed and never again, so every later write
/// through p went to a's storage: a.0 read 7 (Rust: 5) and b read (3, 4)
/// (Rust: (7, 8)). The scalar twin predates the branch (a = 2, b = 20), and a
/// read of `*p` already used p's value, so reads and writes through one
/// pointer disagreed.
#[test]
fn a_write_through_a_reassigned_pointer_lands_in_its_current_referent() {
    run_native(&[
        (
            aggregate_through_a_reassigned_pointer(
                "rp_a0",
                Read::Direct(How::Value, Place::field(1, 0)),
            ),
            5,
        ),
        (
            aggregate_through_a_reassigned_pointer(
                "rp_a1",
                Read::Direct(How::Value, Place::field(1, 1)),
            ),
            6,
        ),
        (
            aggregate_through_a_reassigned_pointer(
                "rp_b0",
                Read::Direct(How::Value, Place::field(2, 0)),
            ),
            7,
        ),
        (
            aggregate_through_a_reassigned_pointer(
                "rp_b1",
                Read::Direct(How::Value, Place::field(2, 1)),
            ),
            8,
        ),
        (
            aggregate_through_a_reassigned_pointer(
                "rp_b1_by_address",
                Read::Addr { place: Place::field(2, 1), pointee: Ty::u64(), how: How::Value },
            ),
            8,
        ),
        (scalar_through_a_reassigned_pointer("rp_scalar_a", 1), 1),
        (scalar_through_a_reassigned_pointer("rp_scalar_b", 2), 2),
        (address_through_a_reassigned_pointer("rp_address_b0"), 3),
    ]);
}

fn drop_fixture(name: &str, locals: Vec<Ty>, place: Place) -> VerifiableFunction {
    let blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Drop {
                unwind: trust_types::UnwindEdge::Unreachable,
                place,
                target: BlockId(1),
                span: SourceSpan::default(),
            },
        },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![assign(Place::local(0), Rvalue::Use(u64_const(0)))],
            terminator: Terminator::Return,
        },
    ];
    function(name, locals, blocks)
}

fn string_like() -> Ty {
    Ty::Adt {
        adt_kind: Some(AdtKind::Struct),
        layout: None,
        name: "alloc::string::String".into(),
        fields: vec![
            ("ptr".to_string(), Ty::i64()),
            ("len".to_string(), Ty::i64()),
            ("cap".to_string(), Ty::i64()),
        ]
        .into(),
        variants: Vec::new().into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    }
}

/// `drop(place)` needs glue when the PLACE's type does, whatever its base
/// local's. rustc emits `drop((*_1))` before `*p = v` on `p: *mut String`.
/// At bed6567522 the terminator typed the place by its base local — a raw
/// pointer, trivially Copy — and lowered both drops below as a plain jump,
/// skipping the glue.
#[test]
fn a_drop_is_typed_by_its_place_not_its_base_local() {
    let deref = drop_fixture(
        "drop_deref_string",
        vec![Ty::u64(), raw_mut(string_like())],
        at(1, vec![Projection::Deref]),
    );
    let err = lowering_error(&deref);
    assert!(err.contains("drop-glue") && err.contains("String"), "{err}");

    let string_and_u64 = Ty::Tuple(vec![string_like(), Ty::u64()]);
    let field = drop_fixture(
        "drop_deref_field_string",
        vec![Ty::u64(), raw_mut(string_and_u64.clone())],
        at(1, vec![Projection::Deref, Projection::Field(0)]),
    );
    let err = lowering_error(&field);
    assert!(err.contains("drop-glue") && err.contains("String"), "{err}");

    // CONTROL: the Copy lane of the same pointee needs no glue.
    let copy_lane = drop_fixture(
        "drop_deref_field_u64",
        vec![Ty::u64(), raw_mut(string_and_u64)],
        at(1, vec![Projection::Deref, Projection::Field(1)]),
    );
    backend().lower_function(&copy_lane).expect("a drop of a u64 lane lowers as a jump");
}

/// `let mut t = (1, 2); let p = &raw mut t; t = (7, 8); (*p).0` is 7. At
/// bed6567522 the whole rebuild rebound `t` to a fresh slot, so p kept
/// addressing the OLD storage and read 1.
#[test]
fn a_whole_rebuild_of_an_address_taken_local_is_seen_through_its_pointer() {
    let stmts = vec![
        assign(Place::local(1), tuple_of(&[1, 2])),
        assign(Place::local(2), Rvalue::AddressOf(true, Place::local(1))),
        assign(Place::local(1), tuple_of(&[7, 8])),
    ];
    let read = |field| Read::Addr {
        place: at(2, vec![Projection::Deref, Projection::Field(field)]),
        pointee: Ty::u64(),
        how: How::Value,
    };
    run_native(&[
        (
            one_block(
                "rebuild_0",
                vec![Ty::u64(), pair(), raw_mut(pair())],
                stmts.clone(),
                read(0),
            ),
            7,
        ),
        (one_block("rebuild_1", vec![Ty::u64(), pair(), raw_mut(pair())], stmts, read(1)), 8),
    ]);
}

/// A write to a field is seen by a later read of the WHOLE local:
/// `let mut t = (7, 9); t.0 = 8; let u = t; u.0` is 8, and so is the same
/// with `t.0` built as an aggregate. At bed6567522 a projected write updated
/// the slot and left t's value stale, so the copy read 7. The lanes past the
/// first word are checked too since the home rule (review 4) copies a whole
/// aggregate byte for byte: before it, a whole-aggregate `Load`/`Store` moved
/// one machine word on AArch64.
#[test]
fn a_field_write_is_seen_by_a_later_whole_copy() {
    let scalar = |name: &str, field: usize| {
        one_block(
            name,
            vec![Ty::u64(), pair(), pair()],
            vec![
                assign(Place::local(1), tuple_of(&[7, 9])),
                assign(Place::field(1, 0), Rvalue::Use(u64_const(8))),
                assign(Place::local(2), Rvalue::Use(Operand::Copy(Place::local(1)))),
            ],
            Read::Direct(How::Value, Place::field(2, field)),
        )
    };
    let nested = Ty::Tuple(vec![pair(), Ty::u64()]);
    let built = |name: &str, lane: Vec<Projection>| {
        one_block(
            name,
            vec![Ty::u64(), nested.clone(), nested.clone(), pair()],
            vec![
                assign(Place::local(3), tuple_of(&[0, 0])),
                assign(
                    Place::local(1),
                    Rvalue::Aggregate(
                        AggregateKind::Tuple,
                        vec![Operand::Move(Place::local(3)), u64_const(5)],
                    ),
                ),
                assign(Place::field(1, 0), tuple_of(&[8, 1])),
                assign(Place::local(2), Rvalue::Use(Operand::Copy(Place::local(1)))),
            ],
            Read::Addr { place: at(2, lane), pointee: Ty::u64(), how: How::Value },
        )
    };
    let f = Projection::Field;
    run_native(&[
        (scalar("field_write_then_copy", 0), 8),
        (scalar("field_write_then_copy_1", 1), 9),
        (built("field_build_then_copy", vec![f(0), f(0)]), 8),
        (built("field_build_then_copy_01", vec![f(0), f(1)]), 1),
        (built("field_build_then_copy_1", vec![f(1)]), 5),
    ]);
}

fn one_field_struct(name: &str) -> Ty {
    Ty::Adt {
        adt_kind: Some(AdtKind::Struct),
        layout: None,
        name: name.into(),
        fields: vec![("x".to_string(), Ty::u64())].into(),
        variants: Vec::new().into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    }
}

fn named_aggregate(aggregate_name: &str, dest_ty: Ty) -> VerifiableFunction {
    let stmts = vec![assign(
        Place::local(1),
        Rvalue::Aggregate(
            AggregateKind::Adt {
                name: aggregate_name.into(),
                variant: 0,
                active_field: None,
                args: None,
            },
            vec![u64_const(7)],
        ),
    )];
    let name = format!("named_{}", adt_name(&dest_ty).replace([':', '<', '>'], "_"));
    one_block(&name, vec![Ty::u64(), dest_ty], stmts, Read::Direct(How::Value, Place::field(1, 0)))
}

/// The aggregate carries the generics-erased path; a generic cut-point type
/// carries the path plus its arguments. `k::G` names `k::G<u64>`, and it does
/// NOT name `k::GBar` (a longer path sharing the prefix) nor `k::G::H`.
#[test]
fn an_aggregate_name_matches_its_generic_instance_and_nothing_longer() {
    run_native(&[(named_aggregate("t216::G", one_field_struct("t216::G<u64>")), 7)]);
    for other in ["t216::GBar", "t216::G::H", "t216::G_"] {
        let err = lowering_error(&named_aggregate("t216::G", one_field_struct(other)));
        assert!(err.contains("t216::G") && err.contains(other), "{other}: {err}");
    }
}
