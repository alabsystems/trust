//! Spec-side unit tests for register aggregates. The positive modules are the producer's own
//! `-Ztrust-dump=ir:` output for ladder rungs s14, s15, s16 and s23 (trustc ac76a2c1a,
//! `-Ztrust-ir-lower=on -Coverflow-checks=off`), with the `#loc`/`#scope` comments dropped.

use super::*;

const HEAD: &str = r#"; TrustIr text format v1
module "rung"
target "arm64-apple-macosx" 8 little structpass=unclassified

struct @P { a: u64 @0, b: u64 @8 } size=16 align=8 id=0

functy.0 = (u64) -> (u64)

type ty.0 = u64
type ty.1 = u32

enum @E repr(u64) { A = 0, B(u64) = 1 } layout(direct tag@0 size=16 align=8 offsets=[[], [8]]) id=0
enum @F repr(u8) { A = 7, B(u64) = 3 } layout(direct tag@0 size=16 align=8 offsets=[[], [8]]) id=1
enum @G repr(i8) { A = -1, B(u64) = 0 } layout(direct tag@0 size=16 align=8 offsets=[[], [8]]) id=2
"#;

fn module(body: &str) -> Module {
    let text = format!(
        "{HEAD}\nfn @rung(functy.0) {{\n    ; #producer: trust\nbb0(%0: u64):\n{body}\n}}\n"
    );
    trust_ir::parser::parse_module(&text).unwrap_or_else(|e| panic!("{e:?}\n{text}"))
}

fn evaluate(module: &Module) -> Result<SpecResult, String> {
    let maps = BTreeMap::new();
    let input = CerInput {
        m_cg: module,
        producers: &[],
        bodies: &maps,
        placements: &BTreeMap::new(),
        object: &[],
        relocation_model: RelocationModel::Static,
    };
    let function = &module.functions[0];
    let signature = signature_of(module, function.ty)?;
    let placement = FnPlacement {
        params: vec![ParamPlace::Scalar(ScalarPlace::gpr(0, 64))],
        ret: ReturnPlace::Scalar(ScalarPlace::gpr(0, 64)),
    };
    check_placement(module, &signature, function.calling_conv, &placement, true)
        .map_err(|e| format!("{e:?}"))?;
    eval_spec(&input, module, function, &signature, &placement, &BTreeMap::new())
}

/// `(x+1, x*2)` built as the producer builds it; the reads are the lanes.
const S14: &str = "    %1 = const u64 1
    %2 = add u64 %0, %1
    %3 = const u64 2
    %4 = mul u64 %0, %3
    %5 = const (u64, u64) { 0, 0 }
    %6 = insertfield (u64, u64) %5, 0, %2
    %7 = insertfield (u64, u64) %6, 1, %4";

const S15: &str = "    %1 = const u64 1
    %2 = add u64 %0, %1
    %3 = const u64 2
    %4 = mul u64 %0, %3
    %5 = const struct.0 { 0, 0 }
    %6 = insertfield struct.0 %5, 0, %2
    %7 = insertfield struct.0 %6, 1, %4";

const S16: &str = "    %1 = const u64 2
    %2 = const u64 3
    %3 = const u64 4
    %4 = const [ty.0 x 4] splat[ 0; 4 ]
    %5 = const i64 0
    %6 = insertelement [ty.0 x 4] %4, %5, %0
    %7 = const i64 1
    %8 = insertelement [ty.0 x 4] %6, %7, %1
    %9 = const i64 2
    %10 = insertelement [ty.0 x 4] %8, %9, %2
    %11 = const i64 3
    %12 = insertelement [ty.0 x 4] %10, %11, %3";

const S16_READS: &str = "    %13 = const usize 0
    %14 = const usize 4
    %15 = icmp ult usize %13, %14
    assert %15, bounds_check %13, %14
    %16 = const i64 0
    %17 = extractelement u64 %12, %16
    %18 = const usize 3
    %19 = const usize 4
    %20 = icmp ult usize %18, %19
    assert %20, bounds_check %18, %19
    %21 = const i64 3
    %22 = extractelement u64 %12, %21
    %23 = add u64 %17, %22
    ret %23";

fn same_value(aggregate: &SpecResult, scalar: &SpecResult) {
    assert_eq!(format!("{:?}", aggregate.value), format!("{:?}", scalar.value));
    assert_eq!(format!("{:?}", aggregate.reach), format!("{:?}", scalar.reach));
    assert!(aggregate.side.is_empty());
}

/// Each modeled aggregate evaluates to exactly the formula of its scalar twin: the lane holds
/// the inserted value, untouched, and a seed lane is its literal.
#[test]
fn aggregate_lanes_equal_their_scalar_twin() {
    let twin = evaluate(&module(
        "    %1 = const u64 1
    %2 = add u64 %0, %1
    %3 = const u64 2
    %4 = mul u64 %0, %3
    %10 = xor u64 %2, %4
    ret %10",
    ))
    .unwrap();
    for build in [S14, S15] {
        let reads = "    %8 = extractfield u64 %7, 0
    %9 = extractfield u64 %7, 1
    %10 = xor u64 %8, %9
    ret %10";
        let spec = evaluate(&module(&format!("{build}\n{reads}"))).unwrap();
        same_value(&spec, &twin);
        assert!(spec.checks.is_empty());
    }
    // A field read swapped against the twin is a different formula (`t.1 - t.0`).
    let swapped = evaluate(&module(&format!(
        "{S14}\n    %8 = extractfield u64 %7, 1\n    %9 = extractfield u64 %7, 0\n    %10 = sub u64 %8, %9\n    ret %10"
    )))
    .unwrap();
    let forward = evaluate(&module(&format!(
        "{S14}\n    %8 = extractfield u64 %7, 0\n    %9 = extractfield u64 %7, 1\n    %10 = sub u64 %8, %9\n    ret %10"
    )))
    .unwrap();
    assert_ne!(format!("{:?}", swapped.value), format!("{:?}", forward.value));

    let spec = evaluate(&module(&format!("{S16}\n{S16_READS}"))).unwrap();
    let twin =
        evaluate(&module("    %3 = const u64 4\n    %23 = add u64 %0, %3\n    ret %23")).unwrap();
    // The value is the twin's; the reach also carries the two closed bounds guards.
    assert_eq!(format!("{:?}", spec.value), format!("{:?}", twin.value));
    assert_eq!(spec.checks.len(), 2, "both bounds checks are recorded");
    // A seed lane that was never written reads as its literal: `a[1]` of `splat[0; 4]` with only
    // `a[0]` written.
    let seed = evaluate(&module(
        "    %4 = const [ty.0 x 4] splat[ 7; 4 ]
    %5 = const i64 0
    %6 = insertelement [ty.0 x 4] %4, %5, %0
    %7 = const i64 1
    %8 = extractelement u64 %6, %7
    ret %8",
    ))
    .unwrap();
    assert_eq!(seed.value, Formula::BitVec { value: 7, width: 64 });
}

/// Everything the interpreter calls UB or a type error, and every use of an aggregate that is
/// not an insert or extract, stays outside the fragment.
#[test]
fn refusals_are_unknown() {
    let cases: &[(&str, String)] = &[
        ("field past the last", format!("{S14}\n    %8 = extractfield u64 %7, 2\n    ret %8")),
        ("insert past the last", format!("{S14}\n    %8 = insertfield (u64, u64) %7, 2, %0\n    %9 = extractfield u64 %8, 0\n    ret %9")),
        (
            "insert of another type, same width",
            format!(
                "{S14}\n    %8 = const i64 1\n    %9 = insertfield (u64, u64) %7, 0, %8\n    %10 = extractfield u64 %9, 0\n    ret %10"
            ),
        ),
        (
            "insert of another type",
            format!("{S14}\n    %8 = const u32 1\n    %9 = insertfield (u64, u64) %7, 0, %8\n    %10 = extractfield u64 %9, 0\n    ret %10"),
        ),
        ("extract at another type", format!("{S14}\n    %8 = extractfield u32 %7, 0\n    %9 = zext u32 %8 to u64\n    ret %9")),
        ("extract at another type, same width", format!("{S14}\n    %8 = extractfield i64 %7, 0\n    ret %8")),
        ("insert type differs", format!("{S14}\n    %8 = insertfield struct.0 %7, 0, %0\n    %9 = extractfield u64 %8, 0\n    ret %9")),
        ("ptr lane", "    %5 = const (u64, ptr) { 0, 0 }\n    %6 = extractfield u64 %5, 0\n    ret %6".into()),
        ("bool lane", "    %5 = const (u64, bool) { 0, false }\n    %6 = extractfield u64 %5, 0\n    ret %6".into()),
        ("u128 lane", "    %5 = const (u64, u128) { 0, 0 }\n    %6 = extractfield u64 %5, 0\n    ret %6".into()),
        ("nested lane", "    %5 = const (u64, (u64, u64)) { 0, { 0, 0 } }\n    %6 = extractfield u64 %5, 0\n    ret %6".into()),
        ("65 lanes", "    %4 = const [ty.0 x 65] splat[ 0; 65 ]\n    %5 = const i64 0\n    %6 = extractelement u64 %4, %5\n    ret %6".into()),
        ("splat length differs", "    %4 = const [ty.0 x 4] splat[ 0; 3 ]\n    %5 = const i64 0\n    %6 = extractelement u64 %4, %5\n    ret %6".into()),
        ("lane count differs", "    %5 = const (u64, u64) { 0 }\n    %6 = extractfield u64 %5, 0\n    ret %6".into()),
        ("non-literal index", format!("{S16}\n    %13 = extractelement u64 %12, %0\n    ret %13")),
        ("negative index", format!("{S16}\n    %13 = const i64 -1\n    %14 = extractelement u64 %12, %13\n    ret %14")),
        ("index at the length", format!("{S16}\n    %13 = const i64 4\n    %14 = extractelement u64 %12, %13\n    ret %14")),
        ("element of another type", format!("{S16}\n    %13 = const i64 0\n    %14 = extractelement u32 %12, %13\n    %15 = zext u32 %14 to u64\n    ret %15")),
        ("field of an array", format!("{S16}\n    %13 = extractfield u64 %12, 0\n    ret %13")),
        ("element of a tuple", format!("{S14}\n    %8 = const i64 0\n    %9 = extractelement u64 %7, %8\n    ret %9")),
        ("returned", format!("{S14}\n    ret %7")),
        ("copied", format!("{S14}\n    %8 = copy (u64, u64) %7\n    %9 = extractfield u64 %8, 0\n    ret %9")),
        ("selected", format!("{S14}\n    %8 = const bool true\n    %9 = select (u64, u64) %8, %7, %7\n    %10 = extractfield u64 %9, 0\n    ret %10")),
        (
            "along an edge into another tuple type",
            format!("{S14}\n    br bb1(%7)\nbb1(%8: (u64, u32)):\n    %9 = extractfield u64 %8, 0\n    ret %9"),
        ),
    ];
    for (what, body) in cases {
        let m = module(body);
        assert!(evaluate(&m).is_err(), "{what} was modeled:\n{body}");
    }
    // Along an edge into a parameter of its own type the tuple keeps its lanes: `t.0` is `x + 1`.
    let edge = evaluate(&module(&format!(
        "{S14}\n    br bb1(%7)\nbb1(%8: (u64, u64)):\n    %9 = extractfield u64 %8, 0\n    ret %9"
    )))
    .unwrap();
    let plus_one =
        evaluate(&module("    %1 = const u64 1\n    %2 = add u64 %0, %1\n    ret %2")).unwrap();
    assert_eq!(format!("{:?}", edge.value), format!("{:?}", plus_one.value));
    // The cap is exact: 64 lanes are modeled.
    let at_cap = module(
        "    %4 = const [ty.0 x 64] splat[ 0; 64 ]\n    %5 = const i64 63\n    %6 = extractelement u64 %4, %5\n    ret %6",
    );
    assert_eq!(evaluate(&at_cap).unwrap().value, Formula::BitVec { value: 0, width: 64 });
}

/// A lane literal is reduced modulo 2^width, and one that does not fit its type is refused.
#[test]
fn lane_literals_are_exact() {
    assert_eq!(
        lane_literal(&IrTy::I8, &Constant::Int(-1)).unwrap().value.f,
        Formula::BitVec { value: 255, width: 8 }
    );
    assert!(lane_literal(&IrTy::I8, &Constant::Int(128)).is_err());
    assert!(lane_literal(&IrTy::U8, &Constant::Int(256)).is_err());
    assert!(lane_literal(&IrTy::U8, &Constant::Int(-1)).is_err());
    assert!(lane_literal(&IrTy::Bool, &Constant::Int(0)).is_err());
    assert!(lane_literal(&IrTy::U64, &Constant::Bool(false)).is_err());
}

/// s23 `match if x & 1 == 0 { E::A } else { E::B(x) } { E::A => 5, E::B(y) => y + 1 }`, the
/// producer's blocks: the enum crosses a block edge, and its tag selects a `Switch` arm.
const S23: &str = "    %3 = const u64 1
    %4 = and u64 %0, %3
    %5 = const u64 0
    %6 = icmp eq u64 %4, %5
    condbr %6, bb1, bb2
bb1:
    %7 = const enum.0 { 0 }
    br bb3(%7)
bb2:
    %8 = const enum.0 { 1, 0 }
    %9 = insertfield enum.0 %8, 1, %0
    br bb3(%9)
bb3(%1: enum.0):
    %10 = extractfield u64 %1, 0
    switch %10 [ 0: bb4 default: bb5 ]
bb4:
    %11 = const u64 5
    br bb6(%11)
bb5:
    %12 = extractfield u64 %1, 1
    %13 = const u64 1
    %14 = add u64 %12, %13
    br bb6(%14)
bb6(%2: u64):
    ret %2";

/// The enum's arms meet the literal `Switch` only on their own path: on the `E::A` path the tag
/// lane is the literal 0, so the `E::B` arm, which reads a payload lane `E::A` lacks, is never
/// evaluated there. The value is the scalar twin's.
#[test]
fn enum_local_equals_its_scalar_twin() {
    let spec = evaluate(&module(S23)).unwrap();
    let twin = evaluate(&module(
        "    %3 = const u64 1
    %4 = and u64 %0, %3
    %5 = const u64 0
    %6 = icmp eq u64 %4, %5
    condbr %6, bb1, bb2
bb1:
    %11 = const u64 5
    br bb6(%11)
bb2:
    %13 = const u64 1
    %14 = add u64 %0, %13
    br bb6(%14)
bb6(%2: u64):
    ret %2",
    ))
    .unwrap();
    same_value(&spec, &twin);
}

fn enum_tag_switch(tag_ty: &str, build: &str, case: &str) -> Module {
    module(&format!(
        "{build}
    %10 = extractfield {tag_ty} %9, 0
    switch %10 [ {case}: bb1 default: bb2 ]
bb1:
    %11 = const u64 10
    ret %11
bb2:
    %12 = extractfield u64 %9, 1
    ret %12"
    ))
}

/// The tag lane holds the declared discriminant, not the variant index, at the enum's tag type,
/// and the literal `Switch` compares modulo the selector's width (`-1` at `i8` is the lane 255).
#[test]
fn enum_tags_are_declared_discriminants() {
    // `F::A = 7`: the tag is 7, so case 7 is taken (a variant-index tag, 0, would take the
    // default and read an absent payload).
    let a = enum_tag_switch("u8", "    %9 = const enum.1 { 7 }", "7");
    assert_eq!(evaluate(&a).unwrap().value, Formula::BitVec { value: 10, width: 64 });
    // `F::B(x) = 3`: not case 7; the default reads the payload.
    let b = enum_tag_switch(
        "u8",
        "    %8 = const enum.1 { 3, 0 }\n    %9 = insertfield enum.1 %8, 1, %0",
        "7",
    );
    let x = evaluate(&module("    ret %0")).unwrap();
    same_value(&evaluate(&b).unwrap(), &x);
    // `G::A = -1` at an `i8` tag.
    let g = enum_tag_switch("i8", "    %9 = const enum.2 { -1 }", "-1");
    assert_eq!(evaluate(&g).unwrap().value, Formula::BitVec { value: 10, width: 64 });
}

#[test]
fn literal_switch_compares_modulo_width() {
    use trust_ir::inst::SwitchCase;
    let case = |v: i128, t: u32| SwitchCase {
        value: Constant::Int(v),
        target: BlockId::new(t),
        args: vec![],
    };
    let lit = |v: i128, w: u32| IrValue { f: Formula::BitVec { value: v, width: w }, width: w };
    let cases = [case(3, 1), case(-1, 2), case(255, 3)];
    let d = BlockId::new(9);
    // First match wins; -1 at 8 bits is 255.
    assert_eq!(
        literal_switch_target(&lit(255, 8), &cases, d, &[]).unwrap().unwrap().0,
        BlockId::new(2)
    );
    assert_eq!(
        literal_switch_target(&lit(3, 8), &cases, d, &[]).unwrap().unwrap().0,
        BlockId::new(1)
    );
    assert_eq!(literal_switch_target(&lit(4, 8), &cases, d, &[]).unwrap().unwrap().0, d);
    // At 16 bits, -1 is 65535, not 255.
    assert_eq!(
        literal_switch_target(&lit(255, 16), &cases, d, &[]).unwrap().unwrap().0,
        BlockId::new(3)
    );
    // A selector that is not a literal of its own width is left to the general rule.
    let x = IrValue { f: Formula::Var("X0".into(), Sort::BitVec(64)), width: 64 };
    assert!(literal_switch_target(&x, &cases, d, &[]).unwrap().is_none());
    assert!(
        literal_switch_target(
            &IrValue { f: Formula::BitVec { value: 3, width: 32 }, width: 8 },
            &cases,
            d,
            &[]
        )
        .unwrap()
        .is_none()
    );
    // A case the general rule refuses is refused here too.
    let bad = [SwitchCase { value: Constant::Float(1.0), target: BlockId::new(1), args: vec![] }];
    assert!(literal_switch_target(&lit(1, 8), &bad, d, &[]).is_err());
}

/// A parameter selector keeps the general rule: both arms stay in the value.
#[test]
fn non_literal_switch_keeps_every_arm() {
    let spec = evaluate(&module(
        "    switch %0 [ 0: bb1 default: bb2 ]
bb1:
    %1 = const u64 10
    ret %1
bb2:
    %2 = const u64 20
    ret %2",
    ))
    .unwrap();
    let text = format!("{:?}", spec.value);
    assert!(text.contains("value: 10") && text.contains("value: 20"), "{text}");
}

#[test]
fn enum_refusals_are_unknown() {
    let cases: &[(&str, &str)] = &[
        (
            "absent payload lane",
            "    %9 = const enum.0 { 0 }\n    %10 = extractfield u64 %9, 1\n    ret %10",
        ),
        (
            "tag rewritten",
            "    %9 = const enum.0 { 0 }\n    %10 = insertfield enum.0 %9, 0, %0\n    %11 = extractfield u64 %10, 0\n    ret %11",
        ),
        (
            "insert into an absent lane",
            "    %9 = const enum.0 { 0 }\n    %10 = insertfield enum.0 %9, 1, %0\n    %11 = extractfield u64 %10, 0\n    ret %11",
        ),
        (
            "undeclared discriminant",
            "    %9 = const enum.0 { 5 }\n    %10 = extractfield u64 %9, 0\n    ret %10",
        ),
        (
            "payload count differs",
            "    %9 = const enum.0 { 1 }\n    %10 = extractfield u64 %9, 0\n    ret %10",
        ),
        (
            "tag at another type",
            "    %9 = const enum.1 { 7 }\n    %10 = extractfield u64 %9, 0\n    ret %10",
        ),
        (
            "into a parameter of another type",
            "    %9 = const enum.0 { 0 }\n    br bb1(%9)\nbb1(%8: enum.1):\n    %10 = const u64 1\n    ret %10",
        ),
        (
            "scalar into an enum parameter",
            "    br bb1(%0)\nbb1(%8: enum.0):\n    %10 = const u64 1\n    ret %10",
        ),
        ("enum returned", "    %9 = const enum.0 { 0 }\n    ret %9"),
    ];
    for (what, body) in cases {
        assert!(evaluate(&module(body)).is_err(), "{what} was modeled:\n{body}");
    }
}

/// A literal selector, scalar or aggregate tag, never evaluates the arms it does not take: a
/// refusal inside one (here an aggregate returned) no longer fires, and the value is the taken
/// arm's. The same `Switch` on the parameter still refuses.
#[test]
fn literal_switch_skips_untaken_arms() {
    let arms = "bb1:
    ret %0
bb2:
    %5 = const (u64, u64) { 0, 0 }
    ret %5";
    let spec = evaluate(&module(&format!(
        "    %1 = const u64 0\n    switch %1 [ 0: bb1 default: bb2 ]\n{arms}"
    )))
    .unwrap();
    same_value(&spec, &evaluate(&module("    ret %0")).unwrap());
    assert!(evaluate(&module(&format!("    switch %0 [ 0: bb1 default: bb2 ]\n{arms}"))).is_err());
}
