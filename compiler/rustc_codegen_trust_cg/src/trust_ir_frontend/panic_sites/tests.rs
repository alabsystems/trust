//! Trust (PKG-CP): the pure half of the panic-site pass, against a fake rustc half.

use trust_ir::value::{FuncId, SourceSpan};
use trust_ir::{AssertKind, AssertOverflowOp, Constant, Inst, Linkage, Module, PanicLocation};

use super::*;

/// `rung(x: u64) -> u64 { [..8 items][(x % 12) as usize] }` as the producer stamps it: a
/// remainder check of a constant divisor (constant true), then a bounds check of a run-time
/// index; and a signed `x / 3` with its `MIN / -1` check (`rhs == -1` is constant false, so
/// the conjunction is) and its divide-by-zero check.
const RUNG: &str = r#"module "k"
target "arm64-apple-macosx" 8 little structpass=unclassified
file 0 "src/lib.rs"

functy.0 = (u64) -> (u64)
functy.1 = (i64) -> (i64)

fn @rung(functy.0) {
    ; #producer: trust
bb0(%0: u64):
    %1 = const u64 12  ; #loc: 0 1 10
    %2 = const u64 0  ; #loc: 0 1 10
    %3 = icmp ne u64 %1, %2  ; #loc: 0 1 10
    assert %3, rem_by_zero  ; #loc: 0 1 10
    %4 = urem u64 %0, %1  ; #loc: 0 1 10
    %5 = bitcast u64 %4 to usize  ; #loc: 0 1 10
    %6 = const usize 8  ; #loc: 0 1 20
    %7 = icmp ult usize %5, %6  ; #loc: 0 1 20
    assert %7, bounds_check %5, %6  ; #loc: 0 1 20
    ret %0  ; #loc: 0 1 30
}

fn @third(functy.1) {
    ; #producer: trust
bb0(%0: i64):
    %1 = const i64 3  ; #loc: 0 2 4
    %2 = const i64 0  ; #loc: 0 2 4
    %3 = icmp ne i64 %1, %2  ; #loc: 0 2 4
    assert %3, div_by_zero  ; #loc: 0 2 4
    %4 = const i64 -1  ; #loc: 0 2 4
    %5 = icmp eq i64 %1, %4  ; #loc: 0 2 4
    %6 = const i64 -9223372036854775808  ; #loc: 0 2 4
    %7 = icmp eq i64 %0, %6  ; #loc: 0 2 4
    %8 = and bool %5, %7  ; #loc: 0 2 4
    %9 = const bool true  ; #loc: 0 2 4
    %10 = xor bool %8, %9  ; #loc: 0 2 4
    assert %10, overflow div  ; #loc: 0 2 4
    %11 = sdiv i64 %0, %1  ; #loc: 0 2 4
    ret %11  ; #loc: 0 2 12
}

obligation 0 arithmetic_safety pending "rem_by_zero" function 0 site f0/bb0#3
obligation 1 bounds_check pending "bounds_check" function 0 site f0/bb0#8
obligation 2 arithmetic_safety pending "overflow div" function 1 site f1/bb0#11
"#;

fn rung() -> Module {
    trust_ir::parser::parse_module(RUNG).expect("the fixture parses")
}

const ENTRY: &str = "_RNvNtNtCs0_4core9panicking18panic_bounds_check";

/// A fake rustc half: every kind's entry is `entry(kind)`, every location a 24-byte record
/// `{ file: ptr, len: u64, line: u32, col: u32 }` keyed by the stamp.
#[derive(Default)]
struct Fake {
    refuse_entry: bool,
    refuse_location: bool,
    mir_disagrees: bool,
    track_caller: Vec<String>,
    /// Each `(symbol, lang items)` the MIR oracle was asked about.
    oracle: Vec<(String, Vec<&'static str>)>,
    asked: Vec<String>,
}

fn entry_name(kind: &AssertKind) -> String {
    match kind {
        AssertKind::BoundsCheck { .. } => ENTRY.to_string(),
        other => {
            let name = other.rust_panic_lang_item().unwrap_or("none");
            format!("_RNvNtNtCs0_4core9panicking11panic_const{}{name}", name.len())
        }
    }
}

fn record_for(span: SourceSpan) -> LocationRecord {
    let file = b"src/lib.rs\0";
    let file_symbol = "alloc_0000000000000000000000000000f11e".to_string();
    let mut elements =
        vec![Constant::SymbolAddr { symbol: file_symbol.clone(), addend: 0 }];
    elements.extend((file.len() as u64 - 1).to_le_bytes().map(|b| Constant::Int(b.into())));
    elements.extend(span.line.to_le_bytes().map(|b| Constant::Int(b.into())));
    elements.extend((span.col + 1).to_le_bytes().map(|b| Constant::Int(b.into())));
    LocationRecord {
        record: DataImage {
            symbol: format!("alloc_{:032x}", u128::from(span.line) << 32 | u128::from(span.col)),
            align: 8,
            elements,
        },
        file: DataImage {
            symbol: file_symbol,
            align: 1,
            elements: file.iter().map(|b| Constant::Int((*b).into())).collect(),
        },
    }
}

impl Resolver for Fake {
    fn entry(&mut self, kind: &AssertKind) -> Result<String, String> {
        if self.refuse_entry {
            return Err("no entry".into());
        }
        Ok(entry_name(kind))
    }
    fn location(&mut self, files: &[String], span: SourceSpan) -> Result<LocationRecord, String> {
        assert_eq!(files, ["src/lib.rs".to_string()]);
        if self.refuse_location {
            return Err("no location".into());
        }
        Ok(record_for(span))
    }
    fn reports_own_location(&mut self, symbol: &str) -> Result<(), String> {
        self.asked.push(symbol.to_string());
        if self.track_caller.iter().any(|s| s == symbol) {
            return Err("track_caller".into());
        }
        Ok(())
    }
    fn matches_rustc_mir(
        &mut self,
        symbol: &str,
        checks: &[(AssertKind, LocationRecord)],
    ) -> Result<(), String> {
        let kinds = checks.iter().map(|(k, _)| k.rust_panic_lang_item().unwrap_or("none")).collect();
        self.oracle.push((symbol.to_string(), kinds));
        if self.mir_disagrees {
            return Err("no such MIR `Assert`".into());
        }
        Ok(())
    }
}

fn asserts(m: &Module, name: &str) -> Vec<Inst> {
    m.functions
        .iter()
        .find(|f| f.name == name)
        .expect("the function")
        .blocks
        .iter()
        .flat_map(|b| b.body.iter())
        .filter(|n| matches!(n.inst, Inst::Assert { .. }))
        .map(|n| n.inst.clone())
        .collect()
}

#[test]
fn constant_truth_is_read_off_the_function_s_own_definitions() {
    let m = rung();
    let f = &m.functions[0];
    let g = &m.functions[1];
    // `12 != 0`, and the signed `3 != 0`.
    assert!(constant_true(f, ValueId::new(3), 64));
    assert!(constant_true(g, ValueId::new(3), 64));
    // A run-time index is not known.
    assert!(!constant_true(f, ValueId::new(7), 64));
    // `!(3 == -1 && x == MIN)`: the conjunction is false whatever `x` is.
    assert!(constant_true(g, ValueId::new(10), 64));
    // The conjunction's run-time half alone is not known.
    assert!(!constant_true(g, ValueId::new(7), 64));
    // Signedness: -1 is below 0 signed and above it unsigned.
    let text = r#"module "k"
functy.0 = () -> (bool)
fn @f(functy.0) {
bb0():
    %0 = const i8 -1
    %1 = const i8 0
    %2 = icmp slt i8 %0, %1
    %3 = icmp ult i8 %0, %1
    ret %2
}
"#;
    let m = trust_ir::parser::parse_module(text).expect("parses");
    assert!(constant_true(&m.functions[0], ValueId::new(2), 64));
    assert!(!constant_true(&m.functions[0], ValueId::new(3), 64));
    // A block parameter is never known.
    assert!(!constant_true(&rung().functions[0], ValueId::new(0), 64));
}

#[test]
fn a_constant_check_is_folded_and_a_run_time_one_is_sited() {
    let before = rung();
    let mut m = before.clone();
    let mut fake = Fake::default();
    let report = site(&mut m, &mut fake);
    assert!(report.refusals.is_empty(), "{report:?}");
    // `rung`: the remainder check folds, the bounds check is sited; `third`: both of its
    // checks fold.
    assert_eq!((report.folded, report.sited), (3, 1));
    assert!(asserts(&m, "third").is_empty());
    let kept = asserts(&m, "rung");
    let [Inst::Assert { kind, site: Some(site), .. }] = kept.as_slice() else {
        panic!("rung keeps exactly one sited check: {kept:?}");
    };
    assert!(matches!(kind, AssertKind::BoundsCheck { .. }));
    let entry = m.function_by_id(site.entry).expect("the entry");
    assert_eq!(entry.name, ENTRY);
    assert!(entry.is_declaration() && entry.linkage == Linkage::External);
    assert_eq!(
        m.func_type(entry.ty).expect("signed"),
        &FuncTy { params: vec![Ty::Usize, Ty::Usize, Ty::Ptr], returns: vec![], is_vararg: false, abi: None }
    );
    let PanicLocation::Global(record) = site.location else { panic!("a global location") };
    let record = &m.globals[record.as_usize()];
    let expected = record_for(SourceSpan { file: 0, line: 1, col: 20 });
    assert_eq!(record.name, expected.record.symbol);
    assert!(!record.mutable && record.tls.is_none() && record.linkage == Linkage::Internal);
    assert_eq!(record.align, Some(8));
    // The record is the canonical packed image of exactly rustc's bytes, and its pointer
    // names the file-name global, which the pass added too.
    let image = trust_cg_bridge::global_image::flat_image_elements(
        &m,
        &record.ty,
        record.initializer.as_ref().expect("initialized"),
    );
    assert_eq!(image.as_deref(), Some(expected.record.elements.as_slice()));
    let file = m.globals.iter().find(|g| g.name == expected.file.symbol).expect("the file");
    assert_eq!(file.align, Some(1));
    assert_eq!(m.globals.len(), before.globals.len() + 2);
    // Only `rung` needed a location of its own, and the MIR oracle saw exactly its one site.
    assert_eq!(fake.asked, vec!["rung".to_string()]);
    assert_eq!(fake.oracle, vec![("rung".to_string(), vec!["panic_bounds_check"])]);
    // An obligation on a folded check keeps its row but loses its site; one on a kept check
    // moves with it (the bounds check is now node 7 of `rung`, one folded node before it).
    let sites: Vec<_> = m.proof_obligations.iter().map(|o| o.site).collect();
    assert_eq!(
        sites,
        vec![
            None,
            Some(trust_ir::ObligationSite::new(FuncId::new(0), trust_ir::value::BlockId::new(0), 7)),
            None,
        ]
    );
    assert!(matches!(
        m.functions[0].blocks[0].body[7].inst,
        Inst::Assert { kind: AssertKind::BoundsCheck { .. }, .. }
    ));
    check_postcondition(&before, &m, 64).expect("the pass keeps its own postcondition");
}

#[test]
fn checks_at_one_location_share_one_record_and_one_entry() {
    let mut m = rung();
    // A second bounds check at the same stamp, after the first.
    let body = &mut m.functions[0].blocks[0].body;
    let at = body.iter().position(|n| matches!(n.inst, Inst::Assert { kind: AssertKind::BoundsCheck { .. }, .. })).unwrap();
    let twin = body[at].clone();
    body.insert(at + 1, twin);
    let before = m.clone();
    let report = site(&mut m, &mut Fake::default());
    assert!(report.refusals.is_empty(), "{report:?}");
    assert_eq!(report.sited, 2);
    assert_eq!(m.functions.len(), before.functions.len() + 1);
    assert_eq!(m.globals.len(), before.globals.len() + 2);
}

// Trust (CP-IMAGE-POINTER-EXTENT): compare typed relocation extents at the actual interner.
#[test]
fn an_exact_existing_panic_image_is_reused_without_changing_the_module() {
    let mut m = rung();
    let image = record_for(SourceSpan { file: 0, line: 1, col: 20 }).record;
    let id = intern_image(&mut m, &image, 8).expect("the original eight-byte image");
    let before = m.clone();

    assert_eq!(intern_image(&mut m, &image, 8).expect("the same typed image"), id);
    assert_eq!(m, before, "reuse must not append a duplicate type, struct or global");
}

#[test]
fn a_panic_image_with_another_pointer_extent_cannot_be_reused() {
    for original_pointer_bytes in [4, 16] {
        let mut m = rung();
        let image = record_for(SourceSpan { file: 0, line: 1, col: 20 }).record;
        let id = intern_image(&mut m, &image, original_pointer_bytes)
            .expect("a typed image with a different pointer extent");
        let global = &m.globals[id.as_usize()];
        // The old comparison loses precisely this distinction: both typed images
        // flatten to the same byte/relocation elements.
        assert_eq!(
            trust_cg_bridge::global_image::flat_image_elements(
                &m,
                &global.ty,
                global.initializer.as_ref().expect("initialized"),
            ),
            Some(image.elements.clone()),
        );
        let before = m.clone();

        let error = intern_image(&mut m, &image, 8)
            .expect_err("matching relocations do not establish their storage extent");
        assert!(error.contains(&image.symbol), "{error}");
        assert_eq!(m, before, "a conflicting identity must leave every catalog unchanged");
    }
}

#[test]
fn a_conflicting_panic_image_refuses_siting_and_rolls_back_the_module() {
    let mut m = rung();
    let images = record_for(SourceSpan { file: 0, line: 1, col: 20 });
    intern_image(&mut m, &images.file, 8).expect("the existing file image");
    intern_image(&mut m, &images.record, 16).expect("the conflicting record image");
    let before = m.clone();

    let report = site(&mut m, &mut Fake::default());
    assert_eq!((report.folded, report.sited), (0, 0));
    assert!(!report.refusals.is_empty(), "{report:?}");
    assert!(
        report.refusals.iter().all(|r| {
            r.class() == super::super::RefusalClass::UnfaithfulPanic
                && r.to_string().contains(&images.record.symbol)
        }),
        "{report:?}"
    );
    assert_eq!(m, before, "entry interning, check folding and all other changes roll back");
}

#[test]
fn a_check_that_cannot_be_sited_refuses_its_function_and_changes_nothing() {
    let cases: Vec<(&str, Box<dyn Fn(&mut Module, &mut Fake)>)> = vec![
        ("the entry", Box::new(|_, f| f.refuse_entry = true)),
        ("the location", Box::new(|_, f| f.refuse_location = true)),
        ("track_caller", Box::new(|_, f| f.track_caller = vec!["rung".into()])),
        ("rustc's MIR", Box::new(|_, f| f.mir_disagrees = true)),
        (
            "an unadmitted kind",
            Box::new(|m, _| {
                for n in &mut m.functions[0].blocks[0].body {
                    if let Inst::Assert { kind, .. } = &mut n.inst
                        && matches!(kind, AssertKind::BoundsCheck { .. })
                    {
                        *kind = AssertKind::Unspecified;
                    }
                }
            }),
        ),
        (
            "no span",
            Box::new(|m, _| {
                for n in &mut m.functions[0].blocks[0].body {
                    if matches!(n.inst, Inst::Assert { kind: AssertKind::BoundsCheck { .. }, .. }) {
                        n.span = None;
                    }
                }
            }),
        ),
    ];
    for (what, setup) in cases {
        let mut m = rung();
        let mut fake = Fake::default();
        setup(&mut m, &mut fake);
        let before = m.clone();
        let report = site(&mut m, &mut fake);
        assert_eq!(report.refusals.len(), 1, "{what}: {report:?}");
        let refusal = &report.refusals[0];
        assert_eq!(refusal.class(), super::super::RefusalClass::UnfaithfulPanic, "{what}");
        assert!(refusal.to_string().contains("`rung`") || refusal.sample_line().contains("rung"), "{what}");
        // `rung` is untouched (its constant check is not folded either); `third`, whose
        // checks are all constant, is still folded.
        assert_eq!(m.functions[0], before.functions[0], "{what}");
        assert!(asserts(&m, "third").is_empty(), "{what}");
        assert_eq!(m.globals.len(), before.globals.len(), "{what}");
    }
}

#[test]
fn an_entry_symbol_names_its_lang_item_as_one_identifier() {
    let v0 = "_RNvNtNtCs1a2b_4core9panicking11panic_const24panic_const_add_overflow";
    let legacy = "__ZN4core9panicking11panic_const24panic_const_add_overflow17h0123456789abcdefE";
    for symbol in [v0, legacy] {
        assert!(names_lang_item(symbol, "panic_const_add_overflow"), "{symbol}");
        assert!(!names_lang_item(symbol, "panic_const_sub_overflow"), "{symbol}");
    }
    // A longer length that merely ends in the right digits is another identifier.
    assert!(!names_lang_item("_RNv1124panic_const_add_overflow", "panic_const_add_overflow"));
    assert!(!names_lang_item("_RNvNtNtCs0_4core9panicking18panic_bounds_chec", "panic_bounds_check"));
}

#[test]
fn an_entry_m_cg_already_declares_is_reused() {
    let mut m = rung();
    let ty = trust_ir::value::FuncTyId::new(m.func_types.len() as u32);
    m.func_types.push(FuncTy {
        params: vec![Ty::Usize, Ty::Usize, Ty::Ptr],
        returns: vec![],
        is_vararg: false,
        abi: None,
    });
    let id = FuncId::new(m.functions.len() as u32);
    let mut declaration = trust_ir::Function::new(id, ENTRY, ty, trust_ir::value::BlockId::new(0));
    declaration.linkage = Linkage::External;
    m.functions.push(declaration);
    let before = m.clone();
    let report = site(&mut m, &mut Fake::default());
    assert!(report.refusals.is_empty(), "{report:?}");
    assert_eq!(report.sited, 1);
    assert_eq!(m.functions.len(), before.functions.len(), "no second declaration");
    let kept = asserts(&m, "rung");
    let [Inst::Assert { site: Some(site), .. }] = kept.as_slice() else {
        panic!("one sited check: {kept:?}")
    };
    assert_eq!(site.entry, id);
}

#[test]
fn an_overflow_entry_takes_only_the_location_and_a_bounds_entry_two_usizes_first() {
    assert_eq!(
        entry_signature(&AssertKind::Overflow(AssertOverflowOp::Add)).params,
        vec![Ty::Ptr]
    );
    assert_eq!(entry_signature(&AssertKind::RemByZero).params, vec![Ty::Ptr]);
    let bounds = AssertKind::BoundsCheck { index: ValueId::new(0), len: ValueId::new(1) };
    assert_eq!(entry_signature(&bounds).params, vec![Ty::Usize, Ty::Usize, Ty::Ptr]);
    for kind in [AssertKind::Unspecified, AssertKind::NullPtr] {
        assert!(!admitted(&kind), "{kind:?}");
    }
}

#[test]
fn the_postcondition_refuses_every_other_change() {
    let before = rung();
    let mut sited = before.clone();
    assert!(site(&mut sited, &mut Fake::default()).refusals.is_empty());
    check_postcondition(&before, &sited, 64).expect("the honest result");

    let mutants: Vec<(&str, Box<dyn Fn(&mut Module)>)> = vec![
        ("a run-time check deleted", Box::new(|m| {
            m.functions[0].blocks[0].body.retain(|n| !matches!(n.inst, Inst::Assert { .. }));
        })),
        ("an operation changed", Box::new(|m| {
            for n in &mut m.functions[0].blocks[0].body {
                if let Inst::Const { value, .. } = &mut n.inst
                    && *value == Constant::Int(8)
                {
                    *value = Constant::Int(9);
                }
            }
        })),
        ("a site pointing at a body", Box::new(|m| {
            for n in &mut m.functions[0].blocks[0].body {
                if let Inst::Assert { site: Some(site), .. } = &mut n.inst {
                    site.entry = FuncId::new(1);
                }
            }
        })),
        ("a mutable record", Box::new(|m| {
            let last = m.globals.len() - 1;
            m.globals[last].mutable = true;
        })),
        ("a defined entry", Box::new(|m| {
            let last = m.functions.len() - 1;
            m.functions[last].linkage = Linkage::Internal;
        })),
        ("a node added", Box::new(|m| {
            m.functions[1].blocks[0].body.insert(0, trust_ir::InstrNode::new(Inst::Unreachable));
        })),
        ("the file table", Box::new(|m| m.files.push("other.rs".into()))),
        ("an obligation left on its old index", Box::new(|m| {
            if let Some(at) = &mut m.proof_obligations[1].site {
                at.inst_index = 8;
            }
        })),
        ("a folded check's obligation still sited", Box::new(|m| {
            m.proof_obligations[0].site =
                Some(trust_ir::ObligationSite::new(FuncId::new(0), trust_ir::value::BlockId::new(0), 2));
        })),
        ("an obligation's status changed", Box::new(|m| {
            m.proof_obligations[1].status = trust_ir::ProofStatus::Trusted;
        })),
        ("the module renamed", Box::new(|m| m.name.push('x'))),
        ("an entry named for another lang item", Box::new(|m| {
            let last = m.functions.len() - 1;
            m.functions[last].name = "_RNvNtNtCs0_4core9panicking18panic_bounds_chex".into();
        })),
        ("a function's producer changed", Box::new(|m| {
            m.functions[0].producer = None;
        })),
        ("a new function signed as no entry", Box::new(|m| {
            let last = m.functions.len() - 1;
            let ty = m.functions[last].ty;
            m.func_types[ty.as_usize()].returns = vec![Ty::Usize];
        })),
    ];
    for (what, mutate) in mutants {
        let mut m = sited.clone();
        mutate(&mut m);
        assert!(check_postcondition(&before, &m, 64).is_err(), "{what} was accepted");
    }
}
