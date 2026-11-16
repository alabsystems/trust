// tests/compiled_object_reader.rs — the AArch64 Mach-O and ELF object readers of
// the call-event refinement gate: obligation O1 (object binding) and the
// structural half of O2 (increment 5, step 5.2; design
// docs/design/2026-10-01-step2-inc5-real-calls-retarget.md §5 O1).
//
// Every object here is produced by trust-cg's `Compiler::compile`; a refusal
// test then patches the MACHINE side (a byte, a relocation record, a symbol, a
// section name) and requires the named refusal, with the unpatched twin bound
// in the same test.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

mod cer_common;

use cer_common::*;
use trust_cg_bridge::compiled_object::{
    CompiledObject, MachineSiteKind, ObjectExpectations, ObjectFormat, ObjectLayout,
    ObjectRefusalKind, RelocKind, RelocationModel, SectionClass, SymbolBinding, SymbolVisibility,
};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::{CodegenLicensePolicy, CompileError};
use trust_cg_lower::AdapterError;
use trust_ir::inst::{BinOp, Inst};
use trust_ir::value::GlobalId;
use trust_ir::{Constant, Global, Linkage, Module, Ty, Visibility};

fn format_of(triple: &str) -> ObjectFormat {
    if triple == DARWIN { ObjectFormat::MachO } else { ObjectFormat::Elf }
}

fn bind(
    module: &Module,
    object: &[u8],
    triple: &str,
) -> Result<ObjectLayout, trust_cg_bridge::compiled_object::ObjectRefusal> {
    let parsed = CompiledObject::parse(object)?;
    let expect =
        ObjectExpectations::from_module(module, format_of(triple), RelocationModel::Static)?;
    ObjectLayout::bind(parsed, &expect)
}

#[track_caller]
fn assert_refusal(module: &Module, object: &[u8], triple: &str, kind: ObjectRefusalKind) {
    match bind(module, object, triple) {
        Err(r) => assert_eq!(r.kind, kind, "{triple}: wrong refusal: {r}\n{}", disassemble(object)),
        Ok(_) => panic!(
            "{triple}: the patched object was NOT refused ({kind:?})\n{}",
            disassemble(object)
        ),
    }
}

fn global(name: &str, init: Option<i128>) -> Global {
    Global {
        section: None,
        visibility: Visibility::Default,
        retained: false,
        name: name.to_string(),
        ty: Ty::U64,
        mutable: false,
        initializer: init.map(Constant::Int),
        linkage: Linkage::External,
        tls: None,
        align: None,
    }
}

/// `g` declared; `f(x) = g(x) + 1`; `h(x) = g(x) ^ 2` (two callers so the
/// object has two windows after the callee declaration).
fn caller_module(callee_has_body: bool) -> Module {
    let mut mb = ModBuilder::new("reader");
    let s = mb.sig(&[Ty::U64], Some(Ty::U64));
    let g = if callee_has_body {
        mb.define("g", s, Linkage::External, |fb| {
            let k = fb.konst(Ty::U64, 9);
            let out = fb.bin(BinOp::Mul, Ty::U64, fb.p(0), k);
            fb.ret(out);
        })
    } else {
        mb.declare("g", s)
    };
    mb.define("f", s, Linkage::External, |fb| {
        let r = fb.call(g, &[fb.p(0)]);
        let one = fb.konst(Ty::U64, 1);
        let out = fb.bin(BinOp::Add, Ty::U64, r, one);
        fb.ret(out);
    });
    mb.finish()
}

/// `f(x) = g(x) + load(G) + load(E)`: a call, a defined global, an external one.
fn global_module() -> Module {
    let mut mb = ModBuilder::new("reader_globals");
    mb.m.globals.push(global("G", Some(7)));
    mb.m.globals.push(global("E", None));
    let s = mb.sig(&[Ty::U64], Some(Ty::U64));
    let g = mb.declare("g", s);
    mb.define("f", s, Linkage::External, |fb| {
        let r = fb.call(g, &[fb.p(0)]);
        let pg = fb.push_inst(Inst::GlobalAddr { global: GlobalId::new(0) });
        let vg = fb.push_inst(Inst::Load { ty: Ty::U64, ptr: pg, volatile: false, align: None });
        let pe = fb.push_inst(Inst::GlobalAddr { global: GlobalId::new(1) });
        let ve = fb.push_inst(Inst::Load { ty: Ty::U64, ptr: pe, volatile: false, align: None });
        let a = fb.bin(BinOp::Add, Ty::U64, r, vg);
        let out = fb.bin(BinOp::Add, Ty::U64, a, ve);
        fb.ret(out);
    });
    mb.finish()
}

fn kinds(object: &[u8]) -> Vec<RelocKind> {
    let o = CompiledObject::parse(object).expect("parses");
    let mut k: Vec<RelocKind> = o
        .sections
        .iter()
        .filter(|s| s.class == SectionClass::Code)
        .flat_map(|s| s.relocations.iter().map(|r| r.kind))
        .collect();
    k.sort();
    k.dedup();
    k
}

/// NEGATIVE CONTROL for `cer_common::fixture_license` and `cer_common::targeted`:
/// the modules this control compiles (`caller_module` with and without its
/// callee's body, and `global_module`; not `switch_module` or the modules other
/// tests build inline) are claim-less, and under trust-cg's DEFAULT
/// license each is refused by that license (`UnlicensedBody` naming one of its
/// bodies, DG-73) on both formats; and a module with a bodyless declaration
/// (`caller_module(false)`) is refused without its target (`TargetInfoRequired`)
/// even under the fixture license. So every object read here was admitted only
/// by the two things the fixtures state. FAILS if the default starts admitting a claim-less body, or
/// if trust-cg starts guessing the target of an untargeted FFI boundary.
#[test]
fn the_default_license_refuses_the_claim_less_fixtures() {
    for triple in BOTH {
        for module in [caller_module(true), caller_module(false), global_module()] {
            let name = module.name.clone();
            compile_under(&module, triple, OptLevel::O2, fixture_license())
                .unwrap_or_else(|e| panic!("{triple} {name}: the fixture license admits it: {e}"));
            let err = compile_under(&module, triple, OptLevel::O2, CodegenLicensePolicy::default())
                .expect_err("the default license refuses a claim-less body");
            assert!(
                matches!(
                    &*err,
                    CompileError::Adapter(AdapterError::UnlicensedBody { function })
                        if module.functions.iter().any(|f| {
                            !f.blocks.is_empty() && f.body_gate.is_none() && f.name == *function
                        })
                ),
                "{triple} {name}: {err:?}"
            );
        }
        let untargeted = caller_module(false);
        assert!(untargeted.target_info.is_none() && untargeted.requires_target_info());
        let spec = trust_cg_codegen::target::TargetSpec::parse(triple).expect("triple parses");
        let config = trust_cg_codegen::CompilerConfig {
            opt_level: OptLevel::O2,
            parallel: false,
            ..trust_cg_codegen::CompilerConfig::default()
        };
        let err = trust_cg_codegen::Compiler::new_for_target_spec(config, spec)
            .with_codegen_license(fixture_license())
            .compile(&untargeted)
            .err()
            .unwrap_or_else(|| panic!("{triple}: an untargeted FFI boundary compiled"));
        assert!(err.to_string().contains("TargetInfoRequired"), "{triple}: {err}");
    }
}

#[test]
fn macho_branch26_page21_pageoff12_got_load_parsed() {
    let module = global_module();
    let object = compile(&module, DARWIN, OptLevel::O2);
    let k = kinds(&object);
    for want in [
        RelocKind::Branch26,
        RelocKind::Page21,
        RelocKind::PageOff12,
        RelocKind::GotLoadPage21,
        RelocKind::GotLoadPageOff12,
    ] {
        assert!(k.contains(&want), "missing {want:?} in {k:?}\n{}", disassemble(&object));
    }
    // Every relocation is consumed; the function is bound, and Unknown only
    // because symbol addresses are bound at steps 5.7/5.9; the defined global's
    // bytes match its initializer image.
    let layout =
        bind(&module, &object, DARWIN).unwrap_or_else(|e| panic!("{e}\n{}", disassemble(&object)));
    let f = &layout.windows["f"];
    assert!(f.unknown.iter().any(|u| u.contains("address materialization")), "{:?}", f.unknown);
    let roles: Vec<&str> = f.relocations.iter().map(|r| r.role.as_str()).collect();
    assert!(roles.contains(&"call") && roles.contains(&"address"), "{roles:?}");
    assert_eq!(layout.verified_globals, vec!["G".to_string()]);
}

#[test]
fn elf_call26_jump26_adr_prel_add_abs_lo12_parsed() {
    // CALL26 from a call; ADR_PREL_PG_HI21 + ADD_ABS_LO12_NC from a global's
    // address; JUMP26 from the relocated tail call trust-cg emits for
    // `t(x) = g(x)` at O2.
    let mut mb = ModBuilder::new("reader_elf");
    mb.m.globals.push(global("G", Some(7)));
    let s = mb.sig(&[Ty::U64], Some(Ty::U64));
    let sp = mb.sig(&[], Some(Ty::Ptr));
    let g = mb.declare("g", s);
    mb.define("f", s, Linkage::External, |fb| {
        let r = fb.call(g, &[fb.p(0)]);
        let one = fb.konst(Ty::U64, 1);
        let out = fb.bin(BinOp::Add, Ty::U64, r, one);
        fb.ret(out);
    });
    mb.define("addr_of_g", sp, Linkage::External, |fb| {
        let p = fb.push_inst(Inst::GlobalAddr { global: GlobalId::new(0) });
        fb.ret(p);
    });
    mb.define("t", s, Linkage::External, |fb| {
        let r = fb.call(g, &[fb.p(0)]);
        fb.ret(r);
    });
    let module = mb.finish();
    let object = compile(&module, LINUX, OptLevel::O2);
    let k = kinds(&object);
    for want in [RelocKind::Call26, RelocKind::AdrPrelPgHi21, RelocKind::AddAbsLo12Nc] {
        assert!(k.contains(&want), "missing {want:?} in {k:?}\n{}", disassemble(&object));
    }
    // `t(x) = g(x)` is compiled to a relocated tail call: JUMP26.
    assert!(k.contains(&RelocKind::Jump26), "missing Jump26 in {k:?}\n{}", disassemble(&object));
    let layout =
        bind(&module, &object, LINUX).unwrap_or_else(|e| panic!("{e}\n{}", disassemble(&object)));
    let t = &layout.windows["t"];
    assert_eq!(t.sites.len(), 1);
    assert_eq!(t.sites[0].kind, MachineSiteKind::Tail);
    assert_eq!(t.sites[0].reloc, Some(RelocKind::Jump26));
    assert_eq!(t.sites[0].callee.as_deref(), Some("g"));
    let f = &layout.windows["f"];
    assert_eq!(f.sites[0].reloc, Some(RelocKind::Call26));
    let a = &layout.windows["addr_of_g"];
    let ak: Vec<RelocKind> = a.relocations.iter().map(|r| r.kind).collect();
    assert_eq!(
        ak,
        vec![RelocKind::AdrPrelPgHi21, RelocKind::AddAbsLo12Nc],
        "{}",
        disassemble(&object)
    );
}

/// Remove `f`'s call relocation and encode the `bl` with the real
/// displacement to `target_delta` past `g`'s start.
fn unrelocate_call(object: &mut [u8], target_delta: i64) {
    let bl = bl_offsets(object, "f")[0];
    let (record, _, _) = reloc_at(object, bl);
    delete_reloc(object, record);
    let g = symbol_offset(object, "g") as i64;
    patch_word(object, bl, enc_bl(g + target_delta - bl as i64));
}

/// Mach-O `MH_SUBSECTIONS_VIA_SYMBOLS` in `mach_header_64.flags` (offset 24).
const MH_SUBSECTIONS_VIA_SYMBOLS: u32 = 0x2000;

/// Clears `MH_SUBSECTIONS_VIA_SYMBOLS` in a Mach-O object's header, so the
/// linker may not cut its sections at their symbols; ELF objects are left
/// unchanged. Asserts the flag was set.
fn without_subsections(triple: &str, object: &mut [u8]) {
    if triple != DARWIN {
        return;
    }
    let flags = u32::from_le_bytes(object[24..28].try_into().unwrap());
    assert_ne!(flags & MH_SUBSECTIONS_VIA_SYMBOLS, 0, "trust-cg sets MH_SUBSECTIONS_VIA_SYMBOLS");
    object[24..28].copy_from_slice(&(flags & !MH_SUBSECTIONS_VIA_SYMBOLS).to_le_bytes());
}

/// An unrelocated `bl` to exactly another symbol's start, in an object whose
/// sections the linker may not cut at symbols (every ELF object; a Mach-O one
/// with `MH_SUBSECTIONS_VIA_SYMBOLS` cleared), is a call to that symbol.
#[test]
fn unrelocated_bl_to_window_start_is_a_call() {
    for triple in BOTH {
        let module = caller_module(true);
        let mut object = compile(&module, triple, OptLevel::O0);
        let before = bind(&module, &object, triple).unwrap_or_else(|e| panic!("{e}"));
        assert!(before.windows["f"].sites[0].reloc.is_some());
        unrelocate_call(&mut object, 0);
        without_subsections(triple, &mut object);
        let layout = bind(&module, &object, triple)
            .unwrap_or_else(|e| panic!("{triple}: {e}\n{}", disassemble(&object)));
        let f = &layout.windows["f"];
        assert!(f.unknown.is_empty(), "{triple}: {:?}", f.unknown);
        assert_eq!(f.sites.len(), 1);
        assert_eq!(f.sites[0].kind, MachineSiteKind::Call);
        assert_eq!(f.sites[0].callee.as_deref(), Some("g"), "{triple}");
        assert_eq!(f.sites[0].reloc, None);
    }
}

/// `MH_SUBSECTIONS_VIA_SYMBOLS` is a Mach-O header bit: the same bit in an ELF
/// object's `e_flags` does not let the linker cut its sections, so an
/// unrelocated `bl` to `g`'s start is still a call to `g`. FAILS if the reader
/// reads bit 0x2000 of ELF `e_flags` as subsections-via-symbols.
#[test]
fn elf_e_flags_bit_0x2000_is_not_subsections_via_symbols() {
    let module = caller_module(true);
    let mut object = compile(&module, LINUX, OptLevel::O0);
    unrelocate_call(&mut object, 0);
    // Elf64_Ehdr: e_flags @48.
    assert_eq!(u32::from_le_bytes(object[48..52].try_into().unwrap()), 0, "trust-cg's e_flags");
    object[48..52].copy_from_slice(&MH_SUBSECTIONS_VIA_SYMBOLS.to_le_bytes());
    let layout =
        bind(&module, &object, LINUX).unwrap_or_else(|e| panic!("{e}\n{}", disassemble(&object)));
    let f = &layout.windows["f"];
    assert!(f.unknown.is_empty(), "{:?}", f.unknown);
    assert_eq!(f.sites.len(), 1);
    assert_eq!(f.sites[0].callee.as_deref(), Some("g"));
}

/// The same `bl` in a Mach-O object with `MH_SUBSECTIONS_VIA_SYMBOLS` set (as
/// trust-cg emits it) is Unknown: the linker may cut `__text` at `g`, and with
/// no relocation to keep `g` it may dead-strip or move it and leave the
/// displacement aimed at whatever lands there.
#[test]
fn unrelocated_bl_between_mach_o_subsections_is_unknown() {
    let module = caller_module(true);
    let mut object = compile(&module, DARWIN, OptLevel::O0);
    unrelocate_call(&mut object, 0);
    let layout = bind(&module, &object, DARWIN).unwrap_or_else(|e| panic!("{e}"));
    let f = &layout.windows["f"];
    assert!(f.unknown.iter().any(|u| u.contains("MH_SUBSECTIONS_VIA_SYMBOLS")), "{:?}", f.unknown);
    assert_eq!(f.sites.len(), 1);
    assert_eq!(f.sites[0].callee, None);
}

/// An unrelocated TAIL `b` to another symbol's start in a Mach-O object with
/// `MH_SUBSECTIONS_VIA_SYMBOLS` set is Unknown and, unlike a `bl`, does not
/// return: the words after it in `f` are unreached, are not padding, and
/// refuse the object. FAILS if an Unknown tail branch falls through to the
/// next word.
#[test]
fn unrelocated_tail_branch_between_mach_o_subsections_ends_the_path() {
    let module = caller_module(true);
    let mut object = compile(&module, DARWIN, OptLevel::O0);
    unrelocate_call(&mut object, 0);
    let at = bl_offsets(&object, "f")[0];
    let g = symbol_offset(&object, "g") as i64;
    patch_word(&mut object, at, enc_b(g - at as i64));
    assert!(
        function_words(&object, "f").iter().any(|&(off, w)| off > at && w != 0 && w != NOP),
        "{}",
        disassemble(&object)
    );
    assert_refusal(&module, &object, DARWIN, ObjectRefusalKind::UncoveredTextByte);
}

#[test]
fn branch_into_window_middle_is_unknown() {
    for triple in BOTH {
        let module = caller_module(true);
        let mut object = compile(&module, triple, OptLevel::O0);
        unrelocate_call(&mut object, 4);
        let layout = bind(&module, &object, triple).unwrap_or_else(|e| panic!("{triple}: {e}"));
        let f = &layout.windows["f"];
        assert!(
            f.unknown.iter().any(|u| u.contains("not the start of a non-preemptible local extent")),
            "{triple}: {:?}",
            f.unknown
        );
        assert_eq!(f.sites[0].callee, None);
    }
}

#[test]
fn uncovered_text_byte_refuses() {
    for triple in BOTH {
        let module = caller_module(true);
        let object = compile(&module, triple, OptLevel::O2);
        bind(&module, &object, triple)
            .unwrap_or_else(|e| panic!("{triple}: unpatched twin refused: {e}"));
        // The first function's symbol moves one instruction later: its first
        // word now lies in no extent.
        let obj = CompiledObject::parse(&object).unwrap();
        let first = obj
            .symbols
            .iter()
            .filter(|s| s.section.is_some() && (s.name == "f" || s.name == "g"))
            .min_by_key(|s| s.value)
            .unwrap()
            .name
            .clone();
        let mut patched = object.clone();
        shift_symbol(&mut patched, &first, 4);
        assert_refusal(&module, &patched, triple, ObjectRefusalKind::UncoveredTextByte);
    }
}

#[test]
fn unconsumed_text_relocation_refuses() {
    for triple in BOTH {
        let module = caller_module(false);
        let mut object = compile(&module, triple, OptLevel::O2);
        bind(&module, &object, triple)
            .unwrap_or_else(|e| panic!("{triple}: unpatched twin refused: {e}"));
        // The call relocation moves onto `f`'s `ret`: an admitted call kind on
        // an instruction it cannot relocate is consumed by no verdict.
        let ret = function_words(&object, "f")
            .into_iter()
            .rev()
            .find(|(_, w)| *w == RET)
            .expect("f returns")
            .0;
        let bl = bl_offsets(&object, "f")[0];
        let (record, _, _) = reloc_at(&object, bl);
        set_reloc_offset(&mut object, record, ret);
        assert_refusal(&module, &object, triple, ObjectRefusalKind::UnconsumedRelocation);
    }
}

#[test]
fn overlapping_extents_refuse() {
    for triple in BOTH {
        let module = caller_module(true);
        let object = compile(&module, triple, OptLevel::O2);
        bind(&module, &object, triple)
            .unwrap_or_else(|e| panic!("{triple}: unpatched twin refused: {e}"));
        let (gs, fs) = (symbol_offset(&object, "g"), symbol_offset(&object, "f"));
        let (lo, hi) = if gs < fs { ("g", "f") } else { ("f", "g") };
        let mut patched = object.clone();
        if triple == LINUX {
            // st_size runs one instruction into the next function.
            let len = symbol_offset(&object, hi) - symbol_offset(&object, lo);
            set_elf_symbol_size(&mut patched, lo, len + 4);
        } else {
            // The later symbol aliases the earlier one's address.
            let delta = symbol_offset(&object, lo) as i64 - symbol_offset(&object, hi) as i64;
            shift_symbol(&mut patched, hi, delta);
        }
        assert_refusal(&module, &patched, triple, ObjectRefusalKind::OverlappingExtents);
    }
}

#[test]
fn unclassified_section_refuses() {
    for triple in BOTH {
        let module = caller_module(false);
        let object = compile(&module, triple, OptLevel::O2);
        let layout = bind(&module, &object, triple)
            .unwrap_or_else(|e| panic!("{triple}: unpatched twin refused: {e}"));
        eprintln!(
            "[{triple}] sections {:?}; unverified {:?}",
            section_names(&object),
            layout.unverified_sections
        );
        let mut patched = object.clone();
        if triple == DARWIN {
            rename_section(&mut patched, "__text", "__texx");
        } else {
            rename_section(&mut patched, ".text", ".texx");
        }
        assert_refusal(&module, &patched, triple, ObjectRefusalKind::UnclassifiedSection);
    }
}

#[test]
fn binding_mismatch_refuses() {
    for triple in BOTH {
        let module = caller_module(false);
        let object = compile(&module, triple, OptLevel::O2);
        bind(&module, &object, triple)
            .unwrap_or_else(|e| panic!("{triple}: unpatched twin refused: {e}"));
        // (a) the object's symbol is made local while M_cg says External.
        let mut patched = object.clone();
        flip_symbol_binding(&mut patched, "f");
        assert_refusal(&module, &patched, triple, ObjectRefusalKind::BindingMismatch);
        // (b) M_cg says hidden while the object's symbol has default visibility.
        let mut hidden = module.clone();
        hidden.functions.iter_mut().find(|f| f.name == "f").unwrap().visibility =
            Visibility::Hidden;
        assert_refusal(&hidden, &object, triple, ObjectRefusalKind::BindingMismatch);
    }
}

/// `M_cg`'s External PROTECTED definitions bind as global protected symbols
/// on ELF only. Mach-O has no protected visibility: a protected body refuses
/// the expectations (BindingMismatch), and a protected or weak global gets
/// no expected symbol (it is never listed as verified). FAILS if a protected
/// definition is expected with default visibility on ELF, or with any symbol
/// on Mach-O, or if a weak global is expected to have a symbol.
#[test]
fn a_protected_definition_binds_only_on_elf() {
    let mut module = caller_module(true);
    module.functions.iter_mut().find(|f| f.name == "f").unwrap().visibility = Visibility::Protected;
    module.globals.push(Global { visibility: Visibility::Protected, ..global("P", Some(1)) });
    module.globals.push(Global { linkage: Linkage::Weak, ..global("W", Some(2)) });
    let elf = ObjectExpectations::from_module(&module, ObjectFormat::Elf, RelocationModel::Static)
        .unwrap_or_else(|e| panic!("ELF: {e}"));
    let f = &elf.bodies["f"];
    assert_eq!(
        (f.binding, f.symbol_visibility),
        (SymbolBinding::Global, SymbolVisibility::Protected)
    );
    assert_eq!(elf.globals["P"].symbol, Some((SymbolBinding::Global, SymbolVisibility::Protected)));
    assert_eq!(elf.globals["W"].symbol, None);
    let refusal =
        ObjectExpectations::from_module(&module, ObjectFormat::MachO, RelocationModel::Static)
            .expect_err("Mach-O has no protected visibility");
    assert_eq!(refusal.kind, ObjectRefusalKind::BindingMismatch, "{refusal}");
    // With `f` default again, Mach-O binds the module but expects no symbol for
    // the protected or the weak global.
    module.functions.iter_mut().find(|f| f.name == "f").unwrap().visibility = Visibility::Default;
    let macho =
        ObjectExpectations::from_module(&module, ObjectFormat::MachO, RelocationModel::Static)
            .unwrap_or_else(|e| panic!("Mach-O: {e}"));
    assert_eq!(macho.globals["P"].symbol, None);
    assert_eq!(macho.globals["W"].symbol, None);
}

/// Refusal (o) judges only an addend-0 call: a call relocated with a nonzero addend against a
/// symbol that names no callee (here the undefined `g` marked weak, which (o) would refuse) is an
/// Unknown site with no callee, and the object still binds. Named by the mutation sweep of
/// 2026-11-13 (o_addend: dropping the addend test refuses this object). The edit is to the
/// parsed object handed to the public `ObjectLayout::bind`; a parsed object reaches the same
/// case (STB_WEAK `g`, as a_weak_undefined_declaration_refuses_the_object patches it, with the
/// CALL26's r_addend set to 4).
#[test]
fn a_nonzero_addend_call_through_a_weak_declaration_is_unknown_not_refused() {
    use trust_cg_bridge::compiled_object::RelocTarget;
    let module = caller_module(false);
    let object = compile(&module, LINUX, OptLevel::O2);
    let mut parsed = CompiledObject::parse(&object).expect("parses");
    let g = parsed
        .symbols
        .iter()
        .position(|s| s.name == "g" && s.section.is_none())
        .expect("undefined g");
    parsed.symbols[g].weak = true;
    let r = parsed
        .sections
        .iter_mut()
        .flat_map(|s| s.relocations.iter_mut())
        .find(|r| r.kind == RelocKind::Call26 && r.target == RelocTarget::Symbol(g))
        .expect("f's CALL26 to g");
    assert_eq!(r.addend, 0);
    r.addend = 4;
    let expect =
        ObjectExpectations::from_module(&module, ObjectFormat::Elf, RelocationModel::Static)
            .unwrap_or_else(|e| panic!("{e}"));
    let layout = ObjectLayout::bind(parsed, &expect)
        .unwrap_or_else(|e| panic!("refused: {e}\n{}", disassemble(&object)));
    let f = &layout.windows["f"];
    assert_eq!(f.sites.len(), 1);
    assert_eq!(f.sites[0].callee, None);
    assert!(f.unknown.iter().any(|u| u.contains("non-zero addend")), "{:?}", f.unknown);
}

/// Refusal (o) for an undefined global named like a body this object defines LOCAL. Local and
/// global names are separate namespaces, so a linker resolves the undefined `memcpy` to another
/// definition (libc's), never to the LOCAL body of that name; a call relocated against it must
/// not be paired with the local body. Found by the 25th adjudication (the pin paired it too).
/// M_cg defines an internal `memcpy` (a runtime-helper name, so the inventory admits an
/// undefined symbol of that name) and `f` calls it. trust-cg refuses to compile a module-local
/// function under a runtime name, so the object is compiled with the helper named `lcpy` and
/// its LOCAL symbol renamed `memcpy` in the parsed object (another producer's object, as `bind`
/// is public); the parsed object then gains an undefined global `memcpy` and `f`'s call
/// relocation is pointed at it, with addend 0. The renamed object binds.
/// FAILS while the reader names a callee through an undefined global that shares a local body's
/// name.
#[test]
fn an_undefined_global_named_like_a_local_body_does_not_name_it() {
    use trust_cg_bridge::compiled_object::{RelocTarget, Symbol, SymbolKind};
    let helper_module = |name: &str| {
        let mut mb = ModBuilder::new("shadowed_helper");
        let s = mb.sig(&[Ty::U64], Some(Ty::U64));
        let helper = mb.define(name, s, Linkage::Internal, |fb| {
            let one = fb.konst(Ty::U64, 1);
            let out = fb.bin(BinOp::Add, Ty::U64, fb.p(0), one);
            fb.ret(out);
        });
        mb.define("f", s, Linkage::External, |fb| {
            let r = fb.call(helper, &[fb.p(0)]);
            fb.ret(r);
        });
        mb.finish()
    };
    for triple in BOTH {
        let object = compile(&helper_module("lcpy"), triple, OptLevel::O0);
        let module = helper_module("memcpy");
        let format = format_of(triple);
        let expect = ObjectExpectations::from_module(&module, format, RelocationModel::Static)
            .unwrap_or_else(|e| panic!("{triple}: {e}"));
        let mut parsed = CompiledObject::parse(&object).expect("parses");
        let local = parsed.symbols.iter_mut().find(|y| y.name == "lcpy").expect("the helper");
        assert_eq!(local.binding, SymbolBinding::Local, "{triple}: the helper is LOCAL");
        local.raw_name = local.raw_name.replace("lcpy", "memcpy");
        local.name = "memcpy".into();
        let control = ObjectLayout::bind(parsed.clone(), &expect)
            .unwrap_or_else(|e| panic!("{triple}: the renamed object refused: {e}"));
        assert!(control.windows.contains_key("memcpy"), "{triple}: the local body binds");
        let undefined = parsed.symbols.len();
        parsed.symbols.push(Symbol {
            index: undefined,
            raw_name: if format == ObjectFormat::MachO { "_memcpy" } else { "memcpy" }.into(),
            name: "memcpy".into(),
            section: None,
            value: 0,
            binding: SymbolBinding::Global,
            visibility: SymbolVisibility::Default,
            kind: SymbolKind::Undefined,
            size: None,
            weak: false,
        });
        let call = parsed
            .sections
            .iter_mut()
            .filter(|s| s.class == SectionClass::Code)
            .flat_map(|s| s.relocations.iter_mut())
            .find(|r| matches!(r.kind, RelocKind::Call26 | RelocKind::Branch26))
            .unwrap_or_else(|| panic!("{triple}: f's call relocation"));
        call.target = RelocTarget::Symbol(undefined);
        call.addend = 0;
        let refusal = match ObjectLayout::bind(parsed, &expect) {
            Ok(layout) => panic!(
                "{triple}: BOUND: the undefined global `memcpy` names the local body; f's sites \
                 name {:?}",
                layout.windows["f"].sites.iter().map(|s| s.callee.clone()).collect::<Vec<_>>()
            ),
            Err(e) => e,
        };
        assert_eq!(refusal.kind, ObjectRefusalKind::Malformed, "{triple}: {}", refusal.reason);
        assert!(
            refusal.reason.contains("neither the one opening a body"),
            "{triple}: {}",
            refusal.reason
        );
    }
}

/// A Mach-O body may open at an untyped (`NoType`) code symbol (the inventory admits one; only
/// ELF requires `STT_FUNC`), and a BRANCH26 relocated against that very symbol still names its
/// callee. Named by the mutation sweep of 2026-11-13 (o_notype: dropping `NoType` from the
/// body-symbol arm of `names_a_callee` leaves this call without a callee). The edit is to the
/// parsed object handed to the public `ObjectLayout::bind`.
#[test]
fn a_macho_call_through_an_untyped_body_symbol_names_its_callee() {
    use trust_cg_bridge::compiled_object::SymbolKind;
    let module = caller_module(true);
    let object = compile(&module, DARWIN, OptLevel::O0);
    let expect =
        ObjectExpectations::from_module(&module, ObjectFormat::MachO, RelocationModel::Static)
            .unwrap_or_else(|e| panic!("{e}"));
    let mut parsed = CompiledObject::parse(&object).expect("parses");
    // Control: unpatched, f's call names g through g's (Function) symbol.
    let before = ObjectLayout::bind(parsed.clone(), &expect).unwrap_or_else(|e| panic!("{e}"));
    assert_eq!(before.windows["f"].sites[0].callee.as_deref(), Some("g"));
    assert_eq!(before.windows["f"].sites[0].reloc, Some(RelocKind::Branch26));
    let g = parsed
        .symbols
        .iter_mut()
        .find(|s| s.name == "g" && s.section.is_some())
        .expect("defined g");
    assert_eq!(g.kind, SymbolKind::Function);
    g.kind = SymbolKind::NoType;
    let layout = ObjectLayout::bind(parsed, &expect)
        .unwrap_or_else(|e| panic!("refused: {e}\n{}", disassemble(&object)));
    let f = &layout.windows["f"];
    assert_eq!(f.sites.len(), 1);
    assert_eq!(f.sites[0].callee.as_deref(), Some("g"));
    assert_eq!(f.sites[0].reloc, Some(RelocKind::Branch26));
}

/// ELF puts every local symbol before every other one, with `.symtab`'s
/// `sh_info` the first non-local index (binutils reads a global below it as
/// local): a table whose `sh_info` disagrees with its bindings, in either
/// direction, refuses at parse.
#[test]
fn an_elf_symbol_table_split_disagreeing_with_sh_info_refuses() {
    let module = caller_module(false);
    let object = compile(&module, LINUX, OptLevel::O2);
    bind(&module, &object, LINUX).unwrap_or_else(|e| panic!("unpatched twin refused: {e}"));
    let symtab = elf_symtab_header(&object);
    let first_global = u32::from_le_bytes(object[symtab + 44..symtab + 48].try_into().unwrap());
    for moved in [first_global - 1, first_global + 1] {
        let mut patched = object.clone();
        patched[symtab + 44..symtab + 48].copy_from_slice(&moved.to_le_bytes());
        let refusal = CompiledObject::parse(&patched).expect_err("sh_info moved");
        assert_eq!(refusal.kind, ObjectRefusalKind::BindingMismatch, "{refusal}");
        assert!(refusal.to_string().contains("sh_info"), "{refusal}");
    }
}

/// The section-header offset of an ELF object's one `SHT_SYMTAB` section.
fn elf_symtab_header(o: &[u8]) -> usize {
    let shoff = u64::from_le_bytes(o[40..48].try_into().unwrap()) as usize;
    let shnum = usize::from(u16::from_le_bytes([o[60], o[61]]));
    (0..shnum)
        .map(|i| shoff + i * 64)
        .find(|h| u32::from_le_bytes(o[h + 4..h + 8].try_into().unwrap()) == 2)
        .expect("SHT_SYMTAB")
}

// ===========================================================================
// DENSE-SWITCH JUMP TABLES (increment 5 step 5.4.1, INC5.4-JUMPTABLE)
// ===========================================================================
//
// trust-cg lowers a dense switch through `cmp Xi, #k; b.hi; adr Xb, T; ldrsw
// Xo, [Xb, Xi, lsl #2]; add Xt, Xb, Xo; br Xt` with the `k + 1` entry table at
// the end of the function (MEASURED at O0 and O2 on both formats; ELF
// `st_size` covers the table). Before 5.4.1 every such object was refused
// (`UncoveredTextByte`: the `br` stopped the walk and the table's words were
// unreached). Each refusal test below binds its unpatched twin first.

const SWITCH_ARMS: usize = 6;

/// [`assert_refusal`], and the refusal's reason names `needle`.
#[track_caller]
fn assert_refusal_because(
    module: &Module,
    object: &[u8],
    triple: &str,
    kind: ObjectRefusalKind,
    needle: &str,
) {
    match bind(module, object, triple) {
        Err(r) => {
            assert_eq!(r.kind, kind, "{triple}: wrong refusal: {r}\n{}", disassemble(object));
            assert!(r.reason.contains(needle), "{triple}: refused for another reason: {r}");
        }
        Ok(_) => panic!(
            "{triple}: the patched object was NOT refused ({kind:?})\n{}",
            disassemble(object)
        ),
    }
}

const UNREACHED: &str = "cannot be reached from its entry and is not padding";

/// `f(x) = match x { 0 => g(x), 1..=5 => x ^ c_i, _ => 9 }` (`g` declared, so
/// arm 0 carries a call relocation), plus a leaf `h(x) = x ^ 0x77` when
/// `with_h`.
fn switch_module(with_h: bool) -> Module {
    switch_module_with(with_h, false)
}

/// [`switch_module`]; with `shared_default` the default is arm 0's block
/// (`_ => g(x)`), so the bound check's taken target is also reached through
/// the table and redirecting the `b.hi` leaves no word unreached.
fn switch_module_with(with_h: bool, shared_default: bool) -> Module {
    use trust_ir::inst::SwitchCase;
    use trust_ir::value::BlockId;
    let mut mb = ModBuilder::new("reader_switch");
    let s = mb.sig(&[Ty::U64], Some(Ty::U64));
    let g = mb.declare("g", s);
    mb.define("f", s, Linkage::External, |fb| {
        let x = fb.p(0);
        let arms: Vec<BlockId> = (0..SWITCH_ARMS).map(|_| fb.block(&[]).0).collect();
        let default = if shared_default { arms[0] } else { fb.block(&[]).0 };
        fb.push_inst_void(Inst::Switch {
            value: x,
            default,
            default_args: vec![],
            cases: arms
                .iter()
                .enumerate()
                .map(|(i, b)| SwitchCase {
                    value: Constant::Int(i as i128),
                    target: *b,
                    args: vec![],
                })
                .collect(),
            exhaustive_enum_unreachable: false,
        });
        for (i, b) in arms.iter().enumerate() {
            fb.switch_to(*b);
            if i == 0 {
                let r = fb.call(g, &[x]);
                fb.ret(r);
            } else {
                let k = fb.konst(Ty::U64, 0x10 * (i as i128 + 1) + i as i128);
                let out = fb.bin(BinOp::Xor, Ty::U64, x, k);
                fb.ret(out);
            }
        }
        if !shared_default {
            fb.switch_to(default);
            let nine = fb.konst(Ty::U64, 9);
            fb.ret(nine);
        }
    });
    if with_h {
        mb.define("h", s, Linkage::External, |fb| {
            let k = fb.konst(Ty::U64, 0x77);
            let out = fb.bin(BinOp::Xor, Ty::U64, fb.p(0), k);
            fb.ret(out);
        });
    }
    mb.finish()
}

/// Bind the unpatched object and return `f`'s single jump table `[T, end)`.
fn switch_table(module: &Module, object: &[u8], triple: &str) -> (u64, u64) {
    let layout = bind(module, object, triple).unwrap_or_else(|e| {
        panic!("{triple}: unpatched twin refused: {e}\n{}", disassemble(object))
    });
    let f = &layout.windows["f"];
    assert_eq!(f.data_in_code.len(), 1, "{triple}: {:?}\n{}", f.unknown, disassemble(object));
    f.data_in_code[0]
}

/// The offset of the dispatch `br` in `f` (the word ending the matched run).
fn dispatch_br(object: &[u8]) -> u64 {
    function_words(object, "f")
        .into_iter()
        .find(|(_, w)| w & 0xffff_fc1f == 0xd61f_0000)
        .expect("f dispatches through a br")
        .0
}

#[test]
fn jump_table_words_are_data_and_every_entry_is_walked() {
    for triple in BOTH {
        for opt in [OptLevel::O0, OptLevel::O2] {
            let module = switch_module(false);
            let object = compile(&module, triple, opt);
            let layout = bind(&module, &object, triple).unwrap_or_else(|e| {
                panic!("{triple} {opt:?}: refused: {e}\n{}", disassemble(&object))
            });
            let f = &layout.windows["f"];
            let (t0, t1) = f.data_in_code[0];
            assert_eq!(f.data_in_code.len(), 1, "{triple} {opt:?}");
            assert_eq!(t1 - t0, 4 * SWITCH_ARMS as u64, "{triple} {opt:?}: k + 1 entries");
            assert!(
                f.unknown.iter().any(|u| u.contains("dense-switch jump table")
                    && u.contains(&format!("({SWITCH_ARMS} entries)"))
                    && u.contains("INC5.4-JUMPTABLE")),
                "{triple} {opt:?}: {:?}",
                f.unknown
            );
            // Every entry's target is walked, no table word is.
            let br = dispatch_br(&object);
            let targets = &f.successors[&br];
            assert!(!targets.is_empty());
            for off in (t0..t1).step_by(4) {
                let entry = word_at(&object, off) as i32;
                let target = (t0 as i64 + i64::from(entry)) as u64;
                assert!(targets.contains(&target), "{triple} {opt:?}: entry target {target:#x}");
                assert!(f.reachable.contains(&target));
                assert!(
                    !f.reachable.contains(&off),
                    "{triple} {opt:?}: table word {off:#x} walked"
                );
            }
            // Every case block returns, so every `ret` in the function is
            // reached; arm 0's call relocation is consumed by `f`.
            for (off, w) in function_words(&object, "f") {
                if w == RET {
                    assert!(f.reachable.contains(&off), "{triple} {opt:?}: ret at {off:#x}");
                }
            }
            assert!(
                f.sites.iter().any(|s| s.callee.as_deref() == Some("g")),
                "{triple} {opt:?}: {:?}",
                f.sites
            );
            assert!(f.relocations.iter().any(|r| r.symbol.as_deref() == Some("g")));
        }
    }
}

#[test]
fn a_jump_table_that_does_not_match_the_idiom_still_refuses() {
    for triple in BOTH {
        let module = switch_module(false);
        let object = compile(&module, triple, OptLevel::O2);
        let _ = switch_table(&module, &object, triple);
        let br = dispatch_br(&object);
        let (cmp, adr) = (br - 20, br - 12);
        // (a) The bound check's immediate, one lower: k = 4 covers five
        // entries, and the sixth table word is unreached data.
        let mut lower = object.clone();
        let cmp_word = word_at(&object, cmp);
        assert_eq!((cmp_word >> 10) & 0xfff, (SWITCH_ARMS - 1) as u32, "{triple}");
        patch_word(&mut lower, cmp, cmp_word - (1 << 10));
        assert_refusal_because(
            &module,
            &lower,
            triple,
            ObjectRefusalKind::UncoveredTextByte,
            UNREACHED,
        );
        // ... and one higher: the table would run past the extent.
        let mut higher = object.clone();
        patch_word(&mut higher, cmp, cmp_word + (1 << 10));
        assert_refusal_because(
            &module,
            &higher,
            triple,
            ObjectRefusalKind::UncoveredTextByte,
            UNREACHED,
        );
        // (b) `adr` writes another register than the one `ldrsw` reads.
        let mut other = object.clone();
        let adr_word = word_at(&object, adr);
        patch_word(&mut other, adr, (adr_word & !31) | ((adr_word + 3) & 31));
        assert_refusal_because(
            &module,
            &other,
            triple,
            ObjectRefusalKind::UncoveredTextByte,
            UNREACHED,
        );
    }
}

#[test]
fn a_non_padding_word_after_the_table_still_refuses() {
    for triple in BOTH {
        let module = switch_module(true);
        let object = compile(&module, triple, OptLevel::O2);
        let (_, t1) = switch_table(&module, &object, triple);
        // `h` starts right after `f`'s table; moving its symbol one word later
        // leaves its first (non-padding) word in `f`'s extent, past the table.
        assert_eq!(symbol_offset(&object, "h"), t1, "{triple}\n{}", disassemble(&object));
        let mut patched = object.clone();
        shift_symbol(&mut patched, "h", 4);
        if triple == LINUX {
            // Without this the `st_size` check refuses first (bytes past it
            // are not padding); grow it so the coverage walk is what refuses.
            let f_start = symbol_offset(&object, "f");
            set_elf_symbol_size(&mut patched, "f", t1 + 4 - f_start);
            let parsed = CompiledObject::parse(&object).unwrap();
            let h_size = parsed.symbols.iter().find(|s| s.name == "h").unwrap().size.unwrap();
            set_elf_symbol_size(&mut patched, "h", h_size - 4);
        }
        assert_refusal_because(
            &module,
            &patched,
            triple,
            ObjectRefusalKind::UncoveredTextByte,
            UNREACHED,
        );
    }
}

#[test]
fn a_relocation_inside_a_jump_table_refuses_the_object() {
    for triple in BOTH {
        let module = switch_module(false);
        let object = compile(&module, triple, OptLevel::O0);
        let (t0, _) = switch_table(&module, &object, triple);
        let call = bl_offsets(&object, "f")[0];
        let (record, _, _) = reloc_at(&object, call);
        let mut patched = object.clone();
        set_reloc_offset(&mut patched, record, t0 + 4);
        assert_refusal_because(
            &module,
            &patched,
            triple,
            ObjectRefusalKind::UncoveredTextByte,
            "relocates a word of the jump table",
        );
    }
}

#[test]
fn a_jump_table_entry_into_the_table_refuses() {
    for triple in BOTH {
        let module = switch_module(false);
        let object = compile(&module, triple, OptLevel::O2);
        let (t0, _) = switch_table(&module, &object, triple);
        for entry in [0u32, 4] {
            let mut patched = object.clone();
            patch_word(&mut patched, t0, entry);
            assert_refusal_because(
                &module,
                &patched,
                triple,
                ObjectRefusalKind::UncoveredTextByte,
                UNREACHED,
            );
        }
    }
}

/// `b.<cond> .+delta` (condition codes: `EQ` 0, `HI` 8).
fn enc_b_cond(cond: u32, delta: i64) -> u32 {
    0x5400_0000 | ((((delta / 4) as u32) & 0x7_ffff) << 5) | (cond & 0xf)
}
const COND_EQ: u32 = 0;
const COND_HI: u32 = 8;

#[test]
fn a_branch_into_the_dispatch_run_or_the_table_refuses() {
    for triple in BOTH {
        let module = switch_module(false);
        let object = compile(&module, triple, OptLevel::O2);
        let (t0, _) = switch_table(&module, &object, triple);
        let br = dispatch_br(&object);
        // A reachable non-branch word of a case block (the default arm's
        // `mov x0, #9`, which every format emits as `movz x0, #9`). It becomes
        // a CONDITIONAL branch, so the words after it stay reachable and the
        // check named in each needle is the only one that refuses.
        let movz = function_words(&object, "f")
            .into_iter()
            .find(|(_, w)| *w == 0xd280_0120)
            .expect("the default arm's mov x0, #9")
            .0;
        // (a) Into the run past its bound check (the `ldrsw`).
        let mut into_run = object.clone();
        patch_word(&mut into_run, movz, enc_b_cond(COND_EQ, br as i64 - 8 - movz as i64));
        assert_refusal_because(
            &module,
            &into_run,
            triple,
            ObjectRefusalKind::UncoveredTextByte,
            "other than by falling through its bound check",
        );
        // (b) Into the table.
        let mut into_table = object.clone();
        patch_word(&mut into_table, movz, enc_b_cond(COND_EQ, t0 as i64 - movz as i64));
        assert_refusal_because(
            &module,
            &into_table,
            triple,
            ObjectRefusalKind::UncoveredTextByte,
            "lies inside the jump table",
        );
    }
}

#[test]
fn a_bound_check_that_branches_into_its_own_run_still_refuses() {
    // The bound check guards `ldrsw` only when its taken target lies outside
    // the run: `b.hi .+4` lands on the `adr` taken or not, so every index
    // would reach `ldrsw`. The default is shared with arm 0, so no word goes
    // unreached by the patch itself; the matcher's check is what refuses.
    for triple in BOTH {
        for opt in [OptLevel::O0, OptLevel::O2] {
            let module = switch_module_with(false, true);
            let object = compile(&module, triple, opt);
            let _ = switch_table(&module, &object, triple);
            let bhi = dispatch_br(&object) - 16;
            assert_eq!(
                word_at(&object, bhi) & 0xff00_001f,
                0x5400_0008,
                "{triple} {opt:?}: b.hi\n{}",
                disassemble(&object)
            );
            // Every target from the `cmp` to the `br`, the vacuous `.+4` first.
            for delta in [4i64, -4, 0, 8, 12, 16] {
                let mut patched = object.clone();
                patch_word(&mut patched, bhi, enc_b_cond(COND_HI, delta));
                assert_refusal_because(
                    &module,
                    &patched,
                    triple,
                    ObjectRefusalKind::UncoveredTextByte,
                    UNREACHED,
                );
            }
        }
    }
}

// Measured first function from the refused 03e6/CG095f source-stack O3
// Compiler capture 56c9847ad00ba8012547c9541e5c8e57f6ecc13fe0b7138c176ea3c3046bc94f.
// Its compare is scheduled above six stack loads. These exact machine bytes
// exercise the reader, independently of whatever a future compiler emits.
fn scheduled_stack_switch() -> (Module, CompiledObject) {
    use trust_cg_bridge::compiled_object::{Section, Symbol, SymbolBinding, SymbolKind, SymbolVisibility};
    let words: [u32; 36] = [
        0xa9bf7bfd, 0x910003fd, 0x398043a1, 0xf100141f,
        0x394047a2, 0x798027a3, 0x79402ba4, 0xb9401ba5,
        0xb9401fa6, 0xf94013a7, 0x54000208, 0x10000269,
        0xb8a0792a, 0x8b0a0120, 0xd61f0000, 0x2a0603e4,
        0x1400000b, 0x93407ca4, 0x14000009, 0x14000008,
        0xaa0303e4, 0x14000006, 0xaa0203e4, 0x14000004,
        0xaa0103e4, 0x14000002, 0xaa0703e4, 0xaa0403e0,
        0xa8c17bfd, 0xd65f03c0, 0xffffffe8, 0xffffffe0,
        0xffffffd8, 0xffffffd4, 0xffffffcc, 0xffffffc4,
    ];
    let bytes: Vec<u8> = words.into_iter().flat_map(u32::to_le_bytes).collect();
    let mut mb = ModBuilder::new("scheduled_reader");
    let sig = mb.sig(&[Ty::I64], Some(Ty::I64));
    mb.define("trust_stack_int", sig, Linkage::External, |fb| fb.ret(fb.p(0)));
    let object = CompiledObject {
        format: ObjectFormat::MachO,
        sections: vec![Section {
            index: 1, name: "__TEXT,__text".into(), class: SectionClass::Code,
            address: 0, size: bytes.len() as u64, bytes, relocations: vec![],
            // S_REGULAR | S_ATTR_PURE_INSTRUCTIONS | S_ATTR_SOME_INSTRUCTIONS,
            // the only flags word the parser admits for `__TEXT,__text`.
            flags: 0x8000_0400,
        }],
        // No MH_SUBSECTIONS_VIA_SYMBOLS: unrelocated branches pair as on the pin.
        header_flags: 0,
        symbols: vec![Symbol {
            index: 0, raw_name: "_trust_stack_int".into(), name: "trust_stack_int".into(),
            section: Some(1), value: 0, binding: SymbolBinding::Global,
            visibility: SymbolVisibility::Default, kind: SymbolKind::Function,
            size: None, weak: false,
        }],
        sha256: [0; 32], // This structural-reader fixture grants no byte/proof identity.
    };
    (mb.finish(), object)
}

fn bind_scheduled(module: &Module, object: CompiledObject) -> Result<ObjectLayout, trust_cg_bridge::compiled_object::ObjectRefusal> {
    let expect = ObjectExpectations::from_module(module, ObjectFormat::MachO, RelocationModel::Static).unwrap();
    ObjectLayout::bind(object, &expect)
}

fn patch_scheduled(object: &mut CompiledObject, offset: usize, word: u32) {
    object.sections[0].bytes[offset..offset + 4].copy_from_slice(&word.to_le_bytes());
}

#[test]
fn scheduled_stack_loads_preserve_the_complete_switch_bound() {
    let (module, object) = scheduled_stack_switch();
    let layout = bind_scheduled(&module, object).unwrap();
    let window = &layout.windows["trust_stack_int"];
    assert_eq!(window.data_in_code, [(0x78, 0x90)]);
    assert_eq!(window.successors[&0x38], [0x3c, 0x44, 0x4c, 0x50, 0x58, 0x60]);
    assert!((0..0x78).step_by(4).all(|off| window.reachable.contains(&off)));
    assert!((0x78..0x90).step_by(4).all(|off| !window.reachable.contains(&off)));
    assert!(window.unknown.iter().any(|row| row.contains("dense-switch jump table")));
}

#[test]
fn scheduled_switch_refuses_index_flags_and_nonload_mutations() {
    let (module, object) = scheduled_stack_switch();
    for word in [
        0xf94013a0, // ldr x0: overwrites the 64-bit index.
        0xb9401fa0, // ldr w0: overwrites its W alias too.
        0xb10004c6, // adds x6, x6, #1: overwrites NZCV.
        0xf90013a7, // str x7: a store is outside the finite load grammar.
        0xbd401fa6, // ldr s6: SIMD is outside it too.
        0xf84087a7, // ldr x7, [x29], #8: writeback is outside it.
        0xf98013a7, // prfm, not a GPR load.
        0xb9c01fa6, // reserved size/opc combination.
    ] {
        let mut patched = object.clone();
        patch_scheduled(&mut patched, 0x24, word);
        let refusal = bind_scheduled(&module, patched).unwrap_err();
        assert_eq!(refusal.kind, ObjectRefusalKind::UncoveredTextByte, "{word:#x}: {refusal}");
    }
}

#[test]
fn scheduled_switch_refuses_every_kind_of_guard_interior_entry() {
    let (module, object) = scheduled_stack_switch();
    // A default-arm conditional branch keeps its fall-through reachable while
    // adding an outside predecessor to each load and each dispatch-tail word.
    for target in (0x10..=0x38).step_by(4) {
        let mut patched = object.clone();
        patch_scheduled(&mut patched, 0x68, enc_b_cond(COND_EQ, target - 0x68));
        let refusal = bind_scheduled(&module, patched).unwrap_err();
        assert_eq!(refusal.kind, ObjectRefusalKind::UncoveredTextByte, "{target:#x}: {refusal}");
        assert!(refusal.reason.contains("other than by falling through its bound check"), "{refusal}");
    }
    // The taken side of b.hi may not bypass its own compare either.
    for target in (0x0c..=0x38).step_by(4) {
        let mut patched = object.clone();
        patch_scheduled(&mut patched, 0x28, enc_b_cond(COND_HI, target - 0x28));
        assert_eq!(bind_scheduled(&module, patched).unwrap_err().kind, ObjectRefusalKind::UncoveredTextByte);
    }
}

#[test]
fn scheduled_switch_keeps_relocation_and_table_refusals() {
    use trust_cg_bridge::compiled_object::{Relocation, RelocTarget};
    let (module, object) = scheduled_stack_switch();
    for offset in (0x0c..=0x38).step_by(4) {
        let mut patched = object.clone();
        patched.sections[0].relocations.push(Relocation {
            offset, kind: RelocKind::Other { raw: 99 }, target: RelocTarget::Symbol(0),
            addend: 0, pc_relative: false, length: 2,
        });
        assert_eq!(bind_scheduled(&module, patched).unwrap_err().kind, ObjectRefusalKind::UncoveredTextByte);
    }
    let mut patched = object.clone();
    patch_scheduled(&mut patched, 0x78, 0); // entry points into its own table.
    assert_eq!(bind_scheduled(&module, patched).unwrap_err().kind, ObjectRefusalKind::UncoveredTextByte);
    let mut patched = object;
    patch_scheduled(&mut patched, 0x78, 1); // misaligned entry target.
    assert_eq!(bind_scheduled(&module, patched).unwrap_err().kind, ObjectRefusalKind::UncoveredTextByte);
}

/// A zero-fill global is listed in `verified_globals` only when its section
/// header is ORDINARY zero-fill (`ordinary_zero_fill`: Mach-O `__DATA,__bss`
/// with flags exactly S_ZEROFILL; ELF flags exactly SHF_ALLOC|SHF_WRITE) and
/// `M_cg` gives it an expected image that is all zeros and fits its extent.
/// In-memory objects (as in `scheduled_stack_switch`): one zero-fill section of
/// 8 bytes holding the external global `Z`. FAILS if a non-ordinary header,
/// a missing image or an image longer than the extent lists `Z`.
#[test]
fn a_zero_fill_global_is_listed_only_under_an_ordinary_header_with_a_fitting_zero_image() {
    use trust_cg_bridge::compiled_object::{Section, Symbol, SymbolKind};
    const S_ZEROFILL: u64 = 0x1;
    const S_ATTR_NO_DEAD_STRIP: u64 = 0x1000_0000;
    const SHF_WRITE: u64 = 0x1;
    const SHF_ALLOC: u64 = 0x2;
    let mut mb = ModBuilder::new("zero_fill_reader");
    mb.m.globals.push(global("Z", Some(0)));
    let module = mb.finish();
    let listed = |format: ObjectFormat, name: &str, flags: u64, image: Option<Vec<u8>>| {
        let object = CompiledObject {
            format,
            sections: vec![Section {
                index: 1,
                name: name.into(),
                class: SectionClass::ZeroFill,
                address: 0,
                size: 8,
                bytes: vec![],
                relocations: vec![],
                flags,
            }],
            header_flags: 0,
            symbols: vec![Symbol {
                index: 1,
                raw_name: if format == ObjectFormat::MachO { "_Z" } else { "Z" }.into(),
                name: "Z".into(),
                section: Some(1),
                value: 0,
                binding: SymbolBinding::Global,
                visibility: SymbolVisibility::Default,
                kind: SymbolKind::Object,
                size: Some(8),
                weak: false,
            }],
            sha256: [0; 32], // structural fixture: no byte identity
        };
        let mut expect =
            ObjectExpectations::from_module(&module, format, RelocationModel::Static).unwrap();
        expect.globals.get_mut("Z").expect("M_cg's `Z`").image = image;
        let layout = ObjectLayout::bind(object, &expect)
            .unwrap_or_else(|e| panic!("{format:?} `{name}` {flags:#x}: refused: {e}"));
        layout.verified_globals.iter().any(|g| g == "Z")
    };
    let zeros = || Some(vec![0u8; 8]);
    // Ordinary zero-fill with a fitting all-zero image: listed.
    assert!(listed(ObjectFormat::MachO, "__DATA,__bss", S_ZEROFILL, zeros()), "Mach-O __bss");
    assert!(listed(ObjectFormat::Elf, ".bss", SHF_ALLOC | SHF_WRITE, zeros()), "ELF .bss");
    // Not ordinary zero-fill: not listed.
    for (format, name, flags) in [
        (ObjectFormat::MachO, "__DATA,__bss", S_ZEROFILL | S_ATTR_NO_DEAD_STRIP),
        (ObjectFormat::MachO, "__DATA,__common", S_ZEROFILL),
        (ObjectFormat::Elf, ".bss", SHF_ALLOC),
    ] {
        assert!(
            !listed(format, name, flags, zeros()),
            "LISTED: {format:?} `{name}` flags {flags:#x} is not ordinary zero-fill"
        );
    }
    // No expected image, or an all-zero image longer than the 8-byte extent: not listed.
    for (format, name, flags) in [
        (ObjectFormat::MachO, "__DATA,__bss", S_ZEROFILL),
        (ObjectFormat::Elf, ".bss", SHF_ALLOC | SHF_WRITE),
    ] {
        assert!(!listed(format, name, flags, None), "LISTED: {format:?} `Z` has no image");
        assert!(
            !listed(format, name, flags, Some(vec![0u8; 16])),
            "LISTED: {format:?} `Z`'s 16-byte image does not fit its 8-byte extent"
        );
    }
}

/// PKG-C5c S2a: the walk RECORDS a dead tail's Location pair and admits nothing. Ladder rung
/// s21's `M_cg` (`cer_common::sited_div`: the division's check sited at
/// `panic_const_div_by_zero` and an immutable Internal Location record) at O0, both formats:
/// `rung`'s `unknown` is exactly the two address-materialization lines, word for word as before
/// S2a; `page_halves` records both halves with the relocation and the word's fields and the
/// very line each put in `unknown`; `trap_tail` is the run `adrp ..= brk`, and the `bl` in it
/// is `in_trap_tail`. FAILS if the reader admits the pair (drops or rewords a line), records a
/// field wrongly, or exposes another trap-tail set.
#[test]
fn a_dead_tail_location_pair_is_recorded_and_its_unknown_lines_are_unchanged() {
    use trust_cg_bridge::compiled_object::{InsnClass, RelocTarget};
    for triple in BOTH {
        let (m_cg, _) = sited_div(true, DivRecord::Pointer);
        let m_cg = targeted(&m_cg, triple);
        let object = compile(&m_cg, triple, OptLevel::O0);
        let layout = bind(&m_cg, &object, triple)
            .unwrap_or_else(|e| panic!("{triple}: {e}\n{}", disassemble(&object)));
        let w = &layout.windows["rung"];
        let record = symbol_index(&object, DIV_LOCATION);
        let [bl] = bl_offsets(&object, "rung")[..] else { panic!("{triple}: not one `bl`") };
        let mut halves: Vec<u64> = text_relocs(&object)
            .into_iter()
            .filter(|(_, _, ty, sym)| *sym == record && !(triple == DARWIN && *ty == 10))
            .map(|(_, at, _, _)| at)
            .collect();
        halves.sort_unstable();
        let [adrp, add] = halves[..] else { panic!("{triple}: {halves:?}") };
        assert_eq!((add, bl), (adrp + 4, adrp + 12), "{triple}: adrp/add/mov/bl/brk");
        let (page, page_off) = if triple == DARWIN {
            (RelocKind::Page21, RelocKind::PageOff12)
        } else {
            (RelocKind::AdrPrelPgHi21, RelocKind::AddAbsLo12Nc)
        };
        let line = |kind: RelocKind, at: u64| {
            format!(
                "address materialization ({}) at {at:#x}: symbol addresses are bound at steps \
                 5.7/5.9",
                kind.name()
            )
        };
        let want: std::collections::BTreeSet<String> =
            [line(page, adrp), line(page_off, add)].into_iter().collect();
        assert_eq!(w.unknown, want.into_iter().collect::<Vec<_>>(), "{triple}");

        assert_eq!(w.page_halves.keys().copied().collect::<Vec<_>>(), [adrp, add], "{triple}");
        let (hi, lo) = (&w.page_halves[&adrp], &w.page_halves[&add]);
        let (wa, wd) = (word_at(&object, adrp), word_at(&object, add));
        assert_eq!(
            (hi.class, hi.kind, hi.target, hi.addend, hi.pc_relative, hi.length),
            (InsnClass::Adrp, page, RelocTarget::Symbol(record), 0, true, 2),
            "{triple}"
        );
        assert_eq!(
            (lo.class, lo.kind, lo.target, lo.addend, lo.pc_relative, lo.length),
            (InsnClass::AddImm64, page_off, RelocTarget::Symbol(record), 0, false, 2),
            "{triple}"
        );
        assert_eq!((hi.rd, hi.imm, hi.shift), ((wa & 0x1f) as u8, 0, 0), "{triple}");
        assert_eq!(
            (lo.rd, lo.rn, lo.imm, lo.shift),
            ((wd & 0x1f) as u8, hi.rd, 0, 0),
            "{triple}: `add xR, xP, #0` with P the `adrp`'s register"
        );
        assert_eq!(
            (hi.unknown_line.clone(), lo.unknown_line.clone()),
            (line(page, adrp), line(page_off, add))
        );
        let relocs = &layout.object.section(w.section).expect("the code section").relocations;
        assert_eq!((relocs[hi.reloc_index].offset, relocs[lo.reloc_index].offset), (adrp, add));

        assert_eq!(
            w.trap_tail.iter().copied().collect::<Vec<_>>(),
            (adrp..=bl + 4).step_by(4).collect::<Vec<_>>(),
            "{triple}"
        );
        let site = w.site_at(bl).expect("the `bl` is a site");
        assert!(site.in_trap_tail && site.kind == MachineSiteKind::Call, "{triple}: {site:?}");
    }
}
