// trust-cg-bridge/compiled_object/pointer_record_tests.rs — the ONE data
// relocation the object reader admits (PKG-CP, 2026-11-11), condition by
// condition.
//
// `compiled_object.rs` is frozen SAMPLE-MORE-OR-REFUSE-MORE and the pointer
// record is an ADMISSION, recorded as an exact-blob exception in
// scripts/frozen-files.txt. These tests are what its waiver row cites. The
// positive case is the image a `core::panic::Location` has, as trust-cg writes
// it (measured on both formats; `tests/f1_compile.rs` drives the real object
// through the whole consumer and links it). Every negative differs from the
// positive in ONE respect and pins the refusal's kind and text. Each is chosen
// so that only the condition it names refuses it, so that deleting that
// condition makes the test fail (run as a mutation battery on each blob of the
// arm; the commit messages record it); where more than one condition refuses
// a negative, its own comment says so.
//
// In the first two groups objects are built as parsed `CompiledObject`s, so a
// test states exactly the relocation record it means, including records
// neither writer would emit.
//
// The first proposal of the admission was rejected by its adjudication
// (2026-11-11), which added the last two tests of the first group; the second
// group, WHAT THE LINKER KEEPS UNDER THE POINTER, holds the conditions that
// answer it. The second proposal was rejected by a second adjudication (the
// same day) for what the Mach-O PARSER kept of a file; the third group, WHAT
// THE MACH-O PARSER REFUSES BEFORE THE ADMISSION IS ASKED, answers it and
// goes through the real parser on a Mach-O file written field by field.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_ir::{
    Block, BlockId, FieldDef, FuncId, FuncTy, Function, Global, Inst, InstrNode, StructDef,
    StructId, TlsModel, TyId,
};

use super::*;

const FILE: &[u8] = b"src/rung.rs\0";
/// `len: u64 = 11`, `line: u32 = 7`, `col: u32 = 5`.
const TAIL: [u8; 16] = [11, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 5, 0, 0, 0];
const RET: u32 = 0xd65f_03c0;

/// The record's section (index 1) and the file name's (index 2).
const LOC_SECTION: usize = 0;
const FILE_SECTION: usize = 1;
/// The symbols, by table index.
const LOC_SYM: usize = 0;
const FILE_SYM: usize = 1;

const FORMATS: [ObjectFormat; 2] = [ObjectFormat::MachO, ObjectFormat::Elf];

fn bytes_global(name: &str, data: &[u8]) -> Global {
    Global {
        name: name.into(),
        ty: Ty::Array(TyId::new(0), data.len() as u64),
        mutable: false,
        initializer: Some(Constant::Bytes { data: data.to_vec(), utf8: false }),
        linkage: Linkage::Internal,
        tls: None,
        align: Some(1),
        section: None,
        visibility: Visibility::Default,
        retained: false,
    }
}

/// `M_cg`: `file = "src/rung.rs\0"` and the record `loc = { ptr @0 = &file +
/// addend, [u8; 16] @8 }`, typed the way trust-cg-lower's `type_flat_image`
/// types an allocation that relocates.
fn module(addend: i64) -> Module {
    let mut m = Module::new("pointer_record");
    m.types.push(Ty::U8);
    m.structs.push(StructDef {
        id: StructId::new(0),
        name: "loc.allocation".into(),
        fields: vec![
            FieldDef { name: "part0".into(), ty: Ty::Ptr, offset: Some(0) },
            FieldDef { name: "part1".into(), ty: Ty::Array(TyId::new(0), 16), offset: Some(8) },
        ],
        size: Some(24),
        align: Some(1),
        repr: StructRepr::Packed(1),
        origin: None,
    });
    m.globals.push(bytes_global("file", FILE));
    m.globals.push(Global {
        ty: Ty::Struct(StructId::new(0)),
        initializer: Some(Constant::Aggregate(vec![
            Constant::SymbolAddr { symbol: "file".into(), addend },
            Constant::Bytes { data: TAIL.to_vec(), utf8: false },
        ])),
        align: Some(8),
        ..bytes_global("loc", &[])
    });
    m
}

fn symbol(format: ObjectFormat, index: usize, name: &str, section: usize, size: u64) -> Symbol {
    let elf = format == ObjectFormat::Elf;
    Symbol {
        index,
        raw_name: if elf { name.into() } else { format!("_{name}") },
        name: name.into(),
        section: Some(section),
        value: 0,
        binding: SymbolBinding::Local,
        visibility: SymbolVisibility::Default,
        kind: SymbolKind::Object,
        size: elf.then_some(size),
        weak: false,
    }
}

/// A section with the header flags word trust-cg writes under `name`
/// (measured 2026-11-11 on the located check's objects): ELF `.data.rel.ro` is
/// `WA`, `.rodata` is `A`, `.text` is `AX`; Mach-O `__TEXT,__text` carries its
/// two instruction attributes and both `__const` sections are zero
/// (`S_REGULAR`, no attribute).
fn data_section(index: usize, name: &str, bytes: Vec<u8>) -> Section {
    let flags = match name {
        ".data.rel.ro" => SHF_ALLOC | SHF_WRITE,
        ".rodata" => SHF_ALLOC,
        ".text" => SHF_ALLOC | SHF_EXECINSTR,
        "__TEXT,__text" => u64::from(S_ATTR_PURE_INSTRUCTIONS | S_ATTR_SOME_INSTRUCTIONS),
        _ => 0,
    };
    Section {
        index,
        name: name.into(),
        class: SectionClass::Data,
        address: 0,
        size: bytes.len() as u64,
        bytes,
        relocations: Vec::new(),
        flags,
    }
}

/// `M_cg` and the object trust-cg writes for it, as the reader parses it
/// (measured 2026-11-11): Mach-O puts the record in `__DATA,__const` with one
/// `ARM64_RELOC_UNSIGNED` (raw type 0, length 3, extern, against the local
/// `_file`) over the addend in place; ELF puts it in `.data.rel.ro` with one
/// `R_AARCH64_ABS64` (raw type 257, `r_addend` = the addend) over zero bytes.
struct Fx {
    module: Module,
    object: CompiledObject,
}

impl Fx {
    fn new(format: ObjectFormat, addend: i64) -> Fx {
        let elf = format == ObjectFormat::Elf;
        let mut record = if elf { [0; 8] } else { addend.to_le_bytes() }.to_vec();
        record.extend_from_slice(&TAIL);
        let (loc_name, file_name) =
            if elf { (".data.rel.ro", ".rodata") } else { ("__DATA,__const", "__TEXT,__const") };
        let mut loc = data_section(1, loc_name, record);
        loc.relocations.push(Relocation {
            offset: 0,
            kind: RelocKind::Other { raw: if elf { 257 } else { 0 } },
            target: RelocTarget::Symbol(FILE_SYM),
            addend: if elf { addend } else { 0 },
            pc_relative: false,
            length: if elf { 2 } else { 3 },
        });
        Fx {
            module: module(addend),
            object: CompiledObject {
                format,
                sections: vec![loc, data_section(2, file_name, FILE.to_vec())],
                symbols: vec![
                    symbol(format, LOC_SYM, "loc", 1, 24),
                    symbol(format, FILE_SYM, "file", 2, FILE.len() as u64),
                ],
                sha256: [0; 32],
                // What trust-cg writes: `MH_SUBSECTIONS_VIA_SYMBOLS`; `e_flags` 0.
                header_flags: if elf { 0 } else { MH_SUBSECTIONS_VIA_SYMBOLS },
            },
        }
    }

    fn reloc(&mut self) -> &mut Relocation {
        &mut self.object.sections[LOC_SECTION].relocations[0]
    }

    fn global(&mut self, name: &str) -> &mut Global {
        self.module.globals.iter_mut().find(|g| g.name == name).expect("global")
    }

    /// Append `global` to `M_cg` and its image to the file name's section,
    /// under a new local symbol; its symbol-table index.
    fn add_global(&mut self, global: Global, image: &[u8]) -> usize {
        self.add_global_in(FILE_SECTION, global, image)
    }

    /// [`Fx::add_global`], into the section at `slot` of the section table.
    fn add_global_in(&mut self, slot: usize, global: Global, image: &[u8]) -> usize {
        let index = self.object.symbols.len();
        let section = &mut self.object.sections[slot];
        let mut sym =
            symbol(self.object.format, index, &global.name, section.index, image.len() as u64);
        sym.value = section.size;
        section.bytes.extend_from_slice(image);
        section.size = section.bytes.len() as u64;
        self.object.symbols.push(sym);
        self.module.globals.push(global);
        index
    }

    /// Add a function `name` to `M_cg`: a one-`ret` Internal body with a local
    /// symbol in a new code section (`body`), or a bodyless declaration with an
    /// undefined symbol. Its symbol-table index.
    fn add_function(&mut self, name: &str, body: bool) -> usize {
        let elf = self.object.format == ObjectFormat::Elf;
        let sig = self
            .module
            .add_func_type(FuncTy { params: vec![], returns: vec![], abi: None, is_vararg: false })
            .expect("signature");
        let id = FuncId::new(self.module.functions.len() as u32);
        let mut f = Function::new(id, name, sig, BlockId::new(0));
        f.linkage = if body { Linkage::Internal } else { Linkage::External };
        if body {
            let mut block = Block::new(BlockId::new(0));
            block.body = vec![InstrNode::new(Inst::Return { values: vec![] })];
            f.blocks = vec![block];
        }
        self.module.functions.push(f);
        let index = self.object.symbols.len();
        let mut sym = symbol(self.object.format, index, name, 3, 4);
        if body {
            sym.kind = SymbolKind::Function;
            self.object.sections.push(Section {
                class: SectionClass::Code,
                ..data_section(
                    3,
                    if elf { ".text" } else { "__TEXT,__text" },
                    RET.to_le_bytes().to_vec(),
                )
            });
        } else {
            sym.section = None;
            sym.kind = SymbolKind::Undefined;
            sym.size = elf.then_some(0);
        }
        self.object.symbols.push(sym);
        index
    }

    fn bind(&self) -> Result<ObjectLayout, ObjectRefusal> {
        let expect = ObjectExpectations::from_module(
            &self.module,
            self.object.format,
            RelocationModel::Static,
        )?;
        ObjectLayout::bind(self.object.clone(), &expect)
    }

    #[track_caller]
    fn binds(&self, what: &str) {
        let layout = self
            .bind()
            .unwrap_or_else(|e| panic!("{:?} {what}: should bind, but: {e}", self.object.format));
        for name in ["loc", "file"] {
            assert!(layout.verified_globals.iter().any(|g| g == name), "{what}: {name}");
        }
    }

    /// Refused with today's whole-object data-relocation refusal, byte for byte.
    #[track_caller]
    fn refuses_the_relocation(&self, what: &str) {
        let section = &self.object.sections[LOC_SECTION].name;
        self.refuses_with(
            what,
            &format!(
                "data section `{section}` carries relocations: pointer-bearing statics are refused"
            ),
        );
    }

    #[track_caller]
    fn refuses_with(&self, what: &str, reason: &str) {
        match self.bind() {
            Ok(_) => panic!("{:?} {what}: BOUND", self.object.format),
            Err(e) => assert_eq!(
                (e.kind, e.reason.as_str()),
                (ObjectRefusalKind::DataImage, reason),
                "{:?} {what}",
                self.object.format
            ),
        }
    }
}

/// THE POSITIVE CASE: the record binds on both formats, with a zero and a
/// non-zero addend, and both globals are compared.
#[test]
fn a_location_record_and_its_one_pointer_relocation_bind() {
    for format in FORMATS {
        for addend in [0, 4] {
            Fx::new(format, addend).binds(&format!("addend {addend}"));
        }
    }
}

/// A relocation against a FUNCTION is refused. The one function symbol that
/// could pass for the global the record names has that global's name, and two
/// conditions refuse it: a name `M_cg` gives to a global and a function names
/// no relocation target (so even the relocation to the data symbol is refused
/// here, which only that condition does), and the target must be the object's
/// data symbol for the global (which [`a_relocation_to_a_symbol_the_inventory_skips_is_refused`]
/// isolates). An ordinary function, of another name, is refused too.
#[test]
fn a_relocation_to_a_function_is_refused() {
    for format in FORMATS {
        let mut fx = Fx::new(format, 0);
        let function = fx.add_function("file", true);
        fx.refuses_the_relocation("the data symbol of a name a function shares");
        fx.reloc().target = RelocTarget::Symbol(function);
        fx.refuses_the_relocation("a function named like the global");

        let mut fx = Fx::new(format, 0);
        let function = fx.add_function("callee", true);
        fx.binds("control: a function of another name changes nothing");
        fx.reloc().target = RelocTarget::Symbol(function);
        fx.refuses_the_relocation("an ordinary function");
    }
}

/// A relocation against an UNDEFINED symbol is refused. `M_cg` declares `file`
/// without defining it (another object does), the record names it, and the
/// object's `file` is undefined: local, and global as a linker would require.
/// So is an undefined symbol with the name of a function `M_cg` declares.
/// THREE conditions refuse the local one, so no single deletion exposes it:
/// the target must be this object's data-symbol definition, its section must
/// be ordinary read-only data, and the addend must lie inside its image (an
/// undefined symbol has no section and no image). With all three deleted this
/// test fails (run once as a mutation, 2026-11-11).
#[test]
fn a_relocation_to_an_undefined_symbol_is_refused() {
    for format in FORMATS {
        for binding in [SymbolBinding::Local, SymbolBinding::Global] {
            let mut fx = Fx::new(format, 0);
            fx.global("file").initializer = None;
            fx.object.sections.remove(FILE_SECTION);
            let file = &mut fx.object.symbols[FILE_SYM];
            file.section = None;
            file.kind = SymbolKind::Undefined;
            file.binding = binding;
            fx.refuses_the_relocation(&format!("{binding:?} undefined `file`"));
        }
        let mut fx = Fx::new(format, 0);
        let undefined = fx.add_function("file", false);
        fx.reloc().target = RelocTarget::Symbol(undefined);
        fx.refuses_the_relocation("an undefined symbol named like the global");
    }
}

/// A relocation against a symbol O1's inventory never binds to a global is
/// refused, though it has the global's name and lies in the global's section:
/// a section, file or debugging symbol is not the object's definition of the
/// global, and its address is whatever the object says.
#[test]
fn a_relocation_to_a_symbol_the_inventory_skips_is_refused() {
    for format in FORMATS {
        for kind in [SymbolKind::Section, SymbolKind::File, SymbolKind::Debug] {
            let mut fx = Fx::new(format, 0);
            let index = fx.object.symbols.len();
            let mut stray = symbol(format, index, "file", 2, 0);
            stray.kind = kind;
            stray.value = 4;
            fx.object.symbols.push(stray);
            fx.binds("control: the stray symbol alone changes nothing");
            fx.reloc().target = RelocTarget::Symbol(index);
            fx.refuses_the_relocation(&format!("a {kind:?} symbol named like the global"));
        }
    }
}

/// A relocation at an offset where the initializer has no `SymbolAddr` is
/// refused: on the record's bytes, straddling the pointer, or on the file name.
#[test]
fn a_relocation_at_an_offset_the_initializer_does_not_name_is_refused() {
    for format in FORMATS {
        for offset in [8, 16, 4, 1] {
            let mut fx = Fx::new(format, 0);
            fx.reloc().offset = offset;
            fx.refuses_the_relocation(&format!("offset {offset}"));
        }
        // A second relocation, on the file name's bytes.
        let mut fx = Fx::new(format, 0);
        let mut extra = fx.reloc().clone();
        extra.target = RelocTarget::Symbol(LOC_SYM);
        fx.object.sections[FILE_SECTION].relocations.push(extra);
        fx.refuses_with(
            "a relocation on the file name",
            &format!(
                "data section `{}` carries relocations: pointer-bearing statics are refused",
                fx.object.sections[FILE_SECTION].name
            ),
        );
    }
}

/// A relocation to a MUTABLE global is refused.
#[test]
fn a_relocation_to_a_mutable_global_is_refused() {
    for format in FORMATS {
        let mut fx = Fx::new(format, 0);
        fx.global("file").mutable = true;
        fx.refuses_the_relocation("mutable target");
    }
}

/// A relocation to a THREAD-LOCAL global is refused.
#[test]
fn a_relocation_to_a_thread_local_global_is_refused() {
    for format in FORMATS {
        for model in [TlsModel::LocalExec, TlsModel::InitialExec, TlsModel::GeneralDynamic] {
            let mut fx = Fx::new(format, 0);
            fx.global("file").tls = Some(model);
            fx.refuses_the_relocation(&format!("{model:?} target"));
        }
    }
}

/// A record that is itself mutable or thread-local is not a pointer record.
#[test]
fn a_mutable_or_thread_local_record_is_refused() {
    for format in FORMATS {
        let mut fx = Fx::new(format, 0);
        fx.global("loc").mutable = true;
        fx.refuses_the_relocation("mutable record");
        let mut fx = Fx::new(format, 0);
        fx.global("loc").tls = Some(TlsModel::LocalExec);
        fx.refuses_the_relocation("thread-local record");
    }
}

/// Any other relocation KIND is refused: every raw type but the format's
/// absolute 64-bit pointer, and every kind the reader names.
#[test]
fn a_relocation_of_another_kind_is_refused() {
    let named = [
        RelocKind::Branch26,
        RelocKind::Page21,
        RelocKind::PageOff12,
        RelocKind::GotLoadPage21,
        RelocKind::GotLoadPageOff12,
        RelocKind::Call26,
        RelocKind::Jump26,
        RelocKind::AdrPrelPgHi21,
        RelocKind::AddAbsLo12Nc,
    ];
    for format in FORMATS {
        let admitted = if format == ObjectFormat::Elf { 257 } else { 0 };
        // Mach-O types are 4 bits; the ELF range covers ABS32/ABS16, the PREL
        // family and the dynamic relocations around ABS64.
        let raws = (0..16).chain(256..320).chain(1024..1040).filter(|raw| *raw != admitted);
        for kind in raws.map(|raw| RelocKind::Other { raw }).chain(named) {
            let mut fx = Fx::new(format, 0);
            fx.reloc().kind = kind;
            fx.refuses_the_relocation(&kind.name());
        }
    }
}

/// A Mach-O relocation of another WIDTH is refused (`r_length` 3 is 8 bytes).
/// ELF has no width field: `R_AARCH64_ABS64` is the 8-byte kind, and the
/// narrower `ABS32`/`ABS16` are other kinds (the test above).
#[test]
fn a_relocation_of_another_width_is_refused() {
    for length in [0, 1, 2] {
        let mut fx = Fx::new(ObjectFormat::MachO, 0);
        fx.reloc().length = length;
        fx.refuses_the_relocation(&format!("length {length}"));
    }
}

/// A PC-RELATIVE relocation is refused.
#[test]
fn a_pc_relative_relocation_is_refused() {
    for format in FORMATS {
        let mut fx = Fx::new(format, 0);
        fx.reloc().pc_relative = true;
        fx.refuses_the_relocation("pc-relative");
    }
}

/// IN-PLACE BYTES that are not what the format keeps there are refused by the
/// image comparison: on Mach-O they are the addend, on ELF they are zero.
#[test]
fn in_place_bytes_that_differ_from_the_addend_are_refused() {
    let differs = "global `loc`'s bytes differ from its initializer image";
    for (addend, in_place) in [(0_i64, 8_i64), (4, 0), (4, 8), (0, -1), (8, -8)] {
        let mut fx = Fx::new(ObjectFormat::MachO, addend);
        fx.object.sections[LOC_SECTION].bytes[..8].copy_from_slice(&in_place.to_le_bytes());
        fx.refuses_with(&format!("addend {addend}, {in_place} in place"), differs);
    }
    for (addend, in_place) in [(0_i64, 8_i64), (4, 4), (0, -1)] {
        let mut fx = Fx::new(ObjectFormat::Elf, addend);
        fx.object.sections[LOC_SECTION].bytes[..8].copy_from_slice(&in_place.to_le_bytes());
        fx.refuses_with(&format!("addend {addend}, {in_place} in place"), differs);
    }
}

/// An ADDEND IN THE RECORD that is not the format's is refused: ELF's
/// `r_addend` must be the initializer's addend, and a Mach-O
/// `ARM64_RELOC_UNSIGNED` carries none (a paired `ARM64_RELOC_ADDEND`).
#[test]
fn a_record_addend_that_differs_is_refused() {
    for (addend, record) in [(0_i64, 4_i64), (4, 0), (4, 8), (4, -4)] {
        let mut fx = Fx::new(ObjectFormat::Elf, addend);
        fx.reloc().addend = record;
        fx.refuses_the_relocation(&format!("ELF addend {addend}, r_addend {record}"));
    }
    for (addend, record) in [(0_i64, 4_i64), (4, 4), (4, -4)] {
        let mut fx = Fx::new(ObjectFormat::MachO, addend);
        fx.reloc().addend = record;
        fx.refuses_the_relocation(&format!("Mach-O addend {addend}, paired addend {record}"));
    }
}

/// A relocation to ANOTHER GLOBAL than the one the initializer names is
/// refused, though that global is as immutable, local and defined here.
#[test]
fn a_relocation_to_another_global_than_the_initializer_names_is_refused() {
    for format in FORMATS {
        let mut fx = Fx::new(format, 0);
        let other = fx.add_global(bytes_global("other", b"src/main.rs\0"), b"src/main.rs\0");
        fx.binds("control: the relocation still names `file`");
        fx.reloc().target = RelocTarget::Symbol(other);
        fx.refuses_the_relocation("another global");
        // The record itself is another global too.
        fx.reloc().target = RelocTarget::Symbol(LOC_SYM);
        fx.refuses_the_relocation("the record itself");
    }
}

/// A relocation to a symbol the linker may bind elsewhere is refused: the
/// target must be LOCAL and not weak. The last case, named by the
/// twenty-fourth adjudication (2026-11-13), isolates the LOCAL condition: the
/// target's `M_cg` linkage is External, so (dd) expects a GLOBAL symbol and
/// passes, and only the target's own LOCAL requirement refuses it (with that
/// requirement removed the object bound, listing `loc` and `file`).
#[test]
fn a_relocation_to_a_non_local_symbol_is_refused() {
    for format in FORMATS {
        for binding in [SymbolBinding::Global, SymbolBinding::Weak] {
            let mut fx = Fx::new(format, 0);
            fx.object.symbols[FILE_SYM].binding = binding;
            fx.refuses_the_relocation(&format!("{binding:?} target"));
        }
        let mut fx = Fx::new(format, 0);
        fx.object.symbols[FILE_SYM].weak = true;
        fx.refuses_the_relocation("weak local target");
        let mut fx = Fx::new(format, 0);
        fx.global("file").linkage = Linkage::External;
        fx.object.symbols[FILE_SYM].binding = SymbolBinding::Global;
        fx.refuses_the_relocation("a Global target M_cg declares External");
    }
}

/// A relocation against a SECTION (Mach-O `r_extern = 0`) is refused, though
/// the section is the one holding the global and the in-place value is the
/// global's address in it.
#[test]
fn a_relocation_against_a_section_is_refused() {
    let mut fx = Fx::new(ObjectFormat::MachO, 0);
    fx.reloc().target = RelocTarget::Section(2);
    fx.refuses_the_relocation("section-relative");
}

/// TWO relocations on one pointer are refused.
#[test]
fn two_relocations_on_one_pointer_are_refused() {
    for format in FORMATS {
        let mut fx = Fx::new(format, 0);
        let again = fx.reloc().clone();
        fx.object.sections[LOC_SECTION].relocations.push(again);
        fx.refuses_the_relocation("two relocations");
    }
}

/// A pointer with NO relocation is refused: its bytes would be the addend,
/// not the address of the global `M_cg` names.
#[test]
fn a_pointer_without_a_relocation_is_refused() {
    for format in FORMATS {
        let mut fx = Fx::new(format, 0);
        fx.object.sections[LOC_SECTION].relocations.clear();
        fx.refuses_with(
            "no relocation",
            "global `loc` has no relocation on its pointer to `file` at 0x0",
        );
    }
}

/// A relocation in a ZERO-FILL section is refused: nothing compares those
/// bytes, so nothing there can be a checked pointer. So is a record whose
/// symbol sits in one with no relocation at all.
#[test]
fn a_record_in_a_zero_fill_section_is_refused() {
    for format in FORMATS {
        let mut fx = Fx::new(format, 0);
        let section = &mut fx.object.sections[LOC_SECTION];
        section.class = SectionClass::ZeroFill;
        section.bytes.clear();
        fx.refuses_the_relocation("relocated zero-fill");
        fx.object.sections[LOC_SECTION].relocations.clear();
        fx.refuses_with(
            "unrelocated zero-fill",
            "global `loc` has no relocation on its pointer to `file` at 0x0",
        );
    }
}

/// A relocation to a global whose symbol sits in a ZERO-FILL section is
/// refused: the pointer must lead to bytes the reader compared with the
/// global's initializer.
#[test]
fn a_relocation_to_a_global_in_a_zero_fill_section_is_refused() {
    for format in FORMATS {
        let mut fx = Fx::new(format, 0);
        let section = &mut fx.object.sections[FILE_SECTION];
        section.class = SectionClass::ZeroFill;
        section.bytes.clear();
        fx.refuses_the_relocation("zero-fill target");
    }
}

/// A name `M_cg` gives to TWO globals is no relocation target and no pointer
/// record, whichever of the two is immutable.
#[test]
fn a_name_m_cg_gives_to_two_globals_is_refused() {
    for format in FORMATS {
        for first in [true, false] {
            let mut fx = Fx::new(format, 0);
            let mut twin = bytes_global("file", FILE);
            twin.mutable = true;
            let at = if first { 0 } else { fx.module.globals.len() };
            fx.module.globals.insert(at, twin);
            fx.refuses_the_relocation(&format!("two `file`, the mutable one first: {first}"));

            let mut fx = Fx::new(format, 0);
            let mut twin = fx.global("loc").clone();
            twin.mutable = true;
            let at = if first { 0 } else { fx.module.globals.len() };
            fx.module.globals.insert(at, twin);
            fx.refuses_the_relocation(&format!("two `loc`, the mutable one first: {first}"));
        }
    }
}

/// Every other pointer-bearing static keeps the refusal it had: a relocated
/// scalar, and a relocated global whose initializer is not a pointer record.
#[test]
fn every_other_relocated_static_keeps_its_refusal() {
    for format in FORMATS {
        // A `u64` global with a relocation on it.
        let mut fx = Fx::new(format, 0);
        let loc = fx.global("loc");
        loc.ty = Ty::U64;
        loc.initializer = Some(Constant::Int(0));
        fx.object.sections[LOC_SECTION].bytes.truncate(8);
        fx.object.sections[LOC_SECTION].size = 8;
        fx.refuses_the_relocation("a relocated u64");
        // A bare `SymbolAddr` at `ptr` type.
        let loc = fx.global("loc");
        loc.ty = Ty::Ptr;
        loc.initializer = Some(Constant::SymbolAddr { symbol: "file".into(), addend: 0 });
        fx.refuses_the_relocation("a relocated bare pointer");
    }
}

/// The image is exact for a pointer record and absent for everything else, so
/// no other aggregate becomes comparable.
#[test]
fn pointer_record_images_are_exact_or_absent() {
    let image = |m: &Module, format| {
        let g = m.globals.iter().find(|g| g.name == "loc").expect("loc");
        pointer_record_image(m, &g.ty, g.initializer.as_ref().expect("initializer"), format)
    };
    let slot = |addend| vec![ExpectedPointer { offset: 0, symbol: "file".into(), addend }];
    for addend in [0_i64, 4, -8] {
        let m = module(addend);
        let mut macho = addend.to_le_bytes().to_vec();
        macho.extend_from_slice(&TAIL);
        assert_eq!(image(&m, ObjectFormat::MachO), Some((macho, slot(addend))));
        let mut elf = vec![0; 8];
        elf.extend_from_slice(&TAIL);
        assert_eq!(image(&m, ObjectFormat::Elf), Some((elf, slot(addend))));
    }

    let absent = |what: &str, edit: &dyn Fn(&mut Module)| {
        let mut m = module(0);
        edit(&mut m);
        for format in FORMATS {
            assert_eq!(image(&m, format), None, "{what}");
        }
    };
    fn loc(m: &mut Module) -> &mut Global {
        m.globals.iter_mut().find(|g| g.name == "loc").expect("loc")
    }
    fn values(m: &mut Module) -> &mut Vec<Constant> {
        match loc(m).initializer.as_mut() {
            Some(Constant::Aggregate(values)) => values,
            other => panic!("{other:?}"),
        }
    }
    for repr in [StructRepr::Rust, StructRepr::C, StructRepr::Transparent, StructRepr::Packed(2)] {
        absent(&format!("repr {repr}"), &|m| m.structs[0].repr = repr);
    }
    absent("a gap before the bytes", &|m| m.structs[0].fields[1].offset = Some(16));
    absent("overlapping fields", &|m| m.structs[0].fields[1].offset = Some(0));
    absent("an unstated offset", &|m| m.structs[0].fields[1].offset = None);
    absent("a pointer not at 0", &|m| m.structs[0].fields[0].offset = Some(8));
    absent("tail padding", &|m| m.structs[0].size = Some(32));
    absent("a short size", &|m| m.structs[0].size = Some(16));
    absent("an unstated size", &|m| m.structs[0].size = None);
    absent("a missing value", &|m| {
        values(m).pop();
    });
    absent("an extra value", &|m| values(m).push(Constant::Int(0)));
    absent("an integer in the pointer", &|m| values(m)[0] = Constant::Int(0));
    absent("a function in the pointer", &|m| values(m)[0] = Constant::FnDef(FuncId::new(0)));
    absent("a usize field", &|m| m.structs[0].fields[0].ty = Ty::Usize);
    absent("an array of another element", &|m| m.types[0] = Ty::U16);
    absent("an array of an unknown element", &|m| m.types.clear());
    absent("too few bytes", &|m| {
        values(m)[1] = Constant::Bytes { data: TAIL[..15].to_vec(), utf8: false };
    });
    absent("an array type longer than its bytes", &|m| {
        m.structs[0].fields[1].ty = Ty::Array(TyId::new(0), 99);
    });
    absent("too many bytes", &|m| {
        values(m)[1] = Constant::Bytes { data: [TAIL.as_slice(), &[0]].concat(), utf8: false };
    });
    absent("a splat for the bytes", &|m| {
        values(m)[1] = Constant::Splat { elem: Box::new(Constant::Int(0)), len: 16 };
    });
    absent("an address for the bytes", &|m| {
        values(m)[1] = Constant::SymbolAddr { symbol: "file".into(), addend: 0 };
    });
    // A field that is neither a pointer nor a byte array (here a zero-sized
    // array initialized by an empty aggregate) refuses the record rather than
    // being skipped (the mutation sweep of 2026-11-13).
    absent("a zero-sized field of neither form", &|m| {
        m.structs[0].fields.insert(
            1,
            FieldDef { name: "empty".into(), ty: Ty::Array(TyId::new(0), 0), offset: Some(8) },
        );
        values(m).insert(1, Constant::Aggregate(vec![]));
    });
    absent("no pointer field", &|m| {
        m.structs[0].fields.remove(0);
        m.structs[0].fields[0].offset = Some(0);
        m.structs[0].size = Some(16);
        values(m).remove(0);
    });
    absent("an unknown struct", &|m| m.structs.clear());
    absent("a scalar type", &|m| loc(m).ty = Ty::U64);
    absent("a tuple-less array type", &|m| loc(m).ty = Ty::Array(TyId::new(0), 24));
    absent("a bytes initializer", &|m| {
        loc(m).initializer = Some(Constant::Bytes { data: vec![0; 24], utf8: false });
    });
    absent("a bare address", &|m| {
        loc(m).initializer = Some(Constant::SymbolAddr { symbol: "file".into(), addend: 0 });
    });
}

/// With no relocation and no pointer record nothing changes: the file name
/// alone binds, and an aggregate that is not a pointer record is still not
/// imaged.
#[test]
fn a_module_without_a_pointer_record_binds_as_before() {
    for format in FORMATS {
        let mut fx = Fx::new(format, 0);
        fx.module.globals.retain(|g| g.name == "file");
        fx.object.sections.remove(LOC_SECTION);
        fx.object.symbols = vec![symbol(format, 0, "file", 2, FILE.len() as u64)];
        let layout = fx.bind().expect("the file name alone binds");
        assert_eq!(layout.verified_globals, ["file"]);

        // The record without its pointer field: a packed struct of bytes.
        let mut fx = Fx::new(format, 0);
        fx.module.structs[0].fields.remove(0);
        fx.module.structs[0].fields[0].offset = Some(0);
        fx.module.structs[0].size = Some(16);
        fx.global("loc").initializer =
            Some(Constant::Aggregate(vec![Constant::Bytes { data: TAIL.to_vec(), utf8: false }]));
        let section = &mut fx.object.sections[LOC_SECTION];
        section.relocations.clear();
        section.bytes = TAIL.to_vec();
        section.size = 16;
        fx.refuses_with(
            "a packed struct with no pointer",
            "global `loc` has an initializer the gate cannot image (fail-closed)",
        );
    }
}

/// The positive case with TWO pointers, `loc = { ptr -> file, ptr -> other,
/// [u8; 8] }`: each slot binds to the global its own initializer names and to
/// no other. Added by the adjudication of the admission (2026-11-11); every
/// other test here has one pointer.
#[test]
fn each_pointer_of_a_record_binds_to_its_own_target() {
    let two = |format| {
        let mut fx = Fx::new(format, 0);
        let other = fx.add_global(bytes_global("other", b"src/main.rs\0"), b"src/main.rs\0");
        fx.module.structs[0].fields = vec![
            FieldDef { name: "part0".into(), ty: Ty::Ptr, offset: Some(0) },
            FieldDef { name: "part1".into(), ty: Ty::Ptr, offset: Some(8) },
            FieldDef { name: "part2".into(), ty: Ty::Array(TyId::new(0), 8), offset: Some(16) },
        ];
        fx.global("loc").initializer = Some(Constant::Aggregate(vec![
            Constant::SymbolAddr { symbol: "file".into(), addend: 0 },
            Constant::SymbolAddr { symbol: "other".into(), addend: 0 },
            Constant::Bytes { data: vec![9; 8], utf8: false },
        ]));
        let section = &mut fx.object.sections[LOC_SECTION];
        section.bytes = [vec![0; 16], vec![9; 8]].concat();
        let mut second = section.relocations[0].clone();
        second.offset = 8;
        second.target = RelocTarget::Symbol(other);
        section.relocations.push(second);
        fx
    };
    fn relocs(fx: &mut Fx) -> &mut Vec<Relocation> {
        &mut fx.object.sections[LOC_SECTION].relocations
    }
    for format in FORMATS {
        let mut fx = two(format);
        fx.binds("each pointer relocated to its own target");
        assert!(fx.bind().expect("binds").verified_globals.iter().any(|g| g == "other"));
        let (first, second) = (relocs(&mut fx)[0].target, relocs(&mut fx)[1].target);

        relocs(&mut fx)[0].target = second;
        relocs(&mut fx)[1].target = first;
        fx.refuses_the_relocation("the two targets swapped");

        let mut fx = two(format);
        relocs(&mut fx)[1].target = first;
        fx.refuses_the_relocation("the second pointer to the first's target");

        let mut fx = two(format);
        relocs(&mut fx)[1].offset = 4;
        fx.refuses_the_relocation("a relocation straddling the two slots");

        let mut fx = two(format);
        relocs(&mut fx).pop();
        fx.refuses_with(
            "the second pointer unrelocated",
            "global `loc` has no relocation on its pointer to `other` at 0x8",
        );

        let mut fx = two(format);
        relocs(&mut fx).remove(0);
        fx.refuses_with(
            "the first pointer unrelocated",
            "global `loc` has no relocation on its pointer to `file` at 0x0",
        );
    }
}

/// ADJUDICATION FINDING, PKG-CP location-record relocation (2026-11-11). RED
/// against compiled_object.rs blob 7681fe547d: every addend below BINDS.
///
/// The admission's ground for a record's pointer is that it leads to bytes the
/// reader compared with the target global's image (the target must be "in
/// initialized data (so its bytes are compared)";
/// [`a_relocation_to_a_global_in_a_zero_fill_section_is_refused`] refuses a
/// target on that ground alone). The addend is compared with the initializer's
/// and with nothing else, so a pointer `M_cg` aims before the target or past
/// its end is admitted, and leads to bytes no comparison of this pointer's
/// target covers: whatever the linker lays out next to the global. That is
/// faithful to `M_cg`, and it is outside what the admission says it admits.
/// One past the end (`addend == len`) is left to the fix to decide.
///
/// FAILS while the reader admits a record pointer that lies outside its
/// target's image.
#[test]
fn a_record_pointer_outside_its_target_is_refused() {
    let len = FILE.len() as i64;
    let mut bound = Vec::new();
    for format in FORMATS {
        for addend in 0..len {
            Fx::new(format, addend).binds(&format!("control: addend {addend} is inside `file`"));
        }
        for addend in [-1, len + 1, 4096, i64::MIN, i64::MAX] {
            if Fx::new(format, addend).bind().is_ok() {
                bound.push((format, addend));
            }
        }
    }
    assert!(bound.is_empty(), "BOUND with a pointer outside `file` ({len} bytes): {bound:?}");
}

// ---------------------------------------------------------------------------
// WHAT THE LINKER KEEPS UNDER THE POINTER (the fixes that answer the
// 2026-11-11 rejection). The conditions above bind the relocation to `M_cg`;
// these make what the reader compared be what the linked program reads. One
// test per condition, each on both formats unless the field is one format's.
// ---------------------------------------------------------------------------

/// Header flags words that are NOT ordinary data when they replace `ordinary`:
/// on Mach-O every section type but `S_REGULAR` (the low byte: zero-fill, the
/// C-string and 4/8/16-byte literal types, the pointer, coalesced and
/// thread-local types, and every value the format leaves undefined) and every
/// single bit above it (the `S_ATTR_*` bits, and bits no header can hold); on
/// ELF `ordinary` with any one bit flipped (`SHF_MERGE`, `SHF_STRINGS`,
/// `SHF_INFO_LINK`, `SHF_LINK_ORDER`, `SHF_GROUP`, `SHF_TLS`,
/// `SHF_COMPRESSED`, `SHF_EXECINSTR`, a missing `SHF_ALLOC`, the OS and
/// processor bits) and the string-merge pair. `SHF_WRITE` (bit 0) is left to
/// the caller: the record's section may carry it, the target's may not.
fn not_ordinary(format: ObjectFormat, ordinary: u64) -> Vec<u64> {
    match format {
        ObjectFormat::MachO => (1..=0xff).chain((8..64).map(|bit| 1 << bit)).collect(),
        ObjectFormat::Elf => {
            (1..64).map(|bit| ordinary ^ (1 << bit)).chain([ordinary | 0x10 | 0x20]).collect()
        }
    }
}

/// Mach-O data names that are not ordinary data under a zero flags word: the
/// literal sections, and a name the parser would not classify at all.
const NOT_ORDINARY_NAMES: [&str; 5] = [
    "__TEXT,__cstring",
    "__TEXT,__literal4",
    "__TEXT,__literal8",
    "__TEXT,__literal16",
    "__DATA,__x",
];

/// The RECORD's section must be ordinary data by its header: a section the
/// linker splits into literals, merges by content, groups, compresses or drops
/// does not keep the record's bytes and its relocation as the reader saw them.
/// The record's section may be read-only or writable (the control).
#[test]
fn a_record_in_a_section_that_is_not_ordinary_data_is_refused() {
    for format in FORMATS {
        // The word trust-cg writes, and on ELF the read-only word as well: the
        // record's section may be either, and neither may gain a bit.
        let written = Fx::new(format, 0).object.sections[LOC_SECTION].flags;
        let bases = if format == ObjectFormat::Elf { vec![written, SHF_ALLOC] } else { vec![0] };
        for flags in bases.into_iter().flat_map(|ordinary| not_ordinary(format, ordinary)) {
            let mut fx = Fx::new(format, 0);
            fx.object.sections[LOC_SECTION].flags = flags;
            fx.refuses_the_relocation(&format!("record section flags {flags:#x}"));
        }
    }
    for name in NOT_ORDINARY_NAMES {
        let mut fx = Fx::new(ObjectFormat::MachO, 0);
        fx.object.sections[LOC_SECTION].name = name.into();
        fx.refuses_the_relocation(&format!("record section `{name}`"));
    }
    // Control: writability of the record's section is not a condition.
    for name in ["__TEXT,__const", "__DATA,__data"] {
        let mut fx = Fx::new(ObjectFormat::MachO, 0);
        fx.object.sections[LOC_SECTION].name = name.into();
        fx.binds(&format!("control: the record in `{name}`"));
    }
    let mut fx = Fx::new(ObjectFormat::Elf, 0);
    fx.object.sections[LOC_SECTION].flags = SHF_ALLOC;
    fx.binds("control: the record in a read-only section");
}

/// The TARGET's section must be ordinary data by its header. This is the
/// rejection's first blocker: in a string-literal or merge section the linker
/// resolves the pointer to the piece the symbol starts, and the bytes after
/// that piece are not the rest of the global
/// (tests/f1_compile.rs::a_record_pointer_into_a_string_literal_section_is_refused
/// drives the real objects; this isolates the header word and the name).
#[test]
fn a_relocation_into_a_section_that_is_not_ordinary_data_is_refused() {
    for format in FORMATS {
        let ordinary = Fx::new(format, 0).object.sections[FILE_SECTION].flags;
        for flags in not_ordinary(format, ordinary) {
            let mut fx = Fx::new(format, 0);
            fx.object.sections[FILE_SECTION].flags = flags;
            fx.refuses_the_relocation(&format!("target section flags {flags:#x}"));
        }
    }
    for name in NOT_ORDINARY_NAMES {
        let mut fx = Fx::new(ObjectFormat::MachO, 0);
        fx.object.sections[FILE_SECTION].name = name.into();
        fx.refuses_the_relocation(&format!("target section `{name}`"));
    }
}

/// The TARGET's section must be READ-ONLY: `M_cg` says the target is
/// immutable, and the object must not put it where the program may write.
/// Mach-O: `__TEXT,__const`, not the `__DATA` segment. ELF: no `SHF_WRITE`.
#[test]
fn a_relocation_to_a_global_in_a_writable_section_is_refused() {
    for name in ["__DATA,__const", "__DATA,__data"] {
        let mut fx = Fx::new(ObjectFormat::MachO, 0);
        fx.object.sections[FILE_SECTION].name = name.into();
        fx.refuses_the_relocation(&format!("target in `{name}`"));
    }
    for name in [".rodata", ".data", ".data.rel.ro"] {
        let mut fx = Fx::new(ObjectFormat::Elf, 0);
        let section = &mut fx.object.sections[FILE_SECTION];
        section.name = name.into();
        section.flags = SHF_ALLOC | SHF_WRITE;
        fx.refuses_the_relocation(&format!("target in a writable `{name}`"));
    }
}

/// THE ADDEND'S BOUND IS `0 <= addend < len`: the last byte of the target
/// binds, ONE PAST THE END is refused, and so is any pointer to a target with
/// an empty image, which has no byte to point at.
/// [`a_record_pointer_outside_its_target_is_refused`] holds the far cases.
#[test]
fn a_record_pointer_one_past_its_target_is_refused() {
    let len = FILE.len() as i64;
    for format in FORMATS {
        Fx::new(format, len - 1).binds("control: the target's last byte");
        Fx::new(format, len).refuses_the_relocation("one past the end");

        let mut fx = Fx::new(format, 0);
        let file = fx.global("file");
        file.ty = Ty::Array(TyId::new(0), 0);
        file.initializer = Some(Constant::Bytes { data: Vec::new(), utf8: false });
        let section = &mut fx.object.sections[FILE_SECTION];
        section.bytes.clear();
        section.size = 0;
        fx.refuses_the_relocation("an empty target");
    }
}

/// THE FILE HEADER'S FLAGS WORD must hold nothing the reader does not name.
/// Mach-O: `MH_SUBSECTIONS_VIA_SYMBOLS` may be set (trust-cg sets it) or clear
/// (the controls), and every other bit refuses. ELF: `e_flags` must be zero.
#[test]
fn a_header_flag_the_reader_does_not_name_is_refused() {
    let mut fx = Fx::new(ObjectFormat::MachO, 0);
    assert_eq!(fx.object.header_flags, MH_SUBSECTIONS_VIA_SYMBOLS);
    fx.binds("control: the section may be cut at its symbols");
    fx.object.header_flags = 0;
    fx.binds("control: the section is kept whole");
    for bit in (0..32).filter(|bit| 1 << bit != MH_SUBSECTIONS_VIA_SYMBOLS) {
        for base in [0, MH_SUBSECTIONS_VIA_SYMBOLS] {
            let mut fx = Fx::new(ObjectFormat::MachO, 0);
            fx.object.header_flags = base | 1 << bit;
            fx.refuses_the_relocation(&format!("Mach-O header flags {:#x}", base | 1 << bit));
        }
    }
    for bit in 0..32 {
        let mut fx = Fx::new(ObjectFormat::Elf, 0);
        fx.object.header_flags = 1 << bit;
        fx.refuses_the_relocation(&format!("ELF e_flags {:#x}", 1_u32 << bit));
    }
}

/// The RECORD's own symbol must be LOCAL: a global one is a name another
/// object can define or reference. (A weak one is refused by the next test.)
/// The first case is also refused by (dd), since `M_cg` declares `loc`
/// internal; the second, named by the twenty-fourth adjudication (2026-11-13),
/// makes `loc` External in `M_cg` so that (dd) expects a GLOBAL symbol and
/// passes, and only (b) refuses it (with (b) removed the object bound, listing
/// `loc` and `file`).
#[test]
fn a_record_whose_symbol_is_not_local_is_refused() {
    for format in FORMATS {
        let mut fx = Fx::new(format, 0);
        fx.object.symbols[LOC_SYM].binding = SymbolBinding::Global;
        fx.refuses_the_relocation("a Global record");
        let mut fx = Fx::new(format, 0);
        fx.global("loc").linkage = Linkage::External;
        fx.object.symbols[LOC_SYM].binding = SymbolBinding::Global;
        fx.refuses_the_relocation("a Global record M_cg declares External");
    }
}

/// The record's and the target's symbols carry the binding and visibility
/// their `M_cg` linkage and visibility require: both symbols are LOCAL, so a
/// record or target that `M_cg` declares external (default or hidden) is
/// refused, while a private one binds like the internal one.
#[test]
fn a_record_or_target_m_cg_declares_external_is_refused() {
    for format in FORMATS {
        for name in ["loc", "file"] {
            let mut fx = Fx::new(format, 0);
            fx.global(name).linkage = Linkage::Private;
            fx.binds(&format!("a private `{name}`"));
            for visibility in [Visibility::Default, Visibility::Hidden] {
                let mut fx = Fx::new(format, 0);
                fx.global(name).linkage = Linkage::External;
                fx.global(name).visibility = visibility;
                fx.refuses_the_relocation(&format!("an external {visibility:?} `{name}`"));
            }
        }
    }
}

/// NO WEAK DEFINITION may share the record's section or the target's. A
/// Mach-O linker drops a weak definition another object overrides, together
/// with a following symbol that starts no piece of its own (`N_ALT_ENTRY`,
/// which the reader does not read), and a pointer to that symbol then leads
/// into the other object's bytes
/// (tests/f1_compile.rs::the_system_linker_moves_an_alt_entry_target_with_an_overridden_weak_definition
/// links and runs it). A local or global non-weak neighbour changes nothing.
#[test]
fn a_weak_definition_in_the_records_or_the_targets_section_is_refused() {
    let weak =
        [(SymbolBinding::Weak, true), (SymbolBinding::Local, true), (SymbolBinding::Weak, false)];
    for format in FORMATS {
        for slot in [FILE_SECTION, LOC_SECTION] {
            for (binding, flag) in weak {
                let mut fx = Fx::new(format, 0);
                let other = fx.add_global_in(slot, bytes_global("other", b"x\0"), b"x\0");
                fx.binds("control: a local neighbour");
                fx.object.symbols[other].binding = SymbolBinding::Global;
                fx.binds("control: a global, non-weak neighbour");
                fx.object.symbols[other].binding = binding;
                fx.object.symbols[other].weak = flag;
                fx.refuses_the_relocation(&format!(
                    "a {binding:?} (weak flag {flag}) neighbour in section slot {slot}"
                ));
            }
        }
        // The record itself, local and flagged weak.
        let mut fx = Fx::new(format, 0);
        fx.object.symbols[LOC_SYM].weak = true;
        fx.refuses_the_relocation("a weak local record");
        // A weak symbol in a third section changes nothing.
        let mut fx = Fx::new(format, 0);
        let function = fx.add_function("callee", true);
        fx.object.symbols[function].weak = true;
        fx.binds("control: a weak symbol in another section");
    }
}

// ---------------------------------------------------------------------------
// WHAT THE MACH-O PARSER REFUSES BEFORE THE ADMISSION IS ASKED. The second
// adjudication (2026-11-11) found two places where the parser kept less than
// the file says, so that a parsed object could satisfy every condition above
// while the file meant something else to a linker: a second `LC_SYMTAB` (the
// parser kept the last table; a relocation names its symbol by table index),
// and an `ARM64_RELOC_ADDEND` entry of value zero paired with the record's
// pointer (indistinguishable, once parsed, from no entry). Both refuse at
// parse now. These tests write a Mach-O FILE and go through
// `CompiledObject::parse`, because a parsed object cannot state either input;
// tests/f1_compile.rs does the same to the object trust-cg really emits.
// ELF has neither field: its parser already refuses a second symbol table, and
// `r_addend` is the relocation's own.
// ---------------------------------------------------------------------------

/// One Mach-O `relocation_info`: `r_address`, then `r_symbolnum | r_pcrel << 24
/// | r_length << 25 | r_extern << 27 | r_type << 28`.
type RelocEntry = [u32; 2];

/// `ARM64_RELOC_UNSIGNED` (type 0), 8 bytes wide, against symbol `symbol`.
fn unsigned_entry(at: u32, symbol: usize) -> RelocEntry {
    [at, symbol as u32 | 3 << 25 | 1 << 27]
}

/// `ARM64_RELOC_PAGE21` (type 3), pc-relative, against symbol `symbol`.
fn page21_entry(at: u32, symbol: usize) -> RelocEntry {
    [at, symbol as u32 | 1 << 24 | 2 << 25 | 1 << 27 | 3 << 28]
}

/// `ARM64_RELOC_ADDEND` (type 10) of `value`, as trust-cg writes the prefix
/// record: not extern, not pc-relative, length 2, the value in `r_symbolnum`.
fn addend_entry(at: u32, value: i32) -> RelocEntry {
    [at, (value as u32 & 0x00ff_ffff) | 2 << 25 | 10 << 28]
}

/// One section of a [`MachOFile`].
struct FileSection {
    segment: &'static str,
    section: &'static str,
    flags: u32,
    bytes: Vec<u8>,
    relocations: Vec<RelocEntry>,
}

/// A Mach-O `MH_OBJECT` file, written field by field: one `LC_SEGMENT_64`
/// with `sections`, then `symtabs` copies of the `LC_SYMTAB` command (each
/// naming the one symbol table and string table), then `dysymtabs` copies of
/// an `LC_DYSYMTAB` that calls every symbol local. Every symbol is a local
/// `N_SECT` definition at offset 0 of its section.
struct MachOFile {
    sections: Vec<FileSection>,
    /// `(name without the underscore, 1-based section ordinal)`.
    symbols: Vec<(&'static str, u8)>,
    symtabs: usize,
    dysymtabs: usize,
}

impl MachOFile {
    /// The file form of `Fx::new(ObjectFormat::MachO, addend)`: the record in
    /// `__DATA,__const` with its one `ARM64_RELOC_UNSIGNED` over the addend in
    /// place, the file name in `__TEXT,__const`, one `LC_SYMTAB` and one
    /// `LC_DYSYMTAB`.
    fn located(addend: i64) -> MachOFile {
        let mut record = addend.to_le_bytes().to_vec();
        record.extend_from_slice(&TAIL);
        MachOFile {
            sections: vec![
                FileSection {
                    segment: "__DATA",
                    section: "__const",
                    flags: 0,
                    bytes: record,
                    relocations: vec![unsigned_entry(0, FILE_SYM)],
                },
                FileSection {
                    segment: "__TEXT",
                    section: "__const",
                    flags: 0,
                    bytes: FILE.to_vec(),
                    relocations: Vec::new(),
                },
            ],
            symbols: vec![("loc", 1), ("file", 2)],
            symtabs: 1,
            dysymtabs: 1,
        }
    }

    fn bytes(&self) -> Vec<u8> {
        fn name16(name: &str) -> [u8; 16] {
            let mut field = [0; 16];
            field[..name.len()].copy_from_slice(name.as_bytes());
            field
        }
        let commands_size = 72 + 80 * self.sections.len() + 24 * self.symtabs + 80 * self.dysymtabs;
        let contents_at = 32 + commands_size;
        let contents: usize = self.sections.iter().map(|s| s.bytes.len()).sum();
        let relocs_at = contents_at + contents;
        let relocs: usize = self.sections.iter().map(|s| s.relocations.len() * 8).sum();
        let symbols_at = relocs_at + relocs;
        let strings_at = symbols_at + self.symbols.len() * 16;
        let mut strings = vec![0_u8];
        let mut nlist = Vec::new();
        let address_of = |ordinal: u8| -> u64 {
            self.sections[..usize::from(ordinal) - 1].iter().map(|s| s.bytes.len() as u64).sum()
        };
        for (name, ordinal) in &self.symbols {
            nlist.extend_from_slice(&(strings.len() as u32).to_le_bytes());
            // n_type N_SECT (local), n_sect, n_desc 0, n_value.
            nlist.extend_from_slice(&[N_SECT, *ordinal, 0, 0]);
            nlist.extend_from_slice(&address_of(*ordinal).to_le_bytes());
            strings.push(b'_');
            strings.extend_from_slice(name.as_bytes());
            strings.push(0);
        }

        let mut o = Vec::new();
        let u32le = |o: &mut Vec<u8>, v: usize| o.extend_from_slice(&(v as u32).to_le_bytes());
        let u64le = |o: &mut Vec<u8>, v: usize| o.extend_from_slice(&(v as u64).to_le_bytes());
        // mach_header_64: magic, cputype, cpusubtype, filetype, ncmds,
        // sizeofcmds, flags, reserved.
        o.extend_from_slice(&MH_MAGIC_64.to_le_bytes());
        o.extend_from_slice(&CPU_TYPE_ARM64.to_le_bytes());
        u32le(&mut o, 0);
        o.extend_from_slice(&MH_OBJECT.to_le_bytes());
        u32le(&mut o, 1 + self.symtabs + self.dysymtabs);
        u32le(&mut o, commands_size);
        o.extend_from_slice(&MH_SUBSECTIONS_VIA_SYMBOLS.to_le_bytes());
        u32le(&mut o, 0);
        // segment_command_64: cmd, cmdsize, segname, vmaddr, vmsize, fileoff,
        // filesize, maxprot, initprot, nsects, flags.
        o.extend_from_slice(&LC_SEGMENT_64.to_le_bytes());
        u32le(&mut o, 72 + 80 * self.sections.len());
        o.extend_from_slice(&name16(""));
        u64le(&mut o, 0);
        u64le(&mut o, contents);
        u64le(&mut o, contents_at);
        u64le(&mut o, contents);
        u32le(&mut o, 7);
        u32le(&mut o, 7);
        u32le(&mut o, self.sections.len());
        u32le(&mut o, 0);
        let (mut address, mut reloff) = (0, relocs_at);
        for s in &self.sections {
            // section_64: sectname, segname, addr, size, offset, align, reloff,
            // nreloc, flags, reserved1..3.
            o.extend_from_slice(&name16(s.section));
            o.extend_from_slice(&name16(s.segment));
            u64le(&mut o, address);
            u64le(&mut o, s.bytes.len());
            u32le(&mut o, contents_at + address);
            // align: the largest power of two (up to 2^4) the address is a
            // multiple of, so the header never claims an alignment the
            // section's address does not have.
            u32le(&mut o, if address == 0 { 4 } else { address.trailing_zeros().min(4) as usize });
            u32le(&mut o, reloff);
            u32le(&mut o, s.relocations.len());
            o.extend_from_slice(&s.flags.to_le_bytes());
            o.extend_from_slice(&[0; 12]);
            address += s.bytes.len();
            reloff += s.relocations.len() * 8;
        }
        for _ in 0..self.symtabs {
            // symtab_command: cmd, cmdsize, symoff, nsyms, stroff, strsize.
            o.extend_from_slice(&LC_SYMTAB.to_le_bytes());
            u32le(&mut o, 24);
            u32le(&mut o, symbols_at);
            u32le(&mut o, self.symbols.len());
            u32le(&mut o, strings_at);
            u32le(&mut o, strings.len());
        }
        for _ in 0..self.dysymtabs {
            // dysymtab_command: cmd, cmdsize, ilocalsym, nlocalsym, and
            // sixteen more words, all zero here.
            o.extend_from_slice(&LC_DYSYMTAB.to_le_bytes());
            u32le(&mut o, 80);
            u32le(&mut o, 0);
            u32le(&mut o, self.symbols.len());
            o.extend_from_slice(&[0; 64]);
        }
        assert_eq!(o.len(), contents_at, "the load commands' size");
        for s in &self.sections {
            o.extend_from_slice(&s.bytes);
        }
        for entry in self.sections.iter().flat_map(|s| &s.relocations) {
            o.extend_from_slice(&entry[0].to_le_bytes());
            o.extend_from_slice(&entry[1].to_le_bytes());
        }
        o.extend_from_slice(&nlist);
        o.extend_from_slice(&strings);
        o
    }

    fn parse(&self) -> Result<CompiledObject, ObjectRefusal> {
        CompiledObject::parse(&self.bytes())
    }

    /// The file parses, and binds against `module(addend)` with both globals
    /// compared: the reader's whole path, from bytes.
    #[track_caller]
    fn binds(&self, addend: i64, what: &str) {
        let object = self.parse().unwrap_or_else(|e| panic!("{what}: should parse, but: {e}"));
        let expect = ObjectExpectations::from_module(
            &module(addend),
            ObjectFormat::MachO,
            RelocationModel::Static,
        )
        .expect("expectations");
        let layout = ObjectLayout::bind(object, &expect)
            .unwrap_or_else(|e| panic!("{what}: should bind, but: {e}"));
        for name in ["loc", "file"] {
            assert!(layout.verified_globals.iter().any(|g| g == name), "{what}: {name}");
        }
    }

    /// The PARSER refuses the file as malformed, with exactly `reason`.
    #[track_caller]
    fn refuses_at_parse(&self, what: &str, reason: &str) {
        match self.parse() {
            Ok(_) => panic!("{what}: PARSED"),
            Err(e) => {
                assert_eq!(
                    (e.kind, e.reason.as_str()),
                    (ObjectRefusalKind::Malformed, reason),
                    "{what}"
                )
            }
        }
    }
}

/// THE FILE FORM OF THE POSITIVE CASE binds through the real parser, with a
/// zero and a non-zero addend in place, and with or without an `LC_DYSYMTAB`.
/// It is the control of every refusal below.
#[test]
fn the_written_mach_o_file_of_a_location_record_parses_and_binds() {
    for addend in [0, 4] {
        for dysymtabs in [0, 1] {
            let mut file = MachOFile::located(addend);
            file.dysymtabs = dysymtabs;
            file.binds(addend, &format!("addend {addend}, {dysymtabs} LC_DYSYMTAB"));
        }
    }
}

/// A SECOND `LC_SYMTAB` REFUSES AT PARSE, even when both commands name the
/// same table. A relocation names its symbol by index into the table, and with
/// two tables the linker decides which it reads; the reader used to keep the
/// last one in silence
/// (tests/f1_compile.rs::a_second_symbol_table_refuses_the_located_object
/// gives trust-cg's object a second, different table, and its comment records
/// what two linkers made of it).
#[test]
fn a_second_symbol_table_command_is_refused() {
    for addend in [0, 4] {
        let mut file = MachOFile::located(addend);
        file.binds(addend, "control: one LC_SYMTAB");
        for symtabs in [2, 3] {
            file.symtabs = symtabs;
            file.refuses_at_parse(
                &format!("{symtabs} LC_SYMTAB commands"),
                "more than one Mach-O symbol table (LC_SYMTAB)",
            );
        }
    }
}

/// A SECOND `LC_DYSYMTAB` REFUSES AT PARSE, decided the same way as a second
/// symbol table. One (as trust-cg writes) or none parses; what the command
/// says is not read.
#[test]
fn a_second_dynamic_symbol_table_command_is_refused() {
    let mut file = MachOFile::located(0);
    file.binds(0, "control: one LC_DYSYMTAB");
    for dysymtabs in [2, 3] {
        file.dysymtabs = dysymtabs;
        file.refuses_at_parse(
            &format!("{dysymtabs} LC_DYSYMTAB commands"),
            "more than one Mach-O dynamic symbol table (LC_DYSYMTAB)",
        );
    }
}

/// AN `ARM64_RELOC_ADDEND` ENTRY OUTSIDE A CODE SECTION REFUSES AT PARSE,
/// whatever its value. Paired with the record's pointer, an entry of value
/// ZERO used to bind (the admission compares the parsed addend with zero, and
/// a zero entry parsed as no entry), over an addend in place of 0 or of 4;
/// non-zero entries were refused by the admission and now refuse here too. The
/// same holds in the file name's section and in an unwind section, where no
/// admission is asked.
#[test]
fn an_addend_entry_outside_a_code_section_is_refused() {
    for in_place in [0, 4] {
        MachOFile::located(in_place).binds(in_place, "control: the pointer with no ADDEND entry");
        for value in [0, 4, -1, 0x7f_ffff, -0x80_0000] {
            let mut file = MachOFile::located(in_place);
            file.sections[LOC_SECTION].relocations.insert(0, addend_entry(0, value));
            file.refuses_at_parse(
                &format!("ADDEND {value} paired with the record's pointer over {in_place}"),
                "ARM64_RELOC_ADDEND in `__DATA,__const`, which is not a code section",
            );
        }
    }
    // In the file name's section (read-only data), paired with a pointer there.
    let mut file = MachOFile::located(0);
    file.sections[FILE_SECTION].relocations = vec![addend_entry(0, 0), unsigned_entry(0, LOC_SYM)];
    file.refuses_at_parse(
        "ADDEND 0 in the file name's section",
        "ARM64_RELOC_ADDEND in `__TEXT,__const`, which is not a code section",
    );
    // In an unwind section. Control: the same pointer there with no ADDEND
    // entry parses (what the binder makes of the section is not this test's).
    let unwind = |relocations: Vec<RelocEntry>| {
        let mut file = MachOFile::located(0);
        file.sections.push(FileSection {
            segment: "__LD",
            section: "__compact_unwind",
            flags: 0,
            bytes: vec![0; 32],
            relocations,
        });
        file
    };
    unwind(vec![unsigned_entry(0, FILE_SYM)]).parse().expect("control: an unwind pointer parses");
    unwind(vec![addend_entry(0, 0), unsigned_entry(0, FILE_SYM)]).refuses_at_parse(
        "ADDEND 0 in an unwind section",
        "ARM64_RELOC_ADDEND in `__LD,__compact_unwind`, which is not a code section",
    );
}

/// ONE `ARM64_RELOC_ADDEND` ENTRY PER RELOCATION, in a code section, where
/// the entry is read: a second entry before the relocation refuses at parse.
/// The parser used to let the later entry replace the earlier one in silence,
/// at the same address or at another. One entry still parses, and its value is
/// the relocation's addend (the controls).
#[test]
fn a_second_addend_entry_before_one_relocation_is_refused() {
    let code = |relocations: Vec<RelocEntry>| {
        let mut file = MachOFile::located(0);
        file.sections.push(FileSection {
            segment: "__TEXT",
            section: "__text",
            flags: S_ATTR_PURE_INSTRUCTIONS | S_ATTR_SOME_INSTRUCTIONS,
            bytes: [RET.to_le_bytes(), RET.to_le_bytes()].concat(),
            relocations,
        });
        file
    };
    const TEXT: usize = 2;
    for value in [5, 0, -3] {
        let object = code(vec![addend_entry(4, value), page21_entry(4, FILE_SYM)])
            .parse()
            .unwrap_or_else(|e| panic!("control: one ADDEND {value} entry should parse, but: {e}"));
        let [reloc] = object.sections[TEXT].relocations.as_slice() else {
            panic!("control: one relocation, the ADDEND entry folded into it")
        };
        assert_eq!((reloc.kind, reloc.addend), (RelocKind::Page21, i64::from(value)));
    }
    let two = "two ARM64_RELOC_ADDEND entries before one relocation in `__TEXT,__text`";
    for (what, first, second) in [
        ("at one address", addend_entry(4, 5), addend_entry(4, 0)),
        ("at one address, equal", addend_entry(4, 5), addend_entry(4, 5)),
        ("the first at another address", addend_entry(0, 5), addend_entry(4, 0)),
    ] {
        code(vec![first, second, page21_entry(4, FILE_SYM)]).refuses_at_parse(what, two);
    }
}
