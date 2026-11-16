//! Trust (2026-09-30): A LOCAL DEFINITION WHOSE SYMBOL IS ONE A LINKED CRATE
//! IMPORTS REPLACES THAT CRATE'S CALLEE, AND NO LANE CHECKS THE REPLACEMENT.
//!
//! docs/KNOWN_HAZARDS.md, "CLOSED 2026-09-30 — a local `#[no_mangle]`
//! definition of a symbol std imports (`malloc`) was believed by the std code
//! that calls it", is the hazard this closes. It is the link-level twin of
//! `unsafe_impl_promise`: there the program hands std an allocator through a
//! trait, here through the linker.
//!
//! ## The hole
//!
//! std reaches the platform through `extern` declarations — `libc::malloc`,
//! `libc::free`, `libc::write`, ... — whose definitions the linker supplies. A
//! crate that DEFINES an item under one of those symbol names (`#[no_mangle]
//! pub extern "C" fn malloc`, `#[export_name = "free"]`) is linked ahead of the
//! system library, so std's `Global` allocator, its I/O, its threads call the
//! program's function instead. Trust verifies that function as ordinary code
//! (its own panics and `unsafe` operations), and credits the std code that
//! calls it under the sysroot premise, which assumes the imported function
//! keeps ITS contract — that `malloc` returns memory it owns. Nothing verifies
//! that the replacement does.
//!
//! Measured on main `0.10.0+g07091c92c` (2026-09-30): a library whose
//! `#[no_mangle] pub extern "C" fn malloc(_: usize) -> *mut u8` returns
//! `16 as *mut u8` — safe code — beside `pub fn f(x: u64) -> u64 { *Box::new(x) }`
//! built rc=0 under the default policy, `certify` and the advisory survey alike,
//! and a driver built verify-off against that rlib died of SIGSEGV (exit 139).
//!
//! ## The rule
//!
//! In a verifying compilation, a local function or static that carries an
//! extern indicator (`#[no_mangle]`, `#[export_name]`, `#[linkage]`) and whose
//! symbol name equals the symbol of a foreign item — an `extern` block
//! declaration — of ANY crate this compilation links (the sysroot's `libc`,
//! `std`, ... or a dependency's) is refused: an error under every fail-closed
//! policy, a warning under the explicit advisory survey. Decided from the two
//! symbol names the compiler itself computes (`symbol_name` of the local item
//! and of the foreign item), never from a list of "dangerous" names.
//!
//! * A local item under a symbol no linked crate imports (a C-ABI export such as
//!   `#[no_mangle] extern "C" fn mylib_add`) is out of scope: no linked code
//!   calls it in place of something else, and its callers inside this crate
//!   are verified against its body.
//! * A collision with a symbol a linked crate DEFINES (not imports) is out of
//!   scope: when the defining object is linked (std is one object) it is a
//!   duplicate-definition link error, not a silent replacement. Archive-member
//!   selection that could leave a multi-object dependency's definition unlinked
//!   in favour of a local one is not modeled; it is recorded with the remaining
//!   premise below.
//! * The local crate's own `extern` declarations are out of scope: a call
//!   through them is this crate's own `unsafe` code, charged where it is made.
//! * The local `#[panic_handler]` is out of scope: it is the `panic_impl` weak
//!   lang item, which `core` imports by design (`extern "Rust" { #[lang =
//!   "panic_impl"] fn panic_impl(..) -> !; }`, symbol `rust_begin_unwind`) for
//!   the program to supply, and the whole of the contract `core` relies on is
//!   its type, `fn(&PanicInfo<'_>) -> !`, which the type checker enforces
//!   (`check_panic_info_fn`). Its body is verified as ordinary code like any
//!   other function's. Decided by the lang-item table (`tcx.lang_items()`),
//!   never by the symbol's name. Measured 2026-09-30 on the first version of
//!   this rule (`0.10.0+g2a7366482`): without it every `#![no_std]` crate with
//!   its own panic handler was refused
//!   (`no_std_panic_handler_owner_keeps_core_credit.rs#local_handler` went red).
//!   No other weak lang item (`eh_personality`, ...) is exempt: their contract
//!   is an ABI no type states.
//!
//! What stays open, recorded in the KNOWN_HAZARDS entry: a symbol linked code
//! calls with NO Rust `extern` declaration anywhere in the crate graph — a
//! libcall LLVM emits by itself (`memcpy`/`memset` for a large copy where no
//! crate declares them, `__stack_chk_fail`, ...) or one a C object linked into
//! the program imports. Those are named nowhere the compiler can read.
//!
//! ## Beside the graph-wide allocator charge (reconciled 2026-10-08)
//!
//! Main closed the allocator half of this class independently
//! (`crate_graph_system_allocator_interposer`, 2026-10-03/04, docs/KNOWN_HAZARDS.md
//! "CLOSED 2026-10-03 — allocation failure was credited as an abort while an
//! allocation-error hook may panic (and a crate defining `malloc` was not a user
//! allocator)"): a crate ANYWHERE in the graph — this one or a non-sysroot
//! dependency — that defines one of eight libc allocator link names (or holds
//! non-island global assembly) makes the graph one with a user allocator, and
//! every body that can reach the allocator is charged the REFUSED
//! `contract:global-alloc-dealloc-panic-free` row. Both stand, because they ask
//! different questions and neither subsumes the other:
//!
//! * that charge reads a DEPENDENCY's definitions, which this rule does not (a
//!   dependency's items rest on the dependency premise here), and it is about
//!   the panic-freedom of the allocator channel: a body that never reaches the
//!   allocator keeps its credit beside a `malloc` that returns `16`;
//! * this rule refuses the local DEFINITION, for ANY symbol a linked crate
//!   imports (`write`, `pthread_create`, a foreign static, a dependency's hook),
//!   decided from the two computed symbol names and no list, and it is about the
//!   imported function's contract (memory safety), so `memory-safe` refuses it
//!   too and it is an error whether or not any local body allocates.
//!
//! A local `#[no_mangle] fn malloc` therefore draws both: this error on the
//! definition, and main's row on each body that reaches the allocator. The
//! diagnostic here says so when the symbol is one of main's allocator link
//! names (`is_system_allocator_link_symbol`), so that "move it into a
//! dependency" is not read as a way out of the second.

use super::*;

/// One refused definition: the local item, the symbol it exports, and a foreign
/// item that imports the same symbol.
struct InterposedImport {
    local: LocalDefId,
    symbol: String,
    import: DefId,
}

/// Is `def_id` a function or static, the two kinds that own a linker symbol?
fn owns_symbol(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn | DefKind::Static { .. })
}

/// Every local definition that exports a symbol some linked crate imports, in
/// the order `hir_crate_items` yields the definitions (source order), so the
/// diagnostics are deterministic. The imports are enumerated only when at least
/// one local item carries an extern indicator, so an ordinary crate pays nothing.
fn interposed_imports(tcx: TyCtxt<'_>) -> Vec<InterposedImport> {
    let mut exported: Vec<(LocalDefId, String)> = Vec::new();
    for local in tcx.hir_crate_items(()).definitions() {
        let def_id = local.to_def_id();
        if !owns_symbol(tcx, def_id) {
            continue;
        }
        // A generic item has no single symbol (and `#[no_mangle]` on one is
        // already rejected); its instances are mangled.
        if tcx.generics_of(def_id).requires_monomorphization(tcx) {
            continue;
        }
        if !tcx.codegen_fn_attrs(def_id).contains_extern_indicator() {
            continue;
        }
        // The program's `#[panic_handler]`: the weak lang item `core` imports by
        // design, whose whole contract is its type-checked signature (see the
        // module doc). Asked of the lang-item table, not of the symbol.
        if tcx.lang_items().panic_impl() == Some(def_id) {
            continue;
        }
        let symbol = tcx.symbol_name(ty::Instance::mono(tcx, def_id)).name.to_string();
        exported.push((local, symbol));
    }
    if exported.is_empty() {
        return Vec::new();
    }
    // The symbol of every foreign item of every linked crate, first declaration
    // kept (crate order, then each crate's declaration order: deterministic).
    let mut imports: FxHashMap<String, DefId> = FxHashMap::default();
    for &cnum in tcx.crates(()) {
        for module in tcx.foreign_modules(cnum).values() {
            for &item in &module.foreign_items {
                if !owns_symbol(tcx, item) {
                    continue;
                }
                let symbol = tcx.symbol_name(ty::Instance::mono(tcx, item)).name.to_string();
                imports.entry(symbol).or_insert(item);
            }
        }
    }
    exported
        .into_iter()
        .filter_map(|(local, symbol)| {
            let import = *imports.get(&symbol)?;
            Some(InterposedImport { local, symbol, import })
        })
        .collect()
}

/// Refuse (or, under the explicit advisory survey, report) every local
/// definition that replaces a linked crate's import. See the module doc.
/// Crate-level, after the walk, beside `unsafe_impl_promise`.
pub(super) fn refuse_interposed_imports(tcx: TyCtxt<'_>, policy: &TrustVerifyPolicy) {
    for found in interposed_imports(tcx) {
        let span = tcx.def_span(found.local);
        let symbol = &found.symbol;
        let import_path = tcx.def_path_str(found.import);
        let importer = tcx.crate_name(found.import.krate);
        let sysroot = trust_mir_extract::def_is_in_real_sysroot_crate(tcx, found.import);
        let relier = if sysroot {
            "std/core/alloc code, whose calls Trust credits under the sysroot premise that the \
             imported function keeps its contract"
        } else {
            "code of that crate, which this build does not verify"
        };
        let message = format!(
            "Trust verification cannot accept a definition of the symbol `{symbol}`: the crate \
             `{importer}` imports that symbol (`{import_path}`), so this definition replaces the \
             function it calls, and no Trust lane verifies that the replacement keeps its \
             contract"
        );
        let reliance = format!(
            "every call the linked program makes through `{import_path}` reaches this item \
             instead, including {relier}; if it breaks that contract (a `malloc` that returns \
             memory it does not own) the caller has undefined behaviour with no obligation of \
             this crate covering it"
        );
        let options = "Options: export the item under a symbol no linked crate imports (drop \
                       `#[no_mangle]`/`#[export_name]`, or rename it), or `-Z \
                       trust-policy=advisory` to record this as a warning";
        // The graph-wide allocator charge (`crate_graph_system_allocator_interposer`)
        // reads the same definition when the symbol is one std's `System` allocator
        // calls; say so, so that moving the definition into a dependency is not
        // read as a way out of it (see the module doc, "Beside the graph-wide
        // allocator charge"). Diagnostic only.
        let allocator_charge = is_system_allocator_link_symbol(symbol).then(|| {
            format!(
                "`{symbol}` is a libc allocator symbol std's default `System` allocator calls, \
                 so this crate graph is also charged as one with a user allocator: every body \
                 that can reach the allocator carries the refused \
                 `contract:global-alloc-dealloc-panic-free` row, wherever the definition lives \
                 (this crate or a dependency)"
            )
        });
        // `struct_span_err` and `struct_span_warn` yield different `Diag` payload
        // types, so the two arms are spelled out.
        if policy.fail_closed() {
            let mut diag = tcx.dcx().struct_span_err(span, message).with_note(reliance);
            if let Some(note) = allocator_charge {
                diag.note(note);
            }
            diag.with_note(options).emit();
        } else {
            let mut diag = tcx.dcx().struct_span_warn(span, message).with_note(reliance);
            if let Some(note) = allocator_charge {
                diag.note(note);
            }
            diag.with_note(options)
                .with_note(
                    "reported, not failed, only because this is the explicit advisory survey; \
                     every fail-closed policy refuses it",
                )
                .emit();
        }
    }
}
