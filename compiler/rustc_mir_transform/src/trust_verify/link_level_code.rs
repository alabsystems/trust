//! Trust (2026-10-01): CODE OR DATA THAT THE LINKER OR THE LOADER ACTS ON WITHOUT
//! A RUST CALL IS VERIFIED BY NO LANE.
//!
//! docs/KNOWN_HAZARDS.md, "CLOSED 2026-10-01 — `global_asm!` and
//! `#[link_section]` ran unverified code without a Rust call", is the hazard
//! this closes. It is the remainder of `symbol_interposition`'s class, found by
//! this item's own adversarial round against that rule: `symbol_interposition`
//! refuses a Rust item whose SYMBOL replaces an import; the two surfaces here
//! reach the linker and the loader without a Rust item the compiler can name.
//!
//! ## The hole
//!
//! Every Trust lane reads function MIR. Two stable source surfaces put bytes in
//! the program that no function's MIR contains, and the platform can run them
//! with no Rust call at all:
//!
//! * a `global_asm!` item is an object fragment the compiler hands to the
//!   assembler verbatim. It can DEFINE any symbol — `_malloc`, which std's
//!   `Global` allocator calls through `libc::malloc`, exactly the replacement
//!   `symbol_interposition` refuses for a `#[no_mangle]` item — or put a
//!   pointer to its own code in a constructor table (`__mod_init_func`,
//!   `.init_array`), which the loader calls before `main`;
//! * `#[link_section]` places a local function or static in a section of the
//!   program's choosing. A constructor table is such a section: the loader
//!   calls every pointer in it at load, so a static there whose value is DATA
//!   (or a function whose machine code is read as pointers) makes the loader
//!   jump to bytes that are not a function.
//!
//! Measured on main `0.10.0+g07091c92c` (2026-10-01), each a library beside a
//! trivially proved `pub fn` and a driver built verify-off against the rlib:
//! `global_asm!` defining `_malloc` (returns `16`) beside `*Box::new(x)` built
//! rc=0 ("2 proved ... 1 skipped") and the driver died of SIGSEGV (exit 139);
//! `global_asm!` putting a null-store routine in `__mod_init_func` built rc=0 and
//! died of SIGSEGV (139) before `main`; a `#[used] #[link_section =
//! "__DATA,__mod_init_func,mod_init_funcs"] static INIT: &[u8; 8]` built rc=0
//! and died of SIGILL (132) before `main`. A `#[naked]` function, the third
//! assembly surface, was already refused (its body does not lower).
//!
//! ## The rule
//!
//! In a verifying compilation, every local `global_asm!` item that is not a
//! `clean { … }` island, and every local function or static that carries
//! `#[link_section]`, is refused: an error under every fail-closed policy, a
//! warning under the explicit advisory survey. Decided from the def kind and
//! the codegen attributes the compiler itself computed, never from the asm text
//! or a list of section names: which sections a loader acts on is platform
//! knowledge no list keeps complete, and what an assembly template defines is
//! not something the compiler parses. This is the rule the certified-monitor
//! lane already applies to the same surface
//! (`reject_targo_certified_monitor_local_startup_surface`, "reject the complete
//! local surface rather than trying to recognize a platform-specific set of
//! initializer section names"); here it applies to every verifying build.
//!
//! * A `clean { … }` island shares `DefKind::GlobalAsm` but lowers no machine
//!   code (`trust_def_is_clean_island`); it is out of scope.
//! * A DEPENDENCY's assembly and sections rest on the dependency-soundness
//!   premise every verify-off crate's code rests on — with one part of that
//!   premise checked since 2026-10-04 by main's graph-wide allocator charge
//!   (`crate_graph_system_allocator_interposer`, reconciled here 2026-10-08): a
//!   crate anywhere in the graph, a dependency included, that holds non-island
//!   global assembly can define `_malloc`, so the graph is charged as one with a
//!   user allocator and every body that can reach the allocator carries the
//!   REFUSED `contract:global-alloc-dealloc-panic-free` row. Both stand: that
//!   charge covers the allocator channel wherever the assembly lives and leaves
//!   a body that never reaches the allocator credited; this rule refuses the
//!   LOCAL surface outright, because assembly can also define any other
//!   imported symbol or fill a constructor table, and `#[link_section]` is not
//!   read by that charge at all. A local `global_asm!` draws both.
//! * `#[naked]` functions are refused by the per-function walk already.
//!
//! What it costs: a crate with ANY `global_asm!` (even an empty template) or any
//! `#[link_section]` item (the `ctor`/`linkme`/`inventory` shapes, a firmware
//! vector table) is refused under the default policy, correct or not; the honest
//! recovery is to keep that code in a verify-off dependency, or the advisory
//! survey. For assembly the first recovery is partial since 2026-10-04: with
//! the assembly in a dependency this refusal is gone, and the graph-wide
//! allocator charge above still refuses every body that can reach the
//! allocator.

use super::*;

/// One refused surface: a `global_asm!` item, or an item placed by
/// `#[link_section]` (with its section).
enum LinkLevelSurface {
    GlobalAsm(LocalDefId),
    LinkSection(LocalDefId, Symbol),
}

/// Every local `global_asm!` item (islands excepted) and every local function or
/// static with `#[link_section]`, in the order `hir_crate_items` yields the
/// definitions (source order), so the diagnostics are deterministic.
fn link_level_surfaces(tcx: TyCtxt<'_>) -> Vec<LinkLevelSurface> {
    let mut found = Vec::new();
    for local in tcx.hir_crate_items(()).definitions() {
        match tcx.def_kind(local) {
            DefKind::GlobalAsm => {
                if !tcx.trust_def_is_clean_island(local.to_def_id()) {
                    found.push(LinkLevelSurface::GlobalAsm(local));
                }
            }
            DefKind::Fn | DefKind::AssocFn | DefKind::Static { .. } => {
                if let Some(section) = tcx.codegen_fn_attrs(local).link_section {
                    found.push(LinkLevelSurface::LinkSection(local, section));
                }
            }
            _ => {}
        }
    }
    found
}

/// Refuse (or, under the explicit advisory survey, report) every local
/// `global_asm!` item and `#[link_section]` item. See the module doc.
/// Crate-level, after the walk, beside `symbol_interposition`.
pub(super) fn refuse_link_level_code(tcx: TyCtxt<'_>, policy: &TrustVerifyPolicy) {
    for surface in link_level_surfaces(tcx) {
        let (span, message, reach, options) = match surface {
            LinkLevelSurface::GlobalAsm(local) => (
                tcx.def_span(local),
                String::from(
                    "Trust verification cannot accept global assembly: a `global_asm!` item is \
                     machine code no Trust lane verifies, and the platform can run it without \
                     any Rust call",
                ),
                String::from(
                    "the assembly can define a symbol a linked crate imports (a `_malloc` that \
                     std's `Global` allocator then calls) or put its own code in a constructor \
                     table the loader runs before `main`; no obligation of this crate covers \
                     either",
                ),
                "Options: move the assembly into a dependency built without verification \
                 (its code then rests on the dependency premise; a graph that holds global \
                 assembly is still charged as one with a user allocator, because assembly \
                 can define `malloc`, so every body that can reach the allocator keeps the \
                 refused `contract:global-alloc-dealloc-panic-free` row), or `-Z \
                 trust-policy=advisory` to record this as a warning",
            ),
            LinkLevelSurface::LinkSection(local, section) => (
                tcx.def_span(local),
                format!(
                    "Trust verification cannot accept `#[link_section = \"{section}\"]` on `{}`: \
                     a custom section places the item where the linker or the loader acts on \
                     it, and no Trust lane verifies what that section means",
                    tcx.def_path_str(local)
                ),
                String::from(
                    "a constructor table (`__mod_init_func`, `.init_array`, `.CRT$XCU`, ...) \
                     makes the loader call every pointer in it before `main`, without any Rust \
                     call: a value there that is data, or code read as pointers, sends the \
                     process to bytes that are not a function; which sections a loader acts on \
                     is platform knowledge, so every `#[link_section]` is refused",
                ),
                "Options: drop `#[link_section]`, place the item from a dependency built \
                 without verification, or `-Z trust-policy=advisory` to record this as a \
                 warning",
            ),
        };
        if policy.fail_closed() {
            tcx.dcx().struct_span_err(span, message).with_note(reach).with_note(options).emit();
        } else {
            tcx.dcx()
                .struct_span_warn(span, message)
                .with_note(reach)
                .with_note(options)
                .with_note(
                    "reported, not failed, only because this is the explicit advisory survey; \
                     every fail-closed policy refuses it",
                )
                .emit();
        }
    }
}
