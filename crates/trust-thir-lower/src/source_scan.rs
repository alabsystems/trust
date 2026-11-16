//! Trust (2026-09-17): the ONE definition of "the production section" for the
//! source-scan tests in `lib.rs`.
//!
//! WHY. Sixty-one of those tests bound "production" at the first `#[cfg(test)]` in
//! the file, each with its own copy of the same eleven lines. On 2026-09-10 two
//! OUT-OF-LINE test modules (`#[cfg(test)] mod array_write_tests;` and
//! `mod slice_index_tests;`) joined the module list near the top of the file — by
//! fleet discipline, one touchpoint per new file — and every scan silently
//! shrank from ~49,000 lines of production to the first 292. Sixty-one tests went
//! red for a week and nothing said so: no push lane runs a `crates/` test.
//!
//! WHAT. An out-of-line `#[cfg(test)] mod name;` declaration says WHERE tests
//! live; it is not where they begin. The production section ends at the first
//! `#[cfg(test)]` that opens an INLINE module (`mod name {`). Every scan now asks
//! this one function, so the next out-of-line declaration cannot move the bound,
//! and a change to the rule is a change in exactly one place.
//!
//! Trust (2026-09-28): the ONE place a test of this crate reads a source file BY PATH.
//!
//! WHY. The producer (`lib.rs`, ~60,000 lines) is about to be split into modules. Every scan
//! read it as `include_str!("lib.rs")`, so after the split each scan would silently shrink to
//! whatever is left in `lib.rs` — the 2026-09-10 blinding above, once per scan, with a red test
//! only where a count happens to fall to zero and a vacuous green everywhere else.
//!
//! WHAT.
//! * [`producer_text`] is the producer as ONE text: every [`PRODUCER_FILES`] file's production
//!   section, then every file's test section, with [`FILE_BOUNDARY_TOKEN`] between two sections
//!   that come from different files. While the producer is the single file `lib.rs` it IS
//!   `include_str!("lib.rs")`, byte for byte. The production composition test
//!   retains that original section and includes every newly classified hook.
//! * [`ScanExt`] holds the bounds a scan draws from an anchor — the next method, a following
//!   needle, a window, an order — and every one of them stops at a file boundary, so a span can
//!   never run from one producer file into the next. Byte offsets of two different files are
//!   not "before" or "after" each other; [`ScanExt::precedes_in_file`] says so.
//! * `every_source_file_of_this_crate_is_classified` walks `src/` and requires every `.rs` file
//!   to be named in exactly one of [`PRODUCER_FILES`], [`PRODUCER_TEST_FILES`] and
//!   [`NON_PRODUCER_FILES`], and every file of the PRODUCER TREE (`producer.rs`, `producer/**`,
//!   `producer_tests/**`: where the split puts what it moves) to be scanned in the section its
//!   path says — `producer_tests/**` as test source, the rest as production. A file there that is
//!   unlisted, listed as NON_PRODUCER, or listed in the other producer list fails by name.
//!   Being listed is not enough: a classification is a claim, and this check holds the claim to
//!   the file's path.
//! * `lowercx_impls_live_in_producer_files` requires every `impl … LowerCx` block outside
//!   [`PRODUCER_FILES`] to belong to one of the extension files that predate this guard, with
//!   exactly the members [`LEGACY_LOWERCX_EXTENSIONS`] pins. A `LowerCx` member moved into any
//!   other file (a new one, a misclassified one, one of those) fails, naming the file and the
//!   member.
//! * WHAT NEITHER SEES, stated rather than implied away: an item that is not a member of an
//!   `impl … LowerCx` block (a free `fn`, a type, a constant) moved into an EXISTING
//!   [`NON_PRODUCER_FILES`] file outside the producer tree. Nothing in that file's text says the
//!   item was producer code, so no check here can tell. Each NON_PRODUCER row is a reviewed
//!   decision, and a move into one of those files is a question for review. Nor can a check here
//!   tell that a file under `producer/` holds only tests: it is read as production, so an
//!   out-of-line producer test file belongs under `producer_tests/`.
//! * `no_test_reads_a_source_file_by_path_outside_source_scan` fails on a NEW by-path read of a
//!   source file anywhere else in the crate. The reads that predate it are listed in
//!   [`GRANDFATHERED_READS`] by exact count; that list may only shrink.

use std::collections::BTreeMap;
use std::sync::LazyLock;

/// Byte offset at which `source`'s production section ends: the first
/// `#[cfg(test)]` attribute whose next line opens an inline module (`mod name {`).
/// `None` if the file has no inline test module at all.
///
/// The needle is assembled at run time because this crate's own `lib.rs` is read
/// through `include_str!`, and a literal `#[cfg(test)]` in a scan would match the
/// scan's own source.
pub(crate) fn production_end(source: &str) -> Option<usize> {
    let marker = format!("\n#[cfg({})]", "test");
    let mut from = 0;
    while let Some(rel) = source[from..].find(&marker) {
        let at = from + rel;
        let after = at + marker.len();
        let next_line = source[after..].strip_prefix('\n').and_then(|rest| rest.lines().next()).unwrap_or("");
        let trimmed = next_line.trim();
        if trimmed.starts_with("mod ") && trimmed.ends_with('{') {
            return Some(at);
        }
        from = after;
    }
    None
}

/// Where one producer file ends and the next begins inside [`producer_text`]. Not Rust, not a
/// comment and not whitespace, so it survives every transform the scans apply (comment-line
/// stripping, whitespace flattening) and no scan needle contains it.
pub(crate) const FILE_BOUNDARY_TOKEN: &str = "@@producer-file-boundary@@";
const FILE_BOUNDARY: &str = "\n@@producer-file-boundary@@\n";

// BEGIN producer-files
/// Every file holding PRODUCER code, `lib.rs` first, each as (path under `src/`, contents).
/// A file that takes items out of `lib.rs` is added HERE, in the same commit that moves them.
pub(crate) const PRODUCER_FILES: &[(&str, &str)] = &[
    ("lib.rs", include_str!("lib.rs")),
    ("ordered_slice_match.rs", include_str!("ordered_slice_match.rs")),
    ("shared_borrow.rs", include_str!("shared_borrow.rs")),
    ("float_storage.rs", include_str!("float_storage.rs")),
    ("primitive_storage.rs", include_str!("primitive_storage.rs")),
    ("primitive_unit_transport.rs", include_str!("primitive_unit_transport.rs")),
    ("float_reference_binding.rs", include_str!("float_reference_binding.rs")),
    ("coroutine_borrow.rs", include_str!("coroutine_borrow.rs")),
    ("drops/owned_shared.rs", include_str!("drops/owned_shared.rs")),
    ("shared_receiver_freeze.rs", include_str!("shared_receiver_freeze.rs")),
    ("indexed_field_assignment.rs", include_str!("indexed_field_assignment.rs")),
    // The callee/body source-ABI derivation `lower_body` and `LowerCx` call: 51558bd9ff moved
    // it out of a `LowerCx` method in `lib.rs` (`CalleeRef::is_rust_abi`), so it stays visible
    // to every producer scan.
    ("calling_convention.rs", include_str!("calling_convention.rs")),
    ("join_provenance.rs", include_str!("join_provenance.rs")),
    ("raw_entry_field.rs", include_str!("raw_entry_field.rs")),
    ("raw_pointer_coercion.rs", include_str!("raw_pointer_coercion.rs")),
    ("core_wrapping_add.rs", include_str!("core_wrapping_add.rs")),
    ("template_lowering/callable.rs", include_str!("template_lowering/callable.rs")),
    ("concrete_type_transport.rs", include_str!("concrete_type_transport.rs")),
    ("instance_const.rs", include_str!("instance_const.rs")),
    ("effect_conservation/thir_source/capture.rs", include_str!("effect_conservation/thir_source/capture.rs")),
    // Original pre-IR source intake and the source claim written by production metadata.
    // Both remain visible to every producer scan; neither grants proof/admission.
    ("source_word64.rs", include_str!("source_word64.rs")),
    ("source_word64/record.rs", include_str!("source_word64/record.rs")),
];
/// Out-of-line test files of producer modules (all test code, no production section), each under
/// `producer_tests/`.
pub(crate) const PRODUCER_TEST_FILES: &[(&str, &str)] = &[];
// END producer-files

/// Every other `.rs` file under `src/`: files no producer scan reads. Each row is a decision —
/// moving producer items into one of these files would hide them from every scan, so a producer
/// file never goes here, and a NEW file goes here only if it holds no producer code. Two checks
/// hold part of that decision (a producer-tree path is never a row here; an `impl … LowerCx`
/// block here is in one of the files pinned below); the rest is review (see the module doc).
pub(crate) const NON_PRODUCER_FILES: &[&str] = &[
    // `impl LowerCx` extensions that landed as files of their own before this guard ("fleet
    // discipline": one `lib.rs` touchpoint per new file). No producer scan reads them. Listing
    // them as producer files would WIDEN what every scan sees — a change with its own evidence,
    // not part of a byte-for-byte move. Their `LowerCx` members are pinned, exactly, in
    // `LEGACY_LOWERCX_EXTENSIONS`. `drops.rs` (the producer's drop planner and its placement
    // hooks, step 2 increment 4b) joined the first three while this guard was in review; the
    // reveal-funnel ratchet reads it by name, through `sibling_source`.
    "const_index_bounds.rs",
    "direct_formula_capture.rs",
    "direct_operand_widening.rs",
    "drops.rs",
    // The other lowering stages, the oracles, and their helpers. `drop_glue.rs` is the
    // DROP-GLUE producer (a body synthesized per type, judged by `drop_glue_oracle.rs`), not
    // the THIR -> trust-ir producer these scans pin; `instance_admission.rs` is the instance
    // lane's frozen admission, which its own tests in `lib.rs` read through `sibling_source`.
    "artifact_publication.rs",
    "clean_origin_join.rs",
    // The Clean-origin join's pre-mutation physical-id admission (no `LowerCx` member).
    "clean_origin_join/checked_ids.rs",
    "clean_origin_purity.rs",
    "clean_origin_reach.rs",
    // Crate assembly's typed by-value closure adapters and per-body closure-layout merge; read
    // by `crate_module.rs` and `effect_conservation/closure_adapters.rs`. No `LowerCx` member.
    "closure_adapter.rs",
    "closure_layout.rs",
    "contract_disclosure.rs",
    // WS5.5 (staged): the contract-bound carry, its zero-authority shadow, and the clause
    // renderer moved out of `contract_disclosure.rs`. None holds an `impl … LowerCx` block.
    "contract_carry.rs",
    "contract_carry_shadow.rs",
    "contract_render.rs",
    "crate_module.rs",
    "crate_module/scalar_correspondence.rs",
    "crate_module/seam_reference.rs",
    "crate_module/static_globals.rs",
    "crate_module/validation_type_context.rs",
    // Pure assembly dependency bound; no LowerCx extension or THIR source scan.
    "crate_module/zero_array_struct.rs",
    "crate_module/zero_array_struct/tests.rs",
    "differential.rs",
    "differential/compare_entries_reference.rs",
    // Carries pass 1's local-definition assignments into publication for `crate_module.rs`;
    // no `LowerCx` member and no producer items.
    "direct_definition_map.rs",
    "direct_obligations.rs",
    "drop_glue.rs",
    "drop_glue_oracle.rs",
    "drop_oracle.rs",
    "effect_conservation.rs",
    // `effect_conservation.rs`'s own submodules: the adapter-protocol effects, exact store
    // correspondence and store-only reaching-copy facts. No `LowerCx` member.
    "effect_conservation/closure_adapters.rs",
    "effect_conservation/exact_store.rs",
    // Pure shared D28 comparison over decoded retained facts; no LowerCx member.
    "effect_conservation/retained.rs",
    "effect_conservation/retained/tests.rs",
    // Data/registry only; the genuine source capturer is included above.
    "effect_conservation/thir_source.rs",
    "effect_conservation/thir_source/concrete.rs",
    "effect_conservation/thir_source/wire.rs",
    "effect_conservation/thir_source/binding.rs",
    "effect_conservation/thir_source/tests.rs",
    "effect_conservation/store_root_facts.rs",
    "effect_conservation/store_root_facts/core.rs",
    "finalization_probe.rs",
    "flip.rs",
    "flip_registry.rs",
    "generated_coroutine.rs",
    "generated_coroutine/fixtures/refusals.rs",
    "generated_coroutine/fixtures/scalar_capture.rs",
    "generated_coroutine/model.rs",
    "instance_admission.rs",
    "instance_flip.rs",
    "instance_probe.rs",
    "instance_seam_test.rs",
    "lineage.rs",
    // Read-only legacy metadata identity recovery and its codec controls.
    // No LowerCx extension, producer body, admission or codegen authority.
    "metadata_site.rs",
    "metadata_site/resolve.rs",
    "metadata_site/tests.rs",
    // Immutable checked handoff facts; no LowerCx/body or admission constructor.
    "codegen_declarations.rs",
    // Foreign scalar prototypes read at crate finalization, instance admission and rmeta entry;
    // `read` refuses inside producer lowering. No `LowerCx` member and no producer caller.
    "foreign_signature.rs",
    "foreign_signature/tests.rs",
    // WS5.2: crate finalization's link-time naming (`Function.name` as the link-time symbol)
    // and the D17 instance-lane carve-out; no `LowerCx` member, read by `crate_module.rs` and
    // the Clean-origin collector.
    "link_symbol.rs",
    "mir_differential.rs",
    "refusal_ledger.rs",
    "remap_certificate.rs",
    "rmeta_entry.rs",
    "source_provenance.rs",
    "source_static_readback.rs",
    "spawn_census.rs",
    "template_lowering.rs",
    // Pending source data/keys: no runtime LowerCx extension or admission.
    "template_lowering/pending.rs",
    "template_key.rs",
    "template_key/rustc.rs",
    "template_key/tests.rs",
    // Authenticated S inputs and an unlicensed scalar graph constructor. These
    // hold no LowerCx extension or source-lowering implementation.
    "template_metadata.rs",
    // Actual callable metadata/type-image custody; no source body or LowerCx member.
    "template_metadata/callable_header.rs",
    "template_metadata/unit_return.rs",
    "template_metadata/const_host.rs",
    "template_metadata/type_host.rs",
    "template_metadata/type_host/tests.rs",
    "template_metadata/instantiate.rs",
    // The diagnostic template-instance TEST-ORACLE (PKG-C2d2 slice 1): reads, never lowers.
    "template_metadata/oracle.rs",
    "template_metadata/rustc.rs",
    "template_metadata/tests.rs",
    "to_mir.rs",
    "tuple_layout.rs",
    "uniform_array_spelling.rs",
    // Those files' out-of-line test modules.
    "clean_origin_join/bulk_memory_type_remap_tests.rs",
    "clean_origin_join/checked_ids/reference_tests.rs",
    "clean_origin_join/unwind_and_site_refusal_tests.rs",
    "clean_origin_purity/tests.rs",
    "contract_carry/tests.rs",
    "contract_disclosure/tests.rs",
    "crate_module/carrier_ledger_tests.rs",
    "crate_module/drop_splice_tests.rs",
    "crate_module/seam_scratch_tests.rs",
    "crate_module/splice_refusal_tests.rs",
    "crate_module/static_globals/tests.rs",
    "crate_module/validation_type_context_caller_tests.rs",
    "differential/assert_operand_demand_tests.rs",
    "drop_glue/tests.rs",
    "drop_glue_oracle/tests.rs",
    "drops/tests.rs",
    "effect_conservation/init_worklist_tests.rs",
    "effect_conservation/store_root_facts/tests.rs",
    "effect_conservation/tests.rs",
    "generated_coroutine/model_tests.rs",
    "instance_admission/tests.rs",
    "rmeta_entry/tests.rs",
    "rmeta_entry/envelope_tests.rs",
    "source_static_readback/tests.rs",
    // Unit-test code only, like the other out-of-line helper tests above.
    "source_word64/record/tests.rs",
    "spawn_census/tests.rs",
    "template_lowering/tests.rs",
    // `lib.rs`'s out-of-line test modules. No scan has ever read them as producer text.
    "array_write_tests.rs",
    "array_write_tests/temporary_support.rs",
    // `lib.rs` includes this module only under `cfg(test)`; it holds six tests and a helper.
    "fat_shape_tests.rs",
    "flip_refinement_tests.rs",
    "flip_registry_refinement_tests.rs",
    "frozen_section_cut.rs",
    "mir_differential_refinement_tests.rs",
    "mir_differential_tailcall_ratification_tests.rs",
    // Pure layout-table helper tests; no producer code or LowerCx extension.
    "replacement_layout_tests.rs",
    "slice_index_tests.rs",
    "struct_registration_tests.rs",
    "slice_index_tests/array_support.rs",
    "slice_index_tests/array_support/projected_support.rs",
    "slice_index_tests/array_support/rvalue_support.rs",
    "slice_index_tests/support.rs",
    "slice_index_tests/unit_support.rs",
    // This file.
    "source_scan.rs",
];

/// The `impl LowerCx` extension files that predate this guard (the first four
/// [`NON_PRODUCER_FILES`] rows), each with the EXACT members (`fn`, `const`, `type`) of its
/// `impl … LowerCx` blocks, in source order. No producer scan reads these files, so a member
/// added to one is a member hidden from every producer scan: do not grow this list — put new
/// `LowerCx` code in a [`PRODUCER_FILES`] file. A member leaves its row in the commit that moves
/// it into a producer file or deletes it; a row leaves when its file becomes a
/// [`PRODUCER_FILES`] row.
pub(crate) const LEGACY_LOWERCX_EXTENSIONS: &[(&str, &[&str])] = &[
    ("const_index_bounds.rs", &["emit_and_record_const_index_bounds"]),
    (
        "direct_formula_capture.rs",
        &[
            "record_direct_assert_typed",
            "direct_formula_outcome",
            "direct_formula_case",
            "direct_formula_width",
            "direct_formula_operand",
            "direct_formula_leaf_operand",
        ],
    ),
    (
        "direct_operand_widening.rs",
        &["thir_binding_census", "widened_named_operand", "nested_checked_operand"],
    ),
    (
        "drops.rs",
        &[
            "plan_drops",
            "record_drop_value",
            "record_drop_borrow_slot",
            "emit_planned_drops",
            "emit_planned_drops_through",
            "emit_one_drop",
            "spill_and_drop",
            "emit_temp_drop",
            "slot_ty",
            "record_drop_site",
            "push_drop_node",
            "alloc_entry_slot",
            "finish_drops",
        ],
    ),
];

/// Is `path` (under `src/`) in the PRODUCER TREE — the module root `producer.rs`, the modules
/// under `producer/` that take items out of `lib.rs`, or the test files under
/// `producer_tests/` (the split plan's layout, §3.1 item 6)? A file there is always scanned: one
/// under `producer_tests/` as a [`PRODUCER_TEST_FILES`] row, every other one as a
/// [`PRODUCER_FILES`] row.
fn in_producer_tree(path: &str) -> bool {
    path == "producer.rs" || path.starts_with("producer/") || in_producer_test_tree(path)
}

/// Is `path` under `producer_tests/`, the one place a [`PRODUCER_TEST_FILES`] row may live? Those
/// rows are read as TEST source, after every production section: producer code in one would
/// leave every scan that bounds itself at the production section. And a test file listed in
/// [`PRODUCER_FILES`] would put test source into that section.
fn in_producer_test_tree(path: &str) -> bool {
    path.starts_with("producer_tests/")
}

/// The classification verdict for the `.rs` files on disk (paths under `src/`): one line per
/// problem, empty when every file is listed exactly once, every listed file exists, every
/// producer-tree file is scanned, and each is scanned in the section its path says.
fn classification_problems(
    on_disk: &[&str],
    producer: &[&str],
    producer_tests: &[&str],
    non_producer: &[&str],
) -> Vec<String> {
    let mut problems = Vec::new();
    let mut listed: BTreeMap<&str, &str> = BTreeMap::new();
    for (path, class) in producer
        .iter()
        .map(|p| (*p, "PRODUCER_FILES"))
        .chain(producer_tests.iter().map(|p| (*p, "PRODUCER_TEST_FILES")))
        .chain(non_producer.iter().map(|p| (*p, "NON_PRODUCER_FILES")))
    {
        // The FIRST listing stands, so a duplicate is one problem, not also a misclassification.
        match listed.entry(path) {
            std::collections::btree_map::Entry::Occupied(first) => problems.push(format!(
                "src/{path} is listed twice ({} and {class}); a file has one classification",
                first.get(),
            )),
            std::collections::btree_map::Entry::Vacant(slot) => {
                slot.insert(class);
            }
        }
    }
    for path in on_disk {
        match listed.get(path) {
            None => problems.push(format!(
                "src/{path} is not classified: list it in PRODUCER_FILES if it holds producer code \
                 (items moved out of lib.rs), else in NON_PRODUCER_FILES"
            )),
            Some(&"NON_PRODUCER_FILES") if in_producer_tree(path) => problems.push(format!(
                "src/{path} is in the producer tree but listed in NON_PRODUCER_FILES: every scan \
                 would skip it. List it in {}.",
                if in_producer_test_tree(path) { "PRODUCER_TEST_FILES" } else { "PRODUCER_FILES" },
            )),
            Some(&"PRODUCER_FILES") if in_producer_test_tree(path) => problems.push(format!(
                "src/{path} is a producer TEST file but listed in PRODUCER_FILES: its test source \
                 would read as production. List it in PRODUCER_TEST_FILES."
            )),
            Some(&"PRODUCER_TEST_FILES") if !in_producer_test_tree(path) => problems.push(format!(
                "src/{path} is listed in PRODUCER_TEST_FILES but is not under producer_tests/: that \
                 list is read as test source, so producer code in it would leave every scan bounded \
                 at the production section. A producer module is a PRODUCER_FILES row; an \
                 out-of-line producer test file lives under producer_tests/."
            )),
            Some(_) => {}
        }
    }
    for (path, class) in &listed {
        if !on_disk.contains(path) {
            problems.push(format!("{class} names src/{path}, which does not exist"));
        }
    }
    problems
}

/// One `impl … LowerCx` block in a file: the line its `impl` sits on and its members (`fn`,
/// `const`, `type` names at the block's own depth), in source order.
#[derive(Debug, PartialEq, Eq)]
struct LowerCxImpl {
    line: usize,
    members: Vec<String>,
}

/// Every `impl` block in `src` whose header (from `impl` to its `{`) names `LowerCx` — inherent or
/// trait, however the path and generics are spelled. `impl` counts only in item position (first
/// in the file, or after `}`, `;`, `{`, an attribute's `]`, `unsafe` or `default`), so an
/// `impl Trait` type (`-> impl Fn(&LowerCx)`, `f: impl Fn()`) is not a block. Comments and
/// strings are not code (the by-path guard's lexer).
fn lowercx_impls(src: &str) -> Vec<LowerCxImpl> {
    let t = tokens(src);
    let mut out = Vec::new();
    for k in 0..t.len() {
        if t[k].0 != Tok::Ident("impl") {
            continue;
        }
        let item_position = k == 0
            || matches!(
                t[k - 1].0,
                Tok::Punct(b'}' | b';' | b'{' | b']') | Tok::Ident("unsafe" | "default")
            );
        if !item_position {
            continue;
        }
        let Some(open) = (k + 1..t.len()).find(|&j| matches!(t[j].0, Tok::Punct(b'{' | b';')))
        else {
            continue;
        };
        if t[open].0 != Tok::Punct(b'{')
            || !t[k + 1..open].iter().any(|(tok, _)| *tok == Tok::Ident("LowerCx"))
        {
            continue;
        }
        let mut members = Vec::new();
        let mut depth = 0usize;
        for j in open..t.len() {
            match t[j].0 {
                Tok::Punct(b'{') => depth += 1,
                Tok::Punct(b'}') => {
                    depth -= 1;
                    if depth == 0 {
                        break;
                    }
                }
                Tok::Ident(kw @ ("fn" | "const" | "type")) if depth == 1 => {
                    if let Some(&(Tok::Ident(name), _)) = t.get(j + 1) {
                        // `const fn`/`const unsafe fn`: the `fn` that follows names the member.
                        let qualifier = matches!(name, "fn" | "unsafe" | "async" | "extern");
                        if !(kw == "const" && qualifier) {
                            members.push(name.to_string());
                        }
                    }
                }
                _ => {}
            }
        }
        out.push(LowerCxImpl { line: t[k].1, members });
    }
    out
}

/// The verdict on every `impl … LowerCx` block outside [`PRODUCER_FILES`]: `files` is each such
/// file as (path under `src/`, text). One line per problem; empty is a pass.
fn lowercx_problems(files: &[(&str, &str)], legacy: &[(&str, &[&str])]) -> Vec<String> {
    let mut problems = Vec::new();
    for &(path, src) in files {
        let impls = lowercx_impls(src);
        let found: Vec<&str> =
            impls.iter().flat_map(|i| i.members.iter().map(String::as_str)).collect();
        match legacy.iter().find(|row| row.0 == path) {
            None => {
                for i in &impls {
                    problems.push(format!(
                        "src/{path}:{} holds an `impl … LowerCx` block ({}), and src/{path} is not \
                         a PRODUCER_FILES file: every producer scan would skip that code. Put it in \
                         a PRODUCER_FILES file, or list src/{path} there.",
                        i.line,
                        if i.members.is_empty() { "no members".to_string() } else { i.members.join(", ") },
                    ));
                }
            }
            Some(&(_, pinned)) => {
                for &m in &found {
                    if !pinned.contains(&m) {
                        problems.push(format!(
                            "NEW `LowerCx` member `{m}` in src/{path}, a legacy extension file no \
                             producer scan reads: put it in a PRODUCER_FILES file."
                        ));
                    }
                }
                for &m in pinned.iter().filter(|&&m| !found.contains(&m)) {
                    problems.push(format!(
                        "STALE: `{m}` is pinned in LEGACY_LOWERCX_EXTENSIONS for src/{path} but is \
                         not a `LowerCx` member there. Delete it from the row — the list only shrinks."
                    ));
                }
            }
        }
    }
    for &(path, _) in legacy {
        if !files.iter().any(|&(p, _)| p == path) {
            problems.push(format!(
                "STALE: LEGACY_LOWERCX_EXTENSIONS names src/{path}, which is not a file outside \
                 PRODUCER_FILES. Delete its row."
            ));
        }
    }
    problems
}

/// `to_mir.rs`, for the producer's tests that pin a property of the shim.
pub(crate) const TO_MIR_SOURCE: &str = include_str!("to_mir.rs");
/// `crate_module.rs`, for the producer's tests that pin a property of the finalizer.
pub(crate) const CRATE_MODULE_SOURCE: &str = include_str!("crate_module.rs");

/// The pinned trust-ir conformance corpus
/// (`first-party/trust-ir/crates/trust-ir-conformance/tests/fixtures`), whose `.tmbc`
/// byte-goldens are the positive fixture set of `crate_module.rs`'s F-099 text-companion
/// guard tests (WS5.23). It names no source file, but it is reached from
/// `env!("CARGO_MANIFEST_DIR")`, the one run-time root of this crate, which a test reads here
/// and nowhere else (`no_test_reads_a_source_file_by_path_outside_source_scan`).
pub(crate) fn trust_ir_conformance_fixture_dir() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../first-party/trust-ir/crates/trust-ir-conformance/tests/fixtures")
}

/// Every SIBLING file (not a producer file) a test in `lib.rs` reads, as (path under `src/`,
/// contents). The split moves `lib.rs`'s test modules into other directories, where a
/// file-relative `include_str!` would re-resolve, so those tests read a sibling here, by name,
/// through [`sibling_source`]. `every_source_file_of_this_crate_is_classified` holds each row's
/// text to its path.
pub(crate) const SIBLING_FILES: &[(&str, &str)] = &[
    ("crate_module.rs", CRATE_MODULE_SOURCE),
    ("differential.rs", include_str!("differential.rs")),
    ("drop_oracle.rs", include_str!("drop_oracle.rs")),
    ("drops.rs", include_str!("drops.rs")),
    ("effect_conservation.rs", include_str!("effect_conservation.rs")),
    ("instance_admission.rs", include_str!("instance_admission.rs")),
    ("source_provenance.rs", include_str!("source_provenance.rs")),
    ("source_static_readback.rs", include_str!("source_static_readback.rs")),
    ("template_lowering.rs", include_str!("template_lowering.rs")),
    // Test 18 (INC6.5-NO-AUTHORITY) reads the oracle's public signatures.
    ("template_metadata/oracle.rs", include_str!("template_metadata/oracle.rs")),
    ("to_mir.rs", TO_MIR_SOURCE),
];

/// Trust (step 2 increment 6, step 6.5.1): every `.rs` file of `compiler/rustc_codegen_trust_cg/src`,
/// recursively, as (path relative to that directory, contents), sorted by path — for the
/// no-authority scan (`no_codegen_or_admission_path_reads_a_template`), which must see a file the
/// codegen crate adds tomorrow, so it walks the directory rather than naming files. A missing
/// directory or an unreadable file panics: a scan that reads nothing must not pass.
pub(crate) fn codegen_trust_cg_sources() -> Vec<(String, String)> {
    fn walk(root: &std::path::Path, dir: &std::path::Path, out: &mut Vec<(String, String)>) {
        let entries = std::fs::read_dir(dir)
            .unwrap_or_else(|e| panic!("cannot read {}: {e}", dir.display()));
        for entry in entries {
            let path = entry.expect("a directory entry").path();
            if path.is_dir() {
                walk(root, &path, out);
            } else if path.extension().is_some_and(|x| x == "rs") {
                let text = std::fs::read_to_string(&path)
                    .unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()));
                let rel = path.strip_prefix(root).unwrap_or(&path).display().to_string();
                out.push((rel, text));
            }
        }
    }
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../compiler/rustc_codegen_trust_cg/src");
    let mut out = Vec::new();
    walk(&root, &root, &mut out);
    out.sort();
    out
}

/// The text of the sibling file `path` (under `src/`): a [`SIBLING_FILES`] row, or a panic that
/// says to add one.
pub(crate) fn sibling_source(path: &str) -> &'static str {
    SIBLING_FILES
        .iter()
        .find(|(p, _)| *p == path)
        .map(|(_, text)| *text)
        .unwrap_or_else(|| panic!("src/{path} is not a SIBLING_FILES row: add it there"))
}

static PRODUCER_TEXT: LazyLock<String> =
    LazyLock::new(|| join_producer_files(PRODUCER_FILES, PRODUCER_TEST_FILES));

/// The producer as ONE text — see the module doc. Every scan of the producer reads this.
pub(crate) fn producer_text() -> &'static str {
    PRODUCER_TEXT.as_str()
}

/// All production sections (in list order), then all test sections, with a boundary between
/// two consecutive sections that come from different files. One file joins to itself.
fn join_producer_files(files: &[(&str, &str)], test_files: &[(&str, &str)]) -> String {
    let mut production = Vec::new();
    let mut tests = Vec::new();
    for &(path, src) in files {
        let end = production_end(src).unwrap_or(src.len());
        production.push((path, &src[..end]));
        tests.push((path, &src[end..]));
    }
    tests.extend(test_files.iter().copied());
    let mut out = String::new();
    let mut previous: Option<&str> = None;
    for (path, section) in production.into_iter().chain(tests) {
        if section.is_empty() {
            continue;
        }
        if previous.is_some_and(|p| p != path) {
            out.push_str(FILE_BOUNDARY);
        }
        out.push_str(section);
        previous = Some(path);
    }
    out
}

/// The bounds a scan draws from an anchor, each stopping at the file boundary. On a text with
/// no boundary in range every method answers exactly what the plain `str` spelling it replaces
/// answers (named in each doc), which is what keeps a scan's bytes unchanged while the
/// producer is one file.
pub(crate) trait ScanExt {
    /// Bytes from the start of `self` to the first file boundary — the rest of the file `self`
    /// starts in. (`self.len()` with no boundary.)
    fn file_len(&self) -> usize;
    /// `self.find(needle)`, but `None` when the needle is only found past a file boundary.
    fn find_in_file(&self, needle: &str) -> Option<usize>;
    /// Where the method after the one `self` starts in begins: the next 4-space-indented `fn`,
    /// `pub fn` or `pub(crate) fn` head in this file (as `self.find("\n    fn ")` answered while
    /// every method was private), else the end of this file.
    fn method_end(&self) -> usize;
    /// `&self[at.saturating_sub(max_len)..at]`, never reaching back past the start of `at`'s file.
    fn window_before(&self, at: usize, max_len: usize) -> &str;
    /// `&self[at..(at + max_len).min(self.len())]`, never reaching past the end of `at`'s file.
    fn window_after(&self, at: usize, max_len: usize) -> &str;
    /// `a < b`, and both offsets in the same file: source order means nothing across files.
    fn precedes_in_file(&self, a: usize, b: usize) -> bool;
}

impl ScanExt for str {
    fn file_len(&self) -> usize {
        self.find(FILE_BOUNDARY_TOKEN).unwrap_or(self.len())
    }

    fn find_in_file(&self, needle: &str) -> Option<usize> {
        self[..self.file_len()].find(needle)
    }

    fn method_end(&self) -> usize {
        let file = &self[..self.file_len()];
        ["\n    fn ", "\n    pub fn ", "\n    pub(crate) fn "]
            .into_iter()
            .filter_map(|head| file.find(head))
            .min()
            .unwrap_or(file.len())
    }

    fn window_before(&self, at: usize, max_len: usize) -> &str {
        let file_start =
            self[..at].rfind(FILE_BOUNDARY_TOKEN).map_or(0, |b| b + FILE_BOUNDARY_TOKEN.len());
        &self[at.saturating_sub(max_len).max(file_start)..at]
    }

    fn window_after(&self, at: usize, max_len: usize) -> &str {
        let end = (at + max_len).min(self.len()).min(at + self[at..].file_len());
        &self[at..end]
    }

    fn precedes_in_file(&self, a: usize, b: usize) -> bool {
        a < b && !self[a..b].contains(FILE_BOUNDARY_TOKEN)
    }
}

/// The by-path source reads that predate the by-path guard, outside this module, as
/// (file under `src/`, read, exact count). NONE reads the producer. Every one is a file
/// scanning ITSELF, a sibling that is not being split, a compiler source, or the `OUT_DIR`
/// copy of a frozen file that a refinement test compares with its pin; several sit in
/// blob-pinned oracle files that cannot change. A NEW read goes through this module
/// ([`producer_text`], or a [`SIBLING_FILES`] row); this list may only shrink — delete a row,
/// or lower its count, in the commit that removes the read.
pub(crate) const GRANDFATHERED_READS: &[(&str, &str, usize)] = &[
    ("crate_module.rs", r#"include_str!("crate_module.rs")"#, 4),
    ("crate_module/seam_scratch_tests.rs", r#"include_str!("../crate_module.rs")"#, 1),
    ("crate_module/seam_scratch_tests.rs", r#"include_str!("../differential.rs")"#, 1),
    ("crate_module/seam_scratch_tests.rs", r#"include_str!("seam_reference.rs")"#, 2),
    ("flip.rs", r#"include_str!("flip.rs")"#, 4),
    ("flip_refinement_tests.rs", r#"include_str!("OUT_DIR" "/flip_current.rs")"#, 1),
    ("flip_refinement_tests.rs", r#"include_str!("OUT_DIR" "/flip_pinned.rs")"#, 1),
    ("flip_refinement_tests.rs", r#"include_str!("OUT_DIR" "/instance_flip_current.rs")"#, 1),
    ("flip_refinement_tests.rs", r#"include_str!("OUT_DIR" "/instance_flip_pinned.rs")"#, 1),
    (
        "flip_registry_refinement_tests.rs",
        r#"include_str!("../../../compiler/rustc_middle/src/hir/map.rs")"#,
        1,
    ),
    (
        "flip_registry_refinement_tests.rs",
        r#"include_str!("../../../compiler/rustc_mir_transform/src/lib.rs")"#,
        1,
    ),
    (
        "flip_registry_refinement_tests.rs",
        r#"include_str!("../../../compiler/rustc_mir_transform/src/pass_manager.rs")"#,
        1,
    ),
    (
        "flip_registry_refinement_tests.rs",
        r#"include_str!("../../../compiler/rustc_mir_transform/src/remove_storage_markers.rs")"#,
        1,
    ),
    (
        "flip_registry_refinement_tests.rs",
        r#"include_str!("../../../compiler/rustc_mir_transform/src/trust_ir_flip.rs")"#,
        1,
    ),
    (
        "flip_registry_refinement_tests.rs",
        r#"include_str!("OUT_DIR" "/flip_registry_current.rs")"#,
        1,
    ),
    (
        "flip_registry_refinement_tests.rs",
        r#"include_str!("OUT_DIR" "/flip_registry_pinned.rs")"#,
        1,
    ),
    ("flip_registry_refinement_tests.rs", r#"include_str!("flip_registry.rs")"#, 1),
    ("frozen_section_cut.rs", r#"include_str!("flip_registry.rs")"#, 1),
    ("frozen_section_cut.rs", r#"include_str!("mir_differential.rs")"#, 1),
    ("instance_flip.rs", r#"include_str!("instance_flip.rs")"#, 1),
    ("instance_flip.rs", r#"include_str!("to_mir.rs")"#, 1),
    (
        "mir_differential_refinement_tests.rs",
        r#"include_str!("OUT_DIR" "/mir_differential_current.rs")"#,
        1,
    ),
    (
        "mir_differential_refinement_tests.rs",
        r#"include_str!("OUT_DIR" "/mir_differential_pinned.rs")"#,
        1,
    ),
    ("remap_certificate.rs", r#"include_str!("crate_module.rs")"#, 1),
    ("to_mir.rs", r#"env!("CARGO_MANIFEST_DIR")"#, 1),
    ("to_mir.rs", r#"include_str!("to_mir.rs")"#, 24),
];

/// One token of Rust source as the by-path guard sees it. Comments are dropped; a string
/// literal keeps its raw contents (escapes are not decoded: the guard only asks whether a
/// literal names a source path); numbers and lifetimes are dropped.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Tok<'a> {
    Ident(&'a str),
    Str(&'a str),
    Punct(u8),
}

fn is_ident_byte(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_' || b >= 0x80
}

/// Tokens of `src`, each with its 1-based line. A lexer only as precise as the guard needs:
/// line and nested block comments, plain/raw/byte/C strings, char literals vs lifetimes, and
/// raw identifiers are told apart, because each has hidden a needle from a cruder scan.
fn tokens(src: &str) -> Vec<(Tok<'_>, usize)> {
    let b = src.as_bytes();
    let mut out = Vec::new();
    let (mut i, mut line) = (0usize, 1usize);
    let lines_in = |from: usize, to: usize| b[from..to].iter().filter(|&&c| c == b'\n').count();
    while i < b.len() {
        let c = b[i];
        if c == b'\n' {
            line += 1;
            i += 1;
        } else if c.is_ascii_whitespace() {
            i += 1;
        } else if b[i..].starts_with(b"//") {
            i = src[i..].find('\n').map_or(b.len(), |n| i + n);
        } else if b[i..].starts_with(b"/*") {
            let (mut depth, start) = (1usize, i);
            i += 2;
            while i < b.len() && depth > 0 {
                if b[i..].starts_with(b"/*") {
                    depth += 1;
                    i += 2;
                } else if b[i..].starts_with(b"*/") {
                    depth -= 1;
                    i += 2;
                } else {
                    i += 1;
                }
            }
            line += lines_in(start, i);
        } else if let Some((content, next)) = string_literal(src, i) {
            out.push((Tok::Str(content), line));
            line += lines_in(i, next);
            i = next;
        } else if c == b'\'' || (c == b'b' && b.get(i + 1) == Some(&b'\'')) {
            let q = if c == b'b' { i + 1 } else { i };
            i = char_or_lifetime_end(src, q);
        } else if c == b'r'
            && b.get(i + 1) == Some(&b'#')
            && b.get(i + 2).is_some_and(|&n| is_ident_byte(n))
        {
            // A raw identifier, `r#type`.
            let start = i + 2;
            i = start;
            while i < b.len() && is_ident_byte(b[i]) {
                i += 1;
            }
            out.push((Tok::Ident(&src[start..i]), line));
        } else if is_ident_byte(c) {
            let start = i;
            while i < b.len() && is_ident_byte(b[i]) {
                i += 1;
            }
            if !c.is_ascii_digit() {
                out.push((Tok::Ident(&src[start..i]), line));
            }
        } else {
            out.push((Tok::Punct(c), line));
            i += 1;
        }
    }
    out
}

/// If a string literal (`"…"`, `r#"…"#`, `b"…"`, `br"…"`, `c"…"`, `cr"…"`) starts at `i`: its
/// contents and the offset just past it.
fn string_literal(src: &str, i: usize) -> Option<(&str, usize)> {
    let b = src.as_bytes();
    let mut j = i;
    if matches!(b[j], b'b' | b'c') {
        j += 1;
    }
    let raw = b.get(j) == Some(&b'r');
    if raw {
        j += 1;
    }
    let hashes = b[j..].iter().take_while(|&&h| h == b'#').count();
    if !raw && hashes > 0 {
        return None;
    }
    j += hashes;
    if b.get(j) != Some(&b'"') {
        return None;
    }
    let open = j + 1;
    if raw {
        let close = format!("\"{}", "#".repeat(hashes));
        let end = src[open..].find(&close).map_or(b.len(), |n| open + n);
        return Some((&src[open..end], (end + close.len()).min(b.len())));
    }
    let mut k = open;
    while k < b.len() && b[k] != b'"' {
        k += if b[k] == b'\\' { 2 } else { 1 };
    }
    let end = k.min(b.len());
    Some((&src[open..end], (end + 1).min(b.len())))
}

/// `q` is at a `'`: skip a char literal (`'a'`, `'\''`, `'\u{1F600}'`, `'"'`) or a lifetime
/// (`'tcx`), returning the offset just past it.
fn char_or_lifetime_end(src: &str, q: usize) -> usize {
    let b = src.as_bytes();
    if b.get(q + 1) == Some(&b'\\') {
        // An escape: skip the escaped character, then run to the closing quote.
        let from = (q + 3).min(b.len());
        return src[from..].find('\'').map_or(b.len(), |n| from + n + 1);
    }
    let Some(ch) = src[q + 1..].chars().next() else { return b.len() };
    let after = q + 1 + ch.len_utf8();
    if b.get(after) == Some(&b'\'') {
        return after + 1;
    }
    let mut k = q + 1;
    while k < b.len() && is_ident_byte(b[k]) {
        k += 1;
    }
    k.max(q + 1)
}

/// Is this string literal a path to a source file, or to the source directory itself?
fn names_a_source_path(literal: &str) -> bool {
    literal.ends_with(".rs")
        || literal == "src"
        || literal.starts_with("src/")
        || literal.contains("/src/")
}

/// The string literals inside the parenthesised group opening at `tokens[open]`, and the index
/// of its closing `)`.
fn group_literals<'a>(tokens: &[(Tok<'a>, usize)], open: usize) -> (Vec<&'a str>, usize) {
    let mut depth = 0usize;
    let mut lits = Vec::new();
    for (k, (t, _)) in tokens.iter().enumerate().skip(open) {
        match t {
            Tok::Punct(b'(' | b'[' | b'{') => depth += 1,
            Tok::Punct(b')' | b']' | b'}') => {
                depth -= 1;
                if depth == 0 {
                    return (lits, k);
                }
            }
            Tok::Str(s) => lits.push(*s),
            _ => {}
        }
    }
    (lits, tokens.len())
}

/// Every by-path read of a source file in `src`, as (line, the read). Three spellings reach a
/// source file by path, and each is recognised in CODE only (never in a comment or a string):
///
/// * `include_str!`/`include_bytes!` whose argument names a `.rs` file, in any of the three
///   delimiters a macro call takes (`(..)`, `[..]`, `{..}`; reported as `(..)`);
/// * `env!("CARGO_MANIFEST_DIR")` — the only root a run-time read can find this crate from;
/// * a file-system or path call (`read_to_string`, `read`, `read_dir`, `open`, `join`,
///   `Path::new`, `PathBuf::from`) handed a literal naming a source path.
///
/// Not seen: a path held in a variable before it is read (a plain literal bound first, or one
/// spelled through `format!`/`concat!`) and read without any of the above, a `macro_rules!`
/// that wraps `include_str!($x)`, or a read through a helper outside this crate. Code inclusion
/// (`include!`, `#[path]`) is not a text read and is not reported.
fn by_path_reads(src: &str) -> Vec<(usize, String)> {
    let t = tokens(src);
    let mut out = Vec::new();
    let quoted =
        |lits: &[&str]| lits.iter().map(|l| format!("{l:?}")).collect::<Vec<_>>().join(" ");
    for k in 0..t.len() {
        let (tok, line) = t[k];
        let next = |d: usize| t.get(k + d).map(|p| p.0);
        match tok {
            Tok::Ident(m @ ("include_str" | "include_bytes"))
                if next(1) == Some(Tok::Punct(b'!'))
                    && matches!(next(2), Some(Tok::Punct(b'(' | b'[' | b'{'))) =>
            {
                let (lits, _) = group_literals(&t, k + 2);
                if lits.iter().any(|l| l.ends_with(".rs")) {
                    out.push((line, format!("{m}!({})", quoted(&lits))));
                }
            }
            Tok::Str("CARGO_MANIFEST_DIR") => {
                out.push((line, format!("env!({:?})", "CARGO_MANIFEST_DIR")))
            }
            Tok::Ident(f @ ("read_to_string" | "read" | "read_dir" | "open" | "join"))
                if next(1) == Some(Tok::Punct(b'(')) =>
            {
                // `join` extends a root some other spelling already found (`root.join("src")`
                // under `env!("CARGO_MANIFEST_DIR")`), so only a FILE it names is a new read.
                let (lits, _) = group_literals(&t, k + 1);
                for l in lits.into_iter().filter(|l| {
                    if f == "join" { l.ends_with(".rs") } else { names_a_source_path(l) }
                }) {
                    out.push((line, format!("{f}({l:?})")));
                }
            }
            Tok::Ident(ty @ ("Path" | "PathBuf"))
                if next(1) == Some(Tok::Punct(b':'))
                    && next(2) == Some(Tok::Punct(b':'))
                    && matches!(next(3), Some(Tok::Ident("new" | "from")))
                    && next(4) == Some(Tok::Punct(b'(')) =>
            {
                let (lits, _) = group_literals(&t, k + 4);
                for l in lits.into_iter().filter(|l| names_a_source_path(l)) {
                    out.push((line, format!("{ty}({l:?})")));
                }
            }
            _ => {}
        }
    }
    out
}

/// Where the guard and the census stand: every `(file, read)` of a by-path read outside this
/// module, with its count and the lines it sits on.
type ReadCensus = BTreeMap<(String, String), Vec<usize>>;

fn read_census<'a>(files: impl IntoIterator<Item = (&'a str, &'a str)>) -> ReadCensus {
    let mut census = ReadCensus::new();
    for (path, src) in files {
        if path == "source_scan.rs" {
            continue;
        }
        for (line, read) in by_path_reads(src) {
            census.entry((path.to_string(), read)).or_default().push(line);
        }
    }
    census
}

/// The guard's verdict: one line per `(file, read)` whose count differs from
/// [`GRANDFATHERED_READS`]. Empty is a pass.
fn guard_verdict(census: &ReadCensus, grandfathered: &[(&str, &str, usize)]) -> Vec<String> {
    let mut allowed: BTreeMap<(String, String), usize> = BTreeMap::new();
    for &(file, read, n) in grandfathered {
        *allowed.entry((file.to_string(), read.to_string())).or_default() += n;
    }
    let mut problems = Vec::new();
    for (key, lines) in census {
        let want = allowed.get(key).copied().unwrap_or(0);
        if lines.len() > want {
            problems.push(format!(
                "NEW by-path source read in src/{}: `{}` x{} (lines {lines:?}; {want} \
                 grandfathered). Read the producer through `crate::source_scan::producer_text()`, \
                 a sibling through `crate::source_scan::sibling_source` — never by path, or the \
                 scan goes blind the day its file moves.",
                key.0,
                key.1,
                lines.len(),
            ));
        }
    }
    for (key, want) in &allowed {
        let have = census.get(key).map_or(0, Vec::len);
        if have < *want {
            problems.push(format!(
                "STALE grandfathered read src/{}: `{}` x{want} listed, x{have} found. Lower or delete \
                 its `GRANDFATHERED_READS` row — the list only shrinks.",
                key.0, key.1,
            ));
        }
    }
    problems
}

/// This crate's `src/` directory: the root of [`crate_sources`].
#[cfg(test)]
fn src_dir() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src")
}

/// Every `.rs` file under `src/`, as a path relative to it with `/` separators, and its text.
///
/// Trust (step 2 increment 4d, sub-step 4d.0a): `pub(crate)` for a scan that must see EVERY
/// file of the crate — `instance_probe.rs`'s `shim_route_tests` counts the callers of private
/// and `pub(crate)` producer entries, which any module of the crate can name — so that the one
/// whole-crate walk stays here, where a by-path read belongs, and nowhere else.
#[cfg(test)]
pub(crate) fn crate_sources() -> Vec<(String, String)> {
    fn walk(dir: &std::path::Path, root: &std::path::Path, out: &mut Vec<(String, String)>) {
        let entries = std::fs::read_dir(dir).unwrap_or_else(|e| panic!("read {}: {e}", dir.display()));
        for entry in entries {
            let path = entry.expect("dir entry").path();
            if path.is_dir() {
                walk(&path, root, out);
            } else if path.extension().is_some_and(|e| e == "rs") {
                let rel = path.strip_prefix(root).expect("under src").to_string_lossy().replace('\\', "/");
                let text = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {rel}: {e}"));
                out.push((rel, text));
            }
        }
    }
    let root = src_dir();
    let mut out = Vec::new();
    walk(&root, &root, &mut out);
    out.sort();
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cfg_test() -> String {
        format!("#[cfg({})]", "test")
    }

    #[test]
    fn an_out_of_line_declaration_does_not_end_production() {
        let attr = cfg_test();
        let src = format!("pub mod a;\n{attr}\nmod early_tests;\npub mod b;\nfn production() {{}}\n{attr}\nmod tests {{\n    fn t() {{}}\n}}\n");
        let end = production_end(&src).expect("an inline test module exists");
        let production = &src[..end];
        assert!(production.contains("mod early_tests;"), "the declaration is inside production: {production:?}");
        assert!(production.contains("fn production() {}"), "code after the declaration is still production: {production:?}");
        assert!(!production.contains("mod tests {"), "the inline module is not: {production:?}");
        assert!(src[end..].starts_with(&format!("\n{attr}\nmod tests {{")));
    }

    #[test]
    fn a_file_with_only_out_of_line_declarations_has_no_bound() {
        let attr = cfg_test();
        let src = format!("pub mod a;\n{attr}\nmod early_tests;\nfn production() {{}}\n");
        assert_eq!(production_end(&src), None);
    }

    #[test]
    fn lib_rs_production_reaches_past_the_module_list() {
        let lib = include_str!("lib.rs");
        let end = production_end(lib).expect("lib.rs has inline test modules");
        let production = &lib[..end];
        // The two declarations that shrank every scan to 292 lines on 2026-09-10 are INSIDE
        // production, and so is the module list they sit in.
        for decl in ["mod array_write_tests;", "mod slice_index_tests;", "pub mod to_mir;"] {
            assert!(production.contains(decl), "`{decl}` must be inside the production section");
        }
        assert!(production.lines().count() > 10_000, "production is the bulk of the file, not its module list");
        // And the bound is an inline module, so nothing after it is production.
        let attr = cfg_test();
        let tail = &lib[end..];
        assert!(tail.starts_with(&format!("\n{attr}\nmod ")), "the bound sits on an inline test module: {:?}", &tail[..tail.len().min(60)]);
        assert!(tail.lines().nth(2).is_some_and(|l| l.trim_end().ends_with('{')));
    }

    // ---- the producer as one text ------------------------------------------------------------

    /// Keep every original production byte and the full newly classified hooks
    /// before the first inline test module. No new source may hide in the tail.
    #[test]
    fn producer_text_contains_every_complete_production_section_before_tests() {
        assert_eq!(PRODUCER_FILES.len(), 22, "all current production files are pinned");
        let paths: Vec<_> = PRODUCER_FILES.iter().map(|(path, _)| *path).collect();
        assert_eq!(paths, [
            "lib.rs", "ordered_slice_match.rs", "shared_borrow.rs", "float_storage.rs",
            "primitive_storage.rs", "primitive_unit_transport.rs", "float_reference_binding.rs",
            "coroutine_borrow.rs", "drops/owned_shared.rs",
            "shared_receiver_freeze.rs", "indexed_field_assignment.rs", "calling_convention.rs",
            "join_provenance.rs",
            "raw_entry_field.rs",
            "raw_pointer_coercion.rs",
            "core_wrapping_add.rs",
            "template_lowering/callable.rs",
            "concrete_type_transport.rs",
            "instance_const.rs",
            "effect_conservation/thir_source/capture.rs",
            "source_word64.rs",
            "source_word64/record.rs",
        ]);
        assert!(PRODUCER_TEST_FILES.is_empty());
        let lib = include_str!("lib.rs");
        let lib_end = production_end(lib).expect("original inline test section");
        let ordered_slice = include_str!("ordered_slice_match.rs");
        assert_eq!(production_end(ordered_slice), None);
        let float_storage = include_str!("float_storage.rs");
        assert_eq!(production_end(float_storage), None);
        let primitive_storage = include_str!("primitive_storage.rs");
        assert_eq!(production_end(primitive_storage), None);
        let unit_transport = include_str!("primitive_unit_transport.rs");
        assert_eq!(production_end(unit_transport), None);
        let float_binding = include_str!("float_reference_binding.rs");
        assert_eq!(production_end(float_binding), None);
        let calling = include_str!("calling_convention.rs");
        let calling_end = production_end(calling).expect("calling convention inline tests");
        let coroutine = include_str!("coroutine_borrow.rs");
        assert_eq!(production_end(coroutine), None);
        let indexed = include_str!("indexed_field_assignment.rs");
        assert_eq!(production_end(indexed), None);
        let provenance = include_str!("join_provenance.rs");
        let provenance_end = production_end(provenance).expect("join provenance inline tests");
        let raw_entry = include_str!("raw_entry_field.rs");
        assert_eq!(production_end(raw_entry), None);
        let raw_coercion = include_str!("raw_pointer_coercion.rs");
        assert_eq!(production_end(raw_coercion), None);
        let wrapping_add = include_str!("core_wrapping_add.rs");
        assert_eq!(production_end(wrapping_add), None);
        let callable = include_str!("template_lowering/callable.rs");
        assert_eq!(production_end(callable), None);
        let concrete_types = include_str!("concrete_type_transport.rs");
        assert_eq!(production_end(concrete_types), None);
        let instance_consts = include_str!("instance_const.rs");
        let instance_end = production_end(instance_consts).expect("instance const inline tests");
        let source_capture = include_str!("effect_conservation/thir_source/capture.rs");
        assert_eq!(production_end(source_capture), None);
        let word64_source = include_str!("source_word64.rs");
        let word64_record = include_str!("source_word64/record.rs");
        assert_eq!(production_end(word64_source), None);
        assert_eq!(production_end(word64_record), None);
        let joined = producer_text();
        let expected = format!(
            "{}{FILE_BOUNDARY}{ordered_slice}{FILE_BOUNDARY}{}{FILE_BOUNDARY}{float_storage}{FILE_BOUNDARY}{primitive_storage}{FILE_BOUNDARY}{unit_transport}{FILE_BOUNDARY}{float_binding}{FILE_BOUNDARY}{coroutine}{FILE_BOUNDARY}{}{FILE_BOUNDARY}{}{FILE_BOUNDARY}{indexed}{FILE_BOUNDARY}{}{FILE_BOUNDARY}{}{FILE_BOUNDARY}{raw_entry}{FILE_BOUNDARY}{raw_coercion}{FILE_BOUNDARY}{wrapping_add}{FILE_BOUNDARY}{callable}{FILE_BOUNDARY}{concrete_types}{FILE_BOUNDARY}{}{FILE_BOUNDARY}{source_capture}{FILE_BOUNDARY}{word64_source}{FILE_BOUNDARY}{word64_record}{FILE_BOUNDARY}{}{FILE_BOUNDARY}{}{FILE_BOUNDARY}{}{FILE_BOUNDARY}{}",
            &lib[..lib_end], include_str!("shared_borrow.rs"),
            include_str!("drops/owned_shared.rs"), include_str!("shared_receiver_freeze.rs"),
            &calling[..calling_end], &provenance[..provenance_end],
            &instance_consts[..instance_end], &lib[lib_end..],
            &calling[calling_end..], &provenance[provenance_end..], &instance_consts[instance_end..],
        );
        assert_eq!(joined, expected);
        assert_eq!(joined.matches(FILE_BOUNDARY_TOKEN).count(), 25);
        let end = production_end(joined).expect("joined inline test section");
        assert!(joined.starts_with(&lib[..lib_end]));
        assert!(joined.ends_with(&instance_consts[instance_end..]));
        assert_eq!(joined.matches(&instance_consts[instance_end..]).count(), 1);
        assert_eq!(joined.matches(&lib[lib_end..]).count(), 1);
        assert!(!joined[..end].contains("fn dead_transport_chain_is_not_a_use"));
        assert!(!joined[..end].contains("fn concrete_integer_values_keep_width_sign_and_upper_u128"));
        for (path, text) in PRODUCER_FILES {
            let production = &text[..production_end(text).unwrap_or(text.len())];
            assert!(!production.is_empty(), "nonvacuous production section: {path}");
            assert_eq!(joined[..end].matches(production).count(), 1, "complete {path} exactly once");
        }
        for hook in [
            "fn require_shared_snapshot_freeze",
            "fn coroutine_capture_borrow_index",
            "fn coroutine_capture_home",
            "fn prepare_coroutine_capture_homes",
            "fn try_lower_coroutine_capture_borrow",
            "fn owns_shared_drop_temporary",
            "fn record_owned_shared_temporary",
            "fn try_lower_owned_temp_field_borrow",
            "fn source_receiver_snapshot_is_freeze",
            "fn lower_indexed_local_field_assign(",
            "fn used_values(",
            "fn raw_entry_field_offset(",
            "fn lower_raw_entry_field_read(",
            "fn lower_mut_to_const_raw_pointer(",
            "fn of_definition(",
            "fn instance_const_value(",
            "fn scalar_value(",
        ] {
            assert!(joined[..end].contains(hook), "guard hook must remain visible: {hook}");
        }
    }

    /// Two files: production sections first, tests after, a boundary at every file edge and at
    /// no other place, and `production_end` of the whole still lands on the first test module.
    #[test]
    fn a_split_producer_joins_production_first_with_a_boundary_at_every_file_edge() {
        let attr = cfg_test();
        let lib = format!("fn a() {{}}\n\n{attr}\nmod lib_tests {{\n    fn t() {{}}\n}}\n");
        let moved = format!("impl X {{\n    fn b() {{}}\n}}\n\n{attr}\nmod b_tests {{\n    fn u() {{}}\n}}\n");
        let out_of_line = "fn v() {}\n";
        let joined = join_producer_files(&[("lib.rs", &lib), ("p/b.rs", &moved)], &[("p/b/t.rs", out_of_line)]);
        let parts: Vec<&str> = joined.split(FILE_BOUNDARY).collect();
        assert_eq!(parts.len(), 5, "five sections, four file edges: {joined:?}");
        assert_eq!(parts[0], "fn a() {}\n", "lib.rs production first");
        assert_eq!(parts[1], "impl X {\n    fn b() {}\n}\n", "then the moved file's production");
        assert_eq!(parts[2], &lib[lib.find("\n#[cfg").unwrap()..], "then lib.rs's tests");
        assert_eq!(parts[3], &moved[moved.find("\n#[cfg").unwrap()..], "then the moved file's tests");
        assert_eq!(parts[4], out_of_line, "then the out-of-line test files");
        let end = production_end(&joined).expect("the tests part starts at an inline test module");
        assert!(joined[..end].contains("fn b() {}"), "every file's production is production");
        assert!(!joined[..end].contains("fn t()") && !joined[..end].contains("fn u()"));
        assert!(joined[end..].contains("fn u()") && joined[end..].contains("fn v()"));
        // One file joins to itself.
        assert_eq!(join_producer_files(&[("lib.rs", &lib)], &[]), lib);
    }

    // ---- bounds stop at file edges -----------------------------------------------------------

    fn two_files() -> String {
        format!("impl A {{\n    fn a() {{ x; }}\n}}{FILE_BOUNDARY}impl B {{\n    fn b() {{ y; }}\n    pub(crate) fn c() {{}}\n}}")
    }

    #[test]
    fn every_bound_stops_at_the_file_edge() {
        let s = two_files();
        let a = s.find("fn a()").unwrap();
        let b = s.find("fn b()").unwrap();
        let edge = s.find(FILE_BOUNDARY_TOKEN).unwrap();
        // `find_in_file`: the plain `find` would reach `y;` in the next file.
        assert!(s[a..].find("y;").is_some());
        assert_eq!(s[a..].find_in_file("y;"), None);
        assert_eq!(s[a..].find_in_file("x;"), s[a..].find("x;"));
        // `method_end`: the plain `find` would run into file B's method.
        assert!(a + s[a..].find("\n    fn ").unwrap() > edge);
        assert!(a + s[a..].method_end() <= edge, "a's span ends at its own file's edge");
        // …and inside B it stops at the `pub(crate) fn` head a moved method will carry.
        assert_eq!(&s[b + s[b..].method_end()..], "\n    pub(crate) fn c() {}\n}");
        // windows
        assert!(!s.window_before(b, 1000).contains("fn a()"), "no reach back into file A");
        assert_eq!(s.window_before(b, 3), &s[b - 3..b]);
        assert!(!s.window_after(a, 1000).contains("fn b()"), "no reach into file B");
        assert_eq!(s.window_after(a, 4), &s[a..a + 4]);
        // order
        assert!(!s.precedes_in_file(a, b), "offsets in two files are not ordered");
        assert!(s.precedes_in_file(b, s.find("fn c()").unwrap()));
        assert!(!s.precedes_in_file(b, b));
        assert_eq!(s.file_len(), edge);
    }

    /// With no boundary in reach every bound is the plain spelling it replaced — the half of the
    /// no-op argument that holds per call.
    #[test]
    fn with_no_boundary_every_bound_is_the_plain_spelling() {
        let s = "impl A {\n    fn a() { x; }\n    fn b() { y; }\n}\n";
        let a = s.find("fn a()").unwrap();
        assert_eq!(s[a..].find_in_file("y;"), s[a..].find("y;"));
        assert_eq!(s[a..].method_end(), s[a..].find("\n    fn ").unwrap());
        assert_eq!(s.window_before(a, 5), &s[a.saturating_sub(5)..a]);
        assert_eq!(s.window_before(a, 500), &s[..a]);
        assert_eq!(s.window_after(a, 500), &s[a..]);
        assert!(s.precedes_in_file(0, a));
        assert_eq!(s.file_len(), s.len());
    }

    // ---- every file is classified ------------------------------------------------------------

    /// THE COMPLETENESS HALF. A producer item moved into a file nobody listed, or into a
    /// producer-tree file listed as NON_PRODUCER, would vanish from every scan; this is where that
    /// fails, naming the file.
    #[test]
    fn every_source_file_of_this_crate_is_classified() {
        let on_disk = crate_sources();
        assert!(on_disk.len() >= 40, "the walk found {} files under {} — a walk that finds nothing passes vacuously", on_disk.len(), src_dir().display());
        let paths: Vec<&str> = on_disk.iter().map(|(p, _)| p.as_str()).collect();
        let producer: Vec<&str> = PRODUCER_FILES.iter().map(|(p, _)| *p).collect();
        let producer_tests: Vec<&str> = PRODUCER_TEST_FILES.iter().map(|(p, _)| *p).collect();
        let problems = classification_problems(&paths, &producer, &producer_tests, NON_PRODUCER_FILES);
        assert!(problems.is_empty(), "{}", problems.join("\n"));
        // A row's path and its `include_str!` must name the same file — and so must each
        // sibling row's. A sibling is never a producer file: reading one by name would step
        // around `producer_text`.
        for (path, text) in PRODUCER_FILES.iter().chain(PRODUCER_TEST_FILES).chain(SIBLING_FILES) {
            let disk = &on_disk.iter().find(|(p, _)| p == path).expect("checked above").1;
            assert!(disk == text, "the source_scan row for src/{path} embeds a different file");
        }
        for (path, _) in SIBLING_FILES {
            assert!(
                NON_PRODUCER_FILES.contains(path),
                "SIBLING_FILES row src/{path} must be a NON_PRODUCER file"
            );
        }
        // Every file-edge bound cuts at the boundary token, so a producer file that spelled it
        // would cut its own scans short without a word. (Permanent: the identity test that
        // also checks it is deleted by the first move.)
        for (path, text) in PRODUCER_FILES.iter().chain(PRODUCER_TEST_FILES) {
            assert!(
                !text.contains(FILE_BOUNDARY_TOKEN),
                "src/{path} spells the file-boundary token; every bound in it would stop there"
            );
        }
        // Non-vacuity: the producer's production section is the bulk of the crate.
        let text = producer_text();
        let production = &text[..production_end(text).expect("the producer has an inline test module")];
        assert!(production.lines().count() > 50_000, "producer production is {} lines", production.lines().count());
    }

    /// NEGATIVE CONTROL for the classification: being listed is not enough. A producer-tree file
    /// listed as NON_PRODUCER — the misclassified `producer/scratch_move.rs` of the 2026-09-28
    /// review — fails by name, as do the other ways a file can leave the scan.
    #[test]
    fn a_producer_tree_file_listed_as_non_producer_fails_by_name() {
        let check = classification_problems;
        let disk = ["lib.rs", "producer.rs", "producer/scratch_move.rs", "producer_tests/x.rs", "tuple_layout.rs"];
        // The correct classification passes.
        let good = check(&disk, &["lib.rs", "producer.rs", "producer/scratch_move.rs"], &["producer_tests/x.rs"], &["tuple_layout.rs"]);
        assert!(good.is_empty(), "{good:?}");
        // Each mistake is ONE problem, naming the file.
        let mistakes: [(&[&str], &[&str], &[&str], &str, &str); 9] = [
            // the review's run G: the new module file listed, but as NON_PRODUCER
            (&["lib.rs", "producer.rs"], &["producer_tests/x.rs"], &["producer/scratch_move.rs", "tuple_layout.rs"], "src/producer/scratch_move.rs", "listed in NON_PRODUCER_FILES"),
            (&["lib.rs", "producer/scratch_move.rs"], &["producer_tests/x.rs"], &["producer.rs", "tuple_layout.rs"], "src/producer.rs", "listed in NON_PRODUCER_FILES"),
            (&["lib.rs", "producer.rs", "producer/scratch_move.rs"], &[], &["producer_tests/x.rs", "tuple_layout.rs"], "src/producer_tests/x.rs", "listed in NON_PRODUCER_FILES"),
            (&["lib.rs", "producer.rs", "producer/scratch_move.rs", "producer_tests/x.rs"], &[], &["tuple_layout.rs"], "src/producer_tests/x.rs", "listed in PRODUCER_FILES"),
            // producer code listed as test source: every production-bounded scan would skip it
            (&["lib.rs", "producer.rs"], &["producer/scratch_move.rs", "producer_tests/x.rs"], &["tuple_layout.rs"], "src/producer/scratch_move.rs", "listed in PRODUCER_TEST_FILES"),
            (&["lib.rs", "producer.rs", "producer/scratch_move.rs"], &["producer_tests/x.rs", "tuple_layout.rs"], &[], "src/tuple_layout.rs", "listed in PRODUCER_TEST_FILES"),
            (&["lib.rs", "producer.rs"], &["producer_tests/x.rs"], &["tuple_layout.rs"], "src/producer/scratch_move.rs", "not classified"),
            (&["lib.rs", "producer.rs", "producer/scratch_move.rs"], &["producer_tests/x.rs"], &["tuple_layout.rs", "producer.rs"], "src/producer.rs", "listed twice"),
            (&["lib.rs", "producer.rs", "producer/scratch_move.rs", "gone.rs"], &["producer_tests/x.rs"], &["tuple_layout.rs"], "src/gone.rs", "does not exist"),
        ];
        for (p, t, n, file, says) in mistakes {
            let got = check(&disk, p, t, n);
            assert!(got.len() == 1 && got[0].contains(file) && got[0].contains(says), "want one `{says}` problem naming {file}: {got:?}");
        }
    }

    /// Every `impl … LowerCx` block outside the producer files is one of the legacy extension
    /// files', with exactly its pinned members — so a `LowerCx` member moved into any other
    /// file, or into one of those (the review's run H: `emit_bind` into
    /// `const_index_bounds.rs`), fails naming the file and the member.
    #[test]
    fn lowercx_impls_live_in_producer_files() {
        let on_disk = crate_sources();
        let outside: Vec<(&str, &str)> = on_disk
            .iter()
            .filter(|(p, _)| !PRODUCER_FILES.iter().any(|(q, _)| q == p))
            .map(|(p, t)| (p.as_str(), t.as_str()))
            .collect();
        assert!(outside.len() >= 40, "{} files outside PRODUCER_FILES", outside.len());
        let problems = lowercx_problems(&outside, LEGACY_LOWERCX_EXTENSIONS);
        assert!(problems.is_empty(), "{}", problems.join("\n"));
        // Non-vacuity: the detector sees the producer's own `impl LowerCx` and its members, and
        // each legacy row's members in the order the file defines them.
        let members: Vec<String> = PRODUCER_FILES.iter().flat_map(|(_, t)| lowercx_impls(t)).flat_map(|i| i.members).collect();
        for m in ["push_node", "emit_bind", "lower_expr_walk", "lower_tuple_match", "lower_enum_match"] {
            assert!(members.iter().any(|x| x == m), "`{m}` must be a LowerCx member the detector finds in the producer");
        }
        // 309 on 2026-09-28, one of them (`try_lower_mut_call_temp_slot`) headed at column 0,
        // which a line-based count misses; a detector that loses most of them fails here.
        assert!(members.len() >= 300, "the detector found only {} LowerCx members in the producer", members.len());
        for (path, pinned) in LEGACY_LOWERCX_EXTENSIONS {
            let text = outside.iter().find(|(p, _)| p == path).expect("checked above").1;
            let found: Vec<String> = lowercx_impls(text).into_iter().flat_map(|i| i.members).collect();
            assert_eq!(found, pinned.to_vec(), "src/{path}: LowerCx members in source order");
        }
    }

    /// NEGATIVE CONTROL for the `LowerCx` check: every spelling of an `impl … LowerCx` block is
    /// seen, with its members at its own depth; an `impl Trait` type, prose and strings are not;
    /// the verdict fails a member moved into a legacy file, an impl in any other file, and a stale
    /// row.
    #[test]
    fn the_lowercx_check_catches_a_moved_member_and_ignores_impl_trait_types() {
        let block = "impl<'a, 'tcx> LowerCx<'a, 'tcx> {\n    /// doc: fn not_a_member\n    fn emit_bind(&mut self) -> bool {\n        fn nested() {}\n        let f: fn(u8) -> u8 = |x| x;\n        '{' == '}'\n    }\n    pub(crate) const K: u8 = 1;\n    type T = u8;\n    pub(crate) const fn cf(&self) {}\n}\nfn after() {}\n";
        assert_eq!(lowercx_impls(block), vec![LowerCxImpl { line: 1, members: ["emit_bind", "K", "T", "cf"].map(String::from).to_vec() }]);
        for src in [
            "impl LowerCx<'_, '_> { fn a() {} }",
            "impl crate::LowerCx<'_, '_> { fn a() {} }",
            "unsafe impl Send for LowerCx<'_, '_> {}",
            "#[cfg(test)]\nimpl Foo for super::LowerCx<'_, '_> { fn a() {} }",
            "use x;\nimpl<'a, 'tcx> LowerCx<'a, 'tcx> where 'tcx: 'a { fn a() {} }",
            "mod m { impl LowerCx<'_, '_> { fn a() {} } }",
        ] {
            assert_eq!(lowercx_impls(src).len(), 1, "in {src:?}");
        }
        for src in [
            "fn f(g: impl Fn(&LowerCx)) {}",
            "fn f() -> impl Iterator<Item = LowerCx> { todo!() }",
            "// impl LowerCx<'_, '_> { fn a() {} }",
            "/* impl LowerCx<'_, '_> { fn a() {} } */",
            "let s = \"impl LowerCx<'_, '_> { fn a() {} }\";",
            "impl Other { fn a(cx: &LowerCx) {} }",
            "impl LowerCxLike { fn a() {} }",
            "impl Trait for Other;",
        ] {
            assert_eq!(lowercx_impls(src), Vec::new(), "in {src:?}");
        }
        // The verdict. The legacy row as it stands passes.
        let legacy_src = "impl<'a, 'tcx> LowerCx<'a, 'tcx> {\n    pub(crate) fn kept(&self) {}\n}\n";
        let rows: [(&str, &[&str]); 1] = [("legacy.rs", &["kept"])];
        assert!(lowercx_problems(&[("legacy.rs", legacy_src), ("other.rs", "fn f() {}")], &rows).is_empty());
        // Run H: a member moved INTO a legacy file.
        let moved_in = "impl<'a, 'tcx> LowerCx<'a, 'tcx> {\n    pub(crate) fn kept(&self) {}\n    fn emit_bind(&mut self) { self.cur.push(x); }\n}\n";
        let got = lowercx_problems(&[("legacy.rs", moved_in)], &rows);
        assert!(got.len() == 1 && got[0].starts_with("NEW") && got[0].contains("`emit_bind`") && got[0].contains("src/legacy.rs"), "{got:?}");
        // Run G's file, moved outside the producer tree: an impl in any other file fails by line.
        let elsewhere = format!("//! moved\nuse crate::*;\n\n{moved_in}");
        let got = lowercx_problems(&[("legacy.rs", legacy_src), ("scratch_move.rs", &elsewhere)], &rows);
        assert!(got.len() == 1 && got[0].contains("src/scratch_move.rs:4") && got[0].contains("kept, emit_bind"), "{got:?}");
        // A member moved OUT of a legacy file, and a legacy file that is gone: stale rows.
        let got = lowercx_problems(&[("legacy.rs", "impl LowerCx<'_, '_> {}")], &rows);
        assert!(got.len() == 1 && got[0].starts_with("STALE") && got[0].contains("`kept`"), "{got:?}");
        let got = lowercx_problems(&[("other.rs", "fn f() {}")], &rows);
        assert!(got.len() == 1 && got[0].starts_with("STALE") && got[0].contains("src/legacy.rs"), "{got:?}");
    }

    // ---- no by-path read outside this module -------------------------------------------------

    /// THE GUARD. A new test that reads a source file by path outside this module fails here —
    /// the next split would blind it the way `include_str!("lib.rs")` would have blinded the
    /// producer's scans.
    #[test]
    fn no_test_reads_a_source_file_by_path_outside_source_scan() {
        let sources = crate_sources();
        let census = read_census(sources.iter().map(|(p, t)| (p.as_str(), t.as_str())));
        let problems = guard_verdict(&census, GRANDFATHERED_READS);
        assert!(problems.is_empty(), "{}", problems.join("\n"));
        // Non-vacuity: the detector sees the reads this crate really has, and none of them reads
        // the producer.
        assert_eq!(census.values().map(Vec::len).sum::<usize>(), GRANDFATHERED_READS.iter().map(|r| r.2).sum::<usize>());
        for (path, _) in PRODUCER_FILES.iter().chain(PRODUCER_TEST_FILES) {
            let name = path.rsplit('/').next().unwrap_or(path);
            assert!(
                census.keys().all(|(_, read)| !read.contains(&format!("{name:?}"))),
                "a grandfathered read names producer file {path}",
            );
        }
    }

    /// NEGATIVE CONTROL for the guard: each by-path spelling is caught, prose and strings and
    /// code inclusion are not, and the verdict fails both a new read and a stale row.
    #[test]
    fn the_by_path_guard_catches_every_spelling_and_ignores_prose() {
        let manifest = "CARGO_MANIFEST_DIR";
        for (src, want) in [
            (r#"let p = include_str!("lib.rs");"#.to_string(), r#"include_str!("lib.rs")"#.to_string()),
            (r#"let p = include_bytes!("producer/x.rs");"#.to_string(), r#"include_bytes!("producer/x.rs")"#.to_string()),
            (format!(r#"let r = PathBuf::from(env!("{manifest}")).join("src");"#), format!(r#"env!("{manifest}")"#)),
            (r#"let t = std::fs::read_to_string("src/lib.rs").unwrap();"#.to_string(), r#"read_to_string("src/lib.rs")"#.to_string()),
            (r#"let t = root.join("lib.rs");"#.to_string(), r#"join("lib.rs")"#.to_string()),
            (r#"let t = Path::new("crates/trust-thir-lower/src/lib.rs");"#.to_string(), r#"Path("crates/trust-thir-lower/src/lib.rs")"#.to_string()),
            (r#"let s = r"x"; let p = include_str!("to_mir.rs");"#.to_string(), r#"include_str!("to_mir.rs")"#.to_string()),
            (r#"let c = '"'; let p = include_str!("lib.rs"); // "#.to_string(), r#"include_str!("lib.rs")"#.to_string()),
            (r#"fn f<'a>(x: &'a str) { include_str!("lib.rs"); }"#.to_string(), r#"include_str!("lib.rs")"#.to_string()),
            // The other two delimiters a macro call takes, and a path-qualified call.
            (r#"let p = include_str!["lib.rs"];"#.to_string(), r#"include_str!("lib.rs")"#.to_string()),
            (r#"let p = include_bytes!{"producer/x.rs"};"#.to_string(), r#"include_bytes!("producer/x.rs")"#.to_string()),
            (r#"let p = ::core::include_str!["to_mir.rs"];"#.to_string(), r#"include_str!("to_mir.rs")"#.to_string()),
        ] {
            let got: Vec<String> = by_path_reads(&src).into_iter().map(|(_, r)| r).collect();
            assert_eq!(got, vec![want], "in {src:?}");
        }
        for src in [
            r#"// let p = include_str!("lib.rs");"#,
            r#"/* include_str!("lib.rs") /* nested */ include_str!("x.rs") */"#,
            r#"let msg = "read it as include_str!(\"lib.rs\")";"#,
            r##"let raw = r#"include_str!("lib.rs")"#;"##,
            r#"let t = crate::source_scan::producer_text();"#,
            r#"#[path = "array_write_tests/temporary_support.rs"] mod support;"#,
            r#"include!(concat!(env!("OUT_DIR"), "/pinned.rs"));"#,
            r#"let m = include_str!("../../../scripts/frozen-files.txt");"#,
            r#"module.files.push("src/arith.rs".to_string());"#,
            r#"let c = '\''; let l: &'static str = "x";"#,
        ] {
            assert_eq!(by_path_reads(src), Vec::new(), "in {src:?}");
        }
        // The verdict: a grandfathered read passes, one more is NEW, one fewer is STALE.
        let one = r#"let a = include_str!("flip.rs");"#;
        let two = format!("{one}\n{one}");
        let rows = [("flip.rs", r#"include_str!("flip.rs")"#, 1)];
        assert!(guard_verdict(&read_census([("flip.rs", one)]), &rows).is_empty());
        let new = guard_verdict(&read_census([("flip.rs", two.as_str())]), &rows);
        assert!(new.len() == 1 && new[0].starts_with("NEW"), "{new:?}");
        let stale = guard_verdict(&read_census([("flip.rs", "fn f() {}")]), &rows);
        assert!(stale.len() == 1 && stale[0].starts_with("STALE"), "{stale:?}");
        // A new read of the producer in some other test file — the case this guard exists for.
        let elsewhere = guard_verdict(&read_census([("lineage.rs", r#"let p = include_str!("lib.rs");"#)]), &rows);
        assert!(elsewhere.iter().any(|p| p.starts_with("NEW") && p.contains("src/lineage.rs")), "{elsewhere:?}");
        // …and this module is the one place allowed to read by path.
        assert!(read_census([("source_scan.rs", r#"include_str!("lib.rs")"#)]).is_empty());
    }
}
