//! The EFFECT-CONSERVATION GATE (`trust_thir_lower::effect_conservation`, 2026-10-01) and the
//! D28 abstraction tags, read back from the two places a consumer outside the compiler sees
//! them: the `<crate>.effect-conservation.json` sidecar beside a `-Ztrust-dump=ir` dump, and
//! probe channel C.
//!
//! Until this change nothing compared a spliced body's effects with the program's. The wave-ER
//! `for` summary, the field-store right-hand-side lanes and drop elision each shipped a lowered,
//! spliced, strict-clean, codegen-licensed body with an effect missing; three value-abstraction
//! lanes (an opaque `()` store, a discriminant-only `Option`, an `undef` whole-value store) stored
//! less than the program does, untagged. The dump said nothing about any of it.
//!
//! Pins:
//!  * every listed function of `effects.rs` has the verdict and the EXACT tag set below in the
//!    sidecar (a shape the producer one day lowers faithfully must move from `refused` to
//!    `conserved` here, deliberately) — including the shapes of the first gate's 2026-10-01
//!    review: a collapsed enum inside a tuple, a destructor-free elided drop (`drop`, no
//!    `destructor`), a write through a caller's `Box`, and a user `eq` after an exempt `str` one;
//!  * the sidecar is bound to the text dump it describes (byte count + FNV-1a 64);
//!  * THE MUTATION: with `-Ztrust-ir-lower-mutate-rhs-effects` (the field-store RHS lane put
//!    back as it was before ec8b51bb3b), the gate names the call the lane dropped —
//!    `not-conserved(call)` — and the panic check — `not-conserved(assert)` — on top of the
//!    abstraction tags;
//!  * channel C reads the same verdicts: `ok` for conserved bodies only, `abstracted(..)` for
//!    the D28 lanes.
//!
//! Step 2 increment 4b (the producer emits drops, `crates/trust-thir-lower/src/drops.rs`):
//!  * `guard_scope` and `drop_string` MOVED from `refused` (`abstracted(drop)`, plus
//!    `abstracted(destructor)` for `guard_scope`) to `conserved`: their trust-ir carries the
//!    `Inst::Drop` rustc's elaboration performs, at the same point, as the gate's drop leg checks
//!    against the drop oracle (`drop_oracle.rs`) — and the dump's text shows it;
//!  * the shapes the producer does not place yet keep `abstracted(drop)`, and the gate says why
//!    (`S::set_rows_call`: a drop-and-replace through `&mut self`);
//!  * THE DROP MUTATIONS (`TRUST_IR_LOWER_MUTATE_DROPS`, TEST-ONLY): a producer that ignores moves
//!    drops a moved value again (`guard_explicit_drop`, `set_box`) and one that places nothing
//!    while recording its plan (`guard_scope`, `drop_string`) are both refused
//!    `not-conserved(drop)` — a missing OR an extra drop refuses;
//!  * channel C's drop column: `guard_scope` reads `drops=placed` (the instance lane still refuses
//!    it as drop-bearing: relaxing that frozen leg is D18 OD-2, increment 4c), and the summary
//!    counts `drops_mismatch=0`.
//!
//! Step 2 increment 4b residuals (the producer places a live temporary, a by-value pattern
//! binding and a drop-and-replace through a pointer): `temp_discard`, `temp_borrow`, `bind_some`,
//! `bind_destructure` and `replace_through` are conserved, and one TEST-ONLY mutation per shape
//! is refused `not-conserved(drop)`: a temporary dropped at the wrong scope's end
//! (`temp-outer-scope`), a partially moved value dropped whole (`open-as-static`), and an old
//! pointee dropped twice (`pointee-twice`).
//!
//! The 4b residuals review (2026-10-08): a borrowed temporary is dropped through the object the
//! program used — `cell_temp` and `refcell_temp` (a callee mutating, through the copy the
//! shared-borrow snapshot lane hands it, a `Cell` and a `RefCell`'s buffer) are conserved, and the
//! dump's text pins each drop's pointer to the operand the callee receives. The gate never reads
//! an `Inst::Drop`'s pointer; the TEST-ONLY mutation `temp-borrow-slot` (the first cut's drop
//! through the borrow's own slot) is caught by that pin.
//@ ignore-cross-compile

use std::collections::BTreeMap;

use run_make_support::{cmd, rfs, rustc, rustc_path, serde_json};

// Trust: resolve fixture paths through the sidecar's exact linker identities.
mod artifact_identity;
use artifact_identity::{body_lines, function_rows, function_symbol};

fn fnv1a64(bytes: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for b in bytes {
        h ^= u64::from(*b);
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    h
}

/// Dump `effects.rs` into `dir` (with extra flags) and return the sidecar's rows:
/// `function -> (verdict, tags)`, plus the parsed sidecar.
fn dump(dir: &str, extra: &[&str]) -> (BTreeMap<String, (String, Vec<String>)>, serde_json::Value) {
    dump_env(dir, extra, None)
}

/// [`dump`] with the drop-mutation environment variable set (`drops.rs`, TEST-ONLY).
fn dump_env(
    dir: &str,
    extra: &[&str],
    mutate_drops: Option<&str>,
) -> (BTreeMap<String, (String, Vec<String>)>, serde_json::Value) {
    let mut c = cmd(rustc_path());
    if let Some(m) = mutate_drops {
        c.env("TRUST_IR_LOWER_MUTATE_DROPS", m);
    }
    c.args([
        "effects.rs",
        "--edition=2024",
        "--crate-type=lib",
        "--crate-name=effects",
        "-Copt-level=0",
        "-Ccodegen-units=1",
        "-Ztrust-verify=off",
        "-Ztrust-ir-lower=on",
        &format!("-Ztrust-dump=ir:{dir}"),
        "--out-dir",
        &format!("{dir}-out"),
    ]);
    c.args(extra);
    c.run();
    let sidecar: serde_json::Value =
        serde_json::from_slice(&rfs::read(format!("{dir}/effects.effect-conservation.json")))
            .expect("the sidecar is valid JSON");
    assert_eq!(sidecar["schema"], "trust.effect-conservation.v1", "{sidecar}");
    let mut rows = BTreeMap::new();
    for (name, f) in function_rows(&sidecar) {
        let name = name.to_string();
        let verdict = f["verdict"].as_str().expect("a verdict").to_string();
        assert!(verdict == "conserved" || verdict == "refused", "{f}");
        let tags: Vec<String> = f["tags"]
            .as_array()
            .expect("a tag list")
            .iter()
            .map(|t| t.as_str().expect("a tag").to_string())
            .collect();
        assert_eq!(verdict == "conserved", tags.is_empty(), "verdict and tags agree: {f}");
        assert!(rows.insert(name, (verdict, tags)).is_none(), "one row per function");
    }
    (rows, sidecar)
}

/// Bind the extra undef tag to the actual field type and store, retaining the
/// source value computation while showing that its result is still discarded.
fn assert_physical_field_abstractions(text: &str, sidecar: &serde_json::Value) {
    for (owner, field, name, kind) in [
        ("S", "rows", "S::set_rows_call", "struct"),
        ("Holder", "p", "Holder::set_pair", "enum"),
    ] {
        let prefix = format!("struct @{owner} {{ {field}: ");
        let declarations: Vec<_> = text.lines().filter(|line| line.starts_with(&prefix)).collect();
        let [declaration] = declarations.as_slice() else {
            panic!("one actual {owner}.{field} declaration: {declarations:?}");
        };
        let field_ty = declaration.strip_prefix(&prefix).unwrap().split_whitespace().next().unwrap();
        let field_id = field_ty.strip_prefix(&format!("{kind}.")).expect("a physical field type");
        let owner_ty = format!("struct.{}", declaration.rsplit_once(" id=").unwrap().1);
        let field_declarations: Vec<_> = text
            .lines()
            .filter(|line| {
                line.starts_with(&format!("{kind} @")) && line.ends_with(&format!(" id={field_id}"))
            })
            .collect();
        let [field_declaration] = field_declarations.as_slice() else {
            panic!("one definition of mapped {field_ty}: {field_declarations:?}");
        };
        if kind == "struct" {
            assert!(
                field_declaration.contains("Vec<u32>")
                    && field_declaration.contains("{ buf: struct.")
                    && field_declaration.contains(", len: usize @"),
                "rows retains the physical Vec fields: {field_declaration}"
            );
        } else {
            let pair = text.lines().find(|line| line.starts_with("struct @Pair { ")).unwrap();
            let pair_ty = format!("struct.{}", pair.rsplit_once(" id=").unwrap().1);
            assert!(
                field_declaration.contains(&format!("Some({pair_ty})"))
                    && field_declaration.contains("layout("),
                "p retains its physical Some(Pair) payload: {field_declaration}"
            );
        }
        let body = body_lines(text, function_symbol(sidecar, name));
        let undefs: Vec<_> =
            body.iter().filter(|line| line.ends_with(&format!(" = undef {field_ty}"))).collect();
        let [undef] = undefs.as_slice() else {
            panic!("one undef of the mapped field type in {name}: {body:#?}");
        };
        let undef_value = undef.split_once(" = ").unwrap().0;
        let insert_marker = format!(" = insertfield {owner_ty} ");
        let inserts: Vec<_> = body
            .iter()
            .filter(|line| {
                line.contains(&insert_marker) && line.ends_with(&format!(", 0, {undef_value}"))
            })
            .collect();
        let [insert] = inserts.as_slice() else {
            panic!("one actual undef store into {owner}.{field}: {body:#?}");
        };
        let (stored_value, inserted) = insert.split_once(&insert_marker).unwrap();
        let base = inserted.split(',').next().unwrap();
        let load_prefix = format!("{base} = load {owner_ty}, ptr ");
        let ptr = body.iter().find_map(|line| line.strip_prefix(&load_prefix)).unwrap();
        assert!(
            body.iter().any(|line| line == &format!("store {owner_ty} {stored_value}, ptr {ptr}")),
            "the undef field update is stored through the same loaded receiver: {body:#?}"
        );
        let source_marker = if kind == "struct" {
            " = call @".to_string()
        } else {
            format!(" = insertfield {field_ty} ")
        };
        let sources: Vec<_> = body.iter().filter(|line| line.contains(&source_marker)).collect();
        let [source] = sources.as_slice() else {
            panic!("one retained source value computation in {name}: {body:#?}");
        };
        let source_value = source.split_once(" = ").unwrap().0;
        for line in body.iter().filter(|line| *line != *source) {
            assert!(
                !line
                    .split(|c: char| !(c.is_ascii_alphanumeric() || c == '_' || c == '%'))
                    .any(|token| token == source_value),
                "{name} still discards its computed value before storing undef: {line}"
            );
        }
    }
}

/// `Ok` when `name`'s one `drop` goes through a pointer some `call` of the same body receives as
/// an operand (the 4b residuals review: the drop runs on the object the callee used).
fn drop_is_callee_operand(text: &str, sidecar: &serde_json::Value, name: &str) -> Result<(), String> {
    let body = body_lines(text, function_symbol(sidecar, name));
    let drops: Vec<&String> = body.iter().filter(|l| l.starts_with("drop ")).collect();
    let [drop] = drops.as_slice() else {
        return Err(format!("expected one drop, found {drops:?} in {body:#?}"));
    };
    let ptr = drop.rsplit(',').next().unwrap_or("").trim().to_string();
    let receives = body.iter().filter(|l| l.starts_with("call @") || l.contains(" call @")).any(|l| {
        let args = l.rsplit_once('(').map(|(_, a)| a.trim_end_matches(')')).unwrap_or("");
        args.split(',').any(|a| a.trim() == ptr)
    });
    if receives { Ok(()) } else { Err(format!("`{drop}`: no call receives `{ptr}` in {body:#?}")) }
}

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return; // Stock rustc has no Trust-IR artifact interface.
    }
    seam_one_working_copy();

    // ── The sidecar ─────────────────────────────────────────────────────────
    let (rows, sidecar) = dump("effects-ir", &[]);
    let row = |name: &str| {
        rows.get(name).cloned().unwrap_or_else(|| panic!("no sidecar row for `{name}`: {rows:?}"))
    };
    for name in [
        "close_ret",
        "rows_after_close",
        "close_then_some",
        "bump",
        "store_through",
        "close_range",
        "max3",
        "<Guard as std::ops::Drop>::drop",
        "guard_explicit_drop",
        "Outer::set_pair",
        "set_flag",
        "consume_ref",
        "set_box",
        "str_then_user",
        // Step 2 increment 4b: the producer places their drops.
        "guard_scope",
        "drop_string",
        // Step 2 increment 4b residuals: a temporary, a pattern binding, a drop-and-replace
        // through a pointer.
        "temp_discard",
        "temp_borrow",
        "bind_some",
        "bind_destructure",
        "replace_through",
        // The 4b residuals review: a borrowed temporary the callee mutates through a copy.
        "cell_temp",
        "refcell_temp",
    ] {
        let (verdict, tags) = row(name);
        assert_eq!(verdict, "conserved", "`{name}` carries every effect of its MIR: {tags:?}");
    }
    let refused: [(&str, &[&str]); 14] = [
        (
            "S::set_rows_call",
            &["abstracted(drop)", "abstracted(undef)", "abstracted(opaque-lane)"],
        ),
        (
            "S::set_boxed_call",
            &["abstracted(drop)", "abstracted(undef)", "abstracted(opaque-lane)"],
        ),
        ("Holder::set_pair", &["abstracted(undef)", "abstracted(opaque-lane)"]),
        (
            "LaneCommand::stdin",
            &[
                "abstracted(drop)",
                "abstracted(destructor)",
                "abstracted(undef)",
                "abstracted(opaque-lane)",
            ],
        ),
        ("resize", &["abstracted(opaque-lane)"]),
        ("clear_pair", &["abstracted(opaque-lane)"]),
        ("ret_tuple", &["abstracted(opaque-lane)"]),
        ("div_lost", &["abstracted(opaque-lane)"]),
        ("ovf_lost", &["abstracted(opaque-lane)"]),
        ("index_lost", &["abstracted(opaque-lane)"]),
        ("payload_eq_then_str", &["abstracted(opaque-lane)"]),
        ("via_box_raw", &["abstracted(opaque-lane)"]),
        ("via_box_param", &["abstracted(opaque-lane)"]),
        ("promoted_collapsed_root", &["abstracted(drop)", "abstracted(opaque-lane)"]),
    ];
    for (name, want) in refused {
        let (verdict, tags) = row(name);
        assert_eq!(verdict, "refused", "`{name}`");
        assert_eq!(tags, want, "`{name}` names exactly its lanes");
    }
    // No lane here drops a CALL or a STORE: an abstraction is not a lost effect.
    for (name, (_, tags)) in &rows {
        assert!(
            !tags.iter().any(|t| t.starts_with("not-conserved(")),
            "`{name}` lost an effect without the mutation: {tags:?}"
        );
    }
    // The gate says why a drop stayed elided: the producer's planner named the shape.
    let detail = sidecar["functions"]
        .as_array()
        .expect("a function list")
        .iter()
        .find(|f| f["def_path"] == "S::set_rows_call")
        .map(|f| f["detail"].to_string())
        .expect("a row for `S::set_rows_call`");
    assert!(
        detail.contains("the producer placed no drop: drop-and-replace of a place that is not a tracked local"),
        "{detail}"
    );
    // A PROMOTED root spelled trivially droppable is not placed either (trust-ir v55's
    // `NonCanonicalDrop`): the placement names the spelling, and no `drop (i32, bool)` reaches
    // the module, which would fail the whole crate's validation and with it this dump.
    let detail = sidecar["functions"]
        .as_array()
        .expect("a function list")
        .iter()
        .find(|f| f["def_path"] == "promoted_collapsed_root")
        .map(|f| f["detail"].to_string())
        .expect("a row for `promoted_collapsed_root`");
    assert!(
        detail.contains("placement failed: root spelled as the trivially droppable `(i32, bool)`"),
        "{detail}"
    );
    // The sidecar is bound to the exact text dump beside it.
    let text = rfs::read("effects-ir/effects.trust-ir.txt");
    // ... and that text carries the drops: `guard_scope`'s body drops its `Guard`.
    let text_str = String::from_utf8_lossy(&text).to_string();
    assert_physical_field_abstractions(&text_str, &sidecar);
    let guard_fn = body_lines(&text_str, function_symbol(&sidecar, "guard_scope")).join("\n");
    assert!(!guard_fn.is_empty(), "`guard_scope` is in the dump:\n{text_str}");
    assert!(guard_fn.contains("\ndrop struct."), "`guard_scope` drops its guard:\n{guard_fn}");
    assert!(!text_str.contains("drop (i32, bool)"), "a trivially droppable drop:\n{text_str}");
    // THE BORROWED TEMPORARY'S POINTER (the 4b residuals review): the gate compares drop keys and
    // counts, never an `Inst::Drop`'s pointer, so the text pins it. Each body drops its borrowed
    // temporary through exactly the operand its callee receives — the object the callee mutated
    // (`cell_temp`'s `Cell`, `refcell_temp`'s buffer) or whose address it saw (`temp_borrow`).
    for name in ["temp_borrow", "cell_temp", "refcell_temp"] {
        drop_is_callee_operand(&text_str, &sidecar, name)
            .unwrap_or_else(|why| panic!("`{name}`: {why}"));
    }
    assert_eq!(sidecar["module_text"]["name"], "effects.trust-ir.txt");
    assert_eq!(sidecar["module_text"]["bytes"], text.len() as u64);
    assert_eq!(sidecar["module_text"]["fnv1a64"], format!("{:016x}", fnv1a64(&text)));

    // ── THE MUTATION: the field-store RHS lane as it was before ec8b51bb3b ──
    let (mutated, _) = dump("effects-mutated-ir", &["-Ztrust-ir-lower-mutate-rhs-effects"]);
    let (_, tags) = mutated.get("S::set_rows_call").cloned().expect("still spliced under the mutation");
    assert!(
        tags.iter().any(|t| t == "not-conserved(call)"),
        "with the lane's effect lowering disabled the gate must name the lost call: {tags:?}"
    );
    // The 2026-10-01 review's lost effects: each is named, by the effect the lane dropped.
    for (name, lost) in [
        ("div_lost", "not-conserved(assert)"),
        ("ovf_lost", "not-conserved(assert)"),
        ("index_lost", "not-conserved(assert)"),
        ("payload_eq_then_str", "not-conserved(call)"),
        ("via_box_raw", "not-conserved(store)"),
        ("via_box_param", "not-conserved(store)"),
    ] {
        let (_, tags) = mutated.get(name).cloned().expect("still spliced under the mutation");
        assert_eq!(
            tags,
            [lost, "abstracted(opaque-lane)"],
            "`{name}`: the gate must name exactly the effect the lane dropped"
        );
    }
    // The mutation touches only that lane: the plain bodies stay conserved.
    for name in ["close_ret", "max3", "store_through", "set_box", "str_then_user"] {
        assert_eq!(mutated[name].0, "conserved", "`{name}` under the mutation");
    }

    // ── THE DROP MUTATIONS (step 2 increment 4b) ───────────────────────────
    // A producer that ignores moves drops a moved value a second time: an EXTRA drop.
    let (extra, _) = dump_env("effects-drops-extra-ir", &[], Some("ignore-moves"));
    for name in ["guard_explicit_drop", "set_box"] {
        assert_eq!(
            extra[name],
            ("refused".to_string(), vec!["not-conserved(drop)".to_string()]),
            "`{name}`: a drop the program does not perform must refuse the body"
        );
    }
    assert_eq!(extra["guard_scope"].0, "conserved", "a body with no move is unaffected");
    // A producer that records its plan but places nothing: the module LACKS the drops.
    let (skipped, _) = dump_env("effects-drops-missing-ir", &[], Some("skip-emission"));
    for name in ["guard_scope", "drop_string"] {
        assert_eq!(
            skipped[name],
            ("refused".to_string(), vec!["not-conserved(drop)".to_string()]),
            "`{name}`: a module without the drops the producer recorded must refuse the body"
        );
    }

    // ── THE RESIDUAL-SHAPE MUTATIONS (step 2 increment 4b residuals) ───────
    // One wrong placement per new shape, each refused by the gate (`not-conserved(drop)`: the
    // claim or the module has a drop the program does not perform).
    let refused_by = |rows: &BTreeMap<String, (String, Vec<String>)>, name: &str, why: &str| {
        let (verdict, tags) = rows
            .get(name)
            .cloned()
            .unwrap_or_else(|| panic!("no sidecar row for `{name}` under the mutation: {rows:?}"));
        assert_eq!(verdict, "refused", "`{name}`: {why}: {tags:?}");
        assert!(tags.iter().any(|t| t == "not-conserved(drop)"), "`{name}`: {why}: {tags:?}");
    };
    // A temporary dropped at the wrong scope's end.
    let (outer, _) = dump_env("effects-drops-temp-scope-ir", &[], Some("temp-outer-scope"));
    for name in ["temp_discard", "temp_borrow"] {
        refused_by(&outer, name, "a temporary dropped at the wrong scope end must refuse the body");
    }
    assert_eq!(outer["guard_scope"].0, "conserved", "a body with no temporary is unaffected");
    // An open drop of a partially moved value placed as a whole drop: the moved part twice.
    let (whole, _) = dump_env("effects-drops-open-ir", &[], Some("open-as-static"));
    for name in ["bind_some", "bind_destructure"] {
        refused_by(&whole, name, "a partially moved value dropped whole must refuse the body");
    }
    assert_eq!(whole["guard_scope"].0, "conserved", "a body with no partial move is unaffected");
    // A drop-and-replace through a pointer that drops the old pointee twice.
    let (twice, _) = dump_env("effects-drops-pointee-ir", &[], Some("pointee-twice"));
    refused_by(&twice, "replace_through", "a pointee dropped twice must refuse the body");
    assert_eq!(twice["guard_scope"].0, "conserved", "a body with no such store is unaffected");

    // The first cut's borrowed-temporary drop (through the borrow's slot, unproved) restored:
    // the callee's operand is a copy, so that drop never proves the temporary's home.
    // Trust (2026-11-08): since 52d37fab29 ("Materialize owned shared temporaries with
    // mandatory home proofs") the producer refuses such a body before it is emitted —
    // `finish_drops` keeps `Borrow(owned temporary home unproved)` when placement fails for a
    // body holding an owned shared temporary, so drop elision cannot admit it — and the
    // body is absent from the module text and the sidecar. Pin that refusal exactly; if a
    // body is ever emitted again, the pointer pin above must still catch its stale drop.
    let (_, slot_sidecar) = dump_env("effects-drops-borrow-slot-ir", &[], Some("temp-borrow-slot"));
    let slot_text =
        String::from_utf8_lossy(&rfs::read("effects-drops-borrow-slot-ir/effects.trust-ir.txt"))
            .to_string();
    let slot_coverage: serde_json::Value =
        serde_json::from_slice(&rfs::read("effects-drops-borrow-slot-ir/effects.coverage.json"))
            .expect("the coverage report is valid JSON");
    let slot_rows = function_rows(&slot_sidecar);
    for name in ["cell_temp", "refcell_temp", "temp_borrow"] {
        if slot_rows.contains_key(name) {
            assert!(
                drop_is_callee_operand(&slot_text, &slot_sidecar, name).is_err(),
                "`{name}`: the first cut drops the borrow's slot, not the callee's operand"
            );
            continue;
        }
        let body = slot_coverage["bodies"]
            .as_array()
            .expect("a body inventory")
            .iter()
            .find(|b| b["def_path"] == name)
            .unwrap_or_else(|| panic!("`{name}` is in the mutated run's body inventory"));
        assert_eq!(body["lowered"], false, "`{name}`: the first cut is refused: {body}");
        assert_eq!(
            body["unsupported"],
            serde_json::json!([["Borrow(owned temporary home unproved)", 1]]),
            "`{name}`: refused by the temporary-home gate, and only by it: {body}"
        );
    }

    // ── Probe channel C on the same fixture ────────────────────────────────
    let probe = rustc()
        .input("effects.rs")
        .crate_type("lib")
        .edition("2024")
        .arg("-Copt-level=0")
        .arg("-Ccodegen-units=1")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .arg("-Ztrust-instance-flip-probe=*")
        .arg("-Zno-steal-thir")
        .run()
        .stderr_utf8();
    let c_row = |def: &str| {
        let found: Vec<&str> = probe
            .lines()
            .filter(|l| l.starts_with("TRUST-WALLA-PROBE C sym="))
            .filter(|l| l.contains(&format!(" def={def} ")))
            .collect();
        assert_eq!(found.len(), 1, "one channel-C row for `{def}`:\n{probe}");
        found[0].to_string()
    };
    let summary = probe
        .lines()
        .find(|l| l.starts_with("TRUST-WALLA-PROBE C summary"))
        .unwrap_or_else(|| panic!("channel C printed no summary:\n{probe}"));
    for field in ["not_conserved=0", "abstracted=", "panics=0", "drops_mismatch=0"] {
        assert!(summary.contains(field), "summary must say `{field}`: {summary}");
    }
    for (def, want) in [
        ("close_ret", "result=ok("),
        ("max3", "result=ok("),
        ("store_through", "result=ok("),
        // Since step 2 increment 3, channel C reads these bodies through the instance lane's
        // frozen admission, which refuses each abstraction before the conservation verdict is
        // asked: the drop gate reads every place type, the opaque-collapse and undef lanes are
        // refused, and a pending-const sentinel is refused first. Still never `ok`; the sidecar
        // rows above carry the conservation tags (measured on the merged tree, 2026-10-01).
        ("guard_scope", "result=refused(LaneRefused(\"drop-bearing\"))"),
        ("S::set_rows_call", "result=refused(LaneRefused(\"opaque collapse\"))"),
        ("S::set_boxed_call", "result=refused(LaneRefused(\"opaque collapse\"))"),
        ("Holder::set_pair", "result=refused(PendingConsts)"),
    ] {
        let r = c_row(def);
        assert!(r.contains(want), "`{def}` must read `{want}`: {r}");
    }
    // The drop column (step 2 increment 4b): the producer placed `guard_scope`'s drop and the gate
    // found it equal to rustc's; `S::set_rows_call`'s stayed elided.
    for (def, want) in [
        ("guard_scope", " drops=placed "),
        ("drop_string", " drops=placed "),
        ("S::set_rows_call", " drops=elided "),
        ("max3", " drops=none "),
    ] {
        let r = c_row(def);
        assert!(r.contains(want), "`{def}` must read `{want}`: {r}");
    }
}

/// Trust (R8-SEAM, `docs/DECISION_QUEUE.md`, taken 2026-10-05): the crate-seam differential computes
/// from ONE working copy of the assembled module what it computed from whole-module copies. The
/// TEST-ONLY `-Ztrust-ir-seam-reference=<report>` option runs the pre-R8-SEAM seam over the
/// pre-R8-SEAM differential (`crates/trust-thir-lower/src/crate_module/seam_reference.rs` and
/// `.../differential/compare_entries_reference.rs`, verbatim) beside the live one at
/// crate finalization and fails finalization on any difference in the verdicts or the UC probe's
/// traced outcomes; `tests/run-make/trust-ir-seam-one-working-copy` pins that each lane is reached.
fn seam_cross_check(file: &str, edition: &str, tag: &str) {
    let report = format!("seam-reference-{tag}.txt");
    let out = rustc()
        .input(file)
        .crate_type("lib")
        .edition(edition)
        .arg("-Copt-level=0")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .arg("--emit=metadata")
        .out_dir(format!("seam-out-{tag}"))
        .arg(format!("-Ztrust-ir-seam-reference={report}"))
        .run();
    let stderr = out.stderr_utf8();
    assert!(!stderr.contains("seam cross-check"), "{tag}: the seams differ:\n{stderr}");
    let text = rfs::read_to_string(&report);
    for line in ["differences 0", "restored true"] {
        assert!(text.lines().any(|l| l == line), "{tag}: the report lacks `{line}`:\n{text}");
    }
    assert!(!text.lines().any(|l| l == "verdicts 0"), "{tag}: no deferred body was compared:\n{text}");
}

fn seam_one_working_copy() {
    seam_cross_check("effects.rs", "2024", "effects");
}

/// The R8-SEAM cross-check on this fixture's subject, under libtest as well as compiletest (the
/// frozen-file waiver cites it).
#[test]
fn the_seam_on_the_effects_subject_is_the_reference_seam() {
    seam_one_working_copy();
}
