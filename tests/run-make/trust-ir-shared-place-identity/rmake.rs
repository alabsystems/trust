//! Actual direct-THIR output: calls, caller reads and drops share the real home.
//! No LLVM artifact or authored IR surrogate substitutes for this observation.
//! Restoring the old copy in the observed text must fail the identity check.

use std::collections::BTreeSet;
use std::path::Path;

use run_make_support::{rfs, rustc, serde_json, source_root};

fn row<'a>(coverage: &'a serde_json::Value, name: &str) -> &'a serde_json::Value {
    named_row(coverage, "bodies", name)
}

fn named_row<'a>(inventory: &'a serde_json::Value, key: &str, name: &str) -> &'a serde_json::Value {
    let found: Vec<_> = inventory[key]
        .as_array()
        .expect("complete body inventory")
        .iter()
        .filter(|row| {
            row["def_path"].as_str().is_some_and(|path| path.rsplit("::").next() == Some(name))
        })
        .collect();
    assert_eq!(found.len(), 1, "one actual row for {name}: {found:?}");
    found[0]
}

fn function<'a>(text: &'a str, name: &str) -> &'a str {
    let directive = format!("; #display-path: {name:?}\n");
    let mut found = Vec::new();
    let mut offset = 0;
    for line in text.split_inclusive('\n') {
        if line.contains("fn @") {
            let tail = &text[offset..];
            let end = tail.find("\n}\n").expect("complete emitted function") + 3;
            if tail[..end].contains(&directive) {
                found.push(&tail[..end]);
            }
        }
        offset += line.len();
    }
    assert_eq!(found.len(), 1, "one actual function for {name}: {found:?}");
    found[0]
}

fn function_id(text: &str, name: &str) -> u64 {
    let body = function(text, name);
    let start = text.find(body).expect("actual function is in the module");
    text[..start].lines().filter(|line| line.contains("fn @")).count() as u64
}

fn calls(function: &str) -> Vec<(u64, Vec<String>)> {
    function
        .lines()
        .filter_map(|line| line.split_once("call @func."))
        .map(|(_, rest)| {
            let digits = rest.bytes().take_while(u8::is_ascii_digit).count();
            let id = rest[..digits].parse().expect("numeric callee identity");
            let args = rest[digits..]
                .strip_prefix('(')
                .and_then(|args| args.split_once(')'))
                .expect("complete direct call")
                .0;
            (id, args.split(',').map(|arg| arg.trim().to_owned()).collect())
        })
        .collect()
}

fn allocations(function: &str) -> Vec<String> {
    function
        .lines()
        .filter_map(|line| line.split_once(" = alloca "))
        .map(|(result, _)| result.trim().to_owned())
        .collect()
}

fn shared_home(function: &str, callees: &[u64]) -> Result<String, String> {
    let slots = allocations(function);
    if slots.len() != 1 {
        return Err(format!("expected one real home, got {slots:?}"));
    }
    let actual = calls(function);
    if actual.iter().map(|(id, _)| *id).ne(callees.iter().copied()) {
        return Err(format!("missing/reordered/repeated consumer: {actual:?} vs {callees:?}"));
    }
    if actual.iter().any(|(_, args)| args != &slots) {
        return Err(format!("consumer received a copied/different home: {actual:?} vs {slots:?}"));
    }
    Ok(slots[0].clone())
}

fn dropped_at(function: &str, home: &str) -> bool {
    let drops: Vec<_> = function
        .lines()
        .map(str::trim)
        // Canonical node metadata is a trailing `  ; #loc:` / `  ; #scope:`
        // clause. It is not part of the Drop's final pointer operand.
        .map(|line| line.split_once("  ; ").map_or(line, |(instruction, _)| instruction))
        .filter(|line| line.starts_with("drop "))
        .map(|line| line.rsplit_once(", ").expect("drop names its pointer").1)
        .collect();
    drops == [home]
}

fn drop_metadata_controls() {
    let home = "%7";
    for suffix in ["", "  ; #loc: 2 17 4", "  ; #scope: 3", "  ; #loc: 2 17 4  ; #scope: 3"] {
        let actual = format!("    drop struct.0, {home}{suffix}\n");
        let wrong = format!("    drop struct.0, %8{suffix}\n");
        let prefix = format!("    drop struct.0, %70{suffix}\n");
        assert!(dropped_at(&actual, home), "canonical suffix lost the real home: {actual}");
        assert!(!dropped_at(&prefix, home), "pointer equality became a prefix check");
        assert!(!dropped_at(&wrong, home), "metadata hid the wrong pointer: {wrong}");
        assert!(!dropped_at(&format!("{actual}{actual}"), home), "duplicate drop accepted");
        assert!(!dropped_at(&format!("{actual}{wrong}"), home), "a second wrong drop was ignored");
    }
    assert!(!dropped_at("    ret  ; #loc: 2 17 4  ; #scope: 3\n", home), "missing drop accepted");
}

fn main() {
    drop_metadata_controls();
    let out = Path::new("shared-place-ir");
    rfs::create_dir(out);
    rustc()
        .input(source_root().join("tests/ui/trust/trust_ir_shared_place_identity.rs"))
        .crate_name("shared_place")
        .crate_type("lib")
        .edition("2021")
        .emit("metadata")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower=on")
        .arg(format!("-Ztrust-dump=ir:{}", out.display()))
        .out_dir(out)
        .run();
    assert!(!rfs::read(out.join("shared_place.trust-ir.bin")).is_empty());
    let text = rfs::read_to_string(out.join("shared_place.trust-ir.txt"));
    let coverage: serde_json::Value =
        serde_json::from_str(&rfs::read_to_string(out.join("shared_place.coverage.json")))
            .expect("valid coverage JSON");
    assert_eq!(coverage["proof_authority"], false);
    assert_eq!(coverage["native_verification_requests"], false);
    assert_eq!(coverage["publication"]["commit_marker"], true);
    let effects: serde_json::Value =
        serde_json::from_slice(&rfs::read(out.join("shared_place.effect-conservation.json")))
            .expect("valid effect conservation JSON");
    assert_eq!(effects["schema"], "trust.effect-conservation.v1");
    assert_eq!(effects["module_text"]["bytes"], text.len());
    let hash = text.bytes().fold(0xcbf2_9ce4_8422_2325_u64, |h, b| {
        (h ^ u64::from(b)).wrapping_mul(0x0000_0100_0000_01b3)
    });
    assert_eq!(effects["module_text"]["fnv1a64"], format!("{hash:016x}"));
    let effect = |name| named_row(&effects, "functions", name);
    let id = |name| row(&coverage, name)["func_id"].as_u64().expect("real consumer identity");
    let body_of = |name| {
        function(&text, row(&coverage, name)["def_path"].as_str().expect("actual display path"))
    };

    for (name, consumers) in [
        ("cell_parameter", vec![id("touch_cell"), id("touch_cell"), id("read_cell")]),
        ("cell_local", vec![id("touch_cell"), id("read_cell")]),
        ("refcell_local", vec![id("touch_refcell"), id("read_refcell")]),
        ("nested_local", vec![id("touch_nested"), id("read_nested")]),
        ("freeze_promoted", vec![id("write_scalar"), id("read_scalar")]),
        ("drop_home", vec![id("touch_drop")]),
        ("unsupported_drop_home", vec![id("read_drop_frozen")]),
    ] {
        let r = row(&coverage, name);
        assert_eq!(r["lowered"], true, "{name}: {r}");
        assert_eq!(r["spliced"], true, "{name}: {r}");
        assert_eq!(r["symbolic"], false, "{name}: {r}");
        assert_eq!(r["unsupported"].as_array().map(Vec::len), Some(0), "{name}: {r}");
        assert_eq!(effect(name)["verdict"], "conserved", "{name}: {}", effect(name));
        let body = body_of(name);
        assert!(!body.contains(" = undef "), "no erased pointee for {name}");
        let home =
            shared_home(body, &consumers).unwrap_or_else(|why| panic!("{name}: {why}\n{body}"));
        if matches!(name, "drop_home" | "unsupported_drop_home") {
            assert!(dropped_at(body, &home), "drop must use the callee's actual home:\n{body}");
            let wrong = body
                .lines()
                .map(|line| {
                    if line.trim_start().starts_with("drop ") {
                        line.replace(&home, "%999999")
                    } else {
                        line.to_owned()
                    }
                })
                .collect::<Vec<_>>()
                .join("\n");
            assert!(!dropped_at(&wrong, &home), "a stale original drop was accepted");
        }

        // The actual old emission has another Alloca and passes that copy to
        // a consumer. This diagnostic mutant must not satisfy the same check.
        let target = format!("call @func.{}({home})", consumers[0]);
        assert!(body.contains(&target));
        let copied = body.replacen(&target, &target.replace(&home, "%999999"), 1);
        assert!(shared_home(&copied, &consumers).is_err(), "copied call accepted for {name}");
        let allocation = body.lines().find(|line| line.contains(" = alloca ")).unwrap();
        let copy = allocation.replacen(&home, "%999999", 1);
        assert!(shared_home(&format!("{copy}\n{copied}"), &consumers).is_err());
    }

    // Unlike the diagnostic text mutants, this is real compiler output for a
    // Rust source mutant that constructs a copy. The writer must reach the new
    // home while both reads reach the original. It must fail the one-home check.
    let copy_row = row(&coverage, "cell_copy_mutant");
    assert_eq!(copy_row["spliced"], true, "source copy mutant did not lower: {copy_row}");
    assert_eq!(copy_row["symbolic"], false);
    assert_eq!(copy_row["unsupported"].as_array().map(Vec::len), Some(0));
    assert_eq!(effect("cell_copy_mutant")["verdict"], "conserved");
    let copied = body_of("cell_copy_mutant");
    let homes = allocations(copied);
    assert_eq!(homes.len(), 2, "source copy mutant must have two real objects: {copied}");
    let consumers = [id("read_cell"), id("touch_cell"), id("read_cell")];
    let uses: Vec<_> = calls(copied).into_iter().filter(|(id, _)| consumers.contains(id)).collect();
    assert_eq!(uses.iter().map(|(id, _)| *id).collect::<Vec<_>>(), consumers);
    assert_eq!(uses[0].1, uses[2].1, "both reads must reach the original: {copied}");
    assert_ne!(uses[0].1, uses[1].1, "writer must reach the copy: {copied}");
    for (_, args) in &uses {
        assert_eq!(args.len(), 1);
        assert!(homes.contains(&args[0]));
    }
    assert!(shared_home(copied, &consumers).is_err(), "real copied-object mutant accepted");

    let forwarded = body_of("forwarded_cell");
    assert_eq!(row(&coverage, "forwarded_cell")["spliced"], true);
    assert_eq!(effect("forwarded_cell")["verdict"], "conserved");
    assert!(allocations(forwarded).is_empty(), "forwarding cannot allocate a new referent");
    let args: BTreeSet<_> = calls(forwarded).into_iter().map(|(_, args)| args).collect();
    assert_eq!(args, BTreeSet::from([vec!["%0".to_owned()]]));

    let field_row = row(&coverage, "freeze_field");
    assert_eq!(field_row["spliced"], true, "genuine field address lost: {field_row}");
    assert_eq!(field_row["symbolic"], false);
    assert_eq!(field_row["unsupported"].as_array().map(Vec::len), Some(0));
    assert_eq!(effect("freeze_field")["verdict"], "conserved");
    let field = body_of("freeze_field");
    let homes = allocations(field);
    assert_eq!(homes.len(), 1, "one home for a genuine projected place: {field}");
    let geps: Vec<_> = field
        .lines()
        .filter_map(|line| line.split_once(" = gep inbounds i8, ptr "))
        .filter(|(_, operands)| operands.starts_with(&format!("{}, ", homes[0])))
        .map(|(result, _)| result.trim().to_owned())
        .collect();
    assert_eq!(geps.len(), 1, "field pointer must derive from the real home: {field}");
    assert_eq!(calls(field), [(id("read_scalar"), geps)]);

    for name in ["freeze_neighbor", "freeze_aggregate", "freeze_temporary"] {
        let frozen = row(&coverage, name);
        assert_eq!(frozen["spliced"], true, "Freeze neighbor lost: {frozen}");
        assert_eq!(frozen["symbolic"], false, "Freeze neighbor substituted: {frozen}");
        assert_eq!(frozen["unsupported"].as_array().map(Vec::len), Some(0));
        assert_eq!(effect(name)["verdict"], "conserved", "{name}: {}", effect(name));
        assert!(!allocations(body_of(name)).is_empty());
    }

    for name in ["cell_field_parameter", "cell_field_local"] {
        let field_row = row(&coverage, name);
        assert_eq!(field_row["spliced"], true, "aggregate field lost: {field_row}");
        assert_eq!(field_row["symbolic"], false);
        assert_eq!(field_row["unsupported"].as_array().map(Vec::len), Some(0));
        assert_eq!(effect(name)["verdict"], "conserved");
        let body = body_of(name);
        let homes = allocations(body);
        assert_eq!(homes.len(), 1, "the parent owns the only storage: {body}");
        let field_ptrs: BTreeSet<_> = body.lines().filter_map(|line| {
            let (result, operands) = line.split_once(" = gep inbounds i8, ptr ")?;
            let offset = operands.split("  ;").next()?.trim()
                .strip_prefix(&format!("{}, ", homes[0]))?;
            let expected = format!("{offset} = const i64 4");
            body.lines().any(|instruction| instruction.split("  ;").next().unwrap().trim() == expected)
                .then(|| result.trim().to_owned())
        }).collect();
        let actual = calls(body);
        let mut expected = vec![id("touch_cell"), id("read_cell")];
        let consumers = if name == "cell_field_local" {
            // This source initializes its field through Cell::new(value).
            // Account for that actual call without confusing its value
            // argument with the later shared field-address arguments.
            let constructor = function_id(&text, "std::cell::Cell::<T>::new");
            expected.insert(0, constructor);
            assert_eq!(actual[0].1, ["%0"], "constructor must use the source value: {body}");
            let call = format!(" = call @func.{constructor}(%0)");
            let constructed = body.lines().find_map(|line| {
                line.split_once(&call).map(|(result, _)| result.trim())
            }).expect("actual constructor result");
            let stored = body.lines().find_map(|line| {
                let line = line.split("  ;").next().unwrap().trim();
                let operands = line.strip_prefix("store ")?;
                let (value, pointer) = operands.split_once(", ptr ")?;
                (pointer == homes[0]).then(|| value.split_once(' ').unwrap())
            }).expect("initial aggregate stored into the original home");
            assert!(body.lines().any(|line| {
                let line = line.split("  ;").next().unwrap().trim();
                line.starts_with(&format!("{} = insertfield {} ", stored.1, stored.0))
                    && line.ends_with(&format!(", 1, {constructed}"))
            }), "the constructor result must initialize the field in that home: {body}");
            &actual[1..]
        } else {
            &actual[..]
        };
        assert_eq!(actual.iter().map(|(callee, _)| *callee).collect::<Vec<_>>(), expected);
        assert!(consumers.iter().all(|(_, args)| args.len() == 1 && field_ptrs.contains(&args[0])),
            "each call must reach the same four-byte field offset of the original home: {body}");
    }

    for name in [
        "nonfreeze_temporary",
        "nonfreeze_refcell_temporary",
        "nonfreeze_nested_temporary",
        "nonfreeze_field_copy",
    ] {
        let refused = row(&coverage, name);
        assert_eq!(refused["spliced"], false, "unsupported snapshot shipped: {refused}");
        assert!(refused["unsupported"].to_string().contains("Borrow(snapshot requires Freeze)"));
    }

    for (name, tag) in [
        ("cell_field_raw_tail_escape", "Return(borrow ptr escapes tail)"),
        ("cell_field_raw_return_escape", "Return(borrow ptr escapes)"),
    ] {
        let escaped = row(&coverage, name);
        assert_eq!(escaped["spliced"], false, "frame-owned aggregate address escaped: {escaped}");
        assert!(escaped["unsupported"].to_string().contains(tag), "{escaped}");
    }

    let unpromotable = row(&coverage, "nonfreeze_unpromotable");
    assert_eq!(unpromotable["spliced"], false);
    for tag in ["Borrow(shared local lacks stable storage)", "Promote(non-scalar &mut param)"] {
        assert!(unpromotable["unsupported"].to_string().contains(tag), "{unpromotable}");
    }

    let unknown = row(&coverage, "unknown_snapshot");
    assert_eq!(unknown["symbolic"], true, "unknown source type must stay abstract: {unknown}");
    assert_eq!(unknown["spliced"], false);
    assert_eq!(unknown["splice_refusal"], "Splice(symbolic body)");
    assert_eq!(unknown["func_id"], serde_json::Value::Null);
    assert_eq!(unknown["differentials"]["interpreter"]["samples"], 0);

    // Coverage alone can contain an unconserved body. The production consumer's
    // conservation gate must still refuse this missing-home case by name.
    let no_home = effect("unrepresented_drop_home");
    assert_eq!(no_home["verdict"], "refused", "a destructor without its home admitted: {no_home}");
    assert!(no_home["tags"].to_string().contains("abstracted(drop)"));
    assert!(no_home["detail"].to_string().contains("shared-borrowed root has no promoted home"));
    assert!(!body_of("unrepresented_drop_home").lines().any(|line| line.trim().starts_with("drop ")));
}
