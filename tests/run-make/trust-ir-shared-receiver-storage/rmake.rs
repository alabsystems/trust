//! The core Lines/SplitWhitespace receiver failure, without a whole core build.
//!
//! The real final validator must accept the module AND retain both caller bodies.
//! Check the actual call operand comes from the stored slot, not the struct value
//! or a vararg declaration. Cell/generic twins must not acquire fresh snapshots.
//! Trust: the nine private source-goal controls live in rustc_driver_impl unit
//! tests, whose normal owner supplies the current in-process compiler cohort.
//@ ignore-cross-compile

use run_make_support::{rfs, rustc, serde_json, source_root};

fn functions(text: &str) -> Vec<&str> {
    let mut starts = Vec::new();
    let mut offset = 0;
    for line in text.split_inclusive('\n') {
        if line.contains("fn @") {
            starts.push(offset);
        }
        offset += line.len();
    }
    starts
        .into_iter()
        .map(|start| {
            let tail = &text[start..];
            let end = tail.find("\n}\n").expect("complete canonical function") + 3;
            &tail[..end]
        })
        .collect()
}

fn body_row<'a>(coverage: &'a serde_json::Value, leaf: &str) -> &'a serde_json::Value {
    let found: Vec<_> = coverage["bodies"]
        .as_array()
        .expect("complete body inventory")
        .iter()
        .filter(|row| {
            row["def_path"]
                .as_str()
                .is_some_and(|path| path.rsplit("::").next() == Some(leaf))
        })
        .collect();
    assert_eq!(found.len(), 1, "one original body for {leaf}");
    found[0]
}

fn main() {
    let fixture = source_root().join("tests/run-make/trust-ir-shared-receiver-storage");
    rfs::create_dir("receiver-ir");
    let stderr = rustc()
        .input(fixture.join("subject.rs"))
        .edition("2024")
        .crate_name("receiver_subject")
        .crate_type("lib")
        .emit("trust-ir")
        .out_dir("receiver-ir")
        .arg("-Ztrust-verify=off")
        .run()
        .stderr_utf8();
    assert!(
        !stderr.contains("semantic finalization failed"),
        "real validator refused:\n{stderr}"
    );
    let text = rfs::read_to_string("receiver-ir/receiver_subject.trust-ir.txt");
    let coverage: serde_json::Value = serde_json::from_str(&rfs::read_to_string(
        "receiver-ir/receiver_subject.trust-ir.coverage.json",
    ))
    .expect("real coverage sidecar");
    let functions = functions(&text);
    for name in ["remaining_lines", "remaining_words"] {
        let row = body_row(&coverage, name);
        assert_eq!(row["lowered"], true, "original caller was withdrawn: {row}");
        assert_eq!(
            row["spliced"], true,
            "original caller was not retained: {row}"
        );
        assert_eq!(
            row["unsupported"].as_array().map(Vec::len),
            Some(0),
            "{row}"
        );
        let bodies: Vec<_> = functions
            .iter()
            .copied()
            .filter(|function| {
                function.lines().any(|line| {
                    line.trim().starts_with("; #display-path:")
                        && line.trim().ends_with(&format!("::{name}\""))
                })
            })
            .collect();
        assert_eq!(bodies.len(), 1, "one actual retained caller {name}");
        let body = bodies[0];
        let slots: Vec<_> = body
            .lines()
            .filter_map(|line| {
                line.trim()
                    .split_once(" = alloca struct.")
                    .map(|(slot, _)| slot)
            })
            .collect();
        assert_eq!(
            slots.len(),
            1,
            "one actual shared snapshot in {name}:\n{body}"
        );
        let slot = slots[0];
        assert!(
            body.lines()
                .any(|line| line.trim().starts_with("store struct.")
                    && line.contains(&format!(", ptr {slot}"))),
            "unstored receiver slot:\n{body}"
        );
        let calls: Vec<_> = body
            .lines()
            .filter(|line| line.contains("call @func."))
            .collect();
        assert_eq!(calls.len(), 1, "one original remainder call:\n{body}");
        let (_, target) = calls[0].split_once("call @func.").expect("direct call");
        let (id, args) = target.split_once('(').expect("call arguments");
        assert!(
            args.starts_with(&format!("{slot})")),
            "actual argument is not its stored pointer:\n{body}"
        );
        let callee = functions[id.parse::<usize>().expect("canonical function id")];
        let (_, signature) = callee
            .lines()
            .next()
            .expect("callee header")
            .split_once("(functy.")
            .expect("callee signature");
        let signature = signature.split(')').next().expect("function type id");
        assert!(
            text.lines()
                .any(|line| line == format!("functy.{signature} = (ptr) -> (bool)")),
            "original callee must keep its real unary pointer ABI:\n{callee}"
        );
    }
    for name in [
        "mutable_receiver",
        "generic_receiver",
        "observe_address",
        "escape_local_snapshot",
    ] {
        let row = body_row(&coverage, name);
        assert_eq!(
            row["lowered"], false,
            "unsupported source snapshot was admitted: {row}"
        );
        assert_eq!(
            row["spliced"], false,
            "unsupported source snapshot was retained: {row}"
        );
        assert!(
            row["unsupported"]
                .as_array()
                .is_some_and(|rows| !rows.is_empty()),
            "refusal must remain disclosed: {row}"
        );
    }
}
