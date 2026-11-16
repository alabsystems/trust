// Trust: the bridge's definition seam AGREES with trust-vcgen's, in the safe
// direction.
//
// Both consumers now share the LocalWrite interpretation in trust-types; their
// traversal/caching remain separate, while escape classification is shared. What must hold is an
// IMPLICATION, not an equality: the bridge's
// native formula is credited only when it byte-matches what trust-vcgen built, so the
// bridge may be STRICTER — that loses a dispatch — and must never be LOOSER, which
// would let a native formula carry a fact trust-vcgen withheld.
//
// The bridge's seam never had a liveness relaxation and trust-vcgen's has been removed,
// so the two now AGREE on every shape the class is about. These rows measure both
// halves: the implication (the bridge is never looser) and the agreement (the
// implication is not vacuous).

use trust_types::VerifiableFunction;

const SPAN: &str = r#"{"file":"f.rs","line_start":1,"col_start":1,"line_end":1,"col_end":1}"#;
const USIZE: &str = r#"{"Int":{"width":64,"signed":false}}"#;

/// `fn f(_1: usize, _2: usize) -> usize` with `blocks_json` as its CFG. Locals `_0.._4`
/// are `usize`; `_1`/`_2` are PARAMETERS.
fn func(blocks_json: &str) -> VerifiableFunction {
    let locals = (0..5)
        .map(|i| format!(r#"{{"index":{i},"ty":{USIZE},"name":null}}"#))
        .collect::<Vec<_>>()
        .join(",");
    let json = format!(
        r#"{{"name":"f","def_path":"f","span":{SPAN},"body":{{"locals":[{locals}],
           "blocks":[{blocks_json}],"arg_count":2,"return_ty":{USIZE}}},"contracts":[]}}"#
    );
    let mut function: VerifiableFunction =
        serde_json::from_str(&json).expect("the synthetic body must deserialize");
    let mut borrows = Vec::new();
    for block in &mut function.body.blocks {
        for statement in &block.stmts {
            if let trust_types::Statement::Assign {
                place,
                rvalue: trust_types::Rvalue::Ref { mutable, place: source },
                ..
            } = statement
            {
                borrows.push((place.local, source.local, *mutable));
            }
        }
        if matches!(block.terminator, trust_types::Terminator::Return) {
            block.stmts.push(serde_json::from_str(&store(0)).expect("return assignment"));
        }
    }
    for (dest, source, mutable) in borrows {
        function.body.locals[dest].ty = trust_types::Ty::Ref {
            mutable,
            inner: Box::new(function.body.locals[source].ty.clone()),
        };
    }
    function
}

fn block(id: usize, stmts: &str, term: &str) -> String {
    format!(r#"{{"id":{id},"stmts":[{stmts}],"terminator":{term}}}"#)
}

fn store(dst: usize) -> String {
    format!(
        r#"{{"Assign":{{"place":{{"local":{dst},"projections":[]}},
           "rvalue":{{"Use":{{"Constant":{{"Uint":[7,64]}}}}}},"span":{SPAN}}}}}"#
    )
}

fn read(src: usize) -> String {
    format!(
        r#"{{"Assign":{{"place":{{"local":4,"projections":[]}},
           "rvalue":{{"Use":{{"Copy":{{"local":{src},"projections":[]}}}}}},"span":{SPAN}}}}}"#
    )
}

const RETURN: &str = r#""Return""#;

/// An inline-asm terminator: a write with NO destination `Place`, so no local can be
/// ruled out — the `LocalWrite::Unlocatable` channel.
fn opaque() -> String {
    format!(r#"{{"Opaque":{{"kind":"asm","targets":[],"span":{SPAN}}}}}"#)
}

/// `_4 = &mut _src` — the `LocalWrite::Escape` channel.
fn mut_borrow(src: usize) -> String {
    format!(
        r#"{{"Assign":{{"place":{{"local":4,"projections":[]}},
           "rvalue":{{"Ref":{{"mutable":true,"place":{{"local":{src},"projections":[]}}}}}},
           "span":{SPAN}}}}}"#
    )
}

/// `_4 = &_src` — NOT a write channel, and the control that keeps the escape rows from
/// passing because both seams refuse everything.
fn shared_borrow(src: usize) -> String {
    format!(
        r#"{{"Assign":{{"place":{{"local":4,"projections":[]}},
           "rvalue":{{"Ref":{{"mutable":false,"place":{{"local":{src},"projections":[]}}}}}},
           "span":{SPAN}}}}}"#
    )
}

fn call_to(dst: usize, target: usize) -> String {
    format!(
        r#"{{"Call":{{"func":"g","args":[],"dest":{{"local":{dst},"projections":[]}},
           "target":{target},"span":{SPAN},"atomic":null,"is_foreign":false,
           "is_unsafe_sig":false,"unwind":"Continue"}}}}"#
    )
}

/// Every shape the parameter-entry-definition class is about, plus the non-parameter
/// controls that must keep their single value.
fn corpus() -> Vec<(&'static str, VerifiableFunction, usize)> {
    vec![
        ("untouched parameter", func(&block(0, "", RETURN)), 1),
        ("read-only parameter", func(&block(0, &read(1), RETURN)), 1),
        (
            "live-entry parameter stored once",
            func(&block(0, &format!("{},{}", read(1), store(1)), RETURN)),
            1,
        ),
        (
            "parameter stored before any read",
            func(&block(0, &format!("{},{}", store(1), read(1)), RETURN)),
            1,
        ),
        (
            "parameter stored twice",
            func(&block(0, &format!("{},{}", store(1), store(1)), RETURN)),
            1,
        ),
        ("undefined temp", func(&block(0, "", RETURN)), 3),
        ("temp stored once", func(&block(0, &store(3), RETURN)), 3),
        ("temp stored twice", func(&block(0, &format!("{},{}", store(3), store(3)), RETURN)), 3),
        // The two channels that report a write the seam CANNOT SEE. Whatever each
        // question answers on them, the two SEAMS must answer it the SAME way — a
        // drift here is a fact the bridge inlines that trust-vcgen refused, or the
        // reverse. Unlocatable writes make the count inexact; Escape does not add a
        // counted value but does invalidate the unique-value resolver on both sides.
        ("temp reachable only by inline asm", func(&block(0, "", &opaque())), 3),
        ("temp stored once, plus inline asm", func(&block(0, &store(3), &opaque())), 3),
        (
            "temp stored once and mutably aliased",
            func(&block(0, &format!("{},{}", store(3), mut_borrow(3)), RETURN)),
            3,
        ),
        (
            "temp stored once and SHARED-borrowed",
            func(&block(0, &format!("{},{}", store(3), shared_borrow(3)), RETURN)),
            3,
        ),
        (
            "one call",
            func(&format!("{},{}", block(0, "", &call_to(3, 1)), block(1, "", RETURN))),
            3,
        ),
        (
            "parameter call",
            func(&format!("{},{}", block(0, "", &call_to(1, 1)), block(1, "", RETURN))),
            1,
        ),
        (
            "two calls",
            func(&format!(
                "{},{},{}",
                block(0, "", &call_to(3, 1)),
                block(1, "", &call_to(3, 2)),
                block(2, "", RETURN)
            )),
            3,
        ),
        (
            "store and call",
            func(&format!("{},{}", block(0, &store(3), &call_to(3, 1)), block(1, "", RETURN))),
            3,
        ),
        (
            "aliased call",
            func(&format!("{},{}", block(0, "", &call_to(3, 1)), block(1, &mut_borrow(3), RETURN))),
            3,
        ),
        (
            "unlocatable call",
            func(&format!("{},{}", block(0, "", &call_to(3, 1)), block(1, "", &opaque()))),
            3,
        ),
        (
            "partially invalidated call",
            func(&format!(
                "{},{}",
                block(0, "", &call_to(3, 1)),
                block(1, r#"{"Deinit":{"place":{"local":3,"projections":[]}}}"#, RETURN)
            )),
            3,
        ),
        (
            "tail call",
            func(&block(
                0,
                "",
                &format!(
                    r#"{{"TailCall":{{"func":"g","args":[],"span":{SPAN},"atomic":null,"is_foreign":false,"is_unsafe_sig":false}}}}"#
                ),
            )),
            0,
        ),
    ]
}

/// Fixed answers from the pre-extraction semantics prevent a shared regression
/// from passing merely because both consumers now call the same implementation.
#[test]
fn exact_answers_keep_the_pre_extraction_contract() {
    use trust_types::ValueCount::{AtLeast, Exactly};
    for (name, f, local) in corpus() {
        let (expected_count, expected_def, expected_call) = match name {
            "untouched parameter" | "read-only parameter" => (Exactly(1), false, false),
            "live-entry parameter stored once"
            | "parameter stored before any read"
            | "parameter call"
            | "temp stored twice"
            | "two calls"
            | "store and call" => (Exactly(2), false, false),
            "parameter stored twice" => (Exactly(3), false, false),
            "undefined temp" => (Exactly(0), false, false),
            "temp stored once" | "temp stored once and SHARED-borrowed" => {
                (Exactly(1), true, false)
            }
            "temp reachable only by inline asm" => (AtLeast(0), false, false),
            "temp stored once, plus inline asm" | "unlocatable call" => (AtLeast(1), false, false),
            "temp stored once and mutably aliased"
            | "aliased call"
            | "partially invalidated call"
            | "tail call" => (Exactly(1), false, false),
            "one call" => (Exactly(1), false, true),
            _ => panic!("missing expected answer for {name}"),
        };
        let (count, definition, call) = trust_ir_bridge::local_defs_exact_for_test(&f, local);
        assert_eq!(count, expected_count, "{name}");
        assert_eq!(definition.is_some(), expected_def, "{name}");
        assert_eq!(call.is_some(), expected_call, "{name}");
        assert_eq!(count, trust_vcgen::local_defs::value_count(&f, local), "{name}");
        match (definition, trust_vcgen::local_defs::unique_value_def(&f, local)) {
            (Some(a), Some(b)) => assert!(std::ptr::eq(a, b), "{name}: different defining rvalues"),
            (None, None) => {}
            _ => panic!("{name}: different definition answers"),
        }
        match (call, trust_vcgen::local_defs::unique_value_call(&f, local)) {
            (Some(a), Some(b)) => assert!(std::ptr::eq(a, b), "{name}: different defining calls"),
            (None, None) => {}
            _ => panic!("{name}: different call answers"),
        }
    }
}

fn interior_cell_fixture() -> VerifiableFunction {
    use trust_types::{AdtKind, Ty};
    let stamped = |name: &str, fields: Vec<(String, Ty)>| {
        let mut ty = Ty::adt(name, fields);
        if let Ty::Adt { adt_kind, .. } = &mut ty {
            *adt_kind = Some(AdtKind::Struct);
        }
        ty
    };
    let cell = stamped(
        "core::cell::Cell<usize>",
        vec![(
            "value".into(),
            stamped("core::cell::UnsafeCell<usize>", vec![("value".into(), Ty::usize())]),
        )],
    );
    let move_parameter = format!(
        r#"{{"Assign":{{"place":{{"local":3,"projections":[]}},
        "rvalue":{{"Use":{{"Move":{{"local":1,"projections":[]}}}}}},"span":{SPAN}}}}}"#
    );
    let mut f = func(&block(0, &format!("{move_parameter},{}", shared_borrow(3)), RETURN));
    f.body.locals[1].ty = cell.clone();
    f.body.locals[3].ty = cell.clone();
    f.body.locals[4].ty = Ty::Ref { mutable: false, inner: Box::new(cell) };
    f
}

/// A shared cell borrow invalidates the initializer in both consumers.
#[test]
fn shared_interior_mutability_invalidates_both_resolvers() {
    let f = interior_cell_fixture();
    let (count, definition, _) = trust_ir_bridge::local_defs_exact_for_test(&f, 3);
    assert_eq!(count, trust_types::ValueCount::Exactly(1));
    assert!(definition.is_none());
    assert!(trust_vcgen::local_defs::unique_value_def(&f, 3).is_none());
}

/// The bridge may withhold where trust-vcgen admits; it may never admit where
/// trust-vcgen withholds. Both seams are private to their crates, so the observable
/// face is the one predicate each exposes to its own callers — here reached through
/// the public `trust_vcgen::local_defs` module and the bridge's own reachable twin.
#[test]
fn bridge_seam_implies_the_vcgen_seam() {
    for (what, f, local) in corpus() {
        let vcgen = trust_vcgen::local_defs::holds_one_value(&f, local);
        let bridge = trust_ir_bridge::local_defs_holds_one_value_for_test(&f, local);
        assert!(
            !bridge || vcgen,
            "{what} (_{local}): the bridge admits a local trust-vcgen withholds — that is \
             the LOOSER direction and can carry a fact into a native formula that vcgen \
             refused"
        );
    }
}

/// The implication would hold vacuously if the bridge said `false` everywhere. Pin the
/// agreement AND that the corpus actually separates the two answers, so neither half is
/// a constant.
#[test]
fn the_two_seams_agree_on_every_shape() {
    let mut differ = Vec::new();
    let (mut any_true, mut any_false) = (false, false);
    for (what, f, local) in corpus() {
        let vcgen = trust_vcgen::local_defs::holds_one_value(&f, local);
        let bridge = trust_ir_bridge::local_defs_holds_one_value_for_test(&f, local);
        if vcgen != bridge {
            differ.push(what);
        }
        any_true |= bridge;
        any_false |= !bridge;
    }
    assert!(differ.is_empty(), "the two seams disagree on {differ:?}");
    assert!(any_true && any_false, "the corpus must separate the two answers, not be constant");
}

/// The same two directions for the RESOLVER. It is the face whose answer is INLINED,
/// so a bridge that resolves a local trust-vcgen declines bakes a value into a native
/// formula that trust-vcgen would not have built.
#[test]
fn the_two_seams_agree_on_the_resolver_too() {
    let mut differ = Vec::new();
    let (mut any_true, mut any_false) = (false, false);
    for (what, f, local) in corpus() {
        let vcgen = trust_vcgen::local_defs::unique_value_def(&f, local).is_some();
        let bridge = trust_ir_bridge::local_defs_unique_value_def_is_some_for_test(&f, local);
        assert!(!bridge || vcgen, "{what} (_{local}): the bridge resolves what vcgen declines");
        if vcgen != bridge {
            differ.push(what);
        }
        any_true |= bridge;
        any_false |= !bridge;
    }
    assert!(differ.is_empty(), "the two resolvers disagree on {differ:?}");
    assert!(any_true && any_false, "the corpus must separate the two answers, not be constant");
}
