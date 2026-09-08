// Trust: the bridge's definition seam AGREES with trust-vcgen's, in the safe
// direction.
//
// `trust-ir-bridge` deliberately does not depend on `trust-vcgen` (its `Cargo.toml`
// spells out why: the dependency closure must stay cycle-free), so the two seams are
// two functions. What must hold is an IMPLICATION, not an equality: the bridge's
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
    serde_json::from_str(&json).expect("the synthetic body must deserialize")
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
        // reverse. (`Unlocatable` is declined by both. `Escape` is admitted by both,
        // in the count and in the resolver; in the resolver that is the open defect
        // named in `trust_vcgen::local_defs::body_unique_value_def`'s `Escape` arm,
        // and these rows are what keep the two seams carrying it identically until it
        // is repaired.)
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
    ]
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
