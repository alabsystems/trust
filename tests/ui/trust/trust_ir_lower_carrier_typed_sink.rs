//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
// wave-CS (INVALID roots 4-6, full-population frontier): the opaque-carrier
// discipline's contract — a carrier's only consumers are opaque (a rebind,
// a discarding write, a summary HAVOC) — was never ENFORCED at the typed
// sinks. A read of a carrier local hands out the raw bound value: the
// SCRUTINEE (spelled at the scrutinee's mapped type) or a fresh `Ty::Unit`
// const. Flowing that into a position that DECLARES a different type
// emitted the measured INVALID family verbatim:
//   * dropck_legal_cycles — `if let Some(child) = children.0 { child }`
//     over an opaque-lane `Option<&T>`: `enum.0` into a `ptr` join param
//     (BranchArgTypeMismatch);
//   * let-else/issue-99975 — `let Some(content) = f() else { return .. };
//     content` returned: `enum.0` where `struct` is declared
//     (ReturnTypeMismatch);
//   * tracked-closure — a `Ty::Unit` carrier into a tuple-typed join
//     (BranchArgTypeMismatch).
// The producer now ledgers every carrier-bound value WITH its spelled type
// (`opaque_carrier_value_spellings`) and the typed sinks — value-producing
// join capture (`capture_arm`) and both `Return` sites — fail closed with
// a named tag on a spelling disagreement. A carrier whose spelling AGREES
// with the sink's declared type stays legal, and the untyped consumers
// (rebinds, discards) never consult the ledger.

pub struct Payload {
    pub tag: u64,
    pub blob: Vec<u8>,
}

fn source() -> Option<Payload> {
    None
}

// The issue-99975 shape: the opaque let-else binds `p` to the Option
// SCRUTINEE; returning THE CARRIER ITSELF where `Payload` is declared is
// the launder. Must DECLINE (`Return(opaque carrier typed sink)`), never
// emit an ill-typed `Return` — probe-verified: this file's module carries
// 0 validation errors while this body reports the tag.
pub fn launder_return(alt: Payload) -> Payload {
    let Some(p) = source() else {
        return alt;
    };
    p
}

// The dropck shape: an if-let VALUE whose then-arm value is the carrier
// read, joined against a differently-typed result param. Must DECLINE at
// the join capture (`Join(opaque carrier typed sink)`).
pub fn launder_join(o: Option<Payload>, alt: Payload) -> Payload {
    if let Some(p) = o { p } else { alt }
}

// Negative control: a carrier that is only REBOUND and DISCARDED never
// reaches a typed sink — the body must stay clear of both wave-CS tags
// (the untyped consumers are the sanctioned ones).
pub fn rebind_and_discard(o: Option<Payload>) -> u64 {
    if let Some(p) = o {
        let q = p;
        let _ = q;
        7
    } else {
        3
    }
}

fn main() {
    let _ = launder_return(Payload { tag: 2, blob: Vec::new() });
    let _ = launder_join(None, Payload { tag: 1, blob: Vec::new() });
    let _ = rebind_and_discard(None);
}
