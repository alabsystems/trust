use super::super::*;

fn id(krate: u64, index: u32, digest: [u64; 2]) -> trust_types::CalleeIdentity {
    trust_types::CalleeIdentity { stable_crate_id: krate, def_index: index, substs_digest: digest }
}

fn registry(items: &[trust_types::CalleeIdentity]) -> FxHashSet<trust_types::CalleeIdentity> {
    items.iter().copied().collect()
}

/// FALSE PROOF #14 AT THIS SEAM, and the general fail-closed law.
///
/// The forgery — a generic parameter named `u64`/`str`/`usize` — reaches this
/// gate with NO identity, because its call's arguments mention a `ty::Param`
/// and the extractor mints nothing for those. An absent identity is absence
/// of evidence and must admit nothing, no matter how full the registry is.
#[test]
fn an_unidentified_call_is_admitted_by_nothing() {
    let full = registry(&[id(1, 2, [3, 4]), id(0, 0, [0, 0])]);
    assert!(!identity_discharges_call(&full, None));
    // Including against the all-zero identity, which is a LEGITIMATE value
    // (it is whatever some empty-substs item hashes to) and must therefore
    // never double as a stand-in for "absent".
    assert!(!identity_discharges_call(&registry(&[id(0, 0, [0, 0])]), None));
}

/// An empty registry admits nothing, including a perfectly well-formed
/// identity: the premise set ranges over nothing (false proof #12's law).
#[test]
fn an_empty_registry_admits_nothing() {
    assert!(!identity_discharges_call(&registry(&[]), Some(&id(1, 2, [3, 4]))));
}

/// THE R43 DESYNC, reduced to the two facts that decide it.
///
/// MEASURED on deployed driver `342ac1c89edcc2d0` from a 60-line fixture
/// (`Parser<'a>` with `bump`/`skip_whitespace`, `TRUST_PF_REG_TRACE=1
/// TRUST_PF_MATCH_TRACE=1`), verbatim:
///
/// ```text
/// [PF_REG]      fn=CID::Parser::<'a>::bump established=true nrows=0
/// [PF_CALLGATE] fn=CID::Parser::<'a>::skip_whitespace UNREGISTERED callee
///               blocks discharge: CID::Parser::<'_>::bump
/// [PF_REG]      fn=CID::Parser::<'a>::skip_whitespace established=false nrows=1
/// ```
///
/// with the LIFETIME-FREE control in the same file discharging normally
/// (`[PF_ZEROGATE] fn=CID::Plain::skip arm=registry callee=CID::Plain::peek`
/// → `established=true nrows=0`). Identical shapes, one lifetime parameter of
/// difference.
///
/// The registration and the query are the SAME `DefId` with substs that
/// differ only in a region — rustc's own collector confirms it on the same
/// driver, emitting ONE mono item (`MONO_ITEM fn Parser::<'_>::bump`) for a
/// program that instantiates the struct at two different lifetimes. Region
/// erasure therefore makes the two digests equal by construction, which is
/// what this test pins: equal identity ⇒ admitted, and the moment anything
/// but the region differs ⇒ refused.
#[test]
fn the_lifetime_desync_closes_and_only_the_lifetime_desync() {
    // What `register_proven_panic_free` stores for `Parser::<'a>::bump`:
    // its `DefId` plus the digest of its REGION-ERASED identity args.
    let registered = id(0x00c1_d000_0000_0001, 17, [0xaaaa, 0xbbbb]);
    let registry = registry(&[registered]);
    // What the call site `Parser::<'_>::bump` carries: same `DefId`, and
    // substs that erase to the same thing because only the region differs.
    let queried_elided = id(0x00c1_d000_0000_0001, 17, [0xaaaa, 0xbbbb]);
    assert!(
        identity_discharges_call(&registry, Some(&queried_elided)),
        "`'a` and `'_` are one function; after region erasure they are one key"
    );
    // CONTROL: a call to the same item whose substs do NOT erase to the same
    // thing is a different monomorphization and stays refused. This is the
    // conjunct that keeps "the generic body verified" from being read as
    // "every instantiation is panic-free".
    let other_mono = id(0x00c1_d000_0000_0001, 17, [0xaaaa, 0xcccc]);
    assert!(!identity_discharges_call(&registry, Some(&other_mono)));
    // CONTROL: a sibling method on the same impl.
    assert!(!identity_discharges_call(
        &registry,
        Some(&id(0x00c1_d000_0000_0001, 18, [0xaaaa, 0xbbbb]))
    ));
}

/// EVERY component discriminates. A neighbour that differs in exactly one
/// field is a DIFFERENT function (or a different monomorphization) and may
/// not ride the grant: same crate + same index but different substs is the
/// `f::<u32>` / `f::<[u8; 1<<40]>` split that a rendered path once erased.
#[test]
fn each_component_discriminates() {
    let granted = id(0xdead_beef, 42, [7, 9]);
    let reg = registry(&[granted]);
    assert!(identity_discharges_call(&reg, Some(&granted)));
    for impostor in [
        id(0xdead_beee, 42, [7, 9]),  // different crate
        id(0xdead_beef, 43, [7, 9]),  // different item
        id(0xdead_beef, 42, [7, 10]), // different substs (high half)
        id(0xdead_beef, 42, [8, 9]),  // different substs (low half)
        id(0xdead_beef, 42, [9, 7]),  // halves transposed
        id(0xdead_beef, 42, [0, 0]),  // "empty" substs
    ] {
        assert!(
            !identity_discharges_call(&reg, Some(&impostor)),
            "a one-field-different identity must not ride the grant: {impostor:?}"
        );
    }
}

// -----------------------------------------------------------------------
// R45 — the SAME gate, now at the seam that decides `arm=NONE`
// (`all_callee_keys_registry_or_bridge_total`). The tests above pin the pure
// predicate; these pin that the ZERO-OBLIGATION arm list actually consults it,
// and that nothing else about that arm list moved.
// -----------------------------------------------------------------------

/// The empty string registries, so a `true` from the arm list under these can
/// only have come from the identity arm.
fn no_string_arms() -> FxHashSet<String> {
    FxHashSet::default()
}

fn decide(
    proven: &FxHashSet<String>,
    proven_identities: &FxHashSet<trust_types::CalleeIdentity>,
    callees: &[(&str, Option<&trust_types::CalleeIdentity>)],
) -> bool {
    all_callee_keys_registry_or_bridge_total(
        proven,
        proven_identities,
        &no_string_arms(),
        &no_string_arms(),
        &no_string_arms(),
        &no_string_arms(),
        &no_string_arms(),
        &no_string_arms(),
        "test::caller",
        callees,
        false,
    )
}

/// THE ANTI-FORGERY PIN, at the deciding seam.
///
/// A call carrying NO identity must not be discharged by the identity arm even
/// when an entry with its EXACT rendered name sits in the proven-identity
/// registry. This is false proof #14's shape: the forgery
/// (`fn attack<u64: TryFrom<u32>>`) renders byte-identically to the honest
/// callee and arrives with `callee_identity: None`, because its arguments
/// mention a `ty::Param`. The name must buy it nothing HERE — the string arms
/// are empty in this fixture, so a `true` could only mean the gate answered an
/// absent identity by looking at the spelling.
#[test]
fn an_unidentified_call_is_not_discharged_by_a_same_named_proven_identity() {
    let honest = id(0x00c1_d000_0000_0001, 17, [0xaaaa, 0xbbbb]);
    let identities = registry(&[honest]);
    assert!(
        !decide(&no_string_arms(), &identities, &[("krate::honest", None)]),
        "an absent identity must admit nothing, whatever the call renders as"
    );
    // And the identical call WITH the authenticated identity does discharge —
    // so the refusal above is the missing identity, not a dead arm.
    assert!(decide(&no_string_arms(), &identities, &[("krate::honest", Some(&honest))]));
}

/// THE R43 DESYNC, closed at the seam that was still deciding it on a string.
///
/// The registration renders `Parser::<'a>::peek` and the call site renders
/// `Parser::<'_>::peek`, so the NAME is absent from `proven` — this is verbatim
/// the measured ny-cert blocker. The identity is present, and that is what the
/// arm list must decide on.
#[test]
fn an_identified_call_discharges_with_its_name_absent_from_the_string_registry() {
    let peek = id(0x00c1_d000_0000_0001, 17, [0xaaaa, 0xbbbb]);
    // The string registry holds the DECLARED-lifetime spelling only.
    let proven: FxHashSet<String> =
        ["ny_cert::json::Parser::<'a>::peek".to_string()].into_iter().collect();
    let identities = registry(&[peek]);
    // Control: the ELIDED-lifetime call key really does miss every string arm.
    assert!(
        !decide(&proven, &FxHashSet::default(), &[("ny_cert::json::Parser::<'_>::peek", None)]),
        "the string arms must still miss — otherwise this fixture proves nothing"
    );
    assert!(
        decide(&proven, &identities, &[("ny_cert::json::Parser::<'_>::peek", Some(&peek))],),
        "the identity arm must discharge a call whose NAME is absent from `proven`"
    );
}

/// Identity grants are additive over the separately authenticated arms. The
/// ordinary display mirror grants nothing; one undischargeable callee anywhere
/// still refuses the whole function, while its authenticated positive passes.
#[test]
fn the_identity_arm_is_strictly_additive_and_one_bad_callee_still_refuses() {
    let known = id(1, 2, [3, 4]);
    let identities = registry(&[known]);
    let proven: FxHashSet<String> = ["krate::named".to_string()].into_iter().collect();
    // A rendered name cannot replace an absent authenticated registry identity.
    assert!(!decide(&proven, &FxHashSet::default(), &[("krate::named", Some(&known))]));
    assert!(!decide(&proven, &identities, &[("krate::named", None)]));
    assert!(!decide(&proven, &identities, &[("krate::named", Some(&id(1, 3, [3, 4])))]));
    assert!(decide(&proven, &identities, &[("krate::named", Some(&known))]));
    assert!(!decide(&proven, &FxHashSet::default(), &[("krate::other", Some(&known))]));
    // A discharged callee does not license an UNdischarged sibling.
    assert!(!decide(
        &proven,
        &identities,
        &[("krate::named", Some(&known)), ("krate::stranger", None)],
    ));
    assert!(!decide(
        &proven,
        &identities,
        &[("krate::stranger", Some(&id(9, 9, [9, 9]))), ("krate::named", Some(&known))],
    ));
    // No calls at all is vacuously true, unchanged.
    assert!(decide(&no_string_arms(), &FxHashSet::default(), &[]));
}
