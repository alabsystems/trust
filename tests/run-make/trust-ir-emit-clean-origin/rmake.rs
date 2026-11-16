//! Trust (IR-1, docs/design/2026-08-27-two-language-direct-to-trust-ir.md §3):
//! the Clean-origin RECORDING PATH — under verification, `--emit=trust-ir` on a
//! crate holding both languages publishes ONE Module carrying BOTH producers'
//! rows, with the Clean rows tier-marked and the coverage sidecar disclosing
//! exactly what was recorded.
//!
//! Pins, per the review-amended design:
//!  * the capability/authority header is BYTE-EXACT `obligation-bearing-pending-v2`
//!    (the owner-signed tier move, c2ac761224; authority axes still false)
//!    / `proof_authority: false` / `native_verification_requests: false` — the
//!    pre-existing test pins containment only; a diff here is a soundness
//!    event, not a golden to re-bless;
//!  * the `clean_origin` coverage section records `cleanWsum` (wrapping-binop),
//!    `cleanSnd` (projection) and `cleanK32` (constant-uint) at tier `gate`,
//!    each with carrier-faithfulness and a digest-bound actual-Function subject;
//!  * the canonical text carries both languages' function names — the
//!    two-languages-one-module witness — and this fixture now also asserts the
//!    landed IR-5 same-crate edge repoint from Rust to the exact gated Clean
//!    FuncId. This is not G5 digest-bound cross-crate linking;
//!  * a called `Nat -> Nat` Clean definition pins the compiler-minted Rust ABI
//!    on its HIR-less Rust-callable declaration, while a called local
//!    `extern "C"` definition remains C — an exact-classifier mutation control;
//!  * under `-Ztrust-verify=off` the same crate records `"recorded": false`
//!    with the lane reason — a DISCLOSED absence, and no new fatal surface on
//!    the verification-off artifact lane;
//!  * plan step 3.4 (owner rulings D36/D37): every `gate` row's published
//!    Function carries `#body-gate: gated "clean-carrier-gate"` in the emitted
//!    module (before: `ungated`), its coverage row discloses the verdict's
//!    environment digest, kernel version and ledger digest and the codegen
//!    license it carries, and the Rust bodies of this Clean-island crate keep
//!    `gated "trust-direct-lane-structural"` (before: every body `ungated`,
//!    leg 4 withdrew the whole module); the general-lane row stays `ungated`.

use std::path::Path;

use run_make_support::object::{Object, ObjectSymbol};
use run_make_support::{rfs, rustc, serde_json};

const TRUST_NO_VERIFY_ENV: &str = "TRUST_NO_VERIFY";

/// The `#body-gate:` directive of the function whose header starts `rustcc fn @<name>(`, in a
/// canonical module text (`None`: no such function, or it makes no licensing claim). WS5.2:
/// `<name>` is the link-time symbol; callers find it by display path (`header_of`).
fn body_gate_of<'a>(text: &'a str, name: &str) -> Option<&'a str> {
    let header = format!("rustcc fn @{name}(");
    let mut lines = text.lines().skip_while(|line| !line.trim_start().starts_with(&header));
    lines.next()?;
    lines
        .take_while(|line| line.trim_start().starts_with(';'))
        .find_map(|line| line.trim_start().strip_prefix("; #body-gate: "))
}

/// WS5.2: the header line of the ONE function whose canonical-text block
/// displays `display_path`. `Function.name` is the link-time symbol; the def
/// path (or a Clean row's Lean spelling) is the `; #display-path:` directive.
fn header_of<'a>(text: &'a str, display_path: &str) -> &'a str {
    let directive = format!("; #display-path: {display_path:?}\n");
    let mut found = Vec::new();
    let mut offset = 0;
    for line in text.split_inclusive('\n') {
        if line.contains("fn @") {
            let block = &text[offset..];
            let block = &block[..block.find("\n}\n").map_or(block.len(), |end| end + 3)];
            if block.contains(&directive) {
                found.push(line.trim());
            }
        }
        offset += line.len();
    }
    assert_eq!(found.len(), 1, "one function displays `{display_path}`: {found:?}\n{text}");
    found[0]
}

/// The function NAME (link-time symbol) in a header line.
fn header_name(header: &str) -> &str {
    header
        .split_once("fn @")
        .and_then(|(_, tail)| tail.split_once('('))
        .map(|(name, _)| name)
        .expect("a function header")
}

fn main() {
    // ── verification ON: the recording path runs ────────────────────────────
    let on_dir = Path::new("emit-on");
    rfs::create_dir(&on_dir);
    rustc()
        .input("foo.rs")
        .crate_type("lib")
        .emit("trust-ir")
        .out_dir(&on_dir)
        .arg("-Ztrust-verify=on")
        // Bootstrap may deauthorize its own nested compiler processes through
        // this inherited override. A run-make recipe is a new policy boundary:
        // its explicit tracked flag must determine this subject compilation.
        .env_remove(TRUST_NO_VERIFY_ENV)
        .run();

    let coverage = rfs::read_to_string(on_dir.join("foo.trust-ir.coverage.json"));
    let coverage_json: serde_json::Value =
        serde_json::from_str(&coverage).expect("coverage sidecar must be valid JSON");
    // Capability header, byte-exact (the design's soundness-event pin).
    for exact in [
        "\"direct_obligation_capability\": \"obligation-bearing-pending-v2\",",
        "\"proof_authority\": false,",
        "\"native_verification_requests\": false,",
    ] {
        assert!(
            coverage.contains(exact),
            "capability header line missing or altered — a soundness event, not a golden \
             to re-bless. wanted byte-exact `{exact}` in:\n{coverage}"
        );
    }
    // The clean_origin section: recorded, with exactly the target row inspected
    // structurally rather than by unrelated substring presence.
    assert!(
        coverage.contains("\"recorded\": true"),
        "clean_origin section must record under verification:\n{coverage}"
    );
    let rows =
        coverage_json["clean_origin"]["emitted"].as_array().expect("clean_origin.emitted array");
    let clean_wsum = rows
        .iter()
        .find(|row| row["clean_name"] == "cleanWsum")
        .expect("cleanWsum must have one emitted row");
    assert_eq!(clean_wsum["shape"], "wrapping-binop");
    assert_eq!(clean_wsum["tier"], "gate");
    assert_eq!(clean_wsum["judgment"], "actual-TrustIR-Function-carrier-defeq");
    assert_eq!(clean_wsum["carrier_faithfulness"], "established");
    assert_eq!(clean_wsum["body_gate"], "carrier-faithful");
    assert_eq!(clean_wsum["gate_carrier"], "UInt64");
    assert_eq!(clean_wsum["gate_method"], "definitional-equality");
    assert!(
        clean_wsum["gate_subject_digest"]
            .as_str()
            .is_some_and(|digest| digest.starts_with("sha256:")),
        "gate row must bind the exact signature/Function by SHA-256: {clean_wsum}"
    );
    assert!(
        clean_wsum["gate_scope"]
            .as_str()
            .is_some_and(|scope| scope.contains("not G5 cross-crate") && scope.contains("not G7")),
        "gate scope must not overclaim completion: {clean_wsum}"
    );
    // W2 gate widening: projection and constant-uint rows publish at tier
    // `gate` with the same digest-bound, carrier-named evidence, and the
    // reflector's own shape reading is disclosed through the row's shape tag.
    for (name, shape, carrier) in
        [("cleanSnd", "projection", "UInt64"), ("cleanK32", "constant-uint", "UInt32")]
    {
        let row = rows
            .iter()
            .find(|row| row["clean_name"] == name)
            .unwrap_or_else(|| panic!("{name} must have one emitted row:\n{coverage}"));
        assert_eq!(row["shape"], shape, "{row}");
        assert_eq!(row["tier"], "gate", "{name} must publish at tier gate: {row}");
        assert_eq!(row["judgment"], "actual-TrustIR-Function-carrier-defeq");
        assert_eq!(row["carrier_faithfulness"], "established");
        assert_eq!(row["body_gate"], "carrier-faithful");
        assert_eq!(row["gate_carrier"], carrier);
        assert_eq!(row["gate_method"], "definitional-equality");
        assert!(
            row["gate_subject_digest"].as_str().is_some_and(|d| d.starts_with("sha256:")),
            "{name} gate row must bind the exact signature/Function by SHA-256: {row}"
        );
    }
    // Plan step 3.4 (design §4.2): every `gate` row discloses the verdict's environment, the
    // kernel version and the ledger digest beside the subject digest, and the license it carries.
    for name in ["cleanWsum", "cleanSnd", "cleanK32"] {
        let row = rows.iter().find(|row| row["clean_name"] == name).expect("row");
        let environment = row["gate_environment_digest"].as_str().unwrap_or_default();
        assert!(
            environment.len() == 64 && environment.bytes().all(|b| b.is_ascii_hexdigit()),
            "{name}: the environment digest is a SHA-256 hex: {row}"
        );
        assert!(row["gate_kernel_version"].as_str().is_some_and(|v| !v.is_empty()), "{row}");
        let ledger = row["gate_ledger_digest"].as_str().unwrap_or_default();
        assert!(ledger.starts_with("sha256:") && ledger != row["gate_subject_digest"], "{row}");
        assert_eq!(row["codegen_license"], "clean-carrier-gate", "{row}");
        assert!(
            row["codegen_license_scope"].as_str().is_some_and(|scope| {
                scope.contains("session ledger") && scope.contains("never a proof grade")
            }),
            "{name}: the license must state its scope: {row}"
        );
    }
    // IR-5: the caller's declared edge is re-pointed at the appended
    // definition, disclosed in the linked array.
    let linked =
        coverage_json["clean_origin"]["linked"].as_array().expect("clean_origin.linked array");
    let clean_wsum_link = linked
        .iter()
        .find(|row| row["def_path"] == clean_wsum["def_path"])
        .expect("cleanWsum same-crate link row");
    assert_eq!(clean_wsum_link["edges_repointed"], 1);
    assert!(
        clean_wsum_link["decl_func_id"].as_u64().is_some(),
        "the linked row must preserve the exact declaration identity: {clean_wsum_link}"
    );
    let source_def_index = clean_wsum_link["source_def_index"]
        .as_u64()
        .expect("the linked row must carry a numeric source_def_index");
    let emitted_def_index =
        clean_wsum["def_index"].as_u64().expect("the emitted row must carry a numeric def_index");
    assert_eq!(source_def_index, emitted_def_index);
    assert_eq!(clean_wsum_link["target_func_id"], clean_wsum["func_id"]);
    // WS5.2: the Rust declaration and the Clean definition of `m::cleanWsum` carry ONE
    // link-time symbol, so they are ONE row — the definition took the declaration's id.
    assert_eq!(clean_wsum_link["decl_func_id"], clean_wsum_link["target_func_id"]);
    assert!(clean_wsum_link["retired_declaration"].is_null(), "{clean_wsum_link}");
    // IR-5 TYPE binding: the edge is linked by TYPE as well as identity. An empty
    // `refusals` alone does not say that — the seam LINKS a position it could not
    // decide and discloses it here rather than refusing (a refusal at that seam is a
    // fatal finalization error). So a typed link is `type_unchecked` present AND empty,
    // and this is the end-to-end statement that the real program is typed at the seam
    // rather than merely arity-matched.
    let unchecked = clean_wsum_link["type_unchecked"]
        .as_array()
        .expect("the linked row must carry a type_unchecked array; absent is not a typed link");
    assert!(
        unchecked.is_empty(),
        "the cleanWsum edge must be fully type-checked at the seam, left {} undecided \
         position(s): {clean_wsum_link}",
        unchecked.len()
    );
    // The GENERAL lane (totality campaign): `triRank` is an inductive `match`
    // the 13-shape planner cannot spell — it must reach the module through
    // clean-compiler's general pipeline, at tier general, disclosed.
    assert!(
        coverage.contains("\"clean_name\": \"triRank\""),
        "the general-lane def must have a row:\n{coverage}"
    );
    assert!(
        coverage.contains("\"tier\": \"general\""),
        "general rows must carry their honest tier:\n{coverage}"
    );
    assert!(
        coverage.contains("\"disposition\": \"compiled\""),
        "triRank must actually compile through the general pipeline:\n{coverage}"
    );

    // Both languages' markers in ONE module's canonical text.
    let text = rfs::read_to_string(on_dir.join("foo.trust-ir.txt"));
    // Plan step 3.4: the stamps, in the module itself. Before: every body `ungated`.
    for name in ["cleanWsum", "cleanSnd", "cleanK32"] {
        assert_eq!(
            body_gate_of(&text, header_name(header_of(&text, name))),
            Some("gated \"clean-carrier-gate\""),
            "the `gate` row `{name}` carries the carrier stamp:\n{text}"
        );
    }
    for name in ["rust_half", "calls_clean"] {
        assert_eq!(
            body_gate_of(&text, header_name(header_of(&text, name))),
            Some("gated \"trust-direct-lane-structural\""),
            "the Rust body `{name}` keeps its license beside the Clean rows (D37):\n{text}"
        );
    }
    let carrier_stamps = text.matches("#body-gate: gated \"clean-carrier-gate\"").count();
    assert_eq!(carrier_stamps, 3, "exactly the three `gate` rows carry the stamp:\n{text}");
    assert!(text.contains("rust_half"), "the Rust producer's row is missing:\n{text}");
    assert!(text.contains("cleanWsum"), "the Clean producer's row is missing:\n{text}");
    assert!(text.contains("calls_clean"), "the Rust caller's row is missing:\n{text}");
    // WS5.2 (F-087/F-092): every row is NAMED by its link-time symbol and DISPLAYS its
    // def path (a Clean row: its Lean spelling). The Clean definition of the Rust item
    // `m::cleanWsum` is named by that item's symbol and carries rustcc; there is no
    // `local-unlowered` orphan and no `<shadowed-by-…>` name (a name that is no symbol).
    let clean_wsum_header = header_of(&text, "cleanWsum");
    assert!(
        clean_wsum_header.starts_with("rustcc fn @_R") && clean_wsum_header.contains("9cleanWsum"),
        "the Clean definition must be named by `m::cleanWsum`'s v0 symbol: {clean_wsum_header}"
    );
    assert!(!text.contains("<shadowed-by-"), "no synthetic symbol is minted:\n{text}");
    assert!(!text.contains("general::"), "the general:: rename is retired:\n{text}");
    let calls_clean_header = header_of(&text, "calls_clean");
    let rust_half_header = header_of(&text, "rust_half");

    // `name == nm symbol`: the native object the SAME source compiles to exports exactly
    // these names — the two languages link by symbol, not by display label.
    let native_dir = Path::new("native");
    rfs::create_dir(&native_dir);
    rustc()
        .input("foo.rs")
        .crate_type("lib")
        .emit("obj")
        .out_dir(&native_dir)
        .arg("-Ztrust-verify=on")
        .env_remove(TRUST_NO_VERIFY_ENV)
        .run();
    let object_bytes = rfs::read(native_dir.join("foo.o"));
    let object = run_make_support::object::File::parse(&*object_bytes).expect("native object");
    let native: Vec<String> =
        object.symbols().filter_map(|symbol| symbol.name().ok().map(str::to_string)).collect();
    for header in [clean_wsum_header, calls_clean_header, rust_half_header] {
        let name = header_name(header);
        assert!(
            native.iter().any(|symbol| symbol == name || symbol.strip_prefix('_') == Some(name)),
            "trust-ir name `{name}` must be a symbol of the native object: {native:?}"
        );
    }

    // The CRATE-ROOT shape of the same rule — where the declaration's `def_path`
    // and the Clean name are ONE string, and the unretired orphan made the
    // producer boundary refuse the whole module as `DuplicateFunctionName` — has
    // its own recipe: `tests/run-make/trust-ir-clean-origin-crate-root`.
    //
    // ── the ABI probe, and the OWNED-SEQUENCE CARRIER it now also pins ───────
    //
    // This companion keeps the locked Clean corpus population stable while
    // permanently exercising the ABI seam with a `repr(Rust)` carrier. Its
    // `Nat` argument ALSO pins the seq-carrier lane, so read the two together.
    //
    // HISTORY, retired here (it was recorded as "KNOWN RED, PRE-EXISTING",
    // measured 2026-09-12 on the sealed packs `b8f4d9ec8` and `f558ea288`):
    // `calls_clean_nat` used to fail strict verification outright —
    //
    //   error: Trust full verification failed for `abi_probe::calls_clean_nat`:
    //          native typed-TrustIr lowering did not complete, so the
    //          panic-freedom of an unmodeled construct could not be established
    //   note: ... unsupported type: Seq { elem: Int { width: 64, signed: false } }
    //
    // — and the note read as if it were about Clean-origin recording. It was
    // not, and it was not narrow either: `trust_bignum::Nat`'s carrier is
    // `Vec<u64>`, `trust-mir-extract` spells every `Vec<T>` as
    // `trust_types::Ty::Seq { elem }`, and `trust-ir-bridge`'s `map_type_ctx`
    // had NO arm for it — so EVERY function whose signature mentioned a `Vec`
    // died at that wall. Measured on `f558ea288`, so did the one-liner
    // `pub fn id_vec(v: Vec<u64>) -> Vec<u64> { v }`.
    //
    // The lane now spells it with the FORMAT'S OWN first-class type,
    // `Ty::Sequence(elem TyId)` — trust-ir's "ordered variable-length sequence
    // of elements of type T", which is exactly what `Ty::Seq` means — so the
    // element identity crosses the boundary instead of being dropped. It claims
    // no layout: `Sequence` has no `bit_width`, trust-mc sorts it as the same
    // uninterpreted placeholder every other compound type gets, and every
    // structural walk over it (field, index, deref) still fails closed.
    //
    // THE CONTROL IS BELOW, and it is what makes this positive half mean
    // something. `seq_carrier_control.rs` carries the SAME `Vec<u64>` parameter
    // shape plus one genuine unproved overflow obligation, and it must still be
    // REFUSED. Removing the carriage turns THIS half red with the lowering error
    // quoted above; making the carriage fail-open — a vacuous "anything holding
    // a Vec passes" — turns the CONTROL half red. Neither can hide behind the
    // other.
    rfs::write(
        "abi_probe.rs",
        r#"
extern crate trust_bignum;

mod abi_m {
    clean {
        def abiNatId (n : Nat) : Nat := n
    }
}

pub fn calls_clean_nat(x: trust_bignum::Nat) -> trust_bignum::Nat {
    abi_m::abiNatId(x)
}

pub extern "C" fn trust_scalar_c_abi<const N: u64>(x: u64) -> u64 {
    let _ignored = N;
    x
}

pub fn calls_c_abi(x: u64) -> u64 {
    trust_scalar_c_abi::<1>(x)
}

// The seq-carrier lane in its most general form: a bare `Vec<T>` with no Clean,
// no ABI seam and no `Nat` anywhere near it. Panic-free by inspection (a move),
// so it must verify — and it is the half that reads the lowering error first if
// the `Ty::Seq -> Ty::Sequence(elem)` arm is ever removed.
pub fn id_vec(v: Vec<u64>) -> Vec<u64> {
    v
}
"#,
    );
    let abi_dir = Path::new("abi-probe");
    rfs::create_dir(&abi_dir);
    rustc()
        .input("abi_probe.rs")
        .crate_type("lib")
        .emit("trust-ir")
        .out_dir(&abi_dir)
        .arg("-Ztrust-verify=on")
        // Trust: abi_probe asserts ABI LABELING in the emitted trust-ir text, not
        // a verdict. `calls_clean_nat` calls a Clean `Nat` function, and Nat is an
        // unmodeled construct for the direct producer, so its Level 0 panic-freedom
        // obligation cannot be discharged and STRICT policy fail-closes before the
        // artifact is written. Advisory keeps the recording path (and verification)
        // ON while reporting the unproved obligation without fatal credit, so the
        // labeling artifact this test inspects is produced. The scalar UInt64 Clean
        // call in foo.rs above stays on the default strict policy and still proves.
        .arg("-Ztrust-policy=advisory")
        .env_remove(TRUST_NO_VERIFY_ENV)
        .run();
    let abi_text = rfs::read_to_string(abi_dir.join("abi_probe.trust-ir.txt"));

    // The Rust-callable Clean-origin signature is installed by the compiler as
    // Rust ABI even though its synthetic DefId has no HIR fn item. Nat is
    // repr(Rust), so a C label on this row makes final validation fail closed.
    // The general-lane `abiNatId` pointer-runtime row is separate, claim-free,
    // and explicitly not callable from Rust; `cleanWsum` above already pins the
    // planner lane's appended Rust-callable definition as `rustcc`.
    // WS5.2: named by the Rust item's link-time symbol, def path as display path.
    let nat_declaration = header_of(&abi_text, "abi_m::abiNatId");
    assert!(
        nat_declaration.starts_with("rustcc fn @_R"),
        "the HIR-less Clean-origin declaration must carry rustcc: {nat_declaration}\n{abi_text}"
    );
    let nat_struct = abi_text
        .lines()
        // WS4.3: a struct name with `::` is outside the bare alphabet -> quoted.
        .find(|line| line.starts_with("struct @\"trust_bignum::Nat\" { "))
        .expect("the Nat carrier struct must be present in canonical TrustIR");
    assert!(
        !nat_struct.contains("repr="),
        "Nat must retain canonical default repr(Rust), not acquire an FFI representation: \
         {nat_struct}"
    );

    // The const generic deliberately keeps this called local callee symbolic:
    // it traverses the same bodyless-declaration classifier as the HIR-less
    // Clean row. The registry exception must be exact, not a blanket rule for
    // called local callees. Canonical C has no convention prefix.
    // RESIDUAL (WS5.2 NARROWED, docs/DECISION_QUEUE.md D17-DECL-SYMBOL-1): the `::<1>`
    // instance is a generic instance of a local fn — the shape the frozen D17 instance lane
    // appends — so its declaration keeps the PRE-WS5.2 name, the bare def path, with no
    // display path: the one place `Function.name` is not yet the link-time symbol.
    let c_abi = abi_text
        .lines()
        .map(str::trim_start)
        .find(|line| line.contains("fn @trust_scalar_c_abi("))
        .expect("the `trust_scalar_c_abi::<1>` declaration keeps its pre-WS5.2 name");
    assert!(
        c_abi.starts_with("fn @"),
        "the local extern-C callee must retain the canonical C convention: {c_abi}\n{abi_text}"
    );
    assert!(
        !c_abi.starts_with("rustcc "),
        "the Clean-origin ABI exception must not relabel a local extern-C callee: {c_abi}"
    );
    assert!(
        !abi_text.contains("; #display-path: \"trust_scalar_c_abi\""),
        "the carved-out declaration carries no display path:\n{abi_text}"
    );

    // ── the seq-carrier CONTROL: the lane still REFUSES a real obligation ───
    //
    // Same `Vec<u64>` parameter shape as `id_vec` above, so it travels the exact
    // same `Ty::Seq -> Ty::Sequence(elem)` carriage — plus one genuine, unproved
    // `u64` overflow. The carriage must let the body LOWER and must not let it
    // PASS: a `Sequence` is transport, never evidence.
    //
    // WHY THE TWO `not_contains` LINES CARRY THE CONTROL, measured rather than
    // assumed: run this exact source through the PRE-CHANGE compiler — the
    // sealed pack `f558ea288`, which has no `Ty::Seq` arm — and it exits 1 with
    // `0 proved, 1 failed, ... 1 skipped out of 2`, its stderr carrying BOTH
    // `[overflow:add] FAILED` AND `native typed-TrustIr lowering did not
    // complete` / `unsupported type: Seq { elem: Int { width: 64, signed: false
    // } }`. So `run_fail()` plus the two `contains` lines alone would pass on
    // the un-fixed compiler: the control would be green for the very reason the
    // lane exists to remove. The `not_contains` pair is what makes it
    // discriminating, and it is the half to keep if this block is ever trimmed.
    // The opposite direction — a carriage that fail-OPENS — is caught by
    // `run_fail()` itself: `x + 1` would prove and the run would exit 0.
    rfs::write(
        "seq_carrier_control.rs",
        r#"
pub fn seq_param_with_real_obligation(_v: Vec<u64>, x: u64) -> u64 {
    x + 1
}
"#,
    );
    let control_dir = Path::new("seq-control");
    rfs::create_dir(&control_dir);
    let control = rustc()
        .input("seq_carrier_control.rs")
        .crate_type("lib")
        .emit("trust-ir")
        .out_dir(&control_dir)
        .arg("-Ztrust-verify=on")
        .env_remove(TRUST_NO_VERIFY_ENV)
        .run_fail();
    control.assert_stderr_contains("seq_carrier_control::seq_param_with_real_obligation");
    control.assert_stderr_contains("[overflow:add]");
    // The refusal must be the OBLIGATION, not the type wall: a `Vec` parameter
    // now lowers, so neither the lowering abort nor the `Seq` blocker may appear.
    control.assert_stderr_not_contains("native typed-TrustIr lowering did not complete");
    control.assert_stderr_not_contains("unsupported type: Seq");

    // ── verification OFF: no recording, DISCLOSED ───────────────────────────
    let off_dir = Path::new("emit-off");
    rfs::create_dir(&off_dir);
    rustc()
        .input("foo.rs")
        .crate_type("lib")
        .emit("trust-ir")
        .out_dir(&off_dir)
        .arg("-Ztrust-verify=off")
        .run();
    let coverage_off = rfs::read_to_string(off_dir.join("foo.trust-ir.coverage.json"));
    assert!(
        coverage_off.contains("\"recorded\": false"),
        "verification-off must disclose the absent recording:\n{coverage_off}"
    );
    assert!(
        !coverage_off.contains("\"clean_name\""),
        "verification-off must not record rows:\n{coverage_off}"
    );
    // Plan step 3.4: nothing recorded, so no row is stamped `clean-carrier-gate` (a stamp needs
    // its ledger entry, and no gate ran).
    let text_off = rfs::read_to_string(off_dir.join("foo.trust-ir.txt"));
    assert!(!text_off.contains("clean-carrier-gate"), "no gate ran, no stamp:\n{text_off}");
}

/// The recipe under libtest as well as compiletest (the frozen-file waiver cites it).
#[test]
fn the_gate_rows_are_stamped_and_the_rust_license_stands() {
    main();
}
