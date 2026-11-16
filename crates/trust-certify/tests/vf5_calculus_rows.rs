// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VF5: `trust_certify::calculus_row` over the REAL VF5 family, on compiled
//! rows (Clean `docs/DECISIONS.md` R169, R170; the aterm rows of the entry that
//! added them).
//!
//! The family is not in this tree's pinned `first-party/clean`, so the test
//! reads it from outside: `TRUST_VF5_FAMILY_OLEANS` names a directory holding
//! the family's `.olean` files as the pinned Lean (v4.30.0-rc2) compiled them
//! from a Clean checkout that carries the family (the producer's
//! `target/vf5-producer`, with `VF5Rows` compiled beside the hand-written
//! modules), and `TRUST_VF5_ROWS` a TSV of rows:
//! `<blob path>\t<fid>\t<symbol>\t<what>`, every row of one artifact whose
//! certificates `VF5Rows.certs_aterm` are. Without both the test is a named
//! skip (it prints why and passes vacuously, never claiming a check).
//!
//! What it shows: the reference entry, built from EMPTY over the family's
//! hand-written cone (`VF5Enum` and below; no generated row module), admits
//! `RowProved` judgments that `certify_calculus_row` builds from the compiled
//! artifact's own bytes and each function's own symbol; and it refuses the
//! same judgment at another row's symbol, on an artifact SemR does not decode,
//! and with the certificates of another artifact; and the recorded certificate
//! is returned for its own symbol over its own bytes only. The environment
//! digest the production pin would name is printed. The base is admitted
//! through `test_support::pin_own_digest` (a pin of its own digest), not a
//! production pin: `PINNED_VF5_ENV_DIGESTS` is empty.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::time::Instant;

use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr};
use clean_olean::recheck_closed::ClosedRecheckOptions;
use clean_olean::{load_module_with_deps, parse_module, reference_base_closed};
use trust_certify::calculus_row::{
    self, CalculusRowClaim, CalculusRowMiss, certify_calculus_row, test_support,
};

/// The family's hand-written modules (Clean's `vf5_f1/ORDER` up to the
/// generated ones), the theory first.
const BASE_MODULES: &[&str] = &[
    "ChkLIA",
    "SemR",
    "VF5Sem",
    "VF5Calc",
    "VF5Lemmas",
    "VF5Ops",
    "VF5Bin",
    "VF5Cmp",
    "VF5Ovf",
    "VF5Env",
    "VF5Step",
    "VF5Call",
    "VF5Frame",
    "VF5Sound",
    "VF5Compose",
    "VF5Check",
    "VF5Mutants",
    "VF5Enum",
];

struct Row {
    blob: PathBuf,
    fid: u64,
    symbol: Vec<u8>,
    what: String,
}

fn rows(path: &Path) -> Vec<Row> {
    std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
        .lines()
        .filter(|line| !line.trim().is_empty() && !line.starts_with('#'))
        .map(|line| {
            let fields: Vec<&str> = line.split('\t').collect();
            let [blob, fid, symbol, what] = fields[..] else {
                panic!("{}: a row is `blob\\tfid\\tsymbol\\twhat`: {line}", path.display())
            };
            let blob = if Path::new(blob).is_absolute() {
                PathBuf::from(blob)
            } else {
                path.parent().expect("a TSV has a directory").join(blob)
            };
            Row {
                blob,
                fid: fid.parse().expect("a fid"),
                symbol: symbol.as_bytes().to_vec(),
                what: what.to_string(),
            }
        })
        .collect()
}

/// The kernel declarations a compiled module makes, read off its own `.olean`.
fn declared(dir: &Path, module: &str) -> Vec<Name> {
    let path = dir.join(format!("{module}.olean"));
    let bytes = std::fs::read(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    let parsed = parse_module(&bytes).unwrap_or_else(|e| panic!("parse {}: {e}", path.display()));
    parsed
        .constants
        .iter()
        .filter(|c| !c.name.ends_with("._unsafe_rec"))
        .map(|c| Name::from_string(&c.name))
        .collect()
}

/// `@Eq Bool (checkBlob bs A cs) true` → (`A`, `cs`) as the statement writes them.
fn annotation_and_certs(env: &Environment, checks: &str) -> (Expr, Expr) {
    let ty = env
        .get_const(&Name::from_string(checks))
        .unwrap_or_else(|| panic!("{checks} is declared"))
        .type_
        .clone();
    let args = ty.get_app_args();
    let [_, lhs, _] = args.as_slice() else { panic!("{checks} is `@Eq _ lhs rhs`") };
    let inner = lhs.get_app_args();
    let [_, annotation, certs] = inner.as_slice() else {
        panic!("{checks}'s lhs is `checkBlob bs A cs`")
    };
    ((*annotation).clone(), (*certs).clone())
}

#[test]
fn compiled_calculus_rows_are_certified_through_the_reference_entry() {
    let (Some(dir), Some(table)) =
        (std::env::var_os("TRUST_VF5_FAMILY_OLEANS"), std::env::var_os("TRUST_VF5_ROWS"))
    else {
        eprintln!(
            "vf5_calculus_rows: NOT RUN (set TRUST_VF5_FAMILY_OLEANS and TRUST_VF5_ROWS; the VF5 \
             family is not in this tree's pinned first-party/clean)"
        );
        return;
    };
    let dir = PathBuf::from(dir);
    let rows = rows(Path::new(&table));
    assert!(rows.len() >= 3, "at least three rows: {}", rows.len());
    let lib = clean_olean::require_pinned_lean_lib_path().expect("the pinned Lean library");

    let mut full = Environment::for_lean_replay();
    load_module_with_deps(&mut full, "VF5Rows", &[dir.clone(), lib.clone()])
        .unwrap_or_else(|e| panic!("load VF5Rows: {e}"));
    // The annotation as `checks_aterm` states it (`annot []`, over the base's
    // constants); the certificates are `certs_aterm`'s VALUE, a closed literal
    // (the generated module is not in the base), as the producer would hand it
    // over.
    let (annotation, _) = annotation_and_certs(&full, "VF5Rows.checks_aterm");
    let certs = value(&full, "VF5Rows.certs_aterm");
    let other_certs = value(&full, "VF5Rows.certs_collision");

    let mut base_env = Environment::for_lean_replay();
    load_module_with_deps(&mut base_env, "VF5Enum", &[dir.clone(), lib])
        .unwrap_or_else(|e| panic!("load VF5Enum: {e}"));
    let names: BTreeSet<Name> =
        BASE_MODULES.iter().flat_map(|module| declared(&dir, module)).collect();
    let started = Instant::now();
    let built = reference_base_closed(&base_env, &names, &ClosedRecheckOptions::default())
        .expect("the base starts");
    assert!(built.report.passed(), "replay: {}", built.report.verdict_sentence());
    assert!(built.entry_refusals.is_empty(), "entry refusals: {:?}", built.entry_refusals);
    let kernel = built.into_kernel().expect("a passing replay");
    eprintln!(
        "vf5_calculus_rows: the VF5 base ({} declared constants) through the entry in {:.1?}; env \
         digest {}",
        names.len(),
        started.elapsed(),
        hex(&kernel.env_digest().0)
    );
    let reference = test_support::pin_own_digest(kernel).expect("the family base is admitted");

    let artifact = std::fs::read(&rows[0].blob).expect("the artifact");
    for row in &rows {
        assert_eq!(std::fs::read(&row.blob).expect("blob"), artifact, "one artifact");
        let claim = CalculusRowClaim {
            artifact: artifact.clone(),
            fid: row.fid,
            symbol: row.symbol.clone(),
        };
        let t = Instant::now();
        let certificate = certify_calculus_row(&reference, &claim, &annotation, &certs)
            .unwrap_or_else(|miss| panic!("{}: {miss:?}", row.what));
        assert!(certificate.binds_symbol(&row.symbol));
        assert_eq!(certificate.fid(), row.fid);
        eprintln!(
            "vf5_calculus_rows: CERTIFIED {} (fid {}, {}) in {:.0} ms; decl digest {}",
            row.what,
            row.fid,
            String::from_utf8_lossy(&row.symbol),
            t.elapsed().as_secs_f64() * 1e3,
            hex(&certificate.reference().decl_digest())
        );
    }

    // Negative controls, each beside the accepted rows above.
    let first = &rows[0];
    let second = &rows[1];
    let refused = |claim: CalculusRowClaim, certs: &Expr, what: &str| {
        let miss = certify_calculus_row(&reference, &claim, &annotation, certs);
        assert!(matches!(miss, Err(CalculusRowMiss::Refused(_))), "{what}: {miss:?}");
        eprintln!("vf5_calculus_rows: REFUSED {what}");
    };
    refused(
        CalculusRowClaim {
            artifact: artifact.clone(),
            fid: first.fid,
            symbol: second.symbol.clone(),
        },
        &certs,
        "a row at another function's symbol",
    );
    let mut truncated = artifact.clone();
    truncated.pop();
    refused(
        CalculusRowClaim { artifact: truncated, fid: first.fid, symbol: first.symbol.clone() },
        &certs,
        "the artifact with its last byte dropped (SemR does not decode it)",
    );
    // A byte the semantics does not read (one in the middle of the artifact's
    // metadata) may still certify: the judgment is then about the changed
    // bytes, and the certificate names THEIR digest, never the original's.
    let original = certify_calculus_row(
        &reference,
        &CalculusRowClaim {
            artifact: artifact.clone(),
            fid: first.fid,
            symbol: first.symbol.clone(),
        },
        &annotation,
        &certs,
    )
    .expect("the original row");
    let mut flipped = artifact.clone();
    let at = flipped.len() / 2;
    flipped[at] ^= 0x01;
    // What the compiler mints from: the recorded certificate, only for its own
    // symbol over its own artifact bytes; the changed bytes get none of it.
    calculus_row::register(original.clone());
    assert_eq!(
        calculus_row::calculus_row_certificate_bound(&first.symbol, &artifact),
        Some(original.clone())
    );
    assert_eq!(calculus_row::calculus_row_certificate_bound(&first.symbol, &flipped), None);
    assert_eq!(calculus_row::calculus_row_certificate_bound(&second.symbol, &artifact), None);
    if let Ok(other) = certify_calculus_row(
        &reference,
        &CalculusRowClaim { artifact: flipped, fid: first.fid, symbol: first.symbol.clone() },
        &annotation,
        &certs,
    ) {
        assert_ne!(other.artifact_sha256(), original.artifact_sha256());
        assert_ne!(other.reference().decl_digest(), original.reference().decl_digest());
        eprintln!(
            "vf5_calculus_rows: byte {at} changed still certifies, as a judgment about the changed \
             artifact only (another artifact digest and declaration digest)"
        );
    }
    refused(
        CalculusRowClaim {
            artifact: artifact.clone(),
            fid: first.fid,
            symbol: first.symbol.clone(),
        },
        &other_certs,
        "another artifact's certificates",
    );
}

fn value(env: &Environment, name: &str) -> Expr {
    env.get_const(&Name::from_string(name))
        .and_then(|c| c.value.clone())
        .unwrap_or_else(|| panic!("{name} has a value"))
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}
