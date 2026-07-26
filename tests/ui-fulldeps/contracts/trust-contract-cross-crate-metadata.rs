//@ run-pass
//@ run-flags: --sysroot {{sysroot-base}}
//@ ignore-stage1 (requires matching sysroot built with in-tree compiler)
//@ ignore-cross-compile
//@ ignore-remote
//@ edition: 2021

#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;

use std::path::{Path, PathBuf};

use rustc_driver::Compilation;
use rustc_hir::def::DefKind;
use rustc_interface::interface;
use rustc_interface::interface::Compiler;
use rustc_middle::mir::trust_contract::{
    TrustContractKind, TrustContractPayloadType, TrustContractPredicateKind, TrustContractSource,
    TrustContractSubject, TrustContractVerifierSort,
};
use rustc_middle::ty::TyCtxt;

const UPSTREAM: &str = "trust_contract_metadata_upstream";
const DOWNSTREAM: &str = "trust_contract_metadata_downstream";
const CONTRACTED_FN: &str = "requires_and_ensures";
const BOOL_LITERAL_FN: &str = "bool_literal_contracts";
const UNSUPPORTED_ENSURES_FN: &str = "unsupported_ensures_shape";
const DECREASES_FN: &str = "native_decreases_measure";
const LOWERED_COMPILER_CONTRACT_PREFIX: &str = "__trust_lowered_compiler_contract__:";

struct NoopCallbacks;

impl rustc_driver::Callbacks for NoopCallbacks {}

struct MetadataCallbacks;

impl rustc_driver::Callbacks for MetadataCallbacks {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        tcx.sess.dcx().abort_if_errors();

        let upstream = tcx
            .crates(())
            .iter()
            .copied()
            .find(|&cnum| tcx.crate_name(cnum).as_str() == UPSTREAM)
            .expect("downstream crate did not load the upstream contract crate");

        let contracted_fn = tcx
            .module_children(upstream.as_def_id())
            .iter()
            .find(|child| child.ident.name.as_str() == CONTRACTED_FN)
            .expect("upstream function is missing from module metadata")
            .res
            .opt_def_id()
            .expect("upstream function child did not resolve to a DefId");

        assert_eq!(tcx.def_kind(contracted_fn), DefKind::Fn);

        let contracts = tcx.trust_contracts(contracted_fn);
        assert_eq!(contracts.def_id, contracted_fn);
        assert!(!contracts.is_empty(), "upstream Trust contracts decoded as an empty bundle");
        assert_eq!(contracts.contracts.len(), 2);
        assert_eq!(contracts.summary.total, 2);
        assert_eq!(contracts.summary.requires, 1);
        assert_eq!(contracts.summary.ensures, 1);
        assert_eq!(contracts.summary.invariants, 0);
        assert_eq!(contracts.summary.assertions, 0);
        assert_eq!(contracts.summary.opaque, 0);

        let mut saw_requires = false;
        let mut saw_ensures = false;
        for contract in contracts.contracts.iter() {
            assert_eq!(contract.source, TrustContractSource::Attribute);
            assert_eq!(contract.subject, TrustContractSubject::Function);
            assert_eq!(contract.predicate.ty, tcx.types.bool);

            match contract.kind {
                TrustContractKind::Requires => {
                    saw_requires = true;
                    match &contract.predicate.kind {
                        TrustContractPredicateKind::Opaque { text }
                        | TrustContractPredicateKind::Typed { text, .. } => {
                            assert!(
                                text.as_str().starts_with(LOWERED_COMPILER_CONTRACT_PREFIX),
                                "requires predicate was not marked as compiler-lowered: {text}"
                            );
                            assert!(
                                text.as_str().ends_with("(x) > (0)"),
                                "unexpected lowered requires predicate: {text}"
                            );
                        }
                        other => panic!("unexpected requires Trust contract predicate: {other:?}"),
                    }
                }
                TrustContractKind::Ensures => {
                    saw_ensures = true;
                    match &contract.predicate.kind {
                        TrustContractPredicateKind::Opaque { text }
                        | TrustContractPredicateKind::Typed { text, .. } => {
                            assert!(
                                text.as_str().starts_with(LOWERED_COMPILER_CONTRACT_PREFIX),
                                "ensures predicate was not marked as compiler-lowered: {text}"
                            );
                            assert!(
                                text.as_str().ends_with("(result) > (0)"),
                                "unexpected lowered ensures predicate: {text}"
                            );
                        }
                        other => panic!("unexpected ensures Trust contract predicate: {other:?}"),
                    }
                }
                other => panic!("unexpected upstream Trust contract kind: {other:?}"),
            }
        }

        assert!(saw_requires);
        assert!(saw_ensures);

        let bool_literal_fn = tcx
            .module_children(upstream.as_def_id())
            .iter()
            .find(|child| child.ident.name.as_str() == BOOL_LITERAL_FN)
            .expect("upstream bool literal function is missing from module metadata")
            .res
            .opt_def_id()
            .expect("upstream bool literal function child did not resolve to a DefId");

        assert_eq!(tcx.def_kind(bool_literal_fn), DefKind::Fn);

        let bool_contracts = tcx.trust_contracts(bool_literal_fn);
        assert_eq!(bool_contracts.def_id, bool_literal_fn);
        assert_eq!(bool_contracts.contracts.len(), 2);
        assert_eq!(bool_contracts.summary.total, 2);
        assert_eq!(bool_contracts.summary.requires, 2);
        assert_eq!(bool_contracts.summary.ensures, 0);
        assert_eq!(bool_contracts.summary.invariants, 0);
        assert_eq!(bool_contracts.summary.assertions, 0);
        assert_eq!(bool_contracts.summary.opaque, 0);

        let mut saw_true = false;
        let mut saw_false = false;
        for contract in bool_contracts.contracts.iter() {
            assert_eq!(contract.kind, TrustContractKind::Requires);
            assert_eq!(contract.source, TrustContractSource::Attribute);
            assert_eq!(contract.subject, TrustContractSubject::Function);
            assert_eq!(contract.predicate.ty, tcx.types.bool);

            match &contract.predicate.kind {
                TrustContractPredicateKind::BoolLiteral { value: true } => saw_true = true,
                TrustContractPredicateKind::BoolLiteral { value: false } => saw_false = true,
                other => panic!("unexpected bool literal Trust contract predicate: {other:?}"),
            }
        }

        assert!(saw_true);
        assert!(saw_false);

        let unsupported_ensures_fn = tcx
            .module_children(upstream.as_def_id())
            .iter()
            .find(|child| child.ident.name.as_str() == UNSUPPORTED_ENSURES_FN)
            .expect("upstream unsupported ensures function is missing from module metadata")
            .res
            .opt_def_id()
            .expect("upstream unsupported ensures function child did not resolve to a DefId");

        assert_eq!(tcx.def_kind(unsupported_ensures_fn), DefKind::Fn);

        let unsupported_contracts = tcx.trust_contracts(unsupported_ensures_fn);
        assert_eq!(unsupported_contracts.def_id, unsupported_ensures_fn);
        assert_eq!(unsupported_contracts.contracts.len(), 1);
        assert_eq!(unsupported_contracts.summary.total, 1);
        assert_eq!(unsupported_contracts.summary.requires, 0);
        assert_eq!(unsupported_contracts.summary.ensures, 1);
        assert_eq!(unsupported_contracts.summary.invariants, 0);
        assert_eq!(unsupported_contracts.summary.assertions, 0);
        assert_eq!(unsupported_contracts.summary.opaque, 1);

        let unsupported_contract = unsupported_contracts
            .contracts
            .iter()
            .next()
            .expect("expected one unsupported ensures contract");
        assert_eq!(unsupported_contract.kind, TrustContractKind::Ensures);
        assert_eq!(unsupported_contract.source, TrustContractSource::Attribute);
        assert_eq!(unsupported_contract.subject, TrustContractSubject::Function);
        assert_eq!(unsupported_contract.predicate.ty, tcx.types.bool);
        match &unsupported_contract.predicate.kind {
            TrustContractPredicateKind::Unsupported { reason } => {
                assert!(
                    reason.as_str().contains("|ret| ret == ret"),
                    "unexpected unsupported ensures reason: {reason}"
                );
            }
            other => panic!("unexpected unsupported ensures Trust contract predicate: {other:?}"),
        }

        let decreases_fn = tcx
            .module_children(upstream.as_def_id())
            .iter()
            .find(|child| child.ident.name.as_str() == DECREASES_FN)
            .expect("upstream native decreases function is missing from module metadata")
            .res
            .opt_def_id()
            .expect("upstream native decreases function child did not resolve to a DefId");

        let decreases_contracts = tcx.trust_contracts(decreases_fn);
        assert_eq!(decreases_contracts.contracts.len(), 1);
        assert_eq!(decreases_contracts.summary.total, 1);
        assert_eq!(decreases_contracts.summary.decreases, 1);
        let decreases_contract = decreases_contracts
            .contracts
            .iter()
            .next()
            .expect("expected one native decreases contract");
        assert_eq!(decreases_contract.kind, TrustContractKind::Decreases);
        assert_eq!(decreases_contract.source, TrustContractSource::Native);
        assert_eq!(decreases_contract.subject, TrustContractSubject::Function);
        assert_eq!(
            decreases_contract.predicate.ty,
            TrustContractPayloadType::Verifier(TrustContractVerifierSort::Int)
        );
        match &decreases_contract.predicate.kind {
            TrustContractPredicateKind::Opaque { text } => assert_eq!(text.as_str(), "n"),
            other => panic!("unexpected native decreases payload: {other:?}"),
        }

        Compilation::Stop
    }
}

fn main() {
    let sysroot = parse_sysroot();
    let tmpdir = std::env::current_dir().unwrap().join("trust-contract-cross-crate-metadata");
    std::fs::create_dir_all(&tmpdir).unwrap();

    let upstream_src = tmpdir.join("upstream.rs");
    let upstream_rmeta = tmpdir.join(format!("lib{UPSTREAM}.rmeta"));
    write_upstream(&upstream_src);
    compile_upstream(&sysroot, &upstream_src, &tmpdir);
    assert!(upstream_rmeta.exists(), "upstream rmeta was not emitted at {upstream_rmeta:?}");

    let downstream_src = tmpdir.join("downstream.rs");
    write_downstream(&downstream_src);
    compile_downstream(&sysroot, &downstream_src, &upstream_rmeta);
}

fn parse_sysroot() -> PathBuf {
    let mut args = std::env::args().skip(1);
    match (args.next().as_deref(), args.next()) {
        (Some("--sysroot"), Some(path)) => PathBuf::from(path),
        other => panic!("expected `--sysroot <path>` run flags, got {other:?}"),
    }
}

fn compile_upstream(sysroot: &Path, upstream_src: &Path, out_dir: &Path) {
    let args = vec![
        "rustc".to_string(),
        "--sysroot".to_string(),
        sysroot.display().to_string(),
        "--edition=2021".to_string(),
        "--crate-name".to_string(),
        UPSTREAM.to_string(),
        "--crate-type=lib".to_string(),
        "--emit=metadata".to_string(),
        "-Zcontract-checks=no".to_string(),
        "--out-dir".to_string(),
        out_dir.display().to_string(),
        upstream_src.display().to_string(),
    ];
    run_rustc(&args, &mut NoopCallbacks);
}

fn compile_downstream(sysroot: &Path, downstream_src: &Path, upstream_rmeta: &Path) {
    let args = vec![
        "rustc".to_string(),
        "--sysroot".to_string(),
        sysroot.display().to_string(),
        "--edition=2021".to_string(),
        "--crate-name".to_string(),
        DOWNSTREAM.to_string(),
        "--crate-type=lib".to_string(),
        "--emit=metadata".to_string(),
        "--extern".to_string(),
        format!("{UPSTREAM}={}", upstream_rmeta.display()),
        downstream_src.display().to_string(),
    ];
    run_rustc(&args, &mut MetadataCallbacks);
}

fn run_rustc(args: &[String], callbacks: &mut (dyn rustc_driver::Callbacks + Send)) {
    let _ = rustc_driver::catch_fatal_errors(|| -> interface::Result<()> {
        rustc_driver::run_compiler(args, callbacks);
        Ok(())
    })
    .unwrap();
}

fn write_upstream(path: &Path) {
    std::fs::write(
        path,
        r#"
#![allow(incomplete_features)]
#![feature(contracts)]

extern crate core;

use core::contracts::{ensures, requires};

#[requires(x > 0)]
#[ensures(|ret| *ret > 0)]
pub fn requires_and_ensures(x: u32) -> u32 {
    x
}

#[requires(true)]
#[requires(false)]
pub fn bool_literal_contracts() {}

#[ensures(|ret| ret == ret)]
pub fn unsupported_ensures_shape(x: u32) -> u32 {
    x
}

pub fn native_decreases_measure(n: u32) -> u32
    decreases n
{
    n
}
"#,
    )
    .unwrap();
}

fn write_downstream(path: &Path) {
    std::fs::write(
        path,
        format!(
            r#"
extern crate {UPSTREAM};

pub fn use_upstream_contract(x: u32) -> u32 {{
    {UPSTREAM}::{CONTRACTED_FN}(x)
}}
"#
        ),
    )
    .unwrap();
}
