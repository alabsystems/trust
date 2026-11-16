//! Read-only actual-TCX carrier extractor/mutator. This embedded driver has no
//! official evidence authority and never runs F1. The official trustc consumes
//! the resulting owned carrier copies separately, with all policies unchanged.
#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
extern crate serde_json;
extern crate trust_ir;
extern crate trust_thir_lower;

use rustc_hir::def::DefKind;
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::{CRATE_DEF_INDEX, DefId};
use serde_json::json;
use trust_ir::{Inst, Ty};
use trust_thir_lower::rmeta_entry::{self as entry, EvidenceEffectKind};

fn stable(tcx: TyCtxt<'_>, def: DefId) -> (u64, u64) {
    let hash = tcx.def_path_hash(def);
    (hash.stable_crate_id().as_u64(), hash.local_hash().as_u64())
}
fn hex(key: (u64, u64)) -> String {
    key.0.to_be_bytes().into_iter().chain(key.1.to_be_bytes()).map(|b| format!("{b:02x}")).collect()
}
fn sibling(tcx: TyCtxt<'_>, def: DefId, name: &str, kind: DefKind) -> DefId {
    let root = DefId { krate: def.krate, index: CRATE_DEF_INDEX };
    let definitions: Vec<_> = tcx.module_children(root).iter()
        .filter(|item| item.ident.name.as_str() == name).filter_map(|item| item.res.opt_def_id())
        // Tuple structs also export a constructor with the same name. Select
        // the actual metadata definition kind, never the first named row.
        .filter(|&definition| tcx.def_kind(definition) == kind).collect();
    assert_eq!(definitions.len(), 1, "one actual metadata owner {name}");
    definitions[0]
}
fn tags(module: &trust_ir::Module, evidence: &entry::Evidence) -> serde_json::Value {
    match trust_thir_lower::effect_conservation::retained::judge(module, evidence) {
        Ok(judgement) => json!({"accepted_by_retained_checker":judgement.tags().is_empty(),
            "tags":format!("{:?}",judgement.tags()),"shape":format!("{:?}",judgement.shape())}),
        Err(error) => json!({"accepted_by_retained_checker":false,"error":error.to_string()}),
    }
}

/// Rust metadata's opaque-blob length and every lazy offset must stay intact.
/// Deliberately adjust only a debug filename to balance changed frame length;
/// disclose the adjustment and rehash the whole new module/envelope normally.
fn same_length_frame(mut module: trust_ir::Module, binding: entry::EntryBinding,
                     mode: bool, evidence: &entry::Evidence, wanted: usize) -> (Vec<u8>, isize) {
    let encoded = entry::encode_evidence(evidence);
    let initial = entry::frame_entry(&module, binding, mode, &encoded).unwrap();
    if initial.len() == wanted {
        return (initial, 0);
    }
    let original = module.files.first().expect("real producer debug filename for length balancing").len();
    let predicted = original as isize + wanted as isize - initial.len() as isize;
    // String-table length prefixes can change width at the predicted size.
    // Search a bounded neighborhood and accept only exact re-framed bytes;
    // every other module field and the outer Rust metadata remain untouched.
    for distance in 0..=64isize {
        for len in [predicted + distance, predicted - distance] {
            if len <= 0 || len >= (1 << 20) { continue; }
            module.files[0] = "x".repeat(len as usize);
            let bytes = entry::frame_entry(&module, binding, mode, &encoded).unwrap();
            if bytes.len() == wanted {
                return (bytes, len - original as isize);
            }
        }
    }
    panic!("no exact same-length debug-filename adjustment in bounded search");
}

struct Reader;
impl rustc_driver::Callbacks for Reader {
    fn after_analysis<'tcx>(&mut self, _: &rustc_interface::interface::Compiler,
                           tcx: TyCtxt<'tcx>) -> rustc_driver::Compilation {
        let out = std::path::PathBuf::from(std::env::var_os("R_IMPORT_MUTATION_OUT").unwrap());
        std::fs::create_dir_all(&out).unwrap();
        assert_eq!(entry::ENTRY_SCHEMA, 6);
        let crates: Vec<_> = tcx.crates(()).iter().copied()
            .filter(|krate| tcx.crate_name(*krate).as_str() == "attack_dep").collect();
        assert_eq!(crates.len(), 1, "actual canonical producer dependency must be loaded");
        let root = DefId { krate: crates[0], index: CRATE_DEF_INDEX };
        let chain = sibling(tcx, root, "chain", DefKind::Fn);
        let nested = sibling(tcx, root, "nested", DefKind::Fn);
        let other = sibling(tcx, root, "other", DefKind::Fn);
        let marker = sibling(tcx, root, "Marker", DefKind::Struct);
        let header = tcx.trust_ir_crate_header(crates[0]).expect("actual producer header");
        assert_eq!(header.entry_schema, 6);
        assert_eq!(header.trust_ir_version, trust_ir::binary::VERSION);
        assert!(header.crate_refusal.is_none());
        let mut records = Vec::new();
        for (name, owner) in [("chain", chain), ("nested", nested)] {
            let blob = tcx.trust_ir_entry(owner).expect("actual canonical R carrier required");
            std::fs::write(out.join(format!("{name}.original.entry")), &blob.0).unwrap();
            let original = entry::decode_entry_for_overflow(&blob.0, tcx.sess.overflow_checks()).unwrap();
            assert_eq!((original.binding.stable_crate_id, original.binding.local_hash), stable(tcx, owner));
            let evidence = entry::decode_evidence(&original.evidence).unwrap();
            assert!(!evidence.ledger.is_empty(), "subject must retain an actual call ledger");
            assert!(tags(&original.module, &evidence)["accepted_by_retained_checker"].as_bool().unwrap());
            let cases: &[&str] = if name == "chain" {
                &["stale_digest", "wrong_owner", "ledger_missing", "ledger_duplicate", "ledger_identity_drift", "source_identity_drift", "ir_call_omitted", "census_call_omitted_observe"]
            } else { &["nested_wrong_kind", "nested_absent"] };
            for &case in cases {
                let mut module = original.module.clone();
                let mut facts = evidence.clone();
                let mut binding = original.binding;
                match case {
                    "stale_digest" => {},
                    "wrong_owner" => {
                        let other = stable(tcx, other);
                        binding = entry::EntryBinding { stable_crate_id:other.0, local_hash:other.1 };
                    },
                    "ledger_missing" => { facts.ledger.remove(0); },
                    "ledger_duplicate" => { facts.ledger.push(facts.ledger[0].clone()); },
                    "ledger_identity_drift" => { facts.ledger[0].ids = vec![stable(tcx, other)]; },
                    "source_identity_drift" => {
                        let call = facts.effects.iter_mut().find_map(|(kind, _)|
                            if let EvidenceEffectKind::Call(call) = kind {Some(call)} else {None}).unwrap();
                        call.ids = vec![stable(tcx, other)];
                    },
                    "ir_call_omitted" => {
                        let body = module.function_by_id_mut(trust_ir::FuncId::new(0)).unwrap();
                        let node = body.blocks.iter_mut().flat_map(|block| &mut block.body)
                            .find(|node| matches!(node.inst, Inst::Call{..})).unwrap();
                        let Inst::Call{args,..} = &node.inst else {unreachable!()};
                        assert_eq!(args.len(),1);
                        node.inst = Inst::Copy{ty:Ty::U64,operand:args[0]};
                    },
                    "census_call_omitted_observe" => {
                        let i = facts.effects.iter().position(|(kind,_)|matches!(kind,EvidenceEffectKind::Call(_))).unwrap();
                        facts.effects.remove(i);
                    },
                    "nested_wrong_kind" | "nested_absent" => {
                        let old = facts.ledger[0].site.clone().expect("real nested nominal site");
                        let marker_key = stable(tcx, marker);
                        let replacement = if case == "nested_wrong_kind" {stable(tcx, other)} else {
                            (1..=16).map(|nonce|(marker_key.0,marker_key.1^nonce))
                                .find(|key|trust_thir_lower::template_key::rustc::definition(tcx,*key).is_err())
                                .expect("bounded actual absent nominal key")
                        };
                        assert_eq!(old.matches(&hex(marker_key)).count(),1,"one actual nested Marker identity");
                        let changed = old.replacen(&hex(marker_key),&hex(replacement),1);
                        facts.ledger[0].site = Some(changed.clone());
                        let mut rewritten = 0;
                        for (kind,_) in &mut facts.effects {
                            if let EvidenceEffectKind::Call(call) = kind
                                && call.site.as_deref() == Some(old.as_str()) {
                                call.site = Some(changed.clone());rewritten += 1;
                            }
                        }
                        assert!(rewritten > 0,"preserve source/ledger site agreement to reach actual nominal recovery");
                    },
                    _ => unreachable!(),
                }
                let observed = tags(&module,&facts);
                let (mut changed,adjustment) = same_length_frame(module,binding,original.overflow_checks,&facts,blob.0.len());
                if case == "stale_digest" {let last=changed.len()-1;changed[last]^=1;}
                assert_ne!(changed,blob.0);
                if case != "stale_digest" {entry::decode_entry_for_overflow(&changed,tcx.sess.overflow_checks()).unwrap();}
                std::fs::write(out.join(format!("{case}.entry")),&changed).unwrap();
                records.push(json!({"case":case,"actual_owner":name,"actual_owner_identity":stable(tcx,owner),
                    "source_mode":original.overflow_checks,"consumer_reader_mode":tcx.sess.overflow_checks(),
                    "bytes":changed.len(),"filename_length_adjustment":adjustment,
                    "retained_checker_observation":observed,"canonical_F1_execution":false,"proof_authority":false}));
            }
        }
        std::fs::write(out.join("MUTATIONS.json"),serde_json::to_vec_pretty(&records).unwrap()).unwrap();
        assert_eq!(records.len(),10);
        rustc_driver::Compilation::Continue
    }
}
fn main() {
    let mut args:Vec<_>=std::env::args().collect();
    args.push("-Zno-steal-thir".into());
    let expected=std::env::var("R_IMPORT_MUTATION_SYSROOT").unwrap();
    let supplied:Vec<_>=args.iter().enumerate().filter_map(|(i,arg)|
        if arg=="--sysroot" {Some(args.get(i+1).expect("sysroot value").as_str())}
        else {arg.strip_prefix("--sysroot=")}).collect();
    assert!(supplied.len()<=1,"one actual sysroot option");
    if let Some(actual)=supplied.first(){assert_eq!(*actual,expected)}
    else{args.extend(["--sysroot".into(),expected]);}
    rustc_driver::run_compiler(&args,&mut Reader);
}
