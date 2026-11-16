#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_span;
extern crate trust_ir;
extern crate trust_thir_lower as producer;
use producer::rmeta_entry::*;
use trust_ir::{Block, BlockId, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty, ValueId};
fn save(name: &str, b: &[u8]) {
    let p = std::path::PathBuf::from(std::env::var_os("CODEC_WIRE_OUT").unwrap());
    std::fs::create_dir_all(&p).unwrap();
    std::fs::write(p.join(name), b).unwrap();
}
fn module() -> Module {
    let mut m = Module::new("complete_R_codec_control");
    let t = m
        .intern_func_type(FuncTy {
            params: vec![Ty::U64],
            returns: vec![Ty::U64],
            is_vararg: false,
            abi: None,
        })
        .unwrap();
    let mut f = Function::new(FuncId::new(0), "actual_R_identity", t, BlockId::new(0))
        .with_producer(trust_ir::Producer::TRust);
    let mut b = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::U64);
    b.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    f.blocks.push(b);
    m.try_add_function(f).unwrap();
    m
}
#[test]
fn complete_r_frame_roundtrip_and_native_negative_controls() {
    let m = module();
    let e = encode_evidence(&sample_evidence());
    let binding = EntryBinding {
        stable_crate_id: 0x1234,
        local_hash: 0xabcd,
    };
    let bytes = frame_entry(&m, binding, true, &e).unwrap();
    let d = decode_entry(&bytes).unwrap();
    assert_eq!(d.binding, binding);
    assert!(d.overflow_checks);
    assert!(decode_entry_for_overflow(&bytes, true).is_ok());
    assert!(matches!(decode_entry_for_overflow(&bytes, false), Err(EntryDecodeError::OverflowMode { producer: true, consumer: false })));
    assert_eq!(d.digest, m.stable_digest().bytes);
    assert_eq!(d.module, m);
    assert_eq!(d.evidence, e);
    assert_eq!(frame_entry(&m, binding, true, &e).unwrap(), bytes);
    save("R-entry.bin", &bytes);
    save("R-entry-checks-off.bin", &frame_entry(&m, binding, false, &e).unwrap());
    for cut in 0..bytes.len() {
        assert!(
            decode_entry(&bytes[..cut]).is_err(),
            "R strict prefix {cut}"
        );
    }
    let mut bad = bytes.clone();
    bad[0] ^= 1;
    assert!(matches!(decode_entry(&bad), Err(EntryDecodeError::Magic)));
    bad = bytes.clone();
    bad[8..12].copy_from_slice(&(ENTRY_SCHEMA + 1).to_le_bytes());
    assert!(matches!(
        decode_entry(&bad),
        Err(EntryDecodeError::Schema(_))
    ));
    bad = bytes.clone();
    bad[12..16].copy_from_slice(&(trust_ir::binary::VERSION + 1).to_le_bytes());
    assert!(matches!(
        decode_entry(&bad),
        Err(EntryDecodeError::TrustIrVersion { .. })
    ));
    bad = bytes.clone();
    bad[32] ^= 1;
    assert!(matches!(decode_entry(&bad), Err(EntryDecodeError::EnvelopeDigest)));
    bad = bytes.clone();
    bad.push(0);
    assert!(matches!(
        decode_entry(&bad),
        Err(EntryDecodeError::TrailingBytes(_))
    ));
    bad = bytes;
    bad[..8].copy_from_slice(b"TRIRTMPL");
    assert!(matches!(decode_entry(&bad), Err(EntryDecodeError::Magic)));
}
#[test]
fn complete_evidence_roundtrip_all_fields_and_native_negative_controls() {
    let e = sample_evidence();
    let b = encode_evidence(&e);
    assert_eq!(decode_evidence(&b), Ok(e));
    save("evidence-all-fields.bin", &b);
    assert_eq!(
        decode_evidence(&encode_evidence(&Evidence::default())),
        Ok(Evidence::default())
    );
    for cut in 0..b.len() {
        assert!(decode_evidence(&b[..cut]).is_err(), "evidence prefix {cut}");
    }
    for schema in [2, 3, EVIDENCE_SCHEMA + 1] {
        let mut bad = b.clone();
        bad[8..12].copy_from_slice(&schema.to_le_bytes());
        assert_eq!(decode_evidence(&bad), Err(EntryDecodeError::EvidenceSchema(schema)));
    }
    let mut bad = b.clone();
    bad[0] ^= 1;
    assert!(decode_evidence(&bad).is_err());
    let mut bad = b;
    bad.push(0);
    assert!(decode_evidence(&bad).is_err());
    for code in 0..=9 {
        let mut e = sample_evidence();
        let EvidenceEffectKind::Call(c) = &mut e.effects[0].0 else {
            panic!()
        };
        c.equivalence = Some(code);
        assert_eq!(decode_evidence(&encode_evidence(&e)), Ok(e));
    }
    let mut e = sample_evidence();
    let EvidenceEffectKind::Call(c) = &mut e.effects[0].0 else {
        panic!()
    };
    c.equivalence = Some(10);
    assert!(decode_evidence(&encode_evidence(&e)).is_err());
}
#[test]
fn evidence_stable_defs_and_body_local_span_ordinals_are_retained() {
    rustc_span::create_default_session_globals_then(|| {
        use producer::effect_conservation::{MemRoot, MirCensus, MirEffect, MirEffectKind};
        use rustc_span::def_id::{CrateNum, DefId, DefIndex};
        use rustc_span::{BytePos, DUMMY_SP};
        struct Spell;
        impl EvidenceSpelling for Spell {
            fn def(&self, d: DefId) -> StableDef {
                (0xc0de, d.index.as_u32() as u64)
            }
            fn site(&self, d: DefId, a: &[producer::SiteArg]) -> String {
                format!("{}:{}", d.index.as_u32(), a.len())
            }
        }
        let a = DUMMY_SP;
        let b = DUMMY_SP.with_lo(BytePos(5));
        let d = DefId {
            krate: CrateNum::from_u32(0),
            index: DefIndex::from_u32(9),
        };
        let census = MirCensus {
            effects: vec![
                MirEffect {
                    kind: MirEffectKind::Call {
                        ids: vec![d],
                        site_args: Some(vec![]),
                        equivalence: None,
                        enum_result: false,
                        enum_args: vec![false],
                    },
                    span: b,
                },
                MirEffect {
                    kind: MirEffectKind::Store(MemRoot::Arg(1)),
                    span: a,
                },
                MirEffect {
                    kind: MirEffectKind::Drop { destructor: false },
                    span: b,
                },
            ],
            arg_count: 2,
            ..Default::default()
        };
        let r = RetainedEvidence {
            census,
            drop_claim: None,
            collapsed_enum_types: vec![7],
            degraded_structs: vec![2],
            union_lane: false,
            enum_param_lane: true,
        };
        let e = evidence_of(&r, &[], &Spell);
        assert_eq!(
            e.effects,
            vec![
                (
                    EvidenceEffectKind::Call(EvidenceCall {
                        ids: vec![(0xc0de, 9)],
                        site: Some("9:0".into()),
                        equivalence: None,
                        enum_result: false,
                        enum_args: vec![false]
                    }),
                    0
                ),
                (EvidenceEffectKind::Store(1), 1),
                (EvidenceEffectKind::Drop { destructor: false }, 0)
            ]
        );
        assert_eq!(
            (
                e.collapsed_enum_types.clone(),
                e.degraded_structs.clone(),
                e.union_lane,
                e.enum_param_lane
            ),
            (vec![7], vec![2], false, true)
        );
        let bytes = encode_evidence(&e);
        assert_eq!(decode_evidence(&bytes), Ok(e));
        save("evidence-spelling.bin", &bytes);
    });
}

fn sample_evidence() -> Evidence {
    Evidence {
        effects: vec![
            (
                EvidenceEffectKind::Call(EvidenceCall {
                    ids: vec![(1, 2), (3, 4)],
                    site: Some("00ab".to_string()),
                    equivalence: Some(7),
                    enum_result: true,
                    enum_args: vec![false, true],
                }),
                0,
            ),
            (EvidenceEffectKind::IndirectCall, 1),
            (EvidenceEffectKind::Store(u32::MAX - 1), 2),
            (EvidenceEffectKind::Drop { destructor: true }, 3),
            (EvidenceEffectKind::Assert(2), 0),
            (
                EvidenceEffectKind::Asm {
                    empty_noreturn: false,
                },
                1,
            ),
            (EvidenceEffectKind::Yield, 2),
        ],
        arg_count: 2,
        arg_enum: vec![true, false],
        ret_enum: true,
        store_values: vec![(0, 1), (u32::MAX, 2)],
        exact_store_args: vec![],
        enum_types: vec![u128::MAX, 5],
        drop_oracle: Some(vec![EvidenceOracleDrop {
            block: 3,
            identity: (1, 17),
            ty: 99,
            span: 3,
            style: Some(1),
            projected: false,
            destructor: true,
        }]),
        drop_dead_blocks: vec![4, 6],
        drop_claim: Some((
            vec![EvidenceDropKey {
                identity: (0, 1),
                ty: 99,
                span: 3,
                style: 0,
            }],
            1,
            vec![true],
        )),
        ledger: vec![EvidenceLedgerRow {
            func_id: 1,
            ids: vec![(1, 2)],
            site: None,
        }],
        collapsed_enum_types: vec![5],
        degraded_structs: vec![0, 3],
        union_lane: true,
        enum_param_lane: false,
    }
}

#[test]
fn evidence_exact_store_arguments_roundtrip_and_reject_malformed_facts() {
    let mut evidence = sample_evidence();
    evidence
        .effects
        .push((EvidenceEffectKind::Store(u32::MAX), 4));
    evidence.exact_store_args = vec![(7, 1)];
    evidence.store_values = vec![(u32::MAX - 1, 2), (u32::MAX, 2)];
    assert_eq!(
        decode_evidence(&encode_evidence(&evidence)),
        Ok(evidence.clone())
    );
    for facts in [
        vec![(7, 2)],
        vec![(0, 1)],
        vec![(2, 1)],
        vec![(8, 1)],
        vec![(7, 1), (7, 0)],
    ] {
        let mut bad = evidence.clone();
        bad.exact_store_args = facts;
        assert!(decode_evidence(&encode_evidence(&bad)).is_err());
    }
    let mut old = encode_evidence(&evidence);
    old[8..12].copy_from_slice(&3u32.to_le_bytes());
    assert_eq!(decode_evidence(&old), Err(EntryDecodeError::EvidenceSchema(3)));
}
