// The hardened `mir_assert::Overflow(Sub)` twin of `input.len() - 4` in aterm-codec's
// `zlib_decompress` (`crates/aterm-codec/src/inflate.rs:911`, aterm 5923cb33c), exactly as
// the channel seal trust-b58a105d (Trust b58a105dde) generates it: captured 2026-10-14
// with `TRUST_DUMP_V2_VC=1 trustc --edition 2024 --crate-type lib -Ztrust-verify-level=2
// -Ztrust-policy=advisory -Ztrust-verify-timeout-ms=5000
// -Ztrust-verify-function-budget-ms=120000 -Ztrust-verify-profile=unix_hardened` on a
// one-file crate holding aterm-codec's `inflate.rs`, `inflate/stream.rs` and `crc32.rs`
// (the row is that file's line 1836), the second `[V2_VC]` line at that span; converted
// to constructors mechanically, nested `And`s flattened. Its 181 conjuncts are the
// per-statement hypotheses plus the twin's type-range battery.
use trust_types::{Formula, Sort};

fn v(name: &str, sort: Sort) -> Formula {
    Formula::Var(name.to_string(), sort)
}

/// The twin's violation, `src/lib.rs:1836:25-1836:40` of the capture crate.
pub fn twin() -> Formula {
    Formula::And(twin_conjuncts())
}

/// The top-level conjuncts, in the compiler's order (its nested `And`s flattened, as
/// the certifier's normalization splits them).
pub fn twin_conjuncts() -> Vec<Formula> {
    vec![
        Formula::Ge(Box::new(v("input__slice_len", Sort::Int)), Box::new(Formula::Int(0i128))),
        Formula::Le(
            Box::new(v("input__slice_len", Sort::Int)),
            Box::new(Formula::Int(9223372036854775807i128)),
        ),
        Formula::Ge(
            Box::new(v("deflate__slice_len#s15_t", Sort::Int)),
            Box::new(Formula::Int(0i128)),
        ),
        Formula::Le(
            Box::new(v("deflate__slice_len#s15_t", Sort::Int)),
            Box::new(Formula::Int(9223372036854775807i128)),
        ),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("_37@0.0.1#s17_t", Sort::Int))),
        Formula::Le(
            Box::new(v("_37@0.0.1#s17_t", Sort::Int)),
            Box::new(Formula::Int(18446744073709551615i128)),
        ),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("_24", Sort::Int))),
        Formula::Le(Box::new(v("_24", Sort::Int)), Box::new(Formula::Int(255i128))),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("_22", Sort::Int))),
        Formula::Le(Box::new(v("_22", Sort::Int)), Box::new(Formula::Int(4294967295i128))),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("_33", Sort::Int))),
        Formula::Le(
            Box::new(v("_33", Sort::Int)),
            Box::new(Formula::Int(18446744073709551615i128)),
        ),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("_7", Sort::Int))),
        Formula::Le(Box::new(v("_7", Sort::Int)), Box::new(Formula::Int(18446744073709551615i128))),
        Formula::Ge(Box::new(v("_7", Sort::Int)), Box::new(Formula::Int(0i128))),
        Formula::Le(Box::new(v("_7", Sort::Int)), Box::new(Formula::Int(0i128))),
        Formula::Le(
            Box::new(Formula::Int(-9223372036854775808i128)),
            Box::new(v("_39", Sort::Int)),
        ),
        Formula::Le(Box::new(v("_39", Sort::Int)), Box::new(Formula::Int(9223372036854775807i128))),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("cmf", Sort::Int))),
        Formula::Le(Box::new(v("cmf", Sort::Int)), Box::new(Formula::Int(255i128))),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("_28", Sort::Int))),
        Formula::Le(Box::new(v("_28", Sort::Int)), Box::new(Formula::Int(255i128))),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("_65", Sort::Int))),
        Formula::Le(
            Box::new(v("_65", Sort::Int)),
            Box::new(Formula::Int(18446744073709551615i128)),
        ),
        Formula::Ge(Box::new(v("_65", Sort::Int)), Box::new(Formula::Int(3i128))),
        Formula::Le(Box::new(v("_65", Sort::Int)), Box::new(Formula::Int(3i128))),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("_19", Sort::Int))),
        Formula::Le(Box::new(v("_19", Sort::Int)), Box::new(Formula::Int(65535i128))),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("_53", Sort::Int))),
        Formula::Le(
            Box::new(v("_53", Sort::Int)),
            Box::new(Formula::Int(18446744073709551615i128)),
        ),
        Formula::Ge(Box::new(v("_53", Sort::Int)), Box::new(Formula::Int(0i128))),
        Formula::Le(Box::new(v("_53", Sort::Int)), Box::new(Formula::Int(0i128))),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("_21", Sort::Int))),
        Formula::Le(Box::new(v("_21", Sort::Int)), Box::new(Formula::Int(255i128))),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("_11", Sort::Int))),
        Formula::Le(
            Box::new(v("_11", Sort::Int)),
            Box::new(Formula::Int(18446744073709551615i128)),
        ),
        Formula::Ge(Box::new(v("_11", Sort::Int)), Box::new(Formula::Int(1i128))),
        Formula::Le(Box::new(v("_11", Sort::Int)), Box::new(Formula::Int(1i128))),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("_18", Sort::Int))),
        Formula::Le(Box::new(v("_18", Sort::Int)), Box::new(Formula::Int(65535i128))),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("_20", Sort::Int))),
        Formula::Le(Box::new(v("_20", Sort::Int)), Box::new(Formula::Int(65535i128))),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("_8", Sort::Int))),
        Formula::Le(Box::new(v("_8", Sort::Int)), Box::new(Formula::Int(18446744073709551615i128))),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("_57", Sort::Int))),
        Formula::Le(
            Box::new(v("_57", Sort::Int)),
            Box::new(Formula::Int(18446744073709551615i128)),
        ),
        Formula::Ge(Box::new(v("_57", Sort::Int)), Box::new(Formula::Int(1i128))),
        Formula::Le(Box::new(v("_57", Sort::Int)), Box::new(Formula::Int(1i128))),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("_43", Sort::Int))),
        Formula::Le(
            Box::new(v("_43", Sort::Int)),
            Box::new(Formula::Int(18446744073709551615i128)),
        ),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("used", Sort::Int))),
        Formula::Le(
            Box::new(v("used", Sort::Int)),
            Box::new(Formula::Int(18446744073709551615i128)),
        ),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("_12", Sort::Int))),
        Formula::Le(
            Box::new(v("_12", Sort::Int)),
            Box::new(Formula::Int(18446744073709551615i128)),
        ),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("_4", Sort::Int))),
        Formula::Le(Box::new(v("_4", Sort::Int)), Box::new(Formula::Int(18446744073709551615i128))),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("flg", Sort::Int))),
        Formula::Le(Box::new(v("flg", Sort::Int)), Box::new(Formula::Int(255i128))),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("_61", Sort::Int))),
        Formula::Le(
            Box::new(v("_61", Sort::Int)),
            Box::new(Formula::Int(18446744073709551615i128)),
        ),
        Formula::Ge(Box::new(v("_61", Sort::Int)), Box::new(Formula::Int(2i128))),
        Formula::Le(Box::new(v("_61", Sort::Int)), Box::new(Formula::Int(2i128))),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("_48", Sort::Int))),
        Formula::Le(
            Box::new(v("_48", Sort::Int)),
            Box::new(Formula::Int(18446744073709551615i128)),
        ),
        Formula::Le(
            Box::new(Formula::Int(-9223372036854775808i128)),
            Box::new(v("_39", Sort::Int)),
        ),
        Formula::Le(Box::new(v("_39", Sort::Int)), Box::new(Formula::Int(9223372036854775807i128))),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("_15", Sort::Int))),
        Formula::Le(Box::new(v("_15", Sort::Int)), Box::new(Formula::Int(255i128))),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("max_output", Sort::Int))),
        Formula::Le(
            Box::new(v("max_output", Sort::Int)),
            Box::new(Formula::Int(18446744073709551615i128)),
        ),
        Formula::Eq(Box::new(v("_4", Sort::Int)), Box::new(v("input__slice_len", Sort::Int))),
        Formula::Eq(
            Box::new(v("_3", Sort::Bool)),
            Box::new(Formula::Lt(Box::new(v("_4", Sort::Int)), Box::new(Formula::Int(6i128)))),
        ),
        Formula::Eq(Box::new(v("_7", Sort::Int)), Box::new(Formula::Int(0i128))),
        Formula::Eq(Box::new(v("_8", Sort::Int)), Box::new(v("input__slice_len", Sort::Int))),
        Formula::Eq(
            Box::new(v("_9", Sort::Bool)),
            Box::new(Formula::Lt(Box::new(v("_7", Sort::Int)), Box::new(v("_8", Sort::Int)))),
        ),
        Formula::Eq(Box::new(v("cmf", Sort::Int)), Box::new(v("input*[0;slice]", Sort::Int))),
        Formula::Eq(Box::new(v("_11", Sort::Int)), Box::new(Formula::Int(1i128))),
        Formula::Eq(Box::new(v("_12", Sort::Int)), Box::new(v("input__slice_len", Sort::Int))),
        Formula::Eq(
            Box::new(v("_13", Sort::Bool)),
            Box::new(Formula::Lt(Box::new(v("_11", Sort::Int)), Box::new(v("_12", Sort::Int)))),
        ),
        Formula::Eq(Box::new(v("flg", Sort::Int)), Box::new(v("input*[1;slice]", Sort::Int))),
        Formula::Eq(
            Box::new(v("_15", Sort::Int)),
            Box::new(Formula::BvToInt(
                Box::new(Formula::BvAnd(
                    Box::new(Formula::IntToBv(Box::new(v("cmf", Sort::Int)), 8)),
                    Box::new(Formula::IntToBv(Box::new(Formula::Int(15i128)), 8)),
                    8,
                )),
                8,
                false,
            )),
        ),
        Formula::Eq(
            Box::new(v("_14", Sort::Bool)),
            Box::new(Formula::Not(Box::new(Formula::Eq(
                Box::new(v("_15", Sort::Int)),
                Box::new(Formula::Int(8i128)),
            )))),
        ),
        Formula::Eq(Box::new(v("_21", Sort::Int)), Box::new(v("cmf", Sort::Int))),
        Formula::Eq(Box::new(v("_22", Sort::Int)), Box::new(Formula::Int(8i128))),
        Formula::Eq(
            Box::new(v("_23", Sort::Bool)),
            Box::new(Formula::Lt(Box::new(v("_22", Sort::Int)), Box::new(Formula::Int(16i128)))),
        ),
        Formula::Eq(
            Box::new(v("_20", Sort::Int)),
            Box::new(Formula::BvToInt(
                Box::new(Formula::BvShl(
                    Box::new(Formula::IntToBv(Box::new(v("_21", Sort::Int)), 16)),
                    Box::new(Formula::BvAnd(
                        Box::new(Formula::IntToBv(Box::new(Formula::Int(8i128)), 16)),
                        Box::new(Formula::BitVec { value: 15i128, width: 16 }),
                        16,
                    )),
                    16,
                )),
                16,
                false,
            )),
        ),
        Formula::Eq(Box::new(v("_24", Sort::Int)), Box::new(v("flg", Sort::Int))),
        Formula::Eq(
            Box::new(v("_19", Sort::Int)),
            Box::new(Formula::BvToInt(
                Box::new(Formula::BvOr(
                    Box::new(Formula::IntToBv(Box::new(v("_20", Sort::Int)), 16)),
                    Box::new(Formula::IntToBv(Box::new(v("_24", Sort::Int)), 16)),
                    16,
                )),
                16,
                false,
            )),
        ),
        Formula::Eq(
            Box::new(v("_25", Sort::Bool)),
            Box::new(Formula::Eq(Box::new(Formula::Int(31i128)), Box::new(Formula::Int(0i128)))),
        ),
        Formula::Eq(
            Box::new(v("_18", Sort::Int)),
            Box::new(Formula::Rem(Box::new(v("_19", Sort::Int)), Box::new(Formula::Int(31i128)))),
        ),
        Formula::Eq(
            Box::new(v("_17", Sort::Bool)),
            Box::new(Formula::Not(Box::new(Formula::Eq(
                Box::new(v("_18", Sort::Int)),
                Box::new(Formula::Int(0i128)),
            )))),
        ),
        Formula::Eq(
            Box::new(v("_28", Sort::Int)),
            Box::new(Formula::BvToInt(
                Box::new(Formula::BvAnd(
                    Box::new(Formula::IntToBv(Box::new(v("flg", Sort::Int)), 8)),
                    Box::new(Formula::IntToBv(Box::new(Formula::Int(32i128)), 8)),
                    8,
                )),
                8,
                false,
            )),
        ),
        Formula::Eq(
            Box::new(v("_27", Sort::Bool)),
            Box::new(Formula::Not(Box::new(Formula::Eq(
                Box::new(v("_28", Sort::Int)),
                Box::new(Formula::Int(0i128)),
            )))),
        ),
        Formula::Le(
            Box::new(Formula::Int(0i128)),
            Box::new(Formula::Sub(Box::new(v("_33", Sort::Int)), Box::new(Formula::Int(4i128)))),
        ),
        Formula::Le(
            Box::new(Formula::Sub(Box::new(v("_33", Sort::Int)), Box::new(Formula::Int(4i128)))),
            Box::new(Formula::Int(18446744073709551615i128)),
        ),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("_33", Sort::Int))),
        Formula::Le(
            Box::new(v("_33", Sort::Int)),
            Box::new(Formula::Int(18446744073709551615i128)),
        ),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(Formula::Int(4i128))),
        Formula::Le(
            Box::new(Formula::Int(4i128)),
            Box::new(Formula::Int(18446744073709551615i128)),
        ),
        Formula::Eq(Box::new(v("_33", Sort::Int)), Box::new(v("input__slice_len", Sort::Int))),
        Formula::Eq(
            Box::new(v("_43", Sort::Int)),
            Box::new(v("deflate__slice_len#s15_t", Sort::Int)),
        ),
        Formula::Eq(
            Box::new(v("_42", Sort::Bool)),
            Box::new(Formula::Not(Box::new(Formula::Eq(
                Box::new(v("used", Sort::Int)),
                Box::new(v("_43", Sort::Int)),
            )))),
        ),
        Formula::Not(Box::new(Formula::Lt(
            Box::new(v("input__slice_len", Sort::Int)),
            Box::new(Formula::Int(6i128)),
        ))),
        v("_9", Sort::Bool),
        v("_13", Sort::Bool),
        Formula::Not(Box::new(Formula::Not(Box::new(Formula::Eq(
            Box::new(v("_15", Sort::Int)),
            Box::new(Formula::Int(8i128)),
        ))))),
        v("_23", Sort::Bool),
        Formula::Not(Box::new(v("_25", Sort::Bool))),
        Formula::Not(Box::new(Formula::Not(Box::new(Formula::Eq(
            Box::new(v("_18", Sort::Int)),
            Box::new(Formula::Int(0i128)),
        ))))),
        Formula::Not(Box::new(Formula::Not(Box::new(Formula::Eq(
            Box::new(v("_28", Sort::Int)),
            Box::new(Formula::Int(0i128)),
        ))))),
        Formula::Not(Box::new(v("_34.1#s14_1", Sort::Bool))),
        Formula::Eq(Box::new(v("_39", Sort::Int)), Box::new(Formula::Int(0i128))),
        Formula::Not(Box::new(Formula::Not(Box::new(Formula::Eq(
            Box::new(v("used", Sort::Int)),
            Box::new(v("deflate__slice_len#s15_t", Sort::Int)),
        ))))),
        Formula::Or(vec![
            Formula::Eq(Box::new(v("_39", Sort::Int)), Box::new(Formula::Int(0i128))),
            Formula::Eq(Box::new(v("_39", Sort::Int)), Box::new(Formula::Int(1i128))),
        ]),
        Formula::Ge(Box::new(v("max_output", Sort::Int)), Box::new(Formula::Int(0i128))),
        Formula::Le(
            Box::new(v("max_output", Sort::Int)),
            Box::new(Formula::Int(18446744073709551615i128)),
        ),
        Formula::Or(vec![
            Formula::Lt(Box::new(v("_33", Sort::Int)), Box::new(Formula::Int(4i128))),
            Formula::Eq(
                Box::new(v("_32", Sort::Int)),
                Box::new(Formula::Sub(
                    Box::new(v("_33", Sort::Int)),
                    Box::new(Formula::Int(4i128)),
                )),
            ),
        ]),
        Formula::Or(vec![
            Formula::Lt(Box::new(v("_48", Sort::Int)), Box::new(Formula::Int(4i128))),
            Formula::Eq(
                Box::new(v("_47", Sort::Int)),
                Box::new(Formula::Sub(
                    Box::new(v("_48", Sort::Int)),
                    Box::new(Formula::Int(4i128)),
                )),
            ),
        ]),
        Formula::Or(vec![
            Formula::Eq(Box::new(Formula::Int(31i128)), Box::new(Formula::Int(0i128))),
            Formula::Lt(Box::new(v("_18", Sort::Int)), Box::new(Formula::Int(31i128))),
        ]),
        Formula::Le(Box::new(v("_7", Sort::Int)), Box::new(Formula::Int(0i128))),
        Formula::Le(Box::new(v("_11", Sort::Int)), Box::new(Formula::Int(1i128))),
        Formula::Le(Box::new(v("_22", Sort::Int)), Box::new(Formula::Int(8i128))),
        Formula::Le(Box::new(v("_53", Sort::Int)), Box::new(Formula::Int(0i128))),
        Formula::Le(Box::new(v("_57", Sort::Int)), Box::new(Formula::Int(1i128))),
        Formula::Le(Box::new(v("_61", Sort::Int)), Box::new(Formula::Int(2i128))),
        Formula::Le(Box::new(v("_65", Sort::Int)), Box::new(Formula::Int(3i128))),
        Formula::Le(Box::new(v("_15", Sort::Int)), Box::new(Formula::Int(15i128))),
        Formula::Le(Box::new(v("_28", Sort::Int)), Box::new(Formula::Int(32i128))),
        Formula::Or(vec![
            Formula::Eq(
                Box::new(v("__trust_mir__discr__37", Sort::Int)),
                Box::new(Formula::Int(0i128)),
            ),
            Formula::Eq(
                Box::new(v("__trust_mir__discr__37", Sort::Int)),
                Box::new(Formula::Int(1i128)),
            ),
        ]),
        Formula::Or(vec![
            Formula::Eq(Box::new(v("_39", Sort::Int)), Box::new(Formula::Int(0i128))),
            Formula::Eq(Box::new(v("_39", Sort::Int)), Box::new(Formula::Int(1i128))),
        ]),
        Formula::Or(vec![
            Formula::Not(Box::new(Formula::Eq(
                Box::new(v("_7", Sort::Int)),
                Box::new(v("_11", Sort::Int)),
            ))),
            Formula::Eq(
                Box::new(v("input*[0;slice]", Sort::Int)),
                Box::new(v("input*[1;slice]", Sort::Int)),
            ),
        ]),
        Formula::Eq(Box::new(v("_4", Sort::Int)), Box::new(v("input__slice_len", Sort::Int))),
        Formula::Eq(
            Box::new(v("_3", Sort::Bool)),
            Box::new(Formula::Lt(Box::new(v("_4", Sort::Int)), Box::new(Formula::Int(6i128)))),
        ),
        Formula::Eq(Box::new(v("_7", Sort::Int)), Box::new(Formula::Int(0i128))),
        Formula::Eq(Box::new(v("_8", Sort::Int)), Box::new(v("input__slice_len", Sort::Int))),
        Formula::Eq(
            Box::new(v("_9", Sort::Bool)),
            Box::new(Formula::Lt(Box::new(v("_7", Sort::Int)), Box::new(v("_8", Sort::Int)))),
        ),
        Formula::Eq(Box::new(v("cmf", Sort::Int)), Box::new(v("input*[0;slice]", Sort::Int))),
        Formula::Eq(Box::new(v("_11", Sort::Int)), Box::new(Formula::Int(1i128))),
        Formula::Eq(Box::new(v("_12", Sort::Int)), Box::new(v("input__slice_len", Sort::Int))),
        Formula::Eq(
            Box::new(v("_13", Sort::Bool)),
            Box::new(Formula::Lt(Box::new(v("_11", Sort::Int)), Box::new(v("_12", Sort::Int)))),
        ),
        Formula::Eq(Box::new(v("flg", Sort::Int)), Box::new(v("input*[1;slice]", Sort::Int))),
        Formula::Eq(
            Box::new(v("_15", Sort::Int)),
            Box::new(Formula::BvToInt(
                Box::new(Formula::BvAnd(
                    Box::new(Formula::IntToBv(Box::new(v("cmf", Sort::Int)), 8)),
                    Box::new(Formula::IntToBv(Box::new(Formula::Int(15i128)), 8)),
                    8,
                )),
                8,
                false,
            )),
        ),
        Formula::Eq(
            Box::new(v("_14", Sort::Bool)),
            Box::new(Formula::Not(Box::new(Formula::Eq(
                Box::new(v("_15", Sort::Int)),
                Box::new(Formula::Int(8i128)),
            )))),
        ),
        Formula::Eq(Box::new(v("_22", Sort::Int)), Box::new(Formula::Int(8i128))),
        Formula::Eq(
            Box::new(v("_23", Sort::Bool)),
            Box::new(Formula::Lt(Box::new(v("_22", Sort::Int)), Box::new(Formula::Int(16i128)))),
        ),
        Formula::Eq(
            Box::new(v("_20", Sort::Int)),
            Box::new(Formula::BvToInt(
                Box::new(Formula::BvShl(
                    Box::new(Formula::IntToBv(Box::new(v("_21", Sort::Int)), 16)),
                    Box::new(Formula::BvAnd(
                        Box::new(Formula::IntToBv(Box::new(Formula::Int(8i128)), 16)),
                        Box::new(Formula::BitVec { value: 15i128, width: 16 }),
                        16,
                    )),
                    16,
                )),
                16,
                false,
            )),
        ),
        Formula::Eq(
            Box::new(v("_19", Sort::Int)),
            Box::new(Formula::BvToInt(
                Box::new(Formula::BvOr(
                    Box::new(Formula::IntToBv(Box::new(v("_20", Sort::Int)), 16)),
                    Box::new(Formula::IntToBv(Box::new(v("_24", Sort::Int)), 16)),
                    16,
                )),
                16,
                false,
            )),
        ),
        Formula::Eq(
            Box::new(v("_25", Sort::Bool)),
            Box::new(Formula::Eq(Box::new(Formula::Int(31i128)), Box::new(Formula::Int(0i128)))),
        ),
        Formula::Eq(
            Box::new(v("_18", Sort::Int)),
            Box::new(Formula::Rem(Box::new(v("_19", Sort::Int)), Box::new(Formula::Int(31i128)))),
        ),
        Formula::Eq(
            Box::new(v("_17", Sort::Bool)),
            Box::new(Formula::Not(Box::new(Formula::Eq(
                Box::new(v("_18", Sort::Int)),
                Box::new(Formula::Int(0i128)),
            )))),
        ),
        Formula::Eq(
            Box::new(v("_28", Sort::Int)),
            Box::new(Formula::BvToInt(
                Box::new(Formula::BvAnd(
                    Box::new(Formula::IntToBv(Box::new(v("flg", Sort::Int)), 8)),
                    Box::new(Formula::IntToBv(Box::new(Formula::Int(32i128)), 8)),
                    8,
                )),
                8,
                false,
            )),
        ),
        Formula::Eq(
            Box::new(v("_27", Sort::Bool)),
            Box::new(Formula::Not(Box::new(Formula::Eq(
                Box::new(v("_28", Sort::Int)),
                Box::new(Formula::Int(0i128)),
            )))),
        ),
        Formula::Eq(Box::new(v("_33", Sort::Int)), Box::new(v("input__slice_len", Sort::Int))),
        Formula::Le(
            Box::new(Formula::Int(0i128)),
            Box::new(Formula::Sub(Box::new(v("_33", Sort::Int)), Box::new(Formula::Int(4i128)))),
        ),
        Formula::Le(
            Box::new(Formula::Sub(Box::new(v("_33", Sort::Int)), Box::new(Formula::Int(4i128)))),
            Box::new(Formula::Int(18446744073709551615i128)),
        ),
        Formula::Eq(
            Box::new(v("_34.0#s14_1", Sort::Int)),
            Box::new(Formula::Sub(Box::new(v("_33", Sort::Int)), Box::new(Formula::Int(4i128)))),
        ),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("_33", Sort::Int))),
        Formula::Le(
            Box::new(v("_33", Sort::Int)),
            Box::new(Formula::Int(18446744073709551615i128)),
        ),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(Formula::Int(4i128))),
        Formula::Le(
            Box::new(Formula::Int(4i128)),
            Box::new(Formula::Int(18446744073709551615i128)),
        ),
        Formula::Eq(Box::new(v("_32", Sort::Int)), Box::new(v("_34.0#s14_1", Sort::Int))),
        Formula::Eq(Box::new(v("_31.0#s15_1", Sort::Int)), Box::new(Formula::Int(2i128))),
        Formula::Eq(Box::new(v("_31@0.0#s15_1", Sort::Int)), Box::new(Formula::Int(2i128))),
        Formula::Eq(Box::new(v("_31.1#s15_1", Sort::Int)), Box::new(v("_32", Sort::Int))),
        Formula::Eq(Box::new(v("_31@0.1#s15_1", Sort::Int)), Box::new(v("_32", Sort::Int))),
        Formula::Eq(Box::new(v("val", Sort::Int)), Box::new(v("_37@0.0#s17_t", Sort::Int))),
        Formula::Eq(
            Box::new(v("out#e_s20_1", Sort::Int)),
            Box::new(v("_37@0.0.0#s17_t", Sort::Int)),
        ),
        Formula::Eq(Box::new(v("used", Sort::Int)), Box::new(v("_37@0.0.1#s17_t", Sort::Int))),
        Formula::Eq(
            Box::new(v("_43", Sort::Int)),
            Box::new(v("deflate__slice_len#s15_t", Sort::Int)),
        ),
        Formula::Eq(
            Box::new(v("_42", Sort::Bool)),
            Box::new(Formula::Not(Box::new(Formula::Eq(
                Box::new(v("used", Sort::Int)),
                Box::new(v("_43", Sort::Int)),
            )))),
        ),
        Formula::Eq(
            Box::new(v("_49.1#s23_1", Sort::Bool)),
            Box::new(Formula::Or(vec![
                Formula::Lt(
                    Box::new(Formula::Sub(
                        Box::new(v("_48", Sort::Int)),
                        Box::new(Formula::Int(4i128)),
                    )),
                    Box::new(Formula::Int(0i128)),
                ),
                Formula::Gt(
                    Box::new(Formula::Sub(
                        Box::new(v("_48", Sort::Int)),
                        Box::new(Formula::Int(4i128)),
                    )),
                    Box::new(Formula::Int(18446744073709551615i128)),
                ),
            ])),
        ),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("_48", Sort::Int))),
        Formula::Le(
            Box::new(v("_48", Sort::Int)),
            Box::new(Formula::Int(18446744073709551615i128)),
        ),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(Formula::Int(4i128))),
        Formula::Le(
            Box::new(Formula::Int(4i128)),
            Box::new(Formula::Int(18446744073709551615i128)),
        ),
        Formula::Eq(Box::new(v("_48", Sort::Int)), Box::new(v("input__slice_len", Sort::Int))),
        Formula::Or(vec![
            Formula::Lt(
                Box::new(Formula::Sub(
                    Box::new(v("_48", Sort::Int)),
                    Box::new(Formula::Int(4i128)),
                )),
                Box::new(Formula::Int(0i128)),
            ),
            Formula::Gt(
                Box::new(Formula::Sub(
                    Box::new(v("_48", Sort::Int)),
                    Box::new(Formula::Int(4i128)),
                )),
                Box::new(Formula::Int(18446744073709551615i128)),
            ),
        ]),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("_48", Sort::Int))),
        Formula::Le(
            Box::new(v("_48", Sort::Int)),
            Box::new(Formula::Int(18446744073709551615i128)),
        ),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(Formula::Int(4i128))),
        Formula::Le(
            Box::new(Formula::Int(4i128)),
            Box::new(Formula::Int(18446744073709551615i128)),
        ),
    ]
}
