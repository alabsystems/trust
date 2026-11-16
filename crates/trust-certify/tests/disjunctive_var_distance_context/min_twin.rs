// The same twin in the nine-line reproducer of TRUST-KI-1014-1's inflate.rs:911 row,
// as trust-b58a105d generates it (captured as `inflate911_twin.rs` says, from this
// crate's line 9; the second `[V2_VC]` line at `9:25-9:40`):
//
//     pub fn zlib_decompress(input: &[u8]) -> Option<(usize, u8, u8, u8)> {
//         if input.len() < 6 {
//             return None;
//         }
//         let cmf = input[0];
//         let flg = input[1];
//         let deflate = &input[2..input.len() - 4];
//         let trailer = &input[input.len() - 4..];
//         Some((deflate.len(), cmf, flg, trailer[0]))
//     }
//
// trust-6606d3bd certifies both `Overflow(Sub)` twins of this body; trust-1b185739,
// -0a1bc12a, -f22fc270 and -b58a105d certify the first only (TRUST_VERIFY_TRACE_CERTIFIED).
use trust_types::{Formula, Sort};

fn v(name: &str, sort: Sort) -> Formula {
    Formula::Var(name.to_string(), sort)
}

/// The twin's violation, `src/lib.rs:9:25-9:40`.
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
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("cmf", Sort::Int))),
        Formula::Le(Box::new(v("cmf", Sort::Int)), Box::new(Formula::Int(255i128))),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("_25", Sort::Int))),
        Formula::Le(
            Box::new(v("_25", Sort::Int)),
            Box::new(Formula::Int(18446744073709551615i128)),
        ),
        Formula::Ge(Box::new(v("_25", Sort::Int)), Box::new(Formula::Int(0i128))),
        Formula::Le(Box::new(v("_25", Sort::Int)), Box::new(Formula::Int(0i128))),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("flg", Sort::Int))),
        Formula::Le(Box::new(v("flg", Sort::Int)), Box::new(Formula::Int(255i128))),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("_20", Sort::Int))),
        Formula::Le(
            Box::new(v("_20", Sort::Int)),
            Box::new(Formula::Int(18446744073709551615i128)),
        ),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("_6", Sort::Int))),
        Formula::Le(Box::new(v("_6", Sort::Int)), Box::new(Formula::Int(18446744073709551615i128))),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("_9", Sort::Int))),
        Formula::Le(Box::new(v("_9", Sort::Int)), Box::new(Formula::Int(18446744073709551615i128))),
        Formula::Ge(Box::new(v("_9", Sort::Int)), Box::new(Formula::Int(1i128))),
        Formula::Le(Box::new(v("_9", Sort::Int)), Box::new(Formula::Int(1i128))),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("_3", Sort::Int))),
        Formula::Le(Box::new(v("_3", Sort::Int)), Box::new(Formula::Int(18446744073709551615i128))),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("_5", Sort::Int))),
        Formula::Le(Box::new(v("_5", Sort::Int)), Box::new(Formula::Int(18446744073709551615i128))),
        Formula::Ge(Box::new(v("_5", Sort::Int)), Box::new(Formula::Int(0i128))),
        Formula::Le(Box::new(v("_5", Sort::Int)), Box::new(Formula::Int(0i128))),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("_15", Sort::Int))),
        Formula::Le(
            Box::new(v("_15", Sort::Int)),
            Box::new(Formula::Int(18446744073709551615i128)),
        ),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("_10", Sort::Int))),
        Formula::Le(
            Box::new(v("_10", Sort::Int)),
            Box::new(Formula::Int(18446744073709551615i128)),
        ),
        Formula::Eq(Box::new(v("_3", Sort::Int)), Box::new(v("input__slice_len", Sort::Int))),
        Formula::Eq(
            Box::new(v("_2", Sort::Bool)),
            Box::new(Formula::Lt(Box::new(v("_3", Sort::Int)), Box::new(Formula::Int(6i128)))),
        ),
        Formula::Eq(Box::new(v("_5", Sort::Int)), Box::new(Formula::Int(0i128))),
        Formula::Eq(Box::new(v("_6", Sort::Int)), Box::new(v("input__slice_len", Sort::Int))),
        Formula::Eq(
            Box::new(v("_7", Sort::Bool)),
            Box::new(Formula::Lt(Box::new(v("_5", Sort::Int)), Box::new(v("_6", Sort::Int)))),
        ),
        Formula::Eq(Box::new(v("cmf", Sort::Int)), Box::new(v("input*[0;slice]", Sort::Int))),
        Formula::Eq(Box::new(v("_9", Sort::Int)), Box::new(Formula::Int(1i128))),
        Formula::Eq(Box::new(v("_10", Sort::Int)), Box::new(v("input__slice_len", Sort::Int))),
        Formula::Eq(
            Box::new(v("_11", Sort::Bool)),
            Box::new(Formula::Lt(Box::new(v("_9", Sort::Int)), Box::new(v("_10", Sort::Int)))),
        ),
        Formula::Le(
            Box::new(Formula::Int(0i128)),
            Box::new(Formula::Sub(Box::new(v("_15", Sort::Int)), Box::new(Formula::Int(4i128)))),
        ),
        Formula::Le(
            Box::new(Formula::Sub(Box::new(v("_15", Sort::Int)), Box::new(Formula::Int(4i128)))),
            Box::new(Formula::Int(18446744073709551615i128)),
        ),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("_15", Sort::Int))),
        Formula::Le(
            Box::new(v("_15", Sort::Int)),
            Box::new(Formula::Int(18446744073709551615i128)),
        ),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(Formula::Int(4i128))),
        Formula::Le(
            Box::new(Formula::Int(4i128)),
            Box::new(Formula::Int(18446744073709551615i128)),
        ),
        Formula::Eq(Box::new(v("flg", Sort::Int)), Box::new(v("input*[1;slice]", Sort::Int))),
        Formula::Eq(Box::new(v("_15", Sort::Int)), Box::new(v("input__slice_len", Sort::Int))),
        Formula::Not(Box::new(Formula::Lt(
            Box::new(v("input__slice_len", Sort::Int)),
            Box::new(Formula::Int(6i128)),
        ))),
        v("_7", Sort::Bool),
        v("_11", Sort::Bool),
        Formula::Not(Box::new(v("_16.1#s4_2", Sort::Bool))),
        Formula::Or(vec![
            Formula::Lt(Box::new(v("_15", Sort::Int)), Box::new(Formula::Int(4i128))),
            Formula::Eq(
                Box::new(v("_14", Sort::Int)),
                Box::new(Formula::Sub(
                    Box::new(v("_15", Sort::Int)),
                    Box::new(Formula::Int(4i128)),
                )),
            ),
        ]),
        Formula::Or(vec![
            Formula::Lt(Box::new(v("_20", Sort::Int)), Box::new(Formula::Int(4i128))),
            Formula::Eq(
                Box::new(v("_19", Sort::Int)),
                Box::new(Formula::Sub(
                    Box::new(v("_20", Sort::Int)),
                    Box::new(Formula::Int(4i128)),
                )),
            ),
        ]),
        Formula::Le(Box::new(v("_5", Sort::Int)), Box::new(Formula::Int(0i128))),
        Formula::Le(Box::new(v("_9", Sort::Int)), Box::new(Formula::Int(1i128))),
        Formula::Le(Box::new(v("_25", Sort::Int)), Box::new(Formula::Int(0i128))),
        Formula::Or(vec![
            Formula::Not(Box::new(Formula::Eq(
                Box::new(v("_5", Sort::Int)),
                Box::new(v("_9", Sort::Int)),
            ))),
            Formula::Eq(
                Box::new(v("input*[0;slice]", Sort::Int)),
                Box::new(v("input*[1;slice]", Sort::Int)),
            ),
        ]),
        Formula::Eq(Box::new(v("_3", Sort::Int)), Box::new(v("input__slice_len", Sort::Int))),
        Formula::Eq(
            Box::new(v("_2", Sort::Bool)),
            Box::new(Formula::Lt(Box::new(v("_3", Sort::Int)), Box::new(Formula::Int(6i128)))),
        ),
        Formula::Eq(Box::new(v("_5", Sort::Int)), Box::new(Formula::Int(0i128))),
        Formula::Eq(Box::new(v("_6", Sort::Int)), Box::new(v("input__slice_len", Sort::Int))),
        Formula::Eq(
            Box::new(v("_7", Sort::Bool)),
            Box::new(Formula::Lt(Box::new(v("_5", Sort::Int)), Box::new(v("_6", Sort::Int)))),
        ),
        Formula::Eq(Box::new(v("cmf", Sort::Int)), Box::new(v("input*[0;slice]", Sort::Int))),
        Formula::Eq(Box::new(v("_9", Sort::Int)), Box::new(Formula::Int(1i128))),
        Formula::Eq(Box::new(v("_10", Sort::Int)), Box::new(v("input__slice_len", Sort::Int))),
        Formula::Eq(
            Box::new(v("_11", Sort::Bool)),
            Box::new(Formula::Lt(Box::new(v("_9", Sort::Int)), Box::new(v("_10", Sort::Int)))),
        ),
        Formula::Eq(Box::new(v("flg", Sort::Int)), Box::new(v("input*[1;slice]", Sort::Int))),
        Formula::Eq(Box::new(v("_15", Sort::Int)), Box::new(v("input__slice_len", Sort::Int))),
        Formula::Le(
            Box::new(Formula::Int(0i128)),
            Box::new(Formula::Sub(Box::new(v("_15", Sort::Int)), Box::new(Formula::Int(4i128)))),
        ),
        Formula::Le(
            Box::new(Formula::Sub(Box::new(v("_15", Sort::Int)), Box::new(Formula::Int(4i128)))),
            Box::new(Formula::Int(18446744073709551615i128)),
        ),
        Formula::Eq(
            Box::new(v("_16.0#s4_2", Sort::Int)),
            Box::new(Formula::Sub(Box::new(v("_15", Sort::Int)), Box::new(Formula::Int(4i128)))),
        ),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("_15", Sort::Int))),
        Formula::Le(
            Box::new(v("_15", Sort::Int)),
            Box::new(Formula::Int(18446744073709551615i128)),
        ),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(Formula::Int(4i128))),
        Formula::Le(
            Box::new(Formula::Int(4i128)),
            Box::new(Formula::Int(18446744073709551615i128)),
        ),
        Formula::Eq(Box::new(v("_14", Sort::Int)), Box::new(v("_16.0#s4_2", Sort::Int))),
        Formula::Eq(Box::new(v("_13.0#s5_1", Sort::Int)), Box::new(Formula::Int(2i128))),
        Formula::Eq(Box::new(v("_13@0.0#s5_1", Sort::Int)), Box::new(Formula::Int(2i128))),
        Formula::Eq(Box::new(v("_13.1#s5_1", Sort::Int)), Box::new(v("_14", Sort::Int))),
        Formula::Eq(Box::new(v("_13@0.1#s5_1", Sort::Int)), Box::new(v("_14", Sort::Int))),
        Formula::Eq(
            Box::new(v("_21.1#s6_1", Sort::Bool)),
            Box::new(Formula::Or(vec![
                Formula::Lt(
                    Box::new(Formula::Sub(
                        Box::new(v("_20", Sort::Int)),
                        Box::new(Formula::Int(4i128)),
                    )),
                    Box::new(Formula::Int(0i128)),
                ),
                Formula::Gt(
                    Box::new(Formula::Sub(
                        Box::new(v("_20", Sort::Int)),
                        Box::new(Formula::Int(4i128)),
                    )),
                    Box::new(Formula::Int(18446744073709551615i128)),
                ),
            ])),
        ),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("_20", Sort::Int))),
        Formula::Le(
            Box::new(v("_20", Sort::Int)),
            Box::new(Formula::Int(18446744073709551615i128)),
        ),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(Formula::Int(4i128))),
        Formula::Le(
            Box::new(Formula::Int(4i128)),
            Box::new(Formula::Int(18446744073709551615i128)),
        ),
        Formula::Eq(Box::new(v("_20", Sort::Int)), Box::new(v("input__slice_len", Sort::Int))),
        Formula::Or(vec![
            Formula::Lt(
                Box::new(Formula::Sub(
                    Box::new(v("_20", Sort::Int)),
                    Box::new(Formula::Int(4i128)),
                )),
                Box::new(Formula::Int(0i128)),
            ),
            Formula::Gt(
                Box::new(Formula::Sub(
                    Box::new(v("_20", Sort::Int)),
                    Box::new(Formula::Int(4i128)),
                )),
                Box::new(Formula::Int(18446744073709551615i128)),
            ),
        ]),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(v("_20", Sort::Int))),
        Formula::Le(
            Box::new(v("_20", Sort::Int)),
            Box::new(Formula::Int(18446744073709551615i128)),
        ),
        Formula::Le(Box::new(Formula::Int(0i128)), Box::new(Formula::Int(4i128))),
        Formula::Le(
            Box::new(Formula::Int(4i128)),
            Box::new(Formula::Int(18446744073709551615i128)),
        ),
    ]
}
