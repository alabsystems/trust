// Trust (UTF8-ENCODE-UTF16-SHORTBUF-1, 2026-10-05): `char::encode_utf16` into a
// caller's buffer, pinned on REAL extracted MIR (`-Ztrust-dump=mir-only` on the
// stage 1 of `dc15b882f6`, main plus wave 16; `fixtures/char_encode_utf16/*.json`,
// named `<revision>_<fn>` after the revision and function of
// `tests/ui/trust/policy_b/char_encode_utf16_short_buffer.rs` that produced them).
//
// BEFORE: every charged function built rc=0 under the default policy at `-O0` and
// `-O3`, its one row a runtime-checked panic-freedom row citing the bundled
// `encode_utf16_raw`, and `param_buf('\u{1F600}', &mut [0u16; 1])` panics
// ("encode_utf16: need 2 bytes to encode U+1F600 but buffer has just 1"). vcgen
// minted no row for the call. These tests pin the fail-closed
// `Call::encode_utf16::panic-freedom-unverified` row it now mints at the root call,
// and that the total `str::encode_utf16` iterator and `len_utf16` get none.
use trust_types::*;
use trust_vcgen::generate_vcs;

fn load(name: &str) -> VerifiableFunction {
    let path =
        format!("{}/tests/fixtures/char_encode_utf16/{name}.json", env!("CARGO_MANIFEST_DIR"));
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("fixture MIR must deserialize")
}

fn utf16_rows(name: &str) -> usize {
    generate_vcs(&load(name))
        .iter()
        .filter(|vc| {
            matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
                if kind == "Call::encode_utf16::panic-freedom-unverified")
        })
        .count()
}

#[test]
fn a_caller_buffer_handed_to_char_encode_utf16_is_charged() {
    for name in ["param_param_buf", "local_local_buf", "ufcs_ufcs_buf"] {
        assert_eq!(utf16_rows(name), 1, "{name}: the root call must carry the fail-closed row");
    }
}

#[test]
fn guarded_and_two_unit_buffers_are_refused_too() {
    // THE OVER-REFUSAL (docs/DECISION_QUEUE.md, UTF8-ENCODE-UTF16-SHORTBUF-1): no
    // buffer length is modeled, so a guarded call and a `[0u16; 2]` buffer, which
    // cannot panic, keep the row — parity with `encode_utf8` and a 4-byte buffer.
    for name in ["guarded_guarded_buf", "two_two_buf"] {
        assert_eq!(utf16_rows(name), 1, "{name}");
    }
}

#[test]
fn the_total_str_iterator_and_length_queries_are_not_charged() {
    // `s.encode_utf16()` is core's `EncodeUtf16` iterator: its `next` calls
    // `encode_utf16` with its own two-unit buffer, inside the bundle, which this
    // root-call row never sees.
    for name in
        ["total_str_count", "total_char_len", "total_utf8_unaffected", "collect_str_collect"]
    {
        assert_eq!(utf16_rows(name), 0, "{name}: no `encode_utf16` row expected");
    }
}
