// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! THE BYTE-IDENTITY GATE: a differential against the real `bincode 1.3.3`.
//!
//! `tests/fixtures/bincode1_golden.json` holds outputs OBSERVED from the
//! incumbent (bincode 1.3.3, serde 1.0.229, rustc 1.96.1, aarch64-apple-darwin).
//! Nothing in it is a re-derivation or a hand-computed expectation, so a
//! disagreement here is always this crate being wrong about the wire format,
//! never a specification argument.
//!
//! # WHAT IS CHECKED, AND WHY IT IS SPLIT INTO SEPARATE TESTS
//!
//! Each class below is its OWN `#[test]`, so the failure NAME already tells you
//! which kind of drift happened. That distinction matters most for the last
//! class: a diagnostic-string change is a compatibility annoyance, whereas a
//! byte change silently corrupts every proof artifact ever written. If
//! `decode_error_MESSAGES_match_the_incumbent` is the only red test, no byte
//! moved.
//!
//! | test | what a failure means |
//! |---|---|
//! | `encode_output_is_byte_identical_to_the_incumbent` | WIRE DRIFT — the encoder writes different bytes |
//! | `serialized_size_matches_the_incumbent` | the size oracle disagrees with the encoder or with bincode |
//! | `every_encode_case_round_trips_the_recorded_bytes` | DECODER drift — the recorded bytes decode to something that re-encodes differently |
//! | `decode_accept_reject_decisions_match_the_incumbent` | the decoder accepts what bincode rejects, or vice versa |
//! | `decode_error_messages_match_the_incumbent` | MESSAGE-ONLY drift — no byte moved |
//! | `encode_error_decisions_match_the_incumbent` | the encoder errors where bincode succeeds, or vice versa |
//! | `encode_error_messages_match_the_incumbent` | MESSAGE-ONLY drift on the encode side |
//! | `every_fixture_case_and_lane_is_covered` | the instrument itself went quiet |
//!
//! # THE SILENT-INSTRUMENT DEFENCE
//!
//! A differential that quietly skips cases reads green while testing less than
//! it claims. Four things make that impossible here:
//!
//! 1. an unknown case name panics rather than being skipped;
//! 2. the set of case names visited is compared for EQUALITY against the
//!    fixture's own set, so an omission is named;
//! 3. for every single case, the set of config/lane keys visited is compared
//!    for EQUALITY against that case's own `configs` object — a lane dropped
//!    inside a case cannot hide behind a correct case count;
//! 4. the observation counters are compared against the fixture's own `counts`
//!    block.
//!
//! # WHAT THIS FILE DOES *NOT* PIN
//!
//! * Big-endian and native-endian configurations. The fixture is little-endian
//!   only, so nothing here is incumbent-observed for those.
//! * `deserialize_in_place`, the `*_seed` API, `serialize_into` against a
//!   failing writer.
//! * `HashMap` with more than one entry (iteration order is unspecified).
//! * f32/f64 NaN bit patterns are host-determined rather than
//!   format-determined; the round-trip class exercises them but proves a
//!   property of this host, not of the format.

mod support;

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::Debug;

use serde::Serialize;
use serde::de::DeserializeOwned;
use serde_json::Value as J;
use trust_bincode::{DefaultOptions, Options};

use support::types::*;
use support::{hex, unhex};

// ---------------------------------------------------------------------------
// the four configurations
// ---------------------------------------------------------------------------

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Cfg {
    /// `DefaultOptions::new().with_fixint_encoding().allow_trailing_bytes()`
    /// — byte-identical to the free functions. This is what `trust-certify`,
    /// `trust-clean` and `trust-proof-cert` use.
    Fn,
    /// `first-party/trust-ir`'s `clean_expr_codec::codec(64 MiB)`.
    TrustIr,
    /// `DefaultOptions::new()` alone: VARINT and REJECT-trailing. The
    /// documented default; no live caller uses it, which is exactly why it has
    /// to be pinned — a replacement must not silently alias it onto fixint.
    Varint,
    /// The trust-ir shape with a tiny limit so the limit is observable.
    /// Decode section only.
    Limit16,
}

impl Cfg {
    fn fixture_key(self) -> &'static str {
        match self {
            Cfg::Fn => "fn_fixint_allow_trailing",
            Cfg::TrustIr => "trust_ir_fixint_reject_trailing_limit64mib",
            Cfg::Varint => "varint_default",
            Cfg::Limit16 => "fixint_reject_trailing_limit16",
        }
    }

    /// Which of the two recorded inputs this config reads.
    fn uses_varint_input(self) -> bool {
        self == Cfg::Varint
    }
}

/// The three configs the fixture recorded for every encode case.
const ENCODE_CFGS: [Cfg; 3] = [Cfg::Fn, Cfg::TrustIr, Cfg::Varint];

/// The eight decode lanes: four configs x {slice, reader}.
const DECODE_LANES: [(Cfg, bool); 8] = [
    (Cfg::Fn, false),
    (Cfg::TrustIr, false),
    (Cfg::Varint, false),
    (Cfg::Limit16, false),
    (Cfg::Fn, true),
    (Cfg::TrustIr, true),
    (Cfg::Varint, true),
    (Cfg::Limit16, true),
];

fn lane_key(cfg: Cfg, via_reader: bool) -> String {
    if via_reader {
        format!("{}__via_reader", cfg.fixture_key())
    } else {
        cfg.fixture_key().to_string()
    }
}

fn encode_with<T: ?Sized + Serialize>(cfg: Cfg, v: &T) -> trust_bincode::Result<Vec<u8>> {
    match cfg {
        Cfg::Fn => DefaultOptions::new()
            .with_fixint_encoding()
            .allow_trailing_bytes()
            .serialize(v),
        Cfg::TrustIr => DefaultOptions::new()
            .with_fixint_encoding()
            .with_little_endian()
            .reject_trailing_bytes()
            .with_limit(64 * 1024 * 1024)
            .serialize(v),
        Cfg::Varint => DefaultOptions::new().serialize(v),
        Cfg::Limit16 => DefaultOptions::new()
            .with_fixint_encoding()
            .with_little_endian()
            .reject_trailing_bytes()
            .with_limit(16)
            .serialize(v),
    }
}

fn size_with<T: ?Sized + Serialize>(cfg: Cfg, v: &T) -> trust_bincode::Result<u64> {
    match cfg {
        Cfg::Fn => DefaultOptions::new()
            .with_fixint_encoding()
            .allow_trailing_bytes()
            .serialized_size(v),
        Cfg::TrustIr => DefaultOptions::new()
            .with_fixint_encoding()
            .with_little_endian()
            .reject_trailing_bytes()
            .with_limit(64 * 1024 * 1024)
            .serialized_size(v),
        Cfg::Varint => DefaultOptions::new().serialized_size(v),
        Cfg::Limit16 => DefaultOptions::new()
            .with_fixint_encoding()
            .with_little_endian()
            .reject_trailing_bytes()
            .with_limit(16)
            .serialized_size(v),
    }
}

fn decode_with<T: DeserializeOwned>(
    cfg: Cfg,
    via_reader: bool,
    input: &[u8],
) -> trust_bincode::Result<T> {
    match (cfg, via_reader) {
        (Cfg::Fn, false) => DefaultOptions::new()
            .with_fixint_encoding()
            .allow_trailing_bytes()
            .deserialize(input),
        (Cfg::Fn, true) => DefaultOptions::new()
            .with_fixint_encoding()
            .allow_trailing_bytes()
            .deserialize_from(input),
        (Cfg::TrustIr, false) => DefaultOptions::new()
            .with_fixint_encoding()
            .with_little_endian()
            .reject_trailing_bytes()
            .with_limit(64 * 1024 * 1024)
            .deserialize(input),
        (Cfg::TrustIr, true) => DefaultOptions::new()
            .with_fixint_encoding()
            .with_little_endian()
            .reject_trailing_bytes()
            .with_limit(64 * 1024 * 1024)
            .deserialize_from(input),
        (Cfg::Varint, false) => DefaultOptions::new().deserialize(input),
        (Cfg::Varint, true) => DefaultOptions::new().deserialize_from(input),
        (Cfg::Limit16, false) => DefaultOptions::new()
            .with_fixint_encoding()
            .with_little_endian()
            .reject_trailing_bytes()
            .with_limit(16)
            .deserialize(input),
        (Cfg::Limit16, true) => DefaultOptions::new()
            .with_fixint_encoding()
            .with_little_endian()
            .reject_trailing_bytes()
            .with_limit(16)
            .deserialize_from(input),
    }
}

// ---------------------------------------------------------------------------
// fixture accessors — every one of them panics rather than defaulting
// ---------------------------------------------------------------------------

fn jget<'a>(v: &'a J, key: &str, ctx: &str) -> &'a J {
    v.get(key)
        .unwrap_or_else(|| panic!("fixture [{ctx}]: missing key {key:?}"))
}

fn jstr<'a>(v: &'a J, key: &str, ctx: &str) -> &'a str {
    jget(v, key, ctx)
        .as_str()
        .unwrap_or_else(|| panic!("fixture [{ctx}]: key {key:?} is not a string"))
}

fn ju64(v: &J, key: &str, ctx: &str) -> u64 {
    jget(v, key, ctx)
        .as_u64()
        .unwrap_or_else(|| panic!("fixture [{ctx}]: key {key:?} is not a u64"))
}

fn jbool(v: &J, key: &str, ctx: &str) -> bool {
    jget(v, key, ctx)
        .as_bool()
        .unwrap_or_else(|| panic!("fixture [{ctx}]: key {key:?} is not a bool"))
}

fn jkeys(v: &J, ctx: &str) -> BTreeSet<String> {
    v.as_object()
        .unwrap_or_else(|| panic!("fixture [{ctx}]: not an object"))
        .keys()
        .cloned()
        .collect()
}

// ---------------------------------------------------------------------------
// diff classes
// ---------------------------------------------------------------------------

/// One bucket per failure MEANING. Diffs are collected rather than asserted
/// on the spot so that one run reports every disagreement, and so a
/// message-only drift lands in a different bucket than a byte drift.
#[derive(Default)]
struct Diffs {
    encode_bytes: Vec<String>,
    encode_size: Vec<String>,
    roundtrip: Vec<String>,
    decode_decision: Vec<String>,
    decode_message: Vec<String>,
    encode_error_decision: Vec<String>,
    encode_error_message: Vec<String>,
    coverage: Vec<String>,
}

/// Renders at most 20 diffs, then says how many were dropped. A mutation that
/// breaks every case must not produce a megabyte of panic text.
fn render(class: &str, diffs: &[String]) -> String {
    let shown = diffs.len().min(20);
    let mut out = format!("{} {class} disagreement(s) with bincode 1.3.3:\n", diffs.len());
    for d in &diffs[..shown] {
        out.push_str("  - ");
        out.push_str(d);
        out.push('\n');
    }
    if diffs.len() > shown {
        out.push_str(&format!("  ... and {} more\n", diffs.len() - shown));
    }
    out
}

// ---------------------------------------------------------------------------
// the runner
// ---------------------------------------------------------------------------

struct Runner {
    root: J,
    encode: BTreeMap<String, J>,
    decode: BTreeMap<String, J>,
    encode_errors: BTreeMap<String, J>,
    enc_seen: BTreeSet<String>,
    dec_seen: BTreeSet<String>,
    enc_err_seen: BTreeSet<String>,
    enc_obs: usize,
    dec_obs: usize,
    enc_err_obs: usize,
    rt_obs: usize,
    d: Diffs,
}

impl Runner {
    fn load() -> Runner {
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/bincode1_golden.json"
        );
        let text = std::fs::read_to_string(path)
            .unwrap_or_else(|e| panic!("cannot read the golden fixture {path}: {e}"));
        let root: J = serde_json::from_str(&text)
            .unwrap_or_else(|e| panic!("the golden fixture is not valid JSON: {e}"));

        assert_eq!(
            jstr(&root, "schema", "root"),
            "trust.bincode1_golden.v1",
            "unexpected fixture schema"
        );
        assert!(
            !jbool(&root, "encode_only_mode", "root"),
            "the fixture was captured in encode-only mode; its decode section is absent"
        );

        let index = |key: &str| -> BTreeMap<String, J> {
            jget(&root, key, "root")
                .as_array()
                .unwrap_or_else(|| panic!("fixture [root]: {key:?} is not an array"))
                .iter()
                .map(|c| (jstr(c, "name", key).to_string(), c.clone()))
                .collect()
        };

        Runner {
            encode: index("encode"),
            decode: index("decode"),
            encode_errors: index("encode_errors"),
            root,
            enc_seen: BTreeSet::new(),
            dec_seen: BTreeSet::new(),
            enc_err_seen: BTreeSet::new(),
            enc_obs: 0,
            dec_obs: 0,
            enc_err_obs: 0,
            rt_obs: 0,
            d: Diffs::default(),
        }
    }

    // -- encode ------------------------------------------------------------

    /// An encode case whose value type also round-trips as itself.
    fn enc<T: Serialize + DeserializeOwned>(&mut self, name: &str, value: &T) {
        self.enc_impl::<T, T>(name, value);
    }

    /// An encode case whose value is serialized as `S` but round-trips as `D`.
    ///
    /// Two shapes need this and both are legitimate: `&str` decodes as
    /// `String`, and `Bytes` (which reaches `serialize_bytes`) decodes as
    /// `Vec<u8>` — fixture observation O6 records that the incumbent writes
    /// identical bytes for both.
    fn enc_as<S: Serialize + ?Sized, D: Serialize + DeserializeOwned>(
        &mut self,
        name: &str,
        value: &S,
    ) {
        self.enc_impl::<S, D>(name, value);
    }

    fn enc_impl<S: Serialize + ?Sized, D: Serialize + DeserializeOwned>(
        &mut self,
        name: &str,
        value: &S,
    ) {
        let case = self
            .encode
            .get(name)
            .unwrap_or_else(|| panic!("no encode case named {name:?} in the fixture"))
            .clone();
        assert!(
            self.enc_seen.insert(name.to_string()),
            "encode case {name:?} checked twice"
        );

        let configs = jget(&case, "configs", name);
        let mut visited = BTreeSet::new();

        for cfg in ENCODE_CFGS {
            let key = cfg.fixture_key();
            let ctx = format!("{name}/{key}");
            let want = jget(configs, key, &ctx);
            assert!(
                jbool(want, "ok", &ctx),
                "{ctx}: fixture says this did not encode; the encode section is ok-only"
            );
            visited.insert(key.to_string());

            let want_hex = jstr(want, "hex", &ctx);
            let want_len = ju64(want, "len", &ctx);
            let want_size = ju64(want, "serialized_size", &ctx);

            // --- byte identity ---
            match encode_with(cfg, value) {
                Ok(got) => {
                    let got_hex = hex(&got);
                    if got_hex != want_hex {
                        self.d.encode_bytes.push(format!(
                            "{ctx}: bytes\n      want {want_hex}\n      got  {got_hex}"
                        ));
                    }
                    if got.len() as u64 != want_len {
                        self.d.encode_bytes.push(format!(
                            "{ctx}: length want {want_len} got {}",
                            got.len()
                        ));
                    }

                    // --- serialized_size ---
                    match size_with(cfg, value) {
                        Ok(size) => {
                            if size != want_size {
                                self.d.encode_size.push(format!(
                                    "{ctx}: serialized_size want {want_size} got {size}"
                                ));
                            }
                            // Fixture observation O16, re-derived rather than
                            // taken on report: the size oracle and the encoder
                            // must agree with EACH OTHER too.
                            if size != got.len() as u64 {
                                self.d.encode_size.push(format!(
                                    "{ctx}: serialized_size {size} disagrees with the {} bytes actually written",
                                    got.len()
                                ));
                            }
                        }
                        Err(e) => self
                            .d
                            .encode_size
                            .push(format!("{ctx}: serialized_size errored: {e}")),
                    }

                    // --- round-trip: decode the RECORDED bytes, re-encode ---
                    // This is the only lane that exercises the DECODER on
                    // every value shape, so a decode-side endianness or
                    // width bug that the encoder does not share dies here.
                    let recorded = unhex(want_hex);
                    match decode_with::<D>(cfg, false, &recorded) {
                        Ok(v) => match encode_with(cfg, &v) {
                            Ok(re) => {
                                let re_hex = hex(&re);
                                if re_hex != want_hex {
                                    self.d.roundtrip.push(format!(
                                        "{ctx}: re-encode\n      want {want_hex}\n      got  {re_hex}"
                                    ));
                                }
                            }
                            Err(e) => self
                                .d
                                .roundtrip
                                .push(format!("{ctx}: re-encode errored: {e}")),
                        },
                        Err(e) => self.d.roundtrip.push(format!(
                            "{ctx}: the recorded bytes {want_hex} did not decode: {e}"
                        )),
                    }
                    self.rt_obs += 1;
                }
                Err(e) => {
                    self.d
                        .encode_bytes
                        .push(format!("{ctx}: encode errored: {e}"));
                }
            }
            self.enc_obs += 1;
        }

        // Fixture observation O1: the free functions ARE the Fn config. This
        // is what pins the fixint/allow-trailing default of `serialize`.
        let ctx = format!("{name}/free_fn");
        match trust_bincode::serialize(value) {
            Ok(free) => {
                let got_hex = hex(&free);
                let want_hex = jstr(&case, "free_fn_serialize_hex", &ctx);
                if got_hex != want_hex {
                    self.d.encode_bytes.push(format!(
                        "{ctx}: bytes\n      want {want_hex}\n      got  {got_hex}"
                    ));
                }
                let want_fn_cfg = jstr(jget(configs, Cfg::Fn.fixture_key(), &ctx), "hex", &ctx);
                if got_hex != want_fn_cfg {
                    self.d.encode_bytes.push(format!(
                        "{ctx}: free-function bytes differ from the fn config's\n      cfg  {want_fn_cfg}\n      free {got_hex}"
                    ));
                }
            }
            Err(e) => self
                .d
                .encode_bytes
                .push(format!("{ctx}: free serialize errored: {e}")),
        }
        match trust_bincode::serialized_size(value) {
            Ok(sz) => {
                let want = ju64(&case, "free_fn_serialized_size", &ctx);
                if sz != want {
                    self.d
                        .encode_size
                        .push(format!("{ctx}: serialized_size want {want} got {sz}"));
                }
            }
            Err(e) => self
                .d
                .encode_size
                .push(format!("{ctx}: free serialized_size errored: {e}")),
        }
        assert!(
            jbool(&case, "free_fn_matches_fn_config", name),
            "{name}: the fixture itself records the free fn NOT matching the fn config"
        );

        let want_keys = jkeys(configs, name);
        if visited != want_keys {
            self.d.coverage.push(format!(
                "encode {name}: visited {visited:?} but the fixture records {want_keys:?}"
            ));
        }
    }

    // -- decode ------------------------------------------------------------

    fn dec<T: DeserializeOwned + Serialize + Debug>(&mut self, name: &str) {
        let case = self
            .decode
            .get(name)
            .unwrap_or_else(|| panic!("no decode case named {name:?} in the fixture"))
            .clone();
        assert!(
            self.dec_seen.insert(name.to_string()),
            "decode case {name:?} checked twice"
        );

        let fixint = unhex(jstr(&case, "input_fixint_hex", name));
        let varint = unhex(jstr(&case, "input_varint_hex", name));
        // The capture deliberately skipped the io::Read lanes for unlimited
        // configs on one case (a u64::MAX length prefix would make the
        // incumbent's IoReader attempt that allocation), so there is no
        // incumbent observation to compare against there.
        let run_unlimited_readers = jbool(&case, "reader_lanes_run_for_unlimited_configs", name);
        let configs = jget(&case, "configs", name);
        let mut visited = BTreeSet::new();

        for (cfg, via_reader) in DECODE_LANES {
            if via_reader && !run_unlimited_readers && cfg != Cfg::Limit16 {
                continue;
            }
            let key = lane_key(cfg, via_reader);
            let ctx = format!("{name}/{key}");
            let want = jget(configs, &key, &ctx);
            visited.insert(key.clone());

            let input: &[u8] = if cfg.uses_varint_input() {
                &varint
            } else {
                &fixint
            };
            let got = decode_with::<T>(cfg, via_reader, input);

            match jstr(want, "outcome", &ctx) {
                "accept" => match got {
                    Ok(v) => {
                        let want_value = jstr(want, "value", &ctx);
                        let got_value = format!("{v:?}");
                        if got_value != want_value {
                            self.d.decode_decision.push(format!(
                                "{ctx}: decoded value\n      want {want_value}\n      got  {got_value}"
                            ));
                        }
                        // `reencoded_hex` is a hex STRING when the incumbent's
                        // re-encode succeeded and an OBJECT carrying the error
                        // when it did not. That happens for real: a 20-byte
                        // string decoded through the SLICE path (where the
                        // byte limit is dropped) does not re-encode under a
                        // 16-byte limit (where it is not).
                        let re = encode_with(cfg, &v);
                        let want_re = jget(want, "reencoded_hex", &ctx);
                        if let Some(want_hex) = want_re.as_str() {
                            match re {
                                Ok(bytes) => {
                                    let got_hex = hex(&bytes);
                                    if got_hex != want_hex {
                                        self.d.decode_decision.push(format!(
                                            "{ctx}: re-encoded bytes\n      want {want_hex}\n      got  {got_hex}"
                                        ));
                                    }
                                }
                                Err(e) => self.d.decode_decision.push(format!(
                                    "{ctx}: expected the re-encode to give {want_hex}, got error {e}"
                                )),
                            }
                        } else if want_re.is_object() {
                            let werr = jget(want_re, "error", &ctx);
                            match re {
                                Ok(b) => self.d.decode_decision.push(format!(
                                    "{ctx}: expected the re-encode to FAIL, it produced {}",
                                    hex(&b)
                                )),
                                Err(e) => {
                                    let (wd, wdbg) =
                                        (jstr(werr, "display", &ctx), jstr(werr, "debug", &ctx));
                                    if e.to_string() != wd {
                                        self.d.decode_message.push(format!(
                                            "{ctx}: re-encode Display\n      want {wd:?}\n      got  {:?}",
                                            e.to_string()
                                        ));
                                    }
                                    if format!("{e:?}") != wdbg {
                                        self.d.decode_message.push(format!(
                                            "{ctx}: re-encode Debug\n      want {wdbg:?}\n      got  {:?}",
                                            format!("{e:?}")
                                        ));
                                    }
                                }
                            }
                        } else {
                            panic!("{ctx}: unexpected reencoded_hex shape {want_re}");
                        }
                    }
                    Err(e) => self
                        .d
                        .decode_decision
                        .push(format!("{ctx}: expected ACCEPT, got error {e}")),
                },
                "error" => match got {
                    Ok(v) => self
                        .d
                        .decode_decision
                        .push(format!("{ctx}: expected an ERROR, decoded {v:?}")),
                    Err(e) => {
                        // Decision matched; anything below is text only.
                        let wd = jstr(want, "error_display", &ctx);
                        let wdbg = jstr(want, "error_debug", &ctx);
                        if e.to_string() != wd {
                            self.d.decode_message.push(format!(
                                "{ctx}: Display\n      want {wd:?}\n      got  {:?}",
                                e.to_string()
                            ));
                        }
                        if format!("{e:?}") != wdbg {
                            self.d.decode_message.push(format!(
                                "{ctx}: Debug\n      want {wdbg:?}\n      got  {:?}",
                                format!("{e:?}")
                            ));
                        }
                    }
                },
                other => panic!("{ctx}: unknown fixture outcome {other:?}"),
            }
            self.dec_obs += 1;
        }

        let want_keys = jkeys(configs, name);
        if visited != want_keys {
            self.d.coverage.push(format!(
                "decode {name}: visited {visited:?} but the fixture records {want_keys:?}"
            ));
        }
    }

    // -- encode errors -----------------------------------------------------

    fn enc_err<T: ?Sized + Serialize>(&mut self, name: &str, value: &T) {
        let case = self
            .encode_errors
            .get(name)
            .unwrap_or_else(|| panic!("no encode_errors case named {name:?} in the fixture"))
            .clone();
        assert!(
            self.enc_err_seen.insert(name.to_string()),
            "encode-error case {name:?} checked twice"
        );

        let configs = jget(&case, "configs", name);
        for key in jkeys(configs, name) {
            let ctx = format!("{name}/{key}");
            let want = jget(configs, &key, &ctx);
            let cfg = match key.as_str() {
                "fn_fixint_allow_trailing" => Cfg::Fn,
                "trust_ir_fixint_reject_trailing_limit64mib" => Cfg::TrustIr,
                "varint_default" => Cfg::Varint,
                "fixint_reject_trailing_limit16" => Cfg::Limit16,
                other => panic!("{ctx}: unknown config key {other:?}"),
            };
            let got = encode_with(cfg, value);
            if jbool(want, "ok", &ctx) {
                match got {
                    Ok(bytes) => {
                        let got_hex = hex(&bytes);
                        let want_hex = jstr(want, "hex", &ctx);
                        if got_hex != want_hex {
                            self.d.encode_error_decision.push(format!(
                                "{ctx}: bytes\n      want {want_hex}\n      got  {got_hex}"
                            ));
                        }
                        let want_len = ju64(want, "len", &ctx);
                        if bytes.len() as u64 != want_len {
                            self.d.encode_error_decision.push(format!(
                                "{ctx}: length want {want_len} got {}",
                                bytes.len()
                            ));
                        }
                    }
                    Err(e) => self
                        .d
                        .encode_error_decision
                        .push(format!("{ctx}: expected OK, got error {e}")),
                }
            } else {
                match got {
                    Ok(b) => self.d.encode_error_decision.push(format!(
                        "{ctx}: expected an ERROR, encoded {}",
                        hex(&b)
                    )),
                    Err(e) => {
                        let werr = jget(want, "error", &ctx);
                        let wd = jstr(werr, "display", &ctx);
                        let wdbg = jstr(werr, "debug", &ctx);
                        if e.to_string() != wd {
                            self.d.encode_error_message.push(format!(
                                "{ctx}: Display\n      want {wd:?}\n      got  {:?}",
                                e.to_string()
                            ));
                        }
                        if format!("{e:?}") != wdbg {
                            self.d.encode_error_message.push(format!(
                                "{ctx}: Debug\n      want {wdbg:?}\n      got  {:?}",
                                format!("{e:?}")
                            ));
                        }
                    }
                }
            }
            self.enc_err_obs += 1;
        }
    }

    // -- coverage ----------------------------------------------------------

    fn check_coverage(&mut self) {
        let want_enc: BTreeSet<String> = self.encode.keys().cloned().collect();
        if self.enc_seen != want_enc {
            self.d.coverage.push(format!(
                "encode cases never checked: {:?}",
                want_enc.difference(&self.enc_seen).collect::<Vec<_>>()
            ));
        }
        let want_dec: BTreeSet<String> = self.decode.keys().cloned().collect();
        if self.dec_seen != want_dec {
            self.d.coverage.push(format!(
                "decode cases never checked: {:?}",
                want_dec.difference(&self.dec_seen).collect::<Vec<_>>()
            ));
        }
        let want_ee: BTreeSet<String> = self.encode_errors.keys().cloned().collect();
        if self.enc_err_seen != want_ee {
            self.d.coverage.push(format!(
                "encode-error cases never checked: {:?}",
                want_ee.difference(&self.enc_err_seen).collect::<Vec<_>>()
            ));
        }

        let counts = jget(&self.root, "counts", "root").clone();
        let mut cmp = |label: &str, got: u64, key: &str| {
            let want = ju64(&counts, key, "counts");
            if got != want {
                self.d
                    .coverage
                    .push(format!("{label}: fixture says {want}, this run made {got}"));
            }
        };
        cmp("encode cases", self.enc_seen.len() as u64, "encode_cases");
        cmp(
            "encode observations",
            self.enc_obs as u64,
            "encode_observations",
        );
        cmp("decode cases", self.dec_seen.len() as u64, "decode_cases");
        cmp(
            "decode observations",
            self.dec_obs as u64,
            "decode_observations",
        );
        cmp(
            "encode-error cases",
            self.enc_err_seen.len() as u64,
            "encode_error_cases",
        );

        // The fixture's own self-checks, restated so a future recapture that
        // broke them cannot slip past unnoticed.
        for key in [
            "serialized_size_vs_actual_len_mismatches",
            "free_fn_vs_fn_config_mismatches",
        ] {
            let arr = jget(&counts, key, "counts")
                .as_array()
                .unwrap_or_else(|| panic!("fixture [counts]: {key:?} is not an array"));
            if !arr.is_empty() {
                self.d
                    .coverage
                    .push(format!("the fixture itself records counts.{key} = {arr:?}"));
            }
        }
    }
}

// ---------------------------------------------------------------------------
// the case table — every fixture case, with its Rust type
// ---------------------------------------------------------------------------

/// Runs the whole differential once and returns the collected diffs. Cheap
/// enough (sub-millisecond per class) that every test can call it.
fn run() -> Runner {
    let mut h = Runner::load();

    // --- bool, unit -------------------------------------------------------
    h.enc("bool_true", &true);
    h.enc("bool_false", &false);
    h.enc("unit", &());

    // --- integers ---------------------------------------------------------
    h.enc("i8_0", &0i8);
    h.enc("i8_1", &1i8);
    h.enc("i8_neg1", &-1i8);
    h.enc("i8_min", &i8::MIN);
    h.enc("i8_max", &i8::MAX);
    h.enc("u8_0", &0u8);
    h.enc("u8_1", &1u8);
    h.enc("u8_250", &250u8);
    h.enc("u8_251", &251u8);
    h.enc("u8_255", &255u8);
    h.enc("i16_0", &0i16);
    h.enc("i16_1", &1i16);
    h.enc("i16_neg1", &-1i16);
    h.enc("i16_125", &125i16);
    h.enc("i16_126", &126i16);
    h.enc("i16_neg126", &-126i16);
    h.enc("i16_min", &i16::MIN);
    h.enc("i16_max", &i16::MAX);
    h.enc("u16_0", &0u16);
    h.enc("u16_250", &250u16);
    h.enc("u16_251", &251u16);
    h.enc("u16_max", &u16::MAX);
    h.enc("i32_0", &0i32);
    h.enc("i32_1", &1i32);
    h.enc("i32_neg1", &-1i32);
    h.enc("i32_123456", &123456i32);
    h.enc("i32_min", &i32::MIN);
    h.enc("i32_max", &i32::MAX);
    h.enc("u32_0", &0u32);
    h.enc("u32_250", &250u32);
    h.enc("u32_251", &251u32);
    h.enc("u32_65535", &65535u32);
    h.enc("u32_65536", &65536u32);
    h.enc("u32_max", &u32::MAX);
    h.enc("i64_0", &0i64);
    h.enc("i64_1", &1i64);
    h.enc("i64_neg1", &-1i64);
    h.enc("i64_min", &i64::MIN);
    h.enc("i64_max", &i64::MAX);
    h.enc("u64_0", &0u64);
    h.enc("u64_250", &250u64);
    h.enc("u64_251", &251u64);
    h.enc("u64_65535", &65535u64);
    h.enc("u64_65536", &65536u64);
    h.enc("u64_u32max", &(u32::MAX as u64));
    h.enc("u64_u32max_plus1", &(u32::MAX as u64 + 1));
    h.enc("u64_max", &u64::MAX);
    h.enc("usize_0", &0usize);
    h.enc("usize_max", &usize::MAX);
    h.enc("isize_neg1", &-1isize);
    h.enc("isize_min", &isize::MIN);
    h.enc("isize_max", &isize::MAX);
    h.enc("i128_0", &0i128);
    h.enc("i128_1", &1i128);
    h.enc("i128_neg1", &-1i128);
    h.enc("i128_min", &i128::MIN);
    h.enc("i128_max", &i128::MAX);
    h.enc("u128_0", &0u128);
    h.enc("u128_250", &250u128);
    h.enc("u128_251", &251u128);
    h.enc("u128_u64max", &(u64::MAX as u128));
    h.enc("u128_u64max_plus1", &(u64::MAX as u128 + 1));
    h.enc("u128_max", &u128::MAX);

    // --- floats -----------------------------------------------------------
    // Constructed from BITS, never from decimal literals: the fixture records
    // signalling NaNs and both NaN signs, which a literal cannot express.
    h.enc("f32_zero", &f32::from_bits(0x0000_0000));
    h.enc("f32_neg_zero", &f32::from_bits(0x8000_0000));
    h.enc("f32_one", &f32::from_bits(0x3f80_0000));
    h.enc("f32_neg_one", &f32::from_bits(0xbf80_0000));
    h.enc("f32_nan", &f32::from_bits(0x7fc0_0000));
    h.enc("f32_neg_nan", &f32::from_bits(0xffc0_0000));
    h.enc("f32_signalling_nan", &f32::from_bits(0x7f80_0001));
    h.enc("f32_inf", &f32::from_bits(0x7f80_0000));
    h.enc("f32_neg_inf", &f32::from_bits(0xff80_0000));
    h.enc("f32_min", &f32::from_bits(0xff7f_ffff));
    h.enc("f32_max", &f32::from_bits(0x7f7f_ffff));
    h.enc("f32_min_positive", &f32::from_bits(0x0080_0000));
    h.enc("f32_epsilon", &f32::from_bits(0x3400_0000));
    h.enc("f64_zero", &f64::from_bits(0x0000_0000_0000_0000));
    h.enc("f64_neg_zero", &f64::from_bits(0x8000_0000_0000_0000));
    h.enc("f64_one", &f64::from_bits(0x3ff0_0000_0000_0000));
    h.enc("f64_neg_one", &f64::from_bits(0xbff0_0000_0000_0000));
    h.enc("f64_nan", &f64::from_bits(0x7ff8_0000_0000_0000));
    h.enc("f64_neg_nan", &f64::from_bits(0xfff8_0000_0000_0000));
    h.enc("f64_signalling_nan", &f64::from_bits(0x7ff0_0000_0000_0001));
    h.enc("f64_inf", &f64::from_bits(0x7ff0_0000_0000_0000));
    h.enc("f64_neg_inf", &f64::from_bits(0xfff0_0000_0000_0000));
    h.enc("f64_min", &f64::from_bits(0xffef_ffff_ffff_ffff));
    h.enc("f64_max", &f64::from_bits(0x7fef_ffff_ffff_ffff));
    h.enc("f64_min_positive", &f64::from_bits(0x0010_0000_0000_0000));
    h.enc("f64_epsilon", &f64::from_bits(0x3cb0_0000_0000_0000));

    // --- char -------------------------------------------------------------
    h.enc("char_a", &'a');
    h.enc("char_nul", &'\0');
    h.enc("char_del_7f", &'\u{7f}');
    h.enc("char_2byte_e_acute", &'\u{e9}');
    h.enc("char_3byte_hangul", &'\u{d55c}');
    h.enc("char_4byte_gclef", &'\u{1d11e}');
    h.enc("char_max_10ffff", &'\u{10ffff}');

    // --- strings ----------------------------------------------------------
    h.enc("string_empty", &String::new());
    h.enc("string_ascii", &String::from("hello"));
    h.enc("string_multibyte", &String::from("héllo wörld 한글 𝄞"));
    h.enc("string_embedded_nul", &String::from("a\0b"));
    h.enc("string_len251_ascii", &"a".repeat(251));
    h.enc("string_len300_ascii", &"b".repeat(300));
    h.enc_as::<str, String>("str_empty", "");
    h.enc_as::<str, String>("str_ascii", "hello");
    h.enc_as::<str, String>("str_multibyte", "héllo wörld 한글 𝄞");
    h.enc_as::<str, String>("str_embedded_nul", "a\0b");

    // --- byte strings (serialize_bytes) -----------------------------------
    h.enc_as::<Bytes, Vec<u8>>("bytes_empty", &Bytes(vec![]));
    h.enc_as::<Bytes, Vec<u8>>("bytes_123", &Bytes(vec![1, 2, 3]));
    h.enc_as::<Bytes, Vec<u8>>("bytes_len251", &Bytes(vec![0xab; 251]));

    // --- sequences and arrays ---------------------------------------------
    h.enc("vec_u8_empty", &Vec::<u8>::new());
    h.enc("vec_u8_123", &vec![1u8, 2, 3]);
    h.enc("vec_u8_len251", &vec![0xcdu8; 251]);
    h.enc("vec_u8_len300", &vec![0xcdu8; 300]);
    h.enc("vec_u32_123", &vec![1u32, 2, 3]);
    h.enc("vec_i32_neg", &vec![-1i32, 0, 1]);
    h.enc("vec_string", &vec!["a".to_string(), "bb".to_string()]);
    h.enc("vec_vec_u8", &vec![vec![1u8, 2], vec![], vec![3u8]]);
    h.enc("vec_option_u8", &vec![None::<u8>, Some(5u8)]);
    h.enc("array_u8_4", &[1u8, 2, 3, 4]);
    h.enc("array_u8_0", &[0u8; 0]);
    h.enc("array_u32_3", &[1u32, 2, 3]);
    h.enc("array_nested", &[[1u8, 2], [3u8, 4]]);

    // --- tuples -----------------------------------------------------------
    h.enc("tuple_unit", &());
    h.enc("tuple_1", &(7u8,));
    h.enc("tuple_2", &(7u8, 8u32));
    h.enc("tuple_3_mixed", &(1u8, "x".to_string(), true));
    h.enc("tuple_nested", &((1u8, 2u8), (3u8, 4u8)));

    // --- maps and sets ----------------------------------------------------
    h.enc("btreemap_empty", &BTreeMap::<String, u32>::new());
    h.enc("btreemap_1", &BTreeMap::from([("a".to_string(), 1u32)]));
    h.enc(
        "btreemap_3",
        &BTreeMap::from([
            ("a".to_string(), 1u32),
            ("b".to_string(), 2u32),
            ("c".to_string(), 3u32),
        ]),
    );
    h.enc(
        "btreemap_nested",
        &BTreeMap::from([(1u8, vec![1u8, 2]), (2u8, vec![])]),
    );
    // Single entry only: HashMap iteration order is unspecified, so a
    // multi-entry case would not be reproducible. The fixture says so too.
    h.enc(
        "hashmap_single_entry_only",
        &HashMap::from([("k".to_string(), 42u32)]),
    );
    h.enc("btreeset_u8", &BTreeSet::from([1u8, 2, 3]));

    // --- Option / Result --------------------------------------------------
    h.enc("option_u32_none", &None::<u32>);
    h.enc("option_u32_some", &Some(7u32));
    h.enc("option_string_some_empty", &Some(String::new()));
    h.enc("option_option_none", &None::<Option<u32>>);
    h.enc("option_option_some_none", &Some(None::<u32>));
    h.enc("option_option_some_some", &Some(Some(1u32)));
    h.enc("option_unit_some", &Some(()));
    h.enc("result_ok", &Ok::<u32, String>(1));
    h.enc("result_err", &Err::<u32, String>("boom".to_string()));

    // --- structs ----------------------------------------------------------
    h.enc("unit_struct", &UnitStruct);
    h.enc("newtype_struct", &NewtypeStruct(300));
    h.enc("tuple_struct", &TupleStruct(1, "ab".to_string()));
    h.enc(
        "named_struct",
        &NamedStruct {
            a: 1,
            b: "ab".to_string(),
            c: vec![9, 9],
        },
    );
    h.enc(
        "nested_struct",
        &NestedStruct {
            inner: NamedStruct {
                a: 1,
                b: String::new(),
                c: vec![],
            },
            opt: Some(3),
        },
    );

    // --- enums ------------------------------------------------------------
    h.enc("e3_a", &E3::A);
    h.enc("e3_b", &E3::B);
    h.enc("e3_c", &E3::C);
    h.enc("mixed_unit", &Mixed::Unit);
    h.enc("mixed_newtype", &Mixed::New(70000));
    h.enc("mixed_tuple", &Mixed::Tup(1, 2));
    h.enc(
        "mixed_struct",
        &Mixed::Struct {
            x: 1,
            y: "z".to_string(),
        },
    );
    h.enc("bigenum_v0", &BigEnum::V0);
    h.enc("bigenum_v250", &BigEnum::V250);
    h.enc("bigenum_v251", &BigEnum::V251);
    h.enc("bigenum_v255", &BigEnum::V255);
    h.enc("bigenum_v256", &BigEnum::V256);
    h.enc("bigenum_v299", &BigEnum::V299);
    h.enc("bigenum_payload_index300", &BigEnum::Payload(7));

    // --- deep nesting -----------------------------------------------------
    h.enc("nest_depth_8", &nest(8, 7));
    h.enc("nest_depth_64", &nest(64, 7));
    h.enc("nest_depth_256", &nest(256, 7));

    // --- encode errors ----------------------------------------------------
    h.enc_err("vec_u8_len100_over_limit16", &vec![0u8; 100]);
    h.enc_err("string_len20_over_limit16", &"a".repeat(20));
    h.enc_err("sequence_without_known_length", &UnknownLenSeq);

    // --- decode -----------------------------------------------------------
    h.dec::<u32>("control_u32_ok");
    h.dec::<bool>("control_bool_true_ok");
    h.dec::<Option<u32>>("control_option_none_ok");
    h.dec::<Option<u32>>("control_option_some_ok");
    h.dec::<UnitStruct>("control_unit_struct_empty_ok");
    h.dec::<char>("control_char_4byte_ok");
    h.dec::<BigEnum>("control_bigenum_index300_ok");
    h.dec::<u32>("u32_truncated_3_bytes");
    h.dec::<u32>("u32_empty_input");
    h.dec::<u64>("u64_truncated");
    h.dec::<String>("string_truncated_payload");
    h.dec::<NamedStruct>("named_struct_truncated");
    h.dec::<char>("char_truncated_multibyte");
    h.dec::<u32>("u32_trailing_garbage");
    h.dec::<bool>("bool_trailing_garbage");
    h.dec::<String>("string_trailing_garbage");
    h.dec::<bool>("bool_byte_02");
    h.dec::<bool>("bool_byte_ff");
    h.dec::<Option<u32>>("option_tag_02");
    h.dec::<Option<u32>>("option_tag_ff");
    h.dec::<E3>("enum3_discriminant_99");
    h.dec::<E3>("enum3_discriminant_u32max");
    h.dec::<BigEnum>("bigenum_discriminant_400");
    h.dec::<Vec<u8>>("vec_u8_len_u64_max");
    h.dec::<Vec<u8>>("vec_u8_len_100_only_2_present");
    h.dec::<BTreeMap<u8, u8>>("map_len_3_only_1_entry");
    h.dec::<String>("string_len20_vs_limit16_no_payload");
    h.dec::<String>("string_len20_full_payload_vs_limit16");
    h.dec::<String>("string_invalid_utf8");
    h.dec::<String>("string_lone_surrogate_bytes");
    h.dec::<char>("char_invalid_first_byte_80");
    h.dec::<char>("char_invalid_first_byte_ff");
    h.dec::<char>("char_overlong_c080");
    h.dec::<char>("char_above_10ffff_f4908080");
    h.dec::<u64>("varint_extension_byte_ff");
    h.dec::<u64>("varint_u128_marker_for_u64");
    h.dec::<u16>("varint_u32_value_into_u16");
    h.dec::<i32>("varint_u64max_into_i32");
    h.dec::<u64>("varint_noncanonical_251_for_small");
    // The capture used `serde_json::Value`, whose `Deserialize` calls
    // `deserialize_any`. serde_json is a dev-dependency of this crate purely
    // so this case is driven through the EXACT type the incumbent was
    // observed with, rather than a stand-in.
    h.dec::<serde_json::Value>("deserialize_any_unsupported");

    h.check_coverage();
    h
}

// ---------------------------------------------------------------------------
// the gates
// ---------------------------------------------------------------------------

#[test]
fn encode_output_is_byte_identical_to_the_incumbent() {
    let h = run();
    println!(
        "encode byte identity: {} cases x {} configs = {} observations, plus {} free-function cross-checks",
        h.enc_seen.len(),
        ENCODE_CFGS.len(),
        h.enc_obs,
        h.enc_seen.len()
    );
    assert!(
        h.d.encode_bytes.is_empty(),
        "{}",
        render("ENCODED-BYTE", &h.d.encode_bytes)
    );
}

#[test]
fn serialized_size_matches_the_incumbent() {
    let h = run();
    println!(
        "serialized_size: {} observations, each also cross-checked against the bytes actually written",
        h.enc_obs
    );
    assert!(
        h.d.encode_size.is_empty(),
        "{}",
        render("SERIALIZED-SIZE", &h.d.encode_size)
    );
}

/// Decode the RECORDED bytes and re-encode them. This is the only lane that
/// drives the decoder over every value shape in the fixture, so a decode-side
/// width or endianness bug that the encoder does not share fails here and
/// nowhere else.
#[test]
fn every_encode_case_round_trips_the_recorded_bytes() {
    let h = run();
    println!(
        "round-trip: {} recorded-byte decodes re-encoded and compared",
        h.rt_obs
    );
    assert!(
        h.d.roundtrip.is_empty(),
        "{}",
        render("ROUND-TRIP", &h.d.roundtrip)
    );
}

#[test]
fn decode_accept_reject_decisions_match_the_incumbent() {
    let h = run();
    println!(
        "decode decisions: {} cases x up to {} lanes = {} observations",
        h.dec_seen.len(),
        DECODE_LANES.len(),
        h.dec_obs
    );
    assert!(
        h.d.decode_decision.is_empty(),
        "{}",
        render("DECODE-DECISION", &h.d.decode_decision)
    );
}

/// MESSAGE-ONLY. A failure here means a diagnostic string drifted and **no
/// byte moved** — every accept/reject decision still agreed, or this test
/// would not have compared texts at all. Treat it as a compatibility report,
/// not as evidence of wire drift; the byte gates above are the ones that
/// guard proof artifacts.
#[test]
fn decode_error_messages_match_the_incumbent() {
    let h = run();
    println!(
        "decode error texts: Display + Debug compared on every lane the fixture recorded as an error"
    );
    assert!(
        h.d.decode_message.is_empty(),
        "{}",
        render(
            "DECODE-MESSAGE (text only; no byte moved)",
            &h.d.decode_message
        )
    );
}

#[test]
fn encode_error_decisions_match_the_incumbent() {
    let h = run();
    println!(
        "encode-error decisions: {} cases / {} observations",
        h.enc_err_seen.len(),
        h.enc_err_obs
    );
    assert!(
        h.d.encode_error_decision.is_empty(),
        "{}",
        render("ENCODE-ERROR-DECISION", &h.d.encode_error_decision)
    );
}

/// MESSAGE-ONLY, encode side. See `decode_error_messages_match_the_incumbent`.
#[test]
fn encode_error_messages_match_the_incumbent() {
    let h = run();
    assert!(
        h.d.encode_error_message.is_empty(),
        "{}",
        render(
            "ENCODE-ERROR-MESSAGE (text only; no byte moved)",
            &h.d.encode_error_message
        )
    );
}

/// The instrument checking itself: case-name sets, per-case lane-key sets,
/// and observation counters all against the fixture's own bookkeeping.
#[test]
fn every_fixture_case_and_lane_is_covered() {
    let h = run();
    println!(
        "coverage: {} encode / {} decode / {} encode-error cases; {} encode, {} decode, {} encode-error, {} round-trip observations",
        h.enc_seen.len(),
        h.dec_seen.len(),
        h.enc_err_seen.len(),
        h.enc_obs,
        h.dec_obs,
        h.enc_err_obs,
        h.rt_obs
    );
    assert!(
        h.d.coverage.is_empty(),
        "{}",
        render("COVERAGE", &h.d.coverage)
    );
}
