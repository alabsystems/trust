use super::*;

#[test]
fn giant_integer_tokens_keep_their_exact_value_and_numeric_kind() {
    for token in
        ["18446744073709551617", "-9223372036854775809", "340282366920938463463374607431768211457"]
    {
        let raw = format!("{{\"number\":{token}}}");
        let value = parse(raw.as_bytes()).expect("valid integer JSON");
        assert!(value["number"].is_number());
        assert_eq!(value["number"].to_string(), token, "token {token}");
    }
}

#[test]
fn private_number_token_objects_remain_objects_at_every_depth() {
    let raw = br#"{"outer":[{"$serde_json::private::Number":"2"}]}"#;
    let value = parse(raw).expect("ordinary object key is not numeric syntax");
    assert!(value["outer"][0].is_object());
    assert_eq!(value["outer"][0]["$serde_json::private::Number"], "2");
}

#[test]
fn valid_unknown_metadata_is_not_limited_to_serde_default_depth() {
    let raw = "[".repeat(500) + "null" + &"]".repeat(500);
    let value = parse(raw.as_bytes()).expect("bounded original JSON metadata depth");
    let mut current = &value;
    let mut levels = 0;
    while let Some(array) = current.as_array() {
        assert_eq!(array.len(), 1);
        levels += 1;
        current = &array[0];
    }
    assert_eq!(levels, 500);
    assert!(current.is_null());
}

#[test]
fn strict_number_grammar_and_container_delimiters_are_preserved() {
    for raw in [
        "+2",
        "02",
        "-",
        "1.",
        "1e",
        "1e+",
        ".1",
        "--2",
        "NaN",
        "Infinity",
        "[1,]",
        "{\"a\":1,}",
        "[1 2]",
        "{}{}",
        "true false",
    ] {
        assert!(parse(raw.as_bytes()).is_err(), "accepted {raw}");
    }
    for raw in ["0", "-0", "2", "2.0", "2e0", "-2.5e+10", "[true,false,null,{}]", "{\"empty\":[]}"]
    {
        assert!(parse(raw.as_bytes()).is_ok(), "refused {raw}");
    }
    assert!(parse(br#"{"a":1,"\u0061":2}"#).is_err());
}

#[test]
fn source_object_order_is_preserved_but_canonical_digest_order_is_sorted() {
    let value = parse(br#"{"z":1,"a":2}"#).unwrap();
    assert_eq!(
        value.as_object().unwrap().keys().map(String::as_str).collect::<Vec<_>>(),
        ["z", "a"]
    );
    assert_eq!(ascii_canonical(&value), r#"{"a":2,"z":1}"#);
}

#[test]
fn string_tokens_keep_valid_pairs_and_refuse_raw_unpaired_surrogates_and_controls() {
    assert_eq!(parse(br#""\ud83d\ude00""#).unwrap(), "😀");
    assert_eq!(parse(br#""\u0000""#).unwrap().as_str().unwrap().as_bytes(), b"\0");
    for raw in [
        br#""\ud800b""#.as_slice(),
        br#""\udcff""#,
        br#""\udfff""#,
        b"\"raw\0control\"",
        b"\"\xff\"",
        br#""\u00gg""#,
    ] {
        assert!(parse(raw).is_err(), "invalid lexical string {raw:?}");
    }
}

#[test]
fn private_number_object_keys_cannot_enter_the_numeric_token_path() {
    for raw in [
        br#"{"$serde_json::private::Number":"18446744073709551617"}"#.as_slice(),
        br#"{"\u0024serde_json::private::Number":"2.0"}"#,
        br#"{"$serde_json::private::Number":2}"#,
    ] {
        assert!(parse(raw).unwrap().is_object());
    }
    let numeric = parse(b"1e400").expect("finite JSON number lexeme need not fit a binary float");
    assert!(numeric.is_number());
    assert!(numeric.to_string().contains('e'));
}

#[test]
fn short_lexical_grammar_matches_the_independent_standard_decoder() {
    // At this length there can be no duplicate object key or private-number
    // pseudo-object, so both parsers must have identical acceptance and values.
    let alphabet = b"[]{}:,0\"a";
    let mut accepted = 0;
    let mut refused = 0;
    for length in 0..=5 {
        for mut index in 0..alphabet.len().pow(length) {
            let mut raw = vec![0; length as usize];
            for byte in &mut raw {
                *byte = alphabet[index % alphabet.len()];
                index /= alphabet.len();
            }
            match (parse(&raw), serde_json::from_slice::<serde_json::Value>(&raw)) {
                (Ok(actual), Ok(expected)) => {
                    assert_eq!(actual.to_string(), expected.to_string(), "input {raw:?}");
                    accepted += 1;
                }
                (Err(_), Err(_)) => refused += 1,
                (actual, expected) => {
                    panic!("grammar mismatch for {raw:?}: native {actual:?}, standard {expected:?}")
                }
            }
        }
    }
    assert!(
        accepted > 20 && refused > 10_000,
        "nonvacuous grammar census: {accepted} accepted/{refused} refused"
    );
}

#[test]
fn direct_parser_enforces_the_same_16_mib_receipt_byte_boundary() {
    let raw = vec![b' '; crate::MAX_RECEIPT_BYTES as usize + 1];
    assert!(parse(&raw).unwrap_err().to_string().contains("16 MiB"));
}

#[test]
fn default_stack_processes_cover_deep_success_and_refused_tree_cleanup() {
    for mode in ["boundary", "refusal", "native-values"] {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--ignored", "--exact", "json::tests::deep_json_process_actor", "--nocapture"])
            .env("TRUST_STAGE_JSON_TEST_ACTOR", mode)
            .env_remove("RUST_MIN_STACK")
            .env_remove("TRUST_STACK_SIZE")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "default-stack {mode}: {}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

#[test]
#[ignore = "child-only default-stack process actor, invoked by its owning test"]
fn deep_json_process_actor() {
    match std::env::var("TRUST_STAGE_JSON_TEST_ACTOR").unwrap().as_str() {
        "boundary" => {
            for depth in [128, 500, MAX_NESTING] {
                for (open, close) in [("[", "]"), ("{\"key\":", "}")] {
                    let raw = open.repeat(depth) + "null" + &close.repeat(depth);
                    let value = parse(raw.as_bytes()).expect("bounded deep JSON");
                    assert_eq!(ascii_canonical(&value), raw);
                    let copy = value.clone();
                    assert_eq!(value, copy);
                    assert_eq!(format!("{value:?}"), raw);
                    let python = python_repr(&value);
                    let expected = if open == "[" {
                        "[".repeat(depth) + "None" + &"]".repeat(depth)
                    } else {
                        "{'key': ".repeat(depth) + "None" + &"}".repeat(depth)
                    };
                    assert_eq!(python, expected);
                    drop(copy);
                    drop(value);
                }
            }
        }
        "refusal" => {
            let excessive = "[".repeat(MAX_NESTING + 1) + "null" + &"]".repeat(MAX_NESTING + 1);
            assert!(parse(excessive.as_bytes()).is_err());
            assert!(parse("[".repeat(100_000).as_bytes()).is_err());
            let complete = "[".repeat(MAX_NESTING) + "null" + &"]".repeat(MAX_NESTING) + "x";
            assert!(parse(complete.as_bytes()).is_err());
            let nested = "[".repeat(MAX_NESTING - 1) + "null" + &"]".repeat(MAX_NESTING - 1);
            let partial_array = format!("[{nested},\"unterminated");
            assert!(parse(partial_array.as_bytes()).is_err());
            let partial_object = format!("{{\"same\":{nested},\"same\":0}}");
            assert!(parse(partial_object.as_bytes()).is_err());
        }
        "native-values" => {
            // Public diagnostic values can be assembled without the receipt
            // parser. Their operations must not reintroduce recursive stack
            // growth outside the parser's 1000-container bound.
            let mut value = Value::Null;
            for _ in 0..100_000 {
                value = Value::Array(vec![value]);
            }
            let copy = value.clone();
            assert_eq!(value, copy);
            assert_eq!(value.to_string().len(), 200_004);
            assert_eq!(format!("{copy:?}").len(), 200_004);
            assert_eq!(python_repr(&value).len(), 200_004);
            drop(copy);
            drop(value);
        }
        other => panic!("unknown owned actor mode {other}"),
    }
}

#[test]
fn python_repr_matches_frozen_original_unicode_and_float_oracle() {
    use std::io::Read as _;
    let mut raw = Vec::new();
    flate2::read::GzDecoder::new(&include_bytes!("../../tests/data/python-repr.json.gz")[..])
        .take(1024 * 1024)
        .read_to_end(&mut raw)
        .unwrap();
    assert_eq!(
        crate::hash(&raw),
        "0e3a6fe6a227f638566a6c5196fa80b2e64b96ae8c095e0ab7c1be3c54e9ec55"
    );
    let oracle = parse(&raw).unwrap();
    assert_eq!(oracle["schema"], "trust.stage-receipt.python-repr.v1");
    assert_eq!(oracle["python"], "3.13.18");
    assert_eq!(oracle["unicode"], "15.1.0");
    assert_eq!(
        oracle["python_image_sha256"],
        "747ca8797fea0949368e9e39d0f75b1eeadbae6c24edadda792ae22299e47a01"
    );
    let cases = oracle["cases"].as_array().unwrap();
    assert_eq!(cases.len(), 7586);
    for (index, case) in cases.iter().enumerate() {
        let token = case["json"].as_str().unwrap();
        let value = parse(token.as_bytes()).unwrap();
        assert_eq!(
            python_repr(&value),
            case["repr"].as_str().unwrap(),
            "Python oracle {index}: {token}"
        );
    }
}

#[test]
fn numeric_storage_and_object_identity_are_lossless_without_float_coercions() {
    let integer = "9".repeat(2048);
    let exponent = "1e".to_owned() + &"9".repeat(100_000);
    for token in [&integer, &exponent, "-0", "2.0", "2e0", "1e400"] {
        let value = parse(token.as_bytes()).unwrap();
        assert_eq!(value.to_string(), token);
        let copy = value.clone();
        assert_eq!(copy, value);
        assert_eq!(copy.to_string(), token);
    }
    let a = parse(br#"{"z":1,"a":{"second":false,"first":null}}"#).unwrap();
    let b = parse(br#"{"a":{"first":null,"second":false},"z":1}"#).unwrap();
    assert_eq!(a, b, "object equality is independent of insertion order");
    assert_ne!(a.to_string(), b.to_string(), "round trips retain their own order");
    let mut edited = a.clone();
    edited["z"] = Value::Bool(true);
    assert_eq!(
        edited.as_object().unwrap().keys().map(String::as_str).collect::<Vec<_>>(),
        ["z", "a"]
    );
    assert_ne!(a, edited);
}

#[test]
fn isolated_native_string_decoder_preserves_incumbent_acceptance_for_every_utf16_unit() {
    for code in 0..=u16::MAX {
        let raw = format!("\"\\u{code:04x}\"");
        match (parse(raw.as_bytes()), serde_json::from_str::<String>(&raw)) {
            (Ok(native), Ok(original)) => assert_eq!(native.as_str(), Some(original.as_str())),
            (Err(_), Err(_)) => {}
            (native, original) => {
                panic!("UTF-16 {code:04x}: native {native:?}, original {original:?}")
            }
        }
    }
    for byte in 0..=u8::MAX {
        let raw = [b'"', byte, b'"'];
        assert_eq!(
            parse(&raw).is_ok(),
            serde_json::from_slice::<String>(&raw).is_ok(),
            "byte {byte:02x}"
        );
    }
}

#[test]
fn integer_boundaries_match_the_original_read_with_its_unchanged_default_limit() {
    use std::io::Read as _;
    let mut raw = Vec::new();
    flate2::read::GzDecoder::new(&include_bytes!("../../tests/data/integer-boundary.json.gz")[..])
        .take(1024 * 1024)
        .read_to_end(&mut raw)
        .unwrap();
    assert_eq!(
        crate::hash(&raw),
        "bab4da9671f5db09e4122c7dcf0beb0dc3b64757e211f123c2cd496dad32554e"
    );
    let oracle = parse(&raw).unwrap();
    assert_eq!(oracle["schema"], "trust.stage-receipt.integer-boundary.v1");
    assert_eq!(oracle["max_int_digits"].as_u64(), Some(4300));
    assert_eq!(
        oracle["reader_sha256"],
        "068819ea74788a22058e0662878ff1cf6fb9354d63fc113b0e7410a389888c6c"
    );
    assert_eq!(
        oracle["python_image_sha256"],
        "747ca8797fea0949368e9e39d0f75b1eeadbae6c24edadda792ae22299e47a01"
    );
    let cases = oracle["cases"].as_array().unwrap();
    assert_eq!(cases.len(), 16);
    for (index, case) in cases.iter().enumerate() {
        let native = parse(case["json"].as_str().unwrap().as_bytes());
        assert_eq!(
            native.is_ok(),
            case["accepted"].as_bool().unwrap(),
            "original read boundary {index}"
        );
        if let Ok(native) = native {
            assert_eq!(
                python_repr(&native["number"]),
                case["repr"].as_str().unwrap(),
                "original read repr {index}"
            );
        }
    }
}
