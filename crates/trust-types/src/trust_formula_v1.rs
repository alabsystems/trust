// trust-types/trust_formula_v1.rs: Lowering from trust_types::Formula into the
// `trust_wp.trust-formula.v1` claim envelope consumed by trust-wp's native
// replay decoder (`decode_trust_formula_v1_claim`).
//
// This is the `TrustFormulaV1` claim lowering that lets the trust-wp
// verifier-api bridge and the compiler turn a symbolic
// (`trust-types.Formula@1`) postcondition / precondition / loop-invariant
// predicate into a replayable typed pure-expression claim. It is serde-only
// (no `trust_wp_core` dependency), so it compiles in every build configuration.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::{collections::BTreeMap, fmt};

use serde::{
    Deserialize, Deserializer,
    de::{self, MapAccess, SeqAccess, Visitor},
};
use serde_json::{Map, Value};

use crate::formula::{Formula, Sort};

/// Stable schema tag for the `trust_wp.trust-formula.v1` claim envelope that
/// trust-wp's `decode_trust_formula_v1_claim` replay decoder accepts.
///
/// Canonical Trust producers emit this underscore spelling. A downstream
/// compatibility decoder may accept the historical hyphen spelling, but that
/// tolerance is not part of the producer contract or this common ingress.
pub const TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION: &str = "trust_wp.trust-formula.v1";

/// Return whether `name` is one opaque identifier token in trust-wp's contract
/// parser and cannot be reinterpreted as parser syntax.
///
/// The stable `TrustWpPureExprV1` serializer has no escaping layer, so its
/// variable names must be narrower than TrustFormula/SMT symbols: exact ASCII
/// `[A-Za-z_][A-Za-z0-9_]*`, excluding every keyword recognized by the sibling
/// contract parser. In particular, `.` is postfix field/method syntax and `#`
/// is not part of the sibling's base identifier token.
pub fn trust_wp_pure_expr_v1_opaque_identifier(name: &str) -> bool {
    let bytes = name.as_bytes();
    let Some((first, rest)) = bytes.split_first() else {
        return false;
    };
    (first.is_ascii_alphabetic() || *first == b'_')
        && rest.iter().all(|byte| byte.is_ascii_alphanumeric() || *byte == b'_')
        && !matches!(
            name,
            // Complete `try_consume_keyword` set in trust-wp's contract parser.
            "as" | "box"
                | "const"
                | "dyn"
                | "else"
                | "exists"
                | "false"
                | "forall"
                | "if"
                | "let"
                | "match"
                | "mut"
                | "old"
                | "ref"
                | "true"
                | "use"
        )
}

/// Canonicalize a prebuilt TrustFormulaV1 envelope after validating the exact
/// arithmetic-free replay fragment used by Trust's machine-contract lane.
///
/// This is the common ingress check for the compiler and the trust-wp adapter.
/// It deliberately lives below both so a prebuilt JSON envelope cannot bypass
/// the arithmetic refusal enforced by their source-AST lowering paths.
pub fn canonical_arithmetic_free_trust_formula_v1_payload(value: &Value) -> Result<String, String> {
    validate_arithmetic_free_trust_formula_v1(value)?;
    serde_json::to_string(value)
        .map_err(|err| format!("could not serialize canonical TrustFormulaV1 predicate: {err}"))
}

/// Parse and canonicalize a raw TrustFormulaV1 payload without accepting
/// duplicate object keys.
///
/// `serde_json::Value` normally keeps only the last duplicate key. That is a
/// poor boundary for proof-bearing input because two readers can otherwise
/// disagree about which schema/body/operator was committed. Raw TrustIr proof
/// formulas therefore enter through this duplicate-rejecting parser before the
/// same arithmetic-free validator used for already-typed JSON values.
pub fn parse_arithmetic_free_trust_formula_v1_payload(payload: &str) -> Result<String, String> {
    let value = parse_unique_proof_json_payload(payload)?;
    canonical_arithmetic_free_trust_formula_v1_payload(&value)
}

/// Parse proof-bearing JSON without accepting duplicate object keys.
///
/// Callers that subsequently decode a schema-specific value must still apply
/// that schema's strict field and semantic validation. This helper only
/// preserves a single, unambiguous JSON interpretation at raw-text ingress.
pub fn parse_unique_proof_json_payload(payload: &str) -> Result<Value, String> {
    let UniqueJsonValue(value) = crate::json_depth::from_str_deep::<UniqueJsonValue>(payload)
        .map_err(|err| format!("invalid proof JSON payload: {err}"))?;
    Ok(value)
}

/// Validate the arithmetic-free legacy TrustWpPureExprV1 stable-text surface.
///
/// This deliberately recognizes only identifiers, bool/int literals,
/// parentheses, boolean connectives, comparisons, and implication. Besides
/// additive arithmetic, it refuses every multiplicative, shift, bitwise,
/// cast/type-ascription, call, and postfix surface that the sibling's broader
/// contract parser could otherwise reinterpret. A minus sign is accepted only
/// when it is immediately attached to an integer literal in operand position.
pub fn reject_trust_wp_pure_expr_v1_text_arithmetic(payload: &str) -> Result<(), String> {
    let bytes = payload.as_bytes();
    let mut index = 0;
    let mut open_parens = 0usize;
    let mut expects_operand = true;
    let mut saw_operand = false;

    while index < bytes.len() {
        while bytes.get(index).is_some_and(u8::is_ascii_whitespace) {
            index += 1;
        }
        if index == bytes.len() {
            break;
        }

        if expects_operand {
            match bytes[index] {
                b'(' => {
                    open_parens += 1;
                    index += 1;
                }
                b'!' if bytes.get(index + 1) != Some(&b'=') => {
                    index += 1;
                }
                b'-' if bytes.get(index + 1).is_some_and(u8::is_ascii_digit) => {
                    index += 1;
                    consume_stable_text_integer(bytes, &mut index, true)?;
                    expects_operand = false;
                    saw_operand = true;
                }
                byte if byte.is_ascii_digit() => {
                    consume_stable_text_integer(bytes, &mut index, false)?;
                    expects_operand = false;
                    saw_operand = true;
                }
                byte if byte.is_ascii_alphabetic() || byte == b'_' => {
                    let start = index;
                    index += 1;
                    while bytes
                        .get(index)
                        .is_some_and(|byte| byte.is_ascii_alphanumeric() || *byte == b'_')
                    {
                        index += 1;
                    }
                    let name = std::str::from_utf8(&bytes[start..index])
                        .expect("ASCII identifier bytes are valid UTF-8");
                    if !matches!(name, "true" | "false")
                        && !trust_wp_pure_expr_v1_opaque_identifier(name)
                    {
                        return Err(format!(
                            "TrustWpPureExprV1 stable text identifier `{name}` is reserved by the downstream contract parser"
                        ));
                    }
                    expects_operand = false;
                    saw_operand = true;
                }
                _ => {
                    return Err(stable_text_fragment_error(bytes, index, true));
                }
            }
            continue;
        }

        if bytes[index] == b')' {
            if open_parens == 0 {
                return Err(format!(
                    "TrustWpPureExprV1 stable text has an unmatched `)` at byte {index}"
                ));
            }
            open_parens -= 1;
            index += 1;
            continue;
        }

        if bytes[index..].starts_with(b"<<") || bytes[index..].starts_with(b">>") {
            return Err(stable_text_fragment_error(bytes, index, false));
        }
        let operator_len = if bytes[index..].starts_with(b"==>") {
            Some(3)
        } else if bytes[index..].starts_with(b"&&")
            || bytes[index..].starts_with(b"||")
            || bytes[index..].starts_with(b"==")
            || bytes[index..].starts_with(b"!=")
            || bytes[index..].starts_with(b"<=")
            || bytes[index..].starts_with(b">=")
        {
            Some(2)
        } else if matches!(bytes[index], b'<' | b'>') {
            Some(1)
        } else {
            None
        };
        if let Some(operator_len) = operator_len {
            index += operator_len;
            expects_operand = true;
            continue;
        }

        return Err(stable_text_fragment_error(bytes, index, false));
    }

    if !saw_operand {
        return Err("TrustWpPureExprV1 stable text is empty".to_string());
    }
    if expects_operand {
        return Err("TrustWpPureExprV1 stable text ends where an operand is required".to_string());
    }
    if open_parens != 0 {
        return Err(format!(
            "TrustWpPureExprV1 stable text has {open_parens} unclosed parenthesis group(s)"
        ));
    }
    Ok(())
}

fn consume_stable_text_integer(
    bytes: &[u8],
    index: &mut usize,
    negative: bool,
) -> Result<(), String> {
    let start = *index;
    let mut previous_was_underscore = false;
    while let Some(byte) = bytes.get(*index) {
        if byte.is_ascii_digit() {
            previous_was_underscore = false;
            *index += 1;
        } else if *byte == b'_' && !previous_was_underscore {
            previous_was_underscore = true;
            *index += 1;
        } else {
            break;
        }
    }
    if *index == start || previous_was_underscore {
        return Err(format!("TrustWpPureExprV1 integer literal at byte {start} is malformed"));
    }
    let magnitude: String = bytes[start..*index]
        .iter()
        .filter(|byte| **byte != b'_')
        .map(|byte| char::from(*byte))
        .collect();
    let magnitude = magnitude
        .parse::<u128>()
        .map_err(|_| format!("TrustWpPureExprV1 integer literal at byte {start} is outside i64"))?;
    let max_magnitude = if negative { i64::MAX as u128 + 1 } else { i64::MAX as u128 };
    if magnitude > max_magnitude {
        return Err(format!("TrustWpPureExprV1 integer literal at byte {start} is outside i64"));
    }
    Ok(())
}

fn stable_text_fragment_error(bytes: &[u8], index: usize, expects_operand: bool) -> String {
    let op = match bytes[index] {
        b'+' => Some("add"),
        b'-' => Some(if expects_operand { "neg" } else { "sub" }),
        b'*' => Some("mul"),
        b'/' => Some("div"),
        b'%' => Some("mod"),
        b'~' => Some("bitnot"),
        b'^' => Some("bitxor"),
        b'<' if bytes.get(index + 1) == Some(&b'<') => Some("shl"),
        b'>' if bytes.get(index + 1) == Some(&b'>') => Some("shr"),
        b'&' => Some("bitand"),
        b'|' => Some("bitor"),
        _ => None,
    };
    if let Some(op) = op {
        return trust_wp_pure_expr_v1_arithmetic_refusal(op);
    }
    format!(
        "TrustWpPureExprV1 stable text is outside the arithmetic-free comparison/boolean fragment at byte {index}: expected {}",
        if expects_operand { "an operand" } else { "a boolean/comparison operator" }
    )
}

fn validate_arithmetic_free_trust_formula_v1(value: &Value) -> Result<(), String> {
    let object = value.as_object().ok_or_else(|| {
        format!("typed `{TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION}` predicate must be a JSON object")
    })?;
    reject_unknown_fields(object, "claim", &["schema", "variables", "result", "body"])?;

    match object.get("schema") {
        Some(Value::String(schema)) if schema == TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION => {}
        Some(Value::String(schema)) => {
            return Err(format!(
                "typed TrustFormulaV1 predicate uses schema `{schema}`, expected `{TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION}`"
            ));
        }
        Some(_) => {
            return Err("typed TrustFormulaV1 predicate field `schema` must be a string".into());
        }
        None => {
            return Err(format!(
                "typed TrustFormulaV1 predicate is missing required field `schema`; expected `{TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION}`"
            ));
        }
    }

    let mut env = BTreeMap::new();
    if let Some(variables) = object.get("variables") {
        let variables = variables
            .as_array()
            .ok_or_else(|| "TrustFormulaV1 `variables` must be an array".to_string())?;
        for (index, binding) in variables.iter().enumerate() {
            let (name, sort) = validate_binding(binding, &format!("variables[{index}]"), false)?;
            if env.insert(name.clone(), sort).is_some() {
                return Err(format!("duplicate TrustFormulaV1 binding `{name}`"));
            }
        }
    }

    let result_name = if let Some(result) = object.get("result") {
        let (name, sort) = validate_binding(result, "result", true)?;
        if env.insert(name.clone(), sort).is_some() {
            return Err(format!("duplicate TrustFormulaV1 binding `{name}`"));
        }
        Some(name)
    } else {
        None
    };

    let body = object.get("body").ok_or_else(|| {
        "typed TrustFormulaV1 predicate is missing required field `body`".to_string()
    })?;
    let body_sort = validate_arithmetic_free_expr(body, &env, result_name.as_deref(), "body")?;
    require_formula_sort(&body_sort, &TrustFormulaV1Sort::Bool, "body")?;
    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum TrustFormulaV1Sort {
    Bool,
    Int,
    Seq,
    Ref { mutable: bool, inner: Box<Self> },
    TypeParam(char),
}

fn validate_binding<'a>(
    value: &'a Value,
    path: &str,
    optional_name: bool,
) -> Result<(String, TrustFormulaV1Sort), String> {
    let object = value.as_object().ok_or_else(|| format!("{path} must be an object"))?;
    reject_unknown_fields(object, path, &["name", "sort"])?;
    let name = match object.get("name") {
        Some(Value::String(name)) => name.as_str(),
        Some(_) => return Err(format!("{path}.name must be a string")),
        None if optional_name => "result",
        None => return Err(format!("{path} is missing required field `name`")),
    };
    validate_name(name, &format!("{path}.name"))?;
    let sort = object
        .get("sort")
        .and_then(Value::as_str)
        .ok_or_else(|| format!("{path}.sort must be a string"))?;
    let sort = decode_trust_formula_v1_sort(sort, &format!("{path}.sort"))?;
    Ok((name.to_string(), sort))
}

fn validate_arithmetic_free_expr(
    value: &Value,
    env: &BTreeMap<String, TrustFormulaV1Sort>,
    result_name: Option<&str>,
    path: &str,
) -> Result<TrustFormulaV1Sort, String> {
    let object = value.as_object().ok_or_else(|| format!("{path} must be an object"))?;

    if let Some(value) = object.get("bool") {
        reject_unknown_fields(object, path, &["bool"])?;
        return value
            .as_bool()
            .map(|_| TrustFormulaV1Sort::Bool)
            .ok_or_else(|| format!("{path}.bool must be a boolean"));
    }
    if let Some(value) = object.get("int") {
        reject_unknown_fields(object, path, &["int"])?;
        return value
            .as_i64()
            .map(|_| TrustFormulaV1Sort::Int)
            .ok_or_else(|| format!("{path}.int must be a signed 64-bit integer"));
    }
    if let Some(value) = object.get("var") {
        reject_unknown_fields(object, path, &["var"])?;
        let name = value.as_str().ok_or_else(|| format!("{path}.var must be a string"))?;
        return env
            .get(name)
            .cloned()
            .ok_or_else(|| format!("{path}.var references undeclared binding `{name}`"));
    }
    if let Some(value) = object.get("result") {
        reject_unknown_fields(object, path, &["result"])?;
        if value.as_bool() != Some(true) {
            return Err(format!("{path}.result must be boolean true"));
        }
        let name = result_name
            .ok_or_else(|| format!("{path}.result requires a top-level result binding"))?;
        return env.get(name).cloned().ok_or_else(|| {
            format!("{path}.result references missing top-level result binding `{name}`")
        });
    }
    if let Some(inner) = object.get("old") {
        reject_unknown_fields(object, path, &["old"])?;
        return validate_arithmetic_free_expr(inner, env, result_name, &format!("{path}.old"));
    }

    let op = object
        .get("op")
        .and_then(Value::as_str)
        .ok_or_else(|| format!("{path}.op must be a string"))?;
    if let Some(label) = arithmetic_op_label(op) {
        return Err(trust_formula_v1_arithmetic_refusal(label));
    }

    match op {
        "not" => {
            reject_unknown_fields(object, path, &["op", "expr"])?;
            let expr = object.get("expr").ok_or_else(|| format!("{path}.expr is required"))?;
            let sort =
                validate_arithmetic_free_expr(expr, env, result_name, &format!("{path}.expr"))?;
            require_formula_sort(&sort, &TrustFormulaV1Sort::Bool, &format!("{path}.expr"))?;
            Ok(TrustFormulaV1Sort::Bool)
        }
        "let" => {
            reject_unknown_fields(object, path, &["op", "name", "sort", "value", "body"])?;
            let (name, declared_sort) = required_name_and_sort(object, path)?;
            if env.contains_key(name) {
                return Err(format!("{path}.name shadows existing binding `{name}`"));
            }
            let value = object.get("value").ok_or_else(|| format!("{path}.value is required"))?;
            let value_sort =
                validate_arithmetic_free_expr(value, env, result_name, &format!("{path}.value"))?;
            require_formula_sort(&value_sort, &declared_sort, &format!("{path}.value"))?;
            let body = object.get("body").ok_or_else(|| format!("{path}.body is required"))?;
            let mut scoped = env.clone();
            scoped.insert(name.to_string(), declared_sort);
            validate_arithmetic_free_expr(body, &scoped, result_name, &format!("{path}.body"))
        }
        "forall" | "exists" => {
            reject_unknown_fields(object, path, &["op", "name", "sort", "body"])?;
            let (name, declared_sort) = required_name_and_sort(object, path)?;
            if env.contains_key(name) {
                return Err(format!("{path}.name shadows existing binding `{name}`"));
            }
            let body = object.get("body").ok_or_else(|| format!("{path}.body is required"))?;
            let mut scoped = env.clone();
            scoped.insert(name.to_string(), declared_sort);
            let body_sort =
                validate_arithmetic_free_expr(body, &scoped, result_name, &format!("{path}.body"))?;
            require_formula_sort(&body_sort, &TrustFormulaV1Sort::Bool, &format!("{path}.body"))?;
            Ok(TrustFormulaV1Sort::Bool)
        }
        "eq" | "ne" | "lt" | "le" | "gt" | "ge" | "and" | "or" | "implies" => {
            reject_unknown_fields(object, path, &["op", "lhs", "rhs"])?;
            let lhs = object.get("lhs").ok_or_else(|| format!("{path}.lhs is required"))?;
            let rhs = object.get("rhs").ok_or_else(|| format!("{path}.rhs is required"))?;
            let lhs_sort =
                validate_arithmetic_free_expr(lhs, env, result_name, &format!("{path}.lhs"))?;
            let rhs_sort =
                validate_arithmetic_free_expr(rhs, env, result_name, &format!("{path}.rhs"))?;
            match op {
                // Equality is the sole operation retained for downstream
                // Seq/ref/type-parameter sorts; both sides must still agree.
                "eq" | "ne" => {
                    require_formula_sort(&rhs_sort, &lhs_sort, &format!("{path}.rhs"))?;
                    // The downstream native-sort inference has no general Seq
                    // sort. It accepts Seq equality only through its structural
                    // reflexivity escape hatch (`lhs == rhs`), so mirror that
                    // exact restriction here instead of admitting a claim that
                    // the advertised common ingress later demotes.
                    if lhs_sort == TrustFormulaV1Sort::Seq && lhs != rhs {
                        return Err(format!(
                            "{path} compares distinct Seq expressions; native TrustFormulaV1 replay supports only structurally reflexive Seq equality"
                        ));
                    }
                }
                "lt" | "le" | "gt" | "ge" => {
                    require_formula_sort(
                        &lhs_sort,
                        &TrustFormulaV1Sort::Int,
                        &format!("{path}.lhs"),
                    )?;
                    require_formula_sort(
                        &rhs_sort,
                        &TrustFormulaV1Sort::Int,
                        &format!("{path}.rhs"),
                    )?;
                }
                "and" | "or" | "implies" => {
                    require_formula_sort(
                        &lhs_sort,
                        &TrustFormulaV1Sort::Bool,
                        &format!("{path}.lhs"),
                    )?;
                    require_formula_sort(
                        &rhs_sort,
                        &TrustFormulaV1Sort::Bool,
                        &format!("{path}.rhs"),
                    )?;
                }
                _ => unreachable!("operator match is exhaustive"),
            }
            Ok(TrustFormulaV1Sort::Bool)
        }
        unsupported => Err(format!(
            "{path}.op `{unsupported}` is outside the arithmetic-free TrustFormulaV1 fragment"
        )),
    }
}

fn required_name_and_sort<'a>(
    object: &'a Map<String, Value>,
    path: &str,
) -> Result<(&'a str, TrustFormulaV1Sort), String> {
    let name = object
        .get("name")
        .and_then(Value::as_str)
        .ok_or_else(|| format!("{path}.name must be a string"))?;
    validate_name(name, &format!("{path}.name"))?;
    let sort = object
        .get("sort")
        .and_then(Value::as_str)
        .ok_or_else(|| format!("{path}.sort must be a string"))?;
    let sort = decode_trust_formula_v1_sort(sort, &format!("{path}.sort"))?;
    Ok((name, sort))
}

fn decode_trust_formula_v1_sort(sort: &str, path: &str) -> Result<TrustFormulaV1Sort, String> {
    let sort = sort.trim();
    if let Some(inner) = sort.strip_prefix("&mut ") {
        return Ok(TrustFormulaV1Sort::Ref {
            mutable: true,
            inner: Box::new(decode_trust_formula_v1_sort(inner, path)?),
        });
    }
    if let Some(inner) = sort.strip_prefix('&') {
        return Ok(TrustFormulaV1Sort::Ref {
            mutable: false,
            inner: Box::new(decode_trust_formula_v1_sort(inner, path)?),
        });
    }
    if sort.starts_with('[') && sort.ends_with(']') {
        let inner = sort[1..sort.len() - 1].trim();
        if inner.is_empty() {
            return Err(format!("{path} slice element type is empty"));
        }
        let _ = decode_trust_formula_v1_sort(inner, path)?;
        return Ok(TrustFormulaV1Sort::Seq);
    }
    let type_param = || -> Option<char> {
        let mut chars = sort.chars();
        match (chars.next(), chars.next()) {
            (Some(ch), None) if ch.is_ascii_uppercase() => Some(ch),
            _ => None,
        }
    };
    match sort {
        "int" | "Int" => Ok(TrustFormulaV1Sort::Int),
        "bool" | "Bool" => Ok(TrustFormulaV1Sort::Bool),
        "seq" | "Seq" => Ok(TrustFormulaV1Sort::Seq),
        _ if type_param().is_some() => {
            Ok(TrustFormulaV1Sort::TypeParam(type_param().expect("guard checked type parameter")))
        }
        _ => Err(format!("{path} `{sort}` is outside the TrustFormulaV1 sort fragment")),
    }
}

fn require_formula_sort(
    actual: &TrustFormulaV1Sort,
    expected: &TrustFormulaV1Sort,
    path: &str,
) -> Result<(), String> {
    if actual == expected {
        Ok(())
    } else {
        Err(format!("{path} has sort {actual:?}, expected {expected:?} in TrustFormulaV1"))
    }
}

fn validate_name(name: &str, path: &str) -> Result<(), String> {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return Err(format!("{path} is empty"));
    };
    if !(first == '_' || first.is_ascii_alphabetic()) {
        return Err(format!("{path} must start with `_` or an ASCII letter"));
    }
    if !chars.all(|ch| {
        ch == '_'
            || ch.is_ascii_alphanumeric()
            || matches!(ch, '#' | '.' | '[' | ']' | '*' | '@' | '-' | ';' | '=')
    }) {
        return Err(format!("{path} contains characters outside the supported SMT-symbol set"));
    }
    Ok(())
}

fn reject_unknown_fields(
    object: &Map<String, Value>,
    path: &str,
    allowed: &[&str],
) -> Result<(), String> {
    if let Some(field) = object.keys().find(|field| !allowed.contains(&field.as_str())) {
        return Err(format!("{path} contains unsupported field `{field}`"));
    }
    Ok(())
}

fn arithmetic_op_label(op: &str) -> Option<&'static str> {
    match op {
        "add" | "+" => Some("add"),
        "sub" | "-" => Some("sub"),
        "mul" | "*" => Some("mul"),
        "div" | "/" => Some("div"),
        "mod" | "rem" | "%" => Some("mod"),
        "neg" => Some("neg"),
        _ => None,
    }
}

fn trust_wp_pure_expr_v1_arithmetic_refusal(op: &str) -> String {
    format!(
        "TrustWpPureExprV1 arithmetic operator `{op}` is outside the trust-wp stable-text bare-claim fragment: machine arithmetic modeled over unbounded Int is a false-proof vector (`x + 1 > x` is Int-provable but false at u64::MAX); see 2026-07-17 trust-wp lowering blueprint amendment 1"
    )
}

struct UniqueJsonValue(Value);

impl<'de> Deserialize<'de> for UniqueJsonValue {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_any(UniqueJsonVisitor)
    }
}

struct UniqueJsonVisitor;

impl<'de> Visitor<'de> for UniqueJsonVisitor {
    type Value = UniqueJsonValue;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("a JSON value without duplicate object keys")
    }

    fn visit_bool<E>(self, value: bool) -> Result<Self::Value, E> {
        Ok(UniqueJsonValue(Value::Bool(value)))
    }

    fn visit_i64<E>(self, value: i64) -> Result<Self::Value, E> {
        Ok(UniqueJsonValue(Value::Number(value.into())))
    }

    fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E> {
        Ok(UniqueJsonValue(Value::Number(value.into())))
    }

    fn visit_f64<E>(self, value: f64) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        serde_json::Number::from_f64(value)
            .map(Value::Number)
            .map(UniqueJsonValue)
            .ok_or_else(|| E::custom("non-finite JSON number"))
    }

    fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Ok(UniqueJsonValue(Value::String(value.to_string())))
    }

    fn visit_string<E>(self, value: String) -> Result<Self::Value, E> {
        Ok(UniqueJsonValue(Value::String(value)))
    }

    fn visit_none<E>(self) -> Result<Self::Value, E> {
        Ok(UniqueJsonValue(Value::Null))
    }

    fn visit_unit<E>(self) -> Result<Self::Value, E> {
        Ok(UniqueJsonValue(Value::Null))
    }

    fn visit_some<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        UniqueJsonValue::deserialize(deserializer)
    }

    fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
    where
        A: SeqAccess<'de>,
    {
        let mut values = Vec::new();
        while let Some(UniqueJsonValue(value)) = sequence.next_element()? {
            values.push(value);
        }
        Ok(UniqueJsonValue(Value::Array(values)))
    }

    fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
    where
        A: MapAccess<'de>,
    {
        let mut values = Map::new();
        while let Some(key) = map.next_key::<String>()? {
            if values.contains_key(&key) {
                return Err(de::Error::custom(format!("duplicate JSON object key `{key}`")));
            }
            let UniqueJsonValue(value) = map.next_value()?;
            values.insert(key, value);
        }
        Ok(UniqueJsonValue(Value::Object(values)))
    }
}

/// Lower a trust-types [`Formula`] into the `trust_wp.trust-formula.v1` claim
/// envelope JSON string accepted by trust-wp's native replay decoder.
///
/// The envelope shape is:
///
/// ```json
/// {
///   "schema": "trust_wp.trust-formula.v1",
///   "variables": [{"name": "x", "sort": "int"}],
///   "body": {"op": "ge", "lhs": {"var": "x"}, "rhs": {"int": 0}}
/// }
/// ```
///
/// # Soundness
///
/// This is a *fail-closed* lowering. It returns `Err` for any formula construct
/// outside trust-wp's native comparison/boolean replay fragment: bitvectors,
/// arrays, conditionals, quantifiers, non-`i64` integer literals, non-int/bool
/// variable sorts, and — since Trust #29 (blueprint amendment 1) — ALL integer
/// arithmetic (`Add`/`Sub`/`Mul`/`Div`/`Rem`/`Neg`). Arithmetic is refused
/// because machine-integer predicates modeled as unbounded Int are a confirmed
/// false-proof vector (`result + 1 > result` is Int-provable but false at
/// `u64::MAX`). A partially-lowered predicate is never produced: on error the
/// caller must fall through to the existing fail-closed path and never report a
/// proof from a truncated or arithmetic claim.
///
/// The lowered envelope is *equivalent* to the source formula on the supported
/// fragment — it neither strengthens nor weakens the predicate — so a trust-wp
/// `Verified` replay of the envelope is a genuine proof of the source predicate.
///
/// # Errors
///
/// Returns a human-readable diagnostic when the formula is outside the supported
/// fragment, or contains a variable name/sort that cannot be declared.
pub fn formula_to_trust_formula_v1_envelope(formula: &Formula) -> Result<String, String> {
    // Lower the body first; this rejects every unsupported construct, so the
    // subsequent free-variable walk only ever traverses supported nodes.
    let body = formula_to_body(formula)?;

    let mut variables: BTreeMap<String, &'static str> = BTreeMap::new();
    collect_free_vars(formula, &mut variables)?;

    let variables_json: Vec<serde_json::Value> = variables
        .into_iter()
        .map(|(name, sort)| serde_json::json!({ "name": name, "sort": sort }))
        .collect();

    let envelope = serde_json::json!({
        "schema": TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION,
        "variables": variables_json,
        "body": body,
    });

    // Route even compiler-constructed envelopes through the same strict
    // validator used for prebuilt JSON ingress. This makes a future lowering
    // extension fail closed unless it also remains inside the arithmetic-free
    // grammar.
    canonical_arithmetic_free_trust_formula_v1_payload(&envelope)
}

/// Map a [`Sort`] to the `trust_wp.trust-formula.v1` sort label, fail-closed for
/// sorts outside the native int/bool fragment.
fn sort_label(sort: &Sort) -> Result<&'static str, String> {
    match sort {
        Sort::Bool => Ok("bool"),
        Sort::Int => Ok("int"),
        Sort::BitVec(_) => Err(
            "bitvector-sorted variable is outside trust_wp.trust-formula.v1 native int/bool fragment"
                .to_string(),
        ),
        Sort::Array(_, _) => Err(
            "array-sorted variable is outside trust_wp.trust-formula.v1 native int/bool fragment"
                .to_string(),
        ),
        // `Sort` is #[non_exhaustive] (defined in trust-ir-contract); fail-closed
        // for any sort outside the native int/bool fragment.
        _ => Err(
            "sort is outside trust_wp.trust-formula.v1 native int/bool fragment".to_string(),
        ),
    }
}

/// Recursively collect free `Var`/`SymVar` names (with sort labels) into `out`.
/// Errors if the same name is used with conflicting sorts.
fn collect_free_vars(
    formula: &Formula,
    out: &mut BTreeMap<String, &'static str>,
) -> Result<(), String> {
    match formula {
        Formula::Var(name, sort) => insert_var(out, name.clone(), sort_label(sort)?),
        Formula::SymVar(sym, sort) => insert_var(out, sym.as_str().to_string(), sort_label(sort)?),
        Formula::Bool(_) | Formula::Int(_) | Formula::UInt(_) => Ok(()),
        _ => {
            // `formula_to_body` already rejected unsupported nodes, so this walk
            // only sees supported nodes. Recursing over `children()` keeps the
            // two walks structurally aligned.
            for child in formula.children() {
                collect_free_vars(child, out)?;
            }
            Ok(())
        }
    }
}

fn insert_var(
    out: &mut BTreeMap<String, &'static str>,
    name: String,
    label: &'static str,
) -> Result<(), String> {
    if name.trim().is_empty() {
        return Err("trust_wp.trust-formula.v1 variable name is empty".to_string());
    }
    match out.insert(name.clone(), label) {
        Some(previous) if previous != label => Err(format!(
            "trust_wp.trust-formula.v1 variable `{name}` is used with conflicting sorts `{previous}` and `{label}`"
        )),
        _ => Ok(()),
    }
}

/// Lower a [`Formula`] into the `body` grammar of a `trust_wp.trust-formula.v1`
/// claim. Fail-closed for every construct outside the native int/bool fragment.
fn formula_to_body(formula: &Formula) -> Result<serde_json::Value, String> {
    match formula {
        // --- Literals ---
        Formula::Bool(value) => Ok(serde_json::json!({ "bool": value })),
        Formula::Int(value) => {
            let value = i64::try_from(*value).map_err(|_| {
                format!("integer literal `{value}` is outside i64 for trust_wp.trust-formula.v1")
            })?;
            Ok(serde_json::json!({ "int": value }))
        }
        Formula::UInt(value) => {
            let value = i64::try_from(*value).map_err(|_| {
                format!(
                    "unsigned integer literal `{value}` is outside i64 for trust_wp.trust-formula.v1"
                )
            })?;
            Ok(serde_json::json!({ "int": value }))
        }

        // --- Variables ---
        Formula::Var(name, _) => {
            if name.trim().is_empty() {
                return Err("trust_wp.trust-formula.v1 variable reference is empty".to_string());
            }
            Ok(serde_json::json!({ "var": name }))
        }
        Formula::SymVar(sym, _) => Ok(serde_json::json!({ "var": sym.as_str() })),

        // --- Boolean connectives ---
        Formula::Not(inner) => {
            Ok(serde_json::json!({ "op": "not", "expr": formula_to_body(inner)? }))
        }
        Formula::And(terms) => fold(terms, "and", true),
        Formula::Or(terms) => fold(terms, "or", false),
        Formula::Implies(lhs, rhs) => binary("implies", lhs, rhs),

        // --- Comparisons ---
        Formula::Eq(lhs, rhs) => binary("eq", lhs, rhs),
        Formula::Lt(lhs, rhs) => binary("lt", lhs, rhs),
        Formula::Le(lhs, rhs) => binary("le", lhs, rhs),
        Formula::Gt(lhs, rhs) => binary("gt", lhs, rhs),
        Formula::Ge(lhs, rhs) => binary("ge", lhs, rhs),

        // --- Integer arithmetic: REFUSED (Trust #29, blueprint amendment 1) ---
        // Lowering machine-integer predicate arithmetic into the unbounded-Int
        // `trust_wp.trust-formula.v1` fragment is a confirmed false-proof
        // vector: the trust-wp sibling's linear-int rule proves free-variable
        // Int tautologies such as `result + 1 > result`, which is FALSE at
        // `u64::MAX` under Rust's wrapping machine semantics. The envelope
        // carries no domain tag distinguishing math-Int from machine-int, so
        // the replay decoder treats it as unbounded Int. Refuse ALL arithmetic
        // exactly as the bare-claim lane
        // (`rustc_mir_transform::trust_verify::trust_spec_expr_to_trust_formula_body`)
        // and the body-bound fragment
        // (`trust_ir_bridge::trust_wp_claim::spec_predicate_to_sibling_json`)
        // already do. Fail-closed: every caller treats `Err` as Unsupported and
        // never reports a proof from an arithmetic predicate. See
        // docs/design-notes/2026-07-17-trust-wp-lowering-blueprint.md.
        Formula::Add(..) => Err(trust_formula_v1_arithmetic_refusal("add")),
        Formula::Sub(..) => Err(trust_formula_v1_arithmetic_refusal("sub")),
        Formula::Mul(..) => Err(trust_formula_v1_arithmetic_refusal("mul")),
        Formula::Div(..) => Err(trust_formula_v1_arithmetic_refusal("div")),
        Formula::Rem(..) => Err(trust_formula_v1_arithmetic_refusal("mod")),
        Formula::Neg(..) => Err(trust_formula_v1_arithmetic_refusal("neg")),

        // Everything else (bitvectors, arrays, conditionals, quantifiers) is
        // outside the native int/bool replay fragment: fail closed.
        other => Err(format!(
            "formula node `{}` is outside the trust_wp.trust-formula.v1 native int/bool replay fragment",
            node_label(other)
        )),
    }
}

/// Trust (#29): amendment-1 arithmetic refusal for the `trust-types.Formula@1`
/// -> `trust_wp.trust-formula.v1` lowering lane. Kept as a single helper so
/// every arithmetic operator refuses with a message that cites the same
/// false-proof vector (machine arithmetic laundered as an unbounded-Int claim)
/// as the bare-claim and body-bound lanes.
fn trust_formula_v1_arithmetic_refusal(op: &str) -> String {
    format!(
        "Formula arithmetic operator `{op}` is outside the trust_wp.trust-formula.v1 arithmetic-free fragment: machine arithmetic modeled over unbounded Int is a false-proof vector (`result + 1 > result` is Int-provable but false at u64::MAX); see 2026-07-17 trust-wp lowering blueprint amendment 1"
    )
}

fn binary(op: &str, lhs: &Formula, rhs: &Formula) -> Result<serde_json::Value, String> {
    Ok(serde_json::json!({
        "op": op,
        "lhs": formula_to_body(lhs)?,
        "rhs": formula_to_body(rhs)?,
    }))
}

/// Fold an n-ary `And`/`Or` into the binary `body` grammar. An empty conjunction
/// is `true`; an empty disjunction is `false`.
fn fold(terms: &[Formula], op: &str, empty_is_true: bool) -> Result<serde_json::Value, String> {
    let Some((first, rest)) = terms.split_first() else {
        return Ok(serde_json::json!({ "bool": empty_is_true }));
    };
    let mut acc = formula_to_body(first)?;
    for term in rest {
        let rhs = formula_to_body(term)?;
        acc = serde_json::json!({ "op": op, "lhs": acc, "rhs": rhs });
    }
    Ok(acc)
}

fn node_label(formula: &Formula) -> &'static str {
    match formula {
        Formula::Ite(..) => "ite",
        Formula::Forall(..) => "forall",
        Formula::Exists(..) => "exists",
        Formula::Select(..) => "array-select",
        Formula::Store(..) => "array-store",
        Formula::BitVec { .. } => "bitvec-literal",
        _ if formula.has_bitvectors() => "bitvector-op",
        _ => "unsupported",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn body_of(formula: &Formula) -> serde_json::Value {
        let envelope = formula_to_trust_formula_v1_envelope(formula).expect("lowers");
        let value: serde_json::Value = serde_json::from_str(&envelope).expect("valid json");
        assert_eq!(value["schema"], TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION);
        value
    }

    #[test]
    fn trivially_true_closed_predicate_lowers() {
        // 5 >= 0
        let f = Formula::Ge(Box::new(Formula::Int(5)), Box::new(Formula::Int(0)));
        let value = body_of(&f);
        assert_eq!(value["variables"].as_array().unwrap().len(), 0);
        assert_eq!(value["body"]["op"], "ge");
        assert_eq!(value["body"]["lhs"]["int"], 5);
        assert_eq!(value["body"]["rhs"]["int"], 0);
    }

    #[test]
    fn predicate_with_int_variable_declares_it() {
        // x > 0  (arithmetic-free: the int variable is still declared)
        let f =
            Formula::Gt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0)));
        let value = body_of(&f);
        let vars = value["variables"].as_array().unwrap();
        assert_eq!(vars.len(), 1);
        assert_eq!(vars[0]["name"], "x");
        assert_eq!(vars[0]["sort"], "int");
        assert_eq!(value["body"]["op"], "gt");
    }

    #[test]
    fn arithmetic_int_tautology_is_refused() {
        // Trust (#29): `x + 1 > x` is Int-provable but FALSE at u64::MAX under
        // machine wrapping semantics. The Formula@1 lowering lane must refuse
        // it so it can never reach the trust-wp sibling as a bare unbounded-Int
        // claim (blueprint amendment 1).
        let x = || Formula::Var("x".into(), Sort::Int);
        let add_taut = Formula::Gt(
            Box::new(Formula::Add(Box::new(x()), Box::new(Formula::Int(1)))),
            Box::new(x()),
        );
        let err = formula_to_trust_formula_v1_envelope(&add_taut).unwrap_err();
        assert!(err.contains("u64::MAX"), "must cite the counterexample: {err}");
        assert!(err.contains("amendment 1"), "must cite the blueprint: {err}");

        // The dual `x - 1 < x` (false at 0) must also be refused.
        let sub_taut = Formula::Lt(
            Box::new(Formula::Sub(Box::new(x()), Box::new(Formula::Int(1)))),
            Box::new(x()),
        );
        assert!(formula_to_trust_formula_v1_envelope(&sub_taut).is_err());
    }

    #[test]
    fn every_arithmetic_operator_is_refused() {
        let x = || Box::new(Formula::Var("x".into(), Sort::Int));
        let one = || Box::new(Formula::Int(1));
        // Each arithmetic node is wrapped in an otherwise-lowerable comparison,
        // so the arithmetic (not a sort/shape issue) is the sole reason for
        // refusal. Add/Sub/Mul/Div/Rem/Neg all fail closed.
        for arith in [
            Formula::Add(x(), one()),
            Formula::Sub(x(), one()),
            Formula::Mul(x(), one()),
            Formula::Div(x(), one()),
            Formula::Rem(x(), one()),
            Formula::Neg(x()),
        ] {
            let f = Formula::Ge(Box::new(arith), Box::new(Formula::Int(0)));
            assert!(
                formula_to_trust_formula_v1_envelope(&f).is_err(),
                "arithmetic operator must be refused"
            );
        }
    }

    #[test]
    fn prebuilt_envelopes_refuse_arithmetic_labels_and_aliases() {
        for op in ["add", "+", "sub", "-", "mul", "*", "div", "/", "mod", "rem", "%"] {
            let value = serde_json::json!({
                "schema": TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION,
                "variables": [{"name": "x", "sort": "int"}],
                "body": {
                    "op": "gt",
                    "lhs": {
                        "op": op,
                        "lhs": {"var": "x"},
                        "rhs": {"int": 1},
                    },
                    "rhs": {"var": "x"},
                },
            });
            let err = canonical_arithmetic_free_trust_formula_v1_payload(&value)
                .expect_err("prebuilt arithmetic envelope must fail closed");
            assert!(err.contains("arithmetic operator"), "{op}: {err}");
            assert!(err.contains("u64::MAX"), "{op}: {err}");
        }

        for op in ["neg"] {
            let value = serde_json::json!({
                "schema": TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION,
                "variables": [{"name": "x", "sort": "int"}],
                "body": {"op": op, "expr": {"var": "x"}},
            });
            assert!(canonical_arithmetic_free_trust_formula_v1_payload(&value).is_err());
        }
    }

    #[test]
    fn prebuilt_envelope_accepts_the_body_bound_let_fragment() {
        let value = serde_json::json!({
            "schema": TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION,
            "variables": [{"name": "x", "sort": "int"}],
            "body": {
                "op": "let",
                "name": "result",
                "sort": "int",
                "value": {"var": "x"},
                "body": {
                    "op": "ge",
                    "lhs": {"var": "result"},
                    "rhs": {"var": "x"},
                },
            },
        });
        let payload = canonical_arithmetic_free_trust_formula_v1_payload(&value)
            .expect("body-bound arithmetic-free envelope remains accepted");
        let round_trip: Value = serde_json::from_str(&payload).expect("canonical JSON");
        assert_eq!(round_trip, value);
    }

    #[test]
    fn prebuilt_envelopes_require_well_sorted_boolean_predicates() {
        let malformed_bodies = [
            serde_json::json!({"int": 1}),
            serde_json::json!({"op": "not", "expr": {"int": 1}}),
            serde_json::json!({
                "op": "lt",
                "lhs": {"bool": false},
                "rhs": {"bool": true},
            }),
            serde_json::json!({
                "op": "and",
                "lhs": {"int": 1},
                "rhs": {"bool": true},
            }),
            serde_json::json!({
                "op": "eq",
                "lhs": {"int": 1},
                "rhs": {"bool": true},
            }),
            serde_json::json!({
                "op": "let",
                "name": "x",
                "sort": "bool",
                "value": {"int": 1},
                "body": {"var": "x"},
            }),
            serde_json::json!({
                "op": "forall",
                "name": "x",
                "sort": "int",
                "body": {"var": "x"},
            }),
        ];
        for body in malformed_bodies {
            let value = serde_json::json!({
                "schema": TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION,
                "body": body,
            });
            let error = canonical_arithmetic_free_trust_formula_v1_payload(&value)
                .expect_err("wrong-sort or non-boolean TrustFormula body must fail closed");
            assert!(error.contains("sort"), "unexpected diagnostic: {error}");
        }
    }

    #[test]
    fn prebuilt_envelope_preserves_supported_opaque_equality_sorts() {
        let value = serde_json::json!({
            "schema": TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION,
            "variables": [
                {"name": "s", "sort": "seq"},
                {"name": "r1", "sort": "&int"},
                {"name": "r2", "sort": "&Int"},
                {"name": "t1", "sort": "T"},
                {"name": "t2", "sort": "T"},
            ],
            "body": {
                "op": "and",
                "lhs": {
                    "op": "and",
                    "lhs": {"op": "eq", "lhs": {"var": "s"}, "rhs": {"var": "s"}},
                    "rhs": {"op": "eq", "lhs": {"var": "r1"}, "rhs": {"var": "r2"}},
                },
                "rhs": {"op": "eq", "lhs": {"var": "t1"}, "rhs": {"var": "t2"}},
            },
        });
        canonical_arithmetic_free_trust_formula_v1_payload(&value)
            .expect("downstream-supported Seq/ref/type-parameter equality remains accepted");

        let distinct_seq = serde_json::json!({
            "schema": TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION,
            "variables": [
                {"name": "lhs", "sort": "seq"},
                {"name": "rhs", "sort": "[int]"},
            ],
            "body": {"op": "eq", "lhs": {"var": "lhs"}, "rhs": {"var": "rhs"}},
        });
        let error = canonical_arithmetic_free_trust_formula_v1_payload(&distinct_seq)
            .expect_err("distinct Seq equality is demoted by native replay and must fail here");
        assert!(error.contains("distinct Seq expressions"), "{error}");
    }

    #[test]
    fn malformed_and_duplicate_prebuilt_envelopes_fail_closed() {
        let missing_body = serde_json::json!({
            "schema": TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION,
        });
        assert!(
            canonical_arithmetic_free_trust_formula_v1_payload(&missing_body)
                .expect_err("body is mandatory")
                .contains("missing required field `body`")
        );

        let duplicate_binding = serde_json::json!({
            "schema": TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION,
            "variables": [
                {"name": "x", "sort": "int"},
                {"name": "x", "sort": "int"},
            ],
            "body": {"op": "eq", "lhs": {"var": "x"}, "rhs": {"var": "x"}},
        });
        assert!(
            canonical_arithmetic_free_trust_formula_v1_payload(&duplicate_binding)
                .expect_err("duplicate binding is ambiguous")
                .contains("duplicate TrustFormulaV1 binding `x`")
        );

        let duplicate_body = format!(
            r#"{{"schema":"{TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION}","body":{{"bool":true}},"body":{{"bool":false}}}}"#
        );
        assert!(
            parse_arithmetic_free_trust_formula_v1_payload(&duplicate_body)
                .expect_err("duplicate raw JSON fields must be rejected")
                .contains("duplicate JSON object key `body`")
        );

        let duplicate_op = format!(
            r#"{{"schema":"{TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION}","variables":[{{"name":"x","sort":"int"}}],"body":{{"op":"gt","op":"add","lhs":{{"var":"x"}},"rhs":{{"int":1}}}}}}"#
        );
        assert!(
            parse_arithmetic_free_trust_formula_v1_payload(&duplicate_op)
                .expect_err("duplicate nested operator must be rejected")
                .contains("duplicate JSON object key `op`")
        );
    }

    #[test]
    fn unique_proof_json_parser_preserves_depth_tolerance() {
        const DEPTH: usize = 256;
        let mut payload = String::with_capacity(DEPTH * 2 + 1);
        payload.extend(std::iter::repeat_n('[', DEPTH));
        payload.push('0');
        payload.extend(std::iter::repeat_n(']', DEPTH));

        let mut value = parse_unique_proof_json_payload(&payload)
            .expect("unique proof JSON beyond serde's default recursion limit must parse");
        for _ in 0..DEPTH {
            let Value::Array(mut items) = value else {
                panic!("deep proof JSON must retain every array level");
            };
            assert_eq!(items.len(), 1);
            value = items.pop().expect("one nested value");
        }
        assert_eq!(value, Value::Number(0.into()));
    }

    #[test]
    fn pure_expr_text_guard_refuses_arithmetic_but_keeps_negative_literals() {
        for text in [
            "(x + 1) > x",
            "(x - 1) < x",
            "(x * 2) > x",
            "(x / 2) <= x",
            "(x % 2) == 0",
            "(x << 1) > x",
            "(x >> 1) <= x",
            "(x & 1) == 0",
            "(x | 1) >= x",
            "(x ^ 1) != x",
            "(~x) < 0",
            "-x < 0",
            "+1 == 1",
            "x as u8 == x",
            "(x: u8) == x",
            "f(x) == f(x)",
            "x.field == x.field",
            "old(x) == old(x)",
            "x[0] == x[0]",
        ] {
            assert!(
                reject_trust_wp_pure_expr_v1_text_arithmetic(text).is_err(),
                "non-opaque or arithmetic stable text must refuse: {text}"
            );
        }
        for text in [
            "x >= -5",
            "(-5 <= x)",
            "x == 0",
            "x >= -9223372036854775808",
            "x <= 9223372036854775807",
            "(x < y) && ((y >= -5) || ready)",
            "!ready ==> x != -1",
        ] {
            assert_eq!(
                reject_trust_wp_pure_expr_v1_text_arithmetic(text),
                Ok(()),
                "signed literals are constants, not arithmetic: {text}"
            );
        }
        for text in ["x >= -9223372036854775809", "x <= 9223372036854775808"] {
            let error = reject_trust_wp_pure_expr_v1_text_arithmetic(text)
                .expect_err("stable-text integers outside i64 must fail before native decode");
            assert!(error.contains("outside i64"), "{text}: {error}");
        }
    }

    #[test]
    fn pure_expr_opaque_identifiers_match_the_downstream_base_token() {
        for accepted in ["x", "_", "_x0", "result", "x_s0_1"] {
            assert!(trust_wp_pure_expr_v1_opaque_identifier(accepted), "{accepted}");
        }
        for rejected in [
            "", "0x", "x.field", "x#s1", "true", "false", "as", "box", "const", "dyn", "else",
            "exists", "forall", "if", "let", "match", "mut", "old", "ref", "use",
        ] {
            assert!(!trust_wp_pure_expr_v1_opaque_identifier(rejected), "{rejected}");
        }
    }

    #[test]
    fn result_variable_is_declared_with_its_sort() {
        // result >= 0  (encoded as a Var named "result")
        let f = Formula::Ge(
            Box::new(Formula::Var("result".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        let value = body_of(&f);
        let vars = value["variables"].as_array().unwrap();
        assert_eq!(vars.len(), 1);
        assert_eq!(vars[0]["name"], "result");
        assert_eq!(vars[0]["sort"], "int");
    }

    #[test]
    fn bool_connectives_fold_left() {
        // a && b && c  -> ((a && b) && c)
        let f = Formula::And(vec![
            Formula::Var("a".into(), Sort::Bool),
            Formula::Var("b".into(), Sort::Bool),
            Formula::Var("c".into(), Sort::Bool),
        ]);
        let value = body_of(&f);
        assert_eq!(value["body"]["op"], "and");
        assert_eq!(value["body"]["lhs"]["op"], "and");
        assert_eq!(value["body"]["rhs"]["var"], "c");
    }

    #[test]
    fn empty_and_is_true_empty_or_is_false() {
        let and = body_of(&Formula::And(vec![]));
        assert_eq!(and["body"]["bool"], true);
        let or = body_of(&Formula::Or(vec![]));
        assert_eq!(or["body"]["bool"], false);
    }

    #[test]
    fn bitvector_formula_is_rejected() {
        let f = Formula::BvAdd(
            Box::new(Formula::Var("x".into(), Sort::BitVec(32))),
            Box::new(Formula::Var("y".into(), Sort::BitVec(32))),
            32,
        );
        assert!(formula_to_trust_formula_v1_envelope(&f).is_err());
    }

    #[test]
    fn bitvector_sorted_variable_is_rejected() {
        // Comparison whose body lowers, but a BV-sorted free var must reject.
        let f = Formula::Eq(
            Box::new(Formula::Var("x".into(), Sort::BitVec(8))),
            Box::new(Formula::Var("y".into(), Sort::BitVec(8))),
        );
        assert!(formula_to_trust_formula_v1_envelope(&f).is_err());
    }

    #[test]
    fn ite_is_rejected() {
        let f = Formula::Ite(
            Box::new(Formula::Bool(true)),
            Box::new(Formula::Int(1)),
            Box::new(Formula::Int(0)),
        );
        assert!(formula_to_trust_formula_v1_envelope(&f).is_err());
    }

    #[test]
    fn quantifier_is_rejected() {
        let f = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Ge(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )),
        );
        assert!(formula_to_trust_formula_v1_envelope(&f).is_err());
    }

    #[test]
    fn conflicting_variable_sorts_are_rejected() {
        // x:int and x:bool in the same predicate.
        let f = Formula::And(vec![
            Formula::Ge(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0))),
            Formula::Var("x".into(), Sort::Bool),
        ]);
        assert!(formula_to_trust_formula_v1_envelope(&f).is_err());
    }

    #[test]
    fn integer_literal_outside_i64_is_rejected() {
        let f = Formula::Ge(
            Box::new(Formula::Int(i128::from(i64::MAX) + 1)),
            Box::new(Formula::Int(0)),
        );
        assert!(formula_to_trust_formula_v1_envelope(&f).is_err());
    }
}
