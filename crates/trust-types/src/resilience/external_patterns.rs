// trust-types/resilience/external_patterns: Known external call patterns
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::VerifiableFunction;
use crate::utils::strip_generics;

use super::types::{ExternalDependency, FailureMode, FailureModel};

/// Known external call patterns for matching against MIR Call func names.
///
/// Maps substrings of def_path to (service_name, default_failure_modes).
pub const EXTERNAL_CALL_PATTERNS: &[(&str, &str, &[FailureMode])] = &[
    // Network / HTTP
    (
        "reqwest::Client::get",
        "http",
        &[FailureMode::Timeout, FailureMode::Error, FailureMode::Unavailable],
    ),
    (
        "reqwest::Client::post",
        "http",
        &[FailureMode::Timeout, FailureMode::Error, FailureMode::Unavailable],
    ),
    (
        "reqwest::Client::put",
        "http",
        &[FailureMode::Timeout, FailureMode::Error, FailureMode::Unavailable],
    ),
    (
        "reqwest::Client::delete",
        "http",
        &[FailureMode::Timeout, FailureMode::Error, FailureMode::Unavailable],
    ),
    (
        "hyper::Client::request",
        "http",
        &[FailureMode::Timeout, FailureMode::Error, FailureMode::Unavailable],
    ),
    // Database
    (
        "sqlx::query",
        "database",
        &[FailureMode::Timeout, FailureMode::Error, FailureMode::Unavailable],
    ),
    (
        "diesel::RunQueryDsl::execute",
        "database",
        &[FailureMode::Timeout, FailureMode::Error, FailureMode::Unavailable],
    ),
    ("rusqlite::Connection::execute", "database", &[FailureMode::Error, FailureMode::Unavailable]),
    // Redis
    (
        "redis::Commands::get",
        "redis",
        &[FailureMode::Timeout, FailureMode::Error, FailureMode::Unavailable],
    ),
    (
        "redis::Commands::set",
        "redis",
        &[FailureMode::Timeout, FailureMode::Error, FailureMode::Unavailable],
    ),
    (
        "redis::Connection::req_command",
        "redis",
        &[FailureMode::Timeout, FailureMode::Error, FailureMode::Unavailable],
    ),
    // File I/O
    ("std::fs::read", "filesystem", &[FailureMode::Error]),
    ("std::fs::write", "filesystem", &[FailureMode::Error]),
    ("std::fs::File::open", "filesystem", &[FailureMode::Error]),
    ("std::fs::File::create", "filesystem", &[FailureMode::Error]),
    ("std::io::Read::read", "filesystem", &[FailureMode::Error, FailureMode::Partial]),
    ("std::io::Write::write", "filesystem", &[FailureMode::Error, FailureMode::Partial]),
    // S3 / AWS
    (
        "aws_sdk_s3::Client::get_object",
        "s3",
        &[FailureMode::Timeout, FailureMode::Error, FailureMode::Unavailable],
    ),
    (
        "aws_sdk_s3::Client::put_object",
        "s3",
        &[FailureMode::Timeout, FailureMode::Error, FailureMode::Unavailable],
    ),
    // DNS / Network primitives
    ("std::net::TcpStream::connect", "network", &[FailureMode::Timeout, FailureMode::Unavailable]),
    (
        "tokio::net::TcpStream::connect",
        "network",
        &[FailureMode::Timeout, FailureMode::Unavailable],
    ),
];

/// Match a MIR Call func path against known external call patterns.
///
/// Returns (service_name, default_failure_modes) if matched.
pub fn match_external_call(func_path: &str) -> Option<(&'static str, Vec<FailureMode>)> {
    let normalized = strip_generics(func_path);
    let mut best_match: Option<(usize, &str, &[FailureMode])> = None;

    for &(pattern, service, modes) in EXTERNAL_CALL_PATTERNS {
        if normalized.contains(pattern) {
            let len = pattern.len();
            if best_match.as_ref().is_none_or(|(best_len, _, _)| len > *best_len) {
                best_match = Some((len, service, modes));
            }
        }
    }

    best_match.map(|(_, service, modes)| (service, modes.to_vec()))
}

/// Extract a failure model from a VerifiableFunction.
///
/// Walks all basic blocks, inspects Call terminators, and matches their
/// func path against known external call patterns. Builds a FailureModel
/// with detected external dependencies and their failure modes.
pub fn extract_failure_model(func: &VerifiableFunction) -> FailureModel {
    let mut model = FailureModel::new(&func.def_path);

    for block in &func.body.blocks {
        if let crate::Terminator::Call { func: func_name, span, .. } = &block.terminator
            && let Some((service, failure_modes)) = match_external_call(func_name)
        {
            model.dependencies.push(ExternalDependency {
                name: service.to_string(),
                failure_modes,
                block: block.id,
                span: span.clone(),
                call_path: func_name.clone(),
            });
        }
    }

    model
}
