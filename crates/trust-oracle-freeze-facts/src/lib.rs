// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

//! Fresh committed-source citation facts, never persisted gate verdicts.
//!
//! One invocation owns its Git readers and reuses only blob/parser facts in
//! that repository context. The shell gate retains subject selection, findings,
//! completeness, waiver checks and actual destination replay. Unsupported
//! namespace/parser profiles request the original real reader instead.

mod git;
mod parser;

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::io::{self, Read};
use std::path::Path;

pub const PROTOCOL: &str = "trust-oracle-freeze-facts-v1";
const MAX_REQUEST_BYTES: u64 = 32 * 1024 * 1024;
const MAX_REQUESTS: usize = 100_000;

#[derive(Debug)]
pub enum Error {
    Unsupported(String),
    Unavailable(String),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unsupported(message) | Self::Unavailable(message) => f.write_str(message),
        }
    }
}

impl std::error::Error for Error {}

impl From<io::Error> for Error {
    fn from(error: io::Error) -> Self {
        Self::Unavailable(error.to_string())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Request {
    pub path: String,
    pub function: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fact {
    Test,
    NotFile,
    MissingTest,
    GitError,
}

impl Fact {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Test => "test",
            Self::NotFile => "not-file",
            Self::MissingTest => "missing-test",
            Self::GitError => "git-error",
        }
    }
}

/// NUL-delimited path/function pairs; order and duplicates are significant.
pub fn read_requests(input: impl Read) -> Result<Vec<Request>, Error> {
    let mut bytes = Vec::new();
    input.take(MAX_REQUEST_BYTES + 1).read_to_end(&mut bytes)?;
    if bytes.len() as u64 > MAX_REQUEST_BYTES {
        return Err(Error::Unsupported("citation request budget exceeded".into()));
    }
    if bytes.is_empty() {
        return Ok(Vec::new());
    }
    if bytes.last() != Some(&0) {
        return Err(Error::Unavailable("unterminated citation request".into()));
    }
    let mut fields = bytes[..bytes.len() - 1].split(|byte| *byte == 0);
    let mut requests = Vec::new();
    while let Some(path) = fields.next() {
        let function =
            fields.next().ok_or_else(|| Error::Unavailable("partial citation pair".into()))?;
        if requests.len() == MAX_REQUESTS {
            return Err(Error::Unsupported("excessive citation requests".into()));
        }
        let valid_path = !path.is_empty()
            && path.iter().all(|byte| byte.is_ascii_alphanumeric() || b"_./-".contains(byte));
        let valid_function = !function.is_empty()
            && function.iter().all(|byte| byte.is_ascii_alphanumeric() || *byte == b'_');
        if !valid_path || !valid_function {
            return Err(Error::Unavailable("invalid citation request grammar".into()));
        }
        requests.push(Request {
            path: String::from_utf8(path.to_vec()).expect("checked ASCII path"),
            function: String::from_utf8(function.to_vec()).expect("checked ASCII function"),
        });
    }
    Ok(requests)
}

struct Budget {
    blob_bytes: usize,
    names: usize,
    name_bytes: usize,
}

impl Budget {
    fn charge(remaining: &mut usize, amount: usize) -> Result<(), Error> {
        *remaining = remaining
            .checked_sub(amount)
            .ok_or_else(|| Error::Unsupported("aggregate citation fact budget exceeded".into()))?;
        Ok(())
    }
}

#[derive(Debug)]
pub struct Observation {
    pub facts: Vec<Fact>,
    /// Actual distinct successfully parsed bodies, useful for conformance tests.
    /// It says nothing about verdicts or timing.
    pub parsed_blobs: usize,
}

pub fn committed_facts(
    repo: &Path,
    commit: &str,
    requests: &[Request],
) -> Result<Observation, Error> {
    committed_facts_with_budget(
        repo,
        commit,
        requests,
        Budget { blob_bytes: 64 * 1024 * 1024, names: 250_000, name_bytes: 16 * 1024 * 1024 },
    )
}

fn committed_facts_with_budget(
    repo: &Path,
    commit: &str,
    requests: &[Request],
    mut budget: Budget,
) -> Result<Observation, Error> {
    git::require_supported(repo, commit)?;
    let paths = requests.iter().map(|request| request.path.clone()).collect::<BTreeSet<_>>();
    let entries = git::entries(repo, commit, &paths)?;
    let mut parsed = BTreeMap::new();
    let mut blobs = git::Blobs::open(repo)?;
    let mut facts = Vec::with_capacity(requests.len());
    for request in requests {
        let fact = match entries.get(&request.path) {
            Some(git::Entry::Blob(object)) => {
                if !parsed.contains_key(object) {
                    let body = blobs.read(object)?;
                    if let Some(body) = &body {
                        Budget::charge(&mut budget.blob_bytes, body.len())?;
                    }
                    let tests = body
                        .map(|body| parser::test_functions(&body))
                        .transpose()
                        .map_err(|reason| {
                            Error::Unsupported(format!(
                                "legacy source predicate required: {reason:?}"
                            ))
                        })?;
                    if let Some(tests) = &tests {
                        Budget::charge(&mut budget.names, tests.len())?;
                        for name in tests {
                            Budget::charge(&mut budget.name_bytes, name.len())?;
                        }
                    }
                    parsed.insert(object.clone(), tests);
                }
                match &parsed[object] {
                    Some(tests) if tests.contains(&request.function) => Fact::Test,
                    Some(_) => Fact::MissingTest,
                    None => Fact::GitError,
                }
            }
            Some(git::Entry::GitError) => Fact::GitError,
            Some(git::Entry::NotFile) | None => Fact::NotFile,
        };
        facts.push(fact);
    }
    blobs.finish()?;
    // Replacement/namespace state must not silently change during the read.
    git::require_supported(repo, commit)?;
    Ok(Observation { facts, parsed_blobs: parsed.values().filter(|value| value.is_some()).count() })
}

#[cfg(test)]
mod tests;
