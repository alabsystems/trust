// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Mode 2: typed declaration dependency closure, never a printed-name walk.
//!
//! Uses the pinned kernel's structural serde vocabulary, including Name
//! constructor tags, all Expr/Level variants, binder multiplicity and metadata.
//! The codec and mode are part of the contract; cached hashes, Arc addresses,
//! discovery order and Display do not enter the digest. This is a binding, not
//! fresh kernel admission or a portable attestation of native callback code.

use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::io::{self, Write};

use bincode::Options;
use clean_kernel::{Environment, Expr, ExprFolderOpt, ExprKind, Name};

use super::{
    ENVIRONMENT_DIGEST_MODE_DEPENDENCY_CLOSURE, EnvironmentDigest, EnvironmentDigestRefusal,
};

const MAX_MEMBERS: usize = 100_000;
const MAX_EXPR_NODES: usize = 1_000_000;
const MAX_RECORD_BYTES: usize = 16 * 1024 * 1024;
const MAX_CLOSURE_BYTES: usize = 64 * 1024 * 1024;

struct LimitedBytes {
    bytes: Vec<u8>,
    limit: usize,
}

impl Write for LimitedBytes {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        if bytes.len() > self.limit.saturating_sub(self.bytes.len()) {
            return Err(io::Error::other("environment digest byte limit exceeded"));
        }
        self.bytes.extend_from_slice(bytes);
        Ok(bytes.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

/// The kernel owns child traversal. The observation hook also sees projection
/// owners, which visit_const alone misses. Pointer keys only avoid revisiting
/// shared immutable nodes; they are never hashed or used as semantic identity.
#[derive(Default)]
struct References {
    names: RefCell<BTreeSet<Name>>,
    seen: RefCell<HashSet<*const ExprKind>>,
    exhausted: Cell<bool>,
}

impl ExprFolderOpt for References {
    fn should_descend(&self, expr: &Expr) -> bool {
        let mut seen = self.seen.borrow_mut();
        let ptr = expr.kind() as *const ExprKind;
        if seen.contains(&ptr) {
            return false;
        }
        if seen.len() == MAX_EXPR_NODES {
            self.exhausted.set(true);
            return false;
        }
        seen.insert(ptr);
        if let ExprKind::Const(name, _) | ExprKind::Proj(name, _, _) = expr.kind() {
            let mut names = self.names.borrow_mut();
            if !names.contains(name) {
                names.insert(name.clone());
            }
        }
        true
    }
}

impl References {
    fn reset(&mut self) {
        self.names.get_mut().clear();
        self.seen.get_mut().clear();
        self.exhausted.set(false);
    }

    fn expression(&mut self, expr: &Expr) {
        // Every default folder arm returns unchanged; no term is rewritten.
        let unchanged = self.fold_expr_opt(expr);
        debug_assert!(unchanged.is_none());
    }

    fn name(&mut self, name: &Name) {
        let names = self.names.get_mut();
        if !names.contains(name) {
            names.insert(name.clone());
        }
    }
}

fn limit(subject: &Name, resource: &'static str, bound: usize) -> EnvironmentDigestRefusal {
    EnvironmentDigestRefusal::ResourceLimit { name: subject.to_string(), resource, limit: bound }
}

pub(super) fn compute(
    env: &Environment,
    subject: &Name,
) -> Result<EnvironmentDigest, EnvironmentDigestRefusal> {
    if env.get_const(subject).is_none() {
        return Err(EnvironmentDigestRefusal::NoSuchDeclaration { name: subject.to_string() });
    }
    let mut members: BTreeMap<Name, Vec<u8>> = BTreeMap::new();
    let mut pending = BTreeSet::from([subject.clone()]);
    let mut refs = References::default();
    let mut total_bytes = 0usize;
    while let Some(current) = pending.pop_first() {
        if members.contains_key(&current) {
            continue;
        }
        if members.len() == MAX_MEMBERS {
            return Err(limit(subject, "declaration count", MAX_MEMBERS));
        }
        let constant = env.get_const(&current);
        let inductive = env.get_inductive(&current);
        let constructor = env.get_constructor(&current);
        let recursor = env.get_recursor(&current);
        let quotient = env.get_quot(&current);
        let fields = env.get_structure_field_names(&current);
        let defaults: Vec<_> = fields
            .unwrap_or_default()
            .iter()
            .map(|field| (field, env.get_structure_field_default(&current, field)))
            .collect();
        let parents = env.get_structure_parents(&current);
        let implementation = env.get_implemented_by(&current);

        // Explicit Option tags bind absence as well as presence. Whole kernel
        // records bind fields that are absent from ConstantInfo (recursor rules,
        // constructor indices, inductive flags and quotient primitive kind).
        let mut record = LimitedBytes { bytes: Vec::new(), limit: MAX_RECORD_BYTES };
        bincode::DefaultOptions::new()
            .with_fixint_encoding()
            .with_little_endian()
            .serialize_into(
                &mut record,
                &(
                    &current,
                    constant,
                    inductive,
                    constructor,
                    recursor,
                    quotient,
                    env.get_constant_origin(&current),
                    env.declaration_verification(&current),
                    fields,
                    &defaults,
                    parents,
                    implementation,
                ),
            )
            .map_err(|error| EnvironmentDigestRefusal::Encoding {
                name: current.to_string(),
                reason: error.to_string(),
            })?;
        total_bytes = total_bytes
            .checked_add(record.bytes.len())
            .filter(|bytes| *bytes <= MAX_CLOSURE_BYTES)
            .ok_or_else(|| limit(subject, "closure bytes", MAX_CLOSURE_BYTES))?;

        refs.reset();
        if let Some(info) = constant {
            refs.expression(&info.type_);
            if let Some(value) = &info.value {
                refs.expression(value);
            }
        }
        if let Some(info) = inductive {
            refs.expression(&info.type_);
            for name in info.all_names.iter().chain(&info.constructor_names) {
                refs.name(name);
            }
        }
        if let Some(info) = constructor {
            refs.expression(&info.type_);
            refs.name(&info.inductive_name);
        }
        if let Some(info) = recursor {
            refs.expression(&info.type_);
            refs.name(&info.inductive_name);
            for rule in &info.rules {
                refs.name(&rule.constructor_name);
                refs.expression(&rule.rhs);
            }
        }
        if let Some(info) = quotient {
            refs.expression(&info.type_);
        }
        for (_, expression) in &defaults {
            if let Some(expression) = expression {
                refs.expression(expression);
            }
        }
        if let Some(parents) = parents {
            for (parent, projection) in parents {
                refs.name(parent);
                refs.name(projection);
            }
        }
        if let Some(name) = implementation {
            refs.name(name);
        }
        if refs.exhausted.get() {
            return Err(limit(subject, "expression nodes per declaration", MAX_EXPR_NODES));
        }
        members.insert(current, record.bytes);
        for name in std::mem::take(refs.names.get_mut()) {
            if !members.contains_key(&name) {
                pending.insert(name);
            }
        }
        if pending.len() > MAX_MEMBERS.saturating_sub(members.len()) {
            return Err(limit(subject, "pending declarations", MAX_MEMBERS));
        }
    }

    let mut output = LimitedBytes {
        bytes: Vec::with_capacity(total_bytes.saturating_add(128).min(MAX_CLOSURE_BYTES)),
        limit: MAX_CLOSURE_BYTES,
    };
    bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .with_little_endian()
        .serialize_into(
            &mut output,
            &(
                "trust-clean-origin.typed-dependency-closure/bincode1-fixed-le",
                ENVIRONMENT_DIGEST_MODE_DEPENDENCY_CLOSURE,
                subject,
                &members,
            ),
        )
        .map_err(|error| EnvironmentDigestRefusal::Encoding {
            name: subject.to_string(),
            reason: error.to_string(),
        })?;
    Ok(EnvironmentDigest::from_validated_hex(trust_types::digest::stable_sha256_hex(&output.bytes)))
}
