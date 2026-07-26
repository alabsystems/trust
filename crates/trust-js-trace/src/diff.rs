// Trace equality + first-divergence explanation for triage. Equality is
// plain structural equality of the parsed schema — the projection already
// removed everything engine-incidental, so any inequality is a real
// divergence (or a projection-too-strong bug, which calibration surfaces).
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::trace::{Completion, HostEvent, ObservableTrace};

#[must_use]
pub fn traces_equal(a: &ObservableTrace, b: &ObservableTrace) -> bool {
    a == b
}

/// A short, human-readable statement of the FIRST point of divergence, for
/// the triage ledger. None iff the traces are equal.
#[must_use]
pub fn explain_divergence(a: &ObservableTrace, b: &ObservableTrace) -> Option<String> {
    if a == b {
        return None;
    }
    if a.schema != b.schema {
        return Some(format!("schema: {} vs {}", a.schema, b.schema));
    }
    if a.caps != b.caps {
        return Some("projection caps differ (mixed driver versions?)".to_string());
    }
    for (i, (ea, eb)) in a.events.iter().zip(b.events.iter()).enumerate() {
        if ea != eb {
            return Some(format!(
                "event[{i}]: {} vs {}",
                summarize_event(ea),
                summarize_event(eb)
            ));
        }
    }
    if a.events.len() != b.events.len() {
        let (longer, n) = if a.events.len() > b.events.len() {
            ("left", a.events.len())
        } else {
            ("right", b.events.len())
        };
        return Some(format!(
            "event count: {} vs {} ({longer} head has {n})",
            a.events.len(),
            b.events.len()
        ));
    }
    if a.completion != b.completion {
        return Some(format!(
            "completion: {} vs {}",
            summarize_completion(&a.completion),
            summarize_completion(&b.completion)
        ));
    }
    Some("traces differ (unlocalized)".to_string())
}

fn summarize_event(e: &HostEvent) -> String {
    match e {
        HostEvent::Stdout { v } => format!("stdout({} args): {}", v.len(), short_json(v)),
        HostEvent::Stderr { v } => format!("stderr({} args): {}", v.len(), short_json(v)),
        HostEvent::Host { v } => format!("host:{v}"),
    }
}

fn summarize_completion(c: &Completion) -> String {
    match c {
        Completion::Normal { v } => format!("normal {}", short_json(v)),
        Completion::Throw { v, phase } => match phase {
            Some(p) => format!("throw[{p}] {}", short_json(v)),
            None => format!("throw {}", short_json(v)),
        },
        Completion::HarnessIncludeError { v } => format!("harness-include-error {}", short_json(v)),
        Completion::DriverError { v } => format!("driver-error {}", short_json(v)),
    }
}

fn short_json<T: serde::Serialize>(v: &T) -> String {
    let s = serde_json::to_string(v).unwrap_or_else(|_| "<unserializable>".to_string());
    if s.len() > 200 {
        let mut end = 200;
        while !s.is_char_boundary(end) {
            end -= 1;
        }
        format!("{}…", &s[..end])
    } else {
        s
    }
}
