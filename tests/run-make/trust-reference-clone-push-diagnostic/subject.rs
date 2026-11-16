// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Minimized producer diagnostic, not Clean's production helper or its model.
//! The non-pure payload and reference-field read precede a real derived Clone
//! and the external Vec::push edge. Control cases change one registration input.
//! The separate enum control exercises discriminant-holder registration; its
//! outcome is observed rather than assumed to match the production refusal.

#[derive(Clone)]
pub struct Rule {
    pub tag: u32,
    #[cfg(not(pure_payload))]
    pub payload: Vec<u32>,
    #[cfg(pure_payload)]
    pub payload: u32,
}

#[cfg(any(reference_first, pure_payload))]
pub fn index_rule(rules: &mut Vec<Rule>, rule: &Rule) {
    if rule.tag == 1 {
        rules.push(rule.clone());
    }
}

#[cfg(no_preread)]
pub fn index_rule(rules: &mut Vec<Rule>, rule: &Rule) {
    rules.push(rule.clone());
}

#[cfg(by_value)]
pub fn index_rule(rules: &mut Vec<Rule>, rule: Rule) {
    rules.push(rule.clone());
}

#[cfg(enum_reference_first)]
#[derive(Clone)]
pub enum Mode {
    One,
    Other,
}

#[cfg(enum_reference_first)]
#[derive(Clone)]
pub struct EnumRule {
    pub mode: Mode,
    pub payload: Vec<u32>,
}

#[cfg(enum_reference_first)]
pub fn index_enum_rule(rules: &mut Vec<EnumRule>, rule: &EnumRule) {
    match rule.mode {
        Mode::One => rules.push(rule.clone()),
        Mode::Other => {}
    }
}
