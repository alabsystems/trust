//! Pattern AST: the parser's output, consumed by `compile`.
//!
//! Character classes stay structural here (items / v-mode set expressions)
//! because their *sets* depend on the effective flags at the use site
//! (`(?i:…)` modifiers change `\w`'s ui extension and v-mode folding), which
//! only the compiler knows.
//!
//! Author: Andrew Yates
//! Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

/// A named-group record: name, 1-based group index, and its
/// disjunction-alternative path (for MightBothParticipate).
#[derive(Debug, Clone)]
pub struct GroupName {
    pub name: String,
    pub index: u32,
    pub path: Vec<(u32, u32)>, // (disjunction id, alternative index)
}

#[derive(Debug, Clone)]
pub struct Parsed {
    pub root: Node,
    pub n_groups: u32,
    pub group_names: Vec<GroupName>,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ModFlags {
    pub i: bool,
    pub m: bool,
    pub s: bool,
}

#[derive(Debug, Clone)]
pub enum Node {
    Empty,
    /// Disjunction: alternatives in preference order.
    Alternation(Vec<Node>),
    Concat(Vec<Node>),
    /// A single character (code point in u/v mode, code unit otherwise).
    Literal(u32),
    Dot,
    Class(ClassAst),
    Group {
        index: u32,
        body: Box<Node>,
    },
    NonCapGroup(Box<Node>),
    /// `(?ims-ims: …)`.
    ModGroup {
        add: ModFlags,
        remove: ModFlags,
        body: Box<Node>,
    },
    Quant {
        min: u64,
        /// `u64::MAX` = unbounded.
        max: u64,
        greedy: bool,
        body: Box<Node>,
    },
    LineStart,
    LineEnd,
    WordBoundary {
        negate: bool,
    },
    Look {
        behind: bool,
        negative: bool,
        body: Box<Node>,
    },
    /// Numeric backreference (validated against group count post-parse).
    Backref(u32),
    /// Named backreference, resolved post-parse to all groups of that name.
    NamedBackref(Vec<u32>),
    /// Unresolved named backreference (parser-internal).
    NamedBackrefRaw(String),
}

/// A `\d \D \s \S \w \W \p \P` class escape (top-level or in-class).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EscClass {
    Digit { negate: bool },
    Space { negate: bool },
    Word { negate: bool },
    Property {
        negate: bool,
        chars: &'static [(u32, u32)],
        /// Property-of-strings members (v-mode lone names only).
        strings: &'static [&'static [u32]],
    },
}

impl EscClass {
    pub fn negated(&self) -> bool {
        match self {
            EscClass::Digit { negate }
            | EscClass::Space { negate }
            | EscClass::Word { negate }
            | EscClass::Property { negate, .. } => *negate,
        }
    }

    pub fn may_contain_strings(&self) -> bool {
        matches!(self, EscClass::Property { negate: false, strings, .. } if !strings.is_empty())
    }
}

/// Non-v class item.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ClassItem {
    Char(u32),
    Range(u32, u32),
    Esc(EscClass),
}

/// v-mode class set operand.
#[derive(Debug, Clone)]
pub enum VOperand {
    Char(u32),
    Range(u32, u32),
    Esc(EscClass),
    Nested { negate: bool, expr: Box<VExpr> },
    /// `\q{…|…}` string disjunction (each string as code points; any
    /// length, including 0; length-1 entries are still "chars" per spec).
    Strings(Vec<Vec<u32>>),
}

/// v-mode class set expression: exactly one operator kind per level.
#[derive(Debug, Clone)]
pub enum VExpr {
    /// Union by juxtaposition (includes the single-operand case).
    Union(Vec<VOperand>),
    /// `op && op && …`
    Intersection(Vec<VOperand>),
    /// `op -- op -- …`
    Subtraction(Vec<VOperand>),
}

#[derive(Debug, Clone)]
pub enum ClassAst {
    /// `[...]` under the non-v grammars. `negate` inverts at match time.
    Simple { negate: bool, items: Vec<ClassItem> },
    /// `[...]` under the v grammar. `negate` complements at compile time.
    VMode { negate: bool, expr: VExpr },
}

impl VOperand {
    pub fn may_contain_strings(&self) -> bool {
        match self {
            VOperand::Char(_) | VOperand::Range(..) => false,
            VOperand::Esc(e) => e.may_contain_strings(),
            VOperand::Nested { negate, expr } => !negate && expr.may_contain_strings(),
            VOperand::Strings(ss) => ss.iter().any(|s| s.len() != 1),
        }
    }
}

impl VExpr {
    pub fn may_contain_strings(&self) -> bool {
        match self {
            VExpr::Union(ops) => ops.iter().any(|o| o.may_contain_strings()),
            VExpr::Intersection(ops) => ops.iter().all(|o| o.may_contain_strings()),
            VExpr::Subtraction(ops) => ops[0].may_contain_strings(),
        }
    }
}
