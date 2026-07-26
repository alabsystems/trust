//! AST → VM program compilation.
//!
//! All flag-dependent semantics resolve here, statically: each consuming
//! instruction carries its fold mode and direction, so `(?ims-ims:…)`
//! modifiers and lookbehind direction cost nothing at match time. Class
//! sets are built per the spec's evaluation order — u/non-u ignoreCase
//! classes store the canonical image and match `canon(input) ∈ image`
//! (CharacterSetMatcher's ∃-canonicalize rule), `\D \S \W \P` complement at
//! compile time (CompileToCharSet), v-mode sets fold at each operand
//! (MaybeSimpleCaseFolding) and complement within `AllCharacters(rer)`
//! (the scf-fixed universe when ignoreCase).
//!
//! Author: Andrew Yates
//! Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::ast::*;
use crate::classes::{complement_ranges, CharSet, MAX_CP};
use crate::generated::case_tables::SCF_SOURCES;
use crate::unicode::{canonicalize, Fold, DIGIT_RANGES, WHITESPACE_RANGES, WORD_BASIC};
use crate::vm::{patch, ClassTable, Insn, Program};
use crate::{CompileError, Flags};

const PATCH: u32 = u32::MAX;

#[derive(Clone, Copy)]
struct Ctx {
    i: bool,
    m: bool,
    s: bool,
    back: bool,
}

pub(crate) fn compile(p: &Parsed, flags: Flags) -> Result<Program, CompileError> {
    let mut c = C {
        insns: Vec::new(),
        classes: Vec::new(),
        lists: Vec::new(),
        n_loops: 0,
        flags,
    };
    let ctx = Ctx {
        i: flags.ignore_case,
        m: flags.multiline,
        s: flags.dot_all,
        back: false,
    };
    c.node(&p.root, ctx)?;
    c.insns.push(Insn::Accept);
    Ok(Program {
        insns: c.insns,
        classes: c.classes,
        backref_lists: c.lists,
        n_slots: 2 * (p.n_groups as usize + 1),
        n_loops: c.n_loops as usize,
        unicode: flags.has_either_unicode(),
    })
}

struct C {
    insns: Vec<Insn>,
    classes: Vec<ClassTable>,
    lists: Vec<Vec<u32>>,
    n_loops: u32,
    flags: Flags,
}

impl C {
    fn emit(&mut self, insn: Insn) -> usize {
        self.insns.push(insn);
        self.insns.len() - 1
    }

    fn here(&self) -> u32 {
        self.insns.len() as u32
    }

    fn fold(&self, ctx: Ctx) -> Fold {
        if !ctx.i {
            Fold::None
        } else if self.flags.has_either_unicode() {
            Fold::Scf
        } else {
            Fold::NonU
        }
    }

    fn node(&mut self, n: &Node, ctx: Ctx) -> Result<(), CompileError> {
        match n {
            Node::Empty => {}
            Node::Literal(cp) => {
                let fold = self.fold(ctx);
                self.emit(Insn::Char {
                    cp: canonicalize(*cp, fold),
                    fold,
                    back: ctx.back,
                });
            }
            Node::Dot => {
                self.emit(Insn::Dot { dot_all: ctx.s, back: ctx.back });
            }
            Node::LineStart => {
                self.emit(Insn::Bol { multiline: ctx.m });
            }
            Node::LineEnd => {
                self.emit(Insn::Eol { multiline: ctx.m });
            }
            Node::WordBoundary { negate } => {
                self.emit(Insn::WordB {
                    negate: *negate,
                    extended: ctx.i && self.flags.has_either_unicode(),
                });
            }
            Node::Concat(xs) => {
                if ctx.back {
                    for x in xs.iter().rev() {
                        self.node(x, ctx)?;
                    }
                } else {
                    for x in xs {
                        self.node(x, ctx)?;
                    }
                }
            }
            Node::Alternation(alts) => {
                let mut jmps = Vec::new();
                for (k, alt) in alts.iter().enumerate() {
                    if k + 1 < alts.len() {
                        let split = self.emit(Insn::Split { prefer: 0, alt: PATCH });
                        self.insns[split] = Insn::Split {
                            prefer: split as u32 + 1,
                            alt: PATCH,
                        };
                        self.node(alt, ctx)?;
                        jmps.push(self.emit(Insn::Jmp { to: PATCH }));
                        let here = self.here();
                        patch(&mut self.insns[split], here);
                    } else {
                        self.node(alt, ctx)?;
                    }
                }
                let end = self.here();
                for j in jmps {
                    patch(&mut self.insns[j], end);
                }
            }
            Node::Group { index, body } => {
                let (first, second) = if ctx.back {
                    (2 * index + 1, 2 * index)
                } else {
                    (2 * index, 2 * index + 1)
                };
                self.emit(Insn::Save { slot: first });
                self.node(body, ctx)?;
                self.emit(Insn::Save { slot: second });
            }
            Node::NonCapGroup(body) => self.node(body, ctx)?,
            Node::ModGroup { add, remove, body } => {
                let inner = Ctx {
                    i: (ctx.i || add.i) && !remove.i,
                    m: (ctx.m || add.m) && !remove.m,
                    s: (ctx.s || add.s) && !remove.s,
                    back: ctx.back,
                };
                self.node(body, inner)?;
            }
            Node::Quant { min, max, greedy, body } => {
                self.quant(*min, *max, *greedy, body, ctx)?;
            }
            Node::Look { behind, negative, body } => {
                let lp = self.emit(Insn::Look {
                    negative: *negative,
                    body: 0,
                    next: PATCH,
                });
                self.insns[lp] = Insn::Look {
                    negative: *negative,
                    body: lp as u32 + 1,
                    next: PATCH,
                };
                self.node(body, Ctx { back: *behind, ..ctx })?;
                self.emit(Insn::Accept);
                let here = self.here();
                patch(&mut self.insns[lp], here);
            }
            Node::Backref(n) => {
                let list = self.add_list(vec![*n]);
                self.emit(Insn::Backref {
                    list,
                    fold: self.fold(ctx),
                    back: ctx.back,
                });
            }
            Node::NamedBackref(groups) => {
                let list = self.add_list(groups.clone());
                self.emit(Insn::Backref {
                    list,
                    fold: self.fold(ctx),
                    back: ctx.back,
                });
            }
            Node::NamedBackrefRaw(_) => unreachable!("unresolved named backref"),
            Node::Class(cls) => self.class(cls, ctx)?,
        }
        Ok(())
    }

    fn quant(
        &mut self,
        min: u64,
        max: u64,
        greedy: bool,
        body: &Node,
        ctx: Ctx,
    ) -> Result<(), CompileError> {
        if max == 0 {
            // RepeatMatcher step 1: matches emptily, touches nothing.
            return Ok(());
        }
        let id = self.n_loops;
        self.n_loops += 1;
        let (cap_lo, cap_hi) = group_range(body).unwrap_or((1, 0));
        self.emit(Insn::LoopInit { id });
        let decide = self.emit(Insn::LoopDecide {
            id,
            min,
            max,
            greedy,
            enter: 0,
            exit: PATCH,
        });
        self.insns[decide] = Insn::LoopDecide {
            id,
            min,
            max,
            greedy,
            enter: decide as u32 + 1,
            exit: PATCH,
        };
        self.emit(Insn::LoopEnter { id, cap_lo, cap_hi });
        self.node(body, ctx)?;
        self.emit(Insn::LoopEnd {
            id,
            head: decide as u32,
            min,
        });
        let here = self.here();
        patch(&mut self.insns[decide], here);
        Ok(())
    }

    fn add_class(&mut self, ranges: Vec<(u32, u32)>) -> u32 {
        self.classes.push(ClassTable { ranges });
        (self.classes.len() - 1) as u32
    }

    fn add_list(&mut self, groups: Vec<u32>) -> u32 {
        if let Some(i) = self.lists.iter().position(|l| *l == groups) {
            return i as u32;
        }
        self.lists.push(groups);
        (self.lists.len() - 1) as u32
    }

    // -- character classes -------------------------------------------------

    fn class(&mut self, cls: &ClassAst, ctx: Ctx) -> Result<(), CompileError> {
        match cls {
            ClassAst::Simple { negate, items } => {
                let fold = self.fold(ctx);
                let mut set = CharSet::default();
                for item in items {
                    match item {
                        ClassItem::Char(c) => set.add_range(*c, *c),
                        ClassItem::Range(a, b) => set.add_range(*a, *b),
                        ClassItem::Esc(e) => set = set.union(&self.esc_set(e, ctx)),
                    }
                }
                let stored = set.fold_image(fold);
                let idx = self.add_class(stored.ranges);
                self.emit(Insn::Class {
                    idx,
                    invert: *negate,
                    fold,
                    back: ctx.back,
                });
                Ok(())
            }
            ClassAst::VMode { negate, expr } => self.v_class(*negate, expr, ctx),
        }
    }

    /// Base set for `\d \s \w` (and their extensions) — no negation.
    fn esc_base(&self, e: &EscClass, ctx: Ctx) -> CharSet {
        match e {
            EscClass::Digit { .. } => CharSet::from_ranges(DIGIT_RANGES.to_vec()),
            EscClass::Space { .. } => CharSet::from_ranges(WHITESPACE_RANGES.to_vec()),
            EscClass::Word { .. } => {
                let mut s = CharSet::from_ranges(WORD_BASIC.to_vec());
                if ctx.i && self.flags.has_either_unicode() {
                    // WordCharacters(rer): chars canonicalizing into the
                    // basic set (U+017F, U+212A), derived from the tables.
                    for cp in crate::unicode::word_char_extras() {
                        s.add_range(cp, cp);
                    }
                }
                s
            }
            EscClass::Property { chars, strings, .. } => {
                let mut s = CharSet::from_ranges(chars.to_vec());
                for st in strings.iter() {
                    s.add_string(st.to_vec());
                }
                s
            }
        }
    }

    /// Non-v class escape set: negation complements at compile time
    /// (CompileToCharSet), within all code units / code points.
    fn esc_set(&self, e: &EscClass, ctx: Ctx) -> CharSet {
        let base = self.esc_base(e, ctx);
        if e.negated() {
            let hi = if self.flags.has_either_unicode() { MAX_CP } else { 0xFFFF };
            base.complement_within(&[(0, hi)])
        } else {
            base
        }
    }

    // -- v-mode ------------------------------------------------------------

    /// AllCharacters(rer) for v mode: all code points, or (ignoreCase) the
    /// scf-fixed points only.
    fn v_universe(&self, ctx: Ctx) -> Vec<(u32, u32)> {
        if ctx.i {
            complement_ranges(SCF_SOURCES, 0, MAX_CP)
        } else {
            vec![(0, MAX_CP)]
        }
    }

    fn v_fold(&self, ctx: Ctx) -> Fold {
        if ctx.i { Fold::Scf } else { Fold::None }
    }

    fn eval_vexpr(&self, e: &VExpr, ctx: Ctx) -> CharSet {
        match e {
            VExpr::Union(ops) => {
                let mut acc = CharSet::default();
                for op in ops {
                    acc = acc.union(&self.eval_voperand(op, ctx));
                }
                acc
            }
            VExpr::Intersection(ops) => {
                let mut acc = self.eval_voperand(&ops[0], ctx);
                for op in &ops[1..] {
                    acc = acc.intersect(&self.eval_voperand(op, ctx));
                }
                acc
            }
            VExpr::Subtraction(ops) => {
                let mut acc = self.eval_voperand(&ops[0], ctx);
                for op in &ops[1..] {
                    acc = acc.subtract(&self.eval_voperand(op, ctx));
                }
                acc
            }
        }
    }

    /// Operand evaluation with the spec's order: complement (within
    /// AllCharacters) BEFORE folding for `\D \S \W \P`; folding BEFORE
    /// complement for nested `[^…]` (whose leaves already folded).
    fn eval_voperand(&self, op: &VOperand, ctx: Ctx) -> CharSet {
        let f = self.v_fold(ctx);
        match op {
            VOperand::Char(c) => CharSet::single(*c).fold_image(f),
            VOperand::Range(a, b) => CharSet::from_ranges(vec![(*a, *b)]).fold_image(f),
            VOperand::Esc(e) => {
                // v mode folds the escape's set BEFORE complementing
                // (CharacterComplement of MaybeSimpleCaseFolding), so e.g.
                // /[\P{Lu}]/vi rejects "A" — unlike u mode's asymmetry.
                let base = self.esc_base(e, ctx).fold_image(f);
                if e.negated() {
                    base.complement_within(&self.v_universe(ctx))
                } else {
                    base
                }
            }
            VOperand::Nested { negate, expr } => {
                let s = self.eval_vexpr(expr, ctx);
                if *negate {
                    debug_assert!(s.strings.is_empty());
                    s.complement_within(&self.v_universe(ctx))
                } else {
                    s
                }
            }
            VOperand::Strings(list) => {
                let mut s = CharSet::default();
                for st in list {
                    s.add_string(st.clone());
                }
                s.fold_image(f)
            }
        }
    }

    fn v_class(&mut self, negate: bool, expr: &VExpr, ctx: Ctx) -> Result<(), CompileError> {
        let fold = self.v_fold(ctx);
        let mut set = self.eval_vexpr(expr, ctx);
        if negate {
            debug_assert!(set.strings.is_empty());
            set = set.complement_within(&self.v_universe(ctx));
        }
        if set.strings.is_empty() {
            let idx = self.add_class(set.ranges);
            self.emit(Insn::Class {
                idx,
                invert: false,
                fold,
                back: ctx.back,
            });
            return Ok(());
        }
        // Class with strings: an alternation in the spec's preference order
        // — strings by descending length, the single-char set (length 1),
        // then the empty string if present.
        enum Br<'s> {
            Str(&'s [u32]),
            Chars,
            Empty,
        }
        let mut branches: Vec<Br> = Vec::new();
        let mut empty_present = false;
        for s in &set.strings {
            if s.is_empty() {
                empty_present = true;
            } else {
                branches.push(Br::Str(s));
            }
        }
        if !set.ranges.is_empty() {
            branches.push(Br::Chars);
        }
        if empty_present {
            branches.push(Br::Empty);
        }
        let chars_idx = if set.ranges.is_empty() {
            None
        } else {
            Some(self.add_class(set.ranges.clone()))
        };
        let mut jmps = Vec::new();
        let n = branches.len();
        for (k, br) in branches.into_iter().enumerate() {
            let split = if k + 1 < n {
                let split = self.emit(Insn::Split { prefer: 0, alt: PATCH });
                self.insns[split] = Insn::Split {
                    prefer: split as u32 + 1,
                    alt: PATCH,
                };
                Some(split)
            } else {
                None
            };
            match br {
                Br::Str(s) => {
                    let cps: Vec<u32> = if ctx.back {
                        s.iter().rev().copied().collect()
                    } else {
                        s.to_vec()
                    };
                    for cp in cps {
                        // String members are pre-folded; fold the input.
                        self.emit(Insn::Char { cp, fold, back: ctx.back });
                    }
                }
                Br::Chars => {
                    self.emit(Insn::Class {
                        idx: chars_idx.unwrap(),
                        invert: false,
                        fold,
                        back: ctx.back,
                    });
                }
                Br::Empty => {}
            }
            if let Some(split) = split {
                jmps.push(self.emit(Insn::Jmp { to: PATCH }));
                let here = self.here();
                patch(&mut self.insns[split], here);
            }
        }
        let end = self.here();
        for j in jmps {
            patch(&mut self.insns[j], end);
        }
        Ok(())
    }
}

/// The contiguous range of capture-group indices within a subtree (parser
/// assigns indices in DFS pre-order). Lookaround bodies count
/// (RepeatMatcher resets every capture inside the quantified Atom).
fn group_range(n: &Node) -> Option<(u32, u32)> {
    fn merge(a: Option<(u32, u32)>, b: Option<(u32, u32)>) -> Option<(u32, u32)> {
        match (a, b) {
            (None, x) | (x, None) => x,
            (Some((a1, a2)), Some((b1, b2))) => Some((a1.min(b1), a2.max(b2))),
        }
    }
    match n {
        Node::Group { index, body } => merge(Some((*index, *index)), group_range(body)),
        Node::Alternation(xs) | Node::Concat(xs) => {
            xs.iter().fold(None, |acc, x| merge(acc, group_range(x)))
        }
        Node::NonCapGroup(body)
        | Node::ModGroup { body, .. }
        | Node::Quant { body, .. }
        | Node::Look { body, .. } => group_range(body),
        _ => None,
    }
}
