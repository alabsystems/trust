//! The backtracking VM.
//!
//! Spec correspondence (ES2025 §22.2.2): the compiled program's `Split`
//! preference order is the spec's Matcher/MatcherContinuation choice order;
//! the backtrack stack holds not-yet-taken continuations; captures and loop
//! counters are journaled so a backtrack restores exactly the spec's
//! MatchState. Loops implement RepeatMatcher: per-iteration capture reset
//! (`LoopEnter`), no exit before `min`, and the empty-match check on
//! iterations at or beyond `min` (`LoopEnd`). Lookarounds are barriered
//! sub-programs: the first success commits (choice points above the barrier
//! are discarded — the spec calls the inner Matcher with a trivial
//! continuation), positive keeps inner captures, negative discards them.
//! Every dispatched instruction and every backtrack pop costs one step
//! against the budget; exhaustion is a sound `Budget` refusal (ReDoS guard).
//!
//! Author: Andrew Yates
//! Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::unicode::{
    canonicalize, in_ranges, is_line_terminator, is_word_char, read_backward, read_forward, Fold,
};
use crate::ExecError;

pub(crate) const UNSET: usize = usize::MAX;
const PATCH: u32 = u32::MAX;

#[derive(Debug, Clone)]
pub(crate) struct Program {
    pub insns: Vec<Insn>,
    pub classes: Vec<ClassTable>,
    /// Backreference target groups (singleton for numeric refs; all
    /// same-named groups for named refs — at most one participates).
    pub backref_lists: Vec<Vec<u32>>,
    pub n_slots: usize,
    pub n_loops: usize,
    pub unicode: bool,
}

#[derive(Debug, Clone)]
pub(crate) struct ClassTable {
    /// Sorted, disjoint ranges. For ignoreCase classes this is already the
    /// canonical image (u/non-u modes) or the folded set (v mode), so
    /// membership is `canon(input) ∈ ranges`.
    pub ranges: Vec<(u32, u32)>,
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum Insn {
    Char { cp: u32, fold: Fold, back: bool },
    Class { idx: u32, invert: bool, fold: Fold, back: bool },
    Dot { dot_all: bool, back: bool },
    Bol { multiline: bool },
    Eol { multiline: bool },
    WordB { negate: bool, extended: bool },
    Jmp { to: u32 },
    Split { prefer: u32, alt: u32 },
    Save { slot: u32 },
    LoopInit { id: u32 },
    LoopDecide { id: u32, min: u64, max: u64, greedy: bool, enter: u32, exit: u32 },
    /// Iteration entry: journal the entry position, reset captures
    /// `cap_lo..=cap_hi` (RepeatMatcher step 3-4).
    LoopEnter { id: u32, cap_lo: u32, cap_hi: u32 },
    LoopEnd { id: u32, head: u32, min: u64 },
    Look { negative: bool, body: u32, next: u32 },
    Backref { list: u32, fold: Fold, back: bool },
    Accept,
}

pub(crate) fn patch(insn: &mut Insn, target: u32) {
    match insn {
        Insn::Jmp { to } => *to = target,
        Insn::Split { alt, .. } => {
            if *alt == PATCH {
                *alt = target;
            }
        }
        Insn::LoopDecide { exit, .. } => *exit = target,
        Insn::Look { next, .. } => *next = target,
        _ => unreachable!("unpatchable instruction"),
    }
}

#[derive(Clone, Copy)]
struct LoopState {
    count: u64,
    entry: usize,
}

enum J {
    Cap { slot: u32, old: usize },
    LoopCount { id: u32, old: u64 },
    LoopEntry { id: u32, old: usize },
}

struct Frame {
    pc: u32,
    pos: usize,
    j_len: usize,
}

struct LookFrame {
    bt_len: usize,
    j_len: usize,
    pos: usize,
    negative: bool,
    next: u32,
}

pub(crate) struct Machine<'a> {
    prog: &'a Program,
    input: &'a [u16],
    budget: u64,
    steps: u64,
    caps: Vec<usize>,
    loops: Vec<LoopState>,
    journal: Vec<J>,
    bt: Vec<Frame>,
    looks: Vec<LookFrame>,
}

enum Step {
    Next,
    Fail,
}

impl<'a> Machine<'a> {
    pub fn new(prog: &'a Program, input: &'a [u16], budget: u64) -> Machine<'a> {
        Machine {
            prog,
            input,
            budget,
            steps: 0,
            caps: vec![UNSET; prog.n_slots],
            loops: vec![LoopState { count: 0, entry: 0 }; prog.n_loops],
            journal: Vec::new(),
            bt: Vec::new(),
            looks: Vec::new(),
        }
    }

    /// One anchored attempt at `start`. The step budget is shared across
    /// attempts on the same Machine.
    pub fn run(&mut self, start: usize) -> Result<Option<Vec<usize>>, ExecError> {
        self.caps.fill(UNSET);
        for l in &mut self.loops {
            *l = LoopState { count: 0, entry: 0 };
        }
        self.journal.clear();
        self.bt.clear();
        self.looks.clear();

        let uni = self.prog.unicode;
        let mut pc: u32 = 0;
        let mut pos = start;
        loop {
            self.steps += 1;
            if self.steps > self.budget {
                return Err(ExecError::Budget);
            }
            let step = match self.prog.insns[pc as usize] {
                Insn::Char { cp, fold, back } => match self.read(pos, back, uni) {
                    Some((ch, w)) => {
                        if canonicalize(ch, fold) == cp {
                            pos = if back { pos - w } else { pos + w };
                            Step::Next
                        } else {
                            Step::Fail
                        }
                    }
                    None => Step::Fail,
                },
                Insn::Class { idx, invert, fold, back } => match self.read(pos, back, uni) {
                    Some((ch, w)) => {
                        let member = in_ranges(
                            &self.prog.classes[idx as usize].ranges,
                            canonicalize(ch, fold),
                        );
                        if member != invert {
                            pos = if back { pos - w } else { pos + w };
                            Step::Next
                        } else {
                            Step::Fail
                        }
                    }
                    None => Step::Fail,
                },
                Insn::Dot { dot_all, back } => match self.read(pos, back, uni) {
                    Some((ch, w)) => {
                        if dot_all || !is_line_terminator(ch) {
                            pos = if back { pos - w } else { pos + w };
                            Step::Next
                        } else {
                            Step::Fail
                        }
                    }
                    None => Step::Fail,
                },
                Insn::Bol { multiline } => {
                    if pos == 0
                        || (multiline
                            && is_line_terminator(read_backward(self.input, pos, uni).0))
                    {
                        Step::Next
                    } else {
                        Step::Fail
                    }
                }
                Insn::Eol { multiline } => {
                    if pos == self.input.len()
                        || (multiline
                            && is_line_terminator(read_forward(self.input, pos, uni).0))
                    {
                        Step::Next
                    } else {
                        Step::Fail
                    }
                }
                Insn::WordB { negate, extended } => {
                    let a = pos > 0
                        && is_word_char(read_backward(self.input, pos, uni).0, extended);
                    let b = pos < self.input.len()
                        && is_word_char(read_forward(self.input, pos, uni).0, extended);
                    if (a != b) != negate {
                        Step::Next
                    } else {
                        Step::Fail
                    }
                }
                Insn::Jmp { to } => {
                    pc = to;
                    continue;
                }
                Insn::Split { prefer, alt } => {
                    self.bt.push(Frame { pc: alt, pos, j_len: self.journal.len() });
                    pc = prefer;
                    continue;
                }
                Insn::Save { slot } => {
                    self.journal.push(J::Cap { slot, old: self.caps[slot as usize] });
                    self.caps[slot as usize] = pos;
                    Step::Next
                }
                Insn::LoopInit { id } => {
                    let l = self.loops[id as usize];
                    self.journal.push(J::LoopCount { id, old: l.count });
                    self.journal.push(J::LoopEntry { id, old: l.entry });
                    self.loops[id as usize] = LoopState { count: 0, entry: 0 };
                    Step::Next
                }
                Insn::LoopDecide { id, min, max, greedy, enter, exit } => {
                    let n = self.loops[id as usize].count;
                    if n < min {
                        pc = enter;
                    } else if n >= max {
                        pc = exit;
                    } else if greedy {
                        self.bt.push(Frame { pc: exit, pos, j_len: self.journal.len() });
                        pc = enter;
                    } else {
                        self.bt.push(Frame { pc: enter, pos, j_len: self.journal.len() });
                        pc = exit;
                    }
                    continue;
                }
                Insn::LoopEnter { id, cap_lo, cap_hi } => {
                    let old = self.loops[id as usize].entry;
                    self.journal.push(J::LoopEntry { id, old });
                    self.loops[id as usize].entry = pos;
                    if cap_lo <= cap_hi {
                        for g in cap_lo..=cap_hi {
                            for slot in [2 * g, 2 * g + 1] {
                                self.journal.push(J::Cap { slot, old: self.caps[slot as usize] });
                                self.caps[slot as usize] = UNSET;
                            }
                        }
                    }
                    Step::Next
                }
                Insn::LoopEnd { id, head, min } => {
                    let l = self.loops[id as usize];
                    // Empty-match rule: an optional iteration (count >= min)
                    // that consumed nothing fails (RepeatMatcher step d.a).
                    if l.count >= min && pos == l.entry {
                        Step::Fail
                    } else {
                        self.journal.push(J::LoopCount { id, old: l.count });
                        self.loops[id as usize].count = l.count + 1;
                        pc = head;
                        continue;
                    }
                }
                Insn::Look { negative, body, next } => {
                    self.looks.push(LookFrame {
                        bt_len: self.bt.len(),
                        j_len: self.journal.len(),
                        pos,
                        negative,
                        next,
                    });
                    pc = body;
                    continue;
                }
                Insn::Backref { list, fold, back } => {
                    let groups = &self.prog.backref_lists[list as usize];
                    let mut range = None;
                    for &g in groups {
                        let s = self.caps[2 * g as usize];
                        let e = self.caps[2 * g as usize + 1];
                        if s != UNSET && e != UNSET {
                            range = Some((s, e));
                            break;
                        }
                    }
                    match range {
                        None => Step::Next, // undefined capture matches empty
                        Some((s, e)) => {
                            let len = e - s;
                            let fits = if back { pos >= len } else { pos + len <= self.input.len() };
                            if !fits {
                                Step::Fail
                            } else {
                                let at = if back { pos - len } else { pos };
                                if self.backref_eq(s, e, at, fold, uni) {
                                    pos = if back { pos - len } else { pos + len };
                                    Step::Next
                                } else {
                                    Step::Fail
                                }
                            }
                        }
                    }
                }
                Insn::Accept => {
                    match self.looks.pop() {
                        Some(lf) => {
                            // Lookaround body succeeded: commit its first
                            // success (no backtracking into it).
                            self.bt.truncate(lf.bt_len);
                            if lf.negative {
                                // Assertion fails; discard inner captures.
                                self.undo(lf.j_len);
                                Step::Fail
                            } else {
                                pos = lf.pos;
                                pc = lf.next;
                                continue;
                            }
                        }
                        None => {
                            self.caps[0] = start;
                            self.caps[1] = pos;
                            return Ok(Some(self.caps.clone()));
                        }
                    }
                }
            };
            match step {
                Step::Next => {
                    pc += 1;
                }
                Step::Fail => {
                    // Backtrack: pop continuations, honoring look barriers.
                    loop {
                        self.steps += 1;
                        if self.steps > self.budget {
                            return Err(ExecError::Budget);
                        }
                        if let Some(lf) = self.looks.last() {
                            if self.bt.len() == lf.bt_len {
                                let lf = self.looks.pop().unwrap();
                                if lf.negative {
                                    // Inner failed => negative holds; the
                                    // original state continues.
                                    self.undo(lf.j_len);
                                    pos = lf.pos;
                                    pc = lf.next;
                                    break;
                                }
                                // Positive lookaround failed: keep failing
                                // below the barrier.
                                continue;
                            }
                        }
                        match self.bt.pop() {
                            Some(fr) => {
                                self.undo(fr.j_len);
                                pos = fr.pos;
                                pc = fr.pc;
                                break;
                            }
                            None => return Ok(None),
                        }
                    }
                }
            }
        }
    }

    fn read(&self, pos: usize, back: bool, uni: bool) -> Option<(u32, usize)> {
        if back {
            if pos == 0 {
                None
            } else {
                Some(read_backward(self.input, pos, uni))
            }
        } else if pos >= self.input.len() {
            None
        } else {
            Some(read_forward(self.input, pos, uni))
        }
    }

    /// Canonical elementwise comparison of the captured range [s, e) with
    /// the input at `at` (same unit length; compared by characters).
    fn backref_eq(&self, s: usize, e: usize, at: usize, fold: Fold, uni: bool) -> bool {
        let (mut i, mut j) = (s, at);
        while i < e {
            let (a, wa) = read_forward(self.input, i, uni);
            let (b, wb) = read_forward(self.input, j, uni);
            if canonicalize(a, fold) != canonicalize(b, fold) {
                return false;
            }
            i += wa;
            j += wb;
        }
        true
    }

    fn undo(&mut self, to: usize) {
        while self.journal.len() > to {
            match self.journal.pop().unwrap() {
                J::Cap { slot, old } => self.caps[slot as usize] = old,
                J::LoopCount { id, old } => self.loops[id as usize].count = old,
                J::LoopEntry { id, old } => self.loops[id as usize].entry = old,
            }
        }
    }
}
