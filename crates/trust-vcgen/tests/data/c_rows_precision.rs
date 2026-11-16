//! The four class-(c) precision rows of the 2026-10-19 seal reading (aterm 6ac89ba10):
//! proved by the channel `trust-edbb3f30`, UNKNOWN (no counterexample, no timeout) on the
//! seal-6 and seal-7 candidates. Each function below is the aterm function's body VERBATIM;
//! only the crate-local helpers it calls are stubbed with the same signatures.
//!
//! * `size_words` — aterm-messages `waits.rs:110` `(bytes + MB / 2)`, safe because the
//!   first branch took every `bytes >= GB - MB / 2`.
//! * `lift_points` — aterm-messages `animate.rs:835` `x - g`, safe because `x` is `g + q`
//!   for the `q` the checked add already took.
//! * `Parser::parse_and_dispatch_osc` — aterm-parser `dispatch.rs:718` `&rest[m + 1..]`,
//!   safe because `position` returns an index below `rest.len()`.
//! * `goal_active` — aterm-phase `turn.rs:157` `&rows[frame.bottom + 1..]`, safe because
//!   `rows[frame.bottom]` already checked `frame.bottom < rows.len()`.
//!
//! Each `*_twin` is WRONG: it panics natively (`-C overflow-checks=on`, `-O0` and `-O3`) at
//! the line marked `// PANIC` on the input in its comment. `tests/c_rows_precision_realmir.rs`
//! pins the rows of the compiler's own extraction of each (`tests/fixtures/c_rows_precision/`).
#![allow(dead_code, clippy::all)]

// ---- aterm-messages waits::size_words -----------------------------------------------

pub fn size_words(bytes: u64) -> String {
    const KB: u64 = 1_000;
    const MB: u64 = 1_000_000;
    const GB: u64 = 1_000_000_000;
    // Tenths of the unit, rounded half up, in integers.
    let tenths = |unit: u64| (bytes.saturating_mul(10) + unit / 2) / unit;
    if bytes >= GB - MB / 2 {
        let t = tenths(GB);
        format!("{}.{} GB", t / 10, t % 10)
    } else if bytes >= 10 * MB - MB / 20 {
        format!("{} MB", (bytes + MB / 2) / MB)
    } else if bytes >= MB - KB / 2 {
        let t = tenths(MB);
        format!("{}.{} MB", t / 10, t % 10)
    } else if bytes >= KB {
        format!("{} KB", (bytes + KB / 2) / KB)
    } else {
        format!("{bytes} B")
    }
}

/// WRONG: the first branch takes only `bytes >= u64::MAX - MB / 4`, so
/// `bytes = u64::MAX - MB / 4 - 1` reaches the `MB` branch and `bytes + MB / 2` overflows.
pub fn size_words_twin(bytes: u64) -> String {
    const KB: u64 = 1_000;
    const MB: u64 = 1_000_000;
    const GB: u64 = 1_000_000_000;
    let tenths = |unit: u64| (bytes.saturating_mul(10) + unit / 2) / unit;
    if bytes >= u64::MAX - MB / 4 {
        let t = tenths(GB);
        format!("{}.{} GB", t / 10, t % 10)
    } else if bytes >= 10 * MB - MB / 20 {
        format!("{} MB", (bytes + MB / 2) / MB) // PANIC
    } else if bytes >= MB - KB / 2 {
        let t = tenths(MB);
        format!("{}.{} MB", t / 10, t % 10)
    } else if bytes >= KB {
        format!("{} KB", (bytes + KB / 2) / KB)
    } else {
        format!("{bytes} B")
    }
}

// ---- aterm-messages animate::lift_points --------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default)]
pub struct Tone {
    pub fill: u8,
    pub lift: u8,
    pub warn: u8,
}

fn raised_cosine(d: i64, r: i64, peak: u8) -> u8 {
    if d == r { 0 } else { peak }
}

const LIFT_STOPS: usize = 16;

fn lift_points(g: i64, r: i64, e: i64, peak: u8, ink: Tone) -> Vec<(i64, Tone)> {
    let mut points = Vec::with_capacity(LIFT_STOPS * 2 + 3);
    let n = i64::try_from(LIFT_STOPS).unwrap_or(16);
    for k in -n..=n {
        let x = g + r * k / n;
        if x > 0 && x < e {
            points.push((
                x,
                Tone {
                    lift: raised_cosine(x - g, r, peak),
                    ..ink
                },
            ));
        }
    }
    points
}

/// WRONG: `x` wraps, so it is no longer `g + q`: `g = i64::MIN + 5, r = 16, e = i64::MAX`
/// gives `x = i64::MAX - 10` at `k = -16`, and `x - g` overflows.
fn lift_points_twin(g: i64, r: i64, e: i64, peak: u8, ink: Tone) -> Vec<(i64, Tone)> {
    let mut points = Vec::with_capacity(LIFT_STOPS * 2 + 3);
    let n = i64::try_from(LIFT_STOPS).unwrap_or(16);
    for k in -n..=n {
        let x = g.wrapping_add(r * k / n);
        if x > 0 && x < e {
            points.push((
                x,
                Tone {
                    lift: raised_cosine(x - g, r, peak), // PANIC
                    ..ink
                },
            ));
        }
    }
    points
}

// ---- aterm-parser Parser::parse_and_dispatch_osc ------------------------------------

pub trait ActionSink {
    fn osc_dispatch_with_terminator(&mut self, params: &[&[u8]], bel_terminated: bool);
}

fn pty_wrap_ref<'a, 'b>(params: &'a [&'b [u8]]) -> &'a [&'b [u8]] {
    params
}

pub struct Parser;

impl Parser {
    fn parse_and_dispatch_osc<S: ActionSink>(data: &[u8], sink: &mut S, bel_terminated: bool) {
        let Some(k) = data.iter().position(|&b| b == b';') else {
            let params: [&[u8]; 1] = [data];
            sink.osc_dispatch_with_terminator(pty_wrap_ref(&params[..]), bel_terminated);
            return;
        };
        let p0 = &data[..k];
        let rest = &data[k + 1..];
        let Some(m) = rest.iter().position(|&b| b == b';') else {
            let params: [&[u8]; 2] = [p0, rest];
            sink.osc_dispatch_with_terminator(pty_wrap_ref(&params[..]), bel_terminated);
            return;
        };
        Self::parse_osc_from_third_param(p0, &rest[..m], &rest[m + 1..], sink, bel_terminated);
    }

    /// WRONG: skips one byte too many after the second `;`: `data = b"a;b;"` gives
    /// `rest = b"b;"`, `m = 1`, and `&rest[3..]` is out of bounds.
    fn parse_and_dispatch_osc_twin<S: ActionSink>(data: &[u8], sink: &mut S, bel_terminated: bool) {
        let Some(k) = data.iter().position(|&b| b == b';') else {
            let params: [&[u8]; 1] = [data];
            sink.osc_dispatch_with_terminator(pty_wrap_ref(&params[..]), bel_terminated);
            return;
        };
        let p0 = &data[..k];
        let rest = &data[k + 1..];
        let Some(m) = rest.iter().position(|&b| b == b';') else {
            let params: [&[u8]; 2] = [p0, rest];
            sink.osc_dispatch_with_terminator(pty_wrap_ref(&params[..]), bel_terminated);
            return;
        };
        Self::parse_osc_from_third_param(p0, &rest[..m], &rest[m + 2..], sink, bel_terminated); // PANIC
    }

    #[inline(never)]
    fn parse_osc_from_third_param<S: ActionSink>(
        p0: &[u8],
        p1: &[u8],
        rest: &[u8],
        sink: &mut S,
        bel_terminated: bool,
    ) {
        let params: [&[u8]; 3] = [p0, p1, rest];
        sink.osc_dispatch_with_terminator(&params[..], bel_terminated);
    }
}

// ---- aterm-phase turn::goal_active --------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Frame {
    pub(crate) top: usize,
    pub(crate) bottom: usize,
}

pub(crate) struct StatusBlock {
    pub(crate) status: Option<usize>,
    pub(crate) end: usize,
    pub(crate) from: usize,
}

mod text {
    pub(crate) fn trim_start(s: &str) -> &str {
        s.trim_start_matches(' ')
    }

    pub(crate) fn trim_end(s: &str) -> &str {
        s.trim_end_matches(' ')
    }
}

fn is_rule(row: &str) -> bool {
    row.starts_with('─')
}

pub(crate) fn composer_frame(rows: &[String]) -> Option<Frame> {
    let top = rows.iter().position(|r| is_rule(r))?;
    let bottom = rows.iter().rposition(|r| is_rule(r))?;
    (top < bottom).then_some(Frame { top, bottom })
}

pub(crate) fn status_block(rows: &[String], top: usize) -> StatusBlock {
    let from = top.min(rows.len());
    StatusBlock { status: None, end: from, from }
}

pub(crate) fn is_against_right_edge(row: &str, width: usize) -> bool {
    text::trim_end(row).chars().count() + 3 >= width
}

pub fn goal_active(rows: &[String]) -> bool {
    let Some(frame) = composer_frame(rows) else {
        return false;
    };
    let width = crate::text::trim_end(&rows[frame.bottom]).chars().count();
    let from = status_block(rows, frame.top).from;
    rows[from..frame.top]
        .iter()
        .chain(&rows[frame.bottom + 1..])
        .any(|r| {
            crate::text::trim_start(r).starts_with("◎ /goal active")
                && is_against_right_edge(r, width)
        })
}

/// WRONG: skips one row too many under the bottom rule: `rows = ["─", "─"]` gives
/// `frame.bottom = 1 = rows.len() - 1`, and `&rows[3..]` is out of bounds.
pub fn goal_active_twin(rows: &[String]) -> bool {
    let Some(frame) = composer_frame(rows) else {
        return false;
    };
    let width = crate::text::trim_end(&rows[frame.bottom]).chars().count();
    let from = status_block(rows, frame.top).from;
    rows[from..frame.top]
        .iter()
        .chain(&rows[frame.bottom + 2..]) // PANIC
        .any(|r| {
            crate::text::trim_start(r).starts_with("◎ /goal active")
                && is_against_right_edge(r, width)
        })
}
