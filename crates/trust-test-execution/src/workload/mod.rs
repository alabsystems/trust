//! Complete native libtest observations, never execution or proof authority.
//!
//! A live producer must separately retain its compiled artifact, admitted
//! original process and actual retirement. Parsing these bytes supplies none
//! of those owners and does not authenticate arbitrary test-program behavior.

use std::collections::BTreeSet;

use serde::Serialize;

pub const TARGETS: [&str; 2] = ["ay_refutation_step_realbody", "ay_refutation_loop_realbody"];
pub const MAX_TEST_CASES: usize = 16_384;
pub const MAX_NAME_BYTES: usize = 4096;
pub const MAX_CAPTURE_BYTES: usize = 64 * 1024 * 1024;
pub const MAX_REPETITIONS: u32 = 32;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Action {
    Inventory,
    Sample { repetition: u32 },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Inventory {
    /// Complete sorted names from this exact artifact's native --list output.
    cases: Vec<String>,
}

impl Inventory {
    pub fn cases(&self) -> &[String] {
        &self.cases
    }

    pub fn parse(bytes: &[u8]) -> Result<Self, String> {
        let text = bounded_utf8(bytes)?;
        let mut cases = BTreeSet::new();
        let mut counts = None;
        for line in text.lines().filter(|line| !line.is_empty()) {
            if counts.is_some() {
                return Err("native inventory has data after its complete denominator".into());
            }
            if let Some(name) = line.strip_suffix(": test") {
                if name.is_empty()
                    || name.len() > MAX_NAME_BYTES
                    || name.chars().any(char::is_control)
                    || !cases.insert(name.to_owned())
                    || cases.len() > MAX_TEST_CASES
                {
                    return Err("native inventory has empty, duplicate or excessive names".into());
                }
            } else if line.ends_with(": benchmark") {
                return Err("consumer workload refuses a benchmark denominator".into());
            } else {
                let (tests, benchmarks) = line
                    .split_once(", ")
                    .ok_or("native inventory has an unsupported discovery line")?;
                counts =
                    Some((plural_count(tests, "test")?, plural_count(benchmarks, "benchmark")?));
            }
        }
        if cases.is_empty() || counts != Some((cases.len() as u64, 0)) {
            return Err("native inventory lacks a complete nonempty test-only denominator".into());
        }
        Ok(Self { cases: cases.into_iter().collect() })
    }

    pub fn validate_sample(&self, stdout: &[u8], stderr: &[u8]) -> Result<Summary, String> {
        let stdout = bounded_utf8(stdout)?;
        let stderr = bounded_utf8(stderr)?;
        let mut summary = None;
        for line in stdout.lines() {
            if line.trim_start().starts_with("SKIPPED:") || line.starts_with("test result: FAILED.")
            {
                return Err("native sample reports failed or skipped work".into());
            }
            if line.starts_with("test result:") {
                if summary.is_some() {
                    return Err("native sample has duplicate result summaries".into());
                }
                summary = Some(Summary::parse(line)?);
            }
        }
        if stderr.lines().any(|line| {
            line.trim_start().starts_with("SKIPPED:") || line.starts_with("test result:")
        }) {
            return Err("native stderr cannot supply or replace the harness result".into());
        }
        let summary = summary.ok_or("native sample has no complete harness result")?;
        if summary.passed != self.cases.len() as u64
            || summary.failed != 0
            || summary.ignored != 0
            || summary.measured != 0
            || summary.filtered_out != 0
        {
            return Err("native sample differs from its complete inventory denominator".into());
        }
        Ok(summary)
    }
}

/// Plain libtest result counts. Elapsed text is format-checked only; actual
/// measurement must come from the owning admitted process, never this line.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct Summary {
    pub passed: u64,
    pub failed: u64,
    pub ignored: u64,
    pub measured: u64,
    pub filtered_out: u64,
}

impl Summary {
    fn parse(line: &str) -> Result<Self, String> {
        let mut text = line.strip_prefix("test result: ok. ").ok_or("unsupported native result")?;
        let passed = count(&mut text, " passed; ")?;
        let failed = count(&mut text, " failed; ")?;
        let ignored = count(&mut text, " ignored; ")?;
        let measured = count(&mut text, " measured; ")?;
        let (filtered, elapsed) =
            text.split_once("; finished in ").map_or((text, None), |(a, b)| (a, Some(b)));
        let filtered_out =
            integer(filtered.strip_suffix(" filtered out").ok_or("incomplete native result")?)?;
        if let Some(elapsed) = elapsed {
            let seconds = elapsed.strip_suffix('s').ok_or("invalid native result elapsed text")?;
            let decimal =
                |part: &str| !part.is_empty() && part.bytes().all(|byte| byte.is_ascii_digit());
            let valid = match seconds.split_once('.') {
                Some((whole, fraction)) => decimal(whole) && decimal(fraction),
                None => decimal(seconds),
            };
            if !valid {
                return Err("invalid native result elapsed text".into());
            }
        }
        Ok(Self { passed, failed, ignored, measured, filtered_out })
    }
}

fn bounded_utf8(bytes: &[u8]) -> Result<&str, String> {
    if bytes.len() > MAX_CAPTURE_BYTES
        || bytes.contains(&0)
        || (!bytes.is_empty() && bytes.last() != Some(&b'\n'))
    {
        return Err("native harness capture is oversized, truncated or contains NUL".into());
    }
    std::str::from_utf8(bytes).map_err(|_| "native harness capture is not UTF8".into())
}

fn integer(value: &str) -> Result<u64, String> {
    if value.is_empty()
        || value.len() > 20
        || (value.len() > 1 && value.starts_with('0'))
        || !value.bytes().all(|b| b.is_ascii_digit())
    {
        return Err("invalid native integer count".into());
    }
    value.parse().map_err(|_| "native count overflows its bound".into())
}

fn plural_count(value: &str, noun: &str) -> Result<u64, String> {
    let (number, suffix) = value.split_once(' ').ok_or("invalid discovery count")?;
    let number = integer(number)?;
    if suffix != if number == 1 { noun.to_owned() } else { format!("{noun}s") } {
        return Err("invalid native discovery count noun".into());
    }
    Ok(number)
}

fn count(text: &mut &str, suffix: &str) -> Result<u64, String> {
    let (number, rest) = text.split_once(suffix).ok_or("incomplete native result count")?;
    let number = integer(number)?;
    *text = rest;
    Ok(number)
}

#[cfg(test)]
mod tests;
