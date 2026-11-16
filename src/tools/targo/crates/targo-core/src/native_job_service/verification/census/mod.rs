//! Complete observed compiler inventory. All fields remain untrusted DATA.
//! Only the enclosing actual native/session owner may present these current
//! claims to the maintained kernel; this parser grants no source/proof credit.
use crate::util::CargoResult;
use anyhow::{Context as _, ensure};
use std::collections::BTreeSet;
use trust_types::{
    CoverageTransportSummary, CrateTransportSummary, FunctionTransportResult, Outcome,
    TransportMessage, TransportObligationResult,
};

pub(super) struct Scope<'a> {
    pub package: &'a str,
    pub krate: &'a str,
    pub primary: bool,
    pub session: &'a str,
}
impl Scope<'_> {
    fn require(
        &self,
        package: Option<&str>,
        krate: Option<&str>,
        primary: bool,
        session: &str,
    ) -> CargoResult<()> {
        ensure!(
            package == Some(self.package)
                && krate == Some(self.krate)
                && primary == self.primary
                && session == self.session,
            "native verifier changed its original package/crate/primary/fresh-session scope"
        );
        Ok(())
    }
}
pub(super) struct Census {
    pub functions: Vec<FunctionTransportResult>,
    pub coverage: CoverageTransportSummary,
    pub terminal: CrateTransportSummary,
}
#[derive(Default)]
struct Counts {
    proved: usize,
    failed: usize,
    unknown: usize,
    timed_out: usize,
    skipped: usize,
    runtime_checked: usize,
    total: usize,
}
impl Counts {
    fn add(&mut self, row: &TransportObligationResult) {
        self.total += 1;
        // Use the maintained instance-discharge predicate: the compiler counts
        // this shape skipped even when its raw outcome says Proved. Never
        // count one callee assumption as another caller proof.
        if row.outcome.is_skipped()
            || row.outcome.is_proved()
                && trust_types::assumption::is_instance_hypothesis_discharge_row(
                    &row.kind,
                    &row.solver,
                )
        {
            self.unknown += 1;
            self.skipped += 1;
            return;
        }
        match row.outcome {
            Outcome::Proved => self.proved += 1,
            Outcome::Failed => self.failed += 1,
            Outcome::RuntimeChecked => self.runtime_checked += 1,
            Outcome::Timeout => {
                self.unknown += 1;
                self.timed_out += 1;
            }
            _ => self.unknown += 1,
        }
    }
    fn tuple(&self) -> (usize, usize, usize, usize, usize, usize, usize) {
        (
            self.proved,
            self.failed,
            self.unknown,
            self.timed_out,
            self.skipped,
            self.runtime_checked,
            self.total,
        )
    }
}

pub(super) fn parse(stderr: &[u8], expected: &Scope<'_>) -> CargoResult<Census> {
    const MAX_STREAM: usize = 64 * 1024 * 1024;
    ensure!(
        stderr.len() <= MAX_STREAM && !expected.session.is_empty(),
        "native verifier exceeds finite original stream/session scope"
    );
    let text = std::str::from_utf8(stderr).context("native verifier stderr is not UTF8")?;
    let mut functions = Vec::new();
    let mut coverage = None;
    let mut terminal = None;
    for line in text.lines() {
        let Some(payload) = line.strip_prefix(trust_types::TRANSPORT_PREFIX) else {
            continue;
        };
        // Reject duplicate keys before the original typed decoder. Its direct
        // i128/u128 deserialization must not pass through serde_json::Value.
        serde_json::from_str::<unique::Document>(payload)
            .context("native verifier emitted duplicate/malformed JSON")?;
        match trust_types::parse_transport_payload(payload)? {
            TransportMessage::FunctionResult(function) => {
                ensure!(
                    coverage.is_none() && terminal.is_none(),
                    "native verifier function followed coverage/terminal"
                );
                expected.require(
                    function.package_name.as_deref(),
                    function.crate_name.as_deref(),
                    function.primary_package,
                    &function.verification_session,
                )?;
                ensure!(
                    function.transport_budget.is_none(),
                    "native verifier withheld part of its original function denominator"
                );
                let mut counts = Counts::default();
                for row in &function.results {
                    counts.add(row);
                }
                ensure!(
                    counts.tuple()
                        == (
                            function.proved,
                            function.failed,
                            function.unknown,
                            function.timed_out,
                            function.skipped,
                            function.runtime_checked,
                            function.total
                        ),
                    "native verifier function counters differ from its original complete rows"
                );
                functions.push(function);
            }
            TransportMessage::CoverageSummary(row) => {
                ensure!(
                    coverage.is_none() && terminal.is_none(),
                    "native verifier repeated or reordered coverage"
                );
                expected.require(
                    Some(&row.package_name),
                    Some(&row.crate_name),
                    row.primary_package,
                    &row.verification_session,
                )?;
                ensure!(
                    row.is_complete() && row.eligible > 0,
                    "native verifier function denominator is absent/incomplete"
                );
                coverage = Some(row);
            }
            TransportMessage::CrateSummary(row) => {
                ensure!(
                    coverage.is_some() && terminal.is_none(),
                    "native verifier terminal precedes coverage or repeats"
                );
                expected.require(
                    row.package_name.as_deref(),
                    Some(&row.crate_name),
                    row.primary_package,
                    &row.verification_session,
                )?;
                terminal = Some(row);
            }
            _ => anyhow::bail!("native verifier emitted an unsupported inventory variant"),
        }
    }
    let coverage = coverage.context("native verifier omitted complete current coverage")?;
    let terminal = terminal.context("native verifier omitted actual terminal inventory")?;
    let identity = coverage
        .function_identities
        .as_ref()
        .context("native verifier omitted exact current function identities")?;
    let canonical = |names: &[String]| {
        names.iter().all(|name| !name.is_empty()) && names.windows(2).all(|pair| pair[0] < pair[1])
    };
    ensure!(
        identity.schema == trust_types::COVERAGE_FUNCTION_IDENTITY_SCHEMA_V1
            && identity.eligible_functions.len() == coverage.eligible
            && identity.processed_functions.len() == coverage.processed
            && canonical(&identity.eligible_functions)
            && canonical(&identity.processed_functions),
        "native verifier function identity inventory is malformed"
    );
    let actual = functions
        .iter()
        .map(|function| function.function.clone())
        .collect::<BTreeSet<_>>();
    ensure!(
        actual.len() == functions.len()
            && actual.iter().eq(identity.eligible_functions.iter())
            && actual.iter().eq(identity.processed_functions.iter()),
        "native verifier exact function population differs from whole-unit coverage"
    );
    let mut counts = Counts::default();
    let mut verified = 0;
    for function in &functions {
        if function.total > 0 && function.proved == function.total {
            verified += 1;
        }
        for row in &function.results {
            counts.add(row);
        }
    }
    ensure!(
        terminal.functions_analyzed == functions.len()
            && terminal.functions_verified == verified
            && counts.tuple()
                == (
                    terminal.total_proved,
                    terminal.total_failed,
                    terminal.total_unknown,
                    terminal.total_timed_out,
                    terminal.total_skipped,
                    terminal.total_runtime_checked,
                    terminal.total_obligations
                )
            && terminal.total_obligations > 0,
        "native verifier terminal differs from its complete nonzero current row population"
    );
    Ok(Census {
        functions,
        coverage,
        terminal,
    })
}

// The same duplicate-key rejection as the maintained compiler transport. This
// only checks JSON shape; actual typed decoding above consumes original bytes.
mod unique {
    use serde::de::{self, MapAccess, SeqAccess, Visitor};
    use serde::{Deserialize, Deserializer};
    use std::{collections::BTreeSet, fmt};
    pub(super) struct Document;
    impl<'de> Deserialize<'de> for Document {
        fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
            d.deserialize_any(Unique)
        }
    }
    struct Unique;
    impl<'de> Visitor<'de> for Unique {
        type Value = Document;
        fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("duplicate-free native compiler JSON")
        }
        fn visit_unit<E: de::Error>(self) -> Result<Document, E> {
            Ok(Document)
        }
        fn visit_bool<E: de::Error>(self, _: bool) -> Result<Document, E> {
            Ok(Document)
        }
        fn visit_i64<E: de::Error>(self, _: i64) -> Result<Document, E> {
            Ok(Document)
        }
        fn visit_u64<E: de::Error>(self, _: u64) -> Result<Document, E> {
            Ok(Document)
        }
        fn visit_f64<E: de::Error>(self, value: f64) -> Result<Document, E> {
            if value.is_finite() {
                Ok(Document)
            } else {
                Err(E::custom("nonfinite native number"))
            }
        }
        fn visit_str<E: de::Error>(self, _: &str) -> Result<Document, E> {
            Ok(Document)
        }
        fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<Document, A::Error> {
            while seq.next_element::<Document>()?.is_some() {}
            Ok(Document)
        }
        fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<Document, A::Error> {
            let mut seen = BTreeSet::new();
            while let Some(key) = map.next_key::<String>()? {
                if !seen.insert(key) {
                    return Err(de::Error::custom("duplicate native JSON key"));
                }
                map.next_value::<Document>()?;
            }
            Ok(Document)
        }
    }
}

#[cfg(test)]
pub(in crate::native_job_service::verification) mod tests;
