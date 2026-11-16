//! Timings from actual in-process work, never loaded report authority. The
//! selected denominator includes failed and abandoned attempts.
use std::collections::{BTreeMap, BTreeSet};
use std::time::Instant;

use crate::{Result, refusal};

pub struct Measurements {
    selected: BTreeSet<String>,
    observed: BTreeMap<String, Option<u64>>,
}
pub struct RunningWork<'a> {
    measurements: &'a mut Measurements,
    name: String,
    started: Instant,
}
/// Longest observed caller interval, including delivery/overhead. This is
/// diagnostic selection, not CPU cause, graph/proof success, or execution grant.
pub struct MeasuredBottleneck {
    name: String,
    elapsed_ns: u64,
    population: BTreeMap<String, u64>,
}
impl Measurements {
    pub fn new(selected: &[String]) -> Result<Self> {
        let names = selected.iter().cloned().collect::<BTreeSet<_>>();
        if names.is_empty() || names.len() != selected.len() || names.iter().any(String::is_empty) {
            return Err(refusal("measured work requires a nonempty unique selected population"));
        }
        Ok(Self { selected: names, observed: BTreeMap::new() })
    }
    pub fn start(&mut self, name: &str) -> Result<RunningWork<'_>> {
        if !self.selected.contains(name) || self.observed.contains_key(name) {
            return Err(refusal("measured work is unselected or already attempted"));
        }
        self.observed.insert(name.into(), None);
        Ok(RunningWork { measurements: self, name: name.into(), started: Instant::now() })
    }
    pub fn observations(&self) -> &BTreeMap<String, Option<u64>> {
        &self.observed
    }
    pub fn select(self) -> Result<MeasuredBottleneck> {
        if self.observed.len() != self.selected.len() || self.observed.values().any(Option::is_none)
        {
            return Err(refusal("incomplete measured work cannot select a bottleneck"));
        }
        let population = self
            .observed
            .into_iter()
            .map(|(name, ns)| (name, ns.unwrap()))
            .collect::<BTreeMap<_, _>>();
        let (name, elapsed_ns) = population.iter().max_by_key(|(_, ns)| *ns).unwrap();
        if *elapsed_ns == 0 {
            return Err(refusal("zero-duration population cannot select a measured bottleneck"));
        }
        Ok(MeasuredBottleneck { name: name.clone(), elapsed_ns: *elapsed_ns, population })
    }
}
impl RunningWork<'_> {
    /// Call only after the actual synchronous work has returned its result.
    /// Failure leaves this item explicitly unmeasured; dropping also does so.
    pub fn finish(self, succeeded: bool) {
        let ns = succeeded.then(|| u64::try_from(self.started.elapsed().as_nanos()).ok()).flatten();
        self.measurements.observed.insert(self.name, ns);
    }
}
impl MeasuredBottleneck {
    pub fn name(&self) -> &str {
        &self.name
    }
    pub fn elapsed_ns(&self) -> u64 {
        self.elapsed_ns
    }
    pub fn population(&self) -> &BTreeMap<String, u64> {
        &self.population
    }
}

#[cfg(test)]
mod tests {
    use super::Measurements;
    #[test]
    fn missing_failed_and_abandoned_work_cannot_shrink_the_denominator() {
        for disposition in 0..3 {
            let mut measurements = Measurements::new(&["first".into(), "second".into()]).unwrap();
            measurements.start("first").unwrap().finish(true);
            if disposition == 1 {
                measurements.start("second").unwrap().finish(false);
            }
            if disposition == 2 {
                drop(measurements.start("second").unwrap());
            }
            assert!(measurements.select().is_err());
        }
    }
    #[test]
    fn real_in_process_work_has_one_complete_population_and_no_replay_slot() {
        let mut measurements = Measurements::new(&["read".into()]).unwrap();
        let temporary = tempfile::NamedTempFile::new().unwrap();
        std::fs::write(temporary.path(), b"actual observed input").unwrap();
        let attempt = measurements.start("read").unwrap();
        let bytes = std::fs::read(temporary.path()).unwrap();
        assert!(!bytes.is_empty());
        attempt.finish(true);
        assert!(measurements.start("read").is_err());
        assert!(measurements.start("other").is_err());
        let selected = measurements.select().unwrap();
        assert_eq!(selected.name(), "read");
        assert!(selected.elapsed_ns() > 0);
        assert_eq!(selected.population().len(), 1);
    }
}
