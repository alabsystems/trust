//! Explicit baseline/candidate source population for a development Land node.
//! Indices select original source owners; they grant no qualification or write.
use super::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourcePair {
    pub baseline: u32,
    pub candidate: u32,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LandSelection {
    pub sources: Vec<SourcePair>,
}
impl LandSelection {
    fn syntax(&self) -> io::Result<()> {
        if self.sources.is_empty() || self.sources.len() > MAX_SOURCES / 2 {
            return Err(invalid());
        }
        let mut original_indices = BTreeSet::new();
        for pair in &self.sources {
            if !original_indices.insert(pair.baseline) || !original_indices.insert(pair.candidate) {
                return Err(invalid());
            }
        }
        Ok(())
    }
    pub fn validate(&self, plan: &Plan, source: u32, comparison: NodeId) -> io::Result<()> {
        self.syntax()?;
        if self.sources.iter().any(|pair| {
            pair.baseline as usize >= plan.sources.len()
                || pair.candidate as usize >= plan.sources.len()
        }) {
            return Err(invalid());
        }
        let Kind::Compare {
            baseline,
            candidate,
            ..
        } = &plan
            .nodes
            .get(comparison.0 as usize)
            .ok_or_else(invalid)?
            .kind
        else {
            return Err(invalid());
        };
        let build_source = |artifact: &Artifact| -> io::Result<u32> {
            let Kind::Compile { source, unit, .. } = &plan
                .nodes
                .get(artifact.producer.0 as usize)
                .ok_or_else(invalid)?
                .kind
            else {
                return Err(invalid());
            };
            if unit != &artifact.unit {
                return Err(invalid());
            }
            Ok(*source)
        };
        let expected = SourcePair {
            baseline: build_source(baseline)?,
            candidate: build_source(candidate)?,
        };
        if expected.candidate != source || !self.sources.contains(&expected) {
            return Err(invalid());
        }
        Ok(())
    }
    pub(in crate::native_job) fn write(&self, e: &mut Encoder) -> io::Result<()> {
        self.syntax()?;
        e.number(1);
        e.number(self.sources.len() as u64);
        for pair in &self.sources {
            e.number(u64::from(pair.baseline));
            e.number(u64::from(pair.candidate));
        }
        Ok(())
    }
    pub(in crate::native_job) fn read(d: &mut Decoder<'_>) -> io::Result<Self> {
        if d.number()? != 1 {
            return Err(invalid());
        }
        let count = d.count(MAX_SOURCES / 2)?;
        let mut sources = Vec::with_capacity(count);
        for _ in 0..count {
            sources.push(SourcePair {
                baseline: d.narrow()?,
                candidate: d.narrow()?,
            });
        }
        let result = Self { sources };
        result.syntax()?;
        Ok(result)
    }
}
