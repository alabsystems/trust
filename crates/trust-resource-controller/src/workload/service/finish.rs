//! Complete member census data stays separate from graph completion and actual
//! root/kernel/cohort retirement. No single final frame substitutes for them.
use super::*;
use crate::workload::host::census;

/// Root diagnostics after compiler retirement are distinct from every native
/// harness's raw stdout/stderr and physical EOF. They cannot alter its libtest
/// denominator, reported process status or owning-wait measurement.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    pub binding: Binding,
    pub stream: Stream,
    pub offset: u64,
    pub bytes: Vec<u8>,
}
impl Diagnostic {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        if self.bytes.is_empty()
            || self.bytes.len() > MAX_CHUNK_BYTES
            || self.offset.checked_add(self.bytes.len() as u64).is_none_or(|n| n > MAX_STREAM_BYTES)
        {
            return Err(invalid());
        }
        let mut e = Encoder::new(46);
        e.number(3);
        self.binding.write(&mut e)?;
        e.number(match self.stream {
            Stream::Stdout => 0,
            Stream::Stderr => 1,
        });
        e.number(self.offset);
        e.frame_bytes(&self.bytes)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8], expected: &Binding) -> io::Result<Self> {
        let mut d = header(bytes, 46)?;
        if d.number()? != 3 {
            return Err(invalid());
        }
        let value = Self {
            binding: Binding::read(&mut d)?,
            stream: match d.number()? {
                0 => Stream::Stdout,
                1 => Stream::Stderr,
                _ => return Err(invalid()),
            },
            offset: d.number()?,
            bytes: d.frame_bytes()?,
        };
        d.done()?;
        value.binding.check(expected)?;
        value.encode()?;
        Ok(value)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Graph {
    pub binding: Binding,
    pub succeeded: bool,
    pub snapshot: [u8; 16],
    pub members: u32,
}
impl Graph {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        if self.snapshot == [0; 16] || self.members > census::MAX_ENTRIES {
            return Err(invalid());
        }
        let mut e = Encoder::new(46);
        e.number(1);
        self.binding.write(&mut e)?;
        e.number(u64::from(self.succeeded));
        e.0.extend(self.snapshot);
        e.number(self.members.into());
        e.finish()
    }
    pub fn decode(bytes: &[u8], expected: &Binding) -> io::Result<Self> {
        let mut d = header(bytes, 46)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let binding = Binding::read(&mut d)?;
        let succeeded = match d.number()? {
            0 => false,
            1 => true,
            _ => return Err(invalid()),
        };
        let value = Self { binding, succeeded, snapshot: d.array()?, members: d.narrow()? };
        d.done()?;
        value.binding.check(expected)?;
        value.encode()?;
        Ok(value)
    }
}
pub fn encode_page(page: &census::Page) -> io::Result<Vec<u8>> {
    let binding = Binding {
        root_attempt: page.request.root_attempt,
        invocation_sha256: page.request.invocation_sha256,
    };
    let mut e = Encoder::new(46);
    e.number(2);
    binding.write(&mut e)?;
    e.0.extend(page.request.snapshot);
    e.number(page.request.offset.into());
    e.frame_bytes(&census::Reply::Page(page.clone()).encode()?)?;
    e.finish()
}
pub fn decode_page(bytes: &[u8], binding: &Binding) -> io::Result<census::Page> {
    let mut d = header(bytes, 46)?;
    if d.number()? != 2 {
        return Err(invalid());
    }
    Binding::read(&mut d)?.check(binding)?;
    let request = census::Request {
        root_attempt: binding.root_attempt,
        invocation_sha256: binding.invocation_sha256,
        snapshot: d.array()?,
        offset: d.narrow()?,
    };
    let frame = d.frame_bytes()?;
    d.done()?;
    match census::Reply::decode(&frame, &request)? {
        census::Reply::Page(page) => Ok(page),
        _ => Err(invalid()),
    }
}

/// Immutable, contiguous, nonshrinking census. All roles/missing measurements
/// stay in the denominator. A final graph frame alone cannot complete it.
pub struct Census {
    binding: Binding,
    snapshot: Option<[u8; 16]>,
    total: Option<u32>,
    entries: Vec<census::Entry>,
    attempts: std::collections::BTreeSet<[u8; 16]>,
    failed: bool,
}
impl Census {
    pub fn new(binding: Binding) -> Self {
        Self {
            binding,
            snapshot: None,
            total: None,
            entries: Vec::new(),
            attempts: Default::default(),
            failed: false,
        }
    }
    pub fn append(&mut self, page: census::Page) -> io::Result<()> {
        let result = (|| {
            if self.failed
                || page.request.root_attempt != self.binding.root_attempt
                || page.request.invocation_sha256 != self.binding.invocation_sha256
                || page.request.offset as usize != self.entries.len()
                || self.snapshot.is_some_and(|value| value != page.request.snapshot)
                || self.total.is_some_and(|value| value != page.total)
            {
                return Err(invalid());
            }
            census::Reply::Page(page.clone()).encode()?;
            if self.total.is_some_and(|total| self.entries.len() == total as usize) {
                return Err(invalid());
            }
            for entry in &page.entries {
                if !self.attempts.insert(entry.member_attempt) {
                    return Err(invalid());
                }
            }
            self.entries.try_reserve(page.entries.len()).map_err(io::Error::other)?;
            self.snapshot = Some(page.request.snapshot);
            self.total = Some(page.total);
            self.entries.extend(page.entries);
            Ok(())
        })();
        if result.is_err() {
            self.failed = true;
        }
        result
    }
    pub fn check_finished(&self, graph: &Graph) -> io::Result<()> {
        graph.binding.check(&self.binding)?;
        graph.encode()?;
        if self.failed
            || self.snapshot != Some(graph.snapshot)
            || self.total != Some(graph.members)
            || self.entries.len() != graph.members as usize
        {
            return Err(invalid());
        }
        Ok(())
    }
    pub fn entries(&self) -> &[census::Entry] {
        &self.entries
    }
}
