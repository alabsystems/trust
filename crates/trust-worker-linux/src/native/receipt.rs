//! Invocation-bound structural issuance/map records. No worker verdict, native
//! ABI, constructor-completion, atomic-snapshot or execution claim is encoded.
use trust_process_isolation::{Budget, Charge, Session};

use super::configuration::Configuration;
use super::grant::{LocalGrant, context};
use super::kernel::{FileIdentity, IssuedDescriptor};
use super::mappings::{ExecutableMapping, ObservedMapping};
use super::{OBJECTS, charge, check, contract, io, reserve};
use crate::Error;

pub(super) const HEADER: usize = 120;
pub(super) const ISSUED: usize = 64;
pub(super) const OBSERVED: usize = 48;

pub(super) fn send(
    grant: &LocalGrant,
    graph: [u8; 32],
    binding: &trust_process_isolation::Binding,
    sequence: u64,
    page: u64,
    issued: &[IssuedDescriptor],
    observed: &[ObservedMapping],
) -> Result<(), Error> {
    let b = &grant.budget;
    if issued.len() > 31
        || observed.len() > 1024
        || sequence == 0
        || !page.is_power_of_two()
        || page > 65536
    {
        return Err(contract(b, "native receipt bound"));
    }
    let mut header = [0; HEADER];
    header[..8].copy_from_slice(b"MAPRECv1");
    header[8..40].copy_from_slice(&grant.capsule);
    header[40..72].copy_from_slice(&context(binding));
    header[72..104].copy_from_slice(&graph);
    header[104..112].copy_from_slice(&sequence.to_le_bytes());
    header[112..116].copy_from_slice(&(page as u32).to_le_bytes());
    header[116..118].copy_from_slice(&(issued.len() as u16).to_le_bytes());
    header[118..120].copy_from_slice(&(observed.len() as u16).to_le_bytes());
    charge(
        b,
        Charge {
            wire_bytes: (HEADER + ISSUED * issued.len() + OBSERVED * observed.len()) as u64,
            ..Charge::default()
        },
    )?;
    io::write_all(&header, b)?;
    for record in issued {
        let mut bytes = [0; ISSUED];
        bytes[0] = record.object;
        bytes[4..8].copy_from_slice(&record.target.to_le_bytes());
        bytes[8..16].copy_from_slice(&record.file.device.to_le_bytes());
        bytes[16..24].copy_from_slice(&record.file.inode.to_le_bytes());
        bytes[24..56].copy_from_slice(&record.sha256);
        bytes[56..64].copy_from_slice(&record.size.to_le_bytes());
        io::write_all(&bytes, b)?;
    }
    for record in observed {
        let mut bytes = [0; OBSERVED];
        bytes[0] = record.object;
        for (at, value) in [
            record.mapping.start,
            record.mapping.end,
            record.mapping.offset,
            record.mapping.file.device,
            record.mapping.file.inode,
        ]
        .into_iter()
        .enumerate()
        {
            bytes[8 + at * 8..16 + at * 8].copy_from_slice(&value.to_le_bytes());
        }
        io::write_all(&bytes, b)?;
    }
    check(b)
}

#[derive(Debug)]
pub(super) struct Receipt {
    pub sequence: u64,
    pub page: u64,
    pub issued: Vec<IssuedDescriptor>,
    pub observed: Vec<ObservedMapping>,
}
impl Receipt {
    /// The parent's bounded driver supplies exact reads under its original
    /// shared budget/monitor, never through a broker or compiler callback.
    pub fn receive(
        session: &Session,
        configuration: &Configuration,
        capsule: [u8; 32],
        sequence: u64,
        read: impl FnMut(&mut [u8]) -> Result<(), Error>,
    ) -> Result<Self, Error> {
        let result = Self::receive_inner(session, configuration, capsule, sequence, read);
        if result.is_err() {
            session.budget().refuse(trust_process_isolation::Error::Phase);
        }
        result
    }
    fn receive_inner(
        session: &Session,
        configuration: &Configuration,
        capsule: [u8; 32],
        sequence: u64,
        mut read: impl FnMut(&mut [u8]) -> Result<(), Error>,
    ) -> Result<Self, Error> {
        configuration.check_owner(session)?;
        let b = session.budget();
        let mut header = [0; HEADER];
        charge(b, Charge { wire_bytes: HEADER as u64, work: HEADER as u64, ..Charge::default() })?;
        read(&mut header)?;
        if &header[..8] != b"MAPRECv1"
            || header[8..40] != capsule
            || header[40..72] != context(session.binding())
            || Some(header[72..104].try_into().unwrap()) != configuration.graph
            || u64::from_le_bytes(header[104..112].try_into().unwrap()) != sequence
            || sequence == 0
        {
            return Err(contract(b, "native broker receipt context/sequence"));
        }
        let page = u32::from_le_bytes(header[112..116].try_into().unwrap()) as u64;
        let count = u16::from_le_bytes(header[116..118].try_into().unwrap()) as usize;
        let mapped = u16::from_le_bytes(header[118..120].try_into().unwrap()) as usize;
        if !page.is_power_of_two() || !(4096..=65536).contains(&page) || count > 31 || mapped > 1024
        {
            return Err(contract(b, "native broker receipt envelope"));
        }
        charge(
            b,
            Charge {
                wire_bytes: (ISSUED * count + OBSERVED * mapped) as u64,
                work: (ISSUED * count + OBSERVED * mapped) as u64,
                ..Charge::default()
            },
        )?;
        let mut issued: Vec<IssuedDescriptor> = reserve(count, b)?;
        for at in 0..count {
            let mut bytes = [0; ISSUED];
            read(&mut bytes)?;
            let object = bytes[0] as usize;
            let target = u32::from_le_bytes(bytes[4..8].try_into().unwrap());
            let file = FileIdentity { device: n64(&bytes, 8), inode: n64(&bytes, 16) };
            let sha256 = bytes[24..56].try_into().unwrap();
            let size = n64(&bytes, 56);
            charge(b, Charge { work: 64 * (issued.len() + 1) as u64, ..Charge::default() })?;
            let expected = configuration
                .objects
                .get(object)
                .and_then(|value| *value)
                .ok_or_else(|| contract(b, "native receipt object index"))?;
            if bytes[1..4] != [0; 3]
                || target != 33 + at as u32
                || file.inode == 0
                || sha256 != expected.sha256
                || size != expected.size
                || issued.iter().any(|old| {
                    (old.object as usize == object && old.file != file)
                        || (old.object as usize != object && old.file == file)
                })
            {
                return Err(contract(b, "native issued receipt identity/bank"));
            }
            issued.push(IssuedDescriptor { object: object as u8, target, file, sha256, size });
        }
        let mut observed: Vec<ObservedMapping> = reserve(mapped, b)?;
        for _ in 0..mapped {
            let mut bytes = [0; OBSERVED];
            read(&mut bytes)?;
            let object = bytes[0];
            let mapping = ExecutableMapping {
                start: n64(&bytes, 8),
                end: n64(&bytes, 16),
                offset: n64(&bytes, 24),
                file: FileIdentity { device: n64(&bytes, 32), inode: n64(&bytes, 40) },
            };
            charge(
                b,
                Charge {
                    work: 64 * (issued.len() + observed.len() + 1) as u64,
                    ..Charge::default()
                },
            )?;
            let source = issued
                .iter()
                .find(|issued| issued.object == object && issued.file == mapping.file)
                .ok_or_else(|| contract(b, "native map lacks admitted issuance"))?;
            let size = source
                .size
                .checked_add(page - 1)
                .map(|size| size & !(page - 1))
                .ok_or_else(|| contract(b, "native map receipt overflow"))?;
            if bytes[1..8] != [0; 7]
                || mapping.start >= mapping.end
                || mapping.start % page != 0
                || mapping.end % page != 0
                || mapping.offset % page != 0
                || mapping
                    .offset
                    .checked_add(mapping.end - mapping.start)
                    .is_none_or(|end| end > size)
                || observed.iter().any(|old| old.mapping == mapping)
            {
                return Err(contract(b, "native observed map receipt bounds/replay"));
            }
            observed.push(ObservedMapping { object, mapping });
        }
        configuration.check_owner(session)?;
        Ok(Self { sequence, page, issued, observed })
    }
    pub fn validate_progress(
        &self,
        previous: Option<&Receipt>,
        configuration: &Configuration,
        session: &Session,
        seen: &mut [bool; OBJECTS],
    ) -> Result<(), Error> {
        configuration.check_owner(session)?;
        let b = session.budget();
        if let Some(previous) = previous {
            charge(
                b,
                Charge { work: 64 * (previous.issued.len() + 1) as u64, ..Charge::default() },
            )?;
            if self.sequence
                != previous
                    .sequence
                    .checked_add(1)
                    .ok_or_else(|| contract(b, "native receipt sequence overflow"))?
                || self.page != previous.page
                || !self.issued.starts_with(&previous.issued)
            {
                return Err(contract(b, "native receipt cumulative issuance/sequence"));
            }
        } else if self.sequence != 1 {
            return Err(contract(b, "native receipt initial sequence"));
        }
        charge(
            b,
            Charge { work: 64 * (self.observed.len() + OBJECTS) as u64, ..Charge::default() },
        )?;
        for record in &self.observed {
            let entry = seen
                .get_mut(record.object as usize)
                .ok_or_else(|| contract(b, "native map progress object"))?;
            *entry = true;
        }
        if configuration.required.iter().zip(seen).any(|(required, seen)| *required && !*seen) {
            return Err(contract(b, "native required root/dependency map unobserved"));
        }
        check(b)
    }
}
fn n64(bytes: &[u8], at: usize) -> u64 {
    u64::from_le_bytes(bytes[at..at + 8].try_into().unwrap())
}

#[cfg(test)]
mod tests {
    use super::*;
    fn wire(session: &Session, config: &Configuration, sequence: u64) -> Vec<u8> {
        let mut bytes = vec![0; HEADER + ISSUED + OBSERVED];
        bytes[..8].copy_from_slice(b"MAPRECv1");
        bytes[8..40].copy_from_slice(&[8; 32]);
        bytes[40..72].copy_from_slice(&context(session.binding()));
        bytes[72..104].copy_from_slice(&config.graph.unwrap());
        bytes[104..112].copy_from_slice(&sequence.to_le_bytes());
        bytes[112..116].copy_from_slice(&4096u32.to_le_bytes());
        bytes[116..118].copy_from_slice(&1u16.to_le_bytes());
        bytes[118..120].copy_from_slice(&1u16.to_le_bytes());
        let object = config.objects[0].unwrap();
        bytes[HEADER + 4..HEADER + 8].copy_from_slice(&33u32.to_le_bytes());
        bytes[HEADER + 8..HEADER + 16].copy_from_slice(&1u64.to_le_bytes());
        bytes[HEADER + 16..HEADER + 24].copy_from_slice(&42u64.to_le_bytes());
        bytes[HEADER + 24..HEADER + 56].copy_from_slice(&object.sha256);
        bytes[HEADER + 56..HEADER + 64].copy_from_slice(&object.size.to_le_bytes());
        for (at, value) in [0x10000u64, 0x11000, 0, 1, 42].into_iter().enumerate() {
            bytes[HEADER + ISSUED + 8 + at * 8..HEADER + ISSUED + 16 + at * 8]
                .copy_from_slice(&value.to_le_bytes());
        }
        bytes
    }
    fn decode(
        session: &Session,
        config: &Configuration,
        bytes: &[u8],
        sequence: u64,
        reads: &mut usize,
    ) -> Result<Receipt, Error> {
        let mut at = 0;
        Receipt::receive(session, config, [8; 32], sequence, |output| {
            *reads += 1;
            let value = bytes
                .get(at..at + output.len())
                .ok_or(Error::Contract("test receipt truncation"))?;
            output.copy_from_slice(value);
            at += output.len();
            Ok(())
        })
    }
    #[test]
    fn receipt_binding_bank_hash_map_and_truncation_failures_are_terminal() {
        // One accepted control prevents an always-refuse parser satisfying the
        // hostile cases. This is a synthetic codec test, not native execution.
        let (session, config) = super::super::tests::receipt_configuration();
        let good = wire(&session, &config, 1);
        let receipt = decode(&session, &config, &good, 1, &mut 0).unwrap();
        let mut seen = [false; OBJECTS];
        receipt.validate_progress(None, &config, &session, &mut seen).unwrap();
        assert!(seen[0]);
        for offset in [
            0,
            8,
            40,
            72,
            104,
            HEADER,
            HEADER + 1,
            HEADER + 4,
            HEADER + 24,
            HEADER + ISSUED + 1,
            HEADER + ISSUED + 40,
        ] {
            let (session, config) = super::super::tests::receipt_configuration();
            let mut bad = wire(&session, &config, 1);
            bad[offset] ^= 1;
            let mut reads = 0;
            assert!(
                decode(&session, &config, &bad, 1, &mut reads).is_err(),
                "tampered offset{offset} admitted"
            );
            assert!(session.budget().check().is_err());
            let before = reads;
            assert!(decode(&session, &config, &wire(&session, &config, 1), 1, &mut reads).is_err());
            assert_eq!(reads, before, "failed receipt parser resumed IO");
        }
        let (session, config) = super::super::tests::receipt_configuration();
        let bytes = wire(&session, &config, 1);
        assert!(decode(&session, &config, &bytes[..bytes.len() - 1], 1, &mut 0).is_err());
        assert!(session.budget().check().is_err());
    }
    #[test]
    fn oversized_receipts_refuse_at_header_before_body_io_or_allocation() {
        for (at, value) in [(116, 32u16), (118, 1025u16)] {
            let (session, config) = super::super::tests::receipt_configuration();
            let mut bytes = wire(&session, &config, 1);
            bytes[at..at + 2].copy_from_slice(&value.to_le_bytes());
            let before = session.budget().usage().unwrap().allocation_bytes;
            let mut reads = 0;
            assert!(decode(&session, &config, &bytes, 1, &mut reads).is_err());
            assert_eq!(reads, 1);
            assert_eq!(session.budget().usage().unwrap().allocation_bytes, before);
        }
    }
    #[test]
    fn receipt_cannot_replay_change_source_inode_or_use_reconstructed_session() {
        let (session, config) = super::super::tests::receipt_configuration();
        let first = decode(&session, &config, &wire(&session, &config, 1), 1, &mut 0).unwrap();
        let mut seen = [false; OBJECTS];
        first.validate_progress(None, &config, &session, &mut seen).unwrap();
        let mut changed = wire(&session, &config, 2);
        changed[HEADER + 16..HEADER + 24].copy_from_slice(&43u64.to_le_bytes());
        changed[HEADER + ISSUED + 40..HEADER + ISSUED + 48].copy_from_slice(&43u64.to_le_bytes());
        let second = decode(&session, &config, &changed, 2, &mut 0).unwrap();
        assert!(second.validate_progress(Some(&first), &config, &session, &mut seen).is_err());
        assert!(session.budget().check().is_err());
        let (session, config) = super::super::tests::receipt_configuration();
        let other = Session::new(session.binding().clone(), session.budget().clone()).unwrap();
        let mut reads = 0;
        assert!(decode(&other, &config, &wire(&session, &config, 1), 1, &mut reads).is_err());
        assert_eq!(reads, 0);
        assert!(session.budget().check().is_err());
        let (session, config) = super::super::tests::receipt_configuration();
        assert!(decode(&session, &config, &wire(&session, &config, 1), 2, &mut 0).is_err());
    }
}
