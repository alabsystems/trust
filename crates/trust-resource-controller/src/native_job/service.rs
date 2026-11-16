//! Native-job service observations only. Frames cannot construct a Root,
//! retired compiler, current proof completion or repository write owner.
use super::{MAX_NODES, NodeId, Plan};
use crate::wire::{Decoder, Encoder, header, invalid};
use std::io;
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Binding {
    pub root_attempt: [u8; 16],
    pub invocation_sha256: [u8; 32],
}
impl Binding {
    fn write(&self, e: &mut Encoder) -> io::Result<()> {
        if self.root_attempt == [0; 16] || self.invocation_sha256 == [0; 32] {
            return Err(invalid());
        }
        e.0.extend(self.root_attempt);
        e.0.extend(self.invocation_sha256);
        Ok(())
    }
    fn read(d: &mut Decoder<'_>) -> io::Result<Self> {
        Ok(Self {
            root_attempt: d.array()?,
            invocation_sha256: d.array()?,
        })
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Outcome {
    Succeeded,
    Failed { reason: String },
    Blocked { reason: String },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Node {
    pub binding: Binding,
    pub id: NodeId,
    pub outcome: Outcome,
    pub parent_elapsed_ns: u64,
    /// Observed producing-compiler calls. Absence is unknown, never zero.
    pub compiler_executions: Option<u64>,
    /// Actual retained warm compilation units, distinct from proof reuse.
    pub reused_units: Option<u64>,
}
impl Node {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        if self.id.0 as usize >= MAX_NODES {
            return Err(invalid());
        }
        let mut e = Encoder::new(109);
        e.number(2);
        self.binding.write(&mut e)?;
        e.number(self.id.0.into());
        match &self.outcome {
            Outcome::Succeeded => e.number(0),
            Outcome::Failed { reason } | Outcome::Blocked { reason } => {
                if reason.is_empty() || reason.len() > 4096 || reason.contains('\0') {
                    return Err(invalid());
                }
                e.number(if matches!(&self.outcome, Outcome::Failed { .. }) {
                    1
                } else {
                    2
                });
                e.bytes(reason.as_bytes())?;
            }
        }
        e.number(self.parent_elapsed_ns);
        write_optional(&mut e, self.compiler_executions);
        write_optional(&mut e, self.reused_units);
        e.finish()
    }
    pub fn decode(bytes: &[u8], binding: Binding) -> io::Result<Self> {
        let mut d = header(bytes, 109)?;
        if d.number()? != 2 {
            return Err(invalid());
        }
        let actual = Binding::read(&mut d)?;
        if actual != binding {
            return Err(invalid());
        }
        let id = NodeId(d.narrow()?);
        let outcome = match d.number()? {
            0 => Outcome::Succeeded,
            tag @ (1 | 2) => {
                let reason = String::from_utf8(d.bytes()?).map_err(|_| invalid())?;
                if tag == 1 {
                    Outcome::Failed { reason }
                } else {
                    Outcome::Blocked { reason }
                }
            }
            _ => return Err(invalid()),
        };
        let value = Self {
            binding,
            id,
            outcome,
            parent_elapsed_ns: d.number()?,
            compiler_executions: read_optional(&mut d)?,
            reused_units: read_optional(&mut d)?,
        };
        d.done()?;
        value.encode()?;
        Ok(value)
    }
}
fn write_optional(e: &mut Encoder, value: Option<u64>) {
    match value {
        None => e.number(0),
        Some(value) => {
            e.number(1);
            e.number(value)
        }
    }
}
fn read_optional(d: &mut Decoder<'_>) -> io::Result<Option<u64>> {
    match d.number()? {
        0 => Ok(None),
        1 => Ok(Some(d.number()?)),
        _ => Err(invalid()),
    }
}
pub fn ready(binding: Binding, reply: &super::host::ReadyReply) -> io::Result<Vec<u8>> {
    if binding.root_attempt != reply.context.context.root_attempt
        || binding.invocation_sha256 != reply.invocation_sha256
    {
        return Err(invalid());
    }
    let mut e = Encoder::new(108);
    e.number(1);
    binding.write(&mut e)?;
    e.bytes(&reply.encode()?)?;
    e.finish()
}
/// Full original denominator, in plan order. Omitted/duplicate/extra nodes
/// refuse before encoding; failed/unsupported nodes remain explicit failures.
pub fn graph(binding: Binding, plan: &Plan, nodes: &[Node]) -> io::Result<Vec<u8>> {
    plan.validate()?;
    if nodes.len() != plan.nodes.len() {
        return Err(invalid());
    }
    let mut e = Encoder::new(110);
    e.number(1);
    binding.write(&mut e)?;
    e.number(nodes.len() as u64);
    for (index, node) in nodes.iter().enumerate() {
        if node.binding != binding || node.id.0 as usize != index {
            return Err(invalid());
        }
        e.bytes(&node.encode()?)?;
    }
    e.finish()
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Stop {
    pub binding: Binding,
}
impl Stop {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(111);
        e.number(1);
        self.binding.write(&mut e)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8], binding: Binding) -> io::Result<Self> {
        let mut d = header(bytes, 111)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let value = Self {
            binding: Binding::read(&mut d)?,
        };
        d.done()?;
        if value.binding != binding {
            return Err(invalid());
        }
        value.encode()?;
        Ok(value)
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn unknown_native_work_is_never_reported_as_observed_zero() {
        let binding = Binding {
            root_attempt: [1; 16],
            invocation_sha256: [2; 32],
        };
        let unknown = Node {
            binding,
            id: NodeId(0),
            outcome: Outcome::Failed {
                reason: "native outcome unknown".into(),
            },
            parent_elapsed_ns: 3,
            compiler_executions: None,
            reused_units: None,
        };
        let zero = Node {
            compiler_executions: Some(0),
            reused_units: Some(0),
            ..unknown.clone()
        };
        assert_ne!(unknown.encode().unwrap(), zero.encode().unwrap());
        assert_eq!(
            Node::decode(&unknown.encode().unwrap(), binding).unwrap(),
            unknown
        );
        assert_eq!(
            Node::decode(&zero.encode().unwrap(), binding).unwrap(),
            zero
        );
        for (version, tag) in [(1, 0), (2, 2)] {
            let mut malformed = Encoder::new(109);
            malformed.number(version);
            binding.write(&mut malformed).unwrap();
            malformed.number(0);
            malformed.number(0);
            malformed.number(3);
            malformed.number(tag);
            malformed.number(0);
            assert!(Node::decode(&malformed.finish().unwrap(), binding).is_err());
        }
    }
    #[test]
    fn native_service_frames_refuse_every_prefix_and_different_original_binding() {
        let binding = Binding {
            root_attempt: [1; 16],
            invocation_sha256: [2; 32],
        };
        let node = Node {
            binding,
            id: NodeId(0),
            outcome: Outcome::Failed {
                reason: "actual unsupported prerequisite".into(),
            },
            parent_elapsed_ns: 3,
            compiler_executions: Some(4),
            reused_units: Some(5),
        };
        let bytes = node.encode().unwrap();
        assert_eq!(Node::decode(&bytes, binding).unwrap(), node);
        for end in 0..bytes.len() {
            assert!(Node::decode(&bytes[..end], binding).is_err());
        }
        let other = Binding {
            root_attempt: [3; 16],
            ..binding
        };
        assert!(Node::decode(&bytes, other).is_err());
        let mut trailing = bytes;
        trailing.push(0);
        assert!(Node::decode(&trailing, binding).is_err());
        let stop = Stop { binding }.encode().unwrap();
        assert!(Stop::decode(&stop, other).is_err());
    }
}
