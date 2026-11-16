//! Typed core for a disposable untrusted macro worker.
//!
//! This crate supplies framing, budgets, phases and opaque-handle ownership. It
//! neither launches nor confines a process and never accepts proof verdicts.
//! Blocking I/O needs a deadline-aware driver; checks between reads cannot
//! interrupt an arbitrary blocking `Read`. Compiler adapters must additionally
//! validate token/literal semantics before creating compiler objects.
#![forbid(unsafe_code)]

mod budget;
mod codec;
mod handles;
mod protocol;
mod session;
mod transport;

pub use budget::{Budget, Charge, Limits, Usage};
pub use codec::{FrameDecoder, decode, encode, frame_payload_length};
pub use handles::{Handle, HandleKind, HandleTable, HandleUse, UseMode};
pub use protocol::{
    Binding, Bound, Call, Diagnostic, Envelope, Literal, Message, Method, PROTOCOL_VERSION, Tree,
    Type, Value,
};
pub use session::{Admission, Phase, Session, SessionOwner};
pub use transport::Transport;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    InvalidLimits,
    Deadline,
    Budget(&'static str),
    Overflow,
    Allocation,
    InvalidWire(&'static str),
    Identity,
    Phase,
    Sequence,
    Schema,
    Handle(&'static str),
    Poisoned,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "isolation protocol refusal: {self:?}")
    }
}

impl std::error::Error for Error {}
