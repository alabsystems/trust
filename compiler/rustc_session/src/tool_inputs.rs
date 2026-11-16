//! Trust: invocation-owned, data-only native tool observations.
//!
//! A collection is reusable only after every started observation reaches its
//! owning wait and the complete bounded shared envelope can be encoded. Neither
//! these records nor their serialized form confer proof or execution authority.
//!
//! The selected local profile assumes fixed host/mount/MAC/security namespaces
//! and credentials/capabilities. It binds the current UID/groups and kernel
//! access decisions; unsupported Linux fsuid/fsgid overrides are excluded by the
//! shared profile unless independently held fixed. Loaded libraries and tools'
//! own subcommands are outside this linker-driver readset.

use std::ffi::OsStr;
use std::path::Path;

use trust_fs_observation::tool_lookup::{
    Context, MAX_RECORD_BYTES, MAX_RECORDS, Pending, Record, ToolInputs,
};
pub use trust_fs_observation::tool_lookup::{DEP_INFO_PREFIX, Profile, UNAVAILABLE};

use crate::Session;

/// Exact projection of the parsed compiler execution mode. This is observation
/// DATA, not runtime admission. Hosted v3 can never downgrade to a local fact.
#[allow(rustc::bad_opt_access)]
pub fn local_profile_for_options(opts: &crate::config::Options) -> Option<Profile> {
    if opts.resource_worker_v3 {
        None
    } else if opts.resource_worker_v2 {
        Some(Profile::LocalUnixNativeResourceV2)
    } else {
        Some(Profile::LocalUnixNativeV1)
    }
}

/// Final data for one completed unit. The codec, including empty envelopes, is
/// owned by the shared library rather than reconstructed by a compiler writer.
pub enum Terminal {
    Available(Vec<u8>),
    Unavailable,
}

pub(crate) struct Collection {
    state: State,
}

enum State {
    Disabled,
    Collecting { records: Vec<Record>, encoded_bytes: usize, in_flight: usize },
    Unavailable,
}

impl Collection {
    pub(crate) fn new(enabled: bool) -> Self {
        Self {
            state: if enabled {
                State::Collecting { records: Vec::new(), encoded_bytes: 0, in_flight: 0 }
            } else {
                State::Disabled
            },
        }
    }

    fn requested(&self) -> bool {
        !matches!(self.state, State::Disabled)
    }

    fn unavailable(&mut self) {
        if self.requested() {
            self.state = State::Unavailable;
        }
    }

    fn started(&mut self) -> bool {
        let State::Collecting { records, in_flight, .. } = &mut self.state else {
            return false;
        };
        if records.len().saturating_add(*in_flight) >= MAX_RECORDS {
            self.unavailable();
            return false;
        }
        *in_flight += 1;
        true
    }

    fn finished(&mut self, record: Option<Record>) {
        let Some(record) = record else {
            self.unavailable();
            return;
        };
        let State::Collecting { records, encoded_bytes, in_flight } = &mut self.state else {
            return;
        };
        let Some(remaining) = in_flight.checked_sub(1) else {
            self.unavailable();
            return;
        };
        let Ok(encoded) = record.encode() else {
            self.unavailable();
            return;
        };
        let Some(bytes) = encoded_bytes.checked_add(encoded.len()) else {
            self.unavailable();
            return;
        };
        if bytes > MAX_RECORD_BYTES {
            self.unavailable();
            return;
        }
        // This bounds retained record data. The shared envelope checks its
        // exact aggregate framing limit again at terminal serialization.
        *encoded_bytes = bytes;
        *in_flight = remaining;
        records.push(record);
    }

    fn terminal(&mut self) -> Option<Terminal> {
        match std::mem::replace(&mut self.state, State::Unavailable) {
            State::Disabled => {
                self.state = State::Disabled;
                None
            }
            State::Collecting { records, in_flight: 0, .. } => Some(
                ToolInputs::from_records(records)
                    .and_then(|inputs| inputs.encode())
                    .map_or(Terminal::Unavailable, Terminal::Available),
            ),
            // A second finalization cannot recreate a successful empty fact.
            State::Collecting { .. } | State::Unavailable => Some(Terminal::Unavailable),
        }
    }
}

/// One live attempt, moved into the owning child and consumed after its wait.
/// Dropping it without finishing leaves in-flight state, withholding a terminal
/// reusable envelope. Decoding cannot manufacture this carrier.
pub struct Attempt {
    pending: Option<Pending>,
    registered: bool,
}

impl Session {
    pub fn tool_inputs_parent_path(&self) -> Option<&OsStr> {
        self.tool_input_parent_path.as_deref()
    }

    pub fn tool_inputs_requested(&self) -> bool {
        self.tool_input_collection.borrow().requested()
    }

    pub fn tool_inputs_unavailable(&self) {
        self.tool_input_collection.borrow_mut().unavailable();
    }

    pub fn begin_tool_inputs(
        &self,
        program: &OsStr,
        cwd: &Path,
        child_path: Option<&OsStr>,
        parent_path: Option<&OsStr>,
    ) -> Attempt {
        let registered = self.tool_input_collection.borrow_mut().started();
        let pending = if registered {
            local_profile_for_options(&self.opts).and_then(|profile| {
                Context::new(program, cwd, child_path, parent_path, profile)
                    .and_then(|context| context.begin())
                    .ok()
            })
        } else {
            None
        };
        if registered && pending.is_none() {
            self.tool_inputs_unavailable();
        }
        Attempt { pending, registered }
    }

    pub fn finish_tool_inputs(&self, attempt: Attempt) {
        if attempt.registered {
            // Observe outside the collection lock; another owned attempt may
            // finish while this one hashes its complete candidate readset.
            let record = attempt.pending.and_then(|pending| pending.finish().ok());
            self.tool_input_collection.borrow_mut().finished(record);
        }
    }

    pub fn terminal_tool_inputs(&self) -> Option<Terminal> {
        self.tool_input_collection.borrow_mut().terminal()
    }
}

#[cfg(test)]
mod tests;
