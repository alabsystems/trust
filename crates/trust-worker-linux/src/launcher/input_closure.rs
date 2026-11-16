use sha2::{Digest, Sha256};

use super::{InputSource, contract};
use crate::Error;

/// Compiler-owned expected input identity, not admission or a worker receipt.
/// Static input roles and the optional native graph have separate hash domains.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InputClosureIdentity {
    static_inputs: [u8; 32],
    native_graph: Option<[u8; 32]>,
}

impl InputClosureIdentity {
    pub fn from_plan(
        worker: &InputSource<'_>,
        inputs: &[InputSource<'_>],
        native_graph: Option<[u8; 32]>,
    ) -> Result<Self, Error> {
        if inputs.len() > 27 || native_graph == Some([0; 32]) {
            return Err(contract("input closure shape"));
        }
        let mut h = Sha256::new();
        h.update(b"trust-static-worker-closure-v1\0");
        for source in std::iter::once(worker).chain(inputs) {
            h.update(source.sha256);
            h.update(source.size.to_le_bytes());
            h.update([u8::from(source.executable)]);
        }
        Ok(Self { static_inputs: h.finalize().into(), native_graph })
    }

    /// This composite, rather than either component, occupies Binding.input_closure.
    pub fn digest(&self) -> [u8; 32] {
        let mut h = Sha256::new();
        h.update(b"trust-invocation-input-closure-v1\0");
        h.update(self.static_inputs);
        h.update([u8::from(self.native_graph.is_some())]);
        if let Some(native) = self.native_graph {
            h.update(native);
        }
        h.finalize().into()
    }

    pub fn native_graph(&self) -> Option<[u8; 32]> {
        self.native_graph
    }
}
