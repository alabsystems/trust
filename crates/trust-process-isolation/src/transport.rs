use crate::{Budget, Error};

/// One B1 connection. Implementations must bound allocation before reading and
/// interrupt blocked I/O using the original budget/deadline. Checks surrounding
/// arbitrary blocking I/O do not establish that property.
///
/// `close` must be terminal, idempotent and non-panicking, including during
/// unwinding and Drop. An owned parent endpoint releases its resources. A
/// protected worker endpoint instead closes logically: trusted entry must then
/// terminate the process, leaving kernel teardown and the outside owner to
/// close/reap it without recycling a reserved descriptor.
pub trait Transport {
    fn send(&mut self, frame: &[u8], budget: &Budget) -> Result<(), Error>;
    fn receive(&mut self, budget: &Budget) -> Result<Vec<u8>, Error>;
    fn close(&mut self);
}
