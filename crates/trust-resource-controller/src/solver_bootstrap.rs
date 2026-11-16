// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! One private final-image bootstrap. Records describe an existing owned
//! attempt; decoding never establishes admission or installed kernel policy.
//! The Host must bind its retained claim, original child and selected image
//! before sending Offer, and durably commit the exact Run clock before sending
//! Run. This module neither launches a process nor grants another resource.
mod wire;
pub use wire::Frame;
/// Exact original-lane record size; an Offer/Ready/Run is never a length-prefixed
/// ordinary controller request and never carries descriptor or grant authority.
pub const FRAME_LEN: usize = wire::LEN;

/// The descriptor transport and native identity receiver require the existing
/// client feature. DTO-only consumers keep the std-only default-features=false.
#[cfg(all(feature = "bootstrap-receiver", any(target_os = "linux", target_os = "macos")))]
mod receive;
#[cfg(all(feature = "bootstrap-receiver", any(target_os = "linux", target_os = "macos")))]
pub use receive::{Accepted, receive};

#[cfg(all(feature = "channel", any(target_os = "linux", target_os = "macos")))]
mod channel {
    use std::io;
    use std::os::fd::BorrowedFd;
    use std::os::unix::net::UnixStream;
    use std::time::Instant;

    use super::{Frame, wire};
    /// A fixed-record private channel; never mix ordinary controller frames
    /// into this socket. Failed or partial transfer poisons the original lane.
    pub struct BootstrapChannel {
        pub(crate) channel: crate::Channel,
        failed: bool,
    }
    impl BootstrapChannel {
        pub fn new(stream: UnixStream) -> io::Result<Self> {
            crate::Channel::new(stream).map(|channel| Self { channel, failed: false })
        }
        pub fn send(&mut self, frame: Frame, deadline: Instant) -> io::Result<()> {
            if self.failed {
                return Err(io::ErrorKind::BrokenPipe.into());
            }
            let result = (|| {
                let bytes = frame.encode();
                Frame::decode(&bytes)?;
                self.channel.send_fixed(bytes, deadline)
            })();
            self.failed |= result.is_err();
            result
        }
        pub fn receive(&mut self, deadline: Instant) -> io::Result<Frame> {
            if self.failed {
                return Err(io::ErrorKind::BrokenPipe.into());
            }
            let result = self
                .channel
                .receive_fixed::<{ wire::LEN }>(deadline)
                .and_then(|bytes| Frame::decode(&bytes));
            self.failed |= result.is_err();
            result
        }
        pub fn as_fd(&self) -> BorrowedFd<'_> {
            self.channel.as_fd()
        }
    }
}
#[cfg(all(feature = "channel", any(target_os = "linux", target_os = "macos")))]
pub use channel::BootstrapChannel;

#[cfg(test)]
mod tests;
