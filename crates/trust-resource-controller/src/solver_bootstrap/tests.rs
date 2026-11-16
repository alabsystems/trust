// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

use super::*;

fn offer() -> Frame {
    Frame {
        kind: 1,
        attempt: [1; 16],
        challenge: [2; 32],
        pid: 42,
        birth: 7,
        footprint_mib: 256,
        units: 1,
        monotonic_ns: 0,
    }
}

#[test]
fn record_rejects_unbound_run_clocks_and_lossy_native_numbers() {
    let offer = offer();
    assert!(Frame::decode(&offer.encode()).unwrap() == offer);
    assert!(Frame::decode(&offer.response(2, 0).encode()).is_ok());
    assert!(Frame::decode(&offer.response(3, 99).encode()).is_ok());
    assert!(Frame::decode(&offer.response(3, 0).encode()).is_err());
    assert!(Frame::decode(&offer.response(2, 99).encode()).is_err());
    let mut bytes = offer.encode();
    bytes[64..72].copy_from_slice(&(u64::from(u32::MAX) + 1).to_be_bytes());
    assert!(Frame::decode(&bytes).is_err());
    assert!(Frame::decode(&offer.encode()[..103]).is_err());
    let mut trailing = offer.encode().to_vec();
    trailing.push(0);
    assert!(Frame::decode(&trailing).is_err());
}

#[cfg(all(feature = "channel", any(target_os = "linux", target_os = "macos")))]
#[test]
fn malformed_original_channel_cannot_be_replayed() {
    use std::io::Write as _;
    use std::os::unix::net::UnixStream;
    use std::time::{Duration, Instant};
    let (mut writer, reader) = UnixStream::pair().unwrap();
    let mut malformed = offer().encode();
    malformed[0] ^= 1;
    writer.write_all(&malformed).unwrap();
    writer.write_all(&offer().encode()).unwrap();
    let mut reader = BootstrapChannel::new(reader).unwrap();
    let deadline = Instant::now() + Duration::from_secs(1);
    assert!(reader.receive(deadline).is_err());
    assert_eq!(reader.receive(deadline).err().unwrap().kind(), std::io::ErrorKind::BrokenPipe);
}
