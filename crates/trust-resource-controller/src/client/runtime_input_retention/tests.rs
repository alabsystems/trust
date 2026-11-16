use std::time::Duration;

use super::*;

#[test]
fn original_deadline_covers_final_native_observation_and_owner_construction() {
    let mut entered = false;
    let expired = finish_observation(Instant::now(), || {
        entered = true;
        Ok(())
    });
    assert_eq!(expired.unwrap_err().kind(), io::ErrorKind::TimedOut);
    assert!(!entered);

    // Actual native observations, not a synthetic Host/Job/completion owner.
    // Their late result must not escape the same guard used after client ACK,
    // final descriptor checks, and opaque observation-owner construction.
    let deadline = Instant::now() + Duration::from_millis(5);
    let late = finish_observation(deadline, || {
        std::thread::sleep(Duration::from_millis(20));
        let file = std::fs::File::open("/dev/null")?;
        let _ = file.metadata()?;
        let own = trust_resource_provenance::process::read_identity(std::process::id())?;
        Ok((own, file))
    });
    assert_eq!(late.unwrap_err().kind(), io::ErrorKind::TimedOut);
    let observed = finish_observation(Instant::now() + Duration::from_secs(30), || {
        trust_resource_provenance::process::read_identity(std::process::id())
    })
    .unwrap();
    assert_eq!(observed.pid, std::process::id());
}
