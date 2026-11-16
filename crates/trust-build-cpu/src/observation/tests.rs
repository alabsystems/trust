use serde_json::json;

use super::*;

fn sample() -> Value {
    json!({"schema":1,"kind":"sys.overview","as_of":{"state":"fresh","age_ms":100,"window_ms":1000},
        "machine":{"cpus":28},"global":{"cpu_mc":20_000,"mem_available_bytes":64_000,
        "mem_available_basis":"free_plus_reclaimable_cache","mem_pressure":"normal","thermal":"nominal"}})
}

fn read(value: &Value, now: Instant) -> io::Result<Observation> {
    Observation::from_aterm_sys(&serde_json::to_vec(value).unwrap(), now)
}

#[test]
fn measured_pressure_changes_admission_without_double_counting_native_cpu() {
    let now = Instant::now();
    let cost = NonZeroU64::new(1000).unwrap();
    let good = read(&sample(), now).unwrap();
    // Twenty busy cores include twelve already leased workers: eight idle add
    // room, not a new total of eight that would throttle our own twelve.
    assert_eq!(good.admission_limit(now, 12_000, 64_000, cost, 0), 20);
    // The independent ledger cap wins over the monitor's cache estimate.
    assert_eq!(good.admission_limit(now, 12_000, 5_000, cost, 0), 5);
    let mut warn = sample();
    warn["global"]["mem_pressure"] = json!("warn");
    assert_eq!(read(&warn, now).unwrap().admission_limit(now, 12_000, 64_000, cost, 0), 10);
    warn["global"]["mem_pressure"] = json!("critical");
    assert_eq!(read(&warn, now).unwrap().admission_limit(now, 12_000, 64_000, cost, 0), 0);
    assert_eq!(good.admission_limit(now, 12_000, 0, cost, 0), 0);
}

#[test]
fn cached_age_and_unknown_sensors_cannot_grant_work() {
    let now = Instant::now();
    let good = read(&sample(), now).unwrap();
    assert_eq!(
        good.admission_limit(
            now + Duration::from_secs(3),
            12_000,
            64_000,
            NonZeroU64::new(1000).unwrap(),
            0
        ),
        0
    );
    for path in ["cpu_mc", "mem_available_bytes", "mem_pressure", "thermal"] {
        let mut bad = sample();
        bad["global"][path] = json!({"why":"warming"});
        assert!(read(&bad, now).is_err(), "accepted unknown {path}");
    }
    for state in ["warming", "stale"] {
        let mut bad = sample();
        bad["as_of"]["state"] = json!(state);
        assert!(read(&bad, now).is_err());
    }
    for window in [0, 10_000] {
        let mut bad = sample();
        bad["as_of"]["window_ms"] = json!(window);
        assert!(read(&bad, now).is_err());
    }
}
