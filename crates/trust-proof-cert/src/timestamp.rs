// trust-proof-cert timestamp parsing
//
// Minimal ISO 8601 parsing used for staleness pruning and registry GC.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

/// Parse an ISO 8601 timestamp to approximate Unix epoch seconds.
///
/// Handles the common `YYYY-MM-DDThh:mm:ssZ` format without pulling in chrono.
/// Used by both `store.rs` (staleness pruning) and `registry.rs` (GC expiration).
pub(crate) fn parse_timestamp_epoch(ts: &str) -> Option<u64> {
    // Minimal parser for "2026-03-27T12:00:00Z" format.
    let ts = ts.trim_end_matches('Z');
    let (date_str, time_str) = ts.split_once('T')?;
    if time_str.contains('T') {
        return None;
    }

    let mut date_parts = date_str.split('-');
    let year: u64 = date_parts.next()?.parse().ok()?;
    let month: u64 = date_parts.next()?.parse().ok()?;
    let day: u64 = date_parts.next()?.parse().ok()?;
    if date_parts.next().is_some() {
        return None;
    }

    let mut time_parts = time_str.split(':');
    let hour: u64 = time_parts.next()?.parse().ok()?;
    let min: u64 = time_parts.next()?.parse().ok()?;
    let sec: u64 = time_parts.next()?.parse().ok()?;
    if time_parts.next().is_some() {
        return None;
    }

    // Approximate days since epoch, which is sufficient for ordering comparisons.
    let days_since_epoch = (year.saturating_sub(1970)) * 365
        + (year.saturating_sub(1969)) / 4
        + cumulative_month_days(month)
        + day.saturating_sub(1);
    Some(days_since_epoch * 86400 + hour * 3600 + min * 60 + sec)
}

fn cumulative_month_days(month: u64) -> u64 {
    match month {
        1 => 0,
        2 => 31,
        3 => 59,
        4 => 90,
        5 => 120,
        6 => 151,
        7 => 181,
        8 => 212,
        9 => 243,
        10 => 273,
        11 => 304,
        12 => 334,
        _ => 0,
    }
}

#[cfg(test)]
mod tests {
    use super::parse_timestamp_epoch;

    #[test]
    fn parse_timestamp_epoch_orders_timestamps() {
        let t1 = parse_timestamp_epoch("2026-03-27T12:00:00Z");
        let t2 = parse_timestamp_epoch("2026-03-27T12:05:00Z");
        assert!(t1 < t2);
    }

    #[test]
    fn parse_timestamp_epoch_rejects_invalid_input() {
        assert!(parse_timestamp_epoch("not-a-timestamp").is_none());
        assert!(parse_timestamp_epoch("").is_none());
    }
}
