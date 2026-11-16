//! Eligibility for incremental ThinLTO work-product reuse.

/// Missing keys are missing evidence, including when both sessions lack a key.
/// An empty persisted key also cannot authorize reuse.
pub(super) fn cache_keys_match(previous: Option<&str>, current: Option<&str>) -> bool {
    matches!((previous, current), (Some(old), Some(new)) if !new.is_empty() && old == new)
}

#[cfg(test)]
mod tests;
