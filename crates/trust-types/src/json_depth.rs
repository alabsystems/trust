//! Depth-tolerant JSON deserialization for compiler-emitted payloads.
//!
//! Trust (R1 corpus, native-lane fallthrough): the typed formula payloads the
//! compiler attaches to verifier-api obligations (`trust.vc.formula.payload`,
//! a `trust.spec-predicate.v1` `TrustSpecPredicate`) are recursive expression
//! trees. Dense loop-unrolled functions (itoa's `Unsigned::fmt` family on the
//! first corpus sweep) legitimately exceed serde_json's default 128-level
//! recursion limit, so `serde_json::from_str` failed with "recursion limit
//! exceeded" — the typed-CHC direct lane then marked the obligation's lowering
//! unsupported ("malformed TrustSpecPredicate metadata") and the obligation
//! fell through to trust-mc with no typed input, stamping cascade noise instead
//! of getting a real solve.
//!
//! [`from_str_deep`] keeps the fast path byte-identical (a plain
//! `serde_json::from_str`) and adds a BOUNDED fallback only when that parse
//! fails with the recursion-limit error: re-parse with
//! `Deserializer::disable_recursion_limit()` on a dedicated thread with a large
//! stack. The fallback is bounded so deep input can never crash the process:
//!
//! * nesting: a linear byte scan ([`json_nesting_depth`]) measures the
//!   payload's real structural depth up front; anything past
//!   [`MAX_DEEP_NESTING`] keeps the original error. The bound is deliberately
//!   sized for the WHOLE lifecycle of the parsed tree — the consumer's
//!   recursive traversals and the derived recursive `Drop` run on ordinary
//!   (~8 MiB) compiler threads, so the parse-side stack is not the binding
//!   constraint;
//! * stack: the re-parse itself runs on its own thread with
//!   [`DEEP_PARSE_STACK_BYTES`] of stack, giving the deserializer two orders
//!   of magnitude of headroom at the depth bound.
//!
//! Failure of the fallback (depth/size bound, thread spawn failure, parse
//! error) surfaces the ORIGINAL recursion-limit error — behavior identical to
//! before, an honest parse failure, never a fabricated value. This is a pure
//! completeness recovery: it can only turn "unparseable payload" into "parsed
//! payload", and every consumer treats a parse failure as fail-closed
//! Unsupported/None.

/// Maximum structural nesting depth the deep fallback will parse.
///
/// The parsed tree must remain safe to recursively traverse (consumer lowering
/// walks, e.g. `trust_mc_typed_chc_expr_from_trust_spec`) and recursively drop
/// on ordinary ~8 MiB compiler threads: at a worst-case ~500 bytes per frame,
/// 4K depth costs ~2 MiB — comfortable headroom — while covering the real
/// corpus payloads (itoa's dense `Unsigned::fmt` formulas exceed the 128
/// default but sit well under this bound).
pub const MAX_DEEP_NESTING: usize = 4_096;

/// Stack size for the dedicated deep-parse thread: 256 MiB of lazily-committed
/// stack is >100x the worst-case deserializer usage at [`MAX_DEEP_NESTING`].
const DEEP_PARSE_STACK_BYTES: usize = 256 * 1024 * 1024;

/// True when `error` is serde_json's recursion-limit syntax error.
fn is_recursion_limit_error(error: &serde_json::Error) -> bool {
    error.classify() == serde_json::error::Category::Syntax
        && error.to_string().contains("recursion limit exceeded")
}

/// Measure the maximum `[`/`{` nesting depth of `json` in one linear scan,
/// ignoring structural characters inside string literals (escape-aware).
#[must_use]
pub fn json_nesting_depth(json: &str) -> usize {
    let mut depth = 0usize;
    let mut max_depth = 0usize;
    let mut in_string = false;
    let mut escaped = false;
    for byte in json.bytes() {
        if in_string {
            if escaped {
                escaped = false;
            } else if byte == b'\\' {
                escaped = true;
            } else if byte == b'"' {
                in_string = false;
            }
            continue;
        }
        match byte {
            b'"' => in_string = true,
            b'[' | b'{' => {
                depth += 1;
                max_depth = max_depth.max(depth);
            }
            b']' | b'}' => depth = depth.saturating_sub(1),
            _ => {}
        }
    }
    max_depth
}

/// `serde_json::from_str` with a bounded deep-recursion fallback.
///
/// See the module docs for the exact bounds and failure behavior.
pub fn from_str_deep<T>(json: &str) -> Result<T, serde_json::Error>
where
    T: serde::de::DeserializeOwned + Send + 'static,
{
    match serde_json::from_str::<T>(json) {
        Ok(value) => Ok(value),
        Err(error)
            if is_recursion_limit_error(&error)
                && json_nesting_depth(json) <= MAX_DEEP_NESTING =>
        {
            deep_parse_on_dedicated_stack::<T>(json)
                .map_err(|deep_error| deep_error.unwrap_or(error))
        }
        Err(error) => Err(error),
    }
}

/// Re-parse `json` with the recursion limit disabled on a big-stack thread.
///
/// Returns `Err(None)` for infrastructure failures (thread spawn/join), so the
/// caller can surface the ORIGINAL recursion-limit error unchanged.
fn deep_parse_on_dedicated_stack<T>(json: &str) -> Result<T, Option<serde_json::Error>>
where
    T: serde::de::DeserializeOwned + Send + 'static,
{
    let owned = json.to_string();
    let handle = std::thread::Builder::new()
        .name("trust-deep-json".to_string())
        .stack_size(DEEP_PARSE_STACK_BYTES)
        .spawn(move || -> Result<T, serde_json::Error> {
            let mut deserializer = serde_json::Deserializer::from_str(&owned);
            deserializer.disable_recursion_limit();
            let value = T::deserialize(&mut deserializer)?;
            deserializer.end()?;
            Ok(value)
        })
        .map_err(|_| None)?;
    match handle.join() {
        Ok(Ok(value)) => Ok(value),
        Ok(Err(parse_error)) => Err(Some(parse_error)),
        // A panicked parse thread (should be unreachable given the depth bound)
        // degrades to the original error — never poisons the caller.
        Err(_) => Err(None),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn nested_array(depth: usize) -> String {
        let mut s = String::with_capacity(depth * 2 + 1);
        for _ in 0..depth {
            s.push('[');
        }
        s.push('1');
        for _ in 0..depth {
            s.push(']');
        }
        s
    }

    #[derive(serde::Deserialize, Debug)]
    #[serde(untagged)]
    enum Nested {
        Leaf(i64),
        Node(Vec<Nested>),
    }

    /// Iterative depth (and iterative drop) so the TEST thread's small stack
    /// never recurses over the parsed tree.
    fn depth_and_consume(root: Nested) -> usize {
        let mut depth = 0usize;
        let mut current = root;
        loop {
            match current {
                Nested::Leaf(_) => return depth,
                Nested::Node(mut children) => {
                    depth += 1;
                    current = children.pop().expect("non-empty");
                }
            }
        }
    }

    #[test]
    fn shallow_payload_uses_fast_path() {
        let v: Vec<i64> = from_str_deep("[1,2,3]").expect("shallow parse");
        assert_eq!(v, vec![1, 2, 3]);
    }

    #[test]
    fn plain_parse_fails_past_default_recursion_limit() {
        // Pin the premise: serde_json's default limit rejects depth 500.
        let err = serde_json::from_str::<Nested>(&nested_array(500)).expect_err("limit");
        assert!(is_recursion_limit_error(&err), "{err}");
    }

    #[test]
    fn deep_payload_recovers_past_default_recursion_limit() {
        // itoa's dense Unsigned::fmt payloads sit in the 10^2..10^4 depth band.
        let parsed: Nested = from_str_deep(&nested_array(3_000)).expect("deep parse");
        assert_eq!(depth_and_consume(parsed), 3_000);
    }

    #[test]
    fn past_depth_bound_keeps_original_recursion_error() {
        let err =
            from_str_deep::<Nested>(&nested_array(MAX_DEEP_NESTING + 1)).expect_err("bounded");
        assert!(is_recursion_limit_error(&err), "{err}");
    }

    #[test]
    fn non_recursion_errors_pass_through_unchanged() {
        let err = from_str_deep::<Vec<i64>>("[1,").expect_err("syntax error");
        assert!(!is_recursion_limit_error(&err));
    }

    #[test]
    fn nesting_depth_scan_ignores_string_contents() {
        assert_eq!(json_nesting_depth(r#"{"a":"[[[["}"#), 1);
        assert_eq!(json_nesting_depth(r#"{"a\"":"}{","b":[[1]]}"#), 3);
        assert_eq!(json_nesting_depth(r#"{"esc":"\\"}"#), 1);
        assert_eq!(json_nesting_depth(&nested_array(42)), 42);
    }
}
