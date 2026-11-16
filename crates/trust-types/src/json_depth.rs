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
//!
//! Trust (T3 L4, C09d): [`from_slice_deep`] is the same reader over bytes (the
//! verifier API's bundle, run and manifest decoders), and [`from_value_deep`]
//! the same bound for a reader that already holds a `serde_json::Value` (a
//! contract predicate inside a bundle). [`MAX_DEEP_NESTING`] is then the one
//! nesting bound a contract predicate meets: `trust-verifier-api` refuses a
//! predicate nested deeper than it, because no reader here decodes one, and
//! bounds nothing else about it.

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

#[cfg(test)]
thread_local! {
    static REFUSE_ENCODING_START: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Encode an owned typed value on the same stack used by deep JSON readers.
///
/// The worker takes ownership only after it starts. If spawning fails, `discard`
/// must release the still-owned input without recursive Drop on the caller's
/// stack. Successful and failed serialization both drop their input on the
/// worker. This changes neither the serializer's bytes nor its semantic/size
/// limits; the owning protocol retains those checks.
pub fn encode_owned_on_deep_stack<T: Send, R: Send>(
    value: T,
    encode: impl FnOnce(T) -> Result<R, serde_json::Error> + Send,
    discard: impl FnOnce(T),
) -> Result<R, serde_json::Error> {
    use serde::ser::Error as _;

    let mut pending = Some(value);
    let result = std::thread::scope(|scope| {
        #[cfg(test)]
        if REFUSE_ENCODING_START.with(std::cell::Cell::take) {
            return Err(serde_json::Error::custom("test encoder start refusal"));
        }
        let pending = &mut pending;
        let worker = std::thread::Builder::new()
            .name("trust-deep-json-encode".into())
            .stack_size(DEEP_PARSE_STACK_BYTES)
            .spawn_scoped(scope, move || {
                match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    match pending.take() {
                        Some(value) => encode(value),
                        None => Err(serde_json::Error::custom("the owned encoding job is gone")),
                    }
                })) {
                    Ok(answer) => answer,
                    Err(payload) => {
                        // Even a panic payload may own a recursive input.
                        drop(payload);
                        Err(serde_json::Error::custom("the deep-encode thread panicked"))
                    }
                }
            })
            .map_err(|error| {
                serde_json::Error::custom(format!("the deep-encode thread did not start: {error}"))
            })?;
        worker
            .join()
            .unwrap_or_else(|_| Err(serde_json::Error::custom("the deep-encode thread panicked")))
    });
    if let Some(value) = pending {
        discard(value);
    }
    result
}

/// Serialize and release a JSON value without recursing on the caller's stack.
pub fn into_string_owned_on_deep_stack(
    value: serde_json::Value,
) -> Result<String, serde_json::Error> {
    encode_owned_on_deep_stack(
        value,
        |value| serde_json::to_string(&value),
        discard_value_iteratively,
    )
}

/// Release JSON containers without recursive Drop, including on codec failure.
pub fn discard_value_iteratively(value: serde_json::Value) {
    let mut pending = vec![value];
    while let Some(value) = pending.pop() {
        match value {
            serde_json::Value::Array(values) => pending.extend(values),
            serde_json::Value::Object(values) => {
                pending.extend(values.into_iter().map(|(_, value)| value));
            }
            serde_json::Value::Null
            | serde_json::Value::Bool(_)
            | serde_json::Value::Number(_)
            | serde_json::Value::String(_) => {}
        }
    }
}

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
            if is_recursion_limit_error(&error) && json_nesting_depth(json) <= MAX_DEEP_NESTING =>
        {
            deep_parse_on_dedicated_stack::<T>(json)
                .map_err(|deep_error| deep_error.unwrap_or(error))
        }
        Err(error) => Err(error),
    }
}

/// [`from_str_deep`] over bytes: `serde_json::from_slice`, and on its recursion-limit error
/// the same bounded re-parse (T3 L4, C09d). Bytes that are not UTF-8 keep the original error,
/// as `from_slice` would have refused them anyway.
pub fn from_slice_deep<T>(json: &[u8]) -> Result<T, serde_json::Error>
where
    T: serde::de::DeserializeOwned + Send + 'static,
{
    match serde_json::from_slice::<T>(json) {
        Ok(value) => Ok(value),
        Err(error) if is_recursion_limit_error(&error) => match std::str::from_utf8(json) {
            Ok(text) if json_nesting_depth(text) <= MAX_DEEP_NESTING => {
                deep_parse_on_dedicated_stack::<T>(text)
                    .map_err(|deep_error| deep_error.unwrap_or(error))
            }
            _ => Err(error),
        },
        Err(error) => Err(error),
    }
}

/// The deepest `[`/`{` nesting of `value`'s JSON text ([`json_nesting_depth`] of its
/// serialization), measured without recursion and without printing it (T3 L4, C09d).
#[must_use]
pub fn value_nesting_depth(value: &serde_json::Value) -> usize {
    let mut deepest = 0usize;
    let mut pending = vec![(value, 1usize)];
    while let Some((value, depth)) = pending.pop() {
        match value {
            serde_json::Value::Array(values) => {
                deepest = deepest.max(depth);
                pending.extend(values.iter().map(|value| (value, depth.saturating_add(1))));
            }
            serde_json::Value::Object(object) => {
                deepest = deepest.max(depth);
                pending.extend(object.values().map(|value| (value, depth.saturating_add(1))));
            }
            serde_json::Value::Null
            | serde_json::Value::Bool(_)
            | serde_json::Value::Number(_)
            | serde_json::Value::String(_) => {}
        }
    }
    deepest
}

/// The nesting `serde_json`'s text parser accepts by default: a value nested no deeper is
/// decoded in place by [`from_value_deep`], exactly as `serde_json::from_value` decodes it.
const INLINE_DECODE_NESTING: usize = 128;

/// `serde_json::from_value` under [`from_str_deep`]'s bound, for a reader that holds the
/// JSON as a `Value` already (T3 L4, C09d: a contract predicate in a bundle). A value nested
/// at most [`INLINE_DECODE_NESTING`] levels ([`value_nesting_depth`]) is decoded in place,
/// as before. One nested deeper, up to [`MAX_DEEP_NESTING`], is decoded on a dedicated
/// thread with [`DEEP_PARSE_STACK_BYTES`] of stack, as [`from_str_deep`]'s fallback is,
/// because the derived deserializers recurse once or more per level. One nested deeper
/// still is refused, as [`from_str_deep`] refuses it, and so is a value whose thread cannot
/// start or panics: never a fabricated value.
pub fn from_value_deep<T>(value: &serde_json::Value) -> Result<T, serde_json::Error>
where
    T: serde::de::DeserializeOwned + Send,
{
    use serde::de::Error as _;
    let depth = value_nesting_depth(value);
    if depth <= INLINE_DECODE_NESTING {
        return serde_json::from_value(value.clone());
    }
    if depth > MAX_DEEP_NESTING {
        return Err(serde_json::Error::custom(format!(
            "JSON value nests {depth} levels, past the {MAX_DEEP_NESTING}-level deep-decode bound"
        )));
    }
    std::thread::scope(|scope| {
        let handle = std::thread::Builder::new()
            .name("trust-deep-json".to_string())
            .stack_size(DEEP_PARSE_STACK_BYTES)
            .spawn_scoped(scope, || serde_json::from_value::<T>(value.clone()))
            .map_err(|error| {
                serde_json::Error::custom(format!("the deep-decode thread did not start: {error}"))
            })?;
        handle
            .join()
            .unwrap_or_else(|_| Err(serde_json::Error::custom("the deep-decode thread panicked")))
    })
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

    #[test]
    fn deep_encoding_errors_panics_and_start_refusal_settle_owned_input() {
        use std::sync::atomic::{AtomicBool, Ordering};
        use std::sync::{Arc, Mutex};

        use serde::ser::Error as _;

        struct Probe {
            value: Option<serde_json::Value>,
            dropped: Arc<Mutex<Vec<std::thread::ThreadId>>>,
        }
        impl Drop for Probe {
            fn drop(&mut self) {
                drop(self.value.take());
                self.dropped.lock().unwrap().push(std::thread::current().id());
            }
        }
        let probe = |dropped| {
            let mut value = serde_json::Value::Null;
            for _ in 0..15000 {
                value = serde_json::Value::Array(vec![value]);
            }
            Probe { value: Some(value), dropped }
        };
        let caller = std::thread::current().id();
        for panic in [false, true] {
            let dropped = Arc::new(Mutex::new(Vec::new()));
            let discarded = Arc::new(AtomicBool::new(false));
            let saw_discard = Arc::clone(&discarded);
            let result: Result<(), _> = encode_owned_on_deep_stack(
                probe(Arc::clone(&dropped)),
                move |owned| {
                    let _owned = owned;
                    if panic {
                        let mut payload = serde_json::Value::Null;
                        for _ in 0..15000 {
                            payload = serde_json::Value::Array(vec![payload]);
                        }
                        std::panic::panic_any(payload);
                    }
                    Err(serde_json::Error::custom("serialization refusal"))
                },
                move |mut owned| {
                    saw_discard.store(true, Ordering::SeqCst);
                    discard_value_iteratively(owned.value.take().unwrap());
                },
            );
            assert!(result.is_err());
            assert!(!discarded.load(Ordering::SeqCst));
            let observed = dropped.lock().unwrap();
            assert_eq!(observed.len(), 1);
            assert_ne!(observed[0], caller, "started jobs release recursive input on their worker");
        }

        let dropped = Arc::new(Mutex::new(Vec::new()));
        let invoked = Arc::new(AtomicBool::new(false));
        let saw_invoke = Arc::clone(&invoked);
        REFUSE_ENCODING_START.with(|refuse| refuse.set(true));
        let result = encode_owned_on_deep_stack(
            probe(Arc::clone(&dropped)),
            move |_owned| {
                saw_invoke.store(true, Ordering::SeqCst);
                Ok(())
            },
            |mut owned| discard_value_iteratively(owned.value.take().unwrap()),
        );
        assert!(result.unwrap_err().to_string().contains("start refusal"));
        assert!(!invoked.load(Ordering::SeqCst));
        assert_eq!(*dropped.lock().unwrap(), vec![caller]);
    }

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
                // Every payload built here nests the single scalar `1`; reading
                // it back shows the deep parse kept the value, not just the shape.
                Nested::Leaf(value) => {
                    assert_eq!(value, 1, "the innermost value survives the deep parse");
                    return depth;
                }
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

    /// A JSON value nested `depth` arrays deep around the scalar `1`, built without recursion.
    fn nested_value(depth: usize) -> serde_json::Value {
        let mut value = serde_json::Value::from(1);
        for _ in 0..depth {
            value = serde_json::Value::Array(vec![value]);
        }
        value
    }

    /// Run `test` on a thread whose stack can drop and clone a value at the deep bound: a
    /// `serde_json::Value`'s `Drop` and `Clone` recurse, and a test thread has 2 MiB.
    fn on_a_deep_stack(test: impl FnOnce() + Send) {
        std::thread::scope(|scope| {
            std::thread::Builder::new()
                .stack_size(DEEP_PARSE_STACK_BYTES)
                .spawn_scoped(scope, test)
                .expect("the test thread starts")
                .join()
                .expect("the test passes");
        });
    }

    /// T3 L4 (C09d): the byte reader is [`from_str_deep`]'s: the fast path, the deep
    /// fallback, the bound, and a non-recursion error passed through.
    #[test]
    fn slice_reader_recovers_deep_payloads_under_the_same_bound() {
        let v: Vec<i64> = from_slice_deep(b"[1,2,3]").expect("shallow parse");
        assert_eq!(v, vec![1, 2, 3]);
        let parsed: Nested = from_slice_deep(nested_array(3_000).as_bytes()).expect("deep parse");
        assert_eq!(depth_and_consume(parsed), 3_000);
        let err = from_slice_deep::<Nested>(nested_array(MAX_DEEP_NESTING + 1).as_bytes())
            .expect_err("bounded");
        assert!(is_recursion_limit_error(&err), "{err}");
        let err = from_slice_deep::<Vec<i64>>(b"[1,").expect_err("syntax error");
        assert!(!is_recursion_limit_error(&err));
    }

    /// T3 L4 (C09d): the value measure is the text measure, without printing.
    #[test]
    fn value_nesting_depth_is_the_text_nesting_depth() {
        for json in ["1", "[]", "[1]", "{}", r#"{"a":[[1],{"b":{}}]}"#, r#"[{"a":"[[["}]"#] {
            let value: serde_json::Value = serde_json::from_str(json).expect("parses");
            assert_eq!(value_nesting_depth(&value), json_nesting_depth(json), "{json}");
        }
        assert_eq!(value_nesting_depth(&nested_value(500)), 500);
    }

    /// T3 L4 (C09d): a value is decoded in place up to the default nesting, on the deep
    /// thread past it, and refused past [`MAX_DEEP_NESTING`]; a malformed one is refused at
    /// any depth.
    #[test]
    fn value_reader_decodes_to_the_deep_bound_and_refuses_past_it() {
        on_a_deep_stack(|| {
            let shallow: Nested = from_value_deep(&nested_value(3)).expect("inline decode");
            assert_eq!(depth_and_consume(shallow), 3);
            for depth in [INLINE_DECODE_NESTING + 1, 3_000, MAX_DEEP_NESTING] {
                let parsed: Nested = from_value_deep(&nested_value(depth)).expect("deep decode");
                assert_eq!(depth_and_consume(parsed), depth);
            }
            let err = from_value_deep::<Nested>(&nested_value(MAX_DEEP_NESTING + 1))
                .expect_err("past the bound");
            assert!(err.to_string().contains("deep-decode bound"), "{err}");
            let mut malformed = serde_json::Value::from("not a leaf");
            for _ in 0..1_000 {
                malformed = serde_json::Value::Array(vec![malformed]);
            }
            assert!(from_value_deep::<Nested>(&malformed).is_err(), "malformed at depth");
        });
    }

    #[test]
    fn nesting_depth_scan_ignores_string_contents() {
        assert_eq!(json_nesting_depth(r#"{"a":"[[[["}"#), 1);
        assert_eq!(json_nesting_depth(r#"{"a\"":"}{","b":[[1]]}"#), 3);
        assert_eq!(json_nesting_depth(r#"{"esc":"\\"}"#), 1);
        assert_eq!(json_nesting_depth(&nested_array(42)), 42);
    }
}
