// Adversarial BigInt differential: a curated mini-suite plus a corpus sweep of
// the BigInt / BigInt typed-array / numeric-operator directories, each case run
// through BOTH trust_js_sem and the real Node trace driver, requiring
// byte-for-byte trace equality. Refusals are sound and counted; a WRONG trace
// is gate-fatal. Env-gated on TRUST_JS_NODE (and optionally TRUST_JS262_CORPUS).
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use std::collections::BTreeMap;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;
use trust_js_sem::{evaluate_case, evaluate_case_opts, SemOutcome};
use trust_js_trace::{explain_divergence, extract_trace, traces_equal};

// Default corpus root: <repo>/build/js262/test262-<pinned rev>. Derived from
// CARGO_MANIFEST_DIR so it works in any checkout; override with
// TRUST_JS262_CORPUS.
const DEFAULT_CORPUS: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../build/js262/test262-9e61c12835c5e4a3bdba93850427e6742c4f64c4"
);

/// (directory, per-dir cap). BigInt built-ins, the BigInt typed-array ctors,
/// and the numeric-operator directories (which also exercise the new Number
/// bitwise/shift/exponent lanes against Node).
const BIGINT_DIRS: &[(&str, usize)] = &[
    ("test/built-ins/BigInt", 400),
    ("test/language/literals/numeric", 400),
    ("test/language/literals/bigint", 400),
    ("test/built-ins/JSON/stringify", 200),
    ("test/built-ins/TypedArrayConstructors/BigInt64Array", 200),
    ("test/built-ins/TypedArrayConstructors/BigUint64Array", 200),
    ("test/built-ins/TypedArrayConstructors/ctors-bigint", 200),
    ("test/language/expressions/addition", 400),
    ("test/language/expressions/subtraction", 200),
    ("test/language/expressions/multiplication", 200),
    ("test/language/expressions/division", 200),
    ("test/language/expressions/modulus", 200),
    ("test/language/expressions/exponentiation", 200),
    ("test/language/expressions/bitwise-and", 200),
    ("test/language/expressions/bitwise-or", 200),
    ("test/language/expressions/bitwise-xor", 200),
    ("test/language/expressions/bitwise-not", 200),
    ("test/language/expressions/left-shift", 200),
    ("test/language/expressions/right-shift", 200),
    ("test/language/expressions/unsigned-right-shift", 200),
    ("test/language/expressions/equals", 200),
    ("test/language/expressions/does-not-equals", 200),
    ("test/language/expressions/strict-equals", 200),
    ("test/language/expressions/strict-does-not-equals", 200),
    ("test/language/expressions/less-than", 200),
    ("test/language/expressions/less-than-or-equal", 200),
    ("test/language/expressions/greater-than", 200),
    ("test/language/expressions/greater-than-or-equal", 200),
    ("test/language/expressions/unary-minus", 100),
    ("test/language/expressions/typeof", 100),
];

// ---------------------------------------------------------------------------
// Curated adversarial minis (completion-witness ON, like the driver default
// for engine-vs-sem work). Each is checked to either COVER (trace-equal to
// Node) or REFUSE soundly.
// ---------------------------------------------------------------------------

#[derive(Clone, Copy)]
#[allow(dead_code)] // Refuse is part of the harness contract (no minis use it yet)
enum Expect {
    Cover,
    Refuse,
}
use Expect::{Cover, Refuse};

const MINIS: &[(&str, Expect, &str)] = &[
    // Literals + projection (projecting a bigint throws TypeError under the
    // driver — reproduced exactly).
    ("lit-log", Cover, "console.log(10n);"),
    ("lit-sep", Cover, "console.log(1_000n === 1000n);"),
    ("lit-hex", Cover, "console.log(0x1fn === 31n);"),
    ("lit-oct", Cover, "console.log(0o17n === 15n);"),
    ("lit-bin", Cover, "console.log(0b101n === 5n);"),
    ("witness-bigint", Cover, "1n + 2n"),
    ("throw-bigint", Cover, "throw 10n;"),
    ("nested-log", Cover, "console.log([1n, 2n]);"),
    // Arithmetic.
    ("add", Cover, "if (1n + 2n !== 3n) throw 0;"),
    ("sub", Cover, "if (5n - 8n !== -3n) throw 0;"),
    ("mul", Cover, "if (6n * 7n !== 42n) throw 0;"),
    ("div-trunc", Cover, "if (-7n / 2n !== -3n) throw 0;"),
    ("rem-sign", Cover, "if (-7n % 2n !== -1n) throw 0;"),
    ("pow", Cover, "if (2n ** 10n !== 1024n) throw 0;"),
    ("div-zero", Cover, "try { 5n / 0n; throw 1; } catch (e) { if (!(e instanceof RangeError)) throw 2; }"),
    ("rem-zero", Cover, "try { 5n % 0n; throw 1; } catch (e) { if (!(e instanceof RangeError)) throw 2; }"),
    ("pow-neg", Cover, "try { 2n ** -1n; throw 1; } catch (e) { if (!(e instanceof RangeError)) throw 2; }"),
    // Unary.
    ("neg", Cover, "if (-5n !== 0n - 5n) throw 0;"),
    ("bitnot", Cover, "if (~5n !== -6n) throw 0;"),
    ("unary-plus-throws", Cover, "try { +5n; throw 1; } catch (e) { if (!(e instanceof TypeError)) throw 2; }"),
    ("increment", Cover, "let x = 5n; x++; if (x !== 6n) throw 0;"),
    ("decrement-pre", Cover, "let x = 5n; if (--x !== 4n) throw 0;"),
    // Bitwise / shift.
    ("and", Cover, "if ((-5n & 3n) !== 3n) throw 0;"),
    ("or", Cover, "if ((-5n | 3n) !== -5n) throw 0;"),
    ("xor", Cover, "if ((-5n ^ 3n) !== -8n) throw 0;"),
    ("shl", Cover, "if ((-5n << 1n) !== -10n) throw 0;"),
    ("shr", Cover, "if ((-5n >> 1n) !== -3n) throw 0;"),
    ("ushr-throws", Cover, "try { 5n >>> 1n; throw 1; } catch (e) { if (!(e instanceof TypeError)) throw 2; }"),
    // Mixed-type TypeErrors.
    ("mixed-add", Cover, "try { 1n + 1; throw 1; } catch (e) { if (!(e instanceof TypeError)) throw 2; }"),
    ("mixed-and", Cover, "try { 1n & 1; throw 1; } catch (e) { if (!(e instanceof TypeError)) throw 2; }"),
    ("mixed-ushr", Cover, "try { 1n >>> 1; throw 1; } catch (e) { if (!(e instanceof TypeError)) throw 2; }"),
    // Comparison / equality (mixed real ordering).
    ("cmp-lt", Cover, "if (!(1n < 2)) throw 0;"),
    ("cmp-gt", Cover, "if (!(2n > 1.5)) throw 0;"),
    ("cmp-nan", Cover, "if (1n < NaN) throw 0;"),
    ("cmp-str", Cover, "if (!(1n < '2')) throw 0;"),
    ("cmp-big", Cover, "if ((2n ** 64n) > 1.8446744073709552e19) throw 0;"),
    ("eq-loose", Cover, "if (!(1n == 1)) throw 0;"),
    ("eq-loose-str", Cover, "if (!(2n == '2')) throw 0;"),
    ("eq-loose-bool", Cover, "if (!(1n == true)) throw 0;"),
    ("eq-strict", Cover, "if (1n === 1) throw 0;"),
    ("eq-nan", Cover, "if (NaN == 1n) throw 0;"),
    ("eq-frac", Cover, "if (1n == 1.5) throw 0;"),
    // typeof / ToBoolean / ToString.
    ("typeof", Cover, "if (typeof 1n !== 'bigint') throw 0;"),
    ("bool-zero", Cover, "if (0n ? 1 : 0) throw 0;"),
    ("bool-nonzero", Cover, "if (!(5n ? 1 : 0)) throw 0;"),
    ("string", Cover, "if (String(10n) !== '10') throw 0;"),
    ("template", Cover, "if (`${5n}` !== '5') throw 0;"),
    ("concat", Cover, "if ('x' + 0n !== 'x0') throw 0;"),
    ("tostring-tag", Cover, "if (Object.prototype.toString.call(5n) !== '[object BigInt]') throw 0;"),
    // BigInt() function + coercions.
    ("bigint-str", Cover, "if (BigInt('123') !== 123n) throw 0;"),
    ("bigint-hex", Cover, "if (BigInt('0x10') !== 16n) throw 0;"),
    ("bigint-bool", Cover, "if (BigInt(true) !== 1n) throw 0;"),
    ("bigint-num", Cover, "if (BigInt(1.0) !== 1n) throw 0;"),
    ("bigint-num-frac", Cover, "try { BigInt(1.5); throw 1; } catch (e) { if (!(e instanceof RangeError)) throw 2; }"),
    ("bigint-nan", Cover, "try { BigInt(NaN); throw 1; } catch (e) { if (!(e instanceof RangeError)) throw 2; }"),
    ("bigint-null", Cover, "try { BigInt(null); throw 1; } catch (e) { if (!(e instanceof TypeError)) throw 2; }"),
    ("bigint-sym", Cover, "try { BigInt(Symbol()); throw 1; } catch (e) { if (!(e instanceof TypeError)) throw 2; }"),
    ("bigint-bad-str", Cover, "try { BigInt('1.5'); throw 1; } catch (e) { if (!(e instanceof SyntaxError)) throw 2; }"),
    ("bigint-arr", Cover, "if (BigInt([5]) !== 5n) throw 0;"),
    ("new-bigint", Cover, "try { new BigInt(1); throw 1; } catch (e) { if (!(e instanceof TypeError)) throw 2; }"),
    // Number(bigint) + prototype methods.
    ("number-of-bigint", Cover, "if (Number(10n) !== 10) throw 0;"),
    ("number-huge", Cover, "if (Number(2n ** 1024n) !== Infinity) throw 0;"),
    ("proto-tostring-radix", Cover, "if ((255n).toString(16) !== 'ff') throw 0;"),
    ("proto-tostring-neg", Cover, "if ((-255n).toString(2) !== '-11111111') throw 0;"),
    ("proto-tostring-bad-radix", Cover, "try { (10n).toString(1); throw 1; } catch (e) { if (!(e instanceof RangeError)) throw 2; }"),
    ("proto-valueof", Cover, "if ((5n).valueOf() !== 5n) throw 0;"),
    ("proto-on-prototype-throws", Cover, "try { BigInt.prototype.valueOf.call(BigInt.prototype); throw 1; } catch (e) { if (!(e instanceof TypeError)) throw 2; }"),
    // asIntN / asUintN.
    ("asintn", Cover, "if (BigInt.asIntN(8, 256n) !== 0n) throw 0;"),
    ("asintn-neg", Cover, "if (BigInt.asIntN(8, 255n) !== -1n) throw 0;"),
    ("asuintn", Cover, "if (BigInt.asUintN(8, -1n) !== 255n) throw 0;"),
    ("asintn-zero", Cover, "if (BigInt.asIntN(0, 123n) !== 0n) throw 0;"),
    // JSON.stringify throws.
    ("json-throws", Cover, "try { JSON.stringify(10n); throw 1; } catch (e) { if (!(e instanceof TypeError)) throw 2; }"),
    // ToNumber(bigint) throws (Math).
    ("math-throws", Cover, "try { Math.abs(1n); throw 1; } catch (e) { if (!(e instanceof TypeError)) throw 2; }"),
    // Property keys.
    ("bigint-key", Cover, "var o = {}; o[1n] = 'a'; if (o['1'] !== 'a') throw 0;"),
    ("obj-lit-key", Cover, "if (Object.keys({1n: 5})[0] !== '1') throw 0;"),
    // BigInt typed arrays.
    ("bi64-construct", Cover, "var a = new BigInt64Array(3); if (a.length !== 3 || a[0] !== 0n) throw 0;"),
    ("bi64-from-arr", Cover, "var a = new BigInt64Array([1n, 2n]); if (a[1] !== 2n) throw 0;"),
    ("bi64-set-get", Cover, "var a = new BigInt64Array(1); a[0] = 5n; if (a[0] !== 5n) throw 0;"),
    ("bi64-wrap", Cover, "var a = new BigInt64Array(1); a[0] = (2n ** 63n); if (a[0] !== -(2n ** 63n)) throw 0;"),
    ("bu64-wrap", Cover, "var a = new BigUint64Array(1); a[0] = -1n; if (a[0] !== (2n ** 64n) - 1n) throw 0;"),
    ("bi64-set-num-throws", Cover, "var a = new BigInt64Array(1); try { a[0] = 5; if (a[0] !== 0n) throw 3; } catch (e) { if (!(e instanceof TypeError)) throw 2; }"),
    ("bi64-from-num-throws", Cover, "try { new BigInt64Array([1]); throw 1; } catch (e) { if (!(e instanceof TypeError)) throw 2; }"),
    ("bi64-fill", Cover, "var a = new BigInt64Array(3); a.fill(7n); if (a[2] !== 7n) throw 0;"),
    ("bi64-reverse", Cover, "var a = new BigInt64Array([1n, 2n, 3n]); a.reverse(); if (a[0] !== 3n) throw 0;"),
    ("bi64-cross-type-throws", Cover, "try { new Int32Array(new BigInt64Array([1n])); throw 1; } catch (e) { if (!(e instanceof TypeError)) throw 2; }"),
    // Number bitwise/shift/exp (the new non-BigInt lanes) vs Node.
    ("num-and", Cover, "if ((3 & 1) !== 1) throw 0;"),
    ("num-or", Cover, "if ((5 | 2) !== 7) throw 0;"),
    ("num-xor", Cover, "if ((5 ^ 1) !== 4) throw 0;"),
    ("num-shl", Cover, "if ((1 << 5) !== 32) throw 0;"),
    ("num-shr", Cover, "if ((-8 >> 1) !== -4) throw 0;"),
    ("num-ushr", Cover, "if ((-1 >>> 0) !== 4294967295) throw 0;"),
    ("num-bitnot", Cover, "if (~5 !== -6) throw 0;"),
    ("num-shl-wrap", Cover, "if ((1 << 32) !== 1) throw 0;"),
    ("num-pow", Cover, "if (2 ** 10 !== 1024) throw 0;"),
    ("num-pow-right-assoc", Cover, "if (2 ** 3 ** 2 !== 512) throw 0;"),
    ("num-pow-unary-syntax", Cover, "eval; try { eval('-2 ** 2'); throw 1; } catch (e) { if (!(e instanceof SyntaxError)) throw 2; }"),
    ("compound-bitand", Cover, "let x = 6; x &= 3; if (x !== 2) throw 0;"),
    ("compound-shl", Cover, "let x = 1; x <<= 4; if (x !== 16) throw 0;"),
    ("compound-bigint-add", Cover, "let x = 5n; x += 2n; if (x !== 7n) throw 0;"),
    // Numeric-separator early errors (must be an exact parse SyntaxError, both
    // modes) — the leading-zero-adjacent separator cluster + placement rules.
    ("sep-lol-0_0", Cover, "0_0;"),
    ("sep-lol-0_1", Cover, "0_1;"),
    ("sep-lol-0_7", Cover, "0_7;"),
    ("sep-nonoctal-0_8", Cover, "0_8;"),
    ("sep-nonoctal-0_9", Cover, "0_9;"),
    ("sep-nzd-leading-zero", Cover, "0_0123456789;"),
    ("sep-bigint-0_0n", Cover, "0_0n;"),
    ("sep-dds-dunder", Cover, "10__0123456789;"),
    ("sep-trailing", Cover, "1_;"),
    ("sep-oil-prefix", Cover, "0o_1;"),
    ("sep-oil-trailing", Cover, "0o1_;"),
    ("sep-hex-prefix", Cover, "0x_1;"),
    ("sep-dot-frac", Cover, "1._5;"),
    ("sep-exp", Cover, "1e_5;"),
    // Valid separators still lex + evaluate.
    ("sep-valid-dec", Cover, "if (1_000 !== 1000) throw 0;"),
    ("sep-valid-hex", Cover, "if (0xFF_FF !== 65535) throw 0;"),
    ("sep-valid-bigint", Cover, "if (1_0n !== 10n) throw 0;"),
    // JSON.stringify(BigInt): toJSON is consulted first; a still-BigInt throws.
    ("json-bigint-tojson", Cover, "BigInt.prototype.toJSON = function () { return this.toString(); }; if (JSON.stringify(0n) !== '\"0\"') throw 0;"),
    ("json-bigint-no-tojson", Cover, "try { JSON.stringify(1n); throw 1; } catch (e) { if (!(e instanceof TypeError)) throw 2; }"),
    ("json-bigint-tojson-receiver", Cover, "Object.defineProperty(BigInt.prototype, 'toJSON', { get() { 'use strict'; return () => typeof this; } }); if (JSON.stringify(1n) !== '\"bigint\"') throw 0;"),
];

#[test]
fn bigint_minis_vs_node() {
    let Ok(node) = std::env::var("TRUST_JS_NODE") else {
        eprintln!("SKIP bigint_minis_vs_node: set TRUST_JS_NODE to run");
        return;
    };
    let driver = driver_path();
    let tmp = tempfile::tempdir().expect("tempdir");
    let mut failures: Vec<String> = Vec::new();
    let mut covered = 0u64;
    let mut refused = 0u64;

    for (i, (name, expect, body)) in MINIS.iter().enumerate() {
        let sem = evaluate_case(&[], body);
        let sem_trace = match (sem, expect) {
            (SemOutcome::NoCoverage { reason }, Refuse) => {
                refused += 1;
                eprintln!("REFUSES (pinned) {name}: {reason}");
                continue;
            }
            (SemOutcome::NoCoverage { reason }, Cover) => {
                failures.push(format!("{name}: unexpected NoCoverage: {reason}"));
                continue;
            }
            (SemOutcome::Trace(_), Refuse) => {
                failures.push(format!("{name}: expected a refusal but produced a trace"));
                continue;
            }
            (SemOutcome::Trace(t), Cover) => t,
        };
        covered += 1;
        let node_trace = match run_node(&node, &driver, &tmp, i, body, "bare", true) {
            Ok(t) => t,
            Err(e) => {
                failures.push(format!("{name}: node run failed: {e}"));
                continue;
            }
        };
        if !traces_equal(&sem_trace, &node_trace) {
            failures.push(format!(
                "{name}: WRONG TRACE: {}",
                explain_divergence(&sem_trace, &node_trace)
                    .unwrap_or_else(|| "unlocalized".to_string())
            ));
        }
    }
    eprintln!("== bigint minis: covered {covered} / refused {refused} ==");
    assert!(
        failures.is_empty(),
        "bigint mini failures ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

#[test]
#[allow(clippy::too_many_lines)]
fn bigint_corpus_vs_node() {
    let Ok(node) = std::env::var("TRUST_JS_NODE") else {
        eprintln!("SKIP bigint_corpus_vs_node: set TRUST_JS_NODE to run");
        return;
    };
    let corpus = PathBuf::from(
        std::env::var("TRUST_JS262_CORPUS").unwrap_or_else(|_| DEFAULT_CORPUS.to_string()),
    );
    assert!(
        corpus.join("harness/assert.js").is_file(),
        "corpus harness not found under {}",
        corpus.display()
    );
    let driver = driver_path();
    let tmp = tempfile::tempdir().expect("tempdir");
    let mut failures: Vec<String> = Vec::new();
    let (mut covered, mut refused, mut equal) = (0u64, 0u64, 0u64);
    let mut per_dir: BTreeMap<&str, (u64, u64)> = BTreeMap::new();
    let mut include_cache: BTreeMap<String, String> = BTreeMap::new();
    let mut refusal_reasons: BTreeMap<String, (u64, String)> = BTreeMap::new();
    let mut case_no = 0usize;

    for (dir, cap) in BIGINT_DIRS {
        let files = collect_js_files(&corpus.join(dir), *cap);
        for path in files {
            let Ok(body) = std::fs::read_to_string(&path) else {
                continue;
            };
            let fm = parse_frontmatter(&body);
            if fm
                .flags
                .iter()
                .any(|f| f == "async" || f == "module" || f == "CanBlockIsRequired")
            {
                continue;
            }
            let raw = fm.flags.iter().any(|f| f == "raw");
            let modes: &[bool] = if fm.flags.iter().any(|f| f == "onlyStrict") {
                &[true]
            } else if raw || fm.flags.iter().any(|f| f == "noStrict") {
                &[false]
            } else {
                &[false, true]
            };
            let mut include_names: Vec<String> = if raw {
                Vec::new()
            } else {
                vec!["assert.js".to_string(), "sta.js".to_string()]
            };
            include_names.extend(fm.includes.iter().cloned());
            let mut include_srcs: Vec<String> = Vec::new();
            let mut include_paths: Vec<String> = Vec::new();
            let mut missing = false;
            for name in &include_names {
                let p = corpus.join("harness").join(name);
                if !p.is_file() {
                    missing = true;
                    break;
                }
                let src = include_cache
                    .entry(name.clone())
                    .or_insert_with(|| std::fs::read_to_string(&p).expect("read include"));
                include_srcs.push(src.clone());
                include_paths.push(p.display().to_string());
            }
            if missing {
                continue;
            }
            let rel = path.strip_prefix(&corpus).unwrap_or(&path).display().to_string();

            for &strict in modes {
                case_no += 1;
                let sem_body = if strict {
                    format!("\"use strict\";\n{body}")
                } else {
                    body.clone()
                };
                let inc_refs: Vec<&str> = include_srcs.iter().map(String::as_str).collect();
                let sem = evaluate_case_opts(&inc_refs, &sem_body, false);
                let sem_trace = match sem {
                    SemOutcome::Trace(t) => t,
                    SemOutcome::NoCoverage { reason } => {
                        refused += 1;
                        per_dir.entry(dir).or_default().1 += 1;
                        refusal_reasons
                            .entry(reason)
                            .or_insert_with(|| (0, rel.clone()))
                            .0 += 1;
                        continue;
                    }
                };
                covered += 1;
                per_dir.entry(dir).or_default().0 += 1;
                let mode = if strict { "strict" } else { "bare" };
                let node_trace = match run_node_inc(
                    &node,
                    &driver,
                    &tmp,
                    case_no,
                    &body,
                    &include_paths,
                    mode,
                    false,
                ) {
                    Ok(t) => t,
                    Err(e) => {
                        failures.push(format!("{rel} [{mode}]: node run failed: {e}"));
                        continue;
                    }
                };
                if traces_equal(&sem_trace, &node_trace) {
                    equal += 1;
                } else {
                    failures.push(format!(
                        "{rel} [{mode}]: WRONG TRACE: {}",
                        explain_divergence(&sem_trace, &node_trace)
                            .unwrap_or_else(|| "unlocalized".to_string())
                    ));
                }
            }
        }
    }

    eprintln!("== bigint corpus: covered {covered} (equal {equal}) / refused {refused} ==");
    for (dir, (c, r)) in &per_dir {
        eprintln!("  {dir}: covered {c} refused {r}");
    }
    let mut reasons: Vec<(u64, String, String)> = refusal_reasons
        .into_iter()
        .map(|(k, (n, sample))| (n, k, sample))
        .collect();
    reasons.sort_by(|a, b| b.0.cmp(&a.0));
    eprintln!("== top refusal reasons ==");
    for (n, reason, sample) in reasons.iter().take(40) {
        eprintln!("  {n} x {reason} (e.g. {sample})");
    }
    assert!(
        failures.is_empty(),
        "bigint corpus WRONG traces ({}):\n{}",
        failures.len(),
        failures.iter().take(80).cloned().collect::<Vec<_>>().join("\n")
    );
}

// ---------------------------------------------------------------------------
// helpers
// ---------------------------------------------------------------------------

fn driver_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crates dir")
        .join("trust-js-trace/js/trace_driver.mjs")
}

fn run_node(
    node: &str,
    driver: &Path,
    tmp: &tempfile::TempDir,
    i: usize,
    body: &str,
    mode: &str,
    witness: bool,
) -> Result<trust_js_trace::ObservableTrace, String> {
    run_node_inc(node, driver, tmp, i, body, &[], mode, witness)
}

#[allow(clippy::too_many_arguments)]
fn run_node_inc(
    node: &str,
    driver: &Path,
    tmp: &tempfile::TempDir,
    i: usize,
    body: &str,
    includes: &[String],
    mode: &str,
    witness: bool,
) -> Result<trust_js_trace::ObservableTrace, String> {
    let body_path = tmp.path().join(format!("bi-{i}.body.js"));
    std::fs::write(&body_path, body).map_err(|e| e.to_string())?;
    let manifest = serde_json::json!({
        "completion_witness": witness,
        "includes": includes,
        "source": body_path.display().to_string(),
        "mode": mode,
        "kind": "script",
    });
    let manifest_path = tmp.path().join(format!("bi-{i}.manifest.json"));
    let mut mf = std::fs::File::create(&manifest_path).map_err(|e| e.to_string())?;
    mf.write_all(manifest.to_string().as_bytes())
        .map_err(|e| e.to_string())?;
    drop(mf);
    let out = Command::new(node)
        .arg(driver)
        .arg(&manifest_path)
        .env("TZ", "UTC")
        .env("LANG", "C")
        .env("LC_ALL", "C")
        .output()
        .map_err(|e| e.to_string())?;
    extract_trace(&out.stdout).map_err(|e| {
        format!(
            "{e} (stderr: {})",
            String::from_utf8_lossy(&out.stderr)
        )
    })
}

struct Frontmatter {
    includes: Vec<String>,
    flags: Vec<String>,
}

fn parse_frontmatter(body: &str) -> Frontmatter {
    let fm = body
        .split_once("/*---")
        .and_then(|(_, rest)| rest.split_once("---*/"))
        .map_or("", |(fm, _)| fm);
    let mut includes = Vec::new();
    let mut flags = Vec::new();
    let mut lines = fm.lines().peekable();
    while let Some(line) = lines.next() {
        let t = line.trim_start();
        if let Some(rest) = t.strip_prefix("includes:") {
            let rest = rest.trim();
            if let Some(inner) = rest.strip_prefix('[') {
                includes.extend(
                    inner
                        .trim_end_matches(']')
                        .split(',')
                        .map(|s| s.trim().to_string())
                        .filter(|s| !s.is_empty()),
                );
            } else {
                while let Some(next) = lines.peek() {
                    let nt = next.trim_start();
                    if let Some(item) = nt.strip_prefix("- ") {
                        includes.push(item.trim().to_string());
                        lines.next();
                    } else {
                        break;
                    }
                }
            }
        } else if let Some(rest) = t.strip_prefix("flags:") {
            if let Some(inner) = rest.trim().strip_prefix('[') {
                flags.extend(
                    inner
                        .trim_end_matches(']')
                        .split(',')
                        .map(|s| s.trim().to_string())
                        .filter(|s| !s.is_empty()),
                );
            }
        }
    }
    Frontmatter { includes, flags }
}

fn collect_js_files(dir: &Path, cap: usize) -> Vec<PathBuf> {
    let mut files: Vec<PathBuf> = Vec::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        let Ok(rd) = std::fs::read_dir(&d) else {
            continue;
        };
        let mut entries: Vec<PathBuf> = rd.filter_map(|e| e.ok().map(|e| e.path())).collect();
        entries.sort();
        for p in entries {
            if p.is_dir() {
                stack.push(p);
            } else if p.extension().is_some_and(|e| e == "js")
                && !p
                    .file_name()
                    .is_some_and(|n| n.to_string_lossy().ends_with("_FIXTURE.js"))
            {
                files.push(p);
            }
        }
    }
    files.sort();
    files.truncate(cap);
    files
}
