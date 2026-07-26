// Empirical render-fidelity check (closes the audit gap).
//
// `check_fidelity` proves the IR interpreter `eval_ir` bit-equals the interp
// oracle over the corpus — but it NEVER executes the rendered `rust_source`
// string. So the emitted Rust artifact's equivalence has, until now, rested on
// `render_rust` faithfully rendering the same IR that `eval_ir` walks: trusted
// by construction, not checked. A precedence / associativity / literal defect in
// `render_rust` would yield a WRONG `rust_source` that the ledger would still
// accept (the ledger only ever looks at `eval_ir`).
//
// This module closes that gap EMPIRICALLY, using the REAL rustc as the oracle
// for "what the rendered Rust means": for a curated set of precedence-sensitive
// positive lowerings we compile the ACTUAL `rust_source` with `rustc -O`, run
// it over a fixed edge-case sample corpus, and assert its `f64::to_bits()`
// output equals `eval_ir` on the same tuples, bit-for-bit. If the compiled Rust
// and `eval_ir` ever disagree that is a REAL render bug and the test fails
// loudly with the offending case; the ONLY sound difference tolerated is a
// NaN-payload difference (JS collapses every NaN payload — `same_js_number`
// treats all NaN as one number), which is documented at the comparison site.
//
// If rustc cannot be found or a trivial probe program will not build, the
// environment has no usable toolchain for this check and the test SKIPS (prints
// a notice, returns Ok) rather than failing on a missing toolchain.

use std::path::{Path, PathBuf};
use std::process::Command;

use super::*;

/// The curated precedence / associativity / branch stress corpus. Every case
/// must lower+verify; the point is to catch a `render_rust` defect that changes
/// meaning (dropped parens, wrong associativity, a mis-rendered literal).
const CASES: &[&str] = &[
    // Left-associativity of `-` (`(a-b)-c`), and the parenthesized right form.
    "function s(a,b,c){return a-b-c}",
    "function sr(a,b,c){return a-(b-c)}",
    // Left-associativity of `/`, and the parenthesized right form.
    "function d(a,b,c){return a/b/c}",
    "function dr(a,b,c){return a/(b/c)}",
    // `*` binds tighter than `-`; forcing the `-` first needs parens.
    "function m(a,b,c){return a-b*c}",
    "function mp(a,b,c){return (a-b)*c}",
    // Unary minus over a product, and double negation (must never emit `--`).
    "function ng(a,b){return -(a*b)}",
    "function nn(a){return -(-a)}",
    // Left-associativity of `%`.
    "function rem(a,b,c){return a%b%c}",
    // Conditionals: max, a nested ternary, and a compound-condition clamp.
    "function mx(a,b){return a>b?a:b}",
    "function sgn(a){return a>0?1:(a<0?-1:0)}",
    "function cl(x,lo,hi){return x<lo?lo:(x>hi?hi:x)}",
    // Local `const`/`let` bindings: the rendered Rust now carries typed `let`s, so
    // rustc also proves those `l{slot}` bindings mean what `eval_func` computes.
    // Numeric locals (difference of squares), a boolean local feeding a ternary,
    // and a dependency chain of locals.
    "function g(a,b){const s=a+b;const d=a-b;return s*d;}",
    "function p(a,b){const big=a>b;return big?a:b;}",
    "function c(a){const x=a+1;const y=x+1;const z=y+1;return z;}",
    // MULTIPLE top-level functions + non-recursive CALLS between them: the whole
    // rendered module (helpers first, entry last) is compiled as a set of free
    // `fn`s, so rustc also proves the `name(a0, ...)` call sites and the entry's
    // composition mean what `eval_module` computes. Sum of squares via a helper,
    // and nested calls (max-of-3) — a call inside a call's argument.
    "function sq(x){return x*x}function f(a,b){return sq(a)+sq(b)}",
    "function mx(a,b){return a>b?a:b}function m3(a,b,c){return mx(mx(a,b),c);}",
    // `Math.*` builtins (increment 5): the rendered module now carries direct
    // `f64` method calls (abs/floor/ceil/trunc/sqrt) and prepended `__js_math_*`
    // JS-semantics helpers (sign/round/min/max). rustc compiles the WHOLE module
    // (helpers + entry) and proves it means what `eval_module` computes, over a
    // corpus that includes NaN, ±0, and ±Inf — so the trap ops (signed zero, NaN
    // propagation, half-to-+Inf) are checked against real rustc, not just asserted.
    // (Math.pow is NOT here: it is a transcendental and REFUSES — never shipped, so
    // there is nothing to compile-check.)
    "function mabs(a){return Math.abs(a)}",
    "function mfloor(a){return Math.floor(a)}",
    "function mceil(a){return Math.ceil(a)}",
    "function mtrunc(a){return Math.trunc(a)}",
    "function msqrt(a){return Math.sqrt(a)}",
    "function msign(a){return Math.sign(a)}",
    "function mround(a){return Math.round(a)}",
    "function mmin(a,b){return Math.min(a,b)}",
    "function mmax(a,b){return Math.max(a,b)}",
    "function mclamp(x,lo,hi){return Math.min(Math.max(x,lo),hi)}",
    // JS bitwise ops (increment 8): the rendered module now carries the prepended
    // `__js_to_int32` / `__js_to_uint32` (ToInt32/ToUint32) helpers and the
    // self-parenthesized `(( … ) as f64)` casts. rustc compiles the WHOLE module and
    // proves it means what `eval_module` computes over a corpus that includes NaN,
    // ±Inf, ±0, and f64::MAX — so ToInt32's modular reduction (incl. the large-value
    // fmod path), the unsigned `>>>`, the shift-count mask, and `~` are all checked
    // against real rustc, not just asserted. These are EXACT integer functions, so
    // they SHIP (contrast Math.pow, a transcendental, which refuses).
    "function orr(a,b){return a|b}",
    "function andb(a,b){return a&b}",
    "function xorb(a,b){return a^b}",
    "function truncise(a){return a|0}", // the x|0 int32-truncate idiom
    "function ushr(a){return a>>>0}",   // unsigned coercion (-1 -> 4294967295)
    "function shl(a,b){return a<<b}",   // shift count mod 32 (1<<32 -> 1)
    "function sshr(a){return a>>1}",    // arithmetic (signed) shift
    "function notb(a){return ~a}",      // bitwise NOT (~0 -> -1)
    "function andxor(a,b,c){return (a&b)^c}",
    "function hashy(a,b){ const h = (a<<5) - a + b; return h | 0; }",
];

/// Curated ARRAY-FOLD cases (increment 6): the whole rendered `&[f64]` module
/// (scalar helpers + the fold, plus any `__js_math_*` helpers) is compiled by the
/// real rustc and its output matched to `eval_fold` over the array corpus,
/// bit-for-bit — so rustc proves the `let mut` accumulator, the `for &x in arr`
/// reduction, the scalar params, a Math step, and a helper call all mean what
/// `eval_fold` computes, over a corpus spanning the empty / NaN / ±0 / ±Inf arrays.
const FOLD_CASES: &[&str] = &[
    "function sum(arr){ let s=0; for(const x of arr){ s=s+x; } return s; }",
    "function prod(arr){ let p=1; for(const x of arr){ p = p*x; } return p; }",
    "function sumsq(arr){ let s=0; for(const x of arr){ s = s + x*x; } return s; }",
    // A scalar param in the step.
    "function axpy(arr,k){ let s=0; for(const x of arr){ s = s + k*x; } return s; }",
    // A Math step (Math.max is a trap helper; Math.abs a direct method).
    "function maxabs(arr){ let m=0; for(const x of arr){ m = Math.max(m, Math.abs(x)); } return m; }",
    // The fold entry calls a strictly-earlier scalar helper in the step.
    "function dbl(x){return x*2} function f(arr){ let s=0; for(const x of arr){ s = s + dbl(x); } return s; }",
];

/// A deterministic edge-case sample corpus for `arity` parameters, chosen so
/// that (a) EVERY parameter position varies across signs/magnitudes/specials
/// (so an associativity defect like `(a-b)-c` vs `a-(b-c)` is exposed on values
/// where float `-` does not reassociate, e.g. `f64::MAX`/`0.1`), and (b) every
/// ternary threshold and NaN-unordered branch is crossed. It reuses the crate's
/// pinned edge values ([`crate::fidelity`]) and takes a full cartesian product of a small
/// per-arity list, so all parameters are exercised together.
fn sample_tuples(arity: usize) -> Vec<Vec<f64>> {
    let list: Vec<f64> = match arity {
        0 => return vec![Vec::new()],
        1 => crate::fidelity::pin().base_samples().to_vec(),
        2 => vec![
            0.0,
            -0.0,
            1.0,
            -1.0,
            f64::NAN,
            f64::INFINITY,
            f64::NEG_INFINITY,
            3.0,
            0.1,
            100.0,
            f64::MAX,
        ],
        _ => vec![0.0, 1.0, -1.0, f64::NAN, f64::INFINITY, 3.0, 0.1, f64::MAX],
    };
    let n = list.len();
    let total = n.checked_pow(arity as u32).expect("sample product fits usize");
    let mut out = Vec::with_capacity(total);
    for i in 0..total {
        let mut t = Vec::with_capacity(arity);
        let mut r = i;
        for _ in 0..arity {
            t.push(list[r % n]);
            r /= n;
        }
        out.push(t);
    }
    out
}

/// Build a standalone Rust program: the rendered module (one or more free `fn`s,
/// helpers first and the entry last), plus a `main` that calls the ENTRY (`name`)
/// on each sample tuple and prints the result's `.to_bits()` (one per line).
/// Sample arguments are rendered with the crate's own bit-exact `render_f64_lit`
/// (finite values round-trip through Rust's shortest-Debug form; specials use
/// the `f64::` constants), so the compiled program sees the identical f64 bits
/// that `eval_ir` sees.
fn program_source(rust_source: &str, name: &str, tuples: &[Vec<f64>]) -> String {
    let mut s = String::with_capacity(rust_source.len() + tuples.len() * 48);
    // A dead `const`/`let` binding (impossible for the curated cases, but sound to
    // allow) would warn, not error — but suppress unused warnings so no warning
    // can ever be mistaken for a render bug.
    s.push_str("#![allow(unused)]\n");
    s.push_str(rust_source);
    s.push_str("\n\nfn main() {\n");
    for t in tuples {
        let args = t.iter().map(|v| render_f64_lit(*v)).collect::<Vec<_>>().join(", ");
        s.push_str(&format!("    println!(\"{{}}\", {name}({args}).to_bits());\n"));
    }
    s.push_str("}\n");
    s
}

/// Build a standalone program from a rendered ARRAY-FOLD module + a `main` that
/// calls the fold entry `name` on each (array, scalars) tuple and prints the
/// result's `.to_bits()`. The array is a Rust slice literal `&[<f64 lits>]` and the
/// scalars are trailing f64 literals, all via the crate's bit-exact
/// `render_f64_lit`, so the compiled program sees the identical f64 bits `eval_fold`
/// sees. The empty array renders `&[]` (inferred as `&[f64]` from the signature).
fn fold_program_source(rust_source: &str, name: &str, corpus: &[(Vec<f64>, Vec<f64>)]) -> String {
    let mut s = String::with_capacity(rust_source.len() + corpus.len() * 48);
    s.push_str("#![allow(unused)]\n");
    s.push_str(rust_source);
    s.push_str("\n\nfn main() {\n");
    for (array, scalars) in corpus {
        let arr_lit = array.iter().map(|v| render_f64_lit(*v)).collect::<Vec<_>>().join(", ");
        let mut args = format!("&[{arr_lit}]");
        for sv in scalars {
            args.push_str(&format!(", {}", render_f64_lit(*sv)));
        }
        s.push_str(&format!("    println!(\"{{}}\", {name}({args}).to_bits());\n"));
    }
    s.push_str("}\n");
    s
}

/// `RUSTC` if set (cargo sets it to the compiler it used), else plain `rustc`.
fn rustc_bin() -> String {
    std::env::var("RUSTC").unwrap_or_else(|_| "rustc".to_string())
}

fn unique_tempdir() -> PathBuf {
    use std::time::{SystemTime, UNIX_EPOCH};
    let nanos = SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_nanos()).unwrap_or(0);
    let pid = std::process::id();
    std::env::temp_dir().join(format!("trust-js-autoform-cc-{pid}-{nanos}"))
}

/// Compile `src_path` with `rustc -O` to `bin_path`; returns the process output
/// (or the spawn error, which the caller treats as "toolchain unavailable").
fn rustc_compile(
    rustc: &str,
    src_path: &Path,
    bin_path: &Path,
) -> std::io::Result<std::process::Output> {
    Command::new(rustc).arg("-O").arg(src_path).arg("-o").arg(bin_path).output()
}

#[test]
fn rendered_rust_matches_eval_ir_via_real_rustc() {
    let rustc = rustc_bin();
    let dir = unique_tempdir();
    if let Err(e) = std::fs::create_dir_all(&dir) {
        eprintln!("[compile_check] SKIP: cannot create temp dir {dir:?}: {e}");
        return;
    }

    // Toolchain probe. A trivial standalone program must build AND run; if it
    // cannot, THIS environment has no usable rustc for the check — SKIP (never
    // fail on a missing toolchain). Only AFTER the probe passes does a later
    // per-case compile failure count as a real render bug.
    let probe_src = dir.join("probe.rs");
    let probe_bin = dir.join(format!("probe{}", std::env::consts::EXE_SUFFIX));
    if std::fs::write(&probe_src, "fn main() { println!(\"{}\", (1.0f64).to_bits()); }").is_err() {
        eprintln!("[compile_check] SKIP: cannot write probe source under {dir:?}");
        let _ = std::fs::remove_dir_all(&dir);
        return;
    }
    match rustc_compile(&rustc, &probe_src, &probe_bin) {
        Err(e) => {
            eprintln!("[compile_check] SKIP: cannot spawn rustc {rustc:?}: {e}");
            let _ = std::fs::remove_dir_all(&dir);
            return;
        }
        Ok(out) if !out.status.success() => {
            eprintln!(
                "[compile_check] SKIP: rustc {rustc:?} cannot build a trivial program \
                 (toolchain unusable here):\n{}",
                String::from_utf8_lossy(&out.stderr)
            );
            let _ = std::fs::remove_dir_all(&dir);
            return;
        }
        Ok(_) => {}
    }
    match Command::new(&probe_bin).output() {
        Ok(out) if out.status.success() => {
            assert_eq!(
                String::from_utf8_lossy(&out.stdout).trim(),
                1.0f64.to_bits().to_string(),
                "probe program output unexpected"
            );
        }
        other => {
            eprintln!("[compile_check] SKIP: probe binary did not run cleanly: {other:?}");
            let _ = std::fs::remove_dir_all(&dir);
            return;
        }
    }

    let mut compiled = 0usize;
    let mut total_rows = 0usize;
    let mut all_nan_only_diffs = 0usize;
    for js in CASES {
        // Public entry point (as the audit requires): get the real artifact.
        let v = match lower_and_verify(js) {
            Ok(v) => v,
            Err(e) => panic!("curated case {js:?} must lower+verify, got refusal: {e:?}"),
        };
        // The ENTRY is the last-declared function; drive it (all helpers are in
        // scope in the rendered module). Take its name/arity from the function
        // table, NOT by parsing the source — for a multi-fn module the FIRST `fn`
        // in the string is a helper, not the entry.
        let entry = &v.functions[v.entry];
        let name = entry.name.clone();
        let arity = entry.arity;
        let tuples = sample_tuples(arity);
        let src = program_source(&v.rust_source, &name, &tuples);

        let src_path = dir.join(format!("case_{name}.rs"));
        let bin_path = dir.join(format!("case_{name}{}", std::env::consts::EXE_SUFFIX));
        std::fs::write(&src_path, &src).expect("write case source");

        // The probe already proved rustc builds standalone programs, so any
        // failure HERE means render_rust emitted Rust that does not compile — a
        // real render bug. Fail loudly with the rendered source and stderr.
        let out = rustc_compile(&rustc, &src_path, &bin_path)
            .expect("rustc probe succeeded, so spawning rustc must work here");
        assert!(
            out.status.success(),
            "REAL RENDER BUG: render_rust emitted Rust that does NOT COMPILE for {js:?}\n\
             --- rendered rust_source ---\n{}\n--- rustc stderr ---\n{}",
            v.rust_source,
            String::from_utf8_lossy(&out.stderr)
        );

        let run = Command::new(&bin_path).output().expect("run compiled program");
        assert!(
            run.status.success(),
            "compiled program for {js:?} exited nonzero:\n{}",
            String::from_utf8_lossy(&run.stderr)
        );
        let stdout = String::from_utf8_lossy(&run.stdout);
        let lines: Vec<&str> = stdout.lines().collect();
        assert_eq!(
            lines.len(),
            tuples.len(),
            "compiled program for {js:?} printed {} lines, expected {}",
            lines.len(),
            tuples.len()
        );

        for (t, line) in tuples.iter().zip(&lines) {
            let compiled_bits: u64 = line
                .trim()
                .parse()
                .unwrap_or_else(|e| panic!("unparseable bits line {line:?} for {js:?}: {e}"));
            let eval_bits = eval_module(&v.functions, v.entry, t).to_bits();
            if compiled_bits != eval_bits {
                // The ONLY sound difference: both results are NaN. JS collapses
                // every NaN payload to one observable Number, and `same_js_number`
                // treats all NaN as equal; a NaN-payload-only diff between the
                // compiled Rust and eval_ir is therefore NOT a render bug. Any
                // other bit difference IS a real render/eval disagreement.
                let both_nan =
                    f64::from_bits(compiled_bits).is_nan() && f64::from_bits(eval_bits).is_nan();
                assert!(
                    both_nan,
                    "REAL RENDER BUG for {js:?} on args {t:?}:\n  \
                     compiled rustc output = {} (bits {compiled_bits})\n  \
                     eval_func             = {} (bits {eval_bits})\n  \
                     rendered rust_source  = {}",
                    f64::from_bits(compiled_bits),
                    f64::from_bits(eval_bits),
                    v.rust_source,
                );
                all_nan_only_diffs += 1;
            }
        }
        compiled += 1;
        total_rows += tuples.len();
    }

    // ARRAY-FOLD cases (increment 6): compile the rendered `&[f64]` fold module and
    // match its output to `eval_fold` over the (array × scalar) corpus, bit-for-bit.
    let mut fold_compiled = 0usize;
    let mut fold_rows = 0usize;
    for js in FOLD_CASES {
        let v = match lower_and_verify(js) {
            Ok(v) => v,
            Err(e) => panic!("curated fold case {js:?} must lower+verify, got refusal: {e:?}"),
        };
        let fold = v.fold.clone().expect("a curated fold case must lower to a fold entry");
        let corpus = build_fold_corpus(fold.scalar_arity);
        let src = fold_program_source(&v.rust_source, &fold.name, &corpus);

        let src_path = dir.join(format!("fold_{}.rs", fold.name));
        let bin_path = dir.join(format!("fold_{}{}", fold.name, std::env::consts::EXE_SUFFIX));
        std::fs::write(&src_path, &src).expect("write fold case source");

        let out = rustc_compile(&rustc, &src_path, &bin_path)
            .expect("rustc probe succeeded, so spawning rustc must work here");
        assert!(
            out.status.success(),
            "REAL RENDER BUG: render_fold_module emitted Rust that does NOT COMPILE for {js:?}\n\
             --- rendered rust_source ---\n{}\n--- rustc stderr ---\n{}",
            v.rust_source,
            String::from_utf8_lossy(&out.stderr)
        );

        let run = Command::new(&bin_path).output().expect("run compiled fold program");
        assert!(
            run.status.success(),
            "compiled fold program for {js:?} exited nonzero:\n{}",
            String::from_utf8_lossy(&run.stderr)
        );
        let stdout = String::from_utf8_lossy(&run.stdout);
        let lines: Vec<&str> = stdout.lines().collect();
        assert_eq!(
            lines.len(),
            corpus.len(),
            "fold program for {js:?} printed {} lines, expected {}",
            lines.len(),
            corpus.len()
        );

        for ((array, scalars), line) in corpus.iter().zip(&lines) {
            let compiled_bits: u64 = line
                .trim()
                .parse()
                .unwrap_or_else(|e| panic!("unparseable bits line {line:?} for {js:?}: {e}"));
            let eval_bits = eval_fold(&fold, &v.functions, array, scalars).to_bits();
            if compiled_bits != eval_bits {
                // The only sound difference: both NaN (JS collapses NaN payloads).
                let both_nan =
                    f64::from_bits(compiled_bits).is_nan() && f64::from_bits(eval_bits).is_nan();
                assert!(
                    both_nan,
                    "REAL RENDER BUG for fold {js:?} on array {array:?} scalars {scalars:?}:\n  \
                     compiled rustc output = {} (bits {compiled_bits})\n  \
                     eval_fold             = {} (bits {eval_bits})\n  \
                     rendered rust_source  = {}",
                    f64::from_bits(compiled_bits),
                    f64::from_bits(eval_bits),
                    v.rust_source,
                );
                all_nan_only_diffs += 1;
            }
        }
        fold_compiled += 1;
        fold_rows += corpus.len();
    }

    let _ = std::fs::remove_dir_all(&dir);

    assert_eq!(compiled, CASES.len(), "every curated scalar case must compile + match");
    assert_eq!(fold_compiled, FOLD_CASES.len(), "every curated fold case must compile + match");
    eprintln!(
        "[compile_check] OK: compiled + ran {compiled} scalar programs ({total_rows} rows) + \
         {fold_compiled} fold programs ({fold_rows} rows) via real rustc ({rustc:?}); all \
         bit-equal to eval ({all_nan_only_diffs} rows equal only up to NaN payload, sound)."
    );
}
