// trust-js-interp: the TrustJS tier-0 faithful interpreter — M1 D2/D4
// (see Cargo.toml). The fourth differential head: it evaluates a test262
// case (harness includes + body) over trust-js-parse's AST against the
// trust-js-value realm, and emits either the exact ObservableTrace the
// in-JS trace driver would emit on a real engine, or a sound NoCoverage
// refusal. Slices S1a (expressions/statements/functions) and S1b (objects,
// arrays, the property machinery, Symbol, basic classes) are live. ZERO
// wrong traces is the bar: every unimplemented syntax, operation, or
// intrinsic surface refuses — never a guessed error, never a mis-read
// `undefined` — and engine-consensus deviations from the spec text are
// either matched (where Node and Bun agree) or refused (where they don't).
//
// Independence: this crate re-derives the S1a semantics from ECMA-262 and
// never depends on trust-js-sem (the reference head it will be judged
// against).
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

mod builtins;
mod builtins_array;
mod builtins_collections;
mod builtins_date;
mod builtins_json;
mod builtins_misc;
mod builtins_object;
mod builtins_regexp;
mod builtins_string;
mod builtins_typedarray;
mod builtins_uri;
mod builtins_weak;
mod class_eval;
mod destr;
mod dispose;
mod eval;
mod expr;
mod funcs;
mod generators;
mod host;
mod interp;
mod iterhelp;
mod iterobj;
mod literals;
mod module_lower;
mod ops;
mod private;
mod project;
mod promise;
mod props;
mod proxy;

pub use project::escape_units;

use std::collections::HashMap;

use interp::{Abrupt, Interp};
use trust_js_parse::ast::{ExportDecl, Stmt};
use trust_js_parse::{parse_module, parse_script, ParseOutcome, Program};
use trust_js_trace::{
    Completion, ObservableTrace, ProjectionCaps, ThrownProjection, SCHEMA_VERSION,
};

/// A sibling-module resolver: given the (canonical) key of the importing
/// module and a specifier as written, return `Ok((resolved_key, source))` or a
/// refusal reason. The harness supplies this — it owns disk access and the
/// relative-path / bounds policy; the linker owns the graph algorithm and the
/// sound-subset guards. Boxed `Send` so the panic-isolated wide-stack worker
/// thread can own it. See [`evaluate_module_graph`].
pub type ModuleResolver = Box<dyn Fn(&str, &str) -> Result<(String, String), String> + Send>;

/// The head verdict for one case: a trace, or a sound refusal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InterpOutcome {
    Trace(ObservableTrace),
    /// The case uses syntax or semantics outside the implemented S1a slice.
    /// Sound: never a false divergence; counted (audited) by the harness.
    NoCoverage { reason: String },
}

/// The projection caps the driver declares; ours are identical by
/// construction.
#[must_use]
pub fn projection_caps() -> ProjectionCaps {
    ProjectionCaps {
        depth: 8,
        keys: 64,
        nodes: 4096,
        string: 4096,
        timers: 10_000,
    }
}

/// The thrown projection a conforming engine produces for a parse-time
/// SyntaxError (constructor identity and `.name` only — never message text).
fn syntax_error_thrown() -> ThrownProjection {
    ThrownProjection::Error {
        ctor: Some("Error:SyntaxError".to_string()),
        name: Some("SyntaxError".to_string()),
        ctor_name: Some("SyntaxError".to_string()),
    }
}

/// Evaluate one assembled case: `includes` are the SOURCE TEXTS of the
/// harness includes (assert.js, sta.js, ...) in driver order, evaluated
/// non-strict in the shared realm exactly like the driver's indirect eval;
/// `body` is the pristine test body; `strict_prefix` prepends
/// `"use strict";\n` exactly as the driver's strict mode does. The completion
/// witness is OFF (`Completion::Normal { v: None }`), matching the driver
/// default the calibrated corpus lanes run with.
#[must_use]
pub fn evaluate_case(includes: &[&str], body: &str, strict_prefix: bool) -> InterpOutcome {
    evaluate_case_opts(includes, body, strict_prefix, false)
}

/// Like [`evaluate_case`], with the completion witness explicit (the witness
/// is an opt-in observable — see trust-js-trace's calibration ruling).
#[must_use]
pub fn evaluate_case_opts(
    includes: &[&str],
    body: &str,
    strict_prefix: bool,
    completion_witness: bool,
) -> InterpOutcome {
    run_case_on_thread(includes, body, strict_prefix, completion_witness, false)
}

/// Evaluate a case in the MODULE goal (the S-module slice): the harness includes
/// are Script-goal sloppy scripts (exactly as the driver evals them), then the
/// body is parsed with [`parse_module`]. A module parse / Static-Semantics early
/// error yields the same SyntaxError-throw trace an engine produces when
/// `import()`-ing the module (covering the negative:parse module tests); a
/// well-formed module is a SOUND `NoCoverage` refusal — module LINKING and
/// EVALUATION (ResolveExport, the module graph) are not yet implemented, so the
/// faithful tier never fabricates a positive-module trace (zero-wrong-traces).
#[must_use]
pub fn evaluate_module(includes: &[&str], body: &str) -> InterpOutcome {
    // Modules are always strict; parse_module bakes that in (no `"use strict";`
    // prefix, which would shift positions).
    run_case_on_thread(includes, body, false, false, true)
}

/// Shared wide-stack, panic-isolated case runner for the script and module goals.
fn run_case_on_thread(
    includes: &[&str],
    body: &str,
    strict_prefix: bool,
    completion_witness: bool,
    module_goal: bool,
) -> InterpOutcome {
    // Totality belt: the interpreter is written panic-free, but a panic must
    // never surface as anything but a sound refusal. Each case runs on a
    // dedicated wide-stack thread so the (capped) evaluation depth can never
    // overflow a caller's thread stack; the interpreter's own depth caps trip
    // long before this stack does.
    let includes: Vec<String> = includes.iter().map(|s| (*s).to_string()).collect();
    let body = body.to_string();
    let spawned = std::thread::Builder::new()
        .name("trust-js-interp-case".to_string())
        .stack_size(32 * 1024 * 1024)
        .spawn(move || {
            let refs: Vec<&str> = includes.iter().map(String::as_str).collect();
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                evaluate_case_inner(&refs, &body, strict_prefix, completion_witness, module_goal)
            }));
            result.unwrap_or_else(|_| InterpOutcome::NoCoverage {
                reason: "internal interpreter panic (refused, not judged)".to_string(),
            })
        });
    match spawned {
        Ok(handle) => handle.join().unwrap_or_else(|_| InterpOutcome::NoCoverage {
            reason: "internal interpreter panic (refused, not judged)".to_string(),
        }),
        Err(e) => InterpOutcome::NoCoverage {
            reason: format!("case thread spawn failed: {e}"),
        },
    }
}

/// Does the source carry an `await using` declaration head (`await` followed,
/// with no line terminator, by the `using` keyword)? Used only to turn the
/// parser's spurious early error on `for (await using …; …; …)` into a sound
/// refusal rather than a fabricated SyntaxError trace. `await using` as a plain
/// statement parses and is refused downstream, so this scan is consulted only
/// on an already-failed body parse; a stray match there costs a little coverage
/// (a refusal) but can never produce a wrong trace.
fn source_has_await_using(src: &str) -> bool {
    let b = src.as_bytes();
    let is_ident = |c: u8| c == b'_' || c == b'$' || c.is_ascii_alphanumeric();
    let mut from = 0;
    while let Some(rel) = src[from..].find("await") {
        let a = from + rel;
        let a_end = a + 5;
        from = a_end;
        // `await` must stand alone as a keyword (word boundaries).
        if a > 0 && is_ident(b[a - 1]) {
            continue;
        }
        if a_end < b.len() && is_ident(b[a_end]) {
            continue;
        }
        // `[no LineTerminator here]`: only spaces/tabs may separate the tokens.
        let mut j = a_end;
        while j < b.len() && (b[j] == b' ' || b[j] == b'\t') {
            j += 1;
        }
        if b[j..].starts_with(b"using") {
            let u_end = j + 5;
            if u_end >= b.len() || !is_ident(b[u_end]) {
                return true;
            }
        }
    }
    false
}

fn evaluate_case_inner(
    includes: &[&str],
    body: &str,
    strict_prefix: bool,
    completion_witness: bool,
    module_goal: bool,
) -> InterpOutcome {
    let mut it = Interp::new();
    // Every parsed Program stays alive for the whole case: the interpreter's
    // address-keyed AST caches (closures, template-site identity) rely on it.
    let mut programs: Vec<Program> = Vec::new();

    if let Err(outcome) = run_harness_includes(&mut it, includes, &mut programs) {
        return outcome;
    }

    let assembled: String;
    let body_src: &str = if strict_prefix {
        assembled = format!("\"use strict\";\n{body}");
        &assembled
    } else {
        body
    };

    // MODULE goal (S-module): parse the body as a Module. A parse / early error
    // is the SyntaxError an engine throws when `import()`-ing the module — the
    // SAME trace the script goal emits for a body early error (events from the
    // already-run harness includes, then a SyntaxError throw). A well-formed
    // module is LOWERED to an equivalent strict Script when it is import-free
    // and uses no module-only construct (module_lower::lower); the lowered
    // program runs through the SAME body path as the script goal, so equivalent
    // programs produce byte-identical trace structure. A module the lowering
    // cannot prove equivalent is a sound refusal — the faithful tier never
    // fabricates a positive-module trace (zero-wrong-traces).
    if module_goal {
        return match parse_module(body_src) {
            ParseOutcome::EarlyError { .. } => InterpOutcome::Trace(ObservableTrace {
                schema: SCHEMA_VERSION.to_string(),
                caps: Some(projection_caps()),
                events: std::mem::take(&mut it.events),
                completion: Completion::Throw { v: syntax_error_thrown(), phase: None },
            }),
            ParseOutcome::Script(prog) => match module_lower::lower(prog) {
                Ok(script_prog) => {
                    programs.push(script_prog);
                    finish_body_run(
                        &mut it,
                        programs.last().expect("just pushed"),
                        completion_witness,
                    )
                }
                Err(reason) => InterpOutcome::NoCoverage { reason },
            },
            ParseOutcome::Unsupported { reason } => InterpOutcome::NoCoverage {
                reason: format!("module body parse: {reason}"),
            },
        };
    }

    let body_prog = match parse_script(body_src, false) {
        ParseOutcome::Script(p) => p,
        ParseOutcome::EarlyError { .. } => {
            // The parser accepts an `await using` declaration as a statement
            // (the interpreter then soundly refuses the out-of-slice explicit
            // resource declaration) but rejects it inside a C-style `for (…;…;…)`
            // head as an early SyntaxError — yet the engines accept that valid
            // syntax and run it. Never emit that spurious SyntaxError: a body
            // that carries an `await using` declaration and fails to parse is an
            // out-of-slice refusal, not a fabricated early error.
            if source_has_await_using(body_src) {
                return InterpOutcome::NoCoverage {
                    reason: "await using declaration in a for-statement head \
                             (explicit resource management, out of slice)"
                        .to_string(),
                };
            }
            // A fully-specified early error: the engines raise SyntaxError
            // while parsing the body, before evaluating any of it.
            return InterpOutcome::Trace(ObservableTrace {
                schema: SCHEMA_VERSION.to_string(),
                caps: Some(projection_caps()),
                events: it.events,
                completion: Completion::Throw {
                    v: syntax_error_thrown(),
                    phase: None,
                },
            });
        }
        ParseOutcome::Unsupported { reason } => {
            return InterpOutcome::NoCoverage {
                reason: format!("body parse: {reason}"),
            }
        }
    };
    programs.push(body_prog);
    finish_body_run(
        &mut it,
        programs.last().expect("just pushed"),
        completion_witness,
    )
}

/// Run one already-parsed body `Program` (a script body, or a module lowered to
/// a strict script) to its trace: `run_script` + reactor-drain + completion
/// projection, exactly mirroring the trace driver's `eval(body); drain…` tail.
/// The script and module goals share this so equivalent programs produce
/// byte-identical trace structure.
fn finish_body_run(it: &mut Interp, prog: &Program, completion_witness: bool) -> InterpOutcome {
    let completion = match it.run_script(prog) {
        Ok(v) => {
            // Only a NORMAL body completion drains the event loop, exactly as
            // the trace driver's `try { eval(body); await drain… }` — a
            // synchronous body throw skips the drain (pending jobs are dropped).
            if let Err(a) = it.run_reactor_drain() {
                return InterpOutcome::NoCoverage {
                    reason: match a {
                        Abrupt::Fatal(e) => e,
                        other => format!("reactor drain: {other:?}"),
                    },
                };
            }
            if let Some(reason) = it.reactor_unhandled_refusal() {
                return InterpOutcome::NoCoverage { reason };
            }
            if completion_witness {
                match project::project(it, &v) {
                    Ok(pv) => Completion::Normal { v: Some(pv) },
                    Err(e) => {
                        return InterpOutcome::NoCoverage {
                            reason: format!("completion projection: {e}"),
                        }
                    }
                }
            } else {
                Completion::Normal { v: None }
            }
        }
        Err(Abrupt::Throw(v)) => match project::project_thrown(it, &v) {
            Ok(t) => Completion::Throw { v: t, phase: None },
            Err(e) => {
                return InterpOutcome::NoCoverage {
                    reason: format!("thrown projection: {e}"),
                }
            }
        },
        Err(Abrupt::Fatal(e)) => return InterpOutcome::NoCoverage { reason: e },
        Err(other) => {
            return InterpOutcome::NoCoverage {
                reason: format!("abrupt completion escaped script: {other:?}"),
            }
        }
    };
    InterpOutcome::Trace(ObservableTrace {
        schema: SCHEMA_VERSION.to_string(),
        caps: Some(projection_caps()),
        events: std::mem::take(&mut it.events),
        completion,
    })
}

/// Run the harness includes (assert.js, sta.js, …) as Script-goal sloppy
/// scripts in the shared realm, exactly like the trace driver's indirect eval.
/// Each parsed program is kept alive in `programs` (address-keyed caches). On
/// success returns `Ok(())`; a parse/eval failure of an include is a terminal
/// outcome (`Err`): a SyntaxError / thrown include is a `HarnessIncludeError`
/// trace observable, an unsupported/fatal include a sound refusal.
fn run_harness_includes(
    it: &mut Interp,
    includes: &[&str],
    programs: &mut Vec<Program>,
) -> Result<(), InterpOutcome> {
    for (i, src) in includes.iter().enumerate() {
        let prog = match parse_script(src, false) {
            ParseOutcome::Script(p) => p,
            ParseOutcome::EarlyError { .. } => {
                return Err(InterpOutcome::Trace(ObservableTrace {
                    schema: SCHEMA_VERSION.to_string(),
                    caps: Some(projection_caps()),
                    events: std::mem::take(&mut it.events),
                    completion: Completion::HarnessIncludeError {
                        v: syntax_error_thrown(),
                    },
                }));
            }
            ParseOutcome::Unsupported { reason } => {
                return Err(InterpOutcome::NoCoverage {
                    reason: format!("include[{i}] parse: {reason}"),
                })
            }
        };
        programs.push(prog);
        match it.run_script(programs.last().expect("just pushed")) {
            Ok(_) => {}
            Err(Abrupt::Throw(v)) => {
                let thrown = match project::project_thrown(it, &v) {
                    Ok(t) => t,
                    Err(e) => {
                        return Err(InterpOutcome::NoCoverage {
                            reason: format!("include[{i}] thrown projection: {e}"),
                        })
                    }
                };
                return Err(InterpOutcome::Trace(ObservableTrace {
                    schema: SCHEMA_VERSION.to_string(),
                    caps: Some(projection_caps()),
                    events: std::mem::take(&mut it.events),
                    completion: Completion::HarnessIncludeError { v: thrown },
                }));
            }
            Err(Abrupt::Fatal(e)) => {
                return Err(InterpOutcome::NoCoverage {
                    reason: format!("include[{i}]: {e}"),
                })
            }
            Err(other) => {
                return Err(InterpOutcome::NoCoverage {
                    reason: format!("include[{i}]: abrupt completion escaped script: {other:?}"),
                })
            }
        }
    }
    Ok(())
}

// ===========================================================================
// Multi-module linking (increment 2b-part-3)
//
// The `trustjs` head COVERS a SOUND, conservative subset of sibling-importing
// module graphs: relative-only specifiers resolving to existing siblings, an
// acyclic graph bounded in depth and module count, named + side-effect imports
// only, named/declaration exports only, no live (reassigned) exported bindings,
// and no module-only construct. Anything outside the subset refuses — never a
// guessed trace. Graph-wide parse errors and missing-export link failures are
// the SyntaxError an engine throws while `import()`-ing the graph (before any
// evaluation); a clean graph evaluates dependencies-first (DFS post-order),
// capturing each module's exported binding VALUES for its importers, then runs
// the main module through the SAME trace tail (`finish_module_run`) the single
// module goal uses.
// ===========================================================================

/// The bounded module count and dependency depth (past these, refuse).
const MAX_MODULES: usize = 8;
const MAX_DEPTH: usize = 3;

/// Evaluate a corpus module test as a linked module graph. `includes` are the
/// harness sources (Script-goal sloppy scripts run first, in the shared realm);
/// `main_key` is the importing test's canonical key; `main_src` its pristine
/// body; `resolver` resolves sibling specifiers to `(key, source)` on disk.
///
/// Import-FREE main modules take the exact single-module path
/// ([`module_lower::lower`] + [`finish_body_run`]) — byte-identical to
/// [`evaluate_module`], so the calibrated import-free coverage never regresses.
/// Import-BEARING main modules enter the sound linking lane.
#[must_use]
pub fn evaluate_module_graph(
    includes: &[&str],
    main_key: &str,
    main_src: &str,
    resolver: ModuleResolver,
) -> InterpOutcome {
    // Same totality belt as run_case_on_thread: a dedicated wide-stack,
    // panic-isolated worker (the resolver — disk I/O and all — runs inside it).
    let includes: Vec<String> = includes.iter().map(|s| (*s).to_string()).collect();
    let main_key = main_key.to_string();
    let main_src = main_src.to_string();
    let spawned = std::thread::Builder::new()
        .name("trust-js-interp-modgraph".to_string())
        .stack_size(32 * 1024 * 1024)
        .spawn(move || {
            let refs: Vec<&str> = includes.iter().map(String::as_str).collect();
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                evaluate_module_graph_inner(&refs, &main_key, &main_src, &resolver)
            }))
            .unwrap_or_else(|_| InterpOutcome::NoCoverage {
                reason: "internal interpreter panic (refused, not judged)".to_string(),
            })
        });
    match spawned {
        Ok(handle) => handle.join().unwrap_or_else(|_| InterpOutcome::NoCoverage {
            reason: "internal interpreter panic (refused, not judged)".to_string(),
        }),
        Err(e) => InterpOutcome::NoCoverage {
            reason: format!("case thread spawn failed: {e}"),
        },
    }
}

/// A module lowered and placed in the graph: its lowered form plus the resolved
/// key each of its import specifiers maps to.
struct GraphNode {
    lowered: module_lower::LoweredModule,
    spec_to_key: HashMap<String, String>,
}

/// The refusal / SyntaxError signal from graph construction. `SyntaxError` is a
/// graph-wide parse error (a Loading-phase SyntaxError, before any evaluation).
enum GraphFail {
    Refuse(String),
    SyntaxError,
}

fn evaluate_module_graph_inner(
    includes: &[&str],
    main_key: &str,
    main_src: &str,
    resolver: &ModuleResolver,
) -> InterpOutcome {
    let mut it = Interp::new();
    let mut programs: Vec<Program> = Vec::new();

    if let Err(outcome) = run_harness_includes(&mut it, includes, &mut programs) {
        return outcome;
    }

    // Parse the main module.
    let main_prog = match parse_module(main_src) {
        ParseOutcome::EarlyError { .. } => return syntax_error_trace(&mut it),
        ParseOutcome::Unsupported { reason } => {
            return InterpOutcome::NoCoverage {
                reason: format!("module body parse: {reason}"),
            }
        }
        ParseOutcome::Script(p) => p,
    };

    // Import-FREE, re-export-FREE fast path: identical to evaluate_module (no
    // regression). A module with a `from`-clause export (re-export) also needs
    // the linking lane even without an `import`, because its re-export source
    // is a dependency that must be evaluated.
    if !needs_linking(&main_prog) {
        return match module_lower::lower(main_prog) {
            Ok(script_prog) => {
                programs.push(script_prog);
                finish_body_run(&mut it, programs.last().expect("just pushed"), false)
            }
            Err(reason) => InterpOutcome::NoCoverage { reason },
        };
    }

    // Build the linked graph (parse + lower every reachable module, resolve
    // edges, enforce the subset + bounds).
    let main_lowered = match module_lower::lower_linked(main_prog) {
        Ok(m) => m,
        Err(reason) => return InterpOutcome::NoCoverage { reason },
    };
    let mut modules: HashMap<String, GraphNode> = HashMap::new();
    let mut order: Vec<String> = Vec::new();
    let mut on_stack: Vec<String> = Vec::new();
    match build_graph(
        main_key,
        main_lowered,
        0,
        resolver,
        &mut modules,
        &mut order,
        &mut on_stack,
    ) {
        Ok(()) => {}
        Err(GraphFail::SyntaxError) => return syntax_error_trace(&mut it),
        Err(GraphFail::Refuse(reason)) => return InterpOutcome::NoCoverage { reason },
    }

    // Resolve every module's complete export NAME set (ResolveExport /
    // GetExportedNames, §16.2.1.6.2/3) — NAME-ONLY, before any body evaluates.
    // This threads local exports, named re-exports (indirect), `export * as`
    // namespace re-exports, and `export *` star re-exports (with local-wins
    // shadowing and diamond dedup) into a per-module map of resolved bindings.
    // Ambiguous star names (two sources, same name, DIFFERENT bindings) refuse
    // the whole graph — that is the class where real engines disagree, so we
    // never guess a namespace. An unresolvable named re-export is a link-time
    // SyntaxError (before evaluation), matching the engine `import()`.
    let export_sets = match compute_export_sets(&modules, &order) {
        Ok(s) => s,
        Err(LinkFail::SyntaxError) => return syntax_error_trace(&mut it),
        Err(LinkFail::Refuse(reason)) => return InterpOutcome::NoCoverage { reason },
    };

    // Link check (ResolveExport for imports): every named import must resolve to
    // an actual export of its target — else the graph fails to link with a
    // SyntaxError, still before any module body evaluates.
    for node in modules.values() {
        for imp in &node.lowered.imports {
            let Some(dep_key) = node.spec_to_key.get(&imp.source) else {
                return InterpOutcome::NoCoverage {
                    reason: "import specifier unresolved (linker bug)".to_string(),
                };
            };
            if !export_sets[dep_key].contains_key(&imp.imported) {
                return syntax_error_trace(&mut it);
            }
        }
    }

    // Evaluate: DFS post-order (dependencies first), building each module's
    // COMPLETE resolved export value map (`full_exports`: export-name -> value,
    // including re-exports) and its LOCAL binding value map (`local_vals`:
    // local-name -> value, the resolution targets). The main module runs last
    // through the shared trace tail. `build_graph` pushes each module POST-order
    // and keeps the main module on the DFS stack throughout, so the main module
    // is placed exactly once, last.
    let mut full_exports: HashMap<String, HashMap<String, trust_js_value::JsValue>> = HashMap::new();
    let mut local_vals: HashMap<String, HashMap<String, trust_js_value::JsValue>> = HashMap::new();
    // A dependency's Module Namespace Exotic Object is created once and shared
    // by every `import * as` / `export * as` of it (namespace identity is
    // per-module-record in the spec: two references to the same module's
    // namespace yield the SAME object).
    let mut namespace_cache: HashMap<String, trust_js_value::JsValue> = HashMap::new();
    let last = order.len() - 1;
    for (idx, key) in order.iter().enumerate() {
        let node = &modules[key];
        // Resolve this module's import bindings to captured dependency values.
        let mut bound: Vec<(String, trust_js_value::JsValue)> =
            Vec::with_capacity(node.lowered.imports.len());
        for imp in &node.lowered.imports {
            let dep_key = &node.spec_to_key[&imp.source];
            let Some(val) = full_exports.get(dep_key).and_then(|m| m.get(&imp.imported)) else {
                return InterpOutcome::NoCoverage {
                    reason: "imported binding value unavailable at link time".to_string(),
                };
            };
            bound.push((imp.local.clone(), val.clone()));
        }
        // Resolve `import * as ns` bindings to the source's namespace object.
        // Collect (local, dep_key) first to release the `modules` borrow before
        // allocating on the heap.
        let ns_reqs: Vec<(String, String)> = node
            .lowered
            .namespace_imports
            .iter()
            .map(|(local, source)| (local.clone(), node.spec_to_key[source].clone()))
            .collect();
        for (local, dep_key) in ns_reqs {
            let ns_val = match namespace_of(&mut it, &dep_key, &full_exports, &mut namespace_cache) {
                Ok(v) => v,
                Err(outcome) => return outcome,
            };
            bound.push((local, ns_val));
        }

        if idx == last {
            // The main module: its completion + drain IS the observed trace.
            return finish_module_run(&mut it, &node.lowered.body, &bound, false);
        }

        // A dependency: evaluate for effect + export capture. A dependency that
        // throws or refuses makes the whole graph refuse (conservative — a
        // cross-module evaluation-throw trace is not modeled yet).
        let env = match it.run_module_body(&node.lowered.body, &bound) {
            Ok(env) => env,
            Err(Abrupt::Throw(_)) => {
                return InterpOutcome::NoCoverage {
                    reason: "dependency module threw during evaluation (out of slice)".to_string(),
                }
            }
            Err(Abrupt::Fatal(e)) => return InterpOutcome::NoCoverage { reason: e },
            Err(other) => {
                return InterpOutcome::NoCoverage {
                    reason: format!("dependency abrupt completion escaped module: {other:?}"),
                }
            }
        };
        // Capture this module's LOCAL export binding values (the resolution
        // targets that named / star re-exports point at).
        let mut lv: HashMap<String, trust_js_value::JsValue> = HashMap::new();
        for (_exported, local) in &node.lowered.exports {
            let Some(val) = it.module_export_value(env, local) else {
                return InterpOutcome::NoCoverage {
                    reason: format!("exported binding `{local}` uninitialized after evaluation"),
                };
            };
            lv.insert(local.clone(), val);
        }
        local_vals.insert(key.clone(), lv);

        // Build this module's complete resolved export value map from its
        // resolved export set: each Binding resolution pulls the value from the
        // (already-evaluated) origin module's local bindings; each Namespace
        // resolution materializes (once, cached) the source module's namespace
        // object. Collect the resolution list first to release the borrow on
        // `export_sets` before touching `it` / the caches.
        let resolutions: Vec<(String, Resolution)> = export_sets[key]
            .iter()
            .map(|(name, res)| (name.clone(), res.clone()))
            .collect();
        let mut fe: HashMap<String, trust_js_value::JsValue> = HashMap::new();
        for (name, res) in resolutions {
            let val = match res {
                Resolution::Binding { module, local } => {
                    let Some(v) = local_vals.get(&module).and_then(|m| m.get(&local)) else {
                        return InterpOutcome::NoCoverage {
                            reason: format!("re-exported binding `{local}` unavailable at link time"),
                        };
                    };
                    v.clone()
                }
                Resolution::Namespace { module } => {
                    match namespace_of(&mut it, &module, &full_exports, &mut namespace_cache) {
                        Ok(v) => v,
                        Err(outcome) => return outcome,
                    }
                }
            };
            fe.insert(name, val);
        }
        full_exports.insert(key.clone(), fe);
    }

    // `order` is non-empty (it contains the main module) and the main module is
    // handled inside the loop, so this is unreachable.
    InterpOutcome::NoCoverage {
        reason: "empty module graph (linker bug)".to_string(),
    }
}

/// DFS that parses, lowers, and places every module reachable from `key` into
/// `modules`, resolving each import specifier to a canonical key. Appends `key`
/// to `order` in POST-order (all dependencies precede it). Detects self-import,
/// cycles, the module-count / depth bounds, resolver failures, dependency
/// parse errors (→ `SyntaxError`), and out-of-subset shapes (→ `Refuse`).
fn build_graph(
    key: &str,
    lowered: module_lower::LoweredModule,
    depth: usize,
    resolver: &ModuleResolver,
    modules: &mut HashMap<String, GraphNode>,
    order: &mut Vec<String>,
    on_stack: &mut Vec<String>,
) -> Result<(), GraphFail> {
    on_stack.push(key.to_string());
    let mut spec_to_key: HashMap<String, String> = HashMap::new();

    for spec in &lowered.dep_specs {
        if spec_to_key.contains_key(spec) {
            continue; // same specifier imported twice: one edge.
        }
        let (dep_key, dep_src) = resolver(key, spec).map_err(GraphFail::Refuse)?;
        if dep_key == key {
            return Err(GraphFail::Refuse(format!("self-import (`{spec}`)")));
        }
        spec_to_key.insert(spec.clone(), dep_key.clone());

        if on_stack.iter().any(|k| k == &dep_key) {
            return Err(GraphFail::Refuse(format!(
                "import cycle detected (`{spec}`)"
            )));
        }
        if modules.contains_key(&dep_key) {
            continue; // already placed (DAG re-reference).
        }
        if modules.len() + 1 >= MAX_MODULES {
            return Err(GraphFail::Refuse(format!(
                "module graph exceeds {MAX_MODULES} modules"
            )));
        }
        if depth + 1 > MAX_DEPTH {
            return Err(GraphFail::Refuse(format!(
                "module graph exceeds depth {MAX_DEPTH}"
            )));
        }
        let dep_lowered = match parse_module(&dep_src) {
            // A parse error ANYWHERE in the graph is a Loading-phase
            // SyntaxError, before any evaluation.
            ParseOutcome::EarlyError { .. } => return Err(GraphFail::SyntaxError),
            ParseOutcome::Unsupported { reason } => {
                return Err(GraphFail::Refuse(format!("dependency parse: {reason}")))
            }
            ParseOutcome::Script(p) => match module_lower::lower_linked(p) {
                Ok(m) => m,
                Err(reason) => return Err(GraphFail::Refuse(reason)),
            },
        };
        build_graph(&dep_key, dep_lowered, depth + 1, resolver, modules, order, on_stack)?;
    }

    on_stack.pop();
    order.push(key.to_string());
    modules.insert(key.to_string(), GraphNode { lowered, spec_to_key });
    Ok(())
}

/// The main module's trace tail for the linking lane: run its body with imports
/// bound, then drain + project exactly like [`finish_body_run`]. Modules never
/// observe a completion witness (the module goal emits `{k:"normal"}`), so the
/// witness flag only mirrors the script tail's shape.
fn finish_module_run(
    it: &mut Interp,
    prog: &Program,
    imports: &[(String, trust_js_value::JsValue)],
    _completion_witness: bool,
) -> InterpOutcome {
    let completion = match it.run_module_body(prog, imports) {
        Ok(_env) => {
            if let Err(a) = it.run_reactor_drain() {
                return InterpOutcome::NoCoverage {
                    reason: match a {
                        Abrupt::Fatal(e) => e,
                        other => format!("reactor drain: {other:?}"),
                    },
                };
            }
            if let Some(reason) = it.reactor_unhandled_refusal() {
                return InterpOutcome::NoCoverage { reason };
            }
            Completion::Normal { v: None }
        }
        Err(Abrupt::Throw(v)) => match project::project_thrown(it, &v) {
            Ok(t) => Completion::Throw { v: t, phase: None },
            Err(e) => {
                return InterpOutcome::NoCoverage {
                    reason: format!("thrown projection: {e}"),
                }
            }
        },
        Err(Abrupt::Fatal(e)) => return InterpOutcome::NoCoverage { reason: e },
        Err(other) => {
            return InterpOutcome::NoCoverage {
                reason: format!("abrupt completion escaped module: {other:?}"),
            }
        }
    };
    InterpOutcome::Trace(ObservableTrace {
        schema: SCHEMA_VERSION.to_string(),
        caps: Some(projection_caps()),
        events: std::mem::take(&mut it.events),
        completion,
    })
}

/// The SyntaxError-throw trace an engine produces when `import()`-ing a module
/// graph that fails at load / link time (a graph-wide parse error or an
/// unresolved export), before any module body evaluates: the harness-include
/// events, then a phase-less SyntaxError throw.
fn syntax_error_trace(it: &mut Interp) -> InterpOutcome {
    InterpOutcome::Trace(ObservableTrace {
        schema: SCHEMA_VERSION.to_string(),
        caps: Some(projection_caps()),
        events: std::mem::take(&mut it.events),
        completion: Completion::Throw {
            v: syntax_error_thrown(),
            phase: None,
        },
    })
}

/// Does a parsed module need the multi-module linking lane? True for a
/// top-level `import` declaration OR a `from`-clause export (`export * from`,
/// `export * as ns from`, `export { … } from`) — a re-export whose source is a
/// dependency that must be evaluated. A module with none of these (only local
/// declaration / from-less exports) takes the single-module fast path.
fn needs_linking(prog: &Program) -> bool {
    prog.body.iter().any(|s| {
        matches!(
            s,
            Stmt::Import(_)
                | Stmt::Export(ExportDecl::Star { .. })
                | Stmt::Export(ExportDecl::Named { source: Some(_), .. })
        )
    })
}

/// A resolved export target within the acyclic module graph — the identity used
/// to detect star-export ambiguity (two star sources providing the same name
/// that resolve to DIFFERENT targets). Mirrors a spec ResolvedBinding Record: a
/// concrete binding `{module, bindingName}`, or a module-namespace binding
/// (`export * as ns` / a `namespace` bindingName). Structural equality is the
/// spec's "same binding" test (§16.2.1.6.3 step 9.d.iii): same module AND same
/// bindingName; a namespace and a concrete binding are never the same.
#[derive(Clone, PartialEq, Eq)]
enum Resolution {
    Binding { module: String, local: String },
    Namespace { module: String },
}

/// A link-phase failure: a graph-wide `SyntaxError` (an unresolvable named
/// re-export, matching the engine `import()`), or a sound refusal (`Refuse`) —
/// notably an ambiguous star re-export, the class where real engines disagree.
enum LinkFail {
    Refuse(String),
    SyntaxError,
}

/// Resolve every module's complete export NAME set (ResolveExport /
/// GetExportedNames), NAME-ONLY, bottom-up over the post-order `order` (a
/// dependency's set is complete before any module that re-exports from it). For
/// each module the map is: exported-name -> resolved binding, threading:
///   * local exports (`export const x` / `export { x }`) — a binding of self;
///   * named re-exports (`export { a as c } from src`) — resolve `a` in `src`'s
///     already-computed set (chains follow transitively; unresolved => SyntaxError);
///   * namespace re-exports (`export * as ns from src`) — a `Namespace{src}`;
///   * star re-exports (`export * from src`) — every non-`default` name of
///     `src` NOT already provided locally/explicitly (local wins), with
///     diamond dedup (same underlying binding) and ambiguity detection (two
///     star sources, same name, different bindings => `Refuse`).
fn compute_export_sets(
    modules: &HashMap<String, GraphNode>,
    order: &[String],
) -> Result<HashMap<String, HashMap<String, Resolution>>, LinkFail> {
    let mut sets: HashMap<String, HashMap<String, Resolution>> = HashMap::new();
    for key in order {
        let node = &modules[key];
        let low = &node.lowered;
        let mut names: HashMap<String, Resolution> = HashMap::new();

        // Local exports resolve to a binding of this module. Parse-time
        // duplicate-export-name detection guarantees each exported name is
        // unique across local + indirect + namespace re-exports.
        for (exp, local) in &low.exports {
            names.insert(
                exp.clone(),
                Resolution::Binding { module: key.clone(), local: local.clone() },
            );
        }
        // Named re-exports (indirect): resolve the imported name in the source's
        // already-computed set. An unresolved name is a link-time SyntaxError.
        for re in &low.named_reexports {
            let src_key = &node.spec_to_key[&re.source];
            let src_set = sets
                .get(src_key)
                .ok_or_else(|| LinkFail::Refuse("re-export source unresolved (linker bug)".to_string()))?;
            match src_set.get(&re.imported) {
                Some(res) => {
                    names.insert(re.exported.clone(), res.clone());
                }
                None => return Err(LinkFail::SyntaxError),
            }
        }
        // Namespace re-exports (`export * as ns from src`): a namespace binding.
        for (ns, source) in &low.namespace_reexports {
            let src_key = node.spec_to_key[source].clone();
            names.insert(ns.clone(), Resolution::Namespace { module: src_key });
        }
        // Star re-exports: accumulate every non-`default` name of each source
        // not already provided locally / explicitly (local wins). A name from
        // two sources is fine iff both resolve to the SAME binding (diamond);
        // conflicting bindings are ambiguous => refuse (engines may disagree).
        let mut star_map: HashMap<String, Resolution> = HashMap::new();
        let mut ambiguous = false;
        for source in &low.star_reexports {
            let src_key = &node.spec_to_key[source];
            let src_set = sets
                .get(src_key)
                .ok_or_else(|| LinkFail::Refuse("star source unresolved (linker bug)".to_string()))?;
            for (n, res) in src_set {
                if n == "default" || names.contains_key(n) {
                    continue;
                }
                match star_map.get(n) {
                    None => {
                        star_map.insert(n.clone(), res.clone());
                    }
                    Some(existing) => {
                        if existing != res {
                            ambiguous = true;
                        }
                    }
                }
            }
        }
        if ambiguous {
            return Err(LinkFail::Refuse(
                "ambiguous `export *` (same name resolving to different bindings) — \
                 real engines disagree, refusing rather than guess a namespace"
                    .to_string(),
            ));
        }
        for (n, res) in star_map {
            names.insert(n, res);
        }
        sets.insert(key.clone(), names);
    }
    Ok(sets)
}

/// Materialize (once, cached) the Module Namespace Exotic Object for module
/// `key`, from its complete resolved export value map. Namespace identity is
/// per-module: every reference to `key`'s namespace shares one object.
fn namespace_of(
    it: &mut Interp,
    key: &str,
    full_exports: &HashMap<String, HashMap<String, trust_js_value::JsValue>>,
    namespace_cache: &mut HashMap<String, trust_js_value::JsValue>,
) -> Result<trust_js_value::JsValue, InterpOutcome> {
    if let Some(v) = namespace_cache.get(key) {
        return Ok(v.clone());
    }
    let Some(exports_map) = full_exports.get(key) else {
        return Err(InterpOutcome::NoCoverage {
            reason: "namespace source unevaluated at link time".to_string(),
        });
    };
    let exports: Vec<(String, trust_js_value::JsValue)> =
        exports_map.iter().map(|(k, v)| (k.clone(), v.clone())).collect();
    let oid = match it.make_module_namespace(&exports) {
        Ok(oid) => oid,
        Err(Abrupt::Fatal(e)) => return Err(InterpOutcome::NoCoverage { reason: e }),
        Err(other) => {
            return Err(InterpOutcome::NoCoverage {
                reason: format!("namespace object construction: {other:?}"),
            })
        }
    };
    let v = trust_js_value::JsValue::Obj(oid);
    namespace_cache.insert(key.to_string(), v.clone());
    Ok(v)
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_js_trace::{HostEvent, ProjectedValue, PropKey, ThrownProjection};

    /// Witness-on run (unit tests inspect completion values).
    fn run(body: &str) -> InterpOutcome {
        evaluate_case_opts(&[], body, false, true)
    }

    fn completion_of(o: InterpOutcome) -> Completion {
        match o {
            InterpOutcome::Trace(t) => t.completion,
            InterpOutcome::NoCoverage { reason } => panic!("unexpected NoCoverage: {reason}"),
        }
    }

    fn events_of(o: InterpOutcome) -> Vec<HostEvent> {
        match o {
            InterpOutcome::Trace(t) => t.events,
            InterpOutcome::NoCoverage { reason } => panic!("unexpected NoCoverage: {reason}"),
        }
    }

    fn num(s: &str) -> ProjectedValue {
        ProjectedValue::Num { v: s.to_string() }
    }

    fn s(v: &str) -> ProjectedValue {
        ProjectedValue::Str { v: v.to_string() }
    }

    fn b(v: bool) -> ProjectedValue {
        ProjectedValue::Bool { v }
    }

    fn bi(v: &str) -> ProjectedValue {
        ProjectedValue::Bigint { v: v.to_string() }
    }

    fn refused(body: &str) -> String {
        match run(body) {
            InterpOutcome::NoCoverage { reason } => reason,
            InterpOutcome::Trace(t) => panic!("expected NoCoverage, got trace: {t:?}"),
        }
    }

    fn logged(body: &str) -> Vec<ProjectedValue> {
        let InterpOutcome::Trace(t) = run(body) else {
            let InterpOutcome::NoCoverage { reason } = run(body) else {
                unreachable!()
            };
            panic!("unexpected NoCoverage: {reason}");
        };
        assert!(
            matches!(t.completion, Completion::Normal { .. }),
            "expected normal completion, got {:?}",
            t.completion
        );
        let mut out = Vec::new();
        for e in t.events {
            match e {
                HostEvent::Stdout { v } => out.extend(v),
                other => panic!("unexpected event {other:?}"),
            }
        }
        out
    }

    #[test]
    fn bigint_semantics() {
        // Literals (all bases) + the decimal toString projection.
        assert_eq!(
            logged("console.log(10n, -5n, 0n, 0xffn, 0b101n, 0o17n);"),
            vec![bi("10"), bi("-5"), bi("0"), bi("255"), bi("5"), bi("15")]
        );
        // Arithmetic, incl. huge values, truncated div / sign-of-dividend rem.
        assert_eq!(logged("console.log(2n ** 64n);"), vec![bi("18446744073709551616")]);
        assert_eq!(
            logged("console.log(7n / 2n, 7n % 2n, -7n / 2n, -7n % 2n);"),
            vec![bi("3"), bi("1"), bi("-3"), bi("-1")]
        );
        // Bitwise / shift / unary.
        assert_eq!(
            logged("console.log(-5n & 3n, 1n << 4n, -5n >> 1n, ~5n, -(5n));"),
            vec![bi("3"), bi("16"), bi("-3"), bi("-6"), bi("-5")]
        );
        // typeof + ToBoolean.
        assert_eq!(
            logged("console.log(typeof 1n, !!0n, !!3n);"),
            vec![s("bigint"), b(false), b(true)]
        );
        // Mixing BigInt and Number in arithmetic → TypeError; no unary +.
        for src in ["1n + 1", "1n * 2", "1n & 1", "1n >>> 1n", "+1n"] {
            assert_eq!(
                completion_of(run(&format!(
                    "var t=false; try {{ {src}; }} catch(e){{ t = e instanceof TypeError; }} t;"
                ))),
                Completion::Normal { v: Some(b(true)) },
                "expected TypeError for {src}"
            );
        }
        // BigInt() constructor + ToBigInt coercion; number must be integral.
        assert_eq!(
            logged("console.log(BigInt('255'), BigInt(255), BigInt(true), BigInt('0x10'));"),
            vec![bi("255"), bi("255"), bi("1"), bi("16")]
        );
        for src in ["BigInt(1.5)", "1n / 0n", "1n % 0n", "2n ** -1n"] {
            assert_eq!(
                completion_of(run(&format!(
                    "var t=false; try {{ {src}; }} catch(e){{ t = e instanceof RangeError; }} t;"
                ))),
                Completion::Normal { v: Some(b(true)) },
                "expected RangeError for {src}"
            );
        }
        // asIntN / asUintN wrap; toString(radix); comparison + equality.
        assert_eq!(
            logged("console.log(BigInt.asIntN(8, 255n), BigInt.asUintN(8, -1n));"),
            vec![bi("-1"), bi("255")]
        );
        assert_eq!(
            logged("console.log((255n).toString(16), (255n).toString(2));"),
            vec![s("ff"), s("11111111")]
        );
        assert_eq!(
            logged("console.log(1n < 2, 2n == 2, 2n === 2, 2n > 1.5, 2n == '2');"),
            vec![b(true), b(true), b(false), b(true), b(true)]
        );
        // BigInt64Array / BigUint64Array round-trip + element coercion.
        assert_eq!(
            logged("var a = new BigInt64Array(2); a[0] = 5n; a[1] = -1n; console.log(a[0], a[1], a.length);"),
            vec![bi("5"), bi("-1"), num("2")]
        );
        assert_eq!(
            logged("var a = new BigUint64Array([1n, 2n]); console.log(a[0] + a[1], typeof a[0]);"),
            vec![bi("3"), s("bigint")]
        );
        // BigInt64Array wraps on store; DataView setBigInt64/getBigInt64.
        assert_eq!(
            logged("var d = new DataView(new ArrayBuffer(8)); d.setBigUint64(0, 18446744073709551615n); console.log(d.getBigUint64(0), d.getBigInt64(0));"),
            vec![bi("18446744073709551615"), bi("-1")]
        );
        // Number(bigint) converts (does NOT throw); huge value → Infinity.
        assert_eq!(
            logged("console.log(Number(10n), Number(-3n), Number(10n ** 400n));"),
            vec![num("10"), num("-3"), num("Infinity")]
        );
        // TOTALITY: an astronomically large intermediate refuses SOUNDLY
        // (NoCoverage), never panics; a small result still computes.
        assert!(matches!(run("2n ** 10000000000n;"), InterpOutcome::NoCoverage { .. }));
        assert!(matches!(
            run("BigInt.asUintN(9007199254740000, -1n);"),
            InterpOutcome::NoCoverage { .. }
        ));
        assert_eq!(logged("console.log(2n ** 200n % 7n);"), vec![bi("4")]);
        // Wrapper/coercion edge cases (cross-checked against Node + Bun):
        // String()/template ToString, toString(radix) sign, Object() wrapper
        // typeof + Object.prototype.toString @@toStringTag, loose-eq with hex/
        // boolean/fractional strings, BigInt property key, method via bracket.
        assert_eq!(
            logged(
                "console.log(String(-255n), (-255n).toString(16), `${1n+2n}`, typeof Object(5n), \
                 Object.prototype.toString.call(5n), 1n=='0x1', 1n==true, 1n=='1.0', \
                 ({})[1n]===undefined, (10n)['toString']());"
            ),
            vec![
                s("-255"),
                s("-ff"),
                s("3"),
                s("object"),
                s("[object BigInt]"),
                b(true),
                b(true),
                b(false),
                b(true),
                s("10"),
            ]
        );
    }

    #[test]
    fn generators_cover_or_refuse_never_panic() {
        // Tractable generators cover (produce a Trace).
        for src in [
            "function* g(){ yield 1; yield 2; return 3; } var it = g(); it.next(); it.next(); it.next();",
            "function* g(){ var x = yield 1; return x; } var it = g(); it.next(); it.next(9);",
            "function* g(){ for (var i=0;i<3;i++) yield i; } [...g()];",
            "function* g(){ while (true) { yield 1; break; } } g().next();",
            "function* g(){ try { yield 1; } finally { 1; } } var it=g(); it.next(); it.return(2);",
            "function* g(){ try { yield 1; } catch(e){ yield e; } } var it=g(); it.next(); it.throw('x');",
            "function* g(){ yield* [1,2,3]; } [...g()];",
            "function* inner(){ yield 1; return 9; } function* g(){ var r = yield* inner(); yield r; } [...g()];",
            "function* g(){ for (var x of [1,2]) yield x; } [...g()];",
            "var o = { *m(){ yield this; } }; o.m().next();",
            "class C { *m(){ yield 1; } } [...new C().m()];",
            "function* g(){ yield 1; } var it = g(); it.next(); it.next(); it.return(5); it.next();",
        ] {
            assert!(
                matches!(run(src), InterpOutcome::Trace(_)),
                "expected coverage for: {src}"
            );
        }
        // Intractable yield positions refuse SOUNDLY (never a wrong trace, never
        // a panic). Refusal happens at resume time, so `.next()` is needed.
        for src in [
            "function* g(){ f(yield 1); } function f(){} g().next();", // call argument
            "function* g(){ var x = 1 + (yield 2); } g().next();",     // operator operand
            "function* g(){ var a = yield 1, b = yield 2; } g().next();", // multi-declarator
            "function* g(){ switch (yield 1) { case 1: yield 2; } } g().next();", // yield in switch disc
            "function* g(){ ({ [yield 1]: 2 }); } g().next();",        // computed key
        ] {
            assert!(
                matches!(run(src), InterpOutcome::NoCoverage { .. }),
                "expected sound refusal for: {src}"
            );
        }
        // Totality: hostile / resource-extreme generators must refuse or throw,
        // never panic (the catch_unwind belt turns any panic into NoCoverage,
        // but these should trip a cap cleanly).
        for src in [
            "function* g(){ while (true) yield 1; } var it = g(); for (var i=0;i<2000000;i++) it.next();",
            "function* g(){ yield* g(); } var it = g(); it.next(); it.next();",
            "function* g(){ return yield yield yield 1; } var it=g(); it.next(); it.next(); it.next(); it.next();",
        ] {
            // Any deterministic verdict is acceptable; the point is no panic.
            let _ = run(src);
        }
    }

    #[test]
    fn promise_static_methods_honor_subclass_receiver() {
        // resolve(x) on a subclass: NewPromiseCapability(SubP) constructs one
        // SubP instance; the result is a SubP promise; the executor arg is a fn.
        assert_eq!(
            logged(
                "var executor = null, callCount = 0;\
                 class SubP extends Promise { constructor(a){ super(a); executor = a; callCount++; } }\
                 var r = SubP.resolve(5);\
                 console.log(r.constructor === SubP, r instanceof SubP, callCount, typeof executor);"
            ),
            vec![b(true), b(true), num("1"), s("function")]
        );
        // PromiseResolve pass-through: an existing promise whose constructor IS
        // the receiver is returned unchanged (no re-wrap, no `then` observation).
        assert_eq!(
            logged(
                "class SubP extends Promise {}\
                 var a = SubP.resolve(5);\
                 console.log(SubP.resolve(a) === a);"
            ),
            vec![b(true)]
        );
        // all([]) / allSettled([]) on a subclass: the result is a subclass
        // instance and the constructor ran exactly once (empty iterable).
        assert_eq!(
            logged(
                "var n = 0;\
                 class SubP extends Promise { constructor(a){ super(a); n++; } }\
                 var r = SubP.all([]);\
                 console.log(r.constructor === SubP, r instanceof SubP, n);"
            ),
            vec![b(true), b(true), num("1")]
        );
        // race([]) on a subclass stays a pending subclass instance (never settles).
        assert_eq!(
            logged(
                "class SubP extends Promise {}\
                 var r = SubP.race([]);\
                 console.log(r instanceof SubP, typeof r.then);"
            ),
            vec![b(true), s("function")]
        );
        // withResolvers on a subclass produces a subclass promise + both fns.
        assert_eq!(
            logged(
                "class SubP extends Promise {}\
                 var o = SubP.withResolvers.call(SubP);\
                 console.log(o.promise instanceof SubP, typeof o.resolve, typeof o.reject);"
            ),
            vec![b(true), s("function"), s("function")]
        );
        // all on an arbitrary constructor C: GetPromiseResolve(C) is Called per
        // element, and the Resolve Element function's [[AlreadyCalled]] guard
        // makes a thenable that fulfills twice count only once.
        assert_eq!(
            logged(
                "var order = [];\
                 function C(exec){ function resolve(vals){ order.push('r:' + vals.length + ':' + vals[0]); } exec(resolve, function(){}); }\
                 C.resolve = function(v){ return v; };\
                 var p1 = { then: function(onF){ onF('X'); onF('Y'); } };\
                 Promise.all.call(C, [p1]);\
                 console.log(order.join('|'));"
            ),
            vec![s("r:1:X")]
        );
        // NewPromiseCapability validation: a constructor that never makes resolve
        // callable throws TypeError; a non-constructor receiver throws TypeError.
        assert_eq!(
            logged(
                "function Bad(){}\
                 var a = false, b2 = false;\
                 try { Promise.all.call(Bad, []); } catch (e) { a = e instanceof TypeError; }\
                 try { Promise.all.call(eval, []); } catch (e) { b2 = e instanceof TypeError; }\
                 console.log(a, b2);"
            ),
            vec![b(true), b(true)]
        );
    }

    #[test]
    fn promise_subclass_receiver_refuses_soundly_never_wrong() {
        // A subclass reject leaves an unhandled rejection: sound NoCoverage.
        assert!(matches!(
            run("class SubP extends Promise {} SubP.reject(1);"),
            InterpOutcome::NoCoverage { .. }
        ));
        // A subclass combinator over a real element needs the subclass @@species
        // `then` path (out of slice): sound NoCoverage, never a wrong trace.
        assert!(matches!(
            run("class SubP extends Promise {} SubP.all([1]);"),
            InterpOutcome::NoCoverage { .. }
        ));
        // Non-object receivers still throw TypeError (Type(C) is not Object).
        assert_eq!(
            completion_of(run(
                "var t = false; try { Promise.resolve.call(undefined, 1); } \
                 catch (e) { t = e instanceof TypeError; } t;"
            )),
            Completion::Normal { v: Some(b(true)) }
        );
    }

    #[test]
    fn completion_values_basics() {
        assert_eq!(completion_of(run("1 + 2;")), Completion::Normal { v: Some(num("3")) });
        assert_eq!(
            completion_of(run("var x = 5;")),
            Completion::Normal { v: Some(ProjectedValue::Undefined) }
        );
        // Declarations leave the previous statement value in place.
        assert_eq!(completion_of(run("42; var y;")), Completion::Normal { v: Some(num("42")) });
        assert_eq!(
            completion_of(run("1; if (true) {}")),
            Completion::Normal { v: Some(ProjectedValue::Undefined) }
        );
        assert_eq!(
            completion_of(run("while (true) { 5; break; }")),
            Completion::Normal { v: Some(num("5")) }
        );
        assert_eq!(
            completion_of(run("a: { 1; break a; 2; }")),
            Completion::Normal { v: Some(num("1")) }
        );
    }

    #[test]
    fn number_projection_vectors() {
        // The shared number vectors, through real evaluation + projection.
        let vs = logged(
            "console.log(1, 0.1, 0.1 + 0.2, 1e21, 1e-7, 123456789, 5e-324, \
             1.7976931348623157e308, 100, 0.000001, -1.5, 2e21, 1.5e22, \
             123456789012345680000, NaN, Infinity, -Infinity, -0, 0);",
        );
        let want: Vec<ProjectedValue> = [
            "1", "0.1", "0.30000000000000004", "1e+21", "1e-7", "123456789", "5e-324",
            "1.7976931348623157e+308", "100", "0.000001", "-1.5", "2e+21", "1.5e+22",
            "123456789012345680000", "NaN", "Infinity", "-Infinity", "-0", "0",
        ]
        .iter()
        .map(|x| num(x))
        .collect();
        assert_eq!(vs, want);
        // String coercion of -0 is "0"; the projection alone says "-0".
        assert_eq!(logged("console.log(String(-0), '' + -0, `${-0}`);"), vec![s("0"), s("0"), s("0")]);
    }

    #[test]
    fn coercion_vectors() {
        assert_eq!(
            logged(
                "console.log('a' + 1, '5' * '2', +true, -'3', 1 + null, 1 + undefined, \
                 'x' + undefined, Number('0x10'), Number(''), Number('  42 '), Boolean(''), \
                 isNaN('abc'), isFinite('10'), '' + {}, ({}) + 1);"
            ),
            vec![
                s("a1"),
                num("10"),
                num("1"),
                num("-3"),
                num("1"),
                num("NaN"),
                s("xundefined"),
                num("16"),
                num("0"),
                num("42"),
                b(false),
                b(true),
                b(true),
                s("[object Object]"),
                s("[object Object]1"),
            ]
        );
        assert_eq!(
            logged(
                "console.log(1 < 2, '10' < '9', 2 <= 2, null == undefined, null === undefined, \
                 NaN == NaN, 1 == '1', 0 == false, typeof 5, typeof undefined, typeof null, \
                 typeof console.log, true && 0, false || 'x', 1 ?? 2, null ?? 'd');"
            ),
            vec![
                b(true),
                b(true),
                b(true),
                b(true),
                b(false),
                b(false),
                b(true),
                b(true),
                s("number"),
                s("undefined"),
                s("object"),
                s("function"),
                num("0"),
                s("x"),
                num("1"),
                s("d"),
            ]
        );
        // Bitwise / shifts (ToInt32/ToUint32 wrapping).
        assert_eq!(
            logged("console.log(5 & 3, 5 | 3, 5 ^ 3, ~5, 1 << 31, -1 >>> 0, -8 >> 1, 2 ** 10, (-2) ** 3);"),
            vec![
                num("1"),
                num("7"),
                num("6"),
                num("-6"),
                num("-2147483648"),
                num("4294967295"),
                num("-4"),
                num("1024"),
                num("-8"),
            ]
        );
    }

    #[test]
    fn closures_and_functions() {
        assert_eq!(
            completion_of(run("function add(a, b) { return a + b; } add(2, 40);")),
            Completion::Normal { v: Some(num("42")) }
        );
        assert_eq!(
            completion_of(run(
                "function mk(n) { return function (m) { return n * m; }; } mk(6)(7);"
            )),
            Completion::Normal { v: Some(num("42")) }
        );
        // Arrows: lexical this + concise body.
        assert_eq!(
            completion_of(run(
                "var o = { v: 40, m: function () { var f = () => this.v + 2; return f(); } }; o.m();"
            )),
            Completion::Normal { v: Some(num("42")) }
        );
        // Default + rest params, name inference, fn length.
        assert_eq!(
            logged(
                "function f(a, b = a + 1, ...r) { return [a, b, r.length]; }\n\
                 var g = function () {};\n\
                 console.log(f(1)[1], f(1, 2, 3, 4)[2], f.length, g.name, g.length);"
            ),
            vec![num("2"), num("2"), num("1"), s("g"), num("0")]
        );
        // Named function expression self-binding is immutable (sloppy no-op).
        assert_eq!(
            completion_of(run("var f = function g() { g = 5; return g; }; f() === f;")),
            Completion::Normal { v: Some(b(true)) }
        );
        assert_eq!(
            completion_of(run(
                "var f = function g() { 'use strict'; g = 5; };\n\
                 var t = false; try { f(); } catch (e) { t = e instanceof TypeError; } t;"
            )),
            Completion::Normal { v: Some(b(true)) }
        );
    }

    #[test]
    fn tdz_and_const() {
        assert_eq!(
            logged(
                "function f() { x = 1; }\n\
                 var t = false;\n\
                 try { f(); } catch (e) { t = e instanceof ReferenceError; }\n\
                 let x;\n\
                 f();\n\
                 console.log(t, x);"
            ),
            vec![b(true), num("1")]
        );
        assert_eq!(
            completion_of(run(
                "const c = 1; var t = false;\n\
                 try { c = 2; } catch (e) { t = e instanceof TypeError; } t;"
            )),
            Completion::Normal { v: Some(b(true)) }
        );
        // typeof of a TDZ binding throws.
        assert_eq!(
            completion_of(run(
                "var t = false; try { typeof z; } catch (e) { t = e instanceof ReferenceError; } let z; t;"
            )),
            Completion::Normal { v: Some(b(true)) }
        );
        // Per-iteration let capture.
        assert_eq!(
            logged(
                "var fns = []; for (let i = 0; i < 3; i++) { fns.push(function () { return i; }); }\n\
                 console.log(fns[0](), fns[1](), fns[2]());"
            ),
            vec![num("0"), num("1"), num("2")]
        );
        assert_eq!(
            logged(
                "var fns = []; for (var j = 0; j < 3; j++) { fns.push(function () { return j; }); }\n\
                 console.log(fns[0](), fns[2]());"
            ),
            vec![num("3"), num("3")]
        );
    }

    #[test]
    fn object_property_order_and_projection() {
        let c = completion_of(run("[7, 8];"));
        let Completion::Normal {
            v: Some(ProjectedValue::Obj { cls, props, .. }),
        } = c
        else {
            panic!("expected object completion");
        };
        assert_eq!(cls.as_deref(), Some("Array"));
        assert_eq!(
            props.expect("props"),
            vec![
                (PropKey::Str("0".to_string()), num("7")),
                (PropKey::Str("1".to_string()), num("8")),
                (
                    PropKey::Str("length".to_string()),
                    ProjectedValue::Nonenum { v: Box::new(num("2")) }
                ),
            ]
        );

        let c = completion_of(run("var o = { b: 1, 2: 'two', a: 3, 0: 'zero' }; o;"));
        let Completion::Normal {
            v: Some(ProjectedValue::Obj { props, .. }),
        } = c
        else {
            panic!("expected object completion");
        };
        let keys: Vec<String> = props
            .expect("props")
            .into_iter()
            .map(|(k, _)| match k {
                PropKey::Str(s) => s,
                PropKey::Sym { .. } => panic!("no symbol keys here"),
            })
            .collect();
        assert_eq!(keys, vec!["0", "2", "b", "a"]);

        // Cycles project as back-references.
        let c = completion_of(run("var o = {}; o.self = o; o;"));
        let Completion::Normal {
            v: Some(ProjectedValue::Obj { id, props, .. }),
        } = c
        else {
            panic!("expected object completion");
        };
        assert_eq!(id, 0);
        assert_eq!(
            props.expect("props"),
            vec![(PropKey::Str("self".to_string()), ProjectedValue::Circ { target: 0 })]
        );

        // Accessors project without being invoked.
        let c = completion_of(run(
            "var n = 0; var o = { get x() { n++; return 1; } }; o;"
        ));
        let Completion::Normal {
            v: Some(ProjectedValue::Obj { props, .. }),
        } = c
        else {
            panic!("expected object completion");
        };
        assert_eq!(
            props.expect("props"),
            vec![(
                PropKey::Str("x".to_string()),
                ProjectedValue::Accessor { get: true, set: false }
            )]
        );
    }

    #[test]
    fn thrown_projections() {
        assert_eq!(
            completion_of(run("throw 42;")),
            Completion::Throw {
                v: ThrownProjection::Prim { v: num("42") },
                phase: None
            }
        );
        assert_eq!(
            completion_of(run("throw new TypeError('boom');")),
            Completion::Throw {
                v: ThrownProjection::Error {
                    ctor: Some("Error:TypeError".to_string()),
                    name: Some("TypeError".to_string()),
                    ctor_name: Some("TypeError".to_string()),
                },
                phase: None
            }
        );
        // A user-constructor instance: Object class, ctor_name from
        // prototype.constructor.name.
        assert_eq!(
            completion_of(run(
                "function Test262Error(m) { this.message = m || ''; }\n\
                 throw new Test262Error('nope');"
            )),
            Completion::Throw {
                v: ThrownProjection::Error {
                    ctor: Some("Object".to_string()),
                    name: None,
                    ctor_name: Some("Test262Error".to_string()),
                },
                phase: None
            }
        );
    }

    #[test]
    fn harness_files_evaluate() {
        // Inline the real sta.js core; the full files run in the env-gated
        // differential test.
        let sta = "function Test262Error(message) {\n\
                   if (!(this instanceof Test262Error)) return new Test262Error(message);\n\
                   this.message = message || \"\";\n\
                   }\n\
                   Test262Error.prototype.toString = function () {\n\
                   return \"Test262Error: \" + this.message;\n\
                   };\n\
                   function $DONOTEVALUATE() { throw \"Test262: This statement should not be evaluated.\"; }";
        let out = evaluate_case_opts(&[sta], "throw new Test262Error('nope');", false, true);
        assert_eq!(
            completion_of(out),
            Completion::Throw {
                v: ThrownProjection::Error {
                    ctor: Some("Object".to_string()),
                    name: None,
                    ctor_name: Some("Test262Error".to_string()),
                },
                phase: None
            }
        );
    }

    #[test]
    fn miss_danger_discipline_refuses() {
        // Unmodeled intrinsic properties refuse at their hop — never
        // mis-answer via chain fallthrough.
        assert!(refused("[1].toLocaleString();").contains("toLocaleString"));
        assert!(matches!(run("function f() {} f.toString;"), InterpOutcome::NoCoverage { .. }));
        assert!(matches!(run("String(function () {});"), InterpOutcome::NoCoverage { .. }));
        assert!(matches!(run("Object.groupBy;"), InterpOutcome::NoCoverage { .. }));
        assert!(matches!(run("Math.random();"), InterpOutcome::NoCoverage { .. }));
        // `match`/`search`/`matchAll` are modeled (S1d/S1e); matchAll returns a
        // %RegExpStringIterator% (iterobj.rs), so it is COVERED, not refused.
        assert!(matches!(run("''.matchAll(',');"), InterpOutcome::Trace(_)));
        assert!(matches!(run("''.normalize();"), InterpOutcome::NoCoverage { .. }));
        assert!(matches!(run("(5).toFixed(2);"), InterpOutcome::NoCoverage { .. }));
        assert!(matches!(run("'a'.localeCompare('b');"), InterpOutcome::NoCoverage { .. }));
        // Symbol.dispose / Symbol.asyncDispose are now MODELED (explicit
        // resource management), so a reference resolves (covered).
        assert!(matches!(run("Symbol.dispose;"), InterpOutcome::Trace(_)));
        assert!(matches!(run("Symbol.asyncDispose;"), InterpOutcome::Trace(_)));
        // A name that IS a realm global we do not model still refuses (we
        // cannot synthesize its value / type / attributes) — never mis-throws.
        assert!(matches!(run("Buffer;"), InterpOutcome::NoCoverage { .. }));
        assert!(matches!(run("typeof Buffer;"), InterpOutcome::NoCoverage { .. }));
        // WeakRef / FinalizationRegistry / Iterator are now MODELED (§26/§27.1),
        // so they cover; WebAssembly remains an unmodeled realm global (refuses).
        assert!(matches!(run("WeakRef;"), InterpOutcome::Trace(_)));
        assert!(matches!(run("WebAssembly;"), InterpOutcome::NoCoverage { .. }));
        // A GENUINELY-undeclared name (not in any environment record, not a
        // realm global) is an unresolvable reference: a bare read throws the
        // exact ReferenceError, `typeof` is "undefined", and a sloppy `delete`
        // is `true` — exactly as every engine.
        assert_eq!(
            completion_of(run("someUnknownGlobal;")),
            Completion::Throw {
                v: ThrownProjection::Error {
                    ctor: Some("Error:ReferenceError".to_string()),
                    name: Some("ReferenceError".to_string()),
                    ctor_name: Some("ReferenceError".to_string()),
                },
                phase: None
            }
        );
        assert_eq!(
            completion_of(run("typeof someUnknownGlobal;")),
            Completion::Normal { v: Some(s("undefined")) }
        );
        assert_eq!(
            completion_of(run("delete someUnknownGlobal;")),
            Completion::Normal { v: Some(b(true)) }
        );
        // `arguments` is context-restricted (an early SyntaxError inside a
        // class field initializer / a direct eval within one — a static rule
        // this interpreter does not enforce), so an UNBOUND `arguments`
        // reference refuses rather than taking the genuine-ReferenceError path
        // and risking a wrong throw where the engine early-errors first.
        assert!(matches!(run("arguments;"), InterpOutcome::NoCoverage { .. }));
        assert!(matches!(run("typeof arguments;"), InterpOutcome::NoCoverage { .. }));
        // `delete` of a name that IS a global-object property (a global
        // `var`/function) still refuses — deleting it would have to remove the
        // configurable property, the global attribute surface this path does
        // not model. Only a TRULY-unresolvable name deletes to `true`.
        assert!(matches!(run("var gv = 1; delete gv;"), InterpOutcome::NoCoverage { .. }));
        assert!(matches!(run("function gf() {} delete gf;"), InterpOutcome::NoCoverage { .. }));
        // Error-instance stack is engine-specific.
        assert!(matches!(run("new Error('x').stack;"), InterpOutcome::NoCoverage { .. }));
        // Reading an interpreter-raised error's message text refuses.
        assert!(matches!(
            run("try { null.x; } catch (e) { e.message; }"),
            InterpOutcome::NoCoverage { .. }
        ));
        // ...but its identity is exact.
        assert_eq!(
            completion_of(run("var t; try { null.x; } catch (e) { t = e instanceof TypeError; } t;")),
            Completion::Normal { v: Some(b(true)) }
        );
        // Out-of-slice syntax surfaces refuse at evaluation. Regex literals
        // and the matcher paths are covered (S1d); generators are covered
        // (S1e) with a tractable body, and refuse (soundly) otherwise.
        assert!(matches!(run("function* g() {}"), InterpOutcome::Trace(_)));
        // BigInt is covered now (arbitrary-precision value model).
        assert!(matches!(run("console.log(10n);"), InterpOutcome::Trace(_)));
        // Tagged templates are modeled: evaluating `` tag`x` `` resolves the
        // callee `tag` first — an undeclared name — so it throws the exact
        // ReferenceError (unresolvable reference), not a refusal.
        assert_eq!(
            completion_of(run("tag`x`;")),
            Completion::Throw {
                v: ThrownProjection::Error {
                    ctor: Some("Error:ReferenceError".to_string()),
                    name: Some("ReferenceError".to_string()),
                    ctor_name: Some("ReferenceError".to_string()),
                },
                phase: None
            }
        );
        // Non-iterables in iteration contexts throw the exact TypeError; a
        // USER @@iterator that returns a non-object throws the exact
        // TypeError at GetIterator (S1e drives the protocol now).
        assert_eq!(
            completion_of(run(
                "var t = false; try { for (var k of ({})) {} } catch (e) { t = e instanceof TypeError; } t;"
            )),
            Completion::Normal { v: Some(b(true)) }
        );
        assert_eq!(
            completion_of(run(
                "var o = {}; o[Symbol.iterator] = function () {}; \
                 var t = false; try { for (var k of o) {} } catch (e) { t = e instanceof TypeError; } t;"
            )),
            Completion::Normal { v: Some(b(true)) }
        );
        // Private class elements are in slice (S1e); generator methods are in
        // slice (S1e); static initialization blocks are now in slice; eval + the
        // Function constructor are in slice (S1f).
        assert!(matches!(run("class C { #p = 1; }"), InterpOutcome::Trace(_)));
        assert!(matches!(run("class C { static { } }"), InterpOutcome::Trace(_)));
        assert!(matches!(
            run("var log = []; class C { static x = 1; static { log.push(this.x); } } log[0];"),
            InterpOutcome::Trace(_)
        ));
        assert!(matches!(run("class C { *g() {} }"), InterpOutcome::Trace(_)));
        assert!(matches!(run("eval('1');"), InterpOutcome::Trace(_)));
        // Sort refusals: impure comparators / object elements.
        assert!(matches!(
            run("var n = 0; [3, 1].sort(function (a, b) { n++; return a - b; });"),
            InterpOutcome::NoCoverage { .. }
        ));
        assert!(matches!(run("[{}, {}].sort();"), InterpOutcome::NoCoverage { .. }));
    }

    #[test]
    fn map_set_s1c() {
        assert_eq!(
            logged(
                "var m = new Map([[1, 'a'], [-0, 'z'], [NaN, 'n']]);\n\
                 console.log(m.size, m.get(1), m.get(0), m.get(-0), m.get(NaN), m.has(2));\n\
                 m.set(1, 'b'); console.log(m.get(1), m.set(9, 'x') === m, m.delete(9), m.delete(9));\n\
                 var order = []; m.forEach(function (v, k, mm) { order.push(v, mm === m); });\n\
                 console.log(order.join(','), typeof m, m instanceof Map);"
            ),
            vec![
                num("3"),
                s("a"),
                s("z"),
                s("z"),
                s("n"),
                b(false),
                s("b"),
                b(true),
                b(true),
                b(false),
                s("b,true,z,true,n,true"),
                s("object"),
                b(true),
            ]
        );
        // Iteration fast paths: for-of / spread / Array.from over pristine
        // maps and sets; entries added mid-iteration are visited.
        assert_eq!(
            logged(
                "var m = new Map([['k', 1]]); m.set('j', 2);\n\
                 var acc = []; for (var e of m) acc.push(e[0], e[1]);\n\
                 var s2 = new Set('aba'); var sp = [...s2];\n\
                 console.log(acc.join(','), s2.size, sp.join(','), Array.from(m).length,\n\
                 new Map(m).size, new Set([1, 1, -0, 0]).size);"
            ),
            vec![s("k,1,j,2"), num("2"), s("a,b"), num("2"), num("2"), num("2")]
        );
        // forEach mutation: additions visited, deletions skipped; clear
        // tombstones in place.
        assert_eq!(
            logged(
                "var m = new Map([[0, 'a'], [1, 'b']]); var log = [];\n\
                 m.forEach(function (v, k) { log.push(k); if (k === 0) m.set(2, 'c'); if (k === 1) m.delete(2); });\n\
                 var m2 = new Map(m); m.clear();\n\
                 console.log(log.join(','), m.size, m2.size);"
            ),
            vec![s("0,1"), num("0"), num("2")]
        );
        // upsert pair (spec side of the audited Node/Bun divergence).
        assert_eq!(
            logged(
                "var m = new Map([[1, 'one']]);\n\
                 console.log(m.getOrInsert(1, 'x'), m.getOrInsert(2, 'two'), m.get(2));\n\
                 var calls = 0;\n\
                 console.log(m.getOrInsertComputed(1, function () { calls++; return 'no'; }), calls);\n\
                 console.log(m.getOrInsertComputed(9, function (k) { return 'k' + k; }),\n\
                 m.getOrInsertComputed(10, function () { m.set(10, 'mut'); return 'win'; }), m.get(10));\n\
                 var t = false; try { m.getOrInsertComputed(11, 'nofn'); } catch (e) { t = e instanceof TypeError; }\n\
                 console.log(t, m.has(11));"
            ),
            vec![
                s("one"),
                s("two"),
                s("two"),
                s("one"),
                num("0"),
                s("k9"),
                s("win"),
                s("win"),
                b(true),
                b(false),
            ]
        );
        // TypeErrors: ctor without new, bad iterables, wrong receivers.
        assert_eq!(
            logged(
                "var t1 = false; try { Map(); } catch (e) { t1 = e instanceof TypeError; }\n\
                 var t2 = false; try { new Map(5); } catch (e) { t2 = e instanceof TypeError; }\n\
                 var t3 = false; try { new Map([1]); } catch (e) { t3 = e instanceof TypeError; }\n\
                 var t4 = false; try { Map.prototype.get.call({}, 1); } catch (e) { t4 = e instanceof TypeError; }\n\
                 var t5 = false; try { new Set().add.call(new Map(), 1); } catch (e) { t5 = e instanceof TypeError; }\n\
                 console.log(t1, t2, t3, t4, t5, new Map(null).size);"
            ),
            vec![b(true), b(true), b(true), b(true), b(true), num("0")]
        );
        // Identities + subclassing + tags.
        assert_eq!(
            logged(
                "console.log(Map.prototype[Symbol.iterator] === Map.prototype.entries,\n\
                 Set.prototype.keys === Set.prototype.values,\n\
                 Set.prototype[Symbol.iterator] === Set.prototype.values,\n\
                 Object.prototype.toString.call(new Map()), Object.prototype.toString.call(new Set()),\n\
                 Map.name, Map.length, Map.prototype.set.length, Map.prototype.getOrInsert.length);\n\
                 class MyMap extends Map {}\n\
                 var mm = new MyMap([[1, 2]]);\n\
                 console.log(mm instanceof MyMap, mm.get(1), Object.getPrototypeOf(mm) === MyMap.prototype);"
            ),
            vec![
                b(true),
                b(true),
                b(true),
                s("[object Map]"),
                s("[object Set]"),
                s("Map"),
                num("0"),
                num("2"),
                num("2"),
                b(true),
                num("2"),
                b(true),
            ]
        );
        // Collection iterator objects now materialize and iterate the live
        // data: appended entries are visited, completion latches, keys===values
        // for Set, @@iterator self-returns, and the class tag is exact.
        assert_eq!(
            completion_of(run(
                "var m = new Map([['a', 1], ['b', 2]]); var it = m.entries();\n\
                 var r0 = it.next(); var ok0 = r0.value[0] === 'a' && r0.value[1] === 1 && !r0.done;\n\
                 m.set('c', 3);\n\
                 var r1 = it.next(); var r2 = it.next(); var r3 = it.next();\n\
                 var ok = ok0 && r1.value[0] === 'b' && r2.value[0] === 'c'\n\
                   && r3.done === true && r3.value === undefined;\n\
                 var s = new Set([1, 2]); var sv = s.values();\n\
                 var sok = sv.next().value === 1 && s.keys().next().value === 1\n\
                   && s.entries().next().value[0] === 1;\n\
                 ok && sok && it[Symbol.iterator]() === it\n\
                   && Object.prototype.toString.call(it) === '[object Map Iterator]'\n\
                   && Object.prototype.toString.call(sv) === '[object Set Iterator]';"
            )),
            Completion::Normal { v: Some(b(true)) }
        );
        // The set-methods surface stays a sound refusal.
        assert!(matches!(run("new Set([1]).union;"), InterpOutcome::NoCoverage { .. }));
        assert!(matches!(run("Map.groupBy;"), InterpOutcome::NoCoverage { .. }));
        // A tampered @@iterator (own or on the prototype) now drives the user
        // protocol: `function () {}` returns undefined → GetIterator TypeError.
        assert_eq!(
            completion_of(run(
                "var m = new Map(); m[Symbol.iterator] = function () {}; \
                 var t = false; try { for (var e of m) {} } catch (e) { t = e instanceof TypeError; } t;"
            )),
            Completion::Normal { v: Some(b(true)) }
        );
        assert_eq!(
            completion_of(run(
                "Map.prototype[Symbol.iterator] = function () {}; \
                 var t = false; try { for (var e of new Map()) {} } catch (e) { t = e instanceof TypeError; } t;"
            )),
            Completion::Normal { v: Some(b(true)) }
        );
    }

    #[test]
    fn user_iterators_s1e() {
        // A plain user iterable drives GetIterator/IteratorStep/IteratorValue
        // through for-of, spread, destructuring, and Array.from.
        let mk = "var mk = function (n) { return { [Symbol.iterator]() { var i = 0; \
                  return { next() { return { value: i, done: i++ >= n }; } }; } }; };\n";
        assert_eq!(
            logged(&format!(
                "{mk}var out = []; for (var x of mk(3)) out.push(x);\n\
                 var sp = [...mk(3)];\n\
                 var [a, b, ...rest] = mk(4);\n\
                 console.log(out.join(','), sp.join(','), a, b, rest.join(','), Array.from(mk(3)).join(','));"
            )),
            vec![s("0,1,2"), s("0,1,2"), num("0"), num("1"), s("2,3"), s("0,1,2")]
        );
        // IteratorClose: a break in for-of over an iterator with `return`
        // calls `return`; the sentinel records it.
        assert_eq!(
            logged(
                "var closed = false;\n\
                 var it = { [Symbol.iterator]() { var i = 0; return {\n\
                   next() { return { value: i++, done: false }; },\n\
                   return() { closed = true; return { done: true }; } }; } };\n\
                 for (var x of it) { if (x === 2) break; }\n\
                 console.log(closed);"
            ),
            vec![b(true)]
        );
        // IteratorClose on an under-consuming destructuring pattern.
        assert_eq!(
            logged(
                "var closed = false;\n\
                 var it = { [Symbol.iterator]() { var i = 0; return {\n\
                   next() { return { value: i++, done: false }; },\n\
                   return() { closed = true; return {}; } }; } };\n\
                 var [p, q] = it;\n\
                 console.log(p, q, closed);"
            ),
            vec![num("0"), num("1"), b(true)]
        );
        // A `return` that returns a non-object throws TypeError at a normal
        // (non-throw) close.
        assert_eq!(
            completion_of(run(
                "var it = { [Symbol.iterator]() { return {\n\
                   next() { return { value: 1, done: false }; },\n\
                   return() { return 5; } }; } };\n\
                 var t = false; try { for (var x of it) break; } catch (e) { t = e instanceof TypeError; } t;"
            )),
            Completion::Normal { v: Some(b(true)) }
        );
        // A throwing body: the original throw wins; `return` is still called
        // but its result (even a throw) is swallowed.
        assert_eq!(
            logged(
                "var closed = false;\n\
                 var it = { [Symbol.iterator]() { return {\n\
                   next() { return { value: 1, done: false }; },\n\
                   return() { closed = true; return {}; } }; } };\n\
                 var caught = '';\n\
                 try { for (var x of it) { throw 'body'; } } catch (e) { caught = e; }\n\
                 console.log(caught, closed);"
            ),
            vec![s("body"), b(true)]
        );
        // new Map / new Set / Object.fromEntries over user iterables.
        assert_eq!(
            logged(&format!(
                "{mk}var entries = {{ [Symbol.iterator]() {{ var i = 0; return {{ next() {{ \
                 return {{ value: [i, i * 10], done: i++ >= 2 }}; }} }}; }} }};\n\
                 var m = new Map(entries); var s2 = new Set(mk(3));\n\
                 console.log(m.get(0), m.get(1), m.size, s2.size);"
            )),
            vec![num("0"), num("10"), num("2"), num("3")]
        );
    }

    #[test]
    fn private_class_elements_s1e() {
        // Fields: read/write via this.#x and obj.#x; NOT own-enumerable (never
        // in Object.keys / JSON / the projection).
        assert_eq!(
            logged(
                "class C { #x = 1; get() { return this.#x; } set(v) { this.#x = v; } }\n\
                 var c = new C();\n\
                 console.log(c.get(), (c.set(9), c.get()), Object.keys(c).length, JSON.stringify(c));"
            ),
            vec![num("1"), num("9"), num("0"), s("{}")]
        );
        // Private methods + accessors (instance + static); shared identity.
        assert_eq!(
            logged(
                "class C {\n\
                   #m() { return 42; }\n\
                   get #y() { return this._y || 0; }\n\
                   set #y(v) { this._y = v * 2; }\n\
                   static #s = 9;\n\
                   run() { this.#y = 5; return [this.#m(), this.#y]; }\n\
                   static get() { return C.#s; }\n\
                 }\n\
                 console.log(new C().run().join(','), C.get());"
            ),
            vec![s("42,10"), num("9")]
        );
        // Brand-check operator; foreign access TypeError; static vs instance
        // brands are distinct.
        assert_eq!(
            logged(
                "class C { #x = 1; static hasX(o) { return #x in o; } m(o) { return o.#x; } }\n\
                 class D { #x = 2; static hasX(o) { return #x in o; } }\n\
                 var c = new C();\n\
                 var t = false; try { c.m({}); } catch (e) { t = e instanceof TypeError; }\n\
                 console.log(C.hasX(c), C.hasX({}), C.hasX(new D()), D.hasX(c), t, c.m(c));"
            ),
            vec![b(true), b(false), b(false), b(false), b(true), num("1")]
        );
        // `#x in <non-object>` throws TypeError.
        assert_eq!(
            completion_of(run(
                "class C { #x = 1; static test() { var t = false; try { #x in 5; } catch (e) { t = e instanceof TypeError; } return t; } } C.test();"
            )),
            Completion::Normal { v: Some(b(true)) }
        );
        // Getter-only private accessor: write throws; setter-only: read throws.
        assert_eq!(
            logged(
                "class C {\n\
                   get #g() { return 3; }\n\
                   set #s(v) {}\n\
                   probe() {\n\
                     var w = false; try { this.#g = 1; } catch (e) { w = e instanceof TypeError; }\n\
                     var r = false; try { this.#s; } catch (e) { r = e instanceof TypeError; }\n\
                     return [this.#g, w, r];\n\
                   }\n\
                 }\n\
                 console.log(new C().probe().join(','));"
            ),
            vec![s("3,true,true")]
        );
        // Private method is not writable.
        assert_eq!(
            completion_of(run(
                "class C { #m() {} t() { var ok = false; try { this.#m = 1; } catch (e) { ok = e instanceof TypeError; } return ok; } } new C().t();"
            )),
            Completion::Normal { v: Some(b(true)) }
        );
        // Compound assignment / update on a private field; arrow field name
        // inference is "#f".
        assert_eq!(
            logged(
                "class C { #n = 10; #f = () => {}; step() { this.#n += 5; this.#n++; return [this.#n, this.#f.name]; } }\n\
                 console.log(new C().step().join(','));"
            ),
            vec![s("16,#f")]
        );
        // Nested class: an inner method references the OUTER private name.
        assert_eq!(
            logged(
                "class Outer { #o = 7; make() { return class Inner { p(x) { return x.#o; } }; } }\n\
                 var I = new Outer().make();\n\
                 console.log(new I().p(new Outer()));"
            ),
            vec![num("7")]
        );
        // Field initializer order (private and public interleave in source
        // order; private methods carry no initializer).
        assert_eq!(
            logged(
                "var log = [];\n\
                 class C { #a = (log.push('a'), 1); #m() {} b = (log.push('b'), 2); }\n\
                 new C();\n\
                 console.log(log.join(','));"
            ),
            vec![s("a,b")]
        );
        // Derived double-brand: super() returning a shared object twice throws.
        assert_eq!(
            completion_of(run(
                "class Base { constructor(o) { return o; } }\n\
                 class D extends Base { #x = 1; constructor(o) { super(o); } }\n\
                 var shared = {}; new D(shared);\n\
                 var t = false; try { new D(shared); } catch (e) { t = e instanceof TypeError; } t;"
            )),
            Completion::Normal { v: Some(b(true)) }
        );
    }

    #[test]
    fn weak_collections_s1c() {
        assert_eq!(
            logged(
                "var wm = new WeakMap(); var k = {};\n\
                 console.log(wm.set(k, 1) === wm, wm.get(k), wm.has(k), wm.delete(k), wm.has(k), wm.get({}));\n\
                 var t1 = false; try { wm.set(1, 2); } catch (e) { t1 = e instanceof TypeError; }\n\
                 var t2 = false; try { new WeakSet().add('x'); } catch (e) { t2 = e instanceof TypeError; }\n\
                 var sym = Symbol('s');\n\
                 var t3 = false; try { new WeakMap().set(Symbol.for('r'), 1); } catch (e) { t3 = e instanceof TypeError; }\n\
                 console.log(t1, t2, new WeakMap().set(sym, 9).get(sym), t3,\n\
                 wm.has(1), wm.delete('z'), new WeakMap([[k, 2]]).get(k));\n\
                 var ws = new WeakSet([k]);\n\
                 console.log(ws.has(k), ws.add(k) === ws, ws.delete(k), ws.has(k),\n\
                 Object.prototype.toString.call(new WeakMap()), new WeakMap().getOrInsert(k, 5));"
            ),
            vec![
                b(true),
                num("1"),
                b(true),
                b(true),
                b(false),
                ProjectedValue::Undefined,
                b(true),
                b(true),
                num("9"),
                b(true),
                b(false),
                b(false),
                num("2"),
                b(true),
                b(true),
                b(true),
                b(false),
                s("[object WeakMap]"),
                num("5"),
            ]
        );
    }

    #[test]
    fn date_s1c() {
        // The driver's deterministic clock: Date.now / new Date() / Date()
        // share one tick stream from the fixed epoch.
        assert_eq!(
            logged("console.log(Date.now(), new Date().getTime(), Date.now());"),
            vec![num("1700000000001"), num("1700000000002"), num("1700000000003")]
        );
        assert_eq!(
            logged("console.log(Date());"),
            vec![s("Tue Nov 14 2023 22:13:20 GMT+0000 (Coordinated Universal Time)")]
        );
        // Constructor forms + getters (TZ pinned to UTC: local == UTC).
        assert_eq!(
            logged(
                "var d = new Date(2023, 5, 15, 12, 30, 45, 678);\n\
                 console.log(d.getFullYear(), d.getMonth(), d.getDate(), d.getDay(), d.getHours(),\n\
                 d.getMinutes(), d.getSeconds(), d.getMilliseconds(), d.getTimezoneOffset(),\n\
                 d.getUTCHours(), d.getTime() === d.valueOf());\n\
                 console.log(new Date(99, 0).getFullYear(), new Date(2023, 13, 32, 25, 61, 61, 1001).toISOString(),\n\
                 new Date(1.5).getTime(), new Date(8.64e15 + 1).getTime(), new Date(new Date(5)).getTime());"
            ),
            vec![
                num("2023"),
                num("5"),
                num("15"),
                num("4"),
                num("12"),
                num("30"),
                num("45"),
                num("678"),
                num("0"),
                num("12"),
                b(true),
                num("1999"),
                s("2024-03-04T02:02:02.001Z"),
                num("1"),
                num("NaN"),
                num("5"),
            ]
        );
        // Setters, Annex B, strings, toJSON.
        assert_eq!(
            logged(
                "var d = new Date(2023, 0, 15);\n\
                 d.setFullYear(2024, 5, 20);\n\
                 console.log(d.toISOString(), d.setTime(123), new Date(NaN).setHours(5));\n\
                 var inv = new Date(NaN); inv.setFullYear(2023);\n\
                 console.log(inv.toISOString(), new Date(NaN).toString(), new Date(NaN).toJSON());\n\
                 var t = false; try { new Date(NaN).toISOString(); } catch (e) { t = e instanceof RangeError; }\n\
                 console.log(t, JSON.stringify(new Date(5)), new Date(1999, 0).getYear(),\n\
                 new Date(5).toUTCString(), Date.prototype.toGMTString === Date.prototype.toUTCString);"
            ),
            vec![
                s("2024-06-20T00:00:00.000Z"),
                num("123"),
                num("NaN"),
                s("2023-01-01T00:00:00.000Z"),
                s("Invalid Date"),
                ProjectedValue::Null,
                b(true),
                s("\\\"1970-01-01T00:00:00.005Z\\\""),
                num("99"),
                s("Thu, 01 Jan 1970 00:00:00 GMT"),
                b(true),
            ]
        );
        // Date.parse: exact ISO grammar; UTC/local/offset forms; rollover.
        assert_eq!(
            logged(
                "console.log(Date.parse('2023-11-14T22:13:20.123Z'), Date.parse('2023-11-14'),\n\
                 Date.parse('2023-11-14T22:13:20'), Date.parse('2023-11-14T22:13:20+05:30'),\n\
                 Date.parse('2023-02-29'), Date.parse('+275760-09-13T00:00:00.000Z'), Date.parse('2023'),\n\
                 new Date('2023-11-14').getTime(), Date.UTC(2023, 0), Date.UTC(), Date.UTC(99, 0));"
            ),
            vec![
                num("1700000000123"),
                num("1699920000000"),
                num("1700000000000"),
                num("1699980200000"),
                num("1677628800000"),
                num("8640000000000000"),
                num("1672531200000"),
                num("1699920000000"),
                num("1672531200000"),
                num("NaN"),
                num("915148800000"),
            ]
        );
        // The wrapper surface (driver firewall observables).
        assert_eq!(
            logged(
                "console.log(Date.length, Date.name, Object.getOwnPropertyNames(Date).join(','),\n\
                 Date.prototype.constructor === Date, Date.prototype.constructor.length,\n\
                 Date.prototype.constructor.parse === Date.parse, typeof Date.prototype.constructor.now);\n\
                 class D extends Date { constructor() { super(7); } }\n\
                 var d = new D();\n\
                 console.log(Object.getPrototypeOf(d) === Date.prototype, d instanceof D, d instanceof Date, d.getTime());"
            ),
            vec![
                num("0"),
                s("Date"),
                s("length,name,prototype,now,parse,UTC"),
                b(false),
                num("7"),
                b(true),
                s("function"),
                b(true),
                b(false),
                b(true),
                num("7"),
            ]
        );
        // @@toPrimitive: default hint is STRING for dates.
        assert_eq!(
            logged(
                "var d = new Date(5);\n\
                 console.log(d + '!', +d, `${d}`.length > 10, d[Symbol.toPrimitive]('number'),\n\
                 Date.prototype[Symbol.toPrimitive].name);\n\
                 var t = false; try { d[Symbol.toPrimitive]('other'); } catch (e) { t = e instanceof TypeError; }\n\
                 var t2 = false; try { Date.prototype.getTime.call({}); } catch (e) { t2 = e instanceof TypeError; }\n\
                 console.log(t, t2);"
            ),
            vec![
                s("Thu Jan 01 1970 00:00:00 GMT+0000 (Coordinated Universal Time)!"),
                num("5"),
                b(true),
                num("5"),
                s("[Symbol.toPrimitive]"),
                b(true),
                b(true),
            ]
        );
        // Projection: a Date instance has NO own properties.
        let c = completion_of(run("new Date(5);"));
        let Completion::Normal {
            v: Some(ProjectedValue::Obj { cls, props, .. }),
        } = c
        else {
            panic!("expected date object completion");
        };
        assert_eq!(cls.as_deref(), Some("Date"));
        assert_eq!(props.expect("props"), vec![]);
        // Refusals: real-clock paths, non-ISO parse, locale surface.
        assert!(matches!(
            run("new (Date.prototype.constructor)();"),
            InterpOutcome::NoCoverage { .. }
        ));
        assert!(matches!(
            run("Date.prototype.constructor.now();"),
            InterpOutcome::NoCoverage { .. }
        ));
        assert!(matches!(run("Date.parse('Nov 14 2023');"), InterpOutcome::NoCoverage { .. }));
        assert!(matches!(run("new Date('11/14/2023');"), InterpOutcome::NoCoverage { .. }));
        assert!(matches!(
            run("Date.parse('2023-11-14T22:13:20.1Z');"),
            InterpOutcome::NoCoverage { .. }
        ));
        assert!(matches!(run("new Date(5).toLocaleString();"), InterpOutcome::NoCoverage { .. }));
    }

    #[test]
    fn json_s1c() {
        // Full parse: values, ordering (integer keys first), duplicates
        // last-win, escapes, exactness of numbers.
        assert_eq!(
            logged(
                "var o = JSON.parse('{\"b\": 1, \"0\": \"z\", \"a\": [1.5e2, true, null], \"b\": 2}');\n\
                 console.log(Object.keys(o).join(','), o.b, o.a.length, o.a[0], JSON.parse('\"\\\\u0041\\\\n\"'),\n\
                 JSON.parse('-0'), 1 / JSON.parse('-0'), JSON.parse('1e-7'), JSON.parse('  [ ]  ').length);"
            ),
            vec![
                s("0,b,a"),
                num("2"),
                num("3"),
                num("150"),
                s("A\\u000a"),
                num("-0"),
                num("-Infinity"),
                num("1e-7"),
                num("0"),
            ]
        );
        // Parse SyntaxErrors are exact.
        assert_eq!(
            logged(
                "var ts = [];\n\
                 for (var src of ['{', '01', '[1,]', '{\"a\":}', 'undefined', \"'x'\", '1 2', '\\\"a', '{a:1}']) {\n\
                 try { JSON.parse(src); ts.push('ok'); } catch (e) { ts.push(e instanceof SyntaxError); }\n\
                 }\n\
                 console.log(ts.join(','));"
            ),
            vec![s("true,true,true,true,true,true,true,true,true")]
        );
        // Reviver: walk order, this-binding, deletion via undefined, and the
        // shipped source-context third argument.
        assert_eq!(
            logged(
                "var log = [];\n\
                 var r = JSON.parse('{\"a\": 1, \"b\": [2, 3]}', function (k, v) {\n\
                 log.push(k + ':' + (arguments.length) + ':' + (arguments[2] && arguments[2].source));\n\
                 if (k === 'a') return undefined;\n\
                 return typeof v === 'number' ? v * 10 : v;\n\
                 });\n\
                 console.log(log.join('|'), 'a' in r, r.b.join(','));"
            ),
            vec![
                s("a:3:1|0:3:2|1:3:3|b:3:undefined|:3:undefined"),
                b(false),
                s("20,30"),
            ]
        );
        // Source dropped for values mutated before their visit.
        assert_eq!(
            logged(
                "var srcs = [];\n\
                 JSON.parse('[1, 2, 3]', function (k, v) {\n\
                 if (k === '0') this[1] = 99;\n\
                 srcs.push(arguments[2].source);\n\
                 return v;\n\
                 });\n\
                 console.log(srcs.join(','));"
            ),
            vec![s("1,,3,")]
        );
        // Full stringify: space forms, replacer array/function, toJSON,
        // wrappers, cycles, holes.
        assert_eq!(
            logged(
                "console.log(JSON.stringify({a: 1, b: [1, {c: 2}]}, null, 2));\n\
                 console.log(JSON.stringify([1, 'a'], null, '--'), JSON.stringify({a: {b: 1}}, null, 12));\n\
                 console.log(JSON.stringify({a: 1, b: 2, 0: 'z'}, ['b', 'a', 'b', new String('a'), new Number(0)]));\n\
                 console.log(JSON.stringify({a: 1, b: [2, 3]}, function (k, v) { return typeof v === 'number' ? v * 10 : v; }));\n\
                 console.log(JSON.stringify({t: {toJSON: function (key) { return [key, this !== undefined]; }}}));\n\
                 console.log(JSON.stringify(undefined), JSON.stringify(function () {}),\n\
                 JSON.stringify({u: undefined, f: function () {}, s: Symbol('x')}),\n\
                 JSON.stringify([undefined, function () {}, Symbol('x')]),\n\
                 JSON.stringify(new Number(5)), JSON.stringify(new String('q')), JSON.stringify(new Boolean(true)),\n\
                 JSON.stringify(-0), JSON.stringify({a: [, 2]}), JSON.stringify([1], [], 4), JSON.stringify(5, 'notafn'));"
            ),
            vec![
                s("{\\u000a  \\\"a\\\": 1,\\u000a  \\\"b\\\": [\\u000a    1,\\u000a    {\\u000a      \\\"c\\\": 2\\u000a    }\\u000a  ]\\u000a}"),
                s("[\\u000a--1,\\u000a--\\\"a\\\"\\u000a]"),
                s("{\\u000a          \\\"a\\\": {\\u000a                    \\\"b\\\": 1\\u000a          }\\u000a}"),
                s("{\\\"b\\\":2,\\\"a\\\":1,\\\"0\\\":\\\"z\\\"}"),
                s("{\\\"a\\\":10,\\\"b\\\":[20,30]}"),
                s("{\\\"t\\\":[\\\"t\\\",true]}"),
                ProjectedValue::Undefined,
                ProjectedValue::Undefined,
                s("{}"),
                s("[null,null,null]"),
                s("5"),
                s("\\\"q\\\""),
                s("true"),
                s("0"),
                s("{\\\"a\\\":[null,2]}"),
                s("[\\u000a    1\\u000a]"),
                s("5"),
            ]
        );
        // Cycle detection (BigInt literals are out of slice, so the BigInt
        // TypeError path is exercised only by corpus cases that refuse
        // earlier).
        assert_eq!(
            logged(
                "var c = {}; c.self = c;\n\
                 var t2 = false; try { JSON.stringify(c); } catch (e) { t2 = e instanceof TypeError; }\n\
                 var deep = { a: [{ b: {} }] }; deep.a[0].b.back = deep;\n\
                 var t3 = false; try { JSON.stringify(deep); } catch (e) { t3 = e instanceof TypeError; }\n\
                 var shared = {}; var ok = JSON.stringify([shared, shared]);\n\
                 console.log(t2, t3, ok, JSON.stringify(NaN), JSON.stringify(Infinity), JSON.stringify(5e-324));"
            ),
            vec![b(true), b(true), s("[{},{}]"), s("null"), s("null"), s("5e-324")]
        );
    }

    #[test]
    fn regexp_skeleton_s1c() {
        // Literals are real objects: identity, accessors, toString,
        // lastIndex, flags in canonical order.
        assert_eq!(
            logged(
                "var r = /ab/g;\n\
                 console.log(typeof r, r instanceof RegExp, r.constructor === RegExp,\n\
                 r.source, r.flags, r.global, r.sticky, r.lastIndex, /a\\/b/.source, /[/]/.source,\n\
                 /a/dgimsuy.flags, /a/v.unicodeSets, '' + /x/gi, /ab/gi.toString(),\n\
                 Object.prototype.toString.call(/x/));\n\
                 r.lastIndex = 42; console.log(r.lastIndex);\n\
                 var d = Object.getOwnPropertyDescriptor(r, 'lastIndex');\n\
                 console.log(d.value, d.writable, d.enumerable, d.configurable,\n\
                 Object.getOwnPropertyNames(r).join(','), JSON.stringify(/x/));"
            ),
            vec![
                s("object"),
                b(true),
                b(true),
                s("ab"),
                s("g"),
                b(true),
                b(false),
                num("0"),
                s("a\\\\/b"),
                s("[/]"),
                s("dgimsuy"),
                b(true),
                s("/x/gi"),
                s("/ab/gi"),
                s("[object RegExp]"),
                num("42"),
                num("42"),
                b(true),
                b(false),
                b(false),
                s("lastIndex"),
                s("{}"),
            ]
        );
        // Prototype accessor semantics: undefined on the proto, TypeError on
        // foreign receivers, flags getter reads properties via Get.
        assert_eq!(
            logged(
                "console.log(RegExp.prototype.source, RegExp.prototype.flags, RegExp.prototype.global);\n\
                 var g = Object.getOwnPropertyDescriptor(RegExp.prototype, 'source').get;\n\
                 console.log(g.name, g.length);\n\
                 var t1 = false; try { g.call({}); } catch (e) { t1 = e instanceof TypeError; }\n\
                 var fl = Object.getOwnPropertyDescriptor(RegExp.prototype, 'flags').get;\n\
                 console.log(t1, fl.call({ global: true, multiline: 1, sticky: 'y' }),\n\
                 typeof RegExp, RegExp.name, RegExp.length);"
            ),
            vec![
                s("(?:)"),
                s(""),
                ProjectedValue::Undefined,
                s("get source"),
                num("0"),
                b(true),
                s("gmy"),
                s("function"),
                s("RegExp"),
                num("2"),
            ]
        );
        // The regex-literal projection carries the nonenum lastIndex.
        let c = completion_of(run("/ab/g;"));
        let Completion::Normal {
            v: Some(ProjectedValue::Obj { cls, props, .. }),
        } = c
        else {
            panic!("expected regex object completion");
        };
        assert_eq!(cls.as_deref(), Some("RegExp"));
        assert_eq!(
            props.expect("props"),
            vec![(
                PropKey::Str("lastIndex".to_string()),
                ProjectedValue::Nonenum { v: Box::new(num("0")) }
            )]
        );
        // S1d: the matcher paths and the constructor are LIVE; @@matchAll now
        // returns a %RegExpStringIterator% (S1e). The legacy statics still refuse.
        assert!(matches!(run("/a/.exec('a');"), InterpOutcome::Trace(_)));
        assert!(matches!(run("/a/.test('a');"), InterpOutcome::Trace(_)));
        assert!(matches!(run("'a'.split(/a/);"), InterpOutcome::Trace(_)));
        assert!(matches!(run("'a'.replace(/a/, 'b');"), InterpOutcome::Trace(_)));
        assert!(matches!(run("new RegExp('a');"), InterpOutcome::Trace(_)));
        assert!(matches!(run("'abc'.match(/b/);"), InterpOutcome::Trace(_)));
        assert!(matches!(run("'abc'.search(/c/);"), InterpOutcome::Trace(_)));
        assert!(matches!(run("/x/[Symbol.matchAll]('x');"), InterpOutcome::Trace(_)));
        assert!(matches!(run("[...'xax'.matchAll(/x/g)].length;"), InterpOutcome::Trace(_)));
        assert!(matches!(run("RegExp.$1;"), InterpOutcome::NoCoverage { .. }));
        assert!(matches!(run("RegExp.escape;"), InterpOutcome::NoCoverage { .. }));
        // A regex argument makes includes/startsWith throw the exact
        // TypeError (IsRegExp through the modeled @@match).
        assert_eq!(
            completion_of(run(
                "var t = false; try { 'a'.includes(/a/); } catch (e) { t = e instanceof TypeError; } t;"
            )),
            Completion::Normal { v: Some(b(true)) }
        );
    }

    #[test]
    fn proxy_and_uri_s1c() {
        // Proxy: binding modeled, call-without-new TypeError is exact,
        // construction refuses (ruled out of S1c).
        assert_eq!(
            logged(
                "var t = false; try { Proxy({}, {}); } catch (e) { t = e instanceof TypeError; }\n\
                 console.log(typeof Proxy, Proxy.name, Proxy.length, t,\n\
                 Object.getOwnPropertyDescriptor(Proxy, 'prototype'));"
            ),
            vec![
                s("function"),
                s("Proxy"),
                num("2"),
                b(true),
                ProjectedValue::Undefined,
            ]
        );
        // Proxy construction is now live (§10.5 trap dispatch): a proxy with an
        // empty handler forwards to its target's ordinary internal methods.
        assert_eq!(
            logged(
                "var t = { a: 1 }; var p = new Proxy(t, {});\n\
                 console.log(p.a, 'a' in p, typeof Proxy.revocable);"
            ),
            vec![num("1"), b(true), s("function")]
        );
        // A get trap is invoked with (target, key, receiver).
        assert_eq!(
            logged(
                "var log = [];\n\
                 var p = new Proxy({ x: 5 }, { get(t, k, r) { log.push(k); return 42; } });\n\
                 console.log(p.x, p.y, log.join(','), r_ok(p));\n\
                 function r_ok(px) { return Reflect.get(px, 'x') === 42; }"
            ),
            vec![num("42"), num("42"), s("x,y"), b(true)]
        );
        // URI functions: exact encode/decode + URIError battery.
        assert_eq!(
            logged(
                "console.log(encodeURIComponent(\"Aa0-_.!~*'()\"), encodeURIComponent('#;/?:@&=+$,'),\n\
                 encodeURI('#;/?:@&=+$,'), encodeURI('a b'), encodeURIComponent('\\u00e9'),\n\
                 decodeURIComponent('%41%42'), decodeURI('a%20b%2Fc'), decodeURIComponent('a%20b%2Fc'),\n\
                 decodeURIComponent('%c3%a9'), encodeURI.name, encodeURI.length);"
            ),
            vec![
                s("Aa0-_.!~*'()"),
                s("%23%3B%2F%3F%3A%40%26%3D%2B%24%2C"),
                s("#;/?:@&=+$,"),
                s("a%20b"),
                s("%C3%A9"),
                s("AB"),
                s("a b%2Fc"),
                s("a b/c"),
                s("\\u00e9"),
                s("encodeURI"),
                num("1"),
            ]
        );
        assert_eq!(
            logged(
                "var t = [];\n\
                 function tc(f) { try { f(); t.push('ok'); } catch (e) { t.push(e instanceof URIError); } }\n\
                 tc(function () { encodeURIComponent('\\ud800'); });\n\
                 tc(function () { decodeURIComponent('%'); });\n\
                 tc(function () { decodeURIComponent('%C0%80'); });\n\
                 tc(function () { decodeURIComponent('%ED%A0%80'); });\n\
                 console.log(t.join(','));"
            ),
            vec![s("true,true,true,true")]
        );
    }

    #[test]
    fn strict_early_errors_are_exact_syntax_error_traces() {
        let is_syntax_throw = |o: InterpOutcome| -> bool {
            matches!(
                o,
                InterpOutcome::Trace(t) if t.completion == Completion::Throw {
                    v: ThrownProjection::Error {
                        ctor: Some("Error:SyntaxError".to_string()),
                        name: Some("SyntaxError".to_string()),
                        ctor_name: Some("SyntaxError".to_string()),
                    },
                    phase: None,
                }
            )
        };
        assert!(is_syntax_throw(run("\"use strict\";\nvar eval = 1;")));
        assert!(is_syntax_throw(run("\"use strict\";\narguments++;")));
        assert!(is_syntax_throw(run("(function eval() { 'use strict'; });")));
        assert!(is_syntax_throw(run("try { } catch (x) { let x; }")));
        // The strict_prefix path matches the driver's prepending.
        assert!(is_syntax_throw(evaluate_case_opts(&[], "var eval = 1;", true, true)));
    }

    #[test]
    fn arguments_object_exact() {
        // Mapped: aliasing both ways, delete unmaps, length/callee shape.
        assert_eq!(
            logged(
                "function f(a, b) {\n\
                 a = 42; console.log(arguments[0]);\n\
                 arguments[1] = 7; console.log(b);\n\
                 delete arguments[0]; a = 9; console.log(arguments[0], arguments.length, arguments.callee === f);\n\
                 }\n\
                 f(1, 2);"
            ),
            vec![
                num("42"),
                num("7"),
                ProjectedValue::Undefined,
                num("2"),
                b(true),
            ]
        );
        // Duplicate params: only the last occurrence maps.
        assert_eq!(
            logged("function d(x, x) { x = 99; console.log(arguments[0], arguments[1]); } d(1, 2);"),
            vec![num("1"), num("99")]
        );
        // Unmapped (strict): no aliasing; callee is a throwing accessor.
        assert_eq!(
            logged(
                "function s(a) { 'use strict'; a = 5; console.log(arguments[0]);\n\
                 var t = false; try { arguments.callee; } catch (e) { t = e instanceof TypeError; }\n\
                 console.log(t); }\n\
                 s(1);"
            ),
            vec![num("1"), b(true)]
        );
        // Non-simple parameter lists are unmapped even sloppy.
        assert_eq!(
            logged("function n(a, b = 0) { a = 5; console.log(arguments[0]); } n(1);"),
            vec![num("1")]
        );
        // Projection carries the @@iterator symbol prop and callee.
        let c = completion_of(run("(function (x) { return arguments; })(1);"));
        let Completion::Normal {
            v: Some(ProjectedValue::Obj { cls, props, .. }),
        } = c
        else {
            panic!("expected arguments object");
        };
        assert_eq!(cls.as_deref(), Some("Object"));
        let props = props.expect("props");
        assert_eq!(props[0], (PropKey::Str("0".to_string()), num("1")));
        assert_eq!(
            props[1],
            (
                PropKey::Str("length".to_string()),
                ProjectedValue::Nonenum { v: Box::new(num("1")) }
            )
        );
        assert!(matches!(
            &props[2],
            (PropKey::Str(k), ProjectedValue::Nonenum { v }) if k == "callee"
                && matches!(v.as_ref(), ProjectedValue::Fun { .. })
        ));
        assert!(matches!(
            &props[3],
            (PropKey::Sym { sym }, ProjectedValue::Nonenum { v })
                if matches!(sym.as_ref(), ProjectedValue::Sym { wk: Some(w), .. } if w == "Symbol.iterator")
                    && matches!(v.as_ref(), ProjectedValue::Fun { name: Some(n) } if n == "values")
        ));
        // `typeof arguments` at script top level is exact only when bound.
        assert_eq!(
            completion_of(run("var arguments = 41; arguments + 1;")),
            Completion::Normal { v: Some(num("42")) }
        );
    }

    #[test]
    fn descriptors_defineproperty_delete() {
        assert_eq!(
            logged(
                "var o = {};\n\
                 Object.defineProperty(o, 'x', { value: 1, writable: false, enumerable: false, configurable: true });\n\
                 var d = Object.getOwnPropertyDescriptor(o, 'x');\n\
                 console.log(d.value, d.writable, d.enumerable, d.configurable);\n\
                 o.x = 9; console.log(o.x);\n\
                 var t = false; try { (function(){'use strict'; o.x = 9;})(); } catch (e) { t = e instanceof TypeError; }\n\
                 console.log(t, delete o.x, o.x);"
            ),
            vec![
                num("1"),
                b(false),
                b(false),
                b(true),
                num("1"),
                b(true),
                b(true),
                ProjectedValue::Undefined,
            ]
        );
        // Getter/setter via defineProperty + literal accessors.
        assert_eq!(
            logged(
                "var log = []; var o = { get p() { return 7; }, set p(v) { log.push(v); } };\n\
                 console.log(o.p); o.p = 3; console.log(log[0]);\n\
                 var d = Object.getOwnPropertyDescriptor(o, 'p');\n\
                 console.log(typeof d.get, typeof d.set, d.get.name, d.set.name, d.enumerable);"
            ),
            vec![
                num("7"),
                num("3"),
                s("function"),
                s("function"),
                s("get p"),
                s("set p"),
                b(true),
            ]
        );
        // Object.keys / getOwnPropertyNames order; function own-key order.
        assert_eq!(
            logged(
                "var o = { b: 1, 0: 'z', a: 2 };\n\
                 console.log(Object.keys(o).join(','), Object.getOwnPropertyNames(function f(x){}).join(','));"
            ),
            vec![s("0,b,a"), s("length,name,prototype")]
        );
        // Non-extensible objects reject creates.
        assert_eq!(
            logged(
                "var o = {}; Object.preventExtensions(o); o.x = 1;\n\
                 console.log(o.x, Object.isExtensible(o));"
            ),
            vec![ProjectedValue::Undefined, b(false)]
        );
    }

    #[test]
    fn array_exotic_length() {
        assert_eq!(
            logged(
                "var a = [1, 2, 3]; a.length = 1; console.log(a.length, a[1]);\n\
                 a[5] = 9; console.log(a.length);\n\
                 var t = false; try { a.length = -1; } catch (e) { t = e instanceof RangeError; }\n\
                 console.log(t);"
            ),
            vec![num("1"), ProjectedValue::Undefined, num("6"), b(true)]
        );
        // push/pop/indexOf/slice/join/concat basics.
        assert_eq!(
            logged(
                "var a = [1, 2]; a.push(3); console.log(a.join('-'), a.pop(), a.indexOf(2), \
                 a.slice(0, 1).length, a.concat([4, 5]).join(','), [].indexOf(1));"
            ),
            vec![s("1-2-3"), num("3"), num("1"), num("1"), s("1,2,4,5"), num("-1")]
        );
        // Inherited elements are consulted through the chain.
        assert_eq!(
            logged(
                "Array.prototype[1] = 9; var x = [0]; x.length = 2;\n\
                 var s2 = x.slice();\n\
                 console.log(s2.hasOwnProperty('1'), s2[1], x.indexOf(9), x.pop(), x.length);"
            ),
            vec![b(true), num("9"), num("1"), num("9"), num("1")]
        );
    }

    #[test]
    fn destructuring_and_spread() {
        assert_eq!(
            logged(
                "var [a, , b = 10, ...r] = [1, 2, undefined, 4, 5];\n\
                 var { x, y: z = 3, ...rest } = { x: 1, w: 9 };\n\
                 console.log(a, b, r.join(','), x, z, rest.w);"
            ),
            vec![num("1"), num("10"), s("4,5"), num("1"), num("3"), num("9")]
        );
        // String iteration is by code points.
        assert_eq!(
            logged("var [c1, c2] = 'a\\u{1F600}b'; console.log(c1, c2.length);"),
            vec![s("a"), num("2")]
        );
        // Spread in calls and array literals.
        assert_eq!(
            logged(
                "function f(a, b, c) { return a + b + c; }\n\
                 console.log(f(...[1, 2, 3]), [0, ...[1, 2], 3].join(''), ({ ...{ a: 1 }, b: 2 }).a);"
            ),
            vec![num("6"), s("0123"), num("1")]
        );
        // Destructuring assignment to member targets.
        assert_eq!(
            logged("var o = {}; [o.a, o.b] = [1, 2]; ({ c: o.c } = { c: 3 }); console.log(o.a, o.b, o.c);"),
            vec![num("1"), num("2"), num("3")]
        );
    }

    #[test]
    fn loops_labels_switch() {
        assert_eq!(
            logged(
                "var s2 = 0; for (var i = 0; i < 10; i++) { s2 += i; }\n\
                 var j = 0; while (j < 3) j++; do j--; while (j > 1);\n\
                 console.log(s2, i, j);"
            ),
            vec![num("45"), num("10"), num("1")]
        );
        assert_eq!(
            logged(
                "var out = [];\n\
                 outer: for (var a = 0; a < 3; a++) {\n\
                   for (var b2 = 0; b2 < 3; b2++) {\n\
                     if (b2 === 1) continue outer;\n\
                     if (a === 2) break outer;\n\
                     out.push(a * 10 + b2);\n\
                   }\n\
                 }\n\
                 console.log(out.join(','));"
            ),
            vec![s("0,10")]
        );
        assert_eq!(
            logged(
                "function f(x) { switch (x) { case 1: return 'one'; case 2: return 'two'; default: return 'many'; } }\n\
                 var fall = [];\n\
                 switch (2) { case 1: fall.push(1); case 2: fall.push(2); case 3: fall.push(3); break; case 4: fall.push(4); }\n\
                 console.log(f(1), f(2), f(9), fall.join(','));"
            ),
            vec![s("one"), s("two"), s("many"), s("2,3")]
        );
        // for-in order and shadowing.
        assert_eq!(
            logged(
                "var p = { a: 1 }; var o = { __proto__: p, 2: 'x', b: 2 };\n\
                 var ks = []; for (var k in o) ks.push(k); console.log(ks.join(','));"
            ),
            vec![s("2,b,a")]
        );
        // for-of over arrays and strings.
        assert_eq!(
            logged(
                "var acc = []; for (var v of [10, 20]) acc.push(v);\n\
                 for (var ch of 'ab') acc.push(ch);\n\
                 console.log(acc.join(','));"
            ),
            vec![s("10,20,a,b")]
        );
    }

    #[test]
    fn try_catch_finally_semantics() {
        assert_eq!(
            logged(
                "var r = []; try { r.push('t'); throw 7; } catch (e) { r.push(e); } finally { r.push('f'); }\n\
                 console.log(r.join(','));"
            ),
            vec![s("t,7,f")]
        );
        // finally overrides with its own abrupt completion.
        assert_eq!(
            completion_of(run(
                "(function () { try { return 1; } finally { return 2; } })();"
            )),
            Completion::Normal { v: Some(num("2")) }
        );
        // Catch-less finally re-throws.
        assert_eq!(
            completion_of(run("try { throw 'x'; } finally { 1; }")),
            Completion::Throw {
                v: ThrownProjection::Prim { v: s("x") },
                phase: None
            }
        );
        // Destructuring catch parameter.
        assert_eq!(
            logged("try { throw { code: 42 }; } catch ({ code }) { console.log(code); }"),
            vec![num("42")]
        );
    }

    #[test]
    fn templates_and_optional_chaining() {
        assert_eq!(
            logged(
                "var x = 6; console.log(`a${x * 7}b`, `line1\nline2`.length, `${'q'}`);"
            ),
            vec![s("a42b"), num("11"), s("q")]
        );
        assert_eq!(
            logged(
                "var o = { a: { b: 1 }, f: function () { return 2; } };\n\
                 var n = null;\n\
                 console.log(o?.a?.b, n?.a?.b, n?.f(), o.f?.(), o.missing?.());"
            ),
            vec![
                num("1"),
                ProjectedValue::Undefined,
                ProjectedValue::Undefined,
                num("2"),
                ProjectedValue::Undefined,
            ]
        );
    }

    #[test]
    fn reference_semantics() {
        // Compound assignment coerces the key at GetValue AND PutValue.
        assert_eq!(
            logged(
                "var n = 0; var o = {}; var p = { toString: function () { n++; return 'k'; } };\n\
                 o[p] += 1; var m = 0; var q = { toString: function () { m++; return 'j'; } };\n\
                 o[q] = 1; console.log(n, m);"
            ),
            vec![num("2"), num("1")]
        );
        // Null base: key + rhs evaluate before PutValue's TypeError.
        assert_eq!(
            logged(
                "var order = []; function k() { order.push('k'); return 'p'; }\n\
                 var base = null; var t = false;\n\
                 try { base[k()] = order.push('rhs'); } catch (e) { t = e instanceof TypeError; }\n\
                 console.log(t, order.join(','));"
            ),
            vec![b(true), s("k,rhs")]
        );
        // instanceof: primitive LHS before prototype read.
        assert_eq!(
            logged(
                "function F() {} var t = false;\n\
                 F.prototype = 5;\n\
                 try { ({}) instanceof F; } catch (e) { t = e instanceof TypeError; }\n\
                 console.log(0 instanceof F, t);"
            ),
            vec![b(false), b(true)]
        );
        // in operator.
        assert_eq!(
            logged("var o = { a: 1 }; console.log('a' in o, 'b' in o, '0' in [7], 'length' in []);"),
            vec![b(true), b(false), b(true), b(true)]
        );
    }

    #[test]
    fn wrappers_and_call_apply_bind() {
        assert_eq!(
            logged(
                "function who() { return typeof this; }\n\
                 console.log(who.call(5), who.call('x'), who.call(null),\n\
                 Object.prototype.toString.call(5), Object.prototype.toString.call([]),\n\
                 Object.prototype.toString.call(null), Object.prototype.toString.call(undefined));"
            ),
            vec![
                s("object"),
                s("object"),
                s("object"),
                s("[object Number]"),
                s("[object Array]"),
                s("[object Null]"),
                s("[object Undefined]"),
            ]
        );
        assert_eq!(
            logged(
                "function add(a, b) { return this.base + a + b; }\n\
                 var bound = add.bind({ base: 100 }, 1);\n\
                 console.log(bound(2), bound.name, bound.length,\n\
                 add.apply({ base: 10 }, [1, 2]), add.call({ base: 20 }, 1, 2));"
            ),
            vec![num("103"), s("bound add"), num("1"), num("13"), num("23")]
        );
        // new String/Number/Boolean wrappers.
        assert_eq!(
            logged(
                "var w = new String('ab');\n\
                 console.log(typeof w, w.length, w[0], w.valueOf(), (new Number(5)).valueOf(), (new Boolean(false)).valueOf());"
            ),
            vec![s("object"), num("2"), s("a"), s("ab"), num("5"), b(false)]
        );
    }

    #[test]
    fn new_and_constructors() {
        assert_eq!(
            logged(
                "function A(x) { this.x = x; } var a = new A(7);\n\
                 console.log(a instanceof A, a.x, a.constructor === A);\n\
                 function B() { return { y: 1 }; } console.log(new B().y);\n\
                 function C() { console.log(new.target === C); } new C(); C();"
            ),
            vec![b(true), num("7"), b(true), num("1"), b(true), b(false)]
        );
        // Methods and arrows are not constructors (exact TypeError).
        assert_eq!(
            logged(
                "var o = { m() {} }; var t1 = false, t2 = false;\n\
                 try { new o.m(); } catch (e) { t1 = e instanceof TypeError; }\n\
                 try { new (() => {})(); } catch (e) { t2 = e instanceof TypeError; }\n\
                 console.log(t1, t2);"
            ),
            vec![b(true), b(true)]
        );
    }

    #[test]
    fn function_own_key_order_is_length_name() {
        // Spec + engines: CreateBuiltinFunction / OrdinaryFunctionCreate
        // install `length` before `name` (test262 Function/property-order).
        assert_eq!(
            logged(
                "console.log(Object.getOwnPropertyNames(Function).join(','),\n\
                 Object.getOwnPropertyNames(function f(x) {}).join(','),\n\
                 Object.getOwnPropertyNames(isNaN).join(','));"
            ),
            vec![
                s("length,name,prototype"),
                s("length,name,prototype"),
                s("length,name"),
            ]
        );
        // %ThrowTypeError% via the unmapped-arguments callee accessor.
        assert_eq!(
            logged(
                "var tte = Object.getOwnPropertyDescriptor(function () {\n\
                 'use strict';\n\
                 return arguments;\n\
                 }(), 'callee').get;\n\
                 var names = Object.getOwnPropertyNames(tte);\n\
                 console.log(names.join(','), names.indexOf('name') === names.indexOf('length') + 1);"
            ),
            vec![s("length,name"), b(true)]
        );
    }

    #[test]
    fn for_head_lexical_tdz_scoping() {
        // ForIn/OfHeadEvaluation: the iterated expression sees the
        // ForDeclaration's bound names in TDZ.
        assert_eq!(
            logged(
                "var t1 = false, t2 = false, t3 = false;\n\
                 try { (function () { let x = 1; for (let x of [x]) {} })(); }\n\
                 catch (e) { t1 = e instanceof ReferenceError; }\n\
                 try { (function () { let y = 1; for (const y of [y]) {} })(); }\n\
                 catch (e) { t2 = e instanceof ReferenceError; }\n\
                 try { (function () { let k = 'a'; for (let k in { a: k }) {} })(); }\n\
                 catch (e) { t3 = e instanceof ReferenceError; }\n\
                 console.log(t1, t2, t3);"
            ),
            vec![b(true), b(true), b(true)]
        );
        // The head scope closes over closures created during the head
        // expression; per-iteration bindings are fresh and visible to the
        // declaration's own defaults and the body.
        assert_eq!(
            logged(
                "let x = 'outside';\n\
                 var probeBefore = function () { return x; };\n\
                 var probeExpr, probeDecl, probeBody;\n\
                 for (\n\
                   let [x, _ = probeDecl = function () { return x; }]\n\
                   of\n\
                   (probeExpr = function () { typeof x; }, [['inside']])\n\
                 )\n\
                   probeBody = function () { return x; };\n\
                 var t = false;\n\
                 try { probeExpr(); } catch (e) { t = e instanceof ReferenceError; }\n\
                 console.log(probeBefore(), t, probeDecl(), probeBody());"
            ),
            vec![s("outside"), b(true), s("inside"), s("inside")]
        );
    }

    #[test]
    fn object_statics_s1b() {
        assert_eq!(
            logged(
                "var log = [];\n\
                 var src = { a: 1, get b() { log.push('g'); return 2; } };\n\
                 var t = Object.assign({ a: 0 }, src, null, undefined, { c: 3 });\n\
                 console.log(t.a, t.b, t.c, log.join(','), Object.assign(t) === t);"
            ),
            vec![num("1"), num("2"), num("3"), s("g"), b(true)]
        );
        assert_eq!(
            logged(
                "var o = { b: 1, 0: 'z', a: 2 };\n\
                 console.log(Object.values(o).join(','), Object.entries(o)[0].join(':'),\n\
                 Object.entries(o).length, Object.hasOwn(o, 'a'), Object.hasOwn(o, 'q'));"
            ),
            vec![s("z,1,2"), s("0:z"), num("3"), b(true), b(false)]
        );
        assert_eq!(
            logged(
                "var o = Object.fromEntries([['a', 1], ['b', 2], ['a', 3]]);\n\
                 console.log(o.a, o.b, Object.keys(o).join(','));"
            ),
            vec![num("3"), num("2"), s("a,b")]
        );
        assert_eq!(
            logged(
                "var o = Object.create(null, { x: { value: 1, enumerable: true } });\n\
                 var d = Object.getOwnPropertyDescriptors({ a: 1 });\n\
                 console.log(o.x, Object.getPrototypeOf(o), d.a.value, d.a.writable);"
            ),
            vec![num("1"), ProjectedValue::Null, num("1"), b(true)]
        );
        assert_eq!(
            logged(
                "var o = Object.defineProperties({}, { x: { value: 7 }, y: { value: 8, enumerable: true } });\n\
                 console.log(o.x, o.y, Object.keys(o).join(','));"
            ),
            vec![num("7"), num("8"), s("y")]
        );
        // freeze/seal/integrity incl. arrays.
        assert_eq!(
            logged(
                "var o = Object.freeze({ a: 1 }); o.a = 2; o.b = 3;\n\
                 var a = Object.seal([1, 2]); a[0] = 9; a.length = 2;\n\
                 var t = false; try { a.push(3); } catch (e) { t = e instanceof TypeError; }\n\
                 console.log(o.a, o.b, Object.isFrozen(o), Object.isSealed(o), a[0], t,\n\
                 Object.isFrozen(1), Object.isSealed('x'), Object.isFrozen([]));"
            ),
            vec![
                num("1"),
                ProjectedValue::Undefined,
                b(true),
                b(true),
                num("9"),
                b(true),
                b(true),
                b(true),
                b(false),
            ]
        );
        // setPrototypeOf + cycle rejection.
        assert_eq!(
            logged(
                "var p = { greet: function () { return 'hi'; } }; var o = {};\n\
                 Object.setPrototypeOf(o, p);\n\
                 var t = false; try { Object.setPrototypeOf(p, o); } catch (e) { t = e instanceof TypeError; }\n\
                 console.log(o.greet(), t, Object.setPrototypeOf(5, null));"
            ),
            vec![s("hi"), b(true), num("5")]
        );
    }

    #[test]
    fn array_methods_s1b() {
        assert_eq!(
            logged(
                "var a = [1, 2, 3, 4];\n\
                 console.log(a.at(-1), a.includes(2), a.includes(5), [NaN].includes(NaN),\n\
                 a.lastIndexOf(3), a.every(function (x) { return x > 0; }),\n\
                 a.some(function (x) { return x > 3; }),\n\
                 a.filter(function (x) { return x % 2 === 0; }).join(','),\n\
                 a.find(function (x) { return x > 2; }), a.findIndex(function (x) { return x > 2; }),\n\
                 a.findLast(function (x) { return x < 4; }), a.findLastIndex(function (x) { return x < 4; }));"
            ),
            vec![
                num("4"),
                b(true),
                b(false),
                b(true),
                num("2"),
                b(true),
                b(true),
                s("2,4"),
                num("3"),
                num("2"),
                num("3"),
                num("2"),
            ]
        );
        assert_eq!(
            logged(
                "console.log([1, [2, [3, [4]]]].flat().length, [1, [2, [3, [4]]]].flat(Infinity).join(','),\n\
                 [1, 2].flatMap(function (x) { return [x, x * 2]; }).join(','),\n\
                 [1, 2, 3].reduce(function (a, b) { return a + b; }),\n\
                 [1, 2, 3].reduce(function (a, b) { return a + b; }, 10),\n\
                 [1, 2, 3].reduceRight(function (a, b) { return a - b; }));"
            ),
            vec![num("3"), s("1,2,3,4"), s("1,2,2,4"), num("6"), num("16"), num("0")]
        );
        assert_eq!(
            logged(
                "var a = [1, 2, 3]; a.reverse();\n\
                 var f = [0, 0, 0, 0]; f.fill(7, 1, 3);\n\
                 var c = [1, 2, 3, 4, 5]; c.copyWithin(0, 3);\n\
                 console.log(a.join(','), f.join(','), c.join(','), [1, 2, 3].shift(),\n\
                 [1, 2].unshift(0), [3, 1, 2].sort().join(','), [10, 9, 1].sort().join(','));"
            ),
            vec![
                s("3,2,1"),
                s("0,7,7,0"),
                s("4,5,3,4,5"),
                num("1"),
                num("3"),
                s("1,2,3"),
                s("1,10,9"),
            ]
        );
        assert_eq!(
            logged(
                "console.log([3, 1, 2].sort(function (a, b) { return a - b; }).join(','),\n\
                 [3, 1, 2].sort(function (a, b) { return b - a; }).join(','),\n\
                 [1, 2, 3, 4].toReversed().join(','), [3, 1, 2].toSorted().join(','),\n\
                 [1, 2, 3].with(1, 9).join(','), [1, 2, 3, 4].toSpliced(1, 2, 'x').join(','));"
            ),
            vec![s("1,2,3"), s("3,2,1"), s("4,3,2,1"), s("1,2,3"), s("1,9,3"), s("1,x,4")]
        );
        // splice with species-free result; holes preserved semantics.
        assert_eq!(
            logged(
                "var a = [1, 2, 3, 4, 5]; var r = a.splice(1, 2, 'a');\n\
                 console.log(a.join(','), r.join(','), a.length,\n\
                 [, 1].sort().length, [, 1].sort().hasOwnProperty('1'));"
            ),
            vec![s("1,a,4,5"), s("2,3"), num("4"), num("2"), b(false)]
        );
        // Array.from / Array.of.
        assert_eq!(
            logged(
                "console.log(Array.from([1, 2]).join(','), Array.from('ab').join(','),\n\
                 Array.from({ length: 2, 0: 'x', 1: 'y' }).join(','),\n\
                 Array.from([1, 2], function (x, i) { return x * 10 + i; }).join(','),\n\
                 Array.of(7, 'a').join(','), Array.of().length,\n\
                 Array.from((function () { return arguments; })(5, 6)).join(','));"
            ),
            vec![s("1,2"), s("a,b"), s("x,y"), s("10,21"), s("7,a"), num("0"), s("5,6")]
        );
        // Exact @@species via subclassing.
        assert_eq!(
            logged(
                "class MyArr extends Array {}\n\
                 var m = MyArr.from([1, 2, 3]);\n\
                 var sliced = m.slice(1);\n\
                 console.log(m instanceof MyArr, sliced instanceof MyArr, sliced.join(','),\n\
                 m.filter(function (x) { return x > 1; }) instanceof MyArr);"
            ),
            vec![b(true), b(true), s("2,3"), b(true)]
        );
    }

    #[test]
    fn symbol_s1b() {
        assert_eq!(
            logged(
                "var s1 = Symbol('one'); var s2 = Symbol('one'); var t = Symbol();\n\
                 console.log(typeof s1, s1 === s2, s1.description, t.description,\n\
                 s1.toString(), String(s1), Symbol.iterator.description,\n\
                 Symbol.for('k') === Symbol.for('k'), Symbol.keyFor(Symbol.for('k')),\n\
                 Symbol.keyFor(s1));"
            ),
            vec![
                s("symbol"),
                b(false),
                s("one"),
                ProjectedValue::Undefined,
                s("Symbol(one)"),
                s("Symbol(one)"),
                s("Symbol.iterator"),
                b(true),
                s("k"),
                ProjectedValue::Undefined,
            ]
        );
        // Symbol-keyed properties end-to-end + reflection.
        assert_eq!(
            logged(
                "var k = Symbol('key'); var o = {};\n\
                 o[k] = 42;\n\
                 console.log(o[k], Object.getOwnPropertySymbols(o).length,\n\
                 Object.getOwnPropertySymbols(o)[0] === k, Object.keys(o).length, k in o);"
            ),
            vec![num("42"), num("1"), b(true), num("0"), b(true)]
        );
        // new Symbol() throws; implicit string coercion throws.
        assert_eq!(
            logged(
                "var t1 = false, t2 = false;\n\
                 try { new Symbol(); } catch (e) { t1 = e instanceof TypeError; }\n\
                 try { '' + Symbol(); } catch (e) { t2 = e instanceof TypeError; }\n\
                 console.log(t1, t2);"
            ),
            vec![b(true), b(true)]
        );
        // @@toPrimitive / @@toStringTag / @@hasInstance user handlers.
        assert_eq!(
            logged(
                "var o = {}; o[Symbol.toPrimitive] = function (hint) { return hint === 'number' ? 42 : 'str'; };\n\
                 var tagged = {}; tagged[Symbol.toStringTag] = 'Custom';\n\
                 function C() {} Object.defineProperty(C, Symbol.hasInstance, { value: function (v) { return v === 1; } });\n\
                 console.log(+o, `${o}`, Object.prototype.toString.call(tagged), 1 instanceof C, 2 instanceof C);"
            ),
            vec![num("42"), s("str"), s("[object Custom]"), b(true), b(false)]
        );
    }

    #[test]
    fn error_family_s1b() {
        assert_eq!(
            logged(
                "var e = new AggregateError([new Error('a'), 1], 'msg');\n\
                 console.log(e instanceof AggregateError, e instanceof Error, e.errors.length,\n\
                 e.errors[1], e.name, Object.getPrototypeOf(TypeError) === Error,\n\
                 e.toString());"
            ),
            vec![
                b(true),
                b(true),
                num("2"),
                num("1"),
                s("AggregateError"),
                b(true),
                s("AggregateError: msg"),
            ]
        );
        assert_eq!(
            logged(
                "var e = new Error('m', { cause: 42 });\n\
                 var d = Object.getOwnPropertyDescriptor(e, 'cause');\n\
                 console.log(e.cause, d.enumerable, d.writable, 'cause' in new Error('x'));"
            ),
            vec![num("42"), b(false), b(true), b(false)]
        );
    }

    #[test]
    fn string_methods_s1b() {
        assert_eq!(
            logged(
                "var s = 'hello world';\n\
                 console.log(s.at(-1), s.codePointAt(0), '\\u{1F600}'.codePointAt(0),\n\
                 s.lastIndexOf('o'), s.includes('world'), s.startsWith('hello'),\n\
                 s.endsWith('world'), s.slice(-5), s.substring(4, 1), s.split(' ').join('|'),\n\
                 'a,b,,c'.split(',').length, 'abc'.split('').join('-'), ''.split(',').length);"
            ),
            vec![
                s("d"),
                num("104"),
                num("128512"),
                num("7"),
                b(true),
                b(true),
                b(true),
                s("world"),
                s("ell"),
                s("hello|world"),
                num("4"),
                s("a-b-c"),
                num("1"),
            ]
        );
        assert_eq!(
            logged(
                "console.log('AbC'.toLowerCase(), 'aBc'.toUpperCase(), '  x  '.trim(),\n\
                 ' x '.trimStart(), ' x '.trimEnd(), 'ab'.repeat(3), '5'.padStart(3, '0'),\n\
                 'ab'.padEnd(5, 'cd'), 'a'.concat('b', 1), 'aXbXc'.replace('X', '-'),\n\
                 'aXbXc'.replaceAll('X', '-'), 'abc'.replace('b', '[$&]'),\n\
                 String.fromCharCode(104, 105), String.fromCodePoint(128512).length,\n\
                 'ab'.isWellFormed(), String.raw`a\\n${1}b`);"
            ),
            vec![
                s("abc"),
                s("ABC"),
                s("x"),
                s("x "),
                s(" x"),
                s("ababab"),
                s("005"),
                s("abcdc"),
                s("ab1"),
                s("a-bXc"),
                s("a-b-c"),
                s("a[b]c"),
                s("hi"),
                num("2"),
                b(true),
                s("a\\\\n1b"),
            ]
        );
        // Non-ASCII case conversion refuses (exactness bar).
        assert!(matches!(run("'É'.toLowerCase();"), InterpOutcome::NoCoverage { .. }));
        assert!(matches!(run("'straße'.toUpperCase();"), InterpOutcome::NoCoverage { .. }));
    }

    #[test]
    fn number_math_s1b() {
        assert_eq!(
            logged(
                "console.log(Number.isInteger(5), Number.isInteger(5.5), Number.isNaN(NaN),\n\
                 Number.isNaN('NaN'), Number.isFinite('5'), Number.isSafeInteger(2 ** 53),\n\
                 Number.MAX_SAFE_INTEGER, Number.EPSILON > 0, Number.parseInt === parseInt,\n\
                 parseInt('  42px'), parseInt('ff', 16), parseInt('0x1F'), parseFloat('3.5e1x'),\n\
                 parseFloat('.5'), parseInt('z', 36));"
            ),
            vec![
                b(true),
                b(false),
                b(true),
                b(false),
                b(false),
                b(false),
                num("9007199254740991"),
                b(true),
                b(true),
                num("42"),
                num("255"),
                num("31"),
                num("35"),
                num("0.5"),
                num("35"),
            ]
        );
        assert_eq!(
            logged(
                "console.log(Math.round(2.5), Math.round(-2.5), Math.round(0.49999999999999994),\n\
                 Math.sign(-3), Math.sign(0), Math.sqrt(9), Math.imul(3, 4),\n\
                 Math.imul(0xffffffff, 5), Math.clz32(1), Math.clz32(0), Math.fround(5.5),\n\
                 (255).toString(16), (8).toString(2), (-255).toString(16));"
            ),
            vec![
                num("3"),
                num("-2"),
                num("0"),
                num("-1"),
                num("0"),
                num("3"),
                num("12"),
                num("-5"),
                num("31"),
                num("32"),
                num("5.5"),
                s("ff"),
                s("1000"),
                s("-ff"),
            ]
        );
    }

    #[test]
    fn classes_s1b() {
        // Base class: ctor, methods, accessors, statics, fields.
        assert_eq!(
            logged(
                "class Point {\n\
                   static origin = 'O';\n\
                   count = 0;\n\
                   constructor(x, y) { this.x = x; this.y = y; }\n\
                   get sum() { return this.x + this.y; }\n\
                   set sum(v) { this.x = v; }\n\
                   dist() { return Math.abs(this.x - this.y); }\n\
                   static make() { return new Point(1, 2); }\n\
                 }\n\
                 var p = new Point(3, 7);\n\
                 console.log(p.x, p.sum, p.dist(), Point.make().sum, Point.origin, p.count,\n\
                 typeof Point, Point.name, Point.length, p instanceof Point,\n\
                 Object.keys(p).join(','), Point.prototype.constructor === Point);"
            ),
            vec![
                num("3"),
                num("10"),
                num("4"),
                num("3"),
                s("O"),
                num("0"),
                s("function"),
                s("Point"),
                num("2"),
                b(true),
                s("count,x,y"),
                b(true),
            ]
        );
        // Derived classes: super(), super.m(), field order, method override.
        assert_eq!(
            logged(
                "class A {\n\
                   constructor(v) { this.v = v; }\n\
                   who() { return 'A' + this.v; }\n\
                 }\n\
                 class B extends A {\n\
                   tag = 'b';\n\
                   constructor() { super(7); }\n\
                   who() { return 'B/' + super.who() + '/' + this.tag; }\n\
                 }\n\
                 var b2 = new B();\n\
                 console.log(b2.who(), b2 instanceof A, b2 instanceof B,\n\
                 Object.getPrototypeOf(B) === A, Object.getPrototypeOf(B.prototype) === A.prototype);"
            ),
            vec![s("B/A7/b"), b(true), b(true), b(true), b(true)]
        );
        // Default derived ctor forwards args; class expressions; TDZ.
        assert_eq!(
            logged(
                "class A { constructor(a, b) { this.s = a + b; } }\n\
                 class B extends A {}\n\
                 var C = class Named {};\n\
                 var t1 = false;\n\
                 try { D; } catch (e) { t1 = e instanceof ReferenceError; }\n\
                 class D {}\n\
                 var E = class {};\n\
                 console.log(new B(1, 2).s, C.name, t1, E.name);"
            ),
            vec![num("3"), s("Named"), b(true), s("E")]
        );
        // Class ctor without new; this-TDZ; super twice.
        assert_eq!(
            logged(
                "class A {}\n\
                 class B extends A { constructor() { super(); } }\n\
                 class C extends A { constructor() { this.x = 1; super(); } }\n\
                 class E extends A { constructor() { super(); super(); } }\n\
                 var t1 = false, t2 = false, t3 = false;\n\
                 try { A(); } catch (e) { t1 = e instanceof TypeError; }\n\
                 try { new C(); } catch (e) { t2 = e instanceof ReferenceError; }\n\
                 try { new E(); } catch (e) { t3 = e instanceof ReferenceError; }\n\
                 console.log(t1, t2, t3, new B() instanceof A);"
            ),
            vec![b(true), b(true), b(true), b(true)]
        );
        // extends Error/Array natives; computed + symbol method keys.
        assert_eq!(
            logged(
                "class MyErr extends Error { constructor(m) { super(m); this.tagged = true; } }\n\
                 var e = new MyErr('x');\n\
                 var key = Symbol('m');\n\
                 class K { [key]() { return 5; } ['computed']() { return 6; } }\n\
                 console.log(e instanceof MyErr, e instanceof Error, e.tagged,\n\
                 new K()[key](), new K().computed(), e.message);"
            ),
            vec![b(true), b(true), b(true), num("5"), num("6"), s("x")]
        );
        // Methods are non-enumerable; prototype non-writable; extends null.
        assert_eq!(
            logged(
                "class C { m() {} static s() {} }\n\
                 var t = false;\n\
                 try { 'use strict'; C.prototype = 5; } catch (e) { t = e instanceof TypeError; }\n\
                 class N extends null { constructor() { return Object.create(N.prototype); } }\n\
                 console.log(Object.keys(C.prototype).length, t,\n\
                 Object.getOwnPropertyDescriptor(C.prototype, 'm').enumerable,\n\
                 Object.getPrototypeOf(N.prototype), new N() instanceof N);"
            ),
            vec![
                num("0"),
                b(false),
                b(false),
                ProjectedValue::Null,
                b(true),
            ]
        );
    }

    #[test]
    fn reflect_s1b() {
        assert_eq!(
            logged(
                "var o = { x: 1 };\n\
                 console.log(Reflect.get(o, 'x'), Reflect.has(o, 'x'), Reflect.set(o, 'y', 2), o.y,\n\
                 Reflect.deleteProperty(o, 'x'), 'x' in o,\n\
                 Reflect.defineProperty(o, 'z', { value: 3 }), o.z,\n\
                 Reflect.ownKeys({ b: 1, 0: 2, a: 3 }).join(','),\n\
                 Reflect.getPrototypeOf([]) === Array.prototype,\n\
                 Reflect.apply(function (a) { return this.base + a; }, { base: 10 }, [5]),\n\
                 Reflect.construct(function C(v) { this.v = v; }, [9]).v,\n\
                 Reflect.isExtensible({}), Object.prototype.toString.call(Reflect));"
            ),
            vec![
                num("1"),
                b(true),
                b(true),
                num("2"),
                b(true),
                b(false),
                b(true),
                num("3"),
                s("0,b,a"),
                b(true),
                num("15"),
                num("9"),
                b(true),
                s("[object Reflect]"),
            ]
        );
        // Reflect.get with receiver drives getters; Reflect.construct with
        // an explicit newTarget re-targets the prototype.
        assert_eq!(
            logged(
                "var src = { get p() { return this.tag; } };\n\
                 function A() {} function B() {}\n\
                 B.prototype.kind = 'B';\n\
                 var inst = Reflect.construct(A, [], B);\n\
                 console.log(Reflect.get(src, 'p', { tag: 't' }), inst.kind,\n\
                 Object.getPrototypeOf(inst) === B.prototype);"
            ),
            vec![s("t"), s("B"), b(true)]
        );
    }

    #[test]
    fn super_this_tdz_order_discipline() {
        // GetValue context: this-TDZ check precedes key evaluation (engine
        // consensus) — the base constructor must NOT run.
        assert_eq!(
            logged(
                "class Base { constructor() { throw new Error('base ran'); } }\n\
                 class D extends Base { constructor() { return super[super()]; } }\n\
                 var t = false;\n\
                 try { new D(); } catch (e) { t = e instanceof ReferenceError; }\n\
                 console.log(t);"
            ),
            vec![b(true)]
        );
        // Assignment-flavored contexts with a computed key under this-TDZ:
        // Node and Bun diverge — refuse.
        assert!(matches!(
            run("class Base { constructor() {} }\n\
                 class D extends Base { constructor() { super[super()] = 1; } }\n\
                 new D();"),
            InterpOutcome::NoCoverage { .. }
        ));
        // Non-computed keys under this-TDZ stay exact (consensus
        // ReferenceError).
        assert_eq!(
            logged(
                "class Base { constructor() {} }\n\
                 class D extends Base { constructor() { super.x = 1; } }\n\
                 var t = false;\n\
                 try { new D(); } catch (e) { t = e instanceof ReferenceError; }\n\
                 console.log(t);"
            ),
            vec![b(true)]
        );
    }

    #[test]
    fn super_in_object_literals() {
        assert_eq!(
            logged(
                "var proto = { greet() { return 'p'; } };\n\
                 var o = { __proto__: proto, greet() { return 'o+' + super.greet(); } };\n\
                 console.log(o.greet());"
            ),
            vec![s("o+p")]
        );
    }

    #[test]
    fn promise_microtask_ordering() {
        // Microtasks drain AFTER the synchronous body: b before a.
        assert_eq!(
            logged("Promise.resolve().then(() => console.log('a')); console.log('b');"),
            vec![s("b"), s("a")]
        );
        // A then-chain resolves one tick at a time, but drains to quiescence.
        assert_eq!(
            logged(
                "Promise.resolve(1).then(v => { console.log(v); return v + 1; })\n\
                 .then(v => console.log(v)); console.log('sync');"
            ),
            vec![s("sync"), num("1"), num("2")]
        );
    }

    #[test]
    fn promise_then_catch_values() {
        assert_eq!(
            logged(
                "Promise.reject('e').catch(x => { console.log('caught', x); return 'ok'; })\n\
                 .then(v => console.log('then', v));"
            ),
            vec![s("caught"), s("e"), s("then"), s("ok")]
        );
        // Promise.all preserves element order regardless of settle order.
        assert_eq!(
            logged(
                "Promise.all([Promise.resolve(1), 2, Promise.resolve(3)])\n\
                 .then(a => console.log(a[0], a[1], a[2], a.length));"
            ),
            vec![num("1"), num("2"), num("3"), num("3")]
        );
    }

    #[test]
    fn settimeout_after_microtasks() {
        // setTimeout(0) is a macrotask: it runs AFTER all microtasks.
        assert_eq!(
            logged(
                "setTimeout(() => console.log('timer'), 0);\n\
                 Promise.resolve().then(() => console.log('micro'));\n\
                 console.log('sync');"
            ),
            vec![s("sync"), s("micro"), s("timer")]
        );
        // Earliest-deadline ordering across timers.
        assert_eq!(
            logged(
                "setTimeout(() => console.log('b'), 10);\n\
                 setTimeout(() => console.log('a'), 5);"
            ),
            vec![s("a"), s("b")]
        );
    }

    #[test]
    fn async_await_basics() {
        // An async function returns a promise; awaits resume on microtasks.
        assert_eq!(
            logged(
                "async function f() { console.log('1'); await null; console.log('2'); return 3; }\n\
                 f().then(v => console.log('done', v)); console.log('sync');"
            ),
            vec![s("1"), s("sync"), s("2"), s("done"), num("3")]
        );
        // try/catch across await catches a rejected awaited promise.
        assert_eq!(
            logged(
                "async function g() {\n\
                   try { await Promise.reject('boom'); } catch (e) { console.log('caught', e); }\n\
                 }\n\
                 g();"
            ),
            vec![s("caught"), s("boom")]
        );
    }

    #[test]
    fn async_fn_abrupt_param_binding_rejects_not_throws() {
        // EvaluateAsyncFunctionBody: a THROW during parameter binding rejects
        // the result promise — the async function call does NOT throw
        // synchronously, and the body never runs.
        // (a) a default-initializer that throws.
        assert_eq!(
            logged(
                "var ran = 0;\n\
                 async function f(_ = (function () { throw new TypeError('boom'); })()) { ran = 1; }\n\
                 f().then(() => console.log('resolved'),\n\
                          (e) => console.log('rejected', e instanceof TypeError, ran));"
            ),
            vec![s("rejected"), b(true), num("0")]
        );
        // (b) a self-reference in the initializer → TDZ ReferenceError.
        assert_eq!(
            logged(
                "async function g(x = x) {}\n\
                 g().then(() => console.log('resolved'),\n\
                          (e) => console.log('rejected', e instanceof ReferenceError));"
            ),
            vec![s("rejected"), b(true)]
        );
        // (c) the call site sees a normal promise value, never a synchronous
        // throw: `f()` returns without escaping, so surrounding sync code runs.
        assert_eq!(
            logged(
                "var y = null;\n\
                 async function h(x = y()) {}\n\
                 h().then(() => console.log('resolved'), () => console.log('rejected'));\n\
                 console.log('after-call');"
            ),
            vec![s("after-call"), s("rejected")]
        );
        // (d) an async arrow with a throwing default binds the same way.
        assert_eq!(
            logged(
                "var k = (async (_ = (() => { throw new RangeError('x'); })()) => {});\n\
                 k().then(() => console.log('resolved'),\n\
                          (e) => console.log('rejected', e instanceof RangeError));"
            ),
            vec![s("rejected"), b(true)]
        );
    }

    #[test]
    fn queue_microtask_and_finally() {
        assert_eq!(
            logged(
                "queueMicrotask(() => console.log('mt'));\n\
                 Promise.resolve('v').finally(() => console.log('fin')).then(v => console.log(v));\n\
                 console.log('sync');"
            ),
            vec![s("sync"), s("mt"), s("fin"), s("v")]
        );
    }

    #[test]
    fn finally_does_not_swallow_out_of_slice_refusal() {
        // A refusal (out-of-slice access) inside `try` must NOT be overridden by
        // an abrupt `finally`: the finally's behavior depends on the unmodeled
        // effect we refused, so overriding would fabricate a trace.
        // Sync path, abrupt (throwing) finally:
        assert!(matches!(
            run("try { Array.fromAsync([1]); } finally { throw new Error('x'); }"),
            InterpOutcome::NoCoverage { .. }
        ));
        // Sync path, clean finally: still refuses.
        assert!(matches!(
            run("try { Array.fromAsync([1]); } finally { var z = 1; }"),
            InterpOutcome::NoCoverage { .. }
        ));
        // Async/generator resumption machine, abrupt finally:
        assert!(matches!(
            run("async function m(){ try { await Array.fromAsync([1]); } finally { throw 0; } } m();"),
            InterpOutcome::NoCoverage { .. }
        ));
        // A GENUINE throw in `try` is still overridden by an abrupt finally
        // (spec TryStatement completion semantics are unchanged).
        assert_eq!(
            completion_of(run(
                "try { throw new TypeError('a'); } finally { throw new RangeError('b'); }"
            )),
            Completion::Throw {
                v: ThrownProjection::Error {
                    ctor: Some("Error:RangeError".into()),
                    name: Some("RangeError".into()),
                    ctor_name: Some("RangeError".into()),
                },
                phase: None,
            }
        );
    }

    #[test]
    fn await_using_for_head_refuses_not_syntax_error() {
        // `await using` in a C-style for-head is valid syntax the parser rejects
        // as an early error; refuse (out of slice) rather than fabricate a
        // SyntaxError trace the engines never produce.
        assert!(matches!(
            run("async function f(){ for (await using x = obj; i < 1; i++) {} } f();"),
            InterpOutcome::NoCoverage { .. }
        ));
        // `await using` as a statement already parses and refuses downstream.
        assert!(matches!(
            run("async function f(){ await using x = obj; } f();"),
            InterpOutcome::NoCoverage { .. }
        ));
    }

    // -- explicit resource management (sync half) --------------------------

    #[test]
    fn using_disposes_at_block_end_reverse_order() {
        // Disposal runs at end of block, in reverse registration order.
        assert_eq!(
            logged(
                "{ using a = { [Symbol.dispose]() { console.log('a'); } },\n\
                       b = { [Symbol.dispose]() { console.log('b'); } };\n\
                   using c = { [Symbol.dispose]() { console.log('c'); } };\n\
                   console.log('body'); }"
            ),
            vec![s("body"), s("c"), s("b"), s("a")]
        );
    }

    #[test]
    fn using_disposes_on_abrupt_throw() {
        // Disposal runs even when the block throws; the original throw survives.
        assert!(matches!(
            completion_of(run(
                "try { using x = { [Symbol.dispose]() { console.log('disposed'); } };\n\
                       throw new RangeError('boom'); } catch (e) {\n\
                   console.log(e instanceof RangeError); }"
            )),
            Completion::Normal { .. }
        ));
        assert_eq!(
            logged(
                "try { using x = { [Symbol.dispose]() { console.log('disposed'); } };\n\
                     throw new RangeError('boom'); } catch (e) { console.log('caught'); }"
            ),
            vec![s("disposed"), s("caught")]
        );
    }

    #[test]
    fn using_disposes_in_function_body() {
        assert_eq!(
            logged(
                "function f() { using x = { [Symbol.dispose]() { console.log('d'); } };\n\
                   console.log('body'); return 1; }\n\
                 console.log(f());"
            ),
            vec![s("body"), s("d"), num("1")]
        );
    }

    #[test]
    fn using_null_and_undefined_initializer_allowed() {
        // null/undefined register no resource and never throw.
        assert!(matches!(
            completion_of(run("{ using x = null; using y = undefined; }")),
            Completion::Normal { .. }
        ));
    }

    #[test]
    fn using_non_object_initializer_type_errors() {
        for init in ["true", "1", "'str'", "Symbol()"] {
            assert_eq!(
                completion_of(run(&format!(
                    "var t = false; try {{ {{ using x = {init}; }} }} \
                     catch (e) {{ t = e instanceof TypeError; }} t;"
                ))),
                Completion::Normal { v: Some(b(true)) },
                "expected TypeError for using x = {init}"
            );
        }
    }

    #[test]
    fn using_missing_or_uncallable_dispose_type_errors() {
        // Missing @@dispose, and a present-but-not-callable @@dispose, both throw.
        for init in ["{}", "{ [Symbol.dispose]: 5 }"] {
            assert_eq!(
                completion_of(run(&format!(
                    "var t = false; try {{ {{ using x = {init}; }} }} \
                     catch (e) {{ t = e instanceof TypeError; }} t;"
                ))),
                Completion::Normal { v: Some(b(true)) },
                "expected TypeError for using x = {init}"
            );
        }
    }

    #[test]
    fn using_dispose_this_is_the_resource() {
        // The dispose method runs with `this` = the resource.
        assert_eq!(
            logged(
                "var r = { id: 7, [Symbol.dispose]() { console.log(this.id); } };\n\
                 { using x = r; }"
            ),
            vec![num("7")]
        );
    }

    #[test]
    fn using_suppressed_error_nesting() {
        // Body throw + two dispose throws → nested SuppressedError chain.
        assert_eq!(
            logged(
                "class MyError extends Error {}\n\
                 const e1 = new MyError(), e2 = new MyError(), e3 = new MyError();\n\
                 try {\n\
                   using _1 = { [Symbol.dispose]() { throw e1; } };\n\
                   using _2 = { [Symbol.dispose]() { throw e2; } };\n\
                   throw e3;\n\
                 } catch (e) {\n\
                   console.log(e instanceof SuppressedError, e.error === e1,\n\
                     e.suppressed instanceof SuppressedError,\n\
                     e.suppressed.error === e2, e.suppressed.suppressed === e3);\n\
                 }"
            ),
            vec![b(true), b(true), b(true), b(true), b(true)]
        );
    }

    #[test]
    fn using_dispose_throw_becomes_completion() {
        // A dispose throw with a normal body completion propagates the throw.
        assert_eq!(
            completion_of(run(
                "var t = false; try { { using x = { [Symbol.dispose]() { throw new TypeError(); } }; } }\n\
                 catch (e) { t = e instanceof TypeError; } t;"
            )),
            Completion::Normal { v: Some(b(true)) }
        );
    }

    #[test]
    fn disposable_stack_dispose_reverse_and_idempotent() {
        assert_eq!(
            logged(
                "const s = new DisposableStack();\n\
                 s.use({ [Symbol.dispose]() { console.log('u1'); } });\n\
                 s.defer(() => console.log('d2'));\n\
                 s.adopt(42, (v) => console.log('adopt' + v));\n\
                 console.log(s.disposed);\n\
                 s.dispose();\n\
                 console.log(s.disposed);\n\
                 s.dispose();"
            ),
            vec![b(false), s("adopt42"), s("d2"), s("u1"), b(true)]
        );
    }

    #[test]
    fn disposable_stack_symbol_dispose_is_dispose() {
        assert_eq!(
            completion_of(run(
                "DisposableStack.prototype[Symbol.dispose] === DisposableStack.prototype.dispose;"
            )),
            Completion::Normal { v: Some(b(true)) }
        );
    }

    #[test]
    fn disposable_stack_use_returns_value_and_disposed_after_throws() {
        // use returns its argument; after dispose, use/adopt/defer throw ReferenceError.
        assert_eq!(
            completion_of(run(
                "const s = new DisposableStack(); const o = { [Symbol.dispose]() {} };\n\
                 s.use(o) === o;"
            )),
            Completion::Normal { v: Some(b(true)) }
        );
        // A non-disposable object (no @@dispose) passed to `use` throws TypeError.
        assert_eq!(
            completion_of(run(
                "var t = false; const s = new DisposableStack();\n\
                 try { s.use({}); } catch (e) { t = e instanceof TypeError; } t;"
            )),
            Completion::Normal { v: Some(b(true)) }
        );
        assert_eq!(
            completion_of(run(
                "var t = false; const s = new DisposableStack(); s.dispose();\n\
                 try { s.use({}); } catch (e) { t = e instanceof ReferenceError; } t;"
            )),
            Completion::Normal { v: Some(b(true)) }
        );
    }

    #[test]
    fn disposable_stack_move_transfers_and_disposes_source() {
        assert_eq!(
            logged(
                "const a = new DisposableStack();\n\
                 a.defer(() => console.log('deferred'));\n\
                 const b = a.move();\n\
                 console.log(a.disposed, b.disposed);\n\
                 a.dispose();\n\
                 console.log('before-b-dispose');\n\
                 b.dispose();"
            ),
            vec![b(true), b(false), s("before-b-dispose"), s("deferred")]
        );
    }

    #[test]
    fn disposable_stack_new_requires_new() {
        assert_eq!(
            completion_of(run(
                "var t = false; try { DisposableStack(); } catch (e) { t = e instanceof TypeError; } t;"
            )),
            Completion::Normal { v: Some(b(true)) }
        );
    }

    #[test]
    fn suppressed_error_constructor_shape() {
        assert_eq!(
            logged(
                "const e = new SuppressedError('E', 'S', 'msg');\n\
                 console.log(e instanceof SuppressedError, e instanceof Error,\n\
                   e.error, e.suppressed, e.message, e.name);"
            ),
            vec![b(true), b(true), s("E"), s("S"), s("msg"), s("SuppressedError")]
        );
    }

    #[test]
    fn thrown_suppressed_error_classifies_as_error_error() {
        // The driver's INTRINSIC_PROTOS omits SuppressedError → a thrown one
        // tags "Error:Error", name "SuppressedError", ctor_name "SuppressedError".
        assert_eq!(
            completion_of(run("throw new SuppressedError(1, 2, 'm');")),
            Completion::Throw {
                v: ThrownProjection::Error {
                    ctor: Some("Error:Error".to_string()),
                    name: Some("SuppressedError".to_string()),
                    ctor_name: Some("SuppressedError".to_string()),
                },
                phase: None
            }
        );
    }

    #[test]
    fn symbol_dispose_projects_by_description() {
        // The driver does NOT treat @@dispose as well-known: it projects by
        // description "Symbol.dispose". A User-symbol model matches exactly.
        assert_eq!(
            logged("console.log(Symbol.dispose, Symbol.asyncDispose);"),
            vec![
                ProjectedValue::Sym { wk: None, v: Some("Symbol.dispose".to_string()) },
                ProjectedValue::Sym { wk: None, v: Some("Symbol.asyncDispose".to_string()) },
            ]
        );
        // Identity is stable across accesses.
        assert_eq!(
            completion_of(run("Symbol.dispose === Symbol.dispose;")),
            Completion::Normal { v: Some(b(true)) }
        );
    }

    #[test]
    fn using_in_unhooked_scope_refuses() {
        // A top-level `using` in an ASYNC function body is a scope this
        // interpreter does not dispose (the async disposal surface is out of
        // slice) → it refuses rather than leak an undisposed resource. (A
        // `using` in a NESTED block inside an async function is disposed by the
        // block and stays covered.)
        assert!(matches!(
            run("async function f(){ using x = { [Symbol.dispose]() {} }; } f();"),
            InterpOutcome::NoCoverage { .. }
        ));
        // A `using` in a for-of head is likewise not disposed here → refuses.
        assert!(matches!(
            run("for (using x of [{ [Symbol.dispose]() {} }]) {}"),
            InterpOutcome::NoCoverage { .. }
        ));
        // AsyncDisposableStack stays unmodeled → refuses (NoCoverage).
        assert!(matches!(
            run("new AsyncDisposableStack();"),
            InterpOutcome::NoCoverage { .. }
        ));
    }

    #[test]
    fn iterator_prototype_dispose_symbols_refuse() {
        // %Iterator.prototype%[@@dispose] and %AsyncIteratorPrototype%
        // [@@asyncDispose] are engine-real but UNMODELED — reachable now that
        // Symbol.dispose/asyncDispose resolve. Accessing them must REFUSE
        // (NoCoverage), never answer `undefined` (which would make a test's own
        // `typeof === 'function'` assertion throw where the engines return).
        let proto_expr = "Object.getPrototypeOf(Object.getPrototypeOf([][Symbol.iterator]()))";
        assert!(matches!(
            run(&format!("{proto_expr}[Symbol.dispose];")),
            InterpOutcome::NoCoverage { .. }
        ));
        // Reached transitively through an iterator instance, too.
        assert!(matches!(
            run("[][Symbol.iterator]()[Symbol.dispose];"),
            InterpOutcome::NoCoverage { .. }
        ));
    }

    #[test]
    fn async_out_of_reach_refuses_not_wrong() {
        // await in a non-suspendable position (call argument) → sound refusal.
        assert!(matches!(
            run("async function f() { console.log(await 1); } f();"),
            InterpOutcome::NoCoverage { .. }
        ));
        // await in an operator operand → sound refusal.
        assert!(matches!(
            run("async function f() { return (await 1) + (await 2); } f();"),
            InterpOutcome::NoCoverage { .. }
        ));
        // Async generators are out of reach → refuse at definition.
        assert!(matches!(
            run("async function* g() {} g();"),
            InterpOutcome::NoCoverage { .. }
        ));
        // Unhandled rejection → refuse (engine-divergent observability).
        assert!(matches!(
            run("Promise.reject(1);"),
            InterpOutcome::NoCoverage { .. }
        ));
    }

    #[test]
    fn caps_and_schema_stamped() {
        let InterpOutcome::Trace(t) = run("1;") else {
            panic!("expected trace");
        };
        assert_eq!(t.schema, SCHEMA_VERSION);
        assert_eq!(t.caps, Some(projection_caps()));
        // Runaway loops refuse via the iteration cap (totality).
        assert!(matches!(run("while (true) {}"), InterpOutcome::NoCoverage { .. }));
        // Runaway recursion refuses via the call-depth cap.
        assert!(matches!(
            run("function f() { return f(); } f();"),
            InterpOutcome::NoCoverage { .. }
        ));
    }
}

#[cfg(test)]
mod module_graph_tests {
    use super::*;
    use trust_js_trace::{Completion, HostEvent, ProjectedValue, ThrownProjection};

    /// Link `main_src` (key `./main.js`) against an in-memory sibling set. The
    /// resolver keys each file by its own specifier (flat directory) so a
    /// specifier equal to `./main.js` is a self-import.
    fn graph(main_src: &str, files: &[(&str, &str)]) -> InterpOutcome {
        let files: HashMap<String, String> =
            files.iter().map(|(k, v)| ((*k).to_string(), (*v).to_string())).collect();
        let resolver: ModuleResolver = Box::new(move |_importer: &str, spec: &str| {
            files
                .get(spec)
                .map(|s| (spec.to_string(), s.clone()))
                .ok_or_else(|| format!("no such sibling `{spec}`"))
        });
        evaluate_module_graph(&[], "./main.js", main_src, resolver)
    }

    fn refusal(o: InterpOutcome) -> String {
        match o {
            InterpOutcome::NoCoverage { reason } => reason,
            InterpOutcome::Trace(t) => panic!("expected NoCoverage, got trace {t:?}"),
        }
    }

    fn completion(o: InterpOutcome) -> Completion {
        match o {
            InterpOutcome::Trace(t) => t.completion,
            InterpOutcome::NoCoverage { reason } => panic!("unexpected NoCoverage: {reason}"),
        }
    }

    fn is_syntax_error(c: &Completion) -> bool {
        matches!(
            c,
            Completion::Throw {
                v: ThrownProjection::Error { name: Some(n), .. },
                phase: None,
            } if n == "SyntaxError"
        )
    }

    #[test]
    fn named_import_const_covers() {
        // main reads a const export; a wrong value would throw.
        let o = graph(
            "import { x } from './dep.js'; if (x !== 42) throw 'wrong';",
            &[("./dep.js", "export const x = 42;")],
        );
        assert!(matches!(completion(o), Completion::Normal { .. }));
    }

    #[test]
    fn named_import_var_not_reassigned_covers() {
        // A `var` export never reassigned is captured as its stable value.
        let o = graph(
            "import { x } from './dep.js'; if (x !== 1) throw 'wrong';",
            &[("./dep.js", "export var x = 1;")],
        );
        assert!(matches!(completion(o), Completion::Normal { .. }));
    }

    #[test]
    fn import_renamed_and_function_export_covers() {
        let o = graph(
            "import { f as g } from './dep.js'; if (g() !== 7) throw 'wrong';",
            &[("./dep.js", "export function f() { return 7; }")],
        );
        assert!(matches!(completion(o), Completion::Normal { .. }));
    }

    #[test]
    fn dependency_evaluates_before_main_in_order() {
        // Side-effect import: dep logs 'a', then main logs 'b'.
        let InterpOutcome::Trace(t) = graph(
            "import './dep.js'; console.log('b');",
            &[("./dep.js", "console.log('a');")],
        ) else {
            panic!("expected trace");
        };
        let logged: Vec<String> = t
            .events
            .into_iter()
            .flat_map(|e| match e {
                HostEvent::Stdout { v } => v
                    .into_iter()
                    .map(|p| match p {
                        ProjectedValue::Str { v } => v,
                        other => format!("{other:?}"),
                    })
                    .collect::<Vec<_>>(),
                other => panic!("unexpected event {other:?}"),
            })
            .collect();
        assert_eq!(logged, vec!["a".to_string(), "b".to_string()]);
    }

    #[test]
    fn transitive_named_import_covers() {
        // main -> a -> b, a re-declares from b's export and re-exports its own.
        let o = graph(
            "import { a } from './a.js'; if (a !== 3) throw 'wrong';",
            &[
                ("./a.js", "import { b } from './b.js'; export const a = b + 1;"),
                ("./b.js", "export const b = 2;"),
            ],
        );
        assert!(matches!(completion(o), Completion::Normal { .. }));
    }

    #[test]
    fn module_env_isolation_holds() {
        // A dep's top-level `var`/`let` must NOT leak into the importer's scope.
        let o = graph(
            "import './dep.js'; var seen = false; try { leaked; } catch (e) { seen = e instanceof ReferenceError; } if (!seen) throw 'leaked';",
            &[("./dep.js", "var leaked = 1; let alsoLeaked = 2;")],
        );
        assert!(matches!(completion(o), Completion::Normal { .. }));
    }

    #[test]
    fn missing_export_is_link_syntax_error() {
        let o = graph(
            "$NEVER; import { y } from './dep.js';",
            &[("./dep.js", "export const x = 1;")],
        );
        assert!(is_syntax_error(&completion(o)), "expected SyntaxError");
    }

    #[test]
    fn dependency_parse_error_is_syntax_error() {
        // A parse error anywhere in the graph is a load-time SyntaxError; the
        // main body never evaluates (its `throw` never runs).
        let o = graph(
            "import './dep.js'; throw 'should-not-run';",
            &[("./dep.js", "let x = ;")],
        );
        assert!(is_syntax_error(&completion(o)), "expected SyntaxError");
    }

    #[test]
    fn self_import_refused() {
        // `x as y` avoids the import/declaration name collision (a real early
        // error) so the self-import guard is what actually fires.
        let r = refusal(graph(
            "import { x as y } from './main.js'; export const x = 1;",
            &[("./main.js", "export const x = 1;")],
        ));
        assert!(r.contains("self-import"), "reason: {r}");
    }

    #[test]
    fn cycle_refused() {
        let r = refusal(graph(
            "import { a } from './a.js';",
            &[
                ("./a.js", "import { b } from './b.js'; export const a = 1;"),
                ("./b.js", "import { a } from './a.js'; export const b = 2;"),
            ],
        ));
        assert!(r.contains("cycle"), "reason: {r}");
    }

    #[test]
    fn reassigned_export_is_live_binding_refused() {
        // The `test262update`-style pattern: an exported binding mutated later.
        let r = refusal(graph(
            "import { x } from './dep.js';",
            &[(
                "./dep.js",
                "export var x = 1; globalThis.bump = function () { x = 2; };",
            )],
        ));
        assert!(r.contains("live binding"), "reason: {r}");
    }

    // ---- default export / import ------------------------------------------

    #[test]
    fn default_import_of_expr_export_covers() {
        let o = graph(
            "import d from './dep.js'; if (d !== 42) throw 'wrong';",
            &[("./dep.js", "export default 42;")],
        );
        assert!(matches!(completion(o), Completion::Normal { .. }));
    }

    #[test]
    fn default_import_of_object_expr_export_covers() {
        let o = graph(
            "import d from './dep.js'; if (d.a !== 1) throw 'wrong';",
            &[("./dep.js", "export default { a: 1 };")],
        );
        assert!(matches!(completion(o), Completion::Normal { .. }));
    }

    #[test]
    fn default_import_named_function_keeps_name_and_local() {
        // The named default export keeps its own name `f`; the local `f` is in
        // scope in the exporter and callable; the importer sees `.name === 'f'`.
        let o = graph(
            "import d from './dep.js'; if (d() !== 7) throw 'call'; if (d.name !== 'f') throw 'name';",
            &[("./dep.js", "export default function f() { return 7; } if (f() !== 7) throw 'localf';")],
        );
        assert!(matches!(completion(o), Completion::Normal { .. }));
    }

    #[test]
    fn default_import_anonymous_function_name_is_default() {
        // SetFunctionName gives an anonymous default function `.name === 'default'`.
        let o = graph(
            "import d from './dep.js'; if (typeof d !== 'function') throw 't'; if (d.name !== 'default') throw d.name;",
            &[("./dep.js", "export default function () { return 5; }")],
        );
        assert!(matches!(completion(o), Completion::Normal { .. }));
    }

    #[test]
    fn default_import_named_class_covers() {
        let o = graph(
            "import D from './dep.js'; if (new D().v !== 9) throw 'inst'; if (D.name !== 'C') throw D.name;",
            &[("./dep.js", "export default class C { constructor() { this.v = 9; } }")],
        );
        assert!(matches!(completion(o), Completion::Normal { .. }));
    }

    #[test]
    fn default_import_anonymous_class_name_is_default() {
        let o = graph(
            "import D from './dep.js'; if (D.name !== 'default') throw D.name;",
            &[("./dep.js", "export default class { }")],
        );
        assert!(matches!(completion(o), Completion::Normal { .. }));
    }

    #[test]
    fn default_import_anonymous_arrow_name_is_default() {
        // `export default <arrow>` — NamedEvaluation("default") sets `.name`.
        let o = graph(
            "import d from './dep.js'; if (d() !== 3) throw 'call'; if (d.name !== 'default') throw d.name;",
            &[("./dep.js", "export default () => 3;")],
        );
        assert!(matches!(completion(o), Completion::Normal { .. }));
    }

    #[test]
    fn export_brace_as_default_import_covers() {
        // `export { x as default }` — the export side already worked; the import
        // side now resolves `default` to the local `x`.
        let o = graph(
            "import d from './dep.js'; if (d !== 5) throw 'wrong';",
            &[("./dep.js", "const x = 5; export { x as default };")],
        );
        assert!(matches!(completion(o), Completion::Normal { .. }));
    }

    #[test]
    fn default_and_named_combined_import_covers() {
        let o = graph(
            "import d, { x } from './dep.js'; if (d !== 1) throw 'd'; if (x !== 2) throw 'x';",
            &[("./dep.js", "export default 1; export const x = 2;")],
        );
        assert!(matches!(completion(o), Completion::Normal { .. }));
    }

    #[test]
    fn missing_default_export_is_link_syntax_error() {
        let o = graph(
            "import d from './dep.js';",
            &[("./dep.js", "export const x = 1;")],
        );
        assert!(is_syntax_error(&completion(o)), "expected SyntaxError");
    }

    #[test]
    fn import_free_default_export_single_module_covers() {
        // A main module with `export default` and NO import takes the import-free
        // fast path; the export is unobservable, only the local binding matters.
        assert!(matches!(
            completion(graph(
                "export default function f() { return 4; } if (f() !== 4) throw 'x'; if (f.name !== 'f') throw f.name;",
                &[],
            )),
            Completion::Normal { .. }
        ));
    }

    // ---- namespace import (Module Namespace Exotic Object) ----------------

    #[test]
    fn namespace_import_names_values_and_tag_cover() {
        let o = graph(
            "import * as ns from './dep.js'; \
             if (Object.getOwnPropertyNames(ns).join(',') !== 'a,b,default,f') throw 'order:' + Object.getOwnPropertyNames(ns).join(','); \
             if (ns.a !== 1) throw 'a'; if (ns.b !== 2) throw 'b'; if (ns.default !== 9) throw 'd'; if (ns.f() !== 7) throw 'f'; \
             if (ns[Symbol.toStringTag] !== 'Module') throw 'tag'; \
             if (Object.prototype.toString.call(ns) !== '[object Module]') throw 'toStr'; \
             if (Object.getPrototypeOf(ns) !== null) throw 'proto'; \
             if (ns.nope !== undefined) throw 'absent'; if ('nope' in ns) throw 'in'; \
             if (Object.isExtensible(ns)) throw 'ext'; if (typeof ns !== 'object') throw 'typeof';",
            &[("./dep.js", "export const b = 2; export const a = 1; export function f(){ return 7; } export default 9;")],
        );
        assert!(matches!(completion(o), Completion::Normal { .. }));
    }

    #[test]
    fn namespace_descriptor_shape_covers() {
        let o = graph(
            "import * as ns from './dep.js'; \
             var d = Object.getOwnPropertyDescriptor(ns, 'a'); \
             if (d.value !== 1) throw 'v'; if (d.writable !== true) throw 'w'; \
             if (d.enumerable !== true) throw 'e'; if (d.configurable !== false) throw 'c'; \
             var t = Object.getOwnPropertyDescriptor(ns, Symbol.toStringTag); \
             if (t.value !== 'Module') throw 'tv'; if (t.writable !== false) throw 'tw'; \
             if (t.enumerable !== false) throw 'te'; if (t.configurable !== false) throw 'tc'; \
             if (Object.getOwnPropertySymbols(ns).length !== 1) throw 'syms';",
            &[("./dep.js", "export const a = 1;")],
        );
        assert!(matches!(completion(o), Completion::Normal { .. }));
    }

    #[test]
    fn namespace_set_and_delete_fail_in_strict_module() {
        // Module code is strict: a failed [[Set]] / [[Delete]] throws TypeError,
        // and the value is unchanged.
        let o = graph(
            "import * as ns from './dep.js'; \
             var setThrew = false; try { ns.a = 5; } catch (e) { setThrew = e instanceof TypeError; } \
             if (!setThrew) throw 'set'; if (ns.a !== 1) throw 'changed'; \
             var delThrew = false; try { delete ns.a; } catch (e) { delThrew = e instanceof TypeError; } \
             if (!delThrew) throw 'del';",
            &[("./dep.js", "export const a = 1;")],
        );
        assert!(matches!(completion(o), Completion::Normal { .. }));
    }

    #[test]
    fn namespace_define_own_property_noop_only() {
        let o = graph(
            "import * as ns from './dep.js'; \
             if (Reflect.defineProperty(ns, 'a', {}) !== true) throw 'noop'; \
             if (Reflect.defineProperty(ns, 'a', {value: 1, writable: true, enumerable: true, configurable: false}) !== true) throw 'match'; \
             if (Reflect.defineProperty(ns, 'a', {value: 99}) !== false) throw 'changeVal'; \
             if (Reflect.defineProperty(ns, 'a', {configurable: true}) !== false) throw 'changeCfg'; \
             if (Reflect.defineProperty(ns, 'a', {writable: false}) !== false) throw 'changeW'; \
             if (Reflect.defineProperty(ns, 'new', {value: 1}) !== false) throw 'newKey'; \
             if (ns.a !== 1) throw 'mutated';",
            &[("./dep.js", "export const a = 1;")],
        );
        assert!(matches!(completion(o), Completion::Normal { .. }));
    }

    #[test]
    fn namespace_setprototypeof_null_ok_matches_node() {
        // Object.setPrototypeOf(ns, null) succeeds (SetImmutablePrototype, V is
        // the current null) — the spec/Node behavior (Bun throws; matching Node
        // keeps the head trace-equal to one engine).
        let o = graph(
            "import * as ns from './dep.js'; \
             if (Object.setPrototypeOf(ns, null) !== ns) throw 'null'; \
             var threw = false; try { Object.setPrototypeOf(ns, {}); } catch (e) { threw = e instanceof TypeError; } \
             if (!threw) throw 'obj';",
            &[("./dep.js", "export const a = 1;")],
        );
        assert!(matches!(completion(o), Completion::Normal { .. }));
    }

    #[test]
    fn namespace_identity_is_cached_per_module() {
        // Two `import * as` of the same module yield the SAME namespace object.
        let o = graph(
            "import * as a from './dep.js'; import * as b from './dep.js'; if (a !== b) throw 'identity';",
            &[("./dep.js", "export const x = 1;")],
        );
        assert!(matches!(completion(o), Completion::Normal { .. }));
    }

    #[test]
    fn namespace_forin_and_keys_are_sorted_exports() {
        let o = graph(
            "import * as ns from './dep.js'; \
             var ks = []; for (var k in ns) ks.push(k); \
             if (ks.join(',') !== 'a,b,c') throw 'forin:' + ks.join(','); \
             if (Object.keys(ns).join(',') !== 'a,b,c') throw 'keys';",
            &[("./dep.js", "export const c = 3; export const b = 2; export const a = 1;")],
        );
        assert!(matches!(completion(o), Completion::Normal { .. }));
    }

    // ---- re-exports (star / named / namespace) ----------------------------

    #[test]
    fn namespace_of_star_reexport_dependency_covers() {
        // `import * as ns` of a dep that `export *`s from another module: the
        // namespace exposes the re-exported name (sorted key-set exact).
        let o = graph(
            "import * as ns from './dep.js'; \
             if (Object.keys(ns).join(',') !== 'x') throw Object.keys(ns).join(','); \
             if (ns.x !== 1) throw 'x';",
            &[
                ("./dep.js", "export * from './other.js';"),
                ("./other.js", "export const x = 1;"),
            ],
        );
        assert!(matches!(completion(o), Completion::Normal { .. }));
    }

    #[test]
    fn star_reexport_named_import_covers() {
        // `import { x }` of a dep that `export *`s from another module resolves.
        let o = graph(
            "import { x } from './dep.js'; if (x !== 5) throw 'x';",
            &[
                ("./dep.js", "export * from './other.js';"),
                ("./other.js", "export const x = 5;"),
            ],
        );
        assert!(matches!(completion(o), Completion::Normal { .. }));
    }

    #[test]
    fn named_reexport_import_covers() {
        // `export { a, b as c } from` — named re-exports resolve by imported name.
        let o = graph(
            "import { a, c } from './dep.js'; if (a !== 1) throw 'a'; if (c !== 2) throw 'c';",
            &[
                ("./dep.js", "export { a, b as c } from './other.js';"),
                ("./other.js", "export const a = 1; export const b = 2;"),
            ],
        );
        assert!(matches!(completion(o), Completion::Normal { .. }));
    }

    #[test]
    fn named_reexport_missing_name_is_link_syntax_error() {
        // A named re-export of a name the source does not provide fails to link.
        let o = graph(
            "import { a } from './dep.js';",
            &[
                ("./dep.js", "export { nope as a } from './other.js';"),
                ("./other.js", "export const x = 1;"),
            ],
        );
        assert!(is_syntax_error(&completion(o)), "expected SyntaxError");
    }

    #[test]
    fn star_reexport_excludes_default() {
        // `export *` never propagates `default`: importing it fails to link.
        let o = graph(
            "import { d } from './dep.js';",
            &[
                ("./dep.js", "export * from './other.js';"),
                ("./other.js", "export default 9; export const x = 1;"),
            ],
        );
        assert!(is_syntax_error(&completion(o)), "expected SyntaxError");
        // …and `default` is absent from the star-re-exporting namespace, while
        // the non-default name is present.
        let o2 = graph(
            "import * as ns from './dep.js'; \
             if ('default' in ns) throw 'default present'; if (ns.x !== 1) throw 'x'; \
             if (Object.keys(ns).join(',') !== 'x') throw Object.keys(ns).join(',');",
            &[
                ("./dep.js", "export * from './other.js';"),
                ("./other.js", "export default 9; export const x = 1;"),
            ],
        );
        assert!(matches!(completion(o2), Completion::Normal { .. }));
    }

    #[test]
    fn star_reexport_local_wins_over_star() {
        // A locally-declared export shadows a same-named star export (no
        // ambiguity), and its own value wins.
        let o = graph(
            "import { x } from './dep.js'; if (x !== 10) throw x;",
            &[
                ("./dep.js", "export const x = 10; export * from './other.js';"),
                ("./other.js", "export const x = 99;"),
            ],
        );
        assert!(matches!(completion(o), Completion::Normal { .. }));
    }

    #[test]
    fn namespace_reexport_covers() {
        // `export * as ns from src` re-exports src's namespace object under `ns`.
        let o = graph(
            "import { inner } from './dep.js'; \
             if (inner[Symbol.toStringTag] !== 'Module') throw 'tag'; \
             if (inner.x !== 1) throw 'x'; if (inner.y !== 2) throw 'y'; \
             if (Object.keys(inner).join(',') !== 'x,y') throw Object.keys(inner).join(',');",
            &[
                ("./dep.js", "export * as inner from './other.js';"),
                ("./other.js", "export const y = 2; export const x = 1;"),
            ],
        );
        assert!(matches!(completion(o), Completion::Normal { .. }));
    }

    #[test]
    fn ambiguous_star_reexport_refused() {
        // Two `export *` sources provide the same name resolving to DIFFERENT
        // bindings: ambiguous. We refuse (never guess) — engines may disagree.
        let r = refusal(graph(
            "import * as ns from './dep.js';",
            &[
                ("./dep.js", "export * from './a.js'; export * from './b.js';"),
                ("./a.js", "export const conflict = 1;"),
                ("./b.js", "export const conflict = 2;"),
            ],
        ));
        assert!(r.contains("ambiguous"), "reason: {r}");
    }

    #[test]
    fn diamond_star_reexport_same_binding_covers() {
        // Two `export *` paths that reach the SAME underlying binding are NOT
        // ambiguous (diamond dedup): the name resolves and covers.
        let o = graph(
            "import { shared } from './dep.js'; if (shared !== 7) throw shared;",
            &[
                ("./dep.js", "export * from './a.js'; export * from './b.js';"),
                ("./a.js", "export * from './base.js';"),
                ("./b.js", "export * from './base.js';"),
                ("./base.js", "export const shared = 7;"),
            ],
        );
        assert!(matches!(completion(o), Completion::Normal { .. }));
    }

    #[test]
    fn reexport_cycle_refused() {
        // A cycle through `export *` is detected and refused (sound).
        let r = refusal(graph(
            "import * as ns from './a.js';",
            &[
                ("./a.js", "export * from './b.js'; export var fromA;"),
                ("./b.js", "export * from './a.js'; export var fromB;"),
            ],
        ));
        assert!(r.contains("cycle"), "reason: {r}");
    }

    #[test]
    fn reexport_only_main_evaluates_source_side_effects() {
        // A main module that only `export *`s (no import) still evaluates the
        // source for its side effects, then runs its own body.
        let InterpOutcome::Trace(t) = graph(
            "export * from './dep.js'; console.log('main');",
            &[("./dep.js", "console.log('dep');")],
        ) else {
            panic!("expected trace");
        };
        let logged: Vec<String> = t
            .events
            .into_iter()
            .flat_map(|e| match e {
                HostEvent::Stdout { v } => v
                    .into_iter()
                    .map(|p| match p {
                        ProjectedValue::Str { v } => v,
                        other => format!("{other:?}"),
                    })
                    .collect::<Vec<_>>(),
                other => panic!("unexpected event {other:?}"),
            })
            .collect();
        assert_eq!(logged, vec!["dep".to_string(), "main".to_string()]);
    }

    #[test]
    fn nonrelative_and_missing_refused() {
        // A bare specifier the resolver rejects (here: absent) is a refusal.
        assert!(matches!(
            graph("import { x } from './nope.js';", &[]),
            InterpOutcome::NoCoverage { .. }
        ));
    }

    #[test]
    fn dependency_throw_refused() {
        // A dependency that throws during evaluation is refused (the
        // cross-module evaluation-throw trace is not modeled).
        let r = refusal(graph(
            "import './dep.js';",
            &[("./dep.js", "throw new Error('boom');")],
        ));
        assert!(r.contains("threw during evaluation"), "reason: {r}");
    }

    #[test]
    fn module_only_construct_refused() {
        // Top-level `this` in the graph lane still refuses (module `this` is
        // undefined; the strict-script model cannot reproduce it).
        assert!(matches!(
            graph("import './dep.js'; this;", &[("./dep.js", ";")]),
            InterpOutcome::NoCoverage { .. }
        ));
    }

    #[test]
    fn import_free_module_fast_path_covers() {
        // No import: the exact single-module lowering (a normal completion).
        assert!(matches!(
            completion(graph("export const x = 1; if (x !== 1) throw 'x';", &[])),
            Completion::Normal { .. }
        ));
    }

    #[test]
    fn depth_and_count_bounds_refuse() {
        // A side-effect chain deeper than MAX_DEPTH refuses.
        let deep = graph(
            "import './m1.js';",
            &[
                ("./m1.js", "import './m2.js';"),
                ("./m2.js", "import './m3.js';"),
                ("./m3.js", "import './m4.js';"),
                ("./m4.js", ";"),
            ],
        );
        assert!(matches!(deep, InterpOutcome::NoCoverage { .. }));
    }
}
