//! Trust (D21): exercise the dispatcher with a real compiler Session, ExtCtxt
//! and Rustc server. The resolver fixture deliberately cannot resolve macros;
//! it observes the real eager-expansion walk rather than supplying its result.

#![allow(rustc::bad_opt_access)]

use std::cell::Cell;
use std::rc::Rc;
use std::sync::Arc;
use std::sync::atomic::AtomicBool;
use std::time::{Duration, Instant};

use rustc_ast::attr::data_structures::CfgEntry;
use rustc_ast::{self as ast, NodeId};
use rustc_feature::Features;
use rustc_lint_defs::RegisteredTools;
use rustc_session::config::{self, ErrorOutputType, Input, Options, TrustVerify};
use rustc_session::{CodegenBackendInit, CompilerIO, EarlyDiagCtxt, Session as CompilerSession};
use rustc_span::def_id::{CRATE_DEF_ID, CrateNum, DefId, LOCAL_CRATE, LocalDefId};
use rustc_span::edition::DEFAULT_EDITION;
use rustc_span::hygiene::AstPass;
use rustc_span::source_map::{RealFileLoader, SourceMapInputs};
use rustc_span::{FileName, Ident, LocalExpnId, SourceFileHashAlgorithm, Symbol, kw};
use trust_process_isolation::{
    Admission, Budget, Envelope, Limits, Message, PROTOCOL_VERSION, Phase, Tree,
};

use super::*;
use crate::base::{
    DeriveResolution, ExtCtxt, Indeterminate, ResolverExpand, SyntaxExtension, SyntaxExtensionKind,
};
use crate::expand::{AstFragment, ExpansionConfig, Invocation};

struct Resolver {
    tools: RegisteredTools,
    quoted: Vec<Span>,
    walks: Rc<Cell<usize>>,
    node: u32,
}

impl ResolverExpand for Resolver {
    fn next_node_id(&mut self) -> NodeId {
        self.node += 1;
        NodeId::from_u32(self.node)
    }
    fn invocation_parent(&self, _: LocalExpnId) -> LocalDefId {
        CRATE_DEF_ID
    }
    fn resolve_dollar_crates(&self) {
        self.walks.set(self.walks.get() + 1);
    }
    fn visit_ast_fragment_with_placeholders(&mut self, _: LocalExpnId, _: &AstFragment) {
        panic!("unexpected monotonic expansion");
    }
    fn register_builtin_macro(&mut self, _: Symbol, _: SyntaxExtensionKind) {
        panic!("unexpected macro registration");
    }
    fn expansion_for_ast_pass(
        &mut self,
        _: Span,
        _: AstPass,
        _: &[Symbol],
        _: Option<NodeId>,
    ) -> LocalExpnId {
        panic!("unexpected AST pass");
    }
    fn resolve_imports(&mut self) {
        panic!("unexpected monotonic import resolution");
    }
    fn resolve_macro_invocation(
        &mut self,
        _: &Invocation,
        _: LocalExpnId,
        _: bool,
    ) -> Result<Arc<SyntaxExtension>, Indeterminate> {
        panic!("fixture cannot resolve macros");
    }
    fn record_macro_rule_usage(&mut self, _: NodeId, _: usize) {
        panic!("unexpected macro rule");
    }
    fn check_unused_macros(&mut self) {
        panic!("unexpected macro check");
    }
    fn has_derive_copy(&self, _: LocalExpnId) -> bool {
        false
    }
    fn has_derive_ord(&self, _: LocalExpnId) -> bool {
        false
    }
    fn resolve_derives(
        &mut self,
        _: LocalExpnId,
        _: bool,
        _: &dyn Fn() -> Vec<DeriveResolution>,
    ) -> Result<(), Indeterminate> {
        panic!("unexpected derive");
    }
    fn take_derive_resolutions(&mut self, _: LocalExpnId) -> Option<Vec<DeriveResolution>> {
        None
    }
    fn cfg_accessible(&mut self, _: LocalExpnId, _: &ast::Path) -> Result<bool, Indeterminate> {
        panic!("unexpected cfg lookup");
    }
    fn macro_accessible(&mut self, _: LocalExpnId, _: &ast::Path) -> Result<bool, Indeterminate> {
        panic!("unexpected macro lookup");
    }
    fn get_proc_macro_quoted_span(&self, krate: CrateNum, id: usize) -> Option<Span> {
        assert_eq!(krate, LOCAL_CRATE);
        self.quoted.get(id).copied()
    }
    fn declare_proc_macro(&mut self, _: NodeId) {
        panic!("unexpected macro declaration");
    }
    fn append_stripped_cfg_item(&mut self, _: NodeId, _: Ident, _: CfgEntry, _: Span) {
        panic!("unexpected cfg item");
    }
    fn registered_attr_tools(&self) -> &RegisteredTools {
        &self.tools
    }
    fn registered_lint_tools(&self) -> &RegisteredTools {
        &self.tools
    }
    fn register_glob_delegation(&mut self, _: LocalExpnId) {
        panic!("unexpected glob delegation");
    }
    fn glob_delegation_suffixes(
        &self,
        _: DefId,
        _: LocalDefId,
        _: Span,
    ) -> Result<Vec<(Ident, Option<Ident>)>, Indeterminate> {
        panic!("unexpected glob suffixes");
    }
    fn insert_impl_trait_name(&mut self, _: NodeId, _: Symbol) {
        panic!("unexpected impl trait");
    }
    fn mark_scope_with_compile_error(&mut self, _: NodeId) {}
}

fn limits() -> Limits {
    Limits {
        frame_bytes: 1 << 20,
        wire_bytes: 1 << 24,
        allocation_bytes: 1 << 28,
        values: 1 << 20,
        work: 1 << 24,
        calls: 1024,
        live_handles: 4096,
        depth: 32,
    }
}

fn binding() -> Binding {
    Binding {
        version: PROTOCOL_VERSION,
        invocation: 17,
        compiler: [1; 32],
        worker: [2; 32],
        artifact: [3; 32],
        metadata: [4; 32],
        unit: [5; 32],
        input_closure: [6; 32],
        host_abi: [7; 32],
    }
}

fn with_dispatcher(
    f: impl FnOnce(&mut Dispatcher<'_, '_>, &mut Session, &CompilerSession, &Cell<usize>),
) {
    with_dispatcher_deadline(Duration::from_secs(30), f)
}

fn with_dispatcher_deadline(
    duration: Duration,
    f: impl FnOnce(&mut Dispatcher<'_, '_>, &mut Session, &CompilerSession, &Cell<usize>),
) {
    let budget = Budget::new(limits(), Instant::now() + duration).unwrap();
    with_unstarted_dispatcher(budget, binding(), |dispatcher, mut session, sess, walks| {
        // Synthetic Ready remains explicit for the in-process unit tests. The
        // owned-child tests below instead receive it from the retained FD3.
        session
            .receive(Envelope { binding: session.binding().clone(), message: Message::Ready })
            .unwrap();
        f(dispatcher, &mut session, sess, walks);
    });
}

fn with_unstarted_dispatcher(
    budget: Budget,
    binding: Binding,
    f: impl FnOnce(&mut Dispatcher<'_, '_>, Session, &CompilerSession, &Cell<usize>),
) {
    let mut options = Options::default();
    options.unstable_opts.trust_verify = TrustVerify::Off;
    options.logical_env.insert("B1_INJECTED".into(), "compiler-owned".into());
    let early = EarlyDiagCtxt::new(ErrorOutputType::default());
    let target = config::build_target_config(
        &early,
        &options.target_triple,
        options.sysroot.path(),
        options.unstable_opts.unstable_options,
    );
    let sm_inputs = SourceMapInputs {
        file_loader: Box::new(RealFileLoader),
        path_mapping: options.file_path_mapping(),
        hash_kind: SourceFileHashAlgorithm::Sha256,
        checksum_hash_kind: None,
    };
    rustc_span::create_session_globals_then(DEFAULT_EDITION, &[], Some(sm_inputs), || {
        static INTERNAL: AtomicBool = AtomicBool::new(false);
        let io = CompilerIO {
            input: Input::Str {
                name: FileName::Custom("dispatch.rs".into()),
                input: "alpha beta".into(),
            },
            output_dir: None,
            output_file: None,
            temps_dir: None,
        };
        let sess = rustc_session::build_session(
            rustc_session::build_early_session(options, target, None),
            CodegenBackendInit::default(),
            io,
            Default::default(),
            "",
            &INTERNAL,
        );
        let input = rustc_parse::source_str_to_stream(
            &sess.psess,
            FileName::Custom("dispatch.rs".into()),
            "alpha beta".into(),
            None,
        )
        .unwrap();
        let call_site = input.get(0).unwrap().span();
        let mixed_site = input.get(1).unwrap().span();
        let walks = Rc::new(Cell::new(0));
        let mut resolver = Resolver {
            tools: Default::default(),
            quoted: vec![call_site],
            walks: walks.clone(),
            node: 10,
        };
        let features = Features::default();
        let mut ecx = ExtCtxt::new(
            &sess,
            ExpansionConfig::default(kw::Crate, &features),
            &mut resolver,
            None,
        );
        // Only test construction bypasses Rustc::new's macro-expansion lookup.
        // Every operation below is the real Rustc Server implementation.
        let server = Rustc {
            ecx: &mut ecx,
            def_site: call_site,
            call_site,
            mixed_site,
            krate: LOCAL_CRATE,
            rebased_spans: Default::default(),
        };
        let session = Session::new(binding, budget).unwrap();
        let mut dispatcher = Dispatcher::new(server, &session).unwrap();
        f(&mut dispatcher, session, &sess, &walks);
    });
}

fn admit(session: &mut Session, id: u64, method: Method, arguments: Vec<Value>) -> Call {
    let call = Call { id, method, arguments };
    let incoming = Envelope { binding: session.binding().clone(), message: Message::Call(call) };
    let Admission::Call(call) = session.receive(incoming).unwrap() else {
        panic!("call not admitted");
    };
    call
}

fn invoke(
    d: &mut Dispatcher<'_, '_>,
    s: &mut Session,
    seen: &mut Vec<Method>,
    method: Method,
    args: Vec<Value>,
) -> Value {
    let call = admit(s, seen.len() as u64 + 1, method, args);
    seen.push(method);
    let id = call.id;
    let value = d.dispatch(s, call).unwrap();
    let reply = s.reply(id, value).unwrap();
    let Message::Reply { value, .. } = reply.message else {
        panic!("not a reply");
    };
    assert!(method.response().accepts(&value));
    value
}

fn stream(value: Value) -> Handle {
    match value {
        Value::Stream(h) => h,
        Value::Result { ok: true, value } => stream(*value),
        _ => panic!("not a stream"),
    }
}

fn span(value: Value) -> Handle {
    match value {
        Value::Span(h) | Value::OptionalSpan(Some(h)) => h,
        _ => panic!("not a span"),
    }
}

#[test]
fn every_method_forwards_to_the_real_compiler_server() {
    with_dispatcher(|d, s, sess, walks| {
        let mut seen = Vec::new();
        macro_rules! call {
            ($m:ident, $args:expr) => {
                invoke(d, s, &mut seen, Method::$m, $args)
            };
        }
        let [def, at, mixed] = d.globals();
        assert_eq!(
            call!(InjectedEnvVar, vec![Value::Text("B1_INJECTED".into())]),
            Value::OptionalText(Some("compiler-owned".into()))
        );
        call!(
            TrackEnvVar,
            vec![Value::Text("B1_TRACKED".into()), Value::OptionalText(Some("value".into()))]
        );
        call!(TrackPath, vec![Value::Text("declared-input".into())]);
        assert!(
            sess.env_depinfo.borrow().iter().any(
                |(k, v)| k.as_str() == "B1_TRACKED" && v.is_some_and(|v| v.as_str() == "value")
            )
        );
        assert!(sess.file_depinfo.borrow().iter().any(|k| k.as_str() == "declared-input"));
        assert!(matches!(
            call!(LiteralFromStr, vec![Value::Text("13u8".into())]),
            Value::Result { ok: true, .. }
        ));

        let a = stream(call!(TsFromStr, vec![Value::Text("42".into())]));
        let copied = stream(call!(TsClone, vec![Value::Stream(a)]));
        assert_eq!(call!(TsIsEmpty, vec![Value::Stream(copied)]), Value::Bool(false));
        assert_eq!(call!(TsToString, vec![Value::Stream(copied)]), Value::Text("42".into()));
        let expanded = stream(call!(TsExpandExpr, vec![Value::Stream(a)]));
        assert_eq!(d.server.ts_to_string(&d.tokens.stream(expanded).unwrap()), "42");
        assert!(walks.get() > 0, "the real eager-expansion walk did not run");

        let tree = Tree::Ident { symbol: "item".into(), is_raw: false, span: at };
        let from_tree = stream(call!(TsFromTokenTree, vec![Value::Tree(Box::new(tree.clone()))]));
        let from_trees = stream(call!(
            TsConcatTrees,
            vec![Value::OptionalStream(Some(from_tree)), Value::Trees(vec![tree])]
        ));
        let joined = stream(call!(
            TsConcatStreams,
            vec![Value::OptionalStream(Some(from_trees)), Value::Streams(vec![copied])]
        ));
        assert!(
            matches!(call!(TsIntoTrees, vec![Value::Stream(joined)]), Value::Trees(ref trees) if trees.len()==3)
        );
        call!(TsDrop, vec![Value::Stream(a)]);

        assert!(
            matches!(call!(SpanDebug, vec![Value::Span(at)]), Value::Text(ref x) if !x.is_empty())
        );
        assert_eq!(call!(SpanParent, vec![Value::Span(at)]), Value::OptionalSpan(None));
        let source = span(call!(SpanSource, vec![Value::Span(at)]));
        assert_eq!(d.tokens.span(source).unwrap(), d.tokens.span(at).unwrap());
        assert_eq!(call!(SpanByteRange, vec![Value::Span(at)]), Value::Range { start: 0, end: 5 });
        let start = span(call!(SpanStart, vec![Value::Span(at)]));
        let end = span(call!(SpanEnd, vec![Value::Span(at)]));
        assert!(d.tokens.span(start).unwrap().is_empty());
        assert!(d.tokens.span(end).unwrap().is_empty());
        assert_eq!(call!(SpanLine, vec![Value::Span(at)]), Value::U64(1));
        assert_eq!(call!(SpanColumn, vec![Value::Span(at)]), Value::U64(1));
        assert!(
            matches!(call!(SpanFile, vec![Value::Span(at)]), Value::Text(ref x) if x.contains("dispatch.rs"))
        );
        assert_eq!(call!(SpanLocalFile, vec![Value::Span(at)]), Value::OptionalText(None));
        let joined_span = span(call!(SpanJoin, vec![Value::Span(at), Value::Span(mixed)]));
        assert_eq!(
            sess.source_map().span_to_snippet(d.tokens.span(joined_span).unwrap()).unwrap(),
            "alpha beta"
        );
        let sub = span(call!(
            SpanSubspan,
            vec![
                Value::Span(at),
                Value::Bound(trust_process_isolation::Bound::Included(1)),
                Value::Bound(trust_process_isolation::Bound::Excluded(4))
            ]
        ));
        assert_eq!(sess.source_map().span_to_snippet(d.tokens.span(sub).unwrap()).unwrap(), "lph");
        let resolved = span(call!(SpanResolvedAt, vec![Value::Span(at), Value::Span(def)]));
        assert_eq!(d.tokens.span(resolved).unwrap().ctxt(), d.tokens.span(def).unwrap().ctxt());
        assert_eq!(
            call!(SpanSourceText, vec![Value::Span(at)]),
            Value::OptionalText(Some("alpha".into()))
        );
        assert_eq!(call!(SpanSaveSpan, vec![Value::Span(at)]), Value::U64(0));
        assert_eq!(sess.proc_macro_quoted_spans().next().unwrap().1, d.tokens.span(at).unwrap());
        let recovered = span(call!(SpanRecoverProcMacroSpan, vec![Value::U64(0)]));
        assert_eq!(d.tokens.span(recovered).unwrap(), d.tokens.span(def).unwrap());
        assert_eq!(
            call!(SymbolNormalizeAndValidateIdent, vec![Value::Text("e\u{301}".into())]),
            Value::Result { ok: true, value: Box::new(Value::Text("é".into())) }
        );
        let before = sess.dcx().err_count();
        call!(
            EmitDiagnostic,
            vec![Value::Diagnostic(Box::new(trust_process_isolation::Diagnostic {
                level: 0,
                message: "B1 diagnostic fixture".into(),
                spans: vec![at],
                children: vec![]
            }))]
        );
        assert_eq!(sess.dcx().err_count(), before + 1);
        let mut tags: Vec<_> = seen.iter().map(|m| m.tag()).collect();
        tags.sort_unstable();
        tags.dedup();
        assert_eq!(tags, Method::ALL.iter().map(|m| m.tag()).collect::<Vec<_>>());
        assert_eq!(s.budget().usage().unwrap().calls, seen.len() as u64);
    });
}

#[test]
fn native_semantic_errors_remain_typed_results() {
    with_dispatcher(|d, s, _, _| {
        let mut seen = Vec::new();
        assert!(matches!(
            invoke(d, s, &mut seen, Method::LiteralFromStr, vec![Value::Text("identifier".into())]),
            Value::Result { ok: false, .. }
        ));
        assert_eq!(
            invoke(
                d,
                s,
                &mut seen,
                Method::SymbolNormalizeAndValidateIdent,
                vec![Value::Text("0bad".into())]
            ),
            Value::Result { ok: false, value: Box::new(Value::Unit) }
        );
        let source = d.server.ts_from_str("1 + 2").unwrap();
        let input = d.store_input(source).unwrap();
        assert_eq!(
            invoke(d, s, &mut seen, Method::TsExpandExpr, vec![Value::Stream(input)]),
            Value::Result { ok: false, value: Box::new(Value::Unit) }
        );
        let at = d.globals()[1];
        assert_eq!(
            invoke(
                d,
                s,
                &mut seen,
                Method::SpanSubspan,
                vec![
                    Value::Span(at),
                    Value::Bound(trust_process_isolation::Bound::Included(100)),
                    Value::Bound(trust_process_isolation::Bound::Unbounded)
                ]
            ),
            Value::OptionalSpan(None)
        );
        assert_eq!(s.phase(), Phase::Active);
    });
}

#[test]
fn hostile_calls_fail_before_compiler_effects_and_poison_the_session() {
    for mode in 0..5 {
        with_dispatcher(|d, s, sess, _| {
            let at = d.globals()[1];
            let input = d
                .store_input(
                    rustc_parse::source_str_to_stream(
                        &sess.psess,
                        FileName::Custom("input".into()),
                        "value".into(),
                        None,
                    )
                    .unwrap(),
                )
                .unwrap();
            let (method, args) = match mode {
                0 => (
                    Method::TsConcatStreams,
                    vec![Value::OptionalStream(Some(input)), Value::Streams(vec![input])],
                ),
                1 => {
                    let mut h = at;
                    h.invocation += 1;
                    (Method::SpanSourceText, vec![Value::Span(h)])
                }
                2 => {
                    let mut h = at;
                    h.generation += 1;
                    (Method::SpanFile, vec![Value::Span(h)])
                }
                3 => (Method::SpanRecoverProcMacroSpan, vec![Value::U64(u64::MAX)]),
                _ => {
                    // The wire tag is Span, but the slot actually owns a
                    // stream. This remains a valid frame and must be refused
                    // by the compiler-owned table before emitting anything.
                    let mut wrong = input;
                    wrong.kind = trust_process_isolation::HandleKind::Span;
                    (
                        Method::EmitDiagnostic,
                        vec![Value::Diagnostic(Box::new(trust_process_isolation::Diagnostic {
                            level: 0,
                            message: "must not emit".into(),
                            spans: vec![wrong],
                            children: vec![],
                        }))],
                    )
                }
            };
            let call = admit(s, 1, method, args);
            let before = sess.dcx().err_count();
            assert!(d.dispatch(s, call).is_err());
            assert_eq!(sess.dcx().err_count(), before);
            assert_eq!(s.phase(), Phase::Terminal);
            assert_eq!(d.tokens.values.live(), 0);
            assert!(d.tokens.budget.check().is_err());
        });
    }
}

#[test]
fn a_different_session_or_unadmitted_call_cannot_change_dependencies() {
    for unadmitted in [false, true] {
        with_dispatcher(|d, s, sess, _| {
            let call = Call {
                id: 1,
                method: Method::TrackPath,
                arguments: vec![Value::Text("forbidden-effect".into())],
            };
            if unadmitted {
                assert!(d.dispatch(s, call).is_err());
            } else {
                let budget = Budget::new(limits(), d.tokens.budget.deadline()).unwrap();
                let mut other = Session::new(binding(), budget).unwrap();
                other.receive(Envelope { binding: binding(), message: Message::Ready }).unwrap();
                let call = admit(&mut other, call.id, call.method, call.arguments);
                assert!(d.dispatch(&mut other, call).is_err());
            }
            assert!(!sess.file_depinfo.borrow().iter().any(|x| x.as_str() == "forbidden-effect"));
        });
    }
}

#[test]
fn parser_depth_is_checked_before_creating_a_source_file() {
    for method in [Method::TsFromStr, Method::LiteralFromStr] {
        with_dispatcher(|d, s, sess, _| {
            let before = sess.source_map().files().len();
            let call = admit(s, 1, method, vec![Value::Text("(".repeat(256))]);
            assert_eq!(d.dispatch(s, call).unwrap_err(), Error::Budget("depth"));
            assert_eq!(sess.source_map().files().len(), before);
        });
    }
}

#[test]
fn nested_diagnostics_are_refused_instead_of_silently_discarded() {
    with_dispatcher(|d, s, sess, _| {
        let leaf = trust_process_isolation::Diagnostic {
            level: 2,
            message: "nested".into(),
            spans: vec![],
            children: vec![],
        };
        let mut child = leaf.clone();
        child.children.push(leaf);
        let root = trust_process_isolation::Diagnostic {
            level: 0,
            message: "not emitted".into(),
            spans: vec![],
            children: vec![child],
        };
        let call = admit(s, 1, Method::EmitDiagnostic, vec![Value::Diagnostic(Box::new(root))]);
        assert_eq!(d.dispatch(s, call).unwrap_err(), Error::InvalidWire("nested subdiagnostic"));
        assert_eq!(sess.dcx().err_count(), 0);
    });
}

#[test]
fn cancellation_and_binding_substitution_cannot_reach_compiler_effects() {
    for substitute in [false, true] {
        with_dispatcher(|d, s, sess, _| {
            let args = vec![Value::Text("must-not-track".into())];
            if substitute {
                let mut changed = binding();
                changed.artifact[0] ^= 1;
                let mut other = Session::new(changed.clone(), s.budget().clone()).unwrap();
                other.receive(Envelope { binding: changed, message: Message::Ready }).unwrap();
                let call = admit(&mut other, 1, Method::TrackPath, args);
                assert_eq!(d.dispatch(&mut other, call).unwrap_err(), Error::Identity);
            } else {
                let call = admit(s, 1, Method::TrackPath, args);
                s.budget().cancel();
                assert!(d.dispatch(s, call).is_err());
                assert_eq!(s.phase(), Phase::Terminal);
            }
            assert!(!sess.file_depinfo.borrow().iter().any(|p| p.as_str() == "must-not-track"));
            assert!(s.budget().check().is_err());
            assert_eq!(d.tokens.values.live(), 0);
        });
    }
}

#[test]
fn a_late_invalid_handle_is_checked_before_any_argument_is_parsed_or_consumed() {
    with_dispatcher(|d, s, sess, _| {
        let source = rustc_parse::source_str_to_stream(
            &sess.psess,
            FileName::Custom("late-handle-input".into()),
            "value".into(),
            None,
        )
        .unwrap();
        let input = d.store_input(source).unwrap();
        let at = d.globals()[1];
        let mut stale = at;
        stale.generation += 1;
        let trees = vec![
            Tree::Literal(trust_process_isolation::Literal {
                kind: 2,
                raw_hashes: 0,
                symbol: "12".into(),
                suffix: None,
                span: at,
            }),
            Tree::Ident { symbol: "later".into(), is_raw: false, span: stale },
        ];
        let before = sess.source_map().files().len();
        let call = admit(
            s,
            1,
            Method::TsConcatTrees,
            vec![Value::OptionalStream(Some(input)), Value::Trees(trees)],
        );
        assert!(matches!(d.dispatch(s, call), Err(Error::Handle(_))));
        assert_eq!(sess.source_map().files().len(), before);
        assert_eq!(d.tokens.values.live(), 0);
    });
}

#[cfg(unix)]
#[test]
fn non_utf8_local_paths_refuse_before_the_native_string_conversion() {
    use std::ffi::OsString;
    use std::os::unix::ffi::OsStringExt;
    use std::path::PathBuf;

    use rustc_span::RealFileName;

    with_dispatcher(|d, s, sess, _| {
        let path = PathBuf::from(OsString::from_vec(b"/synthetic/source-\xff.rs".to_vec()));
        let filename =
            sess.opts.file_path_mapping().to_real_filename(&RealFileName::empty(), &path);
        let source = rustc_parse::source_str_to_stream(
            &sess.psess,
            FileName::Real(filename),
            "item".into(),
            None,
        )
        .unwrap();
        let span = d.tokens.store_span(source.get(0).unwrap().span()).unwrap();
        let call = admit(s, 1, Method::SpanLocalFile, vec![Value::Span(span)]);
        assert_eq!(
            d.dispatch(s, call).unwrap_err(),
            Error::InvalidWire("non-UTF8 local source path")
        );
        assert_eq!(s.phase(), Phase::Terminal);
    });
}

#[test]
fn changing_admitted_arguments_cannot_execute_or_consume_a_different_handle() {
    for text in [true, false] {
        with_dispatcher(|d, s, sess, _| {
            let (original, substitute) = if text {
                (
                    admit(s, 1, Method::TrackPath, vec![Value::Text("original-path".into())]),
                    Value::Text("substituted-path".into()),
                )
            } else {
                let first = d.server.ts_from_str("first").unwrap();
                let second = d.server.ts_from_str("second").unwrap();
                let first = d.store_input(first).unwrap();
                let second = d.store_input(second).unwrap();
                (admit(s, 1, Method::TsDrop, vec![Value::Stream(first)]), Value::Stream(second))
            };
            let mut changed = original.clone();
            changed.arguments[0] = substitute;
            assert_eq!((original.id, original.method), (changed.id, changed.method));
            assert_eq!(d.dispatch(s, changed).unwrap_err(), Error::Identity);
            assert!(
                !sess
                    .file_depinfo
                    .borrow()
                    .iter()
                    .any(|p| matches!(p.as_str(), "original-path" | "substituted-path"))
            );
            assert_eq!(s.phase(), Phase::Terminal);
            assert_eq!(d.tokens.values.live(), 0); // terminal cleanup, not a dispatched drop
            assert_eq!(s.budget().check(), Err(Error::Identity));
        });
    }
}

#[test]
fn an_identical_binding_and_shared_budget_cannot_replace_the_original_session() {
    for finished in [false, true] {
        with_dispatcher(|d, s, sess, _| {
            if finished {
                s.receive(Envelope {
                    binding: s.binding().clone(),
                    message: Message::Finish { output: None },
                })
                .unwrap();
            } else {
                let _pending =
                    admit(s, 1, Method::TrackPath, vec![Value::Text("original-pending".into())]);
            }
            let mut replacement = Session::new(s.binding().clone(), s.budget().clone()).unwrap();
            replacement
                .receive(Envelope {
                    binding: replacement.binding().clone(),
                    message: Message::Ready,
                })
                .unwrap();
            let call = admit(
                &mut replacement,
                1,
                Method::TrackPath,
                vec![Value::Text("replacement-session".into())],
            );
            assert_eq!(d.dispatch(&mut replacement, call).unwrap_err(), Error::Identity);
            assert!(
                !sess
                    .file_depinfo
                    .borrow()
                    .iter()
                    .any(|p| matches!(p.as_str(), "original-pending" | "replacement-session"))
            );
            assert_eq!(s.budget().check(), Err(Error::Identity));
            assert_eq!(replacement.budget().check(), Err(Error::Identity));
            assert_eq!(d.tokens.values.live(), 0);
            assert!(
                s.receive(Envelope {
                    binding: s.binding().clone(),
                    message: Message::Finish { output: None }
                })
                .is_err()
            );
        });
    }
}

#[test]
fn moving_the_original_session_preserves_dispatch_and_sequence() {
    with_dispatcher(|d, s, sess, _| {
        let placeholder = Session::new(s.binding().clone(), s.budget().clone()).unwrap();
        let mut moved = std::mem::replace(s, placeholder);
        let mut seen = Vec::new();
        for name in ["first-valid", "second-valid"] {
            assert_eq!(
                invoke(d, &mut moved, &mut seen, Method::TrackPath, vec![Value::Text(name.into())]),
                Value::Unit
            );
        }
        assert_eq!(moved.phase(), Phase::Active);
        assert_eq!(moved.budget().usage().unwrap().calls, 2);
        assert!(sess.file_depinfo.borrow().iter().any(|p| p.as_str() == "first-valid"));
        assert!(sess.file_depinfo.borrow().iter().any(|p| p.as_str() == "second-valid"));
    });
}

#[test]
fn native_client_span_equality_control_matches_rustc_span_identity() {
    with_dispatcher(|d, _, _, _| {
        let input = d.server.ts_from_str("native_control").unwrap();
        let server = Rustc {
            ecx: &mut *d.server.ecx,
            def_site: d.server.def_site,
            call_site: d.server.call_site,
            mixed_site: d.server.mixed_site,
            krate: d.server.krate,
            rebased_spans: Default::default(),
        };
        let client = rustc_proc_macro::bridge::client::Client::expand1(|input| {
            let span = rustc_proc_macro::Span::call_site();
            assert!(span.eq(&span.source()));
            assert!(span.eq(&span.resolved_at(span)));
            assert!(!span.eq(&rustc_proc_macro::Span::mixed_site()));
            let literal: rustc_proc_macro::Literal = "1".parse().unwrap();
            assert!(literal.span().eq(&span));
            input
        });
        let result =
            client.run1(&rustc_proc_macro::bridge::server::SAME_THREAD, server, input, false);
        let output =
            result.unwrap_or_else(|e| panic!("native client equality failed: {:?}", e.as_str()));
        assert_eq!(d.server.ts_to_string(&output), "native_control");
    });
}

// Trust (D21): exact native ABI through B1 and this compiler dispatcher.
mod worker;

// Trust (D21): actual subprocess/native ABI over bounded Unix socket transport.
#[cfg(any(target_os = "linux", target_os = "macos"))]
mod ipc;

// Trust (PM-1): real compiler dispatcher through the owned B3 static child.
#[cfg(target_os = "linux")]
mod owned;
