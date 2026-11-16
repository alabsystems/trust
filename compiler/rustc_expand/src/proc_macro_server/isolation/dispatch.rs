//! Trust (D21): the complete B1 method dispatcher over the real Rustc server.
//!
//! This consumes calls already admitted by B1's Session. It neither starts a
//! worker nor produces Ready; `launch.rs` owns the worker process and drives
//! this dispatcher for each expansion under `-Ztrust-proc-macro-isolation`.
//! Native compiler operations are opaque intervals: the original deadline is
//! checked around them, not claimed to interrupt them or bound process RSS.

use std::ops::Bound;

use rustc_ast::tokenstream::TokenStream;
use rustc_proc_macro::Level;
use rustc_proc_macro::bridge::Diagnostic;
use rustc_proc_macro::bridge::server::Server;
use rustc_span::Span;
use trust_process_isolation::{
    Binding, Call, Charge, Error, Handle, Method, Session, SessionOwner, Value,
};

use super::super::Rustc;
use super::{NativeTree, OwnedValue, TokenAdapter};

pub(crate) struct Dispatcher<'a, 'b> {
    server: Rustc<'a, 'b>,
    tokens: TokenAdapter,
    binding: Binding,
    session_owner: SessionOwner,
    globals: [Handle; 3],
}

enum Argument<'a> {
    Text(&'a str),
    OptionalText(Option<&'a str>),
    Stream(TokenStream),
    OptionalStream(Option<TokenStream>),
    Streams(Vec<TokenStream>),
    Span(Span),
    Tree(NativeTree),
    Trees(Vec<NativeTree>),
    Bound(Bound<usize>),
    Index(usize),
    Diagnostic(Diagnostic<Span>),
}

impl<'a, 'b> Dispatcher<'a, 'b> {
    pub(crate) fn new(mut server: Rustc<'a, 'b>, session: &Session) -> Result<Self, Error> {
        let mut tokens = TokenAdapter::new(session.binding().invocation, session.budget().clone())?;
        let native = server.globals();
        let globals = [
            tokens.store_span(native.def_site)?,
            tokens.store_span(native.call_site)?,
            tokens.store_span(native.mixed_site)?,
        ];
        Ok(Self {
            server,
            tokens,
            binding: session.binding().clone(),
            session_owner: session.owner(),
            globals,
        })
    }

    /// These are compiler-issued Begin inputs, not worker attestations.
    pub(crate) fn globals(&self) -> [Handle; 3] {
        self.globals
    }

    pub(crate) fn store_input(&mut self, stream: TokenStream) -> Result<Handle, Error> {
        self.tokens.store_stream(stream)
    }

    /// The stream a `Finish` the session admitted names; no handle is the
    /// native ABI's empty stream.
    pub(crate) fn output(&self, handle: Option<Handle>) -> Result<TokenStream, Error> {
        match handle {
            Some(handle) => self.tokens.stream(handle),
            None => Ok(TokenStream::default()),
        }
    }

    /// End the invocation: no handle it issued can be used again.
    pub(crate) fn finish(&mut self) {
        self.tokens.clear();
    }

    pub(crate) fn dispatch(&mut self, session: &mut Session, call: Call) -> Result<Value, Error> {
        // A numerically identical budget or binding is not the original grant.
        if !self.session_owner.matches(session)
            || session.binding() != &self.binding
            || !self.tokens.budget.shares_owner(session.budget())
        {
            return self.tokens.finish(Err(Error::Identity));
        }
        let result = (|| {
            session.validate_pending_call(&call)?;
            self.tokens.charge_storage::<u8>(4096)?;
            self.tokens.budget.charge(Charge { work: 1, ..Charge::default() })?;
            if call.method == Method::InjectedEnvVar {
                if let [Value::Text(name)] = call.arguments.as_slice() {
                    if let Some(value) = self.server.sess().opts.logical_env.get(name) {
                        self.tokens.charge_text(value)?;
                    }
                }
            }
            let uses = call.handle_uses(&self.tokens.budget)?;
            // Check every handle before parsing composite arguments or taking
            // anything. B1 then validates the complete alias transaction.
            for usage in &uses {
                match self.tokens.values.get(usage.handle)? {
                    OwnedValue::Stream(stream) => self.tokens.preflight(stream, 0)?,
                    OwnedValue::Span(_) => {
                        self.tokens.span(usage.handle)?;
                    }
                }
            }
            let mut arguments = self.tokens.reserve(call.arguments.len())?;
            for value in &call.arguments {
                arguments.push(self.prepare(value)?);
            }
            if matches!(call.method, Method::TsFromStr | Method::LiteralFromStr) {
                let [Argument::Text(source)] = arguments.as_slice() else {
                    return Err(Error::Schema);
                };
                self.bound_source(source)?;
            }
            if call.method == Method::SpanSourceText {
                let [Argument::Span(span)] = arguments.as_slice() else {
                    return Err(Error::Schema);
                };
                self.tokens.charge_storage::<u8>((span.hi() - span.lo()).0 as usize)?;
            }
            if call.method == Method::SpanLocalFile {
                let [Argument::Span(span)] = arguments.as_slice() else {
                    return Err(Error::Schema);
                };
                if self
                    .server
                    .psess()
                    .source_map()
                    .lookup_source_file(span.lo())
                    .name
                    .clone()
                    .into_local_path()
                    .is_some_and(|p| p.to_str().is_none())
                {
                    return Err(Error::InvalidWire("non-UTF8 local source path"));
                }
            }
            // Keep the original values alive through the native call. Prepared
            // stream clones preserve native value semantics, not extra handles.
            let _consumed = self.tokens.values.consume(&uses)?;
            self.tokens.budget.check()?;
            let value = self.execute(call.method, arguments)?;
            self.tokens.budget.check()?;
            if !call.method.response().accepts(&value) {
                return Err(Error::Schema);
            }
            // Trust: the transport owns the pending-call/reply transition. It
            // uses this same Session after the compiler has admitted the value.
            Ok(value)
        })();
        if result.is_err() {
            let result = self.tokens.finish(result);
            // Close the bound protocol session too; transport owns whether a
            // cancellation frame is sent and retains process cleanup custody.
            let _ = session.cancel();
            result
        } else {
            result
        }
    }

    fn prepare<'v>(&self, value: &'v Value) -> Result<Argument<'v>, Error> {
        Ok(match value {
            Value::Text(s) => {
                self.tokens.charge_text(s)?;
                Argument::Text(s)
            }
            Value::OptionalText(s) => {
                if let Some(s) = s {
                    self.tokens.charge_text(s)?;
                }
                Argument::OptionalText(s.as_deref())
            }
            Value::Stream(h) => Argument::Stream(self.tokens.stream(*h)?),
            Value::OptionalStream(h) => {
                Argument::OptionalStream(h.map(|h| self.tokens.stream(h)).transpose()?)
            }
            Value::Streams(handles) => {
                let mut streams = self.tokens.reserve(handles.len())?;
                for h in handles {
                    streams.push(self.tokens.stream(*h)?);
                }
                Argument::Streams(streams)
            }
            Value::Span(h) => Argument::Span(self.tokens.span(*h)?),
            Value::Tree(tree) => {
                let mut uses = self.tokens.reserve(4)?;
                Argument::Tree(self.tokens.import_tree(self.server.psess(), tree, &mut uses)?)
            }
            Value::Trees(trees) => {
                let mut native = self.tokens.reserve(trees.len())?;
                let mut uses =
                    self.tokens.reserve(trees.len().checked_mul(4).ok_or(Error::Overflow)?)?;
                for tree in trees {
                    native.push(self.tokens.import_tree(self.server.psess(), tree, &mut uses)?);
                }
                Argument::Trees(native)
            }
            Value::U64(index) => {
                Argument::Index(usize::try_from(*index).map_err(|_| Error::Overflow)?)
            }
            Value::Bound(bound) => Argument::Bound(match bound {
                trust_process_isolation::Bound::Included(n) => {
                    Bound::Included(usize::try_from(*n).map_err(|_| Error::Overflow)?)
                }
                trust_process_isolation::Bound::Excluded(n) => {
                    Bound::Excluded(usize::try_from(*n).map_err(|_| Error::Overflow)?)
                }
                trust_process_isolation::Bound::Unbounded => Bound::Unbounded,
            }),
            Value::Diagnostic(diagnostic) => Argument::Diagnostic(self.diagnostic(diagnostic, 0)?),
            _ => return Err(Error::Schema),
        })
    }

    fn diagnostic(
        &self,
        source: &trust_process_isolation::Diagnostic,
        depth: u16,
    ) -> Result<Diagnostic<Span>, Error> {
        self.tokens.budget.depth(depth)?;
        // Rustc's native emitter supports a root and subdiagnostics, but does
        // not recurse into children of those subdiagnostics. Never drop them.
        if depth > 1 {
            return Err(Error::InvalidWire("nested subdiagnostic"));
        }
        let level = match source.level {
            0 => Level::Error,
            1 => Level::Warning,
            2 => Level::Note,
            3 => Level::Help,
            _ => return Err(Error::InvalidWire("diagnostic level")),
        };
        self.tokens.charge_text(&source.message)?;
        let mut spans = self.tokens.reserve(source.spans.len())?;
        for h in &source.spans {
            spans.push(self.tokens.span(*h)?);
        }
        let mut children = self.tokens.reserve(source.children.len())?;
        for child in &source.children {
            children.push(self.diagnostic(child, depth + 1)?);
        }
        Ok(Diagnostic { level, message: source.message.clone(), spans, children })
    }

    fn bound_source(&self, source: &str) -> Result<(), Error> {
        let mut depth = 0u16;
        for token in rustc_lexer::tokenize(source, rustc_lexer::FrontmatterAllowed::No) {
            self.tokens.budget.charge(Charge {
                values: 1,
                work: u64::from(token.len) + 1,
                ..Charge::default()
            })?;
            use rustc_lexer::TokenKind as T;
            match token.kind {
                T::OpenParen | T::OpenBrace | T::OpenBracket => {
                    depth = depth.checked_add(1).ok_or(Error::Overflow)?;
                    self.tokens.budget.depth(depth)?;
                }
                T::CloseParen | T::CloseBrace | T::CloseBracket => depth = depth.saturating_sub(1),
                _ => {}
            }
        }
        // Native parser bookkeeping, in addition to charged input text.
        self.tokens.charge_storage::<u8>(4096)
    }

    fn text(&self, text: String) -> Result<Value, Error> {
        self.tokens.charge_text(&text)?;
        Ok(Value::Text(text))
    }

    fn optional_text(&self, text: Option<String>) -> Result<Value, Error> {
        if let Some(text) = &text {
            self.tokens.charge_text(text)?;
        }
        Ok(Value::OptionalText(text))
    }

    fn stream(&mut self, stream: TokenStream) -> Result<Value, Error> {
        Ok(Value::Stream(self.tokens.store_stream(stream)?))
    }

    fn span(&mut self, span: Span) -> Result<Value, Error> {
        Ok(Value::Span(self.tokens.store_span(span)?))
    }

    fn optional_span(&mut self, span: Option<Span>) -> Result<Value, Error> {
        Ok(Value::OptionalSpan(span.map(|s| self.tokens.store_span(s)).transpose()?))
    }

    fn result(&self, ok: bool, value: Value) -> Result<Value, Error> {
        self.tokens.charge_storage::<Value>(1)?;
        Ok(Value::Result { ok, value: Box::new(value) })
    }

    fn execute(&mut self, method: Method, arguments: Vec<Argument<'_>>) -> Result<Value, Error> {
        let mut args = arguments.into_iter();
        macro_rules! arg {
            ($variant:ident) => {
                match args.next() {
                    Some(Argument::$variant(value)) => value,
                    _ => return Err(Error::Schema),
                }
            };
        }
        // Exhaustive against the existing B1 enum: no catch-all success or
        // alternate implementation can silently cover a newly added method.
        match method {
            Method::InjectedEnvVar => {
                let name = arg!(Text);
                let value = self.server.injected_env_var(name);
                self.optional_text(value)
            }
            Method::TrackEnvVar => {
                let name = arg!(Text);
                let value = arg!(OptionalText);
                self.server.track_env_var(name, value);
                Ok(Value::Unit)
            }
            Method::TrackPath => {
                self.server.track_path(arg!(Text));
                Ok(Value::Unit)
            }
            Method::LiteralFromStr => match self.server.literal_from_str(arg!(Text)) {
                Ok(literal) => {
                    let tree = self
                        .tokens
                        .export_tree(rustc_proc_macro::bridge::TokenTree::Literal(literal))?;
                    let trust_process_isolation::Tree::Literal(literal) = tree else {
                        return Err(Error::Schema);
                    };
                    self.tokens.charge_storage::<trust_process_isolation::Literal>(1)?;
                    self.result(true, Value::Literal(Box::new(literal)))
                }
                Err(error) => {
                    let error = self.text(error)?;
                    self.result(false, error)
                }
            },
            Method::EmitDiagnostic => {
                self.server.emit_diagnostic(arg!(Diagnostic));
                Ok(Value::Unit)
            }
            Method::TsDrop => {
                self.server.ts_drop(arg!(Stream));
                Ok(Value::Unit)
            }
            Method::TsClone => {
                let value = self.server.ts_clone(&arg!(Stream));
                self.stream(value)
            }
            Method::TsIsEmpty => Ok(Value::Bool(self.server.ts_is_empty(&arg!(Stream)))),
            Method::TsExpandExpr => match self.server.ts_expand_expr(&arg!(Stream)) {
                Ok(stream) => {
                    let value = self.stream(stream)?;
                    self.result(true, value)
                }
                Err(()) => self.result(false, Value::Unit),
            },
            Method::TsFromStr => match self.server.ts_from_str(arg!(Text)) {
                Ok(stream) => {
                    let value = self.stream(stream)?;
                    self.result(true, value)
                }
                Err(error) => {
                    let value = self.text(error)?;
                    self.result(false, value)
                }
            },
            Method::TsToString => {
                let value = self.server.ts_to_string(&arg!(Stream));
                self.text(value)
            }
            Method::TsFromTokenTree => {
                let value = self.server.ts_from_token_tree(arg!(Tree));
                self.stream(value)
            }
            Method::TsConcatTrees => {
                let base = arg!(OptionalStream);
                let trees = arg!(Trees);
                let value = self.server.ts_concat_trees(base, trees);
                self.stream(value)
            }
            Method::TsConcatStreams => {
                let base = arg!(OptionalStream);
                let streams = arg!(Streams);
                let value = self.server.ts_concat_streams(base, streams);
                self.stream(value)
            }
            Method::TsIntoTrees => {
                let native = self.server.ts_into_trees(arg!(Stream));
                let mut trees = self.tokens.reserve(native.len())?;
                for tree in native {
                    trees.push(self.tokens.export_tree(tree)?);
                }
                Ok(Value::Trees(trees))
            }
            Method::SpanDebug => {
                let value = self.server.span_debug(arg!(Span));
                self.text(value)
            }
            Method::SpanParent => {
                let value = self.server.span_parent(arg!(Span));
                self.optional_span(value)
            }
            Method::SpanSource => {
                let value = self.server.span_source(arg!(Span));
                self.span(value)
            }
            Method::SpanByteRange => {
                let value = self.server.span_byte_range(arg!(Span));
                Ok(Value::Range { start: value.start as u64, end: value.end as u64 })
            }
            Method::SpanStart => {
                let value = self.server.span_start(arg!(Span));
                self.span(value)
            }
            Method::SpanEnd => {
                let value = self.server.span_end(arg!(Span));
                self.span(value)
            }
            Method::SpanLine => Ok(Value::U64(self.server.span_line(arg!(Span)) as u64)),
            Method::SpanColumn => Ok(Value::U64(self.server.span_column(arg!(Span)) as u64)),
            Method::SpanFile => {
                let value = self.server.span_file(arg!(Span));
                self.text(value)
            }
            Method::SpanLocalFile => {
                let value = self.server.span_local_file(arg!(Span));
                self.optional_text(value)
            }
            Method::SpanJoin => {
                let first = arg!(Span);
                let second = arg!(Span);
                let value = self.server.span_join(first, second);
                self.optional_span(value)
            }
            Method::SpanSubspan => {
                let span = arg!(Span);
                let start = arg!(Bound);
                let end = arg!(Bound);
                let value = self.server.span_subspan(span, start, end);
                self.optional_span(value)
            }
            Method::SpanResolvedAt => {
                let span = arg!(Span);
                let at = arg!(Span);
                let value = self.server.span_resolved_at(span, at);
                self.span(value)
            }
            Method::SpanSourceText => {
                let value = self.server.span_source_text(arg!(Span));
                self.optional_text(value)
            }
            Method::SpanSaveSpan => Ok(Value::U64(self.server.span_save_span(arg!(Span)) as u64)),
            Method::SpanRecoverProcMacroSpan => {
                let value = self
                    .server
                    .try_recover_proc_macro_span(arg!(Index))
                    .ok_or(Error::InvalidWire("quoted span index"))?;
                self.span(value)
            }
            Method::SymbolNormalizeAndValidateIdent => {
                match self.server.symbol_normalize_and_validate_ident(arg!(Text)) {
                    Ok(symbol) => {
                        let text = self.text(symbol.as_str().to_owned())?;
                        self.result(true, text)
                    }
                    Err(()) => self.result(false, Value::Unit),
                }
            }
        }
    }
}

#[cfg(test)]
mod tests;
