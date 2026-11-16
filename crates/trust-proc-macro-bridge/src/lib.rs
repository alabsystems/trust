//! Worker-side forwarding for the exact in-tree native proc_macro ABI.
//!
//! This does not load a DSO, launch/confine a process, or produce Ready. The
//! caller must separately admit the immutable worker/artifact and install
//! containment before entering any native constructor or client. Native ABI
//! allocation and unwinding remain inside that future disposable worker.
#![deny(unsafe_code)]
#![allow(internal_features)]
#![feature(proc_macro_internals, proc_macro_diagnostic)]

use std::mem::size_of;
use std::ops::{Bound, Range};

use rustc_proc_macro::bridge::client::Client;
use rustc_proc_macro::bridge::server::{SAME_THREAD, Server};
use rustc_proc_macro::bridge::{
    DelimSpan, Diagnostic, ExpnGlobals, Group, Ident, IdentKind, LitKind, Literal, Punct, TokenTree,
};
use rustc_proc_macro::{Delimiter, Level};
// Keep the native bridge's public path while sharing its existing B1 contract
// with restriction-only entry code, which must not depend on the native ABI.
pub use trust_process_isolation::Transport;
use trust_process_isolation::{
    Binding, Budget, Call, Charge, Envelope, Error, Handle, HandleKind, Message, Method, Tree,
    Value, decode, encode,
};

/// Opaque compiler handle. The native ABI's Default stream represents its
/// absent/empty output; methods materialize it through the real compiler parser.
/// Clone only copies the opaque identity; native `ts_clone` below obtains a new
/// compiler-owned stream. Consuming aliases are refused before transmission.
#[derive(Clone, Default)]
pub struct Stream(Option<Handle>);

#[derive(Clone, Copy)]
struct Slot {
    handle: Handle,
    live: bool,
}

/// One invocation, with compiler-issued Begin metadata and the original budget.
/// No native client can replace this binding, reset sequencing, or clear refusal.
pub struct Worker<T: Transport> {
    transport: T,
    binding: Binding,
    budget: Budget,
    globals: [Handle; 3],
    inputs: Option<Vec<Handle>>,
    declaration: u32,
    kind: u8,
    next_id: u64,
    slots: Vec<Option<Slot>>,
    /// The compiler's live-handle limit: no slot at or past it is ever recorded.
    slot_limit: usize,
    failure: Option<Error>,
    closed: bool,
}

/// How one invocation ended when no protocol, resource or transport refusal did.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Completion {
    /// The macro returned and `Finish` was delivered.
    Finished,
    /// The macro panicked and `Failure` carrying [`panic_reason`] was delivered.
    /// The connection is intact: the panic is the macro's result, as it is in
    /// process, not a fault of the worker.
    Panicked,
}

/// The `Failure` reason for a macro panic: `panic` alone when the payload was
/// not a string, else `panic:` followed by the message. Any other reason is a
/// worker fault. The compiler owns the parse ([`parse_panic_reason`]).
pub fn panic_reason(message: Option<&str>) -> String {
    match message {
        Some(message) => format!("panic:{message}"),
        None => "panic".to_owned(),
    }
}

/// `Some(message)` when `reason` is a macro panic ([`panic_reason`]).
pub fn parse_panic_reason(reason: &str) -> Option<Option<&str>> {
    match reason.strip_prefix("panic") {
        Some("") => Some(None),
        Some(rest) => rest.strip_prefix(':').map(Some),
        None => None,
    }
}

impl<T: Transport> Worker<T> {
    /// Validate an already received Begin. This grants no readiness, sandbox,
    /// loader, artifact or proof authority. There is deliberately no Ready API.
    pub fn from_begin(begin: Envelope, budget: Budget, mut transport: T) -> Result<Self, Error> {
        let result = (|| {
            // Begin was already decoded by the bounded transport. Validate
            // its existing schema without charging a second wire transfer.
            budget.check()?;
            begin.binding.validate()?;
            let Message::Begin { declaration, kind, inputs, globals } = begin.message else {
                return Err(Error::Phase);
            };
            if kind > 2 || inputs.len() != if kind == 1 { 2 } else { 1 } {
                return Err(Error::Schema);
            }
            if globals.iter().any(|h| h.kind != HandleKind::Span)
                || inputs.iter().any(|h| h.kind != HandleKind::Stream)
            {
                return Err(Error::Schema);
            }
            budget.charge(Charge {
                work: (globals.len() + inputs.len()) as u64,
                ..Charge::default()
            })?;
            let count =
                usize::try_from(budget.limits().live_handles).map_err(|_| Error::Overflow)?;
            reserve::<Option<Slot>>(&budget, count)?;
            let mut slots = Vec::new();
            slots.try_reserve_exact(count).map_err(|_| Error::Allocation)?;
            reserve::<Option<Slot>>(
                &budget,
                slots.capacity().checked_sub(count).ok_or(Error::Overflow)?,
            )?;
            // The whole table is priced and reserved above; slots are written
            // as handles arrive, so an invocation that sees forty handles does
            // not pay to initialize the limit's worth.
            for handle in globals.iter().chain(inputs.iter()) {
                record(&mut slots, count, &begin.binding, *handle)?;
            }
            Ok((begin.binding, declaration, kind, inputs, globals, slots, count))
        })();
        match result {
            Ok((binding, declaration, kind, inputs, globals, slots, slot_limit)) => Ok(Self {
                transport,
                binding,
                budget,
                globals,
                inputs: Some(inputs),
                declaration,
                kind,
                next_id: 1,
                slots,
                slot_limit,
                failure: None,
                closed: false,
            }),
            Err(error) => {
                transport.close();
                Err(budget.refuse(error))
            }
        }
    }

    /// Execute the compiler-selected declaration from the supplied exact-ABI
    /// declaration table, without loading it. The caller must first bind that
    /// table to the admitted immutable native artifact; neither the table nor
    /// its index establishes containment or proof authority. The Begin index
    /// is used here, so a caller cannot silently substitute a different Client.
    /// Successful completion sends Finish; errors close without success.
    pub fn run_declared(
        &mut self,
        declarations: &[Client],
        force_show_panics: bool,
    ) -> Result<(), Error> {
        match self.run_reported(declarations, force_show_panics)? {
            Completion::Finished => Ok(()),
            // `run_reported` has closed this invocation; only the result differs.
            Completion::Panicked => Err(Error::InvalidWire("native macro panicked")),
        }
    }

    /// [`Self::run_declared`], distinguishing a macro panic from a refusal. The
    /// panic message is sent to the compiler in `Failure`, where the in-process
    /// path reports it; a panic the macro raised after a transport refusal is
    /// that refusal, never `Panicked`.
    pub fn run_reported(
        &mut self,
        declarations: &[Client],
        force_show_panics: bool,
    ) -> Result<Completion, Error> {
        // Finish transmission is outside the native method dispatcher too.
        // Contain its transport unwind before returning control to the owner.
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            self.check()?;
            self.budget.charge(Charge { work: 1, ..Charge::default() })?;
            let index = usize::try_from(self.declaration).map_err(|_| Error::Overflow)?;
            let client = declarations
                .get(index)
                .copied()
                .ok_or(Error::InvalidWire("native macro declaration index"))?;
            self.run_inner(client, force_show_panics)
        }))
        .unwrap_or(Err(Error::InvalidWire("native worker operation panicked")));
        match result {
            Ok(completion) => {
                self.close();
                Ok(completion)
            }
            Err(error) => Err(self.refuse(error)),
        }
    }

    fn run_inner(&mut self, client: Client, force_show_panics: bool) -> Result<Completion, Error> {
        self.check()?;
        let inputs = self.inputs.take().ok_or(Error::Phase)?;
        let input = Stream(Some(inputs[0]));
        let kind = self.kind;
        let server = Remote { worker: self };
        let output = if kind == 1 {
            client.run2(&SAME_THREAD, server, input, Stream(Some(inputs[1])), force_show_panics)
        } else {
            client.run1(&SAME_THREAD, server, input, force_show_panics)
        };
        // A macro may catch the native panic carrying a transport refusal.
        // That must never turn a poisoned invocation into a successful Finish.
        self.check()?;
        let output = match output {
            Ok(output) => output,
            Err(panic) => {
                let frame = encode(
                    &Envelope {
                        binding: self.binding.clone(),
                        message: Message::Failure { reason: panic_reason(panic.as_str()) },
                    },
                    &self.budget,
                )?;
                self.transport.send(&frame, &self.budget)?;
                self.budget.check()?;
                return Ok(Completion::Panicked);
            }
        };
        if let Some(handle) = output.0 {
            self.owned(handle)?;
        }
        let frame = encode(
            &Envelope {
                binding: self.binding.clone(),
                message: Message::Finish { output: output.0 },
            },
            &self.budget,
        )?;
        self.transport.send(&frame, &self.budget)?;
        self.budget.check()?;
        Ok(Completion::Finished)
    }

    fn check(&self) -> Result<(), Error> {
        if let Some(error) = &self.failure {
            return Err(error.clone());
        }
        if self.closed {
            return Err(Error::Phase);
        }
        self.budget.check()
    }
    fn close(&mut self) {
        if !self.closed {
            self.closed = true;
            self.slots.clear();
            self.transport.close();
        }
    }
    fn refuse(&mut self, error: Error) -> Error {
        let error = self.budget.refuse(error);
        self.failure.get_or_insert_with(|| error.clone());
        self.close();
        error
    }
    fn owned(&self, h: Handle) -> Result<(), Error> {
        if h.invocation != self.binding.invocation {
            return Err(Error::Identity);
        }
        match self.slots.get(h.slot as usize).copied().flatten() {
            Some(slot) if slot.live && slot.handle == h => Ok(()),
            _ => Err(Error::Handle("worker ownership")),
        }
    }
    fn call(&mut self, method: Method, arguments: Vec<Value>) -> Result<Value, Error> {
        let result = self.call_inner(method, arguments);
        result.map_err(|error| self.refuse(error))
    }
    fn call_inner(&mut self, method: Method, arguments: Vec<Value>) -> Result<Value, Error> {
        self.check()?;
        let id = self.next_id;
        let call = Call { id, method, arguments };
        call.validate()?;
        let uses = call.handle_uses(&self.budget)?;
        self.budget.charge(Charge {
            work: u64::try_from(uses.len().checked_mul(uses.len()).ok_or(Error::Overflow)?)
                .map_err(|_| Error::Overflow)?,
            ..Charge::default()
        })?;
        for (i, usage) in uses.iter().enumerate() {
            self.owned(usage.handle)?;
            for other in &uses[..i] {
                if usage.handle == other.handle
                    && (usage.mode == trust_process_isolation::UseMode::Consume
                        || other.mode == trust_process_isolation::UseMode::Consume)
                {
                    return Err(Error::Handle("duplicate worker consumption"));
                }
            }
        }
        self.next_id = id.checked_add(1).ok_or(Error::Sequence)?;
        let frame = encode(
            &Envelope { binding: self.binding.clone(), message: Message::Call(call) },
            &self.budget,
        )?;
        self.transport.send(&frame, &self.budget)?;
        let bytes = self.transport.receive(&self.budget)?;
        self.budget.check()?;
        let reply = decode(&bytes, &self.budget)?;
        if reply.binding != self.binding {
            return Err(Error::Identity);
        }
        let Message::Reply { id: reply_id, value } = reply.message else {
            return Err(Error::Phase);
        };
        if reply_id != id {
            return Err(Error::Sequence);
        }
        if !method.response().accepts(&value) {
            return Err(Error::Schema);
        }
        // Consume only after the entire call/reply has been admitted. Terminal
        // errors clear the local ledger and close the owned connection.
        for usage in uses {
            if usage.mode == trust_process_isolation::UseMode::Consume {
                self.slots[usage.handle.slot as usize]
                    .as_mut()
                    .ok_or(Error::Handle("worker slot"))?
                    .live = false;
            }
        }
        self.record_value(&value)?;
        Ok(value)
    }
    fn record_value(&mut self, value: &Value) -> Result<(), Error> {
        match value {
            Value::Stream(h) | Value::Span(h) => {
                record(&mut self.slots, self.slot_limit, &self.binding, *h)
            }
            Value::OptionalStream(h) | Value::OptionalSpan(h) => {
                if let Some(h) = h {
                    record(&mut self.slots, self.slot_limit, &self.binding, *h)?;
                }
                Ok(())
            }
            Value::Streams(values) => {
                for h in values {
                    record(&mut self.slots, self.slot_limit, &self.binding, *h)?;
                }
                Ok(())
            }
            Value::Tree(tree) => self.record_tree(tree),
            Value::Trees(trees) => {
                for tree in trees {
                    self.record_tree(tree)?;
                }
                Ok(())
            }
            Value::Literal(literal) => {
                record(&mut self.slots, self.slot_limit, &self.binding, literal.span)
            }
            Value::Result { value, .. } => self.record_value(value),
            _ => Ok(()),
        }
    }
    fn record_tree(&mut self, tree: &Tree) -> Result<(), Error> {
        match tree {
            Tree::Group { stream, spans, .. } => {
                if let Some(h) = stream {
                    record(&mut self.slots, self.slot_limit, &self.binding, *h)?;
                }
                for h in spans {
                    record(&mut self.slots, self.slot_limit, &self.binding, *h)?;
                }
                Ok(())
            }
            Tree::Punct { span, .. } | Tree::Ident { span, .. } => {
                record(&mut self.slots, self.slot_limit, &self.binding, *span)
            }
            Tree::Literal(literal) => {
                record(&mut self.slots, self.slot_limit, &self.binding, literal.span)
            }
        }
    }
}
impl<T: Transport> Drop for Worker<T> {
    fn drop(&mut self) {
        self.close();
    }
}

fn reserve<T>(budget: &Budget, count: usize) -> Result<(), Error> {
    let bytes = count.checked_mul(size_of::<T>()).ok_or(Error::Overflow)?;
    budget.charge(Charge {
        allocation_bytes: u64::try_from(bytes).map_err(|_| Error::Overflow)?,
        ..Charge::default()
    })
}
fn record(
    slots: &mut Vec<Option<Slot>>,
    limit: usize,
    binding: &Binding,
    h: Handle,
) -> Result<(), Error> {
    if h.invocation != binding.invocation || h.generation == 0 {
        return Err(Error::Identity);
    }
    let index = h.slot as usize;
    if index >= limit {
        return Err(Error::Handle("worker slot"));
    }
    if index >= slots.len() {
        // Within the capacity `from_begin` priced and reserved for `limit`.
        slots.resize(index + 1, None);
    }
    let slot = slots.get_mut(index).ok_or(Error::Handle("worker slot"))?;
    if let Some(previous) = slot {
        if previous.live && previous.handle == h && h.kind == HandleKind::Span {
            return Ok(());
        }
        if previous.live || h.generation <= previous.handle.generation {
            return Err(Error::Handle("worker replay"));
        }
    }
    *slot = Some(Slot { handle: h, live: true });
    Ok(())
}

struct Remote<'a, T: Transport> {
    worker: &'a mut Worker<T>,
}
impl<T: Transport> Remote<'_, T> {
    fn invoke<const N: usize>(&mut self, method: Method, args: [Value; N]) -> Result<Value, Error> {
        // The native ABI catches server panics. Latch an unexpected transport
        // unwind here, before macro code can catch it and return success.
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            reserve::<Value>(&self.worker.budget, N)?;
            self.worker.call(method, Vec::from(args))
        }));
        match result {
            Ok(result) => result.map_err(|e| self.worker.refuse(e)),
            Err(_) => Err(self.worker.refuse(Error::InvalidWire("native forwarding panicked"))),
        }
    }
    fn value<const N: usize>(&mut self, method: Method, args: [Value; N]) -> Value {
        self.invoke(method, args).unwrap_or_else(|error| std::panic::panic_any(error))
    }
    fn refuse(&mut self, error: Error) -> ! {
        std::panic::panic_any(self.worker.refuse(error))
    }
    fn stream(&mut self, stream: Stream) -> Handle {
        match stream.0 {
            Some(h) => h,
            None => match self.ts_from_str("") {
                Ok(Stream(Some(h))) => h,
                _ => self.refuse(Error::Schema),
            },
        }
    }
    fn text(&mut self, text: &str) -> String {
        reserve::<u8>(&self.worker.budget, text.len()).unwrap_or_else(|e| self.refuse(e));
        text.to_owned()
    }
    fn tree_to_wire(&mut self, tree: TokenTree<Stream, Handle, String>) -> Tree {
        match tree {
            TokenTree::Group(g) => Tree::Group {
                delimiter: delimiter(g.delimiter),
                stream: g.stream.map(|s| self.stream(s)),
                spans: [g.span.open, g.span.close, g.span.entire],
            },
            TokenTree::Punct(p) => Tree::Punct { ch: p.ch, joint: p.joint, span: p.span },
            TokenTree::Ident(i) => Tree::Ident {
                symbol: i.sym,
                is_raw: match i.kind {
                    IdentKind::Normal => false,
                    IdentKind::Raw => true,
                    IdentKind::ForcedKeyword => self.refuse(Error::InvalidWire("forced keyword")),
                },
                span: i.span,
            },
            TokenTree::Literal(l) => Tree::Literal(self.literal_to_wire(l)),
        }
    }
    fn literal_to_wire(&mut self, l: Literal<Handle, String>) -> trust_process_isolation::Literal {
        let (kind, raw_hashes) = match l.kind {
            LitKind::Byte => (0, 0),
            LitKind::Char => (1, 0),
            LitKind::Integer => (2, 0),
            LitKind::Float => (3, 0),
            LitKind::Str => (4, 0),
            LitKind::StrRaw(n) => (5, n),
            LitKind::ByteStr => (6, 0),
            LitKind::ByteStrRaw(n) => (7, n),
            LitKind::CStr => (8, 0),
            LitKind::CStrRaw(n) => (9, n),
            LitKind::ErrWithGuar => self.refuse(Error::InvalidWire("error-guaranteed literal")),
        };
        trust_process_isolation::Literal {
            kind,
            raw_hashes,
            symbol: l.symbol,
            suffix: l.suffix,
            span: l.span,
        }
    }
}
fn delimiter(d: Delimiter) -> u8 {
    match d {
        Delimiter::Parenthesis => 0,
        Delimiter::Brace => 1,
        Delimiter::Bracket => 2,
        Delimiter::None => 3,
    }
}
fn native_literal(l: trust_process_isolation::Literal) -> Literal<Handle, String> {
    Literal {
        kind: match l.kind {
            0 => LitKind::Byte,
            1 => LitKind::Char,
            2 => LitKind::Integer,
            3 => LitKind::Float,
            4 => LitKind::Str,
            5 => LitKind::StrRaw(l.raw_hashes),
            6 => LitKind::ByteStr,
            7 => LitKind::ByteStrRaw(l.raw_hashes),
            8 => LitKind::CStr,
            9 => LitKind::CStrRaw(l.raw_hashes),
            _ => unreachable!("B1 decoder checked literal"),
        },
        symbol: l.symbol,
        suffix: l.suffix,
        span: l.span,
    }
}
fn native_tree(t: Tree) -> TokenTree<Stream, Handle, String> {
    match t {
        Tree::Group { delimiter, stream, spans } => TokenTree::Group(Group {
            delimiter: match delimiter {
                0 => Delimiter::Parenthesis,
                1 => Delimiter::Brace,
                2 => Delimiter::Bracket,
                3 => Delimiter::None,
                _ => unreachable!("B1 decoder checked delimiter"),
            },
            stream: stream.map(|h| Stream(Some(h))),
            span: DelimSpan { open: spans[0], close: spans[1], entire: spans[2] },
        }),
        Tree::Punct { ch, joint, span } => TokenTree::Punct(Punct { ch, joint, span }),
        Tree::Ident { symbol, is_raw, span } => TokenTree::Ident(Ident {
            sym: symbol,
            kind: if is_raw { IdentKind::Raw } else { IdentKind::Normal },
            span,
        }),
        Tree::Literal(l) => TokenTree::Literal(native_literal(l)),
    }
}
fn wire_bound(b: Bound<usize>) -> trust_process_isolation::Bound {
    match b {
        Bound::Included(n) => trust_process_isolation::Bound::Included(n as u64),
        Bound::Excluded(n) => trust_process_isolation::Bound::Excluded(n as u64),
        Bound::Unbounded => trust_process_isolation::Bound::Unbounded,
    }
}

macro_rules! extract {
    ($self:ident, $value:expr, $pattern:pat => $result:expr) => {
        match $value {
            $pattern => $result,
            _ => $self.refuse(Error::Schema),
        }
    };
}
impl<T: Transport> Remote<'_, T> {
    fn number(&mut self, method: Method, span: Handle) -> usize {
        let n = extract!(self,self.value(method,[Value::Span(span)]),Value::U64(n)=>n);
        usize::try_from(n).unwrap_or_else(|_| self.refuse(Error::Overflow))
    }
    fn diagnostic(
        &mut self,
        d: Diagnostic<Handle>,
        depth: u16,
    ) -> trust_process_isolation::Diagnostic {
        self.worker.budget.depth(depth).unwrap_or_else(|e| self.refuse(e));
        reserve::<trust_process_isolation::Diagnostic>(&self.worker.budget, d.children.len())
            .unwrap_or_else(|e| self.refuse(e));
        trust_process_isolation::Diagnostic {
            level: match d.level {
                Level::Error => 0,
                Level::Warning => 1,
                Level::Note => 2,
                Level::Help => 3,
                _ => self.refuse(Error::InvalidWire("native diagnostic level")),
            },
            message: d.message,
            spans: d.spans,
            children: d.children.into_iter().map(|x| self.diagnostic(x, depth + 1)).collect(),
        }
    }
}
impl<T: Transport> Server for Remote<'_, T> {
    type TokenStream = Stream;
    type Span = Handle;
    type Symbol = String;
    fn globals(&mut self) -> ExpnGlobals<Handle> {
        let g = self.worker.globals;
        ExpnGlobals { def_site: g[0], call_site: g[1], mixed_site: g[2] }
    }
    fn intern_symbol(s: &str) -> String {
        s.to_owned()
    }
    fn with_symbol_string(s: &String, f: impl FnOnce(&str)) {
        f(s)
    }
    fn injected_env_var(&mut self, var: &str) -> Option<String> {
        let v = self.text(var);
        extract!(self,self.value(Method::InjectedEnvVar,[Value::Text(v)]),Value::OptionalText(x)=>x)
    }
    fn track_env_var(&mut self, var: &str, value: Option<&str>) {
        let var = self.text(var);
        let value = value.map(|x| self.text(x));
        extract!(self,self.value(Method::TrackEnvVar,[Value::Text(var),Value::OptionalText(value)]),Value::Unit=>())
    }
    fn track_path(&mut self, path: &str) {
        let p = self.text(path);
        extract!(self,self.value(Method::TrackPath,[Value::Text(p)]),Value::Unit=>())
    }
    fn literal_from_str(&mut self, s: &str) -> Result<Literal<Handle, String>, String> {
        let s = self.text(s);
        match self.value(Method::LiteralFromStr, [Value::Text(s)]) {
            Value::Result { ok: true, value } => {
                Ok(extract!(self,*value,Value::Literal(l)=>native_literal(*l)))
            }
            Value::Result { ok: false, value } => Err(extract!(self,*value,Value::Text(s)=>s)),
            _ => self.refuse(Error::Schema),
        }
    }
    fn emit_diagnostic(&mut self, d: Diagnostic<Handle>) {
        let d = self.diagnostic(d, 0);
        extract!(self,self.value(Method::EmitDiagnostic,[Value::Diagnostic(Box::new(d))]),Value::Unit=>())
    }
    fn ts_drop(&mut self, s: Stream) {
        // Drop may run during macro unwinding. The first transport failure
        // must latch/close as well, without starting a second unwind.
        if self.worker.failure.is_some()
            || self.worker.closed
            || self.worker.budget.check().is_err()
        {
            return;
        }
        if let Some(h) = s.0 {
            let result = self.invoke(Method::TsDrop, [Value::Stream(h)]);
            let error = match result {
                Ok(Value::Unit) => return,
                Ok(_) => self.worker.refuse(Error::Schema),
                Err(error) => error,
            };
            if !std::thread::panicking() {
                std::panic::panic_any(error);
            }
        }
    }
    fn ts_clone(&mut self, s: &Stream) -> Stream {
        let h = self.stream(s.clone());
        extract!(self,self.value(Method::TsClone,[Value::Stream(h)]),Value::Stream(x)=>Stream(Some(x)))
    }
    fn ts_is_empty(&mut self, s: &Stream) -> bool {
        let h = self.stream(s.clone());
        extract!(self,self.value(Method::TsIsEmpty,[Value::Stream(h)]),Value::Bool(x)=>x)
    }
    fn ts_expand_expr(&mut self, s: &Stream) -> Result<Stream, ()> {
        let h = self.stream(s.clone());
        match self.value(Method::TsExpandExpr, [Value::Stream(h)]) {
            Value::Result { ok: true, value } => {
                Ok(extract!(self,*value,Value::Stream(h)=>Stream(Some(h))))
            }
            Value::Result { ok: false, value } => extract!(self,*value,Value::Unit=>Err(())),
            _ => self.refuse(Error::Schema),
        }
    }
    fn ts_from_str(&mut self, s: &str) -> Result<Stream, String> {
        let s = self.text(s);
        match self.value(Method::TsFromStr, [Value::Text(s)]) {
            Value::Result { ok: true, value } => {
                Ok(extract!(self,*value,Value::Stream(h)=>Stream(Some(h))))
            }
            Value::Result { ok: false, value } => Err(extract!(self,*value,Value::Text(s)=>s)),
            _ => self.refuse(Error::Schema),
        }
    }
    fn ts_to_string(&mut self, s: &Stream) -> String {
        let h = self.stream(s.clone());
        extract!(self,self.value(Method::TsToString,[Value::Stream(h)]),Value::Text(x)=>x)
    }
    fn ts_from_token_tree(&mut self, t: TokenTree<Stream, Handle, String>) -> Stream {
        let t = self.tree_to_wire(t);
        extract!(self,self.value(Method::TsFromTokenTree,[Value::Tree(Box::new(t))]),Value::Stream(x)=>Stream(Some(x)))
    }
    fn ts_concat_trees(
        &mut self,
        base: Option<Stream>,
        trees: Vec<TokenTree<Stream, Handle, String>>,
    ) -> Stream {
        let base = base.map(|x| self.stream(x));
        reserve::<Tree>(&self.worker.budget, trees.len()).unwrap_or_else(|e| self.refuse(e));
        let trees = trees.into_iter().map(|t| self.tree_to_wire(t)).collect();
        extract!(self,self.value(Method::TsConcatTrees,[Value::OptionalStream(base),Value::Trees(trees)]),Value::Stream(x)=>Stream(Some(x)))
    }
    fn ts_concat_streams(&mut self, base: Option<Stream>, streams: Vec<Stream>) -> Stream {
        let base = base.map(|x| self.stream(x));
        reserve::<Handle>(&self.worker.budget, streams.len()).unwrap_or_else(|e| self.refuse(e));
        let streams = streams.into_iter().map(|s| self.stream(s)).collect();
        extract!(self,self.value(Method::TsConcatStreams,[Value::OptionalStream(base),Value::Streams(streams)]),Value::Stream(x)=>Stream(Some(x)))
    }
    fn ts_into_trees(&mut self, s: Stream) -> Vec<TokenTree<Stream, Handle, String>> {
        let h = self.stream(s);
        let trees =
            extract!(self,self.value(Method::TsIntoTrees,[Value::Stream(h)]),Value::Trees(x)=>x);
        reserve::<TokenTree<Stream, Handle, String>>(&self.worker.budget, trees.len())
            .unwrap_or_else(|e| self.refuse(e));
        trees.into_iter().map(native_tree).collect()
    }
    fn span_debug(&mut self, s: Handle) -> String {
        extract!(self,self.value(Method::SpanDebug,[Value::Span(s)]),Value::Text(x)=>x)
    }
    fn span_parent(&mut self, s: Handle) -> Option<Handle> {
        extract!(self,self.value(Method::SpanParent,[Value::Span(s)]),Value::OptionalSpan(x)=>x)
    }
    fn span_source(&mut self, s: Handle) -> Handle {
        extract!(self,self.value(Method::SpanSource,[Value::Span(s)]),Value::Span(x)=>x)
    }
    fn span_byte_range(&mut self, s: Handle) -> Range<usize> {
        let (start, end) = extract!(self,self.value(Method::SpanByteRange,[Value::Span(s)]),Value::Range{start,end}=>(start,end));
        usize::try_from(start).unwrap_or_else(|_| self.refuse(Error::Overflow))
            ..usize::try_from(end).unwrap_or_else(|_| self.refuse(Error::Overflow))
    }
    fn span_start(&mut self, s: Handle) -> Handle {
        extract!(self,self.value(Method::SpanStart,[Value::Span(s)]),Value::Span(x)=>x)
    }
    fn span_end(&mut self, s: Handle) -> Handle {
        extract!(self,self.value(Method::SpanEnd,[Value::Span(s)]),Value::Span(x)=>x)
    }
    fn span_line(&mut self, s: Handle) -> usize {
        self.number(Method::SpanLine, s)
    }
    fn span_column(&mut self, s: Handle) -> usize {
        self.number(Method::SpanColumn, s)
    }
    fn span_file(&mut self, s: Handle) -> String {
        extract!(self,self.value(Method::SpanFile,[Value::Span(s)]),Value::Text(x)=>x)
    }
    fn span_local_file(&mut self, s: Handle) -> Option<String> {
        extract!(self,self.value(Method::SpanLocalFile,[Value::Span(s)]),Value::OptionalText(x)=>x)
    }
    fn span_join(&mut self, s: Handle, o: Handle) -> Option<Handle> {
        extract!(self,self.value(Method::SpanJoin,[Value::Span(s),Value::Span(o)]),Value::OptionalSpan(x)=>x)
    }
    fn span_subspan(
        &mut self,
        s: Handle,
        start: Bound<usize>,
        end: Bound<usize>,
    ) -> Option<Handle> {
        extract!(self,self.value(Method::SpanSubspan,[Value::Span(s),Value::Bound(wire_bound(start)),Value::Bound(wire_bound(end))]),Value::OptionalSpan(x)=>x)
    }
    fn span_resolved_at(&mut self, s: Handle, at: Handle) -> Handle {
        extract!(self,self.value(Method::SpanResolvedAt,[Value::Span(s),Value::Span(at)]),Value::Span(x)=>x)
    }
    fn span_source_text(&mut self, s: Handle) -> Option<String> {
        extract!(self,self.value(Method::SpanSourceText,[Value::Span(s)]),Value::OptionalText(x)=>x)
    }
    fn span_save_span(&mut self, s: Handle) -> usize {
        self.number(Method::SpanSaveSpan, s)
    }
    fn span_recover_proc_macro_span(&mut self, id: usize) -> Handle {
        extract!(self,self.value(Method::SpanRecoverProcMacroSpan,[Value::U64(id as u64)]),Value::Span(x)=>x)
    }
    fn symbol_normalize_and_validate_ident(&mut self, s: &str) -> Result<String, ()> {
        let s = self.text(s);
        match self.value(Method::SymbolNormalizeAndValidateIdent, [Value::Text(s)]) {
            Value::Result { ok: true, value } => Ok(extract!(self,*value,Value::Text(s)=>s)),
            Value::Result { ok: false, value } => extract!(self,*value,Value::Unit=>Err(())),
            _ => self.refuse(Error::Schema),
        }
    }
}

/// Bounded I/O on an already-owned socket; no launch or peer authentication.
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub mod unix;
