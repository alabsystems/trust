use crate::{Budget, Charge, Error, Handle, HandleKind, HandleUse, UseMode};

pub const PROTOCOL_VERSION: u32 = 1;

/// Expected digests come from the owner, never a worker attestation. The host
/// ABI digest binds the compiler-owned host triple and native bridge schema.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Binding {
    pub version: u32,
    pub invocation: u64,
    pub compiler: [u8; 32],
    pub worker: [u8; 32],
    pub artifact: [u8; 32],
    pub metadata: [u8; 32],
    pub unit: [u8; 32],
    pub input_closure: [u8; 32],
    pub host_abi: [u8; 32],
}

impl Binding {
    pub fn validate(&self) -> Result<(), Error> {
        if self.version != PROTOCOL_VERSION
            || self.invocation == 0
            || [
                &self.compiler,
                &self.worker,
                &self.artifact,
                &self.metadata,
                &self.unit,
                &self.input_closure,
                &self.host_abi,
            ]
            .iter()
            .any(|d| **d == [0; 32])
        {
            Err(Error::Identity)
        } else {
            Ok(())
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Envelope {
    pub binding: Binding,
    pub message: Message,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Message {
    Begin { declaration: u32, kind: u8, inputs: Vec<Handle>, globals: [Handle; 3] },
    Ready,
    Call(Call),
    Reply { id: u64, value: Value },
    Finish { output: Option<Handle> },
    Failure { reason: String },
    Cancel,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Call {
    pub id: u64,
    pub method: Method,
    pub arguments: Vec<Value>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Bound {
    Included(u64),
    Excluded(u64),
    Unbounded,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Literal {
    /// 0..=9 correspond to the bridge's non-error literal kinds. No ErrWithGuar.
    pub kind: u8,
    pub raw_hashes: u8,
    pub symbol: String,
    pub suffix: Option<String>,
    pub span: Handle,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Tree {
    Group { delimiter: u8, stream: Option<Handle>, spans: [Handle; 3] },
    Punct { ch: u8, joint: bool, span: Handle },
    Ident { symbol: String, is_raw: bool, span: Handle },
    Literal(Literal),
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic {
    pub level: u8,
    pub message: String,
    pub spans: Vec<Handle>,
    pub children: Vec<Diagnostic>,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value {
    Unit,
    Bool(bool),
    U64(u64),
    Text(String),
    OptionalText(Option<String>),
    Stream(Handle),
    Span(Handle),
    OptionalStream(Option<Handle>),
    OptionalSpan(Option<Handle>),
    Tree(Box<Tree>),
    Trees(Vec<Tree>),
    Streams(Vec<Handle>),
    Bound(Bound),
    Range { start: u64, end: u64 },
    Literal(Box<Literal>),
    Diagnostic(Box<Diagnostic>),
    Result { ok: bool, value: Box<Value> },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Type {
    Unit,
    Bool,
    U64,
    Text,
    OptionalText,
    Stream,
    Span,
    OptionalStream,
    OptionalSpan,
    Tree,
    Trees,
    Streams,
    Bound,
    Range,
    Literal,
    Diagnostic,
    LiteralOrText,
    StreamOrUnit,
    StreamOrText,
    TextOrUnit,
}

impl Type {
    pub fn accepts(self, value: &Value) -> bool {
        use Type as T;
        use Value as V;
        match (self, value) {
            (T::Unit, V::Unit)
            | (T::Bool, V::Bool(_))
            | (T::U64, V::U64(_))
            | (T::Text, V::Text(_))
            | (T::OptionalText, V::OptionalText(_))
            | (T::Tree, V::Tree(_))
            | (T::Trees, V::Trees(_))
            | (T::Streams, V::Streams(_))
            | (T::Bound, V::Bound(_))
            | (T::Range, V::Range { .. })
            | (T::Literal, V::Literal(_))
            | (T::Diagnostic, V::Diagnostic(_)) => true,
            (T::Stream, V::Stream(h)) => h.kind == HandleKind::Stream,
            (T::Span, V::Span(h)) => h.kind == HandleKind::Span,
            (T::OptionalStream, V::OptionalStream(h)) => {
                h.is_none_or(|h| h.kind == HandleKind::Stream)
            }
            (T::OptionalSpan, V::OptionalSpan(h)) => h.is_none_or(|h| h.kind == HandleKind::Span),
            (T::LiteralOrText, V::Result { ok, value }) => {
                if *ok {
                    T::Literal.accepts(value)
                } else {
                    T::Text.accepts(value)
                }
            }
            (T::StreamOrUnit, V::Result { ok, value }) => {
                if *ok {
                    T::Stream.accepts(value)
                } else {
                    T::Unit.accepts(value)
                }
            }
            (T::StreamOrText, V::Result { ok, value }) => {
                if *ok {
                    T::Stream.accepts(value)
                } else {
                    T::Text.accepts(value)
                }
            }
            (T::TextOrUnit, V::Result { ok, value }) => {
                if *ok {
                    T::Text.accepts(value)
                } else {
                    T::Unit.accepts(value)
                }
            }
            _ => false,
        }
    }
}

/// Versioned schema matching all 32 methods of bridge::with_api at base 698.
/// Names are frozen ABI identifiers, not Rust enum discriminant assumptions.
macro_rules! methods {
    ($( $variant:ident = $tag:literal, $name:literal, [$($arg:ident),*], $ret:ident, [$($consume:literal),*]; )*) => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        #[repr(u8)]
        pub enum Method { $( $variant = $tag, )* }
        impl Method {
            pub const ALL: &'static [Self] = &[$( Self::$variant, )*];
            pub fn tag(self) -> u8 { self as u8 }
            pub fn from_tag(tag: u8) -> Result<Self, Error> { match tag { $( $tag => Ok(Self::$variant), )* _ => Err(Error::InvalidWire("method")) } }
            pub fn name(self) -> &'static str { match self { $( Self::$variant => $name, )* } }
            pub fn arguments(self) -> &'static [Type] { match self { $( Self::$variant => &[$(Type::$arg),*], )* } }
            pub fn response(self) -> Type { match self { $( Self::$variant => Type::$ret, )* } }
            pub fn consumes(self, index: usize) -> bool { match self { $( Self::$variant => [$( $consume ),*].contains(&index), )* } }
        }
    }
}
methods! {
    InjectedEnvVar=1,"injected_env_var",[Text],OptionalText,[];
    TrackEnvVar=2,"track_env_var",[Text,OptionalText],Unit,[];
    TrackPath=3,"track_path",[Text],Unit,[];
    LiteralFromStr=4,"literal_from_str",[Text],LiteralOrText,[];
    EmitDiagnostic=5,"emit_diagnostic",[Diagnostic],Unit,[];
    TsDrop=6,"ts_drop",[Stream],Unit,[0];
    TsClone=7,"ts_clone",[Stream],Stream,[];
    TsIsEmpty=8,"ts_is_empty",[Stream],Bool,[];
    TsExpandExpr=9,"ts_expand_expr",[Stream],StreamOrUnit,[];
    TsFromStr=10,"ts_from_str",[Text],StreamOrText,[];
    TsToString=11,"ts_to_string",[Stream],Text,[];
    TsFromTokenTree=12,"ts_from_token_tree",[Tree],Stream,[0];
    TsConcatTrees=13,"ts_concat_trees",[OptionalStream,Trees],Stream,[0,1];
    TsConcatStreams=14,"ts_concat_streams",[OptionalStream,Streams],Stream,[0,1];
    TsIntoTrees=15,"ts_into_trees",[Stream],Trees,[0];
    SpanDebug=16,"span_debug",[Span],Text,[];
    SpanParent=17,"span_parent",[Span],OptionalSpan,[];
    SpanSource=18,"span_source",[Span],Span,[];
    SpanByteRange=19,"span_byte_range",[Span],Range,[];
    SpanStart=20,"span_start",[Span],Span,[];
    SpanEnd=21,"span_end",[Span],Span,[];
    SpanLine=22,"span_line",[Span],U64,[];
    SpanColumn=23,"span_column",[Span],U64,[];
    SpanFile=24,"span_file",[Span],Text,[];
    SpanLocalFile=25,"span_local_file",[Span],OptionalText,[];
    SpanJoin=26,"span_join",[Span,Span],OptionalSpan,[];
    SpanSubspan=27,"span_subspan",[Span,Bound,Bound],OptionalSpan,[];
    SpanResolvedAt=28,"span_resolved_at",[Span,Span],Span,[];
    SpanSourceText=29,"span_source_text",[Span],OptionalText,[];
    SpanSaveSpan=30,"span_save_span",[Span],U64,[];
    SpanRecoverProcMacroSpan=31,"span_recover_proc_macro_span",[U64],Span,[];
    SymbolNormalizeAndValidateIdent=32,"symbol_normalize_and_validate_ident",[Text],TextOrUnit,[];
}

impl Call {
    pub fn validate(&self) -> Result<(), Error> {
        if self.id == 0
            || self.arguments.len() != self.method.arguments().len()
            || !self.arguments.iter().zip(self.method.arguments()).all(|(v, t)| t.accepts(v))
        {
            return Err(Error::Schema);
        }
        Ok(())
    }

    /// Produces the complete ownership transaction for a separately owned table.
    pub fn handle_uses(&self, budget: &Budget) -> Result<Vec<HandleUse>, Error> {
        self.validate()?;
        let mut output = Vec::new();
        for (index, value) in self.arguments.iter().enumerate() {
            collect(value, self.method.consumes(index), &mut output, budget, 0)?;
        }
        budget.check()?;
        Ok(output)
    }
}

fn add(
    handle: Handle,
    expected: HandleKind,
    consume: bool,
    output: &mut Vec<HandleUse>,
    budget: &Budget,
) -> Result<(), Error> {
    if handle.kind != expected || handle.invocation == 0 || handle.generation == 0 {
        return Err(Error::Handle("typed identity"));
    }
    // Full replacement storage can coexist with the old owner during growth.
    // The argument vector is bounded, but it still needs honest growth pricing.
    if output.len() == output.capacity() {
        let capacity =
            output.capacity().checked_mul(2).ok_or_else(|| budget.refuse(Error::Overflow))?.max(1);
        budget.allocation::<HandleUse>(capacity)?;
        budget.charge(Charge {
            work: u64::try_from(output.capacity()).map_err(|_| budget.refuse(Error::Overflow))?,
            ..Charge::default()
        })?;
        output
            .try_reserve_exact(capacity - output.len())
            .map_err(|_| budget.refuse(Error::Allocation))?;
        budget.allocation::<HandleUse>(output.capacity().saturating_sub(capacity))?;
    }
    output.push(HandleUse {
        handle,
        mode: if consume && handle.kind == HandleKind::Stream {
            UseMode::Consume
        } else {
            UseMode::Borrow
        },
    });
    Ok(())
}
fn tree(t: &Tree, consume: bool, out: &mut Vec<HandleUse>, b: &Budget) -> Result<(), Error> {
    match t {
        Tree::Group { delimiter, stream, spans } => {
            if *delimiter > 3 {
                return Err(Error::InvalidWire("delimiter"));
            }
            if let Some(s) = stream {
                add(*s, HandleKind::Stream, consume, out, b)?;
            }
            for s in spans {
                add(*s, HandleKind::Span, false, out, b)?;
            }
        }
        Tree::Punct { span, .. } | Tree::Ident { span, .. } => {
            add(*span, HandleKind::Span, false, out, b)?
        }
        Tree::Literal(l) => {
            if l.kind > 9 {
                return Err(Error::InvalidWire("literal kind"));
            }
            add(l.span, HandleKind::Span, false, out, b)?;
        }
    }
    Ok(())
}
fn diagnostic(
    d: &Diagnostic,
    out: &mut Vec<HandleUse>,
    b: &Budget,
    depth: u16,
) -> Result<(), Error> {
    b.depth(depth)?;
    b.charge(Charge { work: 1, ..Charge::default() })?;
    if d.level > 3 {
        return Err(Error::InvalidWire("diagnostic level"));
    }
    for span in &d.spans {
        add(*span, HandleKind::Span, false, out, b)?;
    }
    for child in &d.children {
        diagnostic(child, out, b, depth.checked_add(1).ok_or(Error::Overflow)?)?;
    }
    Ok(())
}
fn collect(
    v: &Value,
    consume: bool,
    out: &mut Vec<HandleUse>,
    b: &Budget,
    depth: u16,
) -> Result<(), Error> {
    b.depth(depth)?;
    b.charge(Charge { work: 1, ..Charge::default() })?;
    match v {
        Value::Stream(h) => add(*h, HandleKind::Stream, consume, out, b)?,
        Value::Span(h) => add(*h, HandleKind::Span, false, out, b)?,
        Value::OptionalStream(h) => {
            if let Some(h) = h {
                add(*h, HandleKind::Stream, consume, out, b)?;
            }
        }
        Value::OptionalSpan(h) => {
            if let Some(h) = h {
                add(*h, HandleKind::Span, false, out, b)?;
            }
        }
        Value::Streams(hs) => {
            for h in hs {
                add(*h, HandleKind::Stream, consume, out, b)?;
            }
        }
        Value::Tree(t) => tree(t, consume, out, b)?,
        Value::Trees(ts) => {
            for t in ts {
                tree(t, consume, out, b)?;
            }
        }
        Value::Literal(l) => add(l.span, HandleKind::Span, false, out, b)?,
        Value::Diagnostic(d) => diagnostic(d, out, b, depth)?,
        Value::Result { value, .. } => {
            collect(value, consume, out, b, depth.checked_add(1).ok_or(Error::Overflow)?)?
        }
        _ => {}
    }
    Ok(())
}
