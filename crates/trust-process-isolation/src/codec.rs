use crate::protocol::{Bound, Diagnostic, Literal, Tree};
use crate::{
    Binding, Budget, Call, Charge, Envelope, Error, Handle, HandleKind, Message, Method, Value,
};

/// Validate the existing B1 length prefix before allocating or reading payload.
/// This does not consume traffic or grant work; transport/decoder callers debit
/// the bytes they actually handle on their original Budget.
pub fn frame_payload_length(prefix: [u8; 4], budget: &Budget) -> Result<usize, Error> {
    budget.check()?;
    let length = u32::from_le_bytes(prefix);
    if length == 0 || length > budget.limits().frame_bytes {
        return Err(budget.refuse(Error::Budget("frame bytes")));
    }
    usize::try_from(length).map_err(|_| budget.refuse(Error::Overflow))
}

/// One length-prefixed frame, fed by a deadline-aware nonblocking transport.
/// Bytes following a complete frame are rejected, not silently discarded.
#[derive(Debug)]
pub struct FrameDecoder {
    prefix: [u8; 4],
    prefix_len: usize,
    payload: Vec<u8>,
    length: Option<usize>,
    complete: bool,
    budget: Budget,
}
impl FrameDecoder {
    pub fn new(budget: Budget) -> Self {
        Self {
            prefix: [0; 4],
            prefix_len: 0,
            payload: Vec::new(),
            length: None,
            complete: false,
            budget,
        }
    }
    pub fn needed(&self) -> usize {
        if self.complete {
            0
        } else if let Some(n) = self.length {
            n - self.payload.len()
        } else {
            4 - self.prefix_len
        }
    }
    pub fn push(&mut self, input: &[u8]) -> Result<Option<Envelope>, Error> {
        let result = self.push_inner(input);
        if result.is_err() {
            if let Err(error) = &result {
                self.budget.refuse(error.clone());
            }
            self.complete = true;
            self.payload.clear();
        }
        result
    }
    fn push_inner(&mut self, mut input: &[u8]) -> Result<Option<Envelope>, Error> {
        self.budget.check()?;
        if self.complete {
            return Err(Error::Phase);
        }
        self.budget.charge(Charge {
            wire_bytes: u64::try_from(input.len()).map_err(|_| Error::Overflow)?,
            work: u64::try_from(input.len()).map_err(|_| Error::Overflow)?,
            ..Charge::default()
        })?;
        if self.prefix_len < 4 {
            let n = input.len().min(4 - self.prefix_len);
            self.prefix[self.prefix_len..self.prefix_len + n].copy_from_slice(&input[..n]);
            self.prefix_len += n;
            input = &input[n..];
            if self.prefix_len < 4 {
                return Ok(None);
            }
            let n = frame_payload_length(self.prefix, &self.budget)?;
            self.budget.allocation::<u8>(n)?;
            self.payload.try_reserve_exact(n).map_err(|_| Error::Allocation)?;
            self.budget.allocation::<u8>(self.payload.capacity().saturating_sub(n))?;
            self.budget.check()?;
            self.length = Some(n);
        }
        let n = self.length.ok_or(Error::InvalidWire("frame length"))?;
        if input.len() > n - self.payload.len() {
            return Err(Error::InvalidWire("trailing frame data"));
        }
        self.payload.extend_from_slice(input);
        self.budget.check()?;
        if self.payload.len() != n {
            return Ok(None);
        }
        self.complete = true;
        decode_payload(&self.payload, &self.budget).map(Some)
    }
}

pub fn decode(frame: &[u8], budget: &Budget) -> Result<Envelope, Error> {
    FrameDecoder::new(budget.clone())
        .push(frame)?
        .ok_or_else(|| budget.refuse(Error::InvalidWire("truncated frame")))
}

struct Reader<'a> {
    bytes: &'a [u8],
    budget: &'a Budget,
}
impl Reader<'_> {
    fn take(&mut self, n: usize) -> Result<&[u8], Error> {
        self.budget.charge(Charge { work: 1, ..Charge::default() })?;
        if n > self.bytes.len() {
            return Err(Error::InvalidWire("truncated payload"));
        }
        let (head, tail) = self.bytes.split_at(n);
        self.bytes = tail;
        Ok(head)
    }
    fn u8(&mut self) -> Result<u8, Error> {
        Ok(self.take(1)?[0])
    }
    fn bool(&mut self) -> Result<bool, Error> {
        match self.u8()? {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err(Error::InvalidWire("boolean")),
        }
    }
    fn u32(&mut self) -> Result<u32, Error> {
        Ok(u32::from_le_bytes(self.take(4)?.try_into().map_err(|_| Error::InvalidWire("u32"))?))
    }
    fn u64(&mut self) -> Result<u64, Error> {
        Ok(u64::from_le_bytes(self.take(8)?.try_into().map_err(|_| Error::InvalidWire("u64"))?))
    }
    fn digest(&mut self) -> Result<[u8; 32], Error> {
        self.take(32)?.try_into().map_err(|_| Error::Identity)
    }
    fn count(&mut self) -> Result<usize, Error> {
        let n = usize::try_from(self.u32()?).map_err(|_| Error::Overflow)?;
        if n > self.bytes.len() {
            return Err(Error::InvalidWire("impossible count"));
        }
        Ok(n)
    }
    fn string(&mut self) -> Result<String, Error> {
        let n = self.count()?;
        self.budget.charge(Charge {
            work: u64::try_from(n)
                .map_err(|_| Error::Overflow)?
                .checked_mul(2)
                .ok_or(Error::Overflow)?,
            ..Charge::default()
        })?;
        self.budget.allocation::<u8>(n)?;
        let mut result = String::new();
        result.try_reserve_exact(n).map_err(|_| Error::Allocation)?;
        self.budget.allocation::<u8>(result.capacity().saturating_sub(n))?;
        let text = std::str::from_utf8(self.take(n)?).map_err(|_| Error::InvalidWire("UTF-8"))?;
        result.push_str(text);
        self.budget.check()?;
        Ok(result)
    }
    fn opt_string(&mut self) -> Result<Option<String>, Error> {
        if self.bool()? { Ok(Some(self.string()?)) } else { Ok(None) }
    }
    fn handle(&mut self, expected: Option<HandleKind>) -> Result<Handle, Error> {
        let invocation = self.u64()?;
        let kind = match self.u8()? {
            1 => HandleKind::Stream,
            2 => HandleKind::Span,
            _ => return Err(Error::InvalidWire("handle kind")),
        };
        let slot = self.u32()?;
        let generation = self.u32()?;
        if invocation == 0 || generation == 0 || expected.is_some_and(|k| k != kind) {
            return Err(Error::Handle("wire identity"));
        }
        Ok(Handle { invocation, kind, slot, generation })
    }
    fn opt_handle(&mut self, kind: HandleKind) -> Result<Option<Handle>, Error> {
        if self.bool()? { Ok(Some(self.handle(Some(kind))?)) } else { Ok(None) }
    }
    fn vec<T>(
        &mut self,
        mut f: impl FnMut(&mut Self) -> Result<T, Error>,
    ) -> Result<Vec<T>, Error> {
        let count = self.count()?;
        self.budget.allocation::<T>(count)?;
        let mut result = Vec::new();
        result.try_reserve_exact(count).map_err(|_| Error::Allocation)?;
        self.budget.allocation::<T>(result.capacity().saturating_sub(count))?;
        self.budget.check()?;
        for _ in 0..count {
            result.push(f(self)?);
        }
        Ok(result)
    }
    fn boxed<T>(&mut self, value: T) -> Result<Box<T>, Error> {
        self.budget.allocation::<T>(1)?;
        Ok(Box::new(value))
    }
    fn literal(&mut self) -> Result<Literal, Error> {
        let kind = self.u8()?;
        let raw_hashes = self.u8()?;
        if kind > 9 || (![5, 7, 9].contains(&kind) && raw_hashes != 0) {
            return Err(Error::InvalidWire("literal kind"));
        }
        Ok(Literal {
            kind,
            raw_hashes,
            symbol: self.string()?,
            suffix: self.opt_string()?,
            span: self.handle(Some(HandleKind::Span))?,
        })
    }
    fn tree(&mut self) -> Result<Tree, Error> {
        self.budget.charge(Charge { values: 1, ..Charge::default() })?;
        match self.u8()? {
            0 => {
                let delimiter = self.u8()?;
                if delimiter > 3 {
                    return Err(Error::InvalidWire("delimiter"));
                }
                Ok(Tree::Group {
                    delimiter,
                    stream: self.opt_handle(HandleKind::Stream)?,
                    spans: [
                        self.handle(Some(HandleKind::Span))?,
                        self.handle(Some(HandleKind::Span))?,
                        self.handle(Some(HandleKind::Span))?,
                    ],
                })
            }
            1 => Ok(Tree::Punct {
                ch: self.u8()?,
                joint: self.bool()?,
                span: self.handle(Some(HandleKind::Span))?,
            }),
            2 => Ok(Tree::Ident {
                symbol: self.string()?,
                is_raw: self.bool()?,
                span: self.handle(Some(HandleKind::Span))?,
            }),
            3 => Ok(Tree::Literal(self.literal()?)),
            _ => Err(Error::InvalidWire("tree tag")),
        }
    }
    fn diagnostic(&mut self, depth: u16) -> Result<Diagnostic, Error> {
        self.budget.depth(depth)?;
        self.budget.charge(Charge { values: 1, ..Charge::default() })?;
        let level = self.u8()?;
        if level > 3 {
            return Err(Error::InvalidWire("diagnostic level"));
        }
        Ok(Diagnostic {
            level,
            message: self.string()?,
            spans: self.vec(|r| r.handle(Some(HandleKind::Span)))?,
            children: self.vec(|r| r.diagnostic(depth.checked_add(1).ok_or(Error::Overflow)?))?,
        })
    }
    fn value(&mut self, depth: u16) -> Result<Value, Error> {
        self.budget.depth(depth)?;
        self.budget.charge(Charge { values: 1, ..Charge::default() })?;
        Ok(match self.u8()? {
            0 => Value::Unit,
            1 => Value::Bool(self.bool()?),
            2 => Value::U64(self.u64()?),
            3 => Value::Text(self.string()?),
            4 => Value::OptionalText(self.opt_string()?),
            5 => Value::Stream(self.handle(Some(HandleKind::Stream))?),
            6 => Value::Span(self.handle(Some(HandleKind::Span))?),
            7 => Value::OptionalStream(self.opt_handle(HandleKind::Stream)?),
            8 => Value::OptionalSpan(self.opt_handle(HandleKind::Span)?),
            9 => {
                let v = self.tree()?;
                Value::Tree(self.boxed(v)?)
            }
            10 => Value::Trees(self.vec(|r| r.tree())?),
            11 => Value::Streams(self.vec(|r| r.handle(Some(HandleKind::Stream)))?),
            12 => Value::Bound(match self.u8()? {
                0 => Bound::Included(self.u64()?),
                1 => Bound::Excluded(self.u64()?),
                2 => Bound::Unbounded,
                _ => return Err(Error::InvalidWire("bound")),
            }),
            13 => {
                let start = self.u64()?;
                let end = self.u64()?;
                if start > end {
                    return Err(Error::InvalidWire("range"));
                }
                Value::Range { start, end }
            }
            14 => {
                let v = self.literal()?;
                Value::Literal(self.boxed(v)?)
            }
            15 => {
                let v = self.diagnostic(depth)?;
                Value::Diagnostic(self.boxed(v)?)
            }
            16 => {
                let ok = self.bool()?;
                let v = self.value(depth.checked_add(1).ok_or(Error::Overflow)?)?;
                Value::Result { ok, value: self.boxed(v)? }
            }
            _ => return Err(Error::InvalidWire("value tag")),
        })
    }
}

fn decode_payload(bytes: &[u8], budget: &Budget) -> Result<Envelope, Error> {
    let mut r = Reader { bytes, budget };
    if r.take(4)? != b"TMP1" {
        return Err(Error::InvalidWire("magic"));
    }
    let binding = Binding {
        version: r.u32()?,
        invocation: r.u64()?,
        compiler: r.digest()?,
        worker: r.digest()?,
        artifact: r.digest()?,
        metadata: r.digest()?,
        unit: r.digest()?,
        input_closure: r.digest()?,
        host_abi: r.digest()?,
    };
    binding.validate()?;
    let message = match r.u8()? {
        0 => {
            let declaration = r.u32()?;
            let kind = r.u8()?;
            let inputs = r.vec(|r| r.handle(Some(HandleKind::Stream)))?;
            if kind > 2 || inputs.len() != if kind == 1 { 2 } else { 1 } {
                return Err(Error::Schema);
            }
            Message::Begin {
                declaration,
                kind,
                inputs,
                globals: [
                    r.handle(Some(HandleKind::Span))?,
                    r.handle(Some(HandleKind::Span))?,
                    r.handle(Some(HandleKind::Span))?,
                ],
            }
        }
        1 => Message::Ready,
        2 => {
            let call = Call {
                id: r.u64()?,
                method: Method::from_tag(r.u8()?)?,
                arguments: r.vec(|r| r.value(0))?,
            };
            call.validate()?;
            Message::Call(call)
        }
        3 => Message::Reply { id: r.u64()?, value: r.value(0)? },
        4 => Message::Finish { output: r.opt_handle(HandleKind::Stream)? },
        5 => Message::Failure { reason: r.string()? },
        6 => Message::Cancel,
        _ => return Err(Error::InvalidWire("message tag")),
    };
    if !r.bytes.is_empty() {
        return Err(Error::InvalidWire("trailing payload"));
    }
    budget.check()?;
    Ok(Envelope { binding, message })
}

struct Writer<'a> {
    bytes: Vec<u8>,
    budget: &'a Budget,
}
impl Writer<'_> {
    fn put(&mut self, bytes: &[u8]) -> Result<(), Error> {
        self.budget.check()?;
        let n = self.bytes.len().checked_add(bytes.len()).ok_or(Error::Overflow)?;
        let max = usize::try_from(self.budget.limits().frame_bytes)
            .map_err(|_| Error::Overflow)?
            .checked_add(4)
            .ok_or(Error::Overflow)?;
        if n > max {
            return Err(Error::Budget("frame bytes"));
        }
        let mut copy_work = bytes.len();
        if n > self.bytes.capacity() {
            let capacity = self
                .bytes
                .capacity()
                .checked_mul(2)
                .ok_or(Error::Overflow)?
                .max(16)
                .min(max)
                .max(n);
            // Old and new allocations may coexist during realloc. Price the
            // complete replacement, not just its delta, and the old capacity's
            // possible copy; the allocator's interval is opaque to this crate.
            copy_work = copy_work.checked_add(self.bytes.capacity()).ok_or(Error::Overflow)?;
            self.budget.charge(Charge {
                allocation_bytes: u64::try_from(capacity).map_err(|_| Error::Overflow)?,
                work: u64::try_from(copy_work).map_err(|_| Error::Overflow)?,
                ..Charge::default()
            })?;
            self.bytes
                .try_reserve_exact(capacity - self.bytes.len())
                .map_err(|_| Error::Allocation)?;
            self.budget.allocation::<u8>(self.bytes.capacity().saturating_sub(capacity))?;
        } else {
            self.budget.charge(Charge {
                work: u64::try_from(copy_work).map_err(|_| Error::Overflow)?,
                ..Charge::default()
            })?;
        }
        self.budget.check()?;
        self.bytes.extend_from_slice(bytes);
        self.budget.check()?;
        Ok(())
    }
    fn u8(&mut self, n: u8) -> Result<(), Error> {
        self.put(&[n])
    }
    fn bool(&mut self, b: bool) -> Result<(), Error> {
        self.u8(u8::from(b))
    }
    fn u32(&mut self, n: u32) -> Result<(), Error> {
        self.put(&n.to_le_bytes())
    }
    fn u64(&mut self, n: u64) -> Result<(), Error> {
        self.put(&n.to_le_bytes())
    }
    fn string(&mut self, s: &str) -> Result<(), Error> {
        self.u32(u32::try_from(s.len()).map_err(|_| Error::Overflow)?)?;
        self.put(s.as_bytes())
    }
    fn opt_string(&mut self, s: &Option<String>) -> Result<(), Error> {
        self.bool(s.is_some())?;
        if let Some(s) = s {
            self.string(s)?;
        }
        Ok(())
    }
    fn handle(&mut self, h: Handle, kind: HandleKind) -> Result<(), Error> {
        if h.kind != kind || h.invocation == 0 || h.generation == 0 {
            return Err(Error::Handle("wire identity"));
        }
        self.u64(h.invocation)?;
        self.u8(h.kind as u8)?;
        self.u32(h.slot)?;
        self.u32(h.generation)
    }
    fn opt_handle(&mut self, h: Option<Handle>, kind: HandleKind) -> Result<(), Error> {
        self.bool(h.is_some())?;
        if let Some(h) = h {
            self.handle(h, kind)?;
        }
        Ok(())
    }
    fn vec<T>(
        &mut self,
        vs: &[T],
        mut f: impl FnMut(&mut Self, &T) -> Result<(), Error>,
    ) -> Result<(), Error> {
        self.u32(u32::try_from(vs.len()).map_err(|_| Error::Overflow)?)?;
        for v in vs {
            f(self, v)?;
        }
        Ok(())
    }
    fn literal(&mut self, l: &Literal) -> Result<(), Error> {
        if l.kind > 9 || (![5, 7, 9].contains(&l.kind) && l.raw_hashes != 0) {
            return Err(Error::InvalidWire("literal kind"));
        }
        self.u8(l.kind)?;
        self.u8(l.raw_hashes)?;
        self.string(&l.symbol)?;
        self.opt_string(&l.suffix)?;
        self.handle(l.span, HandleKind::Span)
    }
    fn tree(&mut self, t: &Tree) -> Result<(), Error> {
        self.budget.charge(Charge { values: 1, ..Charge::default() })?;
        match t {
            Tree::Group { delimiter, stream, spans } => {
                if *delimiter > 3 {
                    return Err(Error::InvalidWire("delimiter"));
                }
                self.u8(0)?;
                self.u8(*delimiter)?;
                self.opt_handle(*stream, HandleKind::Stream)?;
                for h in spans {
                    self.handle(*h, HandleKind::Span)?;
                }
                Ok(())
            }
            Tree::Punct { ch, joint, span } => {
                self.u8(1)?;
                self.u8(*ch)?;
                self.bool(*joint)?;
                self.handle(*span, HandleKind::Span)
            }
            Tree::Ident { symbol, is_raw, span } => {
                self.u8(2)?;
                self.string(symbol)?;
                self.bool(*is_raw)?;
                self.handle(*span, HandleKind::Span)
            }
            Tree::Literal(l) => {
                self.u8(3)?;
                self.literal(l)
            }
        }
    }
    fn diagnostic(&mut self, d: &Diagnostic, depth: u16) -> Result<(), Error> {
        self.budget.depth(depth)?;
        self.budget.charge(Charge { values: 1, ..Charge::default() })?;
        if d.level > 3 {
            return Err(Error::InvalidWire("diagnostic level"));
        }
        self.u8(d.level)?;
        self.string(&d.message)?;
        self.vec(&d.spans, |w, h| w.handle(*h, HandleKind::Span))?;
        self.vec(&d.children, |w, d| w.diagnostic(d, depth.checked_add(1).ok_or(Error::Overflow)?))
    }
    fn call(&mut self, call: &Call) -> Result<(), Error> {
        call.validate()?;
        self.u64(call.id)?;
        self.u8(call.method.tag())?;
        self.vec(&call.arguments, |w, v| w.value(v, 0))
    }
    fn value(&mut self, v: &Value, depth: u16) -> Result<(), Error> {
        self.budget.depth(depth)?;
        self.budget.charge(Charge { values: 1, ..Charge::default() })?;
        match v {
            Value::Unit => self.u8(0),
            Value::Bool(b) => {
                self.u8(1)?;
                self.bool(*b)
            }
            Value::U64(n) => {
                self.u8(2)?;
                self.u64(*n)
            }
            Value::Text(s) => {
                self.u8(3)?;
                self.string(s)
            }
            Value::OptionalText(s) => {
                self.u8(4)?;
                self.opt_string(s)
            }
            Value::Stream(h) => {
                self.u8(5)?;
                self.handle(*h, HandleKind::Stream)
            }
            Value::Span(h) => {
                self.u8(6)?;
                self.handle(*h, HandleKind::Span)
            }
            Value::OptionalStream(h) => {
                self.u8(7)?;
                self.opt_handle(*h, HandleKind::Stream)
            }
            Value::OptionalSpan(h) => {
                self.u8(8)?;
                self.opt_handle(*h, HandleKind::Span)
            }
            Value::Tree(t) => {
                self.u8(9)?;
                self.tree(t)
            }
            Value::Trees(ts) => {
                self.u8(10)?;
                self.vec(ts, |w, t| w.tree(t))
            }
            Value::Streams(hs) => {
                self.u8(11)?;
                self.vec(hs, |w, h| w.handle(*h, HandleKind::Stream))
            }
            Value::Bound(b) => {
                self.u8(12)?;
                match b {
                    Bound::Included(n) => {
                        self.u8(0)?;
                        self.u64(*n)
                    }
                    Bound::Excluded(n) => {
                        self.u8(1)?;
                        self.u64(*n)
                    }
                    Bound::Unbounded => self.u8(2),
                }
            }
            Value::Range { start, end } => {
                if start > end {
                    return Err(Error::InvalidWire("range"));
                }
                self.u8(13)?;
                self.u64(*start)?;
                self.u64(*end)
            }
            Value::Literal(l) => {
                self.u8(14)?;
                self.literal(l)
            }
            Value::Diagnostic(d) => {
                self.u8(15)?;
                self.diagnostic(d, depth)
            }
            Value::Result { ok, value } => {
                self.u8(16)?;
                self.bool(*ok)?;
                self.value(value, depth.checked_add(1).ok_or(Error::Overflow)?)
            }
        }
    }
}

/// Internal exact snapshot of the existing Call encoding. This shares the
/// wire field encoder, but is not a frame or transmitted traffic: storage and
/// copy/encoding work are charged, while wire_bytes is left unchanged.
pub(crate) fn call_snapshot(call: &Call, budget: &Budget) -> Result<Vec<u8>, Error> {
    let mut writer = Writer { bytes: Vec::new(), budget };
    writer.call(call)?;
    budget.check()?;
    Ok(writer.bytes)
}

pub fn encode(envelope: &Envelope, budget: &Budget) -> Result<Vec<u8>, Error> {
    encode_inner(envelope, budget).map_err(|error| budget.refuse(error))
}
fn encode_inner(envelope: &Envelope, budget: &Budget) -> Result<Vec<u8>, Error> {
    envelope.binding.validate()?;
    let mut w = Writer { bytes: Vec::new(), budget };
    w.put(&[0; 4])?;
    w.put(b"TMP1")?;
    let b = &envelope.binding;
    w.u32(b.version)?;
    w.u64(b.invocation)?;
    for digest in
        [&b.compiler, &b.worker, &b.artifact, &b.metadata, &b.unit, &b.input_closure, &b.host_abi]
    {
        w.put(digest)?;
    }
    match &envelope.message {
        Message::Begin { declaration, kind, inputs, globals } => {
            if *kind > 2 || inputs.len() != if *kind == 1 { 2 } else { 1 } {
                return Err(Error::Schema);
            }
            w.u8(0)?;
            w.u32(*declaration)?;
            w.u8(*kind)?;
            w.vec(inputs, |w, h| w.handle(*h, HandleKind::Stream))?;
            for h in globals {
                w.handle(*h, HandleKind::Span)?;
            }
        }
        Message::Ready => w.u8(1)?,
        Message::Call(call) => {
            w.u8(2)?;
            w.call(call)?;
        }
        Message::Reply { id, value } => {
            w.u8(3)?;
            w.u64(*id)?;
            w.value(value, 0)?;
        }
        Message::Finish { output } => {
            w.u8(4)?;
            w.opt_handle(*output, HandleKind::Stream)?;
        }
        Message::Failure { reason } => {
            w.u8(5)?;
            w.string(reason)?;
        }
        Message::Cancel => w.u8(6)?,
    }
    let length = u32::try_from(w.bytes.len() - 4).map_err(|_| Error::Overflow)?;
    w.bytes[..4].copy_from_slice(&length.to_le_bytes());
    budget.charge(Charge {
        wire_bytes: u64::try_from(w.bytes.len()).map_err(|_| Error::Overflow)?,
        ..Charge::default()
    })?;
    Ok(w.bytes)
}
