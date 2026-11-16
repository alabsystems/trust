//! Full-source closure binding DATA, never source/GNU/CPU retirement authority.
//! Only the original native issuer may attest all actual members, paired loans
//! and observers closed/postchecked while its original inputs remain current.
use super::*;

pub const PURPOSE: &str = "native-bootstrap-compilation-close-v1";
#[derive(Clone, PartialEq, Eq)]
pub struct CloseRequest {
    pub key: Key,
}
impl CloseRequest {
    pub fn validate(&self) -> io::Result<()> {
        self.key.validate()
    }
    pub fn hello(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        self.key.attempt.key.graph.hello(PURPOSE)
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(185);
        e.number(1);
        self.key.write(&mut e)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 185)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let value = Self { key: Key::read(&mut d)? };
        d.done()?;
        value.validate()?;
        Ok(value)
    }
}
#[derive(Clone, PartialEq, Eq)]
pub struct Closed {
    pub request: CloseRequest,
    pub source: SourceAttachment,
    pub output: OutputAttachment,
}
impl Closed {
    pub fn validate(&self) -> io::Result<()> {
        self.request.validate()?;
        self.source.validate()?;
        self.output.encode()?;
        if self.source.key != self.request.key.attempt.key.graph
            || self.output.key != self.source.key
        {
            return Err(invalid());
        }
        Ok(())
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(186);
        e.number(1);
        e.frame_bytes(&self.request.encode()?)?;
        e.frame_bytes(&self.source.encode()?)?;
        e.frame_bytes(&self.output.encode()?)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 186)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let value = Self {
            request: CloseRequest::decode(&d.frame_bytes()?)?,
            source: SourceAttachment::decode(&d.frame_bytes()?)?,
            output: OutputAttachment::decode(&d.frame_bytes()?)?,
        };
        d.done()?;
        value.validate()?;
        Ok(value)
    }
}
#[cfg(test)]
mod tests;
