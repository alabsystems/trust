// Trust: unsupported uncited enum shapes are not new compile errors.
#![allow(dead_code)]
pub enum Phase { Ready, Waiting }
pub fn kernel(p: Phase) -> bool { match p { Phase::Ready if true => true, _ => false } }
