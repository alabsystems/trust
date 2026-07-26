// Trust: regression test for compile-time bug rust-lang#138927
//
// Regression in trait evaluation with generic bounds. When a trait has
// multiple generic parameters with interdependent bounds, the trait solver
// may explore an exponentially growing set of candidate implementations.
// Each additional layer of generic bounds multiplies the search space for
// trait resolution.
//
// The original report showed a regression where previously-fast code became
// slow after changes to the trait evaluation cache. This test exercises
// deep generic bound nesting to ensure trait evaluation remains efficient.
//
// Upstream: https://github.com/rust-lang/rust/issues/138927
// Tracked in Trust: #865
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//@ check-pass

#![allow(dead_code)]

// Base traits with interdependent bounds.
trait Source {
    type Output;
}

trait Transform: Source {
    type Transformed;
    fn transform(&self) -> Self::Transformed;
}

trait Sink<T> {
    fn consume(&self, input: T);
}

// Layered generic struct that nests trait bounds deeply.
struct Pipe<A, B> {
    source: A,
    sink: B,
}

impl<A: Source, B> Source for Pipe<A, B> {
    type Output = A::Output;
}

impl<A: Transform, B: Sink<A::Transformed>> Transform for Pipe<A, B>
where
    A::Transformed: Clone,
{
    type Transformed = A::Transformed;
    fn transform(&self) -> Self::Transformed {
        self.source.transform()
    }
}

// Concrete types implementing the base traits.
struct IntSource;
impl Source for IntSource { type Output = i32; }
impl Transform for IntSource {
    type Transformed = i32;
    fn transform(&self) -> i32 { 42 }
}

struct PrintSink;
impl<T: std::fmt::Debug> Sink<T> for PrintSink {
    fn consume(&self, _input: T) {}
}

// Deeply nested pipeline. Each layer adds trait bound resolution work.
// The solver must verify Transform + Sink bounds at every nesting level.
fn build_pipeline() -> impl Transform {
    let stage1 = Pipe { source: IntSource, sink: PrintSink };
    let stage2 = Pipe { source: stage1, sink: PrintSink };
    let stage3 = Pipe { source: stage2, sink: PrintSink };
    let stage4 = Pipe { source: stage3, sink: PrintSink };
    let stage5 = Pipe { source: stage4, sink: PrintSink };
    let stage6 = Pipe { source: stage5, sink: PrintSink };
    let stage7 = Pipe { source: stage6, sink: PrintSink };
    let stage8 = Pipe { source: stage7, sink: PrintSink };
    let stage9 = Pipe { source: stage8, sink: PrintSink };
    let stage10 = Pipe { source: stage9, sink: PrintSink };
    let stage11 = Pipe { source: stage10, sink: PrintSink };
    let stage12 = Pipe { source: stage11, sink: PrintSink };
    stage12
}

fn main() {
    let pipeline = build_pipeline();
    let _result = pipeline.transform();
}
