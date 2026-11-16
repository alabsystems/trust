//@ only-apple
//@ edition: 2021
//@ proc-macro: serde_shaped.rs
//@ proc-macro: thiserror_shaped.rs
//@ revisions: in_process isolated
//@[isolated] compile-flags: -Ztrust-proc-macro-isolation
//@ run-pass
//! Trust (D21): the programs the two derives expand to run the same, whether the
//! macros ran in rustc or in the sandboxed worker. One crate, two proc-macro
//! dylibs: the isolated revision starts one worker for each.

#[macro_use]
extern crate serde_shaped;
#[macro_use]
extern crate thiserror_shaped;

pub trait Shape {
    const NAME: &'static str;
    const SKIPPED: usize;
    fn fields(&self) -> Vec<(&'static str, String)>;
}

#[derive(Shape)]
struct Point<T> {
    #[shape(rename = "ex")]
    x: T,
    y: u32,
    #[shape(skip)]
    #[allow(dead_code)]
    cache: Vec<Option<T>>,
}

#[derive(Debug, Failure)]
enum LoadFailure {
    #[error("the file is empty")]
    Empty,
    #[error("line {line}: {reason}")]
    Parse { line: usize, reason: String },
    #[error("expected {0} fields, found {1}")]
    Arity(usize, usize),
    #[error("i/o: {0}")]
    Io(#[from] std::io::Error),
}

fn main() {
    let point = Point { x: "left", y: 7, cache: Vec::new() };
    assert_eq!(<Point<&str> as Shape>::NAME, "Point");
    assert_eq!(<Point<&str> as Shape>::SKIPPED, 1);
    assert_eq!(
        point.fields(),
        vec![("ex", "\"left\"".to_string()), ("y", "7".to_string())]
    );

    assert_eq!(LoadFailure::Empty.to_string(), "the file is empty");
    assert_eq!(
        LoadFailure::Parse { line: 3, reason: "stray comma".into() }.to_string(),
        "line 3: stray comma"
    );
    assert_eq!(LoadFailure::Arity(2, 5).to_string(), "expected 2 fields, found 5");
    let converted: LoadFailure = std::io::Error::other("disk").into();
    assert_eq!(converted.to_string(), "i/o: disk");
    let _: &dyn std::error::Error = &converted;
}
