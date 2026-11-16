//@ run-pass
//@ compile-flags: -Z trust-verify=off
//! `clean` is not a keyword. `clean { … }` is an island ONLY at module item
//! position — the one place vanilla Rust rejects it — so a struct or module
//! named `clean` keeps every spelling vanilla Rust accepts, byte for byte:
//! struct literals in `let`, `static`, `const`, tail-expression and argument
//! position, patterns, the type in `fn … -> clean`, `impl clean`,
//! `struct clean`, a module *containing* one — and, the case a lexer-level
//! island has to be careful about, the same tokens inside a macro
//! invocation, which must reach the macro exactly as the user wrote them.
#![allow(non_camel_case_types, dead_code)]

struct clean {
    f: i32,
}

impl clean {
    fn get(&self) -> i32 {
        self.f
    }
}

static S: clean = clean { f: 1 };
const C: clean = clean { f: 2 };

fn tail() -> clean {
    clean { f: 3 }
}

fn after_stmt() -> clean {
    let x = 4;
    clean { f: x }
}

fn after_block() -> clean {
    if S.f == 1 {}
    clean { f: 5 }
}

fn arg(c: clean) -> i32 {
    c.get()
}

mod m {
    pub struct clean {
        pub f: i32,
    }
    pub fn mk() -> clean {
        clean { f: 6 }
    }
    pub mod clean_mod {
        pub fn seven() -> i32 {
            7
        }
    }
}

macro_rules! pass_through {
    ($($t:tt)*) => {
        stringify!($($t)*)
    };
}

macro_rules! make_item {
    ($i:item) => {
        $i
    };
}
make_item! {
    fn nine() -> clean {
        clean { f: 9 }
    }
}

fn main() {
    let s = clean { f: 10 };
    let clean { f } = clean { f: 11 };
    let total = S.f
        + C.f
        + tail().f
        + after_stmt().f
        + after_block().f
        + arg(clean { f: 12 })
        + m::mk().f
        + m::clean_mod::seven()
        + nine().f
        + s.f
        + f;
    assert_eq!(total, 1 + 2 + 3 + 4 + 5 + 12 + 6 + 7 + 9 + 10 + 11);
    match s {
        clean { f: 10 } => {}
        _ => panic!("struct pattern named `clean` must match"),
    }
    // A macro sees the user's tokens, braces and contents included — the
    // island lexer must not have blanked them.
    assert_eq!(pass_through!(clean { f: 1 }), "clean { f: 1 }");
    assert_eq!(stringify!(mod m { clean { f: 1 } }), "mod m { clean { f: 1 } }");
}
