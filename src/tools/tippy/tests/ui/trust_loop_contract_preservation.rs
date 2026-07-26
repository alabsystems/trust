//@compile-flags: -Z trust-verify=off
//@check-pass

#![deny(clippy::if_same_then_else)]
#![deny(clippy::match_same_arms)]
#![deny(clippy::while_let_on_iterator)]
#![allow(clippy::non_minimal_cfg)]
#![allow(clippy::unnested_or_patterns)]
#![allow(dead_code)]

fn contract_blocks_while_let_rewrite(mut values: std::vec::IntoIter<u8>) {
    while let Some(value) = values.next()
        invariant value <= u8::MAX
    {
        let _ = value;
    }
}

fn different_if_contracts(mut n: u8, choose: bool) {
    if choose {
        while n > 0
            invariant n <= 10
        {
            n -= 1;
        }
    } else {
        while n > 0
            invariant n <= 11
        {
            n -= 1;
        }
    }
}

fn different_match_contracts(mut n: u8, choose: bool) {
    match choose {
        true => {
            while n > 0
                invariant n <= 10
            {
                n -= 1;
            }
        }
        false => {
            while n > 0
                invariant n <= 11
            {
                n -= 1;
            }
        }
    }
}

struct Fields {
    a: u8,
    b: u8,
}

// A true `cfg` is retained as `EarlyParsedAttribute::CfgTrace`. Comparing
// these non-focus fields used to reach a production `todo!()` in AST equality.
fn parsed_cfg_attributes_do_not_panic(value: Fields) {
    match value {
        Fields {
            a: 0,
            #[cfg(all())]
            b: 1,
        }
        | Fields {
            a: 2,
            #[cfg(all())]
            b: 1,
        } => {
            std::hint::black_box(());
        },
        _ => {},
    }
}

fn main() {}
