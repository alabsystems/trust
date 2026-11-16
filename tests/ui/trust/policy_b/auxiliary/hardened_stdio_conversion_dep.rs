//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A dependency compiled with verification OFF, the way Targo compiles every
//! dependency unit, whose conversions to `std::process::Stdio` write THIS
//! process's stdout. Each impl is legal here: `From`/`Into` and `Stdio` are
//! foreign, but `Loud`, `Box<Loud>` and `&Loud` count as local (`Box` and `&`
//! are `#[fundamental]`), and `Direct` is the `Self` type of its `Into` impl.
//! `Command::stdout::<T>` runs `cfg.into()`, so passing one of these runs the
//! `println!` below inside that call (measured: exit 101 on a closed pipe).

use std::process::Stdio;

pub struct Loud;

impl From<Loud> for Stdio {
    fn from(_: Loud) -> Stdio {
        println!("written by <Stdio as From<Loud>>::from");
        Stdio::null()
    }
}

impl From<Box<Loud>> for Stdio {
    fn from(_: Box<Loud>) -> Stdio {
        println!("written by <Stdio as From<Box<Loud>>>::from");
        Stdio::null()
    }
}

impl<'a> From<&'a Loud> for Stdio {
    fn from(_: &'a Loud) -> Stdio {
        println!("written by <Stdio as From<&Loud>>::from");
        Stdio::null()
    }
}

pub struct Direct;

impl Into<Stdio> for Direct {
    fn into(self) -> Stdio {
        println!("written by <Direct as Into<Stdio>>::into");
        Stdio::null()
    }
}
