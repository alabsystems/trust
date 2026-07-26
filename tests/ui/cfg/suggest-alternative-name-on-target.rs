#![deny(unexpected_cfgs)]
//~^ NOTE lint level is defined here

// target arch used in `target_abi`
#[cfg(target_abi = "arm")]
//~^ ERROR unexpected `cfg` condition value:
//~| NOTE see the Trust trustc check-cfg documentation
//~| HELP `arm` is an expected value for `target_arch`
struct A;

// target env used in `target_arch`
#[cfg(target_arch = "gnu")]
//~^ ERROR unexpected `cfg` condition value:
//~| NOTE see the Trust trustc check-cfg documentation
//~| HELP `gnu` is an expected value for `target_env`
struct B;

// target os used in `target_env`
#[cfg(target_env = "openbsd")]
//~^ ERROR unexpected `cfg` condition value:
//~| NOTE see the Trust trustc check-cfg documentation
//~| HELP `openbsd` is an expected value for `target_os`
struct C;

// target abi used in `target_os`
#[cfg(target_os = "eabi")]
//~^ ERROR unexpected `cfg` condition value:
//~| NOTE see the Trust trustc check-cfg documentation
//~| HELP `eabi` is an expected value for `target_abi`
struct D;

#[cfg(target_abi = "windows")]
//~^ ERROR unexpected `cfg` condition value:
//~| NOTE see the Trust trustc check-cfg documentation
//~| HELP `windows` is an expected value for `target_family`
//~| HELP `windows` is an expected value for `target_os`
struct E;

fn main() {}
