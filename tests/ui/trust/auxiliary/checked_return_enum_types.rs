//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ no-prefer-dynamic
#![crate_name = "checked_return_enum_types"]

#[derive(Clone, Copy)]
pub enum Linkage { Private, External }

#[derive(Clone, Copy)]
pub enum Visibility { Default, Hidden }

impl Linkage {
    #[inline(never)]
    pub fn is_module_local(self) -> bool { matches!(self, Self::Private) }
}

#[derive(Clone, Copy)]
pub enum CallingConv { Rust, RustCold }

impl CallingConv {
    #[inline(never)]
    pub fn is_abi_surface(self) -> bool { matches!(self, Self::RustCold) }
}
