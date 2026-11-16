//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_diamond.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! 20 seals, seal `s_i` trusting the dependency's `a_i`, over a chain of 20
//! diamonds of generic fns (`seal_dep_diamond`): the paths to a body of the
//! dependency trust 20 different sets of seals' entries, 2^20 sets in all
//! (`Trust.Protocol.Seal`). Every seal HOLDS, and the walk reads each body
//! about once: a body reached again is read again only for a seal that the
//! new way leaves uncovered and every earlier reading covered. Review 1 of
//! the review-14 build: keyed on the set itself, the walk read the bodies
//! once per path, passed its bound of 2,000,000 instances, and refused every
//! seal of this true program. (`_ways.rs`: a body reached on a covered way
//! first, and on an uncovered one after, is still refused.)

#![allow(unused)]

extern crate seal_dep_diamond;

mod m1 {
    pub struct C1 { n: u32 }
    impl C1 {
        pub fn new() -> Self { C1 { n: 0 } }
        pub fn w1(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
}
mod m2 {
    pub struct C2 { n: u32 }
    impl C2 {
        pub fn new() -> Self { C2 { n: 0 } }
        pub fn w2(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
}
mod m3 {
    pub struct C3 { n: u32 }
    impl C3 {
        pub fn new() -> Self { C3 { n: 0 } }
        pub fn w3(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
}
mod m4 {
    pub struct C4 { n: u32 }
    impl C4 {
        pub fn new() -> Self { C4 { n: 0 } }
        pub fn w4(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
}
mod m5 {
    pub struct C5 { n: u32 }
    impl C5 {
        pub fn new() -> Self { C5 { n: 0 } }
        pub fn w5(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
}
mod m6 {
    pub struct C6 { n: u32 }
    impl C6 {
        pub fn new() -> Self { C6 { n: 0 } }
        pub fn w6(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
}
mod m7 {
    pub struct C7 { n: u32 }
    impl C7 {
        pub fn new() -> Self { C7 { n: 0 } }
        pub fn w7(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
}
mod m8 {
    pub struct C8 { n: u32 }
    impl C8 {
        pub fn new() -> Self { C8 { n: 0 } }
        pub fn w8(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
}
mod m9 {
    pub struct C9 { n: u32 }
    impl C9 {
        pub fn new() -> Self { C9 { n: 0 } }
        pub fn w9(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
}
mod m10 {
    pub struct C10 { n: u32 }
    impl C10 {
        pub fn new() -> Self { C10 { n: 0 } }
        pub fn w10(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
}
mod m11 {
    pub struct C11 { n: u32 }
    impl C11 {
        pub fn new() -> Self { C11 { n: 0 } }
        pub fn w11(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
}
mod m12 {
    pub struct C12 { n: u32 }
    impl C12 {
        pub fn new() -> Self { C12 { n: 0 } }
        pub fn w12(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
}
mod m13 {
    pub struct C13 { n: u32 }
    impl C13 {
        pub fn new() -> Self { C13 { n: 0 } }
        pub fn w13(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
}
mod m14 {
    pub struct C14 { n: u32 }
    impl C14 {
        pub fn new() -> Self { C14 { n: 0 } }
        pub fn w14(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
}
mod m15 {
    pub struct C15 { n: u32 }
    impl C15 {
        pub fn new() -> Self { C15 { n: 0 } }
        pub fn w15(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
}
mod m16 {
    pub struct C16 { n: u32 }
    impl C16 {
        pub fn new() -> Self { C16 { n: 0 } }
        pub fn w16(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
}
mod m17 {
    pub struct C17 { n: u32 }
    impl C17 {
        pub fn new() -> Self { C17 { n: 0 } }
        pub fn w17(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
}
mod m18 {
    pub struct C18 { n: u32 }
    impl C18 {
        pub fn new() -> Self { C18 { n: 0 } }
        pub fn w18(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
}
mod m19 {
    pub struct C19 { n: u32 }
    impl C19 {
        pub fn new() -> Self { C19 { n: 0 } }
        pub fn w19(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
}
mod m20 {
    pub struct C20 { n: u32 }
    impl C20 {
        pub fn new() -> Self { C20 { n: 0 } }
        pub fn w20(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
}
pub struct App {
    c1: m1::C1,
    c2: m2::C2,
    c3: m3::C3,
    c4: m4::C4,
    c5: m5::C5,
    c6: m6::C6,
    c7: m7::C7,
    c8: m8::C8,
    c9: m9::C9,
    c10: m10::C10,
    c11: m11::C11,
    c12: m12::C12,
    c13: m13::C13,
    c14: m14::C14,
    c15: m15::C15,
    c16: m16::C16,
    c17: m17::C17,
    c18: m18::C18,
    c19: m19::C19,
    c20: m20::C20,
}
impl App {
    fn new() -> Self {
        App {
            c1: m1::C1::new(),
            c2: m2::C2::new(),
            c3: m3::C3::new(),
            c4: m4::C4::new(),
            c5: m5::C5::new(),
            c6: m6::C6::new(),
            c7: m7::C7::new(),
            c8: m8::C8::new(),
            c9: m9::C9::new(),
            c10: m10::C10::new(),
            c11: m11::C11::new(),
            c12: m12::C12::new(),
            c13: m13::C13::new(),
            c14: m14::C14::new(),
            c15: m15::C15::new(),
            c16: m16::C16::new(),
            c17: m17::C17::new(),
            c18: m18::C18::new(),
            c19: m19::C19::new(),
            c20: m20::C20::new(),
        }
    }
}

fn main() {
    let mut app = App::new();
    app.c1.w1();
    app.c2.w2();
    app.c3.w3();
    app.c4.w4();
    app.c5.w5();
    app.c6.w6();
    app.c7.w7();
    app.c8.w8();
    app.c9.w9();
    app.c10.w10();
    app.c11.w11();
    app.c12.w12();
    app.c13.w13();
    app.c14.w14();
    app.c15.w15();
    app.c16.w16();
    app.c17.w17();
    app.c18.w18();
    app.c19.w19();
    app.c20.w20();
    println!("{} {}", seal_dep_diamond::a1(&app), app.c1.get());
}

clean {
    import Trust.Binding
    namespace TrustMasks
    open Trust.Protocol
    def s1 : Trust.Protocol.Seal := seals "m1::C1" ["w1"] ["C1::new"] ["App::new"] ["seal_dep_diamond::a1"]
    def s2 : Trust.Protocol.Seal := seals "m2::C2" ["w2"] ["C2::new"] ["App::new"] ["seal_dep_diamond::a2"]
    def s3 : Trust.Protocol.Seal := seals "m3::C3" ["w3"] ["C3::new"] ["App::new"] ["seal_dep_diamond::a3"]
    def s4 : Trust.Protocol.Seal := seals "m4::C4" ["w4"] ["C4::new"] ["App::new"] ["seal_dep_diamond::a4"]
    def s5 : Trust.Protocol.Seal := seals "m5::C5" ["w5"] ["C5::new"] ["App::new"] ["seal_dep_diamond::a5"]
    def s6 : Trust.Protocol.Seal := seals "m6::C6" ["w6"] ["C6::new"] ["App::new"] ["seal_dep_diamond::a6"]
    def s7 : Trust.Protocol.Seal := seals "m7::C7" ["w7"] ["C7::new"] ["App::new"] ["seal_dep_diamond::a7"]
    def s8 : Trust.Protocol.Seal := seals "m8::C8" ["w8"] ["C8::new"] ["App::new"] ["seal_dep_diamond::a8"]
    def s9 : Trust.Protocol.Seal := seals "m9::C9" ["w9"] ["C9::new"] ["App::new"] ["seal_dep_diamond::a9"]
    def s10 : Trust.Protocol.Seal := seals "m10::C10" ["w10"] ["C10::new"] ["App::new"] ["seal_dep_diamond::a10"]
    def s11 : Trust.Protocol.Seal := seals "m11::C11" ["w11"] ["C11::new"] ["App::new"] ["seal_dep_diamond::a11"]
    def s12 : Trust.Protocol.Seal := seals "m12::C12" ["w12"] ["C12::new"] ["App::new"] ["seal_dep_diamond::a12"]
    def s13 : Trust.Protocol.Seal := seals "m13::C13" ["w13"] ["C13::new"] ["App::new"] ["seal_dep_diamond::a13"]
    def s14 : Trust.Protocol.Seal := seals "m14::C14" ["w14"] ["C14::new"] ["App::new"] ["seal_dep_diamond::a14"]
    def s15 : Trust.Protocol.Seal := seals "m15::C15" ["w15"] ["C15::new"] ["App::new"] ["seal_dep_diamond::a15"]
    def s16 : Trust.Protocol.Seal := seals "m16::C16" ["w16"] ["C16::new"] ["App::new"] ["seal_dep_diamond::a16"]
    def s17 : Trust.Protocol.Seal := seals "m17::C17" ["w17"] ["C17::new"] ["App::new"] ["seal_dep_diamond::a17"]
    def s18 : Trust.Protocol.Seal := seals "m18::C18" ["w18"] ["C18::new"] ["App::new"] ["seal_dep_diamond::a18"]
    def s19 : Trust.Protocol.Seal := seals "m19::C19" ["w19"] ["C19::new"] ["App::new"] ["seal_dep_diamond::a19"]
    def s20 : Trust.Protocol.Seal := seals "m20::C20" ["w20"] ["C20::new"] ["App::new"] ["seal_dep_diamond::a20"]
    end TrustMasks
}
