// Trust (TG4): a real callable Clean definition forces MIR construction and
// per-declaration carrier/faithfulness admission after the resolver checked it.
clean {
    def cleanFirst (a b : UInt64) : UInt64 := a
}

fn main() {
    assert_eq!(cleanFirst(41, 99), 41);
}
