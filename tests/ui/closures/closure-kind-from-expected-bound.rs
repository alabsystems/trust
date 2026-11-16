// Trust: D0.7 static-semantics source map, row ALG-CLOSURE-KIND-FROM-EXPECTATION.
//
// The closure below neither mutates nor moves out of a capture, so by its body
// alone it implements `Fn`. It is passed where `FnMut` is expected, and rustc
// fixes its kind from that expectation, so the later `Fn` requirement fails.

fn as_fnmut<F: FnMut()>(f: F) -> F {
    f
}

fn needs_fn<F: Fn()>(_: &F) {}

fn main() {
    let c = as_fnmut(|| {});
    //~^ ERROR E0525
    needs_fn(&c);
}
