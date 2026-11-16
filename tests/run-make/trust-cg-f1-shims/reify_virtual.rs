// `Shim(Reify(..))` over a `Virtual`: `<dyn T as T>::get` reified to a fn pointer.
pub trait T {
    fn get(&self) -> u64;
}

pub struct S(pub u64);

impl T for S {
    fn get(&self) -> u64 {
        self.0
    }
}

pub fn run(s: &S) -> u64 {
    let f: fn(&(dyn T + 'static)) -> u64 = <dyn T as T>::get;
    f(s)
}
