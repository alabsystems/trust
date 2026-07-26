// Regression test for rust-lang#102678: associated type normalization unsoundness.
//
// The bug allowed associated type normalization to produce types that do not
// satisfy the bounds declared on the associated type in the trait definition.
// For example, `trait Foo { type Assoc: Clone; }` with an impl that provides
// `type Assoc = NotClone` could bypass the `Clone` bound check during
// normalization, allowing unsound code to compile.
//
// Trust: soundness fix for associated type normalization bound checking.

// Test 1: Direct bound violation through normalization
trait HasCloneAssoc {
    type Assoc: Clone;
}

struct NotClone;

// This impl correctly fails because NotClone doesn't implement Clone.
// The normalization fix ensures bounds are checked even through indirect paths.
impl HasCloneAssoc for () {
    type Assoc = NotClone;
    //~^ ERROR the trait bound `NotClone: Clone` is not satisfied
}

// Test 2: Attempting to exploit normalization through a generic wrapper
trait Transformer {
    type Output: Send + Sync;
}

struct NotSendSync {
    _data: *mut u8,
}

impl Transformer for String {
    type Output = NotSendSync;
    //~^ ERROR `*mut u8` cannot be sent between threads safely
    //~| ERROR `*mut u8` cannot be shared between threads safely
}

// Test 3: Bound checking through nested associated types
trait Outer {
    type Inner: Default;
}

struct NoDefault;

impl Outer for i32 {
    type Inner = NoDefault;
    //~^ ERROR the trait bound `NoDefault: Default` is not satisfied
}

// Test 4: Ensure that valid impls still work after the fix
trait ValidTrait {
    type Assoc: Clone + Default;
}

impl ValidTrait for () {
    type Assoc = String; // String: Clone + Default, this should compile fine
}

fn use_valid<T: ValidTrait>() -> T::Assoc {
    T::Assoc::default()
}

fn main() {
    let _ = use_valid::<()>();
}
