pub mod m { clean {
    inductive Vec (a : Type) : Nat -> Type where
      | nil : Vec a 0
      | cons : a -> {n : Nat} -> Vec a n -> Vec a (n+1)
    def vlen {a : Type} {n : Nat} (_ : Vec a n) : Nat := n
} }
