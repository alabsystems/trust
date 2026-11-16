pub mod m { clean {
    class Mag (a : Type) where
      op : a -> a -> a
    instance : Mag Nat where
      op := fun x y => x + y
    def twice {a : Type} [Mag a] (x : a) : a := Mag.op x x
} }
