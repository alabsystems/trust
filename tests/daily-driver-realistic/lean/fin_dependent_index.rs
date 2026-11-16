pub mod m { clean {
    def pick (i : Fin 3) : Nat := i.val
    theorem pick_lt (i : Fin 3) : pick i < 3 := i.isLt
} }
