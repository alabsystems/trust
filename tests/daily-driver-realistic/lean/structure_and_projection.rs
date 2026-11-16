pub mod m { clean {
    structure Pt where
      x : UInt64
      y : UInt64
    def sumc (p : Pt) : UInt64 := p.x + p.y
} }
