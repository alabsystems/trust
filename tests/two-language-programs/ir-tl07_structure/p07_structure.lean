structure Pt where
  x : UInt64
  y : UInt64

def dot (p q : Pt) : UInt64 := p.x * q.x + p.y * q.y
def dotOf (a b c d : UInt64) : UInt64 := dot ⟨a, b⟩ ⟨c, d⟩
