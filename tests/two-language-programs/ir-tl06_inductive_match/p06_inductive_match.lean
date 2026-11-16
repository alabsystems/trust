inductive Shape where
  | sq (s : UInt64)
  | rect (w h : UInt64)

def area : Shape → UInt64
  | .sq s => s * s
  | .rect w h => w * h

def areaOfRect (w h : UInt64) : UInt64 := area (.rect w h)
