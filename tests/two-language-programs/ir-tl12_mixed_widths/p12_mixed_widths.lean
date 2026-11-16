def w8 (a b : UInt8) : UInt8 := a * b + 1
def w16 (a b : UInt16) : UInt16 := a - b
def w32 (a b : UInt32) : UInt32 := a + b * a
def pickWide (a : UInt8) (b : UInt16) (c : UInt32) (d : UInt64) : UInt16 := b
