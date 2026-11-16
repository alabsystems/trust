-- Lib.lean — the standalone Lean lane, library half.
-- Maximal fragment the standalone `targo trust build --emit=trust-ir` lane admits:
-- wrapping +,-,* expression trees, parameter projection, in-range literal returns,
-- and `let` (zeta-reduced), at the exact carriers UInt8/UInt16/UInt32/UInt64.
-- Theorems stay kernel-only.

def addmul (a b : UInt64) : UInt64 := a * b + a
def poly (x y z : UInt64) : UInt64 := (x * x + y * 3) - (z * x - 7)
def fst3 (a b c : UInt64) : UInt64 := a
def snd32 (a b : UInt32) : UInt32 := b
def lit64 : UInt64 := 18446744073709551615
def lit8 : UInt8 := 255
def wrap8 (a : UInt8) : UInt8 := a + 200
def mul16 (a b : UInt16) : UInt16 := a * b - 1
def sub32 (a b : UInt32) : UInt32 := a - b
def letsq (a : UInt64) : UInt64 := let t := a + 1; t * t
def mixproj (a : UInt8) (b : UInt16) (c : UInt32) (d : UInt64) : UInt32 := c

theorem fst3_eq (a b c : UInt64) : fst3 a b c = a := rfl
theorem addmul_def (a b : UInt64) : addmul a b = a * b + a := rfl
theorem snd32_eq (a b : UInt32) : snd32 a b = b := rfl
