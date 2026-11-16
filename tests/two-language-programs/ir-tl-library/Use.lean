-- Use.lean — second file of the standalone Lean library; imports Lib.
import Lib

def horner (x : UInt64) : UInt64 := ((x * 5 + 3) * x + 2) * x + 1
def negate32 (a : UInt32) : UInt32 := 0 - a
def program : UInt64 := 6

-- kernel-only: cites Lib's theorem across the file boundary
theorem fst3_again (a b c : UInt64) : fst3 a b c = a := fst3_eq a b c
theorem horner_def (x : UInt64) : horner x = ((x * 5 + 3) * x + 2) * x + 1 := rfl
