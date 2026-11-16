-- Part A standalone Lean lane: the second file. It IMPORTS Lib and cites its theorem.
import Lib
def keepLeft (a b : UInt64) : UInt64 := a
theorem keepLeft_is_pick (a b : UInt64) : keepLeft a b = pick a b := rfl
theorem keepLeft_eq (a b : UInt64) : keepLeft a b = a := pick_eq a b
