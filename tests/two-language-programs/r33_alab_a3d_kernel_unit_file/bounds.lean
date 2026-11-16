-- The r31 island, moved verbatim out of line. This file is the ONLY difference
-- between this row and `r31_alab_a3d_kernel_bounds`: same Rust, same clauses,
-- same theorem, same authenticated lane.
--
-- a3d `range_in_bounds`, its overflow wrapper removed: the half-open byte range
-- `[off, end)` is inside a blob of `f` bytes exactly when `e <= f`. `<=` at an
-- unsigned carrier goes through Clean's own `instLEUInt64` /
-- `instDecidableUInt64Le`, which is why the decision spells as plain
-- `decide (e <= f)`.
def within_isl (e : UInt64) (f : UInt64) : Bool := decide (e <= f)

-- a3d `min4`'s two-ary core.
def min2_isl (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b

-- Why the body satisfies a bound its text never mentions: the minimum of two
-- values is at most the first of them.
theorem min2_isl_le_left (a b : UInt64) : min2_isl a b <= a := by
  unfold min2_isl
  split <;> omega
