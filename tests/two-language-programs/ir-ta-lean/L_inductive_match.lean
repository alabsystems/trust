-- Part A standalone-Lean refusal probe: inductive_match
inductive Tri where
  | one : Tri
  | two : Tri
def triRank (t : Tri) : UInt64 :=
  match t with
  | Tri.one => 1
  | Tri.two => 2
