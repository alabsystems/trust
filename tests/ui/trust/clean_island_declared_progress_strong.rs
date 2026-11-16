//@ compile-flags: -Z trust-verify=off
//@ check-pass
//! Temporal P2, a PROGRESS claim that rests on STRONG fairness, proved with no
//! authored proof. Unfair moves wander among x = 0, 1 and 2; `A` (strongly
//! fair) finishes from x = 2, `B` (strongly fair) from x = 1 and `W` (weakly
//! fair) from x = 0. A run that never finishes must eventually avoid x = 2 (or
//! strong fairness takes `A`), then x = 1 (or it takes `B`), and then it sits
//! at x = 0, where `W` is enabled for good. The compiler's certificate says
//! exactly that, one level per strongly fair action the row waits on (x = 2
//! has one level, x = 1 two, x = 0 three), and the KERNEL checks it, so
//! `trust_checked_live.Nest.Finishes : ScalarProgress.claim Nest.Finishes` is
//! a theorem in the environment. Written with `Trust.Protocol`'s short names.

clean {
    import Trust.Protocol

    namespace Nest
    open Trust.Protocol

    def go (name : String) (start target : Nat) : Trust.Temporal.FiniteModel.Action :=
      act name (v "x" ≐ n start ⋏ v "done" ≐ n 0) ["x" ≔ n target]
    def finish (name : String) (start : Nat) : Trust.Temporal.FiniteModel.Action :=
      act name (v "x" ≐ n start ⋏ v "done" ≐ n 0) ["done" ≔ n 1]

    def M : Trust.Temporal.FiniteModel.ScalarModel :=
      machine "Nest" [] [var "x" 0, var "done" 0]
        [go "U01" 0 1, go "U10" 1 0, go "U12" 1 2, go "U21" 2 1,
         finish "A" 2, finish "B" 1, finish "W" 0]
        []

    def Finishes : Trust.Temporal.FiniteModel.ScalarProgress :=
      progress M (v "done" ≐ n 1) ["W"] ["A", "B"]

    end Nest
}

fn main() {}
