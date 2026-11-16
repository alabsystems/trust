//@ compile-flags: -Z trust-verify=off
//! Temporal P2: a bug past the state budget is still caught. The violation is
//! 600 steps deep in a 1,001-state model; the kernel's own search explores 256
//! states. The compiler's fast untrusted search finds the state, and the
//! KERNEL confirms it without searching: it replays the 600 steps and
//! evaluates the invariant false at the end. The run prints its first 4 and
//! last 16 steps.

clean {
    import Trust.FiniteModel
    namespace Deep

    def x : Trust.Temporal.FiniteModel.ScalarExpr :=
      Trust.Temporal.FiniteModel.ScalarExpr.var "x"
    def one : Trust.Temporal.FiniteModel.ScalarExpr :=
      Trust.Temporal.FiniteModel.ScalarExpr.int 1

    def Counter : Trust.Temporal.FiniteModel.ScalarModel :=
      Trust.Temporal.FiniteModel.ScalarModel.mk "Counter" []
        [Trust.Temporal.FiniteModel.StateVar.mk "x" 0]
        [Trust.Temporal.FiniteModel.Action.mk "Step"
           (Trust.Temporal.FiniteModel.Guard.when
             (Trust.Temporal.FiniteModel.ScalarExpr.le
               (Trust.Temporal.FiniteModel.ScalarExpr.add x one)
               (Trust.Temporal.FiniteModel.ScalarExpr.int 1000)))
           [Trust.Temporal.FiniteModel.Update.mk "x"
              (Trust.Temporal.FiniteModel.ScalarExpr.add x one)]]
        [Trust.Temporal.FiniteModel.Invariant.mk "Bounded"
           (Trust.Temporal.FiniteModel.ScalarExpr.le x
             (Trust.Temporal.FiniteModel.ScalarExpr.int 599))]

    end Deep
}
//~^^^^^^^^^^^^^^^^ ERROR finite model `Deep.Counter` is unsafe

fn main() {}
