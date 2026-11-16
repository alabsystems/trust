//@ compile-flags: -Z trust-verify=off
//! Temporal P2, the natural-number trap. `handled <= received - 1`, the usual
//! spelling of `handled < received`, is TRUE at `0 <= 0 - 1` over the naturals
//! the model language uses, so `Handle` fires on an empty queue. The kernel
//! is right about the model as written: it is unsafe. The compiler also says
//! WHY it differs from the model that was meant: it names the subtraction
//! that stopped at zero, where, and in which reachable state. Found by running
//! the models of a real program (aterm) through the checker.

clean {
    import Trust.FiniteModel
    namespace Queue

    def r : Trust.Temporal.FiniteModel.ScalarExpr :=
      Trust.Temporal.FiniteModel.ScalarExpr.var "received"
    def h : Trust.Temporal.FiniteModel.ScalarExpr :=
      Trust.Temporal.FiniteModel.ScalarExpr.var "handled"
    def one : Trust.Temporal.FiniteModel.ScalarExpr :=
      Trust.Temporal.FiniteModel.ScalarExpr.int 1

    def Fifo : Trust.Temporal.FiniteModel.ScalarModel :=
      Trust.Temporal.FiniteModel.ScalarModel.mk "Queue" []
        [Trust.Temporal.FiniteModel.StateVar.mk "received" 0,
         Trust.Temporal.FiniteModel.StateVar.mk "handled" 0]
        [Trust.Temporal.FiniteModel.Action.mk "Receive"
           (Trust.Temporal.FiniteModel.Guard.when
             (Trust.Temporal.FiniteModel.ScalarExpr.le r one))
           [Trust.Temporal.FiniteModel.Update.mk "received"
              (Trust.Temporal.FiniteModel.ScalarExpr.add r one)],
         Trust.Temporal.FiniteModel.Action.mk "Handle"
           (Trust.Temporal.FiniteModel.Guard.when
             (Trust.Temporal.FiniteModel.ScalarExpr.le h
               (Trust.Temporal.FiniteModel.ScalarExpr.sub r one)))
           [Trust.Temporal.FiniteModel.Update.mk "handled"
              (Trust.Temporal.FiniteModel.ScalarExpr.add h one)]]
        [Trust.Temporal.FiniteModel.Invariant.mk "NeverAhead"
           (Trust.Temporal.FiniteModel.ScalarExpr.le h r)]

    end Queue
}
//~^^^^^^^^^^^^^^^^^^^^ ERROR finite model `Queue.Fifo` is unsafe
//~^^^^^^^^^^^^^^^^^^^^^ WARN a subtraction evaluates `0 - 1` in the guard of `Handle`

fn main() {}
