//@ compile-flags: -Z trust-verify=off
//! Temporal P2, the negative twin of `clean_island_declared_model_safe.rs`:
//! the same model with `Buggy = 1`, whose `x = y` invariant breaks one step
//! in. Nobody claimed anything beyond declaring the model, and the BUILD
//! FAILS at its definition, naming the reachable state and the invariant.

clean {
    import Trust.FiniteModel
    namespace Example

    def X : Trust.Temporal.FiniteModel.ScalarExpr :=
      Trust.Temporal.FiniteModel.ScalarExpr.var "x"
    def Y : Trust.Temporal.FiniteModel.ScalarExpr :=
      Trust.Temporal.FiniteModel.ScalarExpr.var "y"
    def Zero : Trust.Temporal.FiniteModel.ScalarExpr :=
      Trust.Temporal.FiniteModel.ScalarExpr.int 0
    def One : Trust.Temporal.FiniteModel.ScalarExpr :=
      Trust.Temporal.FiniteModel.ScalarExpr.int 1
    def Limit : Trust.Temporal.FiniteModel.ScalarExpr :=
      Trust.Temporal.FiniteModel.ScalarExpr.constRef "Limit"
    def Buggy : Trust.Temporal.FiniteModel.ScalarExpr :=
      Trust.Temporal.FiniteModel.ScalarExpr.constRef "Buggy"

    def Lockstep : Trust.Temporal.FiniteModel.ScalarModel :=
      Trust.Temporal.FiniteModel.ScalarModel.mk "CleanLockstep"
        [Trust.Temporal.FiniteModel.Constant.mk "Buggy" 1,
         Trust.Temporal.FiniteModel.Constant.mk "Limit" 2]
        [Trust.Temporal.FiniteModel.StateVar.mk "x" 0,
         Trust.Temporal.FiniteModel.StateVar.mk "y" 0]
        [Trust.Temporal.FiniteModel.Action.mk "Step"
           (Trust.Temporal.FiniteModel.Guard.when
             (Trust.Temporal.FiniteModel.ScalarExpr.le X
               (Trust.Temporal.FiniteModel.ScalarExpr.sub Limit One)))
           [Trust.Temporal.FiniteModel.Update.mk "x"
              (Trust.Temporal.FiniteModel.ScalarExpr.add X One),
            Trust.Temporal.FiniteModel.Update.mk "y"
              (Trust.Temporal.FiniteModel.ScalarExpr.ite
                (Trust.Temporal.FiniteModel.ScalarExpr.eq Buggy Zero)
                (Trust.Temporal.FiniteModel.ScalarExpr.add Y One) Y)],
         Trust.Temporal.FiniteModel.Action.mk "Reset"
           (Trust.Temporal.FiniteModel.Guard.when
             (Trust.Temporal.FiniteModel.ScalarExpr.gt X
               (Trust.Temporal.FiniteModel.ScalarExpr.sub Limit One)))
           [Trust.Temporal.FiniteModel.Update.mk "x" Zero,
            Trust.Temporal.FiniteModel.Update.mk "y" Zero]]
        [Trust.Temporal.FiniteModel.Invariant.mk "Lockstep"
           (Trust.Temporal.FiniteModel.ScalarExpr.eq X Y),
         Trust.Temporal.FiniteModel.Invariant.mk "Bounded"
           (Trust.Temporal.FiniteModel.ScalarExpr.le X Limit)]

    end Example
}
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR finite model `Example.Lockstep` is unsafe

fn main() {}
