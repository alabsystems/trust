// Trust (TG4): an actual two-state model finishes once in HIR, after the
// resolver checked its declarations. The Step witness falsifies the mutant.
clean {
    import Trust.FiniteModel
    namespace Tiny
    def X : Trust.Temporal.FiniteModel.ScalarExpr :=
        Trust.Temporal.FiniteModel.ScalarExpr.var "x"
    def Zero : Trust.Temporal.FiniteModel.ScalarExpr :=
        Trust.Temporal.FiniteModel.ScalarExpr.int 0
    def One : Trust.Temporal.FiniteModel.ScalarExpr :=
        Trust.Temporal.FiniteModel.ScalarExpr.int 1
    def Model : Trust.Temporal.FiniteModel.ScalarModel :=
        Trust.Temporal.FiniteModel.ScalarModel.mk "Tiny"
            []
            [Trust.Temporal.FiniteModel.StateVar.mk "x" 0]
            [Trust.Temporal.FiniteModel.Action.mk "Step"
                (Trust.Temporal.FiniteModel.Guard.when
                    (Trust.Temporal.FiniteModel.ScalarExpr.eq X Zero))
                [Trust.Temporal.FiniteModel.Update.mk "x" One]]
            [Trust.Temporal.FiniteModel.Invariant.mk "bounded"
                (Trust.Temporal.FiniteModel.ScalarExpr.le X One)]
    end Tiny
}

fn main() {}
