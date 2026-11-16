#[derive(Clone, Copy)]
pub enum Site { Summary, Inherited, Call, Handle }

#[derive(Clone, Copy)]
pub enum Kind {
    Precondition, Postcondition, LoopInvariant, TypeInvariant, RefinementType,
    TranslationValidation, MemorySafety, PanicFreedom, TemporalSafety, Liveness,
    Arithmetic, BoundsCheck, GiveBackRefinement, Termination, Ownership, Custom,
}

impl Site {
    #[inline(never)]
    pub const fn admits(self, kind: Kind) -> bool {
        match self {
            Self::Summary => matches!(kind, Kind::Precondition | Kind::Postcondition | Kind::Termination),
            Self::Inherited => matches!(kind,
                Kind::Precondition | Kind::Postcondition | Kind::LoopInvariant | Kind::TypeInvariant |
                Kind::RefinementType | Kind::TranslationValidation | Kind::MemorySafety |
                Kind::PanicFreedom | Kind::TemporalSafety | Kind::Liveness | Kind::Arithmetic |
                Kind::BoundsCheck | Kind::GiveBackRefinement | Kind::Termination | Kind::Ownership),
            Self::Call | Self::Handle => false,
        }
    }
}
