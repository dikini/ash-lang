//! Measured work admission for the bounded DN-0036 experiment.
//!
//! These are cumulative charged units, including reservations, rather than CPU
//! time or bytes. Only the modular public driver selects these allowances.

/// An independently accounted compilation phase.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CompilationPhase {
    /// Checking the complete dependency-ordered source graph.
    SourceChecking,
    /// Applying checked preparations and lowering the linked graph, including zonking.
    FinalElaboration,
    /// Independently authenticating the final modular Core program.
    IndependentCore,
}

impl CompilationPhase {
    /// The completed calibration maximum rounded up to 65,536 charged units.
    #[must_use]
    pub const fn budget(self) -> usize {
        match self {
            Self::SourceChecking => 1_245_184,
            Self::FinalElaboration => 393_216,
            Self::IndependentCore => 1_638_400,
        }
    }

    /// The finite stopping limit, with at most 10% additional whole units.
    #[must_use]
    pub const fn hard_limit(self) -> usize {
        self.budget() + self.budget() / 10
    }

    /// Reports the measured cost without granting checking or Core authority.
    #[must_use]
    pub const fn assess(self, used: usize) -> PhaseCost {
        PhaseCost {
            phase: self,
            used,
            completed: true,
        }
    }
}

/// The relationship between measured work and its calibrated allowance.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum WorkAssessment {
    /// Completed work fits the nominal calibrated budget.
    WithinBudget,
    /// A deficit of at most 10% is accepted and remains an optimization target.
    AcceptedDeficit {
        /// Charged units above the nominal budget.
        units: usize,
    },
    /// The measured work exceeds the hard stopping allowance.
    OutsideAllowance {
        /// Charged units above the nominal budget.
        units: usize,
    },
}

/// One measured cumulative ledger; no physical-cost conversion is implied.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PhaseCost {
    /// Whether the owning phase completed; failed phases retain partial charges.
    pub completed: bool,
    /// The ledger's owning phase.
    pub phase: CompilationPhase,
    /// Actual charged units, including reserved work.
    pub used: usize,
}

impl PhaseCost {
    /// Derives the explicit assessment from the single recorded charged count.
    #[must_use]
    pub const fn assessment(self) -> WorkAssessment {
        if self.used <= self.phase.budget() {
            WorkAssessment::WithinBudget
        } else if self.used <= self.phase.hard_limit() {
            WorkAssessment::AcceptedDeficit {
                units: self.used - self.phase.budget(),
            }
        } else {
            WorkAssessment::OutsideAllowance {
                units: self.used - self.phase.budget(),
            }
        }
    }

    pub(crate) const fn incomplete(mut self) -> Self {
        self.completed = false;
        self
    }

    /// Whether this observation identifies work for future optimization.
    #[must_use]
    pub const fn optimization_target(self) -> bool {
        matches!(self.assessment(), WorkAssessment::AcceptedDeficit { .. })
    }
}

/// Observed phase measurements returned by the public modular driver.
///
/// These do not include separate builder, rewrite, constraint, syntax or runtime
/// budgets, nor CPU or peak RSS. Absent fields were not observed by this run.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct CompilationWork {
    /// Complete source checking, including the closed-entry check.
    pub source_checking: Option<PhaseCost>,
    /// Final elaborator work, excluding earlier linked-interface provider preparation
    /// and separate builder-owned work.
    pub final_elaboration: Option<PhaseCost>,
    /// Complete independent modular Core validation.
    pub independent_core: Option<PhaseCost>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn calibrated_admission_reports_exact_margin_and_first_refused_unit() {
        for phase in [
            CompilationPhase::SourceChecking,
            CompilationPhase::FinalElaboration,
            CompilationPhase::IndependentCore,
        ] {
            assert_eq!(
                phase.assess(phase.budget()).assessment(),
                WorkAssessment::WithinBudget
            );
            let first = phase.assess(phase.budget() + 1);
            assert_eq!(
                first.assessment(),
                WorkAssessment::AcceptedDeficit { units: 1 }
            );
            assert!(first.optimization_target());
            let last = phase.assess(phase.hard_limit());
            assert_eq!(
                last.assessment(),
                WorkAssessment::AcceptedDeficit {
                    units: phase.budget() / 10
                }
            );
            let refused = phase.assess(phase.hard_limit() + 1);
            assert_eq!(
                refused.assessment(),
                WorkAssessment::OutsideAllowance {
                    units: phase.budget() / 10 + 1
                }
            );
            assert!(!refused.optimization_target());
            assert!(matches!(
                phase.assess(usize::MAX).assessment(),
                WorkAssessment::OutsideAllowance { .. }
            ));
            let mut work = crate::types::TypeWorkBudget::with_limit(phase.hard_limit());
            work.charge(phase.hard_limit()).unwrap();
            assert_eq!(work.charge(1), Err(()));
            assert_eq!(work.charge(usize::MAX), Err(()));
            assert_eq!(work.used(), phase.hard_limit());
        }
    }
}
