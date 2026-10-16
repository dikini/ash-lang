//! Cumulative compilation work admission and measured phase reports.
//!
//! These are cumulative charged units, including reservations, rather than CPU
//! time or bytes. Only the modular public driver selects these allowances.

use crate::{module::ModuleGraph, source::SourceFile, types::TypeWorkBudget};

const SOURCE_PER_BYTE: usize = 800;

/// Separate per-arena capacity from the already-paid canonical source size.
pub(crate) fn rewrite_total(bytes: usize) -> Result<usize, ()> {
    bytes.checked_mul(16).ok_or(())
}

fn source_total(bytes: usize) -> Result<usize, ()> {
    bytes.checked_mul(SOURCE_PER_BYTE).ok_or(())
}

fn phase_total(phase: CompilationPhase, bytes: usize) -> Result<usize, ()> {
    match phase {
        CompilationPhase::SourceChecking => source_total(bytes),
        CompilationPhase::FinalElaboration => bytes.checked_mul(800).ok_or(()),
        CompilationPhase::IndependentCore => bytes.checked_mul(345).ok_or(()),
    }
}

fn size_sources<'a>(
    sources: impl Iterator<Item = &'a SourceFile>,
    phase: CompilationPhase,
    work: &mut TypeWorkBudget,
) -> Result<(usize, usize), ()> {
    work.charge(1)?;
    let mut bytes = 0usize;
    for source in sources {
        work.charge(1)?;
        bytes = bytes.checked_add(source.text().len()).ok_or(())?;
    }
    Ok((phase_total(phase, bytes)?, bytes))
}

pub(crate) fn source_work(graph: &ModuleGraph) -> Result<(TypeWorkBudget, usize), ()> {
    // The loader has already admitted one source per canonical module. Aliases
    // and repeated import edges do not add modules or size credit here.
    let bootstrap = graph.modules().len().checked_add(1).ok_or(())?;
    let mut work = TypeWorkBudget::with_limit(bootstrap);
    let (total, bytes) = size_sources(
        graph.modules().iter().map(|module| module.source()),
        CompilationPhase::SourceChecking,
        &mut work,
    )?;
    work.finish_sizing(total)?;
    Ok((work, bytes))
}

pub(crate) fn resident_phase_work(
    phase: CompilationPhase,
    sources: &[&SourceFile],
) -> Result<(TypeWorkBudget, usize), ()> {
    // The public driver supplies the canonical loaded closure, including
    // builtins, once. Each phase pays its own resident-length census.
    let mut work = TypeWorkBudget::with_limit(sources.len().checked_add(1).ok_or(())?);
    let (total, bytes) = size_sources(sources.iter().copied(), phase, &mut work)?;
    work.finish_sizing(total)?;
    Ok((work, bytes))
}

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
    /// The historical calibration reference, rounded to 65,536 charged units.
    /// The modular public driver instead uses its resident-source allowances.
    #[must_use]
    pub const fn budget(self) -> usize {
        match self {
            Self::SourceChecking => 1_245_184,
            Self::FinalElaboration => 393_216,
            Self::IndependentCore => 1_638_400,
        }
    }

    /// The historical calibrated stopping reference, including its 10% margin.
    /// Input-derived public-driver totals do not receive this extra margin.
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
            allowance: None,
        }
    }

    pub(crate) const fn assess_with_allowance(self, used: usize, allowance: usize) -> PhaseCost {
        let mut cost = self.assess(used);
        cost.allowance = Some(allowance);
        cost
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
    /// The actual input-derived total, when this phase uses one. It has no
    /// additional calibrated deficit allowance.
    pub allowance: Option<usize>,
}

impl PhaseCost {
    /// Derives the explicit assessment from the single recorded charged count.
    #[must_use]
    pub const fn assessment(self) -> WorkAssessment {
        if let Some(allowance) = self.allowance {
            return if self.used <= allowance {
                WorkAssessment::WithinBudget
            } else {
                WorkAssessment::OutsideAllowance {
                    units: self.used - allowance,
                }
            };
        }
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
    fn rewrite_gas_uses_the_paid_size_and_checked_scalar_total() {
        let source = SourceFile::new("rewrite-gas.ash", "main () = ()\n").unwrap();
        let (source_work, bytes) =
            resident_phase_work(CompilationPhase::SourceChecking, &[&source]).unwrap();
        assert_eq!(bytes, source.text().len());
        assert_eq!((source_work.used(), source_work.limit()), (2, 800 * bytes));
        assert_eq!(rewrite_total(bytes), Ok(16 * bytes));
        assert_eq!(rewrite_total(0), Ok(0));
        assert!(rewrite_total(usize::MAX / 16 + 1).is_err());
        let mut rewrite = TypeWorkBudget::with_limit(rewrite_total(bytes).unwrap());
        rewrite.charge(rewrite.remaining()).unwrap();
        assert!(rewrite.charge(1).is_err());
        assert_eq!(source_work.used(), 2);
    }

    #[test]
    fn resident_phase_gas_pays_census_and_preserves_exact_total() {
        let source = SourceFile::new("phase.ash", "main : Unit -> Int\nmain () = 42\n").unwrap();
        for (phase, coefficient) in [
            (CompilationPhase::FinalElaboration, 800),
            (CompilationPhase::IndependentCore, 345),
        ] {
            let total = coefficient * source.text().len();
            let (fresh, bytes) = resident_phase_work(phase, &[&source]).unwrap();
            assert_eq!(bytes, source.text().len());
            assert_eq!((fresh.used(), fresh.limit()), (2, total));
            assert!(resident_phase_work(phase, &[]).is_err());
            assert!(phase_total(phase, usize::MAX / coefficient + 1).is_err());
            for prefix in [0, 11, 150] {
                let mut short = TypeWorkBudget::with_limit(prefix + 1);
                short.charge(prefix).unwrap();
                assert!(size_sources(std::iter::once(&source), phase, &mut short).is_err());
                assert_eq!(short.used(), prefix + 1);
                for _ in 0..2 {
                    let mut exact = TypeWorkBudget::with_limit(prefix + 2);
                    exact.charge(prefix).unwrap();
                    assert_eq!(
                        size_sources(std::iter::once(&source), phase, &mut exact),
                        Ok((total, source.text().len()))
                    );
                    exact.finish_sizing(total).unwrap();
                    assert_eq!((exact.used(), exact.limit()), (prefix + 2, total));
                    exact.charge(exact.remaining()).unwrap();
                    assert!(exact.charge(1).is_err());
                    assert_eq!(
                        phase.assess_with_allowance(total + 1, total).assessment(),
                        WorkAssessment::OutsideAllowance { units: 1 }
                    );
                }
            }
        }
    }

    #[test]
    fn source_gas_is_paid_carried_checked_and_has_no_extra_ten_percent() {
        let source = SourceFile::new("source.ash", "main : Unit -> Int\nmain () = 42\n").unwrap();
        let total = source.text().len() * 800;
        assert!(source_total(usize::MAX / 800 + 1).is_err());
        let mut empty = TypeWorkBudget::with_limit(1);
        assert_eq!(
            size_sources(
                std::iter::empty(),
                CompilationPhase::SourceChecking,
                &mut empty
            ),
            Ok((0, 0))
        );
        assert!(empty.finish_sizing(0).is_err());
        for prefix in [0, 11] {
            let mut short = TypeWorkBudget::with_limit(prefix + 1);
            short.charge(prefix).unwrap();
            assert!(
                size_sources(
                    std::iter::once(&source),
                    CompilationPhase::SourceChecking,
                    &mut short
                )
                .is_err()
            );
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + 2);
                exact.charge(prefix).unwrap();
                assert_eq!(
                    size_sources(
                        std::iter::once(&source),
                        CompilationPhase::SourceChecking,
                        &mut exact
                    ),
                    Ok((total, source.text().len()))
                );
                exact.finish_sizing(total).unwrap();
                assert_eq!((exact.used(), exact.limit()), (prefix + 2, total));
                exact.charge(exact.remaining()).unwrap();
                assert!(exact.charge(1).is_err());
                assert_eq!(
                    CompilationPhase::SourceChecking
                        .assess_with_allowance(total + 1, total)
                        .assessment(),
                    WorkAssessment::OutsideAllowance { units: 1 }
                );
            }
        }
    }

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
