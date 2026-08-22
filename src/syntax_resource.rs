//! Shared accounting for retained syntax work.

/// Maximum cumulative lexer-token, lexical-diagnostic, and parser-event work.
///
/// This is an implementation resource budget, not an Ash source restriction.
/// It bounds retained front-end structures before their allocation.
pub const SYNTAX_WORK_LIMIT: usize = 1_500_000;

/// A non-syntactic implementation resource failure.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ResourceFailure {
    /// Constructing another nested syntax layer would exceed the safe budget.
    StructuralDepth {
        /// The active implementation budget.
        limit: usize,
    },
    /// Retaining another token, lexical diagnostic, or parser event would
    /// exceed the cumulative syntax-work budget.
    SyntaxWork {
        /// The active implementation budget.
        limit: usize,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct SyntaxBudget {
    remaining: usize,
    limit: usize,
}

impl Default for SyntaxBudget {
    fn default() -> Self {
        Self {
            remaining: SYNTAX_WORK_LIMIT,
            limit: SYNTAX_WORK_LIMIT,
        }
    }
}

impl SyntaxBudget {
    pub(crate) fn charge(&mut self) -> Result<(), ResourceFailure> {
        let Some(remaining) = self.remaining.checked_sub(1) else {
            return Err(ResourceFailure::SyntaxWork { limit: self.limit });
        };
        self.remaining = remaining;
        Ok(())
    }

    #[cfg(test)]
    const fn with_limit(limit: usize) -> Self {
        Self {
            remaining: limit,
            limit,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn charge_succeeds_at_the_boundary_and_fails_before_the_next_unit() {
        let mut budget = SyntaxBudget::with_limit(2);

        assert_eq!(budget.charge(), Ok(()));
        assert_eq!(budget.charge(), Ok(()));
        assert_eq!(
            budget.charge(),
            Err(ResourceFailure::SyntaxWork { limit: 2 })
        );
        assert_eq!(
            budget.charge(),
            Err(ResourceFailure::SyntaxWork { limit: 2 })
        );
    }
}
