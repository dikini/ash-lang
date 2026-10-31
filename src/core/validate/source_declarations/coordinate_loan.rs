//! Operation-local, source-only coordinate loans. No registry proof is retained.

#[cfg(test)]
use std::collections::HashSet;
use std::{cell::RefCell, collections::HashMap, sync::Arc};

use super::{
    DeclarationCoordinates, ModuleId, SourceFile, SourceId, TypeWorkBudget, ValidationError,
    charge, registry_error, resource,
};

/// Lazy syntax coordinates anchored to a live immutable source arena.
///
/// The reconstruction operation owns this loan. Each consuming validator still
/// authenticates its module relation, registry, binders and complete forest.
/// Nothing in this value records successful semantic authentication.
pub(crate) struct DeclarationCoordinateLoan<'source> {
    anchors: HashMap<ModuleId, &'source SourceFile>,
    coordinates: RefCell<HashMap<(ModuleId, SourceId), Arc<DeclarationCoordinates>>>,
}

impl<'source> DeclarationCoordinateLoan<'source> {
    #[cfg(test)]
    pub(crate) fn new(
        sources: &'source [SourceFile],
        modules: &[ModuleId],
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ValidationError> {
        charge(work, 1)?;
        if sources.len() != modules.len() {
            return Err(registry_error());
        }
        charge(work, sources.len().checked_mul(2).ok_or_else(resource)?)?;
        let mut anchors = HashMap::new();
        let mut source_ids = HashSet::new();
        anchors.try_reserve(sources.len()).map_err(|_| resource())?;
        source_ids
            .try_reserve(sources.len())
            .map_err(|_| resource())?;
        for (module, source) in modules.iter().copied().zip(sources) {
            charge(work, 2)?;
            if anchors.insert(module, source).is_some() || !source_ids.insert(source.id()) {
                return Err(registry_error());
            }
        }
        Ok(Self {
            anchors,
            coordinates: RefCell::new(HashMap::new()),
        })
    }

    /// Borrows complete syntax only, after exact live context correspondence.
    pub(super) fn get(
        &self,
        module: ModuleId,
        source: &SourceFile,
        work: &mut TypeWorkBudget,
    ) -> Result<Arc<DeclarationCoordinates>, ValidationError> {
        self.get_with_factory(module, source, work, |work| {
            DeclarationCoordinates::from_module_source(module, source, work)
        })
    }

    /// The caller may factor a paid source check; only syntax is retained.
    pub(super) fn get_with_factory(
        &self,
        module: ModuleId,
        source: &SourceFile,
        work: &mut TypeWorkBudget,
        make: impl FnOnce(&mut TypeWorkBudget) -> Result<DeclarationCoordinates, ValidationError>,
    ) -> Result<Arc<DeclarationCoordinates>, ValidationError> {
        // Account for anchor lookup, source identity checks and cache lookup.
        charge(work, 3)?;
        let anchored = self.anchors.get(&module).ok_or_else(registry_error)?;
        if anchored.id() != source.id() || !std::ptr::eq(*anchored, source) {
            return Err(registry_error());
        }
        let key = (module, source.id());
        if let Some(coordinates) = self.coordinates.borrow().get(&key) {
            charge(work, 1)?;
            return Ok(Arc::clone(coordinates));
        }
        charge(work, 1)?;
        let coordinates = make(work)?;
        // No failed/partial syntax or unpaid retention becomes a future hit.
        charge(work, 1)?;
        let mut retained = self.coordinates.borrow_mut();
        retained.try_reserve(1).map_err(|_| resource())?;
        let coordinates = Arc::new(coordinates);
        retained.insert(key, Arc::clone(&coordinates));
        Ok(coordinates)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::validate::ValidationReason;

    fn source(name: &str) -> SourceFile {
        SourceFile::new(
            name,
            "type First = One\n| Two(Int)\nnewtype Last = Last(Int)\n",
        )
        .unwrap()
    }

    fn modules(sources: &[SourceFile]) -> Vec<ModuleId> {
        sources
            .iter()
            .map(|source| ModuleId::from(source.id()))
            .collect()
    }

    fn assert_registry<T>(result: Result<T, ValidationError>) {
        assert_eq!(result.err().unwrap().reason(), ValidationReason::Registry);
    }

    fn assert_resource<T>(result: Result<T, ValidationError>) {
        assert_eq!(result.err().unwrap().reason(), ValidationReason::Resource);
    }

    #[test]
    fn coordinate_loan_hits_only_exact_live_source_and_module() {
        let sources = [source("first"), source("second")];
        let modules = modules(&sources);
        let mut work = TypeWorkBudget::default();
        let loan = DeclarationCoordinateLoan::new(&sources, &modules, &mut work).unwrap();
        let first = loan.get(modules[0], &sources[0], &mut work).unwrap();
        let second = loan.get(modules[1], &sources[1], &mut work).unwrap();
        assert!(!Arc::ptr_eq(&first, &second));
        assert!(Arc::ptr_eq(
            &first,
            &loan.get(modules[0], &sources[0], &mut work).unwrap()
        ));
        assert!(Arc::ptr_eq(
            &second,
            &loan.get(modules[1], &sources[1], &mut work).unwrap()
        ));
        assert_eq!(first.nominals.len(), 2);
        assert_eq!(first.constructors.len(), 3);
        let clone = sources[0].clone();
        assert_eq!(clone.id(), sources[0].id());
        let donor = source("donor");
        for (module, source) in [
            (modules[0], &clone),
            (modules[0], &donor),
            (modules[0], &sources[1]),
            (modules[1], &sources[0]),
            (ModuleId::from(donor.id()), &donor),
        ] {
            assert_registry(loan.get(module, source, &mut work));
        }
        assert_eq!(loan.coordinates.borrow().len(), 2);
    }

    #[test]
    fn coordinate_loan_constructor_rejects_duplicate_or_incomplete_associations() {
        let sources = [source("first"), source("second")];
        let ids = modules(&sources);
        assert_registry(DeclarationCoordinateLoan::new(
            &sources,
            &ids[..1],
            &mut TypeWorkBudget::default(),
        ));
        assert_registry(DeclarationCoordinateLoan::new(
            &sources,
            &[ids[0], ids[0]],
            &mut TypeWorkBudget::default(),
        ));
        let clones = [sources[0].clone(), sources[0].clone()];
        assert_registry(DeclarationCoordinateLoan::new(
            &clones,
            &ids,
            &mut TypeWorkBudget::default(),
        ));
        let mut measured = TypeWorkBudget::default();
        DeclarationCoordinateLoan::new(&sources, &ids, &mut measured).unwrap();
        let required = measured.used();
        for prefix in [0, 17] {
            let mut short = TypeWorkBudget::with_limit(prefix + required - 1);
            short.charge(prefix).unwrap();
            assert_resource(DeclarationCoordinateLoan::new(&sources, &ids, &mut short));
            let mut exact = TypeWorkBudget::with_limit(prefix + required);
            exact.charge(prefix).unwrap();
            DeclarationCoordinateLoan::new(&sources, &ids, &mut exact).unwrap();
            assert_eq!(exact.used(), prefix + required);
        }
    }

    #[test]
    fn coordinate_loan_failed_extraction_and_retention_never_publish() {
        let sources = [source("first")];
        let ids = modules(&sources);
        let loan =
            DeclarationCoordinateLoan::new(&sources, &ids, &mut TypeWorkBudget::default()).unwrap();
        let mut extraction = TypeWorkBudget::default();
        DeclarationCoordinates::from_source(&sources[0], &mut extraction).unwrap();
        let syntax_work = extraction.used();
        // Four paid lookup/fresh units precede extraction; one retained-row
        // unit follows it. Refuse independently in extraction and retention.
        for limit in [4 + syntax_work - 1, 4 + syntax_work] {
            let mut short = TypeWorkBudget::with_limit(limit);
            assert_resource(loan.get(ids[0], &sources[0], &mut short));
            assert!(loan.coordinates.borrow().is_empty());
            assert_eq!(short.used(), limit);
        }
        let mut exact = TypeWorkBudget::with_limit(5 + syntax_work);
        loan.get(ids[0], &sources[0], &mut exact).unwrap();
        assert_eq!(exact.used(), 5 + syntax_work);
        assert_eq!(loan.coordinates.borrow().len(), 1);

        let malformed = [SourceFile::new("malformed", "type Value =\n").unwrap()];
        let ids = modules(&malformed);
        let loan = DeclarationCoordinateLoan::new(&malformed, &ids, &mut TypeWorkBudget::default())
            .unwrap();
        for _ in 0..2 {
            assert_registry(loan.get(ids[0], &malformed[0], &mut TypeWorkBudget::default()));
            assert!(loan.coordinates.borrow().is_empty());
        }
    }

    #[test]
    fn coordinate_loan_work_is_cumulative_exact_and_fresh_per_operation() {
        let sources = [source("first")];
        let ids = modules(&sources);
        let operation = |work: &mut TypeWorkBudget| {
            let loan = DeclarationCoordinateLoan::new(&sources, &ids, work)?;
            let first = loan.get(ids[0], &sources[0], work)?;
            let again = loan.get(ids[0], &sources[0], work)?;
            assert!(Arc::ptr_eq(&first, &again));
            Ok::<_, ValidationError>(first)
        };
        let mut measured = TypeWorkBudget::default();
        let first = operation(&mut measured).unwrap();
        let required = measured.used();
        for prefix in [0, 37] {
            let mut short = TypeWorkBudget::with_limit(prefix + required - 1);
            short.charge(prefix).unwrap();
            assert_resource(operation(&mut short));
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + required);
                exact.charge(prefix).unwrap();
                let fresh = operation(&mut exact).unwrap();
                assert!(!Arc::ptr_eq(&first, &fresh));
                assert_eq!(exact.used(), prefix + required);
                assert_resource(operation(&mut exact));
            }
        }
        // A warm hit still requires its paid work; refusal leaves syntax intact.
        let loan =
            DeclarationCoordinateLoan::new(&sources, &ids, &mut TypeWorkBudget::default()).unwrap();
        let warm = loan
            .get(ids[0], &sources[0], &mut TypeWorkBudget::default())
            .unwrap();
        let mut short = TypeWorkBudget::with_limit(3);
        assert_resource(loan.get(ids[0], &sources[0], &mut short));
        let mut exact = TypeWorkBudget::with_limit(4);
        assert!(Arc::ptr_eq(
            &warm,
            &loan.get(ids[0], &sources[0], &mut exact).unwrap()
        ));
        assert_eq!(exact.used(), 4);
    }
}
