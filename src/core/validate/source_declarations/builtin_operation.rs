//! One literal validator operation's completed reserved-source byte coverage.
//! This is not coordinate data or a registry/native/execution certificate.
use super::super::SourceResourceValidationContext;
use super::*;

/// A single restore's immutable resident-byte predicate, not registry authority.
/// Borrowing the frozen arena prevents source replacement while it is in use.
pub(crate) struct RestoreBuiltinForeignBytes<'source> {
    sources: HashMap<ModuleId, (&'source SourceFile, Span)>,
}

impl<'source> RestoreBuiltinForeignBytes<'source> {
    pub(crate) fn new(
        sources: &'source [SourceFile],
        modules: &[ModuleId],
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ValidationError> {
        charge(work, 1)?;
        if sources.len() != modules.len() {
            return Err(registry_error());
        }
        let mut records = HashMap::new();
        for (source, module) in sources.iter().zip(modules) {
            charge(work, 1)?;
            if !module.is_builtin_foreign() {
                continue;
            }
            let span = Self::full_span(source, work)?;
            charge(work, source.text().len())?;
            if source.text() != crate::module::foreign_builtin_source_text() {
                return Err(registry_error());
            }
            charge(work, 2)?;
            records.try_reserve(1).map_err(|_| resource())?;
            if records.insert(*module, (source, span)).is_some() {
                return Err(registry_error());
            }
        }
        // No partial or failed byte coverage escapes this constructor.
        charge(work, 1)?;
        Ok(Self { sources: records })
    }

    fn full_span(source: &SourceFile, work: &mut TypeWorkBudget) -> Result<Span, ValidationError> {
        charge(work, 2)?;
        let end = u32::try_from(source.text().len()).map_err(|_| resource())?;
        let range = crate::source::ByteRange::new(0, end).map_err(|_| registry_error())?;
        source.span(range).map_err(|_| registry_error())
    }

    fn covers(
        &self,
        module: ModuleId,
        source: &SourceFile,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ValidationError> {
        charge(work, 4)?;
        let Some((original, span)) = self.sources.get(&module) else {
            return Ok(false);
        };
        if original.id() != source.id()
            || !std::ptr::eq(*original, source)
            || *span != Self::full_span(source, work)?
        {
            return Err(registry_error());
        }
        Ok(true)
    }
}

pub(in crate::core::validate) struct BuiltinForeignSourceAuthentication<'operation, 'source> {
    registry: &'operation ResolvedRegistry,
    sources: &'operation HashMap<SourceId, &'source SourceFile>,
    modules: &'operation HashMap<ModuleId, SourceId>,
    context: &'operation SourceResourceValidationContext,
}
impl<'operation, 'source> BuiltinForeignSourceAuthentication<'operation, 'source> {
    pub(in crate::core::validate) fn new(
        registry: &'operation ResolvedRegistry,
        sources: &'operation HashMap<SourceId, &'source SourceFile>,
        modules: &'operation HashMap<ModuleId, SourceId>,
        context: &'operation SourceResourceValidationContext,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ValidationError> {
        Self::new_with_restore_bytes(registry, sources, modules, context, None, work)
    }

    pub(in crate::core::validate) fn new_with_restore_bytes(
        registry: &'operation ResolvedRegistry,
        sources: &'operation HashMap<SourceId, &'source SourceFile>,
        modules: &'operation HashMap<ModuleId, SourceId>,
        context: &'operation SourceResourceValidationContext,
        restored: Option<&RestoreBuiltinForeignBytes<'_>>,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ValidationError> {
        charge(work, 1)?;
        if !matches!(
            context,
            SourceResourceValidationContext::OriginalTemplate { .. }
        ) {
            return Err(registry_error());
        }
        for (module, id) in modules {
            charge(work, 1)?;
            if !module.is_builtin_foreign() {
                continue;
            }
            let source = *sources.get(id).ok_or_else(registry_error)?;
            charge(work, 1)?;
            if source.id() != *id {
                return Err(registry_error());
            }
            let covered = restored
                .map(|bytes| bytes.covers(*module, source, work))
                .transpose()?
                .unwrap_or(false);
            if !covered {
                charge(work, source.text().len())?;
                if source.text() != crate::module::foreign_builtin_source_text() {
                    return Err(registry_error());
                }
            }
        }
        // Publication occurs only after complete successful coverage. Retains
        // are paid; immutable references keep literal identities alive.
        charge(work, 1)?;
        Ok(Self {
            registry,
            sources,
            modules,
            context,
        })
    }
    pub(in crate::core::validate) fn context_matches(
        &self,
        registry: &ResolvedRegistry,
        sources: &HashMap<SourceId, &SourceFile>,
        modules: &HashMap<ModuleId, SourceId>,
        context: &SourceResourceValidationContext,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        charge(work, 4)?;
        if !std::ptr::eq(self.registry, registry)
            || !std::ptr::eq(self.sources, sources)
            || !std::ptr::eq(self.modules, modules)
            || !std::ptr::eq(self.context, context)
        {
            return Err(registry_error());
        }
        Ok(())
    }
    pub(in crate::core::validate) fn covers(
        &self,
        registry: &ResolvedRegistry,
        module: ModuleId,
        source: &SourceFile,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ValidationError> {
        charge(work, 4)?;
        if !std::ptr::eq(self.registry, registry) {
            return Err(registry_error());
        }
        if !module.is_builtin_foreign() {
            return Ok(false);
        }
        let id = self.modules.get(&module).ok_or_else(registry_error)?;
        let admitted = *self.sources.get(id).ok_or_else(registry_error)?;
        if *id != source.id() || !std::ptr::eq(admitted, source) {
            return Err(registry_error());
        }
        Ok(true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    };
    static IDS: AtomicU64 = AtomicU64::new(0);
    fn graph() -> crate::module::ModuleGraph {
        graph_with_source("import @builtin.foreign as Foreign\nmain : Unit -> Int\nmain () = 42\n")
    }
    fn graph_with_source(text: &str) -> crate::module::ModuleGraph {
        struct Owned(std::path::PathBuf);
        impl Drop for Owned {
            fn drop(&mut self) {
                let _ = std::fs::remove_dir_all(&self.0);
            }
        }
        let owned = loop {
            let p = std::env::temp_dir().join(format!(
                "ash-builtin-operation-{}-{}",
                std::process::id(),
                IDS.fetch_add(1, Ordering::Relaxed)
            ));
            match std::fs::create_dir(&p) {
                Ok(()) => break Owned(p),
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => panic!("owned test directory: {e}"),
            }
        };
        let entry = owned.0.join("entry.ash");
        std::fs::write(&entry, text).unwrap();
        crate::module::load_module_graph(&entry, &crate::module::ModuleRoots::empty()).unwrap()
    }
    fn context(module: ModuleId) -> SourceResourceValidationContext {
        SourceResourceValidationContext::OriginalTemplate {
            resource: ResourceDefinitionId::new(module, 0),
            answer: false,
        }
    }
    fn registry_error<T>(r: Result<T, ValidationError>) {
        assert_eq!(r.err().unwrap().reason(), ValidationReason::Registry);
    }

    #[test]
    fn builtin_operation_requires_literal_registry_source_relation_and_context() {
        let graph = graph();
        let loaded = graph
            .modules()
            .iter()
            .find(|m| m.id().is_builtin_foreign())
            .unwrap();
        let resolved = crate::resolve::resolve_module(loaded, &[]).unwrap();
        let registry = Arc::clone(resolved.registry());
        let source = loaded.source();
        let sources = HashMap::from([(source.id(), source)]);
        let modules = HashMap::from([(loaded.id(), source.id())]);
        let context = context(loaded.id());
        let mut work = TypeWorkBudget::default();
        let proof = BuiltinForeignSourceAuthentication::new(
            &registry, &sources, &modules, &context, &mut work,
        )
        .unwrap();
        proof
            .context_matches(&registry, &sources, &modules, &context, &mut work)
            .unwrap();
        assert!(
            proof
                .covers(&registry, loaded.id(), source, &mut work)
                .unwrap()
        );
        let clone = source.clone();
        let donor = SourceFile::new("donor", source.text()).unwrap();
        registry_error(proof.covers(&registry, loaded.id(), &clone, &mut work));
        registry_error(proof.covers(&registry, loaded.id(), &donor, &mut work));
        let equal_registry = registry.as_ref().clone();
        registry_error(proof.covers(&equal_registry, loaded.id(), source, &mut work));
        let equal_modules = modules.clone();
        registry_error(proof.context_matches(
            &registry,
            &sources,
            &equal_modules,
            &context,
            &mut work,
        ));
        let other_context = context;
        registry_error(proof.context_matches(
            &registry,
            &sources,
            &modules,
            &other_context,
            &mut work,
        ));
        let other_module = ModuleId::builtin_foreign_for_test(u32::MAX);
        registry_error(proof.covers(&registry, other_module, source, &mut work));
    }

    #[test]
    fn builtin_operation_unused_reserved_module_is_bytes_only_and_malformed_mint_fails() {
        let module = ModuleId::builtin_foreign_for_test(77);
        let canonical =
            SourceFile::new("unused", crate::module::foreign_builtin_source_text()).unwrap();
        let empty = ResolvedRegistry::default();
        let sources = HashMap::from([(canonical.id(), &canonical)]);
        let modules = HashMap::from([(module, canonical.id())]);
        let context = context(module);
        let mut work = TypeWorkBudget::default();
        let proof = BuiltinForeignSourceAuthentication::new(
            &empty, &sources, &modules, &context, &mut work,
        )
        .unwrap();
        assert!(proof.covers(&empty, module, &canonical, &mut work).unwrap());
        let bad = SourceFile::new("wrong reserved source", "type Other = Other\n").unwrap();
        let bad_sources = HashMap::from([(bad.id(), &bad)]);
        let bad_modules = HashMap::from([(module, bad.id())]);
        registry_error(BuiltinForeignSourceAuthentication::new(
            &empty,
            &bad_sources,
            &bad_modules,
            &context,
            &mut work,
        ));
        // No failed or partial operation survives. A fresh canonical retry works.
        BuiltinForeignSourceAuthentication::new(&empty, &sources, &modules, &context, &mut work)
            .unwrap();
        registry_error(BuiltinForeignSourceAuthentication::new(
            &empty,
            &sources,
            &modules,
            &SourceResourceValidationContext::FinalProgram,
            &mut work,
        ));
    }

    #[test]
    fn builtin_operation_mint_and_consumption_have_same_meter_exact_short_spent_fresh_limits() {
        let module = ModuleId::builtin_foreign_for_test(77);
        let source =
            SourceFile::new("builtin", crate::module::foreign_builtin_source_text()).unwrap();
        let registry = ResolvedRegistry::default();
        let sources = HashMap::from([(source.id(), &source)]);
        let modules = HashMap::from([(module, source.id())]);
        let context = context(module);
        let run = |work: &mut TypeWorkBudget| {
            let proof = BuiltinForeignSourceAuthentication::new(
                &registry, &sources, &modules, &context, work,
            )?;
            proof.context_matches(&registry, &sources, &modules, &context, work)?;
            assert!(proof.covers(&registry, module, &source, work)?);
            Ok::<_, ValidationError>(())
        };
        let mut measured = TypeWorkBudget::default();
        run(&mut measured).unwrap();
        let cost = measured.used();
        for prefix in [0, 7] {
            let mut exact = TypeWorkBudget::with_limit(prefix + cost);
            exact.charge(prefix).unwrap();
            run(&mut exact).unwrap();
            assert_eq!(exact.used(), prefix + cost);
            assert_eq!(
                run(&mut exact).unwrap_err().reason(),
                ValidationReason::Resource
            );
            let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
            short.charge(prefix).unwrap();
            assert_eq!(
                run(&mut short).unwrap_err().reason(),
                ValidationReason::Resource
            );
        }
        for _ in 0..2 {
            run(&mut TypeWorkBudget::with_limit(cost)).unwrap();
        }
        // One-short factory completion must not mint a usable receipt.
        let mut mint = TypeWorkBudget::default();
        BuiltinForeignSourceAuthentication::new(&registry, &sources, &modules, &context, &mut mint)
            .unwrap();
        assert_eq!(
            BuiltinForeignSourceAuthentication::new(
                &registry,
                &sources,
                &modules,
                &context,
                &mut TypeWorkBudget::with_limit(mint.used() - 1)
            )
            .err()
            .unwrap()
            .reason(),
            ValidationReason::Resource
        );
    }

    #[test]
    fn builtin_operation_completed_scalar_inventory_still_authenticates_each_host_and_projection() {
        let graph = graph();
        let loaded = graph
            .modules()
            .iter()
            .find(|m| m.id().is_builtin_foreign())
            .unwrap();
        let resolved = crate::resolve::resolve_module(loaded, &[]).unwrap();
        let registry = Arc::clone(resolved.registry());
        let mut work = TypeWorkBudget::default();
        let scalar = registry
            .authenticate_scalar_preflights_for_owners(&mut work)
            .unwrap();
        let host = registry
            .effects()
            .iter()
            .find(|e| e.id.module() == loaded.id())
            .unwrap();
        assert!(
            crate::foreign::checked_builtins::is_canonical_native_host_with_preflights(
                host, &registry, &scalar, &mut work
            )
            .unwrap()
        );
        let mut wrong = host.clone();
        wrong.parameters[0].kind = Kind::EffectRow;
        assert!(
            !crate::foreign::checked_builtins::is_canonical_native_host_with_preflights(
                &wrong, &registry, &scalar, &mut work
            )
            .unwrap()
        );
        let clone = registry.as_ref().clone();
        assert!(
            !crate::foreign::checked_builtins::is_canonical_native_host_with_preflights(
                host, &clone, &scalar, &mut work
            )
            .unwrap()
        );
        // Empty tables cannot supply checked inventory; full fallback refuses absent roles.
        let empty = ResolvedRegistry::default();
        let empty_scalar = empty
            .authenticate_scalar_preflights_for_owners(&mut work)
            .unwrap();
        assert!(
            !crate::foreign::checked_builtins::is_canonical_native_host_with_preflights(
                host,
                &empty,
                &empty_scalar,
                &mut work
            )
            .unwrap()
        );
    }
    #[test]
    fn builtin_operation_selective_legacy_projection_retains_complete_host_checking_inventory() {
        let graph = graph_with_source(
            "import @builtin.foreign (checked_i64 as signed)\nmain : Unit -> Int\nmain () = 42\n",
        );
        let loaded = graph
            .modules()
            .iter()
            .find(|m| m.id().is_builtin_foreign())
            .unwrap();
        let builtin =
            crate::elaborate::check_module(crate::resolve::resolve_module(loaded, &[]).unwrap())
                .unwrap();
        let entry = graph
            .modules()
            .iter()
            .find(|m| !m.id().is_builtin_foreign())
            .unwrap();
        let dependencies = entry
            .dependencies()
            .iter()
            .map(|edge| crate::resolve::DependencyExports::new(edge, builtin.exports()).unwrap())
            .collect::<Vec<_>>();
        let resolved = crate::resolve::resolve_module(entry, &dependencies).unwrap();
        let mut work = TypeWorkBudget::default();
        let view = resolved
            .registry()
            .source_original_checker_view(resolved.imported_facts(), &mut work)
            .unwrap();
        crate::elaborate::check_module(resolved).expect("the actual selective legacy entry checks");
        assert!(
            view.effect(EffectId::new(
                loaded.id(),
                crate::module::FOREIGN_NATIVE_HOST_LOCAL
            ))
            .is_some()
        );
        assert!(
            view.scalar_preflights()
                .all(|(_, fact)| fact.role().host_parameter(fact.module()).is_none())
        );
        for (id, coordinates, family) in
            crate::foreign::scalar_preflight::checked_inventory_dependencies(loaded.id())
        {
            if family {
                let fact = view.nominal(id).expect("retained Host checking family");
                assert_eq!(
                    view.nominal_parameters(id).unwrap().len(),
                    coordinates.formals().len()
                );
                assert_eq!(fact.constructors.len(), coordinates.constructors().len());
            } else {
                assert!(
                    view.nominal(id).is_none(),
                    "opaque checking kind is not materialized"
                );
                assert!(view.nominal_kind(id).is_some());
            }
        }
        let scalar = view
            .authenticate_scalar_preflights_for_owners(&mut work)
            .unwrap();
        let original_host = builtin
            .registry()
            .effect(EffectId::new(
                loaded.id(),
                crate::module::FOREIGN_NATIVE_HOST_LOCAL,
            ))
            .unwrap();
        let mut full = TypeWorkBudget::default();
        assert!(
            crate::foreign::checked_builtins::is_canonical_native_host(
                original_host,
                &view,
                &mut full,
            )
            .unwrap()
        );
        let mut fallback = TypeWorkBudget::default();
        assert!(
            crate::foreign::checked_builtins::is_canonical_native_host_with_preflights(
                original_host,
                &view,
                &scalar,
                &mut fallback
            )
            .unwrap()
        );
        assert!(fallback.used() >= full.used());
        let sources = graph
            .modules()
            .iter()
            .map(|m| (m.source().id(), m.source()))
            .collect::<HashMap<_, _>>();
        let modules = graph
            .modules()
            .iter()
            .map(|m| (m.id(), m.source().id()))
            .collect::<HashMap<_, _>>();
        let context = context(entry.id());
        let operation =
            BuiltinForeignSourceAuthentication::new(&view, &sources, &modules, &context, &mut work)
                .unwrap();
        authenticate_with_builtin_operation(
            &view, &sources, &modules, &mut work, None, &operation, &scalar, &context,
        )
        .expect("actual retained Host has complete checking metadata in the operation path");
        authenticate(&view, &sources, &modules, &mut TypeWorkBudget::default())
            .expect("standalone source authentication accepts the same complete projection");
    }

    #[test]
    fn builtin_operation_selective_legacy_entry_links_and_revalidates_independent_core() {
        struct Owned(std::path::PathBuf);
        impl Drop for Owned {
            fn drop(&mut self) {
                let _ = std::fs::remove_dir_all(&self.0);
            }
        }
        let directory = loop {
            let candidate = std::env::temp_dir().join(format!(
                "ash-selective-linked-{}-{}",
                std::process::id(),
                IDS.fetch_add(1, Ordering::Relaxed)
            ));
            match std::fs::create_dir(&candidate) {
                Ok(()) => break Owned(candidate),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("owned selective entry: {error}"),
            }
        };
        let entry = directory.0.join("entry.ash");
        std::fs::write(
            &entry,
            "import @builtin.foreign (checked_i64 as signed)\nmain : Unit -> Int\nmain () = 42\n",
        )
        .unwrap();
        let compiled = crate::driver::compile_path(crate::driver::RunConfiguration {
            entry,
            roots: crate::module::ModuleRoots::empty(),
        })
        .expect("real selective legacy entry compiles and links");
        if let Some((program, provenance)) = compiled.effect_build_input() {
            let sources = provenance
                .iter()
                .map(|(_, source)| source.as_ref())
                .collect::<Vec<_>>();
            let modules = provenance
                .iter()
                .map(|(module, source)| (*module, source.id()))
                .collect::<Vec<_>>();
            crate::core::validate_effect_modules(
                crate::core::transform::identity_effect_traversal(program).unwrap(),
                &sources,
                &modules,
            )
            .expect("independent linked effect Core accepts selective legacy entry");
            eprintln!("SELECTIVE_LINKED_CORE dialect=effect accepted");
        } else {
            let (program, provenance) = compiled
                .pure_build_input()
                .expect("driver selected one static Core dialect");
            let sources = provenance
                .iter()
                .map(|(_, source)| source.as_ref())
                .collect::<Vec<_>>();
            let modules = provenance
                .iter()
                .map(|(module, source)| (*module, source.id()))
                .collect::<Vec<_>>();
            crate::core::validate_modules(
                crate::core::transform::identity_traversal(program).unwrap(),
                &sources,
                &modules,
            )
            .expect("independent linked pure Core accepts selective legacy entry");
            eprintln!("SELECTIVE_LINKED_CORE dialect=pure accepted");
        }
    }

    #[test]
    fn builtin_operation_warm_syntax_loan_does_not_skip_fresh_byte_admission() {
        let module = ModuleId::builtin_foreign_for_test(77);
        let arena =
            [SourceFile::new("builtin", crate::module::foreign_builtin_source_text()).unwrap()];
        let loan =
            DeclarationCoordinateLoan::new(&arena, &[module], &mut TypeWorkBudget::default())
                .unwrap();
        let source = &arena[0];
        let registry = ResolvedRegistry::default();
        let sources = HashMap::from([(source.id(), source)]);
        let modules = HashMap::from([(module, source.id())]);
        let context = context(module);
        let mut first = None;
        let mut mint_cost = None;
        for _ in 0..2 {
            let mut work = TypeWorkBudget::default();
            let operation = BuiltinForeignSourceAuthentication::new(
                &registry, &sources, &modules, &context, &mut work,
            )
            .unwrap();
            assert!(
                work.used() >= source.text().len(),
                "fresh bytes paid even if syntax is warm"
            );
            if let Some(cost) = mint_cost {
                assert_eq!(work.used(), cost);
            } else {
                mint_cost = Some(work.used());
            }
            let coordinates = loan
                .get_with_factory(module, source, &mut work, |work| {
                    DeclarationCoordinates::from_module_source_with_byte_proof(
                        module,
                        source,
                        work,
                        Some((&operation, &registry)),
                    )
                })
                .unwrap();
            if let Some(previous) = &first {
                assert!(Arc::ptr_eq(previous, &coordinates));
            } else {
                first = Some(coordinates);
            }
        }
    }

    #[test]
    fn restore_bytes_keep_nested_proofs_fresh_and_exactly_source_bound() {
        let module = ModuleId::builtin_foreign_for_test(77);
        let arena = [
            SourceFile::new("root builtin", crate::module::foreign_builtin_source_text()).unwrap(),
        ];
        let witness =
            RestoreBuiltinForeignBytes::new(&arena, &[module], &mut TypeWorkBudget::default())
                .unwrap();
        let source = &arena[0];
        let sources = HashMap::from([(source.id(), source)]);
        let modules = HashMap::from([(module, source.id())]);
        let first_registry = ResolvedRegistry::default();
        let second_registry = ResolvedRegistry::default();
        let first_context = context(module);
        let second_context = SourceResourceValidationContext::OriginalTemplate {
            resource: ResourceDefinitionId::new(module, 1),
            answer: true,
        };
        let mut first = TypeWorkBudget::default();
        let first_proof = BuiltinForeignSourceAuthentication::new_with_restore_bytes(
            &first_registry,
            &sources,
            &modules,
            &first_context,
            Some(&witness),
            &mut first,
        )
        .unwrap();
        let mut second = TypeWorkBudget::default();
        let second_proof = BuiltinForeignSourceAuthentication::new_with_restore_bytes(
            &second_registry,
            &sources,
            &modules,
            &second_context,
            Some(&witness),
            &mut second,
        )
        .unwrap();
        assert_eq!(first.used(), second.used());
        assert!(
            first.used() < source.text().len(),
            "only exact root bytes receive a discount"
        );
        first_proof
            .context_matches(
                &first_registry,
                &sources,
                &modules,
                &first_context,
                &mut TypeWorkBudget::default(),
            )
            .unwrap();
        second_proof
            .context_matches(
                &second_registry,
                &sources,
                &modules,
                &second_context,
                &mut TypeWorkBudget::default(),
            )
            .unwrap();
        registry_error(first_proof.context_matches(
            &second_registry,
            &sources,
            &modules,
            &second_context,
            &mut TypeWorkBudget::default(),
        ));
        registry_error(second_proof.covers(
            &first_registry,
            module,
            source,
            &mut TypeWorkBudget::default(),
        ));

        let clone = source.clone();
        let clones = HashMap::from([(clone.id(), &clone)]);
        registry_error(BuiltinForeignSourceAuthentication::new_with_restore_bytes(
            &first_registry,
            &clones,
            &modules,
            &first_context,
            Some(&witness),
            &mut TypeWorkBudget::default(),
        ));
        let donor_module = ModuleId::builtin_foreign_for_test(78);
        let donor_modules = HashMap::from([(donor_module, source.id())]);
        let mut fallback = TypeWorkBudget::default();
        BuiltinForeignSourceAuthentication::new_with_restore_bytes(
            &first_registry,
            &sources,
            &donor_modules,
            &first_context,
            Some(&witness),
            &mut fallback,
        )
        .unwrap();
        assert!(
            fallback.used() >= source.text().len(),
            "uncovered exact module pays full bytes"
        );
        // A corrupted private record cannot serve even this same source object.
        let mut wrong_span =
            RestoreBuiltinForeignBytes::new(&arena, &[module], &mut TypeWorkBudget::default())
                .unwrap();
        wrong_span.sources.get_mut(&module).unwrap().1 = source
            .span(crate::source::ByteRange::new(0, 0).unwrap())
            .unwrap();
        registry_error(BuiltinForeignSourceAuthentication::new_with_restore_bytes(
            &first_registry,
            &sources,
            &modules,
            &first_context,
            Some(&wrong_span),
            &mut TypeWorkBudget::default(),
        ));
        BuiltinForeignSourceAuthentication::new_with_restore_bytes(
            &first_registry,
            &sources,
            &modules,
            &first_context,
            Some(&witness),
            &mut TypeWorkBudget::default(),
        )
        .unwrap();
    }

    #[test]
    fn restore_bytes_cover_unused_reserved_sources_and_failed_mint_never_escapes() {
        let module = ModuleId::builtin_foreign_for_test(77);
        let unused = ModuleId::builtin_foreign_for_test(78);
        let arena = [
            SourceFile::new("root builtin", crate::module::foreign_builtin_source_text()).unwrap(),
        ];
        let witness =
            RestoreBuiltinForeignBytes::new(&arena, &[module], &mut TypeWorkBudget::default())
                .unwrap();
        let bad = SourceFile::new("unused bad builtin", "type Other = Other\n").unwrap();
        let sources = HashMap::from([(arena[0].id(), &arena[0]), (bad.id(), &bad)]);
        let modules = HashMap::from([(module, arena[0].id()), (unused, bad.id())]);
        // A successful covered root does not erase an extra nested module.
        registry_error(BuiltinForeignSourceAuthentication::new_with_restore_bytes(
            &ResolvedRegistry::default(),
            &sources,
            &modules,
            &context(module),
            Some(&witness),
            &mut TypeWorkBudget::default(),
        ));
        let bad_arena = [arena[0].clone(), bad];
        for _ in 0..2 {
            registry_error(RestoreBuiltinForeignBytes::new(
                &bad_arena,
                &[module, unused],
                &mut TypeWorkBudget::default(),
            ));
        }
        RestoreBuiltinForeignBytes::new(&arena, &[module], &mut TypeWorkBudget::default()).unwrap();
        BuiltinForeignSourceAuthentication::new_with_restore_bytes(
            &ResolvedRegistry::default(),
            &HashMap::new(),
            &HashMap::new(),
            &SourceResourceValidationContext::FinalProgram,
            Some(&witness),
            &mut TypeWorkBudget::default(),
        )
        .err()
        .map(|error| assert_eq!(error.reason(), ValidationReason::Registry))
        .expect("context still checked");
    }

    #[test]
    fn restore_bytes_never_certify_a_new_registrys_host_or_source_projection() {
        let graph = graph();
        let loaded = graph
            .modules()
            .iter()
            .find(|m| m.id().is_builtin_foreign())
            .unwrap();
        let resolved = crate::resolve::resolve_module(loaded, &[]).unwrap();
        let registry = resolved.registry();
        let arena = [loaded.source().clone()];
        let witness =
            RestoreBuiltinForeignBytes::new(&arena, &[loaded.id()], &mut TypeWorkBudget::default())
                .unwrap();
        let sources = HashMap::from([(arena[0].id(), &arena[0])]);
        let modules = HashMap::from([(loaded.id(), arena[0].id())]);
        let current = context(loaded.id());
        let mut work = TypeWorkBudget::default();
        let operation = BuiltinForeignSourceAuthentication::new_with_restore_bytes(
            registry,
            &sources,
            &modules,
            &current,
            Some(&witness),
            &mut work,
        )
        .unwrap();
        let scalar = registry
            .authenticate_scalar_preflights_for_owners(&mut work)
            .unwrap();
        authenticate_with_builtin_operation(
            registry, &sources, &modules, &mut work, None, &operation, &scalar, &current,
        )
        .expect("genuine complete source and registry first");
        let mut effects = registry.effects().to_vec();
        effects
            .iter_mut()
            .find(|effect| {
                effect.id == EffectId::new(loaded.id(), crate::module::FOREIGN_NATIVE_HOST_LOCAL)
            })
            .unwrap()
            .public = false;
        let changed = registry
            .as_ref()
            .clone()
            .replace_effects_for_core_test(effects);
        let another = SourceResourceValidationContext::OriginalTemplate {
            resource: ResourceDefinitionId::new(loaded.id(), 1),
            answer: true,
        };
        // Bytes remain genuine. The NEW semantic operation must still refuse
        // the changed Host projection, not borrow the first registry's proof.
        BuiltinForeignSourceAuthentication::new_with_restore_bytes(
            &changed,
            &sources,
            &modules,
            &another,
            Some(&witness),
            &mut TypeWorkBudget::default(),
        )
        .unwrap();
        assert!(matches!(
            changed.authenticate_scalar_preflights_for_owners(&mut TypeWorkBudget::default()),
            Err(crate::resolved::ResolvedBuildFailure::InvalidState)
        ));
        let fresh_operation = BuiltinForeignSourceAuthentication::new_with_restore_bytes(
            registry,
            &sources,
            &modules,
            &another,
            Some(&witness),
            &mut work,
        )
        .unwrap();
        let fresh_scalar = registry
            .authenticate_scalar_preflights_for_owners(&mut work)
            .unwrap();
        authenticate_with_builtin_operation(
            registry,
            &sources,
            &modules,
            &mut work,
            None,
            &fresh_operation,
            &fresh_scalar,
            &another,
        )
        .unwrap();
    }

    #[test]
    fn restore_bytes_root_and_nested_work_is_exact_prefix_short_spent_and_fresh() {
        let module = ModuleId::builtin_foreign_for_test(77);
        let arena = [
            SourceFile::new("root builtin", crate::module::foreign_builtin_source_text()).unwrap(),
        ];
        let sources = HashMap::from([(arena[0].id(), &arena[0])]);
        let modules = HashMap::from([(module, arena[0].id())]);
        let registry = ResolvedRegistry::default();
        let first_context = context(module);
        let second_context = SourceResourceValidationContext::OriginalTemplate {
            resource: ResourceDefinitionId::new(module, 1),
            answer: true,
        };
        let run = |work: &mut TypeWorkBudget| {
            let witness = RestoreBuiltinForeignBytes::new(&arena, &[module], work)?;
            for current in [&first_context, &second_context] {
                let proof = BuiltinForeignSourceAuthentication::new_with_restore_bytes(
                    &registry,
                    &sources,
                    &modules,
                    current,
                    Some(&witness),
                    work,
                )?;
                proof.context_matches(&registry, &sources, &modules, current, work)?;
                assert!(proof.covers(&registry, module, &arena[0], work)?);
            }
            Ok::<_, ValidationError>(())
        };
        let mut measured = TypeWorkBudget::default();
        run(&mut measured).unwrap();
        let cost = measured.used();
        assert!(
            cost >= arena[0].text().len(),
            "every fresh restore pays its own root bytes"
        );
        for prefix in [0, 7] {
            let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
            short.charge(prefix).unwrap();
            assert_eq!(
                run(&mut short).unwrap_err().reason(),
                ValidationReason::Resource
            );
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                exact.charge(prefix).unwrap();
                run(&mut exact).unwrap();
                assert_eq!(exact.used(), prefix + cost);
                assert_eq!(
                    run(&mut exact).unwrap_err().reason(),
                    ValidationReason::Resource
                );
            }
        }
    }
}
