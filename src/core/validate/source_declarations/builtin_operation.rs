//! One literal validator operation's completed reserved-source byte coverage.
//! This is not coordinate data or a registry/native/execution certificate.
use super::super::SourceResourceValidationContext;
use super::*;

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
            charge(work, source.text().len())?;
            if source.text() != crate::module::foreign_builtin_source_text() {
                return Err(registry_error());
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
        atomic::{AtomicU64, Ordering},
        Arc,
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
        assert!(proof
            .covers(&registry, loaded.id(), source, &mut work)
            .unwrap());
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
    fn builtin_operation_selective_legacy_projection_does_not_certify_checked_inventory() {
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
        assert!(view
            .effect(EffectId::new(
                loaded.id(),
                crate::module::FOREIGN_NATIVE_HOST_LOCAL
            ))
            .is_some());
        assert!(view
            .scalar_preflights()
            .all(|(_, fact)| fact.role().host_parameter(fact.module()).is_none()));
        let missing_nominals = (0..18)
            .filter(|local| {
                view.nominal(crate::types::NominalTypeId::new(loaded.id(), *local))
                    .is_none()
            })
            .collect::<Vec<_>>();
        eprintln!("SELECTIVE_CHECKING_VIEW missing_nominals={missing_nominals:?} host_present=true legacy_functions_only=true");
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
        assert!(!crate::foreign::checked_builtins::is_canonical_native_host(
            original_host,
            &view,
            &mut full,
        )
        .unwrap());
        let mut fallback = TypeWorkBudget::default();
        assert!(
            !crate::foreign::checked_builtins::is_canonical_native_host_with_preflights(
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
        let error = authenticate_with_builtin_operation(
            &view, &sources, &modules, &mut work, None, &operation, &scalar, &context,
        )
        .expect_err("partial legacy projection cannot certify complete checked source inventory");
        assert_eq!(error.reason(), ValidationReason::Registry);
        let old = authenticate(&view, &sources, &modules, &mut TypeWorkBudget::default())
            .expect_err("the old full path has the same incomplete checked-inventory boundary");
        eprintln!(
            "SELECTIVE_SOURCE_AUTH old={:?} operation={:?}",
            old.reason(),
            error.reason()
        );
        assert_eq!(old.reason(), error.reason());
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
}
