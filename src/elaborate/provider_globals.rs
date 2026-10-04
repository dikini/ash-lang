//! Unpublished Core ABI projections of completed checked global facts.
//!
//! This catalog does not admit occurrences or authenticate a template entry.

use super::{
    BinderId, CheckedImplementationFact, CheckedInterfaceFact, CheckedModule, ConstrainedScheme,
    CoreElaborator, CoreLoweringFamily, EvidenceLowering, HashMap, InterfaceId,
    LoweredImplementationMethod, LoweredInterface, LoweredInterfaceMethod, LoweredScheme,
    MethodEvidenceOwner, Origin, OriginOwner, TypeError, TypeWorkBudget, clone_kind_with_budget,
    constraint_resource, discard_origin_iteratively, invalid_state, resolved_build_error,
    same_kinded_type_parameters_with_budget, same_type_with_budget, type_resource,
};
#[cfg(test)]
use super::{
    CheckedRequirement, EffectElaborator, ElaborationFailure, GeneratedReason,
    InterfaceApplication, IterativeTypeOwner, MethodId, RequirementId, ResolvedModule, Type,
    TypeVariableId, check_module, link_modules,
};
use crate::{
    interface::MatchedNominalIdentities,
    resolved::{
        ImportedFacts, same_checked_interface_fact_observing_nominals_with_budget,
        same_origin_with_budget,
    },
};

#[derive(Debug)]
pub(crate) struct ProviderExternalGlobals {
    rows: Box<[ProviderExternalGlobal]>,
    positions: HashMap<BinderId, usize>,
}

#[derive(Debug)]
pub(crate) struct ProviderExternalGlobal {
    binder: BinderId,
    scheme: ConstrainedScheme,
    origin: Origin,
    capture: crate::core::capture::CaptureValueSummary,
    lowered: LoweredScheme,
}

impl ProviderExternalGlobals {
    pub(crate) fn rows(&self) -> &[ProviderExternalGlobal] {
        &self.rows
    }
    pub(crate) fn global(&self, binder: BinderId) -> Option<&ProviderExternalGlobal> {
        self.rows.get(*self.positions.get(&binder)?)
    }
}

impl ProviderExternalGlobal {
    pub(crate) fn binder(&self) -> BinderId {
        self.binder
    }
    pub(crate) fn scheme(&self) -> &ConstrainedScheme {
        &self.scheme
    }
    pub(crate) fn origin(&self) -> &Origin {
        &self.origin
    }
    pub(crate) fn capture(&self) -> &crate::core::capture::CaptureValueSummary {
        &self.capture
    }
    pub(super) fn lowered(&self) -> &LoweredScheme {
        &self.lowered
    }
}

impl Drop for ProviderExternalGlobal {
    fn drop(&mut self) {
        let span = self.origin.primary_span();
        discard_origin_iteratively(std::mem::replace(&mut self.origin, Origin::Source(span)));
    }
}

impl<F: CoreLoweringFamily> CoreElaborator<F> {
    pub(super) fn prepare_provider_external_globals(
        &mut self,
        checked: &CheckedModule,
        imported: &ImportedFacts,
    ) -> Result<ProviderExternalGlobals, TypeError> {
        self.prepare_provider_completed_globals(
            checked.schemes(),
            checked.interface_facts(),
            imported,
        )
    }

    fn prepare_provider_completed_globals(
        &mut self,
        globals: &[super::CheckedGlobalScheme],
        interfaces: &[CheckedInterfaceFact],
        imported: &ImportedFacts,
    ) -> Result<ProviderExternalGlobals, TypeError> {
        let mut lowering = EvidenceLowering {
            lexical_binders: HashMap::new(),
            interfaces: HashMap::new(),
            interface_methods: HashMap::new(),
            global_schemes: HashMap::new(),
            implementation_methods: HashMap::new(),
            active_binders: HashMap::new(),
        };
        let mut admitted_interfaces: HashMap<InterfaceId, &CheckedInterfaceFact> = HashMap::new();
        for fact in imported
            .interface_imports()
            .map(|imported| &imported.fact)
            .chain(interfaces)
        {
            self.type_work.charge(1).map_err(|()| type_resource())?;
            if let Some(previous) = admitted_interfaces.get(&fact.id) {
                if !same_checked_interface_fact_observing_nominals_with_budget(
                    previous,
                    fact,
                    &mut self.type_work,
                    &mut self.constraint_work,
                    &mut MatchedNominalIdentities::default(),
                )
                .map_err(resolved_build_error)?
                {
                    return Err(invalid_state());
                }
                continue;
            }
            self.type_work.charge(1).map_err(|()| type_resource())?;
            admitted_interfaces
                .try_reserve(1)
                .map_err(|_| type_resource())?;
            self.retain_provider_interface(&mut lowering, fact)?;
            admitted_interfaces.insert(fact.id, fact);
        }

        let mut rows: Vec<ProviderExternalGlobal> = Vec::new();
        let mut positions = HashMap::new();
        let imported_globals = imported.globals().map(|fact| GlobalSource {
            binder: fact.binder,
            scheme: &fact.scheme,
            origin: &fact.origin,
            capture: &fact.capture,
        });
        let local_globals = globals.iter().map(|fact| GlobalSource {
            binder: fact.binder,
            scheme: &fact.scheme,
            origin: &fact.origin,
            capture: &fact.capture,
        });
        for source in imported_globals.chain(local_globals) {
            self.type_work.charge(1).map_err(|()| type_resource())?;
            if let Some(position) = positions.get(&source.binder) {
                if !same_global_source(&rows[*position], &source, &mut self.type_work)? {
                    return Err(invalid_state());
                }
                continue;
            }
            // Reserve both immutable-row and lookup carriers before copying
            // any recursive metadata. No catalog escapes on partial failure.
            self.type_work.charge(2).map_err(|()| type_resource())?;
            rows.try_reserve(1).map_err(|_| type_resource())?;
            positions.try_reserve(1).map_err(|_| type_resource())?;
            for requirement in &source.scheme.requirements {
                charge_origin_clone(&requirement.origin, &mut self.type_work)?;
            }
            let scheme = source
                .scheme
                .clone_with_budget(&mut self.type_work)
                .map_err(|()| type_resource())?;
            charge_origin_clone(source.origin, &mut self.type_work)?;
            let origin = OriginOwner::new(source.origin.clone());
            let capture = source
                .capture
                .clone_with_budget(&mut self.type_work)
                .map_err(|()| type_resource())?;
            let lowered = self.lower_constrained_scheme(
                &scheme,
                &lowering,
                MethodEvidenceOwner::Global(source.binder),
                false,
                origin.as_ref().primary_span(),
            )?;
            positions.insert(source.binder, rows.len());
            rows.push(ProviderExternalGlobal {
                binder: source.binder,
                scheme,
                origin: origin.into_inner(),
                capture,
                lowered,
            });
        }
        Ok(ProviderExternalGlobals {
            rows: rows.into_boxed_slice(),
            positions,
        })
    }

    pub(super) fn prepare_provider_defining_facts(
        &mut self,
        globals: &[super::CheckedGlobalScheme],
        interfaces: &[CheckedInterfaceFact],
        implementations: &[CheckedImplementationFact],
        imported: &ImportedFacts,
        constraint_work: &mut super::InterfaceConstraintBudget,
    ) -> Result<crate::resolved::ProviderDefiningFacts, TypeError> {
        let _ = imported;
        self.type_work
            .charge(globals.len().checked_mul(2).ok_or_else(type_resource)?)
            .map_err(|()| type_resource())?;
        let mut retained_globals = Vec::new();
        let mut positions = HashMap::new();
        retained_globals
            .try_reserve_exact(globals.len())
            .map_err(|_| type_resource())?;
        positions
            .try_reserve(globals.len())
            .map_err(|_| type_resource())?;
        for global in globals {
            for requirement in &global.scheme.requirements {
                charge_origin_clone(&requirement.origin, &mut self.type_work)?;
            }
            let scheme = global
                .scheme
                .clone_with_budget(&mut self.type_work)
                .map_err(|()| type_resource())?;
            let origin = crate::core::provider::RetainedHandlerOrigin::copy(
                &global.origin,
                &mut self.type_work,
            )
            .map_err(|failure| {
                if failure.reason() == crate::core::ValidationReason::Resource {
                    type_resource()
                } else {
                    invalid_state()
                }
            })?;
            let capture = global
                .capture
                .clone_with_budget(&mut self.type_work)
                .map_err(|()| type_resource())?;
            if positions
                .insert(global.binder, retained_globals.len())
                .is_some()
            {
                return Err(invalid_state());
            }
            retained_globals.push(crate::resolved::ProviderDefiningGlobal {
                binder: global.binder,
                scheme,
                origin,
                capture,
            });
        }
        self.type_work
            .charge(
                interfaces
                    .len()
                    .checked_add(implementations.len())
                    .ok_or_else(type_resource)?,
            )
            .map_err(|()| type_resource())?;
        let mut retained_interfaces = Vec::new();
        let mut retained_implementations = Vec::new();
        retained_interfaces
            .try_reserve_exact(interfaces.len())
            .map_err(|_| type_resource())?;
        retained_implementations
            .try_reserve_exact(implementations.len())
            .map_err(|_| type_resource())?;
        for fact in interfaces {
            retained_interfaces.push(
                crate::resolved::clone_checked_interface_fact(
                    fact,
                    None,
                    &mut self.type_work,
                    constraint_work,
                )
                .map_err(resolved_build_error)?,
            );
        }
        for fact in implementations {
            retained_implementations.push(
                crate::resolved::clone_checked_implementation_fact(
                    fact,
                    &mut self.type_work,
                    constraint_work,
                )
                .map_err(resolved_build_error)?,
            );
        }
        Ok(crate::resolved::ProviderDefiningFacts {
            globals: retained_globals,
            positions,
            interfaces: retained_interfaces,
            implementations: retained_implementations,
        })
    }

    pub(super) fn prepare_provider_import_lowering(
        &mut self,
        imported: &ImportedFacts,
    ) -> Result<EvidenceLowering, TypeError> {
        let mut lowering = EvidenceLowering {
            lexical_binders: HashMap::new(),
            interfaces: HashMap::new(),
            interface_methods: HashMap::new(),
            global_schemes: HashMap::new(),
            implementation_methods: HashMap::new(),
            active_binders: HashMap::new(),
        };
        for interface in imported.interface_imports() {
            self.retain_provider_interface(&mut lowering, &interface.fact)?;
        }
        let defining = self
            .provider_defining_facts
            .as_ref()
            .map(std::sync::Arc::clone);
        if let Some(defining) = &defining {
            self.type_work
                .charge(defining.interfaces.len())
                .map_err(|()| type_resource())?;
            for interface in &defining.interfaces {
                self.retain_provider_interface(&mut lowering, interface)?;
            }
        }
        for global in (crate::resolved::ProviderExternalFacts {
            imported,
            defining: defining.as_deref(),
        })
        .globals()
        {
            self.type_work.charge(1).map_err(|()| type_resource())?;
            lowering
                .global_schemes
                .try_reserve(1)
                .map_err(|_| type_resource())?;
            let scheme = self.lower_constrained_scheme(
                global.scheme(),
                &lowering,
                MethodEvidenceOwner::Global(global.binder()),
                false,
                global.origin().primary_span(),
            )?;
            if lowering
                .global_schemes
                .insert(global.binder(), scheme)
                .is_some()
            {
                return Err(invalid_state());
            }
        }
        for implementation in imported.implementations() {
            self.retain_completed_implementation_lowering(&mut lowering, &implementation.fact)?;
        }
        if let Some(defining) = &defining {
            self.type_work
                .charge(defining.implementations.len())
                .map_err(|()| type_resource())?;
            for implementation in &defining.implementations {
                self.retain_completed_implementation_lowering(&mut lowering, implementation)?;
            }
        }
        Ok(lowering)
    }

    pub(super) fn retain_completed_implementation_lowering(
        &mut self,
        lowering: &mut EvidenceLowering,
        implementation: &CheckedImplementationFact,
    ) -> Result<(), TypeError> {
        self.type_work
            .charge(implementation.methods.len())
            .map_err(|()| type_resource())?;
        lowering
            .implementation_methods
            .try_reserve(implementation.methods.len())
            .map_err(|_| type_resource())?;
        for method in &implementation.methods {
            let scheme = self.lower_constrained_scheme(
                &method.scheme,
                lowering,
                MethodEvidenceOwner::Implementation(method.id),
                true,
                method.span,
            )?;
            let lowered = LoweredImplementationMethod {
                binder: method.binder,
                head_type_parameter_count: method.head_type_parameter_count(),
                application: implementation
                    .application()
                    .clone_with_budget(&mut self.type_work)
                    .map_err(|()| type_resource())?,
                scheme,
                span: method.span,
            };
            if lowering
                .implementation_methods
                .insert(method.id, lowered)
                .is_some()
            {
                return Err(invalid_state());
            }
        }
        Ok(())
    }

    fn retain_provider_interface(
        &mut self,
        lowering: &mut EvidenceLowering,
        fact: &CheckedInterfaceFact,
    ) -> Result<(), TypeError> {
        self.type_work
            .charge(
                fact.methods
                    .len()
                    .checked_mul(2)
                    .and_then(|methods| methods.checked_add(1))
                    .ok_or_else(type_resource)?,
            )
            .map_err(|()| type_resource())?;
        let mut methods = Vec::new();
        methods
            .try_reserve_exact(fact.methods.len())
            .map_err(|_| type_resource())?;
        lowering
            .interface_methods
            .try_reserve(fact.methods.len())
            .map_err(|_| type_resource())?;
        for method in &fact.methods {
            self.type_work
                .charge(fact.parameters.len())
                .map_err(|()| type_resource())?;
            let mut parameters = Vec::new();
            parameters
                .try_reserve_exact(fact.parameters.len())
                .map_err(|_| type_resource())?;
            parameters.extend(fact.parameters.iter().map(|parameter| parameter.id));
            let authoritative = method.authoritative_type_parameters();
            self.type_work
                .charge(authoritative.len())
                .map_err(|()| type_resource())?;
            let mut type_parameters = Vec::new();
            type_parameters
                .try_reserve_exact(authoritative.len())
                .map_err(|_| type_resource())?;
            for parameter in authoritative {
                type_parameters.push((
                    parameter.id,
                    clone_kind_with_budget(&parameter.kind, &mut self.type_work)
                        .map_err(|()| type_resource())?,
                ));
            }
            let lowered = LoweredInterfaceMethod {
                interface: fact.id,
                parameters: parameters.into_boxed_slice(),
                type_parameters: type_parameters.into_boxed_slice(),
                value_type: self.clone_type(&method.value_type)?,
                declaration_span: method.span,
            };
            if method.id.interface() != fact.id
                || lowering
                    .interface_methods
                    .insert(method.id, lowered)
                    .is_some()
            {
                return Err(invalid_state());
            }
            methods.push(method.id);
        }
        let determination = fact
            .determination()
            .map(|key| {
                self.constraint_work
                    .charge(key.positions().len())
                    .map_err(|()| constraint_resource())?;
                let mut positions = Vec::new();
                positions
                    .try_reserve_exact(key.positions().len())
                    .map_err(|_| constraint_resource())?;
                positions.extend_from_slice(key.positions());
                Ok::<_, TypeError>(positions.into_boxed_slice())
            })
            .transpose()?;
        lowering
            .interfaces
            .try_reserve(1)
            .map_err(|_| type_resource())?;
        lowering.interfaces.insert(
            fact.id,
            LoweredInterface {
                methods: methods.into_boxed_slice(),
                determination,
            },
        );
        Ok(())
    }
}

struct GlobalSource<'a> {
    binder: BinderId,
    scheme: &'a ConstrainedScheme,
    origin: &'a Origin,
    capture: &'a crate::core::capture::CaptureValueSummary,
}

fn same_global_source(
    retained: &ProviderExternalGlobal,
    source: &GlobalSource<'_>,
    work: &mut TypeWorkBudget,
) -> Result<bool, TypeError> {
    work.charge(1).map_err(|()| type_resource())?;
    if retained.binder != source.binder
        || !same_kinded_type_parameters_with_budget(
            &retained.scheme.type_parameters,
            &source.scheme.type_parameters,
            work,
        )
        .map_err(|()| type_resource())?
        || !same_origin_with_budget(&retained.origin, source.origin, work)
            .map_err(|()| type_resource())?
        || !retained
            .capture
            .same_with_budget(source.capture, work)
            .map_err(|()| type_resource())?
        || retained.scheme.requirements.len() != source.scheme.requirements.len()
    {
        return Ok(false);
    }
    work.charge(source.scheme.requirements.len())
        .map_err(|()| type_resource())?;
    for (left, right) in retained
        .scheme
        .requirements
        .iter()
        .zip(&source.scheme.requirements)
    {
        if left.id != right.id
            || left.interface() != right.interface()
            || left.span != right.span
            || left.arguments().len() != right.arguments().len()
            || !same_origin_with_budget(&left.origin, &right.origin, work)
                .map_err(|()| type_resource())?
        {
            return Ok(false);
        }
        work.charge(right.arguments().len())
            .map_err(|()| type_resource())?;
        for (left, right) in left.arguments().iter().zip(right.arguments()) {
            if !same_type_with_budget(left, right, work).map_err(|()| type_resource())? {
                return Ok(false);
            }
        }
    }
    same_type_with_budget(
        retained.scheme.value_type(),
        source.scheme.value_type(),
        work,
    )
    .map_err(|()| type_resource())
}

pub(super) fn charge_origin_clone(
    mut origin: &Origin,
    work: &mut TypeWorkBudget,
) -> Result<(), TypeError> {
    loop {
        // Both the clone's traversal and retained provenance node participate.
        work.charge(2).map_err(|()| type_resource())?;
        match origin {
            Origin::Source(_) => return Ok(()),
            Origin::Generated { cause, .. } => origin = cause,
            Origin::Related { primary, related } => {
                work.charge(related.len().checked_mul(2).ok_or_else(type_resource)?)
                    .map_err(|()| type_resource())?;
                origin = primary;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        module::{ModuleGraph, ModuleRoots, load_module_graph},
        resolve::{DependencyExports, resolve_module},
    };
    use std::{
        fs,
        path::PathBuf,
        sync::atomic::{AtomicU64, Ordering},
    };

    static FIXTURE_IDS: AtomicU64 = AtomicU64::new(0);

    struct Fixture(PathBuf);
    impl Fixture {
        fn new(files: &[(&str, &str)]) -> (Self, ModuleGraph) {
            let id = FIXTURE_IDS.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir()
                .join(format!("ash-provider-globals-{}-{id}", std::process::id()));
            fs::create_dir(&path).unwrap();
            let fixture = Self(path);
            for (name, text) in files {
                fs::write(fixture.0.join(name), text).unwrap();
            }
            let graph =
                load_module_graph(&fixture.0.join("entry.ash"), &ModuleRoots::empty()).unwrap();
            (fixture, graph)
        }
    }
    impl Drop for Fixture {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    fn checked_graph(graph: &ModuleGraph) -> (Vec<CheckedModule>, ResolvedModule) {
        let mut checked: Vec<CheckedModule> = Vec::new();
        for loaded in graph.modules() {
            let dependencies = loaded
                .dependencies()
                .iter()
                .map(|edge| {
                    DependencyExports::new(
                        edge,
                        checked
                            .iter()
                            .find(|module| module.module() == edge.target())
                            .unwrap()
                            .exports(),
                    )
                    .unwrap()
                })
                .collect::<Vec<_>>();
            let resolved = resolve_module(loaded, &dependencies).unwrap();
            if loaded.id() == graph.entry() {
                // Retain the resolver's imported fact view independently while
                // checking each source body once through the ordinary entry.
                let retained = resolve_module(loaded, &dependencies).unwrap();
                checked.push(check_module(resolved).unwrap());
                return (checked, retained);
            }
            checked.push(check_module(resolved).unwrap());
        }
        panic!("the graph contains its entry")
    }

    fn compare_final(
        catalog: &ProviderExternalGlobals,
        checked: Vec<CheckedModule>,
        entry: crate::module::ModuleId,
    ) {
        let linked = link_modules(checked, entry).unwrap();
        let validated = crate::validate_linked_facts_for_test(linked).unwrap();
        let reference = EffectElaborator::for_module_program(&validated).unwrap();
        let lowering = reference.evidence_lowering.as_ref().unwrap();
        for row in catalog.rows() {
            let expected = &lowering.global_schemes[&row.binder()];
            assert_eq!(row.lowered().core_scheme, expected.core_scheme);
            assert_eq!(row.lowered().type_parameters, expected.type_parameters);
            assert_eq!(
                row.lowered().requirements.len(),
                expected.requirements.len()
            );
            for (actual, expected) in row
                .lowered()
                .requirements
                .iter()
                .zip(&expected.requirements)
            {
                assert_eq!(actual.owner, expected.owner);
                assert_eq!(actual.id, expected.id);
                assert_eq!(actual.methods.len(), expected.methods.len());
                for (actual, expected) in actual.methods.iter().zip(&expected.methods) {
                    assert_eq!(actual.method, expected.method);
                    assert_eq!(actual.application, expected.application);
                    assert_eq!(actual.ty, expected.ty);
                }
            }
        }
    }

    #[test]
    fn provider_globals_match_final_unconstrained_polymorphic_and_row_abis() {
        let (_fixture, graph) = Fixture::new(&[(
            "entry.ash",
            concat!(
                "pub identity<A> : A -> A\nidentity value = value\n",
                "pub relay<R : EffectRow, A> : (Unit -> A ! {| R}) -> A ! {| R}\nrelay action = action ()\n",
                "main : Unit -> Int\nmain () = identity 42\n",
            ),
        )]);
        let (checked, retained) = checked_graph(&graph);
        let mut elaborator = EffectElaborator::new();
        let catalog = elaborator
            .prepare_provider_external_globals(checked.last().unwrap(), retained.imported_facts())
            .unwrap();
        assert_eq!(catalog.rows().len(), 3);
        for source in checked.last().unwrap().schemes() {
            let row = catalog.global(source.binder).unwrap();
            assert_eq!(row.scheme(), &source.scheme);
            assert_eq!(row.origin(), &source.origin);
            assert_eq!(row.capture(), &source.capture);
        }
        assert_eq!(elaborator.builder.node_checkpoint(), 0);
        compare_final(&catalog, checked, graph.entry());
    }

    const ORDERED_REQUIREMENTS: &str = concat!(
        "pub interface First<A> {\nfirst : A -> A\ninspect : A -> Int\n}\n",
        "pub interface Second<A> {\nsecond : A -> Bool\n}\n",
        "pub work<A> : A -> Bool where First<A>, Second<A>\nwork value = second (first value)\n",
        "main : Unit -> Int\nmain () = 42\n",
    );

    #[test]
    fn provider_globals_preserve_two_requirement_and_method_orders() {
        let (_fixture, graph) = Fixture::new(&[("entry.ash", ORDERED_REQUIREMENTS)]);
        let (checked, retained) = checked_graph(&graph);
        let owner = checked.last().unwrap();
        let work = owner
            .schemes()
            .iter()
            .find(|scheme| scheme.spelling == "work")
            .unwrap();
        let catalog = EffectElaborator::new()
            .prepare_provider_external_globals(owner, retained.imported_facts())
            .unwrap();
        let row = catalog.global(work.binder).unwrap();
        let requirements = &row.lowered().requirements;
        assert_eq!(requirements.len(), 2);
        assert_eq!(requirements[0].id, work.scheme.requirements[0].id);
        assert_eq!(requirements[1].id, work.scheme.requirements[1].id);
        assert_eq!(
            requirements[0]
                .methods
                .iter()
                .map(|method| method.method)
                .collect::<Vec<_>>(),
            owner.interface_facts()[0]
                .methods
                .iter()
                .map(|method| method.id)
                .collect::<Vec<_>>()
        );
        assert_eq!(
            requirements[1].methods[0].method,
            owner.interface_facts()[1].methods[0].id
        );
        compare_final(&catalog, checked, graph.entry());
    }

    #[test]
    fn provider_globals_refuse_interface_carriers_before_copying_metadata() {
        let (_fixture, graph) = Fixture::new(&[("entry.ash", ORDERED_REQUIREMENTS)]);
        let (checked, _) = checked_graph(&graph);
        let fact = &checked.last().unwrap().interface_facts()[0];
        // The method vector, method index and interface index coexist. Refuse
        // their whole reservation before copying any method metadata.
        let carriers = 1 + 2 * fact.methods.len();
        let mut elaborator = EffectElaborator::new();
        elaborator.type_work = TypeWorkBudget::with_limit(carriers - 1);
        let mut lowering = EvidenceLowering {
            lexical_binders: HashMap::new(),
            interfaces: HashMap::new(),
            interface_methods: HashMap::new(),
            global_schemes: HashMap::new(),
            implementation_methods: HashMap::new(),
            active_binders: HashMap::new(),
        };
        assert!(matches!(
            elaborator.retain_provider_interface(&mut lowering, fact),
            Err(TypeError::Internal(
                ElaborationFailure::TypeResourceExhausted
            ))
        ));
        assert_eq!(elaborator.type_work.used(), 0);
        assert!(lowering.interfaces.is_empty());
        assert!(lowering.interface_methods.is_empty());
    }

    #[test]
    fn provider_globals_preserve_defining_identity_through_alias_and_reexport() {
        let (_fixture, graph) = Fixture::new(&[
            ("helper.ash", ORDERED_REQUIREMENTS),
            ("facade.ash", "pub import helper (work)\n"),
            (
                "entry.ash",
                "import facade (work as relay)\nmain : Unit -> Int\nmain () = 42\n",
            ),
        ]);
        let (checked, retained) = checked_graph(&graph);
        let imported = retained.imported_facts();
        let defining = checked
            .iter()
            .flat_map(CheckedModule::schemes)
            .find(|fact| fact.spelling == "work")
            .unwrap();
        assert!(
            imported
                .globals()
                .any(|fact| fact.binder == defining.binder)
        );
        let mut elaborator = EffectElaborator::new();
        let catalog = elaborator
            .prepare_provider_external_globals(checked.last().unwrap(), imported)
            .unwrap();
        let row = catalog.global(defining.binder).unwrap();
        assert_eq!(row.scheme(), &defining.scheme);
        assert_eq!(row.origin(), &defining.origin);
        assert_eq!(row.capture(), &defining.capture);
        assert_eq!(row.lowered().requirements.len(), 2);
        assert_eq!(elaborator.builder.node_checkpoint(), 0);
        compare_final(&catalog, checked, graph.entry());
    }

    #[test]
    fn provider_globals_use_cumulative_exact_budget_and_leave_inputs_reusable() {
        let (_fixture, graph) = Fixture::new(&[("entry.ash", ORDERED_REQUIREMENTS)]);
        let (checked, retained) = checked_graph(&graph);
        let owner = checked.last().unwrap();
        let imported = retained.imported_facts();
        let mut measured = EffectElaborator::new();
        let reference = measured
            .prepare_provider_external_globals(owner, imported)
            .unwrap();
        let cost = measured.type_work.used();
        assert!(cost > 0);
        for prefix in [0, 17] {
            let mut refused = EffectElaborator::new();
            refused.type_work = TypeWorkBudget::with_limit(prefix + cost - 1);
            refused.type_work.charge(prefix).unwrap();
            assert!(matches!(
                refused.prepare_provider_external_globals(owner, imported),
                Err(TypeError::Internal(
                    ElaborationFailure::TypeResourceExhausted
                ))
            ));
            assert_eq!(refused.builder.node_checkpoint(), 0);
            // Failure consumes cumulative work. Retry from the same immutable
            // facts with fresh ledgers, rather than refunding failed work.
            for _ in 0..2 {
                let mut exact = EffectElaborator::new();
                exact.type_work = TypeWorkBudget::with_limit(prefix + cost);
                exact.type_work.charge(prefix).unwrap();
                let catalog = exact
                    .prepare_provider_external_globals(owner, imported)
                    .unwrap();
                assert_eq!(exact.type_work.used(), prefix + cost);
                for row in catalog.rows() {
                    let expected = reference.global(row.binder()).unwrap();
                    assert_eq!(row.scheme(), expected.scheme());
                    assert_eq!(row.origin(), expected.origin());
                    assert_eq!(row.capture(), expected.capture());
                    assert_eq!(row.lowered().core_scheme, expected.lowered().core_scheme);
                }
            }
        }
        compare_final(&reference, checked, graph.entry());
    }

    #[test]
    fn provider_globals_budget_duplicate_interface_authentication_cumulatively() {
        let (_fixture, graph) = Fixture::new(&[
            ("helper.ash", ORDERED_REQUIREMENTS),
            (
                "entry.ash",
                "import helper (work)\nmain : Unit -> Int\nmain () = 42\n",
            ),
        ]);
        let (checked, retained) = checked_graph(&graph);
        // These independently checked defining and imported views contain the
        // same canonical interface facts. Authenticating duplicate identities
        // must share the existing constraint ledger rather than reset it.
        let owner = &checked[0];
        let imported = retained.imported_facts();
        let mut measured = EffectElaborator::new();
        let reference = measured
            .prepare_provider_external_globals(owner, imported)
            .unwrap();
        let cost = measured.constraint_work.used();
        assert!(cost > 0);
        for prefix in [0, 11] {
            let mut refused = EffectElaborator::new();
            refused.constraint_work =
                crate::interface::InterfaceConstraintBudget::with_limit(prefix + cost - 1);
            refused.constraint_work.charge(prefix).unwrap();
            assert!(matches!(
                refused.prepare_provider_external_globals(owner, imported),
                Err(TypeError::Internal(
                    ElaborationFailure::ConstraintResourceExhausted
                ))
            ));
            let mut exact = EffectElaborator::new();
            exact.constraint_work =
                crate::interface::InterfaceConstraintBudget::with_limit(prefix + cost);
            exact.constraint_work.charge(prefix).unwrap();
            let catalog = exact
                .prepare_provider_external_globals(owner, imported)
                .unwrap();
            assert_eq!(exact.constraint_work.used(), prefix + cost);
            assert_eq!(catalog.rows().len(), reference.rows().len());
            assert_eq!(exact.builder.node_checkpoint(), 0);
        }
    }

    fn imported_copy(
        source: &crate::resolved::CheckedGlobalScheme,
    ) -> crate::resolved::ImportedGlobalScheme {
        let mut work = TypeWorkBudget::unbounded();
        crate::resolved::ImportedGlobalScheme {
            binder: source.binder,
            scheme: source.scheme.clone_with_budget(&mut work).unwrap(),
            origin: source.origin.clone(),
            capture: source.capture.clone_with_budget(&mut work).unwrap(),
        }
    }

    #[test]
    fn provider_globals_reject_conflicting_same_identity_facts() {
        let (_fixture, graph) = Fixture::new(&[("entry.ash", ORDERED_REQUIREMENTS)]);
        let (checked, _) = checked_graph(&graph);
        let owner = checked.last().unwrap();
        let source = owner
            .schemes()
            .iter()
            .find(|fact| fact.spelling == "work")
            .unwrap();
        // Private malformed-fact probes test snapshot consistency. They do not
        // bypass checked-summary admission or constitute source acceptance.
        for mutation in 0..4 {
            let mut fact = imported_copy(source);
            match mutation {
                0 => {}
                1 => fact.scheme.requirements.reverse(),
                2 => fact.capture = crate::core::capture::CaptureValueSummary::default(),
                3 => {
                    fact.origin = Origin::Generated {
                        cause: Box::new(fact.origin),
                        reason: GeneratedReason::BindingLowering,
                    }
                }
                _ => unreachable!(),
            }
            let mut imported = ImportedFacts::default();
            imported
                .insert_global(fact, &mut TypeWorkBudget::unbounded())
                .unwrap();
            let result =
                EffectElaborator::new().prepare_provider_external_globals(owner, &imported);
            if mutation == 0 {
                assert_eq!(result.unwrap().rows().len(), owner.schemes().len());
            } else {
                assert!(matches!(
                    result,
                    Err(TypeError::Internal(ElaborationFailure::InvalidState))
                ));
            }
        }
        let canonical = &owner.interface_facts()[0];
        let mut imported = ImportedFacts::default();
        imported.insert_interface(
            CheckedInterfaceFact::without_methods_for_test(
                canonical.id,
                canonical.spelling.clone(),
                canonical.parameters.to_vec().into_boxed_slice(),
                canonical.origin.clone(),
                canonical.span,
            ),
            owner.module(),
            canonical.span,
            false,
        );
        assert!(matches!(
            EffectElaborator::new().prepare_provider_external_globals(owner, &imported),
            Err(TypeError::Internal(ElaborationFailure::InvalidState))
        ));
    }

    #[test]
    fn provider_globals_dispose_deep_snapshots_after_late_failure_on_small_stack() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let (_fixture, graph) =
                    Fixture::new(&[("entry.ash", "main : Unit -> Int\nmain () = 42\n")]);
                let (checked, _) = checked_graph(&graph);
                let owner = checked.last().unwrap();
                let source = &owner.schemes()[0];
                let mut imported = ImportedFacts::default();
                // Private depth injection exercises ownership disposal, not
                // source typing or permission to publish a checked template.
                let mut ty = Type::Unit;
                let mut origin = source.origin.clone();
                for _ in 0..32_000 {
                    ty = Type::Function(Box::new(Type::Unit), Box::new(ty));
                    origin = Origin::Generated {
                        cause: Box::new(origin),
                        reason: GeneratedReason::BindingLowering,
                    };
                }
                let deep_binder = BinderId::resolved(crate::module::ModuleId::new(99), 0);
                imported
                    .insert_global(
                        crate::resolved::ImportedGlobalScheme {
                            binder: deep_binder,
                            scheme: ConstrainedScheme::from_rank1_type(ty),
                            origin,
                            capture: source
                                .capture
                                .clone_with_budget(&mut TypeWorkBudget::unbounded())
                                .unwrap(),
                        },
                        &mut TypeWorkBudget::unbounded(),
                    )
                    .unwrap();
                let mut measured = EffectElaborator::new();
                let complete = measured
                    .prepare_provider_external_globals(owner, &imported)
                    .unwrap();
                let cost = measured.type_work.used();
                assert_eq!(complete.rows().len(), 2);
                let deep = complete.global(deep_binder).unwrap();
                assert!(
                    same_type_with_budget(
                        deep.scheme().value_type(),
                        imported.globals().next().unwrap().scheme.value_type(),
                        &mut TypeWorkBudget::unbounded(),
                    )
                    .unwrap()
                );
                drop(complete);
                // The deep imported row is complete before the final local
                // row fails. Error teardown must drain already retained rows
                // and all partial snapshots without recursive stack growth.
                let mut refused = EffectElaborator::new();
                refused.type_work = TypeWorkBudget::with_limit(cost - 1);
                assert!(matches!(
                    refused.prepare_provider_external_globals(owner, &imported),
                    Err(TypeError::Internal(
                        ElaborationFailure::TypeResourceExhausted
                    ))
                ));
                for _ in 0..2 {
                    let mut exact = EffectElaborator::new();
                    exact.type_work = TypeWorkBudget::with_limit(cost);
                    let catalog = exact
                        .prepare_provider_external_globals(owner, &imported)
                        .unwrap();
                    assert_eq!(exact.type_work.used(), cost);
                    assert_eq!(catalog.rows().len(), 2);
                    assert_eq!(exact.builder.node_checkpoint(), 0);
                    drop(catalog);
                }
                // The source ImportedFacts owners also drain iteratively.
                drop(imported);
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn provider_globals_constrained_method_application_failure_drains_substituted_type() {
        const CHILD: &str = "ASH_PROVIDER_GLOBAL_METHOD_APPLICATION_CHILD";
        if std::env::var_os(CHILD).is_none() {
            let output = std::process::Command::new(std::env::current_exe().unwrap())
                .args([
                    "--exact",
                    "elaborate::provider_globals::tests::provider_globals_constrained_method_application_failure_drains_substituted_type",
                    "--nocapture",
                ])
                .env(CHILD, "1")
                .output()
                .unwrap();
            assert!(
                output.status.success(),
                "constrained method child failed: {}",
                String::from_utf8_lossy(&output.stderr)
            );
            return;
        }
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let (_fixture, graph) =
                    Fixture::new(&[("entry.ash", "main : Unit -> Int\nmain () = 42\n")]);
                let (checked, _) = checked_graph(&graph);
                let source = &checked[0].schemes()[0];
                let module = crate::module::ModuleId::new(99);
                let interface = InterfaceId::new(module, 0);
                let method = MethodId::new(interface, 0);
                let parameter = TypeVariableId::new(0);
                let binder = BinderId::resolved(module, 0);
                let mut argument = Type::Unit;
                for _ in 0..32_000 {
                    argument = Type::Function(Box::new(Type::Unit), Box::new(argument));
                }
                // Constructed private ABI metadata isolates ownership during
                // dictionary lowering. It grants no source or template admission.
                let scheme = ConstrainedScheme {
                    type_parameters: Box::new([]),
                    requirements: Box::new([CheckedRequirement {
                        id: RequirementId::new(
                            crate::interface::RequirementOwner::Global(binder),
                            0,
                        ),
                        application: InterfaceApplication::new(interface, Box::new([argument])),
                        origin: source.origin.clone(),
                        span: source.origin.primary_span(),
                    }]),
                    value_type: Type::Unit,
                };
                let lowering = EvidenceLowering {
                    lexical_binders: HashMap::new(),
                    interfaces: HashMap::from([(
                        interface,
                        LoweredInterface {
                            methods: Box::new([method]),
                            determination: None,
                        },
                    )]),
                    interface_methods: HashMap::from([(
                        method,
                        LoweredInterfaceMethod {
                            interface,
                            parameters: Box::new([parameter]),
                            type_parameters: Box::new([]),
                            value_type: Type::Variable(parameter),
                            declaration_span: source.origin.primary_span(),
                        },
                    )]),
                    global_schemes: HashMap::new(),
                    implementation_methods: HashMap::new(),
                    active_binders: HashMap::new(),
                };
                let run = |elaborator: &mut EffectElaborator| {
                    elaborator.lower_constrained_scheme(
                        &scheme,
                        &lowering,
                        MethodEvidenceOwner::Global(binder),
                        false,
                        source.origin.primary_span(),
                    )
                };
                let mut measured = EffectElaborator::new();
                let complete = run(&mut measured).unwrap();
                let cost = measured.type_work.used();
                let lowered_method = &complete.requirements[0].methods[0];
                assert_eq!(lowered_method.method, method);
                assert!(
                    same_type_with_budget(
                        &lowered_method.ty,
                        &scheme.requirements[0].arguments()[0],
                        &mut TypeWorkBudget::unbounded()
                    )
                    .unwrap()
                );

                // Measure the actual application clone and actual subsequent
                // Core projection independently. Subtraction locates the
                // constrained method's late application-clone boundary without
                // duplicating substitution's cell-accounting algorithm.
                let mut application_work = TypeWorkBudget::unbounded();
                drop(
                    lowered_method
                        .application
                        .clone_with_budget(&mut application_work)
                        .unwrap(),
                );
                let mut tail = EffectElaborator::new();
                drop(IterativeTypeOwner::new(
                    tail.pure_core_type(&complete.value_type).unwrap(),
                ));
                tail.type_work.charge(1).unwrap();
                drop(IterativeTypeOwner::new(
                    tail.pure_core_type(&lowered_method.ty).unwrap(),
                ));
                let before_application = cost
                    .checked_sub(application_work.used() + tail.type_work.used())
                    .unwrap();
                assert!(before_application > 32_000);
                drop(complete);
                for prefix in [0, 13] {
                    for allowance in [
                        before_application + application_work.used() - 1,
                        before_application,
                    ] {
                        let mut refused = EffectElaborator::new();
                        refused.type_work = TypeWorkBudget::with_limit(prefix + allowance);
                        refused.type_work.charge(prefix).unwrap();
                        eprintln!(
                            "constrained method application refusal: prefix={prefix}, allowance={allowance}, boundary={before_application}"
                        );
                        assert!(matches!(
                            run(&mut refused),
                            Err(TypeError::Internal(
                                ElaborationFailure::TypeResourceExhausted
                            ))
                        ));
                        assert!(refused.type_work.used() >= prefix + before_application);
                        assert_eq!(refused.builder.node_checkpoint(), 0);
                    }
                    for _ in 0..2 {
                        let mut exact = EffectElaborator::new();
                        exact.type_work = TypeWorkBudget::with_limit(prefix + cost);
                        exact.type_work.charge(prefix).unwrap();
                        let complete = run(&mut exact).unwrap();
                        assert_eq!(exact.type_work.used(), prefix + cost);
                        assert!(
                            same_type_with_budget(
                                &complete.requirements[0].methods[0].ty,
                                &scheme.requirements[0].arguments()[0],
                                &mut TypeWorkBudget::unbounded()
                            )
                            .unwrap()
                        );
                        drop(complete);
                    }
                }
                drop(lowering);
                drop(scheme);
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
