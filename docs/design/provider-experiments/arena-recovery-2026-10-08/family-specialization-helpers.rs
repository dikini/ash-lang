// Private insertion draft for src/core/provider/specialization.rs.
// Not a standalone module. Parent composes only after source review.

fn family_certificate<'a>(
    admission: &ProviderScopeAdmission,
    registry: &'a crate::resolved::ResolvedRegistry,
    at: NodeId,
    work: &mut TypeWorkBudget,
) -> Result<&'a crate::elaborate::provider::CheckedProviderContracts, ValidationError> {
    super::charge(work, registry.provider_contract_count())?;
    let certificate = registry.provider_contracts()
        .find(|(module, _)| **module == admission.definition.id.module())
        .map(|(_, certificate)| certificate.as_ref())
        .ok_or_else(|| super::invalid(at))?;
    super::charge(work, certificate.resource_count())?;
    if !certificate.resource_contracts().any(|(_, _, fact)|
        std::sync::Arc::ptr_eq(fact, &admission.definition))
    {
        return Err(super::invalid(at));
    }
    Ok(certificate)
}

/// Reconstructs the member header from the genuine original certificate and
/// the complete outer Type/Row actuals. Hidden answer/row equations, disjoint
/// freshening, and source ownership remain the enclosing admission's checks.
fn authenticate_family_header(
    admission: &ProviderScopeAdmission,
    family: &ProviderFamilyAdmission,
    copy: &ProviderCopiedTemplate<'_>,
    registry: &crate::resolved::ResolvedRegistry,
    renaming: &crate::types::TemplateIdentityRenaming<'_>,
    work: &mut TypeWorkBudget,
) -> Result<crate::types::EffectInstance, ValidationError> {
    use crate::types::{Kind, KindedArgument, Type};
    let ProviderOriginalTemplate::Handler(original) = copy.original else {
        return Err(ValidationError::new(crate::core::ValidationReason::NodeType, None));
    };
    let at = original.original_program().root;
    let fact = admission.definition.as_ref();
    let written = fact.family_template.as_ref().ok_or_else(|| super::invalid(at))?;
    let certificate = family_certificate(admission, registry, at, work)?;
    super::charge(work, certificate.resource_count().checked_mul(4).ok_or_else(super::resource)?)?;
    let identity = certificate.family_identity(fact.id).ok_or_else(|| super::invalid(at))?;
    let application = certificate.family_provider_application(fact.id).ok_or_else(|| super::invalid(at))?;
    let requirements = certificate.family_requirements(fact.id).ok_or_else(|| super::invalid(at))?;
    let original_certificate = certificate.family_handler_certificate(fact.id)
        .ok_or_else(|| super::invalid(at))?;
    if !original.authenticates_certificate(original_certificate) {
        return Err(super::invalid(at));
    }
    if family.identity != identity || identity.definition != fact.id
        || identity.parameter != written.parameter.id || written.parameter.kind != Kind::Type
        || original.original_template() != crate::resolved::ProviderTemplateId::new(fact.id, 3)
        || admission.arguments.len() != fact.parameters.len()
        || family.requirements.len() != requirements.len()
        || !matches!(&family.payload, Type::Unit | Type::Bool | Type::Int)
    {
        return Err(super::invalid(at));
    }
    original.authenticate_source(work)?;
    original.authenticate_definition(fact, work)?;
    super::charge(work, fact.parameters.len())?;
    for (parameter, actual) in fact.parameters.iter().zip(&admission.arguments) {
        match (&parameter.kind, actual) {
            (Kind::Type, KindedArgument::TypeArg(actual)) => {
                let substituted = copy.substitution.types.get(&parameter.id)
                    .ok_or_else(|| super::invalid(at))?;
                if !crate::types::same_type_with_budget(substituted, actual, work)
                    .map_err(|()| super::resource())?
                {
                    return Err(super::invalid(at));
                }
            }
            (Kind::EffectRow, KindedArgument::RowArg(actual)) => {
                let substituted = copy.substitution.rows.get(&parameter.id)
                    .ok_or_else(|| super::invalid(at))?;
                if !crate::types::same_effect_rows_with_budget(substituted, actual, work)
                    .map_err(|()| super::resource())?
                {
                    return Err(super::invalid(at));
                }
            }
            _ => return Err(super::invalid(at)),
        }
    }
    let payload = copy.substitution.types.get(&identity.parameter)
        .ok_or_else(|| super::invalid(at))?;
    if !crate::types::same_type_with_budget(payload, &family.payload, work)
        .map_err(|()| super::resource())?
        || !same_application(application, &written.provider_application, work)?
        || !same_application(&specialized_application(application, copy, renaming, work)?,
            &family.application, work)?
    {
        return Err(super::invalid(at));
    }
    let provided = substitute_instance(&written.provided.instance, &copy.substitution, renaming, work)?;
    let native = substitute_instance(&written.interpreted.instance, &copy.substitution, renaming, work)?;
    if crate::types::compare_effect_instances_with_budget(&native, &family.native_effect, work)
        .map_err(|()| super::resource())? != std::cmp::Ordering::Equal
        || registry.foreign_effect(provided.effect())
    {
        return Err(super::invalid(at));
    }
    let mut original_native = false;
    for registered in registry.foreign_modules() {
        super::charge(work, 1)?;
        if std::sync::Arc::ptr_eq(registered, &admission.native) {
            if original_native { return Err(super::invalid(at)); }
            original_native = true;
        }
    }
    let storage = admission.native.storage.as_ref().ok_or_else(|| super::invalid(at))?;
    if !original_native || native.effect() != storage.effect()
        || fact.state.ty.outer_nominal() != Some(storage.state())
        || !matches!(native.arguments().get(storage.owner_parameter()),
            Some(KindedArgument::TypeArg(Type::Variable(owner))) if *owner == admission.identity)
        || !matches!(native.arguments().get(storage.payload_parameter()),
            Some(KindedArgument::TypeArg(payload)) if crate::types::same_type_with_budget(
                payload, &family.payload, work).map_err(|()| super::resource())?)
    {
        return Err(super::invalid(at));
    }
    Ok(provided)
}

/// Authenticates one unique complete family node and its exact earlier
/// prerequisite locator while retaining the original whole-plan root.
fn authenticate_family_prerequisite(
    family: &ProviderFamilyAdmission,
    ordinal: usize,
    at: NodeId,
    work: &mut TypeWorkBudget,
) -> Result<crate::foreign::ForeignLayoutProducer, ValidationError> {
    use crate::interface::EvidenceNode;
    let (selection, selected) = family.requirements.get(ordinal).ok_or_else(|| super::invalid(at))?;
    super::charge(work, selection.node_count())?;
    let mut matched = None;
    for index in 0..selection.node_count() {
        let node = crate::interface::EvidenceNodeId::new(index);
        let Some(EvidenceNode::ProviderFamily {
            source, definition, parameter, application, prerequisites, ..
        }) = selection.node(node) else { continue; };
        if source != family.lexical || definition != family.identity.definition
            || parameter != family.identity.parameter
            || !same_application(application, &family.application, work)?
        {
            continue;
        }
        super::charge(work, family.requirements.len())?;
        if prerequisites.len() != family.requirements.len()
            || prerequisites.get(ordinal) != Some(selected)
        {
            continue;
        }
        let mut exact = true;
        for ((other, prerequisite), expected) in family.requirements.iter().zip(prerequisites) {
            if !other.shares_plan_with(selection) || other.root() != selection.root()
                || prerequisite != expected || prerequisite.index() >= node.index()
            {
                exact = false;
                break;
            }
        }
        if !exact { continue; }
        if node.index() > selection.root().index() || matched.replace(node).is_some() {
            return Err(super::invalid(at));
        }
    }
    if matched.is_none() { return Err(super::invalid(at)); }
    let Some(EvidenceNode::NativeLayout { producer }) = selection.node(*selected) else {
        return Err(super::invalid(at));
    };
    Ok(producer)
}

/// After `authenticate_family_header` succeeds for these same inputs, produces
/// immutable dictionary projections, never binding or execution authority.
/// Final reauthentication must match each to one ordinary Let with this
/// binder/initializer and check domination of the owning scope.
#[expect(clippy::too_many_arguments, reason = "original certificate, copied graph and canonical native authority remain separate")]
fn authenticate_family_dictionaries(
    admission: &ProviderScopeAdmission,
    family: &ProviderFamilyAdmission,
    entry: &ProviderSpecializationFamilyEntries<'_>,
    copy: &ProviderCopiedTemplate<'_>,
    registry: &crate::resolved::ResolvedRegistry,
    arena: crate::core::dialect::ArenaId,
    target: &[crate::core::dialect::StoredNode<crate::core::EffectOperationFamily>],
    nodes: &std::collections::HashMap<NodeId, NodeId>,
    renaming: &crate::types::TemplateIdentityRenaming<'_>,
    work: &mut TypeWorkBudget,
) -> Result<Vec<SpecializedDictionary>, ValidationError> {
    use crate::core::{EffectExprKind, PureExprKind, PureValue};
    use crate::types::{IterativeTypeOwner, Kind, KindedArgument, Type};
    let ProviderOriginalTemplate::Handler(original) = copy.original else {
        return Err(ValidationError::new(crate::core::ValidationReason::NodeType, None));
    };
    let at = original.original_program().root;
    let certificate = family_certificate(admission, registry, at, work)?;
    super::charge(work, certificate.resource_count())?;
    let requirements = certificate.family_requirements(admission.definition.id)
        .ok_or_else(|| super::invalid(at))?;
    let formals = original.original_dictionary_parameters();
    if requirements.len() != family.requirements.len() || entry.dictionaries.len() != formals.len() {
        return Err(super::invalid(at));
    }
    let layout = admission.native.layout.as_ref().ok_or_else(|| super::invalid(at))?;
    let storage = admission.native.storage.as_ref().ok_or_else(|| super::invalid(at))?;
    super::charge(work, admission.native.canonical_interfaces().len())?;
    let canonical = admission.native.canonical_interfaces().iter()
        .find(|interface| interface.id == layout.interface()).ok_or_else(|| super::invalid(at))?;
    let [interface_parameter] = canonical.parameters.as_ref() else { return Err(super::invalid(at)); };
    let [method] = canonical.methods.as_ref() else { return Err(super::invalid(at)); };
    if interface_parameter.kind != Kind::Type || interface_parameter.id != layout.payload_parameter()
        || method.id != layout.method() || method.id.interface() != canonical.id
        || method.id.declaration() != 0 || !method.type_parameters.is_empty()
        || layout.witness() != storage.witness()
    {
        return Err(super::invalid(at));
    }
    super::charge(work, formals.len().checked_add(requirements.len()).ok_or_else(super::resource)?)?;
    let mut dictionaries = Vec::new();
    dictionaries.try_reserve_exact(formals.len()).map_err(|_| super::resource())?;
    let mut binders = std::collections::HashSet::new();
    binders.try_reserve(formals.len()).map_err(|_| super::resource())?;
    let mut position = 0usize;
    for (ordinal, requirement) in requirements.iter().enumerate() {
        if requirement.id.owner() != crate::interface::RequirementOwner::ResourceFamily(admission.definition.id)
            || usize::try_from(requirement.id.declaration()).ok() != Some(ordinal)
            || requirement.interface() != canonical.id
        {
            return Err(super::invalid(at));
        }
        // This scalar checkpoint admits the sealed one-method Layout contract;
        // other prerequisite categories remain unsupported rather than erased.
        let [KindedArgument::TypeArg(payload)] = requirement.arguments() else {
            return Err(super::invalid(at));
        };
        let formal = formals.get(position).ok_or_else(|| super::invalid(at))?;
        let supplied = entry.dictionaries.get(position).ok_or_else(|| super::invalid(at))?;
        let mut replacements = std::collections::HashMap::new();
        super::charge(work, 1)?;
        replacements.try_reserve(1).map_err(|_| super::resource())?;
        replacements.insert(interface_parameter.id, payload);
        let signature = IterativeTypeOwner::new(crate::types::substitute_type_variables_borrowed_with(
            &method.annotation.ty, &replacements, |units| work.charge(units), || (),
        ).map_err(|()| super::resource())?);
        if !crate::types::same_type_with_budget(&signature, formal.ty(), work)
            .map_err(|()| super::resource())?
        {
            return Err(super::invalid(at));
        }
        let expected = specialized_application(requirement.application(), copy, renaming, work)?;
        let [KindedArgument::TypeArg(payload)] = expected.arguments() else {
            return Err(super::invalid(at));
        };
        if !matches!(payload, Type::Unit | Type::Bool | Type::Int) {
            return Err(super::invalid(at));
        }
        let producer = authenticate_family_prerequisite(family, ordinal, at, work)?;
        let dictionary = registry.foreign_layout_dictionary(producer, work).map_err(|failure|
            if failure.is_resource_exhaustion() { super::resource() } else { super::invalid(at) })?;
        let (encoding, size, alignment) = match payload {
            Type::Unit => (crate::foreign::ForeignScalarEncoding::Unit, 0, 1),
            Type::Bool => (crate::foreign::ForeignScalarEncoding::Bool, 1, 1),
            Type::Int => (crate::foreign::ForeignScalarEncoding::Signed64, 8, 8),
            _ => return Err(super::invalid(at)),
        };
        let producer_payload = IterativeTypeOwner::new(producer.payload_type());
        if producer.interface() != expected.interface() || producer.method() != method.id
            || producer.witness() != layout.witness() || dictionary.producer() != producer
            || !crate::types::same_type_with_budget(dictionary.payload_type(), payload, work)
                .map_err(|()| super::resource())?
            || !crate::types::same_type_with_budget(&producer_payload, payload, work)
                .map_err(|()| super::resource())?
            || dictionary.encoding() != encoding || dictionary.size() != size
            || dictionary.natural_alignment() != alignment
        {
            return Err(super::invalid(at));
        }
        let binder = renamed(formal.id(), copy.freshening.binders, work)?;
        if binder == formal.id() || binder != supplied.binder.id()
            || !matches!(binder, crate::resolved::BinderId::Generated(_))
            || supplied.binder.arena() != arena || !binders.insert(binder)
        {
            return Err(super::invalid(at));
        }
        let original_projection = super::projection::project_binder(at, formal, work)?;
        let projection = specialize_projection(&original_projection, nodes, &copy.freshening,
            &copy.substitution, renaming, work)?;
        let actual_projection = super::projection::project_binder(projection.node, supplied.binder, work)?;
        if !projection.same(&actual_projection, work)? { return Err(super::invalid(projection.node)); }
        let stored = target_node(arena, target, supplied.initializer)?;
        let EffectExprKind::Pure(PureExprKind::Value(PureValue::Intrinsic(intrinsic))) = &stored.kind else {
            return Err(super::invalid(supplied.initializer));
        };
        let producer_type = IterativeTypeOwner::new(producer.producer_type());
        if intrinsic.operation() != (crate::core::packed::Intrinsic::ForeignLayoutWitness { producer })
            || intrinsic.module() != producer.interface().module()
            || !stored.effects.is_empty()
            || !crate::types::same_type_with_budget(&stored.ty, &producer_type, work)
                .map_err(|()| super::resource())?
            || !crate::types::same_type_with_budget(supplied.binder.ty(), &stored.ty, work)
                .map_err(|()| super::resource())?
        {
            return Err(super::invalid(supplied.initializer));
        }
        dictionaries.push(SpecializedDictionary {
            requirement: requirement.id,
            method: method.id,
            binder,
            projection,
            initializer: super::projection::project(supplied.initializer, stored, work)?,
            producer,
        });
        position = position.checked_add(1).ok_or_else(super::resource)?;
    }
    if position != formals.len() { return Err(super::invalid(at)); }
    Ok(dictionaries)
}
