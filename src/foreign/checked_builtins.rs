//! Independent reconstruction of checked Foreign builtin roles.
//!
//! Reserved module admission and private-image restoration establish immutable
//! builtin source bytes. These checks reconstruct original identities, source
//! coordinates and semantic shapes; neither matching spans nor display names
//! alone authorize a host, a native invocation or an executable image.

use super::checked_source::{ForeignAdmissionError, ForeignAdmissionReason, charge, failure};
use crate::{
    module::{
        ForeignCheckedNominalRole as Role, ModuleId, foreign_builtin_source_text,
        foreign_native_host_ranges,
    },
    resolved::{
        CanonicalNominalKind, ResolvedEffectDeclaration, ResolvedNominalDeclarationKind,
        ResolvedRegistry,
    },
    source::{ByteRange, Origin, Span},
    types::{ConstructorId, EffectId, Kind, NominalTypeId, Type, TypeVariableId, TypeWorkBudget},
};

/// Read-only reconstructed roles; these facts supply no execution capability.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct CheckedForeignBuiltinFacts {
    module: ModuleId,
    source: Span,
    native_host: EffectId,
    checked_call: NominalTypeId,
    returned: ConstructorId,
    conversion_failed: ConstructorId,
    boundary_failed: ConstructorId,
}

impl CheckedForeignBuiltinFacts {
    #[cfg(test)]
    pub(crate) const fn module(self) -> ModuleId {
        self.module
    }
    #[cfg(test)]
    pub(crate) const fn source(self) -> Span {
        self.source
    }
    #[cfg(test)]
    pub(crate) const fn native_host(self) -> EffectId {
        self.native_host
    }
    pub(crate) const fn checked_call(self) -> NominalTypeId {
        self.checked_call
    }
    pub(crate) const fn returned(self) -> ConstructorId {
        self.returned
    }
    pub(crate) const fn conversion_failed(self) -> ConstructorId {
        self.conversion_failed
    }
    #[cfg(test)]
    pub(crate) const fn boundary_failed(self) -> ConstructorId {
        self.boundary_failed
    }
}

/// Reconstructs the full canonical inventory after defining-source byte admission.
pub(crate) fn authenticate_checked_builtins(
    registry: &ResolvedRegistry,
    module: ModuleId,
    source: Span,
    work: &mut TypeWorkBudget,
) -> Result<CheckedForeignBuiltinFacts, ForeignAdmissionError> {
    let invalid = || failure(ForeignAdmissionReason::InvalidCodec, source);
    charge(work, 1, source)?;
    let text = foreign_builtin_source_text();
    if !module.is_builtin_foreign()
        || source.range().start() != 0
        || usize::try_from(source.range().end()).ok() != Some(text.len())
    {
        return Err(invalid());
    }
    // Pay the bounded canonical declaration/constructor and host-coordinate scans.
    charge(work, text.len().saturating_mul(3), source)?;
    let (mut offset, mut local, mut materialized, mut constructors) = (0, 0, 0, 0);
    while offset < text.len() {
        let rest = &text[offset..];
        if rest.starts_with("pub type ") || rest.starts_with("pub opaque type ") {
            let end = rest
                .find("\npub ")
                .or_else(|| rest.find("\nnative_host_metadata :"))
                .unwrap_or(rest.len());
            let declaration = rest[..end].trim_end();
            let shape = SHAPES.get(local).ok_or_else(invalid)?;
            if local >= 6 {
                let role = CHECKED_ROLES.get(local - 6).ok_or_else(invalid)?;
                if role.local() as usize != local
                    || role.constructor_count() != shape.constructors.len()
                {
                    return Err(invalid());
                }
            }
            let range = coordinates(offset, offset + declaration.len()).ok_or_else(invalid)?;
            let id = NominalTypeId::new(module, u32::try_from(local).map_err(|_| invalid())?);
            if authenticate_nominal(registry, source, id, declaration, range, shape, work)? {
                materialized += 1;
                constructors += shape.constructors.len();
            }
            local += 1;
            offset += end;
        } else {
            offset += rest.find('\n').map_or(rest.len(), |end| end + 1);
        }
    }
    if local != SHAPES.len() {
        return Err(invalid());
    }
    reject_extra_roles(registry, module, source, materialized, constructors, work)?;
    let host = registry
        .effect(EffectId::new(
            module,
            crate::module::FOREIGN_NATIVE_HOST_LOCAL,
        ))
        .ok_or_else(invalid)?;
    if !host_matches(host, registry, module, source, work)? {
        return Err(invalid());
    }
    let call = NominalTypeId::new(module, Role::CheckedCall.local());
    Ok(CheckedForeignBuiltinFacts {
        module,
        source,
        native_host: host.id,
        checked_call: call,
        returned: ConstructorId::new(call, 0),
        conversion_failed: ConstructorId::new(call, 1),
        boundary_failed: ConstructorId::new(call, 2),
    })
}

/// Malformed candidates are false; exhausted checking remains a resource error.
/// Callers must reject a reserved-role candidate on false, including nonempty APIs.
pub(crate) fn is_canonical_native_host(
    effect: &ResolvedEffectDeclaration,
    registry: &ResolvedRegistry,
    work: &mut TypeWorkBudget,
) -> Result<bool, ForeignAdmissionError> {
    charge(work, 1, effect.span)?;
    if !effect.id.module().is_builtin_foreign()
        || effect.id.declaration() != crate::module::FOREIGN_NATIVE_HOST_LOCAL
    {
        return Ok(false);
    }
    match authenticate_checked_builtins(registry, effect.id.module(), effect.span, work) {
        Ok(facts) => host_matches(effect, registry, facts.module, facts.source, work),
        Err(error) if error.is_resource_exhaustion() => Err(error),
        Err(_) => Ok(false),
    }
}

// Independent expected payload shapes, in original nominal order. This checks
// canonical data roles; it is not a native binding or dispatch inventory.
enum Payload {
    Int,
    Bool,
    String,
    Variable(u32),
    Nominal(u32),
    Apply(u32, u32),
    Tuple(&'static [Payload]),
}
struct NominalShape {
    formals: &'static [u32],
    constructors: &'static [Option<Payload>],
}
const CHECKED_ROLES: &[Role] = &[
    Role::NativeStatus,
    Role::NativeFact,
    Role::DiagnosticAbsence,
    Role::Diagnostic,
    Role::BoundaryRecord,
    Role::BoundaryFailure,
    Role::CheckedCall,
    Role::FinishResult,
    Role::CheckedFinish,
    Role::CheckedCompletion,
    Role::CheckedScope,
    Role::ViolationCause,
];
const SHAPES: &[NominalShape] = &[
    NominalShape {
        formals: &[],
        constructors: &[None],
    },
    NominalShape {
        formals: &[0],
        constructors: &[Some(Payload::Variable(0)), Some(Payload::Nominal(0))],
    },
    NominalShape {
        formals: &[1],
        constructors: &[None, Some(Payload::Variable(1))],
    },
    NominalShape {
        formals: &[2],
        constructors: &[None, Some(Payload::Variable(2))],
    },
    NominalShape {
        formals: &[3],
        constructors: &[Some(Payload::Variable(3)), Some(Payload::Variable(3)), None],
    },
    NominalShape {
        formals: &[4],
        constructors: &[None],
    },
    NominalShape {
        formals: &[],
        constructors: &[None, Some(Payload::Int)],
    },
    NominalShape {
        formals: &[],
        constructors: &[None, None, None, None],
    },
    NominalShape {
        formals: &[],
        constructors: &[None, None, None, None, None, None],
    },
    NominalShape {
        formals: &[],
        constructors: &[Some(Payload::Nominal(8)), Some(Payload::String)],
    },
    NominalShape {
        formals: &[],
        constructors: &[Some(Payload::Tuple(&[
            Payload::Nominal(6),
            Payload::Nominal(7),
            Payload::Bool,
            Payload::Nominal(9),
        ]))],
    },
    NominalShape {
        formals: &[],
        constructors: &[
            Some(Payload::Nominal(10)),
            Some(Payload::Nominal(10)),
            Some(Payload::Nominal(10)),
        ],
    },
    NominalShape {
        formals: &[14],
        constructors: &[
            Some(Payload::Variable(14)),
            Some(Payload::Nominal(0)),
            Some(Payload::Nominal(11)),
        ],
    },
    NominalShape {
        formals: &[15],
        constructors: &[None, Some(Payload::Variable(15))],
    },
    NominalShape {
        formals: &[16, 17],
        constructors: &[
            Some(Payload::Apply(13, 17)),
            Some(Payload::Tuple(&[
                Payload::Variable(16),
                Payload::Variable(17),
            ])),
            Some(Payload::Nominal(11)),
        ],
    },
    NominalShape {
        formals: &[18],
        constructors: &[
            Some(Payload::Tuple(&[
                Payload::Apply(13, 18),
                Payload::Nominal(10),
            ])),
            Some(Payload::Tuple(&[
                Payload::Variable(18),
                Payload::Nominal(10),
            ])),
            Some(Payload::Nominal(11)),
        ],
    },
    NominalShape {
        formals: &[19, 20, 21],
        constructors: &[
            Some(Payload::Variable(20)),
            Some(Payload::Tuple(&[
                Payload::Variable(19),
                Payload::Apply(15, 21),
            ])),
        ],
    },
    NominalShape {
        formals: &[],
        constructors: &[
            Some(Payload::Int),
            Some(Payload::Int),
            None,
            Some(Payload::Int),
            Some(Payload::Tuple(&[Payload::Int, Payload::Int])),
        ],
    },
];
fn coordinates(start: usize, end: usize) -> Option<ByteRange> {
    ByteRange::new(u32::try_from(start).ok()?, u32::try_from(end).ok()?).ok()
}
fn original(origin: &Origin, source: Span, range: ByteRange) -> bool {
    matches!(origin, Origin::Source(span) if span.source() == source.source() && span.range() == range)
}
impl Payload {
    // Recursion follows the finite trusted pattern, never untrusted Type depth.
    fn matches(
        &self,
        value: &Type,
        module: ModuleId,
        source: Span,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ForeignAdmissionError> {
        charge(work, 1, source)?;
        Ok(match (self, value) {
            (Self::Int, Type::Int) | (Self::Bool, Type::Bool) | (Self::String, Type::String) => {
                true
            }
            (Self::Variable(local), Type::Variable(id)) => {
                *id == TypeVariableId::resolved(module, *local)
            }
            (Self::Nominal(local), Type::Nominal(id)) => *id == NominalTypeId::new(module, *local),
            (Self::Apply(owner, formal), Type::Application(function, argument)) => {
                matches!(function.as_ref(), Type::Nominal(id) if *id == NominalTypeId::new(module, *owner))
                    && matches!(argument.as_ref(), Type::Variable(id) if *id == TypeVariableId::resolved(module, *formal))
            }
            (Self::Tuple(expected), Type::Tuple(actual)) if expected.len() == actual.len() => {
                for (shape, field) in expected.iter().zip(actual.iter()) {
                    if !shape.matches(field, module, source, work)? {
                        return Ok(false);
                    }
                }
                true
            }
            _ => false,
        })
    }
}

fn authenticate_nominal(
    registry: &ResolvedRegistry,
    source: Span,
    id: NominalTypeId,
    declaration: &str,
    range: ByteRange,
    shape: &NominalShape,
    work: &mut TypeWorkBudget,
) -> Result<bool, ForeignAdmissionError> {
    let module = id.module();
    let invalid = || failure(ForeignAdmissionReason::InvalidCodec, source);
    charge(work, 5, source)?;
    let Some(nominal) = registry.nominal(id) else {
        let kind_matches = match (id.declaration(), registry.nominal_kind(id)) {
            (
                0,
                Some(CanonicalNominalKind::Frozen {
                    kind: Kind::Type,
                    origin,
                }),
            ) => origin.source() == source.source() && origin.range() == range,
            (
                5,
                Some(CanonicalNominalKind::Frozen {
                    kind: Kind::Arrow(argument, result),
                    origin,
                }),
            ) => {
                argument.as_ref() == &Kind::Type
                    && result.as_ref() == &Kind::Type
                    && origin.source() == source.source()
                    && origin.range() == range
            }
            _ => false,
        };
        return if kind_matches {
            Ok(false)
        } else {
            Err(invalid())
        };
    };
    if nominal.id != id
        || nominal.declaration_kind != ResolvedNominalDeclarationKind::Data
        || nominal.representation.is_some()
        || nominal.representation_provenance.is_some()
        || !original(&nominal.origin, source, range)
        || nominal.constructors.len() != shape.constructors.len()
    {
        return Err(invalid());
    }
    let parameters = registry.nominal_parameters(id).unwrap_or(&[]);
    if parameters.len() != shape.formals.len() {
        return Err(invalid());
    }
    let declaration_start = usize::try_from(range.start()).map_err(|_| invalid())?;
    for (position, (parameter, local)) in parameters.iter().zip(shape.formals).enumerate() {
        charge(work, 3, source)?;
        let offset =
            declaration_start + declaration.find('<').ok_or_else(invalid)? + 1 + position * 3;
        let formal = coordinates(offset, offset + 1).ok_or_else(invalid)?;
        let canonical = registry
            .type_variable(TypeVariableId::resolved(module, *local))
            .ok_or_else(invalid)?;
        if parameter.id != canonical.id
            || canonical.id != TypeVariableId::resolved(module, *local)
            || parameter.kind != Kind::Type
            || canonical.kind != Kind::Type
            || !original(&parameter.origin, source, formal)
            || !original(&canonical.origin, source, formal)
        {
            return Err(invalid());
        }
    }
    let equal = declaration.find('=').ok_or_else(invalid)?;
    let mut constructor_start = declaration_start + equal + 1;
    let mut count = 0;
    for (ordinal, raw) in declaration[equal + 1..].split('|').enumerate() {
        charge(work, 3, source)?;
        let expected = shape.constructors.get(ordinal).ok_or_else(invalid)?;
        let trimmed = raw.trim();
        let start = constructor_start + raw.len() - raw.trim_start().len();
        let constructor_range = coordinates(start, start + trimmed.len()).ok_or_else(invalid)?;
        let identity = ConstructorId::new(id, u32::try_from(ordinal).map_err(|_| invalid())?);
        let constructor = registry.constructor(identity).ok_or_else(invalid)?;
        if nominal.constructors[ordinal] != identity
            || constructor.id != identity
            || constructor.owner != id
            || !original(&constructor.origin, source, constructor_range)
        {
            return Err(invalid());
        }
        match (expected, constructor.payload.as_ref()) {
            (None, None) => {}
            (Some(expected), Some(actual)) if expected.matches(actual, module, source, work)? => {}
            _ => return Err(invalid()),
        }
        constructor_start += raw.len() + 1;
        count += 1;
    }
    if count != shape.constructors.len() {
        return Err(invalid());
    }
    Ok(true)
}

fn reject_extra_roles(
    registry: &ResolvedRegistry,
    module: ModuleId,
    source: Span,
    expected_nominals: usize,
    expected_constructors: usize,
    work: &mut TypeWorkBudget,
) -> Result<(), ForeignAdmissionError> {
    let invalid = || failure(ForeignAdmissionReason::InvalidCodec, source);
    charge(work, registry.nominals().len(), source)?;
    let mut nominals = 0;
    for nominal in registry
        .nominals()
        .iter()
        .filter(|value| value.id.module() == module)
    {
        if nominal.id.is_lexical() || nominal.id.declaration() >= SHAPES.len() as u32 {
            return Err(invalid());
        }
        nominals += 1;
    }
    charge(work, registry.constructors().len(), source)?;
    let mut constructors = 0;
    for constructor in registry
        .constructors()
        .iter()
        .filter(|value| value.id.owner().module() == module || value.owner.module() == module)
    {
        if constructor.owner != constructor.id.owner()
            || constructor.owner.module() != module
            || registry.nominal(constructor.owner).is_none()
        {
            return Err(invalid());
        }
        constructors += 1;
    }
    charge(work, registry.lexical_nominals().len(), source)?;
    charge(work, registry.lexical_constructors().len(), source)?;
    charge(work, registry.abstract_nominal_kind_count(), source)?;
    if registry
        .lexical_nominals()
        .iter()
        .any(|value| value.id.module() == module)
        || registry
            .lexical_constructors()
            .iter()
            .any(|value| value.id.owner().module() == module || value.owner.module() == module)
    {
        return Err(invalid());
    }
    for (id, _, _) in registry
        .abstract_nominal_kind_entries()
        .filter(|(id, _, _)| id.module() == module)
    {
        if !matches!(id.declaration(), 0 | 5) || id.is_lexical() || registry.nominal(id).is_some() {
            return Err(invalid());
        }
    }
    for (id, _) in registry.nominal_parameter_entries() {
        charge(work, 1, source)?;
        if id.module() == module && registry.nominal(id).is_none() {
            return Err(invalid());
        }
    }
    charge(work, registry.effects().len(), source)?;
    let mut effects = 0;
    for effect in registry
        .effects()
        .iter()
        .filter(|value| value.id.module() == module)
    {
        if effect.id.declaration() != crate::module::FOREIGN_NATIVE_HOST_LOCAL {
            return Err(invalid());
        }
        effects += 1;
    }
    if nominals != expected_nominals || constructors != expected_constructors || effects != 1 {
        return Err(invalid());
    }
    Ok(())
}

/// Checks a body-free original declaration after defining-source byte admission.
/// Full call admission separately reconstructs the referenced codec inventory.
pub(crate) fn is_canonical_native_host_declaration(
    effect: &ResolvedEffectDeclaration,
    source: Span,
    work: &mut TypeWorkBudget,
) -> Result<bool, ForeignAdmissionError> {
    charge(work, foreign_builtin_source_text().len() + 6, source)?;
    let Some((anchor, name, formal)) = foreign_native_host_ranges(source) else {
        return Ok(false);
    };
    let module = effect.id.module();
    if !module.is_builtin_foreign()
        || effect.id != EffectId::new(module, crate::module::FOREIGN_NATIVE_HOST_LOCAL)
        || !effect.public
        || effect.native_contract.is_some()
        || !effect.operations.is_empty()
        || effect.parameters.len() != 1
        || effect.span != source
        || effect.span.range() != anchor
        || !original(&effect.origin, source, name)
    {
        return Ok(false);
    }
    let parameter = &effect.parameters[0];
    Ok(parameter.id == TypeVariableId::resolved(module, 22)
        && parameter.kind == Kind::Type
        && original(&parameter.origin, source, formal))
}

fn host_matches(
    effect: &ResolvedEffectDeclaration,
    registry: &ResolvedRegistry,
    module: ModuleId,
    source: Span,
    work: &mut TypeWorkBudget,
) -> Result<bool, ForeignAdmissionError> {
    if !is_canonical_native_host_declaration(effect, source, work)? {
        return Ok(false);
    }
    charge(work, 2, source)?;
    let Some(canonical) = registry.type_variable(TypeVariableId::resolved(module, 22)) else {
        return Ok(false);
    };
    let Some((_, _, formal)) = foreign_native_host_ranges(source) else {
        return Ok(false);
    };
    Ok(effect.id.module() == module
        && canonical.id == TypeVariableId::resolved(module, 22)
        && canonical.kind == Kind::Type
        && original(&canonical.origin, source, formal))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        module::{ModuleRoots, load_module_graph},
        source::Origin,
        types::{Type, TypeVariableId},
    };
    use std::{
        fs,
        sync::{
            Arc,
            atomic::{AtomicUsize, Ordering},
        },
    };

    fn original() -> (Arc<ResolvedRegistry>, ModuleId, Span) {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let directory = std::env::temp_dir().join(format!(
            "ash-checked-builtin-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&directory).unwrap();
        let entry = directory.join("entry.ash");
        fs::write(
            &entry,
            "import @builtin.foreign as Foreign\nmain : Unit -> Int\nmain () = 42\n",
        )
        .unwrap();
        let graph = load_module_graph(&entry, &ModuleRoots::empty()).unwrap();
        fs::remove_dir_all(directory).unwrap();
        let loaded = graph
            .modules()
            .iter()
            .find(|module| module.id().is_builtin_foreign())
            .unwrap();
        let resolved = crate::resolve::resolve_checked_foreign_module(loaded, &[])
            .expect("canonical builtin module resolves");
        (
            Arc::clone(resolved.registry()),
            loaded.id(),
            loaded.surface().span,
        )
    }

    type NominalFacts = Vec<crate::resolved::ResolvedNominalType>;
    type ConstructorFacts = Vec<crate::resolved::ResolvedConstructor>;
    type NominalRows = Vec<(NominalTypeId, Vec<crate::resolved::ResolvedTypeVariable>)>;

    fn mutate(
        registry: &ResolvedRegistry,
        edit: impl FnOnce(
            &mut NominalFacts,
            &mut ConstructorFacts,
            &mut Vec<ResolvedEffectDeclaration>,
            &mut NominalRows,
        ),
    ) -> ResolvedRegistry {
        let mut nominals = registry.nominals().to_vec();
        let mut constructors = registry.constructors().to_vec();
        let mut effects = registry.effects().to_vec();
        let mut parameters = nominals
            .iter()
            .map(|nominal| {
                (
                    nominal.id,
                    registry
                        .nominal_parameters(nominal.id)
                        .unwrap_or(&[])
                        .to_vec(),
                )
            })
            .collect();
        edit(
            &mut nominals,
            &mut constructors,
            &mut effects,
            &mut parameters,
        );
        ResolvedRegistry::new(nominals, constructors)
            .with_type_parameters(parameters)
            .with_additional_type_variables(registry.type_variables().cloned())
            .with_effects(effects)
    }

    #[test]
    fn checked_builtin_full_original_inventory_authenticates_at_exact_work() {
        let (registry, module, source) = original();
        let mut work = TypeWorkBudget::default();
        let facts = authenticate_checked_builtins(&registry, module, source, &mut work).unwrap();
        assert_eq!(facts.module(), module);
        assert_eq!(facts.source(), source);
        assert_eq!(facts.native_host(), EffectId::new(module, 0));
        assert_eq!(facts.checked_call(), NominalTypeId::new(module, 12));
        assert_eq!(
            facts.returned(),
            ConstructorId::new(facts.checked_call(), 0)
        );
        assert_eq!(
            facts.conversion_failed(),
            ConstructorId::new(facts.checked_call(), 1)
        );
        assert_eq!(
            facts.boundary_failed(),
            ConstructorId::new(facts.checked_call(), 2)
        );
        let required = work.used();
        assert!(required > 0);
        for allowance in [required - 1, required, required] {
            let result = authenticate_checked_builtins(
                &registry,
                module,
                source,
                &mut TypeWorkBudget::with_limit(allowance),
            );
            if allowance < required {
                assert!(result.unwrap_err().is_resource_exhaustion());
            } else {
                assert_eq!(result.unwrap(), facts);
            }
        }
        assert!(
            is_canonical_native_host(
                registry.effect(facts.native_host()).unwrap(),
                &registry,
                &mut TypeWorkBudget::default()
            )
            .unwrap()
        );
    }

    #[test]
    fn checked_builtin_reconstruction_rejects_donor_payload_origin_and_formals() {
        let (registry, module, source) = original();
        assert!(
            authenticate_checked_builtins(
                &registry,
                ModuleId::new(7),
                source,
                &mut TypeWorkBudget::default()
            )
            .is_err()
        );
        for mutation in 0..9 {
            let changed =
                mutate(
                    &registry,
                    |nominals, constructors, effects, parameters| match mutation {
                        0 => {
                            constructors
                                .iter_mut()
                                .find(|value| {
                                    value.id
                                        == ConstructorId::new(NominalTypeId::new(module, 12), 2)
                                })
                                .unwrap()
                                .payload = Some(Type::Int)
                        }
                        1 => {
                            let wrong = constructors
                                .iter()
                                .find(|value| {
                                    value.id
                                        == ConstructorId::new(NominalTypeId::new(module, 12), 0)
                                })
                                .unwrap()
                                .origin
                                .clone();
                            constructors
                                .iter_mut()
                                .find(|value| {
                                    value.id
                                        == ConstructorId::new(NominalTypeId::new(module, 12), 2)
                                })
                                .unwrap()
                                .origin = wrong;
                        }
                        2 => {
                            parameters
                                .iter_mut()
                                .find(|(owner, _)| *owner == NominalTypeId::new(module, 12))
                                .unwrap()
                                .1[0]
                                .id = TypeVariableId::resolved(module, 15)
                        }
                        3 => effects[0].parameters[0].id = TypeVariableId::resolved(module, 21),
                        4 => nominals
                            .iter_mut()
                            .find(|value| value.id == NominalTypeId::new(module, 11))
                            .unwrap()
                            .constructors
                            .swap(0, 1),
                        5 => {
                            let mut extra = effects[0].clone();
                            extra.id = EffectId::new(module, 1);
                            effects.push(extra);
                        }
                        6 => {
                            let mut extra = nominals.last().unwrap().clone();
                            extra.id = NominalTypeId::new(module, 18);
                            nominals.push(extra);
                        }
                        7 => {
                            let mut extra = constructors
                                .iter()
                                .find(|value| {
                                    value.id
                                        == ConstructorId::new(NominalTypeId::new(module, 12), 2)
                                })
                                .unwrap()
                                .clone();
                            extra.id = ConstructorId::new(extra.owner, 3);
                            constructors.push(extra);
                        }
                        8 => nominals.retain(|value| value.id != NominalTypeId::new(module, 7)),
                        _ => unreachable!(),
                    },
                );
            assert!(
                authenticate_checked_builtins(
                    &changed,
                    module,
                    source,
                    &mut TypeWorkBudget::default()
                )
                .is_err(),
                "mutation {mutation}"
            );
        }
        let effect = registry.effect(EffectId::new(module, 0)).unwrap();
        let mut wrong = effect.clone();
        wrong.origin = Origin::Source(source);
        assert!(
            !is_canonical_native_host(&wrong, &registry, &mut TypeWorkBudget::default()).unwrap()
        );
    }

    #[test]
    fn checked_builtin_display_aliases_preserve_roles_but_not_forged_declarations() {
        let (registry, module, source) = original();
        let aliased = mutate(&registry, |nominals, constructors, effects, _| {
            for nominal in nominals {
                nominal.spelling = "Alias".to_owned();
            }
            for constructor in constructors {
                constructor.spelling = "Alias".to_owned();
            }
            effects[0].spelling = "HostAlias".to_owned();
        });
        assert!(
            authenticate_checked_builtins(&aliased, module, source, &mut TypeWorkBudget::default())
                .is_ok()
        );
        let mut host = registry.effect(EffectId::new(module, 0)).unwrap().clone();
        assert!(
            is_canonical_native_host_declaration(&host, source, &mut TypeWorkBudget::default())
                .unwrap()
        );
        assert!(
            is_canonical_native_host_declaration(&host, source, &mut TypeWorkBudget::with_limit(0))
                .unwrap_err()
                .is_resource_exhaustion()
        );
        host.parameters[0].kind = Kind::EffectRow;
        assert!(
            !is_canonical_native_host_declaration(&host, source, &mut TypeWorkBudget::default())
                .unwrap()
        );
    }
}
