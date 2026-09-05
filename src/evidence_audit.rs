//! Structural evidence validation at the checked-body transition.

use crate::{
    interface::{ConstrainedScheme, EvidenceSlot, InterfaceConstraintBudget, MethodId},
    resolved::{
        BinderId, ResolvedBlock, ResolvedDefinition, ResolvedDefinitionKind, ResolvedExpr,
        ResolvedExprKind, ResolvedImplementation, ResolvedLocalDeclaration, ResolvedOccurrence,
        ResolvedTermName,
    },
};

/// Failure while authenticating structural evidence before checked wrapping.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum EvidenceAuditFailure {
    /// A resolved occurrence does not carry exactly its checked evidence.
    InvalidState,
    /// Traversal exceeded the graph-wide interface and constraint work bound.
    ConstraintResource,
}

/// Authenticates every occurrence-owned evidence slot before body type-state changes.
///
/// A global occurrence owns one slot per requirement in its checked scheme. A
/// lexical or unconstrained global is absent from `global_scheme` and owns no
/// slots. A known interface method owns exactly one slot. Every expected slot
/// must be authenticated by the caller's staged-publication membership; the
/// audit does not require the one-shot slot to be filled yet.
pub(crate) fn audit_checked_body_evidence<'a, G, M, S>(
    definitions: &[ResolvedDefinition],
    implementations: &[ResolvedImplementation],
    mut global_scheme: G,
    mut method_known: M,
    mut slot_ready: S,
    budget: &mut InterfaceConstraintBudget,
) -> Result<(), EvidenceAuditFailure>
where
    G: FnMut(BinderId) -> Option<&'a ConstrainedScheme>,
    M: FnMut(MethodId) -> bool,
    S: FnMut(&EvidenceSlot, Option<MethodId>) -> bool,
{
    let mut pending = Vec::new();

    for definition in definitions {
        budget
            .charge(1)
            .map_err(|()| EvidenceAuditFailure::ConstraintResource)?;
        match &definition.kind {
            ResolvedDefinitionKind::Equational(global) => {
                reserve_and_push_equations(&mut pending, &global.equations, budget)?;
            }
            ResolvedDefinitionKind::InlineOperational(global) => {
                push_block(&mut pending, &global.body, budget)?;
            }
        }
    }
    for implementation in implementations {
        budget
            .charge(1)
            .map_err(|()| EvidenceAuditFailure::ConstraintResource)?;
        for group in &implementation.method_groups {
            budget
                .charge(1)
                .map_err(|()| EvidenceAuditFailure::ConstraintResource)?;
            reserve_and_push_equations(&mut pending, &group.equations, budget)?;
        }
    }

    while let Some(expression) = pending.pop() {
        budget
            .charge(1)
            .map_err(|()| EvidenceAuditFailure::ConstraintResource)?;
        match &expression.kind {
            ResolvedExprKind::Integer(_)
            | ResolvedExprKind::Boolean(_)
            | ResolvedExprKind::Unit
            | ResolvedExprKind::Constructor(_) => {}
            ResolvedExprKind::Occurrence(occurrence) => {
                audit_occurrence(
                    occurrence,
                    &mut global_scheme,
                    &mut method_known,
                    &mut slot_ready,
                    budget,
                )?;
            }
            ResolvedExprKind::Tuple(elements) => {
                reserve_and_extend(&mut pending, elements.iter(), budget)?;
            }
            ResolvedExprKind::Apply(application) => {
                reserve_and_extend(
                    &mut pending,
                    [application.function.as_ref(), application.argument.as_ref()],
                    budget,
                )?;
            }
            ResolvedExprKind::Add(binary)
            | ResolvedExprKind::Multiply(binary)
            | ResolvedExprKind::Equal(binary) => {
                reserve_and_extend(
                    &mut pending,
                    [binary.left.as_ref(), binary.right.as_ref()],
                    budget,
                )?;
            }
            ResolvedExprKind::Block(block) => push_block(&mut pending, block, budget)?,
            ResolvedExprKind::Function(function) => {
                push_block(&mut pending, &function.body, budget)?;
            }
            ResolvedExprKind::Match(matched) => {
                let additional = matched
                    .arms
                    .len()
                    .checked_add(1)
                    .ok_or(EvidenceAuditFailure::ConstraintResource)?;
                reserve_work(&mut pending, additional, budget)?;
                pending.push(matched.scrutinee.as_ref());
                pending.extend(matched.arms.iter().map(|arm| &arm.body));
            }
            ResolvedExprKind::Perform(request) => pending.push(&request.operand),
            ResolvedExprKind::Handle(handler) => {
                reserve_and_extend(
                    &mut pending,
                    handler.clauses.iter().map(|clause| &clause.body),
                    budget,
                )?;
                reserve_and_extend(&mut pending, std::iter::once(handler.body.as_ref()), budget)?;
            }
            ResolvedExprKind::Resume(resume) => pending.push(&resume.value),
        }
    }
    Ok(())
}

fn audit_occurrence<'a, G, M, S>(
    occurrence: &ResolvedOccurrence,
    global_scheme: &mut G,
    method_known: &mut M,
    slot_ready: &mut S,
    budget: &mut InterfaceConstraintBudget,
) -> Result<(), EvidenceAuditFailure>
where
    G: FnMut(BinderId) -> Option<&'a ConstrainedScheme>,
    M: FnMut(MethodId) -> bool,
    S: FnMut(&EvidenceSlot, Option<MethodId>) -> bool,
{
    budget
        .charge(1)
        .map_err(|()| EvidenceAuditFailure::ConstraintResource)?;
    let (expected, checked_method) = match occurrence.term {
        ResolvedTermName::Global(binder) => (
            global_scheme(binder).map_or(0, |scheme| scheme.requirements.len()),
            None,
        ),
        ResolvedTermName::Method(method) => {
            if !method_known(method) {
                return Err(EvidenceAuditFailure::InvalidState);
            }
            (1, Some(method))
        }
    };
    budget
        .charge(expected)
        .map_err(|()| EvidenceAuditFailure::ConstraintResource)?;
    if occurrence.evidence.len() != expected
        || occurrence
            .evidence
            .iter()
            .any(|slot| !slot_ready(slot, checked_method))
    {
        return Err(EvidenceAuditFailure::InvalidState);
    }
    Ok(())
}

fn reserve_and_push_equations<'a>(
    pending: &mut Vec<&'a ResolvedExpr>,
    equations: &'a [crate::resolved::ResolvedEquation],
    budget: &mut InterfaceConstraintBudget,
) -> Result<(), EvidenceAuditFailure> {
    reserve_and_extend(
        pending,
        equations.iter().map(|equation| &equation.body),
        budget,
    )
}

fn push_block<'a>(
    pending: &mut Vec<&'a ResolvedExpr>,
    block: &'a ResolvedBlock,
    budget: &mut InterfaceConstraintBudget,
) -> Result<(), EvidenceAuditFailure> {
    let mut additional = 1usize;
    for declaration in &block.declarations {
        budget
            .charge(1)
            .map_err(|()| EvidenceAuditFailure::ConstraintResource)?;
        let initializers = match declaration {
            ResolvedLocalDeclaration::Evidence(source) => source
                .method_groups
                .iter()
                .map(|group| group.equations.len())
                .sum(),
            ResolvedLocalDeclaration::Binding(_) => 1,
            ResolvedLocalDeclaration::Recursive(group) => group.members.len(),
            ResolvedLocalDeclaration::Newtype(_) => 0,
        };
        additional = additional
            .checked_add(initializers)
            .ok_or(EvidenceAuditFailure::ConstraintResource)?;
    }
    reserve_work(pending, additional, budget)?;
    pending.push(block.result.as_ref());
    for declaration in &block.declarations {
        match declaration {
            ResolvedLocalDeclaration::Evidence(source) => {
                pending.extend(
                    source
                        .method_groups
                        .iter()
                        .flat_map(|group| group.equations.iter().map(|equation| &equation.body)),
                );
            }
            ResolvedLocalDeclaration::Binding(binding) => pending.push(&binding.initializer),
            ResolvedLocalDeclaration::Recursive(group) => {
                pending.extend(group.members.iter().map(|member| &member.initializer));
            }
            ResolvedLocalDeclaration::Newtype(_) => {}
        }
    }
    Ok(())
}

fn reserve_and_extend<'a, I>(
    pending: &mut Vec<&'a ResolvedExpr>,
    expressions: I,
    budget: &mut InterfaceConstraintBudget,
) -> Result<(), EvidenceAuditFailure>
where
    I: IntoIterator<Item = &'a ResolvedExpr>,
    I::IntoIter: ExactSizeIterator,
{
    let expressions = expressions.into_iter();
    reserve_work(pending, expressions.len(), budget)?;
    pending.extend(expressions);
    Ok(())
}

fn reserve_work<T>(
    pending: &mut Vec<T>,
    additional: usize,
    budget: &mut InterfaceConstraintBudget,
) -> Result<(), EvidenceAuditFailure> {
    budget
        .charge(additional)
        .map_err(|()| EvidenceAuditFailure::ConstraintResource)?;
    pending
        .try_reserve(additional)
        .map_err(|_| EvidenceAuditFailure::ConstraintResource)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        interface::{
            CheckedRequirement, EvidenceSelectionBuilder, EvidenceSlot, InterfaceApplication,
            InterfaceId, RequirementId, RequirementOwner,
        },
        module::ModuleId,
        resolved::{
            Binder, ResolvedApplicationExpr, ResolvedEquation, ResolvedEquationHead,
            ResolvedEquationalGlobal, ResolvedExternalInterface, ResolvedImplementationMethodGroup,
            ResolvedInterfaceApplication, ResolvedInterfaceOccurrence, ResolvedType,
            ResolvedTypeProvenance, ResolvedTypeProvenanceNode,
        },
        source::{ByteRange, Origin, SourceFile, Span},
        types::Type,
    };

    fn fixture_span() -> Span {
        let source =
            SourceFile::new("evidence-audit.ash", "body").expect("the audit fixture should fit");
        source
            .span(ByteRange::new(0, 4).expect("the fixture range should be ordered"))
            .expect("the fixture range should belong to the source")
    }

    fn selected_slot(module: ModuleId) -> EvidenceSlot {
        let slot = EvidenceSlot::empty();
        let requirement =
            RequirementId::new(RequirementOwner::Global(BinderId::resolved(module, 0)), 0);
        let mut builder = EvidenceSelectionBuilder::new();
        let root = builder
            .push_abstract(requirement, &[], &mut InterfaceConstraintBudget::default())
            .expect("the tiny selection should fit");
        let selection = builder
            .finish(
                root,
                InterfaceApplication::new(InterfaceId::new(module, 0), Box::new([Type::Int])),
            )
            .expect("the root should exist");
        slot.handle()
            .fill(
                None,
                InterfaceApplication::new(InterfaceId::new(module, 0), Box::new([Type::Int])),
                Box::new([]),
                None,
                selection,
            )
            .expect("the fresh slot should accept evidence");
        slot
    }

    fn occurrence(term: ResolvedTermName, evidence: Vec<EvidenceSlot>, span: Span) -> ResolvedExpr {
        ResolvedExpr {
            kind: ResolvedExprKind::Occurrence(ResolvedOccurrence {
                term,
                spelling: "value".into(),
                origin: Origin::Source(span),
                import_span: None,
                evidence: evidence.into_boxed_slice(),
            }),
            span,
        }
    }

    fn definition(body: ResolvedExpr, binder: BinderId, span: Span) -> ResolvedDefinition {
        ResolvedDefinition {
            kind: ResolvedDefinitionKind::Equational(ResolvedEquationalGlobal {
                interface: ResolvedExternalInterface {
                    name: Binder {
                        id: binder,
                        spelling: "main".into(),
                        origin: Origin::Source(span),
                    },
                    annotation: ResolvedType {
                        ty: Type::Unit,
                        provenance: ResolvedTypeProvenance::new(
                            vec![ResolvedTypeProvenanceNode::Fact(span)],
                            0,
                        ),
                        origin: Origin::Source(span),
                        span,
                    },
                    requirements: Box::new([]),
                    type_parameters: Box::new([]),
                    span,
                },
                equations: vec![ResolvedEquation {
                    name: ResolvedEquationHead {
                        binder,
                        spelling: "main".into(),
                        origin: Origin::Source(span),
                    },
                    patterns: Vec::new(),
                    body,
                    span,
                }],
            }),
            span,
        }
    }

    fn constrained_scheme(
        interface: InterfaceId,
        owner: BinderId,
        span: Span,
    ) -> ConstrainedScheme {
        ConstrainedScheme {
            type_parameters: Box::new([]),
            requirements: vec![CheckedRequirement {
                id: RequirementId::new(RequirementOwner::Global(owner), 0),
                application: InterfaceApplication::new(interface, Box::new([Type::Unit])),
                origin: Origin::Source(span),
                span,
            }]
            .into_boxed_slice(),
            value_type: Type::Unit,
        }
    }

    fn implementation(body: ResolvedExpr, module: ModuleId, span: Span) -> ResolvedImplementation {
        let interface = InterfaceId::new(module, 0);
        let method = MethodId::new(interface, 0);
        let implementation = crate::interface::ImplId::new(module, 0);
        let binder = BinderId::resolved(module, 10);
        ResolvedImplementation {
            id: implementation,
            public: false,
            head: ResolvedInterfaceApplication {
                interface: ResolvedInterfaceOccurrence {
                    id: interface,
                    spelling: "Show".into(),
                    origin: Origin::Source(span),
                },
                arguments: vec![ResolvedType {
                    ty: Type::Unit,
                    provenance: ResolvedTypeProvenance::new(
                        vec![ResolvedTypeProvenanceNode::Fact(span)],
                        0,
                    ),
                    origin: Origin::Source(span),
                    span,
                }]
                .into_boxed_slice(),
                span,
            },
            head_parameters: Box::new([]),
            prerequisite_only_parameters: Box::new([]),
            prerequisites: Box::new([]),
            method_groups: vec![ResolvedImplementationMethodGroup {
                contextual_parameters: Box::new([]),
                method: Some(method),
                identity: Some(crate::interface::ImplMethodId::new(implementation, method)),
                binder: Binder {
                    id: binder,
                    spelling: "show".into(),
                    origin: Origin::Source(span),
                },
                equations: vec![ResolvedEquation {
                    name: ResolvedEquationHead {
                        binder,
                        spelling: "show".into(),
                        origin: Origin::Source(span),
                    },
                    patterns: Vec::new(),
                    body,
                    span,
                }]
                .into_boxed_slice(),
                span,
            }]
            .into_boxed_slice(),
            span,
        }
    }

    #[test]
    fn accepts_filled_global_and_method_slots_and_unconstrained_occurrences() {
        let span = fixture_span();
        let module = ModuleId::new(31);
        let owner = BinderId::resolved(module, 0);
        let constrained = BinderId::resolved(module, 1);
        let lexical = BinderId::resolved(module, 2);
        let interface = InterfaceId::new(module, 0);
        let method = MethodId::new(interface, 0);
        let scheme = constrained_scheme(interface, constrained, span);
        let body = ResolvedExpr {
            kind: ResolvedExprKind::Tuple(vec![
                occurrence(
                    ResolvedTermName::Global(constrained),
                    vec![selected_slot(module)],
                    span,
                ),
                occurrence(ResolvedTermName::Global(lexical), Vec::new(), span),
                occurrence(
                    ResolvedTermName::Method(method),
                    vec![selected_slot(module)],
                    span,
                ),
            ]),
            span,
        };
        let definitions = [definition(body, owner, span)];

        assert_eq!(
            audit_checked_body_evidence(
                &definitions,
                &[],
                |binder| (binder == constrained).then_some(&scheme),
                |candidate| candidate == method,
                |slot, checked_method| {
                    slot.selection().is_some()
                        && (checked_method.is_none() || checked_method == Some(method))
                },
                &mut InterfaceConstraintBudget::default(),
            ),
            Ok(())
        );
    }

    #[test]
    fn rejects_empty_extra_unknown_method_and_malformed_global_slots() {
        let span = fixture_span();
        let module = ModuleId::new(32);
        let owner = BinderId::resolved(module, 0);
        let constrained = BinderId::resolved(module, 1);
        let interface = InterfaceId::new(module, 0);
        let method = MethodId::new(interface, 0);
        let scheme = constrained_scheme(interface, constrained, span);
        let cases = [
            occurrence(
                ResolvedTermName::Global(constrained),
                vec![EvidenceSlot::empty()],
                span,
            ),
            occurrence(
                ResolvedTermName::Global(owner),
                vec![selected_slot(module)],
                span,
            ),
            occurrence(
                ResolvedTermName::Method(method),
                vec![selected_slot(module)],
                span,
            ),
            occurrence(ResolvedTermName::Global(constrained), Vec::new(), span),
        ];

        for (index, body) in cases.into_iter().enumerate() {
            let definitions = [definition(body, owner, span)];
            let result = audit_checked_body_evidence(
                &definitions,
                &[],
                |binder| (binder == constrained).then_some(&scheme),
                |_| index != 2,
                |slot, _| slot.selection().is_some(),
                &mut InterfaceConstraintBudget::default(),
            );
            assert_eq!(result, Err(EvidenceAuditFailure::InvalidState));
        }
    }

    #[test]
    fn rejects_unfilled_evidence_nested_in_an_implementation_method_body() {
        let span = fixture_span();
        let module = ModuleId::new(35);
        let constrained = BinderId::resolved(module, 1);
        let interface = InterfaceId::new(module, 0);
        let scheme = constrained_scheme(interface, constrained, span);
        let implementations = [implementation(
            occurrence(
                ResolvedTermName::Global(constrained),
                vec![EvidenceSlot::empty()],
                span,
            ),
            module,
            span,
        )];

        assert_eq!(
            audit_checked_body_evidence(
                &[],
                &implementations,
                |binder| (binder == constrained).then_some(&scheme),
                |_| false,
                |slot, _| slot.selection().is_some(),
                &mut InterfaceConstraintBudget::default(),
            ),
            Err(EvidenceAuditFailure::InvalidState)
        );
    }

    #[test]
    fn audits_and_transitions_a_deep_body_on_a_small_stack() {
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(|| {
                let span = fixture_span();
                let module = ModuleId::new(33);
                let binder = BinderId::resolved(module, 0);
                let mut body = occurrence(ResolvedTermName::Global(binder), Vec::new(), span);
                for _ in 0..20_000 {
                    body = ResolvedExpr {
                        kind: ResolvedExprKind::Apply(ResolvedApplicationExpr {
                            function: Box::new(ResolvedExpr {
                                kind: ResolvedExprKind::Unit,
                                span,
                            }),
                            argument: Box::new(body),
                        }),
                        span,
                    };
                }
                let definitions = [definition(body, binder, span)];
                audit_checked_body_evidence(
                    &definitions,
                    &[],
                    |_| None,
                    |_| false,
                    |slot, _| slot.selection().is_some(),
                    &mut InterfaceConstraintBudget::default(),
                )
                .expect("the deep checked body should authenticate iteratively");
                drop(crate::resolved::CheckedDefinition::new(
                    definitions.into_iter().next().expect("one definition"),
                ));
            })
            .expect("the audit thread should start")
            .join()
            .expect("the audit and wrapper drop should remain stack safe");
    }

    #[test]
    fn traversal_budget_has_an_exact_boundary_before_checked_wrapping() {
        let span = fixture_span();
        let module = ModuleId::new(34);
        let binder = BinderId::resolved(module, 0);
        let short_definitions = [definition(
            occurrence(ResolvedTermName::Global(binder), Vec::new(), span),
            binder,
            span,
        )];

        assert_eq!(
            audit_checked_body_evidence(
                &short_definitions,
                &[],
                |_| None,
                |_| false,
                |slot, _| slot.selection().is_some(),
                &mut InterfaceConstraintBudget::with_limit(3),
            ),
            Err(EvidenceAuditFailure::ConstraintResource)
        );

        let exact_definitions = [definition(
            occurrence(ResolvedTermName::Global(binder), Vec::new(), span),
            binder,
            span,
        )];
        assert_eq!(
            audit_checked_body_evidence(
                &exact_definitions,
                &[],
                |_| None,
                |_| false,
                |slot, _| slot.selection().is_some(),
                &mut InterfaceConstraintBudget::with_limit(4),
            ),
            Ok(())
        );
    }

    #[test]
    fn rejects_staged_method_identity_that_differs_from_the_occurrence() {
        let span = fixture_span();
        let module = ModuleId::new(36);
        let owner = BinderId::resolved(module, 0);
        let interface = InterfaceId::new(module, 0);
        let first = MethodId::new(interface, 0);
        let second = MethodId::new(interface, 1);
        let definitions = [definition(
            occurrence(
                ResolvedTermName::Method(first),
                vec![selected_slot(module)],
                span,
            ),
            owner,
            span,
        )];

        assert_eq!(
            audit_checked_body_evidence(
                &definitions,
                &[],
                |_| None,
                |method| method == first,
                |slot, checked_method| {
                    slot.selection().is_some() && checked_method == Some(second)
                },
                &mut InterfaceConstraintBudget::default(),
            ),
            Err(EvidenceAuditFailure::InvalidState),
        );
    }
}
