//! Finite stored-value equations. All edges refer to static expressions or
//! slots; closure captures never contain recursively owned environments.

use std::collections::{HashMap, HashSet, VecDeque};

use super::{Failure, FunctionMetadataPreparation, MetadataVariables, charge, copy_slice, index};
use crate::{
    core::{
        PureComputation, PureExprKind, PureValue,
        data::{CorePattern, CorePatternKind},
        dialect::{CoreOperationFamily, StoredNode},
        effect::EffectOperation,
    },
    resolved::BinderId,
    source::Span,
    types::{ConstructorId, Type, TypeWorkBudget},
};

#[derive(Debug)]
enum Expr {
    Cleanup {
        body: usize,
        action: usize,
    },
    Scalar,
    Slot,
    Unknown,
    Alias(usize),
    Merge(Vec<usize>),
    Function {
        parameters: Vec<usize>,
        body: usize,
        captures: Vec<usize>,
    },
    Call {
        function: usize,
        arguments: Vec<usize>,
        scalar: bool,
        type_application: bool,
    },
    Tuple(Vec<usize>),
    Constructor(ConstructorId),
    Project {
        value: usize,
        field: usize,
        constructor: Option<ConstructorId>,
    },
    Bind {
        binder: usize,
        initializer: usize,
        body: usize,
    },
    Recursive {
        bindings: Vec<(usize, usize)>,
        body: usize,
    },
    Match {
        scrutinee: usize,
        arms: Vec<(Vec<(usize, usize)>, usize)>,
    },
    Resource {
        success: Option<ConstructorId>,
        failure: Option<ConstructorId>,
        handle: usize,
        identity: usize,
        initializer: usize,
        body: usize,
        source: Span,
    },
    Request {
        operand: usize,
        scalar: bool,
    },
    Resume {
        operand: usize,
    },
    Handler {
        body: usize,
        clauses: Vec<DataClause>,
    },
    Evidence {
        value: usize,
        bindings: Vec<(
            crate::interface::RequirementId,
            crate::interface::MethodId,
            usize,
        )>,
    },
}

/// Borrowed exact original pattern and projected clause body. Only the sealed
/// conditional capture builder supplies these inputs; they confer no execution.
pub(super) struct ConditionalClauseInput<'a> {
    pub(super) pattern: &'a CorePattern,
    pub(super) body: crate::core::NodeId,
    pub(super) source: Span,
}

#[derive(Debug)]
struct DataClause {
    input: usize,
    bindings: Vec<(usize, usize)>,
    body: usize,
    captures: Vec<usize>,
}

impl Expr {
    fn copy(&self, offset: usize, budget: &mut TypeWorkBudget) -> Result<Self, Failure> {
        let ids = |values: &[usize], budget: &mut TypeWorkBudget| -> Result<Vec<usize>, Failure> {
            let mut values = copy_slice(values, budget)?;
            for value in &mut values {
                *value += offset;
            }
            Ok(values)
        };
        let pairs = |values: &[(usize, usize)],
                     budget: &mut TypeWorkBudget|
         -> Result<Vec<(usize, usize)>, Failure> {
            let mut values = copy_slice(values, budget)?;
            for (left, right) in &mut values {
                *left += offset;
                *right += offset;
            }
            Ok(values)
        };
        charge(budget, 1)?;
        Ok(match self {
            Self::Scalar => Self::Scalar,
            Self::Slot => Self::Slot,
            Self::Unknown => Self::Unknown,
            Self::Alias(value) => Self::Alias(value + offset),
            Self::Merge(values) => Self::Merge(ids(values, budget)?),
            Self::Tuple(values) => Self::Tuple(ids(values, budget)?),
            Self::Constructor(id) => Self::Constructor(*id),
            Self::Project {
                value,
                field,
                constructor,
            } => Self::Project {
                value: value + offset,
                field: *field,
                constructor: *constructor,
            },
            Self::Function {
                parameters,
                body,
                captures,
            } => Self::Function {
                parameters: ids(parameters, budget)?,
                body: body + offset,
                captures: ids(captures, budget)?,
            },
            Self::Call {
                function,
                arguments,
                scalar,
                type_application,
            } => Self::Call {
                function: function + offset,
                arguments: ids(arguments, budget)?,
                scalar: *scalar,
                type_application: *type_application,
            },
            Self::Cleanup { body, action } => Self::Cleanup {
                body: body + offset,
                action: action + offset,
            },
            Self::Bind {
                binder,
                initializer,
                body,
            } => Self::Bind {
                binder: binder + offset,
                initializer: initializer + offset,
                body: body + offset,
            },
            Self::Recursive { bindings, body } => Self::Recursive {
                bindings: pairs(bindings, budget)?,
                body: body + offset,
            },
            Self::Match { scrutinee, arms } => {
                charge(budget, arms.len())?;
                let mut copied = Vec::new();
                copied
                    .try_reserve(arms.len())
                    .map_err(|_| Failure::Resource)?;
                for (bindings, body) in arms {
                    copied.push((pairs(bindings, budget)?, body + offset));
                }
                Self::Match {
                    scrutinee: scrutinee + offset,
                    arms: copied,
                }
            }
            Self::Resource {
                success,
                failure,
                handle,
                identity,
                initializer,
                body,
                source,
            } => Self::Resource {
                success: *success,
                failure: *failure,
                handle: handle + offset,
                identity: identity + offset,
                initializer: initializer + offset,
                body: body + offset,
                source: *source,
            },
            Self::Request { operand, scalar } => Self::Request {
                operand: operand + offset,
                scalar: *scalar,
            },
            Self::Resume { operand } => Self::Resume {
                operand: operand + offset,
            },
            Self::Evidence { value, bindings } => {
                let mut bindings = copy_slice(bindings, budget)?;
                for (_, _, slot) in &mut bindings {
                    *slot += offset;
                }
                Self::Evidence {
                    value: value + offset,
                    bindings,
                }
            }
            Self::Handler { body, clauses } => {
                charge(budget, clauses.len())?;
                let mut copied = Vec::new();
                copied
                    .try_reserve(clauses.len())
                    .map_err(|_| Failure::Resource)?;
                for clause in clauses {
                    copied.push(DataClause {
                        input: clause.input + offset,
                        bindings: pairs(&clause.bindings, budget)?,
                        body: clause.body + offset,
                        captures: ids(&clause.captures, budget)?,
                    });
                }
                Self::Handler {
                    body: body + offset,
                    clauses: copied,
                }
            }
        })
    }
}

#[derive(Debug, Default)]
struct ProviderQueryBindings {
    lexical: Vec<(usize, usize)>,
    parameters: Vec<usize>,
    capture_ports: Vec<usize>,
}

type EvidenceKey = (crate::interface::RequirementId, crate::interface::MethodId);

#[derive(Debug)]
struct EvidenceIndex {
    prefix: usize,
    first: HashMap<EvidenceKey, usize>,
}

#[derive(Debug)]
pub(super) struct Graph {
    expressions: Vec<Expr>,
    globals: Vec<(usize, usize)>,
    // Empty for ordinary analysis. The single fallible private carrier avoids
    // enlarging every ordinary graph/result stack frame by three vectors.
    provider: Vec<ProviderQueryBindings>,
    sources: Vec<Span>,
    exports: Vec<(BinderId, usize)>,
    positions: HashMap<usize, usize>,
    targets: HashMap<usize, usize>,
    metadata: HashMap<usize, crate::types::TypeVariableId>,
    evidence: Vec<(
        (crate::interface::RequirementId, crate::interface::MethodId),
        usize,
    )>,
    // One fallibly allocated record keeps the table off ordinary Graph frames.
    // The original ordered evidence vector remains the authority for every hit.
    evidence_index: Vec<EvidenceIndex>,
}

#[cfg(test)]
pub(super) fn provider_capture_graph_for_test(
    metadata: Option<crate::types::TypeVariableId>,
    unknown: bool,
) -> Graph {
    let source = crate::source::SourceFile::new("provider-capture.ash", "x").unwrap();
    let span = source
        .span(crate::source::ByteRange::new(0, 1).unwrap())
        .unwrap();
    Graph {
        expressions: vec![
            Expr::Function {
                parameters: Vec::new(),
                body: 0,
                captures: vec![1],
            },
            if unknown { Expr::Unknown } else { Expr::Slot },
        ],
        globals: Vec::new(),
        provider: Vec::new(),
        sources: vec![span; 2],
        exports: Vec::new(),
        positions: HashMap::new(),
        targets: HashMap::from([(0, 0)]),
        metadata: metadata
            .map(|variable| HashMap::from([(1, variable)]))
            .unwrap_or_default(),
        evidence: Vec::new(),
        evidence_index: Vec::new(),
    }
}

pub(super) struct CallSuccessors {
    pub(super) targets: Vec<(usize, usize)>,
    pub(super) unknown: bool,
    pub(super) returns: bool,
}

#[cfg(test)]
pub(super) fn provider_typed_capture_graph_for_test(
    metadata: Option<crate::types::TypeVariableId>,
    unknown: bool,
    capture: bool,
) -> Graph {
    let mut graph = provider_capture_graph_for_test(metadata, unknown);
    graph.expressions[0] = Expr::Function {
        parameters: vec![2],
        body: 3,
        captures: if capture { vec![1] } else { Vec::new() },
    };
    graph.expressions.push(Expr::Slot);
    graph.expressions.push(Expr::Scalar);
    graph.sources.resize(4, graph.sources[0]);
    graph.positions.insert(0, 3);
    graph
}

impl Graph {
    fn provider_bindings<'a>(
        storage: &'a mut Vec<ProviderQueryBindings>,
        budget: &mut TypeWorkBudget,
    ) -> Result<&'a mut ProviderQueryBindings, Failure> {
        if storage.is_empty() {
            charge(budget, 1)?;
            storage
                .try_reserve_exact(1)
                .map_err(|_| Failure::Resource)?;
            storage.push(ProviderQueryBindings::default());
        }
        storage.first_mut().ok_or(Failure::Invalid)
    }

    fn capture_ports(&self) -> &[usize] {
        self.provider
            .first()
            .map_or(&[], |provider| &provider.capture_ports[..])
    }

    fn install_provider_ports(
        &mut self,
        ports: &[crate::core::NodeId],
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        if ports.is_empty() {
            return Ok(());
        }
        charge(budget, ports.len())?;
        let provider = Self::provider_bindings(&mut self.provider, budget)?;
        provider
            .capture_ports
            .try_reserve_exact(ports.len())
            .map_err(|_| Failure::Resource)?;
        provider
            .capture_ports
            .extend(ports.iter().map(|node| index(*node)));
        Ok(())
    }

    fn install_provider_parameters(
        &mut self,
        parameters: &[BinderId],
        symbols: &HashMap<BinderId, usize>,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        if parameters.is_empty() {
            return Ok(());
        }
        charge(budget, parameters.len())?;
        let provider = Self::provider_bindings(&mut self.provider, budget)?;
        provider
            .parameters
            .try_reserve_exact(parameters.len())
            .map_err(|_| Failure::Resource)?;
        for binder in parameters {
            charge(budget, 1)?;
            if let Some(slot) = symbols.get(binder) {
                provider.parameters.push(*slot);
            }
        }
        Ok(())
    }

    fn import_graph(
        &mut self,
        imported: &Graph,
        target_offset: usize,
        code_offset: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<usize, Failure> {
        let offset = self.expressions.len();
        charge(budget, imported.expressions.len() + imported.globals.len())?;
        self.expressions
            .try_reserve(imported.expressions.len())
            .map_err(|_| Failure::Resource)?;
        self.sources
            .try_reserve(imported.sources.len())
            .map_err(|_| Failure::Resource)?;
        for expression in &imported.expressions {
            self.expressions.push(expression.copy(offset, budget)?);
        }
        self.sources.extend_from_slice(&imported.sources);
        self.globals
            .try_reserve(imported.globals.len())
            .map_err(|_| Failure::Resource)?;
        self.globals.extend(
            imported
                .globals
                .iter()
                .map(|(binder, value)| (binder + offset, value + offset)),
        );
        for (&code, &expression) in &imported.positions {
            self.position(code + code_offset, expression + offset, budget)?;
        }
        charge(budget, imported.metadata.len())?;
        self.metadata
            .try_reserve(imported.metadata.len())
            .map_err(|_| Failure::Resource)?;
        self.metadata.extend(
            imported
                .metadata
                .iter()
                .map(|(slot, variable)| (slot + offset, *variable)),
        );
        charge(budget, imported.targets.len())?;
        self.targets
            .try_reserve(imported.targets.len())
            .map_err(|_| Failure::Resource)?;
        self.targets.extend(
            imported
                .targets
                .iter()
                .map(|(expression, target)| (expression + offset, target + target_offset)),
        );
        charge(budget, imported.evidence.len())?;
        self.evidence
            .try_reserve(imported.evidence.len())
            .map_err(|_| Failure::Resource)?;
        self.evidence.extend(
            imported
                .evidence
                .iter()
                .map(|(key, slot)| (*key, slot + offset)),
        );
        Ok(offset)
    }

    /// Append the authenticated original value graph and install its exact
    /// clause-pattern ports at the actual generated handler control position.
    /// The caller separately proves original template/operation/owner identity.
    #[expect(
        clippy::too_many_arguments,
        reason = "exact original handler/body and control/callable relocation coordinates stay distinct at sealed graph admission"
    )]
    pub(super) fn import_conditional_handler(
        &mut self,
        imported: &Graph,
        original_handler: usize,
        actual_body_code: usize,
        actual_handler_code: usize,
        target_offset: usize,
        code_offset: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<usize, Failure> {
        if !matches!(
            imported.expressions.get(original_handler),
            Some(Expr::Handler { .. })
        ) || self.positions.contains_key(&actual_handler_code)
        {
            return Err(Failure::Invalid);
        }
        charge(budget, 2)?;
        for code in imported.positions.keys() {
            charge(budget, 1)?;
            if code.checked_add(code_offset).ok_or(Failure::Resource)? == actual_handler_code {
                return Err(Failure::Invalid);
            }
        }
        let body = *self
            .positions
            .get(&actual_body_code)
            .ok_or(Failure::Invalid)?;
        self.expressions.get(body).ok_or(Failure::Invalid)?;
        let offset = self.import_graph(imported, target_offset, code_offset, budget)?;
        let handler = original_handler
            .checked_add(offset)
            .ok_or(Failure::Resource)?;
        let Expr::Handler { body: actual, .. } =
            self.expressions.get_mut(handler).ok_or(Failure::Invalid)?
        else {
            return Err(Failure::Invalid);
        };
        *actual = body;
        self.position(actual_handler_code, handler, budget)?;
        Ok(handler)
    }

    /// Retain actual lexical initializers available at this checked flow call.
    /// These are local slots, never imported/global source definitions.
    pub(super) fn retain_provider_lexical<F: CoreOperationFamily>(
        &mut self,
        nodes: &[StoredNode<F>],
        environment: &[BinderId],
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        charge(budget, nodes.len())?;
        for (id, node) in nodes.iter().enumerate() {
            let mut retain =
                |binder: BinderId, slot: usize, initializer: usize, budget: &mut TypeWorkBudget| {
                    charge(budget, environment.len())?;
                    if environment.contains(&binder) {
                        charge(budget, 1)?;
                        let provider = Self::provider_bindings(&mut self.provider, budget)?;
                        provider
                            .lexical
                            .try_reserve(1)
                            .map_err(|_| Failure::Resource)?;
                        provider.lexical.push((slot, initializer));
                    }
                    Ok(())
                };
            match (F::pure(&node.kind), &self.expressions[id]) {
                (
                    Some(PureExprKind::Computation(PureComputation::Bind(binding))),
                    Expr::Bind {
                        binder,
                        initializer,
                        ..
                    },
                ) => {
                    retain(binding.binder().id(), *binder, *initializer, budget)?;
                }
                (
                    Some(PureExprKind::Computation(PureComputation::RecursiveBind(binding))),
                    Expr::Recursive { bindings, .. },
                ) => {
                    charge(budget, binding.members().len())?;
                    if binding.members().len() != bindings.len() {
                        return Err(Failure::Invalid);
                    }
                    for (member, (slot, initializer)) in binding.members().iter().zip(bindings) {
                        retain(member.binder().id(), *slot, *initializer, budget)?;
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }

    /// Inspect only the selected closure's retained dependencies. Metadata
    /// slots require an authenticated concrete instantiation from the caller;
    /// unresolved lexical slots and privileged values never become scalars.
    #[cfg(test)]
    pub(super) fn check_provider_selected_captures(
        &self,
        target: usize,
        metadata: &[crate::types::TypeVariableId],
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        charge(budget, self.targets.len())?;
        let expression = self
            .targets
            .iter()
            .find_map(|(expression, candidate)| (*candidate == target).then_some(*expression))
            .ok_or(Failure::Invalid)?;
        let Expr::Function { captures, .. } =
            self.expressions.get(expression).ok_or(Failure::Invalid)?
        else {
            return Err(Failure::Invalid);
        };
        let mut pending = copy_slice(captures, budget)?;
        let mut visited = HashSet::new();
        while let Some(id) = pending.pop() {
            charge(budget, 1)?;
            if visited.contains(&id) {
                continue;
            }
            charge(budget, 1)?;
            visited.try_reserve(1).map_err(|_| Failure::Resource)?;
            visited.insert(id);
            if let Some(variable) = self.metadata.get(&id) {
                charge(budget, metadata.len())?;
                if !metadata.contains(variable) {
                    return Err(Failure::Invalid);
                }
                continue;
            }
            let children: &[usize] = match self.expressions.get(id).ok_or(Failure::Invalid)? {
                Expr::Scalar | Expr::Constructor(_) => &[],
                Expr::Alias(value) | Expr::Project { value, .. } => std::slice::from_ref(value),
                Expr::Merge(values) | Expr::Tuple(values) => values,
                Expr::Function { captures, .. } => captures,
                Expr::Slot => {
                    charge(budget, self.globals.len())?;
                    let value = self
                        .globals
                        .iter()
                        .find_map(|(binder, value)| (*binder == id).then_some(value))
                        .ok_or(Failure::Invalid)?;
                    std::slice::from_ref(value)
                }
                _ => return Err(Failure::Invalid),
            };
            charge(budget, children.len())?;
            pending
                .try_reserve(children.len())
                .map_err(|_| Failure::Resource)?;
            pending.extend(children);
        }
        Ok(())
    }

    pub(super) fn provider_source(
        &self,
        target: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<Span, Failure> {
        charge(budget, self.targets.len())?;
        let expression = self
            .targets
            .iter()
            .find_map(|(expression, candidate)| (*candidate == target).then_some(*expression))
            .ok_or(Failure::Invalid)?;
        self.sources
            .get(expression)
            .copied()
            .ok_or(Failure::Invalid)
    }

    pub(super) fn start_provider(
        &self,
        budget: &mut TypeWorkBudget,
    ) -> Result<Analysis<'_>, Failure> {
        let mut analysis = Analysis::new(self, budget)?;
        analysis.provider_closed_data = true;
        for &(binder, value) in &self.globals {
            let initializer = analysis.slot(value, 0, budget)?;
            let binder = analysis.slot(binder, 0, budget)?;
            analysis.edge(binder, initializer, budget)?;
        }
        for &(binder, value) in self
            .provider
            .first()
            .map_or(&[][..], |provider| &provider.lexical)
        {
            charge(budget, 1)?;
            let initializer = analysis.slot(value, 0, budget)?;
            let binder = analysis.slot(binder, 0, budget)?;
            analysis.edge(binder, initializer, budget)?;
        }
        for &parameter in self
            .provider
            .first()
            .map_or(&[][..], |provider| &provider.parameters)
        {
            charge(budget, 1)?;
            let slot = analysis.slot(parameter, 0, budget)?;
            analysis.atom(slot, Atom::Free, budget)?;
        }
        analysis.close(budget)?;
        Ok(analysis)
    }

    // A cut freezes lexical inputs, not the initializers or local binders that
    // execution has yet to produce. Functions contribute their actual captures.
    fn free_inputs(&self, root: usize, budget: &mut TypeWorkBudget) -> Result<Vec<usize>, Failure> {
        let mut pending = copy_slice(&[root], budget)?;
        let mut visited = HashSet::new();
        let mut bound = HashSet::new();
        let mut inputs = Vec::new();
        while let Some(id) = pending.pop() {
            charge(budget, 1)?;
            visited.try_reserve(1).map_err(|_| Failure::Resource)?;
            if !visited.insert(id) {
                continue;
            }
            let expression = self.expressions.get(id).ok_or(Failure::Invalid)?;
            let mut children = Vec::new();
            let mut bindings = Vec::new();
            match expression {
                Expr::Slot => {
                    charge(budget, 1)?;
                    inputs.try_reserve(1).map_err(|_| Failure::Resource)?;
                    inputs.push(id);
                }
                Expr::Alias(value) | Expr::Project { value, .. } => {
                    children = copy_slice(&[*value], budget)?
                }
                Expr::Merge(values) | Expr::Tuple(values) => children = copy_slice(values, budget)?,
                Expr::Function { captures, .. } => children = copy_slice(captures, budget)?,
                Expr::Call {
                    function,
                    arguments,
                    ..
                } => {
                    children = copy_slice(arguments, budget)?;
                    children.try_reserve(1).map_err(|_| Failure::Resource)?;
                    children.push(*function);
                }
                Expr::Cleanup { body, action } => children = copy_slice(&[*body, *action], budget)?,
                Expr::Bind {
                    binder,
                    initializer,
                    body,
                } => {
                    bindings = copy_slice(&[*binder], budget)?;
                    children = copy_slice(&[*initializer, *body], budget)?;
                }
                Expr::Recursive {
                    bindings: group,
                    body,
                } => {
                    charge(budget, group.len() * 2 + 1)?;
                    bindings
                        .try_reserve(group.len())
                        .map_err(|_| Failure::Resource)?;
                    children
                        .try_reserve(group.len() + 1)
                        .map_err(|_| Failure::Resource)?;
                    for (binder, initializer) in group {
                        bindings.push(*binder);
                        children.push(*initializer);
                    }
                    children.push(*body);
                }
                Expr::Match { scrutinee, arms } => {
                    children = copy_slice(&[*scrutinee], budget)?;
                    for (arm, body) in arms {
                        charge(budget, arm.len() * 2 + 1)?;
                        bindings
                            .try_reserve(arm.len())
                            .map_err(|_| Failure::Resource)?;
                        children
                            .try_reserve(arm.len() + 1)
                            .map_err(|_| Failure::Resource)?;
                        for (binder, initializer) in arm {
                            bindings.push(*binder);
                            children.push(*initializer);
                        }
                        children.push(*body);
                    }
                }
                Expr::Resource {
                    handle,
                    identity,
                    initializer,
                    body,
                    ..
                } => {
                    bindings = copy_slice(&[*handle, *identity], budget)?;
                    children = copy_slice(&[*initializer, *body], budget)?;
                }
                Expr::Request { operand, .. } | Expr::Resume { operand } => {
                    children = copy_slice(&[*operand], budget)?
                }
                Expr::Handler { body, clauses } => {
                    children = copy_slice(&[*body], budget)?;
                    for clause in clauses {
                        charge(
                            budget,
                            clause.bindings.len() * 2 + clause.captures.len() + 2,
                        )?;
                        bindings
                            .try_reserve(clause.bindings.len() + 1)
                            .map_err(|_| Failure::Resource)?;
                        children
                            .try_reserve(clause.bindings.len() + clause.captures.len() + 1)
                            .map_err(|_| Failure::Resource)?;
                        bindings.push(clause.input);
                        for (binder, initializer) in &clause.bindings {
                            bindings.push(*binder);
                            children.push(*initializer);
                        }
                        children.extend(&clause.captures);
                        children.push(clause.body);
                    }
                }
                Expr::Evidence {
                    value,
                    bindings: evidence,
                } => {
                    charge(budget, evidence.len() + 1)?;
                    children
                        .try_reserve(evidence.len() + 1)
                        .map_err(|_| Failure::Resource)?;
                    children.push(*value);
                    children.extend(evidence.iter().map(|(_, _, argument)| *argument));
                }
                Expr::Scalar | Expr::Unknown | Expr::Constructor(_) => {}
            }
            charge(budget, children.len() + bindings.len())?;
            pending
                .try_reserve(children.len())
                .map_err(|_| Failure::Resource)?;
            pending.extend(children);
            bound
                .try_reserve(bindings.len())
                .map_err(|_| Failure::Resource)?;
            bound.extend(bindings);
        }
        charge(budget, inputs.len())?;
        inputs.retain(|input| !bound.contains(input));
        Ok(inputs)
    }

    fn prepare_evidence_index(&mut self, budget: &mut TypeWorkBudget) -> Result<(), Failure> {
        charge(budget, 1)?;
        if self.evidence_index.len() > 1 {
            return Err(Failure::Invalid);
        }
        if self
            .evidence_index
            .first()
            .is_some_and(|index| index.prefix == self.evidence.len())
        {
            return Ok(());
        }
        // Production only appends evidence in this module. A copied/imported
        // vector may contain duplicates; rebuilding visits its exact order and
        // retains the first ordinal rather than replacing it with a later port.
        let length = self.evidence.len();
        charge(budget, length.checked_add(1).ok_or(Failure::Resource)?)?;
        let additional = usize::from(self.evidence_index.is_empty());
        self.evidence_index
            .try_reserve(additional)
            .map_err(|_| Failure::Resource)?;
        let mut staged = EvidenceIndex {
            prefix: length,
            first: HashMap::new(),
        };
        // The complete maximum table capacity and its scalar record are paid
        // before allocation. Duplicate input entries still occupy the original
        // vector; each scan and table lookup pays separately below.
        staged
            .first
            .try_reserve(length)
            .map_err(|_| Failure::Resource)?;
        for (ordinal, &(key, slot)) in self.evidence.iter().enumerate() {
            charge(budget, 2)?;
            if slot >= self.expressions.len() {
                return Err(Failure::Invalid);
            }
            staged.first.entry(key).or_insert(ordinal);
        }
        // No fallible work follows publication of this complete prefix.
        if let Some(index) = self.evidence_index.first_mut() {
            *index = staged;
        } else {
            self.evidence_index.push(staged);
        }
        Ok(())
    }

    fn evidence_slot(
        &mut self,
        requirement: crate::interface::RequirementId,
        method: crate::interface::MethodId,
        source: Span,
        budget: &mut TypeWorkBudget,
    ) -> Result<usize, Failure> {
        self.prepare_evidence_index(budget)?;
        let key = (requirement, method);
        charge(budget, 1)?;
        let ordinal = self.evidence_index[0].first.get(&key).copied();
        if let Some(ordinal) = ordinal {
            charge(budget, 1)?;
            let &(original, slot) = self.evidence.get(ordinal).ok_or(Failure::Invalid)?;
            if original != key || slot >= self.expressions.len() {
                return Err(Failure::Invalid);
            }
            return Ok(slot);
        }
        let ordinal = self.evidence.len();
        let prefix = ordinal.checked_add(1).ok_or(Failure::Resource)?;
        // Admit the original entry, indexed ordinal and prefix update before
        // reserving all append storage. push itself pays/reserves its original
        // expression/source entries before mutating either vector.
        charge(budget, 3)?;
        self.evidence
            .try_reserve(1)
            .map_err(|_| Failure::Resource)?;
        self.evidence_index[0]
            .first
            .try_reserve(1)
            .map_err(|_| Failure::Resource)?;
        let slot = self.push(Expr::Slot, source, budget)?;
        // All reservations and fallible charges succeeded; commit together.
        self.evidence.push((key, slot));
        self.evidence_index[0].first.insert(key, ordinal);
        self.evidence_index[0].prefix = prefix;
        Ok(slot)
    }

    fn method_target(
        &mut self,
        target: super::MethodTarget,
        method: crate::interface::MethodId,
        adapters: &[usize],
        symbols: &mut HashMap<BinderId, usize>,
        source: Span,
        budget: &mut TypeWorkBudget,
    ) -> Result<usize, Failure> {
        match target {
            super::MethodTarget::Binder(binder) => self.symbol(symbols, binder, source, budget),
            super::MethodTarget::Abstract(requirement) => {
                self.evidence_slot(requirement, method, source, budget)
            }
            super::MethodTarget::Adapter { value, .. } => {
                adapters.get(value).copied().ok_or(Failure::Invalid)
            }
        }
    }

    #[allow(clippy::too_many_arguments)] // Explicit graph inputs share the owning work ledger.
    fn abstract_captures<F: CoreOperationFamily>(
        &mut self,
        nodes: &[StoredNode<F>],
        root: usize,
        methods: &super::MethodUses<'_>,
        adapters: &[super::MethodAdapter],
        symbols: &mut HashMap<BinderId, usize>,
        captures: &mut Vec<usize>,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        let mut pending = copy_slice(&[root], budget)?;
        let mut visited = HashSet::new();
        while let Some(id) = pending.pop() {
            charge(budget, 1)?;
            visited.try_reserve(1).map_err(|_| Failure::Resource)?;
            if !visited.insert(id) {
                continue;
            }
            if !self.capture_ports().is_empty() {
                charge(budget, self.capture_ports().len())?;
                if self.capture_ports().contains(&id) {
                    charge(budget, captures.len())?;
                    if !captures.contains(&id) {
                        captures.try_reserve(1).map_err(|_| Failure::Resource)?;
                        captures.push(id);
                    }
                    continue;
                }
            }
            for method in methods.at(id, budget)? {
                if index(method.node) == id {
                    if let super::MethodTarget::Adapter { value, .. } = method.target {
                        let mut pending = copy_slice(&[value], budget)?;
                        let mut seen = HashSet::new();
                        while let Some(adapter) = pending.pop() {
                            charge(budget, 1)?;
                            seen.try_reserve(1).map_err(|_| Failure::Resource)?;
                            if !seen.insert(adapter) {
                                continue;
                            }
                            let adapter = adapters.get(adapter).ok_or(Failure::Invalid)?;
                            let binder =
                                self.symbol(symbols, adapter.binder, self.sources[id], budget)?;
                            charge(budget, captures.len())?;
                            if !captures.contains(&binder) {
                                captures.try_reserve(1).map_err(|_| Failure::Resource)?;
                                captures.push(binder);
                            }
                            charge(budget, adapter.prerequisites.len())?;
                            pending
                                .try_reserve(adapter.prerequisites.len())
                                .map_err(|_| Failure::Resource)?;
                            for (_, _, target) in &adapter.prerequisites {
                                if let super::MethodTarget::Adapter { value, .. } = target {
                                    pending.push(*value);
                                }
                            }
                        }
                    }
                    let slot = if method.requirement.is_some()
                        || matches!(method.target, super::MethodTarget::Adapter { .. })
                    {
                        id
                    } else if let super::MethodTarget::Abstract(requirement) = method.target {
                        self.evidence_slot(requirement, method.method, self.sources[id], budget)?
                    } else {
                        continue;
                    };
                    charge(budget, captures.len())?;
                    if !captures.contains(&slot) {
                        captures.try_reserve(1).map_err(|_| Failure::Resource)?;
                        captures.push(slot);
                    }
                }
            }
            let node = nodes.get(id).ok_or(Failure::Invalid)?;
            let count = F::child_count(&node.kind);
            charge(budget, count)?;
            pending.try_reserve(count).map_err(|_| Failure::Resource)?;
            for ordinal in 0..count {
                pending.push(index(
                    F::child_at(&node.kind, ordinal).ok_or(Failure::Invalid)?,
                ));
            }
        }
        Ok(())
    }

    fn push(
        &mut self,
        expression: Expr,
        source: Span,
        budget: &mut TypeWorkBudget,
    ) -> Result<usize, Failure> {
        charge(budget, 1)?;
        self.expressions
            .try_reserve(1)
            .map_err(|_| Failure::Resource)?;
        self.sources.try_reserve(1).map_err(|_| Failure::Resource)?;
        let index = self.expressions.len();
        self.expressions.push(expression);
        self.sources.push(source);
        Ok(index)
    }

    fn symbol<K: Copy + Eq + std::hash::Hash>(
        &mut self,
        symbols: &mut HashMap<K, usize>,
        key: K,
        source: Span,
        budget: &mut TypeWorkBudget,
    ) -> Result<usize, Failure> {
        charge(budget, 1)?;
        if let Some(id) = symbols.get(&key) {
            return Ok(*id);
        }
        let id = self.push(Expr::Slot, source, budget)?;
        symbols.try_reserve(1).map_err(|_| Failure::Resource)?;
        symbols.insert(key, id);
        Ok(id)
    }

    fn pattern(
        &mut self,
        pattern: &CorePattern,
        value: usize,
        symbols: &mut HashMap<BinderId, usize>,
        budget: &mut TypeWorkBudget,
    ) -> Result<Vec<(usize, usize)>, Failure> {
        let mut pending = copy_slice(&[(pattern, value)], budget)?;
        let mut bindings = Vec::new();
        while let Some((pattern, value)) = pending.pop() {
            charge(budget, 1)?;
            let source = pattern.origin.primary_span();
            match &pattern.kind {
                CorePatternKind::Binder(binder) => {
                    let slot = self.symbol(symbols, binder.id(), source, budget)?;
                    bindings.try_reserve(1).map_err(|_| Failure::Resource)?;
                    bindings.push((slot, value));
                }
                CorePatternKind::Tuple(fields) => {
                    charge(budget, fields.len())?;
                    pending
                        .try_reserve(fields.len())
                        .map_err(|_| Failure::Resource)?;
                    for (field, child) in fields.iter().enumerate() {
                        let projected = self.push(
                            Expr::Project {
                                value,
                                field,
                                constructor: None,
                            },
                            source,
                            budget,
                        )?;
                        pending.push((child, projected));
                    }
                }
                CorePatternKind::Constructor {
                    constructor,
                    payload: Some(payload),
                } => {
                    let projected = self.push(
                        Expr::Project {
                            value,
                            field: 0,
                            constructor: Some(*constructor),
                        },
                        source,
                        budget,
                    )?;
                    pending.try_reserve(1).map_err(|_| Failure::Resource)?;
                    pending.push((payload, projected));
                }
                _ => {}
            }
        }
        Ok(bindings)
    }

    /// Raw selected-producer occurrences outside authenticated source cuts
    /// retain no ordinary source-call authority. Adapter construction uses
    /// its separate canonical import relation, never these raw occurrences.
    pub(super) fn refuse_provider_dictionary_variables<F: CoreOperationFamily>(
        &mut self,
        nodes: &[StoredNode<F>],
        variables: &[crate::core::NodeId],
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        charge(budget, variables.len())?;
        for variable in variables {
            let id = index(*variable);
            if !matches!(
                F::pure(&nodes.get(id).ok_or(Failure::Invalid)?.kind),
                Some(PureExprKind::Variable(_))
            ) {
                return Err(Failure::Invalid);
            }
            *self.expressions.get_mut(id).ok_or(Failure::Invalid)? = Expr::Unknown;
        }
        Ok(())
    }

    fn build_adapters(
        &mut self,
        adapters: &[super::MethodAdapter],
        symbols: &mut HashMap<BinderId, usize>,
        types: &mut HashMap<crate::types::TypeVariableId, usize>,
        budget: &mut TypeWorkBudget,
    ) -> Result<Vec<usize>, Failure> {
        let mut adapter_values = Vec::new();
        charge(budget, adapters.len())?;
        adapter_values
            .try_reserve(adapters.len())
            .map_err(|_| Failure::Resource)?;
        for adapter in adapters {
            let source = adapter.source;
            let binder = self.symbol(symbols, adapter.binder, source, budget)?;
            let mut bindings = Vec::new();
            charge(budget, adapter.prerequisites.len())?;
            bindings
                .try_reserve(adapter.prerequisites.len())
                .map_err(|_| Failure::Resource)?;
            for &(requirement, method, target) in &adapter.prerequisites {
                let value =
                    self.method_target(target, method, &adapter_values, symbols, source, budget)?;
                bindings.push((requirement, method, value));
            }
            let function = if bindings.is_empty() {
                binder
            } else {
                self.push(
                    Expr::Evidence {
                        value: binder,
                        bindings,
                    },
                    source,
                    budget,
                )?
            };
            let mut arguments = Vec::new();
            let mut captures = copy_slice(&[function], budget)?;
            let count = adapter
                .head_arguments
                .len()
                .checked_add(adapter.method_parameters)
                .ok_or(Failure::Resource)?;
            charge(budget, count)?;
            arguments
                .try_reserve(count)
                .map_err(|_| Failure::Resource)?;
            captures
                .try_reserve(adapter.head_arguments.len())
                .map_err(|_| Failure::Resource)?;
            for argument in &adapter.head_arguments {
                let mut metadata = MetadataVariables::default();
                super::retain_type_variables(&mut metadata, argument, budget)?;
                let mut slots = Vec::new();
                slots
                    .try_reserve(metadata.variables.len())
                    .map_err(|_| Failure::Resource)?;
                for variable in metadata.variables {
                    slots.push(self.symbol(types, variable, source, budget)?);
                }
                let argument = self.push(Expr::Merge(slots), source, budget)?;
                arguments.push(argument);
                captures.push(argument);
            }
            let mut parameters = Vec::new();
            parameters
                .try_reserve(adapter.method_parameters)
                .map_err(|_| Failure::Resource)?;
            for _ in 0..adapter.method_parameters {
                let parameter = self.push(Expr::Slot, source, budget)?;
                parameters.push(parameter);
                arguments.push(parameter);
            }
            let applied = if arguments.is_empty() {
                function
            } else {
                self.push(
                    Expr::Call {
                        function,
                        arguments,
                        scalar: false,
                        type_application: true,
                    },
                    source,
                    budget,
                )?
            };
            let value = if parameters.is_empty() {
                applied
            } else {
                self.push(
                    Expr::Function {
                        parameters,
                        body: applied,
                        captures,
                    },
                    source,
                    budget,
                )?
            };
            adapter_values.push(value);
        }
        Ok(adapter_values)
    }

    #[allow(clippy::too_many_arguments)] // Separate phases keep the small-stack construction boundary bounded.
    fn build_expression<F: CoreOperationFamily>(
        &mut self,
        id: usize,
        nodes: &[StoredNode<F>],
        symbols: &mut HashMap<BinderId, usize>,
        types: &mut HashMap<crate::types::TypeVariableId, usize>,
        operation: fn(&F::Kind) -> Option<&EffectOperation>,
        methods: &super::MethodUses<'_>,
        adapters: &[super::MethodAdapter],
        headers: &mut FunctionMetadataPreparation<'_, F>,
        budget: &mut TypeWorkBudget,
    ) -> Result<Expr, Failure> {
        let node = nodes.get(id).ok_or(Failure::Invalid)?;
        let source = self.sources[id];
        Ok(match F::pure(&node.kind) {
            Some(PureExprKind::Variable(variable)) => {
                Expr::Alias(self.symbol(symbols, variable.binder(), source, budget)?)
            }
            Some(PureExprKind::Value(PureValue::Function(function))) => {
                self.targets.try_reserve(1).map_err(|_| Failure::Resource)?;
                self.targets.insert(id, id);
                let parameter = self.symbol(symbols, function.parameter().id(), source, budget)?;
                let mut captures = Vec::new();
                for binder in super::free_values_with_methods(
                    nodes,
                    index(function.body()),
                    &[function.parameter().id()],
                    methods,
                    self.capture_ports(),
                    budget,
                )? {
                    let slot = self.symbol(symbols, binder, source, budget)?;
                    captures.try_reserve(1).map_err(|_| Failure::Resource)?;
                    captures.push(slot);
                }
                let metadata = headers.collect(index(function.body()), budget)?;
                for variable in metadata.variables {
                    let slot = self.symbol(types, variable, source, budget)?;
                    captures.try_reserve(1).map_err(|_| Failure::Resource)?;
                    captures.push(slot);
                }
                self.abstract_captures(
                    nodes,
                    index(function.body()),
                    methods,
                    adapters,
                    symbols,
                    &mut captures,
                    budget,
                )?;
                Expr::Function {
                    parameters: copy_slice(&[parameter], budget)?,
                    body: index(function.body()),
                    captures,
                }
            }
            Some(PureExprKind::Value(PureValue::String(_))) => Expr::Scalar,
            Some(PureExprKind::Value(PureValue::Intrinsic(intrinsic))) => {
                self.targets.try_reserve(1).map_err(|_| Failure::Resource)?;
                self.targets.insert(id, id);
                let parameter = self.push(Expr::Slot, source, budget)?;
                let scalar = self.push(Expr::Scalar, source, budget)?;
                let constructors = match intrinsic.operation() {
                    crate::core::packed::Intrinsic::BytesAppendByte { appended, invalid } => {
                        Some((appended, invalid))
                    }
                    crate::core::packed::Intrinsic::StringFromUtf8 { decoded, invalid } => {
                        Some((decoded, invalid))
                    }
                    _ => None,
                };
                let body = if let Some((success, invalid)) = constructors {
                    let function = self.push(Expr::Constructor(success), source, budget)?;
                    let success = self.push(
                        Expr::Call {
                            function,
                            arguments: copy_slice(&[scalar], budget)?,
                            scalar: false,
                            type_application: false,
                        },
                        source,
                        budget,
                    )?;
                    let invalid = self.push(Expr::Constructor(invalid), source, budget)?;
                    self.push(
                        Expr::Merge(copy_slice(&[success, invalid], budget)?),
                        source,
                        budget,
                    )?
                } else {
                    scalar
                };
                Expr::Function {
                    parameters: copy_slice(&[parameter], budget)?,
                    body,
                    captures: Vec::new(),
                }
            }
            Some(PureExprKind::Value(PureValue::Constructor(constructor))) => {
                Expr::Constructor(constructor.constructor())
            }
            Some(PureExprKind::Computation(computation)) => self.build_computation(
                computation,
                id,
                nodes,
                symbols,
                types,
                methods,
                adapters,
                headers,
                budget,
            )?,
            _ => self.build_operation(
                id, nodes, symbols, types, operation, methods, adapters, headers, budget,
            )?,
        })
    }

    #[allow(clippy::too_many_arguments)] // Borrowed phase inputs avoid another owning environment.
    fn build_computation<F: CoreOperationFamily>(
        &mut self,
        computation: &PureComputation,
        id: usize,
        nodes: &[StoredNode<F>],
        symbols: &mut HashMap<BinderId, usize>,
        types: &mut HashMap<crate::types::TypeVariableId, usize>,
        methods: &super::MethodUses<'_>,
        adapters: &[super::MethodAdapter],
        headers: &mut FunctionMetadataPreparation<'_, F>,
        budget: &mut TypeWorkBudget,
    ) -> Result<Expr, Failure> {
        let node = nodes.get(id).ok_or(Failure::Invalid)?;
        let source = self.sources[id];
        Ok(match computation {
            PureComputation::Bind(binding) => Expr::Bind {
                binder: self.symbol(symbols, binding.binder().id(), source, budget)?,
                initializer: index(binding.initializer()),
                body: index(binding.body()),
            },
            PureComputation::RecursiveBind(binding) => {
                let mut bindings = Vec::new();
                for member in binding.members() {
                    charge(budget, 1)?;
                    let slot = self.symbol(symbols, member.binder().id(), source, budget)?;
                    bindings.try_reserve(1).map_err(|_| Failure::Resource)?;
                    bindings.push((slot, index(member.initializer())));
                }
                Expr::Recursive {
                    bindings,
                    body: index(binding.body()),
                }
            }
            PureComputation::Apply(application) => Expr::Call {
                function: index(application.function()),
                arguments: copy_slice(&[index(application.argument())], budget)?,
                scalar: scalar(&node.ty),
                type_application: false,
            },
            PureComputation::Tuple(tuple) => {
                charge(budget, tuple.elements().len())?;
                let mut fields = Vec::new();
                fields
                    .try_reserve(tuple.elements().len())
                    .map_err(|_| Failure::Resource)?;
                fields.extend(tuple.elements().iter().map(|node| index(*node)));
                Expr::Tuple(fields)
            }
            PureComputation::Match(matching) => {
                let mut arms = Vec::new();
                for arm in matching.arms() {
                    charge(budget, 1)?;
                    let bindings =
                        self.pattern(arm.pattern(), index(matching.scrutinee()), symbols, budget)?;
                    arms.try_reserve(1).map_err(|_| Failure::Resource)?;
                    arms.push((bindings, index(arm.body())));
                }
                Expr::Match {
                    scrutinee: index(matching.scrutinee()),
                    arms,
                }
            }
            PureComputation::TypeAbstraction(abstraction) => {
                let mut parameters = Vec::new();
                for (variable, _) in abstraction.parameters() {
                    let slot = self.symbol(types, *variable, source, budget)?;
                    parameters.try_reserve(1).map_err(|_| Failure::Resource)?;
                    parameters.push(slot);
                }
                let mut captures = Vec::new();
                for binder in super::free_values_with_methods(
                    nodes,
                    index(abstraction.body()),
                    &[],
                    methods,
                    self.capture_ports(),
                    budget,
                )? {
                    let slot = self.symbol(symbols, binder, source, budget)?;
                    captures.try_reserve(1).map_err(|_| Failure::Resource)?;
                    captures.push(slot);
                }
                let metadata = headers.collect(index(abstraction.body()), budget)?;
                for variable in metadata.variables {
                    let slot = self.symbol(types, variable, source, budget)?;
                    charge(budget, parameters.len())?;
                    if !parameters.contains(&slot) {
                        captures.try_reserve(1).map_err(|_| Failure::Resource)?;
                        captures.push(slot);
                    }
                }
                self.abstract_captures(
                    nodes,
                    index(abstraction.body()),
                    methods,
                    adapters,
                    symbols,
                    &mut captures,
                    budget,
                )?;
                Expr::Function {
                    parameters,
                    body: index(abstraction.body()),
                    captures,
                }
            }
            PureComputation::TypeApplication(application) => {
                let mut arguments = Vec::new();
                let Type::Forall(parameters, _) = &nodes[index(application.function())].ty else {
                    return Err(Failure::Invalid);
                };
                let mut ordinary = application.arguments().iter();
                let mut rows = application.row_arguments().iter();
                for (_, kind) in parameters.iter() {
                    let mut metadata = MetadataVariables::default();
                    if matches!(kind, crate::types::Kind::EffectRow) {
                        super::retain_row_variables(
                            &mut metadata,
                            rows.next().ok_or(Failure::Invalid)?,
                            budget,
                        )?;
                    } else {
                        super::retain_type_variables(
                            &mut metadata,
                            ordinary.next().ok_or(Failure::Invalid)?,
                            budget,
                        )?;
                    }
                    let mut slots = Vec::new();
                    for variable in metadata.variables {
                        let slot = self.symbol(types, variable, source, budget)?;
                        slots.try_reserve(1).map_err(|_| Failure::Resource)?;
                        slots.push(slot);
                    }
                    let argument = self.push(Expr::Merge(slots), source, budget)?;
                    arguments.try_reserve(1).map_err(|_| Failure::Resource)?;
                    arguments.push(argument);
                }
                if ordinary.next().is_some() || rows.next().is_some() {
                    return Err(Failure::Invalid);
                }
                Expr::Call {
                    function: index(application.function()),
                    arguments,
                    scalar: scalar(&node.ty),
                    type_application: true,
                }
            }
            PureComputation::LocalNominalScope(scope) => Expr::Alias(index(scope.body())),
            PureComputation::NewtypeConversion(conversion) => {
                Expr::Alias(index(conversion.child()))
            }
            PureComputation::Primitive(_) => {
                let mut children = Vec::new();
                charge(budget, F::child_count(&node.kind))?;
                children
                    .try_reserve(F::child_count(&node.kind))
                    .map_err(|_| Failure::Resource)?;
                for ordinal in 0..F::child_count(&node.kind) {
                    children.push(index(
                        F::child_at(&node.kind, ordinal).ok_or(Failure::Invalid)?,
                    ));
                }
                // Strict children are visited for their scopes and calls,
                // but arithmetic returns a copied scalar.
                let scalar = self.push(Expr::Scalar, source, budget)?;
                let mut bindings = Vec::new();
                bindings
                    .try_reserve(children.len())
                    .map_err(|_| Failure::Resource)?;
                bindings.extend(children.into_iter().map(|child| (scalar, child)));
                Expr::Recursive {
                    bindings,
                    body: scalar,
                }
            }
        })
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "ordinary and conditional handlers share the same exact pattern, body and selected-route capture builder"
    )]
    fn clause_data<F: CoreOperationFamily>(
        &mut self,
        pattern: &CorePattern,
        body: usize,
        source: Span,
        nodes: &[StoredNode<F>],
        symbols: &mut HashMap<BinderId, usize>,
        types: &mut HashMap<crate::types::TypeVariableId, usize>,
        methods: &super::MethodUses<'_>,
        adapters: &[super::MethodAdapter],
        headers: &mut FunctionMetadataPreparation<'_, F>,
        budget: &mut TypeWorkBudget,
    ) -> Result<DataClause, Failure> {
        let input = self.push(Expr::Slot, source, budget)?;
        let bindings = self.pattern(pattern, input, symbols, budget)?;
        let mut captures = Vec::new();
        for binder in super::free_values_with_methods(
            nodes,
            body,
            &[],
            methods,
            self.capture_ports(),
            budget,
        )? {
            let slot = self.symbol(symbols, binder, source, budget)?;
            charge(budget, bindings.len())?;
            if !bindings.iter().any(|(bound, _)| *bound == slot) {
                captures.try_reserve(1).map_err(|_| Failure::Resource)?;
                captures.push(slot);
            }
        }
        let metadata = headers.collect(body, budget)?;
        for variable in metadata.variables {
            let slot = self.symbol(types, variable, source, budget)?;
            captures.try_reserve(1).map_err(|_| Failure::Resource)?;
            captures.push(slot);
        }
        self.abstract_captures(
            nodes,
            body,
            methods,
            adapters,
            symbols,
            &mut captures,
            budget,
        )?;
        Ok(DataClause {
            input,
            bindings,
            body,
            captures,
        })
    }

    #[allow(clippy::too_many_arguments)] // Borrowed phase inputs avoid another owning environment.
    fn build_operation<F: CoreOperationFamily>(
        &mut self,
        id: usize,
        nodes: &[StoredNode<F>],
        symbols: &mut HashMap<BinderId, usize>,
        types: &mut HashMap<crate::types::TypeVariableId, usize>,
        operation: fn(&F::Kind) -> Option<&EffectOperation>,
        methods: &super::MethodUses<'_>,
        adapters: &[super::MethodAdapter],
        headers: &mut FunctionMetadataPreparation<'_, F>,
        budget: &mut TypeWorkBudget,
    ) -> Result<Expr, Failure> {
        let node = nodes.get(id).ok_or(Failure::Invalid)?;
        let source = self.sources[id];
        Ok(match operation(&node.kind) {
            Some(EffectOperation::ProviderStateAccess(_)) => Expr::Unknown,
            Some(EffectOperation::Cleanup(scope)) => Expr::Cleanup {
                body: index(scope.body),
                action: index(scope.action),
            },
            Some(EffectOperation::Registration(scope)) => Expr::Alias(index(scope.body)),
            Some(EffectOperation::Resource(resource)) => Expr::Resource {
                success: resource
                    .acquisition
                    .api()
                    .ok_or(Failure::Invalid)?
                    .outcome()
                    .map(|outcome| ConstructorId::new(outcome, 0)),
                failure: resource
                    .acquisition
                    .api()
                    .ok_or(Failure::Invalid)?
                    .outcome()
                    .map(|outcome| ConstructorId::new(outcome, 1)),
                handle: self.symbol(symbols, resource.handle.id(), source, budget)?,
                identity: self.symbol(types, resource.acquisition.identity, source, budget)?,
                initializer: index(resource.initializer),
                body: index(resource.body),
                source: resource.acquisition.span,
            },
            Some(
                selected_operation @ (EffectOperation::Handler(_)
                | EffectOperation::ProviderScope(_)),
            ) => {
                let (handler, provider) = match selected_operation {
                    EffectOperation::Handler(handler) => (handler, None),
                    EffectOperation::ProviderScope(scope) => (&scope.handler, Some(scope.as_ref())),
                    _ => return Err(Failure::Invalid),
                };
                charge(budget, handler.clauses().len())?;
                let mut clauses = Vec::new();
                clauses
                    .try_reserve(handler.clauses().len())
                    .map_err(|_| Failure::Resource)?;
                for clause in handler.clauses() {
                    clauses.push(self.clause_data(
                        clause.pattern(),
                        index(clause.body()),
                        source,
                        nodes,
                        symbols,
                        types,
                        methods,
                        adapters,
                        headers,
                        budget,
                    )?);
                }
                let handler = Expr::Handler {
                    body: index(handler.body()),
                    clauses,
                };
                if let Some(scope) = provider {
                    let handler = self.push(handler, source, budget)?;
                    let handle = self.symbol(symbols, scope.handle.id(), source, budget)?;
                    let identity =
                        self.symbol(types, scope.descriptor.identity(), source, budget)?;
                    let state = self.symbol(symbols, scope.handler_state.id(), source, budget)?;
                    let finish =
                        self.symbol(symbols, scope.finish.parameter.id(), source, budget)?;
                    let acquire =
                        self.symbol(symbols, scope.acquire.parameter.id(), source, budget)?;
                    let completed = self.push(
                        Expr::Cleanup {
                            body: handler,
                            action: index(scope.finish.body),
                        },
                        source,
                        budget,
                    )?;
                    let with_finish = self.push(
                        Expr::Bind {
                            binder: finish,
                            initializer: handle,
                            body: completed,
                        },
                        source,
                        budget,
                    )?;
                    let with_state = self.push(
                        Expr::Bind {
                            binder: state,
                            initializer: handle,
                            body: with_finish,
                        },
                        source,
                        budget,
                    )?;
                    let acquired = self.push(
                        Expr::Bind {
                            binder: acquire,
                            initializer: index(scope.initializer),
                            body: index(scope.acquire.body),
                        },
                        source,
                        budget,
                    )?;
                    // Completed carries the actual body value and independent
                    // completion data. Both tuple projections must survive
                    // resource-result and imported-summary reconstruction.
                    let completion = self.push(Expr::Scalar, source, budget)?;
                    let result_fields = copy_slice(&[with_state, completion], budget)?;
                    let result = self.push(Expr::Tuple(result_fields), source, budget)?;
                    Expr::Resource {
                        success: Some(scope.descriptor.protocol().scope[1]),
                        failure: Some(scope.descriptor.protocol().scope[0]),
                        handle,
                        identity,
                        initializer: acquired,
                        body: result,
                        source,
                    }
                } else {
                    handler
                }
            }
            Some(EffectOperation::Request(request)) => Expr::Request {
                operand: index(request.operand()),
                scalar: scalar(&node.ty),
            },
            Some(EffectOperation::Resume(resume)) => Expr::Resume {
                operand: index(resume.value()),
            },
            _ => Expr::Scalar,
        })
    }

    #[allow(clippy::too_many_arguments)] // The two authenticated evidence carriers stay explicit.
    #[cfg(test)]
    pub(super) fn build<F: CoreOperationFamily>(
        nodes: &[StoredNode<F>],
        globals: &[(BinderId, crate::core::NodeId)],
        imports: &[(BinderId, &super::CaptureValueSummary)],
        imported_callables: &super::ImportedCallables<'_>,
        operation: fn(&F::Kind) -> Option<&EffectOperation>,
        methods: &[super::MethodUse],
        adapters: &[super::MethodAdapter],
        independent_parameters: &[BinderId],
        capture_ports: &[crate::core::NodeId],
        budget: &mut TypeWorkBudget,
    ) -> Result<Self, Failure> {
        Self::build_with_conditional_handler(
            nodes,
            globals,
            imports,
            imported_callables,
            operation,
            methods,
            adapters,
            independent_parameters,
            capture_ports,
            None,
            budget,
        )
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "the sealed conditional clause ports accompany the existing actual typed-node and selected-evidence graph inputs"
    )]
    #[cfg(test)]
    pub(super) fn build_with_conditional_handler<F: CoreOperationFamily>(
        nodes: &[StoredNode<F>],
        globals: &[(BinderId, crate::core::NodeId)],
        imports: &[(BinderId, &super::CaptureValueSummary)],
        imported_callables: &super::ImportedCallables<'_>,
        operation: fn(&F::Kind) -> Option<&EffectOperation>,
        methods: &[super::MethodUse],
        adapters: &[super::MethodAdapter],
        independent_parameters: &[BinderId],
        capture_ports: &[crate::core::NodeId],
        conditional: Option<(&[ConditionalClauseInput<'_>], &mut Option<usize>)>,
        budget: &mut TypeWorkBudget,
    ) -> Result<Self, Failure> {
        Self::build_in_domain(
            nodes,
            globals,
            imports,
            imported_callables,
            operation,
            methods,
            adapters,
            independent_parameters,
            capture_ports,
            conditional,
            None,
            budget,
        )
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "the same typed value graph preserves source ordinals within the authenticated actual-root domain"
    )]
    pub(super) fn build_in_domain<F: CoreOperationFamily>(
        nodes: &[StoredNode<F>],
        globals: &[(BinderId, crate::core::NodeId)],
        imports: &[(BinderId, &super::CaptureValueSummary)],
        imported_callables: &super::ImportedCallables<'_>,
        operation: fn(&F::Kind) -> Option<&EffectOperation>,
        methods: &[super::MethodUse],
        adapters: &[super::MethodAdapter],
        independent_parameters: &[BinderId],
        capture_ports: &[crate::core::NodeId],
        conditional: Option<(&[ConditionalClauseInput<'_>], &mut Option<usize>)>,
        domain: Option<&HashSet<usize>>,
        budget: &mut TypeWorkBudget,
    ) -> Result<Self, Failure> {
        let methods = super::MethodUses::new(methods, budget)?;
        let mut headers = FunctionMetadataPreparation::new(nodes, operation);
        let mut graph = Self {
            expressions: Vec::new(),
            globals: Vec::new(),
            provider: Vec::new(),
            sources: Vec::new(),
            exports: Vec::new(),
            positions: HashMap::new(),
            targets: HashMap::new(),
            metadata: HashMap::new(),
            evidence: Vec::new(),
            evidence_index: Vec::new(),
        };
        charge(budget, nodes.len())?;
        graph
            .expressions
            .try_reserve(nodes.len())
            .map_err(|_| Failure::Resource)?;
        graph
            .sources
            .try_reserve(nodes.len())
            .map_err(|_| Failure::Resource)?;
        for node in nodes {
            graph.expressions.push(if domain.is_some() {
                Expr::Unknown
            } else {
                Expr::Scalar
            });
            graph
                .sources
                .push(node.origin.as_ref().ok_or(Failure::Invalid)?.primary_span());
        }
        let mut symbols = HashMap::new();
        let mut types = HashMap::new();
        graph.install_provider_ports(capture_ports, budget)?;
        let adapter_values = graph.build_adapters(adapters, &mut symbols, &mut types, budget)?;
        for (binder, node) in globals {
            let slot = graph.symbol(&mut symbols, *binder, graph.sources[index(*node)], budget)?;
            graph
                .globals
                .try_reserve(1)
                .map_err(|_| Failure::Resource)?;
            graph.globals.push((slot, index(*node)));
            graph
                .exports
                .try_reserve(1)
                .map_err(|_| Failure::Resource)?;
            graph.exports.push((*binder, index(*node)));
        }
        for id in 0..nodes.len() {
            charge(budget, 1)?;
            if domain.is_some_and(|domain| !domain.contains(&id)) {
                continue;
            }
            graph.position(id + 1, id, budget)?;
            let source = graph.sources[id];
            graph.expressions[id] = graph.build_expression(
                id,
                nodes,
                &mut symbols,
                &mut types,
                operation,
                &methods,
                adapters,
                &mut headers,
                budget,
            )?;
            if let Some(method) = methods
                .at(id, budget)?
                .iter()
                .find(|method| method.requirement.is_none())
            {
                let selected = graph.method_target(
                    method.target,
                    method.method,
                    &adapter_values,
                    &mut symbols,
                    source,
                    budget,
                )?;
                if method.arguments == 0 {
                    graph.expressions[id] = Expr::Alias(selected);
                } else {
                    let Expr::Call {
                        arguments,
                        scalar,
                        type_application: true,
                        ..
                    } = &graph.expressions[id]
                    else {
                        return Err(Failure::Invalid);
                    };
                    let start = arguments
                        .len()
                        .checked_sub(method.arguments)
                        .ok_or(Failure::Invalid)?;
                    graph.expressions[id] = Expr::Call {
                        function: selected,
                        arguments: copy_slice(&arguments[start..], budget)?,
                        scalar: *scalar,
                        type_application: true,
                    };
                }
            }
            let mut evidence = Vec::new();
            for method in methods.at(id, budget)? {
                if let Some(requirement) = method.requirement {
                    let argument = graph.method_target(
                        method.target,
                        method.method,
                        &adapter_values,
                        &mut symbols,
                        source,
                        budget,
                    )?;
                    evidence.try_reserve(1).map_err(|_| Failure::Resource)?;
                    evidence.push((requirement, method.method, argument));
                }
            }
            if !evidence.is_empty() {
                let original = std::mem::replace(&mut graph.expressions[id], Expr::Slot);
                let value = graph.push(original, source, budget)?;
                graph.expressions[id] = Expr::Evidence {
                    value,
                    bindings: evidence,
                };
            }
        }
        if let Some((clauses, handler)) = conditional {
            if handler.is_some() || clauses.is_empty() {
                return Err(Failure::Invalid);
            }
            charge(budget, clauses.len())?;
            let mut data_clauses = Vec::new();
            data_clauses
                .try_reserve_exact(clauses.len())
                .map_err(|_| Failure::Resource)?;
            for clause in clauses {
                let body = index(clause.body);
                nodes.get(body).ok_or(Failure::Invalid)?;
                data_clauses.push(graph.clause_data(
                    clause.pattern,
                    body,
                    clause.source,
                    nodes,
                    &mut symbols,
                    &mut types,
                    &methods,
                    adapters,
                    &mut headers,
                    budget,
                )?);
            }
            // Uninstantiated external body control is deliberately unavailable.
            // Sealed realization later installs the actual typed body expression.
            let source = clauses[0].source;
            let body = graph.push(Expr::Unknown, source, budget)?;
            *handler = Some(graph.push(
                Expr::Handler {
                    body,
                    clauses: data_clauses,
                },
                source,
                budget,
            )?);
        }
        charge(budget, types.len())?;
        graph
            .metadata
            .try_reserve(types.len())
            .map_err(|_| Failure::Resource)?;
        graph
            .metadata
            .extend(types.iter().map(|(variable, slot)| (*slot, *variable)));
        let mut retained = Vec::new();
        for (binder, summary) in imports {
            charge(budget, retained.len() + 1)?;
            let Some(imported) = summary.graph.as_ref().and_then(|graph| graph.data.as_ref())
            else {
                continue;
            };
            let mut offset = None;
            for (previous, start) in &retained {
                if std::ptr::eq::<Graph>(*previous, imported.as_ref()) {
                    offset = Some(*start);
                    break;
                }
            }
            let offset = if let Some(offset) = offset {
                offset
            } else {
                charge(budget, imported_callables.graphs.len())?;
                let (_, target_offset, code_offset, _) = imported_callables
                    .graphs
                    .iter()
                    .find(|(candidate, ..)| {
                        candidate
                            .data
                            .as_ref()
                            .is_some_and(|data| std::ptr::eq(data.as_ref(), imported.as_ref()))
                    })
                    .ok_or(Failure::Invalid)?;
                let offset = graph.import_graph(imported, *target_offset, *code_offset, budget)?;
                retained.try_reserve(1).map_err(|_| Failure::Resource)?;
                retained.push((imported.as_ref(), offset));
                offset
            };
            charge(budget, imported.exports.len())?;
            let value = imported
                .exports
                .iter()
                .find(|(candidate, _)| candidate == binder)
                .ok_or(Failure::Invalid)?
                .1;
            if let Some(local) = symbols.get(binder) {
                graph
                    .globals
                    .try_reserve(1)
                    .map_err(|_| Failure::Resource)?;
                graph.globals.push((*local, value + offset));
            }
        }
        graph.install_provider_parameters(independent_parameters, &symbols, budget)?;
        // A declared symbolic parameter can still be unresolved during closure.
        // A body-free external binder is instead explicitly opaque from entry.
        let mut defined = HashSet::new();
        let mut retain = |slot| -> Result<(), Failure> {
            charge(budget, 1)?;
            defined.try_reserve(1).map_err(|_| Failure::Resource)?;
            defined.insert(slot);
            Ok(())
        };
        for &(binder, _) in &graph.globals {
            retain(binder)?;
        }
        for expression in &graph.expressions {
            match expression {
                Expr::Function { parameters, .. } => {
                    for &parameter in parameters {
                        retain(parameter)?;
                    }
                }
                Expr::Bind { binder, .. } => retain(*binder)?,
                Expr::Recursive { bindings, .. } => {
                    for &(binder, _) in bindings {
                        retain(binder)?;
                    }
                }
                Expr::Match { arms, .. } => {
                    for (bindings, _) in arms {
                        for &(binder, _) in bindings {
                            retain(binder)?;
                        }
                    }
                }
                Expr::Resource {
                    handle, identity, ..
                } => {
                    retain(*handle)?;
                    retain(*identity)?;
                }
                Expr::Handler { clauses, .. } => {
                    for clause in clauses {
                        for &(binder, _) in &clause.bindings {
                            retain(binder)?;
                        }
                    }
                }
                _ => {}
            }
        }
        for slot in symbols.values() {
            charge(budget, 1)?;
            if !defined.contains(slot) {
                let opaque = graph.push(Expr::Unknown, graph.sources[*slot], budget)?;
                graph
                    .globals
                    .try_reserve(1)
                    .map_err(|_| Failure::Resource)?;
                graph.globals.push((*slot, opaque));
            }
        }
        Ok(graph)
    }

    pub(super) fn position(
        &mut self,
        code: usize,
        expression: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        charge(budget, 1)?;
        self.positions
            .try_reserve(1)
            .map_err(|_| Failure::Resource)?;
        self.positions.insert(code, expression);
        Ok(())
    }

    /// A provider's control handler corresponds to the exact handler equation
    /// inside its resource result, rather than the enclosing Scope equation.
    pub(super) fn position_provider_handler(
        &mut self,
        code: usize,
        scope: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        charge(budget, 1)?;
        let Expr::Resource { body, .. } = self.expressions.get(scope).ok_or(Failure::Invalid)?
        else {
            return Err(Failure::Invalid);
        };
        charge(budget, 1)?;
        let Expr::Tuple(fields) = self.expressions.get(*body).ok_or(Failure::Invalid)? else {
            return Err(Failure::Invalid);
        };
        let [body, _completion] = fields.as_slice() else {
            return Err(Failure::Invalid);
        };
        let mut expression = *body;
        // These are the two hidden state bindings emitted with the real scope.
        for _ in 0..2 {
            charge(budget, 1)?;
            let Expr::Bind { body, .. } =
                self.expressions.get(expression).ok_or(Failure::Invalid)?
            else {
                return Err(Failure::Invalid);
            };
            expression = *body;
        }
        charge(budget, 1)?;
        let Expr::Cleanup { body, .. } =
            self.expressions.get(expression).ok_or(Failure::Invalid)?
        else {
            return Err(Failure::Invalid);
        };
        let handler = *body;
        charge(budget, 1)?;
        if !matches!(self.expressions.get(handler), Some(Expr::Handler { .. })) {
            return Err(Failure::Invalid);
        }
        self.position(code, handler, budget)
    }

    pub(super) fn start(&self, budget: &mut TypeWorkBudget) -> Result<Analysis<'_>, Failure> {
        let mut analysis = Analysis::new(self, budget)?;
        for &(binder, value) in &self.globals {
            let initializer = analysis.slot(value, 0, budget)?;
            let binder = analysis.slot(binder, 0, budget)?;
            analysis.edge(binder, initializer, budget)?;
        }
        // Every source function body has a symbolic entry, including functions
        // that are only exported. Actual calls receive separate contexts.
        for (id, expression) in self.expressions.iter().enumerate() {
            if let Expr::Function {
                parameters,
                body,
                captures,
            } = expression
            {
                let context = analysis.context(0, Transition::Root(id), budget)?;
                analysis
                    .roots
                    .try_reserve(1)
                    .map_err(|_| Failure::Resource)?;
                analysis.roots.insert(*body, context);
                for parameter in parameters {
                    let slot = analysis.slot(*parameter, context, budget)?;
                    analysis.atom(slot, Atom::Unknown, budget)?;
                }
                for capture in captures {
                    let source = analysis.slot(*capture, 0, budget)?;
                    let target = analysis.slot(*capture, context, budget)?;
                    analysis.edge(target, source, budget)?;
                }
                analysis.slot(*body, context, budget)?;
            }
        }
        if self.globals.is_empty() {
            for id in 0..self.expressions.len() {
                if matches!(self.expressions[id], Expr::Resource { .. }) {
                    analysis.slot(id, 0, budget)?;
                }
            }
        }
        analysis.close(budget)?;
        Ok(analysis)
    }
}

fn scalar(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Bytes | Type::String | Type::Int | Type::Bool | Type::Unit
    )
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Atom {
    Free,
    Unknown,
    Closure(usize, usize),
    Aggregate(usize, usize),
    Constructor(ConstructorId),
    Resource(usize, usize),
}

#[derive(Debug)]
struct Slot {
    key: (usize, usize),
    atoms: Vec<Atom>,
    edges: Vec<usize>,
    readers: Vec<usize>,
    queued: bool,
    terminal: bool,
    // Fixed setup and Evidence input watches carry separate completed phases.
    // Neither grants frozen/cut authority or a cached live answer.
    preparation: SlotPreparation,
}

// ASH_INPUT169_BEGIN_PHASE
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SlotPreparation {
    Pending,
    // Existing queue-owned fixed setup plus successful current propagation.
    EdgesInstalled,
    // Every original Evidence input has its watch to this exact source slot.
    EvidenceInputsInstalled,
}

#[cfg(test)]
impl SlotPreparation {
    fn is_edges_installed(self) -> bool {
        self == Self::EdgesInstalled
    }
}
// ASH_INPUT169_END_PHASE

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Transition {
    Root(usize),
    Call(usize),
    Invoke(usize, usize), // Call expression and callee expression, both static graph IDs.
    Dispatch(usize, usize, usize),
    Focus,
    Restore(usize, usize, usize),
}

// Every nonempty canonical path shares its already published prefix. These
// nodes own no recursive storage, values, environments or execution authority.
#[derive(Clone, Copy, Debug)]
enum ContextPath {
    Empty,
    Step {
        parent: usize,
        transition: Transition,
        length: usize,
    },
}

impl ContextPath {
    fn length(self) -> usize {
        match self {
            Self::Empty => 0,
            Self::Step { length, .. } => length,
        }
    }
}

struct ContextPaths {
    paths: Vec<ContextPath>,
    extensions: HashMap<(usize, Transition), usize>,
}

// Absence and the exact immutable parent remain borrowed through reservation.
// Only successful reservation produces the state that can publish both entries.
struct PendingContextExtension<'a> {
    paths: &'a mut ContextPaths,
    parent: usize,
    transition: Transition,
    length: usize,
}

struct ReservedContextExtension<'a>(PendingContextExtension<'a>);

impl<'a> PendingContextExtension<'a> {
    fn reserve(self, budget: &mut TypeWorkBudget) -> Result<ReservedContextExtension<'a>, Failure> {
        // One new flat path record and one exact index entry, before either
        // allocation or publication. No full-prefix copy or hash is performed.
        charge(budget, 2)?;
        self.paths
            .paths
            .try_reserve(1)
            .map_err(|_| Failure::Resource)?;
        self.paths
            .extensions
            .try_reserve(1)
            .map_err(|_| Failure::Resource)?;
        Ok(ReservedContextExtension(self))
    }
}

impl ReservedContextExtension<'_> {
    fn publish(self) -> usize {
        let PendingContextExtension {
            paths,
            parent,
            transition,
            length,
        } = self.0;
        let id = paths.paths.len();
        paths.paths.push(ContextPath::Step {
            parent,
            transition,
            length,
        });
        paths.extensions.insert((parent, transition), id);
        id
    }
}

impl ContextPaths {
    fn new(budget: &mut TypeWorkBudget) -> Result<Self, Failure> {
        charge(budget, 1)?;
        let mut paths = Vec::new();
        paths.try_reserve(1).map_err(|_| Failure::Resource)?;
        paths.push(ContextPath::Empty);
        Ok(Self {
            paths,
            extensions: HashMap::new(),
        })
    }

    fn len(&self) -> usize {
        self.paths.len()
    }

    fn intern(
        &mut self,
        parent: usize,
        transition: Transition,
        budget: &mut TypeWorkBudget,
    ) -> Result<(usize, bool), Failure> {
        let length = self.paths.get(parent).ok_or(Failure::Invalid)?.length();
        // The original recurrence relation is checked along the whole parent
        // chain. Walking backwards must retain the OLDEST match, not the nearest.
        charge(budget, length.checked_add(1).ok_or(Failure::Resource)?)?;
        let mut cursor = parent;
        let mut repeated = None;
        while let ContextPath::Step {
            parent,
            transition: site,
            ..
        } = self.paths[cursor]
        {
            let matches = match (site, transition) {
                (Transition::Root(target), Transition::Invoke(_, callee))
                | (Transition::Invoke(_, target), Transition::Invoke(_, callee)) => {
                    target == callee
                }
                _ => site == transition,
            };
            if matches {
                repeated = Some(cursor);
            }
            cursor = parent;
        }
        if let Some(id) = repeated {
            return Ok((id, false));
        }
        charge(budget, 1)?;
        if let Some(&id) = self.extensions.get(&(parent, transition)) {
            return Ok((id, false));
        }
        let id = PendingContextExtension {
            paths: self,
            parent,
            transition,
            length: length.checked_add(1).ok_or(Failure::Resource)?,
        }
        .reserve(budget)?
        .publish();
        Ok((id, true))
    }

    fn copy(&self, budget: &mut TypeWorkBudget) -> Result<Self, Failure> {
        // The borrowed private owner already establishes every prefix relation.
        // Copy flat nodes once, rebuilding the complete index in original ID order.
        let paths = copy_slice(&self.paths, budget)?;
        let count = paths.len().checked_sub(1).ok_or(Failure::Invalid)?;
        charge(budget, count.checked_mul(2).ok_or(Failure::Resource)?)?;
        let mut extensions = HashMap::new();
        extensions
            .try_reserve(count)
            .map_err(|_| Failure::Resource)?;
        for (id, path) in paths.iter().enumerate().skip(1) {
            let ContextPath::Step {
                parent, transition, ..
            } = *path
            else {
                return Err(Failure::Invalid);
            };
            extensions.insert((parent, transition), id);
        }
        Ok(Self { paths, extensions })
    }

    fn forward(
        &self,
        context: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<Vec<Transition>, Failure> {
        let length = self.paths.get(context).ok_or(Failure::Invalid)?.length();
        // Pay scratch allocation, the parent walk and its reversal. Source
        // provenance is still validated FORWARDS by the original consumer.
        charge(
            budget,
            length
                .checked_mul(3)
                .and_then(|n| n.checked_add(1))
                .ok_or(Failure::Resource)?,
        )?;
        let mut path = Vec::new();
        path.try_reserve_exact(length)
            .map_err(|_| Failure::Resource)?;
        let mut cursor = context;
        while let ContextPath::Step {
            parent, transition, ..
        } = self.paths[cursor]
        {
            path.push(transition);
            cursor = parent;
        }
        path.reverse();
        Ok(path)
    }
}

#[derive(Clone, Copy, Debug)]
pub(super) struct Cut {
    pub(super) context: usize,
    pub(super) input: usize,
    pub(super) result: usize,
}

struct PreparedCut {
    cut: Cut,
    pending: usize,
    completed: Vec<usize>,
    terminal_result: bool,
}

// Scalar original-expression coordinates only. Dynamic slots, atoms and
// notification watches are always reconstructed in the current contexts.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct CaptureVisit {
    expression: usize,
    binding_start: usize,
    binding_end: usize,
    lexical: bool,
}

#[derive(Debug, Eq, PartialEq)]
struct CaptureTopology {
    visits: Vec<CaptureVisit>,
    bindings: Vec<usize>,
    // The complete original dictionary projection, prepared for this exact
    // Graph/function/Evidence pair. Transfer completion remains contextful.
    dictionary: PreparedDictionaryRoutes,
}

// A matched Function installs structural capture coordinates, not live reads.
// This temporary exclusive visit is consumed before Closure publication returns.
struct FunctionCaptureInstallation<'s, 'g> {
    analysis: &'s mut Analysis<'g>,
    slot: usize,
    expression: usize,
    creation: usize,
    body: usize,
    captures: &'g [usize],
}

impl FunctionCaptureInstallation<'_, '_> {
    fn install(self, budget: &mut TypeWorkBudget) -> Result<(), Failure> {
        let Self {
            analysis,
            slot,
            expression,
            creation,
            body,
            captures,
        } = self;
        for capture in captures {
            let source = analysis.install_slot(*capture, creation, budget)?;
            if let Some(root) = analysis.roots.get(&body).copied() {
                let target = analysis.install_slot(*capture, root, budget)?;
                analysis.edge(target, source, budget)?;
            }
        }
        analysis.atom(slot, Atom::Closure(expression, creation), budget)
    }
}

// Private marker policies only distinguish structural coordinates from reads.
struct ObservedCallInputs;
struct OwnCallInputs;

trait CallSlotPolicy {
    fn slot(
        &self,
        analysis: &mut Analysis<'_>,
        expression: usize,
        context: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<usize, Failure>;
}

impl CallSlotPolicy for ObservedCallInputs {
    fn slot(
        &self,
        analysis: &mut Analysis<'_>,
        expression: usize,
        context: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<usize, Failure> {
        analysis.slot(expression, context, budget)
    }
}

impl CallSlotPolicy for OwnCallInputs {
    fn slot(
        &self,
        analysis: &mut Analysis<'_>,
        expression: usize,
        context: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<usize, Failure> {
        analysis.install_slot(expression, context, budget)
    }
}

// Produced only after the original live Call/Function match, arity validation,
// exact full-stamp lookup and fallible completion reservation.
struct CallTransferInstallation<'s, 'g, 'v> {
    analysis: &'s mut Analysis<'g>,
    slot: usize,
    expression: usize,
    context: usize,
    target: usize,
    creation: usize,
    parameters: &'g [usize],
    captures: &'g [usize],
    actual: &'v [usize],
    body: usize,
    transfer: (Option<usize>, usize, usize, usize),
}

impl CallTransferInstallation<'_, '_, '_> {
    fn install(self, budget: &mut TypeWorkBudget) -> Result<(), Failure> {
        let invoked = self.analysis.context(
            self.context,
            Transition::Invoke(self.expression, self.target),
            budget,
        )?;
        // Only this actual exact reader can omit structural shortcut watches.
        charge(budget, 1)?;
        if self.analysis.current == Some(self.slot) {
            self.install_inputs(OwnCallInputs, invoked, budget)
        } else {
            self.install_inputs(ObservedCallInputs, invoked, budget)
        }
    }

    fn install_inputs<P: CallSlotPolicy>(
        self,
        policy: P,
        invoked: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        let Self {
            analysis,
            slot,
            creation,
            parameters,
            captures,
            actual,
            body,
            transfer,
            ..
        } = self;
        for (&parameter, &argument) in parameters.iter().zip(actual) {
            let parameter = policy.slot(analysis, parameter, invoked, budget)?;
            analysis.edge(parameter, argument, budget)?;
        }
        for capture in captures {
            let destination = policy.slot(analysis, *capture, invoked, budget)?;
            let source = policy.slot(analysis, *capture, creation, budget)?;
            analysis.edge(destination, source, budget)?;
        }
        // The body output remains observed and every live edge remains intact.
        analysis.link(slot, body, invoked, budget)?;
        analysis.callable_transfers.insert(transfer);
        Ok(())
    }
}

// Produced only by the paid exact own-reader guard of the actual Evidence visit.
// The token remains transient under that visit's exclusive Analysis loan.
#[derive(Clone, Copy)]
struct OwnEvidenceReader;

#[derive(Clone, Copy)]
enum EvidenceReader {
    Own(OwnEvidenceReader),
    Other,
}

// Successful input installation consumes evaluate's actual Evidence match.
// Its exact Analysis loan then stays with the succeeding dynamic phases and
// returns after an atom is processed; no stored phase grants live answers.
struct CheckedEvidenceVisit<'s, 'g> {
    analysis: &'s mut Analysis<'g>,
    reader: EvidenceReader,
    slot: usize,
    evidence: usize,
    arguments_context: usize,
    bindings: &'g [(
        crate::interface::RequirementId,
        crate::interface::MethodId,
        usize,
    )],
}

// ASH_INPUT169_BEGIN_INSTALL
// Only evaluate's actual original Evidence match constructs this preparation.
// Its borrowed bindings and exact slot/context remain with the consumed loan.
struct EvidenceInputVisit<'s, 'g> {
    analysis: &'s mut Analysis<'g>,
    slot: usize,
    evidence: usize,
    arguments_context: usize,
    value: usize,
    bindings: &'g [(
        crate::interface::RequirementId,
        crate::interface::MethodId,
        usize,
    )],
}

struct InstalledEvidenceInputs<'s, 'g> {
    visit: CheckedEvidenceVisit<'s, 'g>,
    value: usize,
}

impl<'s, 'g> EvidenceInputVisit<'s, 'g> {
    fn install_inputs(
        self,
        budget: &mut TypeWorkBudget,
    ) -> Result<InstalledEvidenceInputs<'s, 'g>, Failure> {
        let Self {
            analysis,
            slot,
            evidence,
            arguments_context: context,
            value: original_value,
            bindings,
        } = self;
        // Pay the exact-reader guard and scalar preparation classification.
        charge(budget, 1)?;
        let own_reader = analysis.current == Some(slot);
        let value = if own_reader
            && analysis.slots[slot].preparation == SlotPreparation::EvidenceInputsInstalled
        {
            // The completed phase proves this exact coordinate and its reader
            // watch were installed. Read the original port; never fabricate it.
            charge(budget, 1)?;
            *analysis
                .indices
                .get(&(original_value, context))
                .ok_or(Failure::Invalid)?
        } else {
            // Preserve every original input and ordered watch installation.
            let value = analysis.slot(original_value, context, budget)?;
            for (_, _, argument) in bindings {
                analysis.slot(*argument, context, budget)?;
            }
            if own_reader {
                // The Slot already owns this scalar phase. Publish only after
                // the entire input prologue succeeds and its store is admitted.
                charge(budget, 1)?;
                analysis.slots[slot].preparation = SlotPreparation::EvidenceInputsInstalled;
            }
            value
        };
        Ok(InstalledEvidenceInputs {
            value,
            visit: CheckedEvidenceVisit {
                analysis,
                reader: if own_reader {
                    EvidenceReader::Own(OwnEvidenceReader)
                } else {
                    EvidenceReader::Other
                },
                slot,
                evidence,
                arguments_context: context,
                bindings,
            },
        })
    }
}
// ASH_INPUT169_END_INSTALL

struct ObservedCaptureSlots;

// The two private policies share one exact installer; neither carries answers.
trait CaptureSlotPolicy {
    fn prepare(&self, budget: &mut TypeWorkBudget) -> Result<(), Failure>;
    fn slot(
        &self,
        analysis: &mut Analysis<'_>,
        expression: usize,
        context: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<usize, Failure>;
}

impl CaptureSlotPolicy for ObservedCaptureSlots {
    fn prepare(&self, _budget: &mut TypeWorkBudget) -> Result<(), Failure> {
        Ok(())
    }
    fn slot(
        &self,
        analysis: &mut Analysis<'_>,
        expression: usize,
        context: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<usize, Failure> {
        analysis.slot(expression, context, budget)
    }
}

impl CaptureSlotPolicy for OwnEvidenceReader {
    fn prepare(&self, budget: &mut TypeWorkBudget) -> Result<(), Failure> {
        charge(budget, 1)
    }
    fn slot(
        &self,
        analysis: &mut Analysis<'_>,
        expression: usize,
        context: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<usize, Failure> {
        analysis.install_slot(expression, context, budget)
    }
}

// Consumes the actual Evidence visit's reader proof and one exact transfer.
// No phase completion survives outside the existing full transfer stamp.
struct CaptureTransferInstallation<'s, 'g, P> {
    analysis: &'s mut Analysis<'g>,
    policy: P,
    function: usize,
    creation: usize,
    specialized: usize,
    evidence: usize,
    arguments_context: usize,
}

impl<P: CaptureSlotPolicy> CaptureTransferInstallation<'_, '_, P> {
    fn install(self, budget: &mut TypeWorkBudget) -> Result<usize, Failure> {
        let Self {
            analysis,
            policy,
            function,
            creation,
            specialized,
            evidence,
            arguments_context,
        } = self;
        let plan = analysis.prepare_capture_topology(function, evidence, budget)?;
        let Expr::Evidence { bindings, .. } = &analysis.graph.expressions[evidence] else {
            return Err(Failure::Invalid);
        };
        if analysis.capture_topologies[plan].visits.is_empty() {
            return Ok(plan);
        }
        let transfer = (
            analysis.current,
            function,
            creation,
            specialized,
            evidence,
            arguments_context,
        );
        charge(budget, 1)?;
        if analysis.specialization_transfers.contains(&transfer) {
            return Ok(plan);
        }
        // Admit the completion entry before any transfer mutation. Only after
        // every original slot/link succeeds may a repeated transfer be skipped.
        charge(budget, 1)?;
        analysis
            .specialization_transfers
            .try_reserve(1)
            .map_err(|_| Failure::Resource)?;
        // Only the structural policy pays for consuming its owned-reader phase.
        policy.prepare(budget)?;
        let visit_count = analysis.capture_topologies[plan].visits.len();
        for position in 0..visit_count {
            charge(budget, 1)?;
            let visit = analysis.capture_topologies[plan].visits[position];
            // Structural destinations are never read here; installed edges remain live.
            let destination = policy.slot(analysis, visit.expression, specialized, budget)?;
            for position in visit.binding_start..visit.binding_end {
                charge(budget, 1)?;
                let original = analysis.capture_topologies[plan].bindings[position];
                let source =
                    policy.slot(analysis, bindings[original].2, arguments_context, budget)?;
                analysis.edge(destination, source, budget)?;
            }
            if visit.lexical {
                let source = policy.slot(analysis, visit.expression, creation, budget)?;
                analysis.edge(destination, source, budget)?;
            }
        }
        // Existing edges and watches still carry every later atom change.
        analysis.specialization_transfers.insert(transfer);
        Ok(plan)
    }
}

struct ReservedEvidenceTransfer<'s, 'g> {
    visit: CheckedEvidenceVisit<'s, 'g>,
    function: usize,
    creation: usize,
    stamp: (Option<usize>, usize, usize, usize),
}

enum EvidenceTransferStage<'s, 'g> {
    Complete(CheckedEvidenceVisit<'s, 'g>),
    Reserved(ReservedEvidenceTransfer<'s, 'g>),
}

struct InstalledCaptureBindings<'s, 'g> {
    visit: CheckedEvidenceVisit<'s, 'g>,
    plan: usize,
    specialized: usize,
    function: usize,
    stamp: (Option<usize>, usize, usize, usize),
}

#[derive(Debug, Eq, PartialEq)]
enum PreparedDictionaryRoutes {
    Complete,
    Pending(Vec<DictionaryObligation>),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct DictionaryObligation {
    binding: usize,
    evidence: usize,
}

// This phase means dictionary-complete and ready to publish, not yet published.
struct ReadyClosure<'s, 'g> {
    visit: CheckedEvidenceVisit<'s, 'g>,
    function: usize,
    specialized: usize,
    stamp: (Option<usize>, usize, usize, usize),
}

impl<'s, 'g> CheckedEvidenceVisit<'s, 'g> {
    fn reserve(
        self,
        function: usize,
        creation: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<EvidenceTransferStage<'s, 'g>, Failure> {
        // Each live Closure still proves its original Function code. The
        // Evidence/slot association is already carried by this actual visit.
        charge(budget, 1)?;
        if !matches!(
            self.analysis.graph.expressions.get(function),
            Some(Expr::Function { .. })
        ) {
            return Err(Failure::Invalid);
        }
        let stamp = (self.analysis.current, self.slot, function, creation);
        charge(budget, 1)?;
        if self.analysis.callable_transfers.contains(&stamp) {
            return Ok(EvidenceTransferStage::Complete(self));
        }
        charge(budget, 1)?;
        self.analysis
            .callable_transfers
            .try_reserve(1)
            .map_err(|_| Failure::Resource)?;
        Ok(EvidenceTransferStage::Reserved(ReservedEvidenceTransfer {
            visit: self,
            function,
            creation,
            stamp,
        }))
    }

    fn route_atom(self, atom: Atom, budget: &mut TypeWorkBudget) -> Result<Self, Failure> {
        match atom {
            Atom::Closure(function, creation) => match self.reserve(function, creation, budget)? {
                EvidenceTransferStage::Complete(visit) => Ok(visit),
                EvidenceTransferStage::Reserved(pending) => pending
                    .install_captures(budget)?
                    .route_dictionary(budget)?
                    .publish(budget),
            },
            other => {
                self.analysis.atom(self.slot, other, budget)?;
                if matches!(other, Atom::Unknown) {
                    for (_, _, argument) in self.bindings {
                        let argument =
                            self.analysis
                                .slot(*argument, self.arguments_context, budget)?;
                        for dependency in self.analysis.dependencies(argument, budget)? {
                            self.analysis.atom(self.slot, dependency, budget)?;
                        }
                    }
                }
                Ok(self)
            }
        }
    }
}

impl<'s, 'g> ReservedEvidenceTransfer<'s, 'g> {
    fn install_captures(
        self,
        budget: &mut TypeWorkBudget,
    ) -> Result<InstalledCaptureBindings<'s, 'g>, Failure> {
        let Self {
            visit,
            function,
            creation,
            stamp,
        } = self;
        let specialized = visit.analysis.context(
            visit.arguments_context,
            Transition::Call(visit.evidence),
            budget,
        )?;
        let plan = match visit.reader {
            EvidenceReader::Other => visit.analysis.specialize_captures(
                function,
                creation,
                specialized,
                visit.evidence,
                visit.arguments_context,
                budget,
            )?,
            EvidenceReader::Own(reader) => CaptureTransferInstallation {
                analysis: visit.analysis,
                policy: reader,
                function,
                creation,
                specialized,
                evidence: visit.evidence,
                arguments_context: visit.arguments_context,
            }
            .install(budget)?,
        };
        Ok(InstalledCaptureBindings {
            visit,
            plan,
            specialized,
            function,
            stamp,
        })
    }
}

impl<'s, 'g> InstalledCaptureBindings<'s, 'g> {
    fn route_dictionary(
        self,
        budget: &mut TypeWorkBudget,
    ) -> Result<ReadyClosure<'s, 'g>, Failure> {
        let Self {
            visit,
            plan,
            specialized,
            function,
            stamp,
        } = self;
        // Only this successful exact contextful transfer can consume the
        // immutable projection. Every uncaptured original port remains pending.
        charge(budget, 1)?;
        match &visit.analysis.capture_topologies[plan].dictionary {
            PreparedDictionaryRoutes::Complete => {}
            PreparedDictionaryRoutes::Pending(obligations) => {
                let count = obligations.len();
                for position in 0..count {
                    // Read both original coordinates, preserving their order.
                    charge(budget, 2)?;
                    let obligation = match &visit.analysis.capture_topologies[plan].dictionary {
                        PreparedDictionaryRoutes::Pending(obligations) => obligations[position],
                        PreparedDictionaryRoutes::Complete => return Err(Failure::Invalid),
                    };
                    let argument = visit
                        .bindings
                        .get(obligation.binding)
                        .ok_or(Failure::Invalid)?
                        .2;
                    let port = visit
                        .analysis
                        .graph
                        .evidence
                        .get(obligation.evidence)
                        .ok_or(Failure::Invalid)?
                        .1;
                    let target = visit.analysis.slot(port, specialized, budget)?;
                    visit
                        .analysis
                        .link(target, argument, visit.arguments_context, budget)?;
                }
            }
        }
        Ok(ReadyClosure {
            visit,
            function,
            specialized,
            stamp,
        })
    }
}

impl<'s, 'g> ReadyClosure<'s, 'g> {
    fn publish(self, budget: &mut TypeWorkBudget) -> Result<CheckedEvidenceVisit<'s, 'g>, Failure> {
        self.visit.analysis.atom(
            self.visit.slot,
            Atom::Closure(self.function, self.specialized),
            budget,
        )?;
        // Reservation belongs to this same exclusive loan. Commit only after
        // dictionary routing and output succeed, then return the exact visit.
        self.visit.analysis.callable_transfers.insert(self.stamp);
        Ok(self.visit)
    }
}

// A queue-owned evaluation carries its exact reader through one exclusive visit.
// The original edge owns the source notification for structural Alias/Merge links.
struct QueuedEvaluation<'s, 'g> {
    analysis: &'s mut Analysis<'g>,
    slot: usize,
}

#[cfg(test)]
#[derive(Clone, Copy)]
struct ObservedAliasLinks;
#[derive(Clone, Copy)]
struct QueuedAliasLinks;

trait AliasLinkPolicy {
    fn link(
        analysis: &mut Analysis<'_>,
        target: usize,
        expression: usize,
        context: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure>;
}

#[cfg(test)]
impl AliasLinkPolicy for ObservedAliasLinks {
    fn link(
        analysis: &mut Analysis<'_>,
        target: usize,
        expression: usize,
        context: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        analysis.link(target, expression, context, budget)
    }
}

impl AliasLinkPolicy for QueuedAliasLinks {
    fn link(
        analysis: &mut Analysis<'_>,
        target: usize,
        expression: usize,
        context: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        let source = analysis.install_slot(expression, context, budget)?;
        analysis.edge(target, source, budget)
    }
}

impl<'s, 'g> QueuedEvaluation<'s, 'g> {
    fn evaluate(self, budget: &mut TypeWorkBudget) -> Result<bool, Failure> {
        self.analysis
            .evaluate_with_alias_links::<QueuedAliasLinks>(self.slot, budget)
    }
}

// One word retains either a watch-only relation or a complete linked prefix.
// MAX cannot be an Atom Vec prefix: Vec allocation lengths are bounded below
// usize::MAX. It is not a new work/depth/graph limit. The original prefix range
// check rejects this sentinel together with every other malformed cursor.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct DependencyProgress(usize);

impl DependencyProgress {
    const WATCHING: Self = Self(usize::MAX);
    const LINKED_EMPTY: Self = Self(0);
}

#[derive(Default)]
struct DependencyRelations {
    // Exact (target/reader, source), with original slot contexts preserved.
    entries: HashMap<(usize, usize), DependencyProgress>,
}

// The exclusive table loan preserves the exact absent or watch-only claim
// through all fallible reservation. Only these producers can publish links.
struct VacantDependency<'a> {
    entries: &'a mut HashMap<(usize, usize), DependencyProgress>,
    pair: (usize, usize),
}

struct ReservedDependency<'a> {
    entries: &'a mut HashMap<(usize, usize), DependencyProgress>,
    pair: (usize, usize),
}

struct WatchingDependency<'a> {
    entries: &'a mut HashMap<(usize, usize), DependencyProgress>,
    pair: (usize, usize),
}

enum WatchPreparation<'a> {
    Complete,
    Vacant(VacantDependency<'a>),
}

enum LinkInstallation<'a> {
    Vacant(VacantDependency<'a>),
    Watching(WatchingDependency<'a>),
}

enum ReservedLinkInstallation<'a> {
    Vacant(ReservedDependency<'a>),
    Watching(WatchingDependency<'a>),
}

enum EdgePreparation<'a> {
    Complete,
    Install(LinkInstallation<'a>),
}

impl<'a> VacantDependency<'a> {
    fn reserve(self) -> Result<ReservedDependency<'a>, Failure> {
        self.entries.try_reserve(1).map_err(|_| Failure::Resource)?;
        Ok(ReservedDependency {
            entries: self.entries,
            pair: self.pair,
        })
    }
}

impl ReservedDependency<'_> {
    fn publish_watching(self) {
        self.entries.insert(self.pair, DependencyProgress::WATCHING);
    }

    fn publish_linked(self) {
        self.entries
            .insert(self.pair, DependencyProgress::LINKED_EMPTY);
    }
}

impl WatchingDependency<'_> {
    fn publish_linked(self) {
        // The exact existing entry cannot allocate; the exclusive table loan
        // has admitted no mutation since the Watching producer classified it.
        self.entries
            .insert(self.pair, DependencyProgress::LINKED_EMPTY);
    }
}

impl ReservedLinkInstallation<'_> {
    fn publish(self) {
        match self {
            Self::Vacant(pending) => pending.publish_linked(),
            Self::Watching(pending) => pending.publish_linked(),
        }
    }
}

// Initially this may be watch-only or malformed. Consuming the ORIGINAL
// source-prefix range check is the producer of the linked cursor authority.
struct PendingDependencyCursor<'a> {
    progress: &'a mut DependencyProgress,
}

struct LinkedDependencyCursor<'a> {
    cursor: &'a mut usize,
    delivered: usize,
    end: usize,
}

impl<'a> PendingDependencyCursor<'a> {
    fn prepare(self, atoms: &[Atom]) -> Result<LinkedDependencyCursor<'a>, Failure> {
        let delivered = self.progress.0;
        let end = atoms.len();
        atoms.get(delivered..end).ok_or(Failure::Invalid)?;
        Ok(LinkedDependencyCursor {
            cursor: &mut self.progress.0,
            delivered,
            end,
        })
    }
}

impl LinkedDependencyCursor<'_> {
    fn publish(self) {
        *self.cursor = self.end;
    }
}

impl DependencyRelations {
    fn prepare_watch(
        &mut self,
        source: usize,
        reader: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<WatchPreparation<'_>, Failure> {
        charge(budget, 1)?;
        let pair = (reader, source);
        if self.entries.contains_key(&pair) {
            return Ok(WatchPreparation::Complete);
        }
        Ok(WatchPreparation::Vacant(VacantDependency {
            entries: &mut self.entries,
            pair,
        }))
    }

    fn prepare_edge(
        &mut self,
        target: usize,
        source: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<EdgePreparation<'_>, Failure> {
        charge(budget, 1)?;
        let pair = (target, source);
        if let Some(progress) = self.entries.get(&pair).copied() {
            // This occupied-entry phase read is additional performed work.
            charge(budget, 1)?;
            if progress == DependencyProgress::WATCHING {
                return Ok(EdgePreparation::Install(LinkInstallation::Watching(
                    WatchingDependency {
                        entries: &mut self.entries,
                        pair,
                    },
                )));
            }
            return Ok(EdgePreparation::Complete);
        }
        Ok(EdgePreparation::Install(LinkInstallation::Vacant(
            VacantDependency {
                entries: &mut self.entries,
                pair,
            },
        )))
    }

    fn pending_cursor(
        &mut self,
        pair: (usize, usize),
    ) -> Result<PendingDependencyCursor<'_>, Failure> {
        let progress = self.entries.get_mut(&pair).ok_or(Failure::Invalid)?;
        Ok(PendingDependencyCursor { progress })
    }
}

// This short loan contains precisely the mutable fields of original atom().
// The edge-cursor table is absent, so propagation cannot invalidate its loan.
struct AtomStore<'s> {
    slots: &'s mut Vec<Slot>,
    atom_pairs: &'s mut HashSet<(usize, Atom)>,
    pending: &'s mut VecDeque<usize>,
    revision: &'s mut usize,
}

impl AtomStore<'_> {
    fn atom(
        &mut self,
        slot: usize,
        atom: Atom,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        // Slot identity includes its exact expression/context; Atom retains
        // its variant and original code/creation coordinates. The ordered Vec
        // remains the sole propagation source, while this set tests membership.
        charge(budget, 1)?;
        let pair = (slot, atom);
        if self.atom_pairs.contains(&pair) {
            return Ok(());
        }
        charge(budget, 2)?;
        self.atom_pairs
            .try_reserve(1)
            .map_err(|_| Failure::Resource)?;
        self.slots[slot]
            .atoms
            .try_reserve(1)
            .map_err(|_| Failure::Resource)?;
        let reader_count = self.slots[slot].readers.len();
        // Prepay the actual ordered notification walk and reserve its maximum
        // possible queue growth. No fallible operation follows publication.
        charge(budget, reader_count)?;
        self.pending
            .try_reserve(reader_count)
            .map_err(|_| Failure::Resource)?;
        self.atom_pairs.insert(pair);
        self.slots[slot].atoms.push(atom);
        *self.revision += 1;
        for index in 0..reader_count {
            let reader = self.slots[slot].readers[index];
            if !self.slots[reader].queued {
                self.pending.push_back(reader);
                self.slots[reader].queued = true;
            }
        }
        Ok(())
    }
}

pub(super) struct Analysis<'a> {
    graph: &'a Graph,
    evidence_ports: HashMap<usize, Vec<usize>>,
    evidence_keys:
        HashMap<(crate::interface::RequirementId, crate::interface::MethodId), Vec<usize>>,
    // Exact immutable Evidence expression -> key -> ordered binding positions.
    // This indexes source bindings only; slots and creation contexts stay live.
    binding_indices: HashMap<
        usize,
        HashMap<(crate::interface::RequirementId, crate::interface::MethodId), Vec<usize>>,
    >,
    // Analysis-local exact (Function expression, Evidence expression) topology.
    // The graph is borrowed immutably for the complete lifetime of this index.
    capture_topology_indices: HashMap<(usize, usize), usize>,
    capture_topologies: Vec<CaptureTopology>,
    contexts: ContextPaths,
    slots: Vec<Slot>,
    atom_pairs: HashSet<(usize, Atom)>,
    // One exact relation retains watch-only or linked-prefix progress.
    // Ordered edge vectors and readers still control transfer/notification.
    dependencies: DependencyRelations,
    // Successful immutable Call/Evidence transfers for exact reader, source
    // slot and Closure(code, creation). Live atoms remain in the ordinary graph.
    callable_transfers: HashSet<(Option<usize>, usize, usize, usize)>,
    // Completed topology only, keyed by exact reader and every source/context
    // coordinate. No stored values or completion demand are retained here.
    specialization_transfers: HashSet<(Option<usize>, usize, usize, usize, usize, usize)>,
    indices: HashMap<(usize, usize), usize>,
    roots: HashMap<usize, usize>,
    revision: usize,
    pending: VecDeque<usize>,
    current: Option<usize>,
    frozen_contexts: usize,
    focus: Option<(usize, usize)>,
    cuts: HashMap<(usize, usize, usize), PreparedCut>,
    provider_closed_data: bool,
}

impl<'a> Analysis<'a> {
    #[allow(clippy::too_many_arguments)] // Static cut identity and its terminal contract are separate inputs.
    pub(super) fn restore_cut(
        &mut self,
        creation: usize,
        code: usize,
        position: usize,
        pending: usize,
        completed: &[usize],
        terminal_result: bool,
        budget: &mut TypeWorkBudget,
    ) -> Result<Cut, Failure> {
        if creation >= self.frozen_contexts {
            return Err(Failure::Invalid);
        }
        let key = (creation, code, position);
        charge(budget, completed.len() + 1)?;
        if let Some(prepared) = self.cuts.get(&key) {
            // The control site's static cut determines these arguments. Keep
            // the private boundary exact if a caller supplies another contract.
            if prepared.pending != pending
                || prepared.completed != completed
                || prepared.terminal_result != terminal_result
            {
                return Err(Failure::Invalid);
            }
            return Ok(prepared.cut);
        }
        let (_, focus) = self.focus.ok_or(Failure::Invalid)?;
        let expression = *self.graph.positions.get(&code).ok_or(Failure::Invalid)?;
        let input = *self.graph.positions.get(&pending).ok_or(Failure::Invalid)?;
        let context = self.context(focus, Transition::Restore(creation, code, position), budget)?;
        // The static cut, not a dynamic execution history, determines which
        // slots are completed values and which one receives the pending result.
        for root in [expression, input] {
            for value in self.graph.free_inputs(root, budget)? {
                self.freeze_slot(value, creation, context, budget)?;
            }
        }
        for code in completed {
            charge(budget, 1)?;
            if let Some(&value) = self.graph.positions.get(code) {
                self.freeze_slot(value, creation, context, budget)?;
            }
        }
        let input = self.slot(input, context, budget)?;
        self.slots[input].terminal = true;
        let result = self.slot(expression, context, budget)?;
        if terminal_result {
            self.slots[result].terminal = true;
            if let Expr::Resource {
                success: Some(_),
                body,
                ..
            } = self.graph.expressions[expression]
            {
                if self.slots[input].key != (body, context) {
                    return Err(Failure::Invalid);
                }
                // This body already owns a successful acquisition. Preserve its
                // result wrapper over the frozen input; never replay acquisition.
                self.atom(result, Atom::Aggregate(expression, context), budget)?;
            } else {
                self.edge(result, input, budget)?;
            }
        }
        let cut = Cut {
            context,
            input,
            result,
        };
        let completed = copy_slice(completed, budget)?;
        charge(budget, 1)?;
        self.cuts.try_reserve(1).map_err(|_| Failure::Resource)?;
        self.cuts.insert(
            key,
            PreparedCut {
                cut,
                pending,
                completed,
                terminal_result,
            },
        );
        Ok(cut)
    }

    pub(super) fn join_ports(
        &mut self,
        target: usize,
        source: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        self.edge(target, source, budget)
    }

    pub(super) fn restore_event(
        &mut self,
        port: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<usize, Failure> {
        let (expression, creation) = self.slots[port].key;
        if creation >= self.frozen_contexts {
            return Ok(port);
        }
        let (_, focus) = self.focus.ok_or(Failure::Invalid)?;
        let context = self.context(
            focus,
            Transition::Restore(creation, expression, usize::MAX),
            budget,
        )?;
        let result = self.slot(expression, context, budget)?;
        self.slots[result].terminal = true;
        Ok(result)
    }

    pub(super) fn focused(
        &self,
        code: usize,
        creation: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<(Self, usize), Failure> {
        let expression = *self.graph.positions.get(&code).ok_or(Failure::Invalid)?;
        let Expr::Resource {
            success,
            handle,
            identity,
            body,
            ..
        } = self.graph.expressions[expression]
        else {
            return Err(Failure::Invalid);
        };
        let mut query = Self::new(self.graph, budget)?;
        charge(budget, self.slots.len())?;
        query.contexts = self.contexts.copy(budget)?;
        query.frozen_contexts = query.contexts.len();
        query
            .slots
            .try_reserve(self.slots.len())
            .map_err(|_| Failure::Resource)?;
        query
            .indices
            .try_reserve(self.slots.len())
            .map_err(|_| Failure::Resource)?;
        for slot in &self.slots {
            let id = query.slots.len();
            let atoms = copy_slice(&slot.atoms, budget)?;
            charge(budget, atoms.len().checked_mul(2).ok_or(Failure::Resource)?)?;
            query
                .atom_pairs
                .try_reserve(atoms.len())
                .map_err(|_| Failure::Resource)?;
            for atom in &atoms {
                query.atom_pairs.insert((id, *atom));
            }
            query.indices.insert(slot.key, id);
            query.slots.push(Slot {
                key: slot.key,
                atoms,
                edges: Vec::new(),
                readers: Vec::new(),
                queued: false,
                terminal: true,
                preparation: SlotPreparation::Pending,
            });
        }
        let context = query.context(0, Transition::Focus, budget)?;
        query.focus = Some((expression, context));
        for input in self.graph.free_inputs(expression, budget)? {
            query.freeze_slot(input, creation, context, budget)?;
        }
        for input in [handle, identity] {
            let input = query.slot(input, context, budget)?;
            query.atom(input, Atom::Resource(expression, context), budget)?;
        }
        let result = query.slot(expression, context, budget)?;
        query.slots[result].terminal = true;
        if success.is_some() {
            query.slot(body, context, budget)?;
            query.atom(result, Atom::Aggregate(expression, context), budget)?;
        } else {
            query.link(result, body, context, budget)?;
        }
        query.close(budget)?;
        Ok((query, context))
    }

    fn freeze_slot(
        &mut self,
        expression: usize,
        frozen: usize,
        active: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        charge(budget, 1)?;
        let source = *self
            .indices
            .get(&(expression, frozen))
            .ok_or(Failure::Invalid)?;
        let target = self.slot(expression, active, budget)?;
        if !self.slots[target].terminal
            && (!self.slots[target].atoms.is_empty() || !self.slots[target].edges.is_empty())
        {
            return Err(Failure::Invalid);
        }
        self.slots[target].terminal = true;
        for atom in copy_slice(&self.slots[source].atoms, budget)? {
            self.atom(target, atom, budget)?;
        }
        Ok(())
    }

    /// Seed a real source callable with an independently checked closed-data input.
    pub(super) fn provider_invoke(
        &mut self,
        target: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<usize, Failure> {
        charge(budget, self.graph.targets.len())?;
        let target = self
            .graph
            .targets
            .iter()
            .find_map(|(expression, candidate)| (*candidate == target).then_some(*expression))
            .ok_or(Failure::Invalid)?;
        let Expr::Function {
            parameters,
            body,
            captures,
        } = &self.graph.expressions[target]
        else {
            return Err(Failure::Invalid);
        };
        if parameters.len() != 1 {
            return Err(Failure::Invalid);
        }
        let context = self.context(0, Transition::Invoke(usize::MAX, target), budget)?;
        let parameter = self.slot(parameters[0], context, budget)?;
        self.atom(parameter, Atom::Free, budget)?;
        for capture in captures {
            let source = self.slot(*capture, 0, budget)?;
            let destination = self.slot(*capture, context, budget)?;
            self.edge(destination, source, budget)?;
        }
        self.slot(*body, context, budget)?;
        self.close(budget)?;
        Ok(context)
    }

    pub(super) fn provider_captures(
        &mut self,
        target: usize,
        context: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        charge(budget, self.graph.targets.len())?;
        let expression = self
            .graph
            .targets
            .iter()
            .find_map(|(expression, candidate)| (*candidate == target).then_some(*expression))
            .ok_or(Failure::Invalid)?;
        let Expr::Function { captures, .. } = &self.graph.expressions[expression] else {
            return Err(Failure::Invalid);
        };
        for capture in captures {
            let slot = *self
                .indices
                .get(&(*capture, context))
                .ok_or(Failure::Invalid)?;
            self.provider_independent_slot(slot, true, budget)?;
        }
        Ok(())
    }

    pub(super) fn provider_result(
        &mut self,
        code: usize,
        context: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        let slot = self.port(code, context, budget)?;
        self.close(budget)?;
        self.provider_independent_slot(slot, false, budget)
    }

    fn provider_independent_slot(
        &self,
        root: usize,
        allow_callable: bool,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        let mut pending = copy_slice(&[root], budget)?;
        let mut visited = HashSet::new();
        while let Some(slot) = pending.pop() {
            charge(budget, 1)?;
            visited.try_reserve(1).map_err(|_| Failure::Resource)?;
            if !visited.insert(slot) {
                continue;
            }
            let atoms = &self.slots.get(slot).ok_or(Failure::Invalid)?.atoms;
            if atoms.is_empty() {
                return Err(Failure::Invalid);
            }
            for atom in atoms {
                let fields = match *atom {
                    Atom::Free | Atom::Constructor(_) => None,
                    Atom::Closure(target, context) if allow_callable => {
                        let Expr::Function { captures, .. } = &self.graph.expressions[target]
                        else {
                            return Err(Failure::Invalid);
                        };
                        Some((captures.as_slice(), context))
                    }
                    Atom::Aggregate(target, context) => match &self.graph.expressions[target] {
                        Expr::Tuple(fields) => Some((fields.as_slice(), context)),
                        Expr::Call { arguments, .. } => Some((arguments.as_slice(), context)),
                        _ => return Err(Failure::Invalid),
                    },
                    _ => return Err(Failure::Invalid),
                };
                if let Some((fields, context)) = fields {
                    charge(budget, fields.len())?;
                    pending
                        .try_reserve(fields.len())
                        .map_err(|_| Failure::Resource)?;
                    for field in fields {
                        pending.push(
                            *self
                                .indices
                                .get(&(*field, context))
                                .ok_or(Failure::Invalid)?,
                        );
                    }
                }
            }
        }
        Ok(())
    }

    pub(super) fn revision(&self) -> usize {
        self.revision
    }

    pub(super) fn actual_request_path(
        &self,
        port: usize,
        context: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<(Span, Vec<super::ActualValuePathStep>), Failure> {
        let (expression, _) = self.slots.get(port).ok_or(Failure::Invalid)?.key;
        let request = *self.graph.sources.get(expression).ok_or(Failure::Invalid)?;
        let path = self.contexts.forward(context, budget)?;
        charge(budget, path.len())?;
        let mut output = Vec::new();
        output
            .try_reserve_exact(path.len())
            .map_err(|_| Failure::Resource)?;
        let source = |expression: usize| {
            self.graph
                .sources
                .get(expression)
                .copied()
                .ok_or(Failure::Invalid)
        };
        for step in &path {
            charge(budget, 1)?;
            output.push(match *step {
                Transition::Root(expression) => {
                    super::ActualValuePathStep::Root(source(expression)?)
                }
                Transition::Call(expression) => {
                    super::ActualValuePathStep::Call(source(expression)?)
                }
                Transition::Invoke(call, target) => {
                    super::ActualValuePathStep::Invoke(source(call)?, source(target)?)
                }
                Transition::Dispatch(request, handler, ordinal) => {
                    super::ActualValuePathStep::Dispatch(
                        source(request)?,
                        source(handler)?,
                        ordinal,
                    )
                }
                // Actual c is reconstructed from original entry paths before
                // any focused resource query or restored continuation replay.
                Transition::Focus | Transition::Restore(..) => return Err(Failure::Invalid),
            });
        }
        Ok((request, output))
    }

    pub(super) fn root_context(
        &self,
        code: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<usize, Failure> {
        charge(budget, 1)?;
        Ok(self
            .graph
            .positions
            .get(&code)
            .and_then(|expression| self.roots.get(expression))
            .copied()
            .unwrap_or(0))
    }

    pub(super) fn port(
        &mut self,
        code: usize,
        context: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<usize, Failure> {
        charge(budget, 1)?;
        let expression = *self.graph.positions.get(&code).ok_or(Failure::Invalid)?;
        self.slot(expression, context, budget)
    }

    pub(super) fn calls(
        &mut self,
        code: usize,
        context: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<CallSuccessors, Failure> {
        let port = self.port(code, context, budget)?;
        self.close(budget)?;
        let (expression, _) = self.slots[port].key;
        let Expr::Call { function, .. } = self.graph.expressions[expression] else {
            return Err(Failure::Invalid);
        };
        let function = self.slot(function, context, budget)?;
        let mut targets = Vec::new();
        let mut unknown = false;
        let mut returns = false;
        for atom in copy_slice(&self.slots[function].atoms, budget)? {
            match atom {
                Atom::Closure(target, _) => {
                    let context =
                        self.context(context, Transition::Invoke(expression, target), budget)?;
                    let target = *self.graph.targets.get(&target).ok_or(Failure::Invalid)?;
                    targets.try_reserve(1).map_err(|_| Failure::Resource)?;
                    targets.push((target, context));
                }
                Atom::Unknown => unknown = true,
                Atom::Constructor(_) => returns = true,
                _ => {}
            }
        }
        Ok(CallSuccessors {
            targets,
            unknown,
            returns,
        })
    }

    pub(super) fn dispatch(
        &mut self,
        request: usize,
        handler: usize,
        ordinal: usize,
        creation: usize,
        destination: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<usize, Failure> {
        let (request_expression, request_context) = self.slots[request].key;
        let expression = *self.graph.positions.get(&handler).ok_or(Failure::Invalid)?;
        let Expr::Handler { clauses, .. } = &self.graph.expressions[expression] else {
            return Err(Failure::Invalid);
        };
        let clause = clauses.get(ordinal).ok_or(Failure::Invalid)?;
        let context = self.context(
            request_context,
            Transition::Dispatch(request_expression, expression, ordinal),
            budget,
        )?;
        let input = self.slot(clause.input, context, budget)?;
        match self.graph.expressions[request_expression] {
            Expr::Request { operand, .. } => self.link(input, operand, request_context, budget)?,
            Expr::Call { .. } => self.atom(input, Atom::Unknown, budget)?,
            _ => return Err(Failure::Invalid),
        }
        for &(binder, initializer) in &clause.bindings {
            let binder = self.slot(binder, context, budget)?;
            self.link(binder, initializer, context, budget)?;
        }
        for capture in &clause.captures {
            let target = self.slot(*capture, context, budget)?;
            self.link(target, *capture, creation, budget)?;
        }
        let handler = self.slot(expression, destination, budget)?;
        self.link(handler, clause.body, context, budget)?;
        Ok(context)
    }

    pub(super) fn resume(
        &mut self,
        request: usize,
        code: usize,
        context: usize,
        handler: usize,
        creation: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        let result = self.port(code, context, budget)?;
        let (expression, _) = self.slots[result].key;
        let Expr::Resume { operand } = self.graph.expressions[expression] else {
            return Err(Failure::Invalid);
        };
        self.link(request, operand, context, budget)?;
        let handler = *self.graph.positions.get(&handler).ok_or(Failure::Invalid)?;
        let Expr::Handler { body, .. } = self.graph.expressions[handler] else {
            return Err(Failure::Invalid);
        };
        self.link(result, body, creation, budget)
    }

    pub(super) fn external_result(
        &mut self,
        request: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        let (expression, _) = self.slots[request].key;
        let scalar = matches!(
            self.graph.expressions[expression],
            Expr::Request { scalar: true, .. } | Expr::Call { scalar: true, .. }
        );
        self.atom(
            request,
            if scalar { Atom::Free } else { Atom::Unknown },
            budget,
        )
    }

    pub(super) fn check_payload(
        &mut self,
        request: usize,
        owner: usize,
        owner_context: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        // Validation only reads the converged graph. A missing port cannot be
        // materialized here after call-successor discovery has finished.
        if !self.pending.is_empty() || self.current.is_some() {
            return Err(Failure::Invalid);
        }
        let (expression, context) = self.slots[request].key;
        let owner = *self.graph.positions.get(&owner).ok_or(Failure::Invalid)?;
        let Expr::Resource { source, .. } = self.graph.expressions[owner] else {
            return Err(Failure::Invalid);
        };
        let mut operands = Vec::new();
        match &self.graph.expressions[expression] {
            Expr::Request { operand, .. } => {
                charge(budget, 1)?;
                operands.try_reserve(1).map_err(|_| Failure::Resource)?;
                operands.push(*operand);
            }
            Expr::Call {
                function,
                arguments,
                ..
            } => {
                charge(budget, arguments.len() + 1)?;
                operands
                    .try_reserve(arguments.len() + 1)
                    .map_err(|_| Failure::Resource)?;
                operands.push(*function);
                operands.extend(arguments);
            }
            _ => return Err(Failure::Invalid),
        }
        for operand in operands {
            charge(budget, 1)?;
            let operand = *self
                .indices
                .get(&(operand, context))
                .ok_or(Failure::Invalid)?;
            let dependencies = self.dependencies(operand, budget)?;
            charge(budget, dependencies.len())?;
            if dependencies.contains(&Atom::Resource(owner, owner_context)) {
                return Err(Failure::Escape {
                    source: self.graph.sources[expression],
                    acquisition: source,
                });
            }
        }
        Ok(())
    }

    pub(super) fn check_resources(&mut self, budget: &mut TypeWorkBudget) -> Result<(), Failure> {
        if !self.pending.is_empty() || self.current.is_some() {
            return Err(Failure::Invalid);
        }
        if let Some((expression, context)) = self.focus {
            let Expr::Resource { body, source, .. } = self.graph.expressions[expression] else {
                return Err(Failure::Invalid);
            };
            charge(budget, 1)?;
            let body_slot = *self.indices.get(&(body, context)).ok_or(Failure::Invalid)?;
            if self
                .dependencies(body_slot, budget)?
                .contains(&Atom::Resource(expression, context))
            {
                return Err(Failure::Escape {
                    source: self.graph.sources[body],
                    acquisition: source,
                });
            }
            return Ok(());
        }
        for slot in 0..self.slots.len() {
            charge(budget, 1)?;
            let (expression, context) = self.slots[slot].key;
            if let Expr::Resource { body, source, .. } = self.graph.expressions[expression]
                && let Some(&body_slot) = self.indices.get(&(body, context))
            {
                let dependencies = self.dependencies(body_slot, budget)?;
                charge(budget, dependencies.len())?;
                if dependencies.contains(&Atom::Resource(expression, context)) {
                    return Err(Failure::Escape {
                        source: self.graph.sources[body],
                        acquisition: source,
                    });
                }
            }
        }
        Ok(())
    }

    pub(super) fn resource_key(
        &self,
        code: usize,
        context: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<(usize, usize), Failure> {
        charge(budget, 1)?;
        let expression = *self.graph.positions.get(&code).ok_or(Failure::Invalid)?;
        if !matches!(self.graph.expressions[expression], Expr::Resource { .. }) {
            return Err(Failure::Invalid);
        }
        Ok((expression, context))
    }

    pub(super) fn resource_candidates(
        &mut self,
        budget: &mut TypeWorkBudget,
    ) -> Result<Vec<(usize, usize)>, Failure> {
        let mut candidates = Vec::new();
        for slot in 0..self.slots.len() {
            charge(budget, 1)?;
            let (expression, context) = self.slots[slot].key;
            if let Expr::Resource { body, .. } = self.graph.expressions[expression]
                && let Some(&body) = self.indices.get(&(body, context))
                && self
                    .dependencies(body, budget)?
                    .contains(&Atom::Resource(expression, context))
            {
                charge(budget, 1)?;
                candidates.try_reserve(1).map_err(|_| Failure::Resource)?;
                candidates.push((expression, context));
            }
        }
        Ok(candidates)
    }

    fn new(graph: &'a Graph, budget: &mut TypeWorkBudget) -> Result<Self, Failure> {
        // Each capture can replace only the evidence keys assigned to that
        // exact expression. Preserve their original order, including distinct
        // keys sharing a port, without scanning unrelated graph evidence.
        charge(budget, graph.evidence.len())?;
        let mut evidence_ports: HashMap<usize, Vec<usize>> = HashMap::new();
        evidence_ports
            .try_reserve(graph.evidence.len())
            .map_err(|_| Failure::Resource)?;
        charge(budget, graph.evidence.len())?;
        let mut evidence_keys: HashMap<_, Vec<usize>> = HashMap::new();
        evidence_keys
            .try_reserve(graph.evidence.len())
            .map_err(|_| Failure::Resource)?;
        for (position, (key, port)) in graph.evidence.iter().enumerate() {
            charge(budget, 2)?;
            let positions = evidence_ports.entry(*port).or_default();
            positions.try_reserve(1).map_err(|_| Failure::Resource)?;
            positions.push(position);
            let positions = evidence_keys.entry(*key).or_default();
            positions.try_reserve(1).map_err(|_| Failure::Resource)?;
            positions.push(position);
        }
        let contexts = ContextPaths::new(budget)?;
        Ok(Self {
            graph,
            evidence_ports,
            evidence_keys,
            binding_indices: HashMap::new(),
            capture_topology_indices: HashMap::new(),
            capture_topologies: Vec::new(),
            contexts,
            slots: Vec::new(),
            atom_pairs: HashSet::new(),
            dependencies: DependencyRelations::default(),
            callable_transfers: HashSet::new(),
            specialization_transfers: HashSet::new(),
            indices: HashMap::new(),
            roots: HashMap::new(),
            revision: 0,
            pending: VecDeque::new(),
            current: None,
            frozen_contexts: 0,
            focus: None,
            cuts: HashMap::new(),
            provider_closed_data: false,
        })
    }

    fn context(
        &mut self,
        parent: usize,
        call: Transition,
        budget: &mut TypeWorkBudget,
    ) -> Result<usize, Failure> {
        let (id, published) = self.contexts.intern(parent, call, budget)?;
        if published {
            self.revision += 1;
        }
        Ok(id)
    }

    fn slot(
        &mut self,
        expression: usize,
        context: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<usize, Failure> {
        let id = self.install_slot(expression, context, budget)?;
        if let Some(reader) = self.current {
            self.watch(id, reader, budget)?;
        }
        Ok(id)
    }

    // Construct exact coordinates and enqueue new slots without reading their atoms.
    // Observing slot(), typed Function/Evidence/Call installers, and queue-owned Alias/Merge links use this constructor.
    fn install_slot(
        &mut self,
        expression: usize,
        context: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<usize, Failure> {
        charge(budget, 1)?;
        let key = (expression, context);
        if let Some(&id) = self.indices.get(&key) {
            return Ok(id);
        }
        self.slots.try_reserve(1).map_err(|_| Failure::Resource)?;
        self.indices.try_reserve(1).map_err(|_| Failure::Resource)?;
        let id = self.slots.len();
        self.slots.push(Slot {
            key,
            atoms: Vec::new(),
            edges: Vec::new(),
            readers: Vec::new(),
            queued: false,
            terminal: context < self.frozen_contexts,
            preparation: SlotPreparation::Pending,
        });
        self.indices.insert(key, id);
        self.revision += 1;
        self.enqueue(id, budget)?;
        Ok(id)
    }

    fn enqueue(&mut self, slot: usize, budget: &mut TypeWorkBudget) -> Result<(), Failure> {
        charge(budget, 1)?;
        if !self.slots[slot].queued {
            self.pending.try_reserve(1).map_err(|_| Failure::Resource)?;
            self.pending.push_back(slot);
            self.slots[slot].queued = true;
        }
        Ok(())
    }

    fn watch(
        &mut self,
        source: usize,
        reader: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        let WatchPreparation::Vacant(pending) =
            self.dependencies.prepare_watch(source, reader, budget)?
        else {
            return Ok(());
        };
        // One compact relation entry and one ordered reader, before mutation.
        charge(budget, 2)?;
        let pending = pending.reserve()?;
        self.slots[source]
            .readers
            .try_reserve(1)
            .map_err(|_| Failure::Resource)?;
        pending.publish_watching();
        self.slots[source].readers.push(reader);
        Ok(())
    }

    fn atom(
        &mut self,
        slot: usize,
        atom: Atom,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        AtomStore {
            slots: &mut self.slots,
            atom_pairs: &mut self.atom_pairs,
            pending: &mut self.pending,
            revision: &mut self.revision,
        }
        .atom(slot, atom, budget)
    }

    fn edge(
        &mut self,
        target: usize,
        source: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        if self.slots[target].key.1 < self.frozen_contexts {
            return Err(Failure::Invalid);
        }
        let EdgePreparation::Install(installation) =
            self.dependencies.prepare_edge(target, source, budget)?
        else {
            return Ok(());
        };
        let (installation, new_reader) = match installation {
            LinkInstallation::Vacant(pending) => {
                // Exact pair, initial scalar cursor, ordered source and reader.
                charge(budget, 4)?;
                let pending = pending.reserve()?;
                (ReservedLinkInstallation::Vacant(pending), true)
            }
            LinkInstallation::Watching(pending) => {
                // Existing-entry mutation lookup/write and ordered source.
                // Its original reader position remains unchanged.
                charge(budget, 3)?;
                (ReservedLinkInstallation::Watching(pending), false)
            }
        };
        self.slots[target]
            .edges
            .try_reserve(1)
            .map_err(|_| Failure::Resource)?;
        if new_reader {
            self.slots[source]
                .readers
                .try_reserve(1)
                .map_err(|_| Failure::Resource)?;
        }
        charge(budget, 1)?;
        let enqueue = !self.slots[target].queued;
        if enqueue {
            self.pending.try_reserve(1).map_err(|_| Failure::Resource)?;
        }
        // All table/vector/queue storage is admitted. Neither a work nor
        // allocation refusal can publish a link without its ordered reader.
        installation.publish();
        self.slots[target].edges.push(source);
        self.revision += 1;
        if new_reader {
            self.slots[source].readers.push(target);
        }
        if enqueue {
            self.pending.push_back(target);
            self.slots[target].queued = true;
        }
        Ok(())
    }

    fn link(
        &mut self,
        target: usize,
        expression: usize,
        context: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        let source = self.slot(expression, context, budget)?;
        self.edge(target, source, budget)
    }

    pub(super) fn close(&mut self, budget: &mut TypeWorkBudget) -> Result<(), Failure> {
        while let Some(slot) = self.pending.pop_front() {
            charge(budget, 1)?;
            self.slots[slot].queued = false;
            self.current = Some(slot);
            let complete_setup = if self.slots[slot].terminal {
                false
            } else if matches!(
                self.graph.expressions[self.slots[slot].key.0],
                Expr::Alias(_)
                    | Expr::Merge(_)
                    | Expr::Function { .. }
                    | Expr::Tuple(_)
                    | Expr::Cleanup { .. }
                    | Expr::Bind { .. }
                    | Expr::Recursive { .. }
                    | Expr::Match { .. }
                    | Expr::Resource { .. }
            ) {
                // The queue visit already admits its bounded kind dispatch.
                // Pay this eligible classification and completion-field lookup.
                charge(budget, 2)?;
                if self.slots[slot].preparation == SlotPreparation::EdgesInstalled {
                    false
                } else {
                    QueuedEvaluation {
                        analysis: self,
                        slot,
                    }
                    .evaluate(budget)?
                }
            } else {
                QueuedEvaluation {
                    analysis: self,
                    slot,
                }
                .evaluate(budget)?;
                false
            };
            // Live ordered edges are processed on every visit, including after
            // setup completion. A later owner/Unknown is never a cached answer.
            // Evaluate has finished installing this visit's edges. atom() below
            // changes atoms and queued readers, never edges, so scalar indexing
            // preserves the original ordered snapshot without retaining a Vec.
            let edge_count = self.slots[slot].edges.len();
            for edge_index in 0..edge_count {
                charge(budget, 1)?;
                let source = self.slots[slot].edges[edge_index];
                let pair = (slot, source);
                let cursor = self
                    .dependencies
                    .pending_cursor(pair)?
                    .prepare(&self.slots[source].atoms)?;
                let delivered = cursor.delivered;
                let end = cursor.end;
                if delivered == end {
                    continue;
                }
                // The retained exact entry loan removes the second table lookup.
                // Prepay its scalar write, then advance only after every original
                // atom transfer succeeds; refusal retains the old cursor.
                charge(budget, 1)?;
                // A distinct source cannot change during atom(target). For a
                // self-edge each source atom already belongs to that same target,
                // so atom() only tests existing membership. Keep the original end
                // and finish the complete ordered suffix before committing it.
                let mut atoms = AtomStore {
                    slots: &mut self.slots,
                    atom_pairs: &mut self.atom_pairs,
                    pending: &mut self.pending,
                    revision: &mut self.revision,
                };
                for atom_index in delivered..end {
                    let atom = atoms.slots[source].atoms[atom_index];
                    atoms.atom(slot, atom, budget)?;
                }
                cursor.publish();
            }
            if complete_setup {
                // The existing Slot admission already reserves this scalar
                // field. Commit only after all original setup AND this slot's
                // current ordered propagation succeed. No fallible work follows
                // in this slot visit.
                charge(budget, 1)?;
                self.slots[slot].preparation = SlotPreparation::EdgesInstalled;
            }
            self.current = None;
        }
        Ok(())
    }

    #[cfg(test)]
    fn edge_pairs(&self) -> HashMap<(usize, usize), usize> {
        self.dependencies
            .entries
            .iter()
            .filter_map(|(&pair, &progress)| {
                (progress != DependencyProgress::WATCHING).then_some((pair, progress.0))
            })
            .collect()
    }

    #[cfg(test)]
    fn watched_pairs(&self) -> HashSet<(usize, usize)> {
        self.dependencies
            .entries
            .keys()
            .map(|&(reader, source)| (source, reader))
            .collect()
    }

    #[cfg(test)]
    fn evaluate(&mut self, slot: usize, budget: &mut TypeWorkBudget) -> Result<bool, Failure> {
        self.evaluate_with_alias_links::<ObservedAliasLinks>(slot, budget)
    }

    fn evaluate_with_alias_links<P: AliasLinkPolicy>(
        &mut self,
        slot: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<bool, Failure> {
        // This reports setup readiness only. The queue owns its completion bit
        // and commits it after propagation; direct evaluation always runs.
        let mut fixed_setup = true;
        let (expression, context) = self.slots[slot].key;
        let graph = self.graph;
        match &graph.expressions[expression] {
            Expr::Scalar => self.atom(slot, Atom::Free, budget)?,
            Expr::Slot => {}
            Expr::Unknown => self.atom(slot, Atom::Unknown, budget)?,
            Expr::Alias(value) => P::link(self, slot, *value, context, budget)?,
            Expr::Merge(values) => {
                self.atom(slot, Atom::Free, budget)?;
                for value in values {
                    P::link(self, slot, *value, context, budget)?;
                }
            }
            Expr::Function { captures, body, .. } => {
                FunctionCaptureInstallation {
                    analysis: self,
                    slot,
                    expression,
                    creation: context,
                    body: *body,
                    captures,
                }
                .install(budget)?;
            }
            Expr::Constructor(constructor) => {
                self.atom(slot, Atom::Constructor(*constructor), budget)?
            }
            Expr::Tuple(fields) => {
                let mut ready = true;
                for field in fields {
                    let field = self.slot(*field, context, budget)?;
                    ready &= !self.slots[field].atoms.is_empty();
                }
                if !ready {
                    return Ok(false);
                }
                self.atom(slot, Atom::Aggregate(expression, context), budget)?;
            }
            Expr::Call {
                function,
                arguments,
                scalar,
                type_application,
            } => {
                fixed_setup = false;
                let function = self.slot(*function, context, budget)?;
                charge(budget, arguments.len())?;
                let mut actual = Vec::new();
                actual
                    .try_reserve(arguments.len())
                    .map_err(|_| Failure::Resource)?;
                let mut ready = true;
                for argument in arguments {
                    let argument = self.slot(*argument, context, budget)?;
                    ready &= !self.slots[argument].atoms.is_empty();
                    actual.push(argument);
                }
                if !ready {
                    return Ok(false);
                }
                // Atom storage is append-only; preserve the original prefix while routing.
                let atom_count = self.slots[function].atoms.len();
                charge(budget, atom_count)?;
                for atom_index in 0..atom_count {
                    let atom = self.slots[function].atoms[atom_index];
                    match atom {
                        Atom::Closure(target, creation) => {
                            let Expr::Function {
                                parameters,
                                body,
                                captures,
                            } = &self.graph.expressions[target]
                            else {
                                return Err(Failure::Invalid);
                            };
                            if parameters.len() != actual.len() {
                                return Err(Failure::Invalid);
                            }
                            // Readiness watches above are refreshed on every
                            // evaluation. Once this exact transfer succeeds,
                            // its existing edges carry later argument/capture atoms.
                            let transfer = (self.current, slot, target, creation);
                            charge(budget, 1)?;
                            if self.callable_transfers.contains(&transfer) {
                                continue;
                            }
                            charge(budget, 1)?;
                            self.callable_transfers
                                .try_reserve(1)
                                .map_err(|_| Failure::Resource)?;
                            CallTransferInstallation {
                                analysis: self,
                                slot,
                                expression,
                                context,
                                target,
                                creation,
                                parameters,
                                captures,
                                actual: &actual,
                                body: *body,
                                transfer,
                            }
                            .install(budget)?;
                        }
                        Atom::Constructor(_) => self.atom(
                            slot,
                            if *type_application {
                                atom
                            } else {
                                Atom::Aggregate(expression, context)
                            },
                            budget,
                        )?,
                        Atom::Unknown => {
                            if !scalar {
                                self.atom(slot, Atom::Unknown, budget)?;
                                for &argument in &actual {
                                    for dependency in self.dependencies(argument, budget)? {
                                        self.atom(slot, dependency, budget)?;
                                    }
                                }
                                for dependency in self.dependencies(function, budget)? {
                                    self.atom(slot, dependency, budget)?;
                                }
                            } else {
                                self.atom(slot, Atom::Free, budget)?;
                            }
                        }
                        _ => {}
                    }
                }
            }
            Expr::Project {
                value,
                field,
                constructor,
            } => {
                fixed_setup = false;
                let value = self.slot(*value, context, budget)?;
                let atom_count = self.slots[value].atoms.len();
                charge(budget, atom_count)?;
                for atom_index in 0..atom_count {
                    let atom = self.slots[value].atoms[atom_index];
                    match atom {
                        Atom::Aggregate(target, creation) => {
                            match &self.graph.expressions[target] {
                                Expr::Tuple(fields) if constructor.is_none() => {
                                    if let Some(value) = fields.get(*field) {
                                        P::link(self, slot, *value, creation, budget)?;
                                    }
                                }
                                Expr::Call { arguments, .. }
                                    if constructor.is_some() && *field == 0 =>
                                {
                                    if let Some(value) = arguments.first() {
                                        P::link(self, slot, *value, creation, budget)?;
                                    }
                                }
                                Expr::Resource {
                                    body,
                                    success: Some(success),
                                    ..
                                } if *constructor == Some(*success) && *field == 0 => {
                                    P::link(self, slot, *body, creation, budget)?;
                                }
                                Expr::Resource {
                                    failure: Some(failure),
                                    ..
                                } if *constructor == Some(*failure) && *field == 0 => {
                                    self.atom(slot, Atom::Free, budget)?;
                                }
                                _ => {}
                            }
                        }
                        Atom::Free if self.provider_closed_data => {
                            self.atom(slot, Atom::Free, budget)?;
                        }
                        Atom::Unknown => {
                            self.atom(slot, Atom::Unknown, budget)?;
                            for dependency in self.dependencies(value, budget)? {
                                self.atom(slot, dependency, budget)?;
                            }
                        }
                        _ => {}
                    }
                }
            }
            Expr::Cleanup { body, action } => {
                let body = self.slot(*body, context, budget)?;
                if self.slots[body].atoms.is_empty() {
                    return Ok(false);
                }
                let action = self.slot(*action, context, budget)?;
                if self.slots[action].atoms.is_empty() {
                    return Ok(false);
                }
                self.edge(slot, body, budget)?;
            }
            Expr::Bind {
                binder,
                initializer,
                body,
            } => {
                let binder = self.slot(*binder, context, budget)?;
                self.link(binder, *initializer, context, budget)?;
                if self.slots[binder].atoms.is_empty() {
                    return Ok(false);
                }
                P::link(self, slot, *body, context, budget)?;
            }
            Expr::Recursive { bindings, body } => {
                let mut ready = true;
                for &(binder, initializer) in bindings {
                    let binder = self.slot(binder, context, budget)?;
                    let initializer = self.slot(initializer, context, budget)?;
                    self.edge(binder, initializer, budget)?;
                    ready &= !self.slots[initializer].atoms.is_empty();
                }
                if !ready {
                    return Ok(false);
                }
                P::link(self, slot, *body, context, budget)?;
            }
            Expr::Match { scrutinee, arms } => {
                let scrutinee = self.slot(*scrutinee, context, budget)?;
                if self.slots[scrutinee].atoms.is_empty() {
                    return Ok(false);
                }
                for (bindings, body) in arms {
                    for &(binder, initializer) in bindings {
                        let binder = self.slot(binder, context, budget)?;
                        self.link(binder, initializer, context, budget)?;
                    }
                    P::link(self, slot, *body, context, budget)?;
                }
            }
            Expr::Resource {
                success,
                handle,
                identity,
                initializer,
                body,
                ..
            } => {
                let initializer = self.slot(*initializer, context, budget)?;
                if self.slots[initializer].atoms.is_empty() {
                    return Ok(false);
                }
                let handle = self.slot(*handle, context, budget)?;
                let identity = self.slot(*identity, context, budget)?;
                self.atom(handle, Atom::Resource(expression, context), budget)?;
                self.atom(identity, Atom::Resource(expression, context), budget)?;
                if success.is_some() {
                    // Allocation can fail independently of body completion.
                    // Successful values retain the ordinary constructor payload.
                    self.slot(*body, context, budget)?;
                    self.atom(slot, Atom::Aggregate(expression, context), budget)?;
                } else {
                    P::link(self, slot, *body, context, budget)?;
                }
            }
            Expr::Request { operand, scalar } => {
                self.slot(*operand, context, budget)?;
                let _ = scalar;
            }
            Expr::Resume { operand } => {
                self.slot(*operand, context, budget)?;
            }
            Expr::Handler { body, .. } => P::link(self, slot, *body, context, budget)?,
            // ASH_INPUT169_BEGIN_EVALUATE
            Expr::Evidence { value, bindings } => {
                fixed_setup = false;
                let InstalledEvidenceInputs { mut visit, value } = EvidenceInputVisit {
                    analysis: self,
                    slot,
                    evidence: expression,
                    arguments_context: context,
                    value: *value,
                    bindings,
                }
                .install_inputs(budget)?;
                let atom_count = visit.analysis.slots[value].atoms.len();
                for atom_index in 0..atom_count {
                    let atom = visit.analysis.slots[value].atoms[atom_index];
                    visit = visit.route_atom(atom, budget)?;
                }
            } // ASH_INPUT169_END_EVALUATE
        }
        Ok(fixed_setup)
    }

    fn build_binding_index(
        &self,
        evidence: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<
        HashMap<(crate::interface::RequirementId, crate::interface::MethodId), Vec<usize>>,
        Failure,
    > {
        charge(budget, 1)?;
        let Some(Expr::Evidence { bindings, .. }) = self.graph.expressions.get(evidence) else {
            return Err(Failure::Invalid);
        };
        let mut positions: HashMap<_, Vec<usize>> = HashMap::new();
        charge(budget, bindings.len())?;
        positions
            .try_reserve(bindings.len())
            .map_err(|_| Failure::Resource)?;
        for (position, (requirement, method, _)) in bindings.iter().enumerate() {
            charge(budget, 1)?;
            let key = (*requirement, *method);
            let ordered = match positions.entry(key) {
                std::collections::hash_map::Entry::Occupied(entry) => entry.into_mut(),
                std::collections::hash_map::Entry::Vacant(entry) => {
                    charge(budget, 1)?;
                    entry.insert(Vec::new())
                }
            };
            charge(budget, 1)?;
            ordered.try_reserve(1).map_err(|_| Failure::Resource)?;
            ordered.push(position);
        }
        Ok(positions)
    }

    #[cfg(test)]
    fn prepare_binding_index(
        &mut self,
        evidence: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        charge(budget, 1)?;
        if self.binding_indices.contains_key(&evidence) {
            return Ok(());
        }
        let positions = self.build_binding_index(evidence, budget)?;
        charge(budget, 1)?;
        self.binding_indices
            .try_reserve(1)
            .map_err(|_| Failure::Resource)?;
        self.binding_indices.insert(evidence, positions);
        Ok(())
    }

    fn prepare_capture_topology(
        &mut self,
        function: usize,
        evidence: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<usize, Failure> {
        let key = (function, evidence);
        charge(budget, 1)?;
        if let Some(&plan) = self.capture_topology_indices.get(&key) {
            return Ok(plan);
        }
        // A key cannot name caller-supplied captures. Derive the complete vector
        // from this exact original function and authenticate both owner shapes.
        charge(budget, 2)?;
        let Some(Expr::Function { captures, .. }) = self.graph.expressions.get(function) else {
            return Err(Failure::Invalid);
        };
        let Some(Expr::Evidence { bindings, .. }) = self.graph.expressions.get(evidence) else {
            return Err(Failure::Invalid);
        };
        charge(budget, 1)?;
        let new_index = if self.binding_indices.contains_key(&evidence) {
            None
        } else {
            Some(self.build_binding_index(evidence, budget)?)
        };
        let binding_index = new_index
            .as_ref()
            .or_else(|| self.binding_indices.get(&evidence))
            .ok_or(Failure::Invalid)?;
        let mut topology = CaptureTopology {
            visits: Vec::new(),
            bindings: Vec::new(),
            dictionary: PreparedDictionaryRoutes::Complete,
        };
        // Constructor-local membership proves which original projection routes
        // the full successful transfer will install; it never becomes a cache.
        let mut bound_ports = HashSet::new();
        let mut pending = copy_slice(captures, budget)?;
        let mut visited = HashSet::new();
        while let Some(capture) = pending.pop() {
            charge(budget, 1)?;
            if visited.contains(&capture) {
                continue;
            }
            charge(budget, 1)?;
            visited.try_reserve(1).map_err(|_| Failure::Resource)?;
            visited.insert(capture);
            let original = self
                .graph
                .expressions
                .get(capture)
                .ok_or(Failure::Invalid)?;
            let binding_start = topology.bindings.len();
            charge(budget, 1)?;
            let matching = self.evidence_ports.get(&capture).map_or(0, Vec::len);
            for position in 0..matching {
                charge(budget, 1)?;
                let key = self.graph.evidence[self.evidence_ports[&capture][position]].0;
                if let Some(positions) = binding_index.get(&key) {
                    for &position in positions {
                        // Retain each ordered original binding position, including
                        // duplicates and distinct keys sharing the same port.
                        charge(budget, 2)?; // Binding visit plus retained route.
                        let argument = bindings.get(position).ok_or(Failure::Invalid)?.2;
                        self.graph
                            .expressions
                            .get(argument)
                            .ok_or(Failure::Invalid)?;
                        topology
                            .bindings
                            .try_reserve(1)
                            .map_err(|_| Failure::Resource)?;
                        topology.bindings.push(position);
                    }
                }
            }
            let replaced = binding_start != topology.bindings.len();
            if replaced {
                // This complete ordered port binding set is immutable structure,
                // not transfer completion. Reserve before plan publication.
                charge(budget, 2)?;
                bound_ports.try_reserve(1).map_err(|_| Failure::Resource)?;
                bound_ports.insert(capture);
            }
            let mut lexical = false;
            if !replaced {
                // Preserve the old stack push order, hence LIFO first-visit order.
                match original {
                    Expr::Alias(value) => {
                        charge(budget, 1)?;
                        pending.try_reserve(1).map_err(|_| Failure::Resource)?;
                        pending.push(*value);
                    }
                    Expr::Merge(values) => {
                        charge(budget, values.len())?;
                        pending
                            .try_reserve(values.len())
                            .map_err(|_| Failure::Resource)?;
                        pending.extend(values);
                    }
                    Expr::Call {
                        function,
                        arguments,
                        type_application: true,
                        ..
                    } => {
                        charge(budget, arguments.len() + 1)?;
                        pending
                            .try_reserve(arguments.len() + 1)
                            .map_err(|_| Failure::Resource)?;
                        pending.push(*function);
                        pending.extend(arguments);
                    }
                    Expr::Evidence { value, bindings } => {
                        charge(budget, bindings.len() + 1)?;
                        pending
                            .try_reserve(bindings.len() + 1)
                            .map_err(|_| Failure::Resource)?;
                        pending.push(*value);
                        pending.extend(bindings.iter().map(|(_, _, argument)| argument));
                    }
                    _ => lexical = true,
                }
            }
            charge(budget, 1)?;
            topology
                .visits
                .try_reserve(1)
                .map_err(|_| Failure::Resource)?;
            topology.visits.push(CaptureVisit {
                expression: capture,
                binding_start,
                binding_end: topology.bindings.len(),
                lexical,
            });
        }
        // Classify the entire original dictionary once, in binding order then
        // original Graph evidence order. Bound-port completeness came from all
        // original keys/positions above, not merely from a captured port name.
        let mut residual = Vec::new();
        for (binding, (requirement, method, _)) in bindings.iter().enumerate() {
            charge(budget, 1)?;
            let key = (*requirement, *method);
            let matching = self.evidence_keys.get(&key).map_or(0, Vec::len);
            for position in 0..matching {
                charge(budget, 2)?; // Original evidence read and membership.
                let evidence = self.evidence_keys[&key][position];
                let port = self.graph.evidence[evidence].1;
                if !bound_ports.contains(&port) {
                    charge(budget, 1)?; // Retained ordered residual instruction.
                    residual.try_reserve(1).map_err(|_| Failure::Resource)?;
                    residual.push(DictionaryObligation { binding, evidence });
                }
            }
        }
        // Pay the retained phase before any map/vector publication. Empty
        // capture topology covers nothing; required routes stay residual.
        charge(budget, 1)?;
        topology.dictionary = if residual.is_empty() {
            PreparedDictionaryRoutes::Complete
        } else {
            PreparedDictionaryRoutes::Pending(residual)
        };
        // Reserve and admit every retained entry before publishing either map.
        // Refusal leaves no partial topology or binding index, and no dynamic
        // slots, edges, watches, atoms, revision or pending work have changed.
        if new_index.is_some() {
            charge(budget, 1)?;
            self.binding_indices
                .try_reserve(1)
                .map_err(|_| Failure::Resource)?;
        }
        charge(budget, 2)?;
        self.capture_topologies
            .try_reserve(1)
            .map_err(|_| Failure::Resource)?;
        self.capture_topology_indices
            .try_reserve(1)
            .map_err(|_| Failure::Resource)?;
        let plan = self.capture_topologies.len();
        if let Some(index) = new_index {
            self.binding_indices.insert(evidence, index);
        }
        self.capture_topologies.push(topology);
        self.capture_topology_indices.insert(key, plan);
        Ok(plan)
    }

    fn specialize_captures(
        &mut self,
        function: usize,
        creation: usize,
        specialized: usize,
        evidence: usize,
        arguments_context: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<usize, Failure> {
        CaptureTransferInstallation {
            analysis: self,
            policy: ObservedCaptureSlots,
            function,
            creation,
            specialized,
            evidence,
            arguments_context,
        }
        .install(budget)
    }

    fn dependencies(
        &mut self,
        root: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<Vec<Atom>, Failure> {
        let mut pending = copy_slice(&[root], budget)?;
        let mut visited = HashSet::new();
        let mut resources = Vec::new();
        while let Some(slot) = pending.pop() {
            charge(budget, 1)?;
            visited.try_reserve(1).map_err(|_| Failure::Resource)?;
            if !visited.insert(slot) {
                continue;
            }
            if let Some(reader) = self.current {
                self.watch(slot, reader, budget)?;
            }
            // This walk only reads atoms; watches above change reader lists, not values.
            for &atom in &self.slots[slot].atoms {
                charge(budget, 1)?;
                let fields = match atom {
                    Atom::Resource(..) => {
                        charge(budget, resources.len())?;
                        if !resources.contains(&atom) {
                            resources.try_reserve(1).map_err(|_| Failure::Resource)?;
                            resources.push(atom);
                        }
                        None
                    }
                    Atom::Closure(target, context) => {
                        let Expr::Function { captures, .. } = &self.graph.expressions[target]
                        else {
                            return Err(Failure::Invalid);
                        };
                        Some((captures.as_slice(), context))
                    }
                    Atom::Aggregate(target, context) => match &self.graph.expressions[target] {
                        Expr::Tuple(fields) => Some((fields.as_slice(), context)),
                        Expr::Call { arguments, .. } => Some((arguments.as_slice(), context)),
                        Expr::Resource {
                            body,
                            success: Some(_),
                            ..
                        } => Some((std::slice::from_ref(body), context)),
                        _ => return Err(Failure::Invalid),
                    },
                    _ => None,
                };
                if let Some((fields, context)) = fields {
                    charge(budget, fields.len())?;
                    pending
                        .try_reserve(fields.len())
                        .map_err(|_| Failure::Resource)?;
                    for field in fields {
                        charge(budget, 1)?;
                        if let Some(slot) = self.indices.get(&(*field, context)) {
                            pending.push(*slot);
                        }
                    }
                }
            }
        }
        Ok(resources)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn graph(expressions: Vec<Expr>) -> Graph {
        let source = crate::source::SourceFile::new("value-cut.ash", "x").unwrap();
        let span = source
            .span(crate::source::ByteRange::new(0, 1).unwrap())
            .unwrap();
        Graph {
            sources: vec![span; expressions.len()],
            expressions,
            globals: Vec::new(),
            provider: Vec::new(),
            exports: Vec::new(),
            positions: HashMap::new(),
            targets: HashMap::new(),
            metadata: HashMap::new(),
            evidence: Vec::new(),
            evidence_index: Vec::new(),
        }
    }

    #[test]
    fn productive_cursor_loans_keep_partial_refusal_self_edges_and_late_original_owners() {
        let original = graph(vec![Expr::Slot, Expr::Slot, Expr::Slot]);
        let setup = || {
            let mut work = TypeWorkBudget::unbounded();
            let mut analysis = Analysis::new(&original, &mut work).unwrap();
            for expression in 0..3 {
                analysis.slot(expression, 0, &mut work).unwrap();
            }
            for atom in [Atom::Resource(9, 0), Atom::Resource(10, 0), Atom::Unknown] {
                analysis.atom(1, atom, &mut work).unwrap();
            }
            analysis.atom(2, Atom::Resource(11, 0), &mut work).unwrap();
            for source in [1, 2, 0] {
                analysis.edge(0, source, &mut work).unwrap();
            }
            analysis
        };
        let expected = vec![
            Atom::Resource(9, 0),
            Atom::Resource(10, 0),
            Atom::Unknown,
            Atom::Resource(11, 0),
        ];
        let mut exact = TypeWorkBudget::unbounded();
        let mut complete = setup();
        complete.close(&mut exact).unwrap();
        assert_eq!(complete.slots[0].atoms, expected);
        assert_eq!(complete.edge_pairs()[&(0, 1)], 3);
        assert_eq!(complete.edge_pairs()[&(0, 2)], 1);
        assert_eq!(complete.edge_pairs()[&(0, 0)], 4);
        for cut in 0..exact.used() {
            let mut refused = setup();
            assert!(matches!(
                refused.close(&mut TypeWorkBudget::with_limit(cut)),
                Err(Failure::Resource)
            ));
            let cursor = refused.edge_pairs()[&(0, 1)];
            assert!(cursor == 0 || cursor == 3, "no partial suffix is complete");
            if cursor == 3 {
                assert!(
                    expected[..3]
                        .iter()
                        .all(|atom| refused.slots[0].atoms.contains(atom))
                );
            }
            assert!(refused.edge_pairs()[&(0, 2)] <= 1);
            assert!(refused.edge_pairs()[&(0, 0)] <= refused.slots[0].atoms.len());
            // A refused analysis is discarded; an exact retry starts fresh.
            // The partial cursor assertions above still cover every failure cut.
            let mut retry = setup();
            retry
                .close(&mut TypeWorkBudget::with_limit(exact.used()))
                .unwrap();
            assert_eq!(retry.slots[0].atoms, expected);
            assert_eq!(retry.edge_pairs(), complete.edge_pairs());
        }
        let later = Atom::Resource(9, 1);
        complete
            .atom(1, later, &mut TypeWorkBudget::unbounded())
            .unwrap();
        complete.close(&mut TypeWorkBudget::unbounded()).unwrap();
        assert_eq!(complete.slots[0].atoms, [expected, vec![later]].concat());
        assert_eq!(complete.edge_pairs()[&(0, 1)], 4);
        assert_eq!(complete.edge_pairs()[&(0, 0)], 5);
    }

    fn immutable_setup_graph() -> Graph {
        let mut original = graph(vec![
            Expr::Slot,
            Expr::Slot,
            Expr::Scalar,
            Expr::Slot,
            Expr::Function {
                parameters: Vec::new(),
                body: 2,
                captures: vec![0, 1],
            },
            Expr::Alias(0),
            Expr::Merge(vec![0, 1]),
            Expr::Tuple(vec![4, 5, 6]),
            Expr::Slot,
        ]);
        original.expressions[3] = Expr::Resource {
            success: None,
            failure: None,
            handle: 0,
            identity: 1,
            initializer: 2,
            body: 2,
            source: original.sources[3],
        };
        original.positions.extend([(20, 3), (21, 2)]);
        original
    }

    #[test]
    fn immutable_setup_keeps_late_real_owners_closure_dependencies_and_direct_readers() {
        let graph = immutable_setup_graph();
        let mut work = TypeWorkBudget::unbounded();
        let mut analysis = Analysis::new(&graph, &mut work).unwrap();
        let mut outputs = Vec::new();
        for expression in [4, 5, 6] {
            let slot = analysis.slot(expression, 0, &mut work).unwrap();
            assert!(!analysis.slots[slot].preparation.is_edges_installed());
            outputs.push(slot);
        }
        analysis.close(&mut work).unwrap();
        for &slot in &outputs {
            assert!(analysis.slots[slot].preparation.is_edges_installed());
            assert!(!analysis.slots[slot].terminal);
        }
        assert_eq!(
            analysis.slots[outputs[0]].atoms,
            vec![Atom::Closure(4, 0)],
            "Function always yields its Closure before capture readiness"
        );
        assert!(analysis.slots[analysis.indices[&(0, 0)]].atoms.is_empty());
        assert!(analysis.slots[analysis.indices[&(1, 0)]].atoms.is_empty());
        assert!(
            analysis
                .dependencies(outputs[0], &mut work)
                .unwrap()
                .is_empty()
        );
        let edges = analysis.edge_pairs();
        let atom_revision = analysis.revision;
        // A new real Resource fills the original handle and identity ports only
        // after the eligible slots' complete first queue visits.
        analysis.slot(3, 0, &mut work).unwrap();
        analysis.close(&mut work).unwrap();
        let owner = Atom::Resource(3, 0);
        assert!(analysis.revision > atom_revision);
        for &slot in &outputs {
            assert_eq!(analysis.dependencies(slot, &mut work).unwrap(), vec![owner]);
            assert!(analysis.slots[slot].preparation.is_edges_installed());
        }
        assert_eq!(analysis.slots[outputs[0]].atoms, vec![Atom::Closure(4, 0)]);
        assert_eq!(analysis.slots[outputs[1]].atoms, vec![owner]);
        assert_eq!(analysis.slots[outputs[2]].atoms, vec![Atom::Free, owner]);
        for pair in edges.keys() {
            assert!(analysis.edge_pairs().contains_key(pair));
        }
        let identity = analysis.indices[&(1, 0)];
        analysis.atom(identity, Atom::Unknown, &mut work).unwrap();
        analysis.close(&mut work).unwrap();
        assert!(analysis.slots[outputs[2]].atoms.contains(&Atom::Unknown));
        assert_eq!(
            analysis.dependencies(outputs[0], &mut work).unwrap(),
            vec![owner]
        );

        let reader = analysis.slot(8, 0, &mut work).unwrap();
        analysis.current = Some(reader);
        for &slot in &outputs {
            analysis.evaluate(slot, &mut work).unwrap();
        }
        for expression in [0, 1] {
            let source = analysis.indices[&(expression, 0)];
            assert!(analysis.slots[source].readers.contains(&reader));
        }
        // Direct evaluation with the same optional reader coordinate also
        // remains ordinary; a queue-owned bit cannot authorize direct reuse.
        analysis.current = Some(outputs[1]);
        // The original Alias path paid 3: slot hit, watch hit, linked hit.
        // A Linked entry now also pays its distinct phase read.
        let linked_phase_read_work = 1;
        let same_reader_work = 3 + linked_phase_read_work;
        let before_relations = analysis.dependencies.entries.clone();
        let source = analysis.indices[&(0, 0)];
        let before_readers = analysis.slots[source].readers.clone();
        let before_revision = analysis.revision;
        let mut short_reader = TypeWorkBudget::with_limit(same_reader_work - 1);
        assert!(matches!(
            analysis.evaluate(outputs[1], &mut short_reader),
            Err(Failure::Resource)
        ));
        assert_eq!(short_reader.used(), same_reader_work - 1);
        assert_eq!(analysis.dependencies.entries, before_relations);
        assert_eq!(analysis.slots[source].readers, before_readers);
        assert_eq!(analysis.revision, before_revision);
        let mut same_reader = TypeWorkBudget::with_limit(same_reader_work);
        analysis.evaluate(outputs[1], &mut same_reader).unwrap();
        assert_eq!(same_reader.used(), same_reader_work);
        analysis.current = None;
        // Function remains 3; Alias and Merge add one and two Linked phase reads.
        let no_reader_work = 10 + 3 * linked_phase_read_work;
        let mut no_reader = TypeWorkBudget::with_limit(no_reader_work);
        for &slot in &outputs {
            analysis.evaluate(slot, &mut no_reader).unwrap();
        }
        assert_eq!(
            no_reader.used(),
            no_reader_work,
            "None still runs original Function, Alias and Merge setup without flag lookup"
        );
        let context = analysis
            .context(0, Transition::Root(99), &mut work)
            .unwrap();
        let fresh = analysis.slot(4, context, &mut work).unwrap();
        assert!(!analysis.slots[fresh].preparation.is_edges_installed());
        analysis.close(&mut work).unwrap();
        assert_eq!(analysis.slots[fresh].atoms, vec![Atom::Closure(4, context)]);
        assert!(analysis.slots[fresh].preparation.is_edges_installed());
    }

    #[test]
    fn function_capture_installation_keeps_live_edges_without_structural_reader_watches() {
        for captures in [vec![0], vec![0, 2]] {
            let mut graph = graph(vec![
                Expr::Slot,
                Expr::Scalar,
                Expr::Function {
                    parameters: Vec::new(),
                    body: 1,
                    captures,
                },
                Expr::Slot,
                Expr::Slot,
                Expr::Slot,
                Expr::Slot,
            ]);
            graph.expressions[5] = Expr::Resource {
                success: None,
                failure: None,
                handle: 0,
                identity: 3,
                initializer: 1,
                body: 1,
                source: graph.sources[5],
            };
            graph.globals.push((4, 2));
            let mut work = TypeWorkBudget::unbounded();
            let mut analysis = graph.start(&mut work).unwrap();
            let function = analysis.indices[&(2, 0)];
            let source = analysis.indices[&(0, 0)];
            let root = analysis.roots[&1];
            let routed = analysis.indices[&(0, root)];
            assert!(!analysis.watched_pairs().contains(&(source, function)));
            assert!(!analysis.watched_pairs().contains(&(routed, function)));
            assert!(analysis.edge_pairs().contains_key(&(routed, source)));
            assert!(analysis.watched_pairs().contains(&(source, routed)));
            assert_eq!(analysis.slots[function].atoms, vec![Atom::Closure(2, 0)]);

            // A genuine live dependency reader still subscribes to every capture.
            let reader = analysis.slot(3, 0, &mut work).unwrap();
            analysis.close(&mut work).unwrap();
            analysis.current = Some(reader);
            assert!(
                analysis
                    .dependencies(function, &mut work)
                    .unwrap()
                    .is_empty()
            );
            assert!(analysis.watched_pairs().contains(&(source, reader)));
            analysis.current = None;
            let owner = Atom::Resource(5, 0);
            analysis.atom(source, owner, &mut work).unwrap();
            assert!(analysis.slots[routed].queued);
            assert!(analysis.slots[reader].queued);
            assert!(!analysis.slots[function].queued);
            analysis.close(&mut work).unwrap();
            assert!(analysis.slots[routed].atoms.contains(&owner));
            assert_eq!(
                analysis.dependencies(function, &mut work).unwrap(),
                vec![owner]
            );
            assert_eq!(analysis.slots[function].atoms, vec![Atom::Closure(2, 0)]);

            // Incoming data edges, including self-capture cycles, remain live.
            let incoming = analysis.slot(6, 0, &mut work).unwrap();
            analysis.edge(function, incoming, &mut work).unwrap();
            analysis.close(&mut work).unwrap();
            analysis.atom(incoming, Atom::Unknown, &mut work).unwrap();
            assert!(analysis.slots[function].queued);
            analysis.close(&mut work).unwrap();
            assert_eq!(
                analysis.slots[function].atoms,
                vec![Atom::Closure(2, 0), Atom::Unknown]
            );
            assert_eq!(analysis.edge_pairs()[&(function, incoming)], 1);
            if matches!(&graph.expressions[2], Expr::Function { captures, .. } if captures.contains(&2))
            {
                // The self-capture root has its ordinary incoming edge and suffix.
                let root_function = analysis.indices[&(2, root)];
                assert!(analysis.slots[root_function].atoms.contains(&Atom::Unknown));
                assert_eq!(analysis.edge_pairs()[&(root_function, function)], 2);
            }
        }
    }

    #[test]
    fn queued_alias_merge_links_keep_edge_watches_late_identity_and_direct_readers() {
        let mut graph = graph(vec![
            Expr::Slot,
            Expr::Alias(0),
            Expr::Merge(vec![0, 1, 2]),
            Expr::Tuple(vec![1]),
            Expr::Scalar,
        ]);
        for _ in 0..2 {
            graph.expressions.push(Expr::Resource {
                success: None,
                failure: None,
                handle: 0,
                identity: 1,
                initializer: 4,
                body: 2,
                source: graph.sources[0],
            });
            graph.sources.push(graph.sources[0]);
        }
        fn setup(graph: &Graph) -> Analysis<'_> {
            let mut work = TypeWorkBudget::unbounded();
            let mut analysis = Analysis::new(graph, &mut work).unwrap();
            for expression in 0..4 {
                analysis.slot(expression, 0, &mut work).unwrap();
            }
            analysis
        }
        let mut analysis = setup(&graph);
        let mut work = TypeWorkBudget::unbounded();
        analysis.close(&mut work).unwrap();
        let exact = work.used();
        let [source, alias, merge, reader] = [0, 1, 2, 3];
        assert_eq!(analysis.slots[source].readers, vec![alias, merge]);
        assert!(analysis.edge_pairs().contains_key(&(merge, merge)));
        for cut in 0..exact {
            let mut refused = setup(&graph);
            let mut short = TypeWorkBudget::with_limit(cut);
            assert!(matches!(refused.close(&mut short), Err(Failure::Resource)));
            for (target, input) in [
                (alias, source),
                (merge, source),
                (merge, alias),
                (merge, merge),
            ] {
                assert_eq!(
                    refused.watched_pairs().contains(&(input, target)),
                    refused.edge_pairs().contains_key(&(target, input)),
                    "a queued structural link publishes its edge-owned watch atomically"
                );
            }
            let mut retry = setup(&graph);
            retry.close(&mut TypeWorkBudget::with_limit(exact)).unwrap();
            assert_eq!(retry.edge_pairs(), analysis.edge_pairs());
            assert_eq!(retry.watched_pairs(), analysis.watched_pairs());
        }

        // Independent direct evaluation still observes for its actual reader.
        analysis.current = Some(reader);
        analysis.evaluate(alias, &mut work).unwrap();
        assert!(analysis.watched_pairs().contains(&(source, reader)));
        analysis.current = None;
        for expression in [5, 6] {
            let owner = Atom::Resource(expression, 0);
            analysis.atom(source, owner, &mut work).unwrap();
            assert!(analysis.slots[alias].queued);
            assert!(analysis.slots[merge].queued);
            assert!(analysis.slots[reader].queued);
            analysis.close(&mut work).unwrap();
            assert!(analysis.slots[alias].atoms.contains(&owner));
            assert!(analysis.slots[merge].atoms.contains(&owner));
            assert!(
                analysis
                    .dependencies(reader, &mut work)
                    .unwrap()
                    .contains(&owner)
            );
            assert_eq!(
                analysis.edge_pairs()[&(alias, source)],
                analysis.slots[source].atoms.len()
            );
            assert_eq!(
                analysis.edge_pairs()[&(merge, source)],
                analysis.slots[source].atoms.len()
            );
        }
        assert_eq!(
            analysis.dependencies(reader, &mut work).unwrap(),
            vec![Atom::Resource(5, 0), Atom::Resource(6, 0)]
        );
    }

    #[test]
    fn immutable_setup_roots_focus_and_restore_keep_separate_frozen_authority() {
        let mut graph = immutable_setup_graph();
        graph.globals.push((8, 4));
        let mut work = TypeWorkBudget::unbounded();
        let mut normal = graph.start(&mut work).unwrap();
        let function = normal.indices[&(4, 0)];
        assert!(normal.slots[function].preparation.is_edges_installed());
        let root = normal.root_context(21, &mut work).unwrap();
        assert_ne!(root, 0);
        normal.slot(3, 0, &mut work).unwrap();
        normal.close(&mut work).unwrap();
        for capture in [0, 1] {
            let source = normal.indices[&(capture, 0)];
            let routed = normal.indices[&(capture, root)];
            assert!(normal.edge_pairs().contains_key(&(routed, source)));
            assert!(normal.slots[routed].atoms.contains(&Atom::Resource(3, 0)));
        }
        let (mut focused, context) = normal.focused(20, 0, &mut work).unwrap();
        assert!(focused.roots.is_empty());
        for original in 0..normal.slots.len() {
            assert!(focused.slots[original].terminal);
            assert!(
                !focused.slots[original].preparation.is_edges_installed(),
                "frozen copies carry atoms, never queue setup completion"
            );
        }
        let function = focused.slot(4, context, &mut work).unwrap();
        assert!(!focused.slots[function].terminal);
        assert!(!focused.slots[function].preparation.is_edges_installed());
        focused.close(&mut work).unwrap();
        assert!(focused.slots[function].preparation.is_edges_installed());
        assert!(
            focused
                .dependencies(function, &mut work)
                .unwrap()
                .contains(&Atom::Resource(3, context))
        );
        assert!(
            matches!(
                focused.freeze_slot(4, 0, context, &mut work),
                Err(Failure::Invalid)
            ),
            "completed active setup never grants freeze authority"
        );
        assert!(!focused.slots[function].terminal);

        let cut = focused
            .restore_cut(0, 21, 9, 21, &[], false, &mut work)
            .unwrap();
        assert!(focused.slots[cut.input].terminal);
        assert!(!focused.slots[cut.input].preparation.is_edges_installed());
        let handle = focused.indices[&(0, context)];
        focused.join_ports(cut.input, handle, &mut work).unwrap();
        focused.close(&mut work).unwrap();
        assert!(
            focused.slots[cut.result]
                .atoms
                .contains(&Atom::Resource(3, context))
        );
        assert!(focused.slots[cut.input].terminal);
        assert!(!focused.slots[cut.input].preparation.is_edges_installed());
        let restored = focused
            .restore_event(normal.indices[&(4, 0)], &mut work)
            .unwrap();
        assert!(focused.slots[restored].terminal);
        assert!(!focused.slots[restored].preparation.is_edges_installed());
    }

    #[test]
    fn immutable_setup_completion_refuses_all_cold_cuts_after_ordered_propagation() {
        let graph = immutable_setup_graph();
        fn setup(graph: &Graph, expression: usize) -> (Analysis<'_>, usize) {
            let mut work = TypeWorkBudget::unbounded();
            let mut analysis = Analysis::new(graph, &mut work).unwrap();
            analysis.slot(3, 0, &mut work).unwrap();
            analysis.close(&mut work).unwrap();
            let slot = analysis.slot(expression, 0, &mut work).unwrap();
            if expression != 4 {
                // Direct setup installs ordinary relations but cannot mark
                // completion; their real Resource prefixes remain undelivered.
                // This isolates one queue attempt including propagation refusal.
                analysis.evaluate(slot, &mut work).unwrap();
                assert!(
                    analysis.slots[slot]
                        .edges
                        .iter()
                        .all(|source| analysis.edge_pairs()[&(slot, *source)] == 0)
                );
            }
            assert!(!analysis.slots[slot].preparation.is_edges_installed());
            assert_eq!(
                analysis.pending.iter().copied().collect::<Vec<_>>(),
                vec![slot]
            );
            (analysis, slot)
        }
        for expression in [4, 5, 6] {
            let (mut measured, slot) = setup(&graph, expression);
            let mut work = TypeWorkBudget::unbounded();
            measured.close(&mut work).unwrap();
            let exact = work.used();
            assert!(measured.slots[slot].preparation.is_edges_installed());
            assert!(
                measured
                    .dependencies(slot, &mut TypeWorkBudget::unbounded())
                    .unwrap()
                    .contains(&Atom::Resource(3, 0))
            );
            for prefix in [0, 9] {
                for available in 0..exact {
                    let (mut refused, attempted) = setup(&graph, expression);
                    let mut short = TypeWorkBudget::with_limit(prefix + available);
                    short.charge(prefix).unwrap();
                    assert!(matches!(refused.close(&mut short), Err(Failure::Resource)));
                    assert!(!refused.slots[attempted].preparation.is_edges_installed());
                    if available == exact - 1 {
                        // The last debit follows all original output/link work
                        // and every actual source atom's ordered delivery.
                        assert!(
                            refused
                                .dependencies(attempted, &mut TypeWorkBudget::unbounded())
                                .unwrap()
                                .contains(&Atom::Resource(3, 0))
                        );
                        for &source in &refused.slots[attempted].edges {
                            assert_eq!(
                                refused.edge_pairs()[&(attempted, source)],
                                refused.slots[source].atoms.len()
                            );
                        }
                    }
                }
                for _ in 0..2 {
                    let (mut retried, attempted) = setup(&graph, expression);
                    let mut exact_work = TypeWorkBudget::with_limit(prefix + exact);
                    exact_work.charge(prefix).unwrap();
                    retried.close(&mut exact_work).unwrap();
                    assert_eq!(exact_work.used(), prefix + exact);
                    assert!(retried.slots[attempted].preparation.is_edges_installed());
                    assert_eq!(retried.slots[attempted].atoms, measured.slots[slot].atoms);
                    assert_eq!(retried.edge_pairs(), measured.edge_pairs());
                    assert_eq!(retried.watched_pairs(), measured.watched_pairs());
                }
            }
        }
    }

    #[test]
    fn ready_setup_completion_refuses_before_publication_and_keeps_live_inputs() {
        for shape in 0..6 {
            let mut graph = graph(vec![
                Expr::Slot,
                Expr::Slot,
                Expr::Slot,
                Expr::Slot,
                Expr::Slot,
                Expr::Slot,
            ]);
            graph.expressions[3] = match shape {
                0 => Expr::Tuple(vec![0, 1]),
                1 => Expr::Cleanup { body: 1, action: 0 },
                2 => Expr::Bind {
                    binder: 2,
                    initializer: 0,
                    body: 1,
                },
                3 => Expr::Recursive {
                    bindings: vec![(2, 2)],
                    body: 1,
                },
                4 => Expr::Match {
                    scrutinee: 0,
                    arms: vec![(Vec::new(), 1)],
                },
                5 => Expr::Resource {
                    success: None,
                    failure: None,
                    handle: 4,
                    identity: 5,
                    initializer: 0,
                    body: 1,
                    source: graph.sources[3],
                },
                _ => unreachable!(),
            };
            let setup = || {
                let mut work = TypeWorkBudget::unbounded();
                let mut analysis = Analysis::new(&graph, &mut work).unwrap();
                for expression in [0, 1, 2, 4, 5] {
                    analysis.slot(expression, 0, &mut work).unwrap();
                }
                for expression in [0, 1, 2] {
                    let input = analysis.indices[&(expression, 0)];
                    analysis
                        .atom(input, Atom::Resource(80 + expression, 0), &mut work)
                        .unwrap();
                }
                let binder = analysis.indices[&(2, 0)];
                let input = analysis.indices[&(0, 0)];
                analysis.edge(binder, input, &mut work).unwrap();
                analysis.edge(binder, binder, &mut work).unwrap();
                analysis.close(&mut work).unwrap();
                let result = analysis.slot(3, 0, &mut work).unwrap();
                assert!(analysis.evaluate(result, &mut work).unwrap());
                assert!(!analysis.slots[result].preparation.is_edges_installed());
                assert_eq!(
                    analysis.pending.iter().copied().collect::<Vec<_>>(),
                    vec![result]
                );
                (analysis, result)
            };
            let (mut measured, result) = setup();
            let mut work = TypeWorkBudget::unbounded();
            measured.close(&mut work).unwrap();
            let exact = work.used();
            assert!(measured.slots[result].preparation.is_edges_installed());
            for prefix in [0, 9] {
                for available in 0..exact {
                    let (mut refused, result) = setup();
                    let mut short = TypeWorkBudget::with_limit(prefix + available);
                    short.charge(prefix).unwrap();
                    assert!(
                        matches!(refused.close(&mut short), Err(Failure::Resource)),
                        "shape={shape} available={available}"
                    );
                    assert!(!refused.slots[result].preparation.is_edges_installed());
                    if available == exact - 1 {
                        for &source in &refused.slots[result].edges {
                            assert_eq!(
                                refused.edge_pairs()[&(result, source)],
                                refused.slots[source].atoms.len()
                            );
                        }
                    }
                }
                let (mut retried, result) = setup();
                let mut exact_work = TypeWorkBudget::with_limit(prefix + exact);
                exact_work.charge(prefix).unwrap();
                retried.close(&mut exact_work).unwrap();
                assert_eq!(exact_work.used(), prefix + exact);
                assert!(retried.slots[result].preparation.is_edges_installed());
                assert_eq!(retried.slots[result].atoms, measured.slots[result].atoms);
                assert_eq!(retried.edge_pairs(), measured.edge_pairs());
                assert_eq!(retried.watched_pairs(), measured.watched_pairs());
                // Newly arriving ownership/Unknown cannot reopen fixed setup,
                // but its original source slots and result dependencies stay live.
                let input = retried.indices[&(1, 0)];
                retried
                    .atom(
                        input,
                        Atom::Resource(99, 0),
                        &mut TypeWorkBudget::unbounded(),
                    )
                    .unwrap();
                retried
                    .atom(input, Atom::Unknown, &mut TypeWorkBudget::unbounded())
                    .unwrap();
                retried.close(&mut TypeWorkBudget::unbounded()).unwrap();
                assert!(
                    retried
                        .dependencies(result, &mut TypeWorkBudget::unbounded())
                        .unwrap()
                        .contains(&Atom::Resource(99, 0)),
                    "shape={shape}"
                );
                assert!(!retried.slots[result].terminal);
            }
        }
    }

    fn call_transfer_graph() -> Graph {
        let mut graph = graph(vec![
            Expr::Slot,
            Expr::Slot,
            Expr::Slot,
            Expr::Slot,
            Expr::Merge(vec![2, 3]),
            Expr::Function {
                parameters: vec![2],
                body: 4,
                captures: vec![3],
            },
            Expr::Call {
                function: 0,
                arguments: vec![1],
                scalar: false,
                type_application: false,
            },
            Expr::Function {
                parameters: vec![2],
                body: 4,
                captures: vec![3],
            },
            Expr::Scalar,
        ]);
        graph.expressions.push(Expr::Resource {
            success: None,
            failure: None,
            handle: 2,
            identity: 3,
            initializer: 8,
            body: 4,
            source: graph.sources[0],
        });
        graph.expressions.push(Expr::Tuple(vec![3]));
        graph.sources.extend([graph.sources[0]; 2]);
        graph
    }

    fn evidence_completion_graph() -> Graph {
        use crate::interface::{InterfaceId, MethodId, RequirementId, RequirementOwner};
        let source = crate::source::SourceFile::new("evidence-completion.ash", "x").unwrap();
        let interface = InterfaceId::new(crate::module::ModuleId::from(source.id()), 0);
        let method = MethodId::new(interface, 0);
        let requirement = RequirementId::new(RequirementOwner::Global(BinderId::generated(980)), 0);
        let mut graph = graph(vec![
            Expr::Slot,
            Expr::Slot,
            Expr::Slot,
            Expr::Slot,
            Expr::Scalar,
            Expr::Function {
                parameters: Vec::new(),
                body: 4,
                captures: vec![2, 3],
            },
            Expr::Evidence {
                value: 0,
                bindings: vec![(requirement, method, 1)],
            },
            Expr::Tuple(vec![3]),
        ]);
        graph.expressions.push(Expr::Resource {
            success: None,
            failure: None,
            handle: 2,
            identity: 3,
            initializer: 4,
            body: 4,
            source: graph.sources[0],
        });
        graph.sources.push(graph.sources[0]);
        graph.evidence = vec![((requirement, method), 2)];
        graph
    }

    #[test]
    fn evidence_self_source_snapshot_keeps_unknown_and_late_resource_dependencies() {
        let mut graph = evidence_completion_graph();
        let Expr::Evidence { value, .. } = &mut graph.expressions[6] else {
            unreachable!()
        };
        *value = 6;
        let mut work = TypeWorkBudget::unbounded();
        let mut analysis = Analysis::new(&graph, &mut work).unwrap();
        analysis.slot(8, 0, &mut work).unwrap();
        analysis.close(&mut work).unwrap();
        let owner = Atom::Resource(8, 0);
        let handle = analysis.indices[&(2, 0)];
        assert!(analysis.slots[handle].atoms.contains(&owner));
        let argument = analysis.slot(1, 0, &mut work).unwrap();
        analysis.atom(argument, owner, &mut work).unwrap();
        let evidence = analysis.slot(6, 0, &mut work).unwrap();
        analysis.atom(evidence, Atom::Unknown, &mut work).unwrap();
        analysis.current = Some(evidence);
        analysis.evaluate(evidence, &mut work).unwrap();
        assert_eq!(analysis.slots[evidence].atoms, vec![Atom::Unknown, owner]);
        analysis.current = None;
        analysis.close(&mut work).unwrap();
        let creation = analysis
            .context(0, Transition::Root(190), &mut work)
            .unwrap();
        analysis.slot(8, creation, &mut work).unwrap();
        analysis.close(&mut work).unwrap();
        let late = Atom::Resource(8, creation);
        let handle = analysis.indices[&(2, creation)];
        assert!(analysis.slots[handle].atoms.contains(&late));
        analysis.atom(argument, late, &mut work).unwrap();
        analysis.close(&mut work).unwrap();
        assert_eq!(
            analysis.slots[evidence].atoms,
            vec![Atom::Unknown, owner, late]
        );
        assert_eq!(
            analysis.dependencies(evidence, &mut work).unwrap(),
            vec![owner, late]
        );
        assert!(analysis.watched_pairs().contains(&(argument, evidence)));
        assert!(analysis.watched_pairs().contains(&(evidence, evidence)));
    }

    #[test]
    fn evidence_completion_keeps_late_dictionary_owners_and_exact_closure_readers() {
        let graph = evidence_completion_graph();
        let mut work = TypeWorkBudget::unbounded();
        let mut analysis = Analysis::new(&graph, &mut work).unwrap();
        let first = analysis
            .context(0, Transition::Root(80), &mut work)
            .unwrap();
        let second = analysis
            .context(0, Transition::Root(81), &mut work)
            .unwrap();
        let creation = analysis
            .context(0, Transition::Root(82), &mut work)
            .unwrap();
        let other_creation = analysis
            .context(0, Transition::Root(83), &mut work)
            .unwrap();
        for context in [creation, other_creation] {
            let lexical = analysis.slot(3, context, &mut work).unwrap();
            analysis.atom(lexical, Atom::Free, &mut work).unwrap();
        }
        let mut evidence = Vec::new();
        for context in [first, second] {
            let value = analysis.slot(0, context, &mut work).unwrap();
            analysis
                .atom(value, Atom::Closure(5, creation), &mut work)
                .unwrap();
            let argument = analysis.slot(1, context, &mut work).unwrap();
            analysis.atom(argument, Atom::Free, &mut work).unwrap();
            evidence.push(analysis.slot(6, context, &mut work).unwrap());
        }
        analysis.close(&mut work).unwrap();
        for &slot in &evidence {
            assert!(
                analysis
                    .callable_transfers
                    .contains(&(Some(slot), slot, 5, creation))
            );
            assert!(analysis.dependencies(slot, &mut work).unwrap().is_empty());
        }
        assert_eq!(analysis.callable_transfers.len(), 2);

        // Obtain the late owner from the graph's actual Resource transfer,
        // then place the independent access fact in only the first dictionary.
        let owner_context = analysis
            .context(0, Transition::Root(84), &mut work)
            .unwrap();
        analysis.slot(8, owner_context, &mut work).unwrap();
        analysis.close(&mut work).unwrap();
        let owner = Atom::Resource(8, owner_context);
        let handle = analysis.indices[&(2, owner_context)];
        assert!(analysis.slots[handle].atoms.contains(&owner));
        let first_argument = analysis.indices[&(1, first)];
        analysis.atom(first_argument, owner, &mut work).unwrap();
        analysis.close(&mut work).unwrap();
        assert_eq!(
            analysis.dependencies(evidence[0], &mut work).unwrap(),
            vec![owner]
        );
        assert!(
            analysis
                .dependencies(evidence[1], &mut work)
                .unwrap()
                .is_empty()
        );
        assert_eq!(analysis.callable_transfers.len(), 2);

        // A new exact closure creation must install its lexical capture links,
        // even though the result uses the existing specialized context.
        let value = analysis.indices[&(0, first)];
        analysis
            .atom(value, Atom::Closure(5, other_creation), &mut work)
            .unwrap();
        analysis.close(&mut work).unwrap();
        assert!(analysis.callable_transfers.contains(&(
            Some(evidence[0]),
            evidence[0],
            5,
            other_creation,
        )));
        let lexical_owner_context = analysis
            .context(0, Transition::Root(85), &mut work)
            .unwrap();
        analysis.slot(8, lexical_owner_context, &mut work).unwrap();
        analysis.close(&mut work).unwrap();
        let lexical_owner = Atom::Resource(8, lexical_owner_context);
        let lexical = analysis.indices[&(3, other_creation)];
        analysis.atom(lexical, lexical_owner, &mut work).unwrap();
        analysis.close(&mut work).unwrap();
        let dependencies = analysis.dependencies(evidence[0], &mut work).unwrap();
        assert!(dependencies.contains(&owner));
        assert!(dependencies.contains(&lexical_owner));
        assert!(
            analysis
                .dependencies(evidence[1], &mut work)
                .unwrap()
                .is_empty()
        );

        let reader_context = analysis
            .context(0, Transition::Root(86), &mut work)
            .unwrap();
        let reader = analysis.slot(4, reader_context, &mut work).unwrap();
        analysis.current = Some(reader);
        analysis.evaluate(evidence[0], &mut work).unwrap();
        let specialized = analysis
            .context(first, Transition::Call(6), &mut work)
            .unwrap();
        for key in [(0, first), (1, first), (2, specialized), (3, specialized)] {
            let dependency = analysis.indices[&key];
            assert!(analysis.slots[dependency].readers.contains(&reader));
        }
        for context in [creation, other_creation] {
            assert!(
                analysis
                    .callable_transfers
                    .contains(&(Some(reader), evidence[0], 5, context,))
            );
        }
        analysis.current = None;
        analysis.evaluate(evidence[0], &mut work).unwrap();
        for context in [creation, other_creation] {
            assert!(
                analysis
                    .callable_transfers
                    .contains(&(None, evidence[0], 5, context))
            );
        }

        // Unknown output retains deep argument readers through an unchanged
        // aggregate. A later resource therefore reaches the ordinary result.
        let unknown_context = analysis
            .context(0, Transition::Root(87), &mut work)
            .unwrap();
        let value = analysis.slot(0, unknown_context, &mut work).unwrap();
        analysis.atom(value, Atom::Unknown, &mut work).unwrap();
        let argument = analysis.slot(1, unknown_context, &mut work).unwrap();
        analysis
            .atom(argument, Atom::Aggregate(7, unknown_context), &mut work)
            .unwrap();
        let field = analysis.slot(3, unknown_context, &mut work).unwrap();
        analysis.atom(field, Atom::Free, &mut work).unwrap();
        let unknown = analysis.slot(6, unknown_context, &mut work).unwrap();
        analysis.close(&mut work).unwrap();
        assert!(analysis.slots[field].readers.contains(&unknown));
        analysis.atom(field, owner, &mut work).unwrap();
        analysis.close(&mut work).unwrap();
        assert!(analysis.slots[unknown].atoms.contains(&Atom::Unknown));
        assert!(analysis.slots[unknown].atoms.contains(&owner));
        assert!(
            analysis
                .callable_transfers
                .iter()
                .all(|(_, slot, _, _)| *slot != unknown)
        );
    }

    #[test]
    fn evidence_completion_refusals_never_publish_attempted_transfers() {
        let graph = evidence_completion_graph();
        fn setup(graph: &Graph) -> (Analysis<'_>, usize) {
            let mut work = TypeWorkBudget::unbounded();
            let mut analysis = Analysis::new(graph, &mut work).unwrap();
            let value = analysis.slot(0, 0, &mut work).unwrap();
            analysis
                .atom(value, Atom::Closure(5, 0), &mut work)
                .unwrap();
            for expression in [1, 3] {
                let input = analysis.slot(expression, 0, &mut work).unwrap();
                analysis.atom(input, Atom::Free, &mut work).unwrap();
            }
            let evidence = analysis.slot(6, 0, &mut work).unwrap();
            analysis.current = Some(evidence);
            (analysis, evidence)
        }
        let (mut measured, evidence) = setup(&graph);
        let mut work = TypeWorkBudget::unbounded();
        measured.evaluate(evidence, &mut work).unwrap();
        let exact = work.used();
        assert!(
            measured
                .callable_transfers
                .contains(&(Some(evidence), evidence, 5, 0))
        );
        assert_eq!(measured.slots[evidence].atoms.len(), 1);
        let edges = measured.edge_pairs();
        let watches = measured.watched_pairs();
        for prefix in [0, 9] {
            for available in 0..exact {
                let (mut refused, evidence) = setup(&graph);
                let mut short = TypeWorkBudget::with_limit(prefix + available);
                short.charge(prefix).unwrap();
                assert!(matches!(
                    refused.evaluate(evidence, &mut short),
                    Err(Failure::Resource)
                ));
                assert!(
                    refused.callable_transfers.is_empty(),
                    "a refused final result or link cannot complete the transfer"
                );
            }
            for _ in 0..2 {
                let (mut retried, evidence) = setup(&graph);
                let mut retry = TypeWorkBudget::with_limit(prefix + exact);
                retry.charge(prefix).unwrap();
                retried.evaluate(evidence, &mut retry).unwrap();
                assert_eq!(retry.used(), prefix + exact);
                assert_eq!(retried.edge_pairs(), edges);
                assert_eq!(retried.watched_pairs(), watches);
                assert_eq!(retried.callable_transfers, measured.callable_transfers);
                assert_eq!(
                    retried.slots[evidence].atoms,
                    measured.slots[evidence].atoms
                );
            }
        }
        let revision = measured.revision;
        let slots = measured.slots.len();
        // ASH_INPUT169_BEGIN_COST
        // Paid input-phase guard and value-port lookup, Function guard and
        // completed-key lookup; dynamic routes still run without a value copy.
        let mut duplicate = TypeWorkBudget::with_limit(4);
        measured.evaluate(evidence, &mut duplicate).unwrap();
        assert_eq!(duplicate.used(), 4);
        // ASH_INPUT169_END_COST
        assert_eq!(measured.revision, revision);
        assert_eq!(measured.slots.len(), slots);
        assert_eq!(measured.edge_pairs(), edges);
        assert_eq!(measured.watched_pairs(), watches);

        let (mut malformed, evidence) = setup(&graph);
        let value = malformed.indices[&(0, 0)];
        malformed.slots[value].atoms = vec![Atom::Closure(7, 0)];
        assert!(matches!(
            malformed.evaluate(evidence, &mut work),
            Err(Failure::Invalid)
        ));
        assert!(malformed.callable_transfers.is_empty());
    }

    #[test]
    fn completed_callable_transfers_keep_late_values_creation_contexts_and_unknown_readers() {
        let graph = call_transfer_graph();
        let mut work = TypeWorkBudget::unbounded();
        let mut analysis = Analysis::new(&graph, &mut work).unwrap();
        let first = analysis
            .context(0, Transition::Root(20), &mut work)
            .unwrap();
        let second = analysis
            .context(0, Transition::Root(21), &mut work)
            .unwrap();
        let creation = analysis
            .context(0, Transition::Root(22), &mut work)
            .unwrap();
        let other_creation = analysis
            .context(0, Transition::Root(23), &mut work)
            .unwrap();
        for captured in [creation, other_creation] {
            let capture = analysis.slot(3, captured, &mut work).unwrap();
            analysis.atom(capture, Atom::Free, &mut work).unwrap();
        }
        let mut calls = Vec::new();
        for context in [first, second] {
            let function = analysis.slot(0, context, &mut work).unwrap();
            analysis
                .atom(function, Atom::Closure(5, creation), &mut work)
                .unwrap();
            let argument = analysis.slot(1, context, &mut work).unwrap();
            analysis.atom(argument, Atom::Free, &mut work).unwrap();
            calls.push(analysis.slot(6, context, &mut work).unwrap());
        }
        analysis.close(&mut work).unwrap();
        assert_eq!(analysis.callable_transfers.len(), 2);
        assert!(
            analysis
                .callable_transfers
                .contains(&(Some(calls[0]), calls[0], 5, creation))
        );
        assert!(
            analysis
                .callable_transfers
                .contains(&(Some(calls[1]), calls[1], 5, creation))
        );
        let first_argument = analysis.indices[&(1, first)];
        let second_argument = analysis.indices[&(1, second)];
        assert_ne!(first_argument, second_argument);
        assert!(analysis.slots[first_argument].readers.contains(&calls[0]));
        assert!(!analysis.slots[first_argument].readers.contains(&calls[1]));
        let first_invoked = analysis
            .context(first, Transition::Invoke(6, 5), &mut work)
            .unwrap();
        for expression in [2, 3] {
            let installed = analysis.indices[&(expression, first_invoked)];
            assert!(!analysis.watched_pairs().contains(&(installed, calls[0])));
        }
        let original_capture = analysis.indices[&(3, creation)];
        assert!(
            !analysis
                .watched_pairs()
                .contains(&(original_capture, calls[0]))
        );
        let argument_owner = Atom::Resource(9, first);
        analysis
            .atom(first_argument, argument_owner, &mut work)
            .unwrap();
        analysis.close(&mut work).unwrap();
        assert!(analysis.slots[calls[0]].atoms.contains(&argument_owner));
        assert!(!analysis.slots[calls[1]].atoms.contains(&argument_owner));
        assert_eq!(analysis.callable_transfers.len(), 2);
        let function = analysis.indices[&(0, first)];
        analysis
            .atom(function, Atom::Closure(5, other_creation), &mut work)
            .unwrap();
        analysis
            .atom(function, Atom::Closure(7, creation), &mut work)
            .unwrap();
        analysis.close(&mut work).unwrap();
        assert!(analysis.callable_transfers.contains(&(
            Some(calls[0]),
            calls[0],
            5,
            other_creation
        )));
        assert!(
            analysis
                .callable_transfers
                .contains(&(Some(calls[0]), calls[0], 7, creation))
        );
        assert_eq!(analysis.callable_transfers.len(), 4);
        let capture = analysis.indices[&(3, other_creation)];
        let captured_owner = Atom::Resource(9, other_creation);
        analysis.atom(capture, captured_owner, &mut work).unwrap();
        analysis.close(&mut work).unwrap();
        assert!(analysis.slots[calls[0]].atoms.contains(&captured_owner));
        assert!(!analysis.slots[calls[1]].atoms.contains(&captured_owner));
        assert_eq!(analysis.callable_transfers.len(), 4);

        // Unknown calls must keep dependency readers beneath unchanged aggregates.
        let unknown_context = analysis
            .context(0, Transition::Root(24), &mut work)
            .unwrap();
        let unknown_function = analysis.slot(0, unknown_context, &mut work).unwrap();
        analysis
            .atom(unknown_function, Atom::Unknown, &mut work)
            .unwrap();
        let unknown_argument = analysis.slot(1, unknown_context, &mut work).unwrap();
        analysis
            .atom(unknown_argument, Atom::Aggregate(10, creation), &mut work)
            .unwrap();
        let unknown_call = analysis.slot(6, unknown_context, &mut work).unwrap();
        analysis.close(&mut work).unwrap();
        let capture = analysis.indices[&(3, creation)];
        assert!(analysis.slots[capture].readers.contains(&unknown_call));
        let late_owner = Atom::Resource(9, creation);
        analysis.atom(capture, late_owner, &mut work).unwrap();
        analysis.close(&mut work).unwrap();
        assert!(analysis.slots[unknown_call].atoms.contains(&late_owner));
        assert_eq!(analysis.callable_transfers.len(), 4);
        assert!(
            analysis
                .callable_transfers
                .iter()
                .all(|(_, call, _, _)| *call != unknown_call)
        );
    }

    #[test]
    fn call_transfer_completion_has_prefilled_refusal_and_fresh_exact_retry_boundaries() {
        fn setup(graph: &Graph) -> (Analysis<'_>, usize) {
            let mut work = TypeWorkBudget::unbounded();
            let mut analysis = Analysis::new(graph, &mut work).unwrap();
            let function = analysis.slot(0, 0, &mut work).unwrap();
            analysis
                .atom(function, Atom::Closure(5, 0), &mut work)
                .unwrap();
            let argument = analysis.slot(1, 0, &mut work).unwrap();
            analysis.atom(argument, Atom::Free, &mut work).unwrap();
            let capture = analysis.slot(3, 0, &mut work).unwrap();
            analysis.atom(capture, Atom::Free, &mut work).unwrap();
            let call = analysis.slot(6, 0, &mut work).unwrap();
            analysis.current = Some(call);
            (analysis, call)
        }
        let graph = call_transfer_graph();
        let (mut measured, call) = setup(&graph);
        let mut work = TypeWorkBudget::unbounded();
        measured.evaluate(call, &mut work).unwrap();
        let exact = work.used();
        assert!(
            measured
                .callable_transfers
                .contains(&(Some(call), call, 5, 0))
        );
        let revision = measured.revision;
        let slot_count = measured.slots.len();
        let edges = measured.edge_pairs();
        let watches = measured.watched_pairs();
        // Two existing slots+watches, one argument visit, a paid atom visit,
        // and one completed-transfer lookup: no context or edge reconstruction.
        let mut duplicate = TypeWorkBudget::with_limit(7);
        measured.evaluate(call, &mut duplicate).unwrap();
        assert_eq!(duplicate.used(), 7);
        assert_eq!(measured.revision, revision);
        assert_eq!(measured.slots.len(), slot_count);
        assert_eq!(measured.edge_pairs(), edges);
        assert_eq!(measured.watched_pairs(), watches);
        for prefix in [0, 9] {
            for available in 0..exact {
                let (mut failed, call) = setup(&graph);
                let mut short = TypeWorkBudget::with_limit(prefix + available);
                short.charge(prefix).unwrap();
                assert!(matches!(
                    failed.evaluate(call, &mut short),
                    Err(Failure::Resource)
                ));
                assert!(
                    failed.callable_transfers.is_empty(),
                    "refused setup cannot publish completed topology"
                );
            }
            let (mut retried, call) = setup(&graph);
            let mut retry = TypeWorkBudget::with_limit(prefix + exact);
            retry.charge(prefix).unwrap();
            retried.evaluate(call, &mut retry).unwrap();
            assert_eq!(retry.used(), prefix + exact);
            assert_eq!(retried.callable_transfers, measured.callable_transfers);
            assert_eq!(retried.edge_pairs(), edges);
            assert_eq!(retried.watched_pairs(), watches);
        }
        // Direct private evaluation may have a different or absent reader.
        // Those calls must not reuse a record that omits their required watches.
        let mut extra = TypeWorkBudget::unbounded();
        let other_reader = measured.slot(8, 0, &mut extra).unwrap();
        measured.current = Some(other_reader);
        measured.evaluate(call, &mut extra).unwrap();
        assert!(
            measured
                .callable_transfers
                .contains(&(Some(other_reader), call, 5, 0))
        );
        let invoked = measured
            .context(0, Transition::Invoke(6, 5), &mut extra)
            .unwrap();
        for key in [
            (0, 0),
            (1, 0),
            (3, 0),
            (2, invoked),
            (3, invoked),
            (4, invoked),
        ] {
            let dependency = measured.indices[&key];
            assert!(measured.slots[dependency].readers.contains(&other_reader));
        }
        measured.current = None;
        measured.evaluate(call, &mut extra).unwrap();
        assert!(measured.callable_transfers.contains(&(None, call, 5, 0)));
        assert_eq!(measured.callable_transfers.len(), 3);
    }

    #[test]
    fn watched_pairs_keep_creation_contexts_notification_order_and_failed_insertion_atomic() {
        let graph = graph(vec![Expr::Slot]);
        let mut setup = TypeWorkBudget::unbounded();
        let mut analysis = Analysis::new(&graph, &mut setup).unwrap();
        let mut slots = Vec::new();
        for root in 1..=6 {
            let context = analysis
                .context(0, Transition::Root(root), &mut setup)
                .unwrap();
            slots.push(analysis.slot(0, context, &mut setup).unwrap());
        }
        let [source, other_source, first, second, fresh, prefilled] = slots.as_slice() else {
            panic!("six exact slots")
        };
        assert_eq!(
            analysis.slots[*source].key.0,
            analysis.slots[*other_source].key.0
        );
        assert_ne!(
            analysis.slots[*source].key.1,
            analysis.slots[*other_source].key.1
        );
        analysis.watch(*source, *second, &mut setup).unwrap();
        analysis.watch(*source, *first, &mut setup).unwrap();
        analysis.watch(*source, *second, &mut setup).unwrap();
        analysis.watch(*other_source, *first, &mut setup).unwrap();
        assert_eq!(analysis.slots[*source].readers, vec![*second, *first]);
        assert_eq!(analysis.slots[*other_source].readers, vec![*first]);
        for (prefix, fresh) in [(0, *fresh), (9, *prefilled)] {
            let mut duplicate = TypeWorkBudget::with_limit(prefix + 1);
            duplicate.charge(prefix).unwrap();
            analysis.watch(*source, *first, &mut duplicate).unwrap();
            assert_eq!(duplicate.used(), prefix + 1);
            let before_pairs = analysis.dependencies.entries.len();
            let before_readers = analysis.slots[*source].readers.clone();
            let mut short = TypeWorkBudget::with_limit(prefix + 2);
            short.charge(prefix).unwrap();
            assert!(matches!(
                analysis.watch(*source, fresh, &mut short),
                Err(Failure::Resource)
            ));
            assert_eq!(short.used(), prefix + 1);
            assert_eq!(analysis.dependencies.entries.len(), before_pairs);
            assert_eq!(analysis.slots[*source].readers, before_readers);
            let mut exact = TypeWorkBudget::with_limit(prefix + 3);
            exact.charge(prefix).unwrap();
            analysis.watch(*source, fresh, &mut exact).unwrap();
            assert_eq!(exact.used(), prefix + 3);
            let mut expected = before_readers;
            expected.push(fresh);
            assert_eq!(analysis.slots[*source].readers, expected);
        }
        analysis.pending.clear();
        for slot in &mut analysis.slots {
            slot.queued = false;
        }
        analysis.atom(*source, Atom::Unknown, &mut setup).unwrap();
        assert_eq!(
            analysis.pending.iter().copied().collect::<Vec<_>>(),
            vec![*second, *first, *fresh, *prefilled]
        );
        assert_eq!(analysis.slots[*source].atoms, vec![Atom::Unknown]);
        assert!(analysis.slots[*other_source].atoms.is_empty());
        analysis.pending.clear();
        for slot in &mut analysis.slots {
            slot.queued = false;
        }
        analysis
            .atom(*other_source, Atom::Resource(99, 0), &mut setup)
            .unwrap();
        assert_eq!(
            analysis.pending.iter().copied().collect::<Vec<_>>(),
            vec![*first]
        );
    }

    #[test]
    fn repeated_wide_watch_dependencies_retry_at_exact_work_without_reordering() {
        const WIDTH: usize = 96;
        let graph = graph(vec![Expr::Slot]);
        let run = |budget: &mut TypeWorkBudget| {
            let mut analysis = Analysis::new(&graph, budget)?;
            let source = analysis.slot(0, 0, budget)?;
            let mut readers = Vec::new();
            for site in 1..=WIDTH {
                let context = analysis.context(0, Transition::Root(site), budget)?;
                let reader = analysis.slot(0, context, budget)?;
                analysis.watch(source, reader, budget)?;
                readers.push(reader);
            }
            // Repeated graph visits observe the same exact pair, not a new
            // notification or an analysis-wide authority conclusion.
            for _ in 0..WIDTH {
                for reader in readers.iter().rev() {
                    analysis.watch(source, *reader, budget)?;
                }
            }
            assert_eq!(analysis.slots[source].readers, readers);
            assert_eq!(analysis.dependencies.entries.len(), WIDTH);
            analysis.pending.clear();
            for slot in &mut analysis.slots {
                slot.queued = false;
            }
            analysis.atom(source, Atom::Unknown, budget)?;
            assert_eq!(
                analysis.pending.iter().copied().collect::<Vec<_>>(),
                readers
            );
            Ok::<(), Failure>(())
        };
        let mut measured = TypeWorkBudget::unbounded();
        run(&mut measured).unwrap();
        // Repeated membership is bounded by pair visits, independently of fanout.
        assert!(measured.used() < 2 * WIDTH * WIDTH);
        let mut short = TypeWorkBudget::with_limit(measured.used() - 1);
        assert!(matches!(run(&mut short), Err(Failure::Resource)));
        for _ in 0..2 {
            let mut exact = TypeWorkBudget::with_limit(measured.used());
            run(&mut exact).unwrap();
            assert_eq!(exact.used(), measured.used());
        }
    }

    #[test]
    fn edge_pairs_preserve_contexts_order_independent_watches_and_atomic_budget_boundaries() {
        assert_eq!(
            std::mem::size_of::<DependencyProgress>(),
            std::mem::size_of::<usize>()
        );
        let graph = graph(vec![Expr::Slot]);
        let mut setup = TypeWorkBudget::unbounded();
        let mut analysis = Analysis::new(&graph, &mut setup).unwrap();
        let mut slots = Vec::new();
        for site in 1..=7 {
            let context = analysis
                .context(0, Transition::Root(site), &mut setup)
                .unwrap();
            slots.push(analysis.slot(0, context, &mut setup).unwrap());
        }
        let [
            target,
            other_target,
            first,
            second,
            fresh,
            prefilled,
            watched,
        ] = slots.as_slice()
        else {
            panic!("seven exact contextful slots")
        };
        assert_eq!(analysis.slots[*first].key.0, analysis.slots[*second].key.0);
        assert_ne!(analysis.slots[*first].key.1, analysis.slots[*second].key.1);
        analysis.watch(*second, *other_target, &mut setup).unwrap();
        analysis.edge(*target, *second, &mut setup).unwrap();
        analysis.edge(*target, *first, &mut setup).unwrap();
        assert_eq!(analysis.slots[*target].edges, vec![*second, *first]);
        assert!(
            !analysis
                .edge_pairs()
                .contains_key(&(*other_target, *second))
        );
        assert_eq!(
            analysis.slots[*second].readers,
            vec![*other_target, *target]
        );
        analysis.pending.clear();
        for slot in &mut analysis.slots {
            slot.queued = false;
        }
        for (prefix, source) in [(0, *fresh), (9, *prefilled)] {
            let mut duplicate = TypeWorkBudget::with_limit(prefix + 2);
            duplicate.charge(prefix).unwrap();
            analysis.edge(*target, *first, &mut duplicate).unwrap();
            assert_eq!(duplicate.used(), prefix + 2);
            assert!(!analysis.slots[*target].queued);
            let before_edges = analysis.slots[*target].edges.clone();
            let before_pairs = analysis.edge_pairs();
            let before_watches = analysis.watched_pairs();
            let before_readers = analysis.slots[source].readers.clone();
            let before_revision = analysis.revision;
            for allowance in 0..6 {
                let mut short = TypeWorkBudget::with_limit(prefix + allowance);
                short.charge(prefix).unwrap();
                assert!(matches!(
                    analysis.edge(*target, source, &mut short),
                    Err(Failure::Resource)
                ));
                assert_eq!(analysis.slots[*target].edges, before_edges);
                assert_eq!(analysis.edge_pairs(), before_pairs);
                assert_eq!(analysis.watched_pairs(), before_watches);
                assert_eq!(analysis.slots[source].readers, before_readers);
                assert_eq!(analysis.revision, before_revision);
                assert!(analysis.pending.is_empty());
                assert!(!analysis.slots[*target].queued);
            }
            let mut exact = TypeWorkBudget::with_limit(prefix + 6);
            exact.charge(prefix).unwrap();
            analysis.edge(*target, source, &mut exact).unwrap();
            assert_eq!(exact.used(), prefix + 6);
            let mut expected = before_edges;
            expected.push(source);
            assert_eq!(analysis.slots[*target].edges, expected);
            assert_eq!(analysis.slots[source].readers, vec![*target]);
            assert_eq!(
                analysis.pending.iter().copied().collect::<Vec<_>>(),
                vec![*target]
            );
            analysis.pending.clear();
            analysis.slots[*target].queued = false;
        }
        // A watch does not imply an edge, and an existing watch costs no new
        // reader storage when the independently missing edge is inserted.
        analysis.watch(*watched, *target, &mut setup).unwrap();
        let before_pairs = analysis.edge_pairs();
        let before_relations = analysis.dependencies.entries.clone();
        let before_readers = analysis.slots[*watched].readers.clone();
        for allowance in 0..6 {
            let mut short = TypeWorkBudget::with_limit(allowance);
            assert!(matches!(
                analysis.edge(*target, *watched, &mut short),
                Err(Failure::Resource)
            ));
            assert_eq!(analysis.edge_pairs(), before_pairs);
            assert_eq!(analysis.dependencies.entries, before_relations);
            assert_eq!(analysis.slots[*watched].readers, before_readers);
            assert!(!analysis.slots[*target].queued);
        }
        let mut exact = TypeWorkBudget::with_limit(6);
        analysis.edge(*target, *watched, &mut exact).unwrap();
        assert_eq!(exact.used(), 6);
        assert_eq!(analysis.dependencies.entries.len(), before_relations.len());
        assert_eq!(
            analysis.dependencies.entries[&(*target, *watched)],
            DependencyProgress::LINKED_EMPTY
        );
        assert_eq!(analysis.slots[*watched].readers, vec![*target]);
        // A second target can already be queued, but still receives the exact
        // edge and its pre-existing watch without a second queue position.
        analysis.watch(*watched, *other_target, &mut setup).unwrap();
        analysis.enqueue(*other_target, &mut setup).unwrap();
        let before_pending = analysis.pending.iter().copied().collect::<Vec<_>>();
        let mut exact = TypeWorkBudget::with_limit(6);
        analysis.edge(*other_target, *watched, &mut exact).unwrap();
        assert_eq!(exact.used(), 6);
        assert_eq!(
            analysis.pending.iter().copied().collect::<Vec<_>>(),
            before_pending
        );
        assert_eq!(analysis.slots[*other_target].edges, vec![*watched]);
        analysis.pending.clear();
        for slot in &mut analysis.slots {
            slot.queued = false;
        }
        analysis.atom(*second, Atom::Unknown, &mut setup).unwrap();
        analysis.atom(*first, Atom::Free, &mut setup).unwrap();
        assert_eq!(
            analysis.pending.iter().copied().collect::<Vec<_>>(),
            vec![*other_target, *target]
        );
        analysis.close(&mut setup).unwrap();
        assert_eq!(
            analysis.slots[*target].atoms,
            vec![Atom::Unknown, Atom::Free]
        );
        assert!(
            analysis.slots[*other_target].atoms.is_empty(),
            "a watch alone never propagates atoms"
        );
        let before_pairs = analysis.edge_pairs();
        let mut frozen = TypeWorkBudget::with_limit(0);
        analysis.frozen_contexts = analysis.contexts.len();
        assert!(matches!(
            analysis.edge(*target, *first, &mut frozen),
            Err(Failure::Invalid)
        ));
        assert_eq!(analysis.edge_pairs(), before_pairs);
        assert_eq!(frozen.used(), 0);
    }

    #[test]
    fn edge_delta_prefixes_preserve_late_identity_order_and_reject_partial_completion() {
        let graph = graph(vec![Expr::Slot]);
        let setup = || {
            let mut work = TypeWorkBudget::unbounded();
            let mut analysis = Analysis::new(&graph, &mut work).unwrap();
            let creation = analysis.context(0, Transition::Root(1), &mut work).unwrap();
            let source = analysis.slot(0, creation, &mut work).unwrap();
            let target = analysis.slot(0, 0, &mut work).unwrap();
            analysis.edge(target, source, &mut work).unwrap();
            for atom in [Atom::Unknown, Atom::Free, Atom::Resource(0, creation)] {
                analysis.atom(source, atom, &mut work).unwrap();
            }
            analysis.pending.clear();
            for slot in &mut analysis.slots {
                slot.queued = false;
            }
            (analysis, source, target, creation)
        };
        let run = |budget: &mut TypeWorkBudget| {
            let (mut analysis, source, target, creation) = setup();
            let result = analysis
                .enqueue(target, budget)
                .and_then(|()| analysis.close(budget));
            if result.is_err() {
                assert_eq!(
                    analysis.edge_pairs().get(&(target, source)),
                    Some(&0),
                    "a refused suffix must not publish its completed prefix"
                );
            }
            result?;
            assert_eq!(
                analysis.slots[target].atoms,
                vec![Atom::Unknown, Atom::Free, Atom::Resource(0, creation)]
            );
            assert_eq!(analysis.edge_pairs().get(&(target, source)), Some(&3));
            Ok::<(), Failure>(())
        };
        // enqueue + pop + one original edge visit + cursor write under its loan +
        // three original ordered atom publications; no retained snapshots.
        const EXACT: usize = 1 + 1 + 1 + 1 + 3 * 3;
        for prefix in [0, 9] {
            for allowance in 0..EXACT {
                let mut short = TypeWorkBudget::with_limit(prefix + allowance);
                short.charge(prefix).unwrap();
                assert!(matches!(run(&mut short), Err(Failure::Resource)));
            }
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + EXACT);
                exact.charge(prefix).unwrap();
                run(&mut exact).unwrap();
                assert_eq!(exact.used(), prefix + EXACT);
            }
        }
        let (mut analysis, source, target, creation) = setup();
        let mut work = TypeWorkBudget::unbounded();
        analysis.enqueue(target, &mut work).unwrap();
        analysis.close(&mut work).unwrap();
        let mut caught_up = TypeWorkBudget::with_limit(3);
        analysis.enqueue(target, &mut caught_up).unwrap();
        analysis.close(&mut caught_up).unwrap();
        assert_eq!(
            caught_up.used(),
            3,
            "caught-up replay pays enqueue/pop/edge cursor, no old atoms"
        );
        let other_creation = analysis.context(0, Transition::Root(2), &mut work).unwrap();
        for atom in [
            Atom::Closure(0, creation),
            Atom::Resource(0, other_creation),
        ] {
            analysis.atom(source, atom, &mut work).unwrap();
        }
        analysis.close(&mut work).unwrap();
        assert_eq!(analysis.slots[target].atoms, analysis.slots[source].atoms);
        assert_eq!(analysis.edge_pairs().get(&(target, source)), Some(&5));
        // A new exact target starts at zero and receives an existing source
        // prefix. Independent readers receive notifications without values.
        let other = analysis.slot(0, other_creation, &mut work).unwrap();
        let observer_context = analysis.context(0, Transition::Root(3), &mut work).unwrap();
        let observer = analysis.slot(0, observer_context, &mut work).unwrap();
        analysis.watch(source, observer, &mut work).unwrap();
        analysis.edge(other, source, &mut work).unwrap();
        assert_eq!(analysis.edge_pairs().get(&(other, source)), Some(&0));
        analysis.edge(target, target, &mut work).unwrap();
        analysis.edge(source, target, &mut work).unwrap();
        analysis.close(&mut work).unwrap();
        assert_eq!(analysis.slots[other].atoms, analysis.slots[source].atoms);
        assert!(analysis.slots[observer].atoms.is_empty());
        analysis
            .atom(source, Atom::Closure(0, other_creation), &mut work)
            .unwrap();
        analysis.close(&mut work).unwrap();
        assert_eq!(analysis.slots[target].atoms, analysis.slots[source].atoms);
        assert_eq!(analysis.slots[other].atoms, analysis.slots[source].atoms);
        assert!(analysis.slots[observer].atoms.is_empty());
        assert_eq!(analysis.slots[target].edges, vec![source, target]);
        assert_eq!(
            analysis.edge_pairs()[&(target, target)],
            analysis.slots[target].atoms.len()
        );
        assert_eq!(
            analysis.edge_pairs()[&(source, target)],
            analysis.slots[target].atoms.len()
        );
        for malformed in [None, Some(4), Some(usize::MAX)] {
            let (mut rejected, source, target, _) = setup();
            if let Some(cursor) = malformed {
                rejected
                    .dependencies
                    .entries
                    .insert((target, source), DependencyProgress(cursor));
            } else {
                rejected.dependencies.entries.remove(&(target, source));
            }
            rejected.enqueue(target, &mut work).unwrap();
            assert!(matches!(rejected.close(&mut work), Err(Failure::Invalid)));
            assert!(rejected.slots[target].atoms.is_empty());
        }
    }

    #[test]
    fn repeated_wide_edges_retry_at_exact_work_without_reordering() {
        const WIDTH: usize = 96;
        let graph = graph(vec![Expr::Slot]);
        let run = |budget: &mut TypeWorkBudget| {
            let mut analysis = Analysis::new(&graph, budget)?;
            let target = analysis.slot(0, 0, budget)?;
            let mut sources = Vec::new();
            for site in 1..=WIDTH {
                let context = analysis.context(0, Transition::Root(site), budget)?;
                let source = analysis.slot(0, context, budget)?;
                analysis.edge(target, source, budget)?;
                sources.push(source);
            }
            assert_eq!(analysis.edge_pairs().len(), WIDTH);
            let mut linked_phase_reads = 0;
            for _ in 0..WIDTH {
                for source in sources.iter().rev() {
                    analysis.edge(target, *source, budget)?;
                    linked_phase_reads += 1;
                }
            }
            assert_eq!(analysis.slots[target].edges, sources);
            assert_eq!(analysis.edge_pairs().len(), WIDTH);
            analysis.close(budget)?;
            Ok::<usize, Failure>(linked_phase_reads)
        };
        let mut measured = TypeWorkBudget::unbounded();
        let linked_phase_reads = run(&mut measured).unwrap();
        assert_eq!(linked_phase_reads, WIDTH * WIDTH);
        // Empty context(1) + target(2) + W * [context(4) + slot(2) + vacant edge(6)]
        // + W^2 * linked hit(2) + close [W + 1 pops + W empty edges].
        assert_eq!(measured.used(), 2 * WIDTH * WIDTH + 14 * WIDTH + 4);
        let linked_phase_read_work = 1;
        let original_tariff_work = measured.used() - linked_phase_reads * linked_phase_read_work;
        assert!(
            original_tariff_work < 2 * WIDTH * WIDTH,
            "original growth bound excludes only the exact new Linked phase reads"
        );
        for prefix in [0, 9] {
            let mut short = TypeWorkBudget::with_limit(prefix + measured.used() - 1);
            short.charge(prefix).unwrap();
            assert!(matches!(run(&mut short), Err(Failure::Resource)));
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + measured.used());
                exact.charge(prefix).unwrap();
                run(&mut exact).unwrap();
                assert_eq!(exact.used(), prefix + measured.used());
            }
        }
    }

    #[test]
    fn atom_membership_publication_and_notifications_have_exact_retry_boundaries() {
        let graph = graph(vec![Expr::Slot, Expr::Slot, Expr::Slot]);
        for queued in [[false, false], [true, false], [true, true]] {
            for prefix in [0, 9] {
                for available in 0..5 {
                    let mut setup = TypeWorkBudget::unbounded();
                    let mut analysis = Analysis::new(&graph, &mut setup).unwrap();
                    let source = analysis.slot(0, 0, &mut setup).unwrap();
                    let first = analysis.slot(1, 0, &mut setup).unwrap();
                    let second = analysis.slot(2, 0, &mut setup).unwrap();
                    analysis.close(&mut setup).unwrap();
                    analysis.watch(source, second, &mut setup).unwrap();
                    analysis.watch(source, first, &mut setup).unwrap();
                    for (reader, already) in [second, first].into_iter().zip(queued) {
                        if already {
                            analysis.enqueue(reader, &mut setup).unwrap();
                        }
                    }
                    let before_pending = analysis.pending.clone();
                    let before_revision = analysis.revision;
                    let before_flags: Vec<_> =
                        analysis.slots.iter().map(|slot| slot.queued).collect();
                    let before_watches = analysis.watched_pairs();
                    let mut short = TypeWorkBudget::with_limit(prefix + available);
                    short.charge(prefix).unwrap();
                    assert!(matches!(
                        analysis.atom(source, Atom::Unknown, &mut short),
                        Err(Failure::Resource)
                    ));
                    assert!(analysis.atom_pairs.is_empty());
                    assert!(analysis.slots[source].atoms.is_empty());
                    assert_eq!(analysis.pending, before_pending);
                    assert_eq!(analysis.revision, before_revision);
                    assert_eq!(
                        analysis
                            .slots
                            .iter()
                            .map(|slot| slot.queued)
                            .collect::<Vec<_>>(),
                        before_flags
                    );
                    assert_eq!(analysis.watched_pairs(), before_watches);
                    let mut retry = TypeWorkBudget::with_limit(prefix + 5);
                    retry.charge(prefix).unwrap();
                    analysis.atom(source, Atom::Unknown, &mut retry).unwrap();
                    assert_eq!(retry.used(), prefix + 5);
                    assert_eq!(analysis.slots[source].atoms, vec![Atom::Unknown]);
                    assert!(analysis.atom_pairs.contains(&(source, Atom::Unknown)));
                    assert_eq!(analysis.revision, before_revision + 1);
                    let mut expected = before_pending;
                    for (reader, already) in [second, first].into_iter().zip(queued) {
                        if !already {
                            expected.push_back(reader);
                        }
                    }
                    assert_eq!(analysis.pending, expected);
                    let mut duplicate = TypeWorkBudget::with_limit(prefix + 1);
                    duplicate.charge(prefix).unwrap();
                    analysis
                        .atom(source, Atom::Unknown, &mut duplicate)
                        .unwrap();
                    assert_eq!(duplicate.used(), prefix + 1);
                    assert_eq!(analysis.pending, expected);
                    assert_eq!(analysis.revision, before_revision + 1);
                    analysis.close(&mut setup).unwrap();
                    for reader in [second, first] {
                        // Watch notification wakes evaluation; ordinary edges
                        // still own value propagation, independently of watches.
                        analysis.edge(reader, source, &mut setup).unwrap();
                    }
                    analysis.close(&mut setup).unwrap();
                    assert_eq!(analysis.slots[first].atoms, vec![Atom::Unknown]);
                    assert_eq!(analysis.slots[second].atoms, vec![Atom::Unknown]);
                }
            }
        }
    }

    #[test]
    fn atom_membership_keeps_variants_creation_contexts_and_slot_contexts_distinct() {
        let graph = graph(vec![Expr::Slot]);
        let mut work = TypeWorkBudget::unbounded();
        let mut analysis = Analysis::new(&graph, &mut work).unwrap();
        let first = analysis.slot(0, 0, &mut work).unwrap();
        let context = analysis.context(0, Transition::Call(0), &mut work).unwrap();
        let second = analysis.slot(0, context, &mut work).unwrap();
        let family = crate::types::NominalTypeId::new(crate::module::ModuleId::new(77), 1);
        let atoms = [
            Atom::Free,
            Atom::Unknown,
            Atom::Constructor(ConstructorId::new(family, 0)),
            Atom::Constructor(ConstructorId::new(family, 1)),
            Atom::Closure(5, 0),
            Atom::Closure(5, 1),
            Atom::Closure(6, 0),
            Atom::Aggregate(5, 0),
            Atom::Aggregate(5, 1),
            Atom::Aggregate(6, 0),
            Atom::Resource(5, 0),
            Atom::Resource(5, 1),
            Atom::Resource(6, 0),
        ];
        for slot in [first, second] {
            for atom in atoms {
                analysis.atom(slot, atom, &mut work).unwrap();
            }
            assert_eq!(analysis.slots[slot].atoms, atoms);
        }
        let before = analysis.revision;
        for prefix in [0, 9] {
            for slot in [first, second] {
                for atom in atoms {
                    let mut exact = TypeWorkBudget::with_limit(prefix + 1);
                    exact.charge(prefix).unwrap();
                    analysis.atom(slot, atom, &mut exact).unwrap();
                    assert_eq!(exact.used(), prefix + 1);
                }
            }
        }
        assert_eq!(analysis.revision, before);
        assert_eq!(analysis.atom_pairs.len(), 2 * atoms.len());
    }

    fn topology_graph() -> Graph {
        use crate::interface::{InterfaceId, MethodId, RequirementId, RequirementOwner};
        let source = crate::source::SourceFile::new("capture-topology.ash", "x").unwrap();
        let interface = InterfaceId::new(crate::module::ModuleId::from(source.id()), 0);
        let method = MethodId::new(interface, 0);
        let requirement = RequirementId::new(RequirementOwner::Global(BinderId::generated(950)), 0);
        let mut graph = graph(vec![
            Expr::Slot,
            Expr::Slot,
            Expr::Slot,
            Expr::Alias(0),
            Expr::Merge(vec![3, 2, 3]),
            Expr::Call {
                function: 4,
                arguments: vec![2],
                scalar: false,
                type_application: true,
            },
            Expr::Evidence {
                value: 5,
                bindings: vec![(requirement, method, 1), (requirement, method, 1)],
            },
            Expr::Function {
                parameters: Vec::new(),
                body: 1,
                captures: vec![6, 2, 6],
            },
            Expr::Evidence {
                value: 7,
                bindings: vec![(requirement, method, 1), (requirement, method, 1)],
            },
            Expr::Evidence {
                value: 7,
                bindings: vec![(requirement, method, 2)],
            },
            Expr::Function {
                parameters: Vec::new(),
                body: 1,
                captures: vec![2],
            },
        ]);
        // Repeated exact port keys remain repeated routes, not a set of links.
        graph.evidence = vec![((requirement, method), 0), ((requirement, method), 0)];
        graph
    }

    #[test]
    fn capture_topology_preserves_lifo_inert_visits_and_exact_evidence_owners() {
        let graph = topology_graph();
        let mut work = TypeWorkBudget::unbounded();
        let mut analysis = Analysis::new(&graph, &mut work).unwrap();
        let first = analysis.prepare_capture_topology(7, 8, &mut work).unwrap();
        assert_eq!(
            analysis.capture_topologies[first]
                .visits
                .iter()
                .map(|visit| visit.expression)
                .collect::<Vec<_>>(),
            vec![6, 1, 5, 2, 4, 3, 0]
        );
        assert_eq!(
            analysis.capture_topologies[first].bindings,
            vec![0, 1, 0, 1]
        );
        assert_eq!(
            analysis.capture_topologies[first]
                .visits
                .iter()
                .filter(|visit| visit.lexical)
                .map(|visit| visit.expression)
                .collect::<Vec<_>>(),
            vec![1, 2]
        );
        assert_eq!(
            analysis.capture_topologies[first].dictionary,
            PreparedDictionaryRoutes::Complete
        );
        let other = analysis.prepare_capture_topology(7, 9, &mut work).unwrap();
        assert_ne!(first, other);
        assert_eq!(analysis.capture_topologies[other].bindings, vec![0, 0]);
        assert_eq!(analysis.capture_topology_indices.len(), 2);
        let warm = work.used();
        assert_eq!(
            analysis.prepare_capture_topology(7, 8, &mut work).unwrap(),
            first
        );
        assert_eq!(work.used() - warm, 1);
        assert!(analysis.slots.is_empty());
        assert!(analysis.dependencies.entries.is_empty());
        assert_eq!(analysis.revision, 0);
        for (function, evidence) in [(8, 9), (7, 7), (usize::MAX, 8), (7, usize::MAX)] {
            assert!(matches!(
                analysis.prepare_capture_topology(function, evidence, &mut work),
                Err(Failure::Invalid)
            ));
            assert_eq!(analysis.capture_topology_indices.len(), 2);
        }
        for malformed_capture in [true, false] {
            let mut graph = topology_graph();
            if malformed_capture {
                let Expr::Function { captures, .. } = &mut graph.expressions[7] else {
                    unreachable!()
                };
                captures.push(usize::MAX);
            } else {
                let Expr::Evidence { bindings, .. } = &mut graph.expressions[8] else {
                    unreachable!()
                };
                bindings[0].2 = usize::MAX;
            }
            let mut rejected = Analysis::new(&graph, &mut work).unwrap();
            assert!(matches!(
                rejected.prepare_capture_topology(7, 8, &mut work),
                Err(Failure::Invalid)
            ));
            assert!(rejected.capture_topologies.is_empty());
            assert!(rejected.capture_topology_indices.is_empty());
            assert!(rejected.binding_indices.is_empty());
            assert!(rejected.slots.is_empty());
            assert!(rejected.dependencies.entries.is_empty());
            assert!(rejected.edge_pairs().is_empty());
            assert_eq!(rejected.revision, 0);
        }
    }

    #[test]
    fn capture_topology_refusals_are_atomic_at_every_cold_and_prefilled_budget_cut() {
        let graph = topology_graph();
        for prefilled in [false, true] {
            let setup = |work: &mut TypeWorkBudget| {
                let mut analysis = Analysis::new(&graph, work).unwrap();
                if prefilled {
                    analysis.prepare_capture_topology(10, 8, work).unwrap();
                }
                analysis
            };
            let mut analysis = setup(&mut TypeWorkBudget::unbounded());
            let mut measured = TypeWorkBudget::unbounded();
            let plan = analysis
                .prepare_capture_topology(7, 8, &mut measured)
                .unwrap();
            let exact = measured.used();
            // C=3 roots, P=12 pops, U=7 unique visits, J=2 port keys,
            // K=4 ordered routes, I=9 inert pushes. A cold binding index
            // contributes 2 + 3*B + Q = 9 (B=2, Q=1). The one
            // constructor-local bound-port set entry costs 2. The complete
            // dictionary projection adds B + 2*P + phase = 2 + 8 + 1 = 11.
            assert_eq!(exact, 75 + if prefilled { 0 } else { 9 });
            for prefix in [0, 11] {
                for available in 0..exact {
                    let mut refused = setup(&mut TypeWorkBudget::unbounded());
                    let mut short = TypeWorkBudget::with_limit(prefix + available);
                    short.charge(prefix).unwrap();
                    assert!(matches!(
                        refused.prepare_capture_topology(7, 8, &mut short),
                        Err(Failure::Resource)
                    ));
                    assert!(!refused.capture_topology_indices.contains_key(&(7, 8)));
                    assert_eq!(refused.capture_topologies.len(), usize::from(prefilled));
                    assert_eq!(refused.binding_indices.len(), usize::from(prefilled));
                    assert!(refused.slots.is_empty());
                    assert!(refused.indices.is_empty());
                    assert!(refused.pending.is_empty());
                    assert!(refused.dependencies.entries.is_empty());
                    assert!(refused.edge_pairs().is_empty());
                    assert!(refused.atom_pairs.is_empty());
                    assert_eq!(refused.revision, 0);
                    let mut retry = TypeWorkBudget::with_limit(prefix + exact);
                    retry.charge(prefix).unwrap();
                    let retry_plan = refused.prepare_capture_topology(7, 8, &mut retry).unwrap();
                    assert_eq!(retry.used(), prefix + exact);
                    assert_eq!(
                        refused.capture_topologies[retry_plan],
                        analysis.capture_topologies[plan]
                    );
                    assert_eq!(refused.binding_indices, analysis.binding_indices);
                    let mut warm = TypeWorkBudget::with_limit(prefix + 1);
                    warm.charge(prefix).unwrap();
                    assert_eq!(
                        refused.prepare_capture_topology(7, 8, &mut warm).unwrap(),
                        retry_plan
                    );
                    assert_eq!(warm.used(), prefix + 1);
                }
            }
        }
    }

    #[test]
    fn capture_topology_replay_keeps_fresh_contexts_readers_and_late_resource_atoms() {
        use crate::interface::{InterfaceId, MethodId, RequirementId, RequirementOwner};
        let source = crate::source::SourceFile::new("topology-contexts.ash", "x").unwrap();
        let interface = InterfaceId::new(crate::module::ModuleId::from(source.id()), 0);
        let method = MethodId::new(interface, 0);
        let requirement = RequirementId::new(RequirementOwner::Global(BinderId::generated(951)), 0);
        let mut graph = graph(vec![
            Expr::Slot,
            Expr::Slot,
            Expr::Slot,
            Expr::Slot,
            Expr::Scalar,
            Expr::Function {
                parameters: Vec::new(),
                body: 4,
                captures: vec![0, 2],
            },
            Expr::Evidence {
                value: 5,
                bindings: vec![(requirement, method, 1)],
            },
            Expr::Evidence {
                value: 5,
                bindings: vec![(requirement, method, 3)],
            },
        ]);
        let span = graph.sources[0];
        graph.expressions.push(Expr::Resource {
            success: None,
            failure: None,
            handle: 0,
            identity: 2,
            initializer: 4,
            body: 4,
            source: span,
        });
        graph.sources.push(span);
        graph.positions.insert(9, 8);
        graph.evidence = vec![((requirement, method), 0)];
        let mut work = TypeWorkBudget::unbounded();
        let mut analysis = Analysis::new(&graph, &mut work).unwrap();
        let creation_a = analysis
            .context(0, Transition::Root(50), &mut work)
            .unwrap();
        let creation_b = analysis
            .context(0, Transition::Root(51), &mut work)
            .unwrap();
        let arguments_a = analysis
            .context(0, Transition::Root(52), &mut work)
            .unwrap();
        let arguments_b = analysis
            .context(0, Transition::Root(53), &mut work)
            .unwrap();
        let specialized_a = analysis
            .context(arguments_a, Transition::Call(6), &mut work)
            .unwrap();
        let specialized_b = analysis
            .context(arguments_b, Transition::Call(6), &mut work)
            .unwrap();
        let reader_a = analysis.slot(3, creation_a, &mut work).unwrap();
        let reader_b = analysis.slot(3, creation_b, &mut work).unwrap();
        analysis.current = Some(reader_a);
        analysis
            .specialize_captures(5, creation_a, specialized_a, 6, arguments_a, &mut work)
            .unwrap();
        let edges = analysis.edge_pairs();
        let watches = analysis.watched_pairs();
        let revision = analysis.revision;
        let mut duplicate = TypeWorkBudget::with_limit(2);
        analysis
            .specialize_captures(5, creation_a, specialized_a, 6, arguments_a, &mut duplicate)
            .unwrap();
        assert_eq!(duplicate.used(), 2);
        assert_eq!(analysis.edge_pairs(), edges);
        assert_eq!(analysis.watched_pairs(), watches);
        assert_eq!(analysis.revision, revision);
        // Same topology under another reader must still install inert-slot and
        // argument/lexical watches; the reader coordinate cannot be omitted.
        let reader_c = analysis.slot(3, arguments_a, &mut work).unwrap();
        analysis.current = Some(reader_c);
        analysis
            .specialize_captures(5, creation_a, specialized_a, 6, arguments_a, &mut work)
            .unwrap();
        let destination = analysis.indices[&(0, specialized_a)];
        let lexical_destination = analysis.indices[&(2, specialized_a)];
        let argument = analysis.indices[&(1, arguments_a)];
        let lexical = analysis.indices[&(2, creation_a)];
        for dependency in [destination, lexical_destination, argument, lexical] {
            assert!(analysis.slots[dependency].readers.contains(&reader_c));
        }
        analysis.current = Some(reader_b);
        analysis
            .specialize_captures(5, creation_b, specialized_b, 6, arguments_b, &mut work)
            .unwrap();
        analysis.current = None;
        analysis.close(&mut work).unwrap();
        assert_eq!(analysis.capture_topologies.len(), 1);
        let destination_a = analysis.indices[&(0, specialized_a)];
        let destination_b = analysis.indices[&(0, specialized_b)];
        let argument_a = analysis.indices[&(1, arguments_a)];
        let argument_b = analysis.indices[&(1, arguments_b)];
        assert_ne!(destination_a, destination_b);
        assert_ne!(argument_a, argument_b);
        assert_eq!(
            analysis.slots[argument_a].readers,
            vec![reader_a, destination_a, reader_c]
        );
        assert_eq!(
            analysis.slots[argument_b].readers,
            vec![reader_b, destination_b]
        );
        analysis
            .atom(argument_a, Atom::Resource(8, creation_a), &mut work)
            .unwrap();
        analysis.close(&mut work).unwrap();
        assert_eq!(
            analysis.slots[destination_a].atoms,
            vec![Atom::Resource(8, creation_a)]
        );
        assert!(analysis.slots[destination_b].atoms.is_empty());
        analysis.atom(argument_b, Atom::Free, &mut work).unwrap();
        let lexical_b = analysis.indices[&(2, creation_b)];
        analysis.atom(lexical_b, Atom::Unknown, &mut work).unwrap();
        analysis.close(&mut work).unwrap();
        assert_eq!(analysis.slots[destination_b].atoms, vec![Atom::Free]);
        let lexical_destination_a = analysis.indices[&(2, specialized_a)];
        let lexical_destination_b = analysis.indices[&(2, specialized_b)];
        assert!(analysis.slots[lexical_destination_a].atoms.is_empty());
        assert_eq!(
            analysis.slots[lexical_destination_b].atoms,
            vec![Atom::Unknown]
        );
        let other = analysis
            .context(arguments_a, Transition::Call(7), &mut work)
            .unwrap();
        analysis
            .specialize_captures(5, creation_a, other, 7, arguments_a, &mut work)
            .unwrap();
        analysis.close(&mut work).unwrap();
        let other_destination = analysis.indices[&(0, other)];
        assert!(analysis.slots[other_destination].atoms.is_empty());
        let other_argument = analysis.indices[&(3, arguments_a)];
        analysis
            .atom(other_argument, Atom::Unknown, &mut work)
            .unwrap();
        analysis.close(&mut work).unwrap();
        assert_eq!(analysis.slots[other_destination].atoms, vec![Atom::Unknown]);
        assert_eq!(
            analysis.slots[destination_a].atoms,
            vec![Atom::Resource(8, creation_a)]
        );
        assert_eq!(analysis.capture_topologies.len(), 2);
        let fresh = Analysis::new(&graph, &mut work).unwrap();
        assert!(fresh.capture_topologies.is_empty());
        assert!(fresh.capture_topology_indices.is_empty());
        assert!(fresh.specialization_transfers.is_empty());
        assert!(fresh.callable_transfers.is_empty());
        let (focused, _) = analysis.focused(9, creation_a, &mut work).unwrap();
        assert!(focused.capture_topologies.is_empty());
        assert!(focused.capture_topology_indices.is_empty());
        assert!(focused.specialization_transfers.is_empty());
        assert!(focused.callable_transfers.is_empty());
    }

    #[test]
    fn specialization_transfer_completion_has_prefilled_refusal_and_fresh_retry_boundaries() {
        use crate::interface::{InterfaceId, MethodId, RequirementId, RequirementOwner};
        let source = crate::source::SourceFile::new("specialization-transfer.ash", "x").unwrap();
        let interface = InterfaceId::new(crate::module::ModuleId::from(source.id()), 0);
        let method = MethodId::new(interface, 0);
        let requirement = RequirementId::new(RequirementOwner::Global(BinderId::generated(953)), 0);
        let mut graph = graph(vec![
            Expr::Slot,
            Expr::Slot,
            Expr::Alias(0),
            Expr::Function {
                parameters: Vec::new(),
                body: 5,
                captures: vec![2, 4],
            },
            Expr::Slot,
            Expr::Scalar,
            Expr::Evidence {
                value: 3,
                bindings: vec![(requirement, method, 1)],
            },
        ]);
        graph.evidence = vec![((requirement, method), 0)];
        fn setup(graph: &Graph) -> (Analysis<'_>, usize, usize) {
            let mut work = TypeWorkBudget::unbounded();
            let mut analysis = Analysis::new(graph, &mut work).unwrap();
            analysis.prepare_capture_topology(3, 6, &mut work).unwrap();
            let specialized = analysis.context(0, Transition::Call(6), &mut work).unwrap();
            let reader = analysis.slot(5, 0, &mut work).unwrap();
            analysis.current = Some(reader);
            (analysis, specialized, reader)
        }
        let (mut measured, specialized, reader) = setup(&graph);
        let mut work = TypeWorkBudget::unbounded();
        measured
            .specialize_captures(3, 0, specialized, 6, 0, &mut work)
            .unwrap();
        let exact = work.used();
        let key = (Some(reader), 3, 0, specialized, 6, 0);
        assert!(measured.specialization_transfers.contains(&key));
        let edges = measured.edge_pairs();
        let watches = measured.watched_pairs();
        for prefix in [0, 9] {
            for available in 0..exact {
                let (mut failed, specialized, _) = setup(&graph);
                let mut short = TypeWorkBudget::with_limit(prefix + available);
                short.charge(prefix).unwrap();
                assert!(matches!(
                    failed.specialize_captures(3, 0, specialized, 6, 0, &mut short),
                    Err(Failure::Resource)
                ));
                assert!(
                    failed.specialization_transfers.is_empty(),
                    "refusal cannot publish completed links"
                );
            }
            // Entire rejected queries are discarded; no full-analysis rollback
            // is claimed for original partial slot/edge work before refusal.
            let (mut retried, specialized, _) = setup(&graph);
            let mut retry = TypeWorkBudget::with_limit(prefix + exact);
            retry.charge(prefix).unwrap();
            retried
                .specialize_captures(3, 0, specialized, 6, 0, &mut retry)
                .unwrap();
            assert_eq!(retry.used(), prefix + exact);
            assert_eq!(
                retried.specialization_transfers,
                measured.specialization_transfers
            );
            assert_eq!(retried.edge_pairs(), edges);
            assert_eq!(retried.watched_pairs(), watches);
            let revision = retried.revision;
            let mut duplicate = TypeWorkBudget::with_limit(prefix + 2);
            duplicate.charge(prefix).unwrap();
            retried
                .specialize_captures(3, 0, specialized, 6, 0, &mut duplicate)
                .unwrap();
            assert_eq!(duplicate.used(), prefix + 2);
            assert_eq!(retried.revision, revision);
            assert_eq!(retried.edge_pairs(), edges);
            assert_eq!(retried.watched_pairs(), watches);
        }
    }

    #[test]
    fn evidence_specialization_preserves_shared_ports_and_inert_aliases() {
        use crate::interface::{InterfaceId, MethodId, RequirementId, RequirementOwner};
        let source = crate::source::SourceFile::new("evidence-specialization.ash", "x").unwrap();
        let interface = InterfaceId::new(crate::module::ModuleId::from(source.id()), 0);
        let method = MethodId::new(interface, 0);
        let other_method = MethodId::new(interface, 1);
        let requirement = RequirementId::new(RequirementOwner::Global(BinderId::generated(900)), 0);
        let other_requirement =
            RequirementId::new(RequirementOwner::Global(BinderId::generated(901)), 0);
        let mut graph = graph(vec![
            Expr::Slot,
            Expr::Scalar,
            Expr::Unknown,
            Expr::Alias(0),
            Expr::Merge(vec![3]),
            Expr::Unknown,
            Expr::Evidence {
                value: 4,
                bindings: vec![
                    (requirement, method, 1),
                    (requirement, other_method, 2),
                    (other_requirement, other_method, 1),
                ],
            },
            Expr::Function {
                parameters: Vec::new(),
                body: 1,
                captures: vec![4, 5],
            },
        ]);
        graph.evidence = vec![
            ((requirement, method), 0),
            ((requirement, other_method), 0),
            ((other_requirement, method), 5),
        ];
        let mut measured = TypeWorkBudget::unbounded();
        Analysis::new(&graph, &mut measured).unwrap();
        assert!(matches!(
            Analysis::new(&graph, &mut TypeWorkBudget::with_limit(measured.used() - 1)),
            Err(Failure::Resource)
        ));
        let mut work = TypeWorkBudget::unbounded();
        let mut analysis = Analysis::new(&graph, &mut work).unwrap();
        let specialized = analysis.context(0, Transition::Call(4), &mut work).unwrap();
        analysis
            .specialize_captures(7, 0, specialized, 6, 0, &mut work)
            .unwrap();
        analysis.close(&mut work).unwrap();
        let shared = analysis.indices[&(0, specialized)];
        assert!(analysis.slots[shared].atoms.contains(&Atom::Free));
        assert!(
            analysis.slots[shared].atoms.contains(&Atom::Unknown),
            "distinct keys sharing a port must both survive"
        );
        let alias = analysis.indices[&(4, specialized)];
        assert!(
            analysis.slots[alias].atoms.contains(&Atom::Unknown),
            "inert alias traversal must reach the exact abstract port"
        );
        let lexical = analysis.indices[&(5, specialized)];
        assert_eq!(
            analysis.slots[lexical].atoms,
            vec![Atom::Unknown],
            "a different method identity cannot replace lexical captures"
        );
    }

    #[test]
    fn binding_indices_preserve_owner_keys_duplicates_and_refusal_atomicity() {
        use crate::interface::{InterfaceId, MethodId, RequirementId, RequirementOwner};
        let source = crate::source::SourceFile::new("binding-indices.ash", "x").unwrap();
        let interface = InterfaceId::new(crate::module::ModuleId::from(source.id()), 0);
        let method = MethodId::new(interface, 0);
        let other_method = MethodId::new(interface, 1);
        let requirement = RequirementId::new(RequirementOwner::Global(BinderId::generated(920)), 0);
        let other_requirement =
            RequirementId::new(RequirementOwner::Global(BinderId::generated(921)), 0);
        let graph = graph(vec![
            Expr::Slot,
            Expr::Scalar,
            Expr::Unknown,
            Expr::Evidence {
                value: 0,
                bindings: vec![
                    (requirement, method, 1),
                    (other_requirement, method, 2),
                    (requirement, method, 2),
                    (requirement, other_method, 1),
                    (requirement, method, 1),
                ],
            },
            Expr::Evidence {
                value: 0,
                bindings: vec![(requirement, method, 2)],
            },
        ]);
        let mut measured = Analysis::new(&graph, &mut TypeWorkBudget::unbounded()).unwrap();
        let mut work = TypeWorkBudget::unbounded();
        measured.prepare_binding_index(3, &mut work).unwrap();
        let exact = work.used();
        assert_eq!(
            measured.binding_indices[&3][&(requirement, method)],
            vec![0, 2, 4]
        );
        assert_eq!(
            measured.binding_indices[&3][&(other_requirement, method)],
            vec![1]
        );
        assert_eq!(
            measured.binding_indices[&3][&(requirement, other_method)],
            vec![3]
        );
        for prefix in [0, 9] {
            for available in 0..exact {
                let mut analysis = Analysis::new(&graph, &mut TypeWorkBudget::unbounded()).unwrap();
                let mut short = TypeWorkBudget::with_limit(prefix + available);
                short.charge(prefix).unwrap();
                assert!(matches!(
                    analysis.prepare_binding_index(3, &mut short),
                    Err(Failure::Resource)
                ));
                assert!(analysis.binding_indices.is_empty());
                assert!(analysis.slots.is_empty());
                assert!(analysis.pending.is_empty());
                assert_eq!(analysis.revision, 0);
                let mut retry = TypeWorkBudget::with_limit(prefix + exact);
                retry.charge(prefix).unwrap();
                analysis.prepare_binding_index(3, &mut retry).unwrap();
                assert_eq!(retry.used(), prefix + exact);
                assert_eq!(analysis.binding_indices, measured.binding_indices);
                let mut duplicate = TypeWorkBudget::with_limit(prefix + 1);
                duplicate.charge(prefix).unwrap();
                analysis.prepare_binding_index(3, &mut duplicate).unwrap();
                assert_eq!(duplicate.used(), prefix + 1);
                assert_eq!(analysis.binding_indices, measured.binding_indices);
            }
        }
        measured
            .prepare_binding_index(4, &mut TypeWorkBudget::unbounded())
            .unwrap();
        assert_eq!(
            measured.binding_indices[&4][&(requirement, method)],
            vec![0]
        );
        assert_eq!(
            measured.binding_indices[&3][&(requirement, method)],
            vec![0, 2, 4]
        );
        for invalid in [0, usize::MAX] {
            let before = measured.binding_indices.clone();
            assert!(matches!(
                measured.prepare_binding_index(invalid, &mut TypeWorkBudget::unbounded()),
                Err(Failure::Invalid)
            ));
            assert_eq!(measured.binding_indices, before);
        }
    }

    #[test]
    fn repeated_binding_lookup_work_depends_on_matches_instead_of_vector_width() {
        use crate::interface::{InterfaceId, MethodId, RequirementId, RequirementOwner};
        let source = crate::source::SourceFile::new("wide-binding-index.ash", "x").unwrap();
        let interface = InterfaceId::new(crate::module::ModuleId::from(source.id()), 0);
        let method = MethodId::new(interface, 0);
        let mut recurring = Vec::new();
        for width in [1, 96] {
            let bindings: Vec<_> = (0..width)
                .map(|position| {
                    (
                        RequirementId::new(
                            RequirementOwner::Global(BinderId::generated(930)),
                            position,
                        ),
                        method,
                        1,
                    )
                })
                .collect();
            let matched = bindings.last().unwrap().0;
            let mut graph = graph(vec![
                Expr::Slot,
                Expr::Scalar,
                Expr::Evidence { value: 0, bindings },
                Expr::Function {
                    parameters: Vec::new(),
                    body: 1,
                    captures: vec![0],
                },
            ]);
            graph.evidence = vec![((matched, method), 0)];
            let mut work = TypeWorkBudget::unbounded();
            let mut analysis = Analysis::new(&graph, &mut work).unwrap();
            let context = analysis.context(0, Transition::Call(2), &mut work).unwrap();
            analysis
                .specialize_captures(3, 0, context, 2, 0, &mut work)
                .unwrap();
            analysis.close(&mut work).unwrap();
            let before = work.used();
            for _ in 0..24 {
                analysis
                    .specialize_captures(3, 0, context, 2, 0, &mut work)
                    .unwrap();
            }
            recurring.push(work.used() - before);
            let destination = analysis.indices[&(0, context)];
            assert_eq!(analysis.slots[destination].atoms, vec![Atom::Free]);
        }
        assert_eq!(
            recurring[0], recurring[1],
            "unrelated immutable bindings must not be rescanned"
        );
    }

    #[test]
    fn completed_bound_ports_keep_duplicate_keys_extra_ports_and_late_owner_routes() {
        use crate::interface::{InterfaceId, MethodId, RequirementId, RequirementOwner};
        let source = crate::source::SourceFile::new("completed-bound-ports.ash", "x").unwrap();
        let interface = InterfaceId::new(crate::module::ModuleId::from(source.id()), 0);
        let method = MethodId::new(interface, 0);
        let key = |ordinal| {
            RequirementId::new(RequirementOwner::Global(BinderId::generated(960)), ordinal)
        };
        let mut original = graph(vec![
            Expr::Slot,
            Expr::Slot,
            Expr::Slot,
            Expr::Slot,
            Expr::Scalar,
            Expr::Function {
                parameters: Vec::new(),
                body: 4,
                captures: vec![0],
            },
            Expr::Evidence {
                value: 5,
                bindings: vec![
                    (key(0), method, 2),
                    (key(0), method, 2),
                    (key(1), method, 3),
                    (key(2), method, 2),
                ],
            },
        ]);
        let span = original.sources[0];
        original.expressions.push(Expr::Resource {
            success: None,
            failure: None,
            handle: 2,
            identity: 3,
            initializer: 4,
            body: 4,
            source: span,
        });
        original.sources.push(span);
        original.positions.insert(88, 7);
        // Two identical records and a different canonical key share one port;
        // the uncaptured port1 still needs the original dictionary transfer.
        original.evidence = vec![
            ((key(0), method), 0),
            ((key(0), method), 0),
            ((key(1), method), 0),
            ((key(0), method), 1),
        ];
        let ordered = original.evidence.clone();
        // No caller supplies a slot/kind association to the phase constructor.
        // Ordinary non-Evidence slots never create transfer stages, and a live
        // wrong-kind Closure in the actual Evidence input still fails closed.
        let mut invalid = Analysis::new(&original, &mut TypeWorkBudget::unbounded()).unwrap();
        let evidence_input = invalid
            .slot(6, 0, &mut TypeWorkBudget::unbounded())
            .unwrap();
        let wrong_slot = invalid
            .slot(0, 0, &mut TypeWorkBudget::unbounded())
            .unwrap();
        invalid.current = Some(wrong_slot);
        invalid
            .evaluate(wrong_slot, &mut TypeWorkBudget::unbounded())
            .unwrap();
        assert!(invalid.callable_transfers.is_empty());
        assert!(invalid.specialization_transfers.is_empty());
        let value_input = invalid
            .slot(5, 0, &mut TypeWorkBudget::unbounded())
            .unwrap();
        invalid
            .atom(
                value_input,
                Atom::Closure(0, 0),
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap();
        invalid.current = Some(evidence_input);
        assert!(matches!(
            invalid.evaluate(evidence_input, &mut TypeWorkBudget::unbounded()),
            Err(Failure::Invalid)
        ));
        assert!(invalid.callable_transfers.is_empty());
        assert!(invalid.specialization_transfers.is_empty());
        let mut work = TypeWorkBudget::unbounded();
        let mut analysis = Analysis::new(&original, &mut work).unwrap();
        let evidence = analysis.slot(6, 0, &mut work).unwrap();
        analysis.close(&mut work).unwrap();
        let specialized = analysis.context(0, Transition::Call(6), &mut work).unwrap();
        let plan = analysis.capture_topology_indices[&(5, 6)];
        assert_eq!(
            analysis.capture_topologies[plan].dictionary,
            PreparedDictionaryRoutes::Pending(vec![
                DictionaryObligation {
                    binding: 0,
                    evidence: 3
                },
                DictionaryObligation {
                    binding: 1,
                    evidence: 3
                },
            ])
        );
        assert_eq!(
            analysis.capture_topologies[plan].bindings,
            vec![0, 1, 0, 1, 2]
        );
        let covered = analysis.indices[&(0, specialized)];
        let extra = analysis.indices[&(1, specialized)];
        let a = analysis.indices[&(2, 0)];
        let b = analysis.indices[&(3, 0)];
        assert_eq!(analysis.slots[covered].edges, vec![a, b]);
        assert_eq!(analysis.slots[extra].edges, vec![a]);
        assert!(analysis.slots[covered].atoms.is_empty());
        assert!(analysis.slots[extra].atoms.is_empty());
        for source in [a, b] {
            assert!(analysis.slots[source].readers.contains(&evidence));
        }
        analysis.slot(7, 0, &mut work).unwrap();
        analysis.close(&mut work).unwrap();
        let owner = Atom::Resource(7, 0);
        assert_eq!(analysis.slots[covered].atoms, vec![owner]);
        assert_eq!(analysis.slots[extra].atoms, vec![owner]);
        assert_eq!(
            analysis.dependencies(evidence, &mut work).unwrap(),
            vec![owner]
        );

        let reader_context = analysis
            .context(0, Transition::Root(96), &mut work)
            .unwrap();
        let reader = analysis.slot(4, reader_context, &mut work).unwrap();
        analysis.current = Some(reader);
        analysis.evaluate(evidence, &mut work).unwrap();
        for dependency in [covered, extra, a, b] {
            assert!(analysis.slots[dependency].readers.contains(&reader));
        }
        analysis.current = None;
        analysis.evaluate(evidence, &mut work).unwrap();
        assert!(
            analysis
                .callable_transfers
                .contains(&(None, evidence, 5, 0))
        );
        assert_eq!(analysis.slots[covered].edges, vec![a, b]);
        assert_eq!(analysis.slots[extra].edges, vec![a]);

        // A new exact creation still completes its own specialization before
        // using bound-port membership; neither that creation nor a fresh
        // Evidence context may borrow another transfer's successful stamp.
        let creation = analysis
            .context(0, Transition::Root(97), &mut work)
            .unwrap();
        let value = analysis.indices[&(5, 0)];
        analysis
            .atom(value, Atom::Closure(5, creation), &mut work)
            .unwrap();
        analysis.close(&mut work).unwrap();
        assert!(analysis.specialization_transfers.contains(&(
            Some(evidence),
            5,
            creation,
            specialized,
            6,
            0
        )));
        let fresh_context = analysis
            .context(0, Transition::Root(98), &mut work)
            .unwrap();
        let fresh = analysis.slot(6, fresh_context, &mut work).unwrap();
        analysis.close(&mut work).unwrap();
        let fresh_specialized = analysis
            .context(fresh_context, Transition::Call(6), &mut work)
            .unwrap();
        let fresh_covered = analysis.indices[&(0, fresh_specialized)];
        let fresh_extra = analysis.indices[&(1, fresh_specialized)];
        assert_ne!(fresh_covered, covered);
        assert_ne!(fresh_extra, extra);
        assert!(analysis.slots[fresh_covered].atoms.is_empty());
        assert!(analysis.slots[fresh_extra].atoms.is_empty());
        let fresh_a = analysis.indices[&(2, fresh_context)];
        analysis.atom(fresh_a, Atom::Unknown, &mut work).unwrap();
        analysis.close(&mut work).unwrap();
        assert_eq!(analysis.slots[fresh_extra].atoms, vec![Atom::Unknown]);
        assert_eq!(analysis.slots[covered].atoms, vec![owner]);
        assert!(
            analysis
                .callable_transfers
                .contains(&(Some(fresh), fresh, 5, fresh_context))
        );
        // A single visit must recover the same loan after completed and new
        // Closure transfers and continue the original Unknown/nonclosure path.
        let third_creation = analysis
            .context(0, Transition::Root(99), &mut work)
            .unwrap();
        analysis.atom(value, Atom::Unknown, &mut work).unwrap();
        analysis.atom(value, Atom::Free, &mut work).unwrap();
        analysis
            .atom(value, Atom::Closure(5, third_creation), &mut work)
            .unwrap();
        analysis.close(&mut work).unwrap();
        assert!(analysis.callable_transfers.contains(&(
            Some(evidence),
            evidence,
            5,
            third_creation
        )));
        let unknown = analysis.slots[evidence]
            .atoms
            .iter()
            .position(|atom| *atom == Atom::Unknown)
            .unwrap();
        let free = analysis.slots[evidence]
            .atoms
            .iter()
            .position(|atom| *atom == Atom::Free)
            .unwrap();
        assert!(unknown < free);
        assert!(analysis.slots[evidence].atoms.contains(&owner));
        assert_eq!(original.evidence, ordered);
        let (focused, _) = analysis.focused(88, 0, &mut work).unwrap();
        assert!(focused.capture_topologies.is_empty());
        assert!(focused.capture_topology_indices.is_empty());
        assert!(focused.specialization_transfers.is_empty());
        assert!(focused.callable_transfers.is_empty());

        // Exercise the entire consumer transition, including residual routes
        // and output publication, at every charged refusal boundary. Original
        // partial setup is query-local; only a fresh query is retried.
        fn setup(graph: &Graph) -> (Analysis<'_>, usize) {
            let mut work = TypeWorkBudget::unbounded();
            let mut analysis = Analysis::new(graph, &mut work).unwrap();
            let evidence = analysis.slot(6, 0, &mut work).unwrap();
            let value = analysis.slot(5, 0, &mut work).unwrap();
            analysis
                .atom(value, Atom::Closure(5, 0), &mut work)
                .unwrap();
            analysis.current = Some(evidence);
            (analysis, evidence)
        }
        let (mut measured, source) = setup(&original);
        let mut measure = TypeWorkBudget::unbounded();
        measured.evaluate(source, &mut measure).unwrap();
        let exact = measure.used();
        assert!(
            measured
                .callable_transfers
                .contains(&(Some(source), source, 5, 0))
        );
        for prefix in [0, 9] {
            for available in 0..exact {
                let (mut refused, source) = setup(&original);
                let mut short = TypeWorkBudget::with_limit(prefix + available);
                short.charge(prefix).unwrap();
                assert!(matches!(
                    refused.evaluate(source, &mut short),
                    Err(Failure::Resource)
                ));
                assert!(
                    refused.callable_transfers.is_empty(),
                    "no ready closure stamp before complete output publication"
                );
            }
            let (mut retried, source) = setup(&original);
            let mut retry = TypeWorkBudget::with_limit(prefix + exact);
            retry.charge(prefix).unwrap();
            retried.evaluate(source, &mut retry).unwrap();
            assert_eq!(retry.used(), prefix + exact);
            assert_eq!(retried.callable_transfers, measured.callable_transfers);
            assert_eq!(
                retried.specialization_transfers,
                measured.specialization_transfers
            );
            assert_eq!(retried.edge_pairs(), measured.edge_pairs());
            assert_eq!(retried.watched_pairs(), measured.watched_pairs());
            assert_eq!(retried.slots[source].atoms, measured.slots[source].atoms);
        }
    }

    #[test]
    fn indexed_bindings_keep_late_notifications_and_distinct_argument_contexts() {
        use crate::interface::{InterfaceId, MethodId, RequirementId, RequirementOwner};
        let source = crate::source::SourceFile::new("binding-notifications.ash", "x").unwrap();
        let interface = InterfaceId::new(crate::module::ModuleId::from(source.id()), 0);
        let method = MethodId::new(interface, 0);
        let requirement = RequirementId::new(RequirementOwner::Global(BinderId::generated(922)), 0);
        let mut graph = graph(vec![
            Expr::Slot,
            Expr::Slot,
            Expr::Slot,
            Expr::Evidence {
                value: 0,
                bindings: vec![
                    (requirement, method, 1),
                    (requirement, method, 2),
                    (requirement, method, 1),
                ],
            },
            Expr::Function {
                parameters: Vec::new(),
                body: 1,
                captures: vec![0],
            },
        ]);
        graph.evidence = vec![((requirement, method), 0)];
        let mut work = TypeWorkBudget::unbounded();
        let mut analysis = Analysis::new(&graph, &mut work).unwrap();
        let first = analysis.context(0, Transition::Call(1), &mut work).unwrap();
        let second = analysis.context(0, Transition::Call(2), &mut work).unwrap();
        analysis
            .specialize_captures(4, 0, first, 3, 0, &mut work)
            .unwrap();
        analysis.close(&mut work).unwrap();
        let destination = analysis.indices[&(0, first)];
        let one = analysis.indices[&(1, 0)];
        let two = analysis.indices[&(2, 0)];
        assert_eq!(analysis.slots[destination].edges, vec![one, two]);
        assert!(analysis.slots[destination].atoms.is_empty());
        assert!(analysis.slots[one].readers.contains(&destination));
        assert!(analysis.slots[two].readers.contains(&destination));
        analysis.atom(one, Atom::Unknown, &mut work).unwrap();
        analysis.atom(two, Atom::Free, &mut work).unwrap();
        analysis.close(&mut work).unwrap();
        assert_eq!(
            analysis.slots[destination].atoms,
            vec![Atom::Unknown, Atom::Free]
        );
        // Reuse only static positions. Fresh argument slots retain their context.
        analysis
            .specialize_captures(4, 0, second, 3, first, &mut work)
            .unwrap();
        analysis.close(&mut work).unwrap();
        let other = analysis.indices[&(0, second)];
        assert!(analysis.slots[other].atoms.is_empty());
        let later = analysis.indices[&(1, first)];
        assert_ne!(one, later);
        analysis.atom(later, Atom::Free, &mut work).unwrap();
        analysis.close(&mut work).unwrap();
        assert_eq!(analysis.slots[other].atoms, vec![Atom::Free]);
        assert_eq!(
            analysis.slots[destination].atoms,
            vec![Atom::Unknown, Atom::Free]
        );
        assert_eq!(analysis.binding_indices.len(), 1);
    }

    fn evidence_lookup_fixture() -> (Graph, [EvidenceKey; 3]) {
        use crate::interface::{InterfaceId, MethodId, RequirementId, RequirementOwner};
        let mut graph = graph(vec![Expr::Slot, Expr::Slot, Expr::Scalar]);
        let interface =
            InterfaceId::new(crate::module::ModuleId::from(graph.sources[0].source()), 0);
        let method = MethodId::new(interface, 0);
        let other_method = MethodId::new(interface, 1);
        let requirement = RequirementId::new(RequirementOwner::Global(BinderId::generated(710)), 0);
        let other = RequirementId::new(RequirementOwner::Global(BinderId::generated(711)), 0);
        let keys = [
            (requirement, method),
            (other, method),
            (requirement, other_method),
        ];
        graph.evidence = vec![(keys[0], 0), (keys[0], 1), (keys[1], 2)];
        (graph, keys)
    }

    #[test]
    fn evidence_lookup_preserves_first_original_imported_port_and_refuses_invalid_ordinals() {
        let (mut original, keys) = evidence_lookup_fixture();
        let source = original.sources[0];
        let mut work = TypeWorkBudget::unbounded();
        assert_eq!(
            original
                .evidence_slot(keys[1].0, keys[1].1, source, &mut work)
                .unwrap(),
            2
        );
        assert_eq!(
            original
                .evidence_slot(keys[0].0, keys[0].1, source, &mut work)
                .unwrap(),
            0
        );
        let mut imported = graph(vec![Expr::Slot, Expr::Slot]);
        imported.evidence = vec![(keys[0], 1), (keys[2], 0), (keys[2], 1)];
        let offset = original.import_graph(&imported, 0, 0, &mut work).unwrap();
        assert_eq!(offset, 3);
        let ordered = vec![
            (keys[0], 0),
            (keys[0], 1),
            (keys[1], 2),
            (keys[0], offset + 1),
            (keys[2], offset),
            (keys[2], offset + 1),
        ];
        assert_eq!(original.evidence, ordered);
        assert_eq!(
            original
                .evidence_slot(keys[0].0, keys[0].1, source, &mut work)
                .unwrap(),
            0
        );
        assert_eq!(
            original
                .evidence_slot(keys[2].0, keys[2].1, source, &mut work)
                .unwrap(),
            offset
        );
        assert_eq!(
            original.evidence, ordered,
            "lookup preserves every imported duplicate"
        );
        // A corrupted scalar table cannot replace original canonical identity.
        original.evidence_index[0].first.insert(keys[0], 2);
        assert!(matches!(
            original.evidence_slot(keys[0].0, keys[0].1, source, &mut work),
            Err(Failure::Invalid)
        ));
        assert_eq!(original.evidence, ordered);
        let (mut invalid, keys) = evidence_lookup_fixture();
        invalid.evidence[0].1 = usize::MAX;
        let source = invalid.sources[0];
        assert!(matches!(
            invalid.evidence_slot(keys[0].0, keys[0].1, source, &mut work),
            Err(Failure::Invalid)
        ));
        assert!(
            invalid.evidence_index.is_empty(),
            "invalid original index never publishes a prefix"
        );
    }

    #[test]
    fn evidence_lookup_charges_cold_imported_and_append_boundaries_with_prefilled_retry() {
        for sync in [false, true] {
            for prefix in [0, 9] {
                let total = if sync { 22 } else { 13 };
                for cut in 0..=total {
                    let (mut candidate, keys) = evidence_lookup_fixture();
                    let source = candidate.sources[0];
                    if sync {
                        candidate
                            .evidence_slot(
                                keys[0].0,
                                keys[0].1,
                                source,
                                &mut TypeWorkBudget::unbounded(),
                            )
                            .unwrap();
                        let mut imported = graph(vec![Expr::Slot, Expr::Slot]);
                        imported.evidence = vec![(keys[0], 1), (keys[2], 0), (keys[2], 1)];
                        candidate
                            .import_graph(&imported, 0, 0, &mut TypeWorkBudget::unbounded())
                            .unwrap();
                    }
                    let ordered = candidate.evidence.clone();
                    let expressions = candidate.expressions.len();
                    let mut work = TypeWorkBudget::with_limit(prefix + cut);
                    work.charge(prefix).unwrap();
                    let result = candidate.evidence_slot(keys[0].0, keys[0].1, source, &mut work);
                    if cut == total {
                        assert_eq!(result.unwrap(), 0);
                    } else {
                        assert!(matches!(result, Err(Failure::Resource)));
                    }
                    assert_eq!(candidate.evidence, ordered);
                    assert_eq!(candidate.expressions.len(), expressions);
                    if let Some(index) = candidate.evidence_index.first() {
                        assert!(index.prefix <= ordered.len());
                        for (key, ordinal) in &index.first {
                            assert_eq!(
                                ordered[..index.prefix]
                                    .iter()
                                    .position(|(original, _)| original == key),
                                Some(*ordinal)
                            );
                        }
                    }
                    if cut == total {
                        assert_eq!(work.used(), prefix + total);
                        let mut warm = TypeWorkBudget::unbounded();
                        assert_eq!(
                            candidate
                                .evidence_slot(keys[0].0, keys[0].1, source, &mut warm)
                                .unwrap(),
                            0
                        );
                        assert_eq!(warm.used(), 3);
                    }
                }
                let (mut retry, keys) = evidence_lookup_fixture();
                let source = retry.sources[0];
                if sync {
                    retry
                        .evidence_slot(
                            keys[0].0,
                            keys[0].1,
                            source,
                            &mut TypeWorkBudget::unbounded(),
                        )
                        .unwrap();
                    let mut imported = graph(vec![Expr::Slot, Expr::Slot]);
                    imported.evidence = vec![(keys[0], 1), (keys[2], 0), (keys[2], 1)];
                    retry
                        .import_graph(&imported, 0, 0, &mut TypeWorkBudget::unbounded())
                        .unwrap();
                }
                let mut exact = TypeWorkBudget::with_limit(prefix + total);
                exact.charge(prefix).unwrap();
                assert_eq!(
                    retry
                        .evidence_slot(keys[0].0, keys[0].1, source, &mut exact)
                        .unwrap(),
                    0
                );
                assert_eq!(exact.used(), prefix + total);
            }
        }
        for prefix in [0, 9] {
            for cut in 0..=6 {
                let (mut candidate, keys) = evidence_lookup_fixture();
                let source = candidate.sources[0];
                candidate
                    .evidence_slot(
                        keys[0].0,
                        keys[0].1,
                        source,
                        &mut TypeWorkBudget::unbounded(),
                    )
                    .unwrap();
                let ordered = candidate.evidence.clone();
                let first = candidate.evidence_index[0].first.clone();
                let mut work = TypeWorkBudget::with_limit(prefix + cut);
                work.charge(prefix).unwrap();
                let result = candidate.evidence_slot(keys[2].0, keys[2].1, source, &mut work);
                if cut < 6 {
                    assert!(matches!(result, Err(Failure::Resource)));
                    assert_eq!(candidate.evidence, ordered);
                    assert_eq!(candidate.expressions.len(), 3);
                    assert_eq!(candidate.sources.len(), 3);
                    assert_eq!(candidate.evidence_index[0].first, first);
                    assert_eq!(candidate.evidence_index[0].prefix, 3);
                } else {
                    assert_eq!(result.unwrap(), 3);
                    assert_eq!(
                        candidate.evidence,
                        ordered
                            .into_iter()
                            .chain([(keys[2], 3)])
                            .collect::<Vec<_>>()
                    );
                    assert_eq!(candidate.evidence_index[0].first[&keys[2]], 3);
                    assert_eq!(candidate.evidence_index[0].prefix, 4);
                    assert_eq!(work.used(), prefix + 6);
                }
            }
            let (mut retry, keys) = evidence_lookup_fixture();
            let source = retry.sources[0];
            retry
                .evidence_slot(
                    keys[0].0,
                    keys[0].1,
                    source,
                    &mut TypeWorkBudget::unbounded(),
                )
                .unwrap();
            let mut exact = TypeWorkBudget::with_limit(prefix + 6);
            exact.charge(prefix).unwrap();
            assert_eq!(
                retry
                    .evidence_slot(keys[2].0, keys[2].1, source, &mut exact)
                    .unwrap(),
                3
            );
            assert_eq!(exact.used(), prefix + 6);
        }
    }

    #[test]
    fn evidence_routes_every_matching_port_with_exact_canonical_identity() {
        use crate::interface::{InterfaceId, MethodId, RequirementId, RequirementOwner};
        let source = crate::source::SourceFile::new("evidence-routes.ash", "x").unwrap();
        let interface = InterfaceId::new(crate::module::ModuleId::from(source.id()), 0);
        let method = MethodId::new(interface, 0);
        let requirement = RequirementId::new(RequirementOwner::Global(BinderId::generated(902)), 0);
        let other_requirement =
            RequirementId::new(RequirementOwner::Global(BinderId::generated(903)), 0);
        let mut graph = graph(vec![
            Expr::Slot,
            Expr::Slot,
            Expr::Scalar,
            Expr::Unknown,
            Expr::Function {
                parameters: Vec::new(),
                body: 2,
                captures: vec![0, 3],
            },
            Expr::Evidence {
                value: 4,
                bindings: vec![(requirement, method, 2)],
            },
        ]);
        graph.evidence = vec![
            ((requirement, method), 0),
            ((requirement, method), 1),
            ((other_requirement, method), 3),
        ];
        let mut work = TypeWorkBudget::unbounded();
        let mut analysis = Analysis::new(&graph, &mut work).unwrap();
        let result = analysis.slot(5, 0, &mut work).unwrap();
        analysis.close(&mut work).unwrap();
        let specialized = analysis.slots[result]
            .atoms
            .iter()
            .find_map(|atom| match atom {
                Atom::Closure(4, context) => Some(*context),
                _ => None,
            })
            .expect("evidence application preserves the specialized closure");
        for port in [0, 1] {
            let target = analysis.indices[&(port, specialized)];
            assert_eq!(
                analysis.slots[target].atoms,
                vec![Atom::Free],
                "all original ports for the selected canonical key receive the argument"
            );
        }
        let unmatched = analysis.indices[&(3, specialized)];
        assert_eq!(
            analysis.slots[unmatched].atoms,
            vec![Atom::Unknown],
            "the same method under another requirement retains its lexical value"
        );
        drop(analysis);
        // No captures establish no installed dictionary routes. Both required
        // global ports still receive their original argument in a fresh query.
        let Expr::Function { captures, .. } = &mut graph.expressions[4] else {
            unreachable!()
        };
        captures.clear();
        let mut empty = Analysis::new(&graph, &mut work).unwrap();
        let result = empty.slot(5, 0, &mut work).unwrap();
        empty.close(&mut work).unwrap();
        let specialized = empty.slots[result]
            .atoms
            .iter()
            .find_map(|atom| match atom {
                Atom::Closure(4, context) => Some(*context),
                _ => None,
            })
            .unwrap();
        let plan = empty.capture_topology_indices[&(4, 5)];
        assert!(empty.capture_topologies[plan].visits.is_empty());
        assert_eq!(
            empty.capture_topologies[plan].dictionary,
            PreparedDictionaryRoutes::Pending(vec![
                DictionaryObligation {
                    binding: 0,
                    evidence: 0
                },
                DictionaryObligation {
                    binding: 0,
                    evidence: 1
                },
            ])
        );
        for port in [0, 1] {
            let target = empty.indices[&(port, specialized)];
            assert_eq!(empty.slots[target].atoms, vec![Atom::Free]);
        }
    }

    #[test]
    fn provider_invocation_charges_wide_target_lookup() {
        let invocation_cost = |width| {
            let mut graph = provider_typed_capture_graph_for_test(None, false, false);
            for target in 1..width {
                let expression = graph.expressions.len();
                graph.expressions.push(Expr::Function {
                    parameters: vec![2],
                    body: 3,
                    captures: Vec::new(),
                });
                graph.sources.push(graph.sources[0]);
                graph.targets.insert(expression, target);
            }
            let mut source_work = TypeWorkBudget::unbounded();
            graph.provider_source(0, &mut source_work).unwrap();
            assert_eq!(source_work.used(), width);
            assert!(matches!(
                graph.provider_source(0, &mut TypeWorkBudget::with_limit(width - 1)),
                Err(Failure::Resource)
            ));
            let mut analysis = graph
                .start_provider(&mut TypeWorkBudget::unbounded())
                .unwrap();
            let mut work = TypeWorkBudget::unbounded();
            analysis.provider_invoke(0, &mut work).unwrap();
            work.used()
        };
        assert_eq!(invocation_cost(65) - invocation_cost(1), 64);
    }

    #[test]
    fn cut_inputs_exclude_pending_local_binders_with_exact_fresh_retry() {
        let graph = graph(vec![
            Expr::Slot,
            Expr::Slot,
            Expr::Scalar,
            Expr::Function {
                parameters: Vec::new(),
                body: 2,
                captures: vec![0, 1],
            },
            Expr::Bind {
                binder: 1,
                initializer: 2,
                body: 3,
            },
        ]);
        let mut measured = TypeWorkBudget::unbounded();
        assert_eq!(graph.free_inputs(4, &mut measured).unwrap(), vec![0]);
        let exact = measured.used();
        assert!(matches!(
            graph.free_inputs(4, &mut TypeWorkBudget::with_limit(exact - 1)),
            Err(Failure::Resource)
        ));
        let mut retry = TypeWorkBudget::with_limit(exact);
        assert_eq!(graph.free_inputs(4, &mut retry).unwrap(), vec![0]);
        assert_eq!(retry.used(), exact);
        assert_eq!(
            graph
                .free_inputs(3, &mut TypeWorkBudget::unbounded())
                .unwrap(),
            vec![1, 0],
            "a prior binding is an input to a later cut"
        );
    }

    #[test]
    fn wide_expression_copies_preflight_outer_staging_and_retry_exactly() {
        const WIDTH: usize = 128;
        for expression in [
            Expr::Match {
                scrutinee: 0,
                arms: (0..WIDTH).map(|_| (Vec::new(), 0)).collect(),
            },
            Expr::Handler {
                body: 0,
                clauses: (0..WIDTH)
                    .map(|_| DataClause {
                        input: 0,
                        bindings: Vec::new(),
                        body: 0,
                        captures: Vec::new(),
                    })
                    .collect(),
            },
        ] {
            for limit in [0, WIDTH] {
                let mut budget = TypeWorkBudget::with_limit(limit);
                assert!(matches!(
                    expression.copy(0, &mut budget),
                    Err(Failure::Resource)
                ));
                assert_eq!(budget.used(), usize::from(limit != 0));
            }
            let mut measured = TypeWorkBudget::unbounded();
            expression.copy(0, &mut measured).unwrap();
            assert!(matches!(
                expression.copy(0, &mut TypeWorkBudget::with_limit(measured.used() - 1)),
                Err(Failure::Resource)
            ));
            for _ in 0..2 {
                expression
                    .copy(0, &mut TypeWorkBudget::with_limit(measured.used()))
                    .unwrap();
            }
        }
    }

    #[test]
    fn wide_call_staging_precedes_argument_slots_and_retries_exactly() {
        const WIDTH: usize = 128;
        let graph = graph(vec![
            Expr::Unknown,
            Expr::Slot,
            Expr::Call {
                function: 0,
                arguments: vec![1; WIDTH],
                scalar: true,
                type_application: false,
            },
        ]);
        let run = |early: bool, budget: &mut TypeWorkBudget| {
            let mut analysis = Analysis::new(&graph, &mut TypeWorkBudget::unbounded()).unwrap();
            let function = analysis
                .slot(0, 0, &mut TypeWorkBudget::unbounded())
                .unwrap();
            analysis
                .atom(function, Atom::Unknown, &mut TypeWorkBudget::unbounded())
                .unwrap();
            let result = analysis
                .slot(2, 0, &mut TypeWorkBudget::unbounded())
                .unwrap();
            let outcome = analysis.evaluate(result, budget);
            if early {
                assert!(
                    !analysis.indices.contains_key(&(1, 0)),
                    "staging must fail before an argument slot is created"
                );
            }
            outcome
        };
        for limit in [0, WIDTH] {
            assert!(matches!(
                run(true, &mut TypeWorkBudget::with_limit(limit)),
                Err(Failure::Resource)
            ));
        }
        let mut measured = TypeWorkBudget::unbounded();
        run(false, &mut measured).unwrap();
        assert!(matches!(
            run(false, &mut TypeWorkBudget::with_limit(measured.used() - 1)),
            Err(Failure::Resource)
        ));
        for _ in 0..2 {
            run(false, &mut TypeWorkBudget::with_limit(measured.used())).unwrap();
        }
    }

    #[test]
    fn wide_payload_and_dependency_staging_preflight_and_retry_exactly() {
        const WIDTH: usize = 128;
        for shape in 0..3 {
            let mut graph = graph(vec![Expr::Scalar, Expr::Scalar, Expr::Scalar, Expr::Scalar]);
            graph.expressions[2] = match shape {
                0 => Expr::Call {
                    function: 0,
                    arguments: vec![1; WIDTH],
                    scalar: true,
                    type_application: false,
                },
                1 => Expr::Tuple(vec![1; WIDTH]),
                _ => Expr::Function {
                    parameters: Vec::new(),
                    body: 0,
                    captures: vec![1; WIDTH],
                },
            };
            graph.expressions[3] = Expr::Resource {
                success: None,
                failure: None,
                handle: 0,
                identity: 1,
                initializer: 0,
                body: 0,
                source: graph.sources[3],
            };
            graph.positions.insert(3, 3);
            let run = |budget: &mut TypeWorkBudget| {
                let mut analysis = Analysis::new(&graph, &mut TypeWorkBudget::unbounded()).unwrap();
                let result = analysis
                    .slot(2, 0, &mut TypeWorkBudget::unbounded())
                    .unwrap();
                analysis.close(&mut TypeWorkBudget::unbounded()).unwrap();
                if shape == 0 {
                    analysis.check_payload(result, 3, 0, budget)
                } else {
                    analysis.dependencies(result, budget).map(|_| ())
                }
            };
            // The singleton root costs two; its pop and borrowed atom visit cost one each.
            let prefix = if shape == 0 { 0 } else { 4 };
            for limit in [0, prefix + WIDTH - 1] {
                let mut budget = TypeWorkBudget::with_limit(limit);
                assert!(matches!(run(&mut budget), Err(Failure::Resource)));
                assert_eq!(budget.used(), if limit == 0 { 0 } else { prefix });
            }
            let mut measured = TypeWorkBudget::unbounded();
            run(&mut measured).unwrap();
            assert!(matches!(
                run(&mut TypeWorkBudget::with_limit(measured.used() - 1)),
                Err(Failure::Resource)
            ));
            for _ in 0..2 {
                run(&mut TypeWorkBudget::with_limit(measured.used())).unwrap();
            }
        }
    }

    #[test]
    fn conditional_handler_import_preserves_per_request_pattern_and_resume_operands() {
        let mut actual = graph(vec![
            Expr::Slot,
            Expr::Request {
                operand: 0,
                scalar: false,
            },
            Expr::Slot,
            Expr::Request {
                operand: 2,
                scalar: false,
            },
            Expr::Scalar,
        ]);
        actual.positions.extend([(10, 4), (11, 1), (12, 3)]);
        let mut original = graph(vec![
            Expr::Slot,
            Expr::Slot,
            Expr::Alias(0),
            Expr::Unknown,
            Expr::Handler {
                body: 3,
                clauses: vec![DataClause {
                    input: 1,
                    bindings: vec![(0, 1)],
                    body: 2,
                    captures: vec![],
                }],
            },
            Expr::Resume { operand: 0 },
        ]);
        original.positions.extend([(1, 2), (2, 5)]);
        let mut budget = TypeWorkBudget::unbounded();
        let handler = actual
            .import_conditional_handler(&original, 4, 10, 50, 0, 20, &mut budget)
            .unwrap();
        let Expr::Handler { body, clauses } = &actual.expressions[handler] else {
            panic!("handler");
        };
        assert_eq!(*body, 4);
        let clause_body = clauses[0].body;
        let mut analysis = Analysis::new(&actual, &mut budget).unwrap();
        let first = analysis.slot(0, 0, &mut budget).unwrap();
        let second = analysis.slot(2, 0, &mut budget).unwrap();
        let a = Atom::Resource(99, 0);
        let b = Atom::Resource(100, 0);
        analysis.atom(first, a, &mut budget).unwrap();
        analysis.atom(second, b, &mut budget).unwrap();
        let first = analysis.port(11, 0, &mut budget).unwrap();
        let second = analysis.port(12, 0, &mut budget).unwrap();
        let first_context = analysis.dispatch(first, 50, 0, 0, 0, &mut budget).unwrap();
        let second_context = analysis.dispatch(second, 50, 0, 0, 0, &mut budget).unwrap();
        assert_ne!(first_context, second_context);
        let first_body = analysis
            .slot(clause_body, first_context, &mut budget)
            .unwrap();
        let second_body = analysis
            .slot(clause_body, second_context, &mut budget)
            .unwrap();
        analysis
            .resume(first, 22, first_context, 50, 0, &mut budget)
            .unwrap();
        analysis
            .resume(second, 22, second_context, 50, 0, &mut budget)
            .unwrap();
        analysis.close(&mut budget).unwrap();
        let first_dependencies = analysis.dependencies(first_body, &mut budget).unwrap();
        let second_dependencies = analysis.dependencies(second_body, &mut budget).unwrap();
        assert!(first_dependencies.contains(&a));
        assert!(!first_dependencies.contains(&b));
        assert!(second_dependencies.contains(&b));
        assert!(!second_dependencies.contains(&a));
        assert!(
            analysis
                .dependencies(first, &mut budget)
                .unwrap()
                .contains(&a)
        );
        assert!(
            analysis
                .dependencies(second, &mut budget)
                .unwrap()
                .contains(&b)
        );
    }

    #[test]
    fn conditional_handler_import_refuses_unknown_body_and_control_port_collisions() {
        let mut original = graph(vec![
            Expr::Unknown,
            Expr::Handler {
                body: 0,
                clauses: vec![],
            },
        ]);
        original.positions.insert(1, 0);
        for (original_handler, body, handler, offset) in [
            (0, 10, 50, 20),
            (1, 99, 50, 20),
            (1, 10, 21, 20),
            (1, 10, 10, 20),
        ] {
            let mut actual = graph(vec![Expr::Scalar]);
            actual.positions.insert(10, 0);
            assert!(matches!(
                actual.import_conditional_handler(
                    &original,
                    original_handler,
                    body,
                    handler,
                    0,
                    offset,
                    &mut TypeWorkBudget::unbounded()
                ),
                Err(Failure::Invalid)
            ));
            assert_eq!(actual.expressions.len(), 1);
        }
        let run = |budget: &mut TypeWorkBudget| {
            let mut actual = graph(vec![Expr::Scalar]);
            actual.positions.insert(10, 0);
            actual.import_conditional_handler(&original, 1, 10, 50, 0, 20, budget)
        };
        let mut measured = TypeWorkBudget::unbounded();
        run(&mut measured).unwrap();
        assert!(matches!(
            run(&mut TypeWorkBudget::with_limit(measured.used() - 1)),
            Err(Failure::Resource)
        ));
        run(&mut TypeWorkBudget::with_limit(measured.used())).unwrap();
    }

    #[test]
    fn wide_pattern_staging_precedes_graph_mutation_and_retries_exactly() {
        const WIDTH: usize = 128;
        let fixture = graph(vec![Expr::Scalar]);
        let origin = crate::source::Origin::Source(fixture.sources[0]);
        let pattern = CorePattern::new(
            Type::Tuple(vec![Type::Unit; WIDTH].into_boxed_slice()),
            origin.clone(),
            CorePatternKind::Tuple(
                (0..WIDTH)
                    .map(|_| {
                        CorePattern::new(Type::Unit, origin.clone(), CorePatternKind::Wildcard)
                    })
                    .collect(),
            ),
        );
        let run = |early: bool, budget: &mut TypeWorkBudget| {
            let mut graph = graph(vec![Expr::Scalar]);
            let mut symbols = HashMap::new();
            let outcome = graph.pattern(&pattern, 0, &mut symbols, budget);
            if early {
                assert_eq!(graph.expressions.len(), 1);
                assert!(symbols.is_empty());
            }
            outcome.map(|_| ())
        };
        for limit in [0, WIDTH + 2] {
            let mut budget = TypeWorkBudget::with_limit(limit);
            assert!(matches!(run(true, &mut budget), Err(Failure::Resource)));
            assert_eq!(budget.used(), if limit == 0 { 0 } else { 3 });
        }
        let mut measured = TypeWorkBudget::unbounded();
        run(false, &mut measured).unwrap();
        assert!(matches!(
            run(false, &mut TypeWorkBudget::with_limit(measured.used() - 1)),
            Err(Failure::Resource)
        ));
        for _ in 0..2 {
            run(false, &mut TypeWorkBudget::with_limit(measured.used())).unwrap();
        }
    }

    #[test]
    fn wide_handler_build_preflights_clauses_and_retries_exactly() {
        use crate::core::{
            data::CoreMatchArm,
            dialect::{ArenaId, DialectId},
            effect::{EffectClause, EffectExprKind, EffectOperationFamily, HandlerId, HandlerNode},
        };
        use crate::{
            resolved::ResumeId,
            source::Origin,
            types::{EffectId, EffectInstance, EffectRow, OperationId},
        };
        const WIDTH: usize = 128;
        let fixture = graph(vec![Expr::Scalar, Expr::Scalar]);
        let span = fixture.sources[0];
        let origin = Origin::Source(span);
        let node = crate::core::NodeId::new(ArenaId::new(0), 0);
        let effect = EffectId::new(crate::module::ModuleId::new(0), 0);
        let clauses = (0..WIDTH)
            .map(|ordinal| {
                EffectClause::new(
                    OperationId::new(effect, ordinal as u32),
                    ResumeId::new(ordinal as u32),
                    CoreMatchArm::new(
                        CorePattern::new(Type::Unit, origin.clone(), CorePatternKind::Wildcard),
                        node,
                        origin.clone(),
                    ),
                )
            })
            .collect();
        let nodes = vec![
            StoredNode::<EffectOperationFamily> {
                dialect: DialectId::named(EffectOperationFamily::DIALECT_NAME),
                ty: Type::Unit,
                effects: EffectRow::empty(),
                origin: Some(origin.clone()),
                kind: EffectExprKind::Pure(PureExprKind::Value(PureValue::Unit(
                    crate::core::literal::UnitNode,
                ))),
            },
            StoredNode::<EffectOperationFamily> {
                dialect: DialectId::named(EffectOperationFamily::DIALECT_NAME),
                ty: Type::Unit,
                effects: EffectRow::empty(),
                origin: Some(origin),
                kind: EffectExprKind::Operation(EffectOperation::Handler(HandlerNode::new(
                    HandlerId::new(0),
                    node,
                    EffectInstance::new(effect, Box::new([])),
                    clauses,
                ))),
            },
        ];
        let run = |early: bool, budget: &mut TypeWorkBudget| {
            let mut graph = graph(vec![Expr::Scalar, Expr::Scalar]);
            let methods = super::super::MethodUses::new(&[], budget).unwrap();
            let result = graph.build_operation(
                1,
                &nodes,
                &mut HashMap::new(),
                &mut HashMap::new(),
                |kind| match kind {
                    EffectExprKind::Operation(operation) => Some(operation),
                    _ => None,
                },
                &methods,
                &[],
                &mut FunctionMetadataPreparation::new(&nodes, |kind| match kind {
                    EffectExprKind::Operation(operation) => Some(operation),
                    _ => None,
                }),
                budget,
            );
            if early {
                assert_eq!(graph.expressions.len(), 2);
            }
            result.map(|_| ())
        };
        for limit in [0, WIDTH - 1] {
            let mut budget = TypeWorkBudget::with_limit(limit);
            assert!(matches!(run(true, &mut budget), Err(Failure::Resource)));
            assert_eq!(budget.used(), 0);
        }
        let mut measured = TypeWorkBudget::unbounded();
        run(false, &mut measured).unwrap();
        assert!(matches!(
            run(false, &mut TypeWorkBudget::with_limit(measured.used() - 1)),
            Err(Failure::Resource)
        ));
        for _ in 0..2 {
            run(false, &mut TypeWorkBudget::with_limit(measured.used())).unwrap();
        }
    }

    #[test]
    fn completed_match_setup_keeps_late_constructor_payload_ownership() {
        let family = crate::types::NominalTypeId::new(crate::module::ModuleId::new(77), 1);
        let first = ConstructorId::new(family, 0);
        let second = ConstructorId::new(family, 1);
        let graph = graph(vec![
            Expr::Slot,
            Expr::Slot,
            Expr::Project {
                value: 0,
                field: 0,
                constructor: Some(second),
            },
            Expr::Match {
                scrutinee: 0,
                arms: vec![(Vec::new(), 4), (vec![(5, 2)], 6)],
            },
            Expr::Scalar,
            Expr::Slot,
            Expr::Alias(5),
            Expr::Constructor(second),
            Expr::Call {
                function: 7,
                arguments: vec![1],
                scalar: false,
                type_application: false,
            },
        ]);
        let mut work = TypeWorkBudget::unbounded();
        let mut analysis = Analysis::new(&graph, &mut work).unwrap();
        let scrutinee = analysis.slot(0, 0, &mut work).unwrap();
        analysis
            .atom(scrutinee, Atom::Constructor(first), &mut work)
            .unwrap();
        let result = analysis.slot(3, 0, &mut work).unwrap();
        analysis.close(&mut work).unwrap();
        assert!(analysis.slots[result].preparation.is_edges_installed());
        assert_eq!(analysis.slots[result].atoms, vec![Atom::Free]);
        let edges = analysis.slots[result].edges.clone();
        let payload = analysis.slot(1, 0, &mut work).unwrap();
        let owner = Atom::Resource(99, 0);
        analysis.atom(payload, owner, &mut work).unwrap();
        let constructor_application = analysis.slot(8, 0, &mut work).unwrap();
        analysis.close(&mut work).unwrap();
        assert!(
            analysis.slots[constructor_application]
                .atoms
                .contains(&Atom::Aggregate(8, 0))
        );
        analysis
            .atom(scrutinee, Atom::Constructor(second), &mut work)
            .unwrap();
        analysis
            .atom(scrutinee, Atom::Aggregate(8, 0), &mut work)
            .unwrap();
        analysis.close(&mut work).unwrap();
        assert!(analysis.slots[result].preparation.is_edges_installed());
        assert_eq!(analysis.slots[result].edges, edges);
        assert_eq!(analysis.slots[result].atoms, vec![Atom::Free, owner]);
        assert_eq!(
            analysis.dependencies(result, &mut work).unwrap(),
            vec![owner]
        );
    }

    #[test]
    fn strict_results_wait_for_bottom_inputs_and_wake_on_late_values() {
        for shape in 0..7 {
            let mut graph = graph(vec![
                Expr::Slot,
                Expr::Slot,
                Expr::Scalar,
                Expr::Function {
                    parameters: Vec::new(),
                    body: 2,
                    captures: vec![1],
                },
                Expr::Slot,
                Expr::Function {
                    parameters: vec![4],
                    body: 3,
                    captures: vec![1],
                },
                Expr::Scalar,
                Expr::Slot,
                Expr::Slot,
            ]);
            graph.expressions[6] = match shape {
                0 => Expr::Match {
                    scrutinee: 0,
                    arms: vec![(Vec::new(), 3)],
                },
                1 => Expr::Tuple(vec![3, 0]),
                2 => Expr::Call {
                    function: 5,
                    arguments: vec![0],
                    scalar: false,
                    type_application: false,
                },
                // Primitive lowering shares an already-inhabited scalar binder:
                // readiness must inspect its initializer, not that binder.
                3 => Expr::Recursive {
                    bindings: vec![(2, 0)],
                    body: 3,
                },
                4 => Expr::Resource {
                    success: None,
                    failure: None,
                    handle: 7,
                    identity: 8,
                    initializer: 0,
                    body: 3,
                    source: graph.sources[6],
                },
                5 => Expr::Cleanup { body: 3, action: 0 },
                6 => Expr::Bind {
                    binder: 7,
                    initializer: 0,
                    body: 3,
                },
                _ => unreachable!(),
            };
            let run = |budget: &mut TypeWorkBudget| {
                let mut analysis = Analysis::new(&graph, budget)?;
                let marker = Atom::Resource(99, 0);
                let capture = analysis.slot(1, 0, budget)?;
                analysis.atom(capture, marker, budget)?;
                let result = analysis.slot(6, 0, budget)?;
                analysis.close(budget)?;
                assert!(
                    analysis.slots[result].atoms.is_empty(),
                    "shape={shape} must not manufacture a result"
                );
                assert!(!analysis.slots[result].preparation.is_edges_installed());
                if shape == 4 {
                    assert!(
                        analysis
                            .indices
                            .get(&(7, 0))
                            .is_none_or(|slot| analysis.slots[*slot].atoms.is_empty())
                    );
                }
                let input = analysis.slot(0, 0, budget)?;
                analysis.atom(input, Atom::Free, budget)?;
                analysis.close(budget)?;
                assert!(
                    analysis.dependencies(result, budget)?.contains(&marker),
                    "shape={shape} must wake after resume"
                );
                assert_eq!(
                    analysis.slots[result].preparation.is_edges_installed(),
                    shape != 2
                );
                // Setup readiness never freezes the result or its lexical fields.
                // A later owner still reaches the same returned closure dependency.
                let later = Atom::Resource(100, 0);
                analysis.atom(capture, later, budget)?;
                analysis.close(budget)?;
                let dependencies = analysis.dependencies(result, budget)?;
                assert!(dependencies.contains(&marker), "shape={shape}");
                assert!(dependencies.contains(&later), "shape={shape}");
                assert!(!analysis.slots[result].terminal);
                Ok::<(), Failure>(())
            };
            let mut measured = TypeWorkBudget::unbounded();
            run(&mut measured).unwrap();
            assert!(matches!(
                run(&mut TypeWorkBudget::with_limit(measured.used() - 1)),
                Err(Failure::Resource)
            ));
            for _ in 0..2 {
                run(&mut TypeWorkBudget::with_limit(measured.used())).unwrap();
            }
        }
    }

    #[test]
    fn recursive_callee_contexts_join_calls_but_keep_distinct_entries() {
        let graph = graph(vec![Expr::Scalar]);
        let run = |budget: &mut TypeWorkBudget| {
            let mut analysis = Analysis::new(&graph, budget)?;
            let first = analysis.context(0, Transition::Invoke(1, 10), budget)?;
            let second = analysis.context(0, Transition::Invoke(2, 10), budget)?;
            assert_ne!(first, second);
            let mutual = analysis.context(first, Transition::Invoke(3, 20), budget)?;
            for site in [4, 5] {
                assert_eq!(
                    analysis.context(mutual, Transition::Invoke(site, 10), budget)?,
                    first
                );
                assert_eq!(
                    analysis.context(second, Transition::Invoke(site, 10), budget)?,
                    second
                );
            }
            // A later Root and an earlier Invoke can both match the next
            // Invoke. Reverse parent traversal must still select the first one.
            let later_root = analysis.context(first, Transition::Root(10), budget)?;
            assert_eq!(
                analysis.context(later_root, Transition::Invoke(99, 10), budget)?,
                first
            );
            let root = analysis.context(0, Transition::Root(10), budget)?;
            assert_eq!(
                analysis.context(root, Transition::Invoke(6, 10), budget)?,
                root
            );
            let focus = analysis.context(0, Transition::Focus, budget)?;
            let fresh = analysis.context(focus, Transition::Invoke(1, 10), budget)?;
            assert_ne!(fresh, first);
            Ok::<(), Failure>(())
        };
        let mut measured = TypeWorkBudget::unbounded();
        run(&mut measured).unwrap();
        assert!(matches!(
            run(&mut TypeWorkBudget::with_limit(measured.used() - 1)),
            Err(Failure::Resource)
        ));
        for _ in 0..2 {
            run(&mut TypeWorkBudget::with_limit(measured.used())).unwrap();
        }
    }

    #[test]
    fn context_lookup_charges_its_path_without_scanning_unrelated_contexts() {
        let graph = graph(vec![Expr::Scalar]);
        let lookup = |width| {
            let mut analysis = Analysis::new(&graph, &mut TypeWorkBudget::unbounded()).unwrap();
            for index in 0..width {
                analysis
                    .context(0, Transition::Root(index), &mut TypeWorkBudget::unbounded())
                    .unwrap();
            }
            let expected = analysis
                .context(0, Transition::Root(width), &mut TypeWorkBudget::unbounded())
                .unwrap();
            let mut measured = TypeWorkBudget::unbounded();
            assert_eq!(
                analysis
                    .context(0, Transition::Root(width), &mut measured)
                    .unwrap(),
                expected
            );
            let exact = measured.used();
            assert!(matches!(
                analysis.context(
                    0,
                    Transition::Root(width),
                    &mut TypeWorkBudget::with_limit(exact - 1)
                ),
                Err(Failure::Resource)
            ));
            let mut retry = TypeWorkBudget::with_limit(exact);
            assert_eq!(
                analysis
                    .context(0, Transition::Root(width), &mut retry)
                    .unwrap(),
                expected
            );
            assert_eq!(retry.used(), exact);
            exact
        };
        assert_eq!(lookup(4), lookup(64));
    }

    #[test]
    fn canonical_context_prefixes_preserve_source_order_and_atomic_cold_publication() {
        let mut graph = graph(vec![Expr::Scalar, Expr::Scalar, Expr::Scalar, Expr::Scalar]);
        let file = crate::source::SourceFile::new("context-path-source", "abcd").unwrap();
        graph.sources = (0..4)
            .map(|offset| {
                file.span(crate::source::ByteRange::new(offset, offset + 1).unwrap())
                    .unwrap()
            })
            .collect();
        let setup = || {
            let mut work = TypeWorkBudget::unbounded();
            let mut analysis = Analysis::new(&graph, &mut work).unwrap();
            let mut parent = 0;
            for transition in [
                Transition::Root(0),
                Transition::Call(1),
                Transition::Invoke(2, 3),
                Transition::Dispatch(1, 2, 4),
            ] {
                parent = analysis.context(parent, transition, &mut work).unwrap();
            }
            (analysis, parent)
        };
        let (mut measured, parent) = setup();
        let port = measured
            .install_slot(0, parent, &mut TypeWorkBudget::unbounded())
            .unwrap();
        let (request, path) = measured
            .actual_request_path(port, parent, &mut TypeWorkBudget::unbounded())
            .unwrap();
        assert_eq!(request, graph.sources[0]);
        assert_eq!(
            path,
            vec![
                super::super::ActualValuePathStep::Root(graph.sources[0]),
                super::super::ActualValuePathStep::Call(graph.sources[1]),
                super::super::ActualValuePathStep::Invoke(graph.sources[2], graph.sources[3]),
                super::super::ActualValuePathStep::Dispatch(graph.sources[1], graph.sources[2], 4),
            ]
        );
        let mut cold = TypeWorkBudget::unbounded();
        let focused = measured
            .context(parent, Transition::Focus, &mut cold)
            .unwrap();
        let exact = cold.used();
        let restored = measured
            .context(
                parent,
                Transition::Restore(1, 2, 3),
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap();
        let malformed_source = measured
            .context(
                parent,
                Transition::Call(99),
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap();
        for context in [focused, restored, malformed_source] {
            assert!(matches!(
                measured.actual_request_path(port, context, &mut TypeWorkBudget::unbounded()),
                Err(Failure::Invalid)
            ));
        }
        let inherited = measured
            .contexts
            .copy(&mut TypeWorkBudget::unbounded())
            .unwrap();
        assert_eq!(inherited.len(), measured.contexts.len());
        for context in 0..inherited.len() {
            assert_eq!(
                inherited
                    .forward(context, &mut TypeWorkBudget::unbounded())
                    .unwrap(),
                measured
                    .contexts
                    .forward(context, &mut TypeWorkBudget::unbounded())
                    .unwrap()
            );
        }
        for prefix in [0, 9] {
            for available in 0..exact {
                let (mut analysis, parent) = setup();
                let before_len = analysis.contexts.len();
                let before_revision = analysis.revision;
                let before_index = analysis.contexts.extensions.clone();
                let mut short = TypeWorkBudget::with_limit(prefix + available);
                short.charge(prefix).unwrap();
                assert!(matches!(
                    analysis.context(parent, Transition::Focus, &mut short),
                    Err(Failure::Resource)
                ));
                assert_eq!(analysis.contexts.len(), before_len);
                assert_eq!(analysis.contexts.extensions, before_index);
                assert_eq!(analysis.revision, before_revision);
                let mut retry = TypeWorkBudget::with_limit(prefix + exact);
                retry.charge(prefix).unwrap();
                assert_eq!(
                    analysis
                        .context(parent, Transition::Focus, &mut retry)
                        .unwrap(),
                    focused
                );
                assert_eq!(retry.used(), prefix + exact);
                assert_eq!(analysis.revision, before_revision + 1);
            }
        }
    }

    #[test]
    fn final_payload_check_cannot_materialize_an_unfinished_or_missing_input() {
        let mut graph = graph(vec![
            Expr::Scalar,
            Expr::Slot,
            Expr::Slot,
            Expr::Request {
                operand: 0,
                scalar: true,
            },
        ]);
        graph.expressions.push(Expr::Resource {
            success: None,
            failure: None,
            handle: 1,
            identity: 2,
            initializer: 0,
            body: 3,
            source: graph.sources[0],
        });
        graph.sources.push(graph.sources[0]);
        graph.positions.insert(4, 4);
        let mut budget = TypeWorkBudget::unbounded();
        let mut analysis = Analysis::new(&graph, &mut budget).unwrap();
        let request = analysis.slot(3, 0, &mut budget).unwrap();
        assert!(matches!(
            analysis.check_payload(request, 4, 0, &mut budget),
            Err(Failure::Invalid)
        ));
        analysis.close(&mut budget).unwrap();
        let revision = analysis.revision();
        analysis.check_payload(request, 4, 0, &mut budget).unwrap();
        assert_eq!(analysis.revision(), revision);
        analysis.indices.remove(&(0, 0));
        assert!(matches!(
            analysis.check_payload(request, 4, 0, &mut budget),
            Err(Failure::Invalid)
        ));
        assert_eq!(analysis.revision(), revision);
        assert!(analysis.pending.is_empty());
    }

    #[test]
    fn delayed_capture_leaf_and_populated_edge_wake_existing_consumers() {
        let graph = graph(vec![
            Expr::Slot,
            Expr::Function {
                parameters: Vec::new(),
                body: 2,
                captures: vec![0],
            },
            Expr::Scalar,
            Expr::Tuple(vec![1, 2]),
            Expr::Project {
                value: 3,
                field: 0,
                constructor: None,
            },
            Expr::Slot,
            Expr::Call {
                function: 5,
                arguments: vec![4],
                scalar: false,
                type_application: false,
            },
            Expr::Project {
                value: 3,
                field: 1,
                constructor: None,
            },
            Expr::Call {
                function: 5,
                arguments: vec![7],
                scalar: false,
                type_application: false,
            },
            Expr::Slot,
            Expr::Alias(9),
            Expr::Call {
                function: 5,
                arguments: vec![10],
                scalar: false,
                type_application: false,
            },
        ]);
        let run = |budget: &mut TypeWorkBudget| {
            let mut analysis = Analysis::new(&graph, budget)?;
            let opaque = analysis.slot(5, 0, budget)?;
            analysis.atom(opaque, Atom::Unknown, budget)?;
            let dependent = analysis.slot(6, 0, budget)?;
            let copied = analysis.slot(8, 0, budget)?;
            let alias = analysis.slot(11, 0, budget)?;
            analysis.close(budget)?;
            let marker = Atom::Resource(99, 0);
            assert!(!analysis.slots[dependent].atoms.contains(&marker));
            let leaf = analysis.slot(0, 0, budget)?;
            analysis.atom(leaf, marker, budget)?;
            analysis.close(budget)?;
            assert!(analysis.slots[dependent].atoms.contains(&marker));
            assert!(!analysis.slots[copied].atoms.contains(&marker));
            assert!(!analysis.slots[alias].atoms.contains(&marker));
            let target = analysis.slot(9, 0, budget)?;
            analysis.join_ports(target, leaf, budget)?;
            analysis.close(budget)?;
            assert!(analysis.slots[alias].atoms.contains(&marker));
            Ok::<(), Failure>(())
        };
        let mut measured = TypeWorkBudget::unbounded();
        run(&mut measured).unwrap();
        run(&mut TypeWorkBudget::with_limit(measured.used())).unwrap();
        assert!(matches!(
            run(&mut TypeWorkBudget::with_limit(measured.used() - 1)),
            Err(Failure::Resource)
        ));
        run(&mut TypeWorkBudget::with_limit(measured.used())).unwrap();
    }

    #[test]
    fn repeated_static_cut_reuses_preparation_but_keeps_new_result_edges() {
        let mut graph = graph(vec![Expr::Scalar, Expr::Slot, Expr::Tuple(vec![0, 1])]);
        for code in 0..3 {
            graph.positions.insert(code, code);
        }
        let run = |reuse: bool, budget: &mut TypeWorkBudget| {
            let mut setup = TypeWorkBudget::unbounded();
            let mut analysis = Analysis::new(&graph, &mut setup)?;
            analysis.slot(2, 0, &mut setup)?;
            analysis.close(&mut setup)?;
            analysis.frozen_contexts = 1;
            let focus = analysis.context(0, Transition::Focus, &mut setup)?;
            analysis.focus = Some((99, focus));
            let before = budget.used();
            let cut = analysis.restore_cut(0, 2, 2, 1, &[0], false, budget)?;
            let first = budget.used() - before;
            if !reuse {
                return Ok(());
            }
            analysis.close(&mut setup)?;
            let source = analysis.slot(1, focus, &mut setup)?;
            analysis.atom(source, Atom::Resource(99, focus), &mut setup)?;
            analysis.close(&mut setup)?;
            let before = budget.used();
            let reused = analysis.restore_cut(0, 2, 2, 1, &[0], false, budget)?;
            assert!(budget.used() - before < first);
            assert_eq!(
                (reused.context, reused.input, reused.result),
                (cut.context, cut.input, cut.result)
            );
            analysis.join_ports(reused.input, source, budget)?;
            analysis.close(budget)?;
            assert!(
                analysis
                    .dependencies(reused.result, budget)?
                    .contains(&Atom::Resource(99, focus))
            );
            assert!(matches!(
                analysis.restore_cut(0, 2, 2, 0, &[0], false, &mut setup),
                Err(Failure::Invalid)
            ));
            Ok::<(), Failure>(())
        };
        for reuse in [false, true] {
            let mut measured = TypeWorkBudget::unbounded();
            run(reuse, &mut measured).unwrap();
            run(reuse, &mut TypeWorkBudget::with_limit(measured.used())).unwrap();
            assert!(matches!(
                run(reuse, &mut TypeWorkBudget::with_limit(measured.used() - 1)),
                Err(Failure::Resource)
            ));
            run(reuse, &mut TypeWorkBudget::with_limit(measured.used())).unwrap();
        }
    }

    #[test]
    fn provider_scope_result_keeps_body_tuple_and_independent_completion() {
        let family = crate::types::NominalTypeId::new(crate::module::ModuleId::new(77), 1);
        let completed = ConstructorId::new(family, 1);
        let refused = ConstructorId::new(family, 0);
        let source = crate::source::SourceFile::new("scope-result.ash", "x").unwrap();
        let span = source
            .span(crate::source::ByteRange::new(0, 1).unwrap())
            .unwrap();
        let graph = graph(vec![
            Expr::Scalar,
            Expr::Slot,
            Expr::Scalar,
            Expr::Tuple(vec![1, 2]),
            Expr::Resource {
                success: Some(completed),
                failure: Some(refused),
                handle: 9,
                identity: 10,
                initializer: 0,
                body: 3,
                source: span,
            },
            Expr::Project {
                value: 4,
                field: 0,
                constructor: Some(completed),
            },
            Expr::Project {
                value: 5,
                field: 0,
                constructor: None,
            },
            Expr::Project {
                value: 5,
                field: 1,
                constructor: None,
            },
            Expr::Project {
                value: 4,
                field: 0,
                constructor: Some(refused),
            },
            Expr::Slot,
            Expr::Slot,
        ]);
        let run = |budget: &mut TypeWorkBudget| {
            let mut analysis = Analysis::new(&graph, budget)?;
            let body = analysis.slot(1, 0, budget)?;
            let marker = Atom::Resource(99, 0);
            analysis.atom(body, marker, budget)?;
            let body_result = analysis.slot(6, 0, budget)?;
            let completion = analysis.slot(7, 0, budget)?;
            let refusal = analysis.slot(8, 0, budget)?;
            analysis.close(budget)?;
            assert!(
                analysis
                    .dependencies(body_result, budget)?
                    .contains(&marker)
            );
            assert!(!analysis.dependencies(completion, budget)?.contains(&marker));
            assert!(!analysis.dependencies(refusal, budget)?.contains(&marker));
            Ok::<(), Failure>(())
        };
        let mut measured = TypeWorkBudget::unbounded();
        run(&mut measured).unwrap();
        run(&mut TypeWorkBudget::with_limit(measured.used())).unwrap();
        assert!(matches!(
            run(&mut TypeWorkBudget::with_limit(measured.used() - 1)),
            Err(Failure::Resource)
        ));
    }

    #[test]
    fn restored_native_result_keeps_success_projection_without_reacquiring() {
        let success = ConstructorId::new(
            crate::types::NominalTypeId::new(crate::module::ModuleId::new(77), 1),
            0,
        );
        let mut graph = graph(vec![Expr::Scalar, Expr::Slot, Expr::Slot, Expr::Slot]);
        graph.expressions.push(Expr::Resource {
            success: Some(success),
            failure: Some(ConstructorId::new(success.owner(), 1)),
            handle: 2,
            identity: 3,
            initializer: 0,
            body: 1,
            source: graph.sources[0],
        });
        graph.expressions.push(Expr::Project {
            value: 4,
            field: 0,
            constructor: Some(success),
        });
        graph.sources.extend([graph.sources[0]; 2]);
        for code in 0..6 {
            graph.positions.insert(code, code);
        }
        let run = |budget: &mut TypeWorkBudget| {
            let mut analysis = Analysis::new(&graph, budget)?;
            analysis.slot(4, 0, budget)?;
            analysis.close(budget)?;
            analysis.frozen_contexts = 1;
            let focus = analysis.context(0, Transition::Focus, budget)?;
            analysis.focus = Some((99, focus));
            let cut = analysis.restore_cut(0, 4, usize::MAX - 1, 1, &[], true, budget)?;
            let marker = Atom::Resource(99, focus);
            analysis.atom(cut.input, marker, budget)?;
            let projected = analysis.slot(5, cut.context, budget)?;
            analysis.close(budget)?;
            assert!(analysis.dependencies(projected, budget)?.contains(&marker));
            assert!(
                !analysis.indices.contains_key(&(0, cut.context)),
                "the initializer is not replayed"
            );
            assert!(
                !analysis.indices.contains_key(&(2, cut.context)),
                "no fresh handle is installed"
            );
            assert!(
                !analysis.indices.contains_key(&(3, cut.context)),
                "no fresh identity is installed"
            );
            Ok::<(), Failure>(())
        };
        let mut measured = TypeWorkBudget::unbounded();
        run(&mut measured).unwrap();
        run(&mut TypeWorkBudget::with_limit(measured.used())).unwrap();
        assert!(matches!(
            run(&mut TypeWorkBudget::with_limit(measured.used() - 1)),
            Err(Failure::Resource)
        ));
        run(&mut TypeWorkBudget::with_limit(measured.used())).unwrap();
    }

    #[test]
    fn terminal_completed_value_keeps_its_frozen_creation_slots() {
        let graph = graph(vec![
            Expr::Slot,
            Expr::Function {
                parameters: Vec::new(),
                body: 3,
                captures: vec![0],
            },
            Expr::Alias(1),
            Expr::Scalar,
        ]);
        let mut budget = TypeWorkBudget::unbounded();
        let mut analysis = Analysis::new(&graph, &mut budget).unwrap();
        let input = analysis.slot(0, 0, &mut budget).unwrap();
        analysis.atom(input, Atom::Free, &mut budget).unwrap();
        analysis.slot(2, 0, &mut budget).unwrap();
        analysis.close(&mut budget).unwrap();
        let active = analysis
            .context(0, Transition::Call(2), &mut budget)
            .unwrap();
        analysis.freeze_slot(2, 0, active, &mut budget).unwrap();
        let input = analysis.slot(0, active, &mut budget).unwrap();
        analysis
            .atom(input, Atom::Resource(3, active), &mut budget)
            .unwrap();
        analysis.close(&mut budget).unwrap();
        let result = analysis.slot(2, active, &mut budget).unwrap();
        assert_eq!(analysis.slots[result].atoms, vec![Atom::Closure(1, 0)]);
        assert!(
            analysis
                .dependencies(result, &mut budget)
                .unwrap()
                .is_empty()
        );
        assert!(
            !analysis.indices.contains_key(&(1, active)),
            "the completed initializer must not be replayed"
        );
    }

    #[test]
    fn focused_entry_marks_only_the_fresh_owner_and_keeps_inherited_structure() {
        let mut graph = graph(vec![
            Expr::Slot,
            Expr::Slot,
            Expr::Slot,
            Expr::Scalar,
            Expr::Function {
                parameters: Vec::new(),
                body: 3,
                captures: vec![1],
            },
            Expr::Tuple(vec![0, 4]),
        ]);
        graph.expressions.push(Expr::Resource {
            success: None,
            failure: None,
            handle: 1,
            identity: 2,
            initializer: 3,
            body: 5,
            source: graph.sources[0],
        });
        graph.sources.push(graph.sources[0]);
        graph.expressions.push(Expr::Slot);
        graph.expressions.push(Expr::Tuple(vec![4, 7]));
        graph.sources.extend([graph.sources[0]; 2]);
        graph.positions.insert(6, 6);
        for code in [4, 7, 8] {
            graph.positions.insert(code, code);
        }
        let mut budget = TypeWorkBudget::unbounded();
        let mut normal = Analysis::new(&graph, &mut budget).unwrap();
        let inherited = normal.slot(0, 0, &mut budget).unwrap();
        normal
            .atom(inherited, Atom::Closure(4, 0), &mut budget)
            .unwrap();
        normal.slot(6, 0, &mut budget).unwrap();
        normal.slot(8, 0, &mut budget).unwrap();
        normal.close(&mut budget).unwrap();
        let mut focused_work = TypeWorkBudget::unbounded();
        let (mut focused, context) = normal.focused(6, 0, &mut focused_work).unwrap();
        let exact = focused_work.used();
        for prefix in [0, 9] {
            let mut short = TypeWorkBudget::with_limit(prefix + exact - 1);
            short.charge(prefix).unwrap();
            assert!(matches!(
                normal.focused(6, 0, &mut short),
                Err(Failure::Resource)
            ));
            let mut retry = TypeWorkBudget::with_limit(prefix + exact);
            retry.charge(prefix).unwrap();
            let (retried, retry_context) = normal.focused(6, 0, &mut retry).unwrap();
            assert_eq!(retry.used(), prefix + exact);
            assert_eq!(retry_context, context);
            assert_eq!(retried.atom_pairs, focused.atom_pairs);
        }
        for (slot, original) in normal.slots.iter().enumerate() {
            for atom in &original.atoms {
                assert!(focused.atom_pairs.contains(&(slot, *atom)));
                let revision = focused.revision;
                focused
                    .atom(slot, *atom, &mut TypeWorkBudget::with_limit(1))
                    .unwrap();
                assert_eq!(
                    focused.revision, revision,
                    "copied frozen atoms are already indexed"
                );
                assert_eq!(focused.slots[slot].atoms, original.atoms);
            }
        }
        let inherited = focused.slot(0, context, &mut budget).unwrap();
        let local = focused.slot(4, context, &mut budget).unwrap();
        assert_eq!(focused.slots[inherited].atoms, vec![Atom::Closure(4, 0)]);
        assert!(
            !focused
                .dependencies(inherited, &mut budget)
                .unwrap()
                .contains(&Atom::Resource(6, context))
        );
        assert!(
            focused
                .dependencies(local, &mut budget)
                .unwrap()
                .contains(&Atom::Resource(6, context))
        );
        let recursive = focused
            .context(context, Transition::Call(4), &mut budget)
            .unwrap();
        assert_ne!(recursive, context);
        assert_eq!(
            focused
                .context(recursive, Transition::Call(4), &mut budget)
                .unwrap(),
            recursive
        );
        let cut = focused
            .restore_cut(0, 8, 2, 7, &[4], false, &mut budget)
            .unwrap();
        focused.join_ports(cut.input, local, &mut budget).unwrap();
        focused.close(&mut budget).unwrap();
        let completed = focused.slot(4, cut.context, &mut budget).unwrap();
        assert_eq!(focused.slots[completed].atoms, vec![Atom::Closure(4, 0)]);
        assert!(
            !focused
                .dependencies(completed, &mut budget)
                .unwrap()
                .contains(&Atom::Resource(6, context))
        );
        assert!(
            focused
                .dependencies(cut.result, &mut budget)
                .unwrap()
                .contains(&Atom::Resource(6, context))
        );
        assert!(
            matches!(
                focused.join_ports(0, local, &mut budget),
                Err(Failure::Invalid)
            ),
            "frozen pre-entry ports cannot be mutated"
        );
    }

    fn structural_transfer_chain_graph() -> Graph {
        let mut graph = evidence_completion_graph();
        graph.expressions.extend([
            Expr::Merge(vec![2, 3]),
            Expr::Function {
                parameters: Vec::new(),
                body: 9,
                captures: vec![2, 3],
            },
            Expr::Call {
                function: 6,
                arguments: Vec::new(),
                scalar: false,
                type_application: false,
            },
            Expr::Slot,
        ]);
        graph.sources.extend([graph.sources[0]; 4]);
        let Expr::Function { body, .. } = &mut graph.expressions[5] else {
            unreachable!()
        };
        *body = 9;
        graph
    }

    #[test]
    fn structural_transfer_chain_keeps_late_identity_unknown_and_real_consumers() {
        let graph = structural_transfer_chain_graph();
        let mut work = TypeWorkBudget::unbounded();
        let mut analysis = Analysis::new(&graph, &mut work).unwrap();
        let value = analysis.slot(0, 0, &mut work).unwrap();
        analysis
            .atom(value, Atom::Closure(5, 0), &mut work)
            .unwrap();
        let argument = analysis.slot(1, 0, &mut work).unwrap();
        analysis.atom(argument, Atom::Free, &mut work).unwrap();
        let lexical = analysis.slot(3, 0, &mut work).unwrap();
        let call = analysis.slot(11, 0, &mut work).unwrap();
        analysis.close(&mut work).unwrap();
        let evidence = analysis.indices[&(6, 0)];
        let specialized = analysis.context(0, Transition::Call(6), &mut work).unwrap();
        let invoked = analysis
            .context(0, Transition::Invoke(11, 5), &mut work)
            .unwrap();
        assert!(
            analysis
                .callable_transfers
                .contains(&(Some(evidence), evidence, 5, 0))
        );
        assert!(
            analysis
                .callable_transfers
                .contains(&(Some(call), call, 5, specialized))
        );
        for expression in [2, 3] {
            let capture = analysis.indices[&(expression, specialized)];
            let destination = analysis.indices[&(expression, invoked)];
            assert!(analysis.edge_pairs().contains_key(&(destination, capture)));
            assert!(!analysis.watched_pairs().contains(&(capture, evidence)));
            assert!(!analysis.watched_pairs().contains(&(capture, call)));
            assert!(!analysis.watched_pairs().contains(&(destination, call)));
        }
        assert!(analysis.watched_pairs().contains(&(argument, evidence)));
        assert!(analysis.watched_pairs().contains(&(evidence, call)));
        let body = analysis.indices[&(9, invoked)];
        assert!(analysis.watched_pairs().contains(&(body, call)));
        let consumer = analysis.slot(12, 0, &mut work).unwrap();
        analysis.close(&mut work).unwrap();
        analysis.current = Some(consumer);
        assert!(
            analysis
                .dependencies(evidence, &mut work)
                .unwrap()
                .is_empty()
        );
        let captured = analysis.indices[&(3, specialized)];
        assert!(analysis.watched_pairs().contains(&(captured, consumer)));
        analysis.current = None;
        let owner = Atom::Resource(8, 0);
        analysis.atom(lexical, owner, &mut work).unwrap();
        assert!(analysis.slots[captured].queued);
        assert!(!analysis.slots[evidence].queued);
        assert!(!analysis.slots[call].queued);
        analysis.close(&mut work).unwrap();
        assert!(analysis.slots[call].atoms.contains(&owner));
        assert!(
            analysis
                .dependencies(evidence, &mut work)
                .unwrap()
                .contains(&owner)
        );

        // A later actual Closure identity installs its own complete transfer.
        let other_creation = analysis
            .context(0, Transition::Root(216), &mut work)
            .unwrap();
        let other_capture = analysis.slot(3, other_creation, &mut work).unwrap();
        let other_owner = Atom::Resource(8, other_creation);
        analysis
            .atom(other_capture, other_owner, &mut work)
            .unwrap();
        analysis
            .atom(value, Atom::Closure(10, other_creation), &mut work)
            .unwrap();
        analysis.close(&mut work).unwrap();
        assert!(analysis.callable_transfers.contains(&(
            Some(evidence),
            evidence,
            10,
            other_creation
        )));
        assert!(
            analysis
                .callable_transfers
                .contains(&(Some(call), call, 10, specialized))
        );
        assert!(analysis.slots[call].atoms.contains(&other_owner));
        let stamps = analysis.callable_transfers.clone();
        let specialization_stamps = analysis.specialization_transfers.clone();
        analysis
            .atom(argument, Atom::Aggregate(7, 0), &mut work)
            .unwrap();
        analysis.atom(value, Atom::Unknown, &mut work).unwrap();
        analysis.close(&mut work).unwrap();
        assert!(analysis.slots[evidence].atoms.contains(&Atom::Unknown));
        assert!(analysis.slots[call].atoms.contains(&Atom::Unknown));
        assert!(analysis.slots[call].atoms.contains(&owner));
        assert!(analysis.slots[call].atoms.contains(&other_owner));
        assert!(analysis.watched_pairs().contains(&(lexical, evidence)));
        assert!(analysis.watched_pairs().contains(&(captured, call)));
        assert_eq!(analysis.callable_transfers, stamps);
        assert_eq!(analysis.specialization_transfers, specialization_stamps);
    }

    #[test]
    fn structural_transfer_chain_refusal_keeps_independent_publication_and_fresh_retry() {
        fn setup(graph: &Graph) -> (Analysis<'_>, usize, usize) {
            let mut work = TypeWorkBudget::unbounded();
            let mut analysis = Analysis::new(graph, &mut work).unwrap();
            let value = analysis.slot(0, 0, &mut work).unwrap();
            analysis
                .atom(value, Atom::Closure(5, 0), &mut work)
                .unwrap();
            let argument = analysis.slot(1, 0, &mut work).unwrap();
            analysis.atom(argument, Atom::Free, &mut work).unwrap();
            let lexical = analysis.slot(3, 0, &mut work).unwrap();
            analysis.atom(lexical, Atom::Free, &mut work).unwrap();
            let evidence = analysis.slot(6, 0, &mut work).unwrap();
            let call = analysis.slot(11, 0, &mut work).unwrap();
            (analysis, evidence, call)
        }
        fn install(
            analysis: &mut Analysis<'_>,
            evidence: usize,
            call: usize,
            work: &mut TypeWorkBudget,
        ) -> Result<(), Failure> {
            analysis.current = Some(evidence);
            analysis.evaluate(evidence, work)?;
            analysis.current = Some(call);
            analysis.evaluate(call, work)?;
            Ok(())
        }
        let graph = structural_transfer_chain_graph();
        let (mut measured, evidence, call) = setup(&graph);
        let mut exact = TypeWorkBudget::unbounded();
        install(&mut measured, evidence, call, &mut exact).unwrap();
        let required = exact.used();
        let transfers = measured.callable_transfers.clone();
        let specialization_stamps = measured.specialization_transfers.clone();
        let edges = measured.edge_pairs();
        let watches = measured.watched_pairs();
        measured.current = None;
        measured.close(&mut TypeWorkBudget::unbounded()).unwrap();
        let result = measured.slots[call].atoms.clone();
        let mut saw_completed_evidence_before_call_refusal = false;
        for prefix in [0, 11] {
            for available in 0..required {
                let (mut refused, evidence, call) = setup(&graph);
                let mut short = TypeWorkBudget::with_limit(prefix + available);
                short.charge(prefix).unwrap();
                assert!(matches!(
                    install(&mut refused, evidence, call, &mut short),
                    Err(Failure::Resource)
                ));
                assert!(
                    !refused
                        .callable_transfers
                        .iter()
                        .any(|(_, reader, _, _)| *reader == call)
                );
                if refused
                    .callable_transfers
                    .contains(&(Some(evidence), evidence, 5, 0))
                {
                    saw_completed_evidence_before_call_refusal = true;
                    assert_eq!(
                        refused.slots[evidence].preparation,
                        SlotPreparation::EvidenceInputsInstalled
                    );
                }
            }
            let (mut retried, evidence, call) = setup(&graph);
            let mut retry = TypeWorkBudget::with_limit(prefix + required);
            retry.charge(prefix).unwrap();
            install(&mut retried, evidence, call, &mut retry).unwrap();
            assert_eq!(retry.used(), prefix + required);
            assert_eq!(retried.callable_transfers, transfers);
            assert_eq!(retried.specialization_transfers, specialization_stamps);
            assert_eq!(retried.edge_pairs(), edges);
            assert_eq!(retried.watched_pairs(), watches);
            retried.current = None;
            retried.close(&mut TypeWorkBudget::unbounded()).unwrap();
            assert_eq!(retried.slots[call].atoms, result);
        }
        assert!(saw_completed_evidence_before_call_refusal);
    }

    // ASH_INPUT169_BEGIN_TESTS
    #[test]
    fn structural_specialization_keeps_late_capture_and_unknown_consumers_live() {
        let mut graph = evidence_completion_graph();
        graph.expressions.push(Expr::Slot);
        graph.sources.push(graph.sources[0]);
        let mut work = TypeWorkBudget::unbounded();
        let mut analysis = Analysis::new(&graph, &mut work).unwrap();
        let value = analysis.slot(0, 0, &mut work).unwrap();
        analysis
            .atom(value, Atom::Closure(5, 0), &mut work)
            .unwrap();
        let argument = analysis.slot(1, 0, &mut work).unwrap();
        analysis.atom(argument, Atom::Free, &mut work).unwrap();
        let lexical = analysis.slot(3, 0, &mut work).unwrap();
        let evidence = analysis.slot(6, 0, &mut work).unwrap();
        analysis.close(&mut work).unwrap();
        let specialized = analysis.context(0, Transition::Call(6), &mut work).unwrap();
        let bound = analysis.indices[&(2, specialized)];
        let captured = analysis.indices[&(3, specialized)];
        assert!(analysis.edge_pairs().contains_key(&(bound, argument)));
        assert!(analysis.edge_pairs().contains_key(&(captured, lexical)));
        assert!(!analysis.watched_pairs().contains(&(bound, evidence)));
        assert!(!analysis.watched_pairs().contains(&(captured, evidence)));
        assert!(!analysis.watched_pairs().contains(&(lexical, evidence)));
        assert!(analysis.watched_pairs().contains(&(argument, evidence)));
        let consumer = analysis.slot(9, 0, &mut work).unwrap();
        analysis.close(&mut work).unwrap();
        analysis.current = Some(consumer);
        assert!(
            analysis
                .dependencies(evidence, &mut work)
                .unwrap()
                .is_empty()
        );
        assert!(analysis.watched_pairs().contains(&(captured, consumer)));
        analysis.current = None;
        let owner = Atom::Resource(8, 0);
        analysis.atom(lexical, owner, &mut work).unwrap();
        assert!(analysis.slots[captured].queued);
        assert!(!analysis.slots[evidence].queued);
        analysis.close(&mut work).unwrap();
        assert!(analysis.slots[captured].atoms.contains(&owner));
        assert_eq!(
            analysis.dependencies(evidence, &mut work).unwrap(),
            vec![owner]
        );
        let stamps = analysis.specialization_transfers.clone();
        analysis
            .atom(argument, Atom::Aggregate(7, 0), &mut work)
            .unwrap();
        analysis.atom(value, Atom::Unknown, &mut work).unwrap();
        analysis.close(&mut work).unwrap();
        assert!(analysis.slots[evidence].atoms.contains(&Atom::Unknown));
        assert!(analysis.slots[evidence].atoms.contains(&owner));
        assert_eq!(analysis.specialization_transfers, stamps);
    }

    #[test]
    fn evidence_input_phase_keeps_late_live_atoms_and_other_direct_readers() {
        let graph = evidence_completion_graph();
        let mut work = TypeWorkBudget::unbounded();
        let mut analysis = Analysis::new(&graph, &mut work).unwrap();
        let value = analysis.slot(0, 0, &mut work).unwrap();
        let argument = analysis.slot(1, 0, &mut work).unwrap();
        analysis.atom(argument, Atom::Free, &mut work).unwrap();
        let lexical = analysis.slot(3, 0, &mut work).unwrap();
        analysis.atom(lexical, Atom::Free, &mut work).unwrap();
        let evidence = analysis.slot(6, 0, &mut work).unwrap();
        analysis.current = Some(evidence);
        assert!(!analysis.evaluate(evidence, &mut work).unwrap());
        assert_eq!(
            analysis.slots[evidence].preparation,
            SlotPreparation::EvidenceInputsInstalled
        );
        assert!(analysis.slots[evidence].atoms.is_empty());
        for source in [value, argument] {
            assert!(analysis.watched_pairs().contains(&(source, evidence)));
            assert!(analysis.slots[source].readers.contains(&evidence));
        }
        analysis.current = None;
        analysis
            .atom(value, Atom::Closure(5, 0), &mut work)
            .unwrap();
        analysis.close(&mut work).unwrap();
        assert!(!analysis.slots[evidence].atoms.is_empty());
        assert_eq!(
            analysis.slots[evidence].preparation,
            SlotPreparation::EvidenceInputsInstalled
        );

        let owner_context = analysis
            .context(0, Transition::Root(170), &mut work)
            .unwrap();
        analysis.slot(8, owner_context, &mut work).unwrap();
        analysis.close(&mut work).unwrap();
        let owner = Atom::Resource(8, owner_context);
        let handle = analysis.indices[&(2, owner_context)];
        assert!(analysis.slots[handle].atoms.contains(&owner));
        analysis.atom(argument, owner, &mut work).unwrap();
        analysis.close(&mut work).unwrap();
        assert!(
            analysis
                .dependencies(evidence, &mut work)
                .unwrap()
                .contains(&owner)
        );

        let reader_context = analysis
            .context(0, Transition::Root(171), &mut work)
            .unwrap();
        let reader = analysis.slot(4, reader_context, &mut work).unwrap();
        analysis.current = Some(reader);
        analysis.evaluate(evidence, &mut work).unwrap();
        for source in [value, argument] {
            assert!(analysis.watched_pairs().contains(&(source, reader)));
            assert!(analysis.slots[source].readers.contains(&reader));
        }
        assert_eq!(
            analysis.slots[evidence].preparation,
            SlotPreparation::EvidenceInputsInstalled
        );

        // A cold None-reader visit cannot certify the slot's own input watches.
        let none_context = analysis
            .context(0, Transition::Root(172), &mut work)
            .unwrap();
        analysis.current = None;
        let none_evidence = analysis.slot(6, none_context, &mut work).unwrap();
        analysis.evaluate(none_evidence, &mut work).unwrap();
        assert_eq!(
            analysis.slots[none_evidence].preparation,
            SlotPreparation::Pending
        );

        // A prepared input phase cannot freeze Unknown's deep dependency walk.
        let unknown_context = analysis
            .context(0, Transition::Root(173), &mut work)
            .unwrap();
        let unknown_value = analysis.slot(0, unknown_context, &mut work).unwrap();
        analysis
            .atom(unknown_value, Atom::Unknown, &mut work)
            .unwrap();
        let unknown_argument = analysis.slot(1, unknown_context, &mut work).unwrap();
        analysis
            .atom(
                unknown_argument,
                Atom::Aggregate(7, unknown_context),
                &mut work,
            )
            .unwrap();
        let field = analysis.slot(3, unknown_context, &mut work).unwrap();
        analysis.atom(field, Atom::Free, &mut work).unwrap();
        let unknown = analysis.slot(6, unknown_context, &mut work).unwrap();
        analysis.close(&mut work).unwrap();
        assert_eq!(
            analysis.slots[unknown].preparation,
            SlotPreparation::EvidenceInputsInstalled
        );
        assert!(analysis.slots[field].readers.contains(&unknown));
        analysis.atom(field, owner, &mut work).unwrap();
        analysis.close(&mut work).unwrap();
        assert!(analysis.slots[unknown].atoms.contains(&Atom::Unknown));
        assert!(analysis.slots[unknown].atoms.contains(&owner));
    }

    #[test]
    fn evidence_input_phase_refusal_cuts_distinguish_inputs_from_dynamic_completion() {
        let graph = evidence_completion_graph();
        let setup = || {
            let mut work = TypeWorkBudget::unbounded();
            let mut analysis = Analysis::new(&graph, &mut work).unwrap();
            analysis.slot(0, 0, &mut work).unwrap();
            analysis.slot(1, 0, &mut work).unwrap();
            let evidence = analysis.slot(6, 0, &mut work).unwrap();
            analysis.current = Some(evidence);
            (analysis, evidence)
        };
        let setup_with_live_value = || {
            let (mut analysis, evidence) = setup();
            let mut work = TypeWorkBudget::unbounded();
            let value = analysis.indices[&(0, 0)];
            let argument = analysis.indices[&(1, 0)];
            analysis.atom(value, Atom::Unknown, &mut work).unwrap();
            analysis.atom(argument, Atom::Free, &mut work).unwrap();
            (analysis, evidence)
        };
        let (mut measured, evidence) = setup_with_live_value();
        let mut exact = TypeWorkBudget::unbounded();
        measured.evaluate(evidence, &mut exact).unwrap();
        assert_eq!(
            measured.slots[evidence].preparation,
            SlotPreparation::EvidenceInputsInstalled
        );
        let mut saw_pending = false;
        let mut saw_completed_inputs = false;
        for prefix in [0, 13] {
            for available in 0..exact.used() {
                let (mut refused, evidence) = setup_with_live_value();
                let mut short = TypeWorkBudget::with_limit(prefix + available);
                short.charge(prefix).unwrap();
                assert!(matches!(
                    refused.evaluate(evidence, &mut short),
                    Err(Failure::Resource)
                ));
                match refused.slots[evidence].preparation {
                    SlotPreparation::Pending => saw_pending = true,
                    SlotPreparation::EvidenceInputsInstalled => {
                        saw_completed_inputs = true;
                        for expression in [0, 1] {
                            let source = refused.indices[&(expression, 0)];
                            assert!(refused.watched_pairs().contains(&(source, evidence)));
                            assert!(refused.slots[source].readers.contains(&evidence));
                        }
                    }
                    SlotPreparation::EdgesInstalled => panic!("Evidence cannot finish fixed setup"),
                }
                assert!(refused.callable_transfers.is_empty());
                assert!(refused.specialization_transfers.is_empty());
                let mut retry = TypeWorkBudget::unbounded();
                refused.evaluate(evidence, &mut retry).unwrap();
                assert_eq!(
                    refused.slots[evidence].preparation,
                    SlotPreparation::EvidenceInputsInstalled
                );
                assert_eq!(refused.watched_pairs(), measured.watched_pairs());
                assert_eq!(
                    refused.slots[evidence].atoms,
                    measured.slots[evidence].atoms
                );
            }
        }
        assert!(saw_pending && saw_completed_inputs);
        // Keep the empty-input boundary separate from genuine live routing.
        let (mut measured, evidence) = setup();
        measured
            .evaluate(evidence, &mut TypeWorkBudget::unbounded())
            .unwrap();
        let mut warm = TypeWorkBudget::unbounded();
        measured.evaluate(evidence, &mut warm).unwrap();
        // Empty live input pays only the phase guard and exact value port.
        assert_eq!(warm.used(), 2);
        for available in 0..warm.used() {
            let mut short = TypeWorkBudget::with_limit(available);
            assert!(matches!(
                measured.evaluate(evidence, &mut short),
                Err(Failure::Resource)
            ));
            assert_eq!(
                measured.slots[evidence].preparation,
                SlotPreparation::EvidenceInputsInstalled
            );
        }
        measured.indices.remove(&(0, 0));
        assert!(matches!(
            measured.evaluate(evidence, &mut TypeWorkBudget::unbounded()),
            Err(Failure::Invalid)
        ));
        assert!(measured.callable_transfers.is_empty());

        // Input preparation may survive later malformed live Closure routing;
        // no successful callable/output phase can be inferred from it.
        let (mut malformed, evidence) = setup();
        let value = malformed.indices[&(0, 0)];
        malformed.slots[value].atoms = vec![Atom::Closure(7, 0)];
        assert!(matches!(
            malformed.evaluate(evidence, &mut TypeWorkBudget::unbounded()),
            Err(Failure::Invalid)
        ));
        assert_eq!(
            malformed.slots[evidence].preparation,
            SlotPreparation::EvidenceInputsInstalled
        );
        assert!(malformed.callable_transfers.is_empty());
        assert!(malformed.slots[evidence].atoms.is_empty());
    }

    #[test]
    fn evidence_input_phase_duplicate_inputs_and_focused_contexts_keep_exact_relations() {
        let mut graph = evidence_completion_graph();
        graph.positions.insert(174, 8);
        let Expr::Evidence { bindings, .. } = &mut graph.expressions[6] else {
            unreachable!()
        };
        let key = (bindings[0].0, bindings[0].1);
        bindings.push((key.0, key.1, 1));
        bindings.push((key.0, key.1, 6)); // The original Evidence is also an input.
        let mut work = TypeWorkBudget::unbounded();
        let mut analysis = Analysis::new(&graph, &mut work).unwrap();
        let evidence = analysis.slot(6, 0, &mut work).unwrap();
        analysis.current = Some(evidence);
        analysis.evaluate(evidence, &mut work).unwrap();
        for expression in [0, 1, 6] {
            let source = analysis.indices[&(expression, 0)];
            assert_eq!(
                analysis.slots[source]
                    .readers
                    .iter()
                    .filter(|&&reader| reader == evidence)
                    .count(),
                1
            );
        }
        assert_eq!(
            analysis.slots[evidence].preparation,
            SlotPreparation::EvidenceInputsInstalled
        );
        let other_context = analysis
            .context(0, Transition::Root(175), &mut work)
            .unwrap();
        analysis.current = None;
        let other = analysis.slot(6, other_context, &mut work).unwrap();
        assert_eq!(analysis.slots[other].preparation, SlotPreparation::Pending);
        analysis.current = Some(other);
        analysis.evaluate(other, &mut work).unwrap();
        assert_eq!(
            analysis.slots[other].preparation,
            SlotPreparation::EvidenceInputsInstalled
        );
        let other_source = analysis.indices[&(1, other_context)];
        assert_ne!(other_source, analysis.indices[&(1, 0)]);
        assert!(analysis.watched_pairs().contains(&(other_source, other)));
        assert!(!analysis.watched_pairs().contains(&(other_source, evidence)));

        let (mut focused, context) = analysis.focused(174, 0, &mut work).unwrap();
        for original in 0..analysis.slots.len() {
            assert!(focused.slots[original].terminal);
            assert_eq!(
                focused.slots[original].preparation,
                SlotPreparation::Pending
            );
        }
        focused.current = None;
        let fresh = focused.slot(6, context, &mut work).unwrap();
        assert_eq!(focused.slots[fresh].preparation, SlotPreparation::Pending);
        focused.current = Some(fresh);
        focused.evaluate(fresh, &mut work).unwrap();
        assert_eq!(
            focused.slots[fresh].preparation,
            SlotPreparation::EvidenceInputsInstalled
        );
        let source = focused.indices[&(1, context)];
        assert!(focused.watched_pairs().contains(&(source, fresh)));
        assert!(!focused.watched_pairs().contains(&(source, evidence)));
        assert!(
            Analysis::new(&graph, &mut work)
                .unwrap()
                .watched_pairs()
                .is_empty()
        );
    }
    // ASH_INPUT169_END_TESTS
}
