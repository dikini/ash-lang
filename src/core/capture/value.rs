//! Finite stored-value equations. All edges refer to static expressions or
//! slots; closure captures never contain recursively owned environments.

use std::collections::{HashMap, HashSet, VecDeque};

use super::{Failure, MetadataVariables, charge, copy_slice, index, retain_function_metadata};
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
                handle,
                identity,
                initializer,
                body,
                source,
            } => Self::Resource {
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

#[derive(Debug)]
pub(super) struct Graph {
    expressions: Vec<Expr>,
    globals: Vec<(usize, usize)>,
    sources: Vec<Span>,
    exports: Vec<(BinderId, usize)>,
    positions: HashMap<usize, usize>,
    targets: HashMap<usize, usize>,
    evidence: Vec<(
        (crate::interface::RequirementId, crate::interface::MethodId),
        usize,
    )>,
}

pub(super) struct CallSuccessors {
    pub(super) targets: Vec<(usize, usize)>,
    pub(super) unknown: bool,
    pub(super) returns: bool,
}

impl Graph {
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

    fn evidence_slot(
        &mut self,
        requirement: crate::interface::RequirementId,
        method: crate::interface::MethodId,
        source: Span,
        budget: &mut TypeWorkBudget,
    ) -> Result<usize, Failure> {
        charge(budget, self.evidence.len() + 1)?;
        if let Some((_, slot)) = self
            .evidence
            .iter()
            .find(|(key, _)| *key == (requirement, method))
        {
            return Ok(*slot);
        }
        let slot = self.push(Expr::Slot, source, budget)?;
        self.evidence
            .try_reserve(1)
            .map_err(|_| Failure::Resource)?;
        self.evidence.push(((requirement, method), slot));
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
        methods: &[super::MethodUse],
        adapters: &[super::MethodAdapter],
        symbols: &mut HashMap<BinderId, usize>,
        captures: &mut Vec<usize>,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        let mut pending = copy_slice(&[root], budget)?;
        let mut visited = HashSet::new();
        while let Some(id) = pending.pop() {
            charge(budget, methods.len() + 1)?;
            visited.try_reserve(1).map_err(|_| Failure::Resource)?;
            if !visited.insert(id) {
                continue;
            }
            for method in methods {
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
        methods: &[super::MethodUse],
        adapters: &[super::MethodAdapter],
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
                    budget,
                )? {
                    let slot = self.symbol(symbols, binder, source, budget)?;
                    captures.try_reserve(1).map_err(|_| Failure::Resource)?;
                    captures.push(slot);
                }
                let mut metadata = MetadataVariables::default();
                retain_function_metadata(
                    &mut metadata,
                    nodes,
                    index(function.body()),
                    operation,
                    budget,
                )?;
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
            Some(PureExprKind::Value(PureValue::Constructor(constructor))) => {
                Expr::Constructor(constructor.constructor())
            }
            Some(PureExprKind::Computation(computation)) => self.build_computation(
                computation,
                id,
                nodes,
                symbols,
                types,
                operation,
                methods,
                adapters,
                budget,
            )?,
            _ => self.build_operation(
                id, nodes, symbols, types, operation, methods, adapters, budget,
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
        operation: fn(&F::Kind) -> Option<&EffectOperation>,
        methods: &[super::MethodUse],
        adapters: &[super::MethodAdapter],
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
                    budget,
                )? {
                    let slot = self.symbol(symbols, binder, source, budget)?;
                    captures.try_reserve(1).map_err(|_| Failure::Resource)?;
                    captures.push(slot);
                }
                let mut metadata = MetadataVariables::default();
                retain_function_metadata(
                    &mut metadata,
                    nodes,
                    index(abstraction.body()),
                    operation,
                    budget,
                )?;
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

    #[allow(clippy::too_many_arguments)] // Borrowed phase inputs avoid another owning environment.
    fn build_operation<F: CoreOperationFamily>(
        &mut self,
        id: usize,
        nodes: &[StoredNode<F>],
        symbols: &mut HashMap<BinderId, usize>,
        types: &mut HashMap<crate::types::TypeVariableId, usize>,
        operation: fn(&F::Kind) -> Option<&EffectOperation>,
        methods: &[super::MethodUse],
        adapters: &[super::MethodAdapter],
        budget: &mut TypeWorkBudget,
    ) -> Result<Expr, Failure> {
        let node = nodes.get(id).ok_or(Failure::Invalid)?;
        let source = self.sources[id];
        Ok(match operation(&node.kind) {
            Some(EffectOperation::Cleanup(scope)) => Expr::Cleanup {
                body: index(scope.body),
                action: index(scope.action),
            },
            Some(EffectOperation::Registration(scope)) => Expr::Alias(index(scope.body)),
            Some(EffectOperation::Resource(resource)) => Expr::Resource {
                handle: self.symbol(symbols, resource.handle.id(), source, budget)?,
                identity: self.symbol(types, resource.acquisition.identity, source, budget)?,
                initializer: index(resource.initializer),
                body: index(resource.body),
                source: resource.acquisition.span,
            },
            Some(EffectOperation::Handler(handler)) => {
                charge(budget, handler.clauses().len())?;
                let mut clauses = Vec::new();
                clauses
                    .try_reserve(handler.clauses().len())
                    .map_err(|_| Failure::Resource)?;
                for clause in handler.clauses() {
                    let input = self.push(Expr::Slot, source, budget)?;
                    let bindings = self.pattern(clause.pattern(), input, symbols, budget)?;
                    let mut captures = Vec::new();
                    for binder in super::free_values_with_methods(
                        nodes,
                        index(clause.body()),
                        &[],
                        methods,
                        budget,
                    )? {
                        let slot = self.symbol(symbols, binder, source, budget)?;
                        charge(budget, bindings.len())?;
                        if !bindings.iter().any(|(bound, _)| *bound == slot) {
                            captures.try_reserve(1).map_err(|_| Failure::Resource)?;
                            captures.push(slot);
                        }
                    }
                    let mut metadata = MetadataVariables::default();
                    retain_function_metadata(
                        &mut metadata,
                        nodes,
                        index(clause.body()),
                        operation,
                        budget,
                    )?;
                    for variable in metadata.variables {
                        let slot = self.symbol(types, variable, source, budget)?;
                        captures.try_reserve(1).map_err(|_| Failure::Resource)?;
                        captures.push(slot);
                    }
                    self.abstract_captures(
                        nodes,
                        index(clause.body()),
                        methods,
                        adapters,
                        symbols,
                        &mut captures,
                        budget,
                    )?;
                    clauses.push(DataClause {
                        input,
                        bindings,
                        body: index(clause.body()),
                        captures,
                    });
                }
                Expr::Handler {
                    body: index(handler.body()),
                    clauses,
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
    pub(super) fn build<F: CoreOperationFamily>(
        nodes: &[StoredNode<F>],
        globals: &[(BinderId, crate::core::NodeId)],
        imports: &[(BinderId, &super::CaptureValueSummary)],
        imported_callables: &super::ImportedCallables<'_>,
        operation: fn(&F::Kind) -> Option<&EffectOperation>,
        methods: &[super::MethodUse],
        adapters: &[super::MethodAdapter],
        budget: &mut TypeWorkBudget,
    ) -> Result<Self, Failure> {
        let mut graph = Self {
            expressions: Vec::new(),
            globals: Vec::new(),
            sources: Vec::new(),
            exports: Vec::new(),
            positions: HashMap::new(),
            targets: HashMap::new(),
            evidence: Vec::new(),
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
            graph.expressions.push(Expr::Scalar);
            graph
                .sources
                .push(node.origin.as_ref().ok_or(Failure::Invalid)?.primary_span());
        }
        let mut symbols = HashMap::new();
        let mut types = HashMap::new();
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
            graph.position(id + 1, id, budget)?;
            let source = graph.sources[id];
            graph.expressions[id] = graph.build_expression(
                id,
                nodes,
                &mut symbols,
                &mut types,
                operation,
                methods,
                adapters,
                budget,
            )?;
            charge(budget, methods.len())?;
            if let Some(method) = methods
                .iter()
                .find(|method| index(method.node) == id && method.requirement.is_none())
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
            for method in methods {
                charge(budget, 1)?;
                if index(method.node) == id
                    && let Some(requirement) = method.requirement
                {
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
                let offset = graph.expressions.len();
                charge(budget, imported.expressions.len() + imported.globals.len())?;
                graph
                    .expressions
                    .try_reserve(imported.expressions.len())
                    .map_err(|_| Failure::Resource)?;
                graph
                    .sources
                    .try_reserve(imported.sources.len())
                    .map_err(|_| Failure::Resource)?;
                for expression in &imported.expressions {
                    graph.expressions.push(expression.copy(offset, budget)?);
                }
                graph.sources.extend_from_slice(&imported.sources);
                graph
                    .globals
                    .try_reserve(imported.globals.len())
                    .map_err(|_| Failure::Resource)?;
                graph.globals.extend(
                    imported
                        .globals
                        .iter()
                        .map(|(binder, value)| (binder + offset, value + offset)),
                );
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
                for (&code, &expression) in &imported.positions {
                    graph.position(code + code_offset, expression + offset, budget)?;
                }
                charge(budget, imported.targets.len())?;
                graph
                    .targets
                    .try_reserve(imported.targets.len())
                    .map_err(|_| Failure::Resource)?;
                graph.targets.extend(
                    imported
                        .targets
                        .iter()
                        .map(|(expression, target)| (expression + offset, target + target_offset)),
                );
                charge(budget, imported.evidence.len())?;
                graph
                    .evidence
                    .try_reserve(imported.evidence.len())
                    .map_err(|_| Failure::Resource)?;
                graph.evidence.extend(
                    imported
                        .evidence
                        .iter()
                        .map(|(key, slot)| (*key, slot + offset)),
                );
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
    matches!(ty, Type::Int | Type::Bool | Type::Unit)
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
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Transition {
    Root(usize),
    Call(usize),
    Dispatch(usize, usize, usize),
    Focus,
    Restore(usize, usize, usize),
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

pub(super) struct Analysis<'a> {
    graph: &'a Graph,
    contexts: Vec<Vec<Transition>>,
    context_indices: HashMap<Vec<Transition>, usize>,
    slots: Vec<Slot>,
    indices: HashMap<(usize, usize), usize>,
    roots: HashMap<usize, usize>,
    revision: usize,
    pending: VecDeque<usize>,
    current: Option<usize>,
    frozen_contexts: usize,
    focus: Option<(usize, usize)>,
    cuts: HashMap<(usize, usize, usize), PreparedCut>,
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
            self.edge(result, input, budget)?;
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
            handle,
            identity,
            body,
            ..
        } = self.graph.expressions[expression]
        else {
            return Err(Failure::Invalid);
        };
        let mut query = Self::new(self.graph, budget)?;
        query.contexts.clear();
        query.context_indices.clear();
        charge(budget, self.contexts.len() + self.slots.len())?;
        query
            .contexts
            .try_reserve(self.contexts.len())
            .map_err(|_| Failure::Resource)?;
        query
            .context_indices
            .try_reserve(self.contexts.len())
            .map_err(|_| Failure::Resource)?;
        for context in &self.contexts {
            charge(budget, context.len() + 1)?;
            query
                .context_indices
                .insert(copy_slice(context, budget)?, query.contexts.len());
            query.contexts.push(copy_slice(context, budget)?);
        }
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
            query.indices.insert(slot.key, query.slots.len());
            query.slots.push(Slot {
                key: slot.key,
                atoms: copy_slice(&slot.atoms, budget)?,
                edges: Vec::new(),
                readers: Vec::new(),
                queued: false,
                terminal: true,
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
        query.link(result, body, context, budget)?;
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

    pub(super) fn revision(&self) -> usize {
        self.revision
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
                    let target = *self.graph.targets.get(&target).ok_or(Failure::Invalid)?;
                    let context = self.context(context, Transition::Call(expression), budget)?;
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
        charge(budget, 2)?;
        let mut contexts = Vec::new();
        contexts.try_reserve(1).map_err(|_| Failure::Resource)?;
        contexts.push(Vec::new());
        let mut context_indices = HashMap::new();
        context_indices
            .try_reserve(1)
            .map_err(|_| Failure::Resource)?;
        context_indices.insert(Vec::new(), 0);
        Ok(Self {
            graph,
            contexts,
            context_indices,
            slots: Vec::new(),
            indices: HashMap::new(),
            roots: HashMap::new(),
            revision: 0,
            pending: VecDeque::new(),
            current: None,
            frozen_contexts: 0,
            focus: None,
            cuts: HashMap::new(),
        })
    }

    fn context(
        &mut self,
        parent: usize,
        call: Transition,
        budget: &mut TypeWorkBudget,
    ) -> Result<usize, Failure> {
        let path = &self.contexts[parent];
        charge(budget, path.len() + 1)?;
        let repeated = path.iter().position(|site| *site == call);
        let mut context = copy_slice(
            &path[..repeated.map_or(path.len(), |index| index + 1)],
            budget,
        )?;
        if repeated.is_none() {
            context.try_reserve(1).map_err(|_| Failure::Resource)?;
            context.push(call);
        }
        charge(budget, context.len() + 1)?;
        if let Some(&id) = self.context_indices.get(&context) {
            return Ok(id);
        }
        self.contexts
            .try_reserve(1)
            .map_err(|_| Failure::Resource)?;
        self.context_indices
            .try_reserve(1)
            .map_err(|_| Failure::Resource)?;
        let id = self.contexts.len();
        charge(budget, context.len() + 1)?;
        self.context_indices
            .insert(copy_slice(&context, budget)?, id);
        self.contexts.push(context);
        self.revision += 1;
        Ok(id)
    }

    fn slot(
        &mut self,
        expression: usize,
        context: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<usize, Failure> {
        charge(budget, 1)?;
        let key = (expression, context);
        if let Some(&id) = self.indices.get(&key) {
            if let Some(reader) = self.current {
                self.watch(id, reader, budget)?;
            }
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
        });
        self.indices.insert(key, id);
        self.revision += 1;
        self.enqueue(id, budget)?;
        if let Some(reader) = self.current {
            self.watch(id, reader, budget)?;
        }
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
        charge(budget, self.slots[source].readers.len() + 1)?;
        if !self.slots[source].readers.contains(&reader) {
            self.slots[source]
                .readers
                .try_reserve(1)
                .map_err(|_| Failure::Resource)?;
            self.slots[source].readers.push(reader);
        }
        Ok(())
    }

    fn atom(
        &mut self,
        slot: usize,
        atom: Atom,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        charge(budget, self.slots[slot].atoms.len() + 1)?;
        if !self.slots[slot].atoms.contains(&atom) {
            self.slots[slot]
                .atoms
                .try_reserve(1)
                .map_err(|_| Failure::Resource)?;
            self.slots[slot].atoms.push(atom);
            self.revision += 1;
            for reader in copy_slice(&self.slots[slot].readers, budget)? {
                self.enqueue(reader, budget)?;
            }
        }
        Ok(())
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
        charge(budget, self.slots[target].edges.len() + 1)?;
        if !self.slots[target].edges.contains(&source) {
            self.slots[target]
                .edges
                .try_reserve(1)
                .map_err(|_| Failure::Resource)?;
            self.slots[target].edges.push(source);
            self.revision += 1;
            self.watch(source, target, budget)?;
            self.enqueue(target, budget)?;
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
            if !self.slots[slot].terminal {
                self.evaluate(slot, budget)?;
            }
            for source in copy_slice(&self.slots[slot].edges, budget)? {
                for atom in copy_slice(&self.slots[source].atoms, budget)? {
                    self.atom(slot, atom, budget)?;
                }
            }
            self.current = None;
        }
        Ok(())
    }

    fn evaluate(&mut self, slot: usize, budget: &mut TypeWorkBudget) -> Result<(), Failure> {
        let (expression, context) = self.slots[slot].key;
        match &self.graph.expressions[expression] {
            Expr::Scalar => self.atom(slot, Atom::Free, budget)?,
            Expr::Slot => {}
            Expr::Unknown => self.atom(slot, Atom::Unknown, budget)?,
            Expr::Alias(value) => self.link(slot, *value, context, budget)?,
            Expr::Merge(values) => {
                self.atom(slot, Atom::Free, budget)?;
                for value in values {
                    self.link(slot, *value, context, budget)?;
                }
            }
            Expr::Function { captures, body, .. } => {
                for capture in captures {
                    let source = self.slot(*capture, context, budget)?;
                    if let Some(root) = self.roots.get(body).copied() {
                        let target = self.slot(*capture, root, budget)?;
                        self.edge(target, source, budget)?;
                    }
                }
                self.atom(slot, Atom::Closure(expression, context), budget)?;
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
                if ready {
                    self.atom(slot, Atom::Aggregate(expression, context), budget)?;
                }
            }
            Expr::Call {
                function,
                arguments,
                scalar,
                type_application,
            } => {
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
                    return Ok(());
                }
                for atom in copy_slice(&self.slots[function].atoms, budget)? {
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
                            let invoked =
                                self.context(context, Transition::Call(expression), budget)?;
                            for (&parameter, &argument) in parameters.iter().zip(&actual) {
                                let parameter = self.slot(parameter, invoked, budget)?;
                                self.edge(parameter, argument, budget)?;
                            }
                            for capture in captures {
                                let destination = self.slot(*capture, invoked, budget)?;
                                let source = self.slot(*capture, creation, budget)?;
                                self.edge(destination, source, budget)?;
                            }
                            self.link(slot, *body, invoked, budget)?;
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
                let value = self.slot(*value, context, budget)?;
                for atom in copy_slice(&self.slots[value].atoms, budget)? {
                    match atom {
                        Atom::Aggregate(target, creation) => {
                            match &self.graph.expressions[target] {
                                Expr::Tuple(fields) if constructor.is_none() => {
                                    if let Some(value) = fields.get(*field) {
                                        self.link(slot, *value, creation, budget)?;
                                    }
                                }
                                Expr::Call { arguments, .. }
                                    if constructor.is_some() && *field == 0 =>
                                {
                                    if let Some(value) = arguments.first() {
                                        self.link(slot, *value, creation, budget)?;
                                    }
                                }
                                _ => {}
                            }
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
                if !self.slots[body].atoms.is_empty() {
                    let action = self.slot(*action, context, budget)?;
                    if !self.slots[action].atoms.is_empty() {
                        self.edge(slot, body, budget)?;
                    }
                }
            }
            Expr::Bind {
                binder,
                initializer,
                body,
            } => {
                let binder = self.slot(*binder, context, budget)?;
                self.link(binder, *initializer, context, budget)?;
                if !self.slots[binder].atoms.is_empty() {
                    self.link(slot, *body, context, budget)?;
                }
            }
            Expr::Recursive { bindings, body } => {
                let mut ready = true;
                for &(binder, initializer) in bindings {
                    let binder = self.slot(binder, context, budget)?;
                    let initializer = self.slot(initializer, context, budget)?;
                    self.edge(binder, initializer, budget)?;
                    ready &= !self.slots[initializer].atoms.is_empty();
                }
                if ready {
                    self.link(slot, *body, context, budget)?;
                }
            }
            Expr::Match { scrutinee, arms } => {
                let scrutinee = self.slot(*scrutinee, context, budget)?;
                if self.slots[scrutinee].atoms.is_empty() {
                    return Ok(());
                }
                for (bindings, body) in arms {
                    for &(binder, initializer) in bindings {
                        let binder = self.slot(binder, context, budget)?;
                        self.link(binder, initializer, context, budget)?;
                    }
                    self.link(slot, *body, context, budget)?;
                }
            }
            Expr::Resource {
                handle,
                identity,
                initializer,
                body,
                ..
            } => {
                let initializer = self.slot(*initializer, context, budget)?;
                if self.slots[initializer].atoms.is_empty() {
                    return Ok(());
                }
                let handle = self.slot(*handle, context, budget)?;
                let identity = self.slot(*identity, context, budget)?;
                self.atom(handle, Atom::Resource(expression, context), budget)?;
                self.atom(identity, Atom::Resource(expression, context), budget)?;
                self.link(slot, *body, context, budget)?;
            }
            Expr::Request { operand, scalar } => {
                self.slot(*operand, context, budget)?;
                let _ = scalar;
            }
            Expr::Resume { operand } => {
                self.slot(*operand, context, budget)?;
            }
            Expr::Handler { body, .. } => self.link(slot, *body, context, budget)?,
            Expr::Evidence { value, bindings } => {
                let value = self.slot(*value, context, budget)?;
                for (_, _, argument) in bindings {
                    self.slot(*argument, context, budget)?;
                }
                for atom in copy_slice(&self.slots[value].atoms, budget)? {
                    if let Atom::Closure(target, creation) = atom {
                        let specialized =
                            self.context(context, Transition::Call(expression), budget)?;
                        let Expr::Function { captures, .. } = &self.graph.expressions[target]
                        else {
                            return Err(Failure::Invalid);
                        };
                        self.specialize_captures(
                            captures,
                            creation,
                            specialized,
                            bindings,
                            context,
                            budget,
                        )?;
                        for (requirement, method, argument) in bindings {
                            charge(budget, self.graph.evidence.len())?;
                            for (key, target) in &self.graph.evidence {
                                if *key == (*requirement, *method) {
                                    let target = self.slot(*target, specialized, budget)?;
                                    self.link(target, *argument, context, budget)?;
                                }
                            }
                        }
                        self.atom(slot, Atom::Closure(target, specialized), budget)?;
                    } else {
                        self.atom(slot, atom, budget)?;
                        if matches!(atom, Atom::Unknown) {
                            for (_, _, argument) in bindings {
                                let argument = self.slot(*argument, context, budget)?;
                                for dependency in self.dependencies(argument, budget)? {
                                    self.atom(slot, dependency, budget)?;
                                }
                            }
                        }
                    }
                }
            }
        }
        Ok(())
    }

    fn specialize_captures(
        &mut self,
        captures: &[usize],
        creation: usize,
        specialized: usize,
        bindings: &[(
            crate::interface::RequirementId,
            crate::interface::MethodId,
            usize,
        )],
        arguments_context: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        let mut pending = copy_slice(captures, budget)?;
        let mut visited = HashSet::new();
        while let Some(capture) = pending.pop() {
            charge(budget, 1)?;
            visited.try_reserve(1).map_err(|_| Failure::Resource)?;
            if !visited.insert(capture) {
                continue;
            }
            let destination = self.slot(capture, specialized, budget)?;
            let mut replaced = false;
            for (key, port) in &self.graph.evidence {
                charge(budget, bindings.len() + 1)?;
                if *port != capture {
                    continue;
                }
                for (requirement, method, argument) in bindings {
                    if *key == (*requirement, *method) {
                        self.link(destination, *argument, arguments_context, budget)?;
                        replaced = true;
                    }
                }
            }
            if replaced {
                continue;
            }
            // Only inert occurrence expressions are rebuilt. Their terminal slots
            // keep lexical captures; exact abstract ports receive the selected methods.
            match &self.graph.expressions[capture] {
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
                _ => self.link(destination, capture, creation, budget)?,
            }
        }
        Ok(())
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
            for atom in copy_slice(&self.slots[slot].atoms, budget)? {
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
            exports: Vec::new(),
            positions: HashMap::new(),
            targets: HashMap::new(),
            evidence: Vec::new(),
        }
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
            // Two singleton copy_slice owners cost two each, plus pop and atom visits.
            let prefix = if shape == 0 { 0 } else { 6 };
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
            let result = graph.build_operation(
                1,
                &nodes,
                &mut HashMap::new(),
                &mut HashMap::new(),
                |kind| match kind {
                    EffectExprKind::Operation(operation) => Some(operation),
                    _ => None,
                },
                &[],
                &[],
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
    fn strict_results_wait_for_bottom_inputs_and_wake_on_late_values() {
        for shape in 0..5 {
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
                    handle: 7,
                    identity: 8,
                    initializer: 0,
                    body: 3,
                    source: graph.sources[6],
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
        let (mut focused, context) = normal.focused(6, 0, &mut budget).unwrap();
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
}
