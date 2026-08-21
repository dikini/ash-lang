//! Independent validation for unchecked pure Core arenas.

use std::{collections::HashMap, error::Error, fmt};

use super::{
    dialect::{
        DialectId, NodeId, PureComputation, PureExprKind, PureProgram, PureValue, StoredNode,
        TypedExpr, UnvalidatedProgram, ValidatedProgram,
    },
    variable::TypedBinder,
};
use crate::{
    resolved::BinderId,
    source::{Origin, SourceFile, SourceId, Span},
    types::Type,
};

/// The independently checked invariant that malformed Core violated.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ValidationReason {
    /// A variable or binder identity violates lexical scope.
    Scope,
    /// A node or binder has an inconsistent structural type.
    NodeType,
    /// An application disagrees with its function domain or codomain.
    ApplicationType,
    /// A recursive binding violates its group-shape invariants.
    RecursiveBinding,
    /// Required causal source provenance is missing or invalid.
    Provenance,
    /// A stored node does not belong to the selected pure dialect.
    DialectMembership,
    /// A node refers outside its arena.
    NodeBounds,
    /// The expression graph contains a cycle.
    Cycle,
    /// The selected root does not belong to the arena.
    Root,
    /// The arena contains a node unreachable from its selected root.
    Unreachable,
}

impl fmt::Display for ValidationReason {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::Scope => "core.validation.scope",
            Self::NodeType => "core.validation.node-type",
            Self::ApplicationType => "core.validation.application-type",
            Self::RecursiveBinding => "core.validation.recursive-binding",
            Self::Provenance => "core.validation.provenance",
            Self::DialectMembership => "core.validation.dialect-membership",
            Self::NodeBounds => "core.validation.node-bounds",
            Self::Cycle => "core.validation.cycle",
            Self::Root => "core.validation.root",
            Self::Unreachable => "core.validation.unreachable",
        })
    }
}

/// A structured internal compiler failure produced by Core validation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ValidationError {
    reason: ValidationReason,
    node: Option<NodeId>,
}

impl ValidationError {
    const fn new(reason: ValidationReason, node: Option<NodeId>) -> Self {
        Self { reason, node }
    }

    /// Returns the violated invariant category.
    #[must_use]
    pub const fn reason(&self) -> ValidationReason {
        self.reason
    }

    /// Returns the arena node associated with the failure, when available.
    #[must_use]
    pub const fn node(&self) -> Option<NodeId> {
        self.node
    }
}

impl fmt::Display for ValidationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.node {
            Some(node) => write!(formatter, "{} at Core node {}", self.reason, node.value()),
            None => self.reason.fmt(formatter),
        }
    }
}

impl Error for ValidationError {}

/// Consumes unchecked Core and returns the capability required by consumers.
///
/// `sources` is the complete set admitted to the current compilation. Every
/// node and binder origin must lead to a checked span in that set.
///
/// # Errors
///
/// Returns a structured internal failure if graph, scope, type, dialect, or
/// provenance invariants do not hold.
pub fn validate(
    program: UnvalidatedProgram,
    sources: &[&SourceFile],
) -> Result<ValidatedProgram, ValidationError> {
    Validator::new(&program, sources).run()?;

    let mut nodes = Vec::with_capacity(program.nodes.len());
    for (index, stored) in program.nodes.into_iter().enumerate() {
        let node = node_id(program.arena, index)?;
        let Some(origin) = stored.origin else {
            return Err(ValidationError::new(
                ValidationReason::Provenance,
                Some(node),
            ));
        };
        nodes.push(TypedExpr {
            ty: stored.ty,
            origin,
            kind: stored.kind,
        });
    }

    Ok(ValidatedProgram::new(PureProgram::new(
        program.arena,
        nodes,
        program.root,
    )))
}

struct Validator<'program, 'source> {
    program: &'program UnvalidatedProgram,
    sources: HashMap<SourceId, &'source SourceFile>,
    binders: HashMap<BinderId, &'program TypedBinder>,
}

impl<'program, 'source> Validator<'program, 'source> {
    fn new(program: &'program UnvalidatedProgram, sources: &[&'source SourceFile]) -> Self {
        Self {
            program,
            sources: sources
                .iter()
                .map(|source| (source.id(), *source))
                .collect(),
            binders: HashMap::new(),
        }
    }

    fn run(mut self) -> Result<(), ValidationError> {
        self.validate_envelopes()?;
        self.validate_graph()?;
        self.collect_binders()?;
        self.validate_node_types()?;
        self.validate_scopes()
    }

    fn validate_envelopes(&self) -> Result<(), ValidationError> {
        for (index, node) in self.program.nodes.iter().enumerate() {
            let id = node_id(self.program.arena, index)?;
            if node.dialect != DialectId::PURE {
                return Err(ValidationError::new(
                    ValidationReason::DialectMembership,
                    Some(id),
                ));
            }
            let Some(origin) = node.origin.as_ref() else {
                return Err(ValidationError::new(ValidationReason::Provenance, Some(id)));
            };
            self.validate_origin(origin, id)?;
        }
        Ok(())
    }

    fn validate_origin(&self, origin: &Origin, node: NodeId) -> Result<(), ValidationError> {
        let mut work = vec![origin];
        while let Some(current) = work.pop() {
            match current {
                Origin::Source(span) => self.validate_span(*span, node)?,
                Origin::Generated { cause, .. } => work.push(cause),
                Origin::Related { primary, related } => {
                    let primary_source = primary.primary_span().source();
                    for span in related {
                        if span.source() != primary_source {
                            return Err(ValidationError::new(
                                ValidationReason::Provenance,
                                Some(node),
                            ));
                        }
                        self.validate_span(*span, node)?;
                    }
                    work.push(primary);
                }
            }
        }
        Ok(())
    }

    fn validate_span(&self, span: Span, node: NodeId) -> Result<(), ValidationError> {
        let Some(source) = self.sources.get(&span.source()) else {
            return Err(ValidationError::new(
                ValidationReason::Provenance,
                Some(node),
            ));
        };
        source
            .span(span.range())
            .map_err(|_| ValidationError::new(ValidationReason::Provenance, Some(node)))?;
        Ok(())
    }

    fn validate_graph(&self) -> Result<(), ValidationError> {
        if self.node(self.program.root).is_err() {
            return Err(ValidationError::new(ValidationReason::Root, None));
        }

        let mut colors = vec![Color::White; self.program.nodes.len()];
        let mut work = vec![GraphTask::Enter(self.program.root)];
        while let Some(task) = work.pop() {
            match task {
                GraphTask::Enter(id) => {
                    let index = self.index(id)?;
                    match colors[index] {
                        Color::Gray => {
                            return Err(ValidationError::new(ValidationReason::Cycle, Some(id)));
                        }
                        Color::Black => continue,
                        Color::White => {}
                    }
                    colors[index] = Color::Gray;
                    work.push(GraphTask::Exit(id));
                    let node = self.node(id)?;
                    for child_index in (0..node.kind.child_count()).rev() {
                        let Some(child) = node.kind.child_at(child_index) else {
                            return Err(ValidationError::new(
                                ValidationReason::NodeBounds,
                                Some(id),
                            ));
                        };
                        if self.node(child).is_err() {
                            return Err(ValidationError::new(
                                ValidationReason::NodeBounds,
                                Some(id),
                            ));
                        }
                        work.push(GraphTask::Enter(child));
                    }
                }
                GraphTask::Exit(id) => {
                    let index = self.index(id)?;
                    colors[index] = Color::Black;
                }
            }
        }

        if let Some(index) = colors.iter().position(|color| *color == Color::White) {
            return Err(ValidationError::new(
                ValidationReason::Unreachable,
                Some(node_id(self.program.arena, index)?),
            ));
        }
        Ok(())
    }

    fn collect_binders(&mut self) -> Result<(), ValidationError> {
        for (index, node) in self.program.nodes.iter().enumerate() {
            let id = node_id(self.program.arena, index)?;
            match &node.kind {
                PureExprKind::Value(PureValue::Function(function)) => {
                    self.collect_binder(id, function.parameter())?;
                }
                PureExprKind::Computation(PureComputation::Bind(binding)) => {
                    self.collect_binder(id, binding.binder())?;
                }
                PureExprKind::Computation(PureComputation::RecursiveBind(group)) => {
                    for member in group.members() {
                        self.collect_binder(id, member.binder())?;
                    }
                }
                PureExprKind::Value(
                    PureValue::Integer(_) | PureValue::Boolean(_) | PureValue::Unit(_),
                )
                | PureExprKind::Variable(_)
                | PureExprKind::Computation(
                    PureComputation::Apply(_) | PureComputation::Primitive(_),
                ) => {}
            }
        }
        Ok(())
    }

    fn collect_binder(
        &mut self,
        node: NodeId,
        binder: &'program TypedBinder,
    ) -> Result<(), ValidationError> {
        if binder.arena() != self.program.arena {
            return Err(ValidationError::new(ValidationReason::Scope, Some(node)));
        }
        self.validate_origin(binder.origin(), node)?;
        if self.binders.insert(binder.id(), binder).is_some() {
            return Err(ValidationError::new(ValidationReason::Scope, Some(node)));
        }
        Ok(())
    }

    fn validate_node_types(&self) -> Result<(), ValidationError> {
        for (index, node) in self.program.nodes.iter().enumerate() {
            let id = node_id(self.program.arena, index)?;
            match &node.kind {
                PureExprKind::Value(value) => self.validate_value(id, node, value)?,
                PureExprKind::Variable(variable) => {
                    let Some(binder) = self.binders.get(&variable.binder()) else {
                        return Err(ValidationError::new(ValidationReason::Scope, Some(id)));
                    };
                    if node.ty != *binder.ty() {
                        return Err(ValidationError::new(ValidationReason::NodeType, Some(id)));
                    }
                }
                PureExprKind::Computation(computation) => {
                    self.validate_computation(id, node, computation)?;
                }
            }
        }
        Ok(())
    }

    fn validate_value(
        &self,
        id: NodeId,
        node: &StoredNode,
        value: &PureValue,
    ) -> Result<(), ValidationError> {
        let expected = match value {
            PureValue::Integer(integer) => integer.expected_type(),
            PureValue::Boolean(boolean) => boolean.expected_type(),
            PureValue::Unit(unit) => unit.expected_type(),
            PureValue::Function(function) => {
                let body = self.node(function.body())?;
                Type::Function(
                    Box::new(function.parameter().ty().clone()),
                    Box::new(body.ty.clone()),
                )
            }
        };
        if node.ty != expected {
            return Err(ValidationError::new(ValidationReason::NodeType, Some(id)));
        }
        Ok(())
    }

    fn validate_computation(
        &self,
        id: NodeId,
        node: &StoredNode,
        computation: &PureComputation,
    ) -> Result<(), ValidationError> {
        match computation {
            PureComputation::Bind(binding) => {
                let initializer = self.node(binding.initializer())?;
                let body = self.node(binding.body())?;
                if initializer.ty != *binding.binder().ty() || node.ty != body.ty {
                    return Err(ValidationError::new(ValidationReason::NodeType, Some(id)));
                }
            }
            PureComputation::RecursiveBind(group) => {
                if group.members().is_empty() {
                    return Err(ValidationError::new(
                        ValidationReason::RecursiveBinding,
                        Some(id),
                    ));
                }
                for member in group.members() {
                    let initializer = self.node(member.initializer())?;
                    if !matches!(
                        initializer.kind,
                        PureExprKind::Value(PureValue::Function(_))
                    ) {
                        return Err(ValidationError::new(
                            ValidationReason::RecursiveBinding,
                            Some(id),
                        ));
                    }
                    if initializer.ty != *member.binder().ty() {
                        return Err(ValidationError::new(ValidationReason::NodeType, Some(id)));
                    }
                }
                let body = self.node(group.body())?;
                if node.ty != body.ty {
                    return Err(ValidationError::new(ValidationReason::NodeType, Some(id)));
                }
            }
            PureComputation::Apply(application) => {
                let function = self.node(application.function())?;
                let argument = self.node(application.argument())?;
                let Type::Function(domain, codomain) = &function.ty else {
                    return Err(ValidationError::new(
                        ValidationReason::ApplicationType,
                        Some(id),
                    ));
                };
                if domain.as_ref() != &argument.ty || codomain.as_ref() != &node.ty {
                    return Err(ValidationError::new(
                        ValidationReason::ApplicationType,
                        Some(id),
                    ));
                }
            }
            PureComputation::Primitive(primitive) => {
                let left = self.node(primitive.left())?;
                let right = self.node(primitive.right())?;
                let (left_type, right_type, result_type) = primitive.primitive().signature();
                if left.ty != left_type || right.ty != right_type || node.ty != result_type {
                    return Err(ValidationError::new(ValidationReason::NodeType, Some(id)));
                }
            }
        }
        Ok(())
    }

    fn validate_scopes(&self) -> Result<(), ValidationError> {
        let analysis = self.analyze_free_binders()?;
        if analysis.analyzed_nodes != self.program.nodes.len() {
            return Err(ValidationError::new(ValidationReason::Scope, None));
        }
        if let Some(occurrence) = analysis
            .root_requirements
            .values()
            .min_by_key(|node| node.value())
        {
            return Err(ValidationError::new(
                ValidationReason::Scope,
                Some(*occurrence),
            ));
        }
        Ok(())
    }

    fn analyze_free_binders(&self) -> Result<ScopeAnalysis, ValidationError> {
        let mut scheduled = vec![false; self.program.nodes.len()];
        let mut requirements = vec![None; self.program.nodes.len()];
        let mut work = vec![ScopeAnalysisTask::Enter(self.program.root)];
        let mut analyzed_nodes = 0;

        while let Some(task) = work.pop() {
            match task {
                ScopeAnalysisTask::Enter(id) => {
                    let index = self.index(id)?;
                    if scheduled[index] {
                        continue;
                    }
                    scheduled[index] = true;
                    work.push(ScopeAnalysisTask::Finish(id));
                    let kind = &self.node(id)?.kind;
                    for child_index in (0..kind.child_count()).rev() {
                        let child = kind.child_at(child_index).ok_or_else(|| {
                            ValidationError::new(ValidationReason::Scope, Some(id))
                        })?;
                        work.push(ScopeAnalysisTask::Enter(child));
                    }
                }
                ScopeAnalysisTask::Finish(id) => {
                    let node = self.node(id)?;
                    let free = match &node.kind {
                        PureExprKind::Variable(variable) => {
                            HashMap::from([(variable.binder(), id)])
                        }
                        PureExprKind::Value(PureValue::Function(function)) => {
                            let mut body = self.requirements_for(&requirements, function.body())?;
                            body.remove(&function.parameter().id());
                            body
                        }
                        PureExprKind::Computation(PureComputation::Bind(binding)) => {
                            let initializer =
                                self.requirements_for(&requirements, binding.initializer())?;
                            let mut body = self.requirements_for(&requirements, binding.body())?;
                            body.remove(&binding.binder().id());
                            union_requirements(initializer, body)
                        }
                        PureExprKind::Computation(PureComputation::RecursiveBind(group)) => {
                            let mut free = self.requirements_for(&requirements, group.body())?;
                            for member in group.members() {
                                let initializer =
                                    self.requirements_for(&requirements, member.initializer())?;
                                free = union_requirements(free, initializer);
                            }
                            for member in group.members() {
                                free.remove(&member.binder().id());
                            }
                            free
                        }
                        PureExprKind::Computation(PureComputation::Apply(application)) => {
                            let function =
                                self.requirements_for(&requirements, application.function())?;
                            let argument =
                                self.requirements_for(&requirements, application.argument())?;
                            union_requirements(function, argument)
                        }
                        PureExprKind::Computation(PureComputation::Primitive(primitive)) => {
                            let left = self.requirements_for(&requirements, primitive.left())?;
                            let right = self.requirements_for(&requirements, primitive.right())?;
                            union_requirements(left, right)
                        }
                        PureExprKind::Value(
                            PureValue::Integer(_) | PureValue::Boolean(_) | PureValue::Unit(_),
                        ) => HashMap::new(),
                    };
                    let index = self.index(id)?;
                    requirements[index] = Some(free);
                    analyzed_nodes += 1;
                }
            }
        }

        let root_index = self.index(self.program.root)?;
        let Some(root_requirements) = requirements[root_index].take() else {
            return Err(ValidationError::new(ValidationReason::Scope, None));
        };
        Ok(ScopeAnalysis {
            root_requirements,
            analyzed_nodes,
        })
    }

    fn requirements_for(
        &self,
        requirements: &[Option<HashMap<BinderId, NodeId>>],
        id: NodeId,
    ) -> Result<HashMap<BinderId, NodeId>, ValidationError> {
        let index = self.index(id)?;
        let Some(free) = requirements.get(index).and_then(Option::as_ref) else {
            return Err(ValidationError::new(ValidationReason::Scope, Some(id)));
        };
        Ok(free.clone())
    }

    fn index(&self, id: NodeId) -> Result<usize, ValidationError> {
        if id.arena() != self.program.arena {
            return Err(ValidationError::new(ValidationReason::NodeBounds, Some(id)));
        }
        usize::try_from(id.value())
            .ok()
            .filter(|index| *index < self.program.nodes.len())
            .ok_or_else(|| ValidationError::new(ValidationReason::NodeBounds, Some(id)))
    }

    fn node(&self, id: NodeId) -> Result<&'program StoredNode, ValidationError> {
        let index = self.index(id)?;
        self.program
            .nodes
            .get(index)
            .ok_or_else(|| ValidationError::new(ValidationReason::NodeBounds, Some(id)))
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum Color {
    White,
    Gray,
    Black,
}

enum GraphTask {
    Enter(NodeId),
    Exit(NodeId),
}

struct ScopeAnalysis {
    root_requirements: HashMap<BinderId, NodeId>,
    analyzed_nodes: usize,
}

enum ScopeAnalysisTask {
    Enter(NodeId),
    Finish(NodeId),
}

fn union_requirements(
    mut left: HashMap<BinderId, NodeId>,
    right: HashMap<BinderId, NodeId>,
) -> HashMap<BinderId, NodeId> {
    for (binder, occurrence) in right {
        left.entry(binder).or_insert(occurrence);
    }
    left
}

fn node_id(arena: super::dialect::ArenaId, index: usize) -> Result<NodeId, ValidationError> {
    u32::try_from(index)
        .map(|index| NodeId::new(arena, index))
        .map_err(|_| ValidationError::new(ValidationReason::NodeBounds, None))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        core::{CoreBuilder, PureValue},
        source::ByteRange,
    };

    fn source() -> SourceFile {
        SourceFile::new("test.ash", "()").expect("test source")
    }

    fn origin(source: &SourceFile) -> Origin {
        let range = ByteRange::new(0, 2).expect("ordered range");
        Origin::Source(source.span(range).expect("source span"))
    }

    #[test]
    fn rejects_a_foreign_dialect_envelope_without_a_foreign_pure_variant() {
        let file = source();
        let mut builder = CoreBuilder::new();
        let root = builder
            .unit(Type::Unit, origin(&file))
            .expect("small arena");
        let mut program = builder.finish(root).expect("valid root");
        program.nodes[0].dialect = DialectId::FOREIGN;

        let error = validate(program, &[&file]).expect_err("foreign dialect");
        assert_eq!(error.reason(), ValidationReason::DialectMembership);
    }

    #[test]
    fn rejects_missing_provenance_before_projection() {
        let file = source();
        let mut builder = CoreBuilder::new();
        let root = builder
            .unit(Type::Unit, origin(&file))
            .expect("small arena");
        let mut program = builder.finish(root).expect("valid root");
        program.nodes[0].origin = None;

        let error = validate(program, &[&file]).expect_err("missing origin");
        assert_eq!(error.reason(), ValidationReason::Provenance);
    }

    #[test]
    fn rejects_a_root_outside_the_arena() {
        let file = source();
        let arena = super::super::dialect::ArenaId::new(100);
        let program = UnvalidatedProgram {
            arena,
            nodes: Vec::new(),
            root: NodeId::new(arena, 0),
        };

        let error = validate(program, &[&file]).expect_err("invalid root");
        assert_eq!(error.reason(), ValidationReason::Root);
        assert_eq!(error.node(), None);
    }

    #[test]
    fn rejects_a_privately_corrupted_foreign_binder_capability() {
        let file = source();
        let arena = super::super::dialect::ArenaId::new(102);
        let foreign_arena = super::super::dialect::ArenaId::new(103);
        let unit = StoredNode {
            dialect: DialectId::PURE,
            ty: Type::Unit,
            origin: Some(origin(&file)),
            kind: PureExprKind::Value(PureValue::Unit(super::super::literal::UnitNode)),
        };
        let function = StoredNode {
            dialect: DialectId::PURE,
            ty: Type::Function(Box::new(Type::Unit), Box::new(Type::Unit)),
            origin: Some(origin(&file)),
            kind: PureExprKind::Value(PureValue::Function(
                super::super::function::FunctionNode::new(
                    TypedBinder::new(foreign_arena, BinderId::new(0), Type::Unit, origin(&file)),
                    NodeId::new(arena, 0),
                ),
            )),
        };
        let program = UnvalidatedProgram {
            arena,
            nodes: vec![unit, function],
            root: NodeId::new(arena, 1),
        };

        let error = validate(program, &[&file]).expect_err("foreign binder capability");
        assert_eq!(error.reason(), ValidationReason::Scope);
        assert_eq!(error.node(), Some(NodeId::new(arena, 1)));
    }

    #[test]
    fn rejects_out_of_bounds_and_cycles_without_recursion() {
        let file = source();
        let arena = super::super::dialect::ArenaId::new(101);
        let stored = StoredNode {
            dialect: DialectId::PURE,
            ty: Type::Function(Box::new(Type::Unit), Box::new(Type::Unit)),
            origin: Some(origin(&file)),
            kind: PureExprKind::Value(PureValue::Function(
                super::super::function::FunctionNode::new(
                    TypedBinder::new(arena, BinderId::new(0), Type::Unit, origin(&file)),
                    NodeId::new(arena, 1),
                ),
            )),
        };
        let program = UnvalidatedProgram {
            arena,
            nodes: vec![stored],
            root: NodeId::new(arena, 0),
        };
        let error = validate(program, &[&file]).expect_err("out-of-bounds child");
        assert_eq!(error.reason(), ValidationReason::NodeBounds);

        let cyclic = StoredNode {
            dialect: DialectId::PURE,
            ty: Type::Function(Box::new(Type::Unit), Box::new(Type::Unit)),
            origin: Some(origin(&file)),
            kind: PureExprKind::Value(PureValue::Function(
                super::super::function::FunctionNode::new(
                    TypedBinder::new(arena, BinderId::new(0), Type::Unit, origin(&file)),
                    NodeId::new(arena, 0),
                ),
            )),
        };
        let program = UnvalidatedProgram {
            arena,
            nodes: vec![cyclic],
            root: NodeId::new(arena, 0),
        };
        let error = validate(program, &[&file]).expect_err("cycle");
        assert_eq!(error.reason(), ValidationReason::Cycle);
    }

    #[test]
    fn rejects_an_ownership_cycle_through_a_recursive_group_body() {
        let file = source();
        let arena = super::super::dialect::ArenaId::new(104);
        let node_origin = origin(&file);
        let function_type = Type::Function(Box::new(Type::Unit), Box::new(Type::Unit));
        let recursive = TypedBinder::new(
            arena,
            BinderId::new(0),
            function_type.clone(),
            node_origin.clone(),
        );
        let parameter = TypedBinder::new(arena, BinderId::new(1), Type::Unit, node_origin.clone());
        let group = StoredNode {
            dialect: DialectId::PURE,
            ty: Type::Unit,
            origin: Some(node_origin.clone()),
            kind: PureExprKind::Computation(PureComputation::RecursiveBind(
                super::super::recursion::RecursiveBindingNode::new(
                    vec![super::super::recursion::RecursiveBindingMember::new(
                        recursive,
                        NodeId::new(arena, 1),
                    )],
                    NodeId::new(arena, 0),
                ),
            )),
        };
        let function = StoredNode {
            dialect: DialectId::PURE,
            ty: function_type,
            origin: Some(node_origin.clone()),
            kind: PureExprKind::Value(PureValue::Function(
                super::super::function::FunctionNode::new(parameter, NodeId::new(arena, 2)),
            )),
        };
        let unit = StoredNode {
            dialect: DialectId::PURE,
            ty: Type::Unit,
            origin: Some(node_origin),
            kind: PureExprKind::Value(PureValue::Unit(super::super::literal::UnitNode)),
        };
        let program = UnvalidatedProgram {
            arena,
            nodes: vec![group, function, unit],
            root: NodeId::new(arena, 0),
        };

        let error = validate(program, &[&file]).expect_err("recursive ownership cycle");
        assert_eq!(error.reason(), ValidationReason::Cycle);
        assert_eq!(error.node(), Some(NodeId::new(arena, 0)));
    }

    #[test]
    fn validates_a_deep_arena_with_explicit_work_stacks() {
        let file = source();
        let node_origin = origin(&file);
        let mut builder = CoreBuilder::new();
        let initializer = builder
            .unit(Type::Unit, node_origin.clone())
            .expect("small initial arena");
        let mut root = initializer;
        for _ in 0..10_000 {
            let binder = builder
                .binder(Type::Unit, node_origin.clone())
                .expect("bounded binder set");
            root = builder
                .binding(binder, initializer, root, Type::Unit, node_origin.clone())
                .expect("bounded arena");
        }

        let validated = validate(builder.finish(root).expect("valid root"), &[&file])
            .expect("deep acyclic Core");
        assert_eq!(validated.node_count(), 10_001);
    }

    #[test]
    fn shared_dag_scope_analysis_visits_each_node_once() {
        let file = SourceFile::new("shared.ash", "1").expect("test source");
        let node_origin = Origin::Source(
            file.span(ByteRange::new(0, 1).expect("ordered range"))
                .expect("source span"),
        );
        let mut builder = CoreBuilder::new();
        let mut root = builder
            .integer(
                crate::integer::Integer::parse_decimal("1").expect("test integer"),
                Type::Int,
                node_origin.clone(),
            )
            .expect("small arena");
        for _ in 0..64 {
            root = builder
                .primitive(
                    crate::core::Primitive::Add,
                    root,
                    root,
                    Type::Int,
                    node_origin.clone(),
                )
                .expect("bounded arena");
        }
        let program = builder.finish(root).expect("valid root");
        let sources = [&file];
        let validator = Validator::new(&program, &sources);

        let analysis = validator.analyze_free_binders().expect("valid shared DAG");
        assert!(analysis.root_requirements.is_empty());
        assert_eq!(analysis.analyzed_nodes, program.nodes.len());
    }
}
