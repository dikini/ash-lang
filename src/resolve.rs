//! Lexical name resolution for recovery-free surface syntax.

use std::{collections::HashMap, fmt, ops::Deref, sync::Arc};

use crate::{
    diagnostic::{Diagnostic, SourceLabel},
    resolved::{
        Binder, BinderId, ResolvedApplicationExpr, ResolvedBinaryExpr, ResolvedBinding,
        ResolvedBlock, ResolvedConstructor, ResolvedConstructorOccurrence, ResolvedDefinition,
        ResolvedDefinitionKind, ResolvedEquation, ResolvedEquationalGlobal, ResolvedExpr,
        ResolvedExprKind, ResolvedExternalInterface, ResolvedFunctionExpr,
        ResolvedInlineOperationalGlobal, ResolvedInlineOperationalHeader, ResolvedLocalDeclaration,
        ResolvedMatchArm, ResolvedMatchExpr, ResolvedNominalType, ResolvedOccurrence,
        ResolvedPattern, ResolvedPatternKind, ResolvedProgram, ResolvedRecursiveGroup,
        ResolvedRecursiveMember, ResolvedRegistry, ResolvedType, ResolvedTypeProvenance,
        ResolvedTypeProvenanceNode, ResolvedTypeVariable, ResolvedTypedPattern,
    },
    source::Origin,
    surface::{
        BinaryExpr, SurfaceBinding, SurfaceBlock, SurfaceDefinitionKind, SurfaceExpr,
        SurfaceExprKind, SurfaceLocalDeclaration, SurfacePattern, SurfacePatternKind,
        SurfaceProgram, SurfaceRecursiveGroup, SurfaceType, SurfaceTypeKind,
    },
    types::{ConstructorId, NominalTypeId, Type, TypeVariableId, TypeWorkBudget},
};

/// The semantic reason that prevented name resolution.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ResolveReason {
    /// An occurrence has no binding in lexical scope.
    UnknownName,
    /// The equation head repeats a different name from its interface.
    EquationNameMismatch,
    /// A file contains a second global with the same spelling.
    DuplicateGlobal,
    /// A file contains a second nominal type spelling.
    DuplicateType,
    /// A file contains a second constructor spelling.
    DuplicateConstructor,
    /// A declaration repeats one type-parameter spelling.
    DuplicateTypeParameter,
    /// A source type occurrence names no declaration.
    UnknownType,
    /// A nominal type constructor has the wrong number of arguments.
    TypeArgumentCount,
    /// A type of kind `Type` was used as a type constructor.
    TypeKind,
    /// An uppercase term or pattern names no constructor.
    UnknownConstructor,
    /// One pattern vector binds the same spelling more than once.
    DuplicatePatternBinder,
    /// A recursive group contains a second member with the same spelling.
    DuplicateRecursiveMember,
    /// The resolver cannot assign another distinct binder identity.
    BinderIdExhausted,
    /// Cumulative source-type resolution exceeded the compiler work budget.
    TypeResourceExhausted,
    /// An internal resolver invariant was lost.
    InternalState,
}

impl fmt::Display for ResolveReason {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::UnknownName => "resolve.unknown-name",
            Self::EquationNameMismatch => "resolve.equation-name-mismatch",
            Self::DuplicateGlobal => "resolve.duplicate-global",
            Self::DuplicateType => "resolve.duplicate-type",
            Self::DuplicateConstructor => "resolve.duplicate-constructor",
            Self::DuplicateTypeParameter => "resolve.duplicate-type-parameter",
            Self::UnknownType => "resolve.unknown-type",
            Self::TypeArgumentCount => "resolve.type-argument-count",
            Self::TypeKind => "resolve.type-kind",
            Self::UnknownConstructor => "resolve.unknown-constructor",
            Self::DuplicatePatternBinder => "pattern.duplicate-binder",
            Self::DuplicateRecursiveMember => "resolve.duplicate-recursive-member",
            Self::BinderIdExhausted => "resolve.binder-id-exhausted",
            Self::TypeResourceExhausted => "resolve.type-resource",
            Self::InternalState => "resolve.internal-state",
        })
    }
}

/// A structured name-resolution failure kept compact in pipeline results.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolveError(Box<Diagnostic<ResolveReason>>);

impl ResolveError {
    /// Returns the phase-owned structured diagnostic.
    #[must_use]
    pub fn diagnostic(&self) -> &Diagnostic<ResolveReason> {
        &self.0
    }

    /// Consumes the failure and returns its structured diagnostic.
    #[must_use]
    pub fn into_diagnostic(self) -> Diagnostic<ResolveReason> {
        *self.0
    }
}

impl From<Diagnostic<ResolveReason>> for ResolveError {
    fn from(diagnostic: Diagnostic<ResolveReason>) -> Self {
        Self(Box::new(diagnostic))
    }
}

impl Deref for ResolveError {
    type Target = Diagnostic<ResolveReason>;

    fn deref(&self) -> &Self::Target {
        self.diagnostic()
    }
}

impl fmt::Display for ResolveError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.0.render_plain())
    }
}

impl std::error::Error for ResolveError {}

/// Resolves all binding and occurrence spellings in a recovery-free program.
///
/// # Errors
///
/// Returns a structured failure when a name is not in scope, a global
/// definition violates the accepted name rules, the binder identity domain is
/// exhausted, or an internal scope invariant is lost.
pub fn resolve(program: &SurfaceProgram) -> Result<ResolvedProgram, ResolveError> {
    Resolver::new().resolve_program(program)
}

struct Resolver {
    next_binder: u32,
    next_type_variable: u32,
    scopes: Vec<HashMap<String, Binder>>,
    globals: HashMap<String, GlobalFact>,
    type_names: HashMap<String, NominalTypeId>,
    constructor_names: HashMap<String, ConstructorId>,
    type_scopes: Vec<HashMap<String, ResolvedTypeVariable>>,
    nominal_parameter_counts: Vec<usize>,
    type_work: TypeWorkBudget,
}

struct GlobalFact {
    name_span: crate::source::Span,
    definition_span: crate::source::Span,
}

impl Resolver {
    fn new() -> Self {
        Self {
            next_binder: 0,
            next_type_variable: 0,
            scopes: vec![HashMap::new()],
            globals: HashMap::new(),
            type_names: HashMap::new(),
            constructor_names: HashMap::new(),
            type_scopes: Vec::new(),
            nominal_parameter_counts: Vec::new(),
            type_work: TypeWorkBudget::default(),
        }
    }

    fn resolve_program(
        mut self,
        program: &SurfaceProgram,
    ) -> Result<ResolvedProgram, ResolveError> {
        let registry = self.resolve_registry(program)?;
        let mut global_type_parameters = Vec::with_capacity(program.definitions.len());
        for definition in &program.definitions {
            global_type_parameters.push(self.allocate_global_type_parameters(definition)?);
        }
        let mut global_binders = Vec::with_capacity(program.definitions.len());
        for definition in &program.definitions {
            let (global_name, global_name_span) = match &definition.kind {
                SurfaceDefinitionKind::Equational(equational) => {
                    if equational.equations.is_empty() {
                        return Err(error(
                            ResolveReason::InternalState,
                            definition.span,
                            "the equational definition has no clause",
                        ));
                    }
                    for equation in &equational.equations {
                        if equational.interface.name.text != equation.name.text {
                            let mut diagnostic = Diagnostic::new(
                                ResolveReason::EquationNameMismatch,
                                SourceLabel::new(
                                    equation.name.span,
                                    "this equation name does not match its interface",
                                ),
                            );
                            diagnostic.related.push(SourceLabel::new(
                                equational.interface.name.span,
                                "the external interface declares this name",
                            ));
                            diagnostic.expected = Some(equational.interface.name.text.clone());
                            diagnostic.found = Some(equation.name.text.clone());
                            diagnostic.help = Some(format!(
                                "rename the equation head to `{}`",
                                equational.interface.name.text
                            ));
                            return Err(diagnostic.into());
                        }
                    }
                    (
                        equational.interface.name.text.as_str(),
                        equational.interface.name.span,
                    )
                }
                SurfaceDefinitionKind::InlineOperational(operational) => (
                    operational.header.name.text.as_str(),
                    operational.header.name.span,
                ),
            };
            if let Some(first) = self.globals.get(global_name) {
                let mut diagnostic = Diagnostic::new(
                    ResolveReason::DuplicateGlobal,
                    SourceLabel::new(global_name_span, "this global name is already defined"),
                );
                diagnostic.related.push(SourceLabel::new(
                    first.name_span,
                    "the first global name is here",
                ));
                diagnostic.related.push(SourceLabel::new(
                    first.definition_span,
                    "the first complete definition is here",
                ));
                return Err(diagnostic.into());
            }
            let global = self.allocate_binder(global_name, global_name_span)?;
            let Some(file_scope) = self.scopes.first_mut() else {
                return Err(error(
                    ResolveReason::InternalState,
                    definition.span,
                    "the resolver lost the file scope",
                ));
            };
            file_scope.insert(global.spelling.clone(), global.clone());
            self.globals.insert(
                global_name.to_owned(),
                GlobalFact {
                    name_span: global_name_span,
                    definition_span: definition.span,
                },
            );
            global_binders.push(global);
        }

        let mut definitions = Vec::with_capacity(program.definitions.len());
        for ((definition, global), type_parameters) in program
            .definitions
            .iter()
            .zip(global_binders)
            .zip(global_type_parameters)
        {
            let type_scope_checkpoint = self.type_scopes.len();
            self.type_scopes.push(
                type_parameters
                    .iter()
                    .map(|parameter| (parameter.spelling.clone(), parameter.clone()))
                    .collect(),
            );
            let kind = match &definition.kind {
                SurfaceDefinitionKind::Equational(equational) => {
                    let annotation = self.resolve_type(&equational.interface.annotation)?;
                    let mut equations = Vec::with_capacity(equational.equations.len());
                    for equation in &equational.equations {
                        let scope_checkpoint = self.scopes.len();
                        let (patterns, binders) =
                            self.resolve_pattern_vector(&equation.patterns)?;
                        self.push_binder_scope_many(&binders);
                        let resolved_body = self.resolve_expr(&equation.body);
                        self.scopes.truncate(scope_checkpoint);
                        equations.push(ResolvedEquation {
                            name: ResolvedOccurrence {
                                binder: global.id,
                                spelling: equation.name.text.clone(),
                                origin: Origin::Source(equation.name.span),
                            },
                            patterns,
                            body: resolved_body?,
                            span: equation.span,
                        });
                    }
                    if equations.is_empty() {
                        return Err(error(
                            ResolveReason::InternalState,
                            definition.span,
                            "the resolver produced no equation",
                        ));
                    }
                    ResolvedDefinitionKind::Equational(ResolvedEquationalGlobal {
                        interface: ResolvedExternalInterface {
                            name: global.clone(),
                            annotation,
                            type_parameters: type_parameters.clone().into_boxed_slice(),
                            span: equational.interface.span,
                        },
                        equations,
                    })
                }
                SurfaceDefinitionKind::InlineOperational(operational) => {
                    let surface_patterns = operational
                        .header
                        .parameters
                        .iter()
                        .map(|parameter| parameter.pattern.clone())
                        .collect::<Vec<_>>();
                    let (patterns, binders) = self.resolve_pattern_vector(&surface_patterns)?;
                    let scope_checkpoint = self.scopes.len();
                    self.push_binder_scope_many(&binders);
                    let resolved_body = self.resolve_block(&operational.body);
                    self.scopes.truncate(scope_checkpoint);
                    let body = resolved_body?;
                    let parameters = patterns
                        .into_iter()
                        .zip(&operational.header.parameters)
                        .map(|(pattern, parameter)| {
                            Ok(ResolvedTypedPattern {
                                pattern,
                                annotation: self.resolve_type(&parameter.annotation)?,
                                span: parameter.span,
                            })
                        })
                        .collect::<Result<Vec<_>, ResolveError>>()?;
                    if parameters.is_empty() {
                        return Err(error(
                            ResolveReason::InternalState,
                            operational.header.span,
                            "the resolver produced no operational parameter",
                        ));
                    }
                    ResolvedDefinitionKind::InlineOperational(ResolvedInlineOperationalGlobal {
                        header: ResolvedInlineOperationalHeader {
                            name: global.clone(),
                            parameters,
                            result_type: self.resolve_type(&operational.header.result_type)?,
                            type_parameters: type_parameters.clone().into_boxed_slice(),
                            span: operational.header.span,
                        },
                        body,
                    })
                }
            };
            definitions.push(ResolvedDefinition {
                kind,
                span: definition.span,
            });
            self.type_scopes.truncate(type_scope_checkpoint);
        }

        let result = self.resolve_expr(&program.result)?;
        Ok(ResolvedProgram {
            registry,
            definitions,
            result,
            span: program.span,
        })
    }

    fn resolve_registry(
        &mut self,
        program: &SurfaceProgram,
    ) -> Result<Arc<ResolvedRegistry>, ResolveError> {
        let mut first_types = HashMap::new();
        let mut nominal_ids = Vec::with_capacity(program.type_declarations.len());
        for (index, declaration) in program.type_declarations.iter().enumerate() {
            if let Some(first) =
                first_types.insert(declaration.name.text.as_str(), declaration.name.span)
            {
                let mut diagnostic = Diagnostic::new(
                    ResolveReason::DuplicateType,
                    SourceLabel::new(
                        declaration.name.span,
                        "this nominal type name is already defined",
                    ),
                );
                diagnostic
                    .related
                    .push(SourceLabel::new(first, "the first nominal type is here"));
                return Err(diagnostic.into());
            }
            let index = u32::try_from(index).map_err(|_| {
                error(
                    ResolveReason::InternalState,
                    declaration.span,
                    "the file contains too many type declarations",
                )
            })?;
            let id = NominalTypeId::new(declaration.span.source(), index);
            self.type_names.insert(declaration.name.text.clone(), id);
            nominal_ids.push(id);
        }

        let mut first_constructors = HashMap::new();
        let mut constructor_ids = Vec::with_capacity(program.type_declarations.len());
        for (declaration, owner) in program.type_declarations.iter().zip(&nominal_ids) {
            let mut owned = Vec::with_capacity(declaration.constructors.len());
            for (index, constructor) in declaration.constructors.iter().enumerate() {
                if let Some(first) =
                    first_constructors.insert(constructor.name.text.as_str(), constructor.name.span)
                {
                    let mut diagnostic = Diagnostic::new(
                        ResolveReason::DuplicateConstructor,
                        SourceLabel::new(
                            constructor.name.span,
                            "this constructor name is already defined",
                        ),
                    );
                    diagnostic
                        .related
                        .push(SourceLabel::new(first, "the first constructor is here"));
                    return Err(diagnostic.into());
                }
                let index = u32::try_from(index).map_err(|_| {
                    error(
                        ResolveReason::InternalState,
                        constructor.span,
                        "the declaration contains too many constructors",
                    )
                })?;
                let id = ConstructorId::new(*owner, index);
                self.constructor_names
                    .insert(constructor.name.text.clone(), id);
                owned.push(id);
            }
            constructor_ids.push(owned);
        }

        let mut nominal_parameters = Vec::with_capacity(program.type_declarations.len());
        for (declaration, owner) in program.type_declarations.iter().zip(&nominal_ids) {
            let mut first = HashMap::new();
            let mut parameters = Vec::with_capacity(declaration.parameters.len());
            for parameter in &declaration.parameters {
                if let Some(first_span) = first.insert(parameter.text.as_str(), parameter.span) {
                    let mut diagnostic = Diagnostic::new(
                        ResolveReason::DuplicateTypeParameter,
                        SourceLabel::new(parameter.span, "this type parameter is already declared"),
                    );
                    diagnostic.related.push(SourceLabel::new(
                        first_span,
                        "the first type parameter is here",
                    ));
                    return Err(diagnostic.into());
                }
                parameters.push(self.allocate_type_variable(&parameter.text, parameter.span)?);
            }
            nominal_parameters.push((*owner, parameters));
        }
        self.nominal_parameter_counts = nominal_parameters
            .iter()
            .map(|(_, parameters)| parameters.len())
            .collect();

        let nominals = program
            .type_declarations
            .iter()
            .zip(&nominal_ids)
            .zip(&constructor_ids)
            .map(|((declaration, id), constructors)| ResolvedNominalType {
                id: *id,
                spelling: declaration.name.text.clone(),
                constructors: constructors.clone().into_boxed_slice(),
                origin: Origin::Source(declaration.span),
            })
            .collect::<Vec<_>>();
        let mut constructors = Vec::new();
        for (((declaration, owner), ids), (_, parameters)) in program
            .type_declarations
            .iter()
            .zip(&nominal_ids)
            .zip(&constructor_ids)
            .zip(&nominal_parameters)
        {
            self.type_scopes.push(
                parameters
                    .iter()
                    .map(|parameter| (parameter.spelling.clone(), parameter.clone()))
                    .collect(),
            );
            for (constructor, id) in declaration.constructors.iter().zip(ids) {
                let payload = match constructor.fields.as_slice() {
                    [] => None,
                    [field] => Some(self.resolve_type(field)?.ty),
                    fields => Some(Type::Tuple(
                        fields
                            .iter()
                            .map(|field| self.resolve_type(field).map(|resolved| resolved.ty))
                            .collect::<Result<Vec<_>, _>>()?
                            .into_boxed_slice(),
                    )),
                };
                constructors.push(ResolvedConstructor {
                    id: *id,
                    owner: *owner,
                    spelling: constructor.name.text.clone(),
                    payload,
                    origin: Origin::Source(constructor.span),
                });
            }
            let _ = self.type_scopes.pop();
        }
        Ok(Arc::new(
            ResolvedRegistry::new(nominals, constructors).with_type_parameters(nominal_parameters),
        ))
    }

    fn push_binder_scope_many(&mut self, binders: &[Binder]) {
        self.scopes.push(
            binders
                .iter()
                .map(|binder| (binder.spelling.clone(), binder.clone()))
                .collect(),
        );
    }

    fn resolve_type(&mut self, surface: &SurfaceType) -> Result<ResolvedType, ResolveError> {
        enum Task<'a> {
            Visit(&'a SurfaceType),
            Tuple(usize, crate::source::Span),
            Function(crate::source::Span),
            Application(NominalTypeId, usize, crate::source::Span),
        }
        let mut tasks = vec![Task::Visit(surface)];
        let mut completed = Vec::new();
        let mut provenance = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(current) => {
                    self.type_work.charge(1).map_err(|()| {
                        error(
                            ResolveReason::TypeResourceExhausted,
                            current.span,
                            "source type resolution exceeded its work budget",
                        )
                    })?;
                    match &current.kind {
                        SurfaceTypeKind::Int => {
                            provenance.push(ResolvedTypeProvenanceNode::Fact(current.span));
                            completed.push((Type::Int, provenance.len() - 1));
                        }
                        SurfaceTypeKind::Bool => {
                            provenance.push(ResolvedTypeProvenanceNode::Fact(current.span));
                            completed.push((Type::Bool, provenance.len() - 1));
                        }
                        SurfaceTypeKind::Unit => {
                            provenance.push(ResolvedTypeProvenanceNode::Fact(current.span));
                            completed.push((Type::Unit, provenance.len() - 1));
                        }
                        SurfaceTypeKind::Named(name) => {
                            if let Some(variable) = self
                                .type_scopes
                                .iter()
                                .rev()
                                .find_map(|scope| scope.get(&name.text))
                            {
                                provenance.push(ResolvedTypeProvenanceNode::Fact(current.span));
                                completed.push((Type::Variable(variable.id), provenance.len() - 1));
                                continue;
                            }
                            let id = self.type_names.get(&name.text).copied().ok_or_else(|| {
                                let mut diagnostic = Diagnostic::new(
                                    ResolveReason::UnknownType,
                                    SourceLabel::new(
                                        name.span,
                                        "this nominal type is not declared",
                                    ),
                                );
                                diagnostic.found = Some(name.text.clone());
                                ResolveError::from(diagnostic)
                            })?;
                            let expected = self.nominal_parameter_count(id).ok_or_else(|| {
                                error(
                                    ResolveReason::InternalState,
                                    current.span,
                                    "the resolver lost nominal parameter metadata",
                                )
                            })?;
                            if expected != 0 {
                                return Err(type_argument_count(
                                    name.span, &name.text, expected, 0,
                                ));
                            }
                            provenance.push(ResolvedTypeProvenanceNode::Fact(current.span));
                            completed.push((Type::Nominal(id), provenance.len() - 1));
                        }
                        SurfaceTypeKind::Application {
                            constructor,
                            arguments,
                        } => {
                            if self
                                .type_scopes
                                .iter()
                                .rev()
                                .any(|scope| scope.contains_key(&constructor.text))
                            {
                                return Err(error(
                                    ResolveReason::TypeKind,
                                    constructor.span,
                                    "a parameter of kind Type cannot be applied",
                                ));
                            }
                            let id = self.type_names.get(&constructor.text).copied().ok_or_else(
                                || {
                                    let mut diagnostic = Diagnostic::new(
                                        ResolveReason::UnknownType,
                                        SourceLabel::new(
                                            constructor.span,
                                            "this nominal type is not declared",
                                        ),
                                    );
                                    diagnostic.found = Some(constructor.text.clone());
                                    ResolveError::from(diagnostic)
                                },
                            )?;
                            let expected = self.nominal_parameter_count(id).ok_or_else(|| {
                                error(
                                    ResolveReason::InternalState,
                                    current.span,
                                    "the resolver lost nominal parameter metadata",
                                )
                            })?;
                            if expected != arguments.len() {
                                return Err(type_argument_count(
                                    current.span,
                                    &constructor.text,
                                    expected,
                                    arguments.len(),
                                ));
                            }
                            tasks.push(Task::Application(id, arguments.len(), current.span));
                            tasks.extend(arguments.iter().rev().map(Task::Visit));
                        }
                        SurfaceTypeKind::Tuple(elements) => {
                            tasks.push(Task::Tuple(elements.len(), current.span));
                            tasks.extend(elements.iter().rev().map(Task::Visit));
                        }
                        SurfaceTypeKind::Function(function) => {
                            tasks.push(Task::Function(current.span));
                            tasks.push(Task::Visit(&function.codomain));
                            tasks.push(Task::Visit(&function.domain));
                        }
                    }
                }
                Task::Tuple(count, span) => {
                    let split = completed.len().checked_sub(count).ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            surface.span,
                            "the resolver lost a tuple type element",
                        )
                    })?;
                    let elements = completed.split_off(split);
                    let roots = elements
                        .iter()
                        .map(|(_, root)| *root)
                        .collect::<Vec<_>>()
                        .into_boxed_slice();
                    provenance.push(ResolvedTypeProvenanceNode::Tuple {
                        span,
                        elements: roots,
                    });
                    completed.push((
                        Type::Tuple(
                            elements
                                .into_iter()
                                .map(|(ty, _)| ty)
                                .collect::<Vec<_>>()
                                .into_boxed_slice(),
                        ),
                        provenance.len() - 1,
                    ));
                }
                Task::Function(span) => {
                    let (codomain, codomain_root) = completed.pop().ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            surface.span,
                            "the resolver lost a function codomain",
                        )
                    })?;
                    let (domain, domain_root) = completed.pop().ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            surface.span,
                            "the resolver lost a function domain",
                        )
                    })?;
                    provenance.push(ResolvedTypeProvenanceNode::Function {
                        span,
                        domain: domain_root,
                        codomain: codomain_root,
                    });
                    completed.push((
                        Type::Function(Box::new(domain), Box::new(codomain)),
                        provenance.len() - 1,
                    ));
                }
                Task::Application(owner, count, span) => {
                    let split = completed.len().checked_sub(count).ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            surface.span,
                            "the resolver lost a type argument",
                        )
                    })?;
                    let arguments = completed.split_off(split);
                    let roots = arguments
                        .iter()
                        .map(|(_, root)| *root)
                        .collect::<Vec<_>>()
                        .into_boxed_slice();
                    provenance.push(ResolvedTypeProvenanceNode::Application {
                        span,
                        arguments: roots,
                    });
                    completed.push((
                        Type::AppliedNominal(
                            owner,
                            arguments
                                .into_iter()
                                .map(|(ty, _)| ty)
                                .collect::<Vec<_>>()
                                .into_boxed_slice(),
                        ),
                        provenance.len() - 1,
                    ));
                }
            }
        }
        if completed.len() != 1 {
            return Err(error(
                ResolveReason::InternalState,
                surface.span,
                "the resolver retained incomplete type state",
            ));
        }
        let (ty, root) = completed.pop().ok_or_else(|| {
            error(
                ResolveReason::InternalState,
                surface.span,
                "the resolver produced no type",
            )
        })?;
        Ok(ResolvedType {
            ty,
            provenance: ResolvedTypeProvenance::new(provenance, root),
            origin: Origin::Source(surface.span),
            span: surface.span,
        })
    }

    fn resolve_pattern_vector(
        &mut self,
        patterns: &[SurfacePattern],
    ) -> Result<(Vec<ResolvedPattern>, Vec<Binder>), ResolveError> {
        let mut seen = HashMap::new();
        let mut binders = Vec::new();
        let patterns = patterns
            .iter()
            .map(|pattern| self.resolve_pattern(pattern, &mut seen, &mut binders))
            .collect::<Result<Vec<_>, _>>()?;
        Ok((patterns, binders))
    }

    fn resolve_pattern(
        &mut self,
        pattern: &SurfacePattern,
        seen: &mut HashMap<String, crate::source::Span>,
        binders: &mut Vec<Binder>,
    ) -> Result<ResolvedPattern, ResolveError> {
        let kind = match &pattern.kind {
            SurfacePatternKind::Binder(surface) => {
                if let Some(first) = seen.insert(surface.name.text.clone(), surface.name.span) {
                    let mut diagnostic = Diagnostic::new(
                        ResolveReason::DuplicatePatternBinder,
                        SourceLabel::new(
                            surface.name.span,
                            "this pattern binder is already defined",
                        ),
                    );
                    diagnostic
                        .related
                        .push(SourceLabel::new(first, "the first pattern binder is here"));
                    return Err(diagnostic.into());
                }
                let binder = self.allocate_binder(&surface.name.text, surface.name.span)?;
                binders.push(binder.clone());
                ResolvedPatternKind::Binder(binder)
            }
            SurfacePatternKind::Wildcard => ResolvedPatternKind::Wildcard,
            SurfacePatternKind::Boolean(value) => ResolvedPatternKind::Boolean(*value),
            SurfacePatternKind::Unit => ResolvedPatternKind::Unit,
            SurfacePatternKind::Tuple(elements) => ResolvedPatternKind::Tuple(
                elements
                    .iter()
                    .map(|element| self.resolve_pattern(element, seen, binders))
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            SurfacePatternKind::Constructor { name, payload } => {
                let constructor =
                    self.constructor_names
                        .get(&name.text)
                        .copied()
                        .ok_or_else(|| {
                            let mut diagnostic = Diagnostic::new(
                                ResolveReason::UnknownConstructor,
                                SourceLabel::new(name.span, "this constructor is not declared"),
                            );
                            diagnostic.found = Some(name.text.clone());
                            ResolveError::from(diagnostic)
                        })?;
                ResolvedPatternKind::Constructor {
                    constructor,
                    occurrence: ResolvedConstructorOccurrence {
                        constructor,
                        spelling: name.text.clone(),
                        origin: Origin::Source(name.span),
                    },
                    payload: payload
                        .as_deref()
                        .map(|payload| self.resolve_pattern(payload, seen, binders).map(Box::new))
                        .transpose()?,
                }
            }
        };
        Ok(ResolvedPattern {
            kind,
            span: pattern.span,
        })
    }

    fn resolve_block(&mut self, block: &SurfaceBlock) -> Result<ResolvedBlock, ResolveError> {
        let resolved = self.resolve_work(ResolveTask::VisitBlock(block))?;
        let ResolvedExprKind::Block(block) = resolved.kind else {
            return Err(error(
                ResolveReason::InternalState,
                block.span,
                "the resolver produced the wrong block payload",
            ));
        };
        Ok(block)
    }

    fn allocate_binder(
        &mut self,
        spelling: &str,
        span: crate::source::Span,
    ) -> Result<Binder, ResolveError> {
        let id = BinderId::new(self.next_binder);
        self.next_binder = self.next_binder.checked_add(1).ok_or_else(|| {
            error(
                ResolveReason::BinderIdExhausted,
                span,
                "the program contains too many binders",
            )
        })?;
        Ok(Binder {
            id,
            spelling: spelling.to_owned(),
            origin: Origin::Source(span),
        })
    }

    fn allocate_type_variable(
        &mut self,
        spelling: &str,
        span: crate::source::Span,
    ) -> Result<ResolvedTypeVariable, ResolveError> {
        let id = TypeVariableId::new(self.next_type_variable);
        self.next_type_variable = self.next_type_variable.checked_add(1).ok_or_else(|| {
            error(
                ResolveReason::BinderIdExhausted,
                span,
                "the program contains too many type binders",
            )
        })?;
        Ok(ResolvedTypeVariable {
            id,
            spelling: spelling.to_owned(),
            origin: Origin::Source(span),
        })
    }

    fn allocate_global_type_parameters(
        &mut self,
        definition: &crate::surface::SurfaceDefinition,
    ) -> Result<Vec<ResolvedTypeVariable>, ResolveError> {
        let mut names = Vec::new();
        match &definition.kind {
            SurfaceDefinitionKind::Equational(equational) => {
                collect_free_type_names(
                    &equational.interface.annotation,
                    &self.type_names,
                    &mut names,
                );
            }
            SurfaceDefinitionKind::InlineOperational(operational) => {
                for parameter in &operational.header.parameters {
                    collect_free_type_names(&parameter.annotation, &self.type_names, &mut names);
                }
                collect_free_type_names(
                    &operational.header.result_type,
                    &self.type_names,
                    &mut names,
                );
            }
        }
        names
            .into_iter()
            .map(|name| self.allocate_type_variable(&name.text, name.span))
            .collect()
    }

    fn nominal_parameter_count(&self, id: NominalTypeId) -> Option<usize> {
        usize::try_from(id.declaration())
            .ok()
            .and_then(|index| self.nominal_parameter_counts.get(index).copied())
    }

    fn resolve_expr(&mut self, expression: &SurfaceExpr) -> Result<ResolvedExpr, ResolveError> {
        self.resolve_work(ResolveTask::VisitExpr(expression))
    }

    fn resolve_work<'a>(&mut self, initial: ResolveTask<'a>) -> Result<ResolvedExpr, ResolveError> {
        let scope_checkpoint = self.scopes.len();
        let result = self.resolve_work_inner(initial);
        if result.is_err() {
            self.scopes.truncate(scope_checkpoint);
        }
        result
    }

    fn resolve_work_inner<'a>(
        &mut self,
        initial: ResolveTask<'a>,
    ) -> Result<ResolvedExpr, ResolveError> {
        let initial_span = initial.span();
        let mut tasks = vec![initial];
        let mut expressions = Vec::new();
        let mut declarations = Vec::new();

        while let Some(task) = tasks.pop() {
            match task {
                ResolveTask::VisitExpr(expression) => {
                    self.visit_expression(expression, &mut tasks, &mut expressions)?;
                }
                ResolveTask::VisitBlock(block) => {
                    let scope_checkpoint = self.scopes.len();
                    self.scopes.push(HashMap::new());
                    let declaration_start = declarations.len();
                    tasks.push(ResolveTask::FinishBlock {
                        declaration_start,
                        scope_checkpoint,
                        span: block.span,
                    });
                    tasks.push(ResolveTask::VisitExpr(&block.result));
                    for declaration in block.declarations.iter().rev() {
                        match declaration {
                            SurfaceLocalDeclaration::Binding(binding) => {
                                tasks.push(ResolveTask::FinishBinding(binding));
                                tasks.push(ResolveTask::VisitExpr(&binding.initializer));
                            }
                            SurfaceLocalDeclaration::Recursive(group) => {
                                tasks.push(ResolveTask::VisitRecursiveGroup(group));
                            }
                        }
                    }
                }
                ResolveTask::VisitRecursiveGroup(group) => {
                    let mut first_members = HashMap::with_capacity(group.members.len());
                    let mut binders = Vec::with_capacity(group.members.len());
                    for member in &group.members {
                        if let Some(first_span) =
                            first_members.get(member.binder.name.text.as_str()).copied()
                        {
                            let mut diagnostic = Diagnostic::new(
                                ResolveReason::DuplicateRecursiveMember,
                                SourceLabel::new(
                                    member.binder.name.span,
                                    "this recursive member name is already defined",
                                ),
                            );
                            diagnostic.related.push(SourceLabel::new(
                                first_span,
                                "the first recursive member is here",
                            ));
                            diagnostic.found = Some(member.binder.name.text.clone());
                            return Err(diagnostic.into());
                        }
                        first_members
                            .insert(member.binder.name.text.as_str(), member.binder.name.span);
                        binders.push(
                            self.allocate_binder(
                                &member.binder.name.text,
                                member.binder.name.span,
                            )?,
                        );
                    }
                    let Some(scope) = self.scopes.last_mut() else {
                        return Err(error(
                            ResolveReason::InternalState,
                            group.span,
                            "the resolver lost the current lexical scope",
                        ));
                    };
                    for binder in &binders {
                        scope.insert(binder.spelling.clone(), binder.clone());
                    }
                    tasks.push(ResolveTask::FinishRecursiveGroup { group, binders });
                    for member in group.members.iter().rev() {
                        tasks.push(ResolveTask::VisitExpr(&member.initializer));
                    }
                }
                ResolveTask::FinishApplication { span } => {
                    let (function, argument) = take_expression_pair(&mut expressions, span)?;
                    expressions.push(ResolvedExpr {
                        kind: ResolvedExprKind::Apply(ResolvedApplicationExpr {
                            function: Box::new(function),
                            argument: Box::new(argument),
                        }),
                        span,
                    });
                }
                ResolveTask::FinishBinary {
                    kind,
                    operator_span,
                    span,
                } => {
                    let (left, right) = take_expression_pair(&mut expressions, span)?;
                    let binary = ResolvedBinaryExpr {
                        left: Box::new(left),
                        right: Box::new(right),
                        operator_span,
                    };
                    expressions.push(ResolvedExpr {
                        kind: kind.finish(binary),
                        span,
                    });
                }
                ResolveTask::FinishBinding(binding) => {
                    let Some(initializer) = expressions.pop() else {
                        return Err(error(
                            ResolveReason::InternalState,
                            binding.span,
                            "the resolver lost a binding initializer",
                        ));
                    };
                    let (mut patterns, binders) =
                        self.resolve_pattern_vector(std::slice::from_ref(&binding.pattern))?;
                    let pattern = patterns.pop().ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            binding.pattern.span,
                            "the resolver produced no binding pattern",
                        )
                    })?;
                    let annotation = binding
                        .annotation
                        .as_ref()
                        .map(|annotation| self.resolve_type(annotation))
                        .transpose()?;
                    let Some(scope) = self.scopes.last_mut() else {
                        return Err(error(
                            ResolveReason::InternalState,
                            binding.span,
                            "the resolver lost the current lexical scope",
                        ));
                    };
                    for binder in binders {
                        scope.insert(binder.spelling.clone(), binder);
                    }
                    declarations.push(ResolvedLocalDeclaration::Binding(Box::new(
                        ResolvedBinding {
                            pattern,
                            annotation,
                            initializer,
                            span: binding.span,
                        },
                    )));
                }
                ResolveTask::FinishRecursiveGroup { group, binders } => {
                    if binders.len() != group.members.len()
                        || expressions.len() < group.members.len()
                    {
                        return Err(error(
                            ResolveReason::InternalState,
                            group.span,
                            "the resolver lost a recursive group member",
                        ));
                    }
                    let expression_start = expressions.len() - group.members.len();
                    let initializers = expressions.split_off(expression_start);
                    let members = group
                        .members
                        .iter()
                        .zip(binders)
                        .zip(initializers)
                        .map(|((member, binder), initializer)| {
                            Ok(ResolvedRecursiveMember {
                                introducer_span: member.introducer_span,
                                binder,
                                annotation: self.resolve_type(&member.annotation)?,
                                initializer,
                                span: member.span,
                            })
                        })
                        .collect::<Result<Vec<_>, ResolveError>>()?;
                    declarations.push(ResolvedLocalDeclaration::Recursive(
                        ResolvedRecursiveGroup {
                            members,
                            span: group.span,
                        },
                    ));
                }
                ResolveTask::FinishBlock {
                    declaration_start,
                    scope_checkpoint,
                    span,
                } => {
                    let Some(result) = expressions.pop() else {
                        return Err(error(
                            ResolveReason::InternalState,
                            span,
                            "the resolver lost a block result",
                        ));
                    };
                    if declaration_start > declarations.len() {
                        return Err(error(
                            ResolveReason::InternalState,
                            span,
                            "the resolver lost a block binding",
                        ));
                    }
                    let block_declarations = declarations.split_off(declaration_start);
                    self.scopes.truncate(scope_checkpoint);
                    expressions.push(ResolvedExpr {
                        kind: ResolvedExprKind::Block(ResolvedBlock {
                            declarations: block_declarations,
                            result: Box::new(result),
                            span,
                        }),
                        span,
                    });
                }
                ResolveTask::FinishFunction {
                    parameter: pattern,
                    scope_checkpoint,
                    span,
                } => {
                    let Some(body_expression) = expressions.pop() else {
                        return Err(error(
                            ResolveReason::InternalState,
                            span,
                            "the resolver lost a function body",
                        ));
                    };
                    let ResolvedExprKind::Block(body) = body_expression.kind else {
                        return Err(error(
                            ResolveReason::InternalState,
                            span,
                            "the resolver produced the wrong function body payload",
                        ));
                    };
                    self.scopes.truncate(scope_checkpoint);
                    expressions.push(ResolvedExpr {
                        kind: ResolvedExprKind::Function(ResolvedFunctionExpr { pattern, body }),
                        span,
                    });
                }
                ResolveTask::FinishTuple { count, span } => {
                    let split = expressions.len().checked_sub(count).ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            span,
                            "the resolver lost a tuple element",
                        )
                    })?;
                    let elements = expressions.split_off(split);
                    expressions.push(ResolvedExpr {
                        kind: ResolvedExprKind::Tuple(elements),
                        span,
                    });
                }
            }
        }

        let Some(result) = expressions.pop() else {
            return Err(error(
                ResolveReason::InternalState,
                initial_span,
                "the resolver produced no expression",
            ));
        };
        if !expressions.is_empty() || !declarations.is_empty() {
            return Err(error(
                ResolveReason::InternalState,
                initial_span,
                "the resolver retained incomplete expression state",
            ));
        }
        Ok(result)
    }

    fn visit_expression<'a>(
        &mut self,
        expression: &'a SurfaceExpr,
        tasks: &mut Vec<ResolveTask<'a>>,
        expressions: &mut Vec<ResolvedExpr>,
    ) -> Result<(), ResolveError> {
        match &expression.kind {
            SurfaceExprKind::Integer(value) => expressions.push(ResolvedExpr {
                kind: ResolvedExprKind::Integer(value.clone()),
                span: expression.span,
            }),
            SurfaceExprKind::Boolean(value) => expressions.push(ResolvedExpr {
                kind: ResolvedExprKind::Boolean(*value),
                span: expression.span,
            }),
            SurfaceExprKind::Unit => expressions.push(ResolvedExpr {
                kind: ResolvedExprKind::Unit,
                span: expression.span,
            }),
            SurfaceExprKind::Name(name) => {
                let binder = self
                    .scopes
                    .iter()
                    .rev()
                    .find_map(|scope| scope.get(&name.text));
                if let Some(binder) = binder {
                    expressions.push(ResolvedExpr {
                        kind: ResolvedExprKind::Occurrence(ResolvedOccurrence {
                            binder: binder.id,
                            spelling: name.text.clone(),
                            origin: Origin::Source(name.span),
                        }),
                        span: expression.span,
                    });
                } else if let Some(constructor) = self.constructor_names.get(&name.text).copied() {
                    expressions.push(ResolvedExpr {
                        kind: ResolvedExprKind::Constructor(ResolvedConstructorOccurrence {
                            constructor,
                            spelling: name.text.clone(),
                            origin: Origin::Source(name.span),
                        }),
                        span: expression.span,
                    });
                } else {
                    return Err(
                        if name.text.chars().next().is_some_and(char::is_uppercase) {
                            let mut diagnostic = Diagnostic::new(
                                ResolveReason::UnknownConstructor,
                                SourceLabel::new(name.span, "this constructor is not declared"),
                            );
                            diagnostic.found = Some(name.text.clone());
                            ResolveError::from(diagnostic)
                        } else {
                            error(
                                ResolveReason::UnknownName,
                                name.span,
                                "this name is not in scope",
                            )
                        },
                    );
                }
            }
            SurfaceExprKind::Apply(application) => {
                tasks.push(ResolveTask::FinishApplication {
                    span: expression.span,
                });
                tasks.push(ResolveTask::VisitExpr(&application.argument));
                tasks.push(ResolveTask::VisitExpr(&application.function));
            }
            SurfaceExprKind::Add(binary) => {
                schedule_binary(BinaryKind::Add, expression.span, binary, tasks);
            }
            SurfaceExprKind::Multiply(binary) => {
                schedule_binary(BinaryKind::Multiply, expression.span, binary, tasks);
            }
            SurfaceExprKind::Equal(binary) => {
                schedule_binary(BinaryKind::Equal, expression.span, binary, tasks);
            }
            SurfaceExprKind::Block(block) => tasks.push(ResolveTask::VisitBlock(block)),
            SurfaceExprKind::Function(function) => {
                let (mut patterns, binders) =
                    self.resolve_pattern_vector(std::slice::from_ref(&function.parameter))?;
                let parameter = patterns.pop().ok_or_else(|| {
                    error(
                        ResolveReason::InternalState,
                        function.parameter.span,
                        "the resolver produced no function pattern",
                    )
                })?;
                let scope_checkpoint = self.scopes.len();
                self.push_binder_scope_many(&binders);
                tasks.push(ResolveTask::FinishFunction {
                    parameter,
                    scope_checkpoint,
                    span: expression.span,
                });
                tasks.push(ResolveTask::VisitBlock(&function.body));
            }
            SurfaceExprKind::Tuple(elements) => {
                tasks.push(ResolveTask::FinishTuple {
                    count: elements.len(),
                    span: expression.span,
                });
                tasks.extend(elements.iter().rev().map(ResolveTask::VisitExpr));
            }
            SurfaceExprKind::Match(match_expression) => {
                let scrutinee = self.resolve_expr(&match_expression.scrutinee)?;
                let mut arms = Vec::with_capacity(match_expression.arms.len());
                for arm in &match_expression.arms {
                    let scope_checkpoint = self.scopes.len();
                    let (mut patterns, binders) =
                        self.resolve_pattern_vector(std::slice::from_ref(&arm.pattern))?;
                    let pattern = patterns.pop().ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            arm.span,
                            "the resolver produced no match pattern",
                        )
                    })?;
                    self.push_binder_scope_many(&binders);
                    let body = self.resolve_expr(&arm.body);
                    self.scopes.truncate(scope_checkpoint);
                    arms.push(ResolvedMatchArm {
                        pattern,
                        body: body?,
                        span: arm.span,
                    });
                }
                expressions.push(ResolvedExpr {
                    kind: ResolvedExprKind::Match(ResolvedMatchExpr {
                        scrutinee: Box::new(scrutinee),
                        arms,
                    }),
                    span: expression.span,
                });
            }
        }
        Ok(())
    }
}

enum ResolveTask<'a> {
    VisitExpr(&'a SurfaceExpr),
    VisitBlock(&'a SurfaceBlock),
    VisitRecursiveGroup(&'a SurfaceRecursiveGroup),
    FinishApplication {
        span: crate::source::Span,
    },
    FinishBinary {
        kind: BinaryKind,
        operator_span: crate::source::Span,
        span: crate::source::Span,
    },
    FinishBinding(&'a SurfaceBinding),
    FinishRecursiveGroup {
        group: &'a SurfaceRecursiveGroup,
        binders: Vec<Binder>,
    },
    FinishBlock {
        declaration_start: usize,
        scope_checkpoint: usize,
        span: crate::source::Span,
    },
    FinishFunction {
        parameter: ResolvedPattern,
        scope_checkpoint: usize,
        span: crate::source::Span,
    },
    FinishTuple {
        count: usize,
        span: crate::source::Span,
    },
}

impl ResolveTask<'_> {
    fn span(&self) -> crate::source::Span {
        match self {
            Self::VisitExpr(expression) => expression.span,
            Self::VisitBlock(block) => block.span,
            Self::VisitRecursiveGroup(group) => group.span,
            Self::FinishApplication { span }
            | Self::FinishBinary { span, .. }
            | Self::FinishBlock { span, .. }
            | Self::FinishFunction { span, .. }
            | Self::FinishTuple { span, .. } => *span,
            Self::FinishBinding(binding) => binding.span,
            Self::FinishRecursiveGroup { group, .. } => group.span,
        }
    }
}

#[derive(Clone, Copy)]
enum BinaryKind {
    Add,
    Multiply,
    Equal,
}

impl BinaryKind {
    fn finish(self, binary: ResolvedBinaryExpr) -> ResolvedExprKind {
        match self {
            Self::Add => ResolvedExprKind::Add(binary),
            Self::Multiply => ResolvedExprKind::Multiply(binary),
            Self::Equal => ResolvedExprKind::Equal(binary),
        }
    }
}

fn schedule_binary<'a>(
    kind: BinaryKind,
    span: crate::source::Span,
    binary: &'a BinaryExpr,
    tasks: &mut Vec<ResolveTask<'a>>,
) {
    tasks.push(ResolveTask::FinishBinary {
        kind,
        operator_span: binary.operator_span,
        span,
    });
    tasks.push(ResolveTask::VisitExpr(&binary.right));
    tasks.push(ResolveTask::VisitExpr(&binary.left));
}

fn take_expression_pair(
    expressions: &mut Vec<ResolvedExpr>,
    span: crate::source::Span,
) -> Result<(ResolvedExpr, ResolvedExpr), ResolveError> {
    let Some(right) = expressions.pop() else {
        return Err(error(
            ResolveReason::InternalState,
            span,
            "the resolver lost a right operand",
        ));
    };
    let Some(left) = expressions.pop() else {
        return Err(error(
            ResolveReason::InternalState,
            span,
            "the resolver lost a left operand",
        ));
    };
    Ok((left, right))
}

fn error(reason: ResolveReason, span: crate::source::Span, message: &str) -> ResolveError {
    Diagnostic::new(reason, SourceLabel::new(span, message)).into()
}

fn type_argument_count(
    span: crate::source::Span,
    spelling: &str,
    expected: usize,
    found: usize,
) -> ResolveError {
    let mut diagnostic = Diagnostic::new(
        ResolveReason::TypeArgumentCount,
        SourceLabel::new(span, "this nominal type has the wrong number of arguments"),
    );
    diagnostic.expected = Some(format!("{spelling} with {expected} type arguments"));
    diagnostic.found = Some(found.to_string());
    diagnostic.into()
}

fn collect_free_type_names(
    root: &SurfaceType,
    nominals: &HashMap<String, NominalTypeId>,
    output: &mut Vec<crate::surface::SurfaceName>,
) {
    let mut work = vec![root];
    while let Some(ty) = work.pop() {
        match &ty.kind {
            SurfaceTypeKind::Named(name) => {
                if !nominals.contains_key(&name.text)
                    && !output.iter().any(|known| known.text == name.text)
                {
                    output.push(name.clone());
                }
            }
            SurfaceTypeKind::Application {
                constructor,
                arguments,
            } => {
                if !nominals.contains_key(&constructor.text)
                    && !output.iter().any(|known| known.text == constructor.text)
                {
                    output.push(constructor.clone());
                }
                work.extend(arguments.iter().rev());
            }
            SurfaceTypeKind::Tuple(elements) => work.extend(elements.iter().rev()),
            SurfaceTypeKind::Function(function) => {
                work.push(&function.codomain);
                work.push(&function.domain);
            }
            SurfaceTypeKind::Int | SurfaceTypeKind::Bool | SurfaceTypeKind::Unit => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::source::{ByteRange, SourceFile};
    use crate::{
        lexer::lex,
        parser::{parse, project},
    };

    #[test]
    fn binder_identity_allocation_reports_exhaustion_without_wrapping() {
        let source =
            SourceFile::new("exhaustion.ash", "name").expect("the allocator fixture should fit");
        let span = source
            .span(ByteRange::new(0, 4).expect("the range is ordered"))
            .expect("the range belongs to the fixture");
        let mut resolver = Resolver::new();
        resolver.next_binder = u32::MAX;

        let error = resolver
            .allocate_binder("name", span)
            .expect_err("the reserved exhaustion sentinel must not be exposed");

        assert_eq!(error.reason, ResolveReason::BinderIdExhausted);
        assert_eq!(resolver.next_binder, u32::MAX);
    }

    #[test]
    fn failed_nested_and_recursive_resolution_restore_the_scope_stack() {
        for (name, text) in [
            ("scope-error.ash", "fn(value) {\n{\nmissing\n}\n}\n"),
            (
                "recursive-scope-error.ash",
                "{\nlet rec repeat : Unit -> Int = fn(ignored) {\nmissing\n}\nrepeat ()\n}\n",
            ),
        ] {
            let source = SourceFile::new(name, text).expect("the scope fixture should fit");
            let tree = parse(lex(&source).expect("the fixture should lex"));
            let program = project(&source, &tree).expect("the fixture should project");
            let mut resolver = Resolver::new();
            let initial_scope_count = resolver.scopes.len();

            let error = resolver
                .resolve_expr(&program.result)
                .expect_err("the nested unknown name should fail");

            assert_eq!(error.reason, ResolveReason::UnknownName);
            assert_eq!(resolver.scopes.len(), initial_scope_count);
        }
    }
}
