//! Lexical name resolution for recovery-free surface syntax.

use std::{collections::HashMap, fmt, ops::Deref};

use crate::{
    diagnostic::{Diagnostic, SourceLabel},
    resolved::{
        Binder, BinderId, ResolvedApplicationExpr, ResolvedBinaryExpr, ResolvedBinding,
        ResolvedBlock, ResolvedDefinition, ResolvedDefinitionKind, ResolvedEquation,
        ResolvedEquationalGlobal, ResolvedExpr, ResolvedExprKind, ResolvedExternalInterface,
        ResolvedFunctionExpr, ResolvedInlineOperationalGlobal, ResolvedInlineOperationalHeader,
        ResolvedOccurrence, ResolvedProgram, ResolvedTypedBinder,
    },
    source::Origin,
    surface::{
        BinaryExpr, SurfaceBinding, SurfaceBlock, SurfaceDefinitionKind, SurfaceExpr,
        SurfaceExprKind, SurfaceProgram,
    },
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
    /// The resolver cannot assign another distinct binder identity.
    BinderIdExhausted,
    /// An internal resolver invariant was lost.
    InternalState,
}

impl fmt::Display for ResolveReason {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::UnknownName => "resolve.unknown-name",
            Self::EquationNameMismatch => "resolve.equation-name-mismatch",
            Self::DuplicateGlobal => "resolve.duplicate-global",
            Self::BinderIdExhausted => "resolve.binder-id-exhausted",
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
    scopes: Vec<HashMap<String, Binder>>,
    globals: HashMap<String, GlobalFact>,
}

struct GlobalFact {
    name_span: crate::source::Span,
    definition_span: crate::source::Span,
}

impl Resolver {
    fn new() -> Self {
        Self {
            next_binder: 0,
            scopes: vec![HashMap::new()],
            globals: HashMap::new(),
        }
    }

    fn resolve_program(
        mut self,
        program: &SurfaceProgram,
    ) -> Result<ResolvedProgram, ResolveError> {
        let mut definitions = Vec::with_capacity(program.definitions.len());
        for definition in &program.definitions {
            let (global_name, global_name_span) = match &definition.kind {
                SurfaceDefinitionKind::Equational(equational) => {
                    if equational.interface.name.text != equational.equation.name.text {
                        let mut diagnostic = Diagnostic::new(
                            ResolveReason::EquationNameMismatch,
                            SourceLabel::new(
                                equational.equation.name.span,
                                "this equation name does not match its interface",
                            ),
                        );
                        diagnostic.related.push(SourceLabel::new(
                            equational.interface.name.span,
                            "the external interface declares this name",
                        ));
                        diagnostic.expected = Some(equational.interface.name.text.clone());
                        diagnostic.found = Some(equational.equation.name.text.clone());
                        diagnostic.help = Some(format!(
                            "rename the equation head to `{}`",
                            equational.interface.name.text
                        ));
                        return Err(diagnostic.into());
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
            let kind = match &definition.kind {
                SurfaceDefinitionKind::Equational(equational) => {
                    let parameter = self.allocate_binder(
                        &equational.equation.binder.name.text,
                        equational.equation.binder.name.span,
                    )?;
                    let scope_checkpoint = self.scopes.len();
                    self.push_binder_scope(&parameter);
                    let resolved_body = self.resolve_expr(&equational.equation.body);
                    self.scopes.truncate(scope_checkpoint);
                    let body = resolved_body?;
                    ResolvedDefinitionKind::Equational(ResolvedEquationalGlobal {
                        interface: ResolvedExternalInterface {
                            name: global.clone(),
                            annotation: equational.interface.annotation.clone(),
                            span: equational.interface.span,
                        },
                        equation: ResolvedEquation {
                            name: ResolvedOccurrence {
                                binder: global.id,
                                spelling: equational.equation.name.text.clone(),
                                origin: Origin::Source(equational.equation.name.span),
                            },
                            binder: parameter,
                            body,
                            span: equational.equation.span,
                        },
                    })
                }
                SurfaceDefinitionKind::InlineOperational(operational) => {
                    let parameter = self.allocate_binder(
                        &operational.header.parameter.binder.name.text,
                        operational.header.parameter.binder.name.span,
                    )?;
                    let scope_checkpoint = self.scopes.len();
                    self.push_binder_scope(&parameter);
                    let resolved_body = self.resolve_block(&operational.body);
                    self.scopes.truncate(scope_checkpoint);
                    let body = resolved_body?;
                    ResolvedDefinitionKind::InlineOperational(ResolvedInlineOperationalGlobal {
                        header: ResolvedInlineOperationalHeader {
                            name: global.clone(),
                            parameter: ResolvedTypedBinder {
                                binder: parameter,
                                annotation: operational.header.parameter.annotation.clone(),
                                span: operational.header.parameter.span,
                            },
                            result_type: operational.header.result_type.clone(),
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
            let Some(file_scope) = self.scopes.first_mut() else {
                return Err(error(
                    ResolveReason::InternalState,
                    definition.span,
                    "the resolver lost the file scope",
                ));
            };
            file_scope.insert(global.spelling.clone(), global);
            self.globals.insert(
                global_name.to_owned(),
                GlobalFact {
                    name_span: global_name_span,
                    definition_span: definition.span,
                },
            );
        }

        let result = self.resolve_expr(&program.result)?;
        Ok(ResolvedProgram {
            definitions,
            result,
            span: program.span,
        })
    }

    fn push_binder_scope(&mut self, binder: &Binder) {
        self.scopes
            .push(HashMap::from([(binder.spelling.clone(), binder.clone())]));
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
        let mut bindings = Vec::new();

        while let Some(task) = tasks.pop() {
            match task {
                ResolveTask::VisitExpr(expression) => {
                    self.visit_expression(expression, &mut tasks, &mut expressions)?;
                }
                ResolveTask::VisitBlock(block) => {
                    let scope_checkpoint = self.scopes.len();
                    self.scopes.push(HashMap::new());
                    let binding_start = bindings.len();
                    tasks.push(ResolveTask::FinishBlock {
                        binding_start,
                        scope_checkpoint,
                        span: block.span,
                    });
                    tasks.push(ResolveTask::VisitExpr(&block.result));
                    for binding in block.bindings.iter().rev() {
                        tasks.push(ResolveTask::FinishBinding(binding));
                        tasks.push(ResolveTask::VisitExpr(&binding.initializer));
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
                    let binder =
                        self.allocate_binder(&binding.binder.name.text, binding.binder.name.span)?;
                    let Some(scope) = self.scopes.last_mut() else {
                        return Err(error(
                            ResolveReason::InternalState,
                            binding.span,
                            "the resolver lost the current lexical scope",
                        ));
                    };
                    scope.insert(binder.spelling.clone(), binder.clone());
                    bindings.push(ResolvedBinding {
                        binder,
                        annotation: binding.annotation.clone(),
                        initializer,
                        span: binding.span,
                    });
                }
                ResolveTask::FinishBlock {
                    binding_start,
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
                    if binding_start > bindings.len() {
                        return Err(error(
                            ResolveReason::InternalState,
                            span,
                            "the resolver lost a block binding",
                        ));
                    }
                    let block_bindings = bindings.split_off(binding_start);
                    self.scopes.truncate(scope_checkpoint);
                    expressions.push(ResolvedExpr {
                        kind: ResolvedExprKind::Block(ResolvedBlock {
                            bindings: block_bindings,
                            result: Box::new(result),
                            span,
                        }),
                        span,
                    });
                }
                ResolveTask::FinishFunction {
                    parameter,
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
                        kind: ResolvedExprKind::Function(ResolvedFunctionExpr { parameter, body }),
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
        if !expressions.is_empty() || !bindings.is_empty() {
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
                    .find_map(|scope| scope.get(&name.text))
                    .ok_or_else(|| {
                        error(
                            ResolveReason::UnknownName,
                            name.span,
                            "this name is not in scope",
                        )
                    })?;
                expressions.push(ResolvedExpr {
                    kind: ResolvedExprKind::Occurrence(ResolvedOccurrence {
                        binder: binder.id,
                        spelling: name.text.clone(),
                        origin: Origin::Source(name.span),
                    }),
                    span: expression.span,
                });
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
                let parameter = self
                    .allocate_binder(&function.parameter.name.text, function.parameter.name.span)?;
                let scope_checkpoint = self.scopes.len();
                self.push_binder_scope(&parameter);
                tasks.push(ResolveTask::FinishFunction {
                    parameter,
                    scope_checkpoint,
                    span: expression.span,
                });
                tasks.push(ResolveTask::VisitBlock(&function.body));
            }
        }
        Ok(())
    }
}

enum ResolveTask<'a> {
    VisitExpr(&'a SurfaceExpr),
    VisitBlock(&'a SurfaceBlock),
    FinishApplication {
        span: crate::source::Span,
    },
    FinishBinary {
        kind: BinaryKind,
        operator_span: crate::source::Span,
        span: crate::source::Span,
    },
    FinishBinding(&'a SurfaceBinding),
    FinishBlock {
        binding_start: usize,
        scope_checkpoint: usize,
        span: crate::source::Span,
    },
    FinishFunction {
        parameter: Binder,
        scope_checkpoint: usize,
        span: crate::source::Span,
    },
}

impl ResolveTask<'_> {
    fn span(&self) -> crate::source::Span {
        match self {
            Self::VisitExpr(expression) => expression.span,
            Self::VisitBlock(block) => block.span,
            Self::FinishApplication { span }
            | Self::FinishBinary { span, .. }
            | Self::FinishBlock { span, .. }
            | Self::FinishFunction { span, .. } => *span,
            Self::FinishBinding(binding) => binding.span,
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
    fn failed_nested_resolution_restores_the_scope_stack() {
        let source = SourceFile::new("scope-error.ash", "fn(value) {\n{\nmissing\n}\n}\n")
            .expect("the scope fixture should fit");
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
