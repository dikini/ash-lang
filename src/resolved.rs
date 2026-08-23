//! Name-resolved, source-spanned syntax passed to typed elaboration.

use std::{collections::HashMap, sync::Arc};

use crate::{
    integer::Integer,
    source::{Origin, Span, discard_origin_iteratively},
    types::{ConstructorId, NominalTypeId, Type, TypeVariableId, discard_type_iteratively},
};

/// Identifies one binding within a resolved program.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct BinderId(u32);

impl BinderId {
    pub(crate) const fn new(value: u32) -> Self {
        Self(value)
    }

    /// Returns the resolver-assigned numeric identity.
    #[must_use]
    pub const fn value(self) -> u32 {
        self.0
    }
}

/// A resolved definition site.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Binder {
    /// Stable identity assigned by the resolver.
    pub id: BinderId,
    /// Exact source spelling.
    pub spelling: String,
    /// Causal source provenance for the definition site.
    pub origin: Origin,
}

/// A resolved occurrence site.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedOccurrence {
    /// Identity of the definition selected by lexical scope.
    pub binder: BinderId,
    /// Exact source spelling at this occurrence.
    pub spelling: String,
    /// Causal source provenance for the occurrence site.
    pub origin: Origin,
}

/// One resolved Mini-Ash source file.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedProgram {
    /// Immutable nominal and constructor registry.
    pub registry: Arc<ResolvedRegistry>,
    /// Resolved global definitions in source order.
    pub definitions: Vec<ResolvedDefinition>,
    /// Required final result expression.
    pub result: ResolvedExpr,
    /// Complete accepted source span.
    pub span: Span,
}

/// Immutable resolved metadata for one source file.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ResolvedRegistry {
    nominals: Box<[ResolvedNominalType]>,
    constructors: Box<[ResolvedConstructor]>,
    nominal_positions: HashMap<NominalTypeId, usize>,
    constructor_positions: HashMap<ConstructorId, usize>,
    nominal_parameters: HashMap<NominalTypeId, Box<[ResolvedTypeVariable]>>,
    type_variables: HashMap<TypeVariableId, ResolvedTypeVariable>,
}

impl ResolvedRegistry {
    /// Constructs one closed registry after two-pass resolution.
    #[must_use]
    pub fn new(nominals: Vec<ResolvedNominalType>, constructors: Vec<ResolvedConstructor>) -> Self {
        let nominal_positions = nominals
            .iter()
            .enumerate()
            .map(|(index, nominal)| (nominal.id, index))
            .collect();
        let constructor_positions = constructors
            .iter()
            .enumerate()
            .map(|(index, constructor)| (constructor.id, index))
            .collect();
        Self {
            nominals: nominals.into_boxed_slice(),
            constructors: constructors.into_boxed_slice(),
            nominal_positions,
            constructor_positions,
            nominal_parameters: HashMap::new(),
            type_variables: HashMap::new(),
        }
    }

    /// Attaches ordered declaration parameters after nominal identity allocation.
    #[must_use]
    pub fn with_type_parameters(
        mut self,
        parameters: Vec<(NominalTypeId, Vec<ResolvedTypeVariable>)>,
    ) -> Self {
        for (owner, parameters) in parameters {
            for parameter in &parameters {
                self.insert_type_variable(parameter.clone());
            }
            if let Some(replaced) = self
                .nominal_parameters
                .insert(owner, parameters.into_boxed_slice())
            {
                for parameter in replaced.into_vec() {
                    discard_origin_iteratively(parameter.origin);
                }
            }
        }
        self
    }

    /// Attaches non-nominal type parameters before the registry is published.
    #[must_use]
    pub(crate) fn with_additional_type_variables(
        mut self,
        parameters: impl IntoIterator<Item = ResolvedTypeVariable>,
    ) -> Self {
        for parameter in parameters {
            self.insert_type_variable(parameter);
        }
        self
    }

    fn insert_type_variable(&mut self, parameter: ResolvedTypeVariable) {
        if let Some(replaced) = self.type_variables.insert(parameter.id, parameter) {
            discard_origin_iteratively(replaced.origin);
        }
    }

    /// Returns nominal declarations in source order.
    #[must_use]
    pub fn nominals(&self) -> &[ResolvedNominalType] {
        &self.nominals
    }

    /// Returns constructors in file and declaration order.
    #[must_use]
    pub fn constructors(&self) -> &[ResolvedConstructor] {
        &self.constructors
    }

    /// Looks up a nominal declaration by stable identity.
    #[must_use]
    pub fn nominal(&self, id: NominalTypeId) -> Option<&ResolvedNominalType> {
        self.nominal_positions
            .get(&id)
            .and_then(|index| self.nominals.get(*index))
            .filter(|nominal| nominal.id == id)
    }

    /// Looks up a constructor by stable identity.
    #[must_use]
    pub fn constructor(&self, id: ConstructorId) -> Option<&ResolvedConstructor> {
        self.constructor_positions
            .get(&id)
            .and_then(|index| self.constructors.get(*index))
            .filter(|constructor| constructor.id == id)
    }

    /// Looks up a declaration type parameter by stable identity.
    #[must_use]
    pub fn type_variable(&self, id: TypeVariableId) -> Option<&ResolvedTypeVariable> {
        self.type_variables.get(&id)
    }

    /// Returns a nominal declaration's ordered parameters.
    #[must_use]
    pub fn nominal_parameters(&self, id: NominalTypeId) -> Option<&[ResolvedTypeVariable]> {
        self.nominal(id)?;
        Some(self.nominal_parameters.get(&id).map_or(&[], Box::as_ref))
    }

    pub(crate) fn nominal_parameter_entries(
        &self,
    ) -> impl Iterator<Item = (NominalTypeId, &[ResolvedTypeVariable])> {
        self.nominal_parameters
            .iter()
            .map(|(owner, parameters)| (*owner, parameters.as_ref()))
    }

    /// Renders a type with source declaration spellings for nominal identities.
    #[must_use]
    pub fn display_type(&self, ty: &Type) -> String {
        self.display_type_with_inference(ty, false)
    }

    /// Renders a source-facing type without exposing elaborator inference identities.
    #[must_use]
    pub(crate) fn display_source_type(&self, ty: &Type) -> String {
        self.display_type_with_inference(ty, true)
    }

    fn display_type_with_inference(&self, ty: &Type, anonymous_inference: bool) -> String {
        enum Task<'a> {
            Type(&'a Type),
            Text(&'static str),
        }

        let mut output = String::new();
        let mut work = vec![Task::Type(ty)];
        while let Some(task) = work.pop() {
            match task {
                Task::Text(text) => output.push_str(text),
                Task::Type(Type::Int) => output.push_str("Int"),
                Task::Type(Type::Bool) => output.push_str("Bool"),
                Task::Type(Type::Unit) => output.push_str("Unit"),
                Task::Type(Type::Nominal(id)) => {
                    if let Some(nominal) = self.nominal(*id) {
                        output.push_str(&nominal.spelling);
                    } else {
                        output.push_str(&Type::Nominal(*id).to_string());
                    }
                }
                Task::Type(Type::Variable(id)) => {
                    if let Some(variable) = self.type_variable(*id) {
                        output.push_str(&variable.spelling);
                    } else {
                        output.push_str(&Type::Variable(*id).to_string());
                    }
                }
                Task::Type(Type::Inference(id)) => {
                    if anonymous_inference {
                        output.push('_');
                    } else {
                        output.push_str(&Type::Inference(*id).to_string());
                    }
                }
                Task::Type(Type::AppliedNominal(id, arguments)) => {
                    if let Some(nominal) = self.nominal(*id) {
                        output.push_str(&nominal.spelling);
                    } else {
                        output.push_str(&Type::Nominal(*id).to_string());
                    }
                    output.push('<');
                    work.push(Task::Text(">"));
                    for (index, argument) in arguments.iter().enumerate().rev() {
                        work.push(Task::Type(argument));
                        if index > 0 {
                            work.push(Task::Text(", "));
                        }
                    }
                }
                Task::Type(Type::Forall(parameters, body)) => {
                    output.push_str("forall ");
                    for (index, parameter) in parameters.iter().enumerate() {
                        if index > 0 {
                            output.push_str(", ");
                        }
                        if let Some(variable) = self.type_variable(*parameter) {
                            output.push_str(&variable.spelling);
                        } else {
                            output.push_str(&format!("T{}", parameter.value()));
                        }
                    }
                    output.push_str(". ");
                    work.push(Task::Type(body));
                }
                Task::Type(Type::Tuple(elements)) => {
                    output.push('(');
                    work.push(Task::Text(")"));
                    for (index, element) in elements.iter().enumerate().rev() {
                        work.push(Task::Type(element));
                        if index > 0 {
                            work.push(Task::Text(", "));
                        }
                    }
                }
                Task::Type(Type::Function(domain, codomain)) => {
                    work.push(Task::Type(codomain));
                    work.push(Task::Text(" -> "));
                    if matches!(domain.as_ref(), Type::Function(_, _)) {
                        work.push(Task::Text(")"));
                        work.push(Task::Type(domain));
                        work.push(Task::Text("("));
                    } else {
                        work.push(Task::Type(domain));
                    }
                }
            }
        }
        output
    }

    /// Destroys untrusted registry payloads without following host recursion.
    pub(crate) fn discard_iteratively(mut self) {
        self.discard_owned_payloads();
    }

    fn discard_owned_payloads(&mut self) {
        let nominals = std::mem::take(&mut self.nominals);
        let constructors = std::mem::take(&mut self.constructors);
        let nominal_parameters = std::mem::take(&mut self.nominal_parameters);
        let type_variables = std::mem::take(&mut self.type_variables);
        self.nominal_positions.clear();
        self.constructor_positions.clear();
        for nominal in nominals.into_vec() {
            discard_origin_iteratively(nominal.origin);
        }
        for constructor in constructors.into_vec() {
            if let Some(payload) = constructor.payload {
                discard_type_iteratively(payload);
            }
            discard_origin_iteratively(constructor.origin);
        }
        for parameters in nominal_parameters.into_values() {
            for parameter in parameters.into_vec() {
                discard_origin_iteratively(parameter.origin);
            }
        }
        for parameter in type_variables.into_values() {
            discard_origin_iteratively(parameter.origin);
        }
    }
}

impl Drop for ResolvedRegistry {
    fn drop(&mut self) {
        self.discard_owned_payloads();
    }
}

/// Resolved metadata for one nominal declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedNominalType {
    /// Stable source-order identity.
    pub id: NominalTypeId,
    /// Exact declaration spelling.
    pub spelling: String,
    /// Constructor identities in declaration order.
    pub constructors: Box<[ConstructorId]>,
    /// Declaration provenance.
    pub origin: Origin,
}

/// One resolved source type binder.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedTypeVariable {
    /// Stable program-local identity.
    pub id: TypeVariableId,
    /// Exact source spelling.
    pub spelling: String,
    /// Definition provenance.
    pub origin: Origin,
}

/// Resolved metadata for one constructor declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedConstructor {
    /// Stable constructor identity.
    pub id: ConstructorId,
    /// Owning nominal identity.
    pub owner: NominalTypeId,
    /// Exact constructor spelling.
    pub spelling: String,
    /// Zero or one semantic payload type.
    pub payload: Option<Type>,
    /// Declaration provenance.
    pub origin: Origin,
}

/// One fully resolved type occurrence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedType {
    /// Resolved structural or nominal type.
    pub ty: Type,
    /// Stack-safe provenance aligned with every structural type component.
    pub provenance: ResolvedTypeProvenance,
    /// Causal source provenance.
    pub origin: Origin,
    /// Complete source occurrence span.
    pub span: Span,
}

/// Shareable arena-shaped provenance for one resolved type occurrence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedTypeProvenance {
    nodes: Arc<[ResolvedTypeProvenanceNode]>,
    root: usize,
}

/// One node in a resolved type-provenance arena.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResolvedTypeProvenanceNode {
    /// An atomic or nominal type occurrence.
    Fact(Span),
    /// A tuple occurrence and its element provenance roots.
    Tuple { span: Span, elements: Box<[usize]> },
    /// A function occurrence and its component provenance roots.
    Function {
        span: Span,
        domain: usize,
        codomain: usize,
    },
    /// A saturated nominal type application and its argument roots.
    Application { span: Span, arguments: Box<[usize]> },
}

impl ResolvedTypeProvenance {
    /// Builds an admitted provenance arena from source-ordered nodes.
    #[must_use]
    pub(crate) fn new(nodes: Vec<ResolvedTypeProvenanceNode>, root: usize) -> Self {
        Self {
            nodes: nodes.into(),
            root,
        }
    }

    /// Returns the complete source span of this provenance view.
    #[must_use]
    pub fn span(&self) -> Option<Span> {
        self.nodes.get(self.root).map(|node| match node {
            ResolvedTypeProvenanceNode::Fact(span)
            | ResolvedTypeProvenanceNode::Tuple { span, .. }
            | ResolvedTypeProvenanceNode::Function { span, .. }
            | ResolvedTypeProvenanceNode::Application { span, .. } => *span,
        })
    }

    /// Returns views of a function domain and codomain.
    #[must_use]
    pub fn function_parts(&self) -> Option<(Self, Self)> {
        let ResolvedTypeProvenanceNode::Function {
            domain, codomain, ..
        } = self.nodes.get(self.root)?
        else {
            return None;
        };
        Some((self.view(*domain)?, self.view(*codomain)?))
    }

    /// Returns tuple element views in source order.
    #[must_use]
    pub fn tuple_elements(&self) -> Option<Vec<Self>> {
        let ResolvedTypeProvenanceNode::Tuple { elements, .. } = self.nodes.get(self.root)? else {
            return None;
        };
        elements.iter().map(|root| self.view(*root)).collect()
    }

    fn view(&self, root: usize) -> Option<Self> {
        self.nodes.get(root)?;
        Some(Self {
            nodes: Arc::clone(&self.nodes),
            root,
        })
    }

    pub(crate) fn nodes(&self) -> &[ResolvedTypeProvenanceNode] {
        &self.nodes
    }

    pub(crate) const fn root(&self) -> usize {
        self.root
    }
}

/// One resolved global definition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedDefinition {
    /// Presentation-specific definition payload.
    pub kind: ResolvedDefinitionKind,
    /// Complete definition span.
    pub span: Span,
}

/// The closed resolved global-definition family.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResolvedDefinitionKind {
    /// An external interface followed by an equation.
    Equational(ResolvedEquationalGlobal),
    /// An inline operational function definition.
    InlineOperational(ResolvedInlineOperationalGlobal),
}

/// A resolved equational global.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedEquationalGlobal {
    /// Separately written external interface.
    pub interface: ResolvedExternalInterface,
    /// Nonempty contiguous clause group.
    pub equations: Vec<ResolvedEquation>,
}

/// A resolved external interface.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedExternalInterface {
    /// Global definition site.
    pub name: Binder,
    /// Declared resolved type.
    pub annotation: ResolvedType,
    /// Implicit outer type binders in first-occurrence order.
    pub type_parameters: Box<[ResolvedTypeVariable]>,
    /// Complete interface span.
    pub span: Span,
}

/// A resolved equation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedEquation {
    /// Repeated global name in the equation head.
    pub name: ResolvedOccurrence,
    /// Patterns consuming successive arrow domains.
    pub patterns: Vec<ResolvedPattern>,
    /// Resolved equation body.
    pub body: ResolvedExpr,
    /// Complete equation span.
    pub span: Span,
}

/// A resolved inline operational global.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedInlineOperationalGlobal {
    /// Complete operational header.
    pub header: ResolvedInlineOperationalHeader,
    /// Resolved braced body.
    pub body: ResolvedBlock,
}

/// A resolved inline operational header.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedInlineOperationalHeader {
    /// Global definition site.
    pub name: Binder,
    /// Nonempty typed operational parameter vector.
    pub parameters: Vec<ResolvedTypedPattern>,
    /// Declared result type.
    pub result_type: ResolvedType,
    /// Implicit outer type binders in first-occurrence order.
    pub type_parameters: Box<[ResolvedTypeVariable]>,
    /// Complete header span, excluding the body.
    pub span: Span,
}

/// One resolved pattern with a resolved type annotation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedTypedPattern {
    /// Resolved pattern.
    pub pattern: ResolvedPattern,
    /// Required resolved type.
    pub annotation: ResolvedType,
    /// Complete source span.
    pub span: Span,
}

/// One resolved pattern.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedPattern {
    /// Resolved pattern payload.
    pub kind: ResolvedPatternKind,
    /// Complete pattern span.
    pub span: Span,
}

/// The closed resolved pattern family.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResolvedPatternKind {
    /// A stable binder definition.
    Binder(Binder),
    /// A nonbinding wildcard.
    Wildcard,
    /// A Boolean literal pattern.
    Boolean(bool),
    /// Unit.
    Unit,
    /// A structural tuple pattern.
    Tuple(Vec<ResolvedPattern>),
    /// A constructor identity and optional payload pattern.
    Constructor {
        /// Resolved constructor identity.
        constructor: ConstructorId,
        /// Original spelling and source provenance.
        occurrence: ResolvedConstructorOccurrence,
        /// Optional payload pattern.
        payload: Option<Box<ResolvedPattern>>,
    },
}

/// A resolved sequential block.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedBlock {
    /// Ordered resolved local declarations.
    pub declarations: Vec<ResolvedLocalDeclaration>,
    /// Required block result expression.
    pub result: Box<ResolvedExpr>,
    /// Complete braced span.
    pub span: Span,
}

/// The closed resolved local-declaration family.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResolvedLocalDeclaration {
    /// A sequential nonrecursive binding.
    Binding(Box<ResolvedBinding>),
    /// A simultaneous recursive binding group.
    Recursive(ResolvedRecursiveGroup),
}

/// One resolved simultaneous recursive binding group.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedRecursiveGroup {
    /// Members in source order.
    pub members: Vec<ResolvedRecursiveMember>,
    /// Complete recursive group span.
    pub span: Span,
}

/// One resolved recursive group member.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedRecursiveMember {
    /// The `let rec` or `and` delimiter introducing this member.
    pub introducer_span: Span,
    /// Introduced definition site.
    pub binder: Binder,
    /// Required declared monotype.
    pub annotation: ResolvedType,
    /// Initializer resolved in the simultaneous group scope.
    pub initializer: ResolvedExpr,
    /// Complete member span.
    pub span: Span,
}

/// A resolved immutable local binding.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedBinding {
    /// Introduced irrefutable pattern.
    pub pattern: ResolvedPattern,
    /// Optional source type annotation.
    pub annotation: Option<ResolvedType>,
    /// Initializer resolved in the incoming scope.
    pub initializer: ResolvedExpr,
    /// Complete binding span.
    pub span: Span,
}

/// A resolved expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedExpr {
    /// Resolved expression payload.
    pub kind: ResolvedExprKind,
    /// Complete expression span.
    pub span: Span,
}

/// The closed resolved expression family.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResolvedExprKind {
    /// An arbitrary-precision integer literal.
    Integer(Integer),
    /// A Boolean literal.
    Boolean(bool),
    /// The unit value.
    Unit,
    /// A resolved name occurrence.
    Occurrence(ResolvedOccurrence),
    /// A resolved constructor term occurrence.
    Constructor(ResolvedConstructorOccurrence),
    /// A strict structural tuple.
    Tuple(Vec<ResolvedExpr>),
    /// Strict unary application.
    Apply(ResolvedApplicationExpr),
    /// Integer addition.
    Add(ResolvedBinaryExpr),
    /// Integer multiplication.
    Multiply(ResolvedBinaryExpr),
    /// Integer equality.
    Equal(ResolvedBinaryExpr),
    /// A sequential block expression.
    Block(ResolvedBlock),
    /// An anonymous unary function.
    Function(ResolvedFunctionExpr),
    /// A structured match.
    Match(ResolvedMatchExpr),
}

/// One resolved constructor occurrence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedConstructorOccurrence {
    /// Stable constructor identity.
    pub constructor: ConstructorId,
    /// Exact source spelling.
    pub spelling: String,
    /// Causal source provenance.
    pub origin: Origin,
}

/// A resolved structured match.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedMatchExpr {
    /// Resolved scrutinee.
    pub scrutinee: Box<ResolvedExpr>,
    /// Source-ordered arms.
    pub arms: Vec<ResolvedMatchArm>,
}

/// One resolved match arm.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedMatchArm {
    /// Resolved arm pattern.
    pub pattern: ResolvedPattern,
    /// Resolved arm body.
    pub body: ResolvedExpr,
    /// Complete arm span.
    pub span: Span,
}

/// A resolved unary application.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedApplicationExpr {
    /// Resolved function position.
    pub function: Box<ResolvedExpr>,
    /// Resolved argument position.
    pub argument: Box<ResolvedExpr>,
}

/// A resolved binary expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedBinaryExpr {
    /// Resolved left operand.
    pub left: Box<ResolvedExpr>,
    /// Resolved right operand.
    pub right: Box<ResolvedExpr>,
    /// Exact source span of the operator token.
    pub operator_span: Span,
}

/// A resolved anonymous function expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedFunctionExpr {
    /// Unary domain pattern.
    pub pattern: ResolvedPattern,
    /// Resolved braced body.
    pub body: ResolvedBlock,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::source::{ByteRange, GeneratedReason, SourceFile};

    #[test]
    fn destroys_replaced_additional_type_variables_on_a_small_stack() {
        std::thread::scope(|scope| {
            std::thread::Builder::new()
                .stack_size(256 * 1024)
                .spawn_scoped(scope, move || {
                    let file = SourceFile::new("additional parameter", "parameter")
                        .expect("test source should fit");
                    let span = file
                        .span(ByteRange::new(0, 1).expect("ordered parameter range"))
                        .expect("parameter range should belong to source");
                    let mut origin = Origin::Source(span);
                    for index in 0..5_000 {
                        origin = if index % 2 == 0 {
                            Origin::Generated {
                                cause: Box::new(origin),
                                reason: GeneratedReason::TypeChecking,
                            }
                        } else {
                            Origin::Related {
                                primary: Box::new(origin),
                                related: vec![span],
                            }
                        };
                    }
                    let parameter = TypeVariableId::new(0);
                    let registry = ResolvedRegistry::new(Vec::new(), Vec::new())
                        .with_additional_type_variables([
                            ResolvedTypeVariable {
                                id: parameter,
                                spelling: "A".into(),
                                origin,
                            },
                            ResolvedTypeVariable {
                                id: parameter,
                                spelling: "B".into(),
                                origin: Origin::Source(span),
                            },
                        ]);
                    assert_eq!(
                        registry
                            .type_variable(parameter)
                            .map(|parameter| parameter.spelling.as_str()),
                        Some("B")
                    );
                    drop(registry);
                })
                .expect("small-stack thread should start")
                .join()
                .expect("replaced additional parameter teardown must fit the small stack");
        });
    }
}
