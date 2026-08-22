use std::collections::HashMap;

use ash::{
    core::{
        CoreBuilder, MiniAshPureDialect, NodeId, Primitive, PureComputation, PureExprKind,
        PureValue, TypedExpr, ValidatedProgram,
        binding::BindingNode,
        data::{ConstructorNode, MatchNode, TupleNode},
        function::{ApplicationNode, FunctionNode},
        literal::{BooleanNode, IntegerNode, UnitNode},
        primitive::PrimitiveNode,
        recursion::RecursiveBindingNode,
        validate,
        variable::VariableNode,
    },
    integer::Integer,
    resolved::BinderId,
    source::{ByteRange, Origin, SourceFile},
    types::Type,
};

trait OperationFamily {
    type Operation;
}

enum PureOperation {}

struct PureOperations;

impl OperationFamily for PureOperations {
    type Operation = PureOperation;
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum MockFutureOperation {
    YieldOnce,
}

struct MockFutureOperations;

impl OperationFamily for MockFutureOperations {
    type Operation = MockFutureOperation;
}

enum Computation<F: OperationFamily> {
    Pure {
        result: Type,
        computation: PureComputation,
    },
    Operation {
        result: Type,
        operation: F::Operation,
    },
}

fn computation_result<F: OperationFamily>(computation: &Computation<F>) -> &Type {
    match computation {
        Computation::Pure { result, .. } | Computation::Operation { result, .. } => result,
    }
}

fn pure_computation_result(computation: &Computation<PureOperations>) -> &Type {
    match computation {
        Computation::Pure { result, .. } => result,
        Computation::Operation { operation, .. } => match *operation {},
    }
}

fn primitive_program() -> (ValidatedProgram, NodeId) {
    let source = SourceFile::new("architecture.ash", "1 + 2").expect("test source");
    let range = ByteRange::new(0, 5).expect("ordered test range");
    let origin = Origin::Source(source.span(range).expect("test span"));
    let mut builder = CoreBuilder::new();
    let left = builder
        .integer(
            Integer::parse_decimal("1").expect("test integer"),
            Type::Int,
            origin.clone(),
        )
        .expect("small arena");
    let right = builder
        .integer(
            Integer::parse_decimal("2").expect("test integer"),
            Type::Int,
            origin.clone(),
        )
        .expect("small arena");
    let root = builder
        .primitive(Primitive::Add, left, right, Type::Int, origin)
        .expect("small arena");
    let program = validate(builder.finish(root).expect("valid root"), &[&source])
        .expect("valid test computation");
    (program, root)
}

fn pure_payload(program: &ValidatedProgram, root: NodeId) -> PureComputation {
    match &program.node(root).expect("validated root").kind {
        PureExprKind::Computation(computation) => computation.clone(),
        PureExprKind::Value(_) | PureExprKind::Variable(_) => {
            panic!("expected primitive computation")
        }
    }
}

mod mock_feature {
    use ash::types::Type;

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub struct MockNode;

    impl MockNode {
        pub const fn expected_type(self) -> Type {
            Type::Unit
        }
    }
}

struct ShadowTypedExpr {
    ty: Type,
    kind: ShadowExprKind,
}

enum ShadowExprKind {
    Value(ShadowValue),
    Variable(VariableNode),
    Computation(ShadowPureComputation),
    Mock(mock_feature::MockNode),
}

enum ShadowValue {
    Integer(IntegerNode),
    Boolean(BooleanNode),
    Unit(UnitNode),
    Function(FunctionNode),
    Constructor(ConstructorNode),
}

enum ShadowPureComputation {
    Bind(BindingNode),
    RecursiveBind(RecursiveBindingNode),
    Apply(ApplicationNode),
    Primitive(PrimitiveNode),
    Tuple(TupleNode),
    Match(MatchNode),
}

fn assemble_shadow(expression: &TypedExpr) -> ShadowTypedExpr {
    let kind = match &expression.kind {
        PureExprKind::Value(value) => ShadowExprKind::Value(match value {
            PureValue::Integer(node) => ShadowValue::Integer(node.clone()),
            PureValue::Boolean(node) => ShadowValue::Boolean(*node),
            PureValue::Unit(node) => ShadowValue::Unit(*node),
            PureValue::Function(node) => ShadowValue::Function(node.clone()),
            PureValue::Constructor(node) => ShadowValue::Constructor(*node),
        }),
        PureExprKind::Variable(node) => ShadowExprKind::Variable(*node),
        PureExprKind::Computation(computation) => ShadowExprKind::Computation(match computation {
            PureComputation::Bind(node) => ShadowPureComputation::Bind(node.clone()),
            PureComputation::RecursiveBind(node) => {
                ShadowPureComputation::RecursiveBind(node.clone())
            }
            PureComputation::Apply(node) => ShadowPureComputation::Apply(*node),
            PureComputation::Primitive(node) => ShadowPureComputation::Primitive(*node),
            PureComputation::Tuple(node) => ShadowPureComputation::Tuple(node.clone()),
            PureComputation::Match(node) => ShadowPureComputation::Match(node.clone()),
        }),
    };
    ShadowTypedExpr {
        ty: expression.ty.clone(),
        kind,
    }
}

fn mock_shadow() -> ShadowTypedExpr {
    ShadowTypedExpr {
        ty: Type::Unit,
        kind: ShadowExprKind::Mock(mock_feature::MockNode),
    }
}

struct ShadowFacts<'program> {
    program: &'program ValidatedProgram,
    binders: &'program HashMap<BinderId, Type>,
}

impl ShadowFacts<'_> {
    fn node_type(&self, node: NodeId) -> Option<&Type> {
        self.program.node(node).map(|expression| &expression.ty)
    }
}

fn validate_shadow(expression: &ShadowTypedExpr, facts: &ShadowFacts<'_>) -> bool {
    match &expression.kind {
        ShadowExprKind::Value(value) => validate_shadow_value(&expression.ty, value, facts),
        ShadowExprKind::Variable(variable) => {
            facts.binders.get(&variable.binder()) == Some(&expression.ty)
        }
        ShadowExprKind::Computation(computation) => {
            validate_shadow_computation(&expression.ty, computation, facts)
        }
        ShadowExprKind::Mock(node) => expression.ty == node.expected_type(),
    }
}

fn validate_shadow_value(ty: &Type, value: &ShadowValue, facts: &ShadowFacts<'_>) -> bool {
    match value {
        ShadowValue::Integer(node) => {
            let _ = node.value();
            *ty == Type::Int
        }
        ShadowValue::Boolean(node) => {
            let _ = node.value();
            *ty == Type::Bool
        }
        ShadowValue::Unit(_) => *ty == Type::Unit,
        ShadowValue::Function(node) => facts.node_type(node.body()).is_some_and(|body_type| {
            ty == &Type::Function(
                Box::new(node.parameter().ty().clone()),
                Box::new(body_type.clone()),
            )
        }),
        ShadowValue::Constructor(node) => {
            let _ = node.constructor();
            true
        }
    }
}

fn validate_shadow_computation(
    ty: &Type,
    computation: &ShadowPureComputation,
    facts: &ShadowFacts<'_>,
) -> bool {
    match computation {
        ShadowPureComputation::Bind(node) => {
            facts.node_type(node.initializer()) == Some(node.binder().ty())
                && facts.node_type(node.body()) == Some(ty)
        }
        ShadowPureComputation::RecursiveBind(node) => {
            !node.members().is_empty()
                && facts.node_type(node.body()) == Some(ty)
                && node.members().iter().all(|member| {
                    facts.node_type(member.initializer()) == Some(member.binder().ty())
                })
        }
        ShadowPureComputation::Apply(node) => {
            let Some(Type::Function(domain, codomain)) = facts.node_type(node.function()) else {
                return false;
            };
            facts.node_type(node.argument()) == Some(domain.as_ref()) && codomain.as_ref() == ty
        }
        ShadowPureComputation::Primitive(node) => {
            let (left, right, result) = match node.primitive() {
                Primitive::Add | Primitive::Multiply => (Type::Int, Type::Int, Type::Int),
                Primitive::Equal => (Type::Int, Type::Int, Type::Bool),
            };
            facts.node_type(node.left()) == Some(&left)
                && facts.node_type(node.right()) == Some(&right)
                && ty == &result
        }
        ShadowPureComputation::Tuple(node) => {
            let Type::Tuple(types) = ty else { return false };
            node.elements().len() == types.len()
                && node
                    .elements()
                    .iter()
                    .zip(types)
                    .all(|(element, expected)| facts.node_type(*element) == Some(expected))
        }
        ShadowPureComputation::Match(node) => {
            facts.node_type(node.scrutinee()).is_some()
                && node
                    .arms()
                    .iter()
                    .all(|arm| facts.node_type(arm.body()) == Some(ty))
        }
    }
}

fn traverse_shadow(expression: &ShadowTypedExpr) -> Vec<NodeId> {
    match &expression.kind {
        ShadowExprKind::Value(value) => match value {
            ShadowValue::Function(node) => vec![node.body()],
            ShadowValue::Integer(_)
            | ShadowValue::Boolean(_)
            | ShadowValue::Unit(_)
            | ShadowValue::Constructor(_) => Vec::new(),
        },
        ShadowExprKind::Variable(_) | ShadowExprKind::Mock(_) => Vec::new(),
        ShadowExprKind::Computation(computation) => match computation {
            ShadowPureComputation::Bind(node) => vec![node.initializer(), node.body()],
            ShadowPureComputation::RecursiveBind(node) => node
                .members()
                .iter()
                .map(|member| member.initializer())
                .chain(std::iter::once(node.body()))
                .collect(),
            ShadowPureComputation::Apply(node) => vec![node.function(), node.argument()],
            ShadowPureComputation::Primitive(node) => vec![node.left(), node.right()],
            ShadowPureComputation::Tuple(node) => node.elements().to_vec(),
            ShadowPureComputation::Match(node) => std::iter::once(node.scrutinee())
                .chain(node.arms().iter().map(|arm| arm.body()))
                .collect(),
        },
    }
}

#[derive(Debug, Eq, PartialEq)]
enum ShadowTransformPlan {
    Preserve(Vec<NodeId>),
    ReplaceWithMockUnit,
}

fn transform_shadow(expression: &ShadowTypedExpr) -> ShadowTransformPlan {
    match &expression.kind {
        ShadowExprKind::Value(value) => match value {
            ShadowValue::Function(node) => ShadowTransformPlan::Preserve(vec![node.body()]),
            ShadowValue::Integer(_)
            | ShadowValue::Boolean(_)
            | ShadowValue::Unit(_)
            | ShadowValue::Constructor(_) => ShadowTransformPlan::Preserve(Vec::new()),
        },
        ShadowExprKind::Variable(_) => ShadowTransformPlan::Preserve(Vec::new()),
        ShadowExprKind::Computation(computation) => match computation {
            ShadowPureComputation::Bind(node) => {
                ShadowTransformPlan::Preserve(vec![node.initializer(), node.body()])
            }
            ShadowPureComputation::RecursiveBind(node) => ShadowTransformPlan::Preserve(
                node.members()
                    .iter()
                    .map(|member| member.initializer())
                    .chain(std::iter::once(node.body()))
                    .collect(),
            ),
            ShadowPureComputation::Apply(node) => {
                ShadowTransformPlan::Preserve(vec![node.function(), node.argument()])
            }
            ShadowPureComputation::Primitive(node) => {
                ShadowTransformPlan::Preserve(vec![node.left(), node.right()])
            }
            ShadowPureComputation::Tuple(node) => {
                ShadowTransformPlan::Preserve(node.elements().to_vec())
            }
            ShadowPureComputation::Match(node) => ShadowTransformPlan::Preserve(
                std::iter::once(node.scrutinee())
                    .chain(node.arms().iter().map(|arm| arm.body()))
                    .collect(),
            ),
        },
        ShadowExprKind::Mock(_) => ShadowTransformPlan::ReplaceWithMockUnit,
    }
}

fn consume_shadow(expression: &ShadowTypedExpr) -> &'static str {
    match &expression.kind {
        ShadowExprKind::Value(value) => match value {
            ShadowValue::Integer(_) => "integer",
            ShadowValue::Boolean(_) => "boolean",
            ShadowValue::Unit(_) => "unit",
            ShadowValue::Function(_) => "function",
            ShadowValue::Constructor(_) => "constructor",
        },
        ShadowExprKind::Variable(_) => "variable",
        ShadowExprKind::Computation(computation) => match computation {
            ShadowPureComputation::Bind(_) => "binding",
            ShadowPureComputation::RecursiveBind(_) => "recursive binding",
            ShadowPureComputation::Apply(_) => "application",
            ShadowPureComputation::Primitive(_) => "primitive",
            ShadowPureComputation::Tuple(_) => "tuple",
            ShadowPureComputation::Match(_) => "match",
        },
        ShadowExprKind::Mock(_) => "mock",
    }
}

struct Representative {
    program: ValidatedProgram,
    binders: HashMap<BinderId, Type>,
    one: NodeId,
    two: NodeId,
    primitive: NodeId,
    variable: NodeId,
    function: NodeId,
    application: NodeId,
    result_variable: NodeId,
    inner_binding: NodeId,
    boolean: NodeId,
    boolean_binding: NodeId,
    unit: NodeId,
    root: NodeId,
}

fn representative_program() -> Representative {
    let source = SourceFile::new("shadow.ash", "representative").expect("test source");
    let range = ByteRange::new(0, 14).expect("ordered test range");
    let origin = Origin::Source(source.span(range).expect("test span"));
    let mut builder = CoreBuilder::new();
    let one = builder
        .integer(
            Integer::parse_decimal("1").expect("test integer"),
            Type::Int,
            origin.clone(),
        )
        .expect("small arena");
    let two = builder
        .integer(
            Integer::parse_decimal("2").expect("test integer"),
            Type::Int,
            origin.clone(),
        )
        .expect("small arena");
    let primitive = builder
        .primitive(Primitive::Add, one, two, Type::Int, origin.clone())
        .expect("small arena");
    let parameter = builder
        .binder(Type::Int, origin.clone())
        .expect("small binder set");
    let variable = builder
        .variable(parameter.id(), Type::Int, origin.clone())
        .expect("small arena");
    let function = builder
        .function(
            parameter.clone(),
            variable,
            Type::Function(Box::new(Type::Int), Box::new(Type::Int)),
            origin.clone(),
        )
        .expect("small arena");
    let application = builder
        .application(function, primitive, Type::Int, origin.clone())
        .expect("small arena");
    let result_binder = builder
        .binder(Type::Int, origin.clone())
        .expect("small binder set");
    let result_variable = builder
        .variable(result_binder.id(), Type::Int, origin.clone())
        .expect("small arena");
    let inner_binding = builder
        .binding(
            result_binder.clone(),
            application,
            result_variable,
            Type::Int,
            origin.clone(),
        )
        .expect("small arena");
    let boolean = builder
        .boolean(true, Type::Bool, origin.clone())
        .expect("small arena");
    let boolean_binder = builder
        .binder(Type::Bool, origin.clone())
        .expect("small binder set");
    let boolean_binding = builder
        .binding(
            boolean_binder.clone(),
            boolean,
            inner_binding,
            Type::Int,
            origin.clone(),
        )
        .expect("small arena");
    let unit = builder
        .unit(Type::Unit, origin.clone())
        .expect("small arena");
    let unit_binder = builder
        .binder(Type::Unit, origin.clone())
        .expect("small binder set");
    let root = builder
        .binding(
            unit_binder.clone(),
            unit,
            boolean_binding,
            Type::Int,
            origin,
        )
        .expect("small arena");
    let program = validate(builder.finish(root).expect("valid root"), &[&source])
        .expect("valid representative program");
    let binders = HashMap::from([
        (parameter.id(), parameter.ty().clone()),
        (result_binder.id(), result_binder.ty().clone()),
        (boolean_binder.id(), boolean_binder.ty().clone()),
        (unit_binder.id(), unit_binder.ty().clone()),
    ]);

    Representative {
        program,
        binders,
        one,
        two,
        primitive,
        variable,
        function,
        application,
        result_variable,
        inner_binding,
        boolean,
        boolean_binding,
        unit,
        root,
    }
}

#[test]
fn pure_dialect_is_named_and_has_no_inhabited_operation_family() {
    assert_eq!(MiniAshPureDialect::NAME, "mini-ash.pure");

    let (program, root) = primitive_program();
    let pure = Computation::<PureOperations>::Pure {
        result: Type::Int,
        computation: pure_payload(&program, root),
    };
    assert_eq!(pure_computation_result(&pure), &Type::Int);
    let Computation::Pure { computation, .. } = pure;
    assert!(matches!(computation, PureComputation::Primitive(_)));
}

#[test]
fn future_operation_crosses_one_boundary_without_changing_pure_features() {
    let request = Computation::<MockFutureOperations>::Operation {
        result: Type::Unit,
        operation: MockFutureOperation::YieldOnce,
    };
    assert_eq!(computation_result(&request), &Type::Unit);
    let Computation::Operation { operation, .. } = request else {
        panic!("expected mock operation")
    };
    assert_eq!(operation, MockFutureOperation::YieldOnce);

    let unchanged_pure_node = PureExprKind::Value(PureValue::Unit(UnitNode));
    assert!(matches!(
        unchanged_pure_node,
        PureExprKind::Value(PureValue::Unit(_))
    ));
}

#[test]
fn one_mock_pure_feature_changes_only_the_recorded_closed_sites() {
    let representative = representative_program();
    let facts = ShadowFacts {
        program: &representative.program,
        binders: &representative.binders,
    };
    let cases = [
        (representative.one, "integer", vec![]),
        (representative.two, "integer", vec![]),
        (
            representative.primitive,
            "primitive",
            vec![representative.one, representative.two],
        ),
        (representative.variable, "variable", vec![]),
        (
            representative.function,
            "function",
            vec![representative.variable],
        ),
        (
            representative.application,
            "application",
            vec![representative.function, representative.primitive],
        ),
        (representative.result_variable, "variable", vec![]),
        (
            representative.inner_binding,
            "binding",
            vec![representative.application, representative.result_variable],
        ),
        (representative.boolean, "boolean", vec![]),
        (
            representative.boolean_binding,
            "binding",
            vec![representative.boolean, representative.inner_binding],
        ),
        (representative.unit, "unit", vec![]),
        (
            representative.root,
            "binding",
            vec![representative.unit, representative.boolean_binding],
        ),
    ];
    for (id, label, children) in cases {
        let shadow = assemble_shadow(representative.program.node(id).expect("validated node"));
        assert!(validate_shadow(&shadow, &facts));
        assert_eq!(traverse_shadow(&shadow), children);
        assert_eq!(
            transform_shadow(&shadow),
            ShadowTransformPlan::Preserve(children)
        );
        assert_eq!(consume_shadow(&shadow), label);
    }

    let mock = mock_shadow();
    assert!(validate_shadow(&mock, &facts));
    assert_eq!(traverse_shadow(&mock), Vec::<NodeId>::new());
    assert_eq!(
        transform_shadow(&mock),
        ShadowTransformPlan::ReplaceWithMockUnit
    );
    assert_eq!(consume_shadow(&mock), "mock");
}
