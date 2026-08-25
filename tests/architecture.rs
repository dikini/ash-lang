use std::collections::HashMap;

use ash::{
    core::{
        AshPureDialect, CoreBuilder, NodeId, Primitive, PureComputation, PureExprKind, PureValue,
        TypedExpr, ValidatedProgram,
        binding::BindingNode,
        data::{ConstructorNode, MatchNode, TupleNode},
        function::{ApplicationNode, FunctionNode},
        literal::{BooleanNode, IntegerNode, UnitNode},
        primitive::PrimitiveNode,
        recursion::RecursiveBindingNode,
        type_ops::{TypeAbstractionNode, TypeApplicationNode},
        validate,
        variable::VariableNode,
    },
    integer::Integer,
    resolved::BinderId,
    source::{ByteRange, Origin, SourceFile},
    types::Type,
};

const DRIVER_SOURCE: &str = include_str!("../src/driver.rs");
const EVIDENCE_VALIDATION_SOURCE: &str = include_str!("../src/evidence_validation.rs");
const PARSER_EXPORTS: &str = include_str!("../src/parser/mod.rs");
const PARSER_GRAMMAR: &str = include_str!("../src/parser/grammar.rs");
const PARSER_PROJECTION: &str = include_str!("../src/parser/project.rs");
const CORE_AND_EVALUATOR_SOURCES: &[(&str, &str)] = &[
    (
        "src/core/binding.rs",
        include_str!("../src/core/binding.rs"),
    ),
    ("src/core/data.rs", include_str!("../src/core/data.rs")),
    (
        "src/core/dialect.rs",
        include_str!("../src/core/dialect.rs"),
    ),
    (
        "src/core/function.rs",
        include_str!("../src/core/function.rs"),
    ),
    (
        "src/core/literal.rs",
        include_str!("../src/core/literal.rs"),
    ),
    ("src/core/mod.rs", include_str!("../src/core/mod.rs")),
    (
        "src/core/primitive.rs",
        include_str!("../src/core/primitive.rs"),
    ),
    (
        "src/core/recursion.rs",
        include_str!("../src/core/recursion.rs"),
    ),
    (
        "src/core/transform.rs",
        include_str!("../src/core/transform.rs"),
    ),
    (
        "src/core/type_ops.rs",
        include_str!("../src/core/type_ops.rs"),
    ),
    (
        "src/core/validate.rs",
        include_str!("../src/core/validate.rs"),
    ),
    (
        "src/core/variable.rs",
        include_str!("../src/core/variable.rs"),
    ),
    (
        "src/eval/machine.rs",
        include_str!("../src/eval/machine.rs"),
    ),
    ("src/eval/mod.rs", include_str!("../src/eval/mod.rs")),
    ("src/eval/value.rs", include_str!("../src/eval/value.rs")),
];

#[test]
fn current_source_exposes_only_the_modular_source_pipeline() {
    assert!(
        !DRIVER_SOURCE.contains("run_source("),
        "the current driver must not retain the historical file-result pipeline"
    );
    let projection_exports = PARSER_EXPORTS
        .lines()
        .find(|line| line.trim_start().starts_with("pub use project::{"))
        .expect("the parser should publish its modular projection boundary");
    assert!(
        !projection_exports
            .trim_start_matches("pub use project::{")
            .trim_end_matches("};")
            .split(',')
            .any(|export| export.trim() == "project"),
        "the current parser must not export the historical program projection"
    );
    assert!(
        !PARSER_EXPORTS.contains("Program,")
            && !PARSER_PROJECTION.contains("SurfaceProgram")
            && !PARSER_PROJECTION.contains("pub fn project(")
            && !PARSER_PROJECTION.contains("fn project_program("),
        "the current parser must not retain a historical file-result root"
    );
    assert!(
        PARSER_EXPORTS.contains("grammar::module(&mut parser);"),
        "the public parser must enter the declarations-only module grammar"
    );
    assert!(
        PARSER_GRAMMAR.contains("&MODULAR_ASH_DIALECT"),
        "the selected grammar must be Modular Ash"
    );
    assert!(
        !PARSER_GRAMMAR.contains("MINI_ASH_DIALECT"),
        "the current parser must not retain a Mini-Ash grammar selector"
    );
}

#[test]
fn core_and_evaluator_keep_interface_evidence_outside_their_closed_inventories() {
    for (path, source) in CORE_AND_EVALUATOR_SOURCES {
        for identifier in rust_code_identifiers(source) {
            assert!(
                !is_forbidden_interface_identifier(identifier),
                "{path} must not gain the {identifier} interface runtime mechanism"
            );
        }
    }
}

#[test]
fn authenticated_interface_state_ends_at_the_core_synthesis_boundary() {
    let retains_linked_registry =
        validated_program_retains_linked_registry(EVIDENCE_VALIDATION_SOURCE);
    let releases_before_core_validation = interface_state_release_is_ordered(DRIVER_SOURCE);

    assert!(
        !retains_linked_registry && releases_before_core_validation,
        "authenticated interface state must not retain the validator registry and the driver must release the validated interface program after synthesis finish but before Core validation; retains registry: {retains_linked_registry}, releases at boundary: {releases_before_core_validation}"
    );
}

fn validated_program_retains_linked_registry(source: &str) -> bool {
    let identifiers = rust_code_identifiers(source);
    let validated_program = identifiers_between(
        &identifiers,
        &["pub", "struct", "ValidatedInterfaceProgram"],
        &["impl", "ValidatedInterfaceProgram"],
    )
    .expect("the validated interface capability should retain a visible definition");
    validated_program.contains(&"LinkedInterfaceRegistry")
}

fn interface_state_release_is_ordered(source: &str) -> bool {
    let identifiers = rust_code_identifiers(source);
    let driver_pipeline = identifiers_between(
        &identifiers,
        &["fn", "run_path_with_consumers_and_constraint_budget"],
        &["fn", "entry_failure"],
    )
    .expect("the driver should retain one ordered modular pipeline");
    let synthesis_finish =
        identifier_sequence_position(driver_pipeline, &["elaborator", "finish", "typed", "node"])
            .expect("the driver should finish Core synthesis");
    let core_validation = identifier_sequence_position(
        driver_pipeline,
        &[
            "let",
            "validated",
            "validator",
            "unchecked",
            "sources",
            "module_sources",
        ],
    )
    .expect("the driver should independently validate synthesized Core");
    identifier_sequence_position(driver_pipeline, &["drop", "validated_interfaces"])
        .is_some_and(|release| release > synthesis_finish && release < core_validation)
}

#[test]
fn interface_state_boundary_guard_ignores_prose_and_requires_code_sequences() {
    let registry_in_prose = r#"
        pub struct ValidatedInterfaceProgram {
            /// LinkedInterfaceRegistry is prose.
            #[doc = "LinkedInterfaceRegistry is also prose"]
            source: ResolvedModuleProgram,
        }
        impl ValidatedInterfaceProgram {}
    "#;
    assert!(!validated_program_retains_linked_registry(
        registry_in_prose
    ));

    let registry_in_code = r#"
        pub struct ValidatedInterfaceProgram {
            source: ResolvedModuleProgram,
            linked: LinkedInterfaceRegistry,
        }
        impl ValidatedInterfaceProgram {}
    "#;
    assert!(validated_program_retains_linked_registry(registry_in_code));

    let commented_drop = r#"
        fn run_path_with_consumers_and_constraint_budget() {
            let unchecked = elaborator.finish(typed.node)?;
            // drop(validated_interfaces);
            let note = "drop(validated_interfaces);";
            let validated = validator(unchecked, &sources, &module_sources)?;
        }
        fn entry_failure() {}
    "#;
    assert!(!interface_state_release_is_ordered(commented_drop));

    let actual_drop = r#"
        fn run_path_with_consumers_and_constraint_budget() {
            let unchecked = elaborator.finish(typed.node)?;
            drop(validated_interfaces);
            let validated = validator(unchecked, &sources, &module_sources)?;
        }
        fn entry_failure() {}
    "#;
    assert!(interface_state_release_is_ordered(actual_drop));
}

fn is_forbidden_interface_identifier(identifier: &str) -> bool {
    let names_interface_abstraction = has_identifier_component(identifier, "Impl", "impl")
        || has_camel_component(identifier, "Requirement");
    let identifier = identifier.to_ascii_lowercase();
    let carries_interface_vocabulary = ["interface", "evidence", "dictionary", "implementation"]
        .iter()
        .any(|term| identifier.contains(term));
    let combines_runtime_or_method_dispatch = ["runtime", "method"]
        .iter()
        .any(|qualifier| identifier.contains(qualifier))
        && ["registry", "lookup", "dispatch"]
            .iter()
            .any(|mechanism| identifier.contains(mechanism));
    let combines_requirement_mechanism = identifier
        .split('_')
        .any(|component| component == "requirement")
        && [
            "interface",
            "impl",
            "evidence",
            "dictionary",
            "registry",
            "lookup",
            "dispatch",
            "method",
        ]
        .iter()
        .any(|mechanism| identifier.contains(mechanism));

    names_interface_abstraction
        || carries_interface_vocabulary
        || combines_runtime_or_method_dispatch
        || combines_requirement_mechanism
}

fn has_identifier_component(identifier: &str, camel: &str, snake: &str) -> bool {
    let snake_component = identifier != snake
        && identifier
            .split('_')
            .any(|component| component.eq_ignore_ascii_case(snake));

    has_camel_component(identifier, camel) || snake_component
}

fn has_camel_component(identifier: &str, camel: &str) -> bool {
    identifier.match_indices(camel).any(|(start, _)| {
        let end = start + camel.len();
        identifier
            .as_bytes()
            .get(end)
            .is_none_or(|next| !next.is_ascii_lowercase())
    })
}

fn rust_code_identifiers(source: &str) -> Vec<&str> {
    let bytes = source.as_bytes();
    let mut identifiers = Vec::new();
    let mut cursor = 0;

    while cursor < bytes.len() {
        if bytes[cursor..].starts_with(b"//") {
            cursor += 2;
            while cursor < bytes.len() && bytes[cursor] != b'\n' {
                cursor += 1;
            }
            continue;
        }
        if bytes[cursor..].starts_with(b"/*") {
            cursor += 2;
            let mut depth = 1usize;
            while cursor < bytes.len() && depth > 0 {
                if bytes[cursor..].starts_with(b"/*") {
                    depth += 1;
                    cursor += 2;
                } else if bytes[cursor..].starts_with(b"*/") {
                    depth -= 1;
                    cursor += 2;
                } else {
                    cursor += 1;
                }
            }
            continue;
        }
        if let Some(end) = rust_literal_end(bytes, cursor) {
            cursor = end;
            continue;
        }
        if bytes[cursor].is_ascii_alphabetic() || bytes[cursor] == b'_' {
            let start = cursor;
            cursor += 1;
            while cursor < bytes.len()
                && (bytes[cursor].is_ascii_alphanumeric() || bytes[cursor] == b'_')
            {
                cursor += 1;
            }
            identifiers.push(&source[start..cursor]);
            continue;
        }
        cursor += 1;
    }

    identifiers
}

fn identifier_sequence_position(identifiers: &[&str], sequence: &[&str]) -> Option<usize> {
    if sequence.is_empty() {
        return None;
    }
    identifiers
        .windows(sequence.len())
        .position(|window| window == sequence)
}

fn identifiers_between<'a>(
    identifiers: &'a [&'a str],
    start: &[&str],
    end: &[&str],
) -> Option<&'a [&'a str]> {
    let body_start = identifier_sequence_position(identifiers, start)? + start.len();
    let body_end = body_start + identifier_sequence_position(&identifiers[body_start..], end)?;
    Some(&identifiers[body_start..body_end])
}

fn rust_literal_end(source: &[u8], cursor: usize) -> Option<usize> {
    let quote = match source.get(cursor..)? {
        [b'"', ..] => cursor,
        [b'b' | b'c', b'"', ..] => cursor + 1,
        [b'r', rest @ ..] => return rust_raw_literal_end(source, cursor, rest),
        [b'b' | b'c', b'r', rest @ ..] => return rust_raw_literal_end(source, cursor + 1, rest),
        _ => return None,
    };
    let mut end = quote + 1;
    while end < source.len() {
        match source[end] {
            b'\\' => end = end.saturating_add(2),
            b'"' => return Some(end + 1),
            _ => end += 1,
        }
    }
    Some(source.len())
}

fn rust_raw_literal_end(source: &[u8], raw_prefix: usize, rest: &[u8]) -> Option<usize> {
    debug_assert_eq!(source[raw_prefix], b'r');
    let hash_count = rest.iter().take_while(|byte| **byte == b'#').count();
    if rest.get(hash_count) != Some(&b'"') {
        return None;
    }
    let mut end = raw_prefix + hash_count + 2;
    while end < source.len() {
        if source[end] == b'"'
            && source
                .get(end + 1..end + 1 + hash_count)
                .is_some_and(|suffix| suffix.iter().all(|byte| *byte == b'#'))
        {
            return Some(end + 1 + hash_count);
        }
        end += 1;
    }
    Some(source.len())
}

#[test]
fn interface_inventory_guard_reads_code_identifiers_but_not_prose() {
    assert_eq!(
        rust_code_identifiers(
            r###"
            // InterfaceRegistry is prose.
            const NOTE: &str = "EvidenceLookup is prose";
            /* DictionaryDispatch is prose. */
            struct ImplRegistry;
            "###,
        ),
        ["const", "NOTE", "str", "struct", "ImplRegistry"],
    );
    for forbidden in [
        "ImplRegistry",
        "RegistryImpl",
        "impl_lookup",
        "lookup_impl",
        "ImplMethod",
        "RequirementNode",
        "RuntimeRequirement",
        "requirement_registry",
        "RuntimeLookup",
        "dispatch_runtime",
        "registry_interface",
    ] {
        assert!(is_forbidden_interface_identifier(forbidden));
    }
    for allowed in [
        "impl",
        "Implicit",
        "ImplicitFrame",
        "Implementor",
        "requirement",
        "requirements",
        "lookup",
        "dispatch_entry",
        "registry",
    ] {
        assert!(!is_forbidden_interface_identifier(allowed));
    }
}

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
    TypeAbstraction(TypeAbstractionNode),
    TypeApplication(TypeApplicationNode),
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
            PureComputation::TypeAbstraction(node) => {
                ShadowPureComputation::TypeAbstraction(node.clone())
            }
            PureComputation::TypeApplication(node) => {
                ShadowPureComputation::TypeApplication(node.clone())
            }
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
        ShadowPureComputation::TypeAbstraction(node) => {
            matches!(ty, Type::Forall(parameters, body)
                if parameters.as_ref() == node.parameters()
                    && facts.node_type(node.body()) == Some(body.as_ref()))
        }
        ShadowPureComputation::TypeApplication(node) => {
            !node.arguments().is_empty() && facts.node_type(node.function()).is_some()
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
            ShadowPureComputation::TypeAbstraction(node) => vec![node.body()],
            ShadowPureComputation::TypeApplication(node) => vec![node.function()],
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
            ShadowPureComputation::TypeAbstraction(node) => {
                ShadowTransformPlan::Preserve(vec![node.body()])
            }
            ShadowPureComputation::TypeApplication(node) => {
                ShadowTransformPlan::Preserve(vec![node.function()])
            }
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
            ShadowPureComputation::TypeAbstraction(_) => "type abstraction",
            ShadowPureComputation::TypeApplication(_) => "type application",
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
    assert_eq!(AshPureDialect::NAME, "ash.pure");

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
