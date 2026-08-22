use ash::{
    core::{
        BuildError, CORE_PAYLOAD_DEPTH_LIMIT, CoreBuilder, CoreMatchArm, CorePattern,
        CorePatternKind, Primitive, PureComputation, PureExprKind, PureValue, ValidationReason,
        validate,
    },
    integer::Integer,
    resolved::{ResolvedConstructor, ResolvedNominalType, ResolvedRegistry},
    source::{ByteRange, GeneratedReason, Origin, SourceFile},
    types::{ConstructorId, NominalTypeId, Type, same_type},
};
use std::sync::Arc;

#[test]
fn validates_registry_tuples_constructors_and_structured_matches() {
    let file = source("data core");
    let origin = whole_origin(&file);
    let nominal = NominalTypeId::new(file.id(), 0);
    let empty = ConstructorId::new(nominal, 0);
    let registry = Arc::new(ResolvedRegistry::new(
        vec![ResolvedNominalType {
            id: nominal,
            spelling: "Choice".into(),
            constructors: vec![empty].into_boxed_slice(),
            origin: origin.clone(),
        }],
        vec![ResolvedConstructor {
            id: empty,
            owner: nominal,
            spelling: "Empty".into(),
            payload: None,
            origin: origin.clone(),
        }],
    ));
    let mut builder = CoreBuilder::with_registry(Arc::clone(&registry));
    let constructor = builder
        .constructor(empty, Type::Nominal(nominal), origin.clone())
        .expect("constructor node");
    let arm = CoreMatchArm::new(
        CorePattern::new(
            Type::Nominal(nominal),
            origin.clone(),
            CorePatternKind::Constructor {
                constructor: empty,
                payload: None,
            },
        ),
        constructor,
        origin.clone(),
    );
    let root = builder
        .match_expression(constructor, vec![arm], Type::Nominal(nominal), origin)
        .expect("match node");

    let program = validate(builder.finish(root).expect("root"), &[&file])
        .expect("well-formed data Core should validate");
    assert!(Arc::ptr_eq(program.registry(), &registry));
}

#[test]
fn rejects_malformed_data_registries_and_constructor_annotations() {
    let file = source("malformed data core");
    let origin = whole_origin(&file);
    let nominal = NominalTypeId::new(file.id(), 0);
    let empty_registry = Arc::new(ResolvedRegistry::new(
        vec![ResolvedNominalType {
            id: nominal,
            spelling: "Empty".into(),
            constructors: Box::new([]),
            origin: origin.clone(),
        }],
        Vec::new(),
    ));
    let mut builder = CoreBuilder::with_registry(empty_registry);
    let root = builder.unit(Type::Unit, origin.clone()).expect("unit");
    let error = validate(builder.finish(root).expect("root"), &[&file])
        .expect_err("empty nominal declaration");
    assert_eq!(error.reason(), ValidationReason::Registry);

    let constructor = ConstructorId::new(nominal, 0);
    let registry = Arc::new(ResolvedRegistry::new(
        vec![ResolvedNominalType {
            id: nominal,
            spelling: "One".into(),
            constructors: vec![constructor].into_boxed_slice(),
            origin: origin.clone(),
        }],
        vec![ResolvedConstructor {
            id: constructor,
            owner: nominal,
            spelling: "One".into(),
            payload: None,
            origin: origin.clone(),
        }],
    ));
    let mut builder = CoreBuilder::with_registry(registry);
    let root = builder
        .constructor(constructor, Type::Int, origin)
        .expect("unchecked wrong annotation");
    let error = validate(builder.finish(root).expect("root"), &[&file])
        .expect_err("constructor type disagreement");
    assert_eq!(error.reason(), ValidationReason::NodeType);
}

#[test]
fn rejects_missing_and_redundant_structured_match_arms() {
    let file = source("coverage core");
    let origin = whole_origin(&file);
    let mut missing = CoreBuilder::new();
    let scrutinee = missing
        .boolean(true, Type::Bool, origin.clone())
        .expect("scrutinee");
    let body = missing
        .integer(integer("1"), Type::Int, origin.clone())
        .expect("body");
    let arm = CoreMatchArm::new(
        CorePattern::new(Type::Bool, origin.clone(), CorePatternKind::Boolean(true)),
        body,
        origin.clone(),
    );
    let root = missing
        .match_expression(scrutinee, vec![arm], Type::Int, origin.clone())
        .expect("unchecked match");
    let error =
        validate(missing.finish(root).expect("root"), &[&file]).expect_err("missing false witness");
    assert_eq!(error.reason(), ValidationReason::Coverage);

    let mut redundant = CoreBuilder::new();
    let scrutinee = redundant
        .boolean(true, Type::Bool, origin.clone())
        .expect("scrutinee");
    let first = redundant
        .integer(integer("1"), Type::Int, origin.clone())
        .expect("first body");
    let second = redundant
        .integer(integer("2"), Type::Int, origin.clone())
        .expect("second body");
    let wildcard = || CorePattern::new(Type::Bool, origin.clone(), CorePatternKind::Wildcard);
    let root = redundant
        .match_expression(
            scrutinee,
            vec![
                CoreMatchArm::new(wildcard(), first, origin.clone()),
                CoreMatchArm::new(wildcard(), second, origin.clone()),
            ],
            Type::Int,
            origin,
        )
        .expect("unchecked redundant match");
    let error =
        validate(redundant.finish(root).expect("root"), &[&file]).expect_err("redundant wildcard");
    assert_eq!(error.reason(), ValidationReason::Coverage);
}

#[test]
fn nominal_identity_and_tuple_structure_share_one_type_equality_rule() {
    let first_source = source("first nominal source");
    let second_source = source("second nominal source");
    let first = NominalTypeId::new(first_source.id(), 0);
    let same = NominalTypeId::new(first_source.id(), 0);
    let other_declaration = NominalTypeId::new(first_source.id(), 1);
    let other_source = NominalTypeId::new(second_source.id(), 0);

    assert!(same_type(&Type::Nominal(first), &Type::Nominal(same)));
    assert!(!same_type(
        &Type::Nominal(first),
        &Type::Nominal(other_declaration)
    ));
    assert!(!same_type(
        &Type::Nominal(first),
        &Type::Nominal(other_source)
    ));

    let left = Type::Tuple(vec![Type::Int, Type::Nominal(first)].into_boxed_slice());
    let right = Type::Tuple(vec![Type::Int, Type::Nominal(same)].into_boxed_slice());
    assert!(same_type(&left, &right));
    assert_eq!(left.to_string(), format!("(Int, {})", Type::Nominal(first)));
}

#[test]
fn structural_types_render_with_unambiguous_function_association() {
    assert_eq!(Type::Int.to_string(), "Int");
    assert_eq!(Type::Bool.to_string(), "Bool");
    assert_eq!(Type::Unit.to_string(), "Unit");

    let curried = Type::Function(
        Box::new(Type::Int),
        Box::new(Type::Function(Box::new(Type::Bool), Box::new(Type::Unit))),
    );
    assert_eq!(curried.to_string(), "Int -> Bool -> Unit");

    let higher_order = Type::Function(
        Box::new(Type::Function(Box::new(Type::Int), Box::new(Type::Bool))),
        Box::new(Type::Unit),
    );
    assert_eq!(higher_order.to_string(), "(Int -> Bool) -> Unit");
}

fn source(text: &str) -> SourceFile {
    SourceFile::new("test.ash", text).expect("test source should be representable")
}

fn whole_origin(source: &SourceFile) -> Origin {
    let end = u32::try_from(source.text().len()).expect("test source should fit u32");
    let range = ByteRange::new(0, end).expect("ordered test range");
    Origin::Source(
        source
            .span(range)
            .expect("test range should belong to source"),
    )
}

fn integer(text: &str) -> Integer {
    Integer::parse_decimal(text).expect("test integer should be valid")
}

fn function_type(depth: usize) -> Type {
    let mut ty = Type::Unit;
    for _ in 0..depth {
        ty = Type::Function(Box::new(Type::Unit), Box::new(ty));
    }
    ty
}

fn generated_origin(source: &SourceFile, depth: usize) -> Origin {
    let mut origin = whole_origin(source);
    for _ in 0..depth {
        origin = Origin::Generated {
            cause: Box::new(origin),
            reason: GeneratedReason::TypeChecking,
        };
    }
    origin
}

#[test]
fn validates_a_recursive_function_binding_group() {
    let file = source("recursive core");
    let origin = whole_origin(&file);
    let function_type = Type::Function(Box::new(Type::Unit), Box::new(Type::Int));
    let mut builder = CoreBuilder::new();
    let recursive = builder
        .binder(function_type.clone(), origin.clone())
        .expect("recursive binder");
    let parameter = builder
        .binder(Type::Unit, origin.clone())
        .expect("function parameter");
    let forty_two = builder
        .integer(integer("42"), Type::Int, origin.clone())
        .expect("function body");
    let function = builder
        .function(parameter, forty_two, function_type.clone(), origin.clone())
        .expect("function initializer");
    let occurrence = builder
        .variable(recursive.id(), function_type, origin.clone())
        .expect("recursive occurrence");
    let argument = builder
        .unit(Type::Unit, origin.clone())
        .expect("unit argument");
    let application = builder
        .application(occurrence, argument, Type::Int, origin.clone())
        .expect("recursive call");
    let root = builder
        .recursive_binding(vec![(recursive, function)], application, Type::Int, origin)
        .expect("recursive group");

    let validated = validate(builder.finish(root).expect("root"), &[&file])
        .expect("well-formed recursive Core should validate");

    assert_eq!(validated.root(), root);
    assert_eq!(validated.node(root).expect("group root").ty, Type::Int);
}

#[test]
fn rejects_empty_and_non_function_recursive_groups() {
    let empty_file = source("empty recursive core");
    let empty_origin = whole_origin(&empty_file);
    let mut empty_builder = CoreBuilder::new();
    let empty_body = empty_builder
        .integer(integer("1"), Type::Int, empty_origin.clone())
        .expect("empty body");
    let empty_root = empty_builder
        .recursive_binding(Vec::new(), empty_body, Type::Int, empty_origin)
        .expect("unchecked empty group");
    let empty_error = validate(
        empty_builder.finish(empty_root).expect("empty root"),
        &[&empty_file],
    )
    .expect_err("an empty recursive group is malformed");
    assert_eq!(empty_error.reason(), ValidationReason::RecursiveBinding);

    let value_file = source("value recursive core");
    let value_origin = whole_origin(&value_file);
    let mut value_builder = CoreBuilder::new();
    let binder = value_builder
        .binder(Type::Int, value_origin.clone())
        .expect("value binder");
    let initializer = value_builder
        .integer(integer("1"), Type::Int, value_origin.clone())
        .expect("value initializer");
    let body = value_builder
        .integer(integer("2"), Type::Int, value_origin.clone())
        .expect("value body");
    let root = value_builder
        .recursive_binding(vec![(binder, initializer)], body, Type::Int, value_origin)
        .expect("unchecked value group");
    let value_error = validate(
        value_builder.finish(root).expect("value root"),
        &[&value_file],
    )
    .expect_err("a recursive initializer must be a function node");
    assert_eq!(value_error.reason(), ValidationReason::RecursiveBinding);
}

#[test]
fn rejects_recursive_member_type_disagreement_and_duplicate_binders() {
    let mismatch_file = source("mismatched recursive core");
    let mismatch_origin = whole_origin(&mismatch_file);
    let declared_type = Type::Function(Box::new(Type::Unit), Box::new(Type::Int));
    let actual_type = Type::Function(Box::new(Type::Unit), Box::new(Type::Unit));
    let mut mismatch_builder = CoreBuilder::new();
    let member = mismatch_builder
        .binder(declared_type, mismatch_origin.clone())
        .expect("member binder");
    let parameter = mismatch_builder
        .binder(Type::Unit, mismatch_origin.clone())
        .expect("member parameter");
    let unit = mismatch_builder
        .unit(Type::Unit, mismatch_origin.clone())
        .expect("unit body");
    let function = mismatch_builder
        .function(parameter, unit, actual_type, mismatch_origin.clone())
        .expect("mismatched function");
    let result = mismatch_builder
        .integer(integer("1"), Type::Int, mismatch_origin.clone())
        .expect("group result");
    let mismatch_root = mismatch_builder
        .recursive_binding(vec![(member, function)], result, Type::Int, mismatch_origin)
        .expect("unchecked mismatch group");
    let mismatch_error = validate(
        mismatch_builder
            .finish(mismatch_root)
            .expect("mismatch root"),
        &[&mismatch_file],
    )
    .expect_err("the member type must agree with its function initializer");
    assert_eq!(mismatch_error.reason(), ValidationReason::NodeType);

    let duplicate_file = source("duplicate recursive core");
    let duplicate_origin = whole_origin(&duplicate_file);
    let function_type = Type::Function(Box::new(Type::Unit), Box::new(Type::Int));
    let mut duplicate_builder = CoreBuilder::new();
    let member = duplicate_builder
        .binder(function_type.clone(), duplicate_origin.clone())
        .expect("member binder");
    let parameter = duplicate_builder
        .binder(Type::Unit, duplicate_origin.clone())
        .expect("member parameter");
    let result = duplicate_builder
        .integer(integer("1"), Type::Int, duplicate_origin.clone())
        .expect("member body");
    let function = duplicate_builder
        .function(parameter, result, function_type, duplicate_origin.clone())
        .expect("member function");
    let duplicate_root = duplicate_builder
        .recursive_binding(
            vec![(member.clone(), function), (member, function)],
            result,
            Type::Int,
            duplicate_origin,
        )
        .expect("unchecked duplicate group");
    let duplicate_error = validate(
        duplicate_builder
            .finish(duplicate_root)
            .expect("duplicate root"),
        &[&duplicate_file],
    )
    .expect_err("one binder cannot have two recursive definition sites");
    assert_eq!(duplicate_error.reason(), ValidationReason::Scope);
}

#[test]
fn recursive_group_rejects_foreign_children_and_binder_capabilities() {
    let file = source("foreign recursive core");
    let origin = whole_origin(&file);
    let function_type = Type::Function(Box::new(Type::Unit), Box::new(Type::Int));

    let mut foreign_builder = CoreBuilder::new();
    let foreign_parameter = foreign_builder
        .binder(Type::Unit, origin.clone())
        .expect("foreign parameter");
    let foreign_body = foreign_builder
        .integer(integer("1"), Type::Int, origin.clone())
        .expect("foreign body");
    let foreign_function = foreign_builder
        .function(
            foreign_parameter,
            foreign_body,
            function_type.clone(),
            origin.clone(),
        )
        .expect("foreign function");
    let foreign_binder = foreign_builder
        .binder(function_type.clone(), origin.clone())
        .expect("foreign recursive binder");

    let mut receiver = CoreBuilder::new();
    let local_binder = receiver
        .binder(function_type, origin.clone())
        .expect("local recursive binder");
    let body = receiver
        .integer(integer("2"), Type::Int, origin.clone())
        .expect("local body");
    assert_eq!(
        receiver.recursive_binding(
            vec![(foreign_binder, foreign_function)],
            body,
            Type::Int,
            origin.clone(),
        ),
        Err(BuildError::ForeignBinder)
    );

    let root = receiver
        .recursive_binding(
            vec![(local_binder, foreign_function)],
            body,
            Type::Int,
            origin,
        )
        .expect("unchecked construction accepts child handles");
    let error = validate(receiver.finish(root).expect("local root"), &[&file])
        .expect_err("recursive initializer must belong to the group arena");
    assert_eq!(error.reason(), ValidationReason::NodeBounds);
    assert_eq!(error.node(), Some(root));
}

#[test]
fn recursive_group_rejects_foreign_group_and_binder_provenance() {
    let admitted = source("admitted recursive core");
    let foreign = source("foreign recursive core");
    let admitted_origin = whole_origin(&admitted);
    let foreign_origin = whole_origin(&foreign);
    let function_type = Type::Function(Box::new(Type::Unit), Box::new(Type::Int));

    let mut foreign_group_builder = CoreBuilder::new();
    let member = foreign_group_builder
        .binder(function_type.clone(), admitted_origin.clone())
        .expect("member binder");
    let parameter = foreign_group_builder
        .binder(Type::Unit, admitted_origin.clone())
        .expect("parameter binder");
    let body = foreign_group_builder
        .integer(integer("1"), Type::Int, admitted_origin.clone())
        .expect("function body");
    let function = foreign_group_builder
        .function(
            parameter,
            body,
            function_type.clone(),
            admitted_origin.clone(),
        )
        .expect("function initializer");
    let root = foreign_group_builder
        .recursive_binding(
            vec![(member, function)],
            body,
            Type::Int,
            foreign_origin.clone(),
        )
        .expect("unchecked group");
    let error = validate(
        foreign_group_builder.finish(root).expect("group root"),
        &[&admitted],
    )
    .expect_err("a recursive group origin must be admitted");
    assert_eq!(error.reason(), ValidationReason::Provenance);
    assert_eq!(error.node(), Some(root));

    let mut foreign_binder_builder = CoreBuilder::new();
    let member = foreign_binder_builder
        .binder(function_type.clone(), foreign_origin)
        .expect("unchecked foreign-origin binder");
    let parameter = foreign_binder_builder
        .binder(Type::Unit, admitted_origin.clone())
        .expect("parameter binder");
    let body = foreign_binder_builder
        .integer(integer("1"), Type::Int, admitted_origin.clone())
        .expect("function body");
    let function = foreign_binder_builder
        .function(parameter, body, function_type, admitted_origin.clone())
        .expect("function initializer");
    let root = foreign_binder_builder
        .recursive_binding(vec![(member, function)], body, Type::Int, admitted_origin)
        .expect("unchecked group");
    let error = validate(
        foreign_binder_builder.finish(root).expect("group root"),
        &[&admitted],
    )
    .expect_err("a recursive member binder origin must be admitted");
    assert_eq!(error.reason(), ValidationReason::Provenance);
    assert_eq!(error.node(), Some(root));
}

#[test]
fn recursive_group_rejects_a_free_occurrence_and_an_unreachable_child() {
    let scope_file = source("recursive free occurrence");
    let scope_origin = whole_origin(&scope_file);
    let function_type = Type::Function(Box::new(Type::Unit), Box::new(Type::Int));
    let mut scope_builder = CoreBuilder::new();
    let member = scope_builder
        .binder(function_type.clone(), scope_origin.clone())
        .expect("member binder");
    let parameter = scope_builder
        .binder(Type::Unit, scope_origin.clone())
        .expect("parameter binder");
    let unbound = scope_builder
        .binder(Type::Int, scope_origin.clone())
        .expect("unbound binder capability");
    let free_occurrence = scope_builder
        .variable(unbound.id(), Type::Int, scope_origin.clone())
        .expect("free occurrence");
    let function = scope_builder
        .function(
            parameter,
            free_occurrence,
            function_type.clone(),
            scope_origin.clone(),
        )
        .expect("function initializer");
    let result = scope_builder
        .integer(integer("1"), Type::Int, scope_origin.clone())
        .expect("group result");
    let root = scope_builder
        .recursive_binding(vec![(member, function)], result, Type::Int, scope_origin)
        .expect("unchecked group");
    let error = validate(
        scope_builder.finish(root).expect("group root"),
        &[&scope_file],
    )
    .expect_err("a recursive function cannot acquire an unbound occurrence");
    assert_eq!(error.reason(), ValidationReason::Scope);
    assert_eq!(error.node(), Some(free_occurrence));

    let unreachable_file = source("recursive unreachable child");
    let unreachable_origin = whole_origin(&unreachable_file);
    let mut unreachable_builder = CoreBuilder::new();
    let orphan = unreachable_builder
        .integer(integer("0"), Type::Int, unreachable_origin.clone())
        .expect("orphan node");
    let member = unreachable_builder
        .binder(function_type.clone(), unreachable_origin.clone())
        .expect("member binder");
    let parameter = unreachable_builder
        .binder(Type::Unit, unreachable_origin.clone())
        .expect("parameter binder");
    let body = unreachable_builder
        .integer(integer("1"), Type::Int, unreachable_origin.clone())
        .expect("function body");
    let function = unreachable_builder
        .function(parameter, body, function_type, unreachable_origin.clone())
        .expect("function initializer");
    let root = unreachable_builder
        .recursive_binding(
            vec![(member, function)],
            body,
            Type::Int,
            unreachable_origin,
        )
        .expect("unchecked group");
    let error = validate(
        unreachable_builder.finish(root).expect("group root"),
        &[&unreachable_file],
    )
    .expect_err("all recursive arena nodes must be reachable from the group");
    assert_eq!(error.reason(), ValidationReason::Unreachable);
    assert_eq!(error.node(), Some(orphan));
}

#[test]
fn rejects_cross_builder_binders_without_consuming_receiver_state() {
    let file = source("()");
    let origin = whole_origin(&file);
    let mut owner = CoreBuilder::new();
    let foreign = owner
        .binder(Type::Unit, origin.clone())
        .expect("owner binder");

    let mut function_receiver = CoreBuilder::new();
    let body = function_receiver
        .unit(Type::Unit, origin.clone())
        .expect("receiver body");
    assert_eq!(
        function_receiver.function(
            foreign.clone(),
            body,
            Type::Function(Box::new(Type::Unit), Box::new(Type::Unit)),
            origin.clone(),
        ),
        Err(BuildError::ForeignBinder)
    );
    let first_generated = function_receiver
        .binder(Type::Unit, origin.clone())
        .expect("rejection does not consume a binder identity");
    assert_eq!(first_generated.id().value(), 0);
    let program = validate(
        function_receiver
            .finish(body)
            .expect("only the original body node remains"),
        &[&file],
    )
    .expect("the receiver remains valid");
    assert_eq!(program.node_count(), 1);

    let mut binding_receiver = CoreBuilder::new();
    let unit = binding_receiver
        .unit(Type::Unit, origin.clone())
        .expect("receiver unit");
    assert_eq!(
        binding_receiver.binding(foreign, unit, unit, Type::Unit, origin.clone()),
        Err(BuildError::ForeignBinder)
    );
    let first_generated = binding_receiver
        .binder(Type::Unit, origin)
        .expect("binding rejection does not consume a binder identity");
    assert_eq!(first_generated.id().value(), 0);
    let program = validate(
        binding_receiver
            .finish(unit)
            .expect("only the original unit node remains"),
        &[&file],
    )
    .expect("the binding receiver remains valid");
    assert_eq!(program.node_count(), 1);
}

#[test]
fn foreign_binder_rejection_admits_payloads_before_checking_capability() {
    std::thread::Builder::new()
        .name("foreign-binder-payload-order".to_owned())
        .stack_size(256 * 1024)
        .spawn(|| {
            let file = source("()");
            let origin = whole_origin(&file);
            let mut owner = CoreBuilder::new();
            let foreign = owner
                .binder(Type::Unit, origin.clone())
                .expect("owner binder");
            let mut receiver = CoreBuilder::new();
            let body = receiver
                .unit(Type::Unit, origin.clone())
                .expect("receiver body");

            assert_eq!(
                receiver.function(
                    foreign.clone(),
                    body,
                    function_type(50_000),
                    generated_origin(&file, 50_000),
                ),
                Err(BuildError::TypeDepthExceeded)
            );
            assert_eq!(
                receiver.function(
                    foreign,
                    body,
                    function_type(CORE_PAYLOAD_DEPTH_LIMIT),
                    generated_origin(&file, CORE_PAYLOAD_DEPTH_LIMIT),
                ),
                Err(BuildError::ForeignBinder)
            );
            let first_generated = receiver
                .binder(Type::Unit, origin)
                .expect("rejections leave binder allocation untouched");
            assert_eq!(first_generated.id().value(), 0);
            let program = validate(receiver.finish(body).expect("receiver root"), &[&file])
                .expect("receiver remains valid");
            assert_eq!(program.node_count(), 1);
        })
        .expect("test thread should start")
        .join()
        .expect("foreign payload rejection should remain stack safe");
}

#[test]
fn validates_all_pure_value_and_computation_families() {
    let file = source("core");
    let origin = whole_origin(&file);

    let mut builder = CoreBuilder::new();
    let one = builder
        .integer(integer("1"), Type::Int, origin.clone())
        .expect("small arena");
    let two = builder
        .integer(integer("2"), Type::Int, origin.clone())
        .expect("small arena");
    let sum = builder
        .primitive(Primitive::Add, one, two, Type::Int, origin.clone())
        .expect("small arena");
    let binder = builder
        .binder(Type::Int, origin.clone())
        .expect("small binder set");
    let variable = builder
        .variable(binder.id(), Type::Int, origin.clone())
        .expect("small arena");
    let function = builder
        .function(
            binder.clone(),
            variable,
            Type::Function(Box::new(Type::Int), Box::new(Type::Int)),
            origin.clone(),
        )
        .expect("small arena");
    let application = builder
        .application(function, sum, Type::Int, origin.clone())
        .expect("small arena");
    let result_binder = builder
        .binder(Type::Int, origin.clone())
        .expect("small binder set");
    let result_variable = builder
        .variable(result_binder.id(), Type::Int, origin.clone())
        .expect("small arena");
    let root = builder
        .binding(
            result_binder,
            application,
            result_variable,
            Type::Int,
            origin.clone(),
        )
        .expect("small arena");

    let validated = validate(
        builder.finish(root).expect("root belongs to arena"),
        &[&file],
    )
    .expect("well-typed Core should validate");

    assert_eq!(validated.root(), root);
    assert_eq!(validated.node(root).expect("validated root").ty, Type::Int);
    assert!(matches!(
        validated.node(root).expect("validated root").kind,
        PureExprKind::Computation(PureComputation::Bind(_))
    ));
    assert_eq!(validated.node_count(), 8);
    let function_node = validated.node(function).expect("validated function");
    let PureExprKind::Value(PureValue::Function(function_node)) = &function_node.kind else {
        panic!("expected function payload");
    };
    assert_eq!(function_node.parameter().ty(), &Type::Int);
    assert_eq!(function_node.parameter().origin(), &origin);

    for (ty, build) in [
        (Type::Bool, 0_u8),
        (Type::Unit, 1_u8),
        (Type::Bool, 2_u8),
        (Type::Int, 3_u8),
    ] {
        let mut builder = CoreBuilder::new();
        let root = match build {
            0 => builder.boolean(true, ty.clone(), origin.clone()),
            1 => builder.unit(ty.clone(), origin.clone()),
            2 => {
                let left = builder
                    .integer(integer("1"), Type::Int, origin.clone())
                    .expect("small arena");
                let right = builder
                    .integer(integer("1"), Type::Int, origin.clone())
                    .expect("small arena");
                builder.primitive(Primitive::Equal, left, right, ty.clone(), origin.clone())
            }
            _ => {
                let left = builder
                    .integer(integer("2"), Type::Int, origin.clone())
                    .expect("small arena");
                let right = builder
                    .integer(integer("3"), Type::Int, origin.clone())
                    .expect("small arena");
                builder.primitive(Primitive::Multiply, left, right, ty.clone(), origin.clone())
            }
        }
        .expect("small arena");
        let validated = validate(
            builder.finish(root).expect("root belongs to arena"),
            &[&file],
        )
        .expect("well-typed value should validate");
        let kind = &validated.node(root).expect("validated root").kind;
        assert!(matches!(
            kind,
            PureExprKind::Value(PureValue::Boolean(_))
                | PureExprKind::Value(PureValue::Unit(_))
                | PureExprKind::Computation(PureComputation::Primitive(_))
        ));
    }
}

#[test]
fn binding_initializer_does_not_see_the_binder_it_defines() {
    let file = source("let x = x; x");
    let origin = whole_origin(&file);
    let mut builder = CoreBuilder::new();
    let binder = builder
        .binder(Type::Int, origin.clone())
        .expect("small binder set");
    let initializer = builder
        .variable(binder.id(), Type::Int, origin.clone())
        .expect("small arena");
    let body = builder
        .variable(binder.id(), Type::Int, origin.clone())
        .expect("small arena");
    let root = builder
        .binding(binder, initializer, body, Type::Int, origin)
        .expect("small arena");

    let error = validate(
        builder.finish(root).expect("root belongs to arena"),
        &[&file],
    )
    .expect_err("binding initializer must use the incoming scope");
    assert_eq!(error.reason(), ValidationReason::Scope);
    assert_eq!(error.node(), Some(initializer));
}

#[test]
fn rejects_reusing_one_binder_identity_at_two_definition_sites() {
    let file = source("let x = (); let x = (); ()");
    let origin = whole_origin(&file);
    let mut builder = CoreBuilder::new();
    let binder = builder
        .binder(Type::Unit, origin.clone())
        .expect("small binder set");
    let unit = builder
        .unit(Type::Unit, origin.clone())
        .expect("small arena");
    let inner = builder
        .binding(binder.clone(), unit, unit, Type::Unit, origin.clone())
        .expect("small arena");
    let root = builder
        .binding(binder, unit, inner, Type::Unit, origin)
        .expect("small arena");

    let error = validate(
        builder.finish(root).expect("root belongs to arena"),
        &[&file],
    )
    .expect_err("a binder identity must name one definition site");
    assert_eq!(error.reason(), ValidationReason::Scope);
    assert_eq!(error.node(), Some(root));
}

#[test]
fn shared_variable_reached_only_under_its_binder_is_valid() {
    let file = source("let x = 1; x + x");
    let origin = whole_origin(&file);
    let mut builder = CoreBuilder::new();
    let binder = builder
        .binder(Type::Int, origin.clone())
        .expect("small binder set");
    let initializer = builder
        .integer(integer("1"), Type::Int, origin.clone())
        .expect("small arena");
    let variable = builder
        .variable(binder.id(), Type::Int, origin.clone())
        .expect("small arena");
    let sum = builder
        .primitive(
            Primitive::Add,
            variable,
            variable,
            Type::Int,
            origin.clone(),
        )
        .expect("small arena");
    let root = builder
        .binding(binder, initializer, sum, Type::Int, origin)
        .expect("small arena");

    validate(
        builder.finish(root).expect("root belongs to arena"),
        &[&file],
    )
    .expect("both shared paths introduce the binder");
}

#[test]
fn shared_variable_reached_inside_and_outside_its_binder_is_rejected_at_the_occurrence() {
    let file = source("malformed shared variable");
    let origin = whole_origin(&file);
    let mut builder = CoreBuilder::new();
    let binder = builder
        .binder(Type::Int, origin.clone())
        .expect("small binder set");
    let variable = builder
        .variable(binder.id(), Type::Int, origin.clone())
        .expect("small arena");
    let root = builder
        .binding(binder, variable, variable, Type::Int, origin)
        .expect("small arena");

    let error = validate(
        builder.finish(root).expect("root belongs to arena"),
        &[&file],
    )
    .expect_err("the initializer path does not introduce the binder");
    assert_eq!(error.reason(), ValidationReason::Scope);
    assert_eq!(error.node(), Some(variable));
}

#[test]
fn rejects_i001_variable_outside_its_binder_scope() {
    let file = source("x");
    let origin = whole_origin(&file);
    let mut builder = CoreBuilder::new();
    let binder = builder
        .binder(Type::Int, origin.clone())
        .expect("small binder set");
    let root = builder
        .variable(binder.id(), Type::Int, origin)
        .expect("small arena");

    let error = validate(
        builder.finish(root).expect("root belongs to arena"),
        &[&file],
    )
    .expect_err("free Core variable must be rejected");
    assert_eq!(error.reason(), ValidationReason::Scope);
    assert_eq!(error.node(), Some(root));
}

#[test]
fn rejects_i002_primitive_with_wrong_result_type() {
    let file = source("1 + 2");
    let origin = whole_origin(&file);
    let mut builder = CoreBuilder::new();
    let left = builder
        .integer(integer("1"), Type::Int, origin.clone())
        .expect("small arena");
    let right = builder
        .integer(integer("2"), Type::Int, origin.clone())
        .expect("small arena");
    let root = builder
        .primitive(Primitive::Add, left, right, Type::Bool, origin)
        .expect("small arena");

    let error = validate(
        builder.finish(root).expect("root belongs to arena"),
        &[&file],
    )
    .expect_err("mis-typed primitive must be rejected");
    assert_eq!(error.reason(), ValidationReason::NodeType);
    assert_eq!(error.node(), Some(root));
}

#[test]
fn rejects_i003_application_domain_disagreement() {
    let file = source("f true");
    let origin = whole_origin(&file);
    let mut builder = CoreBuilder::new();
    let parameter = builder
        .binder(Type::Int, origin.clone())
        .expect("small binder set");
    let body = builder
        .variable(parameter.id(), Type::Int, origin.clone())
        .expect("small arena");
    let function = builder
        .function(
            parameter,
            body,
            Type::Function(Box::new(Type::Int), Box::new(Type::Int)),
            origin.clone(),
        )
        .expect("small arena");
    let argument = builder
        .boolean(true, Type::Bool, origin.clone())
        .expect("small arena");
    let root = builder
        .application(function, argument, Type::Int, origin)
        .expect("small arena");

    let error = validate(
        builder.finish(root).expect("root belongs to arena"),
        &[&file],
    )
    .expect_err("application domain mismatch must be rejected");
    assert_eq!(error.reason(), ValidationReason::ApplicationType);
    assert_eq!(error.node(), Some(root));
}

#[test]
fn rejects_i004_origin_outside_the_admitted_source_set() {
    let admitted = source("1");
    let foreign = source("2");
    let mut builder = CoreBuilder::new();
    let root = builder
        .integer(integer("1"), Type::Int, whole_origin(&foreign))
        .expect("small arena");

    let error = validate(
        builder.finish(root).expect("root belongs to arena"),
        &[&admitted],
    )
    .expect_err("foreign provenance must be rejected");
    assert_eq!(error.reason(), ValidationReason::Provenance);
    assert_eq!(error.node(), Some(root));
}

#[test]
fn rejects_related_provenance_that_crosses_source_files() {
    let primary = source("1");
    let related = source("2");
    let origin = Origin::Related {
        primary: Box::new(whole_origin(&primary)),
        related: vec![whole_origin(&related).primary_span()],
    };
    let mut builder = CoreBuilder::new();
    let root = builder
        .integer(integer("1"), Type::Int, origin)
        .expect("small arena");

    let error = validate(
        builder.finish(root).expect("root belongs to arena"),
        &[&primary, &related],
    )
    .expect_err("relations must stay within the primary source file");
    assert_eq!(error.reason(), ValidationReason::Provenance);
}

#[test]
fn rejects_a_root_handle_from_another_arena_even_when_its_index_exists() {
    let file = source("()");
    let origin = whole_origin(&file);
    let mut first = CoreBuilder::new();
    let foreign_root = first
        .unit(Type::Unit, origin.clone())
        .expect("small first arena");
    let mut second = CoreBuilder::new();
    let _local_root = second.unit(Type::Unit, origin).expect("small second arena");

    let error = second
        .finish(foreign_root)
        .expect_err("a root handle must identify its own arena");
    assert_eq!(error, ash::core::BuildError::InvalidNodeId);
}

#[test]
fn validation_rejects_a_foreign_child_even_when_its_index_exists_locally() {
    let file = source("1 + 2");
    let origin = whole_origin(&file);
    let mut first = CoreBuilder::new();
    let foreign_left = first
        .integer(integer("1"), Type::Int, origin.clone())
        .expect("small first arena");

    let mut second = CoreBuilder::new();
    let _local_left = second
        .integer(integer("1"), Type::Int, origin.clone())
        .expect("small second arena");
    let right = second
        .integer(integer("2"), Type::Int, origin.clone())
        .expect("small second arena");
    let root = second
        .primitive(Primitive::Add, foreign_left, right, Type::Int, origin)
        .expect("unchecked construction accepts child handles");
    let error = validate(second.finish(root).expect("local root"), &[&file])
        .expect_err("validation must reject a child from another arena");
    assert_eq!(error.reason(), ValidationReason::NodeBounds);
    assert_eq!(error.node(), Some(root));
}

#[test]
fn validated_lookup_rejects_a_handle_from_another_arena() {
    let file = source("()");
    let origin = whole_origin(&file);
    let mut first = CoreBuilder::new();
    let first_root = first
        .unit(Type::Unit, origin.clone())
        .expect("small first arena");
    let first = validate(first.finish(first_root).expect("local root"), &[&file])
        .expect("valid first arena");

    let mut second = CoreBuilder::new();
    let second_root = second.unit(Type::Unit, origin).expect("small second arena");
    let _second = validate(second.finish(second_root).expect("local root"), &[&file])
        .expect("valid second arena");

    assert!(first.node(second_root).is_none());
}
