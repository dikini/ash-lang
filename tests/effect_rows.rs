use std::collections::HashMap;

use ash::{
    module::ModuleId,
    source::SourceFile,
    types::{
        ComputationType, EffectId, EffectInstance, EffectRow, EffectRowError, EffectRowVariable,
        OperationId, Type, TypeVariableId,
    },
};

fn effect(module: ModuleId, declaration: u32, arguments: impl Into<Box<[Type]>>) -> EffectInstance {
    EffectInstance::new(EffectId::new(module, declaration), arguments.into())
}

#[test]
fn effect_and_operation_identities_are_stable_and_owner_scoped() {
    let source = SourceFile::new("effect-identities.ash", "").expect("fixture should fit");
    let owner = EffectId::new(ModuleId::from(source.id()), 2);
    let first = OperationId::new(owner, 0);
    let second = OperationId::new(owner, 1);

    assert_eq!(first.owner(), owner);
    assert_eq!(first.operation(), 0);
    assert_ne!(first, second);
    assert_eq!(owner.declaration(), 2);
}

#[test]
fn open_row_union_requires_an_existing_lacks_fact() {
    let source =
        SourceFile::new("effect-row.ash", "").expect("the effect-row identity fixture should fit");
    let _pure_computation = ComputationType::pure(Type::Unit);
    let effect = EffectInstance::new(
        EffectId::new(ModuleId::from(source.id()), 3),
        vec![Type::Int].into_boxed_slice(),
    );
    let tail = EffectRowVariable::rigid(TypeVariableId::new(11));
    let open = EffectRow::open(tail, Box::new([]));

    assert_eq!(
        open.union(&EffectRow::singleton(effect.clone())),
        Err(EffectRowError::Ambiguous),
    );

    let open_with_lacks = EffectRow::open(tail, Box::new([effect.clone()]));
    assert_eq!(
        open_with_lacks.union(&EffectRow::singleton(effect.clone())),
        Ok(EffectRow::with_tail(
            Box::new([effect.clone()]),
            tail,
            Box::new([effect]),
        )),
    );
}

#[test]
fn closed_rows_are_unordered_idempotent_exact_instance_sets() {
    let source = SourceFile::new("closed-effect-row.ash", "").expect("fixture should fit");
    let module = ModuleId::from(source.id());
    let state_int = effect(module, 0, vec![Type::Int]);
    let state_bool = effect(module, 0, vec![Type::Bool]);
    let io = effect(module, 1, Vec::<Type>::new());

    assert_eq!(
        EffectRow::closed(vec![io.clone(), state_int.clone(), io.clone()].into_boxed_slice()),
        EffectRow::closed(vec![state_int.clone(), io].into_boxed_slice()),
    );
    assert_ne!(
        EffectRow::singleton(state_int),
        EffectRow::singleton(state_bool),
    );

    let other_source =
        SourceFile::new("other-closed-effect-row.ash", "").expect("fixture should fit");
    let other_module = ModuleId::from(other_source.id());
    let same_render_left = effect(
        module,
        2,
        vec![Type::Variable(TypeVariableId::resolved(module, 0))],
    );
    let same_render_right = effect(
        module,
        2,
        vec![Type::Variable(TypeVariableId::resolved(other_module, 0))],
    );
    assert_eq!(
        EffectRow::closed(
            vec![same_render_left.clone(), same_render_right.clone()].into_boxed_slice(),
        ),
        EffectRow::closed(vec![same_render_right, same_render_left].into_boxed_slice()),
    );
}

#[test]
fn substitution_reaches_exact_arguments_and_preserves_row_lacks() {
    let source = SourceFile::new("substituted-effect-row.ash", "").expect("fixture should fit");
    let module = ModuleId::from(source.id());
    let variable = TypeVariableId::new(4);
    let member = effect(module, 0, vec![Type::Variable(variable)]);
    let tail = EffectRowVariable::rigid(TypeVariableId::new(5));
    let row = EffectRow::with_tail(Box::new([member.clone()]), tail, Box::new([member]));
    let replacements = HashMap::from([(variable, Type::Int)]);

    assert_eq!(
        row.substitute_type_variables(&replacements),
        EffectRow::with_tail(
            Box::new([effect(module, 0, vec![Type::Int])]),
            tail,
            Box::new([effect(module, 0, vec![Type::Int])]),
        ),
    );

    let merging = EffectRow::closed(
        vec![
            effect(module, 1, vec![Type::Variable(variable)]),
            effect(module, 1, vec![Type::Int]),
        ]
        .into_boxed_slice(),
    );
    assert_eq!(
        merging
            .substitute_type_variables(&replacements)
            .known()
            .len(),
        1
    );
}

#[test]
fn exact_removal_does_not_remove_another_instance_or_search_an_unknown_tail() {
    let source = SourceFile::new("remove-effect-row.ash", "").expect("fixture should fit");
    let module = ModuleId::from(source.id());
    let state_int = effect(module, 0, vec![Type::Int]);
    let state_bool = effect(module, 0, vec![Type::Bool]);
    let tail = EffectRowVariable::rigid(TypeVariableId::new(6));
    let row = EffectRow::with_tail(
        Box::new([state_int.clone(), state_bool.clone()]),
        tail,
        Box::new([state_int.clone(), state_bool.clone()]),
    );

    assert_eq!(
        row.remove_exact(&state_int),
        Ok(EffectRow::with_tail(
            Box::new([state_bool.clone()]),
            tail,
            Box::new([state_int, state_bool]),
        )),
    );
    let unknown = effect(module, 1, Vec::<Type>::new());
    assert_eq!(row.remove_exact(&unknown), Err(EffectRowError::Ambiguous));
}

#[test]
fn union_retains_one_shared_tail_and_rejects_unrelated_tails() {
    let source = SourceFile::new("tail-effect-row.ash", "").expect("fixture should fit");
    let module = ModuleId::from(source.id());
    let left = effect(module, 0, Vec::<Type>::new());
    let right = effect(module, 1, Vec::<Type>::new());
    let shared = EffectRowVariable::rigid(TypeVariableId::new(7));
    let shared_lacks = Box::new([left.clone(), right.clone()]);

    assert_eq!(
        EffectRow::with_tail(Box::new([left.clone()]), shared, shared_lacks.clone()).union(
            &EffectRow::with_tail(Box::new([right.clone()]), shared, shared_lacks.clone()),
        ),
        Ok(EffectRow::with_tail(
            Box::new([left.clone(), right.clone()]),
            shared,
            shared_lacks,
        )),
    );
    assert_eq!(
        EffectRow::open(shared, Box::new([])).union(&EffectRow::open(
            EffectRowVariable::rigid(TypeVariableId::new(8)),
            Box::new([]),
        )),
        Err(EffectRowError::Ambiguous),
    );
}

#[test]
fn same_tail_union_combines_operand_local_lacks_before_admitting_members() {
    let source = SourceFile::new("same-tail-union.ash", "").expect("fixture should fit");
    let module = ModuleId::from(source.id());
    let left = effect(module, 0, Vec::<Type>::new());
    let right = effect(module, 1, Vec::<Type>::new());
    let shared = EffectRowVariable::rigid(TypeVariableId::new(9));

    let union = EffectRow::with_tail(Box::new([left.clone()]), shared, Box::new([])).union(
        &EffectRow::with_tail(Box::new([right.clone()]), shared, Box::new([])),
    );

    assert_eq!(
        union,
        Ok(EffectRow::with_tail(
            Box::new([left, right]),
            shared,
            Box::new([]),
        )),
    );
}

#[test]
fn computation_rendering_distinguishes_latent_rows_and_canonicalizes_pure_functions() {
    let source = SourceFile::new("render-effect-row.ash", "").expect("fixture should fit");
    let module = ModuleId::from(source.id());
    let pure = Type::function_computation(Type::Unit, ComputationType::pure(Type::Int));
    let effectful = Type::function_computation(
        Type::Unit,
        ComputationType::new(
            Type::Int,
            EffectRow::singleton(effect(module, 2, Vec::<Type>::new())),
        ),
    );

    assert!(matches!(pure, Type::Function(_, _)));
    assert_eq!(pure.to_string(), "Unit -> Int");
    assert_eq!(
        effectful.to_string(),
        format!("Unit -> Int ! {{<effect:{module}:2>}}"),
    );
}

#[test]
fn dropping_a_row_with_a_deep_exact_argument_is_stack_safe() {
    let source = SourceFile::new("deep-effect-row.ash", "").expect("fixture should fit");
    let module = ModuleId::from(source.id());
    let mut argument = Type::Unit;
    for _ in 0..50_000 {
        argument = Type::Application(Box::new(Type::Unit), Box::new(argument));
    }
    drop(EffectRow::singleton(effect(module, 0, vec![argument])));
}

#[test]
fn nested_owner_row_arguments_preserve_exact_identity_and_lacks() {
    use ash::types::KindedArgument;

    let source = SourceFile::new("nested-owner-rows.ash", "").expect("fixture should fit");
    let module = ModuleId::from(source.id());
    let outer = EffectId::new(module, 0);
    let h = effect(module, 1, Vec::<Type>::new());
    let j = effect(module, 2, Vec::<Type>::new());
    let k = effect(module, 3, Vec::<Type>::new());
    let tail = EffectRowVariable::rigid(TypeVariableId::resolved(module, 0));
    let application = |row| {
        EffectInstance::new_kinded(
            outer,
            Box::new([
                KindedArgument::TypeArg(Type::Int),
                KindedArgument::RowArg(row),
            ]),
        )
    };
    assert_eq!(
        application(EffectRow::closed(Box::new([h.clone(), j.clone()]))),
        application(EffectRow::closed(Box::new([j.clone(), h.clone()]))),
    );
    // Only the tail's lacks set differs; the owner, known members and tail ID agree.
    assert_ne!(
        application(EffectRow::with_tail(
            Box::new([k.clone()]),
            tail,
            Box::new([k.clone(), h.clone()]),
        )),
        application(EffectRow::with_tail(
            Box::new([k.clone()]),
            tail,
            Box::new([k.clone(), j]),
        )),
    );
    // Only the tail identity differs; the known members and lacks set agree.
    assert_ne!(
        application(EffectRow::with_tail(
            Box::new([k.clone()]),
            tail,
            Box::new([k.clone(), h.clone()]),
        )),
        application(EffectRow::with_tail(
            Box::new([k.clone()]),
            EffectRowVariable::rigid(TypeVariableId::resolved(module, 1)),
            Box::new([k, h]),
        )),
    );
}

#[test]
fn type_substitution_descends_into_owner_row_members_and_lacks() {
    use ash::types::KindedArgument;

    let source = SourceFile::new("owner-row-substitution.ash", "").expect("fixture should fit");
    let module = ModuleId::from(source.id());
    let parameter = TypeVariableId::resolved(module, 0);
    let row_parameter = EffectRowVariable::rigid(TypeVariableId::resolved(module, 1));
    let nested = || effect(module, 1, vec![Type::Variable(parameter)]);
    let application = |row| {
        EffectRow::singleton(EffectInstance::new_kinded(
            EffectId::new(module, 0),
            Box::new([KindedArgument::RowArg(row)]),
        ))
    };
    let actual = application(EffectRow::with_tail(
        Box::new([nested()]),
        row_parameter,
        Box::new([nested()]),
    ));
    let expected_member = || effect(module, 1, vec![Type::Bool]);
    let expected = application(EffectRow::with_tail(
        Box::new([expected_member()]),
        row_parameter,
        Box::new([expected_member()]),
    ));
    let replacements = HashMap::from([(parameter, Type::Bool)]);
    assert_eq!(actual.substitute_type_variables(&replacements), expected);
    assert!(matches!(
        actual.known()[0].arguments(),
        [KindedArgument::RowArg(_)]
    ));
}

#[test]
fn mixed_resource_applications_retain_defining_identity_and_slot_order() {
    use ash::types::{KindedArgument, ResourceDefinitionId};

    let source = SourceFile::new("resource-defining-identity.ash", "").expect("fixture should fit");
    let module = ModuleId::from(source.id());
    let resource = ResourceDefinitionId::new(module, 0);
    let make = |definition, row| {
        Type::ResourceApply(
            definition,
            Box::new([
                KindedArgument::TypeArg(Type::Int),
                KindedArgument::RowArg(row),
            ]),
        )
    };
    assert_eq!(
        resource,
        ash::resolved::ResourceDefinitionId::new(module, 0)
    );
    assert_eq!(
        make(resource, EffectRow::empty()),
        make(resource, EffectRow::empty())
    );
    assert_ne!(
        make(resource, EffectRow::empty()),
        make(ResourceDefinitionId::new(module, 1), EffectRow::empty()),
    );
    assert_ne!(
        make(resource, EffectRow::empty()),
        Type::ResourceApply(
            resource,
            Box::new([
                KindedArgument::RowArg(EffectRow::empty()),
                KindedArgument::TypeArg(Type::Int)
            ]),
        ),
    );
}

#[test]
fn alternating_resource_row_arguments_clone_compare_hash_and_drop_on_small_stack() {
    use ash::types::{KindedArgument, ResourceDefinitionId, discard_type_iteratively};
    use std::hash::{DefaultHasher, Hash, Hasher};

    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let source =
                SourceFile::new("alternating-owner-rows.ash", "").expect("fixture should fit");
            let module = ModuleId::from(source.id());
            let definition = ResourceDefinitionId::new(module, 0);
            let owner = EffectId::new(module, 0);
            // This raw graph tests structural ownership; it is not a well-kinded source resource.
            let mut ty = Type::Unit;
            for _ in 0..10_000 {
                ty = Type::ResourceApply(
                    definition,
                    Box::new([KindedArgument::RowArg(EffectRow::singleton(
                        EffectInstance::new_kinded(owner, Box::new([KindedArgument::TypeArg(ty)])),
                    ))]),
                );
            }
            let copy = ty.clone();
            assert_eq!(ty, copy);
            let hash = |value: &Type| {
                let mut state = DefaultHasher::new();
                value.hash(&mut state);
                state.finish()
            };
            assert_eq!(hash(&ty), hash(&copy));
            assert_eq!(format!("{ty:?}"), format!("{copy:?}"));
            discard_type_iteratively(ty);
            discard_type_iteratively(copy);
        })
        .expect("small-stack witness starts")
        .join()
        .expect("alternating owners remain stack safe");
}

mod support;

#[test]
fn local_annotations_require_the_enclosing_rigid_row_exclusion() {
    for lexical_body in [false, true] {
        for established in [false, true] {
            let callback_row = if established { "H | Delta" } else { "| Delta" };
            let accepted_body = if lexical_body {
                "newtype Token = Token(Unit)\nwith Run<Token, {| Delta}> {\nrun (token, callback) = callback ()\n}\n()\n"
            } else {
                "()\n"
            };
            let source = format!(
                "effect H {{\nop : Unit -> Unit\n}}\n\
                 interface Run<Key : Type, Rows : EffectRow> {{\n\
                 run : (Key, Unit -> Unit ! {{| Rows}}) -> Unit ! {{H | Rows}}\n}}\n\
                 caller<Delta : EffectRow> : (Unit -> Unit ! {{{callback_row}}}) -> Unit\n\
                 caller callback = {{\n\
                 let accept : (Unit -> Unit ! {{H | Delta}}) -> Unit = fn(accepted) {{\n()\n}}\n\
                 accept (fn(ignored) {{\n{accepted_body}}})\n}}\n\
                 observe : Unit -> Unit ! {{H}}\nobserve () = perform H.op ()\n\
                 main : Unit -> Int\nmain () = {{\nlet ignored = caller observe\n42\n}}\n"
            );
            let result = support::run_module("rigid-row-annotation.ash", &source);
            if established {
                assert_eq!(result.unwrap().value_display(), "42");
            } else {
                let failure =
                    result.expect_err("a local annotation cannot strengthen arbitrary rigid Delta");
                assert!(failure.is_source_rejection(), "{failure:?}");
                assert_eq!(failure.reason_code(), "effect.row-exclusion");
                assert!(
                    matches!(&failure, ash::driver::PipelineFailure::Typing(_)),
                    "{failure:?}"
                );
            }
        }
    }
}

#[test]
fn a_bare_local_row_preserves_the_enclosing_declarations_exclusions() {
    let source = r"effect H {
op : Unit -> Unit
}
caller<Delta : EffectRow> : (Unit -> Unit ! {| Delta}) -> Unit ! {H | Delta}
caller callback = {
let invoke : Unit -> Unit ! {| Delta} = fn(ignored) {
callback ()
}
()
}
main : Unit -> Int
main () = 42
";
    assert_eq!(
        support::run_module("established-bare-row.ash", source)
            .unwrap()
            .value_display(),
        "42"
    );
}

#[test]
fn row_arguments_have_no_standalone_or_ordinary_nominal_type_denotation() {
    use ash::driver::PipelineFailure;
    for (declaration, standalone_row) in [
        ("pub invalid : {| Rows} -> Unit\ninvalid value = ()\n", true),
        ("pub type Invalid<A : EffectRow> = Invalid(A)\n", false),
        (
            "pub type Box<A> = Box(A)\npub invalid : Box<{}> -> Unit\ninvalid value = ()\n",
            false,
        ),
    ] {
        let source = format!("{declaration}\nmain : Unit -> Unit\nmain () = ()\n");
        let failure = support::run_module("invalid-row-denotation.ash", &source)
            .expect_err("ordinary monotypes cannot absorb row arguments or row-kind arrows");
        if standalone_row {
            assert!(
                matches!(&failure, PipelineFailure::Syntax(_)),
                "a standalone row is outside atomic type syntax: {failure:?}"
            );
        } else {
            assert!(
                matches!(
                    &failure,
                    PipelineFailure::Resolution(_)
                        | PipelineFailure::Kind(_)
                        | PipelineFailure::Typing(_)
                ),
                "ordinary row arguments parse before kind rejection: {failure:?}"
            );
        }
        assert!(failure.is_source_rejection(), "{failure:?}");
    }
}

#[test]
fn nested_owner_rows_obey_the_existing_depth_limit_on_a_small_stack() {
    use ash::{
        driver::PipelineFailure,
        parser::{ResourceFailure, STRUCTURAL_DEPTH_LIMIT},
    };
    std::thread::Builder::new().stack_size(256 * 1024).spawn(|| {
        for depth in [STRUCTURAL_DEPTH_LIMIT + 1, 1_024] {
            let row = format!("{}{{Inner}}{}", "{Outer<".repeat(depth - 1), ">}".repeat(depth - 1));
            let source = format!("effect Inner {{\n    inner : Unit -> Unit\n}}\neffect Outer<Rows : EffectRow> {{\n    outer : Unit -> Unit\n}}\ninterface Witness<Rows : EffectRow> {{\n    witness : (Unit -> Unit ! {{| Rows}}) -> Unit ! {{| Rows}}\n}}\npub deep : Unit -> Unit where Witness<{row}>\ndeep () = ()\nmain : Unit -> Unit\nmain () = ()\n");
            let failure = support::run_module("nested-row-depth.ash", &source)
                .expect_err("complete nested rows consume the existing structural depth budget");
            let PipelineFailure::Syntax(syntax) = &failure else {
                panic!("the parser must reject the depth before source checking: {failure:?}");
            };
            assert_eq!(syntax.resource, Some(ResourceFailure::StructuralDepth { limit: STRUCTURAL_DEPTH_LIMIT }));
            assert!(syntax.lexical.is_empty());
            assert!(syntax.parser.is_empty());
            assert!(!failure.is_source_rejection(), "a replaceable implementation depth limit is not a language rejection");
        }
    }).unwrap().join().unwrap();
}
