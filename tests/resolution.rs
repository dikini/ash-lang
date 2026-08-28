use std::{
    fs,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    elaborate::check_module,
    interface::RequirementOwner,
    module::{ModuleRoots, load_module_graph},
    parser::STRUCTURAL_DEPTH_LIMIT,
    resolve::{ResolveReason, resolve_module},
    resolved::{
        Binder, BinderId, ResolvedBinding, ResolvedBlock, ResolvedDefinitionKind, ResolvedExprKind,
        ResolvedLocalDeclaration, ResolvedModule, ResolvedPattern, ResolvedPatternKind,
        ResolvedTermName,
    },
    types::{Kind, Type},
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

fn with_loaded<T>(text: &str, action: impl FnOnce(&ash::module::LoadedModule) -> T) -> T {
    let directory = loop {
        let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("ash-resolution-module-{}-{id}", std::process::id()));
        match fs::create_dir(&path) {
            Ok(()) => break path,
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(error) => panic!("resolution fixture directory should be creatable: {error}"),
        }
    };
    let entry = directory.join("resolution.ash");
    fs::write(&entry, text).expect("resolution fixture should be writable");
    let graph =
        load_module_graph(&entry, &ModuleRoots::empty()).expect("resolution fixture should load");
    let result = action(&graph.modules()[0]);
    let _ = fs::remove_dir_all(directory);
    result
}

fn resolve_valid(text: &str) -> ResolvedModule {
    with_loaded(text, |loaded| {
        resolve_module(loaded, &[]).expect("the fixture should resolve")
    })
}

fn main_body(program: &ResolvedModule) -> &ash::resolved::ResolvedExpr {
    let main = program
        .definitions()
        .iter()
        .find_map(|definition| match &definition.kind {
            ResolvedDefinitionKind::Equational(global)
                if global.interface.name.spelling == "main" =>
            {
                Some(global)
            }
            _ => None,
        })
        .expect("the fixture should declare equational main");
    &main.equations[0].body
}

fn occurrence_binder(occurrence: &ash::resolved::ResolvedOccurrence) -> BinderId {
    occurrence
        .global_binder()
        .expect("the fixture occurrence should resolve to an ordinary binder")
}

#[test]
fn resolves_local_interface_and_method_identities() {
    let program = resolve_valid(
        "interface Equal<A> {\nequal : (A, A) -> Bool\n}\n\nsame : (Int, Int) -> Bool where Equal<Int>\nsame pair = equal pair\n",
    );

    let [interface] = program.interfaces() else {
        panic!("expected one resolved interface");
    };
    assert_eq!(interface.id.module(), program.module());
    assert_eq!(interface.id.declaration(), 0);
    assert_eq!(interface.spelling, "Equal");
    assert_eq!(interface.parameter.spelling, "A");
    let [method] = interface.methods.as_ref() else {
        panic!("expected one resolved interface method");
    };
    assert_eq!(method.id.interface(), interface.id);
    assert_eq!(method.id.declaration(), 0);
    assert_eq!(method.spelling, "equal");

    let ResolvedDefinitionKind::Equational(same) = &program.definitions()[0].kind else {
        panic!("expected the constrained equational global");
    };
    assert_eq!(
        same.interface.name.id.local(),
        0,
        "interface and method identities must not consume the binder namespace"
    );
    let [requirement] = same.interface.requirements.as_ref() else {
        panic!("expected one resolved requirement");
    };
    assert_eq!(
        requirement.id.owner(),
        RequirementOwner::Global(same.interface.name.id)
    );
    assert_eq!(requirement.id.declaration(), 0);
    assert_eq!(requirement.interface.id, interface.id);
    assert_eq!(requirement.argument.ty, Type::Int);

    let ResolvedExprKind::Apply(application) = &same.equations[0].body.kind else {
        panic!("expected a method application");
    };
    let ResolvedExprKind::Occurrence(occurrence) = &application.function.kind else {
        panic!("expected a resolved method occurrence");
    };
    assert_eq!(occurrence.term, ResolvedTermName::Method(method.id));
    assert_eq!(occurrence.evidence.len(), 1);
    assert!(occurrence.evidence[0].selection().is_none());
}

#[test]
fn local_binders_shadow_methods_without_inheriting_method_evidence() {
    let program = resolve_valid(
        "interface Equal<A> {\nequal : (A, A) -> Bool\n}\n\nprobe : Bool -> Bool\nprobe equal = equal\n",
    );
    let ResolvedDefinitionKind::Equational(probe) = &program.definitions()[0].kind else {
        panic!("expected the probe global");
    };
    let ResolvedPatternKind::Binder(parameter) = &probe.equations[0].patterns[0].kind else {
        panic!("expected the shadowing parameter binder");
    };
    let ResolvedExprKind::Occurrence(occurrence) = &probe.equations[0].body.kind else {
        panic!("expected the shadowing local occurrence");
    };

    assert_eq!(occurrence.term, ResolvedTermName::Global(parameter.id));
    assert!(occurrence.evidence.is_empty());
}

#[test]
fn retains_method_local_type_candidates_for_interface_checking() {
    let program = resolve_valid("interface Broken<A> {\nbroken : B -> A\n}\n");
    let [interface] = program.interfaces() else {
        panic!("expected one resolved interface");
    };
    let [method] = interface.methods.as_ref() else {
        panic!("expected one resolved interface method");
    };
    let [candidate] = method.type_parameters.as_ref() else {
        panic!("expected one retained method-local type candidate");
    };

    assert_eq!(candidate.spelling, "B");
    let Type::Function(domain, codomain) = &method.annotation.ty else {
        panic!("expected the method's resolved function type");
    };
    assert_eq!(domain.as_ref(), &Type::Variable(candidate.id));
    assert_eq!(codomain.as_ref(), &Type::Variable(interface.parameter.id));
}

#[test]
fn rejects_interface_and_nominal_wrong_sorts() {
    let cases = [
        (
            "type Named = Named\n\nvalue : Unit -> Bool where Named<Int>\nvalue () = true\n",
            ResolveReason::InterfaceKind,
        ),
        (
            "interface Equal<A> {\nequal : (A, A) -> Bool\n}\n\nvalue : Equal -> Bool\nvalue argument = true\n",
            ResolveReason::TypeKind,
        ),
        (
            "value : A -> Bool where A<A>\nvalue argument = true\n",
            ResolveReason::InterfaceKind,
        ),
        (
            "type Option = Some\n\nvalue : Unit -> Bool where Some<Int>\nvalue () = true\n",
            ResolveReason::InterfaceKind,
        ),
        (
            "value : Unit -> Bool where Missing<Unit>\nvalue () = true\n",
            ResolveReason::UnknownInterface,
        ),
    ];

    for (source, expected) in cases {
        assert_eq!(resolve_error(source).reason, expected, "source:\n{source}");
    }
}

#[test]
fn rejects_local_interface_and_method_namespace_conflicts() {
    let cases = [
        (
            "type Equal = Equal\n\ninterface Equal<A> {\nequal : (A, A) -> Bool\n}\n",
            ResolveReason::DuplicateType,
        ),
        (
            "interface Equal<A> {\nequal : (A, A) -> Bool\n}\n\nequal : Unit -> Bool\nequal () = true\n",
            ResolveReason::DuplicateGlobal,
        ),
    ];

    for (source, expected) in cases {
        assert_eq!(resolve_error(source).reason, expected, "source:\n{source}");
    }
}

#[test]
fn resolves_duplicate_requirements_as_distinct_ordered_occurrences() {
    let program = resolve_valid(
        "interface Equal<A> {\nequal : (A, A) -> Bool\n}\n\nsame : A -> Bool where Equal<A>, Equal<A>, Equal<B>\nsame value = true\n",
    );
    let ResolvedDefinitionKind::Equational(same) = &program.definitions()[0].kind else {
        panic!("expected one constrained equational global");
    };

    assert_eq!(
        same.interface
            .type_parameters
            .iter()
            .map(|parameter| parameter.spelling.as_str())
            .collect::<Vec<_>>(),
        vec!["A", "B"]
    );
    let [first, duplicate, requirement_only] = same.interface.requirements.as_ref() else {
        panic!("expected three ordered resolved requirements");
    };
    assert_eq!(first.interface.id, duplicate.interface.id);
    assert_eq!(first.argument.ty, duplicate.argument.ty);
    assert_ne!(first.id, duplicate.id);
    assert_eq!(first.id.declaration(), 0);
    assert_eq!(duplicate.id.declaration(), 1);
    assert_eq!(requirement_only.id.declaration(), 2);
    assert_eq!(
        first.id.owner(),
        RequirementOwner::Global(same.interface.name.id)
    );
    assert!(matches!(
        requirement_only.argument.ty,
        Type::Variable(id) if id == same.interface.type_parameters[1].id
    ));
}

#[test]
fn allocates_all_hidden_method_binders_before_resolving_bodies() {
    let program = resolve_valid(
        "interface Convert<A> {\nfirst : A -> A\nsecond : A -> A\n}\n\nbefore : Int -> Int\nbefore value = value\n\nimpl Convert<Int> {\nfirst value = second value\nsecond value = first value\n}\n\nafter : Int -> Int\nafter value = value\n",
    );

    let [implementation] = program.implementations() else {
        panic!("expected one resolved implementation");
    };
    let [first, second] = implementation.method_groups.as_ref() else {
        panic!("expected two resolved method groups");
    };
    let ResolvedDefinitionKind::Equational(before) = &program.definitions()[0].kind else {
        panic!("expected the first global");
    };
    let ResolvedDefinitionKind::Equational(after) = &program.definitions()[1].kind else {
        panic!("expected the second global");
    };

    assert_eq!(before.interface.name.id.local(), 0);
    assert_eq!(first.binder.id.local(), 1);
    assert_eq!(second.binder.id.local(), 2);
    assert_eq!(after.interface.name.id.local(), 3);
    let ResolvedPatternKind::Binder(before_parameter) = &before.equations[0].patterns[0].kind
    else {
        panic!("expected the first body parameter binder");
    };
    assert!(before_parameter.id.local() > after.interface.name.id.local());
}

#[test]
fn allocates_impl_and_hidden_method_binders_in_source_order() {
    let program = resolve_valid(
        "interface Convert<A> {\nconvert : A -> A\n}\n\nbefore : Int -> Int\nbefore value = value\n\nimpl Convert<Int> {\nconvert value = value\n}\n\nmiddle : Int -> Int\nmiddle value = value\n\nimpl Convert<Bool> {\nconvert value = value\n}\n\nafter : Int -> Int\nafter value = value\n",
    );

    let [first_implementation, second_implementation] = program.implementations() else {
        panic!("expected two resolved implementations");
    };
    let [first_method] = first_implementation.method_groups.as_ref() else {
        panic!("expected one method group in the first implementation");
    };
    let [second_method] = second_implementation.method_groups.as_ref() else {
        panic!("expected one method group in the second implementation");
    };
    let [before, middle, after] = program.definitions() else {
        panic!("expected three resolved globals");
    };
    let ResolvedDefinitionKind::Equational(before) = &before.kind else {
        panic!("expected the first equational global");
    };
    let ResolvedDefinitionKind::Equational(middle) = &middle.kind else {
        panic!("expected the middle equational global");
    };
    let ResolvedDefinitionKind::Equational(after) = &after.kind else {
        panic!("expected the final equational global");
    };

    assert_eq!(first_implementation.id.module(), program.module());
    assert_eq!(first_implementation.id.declaration(), 0);
    assert_eq!(second_implementation.id.module(), program.module());
    assert_eq!(second_implementation.id.declaration(), 1);
    assert_eq!(before.interface.name.id.local(), 0);
    assert_eq!(first_method.binder.id.local(), 1);
    assert_eq!(middle.interface.name.id.local(), 2);
    assert_eq!(second_method.binder.id.local(), 3);
    assert_eq!(after.interface.name.id.local(), 4);
}

#[test]
fn resolves_impl_prerequisites_and_method_occurrences_to_method_ids() {
    let program = resolve_valid(
        "interface Convert<A> {\nconvert : A -> A\n}\n\nimpl Convert<A> where Convert<A>, Convert<B> {\nconvert value = convert value\n}\n",
    );

    let [interface] = program.interfaces() else {
        panic!("expected one resolved interface");
    };
    let [method] = interface.methods.as_ref() else {
        panic!("expected one resolved interface method");
    };
    let [implementation] = program.implementations() else {
        panic!("expected one resolved implementation");
    };
    let [head_parameter] = implementation.head_parameters.as_ref() else {
        panic!("expected one head parameter");
    };
    let [prerequisite_only_parameter] = implementation.prerequisite_only_parameters.as_ref() else {
        panic!("expected one prerequisite-only parameter");
    };
    let [first, second] = implementation.prerequisites.as_ref() else {
        panic!("expected two ordered prerequisites");
    };

    assert!(matches!(
        implementation.argument.ty,
        Type::Variable(id) if id == head_parameter.id
    ));
    assert_eq!(first.id.owner(), RequirementOwner::Impl(implementation.id));
    assert_eq!(first.id.declaration(), 0);
    assert_eq!(second.id.owner(), RequirementOwner::Impl(implementation.id));
    assert_eq!(second.id.declaration(), 1);
    assert_eq!(first.interface.id, interface.id);
    assert_eq!(second.interface.id, interface.id);
    assert!(matches!(
        first.argument.ty,
        Type::Variable(id) if id == head_parameter.id
    ));
    assert!(matches!(
        second.argument.ty,
        Type::Variable(id) if id == prerequisite_only_parameter.id
    ));

    let [group] = implementation.method_groups.as_ref() else {
        panic!("expected one resolved method group");
    };
    let ResolvedExprKind::Apply(application) = &group.equations[0].body.kind else {
        panic!("expected a method application");
    };
    let ResolvedExprKind::Occurrence(occurrence) = &application.function.kind else {
        panic!("expected a resolved method occurrence");
    };
    assert_eq!(occurrence.term, ResolvedTermName::Method(method.id));
    assert_eq!(occurrence.evidence.len(), 1);
    assert!(occurrence.evidence[0].selection().is_none());
}

#[test]
fn derives_impl_method_identity_from_impl_and_interface_method() {
    let program = resolve_valid(
        "interface Convert<A> {\nconvert : A -> A\n}\n\nimpl Convert<Int> {\nconvert value = value\n}\n",
    );

    let [interface] = program.interfaces() else {
        panic!("expected one resolved interface");
    };
    let [method] = interface.methods.as_ref() else {
        panic!("expected one resolved interface method");
    };
    let [implementation] = program.implementations() else {
        panic!("expected one resolved implementation");
    };
    let [group] = implementation.method_groups.as_ref() else {
        panic!("expected one resolved method group");
    };
    let identity = group
        .identity
        .expect("the method group should have an identity");

    assert_eq!(group.method, Some(method.id));
    assert_eq!(identity.implementation(), implementation.id);
    assert_eq!(identity.method(), method.id);
}

#[test]
fn retains_duplicate_impl_method_groups_with_one_shared_semantic_identity() {
    let program = resolve_valid(
        "interface Convert<A> {\nfirst : A -> A\nsecond : A -> A\n}\n\nimpl Convert<Int> {\nfirst value = value\nsecond value = value\nfirst value = value\n}\n",
    );

    let [implementation] = program.implementations() else {
        panic!("expected one resolved implementation");
    };
    let [first, second, duplicate] = implementation.method_groups.as_ref() else {
        panic!("expected three maximal contiguous method groups");
    };

    assert_eq!(first.method, duplicate.method);
    assert_eq!(first.identity, duplicate.identity);
    assert_ne!(first.binder.id, duplicate.binder.id);
    assert_ne!(first.method, second.method);
    assert_ne!(first.identity, second.identity);
}

#[test]
fn contiguous_impl_equations_form_one_method_group() {
    let program = resolve_valid(
        "interface Convert<A> {\nfirst : A -> A\nsecond : A -> A\n}\n\nimpl Convert<Int> {\nfirst value = value\nfirst other = other\nsecond value = value\n}\n",
    );
    let [implementation] = program.implementations() else {
        panic!("expected one resolved implementation");
    };
    let [first, second] = implementation.method_groups.as_ref() else {
        panic!("expected two maximal contiguous groups");
    };

    assert_eq!(first.equations.len(), 2);
    assert_eq!(second.equations.len(), 1);
    assert_ne!(first.binder.id, second.binder.id);
    assert_eq!(
        first.span.range().start(),
        first.equations[0].span.range().start()
    );
    assert_eq!(
        first.span.range().end(),
        first.equations[1].span.range().end()
    );
}

#[test]
fn leaves_extra_impl_method_group_without_semantic_identity() {
    let program = resolve_valid(
        "interface Convert<A> {\nconvert : A -> A\n}\n\nimpl Convert<Int> {\nconvert value = value\nextra value = value\n}\n",
    );

    let [implementation] = program.implementations() else {
        panic!("expected one resolved implementation");
    };
    let [method, extra] = implementation.method_groups.as_ref() else {
        panic!("expected the method and extra source groups");
    };

    assert!(method.method.is_some());
    assert!(method.identity.is_some());
    assert_eq!(extra.binder.spelling, "extra");
    assert_eq!(extra.method, None);
    assert_eq!(extra.identity, None);
    assert_ne!(method.binder.id, extra.binder.id);
}

#[test]
fn resolved_constraint_occurrences_start_with_owned_empty_evidence_slots() {
    let program = resolve_valid(
        "interface Convert<A> {\nconvert : A -> A\n}\n\nsource : Int -> Int where Convert<Int>, Convert<Int>\nsource value = value\n\ncaller : Int -> Int where Convert<Int>\ncaller value = source (convert value)\n",
    );
    let ResolvedDefinitionKind::Equational(source) = &program.definitions()[0].kind else {
        panic!("expected the constrained source global");
    };
    let ResolvedDefinitionKind::Equational(caller) = &program.definitions()[1].kind else {
        panic!("expected the constrained caller global");
    };
    let ResolvedExprKind::Apply(source_application) = &caller.equations[0].body.kind else {
        panic!("expected the constrained global application");
    };
    let ResolvedExprKind::Occurrence(source_occurrence) = &source_application.function.kind else {
        panic!("expected the constrained global occurrence");
    };
    let ResolvedExprKind::Apply(method_application) = &source_application.argument.kind else {
        panic!("expected the method application argument");
    };
    let ResolvedExprKind::Occurrence(method_occurrence) = &method_application.function.kind else {
        panic!("expected the method occurrence");
    };

    assert_eq!(
        source_occurrence.term,
        ResolvedTermName::Global(source.interface.name.id)
    );
    assert_eq!(source_occurrence.evidence.len(), 2);
    assert!(
        source_occurrence
            .evidence
            .iter()
            .all(|slot| slot.selection().is_none())
    );
    assert!(matches!(
        method_occurrence.term,
        ResolvedTermName::Method(_)
    ));
    assert_eq!(method_occurrence.evidence.len(), 1);
    assert!(method_occurrence.evidence[0].selection().is_none());
}

#[test]
fn data_and_pattern_resolution_allocates_file_wide_identities_and_pattern_binders() {
    let program = resolve_valid(
        "type First =\n    First(Second)\n\ntype Second =\n    Empty\n    | More(First)\n\nunwrap : First -> Second\nunwrap (First value) = value\n\nmain : Unit -> Second\nmain () = match First(Empty) {\n    First(value) => value\n}\n",
    );

    assert_eq!(program.registry().nominals().len(), 2);
    let first = &program.registry().nominals()[0];
    let second = &program.registry().nominals()[1];
    assert_ne!(first.id, second.id);
    let first_constructor = &program.registry().constructors()[0];
    assert_eq!(first_constructor.owner, first.id);
    assert_eq!(first_constructor.payload, Some(Type::Nominal(second.id)));
    let ResolvedDefinitionKind::Equational(definition) = &program.definitions()[0].kind else {
        panic!("expected equation group");
    };
    let pattern = &definition.equations[0].patterns[0];
    let ash::resolved::ResolvedPatternKind::Constructor { payload, .. } = &pattern.kind else {
        panic!("expected resolved constructor pattern");
    };
    let ash::resolved::ResolvedPatternKind::Binder(pattern_binder) =
        &payload.as_ref().expect("payload pattern").kind
    else {
        panic!("expected payload binder");
    };
    let ash::resolved::ResolvedExprKind::Occurrence(body_use) = &definition.equations[0].body.kind
    else {
        panic!("expected resolved body occurrence");
    };
    assert_eq!(occurrence_binder(body_use), pattern_binder.id);
}

#[test]
fn implicit_global_parameters_preserve_free_name_order_and_exclude_nominals() {
    let program = resolve_valid(
        "type Option<A> =\nNone\n| Some(A)\n\nfn select(left : Option<B>, right : C) -> B {\n()\n}\n\nmain : Unit -> Unit\nmain value = value\n",
    );
    let ResolvedDefinitionKind::InlineOperational(definition) = &program.definitions()[0].kind
    else {
        panic!("expected operational definition");
    };

    assert_eq!(
        definition
            .header
            .type_parameters
            .iter()
            .map(|parameter| parameter.spelling.as_str())
            .collect::<Vec<_>>(),
        ["B", "C"]
    );
}

#[test]
fn explicit_global_syntax_preserves_predecessor_resolution_until_kind_checking() {
    let program = resolve_valid(
        "identity<A : Type> : A -> A\nidentity value = value\n\nfn operational<A : Type>(value : A) -> A {\nvalue\n}\n",
    );

    let ResolvedDefinitionKind::Equational(identity) = &program.definitions()[0].kind else {
        panic!("expected an equational definition");
    };
    assert_eq!(
        identity
            .interface
            .type_parameters
            .iter()
            .map(|parameter| parameter.spelling.as_str())
            .collect::<Vec<_>>(),
        ["A"]
    );

    let ResolvedDefinitionKind::InlineOperational(operational) = &program.definitions()[1].kind
    else {
        panic!("expected an operational definition");
    };
    assert_eq!(
        operational
            .header
            .type_parameters
            .iter()
            .map(|parameter| parameter.spelling.as_str())
            .collect::<Vec<_>>(),
        ["A"]
    );
}

#[test]
fn explicit_kind_binders_are_complete_and_ordered() {
    let program = resolve_valid(
        "type Pair<Left, Right> = Pair(Left, Right)\n\ninterface Witness<Value> {\nwitness : Value -> Bool\n}\n\nordered<B : Type, A : Type> : A -> B -> A\nordered left right = left\n\nrequirement_only<B : Type, A : Type> : A -> A where Witness<B>\nrequirement_only value = value\n\nfn operational<D : Type, C : Type>(left : C, right : D) -> C {\nleft\n}\n\nimpl<B : Type, A : Type> Witness<Pair<A, B>> {\nwitness value = true\n}\n",
    );

    let ResolvedDefinitionKind::Equational(ordered) = &program.definitions()[0].kind else {
        panic!("expected the ordered equational global");
    };
    assert_eq!(
        ordered
            .interface
            .type_parameters
            .iter()
            .map(|parameter| parameter.spelling.as_str())
            .collect::<Vec<_>>(),
        ["B", "A"],
    );
    assert!(
        ordered
            .interface
            .type_parameters
            .iter()
            .all(|parameter| parameter.kind == Kind::Type),
    );

    let ResolvedDefinitionKind::Equational(requirement_only) = &program.definitions()[1].kind
    else {
        panic!("expected the requirement-only equational global");
    };
    assert_eq!(
        requirement_only
            .interface
            .type_parameters
            .iter()
            .map(|parameter| parameter.spelling.as_str())
            .collect::<Vec<_>>(),
        ["B", "A"],
    );

    let ResolvedDefinitionKind::InlineOperational(operational) = &program.definitions()[2].kind
    else {
        panic!("expected the operational global");
    };
    assert_eq!(
        operational
            .header
            .type_parameters
            .iter()
            .map(|parameter| parameter.spelling.as_str())
            .collect::<Vec<_>>(),
        ["D", "C"],
    );

    let [implementation] = program.implementations() else {
        panic!("expected one implementation");
    };
    assert_eq!(
        implementation
            .head_parameters
            .iter()
            .map(|parameter| parameter.spelling.as_str())
            .collect::<Vec<_>>(),
        ["B", "A"],
    );
    assert!(
        implementation
            .head_parameters
            .iter()
            .all(|parameter| parameter.kind == Kind::Type),
    );
}

#[test]
fn explicit_global_binders_reject_duplicates_unused_names_and_omissions() {
    let duplicate_source = "same<A : Type, A : Type> : A -> A\nsame value = value\n";
    let duplicate = resolve_error(duplicate_source);
    assert_eq!(duplicate.reason, ResolveReason::DuplicateTypeParameter);
    assert_eq!(duplicate.primary.span().range().start(), 15);
    assert_eq!(duplicate.primary.span().range().end(), 16);
    assert_eq!(duplicate.related.len(), 1);
    assert_eq!(duplicate.related[0].span().range().start(), 5);
    assert_eq!(duplicate.related[0].span().range().end(), 6);

    let unused_source = "same<A : Type, B : Type> : A -> A\nsame value = value\n";
    let unused = resolve_error(unused_source);
    assert_eq!(unused.reason.to_string(), "resolve.unused-type-parameter",);
    assert_eq!(unused.primary.span().range().start(), 15);
    assert_eq!(unused.primary.span().range().end(), 16);
    assert_eq!(unused.found.as_deref(), Some("B"));

    let omitted_source = "same<A : Type> : A -> B -> A\nsame left right = left\n";
    let omitted = resolve_error(omitted_source);
    assert_eq!(omitted.reason, ResolveReason::UnknownType);
    assert_eq!(omitted.primary.span().range().start(), 22);
    assert_eq!(omitted.primary.span().range().end(), 23);
    assert_eq!(omitted.found.as_deref(), Some("B"));
}

#[test]
fn explicit_global_unlisted_requirement_variable_is_unknown_at_its_occurrence() {
    let source = "type Pair<Left, Right> = Pair(Left, Right)\n\ninterface Equal<A> {\nequal : (A, A) -> Bool\n}\n\nsame<A : Type> : A -> Bool where Equal<Pair<A, B>>\nsame value = true\n";
    let error = resolve_error(source);

    assert_eq!(error.reason, ResolveReason::UnknownType);
    assert_eq!(error.found.as_deref(), Some("B"));
    let occurrence = u32::try_from(
        source
            .find("B>>")
            .expect("the omitted occurrence is present"),
    )
    .expect("the test source fits in a span");
    assert_eq!(error.primary.span().range().start(), occurrence);
    assert_eq!(error.primary.span().range().end(), occurrence + 1);
}

#[test]
fn explicit_implementation_binders_reject_duplicates_unused_names_and_omissions() {
    let prelude = "type Pair<Left, Right> = Pair(Left, Right)\n\ninterface Witness<Value> {\nwitness : Value -> Bool\n}\n\n";

    let duplicate_source = format!(
        "{prelude}impl<A : Type, A : Type> Witness<Pair<A, A>> {{\nwitness value = true\n}}\n",
    );
    let duplicate = resolve_error(&duplicate_source);
    assert_eq!(duplicate.reason, ResolveReason::DuplicateTypeParameter);
    assert_eq!(duplicate.related.len(), 1);

    let unused_source = format!(
        "{prelude}impl<A : Type, B : Type> Witness<Pair<A, A>> {{\nwitness value = true\n}}\n",
    );
    let unused = resolve_error(&unused_source);
    assert_eq!(unused.reason.to_string(), "resolve.unused-type-parameter",);
    assert_eq!(unused.found.as_deref(), Some("B"));

    let omitted_source =
        format!("{prelude}impl<A : Type> Witness<Pair<A, B>> {{\nwitness value = true\n}}\n",);
    let omitted = resolve_error(&omitted_source);
    assert_eq!(omitted.reason, ResolveReason::UnknownType);
    assert_eq!(omitted.found.as_deref(), Some("B"));
}

#[test]
fn declaration_binder_defaults_and_legacy_order_are_fixed_at_type() {
    let program = resolve_valid(
        "type Phantom<F : Type -> Type, A> = Phantom(A)\n\ninterface Witness<Value> {\nwitness : Value -> Bool\n}\n\nlegacy : B -> A -> B\nlegacy left right = left\n\nimpl Witness<(B, A)> {\nwitness value = true\n}\n",
    );

    let phantom = program
        .registry()
        .nominal_parameters(program.registry().nominals()[0].id)
        .expect("the phantom nominal should retain its parameters");
    assert_eq!(phantom.len(), 2);
    assert_eq!(
        phantom[0].kind,
        Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
    );
    assert_eq!(phantom[1].kind, Kind::Type);

    let [interface] = program.interfaces() else {
        panic!("expected one interface");
    };
    assert_eq!(interface.parameter.kind, Kind::Type);

    let ResolvedDefinitionKind::Equational(legacy) = &program.definitions()[0].kind else {
        panic!("expected the legacy equational global");
    };
    assert_eq!(
        legacy
            .interface
            .type_parameters
            .iter()
            .map(|parameter| (parameter.spelling.as_str(), &parameter.kind))
            .collect::<Vec<_>>(),
        [("B", &Kind::Type), ("A", &Kind::Type)],
    );

    let [implementation] = program.implementations() else {
        panic!("expected one implementation");
    };
    assert_eq!(
        implementation
            .head_parameters
            .iter()
            .map(|parameter| (parameter.spelling.as_str(), &parameter.kind))
            .collect::<Vec<_>>(),
        [("B", &Kind::Type), ("A", &Kind::Type)],
    );
}

#[test]
fn declaration_type_binder_identities_follow_source_order_across_interface_and_nominal_families() {
    let program = resolve_valid(
        "interface Project<A> {\nproject : B -> A\n}\n\ntype Pair<C, D> = Pair(C, D)\n\nidentity<E> : E -> E\nidentity value = value\n",
    );

    let [interface] = program.interfaces() else {
        panic!("expected one interface");
    };
    let [method_parameter] = interface.methods[0].type_parameters.as_ref() else {
        panic!("expected one method-local type candidate");
    };
    let nominal = program
        .registry()
        .nominal_parameters(program.registry().nominals()[0].id)
        .expect("the nominal should retain its parameters");
    let ResolvedDefinitionKind::Equational(identity) = &program.definitions()[0].kind else {
        panic!("expected the equational global");
    };

    assert_eq!(interface.parameter.id.local(), 0);
    assert_eq!(method_parameter.id.local(), 1);
    assert_eq!(nominal[0].id.local(), 2);
    assert_eq!(nominal[1].id.local(), 3);
    assert_eq!(identity.interface.type_parameters[0].id.local(), 4);
}

#[test]
fn declaration_type_binder_identities_follow_source_order_across_impl_and_global_families() {
    let program = resolve_valid(
        "interface Witness<Value> {\nwitness : Value -> Bool\n}\n\nimpl<A> Witness<A> where Witness<B> {\nwitness value = true\n}\n\nlater<C, D> : C -> D -> C\nlater first second = first\n",
    );

    let [interface] = program.interfaces() else {
        panic!("expected one interface");
    };
    let [implementation] = program.implementations() else {
        panic!("expected one implementation");
    };
    let [head_parameter] = implementation.head_parameters.as_ref() else {
        panic!("expected one implementation head parameter");
    };
    let [prerequisite_parameter] = implementation.prerequisite_only_parameters.as_ref() else {
        panic!("expected one prerequisite-only parameter");
    };
    let ResolvedDefinitionKind::Equational(later) = &program.definitions()[0].kind else {
        panic!("expected the later equational global");
    };

    assert_eq!(interface.parameter.id.local(), 0);
    assert_eq!(head_parameter.id.local(), 1);
    assert_eq!(prerequisite_parameter.id.local(), 2);
    assert_eq!(later.interface.type_parameters[0].id.local(), 3);
    assert_eq!(later.interface.type_parameters[1].id.local(), 4);
}

#[test]
fn omitted_kinds_and_implicit_lists_preserve_exact_type_kinds_and_order() {
    let program = resolve_valid(concat!(
        "type ExplicitPair<Left, Right> = ExplicitPair(Left, Right)\n",
        "type ImplicitPair<First, Second> = ImplicitPair(First, Second)\n\n",
        "interface Witness<Subject> {\n",
        "witness : Subject -> Bool\n",
        "}\n\n",
        "ordered<B, A> : A -> B -> A\n",
        "ordered left right = left\n\n",
        "fn operational<D, C>(left : C, right : D) -> C {\n",
        "left\n",
        "}\n\n",
        "impl<F, E> Witness<ExplicitPair<E, F>> {\n",
        "witness value = true\n",
        "}\n\n",
        "legacy : Y -> X -> Y\n",
        "legacy left right = left\n\n",
        "fn legacy_operational(left : W, right : V) -> W {\n",
        "left\n",
        "}\n\n",
        "impl Witness<ImplicitPair<S, R>> {\n",
        "witness value = true\n",
        "}\n",
    ));

    let nominal_parameters = program
        .registry()
        .nominals()
        .iter()
        .map(|nominal| {
            program
                .registry()
                .nominal_parameters(nominal.id)
                .expect("each nominal should retain its omitted-kind binders")
                .iter()
                .map(|parameter| (parameter.spelling.as_str(), &parameter.kind))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    assert_eq!(
        nominal_parameters,
        [
            vec![("Left", &Kind::Type), ("Right", &Kind::Type)],
            vec![("First", &Kind::Type), ("Second", &Kind::Type)],
        ]
    );

    let [interface] = program.interfaces() else {
        panic!("expected one interface");
    };
    assert_eq!(
        (&*interface.parameter.spelling, &interface.parameter.kind),
        ("Subject", &Kind::Type)
    );

    let [ordered, operational, legacy, legacy_operational] = program.definitions() else {
        panic!("expected four globals");
    };
    let ResolvedDefinitionKind::Equational(ordered) = &ordered.kind else {
        panic!("expected the explicit equational global");
    };
    let ResolvedDefinitionKind::InlineOperational(operational) = &operational.kind else {
        panic!("expected the explicit inline global");
    };
    let ResolvedDefinitionKind::Equational(legacy) = &legacy.kind else {
        panic!("expected the implicit equational global");
    };
    let ResolvedDefinitionKind::InlineOperational(legacy_operational) = &legacy_operational.kind
    else {
        panic!("expected the implicit inline global");
    };
    assert_eq!(
        ordered
            .interface
            .type_parameters
            .iter()
            .map(|parameter| (parameter.spelling.as_str(), &parameter.kind))
            .collect::<Vec<_>>(),
        [("B", &Kind::Type), ("A", &Kind::Type)]
    );
    assert_eq!(
        operational
            .header
            .type_parameters
            .iter()
            .map(|parameter| (parameter.spelling.as_str(), &parameter.kind))
            .collect::<Vec<_>>(),
        [("D", &Kind::Type), ("C", &Kind::Type)]
    );
    assert_eq!(
        legacy
            .interface
            .type_parameters
            .iter()
            .map(|parameter| (parameter.spelling.as_str(), &parameter.kind))
            .collect::<Vec<_>>(),
        [("Y", &Kind::Type), ("X", &Kind::Type)]
    );
    assert_eq!(
        legacy_operational
            .header
            .type_parameters
            .iter()
            .map(|parameter| (parameter.spelling.as_str(), &parameter.kind))
            .collect::<Vec<_>>(),
        [("W", &Kind::Type), ("V", &Kind::Type)]
    );

    let [explicit, implicit] = program.implementations() else {
        panic!("expected explicit and implicit implementations");
    };
    assert_eq!(
        explicit
            .head_parameters
            .iter()
            .map(|parameter| (parameter.spelling.as_str(), &parameter.kind))
            .collect::<Vec<_>>(),
        [("F", &Kind::Type), ("E", &Kind::Type)]
    );
    assert_eq!(
        implicit
            .head_parameters
            .iter()
            .map(|parameter| (parameter.spelling.as_str(), &parameter.kind))
            .collect::<Vec<_>>(),
        [("S", &Kind::Type), ("R", &Kind::Type)]
    );

    check_module(program).expect("all predecessor-compatible binder forms should check");
}

#[test]
fn non_type_explicit_kinds_are_retained_on_every_declaration_binder_owner() {
    let program = resolve_valid(
        "type Holder<F : Type -> Type> = Holder\n\ninterface Transform<F : Type -> Type> {\ntransform : Holder<F> -> Bool\n}\n\ninterface Observe<A> {\nobserve : A -> Bool\n}\n\nuses<F : Type -> Type> : Holder<F> -> Bool\nuses value = true\n\nimpl<F : Type -> Type> Observe<Holder<F>> {\nobserve value = true\n}\n",
    );
    let expected = Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));

    let [nominal_parameter] = program
        .registry()
        .nominal_parameters(program.registry().nominals()[0].id)
        .expect("the nominal should retain its binder")
    else {
        panic!("expected one nominal binder");
    };
    assert_eq!(nominal_parameter.kind, expected);

    assert_eq!(program.interfaces()[0].parameter.kind, expected);

    let ResolvedDefinitionKind::Equational(global) = &program.definitions()[0].kind else {
        panic!("expected the kinded global");
    };
    let [global_parameter] = global.interface.type_parameters.as_ref() else {
        panic!("expected one global binder");
    };
    assert_eq!(global_parameter.kind, expected);

    let [implementation] = program.implementations() else {
        panic!("expected one implementation");
    };
    let [implementation_parameter] = implementation.head_parameters.as_ref() else {
        panic!("expected one implementation binder");
    };
    assert_eq!(implementation_parameter.kind, expected);
}

#[test]
fn data_namespaces_report_stable_resolution_reasons() {
    let cases = [
        (
            "type T = A\n\ntype T = B\n\nmain : Unit -> T\nmain () = A\n",
            ResolveReason::DuplicateType,
        ),
        (
            "type T = Same\n\ntype U = Same\n\nmain : Unit -> T\nmain () = Same\n",
            ResolveReason::DuplicateConstructor,
        ),
        (
            "type T = Make(Missing)\n\nmain : Unit -> T\nmain () = Make\n",
            ResolveReason::UnknownType,
        ),
        (
            "main : Unit -> Unit\nmain () = Missing\n",
            ResolveReason::UnknownConstructor,
        ),
        (
            "type Pair = Pair(Int, Int)\n\nmain : Unit -> Int\nmain () = match Pair(1, 2) {\n    Pair(value, value) => value\n}\n",
            ResolveReason::DuplicatePatternBinder,
        ),
    ];

    for (source, reason) in cases {
        assert_eq!(resolve_error(source).reason, reason, "source:\n{source}");
    }
}

#[test]
fn match_arm_pattern_scope_does_not_leak_to_later_arms() {
    let error = resolve_error(
        "main : Unit -> Bool\nmain () = match true {\n    value => value\n    _ => value\n}\n",
    );

    assert_eq!(error.reason, ResolveReason::UnknownName);
}

fn resolve_error(text: &str) -> ash::resolve::ResolveError {
    with_loaded(text, |loaded| {
        match resolve_module(loaded, &[]).expect_err("the fixture should fail resolution") {
            ash::resolve::ResolveModuleError::Resolution(error) => error,
            ash::resolve::ResolveModuleError::Kind(error) => {
                panic!("resolution fixture unexpectedly reached kind checking: {error:?}")
            }
        }
    })
}

fn binding(block: &ResolvedBlock, index: usize) -> &ResolvedBinding {
    let ResolvedLocalDeclaration::Binding(binding) = &block.declarations[index] else {
        panic!("expected ordinary binding")
    };
    binding
}

fn pattern_binder(pattern: &ResolvedPattern) -> &Binder {
    let ResolvedPatternKind::Binder(binder) = &pattern.kind else {
        panic!("expected binder pattern")
    };
    binder
}

fn binding_binder(binding: &ResolvedBinding) -> &Binder {
    pattern_binder(&binding.pattern)
}

#[test]
fn completed_global_is_visible_to_the_program_result() {
    let program = resolve_valid(
        "identity : Int -> Int\nidentity value = value\n\nmain : Unit -> Int\nmain () = identity 1\n",
    );

    let ResolvedDefinitionKind::Equational(definition) = &program.definitions()[0].kind else {
        panic!("expected an equational definition");
    };
    let ResolvedExprKind::Apply(application) = &main_body(&program).kind else {
        panic!("expected an application");
    };
    let ResolvedExprKind::Occurrence(global_use) = &application.function.kind else {
        panic!("expected a resolved global occurrence");
    };

    assert_eq!(occurrence_binder(global_use), definition.interface.name.id);
    assert_eq!(
        definition.equations[0].name.binder,
        definition.interface.name.id
    );
    assert_eq!(global_use.spelling, "identity");
}

#[test]
fn equation_name_mismatch_relates_the_equation_head_to_the_interface() {
    let error = resolve_error(
        "first : Int -> Int\nsecond value = value\n\nmain : Unit -> Int\nmain () = 0\n",
    );

    assert_eq!(error.reason, ResolveReason::EquationNameMismatch);
    assert_eq!(error.primary.span().range().start(), 19);
    assert_eq!(error.primary.span().range().end(), 25);
    assert_eq!(error.related.len(), 1);
    assert_eq!(error.related[0].span().range().start(), 0);
    assert_eq!(error.related[0].span().range().end(), 5);
    assert_eq!(error.expected.as_deref(), Some("first"));
    assert_eq!(error.found.as_deref(), Some("second"));
}

#[test]
fn duplicate_global_relates_the_second_name_to_the_first_name_and_definition() {
    let error = resolve_error(
        "same : Int -> Int\nsame value = value\n\nsame : Int -> Int\nsame other = other\n\nmain : Unit -> Int\nmain () = 0\n",
    );

    assert_eq!(error.reason, ResolveReason::DuplicateGlobal);
    assert_eq!(error.primary.span().range().start(), 38);
    assert_eq!(error.primary.span().range().end(), 42);
    assert_eq!(error.related.len(), 2);
    assert_eq!(error.related[0].span().range().start(), 0);
    assert_eq!(error.related[0].span().range().end(), 4);
    assert_eq!(error.related[1].span().range().start(), 0);
    assert_eq!(error.related[1].span().range().end(), 36);
}

#[test]
fn inline_operational_global_resolves_parameter_and_later_global_use() {
    let program = resolve_valid(
        "fn identity(value : Int) -> Int {\n    value\n}\n\nmain : Unit -> Int\nmain () = identity 1\n",
    );

    let ResolvedDefinitionKind::InlineOperational(definition) = &program.definitions()[0].kind
    else {
        panic!("expected an inline operational definition");
    };
    let ResolvedExprKind::Occurrence(body_use) = &definition.body.result.kind else {
        panic!("expected a resolved parameter occurrence");
    };
    let ResolvedExprKind::Apply(application) = &main_body(&program).kind else {
        panic!("expected an application");
    };
    let ResolvedExprKind::Occurrence(global_use) = &application.function.kind else {
        panic!("expected a resolved global occurrence");
    };

    assert_eq!(
        occurrence_binder(body_use),
        pattern_binder(&definition.header.parameters[0].pattern).id
    );
    assert_eq!(occurrence_binder(global_use), definition.header.name.id);
    assert_ne!(occurrence_binder(body_use), occurrence_binder(global_use));
}

#[test]
fn local_initializer_uses_incoming_scope_before_shadowing_binder_is_introduced() {
    let program = resolve_valid(
        "main : Unit -> Int\nmain () = {\n    let value = 1\n    let value = value + 1\n    value\n}\n",
    );
    let ResolvedExprKind::Block(block) = &main_body(&program).kind else {
        panic!("expected a resolved block");
    };
    let first = binding_binder(binding(block, 0));
    let second = binding_binder(binding(block, 1));
    let ResolvedExprKind::Add(addition) = &binding(block, 1).initializer.kind else {
        panic!("expected an addition initializer");
    };
    let ResolvedExprKind::Occurrence(initializer_use) = &addition.left.kind else {
        panic!("expected a resolved initializer occurrence");
    };
    let ResolvedExprKind::Occurrence(result_use) = &block.result.kind else {
        panic!("expected a resolved result occurrence");
    };

    assert_ne!(first.id, second.id);
    assert_eq!(occurrence_binder(initializer_use), first.id);
    assert_eq!(occurrence_binder(result_use), second.id);
    assert_eq!(first.origin.primary_span().range().start(), 39);
    assert_eq!(second.origin.primary_span().range().start(), 57);
    assert_eq!(initializer_use.origin.primary_span().range().start(), 65);
    assert_eq!(result_use.origin.primary_span().range().start(), 79);
}

#[test]
fn anonymous_parameter_shadows_outer_binder_only_inside_its_body() {
    let program = resolve_valid(
        "main : Unit -> Int\nmain () = {\n    let value = 1\n    let identity = fn(value) {\n        value\n    }\n    value\n}\n",
    );
    let ResolvedExprKind::Block(block) = &main_body(&program).kind else {
        panic!("expected a resolved block");
    };
    let outer = binding_binder(binding(block, 0));
    let ResolvedExprKind::Function(function) = &binding(block, 1).initializer.kind else {
        panic!("expected a resolved anonymous function");
    };
    let ResolvedExprKind::Occurrence(body_use) = &function.body.result.kind else {
        panic!("expected a resolved parameter occurrence");
    };
    let ResolvedExprKind::Occurrence(block_use) = &block.result.kind else {
        panic!("expected a resolved outer occurrence");
    };

    let parameter = pattern_binder(&function.pattern);
    assert_ne!(outer.id, parameter.id);
    assert_eq!(occurrence_binder(body_use), parameter.id);
    assert_eq!(occurrence_binder(block_use), outer.id);
}

#[test]
fn primitive_and_binary_forms_preserve_values_and_operator_spans() {
    let boolean = resolve_valid("main : Unit -> Bool\nmain () = true == (2 * 3 + 4)\n");
    let ResolvedExprKind::Equal(equality) = &main_body(&boolean).kind else {
        panic!("expected equality");
    };
    assert!(matches!(
        equality.left.kind,
        ResolvedExprKind::Boolean(true)
    ));
    assert_eq!(equality.operator_span.range().start(), 35);
    let ResolvedExprKind::Add(addition) = &equality.right.kind else {
        panic!("expected addition");
    };
    let ResolvedExprKind::Multiply(multiplication) = &addition.left.kind else {
        panic!("expected multiplication");
    };
    assert_eq!(multiplication.operator_span.range().start(), 41);
    assert_eq!(addition.operator_span.range().start(), 45);

    let unit = resolve_valid("main : Unit -> Unit\nmain () = ()\n");
    assert!(matches!(main_body(&unit).kind, ResolvedExprKind::Unit));
}

#[test]
fn unknown_name_has_r001_reason_and_only_the_causal_occurrence() {
    let error = resolve_error("main : Unit -> Unit\nmain () = missing\n");

    assert_eq!(error.reason, ResolveReason::UnknownName);
    assert_eq!(error.reason.to_string(), "resolve.unknown-name");
    assert_eq!(error.primary.span().range().start(), 30);
    assert_eq!(error.primary.span().range().end(), 37);
    assert!(error.related.is_empty());
    assert!(error.expected.is_none());
    assert!(error.found.is_none());
    assert!(error.help.is_none());
}

#[test]
fn recursive_global_bodies_see_the_complete_file_scope() {
    let recursive = resolve_valid(
        "self : Int -> Int\nself value = self value\n\nmain : Unit -> Int\nmain () = 0\n",
    );
    let ResolvedDefinitionKind::Equational(self_definition) = &recursive.definitions()[0].kind
    else {
        panic!("expected self equation")
    };
    let ResolvedExprKind::Apply(self_application) = &self_definition.equations[0].body.kind else {
        panic!("expected recursive application")
    };
    let ResolvedExprKind::Occurrence(self_use) = &self_application.function.kind else {
        panic!("expected recursive occurrence")
    };
    assert_eq!(
        occurrence_binder(self_use),
        self_definition.interface.name.id
    );

    let forward = resolve_valid(
        "first : Int -> Int\nfirst value = second value\n\nsecond : Int -> Int\nsecond value = value\n\nmain : Unit -> Int\nmain () = first 0\n",
    );
    let ResolvedDefinitionKind::Equational(first) = &forward.definitions()[0].kind else {
        panic!("expected first equation")
    };
    let ResolvedDefinitionKind::Equational(second) = &forward.definitions()[1].kind else {
        panic!("expected second equation")
    };
    let ResolvedExprKind::Apply(application) = &first.equations[0].body.kind else {
        panic!("expected forward application")
    };
    let ResolvedExprKind::Occurrence(second_use) = &application.function.kind else {
        panic!("expected forward occurrence")
    };
    assert_eq!(occurrence_binder(second_use), second.interface.name.id);
}

#[test]
fn recursive_local_members_share_scope_and_remain_visible_after_the_group() {
    let program = resolve_valid(
        "main : Unit -> Int\nmain () = {\nlet rec first : Unit -> Int = fn(ignored) {\nsecond ()\n}\nand second : Unit -> Int = fn(ignored) {\nfirst ()\n}\nfirst ()\n}\n",
    );
    let ResolvedExprKind::Block(block) = &main_body(&program).kind else {
        panic!("expected block")
    };
    let ResolvedLocalDeclaration::Recursive(group) = &block.declarations[0] else {
        panic!("expected recursive group")
    };
    assert_eq!(group.members.len(), 2);
    let first = &group.members[0];
    let second = &group.members[1];
    let ResolvedExprKind::Function(first_function) = &first.initializer.kind else {
        panic!("expected first function")
    };
    let ResolvedExprKind::Apply(first_body) = &first_function.body.result.kind else {
        panic!("expected first call")
    };
    let ResolvedExprKind::Occurrence(second_use) = &first_body.function.kind else {
        panic!("expected second occurrence")
    };
    let ResolvedExprKind::Function(second_function) = &second.initializer.kind else {
        panic!("expected second function")
    };
    let ResolvedExprKind::Apply(second_body) = &second_function.body.result.kind else {
        panic!("expected second call")
    };
    let ResolvedExprKind::Occurrence(first_use) = &second_body.function.kind else {
        panic!("expected first occurrence")
    };
    let ResolvedExprKind::Apply(result) = &block.result.kind else {
        panic!("expected result call")
    };
    let ResolvedExprKind::Occurrence(result_use) = &result.function.kind else {
        panic!("expected result occurrence")
    };

    assert_eq!(occurrence_binder(second_use), second.binder.id);
    assert_eq!(occurrence_binder(first_use), first.binder.id);
    assert_eq!(occurrence_binder(result_use), first.binder.id);
}

#[test]
fn recursive_group_captures_outer_scope_and_may_shadow_it() {
    let captured = resolve_valid(
        "main : Unit -> Int\nmain () = {\nlet captured = 42\nlet rec read : Unit -> Int = fn(ignored) {\ncaptured\n}\nread ()\n}\n",
    );
    let ResolvedExprKind::Block(block) = &main_body(&captured).kind else {
        panic!("expected captured block")
    };
    let outer = binding(block, 0);
    let ResolvedLocalDeclaration::Recursive(group) = &block.declarations[1] else {
        panic!("expected recursive group")
    };
    let ResolvedExprKind::Function(function) = &group.members[0].initializer.kind else {
        panic!("expected recursive function")
    };
    let ResolvedExprKind::Occurrence(captured_use) = &function.body.result.kind else {
        panic!("expected captured occurrence")
    };
    assert_eq!(occurrence_binder(captured_use), binding_binder(outer).id);

    let shadowed = resolve_valid(
        "main : Unit -> Int\nmain () = {\nlet repeat : Unit -> Int = fn(ignored) {\n1\n}\nlet rec repeat : Unit -> Int = fn(ignored) {\nrepeat ()\n}\nrepeat ()\n}\n",
    );
    let ResolvedExprKind::Block(block) = &main_body(&shadowed).kind else {
        panic!("expected shadowing block")
    };
    let outer = binding(block, 0);
    let ResolvedLocalDeclaration::Recursive(group) = &block.declarations[1] else {
        panic!("expected shadowing recursive group")
    };
    let member = &group.members[0];
    let ResolvedExprKind::Function(function) = &member.initializer.kind else {
        panic!("expected recursive function")
    };
    let ResolvedExprKind::Apply(call) = &function.body.result.kind else {
        panic!("expected self call")
    };
    let ResolvedExprKind::Occurrence(self_use) = &call.function.kind else {
        panic!("expected self occurrence")
    };
    assert_ne!(member.binder.id, binding_binder(outer).id);
    assert_eq!(occurrence_binder(self_use), member.binder.id);
}

#[test]
fn duplicate_recursive_member_relates_the_first_definition() {
    let error = resolve_error(
        "main : Unit -> Int\nmain () = {\nlet rec same : Unit -> Int = fn(value) {\n1\n}\nand same : Unit -> Int = fn(value) {\n2\n}\nsame ()\n}\n",
    );

    assert_eq!(error.reason, ResolveReason::DuplicateRecursiveMember);
    assert_eq!(error.related.len(), 1);
    assert_eq!(error.found.as_deref(), Some("same"));
}

#[test]
fn later_global_body_resolves_an_earlier_global_identity() {
    let program = resolve_valid(
        "first : Int -> Int\nfirst value = value\n\nsecond : Int -> Int\nsecond value = first value\n\nmain : Unit -> Int\nmain () = second 1\n",
    );
    let ResolvedDefinitionKind::Equational(first) = &program.definitions()[0].kind else {
        panic!("expected first equation");
    };
    let ResolvedDefinitionKind::Equational(second) = &program.definitions()[1].kind else {
        panic!("expected second equation");
    };
    let ResolvedExprKind::Apply(application) = &second.equations[0].body.kind else {
        panic!("expected the second body application");
    };
    let ResolvedExprKind::Occurrence(first_use) = &application.function.kind else {
        panic!("expected an earlier-global occurrence");
    };

    assert_eq!(occurrence_binder(first_use), first.interface.name.id);
    assert_ne!(occurrence_binder(first_use), second.interface.name.id);
}

#[test]
fn local_initializer_cannot_see_the_binder_it_is_defining() {
    let error =
        resolve_error("main : Unit -> Int\nmain () = {\n    let value = value\n    value\n}\n");

    assert_eq!(error.reason, ResolveReason::UnknownName);
    assert_eq!(error.primary.span().range().start(), 47);
    assert_eq!(error.primary.span().range().end(), 52);
}

#[test]
fn duplicate_check_applies_across_both_global_presentations() {
    let error = resolve_error(
        "first : Int -> Int\nfirst value = value\n\nfn first(value : Int) -> Int {\n    value\n}\n\nmain : Unit -> Int\nmain () = 0\n",
    );

    assert_eq!(error.reason, ResolveReason::DuplicateGlobal);
    assert_eq!(error.primary.span().range().start(), 43);
    assert_eq!(error.primary.span().range().end(), 48);
    assert_eq!(error.related.len(), 2);
}

#[test]
fn definition_and_occurrence_keep_distinct_causal_origins_and_exact_spelling() {
    let program = resolve_valid(
        "identity : Int -> Int\nidentity value = value\n\nmain : Unit -> (Int -> Int)\nmain () = identity\n",
    );
    let ResolvedDefinitionKind::Equational(definition) = &program.definitions()[0].kind else {
        panic!("expected an equation");
    };
    let ResolvedExprKind::Occurrence(use_site) = &main_body(&program).kind else {
        panic!("expected a resolved occurrence");
    };

    assert_eq!(definition.interface.name.spelling, "identity");
    assert_eq!(use_site.spelling, "identity");
    assert_eq!(occurrence_binder(use_site), definition.interface.name.id);
    assert_eq!(
        definition
            .interface
            .name
            .origin
            .primary_span()
            .range()
            .start(),
        0
    );
    assert_eq!(
        definition
            .interface
            .name
            .origin
            .primary_span()
            .range()
            .end(),
        8
    );
    assert_eq!(use_site.origin.primary_span().range().start(), 84);
    assert_eq!(use_site.origin.primary_span().range().end(), 92);
}

#[test]
fn admitted_expression_depth_resolves_and_drops_on_a_small_host_stack() {
    let expression = std::iter::repeat_n("1", STRUCTURAL_DEPTH_LIMIT + 1)
        .collect::<Vec<_>>()
        .join(" + ");
    let worker = std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(move || {
            let source = format!("main : Unit -> Int\nmain () = {expression}\n");
            let program = resolve_valid(&source);
            assert!(matches!(main_body(&program).kind, ResolvedExprKind::Add(_)));
        })
        .expect("the depth-test worker should start");

    worker
        .join()
        .expect("resolution and recursive value drop should remain within the stack budget");
}

#[test]
fn admitted_function_and_block_depth_resolves_and_drops_on_a_small_host_stack() {
    let mut expression = "1".to_owned();
    for _ in 0..(STRUCTURAL_DEPTH_LIMIT / 2) {
        expression = format!("fn(value) {{\n{expression}\n}}");
    }
    let worker = std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(move || {
            let source = format!("main : Unit -> Unit\nmain () = {expression}\n");
            let program = resolve_valid(&source);
            assert!(matches!(
                main_body(&program).kind,
                ResolvedExprKind::Function(_)
            ));
        })
        .expect("the nested-function worker should start");

    worker
        .join()
        .expect("nested function resolution and drop should remain within the stack budget");
}

#[test]
fn admitted_type_depth_resolves_and_drops_on_a_small_host_stack() {
    let source = format!(
        "f : {}Int\nf value = value\n\nmain : Unit -> Unit\nmain value = value\n",
        "Int -> ".repeat(STRUCTURAL_DEPTH_LIMIT)
    );
    let worker = std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(move || {
            let program = resolve_valid(&source);
            assert_eq!(program.definitions().len(), 2);
        })
        .expect("the nested-type worker should start");

    worker
        .join()
        .expect("type preservation and drop should remain within the stack budget");
}

#[test]
fn resolved_presentations_retain_annotations_component_spans_and_full_spans() {
    let program = resolve_valid(
        "fn increment(value : Int) -> Int {\n    let one : Int = 1\n    value + one\n}\n\nmain : Unit -> Int\nmain () = increment 41\n",
    );
    let definition = &program.definitions()[0];
    let ResolvedDefinitionKind::InlineOperational(definition) = &definition.kind else {
        panic!("expected an inline operational definition");
    };

    assert_eq!(
        definition.header.name.origin.primary_span().range().start(),
        3
    );
    assert_eq!(definition.header.parameters[0].span.range().start(), 13);
    assert_eq!(definition.header.parameters[0].span.range().end(), 24);
    assert_eq!(definition.header.parameters[0].annotation.ty, Type::Int);
    assert_eq!(definition.header.result_type.span.range().start(), 29);
    assert_eq!(definition.header.result_type.span.range().end(), 32);
    assert_eq!(binding(&definition.body, 0).span.range().start(), 39);
    assert_eq!(binding(&definition.body, 0).span.range().end(), 56);
    assert_eq!(
        binding(&definition.body, 0)
            .annotation
            .as_ref()
            .map(|annotation| &annotation.ty),
        Some(&Type::Int)
    );
    let ResolvedExprKind::Add(addition) = &definition.body.result.kind else {
        panic!("expected an addition body");
    };
    assert_eq!(addition.operator_span.range().start(), 67);
    assert_eq!(addition.operator_span.range().end(), 68);
    assert_eq!(definition.body.span.range().start(), 33);
    assert_eq!(definition.body.span.range().end(), 74);
    assert_eq!(program.span().range().start(), 0);
}

#[test]
fn fail_fast_resolution_reports_only_the_first_unavailable_name_fact() {
    let error = resolve_error("main : Unit -> Int\nmain () = missing + unavailable\n");

    assert_eq!(error.reason, ResolveReason::UnknownName);
    assert_eq!(error.primary.span().range().start(), 29);
    assert_eq!(error.primary.span().range().end(), 36);
    assert!(error.related.is_empty());
}

#[test]
fn local_binding_may_shadow_a_global_without_changing_the_global_identity() {
    let program = resolve_valid(
        "value : Int -> Int\nvalue parameter = parameter\n\nmain : Unit -> Int\nmain () = {\n    let value = 1\n    value\n}\n",
    );
    let ResolvedDefinitionKind::Equational(global) = &program.definitions()[0].kind else {
        panic!("expected an equation");
    };
    let ResolvedExprKind::Block(block) = &main_body(&program).kind else {
        panic!("expected a block");
    };
    let ResolvedExprKind::Occurrence(local_use) = &block.result.kind else {
        panic!("expected a local occurrence");
    };

    assert_ne!(
        binding_binder(binding(block, 0)).id,
        global.interface.name.id
    );
    assert_eq!(
        occurrence_binder(local_use),
        binding_binder(binding(block, 0)).id
    );
}

#[test]
fn anonymous_function_captures_outer_binder_and_keeps_parameter_identity_separate() {
    let program = resolve_valid(
        "main : Unit -> Int\nmain () = {\n    let offset = 40\n    let add_offset = fn(value) {\n        value + offset\n    }\n    add_offset 2\n}\n",
    );
    let ResolvedExprKind::Block(block) = &main_body(&program).kind else {
        panic!("expected a block");
    };
    let offset = binding_binder(binding(block, 0));
    let ResolvedExprKind::Function(function) = &binding(block, 1).initializer.kind else {
        panic!("expected an anonymous function");
    };
    let ResolvedExprKind::Add(addition) = &function.body.result.kind else {
        panic!("expected an addition body");
    };
    let ResolvedExprKind::Occurrence(parameter_use) = &addition.left.kind else {
        panic!("expected a parameter occurrence");
    };
    let ResolvedExprKind::Occurrence(capture_use) = &addition.right.kind else {
        panic!("expected a captured occurrence");
    };

    assert_eq!(
        occurrence_binder(parameter_use),
        pattern_binder(&function.pattern).id
    );
    assert_eq!(occurrence_binder(capture_use), offset.id);
    assert_ne!(
        occurrence_binder(parameter_use),
        occurrence_binder(capture_use)
    );
}
