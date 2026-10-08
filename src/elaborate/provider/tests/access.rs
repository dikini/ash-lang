use super::*;

#[test]
fn independent_state_access_association_checks_exact_defining_relation_and_budget() {
    let fixture = Fixture::with_registrations(
        &format!("import @foreign.provider as Provider\n{SOURCE}\n{STATEMENT}"),
        ForeignRegistrations::new([
            sqlite_manifest(ForeignRegistrationId::new(991)).unwrap(),
            crate::foreign::provider_manifest(ForeignRegistrationId::new(992)).unwrap(),
        ])
        .unwrap(),
    );
    let mut checker = fixture.elaborator();
    let connection = &fixture.resolved.resources()[0];
    let statement = &fixture.resolved.resources()[1];
    let connection_header = checker
        .check_provider_header(&fixture.resolved, connection)
        .unwrap();
    let statement_header = checker
        .check_provider_header(&fixture.resolved, statement)
        .unwrap();
    let source_association = &connection_header.state_association;
    let draft = fixture
        .elaborator()
        .compile_provider_lifecycle_with_associations(
            statement,
            &statement_header,
            Phase::Acquire,
            vec![
                source_association
                    .clone_with_budget(&mut checker.type_work)
                    .unwrap(),
            ],
        )
        .unwrap();
    let association = crate::core::provider::DraftStateAssociation {
        definition: source_association.definition,
        family: source_association.family,
        parameters: &source_association.parameters,
        state: &source_association.state,
    };
    let mut measured = TypeWorkBudget::with_limit(usize::MAX);
    crate::core::provider::check_state_access_associations(
        &draft.core,
        &[association],
        &mut measured,
    )
    .unwrap();
    draft
        .check_flow_with_associations(statement, &[association], &mut TypeWorkBudget::unbounded())
        .unwrap();
    let mut exact = TypeWorkBudget::with_limit(measured.used());
    crate::core::provider::check_state_access_associations(&draft.core, &[association], &mut exact)
        .unwrap();
    assert_eq!(exact.used(), measured.used());
    let mut short = TypeWorkBudget::with_limit(measured.used() - 1);
    assert_eq!(
        crate::core::provider::check_state_access_associations(
            &draft.core,
            &[association],
            &mut short
        )
        .unwrap_err()
        .reason(),
        crate::core::ValidationReason::Resource
    );
    let mut prefix = TypeWorkBudget::with_limit(measured.used() + 5);
    prefix.charge(5).unwrap();
    crate::core::provider::check_state_access_associations(
        &draft.core,
        &[association],
        &mut prefix,
    )
    .unwrap();
    assert_eq!(prefix.used(), measured.used() + 5);
    assert!(
        crate::core::provider::check_state_access_associations(
            &draft.core,
            &[],
            &mut TypeWorkBudget::unbounded()
        )
        .is_err()
    );
    assert!(
        crate::core::provider::check_state_access_associations(
            &draft.core,
            &[association, association],
            &mut TypeWorkBudget::unbounded()
        )
        .is_err()
    );

    use crate::core::provider::AccessMutation;
    for mutation in [
        AccessMutation::Method,
        AccessMutation::Definition,
        AccessMutation::Arguments,
        AccessMutation::Operand,
        AccessMutation::Result,
        AccessMutation::Effects,
    ] {
        let mut mutated = fixture
            .elaborator()
            .compile_provider_lifecycle_with_associations(
                statement,
                &statement_header,
                Phase::Acquire,
                vec![
                    source_association
                        .clone_with_budget(&mut checker.type_work)
                        .unwrap(),
                ],
            )
            .unwrap();
        crate::core::provider::mutate_state_access(&mut mutated.core, mutation);
        assert!(
            crate::core::provider::check_state_access_associations(
                &mutated.core,
                &[association],
                &mut TypeWorkBudget::unbounded()
            )
            .is_err()
        );
    }
}

#[test]
fn independent_state_access_association_deep_metadata_failure_and_drop_on_small_stack() {
    let fixture = Fixture::with_registrations(
        &format!("import @foreign.provider as Provider\n{SOURCE}\n{STATEMENT}"),
        ForeignRegistrations::new([
            sqlite_manifest(ForeignRegistrationId::new(991)).unwrap(),
            crate::foreign::provider_manifest(ForeignRegistrationId::new(992)).unwrap(),
        ])
        .unwrap(),
    );
    let mut checker = fixture.elaborator();
    let connection_header = checker
        .check_provider_header(&fixture.resolved, &fixture.resolved.resources()[0])
        .unwrap();
    let statement = &fixture.resolved.resources()[1];
    let statement_header = checker
        .check_provider_header(&fixture.resolved, statement)
        .unwrap();
    let source_association = connection_header
        .state_association
        .clone_with_budget(&mut checker.type_work)
        .unwrap();
    let mut draft = fixture
        .elaborator()
        .compile_provider_lifecycle_with_associations(
            statement,
            &statement_header,
            Phase::Acquire,
            vec![
                source_association
                    .clone_with_budget(&mut checker.type_work)
                    .unwrap(),
            ],
        )
        .unwrap();
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(move || {
            // Untrusted deep metadata tests the bounded relational helper and its
            // cleanup; it is not an admitted kind/depth/phase/executable artifact.
            crate::core::provider::deepen_state_access_argument(&mut draft.core, 8192);
            let association = crate::core::provider::DraftStateAssociation {
                definition: source_association.definition,
                family: source_association.family,
                parameters: &source_association.parameters,
                state: &source_association.state,
            };
            let mut measured = TypeWorkBudget::unbounded();
            crate::core::provider::check_state_access_associations(
                &draft.core,
                &[association],
                &mut measured,
            )
            .unwrap();
            let mut exact = TypeWorkBudget::with_limit(measured.used());
            crate::core::provider::check_state_access_associations(
                &draft.core,
                &[association],
                &mut exact,
            )
            .unwrap();
            let mut late = TypeWorkBudget::with_limit(measured.used() - 1);
            assert_eq!(
                crate::core::provider::check_state_access_associations(
                    &draft.core,
                    &[association],
                    &mut late
                )
                .unwrap_err()
                .reason(),
                crate::core::ValidationReason::Resource
            );
            drop(draft);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn independent_state_access_association_proves_enclosing_coordinates_and_clears_callable_phase() {
    let statement_source = STATEMENT.replace(
        "(db, sql) => perform Native.Statement<S, C>.prepare (Provider.state_of db, sql)",
        "(db, sql) => {\nlet unused : Unit -> Int = fn(value) {\nlet untouched = 42\n42\n}\nlet held = Provider.state_of db\nperform Native.Statement<S, C>.prepare (held, sql)\n}",
    );
    let fixture = Fixture::with_registrations(
        &format!("import @foreign.provider as Provider\n{SOURCE}\n{statement_source}"),
        ForeignRegistrations::new([
            sqlite_manifest(ForeignRegistrationId::new(991)).unwrap(),
            crate::foreign::provider_manifest(ForeignRegistrationId::new(992)).unwrap(),
        ])
        .unwrap(),
    );
    let mut checker = fixture.elaborator();
    let connection = &fixture.resolved.resources()[0];
    let statement = &fixture.resolved.resources()[1];
    let connection_header = checker
        .check_provider_header(&fixture.resolved, connection)
        .unwrap();
    let statement_header = checker
        .check_provider_header(&fixture.resolved, statement)
        .unwrap();
    let source_association = &connection_header.state_association;
    let association = crate::core::provider::DraftStateAssociation {
        definition: source_association.definition,
        family: source_association.family,
        parameters: &source_association.parameters,
        state: &source_association.state,
    };
    let mut compile = || {
        fixture
            .elaborator()
            .compile_provider_lifecycle_with_associations(
                statement,
                &statement_header,
                Phase::Acquire,
                vec![
                    source_association
                        .clone_with_budget(&mut checker.type_work)
                        .unwrap(),
                ],
            )
            .unwrap()
    };
    let draft = compile();
    let mut measured = TypeWorkBudget::unbounded();
    draft
        .check_flow_with_associations(statement, &[association], &mut measured)
        .unwrap();
    crate::core::provider::check_enclosing_finish_rejection_for_test(
        &draft.core,
        &mut TypeWorkBudget::unbounded(),
    )
    .unwrap();
    let mut exact = TypeWorkBudget::with_limit(measured.used());
    draft
        .check_flow_with_associations(statement, &[association], &mut exact)
        .unwrap();
    let mut short = TypeWorkBudget::with_limit(measured.used() - 1);
    assert!(
        matches!(draft.check_flow_with_associations(statement, &[association], &mut short), Err(LifecycleDraftCheckError::Core(error)) if error.reason() == crate::core::ValidationReason::Resource)
    );
    let mut prefix = TypeWorkBudget::with_limit(measured.used() + 7);
    prefix.charge(7).unwrap();
    draft
        .check_flow_with_associations(statement, &[association], &mut prefix)
        .unwrap();
    assert_eq!(prefix.used(), measured.used() + 7);
    for mutation in [
        crate::core::provider::AccessMutation::OtherEnclosing,
        crate::core::provider::AccessMutation::Callable,
    ] {
        let mut changed = compile();
        crate::core::provider::mutate_state_access(&mut changed.core, mutation);
        // Both mutations preserve the exact header/type association. The flow
        // proof must independently reject wrong native coordinates or a phase
        // moved beneath an ordinary callable with an independent result.
        crate::core::provider::check_state_access_associations(
            &changed.core,
            &[association],
            &mut TypeWorkBudget::unbounded(),
        )
        .unwrap();
        assert!(
            matches!(changed.check_flow_with_associations(statement, &[association], &mut TypeWorkBudget::unbounded()), Err(LifecycleDraftCheckError::Core(error)) if error.reason() == crate::core::ValidationReason::ResourceEscape)
        );
    }
}
