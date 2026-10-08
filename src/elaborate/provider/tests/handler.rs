use super::*;

const SQLITE: &str =
    include_str!("../../../../tests/fixtures/provider-experiments/sqlite-copying/sqlite.ash");
const PROVIDER: &str =
    include_str!("../../../../tests/fixtures/provider-experiments/sqlite-copying/provider.ash");

const STATEMENT_METHODS: [&str; 3] = ["bind_int", "step", "column_int"];

fn statement_links(
    fixture: &Fixture,
) -> Vec<(crate::types::OperationId, crate::resolved::ResumeId)> {
    let definition = &fixture.resolved.resources()[1];
    let effect = fixture
        .resolved
        .registry()
        .effect(definition.provided.instance.effect())
        .unwrap();
    assert_eq!(
        effect
            .operations
            .iter()
            .map(|operation| operation.spelling.as_str())
            .collect::<Vec<_>>(),
        STATEMENT_METHODS
    );
    assert_eq!(
        definition
            .handlers
            .iter()
            .map(|clause| clause.operation)
            .collect::<Vec<_>>(),
        effect
            .operations
            .iter()
            .map(|operation| operation.id)
            .collect::<Vec<_>>()
    );
    definition
        .handlers
        .iter()
        .map(|clause| (clause.operation, clause.resume))
        .collect()
}

fn assert_statement_occurrences(
    fixture: &Fixture,
    occurrences: &[CheckedGlobalOccurrence],
    expected: [usize; 3],
) {
    let links = statement_links(fixture);
    let definition = &fixture.resolved.resources()[1];
    assert_eq!(links.len(), expected.len());
    let mut actual = [0; 3];
    for occurrence in occurrences {
        let span = occurrence.occurrence.origin.primary_span();
        let owners = definition
            .handlers
            .iter()
            .enumerate()
            .filter(|(_, clause)| {
                let body = clause.body.span;
                body.source() == span.source()
                    && body.range().start() <= span.range().start()
                    && span.range().end() <= body.range().end()
            })
            .map(|(index, _)| index)
            .collect::<Vec<_>>();
        assert_eq!(
            owners.len(),
            1,
            "every selected occurrence belongs to exactly one actual clause"
        );
        actual[owners[0]] += 1;
    }
    assert_eq!(
        actual, expected,
        "selected occurrences cover the exact ordered Statement roots"
    );
}

fn actual_fixture(source: &str) -> external::HelperFixture {
    external::HelperFixture::new(
        &source.replace("import provider as Provider", "import helper as Provider"),
        PROVIDER,
    )
}

fn check(fixture: &Fixture, ordinal: usize) -> Result<HandlerSourceDraft, TypeError> {
    let definition = &fixture.resolved.resources()[ordinal];
    let header = fixture
        .elaborator()
        .check_provider_header(&fixture.resolved, definition)?;
    fixture.elaborator().check_provider_handler_source(
        definition,
        &header,
        fixture.resolved.imported_facts(),
    )
}

#[test]
fn actual_connection_handler_has_a_declaration_draft_entry() {
    let fixture = actual_fixture(SQLITE);
    let fixture = &fixture.fixture;
    let draft = check(fixture, 0).unwrap();
    let definition = &fixture.resolved.resources()[0];
    assert_eq!(draft.id, ProviderTemplateId::new(definition.id, 2));
    assert_eq!(draft.state_parameter.id(), definition.handlers_binder.id);
    assert_ne!(
        draft.hidden_row,
        EffectRowVariable::rigid(draft.hidden_answer)
    );
    assert_eq!(draft.clauses.len(), 1);
    assert_eq!(
        draft.direct_demands.known(),
        std::slice::from_ref(&definition.interpreted.instance)
    );
    assert!(draft.direct_demands.tail().is_none());
    let clause = &draft.clauses[0];
    assert_eq!(clause.operation, definition.handlers[0].operation);
    assert_eq!(clause.resume, definition.handlers[0].resume);
    assert_eq!(clause.origin.primary_span(), definition.handlers[0].span);
    let body = usize::try_from(clause.body.value()).unwrap();
    assert!(clause.range.contains(&body));
    assert!(clause.range.end <= draft.builder.node_checkpoint());
    assert_eq!(
        clause.pattern.binder_iter().next().unwrap().id(),
        match &definition.handlers[0].pattern.kind {
            ResolvedPatternKind::Binder(binder) => binder.id,
            _ => unreachable!(),
        }
    );
}

#[test]
fn actual_statement_handlers_check_tuple_columns_and_each_error_branch() {
    let fixture = actual_fixture(SQLITE);
    let fixture = &fixture.fixture;
    let draft = check(fixture, 1).unwrap();
    let definition = &fixture.resolved.resources()[1];
    assert_eq!(draft.clauses.len(), 3);
    assert_eq!(
        draft.direct_demands.known(),
        std::slice::from_ref(&definition.interpreted.instance)
    );
    assert!(draft.direct_demands.tail().is_none());
    for (actual, source) in draft.clauses.iter().zip(&definition.handlers) {
        assert_eq!(actual.operation, source.operation);
        assert_eq!(actual.resume, source.resume);
        assert_eq!(actual.origin.primary_span(), source.span);
        assert!(
            actual
                .range
                .contains(&usize::try_from(actual.body.value()).unwrap())
        );
    }
    assert!(
        draft
            .clauses
            .windows(2)
            .all(|pair| pair[0].range.end <= pair[1].range.start)
    );
}

#[test]
fn source_handler_checks_pure_imported_error_mapping_and_single_resume_branches() {
    let source = SQLITE.replace(
        "ForeignError (perform Native.Connection<R>.diagnostic state)",
        "ForeignError (Provider.map (perform Native.Connection<R>.diagnostic state))",
    );
    let fixture = external::HelperFixture::new(
        &source.replace("import provider as Provider", "import helper as Provider"),
        &format!(
            "import @foreign.sqlite as Native\n{PROVIDER}\npub map : Native.Error -> Native.Error\nmap error = error\n"
        ),
    );
    let draft = check(&fixture.fixture, 0).unwrap();
    assert_eq!(draft.clauses.len(), 1);
    assert_eq!(draft.occurrences.len(), 1);
    assert!(draft.occurrences.iter().all(|occurrence| {
        occurrence
            .occurrence
            .evidence
            .iter()
            .all(|slot| slot.selection().is_none())
    }));
    let source = SQLITE.replace("diagnostic db => resume (ForeignError (perform Native.Connection<R>.diagnostic state))", "diagnostic db => match true {\ntrue => resume (ForeignError (perform Native.Connection<R>.diagnostic state))\nfalse => resume MissingRow\n}");
    let fixture = actual_fixture(&source);
    assert!(check(&fixture.fixture, 0).is_ok());
}

#[test]
fn source_handler_rejects_wrong_results_resume_usage_and_native_laundering() {
    let original =
        "diagnostic db => resume (ForeignError (perform Native.Connection<R>.diagnostic state))";
    for replacement in [
        "diagnostic db => resume ()",
        "diagnostic db => MissingRow",
        "diagnostic db => {\nlet ignored = resume MissingRow\nresume MissingRow\n}",
        "diagnostic db => {\nlet ignored = fn(unit) {\nresume MissingRow\n}\nresume MissingRow\n}",
        "diagnostic (db, ignored) => resume MissingRow",
        "diagnostic db => {\nlet ignored = perform Native.Connection<R>.open InMemory\nresume MissingRow\n}",
        "diagnostic db => {\nlet ignored = perform Native.Connection<R>.close state\nresume MissingRow\n}",
        "diagnostic db => {\nlet ignored = fn(unit) {\nperform Native.Connection<R>.diagnostic state\n}\nresume MissingRow\n}",
        "diagnostic db => resume (ForeignError (perform Native.Connection<Int>.diagnostic state))",
    ] {
        let fixture = actual_fixture(&SQLITE.replace(original, replacement));
        assert!(
            check(&fixture.fixture, 0).is_err(),
            "accepted {replacement}"
        );
    }
}

#[test]
fn source_handler_checks_owner_coverage_refutability_and_exact_resume_identity() {
    let fixture = actual_fixture(SQLITE);
    let f = &fixture.fixture;
    for mutation in 0..4 {
        let mut definition = f.resolved.resources()[0].clone();
        match mutation {
            0 => definition.handlers[0].operation = f.resolved.resources()[1].handlers[0].operation,
            1 => definition.handlers = Box::new([]),
            2 => {
                definition.handlers = vec![
                    definition.handlers[0].clone(),
                    definition.handlers[0].clone(),
                ]
                .into_boxed_slice()
            }
            3 => {
                let ResolvedExprKind::Resume(resume) = &mut definition.handlers[0].body.kind else {
                    unreachable!()
                };
                resume.owner = Some(f.resolved.resources()[1].handlers[0].resume);
            }
            _ => unreachable!(),
        }
        let header = f
            .elaborator()
            .check_provider_header(&f.resolved, &f.resolved.resources()[0])
            .unwrap();
        assert!(
            f.elaborator()
                .check_provider_handler_source(&definition, &header, f.resolved.imported_facts())
                .is_err(),
            "accepted mutation {mutation}"
        );
    }
    let source = SOURCE
        .replace("Connection<R> -> Native.Error", "Bool -> Native.Error")
        .replace("read db =>", "read true =>");
    let fixture = Fixture::new(&source);
    assert!(check(&fixture, 0).is_err());
}

#[test]
fn source_handler_budget_refusal_is_unpublished_and_fresh_retry_is_exact() {
    let fixture = actual_fixture(SQLITE);
    let f = &fixture.fixture;
    for definition in f.resolved.resources() {
        let header = f
            .elaborator()
            .check_provider_header(&f.resolved, definition)
            .unwrap();
        let mut compiler = f.elaborator();
        compiler.type_work = TypeWorkBudget::unbounded();
        let draft = compiler
            .check_provider_handler_source(definition, &header, f.resolved.imported_facts())
            .unwrap();
        let cost = draft.compile_work;
        eprintln!("handler source {} compile={cost}", definition.spelling);
        for prefix in [0, 17] {
            for allowance in [cost - 1, cost] {
                for _ in 0..2 {
                    let mut compiler = f.elaborator();
                    compiler.type_work = TypeWorkBudget::with_limit(prefix + allowance);
                    compiler.type_work.charge(prefix).unwrap();
                    let result = compiler.check_provider_handler_source(
                        definition,
                        &header,
                        f.resolved.imported_facts(),
                    );
                    if allowance == cost {
                        let draft = result.unwrap();
                        assert_eq!(draft.compile_work, prefix + cost);
                        assert!(draft.occurrences.iter().all(|occurrence| {
                            occurrence
                                .occurrence
                                .evidence
                                .iter()
                                .all(|slot| slot.selection().is_none())
                        }));
                    } else {
                        assert!(
                            matches!(
                                result,
                                Err(TypeError::Internal(
                                    ElaborationFailure::TypeResourceExhausted
                                ))
                            ),
                            "unexpected short result: {result:?}"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn actual_clause_late_refusal_unwinds_pattern_binders_and_active_resume() {
    let fixture = actual_fixture(&SQLITE.replace(
        "resume (ForeignError (perform Native.Connection<R>.diagnostic state))",
        "resume ()",
    ));
    let f = &fixture.fixture;
    let definition = &f.resolved.resources()[0];
    let mut compiler = f.elaborator();
    let answer = compiler
        .fresh_type_variable(&Kind::Type, definition.span)
        .unwrap();
    let mut context = compiler.base_context.clone();
    let original = context.binders.len();
    let result = compiler.check_effect_clauses(
        &definition.provided.instance,
        &definition.handlers,
        definition.span,
        &mut context,
        &Type::Variable(answer),
        EffectRow::empty(),
    );
    assert!(result.is_err());
    assert_eq!(context.binders.len(), original);
    assert!(compiler.active_resumes.is_empty());
}

#[test]
fn source_handler_checks_actual_tuple_pattern_and_irrefutable_newtype_lowering() {
    let source = SQLITE
        .replace(
            "diagnostic : Connection<R> -> Error",
            "diagnostic : (Connection<R>, SqlText) -> Error",
        )
        .replace("diagnostic db =>", "diagnostic (db, SqlText(bytes)) =>");
    let fixture = actual_fixture(&source);
    let draft = check(&fixture.fixture, 0).unwrap();
    assert_eq!(draft.clauses.len(), 1);
    // The newtype pattern is lowered before retention; its actual clause body
    // remains within the replay range and the operation identity is unchanged.
    let clause = &draft.clauses[0];
    assert!(
        matches!(&clause.pattern.kind, CorePatternKind::Tuple(elements) if elements.len() == 2 && matches!(elements[1].kind, CorePatternKind::Binder(_)))
    );
    assert!(
        clause
            .range
            .contains(&usize::try_from(clause.body.value()).unwrap())
    );
    assert_eq!(
        clause.operation,
        fixture.fixture.resolved.resources()[0].handlers[0].operation
    );
}

#[test]
fn every_clause_work_refusal_removes_pattern_binders_and_active_resume() {
    let fixture = actual_fixture(&SQLITE.replace(
        "resume (ForeignError (perform Native.Connection<R>.diagnostic state))",
        "resume MissingRow",
    ));
    let f = &fixture.fixture;
    let definition = &f.resolved.resources()[0];
    let run = |allowance| {
        let mut compiler = f.elaborator();
        let answer = compiler
            .fresh_type_variable(&Kind::Type, definition.span)
            .unwrap();
        let mut context = compiler.base_context.clone();
        let original = context.binders.len();
        compiler.type_work = TypeWorkBudget::with_limit(allowance);
        let result = compiler.check_effect_clauses(
            &definition.provided.instance,
            &definition.handlers,
            definition.span,
            &mut context,
            &Type::Variable(answer),
            EffectRow::empty(),
        );
        assert_eq!(
            context.binders.len(),
            original,
            "retained pattern at allowance {allowance}"
        );
        assert!(
            compiler.active_resumes.is_empty(),
            "retained resume at allowance {allowance}"
        );
        (result, compiler.type_work.used())
    };
    let (result, cost) = run(usize::MAX);
    assert!(result.is_ok());
    for allowance in 0..cost {
        assert!(
            run(allowance).0.is_err(),
            "accepted short clause work {allowance}/{cost}"
        );
    }
    assert!(run(cost).0.is_ok());
}

#[test]
fn source_handler_retains_nested_handler_before_continuation_row_realization() {
    let source = SQLITE.replace("pub effect ConnectionOps<R>", "pub effect H {\nop : Unit -> Unit\n}\npub effect ConnectionOps<R>").replace(
        "diagnostic db => resume (ForeignError (perform Native.Connection<R>.diagnostic state))",
        "diagnostic db => handle ({\nlet ignored = perform H.op ()\nresume MissingRow\n}) with H {\nop unit => resume ()\n}",
    );
    let fixture = actual_fixture(&source);
    let draft = check(&fixture.fixture, 0).unwrap();
    assert!(draft.direct_demands.is_empty());
    assert_eq!(draft.clauses.len(), 1);
    assert_eq!(draft.handler, HandlerId::new(0));
    // This proves source checking of the actual nested handler. Its shared
    // rows remain provisional until every owner is replayed at specialization.
}

#[test]
fn conditional_handler_retains_actual_nested_discard_before_admission() {
    let source = SQLITE.replace("pub effect ConnectionOps<R>", "pub effect H {\nop : Unit -> Unit\n}\npub effect ConnectionOps<R>").replace(
        "diagnostic db => resume (ForeignError (perform Native.Connection<R>.diagnostic state))",
        "diagnostic db => {\nlet ignored = handle (perform H.op ()) with H {\nop unit => discard\n}\nresume (ForeignError (perform Native.Connection<R>.diagnostic state))\n}",
    );
    let fixture = actual_fixture(&source);
    check(&fixture.fixture, 0).expect("well-typed provider clause with actual nested discard");
    let draft = compile(&fixture.fixture, 0)
        .expect("conditional cleanup equations must survive source forest lowering");
    assert_eq!(draft.fragment.clauses.len(), 1);
    assert!(!draft.fragment.pending_rows.equations.is_empty());
    eprintln!(
        "{}",
        crate::core::provider::pending_row_inventory_for_test(&draft.fragment)
    );
    let (_, owners, discards) = crate::core::provider::reconstructed_row_inventory_for_test(
        &draft.fragment,
        &fixture.fixture.resolved,
        &mut TypeWorkBudget::unbounded(),
    )
    .expect("actual row owners and discard ports reconstruct independently");
    assert_eq!((owners, discards), (2, 1));
    independent_compiled(&fixture.fixture, &draft, &mut TypeWorkBudget::unbounded())
        .expect("actual conditional nested discard needs independently authenticated recipe entry");
}

#[test]
fn conditional_recipe_reconstructs_distinct_actual_nested_output_owners() {
    let source = SQLITE.replace("pub effect ConnectionOps<R>", "pub effect H {\nop : Unit -> Unit\n}\npub effect ConnectionOps<R>").replace(
        "diagnostic db => resume (ForeignError (perform Native.Connection<R>.diagnostic state))",
        "diagnostic db => handle ({\nlet ignored = perform H.op ()\nresume MissingRow\n}) with H {\nop unit => resume ()\n}",
    );
    let fixture = actual_fixture(&source);
    let draft = compile(&fixture.fixture, 0).unwrap();
    let links = crate::core::provider::row_recipe_links_for_test(
        &draft.fragment,
        &fixture.fixture.resolved,
        &mut TypeWorkBudget::unbounded(),
    )
    .unwrap();
    let outer = links
        .iter()
        .filter(|(_, _, provider)| *provider)
        .collect::<Vec<_>>();
    let nested = links
        .iter()
        .filter(|(_, _, provider)| !*provider)
        .collect::<Vec<_>>();
    assert_eq!((outer.len(), nested.len()), (1, 1));
    assert_ne!(outer[0].1, nested[0].1);
    assert_eq!(outer[0].1, draft.fragment.handler);
    let capture = crate::core::capture::conditional_capture_inventory_for_test(
        &draft.fragment,
        &fixture.fixture.resolved,
        &mut TypeWorkBudget::unbounded(),
    )
    .unwrap();
    assert_eq!(capture, (1, 1, 1));
    independent_compiled(&fixture.fixture, &draft, &mut TypeWorkBudget::unbounded()).unwrap();
}

#[test]
fn conditional_recipe_rejects_pending_row_on_unrelated_pure_node() {
    let source = SQLITE.replace("pub effect ConnectionOps<R>", "pub effect H {\nop : Unit -> Unit\n}\npub effect ConnectionOps<R>").replace(
        "diagnostic db => resume (ForeignError (perform Native.Connection<R>.diagnostic state))",
        "diagnostic db => {\nlet ignored = handle (perform H.op ()) with H {\nop unit => discard\n}\nresume (ForeignError (perform Native.Connection<R>.diagnostic state))\n}",
    );
    let fixture = actual_fixture(&source);
    let mut draft = compile(&fixture.fixture, 0).unwrap();
    crate::core::provider::put_pending_on_unrelated_unit_for_test(&mut draft.fragment);
    assert!(
        crate::core::provider::reconstructed_row_inventory_for_test(
            &draft.fragment,
            &fixture.fixture.resolved,
            &mut TypeWorkBudget::unbounded(),
        )
        .is_err(),
        "a retained discard identity grants no independent pure-node row position"
    );
}

#[test]
fn conditional_recipe_rejects_coherent_pending_native_demand_loss() {
    let source = SQLITE.replace("pub effect ConnectionOps<R>", "pub effect H {\nop : Unit -> Unit\n}\npub effect ConnectionOps<R>").replace(
        "diagnostic db => resume (ForeignError (perform Native.Connection<R>.diagnostic state))",
        "diagnostic db => {\nlet ignored = handle (perform H.op ()) with H {\nop unit => discard\n}\nresume (ForeignError (perform Native.Connection<R>.diagnostic state))\n}",
    );
    let fixture = actual_fixture(&source);
    let mut draft = compile(&fixture.fixture, 0).unwrap();
    crate::core::provider::drop_native_from_pending_demands_for_test(&mut draft.fragment);
    assert!(
        crate::core::provider::reconstructed_row_inventory_for_test(
            &draft.fragment,
            &fixture.fixture.resolved,
            &mut TypeWorkBudget::unbounded(),
        )
        .is_err(),
        "actual Native request cannot disappear through matching pending metadata"
    );
}

#[test]
fn conditional_recipe_retains_pending_local_callable_latent_demand() {
    let source = SQLITE.replace("pub effect ConnectionOps<R>", "pub effect H {\nop : Unit -> Unit\n}\npub effect ConnectionOps<R>").replace(
        "diagnostic db => resume (ForeignError (perform Native.Connection<R>.diagnostic state))",
        "diagnostic db => {\nlet action = fn(unit) {\nhandle (perform H.op ()) with H {\nop unit => discard\n}\n}\nlet ignored = action ()\nresume (ForeignError (perform Native.Connection<R>.diagnostic state))\n}",
    );
    let fixture = actual_fixture(&source);
    let draft =
        compile(&fixture.fixture, 0).expect("actual source callable with pending cleanup demand");
    crate::core::provider::reconstructed_row_inventory_for_test(
        &draft.fragment,
        &fixture.fixture.resolved,
        &mut TypeWorkBudget::unbounded(),
    )
    .expect("a real callable body establishes its pending latent demand");
}

#[test]
fn conditional_recipe_rejects_wrong_recomputation_owner_at_equal_row() {
    let source = SQLITE.replace("pub effect ConnectionOps<R>", "pub effect H {\nop : Unit -> Unit\n}\npub effect ConnectionOps<R>").replace(
        "diagnostic db => resume (ForeignError (perform Native.Connection<R>.diagnostic state))",
        "diagnostic db => {\nlet ignored = handle (perform H.op ()) with H {\nop unit => discard\n}\nresume (ForeignError (perform Native.Connection<R>.diagnostic state))\n}",
    );
    let fixture = actual_fixture(&source);
    let mut draft = compile(&fixture.fixture, 0).unwrap();
    crate::core::provider::wrong_pending_recomputation_owner_for_test(&mut draft.fragment);
    assert!(
        crate::core::provider::reconstructed_row_inventory_for_test(
            &draft.fragment,
            &fixture.fixture.resolved,
            &mut TypeWorkBudget::unbounded(),
        )
        .is_err(),
        "row equality cannot authenticate another clause's replay owner"
    );
}

#[test]
fn conditional_recipe_rejects_unused_pending_equality() {
    let source = SQLITE.replace("pub effect ConnectionOps<R>", "pub effect H {\nop : Unit -> Unit\n}\npub effect ConnectionOps<R>").replace(
        "diagnostic db => resume (ForeignError (perform Native.Connection<R>.diagnostic state))",
        "diagnostic db => {\nlet ignored = handle (perform H.op ()) with H {\nop unit => discard\n}\nresume (ForeignError (perform Native.Connection<R>.diagnostic state))\n}",
    );
    let fixture = actual_fixture(&source);
    let mut draft = compile(&fixture.fixture, 0).unwrap();
    crate::core::provider::add_unused_pending_equality_for_test(&mut draft.fragment);
    assert!(
        crate::core::provider::reconstructed_row_inventory_for_test(
            &draft.fragment,
            &fixture.fixture.resolved,
            &mut TypeWorkBudget::unbounded(),
        )
        .is_err(),
        "a vacuous scalar equality has no actual conditional graph position"
    );
}

#[test]
fn conditional_recipe_retains_actual_formal_open_demand() {
    let declarations = &SQLITE[..SQLITE.find("pub effect StatementOps").unwrap()];
    let resource_start = SQLITE.find("pub resource Connection<R>").unwrap();
    let resource_end = SQLITE.find("pub resource Statement<S, C>").unwrap();
    let source = format!("{declarations}{}", &SQLITE[resource_start..resource_end])
        .replace("ConnectionOps<R>", "ConnectionOps<R, Rows>")
        .replace("ConnectionProvider<R>", "ConnectionProvider<R, Rows>")
        .replace("Connection<R>", "Connection<R, Rows>")
        .replace("Native.Connection<R, Rows>", "Native.Connection<R>")
        .replace("pub effect ConnectionOps<R, Rows>", "pub effect ConnectionOps<R, Rows : EffectRow>")
        .replace("pub interface ConnectionProvider<R, Rows>", "pub interface ConnectionProvider<R, Rows : EffectRow>")
        .replace("pub resource Connection<R, Rows>", "pub resource Connection<R, Rows : EffectRow>")
        .replace("diagnostic : Connection<R, Rows> -> Error", "diagnostic : (Connection<R, Rows>, Unit -> Unit ! {| Rows}) -> Error")
        .replace("diagnostic db => resume (ForeignError (perform Native.Connection<R>.diagnostic state))", "diagnostic (db, callback) => {\nlet ignored = callback ()\nresume MissingRow\n}")
        .replace("Connection<R, Rows>", "Connection<R, {| Rows}>")
        .replace("ConnectionOps<R, Rows>", "ConnectionOps<R, {| Rows}>")
        .replace("ConnectionProvider<R, Rows>", "ConnectionProvider<R, {| Rows}>");
    let fixture = actual_fixture(&source);
    let draft = compile(&fixture.fixture, 0).expect("actual resource formal EffectRow demand");
    assert!(matches!(
        draft.fragment.direct_demands.tail().unwrap().variable(),
        EffectRowVariable::Rigid(_)
    ));
    crate::core::provider::reconstructed_row_inventory_for_test(
        &draft.fragment,
        &fixture.fixture.resolved,
        &mut TypeWorkBudget::unbounded(),
    )
    .expect("ordinary open D remains a checked input to the retained recipe");
}

#[test]
fn conditional_recipe_retains_actual_method_local_open_equation() {
    let source = SQLITE.replace(
        "diagnostic db => resume (ForeignError (perform Native.Connection<R>.diagnostic state))",
        "diagnostic db => {\nlet relay = fn(callback) {\ncallback ()\n}\nresume MissingRow\n}",
    );
    let fixture = actual_fixture(&source);
    let draft = compile(&fixture.fixture, 0).expect("actual method-local row abstraction");
    assert!(
        crate::core::provider::has_actual_open_equation_for_test(
            &draft.fragment,
            &fixture.fixture.resolved,
            &mut TypeWorkBudget::unbounded(),
        )
        .expect("actual scoped formal demand equation")
    );
    independent_compiled(&fixture.fixture, &draft, &mut TypeWorkBudget::unbounded())
        .expect("method-local ordinary formal rows stay owned by their type abstraction");
}

#[test]
fn conditional_recipe_reconstructs_pending_nested_resume_output() {
    let source = SQLITE.replace("pub effect ConnectionOps<R>", "pub effect H {\nstop : Unit -> Unit\nnext : Unit -> Unit\n}\npub effect ConnectionOps<R>").replace(
        "diagnostic db => resume (ForeignError (perform Native.Connection<R>.diagnostic state))",
        "diagnostic db => {\nlet ignored = handle (perform H.next ()) with H {\nstop unit => discard\nnext unit => resume ()\n}\nresume (ForeignError (perform Native.Connection<R>.diagnostic state))\n}",
    );
    let fixture = actual_fixture(&source);
    let draft =
        compile(&fixture.fixture, 0).expect("nested ordinary resume has shared conditional output");
    crate::core::provider::reconstructed_row_inventory_for_test(
        &draft.fragment,
        &fixture.fixture.resolved,
        &mut TypeWorkBudget::unbounded(),
    )
    .expect("nested owned resume retains its distinct conditional output equation");
    independent_compiled(&fixture.fixture, &draft, &mut TypeWorkBudget::unbounded()).unwrap();
}

#[test]
fn conditional_recipe_owned_admission_survives_defining_context_drop() {
    let source = SQLITE.replace("pub effect ConnectionOps<R>", "pub effect H {\nop : Unit -> Unit\n}\npub effect ConnectionOps<R>").replace(
        "diagnostic db => resume (ForeignError (perform Native.Connection<R>.diagnostic state))",
        "diagnostic db => {\nlet ignored = handle (perform H.op ()) with H {\nop unit => discard\n}\nresume (ForeignError (perform Native.Connection<R>.diagnostic state))\n}",
    );
    let fixture = actual_fixture(&source);
    let draft = compile(&fixture.fixture, 0).unwrap();
    let sources = fixture
        .fixture
        .graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let modules = fixture
        .fixture
        .graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    let owned = draft
        .admit(
            &fixture.fixture.resolved,
            &sources,
            &modules,
            &mut TypeWorkBudget::unbounded(),
        )
        .expect("consuming admission owns independently authenticated conditional code");
    assert!(owned.staged_externals.occurrences.iter().all(|occurrence| {
        occurrence
            .occurrence
            .evidence
            .iter()
            .all(|slot| slot.selection().is_none())
    }));
    drop(sources);
    drop(fixture);
    let links = crate::core::validate::owned_handler_links_for_test(&owned.template);
    assert_eq!(links.len(), 1);
}

#[test]
fn conditional_recipe_owned_selected_statement_survives_helper_context_drop() {
    let source = SQLITE.replace("ForeignError error", "ForeignError (Provider.map error)");
    let fixture = selected_error_fixture(&source);
    let draft = compile(&fixture.fixture, 1).unwrap();
    let sources = fixture
        .fixture
        .graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let modules = fixture
        .fixture
        .graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    let owned = draft
        .admit(
            &fixture.fixture.resolved,
            &sources,
            &modules,
            &mut TypeWorkBudget::unbounded(),
        )
        .expect("selected imported facts transfer with actual Statement roots");
    assert!(owned.staged_externals.occurrences.iter().all(|occurrence| {
        occurrence
            .occurrence
            .evidence
            .iter()
            .all(|slot| slot.selection().is_none())
    }));
    assert_eq!(owned.staged_externals.occurrences.len(), 3);
    drop(sources);
    drop(fixture);
    assert_eq!(
        crate::core::validate::owned_handler_links_for_test(&owned.template).len(),
        3
    );
}

#[test]
fn conditional_recipe_owned_retains_nested_cleanup_and_unknown_outer_capture() {
    let source = SQLITE.replace("pub effect ConnectionOps<R>", "pub effect H {\nop : Unit -> Unit\n}\npub effect J {\nop : Unit -> Unit\n}\npub effect ConnectionOps<R>").replace(
        "diagnostic db => resume (ForeignError (perform Native.Connection<R>.diagnostic state))",
        "diagnostic db => {\nlet ignored = handle (cleanup fn(unit) {\nperform J.op ()\n} {\nperform H.op ()\n}) with H {\nop unit => discard\n}\nresume (ForeignError (perform Native.Connection<R>.diagnostic state))\n}",
    );
    let fixture = actual_fixture(&source);
    let draft = compile(&fixture.fixture, 0).expect("actual nested cleanup source");
    crate::core::provider::reconstructed_row_inventory_for_test(
        &draft.fragment,
        &fixture.fixture.resolved,
        &mut TypeWorkBudget::unbounded(),
    )
    .expect("cleanup row reconstruction");
    let sources = fixture
        .fixture
        .graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let modules = fixture
        .fixture
        .graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    let owned = draft
        .admit(
            &fixture.fixture.resolved,
            &sources,
            &modules,
            &mut TypeWorkBudget::unbounded(),
        )
        .expect("actual cleanup callback and capture topology remain conditional");
    drop(sources);
    drop(fixture);
    assert_eq!(
        crate::core::validate::owned_handler_links_for_test(&owned.template).len(),
        1
    );
}

#[test]
fn conditional_recipe_owned_work_is_exact_prefixed_fresh_and_unpublished() {
    let source = SQLITE.replace("ForeignError error", "ForeignError (Provider.map error)");
    let fixture = selected_error_fixture(&source);
    let sources = fixture
        .fixture
        .graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let modules = fixture
        .fixture
        .graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    let mut measured = TypeWorkBudget::unbounded();
    let owned = compile(&fixture.fixture, 1)
        .unwrap()
        .admit(&fixture.fixture.resolved, &sources, &modules, &mut measured)
        .unwrap();
    let cost = measured.used();
    assert!(cost > 0);
    eprintln!("owned selected handler admission work={cost}");
    drop(owned);
    for prefix in [0, 23] {
        for allowance in [cost - 1, cost] {
            for _ in 0..2 {
                let draft = compile(&fixture.fixture, 1).unwrap();
                assert_selected_slots_empty(&draft);
                let slots = draft
                    .staged_externals
                    .as_ref()
                    .unwrap()
                    .occurrences
                    .iter()
                    .flat_map(|occurrence| occurrence.occurrence.evidence.iter())
                    .map(|slot| slot.retain_unpublished().unwrap())
                    .collect::<Vec<_>>();
                let mut work = TypeWorkBudget::with_limit(prefix + allowance);
                work.charge(prefix).unwrap();
                let result = draft.admit(&fixture.fixture.resolved, &sources, &modules, &mut work);
                if allowance == cost {
                    let owned = result.unwrap();
                    assert_eq!(work.used(), prefix + cost);
                    assert!(owned.staged_externals.occurrences.iter().all(|occurrence| {
                        occurrence
                            .occurrence
                            .evidence
                            .iter()
                            .all(|slot| slot.selection().is_none())
                    }));
                    assert_eq!(
                        crate::core::validate::owned_handler_links_for_test(&owned.template).len(),
                        3
                    );
                } else {
                    match result {
                        Err(LifecycleDraftCheckError::Resource) => {}
                        Err(LifecycleDraftCheckError::Core(error))
                            if error.reason() == crate::core::ValidationReason::Resource => {}
                        _ => panic!("one-short must be Resource, never malformed-input refusal"),
                    }
                }
                assert!(slots.iter().all(|slot| slot.selection().is_none()));
            }
        }
    }
}

#[test]
fn conditional_recipe_retains_actual_pending_exact_removal() {
    let source = SQLITE.replace("pub effect ConnectionOps<R>", "pub effect H {\nop : Unit -> Unit\n}\npub effect J {\nop : Unit -> Unit\n}\npub effect ConnectionOps<R>").replace(
        "diagnostic db => resume (ForeignError (perform Native.Connection<R>.diagnostic state))",
        "diagnostic db => {\nlet ignored = handle ({\nlet stopped = handle (perform J.op ()) with J {\nop unit => discard\n}\nperform H.op ()\n}) with H {\nop unit => resume ()\n}\nresume (ForeignError (perform Native.Connection<R>.diagnostic state))\n}",
    );
    let fixture = actual_fixture(&source);
    let draft = compile(&fixture.fixture, 0).expect("actual pending exact removal source");
    assert!(
        draft
            .fragment
            .pending_rows
            .equations
            .iter()
            .any(|record| matches!(
                record.equation,
                crate::core::provider::PendingRowEquation::Remove(..)
            ))
    );
    independent_compiled(&fixture.fixture, &draft, &mut TypeWorkBudget::unbounded())
        .expect("actual ordinary removal equation retained");
    let mut wrong = compile(&fixture.fixture, 0).unwrap();
    let record = wrong
        .fragment
        .pending_rows
        .equations
        .iter_mut()
        .find(|record| {
            matches!(
                record.equation,
                crate::core::provider::PendingRowEquation::Remove(..)
            )
        })
        .unwrap();
    let crate::core::provider::PendingRowEquation::Remove(_, _, absent) = &mut record.equation
    else {
        unreachable!()
    };
    *absent = !*absent;
    assert!(
        independent_compiled(&fixture.fixture, &wrong, &mut TypeWorkBudget::unbounded()).is_err(),
        "equal scalar removal does not authenticate wrong absence policy"
    );
}

#[test]
fn conditional_recipe_owned_refuses_missing_duplicate_wrong_and_unused_equations() {
    let source = SQLITE.replace("pub effect ConnectionOps<R>", "pub effect H {\nop : Unit -> Unit\n}\npub effect ConnectionOps<R>").replace(
        "diagnostic db => resume (ForeignError (perform Native.Connection<R>.diagnostic state))",
        "diagnostic db => {\nlet ignored = handle (perform H.op ()) with H {\nop unit => discard\n}\nresume (ForeignError (perform Native.Connection<R>.diagnostic state))\n}",
    );
    let fixture = actual_fixture(&source);
    let sources = fixture
        .fixture
        .graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let modules = fixture
        .fixture
        .graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    for mutation in 0..4 {
        let mut draft = compile(&fixture.fixture, 0).unwrap();
        let pending = &mut draft.fragment.pending_rows;
        match mutation {
            0 => {
                pending.equations.remove(0);
            }
            1 => {
                let original = &pending.equations[0];
                let crate::core::provider::PendingRowEquation::Discard(node) = original.equation
                else {
                    panic!("actual discard record")
                };
                pending
                    .equations
                    .push(crate::core::provider::PendingRowRecord {
                        identity: original.identity,
                        source: original.source,
                        equation: crate::core::provider::PendingRowEquation::Discard(node),
                    });
            }
            2 => {
                pending.equations[0].equation = crate::core::provider::PendingRowEquation::Discard(
                    draft.fragment.clauses[0].body(),
                );
            }
            3 => {
                let original = &pending.equations[0];
                let unused = crate::types::InferenceVariableId::new(100000);
                pending
                    .equations
                    .push(crate::core::provider::PendingRowRecord {
                        identity: unused,
                        source: original.source,
                        equation: crate::core::provider::PendingRowEquation::Union(
                            EffectRow::empty(),
                            EffectRow::empty(),
                        ),
                    });
            }
            _ => unreachable!(),
        }
        let result = draft.admit(
            &fixture.fixture.resolved,
            &sources,
            &modules,
            &mut TypeWorkBudget::unbounded(),
        );
        match result {
            Err(LifecycleDraftCheckError::Core(error)) => assert_ne!(
                error.reason(),
                crate::core::ValidationReason::Resource,
                "wrong equation is a semantic refusal"
            ),
            _ => panic!("accepted pending equation mutation {mutation}"),
        }
    }
}

#[test]
fn conditional_recipe_refuses_known_callable_demand_in_a_pure_codomain() {
    let source = SQLITE.replace("pub effect ConnectionOps<R>", "pub effect H {\nop : Unit -> Unit\n}\npub effect J {\nop : Unit -> Unit\n}\npub effect ConnectionOps<R>").replace(
        "diagnostic db => resume (ForeignError (perform Native.Connection<R>.diagnostic state))",
        "diagnostic db => {\nlet action = fn(unit) {\nlet stopped = handle (perform H.op ()) with H {\nop ignored => discard\n}\nperform J.op ()\n}\nresume (ForeignError (perform Native.Connection<R>.diagnostic state))\n}",
    );
    let fixture = actual_fixture(&source);
    let mut draft = compile(&fixture.fixture, 0)
        .expect("actual callable with pending close and direct J demand");
    crate::core::provider::reconstructed_row_inventory_for_test(
        &draft.fragment,
        &fixture.fixture.resolved,
        &mut TypeWorkBudget::unbounded(),
    )
    .expect("actual callable demand relation");
    crate::core::provider::erase_pending_function_latent_for_test(&mut draft.fragment);
    assert!(
        crate::core::provider::reconstructed_row_inventory_for_test(
            &draft.fragment,
            &fixture.fixture.resolved,
            &mut TypeWorkBudget::unbounded()
        )
        .is_err(),
        "unknown capture cannot erase a known direct request from a pure callable codomain"
    );
}

fn fragment(draft: HandlerSourceDraft) -> crate::core::provider::HandlerFragmentDraft {
    let root = draft.clauses[0].body;
    let program = draft.builder.finish(root).unwrap();
    let clauses = draft
        .clauses
        .into_iter()
        .map(|clause| {
            crate::core::effect::EffectClause::new(
                clause.operation,
                clause.resume,
                crate::core::CoreMatchArm::new(
                    clause.pattern.into_inner(),
                    clause.body,
                    clause.origin,
                ),
            )
        })
        .collect::<Vec<_>>()
        .into_boxed_slice();
    crate::core::provider::HandlerFragmentDraft {
        defining_facts: None,
        program,
        template: draft.id,
        handler: draft.handler,
        state: draft.state_parameter,
        hidden: [
            (draft.hidden_answer, Kind::Type),
            (
                match draft.hidden_row {
                    EffectRowVariable::Rigid(id) => id,
                    _ => unreachable!(),
                },
                Kind::EffectRow,
            ),
        ],
        clauses,
        dictionary_parameters: Box::new([]),
        family_requirements: Box::new([]),
        direct_demands: draft.direct_demands,
        pending_rows: draft.pending_rows,
    }
}

fn independent(
    fixture: &Fixture,
    draft: &crate::core::provider::HandlerFragmentDraft,
    work: &mut TypeWorkBudget,
) -> Result<(), crate::core::ValidationError> {
    let sources = fixture
        .graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let modules = fixture
        .graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    crate::core::validate::check_provider_handler_structure(
        draft,
        &fixture.resolved,
        &sources,
        &modules,
        work,
    )
}

fn independent_compiled(
    fixture: &Fixture,
    draft: &CompiledHandlerDraft,
    work: &mut TypeWorkBudget,
) -> Result<(), LifecycleDraftCheckError> {
    let sources = fixture
        .graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let modules = fixture
        .graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    draft.check(&fixture.resolved, &sources, &modules, work)
}

fn compile(fixture: &Fixture, ordinal: usize) -> Result<CompiledHandlerDraft, TypeError> {
    let definition = &fixture.resolved.resources()[ordinal];
    let header = fixture
        .elaborator()
        .check_provider_header(&fixture.resolved, definition)?;
    fixture.elaborator().compile_provider_handler(
        definition,
        &header,
        fixture.resolved.imported_facts(),
    )
}

#[test]
fn independent_actual_connection_fragment_requires_canonical_entry() {
    let fixture = actual_fixture(SQLITE);
    let draft = fragment(check(&fixture.fixture, 0).unwrap());
    let result = independent(&fixture.fixture, &draft, &mut TypeWorkBudget::unbounded());
    assert!(
        result.is_ok(),
        "actual Connection fragment lacks independent entry: {result:?}"
    );
}

#[test]
fn independent_actual_statement_fragment_checks_all_real_clause_roots() {
    let fixture = actual_fixture(SQLITE);
    let draft = fragment(check(&fixture.fixture, 1).unwrap());
    assert_eq!(draft.clauses.len(), 3);
    let result = independent(&fixture.fixture, &draft, &mut TypeWorkBudget::unbounded());
    assert!(
        result.is_ok(),
        "actual Statement fragment lacks independent entry: {result:?}"
    );
}

#[test]
fn independent_actual_newtype_fragment_checks_lowering_and_pattern_roots() {
    let source = SQLITE
        .replace(
            "diagnostic : Connection<R> -> Error",
            "diagnostic : (Connection<R>, SqlText) -> Error",
        )
        .replace("diagnostic db =>", "diagnostic (db, SqlText(bytes)) =>");
    let fixture = actual_fixture(&source);
    let draft = fragment(check(&fixture.fixture, 0).unwrap());
    let result = independent(&fixture.fixture, &draft, &mut TypeWorkBudget::unbounded());
    assert!(
        result.is_ok(),
        "actual newtype fragment lacks independent entry: {result:?}"
    );
}

#[test]
fn independent_actual_nested_fragment_checks_provisional_owner_relations() {
    let source = SQLITE.replace("pub effect ConnectionOps<R>", "pub effect H {\nop : Unit -> Unit\n}\npub effect ConnectionOps<R>").replace(
        "diagnostic db => resume (ForeignError (perform Native.Connection<R>.diagnostic state))",
        "diagnostic db => handle ({\nlet ignored = perform H.op ()\nresume MissingRow\n}) with H {\nop unit => resume ()\n}",
    );
    let fixture = actual_fixture(&source);
    let draft = fragment(check(&fixture.fixture, 0).unwrap());
    let result = independent(&fixture.fixture, &draft, &mut TypeWorkBudget::unbounded());
    assert!(
        result.is_ok(),
        "actual nested fragment lacks provisional structural checking: {result:?}"
    );
    // This does not solve the distinct shared outputs at specialization.
}

#[test]
fn independent_nested_handler_cannot_interpret_registered_native_effect() {
    let source = SQLITE
        .replace("pub effect ConnectionOps<R>", "pub effect H<R> {\nopen : Native.OpenConfig -> Native.Acquire<Unit, Native.OpenError>\ndiagnostic : Unit -> Native.Error\nclose : Unit -> Native.Finish<Unit, Native.CloseError>\n}\npub effect ConnectionOps<R>")
        .replace(
            "diagnostic db => resume (ForeignError (perform Native.Connection<R>.diagnostic state))",
            "diagnostic db => handle ({\nlet ignored = perform H<R>.open Native.InMemory\nlet borrowed = perform Native.Connection<R>.diagnostic state\nresume MissingRow\n}) with H<R> {\nopen cfg => resume (Native.Refused (Native.OpenFailure Native.ConversionFailure))\ndiagnostic ignored_state => resume Native.ConversionFailure\nclose ignored_state => resume Native.Consumed\n}",
        );
    let fixture = actual_fixture(&source);
    let mut draft = fragment(check(&fixture.fixture, 0).unwrap());
    independent(&fixture.fixture, &draft, &mut TypeWorkBudget::unbounded())
        .expect("actual ordinary nested handler baseline");
    assert!(!draft.direct_demands.is_empty());
    crate::core::provider::mutate_handler_for_test(
        &mut draft,
        &fixture.fixture.resolved.resources()[0],
        crate::core::provider::HandlerMutation::NestedForeignHandler,
    );
    let result = independent(&fixture.fixture, &draft, &mut TypeWorkBudget::unbounded());
    eprintln!("coherent nested Native interpretation result: {result:?}");
    let mut compiled = compile(&fixture.fixture, 0).unwrap();
    independent_compiled(
        &fixture.fixture,
        &compiled,
        &mut TypeWorkBudget::unbounded(),
    )
    .expect("actual compiled ordinary nested handler baseline");
    assert_selected_slots_empty(&compiled);
    crate::core::provider::mutate_handler_for_test(
        &mut compiled.fragment,
        &fixture.fixture.resolved.resources()[0],
        crate::core::provider::HandlerMutation::NestedForeignHandler,
    );
    let mut measured = TypeWorkBudget::unbounded();
    let compiled_result = independent_compiled(&fixture.fixture, &compiled, &mut measured);
    eprintln!("compiled coherent nested Native interpretation result: {compiled_result:?}");
    assert_selected_slots_empty(&compiled);
    let error = result.expect_err("accepted an ordinary nested Native interpreter");
    assert_eq!(
        error.reason(),
        crate::core::ValidationReason::ResourceEscape
    );
    assert_eq!(error.node(), Some(draft.clauses[0].body()));
    let LifecycleDraftCheckError::Core(error) =
        compiled_result.expect_err("accepted a compiled ordinary nested Native interpreter")
    else {
        panic!("native target must be refused by independent Core validation");
    };
    assert_eq!(
        error.reason(),
        crate::core::ValidationReason::ResourceEscape
    );
    assert_eq!(error.node(), Some(compiled.fragment.clauses[0].body()));
    let refusal_cost = measured.used();
    eprintln!("registered native Handler refusal cost={refusal_cost}");
    for prefix in [0, 19] {
        for allowance in [refusal_cost - 1, refusal_cost] {
            for _ in 0..2 {
                let mut work = TypeWorkBudget::with_limit(prefix + allowance);
                work.charge(prefix).unwrap();
                let error = independent_compiled(&fixture.fixture, &compiled, &mut work)
                    .expect_err("registered native Handler must never be admitted");
                match error {
                    LifecycleDraftCheckError::Resource => assert!(allowance < refusal_cost),
                    LifecycleDraftCheckError::Core(error) => assert_eq!(
                        error.reason(),
                        if allowance == refusal_cost {
                            crate::core::ValidationReason::ResourceEscape
                        } else {
                            crate::core::ValidationReason::Resource
                        }
                    ),
                    LifecycleDraftCheckError::InvalidEntry => panic!("wrong refusal boundary"),
                }
                assert_selected_slots_empty(&compiled);
            }
        }
    }
}

#[test]
fn canonical_registered_effect_and_state_lookups_charge_empty_and_wide_inventories() {
    use crate::foreign::{
        ForeignEffectDeclaration, ForeignManifest, ForeignManifestSchema,
        ForeignOperationDeclaration, ForeignResultRelation, ForeignTypeDeclaration,
    };
    const MODULES: usize = 64;
    const EFFECTS: usize = 8;
    let mut manifests = vec![sqlite_manifest(ForeignRegistrationId::new(991)).unwrap()];
    let mut imports = String::new();
    for index in 0..MODULES {
        let path = format!("@foreign.lookup{index}");
        imports.push_str(&format!("import {path} as Lookup{index}\n"));
        manifests.push(
            ForeignManifest::new(
                path,
                ForeignRegistrationId::new(1000 + index as u64),
                ForeignManifestSchema {
                    foundation: None,
                    types: vec![ForeignTypeDeclaration {
                        name: "State".into(),
                        parameters: vec!["R".into()],
                        category: crate::foreign::ForeignTypeCategory::State,
                        constructors: vec![],
                    }],
                    effects: (0..EFFECTS)
                        .map(|effect| ForeignEffectDeclaration {
                            name: format!("Probe{effect}"),
                            parameters: vec!["R".into()],
                            operations: vec![ForeignOperationDeclaration {
                                name: "read".into(),
                                signature: "State<R> -> Int".into(),
                                role: ForeignOperationRole::Borrow,
                                owned_identity_position: 0,
                                state_operands: vec![vec![]],
                                retained_arguments: vec![],
                                result: ForeignResultRelation::Independent,
                            }],
                        })
                        .collect(),
                    state_access: None,
                },
            )
            .unwrap(),
        );
    }
    let wide = Fixture::with_registrations(
        &format!("{imports}{SOURCE}"),
        ForeignRegistrations::new(manifests).unwrap(),
    );
    let narrow = Fixture::new(SOURCE);
    let empty = crate::resolved::ResolvedRegistry::new(Vec::new(), Vec::new());
    let wide_registry = wide.elaborator().registry;
    let narrow_registry = narrow.elaborator().registry;
    let ordinary = wide.resolved.resources()[0].provided.instance.effect();
    let last_native = *wide_registry
        .foreign_modules()
        .last()
        .unwrap()
        .effects
        .last()
        .unwrap();
    assert_eq!(wide_registry.foreign_modules().count(), MODULES + 1);
    let run = |registry: &crate::resolved::ResolvedRegistry, target, work: &mut TypeWorkBudget| {
        crate::core::validate::registered_foreign_effect_with_charge(registry, target, |cells| {
            work.charge(cells)
        })
    };
    let mut measured = TypeWorkBudget::unbounded();
    assert!(!run(&empty, ordinary, &mut measured).unwrap());
    assert_eq!(measured.used(), 0);
    assert!(!run(&narrow_registry, ordinary, &mut measured).unwrap());
    assert_eq!(measured.used(), 3); // One canonical SQLite module, two effects.
    let expected = MODULES * (1 + EFFECTS) + 3;
    for (target, membership) in [(ordinary, false), (last_native, true)] {
        let mut measured = TypeWorkBudget::unbounded();
        assert_eq!(
            run(&wide_registry, target, &mut measured).unwrap(),
            membership
        );
        assert_eq!(measured.used(), expected);
        for prefix in [0, 23] {
            for allowance in [expected - 1, expected] {
                for _ in 0..2 {
                    let mut work = TypeWorkBudget::with_limit(prefix + allowance);
                    work.charge(prefix).unwrap();
                    let result = run(&wide_registry, target, &mut work);
                    if allowance == expected {
                        assert_eq!(result.unwrap(), membership);
                        assert_eq!(work.used(), prefix + expected);
                    } else {
                        assert_eq!(result, Err(()));
                    }
                }
            }
        }
    }
    fn state_run<'a>(
        registry: &'a crate::resolved::ResolvedRegistry,
        target: crate::types::NominalTypeId,
        work: &mut TypeWorkBudget,
    ) -> Result<Option<&'a crate::foreign::ForeignStateFact>, ()> {
        crate::core::validate::registered_foreign_state_with_charge(registry, target, |cells| {
            work.charge(cells)
        })
    }
    let narrow_state = narrow.resolved.resources()[0]
        .state
        .ty
        .outer_nominal()
        .unwrap();
    let wide_state = wide.resolved.resources()[0]
        .state
        .ty
        .outer_nominal()
        .unwrap();
    let missing_state = wide.resolved.resources()[0].family;
    let mut measured = TypeWorkBudget::unbounded();
    assert!(
        state_run(&empty, wide_state, &mut measured)
            .unwrap()
            .is_none()
    );
    assert_eq!(measured.used(), 0);
    let narrow_fact = state_run(&narrow_registry, narrow_state, &mut measured)
        .unwrap()
        .unwrap();
    assert!(std::ptr::eq(
        narrow_fact,
        narrow_registry.foreign_state(narrow_state).unwrap()
    ));
    assert_eq!(measured.used(), 3);
    let state_expected = MODULES * 2 + 3;
    for (target, membership) in [(missing_state, false), (wide_state, true)] {
        let mut measured = TypeWorkBudget::unbounded();
        let fact = state_run(&wide_registry, target, &mut measured).unwrap();
        assert_eq!(fact.is_some(), membership);
        if let Some(fact) = fact {
            assert!(std::ptr::eq(
                fact,
                wide_registry.foreign_state(target).unwrap()
            ));
        }
        assert_eq!(measured.used(), state_expected);
        for prefix in [0, 23] {
            for allowance in [state_expected - 1, state_expected] {
                for _ in 0..2 {
                    let mut work = TypeWorkBudget::with_limit(prefix + allowance);
                    work.charge(prefix).unwrap();
                    let result = state_run(&wide_registry, target, &mut work);
                    if allowance == state_expected {
                        assert_eq!(result.unwrap().is_some(), membership);
                        assert_eq!(work.used(), prefix + state_expected);
                    } else {
                        assert!(matches!(result, Err(())));
                    }
                }
            }
        }
    }
    let source_draft = check(&wide, 0).unwrap();
    assert!(source_draft.occurrences.iter().all(|occurrence| {
        occurrence
            .occurrence
            .evidence
            .iter()
            .all(|slot| slot.selection().is_none())
    }));
    let draft = fragment(source_draft);
    let mut measured = TypeWorkBudget::unbounded();
    independent(&wide, &draft, &mut measured).unwrap();
    let cost = measured.used();
    for prefix in [0, 23] {
        for allowance in [cost - 1, cost] {
            for _ in 0..2 {
                let mut work = TypeWorkBudget::with_limit(prefix + allowance);
                work.charge(prefix).unwrap();
                let result = independent(&wide, &draft, &mut work);
                if allowance == cost {
                    result.unwrap();
                    assert_eq!(work.used(), prefix + cost);
                } else {
                    assert_eq!(
                        result.unwrap_err().reason(),
                        crate::core::ValidationReason::Resource
                    );
                }
            }
        }
    }
    eprintln!(
        "registered effect lookup empty=0 narrow=3 wide={expected}; state lookup empty=0 narrow=3 wide={state_expected}; wide actual entry={cost}"
    );
}

#[test]
fn independent_actual_current_state_access_requires_operand_provenance() {
    let source = SQLITE.replace(
        "perform Native.Connection<R>.diagnostic state",
        "perform Native.Connection<R>.diagnostic (Provider.state_of db)",
    );
    let fixture = actual_fixture(&source);
    let draft = fragment(check(&fixture.fixture, 0).unwrap());
    let result = independent(&fixture.fixture, &draft, &mut TypeWorkBudget::unbounded());
    assert!(
        result.is_ok(),
        "actual Current StateAccess lacks independent operand provenance: {result:?}"
    );
}

#[test]
fn independent_current_state_access_survives_a_direct_source_alias() {
    let source = SQLITE.replace("diagnostic db => resume (ForeignError (perform Native.Connection<R>.diagnostic state))",
        "diagnostic db => {\nlet alias = Provider.state_of db\nresume (ForeignError (perform Native.Connection<R>.diagnostic alias))\n}");
    let fixture = actual_fixture(&source);
    let draft = fragment(check(&fixture.fixture, 0).unwrap());
    let result = independent(&fixture.fixture, &draft, &mut TypeWorkBudget::unbounded());
    assert!(
        result.is_ok(),
        "lawful direct state alias lacks source-root correspondence: {result:?}"
    );
}

#[test]
fn independent_actual_pure_error_helper_requires_import_correspondence() {
    let source = SQLITE.replace(
        "ForeignError (perform Native.Connection<R>.diagnostic state)",
        "ForeignError (Provider.map (perform Native.Connection<R>.diagnostic state))",
    );
    let fixture = external::HelperFixture::new(
        &source.replace("import provider as Provider", "import helper as Provider"),
        &format!(
            "import @foreign.sqlite as Native\n{PROVIDER}\npub map : Native.Error -> Native.Error\nmap error = error\n"
        ),
    );
    let draft = fragment(check(&fixture.fixture, 0).unwrap());
    let result = independent(&fixture.fixture, &draft, &mut TypeWorkBudget::unbounded());
    assert!(
        result.is_ok(),
        "actual error helper lacks independent import correspondence: {result:?}"
    );
}

#[test]
fn independent_fragment_rejects_canonical_metadata_scope_and_row_mutations() {
    use crate::core::provider::{HandlerMutation as M, mutate_handler_for_test};
    let fixture = actual_fixture(SQLITE);
    let f = &fixture.fixture;
    for mutation in [
        M::OperationOwner,
        M::Coverage,
        M::PatternDomain,
        M::PatternOrigin,
        M::BinderReason,
        M::BinderCause,
        M::BodyReason,
        M::BodyCause,
        M::HiddenKind,
        M::HiddenCollision,
        M::HiddenFormal,
        M::StateType,
        M::ResumeOwner,
        M::ResumeHandler,
        M::ResumeAvailable,
        M::ResumeResult,
        M::ResumeRowErasure,
        M::DirectDemandErasure,
        M::HiddenRowPosition,
    ] {
        let mut draft = fragment(check(f, 0).unwrap());
        mutate_handler_for_test(&mut draft, &f.resolved.resources()[0], mutation);
        let result = independent(f, &draft, &mut TypeWorkBudget::unbounded());
        assert!(result.is_err(), "accepted {mutation:?}");
    }
    for mutation in [M::DuplicateRoot, M::SwapRoots] {
        let mut draft = fragment(check(f, 1).unwrap());
        mutate_handler_for_test(&mut draft, &f.resolved.resources()[1], mutation);
        assert!(
            independent(f, &draft, &mut TypeWorkBudget::unbounded()).is_err(),
            "accepted {mutation:?}"
        );
    }
}

#[test]
fn independent_binding_root_rejects_wrong_generated_reason_and_related_cause() {
    use crate::core::provider::{HandlerMutation as M, mutate_handler_for_test};
    let source = SQLITE.replace("diagnostic db => resume (ForeignError (perform Native.Connection<R>.diagnostic state))",
        "diagnostic db => {\nlet alias = Provider.state_of db\nresume (ForeignError (perform Native.Connection<R>.diagnostic alias))\n}");
    let fixture = actual_fixture(&source);
    for mutation in [M::BodyReason, M::BodyCause] {
        let mut draft = fragment(check(&fixture.fixture, 0).unwrap());
        mutate_handler_for_test(
            &mut draft,
            &fixture.fixture.resolved.resources()[0],
            mutation,
        );
        assert!(
            independent(&fixture.fixture, &draft, &mut TypeWorkBudget::unbounded()).is_err(),
            "accepted {mutation:?}"
        );
    }
}

#[test]
fn independent_actual_state_access_mutations_cannot_claim_operand_lineage() {
    use crate::core::provider::{AccessMutation as M, mutate_state_access};
    let source = SQLITE.replace(
        "perform Native.Connection<R>.diagnostic state",
        "perform Native.Connection<R>.diagnostic (Provider.state_of db)",
    );
    let fixture = actual_fixture(&source);
    for mutation in [
        M::Method,
        M::Definition,
        M::Arguments,
        M::Operand,
        M::Result,
    ] {
        let mut draft = fragment(check(&fixture.fixture, 0).unwrap());
        mutate_state_access(&mut draft.program, mutation);
        assert!(independent(&fixture.fixture, &draft, &mut TypeWorkBudget::unbounded()).is_err());
    }
}

#[test]
fn independent_fragment_work_is_cumulative_exact_and_retryable() {
    let fixture = actual_fixture(SQLITE);
    let f = &fixture.fixture;
    for ordinal in [0, 1] {
        let draft = fragment(check(f, ordinal).unwrap());
        let mut work = TypeWorkBudget::unbounded();
        independent(f, &draft, &mut work).unwrap();
        let cost = work.used();
        eprintln!("handler independent ordinal={ordinal} cost={cost}");
        for prefix in [0, 17] {
            for allowance in [cost - 1, cost] {
                for _ in 0..2 {
                    let mut work = TypeWorkBudget::with_limit(prefix + allowance);
                    work.charge(prefix).unwrap();
                    let result = independent(f, &draft, &mut work);
                    if allowance == cost {
                        result.unwrap();
                        assert_eq!(work.used(), prefix + cost);
                    } else {
                        assert_eq!(
                            result.unwrap_err().reason(),
                            crate::core::ValidationReason::Resource
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn independent_same_typed_import_cannot_replace_the_actual_source_helper() {
    let source = SQLITE.replace(
        "ForeignError (perform Native.Connection<R>.diagnostic state)",
        "ForeignError (Provider.map (perform Native.Connection<R>.diagnostic state))",
    );
    let fixture = external::HelperFixture::new(
        &source.replace("import provider as Provider", "import helper as Provider"),
        &format!(
            "import @foreign.sqlite as Native\n{PROVIDER}\npub map : Native.Error -> Native.Error\nmap error = error\npub other : Native.Error -> Native.Error\nother error = error\n"
        ),
    );
    let mut draft = fragment(check(&fixture.fixture, 0).unwrap());
    crate::core::provider::mutate_external_for_test(
        &mut draft.program,
        fixture.globals["map"],
        crate::core::provider::ExternalMutation::Binder(fixture.globals["other"]),
    );
    let result = independent(&fixture.fixture, &draft, &mut TypeWorkBudget::unbounded());
    assert!(
        result.is_err(),
        "same-typed alternate import acquired the original occurrence authority"
    );
}

#[test]
fn independent_wide_source_inventory_and_clause_roots_charge_exactly() {
    let operations = (0..63)
        .map(|index| format!("read{index} : Connection<R> -> Native.Error\n"))
        .collect::<String>();
    let methods = (0..63)
        .map(|index| format!("read{index} : Connection<R> -> Native.Error ! {{Ops<R>}}\n"))
        .collect::<String>();
    let clauses = (0..63)
        .map(|index| {
            format!("read{index} db => resume (perform Native.Connection<R>.diagnostic state)\n")
        })
        .collect::<String>();
    let source = SOURCE
        .replace(
            "pub interface Reader<R> {\n",
            &format!("pub interface Reader<R> {{\n{methods}"),
        )
        .replace(
            "pub effect Ops<R> {\n",
            &format!("pub effect Ops<R> {{\n{operations}"),
        )
        .replace(
            "handlers state {\n",
            &format!("handlers state {{\n{clauses}"),
        );
    let fixture = Fixture::new(&source);
    let draft = fragment(check(&fixture, 0).unwrap());
    assert_eq!(draft.clauses.len(), 64);
    let extras = (0..64)
        .map(|index| crate::source::SourceFile::new(format!("extra-{index}.ash"), "").unwrap())
        .collect::<Vec<_>>();
    let mut sources = fixture
        .graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    sources.extend(extras.iter());
    let mut modules = fixture
        .graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    modules.extend(extras.iter().enumerate().map(|(index, source)| {
        (
            crate::module::ModuleId::new(1000 + index as u32),
            source.id(),
        )
    }));
    let check = |work: &mut TypeWorkBudget| {
        crate::core::validate::check_provider_handler_structure(
            &draft,
            &fixture.resolved,
            &sources,
            &modules,
            work,
        )
    };
    let mut work = TypeWorkBudget::unbounded();
    check(&mut work).unwrap();
    let cost = work.used();
    eprintln!(
        "wide handler roots=64 sources={} modules={} cost={cost}",
        sources.len(),
        modules.len()
    );
    for prefix in [0, 19] {
        for allowance in [cost - 1, cost] {
            for _ in 0..2 {
                let mut work = TypeWorkBudget::with_limit(prefix + allowance);
                work.charge(prefix).unwrap();
                let result = check(&mut work);
                if allowance == cost {
                    result.unwrap();
                    assert_eq!(work.used(), prefix + cost);
                } else {
                    assert_eq!(
                        result.unwrap_err().reason(),
                        crate::core::ValidationReason::Resource
                    );
                }
            }
        }
    }
}

#[test]
fn independent_actual_statement_state_access_keeps_tuple_operand_paths() {
    let source = SQLITE
        .replace(
            "Native.Statement<S, C>.bind_int (state, index, value)",
            "Native.Statement<S, C>.bind_int (Provider.state_of stmt, index, value)",
        )
        .replace(
            "Native.Statement<S, C>.step state",
            "Native.Statement<S, C>.step (Provider.state_of stmt)",
        )
        .replace(
            "Native.Statement<S, C>.column_int (state, index)",
            "Native.Statement<S, C>.column_int (Provider.state_of stmt, index)",
        );
    let fixture = actual_fixture(&source);
    let draft = fragment(check(&fixture.fixture, 1).unwrap());
    let result = independent(&fixture.fixture, &draft, &mut TypeWorkBudget::unbounded());
    assert!(
        result.is_ok(),
        "actual Statement tuple/current lineage lacks admission: {result:?}"
    );
}

#[test]
fn independent_import_inventory_covers_aliases_and_unused_stored_values() {
    for called in [false, true] {
        let body = if called {
            "resume (ForeignError (mapper (perform Native.Connection<R>.diagnostic state)))"
        } else {
            "resume (ForeignError (perform Native.Connection<R>.diagnostic state))"
        };
        let source = SQLITE.replace("diagnostic db => resume (ForeignError (perform Native.Connection<R>.diagnostic state))",
            &format!("diagnostic db => {{\nlet mapper = Provider.map\n{body}\n}}"));
        let fixture = external::HelperFixture::new(
            &source.replace("import provider as Provider", "import helper as Provider"),
            &format!(
                "import @foreign.sqlite as Native\n{PROVIDER}\npub map : Native.Error -> Native.Error\nmap error = error\npub other : Native.Error -> Native.Error\nother error = error\n"
            ),
        );
        let mut draft = fragment(check(&fixture.fixture, 0).unwrap());
        let result = independent(&fixture.fixture, &draft, &mut TypeWorkBudget::unbounded());
        assert!(
            result.is_ok(),
            "actual helper alias called={called}: {result:?}"
        );
        crate::core::provider::mutate_external_for_test(
            &mut draft.program,
            fixture.globals["map"],
            crate::core::provider::ExternalMutation::Binder(fixture.globals["other"]),
        );
        assert!(
            independent(&fixture.fixture, &draft, &mut TypeWorkBudget::unbounded()).is_err(),
            "stored alternate helper called={called} acquired occurrence authority"
        );
    }
}

#[test]
fn independent_actual_constrained_error_helper_requires_selected_abi() {
    let source = SQLITE.replace(
        "ForeignError (perform Native.Connection<R>.diagnostic state)",
        "ForeignError (Provider.map (perform Native.Connection<R>.diagnostic state))",
    );
    let helper = format!(
        "import @foreign.sqlite as Native\n{PROVIDER}\npub interface Pass<A> {{\npass : A -> A\n}}\npub impl Pass<Native.Error> {{\npass value = value\n}}\npub map<A> : A -> A where Pass<A>\nmap value = pass value\n"
    );
    let fixture = external::HelperFixture::new(
        &source.replace(
            "import provider as Provider",
            "import helper as Provider\nimport helper (impl Pass)",
        ),
        &helper,
    );
    let source = check(&fixture.fixture, 0).unwrap();
    assert_eq!(source.occurrences.len(), 1);
    assert!(source.occurrences.iter().all(|occurrence| {
        occurrence
            .occurrence
            .evidence
            .iter()
            .all(|slot| slot.selection().is_none())
    }));
    drop(source);
    let draft = compile(&fixture.fixture, 0).unwrap();
    assert!(
        draft
            .staged_externals
            .as_ref()
            .unwrap()
            .occurrences
            .iter()
            .all(|occurrence| occurrence
                .occurrence
                .evidence
                .iter()
                .all(|slot| slot.selection().is_none()))
    );
    let result = independent_compiled(&fixture.fixture, &draft, &mut TypeWorkBudget::unbounded());
    assert!(
        result.is_ok(),
        "actual constrained handler helper lacks selected ABI proof: {result:?}"
    );
}

#[test]
fn independent_compiled_real_handler_forest_preserves_state_and_pattern_arenas() {
    let fixture = actual_fixture(SQLITE);
    for ordinal in [0, 1] {
        let draft = compile(&fixture.fixture, ordinal).unwrap();
        let result =
            independent_compiled(&fixture.fixture, &draft, &mut TypeWorkBudget::unbounded());
        assert!(
            result.is_ok(),
            "actual compiled forest ordinal={ordinal}: {result:?}"
        );
    }
    let source = SQLITE
        .replace(
            "diagnostic : Connection<R> -> Error",
            "diagnostic : (Connection<R>, SqlText) -> Error",
        )
        .replace("diagnostic db =>", "diagnostic (db, SqlText(bytes)) =>");
    let fixture = actual_fixture(&source);
    let draft = compile(&fixture.fixture, 0).unwrap();
    let result = independent_compiled(&fixture.fixture, &draft, &mut TypeWorkBudget::unbounded());
    assert!(result.is_ok(), "actual compiled newtype forest: {result:?}");
}

fn selected_error_fixture(source: &str) -> external::HelperFixture {
    let helper = format!(
        concat!(
            "import @foreign.sqlite as Native\n{}\n",
            "pub interface Pass<A> {{\nfirst : A -> A\nsecond : A -> A\n}}\n",
            "pub interface Stamp<A> {{\nstamp : (A, Int) -> A\n}}\n",
            "pub impl Pass<Native.Error> {{\nfirst value = value\nsecond value = value\n}}\n",
            "pub impl Stamp<Native.Error> {{\nstamp (value, ignored) = value\n}}\n",
            "pub map<A> : A -> A where Pass<A>, Stamp<A>\nmap value = stamp ((second (first value), 7))\n",
            "pub other<A> : A -> A where Pass<A>, Stamp<A>\nother value = stamp ((second (first value), 7))\n",
        ),
        PROVIDER
    );
    external::HelperFixture::new(
        &source.replace(
            "import provider as Provider",
            "import helper as Provider\nimport helper (impl Pass, impl Stamp)",
        ),
        &helper,
    )
}

fn assert_selected_slots_empty(draft: &CompiledHandlerDraft) {
    assert!(
        draft
            .staged_externals
            .as_ref()
            .unwrap()
            .occurrences
            .iter()
            .all(|occurrence| occurrence
                .occurrence
                .evidence
                .iter()
                .all(|slot| slot.selection().is_none()))
    );
}

#[test]
fn selected_error_mapper_covers_all_statement_roots_and_ordered_methods() {
    let source = SQLITE.replace("ForeignError error", "ForeignError (Provider.map error)");
    let fixture = selected_error_fixture(&source);
    let draft = compile(&fixture.fixture, 1).unwrap();
    assert_eq!(
        draft.staged_externals.as_ref().unwrap().occurrences.len(),
        3
    );
    assert!(
        draft
            .staged_externals
            .as_ref()
            .unwrap()
            .occurrences
            .iter()
            .all(|occurrence| occurrence.occurrence.evidence.len() == 2)
    );
    independent_compiled(&fixture.fixture, &draft, &mut TypeWorkBudget::unbounded()).unwrap();
    assert_selected_slots_empty(&draft);
}

#[test]
fn selected_error_mapper_in_later_clause_forwarder_and_stored_value_keeps_forest() {
    for called in [false, true] {
        let body = if called { "forward error" } else { "error" };
        let source = SQLITE.replace("Native.Err(error) => resume (Err (ForeignError error))",
            &format!("Native.Err(error) => {{\nlet stored : Native.Error -> Native.Error = Provider.map\nlet forward : Native.Error -> Native.Error = fn(value) {{\nProvider.map value\n}}\nresume (Err (ForeignError ({body})))\n}}"));
        let fixture = selected_error_fixture(&source);
        let draft = compile(&fixture.fixture, 1).unwrap();
        assert_eq!(
            draft.staged_externals.as_ref().unwrap().occurrences.len(),
            4
        );
        let result =
            independent_compiled(&fixture.fixture, &draft, &mut TypeWorkBudget::unbounded());
        assert!(
            result.is_ok(),
            "later clause forwarding/stored called={called}: {result:?}"
        );
        assert_selected_slots_empty(&draft);
    }
}

#[test]
fn malformed_original_handler_coordinates_refuse_without_publication_and_retry() {
    let source = SQLITE.replace("ForeignError error", "ForeignError (Provider.map error)");
    let fixture = selected_error_fixture(&source);
    let f = &fixture.fixture;
    let definition = &f.resolved.resources()[1];
    let original_slots = definition
        .handlers
        .iter()
        .flat_map(|clause| {
            crate::elaborate::provider::external::all_provider_expression_occurrences(
                &clause.body,
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap()
        })
        .flat_map(|occurrence| occurrence.evidence.iter())
        .map(|slot| slot.retain_unpublished().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(original_slots.len(), 2 * STATEMENT_METHODS.len());
    let mut original_ids = original_slots
        .iter()
        .map(|slot| slot.storage_id())
        .collect::<Vec<_>>();
    original_ids.sort_unstable();
    let header = f
        .elaborator()
        .check_provider_header(&f.resolved, definition)
        .unwrap();
    for mutation in 0..4 {
        let mut compiler = f.elaborator();
        let prepared = compiler
            .prepare_provider_handler_source(definition, &header, f.resolved.imported_facts())
            .unwrap();
        assert_eq!(
            prepared
                .clauses
                .iter()
                .map(|clause| (clause.operation, clause.resume))
                .collect::<Vec<_>>(),
            statement_links(f)
        );
        assert_statement_occurrences(f, &compiler.provider_global_occurrences, [1; 3]);
        let mut prepared_ids = compiler
            .provider_global_occurrences
            .iter()
            .flat_map(|occurrence| occurrence.occurrence.evidence.iter())
            .map(|slot| slot.storage_id())
            .collect::<Vec<_>>();
        prepared_ids.sort_unstable();
        assert_eq!(
            prepared_ids, original_ids,
            "private preparation retains the exact original source slots"
        );
        let publication = compiler.prepare_evidence_publication().unwrap();
        compiler
            .type_work
            .charge(prepared.clauses.len().checked_mul(2).unwrap())
            .unwrap();
        let mut roots = Vec::new();
        roots.try_reserve_exact(prepared.clauses.len()).unwrap();
        roots.extend(prepared.clauses.iter().map(|clause| clause.body));
        let mut patterns = Vec::new();
        patterns.try_reserve_exact(prepared.clauses.len()).unwrap();
        patterns.extend(prepared.clauses.iter().map(|clause| &*clause.pattern));
        let pending_rows = compiler
            .cleanup_rows
            .take_provider_pending(&compiler.builder, roots[0], &mut compiler.type_work)
            .unwrap();
        let first = compiler.provider_global_occurrences[0].node.unwrap();
        let second = compiler.provider_global_occurrences[1].node.unwrap();
        assert_ne!(first, second);
        assert!(
            compiler
                .provider_global_occurrences
                .iter()
                .all(|occurrence| occurrence.node == occurrence.source_node)
        );
        match mutation {
            0 => compiler.provider_global_occurrences[0].node = None,
            1 => compiler.provider_global_occurrences[0].source_node = None,
            2 => compiler.provider_global_occurrences[0].source_node = Some(second),
            3 => {
                compiler.provider_global_occurrences[1].node = Some(first);
                compiler.provider_global_occurrences[1].source_node = Some(first);
            }
            _ => unreachable!(),
        }
        let result = compiler.lower_provider_source_forest_with_pending(
            &roots,
            f.resolved.imported_facts(),
            publication,
            &OwnerReplacementBuffer::new(),
            &[&prepared.state_parameter],
            &patterns,
            pending_rows,
        );
        assert!(
            matches!(
                result,
                Err(TypeError::Internal(ElaborationFailure::InvalidState))
            ),
            "original coordinate mutation {mutation} must refuse malformed private metadata"
        );
        assert!(original_slots.iter().all(|slot| slot.selection().is_none()));
        drop(compiler);
        let retry = compile(f, 1)
            .expect("fresh compiler retries the unchanged original three-root fixture");
        assert_statement_occurrences(
            f,
            &retry.staged_externals.as_ref().unwrap().occurrences,
            [1; 3],
        );
        assert_eq!(
            retry
                .fragment
                .clauses
                .iter()
                .map(|clause| (clause.operation(), clause.resume()))
                .collect::<Vec<_>>(),
            statement_links(f)
        );
        independent_compiled(f, &retry, &mut TypeWorkBudget::unbounded()).unwrap();
        assert_selected_slots_empty(&retry);
        assert!(original_slots.iter().all(|slot| slot.selection().is_none()));
    }
}

#[test]
fn selected_handler_occurrence_dictionary_and_catalog_mutations_are_refused() {
    use crate::core::dialect::MethodEvidenceCatalogMutationForTest as M;
    let source = SQLITE.replace("ForeignError error", "ForeignError (Provider.map error)");
    let fixture = selected_error_fixture(&source);
    for mutation in 0..9 {
        let mut draft = compile(&fixture.fixture, 1).unwrap();
        let staged = draft.staged_externals.as_mut().unwrap();
        let occurrence = &mut staged.occurrences[1];
        match mutation {
            0 => crate::core::provider::swap_dictionary_methods_for_test(
                &mut draft.fragment.program,
                occurrence.node.unwrap(),
            ),
            1 => crate::core::provider::wrong_dictionary_producer_for_test(
                &mut draft.fragment.program,
                occurrence.node.unwrap(),
            ),
            2 => occurrence.occurrence.evidence.swap(0, 1),
            3 => discard_type_iteratively(std::mem::replace(
                &mut occurrence.arguments.0[0],
                Type::Int,
            )),
            4 => staged
                .publication
                .relocate_types(
                    |_, _| Ok(Type::Int),
                    &mut InterfaceConstraintBudget::with_limit(usize::MAX),
                    &mut TypeWorkBudget::unbounded(),
                )
                .unwrap(),
            5 => {
                staged.occurrences.pop();
            }
            6 => occurrence.node = Some(draft.fragment.clauses[0].body()),
            7 => {
                occurrence.occurrence.term =
                    crate::resolved::ResolvedTermName::Global(fixture.globals["other"])
            }
            8 => occurrence.occurrence.spelling = "other".to_owned(),
            _ => unreachable!(),
        }
        let result =
            independent_compiled(&fixture.fixture, &draft, &mut TypeWorkBudget::unbounded());
        assert!(
            result.is_err(),
            "accepted selected occurrence mutation {mutation}"
        );
        assert_selected_slots_empty(&draft);
    }
    {
        let mutation = M::WrongMethodScheme;
        let mut draft = compile(&fixture.fixture, 1).unwrap();
        crate::core::provider::mutate_method_catalog_for_test(
            &mut draft.fragment.program,
            mutation,
        );
        assert!(
            independent_compiled(&fixture.fixture, &draft, &mut TypeWorkBudget::unbounded())
                .is_err(),
            "accepted handler catalog {mutation:?}"
        );
        assert_selected_slots_empty(&draft);
    }
}

#[test]
fn selected_handler_compile_and_check_work_are_cumulative_and_unpublished() {
    let source = SQLITE.replace("ForeignError error", "ForeignError (Provider.map error)");
    let fixture = selected_error_fixture(&source);
    let f = &fixture.fixture;
    let definition = &f.resolved.resources()[1];
    let header = f
        .elaborator()
        .check_provider_header(&f.resolved, definition)
        .unwrap();
    let mut compiler = f.elaborator();
    compiler.type_work = TypeWorkBudget::unbounded();
    let draft = compiler
        .compile_provider_handler(definition, &header, f.resolved.imported_facts())
        .unwrap();
    let compile_cost = draft.compile_work;
    let mut measured = TypeWorkBudget::unbounded();
    independent_compiled(f, &draft, &mut measured).unwrap();
    let check_cost = measured.used();
    eprintln!(
        "selected handler forest roots=3 occurrences=3 compile={compile_cost} check={check_cost}; builder/constraint ledgers separate"
    );
    for prefix in [0, 23] {
        for allowance in [compile_cost - 1, compile_cost] {
            for _ in 0..2 {
                let mut compiler = f.elaborator();
                compiler.type_work = TypeWorkBudget::with_limit(prefix + allowance);
                compiler.type_work.charge(prefix).unwrap();
                let result = compiler.compile_provider_handler(
                    definition,
                    &header,
                    f.resolved.imported_facts(),
                );
                if allowance == compile_cost {
                    let retry = result.unwrap();
                    assert_eq!(retry.compile_work, prefix + compile_cost);
                    assert_selected_slots_empty(&retry);
                } else {
                    assert!(
                        matches!(
                            result,
                            Err(TypeError::Internal(
                                ElaborationFailure::TypeResourceExhausted
                            ))
                        ),
                        "unexpected short compilation outcome"
                    );
                }
            }
        }
        for allowance in [check_cost - 1, check_cost] {
            for _ in 0..2 {
                let mut work = TypeWorkBudget::with_limit(prefix + allowance);
                work.charge(prefix).unwrap();
                let result = independent_compiled(f, &draft, &mut work);
                if allowance == check_cost {
                    result.unwrap();
                    assert_eq!(work.used(), prefix + check_cost);
                } else {
                    match result.unwrap_err() {
                        LifecycleDraftCheckError::Resource => {}
                        LifecycleDraftCheckError::Core(error) => {
                            assert_eq!(error.reason(), crate::core::ValidationReason::Resource)
                        }
                        LifecycleDraftCheckError::InvalidEntry => {
                            panic!("one-short refused entry rather than work")
                        }
                    }
                }
                assert_selected_slots_empty(&draft);
            }
        }
    }
    // Retained source selections remain empty across successful and refused
    // compilation; this check does not publish a descriptor or template.
    let source = check(f, 1).unwrap();
    assert!(source.occurrences.iter().all(|o| {
        o.occurrence
            .evidence
            .iter()
            .all(|slot| slot.selection().is_none())
    }));
}

#[test]
fn selected_handler_check_uses_retained_helper_facts_after_file_deletion() {
    let source = SQLITE.replace("ForeignError error", "ForeignError (Provider.map error)");
    let fixture = selected_error_fixture(&source);
    let draft = compile(&fixture.fixture, 1).unwrap();
    let helper = fixture
        .fixture
        .graph
        .modules()
        .iter()
        .find(|module| module.source().display_path().ends_with("/helper.ash"))
        .unwrap();
    fs::remove_file(helper.source().display_path()).unwrap();
    independent_compiled(&fixture.fixture, &draft, &mut TypeWorkBudget::unbounded()).unwrap();
    assert_selected_slots_empty(&draft);
}

#[test]
fn selected_nested_error_prerequisites_in_all_roots_authenticate_catalog() {
    use crate::core::dialect::MethodEvidenceCatalogMutationForTest as M;
    let source = SQLITE.replace("ForeignError error", "ForeignError (match Provider.normalize (Provider.Box (Provider.Box error)) {\nProvider.Box(Provider.Box(mapped)) => mapped\n})")
        .replace("import provider as Provider", "import helper as Provider\nimport helper (impl Pass, impl Stamp)");
    let helper = external::nested_constrained_helper()
        .replace("Native.OpenConfig", "Native.Error")
        .replace(
            "import @foreign.sqlite as Native\n",
            &format!("import @foreign.sqlite as Native\n{PROVIDER}\n"),
        );
    let fixture = external::HelperFixture::new(&source, &helper);
    let draft = compile(&fixture.fixture, 1).unwrap();
    assert_eq!(
        draft.staged_externals.as_ref().unwrap().occurrences.len(),
        3
    );
    let result = independent_compiled(&fixture.fixture, &draft, &mut TypeWorkBudget::unbounded());
    assert!(
        result.is_ok(),
        "actual nested Error prerequisites in all roots: {result:?}"
    );
    assert_selected_slots_empty(&draft);
    for mutation in [
        M::WrongRequirementPosition,
        M::WrongMethodPosition,
        M::WrongMethodScheme,
        M::WrongCanonicalMethodParameter,
        M::WrongAdapterBinder,
        M::WrongAdapterSourceParameter,
        M::WrongOwnerSourceParameter,
        M::WrongHeadCount,
        M::WrongHeadArgument,
        M::MissingPrerequisite,
        M::WrongPrerequisiteProducer,
        M::MissingExpectation,
        M::ExtraExpectation,
    ] {
        let mut draft = compile(&fixture.fixture, 1).unwrap();
        crate::core::provider::mutate_method_catalog_for_test(
            &mut draft.fragment.program,
            mutation,
        );
        assert!(
            independent_compiled(&fixture.fixture, &draft, &mut TypeWorkBudget::unbounded())
                .is_err(),
            "accepted nested handler catalog {mutation:?}"
        );
        assert_selected_slots_empty(&draft);
    }
}

#[test]
fn selected_handler_forest_failure_and_retry_dispose_on_provider_stack() {
    let source = SQLITE.replace("ForeignError error", "ForeignError (Provider.map error)");
    let fixture = selected_error_fixture(&source);
    let draft = compile(&fixture.fixture, 1).unwrap();
    let source = SQLITE
        .replace(
            "diagnostic : Connection<R> -> Error",
            "diagnostic : (Connection<R>, SqlText) -> Error",
        )
        .replace("diagnostic db =>", "diagnostic (db, SqlText(bytes)) =>");
    let newtype = actual_fixture(&source);
    let pattern_draft = compile(&newtype.fixture, 0).unwrap();
    // Fixture parsing/import checking use the normal test stack. This probes
    // only the admitted private proof, late refusal and retained owners.
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(move || {
            let mut measured = TypeWorkBudget::unbounded();
            independent_compiled(&fixture.fixture, &draft, &mut measured).unwrap();
            for _ in 0..2 {
                let error = independent_compiled(
                    &fixture.fixture,
                    &draft,
                    &mut TypeWorkBudget::with_limit(measured.used() - 1),
                )
                .unwrap_err();
                match error {
                    LifecycleDraftCheckError::Resource => {}
                    LifecycleDraftCheckError::Core(error) => {
                        assert_eq!(error.reason(), crate::core::ValidationReason::Resource)
                    }
                    LifecycleDraftCheckError::InvalidEntry => {
                        panic!("stack test refused entry rather than work")
                    }
                }
                independent_compiled(
                    &fixture.fixture,
                    &draft,
                    &mut TypeWorkBudget::with_limit(measured.used()),
                )
                .unwrap();
                assert_selected_slots_empty(&draft);
            }
            drop(draft);
            independent_compiled(
                &newtype.fixture,
                &pattern_draft,
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap();
            drop(pattern_draft);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn contextual_handler_registry_mirror_rejects_coherent_annotation_provenance() {
    let fixture = actual_fixture(SQLITE);
    let f = &fixture.fixture;
    let mut draft = compile(f, 0).unwrap();
    let mut altered = f
        .resolved
        .registry()
        .provider_template_view(
            f.resolved.imported_facts(),
            &mut TypeWorkBudget::unbounded(),
        )
        .unwrap();
    altered
        .mutate_provider_annotation_origin_for_test(Origin::Source(f.resolved.resources()[0].span));
    crate::core::provider::replace_external_registry_for_test(
        &mut draft.fragment.program,
        Arc::new(altered),
    );
    assert!(independent_compiled(f, &draft, &mut TypeWorkBudget::unbounded()).is_err());
}

#[test]
fn contextual_wide_imported_nominal_source_sort_has_exact_work() {
    let types = (0..64)
        .map(|index| format!("pub type Extra{index} = Extra{index}(Unit)\n"))
        .collect::<String>();
    let operands = (0..64)
        .map(|index| format!(", Provider.Extra{index}"))
        .collect::<String>();
    let binders = (0..64)
        .map(|index| format!(", ignored{index}"))
        .collect::<String>();
    let source = SQLITE
        .replace(
            "diagnostic : Connection<R> -> Error",
            &format!("diagnostic : (Connection<R>{operands}) -> Error"),
        )
        .replace("diagnostic db =>", &format!("diagnostic (db{binders}) =>"));
    let fixture = external::HelperFixture::new(
        &source.replace("import provider as Provider", "import helper as Provider"),
        &format!("{PROVIDER}\n{types}"),
    );
    let draft = compile(&fixture.fixture, 0).unwrap();
    let mut measured = TypeWorkBudget::unbounded();
    independent_compiled(&fixture.fixture, &draft, &mut measured).unwrap();
    let cost = measured.used();
    eprintln!("contextual handler imported nominals=64 plus canonical data, cost={cost}");
    for prefix in [0, 29] {
        for allowance in [cost - 1, cost] {
            for _ in 0..2 {
                let mut work = TypeWorkBudget::with_limit(prefix + allowance);
                work.charge(prefix).unwrap();
                let result = independent_compiled(&fixture.fixture, &draft, &mut work);
                if allowance == cost {
                    result.unwrap();
                    assert_eq!(work.used(), prefix + cost);
                } else {
                    match result.unwrap_err() {
                        LifecycleDraftCheckError::Resource => {}
                        LifecycleDraftCheckError::Core(error) => {
                            assert_eq!(error.reason(), crate::core::ValidationReason::Resource)
                        }
                        LifecycleDraftCheckError::InvalidEntry => {
                            panic!("sort budget refused entry rather than work")
                        }
                    }
                }
            }
        }
    }
}
