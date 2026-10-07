// Include inside value::tests. Synthetic original Graph with complete, kinded
// producer witnesses; this is executable experiment evidence, not Ash authority.

struct ProducerConnectedLevel {
    factory: usize,
    returned: usize,
    body: usize,
    global: usize,
    formals: [usize; 2],
    binders: [crate::types::TypeVariableId; 2],
    dictionary: Vec<usize>,
    application: Option<usize>,
    requirement: crate::interface::RequirementId,
}

struct ProducerConnectedFixture {
    graph: Graph,
    levels: Vec<ProducerConnectedLevel>,
    root_application: usize,
    outer_evidence: usize,
    ordinary_call: usize,
    method_functions: Vec<usize>,
}

fn producer_test_expr(graph: &mut Graph, expression: Expr) -> usize {
    let id = graph.expressions.len();
    graph.expressions.push(expression);
    graph.sources.push(graph.sources[0]);
    id
}

fn producer_test_application(
    graph: &mut Graph,
    factory_global: usize,
    header: Vec<(crate::types::TypeVariableId, crate::types::Kind)>,
    actuals: Vec<(Vec<usize>, crate::types::KindedArgument)>,
) -> usize {
    let function = producer_test_expr(graph, Expr::Alias(factory_global));
    let mut arguments = Vec::new();
    let mut witnesses = Vec::new();
    for (inputs, argument) in actuals {
        let port = producer_test_expr(graph, Expr::Merge(inputs));
        arguments.push(port);
        witnesses.push(ProducerArgument {
            port,
            value: crate::types::IterativeArgumentOwner::new(argument),
        });
    }
    let application = producer_test_expr(graph, Expr::Call {
        function, arguments, scalar: false, type_application: true,
    });
    graph.install_producer(application, ProducerWitness::Application {
        function, binders: header, arguments: witnesses,
    }, &mut TypeWorkBudget::unbounded()).unwrap();
    application
}

// depth counts nonleaf links: every link adds a genuine captured Evidence of
// a typed child and an ordinary consumer of its returned callable.
fn producer_connected_fixture(depth: usize) -> ProducerConnectedFixture {
    use crate::interface::{InterfaceId, MethodId, RequirementId, RequirementOwner};
    use crate::module::ModuleId;
    use crate::types::{EffectRow, EffectRowVariable, Kind, KindedArgument, TypeVariableId};

    let mut graph = graph(vec![Expr::Scalar]);
    let module = ModuleId::new(55_312);
    let methods: Vec<_> = (0..9).map(|i| MethodId::new(InterfaceId::new(module, 0), i)).collect();
    let mut method_functions = Vec::new();
    let mut method_globals = Vec::new();
    let mut method_values = Vec::new();
    for _ in 0..9 {
        let parameter = producer_test_expr(&mut graph, Expr::Slot);
        let body = producer_test_expr(&mut graph, Expr::Scalar);
        let function = producer_test_expr(&mut graph, Expr::Function {
            parameters: vec![parameter], body, captures: Vec::new(),
        });
        graph.targets.insert(function, body);
        let global = producer_test_expr(&mut graph, Expr::Slot);
        graph.globals.push((global, function));
        method_functions.push(function);
        method_globals.push(global);
        method_values.push(producer_test_expr(&mut graph, Expr::Alias(global)));
    }
    let mut levels: Vec<ProducerConnectedLevel> = Vec::new();
    for i in 0..=depth {
        let local = u32::try_from(i).unwrap();
        let binders = [TypeVariableId::generated(55_312 + 2 * local),
            TypeVariableId::generated(55_313 + 2 * local)];
        let formals = [producer_test_expr(&mut graph, Expr::Slot),
            producer_test_expr(&mut graph, Expr::Slot)];
        graph.metadata.insert(formals[0], binders[0]);
        graph.metadata.insert(formals[1], binders[1]);
        let requirement = RequirementId::new(
            RequirementOwner::Global(BinderId::resolved(module, 100 + local)), 0);
        let mut dictionary = Vec::new();
        for &method in &methods {
            let slot = producer_test_expr(&mut graph, Expr::Slot);
            graph.evidence.push(((requirement, method), slot));
            dictionary.push(slot);
        }
        let parameter = producer_test_expr(&mut graph, Expr::Slot);
        let (application, nested_evidence) = if let Some(child) = levels.last() {
            let q = producer_test_application(&mut graph, child.global,
                vec![(child.binders[0], Kind::Type), (child.binders[1], Kind::EffectRow)],
                vec![
                    (vec![formals[0]], KindedArgument::TypeArg(Type::Variable(binders[0]))),
                    (vec![formals[1]], KindedArgument::RowArg(EffectRow::open(
                        EffectRowVariable::Rigid(binders[1]), Box::new([])))),
                ]);
            let bindings = methods.iter().zip(&method_values)
                .map(|(&method, &value)| (child.requirement, method, value)).collect();
            let evidence = producer_test_expr(&mut graph, Expr::Evidence { value: q, bindings });
            (Some(q), Some(evidence))
        } else { (None, None) };
        let body = if let Some(evidence) = nested_evidence {
            let call = producer_test_expr(&mut graph, Expr::Call {
                function: evidence, arguments: vec![parameter], scalar: false,
                type_application: false,
            });
            graph.positions.insert(call, call);
            call
        } else { producer_test_expr(&mut graph, Expr::Alias(dictionary[0])) };
        let mut captures = formals.to_vec();
        captures.extend_from_slice(&dictionary);
        captures.extend(nested_evidence);
        let returned = producer_test_expr(&mut graph, Expr::Function {
            parameters: vec![parameter], body, captures,
        });
        graph.targets.insert(returned, body);
        let mut factory_captures = method_globals.clone();
        if let Some(child) = levels.last() { factory_captures.push(child.global); }
        // This nonSlot capture retains the independent saved e@0 channel.
        factory_captures.extend(nested_evidence);
        let factory = producer_test_expr(&mut graph, Expr::Function {
            parameters: formals.to_vec(), body: returned, captures: factory_captures,
        });
        graph.targets.insert(factory, returned);
        graph.install_producer(factory, ProducerWitness::Abstraction {
            binders: vec![(binders[0], Kind::Type), (binders[1], Kind::EffectRow)],
            formals: formals.to_vec(),
        }, &mut TypeWorkBudget::unbounded()).unwrap();
        let global = producer_test_expr(&mut graph, Expr::Slot);
        graph.globals.push((global, factory));
        levels.push(ProducerConnectedLevel { factory, returned, body, global, formals,
            binders, dictionary, application, requirement });
    }
    levels.reverse();
    let top = &levels[0];
    let root_application = producer_test_application(&mut graph, top.global,
        vec![(top.binders[0], Kind::Type), (top.binders[1], Kind::EffectRow)],
        vec![(Vec::new(), KindedArgument::TypeArg(Type::Int)),
            (Vec::new(), KindedArgument::RowArg(EffectRow::empty()))]);
    let bindings = methods.iter().zip(&method_values)
        .map(|(&method, &value)| (top.requirement, method, value)).collect();
    let outer_evidence = producer_test_expr(&mut graph, Expr::Evidence {
        value: root_application, bindings,
    });
    let argument = producer_test_expr(&mut graph, Expr::Scalar);
    let ordinary_call = producer_test_expr(&mut graph, Expr::Call {
        function: outer_evidence, arguments: vec![argument], scalar: false,
        type_application: false,
    });
    graph.positions.insert(ordinary_call, ordinary_call);
    let output = producer_test_expr(&mut graph, Expr::Slot);
    graph.globals.push((output, ordinary_call));
    ProducerConnectedFixture { graph, levels, root_application, outer_evidence,
        ordinary_call, method_functions }
}

// Graph::start's original initialization, split before close so the reference
// arm can choose Original without removing typed witnesses or the v3 consumer.
fn producer_test_start<'g>(graph: &'g Graph, original: &[usize],
    budget: &mut TypeWorkBudget) -> Analysis<'g>
{
    let mut analysis = Analysis::new(graph, budget).unwrap();
    for &(binder, value) in &graph.globals {
        let initializer = analysis.slot(value, 0, budget).unwrap();
        let binder = analysis.slot(binder, 0, budget).unwrap();
        analysis.edge(binder, initializer, budget).unwrap();
    }
    for (id, expression) in graph.expressions.iter().enumerate() {
        if let Expr::Function { parameters, body, captures } = expression {
            let context = analysis.context(0, Transition::Root(id), budget).unwrap();
            analysis.roots.insert(*body, context);
            for &parameter in parameters {
                let slot = analysis.slot(parameter, context, budget).unwrap();
                analysis.atom(slot, Atom::Unknown, budget).unwrap();
            }
            for &capture in captures {
                let source = analysis.slot(capture, 0, budget).unwrap();
                let target = analysis.slot(capture, context, budget).unwrap();
                analysis.edge(target, source, budget).unwrap();
            }
            analysis.slot(*body, context, budget).unwrap();
        }
    }
    if !original.is_empty() {
        super::source_producer::original_entries_for_test(&mut analysis, original, budget).unwrap();
    }
    analysis.close(budget).unwrap();
    analysis
}

fn producer_test_callable_codes(analysis: &Analysis<'_>, expression: usize, context: usize)
    -> Vec<usize>
{
    let slot = analysis.indices[&(expression, context)];
    let mut codes: Vec<_> = analysis.slots[slot].atoms.iter().filter_map(|atom| match atom {
        Atom::Closure(function, _) | Atom::FramedClosure(function, _) => Some(*function),
        _ => None,
    }).collect();
    codes.sort_unstable();
    codes.dedup();
    codes
}

#[test]
fn connected_nonleaf_producer_preserves_original_evidence_tuple_roots_and_control() {
    for depth in [1, 3] {
        let fixture = producer_connected_fixture(depth);
        let mut applications = vec![(fixture.root_application, fixture.levels[0].factory)];
        for pair in fixture.levels.windows(2) {
            applications.push((pair[0].application.unwrap(), pair[1].factory));
        }
        let qcodes: Vec<_> = applications.iter().map(|&(q, _)| q).collect();
        let mut work = TypeWorkBudget::unbounded();
        let mut candidate = producer_test_start(&fixture.graph, &[], &mut work);
        let mut reference = producer_test_start(&fixture.graph, &qcodes, &mut work);
        let mut reference_invoke = reference.contexts.extensions[&(0,
            Transition::Invoke(fixture.root_application, fixture.levels[0].factory))];
        for pair in fixture.levels.windows(2) {
            reference_invoke = *reference.contexts.extensions.get(&(reference_invoke,
                Transition::Invoke(pair[0].application.unwrap(), pair[1].factory)))
                .expect("original nonleaf constructor chain must materialize every raw Invoke");
        }
        for &(q, factory) in &applications {
            let (installed, raw, evidence) = super::source_producer::coverage_for_test(&candidate, q);
            assert!(installed, "a fallback is not connected producer coverage: q={q}");
            assert!(raw >= depth + 1 && evidence >= depth,
                "the growing family must build nonleaf Raw and virtual Evidence scopes");
            assert!(!candidate.contexts.extensions.contains_key(&(0, Transition::Invoke(q, factory))),
                "installed q@0 must avoid its original raw Invoke");
            // A nested q@0 can remain pending because its formal metadata
            // heads are Empty. The reference chain above exercises its actual
            // nonzero constructor occurrence, rather than inventing readiness.
            let Expr::Call { function, arguments, type_application: true, .. } =
                &fixture.graph.expressions[q] else { panic!("typed fixture") };
            assert_eq!(arguments.len(), 2, "full ordered Type/Row metadata tuple");
            let output = candidate.indices[&(q, 0)];
            let watches = candidate.watched_pairs();
            for input in std::iter::once(function).chain(arguments.iter()) {
                assert!(watches.contains(&(candidate.indices[&(*input, 0)], output)),
                    "own readiness retains callee and every actual input");
            }
        }
        let top = &fixture.levels[0];
        for analysis in [&mut candidate, &mut reference] {
            let e0 = analysis.contexts.extensions[&(0, Transition::Call(fixture.outer_evidence))];
            let evidence = analysis.indices[&(fixture.outer_evidence, 0)];
            assert!(analysis.slots[evidence].atoms.contains(&Atom::Closure(top.returned, e0)),
                "actual Evidence retains the original closure and original Call creation");
            analysis.provider_independent_slot(evidence, true, &mut work).unwrap();
            for (&capture, &method) in top.dictionary.iter().zip(&fixture.method_functions) {
                assert_eq!(producer_test_callable_codes(analysis, capture, e0), vec![method],
                    "all nine dictionary components retain their exact target");
                if let Some(frames) = analysis.frames.first() {
                    assert!(frames.arena.lookup_head(super::deferred_frame::OriginalPort {
                        expression: capture, context: e0,
                    }, &mut work).unwrap().is_none(),
                        "original Evidence slots stay concrete under the no-head policy");
                }
            }
            for &formal in &top.formals {
                let slot = analysis.indices[&(formal, e0)];
                assert!(analysis.slots[slot].atoms.contains(&Atom::Free));
            }
            for level in &fixture.levels {
                let factory_root = analysis.roots[&level.returned];
                assert!(matches!(analysis.contexts.paths[factory_root],
                    ContextPath::Step { parent: 0, transition: Transition::Root(owner), .. }
                        if owner == level.factory));
                let returned_root = analysis.roots[&level.body];
                assert!(matches!(analysis.contexts.paths[returned_root],
                    ContextPath::Step { parent: 0, transition: Transition::Root(owner), .. }
                        if owner == level.returned));
                for &formal in &level.formals {
                    let slot = analysis.indices[&(formal, returned_root)];
                    assert!(analysis.slots[slot].atoms.contains(&Atom::Free),
                        "activated constructors retain K/root capture feeds");
                }
            }
        }
        let expected = reference.calls(fixture.ordinary_call, 0, &mut work).unwrap();
        let actual = candidate.calls(fixture.ordinary_call, 0, &mut work).unwrap();
        assert_eq!(actual.unknown, expected.unknown);
        assert_eq!(actual.returns, expected.returns);
        let mut expected_codes: Vec<_> = expected.targets.iter().map(|&(code, _)| code).collect();
        let mut actual_codes: Vec<_> = actual.targets.iter().map(|&(code, _)| code).collect();
        expected_codes.sort_unstable(); expected_codes.dedup();
        actual_codes.sort_unstable(); actual_codes.dedup();
        assert_eq!(actual_codes, expected_codes);
        assert_eq!(actual_codes, vec![top.body], "original ordinary control reaches G's body");
        let ordinary = candidate.contexts.extensions[&(0,
            Transition::Invoke(fixture.ordinary_call, top.returned))];
        let nested = candidate.calls(top.body, ordinary, &mut work).unwrap();
        assert!(nested.targets.iter().any(|&(code, _)| code == fixture.levels[1].body),
            "the retained ordinary body consumes the nonleaf captured Evidence");
    }
}
