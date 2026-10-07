// Include inside value::tests after producer_integration_tests.rs. This is a
// synthetic original-Graph regression, not a claim of source qualification.

#[test]
fn symbolic_returned_root_keeps_both_full_specializations_and_original_typecall() {
    use crate::types::{EffectRow, Kind, KindedArgument};
    use super::typed_environment::TypeOrigin;

    // F<A,R> returns one literal G whose ordinary body calls the result of a
    // captured Evidence(H<A,R>). Both uses below share that exact G/q/body.
    let mut fixture = producer_connected_fixture(2);
    let top = &fixture.levels[0];
    let child = &fixture.levels[1];
    let top_returned = top.returned;
    let ordinary_call = top.body;
    let nested_typecall = top.application.expect("nonleaf typed application");
    let child_factory = child.factory;
    let child_returned = child.returned;
    let int_application = fixture.root_application;
    // Root(G) receives only G's declared captures. The nested TypeCall and
    // its Evidence dictionary need these original global inputs at that root;
    // being captured by the enclosing factory alone does not supply them.
    let globals: HashSet<_> = fixture.graph.globals.iter().map(|(binder, _)| *binder).collect();
    let factory_globals: Vec<_> = match &fixture.graph.expressions[top.factory] {
        Expr::Function { captures, .. } => captures.iter().copied()
            .filter(|capture| globals.contains(capture)).collect(),
        _ => panic!("fixture factory"),
    };
    let Expr::Function { captures, .. } = &mut fixture.graph.expressions[top_returned]
        else { panic!("fixture returned function"); };
    for capture in factory_globals {
        if !captures.contains(&capture) { captures.push(capture); }
    }
    let bool_application = producer_test_application(
        &mut fixture.graph,
        top.global,
        vec![(top.binders[0], Kind::Type), (top.binders[1], Kind::EffectRow)],
        vec![
            (Vec::new(), KindedArgument::TypeArg(Type::Bool)),
            (Vec::new(), KindedArgument::RowArg(EffectRow::empty())),
        ],
    );
    let argument_ports = |application| match &fixture.graph.expressions[application] {
        Expr::Call { arguments, type_application: true, .. } => arguments.clone(),
        _ => panic!("fixture typed application"),
    };
    let int_arguments = argument_ports(int_application);
    let bool_arguments = argument_ports(bool_application);

    let mut work = TypeWorkBudget::unbounded();
    // The same fully typed Graph must exercise this original nonzero path
    // without connected zero entries as well; this checks fixture readiness.
    let original_qcodes: Vec<_> = fixture.levels.iter().filter_map(|level| level.application)
        .chain([int_application, bool_application]).collect();
    let reference = producer_test_start(&fixture.graph, &original_qcodes, &mut work);
    let reference_root = reference.roots[&ordinary_call];
    assert!(reference.contexts.paths.iter().any(|path| matches!(path,
        ContextPath::Step { parent, transition: Transition::Invoke(application, function), .. }
            if *parent == reference_root && *application == nested_typecall
                && *function == child_factory)),
        "the same Graph's original protocol must have a ready nonzero typed invocation");
    let mut analysis = fixture.graph.start(&mut work).unwrap();
    let int_output = analysis.slot(int_application, 0, &mut work).unwrap();
    let bool_output = analysis.slot(bool_application, 0, &mut work).unwrap();
    analysis.close(&mut work).unwrap();
    for application in [int_application, bool_application] {
        assert!(super::source_producer::coverage_for_test(&analysis, application).0,
            "both distinct typed uses must retain the connected local producer");
    }
    // The two full static arguments are deliberately indistinguishable in
    // resource atoms. Passing this check alone cannot authorize substitution.
    for arguments in [&int_arguments, &bool_arguments] {
        for &argument in arguments {
            let port = analysis.indices[&(argument, 0)];
            assert_eq!(analysis.slots[port].atoms, vec![Atom::Free]);
        }
    }
    for output in [int_output, bool_output] {
        assert!(analysis.slots[output].atoms.iter().any(|atom|
            matches!(atom, Atom::FramedClosure(function, _) if *function == top_returned)),
            "both original zero applications must exercise the connected producer");
    }

    let symbolic_root = analysis.roots[&ordinary_call];
    assert!(matches!(analysis.contexts.paths[symbolic_root],
        ContextPath::Step { parent: 0, transition: Transition::Root(function), .. }
            if function == top_returned));
    analysis.slot(ordinary_call, symbolic_root, &mut work).unwrap();
    analysis.close(&mut work).unwrap();

    let (callee, actuals) = match &fixture.graph.expressions[nested_typecall] {
        Expr::Call { function, arguments, type_application: true, .. } => (*function, arguments),
        _ => panic!("nested typed application"),
    };
    let callee = *analysis.indices.get(&(callee, symbolic_root))
        .expect("original root callee input");
    assert!(analysis.slots[callee].atoms.iter().any(|atom| matches!(atom,
        Atom::Closure(function, _) | Atom::FramedClosure(function, _)
            if *function == child_factory)), "the child factory must be ready at Root(G)");
    for &actual in actuals {
        let actual = *analysis.indices.get(&(actual, symbolic_root))
            .expect("original root typed actual");
        assert!(!analysis.slots[actual].atoms.is_empty(),
            "every original Type/Row actual must be ready at Root(G)");
    }

    // Locate an already-created invocation: constructing this coordinate in
    // the test would hide loss of the mandatory nonzero original protocol.
    let original_type_invoke = analysis.contexts.paths.iter().position(|path|
        matches!(path, ContextPath::Step { parent,
            transition: Transition::Invoke(application, function), .. }
            if *parent == symbolic_root && *application == nested_typecall
                && *function == child_factory))
        .expect("q at Root(G) must retain its original typed invocation");
    let q_at_root = analysis.indices[&(nested_typecall, symbolic_root)];
    let mut original_constructor = false;
    for atom in &analysis.slots[q_at_root].atoms {
        match *atom {
            Atom::Closure(function, creation) => {
                original_constructor |= function == child_returned
                    && creation == original_type_invoke;
            }
            Atom::FramedClosure(function, frame) if function == child_returned => {
                original_constructor |= analysis.frames.first().unwrap().arena
                    .original_creation(frame, &mut work).unwrap() == Some(original_type_invoke);
            }
            _ => {}
        }
    }
    assert!(original_constructor,
        "the original local constructor branch survives beside projected feeds");

    // q = H<A,R> returns the ordinary child G: the ordinary consumer invokes
    // that returned code, not the TypeAbstraction H itself. Same-code capture
    // feeds meet here without giving the symbolic root one static type origin.
    let ordinary_invoke = analysis.contexts.paths.iter().position(|path|
        matches!(path, ContextPath::Step { parent,
            transition: Transition::Invoke(application, function), .. }
            if *parent == symbolic_root && *application == ordinary_call
                && *function == child_returned))
        .expect("ordinary child consumer");
    let (origins, _) = analysis.resolved_type_origins(ordinary_invoke, None, &mut work).unwrap();
    let types = &analysis.frames.first().expect("connected frame owner").types;
    let mut int = false;
    let mut boolean = false;
    for origin in origins {
        let TypeOrigin::Normalized(id) = origin else { continue; };
        let environment = types.normalized(id).unwrap();
        if environment.factory() != child_factory { continue; }
        for binding in environment.bindings() {
            match binding.argument() {
                KindedArgument::TypeArg(Type::Int) => int = true,
                KindedArgument::TypeArg(Type::Bool) => boolean = true,
                _ => {}
            }
        }
    }
    assert!(int && boolean,
        "Root(G) must transport both complete Int and Bool origins downstream");
    // Saved symbolic q@0 and unresolved original branches are legitimate;
    // neither an exact-two-origin assertion nor a guessed symbolic origin is
    // a substitute for retaining both demanded concrete specializations.
}
