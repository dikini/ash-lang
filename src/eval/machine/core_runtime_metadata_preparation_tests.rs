//! Bounded C3.4 executable ledger evidence for actual activation-map preparation.
//! Internal Machine configurations; no claim of full source reachability.
use super::tests::{effect_program, integer, resource_node};
use super::*;
use crate::types::{Type, TypeVariableId};

fn fixture() -> (ValidatedEffectProgram, NodeId, NodeId) {
    let program = effect_program(
        "import @builtin.cell as Cell\nmain : Unit -> Int\nmain () = resource cell<R> c = 41 {\nCell.read c\n}\n",
    );
    let resource = resource_node(&program);
    let mut pending = vec![program.root()];
    let request = loop {
        let node = pending.pop().expect("literal request exists");
        let kind = &program.node(node).unwrap().kind;
        if matches!(kind, EffectExprKind::Operation(EffectOperation::Request(request)) if request.operation().operation() == 0)
        {
            break node;
        }
        pending.extend((0..kind.child_count()).filter_map(|index| kind.child_at(index)));
    };
    (program, resource, request)
}

fn shadowed_environment(identity: TypeVariableId) -> Environment {
    let mut environment = Environment::new();
    // Provenance is this actual prior map acquisition, not a supplied result.
    environment.instantiation = environment
        .instantiation
        .acquire(
            identity,
            ActivationKey(4),
            &mut TypeWorkBudget::unbounded(),
            None,
        )
        .unwrap();
    environment
}

fn details(failure: RuntimeFailure) -> super::super::ResourceFailure {
    match failure {
        RuntimeFailure::Report(report) => report.primary.resource().expect("resource details"),
        _ => panic!("expected structured metadata refusal: {failure:?}"),
    }
}

#[test]
fn activation_acquire_computed_exact_shadow_and_instruction_diagnostics() {
    let (program, resource, _) = fixture();
    let identity = match &program.node(resource).unwrap().kind {
        EffectExprKind::Operation(EffectOperation::Resource(scope)) => scope.acquisition.identity,
        _ => unreachable!(),
    };
    // One retained activation leaf: admission(n+1), n clone visits,
    // one parameter visit and one empty-caller activation clone = 2n+3.
    let old_entries = 1;
    let computed = 2 * old_entries + 3;
    for (budget, expected_request) in [(2, None), (3, Some(1)), (computed - 1, None)] {
        let mut machine = Machine::new_effect(&program);
        machine.next_activation = 7;
        machine.instantiation_work = TypeWorkBudget::with_limit(budget);
        let failure = machine
            .acquire_resource(resource, shadowed_environment(identity), integer("41"))
            .unwrap_err();
        let detail = details(failure);
        assert_eq!(detail.cause, ResourceFailureCause::WorkBudgetExhausted);
        assert_eq!(detail.phase, RuntimePhase::Acquisition);
        assert_eq!(detail.resource, RuntimeResource::WorkUnits);
        assert_eq!(detail.requested, expected_request);
        assert_eq!(detail.available, Some(0));
        assert_eq!(machine.instantiation_work.used(), budget);
        assert_eq!(machine.next_activation, 7);
        assert_eq!(machine.live_resources, 0);
        assert!(machine.frames.is_empty());
        assert!(machine.effect_trace.as_ref().unwrap().is_empty());
    }
    let mut machine = Machine::new_effect(&program);
    machine.next_activation = 7;
    machine.instantiation_work = TypeWorkBudget::with_limit(computed);
    machine
        .acquire_resource(resource, shadowed_environment(identity), integer("41"))
        .unwrap();
    assert_eq!(machine.instantiation_work.used(), computed);
    assert_eq!(machine.live_resources, 1);
    assert_eq!(machine.next_activation, 8);
    let Some(Control::Evaluate(_, environment)) = &machine.control else {
        panic!("actual resource body published")
    };
    let (entries, has_rows) = environment.instantiation.alignment_bindings();
    assert!(!has_rows);
    assert_eq!(entries.len(), old_entries); // Shadowing still reserved n+1.
    assert!(matches!(entries.as_slice(), [(found, Type::Inference(key))]
        if *found == identity && key.value() == 7));
    assert_eq!(environment.len, 1); // Extension adds no work charge.
    assert_eq!(
        machine.effect_trace.as_ref().unwrap(),
        &[EffectTraceEvent::ResourceAcquired(7)]
    );
}

#[test]
fn cell_request_computed_exact_and_top_down_one_short_preserve_prefix() {
    let (program, resource, request) = fixture();
    // Literal one-argument cell instance: charge2 + substitution leaf1.
    // Two physical frames visited: nonhandler Bind, then ResourceBoundary.
    let computed = 3 + 2;
    for budget in [computed - 1, computed] {
        let mut machine = Machine::new_effect(&program);
        machine
            .acquire_resource(resource, Environment::new(), integer("41"))
            .unwrap();
        let Some(Control::Evaluate(body, environment)) = machine.control.take() else {
            panic!("acquired body")
        };
        let saved = environment.instantiation.clone();
        machine.frames.push(Frame::Bind {
            binder: machine.resource(resource).unwrap().acquisition.handle,
            body,
            environment,
        });
        machine.control = Some(Control::Return(Value::ResourceHandle(ActivationKey(0))));
        machine.instantiation_work = TypeWorkBudget::with_limit(budget);
        let result =
            machine.return_request(request, &saved, Value::ResourceHandle(ActivationKey(0)));
        assert_eq!(machine.instantiation_work.used(), budget);
        assert_eq!(machine.live_resources, 1);
        if budget < computed {
            let detail = details(result.unwrap_err());
            assert_eq!(detail.cause, ResourceFailureCause::WorkBudgetExhausted);
            assert_eq!(detail.phase, RuntimePhase::Access);
            assert_eq!(detail.resource, RuntimeResource::WorkUnits);
            assert_eq!(detail.requested, Some(1));
            assert_eq!(detail.available, Some(0));
            assert_eq!(
                machine.effect_trace.as_ref().unwrap(),
                &[EffectTraceEvent::ResourceAcquired(0)]
            );
            assert!(matches!(
                machine.control,
                Some(Control::Return(Value::ResourceHandle(_)))
            ));
        } else {
            result.unwrap();
            assert!(
                matches!(machine.control, Some(Control::Return(Value::Integer(ref value)))
                if value.to_string() == "41")
            );
            let operation = match &program.node(request).unwrap().kind {
                EffectExprKind::Operation(EffectOperation::Request(request)) => request.operation(),
                _ => unreachable!(),
            };
            assert_eq!(
                machine.effect_trace.as_ref().unwrap(),
                &[
                    EffectTraceEvent::ResourceAcquired(0),
                    EffectTraceEvent::Request(operation),
                    EffectTraceEvent::ResourceRead(0)
                ]
            );
        }
    }
}
