//! Focused executable C3.4 evidence. Uses existing allocator injection only.
use super::native_buffer::tests as allocation_probe;
use super::tests::effect_program;
use super::*;

fn cleanup_fixture() -> (
    ValidatedEffectProgram,
    crate::core::effect::CleanupScopeNode,
    Environment,
) {
    let program = effect_program(
        "main : Unit -> Int\nmain () = cleanup fn(ignored) {\nlet callback_started = 7001\n()\n} {\n42\n}\n",
    );
    let mut pending = vec![program.root()];
    let mut scope = None;
    let mut bindings = Vec::new();
    while let Some(node) = pending.pop() {
        let expression = program.node(node).unwrap();
        match &expression.kind {
            EffectExprKind::Operation(EffectOperation::Cleanup(found)) => scope = Some(*found),
            EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(binding))) => {
                bindings.push((binding.binder().id(), binding.initializer()));
            }
            _ => {}
        }
        pending
            .extend((0..expression.kind.child_count()).filter_map(|i| expression.kind.child_at(i)));
    }
    let scope = scope.unwrap();
    let initializer = bindings
        .into_iter()
        .find(|(binder, _)| *binder == scope.callback)
        .unwrap()
        .1;
    let executable = ExecutableProgram::Effect(program.shared());
    let transition = dispatch_entry(
        &executable,
        initializer,
        Environment::new(),
        &mut Vec::new(),
    )
    .unwrap();
    let Control::Return(callback) = transition.control else {
        panic!("ordinary callback")
    };
    let environment = Environment::new().extend(scope.callback, callback).unwrap();
    (program, scope, environment)
}

// Each entry owns independent parent and captured-environment branches. A
// depth of ten exceeds the actual disposal walker's eight retained slots.
// Shared linear aliases would not exercise this allocation boundary.
fn branching_environment(depth: usize, binder: BinderId, template: &Closure) -> Environment {
    if depth == 0 {
        return Environment::new();
    }
    let parent = branching_environment(depth - 1, binder, template);
    let captured = branching_environment(depth - 1, binder, template);
    let mut closure = template.clone();
    closure.environment = captured;
    parent.extend(binder, Value::Function(closure)).unwrap()
}

fn prepared() -> Machine {
    let (program, cleanup, environment) = cleanup_fixture();
    let mut machine = Machine::new_effect(&program);
    let Value::Function(template) = environment
        .lookup(cleanup.callback, &machine.program)
        .unwrap()
    else {
        panic!("callback closure")
    };
    let discarded = branching_environment(10, cleanup.callback, &template);
    machine.acquire_cleanup(cleanup, environment).unwrap();
    machine.frames.push(Frame::Bind {
        binder: cleanup.callback,
        body: cleanup.body,
        environment: discarded,
    });
    let captured = machine.capture_from(0).unwrap();
    machine.frames.push(Frame::ClauseBoundary {
        handler: HandlerId::new(0),
        owner: ResumeId::new(0),
        registration: None,
        continuation: Some(captured),
    });
    machine.control = Some(Control::Return(Value::Unit));
    machine.effect_trace = Some(Vec::new());
    machine.instantiation_work = TypeWorkBudget::unbounded();
    machine
}

fn capability_live(machine: &Machine) -> bool {
    matches!(
        machine.frames.first(),
        Some(Frame::ClauseBoundary {
            continuation: Some(_),
            ..
        })
    )
}

fn discarded_events(machine: &Machine) -> usize {
    machine
        .effect_trace
        .as_ref()
        .unwrap()
        .iter()
        .filter(|event| matches!(event, EffectTraceEvent::Discard(_)))
        .count()
}

#[test]
fn discard_disposal_refusal_consumes_owner_without_publishing_discard_or_replaying_cleanup() {
    // Same actual frame/capture shape succeeds without disposal refusal.
    allocation_probe::reset();
    let mut success = prepared();
    success
        .discard(HandlerId::new(0), ResumeId::new(0))
        .unwrap();
    assert!(!capability_live(&success));
    assert_eq!(success.captured_cells, 0);
    assert_eq!(success.live_cleanups, 1);
    assert_eq!(discarded_events(&success), 1);
    assert_eq!(success.run().unwrap().value.to_string(), "()");

    // Pre-consumption refusal retains capability/accounting and publishes no
    // discard. Dropping that retained state can add a distinct secondary cause.
    allocation_probe::reset();
    let mut preflight = prepared();
    preflight.instantiation_work = TypeWorkBudget::with_limit(0);
    let host_scope = disposal::Scope::enter();
    let primary = preflight
        .discard(HandlerId::new(0), ResumeId::new(0))
        .unwrap_err();
    assert!(capability_live(&preflight));
    assert_eq!(preflight.captured_cells, 2);
    assert_eq!(discarded_events(&preflight), 0);
    allocation_probe::FAIL_DISPOSAL_GROWTH.set(true);
    drop(preflight);
    let RuntimeFailure::Report(report) = host_scope.finish::<()>(Err(primary)).unwrap_err() else {
        panic!("preflight report")
    };
    assert_eq!(
        report.primary.resource().unwrap().cause,
        ResourceFailureCause::WorkBudgetExhausted
    );
    assert_eq!(
        report.primary.resource().unwrap().phase,
        RuntimePhase::Capture
    );
    let secondary = report.teardown.unwrap();
    assert_eq!(secondary.cause, ResourceFailureCause::AllocatorRefused);
    assert_eq!(secondary.phase, RuntimePhase::Teardown);
    assert_eq!(secondary.resource, RuntimeResource::EnvironmentDisposal);
    assert_eq!(report.cleanup, super::super::CleanupStatus::Incomplete);
    drop(host_scope);

    // Real environment disposal while projecting a nonowner frame happens
    // after ticket consumption. It is detected at the next projection check.
    allocation_probe::reset();
    let mut stopped = prepared();
    let observed = Arc::new(std::sync::Mutex::new(Vec::new()));
    stopped.work_trace = Some(Arc::clone(&observed));
    let host_scope = disposal::Scope::enter();
    disposal::reset_growth_attempts();
    allocation_probe::FAIL_DISPOSAL_GROWTH.set(true);
    let primary = stopped
        .discard(HandlerId::new(0), ResumeId::new(0))
        .unwrap_err();
    assert!(!capability_live(&stopped));
    assert_eq!(
        stopped.captured_cells, 2,
        "accounting publication was not reached"
    );
    assert_eq!(stopped.live_cleanups, 1);
    assert_eq!(discarded_events(&stopped), 0);
    assert_eq!(stopped.frames.len(), 1, "closing frames were not published");
    let later = stopped.run_loop().unwrap_err();
    assert_eq!(later, primary);
    assert!(
        observed.lock().unwrap().is_empty(),
        "callback/body/source replay never entered"
    );
    let RuntimeFailure::Report(report) = host_scope.finish::<()>(Err(primary)).unwrap_err() else {
        panic!("post-consumption report")
    };
    let details = report.primary.resource().unwrap();
    assert_eq!(details.cause, ResourceFailureCause::AllocatorRefused);
    assert_eq!(details.phase, RuntimePhase::Teardown);
    assert_eq!(details.resource, RuntimeResource::EnvironmentDisposal);
    assert!(
        report.teardown.is_none(),
        "same first failure is not duplicated as secondary"
    );
    assert_eq!(report.cleanup, super::super::CleanupStatus::Incomplete);
    assert_eq!(
        disposal::growth_attempts(),
        1,
        "failed growth is not retried"
    );
    drop(host_scope);
}
