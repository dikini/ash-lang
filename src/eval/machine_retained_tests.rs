//! Focused ownership tests for the retained-control store's actual frame moves.

use super::*;
use crate::types::{Type, TypeVariableId};

fn saved(value: i128) -> Frame {
    Frame::CleanupCompletion {
        saved: Value::SmallInteger(value),
    }
}

fn live_capture() -> CapturedContinuation {
    CapturedContinuation {
        frames: vec![
            saved(77),
            Frame::ClauseBoundary {
                retained: None,
                handler: HandlerId::new(1),
                owner: ResumeId::new(1),
                continuation: Some(CapturedContinuation {
                    frames: vec![Frame::CloseCompletion],
                }),
                registration: None,
                completion_count: 1,
            },
            Frame::ClauseBoundary {
                retained: None,
                handler: HandlerId::new(2),
                owner: ResumeId::new(2),
                continuation: None,
                registration: None,
                completion_count: 1,
            },
        ],
    }
}

#[test]
fn retained_move_restores_once_above_the_current_consumer() {
    let mut store = RetainedStore::new(ActivationKey(7), test_store_api());
    let mut owner = Some(live_capture());
    let mut work = TypeWorkBudget::default();
    let key = store.retain(&mut owner, &mut work).unwrap();
    assert!(owner.is_none());

    // The nested live capture remains counted when its containing segment is
    // restored. Sentinels mark the current consumer and its prepared adapter.
    let mut captured_cells = 4;
    let mut frames = vec![saved(1)];
    assert!(
        store
            .restore(key, &mut frames, saved(2), &mut captured_cells, &mut work)
            .unwrap()
    );
    assert_eq!(captured_cells, 1);
    assert_eq!(frames.len(), 5);
    assert!(matches!(
        &frames[0],
        Frame::CleanupCompletion {
            saved: Value::SmallInteger(1)
        }
    ));
    assert!(matches!(
        &frames[1],
        Frame::CleanupCompletion {
            saved: Value::SmallInteger(2)
        }
    ));
    assert!(matches!(
        &frames[2],
        Frame::CleanupCompletion {
            saved: Value::SmallInteger(77)
        }
    ));
    assert!(matches!(
        &frames[3],
        Frame::ClauseBoundary {
            continuation: Some(_),
            ..
        }
    ));
    assert!(matches!(
        &frames[4],
        Frame::ClauseBoundary {
            continuation: None,
            ..
        }
    ));

    let len = frames.len();
    assert!(
        !store
            .restore(key, &mut frames, saved(3), &mut captured_cells, &mut work)
            .unwrap()
    );
    assert_eq!(frames.len(), len);
    assert_eq!(captured_cells, 1);
    eprintln!("Frame size: {} bytes", std::mem::size_of::<Frame>());
}

#[test]
fn retained_adapter_uses_the_current_consumer_region_after_restoration() {
    let source = concat!(
        "import @builtin.retained_control as Control\n",
        "forward<N,A,E : EffectRow> : ",
        "(Control.Store<N,(Unit -> A ! {| E})>, Control.Key<N>) -> ",
        "Control.Option<A> ! {Control.Drive<N> | E}\n",
        "forward pair = Control.advance pair\n",
        "main : Unit -> Int\nmain () = 42\n",
    );
    let (program, _, _) = crate::core::validate::generic_cell_source_fixture_for_test(source, None);
    let mut pending = vec![program.root()];
    let mut visited = std::collections::HashSet::new();
    let mut region = None;
    let mut adapter = None;
    let mut branch = None;
    while let Some(id) = pending.pop() {
        if !visited.insert(id) {
            continue;
        }
        let expression = program.node(id).unwrap();
        match &expression.kind {
            EffectExprKind::Operation(EffectOperation::Region(scope)) if scope.entry => {
                region = Some(id);
            }
            EffectExprKind::Operation(EffectOperation::Continue(continuation)) => {
                adapter = Some(continuation.adapter.clone());
            }
            EffectExprKind::Pure(PureExprKind::Value(PureValue::Integer(integer)))
                if integer.value().to_i128() == Some(42) =>
            {
                branch = Some(id)
            }
            _ => {}
        }
        pending
            .extend((0..expression.kind.child_count()).filter_map(|i| expression.kind.child_at(i)));
    }
    let (region, adapter, branch) = (region.unwrap(), adapter.unwrap(), branch.unwrap());

    let consumer = || {
        let mut machine = Machine::new_effect(&program);
        let scope = machine.region_scope(region).unwrap();
        let (identity, access, handler) = (scope.identity(), scope.access().id(), scope.body());
        assert!(machine.handler(handler).is_some());
        let selected = ActivationKey(9);
        let mut environment = Environment::new();
        environment.instantiation = environment
            .instantiation
            .acquire(identity, selected, &mut machine.instantiation_work, None)
            .unwrap();
        environment = environment
            .extend(access, Value::RegionView(selected))
            .unwrap();
        machine.frames.push(Frame::RegionBoundary {
            node: region,
            key: selected,
            allocate: Value::RegionHostFunction {
                owner: selected,
                release: false,
            },
            release: Value::RegionHostFunction {
                owner: selected,
                release: true,
            },
            preceding: Value::Unit,
            records: Vec::new(),
        });
        machine.frames.push(Frame::HandlerBoundary {
            retained: None,
            node: handler,
            environment: environment.clone(),
            registration: None,
        });
        (machine, environment, access)
    };

    let (mut machine, consumer_environment, access) = consumer();
    // The old branch environment points elsewhere. Only the current consumer
    // has a live allocator; using the saved branch environment would fail.
    let branch_environment = consumer_environment
        .clone()
        .extend(access, Value::RegionView(ActivationKey(99)))
        .unwrap();
    let mut store = RetainedStore::new(ActivationKey(7), test_store_api());
    let mut capture = Some(CapturedContinuation {
        frames: vec![Frame::Bind {
            binder: adapter.answer.id(),
            body: branch,
            environment: branch_environment,
        }],
    });
    let key = store
        .retain(&mut capture, &mut machine.instantiation_work)
        .unwrap();
    machine.captured_cells = 1;
    assert!(
        store
            .restore(
                key,
                &mut machine.frames,
                Frame::Bind {
                    binder: adapter.answer.id(),
                    body: adapter.some,
                    environment: consumer_environment.clone()
                },
                &mut machine.captured_cells,
                &mut machine.instantiation_work,
            )
            .unwrap()
    );
    assert!(
        machine.heap.is_empty(),
        "restoring must not run the adapter or allocate an Ash record"
    );
    machine.control = Some(Control::Return(Value::Unit));
    let result = machine.run_loop().unwrap();
    assert_eq!(result.value.to_string(), "Some(42)");
    assert_eq!(machine.next_region_invocation, 1);
    let entered = |node| {
        result
            .trace
            .iter()
            .position(|event| *event == TraceEvent::Enter(node))
    };
    assert!(entered(branch).unwrap() < entered(adapter.some).unwrap());
    assert!(entered(adapter.none).is_none());

    let (mut missing, consumer_environment, _) = consumer();
    let frame_count = missing.frames.len();
    assert!(
        !store
            .restore(
                key,
                &mut missing.frames,
                Frame::Bind {
                    binder: adapter.answer.id(),
                    body: adapter.some,
                    environment: consumer_environment.clone()
                },
                &mut missing.captured_cells,
                &mut missing.instantiation_work,
            )
            .unwrap()
    );
    assert_eq!(missing.frames.len(), frame_count);
    missing.control = Some(Control::Evaluate(adapter.none, consumer_environment));
    let result = missing.run_loop().unwrap();
    assert_eq!(result.value.to_string(), "None");
    assert_eq!(missing.next_region_invocation, 1);
    assert!(
        result
            .trace
            .iter()
            .any(|event| *event == TraceEvent::Enter(adapter.none))
    );
    assert!(
        !result
            .trace
            .iter()
            .any(|event| *event == TraceEvent::Enter(branch)
                || *event == TraceEvent::Enter(adapter.some))
    );
}

fn checkpoint_fixture() -> (ValidatedEffectProgram, NodeId, NodeId, NodeId) {
    let program = super::tests::effect_program(concat!(
        "effect Checkpoint {\nwait : Unit -> Unit\n}\n",
        "main : Unit -> Unit\n",
        "main () = handle (perform Checkpoint.wait ()) with Checkpoint {\n",
        "wait ignored => resume ()\n}\n",
    ));
    let mut pending = vec![program.root()];
    let mut seen = std::collections::HashSet::new();
    let mut handler_node = None;
    let mut request_node = None;
    let mut resumes = Vec::new();
    while let Some(id) = pending.pop() {
        if !seen.insert(id) {
            continue;
        }
        let node = program.node(id).unwrap();
        match &node.kind {
            EffectExprKind::Operation(EffectOperation::Handler(handler))
                if program
                    .registry()
                    .effect(handler.effect().effect())
                    .is_some_and(|effect| effect.spelling == "Checkpoint") =>
            {
                handler_node = Some(id)
            }
            EffectExprKind::Operation(EffectOperation::Request(request))
                if program
                    .registry()
                    .effect(request.effect().effect())
                    .is_some_and(|effect| effect.spelling == "Checkpoint") =>
            {
                request_node = Some(id)
            }
            EffectExprKind::Operation(EffectOperation::Resume(_)) => resumes.push(id),
            _ => {}
        }
        pending.extend((0..node.kind.child_count()).filter_map(|i| node.kind.child_at(i)));
    }
    let (handler_node, request_node) = (handler_node.unwrap(), request_node.unwrap());
    let EffectExprKind::Operation(EffectOperation::Handler(handler)) =
        &program.node(handler_node).unwrap().kind
    else {
        unreachable!()
    };
    let resume = resumes.into_iter().find(|id| matches!(&program.node(*id).unwrap().kind,
        EffectExprKind::Operation(EffectOperation::Resume(resume)) if resume.handler() == handler.id())).unwrap();
    (program, handler_node, request_node, resume)
}

fn probe_fixture() -> (ValidatedEffectProgram, NodeId, NodeId, TypeVariableId) {
    let program = super::tests::effect_program(concat!(
        "import @builtin.retained_control as Control\n",
        "intercept<N> : Control.Store<N,(Unit -> Unit)> -> Bool\n",
        "intercept store = handle (perform Control.Probe<N>.quiescent ()) ",
        "with Control.Probe<N> {\nquiescent ignored => resume true\n}\n",
        "main : Unit -> Int\nmain () = 42\n",
    ));
    let mut pending = vec![program.root()];
    let mut seen = std::collections::HashSet::new();
    let mut handler = None;
    let mut request = None;
    while let Some(id) = pending.pop() {
        if !seen.insert(id) {
            continue;
        }
        let node = program.node(id).unwrap();
        match &node.kind {
            EffectExprKind::Operation(EffectOperation::Handler(candidate))
                if program
                    .registry()
                    .effect(candidate.effect().effect())
                    .is_some_and(|effect| effect.spelling == "Probe") =>
            {
                handler = Some(id)
            }
            EffectExprKind::Operation(EffectOperation::Request(candidate))
                if program
                    .registry()
                    .effect(candidate.effect().effect())
                    .is_some_and(|effect| effect.spelling == "Probe") =>
            {
                request = Some(id)
            }
            _ => {}
        }
        pending.extend((0..node.kind.child_count()).filter_map(|i| node.kind.child_at(i)));
    }
    let request = request.unwrap();
    let EffectExprKind::Operation(EffectOperation::Request(candidate)) =
        &program.node(request).unwrap().kind
    else {
        unreachable!()
    };
    let [crate::types::KindedArgument::TypeArg(Type::Variable(identity))] =
        candidate.effect().arguments()
    else {
        panic!("generic probe identity")
    };
    let identity = *identity;
    (program, handler.unwrap(), request, identity)
}

fn probe_api(program: &ValidatedEffectProgram, request: NodeId) -> crate::resolved::StoreApi {
    let EffectExprKind::Operation(EffectOperation::Request(request)) =
        &program.node(request).unwrap().kind
    else {
        unreachable!()
    };
    crate::resolved::StoreApi::for_module(request.effect().effect().module()).unwrap()
}

fn test_store_api() -> crate::resolved::StoreApi {
    static API: std::sync::OnceLock<crate::resolved::StoreApi> = std::sync::OnceLock::new();
    *API.get_or_init(|| {
        let (program, _, request, _) = probe_fixture();
        probe_api(&program, request)
    })
}

#[test]
fn retained_probe_checks_driver_before_source_handler_selection() {
    let (program, handler, request, identity) = probe_fixture();
    let api = probe_api(&program, request);
    let activation = ActivationKey(7);
    let mut machine = Machine::new_effect(&program);
    machine.control.take();
    let instantiation = Instantiation::default()
        .acquire(identity, activation, &mut machine.instantiation_work, None)
        .unwrap();
    let mut environment = Environment::new();
    environment.instantiation = instantiation.clone();
    machine.frames.push(Frame::ResourceBoundary {
        node: program.root(),
        key: activation,
        payload: ResourcePayload::Store(Box::new(RetainedStore::new(activation, api))),
    });
    machine
        .frames
        .push(Frame::RetainedRootCompletion { key: activation });
    machine.frames.push(Frame::HandlerBoundary {
        node: handler,
        environment: environment.clone(),
        registration: None,
        retained: None,
    });
    assert!(
        machine
            .return_request(request, &instantiation, Value::Unit)
            .is_err()
    );
    assert!(matches!(
        machine.frames.last(),
        Some(Frame::HandlerBoundary { .. })
    ));
    machine.frames.remove(1);
    machine
        .return_request(request, &instantiation, Value::Unit)
        .unwrap();
    assert!(matches!(
        machine.control.take(),
        Some(Control::Evaluate(..))
    ));
    assert!(matches!(
        machine.frames.last(),
        Some(Frame::ClauseBoundary { .. })
    ));

    // A different, non-store identity remains an ordinary request even
    // while this store's branch is active.
    let mut other = Machine::new_effect(&program);
    other.control.take();
    let other_instantiation = Instantiation::default()
        .acquire(
            identity,
            ActivationKey(8),
            &mut other.instantiation_work,
            None,
        )
        .unwrap();
    environment.instantiation = other_instantiation.clone();
    other.frames.push(Frame::ResourceBoundary {
        node: program.root(),
        key: activation,
        payload: ResourcePayload::Store(Box::new(RetainedStore::new(activation, api))),
    });
    other
        .frames
        .push(Frame::RetainedRootCompletion { key: activation });
    other.frames.push(Frame::HandlerBoundary {
        node: handler,
        environment,
        registration: None,
        retained: None,
    });
    other
        .return_request(request, &other_instantiation, Value::Unit)
        .unwrap();
    assert!(matches!(other.control.take(), Some(Control::Evaluate(..))));
}

#[test]
fn retained_probe_reads_the_actual_owned_work() {
    let (program, _, request, _) = probe_fixture();
    let EffectExprKind::Operation(EffectOperation::Request(request)) =
        &program.node(request).unwrap().kind
    else {
        unreachable!()
    };
    let api = crate::resolved::StoreApi::for_module(request.effect().effect().module()).unwrap();
    let operation = request.operation();
    let activation = ActivationKey(7);
    let mut machine = Machine::new_effect(&program);
    machine.control.take();
    machine.frames.push(Frame::ResourceBoundary {
        node: program.root(),
        key: activation,
        payload: ResourcePayload::Store(Box::new(RetainedStore::new(activation, api))),
    });
    let probe = |machine: &mut Machine<'_>, expected| {
        machine
            .interpret_store_probe(0, api, operation, Value::Unit)
            .unwrap();
        assert!(
            matches!(machine.control.take(), Some(Control::Return(Value::Boolean(actual))) if actual == expected)
        );
    };
    probe(&mut machine, true);
    let Frame::ResourceBoundary {
        payload: ResourcePayload::Store(store),
        ..
    } = &mut machine.frames[0]
    else {
        unreachable!()
    };
    store.active_roots = 1;
    probe(&mut machine, false);
    let Frame::ResourceBoundary {
        payload: ResourcePayload::Store(store),
        ..
    } = &mut machine.frames[0]
    else {
        unreachable!()
    };
    store.active_roots = 0;
    store.slots.push(RetainedSlot {
        generation: 0,
        continuation: Some(live_capture()),
    });
    probe(&mut machine, false);
    let Frame::ResourceBoundary {
        payload: ResourcePayload::Store(store),
        ..
    } = &mut machine.frames[0]
    else {
        unreachable!()
    };
    store.slots[0].continuation = None;
    probe(&mut machine, true);
    assert!(
        machine
            .interpret_store_probe(0, api, operation, Value::Boolean(true))
            .is_err()
    );
    machine.instantiation_work = TypeWorkBudget::with_limit(0);
    assert!(
        machine
            .interpret_store_probe(0, api, operation, Value::Unit)
            .is_err()
    );
    assert!(machine.control.is_none());
}

#[test]
fn retained_probe_request_selects_the_owning_store() {
    let (program, _, request, identity) = probe_fixture();
    let api = probe_api(&program, request);
    let activation = ActivationKey(7);
    let mut machine = Machine::new_effect(&program);
    machine.control.take();
    let instantiation = Instantiation::default()
        .acquire(identity, activation, &mut machine.instantiation_work, None)
        .unwrap();
    machine.frames.push(Frame::ResourceBoundary {
        node: program.root(),
        key: activation,
        payload: ResourcePayload::Store(Box::new(RetainedStore::new(activation, api))),
    });
    let other = ActivationKey(8);
    let mut other_store = RetainedStore::new(other, api);
    other_store.slots.push(RetainedSlot {
        generation: 0,
        continuation: Some(live_capture()),
    });
    machine.frames.push(Frame::ResourceBoundary {
        node: program.root(),
        key: other,
        payload: ResourcePayload::Store(Box::new(other_store)),
    });
    machine
        .return_request(request, &instantiation, Value::Unit)
        .unwrap();
    assert!(matches!(
        machine.control.take(),
        Some(Control::Return(Value::Boolean(true)))
    ));
    let Frame::ResourceBoundary {
        payload: ResourcePayload::Store(store),
        ..
    } = &mut machine.frames[0]
    else {
        unreachable!()
    };
    store.slots.push(RetainedSlot {
        generation: 0,
        continuation: Some(live_capture()),
    });
    machine
        .return_request(request, &instantiation, Value::Unit)
        .unwrap();
    assert!(matches!(
        machine.control.take(),
        Some(Control::Return(Value::Boolean(false)))
    ));

    let foreign_api = test_store_api();
    assert_ne!(foreign_api.probe(), api.probe());
    let mut foreign = Machine::new_effect(&program);
    foreign.control.take();
    foreign.frames.push(Frame::ResourceBoundary {
        node: program.root(),
        key: activation,
        payload: ResourcePayload::Store(Box::new(RetainedStore::new(activation, foreign_api))),
    });
    assert_eq!(
        foreign.return_request(request, &instantiation, Value::Unit),
        Err(RuntimeFailure::ForeignBinding)
    );
    assert!(foreign.control.is_none());
}

#[test]
fn retained_root_moves_only_the_nearest_associated_clause_owner() {
    let (program, handler_node, request_node, _) = checkpoint_fixture();
    let mut machine = Machine::new_effect(&program);
    machine.control.take();
    let activation = ActivationKey(7);
    machine.frames.push(Frame::ResourceBoundary {
        node: program.root(),
        key: activation,
        payload: ResourcePayload::Store(Box::new(RetainedStore::new(activation, test_store_api()))),
    });
    machine.live_resources = 1;
    machine
        .begin_retained_root(handler_node, activation, Environment::new())
        .unwrap();
    assert!(matches!(
        machine.control.take(),
        Some(Control::Evaluate(..))
    ));
    let handler = machine.handler(handler_node).unwrap().id();
    let owner = machine.handler(handler_node).unwrap().clauses()[0].resume();
    machine
        .return_request(request_node, &Instantiation::default(), Value::Unit)
        .unwrap();
    assert!(matches!(
        machine.control.take(),
        Some(Control::Evaluate(..))
    ));
    assert!(machine.ensure_retained_driver(activation).is_err());
    assert!(matches!(machine.frames.last(), Some(Frame::ClauseBoundary {
        handler: found, owner: selected, retained: Some(key), continuation: Some(_), ..
    }) if *found == handler && *selected == owner && *key == activation));

    machine.frames.push(Frame::ClauseBoundary {
        handler,
        owner: ResumeId::new(owner.value() + 1),
        continuation: None,
        registration: None,
        retained: None,
        completion_count: 1,
    });
    assert!(machine.retain_selected(handler, owner).is_err());
    assert!(matches!(
        machine.frames[machine.frames.len() - 2],
        Frame::ClauseBoundary {
            continuation: Some(_),
            ..
        }
    ));
    machine.frames.pop();
    machine_test_hooks::FAIL_CONTROL_RESERVATION.set(Some(ResourceFailureCause::AllocatorRefused));
    assert!(machine.retain_selected(handler, owner).is_err());
    machine_test_hooks::reset();
    assert!(matches!(
        machine.frames.last(),
        Some(Frame::ClauseBoundary {
            continuation: Some(_),
            ..
        })
    ));
    machine.retain_selected(handler, owner).unwrap();
    let Some(Control::Return(Value::RetainedKey(key))) = machine.control.take() else {
        panic!("retain must return its newly published locator");
    };
    assert_eq!(key.activation, activation);
    assert!(machine.ensure_retained_driver(activation).is_err());
    let clause = machine.frames.pop().unwrap();
    machine.return_from(clause, Value::Unit).unwrap();
    machine.control.take();
    assert!(machine.ensure_retained_driver(activation).is_err());
    let completion = machine.frames.pop().unwrap();
    machine.return_from(completion, Value::Unit).unwrap();
    machine.control.take();
    assert!(machine.ensure_retained_driver(activation).is_ok());
    let Frame::ResourceBoundary {
        payload: ResourcePayload::Store(store),
        ..
    } = &machine.frames[0]
    else {
        panic!("store")
    };
    assert_eq!(store.active_roots, 0);
    assert!(store.slots[key.slot].continuation.is_some());
}

#[test]
fn retained_resume_reyield_preserves_each_suffix_and_unrelated_work() {
    let (program, handler_node, request_node, resume_node) = checkpoint_fixture();
    let activation = ActivationKey(7);
    let mut store = RetainedStore::new(activation, test_store_api());
    let mut unrelated = Some(CapturedContinuation {
        frames: vec![Frame::CloseCompletion],
    });
    let other_key = store
        .retain(&mut unrelated, &mut TypeWorkBudget::default())
        .unwrap();
    let mut machine = Machine::new_effect(&program);
    machine.control.take();
    machine.frames.push(Frame::ResourceBoundary {
        node: program.root(),
        key: activation,
        payload: ResourcePayload::Store(Box::new(store)),
    });
    machine.live_resources = 1;
    machine.captured_cells = 1;
    machine
        .begin_retained_root(handler_node, activation, Environment::new())
        .unwrap();
    machine.control.take();
    let handler = machine.handler(handler_node).unwrap().id();
    let owner = machine.handler(handler_node).unwrap().clauses()[0].resume();
    for _ in 0..2 {
        machine
            .return_request(request_node, &Instantiation::default(), Value::Unit)
            .unwrap();
        machine.control.take();
        machine.return_resume(resume_node, Value::Unit).unwrap();
        machine.control.take();
    }
    let clauses = machine.frames.iter().filter(|frame| matches!(frame,
        Frame::ClauseBoundary { retained: Some(key), continuation: None, completion_count: 1, .. } if *key == activation)).count();
    assert_eq!(
        clauses, 2,
        "same static identities do not merge associated suffixes"
    );
    assert_eq!(machine.captured_cells, 1);
    machine
        .return_request(request_node, &Instantiation::default(), Value::Unit)
        .unwrap();
    machine.control.take();
    machine.retain_selected(handler, owner).unwrap();
    let Some(Control::Return(Value::RetainedKey(key))) = machine.control.take() else {
        panic!("key")
    };
    assert_ne!(key.slot, other_key.slot);
    assert_eq!(machine.captured_cells, 2);
    for _ in 0..3 {
        assert!(machine.ensure_retained_driver(activation).is_err());
        let clause = machine.frames.pop().unwrap();
        assert!(matches!(
            clause,
            Frame::ClauseBoundary {
                retained: Some(_),
                ..
            }
        ));
        machine.return_from(clause, Value::Unit).unwrap();
        machine.control.take();
    }
    assert!(machine.ensure_retained_driver(activation).is_err());
    let completion = machine.frames.pop().unwrap();
    machine.return_from(completion, Value::Unit).unwrap();
    machine.control.take();
    assert!(machine.ensure_retained_driver(activation).is_ok());
    let Frame::ResourceBoundary {
        payload: ResourcePayload::Store(store),
        ..
    } = &machine.frames[0]
    else {
        panic!("store")
    };
    assert_eq!(store.active_roots, 0);
    assert!(store.slots[key.slot].continuation.is_some());
    assert!(store.slots[other_key.slot].continuation.is_some());
    assert_eq!(machine.captured_cells, 2);
}

#[test]
fn retained_root_in_owned_service_segment_keeps_driver_blocked() {
    let (program, _, _, _) = checkpoint_fixture();
    let key = ActivationKey(7);
    for region_segment in [false, true] {
        let mut machine = Machine::new_effect(&program);
        machine.control.take();
        let mut store = RetainedStore::new(key, test_store_api());
        store.active_roots = 1;
        machine.frames.push(Frame::ResourceBoundary {
            node: program.root(),
            key,
            payload: ResourcePayload::Store(Box::new(store)),
        });
        let segment = CapturedContinuation {
            frames: vec![Frame::RetainedRootCompletion { key }],
        };
        machine.frames.push(if region_segment {
            Frame::RegionAllocated {
                segment,
                invocation: super::super::value::RegionInvocation {
                    owner: key,
                    serial: 0,
                },
                registered: false,
            }
        } else {
            Frame::ClauseBoundary {
                handler: HandlerId::new(0),
                owner: ResumeId::new(0),
                continuation: Some(segment),
                registration: None,
                retained: None,
                completion_count: 1,
            }
        });
        assert!(machine.ensure_retained_driver(key).is_err());
        let Frame::ResourceBoundary {
            payload: ResourcePayload::Store(store),
            ..
        } = &machine.frames[0]
        else {
            panic!("store")
        };
        assert_eq!(store.active_roots, 1, "moving a frame is not completion");
    }
}

#[test]
fn retained_outer_discard_refuses_to_abandon_a_root_completion() {
    let (program, handler_node, _, _) = checkpoint_fixture();
    let key = ActivationKey(7);
    let mut machine = Machine::new_effect(&program);
    machine.control.take();
    let handler = machine.handler(handler_node).unwrap().id();
    let owner = machine.handler(handler_node).unwrap().clauses()[0].resume();
    let mut store = RetainedStore::new(key, test_store_api());
    store.active_roots = 1;
    machine.frames.push(Frame::ResourceBoundary {
        node: program.root(),
        key,
        payload: ResourcePayload::Store(Box::new(store)),
    });
    machine.frames.push(Frame::ClauseBoundary {
        handler,
        owner,
        continuation: Some(CapturedContinuation {
            frames: vec![
                Frame::HandlerBoundary {
                    node: handler_node,
                    environment: Environment::new(),
                    registration: None,
                    retained: None,
                },
                Frame::RetainedRootCompletion { key },
            ],
        }),
        registration: None,
        retained: None,
        completion_count: 1,
    });
    machine.captured_cells = 2;
    assert_eq!(
        machine.discard(handler, owner),
        Err(RuntimeFailure::InvalidControlState)
    );
    assert_eq!(machine.captured_cells, 2);
    assert!(
        matches!(&machine.frames[1], Frame::ClauseBoundary { continuation: Some(capture), .. } if capture.frames.len() == 2)
    );
    let Frame::ResourceBoundary {
        payload: ResourcePayload::Store(store),
        ..
    } = &machine.frames[0]
    else {
        panic!("store")
    };
    assert_eq!(store.active_roots, 1);
}

#[test]
fn retained_continue_carrier_runs_the_restored_branch_for_its_current_consumer() {
    let source = concat!(
        "import @builtin.retained_control as Control\n",
        "effect Checkpoint {\nwait : Unit -> Unit\n}\n",
        "forward<N,A,E : EffectRow> : ",
        "(Control.Store<N,(Unit -> A ! {| E})>, Control.Key<N>) -> ",
        "Control.Option<A> ! {Control.Drive<N> | E}\n",
        "forward pair = Control.advance pair\n",
        "main : Unit -> Int\n",
        "main () = handle ({\nlet _ = perform Checkpoint.wait ()\n42\n}) with Checkpoint {\n",
        "wait ignored => resume ()\n}\n",
    );
    let (program, _, _) = crate::core::validate::generic_cell_source_fixture_for_test(source, None);
    let mut pending = vec![program.root()];
    let mut seen = std::collections::HashSet::new();
    let (mut region, mut carrier, mut handler, mut request) = (None, None, None, None);
    while let Some(id) = pending.pop() {
        if !seen.insert(id) {
            continue;
        }
        let node = program.node(id).unwrap();
        match &node.kind {
            EffectExprKind::Operation(EffectOperation::Region(scope)) if scope.entry => {
                region = Some(id)
            }
            EffectExprKind::Operation(EffectOperation::Continue(continuation)) => {
                carrier = Some((id, continuation.clone()))
            }
            EffectExprKind::Operation(EffectOperation::Handler(candidate))
                if program
                    .registry()
                    .effect(candidate.effect().effect())
                    .is_some_and(|e| e.spelling == "Checkpoint") =>
            {
                handler = Some(id)
            }
            EffectExprKind::Operation(EffectOperation::Request(candidate))
                if program
                    .registry()
                    .effect(candidate.effect().effect())
                    .is_some_and(|e| e.spelling == "Checkpoint") =>
            {
                request = Some(id)
            }
            _ => {}
        }
        pending.extend((0..node.kind.child_count()).filter_map(|i| node.kind.child_at(i)));
    }
    let (region, (carrier_node, carrier), handler, request) = (
        region.unwrap(),
        carrier.unwrap(),
        handler.unwrap(),
        request.unwrap(),
    );
    let EffectExprKind::Operation(EffectOperation::Request(checkpoint)) =
        &program.node(request).unwrap().kind
    else {
        panic!("checkpoint request")
    };
    let branch = checkpoint.operand();
    let EffectExprKind::Pure(PureExprKind::Variable(store_variable)) =
        &program.node(carrier.store).unwrap().kind
    else {
        panic!("store variable")
    };
    let EffectExprKind::Pure(PureExprKind::Variable(key_variable)) =
        &program.node(carrier.key).unwrap().kind
    else {
        panic!("key variable")
    };
    let (store_binder, key_binder) = (store_variable.binder(), key_variable.binder());
    let activation = ActivationKey(7);
    let consumer = || {
        let mut machine = Machine::new_effect(&program);
        let scope = machine.region_scope(region).unwrap();
        let (identity, access, default_handler) =
            (scope.identity(), scope.access().id(), scope.body());
        let selected = ActivationKey(9);
        let mut environment = Environment::new();
        environment.instantiation = environment
            .instantiation
            .acquire(identity, selected, &mut machine.instantiation_work, None)
            .unwrap();
        environment = environment
            .extend(access, Value::RegionView(selected))
            .unwrap();
        machine.frames.push(Frame::RegionBoundary {
            node: region,
            key: selected,
            allocate: Value::RegionHostFunction {
                owner: selected,
                release: false,
            },
            release: Value::RegionHostFunction {
                owner: selected,
                release: true,
            },
            preceding: Value::Unit,
            records: Vec::new(),
        });
        machine.frames.push(Frame::HandlerBoundary {
            node: default_handler,
            environment: environment.clone(),
            registration: None,
            retained: None,
        });
        machine.frames.push(Frame::ResourceBoundary {
            node: program.root(),
            key: activation,
            payload: ResourcePayload::Store(Box::new(RetainedStore::new(
                activation,
                test_store_api(),
            ))),
        });
        machine.live_resources = 1;
        (machine, environment, access)
    };
    let (mut machine, environment, access) = consumer();
    machine.control.take();
    let branch_environment = environment
        .clone()
        .extend(access, Value::RegionView(ActivationKey(99)))
        .unwrap();
    machine
        .begin_retained_root(handler, activation, branch_environment.clone())
        .unwrap();
    machine.control.take();
    // The checkpoint occurs in an already running cleanup. Its continuation
    // must finish that action once and then return the saved body result.
    machine.frames.push(saved(77));
    machine.live_cleanups = 1;
    machine.frames.push(Frame::Bind {
        binder: carrier.adapter.answer.id(),
        body: branch,
        environment: branch_environment,
    });
    let handler_id = machine.handler(handler).unwrap().id();
    let owner = machine.handler(handler).unwrap().clauses()[0].resume();
    machine
        .return_request(request, &Instantiation::default(), Value::Unit)
        .unwrap();
    machine.control.take();
    machine.retain_selected(handler_id, owner).unwrap();
    let Some(Control::Return(Value::RetainedKey(key))) = machine.control.take() else {
        panic!("key")
    };
    let clause = machine.frames.pop().unwrap();
    machine.return_from(clause, Value::Unit).unwrap();
    machine.control.take();
    let completion = machine.frames.pop().unwrap();
    machine.return_from(completion, Value::Unit).unwrap();
    machine.control.take();
    assert_eq!(machine.captured_cells, 3);
    assert_eq!(machine.live_cleanups, 1);

    let caller = environment
        .clone()
        .extend(store_binder, Value::ResourceHandle(activation))
        .unwrap()
        .extend(key_binder, Value::RetainedKey(key))
        .unwrap();
    machine_test_hooks::FAIL_CONTROL_RESERVATION.set(Some(ResourceFailureCause::AllocatorRefused));
    assert!(
        machine
            .continue_retained(carrier_node, caller.clone(), activation, key)
            .is_err()
    );
    machine_test_hooks::reset();
    assert_eq!(machine.captured_cells, 3);
    assert_eq!(machine.live_cleanups, 1);
    let Frame::ResourceBoundary {
        payload: ResourcePayload::Store(store),
        ..
    } = &machine.frames[2]
    else {
        panic!("store")
    };
    assert!(store.slots[key.slot].continuation.is_some());
    assert_eq!(store.active_roots, 0);
    machine.control = Some(Control::Evaluate(carrier_node, caller));
    let result = machine.run_loop().unwrap();
    assert_eq!(result.value.to_string(), "Some(77)");
    assert_eq!(machine.captured_cells, 0);
    assert_eq!(machine.live_cleanups, 0);
    assert_eq!(machine.live_resources, 0);
    assert_eq!(machine.next_region_invocation, 1);
    let entered = |node| {
        result
            .trace
            .iter()
            .position(|event| *event == TraceEvent::Enter(node))
    };
    assert!(entered(carrier.store).unwrap() < entered(carrier.key).unwrap());
    assert!(entered(carrier.key).unwrap() < entered(branch).unwrap());
    assert!(entered(branch).unwrap() < entered(carrier.adapter.some).unwrap());
    assert!(entered(carrier.adapter.none).is_none());
    assert_eq!(
        result
            .trace
            .iter()
            .filter(|event| **event == TraceEvent::Enter(branch))
            .count(),
        1,
        "restoration completes the running cleanup exactly once"
    );

    let (mut missing, environment, _) = consumer();
    let Frame::ResourceBoundary {
        payload: ResourcePayload::Store(store),
        ..
    } = &mut missing.frames[2]
    else {
        panic!("store")
    };
    store.slots.push(RetainedSlot {
        generation: key.generation,
        continuation: None,
    });
    let caller = environment
        .extend(store_binder, Value::ResourceHandle(activation))
        .unwrap()
        .extend(key_binder, Value::RetainedKey(key))
        .unwrap();
    missing.control = Some(Control::Evaluate(carrier_node, caller));
    let result = missing.run_loop().unwrap();
    assert_eq!(result.value.to_string(), "None");
    assert_eq!(missing.next_region_invocation, 1);
    assert!(
        result
            .trace
            .iter()
            .any(|event| *event == TraceEvent::Enter(carrier.adapter.none))
    );
    assert!(
        !result
            .trace
            .iter()
            .any(|event| *event == TraceEvent::Enter(branch)
                || *event == TraceEvent::Enter(carrier.adapter.some))
    );
}

#[test]
fn retained_move_prepares_storage_before_taking_either_owner() {
    let mut store = RetainedStore::new(ActivationKey(3), test_store_api());
    let mut owner = Some(CapturedContinuation {
        frames: vec![saved(11)],
    });
    let mut work = TypeWorkBudget::default();
    let mut no_work = TypeWorkBudget::with_limit(0);
    assert!(store.retain(&mut owner, &mut no_work).is_err());
    assert!(owner.is_some());
    assert!(store.slots.is_empty());
    // The slot reservation can succeed before capture inspection runs out of
    // work; this must still leave the owner and published slot set unchanged.
    let mut inspection_work = TypeWorkBudget::with_limit(1);
    assert!(store.retain(&mut owner, &mut inspection_work).is_err());
    assert!(owner.is_some());
    assert!(store.slots.is_empty());
    machine_test_hooks::FAIL_CONTROL_RESERVATION.set(Some(ResourceFailureCause::AllocatorRefused));
    assert!(store.retain(&mut owner, &mut work).is_err());
    machine_test_hooks::reset();
    assert!(owner.is_some());
    assert!(store.slots.is_empty());

    let key = store.retain(&mut owner, &mut work).unwrap();
    assert!(owner.is_none());
    let mut captured_cells = 1;
    let mut frames = vec![saved(1)];
    machine_test_hooks::FAIL_CONTROL_RESERVATION.set(Some(ResourceFailureCause::AllocatorRefused));
    assert!(
        store
            .restore(key, &mut frames, saved(2), &mut captured_cells, &mut work)
            .is_err()
    );
    machine_test_hooks::reset();
    assert_eq!(frames.len(), 1);
    assert_eq!(captured_cells, 1);
    assert!(store.slots[0].continuation.is_some());
    assert!(
        store
            .restore(key, &mut frames, saved(2), &mut captured_cells, &mut work)
            .unwrap()
    );
    assert_eq!(captured_cells, 0);
}

#[test]
fn retained_move_rejects_its_owner_inside_nested_captures() {
    let program = super::tests::effect_program("main : Unit -> Int\nmain () = 42\n");
    let node = program.root();
    let key = ActivationKey(3);
    let mut store = RetainedStore::new(key, test_store_api());
    let nested = CapturedContinuation {
        frames: vec![Frame::ResourceBoundary {
            node,
            key,
            payload: ResourcePayload::Store(Box::new(RetainedStore::new(key, test_store_api()))),
        }],
    };
    let mut owner = Some(CapturedContinuation {
        frames: vec![Frame::ClauseBoundary {
            retained: None,
            handler: HandlerId::new(1),
            owner: ResumeId::new(1),
            continuation: Some(nested),
            registration: None,
            completion_count: 1,
        }],
    });
    let result = store.retain(&mut owner, &mut TypeWorkBudget::default());
    assert!(matches!(result, Err(RuntimeFailure::InvalidControlState)));
    assert!(owner.is_some());
    assert!(store.slots.is_empty());
}

#[test]
fn retained_store_edges_are_disposed_without_recursive_stack_growth() {
    let program = super::tests::effect_program("main : Unit -> Int\nmain () = 42\n");
    let node = program.root();
    let api = test_store_api();
    std::thread::Builder::new()
        .stack_size(64 * 1024)
        .spawn(move || {
            let mut captured = CapturedContinuation { frames: Vec::new() };
            for index in 0..10_000_u32 {
                let key = ActivationKey(index);
                let store = RetainedStore {
                    active_roots: 0,
                    activation: key,
                    api,
                    slots: vec![RetainedSlot {
                        generation: 0,
                        continuation: Some(captured),
                    }],
                };
                captured = CapturedContinuation {
                    frames: vec![Frame::ResourceBoundary {
                        node,
                        key,
                        payload: ResourcePayload::Store(Box::new(store)),
                    }],
                };
            }
            drop(captured);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn retained_store_disposal_reports_incomplete_without_retrying_growth() {
    let program = super::tests::effect_program("main : Unit -> Int\nmain () = 42\n");
    let node = program.root();
    let api = test_store_api();
    let payload: Arc<[u8]> = Arc::from(&b"retained"[..]);
    let forest = || {
        let slots = (0..12)
            .map(|_| RetainedSlot {
                generation: 0,
                continuation: Some(CapturedContinuation {
                    frames: vec![Frame::CleanupCompletion {
                        saved: Value::Bytes(Arc::clone(&payload)),
                    }],
                }),
            })
            .collect();
        CapturedContinuation {
            frames: vec![Frame::ResourceBoundary {
                node,
                key: ActivationKey(3),
                payload: ResourcePayload::Store(Box::new(RetainedStore {
                    active_roots: 0,
                    activation: ActivationKey(3),
                    api,
                    slots,
                })),
            }],
        }
    };
    drop(forest());
    assert_eq!(Arc::strong_count(&payload), 1);

    let captured = forest();
    let scope = disposal::Scope::enter();
    disposal::reset_growth_attempts();
    machine_test_hooks::FAIL_DISPOSAL_GROWTH.set(true);
    drop(captured);
    assert!(disposal::check().is_err());
    assert_eq!(disposal::growth_attempts(), 1);
    let RuntimeFailure::Report(report) = scope.finish(Ok::<_, RuntimeFailure>(())).unwrap_err()
    else {
        panic!("incomplete disposal should report its resource failure");
    };
    let details = report.primary.resource().unwrap();
    assert_eq!(details.phase, RuntimePhase::Teardown);
    assert_eq!(details.resource, RuntimeResource::CapturedDisposal);
    assert_eq!(details.cause, ResourceFailureCause::AllocatorRefused);
    assert_eq!(report.cleanup, super::super::CleanupStatus::Incomplete);
    // The failed teardown abandons the residual owners; it does not release
    // any of these values a second time or execute their saved cleanups.
    assert_eq!(Arc::strong_count(&payload), 13);
    machine_test_hooks::reset();
}

#[test]
fn retained_locators_cannot_replay_or_cross_store_generations() {
    let mut store = RetainedStore::new(ActivationKey(3), test_store_api());
    let mut work = TypeWorkBudget::default();
    let mut first = Some(CapturedContinuation {
        frames: vec![saved(1)],
    });
    let old = store.retain(&mut first, &mut work).unwrap();
    let mut frames = Vec::new();
    let mut captured_cells = 1;
    let foreign = RetainedKey {
        activation: ActivationKey(4),
        ..old
    };
    assert!(
        !store
            .restore(
                foreign,
                &mut frames,
                saved(2),
                &mut captured_cells,
                &mut work
            )
            .unwrap()
    );
    assert!(
        store
            .restore(old, &mut frames, saved(2), &mut captured_cells, &mut work)
            .unwrap()
    );

    let mut second = Some(CapturedContinuation {
        frames: vec![saved(3)],
    });
    let current = store.retain(&mut second, &mut work).unwrap();
    assert_ne!(old.generation, current.generation);
    captured_cells = 1;
    assert!(
        !store
            .restore(old, &mut frames, saved(4), &mut captured_cells, &mut work)
            .unwrap()
    );
    assert!(
        store
            .restore(
                current,
                &mut frames,
                saved(4),
                &mut captured_cells,
                &mut work
            )
            .unwrap()
    );

    store.slots[0].generation = u64::MAX;
    let mut third = Some(CapturedContinuation {
        frames: vec![saved(5)],
    });
    let fresh = store.retain(&mut third, &mut work).unwrap();
    assert_ne!(fresh.slot, old.slot);
    captured_cells = 1;
    assert!(
        !store
            .restore(old, &mut frames, saved(6), &mut captured_cells, &mut work)
            .unwrap()
    );
    assert!(
        store
            .restore(fresh, &mut frames, saved(6), &mut captured_cells, &mut work)
            .unwrap()
    );
}
