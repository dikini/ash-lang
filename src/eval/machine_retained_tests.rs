//! Focused ownership tests for the retained-control store's actual frame moves.

use super::*;

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
                handler: HandlerId::new(1),
                owner: ResumeId::new(1),
                continuation: Some(CapturedContinuation {
                    frames: vec![Frame::CloseCompletion],
                }),
                registration: None,
                completion_count: 1,
            },
            Frame::ClauseBoundary {
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
    let mut store = RetainedStore::new(ActivationKey(7));
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
    let mut store = RetainedStore::new(ActivationKey(7));
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

#[test]
fn retained_move_prepares_storage_before_taking_either_owner() {
    let mut store = RetainedStore::new(ActivationKey(3));
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
    let mut store = RetainedStore::new(key);
    let nested = CapturedContinuation {
        frames: vec![Frame::ResourceBoundary {
            node,
            key,
            payload: ResourcePayload::Store(Box::new(RetainedStore::new(key))),
        }],
    };
    let mut owner = Some(CapturedContinuation {
        frames: vec![Frame::ClauseBoundary {
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
    std::thread::Builder::new()
        .stack_size(64 * 1024)
        .spawn(move || {
            let mut captured = CapturedContinuation { frames: Vec::new() };
            for index in 0..10_000_u32 {
                let key = ActivationKey(index);
                let store = RetainedStore {
                    activation: key,
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
                    activation: ActivationKey(3),
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
    let mut store = RetainedStore::new(ActivationKey(3));
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
