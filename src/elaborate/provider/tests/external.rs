use super::*;

pub(super) struct HelperFixture {
    pub(super) fixture: Fixture,
    path: std::path::PathBuf,
    pub(super) globals: HashMap<String, BinderId>,
}
impl Drop for HelperFixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}
impl HelperFixture {
    pub(super) fn new(source: &str, helper: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "ash-provider-external-{}-{}",
            std::process::id(),
            IDS.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        fs::write(path.join("helper.ash"), helper).unwrap();
        fs::write(path.join("entry.ash"), source).unwrap();
        let roots = ModuleRoots::empty().with_foreign_registrations(
            ForeignRegistrations::new([
                sqlite_manifest(ForeignRegistrationId::new(991)).unwrap(),
                crate::foreign::provider_manifest(ForeignRegistrationId::new(992)).unwrap(),
            ])
            .unwrap(),
        );
        let graph = load_module_graph(&path.join("entry.ash"), &roots).unwrap();
        let mut checked = Vec::<CheckedModule>::new();
        let mut entry = None;
        let mut globals = HashMap::new();
        for module in graph.modules() {
            let dependencies = module
                .dependencies()
                .iter()
                .map(|edge| {
                    DependencyExports::new(
                        edge,
                        checked
                            .iter()
                            .find(|checked| checked.module() == edge.target())
                            .unwrap()
                            .exports(),
                    )
                    .unwrap()
                })
                .collect::<Vec<_>>();
            let resolved = resolve_module(module, &dependencies).unwrap();
            if module.id() == graph.entry() {
                entry = Some(resolved);
                break;
            }
            let module = check_module(resolved).unwrap();
            globals.extend(
                module
                    .schemes()
                    .iter()
                    .map(|scheme| (scheme.spelling.clone(), scheme.binder)),
            );
            checked.push(module);
        }
        Self {
            fixture: Fixture {
                graph,
                resolved: entry.unwrap(),
            },
            path,
            globals,
        }
    }
    fn check(
        &self,
        draft: &LifecycleTemplateDraft,
        work: &mut TypeWorkBudget,
    ) -> Result<(), LifecycleDraftCheckError> {
        let fixture = &self.fixture;
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
        draft.check_plain_externals(
            &fixture.resolved.resources()[0],
            fixture.resolved.imported_facts(),
            &sources,
            &modules,
            &fixture.elaborator().registry,
            work,
        )
    }
    fn staged_draft(&self, phase: Phase) -> LifecycleTemplateDraft {
        let f = &self.fixture;
        let header = f
            .elaborator()
            .check_provider_header(&f.resolved, &f.resolved.resources()[0])
            .unwrap();
        f.elaborator()
            .compile_provider_lifecycle_with_externals(
                &f.resolved.resources()[0],
                &header,
                phase,
                f.resolved.imported_facts(),
            )
            .unwrap()
    }
    fn check_staged(
        &self,
        draft: &LifecycleTemplateDraft,
        work: &mut TypeWorkBudget,
    ) -> Result<(), LifecycleDraftCheckError> {
        let f = &self.fixture;
        let sources = f
            .graph
            .modules()
            .iter()
            .map(|module| module.source())
            .collect::<Vec<_>>();
        let modules = f
            .graph
            .modules()
            .iter()
            .map(|module| (module.id(), module.source().id()))
            .collect::<Vec<_>>();
        draft.check_staged_externals(
            &f.resolved.resources()[0],
            f.resolved.imported_facts(),
            &sources,
            &modules,
            &f.elaborator().registry,
            work,
        )
    }
    fn draft(&self, phase: Phase) -> LifecycleTemplateDraft {
        let fixture = &self.fixture;
        let header = fixture
            .elaborator()
            .check_provider_header(&fixture.resolved, &fixture.resolved.resources()[0])
            .unwrap();
        fixture
            .elaborator()
            .compile_provider_lifecycle(&fixture.resolved.resources()[0], &header, phase)
            .unwrap()
    }
}

const HELPER: &str = "pub identity<A> : A -> A\nidentity value = value\n";

#[test]
fn lifecycle_owned_admission_survives_defining_source_disposal_with_original_slots() {
    let source = SOURCE
        .replace(
            "import @foreign.sqlite as Native",
            "import @foreign.sqlite as Native\nimport helper as Helper\nimport helper (impl Pass, impl Stamp)",
        )
        .replace(
            "perform Native.Connection<R>.open config",
            "perform Native.Connection<R>.open (Helper.normalize config)",
        );
    let fixture = HelperFixture::new(&source, CONSTRAINED_HELPER);
    let draft = fixture.staged_draft(Phase::Acquire);
    let original = draft
        .staged_externals
        .as_ref()
        .unwrap()
        .occurrences
        .iter()
        .flat_map(|occurrence| {
            occurrence
                .occurrence
                .evidence
                .iter()
                .map(|slot| slot.storage_id())
        })
        .collect::<Vec<_>>();
    assert_eq!(original.len(), 2);
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
    let checked = draft
        .admit(
            &fixture.fixture.resolved,
            &sources,
            &modules,
            &mut TypeWorkBudget::unbounded(),
        )
        .unwrap();
    let template = checked.draft.id;
    drop(sources);
    drop(fixture);
    for _ in 0..256 {
        let churn = vec![0_u8; 8192];
        std::hint::black_box(churn);
    }
    assert_eq!(checked.draft.id, template);
    assert!(checked.canonical.foreign_modules().next().is_some());
    let retained = checked
        .draft
        .staged_externals
        .as_ref()
        .unwrap()
        .occurrences
        .iter()
        .flat_map(|occurrence| {
            occurrence
                .occurrence
                .evidence
                .iter()
                .map(|slot| slot.storage_id())
        })
        .collect::<Vec<_>>();
    assert_eq!(retained, original);
    assert!(
        checked
            .draft
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
const NOISY_IDENTITY_HELPER: &str = "pub effect Noise {\nask : Unit -> Unit\n}\npub identity<A> : A -> A\nidentity value = {\nlet ignored = handle (perform Noise.ask ()) with Noise {\nask () => resume ()\n}\nvalue\n}\n";

#[test]
fn lifecycle_owned_admission_has_exact_shared_work_and_refuses_transplanted_binders() {
    let fixture = HelperFixture::new(&constrained_source(), CONSTRAINED_HELPER);
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
    for phase in [Phase::Acquire, Phase::Finish] {
        let mut measured = TypeWorkBudget::unbounded();
        let checked = fixture
            .staged_draft(phase)
            .admit(&fixture.fixture.resolved, &sources, &modules, &mut measured)
            .unwrap();
        let cost = measured.used();
        assert!(cost > 0);
        assert_eq!(
            checked.associations.len(),
            fixture.fixture.resolved.resources().len()
        );
        drop(checked);
        for prefix in [0, 19] {
            for allowance in [cost - 1, cost] {
                for _ in 0..2 {
                    let draft = fixture.staged_draft(phase);
                    let slots = draft
                        .staged_externals
                        .as_ref()
                        .unwrap()
                        .occurrences
                        .iter()
                        .flat_map(|occurrence| occurrence.occurrence.evidence.iter())
                        .map(|slot| slot.retain_unpublished().unwrap())
                        .collect::<Vec<_>>();
                    assert!(!slots.is_empty());
                    let mut work = TypeWorkBudget::with_limit(prefix + allowance);
                    work.charge(prefix).unwrap();
                    let result =
                        draft.admit(&fixture.fixture.resolved, &sources, &modules, &mut work);
                    if allowance == cost {
                        assert!(result.is_ok());
                        assert_eq!(work.used(), prefix + cost);
                    } else {
                        assert!(result.is_err());
                    }
                    assert!(slots.iter().all(|slot| slot.selection().is_none()));
                }
            }
        }
        let mut changed = fixture.staged_draft(phase);
        changed.hidden_answer = changed.formal_parameters[0].1;
        assert!(
            changed
                .admit(
                    &fixture.fixture.resolved,
                    &sources,
                    &modules,
                    &mut TypeWorkBudget::unbounded()
                )
                .is_err()
        );
    }
}
const CONSTRAINED_HELPER: &str = concat!(
    "import @foreign.sqlite as Native\n",
    "pub interface Pass<A> {\nfirst : A -> A\nsecond : A -> A\n}\n",
    "pub interface Stamp<A> {\nstamp : (A, Int) -> A\n}\n",
    "pub impl Pass<Native.OpenConfig> {\nfirst value = value\nsecond value = value\n}\n",
    "pub impl Stamp<Native.OpenConfig> {\nstamp (value, ignored) = value\n}\n",
    "pub impl Pass<Native.CloseError> {\nfirst value = value\nsecond value = value\n}\n",
    "pub impl Stamp<Native.CloseError> {\nstamp (value, ignored) = value\n}\n",
    "pub normalize<A> : A -> A where Pass<A>, Stamp<A>\n",
    "normalize value = stamp ((second (first value), 7))\n",
);

pub(super) fn nested_constrained_helper() -> String {
    let mut helper = String::from(concat!(
        "import @foreign.sqlite as Native\n",
        "pub type Box<A> = Box(A)\n",
        "pub interface Pass<X> {\nfirst<B> : (X, B) -> X\nsecond : X -> X\nthird : X -> X\n}\n",
        "pub interface Stamp<X> {\nstamp : (X, Int) -> X\n}\n",
        "pub impl<A> Pass<Box<A>> where Pass<A> {\nfirst (Box value, ignored) = Box(first((value, ignored)))\nsecond (Box value) = Box(second value)\nthird (Box value) = Box(third value)\n}\n",
        "pub impl<A> Stamp<Box<A>> where Stamp<A> {\nstamp (Box value, tag) = Box(stamp((value, tag)))\n}\n",
    ));
    for ty in ["Native.OpenConfig", "Native.CloseError", "Bytes"] {
        helper.push_str(&format!("pub impl Pass<{ty}> {{\nfirst (value, ignored) = value\nsecond value = value\nthird value = value\n}}\npub impl Stamp<{ty}> {{\nstamp (value, ignored) = value\n}}\n"));
    }
    helper.push_str("pub normalize<X> : X -> X where Pass<X>, Stamp<X>\nnormalize value = stamp ((third(second(first((first((value, true)), ())))), 7))\n");
    helper
}

fn nested_normalize(value: &str, alias: &str) -> String {
    format!(
        "(match {alias}.normalize ({alias}.Box ({alias}.Box {value})) {{\n{alias}.Box({alias}.Box(mapped)) => mapped\n}})"
    )
}

#[test]
fn provider_external_nested_parameterized_data_prerequisites_and_method_arguments() {
    let source = constrained_source()
        .replace(
            "Helper.normalize config",
            &nested_normalize("config", "Helper"),
        )
        .replace(
            "Helper.normalize error",
            &nested_normalize("error", "Helper"),
        );
    let source = source
        .replace("helper as Helper", "helper as Renamed")
        .replace("Helper.", "Renamed.");
    let fixture = HelperFixture::new(&source, &nested_constrained_helper());
    fs::remove_file(fixture.path.join("helper.ash")).unwrap();
    for phase in [Phase::Acquire, Phase::Finish] {
        let f = &fixture.fixture;
        let definition = &f.resolved.resources()[0];
        let header = f
            .elaborator()
            .check_provider_header(&f.resolved, definition)
            .unwrap();
        let mut compiler = f.elaborator();
        compiler.type_work = TypeWorkBudget::unbounded();
        let draft = compiler
            .compile_provider_lifecycle_with_externals(
                definition,
                &header,
                phase,
                f.resolved.imported_facts(),
            )
            .unwrap();
        let mut measured = TypeWorkBudget::unbounded();
        fixture.check_staged(&draft, &mut measured).unwrap();
        let cost = measured.used();
        eprintln!(
            "B3 {phase:?} cumulative check={cost}, compile={}",
            draft.compile_work
        );
        for prefix in [0, 17] {
            let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
            short.charge(prefix).unwrap();
            assert!(fixture.check_staged(&draft, &mut short).is_err());
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                exact.charge(prefix).unwrap();
                fixture.check_staged(&draft, &mut exact).unwrap();
                assert_eq!(exact.used(), prefix + cost);
            }
        }
        let f = &fixture.fixture;
        let definition = &f.resolved.resources()[0];
        let header = f
            .elaborator()
            .check_provider_header(&f.resolved, definition)
            .unwrap();
        for prefix in [0, 17] {
            for allowance in [draft.compile_work - 1, draft.compile_work] {
                let mut compiler = f.elaborator();
                compiler.type_work = TypeWorkBudget::with_limit(prefix + allowance);
                compiler.type_work.charge(prefix).unwrap();
                let result = compiler.compile_provider_lifecycle_with_externals(
                    definition,
                    &header,
                    phase,
                    f.resolved.imported_facts(),
                );
                if allowance == draft.compile_work {
                    let exact = result.unwrap();
                    assert_eq!(exact.compile_work, prefix + draft.compile_work);
                    fixture
                        .check_staged(&exact, &mut TypeWorkBudget::unbounded())
                        .unwrap();
                } else {
                    assert!(
                        matches!(
                            result,
                            Err(TypeError::Internal(
                                ElaborationFailure::TypeResourceExhausted
                            ))
                        ),
                        "bounded B3 compile must refuse one-short"
                    );
                }
            }
        }
        let retained = &draft.staged_externals.as_ref().unwrap().occurrences;
        assert!(retained.iter().all(|o| {
            o.occurrence.global_binder() == Some(fixture.globals["normalize"])
                && o.occurrence
                    .evidence
                    .iter()
                    .all(|slot| slot.selection().is_none())
        }));
    }
}

#[test]
fn provider_external_constrained_helper_stages_checked_occurrences_in_both_phases() {
    let fixture = HelperFixture::new(
        &source()
            .replace("Helper.identity", "Helper.normalize")
            .replace(
                "import helper as Helper",
                "import helper as Helper\nimport helper (impl Pass, impl Stamp)",
            ),
        CONSTRAINED_HELPER,
    );
    for phase in [Phase::Acquire, Phase::Finish] {
        let f = &fixture.fixture;
        let header = f
            .elaborator()
            .check_provider_header(&f.resolved, &f.resolved.resources()[0])
            .unwrap();
        let draft = f
            .elaborator()
            .compile_provider_lifecycle_with_externals(
                &f.resolved.resources()[0],
                &header,
                phase,
                f.resolved.imported_facts(),
            )
            .unwrap();
        assert!(
            fixture
                .check(&draft, &mut TypeWorkBudget::unbounded())
                .is_err()
        );
        let sources = f
            .graph
            .modules()
            .iter()
            .map(|module| module.source())
            .collect::<Vec<_>>();
        let modules = f
            .graph
            .modules()
            .iter()
            .map(|module| (module.id(), module.source().id()))
            .collect::<Vec<_>>();
        draft
            .check_staged_externals(
                &f.resolved.resources()[0],
                f.resolved.imported_facts(),
                &sources,
                &modules,
                &f.elaborator().registry,
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap();
    }
}
fn source() -> String {
    SOURCE.replace("pub type Completion", "import helper as Helper\npub type Completion").replace(".open config", ".open (Helper.identity config)").replace("finish state => perform Native.Connection<R>.close state", "finish state => match perform Native.Connection<R>.close state {\nNative.Consumed => Native.Consumed\nNative.ConsumedFailure(error) => Native.ConsumedFailure (Helper.identity error)\nNative.Retained(state, error) => Native.Retained(state, Helper.identity error)\n}")
}

#[test]
fn provider_external_plain_helper_uses_checked_generic_source_in_both_phases() {
    let fixture = HelperFixture::new(&source(), HELPER);
    for phase in [Phase::Acquire, Phase::Finish] {
        let draft = fixture.draft(phase);
        assert!(
            draft
                .check_flow(
                    &fixture.fixture.resolved.resources()[0],
                    &mut TypeWorkBudget::unbounded()
                )
                .is_err()
        );
        fixture
            .check(&draft, &mut TypeWorkBudget::unbounded())
            .unwrap();
    }
}

#[test]
fn provider_external_plain_helper_has_cumulative_exact_budget_and_fresh_retry() {
    let fixture = HelperFixture::new(&source(), HELPER);
    let draft = fixture.draft(Phase::Acquire);
    let mut measured = TypeWorkBudget::unbounded();
    fixture.check(&draft, &mut measured).unwrap();
    let cost = measured.used();
    eprintln!("provider external Acquire cumulative cost={cost}");
    for prefix in [0, 13] {
        let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
        short.charge(prefix).unwrap();
        assert!(fixture.check(&draft, &mut short).is_err());
        for _ in 0..2 {
            let mut exact = TypeWorkBudget::with_limit(prefix + cost);
            exact.charge(prefix).unwrap();
            fixture.check(&draft, &mut exact).unwrap();
            assert_eq!(exact.used(), prefix + cost);
        }
    }
}

#[test]
fn provider_external_plain_helper_does_not_transport_current_state() {
    let source = source().replace(".close state {", ".close (Helper.identity state) {");
    let fixture = HelperFixture::new(&source, HELPER);
    let f = &fixture.fixture;
    let header = f
        .elaborator()
        .check_provider_header(&f.resolved, &f.resolved.resources()[0])
        .unwrap();
    assert!(
        f.elaborator()
            .compile_provider_lifecycle(&f.resolved.resources()[0], &header, Phase::Finish)
            .is_err()
    );
}

#[test]
fn provider_external_plain_helper_does_not_admit_missing_import_authority() {
    let fixture = HelperFixture::new(&source(), HELPER);
    let draft = fixture.draft(Phase::Acquire);
    let f = &fixture.fixture;
    let sources = f
        .graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let modules = f
        .graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    assert!(
        draft
            .check_plain_externals(
                &f.resolved.resources()[0],
                &crate::resolved::ImportedFacts::default(),
                &sources,
                &modules,
                &f.elaborator().registry,
                &mut TypeWorkBudget::unbounded()
            )
            .is_err()
    );
}

#[test]
fn provider_external_plain_helper_queries_only_selected_control_cone() {
    let helper = format!(
        "{HELPER}pub effect Noise {{\nask : Unit -> Unit\n}}\npub noisy : Unit -> Unit ! {{Noise}}\nnoisy () = perform Noise.ask ()\n"
    );
    let fixture = HelperFixture::new(&source(), &helper);
    fixture
        .check(
            &fixture.draft(Phase::Acquire),
            &mut TypeWorkBudget::unbounded(),
        )
        .unwrap();
}

#[test]
fn provider_external_plain_helper_rejects_selected_handled_control() {
    let helper = "pub effect Noise {\nask : Unit -> Unit\n}\npub identity<A> : A -> A\nidentity value = {\nlet ignored = handle (perform Noise.ask ()) with Noise {\nask () => resume ()\n}\nvalue\n}\n";
    let fixture = HelperFixture::new(&source(), helper);
    assert!(
        fixture
            .check(
                &fixture.draft(Phase::Acquire),
                &mut TypeWorkBudget::unbounded()
            )
            .is_err()
    );
}

#[test]
fn provider_external_plain_local_forwarder_uses_actual_source_call_relation() {
    let noisy = "pub effect Noise {\nask : Unit -> Unit\n}\npub identity<A> : A -> A\nidentity value = {\nlet ignored = handle (perform Noise.ask ()) with Noise {\nask () => resume ()\n}\nvalue\n}\n";
    let forwarded_source = source()
        .replace("Helper.identity config", "{\nlet forward : Native.OpenConfig -> Native.OpenConfig = fn(value) {\nHelper.identity value\n}\nforward config\n}")
        .replace("Helper.identity error", "{\nlet forward : Native.CloseError -> Native.CloseError = fn(value) {\nHelper.identity value\n}\nforward error\n}");
    let forwarded_source = forwarded_source.replace("Helper", "Renamed");
    let mut failures = Vec::new();
    for (label, helper) in [("pure", HELPER), ("noisy", noisy)] {
        let direct = HelperFixture::new(&source(), helper);
        let forwarded = HelperFixture::new(&forwarded_source, helper);
        fs::remove_file(forwarded.path.join("helper.ash")).unwrap();
        for phase in [Phase::Acquire, Phase::Finish] {
            let direct_raw = direct.draft(phase);
            let result = direct.check(&direct_raw, &mut TypeWorkBudget::unbounded());
            eprintln!("plain forwarding probe {label} {phase:?} direct raw check: {result:?}");
            assert_eq!(result.is_ok(), label == "pure");
            let direct_staged = direct.staged_draft(phase);
            let result = direct.check_staged(&direct_staged, &mut TypeWorkBudget::unbounded());
            eprintln!("plain forwarding probe {label} {phase:?} direct staged check: {result:?}");
            assert_eq!(result.is_ok(), label == "pure");
            let f = &forwarded.fixture;
            let definition = &f.resolved.resources()[0];
            let header = f
                .elaborator()
                .check_provider_header(&f.resolved, definition)
                .unwrap();
            for staged in [false, true] {
                let mut compiler = f.elaborator();
                let draft = if staged {
                    compiler.compile_provider_lifecycle_with_externals(
                        definition,
                        &header,
                        phase,
                        f.resolved.imported_facts(),
                    )
                } else {
                    compiler.compile_provider_lifecycle(definition, &header, phase)
                };
                match draft {
                    Ok(draft) => {
                        eprintln!(
                            "plain forwarding probe {label} {phase:?} staged={staged} source compile: Ok"
                        );
                        if staged {
                            let source = match phase {
                                Phase::Acquire => &definition.acquire,
                                Phase::Finish => &definition.finish,
                                _ => unreachable!(),
                            };
                            let expected =
                                crate::elaborate::provider::external::provider_source_occurrences(
                                    source,
                                    f.resolved.imported_facts(),
                                    &mut TypeWorkBudget::unbounded(),
                                )
                                .unwrap();
                            eprintln!(
                                "plain forwarding probe {label} {phase:?} occurrence counts source={}, retained={}",
                                expected.len(),
                                draft.staged_externals.as_ref().unwrap().occurrences.len()
                            );
                        }
                        let result = if staged {
                            forwarded.check_staged(&draft, &mut TypeWorkBudget::unbounded())
                        } else {
                            forwarded.check(&draft, &mut TypeWorkBudget::unbounded())
                        };
                        eprintln!(
                            "plain forwarding probe {label} {phase:?} staged={staged} forwarded check: {result:?}"
                        );
                        let valid = if label == "pure" {
                            result.is_ok()
                        } else {
                            matches!(result, Err(LifecycleDraftCheckError::Core(ref error))
                                if error.reason() == crate::core::ValidationReason::ResourceEscape)
                        };
                        if !valid {
                            failures.push((label, phase, staged));
                        }
                    }
                    Err(error) => panic!(
                        "normally checked local forwarder {label} {phase:?} staged={staged} source failed to compile: {error:?}"
                    ),
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "actual local-call correspondence missing in {failures:?}"
    );
}

fn local_external_forwarder(input: &str, ty: &str, variant: usize) -> String {
    let arrow = format!("Native.{ty} -> Native.{ty}");
    let body = match variant {
        0 => format!(
            "let alias : {arrow} = Helper.identity\nlet forward : {arrow} = fn(value) {{\nalias value\n}}\nforward {input}"
        ),
        1 => format!(
            "let held : ((({arrow}), Unit), Unit) = ((Helper.identity, ()), ())\nlet forward : {arrow} = fn(value) {{\nmatch held {{\n((alias, ()), ()) => alias value\n}}\n}}\nforward {input}"
        ),
        2 => format!(
            "let rec forward : {arrow} = fn(value) {{\nrelay value\n}}\nand relay : {arrow} = fn(value) {{\nHelper.identity value\n}}\nforward {input}"
        ),
        3 => format!(
            "let keep : (({arrow}) -> ({arrow})) = fn(callable) {{\ncallable\n}}\nlet escaped = keep Helper.identity\nescaped {input}"
        ),
        4 => format!(
            "let make : Unit -> ({arrow}) = fn(ignored) {{\nHelper.identity\n}}\nlet escaped = make ()\nescaped {input}"
        ),
        5 => format!(
            "let held : Helper.Carrier<({arrow})> = Helper.Carrier(Helper.identity)\nlet forward : {arrow} = fn(value) {{\nmatch held {{\nHelper.Carrier(alias) => alias value\n}}\n}}\nforward {input}"
        ),
        6 => format!(
            "let keep : (((({arrow}), Unit), Unit) -> ((({arrow}), Unit), Unit)) = fn(value) {{\nvalue\n}}\nlet held = keep ((Helper.identity, ()), ())\nmatch held {{\n((alias, ()), ()) => alias {input}\n}}"
        ),
        _ => unreachable!(),
    };
    format!("{{\n{body}\n}}")
}

#[test]
fn provider_external_plain_local_dependencies_have_actual_call_proofs() {
    for (pure, helper) in [(true, HELPER), (false, NOISY_IDENTITY_HELPER)] {
        let helper = format!("{helper}pub type Carrier<A> = Carrier(A)\n");
        for variant in 0..7 {
            let source = source()
                .replace(
                    "Helper.identity config",
                    &local_external_forwarder("config", "OpenConfig", variant),
                )
                .replace(
                    "Helper.identity error",
                    &local_external_forwarder("error", "CloseError", variant),
                );
            let fixture = HelperFixture::new(&source, &helper);
            for phase in [Phase::Acquire, Phase::Finish] {
                for staged in [false, true] {
                    let draft = if staged {
                        fixture.staged_draft(phase)
                    } else {
                        fixture.draft(phase)
                    };
                    let check = |work: &mut TypeWorkBudget| {
                        if staged {
                            fixture.check_staged(&draft, work)
                        } else {
                            fixture.check(&draft, work)
                        }
                    };
                    let supported = pure && matches!(variant, 0 | 1 | 2 | 5);
                    let mut measured = TypeWorkBudget::unbounded();
                    let result = check(&mut measured);
                    assert!(
                        if supported {
                            result.is_ok()
                        } else {
                            matches!(result, Err(LifecycleDraftCheckError::Core(ref error))
                if error.reason() == crate::core::ValidationReason::ResourceEscape)
                        },
                        "local external carrier {variant} {phase:?} pure={pure} staged={staged}: {result:?}"
                    );
                    let cost = measured.used();
                    for prefix in [0, 17] {
                        let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
                        short.charge(prefix).unwrap();
                        let result = check(&mut short);
                        assert!(
                            matches!(result, Err(LifecycleDraftCheckError::Resource))
                                || matches!(result, Err(LifecycleDraftCheckError::Core(ref error))
                        if error.reason() == crate::core::ValidationReason::Resource)
                        );
                        for _ in 0..2 {
                            let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                            exact.charge(prefix).unwrap();
                            let result = check(&mut exact);
                            assert!(if supported {
                                result.is_ok()
                            } else {
                                matches!(result, Err(LifecycleDraftCheckError::Core(ref error))
                        if error.reason() == crate::core::ValidationReason::ResourceEscape)
                            });
                            assert_eq!(exact.used(), prefix + cost);
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn provider_external_plain_local_captured_data_has_actual_flow_environment() {
    for data in [false, true] {
        let capture = |input: &str, ty: &str| {
            let (held, pattern) = if data {
                (
                    format!("Helper.Carrier(({input}, 41))"),
                    "Helper.Carrier((saved, tag))",
                )
            } else {
                (format!("({input}, 41)"), "(saved, tag)")
            };
            format!(
                "{{\nlet held = {held}\nlet forward : Unit -> Native.{ty} = fn(ignored) {{\nmatch held {{\n{pattern} => Helper.identity saved\n}}\n}}\nforward ()\n}}"
            )
        };
        let source = source()
            .replace("Helper.identity config", &capture("config", "OpenConfig"))
            .replace("Helper.identity error", &capture("error", "CloseError"));
        for (pure, helper) in [(true, HELPER), (false, NOISY_IDENTITY_HELPER)] {
            let helper = format!("{helper}pub type Carrier<A> = Carrier(A)\n");
            let fixture = HelperFixture::new(&source, &helper);
            for phase in [Phase::Acquire, Phase::Finish] {
                let draft = fixture.staged_draft(phase);
                let mut measured = TypeWorkBudget::unbounded();
                let result = fixture.check_staged(&draft, &mut measured);
                assert!(
                    if pure {
                        result.is_ok()
                    } else {
                        matches!(result, Err(LifecycleDraftCheckError::Core(ref error))
                    if error.reason() == crate::core::ValidationReason::ResourceEscape)
                    },
                    "captured data={data} pure={pure} {phase:?}: {result:?}"
                );
                let cost = measured.used();
                for prefix in [0, 17] {
                    let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
                    short.charge(prefix).unwrap();
                    let refusal = fixture.check_staged(&draft, &mut short);
                    assert!(
                        matches!(refusal, Err(LifecycleDraftCheckError::Resource))
                            || matches!(refusal, Err(LifecycleDraftCheckError::Core(ref error)) if error.reason() == crate::core::ValidationReason::Resource)
                    );
                    for _ in 0..2 {
                        let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                        exact.charge(prefix).unwrap();
                        let result = fixture.check_staged(&draft, &mut exact);
                        assert_eq!(result.is_ok(), pure);
                        assert_eq!(exact.used(), prefix + cost);
                    }
                }
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
        }
    }
}

#[test]
fn provider_external_constrained_local_forwarder_has_actual_source_overlay() {
    for nested in [false, true] {
        for pure in [true, false] {
            let forward = |input: &str, ty: &str| {
                let body = if nested {
                    nested_normalize("value", "Helper")
                } else {
                    "Helper.normalize value".to_string()
                };
                format!(
                    "{{\nlet forward : Native.{ty} -> Native.{ty} = fn(value) {{\n{body}\n}}\nforward {input}\n}}"
                )
            };
            let source = constrained_source()
                .replace("Helper.normalize config", &forward("config", "OpenConfig"))
                .replace("Helper.normalize error", &forward("error", "CloseError"));
            let helper = if nested {
                nested_constrained_helper()
            } else {
                CONSTRAINED_HELPER.to_string()
            };
            let helper = if pure {
                helper
            } else {
                helper.replace("pub interface Pass", "pub effect Noise {\nask : Unit -> Unit\n}\npub interface Pass")
                .replace("normalize value = stamp ((second (first value), 7))", "normalize value = {\nlet noise = handle (perform Noise.ask ()) with Noise {\nask () => resume ()\n}\nstamp ((second (first value), 7))\n}")
                .replace("normalize value = stamp ((third(second(first((first((value, true)), ())))), 7))", "normalize value = {\nlet noise = handle (perform Noise.ask ()) with Noise {\nask () => resume ()\n}\nstamp ((third(second(first((first((value, true)), ())))), 7))\n}")
            };
            let fixture = HelperFixture::new(&source, &helper);
            fs::remove_file(fixture.path.join("helper.ash")).unwrap();
            for phase in [Phase::Acquire, Phase::Finish] {
                let draft = fixture.staged_draft(phase);
                let mut measured = TypeWorkBudget::unbounded();
                let result = fixture.check_staged(&draft, &mut measured);
                assert!(
                    if pure {
                        result.is_ok()
                    } else {
                        matches!(result, Err(LifecycleDraftCheckError::Core(ref error)) if error.reason() == crate::core::ValidationReason::ResourceEscape)
                    },
                    "constrained local nested={nested} pure={pure} {phase:?}: {result:?}"
                );
                let cost = measured.used();
                for prefix in [0, 17] {
                    let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
                    short.charge(prefix).unwrap();
                    assert!(fixture.check_staged(&draft, &mut short).is_err());
                    for _ in 0..2 {
                        let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                        exact.charge(prefix).unwrap();
                        let result = fixture.check_staged(&draft, &mut exact);
                        assert!(if pure {
                            result.is_ok()
                        } else {
                            matches!(result, Err(LifecycleDraftCheckError::Core(ref error)) if error.reason() == crate::core::ValidationReason::ResourceEscape)
                        });
                        assert_eq!(exact.used(), prefix + cost);
                    }
                }
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
        }
    }
}

#[test]
fn provider_external_constrained_local_statement_keeps_enclosing_association() {
    let source = constrained_statement_source().replace(
        "Renamed.normalize sql",
        "{\nlet forward : Bytes -> Bytes = fn(value) {\nRenamed.normalize value\n}\nforward sql\n}",
    );
    check_constrained_statement_fixture(&source, &constrained_statement_helper());
}

#[test]
fn provider_external_ordinary_pure_local_computation_remains_admitted() {
    let ordinary = |input: &str, ty: &str| {
        format!(
            "{{\nlet count : Int -> Int = fn(value) {{\nvalue + 1\n}}\nlet unused = count 41\nlet forward : Native.{ty} -> Native.{ty} = fn(value) {{\nvalue\n}}\nforward {input}\n}}"
        )
    };
    let source = source()
        .replace("Helper.identity config", &ordinary("config", "OpenConfig"))
        .replace("Helper.identity error", &ordinary("error", "CloseError"));
    let fixture = HelperFixture::new(&source, HELPER);
    for phase in [Phase::Acquire, Phase::Finish] {
        for staged in [false, true] {
            let draft = if staged {
                fixture.staged_draft(phase)
            } else {
                fixture.draft(phase)
            };
            let check = |work: &mut TypeWorkBudget| {
                if staged {
                    fixture.check_staged(&draft, work)
                } else {
                    fixture.check(&draft, work)
                }
            };
            let mut measured = TypeWorkBudget::unbounded();
            check(&mut measured).unwrap();
            let cost = measured.used();
            for prefix in [0, 17] {
                let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
                short.charge(prefix).unwrap();
                assert!(check(&mut short).is_err());
                for _ in 0..2 {
                    let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                    exact.charge(prefix).unwrap();
                    check(&mut exact).unwrap();
                    assert_eq!(exact.used(), prefix + cost);
                }
            }
        }
    }
}

#[test]
fn provider_external_plain_authenticated_alias_keeps_actual_call_relation() {
    let alias = |input: &str, ty: &str| {
        format!("{{\nlet alias : Native.{ty} -> Native.{ty} = Helper.identity\nalias {input}\n}}")
    };
    let source = source()
        .replace("Helper.identity config", &alias("config", "OpenConfig"))
        .replace("Helper.identity error", &alias("error", "CloseError"));
    let fixture = HelperFixture::new(&source, HELPER);
    for phase in [Phase::Acquire, Phase::Finish] {
        fixture
            .check(&fixture.draft(phase), &mut TypeWorkBudget::unbounded())
            .unwrap();
        fixture
            .check_staged(
                &fixture.staged_draft(phase),
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap();
    }
}

#[test]
fn provider_external_plain_helper_authenticates_full_occurrence_metadata() {
    use crate::core::provider::{ExternalMutation, mutate_external_for_test};
    let fixture = HelperFixture::new(&source(), HELPER);
    for mutation in [
        ExternalMutation::Type,
        ExternalMutation::Kind,
        ExternalMutation::Row,
    ] {
        let mut draft = fixture.draft(Phase::Acquire);
        mutate_external_for_test(&mut draft.core, fixture.globals["identity"], mutation);
        assert!(
            fixture
                .check(&draft, &mut TypeWorkBudget::unbounded())
                .is_err()
        );
    }
}

#[test]
fn provider_external_plain_helper_rejects_private_and_unimported_globals() {
    use crate::core::provider::{ExternalMutation, mutate_external_for_test};
    let helper = format!(
        "{HELPER}private<A> : A -> A\nprivate value = value\npub absent<A> : A -> A\nabsent value = value\n"
    );
    let source = source()
        .replace("import helper as Helper", "import helper (identity)")
        .replace("Helper.identity", "identity");
    let fixture = HelperFixture::new(&source, &helper);
    for spelling in ["private", "absent"] {
        let mut draft = fixture.draft(Phase::Acquire);
        mutate_external_for_test(
            &mut draft.core,
            fixture.globals["identity"],
            ExternalMutation::Binder(fixture.globals[spelling]),
        );
        assert!(
            fixture
                .check(&draft, &mut TypeWorkBudget::unbounded())
                .is_err(),
            "admitted {spelling}"
        );
    }
}

#[test]
fn provider_external_plain_helper_keeps_dictionary_requirement_closed() {
    let helper = "pub interface Tag<A> {\nmark : A -> A\n}\npub identity<A> : A -> A where Tag<A>\nidentity value = value\n";
    let fixture = HelperFixture::new(&source(), helper);
    let f = &fixture.fixture;
    let header = f
        .elaborator()
        .check_provider_header(&f.resolved, &f.resolved.resources()[0])
        .unwrap();
    assert!(matches!(
        f.elaborator().compile_provider_lifecycle(
            &f.resolved.resources()[0],
            &header,
            Phase::Acquire
        ),
        Err(TypeError::Internal(ElaborationFailure::InvalidState))
    ));
}

#[test]
fn provider_external_plain_helper_requirement_guard_uses_checked_import_fact() {
    let helper = "pub interface Tag<A> {\nmark : A -> A\n}\npub identity<A> : A -> A where Tag<A>\nidentity value = value\n";
    let source = SOURCE.replace(
        "pub type Completion",
        "import helper as Helper\npub type Completion",
    );
    let fixture = HelperFixture::new(&source, helper);
    let mut draft = fixture.draft(Phase::Acquire);
    let binder = fixture.globals["identity"];
    let fact = fixture
        .fixture
        .resolved
        .imported_facts()
        .global(binder)
        .unwrap();
    assert!(!fact.scheme.requirements.is_empty());
    // Forge an external source-scheme occurrence, retaining its completed
    // dependency scheme. The plain gate must refuse before structural use.
    crate::core::provider::introduce_external_for_test(&mut draft.core, binder, &fact.scheme);
    assert!(
        matches!(fixture.check(&draft, &mut TypeWorkBudget::unbounded()), Err(LifecycleDraftCheckError::Core(error)) if error.reason() == crate::core::ValidationReason::ResourceEscape)
    );
}

#[test]
fn provider_external_plain_helper_keeps_type_application_identity_through_alias() {
    let source = source().replace(
        ".open (Helper.identity config)",
        ".open ({\nlet same : Native.OpenConfig -> Native.OpenConfig = Helper.identity\nsame config\n})",
    );
    let fixture = HelperFixture::new(&source, HELPER);
    fixture
        .check(
            &fixture.draft(Phase::Acquire),
            &mut TypeWorkBudget::unbounded(),
        )
        .unwrap();
}

#[test]
fn provider_external_plain_helper_composes_with_statement_state_access_association() {
    let statement = STATEMENT.replace(
        "Provider.state_of db, sql",
        "Provider.state_of db, Helper.identity sql",
    );
    let fixture = HelperFixture::new(
        &format!(
            "import @foreign.provider as Provider\n{}\n{statement}",
            source()
        ),
        HELPER,
    );
    let f = &fixture.fixture;
    let mut checker = f.elaborator();
    let connection = &f.resolved.resources()[0];
    let statement = &f.resolved.resources()[1];
    let connection_header = checker
        .check_provider_header(&f.resolved, connection)
        .unwrap();
    let statement_header = checker
        .check_provider_header(&f.resolved, statement)
        .unwrap();
    let source_association = &connection_header.state_association;
    let draft = f
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
    let sources = f
        .graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let modules = f
        .graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    assert!(
        draft
            .check_plain_externals_with_associations(
                statement,
                f.resolved.imported_facts(),
                &sources,
                &modules,
                &f.elaborator().registry,
                &[],
                &mut TypeWorkBudget::unbounded()
            )
            .is_err()
    );
    draft
        .check_plain_externals_with_associations(
            statement,
            f.resolved.imported_facts(),
            &sources,
            &modules,
            &f.elaborator().registry,
            &[association],
            &mut TypeWorkBudget::unbounded(),
        )
        .unwrap();
    for mutation in [
        crate::core::provider::AccessMutation::Method,
        crate::core::provider::AccessMutation::Definition,
        crate::core::provider::AccessMutation::Arguments,
        crate::core::provider::AccessMutation::Operand,
        crate::core::provider::AccessMutation::Result,
        crate::core::provider::AccessMutation::Effects,
    ] {
        let mut changed = f
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
        crate::core::provider::mutate_state_access(&mut changed.core, mutation);
        assert!(
            changed
                .check_plain_externals_with_associations(
                    statement,
                    f.resolved.imported_facts(),
                    &sources,
                    &modules,
                    &f.elaborator().registry,
                    &[association],
                    &mut TypeWorkBudget::unbounded()
                )
                .is_err()
        );
    }
    for identity in [false, true] {
        let mut changed = f
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
        let mut work = TypeWorkBudget::unbounded();
        let mut registry = f
            .resolved
            .registry()
            .provider_template_view(f.resolved.imported_facts(), &mut work)
            .unwrap();
        if identity {
            registry.mutate_provider_effect_identity_for_test(f.resolved.module());
        } else {
            registry.mutate_provider_annotation_origin_for_test(Origin::Source(statement.span));
        }
        crate::core::provider::replace_external_registry_for_test(
            &mut changed.core,
            Arc::new(registry),
        );
        assert!(
            matches!(changed.check_plain_externals_with_associations(statement, f.resolved.imported_facts(), &sources, &modules, &f.elaborator().registry, &[association], &mut TypeWorkBudget::unbounded()), Err(LifecycleDraftCheckError::Core(error)) if error.reason() == crate::core::ValidationReason::Registry)
        );
    }
}

fn constrained_statement_source() -> String {
    format!(
        "import @foreign.provider as Provider\n{}\n{}",
        SOURCE.replace(
            "pub type Completion",
            "import helper as Renamed\nimport helper (impl Pass, impl Stamp)\npub type Completion"
        ),
        STATEMENT.replace(
            "Provider.state_of db, sql",
            "Provider.state_of db, Renamed.normalize sql"
        ),
    )
}

fn constrained_statement_helper() -> String {
    CONSTRAINED_HELPER.replace("Native.OpenConfig", "Bytes")
}

#[test]
fn provider_external_constrained_statement_composes_with_enclosing_state_association() {
    check_constrained_statement_fixture(
        &constrained_statement_source(),
        &constrained_statement_helper(),
    );
}

#[test]
fn provider_external_nested_statement_composes_with_enclosing_state_association() {
    let source = constrained_statement_source()
        .replace("Renamed.normalize sql", &nested_normalize("sql", "Renamed"));
    check_constrained_statement_fixture(&source, &nested_constrained_helper());
}

fn check_constrained_statement_fixture(source: &str, helper: &str) {
    let fixture = HelperFixture::new(source, helper);
    let f = &fixture.fixture;
    let mut checker = f.elaborator();
    let connection_header = checker
        .check_provider_header(&f.resolved, &f.resolved.resources()[0])
        .unwrap();
    let statement = &f.resolved.resources()[1];
    let statement_header = checker
        .check_provider_header(&f.resolved, statement)
        .unwrap();
    let source_association = &connection_header.state_association;
    let mut compiler = f.elaborator();
    compiler.type_work = TypeWorkBudget::unbounded();
    let retained_association = source_association
        .clone_with_budget(&mut compiler.type_work)
        .unwrap();
    let draft = compiler
        .compile_provider_lifecycle_with_externals_and_associations(
            statement,
            &statement_header,
            Phase::Acquire,
            f.resolved.imported_facts(),
            vec![retained_association],
        )
        .unwrap();
    let association = crate::core::provider::DraftStateAssociation {
        definition: source_association.definition,
        family: source_association.family,
        parameters: &source_association.parameters,
        state: &source_association.state,
    };
    let sources = f
        .graph
        .modules()
        .iter()
        .map(|m| m.source())
        .collect::<Vec<_>>();
    let modules = f
        .graph
        .modules()
        .iter()
        .map(|m| (m.id(), m.source().id()))
        .collect::<Vec<_>>();
    let check = |draft: &LifecycleTemplateDraft,
                 associations: &[crate::core::provider::DraftStateAssociation<'_>],
                 work: &mut TypeWorkBudget| {
        draft.check_staged_externals_with_associations(
            statement,
            f.resolved.imported_facts(),
            &sources,
            &modules,
            &f.elaborator().registry,
            associations,
            work,
        )
    };
    let mut measured = TypeWorkBudget::unbounded();
    check(&draft, &[association], &mut measured).unwrap();
    let cost = measured.used();
    eprintln!("constrained Statement acquire cumulative check cost={cost}");
    for prefix in [0, 17] {
        let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
        short.charge(prefix).unwrap();
        assert!(check(&draft, &[association], &mut short).is_err());
        for _ in 0..2 {
            let mut exact = TypeWorkBudget::with_limit(prefix + cost);
            exact.charge(prefix).unwrap();
            check(&draft, &[association], &mut exact).unwrap();
            assert_eq!(exact.used(), prefix + cost);
        }
    }
    if source.contains("let forward") {
        for unused in [false, true] {
            let mut compiler = f.elaborator();
            let retained = source_association
                .clone_with_budget(&mut compiler.type_work)
                .unwrap();
            let mut changed = compiler
                .compile_provider_lifecycle_with_externals_and_associations(
                    statement,
                    &statement_header,
                    Phase::Acquire,
                    f.resolved.imported_facts(),
                    vec![retained],
                )
                .unwrap();
            crate::core::provider::put_state_access_in_local_callable_for_test(
                &mut changed.core,
                unused,
            );
            assert!(
                check(&changed, &[association], &mut TypeWorkBudget::unbounded()).is_err(),
                "privileged local callable unused={unused}"
            );
        }
    }
    assert!(check(&draft, &[], &mut TypeWorkBudget::unbounded()).is_err());
    assert!(
        check(
            &draft,
            &[association, association],
            &mut TypeWorkBudget::unbounded()
        )
        .is_err()
    );
    let wrong_state = Type::Int;
    let wrong_parameters = [statement_header.state_association.parameters[0]];
    for changed in [
        crate::core::provider::DraftStateAssociation {
            state: &wrong_state,
            ..association
        },
        crate::core::provider::DraftStateAssociation {
            definition: statement.id,
            ..association
        },
        crate::core::provider::DraftStateAssociation {
            family: statement_header.state_association.family,
            ..association
        },
        crate::core::provider::DraftStateAssociation {
            parameters: &wrong_parameters,
            ..association
        },
    ] {
        assert!(check(&draft, &[changed], &mut TypeWorkBudget::unbounded()).is_err());
    }
    assert!(
        f.elaborator()
            .compile_provider_lifecycle_with_externals(
                statement,
                &statement_header,
                Phase::Acquire,
                f.resolved.imported_facts()
            )
            .is_err()
    );
    let compile_cost = draft.compile_work;
    eprintln!("constrained Statement acquire cumulative compile cost={compile_cost}");
    for prefix in [0, 17] {
        for allowance in [compile_cost - 1, compile_cost] {
            let mut compiler = f.elaborator();
            compiler.type_work = TypeWorkBudget::with_limit(prefix + allowance);
            compiler.type_work.charge(prefix).unwrap();
            let retained_association = source_association
                .clone_with_budget(&mut compiler.type_work)
                .unwrap();
            let result = compiler.compile_provider_lifecycle_with_externals_and_associations(
                statement,
                &statement_header,
                Phase::Acquire,
                f.resolved.imported_facts(),
                vec![retained_association],
            );
            if allowance == compile_cost {
                let exact = result.unwrap();
                assert_eq!(exact.compile_work, prefix + compile_cost);
                check(&exact, &[association], &mut TypeWorkBudget::unbounded()).unwrap();
            } else {
                assert!(matches!(
                    result,
                    Err(TypeError::Internal(
                        ElaborationFailure::TypeResourceExhausted
                    ))
                ));
            }
        }
    }
    fs::remove_file(fixture.path.join("helper.ash")).unwrap();
    check(&draft, &[association], &mut TypeWorkBudget::unbounded()).unwrap();
    let originals = super::super::external::provider_source_occurrences(
        &statement.acquire,
        f.resolved.imported_facts(),
        &mut TypeWorkBudget::unbounded(),
    )
    .unwrap();
    let retained = &draft.staged_externals.as_ref().unwrap().occurrences;
    assert_eq!(originals.len(), 1);
    assert_eq!(
        retained[0].occurrence.global_binder(),
        Some(fixture.globals["normalize"])
    );
    assert_eq!(originals[0].evidence.len(), 2);
    assert!(
        originals[0]
            .evidence
            .iter()
            .zip(&retained[0].occurrence.evidence)
            .all(|(a, b)| a.storage_id() == b.storage_id()
                && a.selection().is_none()
                && b.selection().is_none())
    );
}

#[test]
fn provider_external_constrained_statement_rejects_state_access_and_phase_mutations() {
    let fixture = HelperFixture::new(
        &constrained_statement_source(),
        &constrained_statement_helper(),
    );
    let f = &fixture.fixture;
    let mut checker = f.elaborator();
    let connection_header = checker
        .check_provider_header(&f.resolved, &f.resolved.resources()[0])
        .unwrap();
    let statement = &f.resolved.resources()[1];
    let statement_header = checker
        .check_provider_header(&f.resolved, statement)
        .unwrap();
    let source_association = &connection_header.state_association;
    let association = crate::core::provider::DraftStateAssociation {
        definition: source_association.definition,
        family: source_association.family,
        parameters: &source_association.parameters,
        state: &source_association.state,
    };
    let sources = f
        .graph
        .modules()
        .iter()
        .map(|m| m.source())
        .collect::<Vec<_>>();
    let modules = f
        .graph
        .modules()
        .iter()
        .map(|m| (m.id(), m.source().id()))
        .collect::<Vec<_>>();
    for mutation in [
        crate::core::provider::AccessMutation::Method,
        crate::core::provider::AccessMutation::Definition,
        crate::core::provider::AccessMutation::Arguments,
        crate::core::provider::AccessMutation::Operand,
        crate::core::provider::AccessMutation::Result,
        crate::core::provider::AccessMutation::Effects,
        crate::core::provider::AccessMutation::OtherEnclosing,
    ] {
        let mut compiler = f.elaborator();
        let retained_association = source_association
            .clone_with_budget(&mut compiler.type_work)
            .unwrap();
        let mut draft = compiler
            .compile_provider_lifecycle_with_externals_and_associations(
                statement,
                &statement_header,
                Phase::Acquire,
                f.resolved.imported_facts(),
                vec![retained_association],
            )
            .unwrap();
        crate::core::provider::mutate_state_access(&mut draft.core, mutation);
        assert!(
            draft
                .check_staged_externals_with_associations(
                    statement,
                    f.resolved.imported_facts(),
                    &sources,
                    &modules,
                    &f.elaborator().registry,
                    &[association],
                    &mut TypeWorkBudget::unbounded()
                )
                .is_err()
        );
    }
    let mut compiler = f.elaborator();
    let retained_association = source_association
        .clone_with_budget(&mut compiler.type_work)
        .unwrap();
    let mut draft = compiler
        .compile_provider_lifecycle_with_externals_and_associations(
            statement,
            &statement_header,
            Phase::Acquire,
            f.resolved.imported_facts(),
            vec![retained_association],
        )
        .unwrap();
    draft.phase = Phase::Finish;
    assert!(
        draft
            .check_staged_externals_with_associations(
                statement,
                f.resolved.imported_facts(),
                &sources,
                &modules,
                &f.elaborator().registry,
                &[association],
                &mut TypeWorkBudget::unbounded()
            )
            .is_err()
    );
}

#[test]
fn provider_external_constrained_statement_rejects_pure_helper_state_transport() {
    let helper = format!(
        "{}pub identity<A> : A -> A\nidentity value = value\n",
        constrained_statement_helper()
    );
    for source in [
        constrained_statement_source().replace(
            "Provider.state_of db,",
            "Renamed.identity (Provider.state_of db),",
        ),
        constrained_statement_source().replace(
            "Provider.state_of db,",
            "Provider.state_of (Renamed.identity db),",
        ),
    ] {
        let fixture = HelperFixture::new(&source, &helper);
        let f = &fixture.fixture;
        let mut checker = f.elaborator();
        let connection_header = checker
            .check_provider_header(&f.resolved, &f.resolved.resources()[0])
            .unwrap();
        let statement = &f.resolved.resources()[1];
        let statement_header = checker
            .check_provider_header(&f.resolved, statement)
            .unwrap();
        let mut compiler = f.elaborator();
        let association = connection_header
            .state_association
            .clone_with_budget(&mut compiler.type_work)
            .unwrap();
        let result = compiler.compile_provider_lifecycle_with_externals_and_associations(
            statement,
            &statement_header,
            Phase::Acquire,
            f.resolved.imported_facts(),
            vec![association],
        );
        match result {
            Err(TypeError::Source(error)) => {
                assert_eq!(error.reason, TypeReason::Argument);
            }
            Err(error) => panic!("unexpected state transport failure: {error:?}"),
            Ok(draft) => {
                let source_association = &connection_header.state_association;
                let association = crate::core::provider::DraftStateAssociation {
                    definition: source_association.definition,
                    family: source_association.family,
                    parameters: &source_association.parameters,
                    state: &source_association.state,
                };
                let sources = f
                    .graph
                    .modules()
                    .iter()
                    .map(|m| m.source())
                    .collect::<Vec<_>>();
                let modules = f
                    .graph
                    .modules()
                    .iter()
                    .map(|m| (m.id(), m.source().id()))
                    .collect::<Vec<_>>();
                assert!(
                    draft
                        .check_staged_externals_with_associations(
                            statement,
                            f.resolved.imported_facts(),
                            &sources,
                            &modules,
                            &f.elaborator().registry,
                            &[association],
                            &mut TypeWorkBudget::unbounded()
                        )
                        .is_err()
                );
            }
        }
    }
}

#[test]
fn provider_external_transitive_generic_context_is_replayed() {
    let helper = "pub identity<A> : A -> A\nidentity value = value\npub prepare<B> : B -> B\nprepare value = identity value\n";
    let fixture = HelperFixture::new(
        &source().replace("Helper.identity", "Helper.prepare"),
        helper,
    );
    for phase in [Phase::Acquire, Phase::Finish] {
        let draft = fixture.draft(phase);
        fixture
            .check(&draft, &mut TypeWorkBudget::unbounded())
            .unwrap();
    }
}

#[test]
fn normal_provider_completed_local_constrained_helpers_use_checked_methods() {
    let source = constrained_source()
        .replace("import helper as Helper\n", "")
        .replace("import helper (impl Pass, impl Stamp)\n", "")
        .replace("Helper.normalize", "normalize");
    let source = format!(
        "{source}\n{}",
        CONSTRAINED_HELPER.replace("import @foreign.sqlite as Native\n", "")
    );
    let fixture = Fixture::new(&source);
    let mut slots = Vec::new();
    let mut work = TypeWorkBudget::unbounded();
    for resource in fixture.resolved.resources() {
        for body in [&resource.acquire, &resource.finish] {
            for occurrence in
                crate::elaborate::provider::external::all_provider_expression_occurrences(
                    body, &mut work,
                )
                .unwrap()
            {
                for slot in &occurrence.evidence {
                    slots.push(slot.retain_unpublished().unwrap());
                }
            }
        }
    }
    assert_eq!(slots.len(), 6);
    assert!(slots.iter().all(|slot| slot.selection().is_none()));
    let checked = check_module(fixture.resolved).unwrap();
    assert_eq!(checked.exports().resource_types().count(), 1);
    assert!(slots.iter().all(|slot| slot.filled().is_some()));
    let group = checked
        .into_group(&mut InterfaceConstraintBudget::default())
        .unwrap();
    let code = group.provider_code().unwrap();
    code.authenticate_code(code.contracts(), &mut TypeWorkBudget::unbounded())
        .unwrap();
}

#[test]
fn normal_provider_late_clause_failure_keeps_original_helper_slots_pending() {
    let valid = constrained_source()
        .replace("import helper as Helper\n", "")
        .replace("import helper (impl Pass, impl Stamp)\n", "")
        .replace("Helper.normalize", "normalize");
    let valid = format!(
        "{valid}\n{}",
        CONSTRAINED_HELPER.replace("import @foreign.sqlite as Native\n", "")
    );
    let invalid = valid.replace(
        "resume (perform Native.Connection<R>.diagnostic state)",
        "resume 42",
    );
    assert_ne!(valid, invalid);
    let fixture = Fixture::new(&invalid);
    let mut slots = Vec::new();
    let mut work = TypeWorkBudget::unbounded();
    for resource in fixture.resolved.resources() {
        for body in [&resource.acquire, &resource.finish] {
            for occurrence in
                crate::elaborate::provider::external::all_provider_expression_occurrences(
                    body, &mut work,
                )
                .unwrap()
            {
                for slot in &occurrence.evidence {
                    slots.push(slot.retain_unpublished().unwrap());
                }
            }
        }
    }
    assert_eq!(slots.len(), 6);
    assert!(matches!(
        check_module(fixture.resolved),
        Err(TypeError::Mismatch(_))
    ));
    assert!(slots.iter().all(|slot| slot.selection().is_none()));
    let retry = Fixture::new(&valid);
    let checked = check_module(retry.resolved).unwrap();
    let group = checked
        .into_group(&mut InterfaceConstraintBudget::default())
        .unwrap();
    let code = group.provider_code().unwrap();
    code.authenticate_code(code.contracts(), &mut TypeWorkBudget::unbounded())
        .unwrap();
}

#[test]
fn normal_provider_late_clause_origin_and_native_refusals_keep_all_slots_pending() {
    let source = constrained_source()
        .replace("import helper as Helper\n", "")
        .replace("import helper (impl Pass, impl Stamp)\n", "")
        .replace("Helper.normalize", "normalize");
    let valid = format!(
        "{source}\n{}",
        CONSTRAINED_HELPER.replace("import @foreign.sqlite as Native\n", "")
    );
    for mutation in 0..2 {
        let source = if mutation == 1 {
            valid.replace(
                "Native.Connection<R>.diagnostic state",
                "Native.Connection<R>.close state",
            )
        } else {
            valid.clone()
        };
        let mut fixture = Fixture::new(&source);
        let slots = normal_pending_slots(&fixture.resolved);
        assert_eq!(slots.len(), 9);
        if mutation == 0 {
            let unadmitted =
                crate::source::SourceFile::new("unadmitted-clause.ash", "resume").unwrap();
            fixture
                .resolved
                .replace_provider_handler_body_span_for_test(
                    unadmitted
                        .span(crate::source::ByteRange::new(0, 6).unwrap())
                        .unwrap(),
                );
        }
        let error = check_module(fixture.resolved).unwrap_err();
        match mutation {
            0 => assert!(
                matches!(error, TypeError::Internal(ElaborationFailure::InvalidState)),
                "origin: {error:?}"
            ),
            1 => assert!(
                matches!(error, TypeError::Source(ref error) if error.reason == crate::elaborate::TypeReason::Argument),
                "native: {error:?}"
            ),
            _ => unreachable!(),
        }
        assert!(slots.iter().all(|slot| slot.selection().is_none()));
        let fresh = Fixture::new(&valid);
        let slots = normal_pending_slots(&fresh.resolved);
        check_module(fresh.resolved).unwrap();
        assert!(slots.iter().all(|slot| slot.selection().is_some()));
    }
}

#[test]
fn normal_provider_conditional_clause_retains_selected_local_helper() {
    let source = SOURCE
        .replace(
            "read db => resume",
            "read db => {\nlet ignored = normalize 42\nresume",
        )
        .replace("diagnostic state)\n}", "diagnostic state)\n}\n}");
    let source = format!(
        "{source}\n{}\npub impl Pass<Int> {{\nfirst value = value\nsecond value = value\n}}\npub impl Stamp<Int> {{\nstamp (value, ignored) = value\n}}\n",
        CONSTRAINED_HELPER.replace("import @foreign.sqlite as Native\n", "")
    );
    let fixture = Fixture::new(&source);
    let crate::resolved::ResolvedExprKind::Block(block) =
        &fixture.resolved.resources()[0].handlers[0].body.kind
    else {
        panic!("clause block");
    };
    let crate::resolved::ResolvedLocalDeclaration::Binding(binding) = &block.declarations[0] else {
        panic!("local helper binding");
    };
    let mut work = TypeWorkBudget::unbounded();
    let occurrences = crate::elaborate::provider::external::all_provider_expression_occurrences(
        &binding.initializer,
        &mut work,
    )
    .unwrap();
    let slots = occurrences
        .iter()
        .flat_map(|occurrence| &occurrence.evidence)
        .map(|slot| slot.retain_unpublished().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(slots.len(), 2);
    let checked = check_module(fixture.resolved).unwrap();
    assert!(slots.iter().all(|slot| slot.filled().is_some()));
    let group = checked
        .into_group(&mut InterfaceConstraintBudget::default())
        .unwrap();
    let code = group.provider_code().unwrap();
    code.authenticate_code(code.contracts(), &mut TypeWorkBudget::unbounded())
        .unwrap();
}

#[test]
fn normal_provider_publication_has_exact_shared_type_budget_and_pending_retry() {
    for local in [false, true] {
        let source = if local {
            let source = constrained_source()
                .replace("import helper as Helper\n", "")
                .replace("import helper (impl Pass, impl Stamp)\n", "")
                .replace("Helper.normalize", "normalize");
            format!(
                "{source}\n{}",
                CONSTRAINED_HELPER.replace("import @foreign.sqlite as Native\n", "")
            )
        } else {
            constrained_source()
        };
        let fixture = || {
            if local {
                Fixture::new(&source)
            } else {
                Fixture::with_modules(
                    &source,
                    &[("helper.ash", CONSTRAINED_HELPER)],
                    ForeignRegistrations::new([
                        sqlite_manifest(ForeignRegistrationId::new(991)).unwrap()
                    ])
                    .unwrap(),
                )
            }
        };
        let mut measured = TypeWorkBudget::unbounded();
        let mut coverage = UsefulnessBudget::default();
        let mut constraints = InterfaceConstraintBudget::with_limit(usize::MAX);
        crate::elaborate::check_module_with_budget(
            fixture().resolved,
            &mut measured,
            &mut coverage,
            &mut constraints,
        )
        .unwrap();
        let cost = measured.used();
        assert!(cost > 1000);
        for prefix in [0, 13] {
            let current = fixture();
            let slots = normal_pending_slots(&current.resolved);
            assert_eq!(slots.len(), if local { 9 } else { 6 });
            let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
            short.charge(prefix).unwrap();
            let failure = crate::elaborate::check_module_with_budget(
                current.resolved,
                &mut short,
                &mut UsefulnessBudget::default(),
                &mut InterfaceConstraintBudget::with_limit(usize::MAX),
            )
            .unwrap_err();
            assert!(matches!(
                failure,
                TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
            ));
            assert!(slots.iter().all(|slot| slot.selection().is_none()));
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                exact.charge(prefix).unwrap();
                let checked = crate::elaborate::check_module_with_budget(
                    fixture().resolved,
                    &mut exact,
                    &mut UsefulnessBudget::default(),
                    &mut InterfaceConstraintBudget::with_limit(usize::MAX),
                )
                .unwrap();
                assert_eq!(exact.used(), prefix + cost);
                assert_eq!(checked.exports().resource_types().count(), 1);
            }
        }
    }
}

#[test]
fn normal_provider_publication_has_exact_constraint_and_coverage_budgets() {
    for local in [false, true] {
        let source = if local {
            let source = constrained_source()
                .replace("import helper as Helper\n", "")
                .replace("import helper (impl Pass, impl Stamp)\n", "")
                .replace("Helper.normalize", "normalize");
            format!(
                "{source}\n{}",
                CONSTRAINED_HELPER.replace("import @foreign.sqlite as Native\n", "")
            )
        } else {
            constrained_source()
        };
        let fixture = || {
            if local {
                Fixture::new(&source)
            } else {
                Fixture::with_modules(
                    &source,
                    &[("helper.ash", CONSTRAINED_HELPER)],
                    ForeignRegistrations::new([
                        sqlite_manifest(ForeignRegistrationId::new(991)).unwrap()
                    ])
                    .unwrap(),
                )
            }
        };
        let mut constraints = InterfaceConstraintBudget::with_limit(usize::MAX);
        let mut coverage = UsefulnessBudget::with_limit(usize::MAX);
        crate::elaborate::check_module_with_budget(
            fixture().resolved,
            &mut TypeWorkBudget::unbounded(),
            &mut coverage,
            &mut constraints,
        )
        .unwrap();
        let costs = [
            constraints.used(),
            usize::MAX - coverage.remaining_for_test(),
        ];
        assert!(costs.iter().all(|cost| *cost > 0));
        for (axis, cost) in costs.iter().copied().enumerate() {
            for prefix in [0, 13] {
                for exact in [false, true, true] {
                    let current = fixture();
                    let slots = normal_pending_slots(&current.resolved);
                    assert_eq!(slots.len(), if local { 9 } else { 6 });
                    let limit = prefix + cost - usize::from(!exact);
                    let mut constraints = InterfaceConstraintBudget::with_limit(if axis == 0 {
                        limit
                    } else {
                        usize::MAX
                    });
                    let mut coverage =
                        UsefulnessBudget::with_limit(if axis == 1 { limit } else { usize::MAX });
                    if axis == 0 {
                        constraints.charge(prefix).unwrap();
                    } else {
                        coverage.charge_for_test(prefix).unwrap();
                    }
                    let result = crate::elaborate::check_module_with_budget(
                        current.resolved,
                        &mut TypeWorkBudget::unbounded(),
                        &mut coverage,
                        &mut constraints,
                    );
                    if exact {
                        let checked = result.unwrap();
                        assert_eq!(checked.exports().resource_types().count(), 1);
                        assert_eq!(
                            if axis == 0 {
                                constraints.used()
                            } else {
                                limit - coverage.remaining_for_test()
                            },
                            prefix + costs[axis]
                        );
                        assert!(slots.iter().all(|slot| slot.selection().is_some()));
                    } else {
                        let error = result.unwrap_err();
                        assert!(
                            matches!(
                                error,
                                TypeError::Internal(
                                    ElaborationFailure::ConstraintResourceExhausted
                                        | ElaborationFailure::CoverageResourceExhausted(_)
                                ) | TypeError::Interface(_)
                            ),
                            "axis={axis}: {error:?}"
                        );
                        assert!(slots.iter().all(|slot| slot.selection().is_none()));
                    }
                }
            }
        }
    }
}

#[test]
fn normal_provider_injected_late_reservation_refusal_keeps_all_slots_pending() {
    let source = constrained_source()
        .replace("import helper as Helper\n", "")
        .replace("import helper (impl Pass, impl Stamp)\n", "")
        .replace("Helper.normalize", "normalize");
    let source = format!(
        "{source}\n{}",
        CONSTRAINED_HELPER.replace("import @foreign.sqlite as Native\n", "")
    );
    let fixture = Fixture::new(&source);
    let slots = normal_pending_slots(&fixture.resolved);
    assert_eq!(slots.len(), 9);
    let mut types = TypeWorkBudget::unbounded();
    types.charge(13).unwrap();
    let mut constraints = InterfaceConstraintBudget::with_limit(usize::MAX);
    constraints.charge(13).unwrap();
    // The second append reserves actual finish selections after lifecycle and
    // clause checks; the first acquire append has already reserved its slots.
    let refusal = crate::evidence::refuse_append_reservation_after_for_test(1);
    let error = crate::elaborate::check_module_with_budget(
        fixture.resolved,
        &mut types,
        &mut UsefulnessBudget::default(),
        &mut constraints,
    )
    .unwrap_err();
    assert!(refusal.was_consumed());
    assert!(
        matches!(
            error,
            TypeError::Internal(ElaborationFailure::ConstraintResourceExhausted)
                | TypeError::Interface(_)
        ),
        "injected reservation: {error:?}"
    );
    assert!(types.used() > 1000 && constraints.used() > 13);
    assert!(slots.iter().all(|slot| slot.selection().is_none()));
    drop(refusal);
    let fresh = Fixture::new(&source);
    let slots = normal_pending_slots(&fresh.resolved);
    let checked = check_module(fresh.resolved).unwrap();
    assert_eq!(checked.exports().resource_types().count(), 1);
    assert!(slots.iter().all(|slot| slot.selection().is_some()));
}

#[test]
fn normal_provider_completed_local_helper_links_ordinary_main() {
    let source = constrained_source()
        .replace("import helper as Helper\n", "")
        .replace("import helper (impl Pass, impl Stamp)\n", "")
        .replace("Helper.normalize", "normalize");
    let source = format!(
        "{source}\n{}\nmain : Unit -> Int\nmain () = 42\n",
        CONSTRAINED_HELPER.replace("import @foreign.sqlite as Native\n", "")
    );
    let fixture = Fixture::new(&source);
    let mut checked = Vec::<CheckedModule>::new();
    for loaded in fixture.graph.modules() {
        let dependencies = loaded
            .dependencies()
            .iter()
            .map(|edge| {
                DependencyExports::new(
                    edge,
                    checked
                        .iter()
                        .find(|module| module.module() == edge.target())
                        .unwrap()
                        .exports(),
                )
                .unwrap()
            })
            .collect::<Vec<_>>();
        checked.push(check_module(resolve_module(loaded, &dependencies).unwrap()).unwrap());
    }
    let linked = crate::elaborate::link_modules(checked, fixture.graph.entry()).unwrap();
    let validated = crate::validate_linked_facts_for_test(linked).unwrap();
    let mut elaborator =
        crate::elaborate::EffectElaborator::for_module_program(&validated).unwrap();
    let typed = elaborator
        .synthesize_effect_module_program(&validated)
        .unwrap();
    let core = elaborator.finish(typed.node).unwrap();
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
    let core = crate::core::validate_effect_modules(core, &sources, &modules).unwrap();
    assert_eq!(
        crate::eval::evaluate_effect(&core)
            .unwrap()
            .value
            .to_string(),
        "42"
    );
}

fn normal_pending_slots(
    resolved: &crate::resolved::ResolvedModule,
) -> Vec<crate::interface::EvidenceSlot> {
    let mut slots = Vec::new();
    let mut work = TypeWorkBudget::unbounded();
    let mut collect = |body: &crate::resolved::ResolvedExpr| {
        for occurrence in crate::elaborate::provider::external::all_provider_expression_occurrences(
            body, &mut work,
        )
        .unwrap()
        {
            for slot in &occurrence.evidence {
                slots.push(slot.retain_unpublished().unwrap());
            }
        }
    };
    for resource in resolved.resources() {
        for body in [&resource.acquire, &resource.finish] {
            collect(body);
        }
        for clause in &resource.handlers {
            collect(&clause.body);
        }
    }
    for implementation in resolved.implementations() {
        for group in &implementation.method_groups {
            for equation in &group.equations {
                collect(&equation.body);
            }
        }
    }
    for definition in resolved.definitions() {
        if let crate::resolved::ResolvedDefinitionKind::Equational(global) = &definition.kind {
            for equation in &global.equations {
                collect(&equation.body);
            }
        }
    }
    slots
}

#[test]
fn normal_provider_failures_keep_ordinary_and_lifecycle_slots_pending() {
    let source = constrained_source()
        .replace("import helper as Helper\n", "")
        .replace("import helper (impl Pass, impl Stamp)\n", "")
        .replace("Helper.normalize", "normalize");
    let valid = format!(
        "{source}\n{}\nprobe : Native.OpenConfig -> Native.OpenConfig\nprobe config = normalize config\n",
        CONSTRAINED_HELPER.replace("import @foreign.sqlite as Native\n", "")
    );
    for case in 0..4 {
        let source = match case {
            0 => valid.replace("resume (perform Native.Connection<R>.diagnostic state)", "resume 42"),
            1 => format!("{valid}\nwrong : Unit -> Int\nwrong () = true\n"),
            2 => valid.replace("pub impl Pass<Native.CloseError> {\nfirst value = value\nsecond value = value\n}\n", ""),
            3 => valid.replace("finish state => match perform Native.Connection<R>.close state", "finish state => match perform Native.Connection<R>.diagnostic state"),
            _ => unreachable!(),
        };
        assert_ne!(source, valid);
        let fixture = Fixture::new(&source);
        let slots = normal_pending_slots(&fixture.resolved);
        assert_eq!(slots.len(), 11);
        let failure = check_module(fixture.resolved).unwrap_err();
        match case {
            0 => assert!(
                matches!(failure, TypeError::Mismatch(_)),
                "case {case}: {failure:?}"
            ),
            1 => assert!(
                matches!(failure, TypeError::Source(ref error) if error.reason == crate::elaborate::TypeReason::DefinitionResult),
                "case {case}: {failure:?}"
            ),
            2 => assert!(
                matches!(failure, TypeError::Interface(ref error) if error.reason == InterfaceReason::Unsatisfied),
                "case {case}: {failure:?}"
            ),
            3 => assert!(
                matches!(failure, TypeError::Source(ref error) if error.reason == crate::elaborate::TypeReason::Argument),
                "case {case}: {failure:?}"
            ),
            _ => unreachable!(),
        }
        assert!(
            slots.iter().all(|slot| slot.selection().is_none()),
            "case {case}"
        );
        let retry = Fixture::new(&valid);
        let slots = normal_pending_slots(&retry.resolved);
        let checked = check_module(retry.resolved).unwrap();
        assert!(slots.iter().all(|slot| slot.selection().is_some()));
        let group = checked
            .into_group(&mut InterfaceConstraintBudget::default())
            .unwrap();
        let code = group.provider_code().unwrap();
        code.authenticate_code(code.contracts(), &mut TypeWorkBudget::unbounded())
            .unwrap();
    }
}

#[test]
fn normal_provider_second_resource_failure_keeps_first_group_and_ordinary_slots_pending() {
    let source = constrained_source()
        .replace("import helper as Helper\n", "")
        .replace("import helper (impl Pass, impl Stamp)\n", "")
        .replace("Helper.normalize", "normalize");
    let valid = format!(
        "import @foreign.provider as Provider\n{source}\n{}\n{STATEMENT}",
        CONSTRAINED_HELPER.replace("import @foreign.sqlite as Native\n", "")
    );
    let invalid = valid.replace(".finalize state", ".finalize 42");
    let fixture = |source: &str| {
        Fixture::with_registrations(
            source,
            ForeignRegistrations::new([
                sqlite_manifest(ForeignRegistrationId::new(991)).unwrap(),
                crate::foreign::provider_manifest(ForeignRegistrationId::new(992)).unwrap(),
            ])
            .unwrap(),
        )
    };
    let current = fixture(&invalid);
    let slots = normal_pending_slots(&current.resolved);
    assert_eq!(slots.len(), 10);
    let expected = IterativeTypeOwner::new(
        crate::types::clone_type_with_budget(
            &current.resolved.resources()[1].state.ty,
            &mut TypeWorkBudget::unbounded(),
        )
        .unwrap(),
    );
    let failure = check_module(current.resolved).unwrap_err();
    assert!(
        matches!(failure, TypeError::Mismatch(ref mismatch) if mismatch.expected.as_ref() == &*expected && *mismatch.found == Type::Int),
        "{failure:?}"
    );
    assert!(slots.iter().all(|slot| slot.selection().is_none()));
    let wrong_state = fixture(&valid.replace("Provider.state_of db", "Provider.state_of sql"));
    let wrong_slots = normal_pending_slots(&wrong_state.resolved);
    assert_eq!(wrong_slots.len(), 10);
    let error = check_module(wrong_state.resolved).unwrap_err();
    assert!(
        matches!(error, TypeError::Source(ref error) if error.reason == crate::elaborate::TypeReason::Argument),
        "wrong state: {error:?}"
    );
    assert!(wrong_slots.iter().all(|slot| slot.selection().is_none()));
    let retry = fixture(&valid);
    let slots = normal_pending_slots(&retry.resolved);
    let checked = check_module(retry.resolved).unwrap();
    assert_eq!(checked.exports().resource_types().count(), 2);
    // The sealed state_of occurrence reserves a source relation slot,
    // authenticated by the typed StateAccess association rather than an
    // ordinary selected dictionary. All nine dictionary slots commit.
    assert_eq!(
        slots
            .iter()
            .filter(|slot| slot.selection().is_some())
            .count(),
        9
    );
    let group = checked
        .into_group(&mut InterfaceConstraintBudget::default())
        .unwrap();
    let code = group.provider_code().unwrap();
    code.authenticate_code(code.contracts(), &mut TypeWorkBudget::unbounded())
        .unwrap();
}

#[test]
fn normal_provider_retained_selected_method_and_native_facts_refuse_mutation() {
    let source = constrained_source()
        .replace(
            "Helper.normalize config",
            &nested_normalize("config", "Helper"),
        )
        .replace(
            "Helper.normalize error",
            &nested_normalize("error", "Helper"),
        );
    let source = format!("{source}\nmain : Unit -> Int\nmain () = 42\n");
    let helper = nested_constrained_helper();
    for mutation in 0..11 {
        let fixture = Fixture::with_modules(
            &source,
            &[("helper.ash", &helper)],
            ForeignRegistrations::new([sqlite_manifest(ForeignRegistrationId::new(991)).unwrap()])
                .unwrap(),
        );
        let build = || {
            let mut modules = Vec::<CheckedModule>::new();
            for loaded in fixture.graph.modules() {
                let dependencies = loaded
                    .dependencies()
                    .iter()
                    .map(|edge| {
                        DependencyExports::new(
                            edge,
                            modules
                                .iter()
                                .find(|module| module.module() == edge.target())
                                .unwrap()
                                .exports(),
                        )
                        .unwrap()
                    })
                    .collect::<Vec<_>>();
                modules.push(check_module(resolve_module(loaded, &dependencies).unwrap()).unwrap());
            }
            modules
        };
        let positive = crate::elaborate::link_modules(build(), fixture.graph.entry()).unwrap();
        crate::validate_linked_facts_for_test(positive).unwrap();
        let mut modules = build();
        let checked = modules
            .iter_mut()
            .find(|module| module.module() == fixture.graph.entry())
            .unwrap();
        let mut code = checked.take_provider_code_for_test().unwrap();
        let certificate = Arc::clone(code.contracts());
        let owned = Arc::get_mut(&mut code).unwrap();
        let core = &mut owned.declarations[0].finish.draft.core;
        match mutation {
            0 => crate::core::erase_registered_foreign_facts_for_test(core),
            1 => crate::core::provider::mutate_method_catalog_for_test(core, crate::core::dialect::MethodEvidenceCatalogMutationForTest::WrongMethodPosition),
            2 => crate::core::provider::mutate_method_catalog_for_test(core, crate::core::dialect::MethodEvidenceCatalogMutationForTest::WrongMethodScheme),
            3..=7 => crate::core::provider::mutate_polymorphic_prerequisite_for_test(core, mutation - 3),
            8 => crate::core::provider::mutate_method_catalog_for_test(core, crate::core::dialect::MethodEvidenceCatalogMutationForTest::WrongDomainSourceParameter),
            9 => crate::core::provider::mutate_method_catalog_for_test(core, crate::core::dialect::MethodEvidenceCatalogMutationForTest::WrongDomainParameterKind),
            10 => crate::core::provider::mutate_method_catalog_for_test(core, crate::core::dialect::MethodEvidenceCatalogMutationForTest::WrongDomainParameterOrder),
            _ => unreachable!(),
        }
        let result = code.authenticate_code(&certificate, &mut TypeWorkBudget::unbounded());
        assert!(
            matches!(
                result,
                Err(crate::resolved::ResolvedBuildFailure::InvalidState)
            ),
            "retained mutation {mutation}: {result:?}"
        );
        checked.restore_provider_code_for_test(code);
        assert!(
            matches!(
                crate::elaborate::link_modules(modules, fixture.graph.entry()),
                Err(TypeError::Internal(ElaborationFailure::InvalidState))
            ),
            "retained mutation {mutation} must refuse defining summary/code linkage"
        );
    }
}

fn constrained_source() -> String {
    source()
        .replace("Helper.identity", "Helper.normalize")
        .replace(
            "import helper as Helper",
            "import helper as Helper\nimport helper (impl Pass, impl Stamp)",
        )
}
#[test]
fn provider_external_constrained_alias_requires_separate_implementation_imports() {
    let fixture = HelperFixture::new(
        &source().replace("Helper.identity", "Helper.normalize"),
        CONSTRAINED_HELPER,
    );
    let f = &fixture.fixture;
    let header = f
        .elaborator()
        .check_provider_header(&f.resolved, &f.resolved.resources()[0])
        .unwrap();
    assert!(
        matches!(f.elaborator().compile_provider_lifecycle_with_externals(&f.resolved.resources()[0], &header,
        Phase::Acquire, f.resolved.imported_facts()), Err(TypeError::Interface(error)) if error.reason == InterfaceReason::Unsatisfied)
    );
}
#[test]
fn provider_external_constrained_closed_entry_remains_guarded_with_valid_source() {
    let fixture = HelperFixture::new(&constrained_source(), CONSTRAINED_HELPER);
    let f = &fixture.fixture;
    let header = f
        .elaborator()
        .check_provider_header(&f.resolved, &f.resolved.resources()[0])
        .unwrap();
    for phase in [Phase::Acquire, Phase::Finish] {
        assert!(matches!(
            f.elaborator()
                .compile_provider_lifecycle(&f.resolved.resources()[0], &header, phase),
            Err(TypeError::Internal(ElaborationFailure::InvalidState))
        ));
    }
}
const TUPLE_HELPER: &str = concat!(
    "pub interface Pass<A> {\nfirst : A -> A\nsecond : A -> A\n}\n",
    "pub interface Stamp<A> {\nstamp : (A, Int) -> A\n}\n",
    "pub impl<A> Pass<(A, Int)> {\nfirst value = value\nsecond value = value\n}\n",
    "pub impl<A> Stamp<(A, Int)> {\nstamp (value, ignored) = value\n}\n",
    "pub normalize<X> : X -> X where Pass<X>, Stamp<X>\n",
    "normalize value = stamp ((second (first value), 7))\n"
);

#[test]
fn provider_external_constrained_generic_tuple_producer_contexts() {
    let helper = TUPLE_HELPER;
    let source = constrained_source()
        .replace(
            ".open (Helper.normalize config)",
            ".open (match Helper.normalize((config, 0)) {\n(mapped, tag) => mapped\n})",
        )
        .replace(
            "Helper.normalize error",
            "(match Helper.normalize((error, 0)) {\n(mapped, tag) => mapped\n})",
        );
    let fixture = HelperFixture::new(&source, helper);
    for phase in [Phase::Acquire, Phase::Finish] {
        let draft = fixture.staged_draft(phase);
        fixture
            .check_staged(&draft, &mut TypeWorkBudget::unbounded())
            .unwrap();
    }
}

#[test]
fn provider_external_constrained_exact_abi_and_defining_identity_without_helper_file() {
    let source = constrained_source()
        .replace("helper as Helper", "helper as Renamed")
        .replace("Helper.normalize", "Renamed.normalize");
    let fixture = HelperFixture::new(&source, CONSTRAINED_HELPER);
    fs::remove_file(fixture.path.join("helper.ash")).unwrap();
    for phase in [Phase::Acquire, Phase::Finish] {
        let draft = fixture.staged_draft(phase);
        let scheme = crate::core::provider::external_scheme_for_test(
            &draft.core,
            fixture.globals["normalize"],
        );
        let Type::Forall(parameters, _) = scheme else {
            panic!("generic helper");
        };
        assert_eq!(parameters.len(), 1);
        assert_eq!(parameters[0].1, Kind::Type);
        let a = Type::Variable(parameters[0].0);
        let arrow = |input, result| Type::Function(Box::new(input), Box::new(result));
        let expected = Type::Forall(
            parameters.clone(),
            Box::new(arrow(
                arrow(a.clone(), a.clone()),
                arrow(
                    arrow(a.clone(), a.clone()),
                    arrow(
                        arrow(Type::Tuple(Box::new([a.clone(), Type::Int])), a.clone()),
                        arrow(a.clone(), a),
                    ),
                ),
            )),
        );
        assert!(
            same_type_with_budget(scheme, &expected, &mut TypeWorkBudget::unbounded()).unwrap()
        );
        fixture
            .check_staged(&draft, &mut TypeWorkBudget::unbounded())
            .unwrap();
        assert!(
            fixture
                .check(&draft, &mut TypeWorkBudget::unbounded())
                .is_err()
        );
        for occurrence in &draft.staged_externals.as_ref().unwrap().occurrences {
            assert!(
                occurrence
                    .occurrence
                    .evidence
                    .iter()
                    .all(|slot| slot.selection().is_none())
            );
        }
    }
}

#[test]
fn provider_external_constrained_independent_order_producer_slots_and_actual_arguments() {
    let fixture = HelperFixture::new(&constrained_source(), CONSTRAINED_HELPER);
    for mutation in 0..5 {
        let mut draft = fixture.staged_draft(Phase::Acquire);
        let staged = draft.staged_externals.as_mut().unwrap();
        let occurrence = &mut staged.occurrences[0];
        match mutation {
            0 => crate::core::provider::swap_dictionary_methods_for_test(
                &mut draft.core,
                occurrence.node.unwrap(),
            ),
            1 => crate::core::provider::wrong_dictionary_producer_for_test(
                &mut draft.core,
                occurrence.node.unwrap(),
            ),
            2 => occurrence.occurrence.evidence.swap(0, 1),
            3 => {
                discard_type_iteratively(std::mem::replace(
                    &mut occurrence.arguments.0[0],
                    Type::Int,
                ));
            }
            4 => {
                staged
                    .publication
                    .relocate_types(
                        |_, _| Ok(Type::Int),
                        &mut InterfaceConstraintBudget::with_limit(usize::MAX),
                        &mut TypeWorkBudget::unbounded(),
                    )
                    .unwrap();
            }
            _ => unreachable!(),
        }
        assert!(
            fixture
                .check_staged(&draft, &mut TypeWorkBudget::unbounded())
                .is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn provider_external_constrained_authenticates_abi_and_source_identity() {
    use crate::core::provider::{ExternalMutation, mutate_external_for_test};
    let helper = format!(
        "{CONSTRAINED_HELPER}private<A> : A -> A\nprivate value = value\npub absent<A> : A -> A\nabsent value = value\n"
    );
    let source = constrained_source()
        .replace("import helper as Helper", "import helper (normalize)")
        .replace("Helper.normalize", "normalize");
    let fixture = HelperFixture::new(&source, &helper);
    for phase in [Phase::Acquire, Phase::Finish] {
        for mutation in [
            ExternalMutation::Type,
            ExternalMutation::Kind,
            ExternalMutation::Row,
            ExternalMutation::Binder(fixture.globals["private"]),
            ExternalMutation::Binder(fixture.globals["absent"]),
        ] {
            let mut draft = fixture.staged_draft(phase);
            mutate_external_for_test(&mut draft.core, fixture.globals["normalize"], mutation);
            assert!(
                fixture
                    .check_staged(&draft, &mut TypeWorkBudget::unbounded())
                    .is_err()
            );
        }
        for spelling in ["private", "absent"] {
            let mut draft = fixture.staged_draft(phase);
            draft.staged_externals.as_mut().unwrap().occurrences[0]
                .occurrence
                .term = crate::resolved::ResolvedTermName::Global(fixture.globals[spelling]);
            assert!(
                fixture
                    .check_staged(&draft, &mut TypeWorkBudget::unbounded())
                    .is_err()
            );
        }
    }
}

#[test]
fn provider_external_constrained_cumulative_budget_refusal_slots_empty_and_fresh_retry() {
    let fixture = HelperFixture::new(&constrained_source(), CONSTRAINED_HELPER);
    for phase in [Phase::Acquire, Phase::Finish] {
        let draft = fixture.staged_draft(phase);
        let mut measured = TypeWorkBudget::unbounded();
        fixture.check_staged(&draft, &mut measured).unwrap();
        let cost = measured.used();
        eprintln!("provider constrained {phase:?} cumulative check cost={cost}");
        for prefix in [0, 17] {
            let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
            short.charge(prefix).unwrap();
            assert!(fixture.check_staged(&draft, &mut short).is_err());
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                exact.charge(prefix).unwrap();
                fixture.check_staged(&draft, &mut exact).unwrap();
                assert_eq!(exact.used(), prefix + cost);
            }
            assert!(
                draft
                    .staged_externals
                    .as_ref()
                    .unwrap()
                    .occurrences
                    .iter()
                    .all(|o| o
                        .occurrence
                        .evidence
                        .iter()
                        .all(|slot| slot.selection().is_none()))
            );
        }
    }
}

#[test]
fn provider_external_constrained_selected_producer_control_is_not_erased() {
    let helper = CONSTRAINED_HELPER.replace("pub interface Pass", "pub effect Noise {\nask : Unit -> Unit\n}\npub interface Pass")
        .replace("first value = value", "first value = {\nlet ignored = handle (perform Noise.ask ()) with Noise {\nask () => resume ()\n}\nvalue\n}");
    let fixture = HelperFixture::new(&constrained_source(), &helper);
    for phase in [Phase::Acquire, Phase::Finish] {
        let draft = fixture.staged_draft(phase);
        assert!(
            fixture
                .check_staged(&draft, &mut TypeWorkBudget::unbounded())
                .is_err()
        );
    }
}

#[test]
fn provider_external_constrained_unselected_control_is_not_traversed() {
    let helper = format!(
        "{CONSTRAINED_HELPER}pub effect Noise {{\nask : Unit -> Unit\n}}\npub noisy : Unit -> Unit ! {{Noise}}\nnoisy () = perform Noise.ask ()\n"
    );
    let fixture = HelperFixture::new(&constrained_source(), &helper);
    for phase in [Phase::Acquire, Phase::Finish] {
        fixture
            .check_staged(
                &fixture.staged_draft(phase),
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap();
    }
}

#[test]
fn provider_external_constrained_compile_budget_failure_is_unpublished_and_retryable() {
    let fixture = HelperFixture::new(&constrained_source(), CONSTRAINED_HELPER);
    let f = &fixture.fixture;
    let definition = &f.resolved.resources()[0];
    let header = f
        .elaborator()
        .check_provider_header(&f.resolved, definition)
        .unwrap();
    for phase in [Phase::Acquire, Phase::Finish] {
        let mut measured = f.elaborator();
        measured.type_work = TypeWorkBudget::unbounded();
        let draft = measured
            .compile_provider_lifecycle_with_externals(
                definition,
                &header,
                phase,
                f.resolved.imported_facts(),
            )
            .unwrap();
        let cost = draft.compile_work;
        eprintln!("provider constrained {phase:?} cumulative compile cost={cost}");
        for prefix in [0, 17] {
            for allowance in [cost - 1, cost] {
                let mut bounded = f.elaborator();
                bounded.type_work = TypeWorkBudget::with_limit(prefix + allowance);
                bounded.type_work.charge(prefix).unwrap();
                let result = bounded.compile_provider_lifecycle_with_externals(
                    definition,
                    &header,
                    phase,
                    f.resolved.imported_facts(),
                );
                if allowance == cost {
                    let exact = result.unwrap();
                    assert_eq!(exact.compile_work, prefix + cost);
                    fixture
                        .check_staged(&exact, &mut TypeWorkBudget::unbounded())
                        .unwrap();
                } else {
                    assert!(matches!(
                        result,
                        Err(TypeError::Internal(
                            ElaborationFailure::TypeResourceExhausted
                        ))
                    ));
                }
            }
        }
        // The closed immutable result is reusable after each independent refusal.
        fixture
            .check_staged(&draft, &mut TypeWorkBudget::unbounded())
            .unwrap();
        for limit in [0, 23, 200] {
            let mut short = f.elaborator();
            short.type_work = TypeWorkBudget::with_limit(limit);
            assert!(matches!(
                short.compile_provider_lifecycle_with_externals(
                    definition,
                    &header,
                    phase,
                    f.resolved.imported_facts()
                ),
                Err(TypeError::Internal(
                    ElaborationFailure::TypeResourceExhausted
                ))
            ));
            let originals = super::super::external::provider_source_occurrences(
                match phase {
                    Phase::Acquire => &definition.acquire,
                    _ => &definition.finish,
                },
                f.resolved.imported_facts(),
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap();
            assert!(originals.iter().all(|occurrence| {
                occurrence
                    .evidence
                    .iter()
                    .all(|slot| slot.selection().is_none())
            }));
            fixture
                .check_staged(
                    &fixture.staged_draft(phase),
                    &mut TypeWorkBudget::unbounded(),
                )
                .unwrap();
        }
    }
}

#[test]
fn provider_external_generic_producer_nested_source_actual_contexts() {
    let helper = format!(
        "{}pub identity<B> : B -> B\nidentity value = value\npub relay<C> : C -> C\nrelay value = identity value\n",
        TUPLE_HELPER.replace("first value = value", "first value = relay value")
    );
    let source = constrained_source()
        .replace(
            ".open (Helper.normalize config)",
            ".open (match Helper.normalize((config, 0)) {\n(mapped, tag) => mapped\n})",
        )
        .replace(
            "Helper.normalize error",
            "(match Helper.normalize((error, 0)) {\n(mapped, tag) => mapped\n})",
        );
    let fixture = HelperFixture::new(&source, &helper);
    for phase in [Phase::Acquire, Phase::Finish] {
        fixture
            .check_staged(
                &fixture.staged_draft(phase),
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap();
    }
}

#[test]
fn provider_external_constrained_deep_refusal_drops_owned_arguments_on_small_stack() {
    const CHILD: &str = "ASH_B2_DEEP_ARGUMENT_CHILD";
    if std::env::var_os(CHILD).is_none() {
        let status = std::process::Command::new(std::env::current_exe().unwrap()).args(["--exact", "elaborate::provider::tests::external::provider_external_constrained_deep_refusal_drops_owned_arguments_on_small_stack", "--nocapture"]).env(CHILD, "1").status().unwrap();
        assert!(status.success());
        return;
    }
    let fixture = HelperFixture::new(&constrained_source(), CONSTRAINED_HELPER);
    let mut draft = fixture.staged_draft(Phase::Acquire);
    fixture
        .check_staged(&draft, &mut TypeWorkBudget::unbounded())
        .unwrap();
    let canonical = Arc::clone(&fixture.fixture.elaborator().registry);
    std::thread::Builder::new()
        .name("b2-deep-refusal".into())
        .stack_size(256 * 1024)
        .spawn(move || {
            let f = &fixture.fixture;
            let sources = f
                .graph
                .modules()
                .iter()
                .map(|module| module.source())
                .collect::<Vec<_>>();
            let modules = f
                .graph
                .modules()
                .iter()
                .map(|module| (module.id(), module.source().id()))
                .collect::<Vec<_>>();
            let check = |draft: &LifecycleTemplateDraft, work: &mut TypeWorkBudget| {
                draft.check_staged_externals(
                    &f.resolved.resources()[0],
                    f.resolved.imported_facts(),
                    &sources,
                    &modules,
                    &canonical,
                    work,
                )
            };
            check(&draft, &mut TypeWorkBudget::unbounded()).unwrap();
            let mut deep = Type::Int;
            for _ in 0..8192 {
                deep = Type::Tuple(Box::new([deep]));
            }
            let argument = &mut draft.staged_externals.as_mut().unwrap().occurrences[0]
                .arguments
                .0[0];
            discard_type_iteratively(std::mem::replace(argument, deep));
            for limit in [0, 128, 8192, 32768] {
                assert!(check(&draft, &mut TypeWorkBudget::with_limit(limit)).is_err());
            }
            assert!(check(&draft, &mut TypeWorkBudget::unbounded()).is_err());
            drop(draft);
            drop(fixture);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn provider_external_b3_fixture_ordinary_linked_method_catalog() {
    let mut helper = nested_constrained_helper();
    helper.push_str("pub impl Pass<Int> {\nfirst (value, ignored) = value\nsecond value = value\nthird value = value\n}\npub impl Stamp<Int> {\nstamp (value, ignored) = value\n}\n");
    let entry = format!(
        "import helper as Helper\nimport helper (impl Pass, impl Stamp)\nmain : Unit -> Int\nmain () = {}\n",
        nested_normalize("7", "Helper")
    );
    check_ordinary_nested_helper_fixture(&entry, &helper);
}

#[test]
fn provider_external_ordinary_concrete_parent_uses_zero_parameter_source() {
    let helper = nested_constrained_helper()
        .replace(
            "pub impl<A> Pass<Box<A>> where Pass<A>",
            "pub impl Pass<Box<Int>> where Pass<Int>",
        )
        .replace(
            "pub impl<A> Stamp<Box<A>> where Stamp<A>",
            "pub impl Stamp<Box<Int>> where Stamp<Int>",
        );
    let helper = format!(
        "{helper}pub impl Pass<Int> {{\nfirst (value, ignored) = value\nsecond value = value\nthird value = value\n}}\npub impl Stamp<Int> {{\nstamp (value, ignored) = value\n}}\n"
    );
    let entry = "import helper as Helper\nimport helper (impl Pass, impl Stamp)\nmain : Unit -> Int\nmain () = match Helper.normalize (Helper.Box 7) {\nHelper.Box(value) => value\n}\n";
    check_ordinary_nested_helper_fixture(entry, &helper);
}

fn check_ordinary_nested_helper_fixture(entry: &str, helper: &str) {
    let fixture = HelperFixture::new(entry, helper);
    let graph = &fixture.fixture.graph;
    let mut checked = Vec::<CheckedModule>::new();
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                DependencyExports::new(
                    edge,
                    checked
                        .iter()
                        .find(|checked| checked.module() == edge.target())
                        .unwrap()
                        .exports(),
                )
                .unwrap()
            })
            .collect::<Vec<_>>();
        checked.push(check_module(resolve_module(module, &dependencies).unwrap()).unwrap());
    }
    let linked = crate::elaborate::link_modules(checked, graph.entry()).unwrap();
    let linked = crate::evidence_validation::validate_interface_evidence(linked).unwrap();
    let mut elaborator =
        CoreElaborator::<EffectOperationFamily>::for_module_program(&linked).unwrap();
    let typed = elaborator
        .synthesize_effect_module_program(&linked)
        .unwrap();
    let core = elaborator.finish(typed.node).unwrap();
    let sources = graph
        .modules()
        .iter()
        .map(|m| m.source())
        .collect::<Vec<_>>();
    let modules = graph
        .modules()
        .iter()
        .map(|m| (m.id(), m.source().id()))
        .collect::<Vec<_>>();
    let validated = crate::core::validate_effect_modules(core, &sources, &modules).unwrap();
    for mutation in [0, 2, 3, 4] {
        let mut changed =
            crate::core::transform::fold_effect_literal_primitives(&validated).unwrap();
        crate::core::provider::mutate_polymorphic_prerequisite_for_test(&mut changed, mutation);
        assert!(
            crate::core::validate_effect_modules(changed, &sources, &modules).is_err(),
            "linked prerequisite mutation {mutation}"
        );
    }
}

#[test]
fn provider_external_wide_imported_concrete_roots_have_exact_retry_boundaries() {
    for width in [1, 17] {
        let declarations = (0..width)
            .map(|i| format!("\nextra{i} : A -> A"))
            .collect::<String>();
        let definitions = (0..width)
            .map(|i| format!("\nextra{i} value = value"))
            .collect::<String>();
        let helper = CONSTRAINED_HELPER
            .replace("second : A -> A", &format!("second : A -> A{declarations}"))
            .replace(
                "second value = value",
                &format!("second value = value{definitions}"),
            );
        let fixture = HelperFixture::new(&constrained_source(), &helper);
        let draft = fixture.staged_draft(Phase::Acquire);
        let staged = draft.staged_externals.as_ref().unwrap();
        let mut constraint = InterfaceConstraintBudget::with_limit(usize::MAX);
        let mut types = TypeWorkBudget::unbounded();
        let catalog = crate::evidence_validation::build_imported_method_evidence_catalog(
            fixture.fixture.resolved.imported_facts(),
            &fixture.fixture.elaborator().registry,
            staged.occurrences[0].occurrence.origin.primary_span(),
            staged.occurrences.iter().map(|o| &o.occurrence),
            &staged.publication,
            &mut constraint,
            &mut types,
        )
        .unwrap();
        assert_eq!(catalog.concrete_sources().len(), width + 3);
        let cost = constraint.used();
        for prefix in [0, 13] {
            for allowance in [cost - 1, cost, cost] {
                let mut work = InterfaceConstraintBudget::with_limit(prefix + allowance);
                work.charge(prefix).unwrap();
                let result = crate::evidence_validation::build_imported_method_evidence_catalog(
                    fixture.fixture.resolved.imported_facts(),
                    &fixture.fixture.elaborator().registry,
                    staged.occurrences[0].occurrence.origin.primary_span(),
                    staged.occurrences.iter().map(|o| &o.occurrence),
                    &staged.publication,
                    &mut work,
                    &mut TypeWorkBudget::unbounded(),
                );
                if allowance == cost {
                    result.unwrap();
                    assert_eq!(work.used(), prefix + cost);
                } else {
                    assert!(result.is_err());
                }
                assert!(staged.occurrences.iter().all(|o| {
                    o.occurrence
                        .evidence
                        .iter()
                        .all(|s| s.selection().is_none())
                }));
            }
        }
        fixture
            .check_staged(&draft, &mut TypeWorkBudget::unbounded())
            .unwrap();
    }
}

#[test]
fn provider_external_nested_canonical_catalog_and_prerequisites_reject_mutation() {
    use crate::core::dialect::MethodEvidenceCatalogMutationForTest as Mutation;
    let source = constrained_source()
        .replace(
            "Helper.normalize config",
            &nested_normalize("config", "Helper"),
        )
        .replace(
            "Helper.normalize error",
            &nested_normalize("error", "Helper"),
        );
    let fixture = HelperFixture::new(&source, &nested_constrained_helper());
    for phase in [Phase::Acquire, Phase::Finish] {
        for mutation in [
            Mutation::WrongRequirementPosition,
            Mutation::WrongMethodPosition,
            Mutation::WrongMethodScheme,
            Mutation::WrongCanonicalMethodParameter,
            Mutation::WrongAdapterBinder,
            Mutation::WrongAdapterSourceParameter,
            Mutation::WrongOwnerSourceParameter,
            Mutation::WrongHeadCount,
            Mutation::WrongHeadArgument,
            Mutation::MissingPrerequisite,
            Mutation::WrongPrerequisiteProducer,
            Mutation::MissingExpectation,
            Mutation::ExtraExpectation,
        ] {
            let mut draft = fixture.staged_draft(phase);
            crate::core::provider::mutate_method_catalog_for_test(&mut draft.core, mutation);
            assert!(
                fixture
                    .check_staged(&draft, &mut TypeWorkBudget::unbounded())
                    .is_err(),
                "{phase:?} catalog {mutation:?}"
            );
        }
        for mutation in 0..5 {
            let mut draft = fixture.staged_draft(phase);
            crate::core::provider::mutate_polymorphic_prerequisite_for_test(
                &mut draft.core,
                mutation,
            );
            assert!(
                fixture
                    .check_staged(&draft, &mut TypeWorkBudget::unbounded())
                    .is_err(),
                "{phase:?} prerequisite {mutation}"
            );
        }
        let mut draft = fixture.staged_draft(phase);
        let root = draft.staged_externals.as_ref().unwrap().occurrences[0]
            .node
            .unwrap();
        crate::core::provider::swap_dictionary_methods_for_test(&mut draft.core, root);
        assert!(
            fixture
                .check_staged(&draft, &mut TypeWorkBudget::unbounded())
                .is_err(),
            "equal-typed second/third order"
        );
    }
}

#[test]
fn provider_external_parameterized_storage_uses_complete_instantiated_payloads() {
    let helper = format!(
        "{HELPER}pub type Box<A> = Box(A)\npub type Grow<A> = Leaf(A)\n| Next(Grow<(A, Unit -> Unit)>)\npub opaque type Opaque = Hidden\npub opaque newtype TransparentStorage<A> = TransparentStorage(A)\n"
    );
    let fixture = HelperFixture::new(&source(), &helper);
    let draft = fixture.draft(Phase::Acquire);
    let imported = fixture.fixture.resolved.imported_facts();
    let nominal = |name: &str| {
        imported
            .nominals()
            .find(|f| f.display_spelling.as_deref() == Some(name))
            .unwrap()
            .id
    };
    let apply = |id, ty| Type::Application(Box::new(Type::Nominal(id)), Box::new(ty));
    let box_int = apply(nominal("Box"), Type::Int);
    let header = fixture
        .fixture
        .elaborator()
        .check_provider_header(
            &fixture.fixture.resolved,
            &fixture.fixture.resolved.resources()[0],
        )
        .unwrap();
    let unsafe_types = [
        apply(
            nominal("Box"),
            Type::Function(Box::new(Type::Unit), Box::new(Type::Unit)),
        ),
        apply(nominal("Box"), header.state_association.state.clone()),
        Type::Tuple(Box::new([
            box_int.clone(),
            apply(
                nominal("Box"),
                Type::Function(Box::new(Type::Unit), Box::new(Type::Unit)),
            ),
        ])),
        apply(nominal("Grow"), Type::Int),
        Type::Nominal(nominal("Opaque")),
    ];
    let check = |ty: &Type, work: &mut TypeWorkBudget| {
        crate::core::provider::check_external_data_type_for_test(&draft.core, imported, ty, work)
    };
    for ty in unsafe_types {
        assert!(check(&ty, &mut TypeWorkBudget::unbounded()).is_err());
        discard_type_iteratively(ty);
    }
    for ty in [box_int, apply(nominal("TransparentStorage"), Type::Int)] {
        let mut measured = TypeWorkBudget::unbounded();
        check(&ty, &mut measured).unwrap();
        let cost = measured.used();
        for prefix in [0, 11] {
            let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
            short.charge(prefix).unwrap();
            assert!(check(&ty, &mut short).is_err());
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                exact.charge(prefix).unwrap();
                check(&ty, &mut exact).unwrap();
                assert_eq!(exact.used(), prefix + cost);
            }
        }
        discard_type_iteratively(ty);
    }
}

#[test]
fn provider_external_parameterized_storage_deep_refusal_has_guarded_disposal() {
    let fixture = HelperFixture::new(&source(), &format!("{HELPER}pub type Box<A> = Box(A)\n"));
    let draft = fixture.draft(Phase::Acquire);
    let id = fixture
        .fixture
        .resolved
        .imported_facts()
        .nominals()
        .find(|f| f.display_spelling.as_deref() == Some("Box"))
        .unwrap()
        .id;
    let mut ty = Type::Int;
    for _ in 0..8192 {
        ty = Type::Application(Box::new(Type::Nominal(id)), Box::new(ty));
    }
    let ty = crate::types::IterativeTypeOwner::new(ty);
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(move || {
            for limit in [0, 64, 100_000] {
                let result = crate::core::provider::check_external_data_type_for_test(
                    &draft.core,
                    fixture.fixture.resolved.imported_facts(),
                    &ty,
                    &mut TypeWorkBudget::with_limit(limit),
                );
                assert!(result.is_err());
            }
            drop(ty);
            drop(draft);
            drop(fixture);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn provider_external_nested_source_authority_and_selected_control_remain_exact() {
    let source = constrained_source()
        .replace(
            "Helper.normalize config",
            &nested_normalize("config", "Helper"),
        )
        .replace(
            "Helper.normalize error",
            &nested_normalize("error", "Helper"),
        );
    let helper = nested_constrained_helper();
    let missing = source.replace("import helper (impl Pass, impl Stamp)", "");
    let fixture = HelperFixture::new(&missing, &helper);
    let f = &fixture.fixture;
    let definition = &f.resolved.resources()[0];
    let header = f
        .elaborator()
        .check_provider_header(&f.resolved, definition)
        .unwrap();
    for phase in [Phase::Acquire, Phase::Finish] {
        assert!(
            f.elaborator()
                .compile_provider_lifecycle_with_externals(
                    definition,
                    &header,
                    phase,
                    f.resolved.imported_facts()
                )
                .is_err()
        );
    }
    let noisy = helper.replace("pub type Box", "pub effect Noise {\nask : Unit -> Unit\n}\npub type Box").replace("first (value, ignored) = value", "first (value, ignored) = {\nlet noise = handle (perform Noise.ask ()) with Noise {\nask () => resume ()\n}\nvalue\n}");
    let fixture = HelperFixture::new(&source, &noisy);
    for phase in [Phase::Acquire, Phase::Finish] {
        let draft = fixture.staged_draft(phase);
        assert!(
            fixture
                .check_staged(&draft, &mut TypeWorkBudget::unbounded())
                .is_err(),
            "selected prerequisite control {phase:?}"
        );
    }
    let helper = format!(
        "{helper}pub effect Noise {{\nask : Unit -> Unit\n}}\npub unrelated : Unit -> Unit\nunrelated () = handle (perform Noise.ask ()) with Noise {{\nask () => resume ()\n}}\n"
    );
    let fixture = HelperFixture::new(&source, &helper);
    for phase in [Phase::Acquire, Phase::Finish] {
        let draft = fixture.staged_draft(phase);
        fixture
            .check_staged(&draft, &mut TypeWorkBudget::unbounded())
            .unwrap();
    }
}

fn unused_noisy_selected_helper() -> String {
    nested_constrained_helper().replace("normalize value = stamp ((third(second(first((first((value, true)), ())))), 7))", "normalize value = third value")
        .replace("pub type Box", "pub effect Noise {\nask : Unit -> Unit\n}\npub type Box")
        .replace("second value = value", "second value = {\nlet noise = handle (perform Noise.ask ()) with Noise {\nask () => resume ()\n}\nvalue\n}")
        .replace("first (value, ignored) = value", "first (value, ignored) = {\nlet noise = handle (perform Noise.ask ()) with Noise {\nask () => resume ()\n}\nvalue\n}")
}

#[test]
fn provider_external_dictionary_carriers_cannot_be_reused_as_unproved_source_calls() {
    let source = constrained_source()
        .replace(
            "Helper.normalize config",
            &nested_normalize("config", "Helper"),
        )
        .replace(
            "Helper.normalize error",
            &nested_normalize("error", "Helper"),
        );
    let helper = unused_noisy_selected_helper();
    let fixture = HelperFixture::new(&source, &helper);
    for mutation in 0..8 {
        let mut draft = fixture.staged_draft(Phase::Acquire);
        fixture
            .check_staged(&draft, &mut TypeWorkBudget::unbounded())
            .unwrap();
        let root = draft.staged_externals.as_ref().unwrap().occurrences[0]
            .node
            .unwrap();
        crate::core::provider::reuse_dictionary_producer_as_call_for_test(
            &mut draft.core,
            root,
            mutation,
        );
        assert!(
            fixture
                .check_staged(&draft, &mut TypeWorkBudget::unbounded())
                .is_err(),
            "dictionary reuse {mutation} has no selected source-call relation"
        );
    }
}

#[test]
fn provider_external_local_source_projection_preserves_dictionary_call_authority() {
    for nested in [false, true] {
        let forward = |input: &str, ty: &str| {
            format!(
                "{{\nlet forward : Native.{ty} -> Native.{ty} = fn(value) {{\n{}\n}}\nforward {input}\n}}",
                if nested {
                    nested_normalize("value", "Helper")
                } else {
                    "match Helper.normalize value {\nmapped => mapped\n}".to_string()
                }
            )
        };
        let source = constrained_source()
            .replace("Helper.normalize config", &forward("config", "OpenConfig"))
            .replace("Helper.normalize error", &forward("error", "CloseError"));
        let fixture = HelperFixture::new(
            &source,
            &if nested {
                unused_noisy_selected_helper()
            } else {
                CONSTRAINED_HELPER.to_string()
            },
        );
        fs::remove_file(fixture.path.join("helper.ash")).unwrap();
        for phase in [Phase::Acquire, Phase::Finish] {
            for mutation in 0..9 {
                let mut draft = fixture.staged_draft(phase);
                fixture
                    .check_staged(&draft, &mut TypeWorkBudget::unbounded())
                    .unwrap();
                let root = draft.staged_externals.as_ref().unwrap().occurrences[0]
                    .node
                    .unwrap();
                crate::core::provider::reuse_dictionary_producer_as_call_for_test(
                    &mut draft.core,
                    root,
                    mutation,
                );
                let result = fixture.check_staged(&draft, &mut TypeWorkBudget::unbounded());
                assert!(
                    result.is_err(),
                    "local projected dictionary reuse {mutation} {phase:?}: {result:?}"
                );
            }
        }
    }
}

#[test]
fn provider_external_local_target_and_source_ledger_are_independent() {
    let forward = |input: &str, ty: &str| {
        format!(
            "{{\nlet alternative : Native.{ty} -> Native.{ty} = Helper.noisy\nlet forward : Native.{ty} -> Native.{ty} = fn(value) {{\nHelper.identity value\n}}\nforward {input}\n}}"
        )
    };
    let source = source()
        .replace("Helper.identity config", &forward("config", "OpenConfig"))
        .replace("Helper.identity error", &forward("error", "CloseError"));
    let helper = format!(
        "{HELPER}{}",
        NOISY_IDENTITY_HELPER.replace("identity", "noisy")
    );
    let fixture = HelperFixture::new(&source, &helper);
    fs::remove_file(fixture.path.join("helper.ash")).unwrap();
    for phase in [Phase::Acquire, Phase::Finish] {
        for mutation in 0..5 {
            let mut draft = fixture.staged_draft(phase);
            fixture
                .check_staged(&draft, &mut TypeWorkBudget::unbounded())
                .unwrap();
            let staged = draft.staged_externals.as_mut().unwrap();
            let identity = staged.occurrences.iter().find(|occurrence| matches!(occurrence.occurrence.term, crate::resolved::ResolvedTermName::Global(binder) if binder == fixture.globals["identity"])).unwrap().node.unwrap();
            let noisy = staged.occurrences.iter().find(|occurrence| matches!(occurrence.occurrence.term, crate::resolved::ResolvedTermName::Global(binder) if binder == fixture.globals["noisy"])).unwrap().node.unwrap();
            match mutation {
                0 => crate::core::provider::redirect_local_source_call_for_test(
                    &mut draft.core,
                    identity,
                    noisy,
                ),
                1 => staged.occurrences[0].node = Some(identity),
                2 => {
                    discard_type_iteratively(std::mem::replace(
                        &mut staged.occurrences[0].arguments.0[0],
                        Type::Int,
                    ));
                }
                3 => {
                    staged.occurrences[0].occurrence.term =
                        crate::resolved::ResolvedTermName::Global(fixture.globals["identity"])
                }
                4 => {
                    staged.occurrences[0].occurrence.origin =
                        staged.occurrences[1].occurrence.origin.clone()
                }
                _ => unreachable!(),
            }
            assert!(
                fixture
                    .check_staged(&draft, &mut TypeWorkBudget::unbounded())
                    .is_err(),
                "local target/ledger mutation {mutation} {phase:?}"
            );
        }
    }
}

#[test]
fn provider_source_wrapper_origin_refusal_owns_deep_types_until_handoff() {
    let fixture = HelperFixture::new(&source(), HELPER);
    let draft = fixture.staged_draft(Phase::Acquire);
    let global = fixture
        .fixture
        .resolved
        .imported_facts()
        .global(fixture.globals["identity"])
        .unwrap();
    let nested = |depth| {
        let mut ty = Type::Unit;
        for _ in 0..depth {
            ty = Type::Tuple(vec![ty].into_boxed_slice());
        }
        crate::types::IterativeTypeOwner::new(ty)
    };
    // The actual emitter refuses 8192 layers before the wrapper handoff.
    // The 128-layer payload exercises all admitted origin refusal positions;
    // it did not demonstrate an overflow before the ordering repair.
    let refused_argument = nested(8192);
    let argument = nested(128);
    let args = std::slice::from_ref(&*argument);
    let (legacy, guarded) = crate::core::provider::source_wrapper_origin_prefixes_for_test(
        &draft.core,
        crate::resolved::ProviderGlobalFact::Imported(global),
        args,
    );
    let check = |arguments, work: &mut TypeWorkBudget| {
        crate::core::provider::source_wrapper_for_test(
            &draft.core,
            crate::resolved::ProviderGlobalFact::Imported(global),
            arguments,
            fixture.fixture.resolved.imported_facts(),
            work,
        )
    };
    std::thread::scope(|scope| {
        let run = || {
            let mut deep_work = TypeWorkBudget::unbounded();
            assert!(matches!(
                check(std::slice::from_ref(&*refused_argument), &mut deep_work),
                Err(ref error) if error.reason() == crate::core::ValidationReason::Resource
            ));
            let mut measured = TypeWorkBudget::unbounded();
            check(args, &mut measured).unwrap();
            let cost = measured.used();
            for prefix in [0, 17] {
                let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
                short.charge(prefix).unwrap();
                assert!(matches!(
                    check(args, &mut short),
                    Err(ref error) if error.reason() == crate::core::ValidationReason::Resource
                ));
                for _ in 0..2 {
                    let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                    exact.charge(prefix).unwrap();
                    check(args, &mut exact).unwrap();
                    assert_eq!(exact.used(), prefix + cost);
                }
            }
            eprintln!("wrapper admitted payload depth=128 caller cost={cost}");
            for (stage, allowance) in legacy.into_iter().enumerate() {
                eprintln!("wrapper legacy origin refusal stage={stage} allowance={allowance}");
                let mut work = TypeWorkBudget::with_limit(allowance);
                assert!(matches!(
                    check(args, &mut work),
                    Err(ref error) if error.reason() == crate::core::ValidationReason::Resource
                ));
            }
            for (stage, allowance) in guarded.into_iter().enumerate() {
                for prefix in [0, 17] {
                    eprintln!("wrapper guarded origin refusal stage={stage} prefix={prefix}");
                    let mut work = TypeWorkBudget::with_limit(prefix + allowance);
                    work.charge(prefix).unwrap();
                    assert!(matches!(
                        check(args, &mut work),
                        Err(ref error) if error.reason() == crate::core::ValidationReason::Resource
                    ));
                    assert_eq!(work.used(), prefix + allowance);
                }
            }
        };
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn_scoped(scope, run)
            .unwrap()
            .join()
            .unwrap();
    });
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
