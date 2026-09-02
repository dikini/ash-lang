use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    elaborate::{TypeError, check_module},
    kind::{KindError, KindExpectation, KindFailure, KindReason},
    module::{ModuleRoots, load_module_graph},
    resolve::{ResolveModuleError, resolve_module},
    resolved::ResolvedModule,
    source::Span,
    types::Kind,
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct KindFixture {
    path: PathBuf,
    text: String,
}

impl KindFixture {
    fn new(text: &str) -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let directory =
                std::env::temp_dir().join(format!("ash-resolved-kind-{}-{id}", std::process::id()));
            match fs::create_dir(&directory) {
                Ok(()) => {
                    let path = directory.join("kinds.ash");
                    fs::write(&path, text).expect("the resolved-kind fixture should be writable");
                    return Self {
                        path,
                        text: text.to_owned(),
                    };
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("resolved-kind fixture directory creation failed: {error}"),
            }
        }
    }

    fn resolve(&self) -> Result<ResolvedModule, ResolveModuleError> {
        let graph = load_module_graph(&self.path, &ModuleRoots::empty())
            .expect("the resolved-kind fixture should load");
        resolve_module(&graph.modules()[0], &[])
    }

    fn span_of(&self, needle: &str, occurrence: usize) -> Span {
        let start = self
            .text
            .match_indices(needle)
            .nth(occurrence)
            .map(|(start, _)| start)
            .expect("the expected span text should occur");
        let graph = load_module_graph(&self.path, &ModuleRoots::empty())
            .expect("the resolved-kind fixture should reload");
        graph.modules()[0]
            .source()
            .span(
                ash::source::ByteRange::new(
                    u32::try_from(start).expect("the fixture offset should fit"),
                    u32::try_from(start + needle.len()).expect("the fixture offset should fit"),
                )
                .expect("the fixture range should be ordered"),
            )
            .expect("the fixture span should belong to its source")
    }
}

impl Drop for KindFixture {
    fn drop(&mut self) {
        if let Some(directory) = self.path.parent() {
            let _ = fs::remove_dir_all(directory);
        }
    }
}

fn resolve_valid(text: &str) -> ResolvedModule {
    KindFixture::new(text)
        .resolve()
        .expect("the resolved kind matrix should succeed")
}

fn kind_error(fixture: &KindFixture) -> KindError {
    match fixture
        .resolve()
        .expect_err("the malformed kind fixture should fail")
    {
        ResolveModuleError::Kind(KindFailure::Source(error)) => *error,
        ResolveModuleError::Kind(error) => {
            panic!("expected a source kind rejection, found {error:?}")
        }
        ResolveModuleError::Resolution(error) => {
            panic!("name resolution stole kind-error ownership: {error:?}")
        }
    }
}

fn arrow(domain: Kind, codomain: Kind) -> Kind {
    Kind::Arrow(Box::new(domain), Box::new(codomain))
}

#[test]
fn effect_row_is_an_atomic_fixed_kind_not_a_value_kind_alias() {
    let row = Kind::EffectRow;

    assert_eq!(row.to_string(), "EffectRow");
    assert_eq!(row, row.clone());
    assert_ne!(row, Kind::Type);
    assert_eq!(
        arrow(Kind::EffectRow, Kind::Type).to_string(),
        "EffectRow -> Type",
    );
}

fn assert_primary(error: &KindError, span: Span) {
    assert_eq!(error.primary.span().range(), span.range());
}

fn later_owner_reason(text: &str) -> String {
    let resolved = KindFixture::new(text)
        .resolve()
        .expect("the kind stage should defer the established later-owned fact");
    match check_module(resolved).expect_err("the later owner should reject the fact") {
        TypeError::Interface(diagnostic) => diagnostic.reason.to_string(),
        error => panic!("expected an interface-owned failure, found {error:?}"),
    }
}

#[test]
fn total_resolved_kinding_accepts_every_type_form_and_value_site() {
    let resolved = resolve_valid(concat!(
        "type Token = Token\n",
        "type Option<A> =\nNone\n| Some(A)\n",
        "type Apply<F : Type -> Type, A> = Apply(F<A>)\n",
        "type Left<F : Type -> Type> = Left(Right<F>)\n",
        "type Right<F : Type -> Type> = Right(Left<F>)\n\n",
        "interface Higher<F : Type -> Type> {\n",
        "use : F<Int> -> F<Int>\n",
        "}\n\n",
        "matrix<F : Type -> Type, A> : (Int, Bool, Unit, Token, Option<A>, Apply<F, A>, F<A>, A -> A) -> Unit where Higher<F>, Higher<Option>\n",
        "matrix value = {\n",
        "    let local : Option<Int> = None\n",
        "    ()\n",
        "}\n\n",
        "fn operational<F : Type -> Type>(value : F<Int>) -> F<Int> where Higher<F> {\n",
        "    let local : F<Int> = value\n",
        "    let rec recursive : F<Int> = local\n",
        "    recursive\n",
        "}\n\n",
        "impl<F : Type -> Type> Higher<F> where Higher<F> {\n",
        "use value = {\n",
        "    let local : F<Int> = value\n",
        "    local\n",
        "}\n",
        "}\n",
    ));

    assert_eq!(resolved.registry().nominals().len(), 5);
    assert_eq!(resolved.interfaces().len(), 1);
    assert_eq!(resolved.implementations().len(), 1);
    assert_eq!(resolved.definitions().len(), 2);
}

#[test]
fn residual_constructor_kind_is_valid_for_a_higher_kinded_interface_argument() {
    let resolved = resolve_valid(concat!(
        "type Option<A> =\nNone\n| Some(A)\n\n",
        "interface Higher<F : Type -> Type> {\n",
        "use : F<Int> -> F<Int>\n",
        "}\n\n",
        "accept : Unit -> Unit where Higher<Option>\n",
        "accept value = value\n",
    ));

    assert_eq!(resolved.definitions().len(), 1);
}

#[test]
fn value_boundaries_all_require_kind_type() {
    let cases = [
        "type Option<A> =\nNone\n| Some(A)\ntype Bad = Bad(Option)\n",
        "type Option<A> =\nNone\n| Some(A)\nbad : Unit -> Option\nbad () = None\n",
        concat!(
            "type Option<A> =\nNone\n| Some(A)\n",
            "interface Bad<A> {\nmethod : Option\n}\n",
        ),
        concat!(
            "type Option<A> =\nNone\n| Some(A)\n",
            "fn bad(value : Option) -> Unit {\n()\n}\n",
        ),
        concat!(
            "type Option<A> =\nNone\n| Some(A)\n",
            "fn bad(value : Unit) -> Option {\nvalue\n}\n",
        ),
        concat!(
            "type Option<A> =\nNone\n| Some(A)\n",
            "main : Unit -> Unit\n",
            "main () = {\nlet value : Option = None\n()\n}\n",
        ),
        concat!(
            "type Option<A> =\nNone\n| Some(A)\n",
            "main : Unit -> Unit\n",
            "main () = {\nlet rec value : Option = None\n()\n}\n",
        ),
    ];

    for text in cases {
        let fixture = KindFixture::new(text);
        let error = kind_error(&fixture);
        assert_eq!(error.reason, KindReason::ExpectedType, "source:\n{text}");
        assert_eq!(error.expected_kind(), Some(&Kind::Type), "source:\n{text}");
        assert_eq!(
            error.found_kind(),
            Some(&arrow(Kind::Type, Kind::Type)),
            "source:\n{text}"
        );
    }
}

#[test]
fn bare_nominal_in_a_value_type_reports_structured_expected_type() {
    let fixture = KindFixture::new(concat!(
        "type Option<A> =\nNone\n| Some(A)\n",
        "bad : Unit -> Option\n",
        "bad () = None\n",
    ));
    let error = kind_error(&fixture);

    assert_eq!(error.reason, KindReason::ExpectedType);
    assert_eq!(error.expected_kind(), Some(&Kind::Type));
    assert_eq!(error.found_kind(), Some(&arrow(Kind::Type, Kind::Type)));
    assert_primary(&error, fixture.span_of("Option", 1));
    assert_eq!(error.related.len(), 1);
    assert_eq!(
        error.related[0].span().range(),
        fixture
            .span_of("type Option<A> =\nNone\n| Some(A)", 0)
            .range()
    );
}

#[test]
fn applying_a_type_kinded_binder_reports_not_applicable() {
    let fixture = KindFixture::new("bad<A> : A<Int> -> Unit\nbad value = ()\n");
    let error = kind_error(&fixture);

    assert_eq!(error.reason, KindReason::NotApplicable);
    assert_eq!(error.expected_kind(), None);
    assert_eq!(
        error.expectation(),
        &KindExpectation::Function { domain: Kind::Type }
    );
    assert_eq!(error.found_kind(), Some(&Kind::Type));
    assert_primary(&error, fixture.span_of("A<Int>", 0));
    assert_eq!(error.related.len(), 1);
    assert_eq!(
        error.related[0].span().range(),
        fixture.span_of("A", 0).range()
    );
}

#[test]
fn omitted_lists_do_not_infer_arrow_kinds_in_this_phase() {
    // This is the current increment's compatibility boundary. It records no
    // permanent language principle: a later proposal may add bounded,
    // declaration-local kind inference.
    for text in [
        "legacy : F<Int> -> Unit\nlegacy value = ()\n",
        "fn legacy(value : F<Int>) -> Unit {\n()\n}\n",
        concat!(
            "interface Witness<A> {\n",
            "witness : A -> Bool\n",
            "}\n\n",
            "impl Witness<F<Int>> {\n",
            "witness value = true\n",
            "}\n",
        ),
    ] {
        let fixture = KindFixture::new(text);
        let error = kind_error(&fixture);

        assert_eq!(error.reason, KindReason::NotApplicable, "source:\n{text}");
        assert_eq!(
            error.expectation(),
            &KindExpectation::Function { domain: Kind::Type },
            "source:\n{text}"
        );
        assert_eq!(error.expected_kind(), None, "source:\n{text}");
        assert_eq!(error.found_kind(), Some(&Kind::Type), "source:\n{text}");
        assert_primary(&error, fixture.span_of("F<Int>", 0));
    }
}

#[test]
fn application_domain_mismatch_reports_argument_kind_and_declaration() {
    let fixture = KindFixture::new(concat!(
        "type Box<F : Type -> Type> = Box\n",
        "bad : Box<Int> -> Unit\n",
        "bad value = ()\n",
    ));
    let error = kind_error(&fixture);

    assert_eq!(error.reason, KindReason::Argument);
    assert_eq!(error.expected_kind(), Some(&arrow(Kind::Type, Kind::Type)));
    assert_eq!(error.found_kind(), Some(&Kind::Type));
    assert_primary(&error, fixture.span_of("Int", 0));
    assert_eq!(error.related.len(), 1);
    assert_eq!(
        error.related[0].span().range(),
        fixture
            .span_of("type Box<F : Type -> Type> = Box", 0)
            .range()
    );
}

#[test]
fn implementation_head_kind_argument_precedes_overlap_and_membership() {
    let fixture = KindFixture::new(concat!(
        "type Option<A> =\nNone\n| Some(A)\n\n",
        "interface Build<Constructor : Type -> Type> {\n",
        "build : Constructor<Int> -> Int\n",
        "}\n\n",
        "impl Build<Option<Int>> {\n}\n",
        "impl Build<Option<Int>> {\n}\n",
    ));
    let error = kind_error(&fixture);

    assert_eq!(error.reason, KindReason::Argument);
    assert_eq!(error.expected_kind(), Some(&arrow(Kind::Type, Kind::Type)));
    assert_eq!(error.found_kind(), Some(&Kind::Type));
    assert_primary(&error, fixture.span_of("Option<Int>", 0));
    assert_eq!(error.related.len(), 1);
    assert_eq!(
        error.related[0].span().range(),
        fixture.span_of("Constructor", 0).range()
    );
}

#[test]
fn implementation_prerequisite_kind_argument_precedes_termination_and_membership() {
    let fixture = KindFixture::new(concat!(
        "type Triple<First, Second, Third> = Triple(First, Second, Third)\n\n",
        "interface Build<Constructor : Type -> Type> {\n",
        "build : Constructor<Int> -> Int\n",
        "}\n\n",
        "impl<First : Type, Second : Type> Build<Triple<First, Second>> ",
        "where Build<Triple<Second, First, Int>> {\n",
        "}\n",
    ));
    let error = kind_error(&fixture);

    assert_eq!(error.reason, KindReason::Argument);
    assert_eq!(error.expected_kind(), Some(&arrow(Kind::Type, Kind::Type)));
    assert_eq!(error.found_kind(), Some(&Kind::Type));
    assert_primary(&error, fixture.span_of("Triple<Second, First, Int>", 0));
    assert_eq!(error.related.len(), 1);
    assert_eq!(
        error.related[0].span().range(),
        fixture.span_of("Constructor", 0).range()
    );
}

#[test]
fn nested_tuple_and_function_failures_use_the_causal_child_occurrence() {
    for text in [
        concat!(
            "type Option<A> =\nNone\n| Some(A)\n",
            "bad : (Int, (Option, Bool)) -> Unit\n",
            "bad value = ()\n",
        ),
        concat!(
            "type Option<A> =\nNone\n| Some(A)\n",
            "bad : (Int -> (Bool -> Option)) -> Unit\n",
            "bad value = ()\n",
        ),
    ] {
        let fixture = KindFixture::new(text);
        let error = kind_error(&fixture);
        assert_eq!(error.reason, KindReason::ExpectedType);
        assert_primary(&error, fixture.span_of("Option", 1));
        assert_eq!(error.related.len(), 1);
        assert_eq!(
            error.related[0].span().range(),
            fixture
                .span_of("type Option<A> =\nNone\n| Some(A)", 0)
                .range()
        );
    }
}

#[test]
fn nested_residual_application_succeeds_and_overapplication_stops_at_the_first_non_arrow() {
    resolve_valid(concat!(
        "type Option<A> =\nNone\n| Some(A)\n",
        "type Lift<F : Type -> Type, A> = Lift(F<A>)\n\n",
        "interface Higher<F : Type -> Type> {\n",
        "higher : F<Int> -> Unit\n",
        "}\n\n",
        "accept : Unit -> Unit where Higher<Lift<Option>>\n",
        "accept value = value\n",
    ));

    let fixture = KindFixture::new(concat!(
        "type Option<A> =\nNone\n| Some(A)\n",
        "bad : Option<Int, Bool> -> Unit\n",
        "bad value = ()\n",
    ));
    let error = kind_error(&fixture);
    assert_eq!(error.reason, KindReason::NotApplicable);
    assert_eq!(
        error.expectation(),
        &KindExpectation::Function { domain: Kind::Type }
    );
    assert_eq!(error.found_kind(), Some(&Kind::Type));
    assert_primary(&error, fixture.span_of("Option<Int, Bool>", 0));
}

#[test]
fn constructor_multi_field_kind_mismatch_uses_the_exact_argument_span() {
    let fixture = KindFixture::new(concat!(
        "type Holder<F : Type -> Type> = Holder\n",
        "type Bad = Bad(Int, Holder<Int>, Bool)\n",
    ));
    let error = kind_error(&fixture);
    assert_eq!(error.reason, KindReason::Argument);
    assert_eq!(error.expected_kind(), Some(&arrow(Kind::Type, Kind::Type)));
    assert_eq!(error.found_kind(), Some(&Kind::Type));
    assert_primary(&error, fixture.span_of("Int", 1));
    assert_eq!(error.related.len(), 1);
    assert_eq!(
        error.related[0].span().range(),
        fixture
            .span_of("type Holder<F : Type -> Type> = Holder", 0)
            .range()
    );
}

#[test]
fn top_level_kind_failures_follow_declaration_order() {
    let fixture = KindFixture::new(concat!(
        "type Option<A> =\nNone\n| Some(A)\n",
        "first : Option -> Unit\n",
        "first value = ()\n",
        "second : Unit -> Option\n",
        "second value = None\n",
    ));
    let error = kind_error(&fixture);
    assert_eq!(error.reason, KindReason::ExpectedType);
    assert_primary(&error, fixture.span_of("Option", 1));
}

#[test]
fn present_method_type_parameter_kinds_are_fixed_and_checked() {
    resolve_valid(concat!(
        "interface Functor<F : Type -> Type> {\n",
        "map<A, G : Type -> Type> : (A, G<A>) -> F<A>\n",
        "}\n",
    ));

    let fixture = KindFixture::new(concat!(
        "interface Bad<A> {\n",
        "bad<F : Type -> Type> : F -> A\n",
        "}\n",
    ));
    let error = kind_error(&fixture);
    assert_eq!(error.reason, KindReason::ExpectedType);
    assert_eq!(error.expected_kind(), Some(&Kind::Type));
    assert_eq!(error.found_kind(), Some(&arrow(Kind::Type, Kind::Type)));
    assert_primary(&error, fixture.span_of("F", 1));
    assert_eq!(error.related.len(), 1);
    assert_eq!(
        error.related[0].span().range(),
        fixture.span_of("F", 0).range()
    );

    let fixture = KindFixture::new(concat!(
        "interface Bad<A> {\n",
        "bad<B> : B<Int> -> A\n",
        "}\n",
    ));
    let error = kind_error(&fixture);
    assert_eq!(error.reason, KindReason::NotApplicable);
    assert_eq!(
        error.expectation(),
        &KindExpectation::Function { domain: Kind::Type }
    );
    assert_eq!(error.found_kind(), Some(&Kind::Type));
    assert_primary(&error, fixture.span_of("B<Int>", 0));
    assert_eq!(error.related.len(), 1);
    assert_eq!(
        error.related[0].span().range(),
        fixture.span_of("B", 1).range()
    );
}

#[test]
fn method_local_candidate_precedes_its_invalid_kind_application() {
    assert_eq!(
        later_owner_reason(concat!(
            "type Option<A> =\nNone\n| Some(A)\n\n",
            "interface Witness<A> {\n",
            "witness : G<Int> -> A\n",
            "later : Option -> A\n",
            "}\n",
        )),
        "interface.method-parameter",
    );
}

#[test]
fn method_local_candidate_precedes_a_later_top_level_kind_failure() {
    assert_eq!(
        later_owner_reason(concat!(
            "type Option<A> =\nNone\n| Some(A)\n\n",
            "interface Witness<A> {\n",
            "witness : G<Int> -> A\n",
            "}\n\n",
            "later : Option -> Unit\n",
            "later value = ()\n",
        )),
        "interface.method-parameter",
    );
}

#[test]
fn prerequisite_only_candidate_precedes_its_invalid_kind_application() {
    assert_eq!(
        later_owner_reason(concat!(
            "type Option<A> =\nNone\n| Some(A)\n",
            "type Head<A> = Head(A)\n",
            "interface Witness<A> {\n",
            "witness : A -> Bool\n",
            "}\n\n",
            "impl Witness<Head<A>> where Witness<B> {\n",
            "witness value = {\n",
            "let deferred : B = value\n",
            "let later : Option = None\n",
            "true\n",
            "}\n",
            "}\n",
        )),
        "impl.prerequisite-variable",
    );
}

#[test]
fn prerequisite_only_candidate_precedes_a_later_top_level_kind_failure() {
    assert_eq!(
        later_owner_reason(concat!(
            "type Option<A> =\nNone\n| Some(A)\n",
            "type Head<A> = Head(A)\n",
            "interface Witness<A> {\n",
            "witness : A -> Bool\n",
            "}\n\n",
            "impl Witness<Head<A>> where Witness<B> {\n",
            "witness value = {\n",
            "let deferred : B = value\n",
            "true\n",
            "}\n",
            "}\n\n",
            "later : Option -> Unit\n",
            "later value = ()\n",
        )),
        "impl.prerequisite-variable",
    );
}

#[test]
fn requirement_only_global_candidate_precedes_its_invalid_kind_application() {
    assert_eq!(
        later_owner_reason(concat!(
            "type Option<A> =\nNone\n| Some(A)\n",
            "interface Witness<A> {\n",
            "witness : A -> Bool\n",
            "}\n\n",
            "global<B : Type, A : Type> : A -> Bool where Witness<B>\n",
            "global value = {\n",
            "let later : Option = None\n",
            "true\n",
            "}\n",
        )),
        "constraint.undetermined-parameter",
    );
}

#[test]
fn requirement_only_global_candidate_precedes_a_later_top_level_kind_failure() {
    assert_eq!(
        later_owner_reason(concat!(
            "type Option<A> =\nNone\n| Some(A)\n",
            "interface Witness<A> {\n",
            "witness : A -> Bool\n",
            "}\n\n",
            "global<B : Type, A : Type> : A -> Bool where Witness<B>\n",
            "global value = true\n\n",
            "later : Option -> Unit\n",
            "later value = ()\n",
        )),
        "constraint.undetermined-parameter",
    );
}

#[test]
fn local_annotation_failures_follow_source_declaration_order() {
    let fixture = KindFixture::new(concat!(
        "type Option<A> =\nNone\n| Some(A)\n",
        "main : Unit -> Unit\n",
        "main () = {\n",
        "let first : Option = None\n",
        "let second : Option = None\n",
        "()\n",
        "}\n",
    ));

    let error = kind_error(&fixture);
    assert_eq!(error.reason, KindReason::ExpectedType);
    assert_primary(&error, fixture.span_of("Option", 1));
}

#[test]
fn nested_initializer_failure_precedes_a_later_declaration_header() {
    let fixture = KindFixture::new(concat!(
        "type Option<A> =\nNone\n| Some(A)\n",
        "main : Unit -> Unit\n",
        "main () = {\n",
        "let first = {\n",
        "let nested : Option = None\n",
        "()\n",
        "}\n",
        "let later : Option = None\n",
        "()\n",
        "}\n",
    ));

    let error = kind_error(&fixture);
    assert_eq!(error.reason, KindReason::ExpectedType);
    assert_primary(&error, fixture.span_of("Option", 1));
}
