use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    core::{validate_effect_modules, validate_modules},
    elaborate::{EffectElaborator, Elaborator, TypeError, TypeReason, check_module, link_modules},
    eval::{EffectTraceEvent, Value, evaluate, evaluate_effect},
    evidence_validation::validate_interface_evidence,
    module::{ModuleRoots, load_module_graph},
    resolve::{DependencyExports, ResolveModuleError, ResolveReason, resolve_module},
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct Fixture(PathBuf);

impl Fixture {
    fn new(text: &str) -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let directory = std::env::temp_dir().join(format!(
                "ash-scoped-evidence-interactions-{}-{id}",
                std::process::id()
            ));
            match fs::create_dir(&directory) {
                Ok(()) => {
                    let path = directory.join("entry.ash");
                    fs::write(&path, text).expect("interaction fixture should be writable");
                    return Self(path);
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("interaction fixture should be creatable: {error}"),
            }
        }
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        if let Some(directory) = self.0.parent() {
            let _ = fs::remove_dir_all(directory);
        }
    }
}

fn assert_execution(text: &str) {
    let fixture = Fixture::new(text);
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
        .expect("interaction fixture should load");
    let resolved =
        resolve_module(&graph.modules()[0], &[]).expect("interaction fixture should resolve");
    let checked = check_module(resolved).expect("interaction fixture should check");
    let linked = link_modules(vec![checked], graph.entry()).expect("fixture should link");
    let linked = validate_interface_evidence(linked).expect("evidence should authenticate");
    let mut elaborator =
        Elaborator::for_module_program(&linked).expect("Core namespace should fit");
    let typed = elaborator
        .synthesize_module_program(&linked)
        .expect("interaction fixture should elaborate");
    let program = elaborator.finish(typed.node).expect("Core should finish");
    let source = graph.modules()[0].source();
    let relation = [(graph.entry(), source.id())];
    let validated = validate_modules(program, &[source], &relation).expect("Core should validate");
    let observed = evaluate(&validated).expect("Core should execute");
    assert!(matches!(observed.value, Value::Integer(value) if value.to_string() == "42"));
    for transformed in [
        ash::core::transform::identity_traversal(&validated)
            .expect("identity traversal should rebuild"),
        ash::core::transform::fold_literal_primitives(&validated)
            .expect("literal folding should rebuild"),
    ] {
        let validated = validate_modules(transformed, &[source], &relation)
            .expect("transformed Core should validate");
        let observed = evaluate(&validated).expect("transformed Core should execute");
        assert!(matches!(observed.value, Value::Integer(value) if value.to_string() == "42"));
    }
}

fn assert_reason(text: &str, expected: &str) {
    let fixture = Fixture::new(text);
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
        .expect("rejected interaction should load");
    let resolved = resolve_module(&graph.modules()[0], &[])
        .expect("rejected interaction should resolve before checking");
    let error = check_module(resolved).expect_err("interaction must be rejected");
    let reason = match error {
        TypeError::Interface(diagnostic) => diagnostic.reason.to_string(),
        TypeError::Source(diagnostic) => diagnostic.reason.to_string(),
        error => panic!("expected a categorized source rejection, found {error:?}"),
    };
    assert_eq!(reason, expected);
}

fn assert_effect_execution(text: &str) {
    let fixture = Fixture::new(text);
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
        .expect("effect interaction should load");
    let resolved =
        resolve_module(&graph.modules()[0], &[]).expect("effect interaction should resolve");
    let checked = check_module(resolved).expect("effect interaction should check");
    let linked = link_modules(vec![checked], graph.entry()).expect("effect fixture should link");
    let linked = validate_interface_evidence(linked).expect("evidence should authenticate");
    let mut elaborator =
        EffectElaborator::for_module_program(&linked).expect("effect Core namespace should fit");
    let typed = elaborator
        .synthesize_effect_module_program(&linked)
        .expect("effect interaction should elaborate");
    let program = elaborator
        .finish(typed.node)
        .expect("effect Core should finish");
    let source = graph.modules()[0].source();
    let relation = [(graph.entry(), source.id())];
    let validated = validate_effect_modules(program, &[source], &relation)
        .expect("effect Core should validate");
    let observed = evaluate_effect(&validated).expect("effect Core should execute");
    assert!(matches!(observed.value, Value::Integer(ref value) if value.to_string() == "42"));
    assert_eq!(
        observed
            .effect_trace()
            .iter()
            .filter(|event| matches!(event, EffectTraceEvent::Request(_)))
            .count(),
        1,
    );
    assert_eq!(
        observed
            .effect_trace()
            .iter()
            .filter(|event| matches!(event, EffectTraceEvent::Resume(_)))
            .count(),
        1,
    );
    for transformed in [
        ash::core::transform::identity_effect_traversal(&validated)
            .expect("effect identity traversal should rebuild"),
        ash::core::transform::fold_effect_literal_primitives(&validated)
            .expect("effect literal folding should rebuild"),
    ] {
        let validated = validate_effect_modules(transformed, &[source], &relation)
            .expect("transformed effect Core should validate");
        let transformed =
            evaluate_effect(&validated).expect("transformed effect Core should execute");
        assert!(
            matches!(transformed.value, Value::Integer(ref value) if value.to_string() == "42")
        );
        assert_eq!(transformed.effect_trace(), observed.effect_trace());
    }
}

#[test]
fn identity_free_closure_retains_lexical_method_after_nominal_scope_returns() {
    assert_execution(
        r#"interface Read<A> {
    read : A -> Int
}
make : Unit -> (Unit -> Int)
make () = {
    newtype Token = Token(Int)
    let saved = Token(41)
    with Read<Token> {
        read ignored = match saved {
            Token(value) => value + 1
        }
    }
    fn(ignored) {
        read(saved)
    }
}
main : Unit -> Int
main () = make()()
"#,
    );
}

#[test]
fn selected_method_leaves_evidence_scope_while_outer_nominal_remains() {
    assert_execution(
        r#"interface Read<A> {
    read : A -> Int
}
main : Unit -> Int
main () = {
    newtype Token = Token(Int)
    let chosen : Token -> Int = {
        with Read<Token> {
            read (Token(value)) = value + 1
        }
        read
    }
    chosen(Token(41))
}
"#,
    );
}

#[test]
fn returned_method_does_not_export_lexical_evidence_to_later_occurrences() {
    assert_reason(
        r#"interface Read<A> {
    read : A -> Int
}
main : Unit -> Int
main () = {
    newtype Token = Token(Int)
    let chosen : Token -> Int = {
        with Read<Token> {
            read (Token(value)) = value + 1
        }
        read
    }
    read(Token(41))
}
"#,
        "constraint.unsatisfied",
    );
}

#[test]
fn lexical_method_precedes_matching_generic_concrete_implementation() {
    assert_execution(
        r#"type Box<A> = Box(A)
interface Read<A> {
    read : A -> Int
}
impl<A> Read<Box<A>> {
    read ignored = 0
}
main : Unit -> Int
main () = {
    newtype Token = Token(Int)
    with Read<Box<Token>> {
        read ignored = 42
    }
    read(Box(Token(0)))
}
"#,
    );
}

#[test]
fn repeated_execution_keeps_distinct_method_captures_for_one_static_source() {
    assert_execution(
        r#"interface Read<A> {
    read : A -> Int
}
make : Int -> (Unit -> Int)
make input = {
    newtype Token = Token(Int)
    let saved = Token(input)
    with Read<Token> {
        read ignored = match saved {
            Token(value) => value + 1
        }
    }
    fn(ignored) {
        read(saved)
    }
}
main : Unit -> Int
main () = {
    let left = make(19)
    let right = make(21)
    left() + right()
}
"#,
    );
}

#[test]
fn same_spelled_nested_nominals_have_distinct_lexical_evidence() {
    assert_execution(
        r#"interface Read<A> {
    read : A -> Int
}
main : Unit -> Int
main () = {
    newtype Token = Token(Int)
    with Read<Token> {
        read ignored = 20
    }
    let inner = {
        newtype Token = Token(Int)
        with Read<Token> {
            read ignored = 22
        }
        read(Token(0))
    }
    read(Token(0)) + inner
}
"#,
    );
}

#[test]
fn duplicate_active_lexical_key_is_rejected() {
    assert_reason(
        r#"interface Read<A> {
    read : A -> Int
}
main : Unit -> Int
main () = {
    newtype Token = Token(Int)
    with Read<Token> {
        read ignored = 20
    }
    with Read<Token> {
        read ignored = 42
    }
    read(Token(0))
}
"#,
        "evidence.duplicate",
    );
}

#[test]
fn local_identity_only_in_dependent_does_not_authorize_a_global_key() {
    assert_reason(
        r#"interface Convert<A, B> where A -> B {
    convert : A -> B
}
main : Unit -> Int
main () = {
    newtype Token = Token(Int)
    with Convert<Int, Token> {
        convert value = Token(value)
    }
    42
}
"#,
        "evidence.missing-local-key",
    );
}

#[test]
fn lexical_improvement_checks_an_already_known_dependent() {
    assert_reason(
        r#"interface Rel<A, B> where A -> B {
    relate : (A, B) -> Unit
}
main : Unit -> Int
main () = {
    newtype Token = Token(Int)
    with Rel<Token, Int> {
        relate pair = ()
    }
    let ignored = relate((Token(41), true))
    42
}
"#,
        "constraint.determination-conflict",
    );
}

#[test]
fn concrete_recursive_prerequisite_consumes_exact_lexical_evidence() {
    assert_execution(
        r#"type Box<A> = Box(A)
interface Read<A> {
    read : A -> Int
}
impl<A> Read<Box<A>> where Read<A> {
    read (Box(value)) = read(value)
}
main : Unit -> Int
main () = {
    newtype Token = Token(Int)
    with Read<Token> {
        read (Token(value)) = value + 1
    }
    read(Box(Token(41)))
}
"#,
    );
}

const RECURSIVE_COMPLETE_GOAL: &str = r#"type Box<A> = Box(A)
type Outer<A> = Outer(A)
interface Read<A, B> where A -> B {
    read : A -> B
}
interface Check<A> {
    check : A -> Int
}
impl<A> Read<Box<A>, Bool> {
    read ignored = true
}
impl<A> Check<Outer<A>> where Read<A, Bool> {
    check (Outer(value)) = match read(value) {
        true => 42
        false => 0
    }
}
main : Unit -> Int
main () = {
    newtype Token = Token(Int)
    with Read<Box<Token>, Int> {
        read ignored = 0
    }
    check(Outer(Box(Token(0))))
}
"#;

#[test]
fn recursive_complete_goal_skips_same_key_lexical_source_with_other_dependent() {
    assert_execution(RECURSIVE_COMPLETE_GOAL);
}

#[test]
fn pending_root_cannot_skip_lexical_improvement_for_a_concrete_dependent() {
    assert_reason(
        &RECURSIVE_COMPLETE_GOAL.replace(
            "    check(Outer(Box(Token(0))))",
            "    let observed : Bool = read(Box(Token(0)))\n    42",
        ),
        "constraint.determination-conflict",
    );
}

#[test]
fn lexical_method_keeps_enclosing_abstract_and_exact_current_contexts() {
    assert_execution(
        r#"type Box<A> = Box(A)
interface Read<A> {
    read : A -> Int
}
interface Check<A> {
    check : (A, Int) -> Int
}
impl Read<Int> {
    read value = value
}
impl<A> Check<Box<A>> where Read<A> {
    check (Box(value), fuel) = {
        newtype Token = Token(Int)
        with Read<Token> {
            read (Token(step)) = match step == 0 {
                true => read(value)
                false => check((Box(value), 0)) + 1
            }
        }
        read(Token(fuel))
    }
}
main : Unit -> Int
main () = check((Box(41), 1))
"#,
    );
}

const DELAYED_LEXICAL_SCOPE: &str = r#"interface Produce<A, B> where A -> B {
    produce : A -> B
}
interface Consume<A, B> where A -> B {
    consume : (A, B) -> Int
}
main : Unit -> Int
main () = {
    newtype Token = Token(Int)
    newtype Output = Output(Bool)
    with Consume<Output, Unit> {
        consume ignored = 42
    }
    let produced : Output = {
        with Produce<Token, Output> {
            produce ignored = Output(true)
        }
        produce(Token(0))
    }
    consume((produced, ()))
}
"#;

#[test]
fn delayed_inference_retains_the_occurrence_scope_after_inner_block_exit() {
    assert_execution(DELAYED_LEXICAL_SCOPE);
}

#[test]
fn lexical_improvement_does_not_unlock_an_initially_ineligible_root() {
    assert_reason(
        &DELAYED_LEXICAL_SCOPE.replace("let produced : Output =", "let produced ="),
        "constraint.ambiguous",
    );
}

#[test]
fn lexical_method_scheme_instantiates_independently_at_each_occurrence() {
    assert_execution(
        r#"interface Choose<I> {
    choose<A> : (I, A) -> A
}
main : Unit -> Int
main () = {
    newtype Token = Token(Unit)
    with Choose<Token> {
        choose (ignored, value) = value
    }
    let flag = choose((Token(()), true))
    match flag {
        true => choose((Token(()), 42))
        false => 0
    }
}
"#,
    );
}

#[test]
fn method_parameter_spelling_does_not_shadow_an_enclosing_type_name() {
    assert_execution(
        r#"interface Choose<I> {
    choose<A> : (I, A) -> A
}
run<A> : A -> Int
run outer = {
    newtype Token = Token(Unit)
    with Choose<Token> {
        choose (ignored, value) = {
            let saved : A = outer
            value
        }
    }
    match choose((Token(()), true)) {
        true => 42
        false => 0
    }
}
main : Unit -> Int
main () = run(0)
"#,
    );
}

#[test]
fn lexical_method_supports_a_nominal_representation_with_enclosing_parameter() {
    assert_execution(
        r#"interface Read<A> {
    read : A -> Int
}
run<A> : A -> Int
run value = {
    newtype Token = Token(A)
    with Read<Token> {
        read (Token(ignored)) = 42
    }
    read(Token(value))
}
main : Unit -> Int
main () = run(true)
"#,
    );
}

#[test]
fn lexical_source_accepts_higher_kinded_interface_arguments() {
    assert_execution(
        r#"type Box<A> = Box(A)
interface Read<F : Type -> Type, A> {
    read : F<A> -> Int
}
main : Unit -> Int
main () = {
    newtype Token = Token(Unit)
    with Read<Box, Token> {
        read ignored = 42
    }
    read(Box(Token(())))
}
"#,
    );
}

#[test]
fn key_admission_precedes_missing_method_inventory() {
    assert_reason(
        r#"interface Read<A> {
    read : A -> Int
}
main : Unit -> Int
main () = {
    with Read<Int> {
    }
    42
}
"#,
        "evidence.missing-local-key",
    );
}

#[test]
fn duplicate_key_precedes_missing_method_inventory() {
    assert_reason(
        r#"interface Read<A> {
    read : A -> Int
}
main : Unit -> Int
main () = {
    newtype Token = Token(Int)
    with Read<Token> {
        read ignored = 0
    }
    with Read<Token> {
    }
    42
}
"#,
        "evidence.duplicate",
    );
}

#[test]
fn active_lexical_keys_cannot_disagree_on_dependents() {
    assert_reason(
        r#"interface Read<A, B> where A -> B {
    read : A -> B
}
main : Unit -> Int
main () = {
    newtype Token = Token(Int)
    with Read<Token, Int> {
        read ignored = 0
    }
    with Read<Token, Bool> {
        read ignored = true
    }
    42
}
"#,
        "evidence.determination-conflict",
    );
}

#[test]
fn missing_lexical_method_is_owned_by_evidence_admission() {
    assert_reason(
        r#"interface Read<A> {
    read : A -> Int
}
main : Unit -> Int
main () = {
    newtype Token = Token(Int)
    with Read<Token> {
    }
    42
}
"#,
        "evidence.missing-method",
    );
}

#[test]
fn extra_lexical_method_is_owned_by_evidence_admission() {
    assert_reason(
        r#"interface Read<A> {
    read : A -> Int
}
main : Unit -> Int
main () = {
    newtype Token = Token(Int)
    with Read<Token> {
        read ignored = 0
        unknown ignored = 42
    }
    42
}
"#,
        "evidence.extra-method",
    );
}

#[test]
fn separated_duplicate_lexical_method_group_is_rejected() {
    assert_reason(
        r#"interface Both<A> {
    first : A -> Int
    second : A -> Int
}
main : Unit -> Int
main () = {
    newtype Token = Token(Int)
    with Both<Token> {
        first ignored = 0
        second ignored = 0
        first ignored = 42
    }
    42
}
"#,
        "evidence.duplicate-method",
    );
}

#[test]
fn supplied_effectful_method_preserves_its_declared_effect_row() {
    assert_effect_execution(
        r#"effect Ask {
    ask : Unit -> Int
}
interface Read<A> {
    read : A -> Int ! {Ask}
}
main : Unit -> Int
main () = {
    newtype Token = Token(Unit)
    with Read<Token> {
        read ignored = perform Ask.ask ()
    }
    handle (read(Token(()))) with Ask {
        ask ignored => resume 42
    }
}
"#,
    );
}

#[test]
fn supplied_method_may_use_its_own_nested_handler_resume() {
    assert_effect_execution(
        r#"effect Ask {
    ask : Unit -> Int
}
interface Read<A> {
    read : A -> Int
}
main : Unit -> Int
main () = {
    newtype Token = Token(Unit)
    with Read<Token> {
        read ignored = handle (perform Ask.ask ()) with Ask {
            ask ignored => resume 42
        }
    }
    read(Token(()))
}
"#,
    );
}

#[test]
fn supplied_method_cannot_capture_an_enclosing_handler_resume() {
    assert_reason(
        r#"effect Ask {
    ask : Unit -> Int
}
interface Read<A> {
    read : A -> Int
}
main : Unit -> Int
main () = handle (perform Ask.ask ()) with Ask {
    ask ignored => {
        newtype Token = Token(Unit)
        with Read<Token> {
            read ignored = resume 42
        }
        resume 42
    }
}
"#,
        "effect.resume-capture",
    );
}

#[test]
fn disjoint_evidence_scopes_may_supply_different_methods_for_one_nominal() {
    assert_execution(
        r#"interface Read<A> {
    read : A -> Int
}
main : Unit -> Int
main () = {
    newtype Token = Token(Int)
    let first = {
        with Read<Token> {
            read ignored = 20
        }
        read(Token(0))
    }
    let second = {
        with Read<Token> {
            read ignored = 22
        }
        read(Token(0))
    }
    first + second
}
"#,
    );
}

#[test]
fn supplied_method_may_capture_a_preceding_recursive_function() {
    assert_execution(
        r#"interface Read<A> {
    read : A -> Int
}
main : Unit -> Int
main () = {
    newtype Token = Token(Int)
    let rec count : Int -> Int = fn(value) {
        match value == 42 {
            true => 42
            false => count(value + 1)
        }
    }
    with Read<Token> {
        read (Token(value)) = count(value)
    }
    read(Token(0))
}
"#,
    );
}

#[test]
fn supplied_methods_cannot_select_their_own_source() {
    assert_reason(
        r#"interface Read<A> {
    read : A -> Int
}
main : Unit -> Int
main () = {
    newtype Token = Token(Int)
    with Read<Token> {
        read value = read(value)
    }
    42
}
"#,
        "constraint.unsatisfied",
    );
}

#[test]
fn supplied_methods_do_not_implicitly_select_siblings() {
    assert_reason(
        r#"interface Both<A> {
    first : A -> Int
    second : A -> Int
}
main : Unit -> Int
main () = {
    newtype Token = Token(Int)
    with Both<Token> {
        first value = second(value)
        second ignored = 42
    }
    42
}
"#,
        "constraint.unsatisfied",
    );
}

#[test]
fn same_spelled_nominal_does_not_inherit_outer_evidence() {
    assert_reason(
        r#"interface Read<A> {
    read : A -> Int
}
main : Unit -> Int
main () = {
    newtype Token = Token(Int)
    with Read<Token> {
        read ignored = 42
    }
    {
        newtype Token = Token(Int)
        read(Token(0))
    }
}
"#,
        "constraint.unsatisfied",
    );
}

#[test]
fn representation_does_not_receive_nominal_evidence() {
    assert_reason(
        r#"interface Read<A> {
    read : A -> Int
}
main : Unit -> Int
main () = {
    newtype Token = Token(Int)
    with Read<Token> {
        read ignored = 42
    }
    read(0)
}
"#,
        "constraint.unsatisfied",
    );
}

#[test]
fn supplied_method_equations_keep_coverage_checking() {
    assert_reason(
        r#"interface Read<A> {
    read : A -> Int
}
main : Unit -> Int
main () = {
    newtype Token = Token(Bool)
    with Read<Token> {
        read (Token(true)) = 42
    }
    42
}
"#,
        "coverage.non-exhaustive",
    );
}

#[test]
fn supplied_method_without_a_handler_keeps_resume_diagnostic_owner() {
    let fixture = Fixture::new(
        r#"interface Read<A> {
    read : A -> Int
}
main : Unit -> Int
main () = {
    newtype Token = Token(Int)
    with Read<Token> {
        read ignored = resume 42
    }
    42
}
"#,
    );
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
        .expect("resume outside a handler should parse");
    let error = resolve_module(&graph.modules()[0], &[])
        .expect_err("resume outside a handler must fail resolution");
    assert!(
        matches!(error, ResolveModuleError::Resolution(ref error)
            if error.reason == ResolveReason::ResumeOutsideClause),
        "{error:?}",
    );
}

#[test]
fn evidence_diagnostics_label_the_new_and_related_declarations() {
    let first = "with Read<Token, Int> {\nread ignored = 42\nsecond ignored = 42\n}\n";
    let cases = [
        (
            "with Read<Int, Int> {\n}\n".to_owned(),
            "evidence.missing-local-key",
            "Read<Int, Int>",
            None,
        ),
        (
            format!("{first}with Read<Token, Int> {{\n}}\n"),
            "evidence.duplicate",
            "Read<Token, Int>",
            Some("Read<Token, Int>"),
        ),
        (
            format!("{first}with Read<Token, Bool> {{\n}}\n"),
            "evidence.determination-conflict",
            "Read<Token, Bool>",
            Some("Read<Token, Int>"),
        ),
        (
            "with Read<Token, Int> {\n}\n".to_owned(),
            "evidence.missing-method",
            "Read<Token, Int>",
            Some("read :"),
        ),
        (
            "with Read<Token, Int> {\nunknown ignored = 42\n}\n".to_owned(),
            "evidence.extra-method",
            "unknown",
            Some("interface Read"),
        ),
        (
            "with Read<Token, Int> {\nread ignored = 42\nsecond ignored = 42\nread again = 42\n}\n"
                .to_owned(),
            "evidence.duplicate-method",
            "read again",
            Some("read ignored"),
        ),
    ];
    for (body, reason, primary, related) in cases {
        let text = format!(
            "interface Read<A, B> where A -> B {{\nread : A -> B\nsecond : A -> B\n}}\nmain : Unit -> Int\nmain () = {{\nnewtype Token = Token(Int)\n{body}42\n}}\n"
        );
        let fixture = Fixture::new(&text);
        let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
            .expect("diagnostic fixture should load");
        let resolved =
            resolve_module(&graph.modules()[0], &[]).expect("diagnostic fixture should resolve");
        let TypeError::Interface(diagnostic) =
            check_module(resolved).expect_err("diagnostic fixture should fail evidence admission")
        else {
            panic!("{reason} must retain interface diagnostic ownership");
        };
        assert_eq!(diagnostic.reason.to_string(), reason);
        assert_eq!(
            diagnostic.primary.span().range().start() as usize,
            text.rfind(primary).expect("primary marker should exist"),
            "{reason} primary label",
        );
        assert_eq!(diagnostic.related.len(), usize::from(related.is_some()));
        if let Some(related) = related {
            assert_eq!(
                diagnostic.related[0].span().range().start() as usize,
                text.find(related).expect("related marker should exist"),
                "{reason} related label",
            );
        }
    }
}

#[test]
fn supplied_equation_groups_follow_interface_slots_not_source_order() {
    assert_execution(
        r#"interface Both<A> {
    first : A -> Int
    second : A -> Int
}
main : Unit -> Int
main () = {
    newtype Token = Token(Bool)
    with Both<Token> {
        second (Token(true)) = 1
        second (Token(false)) = 22
        first (Token(true)) = 20
        first (Token(false)) = 2
    }
    first(Token(true)) + second(Token(false))
}
"#,
    );
}

#[test]
fn unused_supplied_method_still_checks_its_declared_result_type() {
    let fixture = Fixture::new(
        r#"interface Read<A> {
    read : A -> Int
}
main : Unit -> Int
main () = {
    newtype Token = Token(Int)
    with Read<Token> {
        read ignored = true
    }
    42
}
"#,
    );
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
        .expect("ill-typed supplied method should parse");
    let resolved =
        resolve_module(&graph.modules()[0], &[]).expect("ill-typed supplied method should resolve");
    let error = check_module(resolved).expect_err("unused supplied method must check");
    assert!(
        matches!(error, TypeError::Source(ref diagnostic)
            if diagnostic.reason == TypeReason::DefinitionResult),
        "{error:?}",
    );
}

#[test]
fn polymorphic_lexical_method_forwards_through_a_constrained_global() {
    assert_execution(
        r#"interface Choose<I> {
    choose<A> : (I, A) -> A
}
forward<I, A> : (I, A) -> A where Choose<I>
forward value = choose(value)
main : Unit -> Int
main () = {
    newtype Token = Token(Int)
    with Choose<Token> {
        choose (ignored, value) = value
    }
    forward(Token(0), 42)
}
"#,
    );
}

#[test]
fn lexical_application_retains_an_enclosing_rigid_parameter() {
    assert_execution(
        r#"type Box<A, B> = Box(A, B)
interface Read<I, O> where I -> O {
    read : I -> O
}
run<A> : A -> A
run value = {
    newtype Token = Token(Unit)
    with Read<Box<A, Token>, A> {
        read (Box(result, ignored)) = result
    }
    read(Box(value, Token(())))
}
main : Unit -> Int
main () = run(42)
"#,
    );
}

#[test]
fn lexical_application_retains_an_enclosing_implementation_parameter() {
    assert_execution(
        r#"type Box<A> = Box(A)
interface Read<I, O> where I -> O {
    read : I -> O
}
interface Check<A> {
    check : A -> A
}
impl<A> Check<Box<A>> {
    check (Box(value)) = {
        newtype N = N(Unit)
        with Read<N, A> {
            read ignored = value
        }
        Box(read(N(())))
    }
}
main : Unit -> Int
main () = match check(Box(42)) {
    Box(value) => value
}
"#,
    );
}

#[test]
fn unused_lexical_header_retains_an_enclosing_implementation_dependent() {
    assert_execution(
        r#"type Box<A> = Box(A)
interface Inspect<I, O> where I -> O {
    inspect : I -> Int
}
interface Check<A> {
    check : A -> A
}
impl<A> Check<Box<A>> {
    check (Box(value)) = {
        newtype N = N(Unit)
        with Inspect<N, A> {
            inspect ignored = 0
        }
        Box(value)
    }
}
main : Unit -> Int
main () = match check(Box(42)) {
    Box(value) => value
}
"#,
    );
}

#[test]
fn exported_generic_factory_keeps_nested_lexical_nominals_through_public_routes() {
    for entry in [
        "import factory (make)\nmain : Unit -> Int\nmain () = make(42)()\n",
        "import facade (build)\nmain : Unit -> Int\nmain () = build(42)()\n",
        "import left as Left\nimport right as Right\nmain : Unit -> Int\nmain () = Left.build(20)() + Right.build(22)()\n",
    ] {
        let fixture = Fixture::new(entry);
        let directory = fixture.0.parent().unwrap();
        fs::write(
            directory.join("factory.ash"),
            r#"effect Hidden {
    ask : Unit -> Int
}
pub make<A> : A -> (Unit -> A)
make value = {
    let unused : Unit -> Int !{Hidden} = fn(ignored) {
        42
    }
    newtype Outer = Outer(A)
    newtype Inner = Inner(Outer)
    let saved = Inner(Outer(value))
    fn(ignored) {
        match saved {
            Inner(Outer(result)) => result
        }
    }
}
"#,
        )
        .unwrap();
        fs::write(
            directory.join("facade.ash"),
            "pub import factory (make as build)\n",
        )
        .unwrap();
        fs::write(directory.join("left.ash"), "pub import facade (build)\n").unwrap();
        fs::write(directory.join("right.ash"), "pub import facade (build)\n").unwrap();
        let observation = ash::driver::run_path(ash::driver::RunConfiguration {
            entry: fixture.0.clone(),
            roots: ModuleRoots::empty(),
        })
        .expect("the factory's internal lexical types must stay in its capture graph");
        assert_eq!(observation.value_display(), "42");
    }
}

#[test]
fn imported_implementation_factory_keeps_its_lexical_capture_types() {
    let fixture = Fixture::new(
        "import factory (Factory, create, impl Factory)\nmain : Unit -> Int\nmain () = create()()\n",
    );
    fs::write(
        fixture.0.parent().unwrap().join("factory.ash"),
        r#"effect Hidden {
    ask : Unit -> Int
}
pub interface Factory<A> {
    create : A -> (Unit -> Int)
}
pub impl Factory<Unit> {
    create () = {
        let unused : Unit -> Int !{Hidden} = fn(ignored) {
            42
        }
        newtype Token = Token(Int)
        let saved = Token(42)
        fn(ignored) {
            match saved {
                Token(value) => value
            }
        }
    }
}
"#,
    )
    .unwrap();
    let observation = ash::driver::run_path(ash::driver::RunConfiguration {
        entry: fixture.0.clone(),
        roots: ModuleRoots::empty(),
    })
    .expect("implementation capture metadata must preserve internal lexical types");
    assert_eq!(observation.value_display(), "42");
}

#[test]
fn lexical_factory_wrapper_does_not_hide_a_resource_dependency() {
    let fixture = Fixture::new("import factory (make)\nmain : Unit -> Int\nmain () = make()()\n");
    fs::write(
        fixture.0.parent().unwrap().join("factory.ash"),
        r#"import @builtin.cell as Cell
pub make : Unit -> (Unit -> Int)
make () = resource cell<R> c = 42 {
    newtype Saved = Saved(Unit -> Int)
    let get : Unit -> Int = fn(ignored) {
        handle (Cell.read c) with Cell.Ops<R> {
            read value => resume 42
            write value => resume ()
        }
    }
    let saved = Saved(get)
    let later : Unit -> Int = fn(ignored) {
        match saved {
            Saved(get) => get()
        }
    }
    later
}
"#,
    )
    .unwrap();
    let failure = ash::driver::run_path(ash::driver::RunConfiguration {
        entry: fixture.0.clone(),
        roots: ModuleRoots::empty(),
    })
    .expect_err("internal lexical types must not erase retained resource ownership");
    assert_eq!(failure.reason_code(), "type.resource-escape");
}

#[test]
fn exported_factory_transfers_a_closure_without_interface_evidence() {
    let fixture = Fixture::new("import factory (make)\nmain : Unit -> Int\nmain () = make()()\n");
    fs::write(
        fixture
            .0
            .parent()
            .expect("fixture directory")
            .join("factory.ash"),
        r#"interface Read<A> {
    read : A -> Int
}
pub make : Unit -> (Unit -> Int)
make () = {
    newtype Token = Token(Int)
    let saved = Token(41)
    with Read<Token> {
        read (Token(value)) = value + 1
    }
    fn(ignored) {
        read(saved)
    }
}
"#,
    )
    .expect("factory module should be writable");
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
        .expect("factory and importer should load");
    let library = graph
        .modules()
        .iter()
        .find(|module| module.id() != graph.entry())
        .expect("factory should be a dependency");
    let library = check_module(resolve_module(library, &[]).expect("factory should resolve"))
        .expect("factory should check");
    let interface = library.interfaces()[0].id;
    assert!(library.implementations().is_empty());
    assert!(library.available_implementations().is_empty());
    let entry = graph
        .modules()
        .iter()
        .find(|module| module.id() == graph.entry())
        .expect("importer should be the entry");
    let dependency = DependencyExports::new(&entry.dependencies()[0], library.exports())
        .expect("ordinary factory export should authenticate");
    let entry = resolve_module(entry, &[dependency]).expect("importer should resolve");
    assert!(entry.imported_facts().interface(interface).is_none());
    let entry = check_module(entry).expect("importer should check without interface evidence");
    assert!(entry.available_implementations().is_empty());
    let observation = ash::driver::run_path(ash::driver::RunConfiguration {
        entry: fixture.0.clone(),
        roots: ModuleRoots::empty(),
    })
    .expect("exported closure should retain ordinary selected method captures");
    assert_eq!(observation.value_display(), "42");
}

#[test]
fn polymorphic_supplied_method_can_use_preceding_lexical_evidence() {
    assert_execution(
        r#"interface Choose<I> {
    choose<A> : (I, A) -> A
}
main : Unit -> Int
main () = {
    newtype First = First(Unit)
    let first = First(())
    with Choose<First> {
        choose (ignored, value) = value
    }
    newtype Second = Second(Unit)
    with Choose<Second> {
        choose (ignored, value) = choose(first, value)
    }
    choose(Second(()), 42)
}
"#,
    );
}

#[test]
fn nested_supplied_methods_have_independent_rigid_parameters() {
    assert_reason(
        r#"interface Choose<I> {
    choose<A> : (I, A) -> A
}
main : Unit -> Int
main () = {
    newtype Outer = Outer(Unit)
    with Choose<Outer> {
        choose (ignored, outer_value) = {
            newtype Inner = Inner(Unit)
            with Choose<Inner> {
                choose (ignored, inner_value) = outer_value
            }
            outer_value
        }
    }
    choose(Outer(()), 42)
}
"#,
        "type.definition-result",
    );
}

#[test]
fn polymorphic_method_effect_instances_coalesce_after_substitution() {
    assert_effect_execution(
        r#"effect Ping<A> {
    ping : A -> Unit
}
interface Read<I> {
    read<A> : (I, A) -> Int ! {Ping<A>, Ping<Int>}
}
main : Unit -> Int
main () = {
    newtype Token = Token(Unit)
    with Read<Token> {
        read (ignored, value) = {
            let sent = perform Ping<Int>.ping 0
            42
        }
    }
    handle (read(Token(()), 0)) with Ping<Int> {
        ping ignored => resume ()
    }
}
"#,
    );
}

#[test]
fn nested_polymorphic_supplied_method_preserves_its_own_parameter() {
    assert_execution(
        r#"interface Choose<I> {
    choose<A> : (I, A) -> A
}
main : Unit -> Int
main () = {
    newtype Outer = Outer(Unit)
    with Choose<Outer> {
        choose (ignored, outer_value) = {
            newtype Inner = Inner(Unit)
            with Choose<Inner> {
                choose (ignored, inner_value) = inner_value
            }
            choose(Inner(()), outer_value)
        }
    }
    choose(Outer(()), 42)
}
"#,
    );
}

#[test]
fn nested_polymorphic_groups_preserve_source_order_and_declared_method_slots() {
    assert_execution(
        r#"interface Choose<I> {
    left<A> : (I, A) -> A
    right<B> : (I, B) -> B
}

main : Unit -> Int
main () = {
    newtype Outer = Outer(Unit)
    with Choose<Outer> {
        right (_, value) = {
            newtype Inner = Inner(Unit)
            with Choose<Inner> {
                left (_, inner_value) = inner_value
                right (_, inner_value) = inner_value
            }
            left(Inner(), value)
        }
        left (_, value) = value
    }
    right(Outer(), 21) + left(Outer(), 21)
}
"#,
    );
}

#[test]
fn supplied_method_error_inside_handler_keeps_its_source_diagnostic() {
    assert_reason(
        r#"interface Read<A> {
    read : A -> Int
}
effect Ping {
    ping : Unit -> Unit
}
main : Unit -> Int
main () = {
    let done = handle (perform Ping.ping ()) with Ping {
        ping ignored => {
            newtype Token = Token(Unit)
            with Read<Token> {
                read ignored = true
            }
            resume ()
        }
    }
    42
}
"#,
        "type.definition-result",
    );
}
