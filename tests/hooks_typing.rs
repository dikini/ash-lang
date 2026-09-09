use ash::{
    driver::{RunConfiguration, run_path},
    module::ModuleRoots,
    source::SourceFile,
};

fn check(source: &str) -> Result<String, String> {
    check_result(source)
        .map(|value| value.value_display())
        .map_err(|error| error.reason_code())
}

fn check_result(source: &str) -> Result<ash::driver::Observation, ash::driver::FileFailure> {
    let path = std::env::temp_dir().join(format!(
        "ash-hooks-typing-{}-{}.ash",
        std::process::id(),
        SourceFile::new("hook", "").unwrap().id().value()
    ));
    std::fs::write(&path, source).unwrap();
    let result = run_path(RunConfiguration {
        entry: path.clone(),
        roots: ModuleRoots::empty(),
    });
    let _ = std::fs::remove_file(path);
    result
}

#[test]
fn registration_tuple_and_projected_callback_dependency_cannot_escape() {
    for (result_type, result) in [
        ("(Int, Unit -> Int)", "result"),
        ("(Unit -> Int)", "let (number, saved) = result\nsaved"),
    ] {
        assert_eq!(
            check(&format!(
                "import @builtin.cell as Cell\neffect Adjust {{\npublish : (Int, Unit -> Int) -> (Int, Unit -> Int)\n}}\nconstant : Unit -> Int\nconstant ignored = 1\nmain : Unit -> {result_type}\nmain () = resource cell<R> c = 42 {{\nlet callback : (Int, Unit -> Int) -> (Int, Unit -> Int) = fn(previous) {{\nlet (number, old) = previous\nlet saved : Unit -> Int = fn(ignored) {{\nlet held = c\n42\n}}\n(number + 1, saved)\n}}\nlet result = hook Adjust {{\nregister Adjust callback {{\nperform Adjust.publish (1, constant)\n}}\n}}\n{result}\n}}\n"
            )),
            Err("type.resource-escape".into()),
            "{result_type}",
        );
    }
}

#[test]
fn registration_original_tuple_dependency_cannot_be_lent_before_callback_erases_it() {
    assert_eq!(
        check(
            "import @builtin.cell as Cell\neffect Adjust {\npublish : (Int, Unit -> Int) -> (Int, Unit -> Int)\n}\nconstant : Unit -> Int\nconstant ignored = 1\nerase : (Int, Unit -> Int) -> (Int, Unit -> Int)\nerase previous = (0, constant)\nmain : Unit -> Int\nmain () = hook Adjust {\nresource cell<R> c = 42 {\nlet saved : Unit -> Int = fn(ignored) {\nlet held = c\n42\n}\nlet result = register Adjust erase {\nperform Adjust.publish (1, saved)\n}\nlet (number, restored) = result\nnumber + restored ()\n}\n}\n"
        ),
        Err("type.resource-escape".into())
    );
}

#[test]
fn coincident_registration_callback_cannot_export_its_cell_dependency() {
    assert_eq!(
        check(
            "import @builtin.cell as Cell\neffect Mark<T> {\npublish : (Unit -> Int) -> (Unit -> Int)\n}\nconstant : Unit -> Int\nconstant ignored = 1\nprobe<T, U> : (T, U, ((Unit -> Int) -> (Unit -> Int))) -> (Unit -> Int) ! {Mark<T>, Mark<U>}\nprobe (first, second, callback) = register Mark<U> callback {\nperform Mark<T>.publish constant\n}\nmain : Unit -> (Unit -> Int)\nmain () = resource cell<R> c = 42 {\nlet callback : (Unit -> Int) -> (Unit -> Int) = fn(previous) {\nfn(ignored) {\nlet held = c\n42\n}\n}\nhook Mark<Unit> {\nhook Mark<Bool> {\nprobe ((), (), callback)\n}\n}\n}\n"
        ),
        Err("type.resource-escape".into())
    );
}

#[test]
fn owned_registration_closes_with_or_without_coincidence() {
    for (argument, expected) in [("()", "4"), ("true", "3")] {
        assert_eq!(
            check(&format!(
                "effect Mark<T> {{\npublish : Int -> Int\n}}\neffect Pause {{\nask : Int -> Int\n}}\nincrement : Int -> Int\nincrement value = value + 1\nprobe<T, U> : (T, U) -> Int ! {{Mark<T>, Mark<U>, Pause}}\nprobe ignored = register Mark<U> increment {{\nlet value = perform Mark<T>.publish 3\nperform Pause.ask value\n}}\nmain : Unit -> Int\nmain () = handle (hook Mark<Unit> {{\nhook Mark<Bool> {{\nprobe ((), {argument})\n}}\n}}) with Pause {{\nask value => {{\nlet done = discard\nvalue\n}}\n}}\n"
            )),
            Ok(expected.into()),
            "argument: {argument}",
        );
    }
}

#[test]
fn hook_argument_kinds_keep_original_nested_source_spans() {
    for (parameter, argument, reason, occurrence) in [
        ("F : Type -> Type", "Int", "kind.argument", "Int"),
        ("T", "Atom<Bool>", "kind.not-applicable", "Atom<Bool>"),
    ] {
        let source = format!(
            "type Atom = Atom\neffect Bad<{parameter}> {{\nask : Int -> Int\n}}\nmain : Unit -> Int\nmain () = hook Bad<{argument}> {{\n42\n}}\n"
        );
        let error = check_result(&source).unwrap_err();
        assert_eq!(error.reason_code(), reason, "{error:?}");
        let ash::driver::PipelineFailure::Kind(ash::kind::KindFailure::Source(error)) =
            error.pipeline_failure().expect("pipeline failure")
        else {
            panic!("source kind failure: {error:?}")
        };
        let span = error.diagnostic().primary.span();
        let start = source.find("hook Bad<").unwrap() + "hook Bad<".len();
        assert_eq!(span.range().start() as usize, start);
        assert_eq!(span.range().end() as usize, start + occurrence.len());
    }
}

#[test]
fn hook_api_equality_is_declared_before_instantiation() {
    for (declaration, target) in [
        ("effect Bad {\nask : Int -> Int\n}\n", "Bad"),
        (
            "effect Bad {\npublish : Int -> Int\nask : Int -> Int\n}\n",
            "Bad",
        ),
        (
            "effect Convert<A, B> {\npublish : A -> B\n}\n",
            "Convert<Int, Int>",
        ),
    ] {
        assert_eq!(
            check(&format!(
                "{declaration}main : Unit -> Int\nmain () = hook {target} {{\n42\n}}\n"
            )),
            Err("type.hook-api".into())
        );
    }
}

#[test]
fn unused_root_body_result_is_independent_of_payload() {
    assert_eq!(
        check(
            "effect Adjust {\npublish : Int -> Int\n}\nmain : Unit -> Bool\nmain () = hook Adjust {\ntrue\n}\n"
        ),
        Ok("true".into())
    );
}

#[test]
fn registration_callback_and_body_errors_precede_publication_gate() {
    for (callback, body) in [("42", "true"), ("identity", "1 + true")] {
        let error = check(&format!(
            "effect Adjust {{\npublish : Int -> Int\n}}\nidentity : Int -> Int\nidentity value = value\nmain : Unit -> Bool\nmain () = hook Adjust {{\nregister Adjust {callback} {{\n{body}\n}}\n}}\n"
        )).unwrap_err();
        assert!(error.starts_with("type."), "{error}");
        assert_ne!(error, "type.hook-api");
    }
}

#[test]
fn unused_owned_registration_closes_without_invoking_its_callback() {
    assert_eq!(
        check(
            "effect Adjust {\npublish : Int -> Int\n}\neffect Stop {\nstop : Unit -> Unit\n}\nidentity : Int -> Int\nidentity value = value\nmain : Unit -> Int\nmain () = hook Adjust {\nhandle (register Adjust identity {\nlet ignored = perform Stop.stop ()\n42\n}) with Stop {\nstop ignored => {\nlet done = discard\n7\n}\n}\n}\n"
        ),
        Ok("7".into())
    );
}

#[test]
fn registration_discard_cannot_skip_completion_outside_its_immediate_capture() {
    assert_eq!(
        check(
            "effect Adjust {\npublish : Int -> Int\n}\neffect A {\nask : Unit -> Unit\n}\neffect B {\nask : Unit -> Unit\n}\nidentity : Int -> Int\nidentity value = value\nmain : Unit -> Unit\nmain () = hook Adjust {\nhandle (register Adjust identity {\nperform A.ask ()\n}) with A {\nask ignored => {\nlet _ = handle {\nlet _ = perform B.ask ()\nresume ()\n} with B {\nask ignored => discard\n}\n()\n}\n}\n}\n"
        ),
        Err("effect.discard-unsafe".into())
    );
}

#[test]
fn registration_api_shape_is_checked_before_generated_clause_artifacts() {
    for (declaration, target) in [
        ("effect Bad {\nask : Int -> Int\n}", "Bad"),
        (
            "effect Bad {\npublish : Int -> Int\nask : Int -> Int\n}",
            "Bad",
        ),
        (
            "effect Convert<A, B> {\npublish : A -> B\n}",
            "Convert<Int, Int>",
        ),
    ] {
        assert_eq!(
            check(&format!(
                "{declaration}\nidentity : Int -> Int\nidentity value = value\nmain : Unit -> Int ! {{{target}}}\nmain () = register {target} identity {{\n42\n}}\n"
            )),
            Err("type.hook-api".into())
        );
    }
}

#[test]
fn registration_unknown_tail_precedes_api_shape() {
    assert_eq!(
        check(
            "effect Bad {\nask : Int -> Int\n}\nidentity : Int -> Int\nidentity value = value\nrelay<R : EffectRow> : (Unit -> Int ! {| R}) -> Int ! {| R}\nrelay action = register Bad identity {\naction ()\n}\nmain : Unit -> Int\nmain () = 42\n"
        ),
        Err("effect.row-union-ambiguous".into())
    );
}

#[test]
fn registration_unused_callback_keeps_forwarded_and_latent_requirements() {
    for (signature, body) in [
        ("Int", "register Adjust identity {\n42\n}"),
        ("Int", "hook Adjust {\nregister Adjust callback {\n42\n}\n}"),
        (
            "Int",
            "hook Adjust {\nregister Adjust callback {\nhandle (perform Log.log 42) with Log {\nlog value => resume value\n}\n}\n}",
        ),
    ] {
        let reason = check(&format!("effect Adjust {{\npublish : Int -> Int\n}}\neffect Log {{\nlog : Int -> Int\n}}\nidentity : Int -> Int\nidentity value = value\ncallback : Int -> Int ! {{Log}}\ncallback value = perform Log.log value\nmain : Unit -> {signature}\nmain () = {body}\n")).unwrap_err();
        assert!(
            reason.starts_with("effect.") || reason.starts_with("type."),
            "{reason}"
        );
    }
}

#[test]
fn registration_initializer_effect_remains_outward() {
    let error = check(
        "effect Adjust {\npublish : Int -> Int\n}\neffect Before {\nbefore : Unit -> Unit\n}\nidentity : Int -> Int\nidentity value = value\nmake : Unit -> (Int -> Int) ! {Before}\nmake ignored = {\nlet done = perform Before.before ()\nidentity\n}\nmain : Unit -> Int\nmain () = hook Adjust {\nregister Adjust (make ()) {\n42\n}\n}\n"
    ).unwrap_err();
    assert!(
        error.starts_with("effect.") || error.starts_with("type."),
        "{error}"
    );
}

#[test]
fn registration_transformed_function_dependencies_cannot_escape() {
    assert_eq!(
        check(
            "import @builtin.cell as Cell\neffect Adjust {\npublish : (Unit -> Int) -> (Unit -> Int)\n}\nconstant : Unit -> Int\nconstant ignored = 1\nmain : Unit -> (Unit -> Int)\nmain () = resource cell<R> c = 42 {\nhook Adjust {\nlet callback : (Unit -> Int) -> (Unit -> Int) = fn(previous) {\nfn(ignored) {\nlet held = c\n42\n}\n}\nregister Adjust callback {\nperform Adjust.publish constant\n}\n}\n}\n"
        ),
        Err("type.resource-escape".into())
    );
}

#[test]
fn registration_forwarded_input_cannot_be_lent_before_callback_erases_it() {
    assert_eq!(
        check(
            "import @builtin.cell as Cell\neffect Adjust {\npublish : (Unit -> Int) -> (Unit -> Int)\n}\nconstant : Unit -> Int\nconstant ignored = 1\nerase : (Unit -> Int) -> (Unit -> Int)\nerase previous = constant\nmain : Unit -> Int\nmain () = hook Adjust {\nresource cell<R> c = 42 {\nlet payload : Unit -> Int = fn(ignored) {\nlet held = c\n42\n}\nlet result = register Adjust erase {\nperform Adjust.publish payload\n}\nresult ()\n}\n}\n"
        ),
        Err("type.resource-escape".into())
    );
}

#[test]
fn unused_ordinary_handler_still_requires_present_target() {
    assert_eq!(
        check(
            "effect Adjust {\npublish : Int -> Int\n}\nmain : Unit -> Int\nmain () = handle 42 with Adjust {\npublish input => resume input\n}\n"
        ),
        Err("effect.handler-missing-input".into())
    );
}

#[test]
fn root_preserves_enclosing_resume_scope() {
    assert_eq!(
        check(
            "effect Adjust {\npublish : Int -> Int\n}\neffect Ask {\nask : Unit -> Int\n}\nmain : Unit -> Int\nmain () = handle (perform Ask.ask ()) with Ask {\nask ignored => hook Adjust {\nresume 42\n}\n}\n"
        ),
        Ok("42".into())
    );
}

#[test]
fn absent_open_tail_requires_an_existing_lacks_fact() {
    for (row, expected) in [
        ("Adjust | R", Ok("42".into())),
        ("| R", Err("effect.row-union-ambiguous".into())),
    ] {
        let source = format!(
            "effect Adjust {{\npublish : Int -> Int\n}}\nrelay<R : EffectRow> : (Unit -> Int ! {{| R}}) -> Int ! {{{row}}}\nrelay action = hook Adjust {{\naction ()\n}}\nconstant : Unit -> Int\nconstant () = 42\nmain : Unit -> Int\nmain () = hook Adjust {{\nrelay constant\n}}\n"
        );
        assert_eq!(check(&source), expected, "{source}");
    }
}

#[test]
fn generic_root_selects_only_after_equal_instantiation() {
    for (second, expected) in [("()", "3"), ("true", "13")] {
        assert_eq!(
            check(&format!(
                "effect Mark<T> {{\npublish : Int -> Int\n}}\nprobe<T, U> : (T, U) -> Int ! {{Mark<T>}}\nprobe (first, second) = hook Mark<U> {{\nperform Mark<T>.publish 3\n}}\nmain : Unit -> Int\nmain () = handle (probe ((), {second})) with Mark<Unit> {{\npublish input => resume (input + 10)\n}}\n"
            )),
            Ok(expected.into())
        );
    }
}

#[test]
fn ordinary_kind_type_and_resume_errors_precede_api_shape() {
    let bad_kind = check(
        "effect Bad {\nask : Int -> Int\n}\nmain : Unit -> Int\nmain () = hook Bad<Int> {\n42\n}\n",
    )
    .unwrap_err();
    assert_eq!(bad_kind, "effect.handler-coverage");
    let bad_type = check("effect Bad {\nask : Int -> Int\n}\nmain : Unit -> Int\nmain () = hook Bad {\n1 + true\n}\n").unwrap_err();
    assert_ne!(bad_type, "type.hook-api");
    assert!(bad_type.starts_with("type."), "{bad_type}");
    assert_eq!(
        check(
            "effect Bad {\nask : Int -> Int\n}\nmain : Unit -> Int\nmain () = hook Bad {\nresume 42\n}\n"
        ),
        Err("effect.resume-outside-clause".into())
    );
}

#[test]
fn unresolved_root_tail_precedes_hook_api_shape() {
    assert_eq!(
        check(
            "effect Bad {\nask : Int -> Int\n}\nrelay<R : EffectRow> : (Unit -> Int ! {| R}) -> Int ! {| R}\nrelay action = hook Bad {\naction ()\n}\nmain : Unit -> Int\nmain () = 42\n"
        ),
        Err("effect.row-union-ambiguous".into())
    );
}

#[test]
fn identity_root_does_not_authorize_temporary_outward_resource_lending() {
    assert_eq!(
        check(
            "import @builtin.cell as Cell\neffect Adjust {\npublish : (Unit -> Int) -> (Unit -> Int)\n}\nmain : Unit -> Int\nmain () = hook Adjust {\nresource cell<R> c = 42 {\nlet get : Unit -> Int = fn(ignored) {\nhandle (Cell.read c) with Cell.Ops<R> {\nread value => resume 42\nwrite value => resume ()\n}\n}\nlet restored = perform Adjust.publish get\nrestored ()\n}\n}\n"
        ),
        Err("type.resource-escape".into())
    );
}

#[test]
fn generic_coincidence_keeps_resource_payload_dependencies() {
    for (second, expected) in [("()", "42"), ("true", "13")] {
        let source = format!(
            "import @builtin.cell as Cell\neffect Mark<T> {{\npublish : (Unit -> Int) -> (Unit -> Int)\n}}\nprobe<T, U> : (T, U, (Unit -> Int)) -> (Unit -> Int) ! {{Mark<T>}}\nprobe (first, second, payload) = hook Mark<U> {{\nperform Mark<T>.publish payload\n}}\nmain : Unit -> Int\nmain () = resource cell<R> c = 42 {{\nlet get : Unit -> Int = fn(ignored) {{\nhandle (Cell.read c) with Cell.Ops<R> {{\nread value => resume 42\nwrite value => resume ()\n}}\n}}\nlet restored = handle (probe ((), {second}, get)) with Mark<Unit> {{\npublish input => resume (fn(ignored) {{\n13\n}})\n}}\nrestored ()\n}}\n"
        );
        assert_eq!(check(&source), Ok(expected.into()));
        if second == "()" {
            let escaping = source
                .replace("main : Unit -> Int", "main : Unit -> (Unit -> Int)")
                .replace("restored ()\n", "restored\n");
            assert_eq!(check(&escaping), Err("type.resource-escape".into()));
        }
    }
}

#[test]
fn generic_coincidence_closes_owned_pending_resume_completion() {
    for (second, expected) in [("()", Ok("()".into())), ("true", Ok("()".into()))] {
        let source = format!(
            "effect Mark<T> {{\npublish : Unit -> Unit\n}}\neffect Begin {{\nstart : Unit -> Unit\n}}\nprobe<T, U> : (T, U) -> Unit ! {{Mark<T>}}\nprobe (first, second) = hook Mark<U> {{\nperform Mark<T>.publish ()\n}}\nmain : Unit -> Unit\nmain () = handle (handle (perform Begin.start ()) with Begin {{\nstart ignored => {{\nlet _ = probe ((), {second})\nresume ()\n}}\n}}) with Mark<Unit> {{\npublish ignored => discard\n}}\n"
        );
        assert_eq!(check(&source), expected);
    }
}
