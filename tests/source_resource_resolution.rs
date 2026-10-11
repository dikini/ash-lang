use ash::{
    driver::{FileFailure, PipelineFailure, RunConfiguration, compile_path},
    elaborate::{TypeError, TypeReason},
    module::{ModuleRoots, load_module_graph},
    resolve::{ResolveModuleError, ResolveReason, resolve_module},
    resolved::{ResolvedDefinitionKind, ResolvedExprKind, ResolvedPatternKind},
    types::{Kind, KindedArgument},
};
use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

static IDS: AtomicU64 = AtomicU64::new(0);
struct Source(PathBuf);
impl Source {
    fn new(text: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "ash-source-resource-resolve-{}-{}.ash",
            std::process::id(),
            IDS.fetch_add(1, Ordering::Relaxed)
        ));
        fs::write(&path, text).unwrap();
        Self(path)
    }
}
impl Drop for Source {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}

// Resolution evidence: ordinary State and ordinary native-looking effects carry
// no source owner or native execution permission.
const SOURCE: &str = r"type State<R> = Token(Unit)
type Acquire<S, D, I> = Acquired(S, D)
    | Refused(I)
type Finish<S, E> = Consumed
    | ConsumedFailure(E)
    | Retained(S, E)
type Completion<E> = Closed
    | ConsumedError(E)
    | RetainedError(E)
type Scope<I, E, T> = NotAcquired(I)
    | Completed(T, Completion<E>)
interface BufferProvider<Before : EffectRow, R, T, After : EffectRow> {
    value : Buffer<{| Before}, R, T, {| After}> -> Int
}
effect BufferOps<Before : EffectRow, R, T, After : EffectRow> {
    value : Buffer<{| Before}, R, T, {| After}> -> Int
}
effect Allocate<Before : EffectRow, R, After : EffectRow> {
    call : Unit -> State<R>
}
effect Free<Before : EffectRow, R, After : EffectRow> {
    call : State<R> -> Unit
}
pub resource Buffer<Before : EffectRow, R, T, After : EffectRow> {
    owned R
    input (Int, Bool)
    state State<R>
    data Int
    acquisition Acquire<State<R>, Int, Unit>
    completion Finish<State<R>, Unit>
    result Scope<Unit, Unit, Answer> for <Answer>
    codec scope
    provider BufferProvider<{| Before}, R, T, {| After}>
    effect BufferOps<{| Before}, R, T, {| After}>
    interpret Allocate<{| Before}, R, {| After}>, Free<{| Before}, R, {| After}>
    acquire (length, flags) => Acquired(Token (), length)
    finish (native, data) => Consumed
    handlers (native, data) {
        value () => resume data
    }
}
main : Unit -> Int
main () = resource Buffer<{}, Fresh, Bool, {}> buffer = (8, true) {
    42
}
";

fn resolve(text: &str) -> Result<ash::resolved::ResolvedModule, ResolveModuleError> {
    let source = Source::new(text);
    let graph = load_module_graph(&source.0, &ModuleRoots::empty()).unwrap();
    resolve_module(graph.modules().last().unwrap(), &[])
}

fn replace_changed(source: &str, original: &str, replacement: &str) -> String {
    let changed = source.replace(original, replacement);
    assert_ne!(changed, source, "mutation did not replace {original:?}");
    changed
}

#[test]
fn source_headers_keep_owned_position_complete_interpretations_and_patterns() {
    let module = resolve(SOURCE).unwrap();
    assert!(module.resources().is_empty());
    let definition = &module.source_resources()[0];
    assert_eq!(definition.owned_position, 1);
    assert_eq!(
        definition
            .parameters
            .iter()
            .map(|parameter| &parameter.kind)
            .collect::<Vec<_>>(),
        [&Kind::EffectRow, &Kind::Type, &Kind::Type, &Kind::EffectRow]
    );
    assert_eq!(definition.interpreted.len(), 2);
    for effect in &definition.interpreted {
        assert!(matches!(
            effect.instance.arguments()[0],
            KindedArgument::RowArg(_)
        ));
        assert!(matches!(
            effect.instance.arguments()[1],
            KindedArgument::TypeArg(_)
        ));
        assert!(matches!(
            effect.instance.arguments()[2],
            KindedArgument::RowArg(_)
        ));
    }
    for pattern in [
        &definition.acquire_pattern,
        &definition.finish_pattern,
        &definition.handlers_pattern,
    ] {
        assert!(matches!(pattern.kind, ResolvedPatternKind::Tuple(_)));
    }
    let ResolvedDefinitionKind::Equational(main) = &module.definitions()[0].kind else {
        panic!("equational main")
    };
    let ResolvedExprKind::ProviderResource(instance) = &main.equations[0].body.kind else {
        panic!("source resource instance")
    };
    assert_eq!(instance.definition, definition.id);
    assert_eq!(instance.identity.spelling, "Fresh");
    assert_ne!(instance.identity.id, definition.parameters[1].id);
    let arguments = instance.arguments.as_ref().unwrap();
    assert!(matches!(arguments[0].ty, KindedArgument::RowArg(_)));
    assert!(matches!(arguments[1].ty, KindedArgument::TypeArg(_)));
    assert!(matches!(arguments[2].ty, KindedArgument::RowArg(_)));
    assert!(std::sync::Arc::ptr_eq(
        module
            .registry()
            .source_resource_fact(definition.id)
            .unwrap(),
        &definition.header
    ));
}

#[test]
fn source_owned_selectors_and_complete_instances_reject_wrong_shapes() {
    for source in [
        replace_changed(SOURCE, "owned R", "owned Missing"),
        replace_changed(SOURCE, "owned R", "owned Before"),
        replace_changed(
            SOURCE,
            "Buffer<{}, Fresh, Bool, {}>",
            "Buffer<{}, Fresh, Bool>",
        ),
        replace_changed(
            SOURCE,
            "Buffer<{}, Fresh, Bool, {}>",
            "Buffer<{}, {}, Bool, {}>",
        ),
    ] {
        let ResolveModuleError::Resolution(error) = resolve(&source).unwrap_err() else {
            panic!("source shape must fail in name resolution")
        };
        assert_eq!(error.reason, ResolveReason::TypeKind);
    }
}

#[test]
fn source_initializer_cannot_observe_the_fresh_owned_identity() {
    let source = replace_changed(
        SOURCE,
        "= (8, true) {",
        "= (perform Allocate<{}, Fresh, {}>.call ()) {",
    );
    let ResolveModuleError::Resolution(error) = resolve(&source).unwrap_err() else {
        panic!("initializer must fail in preceding scope")
    };
    assert_eq!(error.reason, ResolveReason::UnknownType);
}

// The public compilation fixture keeps its provider interface public. A private
// interface declared beside a public source resource currently cannot enter the
// shared export closure: that closure retains imported shared interfaces only.
// These cases exercise source resource admission without changing visibility.
const OWNER: &str = include_str!("fixtures/source-owner/owner.ash");
const PURE_ENTRY: &str = "import owner as Owner\nmain : Unit -> Owner.Scope<Unit, Unit, Int>\nmain () = resource Owner.Probe<{}, Fresh, {}> owner = 8 {\n    42\n}\n";

struct CompilationFixture(PathBuf);
impl CompilationFixture {
    fn new(owner: &str, entry: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "ash-source-resource-check-{}-{}",
            std::process::id(),
            IDS.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        fs::write(path.join("owner.ash"), owner).unwrap();
        fs::write(path.join("entry.ash"), entry).unwrap();
        Self(path)
    }

    fn refusal(&self) -> FileFailure {
        match compile_path(RunConfiguration {
            entry: self.0.join("entry.ash"),
            roots: ModuleRoots::empty(),
        }) {
            Ok(_) => panic!("source resource authority violation was accepted"),
            Err(error) => error,
        }
    }
}
impl Drop for CompilationFixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn public_source_resource_compiles_row_free_arguments_with_nonfirst_owned_position() {
    let formals = "<Before : EffectRow, R, After : EffectRow>";
    let actuals = "<{| Before}, R, {| After}>";
    let entry_actuals = "Owner.Probe<{}, Fresh, {}>";
    assert_eq!(OWNER.matches(formals).count(), 3);
    assert_eq!(OWNER.matches(actuals).count(), 6);
    assert_eq!(PURE_ENTRY.matches(entry_actuals).count(), 1);
    let owner = replace_changed(OWNER, formals, "<Before, R, After>");
    let owner = replace_changed(&owner, actuals, "<Before, R, After>");
    let entry = replace_changed(PURE_ENTRY, entry_actuals, "Owner.Probe<Bool, Fresh, Int>");
    let fixture = CompilationFixture::new(&owner, &entry);
    compile_path(RunConfiguration {
        entry: fixture.0.join("entry.ash"),
        roots: ModuleRoots::empty(),
    })
    .expect(
        "the original owner contract compiles with a complete Type vector and owned position 1",
    );
}

#[test]
fn public_source_resource_facade_preserves_mixed_arguments_and_owned_position() {
    let entry = r"import facade as Facade
main : Unit -> Facade.Result<Unit, Unit, Int>
main () = resource Facade.Sensor<{}, Fresh, {}> sensor = 8 {
    perform Facade.Reads<Facade.Sensor<{}, Fresh, {}>>.read sensor
}
";
    let fixture = CompilationFixture::new(OWNER, entry);
    fs::write(
        fixture.0.join("facade.ash"),
        "pub import owner (Probe as Sensor, ProbeOps as Reads, Scope as Result)\n",
    )
    .unwrap();
    compile_path(RunConfiguration {
        entry: fixture.0.join("entry.ash"),
        roots: ModuleRoots::empty(),
    })
    .expect("renamed facade retains the original mixed resource header and checked code");
    fs::write(
        fixture.0.join("entry.ash"),
        "import facade (ProbeProvider)\nmain : Unit -> Int\nmain () = 42\n",
    )
    .unwrap();
    let failure = fixture.refusal();
    assert!(
        matches!(failure.pipeline_failure(), Some(PipelineFailure::Resolution(error))
        if error.diagnostic().reason == ResolveReason::UnavailableExport),
        "{failure:?}"
    );
}

#[test]
fn public_source_resource_rejects_owned_handle_escape() {
    let entry = "import owner as Owner\nmain : Unit -> Unit\nmain () = resource Owner.Probe<{}, Fresh, {}> owner = 8 {\n    owner\n}\n";
    let failure = CompilationFixture::new(OWNER, entry).refusal();
    assert!(
        matches!(
            failure.pipeline_failure(),
            Some(PipelineFailure::Typing(TypeError::Source(diagnostic)))
                if diagnostic.reason == TypeReason::ResourceEscape
        ),
        "{failure:?}"
    );
}

#[test]
fn public_source_resource_rejects_wrong_kind_and_actual_tags() {
    for (owner, entry) in [
        (
            replace_changed(
                OWNER,
                "    effect ProbeOps<Probe<{| Before}, R, {| After}>>\n",
                "    effect ProbeOps<{}>\n",
            ),
            PURE_ENTRY.to_owned(),
        ),
        (
            OWNER.to_owned(),
            replace_changed(
                PURE_ENTRY,
                "Owner.Probe<{}, Fresh, {}>",
                "Owner.Probe<{}, {}, {}>",
            ),
        ),
        (
            OWNER.to_owned(),
            replace_changed(
                PURE_ENTRY,
                "Owner.Probe<{}, Fresh, {}>",
                "Owner.Probe<Int, Fresh, {}>",
            ),
        ),
        (
            OWNER.to_owned(),
            replace_changed(
                PURE_ENTRY,
                "Owner.Probe<{}, Fresh, {}>",
                "Owner.Probe<{}, Fresh>",
            ),
        ),
    ] {
        let failure = CompilationFixture::new(&owner, &entry).refusal();
        assert!(
            matches!(
                failure.pipeline_failure(),
                Some(PipelineFailure::Resolution(_)) | Some(PipelineFailure::Kind(_))
            ),
            "{failure:?}"
        );
    }
}

#[test]
fn public_source_resource_authenticates_original_owner_and_interpretations() {
    let wrong_state = replace_changed(
        OWNER,
        "pub resource Probe<Before : EffectRow, R, After : EffectRow>",
        "pub type Other<R> = Other(Unit)\npub resource Probe<Before : EffectRow, R, After : EffectRow>",
    );
    let wrong_state = replace_changed(&wrong_state, "state State<R>", "state Other<R>");
    let wrong_state = replace_changed(
        &wrong_state,
        "acquisition Acquire<State<R>",
        "acquisition Acquire<Other<R>",
    );
    let wrong_state = replace_changed(
        &wrong_state,
        "completion Finish<State<R>",
        "completion Finish<Other<R>",
    );
    let wrong_actual = replace_changed(
        OWNER,
        "interpret Allocate<{| Before}, R, {| After}>, Free<{| Before}, R, {| After}>",
        "interpret Allocate<{| Before}, Int, {| After}>, Free<{| Before}, R, {| After}>",
    );
    let wrong_row = replace_changed(
        OWNER,
        "interpret Allocate<{| Before}, R, {| After}>, Free<{| Before}, R, {| After}>",
        "interpret Allocate<{}, R, {| After}>, Free<{| Before}, R, {| After}>",
    );
    let wrong_symbol = replace_changed(
        OWNER,
        "interpret Allocate<{| Before}, R, {| After}>, Free<{| Before}, R, {| After}>",
        "interpret Free<{| Before}, R, {| After}>, Free<{| Before}, R, {| After}>",
    );
    for owner in [wrong_state, wrong_actual, wrong_row, wrong_symbol] {
        assert_ne!(owner, OWNER);
        let failure = CompilationFixture::new(&owner, PURE_ENTRY).refusal();
        assert!(
            matches!(
                failure.pipeline_failure(),
                Some(PipelineFailure::Typing(TypeError::Source(diagnostic)))
                    if diagnostic.reason == TypeReason::Argument
            ),
            "{failure:?}"
        );
    }
}

#[test]
fn selective_source_owner_type_import_preserves_no_operation_availability() {
    let entry = "import owner (State)\nmain : Unit -> Int\nmain () = 42\n";
    let fixture = CompilationFixture::new(OWNER, entry);
    compile_path(RunConfiguration {
        entry: fixture.0.join("entry.ash"),
        roots: ModuleRoots::empty(),
    })
    .expect("selecting only the opaque owner type retains its category without native execution");

    fs::write(
        fixture.0.join("facade.ash"),
        "pub import owner (State as OpaqueState)\n",
    )
    .unwrap();
    fs::write(
        fixture.0.join("entry.ash"),
        "import facade (OpaqueState)\nmain : Unit -> Int\nmain () = 42\n",
    )
    .unwrap();
    compile_path(RunConfiguration {
        entry: fixture.0.join("entry.ash"),
        roots: ModuleRoots::empty(),
    })
    .expect("a selected opaque owner facade preserves original category authority");

    let entry = "import owner (State)\nmain : Unit -> Unit\nmain () = perform Allocate<{}, Int, {}>.call 8\n";
    let failure = CompilationFixture::new(OWNER, entry).refusal();
    assert!(
        matches!(failure.pipeline_failure(), Some(PipelineFailure::Resolution(error))
        if error.diagnostic().reason == ResolveReason::UnknownEffect),
        "{failure:?}"
    );
}

#[test]
fn public_source_owner_rejects_ordinary_lifecycle_requests_and_state_parameters() {
    for entry in [
        "import owner as Owner\nmain : Unit -> Unit\nmain () = perform Owner.Allocate<{}, Int, {}>.call 8\n",
        "import owner as Owner\nread : Owner.State<Int> -> Int\nread state = 0\nmain : Unit -> Int\nmain () = 42\n",
        "import owner (State)\nread : State<Int> -> Int\nread state = 0\nmain : Unit -> Int\nmain () = 42\n",
    ] {
        let failure = CompilationFixture::new(OWNER, entry).refusal();
        assert!(
            matches!(
                failure.pipeline_failure(),
                Some(PipelineFailure::Typing(TypeError::Source(diagnostic)))
                    if diagnostic.reason == TypeReason::Argument
            ),
            "{failure:?}"
        );
    }
}

#[test]
fn public_source_resource_finish_requires_the_recorded_native_outcome() {
    let (prefix, finish_and_handlers) = OWNER.split_once("    finish (state, data) =>").unwrap();
    let (_, handlers) = finish_and_handlers.split_once("    handlers").unwrap();
    for result in ["Retained(state, ())", "Consumed"] {
        let owner = format!("{prefix}    finish (state, data) => {result}\n    handlers{handlers}");
        assert_ne!(owner, OWNER);
        let failure = CompilationFixture::new(&owner, PURE_ENTRY).refusal();
        assert!(
            matches!(
                failure.pipeline_failure(),
                Some(PipelineFailure::Typing(TypeError::Source(diagnostic)))
                    if diagnostic.reason == TypeReason::Argument
            ),
            "{failure:?}"
        );
    }
}

#[test]
fn source_resource_answer_preserves_enclosing_owner_callable_dependency() {
    let entry = r"import owner as Owner
import @builtin.cell as Cell
main : Unit -> Owner.Scope<Unit, Unit, (Unit -> Int)>
main () = resource cell<Outer> outer = 1 {
    resource Owner.Probe<{}, Inner, {}> inner = 8 {
        let delayed : Unit -> Int = fn(ignored) {
            let held = outer
            42
        }
        delayed
    }
}
";
    let failure = CompilationFixture::new(OWNER, entry).refusal();
    assert!(
        matches!(failure.pipeline_failure(), Some(PipelineFailure::Typing(TypeError::Source(diagnostic))) if diagnostic.reason == TypeReason::ResourceEscape),
        "{failure:?}"
    );
}

#[test]
fn public_source_provider_association_requires_exact_names_types_and_effect_rows() {
    let owner = include_str!("fixtures/source-owner/forwarding_owner.ash");
    let variants = [
        owner.replace(
            "    offset : (Access, Int) -> Int ! {ProbeOps<Access>}\n",
            "",
        ),
        owner.replace(
            "offset : (Access, Int) -> Int !",
            "shift : (Access, Int) -> Int !",
        ),
        owner.replace(
            "offset : (Access, Int) -> Int !",
            "offset : (Access, Bool) -> Int !",
        ),
        owner.replace(
            "read : Access -> Int ! {ProbeOps<Access>}",
            "read : Access -> Int",
        ),
        owner
            .replace(
                "pub interface ProbeProvider",
                "pub effect Extra {\n    mark : Unit -> Unit\n}\npub interface ProbeProvider",
            )
            .replace(
                "read : Access -> Int ! {ProbeOps<Access>}",
                "read : Access -> Int ! {ProbeOps<Access>, Extra}",
            ),
    ];
    for owner in variants {
        let failure = CompilationFixture::new(&owner, PURE_ENTRY).refusal();
        assert!(
            matches!(failure.pipeline_failure(),
            Some(PipelineFailure::Typing(TypeError::Source(diagnostic)))
                if diagnostic.reason == TypeReason::Argument),
            "{failure:?}"
        );
    }
}

#[test]
fn public_source_provider_seal_survives_interface_only_imports_and_facades() {
    let owner = include_str!("fixtures/source-owner/forwarding_owner.ash");
    for route in [
        "import owner (ProbeProvider, ProbeOps)",
        "import facade (ProbeProvider, ProbeOps)",
    ] {
        for body in [
            "type Local = Local(Unit)\nimpl ProbeProvider<Local> {\n    read value = perform ProbeOps<Local>.read value\n    offset input = perform ProbeOps<Local>.offset input\n}\nmain : Unit -> Int\nmain () = 42\n",
            "type Local = Local(Unit)\nmain : Unit -> Int\nmain () = {\n    with ProbeProvider<Local> {\n        read value = perform ProbeOps<Local>.read value\n        offset input = perform ProbeOps<Local>.offset input\n    }\n    42\n}\n",
        ] {
            let entry = format!("{route}\n{body}");
            let fixture = CompilationFixture::new(owner, &entry);
            fs::write(
                fixture.0.join("facade.ash"),
                "pub import owner (ProbeProvider, ProbeOps)\n",
            )
            .unwrap();
            let failure = fixture.refusal();
            assert!(
                matches!(failure.pipeline_failure(), Some(PipelineFailure::Resolution(error))
                if error.diagnostic().reason == ResolveReason::SealedProvider),
                "{route}: {failure:?}"
            );
        }
    }
}

#[test]
fn public_source_provider_rejects_a_second_association_and_existing_imported_impl() {
    let owner = include_str!("fixtures/source-owner/forwarding_owner.ash");
    let (_, definition) = owner.split_once("pub resource Probe<").unwrap();
    let duplicate = format!(
        "{owner}\npub resource Other<{}",
        definition.replace(
            "Probe<{| Before}, R, {| After}>",
            "Other<{| Before}, R, {| After}>"
        )
    );
    let failure = CompilationFixture::new(&duplicate, PURE_ENTRY).refusal();
    assert!(
        matches!(failure.pipeline_failure(), Some(PipelineFailure::Resolution(error))
        if error.diagnostic().reason == ResolveReason::SealedProvider),
        "{failure:?}"
    );

    let (prefix, definition) = owner.split_once("pub interface ProbeProvider").unwrap();
    let (association, resource) = definition.split_once("pub resource Probe<").unwrap();
    for visibility in ["", "pub "] {
        let prior = format!(
            "pub interface ProbeProvider{association}\n{visibility}impl ProbeProvider<Int> {{\n    read value = perform ProbeOps<Int>.read value\n    offset input = perform ProbeOps<Int>.offset input\n}}\n"
        );
        let moved = format!(
            "import prior (ProbeProvider, ProbeOps, impl ProbeProvider)\n{prefix}pub resource Probe<{resource}"
        );
        let fixture = CompilationFixture::new(&moved, PURE_ENTRY);
        fs::write(fixture.0.join("prior.ash"), prior).unwrap();
        let failure = fixture.refusal();
        assert!(
            matches!(failure.pipeline_failure(), Some(PipelineFailure::Resolution(error))
            if error.diagnostic().reason == ResolveReason::SealedProvider),
            "{visibility:?}: {failure:?}"
        );
    }
}

#[test]
fn public_source_provider_passive_headers_add_no_resource_or_native_source_names() {
    let owner = include_str!("fixtures/source-owner/forwarding_owner.ash");
    for route in ["owner", "facade"] {
        let fixture = CompilationFixture::new(
            owner,
            &format!(
                "import {route} (ProbeProvider, ProbeOps)\nmain : Unit -> Int\nmain () = 42\n"
            ),
        );
        fs::write(
            fixture.0.join("facade.ash"),
            "pub import owner (ProbeProvider, ProbeOps)\n",
        )
        .unwrap();
        compile_path(RunConfiguration {
            entry: fixture.0.join("entry.ash"),
            roots: ModuleRoots::empty(),
        })
        .unwrap();
        fs::write(fixture.0.join("entry.ash"), format!("import {route} (ProbeProvider, ProbeOps)\nmain : Unit -> Int\nmain () = resource Probe<{{}}, Fresh, {{}}> owner = 42 {{\n    42\n}}\n")).unwrap();
        let failure = fixture.refusal();
        assert!(
            matches!(failure.pipeline_failure(), Some(PipelineFailure::Resolution(error)) if error.diagnostic().reason == ResolveReason::UnknownType),
            "{route}: {failure:?}"
        );
        fs::write(fixture.0.join("entry.ash"), format!("import {route} (ProbeProvider, ProbeOps)\nmain : Unit -> Unit\nmain () = perform Allocate<{{}}, Int, {{}}>.call 42\n")).unwrap();
        let failure = fixture.refusal();
        assert!(
            matches!(failure.pipeline_failure(), Some(PipelineFailure::Resolution(error)) if error.diagnostic().reason == ResolveReason::UnknownEffect),
            "{route}: {failure:?}"
        );
    }
}

#[test]
fn public_source_provider_imported_generic_helper_cannot_hide_access_capture() {
    let owner = include_str!("fixtures/source-owner/forwarding_owner.ash");
    let entry = r"import owner as Owner
import helper as Helper
main : Unit -> Owner.Scope<Unit, Unit, (Unit -> Int)>
main () = resource Owner.Probe<{}, Fresh, {}> owner = 42 {
    Helper.retain owner
}

";
    for import in [
        "import owner (ProbeProvider, ProbeOps)",
        "import facade (ProbeProvider, ProbeOps)",
    ] {
        let fixture = CompilationFixture::new(owner, entry);
        fs::write(
            fixture.0.join("facade.ash"),
            "pub import owner (ProbeProvider, ProbeOps)\n",
        )
        .unwrap();
        fs::write(fixture.0.join("helper.ash"), format!("{import}\npub retain<Access> : Access -> (Unit -> Int)\nretain access = fn(ignored) {{\n    let held = access\n    42\n}}\n")).unwrap();
        let failure = fixture.refusal();
        assert!(
            matches!(failure.pipeline_failure(), Some(PipelineFailure::Typing(TypeError::Source(diagnostic))) if diagnostic.reason == TypeReason::ResourceEscape),
            "{import}: {failure:?}"
        );
    }
}

#[test]
fn public_source_provider_passive_census_preserves_unassociated_interface_selection() {
    let prior = "pub interface Plain<A> {\n    value : A -> Int\n}\ntype SourceKey = SourceKey\nimpl Plain<SourceKey> {\n    value ignored = 1\n}\n";
    for route in ["owner", "facade"] {
        let entry = format!(
            "import {route} (Plain, value)\ntype Local = Local\nimpl Plain<Local> {{\n    value ignored = 42\n}}\nmain : Unit -> Int\nmain () = value Local\n"
        );
        let fixture = CompilationFixture::new(prior, &entry);
        fs::write(
            fixture.0.join("facade.ash"),
            "pub import owner (Plain, value)\n",
        )
        .unwrap();
        compile_path(RunConfiguration {
            entry: fixture.0.join("entry.ash"),
            roots: ModuleRoots::empty(),
        })
        .expect("a passive private-implementation census supplies no selection or seal");
    }
}
