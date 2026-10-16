//! Product resource admission and real native calls through the public build.

use ash::{
    build::{BuildConfiguration, NativeLinkInput, build_prepared, prepare_program},
    driver::{RunConfiguration, compile_path},
    module::ModuleRoots,
};
use std::{
    fs,
    path::PathBuf,
    process::{Command, Stdio},
    sync::atomic::{AtomicU64, Ordering},
    thread,
    time::{Duration, Instant},
};

struct Fixture(PathBuf);
impl Fixture {
    fn new(entry: &str) -> Self {
        static IDS: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "ash-source-owner-{}-{}",
            std::process::id(),
            IDS.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        fs::write(
            path.join("owner.ash"),
            include_str!("fixtures/source-owner/owner.ash"),
        )
        .unwrap();
        fs::write(path.join("entry.ash"), entry).unwrap();
        Self(path)
    }
    fn configuration(&self) -> RunConfiguration {
        RunConfiguration {
            entry: self.0.join("entry.ash"),
            roots: ModuleRoots::empty(),
        }
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn owner_with_scalar_teardown_result() -> String {
    include_str!("fixtures/source-owner/owner.ash")
        .replace("repr Size = size_t", "repr Size = size_t\n    repr Status = signed(32)")
        .replace("Foreign.Disposition<Unit>", "Foreign.Disposition<Int>")
        .replace("abi (pointer(Address)) -> void", "abi (pointer(Address)) -> Status")
        .replace(
            "outcome otherwise { consumed 0 }",
            "output result as scalar\n        outcome otherwise { readable result, consumed 0 }",
        )
        .replace("completion Finish<State<R>, Unit>", "completion Finish<State<R>, Int>")
        .replace("result Scope<Unit, Unit, Answer>", "result Scope<Unit, Int, Answer>")
        .replace(
            "Foreign.Returned(Foreign.Consumed(())) => Consumed",
            "Foreign.Returned(Foreign.Consumed(status)) => match status == 0 {\n            true => Consumed\n            false => ConsumedFailure(status)\n        }",
        )
        .replace(
            "Foreign.Returned(Foreign.Retained(())) => Retained(state, ())",
            "Foreign.Returned(Foreign.Retained(status)) => Retained(state, status)",
        )
        .replace("Retained(state, ())", "Retained(state, 1)")
}

#[test]
fn source_control_open_delta_executes_with_type_only_native_owner() {
    generated_owner_program_with_helpers(
        include_str!("fixtures/source-owner/owner.ash"),
        include_str!("fixtures/source-owner/control_open_delta_entry.ash"),
        Some(include_str!("fixtures/source-owner/control_callbacks.ash")),
        "(Completed(MissingRow, Closed), 42)",
        "acquire:42\nrelease:42\n",
    );
}

#[test]
fn source_control_equal_substitution_keeps_distinct_capture_demands() {
    generated_owner_program_with_helpers(
        include_str!("fixtures/source-owner/owner.ash"),
        include_str!("fixtures/source-owner/control_capture_entry.ash"),
        Some(include_str!("fixtures/source-owner/control_capture.ash")),
        "(Completed((MissingRow, MissingRow), Closed), 42)",
        "acquire:42\nacquire:8\nrelease:8\nrelease:42\n",
    );
}

#[test]
fn source_control_qualified_resource_identity_before_later_formal() {
    let entry = format!(
        "import owner as Donor\n{}\nmain : Unit -> Donor.Scope<Unit, Unit, Int>\nmain () = resource Donor.Probe<{{}}, ImportedFresh, {{}}> owner = 42 {{\n    42\n}}\ninterface KeepConfig<A> {{\n    keepConfig : A -> A\n}}\n",
        include_str!("fixtures/source-owner/owner.ash"),
    );
    let fixture = Fixture::new(&entry);
    compile_path(fixture.configuration()).expect(
        "an imported resource's fresh identity precedes a later declaration formal and reaches independent Core",
    );
}

#[test]
fn pr27_implicit_finish_tracks_replaced_private_payload_captures() {
    let owner = include_str!("fixtures/source-owner/replaced_payload_owner.ash");
    let entry = r#"import owner as Owner
initial : Unit -> Int
initial () = 7
main : Unit -> Owner.Scope<Unit, Unit -> Int, Unit>
main () = resource Owner.Probe<{}, Fresh, {}> owner = initial {
    let replacement : Unit -> Int = fn(ignored) {
        let retained = owner
        42
    }
    Owner.store (owner, replacement)
}
"#;
    let independent = entry.replace("let retained = owner", "let retained = 1");
    let handled = entry.replace(
        "let retained = owner\n        42",
        "handle (Owner.read owner) with Owner.ProbeOps<Owner.Probe<{}, Fresh, {}>> {\n            read ignored => resume 42\n            store ignored => resume ()\n        }",
    );
    let explicit = owner
        .replace(
            "finish (state, data) => match perform Free",
            "finish (state, data) => {\n        let latest : Unit -> Int = Foreign.data_of state\n        match perform Free",
        )
        .replace("ConsumedFailure data", "ConsumedFailure latest")
        .replace("Retained(state, data)", "Retained(state, latest)")
        .replace("    handlers (state, data)", "    }\n    handlers (state, data)");
    let discarded = format!("{owner}\nindependent : Unit -> Int\nindependent ignored = 42\n")
        .replace("ConsumedFailure data", "Consumed")
        .replace("Retained(state, data)", "Retained(state, independent)");
    let mut unexpected = Vec::new();
    for (name, library, source, accepted) in [
        ("independent replacement", owner, independent.as_str(), true),
        ("explicit latest read", explicit.as_str(), entry, false),
        ("implicit finish data", owner, entry, false),
        ("locally handled request", owner, handled.as_str(), false),
        (
            "payload retained identity",
            discarded.as_str(),
            entry,
            false,
        ),
    ] {
        let fixture = Fixture::new(source);
        fs::write(fixture.0.join("owner.ash"), library).unwrap();
        match compile_path(fixture.configuration()) {
            Ok(_) => {
                println!("{name}: accepted through independent Core");
                if !accepted {
                    unexpected.push(name);
                }
            }
            Err(failure) => {
                println!("{name}: {}", failure.reason_code());
                assert!(
                    !accepted,
                    "independent callback must remain legal: {failure:?}"
                );
                assert_eq!(failure.reason_code(), "type.resource-escape");
            }
        }
    }
    assert!(
        unexpected.is_empty(),
        "closing-owner capture admitted: {unexpected:?}"
    );
}

#[test]
fn pr27_latest_finish_payload_preserves_immutable_handler_aliases() {
    let owner = include_str!("fixtures/source-owner/replaced_payload_owner.ash")
        .replace("read : Access -> Int", "read : Access -> (Unit -> Int)")
        .replace("read access => resume 7", "read access => resume data");
    // The handler returns its independent callback value. Calling that value
    // belongs to the ordinary body, outside the bounded lifecycle call carrier.
    generated_owner_program_with_native(
        &owner,
        "import owner as Owner\ninitial : Unit -> Int\ninitial () = 7\nmain : Unit -> (Int, Int)\nmain () = {\n    let report = resource Owner.Probe<{}, Fresh, {}> owner = initial {\n        let replacement : Unit -> Int = fn(ignored) {\n            42\n        }\n        let stored = Owner.store (owner, replacement)\n        let original = Owner.read owner\n        original ()\n    }\n    match report {\n        Owner.Completed(observed, Owner.ConsumedError(action)) => (observed, action ())\n        _ => (0, 0)\n    }\n}\n",
        None,
        "(7, 42)",
        "acquire:8\nrelease:8\n",
        include_str!("fixtures/source-owner/native_owner.c"),
    );
}

#[test]
fn pr27_acquired_handler_borrow_uses_the_exact_retained_enclosing_owner() {
    let query = r#"    symbol ChildQuery<P, R> : (ChildState<P, R>, ParentState<P>) -> Foreign.Call<Int> {
        name "ash_child_query"
        abi (pointer(Address), pointer(ParentBytes)) -> Status
        operand 0 from 0 current
        operand 1 from 1 enclosing
        output result as scalar
        outcome otherwise { readable result }
    }
"#;
    let owner = include_str!("fixtures/source-owner/dependent_owner.ash")
        .replace("    repr Size = size_t", "    repr Size = size_t\n    repr Status = signed(32)")
        .replace("    symbol ChildHold<P, R>", &format!("{query}    symbol ChildHold<P, R>"))
        .replace("interpret ChildAllocate<P, R>, ChildHold<P, R>", "interpret ChildAllocate<P, R>, ChildHold<P, R>, ChildQuery<P, R>")
        .replace("child_read access => resume label", "child_read access => {\n            let dependency = perform ParentOps<Parent<P>, ParentState<P>>.borrow parent\n            match perform ChildQuery<P, R>.call (state, dependency) {\n                Foreign.Returned(value) => resume value\n                Foreign.ConversionFailed(_) => resume 0\n            }\n        }");
    let native = format!(
        "{}\nint ash_child_query(struct ash_child *child, struct ash_parent *parent) {{\n    assert(child != NULL && child->parent == parent && parent->children != 0);\n    record(\"child-query\", child->identity);\n    return 42;\n}}\n",
        include_str!("fixtures/source-owner/native_dependent_owner.c")
    );
    generated_owner_program_with_native(
        &owner,
        "import owner as Owner\nmain : Unit -> Owner.Scope<Unit, Unit, Owner.Scope<Unit, Unit, Int>>\nmain () = resource Owner.Parent<ParentFresh> parent = 64 {\n    resource Owner.Child<ParentFresh, ChildFresh> child = (parent, 4) {\n        Owner.child_read child\n    }\n}\n",
        None,
        "Completed(Completed(42, RetainedError(())), RetainedError(()))",
        "parent-acquire:64\nchild-acquire:4\nchild-query:4\nchild-retain:4\nchild-release:4\nparent-final-byte:99\nparent-release:64\n",
        &native,
    );
}

#[test]
fn generated_status_owner_records_consumption_before_reporting_scalar_result() {
    let owner = owner_with_scalar_teardown_result();
    let native = include_str!("fixtures/source-owner/native_owner.c")
        .replace("void ash_owner_release(void *raw)", "int32_t ash_owner_release(void *raw)")
        .replace(
            "record(\"release\", owner->size);\n    free(owner);",
            "int32_t status = owner->size == 42 ? 3 : 0;\n    record(\"release\", owner->size);\n    free(owner);\n    return status;",
        );
    generated_owner_program_with_native(
        &owner,
        "import owner as Owner\nprobe : Int -> Owner.Scope<Unit, Int, Int>\nprobe size = resource Owner.Probe<{}, Fresh, {}> owner = size {\n    Owner.read owner\n}\nmain : Unit -> (Owner.Scope<Unit, Int, Int>, Owner.Scope<Unit, Int, Int>)\nmain () = (probe 42, probe 64)\n",
        None,
        "(Completed(42, ConsumedError(3)), Completed(64, Closed))",
        "acquire:42\nrelease:42\nacquire:64\nrelease:64\n",
        &native,
    );
}

fn owner_with_conditional_status_teardown() -> String {
    include_str!("fixtures/source-owner/status_owner.ash").to_owned()
}

#[test]
fn generated_status_owner_retains_then_original_host_teardown_consumes_once() {
    let native = include_str!("fixtures/source-owner/native_owner.c")
        .replace("size_t size;", "size_t size;\n    unsigned attempts;")
        .replace("owner->size = size;", "owner->size = size;\n    owner->attempts = 0;")
        .replace("void ash_owner_release(void *raw)", "int32_t ash_owner_release(void *raw)")
        .replace("record(\"release\", owner->size);\n    free(owner);", "record(\"release\", owner->size);\n    if (owner->attempts++ == 0) return 7;\n    free(owner);\n    return 0;");
    generated_owner_program_with_native(
        &owner_with_conditional_status_teardown(),
        "import owner as Owner\nmain : Unit -> Owner.Scope<Unit, Int, Int>\nmain () = resource Owner.Probe<{}, Fresh, {}> owner = 42 {\n    Owner.read owner\n}\n",
        None,
        "Completed(42, RetainedError(7))",
        "acquire:42\nrelease:42\nrelease:42\n",
        &native,
    );
}

#[test]
fn generated_status_owner_incomplete_host_teardown_does_not_retry() {
    let native = include_str!("fixtures/source-owner/native_owner.c")
        .replace(
            "void ash_owner_release(void *raw)",
            "int32_t ash_owner_release(void *raw)",
        )
        .replace(
            "record(\"release\", owner->size);\n    free(owner);",
            "record(\"release\", owner->size);\n    return 7;",
        );
    generated_owner_execution_with_native(
        &owner_with_conditional_status_teardown(),
        "import owner as Owner\nmain : Unit -> Owner.Scope<Unit, Int, Int>\nmain () = resource Owner.Probe<{}, Fresh, {}> owner = 42 {\n    Owner.read owner\n}\n",
        None,
        Err("source resource completion failed"),
        "acquire:42\nrelease:42\nrelease:42\n",
        &native,
    );
}

#[test]
fn generated_status_dependent_retention_blocks_parent_before_c_and_host_recovers_in_order() {
    let owner = include_str!("fixtures/source-owner/dependent_owner.ash")
        .replace(
            "    repr Size = size_t",
            "    repr Size = size_t\n    repr Status = signed(32)\n    const Held : Status = 7",
        )
        .replace(
            "        let marked = Foreign.byte_write (state, 0, 99)\n",
            "",
        );
    let owner = owner.replace("symbol ParentFree<P> : ParentState<P> -> Foreign.Call<Foreign.Disposition<Unit>>", "symbol ParentFree<P> : ParentState<P> -> Foreign.Call<Foreign.Disposition<Int>>")
        .replace("abi (pointer(ParentBytes)) -> void", "abi (pointer(ParentBytes)) -> Status")
        .replace("        outcome otherwise { consumed 0 }", "        output result as scalar\n        outcome otherwise { readable result, consumed 0 }");
    let start = owner.find("    symbol ChildFree<P, R>").unwrap();
    let end = start + owner[start..].find("    symbol ChildHold<P, R>").unwrap();
    let free = owner[start..end]
        .replace("Foreign.Disposition<Unit>", "Foreign.Disposition<Int>")
        .replace("-> void", "-> Status")
        .replace("outcome otherwise { readable result, consumed 0 }", "outcome result == Held { readable result, retained 0 }\n        outcome otherwise { readable result, consumed 0 }");
    let owner = format!("{}{free}{}", &owner[..start], &owner[end..]);
    let parent_start = owner.find("pub resource Parent<P>").unwrap();
    let child_start = owner.find("pub interface ChildProvider").unwrap();
    let parent = owner[parent_start..child_start]
        .replace(
            "completion Finish<ParentState<P>, Unit>",
            "completion Finish<ParentState<P>, Int>",
        )
        .replace(
            "result Scope<Unit, Unit, Answer>",
            "result Scope<Unit, Int, Answer>",
        )
        .replace("Foreign.Consumed(())", "Foreign.Consumed(_)")
        .replace(
            "Foreign.Returned(Foreign.Retained(())) => Retained(state, ())",
            "Foreign.Returned(Foreign.Retained(status)) => Retained(state, status)",
        )
        .replace(
            "Foreign.Returned(Foreign.BlockedDependent) => Retained(state, ())",
            "Foreign.Returned(Foreign.BlockedDependent) => Retained(state, 111)",
        )
        .replace("Retained(state, ())", "Retained(state, 222)");
    let owner = format!(
        "{}{parent}{}",
        &owner[..parent_start],
        &owner[child_start..]
    );
    let child_start = owner.find("pub resource Child<P, R>").unwrap();
    let child = owner[child_start..]
        .replace("ChildHold<P, R>", "ChildFree<P, R>")
        .replace(
            "completion Finish<ChildState<P, R>, Unit>",
            "completion Finish<ChildState<P, R>, Int>",
        )
        .replace(
            "result Scope<Unit, Unit, Answer>",
            "result Scope<Unit, Int, Answer>",
        )
        .replace("Foreign.Consumed(())", "Foreign.Consumed(_)")
        .replace(
            "Foreign.Returned(Foreign.Retained(())) => Retained(state, ())",
            "Foreign.Returned(Foreign.Retained(status)) => Retained(state, status)",
        )
        .replace("Retained(state, ())", "Retained(state, 1)");
    let owner = format!("{}{child}", &owner[..child_start]);
    let native = include_str!("fixtures/source-owner/native_dependent_owner.c")
        .replace("#include <assert.h>", "#include <assert.h>\n#include <stdint.h>")
        .replace("void ash_child_release", "int32_t ash_child_release")
        .replace("void ash_parent_release", "int32_t ash_parent_release")
        .replace("    free(parent);", "    free(parent);\n    return 0;")
        .replace("    record(\"child-release\", child->identity);", "    static unsigned attempts;\n    record(\"child-release\", child->identity);\n    if (attempts++ == 0) return 7;")
        .replace("    free(child);", "    free(child);\n    return 0;");
    generated_owner_program_with_native(
        &owner,
        "import owner as Owner\nmain : Unit -> Owner.Scope<Unit, Int, Owner.Scope<Unit, Int, Int>>\nmain () = resource Owner.Parent<ParentFresh> parent = 64 {\n    resource Owner.Child<ParentFresh, ChildFresh> child = (parent, 4) {\n        Owner.child_read child\n    }\n}\n",
        None,
        "Completed(Completed(4, RetainedError(7)), RetainedError(111))",
        "parent-acquire:64\nchild-acquire:4\nchild-release:4\nchild-release:4\nparent-final-byte:0\nparent-release:64\n",
        &native,
    );
}

#[test]
fn checked_source_status_literal_also_publishes_an_ordinary_int_value() {
    let fixture = Fixture::new("import owner as Owner\nmain : Unit -> Int\nmain () = Owner.Held\n");
    fs::write(
        fixture.0.join("owner.ash"),
        owner_with_conditional_status_teardown(),
    )
    .unwrap();
    let value = ash::driver::run_path(fixture.configuration()).unwrap();
    assert_eq!(value.value_display(), "7");
}

fn status_native_consuming() -> String {
    include_str!("fixtures/source-owner/native_owner.c")
        .replace(
            "void ash_owner_release(void *raw)",
            "int32_t ash_owner_release(void *raw)",
        )
        .replace(
            "record(\"release\", owner->size);\n    free(owner);",
            "record(\"release\", owner->size);\n    free(owner);\n    return 0;",
        )
}

#[test]
fn generated_status_owner_resume_and_ordinary_override_keep_one_activation() {
    generated_owner_program_with_native(
        &owner_with_scalar_teardown_result(),
        "import owner as Owner\neffect Pause {\n    pause : Unit -> Unit\n}\nmain : Unit -> Owner.Scope<Unit, Int, (Int, Int)>\nmain () = handle (resource Owner.Probe<{}, Fresh, {}> owner = 42 {\n    let paused = perform Pause.pause ()\n    let overridden = handle (Owner.read owner) with Owner.ProbeOps<Owner.Probe<{}, Fresh, {}>> {\n        read access => resume 84\n    }\n    (overridden, Owner.read owner)\n}) with Pause {\n    pause ignored => resume ()\n}\n",
        None,
        "Completed((84, 42), Closed)",
        "acquire:42\nrelease:42\n",
        &status_native_consuming(),
    );
}

#[test]
fn generated_status_owner_retained_discard_is_terminal_even_when_host_later_consumes() {
    let native = include_str!("fixtures/source-owner/native_owner.c")
        .replace("size_t size;", "size_t size;\n    unsigned attempts;")
        .replace("owner->size = size;", "owner->size = size;\n    owner->attempts = 0;")
        .replace("void ash_owner_release(void *raw)", "int32_t ash_owner_release(void *raw)")
        .replace("record(\"release\", owner->size);\n    free(owner);", "record(\"release\", owner->size);\n    if (owner->attempts++ == 0) return 7;\n    free(owner);\n    return 0;");
    generated_owner_execution_with_native(
        &owner_with_conditional_status_teardown(),
        "import owner as Owner\neffect Pause {\n    pause : Unit -> Unit\n}\nmain : Unit -> Int\nmain () = handle {\n    let abandoned = resource Owner.Probe<{}, Fresh, {}> owner = 42 {\n        let paused = perform Pause.pause ()\n        Owner.read owner\n    }\n    111\n} with Pause {\n    pause ignored => {\n        let closed = discard\n        84\n    }\n}\n",
        None,
        Err("source resource completion failed"),
        "acquire:42\nrelease:42\nrelease:42\n",
        &native,
    );
}

#[test]
fn source_status_unreadable_scalar_contract_is_refused_before_execution() {
    for disposition in ["consumed", "retained"] {
        let fixture = Fixture::new(
            "import owner as Owner\nmain : Unit -> Owner.Scope<Unit, Int, Int>\nmain () = resource Owner.Probe<{}, Fresh, {}> owner = 42 {\n    Owner.read owner\n}\n",
        );
        let owner = owner_with_scalar_teardown_result().replace(
            "outcome otherwise { readable result, consumed 0 }",
            &format!("outcome otherwise {{ unreadable result, {disposition} 0 }}"),
        );
        fs::write(fixture.0.join("owner.ash"), owner).unwrap();
        let failure = compile_path(fixture.configuration()).unwrap_err();
        let Some(ash::driver::PipelineFailure::Resolution(error)) = failure.pipeline_failure()
        else {
            panic!("expected scalar contract admission refusal: {failure:?}");
        };
        assert_eq!(error.reason, ash::resolve::ResolveReason::ForeignContract);
        assert!(
            error.to_string().contains("readable exactly once"),
            "{error}"
        );
    }
}

#[test]
fn generated_status_owner_widens_full_unsigned_native_range_after_recording() {
    let owner = owner_with_scalar_teardown_result()
        .replace("repr Status = signed(32)", "repr Status = unsigned(64)");
    let native = include_str!("fixtures/source-owner/native_owner.c")
        .replace(
            "void ash_owner_release(void *raw)",
            "uint64_t ash_owner_release(void *raw)",
        )
        .replace(
            "record(\"release\", owner->size);\n    free(owner);",
            "record(\"release\", owner->size);\n    free(owner);\n    return UINT64_MAX;",
        );
    generated_owner_program_with_native(
        &owner,
        "import owner as Owner\nmain : Unit -> Owner.Scope<Unit, Int, Int>\nmain () = resource Owner.Probe<{}, Fresh, {}> owner = 42 {\n    Owner.read owner\n}\n",
        None,
        "Completed(42, ConsumedError(18446744073709551615))",
        "acquire:42\nrelease:42\n",
        &native,
    );
}

#[test]
fn source_status_readable_consumed_result_cannot_restore_revoked_state() {
    let fixture = Fixture::new(
        "import owner as Owner\nmain : Unit -> Owner.Scope<Unit, Int, Int>\nmain () = resource Owner.Probe<{}, Fresh, {}> owner = 42 {\n    Owner.read owner\n}\n",
    );
    let owner = owner_with_scalar_teardown_result()
        .replace("true => Consumed", "true => Retained(state, 1)");
    fs::write(fixture.0.join("owner.ash"), owner).unwrap();
    let failure = compile_path(fixture.configuration()).unwrap_err();
    assert!(matches!(
        failure.pipeline_failure(),
        Some(ash::driver::PipelineFailure::Typing(_))
    ));
}

#[test]
fn source_owner_retained_disposition_is_admitted() {
    let fixture = Fixture::new(
        "import owner as Owner\nmain : Unit -> Owner.Scope<Unit, Unit, Int>\nmain () = resource Owner.Probe<{}, Fresh, {}> owner = 42 {\n    Owner.read owner\n}\n",
    );
    let owner = include_str!("fixtures/source-owner/owner.ash").replace(
        "outcome otherwise { consumed 0 }",
        "outcome otherwise { retained 0 }",
    );
    fs::write(fixture.0.join("owner.ash"), owner).unwrap();
    compile_path(fixture.configuration())
        .expect("declared retained native disposition must reach source-resource admission");
}

#[test]
fn source_owner_declared_enclosing_dependency_is_admitted() {
    let fixture = Fixture::new(
        "import owner as Owner\nmain : Unit -> Owner.Scope<Unit, Unit, Owner.Scope<Unit, Unit, Int>>\nmain () = resource Owner.Parent<ParentFresh> parent = 64 {\n    resource Owner.Child<ParentFresh, ChildFresh> child = (parent, 4) {\n        Owner.child_read child\n    }\n}\n",
    );
    fs::write(
        fixture.0.join("owner.ash"),
        include_str!("fixtures/source-owner/dependent_owner.ash"),
    )
    .unwrap();
    compile_path(fixture.configuration()).unwrap_or_else(|error| {
        panic!(
            "declared enclosing dependency: {} {:?}",
            error.reason_code(),
            error.pipeline_failure()
        );
    });
}

fn dependent_owner_with_wrapped_access() -> String {
    let owner = include_str!("fixtures/source-owner/dependent_owner.ash").replace(
        "pub type Acquire<",
        "pub type Wrapped<T> = Wrapped(T)\n\npub type Acquire<",
    );
    let start = owner.find("pub resource Child<P, R>").unwrap();
    let child = owner[start..]
        .replace("(Parent<P>, Int)", "(Wrapped<Parent<P>>, Int)")
        .replace(
            "acquire (parent, label)",
            "acquire (Wrapped(parent), label)",
        )
        .replace(
            "Acquired(state, (parent, label))",
            "Acquired(state, (Wrapped(parent), label))",
        )
        .replace(
            "finish (state, (parent, label))",
            "finish (state, (Wrapped(parent), label))",
        )
        .replace(
            "handlers (state, (parent, label))",
            "handlers (state, (Wrapped(parent), label))",
        );
    format!("{}{child}", &owner[..start])
}

#[test]
fn source_owner_wrapped_access_dependency_is_admitted() {
    let fixture = Fixture::new(
        "import owner as Owner\nmain : Unit -> Owner.Scope<Unit, Unit, Owner.Scope<Unit, Unit, Int>>\nmain () = resource Owner.Parent<ParentFresh> parent = 64 {\n    resource Owner.Child<ParentFresh, ChildFresh> child = (Owner.Wrapped parent, 4) {\n        Owner.child_read child\n    }\n}\n",
    );
    fs::write(
        fixture.0.join("owner.ash"),
        dependent_owner_with_wrapped_access(),
    )
    .unwrap();
    compile_path(fixture.configuration()).unwrap_or_else(|error| {
        panic!(
            "wrapped access dependency: {} {:?}",
            error.reason_code(),
            error.pipeline_failure()
        );
    });
}

#[test]
fn source_owner_rejects_enclosing_native_state_in_private_data() {
    let original = include_str!("fixtures/source-owner/dependent_owner.ash");
    let start = original.find("pub resource Child<P, R>").unwrap();
    let child = original[start..]
        .replace("Parent<P>", "ParentState<P>")
        .replace(
            "        let dependency = perform ParentOps<ParentState<P>, ParentState<P>>.borrow parent\n",
            "",
        )
        .replace("(dependency, label)", "(parent, label)")
        .replace("(state, dependency)", "(state, parent)");
    let tuple = format!("{}{child}", &original[..start]);
    let fixture = Fixture::new("import owner as Owner\nmain : Unit -> Int\nmain () = 42\n");
    let prefix = original[..start].replace(
        "pub type Acquire<",
        "pub type Wrapped<T> = Wrapped(T)\n\npub type Acquire<",
    );
    let wrapped_child = child
        .replace("(ParentState<P>, Int)", "(Wrapped<ParentState<P>>, Int)")
        .replace(
            "acquire (parent, label)",
            "acquire (Wrapped(parent), label)",
        )
        .replace(
            "finish (state, (parent, label))",
            "finish (state, (Wrapped(parent), label))",
        )
        .replace(
            "handlers (state, (parent, label))",
            "handlers (state, (Wrapped(parent), label))",
        )
        .replace(
            "Acquired(state, (parent, label))",
            "Acquired(state, (Wrapped parent, label))",
        );
    let wrapped = format!("{prefix}{wrapped_child}");
    let hidden = original[..start].replace(
        "pub type Acquire<",
        "pub type Hidden<P> = Hidden(ParentState<P>)\n\npub type Acquire<",
    );
    let hidden_child = child
        .replace("(ParentState<P>, Int)", "(Hidden<P>, Int)")
        .replace("acquire (parent, label)", "acquire (Hidden(parent), label)")
        .replace(
            "finish (state, (parent, label))",
            "finish (state, (Hidden(parent), label))",
        )
        .replace(
            "handlers (state, (parent, label))",
            "handlers (state, (Hidden(parent), label))",
        )
        .replace(
            "Acquired(state, (parent, label))",
            "Acquired(state, (Hidden parent, label))",
        );
    let hidden = format!("{hidden}{hidden_child}");
    for (position, owner) in [tuple, wrapped, hidden].into_iter().enumerate() {
        fs::write(fixture.0.join("owner.ash"), owner).unwrap();
        let failure = match compile_path(fixture.configuration()) {
            Err(failure) => failure,
            Ok(_) => panic!("an enclosing native State cannot become ordinary private D"),
        };
        assert_eq!(failure.reason_code(), "type.argument");
        println!(
            "private native State refusal {position}: {:?}",
            failure.pipeline_failure()
        );
    }
    // The same declared dependency still admits ordinary handles in D and
    // locally authenticated native State in acquisition and finish.
    fs::write(fixture.0.join("owner.ash"), original).unwrap();
    compile_path(fixture.configuration()).expect("local lifecycle State is not private storage");
}

#[test]
fn source_owner_rejects_undeclared_dependency_inside_ordinary_adt_payload() {
    let owner = dependent_owner_with_wrapped_access();
    let start = owner.find("pub resource Child<P, R>").unwrap();
    let child = owner[start..]
        .replace("Child<P, R>", "Child<P, Q, R>")
        .replace(
            "(Wrapped<Parent<P>>, Int)",
            "(Wrapped<Parent<P>>, Wrapped<Parent<Q>>, Int)",
        )
        .replace(
            "(Wrapped(parent), label)",
            "(Wrapped(parent), Wrapped(other), label)",
        );
    let fixture = Fixture::new(
        "import owner as Owner\nmain : Unit -> Owner.Scope<Unit, Unit, Owner.Scope<Unit, Unit, Int>>\nmain () = resource Owner.Parent<First> first = 64 {\n    resource Owner.Parent<Second> second = 65 {\n        let child_report = resource Owner.Child<First, Second, ChildFresh> child = (Owner.Wrapped first, Owner.Wrapped second, 4) {\n            Owner.child_read child\n        }\n        0\n    }\n}\n",
    );
    let owner = format!("{}{child}", &owner[..start]);
    fs::write(fixture.0.join("owner.ash"), &owner).unwrap();
    let failure = match compile_path(fixture.configuration()) {
        Err(failure) => failure,
        Ok(_) => panic!("an ordinary ADT cannot add an undeclared owner dependency"),
    };
    assert_eq!(failure.reason_code(), "type.argument");
    println!(
        "undeclared wrapped dependency refusal: {} {:?}",
        failure.reason_code(),
        failure.pipeline_failure()
    );
    // Keep the same source payload/patterns/provider, while making Q a genuine
    // declared owner role. This positive control isolates the dependency census
    // from ordinary ADT shape or a malformed source method signature.
    let declared = owner
        .replace("ChildState<P, R>", "ChildState<P, Q, R>")
        .replace("retains P", "retains P, Q")
        .replace("ChildAllocate<P, R>", "ChildAllocate<P, Q, R>")
        .replace("ChildHold<P, R>", "ChildHold<P, Q, R>")
        .replace("ChildFree<P, R>", "ChildFree<P, Q, R>");
    fs::write(fixture.0.join("owner.ash"), declared).unwrap();
    compile_path(fixture.configuration())
        .expect("declared ordinary ADT access roles admit the same well-typed payload");
}

#[test]
fn generated_dependent_non_nearest_same_family_owner_keeps_exact_parent_activation() {
    generated_owner_program_with_native(
        include_str!("fixtures/source-owner/dependent_owner.ash"),
        "import owner as Owner\nmain : Unit -> Owner.Scope<Unit, Unit, Owner.Scope<Unit, Unit, Owner.Scope<Unit, Unit, Int>>>\nmain () = resource Owner.Parent<First> first = 64 {\n    resource Owner.Parent<Second> second = 65 {\n        resource Owner.Child<First, ChildFresh> child = (first, 4) {\n            Owner.child_read child\n        }\n    }\n}\n",
        None,
        "Completed(Completed(Completed(4, RetainedError(())), Closed), RetainedError(()))",
        "parent-acquire:64\nparent-acquire:65\nchild-acquire:4\nchild-retain:4\nparent-release:65\nchild-release:4\nparent-final-byte:99\nparent-release:64\n",
        include_str!("fixtures/source-owner/native_dependent_owner.c"),
    );
}

#[test]
fn generated_dependent_wrapped_access_keeps_native_views_out_of_private_data() {
    generated_owner_program_with_native(
        &dependent_owner_with_wrapped_access(),
        "import owner as Owner\nmain : Unit -> Owner.Scope<Unit, Unit, Owner.Scope<Unit, Unit, Int>>\nmain () = resource Owner.Parent<ParentFresh> parent = 64 {\n    resource Owner.Child<ParentFresh, ChildFresh> child = (Owner.Wrapped parent, 4) {\n        Owner.child_read child\n    }\n}\n",
        None,
        "Completed(Completed(4, RetainedError(())), RetainedError(()))",
        "parent-acquire:64\nchild-acquire:4\nchild-retain:4\nchild-release:4\nparent-final-byte:99\nparent-release:64\n",
        include_str!("fixtures/source-owner/native_dependent_owner.c"),
    );
}

#[test]
fn generated_dependent_retained_child_blocks_parent_until_host_destruction() {
    generated_owner_program_with_native(
        include_str!("fixtures/source-owner/dependent_owner.ash"),
        "import owner as Owner\nmain : Unit -> Owner.Scope<Unit, Unit, Owner.Scope<Unit, Unit, Int>>\nmain () = resource Owner.Parent<ParentFresh> parent = 64 {\n    resource Owner.Child<ParentFresh, ChildFresh> child = (parent, 4) {\n        Owner.child_read child\n    }\n}\n",
        None,
        "Completed(Completed(4, RetainedError(())), RetainedError(()))",
        "parent-acquire:64\nchild-acquire:4\nchild-retain:4\nchild-release:4\nparent-final-byte:99\nparent-release:64\n",
        include_str!("fixtures/source-owner/native_dependent_owner.c"),
    );
}

fn dependent_owner_with_consumed_finish() -> String {
    include_str!("fixtures/source-owner/dependent_owner.ash")
        .replace(
            "interpret ChildAllocate<P, R>, ChildHold<P, R>",
            "interpret ChildAllocate<P, R>, ChildFree<P, R>",
        )
        .replace(
            "match perform ChildHold<P, R>.call",
            "match perform ChildFree<P, R>.call",
        )
}

#[test]
fn generated_transitive_retention_keeps_pending_dependency_cleanup_and_host_order() {
    let owner = include_str!("fixtures/source-owner/dependent_owner.ash")
        .replace("repr ParentBytes = bytes", "repr ParentBytes = opaque")
        .replace(
            "readable result, initialized_bytes result from 0",
            "readable result",
        )
        .replace("    read : Access -> Int ! {ParentOps<Access, State>}\n", "")
        .replace("    read : Access -> Int\n", "")
        .replace("        read access => resume data\n", "")
        .replace("        let marked = Foreign.byte_write (state, 0, 99)\n", "")
        .replace("ChildHold<P, R>", "ChildFree<P, R>")
        .replace("pub interface ChildProvider<Access>", "pub interface ChildProvider<Access, State>")
        .replace("ChildOps<Access>", "ChildOps<Access, State>")
        .replace("ChildProvider<Child<P, R>>", "ChildProvider<Child<P, R>, ChildState<P, R>>")
        .replace("ChildOps<Child<P, R>>", "ChildOps<Child<P, R>, ChildState<P, R>>")
        .replace("    child_read : Access -> Int ! {ChildOps<Access, State>}", "    child_borrow : Access -> State ! {ChildOps<Access, State>}\n    child_read : Access -> Int ! {ChildOps<Access, State>}")
        .replace("    child_read : Access -> Int\n", "    child_borrow : Access -> State\n    child_read : Access -> Int\n")
        .replace("        child_read access => resume label", "        child_borrow access => resume state\n        child_read access => resume label")
        .replace("    symbol ParentAllocate<P>", concat!(
            "    owner GrandState<P, R, G> {\n        representation Address\n        owned G\n        retains R\n        teardown GrandFree\n    }\n",
            "    symbol GrandAllocate<P, R, G> : (ChildState<P, R>, Int) -> Foreign.Call<Foreign.Output<Foreign.Nullable<GrandState<P, R, G>>>> {\n",
            "        name \"ash_grand_acquire\"\n        abi (pointer(Address), Size) -> pointer(Address)\n        operand 0 from 0 enclosing\n        operand 1 from 1 scalar\n        output result as owner(GrandState<P, R, G>)\n        outcome result nonnull { readable result }\n        outcome otherwise { readable result }\n    }\n",
            "    symbol GrandFree<P, R, G> : (GrandState<P, R, G>, ChildState<P, R>) -> Foreign.Call<Foreign.Disposition<Unit>> {\n",
            "        name \"ash_grand_release\"\n        abi (pointer(Address), pointer(Address)) -> void\n        operand 0 from 0 current\n        operand 1 from 1 enclosing\n        retained_dependents block\n        outcome otherwise { consumed 0 }\n    }\n",
            "    symbol GrandHold<P, R, G> : (GrandState<P, R, G>, ChildState<P, R>) -> Foreign.Call<Foreign.Disposition<Unit>> {\n",
            "        name \"ash_grand_hold\"\n        abi (pointer(Address), pointer(Address)) -> void\n        operand 0 from 0 current\n        operand 1 from 1 enclosing\n        retained_dependents block\n        outcome otherwise { retained 0 }\n    }\n",
            "    symbol ParentAllocate<P>"
        ));
    // Child finish is blocked by the live grandchild; its ordinary consuming
    // symbol and the separate host destructor therefore share one contract.
    // Drop the now-duplicate unused symbol, not any lifecycle obligation.
    let mut owner = owner;
    let last = owner.rfind("    symbol ChildFree<P, R>").unwrap();
    let end = last + owner[last..].find("    }\n").unwrap() + "    }\n".len();
    owner.replace_range(last..end, "");
    let owner = owner
        .replace(
            "    child_read : Access -> Int ! {ChildOps<Access, State>}\n",
            "",
        )
        .replace("    child_read : Access -> Int\n", "")
        .replace("        child_read access => resume label\n", "");
    let owner = format!(
        "{owner}\n{}",
        include_str!("fixtures/source-owner/grandchild_resource.ash")
    );
    let mut owner = owner;
    for indent in ["        ", "            "] {
        owner = owner.replace(
            &format!("{indent}Foreign.Returned(Foreign.Readable(Foreign.Null)) => Refused ()\n{indent}Foreign.Returned(Foreign.Unreadable) => Refused ()\n{indent}Foreign.ConversionFailed(_) => Refused ()"),
            &format!("{indent}_ => Refused ()"),
        ).replace(
            &format!("{indent}Foreign.Returned(Foreign.Retained(())) => Retained(state, ())\n{indent}Foreign.Returned(Foreign.BlockedDependent) => Retained(state, ())\n{indent}Foreign.ConversionFailed(_) => Retained(state, ())"),
            &format!("{indent}_ => Retained(state, ())"),
        );
    }
    let native = include_str!("fixtures/source-owner/native_dependent_owner.c")
        .replace(
            "    struct ash_parent *parent;",
            "    struct ash_parent *parent;\n    size_t children;",
        )
        .replace(
            "    child->parent = parent;",
            "    child->parent = parent;\n    child->children = 0;",
        )
        .replace(
            "    record(\"child-release\", child->identity);",
            "    assert(child->children == 0);\n    record(\"child-release\", child->identity);",
        );
    let native = format!(
        "{native}\n{}",
        include_str!("fixtures/source-owner/native_grandchild.c")
    );
    generated_owner_execution_with_native(
        &owner,
        "import owner as Owner\nmain : Unit -> Owner.Scope<Unit, Unit, Owner.Scope<Unit, Unit, Owner.Scope<Unit, Unit, Int>>>\nmain () = resource Owner.Parent<P> parent = 64 {\n    resource Owner.Child<P, R> child = (parent, 4) {\n        resource Owner.Grand<P, R, G> grand = (child, 5) {\n            5\n        }\n    }\n}\n",
        None,
        Ok(
            "Completed(Completed(Completed(5, RetainedError(())), RetainedError(())), RetainedError(()))",
        ),
        "parent-acquire:64\nchild-acquire:4\ngrand-acquire:5\ngrand-retain:5\ngrand-release:5\nchild-release:4\nparent-final-byte:0\nparent-release:64\n",
        &native,
    );
}

fn pending_sibling_owner() -> String {
    let original = include_str!("fixtures/source-owner/dependent_owner.ash");
    let split = original.find("pub interface ChildProvider").unwrap();
    let sibling = original[split..]
        .replace("ChildProvider", "SiblingProvider")
        .replace("ChildOps", "SiblingOps")
        .replace("Child<P, R>", "Sibling<P, R>")
        .replace("child_read", "sibling_read")
        .replace("ChildHold<P, R>", "ChildFree<P, R>");
    format!("{original}\n{sibling}")
        .replace("repr ParentBytes = bytes", "repr ParentBytes = opaque")
        .replace(
            "readable result, initialized_bytes result from 0",
            "readable result",
        )
        .replace(
            "    read : Access -> Int ! {ParentOps<Access, State>}\n",
            "",
        )
        .replace("    read : Access -> Int\n", "")
        .replace("        read access => resume data\n", "")
        .replace(
            "        let marked = Foreign.byte_write (state, 0, 99)\n",
            "",
        )
}

#[test]
fn generated_retained_sibling_keeps_pending_enclosing_state_cleanup_live() {
    let owner = pending_sibling_owner();
    generated_owner_program_with_native(
        &owner,
        "import owner as Owner\nmain : Unit -> Owner.Scope<Unit, Unit, Owner.Scope<Unit, Unit, Owner.Scope<Unit, Unit, Int>>>\nmain () = resource Owner.Parent<P> parent = 64 {\n    resource Owner.Sibling<P, R> sibling = (parent, 4) {\n        resource Owner.Child<P, T> child = (parent, 5) {\n            5\n        }\n    }\n}\n",
        None,
        "Completed(Completed(Completed(5, RetainedError(())), Closed), RetainedError(()))",
        "parent-acquire:64\nchild-acquire:4\nchild-acquire:5\nchild-retain:5\nchild-release:4\nparent-final-byte:0\nchild-release:5\nparent-final-byte:0\nparent-release:64\n",
        include_str!("fixtures/source-owner/native_dependent_owner.c"),
    );
}

#[test]
fn generated_retained_sibling_cleanup_cannot_restore_ordinary_parent_read() {
    let owner = pending_sibling_owner()
        .replace("    borrow : Access -> State ! {ParentOps<Access, State>}\n", "    borrow : Access -> State ! {ParentOps<Access, State>}\n    read : Access -> Int ! {ParentOps<Access, State>}\n")
        .replace("    borrow : Access -> State\n", "    borrow : Access -> State\n    read : Access -> Int\n")
        .replace("        borrow access => resume state\n", "        borrow access => resume state\n        read access => resume data\n");
    let split = owner.find("pub resource Sibling<P, R>").unwrap();
    let sibling = owner[split..].replace(
        "    finish (state, (parent, label)) => {\n",
        "    finish (state, (parent, label)) => {\n        let forbidden = perform ParentOps<Parent<P>, ParentState<P>>.read parent\n",
    );
    let owner = format!("{}{sibling}", &owner[..split]);
    // The extra ordinary operation is the discriminating negative. Equivalent
    // refusal/retention alternatives keep its independent fixture within the
    // normal cumulative image allowance without changing any native contract.
    let mut owner = owner;
    for indent in ["        ", "            "] {
        owner = owner.replace(
            &format!("{indent}Foreign.Returned(Foreign.Readable(Foreign.Null)) => Refused ()\n{indent}Foreign.Returned(Foreign.Unreadable) => Refused ()\n{indent}Foreign.ConversionFailed(_) => Refused ()"),
            &format!("{indent}_ => Refused ()"),
        ).replace(
            &format!("{indent}Foreign.Returned(Foreign.Retained(())) => Retained(state, ())\n{indent}Foreign.Returned(Foreign.BlockedDependent) => Retained(state, ())\n{indent}Foreign.ConversionFailed(_) => Retained(state, ())"),
            &format!("{indent}_ => Retained(state, ())"),
        );
    }
    // A refused ordinary read unwinds the still-unquarantined sibling guard.
    // Its host destructor may run before the retained child: neither sibling
    // depends on the other, and their shared parent remains protected.
    generated_owner_execution_with_native(
        &owner,
        "import owner as Owner\nmain : Unit -> Owner.Scope<Unit, Unit, Owner.Scope<Unit, Unit, Owner.Scope<Unit, Unit, Int>>>\nmain () = resource Owner.Parent<P> parent = 64 {\n    resource Owner.Sibling<P, R> sibling = (parent, 4) {\n        resource Owner.Child<P, T> child = (parent, 5) {\n            5\n        }\n    }\n}\n",
        None,
        Err("executable foreign binding or conversion contract failed"),
        "parent-acquire:64\nchild-acquire:4\nchild-acquire:5\nchild-retain:5\nchild-release:4\nparent-final-byte:0\nchild-release:5\nparent-final-byte:0\nparent-release:64\n",
        include_str!("fixtures/source-owner/native_dependent_owner.c"),
    );
}

#[test]
fn generated_dependent_consumed_child_restores_parent_close_readiness() {
    generated_owner_program_with_native(
        &dependent_owner_with_consumed_finish(),
        "import owner as Owner\nmain : Unit -> Owner.Scope<Unit, Unit, Int>\nmain () = resource Owner.Parent<ParentFresh> parent = 64 {\n    let child_report = resource Owner.Child<ParentFresh, ChildFresh> child = (parent, 4) {\n        Owner.child_read child\n    }\n    let state : Owner.ParentState<ParentFresh> = Owner.borrow parent\n    64\n}\n",
        None,
        "Completed(64, Closed)",
        "parent-acquire:64\nchild-acquire:4\nchild-release:4\nparent-final-byte:0\nparent-release:64\n",
        include_str!("fixtures/source-owner/native_dependent_owner.c"),
    );
}

#[test]
fn generated_dependent_retained_child_revokes_ordinary_parent_access() {
    generated_owner_execution_with_native(
        include_str!("fixtures/source-owner/dependent_owner.ash"),
        "import owner as Owner\nmain : Unit -> Owner.Scope<Unit, Unit, Int>\nmain () = resource Owner.Parent<ParentFresh> parent = 64 {\n    let child_report = resource Owner.Child<ParentFresh, ChildFresh> child = (parent, 4) {\n        Owner.child_read child\n    }\n    let state : Owner.ParentState<ParentFresh> = Owner.borrow parent\n    64\n}\n",
        None,
        Err("runtime machine control state is inconsistent"),
        "parent-acquire:64\nchild-acquire:4\nchild-retain:4\nchild-release:4\nparent-final-byte:0\nparent-release:64\n",
        include_str!("fixtures/source-owner/native_dependent_owner.c"),
    );
}

#[test]
fn generated_dependent_incomplete_host_destruction_does_not_close_parent_or_retry() {
    let owner = include_str!("fixtures/source-owner/dependent_owner.ash").replace(
        "name \"ash_child_release\"\n        abi (pointer(Address), pointer(ParentBytes)) -> void\n        operand 0 from 0 current\n        operand 1 from 1 enclosing\n        retained_dependents block\n        outcome otherwise { consumed 0 }",
        "name \"ash_child_release\"\n        abi (pointer(Address), pointer(ParentBytes)) -> void\n        operand 0 from 0 current\n        operand 1 from 1 enclosing\n        retained_dependents block\n        outcome otherwise { retained 0 }",
    );
    let native = include_str!("fixtures/source-owner/native_dependent_owner.c").replace(
        "record(\"child-release\", child->identity);\n    record(\"parent-final-byte\", parent->bytes[0]);\n    parent->children -= 1;\n    free(child);",
        "record(\"host-child-retain\", child->identity);",
    );
    generated_owner_execution_with_native(
        &owner,
        "import owner as Owner\nmain : Unit -> Owner.Scope<Unit, Unit, Owner.Scope<Unit, Unit, Int>>\nmain () = resource Owner.Parent<ParentFresh> parent = 64 {\n    resource Owner.Child<ParentFresh, ChildFresh> child = (parent, 4) {\n        Owner.child_read child\n    }\n}\n",
        None,
        Err("source resource completion failed"),
        "parent-acquire:64\nchild-acquire:4\nchild-retain:4\nhost-child-retain:4\n",
        &native,
    );
}

#[test]
fn generated_dependent_discard_retained_closure_is_terminal_before_outer_finish() {
    // The discarded child still uses the scope codec. Its parent report is
    // never observed; acquired_only removes unused outer report metadata while
    // preserving required parent lifetime/completion and the fixed image budget.
    let owner = include_str!("fixtures/source-owner/dependent_owner.ash");
    let split = owner.find("pub interface ChildProvider").unwrap();
    let parent = owner[..split]
        .replace(
            "pub type Acquire<",
            "pub type Outcome<T> = Success(T)\n    | Failure(Unit)\n\npub type Acquire<",
        )
        .replace(
            "result Scope<Unit, Unit, Answer> for <Answer>",
            "result Outcome<Answer> for <Answer>",
        )
        .replace("codec scope", "codec acquired_only")
        .replace(
            "    read : Access -> Int ! {ParentOps<Access, State>}\n",
            "",
        )
        .replace("    read : Access -> Int\n", "")
        .replace("        read access => resume data\n", "")
        .replace(
            "        let marked = Foreign.byte_write (state, 0, 99)\n",
            "",
        );
    let owner = format!("{parent}{}", &owner[split..]);
    generated_owner_execution_with_native(
        &owner,
        "import owner as Owner\neffect Pause {\n    pause : Unit -> Unit\n}\nmain : Unit -> Int\nmain () = handle {\n    let abandoned = resource Owner.Parent<ParentFresh> parent = 64 {\n        resource Owner.Child<ParentFresh, ChildFresh> child = (parent, 4) {\n            let paused = perform Pause.pause ()\n            123\n        }\n    }\n    111\n} with Pause {\n    pause ignored => {\n        let closed = discard\n        84\n    }\n}\n",
        None,
        Err("source resource completion failed"),
        "parent-acquire:64\nchild-acquire:4\nchild-retain:4\nchild-release:4\nparent-final-byte:0\nparent-release:64\n",
        include_str!("fixtures/source-owner/native_dependent_owner.c"),
    );
}

fn owner_with_retained_finish() -> String {
    include_str!("fixtures/source-owner/owner.ash")
        .replace("    symbol Free<", "    symbol Hold<Before : EffectRow, R, After : EffectRow> : State<R> -> Foreign.Call<Foreign.Disposition<Unit>> {\n        name \"ash_owner_hold\"\n        abi (pointer(Address)) -> void\n        operand 0 from 0 current\n        retained_dependents block\n        outcome otherwise { retained 0 }\n    }\n    symbol Free<")
        .replace("interpret Allocate<{| Before}, R, {| After}>, Free<", "interpret Allocate<{| Before}, R, {| After}>, Hold<")
        .replace("match perform Free<", "match perform Hold<")
}

fn native_with_retained_finish() -> String {
    format!(
        "{}\nvoid ash_owner_hold(struct ash_owner *owner) {{ record(\"retain\", owner->size); }}\n",
        include_str!("fixtures/source-owner/native_owner.c")
    )
}

#[test]
fn generated_source_owner_retained_finish_uses_separate_host_destructor() {
    let owner = owner_with_retained_finish();
    let native = native_with_retained_finish();
    generated_owner_program_with_native(
        &owner,
        "import owner as Owner\nmain : Unit -> Owner.Scope<Unit, Unit, Int>\nmain () = resource Owner.Probe<{}, Fresh, {}> owner = 42 {\n    Owner.read owner\n}\n",
        None,
        "Completed(42, RetainedError(()))",
        "acquire:42\nretain:42\nrelease:42\n",
        &native,
    );
}

#[test]
fn generated_source_owner_retained_failure_on_discard_is_terminal() {
    generated_owner_execution_with_native(
        &owner_with_retained_finish(),
        "import owner as Owner\neffect Pause {\n    pause : Unit -> Unit\n}\nmain : Unit -> Int\nmain () = handle {\n    let abandoned = resource Owner.Probe<{}, Fresh, {}> owner = 42 {\n        let paused = perform Pause.pause ()\n        Owner.read owner\n    }\n    111\n} with Pause {\n    pause ignored => {\n        let closed = discard\n        84\n    }\n}\n",
        None,
        Err("source resource completion failed"),
        "acquire:42\nretain:42\nrelease:42\n",
        &native_with_retained_finish(),
    );
}

#[test]
fn source_owner_outward_capture_and_resume_is_admitted() {
    let fixture = Fixture::new(
        "import owner as Owner\neffect Pause {\n    pause : Unit -> Unit\n}\nmain : Unit -> Owner.Scope<Unit, Unit, Int>\nmain () = handle (resource Owner.Probe<{}, Fresh, {}> owner = 42 {\n    let paused = perform Pause.pause ()\n    Owner.read owner\n}) with Pause {\n    pause ignored => resume ()\n}\n",
    );
    compile_path(fixture.configuration())
        .expect("outward capture/resume must preserve the same source owner activation");
}

#[test]
fn generated_source_owner_outward_resume_moves_the_same_guard() {
    generated_owner_program_with_helpers(
        include_str!("fixtures/source-owner/owner.ash"),
        "import owner as Owner\neffect Pause {\n    pause : Unit -> Unit\n}\nmain : Unit -> Owner.Scope<Unit, Unit, Int>\nmain () = handle (resource Owner.Probe<{}, Fresh, {}> owner = 42 {\n    let paused = perform Pause.pause ()\n    Owner.read owner\n}) with Pause {\n    pause ignored => resume ()\n}\n",
        None,
        "Completed(42, Closed)",
        "acquire:42\nrelease:42\n",
    );
}

#[test]
fn generated_source_owner_owned_discard_finishes_without_scope_report() {
    let owner = include_str!("fixtures/source-owner/byte_owner.ash")
        .replace("finish (state, data) => match perform Free", "finish (state, data) => {\n        let marked = Foreign.byte_write (state, 0, 99)\n        match perform Free")
        .replace("    handlers (state, data)", "    }\n    handlers (state, data)");
    let native = include_str!("fixtures/source-owner/native_bytes.c").replace(
        "record(\"release\", owner->identity);",
        "record(\"release\", owner->identity);\n    record(\"final-byte\", owner->bytes[0]);",
    );
    generated_owner_program_with_native(
        &owner,
        "import owner as Owner\neffect Pause {\n    pause : Unit -> Unit\n}\nmain : Unit -> Int\nmain () = handle {\n    let abandoned = resource Owner.Probe<{}, Fresh, {}> owner = (42, 7) {\n        let paused = perform Pause.pause ()\n        Owner.read (owner, 0)\n    }\n    111\n} with Pause {\n    pause ignored => {\n        let closed = discard\n        84\n    }\n}\n",
        None,
        "84",
        "acquire:42\nrelease:42\nfinal-byte:99\n",
        &native,
    );
}

fn owner_with_outward_finish() -> String {
    format!("{}\n{}", include_str!("fixtures/source-owner/owner.ash")
        .replace("finish (state, data) => match perform Free", "finish (state, data) => {\n        let noticed = perform Notice.notice data\n        match perform Free")
        .replace("    handlers (state, data)", "    }\n    handlers (state, data)"),
        "pub effect Notice {\n    notice : Int -> Unit\n}\n")
}

#[test]
fn source_owner_outward_finish_requires_its_outside_interpreter() {
    let owner = owner_with_outward_finish();
    let positive = "import owner as Owner\neffect Pause {\n    pause : Unit -> Unit\n}\nmain : Unit -> Int\nmain () = handle (handle {\n    let abandoned = resource Owner.Probe<{}, Fresh, {}> owner = 42 {\n        let paused = perform Pause.pause ()\n        Owner.read owner\n    }\n    111\n} with Pause {\n    pause ignored => {\n        let closed = discard\n        84\n    }\n}) with Owner.Notice {\n    notice label => resume ()\n}\n";
    let fixture = Fixture::new(positive);
    fs::write(fixture.0.join("owner.ash"), &owner).unwrap();
    compile_path(fixture.configuration())
        .expect("required finish interpreter remains outside the cut");
    let negative = "import owner as Owner\neffect Pause {\n    pause : Unit -> Unit\n}\nmain : Unit -> Int\nmain () = handle (handle {\n    let abandoned = resource Owner.Probe<{}, Fresh, {}> owner = 42 {\n        let paused = perform Pause.pause ()\n        Owner.read owner\n    }\n    111\n} with Owner.Notice {\n    notice label => resume ()\n}) with Pause {\n    pause ignored => {\n        let closed = discard\n        84\n    }\n}\n";
    fs::write(fixture.0.join("entry.ash"), negative).unwrap();
    let error = compile_path(fixture.configuration())
        .expect_err("discard cannot skip the required finish interpreter");
    println!(
        "required interpreter refusal: {} {:?}",
        error.reason_code(),
        error.pipeline_failure()
    );
    assert_eq!(error.reason_code(), "effect.row-union-ambiguous");
}

#[test]
fn generated_source_owner_outward_finish_resumes_in_its_outside_interpreter() {
    generated_owner_program(
        &owner_with_outward_finish(),
        "import owner as Owner\neffect Pause {\n    pause : Unit -> Unit\n}\nmain : Unit -> Int\nmain () = handle (handle {\n    let abandoned = resource Owner.Probe<{}, Fresh, {}> owner = 42 {\n        let paused = perform Pause.pause ()\n        Owner.read owner\n    }\n    111\n} with Pause {\n    pause ignored => {\n        let closed = discard\n        84\n    }\n}) with Owner.Notice {\n    notice label => resume ()\n}\n",
        "84",
        "acquire:42\nrelease:42\n",
    );
}

#[test]
fn generated_source_owner_consumed_failure_on_discard_is_terminal() {
    let owner = include_str!("fixtures/source-owner/owner.ash").replace(
        "Foreign.Returned(Foreign.Consumed(())) => Consumed",
        "Foreign.Returned(Foreign.Consumed(())) => ConsumedFailure ()",
    );
    generated_owner_execution_with_native(
        &owner,
        "import owner as Owner\neffect Pause {\n    pause : Unit -> Unit\n}\nmain : Unit -> Int\nmain () = handle {\n    let abandoned = resource Owner.Probe<{}, Fresh, {}> owner = 42 {\n        let paused = perform Pause.pause ()\n        Owner.read owner\n    }\n    111\n} with Pause {\n    pause ignored => {\n        let closed = discard\n        84\n    }\n}\n",
        None,
        Err("source resource completion failed"),
        "acquire:42\nrelease:42\n",
        include_str!("fixtures/source-owner/native_owner.c"),
    );
}

#[test]
fn generated_source_owner_normal_consumed_error_remains_a_scope_report() {
    let owner = include_str!("fixtures/source-owner/owner.ash").replace(
        "Foreign.Returned(Foreign.Consumed(())) => Consumed",
        "Foreign.Returned(Foreign.Consumed(())) => ConsumedFailure ()",
    );
    generated_owner_program(
        &owner,
        "import owner as Owner\nmain : Unit -> Owner.Scope<Unit, Unit, Int>\nmain () = resource Owner.Probe<{}, Fresh, {}> owner = 42 {\n    Owner.read owner\n}\n",
        "Completed(42, ConsumedError(()))",
        "acquire:42\nrelease:42\n",
    );
}

fn outer_owner_write_only() -> String {
    include_str!("fixtures/source-owner/byte_owner.ash")
        .replace("    read : (Access, Int) -> Foreign.Call<Int> ! {ProbeOps<Access>}\n", "")
        .replace("    read : (Access, Int) -> Foreign.Call<Int>\n", "")
        .replace("        read (access, index) => {\n            let read_byte = match index == 0 {\n                true => Foreign.byte_read\n                false => Foreign.byte_read\n            }\n            resume read_byte (state, index)\n        }\n", "")
}

#[test]
fn source_owner_distinct_originals_with_same_spelling_survive_control_checking() {
    let fixture = Fixture::new(
        "import owner as Owner\nimport helpers as Inner\neffect Pause {\n    pause : Unit -> Unit\n}\nmain : Unit -> Owner.Scope<Unit, Unit, Int>\nmain () = resource Owner.Probe<{}, Outer, {}> outer = (64, 7) {\n    handle (handle {\n        let abandoned = resource Inner.Probe<{}, Fresh, {}> inner = 42 {\n            let paused = perform Pause.pause ()\n            Inner.read inner\n        }\n        111\n    } with Pause {\n        pause ignored => {\n            let closed = discard\n            84\n        }\n    }) with Inner.Notice {\n        notice label => {\n            let marked = Owner.write (outer, 0, 99)\n            resume ()\n        }\n    }\n}\n",
    );
    fs::write(fixture.0.join("owner.ash"), outer_owner_write_only()).unwrap();
    fs::write(fixture.0.join("helpers.ash"), owner_with_outward_finish()).unwrap();
    compile_path(fixture.configuration()).expect(
        "both original Probe headers and exact copied control rows survive independent Core",
    );
}

#[test]
fn generated_source_owner_discard_keeps_the_needed_outer_owner_live() {
    let owner = format!("{}\npub effect Notice {{\n    notice : Int -> Unit\n}}\n", outer_owner_write_only()
        .replace("finish (state, data) => match perform Free", "finish (state, data) => {\n        let noticed = perform Notice.notice data\n        match perform Free")
        .replace("    handlers (state, data)", "    }\n    handlers (state, data)"));
    let native = include_str!("fixtures/source-owner/native_bytes.c").replace(
        "record(\"release\", owner->identity);",
        "record(\"release\", owner->identity);\n    record(\"final-byte\", owner->bytes[0]);",
    );
    generated_owner_program_with_native(
        &owner,
        "import owner as Owner\neffect Pause {\n    pause : Unit -> Unit\n}\nmain : Unit -> Owner.Scope<Unit, Unit, Int>\nmain () = handle (resource Owner.Probe<{}, Outer, {}> outer = (64, 7) {\n    handle (handle {\n        let abandoned = resource Owner.Probe<{}, Inner, {}> inner = (42, 7) {\n            let paused = perform Pause.pause ()\n            Owner.write (inner, 0, 11)\n        }\n        111\n    } with Pause {\n        pause ignored => {\n            let closed = discard\n            84\n        }\n    }) with Owner.Notice {\n        notice label => {\n            let marked = Owner.write (outer, 0, 99)\n            resume ()\n        }\n    }\n}) with Owner.Notice {\n    notice label => resume ()\n}\n",
        None,
        "Completed(84, Closed)",
        "acquire:64\nacquire:42\nrelease:42\nfinal-byte:5\nrelease:64\nfinal-byte:99\n",
        &native,
    );
}

#[test]
fn generated_source_owner_owned_discard_finishes_nested_guards_in_order() {
    let owner = outer_owner_write_only()
        .replace("finish (state, data) => match perform Free", "finish (state, data) => {\n        let marked = Foreign.byte_write (state, 0, 99)\n        match perform Free")
        .replace("    handlers (state, data)", "    }\n    handlers (state, data)");
    let native = include_str!("fixtures/source-owner/native_bytes.c").replace(
        "record(\"release\", owner->identity);",
        "record(\"release\", owner->identity);\n    record(\"final-byte\", owner->bytes[0]);",
    );
    generated_owner_program_with_native(
        &owner,
        "import owner as Owner\neffect Pause {\n    pause : Unit -> Unit\n}\nmain : Unit -> Int\nmain () = handle {\n    let abandoned = resource Owner.Probe<{}, Outer, {}> outer = (64, 7) {\n        resource Owner.Probe<{}, Inner, {}> inner = (42, 7) {\n            let paused = perform Pause.pause ()\n            Owner.write (inner, 0, 11)\n        }\n    }\n    111\n} with Pause {\n    pause ignored => {\n        let closed = discard\n        84\n    }\n}\n",
        None,
        "84",
        "acquire:64\nacquire:42\nrelease:42\nfinal-byte:99\nrelease:64\nfinal-byte:99\n",
        &native,
    );
}

#[test]
fn generated_source_owner_acquisition_discard_revokes_only_the_unpublished_guard() {
    let owner = outer_owner_write_only()
        .replace("false => Acquired(state, size)", "false => {\n                let paused = perform Pause.pause ()\n                Acquired(state, size)\n            }")
        .replace("finish (state, data) => match perform Free", "finish (state, data) => {\n        let marked = Foreign.byte_write (state, 0, 99)\n        match perform Free")
        .replace("    handlers (state, data)", "    }\n    handlers (state, data)");
    let owner = format!("{owner}\npub effect Pause {{\n    pause : Unit -> Unit\n}}\n");
    let native = include_str!("fixtures/source-owner/native_bytes.c").replace(
        "record(\"release\", owner->identity);",
        "record(\"release\", owner->identity);\n    record(\"final-byte\", owner->bytes[0]);",
    );
    generated_owner_program_with_native(
        &owner,
        "import owner as Owner\nmain : Unit -> Int\nmain () = handle {\n    let abandoned = resource Owner.Probe<{}, R, {}> owner = (42, 7) {\n        Owner.write (owner, 0, 11)\n    }\n    111\n} with Owner.Pause {\n    pause ignored => {\n        let closed = discard\n        84\n    }\n}\n",
        None,
        "84",
        "acquire:42\nrelease:42\nfinal-byte:5\n",
        &native,
    );
}

#[test]
fn generated_source_owner_acquisition_discard_before_allocation_makes_no_native_call() {
    let owner = outer_owner_write_only()
        .replace("acquire (size, extent) => match perform Allocate", "acquire (size, extent) => {\n        let paused = perform Pause.pause ()\n        match perform Allocate")
        .replace("    finish (state, data)", "    }\n    finish (state, data)");
    let owner = format!("{owner}\npub effect Pause {{\n    pause : Unit -> Unit\n}}\n");
    generated_owner_program_with_native(
        &owner,
        "import owner as Owner\nmain : Unit -> Int\nmain () = handle {\n    let abandoned = resource Owner.Probe<{}, R, {}> owner = (42, 7) {\n        Owner.write (owner, 0, 11)\n    }\n    111\n} with Owner.Pause {\n    pause ignored => {\n        let closed = discard\n        84\n    }\n}\n",
        None,
        "84",
        "",
        include_str!("fixtures/source-owner/native_bytes.c"),
    );
}

#[test]
fn generated_source_owner_capture_during_acquisition_moves_the_pending_guard() {
    let owner = include_str!("fixtures/source-owner/owner.ash")
        .replace("false => Acquired(state, size)", "false => {\n                let paused = perform Pause.pause ()\n                Acquired(state, size)\n            }");
    let owner = format!("{owner}\npub effect Pause {{\n    pause : Unit -> Unit\n}}\n");
    generated_owner_program(
        &owner,
        "import owner as Owner\nmain : Unit -> Owner.Scope<Unit, Unit, Int>\nmain () = handle (resource Owner.Probe<{}, Fresh, {}> owner = 42 {\n    Owner.read owner\n}) with Owner.Pause {\n    pause ignored => resume ()\n}\n",
        "Completed(42, Closed)",
        "acquire:42\nrelease:42\n",
    );
}

#[test]
fn source_owner_running_finish_cannot_be_discarded() {
    let fixture = Fixture::new(
        "import owner as Owner\nmain : Unit -> Int\nmain () = handle {\n    let abandoned = resource Owner.Probe<{}, Fresh, {}> owner = 42 {\n        Owner.read owner\n    }\n    111\n} with Owner.Notice {\n    notice label => {\n        let closed = discard\n        84\n    }\n}\n",
    );
    fs::write(fixture.0.join("owner.ash"), owner_with_outward_finish()).unwrap();
    let error =
        compile_path(fixture.configuration()).expect_err("running finish is nonabandonable");
    println!(
        "running finish refusal: {} {:?}",
        error.reason_code(),
        error.pipeline_failure()
    );
    assert_eq!(error.reason_code(), "effect.discard-unsafe");
}

#[test]
fn source_resource_lifecycle_compiles_from_original_checked_templates() {
    let fixture = Fixture::new(include_str!("fixtures/source-owner/entry.ash"));
    let compiled =
        compile_path(fixture.configuration()).expect("complete source owner/resource admission");
    println!(
        "source owner compilation work: {:?}",
        compiled.compilation_work()
    );
}

#[test]
fn initialized_owner_byte_read_compiles_through_public_source_admission() {
    let fixture = Fixture::new(include_str!("fixtures/source-owner/entry.ash"));
    let owner = include_str!("fixtures/source-owner/owner.ash")
        .replace("repr Address = opaque", "repr Address = bytes")
        .replace(
            "outcome result nonnull { readable result }",
            "outcome result nonnull { readable result, initialized_bytes result from 0 }",
        )
        .replace(
            "read access => resume data",
            "read access => match Foreign.byte_read (state, 0) {\n            Foreign.Returned(byte) => resume byte\n            Foreign.ConversionFailed(_) => resume 0\n        }",
        );
    fs::write(fixture.0.join("owner.ash"), owner).unwrap();
    compile_path(fixture.configuration()).expect("initialized byte access source admission");
}

#[test]
fn byte_primitives_reject_arbitrary_state_arguments_in_independent_core() {
    for entry in [
        "import @builtin.foreign as Foreign\nmain : Unit -> Foreign.Call<Int>\nmain () = Foreign.byte_read (7, 0)\n",
        "import @builtin.foreign as Foreign\nmain : Unit -> Foreign.Call<Unit>\nmain () = Foreign.byte_write (7, 0, 255)\n",
        "import @builtin.foreign as Foreign\nhelper<S> : (S, Int) -> Foreign.Call<Int>\nhelper pair = Foreign.byte_read pair\nmain : Unit -> Int\nmain () = 42\n",
    ] {
        let fixture = Fixture::new(entry);
        let failure = compile_path(fixture.configuration()).unwrap_err();
        assert!(
            matches!(failure, ash::driver::FileFailure::Pipeline(ref diagnostic)
            if matches!(diagnostic.failure(), ash::driver::PipelineFailure::Validation(_))),
            "arbitrary S must reach independent Core rejection: {failure:?}"
        );
    }
}

#[test]
fn byte_callable_alias_compiles_with_original_call_lineage() {
    let fixture = Fixture::new(include_str!("fixtures/source-owner/byte_entry.ash"));
    fs::write(
        fixture.0.join("owner.ash"),
        include_str!("fixtures/source-owner/byte_owner.ash"),
    )
    .unwrap();
    compile_path(fixture.configuration())
        .expect("selected canonical alias and byte write admission");
}

#[test]
fn generated_byte_owner_reads_writes_and_refuses_without_mutation() {
    generated_owner_program_with_native(
        include_str!("fixtures/source-owner/byte_owner.ash"),
        include_str!("fixtures/source-owner/byte_entry.ash"),
        None,
        "Completed((5, 255, true, 255, false, 255, false, 255), Closed)",
        "acquire:42\nrelease:42\n",
        include_str!("fixtures/source-owner/native_bytes.c"),
    );
}

#[test]
fn generated_byte_owner_borrows_live_state_in_acquire_body_and_finish() {
    let owner = include_str!("fixtures/source-owner/byte_owner.ash")
        .replace("false => Acquired(state, size)", "false => match Foreign.byte_read (state, 0) {\n            Foreign.Returned(byte) => Acquired(state, byte)\n            Foreign.ConversionFailed(_) => Refused ()\n        }")
        .replace("finish (state, data) => match perform Free", "finish (state, data) => {\n        let restored = Foreign.byte_write (state, 0, data)\n        match perform Free")
        .replace("    handlers (state, data)", "    }\n    handlers (state, data)");
    let native = include_str!("fixtures/source-owner/native_bytes.c").replace(
        "record(\"release\", owner->identity);",
        "record(\"release\", owner->identity);\n    record(\"final-byte\", owner->bytes[0]);",
    );
    generated_owner_program_with_native(
        &owner,
        "import owner as Owner\nimport @builtin.foreign as Foreign\nmain : Unit -> Owner.Scope<Unit, Unit, Foreign.Call<Int>>\nmain () = resource Owner.Probe<{}, R, {}> owner = (42, 7) {\n    let written = Owner.write (owner, 0, 255)\n    Owner.read (owner, 0)\n}\n",
        None,
        "Completed(Returned(255), Closed)",
        "acquire:42\nrelease:42\nfinal-byte:5\n",
        &native,
    );
}

#[test]
fn generated_byte_owner_complete_actuals_nested_aliases_and_override_precedence() {
    let owner = include_str!("fixtures/source-owner/byte_owner.ash")
        .replace(
            "Before : EffectRow, R, After : EffectRow",
            "Before : EffectRow, Phantom, R, After : EffectRow",
        )
        .replace(
            "<{| Before}, R, {| After}>",
            "<{| Before}, Phantom, R, {| After}>",
        );
    let entry = include_str!("fixtures/source-owner/byte_generic_rows_entry.ash")
        .replace("Before : EffectRow, R, After : EffectRow", "Before : EffectRow, Phantom, R, After : EffectRow")
        .replace("<{| Before}, R, {| After}>", "<{| Before}, Phantom, R, {| After}>")
        .replace("<{| Before}, Inner, {| After}>", "<{| Before}, Phantom, Inner, {| After}>")
        .replace("<{Tag}, Outer, {}>", "<{Tag}, Int, Outer, {}>")
        .replace("Foreign.Call<Int>", "(Foreign.Call<Int>, Foreign.Call<Int>, Foreign.Call<Int>)")
        .replace("    Owner.read (inner, 0)", "    let first = Owner.read (inner, 0)\n    let overridden = handle (Owner.read (inner, 0)) with Owner.ProbeOps<Owner.Probe<{| Before}, Phantom, Inner, {| After}>> {\n        read (access, index) => resume Foreign.Returned 84\n        write (access, index, byte) => resume Foreign.Returned ()\n    }\n    let last = Owner.read (inner, 1)\n    (first, overridden, last)");
    // Both selected canonical alias branches execute under two different
    // phantom Type/Row applications of the same defining helper and template.
    // Those arguments are absent from the byte callable's State value type.
    let nested = "Owner.Scope<Unit, Unit, Owner.Scope<Unit, Unit, (Foreign.Call<Int>, Foreign.Call<Int>, Foreign.Call<Int>)>>";
    let entry = format!(
        "{}main : Unit -> ({nested}, {nested})\nmain () = {{\n    let first = resource Owner.Probe<{{Tag}}, Int, Outer, {{}}> outer = (42, 7) {{\n        within outer\n    }}\n    let second = resource Owner.Probe<{{}}, Unit, Other, {{}}> outer = (44, 7) {{\n        within outer\n    }}\n    (first, second)\n}}\n",
        entry.split("main :").next().unwrap()
    );
    generated_owner_program_with_native(
        &owner,
        &entry,
        None,
        "(Completed(Completed((Returned(5), Returned(84), Returned(255)), Closed), Closed), Completed(Completed((Returned(5), Returned(84), Returned(255)), Closed), Closed))",
        "acquire:42\nacquire:43\nrelease:43\nrelease:42\nacquire:44\nacquire:43\nrelease:43\nrelease:44\n",
        include_str!("fixtures/source-owner/native_bytes.c"),
    );
}

#[test]
fn generated_byte_owner_acquired_only_null_and_zero_extent_keep_result_and_release_shape() {
    let owner = include_str!("fixtures/source-owner/byte_owner.ash")
        .replace(
            "pub type Scope<I, E, T> = NotAcquired(I)\n    | Completed(T, Completion<E>)",
            "pub type Outcome<T> = Success(T)\n    | Failure(Unit)",
        )
        .replace(
            "result Scope<Unit, Unit, Answer> for <Answer>",
            "result Outcome<Answer> for <Answer>",
        )
        .replace("codec scope", "codec acquired_only");
    generated_owner_program_with_native(
        &owner,
        "import owner as Owner\nimport @builtin.foreign as Foreign\nread_result : Foreign.Call<Int> -> Int\nread_result value = match value {\n    Foreign.Returned(byte) => byte\n    Foreign.ConversionFailed(_) => 999\n}\nmain : Unit -> (Owner.Outcome<Int>, Owner.Outcome<Int>)\nmain () = {\n    let null = resource Owner.Probe<{}, Null, {}> owner = (0, 7) {\n        read_result (Owner.read (owner, 0))\n    }\n    let zero = resource Owner.Probe<{}, Zero, {}> owner = (42, 0) {\n        read_result (Owner.read (owner, 0))\n    }\n    (null, zero)\n}\n",
        None,
        "(Failure(()), Success(999))",
        "acquire:0\nacquire:42\nrelease:42\n",
        include_str!("fixtures/source-owner/native_bytes.c"),
    );
}

#[test]
fn generated_owner_host_acquires_publishes_private_payload_and_releases_once() {
    generated_owner_case(include_str!("fixtures/source-owner/owner.ash"));
}

#[test]
fn generated_source_provider_methods_preserve_association_and_lexical_forwarding() {
    // Method and operation declaration orders differ. Ordinary interface calls
    // must select their exact checked operation and retain its typed operands.
    generated_owner_program(
        include_str!("fixtures/source-owner/forwarding_owner.ash"),
        include_str!("fixtures/source-owner/forwarding_entry.ash"),
        "Completed((42, 1), Closed)",
        "acquire:42\nrelease:42\n",
    );
}

#[test]
fn generated_source_provider_helpers_retain_evidence_and_ordinary_precedence() {
    let owner = include_str!("fixtures/source-owner/forwarding_owner.ash");
    let helpers = include_str!("fixtures/source-owner/forwarding_helpers.ash");
    generated_owner_program_with_helpers(
        owner,
        include_str!("fixtures/source-owner/forwarding_helper_entry.ash"),
        Some(helpers),
        "Completed((42, 5), Closed)",
        "acquire:42\nrelease:42\n",
    );
    generated_owner_program_with_helpers(
        owner,
        include_str!("fixtures/source-owner/forwarding_override_entry.ash"),
        Some(helpers),
        "Completed((42, (84, 105), 42), Closed)",
        "acquire:42\nrelease:42\n",
    );
}

#[test]
fn generated_source_provider_repeated_and_nested_activations_keep_unique_owners() {
    let owner = include_str!("fixtures/source-owner/forwarding_owner.ash");
    generated_owner_program(
        owner,
        include_str!("fixtures/source-owner/forwarding_repeated_entry.ash"),
        "(Completed((42, 5), Closed), Completed((8, 5), Closed), NotAcquired(()), NotAcquired(()))",
        "acquire:42\nrelease:42\nacquire:8\nrelease:8\nacquire:0\nacquire:9\nrelease:9\n",
    );
    generated_owner_program(
        owner,
        include_str!("fixtures/source-owner/forwarding_nested_entry.ash"),
        "Completed((64, Completed((4, 3), Closed), 64), Closed)",
        "acquire:64\nacquire:4\nrelease:4\nrelease:64\n",
    );
}

#[test]
fn generated_source_provider_wrapped_access_restores_through_generic_helpers() {
    let owner = include_str!("fixtures/source-owner/forwarding_owner.ash")
        .replace(
            "pub interface ProbeProvider",
            "pub type Wrapped<T> = Wrapped(T)\n\npub interface ProbeProvider",
        )
        .replace("read : Access -> Int", "read : Wrapped<Access> -> Int")
        .replace(
            "read access => resume data",
            "read Wrapped(access) => resume data",
        );
    generated_owner_program(
        &owner,
        include_str!("fixtures/source-owner/forwarding_wrapped_entry.ash"),
        "Completed((42, 5), Closed)",
        "acquire:42\nrelease:42\n",
    );
    generated_owner_program_with_helpers(
        &owner,
        include_str!("fixtures/source-owner/forwarding_helper_entry.ash"),
        Some(include_str!(
            "fixtures/source-owner/forwarding_wrapped_helpers.ash"
        )),
        "Completed((42, 5), Closed)",
        "acquire:42\nrelease:42\n",
    );
}

#[test]
fn generated_source_provider_forwarding_preserves_acquired_only_report() {
    let owner = include_str!("fixtures/source-owner/forwarding_owner.ash")
        .replace(
            "pub type Scope<I, E, T> = NotAcquired(I)\n    | Completed(T, Completion<E>)",
            "pub type Outcome<T> = Success(T)\n    | Failure(Unit)",
        )
        .replace(
            "result Scope<Unit, Unit, Answer> for <Answer>",
            "result Outcome<Answer> for <Answer>",
        )
        .replace("codec scope", "codec acquired_only");
    let entry = include_str!("fixtures/source-owner/forwarding_entry.ash").replace(
        "Owner.Scope<Unit, Unit, (Int, Int)>",
        "Owner.Outcome<(Int, Int)>",
    );
    generated_owner_program(
        &owner,
        &entry,
        // Constructor Display renders its tuple payload's fields inside the
        // constructor parentheses; the checked report still has one tuple field.
        "Success(42, 1)",
        "acquire:42\nrelease:42\n",
    );
}

#[test]
fn generated_source_provider_complete_rows_preserve_frozen_metadata() {
    generated_owner_program(
        include_str!("fixtures/source-owner/forwarding_owner.ash"),
        include_str!("fixtures/source-owner/forwarding_generic_rows_entry.ash"),
        "Completed(Completed((4, 5), Closed), Closed)",
        "acquire:42\nacquire:4\nrelease:4\nrelease:42\n",
    );
}

#[test]
fn generated_initialized_byte_owner_host_preserves_native_acquisition_and_release() {
    // The native fixture initializes one eight-byte size_t object. Seven bytes
    // therefore form a valid promised region, independent of its stored value.
    let owner = include_str!("fixtures/source-owner/owner.ash")
        .replace("repr Address = opaque", "repr Address = bytes")
        .replace(
            ": Int -> Foreign.Call<Foreign.Output<Foreign.Nullable<State<R>>>>",
            ": (Int, Int) -> Foreign.Call<Foreign.Output<Foreign.Nullable<State<R>>>>",
        )
        .replace(
            "outcome result nonnull { readable result }",
            "outcome result nonnull { readable result, initialized_bytes result from 1 }",
        )
        .replace(".call size {", ".call (size, 7) {");
    generated_owner_case(&owner);
    // A zero initialized extent still owns a non-null native allocation.
    generated_owner_case(&owner.replace(".call (size, 7) {", ".call (size, 0) {"));
}

#[test]
fn initialized_byte_resource_without_initialization_fact_is_rejected() {
    let fixture = Fixture::new(include_str!("fixtures/source-owner/entry.ash"));
    let owner = include_str!("fixtures/source-owner/owner.ash")
        .replace("repr Address = opaque", "repr Address = bytes");
    fs::write(fixture.0.join("owner.ash"), owner).unwrap();
    let failure = compile_path(fixture.configuration()).unwrap_err();
    assert_eq!(failure.reason_code(), "foreign.contract");
}

#[test]
fn generated_initialized_byte_extents_refuse_before_native_owner_entry() {
    let owner = include_str!("fixtures/source-owner/owner.ash")
        .replace("repr Address = opaque", "repr Address = bytes")
        .replace(
            ": Int -> Foreign.Call<Foreign.Output<Foreign.Nullable<State<R>>>>",
            ": (Int, Int) -> Foreign.Call<Foreign.Output<Foreign.Nullable<State<R>>>>",
        )
        .replace(
            "outcome result nonnull { readable result }",
            "outcome result nonnull { readable result, initialized_bytes result from 1 }",
        )
        .replace("input Int", "input (Int, Int)")
        .replace("acquire size =>", "acquire (size, extent) =>")
        .replace(".call size {", ".call (size, extent) {");
    let entry = r#"import @builtin.foreign as Foreign
import owner as Owner
foreign library Inputs {
    profile "x86_64-unknown-linux-gnu"
    repr Signed = signed(64)
    symbol NegativeInput : Unit -> Foreign.Call<Int> {
        name "ash_owner_negative_input"
        abi () -> Signed
        output result as scalar
        outcome otherwise { readable result }
    }
}
unreachable : Unit -> Int
unreachable () = unreachable ()
probe : Int -> Owner.Scope<Unit, Unit, Int>
probe extent = resource Owner.Probe<{}, Fresh, {}> owner = (42, extent) {
    unreachable ()
}
main : Unit -> (Owner.Scope<Unit, Unit, Int>, Owner.Scope<Unit, Unit, Int>) ! {NegativeInput}
main () = {
    let negative = match perform NegativeInput.call () {
        Foreign.Returned(value) => value
        Foreign.ConversionFailed(_) => 0
    }
    (probe negative, probe ((9223372036854775807 + 1) * 2))
}
"#;
    generated_owner_program(&owner, entry, "(NotAcquired(()), NotAcquired(()))", "");
}

fn generated_owner_case(owner: &str) {
    generated_owner_program(
        owner,
        include_str!("fixtures/source-owner/entry.ash"),
        "(Completed(42, Closed), Completed(8, Closed), NotAcquired(()), NotAcquired(()), Completed(Completed(4, Closed), Closed), Completed(84, Closed), NotAcquired(()))",
        "acquire:42\nrelease:42\nacquire:8\nrelease:8\nacquire:0\nacquire:9\nrelease:9\nacquire:64\nacquire:4\nrelease:4\nrelease:64\nacquire:7\nrelease:7\n",
    );
}

fn generated_owner_program(owner: &str, entry: &str, expected_result: &str, expected_trace: &str) {
    generated_owner_program_with_helpers(owner, entry, None, expected_result, expected_trace);
}

fn generated_owner_program_with_helpers(
    owner: &str,
    entry: &str,
    helpers: Option<&str>,
    expected_result: &str,
    expected_trace: &str,
) {
    generated_owner_program_with_native(
        owner,
        entry,
        helpers,
        expected_result,
        expected_trace,
        include_str!("fixtures/source-owner/native_owner.c"),
    );
}

fn generated_owner_program_with_native(
    owner: &str,
    entry: &str,
    helpers: Option<&str>,
    expected_result: &str,
    expected_trace: &str,
    native_source: &str,
) {
    generated_owner_execution_with_native(
        owner,
        entry,
        helpers,
        Ok(expected_result),
        expected_trace,
        native_source,
    );
}

fn generated_owner_execution_with_native(
    owner: &str,
    entry: &str,
    helpers: Option<&str>,
    expected_result: Result<&str, &str>,
    expected_trace: &str,
    native_source: &str,
) {
    let fixture = Fixture::new(entry);
    fs::write(fixture.0.join("owner.ash"), owner).unwrap();
    if let Some(helpers) = helpers {
        fs::write(fixture.0.join("helpers.ash"), helpers).unwrap();
    }
    let compiled = compile_path(fixture.configuration()).unwrap();
    println!(
        "forwarding/native compilation work: {:?}",
        compiled.compilation_work()
    );
    let native = fixture.0.join("native_owner.c");
    let object = fixture.0.join("native_owner.o");
    let archive = fixture.0.join("libash_owner.a");
    fs::write(&native, native_source).unwrap();
    for output in [
        Command::new("cc")
            .args(["-std=c11", "-Wall", "-Wextra", "-Werror", "-c"])
            .arg(&native)
            .arg("-o")
            .arg(&object)
            .output()
            .unwrap(),
        Command::new("ar")
            .arg("crs")
            .arg(&archive)
            .arg(&object)
            .output()
            .unwrap(),
    ] {
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
    // The generated host restores checked Core; it does not reopen Ash source.
    fs::remove_file(fixture.0.join("entry.ash")).unwrap();
    fs::remove_file(fixture.0.join("owner.ash")).unwrap();
    if helpers.is_some() {
        fs::remove_file(fixture.0.join("helpers.ash")).unwrap();
    }
    let executable = fixture.0.join("program");
    let mut configuration = BuildConfiguration::new(executable.clone());
    configuration.native_inputs = vec![NativeLinkInput::StaticArchive(archive)];
    let cache = std::env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target"));
    configuration.cargo_target_directory = Some(cache.join("ffi-native-hosts"));
    let prepared = prepare_program(&compiled, configuration).unwrap();
    assert!(!prepared.generated_rust().contains("compile_path"));
    let rust_bytes = prepared.generated_rust().len();
    let preparation_work = prepared.preparation_work();
    let built = build_prepared(prepared).unwrap();
    let generated = built.generated_source().parent().unwrap();
    let image = generated.join("program-image.bin");
    let facts = generated.join("expected-facts.bin");
    println!(
        "owner/native preparation: rust_bytes={rust_bytes}, image_bytes={}, fact_bytes={}, work={preparation_work}",
        fs::metadata(&image).unwrap().len(),
        fs::metadata(&facts).unwrap().len(),
    );
    // Compilation embeds both exact payloads. Execution must require neither
    // Ash source nor files used to build the standalone host.
    fs::remove_file(image).unwrap();
    fs::remove_file(facts).unwrap();
    let trace = fixture.0.join("native-trace");
    let mut child = Command::new(executable)
        .env("ASH_OWNER_TRACE", &trace)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let started = Instant::now();
    while child.try_wait().unwrap().is_none() {
        if started.elapsed() > Duration::from_secs(30) {
            child.kill().unwrap();
            let _ = child.wait();
            panic!("owner fixture exceeded its 30-second execution deadline");
        }
        thread::sleep(Duration::from_millis(20));
    }
    let output = child.wait_with_output().unwrap();
    // Preserve the native-entry/cleanup frontier even when the child refuses
    // before the result assertions and fixture cleanup removes its files.
    let observed_trace = match fs::read_to_string(&trace) {
        Ok(trace) => trace,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => String::new(),
        Err(error) => panic!("cannot read native trace: {error}"),
    };
    println!("owner/native actual trace:\n{observed_trace}");
    match expected_result {
        Ok(expected) => {
            assert!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            assert_eq!(String::from_utf8(output.stdout).unwrap().trim(), expected);
        }
        Err(expected) => {
            assert!(
                !output.status.success(),
                "failed completion published success"
            );
            assert!(
                output.stdout.is_empty(),
                "failed completion published a report"
            );
            assert!(
                String::from_utf8_lossy(&output.stderr).contains(expected),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
        }
    }
    if expected_trace.is_empty() {
        assert!(
            !trace.exists(),
            "refused extents must not enter native owner code"
        );
    } else {
        assert_eq!(observed_trace, expected_trace);
    }
}

#[test]
fn generated_owner_calls_use_fixed_original_constants_in_all_native_phases() {
    let owner = include_str!("fixtures/source-owner/owner.ash")
        .replace("    repr Size = size_t", "    repr Size = size_t\n    repr Flag = signed(32)\n    const AllocateFlag : Flag = 7\n    const ReleaseFlag : Flag = -7")
        .replace("abi (Size) -> pointer(Address)", "abi (Size, Flag) -> pointer(Address)")
        .replace("operand 0 from 0 scalar", "operand 0 from 0 scalar\n        operand 1 from constant AllocateFlag")
        .replace("abi (pointer(Address)) -> void", "abi (pointer(Address), Flag) -> void")
        .replace("operand 0 from 0 current", "operand 0 from 0 current\n        operand 1 from constant ReleaseFlag");
    let native = include_str!("fixtures/source-owner/native_owner.c")
        .replace(
            "void *ash_owner_acquire(size_t size) {",
            "void *ash_owner_acquire(size_t size, int32_t flag) {\n    if (flag != 7) abort();",
        )
        .replace(
            "void ash_owner_release(void *raw) {",
            "void ash_owner_release(void *raw, int32_t flag) {\n    if (flag != -7) abort();",
        );
    generated_owner_program_with_native(
        &owner,
        "import owner as Owner\nmain : Unit -> (Owner.Scope<Unit, Unit, Int>, Owner.Scope<Unit, Unit, Int>)\nmain () = (resource Owner.Probe<{}, First, {}> owner = 42 {\n    Owner.read owner\n}, resource Owner.Probe<{}, Second, {}> owner = 9 {\n    Owner.read owner\n})\n",
        None,
        "(Completed(42, Closed), NotAcquired(()))",
        "acquire:42\nrelease:42\nacquire:9\nrelease:9\n",
        &native,
    );
}

#[test]
fn generated_owner_calls_use_noncallable_sentinels_in_all_native_phases() {
    let owner = include_str!("fixtures/source-owner/owner.ash")
        .replace("    repr Size = size_t", "    repr Size = size_t\n    repr Destructor = function_address\n    sentinel Transient : Destructor = all_bits_one")
        .replace("abi (Size) -> pointer(Address)", "abi (Size, Destructor) -> pointer(Address)")
        .replace("operand 0 from 0 scalar", "operand 0 from 0 scalar\n        operand 1 from constant Transient")
        .replace("abi (pointer(Address)) -> void", "abi (pointer(Address), Destructor) -> void")
        .replace("operand 0 from 0 current", "operand 0 from 0 current\n        operand 1 from constant Transient");
    let check = "uintptr_t bits = 0;\n    _Static_assert(sizeof(sentinel) == sizeof(bits), \"GNU64 function-address width\");\n    memcpy(&bits, &sentinel, sizeof(bits));\n    if (bits != UINTPTR_MAX) abort();";
    let native = format!(
        "#include <string.h>\n{}",
        include_str!("fixtures/source-owner/native_owner.c")
    )
    .replace(
        "void *ash_owner_acquire(size_t size) {",
        &format!("void *ash_owner_acquire(size_t size, void (*sentinel)(void *)) {{\n    {check}"),
    )
    .replace(
        "void ash_owner_release(void *raw) {",
        &format!("void ash_owner_release(void *raw, void (*sentinel)(void *)) {{\n    {check}"),
    );
    generated_owner_program_with_native(
        &owner,
        "import owner as Owner\nmain : Unit -> (Owner.Scope<Unit, Unit, Int>, Owner.Scope<Unit, Unit, Int>)\nmain () = (resource Owner.Probe<{}, First, {}> owner = 42 {\n    Owner.read owner\n}, resource Owner.Probe<{}, Second, {}> owner = 9 {\n    Owner.read owner\n})\n",
        None,
        "(Completed(42, Closed), NotAcquired(()))",
        "acquire:42\nrelease:42\nacquire:9\nrelease:9\n",
        &native,
    );
}

#[test]
fn lifecycle_payload_helper_identity_is_admitted() {
    // CP22 permits pure ordinary payload helpers. Native calls and State stay
    // in the descriptor's original lifecycle body.
    let fixture = Fixture::new(
        "import owner as Owner\nmain : Unit -> Owner.Scope<Unit, Int, Int>\nmain () = resource Owner.Probe<{}, Fresh, {}> owner = 42 {\n    Owner.read owner\n}\n",
    );
    let owner = include_str!("fixtures/source-owner/status_owner.ash").replace(
        "false => Acquired(state, size)",
        "false => Acquired(state, payload_copy size)",
    ) + "\npayload_copy<T> : T -> T\npayload_copy value = value\n";
    fs::write(fixture.0.join("owner.ash"), owner).unwrap();
    let result = compile_path(fixture.configuration());
    assert!(
        result.is_ok(),
        "independent payload-only helper admission: {:?}",
        result.err().and_then(|error| error
            .pipeline_failure()
            .map(|failure| format!("{failure:?}")))
    );
}

#[test]
fn lifecycle_payload_helpers_execute_local_and_imported_originals() {
    for imported in [false, true] {
        let (helper, prefix, suffix, helpers) = if imported {
            (
                "Payload.copy",
                "import helpers as Payload\n",
                "",
                Some("pub copy<Before : EffectRow, T> : T -> T ! {| Before}\ncopy value = value\n"),
            )
        } else {
            (
                "payload_copy",
                "",
                "\npayload_copy<Before : EffectRow, T> : T -> T ! {| Before}\npayload_copy value = value\n",
                None,
            )
        };
        let owner = include_str!("fixtures/source-owner/owner.ash")
            .replace("false => Acquired(state, size)", &format!("false => {{\n                let copy : Int -> Int = match size == 42 {{\n                    true => {helper}\n                    false => {helper}\n                }}\n                Acquired(state, copy (size + 1))\n            }}"))
            .replace("Foreign.Returned(Foreign.Consumed(())) => Consumed", &format!("Foreign.Returned(Foreign.Consumed(())) => {{\n            let copy : Int -> Int = {helper}\n            match copy data == data {{\n                true => Consumed\n                false => ConsumedFailure(())\n            }}\n        }}"));
        let owner = format!("{prefix}{owner}{suffix}");
        assert!(owner.contains("copy (size + 1)"));
        generated_owner_program_with_native(
            &owner,
            "import owner as Owner\nmain : Unit -> Owner.Scope<Unit, Unit, Int>\nmain () = resource Owner.Probe<{}, Fresh, {}> owner = 42 {\n    Owner.read owner\n}\n",
            helpers,
            "Completed(43, Closed)",
            "acquire:42\nrelease:42\n",
            include_str!("fixtures/source-owner/native_owner.c"),
        );
    }
}

#[test]
fn lifecycle_payload_helpers_do_not_transport_native_state() {
    for expression in [
        "Acquired(payload_copy state, size)",
        "{\n                let discarded = payload_ignore state\n                Acquired(state, size)\n            }",
    ] {
        let fixture = Fixture::new(
            "import owner as Owner\nmain : Unit -> Owner.Scope<Unit, Unit, Int>\nmain () = resource Owner.Probe<{}, Fresh, {}> owner = 42 {\n    Owner.read owner\n}\n",
        );
        let owner = include_str!("fixtures/source-owner/owner.ash").replace(
            "false => Acquired(state, size)",
            &format!("false => {expression}"),
        ) + "\npayload_copy<T> : T -> T\npayload_copy value = value\npayload_ignore<T> : T -> Unit\npayload_ignore value = ()\n";
        fs::write(fixture.0.join("owner.ash"), owner).unwrap();
        let error = compile_path(fixture.configuration())
            .expect_err("native State must not cross an ordinary helper");
        let failure = format!("{:?}", error.pipeline_failure().unwrap());
        assert!(
            failure.starts_with("Typing("),
            "expected a checked State refusal, not an invalid source fixture: {failure}; {expression}"
        );
    }
}

#[test]
fn lifecycle_payload_helpers_cannot_hide_native_requests() {
    let fixture = Fixture::new(
        "import owner as Owner\nmain : Unit -> Owner.Scope<Unit, Unit, Int>\nmain () = resource Owner.Probe<{}, Fresh, {}> owner = 42 {\n    Owner.read owner\n}\n",
    );
    let owner = include_str!("fixtures/source-owner/owner.ash").replace(
        "false => Acquired(state, size)",
        "false => Acquired(state, payload_native size)",
    ) + "\npayload_native : Int -> Int ! {Allocate<{}, Unit, {}>}\npayload_native value = {\n    let output = perform Allocate<{}, Unit, {}>.call value\n    value\n}\n";
    fs::write(fixture.0.join("owner.ash"), owner).unwrap();
    let error = compile_path(fixture.configuration())
        .expect_err("an ordinary payload helper grants no native request permission");
    let failure = format!("{:?}", error.pipeline_failure().unwrap());
    assert!(
        failure.starts_with("Typing("),
        "expected checked hidden-effect refusal: {failure}"
    );
}
