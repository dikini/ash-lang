use super::*;

const SELECTED_HOST: &str = r#"import @builtin.foreign as Foreign
foreign checked library C {
    profile "x86_64-unknown-linux-gnu"
    repr I32 = signed(32)
    symbol Abs<H> : Int -> Foreign.CheckedCall<Int> {
        name "abs"
        abi (I32) -> I32
        host H
        assumes { }
        operand 0 from 0 scalar
        output result as scalar
        outcome otherwise { readable result }
    }
}
closed : Int -> Foreign.CheckedCall<Int>
closed value = foreign host Local {
    perform Abs<Local>.call value
}
interface Read<A> {
    read : A -> Foreign.CheckedCall<Int>
}
impl Read<Int> {
    read value = closed value
}
main : Unit -> Foreign.CheckedCall<Int>
main () = read 7
"#;

#[test]
fn checked_selected_host_single_module_authenticates_each_core_phase() {
    let (program, graph) = super::foreign_host_tests::original(SELECTED_HOST);
    let sources = graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let modules = graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    let mut validator = Validator::new_modules(&program, &sources, &modules).unwrap();
    let mut owners = validator
        .validate_registry()
        .expect("selected host nominal/variable registry admission");
    validator
        .validate_effect_registry(validator.module_sources.as_ref(), &mut owners)
        .expect("selected host effect registry admission");
    validator
        .validate_method_evidence_authority()
        .expect("selected host method evidence authority");
    validator
        .run_effect()
        .expect("selected host independent Core validation");
}

fn validation_work(
    program: &crate::core::UnvalidatedEffectProgram,
    graph: &crate::module::ModuleGraph,
    limit: Option<usize>,
) -> (Option<ValidationReason>, usize) {
    let sources = graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let modules = graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    let mut validator = Validator::new_modules(program, &sources, &modules).unwrap();
    if let Some(limit) = limit {
        validator.type_work_limit = limit;
    }
    let reason = validator.run_effect().err().map(|error| error.reason());
    (reason, validator.type_work.get())
}

#[test]
fn checked_selected_host_ordering_preserves_independent_host_authentication() {
    use crate::core::effect::{EffectExprKind, EffectOperation, ForeignHostIdentity};
    use crate::types::{EffectId, TypeVariableId};

    let (program, graph) = super::foreign_host_tests::original(SELECTED_HOST);
    let sources = graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let modules = graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    let validated = crate::core::validate_effect_modules(program, &sources, &modules).unwrap();
    for change in 0..4 {
        let mut changed = crate::core::transform::identity_effect_traversal(&validated).unwrap();
        let donor = changed
            .registry
            .type_variables()
            .find(|parameter| {
                parameter.spelling == "A" && parameter.id.module() == Some(graph.entry())
            })
            .unwrap()
            .id;
        let boundary = changed
            .nodes
            .iter_mut()
            .find_map(|node| match &mut node.kind {
                EffectExprKind::Operation(EffectOperation::NativeInterpret(boundary))
                    if boundary.host().is_some() =>
                {
                    Some(boundary)
                }
                _ => None,
            })
            .unwrap();
        let host = boundary.host.unwrap();
        match change {
            0 => boundary.host = None,
            1 => {
                boundary.host = Some(ForeignHostIdentity {
                    identity: donor,
                    ..host
                })
            }
            2 => {
                boundary.host = Some(ForeignHostIdentity {
                    identity: TypeVariableId::new(900_001),
                    ..host
                })
            }
            3 => {
                boundary.host = Some(ForeignHostIdentity {
                    effect: EffectId::new(host.effect().module(), 1),
                    ..host
                })
            }
            _ => unreachable!(),
        }
        if change == 3 {
            // The genuine H still classifies body ordering; forged host-effect
            // authority must be rejected independently after registry ordering.
            Validator::new_modules(&changed, &sources, &modules)
                .unwrap()
                .validate_registry()
                .expect("forged effect does not alter the actual host binder ordering");
        }
        assert!(
            validation_work(&changed, &graph, None).0.is_some(),
            "host mutation {change}"
        );
    }
}

#[test]
fn checked_selected_host_ordering_is_charged_exact_short_spent_and_fresh() {
    let (program, graph) = super::foreign_host_tests::original(SELECTED_HOST);
    let (reason, work) = validation_work(&program, &graph, None);
    assert_eq!(reason, None);
    assert!(work > 0);
    assert_eq!(validation_work(&program, &graph, Some(work)).0, None);
    assert_eq!(
        validation_work(&program, &graph, Some(work - 1)).0,
        Some(ValidationReason::Resource)
    );

    let sources = graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let modules = graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    for (limit, expected) in [
        (work + 7, None),
        (work + 6, Some(ValidationReason::Resource)),
    ] {
        let mut prefixed = Validator::new_modules(&program, &sources, &modules).unwrap();
        prefixed.type_work_limit = limit;
        prefixed.charge_type_work(7).unwrap();
        assert_eq!(
            prefixed.run_effect().err().map(|error| error.reason()),
            expected
        );
    }
    // A successful whole run also consumes its budget cumulatively.
    let mut spent = Validator::new_modules(&program, &sources, &modules).unwrap();
    spent.type_work_limit = work;
    spent.run_effect().unwrap();
    assert_eq!(
        spent.run_effect().unwrap_err().reason(),
        ValidationReason::Resource
    );
    assert_eq!(validation_work(&program, &graph, Some(work)).0, None);
}

#[test]
fn checked_selected_host_ordering_does_not_exempt_unrelated_header_parameters() {
    let (program, graph) = super::foreign_host_tests::original(SELECTED_HOST);
    let sources = graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let modules = graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    let validated = crate::core::validate_effect_modules(program, &sources, &modules).unwrap();
    let mut changed = crate::core::transform::identity_effect_traversal(&validated).unwrap();
    let mut ordinary = changed
        .registry
        .type_variables()
        .find(|parameter| parameter.spelling == "A" && parameter.id.module() == Some(graph.entry()))
        .unwrap()
        .clone();
    let earlier = changed
        .registry
        .type_variables()
        .find(|parameter| parameter.spelling == "H" && parameter.id.module() == Some(graph.entry()))
        .unwrap()
        .origin
        .clone();
    ordinary.origin = earlier;
    let ordinary_id = ordinary.id;
    changed.registry = Arc::new(
        (*changed.registry)
            .clone()
            .with_additional_type_variables([ordinary]),
    );
    let validator = Validator::new_modules(&changed, &sources, &modules).unwrap();
    assert!(!validator.is_foreign_host_parameter(ordinary_id).unwrap());
    assert_eq!(
        validator.validate_registry().unwrap_err().reason(),
        ValidationReason::Registry
    );
}
