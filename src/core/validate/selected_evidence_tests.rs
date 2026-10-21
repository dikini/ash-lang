use super::*;

#[test]
fn checked_selected_host_single_module_authenticates_each_core_phase() {
    let source = r#"import @builtin.foreign as Foreign
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
    let (program, graph) = super::foreign_host_tests::original(source);
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
