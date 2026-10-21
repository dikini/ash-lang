//! Real parsed checked-owner binding and bounded refusal controls.

use super::{
    bind_checked_foreign_owner, bind_foreign_owner,
    tests::{SOURCE, fixture_from},
};
use crate::{
    foreign::{
        checked_source::{ForeignAdmissionError, ForeignAdmissionReason, NativeLibraryId},
        source_contract::{PreparedForeignLibrary, prepare_checked_foreign_library},
    },
    lexer::lex,
    module::ModuleId,
    parser::{parse, project_module},
    resolved::{ResolvedRegistry, ResolvedTypeVariable},
    source::{Origin, SourceFile},
    types::{Kind, NominalTypeId, TypeWorkBudget},
};
use std::sync::Arc;

fn checked_source() -> String {
    SOURCE
        .replace("foreign library", "foreign checked library")
        .replace("Foreign.Call<", "Foreign.CheckedCall<")
        .replace("owned R", "owned R\n            host T")
        .replace(
            "operand 0 from",
            "host T\n            assumes {}\n            operand 0 from",
        )
}

fn fixture() -> (Arc<PreparedForeignLibrary>, NominalTypeId, ResolvedRegistry) {
    fixture_from(&checked_source())
}

fn assert_invalid<T>(result: Result<T, ForeignAdmissionError>) {
    let error = result
        .err()
        .expect("mutated original correspondence must refuse");
    assert!(
        matches!(
            error.reason(),
            ForeignAdmissionReason::InvalidLibrary
                | ForeignAdmissionReason::InvalidParameters
                | ForeignAdmissionReason::InvalidSignature
        ),
        "expected identity/shape refusal, got {error:?}"
    );
}

#[test]
fn checked_owner_binding_preserves_original_and_exact_prefixed_work() {
    let (prepared, nominal, registry) = fixture();
    let parameters = registry.nominal_parameters(nominal).unwrap();
    let library = NativeLibraryId::new(prepared.module(), 0);
    let run = |work: &mut TypeWorkBudget| {
        bind_checked_foreign_owner(
            library,
            Arc::clone(&prepared),
            0,
            nominal,
            parameters,
            &registry,
            work,
        )
    };
    let mut measured = TypeWorkBudget::default();
    let bound = run(&mut measured).unwrap();
    assert!(Arc::ptr_eq(bound.prepared(), &prepared));
    assert_eq!(bound.nominal(), nominal);
    assert_eq!(bound.owner().member_index(), 3);
    assert_eq!(bound.owned_parameter(), 1);
    assert_eq!(bound.parameter_ids(), &[parameters[0].id, parameters[1].id]);
    let selected = &prepared.checked_contract().unwrap().owners()[0];
    assert_eq!(selected.host_parameter(), 0);
    assert_ne!(selected.host_parameter(), bound.owned_parameter());
    assert!(prepared.owners()[0].retained_parameters().is_empty());
    let required = measured.used();
    assert!(required > 5);
    for prefix in [0, 7] {
        let mut short = TypeWorkBudget::with_limit(prefix + required - 1);
        short.charge(prefix).unwrap();
        assert_eq!(
            run(&mut short).unwrap_err().reason(),
            ForeignAdmissionReason::WorkExhausted
        );
        for _ in 0..2 {
            let mut exact = TypeWorkBudget::with_limit(prefix + required);
            exact.charge(prefix).unwrap();
            let retry = run(&mut exact).unwrap();
            assert_eq!(retry.parameter_ids(), bound.parameter_ids());
            assert!(Arc::ptr_eq(retry.prepared(), &prepared));
            assert_eq!(exact.used(), prefix + required);
            assert_eq!(
                run(&mut exact).unwrap_err().reason(),
                ForeignAdmissionReason::WorkExhausted
            );
        }
    }
}

#[test]
fn checked_owner_binding_rejects_parameter_order_identity_kind_and_origins() {
    let (prepared, nominal, registry) = fixture();
    let parameters = registry.nominal_parameters(nominal).unwrap();
    let library = NativeLibraryId::new(prepared.module(), 0);
    bind_checked_foreign_owner(
        library,
        Arc::clone(&prepared),
        0,
        nominal,
        parameters,
        &registry,
        &mut TypeWorkBudget::default(),
    )
    .unwrap();
    let mutations: &[fn(&mut [ResolvedTypeVariable])] = &[
        |parameters| parameters.swap(0, 1),
        |parameters| parameters[0].id = parameters[1].id,
        |parameters| parameters[0].kind = Kind::EffectRow,
        |parameters| parameters[0].origin = parameters[1].origin.clone(),
        |parameters| parameters[0].spelling = "Donor".to_owned(),
    ];
    for mutate in mutations {
        let mut changed = parameters.to_vec();
        mutate(&mut changed);
        assert_invalid(bind_checked_foreign_owner(
            library,
            Arc::clone(&prepared),
            0,
            nominal,
            &changed,
            &registry,
            &mut TypeWorkBudget::default(),
        ));
    }
    // A coherent changed kind mirror still disagrees with the parsed original.
    let mut changed = parameters.to_vec();
    changed[0].kind = Kind::EffectRow;
    let changed_registry = registry
        .clone()
        .with_type_parameters(vec![(nominal, changed.clone())]);
    assert_invalid(bind_checked_foreign_owner(
        library,
        Arc::clone(&prepared),
        0,
        nominal,
        &changed,
        &changed_registry,
        &mut TypeWorkBudget::default(),
    ));
    let donor = SourceFile::new("donor-owner.ash", checked_source()).unwrap();
    let mut changed = parameters.to_vec();
    changed[0].origin = Origin::Source(
        donor
            .span(parameters[0].origin.primary_span().range())
            .unwrap(),
    );
    assert_invalid(bind_checked_foreign_owner(
        library,
        prepared,
        0,
        nominal,
        &changed,
        &registry,
        &mut TypeWorkBudget::default(),
    ));
}

#[test]
fn checked_owner_binding_rejects_donor_library_nominal_registry_and_index() {
    let (prepared, nominal, registry) = fixture();
    let (donor, donor_nominal, donor_registry) = fixture();
    let parameters = registry.nominal_parameters(nominal).unwrap();
    let library = NativeLibraryId::new(prepared.module(), 0);
    bind_checked_foreign_owner(
        library,
        Arc::clone(&prepared),
        0,
        nominal,
        parameters,
        &registry,
        &mut TypeWorkBudget::default(),
    )
    .unwrap();
    assert_invalid(bind_checked_foreign_owner(
        NativeLibraryId::new(donor.module(), 0),
        Arc::clone(&prepared),
        0,
        nominal,
        parameters,
        &registry,
        &mut TypeWorkBudget::default(),
    ));
    assert_invalid(bind_checked_foreign_owner(
        library,
        Arc::clone(&prepared),
        1,
        nominal,
        parameters,
        &registry,
        &mut TypeWorkBudget::default(),
    ));
    assert_invalid(bind_checked_foreign_owner(
        library,
        Arc::clone(&prepared),
        0,
        NominalTypeId::new(prepared.module(), 1),
        parameters,
        &registry,
        &mut TypeWorkBudget::default(),
    ));
    assert_invalid(bind_checked_foreign_owner(
        library,
        Arc::clone(&prepared),
        0,
        donor_nominal,
        parameters,
        &registry,
        &mut TypeWorkBudget::default(),
    ));
    assert_invalid(bind_checked_foreign_owner(
        library,
        donor,
        0,
        nominal,
        parameters,
        &registry,
        &mut TypeWorkBudget::default(),
    ));
    assert_invalid(bind_checked_foreign_owner(
        library,
        prepared,
        0,
        nominal,
        parameters,
        &donor_registry,
        &mut TypeWorkBudget::default(),
    ));
}

#[test]
fn checked_owner_preparation_rejects_host_selected_as_owned_identity() {
    let text = checked_source().replace("host T", "host R");
    let source = SourceFile::new("checked-host-owned.ash", text).unwrap();
    let tree = parse(lex(&source).unwrap());
    assert!(tree.parse_diagnostics().is_empty());
    let module = project_module(&source, &tree).unwrap();
    assert!(
        prepare_checked_foreign_library(ModuleId::from(source.id()), &module.foreign_libraries[0])
            .is_err(),
        "H cannot select the owner's fresh owned slot"
    );
}

#[test]
fn checked_owner_binding_and_legacy_binding_do_not_cross_profiles() {
    let (legacy, nominal, registry) = fixture_from(SOURCE);
    let parameters = registry.nominal_parameters(nominal).unwrap();
    let library = NativeLibraryId::new(legacy.module(), 0);
    bind_foreign_owner(
        library,
        Arc::clone(&legacy),
        0,
        nominal,
        parameters,
        &registry,
        &mut TypeWorkBudget::default(),
    )
    .unwrap();
    assert_invalid(bind_checked_foreign_owner(
        library,
        legacy,
        0,
        nominal,
        parameters,
        &registry,
        &mut TypeWorkBudget::default(),
    ));
    let (checked, nominal, registry) = fixture();
    assert_invalid(bind_foreign_owner(
        NativeLibraryId::new(checked.module(), 0),
        checked,
        0,
        nominal,
        registry.nominal_parameters(nominal).unwrap(),
        &registry,
        &mut TypeWorkBudget::default(),
    ));
}
