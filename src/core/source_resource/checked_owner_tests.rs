//! Legacy codecs cannot admit checked owners before checked_scope exists.
use super::CheckedSourceResourceHeader;
use crate::{module::ModuleRoots, types::TypeWorkBudget};
use std::{
    fs,
    sync::atomic::{AtomicU64, Ordering},
};

struct Fixture(std::path::PathBuf);
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
fn header_admission(
    text: &str,
    checked: bool,
    work: &mut TypeWorkBudget,
) -> Result<(), super::ValidationError> {
    static IDS: AtomicU64 = AtomicU64::new(0);
    let fixture = Fixture(std::env::temp_dir().join(format!(
        "ash-checked-owner-codec-{}-{}",
        std::process::id(),
        IDS.fetch_add(1, Ordering::Relaxed)
    )));
    fs::create_dir(&fixture.0).unwrap();
    fs::write(fixture.0.join("entry.ash"), text).unwrap();
    let graph =
        crate::module::load_module_graph(&fixture.0.join("entry.ash"), &ModuleRoots::empty())
            .unwrap();
    let mut modules = Vec::<crate::resolved::CheckedModule>::new();
    for loaded in graph.modules() {
        let dependencies = loaded
            .dependencies()
            .iter()
            .map(|edge| {
                crate::resolve::DependencyExports::new(
                    edge,
                    modules
                        .iter()
                        .find(|m| m.module() == edge.target())
                        .unwrap()
                        .exports(),
                )
                .unwrap()
            })
            .collect::<Vec<_>>();
        let resolved = if checked {
            crate::resolve::resolve_checked_foreign_module(loaded, &dependencies)
        } else {
            crate::resolve::resolve_module(loaded, &dependencies)
        }
        .expect("canonical passive resource source resolves before independent header admission");
        if loaded.id() == graph.entry() {
            let registry = resolved.registry();
            let header = registry
                .source_resource_facts()
                .find(|header| header.spelling == "Probe")
                .unwrap();
            return CheckedSourceResourceHeader::admit(header, registry, work).map(|_| ());
        }
        modules.push(crate::elaborate::check_module(resolved).unwrap());
    }
    panic!("entry");
}
fn checked_source(original: &str) -> String {
    original
        .replace("foreign library", "foreign checked library")
        .replace("State<R>", "State<H, R>")
        .replace(
            "Before : EffectRow, R, After : EffectRow",
            "Before : EffectRow, H, R, After : EffectRow",
        )
        .replace("{| Before}, R, {| After}", "{| Before}, H, R, {| After}")
        .replacen("owned R", "owned R\n        host H", 1)
        .replace(
            "operand 0 from",
            "host H\n        assumes {}\n        operand 0 from",
        )
        .replace("Foreign.Call<", "Foreign.CheckedCall<")
        .replace("Foreign.Returned", "Foreign.CheckedReturned")
        .replace(
            "Foreign.ConversionFailed",
            "Foreign.CheckedConversionFailed",
        )
}
fn legacy_codec_must_refuse_checked(original: &str) {
    header_admission(original, false, &mut TypeWorkBudget::default())
        .expect("the unchanged ordinary resource codec is valid");
    let checked = checked_source(original);
    let run = |work: &mut TypeWorkBudget| header_admission(&checked, true, work);
    let mut measured = TypeWorkBudget::default();
    let failure = run(&mut measured).expect_err("legacy codec must refuse checked owner lifecycle");
    assert_eq!(failure.reason(), crate::core::ValidationReason::Registry);
    let cost = measured.used();
    for prefix in [0, 7] {
        let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
        short.charge(prefix).unwrap();
        assert_eq!(
            run(&mut short).unwrap_err().reason(),
            crate::core::ValidationReason::Resource
        );
        let mut exact = TypeWorkBudget::with_limit(prefix + cost);
        exact.charge(prefix).unwrap();
        assert_eq!(
            run(&mut exact).unwrap_err().reason(),
            crate::core::ValidationReason::Registry
        );
        assert_eq!(exact.used(), prefix + cost);
        assert_eq!(
            run(&mut exact).unwrap_err().reason(),
            crate::core::ValidationReason::Resource
        );
    }
    assert_eq!(
        run(&mut TypeWorkBudget::default()).unwrap_err().reason(),
        crate::core::ValidationReason::Registry
    );
}
#[test]
fn checked_owner_legacy_scope_refuses_at_independent_header_admission() {
    legacy_codec_must_refuse_checked(include_str!(
        "../../../tests/fixtures/source-owner/owner.ash"
    ));
}
#[test]
fn checked_owner_legacy_acquired_only_refuses_at_independent_header_admission() {
    legacy_codec_must_refuse_checked(include_str!(
        "../../../tests/fixtures/source-owner/acquired_only_owner.ash"
    ));
}
