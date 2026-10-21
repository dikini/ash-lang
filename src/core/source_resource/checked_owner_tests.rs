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
fn header_admission(text: &str, checked: bool) -> Result<(), super::ValidationError> {
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
            return CheckedSourceResourceHeader::admit(
                header,
                registry,
                &mut TypeWorkBudget::default(),
            )
            .map(|_| ());
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
#[test]
fn checked_owner_legacy_resource_codecs_refuse_at_independent_header_admission() {
    for original in [
        include_str!("../../../tests/fixtures/source-owner/owner.ash"),
        include_str!("../../../tests/fixtures/source-owner/acquired_only_owner.ash"),
    ] {
        header_admission(original, false).expect("the unchanged ordinary resource codec is valid");
        let failure = header_admission(&checked_source(original), true)
            .expect_err("legacy resource codec must not admit checked owner lifecycle");
        assert!(
            failure.reason() != crate::core::ValidationReason::Resource,
            "{failure:?}"
        );
    }
}
