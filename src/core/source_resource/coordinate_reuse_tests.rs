//! Real restored handler checks share syntax, never a completed forest proof.
use super::*;
use crate::{
    core::validate::{DeclarationCoordinateLoan, SourceResourceStructureSession},
    module::ModuleId,
    source::SourceFile,
};

pub(crate) fn assert_handler_coordinate_reuse(
    program: &crate::core::ValidatedEffectProgram,
    source_arena: &[SourceFile],
    modules: &[ModuleId],
) {
    let template = program.nodes().iter().find_map(|node| match &node.kind {
        EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope))
            if matches!(scope.header().codec.report, SourceResourceReportCodec::CheckedScope { .. }) =>
                Some(scope.original()),
        _ => None,
    }).expect("actual independently restored checked template");
    let sources = template.module_sources.iter().map(|(_, id)| {
        source_arena.iter().find(|source| source.id() == *id)
            .expect("actual template source in immutable restored arena")
    }).collect::<Vec<_>>();
    let rows = template.handler_rows.as_ref().expect("actual conditional handler");
    let mut graph = SourceHandlerGraph::reconstruct(
        &template.handler, &template.header, &rows.inputs, &mut TypeWorkBudget::default(),
    ).unwrap();
    graph.recipe = Some(&rows.recipe);
    let check = |loan: &DeclarationCoordinateLoan<'_>, sources: &[&SourceFile],
                 module_sources: &[(ModuleId, crate::source::SourceId)], work: &mut TypeWorkBudget| {
        // New session: the conditional branch still runs full semantic checks.
        SourceResourceStructureSession::with_coordinate_loan(loan).check_with_handler_graph(
            &template.handler, &template.header.original, true, sources,
            module_sources, &template.globals, Some(&graph), work,
        )
    };
    let loan = DeclarationCoordinateLoan::new(source_arena, modules, &mut TypeWorkBudget::default()).unwrap();
    SourceResourceStructureSession::with_coordinate_loan(&loan).check_with_handler_graph(
        &template.acquire, &template.header.original, false, &sources,
        &template.module_sources, &template.globals, None, &mut TypeWorkBudget::default(),
    ).expect("actual acquire warms syntax for the fresh handler admission");
    let mut measured = TypeWorkBudget::default();
    check(&loan, &sources, &template.module_sources, &mut measured)
        .expect("canonical full handler authentication with warm syntax");
    let warm = measured.used();
    assert!(warm > 0);
    let cold_loan = DeclarationCoordinateLoan::new(source_arena, modules, &mut TypeWorkBudget::default()).unwrap();
    let mut cold = TypeWorkBudget::default();
    check(&cold_loan, &sources, &template.module_sources, &mut cold)
        .expect("fresh operation pays syntax and semantic authentication");
    assert!(cold.used() > warm, "fresh syntax extraction remains paid");
    let fresh_loan = DeclarationCoordinateLoan::new(source_arena, modules, &mut TypeWorkBudget::default()).unwrap();
    let mut fresh = TypeWorkBudget::default();
    check(&fresh_loan, &sources, &template.module_sources, &mut fresh).unwrap();
    assert_eq!(fresh.used(), cold.used(), "no cross-operation syntax receipt");
    for prefix in [0, 7] {
        let mut short = TypeWorkBudget::with_limit(prefix + warm - 1);
        short.charge(prefix).unwrap();
        assert_eq!(check(&loan, &sources, &template.module_sources, &mut short).unwrap_err().reason(),
            crate::core::ValidationReason::Resource);
        for _ in 0..2 {
            let mut exact = TypeWorkBudget::with_limit(prefix + warm);
            exact.charge(prefix).unwrap();
            check(&loan, &sources, &template.module_sources, &mut exact).unwrap();
            assert_eq!(exact.used(), prefix + warm);
            assert_eq!(check(&loan, &sources, &template.module_sources, &mut exact).unwrap_err().reason(),
                crate::core::ValidationReason::Resource);
        }
    }
    // Equal source IDs and bytes in new allocations cannot borrow this loan.
    let cloned = sources.iter().map(|source| (**source).clone()).collect::<Vec<_>>();
    let cloned_refs = cloned.iter().collect::<Vec<_>>();
    assert_eq!(check(&loan, &cloned_refs, &template.module_sources, &mut TypeWorkBudget::default())
        .unwrap_err().reason(), crate::core::ValidationReason::Registry);
    let mut wrong_modules = template.module_sources.to_vec();
    assert!(wrong_modules.len() > 1, "real checked fixture imports its builtin module");
    let first_source = wrong_modules[0].1;
    wrong_modules[0].1 = wrong_modules[1].1;
    wrong_modules[1].1 = first_source;
    assert_eq!(check(&loan, &sources, &wrong_modules, &mut TypeWorkBudget::default())
        .unwrap_err().reason(), crate::core::ValidationReason::Registry);
    let mut retry = TypeWorkBudget::default();
    check(&loan, &sources, &template.module_sources, &mut retry).unwrap();
    assert_eq!(retry.used(), warm, "refusal preserves unchanged canonical retry");
}
