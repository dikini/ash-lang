use crate::{
    lexer::{lex, lex_with_budget},
    source::SourceFile,
    surface::{SurfaceImportItem, SurfaceImportSelection},
    syntax_resource::SyntaxBudget,
};

use super::{
    ConcreteTree, ProjectionError, ResourceFailure, finish_module_from_checkpoint, parse,
    parse_module_header, parse_with_budget, parse_with_budget_and_header, project_module_header,
};

fn parse_at_limit(source: &SourceFile, limit: usize) -> (ConcreteTree, usize) {
    let mut budget = SyntaxBudget::with_limit(limit);
    let lexed = lex_with_budget(source, &mut budget).unwrap();
    let tree = parse_with_budget(lexed, &mut budget);
    (tree, budget.consumed())
}

#[test]
fn module_header_and_body_have_exact_syntax_budget_boundaries() {
    for (text, original_cost) in [
        ("main : Unit -> Int\nmain () = 42\n", 52),
        (
            "import helpers as Helpers\nimport values (answer)\nmain : Unit -> Int\nmain () = Helpers.increment(answer)\n",
            104,
        ),
        (
            "import helpers (answer\nmain : Unit -> Int\nmain () = 42\n",
            70,
        ),
    ] {
        let source = SourceFile::new("budget-parity.ash", text).unwrap();
        let (expected, cost) = parse_at_limit(&source, 10_000);
        assert!(expected.resource_failure().is_none());
        assert_eq!(cost, original_cost, "original parser cost: {text:?}");
        let (at_limit, paid) = parse_at_limit(&source, cost);
        assert_eq!(at_limit, expected, "exact budget: {text:?}");
        assert_eq!(paid, cost);
        let (below_limit, _) = parse_at_limit(&source, cost - 1);
        assert_eq!(
            below_limit.resource_failure(),
            Some(ResourceFailure::SyntaxWork { limit: cost - 1 }),
            "one below budget: {text:?}"
        );
        for limit in [0, 1, expected.tokens().len() + 1] {
            let (limited, _) = parse_at_limit(&source, limit);
            assert_eq!(
                limited.resource_failure(),
                Some(ResourceFailure::SyntaxWork { limit }),
                "low budget {limit}: {text:?}"
            );
        }
        for limit in [1, cost - 1, cost] {
            let (baseline, spent) = parse_at_limit(&source, limit);
            let mut budget = SyntaxBudget::with_limit(limit);
            let lexed = lex_with_budget(&source, &mut budget).unwrap();
            let (loaded, _) = parse_with_budget_and_header(&source, lexed, &mut budget);
            assert_eq!(
                loaded, baseline,
                "loader parser at budget {limit}: {text:?}"
            );
            assert_eq!(budget.consumed(), spent);
        }
    }
}

#[test]
fn interleaved_header_checkpoints_preserve_complete_trees_and_one_budget() {
    let first = SourceFile::new(
        "first.ash",
        "import helpers as Helpers\nimport values (answer)\nmain : Unit -> Int\nmain () = Helpers.increment(answer)\n",
    )
    .unwrap();
    let second = SourceFile::new(
        "second.ash",
        "import helpers (answer\nmain : Unit -> Int\nmain () = 42\n",
    )
    .unwrap();
    let expected_first = parse(lex(&first).unwrap());
    let expected_second = parse(lex(&second).unwrap());
    let mut budget = SyntaxBudget::with_limit(174);
    let (first_tokens, first_lexical, _, first_failure) =
        lex_with_budget(&first, &mut budget).unwrap().into_parts();
    let (second_tokens, second_lexical, _, second_failure) =
        lex_with_budget(&second, &mut budget).unwrap().into_parts();
    assert!(first_failure.is_none() && second_failure.is_none());
    let (first_header, budget) = parse_module_header(first_tokens, first_lexical, budget);
    let (second_header, budget) = parse_module_header(second_tokens, second_lexical, budget);
    let (actual_second, budget) = finish_module_from_checkpoint(second_header, budget);
    let (actual_first, budget) = finish_module_from_checkpoint(first_header, budget);
    assert_eq!(actual_first, expected_first);
    assert_eq!(actual_second, expected_second);
    assert_eq!(budget.consumed(), 174);
}

#[test]
fn header_projection_extracts_imports_before_the_body_is_parsed() {
    let source = SourceFile::new(
        "header.ash",
        "import values (answer as number)\nmain : Unit -> Int\nmain () = )\n",
    )
    .unwrap();
    let mut budget = SyntaxBudget::with_limit(1_000);
    let (tokens, lexical, _, failure) = lex_with_budget(&source, &mut budget).unwrap().into_parts();
    assert!(failure.is_none());
    let (header, budget) = parse_module_header(tokens, lexical, budget);
    let imports = project_module_header(&source, &header).expect("valid header projects");
    let [import] = imports.as_slice() else {
        panic!("expected one import");
    };
    let SurfaceImportSelection::Targeted(items) = &import.selection else {
        panic!("expected a targeted import");
    };
    assert!(matches!(
        items.as_slice(),
        [SurfaceImportItem::Name { name, alias: Some(alias), .. }]
            if name.text == "answer" && alias.text == "number"
    ));
    let (tree, _) = finish_module_from_checkpoint(header, budget);
    assert!(!tree.parse_diagnostics().is_empty());
}

#[test]
fn header_projection_rejects_recovery_and_foreign_sources() {
    let source = SourceFile::new("header.ash", "import values (answer\nmain () = 42\n").unwrap();
    let mut budget = SyntaxBudget::with_limit(1_000);
    let (tokens, lexical, _, _) = lex_with_budget(&source, &mut budget).unwrap().into_parts();
    let (header, _) = parse_module_header(tokens, lexical, budget);
    assert_eq!(
        project_module_header(&source, &header),
        Err(ProjectionError::RecoveryNodesPresent)
    );

    let source = SourceFile::new("good.ash", "import values (answer)\n").unwrap();
    let foreign = SourceFile::new("other.ash", source.text()).unwrap();
    let mut budget = SyntaxBudget::with_limit(1_000);
    let (tokens, lexical, _, _) = lex_with_budget(&source, &mut budget).unwrap().into_parts();
    let (header, _) = parse_module_header(tokens, lexical, budget);
    assert!(matches!(
        project_module_header(&foreign, &header),
        Err(ProjectionError::MalformedTree(
            super::InternalReason::ForeignSpan
        ))
    ));
}

#[test]
fn header_projection_rejects_header_lexical_errors_but_retains_body_errors() {
    for (text, header_error) in [
        ("import values # (answer)\nmain () = 42\n", true),
        ("import values (answer)\nmain () = 42 #\n", false),
    ] {
        let source = SourceFile::new("lexical.ash", text).unwrap();
        let mut budget = SyntaxBudget::with_limit(1_000);
        let (tokens, lexical, _, _) = lex_with_budget(&source, &mut budget).unwrap().into_parts();
        assert!(!lexical.is_empty());
        let (header, budget) = parse_module_header(tokens, lexical, budget);
        let imports = project_module_header(&source, &header);
        if header_error {
            assert_eq!(imports, Err(ProjectionError::RecoveryNodesPresent));
        } else {
            assert_eq!(imports.unwrap().len(), 1);
        }
        let (tree, _) = finish_module_from_checkpoint(header, budget);
        assert!(!tree.lexical_diagnostics().is_empty());
    }
}

#[test]
fn header_projection_refuses_an_exhausted_parser_budget() {
    let source = SourceFile::new("limited.ash", "import values (answer)\n").unwrap();
    let (tokens, lexical, _, _) = lex(&source).unwrap().into_parts();
    let (header, _) = parse_module_header(tokens, lexical, SyntaxBudget::with_limit(0));
    assert_eq!(
        project_module_header(&source, &header),
        Err(ProjectionError::ResourceLimit(
            ResourceFailure::SyntaxWork { limit: 0 }
        ))
    );
}

#[test]
fn header_projection_rejects_a_prematurely_closed_module_event() {
    let source = SourceFile::new("closed.ash", "import values (answer)\n").unwrap();
    let (tokens, lexical, _, _) = lex(&source).unwrap().into_parts();
    let (mut header, _) = parse_module_header(tokens, lexical, SyntaxBudget::with_limit(1_000));
    header.events.push(super::Event::Finish);
    assert!(matches!(
        project_module_header(&source, &header),
        Err(ProjectionError::MalformedTree(_))
    ));
}

#[test]
fn projected_header_matches_complete_projection_for_import_forms() {
    let source = SourceFile::new(
        "imports.ash",
        "import @std.collections.list as List\nimport helpers.math (sum, Number as ImportedNumber)\npub import equality (Equal as Equality, equal, impl Equal)\nmain : Unit -> Int\nmain () = 42\n",
    )
    .unwrap();
    let mut budget = SyntaxBudget::with_limit(10_000);
    let (tokens, lexical, _, _) = lex_with_budget(&source, &mut budget).unwrap().into_parts();
    let (header, budget) = parse_module_header(tokens, lexical, budget);
    let imports = project_module_header(&source, &header).unwrap();
    let (tree, _) = finish_module_from_checkpoint(header, budget);
    assert_eq!(
        imports,
        super::project_module(&source, &tree).unwrap().imports
    );
}
