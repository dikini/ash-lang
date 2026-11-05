use crate::{
    lexer::{lex, lex_with_budget},
    source::SourceFile,
    syntax_resource::SyntaxBudget,
};

use super::{
    ConcreteTree, ResourceFailure, finish_module_from_checkpoint, parse, parse_module_header,
    parse_with_budget,
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
