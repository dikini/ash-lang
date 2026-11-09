use std::path::{Path, PathBuf};

use ash::{
    driver::{RunConfiguration, compile_path},
    lexer::lex,
    module::{LoadGraphError, ModuleRoots},
    parser::{
        ConcreteElement, ConcreteNode, ConcreteTree, InternalReason, NodeKind, ParseReason,
        ProjectionError, ResourceFailure, STRUCTURAL_DEPTH_LIMIT, parse, project_module,
    },
    source::SourceFile,
};

fn parse_source(text: &str) -> (SourceFile, ConcreteTree) {
    let source = SourceFile::new("quote-parser.ash", text).unwrap();
    let tree = parse(lex(&source).unwrap());
    (source, tree)
}

fn text_at<'a>(source: &'a SourceFile, span: ash::source::Span) -> &'a str {
    assert_eq!(span.source(), source.id());
    &source.text()[span.range().start() as usize..span.range().end() as usize]
}

fn nodes_of_kind(tree: &ConcreteTree, kind: NodeKind) -> Vec<&ConcreteNode> {
    let mut found = Vec::new();
    let mut pending = vec![tree.root().expect("the concrete tree must have a root")];
    while let Some(node) = pending.pop() {
        if node.kind == kind {
            found.push(node);
        }
        pending.extend(node.children.iter().rev().filter_map(|child| match child {
            ConcreteElement::Node(child) => Some(child),
            _ => None,
        }));
    }
    found
}

fn direct_token_texts<'a>(
    source: &'a SourceFile,
    tree: &ConcreteTree,
    node: &ConcreteNode,
) -> Vec<&'a str> {
    node.children
        .iter()
        .filter_map(|child| match child {
            ConcreteElement::Token(index) => Some(text_at(source, tree.tokens()[*index].span)),
            _ => None,
        })
        .collect()
}

#[test]
fn malformed_unused_quote_reports_the_missing_operand_in_its_definition() {
    let entry = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("docs/design/macros/fixtures/generators/malformed_helper.ash");
    let failure = compile_path(RunConfiguration {
        entry,
        roots: ModuleRoots::empty(),
    })
    .expect_err("the imported unused malformed quote must reject");
    let Some(LoadGraphError::Syntax(syntax)) = failure.graph_failure() else {
        panic!("expected source parsing to reject the quote: {failure:?}");
    };
    assert!(Path::new(syntax.source.display_path()).ends_with("malformed_helper_forms.ash"));
    assert_eq!(syntax.resource, None);
    let diagnostic = syntax
        .parser
        .iter()
        .find(|diagnostic| diagnostic.reason == ParseReason::ExpectedOperand)
        .expect("the quoted addition must report a missing operand");
    let span = diagnostic.primary.span();
    assert_eq!(text_at(&syntax.source, span), "+");
}

#[test]
fn expression_quotes_parse_as_primaries_without_resolving_holes() {
    let (source, tree) =
        parse_source("probe : Unit -> Unit\nprobe () = consume(syntax { $fragment + 1 })\n");
    assert!(tree.lexical_diagnostics().is_empty());
    assert_eq!(tree.resource_failure(), None);
    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    assert!(tree.root().is_some());
    assert_eq!(
        project_module(&source, &tree),
        Err(ProjectionError::MalformedTree(
            InternalReason::UnexpectedShape
        ))
    );
}

#[test]
fn quotes_are_accepted_in_existing_primary_positions() {
    for expression in [
        "syntax { 1 }",
        "syntax { 1 } + 2",
        "1 + syntax { 2 }",
        "syntax { 1 } argument",
        "consume syntax { 1 }",
        "(syntax { 1 }, 2)",
    ] {
        let text = format!("probe : Unit -> Int\nprobe () = {expression}\n");
        let (_, tree) = parse_source(&text);
        assert_eq!(tree.resource_failure(), None, "{expression}");
        assert!(
            tree.parse_diagnostics().is_empty(),
            "{expression}: {:?}",
            tree.parse_diagnostics()
        );
        assert_eq!(
            nodes_of_kind(&tree, NodeKind::SyntaxQuote).len(),
            1,
            "{expression}"
        );
    }
}

#[test]
fn malformed_quote_inside_an_outer_template_reports_its_operand() {
    let (source, tree) = parse_source(
        "pub syntax declaration: (broken) $name:ident => {\n$name () = syntax { 0 + }\n}\n",
    );
    let diagnostic = tree
        .parse_diagnostics()
        .iter()
        .find(|diagnostic| diagnostic.reason == ParseReason::ExpectedOperand)
        .expect("the nested quoted addition must report a missing operand");
    assert_eq!(text_at(&source, diagnostic.primary.span()), "+");
}

#[test]
fn nested_multiline_escape_preserves_the_three_dollar_scopes() {
    let (source, tree) = parse_source(
        "pub syntax declaration: (nested) $name:ident => {\n\
         $name () = syntax {\n\
         $name + ${\n\
         let value = $name\n\
         let inner = syntax { $value }\n\
         let another = $name\n\
         inner\n\
         } + $name\n\
         }\n\
         sibling () = syntax { $name }\n\
         }\n",
    );
    assert!(tree.lexical_diagnostics().is_empty());
    assert_eq!(tree.resource_failure(), None);
    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    assert_eq!(nodes_of_kind(&tree, NodeKind::SyntaxQuote).len(), 3);
    assert_eq!(nodes_of_kind(&tree, NodeKind::SyntaxEscape).len(), 1);
    for (kind, expected, count) in [
        (NodeKind::TemplateSplice, "$name", 3),
        (NodeKind::EscapeCaptureRead, "$name", 2),
        (NodeKind::QuoteHole, "$value", 1),
    ] {
        let nodes = nodes_of_kind(&tree, kind);
        assert_eq!(nodes.len(), count, "{kind:?}");
        for node in nodes {
            assert_eq!(direct_token_texts(&source, &tree, node).concat(), expected);
        }
    }
}

#[test]
fn malformed_quote_restores_template_mode_for_a_sibling_quote() {
    let (source, tree) = parse_source(
        "pub syntax declaration: (broken) $name:ident => {\n\
         $name () = syntax { 1 + }\n\
         sibling () = syntax { $name }\n\
         }\n",
    );
    assert!(tree.parse_diagnostics().iter().any(|diagnostic| {
        diagnostic.reason == ParseReason::ExpectedOperand
            && text_at(&source, diagnostic.primary.span()) == "+"
    }));
    let splices = nodes_of_kind(&tree, NodeKind::TemplateSplice);
    assert_eq!(splices.len(), 1);
    assert_eq!(
        direct_token_texts(&source, &tree, splices[0]).concat(),
        "$name"
    );
    assert!(nodes_of_kind(&tree, NodeKind::QuoteHole).is_empty());
}

#[test]
fn inline_escapes_restore_capture_and_quote_modes() {
    let (source, tree) = parse_source(
        "pub syntax declaration: (inline) $name:ident from $value:expr => {\n\
         $name () = syntax { ${ $value } + $name }\n\
         sibling () = syntax { ${ syntax { $local } } + $name }\n\
         }\n",
    );
    assert_eq!(tree.resource_failure(), None);
    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    for (kind, spelling, count) in [
        (NodeKind::SyntaxEscape, "", 2),
        (NodeKind::TemplateSplice, "$name", 2),
        (NodeKind::EscapeCaptureRead, "$value", 1),
        (NodeKind::QuoteHole, "$local", 1),
    ] {
        let nodes = nodes_of_kind(&tree, kind);
        assert_eq!(nodes.len(), count, "{kind:?}");
        if !spelling.is_empty() {
            for node in nodes {
                assert_eq!(direct_token_texts(&source, &tree, node).concat(), spelling);
            }
        }
    }
}

#[test]
fn inline_escape_uses_one_expression_and_existing_line_rules() {
    for newline in ["\n", "\r\n"] {
        let text = format!(
            "probe : Unit -> Int{newline}probe () = syntax {{ ${{ (1 +{newline}2) }} }}{newline}"
        );
        let (_, tree) = parse_source(&text);
        assert!(tree.lexical_diagnostics().is_empty());
        assert_eq!(tree.resource_failure(), None);
        assert!(
            tree.parse_diagnostics().is_empty(),
            "{:?}",
            tree.parse_diagnostics()
        );
    }
    let (_, application) = parse_source("probe : Unit -> Int\nprobe () = syntax { ${ 1 2 } }\n");
    assert!(
        application.parse_diagnostics().is_empty(),
        "{:?}",
        application.parse_diagnostics()
    );
    assert_eq!(
        nodes_of_kind(&application, NodeKind::ApplicationExpression).len(),
        1
    );
    let (_, ordinary_block) = parse_source("probe : Unit -> Int\nprobe () = { 1 }\n");
    assert!(!ordinary_block.parse_diagnostics().is_empty());

    for (expression, expected) in [
        ("${ 1, 2 }", ","),
        ("${ 1\n}", "\n"),
        ("${ 1\r\n}", "\r\n"),
        ("${ let value = 1 }", "let"),
        ("${ newtype Token = Token(Unit) }", "newtype"),
        ("${ with Check<Token> { } }", "with"),
        ("${ }", "}"),
        ("${ 1 + }", "+"),
    ] {
        let text = format!("probe : Unit -> Int\nprobe () = syntax {{ {expression} }}\n");
        let (source, tree) = parse_source(&text);
        assert!(
            tree.parse_diagnostics()
                .iter()
                .any(|diagnostic| { text_at(&source, diagnostic.primary.span()) == expected }),
            "{expression}: {:?}",
            tree.parse_diagnostics()
        );
    }
    let (_, mismatched) = parse_source("probe : Unit -> Int\nprobe () = syntax { ${ (1 } }\n");
    assert!(!mismatched.parse_diagnostics().is_empty());
}

#[test]
fn malformed_inline_escape_restores_mode_for_the_next_quote() {
    let (source, tree) = parse_source(
        "pub syntax declaration: (broken) $name:ident => {\n\
         $name () = syntax { ${ 1 + } }\n\
         sibling () = syntax { $name }\n\
         }\n",
    );
    assert_eq!(
        tree.parse_diagnostics().len(),
        1,
        "{:?}",
        tree.parse_diagnostics()
    );
    assert!(tree.parse_diagnostics().iter().any(|diagnostic| {
        diagnostic.reason == ParseReason::ExpectedOperand
            && text_at(&source, diagnostic.primary.span()) == "+"
    }));
    let splices = nodes_of_kind(&tree, NodeKind::TemplateSplice);
    assert_eq!(splices.len(), 1);
    assert_eq!(
        direct_token_texts(&source, &tree, splices[0]).concat(),
        "$name"
    );
    assert!(nodes_of_kind(&tree, NodeKind::QuoteHole).is_empty());
}

#[test]
fn fixed_inline_escape_inputs_parse_without_claiming_execution() {
    for text in [
        include_str!("../docs/design/macros/fixtures/escapes/quote_roundtrip_forms.ash"),
        include_str!("../docs/design/macros/fixtures/escapes/primitive_escape_forms.ash"),
        include_str!("../docs/design/macros/fixtures/escapes/wrong_category_forms.ash"),
    ] {
        let (_, tree) = parse_source(text);
        assert!(tree.lexical_diagnostics().is_empty());
        assert_eq!(tree.resource_failure(), None);
        assert!(
            tree.parse_diagnostics().is_empty(),
            "{:?}",
            tree.parse_diagnostics()
        );
        assert!(!nodes_of_kind(&tree, NodeKind::SyntaxEscape).is_empty());
    }
}

#[test]
fn fixed_early_categories_prefix_parses_before_d5() {
    let original =
        include_str!("../docs/design/macros/fixtures/escapes/early_categories_forms.ash");
    let end = original
        .find("pub syntax declaration: (pass_declaration)")
        .expect("the original declaration-capture case must remain present");
    let (_, tree) = parse_source(&original[..end]);
    assert!(tree.lexical_diagnostics().is_empty());
    assert_eq!(tree.resource_failure(), None);
    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    assert!(tree.root().is_some());
    assert_eq!(nodes_of_kind(&tree, NodeKind::SyntaxEscape).len(), 7);
}

#[test]
fn fixed_early_categories_forms_parse_in_full() {
    let (_, tree) = parse_source(include_str!(
        "../docs/design/macros/fixtures/escapes/early_categories_forms.ash"
    ));
    assert!(tree.lexical_diagnostics().is_empty());
    assert_eq!(tree.resource_failure(), None);
    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    assert_eq!(nodes_of_kind(&tree, NodeKind::SyntaxEscape).len(), 8);
}

#[test]
fn inline_escape_within_expression_quote_parses() {
    let (_, tree) = parse_source("probe : Unit -> Int\nprobe () = syntax { ${ 42 } }\n");
    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    assert_eq!(nodes_of_kind(&tree, NodeKind::SyntaxEscape).len(), 1);
}

fn inline_nested_block_depth_source(inner: usize) -> String {
    format!(
        "probe : Unit -> Int\nprobe () = (syntax {{ ${{ {{\n1{}\n}} }} }}) + 1\n",
        " + 1".repeat(inner)
    )
}

#[test]
fn inline_nested_block_depth_and_drop_fit_a_small_stack() {
    let markers = std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut markers = Vec::new();
            let (_, exact) = parse_source(&inline_nested_block_depth_source(123));
            assert_eq!(exact.resource_failure(), None);
            assert!(
                exact.parse_diagnostics().is_empty(),
                "{:?}",
                exact.parse_diagnostics()
            );
            for (kind, count) in [
                (NodeKind::SyntaxQuote, 1),
                (NodeKind::SyntaxEscape, 1),
                (NodeKind::Block, 1),
                (NodeKind::ParenthesizedExpression, 1),
                (NodeKind::AdditiveExpression, 124),
            ] {
                assert_eq!(nodes_of_kind(&exact, kind).len(), count, "{kind:?}");
            }
            markers.push("accepted");
            drop(exact);
            markers.push("accepted dropped");
            let (_, over) = parse_source(&inline_nested_block_depth_source(124));
            assert_eq!(
                over.resource_failure(),
                Some(ResourceFailure::StructuralDepth {
                    limit: STRUCTURAL_DEPTH_LIMIT,
                })
            );
            assert!(over.root().is_none());
            markers.push("rejected");
            drop(over);
            markers.push("rejected dropped");
            markers
        })
        .expect("the small-stack thread should start")
        .join()
        .expect("inline block parsing and disposal should fit the small stack");
    assert_eq!(
        markers,
        [
            "accepted",
            "accepted dropped",
            "rejected",
            "rejected dropped"
        ]
    );
}

#[test]
fn fixed_outer_quote_retains_the_missing_name_as_an_outer_splice() {
    let (source, tree) = parse_source(include_str!(
        "../docs/design/macros/fixtures/escapes/unbound_outer_forms.ash"
    ));
    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    let splices = nodes_of_kind(&tree, NodeKind::TemplateSplice);
    assert_eq!(splices.len(), 1);
    assert_eq!(
        direct_token_texts(&source, &tree, splices[0]).concat(),
        "$missing"
    );
}

#[test]
fn fixed_nested_quote_graph_retains_its_quote_and_escape_structure() {
    let (_, tree) = parse_source(include_str!(
        "../docs/design/macros/fixtures/escapes/early_nested_forms.ash"
    ));
    assert!(tree.lexical_diagnostics().is_empty());
    assert_eq!(tree.resource_failure(), None);
    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    assert_eq!(nodes_of_kind(&tree, NodeKind::SyntaxQuote).len(), 4);
    assert_eq!(nodes_of_kind(&tree, NodeKind::SyntaxEscape).len(), 2);
    assert_eq!(nodes_of_kind(&tree, NodeKind::QuoteHole).len(), 2);
}

#[test]
fn repetition_tokens_remain_template_data_and_are_not_quote_holes() {
    let (_, tree) = parse_source("pub syntax repeat $value:expr => {\n$( $value ),*\n}\n");
    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    assert!(nodes_of_kind(&tree, NodeKind::SyntaxQuote).is_empty());
    assert!(nodes_of_kind(&tree, NodeKind::QuoteHole).is_empty());

    let (_, quote) = parse_source("probe : Unit -> Unit\nprobe () = syntax { $(value) }\n");
    assert!(!quote.parse_diagnostics().is_empty());
}

#[test]
fn quotes_reject_empty_or_multiple_expressions_at_the_inner_boundary() {
    for (quote, expected) in [("syntax { }", "}"), ("syntax { 1, 2 }", ",")] {
        let text = format!("probe : Unit -> Unit\nprobe () = {quote}\n");
        let (source, tree) = parse_source(&text);
        assert!(
            tree.parse_diagnostics()
                .iter()
                .any(|diagnostic| { text_at(&source, diagnostic.primary.span()) == expected }),
            "{quote}: {:?}",
            tree.parse_diagnostics()
        );
    }
}

#[test]
fn quote_depth_composes_with_its_surrounding_expression() {
    let (_, exact) = parse_source(&mixed_quote_depth_source(66));
    assert_eq!(exact.resource_failure(), None);
    assert!(exact.parse_diagnostics().is_empty());
    let (_, over) = parse_source(&mixed_quote_depth_source(67));
    assert_eq!(
        over.resource_failure(),
        Some(ResourceFailure::StructuralDepth {
            limit: STRUCTURAL_DEPTH_LIMIT
        })
    );
    assert!(over.root().is_none());
}

fn mixed_quote_depth_source(outer: usize) -> String {
    format!(
        "probe : Unit -> Int\nprobe () = (syntax {{ 1{} }}){}\n",
        " + 1".repeat(60),
        " + 1".repeat(outer)
    )
}

fn nested_escape_quote_depth_source(additions: usize) -> String {
    let mut expression = format!("1{}", " + 1".repeat(additions));
    for _ in 0..8 {
        expression = format!("syntax {{ ${{\n{expression}\n}} }}");
    }
    format!("probe : Unit -> Int\nprobe () = ({expression}) + 1\n")
}

#[test]
fn quote_depth_success_failure_and_drop_fit_a_small_stack() {
    let markers = std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut markers = Vec::new();
            // Eight quote/block pairs, 110 additions, one group and one outer
            // addition have a combined structural weight of 128.
            let (_, accepted) = parse_source(&nested_escape_quote_depth_source(110));
            assert_eq!(accepted.resource_failure(), None);
            assert!(accepted.root().is_some());
            assert_eq!(nodes_of_kind(&accepted, NodeKind::SyntaxQuote).len(), 8);
            assert_eq!(nodes_of_kind(&accepted, NodeKind::SyntaxEscape).len(), 8);
            assert_eq!(nodes_of_kind(&accepted, NodeKind::Block).len(), 8);
            assert_eq!(
                nodes_of_kind(&accepted, NodeKind::AdditiveExpression).len(),
                111
            );
            assert_eq!(
                nodes_of_kind(&accepted, NodeKind::ParenthesizedExpression).len(),
                1
            );
            markers.push("accepted");
            drop(accepted);
            markers.push("accepted dropped");

            let (_, rejected) = parse_source(&nested_escape_quote_depth_source(111));
            assert_eq!(
                rejected.resource_failure(),
                Some(ResourceFailure::StructuralDepth {
                    limit: STRUCTURAL_DEPTH_LIMIT
                })
            );
            assert!(rejected.root().is_none());
            markers.push("rejected");
            drop(rejected);
            markers.push("rejected dropped");
            markers
        })
        .expect("the small-stack parser thread should start")
        .join()
        .expect("the parser and tree disposal should fit the small stack");
    assert_eq!(
        markers,
        [
            "accepted",
            "accepted dropped",
            "rejected",
            "rejected dropped"
        ]
    );
}

#[test]
fn maximum_quote_nesting_parses_rejects_and_drops_on_a_small_stack() {
    const CHILD: &str = "ASH_E1_QUOTE_STACK_CHILD";
    if std::env::var_os(CHILD).is_none() {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "maximum_quote_nesting_parses_rejects_and_drops_on_a_small_stack",
                "--nocapture",
            ])
            .env(CHILD, "1")
            .output()
            .expect("the isolated stack witness should start");
        assert!(
            output.status.success(),
            "the isolated stack witness failed: {}\n{}",
            output.status,
            String::from_utf8_lossy(&output.stderr)
        );
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(stdout.contains("accepted, accepted dropped, rejected, rejected dropped"));
        print!("{stdout}");
        return;
    }
    let markers = std::thread::Builder::new()
        .stack_size(512 * 1024)
        .spawn(|| {
            let source = |depth| {
                format!(
                    "probe : Unit -> Int\nprobe () = {}1{}\n",
                    "syntax { ".repeat(depth),
                    " }".repeat(depth)
                )
            };
            let mut markers = Vec::new();
            let (_, accepted) = parse_source(&source(STRUCTURAL_DEPTH_LIMIT));
            assert_eq!(accepted.resource_failure(), None);
            assert_eq!(
                nodes_of_kind(&accepted, NodeKind::SyntaxQuote).len(),
                STRUCTURAL_DEPTH_LIMIT
            );
            markers.push("accepted");
            drop(accepted);
            markers.push("accepted dropped");
            let (_, rejected) = parse_source(&source(STRUCTURAL_DEPTH_LIMIT + 1));
            assert_eq!(
                rejected.resource_failure(),
                Some(ResourceFailure::StructuralDepth {
                    limit: STRUCTURAL_DEPTH_LIMIT
                })
            );
            markers.push("rejected");
            drop(rejected);
            markers.push("rejected dropped");
            markers
        })
        .expect("the bounded-stack parser thread should start")
        .join()
        .expect("maximum quote parsing and disposal should fit the stack");
    assert_eq!(
        markers,
        [
            "accepted",
            "accepted dropped",
            "rejected",
            "rejected dropped"
        ]
    );
    println!("{}", markers.join(", "));
}

#[test]
fn maximum_inline_escape_nesting_fits_a_small_stack() {
    const CHILD: &str = "ASH_E1_INLINE_STACK_CHILD";
    if std::env::var_os(CHILD).is_none() {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "maximum_inline_escape_nesting_fits_a_small_stack",
                "--nocapture",
            ])
            .env(CHILD, "1")
            .output()
            .expect("the isolated inline stack witness should start");
        assert!(
            output.status.success(),
            "{}\n{}",
            output.status,
            String::from_utf8_lossy(&output.stderr)
        );
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(stdout.contains("accepted, accepted dropped, rejected, rejected dropped"));
        print!("{stdout}");
        return;
    }
    let markers = std::thread::Builder::new()
        .stack_size(512 * 1024)
        .spawn(|| {
            let mut expression = String::from("1");
            for _ in 0..(STRUCTURAL_DEPTH_LIMIT / 2) {
                expression = format!("syntax {{ ${{ {expression} }} }}");
            }
            let source =
                |expression: &str| format!("probe : Unit -> Int\nprobe () = {expression}\n");
            let mut markers = Vec::new();
            let (_, exact) = parse_source(&source(&expression));
            assert_eq!(exact.resource_failure(), None);
            assert!(
                exact.parse_diagnostics().is_empty(),
                "{:?}",
                exact.parse_diagnostics()
            );
            assert_eq!(
                nodes_of_kind(&exact, NodeKind::SyntaxQuote).len(),
                STRUCTURAL_DEPTH_LIMIT / 2
            );
            assert_eq!(
                nodes_of_kind(&exact, NodeKind::SyntaxEscape).len(),
                STRUCTURAL_DEPTH_LIMIT / 2
            );
            markers.push("accepted");
            drop(exact);
            markers.push("accepted dropped");
            let (_, over) = parse_source(&source(&format!("syntax {{ {expression} }}")));
            assert_eq!(
                over.resource_failure(),
                Some(ResourceFailure::StructuralDepth {
                    limit: STRUCTURAL_DEPTH_LIMIT,
                })
            );
            markers.push("rejected");
            drop(over);
            markers.push("rejected dropped");
            markers
        })
        .expect("the bounded-stack inline parser thread should start")
        .join()
        .expect("inline escape parsing and disposal should fit the stack");
    assert_eq!(
        markers,
        [
            "accepted",
            "accepted dropped",
            "rejected",
            "rejected dropped"
        ]
    );
    println!("{}", markers.join(", "));
}
