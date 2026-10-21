//! Synthetic control obligations retain independent request value ports.
//! These graph-only fixtures grant no host, native contract or owner authority.

use super::*;

const OWNER_CODE: usize = 20;
const NATIVE_CODE: usize = 30;
const HOST_CODE: usize = 40;

fn graph() -> Graph {
    let source = crate::source::SourceFile::new("host-port.ash", "x").unwrap();
    let span = source
        .span(crate::source::ByteRange::new(0, 1).unwrap())
        .unwrap();
    let expressions = vec![
        Expr::Slot,
        Expr::Scalar,
        Expr::Resource {
            success: None,
            failure: None,
            failure_payload: None,
            handle: 0,
            identity: 0,
            initializer: 1,
            body: 1,
            source: span,
        },
        Expr::Request {
            operand: 0,
            scalar: false,
            reply: None,
        },
    ];
    Graph {
        sources: vec![span; expressions.len()],
        expressions,
        globals: Vec::new(),
        provider: Vec::new(),
        exports: Vec::new(),
        positions: HashMap::from([(OWNER_CODE, 2), (NATIVE_CODE, 3)]),
        targets: HashMap::new(),
        metadata: HashMap::new(),
        evidence: Vec::new(),
        evidence_index: Vec::new(),
    }
}

fn assert_independent_mapping(graph: &Graph) {
    assert_eq!(graph.positions[&NATIVE_CODE], 3);
    assert!(matches!(
        graph.expressions[3],
        Expr::Request {
            operand: 0,
            scalar: false,
            reply: None
        }
    ));
    let host = graph.positions[&HOST_CODE];
    assert_ne!(
        host, 3,
        "host obligation must not alias the State-bearing native request"
    );
    let Expr::Request {
        operand,
        scalar: true,
        reply: Some(reply),
    } = graph.expressions[host]
    else {
        panic!("independent synthetic request and explicit reply");
    };
    assert_ne!(operand, 0);
    assert!(matches!(graph.expressions[operand], Expr::Scalar));
    assert!(matches!(graph.expressions[reply], Expr::Scalar));
    assert_eq!(graph.sources[host], graph.sources[3]);
}

#[test]
fn checked_host_request_port_preserves_native_payload_rejection_and_independent_reply() {
    let mut graph = graph();
    let source = graph.sources[3];
    let mut budget = TypeWorkBudget::default();
    graph
        .position_independent_request(HOST_CODE, source, &mut budget)
        .unwrap();
    assert_independent_mapping(&graph);
    let mut analysis = Analysis::new(&graph, &mut budget).unwrap();
    let state = analysis.slot(0, 0, &mut budget).unwrap();
    // Inject a symbolic owner dependency only; this is not a native State fact.
    analysis
        .atom(state, Atom::Resource(2, 0), &mut budget)
        .unwrap();
    let native = analysis.port(NATIVE_CODE, 0, &mut budget).unwrap();
    let host = analysis.port(HOST_CODE, 0, &mut budget).unwrap();
    analysis.close(&mut budget).unwrap();
    assert!(
        matches!(
            analysis.check_payload(native, OWNER_CODE, 0, &mut budget),
            Err(Failure::Escape { .. })
        ),
        "original native payload must keep its owner escape check"
    );
    analysis
        .check_payload(host, OWNER_CODE, 0, &mut budget)
        .expect("independent host payload contains no State dependency");
    analysis.external_result(host, &mut budget).unwrap();
    analysis.close(&mut budget).unwrap();
    assert!(analysis.slots[host].atoms.contains(&Atom::Free));
    assert!(!analysis.slots[host].atoms.contains(&Atom::Unknown));
    assert!(
        !analysis
            .dependencies(host, &mut budget)
            .unwrap()
            .contains(&Atom::Resource(2, 0))
    );
    assert!(
        matches!(
            analysis.check_payload(native, OWNER_CODE, 0, &mut budget),
            Err(Failure::Escape { .. })
        ),
        "independent reply cannot launder the native payload"
    );
}

#[test]
fn checked_host_request_missing_value_mapping_still_refuses() {
    let graph = graph();
    let mut budget = TypeWorkBudget::default();
    let mut analysis = Analysis::new(&graph, &mut budget).unwrap();
    assert!(matches!(
        analysis.port(HOST_CODE, 0, &mut budget),
        Err(Failure::Invalid)
    ));
    assert!(!graph.positions.contains_key(&HOST_CODE));
    assert_eq!(graph.positions.len(), 2);
}

#[test]
fn checked_host_request_mapping_has_exact_prefix_short_spent_and_fresh_limits() {
    let mut measured_graph = graph();
    let source = measured_graph.sources[3];
    let mut measured = TypeWorkBudget::default();
    measured_graph
        .position_independent_request(HOST_CODE, source, &mut measured)
        .unwrap();
    let cost = measured.used();
    assert!(cost > 0);
    for prefix in [0, 7] {
        let mut exact_graph = graph();
        let source = exact_graph.sources[3];
        let mut exact = TypeWorkBudget::with_limit(prefix + cost);
        exact.charge(prefix).unwrap();
        exact_graph
            .position_independent_request(HOST_CODE, source, &mut exact)
            .unwrap();
        assert_independent_mapping(&exact_graph);
        assert_eq!(exact.used(), prefix + cost);
        assert!(matches!(
            exact_graph.position_independent_request(HOST_CODE + 1, source, &mut exact),
            Err(Failure::Resource)
        ));
        assert!(!exact_graph.positions.contains_key(&(HOST_CODE + 1)));

        let mut short_graph = graph();
        let source = short_graph.sources[3];
        let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
        short.charge(prefix).unwrap();
        assert!(matches!(
            short_graph.position_independent_request(HOST_CODE, source, &mut short),
            Err(Failure::Resource)
        ));
        assert!(
            !short_graph.positions.contains_key(&HOST_CODE),
            "unpaid mapping must not become a completed value port"
        );
        assert_eq!(short_graph.positions[&NATIVE_CODE], 3);
    }
    for _ in 0..2 {
        let mut fresh_graph = graph();
        let source = fresh_graph.sources[3];
        let mut fresh = TypeWorkBudget::with_limit(cost);
        fresh_graph
            .position_independent_request(HOST_CODE, source, &mut fresh)
            .unwrap();
        assert_independent_mapping(&fresh_graph);
        assert_eq!(fresh.used(), cost);
    }
}
