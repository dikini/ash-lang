//! Static declared owner-dependency correspondence; no evaluator/native entry.

use super::*;

const DEPENDENT: &str = include_str!("../../tests/fixtures/checked-owner-dependencies/owner.ash");
const CONSUMER: &str = "import @builtin.foreign as Foreign\nimport producer as Producer\nmain : Unit -> Foreign.CheckedScope<Foreign.CheckedScope<Int, Unit, Unit>, Unit, Unit>\nmain () = Producer.run ()\n";

#[test]
fn checked_owner_dependency_canonical_source_retains_exact_parent() {
    let canonical = check_graph(&graph(PRODUCER, false))
        .expect("existing dependency-free checked lifecycle is the positive setup");
    assert_producer_originals(&canonical);
    let graph = graph_with_entry(DEPENDENT, Some(CONSUMER));
    let checked = check_graph(&graph)
        .expect("declared checked child dependency must survive source and body-free checking");
    let producer = checked
        .iter()
        .find(|module| module.source_resource_code().is_some())
        .expect("actual dependent producer retains immutable original resource forests");
    let child = producer
        .source_resource_code()
        .unwrap()
        .headers()
        .find(|header| header.original.spelling == "Child")
        .expect("actual checked child header");
    assert_eq!(child.original.parameters[0].spelling, "H");
    assert_eq!(child.original.parameters[1].spelling, "C");
    assert_eq!(child.original.parameters[2].spelling, "S");
    assert_eq!(
        child.dependencies.as_ref(),
        &[child.original.parameters[1].id]
    );
    assert_ne!(child.dependencies[0], child.original.parameters[2].id);
    assert_eq!(child.owner.owner().retained_parameters(), &[1]);
    assert!(child.owner.prepared().checked_contract().is_some());
    assert!(
        producer
            .exports()
            .source_resource_facts()
            .any(|header| Arc::ptr_eq(header, &child.original))
    );
    validate_latest_payload_core(&graph);
}
