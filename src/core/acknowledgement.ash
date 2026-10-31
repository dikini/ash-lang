type RecordLookup =
    NoRecord
    | HasRecord(Record)
type ChildLookup =
    NoChild
    | HasChild(Child)

record_id : Record -> Identity
record_id record = match record {
    Record(actual, parent, phase, children) => actual
}

find_record : (Identity, Records) -> RecordLookup
find_record (wanted, records) = match records {
    NoRecords => NoRecord
    RecordCons(record, tail) => match same_id (record_id record, wanted) {
        true => HasRecord(record)
        false => find_record (wanted, tail)
    }
}

update_record : (Identity, Record, Records) -> Records
update_record (wanted, replacement, records) = match records {
    NoRecords => NoRecords
    RecordCons(record, tail) => match same_id (record_id record, wanted) {
        true => RecordCons(replacement, tail)
        false => RecordCons(record, update_record (wanted, replacement, tail))
    }
}

find_child : (Identity, Children) -> ChildLookup
find_child (wanted, children) = match children {
    Empty => NoChild
    More(entry, tail) => match same_id (child_id entry, wanted) {
        true => HasChild(entry)
        false => find_child (wanted, tail)
    }
}

ack_commit : (Int, Identity, Identity, Records, Outputs, Identity, Parent, Phase, Children) -> Ledger
ack_commit (next, parent_id, child_id, records, outputs, actual, parent, phase, children) = match remove_child (child_id, children) {
    (remaining, status) => Ledger(next, update_record (parent_id, Record(actual, parent, phase, remaining), records), outputs)
}

ack_child : (Child, Ledger, Int, Identity, Identity, Int, Records, Outputs, Identity, Parent, Phase, Children) -> Ledger
ack_child (entry, ledger, next, parent_id, child_id, peer, records, outputs, actual, parent, phase, children) = match entry {
    Child(id, destination) => match destination == peer {
        false => ledger
        true => ack_commit (next, parent_id, child_id, records, outputs, actual, parent, phase, children)
    }
}

ack_found : (Record, Ledger, Int, Identity, Identity, Int, Records, Outputs) -> Ledger
ack_found (record, ledger, next, parent_id, child_id, peer, records, outputs) = match record {
    Record(actual, parent, phase, children) => match find_child (child_id, children) {
        NoChild => ledger
        HasChild(entry) => ack_child (entry, ledger, next, parent_id, child_id, peer, records, outputs, actual, parent, phase, children)
    }
}

acknowledge : (Ledger, Identity, Identity, Int) -> Ledger
acknowledge (ledger, parent_id, child_id, peer) = match ledger {
    Ledger(next, records, outputs) => match find_record (parent_id, records) {
        NoRecord => ledger
        HasRecord(record) => ack_found (record, ledger, next, parent_id, child_id, peer, records, outputs)
    }
}
