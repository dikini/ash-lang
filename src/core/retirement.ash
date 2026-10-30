type RecordLookup =
    NoRecord
    | HasRecord(Record)

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

remove_record : (Identity, Records) -> (Records, Removal)
remove_record (wanted, records) = match records {
    NoRecords => (NoRecords, Missing)
    RecordCons(entry, tail) => match same_id (record_id entry, wanted) {
        true => (tail, Found)
        false => match remove_record (wanted, tail) {
            (remaining, status) => (RecordCons(entry, remaining), status)
        }
    }
}

append_output : (Envelope, Outputs) -> Outputs
append_output (added, outputs) = match outputs {
    NoOutputs => OutputCons(added, NoOutputs)
    OutputCons(output, tail) => OutputCons(output, append_output (added, tail))
}

commit_retirement : (Int, Identity, Records, Outputs, Parent) -> Ledger
commit_retirement (next, wanted, records, outputs, parent) = match remove_record (wanted, records) {
    (remaining, status) => Ledger(next, remaining, append_output (AckOut(parent, wanted), outputs))
}

retire_children : (Children, Ledger, Int, Identity, Records, Outputs, Parent) -> Ledger
retire_children (children, ledger, next, wanted, records, outputs, parent) = match children {
    Empty => commit_retirement (next, wanted, records, outputs, parent)
    More(child, tail) => ledger
}

retire_phase : (Phase, Children, Ledger, Int, Identity, Records, Outputs, Parent) -> Ledger
retire_phase (phase, children, ledger, next, wanted, records, outputs, parent) = match phase {
    Open => ledger
    Closed => retire_children (children, ledger, next, wanted, records, outputs, parent)
}

retire_parent : (Parent, Phase, Children, Ledger, Int, Identity, Records, Outputs) -> Ledger
retire_parent (parent, phase, children, ledger, next, wanted, records, outputs) = match parent {
    NoParent => ledger
    Parent(owner, id) => retire_phase (phase, children, ledger, next, wanted, records, outputs, parent)
}

retire_found : (Record, Ledger, Int, Identity, Records, Outputs) -> Ledger
retire_found (record, ledger, next, wanted, records, outputs) = match record {
    Record(actual, parent, phase, children) => retire_parent (parent, phase, children, ledger, next, wanted, records, outputs)
}

retire_work : (Ledger, Int, Identity, Records, Outputs) -> Ledger
retire_work (ledger, next, wanted, records, outputs) = match find_record (wanted, records) {
    NoRecord => ledger
    HasRecord(record) => retire_found (record, ledger, next, wanted, records, outputs)
}

retire : (Ledger, Identity) -> Ledger
retire (ledger, wanted) = match ledger {
    Ledger(next, records, outputs) => match wanted {
        Root => ledger
        Work(owner, serial) => retire_work (ledger, next, wanted, records, outputs)
    }
}
