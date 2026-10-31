import network_types as LedgerTypes
import @builtin.network as Network
import @builtin.bytes as ByteOps

driver<N> : (Network.Worker<N>, Ledger) -> Unit ! {Network.IO<N>}
driver (endpoint, ledger) = match Network.try_receive endpoint {
    Network.Message(Network.Application, message) => match reserve_job (ledger, 0, LedgerTypes.Root, 0, message) {
        (successor, status) => driver (endpoint, successor)
    }
    Network.Message(Network.Control, _) => ()
    Network.Empty => driver (endpoint, ledger)
    Network.End => ()
    Network.ReceiveFailed(_) => ()
}

worker<N> : (Network.Worker<N>, Bytes) -> Unit ! {Network.IO<N>}
worker (endpoint, payload) = {
    let ledger = initial ()
    driver (endpoint, ledger)
}

main : Unit -> Unit
main () = {
    resource Network.Pair<N> pair = (1, worker, worker, ByteOps.empty (), ByteOps.empty ()) {
        ()
    }
}


type Child = Child(LedgerTypes.Identity, Int)
type Children =
    Empty
    | More(Child, Children)
type Phase =
    Open
    | Closed
type Record = Record(LedgerTypes.Identity, LedgerTypes.Parent, Phase, Children)
type Records =
    NoRecords
    | RecordCons(Record, Records)
type Outputs =
    NoOutputs
    | OutputCons(LedgerTypes.Envelope, Outputs)
type Ledger = Ledger(Int, Records, Outputs)
type Removal =
    Found
    | Missing

same_id : (LedgerTypes.Identity, LedgerTypes.Identity) -> Bool
same_id (left, right) = match (left, right) {
    (LedgerTypes.Root, LedgerTypes.Root) => true
    (LedgerTypes.Work(a, b), LedgerTypes.Work(c, d)) => match a == c {
        true => b == d
        false => false
    }
    _ => false
}

child_id : Child -> LedgerTypes.Identity
child_id entry = match entry {
    Child(actual, destination) => actual
}

remove_child : (LedgerTypes.Identity, Children) -> (Children, Removal)
remove_child (wanted, children) = match children {
    Empty => (Empty, Missing)
    More(entry, tail) => match same_id (child_id entry, wanted) {
        true => (tail, Found)
        false => match remove_child (wanted, tail) {
            (remaining, status) => (More(entry, remaining), status)
        }
    }
}

initial : Unit -> Ledger
initial () = Ledger(0, RecordCons(Record(LedgerTypes.Root, LedgerTypes.NoParent, Open, Empty), NoRecords), NoOutputs)



type RecordLookup =
    NoRecord
    | HasRecord(Record)
type Registration =
    Rejected
    | Registered(LedgerTypes.Identity)

record_id : Record -> LedgerTypes.Identity
record_id record = match record {
    Record(actual, parent, phase, children) => actual
}

find_record : (LedgerTypes.Identity, Records) -> RecordLookup
find_record (wanted, records) = match records {
    NoRecords => NoRecord
    RecordCons(record, tail) => match same_id (record_id record, wanted) {
        true => HasRecord(record)
        false => find_record (wanted, tail)
    }
}

update_record : (LedgerTypes.Identity, Record, Records) -> Records
update_record (wanted, replacement, records) = match records {
    NoRecords => NoRecords
    RecordCons(record, tail) => match same_id (record_id record, wanted) {
        true => RecordCons(replacement, tail)
        false => RecordCons(record, update_record (wanted, replacement, tail))
    }
}

append_child : (Child, Children) -> Children
append_child (added, children) = match children {
    Empty => More(added, Empty)
    More(child, tail) => More(child, append_child (added, tail))
}

append_output : (LedgerTypes.Envelope, Outputs) -> Outputs
append_output (added, outputs) = match outputs {
    NoOutputs => OutputCons(added, NoOutputs)
    OutputCons(output, tail) => OutputCons(output, append_output (added, tail))
}

commit_registration : (Int, Int, LedgerTypes.Identity, Int, Bytes, Records, Outputs, LedgerTypes.Parent, Children) -> (Ledger, Registration)
commit_registration (next, owner, wanted, destination, payload, records, outputs, parent, children) = {
    let child = LedgerTypes.Work(owner, next)
    let replacement = Record(wanted, parent, Open, append_child (Child(child, destination), children))
    let remaining = update_record (wanted, replacement, records)
    let outgoing = append_output (LedgerTypes.WorkOut(child, LedgerTypes.Parent(owner, wanted), destination, payload), outputs)
    (Ledger(next + 1, remaining, outgoing), Registered(child))
}

finish_registration : (Record, Ledger, Int, Int, LedgerTypes.Identity, Int, Bytes, Records, Outputs) -> (Ledger, Registration)
finish_registration (record, ledger, next, owner, wanted, destination, payload, records, outputs) = match record {
    Record(actual, parent, phase, children) => match phase {
        Closed => (ledger, Rejected)
        Open => commit_registration (next, owner, wanted, destination, payload, records, outputs, parent, children)
    }
}

reserve_job : (Ledger, Int, LedgerTypes.Identity, Int, Bytes) -> (Ledger, Registration)
reserve_job (ledger, owner, wanted, destination, payload) = match ledger {
    Ledger(next, records, outputs) => match find_record (wanted, records) {
        NoRecord => (ledger, Rejected)
        HasRecord(record) => finish_registration (record, ledger, next, owner, wanted, destination, payload, records, outputs)
    }
}


remove_record : (LedgerTypes.Identity, Records) -> (Records, Removal)
remove_record (wanted, records) = match records {
    NoRecords => (NoRecords, Missing)
    RecordCons(entry, tail) => match same_id (record_id entry, wanted) {
        true => (tail, Found)
        false => match remove_record (wanted, tail) {
            (remaining, status) => (RecordCons(entry, remaining), status)
        }
    }
}


commit_retirement : (Int, LedgerTypes.Identity, Records, Outputs, LedgerTypes.Parent) -> Ledger
commit_retirement (next, wanted, records, outputs, parent) = match remove_record (wanted, records) {
    (remaining, status) => Ledger(next, remaining, append_output (LedgerTypes.AckOut(parent, wanted), outputs))
}

retire_children : (Children, Ledger, Int, LedgerTypes.Identity, Records, Outputs, LedgerTypes.Parent) -> Ledger
retire_children (children, ledger, next, wanted, records, outputs, parent) = match children {
    Empty => commit_retirement (next, wanted, records, outputs, parent)
    More(child, tail) => ledger
}

retire_phase : (Phase, Children, Ledger, Int, LedgerTypes.Identity, Records, Outputs, LedgerTypes.Parent) -> Ledger
retire_phase (phase, children, ledger, next, wanted, records, outputs, parent) = match phase {
    Open => ledger
    Closed => retire_children (children, ledger, next, wanted, records, outputs, parent)
}

retire_parent : (LedgerTypes.Parent, Phase, Children, Ledger, Int, LedgerTypes.Identity, Records, Outputs) -> Ledger
retire_parent (parent, phase, children, ledger, next, wanted, records, outputs) = match parent {
    LedgerTypes.NoParent => ledger
    LedgerTypes.Parent(owner, id) => retire_phase (phase, children, ledger, next, wanted, records, outputs, parent)
}

retire_found : (Record, Ledger, Int, LedgerTypes.Identity, Records, Outputs) -> Ledger
retire_found (record, ledger, next, wanted, records, outputs) = match record {
    Record(actual, parent, phase, children) => retire_parent (parent, phase, children, ledger, next, wanted, records, outputs)
}

retire_work : (Ledger, Int, LedgerTypes.Identity, Records, Outputs) -> Ledger
retire_work (ledger, next, wanted, records, outputs) = match find_record (wanted, records) {
    NoRecord => ledger
    HasRecord(record) => retire_found (record, ledger, next, wanted, records, outputs)
}

retire : (Ledger, LedgerTypes.Identity) -> Ledger
retire (ledger, wanted) = match ledger {
    Ledger(next, records, outputs) => match wanted {
        LedgerTypes.Root => ledger
        LedgerTypes.Work(owner, serial) => retire_work (ledger, next, wanted, records, outputs)
    }
}

type ChildLookup =
    NoChild
    | HasChild(Child)


find_child : (LedgerTypes.Identity, Children) -> ChildLookup
find_child (wanted, children) = match children {
    Empty => NoChild
    More(entry, tail) => match same_id (child_id entry, wanted) {
        true => HasChild(entry)
        false => find_child (wanted, tail)
    }
}

ack_commit : (Int, LedgerTypes.Identity, LedgerTypes.Identity, Records, Outputs, LedgerTypes.Identity, LedgerTypes.Parent, Phase, Children) -> Ledger
ack_commit (next, parent_id, child_id, records, outputs, actual, parent, phase, children) = match remove_child (child_id, children) {
    (remaining, status) => Ledger(next, update_record (parent_id, Record(actual, parent, phase, remaining), records), outputs)
}

ack_child : (Child, Ledger, Int, LedgerTypes.Identity, LedgerTypes.Identity, Int, Records, Outputs, LedgerTypes.Identity, LedgerTypes.Parent, Phase, Children) -> Ledger
ack_child (entry, ledger, next, parent_id, child_id, peer, records, outputs, actual, parent, phase, children) = match entry {
    Child(id, destination) => match destination == peer {
        false => ledger
        true => ack_commit (next, parent_id, child_id, records, outputs, actual, parent, phase, children)
    }
}

ack_found : (Record, Ledger, Int, LedgerTypes.Identity, LedgerTypes.Identity, Int, Records, Outputs) -> Ledger
ack_found (record, ledger, next, parent_id, child_id, peer, records, outputs) = match record {
    Record(actual, parent, phase, children) => match find_child (child_id, children) {
        NoChild => ledger
        HasChild(entry) => ack_child (entry, ledger, next, parent_id, child_id, peer, records, outputs, actual, parent, phase, children)
    }
}

acknowledge : (Ledger, LedgerTypes.Identity, LedgerTypes.Identity, Int) -> Ledger
acknowledge (ledger, parent_id, child_id, peer) = match ledger {
    Ledger(next, records, outputs) => match find_record (parent_id, records) {
        NoRecord => ledger
        HasRecord(record) => ack_found (record, ledger, next, parent_id, child_id, peer, records, outputs)
    }
}
