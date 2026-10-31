import network_types as LedgerTypes
import network_codec as Codec
import @builtin.retained_control as Control
import @builtin.network as Network
import @builtin.bytes as ByteOps

worker<N> : (Network.Worker<N>, Bytes) -> Unit ! {Network.IO<N>}
worker (endpoint, payload) = {
    let ledger = initial_root ()
    let (successor, status) = reserve_job (ledger, 0, LedgerTypes.Root, 1, payload)
    match status {
        Rejected => stop_worker endpoint
        Registered(child) => {
            let closed = close_record (successor, LedgerTypes.Root)
            finish_worker (endpoint, driver (endpoint, closed, 0, 1, RootOpen))
        }
    }
}

peer<N> : (Network.Worker<N>, Bytes) -> Unit ! {Network.IO<N>}
peer (endpoint, payload) = {
    let ledger = initial_worker ()
    finish_worker (endpoint, driver (endpoint, ledger, 1, 0, PeerOpen))
}

stop_worker<N> : Network.Worker<N> -> Unit ! {Network.IO<N>}
stop_worker endpoint = {
    let _ = Network.finish_send endpoint
    ()
}

finish_worker<N> : (Network.Worker<N>, Bool) -> Unit ! {Network.IO<N>}
finish_worker (endpoint, success) = match success {
    true => match Network.finish_receive endpoint {
        Network.Ok => ()
        Network.Failed(_) => stop_worker endpoint
    }
    false => stop_worker endpoint
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

initial_root : Unit -> Ledger
initial_root () = Ledger(0, RecordCons(Record(LedgerTypes.Root, LedgerTypes.NoParent, Open, Empty), NoRecords), NoOutputs)

initial_worker : Unit -> Ledger
initial_worker () = Ledger(0, NoRecords, NoOutputs)



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

finish_close : (Record, Ledger, Int, LedgerTypes.Identity, Records, Outputs) -> Ledger
finish_close (record, ledger, next, wanted, records, outputs) = match record {
    Record(actual, parent, phase, children) => match phase {
        Open => Ledger(next, update_record (wanted, Record(actual, parent, Closed, children), records), outputs)
        Closed => ledger
    }
}

close_record : (Ledger, LedgerTypes.Identity) -> Ledger
close_record (ledger, wanted) = match ledger {
    Ledger(next, records, outputs) => match find_record (wanted, records) {
        NoRecord => ledger
        HasRecord(record) => finish_close (record, ledger, next, wanted, records, outputs)
    }
}

append_record : (Record, Records) -> Records
append_record (added, records) = match records {
    NoRecords => RecordCons(added, NoRecords)
    RecordCons(record, tail) => RecordCons(record, append_record (added, tail))
}

finish_install : (Ledger, LedgerTypes.Identity, LedgerTypes.Parent) -> (Ledger, Bool)
finish_install (ledger, child, parent) = match ledger {
    Ledger(next, records, outputs) => match find_record (child, records) {
        NoRecord => (Ledger(next, append_record (Record(child, parent, Open, Empty), records), outputs), true)
        HasRecord(existing) => (ledger, false)
    }
}

install_received : (Ledger, LedgerTypes.Identity, LedgerTypes.Parent) -> (Ledger, Bool)
install_received (ledger, child, parent) = match child {
    LedgerTypes.Root => (ledger, false)
    LedgerTypes.Work(allocator, serial) => match parent {
        LedgerTypes.NoParent => (ledger, false)
        LedgerTypes.Parent(owner, parent_id) => finish_install (ledger, child, parent)
    }
}

effect Checkpoint<S> {
    checkpoint : Unit -> Unit
}

consume_payload : Bytes -> Unit
consume_payload payload = {
    let _ = ByteOps.length payload
    ()
}

effect DeferredSpawn {
    request : Unit -> Unit
}

type ProcessResult =
    Processed(Ledger)
    | ProtocolError

process_work : (Ledger, LedgerTypes.Identity, LedgerTypes.Parent, Bytes, Int, Int) -> ProcessResult
process_work (installed, child, parent, payload, own, peer) = {
    let (after_cleanup, ready) = handle (cleanup fn(ignored) {
        match parent {
            LedgerTypes.NoParent => ()
            LedgerTypes.Parent(owner, parent_id) => match parent_id {
                LedgerTypes.Root => perform DeferredSpawn.request ()
                LedgerTypes.Work(allocator, serial) => ()
            }
        }
        } {
        let _ = resource Control.Store<S,(Unit -> Unit ! {Control.Drive<S>})> store = () {
            handle {
                let _ = perform Checkpoint<S>.checkpoint ()
                consume_payload payload
            } with Checkpoint<S> using store {
                checkpoint ignored => resume ()
            }
        }
        (installed, true)
    }) with DeferredSpawn {
        request ignored => match (resume ()) {
            (current, _) => {
                let (successor, status) = reserve_job (current, own, child, peer, payload)
                match status {
                    Registered(new_child) => (successor, true)
                    Rejected => (successor, false)
                }
            }
        }
    }
    match ready {
        true => {
            let closed = close_record (after_cleanup, child)
            Processed(retire (closed, child))
        }
        false => ProtocolError
    }
}

handle_work : (Ledger, LedgerTypes.Identity, LedgerTypes.Parent, Bytes, Int, Int) -> ProcessResult
handle_work (ledger, child, parent, payload, own, peer) = match install_received (ledger, child, parent) {
    (successor, installed) => match installed {
        true => process_work (successor, child, parent, payload, own, peer)
        false => ProtocolError
    }
}

handle_parent : (Ledger, LedgerTypes.Parent, LedgerTypes.Identity, Int, Int) -> Ledger
handle_parent (ledger, parent, child, own, peer) = match parent {
    LedgerTypes.NoParent => ledger
    LedgerTypes.Parent(owner, id) => match owner == own {
        true => {
            let acknowledged = acknowledge (ledger, id, child, peer)
            retire (acknowledged, id)
        }
        false => ledger
    }
}

handle_message : (Ledger, Bytes, Network.EnvelopeKind, Int, Int) -> ProcessResult
handle_message (ledger, message, kind, own, peer) = match Codec.decode message {
    Codec.WorkDecoded(child, parent, payload) => match kind {
        Network.Application => handle_work (ledger, child, parent, payload, own, peer)
        Network.Control => ProtocolError
    }
    Codec.AckDecoded(parent, child) => match kind {
        Network.Application => ProtocolError
        Network.Control => match child {
            LedgerTypes.Root => ProtocolError
            LedgerTypes.Work(allocator, serial) => Processed(handle_parent (ledger, parent, child, own, peer))
        }
    }
    Codec.InvalidFrame => ProtocolError
}

root_record_quiet : Record -> Bool
root_record_quiet record = match record {
    Record(id, parent, phase, children) => match phase {
        Open => false
        Closed => match children {
            Empty => true
            More(child, tail) => false
        }
    }
}

root_quiet : Ledger -> Bool
root_quiet ledger = match ledger {
    Ledger(next, records, outputs) => match find_record (LedgerTypes.Root, records) {
        NoRecord => false
        HasRecord(record) => root_record_quiet record
    }
}

type SendState =
    RootOpen
    | RootSealed
    | PeerOpen
type SendStep =
    SentTail(Ledger)
    | FullHead(Ledger)
    | SendStop
    | NoPending

transmit<N> : (Network.Worker<N>, Ledger, Int, Records, LedgerTypes.Envelope, Outputs, Bytes) -> SendStep ! {Network.IO<N>}
transmit (endpoint, ledger, next, records, head, tail, bytes) = {
    let result = match head {
        LedgerTypes.WorkOut(_, _, _, _) => Network.try_send (endpoint, bytes)
        LedgerTypes.AckOut(_, _) => Network.send_control (endpoint, bytes)
    }
    match result {
        Network.Sent => {
            let successor = Ledger(next, records, tail)
            SentTail(successor)
        }
        Network.Full => FullHead(ledger)
        Network.Closed => SendStop
        Network.SendFailed(_) => SendStop
    }
}

type ReceiptStep =
    NextReceipt(Ledger)
    | ReceiveEnd
    | ReceiveStop

inspect_outputs<N> : (Network.Worker<N>, Ledger) -> SendStep ! {Network.IO<N>}
inspect_outputs (endpoint, ledger) = {
    let Ledger(next, records, outputs) = ledger
    match outputs {
        NoOutputs => NoPending
        OutputCons(head, tail) => match Codec.encode head {
            Codec.Encoded(bytes) => transmit (endpoint, ledger, next, records, head, tail, bytes)
            Codec.EncodeFailed => SendStop
        }
    }
}

type PollOrigin =
    AfterNoPending
    | AfterFull
type DriverStep =
    Continue(Ledger, SendState)
    | Poll(Ledger, PollOrigin)
    | Stop

driver<N> : (Network.Worker<N>, Ledger, Int, Int, SendState) -> Bool ! {Network.IO<N>}
driver (endpoint, ledger, own, peer, send_state) = {
    let action = match inspect_outputs (endpoint, ledger) {
        NoPending => {
            let quiet = match send_state {
                RootOpen => root_quiet ledger
                _ => false
            }
            match quiet {
                true => match Network.finish_send endpoint {
                    Network.Ok => Continue(ledger, RootSealed)
                    Network.Failed(_) => Stop
                }
                false => Poll(ledger, AfterNoPending)
            }
        }
        SentTail(successor) => Continue(successor, send_state)
        FullHead(original) => Poll(original, AfterFull)
        SendStop => Stop
    }
    match action {
        Continue(next, next_state) => driver (endpoint, next, own, peer, next_state)
        Poll(current, origin) => match receive_once (endpoint, current, own, peer) {
            NextReceipt(next) => driver (endpoint, next, own, peer, send_state)
            ReceiveEnd => match origin {
                AfterNoPending => finish_after_end (endpoint, send_state)
                AfterFull => false
            }
            ReceiveStop => false
        }
        Stop => false
    }
}

finish_after_end<N> : (Network.Worker<N>, SendState) -> Bool ! {Network.IO<N>}
finish_after_end (endpoint, send_state) = match send_state {
    RootSealed => true
    PeerOpen => match Network.finish_send endpoint {
        Network.Ok => true
        Network.Failed(_) => false
    }
    RootOpen => false
}

receive_once<N> : (Network.Worker<N>, Ledger, Int, Int) -> ReceiptStep ! {Network.IO<N>}
receive_once (endpoint, ledger, own, peer) = match Network.try_receive endpoint {
    Network.Message(kind, message) => match handle_message (ledger, message, kind, own, peer) {
        Processed(next) => NextReceipt(next)
        ProtocolError => ReceiveStop
    }
    Network.Empty => NextReceipt(ledger)
    Network.End => ReceiveEnd
    Network.ReceiveFailed(_) => ReceiveStop
}

pub run : Unit -> Int
run () = {
    let input = ByteOps.empty ()
    resource Network.Pair<N> pair = (1, worker, peer, input, input) {
        match Network.settle pair {
            Network.Ok => 42
            Network.Failed(_) => 0
        }
    }
}
