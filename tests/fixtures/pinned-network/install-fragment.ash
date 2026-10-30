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
