finish_close : (Record, Ledger, Int, Identity, Records, Outputs) -> Ledger
finish_close (record, ledger, next, wanted, records, outputs) = match record {
    Record(actual, parent, phase, children) => match phase {
        Open => Ledger(next, update_record (wanted, Record(actual, parent, Closed, children), records), outputs)
        Closed => ledger
    }
}

close_record : (Ledger, Identity) -> Ledger
close_record (ledger, wanted) = match ledger {
    Ledger(next, records, outputs) => match find_record (wanted, records) {
        NoRecord => ledger
        HasRecord(record) => finish_close (record, ledger, next, wanted, records, outputs)
    }
}
