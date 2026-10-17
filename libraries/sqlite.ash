import @builtin.string as Text
import @builtin.bytes as B
import @builtin.foreign as Foreign
pub foreign library NativeSqlite {
    profile "x86_64-unknown-linux-gnu"
    repr CInt = signed(32)
    repr Address = opaque
    repr InputAddress = bytes
    repr Destructor = function_address
    sentinel Transient : Destructor = all_bits_one
    const NativeOk : CInt = 0
    const ReadWriteCreate : CInt = 6
    owner ConnectionState<C> {
        representation Address
        owned C
        teardown Close
    }
    repr I64 = signed(64)
    const NativeRow : CInt = 100
    const NativeDone : CInt = 101
    const NegativeOne : I64 = -1
    owner StatementState<C, S> {
        representation Address
        owned S
        retains C
        teardown Finalize
    }
    symbol Prepare<C, S> : (ConnectionState<C>, String, Int) -> Foreign.Call<(Int, Foreign.Output<Foreign.Nullable<StatementState<C, S>>>, Foreign.Output<Foreign.Nullable<Int>>)> {
        name "sqlite3_prepare_v2"
        abi (pointer(Address), pointer(InputAddress), CInt, out(pointer(Address)), out(pointer(InputAddress))) -> CInt
        operand 0 from 0 enclosing
        operand 1 from 1 nul call_borrow
        operand 2 from 2 scalar
        output result as scalar
        output 3 as owner(StatementState<C, S>)
        output 4 as offset_into(1)
        outcome result == NativeOk { readable result, readable 3, readable 4 }
        outcome otherwise { readable result, readable 3, unreadable 4 }
    }
    symbol Step<C, S> : StatementState<C, S> -> Foreign.Call<Int> {
        name "sqlite3_step"
        abi (pointer(Address)) -> CInt
        operand 0 from 0 current
        output result as scalar
        outcome otherwise { readable result }
    }
    symbol ColumnInt<C, S> : (StatementState<C, S>, Int) -> Foreign.Call<Int> {
        name "sqlite3_column_int64"
        abi (pointer(Address), CInt) -> I64
        operand 0 from 0 current
        operand 1 from 1 scalar
        output result as scalar
        outcome otherwise { readable result }
    }
    symbol Finalize<C, S> : StatementState<C, S> -> Foreign.Call<Foreign.Disposition<Int>> {
        name "sqlite3_finalize"
        abi (pointer(Address)) -> CInt
        operand 0 from 0 current
        output result as scalar
        retained_dependents block
        outcome otherwise { readable result, consumed 0 }
    }
    symbol ColumnCount<C, S> : StatementState<C, S> -> Foreign.Call<Int> {
        name "sqlite3_column_count"
        abi (pointer(Address)) -> CInt
        operand 0 from 0 current
        output result as scalar
        outcome otherwise { readable result }
    }
    symbol ColumnType<C, S> : (StatementState<C, S>, Int) -> Foreign.Call<Int> {
        name "sqlite3_column_type"
        abi (pointer(Address), CInt) -> CInt
        operand 0 from 0 current
        operand 1 from 1 scalar
        output result as scalar
        outcome otherwise { readable result }
    }
    access BlobView<W, C, S> {
        window W
        owner StatementState<C, S>
        extent bytes
        preserves ColumnBlob, ColumnBlobExtent
    }
    symbol ColumnBlob<W, C, S> : (StatementState<C, S>, Int) -> Foreign.Call<Foreign.Output<Foreign.Nullable<BlobView<W, C, S>>>> {
        name "sqlite3_column_blob"
        abi (pointer(Address), CInt) -> pointer(InputAddress)
        operand 0 from 0 current
        operand 1 from 1 scalar
        output result as view(BlobView<W, C, S>, 1)
        outcome otherwise { readable result }
    }
    symbol ColumnBlobExtent<W, C, S> : (StatementState<C, S>, Int, BlobView<W, C, S>) -> Foreign.Call<Foreign.Extent<BlobView<W, C, S>>> {
        name "sqlite3_column_bytes"
        abi (pointer(Address), CInt) -> CInt
        operand 0 from 0 current
        operand 1 from 1 scalar
        output result as extent_of(2, 1)
        outcome otherwise { readable result }
    }
    access TextView<W, C, S> {
        window W
        owner StatementState<C, S>
        extent bytes
        preserves ColumnText, ColumnTextExtent
    }
    symbol ColumnText<W, C, S> : (StatementState<C, S>, Int) -> Foreign.Call<Foreign.Output<Foreign.Nullable<TextView<W, C, S>>>> {
        name "sqlite3_column_text"
        abi (pointer(Address), CInt) -> pointer(InputAddress)
        operand 0 from 0 current
        operand 1 from 1 scalar
        output result as view(TextView<W, C, S>, 1)
        outcome otherwise { readable result }
    }
    symbol ColumnTextExtent<W, C, S> : (StatementState<C, S>, Int, TextView<W, C, S>) -> Foreign.Call<Foreign.Extent<TextView<W, C, S>>> {
        name "sqlite3_column_bytes"
        abi (pointer(Address), CInt) -> CInt
        operand 0 from 0 current
        operand 1 from 1 scalar
        output result as extent_of(2, 1)
        outcome otherwise { readable result }
    }
    symbol ColumnByteLength<C, S> : (StatementState<C, S>, Int) -> Foreign.Call<Int> {
        name "sqlite3_column_bytes"
        abi (pointer(Address), CInt) -> CInt
        operand 0 from 0 current
        operand 1 from 1 scalar
        output result as scalar
        outcome otherwise { readable result }
    }
    access DiagnosticView<W, C> {
        window W
        owner ConnectionState<C>
        extent nul
        preserves ErrorMessage
    }
    symbol ErrorMessage<W, C> : ConnectionState<C> -> Foreign.Call<Foreign.Output<Foreign.Nullable<DiagnosticView<W, C>>>> {
        name "sqlite3_errmsg"
        abi (pointer(Address)) -> pointer(InputAddress)
        operand 0 from 0 current
        output result as view(DiagnosticView<W, C>)
        outcome otherwise { readable result }
    }
    symbol ErrorCode<C> : ConnectionState<C> -> Foreign.Call<Int> {
        name "sqlite3_errcode"
        abi (pointer(Address)) -> CInt
        operand 0 from 0 current
        output result as scalar
        outcome otherwise { readable result }
    }
    symbol BindInt<C, S> : (StatementState<C, S>, Int, Int) -> Foreign.Call<Int> {
        name "sqlite3_bind_int64"
        abi (pointer(Address), CInt, I64) -> CInt
        operand 0 from 0 current
        operand 1 from 1 scalar
        operand 2 from 2 scalar
        output result as scalar
        outcome otherwise { readable result }
    }
    symbol BindBlob<C, S> : (StatementState<C, S>, Int, Bytes, Int) -> Foreign.Call<Int> {
        name "sqlite3_bind_blob"
        abi (pointer(Address), CInt, pointer(InputAddress), CInt, Destructor) -> CInt
        operand 0 from 0 current
        operand 1 from 1 scalar
        operand 2 from 2 bytes(3) copy
        operand 3 from 3 scalar
        operand 4 from constant Transient
        output result as scalar
        outcome otherwise { readable result }
    }
    symbol BindText<C, S> : (StatementState<C, S>, Int, String, Int) -> Foreign.Call<Int> {
        name "sqlite3_bind_text"
        abi (pointer(Address), CInt, pointer(InputAddress), CInt, Destructor) -> CInt
        operand 0 from 0 current
        operand 1 from 1 scalar
        operand 2 from 2 bytes(3) copy
        operand 3 from 3 scalar
        operand 4 from constant Transient
        output result as scalar
        outcome otherwise { readable result }
    }
    symbol BindNull<C, S> : (StatementState<C, S>, Int) -> Foreign.Call<Int> {
        name "sqlite3_bind_null"
        abi (pointer(Address), CInt) -> CInt
        operand 0 from 0 current
        operand 1 from 1 scalar
        output result as scalar
        outcome otherwise { readable result }
    }
    symbol Reset<C, S> : StatementState<C, S> -> Foreign.Call<Int> {
        name "sqlite3_reset"
        abi (pointer(Address)) -> CInt
        operand 0 from 0 current
        output result as scalar
        outcome otherwise { readable result }
    }
    symbol ClearBindings<C, S> : StatementState<C, S> -> Foreign.Call<Int> {
        name "sqlite3_clear_bindings"
        abi (pointer(Address)) -> CInt
        operand 0 from 0 current
        output result as scalar
        outcome otherwise { readable result }
    }
    symbol Initialize : Unit -> Foreign.Call<Int> {
        name "sqlite3_initialize"
        abi () -> CInt
        output result as scalar
        outcome otherwise { readable result }
    }
    symbol Open<C> : String -> Foreign.Call<(Int, Foreign.Output<Foreign.Nullable<ConnectionState<C>>>)> {
        name "sqlite3_open_v2"
        abi (pointer(InputAddress), out(pointer(Address)), CInt, pointer(InputAddress)) -> CInt
        operand 0 from 0 nul call_borrow
        operand 2 from constant ReadWriteCreate
        operand 3 from null
        output result as scalar
        output 1 as owner(ConnectionState<C>)
        outcome otherwise { readable result, readable 1 }
    }
    symbol Close<C> : ConnectionState<C> -> Foreign.Call<Foreign.Disposition<Int>> {
        name "sqlite3_close"
        abi (pointer(Address)) -> CInt
        operand 0 from 0 current
        output result as scalar
        retained_dependents block
        outcome result == NativeOk { readable result, consumed 0 }
        outcome otherwise { readable result, retained 0 }
    }
}
pub type OpenConfig = InMemory
    | File(String)
pub memory : Unit -> OpenConfig
memory () = InMemory
pub type OpenError = InvalidPath
    | InitializationFailed(Int)
    | InitializationRefused
    | NativeOpen(Int)
type Initialization = Initialized
    | InitializationError(OpenError)
initialization : Foreign.Call<Int> -> Initialization
initialization reply = match reply {
    Foreign.Returned(code) => match code == NativeOk {
        true => Initialized
        false => InitializationError (InitializationFailed code)
    }
    Foreign.ConversionFailed(_) => InitializationError InitializationRefused
}
pub type CloseError = NativeClose(Int)
    | BlockedByStatement
    | InvalidClose
pub type Acquire<S, D, I> = Acquired(S, D)
    | Refused(I)
pub type Finish<S, E> = Consumed
    | ConsumedFailure(E)
    | Retained(S, E)
pub type Completion<E> = Closed
    | ConsumedError(E)
    | RetainedError(E)
pub type Scope<I, E, T> = NotAcquired(I)
    | Completed(T, Completion<E>)
pub interface ConnectionProvider<C> {
    borrow : Connection<C> -> ConnectionState<C> ! {ConnectionOps<C>}
    error_code : Connection<C> -> Result<Int> ! {ConnectionOps<C>}
    diagnostic : Connection<C> -> Error ! {ConnectionOps<C>}
    is_open : Connection<C> -> Bool ! {ConnectionOps<C>}
}
pub effect ConnectionOps<C> {
    borrow : Connection<C> -> ConnectionState<C>
    error_code : Connection<C> -> Result<Int>
    diagnostic : Connection<C> -> Error
    is_open : Connection<C> -> Bool
}
pub resource Connection<C> {
    owned C
    input OpenConfig
    state ConnectionState<C>
    data Unit
    acquisition Acquire<ConnectionState<C>, Unit, OpenError>
    completion Finish<ConnectionState<C>, CloseError>
    result Scope<OpenError, CloseError, Answer> for <Answer>
    codec scope
    provider ConnectionProvider<C>
    effect ConnectionOps<C>
    interpret Open<C>, Close<C>, ErrorCode<C>
    acquire config => {
        let path = match config {
            InMemory => ":memory:"
            File(path) => path
        }
        let validated = match Foreign.checked_nul path {
            Foreign.Returned(_) => Initialized
            Foreign.ConversionFailed(_) => InitializationError InvalidPath
        }
        let initialized = match validated {
            Initialized => initialization (perform Initialize.call ())
            InitializationError(error) => InitializationError error
        }
        match initialized {
            Initialized => match perform Open<C>.call path {
                Foreign.Returned((code, Foreign.Readable(Foreign.NonNull(state)))) => match code == NativeOk {
                    true => Acquired(state, ())
                    false => Refused (NativeOpen code)
                }
                Foreign.Returned((code, _)) => Refused (NativeOpen code)
                Foreign.ConversionFailed(_) => Refused InvalidPath
            }
            InitializationError(error) => Refused error
        }
    }
    finish (state, data) => match perform Close<C>.call state {
        Foreign.Returned(Foreign.Consumed(code)) => match code == NativeOk {
            true => Consumed
            false => ConsumedFailure (NativeClose code)
        }
        Foreign.Returned(Foreign.Retained(code)) => Retained(state, NativeClose code)
        Foreign.Returned(Foreign.BlockedDependent) => Retained(state, BlockedByStatement)
        Foreign.ConversionFailed(_) => Retained(state, InvalidClose)
    }
    handlers (state, data) {
        borrow access => resume state
        error_code access => resume (column_int_result (perform ErrorCode<C>.call state))
        diagnostic access => {
            let code = column_int_result (perform ErrorCode<C>.call state)
            let result = match code {
                Err(error) => error
                Ok(code) => {
                    let copied = copy_window DiagnosticView<W, C> from state {
                        match perform ErrorMessage<W, C>.call state {
                            Foreign.Returned(Foreign.Readable(Foreign.NonNull(view))) => Foreign.copy_nul (view, 327680)
                            Foreign.Returned(_) => Foreign.Returned (Text.to_utf8 "")
                            Foreign.ConversionFailed(error) => Foreign.ConversionFailed error
                        }
                    }
                    ForeignError (NativeDiagnostic (diagnostic_copy (code, copied)))
                }
            }
            resume result
        }
        is_open access => resume true
    }
}

pub type Diagnostic = Diagnostic(Int, String)
    | DiagnosticUnavailable(Int)
pub diagnostic_copy : (Int, Foreign.Call<Bytes>) -> Diagnostic
diagnostic_copy (code, reply) = match reply {
    Foreign.Returned(bytes) => match Text.from_utf8 bytes {
        Text.Decoded(text) => Diagnostic(code, text)
        Text.InvalidUtf8 => DiagnosticUnavailable code
    }
    Foreign.ConversionFailed(_) => DiagnosticUnavailable code
}

pub type NativeError = NativeStatus(Int)
    | InputFailure(InputFault)
    | ProtocolFailure(ProtocolFault)
    | ConversionFailure
    | NativeDiagnostic(Diagnostic)
pub type InputFault = BadIndex
    | BadInteger
    | BadBytes
    | BadText
    | BadColumn
    | ColumnTypeMismatch
pub type ProtocolFault = NotPrepared
    | NotRow
    | AfterDone
pub type Error = ForeignError(NativeError)
    | MissingRow
    | UnexpectedRow
pub type Result<T> = Ok(T)
    | Err(Error)
pub type StepResult = Row
    | Done
    | StepError(Error)
pub type PrepareError = InvalidSql
    | PrepareFailed(Int)
    | EmptySql
    | InvalidTail
prepare_absent_output : (Int, PrepareError) -> PrepareError
prepare_absent_output (code, absent) = match code == NativeOk {
    true => absent
    false => PrepareFailed code
}
pub type FinalizeError = NativeFinalize(Int)
    | InvalidFinalize
ascii_space : Int -> Bool
ascii_space byte = {
    let first = match byte == 9 {
        true => true
        false => byte == 10
    }
    let second = byte == 12
    let third = match byte == 13 {
        true => true
        false => byte == 32
    }
    match first {
        true => true
        false => match second {
            true => true
            false => third
        }
    }
}
tail_whitespace : (Bytes, Int) -> Bool
tail_whitespace (bytes, offset) = match offset == B.length bytes {
    true => true
    false => match B.at (bytes, offset) {
        B.InvalidIndex => false
        B.ByteAt(byte) => match ascii_space byte {
            true => tail_whitespace (bytes, offset + 1)
            false => false
        }
    }
}
valid_tail : (String, Int) -> Bool
valid_tail (sql, offset) = tail_whitespace (Text.to_utf8 sql, offset)
pub type BytesOrNull = NullBytes
    | BlobBytes(Bytes)
pub type TextOrNull = NullText
    | TextValue(String)
type BlobProbe = CopiedBlob(Bytes)
    | EmptyBlob
    | NullBlobPointer
    | SqlNullBlob
    | BlobCopyError(Error)
column_copy_kind_result : (Int, Foreign.Call<Int>) -> Result<Bool>
column_copy_kind_result (expected, reply) = match reply {
    Foreign.Returned(kind) => match kind == 5 {
        true => Ok true
        false => match kind == expected {
            true => Ok false
            false => Err (ForeignError (InputFailure ColumnTypeMismatch))
        }
    }
    Foreign.ConversionFailed(_) => Err (ForeignError ConversionFailure)
}
blob_copy_result : Foreign.Call<Bytes> -> BlobProbe
blob_copy_result reply = match reply {
    Foreign.Returned(bytes) => CopiedBlob bytes
    Foreign.ConversionFailed(_) => BlobCopyError (ForeignError ConversionFailure)
}
blob_suspect : BlobProbe -> Bool
blob_suspect probe = match probe {
    EmptyBlob => true
    NullBlobPointer => true
    _ => false
}
blob_null_pointer : BlobProbe -> Bool
blob_null_pointer probe = match probe {
    NullBlobPointer => true
    _ => false
}
column_allocation_check : Result<Int> -> Result<Unit>
column_allocation_check reply = match reply {
    Ok(code) => match code == 7 {
        true => Err (ForeignError (NativeStatus code))
        false => Ok ()
    }
    Err(error) => Err error
}
null_blob_length : Foreign.Call<Int> -> Result<Unit>
null_blob_length reply = match reply {
    Foreign.Returned(length) => match length == 0 {
        true => Ok ()
        false => Err (ForeignError ConversionFailure)
    }
    Foreign.ConversionFailed(_) => Err (ForeignError ConversionFailure)
}
blob_result : (BlobProbe, Result<Unit>) -> Result<BytesOrNull>
blob_result (probe, checked) = match checked {
    Err(error) => Err error
    Ok(()) => match probe {
        CopiedBlob(bytes) => Ok (BlobBytes bytes)
        EmptyBlob => Ok (BlobBytes (B.empty ()))
        NullBlobPointer => Ok (BlobBytes (B.empty ()))
        SqlNullBlob => Ok NullBytes
        BlobCopyError(error) => Err error
    }
}
text_result : (BlobProbe, Result<Unit>) -> Result<TextOrNull>
text_result (probe, checked) = match blob_result (probe, checked) {
    Err(error) => Err error
    Ok(NullBytes) => Ok NullText
    Ok(BlobBytes(bytes)) => match Text.from_utf8 bytes {
        Text.Decoded(text) => Ok (TextValue text)
        Text.InvalidUtf8 => Err (ForeignError ConversionFailure)
    }
}
can_step : Int -> Bool
can_step phase = match phase == 0 {
    true => true
    false => phase == 1
}
step_refusal : Int -> StepResult
step_refusal phase = match phase == 2 {
    true => StepError (ForeignError (ProtocolFailure AfterDone))
    false => StepError (ForeignError (ProtocolFailure NotPrepared))
}
classify_step : Int -> (Int, StepResult)
classify_step code = match code == NativeRow {
    true => (1, Row)
    false => match code == NativeDone {
        true => (2, Done)
        false => (3, StepError (ForeignError (NativeStatus code)))
    }
}
valid_column : Int -> Bool
valid_column index = match Foreign.checked_size_t index {
    Foreign.ConversionFailed(_) => false
    Foreign.Returned(_) => match Foreign.checked_size_t (2147483647 + (index * NegativeOne)) {
        Foreign.Returned(_) => true
        Foreign.ConversionFailed(_) => false
    }
}
column_in_count : (Int, Int) -> Bool
column_in_count (index, count) = match Foreign.checked_size_t (count + (index * NegativeOne) + NegativeOne) {
    Foreign.Returned(_) => true
    Foreign.ConversionFailed(_) => false
}
column_admission : (Int, Int) -> Result<Unit>
column_admission (phase, index) = match phase == 1 {
    false => Err (ForeignError (ProtocolFailure NotRow))
    true => match valid_column index {
        false => Err (ForeignError (InputFailure BadColumn))
        true => Ok ()
    }
}
column_range_result : (Int, Foreign.Call<Int>) -> Result<Unit>
column_range_result (index, reply) = match reply {
    Foreign.Returned(count) => match column_in_count (index, count) {
        false => Err (ForeignError (InputFailure BadColumn))
        true => Ok ()
    }
    Foreign.ConversionFailed(_) => Err (ForeignError ConversionFailure)
}
column_kind_result : Foreign.Call<Int> -> Result<Unit>
column_kind_result reply = match reply {
    Foreign.Returned(kind) => match kind == 1 {
        false => Err (ForeignError (InputFailure ColumnTypeMismatch))
        true => Ok ()
    }
    Foreign.ConversionFailed(_) => Err (ForeignError ConversionFailure)
}
column_int_result : Foreign.Call<Int> -> Result<Int>
column_int_result reply = match reply {
    Foreign.Returned(value) => Ok value
    Foreign.ConversionFailed(_) => Err (ForeignError ConversionFailure)
}
status_result : Foreign.Call<Int> -> Result<Unit>
status_result reply = match reply {
    Foreign.Returned(code) => match code == NativeOk {
        true => Ok ()
        false => Err (ForeignError (NativeStatus code))
    }
    Foreign.ConversionFailed(_) => Err (ForeignError ConversionFailure)
}
valid_parameter : Int -> Bool
valid_parameter index = match valid_column index {
    false => false
    true => match index == 0 {
        true => false
        false => true
    }
}
binding_admission : (Int, Int) -> Result<Unit>
binding_admission (phase, index) = match phase == 0 {
    true => match valid_parameter index {
        true => Ok ()
        false => Err (ForeignError (InputFailure BadIndex))
    }
    false => Err (ForeignError (ProtocolFailure NotPrepared))
}
binding_length_admission : (Int, InputFault) -> Result<Unit>
binding_length_admission (length, fault) = match valid_column length {
    true => Ok ()
    false => Err (ForeignError (InputFailure fault))
}
text_binding_admission : String -> Result<Unit>
text_binding_admission text = match Foreign.checked_nul text {
    Foreign.ConversionFailed(_) => Err (ForeignError (InputFailure BadText))
    Foreign.Returned(_) => binding_length_admission (Text.byte_length text, BadText)
}
pub interface StatementProvider<Access> {
    bind_int : (Access, Int, Int) -> Result<Unit> ! {StatementOps<Access>}
    bind_bytes : (Access, Int, BytesOrNull) -> Result<Unit> ! {StatementOps<Access>}
    bind_text : (Access, Int, TextOrNull) -> Result<Unit> ! {StatementOps<Access>}
    reset : Access -> Result<Unit> ! {StatementOps<Access>}
    clear_bindings : Access -> Result<Unit> ! {StatementOps<Access>}
    step : Access -> StepResult ! {StatementOps<Access>}
    column_bytes : (Access, Int) -> Result<BytesOrNull> ! {StatementOps<Access>}
    column_text : (Access, Int) -> Result<TextOrNull> ! {StatementOps<Access>}
    column_int : (Access, Int) -> Result<Int> ! {StatementOps<Access>}
}
pub effect StatementOps<Access> {
    bind_int : (Access, Int, Int) -> Result<Unit>
    bind_bytes : (Access, Int, BytesOrNull) -> Result<Unit>
    bind_text : (Access, Int, TextOrNull) -> Result<Unit>
    reset : Access -> Result<Unit>
    clear_bindings : Access -> Result<Unit>
    step : Access -> StepResult
    column_bytes : (Access, Int) -> Result<BytesOrNull>
    column_text : (Access, Int) -> Result<TextOrNull>
    column_int : (Access, Int) -> Result<Int>
}
pub resource Statement<S, C> {
    owned S
    input (Connection<C>, String)
    state StatementState<C, S>
    data (Connection<C>, Int)
    acquisition Acquire<StatementState<C, S>, (Connection<C>, Int), PrepareError>
    completion Finish<StatementState<C, S>, FinalizeError>
    result Scope<PrepareError, FinalizeError, Answer> for <Answer>
    codec scope
    provider StatementProvider<Statement<S, C>>
    effect StatementOps<Statement<S, C>>
    interpret BindBlob<C, S>, BindText<C, S>, BindNull<C, S>, ColumnByteLength<C, S>, BindInt<C, S>, Reset<C, S>, ClearBindings<C, S>, Prepare<C, S>, Finalize<C, S>, Step<C, S>, ColumnInt<C, S>, ColumnCount<C, S>, ColumnType<C, S>
    acquire (connection, sql) => {
        let enclosing = perform ConnectionOps<C>.borrow connection
        let length = Text.byte_length sql + 1
        match perform Prepare<C, S>.call (enclosing, sql, length) {
            Foreign.Returned((code, Foreign.Readable(Foreign.NonNull(state)), Foreign.Readable(Foreign.NonNull(tail)))) => match code == NativeOk {
                true => match valid_tail (sql, tail) {
                    true => Acquired(state, (connection, 0))
                    false => Refused InvalidTail
                }
                false => Refused (PrepareFailed code)
            }
            Foreign.Returned((code, Foreign.Readable(Foreign.Null), _)) => Refused (prepare_absent_output (code, EmptySql))
            Foreign.Returned((code, _, Foreign.Readable(Foreign.Null))) => Refused (prepare_absent_output (code, InvalidTail))
            Foreign.Returned((code, _, _)) => Refused (PrepareFailed code)
            Foreign.ConversionFailed(_) => Refused InvalidSql
        }
    }
    finish (state, data) => match perform Finalize<C, S>.call state {
        Foreign.Returned(Foreign.Consumed(code)) => match code == NativeOk {
            true => Consumed
            false => ConsumedFailure (NativeFinalize code)
        }
        Foreign.Returned(Foreign.Retained(code)) => Retained(state, NativeFinalize code)
        Foreign.Returned(Foreign.BlockedDependent) => Retained(state, InvalidFinalize)
        Foreign.ConversionFailed(_) => Retained(state, InvalidFinalize)
    }
    handlers (state, data) {
        bind_int (access, index, value) => {
            let before : (Connection<C>, Int) = Foreign.data_of state
            let phase = match before {
                (_, phase) => phase
            }
            let index_admitted = binding_admission (phase, index)
            let value_admitted = match index_admitted {
                Err(error) => Err error
                Ok(()) => match Foreign.checked_i64 value {
                    Foreign.Returned(_) => Ok ()
                    Foreign.ConversionFailed(_) => Err (ForeignError (InputFailure BadInteger))
                }
            }
            let result = match value_admitted {
                Err(error) => Err error
                Ok(()) => status_result (perform BindInt<C, S>.call (state, index, value))
            }
            resume result
        }
        bind_bytes (access, index, value) => {
            let before : (Connection<C>, Int) = Foreign.data_of state
            let phase = match before {
                (_, phase) => phase
            }
            let admitted = binding_admission (phase, index)
            let result = match admitted {
                Err(error) => Err error
                Ok(()) => match value {
                    NullBytes => status_result (perform BindNull<C, S>.call (state, index))
                    BlobBytes(bytes) => match binding_length_admission (B.length bytes, BadBytes) {
                        Err(error) => Err error
                        Ok(()) => status_result (perform BindBlob<C, S>.call (state, index, bytes, B.length bytes))
                    }
                }
            }
            resume result
        }
        bind_text (access, index, value) => {
            let before : (Connection<C>, Int) = Foreign.data_of state
            let phase = match before {
                (_, phase) => phase
            }
            let admitted = binding_admission (phase, index)
            let result = match admitted {
                Err(error) => Err error
                Ok(()) => match value {
                    NullText => status_result (perform BindNull<C, S>.call (state, index))
                    TextValue(text) => match text_binding_admission text {
                        Err(error) => Err error
                        Ok(()) => status_result (perform BindText<C, S>.call (state, index, text, Text.byte_length text))
                    }
                }
            }
            resume result
        }
        reset access => {
            let before : (Connection<C>, Int) = Foreign.data_of state
            let parent = match before {
                (parent, _) => parent
            }
            let reply = perform Reset<C, S>.call state
            let _ = Foreign.replace_data (state, (parent, 0))
            resume (status_result reply)
        }
        clear_bindings access => {
            let before : (Connection<C>, Int) = Foreign.data_of state
            let allowed = match before {
                (_, phase) => phase == 0
            }
            let result = match allowed {
                false => Err (ForeignError (ProtocolFailure NotPrepared))
                true => status_result (perform ClearBindings<C, S>.call state)
            }
            resume result
        }
        step access => {
            let before : (Connection<C>, Int) = Foreign.data_of state
            let connection = match before {
                (parent, _) => parent
            }
            let phase = match before {
                (_, current) => current
            }
            let result = match can_step phase {
                false => step_refusal phase
                true => match perform Step<C, S>.call state {
                    Foreign.Returned(code) => {
                        let classified = classify_step code
                        let next = match classified {
                            (next, _) => next
                        }
                        let result = match classified {
                            (_, result) => result
                        }
                        let _ = Foreign.replace_data (state, (connection, next))
                        result
                    }
                    Foreign.ConversionFailed(_) => StepError (ForeignError ConversionFailure)
                }
            }
            resume result
        }
        column_bytes (access, index) => {
            let before : (Connection<C>, Int) = Foreign.data_of state
            let connection = match before {
                (parent, _) => parent
            }
            let phase = match before {
                (_, phase) => phase
            }
            let admitted = column_admission (phase, index)
            let counted = match admitted {
                Err(error) => Err error
                Ok(()) => column_range_result (index, perform ColumnCount<C, S>.call state)
            }
            let typed = match counted {
                Err(error) => Err error
                Ok(()) => column_copy_kind_result (4, perform ColumnType<C, S>.call (state, index))
            }
            let queried_probe = copy_window BlobView<W, C, S> from state {
                let queried = match typed {
                    Ok(false) => perform ColumnBlob<W, C, S>.call (state, index)
                    _ => Foreign.Returned (Foreign.Readable Foreign.Null)
                }
                match queried {
                    Foreign.Returned(Foreign.Readable(Foreign.NonNull(view))) => {
                        let extent = perform ColumnBlobExtent<W, C, S>.call (state, index, view)
                        match extent {
                            Foreign.Returned(extent) => match Foreign.extent_value extent == 0 {
                                true => EmptyBlob
                                false => blob_copy_result (Foreign.copy_bytes (view, extent))
                            }
                            Foreign.ConversionFailed(_) => BlobCopyError (ForeignError ConversionFailure)
                        }
                    }
                    Foreign.Returned(_) => NullBlobPointer
                    Foreign.ConversionFailed(_) => BlobCopyError (ForeignError ConversionFailure)
                }
            }
            let probe = match typed {
                Err(error) => BlobCopyError error
                Ok(true) => SqlNullBlob
                Ok(false) => queried_probe
            }
            let allocation = match blob_suspect probe {
                true => {
                    column_allocation_check (perform ConnectionOps<C>.error_code connection)
                }
                false => Ok ()
            }
            let length = match allocation {
                Err(error) => Err error
                Ok(()) => match blob_null_pointer probe {
                    true => null_blob_length (perform ColumnByteLength<C, S>.call (state, index))
                    false => Ok ()
                }
            }
            let checked = match length {
                Err(error) => Err error
                Ok(()) => match blob_null_pointer probe {
                    true => {
                        column_allocation_check (perform ConnectionOps<C>.error_code connection)
                    }
                    false => Ok ()
                }
            }
            resume (blob_result (probe, checked))
        }
        column_text (access, index) => {
            let before : (Connection<C>, Int) = Foreign.data_of state
            let connection = match before {
                (parent, _) => parent
            }
            let phase = match before {
                (_, phase) => phase
            }
            let admitted = column_admission (phase, index)
            let counted = match admitted {
                Err(error) => Err error
                Ok(()) => column_range_result (index, perform ColumnCount<C, S>.call state)
            }
            let typed = match counted {
                Err(error) => Err error
                Ok(()) => column_copy_kind_result (3, perform ColumnType<C, S>.call (state, index))
            }
            let queried_probe = copy_window TextView<W, C, S> from state {
                let queried = match typed {
                    Ok(false) => perform ColumnText<W, C, S>.call (state, index)
                    _ => Foreign.Returned (Foreign.Readable Foreign.Null)
                }
                match queried {
                    Foreign.Returned(Foreign.Readable(Foreign.NonNull(view))) => {
                        let extent = perform ColumnTextExtent<W, C, S>.call (state, index, view)
                        match extent {
                            Foreign.Returned(extent) => match Foreign.extent_value extent == 0 {
                                true => EmptyBlob
                                false => blob_copy_result (Foreign.copy_bytes (view, extent))
                            }
                            Foreign.ConversionFailed(_) => BlobCopyError (ForeignError ConversionFailure)
                        }
                    }
                    Foreign.Returned(_) => NullBlobPointer
                    Foreign.ConversionFailed(_) => BlobCopyError (ForeignError ConversionFailure)
                }
            }
            let probe = match typed {
                Err(error) => BlobCopyError error
                Ok(true) => SqlNullBlob
                Ok(false) => queried_probe
            }
            let allocation = match blob_suspect probe {
                true => {
                    column_allocation_check (perform ConnectionOps<C>.error_code connection)
                }
                false => Ok ()
            }
            let checked = match allocation {
                Err(error) => Err error
                Ok(()) => match blob_null_pointer probe {
                    true => Err (ForeignError ConversionFailure)
                    false => Ok ()
                }
            }
            resume (text_result (probe, checked))
        }
        column_int (access, index) => {
            let before : (Connection<C>, Int) = Foreign.data_of state
            let phase = match before {
                (_, phase) => phase
            }
            let checked = column_admission (phase, index)
            let counted = match checked {
                Err(error) => Err error
                Ok(()) => column_range_result (index, perform ColumnCount<C, S>.call state)
            }
            let typed = match counted {
                Err(error) => Err error
                Ok(()) => column_kind_result (perform ColumnType<C, S>.call (state, index))
            }
            let result = match typed {
                Err(error) => Err error
                Ok(()) => column_int_result (perform ColumnInt<C, S>.call (state, index))
            }
            resume result
        }
    }
}
