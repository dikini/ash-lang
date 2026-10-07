import @foreign.sqlite as Native
import provider as Provider
pub import @foreign.sqlite (BytesOrNull, NullBytes, BlobBytes, TextOrNull, NullText, TextValue, OpenConfig, InMemory, File, OpenError, OpenFailure, CloseError, CloseFailure, PrepareError, PrepareFailure, EmptySql, FinalizeError, FinalizeFailure)

pub newtype SqlText = SqlText(String)

pub type Error = ForeignError(Native.Error)
| MissingRow
| UnexpectedRow
pub type Result<T> = Ok(T)
| Err(Error)
pub type StepResult = Row
| Done
| StepError(Error)

pub effect ConnectionOps<R> {
diagnostic : Connection<R> -> Error
}
pub interface ConnectionProvider<R> {
diagnostic : Connection<R> -> Error ! {ConnectionOps<R>}
}

pub effect StatementOps<S, C> {
bind_int : (Statement<S, C>, Int, Int) -> Result<Unit>
step : Statement<S, C> -> StepResult
column_int : (Statement<S, C>, Int) -> Result<Int>
bind_bytes : (Statement<S, C>, Int, BytesOrNull) -> Result<Unit>
column_bytes : (Statement<S, C>, Int) -> Result<BytesOrNull>
bind_text : (Statement<S, C>, Int, TextOrNull) -> Result<Unit>
column_text : (Statement<S, C>, Int) -> Result<TextOrNull>
reset : Statement<S, C> -> Result<Unit>
clear_bindings : Statement<S, C> -> Result<Unit>
}
pub interface StatementProvider<S, C> {
bind_int : (Statement<S, C>, Int, Int) -> Result<Unit> ! {StatementOps<S, C>}
step : Statement<S, C> -> StepResult ! {StatementOps<S, C>}
column_int : (Statement<S, C>, Int) -> Result<Int> ! {StatementOps<S, C>}
bind_bytes : (Statement<S, C>, Int, BytesOrNull) -> Result<Unit> ! {StatementOps<S, C>}
column_bytes : (Statement<S, C>, Int) -> Result<BytesOrNull> ! {StatementOps<S, C>}
bind_text : (Statement<S, C>, Int, TextOrNull) -> Result<Unit> ! {StatementOps<S, C>}
column_text : (Statement<S, C>, Int) -> Result<TextOrNull> ! {StatementOps<S, C>}
reset : Statement<S, C> -> Result<Unit> ! {StatementOps<S, C>}
clear_bindings : Statement<S, C> -> Result<Unit> ! {StatementOps<S, C>}
}

pub resource Connection<R> {
input OpenConfig
state Native.ConnectionState<R>
result Provider.Scope<OpenError, CloseError, T> for <T>
provider ConnectionProvider<R>
effect ConnectionOps<R>
interpret Native.Connection<R>
acquire config => perform Native.Connection<R>.open config
finish state => perform Native.Connection<R>.close state
handlers state {
diagnostic db => resume (ForeignError (perform Native.Connection<R>.diagnostic state))
}
}

pub resource Statement<S, C> {
input (Connection<C>, SqlText)
state Native.StatementState<S, C>
result Provider.Scope<PrepareError, FinalizeError, T> for <T>
provider StatementProvider<S, C>
effect StatementOps<S, C>
interpret Native.Statement<S, C>
acquire input => match input {
(db, SqlText(sql)) => perform Native.Statement<S, C>.prepare (Provider.state_of db, sql)
}
finish state => perform Native.Statement<S, C>.finalize state
handlers state {
bind_int operand => match operand {
(stmt, index, value) => match (perform Native.Statement<S, C>.bind_int (state, index, value)) {
Native.Ok(()) => resume (Ok ())
Native.Err(error) => resume (Err (ForeignError error))
}
}
step stmt => match (perform Native.Statement<S, C>.step state) {
Native.Row => resume Row
Native.Done => resume Done
Native.StepError(error) => resume (StepError (ForeignError error))
}
column_int operand => match operand {
(stmt, index) => match (perform Native.Statement<S, C>.column_int (state, index)) {
Native.Ok(value) => resume (Ok value)
Native.Err(error) => resume (Err (ForeignError error))
}
}
bind_bytes operand => match operand {
(stmt, index, value) => match (perform Native.Statement<S, C>.bind_bytes (state, index, value)) {
Native.Ok(value) => resume (Ok value)
Native.Err(error) => resume (Err (ForeignError error))
}
}
column_bytes operand => match operand {
(stmt, index) => match (perform Native.Statement<S, C>.column_bytes (state, index)) {
Native.Ok(value) => resume (Ok value)
Native.Err(error) => resume (Err (ForeignError error))
}
}
bind_text operand => match operand {
(stmt, index, value) => match (perform Native.Statement<S, C>.bind_text (state, index, value)) {
Native.Ok(value) => resume (Ok value)
Native.Err(error) => resume (Err (ForeignError error))
}
}
column_text operand => match operand {
(stmt, index) => match (perform Native.Statement<S, C>.column_text (state, index)) {
Native.Ok(value) => resume (Ok value)
Native.Err(error) => resume (Err (ForeignError error))
}
}
reset stmt => match (perform Native.Statement<S, C>.reset state) {
Native.Ok(value) => resume (Ok value)
Native.Err(error) => resume (Err (ForeignError error))
}
clear_bindings stmt => match (perform Native.Statement<S, C>.clear_bindings state) {
Native.Ok(value) => resume (Ok value)
Native.Err(error) => resume (Err (ForeignError error))
}
}
}

pub memory : Unit -> OpenConfig
memory () = InMemory

pub select_parameter : Unit -> SqlText
select_parameter () = SqlText "SELECT ?1"
