import @builtin.string as TextOps
import @foreign.sqlite as Native
import provider as Provider
pub import @foreign.sqlite (OpenConfig, InMemory, File, OpenError, OpenFailure, CloseError, CloseFailure, PrepareError, PrepareFailure, EmptySql, FinalizeError, FinalizeFailure)

pub newtype SqlText = SqlText(Bytes)

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
}
pub interface StatementProvider<S, C> {
bind_int : (Statement<S, C>, Int, Int) -> Result<Unit> ! {StatementOps<S, C>}
step : Statement<S, C> -> StepResult ! {StatementOps<S, C>}
column_int : (Statement<S, C>, Int) -> Result<Int> ! {StatementOps<S, C>}
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
}
}

pub memory : Unit -> OpenConfig
memory () = InMemory

pub select_parameter : Unit -> SqlText
select_parameter () = SqlText (TextOps.to_utf8 "SELECT ?1")

pub failing_query : Unit -> SqlText
failing_query () = SqlText (TextOps.to_utf8 "SELECT abs(-9223372036854775808)")
