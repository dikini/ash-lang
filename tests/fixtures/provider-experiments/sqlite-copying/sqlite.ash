import @foreign.sqlite as Native
import provider as Provider
pub import @foreign.sqlite (Bytes, EmptyBytes, MoreBytes, OpenConfig, InMemory, File, OpenError, OpenFailure, CloseError, CloseFailure, PrepareError, PrepareFailure, EmptySql, FinalizeError, FinalizeFailure)

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
select_parameter () = {
let byte8 = MoreBytes (49, EmptyBytes)
let byte7 = MoreBytes (63, byte8)
let byte6 = MoreBytes (32, byte7)
let byte5 = MoreBytes (84, byte6)
let byte4 = MoreBytes (67, byte5)
let byte3 = MoreBytes (69, byte4)
let byte2 = MoreBytes (76, byte3)
let byte1 = MoreBytes (69, byte2)
let byte0 = MoreBytes (83, byte1)
SqlText byte0
}
