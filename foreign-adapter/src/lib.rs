//! Safe copying SQLite and physical arena backing for bounded Ash experiments.
//!
//! Native pointers remain private. Statements keep an internal connection guard,
//! not an Ash lifetime extension. The evaluator must enforce Ash scope ownership.
//! There is no shutdown call: initialization belongs to the host process.

pub mod arena;
/// Identity-bound executable Ash bindings for the SQLite copying experiment.
pub mod ash_bindings;
pub use ash_bindings::{SqliteFinishFaults, sqlite_binding, sqlite_binding_with_finish_faults};

use std::{
    cell::{Cell, RefCell},
    ffi::{CStr, CString, c_char, c_int, c_void},
    ptr::{self, NonNull},
    rc::Rc,
};

#[repr(C)]
struct Db {
    _private: [u8; 0],
}
#[repr(C)]
struct Stmt {
    _private: [u8; 0],
}
unsafe extern "C" {
    fn sqlite3_libversion() -> *const c_char;
    fn sqlite3_sourceid() -> *const c_char;
    fn sqlite3_compileoption_get(index: c_int) -> *const c_char;
    fn sqlite3_initialize() -> c_int;
    fn sqlite3_open_v2(
        path: *const c_char,
        db: *mut *mut Db,
        flags: c_int,
        vfs: *const c_char,
    ) -> c_int;
    fn sqlite3_prepare_v2(
        db: *mut Db,
        sql: *const c_char,
        len: c_int,
        stmt: *mut *mut Stmt,
        tail: *mut *const c_char,
    ) -> c_int;
    fn sqlite3_bind_int64(stmt: *mut Stmt, index: c_int, value: i64) -> c_int;
    fn ash_sqlite_bind_blob_copy(
        stmt: *mut Stmt,
        index: c_int,
        value: *const c_void,
        len: c_int,
    ) -> c_int;
    fn sqlite3_bind_null(stmt: *mut Stmt, index: c_int) -> c_int;
    fn sqlite3_step(stmt: *mut Stmt) -> c_int;
    fn sqlite3_column_count(stmt: *mut Stmt) -> c_int;
    fn sqlite3_column_type(stmt: *mut Stmt, column: c_int) -> c_int;
    fn sqlite3_column_int64(stmt: *mut Stmt, column: c_int) -> i64;
    fn sqlite3_column_blob(stmt: *mut Stmt, column: c_int) -> *const c_void;
    fn sqlite3_column_bytes(stmt: *mut Stmt, column: c_int) -> c_int;
    fn sqlite3_reset(stmt: *mut Stmt) -> c_int;
    fn sqlite3_clear_bindings(stmt: *mut Stmt) -> c_int;
    fn sqlite3_finalize(stmt: *mut Stmt) -> c_int;
    fn sqlite3_close(db: *mut Db) -> c_int;
    fn sqlite3_errcode(db: *mut Db) -> c_int;
    fn sqlite3_errmsg(db: *mut Db) -> *const c_char;
}
const OK: c_int = 0;
const NOMEM: c_int = 7;
const ROW: c_int = 100;
const DONE: c_int = 101;

/// Native runtime metadata copied from the linked library.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeInfo {
    /// Runtime version, independent of the pinned header version.
    pub version: String,
    /// Runtime source identifier.
    pub source_id: String,
    /// Reported native compile options.
    pub compile_options: Vec<String>,
}
/// Observes runtime metadata without acquiring a database.
#[must_use]
pub fn runtime_info() -> RuntimeInfo {
    // SAFETY: SQLite supplies process-lifetime terminated strings for these APIs.
    let (version, source_id) = unsafe {
        (
            copy_c_string(sqlite3_libversion()),
            copy_c_string(sqlite3_sourceid()),
        )
    };
    let mut compile_options = Vec::new();
    for index in 0..c_int::MAX {
        // SAFETY: All nonnegative indices are accepted; null marks the end.
        let option = unsafe { sqlite3_compileoption_get(index) };
        if option.is_null() {
            break;
        }
        // SAFETY: A non-null compile option is a process-lifetime C string.
        compile_options.push(unsafe { copy_c_string(option) });
    }
    RuntimeInfo {
        version,
        source_id,
        compile_options,
    }
}
unsafe fn copy_c_string(pointer: *const c_char) -> String {
    if pointer.is_null() {
        return String::new();
    }
    // SAFETY: Callers provide a live, NUL-terminated SQLite string.
    unsafe { CStr::from_ptr(pointer) }
        .to_string_lossy()
        .into_owned()
}

/// Current connection status copied from SQLite, including a successful status.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic {
    /// Current native code; zero (`SQLITE_OK`) does not report a failure.
    pub code: i32,
    /// Independent message copy; empty when SQLite supplies no message.
    pub message: String,
}
/// Actual SQLite failure; its diagnostics are independent copied data.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeError {
    /// API operation that reported the failure.
    pub operation: &'static str,
    /// Native return code, retained without converting it to another outcome.
    pub code: i32,
    /// Diagnostic copied before destroying native state.
    pub message: String,
}
/// Checked wrapper errors are distinct from actual native outcomes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    /// SQLite returned a failure code.
    Native(NativeError),
    /// An input cannot be represented by the selected native ABI.
    InvalidInput(&'static str),
    /// An operation violates the wrapper's checked state protocol.
    Protocol(&'static str),
    /// The column has a different SQLite storage kind.
    ColumnKind,
    /// The foreign library contradicted an assumed ABI postcondition.
    Contract(&'static str),
    /// Deterministic test-only publication failure, not native exhaustion.
    InjectedPublicationFailure,
    /// Deterministic test-only native-result classification, not actual native failure.
    InjectedNativeFailure {
        /// Native operation whose failure was simulated.
        operation: &'static str,
        /// Simulated native code.
        code: i32,
    },
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::error::Error for Error {}

/// One actual native call or a successful byte-copy observation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Event {
    /// A native operation returned the recorded code.
    Call {
        /// Operation name.
        operation: &'static str,
        /// Unmodified native return code.
        code: i32,
    },
    /// Test-only native-result fault; distinct from an actual native outcome.
    FaultInjected {
        /// Operation being simulated.
        operation: &'static str,
        /// Simulated native code.
        code: i32,
    },
    /// A native data query was called; its return value is not a status code.
    Query {
        /// Operation name.
        operation: &'static str,
    },
    /// SQLite accepted this many input bytes with TRANSIENT copying.
    InputCopied(usize),
    /// The adapter copied this many output bytes into independent Rust storage.
    OutputCopied(usize),
}
/// Explicit observations of adapter calls, not SQLite allocator activity.
#[derive(Debug, Clone, Default)]
pub struct Observations(Rc<RefCell<Vec<Event>>>);
impl Observations {
    /// Returns a snapshot that remains readable after owners complete.
    #[must_use]
    pub fn events(&self) -> Vec<Event> {
        self.0.borrow().clone()
    }
    /// Counts native calls to a particular API in this observation set.
    #[must_use]
    pub fn calls(&self, operation: &str) -> usize {
        self.0.borrow().iter().filter(|event| matches!(event, Event::Call { operation: name, .. } | Event::Query { operation: name } if *name == operation)).count()
    }
    fn call(&self, operation: &'static str, code: c_int) {
        self.0.borrow_mut().push(Event::Call { operation, code });
    }
    fn query(&self, operation: &'static str) {
        self.push(Event::Query { operation });
    }
    fn push(&self, event: Event) {
        self.0.borrow_mut().push(event);
    }
}
#[derive(Debug)]
struct ConnectionInner {
    pointer: Cell<Option<NonNull<Db>>>,
    observations: Observations,
}
impl ConnectionInner {
    fn pointer(&self) -> Result<NonNull<Db>, Error> {
        self.pointer
            .get()
            .ok_or(Error::Protocol("connection is closed"))
    }
    fn error(&self, operation: &'static str, code: c_int) -> Error {
        let message = self.pointer.get().map_or_else(String::new, |pointer| {
            self.observations.query("errmsg");
            // SAFETY: The connection remains live while diagnostics are copied.
            unsafe { copy_c_string(sqlite3_errmsg(pointer.as_ptr())) }
        });
        Error::Native(NativeError {
            operation,
            code,
            message,
        })
    }
    fn close(&self) -> Result<(), Error> {
        let pointer = self.pointer()?;
        // SAFETY: The pointer is a live SQLite connection. Refusal retains it.
        let code = unsafe { sqlite3_close(pointer.as_ptr()) };
        self.observations.call("close", code);
        if code == OK {
            self.pointer.set(None);
            Ok(())
        } else {
            Err(self.error("close", code))
        }
    }
}
impl Drop for ConnectionInner {
    fn drop(&mut self) {
        if self.pointer.get().is_some() {
            // Every statement owns a guard, so all statements have finalized
            // before the last guard drops. No close_v2 deferred fallback exists.
            let _ = self.close();
        }
    }
}
/// Unique client connection owner with private, single-threaded native state.
#[derive(Debug)]
pub struct Connection {
    inner: Rc<ConnectionInner>,
}
impl Connection {
    /// Opens a writable database, creating it when absent.
    ///
    /// # Errors
    /// Returns input/setup/native errors. Any partial owner is closed before return.
    pub fn open(path: &str) -> Result<Self, Error> {
        Self::open_observed(path, Observations::default())
    }
    /// Opens a database and records actual calls in the supplied observation set.
    ///
    /// # Errors
    /// Has the same failure and partial-owner contract as [`Self::open`].
    pub fn open_observed(path: &str, observations: Observations) -> Result<Self, Error> {
        let path =
            CString::new(path).map_err(|_| Error::InvalidInput("database path contains NUL"))?;
        // SAFETY: SQLite initialization is host-global and idempotent. We never shut it down.
        let code = unsafe { sqlite3_initialize() };
        observations.call("initialize", code);
        if code != OK {
            return Err(Error::Native(NativeError {
                operation: "initialize",
                code,
                message: String::new(),
            }));
        }
        let mut pointer = ptr::null_mut();
        // SAFETY: The input string and output slot are valid during the call;
        // READWRITE|CREATE is supported and null selects the default VFS.
        let code = unsafe { sqlite3_open_v2(path.as_ptr(), &mut pointer, 2 | 4, ptr::null()) };
        observations.call("open", code);
        let inner = Rc::new(ConnectionInner {
            pointer: Cell::new(NonNull::new(pointer)),
            observations,
        });
        if code != OK {
            return Err(inner.error("open", code));
        }
        inner.pointer()?;
        #[cfg(test)]
        if test_support::FAIL_OPEN_PUBLICATION.replace(false) {
            return Err(Error::InjectedPublicationFailure);
        }
        Ok(Self { inner })
    }
    /// Copies the live connection's current native code and message.
    ///
    /// The result includes `SQLITE_OK`; it does not assert an operation failed.
    /// Later native calls or connection completion cannot invalidate the copy.
    /// This query does not consume the connection or change statement protocol.
    ///
    /// # Errors
    /// Returns [`Error::Protocol`] for a closed owner, before querying SQLite.
    pub fn diagnostic(&self) -> Result<Diagnostic, Error> {
        let pointer = self.inner.pointer()?;
        self.inner.observations.query("errcode");
        // SAFETY: The private connection pointer is live for this shared borrow.
        let code = unsafe { sqlite3_errcode(pointer.as_ptr()) };
        self.inner.observations.query("errmsg");
        // SAFETY: The live connection owns the message. Both diagnostic queries
        // preserve its error code, and the message is copied before another call.
        let message = unsafe { copy_c_string(sqlite3_errmsg(pointer.as_ptr())) };
        Ok(Diagnostic { code, message })
    }
    /// Prepares exactly one statement, or returns `None` for no executable SQL.
    /// Trailing non-whitespace input is rejected rather than silently ignored.
    ///
    /// # Errors
    /// Returns input, closed-owner, native preparation, or unused-input errors.
    pub fn prepare(&mut self, sql: &str) -> Result<Option<Statement>, Error> {
        let db = self.inner.pointer()?;
        let sql = CString::new(sql).map_err(|_| Error::InvalidInput("SQL contains NUL"))?;
        let len = c_int::try_from(sql.as_bytes_with_nul().len())
            .map_err(|_| Error::InvalidInput("SQL length exceeds C int"))?;
        let mut pointer = ptr::null_mut();
        let mut tail = ptr::null();
        // SAFETY: SQL includes its terminator; outputs are live local slots;
        // the connection is live. SQLite does not retain the SQL input.
        let code =
            unsafe { sqlite3_prepare_v2(db.as_ptr(), sql.as_ptr(), len, &mut pointer, &mut tail) };
        self.inner.observations.call("prepare", code);
        let mut statement = NonNull::new(pointer).map(|pointer| Statement {
            pointer: Some(pointer),
            connection: Rc::clone(&self.inner),
            state: StatementState::Prepared,
        });
        if code != OK {
            return Err(self.inner.error("prepare", code));
        }
        let start = sql.as_ptr() as usize;
        let end = start + sql.as_bytes().len();
        let tail = tail as usize;
        if !(start..=end).contains(&tail) {
            return Err(Error::Contract("prepare tail outside SQL input"));
        }
        if !sql.as_bytes()[tail - start..]
            .iter()
            .all(u8::is_ascii_whitespace)
        {
            return Err(Error::InvalidInput("unused SQL after first statement"));
        }
        #[cfg(test)]
        if statement.is_some() && test_support::FAIL_PREPARE_PUBLICATION.replace(false) {
            return Err(Error::InjectedPublicationFailure);
        }
        Ok(statement.take())
    }
    /// Attempts actual native close. Refusal preserves a callable connection.
    ///
    /// # Errors
    /// Reports native refusal, including BUSY, or an already-closed owner.
    pub fn close(&mut self) -> Result<(), Error> {
        self.inner.close()
    }
}
/// Checked native statement protocol state.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StatementState {
    /// Binding and first stepping are permitted.
    Prepared,
    /// Column access and subsequent stepping are permitted.
    Row,
    /// Execution completed; reset is required before another step.
    Done,
    /// Execution failed; reset is required before another step.
    Failed,
}
/// Native step outcome excluding actual errors.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Step {
    /// A row is available.
    Row,
    /// Execution completed.
    Done,
}
/// Independent copied column data for the admitted storage kinds.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Column {
    /// SQLite integer copied through sqlite3_int64.
    Integer(i64),
    /// SQLite BLOB copied into independent storage, including an empty BLOB.
    Blob(Vec<u8>),
    /// SQL null, distinct from empty bytes.
    Null,
}
/// Unique statement owner; its internal guard keeps native cleanup safe.
#[derive(Debug)]
pub struct Statement {
    pointer: Option<NonNull<Stmt>>,
    connection: Rc<ConnectionInner>,
    state: StatementState,
}
impl Statement {
    fn pointer(&self) -> NonNull<Stmt> {
        self.pointer.expect("live Statement always owns a pointer")
    }
    fn require_prepared(&self) -> Result<(), Error> {
        if self.state != StatementState::Prepared {
            return Err(Error::Protocol(
                "binding requires a prepared or reset statement",
            ));
        }
        Ok(())
    }
    fn parameter(&self, index: usize) -> Result<c_int, Error> {
        self.require_prepared()?;
        if index == 0 {
            return Err(Error::InvalidInput("parameter index starts at one"));
        }
        c_int::try_from(index).map_err(|_| Error::InvalidInput("parameter index exceeds C int"))
    }
    fn status(&self, operation: &'static str, code: c_int) -> Result<(), Error> {
        self.connection.observations.call(operation, code);
        if code == OK {
            Ok(())
        } else {
            Err(self.connection.error(operation, code))
        }
    }
    /// Returns the current checked state.
    #[must_use]
    pub const fn state(&self) -> StatementState {
        self.state
    }
    /// Binds a copied 64-bit SQLite integer; callers must check Ash integer range.
    ///
    /// # Errors
    /// Reports invalid indices, binding protocol errors, and native binding errors.
    pub fn bind_int64(&mut self, index: usize, value: i64) -> Result<(), Error> {
        let index = self.parameter(index)?;
        // SAFETY: Pointer is live and has not stepped since preparation/reset.
        let code = unsafe { sqlite3_bind_int64(self.pointer().as_ptr(), index, value) };
        self.status("bind_int64", code)
    }
    /// Binds bytes with SQLITE_TRANSIENT: input storage may end after return.
    ///
    /// # Errors
    /// Reports invalid sizes/indices, protocol errors, or native errors.
    pub fn bind_blob_copy(&mut self, index: usize, bytes: &[u8]) -> Result<(), Error> {
        let index = self.parameter(index)?;
        let len = c_int::try_from(bytes.len())
            .map_err(|_| Error::InvalidInput("BLOB length exceeds C int"))?;
        // SAFETY: Even an empty Rust slice has a non-null pointer, distinguishing
        // empty BLOB from SQL null. C uses TRANSIENT and copies before return.
        let code = unsafe {
            ash_sqlite_bind_blob_copy(self.pointer().as_ptr(), index, bytes.as_ptr().cast(), len)
        };
        self.status("bind_blob_copy", code)?;
        self.connection
            .observations
            .push(Event::InputCopied(bytes.len()));
        Ok(())
    }
    /// Binds SQL null.
    ///
    /// # Errors
    /// Reports invalid indices, binding protocol errors, and native errors.
    pub fn bind_null(&mut self, index: usize) -> Result<(), Error> {
        let index = self.parameter(index)?;
        // SAFETY: Pointer is live and binding is permitted by checked state.
        let code = unsafe { sqlite3_bind_null(self.pointer().as_ptr(), index) };
        self.status("bind_null", code)
    }
    /// Steps a prepared statement or advances an available row.
    ///
    /// # Errors
    /// Reports completed/failed protocol states or an actual execution failure.
    pub fn step(&mut self) -> Result<Step, Error> {
        if !matches!(self.state, StatementState::Prepared | StatementState::Row) {
            return Err(Error::Protocol(
                "step requires preparation, reset, or a row",
            ));
        }
        // SAFETY: The live statement's state permits stepping. No views escape.
        let code = unsafe { sqlite3_step(self.pointer().as_ptr()) };
        self.connection.observations.call("step", code);
        match code {
            ROW => {
                self.state = StatementState::Row;
                Ok(Step::Row)
            }
            DONE => {
                self.state = StatementState::Done;
                Ok(Step::Done)
            }
            _ => {
                self.state = StatementState::Failed;
                Err(self.connection.error("step", code))
            }
        }
    }
    /// Copies an integer, BLOB, or null from the current row.
    ///
    /// # Errors
    /// Reports protocol/range/kind errors and native BLOB access exhaustion.
    pub fn column_copy(&mut self, column: usize) -> Result<Column, Error> {
        if self.state != StatementState::Row {
            return Err(Error::Protocol("column access requires a row"));
        }
        let column = c_int::try_from(column)
            .map_err(|_| Error::InvalidInput("column index exceeds C int"))?;
        // SAFETY: Pointer is live with an available row; count has no side effects.
        let count = unsafe { sqlite3_column_count(self.pointer().as_ptr()) };
        self.connection.observations.query("column_count");
        if column >= count {
            return Err(Error::InvalidInput("column index outside row"));
        }
        // SAFETY: Column is within the available row. Type query does not convert.
        let kind = unsafe { sqlite3_column_type(self.pointer().as_ptr(), column) };
        self.connection.observations.query("column_type");
        match kind {
            1 => {
                // SAFETY: Valid integer column in a live row, copied by value.
                let value = unsafe { sqlite3_column_int64(self.pointer().as_ptr(), column) };
                self.connection.observations.query("column_int64");
                Ok(Column::Integer(value))
            }
            4 => {
                // SAFETY: Valid BLOB column; no native invalidating operation can
                // interleave, and we copy before returning any data to the caller.
                let mut pointer = unsafe { sqlite3_column_blob(self.pointer().as_ptr(), column) };
                self.connection.observations.query("column_blob");
                let injected_blob = injected_column_failure("column_blob");
                if injected_blob {
                    pointer = ptr::null();
                }
                if pointer.is_null() {
                    self.check_column_oom("column_blob", injected_blob)?;
                }
                // SAFETY: BLOB kind was checked, so the length query does not
                // invalidate its storage. Suspect pointer failure was checked first.
                let mut len = unsafe { sqlite3_column_bytes(self.pointer().as_ptr(), column) };
                self.connection.observations.query("column_bytes");
                let injected_bytes = injected_column_failure("column_bytes");
                if injected_bytes {
                    len = 0;
                }
                if len == 0 {
                    self.check_column_oom("column_bytes", injected_bytes)?;
                }
                if pointer.is_null() && len != 0 {
                    return Err(Error::Contract("null BLOB with nonzero length"));
                }
                let len =
                    usize::try_from(len).map_err(|_| Error::Contract("negative BLOB length"))?;
                let bytes = if len == 0 {
                    Vec::new()
                } else {
                    // SAFETY: Nonzero live BLOB storage contains the reported
                    // bytes. C int length fits isize on the audited 64-bit target.
                    unsafe { std::slice::from_raw_parts(pointer.cast::<u8>(), len) }.to_vec()
                };
                self.connection.observations.push(Event::OutputCopied(len));
                Ok(Column::Blob(bytes))
            }
            5 => Ok(Column::Null),
            _ => Err(Error::ColumnKind),
        }
    }
    fn check_column_oom(&self, operation: &'static str, injected: bool) -> Result<(), Error> {
        // SAFETY: The statement's guard keeps the connection live. This call
        // precedes every other SQLite interface after the suspect column result.
        let code = unsafe { sqlite3_errcode(self.connection.pointer()?.as_ptr()) };
        self.connection.observations.query("errcode");
        if injected {
            self.connection.observations.push(Event::FaultInjected {
                operation,
                code: NOMEM,
            });
            return Err(Error::InjectedNativeFailure {
                operation,
                code: NOMEM,
            });
        }
        if code == NOMEM {
            return Err(self.connection.error(operation, code));
        }
        Ok(())
    }
    /// Resets execution while preserving bound values, even if reporting prior failure.
    ///
    /// # Errors
    /// Reports the preceding native execution error; state still becomes Prepared.
    pub fn reset(&mut self) -> Result<(), Error> {
        // SAFETY: Live statement may be reset in any admitted non-finalized state.
        let code = unsafe { sqlite3_reset(self.pointer().as_ptr()) };
        self.state = StatementState::Prepared;
        self.status("reset", code)
    }
    /// Clears bound values on a prepared/reset statement.
    ///
    /// # Errors
    /// Reports protocol violations or actual native errors.
    pub fn clear_bindings(&mut self) -> Result<(), Error> {
        self.require_prepared()?;
        // SAFETY: Live statement is prepared/reset, with no exposed retained views.
        let code = unsafe { sqlite3_clear_bindings(self.pointer().as_ptr()) };
        self.status("clear_bindings", code)
    }
    fn finish(&mut self) -> Result<(), Error> {
        let Some(pointer) = self.pointer.take() else {
            return Ok(());
        };
        // SAFETY: The pointer is uniquely owned and removed before destruction.
        // SQLite consumes it even when the returned code reports an earlier error.
        let code = unsafe { sqlite3_finalize(pointer.as_ptr()) };
        self.status("finalize", code)
    }
    /// Consumes the statement and returns its native completion report.
    ///
    /// # Errors
    /// May report preceding native failure; the statement is still consumed.
    pub fn finalize(mut self) -> Result<(), Error> {
        self.finish()
    }
}
impl Drop for Statement {
    fn drop(&mut self) {
        let _ = self.finish();
    }
}

fn injected_column_failure(_operation: &'static str) -> bool {
    #[cfg(test)]
    if test_support::COLUMN_FAILURE.get() == Some(_operation) {
        test_support::COLUMN_FAILURE.set(None);
        return true;
    }
    false
}
#[cfg(test)]
mod test_support {
    use std::cell::Cell;
    std::thread_local! {
        pub(super) static COLUMN_FAILURE: Cell<Option<&'static str>> = const { Cell::new(None) };
        pub(super) static FAIL_OPEN_PUBLICATION: Cell<bool> = const { Cell::new(false) };
        pub(super) static FAIL_PREPARE_PUBLICATION: Cell<bool> = const { Cell::new(false) };
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use std::{
        path::PathBuf,
        sync::atomic::{AtomicUsize, Ordering},
    };

    struct Directory(PathBuf);
    impl Directory {
        fn new() -> Self {
            static NEXT: AtomicUsize = AtomicUsize::new(0);
            let path = std::env::temp_dir().join(format!(
                "ash-sqlite-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            std::fs::create_dir(&path).expect("exclusively create test directory");
            Self(path)
        }
        fn path(&self, name: &str) -> String {
            self.0.join(name).to_str().unwrap().into()
        }
    }
    impl Drop for Directory {
        fn drop(&mut self) {
            std::fs::remove_dir_all(&self.0).expect("remove owned fixture directory");
        }
    }
    fn statement(connection: &mut Connection, sql: &str) -> Statement {
        connection
            .prepare(sql)
            .unwrap()
            .expect("SQL produces a statement")
    }
    fn execute(connection: &mut Connection, sql: &str) {
        let mut stmt = statement(connection, sql);
        assert_eq!(stmt.step(), Ok(Step::Done));
        stmt.finalize().unwrap();
    }
    #[test]
    fn opens_real_memory_database() {
        assert!(Connection::open(":memory:").is_ok());
    }
    #[test]
    fn diagnostic_reports_actual_prepare_failure() {
        let observations = Observations::default();
        let mut connection = Connection::open_observed(":memory:", observations.clone()).unwrap();
        let Error::Native(error) = connection
            .prepare("SELECT * FROM diagnostic_missing_table")
            .unwrap_err()
        else {
            panic!("missing table must produce an actual SQLite error");
        };
        assert_eq!(error.operation, "prepare");
        assert_ne!(error.code, OK);
        let before = observations.events().len();
        let diagnostic = connection.diagnostic().unwrap();
        assert_eq!(diagnostic.code, error.code);
        assert_eq!(diagnostic.message, error.message);
        assert_eq!(
            &observations.events()[before..],
            [
                Event::Query {
                    operation: "errcode"
                },
                Event::Query {
                    operation: "errmsg"
                },
            ]
        );
        connection.close().unwrap();
    }
    #[test]
    fn diagnostic_reports_success_without_consuming_native_owners() {
        let observations = Observations::default();
        let mut connection = Connection::open_observed(":memory:", observations.clone()).unwrap();
        assert_eq!(connection.diagnostic().unwrap().code, OK);
        let mut stmt = statement(&mut connection, "SELECT 42");
        let before = observations.events().len();
        assert_eq!(connection.diagnostic().unwrap().code, OK);
        assert_eq!(
            &observations.events()[before..],
            [
                Event::Query {
                    operation: "errcode"
                },
                Event::Query {
                    operation: "errmsg"
                },
            ]
        );
        assert_eq!(observations.calls("finalize"), 0);
        assert_eq!(observations.calls("close"), 0);
        assert_eq!(stmt.state(), StatementState::Prepared);
        assert_eq!(stmt.step(), Ok(Step::Row));
        assert_eq!(stmt.column_copy(0), Ok(Column::Integer(42)));
        stmt.finalize().unwrap();
        connection.close().unwrap();
        assert_eq!(observations.calls("finalize"), 1);
        assert_eq!(observations.calls("close"), 1);
    }
    #[test]
    fn diagnostic_copy_survives_later_native_calls_and_close() {
        let mut connection = Connection::open(":memory:").unwrap();
        let Error::Native(error) = connection
            .prepare("SELECT * FROM diagnostic_missing_table")
            .unwrap_err()
        else {
            panic!("missing table must produce an actual SQLite error");
        };
        let diagnostic = connection.diagnostic().unwrap();
        execute(
            &mut connection,
            "CREATE TABLE diagnostic_missing_table(value INTEGER)",
        );
        assert_eq!(connection.diagnostic().unwrap().code, OK);
        connection.close().unwrap();
        drop(connection);
        assert_eq!(diagnostic.code, error.code);
        assert_eq!(diagnostic.message, error.message);
        assert!(diagnostic.message.contains("diagnostic_missing_table"));
    }
    #[test]
    fn diagnostic_rejects_closed_owner_before_any_native_query() {
        let observations = Observations::default();
        let mut connection = Connection::open_observed(":memory:", observations.clone()).unwrap();
        connection.close().unwrap();
        let before = observations.events();
        for _ in 0..2 {
            assert!(matches!(connection.diagnostic(), Err(Error::Protocol(_))));
        }
        assert_eq!(observations.events(), before);
    }
    #[test]
    fn records_runtime_version_and_configuration() {
        let metadata = runtime_info();
        assert_eq!(metadata.version, "3.46.1");
        assert!(metadata.source_id.contains("c9c2ab54"));
        assert!(
            metadata
                .compile_options
                .iter()
                .any(|option| option == "THREADSAFE=1")
        );
    }
    #[test]
    fn select_parameter_copies_42_and_finalizes_before_close() {
        let observations = Observations::default();
        let mut connection = Connection::open_observed(":memory:", observations.clone()).unwrap();
        let mut stmt = statement(&mut connection, "SELECT ?1");
        stmt.bind_int64(1, 42).unwrap();
        assert_eq!(stmt.step(), Ok(Step::Row));
        let value = stmt.column_copy(0).unwrap();
        assert_eq!(stmt.step(), Ok(Step::Done));
        stmt.finalize().unwrap();
        connection.close().unwrap();
        assert_eq!(value, Column::Integer(42));
        assert_eq!(observations.calls("open"), 1);
        assert_eq!(observations.calls("finalize"), 1);
        assert_eq!(observations.calls("close"), 1);
        let events = observations.events();
        let finalize = events
            .iter()
            .position(|e| {
                matches!(
                    e,
                    Event::Call {
                        operation: "finalize",
                        ..
                    }
                )
            })
            .unwrap();
        let close = events
            .iter()
            .position(|e| {
                matches!(
                    e,
                    Event::Call {
                        operation: "close",
                        ..
                    }
                )
            })
            .unwrap();
        assert!(finalize < close);
    }
    #[test]
    fn copied_blob_survives_input_and_native_owner_completion() {
        let observations = Observations::default();
        let mut connection = Connection::open_observed(":memory:", observations.clone()).unwrap();
        let mut stmt = statement(&mut connection, "SELECT ?1");
        {
            let bytes = vec![1, 2, 3];
            stmt.bind_blob_copy(1, &bytes).unwrap();
        }
        assert_eq!(stmt.step(), Ok(Step::Row));
        let value = stmt.column_copy(0).unwrap();
        stmt.finalize().unwrap();
        connection.close().unwrap();
        assert_eq!(value, Column::Blob(vec![1, 2, 3]));
        assert!(observations.events().contains(&Event::InputCopied(3)));
        assert!(observations.events().contains(&Event::OutputCopied(3)));
        assert!(
            !observations.events().iter().any(|event| matches!(
                event,
                Event::Call {
                    operation: "column_blob" | "column_bytes" | "column_type" | "column_count",
                    ..
                }
            )),
            "column APIs return data; observations must not fabricate status codes"
        );
    }
    #[test]
    fn empty_blob_and_sql_null_remain_distinct() {
        let mut connection = Connection::open(":memory:").unwrap();
        let mut stmt = statement(&mut connection, "SELECT ?1, ?2");
        stmt.bind_blob_copy(1, &[]).unwrap();
        stmt.bind_null(2).unwrap();
        assert_eq!(stmt.step(), Ok(Step::Row));
        assert_eq!(stmt.column_copy(0), Ok(Column::Blob(Vec::new())));
        assert_eq!(stmt.column_copy(1), Ok(Column::Null));
    }
    #[test]
    fn empty_blob_checks_suspect_results_before_another_native_interface() {
        let observations = Observations::default();
        let mut connection = Connection::open_observed(":memory:", observations.clone()).unwrap();
        let mut stmt = statement(&mut connection, "SELECT zeroblob(0)");
        assert_eq!(stmt.step(), Ok(Step::Row));
        assert_eq!(stmt.column_copy(0), Ok(Column::Blob(Vec::new())));
        let queries: Vec<_> = observations
            .events()
            .into_iter()
            .filter_map(|event| match event {
                Event::Query { operation } => Some(operation),
                _ => None,
            })
            .collect();
        assert_eq!(
            queries,
            [
                "column_count",
                "column_type",
                "column_blob",
                "errcode",
                "column_bytes",
                "errcode"
            ]
        );
    }
    fn injected_column_failure_is_classified(operation: &'static str) {
        let observations = Observations::default();
        let mut connection = Connection::open_observed(":memory:", observations.clone()).unwrap();
        let mut stmt = statement(&mut connection, "SELECT zeroblob(3)");
        assert_eq!(stmt.step(), Ok(Step::Row));
        test_support::COLUMN_FAILURE.set(Some(operation));
        assert_eq!(
            stmt.column_copy(0),
            Err(Error::InjectedNativeFailure {
                operation,
                code: NOMEM
            })
        );
        assert!(observations.events().contains(&Event::FaultInjected {
            operation,
            code: NOMEM
        }));
        assert!(
            !observations
                .events()
                .iter()
                .any(|event| matches!(event, Event::OutputCopied(_)))
        );
        if operation == "column_blob" {
            assert_eq!(observations.calls("column_bytes"), 0);
        }
        stmt.finalize().unwrap();
        connection.close().unwrap();
        assert_eq!(observations.calls("finalize"), 1);
        assert_eq!(observations.calls("close"), 1);
    }
    #[test]
    fn injected_blob_oom_is_classified_without_claiming_native_exhaustion() {
        injected_column_failure_is_classified("column_blob");
    }
    #[test]
    fn injected_bytes_oom_is_classified_without_claiming_native_exhaustion() {
        injected_column_failure_is_classified("column_bytes");
    }
    #[test]
    fn actual_failed_open_disposes_partial_connection_without_publication() {
        let directory = Directory::new();
        let observations = Observations::default();
        let result =
            Connection::open_observed(&directory.path("missing/db.sqlite"), observations.clone());
        assert!(matches!(
            result,
            Err(Error::Native(NativeError {
                operation: "open",
                code: 14,
                ..
            }))
        ));
        assert_eq!(observations.calls("open"), 1);
        assert_eq!(observations.calls("close"), 1);
    }
    #[test]
    fn malformed_sql_is_error_and_empty_sql_has_no_statement() {
        let mut connection = Connection::open(":memory:").unwrap();
        assert!(matches!(
            connection.prepare("SELECT FROM"),
            Err(Error::Native(_))
        ));
        assert!(connection.prepare("").unwrap().is_none());
        assert!(
            connection
                .prepare("  -- no executable SQL")
                .unwrap()
                .is_none()
        );
    }
    #[test]
    fn unused_sql_is_rejected_and_unpublished_statement_is_finalized() {
        let observations = Observations::default();
        let mut connection = Connection::open_observed(":memory:", observations.clone()).unwrap();
        assert!(matches!(
            connection.prepare("SELECT 1; SELECT 2"),
            Err(Error::InvalidInput(_))
        ));
        assert_eq!(observations.calls("finalize"), 1);
        connection.close().unwrap();
    }
    #[test]
    fn constraint_body_failure_and_consuming_finalize_report_are_preserved() {
        let observations = Observations::default();
        let mut connection = Connection::open_observed(":memory:", observations.clone()).unwrap();
        execute(&mut connection, "CREATE TABLE items(value INTEGER UNIQUE)");
        execute(&mut connection, "INSERT INTO items VALUES (42)");
        let mut stmt = statement(&mut connection, "INSERT INTO items VALUES (42)");
        let body_error = stmt.step().unwrap_err();
        assert!(matches!(
            body_error,
            Error::Native(NativeError {
                operation: "step",
                code: 19,
                ..
            })
        ));
        assert_eq!(stmt.state(), StatementState::Failed);
        let finish_error = stmt.finalize().unwrap_err();
        assert!(matches!(
            finish_error,
            Error::Native(NativeError {
                operation: "finalize",
                code: 19,
                ..
            })
        ));
        assert_eq!(observations.calls("finalize"), 3);
        connection.close().unwrap();
    }
    #[test]
    fn actual_busy_close_retains_connection_until_statement_finishes() {
        let observations = Observations::default();
        let mut connection = Connection::open_observed(":memory:", observations.clone()).unwrap();
        let mut stmt = statement(&mut connection, "SELECT 42");
        assert!(matches!(
            connection.close(),
            Err(Error::Native(NativeError {
                operation: "close",
                code: 5,
                ..
            }))
        ));
        assert_eq!(stmt.step(), Ok(Step::Row));
        assert_eq!(stmt.column_copy(0), Ok(Column::Integer(42)));
        stmt.finalize().unwrap();
        execute(&mut connection, "SELECT 42 WHERE 0");
        connection.close().unwrap();
        assert_eq!(observations.calls("close"), 2);
        assert!(matches!(
            connection.prepare("SELECT 1"),
            Err(Error::Protocol(_))
        ));
    }
    #[test]
    fn drop_order_is_safe_even_if_rust_connection_owner_drops_first() {
        let observations = Observations::default();
        let mut connection = Connection::open_observed(":memory:", observations.clone()).unwrap();
        let stmt = statement(&mut connection, "SELECT 42");
        drop(connection);
        assert_eq!(observations.calls("close"), 0);
        drop(stmt);
        assert_eq!(observations.calls("finalize"), 1);
        assert_eq!(observations.calls("close"), 1);
    }
    #[test]
    fn protocol_checks_prevent_native_column_and_automatic_reset_access() {
        let observations = Observations::default();
        let mut connection = Connection::open_observed(":memory:", observations.clone()).unwrap();
        let mut stmt = statement(&mut connection, "SELECT 42");
        assert!(matches!(stmt.column_copy(0), Err(Error::Protocol(_))));
        assert_eq!(observations.calls("column_type"), 0);
        assert_eq!(stmt.step(), Ok(Step::Row));
        assert!(matches!(stmt.bind_int64(1, 0), Err(Error::Protocol(_))));
        assert_eq!(observations.calls("bind_int64"), 0);
        assert!(matches!(stmt.column_copy(1), Err(Error::InvalidInput(_))));
        assert_eq!(stmt.step(), Ok(Step::Done));
        assert!(matches!(stmt.step(), Err(Error::Protocol(_))));
        assert_eq!(observations.calls("step"), 2);
    }
    #[test]
    fn reset_preserves_bindings_and_clear_replaces_them_with_null() {
        let mut connection = Connection::open(":memory:").unwrap();
        let mut stmt = statement(&mut connection, "SELECT ?1");
        stmt.bind_int64(1, 42).unwrap();
        assert_eq!(stmt.step(), Ok(Step::Row));
        stmt.reset().unwrap();
        assert_eq!(stmt.step(), Ok(Step::Row));
        assert_eq!(stmt.column_copy(0), Ok(Column::Integer(42)));
        stmt.reset().unwrap();
        stmt.clear_bindings().unwrap();
        assert_eq!(stmt.step(), Ok(Step::Row));
        assert_eq!(stmt.column_copy(0), Ok(Column::Null));
    }
    #[test]
    fn invalid_abi_inputs_and_storage_kind_are_checked() {
        assert!(matches!(
            Connection::open("x\0y"),
            Err(Error::InvalidInput(_))
        ));
        let mut connection = Connection::open(":memory:").unwrap();
        assert!(matches!(
            connection.prepare("SELECT\0 1"),
            Err(Error::InvalidInput(_))
        ));
        let mut stmt = statement(&mut connection, "SELECT ?1, 'text'");
        assert!(matches!(
            stmt.bind_int64(0, 42),
            Err(Error::InvalidInput(_))
        ));
        assert!(matches!(
            stmt.bind_int64(usize::MAX, 42),
            Err(Error::InvalidInput(_))
        ));
        assert!(matches!(
            stmt.bind_int64(2, 42),
            Err(Error::Native(NativeError { code: 25, .. }))
        ));
        stmt.bind_int64(1, i64::MIN).unwrap();
        assert_eq!(stmt.step(), Ok(Step::Row));
        assert_eq!(stmt.column_copy(0), Ok(Column::Integer(i64::MIN)));
        assert_eq!(stmt.column_copy(1), Err(Error::ColumnKind));
        stmt.reset().unwrap();
        stmt.bind_int64(1, i64::MAX).unwrap();
        assert_eq!(stmt.step(), Ok(Step::Row));
        assert_eq!(stmt.column_copy(0), Ok(Column::Integer(i64::MAX)));
    }
    #[test]
    fn independent_connections_and_repeat_activations_keep_distinct_bindings() {
        for _ in 0..2 {
            let mut first = Connection::open(":memory:").unwrap();
            let mut second = Connection::open(":memory:").unwrap();
            let mut first_stmt = statement(&mut first, "SELECT ?1");
            let mut second_stmt = statement(&mut second, "SELECT ?1");
            first_stmt.bind_int64(1, 42).unwrap();
            second_stmt.bind_int64(1, 99).unwrap();
            assert_eq!(second_stmt.step(), Ok(Step::Row));
            assert_eq!(first_stmt.step(), Ok(Step::Row));
            assert_eq!(first_stmt.column_copy(0), Ok(Column::Integer(42)));
            assert_eq!(second_stmt.column_copy(0), Ok(Column::Integer(99)));
        }
    }
    #[test]
    fn file_persistence_is_observed_after_close_and_reopen() {
        let directory = Directory::new();
        let path = directory.path("database.sqlite");
        {
            let mut connection = Connection::open(&path).unwrap();
            execute(&mut connection, "CREATE TABLE values_table(value INTEGER)");
            let mut stmt = statement(&mut connection, "INSERT INTO values_table VALUES (?1)");
            stmt.bind_int64(1, 42).unwrap();
            assert_eq!(stmt.step(), Ok(Step::Done));
            stmt.finalize().unwrap();
            connection.close().unwrap();
        }
        let mut connection = Connection::open(&path).unwrap();
        let mut stmt = statement(&mut connection, "SELECT value FROM values_table");
        assert_eq!(stmt.step(), Ok(Step::Row));
        assert_eq!(stmt.column_copy(0), Ok(Column::Integer(42)));
        assert_eq!(stmt.step(), Ok(Step::Done));
        stmt.finalize().unwrap();
        connection.close().unwrap();
    }
    #[test]
    fn injected_open_publication_failure_is_distinct_and_disposes_native_owner() {
        let observations = Observations::default();
        test_support::FAIL_OPEN_PUBLICATION.set(true);
        assert!(matches!(
            Connection::open_observed(":memory:", observations.clone()),
            Err(Error::InjectedPublicationFailure)
        ));
        assert_eq!(observations.calls("open"), 1);
        assert_eq!(observations.calls("close"), 1);
    }
    #[test]
    fn injected_statement_publication_failure_finalizes_before_close() {
        let observations = Observations::default();
        let mut connection = Connection::open_observed(":memory:", observations.clone()).unwrap();
        test_support::FAIL_PREPARE_PUBLICATION.set(true);
        assert!(matches!(
            connection.prepare("SELECT 42"),
            Err(Error::InjectedPublicationFailure)
        ));
        assert_eq!(observations.calls("finalize"), 1);
        connection.close().unwrap();
        assert_eq!(observations.calls("close"), 1);
    }
}
