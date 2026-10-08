//! Small direct SQLite reference, checked against the pinned sqlite3.h and C shim.
//! Statement borrows its connection; copied columns own their Rust storage.
//! The existing C shim supplies SQLITE_TRANSIENT without constructing its
//! implementation-defined destructor sentinel as a Rust function pointer.
#![allow(dead_code, reason = "each reference crate uses a subset of the shared bridge")]

use std::{
    cell::RefCell,
    collections::BTreeMap,
    ffi::{CStr, CString, c_char, c_int, c_void},
    ptr::{self, NonNull},
    rc::Rc,
};

#[repr(C)]
struct Db { _private: [u8; 0] }
#[repr(C)]
struct Stmt { _private: [u8; 0] }

#[link(name = "libsqlite3.so.0", kind = "dylib", modifiers = "+verbatim")]
unsafe extern "C" {
    fn sqlite3_open_v2(path: *const c_char, db: *mut *mut Db, flags: c_int, vfs: *const c_char) -> c_int;
    fn sqlite3_prepare_v2(db: *mut Db, sql: *const c_char, len: c_int, stmt: *mut *mut Stmt, tail: *mut *const c_char) -> c_int;
    fn sqlite3_bind_int64(stmt: *mut Stmt, index: c_int, value: i64) -> c_int;
    fn sqlite3_bind_null(stmt: *mut Stmt, index: c_int) -> c_int;
    fn sqlite3_step(stmt: *mut Stmt) -> c_int;
    fn sqlite3_column_count(stmt: *mut Stmt) -> c_int;
    fn sqlite3_column_type(stmt: *mut Stmt, column: c_int) -> c_int;
    fn sqlite3_column_int64(stmt: *mut Stmt, column: c_int) -> i64;
    fn sqlite3_column_text(stmt: *mut Stmt, column: c_int) -> *const u8;
    fn sqlite3_column_blob(stmt: *mut Stmt, column: c_int) -> *const c_void;
    fn sqlite3_column_bytes(stmt: *mut Stmt, column: c_int) -> c_int;
    fn sqlite3_reset(stmt: *mut Stmt) -> c_int;
    fn sqlite3_clear_bindings(stmt: *mut Stmt) -> c_int;
    fn sqlite3_finalize(stmt: *mut Stmt) -> c_int;
    fn sqlite3_close(db: *mut Db) -> c_int;
    fn sqlite3_close_v2(db: *mut Db) -> c_int;
    fn sqlite3_errmsg(db: *mut Db) -> *const c_char;
}

#[link(name = "ash_sqlite_bridge", kind = "static")]
unsafe extern "C" {
    fn ash_sqlite_bind_text_copy(stmt: *mut Stmt, index: c_int, text: *const c_char, len: c_int) -> c_int;
    fn ash_sqlite_bind_blob_copy(stmt: *mut Stmt, index: c_int, bytes: *const c_void, len: c_int) -> c_int;
}

const OK: c_int = 0;
const ROW: c_int = 100;
const DONE: c_int = 101;
const INTEGER: c_int = 1;
const TEXT: c_int = 3;
const BLOB: c_int = 4;
const NULL: c_int = 5;

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    Native(i32, String), BadText, BadIndex, BadColumn, BadKind,
    BadLength, MissingRow, UnexpectedRow, Protocol, EmptySql, MultipleStatements,
    InvalidUtf8, Io(String),
}
pub type Result<T> = std::result::Result<T, Error>;
impl From<std::io::Error> for Error {
    fn from(error: std::io::Error) -> Self { Self::Io(error.to_string()) }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Completion<E> { Closed, Failed(E) }
#[derive(Debug, PartialEq, Eq)]
pub enum Scope<I, E, T> { InitFailed(I), Completed(T, Completion<E>) }
pub type Report<T> = Scope<Error, Error, T>;
#[derive(Debug, PartialEq, Eq)]
pub enum TextOrNull { TextValue(String), NullText }
#[derive(Debug, PartialEq, Eq)]
pub enum BytesOrNull { BlobBytes(Vec<u8>), NullBytes }
pub struct SqlText<'a>(pub &'a str);
#[derive(Debug, PartialEq, Eq)]
pub enum Step { Row, Done }

#[derive(Debug, Default)]
pub struct Stats {
    calls: BTreeMap<&'static str, usize>,
    events: Vec<&'static str>,
    pub input_copies: Vec<usize>,
    pub output_copies: Vec<usize>,
}
pub type Log = Rc<RefCell<Stats>>;
pub fn log() -> Log { Rc::new(RefCell::new(Stats::default())) }
fn called(log: &Log, operation: &'static str) {
    let mut stats = log.borrow_mut();
    *stats.calls.entry(operation).or_default() += 1;
    stats.events.push(operation);
}
pub fn assert_calls(log: &Log, expected: &[(&'static str, usize)]) {
    let stats = log.borrow();
    for &(operation, count) in expected {
        assert_eq!(stats.calls.get(operation).copied().unwrap_or(0), count, "{operation}");
    }
}
pub fn assert_finished(log: &Log, connections: usize, statements: usize) {
    assert_calls(log, &[("open", connections), ("close", connections),
                        ("prepare", statements), ("finalize", statements), ("close_v2", 0)]);
    let mut active = 0;
    let mut connection_open = false;
    for event in &log.borrow().events {
        match *event {
            "open" => { assert!(!connection_open, "reopen follows the previous close"); connection_open = true; }
            "prepare" => active += 1,
            "finalize" => { assert!(active > 0); active -= 1; }
            "close" => { assert_eq!(active, 0, "finalize before connection close"); assert!(connection_open); connection_open = false; }
            _ => {}
        }
    }
    assert_eq!(active, 0);
    assert!(!connection_open);
}

pub struct Connection { raw: Option<NonNull<Db>>, log: Log }
impl Connection {
    pub fn open(path: &str, log: &Log) -> Result<Self> {
        let path = CString::new(path).map_err(|_| Error::BadText)?;
        let mut raw = ptr::null_mut();
        called(log, "open");
        // SAFETY: terminated path and valid out-pointer; SQLite owns the new handle.
        let code = unsafe { sqlite3_open_v2(path.as_ptr(), &mut raw, 2 | 4, ptr::null()) };
        let connection = Self { raw: NonNull::new(raw), log: Rc::clone(log) };
        if code != OK { return Err(connection.error(code)); }
        if connection.raw.is_none() { return Err(Error::Protocol); }
        Ok(connection)
    }
    fn raw(&self) -> *mut Db { self.raw.expect("live connection").as_ptr() }
    fn error(&self, code: c_int) -> Error {
        let message = if let Some(raw) = self.raw {
            // SAFETY: an active SQLite connection provides a terminated diagnostic.
            unsafe { CStr::from_ptr(sqlite3_errmsg(raw.as_ptr())).to_string_lossy().into_owned() }
        } else { "sqlite did not return a connection".into() };
        Error::Native(code, message)
    }
    fn checked(&self, code: c_int) -> Result<()> {
        if code == OK { Ok(()) } else { Err(self.error(code)) }
    }
    pub fn prepare(&self, sql: SqlText<'_>) -> Result<Statement<'_>> {
        let sql = CString::new(sql.0).map_err(|_| Error::BadText)?;
        let len = sql.as_bytes_with_nul().len().try_into().map_err(|_| Error::BadLength)?;
        let mut raw = ptr::null_mut();
        let mut tail = ptr::null();
        called(&self.log, "prepare");
        // SAFETY: active connection, complete SQL bytes and valid output pointers.
        let code = unsafe { sqlite3_prepare_v2(self.raw(), sql.as_ptr(), len, &mut raw, &mut tail) };
        let statement = Statement { raw: NonNull::new(raw), db: self, state: State::Ready };
        if code != OK { return Err(self.error(code)); }
        if statement.raw.is_none() { return Err(Error::EmptySql); }
        // SAFETY: SQLite's tail points into the still-live terminated SQL buffer.
        if !tail.is_null() && !unsafe { CStr::from_ptr(tail) }.to_bytes().iter().all(u8::is_ascii_whitespace) {
            return Err(Error::MultipleStatements);
        }
        Ok(statement)
    }
    fn close(&mut self) -> Result<()> {
        let Some(raw) = self.raw.take() else { return Ok(()); };
        called(&self.log, "close");
        // SAFETY: borrowing prevents a live Statement when Connection is consumed/dropped.
        let code = unsafe { sqlite3_close(raw.as_ptr()) };
        if code == OK { return Ok(()); }
        // A failed close retains the handle. Schedule native cleanup rather than leak it.
        self.raw = Some(raw);
        let error = self.error(code);
        called(&self.log, "close_v2");
        // SAFETY: failed sqlite3_close leaves this connection active.
        unsafe { sqlite3_close_v2(raw.as_ptr()); }
        self.raw = None;
        Err(error)
    }
    pub fn finish(mut self) -> Result<()> { self.close() }
}
impl Drop for Connection { fn drop(&mut self) { let _ = self.close(); } }

#[derive(PartialEq, Eq)]
enum State { Ready, Row, Done }
pub struct Statement<'db> { raw: Option<NonNull<Stmt>>, db: &'db Connection, state: State }
pub trait StatementOps {
    fn bind_int(&mut self, index: i32, value: i64) -> Result<()>;
    fn bind_text(&mut self, index: i32, value: &TextOrNull) -> Result<()>;
    fn bind_bytes(&mut self, index: i32, value: &BytesOrNull) -> Result<()>;
    fn step(&mut self) -> Result<Step>;
    fn column_int(&self, column: i32) -> Result<i64>;
    fn column_text(&self, column: i32) -> Result<TextOrNull>;
    fn column_bytes(&self, column: i32) -> Result<BytesOrNull>;
    fn reset(&mut self) -> Result<()>;
    fn clear_bindings(&mut self) -> Result<()>;
}
impl Statement<'_> {
    fn raw(&self) -> *mut Stmt { self.raw.expect("live statement").as_ptr() }
    fn bindable(&self, index: i32) -> Result<()> {
        if self.state != State::Ready { return Err(Error::Protocol); }
        if index < 1 { return Err(Error::BadIndex); }
        Ok(())
    }
    fn column_kind(&self, column: i32) -> Result<c_int> {
        if self.state != State::Row { return Err(Error::Protocol); }
        called(&self.db.log, "column_count");
        // SAFETY: live statement, stepped onto a row before inspecting columns.
        let count = unsafe { sqlite3_column_count(self.raw()) };
        if column < 0 || column >= count { return Err(Error::BadColumn); }
        called(&self.db.log, "column_type");
        // SAFETY: column is within this live row's bounds.
        Ok(unsafe { sqlite3_column_type(self.raw(), column) })
    }
    fn copied_column(&self, column: i32, text: bool) -> Result<Vec<u8>> {
        // SAFETY: caller checked the live row and exact storage kind; no mutation
        // occurs between pointer acquisition, byte count and the immediate copy.
        let (bytes, len) = unsafe {
            let bytes = if text { sqlite3_column_text(self.raw(), column) }
                        else { sqlite3_column_blob(self.raw(), column).cast() };
            (bytes, sqlite3_column_bytes(self.raw(), column))
        };
        let len: usize = len.try_into().map_err(|_| Error::BadLength)?;
        let copied = if len == 0 { Vec::new() } else {
            if bytes.is_null() { return Err(Error::Protocol); }
            // SAFETY: SQLite guarantees len accessible bytes until row mutation.
            unsafe { std::slice::from_raw_parts(bytes, len) }.to_vec()
        };
        self.db.log.borrow_mut().output_copies.push(len);
        Ok(copied)
    }
    fn finalize(&mut self) -> Result<()> {
        let Some(raw) = self.raw.take() else { return Ok(()); };
        called(&self.db.log, "finalize");
        // SAFETY: this guard uniquely owns the statement; finalize consumes it even on error.
        self.db.checked(unsafe { sqlite3_finalize(raw.as_ptr()) })
    }
    pub fn finish(mut self) -> Result<()> { self.finalize() }
}
impl Drop for Statement<'_> { fn drop(&mut self) { let _ = self.finalize(); } }
impl StatementOps for Statement<'_> {
    fn bind_int(&mut self, index: i32, value: i64) -> Result<()> {
        self.bindable(index)?;
        called(&self.db.log, "bind_int64");
        // SAFETY: active, unstepped statement and checked positive parameter index.
        self.db.checked(unsafe { sqlite3_bind_int64(self.raw(), index, value) })
    }
    fn bind_text(&mut self, index: i32, value: &TextOrNull) -> Result<()> {
        self.bindable(index)?;
        let TextOrNull::TextValue(text) = value else { return self.bind_null(index); };
        if text.contains('\0') { return Err(Error::BadText); }
        let len = text.len().try_into().map_err(|_| Error::BadLength)?;
        called(&self.db.log, "bind_text_copy");
        let pointer = if text.is_empty() { c"".as_ptr() } else { text.as_ptr().cast() };
        // SAFETY: valid UTF-8 bytes remain live during the C shim's SQLITE_TRANSIENT copy.
        self.db.checked(unsafe { ash_sqlite_bind_text_copy(self.raw(), index, pointer, len) })?;
        self.db.log.borrow_mut().input_copies.push(text.len());
        Ok(())
    }
    fn bind_bytes(&mut self, index: i32, value: &BytesOrNull) -> Result<()> {
        self.bindable(index)?;
        let BytesOrNull::BlobBytes(bytes) = value else { return self.bind_null(index); };
        let len = bytes.len().try_into().map_err(|_| Error::BadLength)?;
        called(&self.db.log, "bind_blob_copy");
        let pointer = if bytes.is_empty() { c"".as_ptr().cast() } else { bytes.as_ptr().cast() };
        // SAFETY: nonnull pointer and nonnegative length; shim copies before returning.
        self.db.checked(unsafe { ash_sqlite_bind_blob_copy(self.raw(), index, pointer, len) })?;
        self.db.log.borrow_mut().input_copies.push(bytes.len());
        Ok(())
    }
    fn step(&mut self) -> Result<Step> {
        if self.state == State::Done { return Err(Error::Protocol); }
        called(&self.db.log, "step");
        // SAFETY: uniquely borrowed live statement, not already completed.
        match unsafe { sqlite3_step(self.raw()) } {
            ROW => { self.state = State::Row; Ok(Step::Row) }
            DONE => { self.state = State::Done; Ok(Step::Done) }
            code => Err(self.db.error(code)),
        }
    }
    fn column_int(&self, column: i32) -> Result<i64> {
        if self.column_kind(column)? != INTEGER { return Err(Error::BadKind); }
        called(&self.db.log, "column_int64");
        // SAFETY: validated INTEGER column in the current live row.
        Ok(unsafe { sqlite3_column_int64(self.raw(), column) })
    }
    fn column_text(&self, column: i32) -> Result<TextOrNull> {
        match self.column_kind(column)? {
            NULL => Ok(TextOrNull::NullText),
            TEXT => {
                called(&self.db.log, "column_text");
                let bytes = self.copied_column(column, true)?;
                Ok(TextOrNull::TextValue(String::from_utf8(bytes).map_err(|_| Error::InvalidUtf8)?))
            }
            _ => Err(Error::BadKind),
        }
    }
    fn column_bytes(&self, column: i32) -> Result<BytesOrNull> {
        match self.column_kind(column)? {
            NULL => Ok(BytesOrNull::NullBytes),
            BLOB => { called(&self.db.log, "column_blob"); Ok(BytesOrNull::BlobBytes(self.copied_column(column, false)?)) }
            _ => Err(Error::BadKind),
        }
    }
    fn reset(&mut self) -> Result<()> {
        called(&self.db.log, "reset");
        // SAFETY: live statement; reset preserves SQLite-owned copied bindings.
        self.db.checked(unsafe { sqlite3_reset(self.raw()) })?;
        self.state = State::Ready;
        Ok(())
    }
    fn clear_bindings(&mut self) -> Result<()> {
        if self.state != State::Ready { return Err(Error::Protocol); }
        called(&self.db.log, "clear_bindings");
        // SAFETY: live reset/unstepped statement; SQLite releases its binding copies.
        self.db.checked(unsafe { sqlite3_clear_bindings(self.raw()) })
    }
}
impl Statement<'_> {
    fn bind_null(&mut self, index: i32) -> Result<()> {
        called(&self.db.log, "bind_null");
        // SAFETY: caller checked bindable state and parameter index.
        self.db.checked(unsafe { sqlite3_bind_null(self.raw(), index) })
    }
}

fn completion(result: Result<()>) -> Completion<Error> {
    match result { Ok(()) => Completion::Closed, Err(error) => Completion::Failed(error) }
}
pub fn with_connection<T>(path: &str, log: &Log, body: impl FnOnce(&Connection) -> T) -> Report<T> {
    match Connection::open(path, log) {
        Err(error) => Scope::InitFailed(error),
        Ok(db) => { let value = body(&db); Scope::Completed(value, completion(db.finish())) }
    }
}
pub fn with_statement<T>(db: &Connection, sql: SqlText<'_>, body: impl FnOnce(&mut Statement<'_>) -> T) -> Report<T> {
    match db.prepare(sql) {
        Err(error) => Scope::InitFailed(error),
        Ok(mut stmt) => { let value = body(&mut stmt); Scope::Completed(value, completion(stmt.finish())) }
    }
}
pub fn closed<T>(report: Report<T>) -> Result<T> {
    match report {
        Scope::Completed(value, Completion::Closed) => Ok(value),
        Scope::InitFailed(error) | Scope::Completed(_, Completion::Failed(error)) => Err(error),
    }
}
pub fn expect_done<S: StatementOps>(stmt: &mut S) -> Result<()> {
    match stmt.step()? { Step::Done => Ok(()), Step::Row => Err(Error::UnexpectedRow) }
}
#[derive(Debug, PartialEq, Eq)]
pub enum List<T> { Nil, Cons(T, Box<List<T>>) }
pub fn collect<S: StatementOps, T>(stmt: &mut S, read: &mut impl FnMut(&S) -> Result<T>) -> Result<List<T>> {
    match stmt.step()? {
        Step::Done => Ok(List::Nil),
        Step::Row => { let value = read(stmt)?; Ok(List::Cons(value, Box::new(collect(stmt, read)?))) }
    }
}
