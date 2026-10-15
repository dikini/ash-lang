//! Executable SQLite bindings outside compiler-specific dispatch.

use crate::{
    Column, Connection, CopyColumnKind, DiagnosticCopyFailure, Error, Event, InputError,
    NativeError, Observations, ProtocolError, Statement, StatementState, Step, sqlite_manifest,
};
use ash::{
    foreign::{
        ForeignManifest, ForeignModuleFact,
        runtime::{
            ExecutableForeignModule, ForeignAcquisition, ForeignCompletion, ForeignData,
            ForeignDataNode, ForeignExecutionError, ForeignFinishContext, ForeignOperationKey,
            ForeignRuntimeBinding, NativeResourceOwner,
        },
    },
    types::{ConstructorId, TYPE_WORK_LIMIT},
};
use std::{any::Any, cell::RefCell, sync::Arc};

/// Binds the exact SQLite registration retained by the source loader.
///
/// # Errors
/// Rejects an unrelated or changed manifest before executing native code.
pub fn sqlite_binding(
    manifest: Arc<ForeignManifest>,
    observations: Observations,
) -> Result<ForeignRuntimeBinding, ForeignExecutionError> {
    sqlite_binding_with_finish_faults(manifest, observations, SqliteFinishFaults::default())
}

/// Explicit deterministic completion faults, separate from real native calls.
#[derive(Clone, Copy, Debug, Default)]
pub struct SqliteFinishFaults {
    /// Finalize the real statement, then report an injected consumed error.
    pub consumed_finalize: bool,
    /// Refuse source close before transition, preserving its exact native owner.
    pub retained_close: bool,
}

/// Binds SQLite with explicitly labelled completion fault observations.
/// # Errors
/// Rejects an unrelated manifest before executing native code.
pub fn sqlite_binding_with_finish_faults(
    manifest: Arc<ForeignManifest>,
    observations: Observations,
    faults: SqliteFinishFaults,
) -> Result<ForeignRuntimeBinding, ForeignExecutionError> {
    let expected = sqlite_manifest(manifest.id())
        .map_err(|_| ForeignExecutionError("invalid SQLite manifest"))?;
    if manifest.as_ref() != &expected {
        return Err(ForeignExecutionError(
            "SQLite adapter requires its exact manifest contract",
        ));
    }
    Ok(ForeignRuntimeBinding::new(
        manifest,
        Box::new(SqliteBinding {
            observations,
            faults,
        }),
    ))
}
#[derive(Debug)]
struct SqliteBinding {
    observations: Observations,
    faults: SqliteFinishFaults,
}
#[derive(Debug)]
struct ConnectionOwner(RefCell<Option<Connection>>);
#[derive(Debug)]
struct StatementOwner(RefCell<Option<Statement>>);
impl NativeResourceOwner for ConnectionOwner {
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }
}
impl NativeResourceOwner for StatementOwner {
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }
}

struct Codec<'a> {
    module: &'a ForeignModuleFact,
    nodes: Vec<ForeignDataNode>,
    work: usize,
}
impl<'a> Codec<'a> {
    fn new(module: &'a ForeignModuleFact) -> Self {
        Self {
            module,
            nodes: Vec::new(),
            work: 0,
        }
    }
    fn push(&mut self, node: ForeignDataNode) -> Result<usize, ForeignExecutionError> {
        let payload_work = match &node {
            ForeignDataNode::Integer(integer) => usize::try_from(integer.magnitude_byte_length())
                .map_err(|_| ForeignExecutionError::WORK_EXHAUSTED)?
                .max(1),
            ForeignDataNode::Bytes(bytes) => bytes.len(),
            ForeignDataNode::String(text) => text.len(),
            ForeignDataNode::Tuple(children) => children.len(),
            _ => 0,
        };
        self.work = self
            .work
            .checked_add(1)
            .and_then(|work| work.checked_add(payload_work))
            .filter(|work| *work <= TYPE_WORK_LIMIT)
            .ok_or(ForeignExecutionError::WORK_EXHAUSTED)?;
        self.nodes
            .try_reserve(1)
            .map_err(|_| ForeignExecutionError::STORAGE_REFUSED)?;
        let index = self.nodes.len();
        self.nodes.push(node);
        Ok(index)
    }
    fn constructor(
        &mut self,
        name: &str,
        payload: Option<usize>,
    ) -> Result<usize, ForeignExecutionError> {
        let id = self
            .module
            .constructors
            .get(name)
            .copied()
            .ok_or(ForeignExecutionError("SQLite codec constructor absent"))?;
        self.push(ForeignDataNode::Constructor(id, payload))
    }
    fn tuple(&mut self, fields: &[usize]) -> Result<usize, ForeignExecutionError> {
        let mut children = Vec::new();
        children
            .try_reserve_exact(fields.len())
            .map_err(|_| ForeignExecutionError::STORAGE_REFUSED)?;
        children.extend_from_slice(fields);
        self.push(ForeignDataNode::Tuple(children.into_boxed_slice()))
    }
    fn bytes(&mut self, bytes: &[u8]) -> Result<usize, ForeignExecutionError> {
        if bytes.len() >= TYPE_WORK_LIMIT.saturating_sub(self.work) {
            return Err(ForeignExecutionError::WORK_EXHAUSTED);
        }

        let mut copied = Vec::new();
        copied
            .try_reserve_exact(bytes.len())
            .map_err(|_| ForeignExecutionError::STORAGE_REFUSED)?;
        copied.extend_from_slice(bytes);
        self.push(ForeignDataNode::Bytes(Arc::from(copied)))
    }
    fn string(&mut self, text: &str) -> Result<usize, ForeignExecutionError> {
        if text.len() >= TYPE_WORK_LIMIT.saturating_sub(self.work) {
            return Err(ForeignExecutionError::WORK_EXHAUSTED);
        }
        let mut copied = String::new();
        copied
            .try_reserve_exact(text.len())
            .map_err(|_| ForeignExecutionError::STORAGE_REFUSED)?;
        copied.push_str(text);
        self.push(ForeignDataNode::String(Arc::from(copied)))
    }
    fn error(&mut self, error: &Error) -> Result<usize, ForeignExecutionError> {
        self.error_with_state(error, None)
    }
    fn error_with_state(
        &mut self,
        error: &Error,
        state: Option<StatementState>,
    ) -> Result<usize, ForeignExecutionError> {
        match error {
            Error::Native(native) => {
                let code = self.push(ForeignDataNode::Integer(ash::integer::Integer::from_i64(
                    i64::from(native.code),
                )))?;
                let message = self.string(&native.message)?;
                let payload = self.tuple(&[code, message])?;
                self.constructor("NativeFailure", Some(payload))
            }
            Error::InvalidInput(input) => {
                let name = match input {
                    InputError::PathContainsNul => "BadPath",
                    InputError::SqlContainsNul | InputError::SqlLength => "BadSql",
                    InputError::UnusedSql => "MultipleStatements",
                    InputError::ParameterIndexZero | InputError::ParameterIndexRange => "BadIndex",
                    InputError::ColumnIndexRange | InputError::ColumnOutsideRow => "BadColumn",
                    InputError::BlobLength => "BadBytes",
                    InputError::TextLength | InputError::TextContainsNul => "BadText",
                };
                let fault = self.constructor(name, None)?;
                self.constructor("InputFailure", Some(fault))
            }
            Error::ColumnKind => {
                let fault = self.constructor("ColumnTypeMismatch", None)?;
                self.constructor("InputFailure", Some(fault))
            }
            Error::Protocol(protocol) => {
                let name = match protocol {
                    ProtocolError::ConnectionClosed => "ClosedOwner",
                    ProtocolError::BindingRequiresPrepared => "NotPrepared",
                    ProtocolError::ColumnRequiresRow => "NotRow",
                    ProtocolError::StepRequiresPreparedOrRow
                        if state == Some(StatementState::Done) =>
                    {
                        "AfterDone"
                    }
                    ProtocolError::StepRequiresPreparedOrRow => "NotPrepared",
                };
                let fault = self.constructor(name, None)?;
                self.constructor("ProtocolFailure", Some(fault))
            }
            Error::InvalidUtf8 => self.constructor("ConversionFailure", None),
            Error::DiagnosticCopyRefused { cause, .. } => match cause {
                DiagnosticCopyFailure::WorkExhausted { .. } => {
                    Err(ForeignExecutionError::WORK_EXHAUSTED)
                }
                DiagnosticCopyFailure::StorageRefused { .. } => {
                    Err(ForeignExecutionError::STORAGE_REFUSED)
                }
                DiagnosticCopyFailure::InvalidUtf8 => self.constructor("ConversionFailure", None),
            },
            Error::CopyWorkExhausted { .. } => Err(ForeignExecutionError::WORK_EXHAUSTED),
            Error::StorageRefused { .. } => Err(ForeignExecutionError::STORAGE_REFUSED),
            Error::Contract(_)
            | Error::InjectedPublicationFailure
            | Error::InjectedNativeFailure { .. } => Err(ForeignExecutionError(
                "SQLite native contract or injected failure",
            )),
        }
    }
    fn report_statement_error(
        mut self,
        wrapper: &str,
        error: &Error,
        state: StatementState,
    ) -> Result<ForeignData, ForeignExecutionError> {
        let error = self.error_with_state(error, Some(state))?;
        let root = self.constructor(wrapper, Some(error))?;
        self.finish(root)
    }
    fn report_error(
        mut self,
        wrapper: &str,
        error: &Error,
    ) -> Result<ForeignData, ForeignExecutionError> {
        let error = self.error(error)?;
        let root = self.constructor(wrapper, Some(error))?;
        ForeignData::new(self.nodes, root)
    }
    fn input_error(
        mut self,
        wrapper: &str,
        fault: &str,
    ) -> Result<ForeignData, ForeignExecutionError> {
        let fault = self.constructor(fault, None)?;
        let error = self.constructor("InputFailure", Some(fault))?;
        let root = self.constructor(wrapper, Some(error))?;
        self.finish(root)
    }
    fn finish(self, root: usize) -> Result<ForeignData, ForeignExecutionError> {
        ForeignData::new(self.nodes, root)
    }
}
fn injected_error(
    operation: &'static str,
    code: i32,
    message: &str,
) -> Result<Error, ForeignExecutionError> {
    let mut copied = String::new();
    copied
        .try_reserve_exact(message.len())
        .map_err(|_| ForeignExecutionError::STORAGE_REFUSED)?;
    copied.push_str(message);
    Ok(Error::Native(NativeError {
        operation,
        code,
        message: copied,
    }))
}
fn node(input: &ForeignData, index: usize) -> Result<&ForeignDataNode, ForeignExecutionError> {
    input
        .node(index)
        .ok_or(ForeignExecutionError("SQLite input codec index missing"))
}
fn tuple(input: &ForeignData, index: usize) -> Result<&[usize], ForeignExecutionError> {
    match node(input, index)? {
        ForeignDataNode::Tuple(fields) => Ok(fields),
        _ => Err(ForeignExecutionError("SQLite input expected tuple")),
    }
}
fn integer(
    input: &ForeignData,
    index: usize,
) -> Result<&ash::integer::Integer, ForeignExecutionError> {
    match node(input, index)? {
        ForeignDataNode::Integer(value) => Ok(value),
        _ => Err(ForeignExecutionError("SQLite input expected integer")),
    }
}
fn checked_index(
    input: &ForeignData,
    index: usize,
    parameter: bool,
) -> Result<Option<usize>, ForeignExecutionError> {
    let value = integer(input, index)?
        .to_i64()
        .and_then(|value| std::ffi::c_int::try_from(value).ok())
        .and_then(|value| usize::try_from(value).ok())
        .filter(|value| !parameter || *value != 0);
    Ok(value)
}
fn string(input: &ForeignData, index: usize) -> Result<&str, ForeignExecutionError> {
    match node(input, index)? {
        ForeignDataNode::String(text) => Ok(text),
        _ => Err(ForeignExecutionError("SQLite input expected packed string")),
    }
}
fn constructor(
    module: &ForeignModuleFact,
    name: &str,
) -> Result<ConstructorId, ForeignExecutionError> {
    module
        .constructors
        .get(name)
        .copied()
        .ok_or(ForeignExecutionError("SQLite constructor absent"))
}
fn bytes(input: &ForeignData, index: usize) -> Result<&[u8], ForeignExecutionError> {
    match node(input, index)? {
        ForeignDataNode::Bytes(bytes) => Ok(bytes),
        _ => Err(ForeignExecutionError("SQLite input expected packed bytes")),
    }
}
fn connection<'a>(
    states: &[&'a dyn NativeResourceOwner],
) -> Result<&'a ConnectionOwner, ForeignExecutionError> {
    states
        .first()
        .and_then(|owner| (*owner).as_any().downcast_ref())
        .ok_or(ForeignExecutionError("SQLite connection state mismatch"))
}
fn statement<'a>(
    states: &[&'a dyn NativeResourceOwner],
) -> Result<&'a StatementOwner, ForeignExecutionError> {
    states
        .first()
        .and_then(|owner| (*owner).as_any().downcast_ref())
        .ok_or(ForeignExecutionError("SQLite statement state mismatch"))
}

impl ExecutableForeignModule for SqliteBinding {
    fn preflight(&self, module: &ForeignModuleFact) -> Result<(), ForeignExecutionError> {
        let expected = sqlite_manifest(module.admission.registration_id)
            .map_err(|_| ForeignExecutionError("SQLite manifest unavailable"))?;
        if module.manifest().as_ref() != &expected
            || module.effects.len() != 2
            || module.operations.len() != 14
        {
            return Err(ForeignExecutionError("SQLite executable contract mismatch"));
        }
        for name in [
            "InMemory",
            "File",
            "OpenFailure",
            "CloseFailure",
            "PrepareFailure",
            "EmptySql",
            "FinalizeFailure",
            "Ok",
            "Err",
            "Row",
            "Done",
            "StepError",
            "NativeFailure",
            "InputFailure",
            "ProtocolFailure",
            "ConversionFailure",
            "BadIndex",
            "BadInteger",
            "BadBytes",
            "BadColumn",
            "BadText",
            "MultipleStatements",
            "NotPrepared",
            "NotRow",
            "AfterDone",
            "AllocationFailure",
            "NullText",
            "TextValue",
            "ColumnTypeMismatch",
            "ClosedOwner",
            "NullBytes",
            "BlobBytes",
            "BadPath",
            "BadSql",
            "Acquired",
            "Refused",
            "Consumed",
            "ConsumedFailure",
            "Retained",
        ] {
            constructor(module, name)?;
        }
        Ok(())
    }
    fn acquire(
        &self,
        key: ForeignOperationKey,
        module: &ForeignModuleFact,
        input: &ForeignData,
        states: &[&dyn NativeResourceOwner],
    ) -> Result<ForeignAcquisition, ForeignExecutionError> {
        match (key.effect, key.operation) {
            (0, 0) => {
                if !states.is_empty() {
                    return Err(ForeignExecutionError("SQLite open has borrowed state"));
                }
                let path = match node(input, input.root())? {
                    ForeignDataNode::Constructor(id, None)
                        if *id == constructor(module, "InMemory")? =>
                    {
                        ":memory:"
                    }
                    ForeignDataNode::Constructor(id, Some(payload))
                        if *id == constructor(module, "File")? =>
                    {
                        string(input, *payload)?
                    }
                    _ => return Err(ForeignExecutionError("SQLite open configuration mismatch")),
                };
                if path.as_bytes().contains(&0) {
                    return Ok(ForeignAcquisition::Refused(
                        Codec::new(module).input_error("OpenFailure", "BadPath")?,
                    ));
                }
                match Connection::open_observed_with_diagnostic_limit(
                    path,
                    self.observations.clone(),
                    TYPE_WORK_LIMIT,
                ) {
                    Ok(owner) => Ok(ForeignAcquisition::Acquired(Box::new(ConnectionOwner(
                        RefCell::new(Some(owner)),
                    )))),
                    Err(error) => Ok(ForeignAcquisition::Refused(
                        Codec::new(module).report_error("OpenFailure", &error)?,
                    )),
                }
            }
            (1, 0) => {
                let fields = tuple(input, input.root())?;
                if fields.len() != 2 || states.len() != 1 {
                    return Err(ForeignExecutionError("SQLite prepare operand arity"));
                }
                let sql = string(input, fields[1])?;
                if sql.as_bytes().contains(&0) {
                    return Ok(ForeignAcquisition::Refused(
                        Codec::new(module).input_error("PrepareFailure", "BadSql")?,
                    ));
                }
                let mut owner = connection(states)?
                    .0
                    .try_borrow_mut()
                    .map_err(|_| ForeignExecutionError("SQLite connection already borrowed"))?;
                let result = owner
                    .as_mut()
                    .ok_or(ForeignExecutionError("SQLite connection already consumed"))?
                    .prepare(sql);
                match result {
                    Ok(Some(owner)) => Ok(ForeignAcquisition::Acquired(Box::new(StatementOwner(
                        RefCell::new(Some(owner)),
                    )))),
                    Ok(None) => {
                        let mut codec = Codec::new(module);
                        let root = codec.constructor("EmptySql", None)?;
                        Ok(ForeignAcquisition::Refused(codec.finish(root)?))
                    }
                    Err(error) => Ok(ForeignAcquisition::Refused(
                        Codec::new(module).report_error("PrepareFailure", &error)?,
                    )),
                }
            }
            _ => Err(ForeignExecutionError(
                "SQLite operation is not an acquisition",
            )),
        }
    }
    fn invoke(
        &self,
        key: ForeignOperationKey,
        module: &ForeignModuleFact,
        input: &ForeignData,
        states: &[&dyn NativeResourceOwner],
    ) -> Result<ForeignData, ForeignExecutionError> {
        if states.len() != 1 {
            return Err(ForeignExecutionError("SQLite borrowed operand count"));
        }
        if (key.effect, key.operation) == (0, 1) {
            let owner = connection(states)?
                .0
                .try_borrow()
                .map_err(|_| ForeignExecutionError("SQLite connection already borrowed"))?;
            let diagnostic = owner
                .as_ref()
                .ok_or(ForeignExecutionError("SQLite connection consumed"))?
                .diagnostic();
            let mut codec = Codec::new(module);
            let root = match diagnostic {
                Ok(diagnostic) => codec.error(&Error::Native(NativeError {
                    operation: "diagnostic",
                    code: diagnostic.code,
                    message: diagnostic.message,
                }))?,
                Err(error) => codec.error(&error)?,
            };
            return codec.finish(root);
        }
        if key.effect != 1 {
            return Err(ForeignExecutionError("SQLite borrowed effect mismatch"));
        }
        let mut slot = statement(states)?
            .0
            .try_borrow_mut()
            .map_err(|_| ForeignExecutionError("SQLite statement already borrowed"))?;
        let owner = slot
            .as_mut()
            .ok_or(ForeignExecutionError("SQLite statement consumed"))?;
        let mut codec = Codec::new(module);
        match key.operation {
            1 => {
                let fields = tuple(input, input.root())?;
                if fields.len() != 3 {
                    return Err(ForeignExecutionError("SQLite bind integer arity"));
                }
                let Some(index) = checked_index(input, fields[1], true)? else {
                    return codec.input_error("Err", "BadIndex");
                };
                let Some(value) = integer(input, fields[2])?.to_i64() else {
                    return codec.input_error("Err", "BadInteger");
                };
                match owner.bind_int64(index, value) {
                    Ok(()) => {
                        let value = codec.push(ForeignDataNode::Unit)?;
                        let root = codec.constructor("Ok", Some(value))?;
                        codec.finish(root)
                    }
                    Err(error) => codec.report_error("Err", &error),
                }
            }
            2 => match owner.step() {
                Ok(Step::Row) => {
                    let root = codec.constructor("Row", None)?;
                    codec.finish(root)
                }
                Ok(Step::Done) => {
                    let root = codec.constructor("Done", None)?;
                    codec.finish(root)
                }
                Err(error) => codec.report_statement_error("StepError", &error, owner.state()),
            },
            3 | 6 | 10 => {
                let fields = tuple(input, input.root())?;
                if fields.len() != 2 {
                    return Err(ForeignExecutionError("SQLite column arity"));
                }
                let Some(index) = checked_index(input, fields[1], false)? else {
                    return codec.input_error("Err", "BadColumn");
                };
                let expected = match key.operation {
                    3 => CopyColumnKind::Integer,
                    6 => CopyColumnKind::BlobOrNull,
                    10 => CopyColumnKind::TextOrNull,
                    _ => return Err(ForeignExecutionError("SQLite column operation mismatch")),
                };
                let value = match owner.column_copy_kind_bounded(index, expected, TYPE_WORK_LIMIT) {
                    Ok(Column::Integer(value)) if key.operation == 3 => codec.push(
                        ForeignDataNode::Integer(ash::integer::Integer::from_i64(value)),
                    )?,
                    Ok(Column::Blob(bytes)) if key.operation == 6 => {
                        let bytes = codec.bytes(&bytes)?;
                        codec.constructor("BlobBytes", Some(bytes))?
                    }
                    Ok(Column::Null) if key.operation == 6 => {
                        codec.constructor("NullBytes", None)?
                    }
                    Ok(Column::Text(text)) if key.operation == 10 => {
                        let text = codec.string(&text)?;
                        codec.constructor("TextValue", Some(text))?
                    }
                    Ok(Column::Null) if key.operation == 10 => {
                        codec.constructor("NullText", None)?
                    }
                    Ok(_) => return codec.report_error("Err", &Error::ColumnKind),
                    Err(error) => return codec.report_error("Err", &error),
                };
                let root = codec.constructor("Ok", Some(value))?;
                codec.finish(root)
            }
            5 | 9 => {
                let fields = tuple(input, input.root())?;
                if fields.len() != 3 {
                    return Err(ForeignExecutionError("SQLite bind copied data arity"));
                }
                let Some(index) = checked_index(input, fields[1], true)? else {
                    return codec.input_error("Err", "BadIndex");
                };
                let result = match node(input, fields[2])? {
                    ForeignDataNode::Constructor(id, None)
                        if key.operation == 5 && *id == constructor(module, "NullBytes")? =>
                    {
                        owner.bind_null(index)
                    }
                    ForeignDataNode::Constructor(id, Some(payload))
                        if key.operation == 5 && *id == constructor(module, "BlobBytes")? =>
                    {
                        owner.bind_blob_copy(index, bytes(input, *payload)?)
                    }
                    ForeignDataNode::Constructor(id, None)
                        if key.operation == 9 && *id == constructor(module, "NullText")? =>
                    {
                        owner.bind_null(index)
                    }
                    ForeignDataNode::Constructor(id, Some(payload))
                        if key.operation == 9 && *id == constructor(module, "TextValue")? =>
                    {
                        owner.bind_text_copy(index, string(input, *payload)?)
                    }
                    _ => {
                        return Err(ForeignExecutionError(
                            "SQLite copied-data-or-null codec mismatch",
                        ));
                    }
                };
                match result {
                    Ok(()) => {
                        let value = codec.push(ForeignDataNode::Unit)?;
                        let root = codec.constructor("Ok", Some(value))?;
                        codec.finish(root)
                    }
                    Err(error) => codec.report_error("Err", &error),
                }
            }
            7 | 8 => {
                let result = if key.operation == 7 {
                    owner.reset()
                } else {
                    owner.clear_bindings()
                };
                match result {
                    Ok(()) => {
                        let value = codec.push(ForeignDataNode::Unit)?;
                        let root = codec.constructor("Ok", Some(value))?;
                        codec.finish(root)
                    }
                    Err(error) => codec.report_error("Err", &error),
                }
            }
            _ => Err(ForeignExecutionError("SQLite operation is not borrowed")),
        }
    }
    fn finish(
        &self,
        key: ForeignOperationKey,
        module: &ForeignModuleFact,
        owner: &mut dyn NativeResourceOwner,
        context: ForeignFinishContext,
    ) -> Result<ForeignCompletion, ForeignExecutionError> {
        if context.retained_dependents {
            return Err(ForeignExecutionError(
                "retained native dependency prevents finish transition",
            ));
        }
        match (key.effect, key.operation) {
            (0, 2) => {
                let owner = owner
                    .as_any_mut()
                    .downcast_mut::<ConnectionOwner>()
                    .ok_or(ForeignExecutionError("SQLite finisher connection mismatch"))?;
                let slot = owner.0.get_mut();
                let connection = slot
                    .as_mut()
                    .ok_or(ForeignExecutionError("SQLite connection finish repeated"))?;
                self.observations
                    .0
                    .borrow_mut()
                    .try_reserve(if self.faults.retained_close { 2 } else { 1 })
                    .map_err(|_| ForeignExecutionError::STORAGE_REFUSED)?;
                self.observations
                    .push(Event::FinishDispatched { operation: "close" });
                if self.faults.retained_close {
                    self.observations.push(Event::FaultInjected {
                        operation: "sqlite3_close",
                        code: 5,
                    });
                    let data = injected_error("sqlite3_close", 5, "injected SQLite close refusal")
                        .and_then(|error| Codec::new(module).report_error("CloseFailure", &error));
                    return Ok(ForeignCompletion::RetainedError(data));
                }
                match connection.close() {
                    Ok(()) => {
                        drop(slot.take());
                        Ok(ForeignCompletion::Closed)
                    }
                    Err(error) => Ok(ForeignCompletion::RetainedError(
                        Codec::new(module).report_error("CloseFailure", &error),
                    )),
                }
            }
            (1, 4) => {
                let owner = owner
                    .as_any_mut()
                    .downcast_mut::<StatementOwner>()
                    .ok_or(ForeignExecutionError("SQLite finisher statement mismatch"))?;
                let slot = owner.0.get_mut();
                if slot.is_none() {
                    return Err(ForeignExecutionError("SQLite statement finish repeated"));
                }
                // Admit the dispatch observation before taking native ownership.
                // Fault mode also reserves its normal native call and injected event;
                // other observation growth retains the existing host allocation policy.
                self.observations
                    .0
                    .borrow_mut()
                    .try_reserve(if self.faults.consumed_finalize { 3 } else { 1 })
                    .map_err(|_| ForeignExecutionError::STORAGE_REFUSED)?;
                self.observations.push(Event::FinishDispatched {
                    operation: "finalize",
                });
                let statement = slot
                    .take()
                    .ok_or(ForeignExecutionError("SQLite statement finish repeated"))?;
                match statement.finalize() {
                    Ok(()) if self.faults.consumed_finalize => {
                        self.observations.push(Event::FaultInjected {
                            operation: "sqlite3_finalize",
                            code: 1,
                        });
                        let data = injected_error(
                            "sqlite3_finalize",
                            1,
                            "injected consumed SQLite finalize error",
                        )
                        .and_then(|error| {
                            Codec::new(module).report_error("FinalizeFailure", &error)
                        });
                        Ok(ForeignCompletion::ConsumedError(data))
                    }
                    Ok(()) => Ok(ForeignCompletion::Closed),
                    Err(error) => Ok(ForeignCompletion::ConsumedError(
                        Codec::new(module).report_error("FinalizeFailure", &error),
                    )),
                }
            }
            _ => Err(ForeignExecutionError("SQLite operation is not a finisher")),
        }
    }
}
