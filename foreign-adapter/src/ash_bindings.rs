//! Executable SQLite bindings outside compiler-specific dispatch.

use crate::{Column, Connection, Error, Event, NativeError, Observations, Statement, Step};
use ash::{
    foreign::{
        ForeignManifest, ForeignModuleFact,
        runtime::{
            ExecutableForeignModule, ForeignAcquisition, ForeignCompletion, ForeignData,
            ForeignDataNode, ForeignExecutionError, ForeignFinishContext, ForeignOperationKey,
            ForeignRuntimeBinding, NativeResourceOwner,
        },
        sqlite_manifest,
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
                .map_err(|_| ForeignExecutionError("SQLite integer codec work exhausted"))?
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
            .ok_or(ForeignExecutionError("SQLite codec work exhausted"))?;
        self.nodes
            .try_reserve(1)
            .map_err(|_| ForeignExecutionError("SQLite codec allocation failed"))?;
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
            .map_err(|_| ForeignExecutionError("SQLite tuple allocation failed"))?;
        children.extend_from_slice(fields);
        self.push(ForeignDataNode::Tuple(children.into_boxed_slice()))
    }
    fn bytes(&mut self, bytes: &[u8]) -> Result<usize, ForeignExecutionError> {
        if bytes.len() >= TYPE_WORK_LIMIT.saturating_sub(self.work) {
            return Err(ForeignExecutionError("SQLite byte copy work exhausted"));
        }

        let mut copied = Vec::new();
        copied
            .try_reserve_exact(bytes.len())
            .map_err(|_| ForeignExecutionError("SQLite byte copy allocation failed"))?;
        copied.extend_from_slice(bytes);
        self.push(ForeignDataNode::Bytes(Arc::from(copied)))
    }
    fn error(&mut self, error: &Error) -> Result<usize, ForeignExecutionError> {
        match error {
            Error::Native(native) => {
                let code = self.push(ForeignDataNode::Integer(ash::integer::Integer::from_i64(
                    i64::from(native.code),
                )))?;
                let message = self.bytes(native.message.as_bytes())?;
                let payload = self.tuple(&[code, message])?;
                self.constructor("NativeFailure", Some(payload))
            }
            Error::InvalidInput(_) | Error::ColumnKind => {
                let fault = self.constructor(
                    if matches!(error, Error::ColumnKind) {
                        "ColumnTypeMismatch"
                    } else {
                        "BadIndex"
                    },
                    None,
                )?;
                self.constructor("InputFailure", Some(fault))
            }
            Error::Protocol(_) => {
                let fault = self.constructor("ClosedOwner", None)?;
                self.constructor("ProtocolFailure", Some(fault))
            }
            _ => self.constructor("ConversionFailure", None),
        }
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
        .map_err(|_| ForeignExecutionError("SQLite injected error allocation failed"))?;
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
fn integer(input: &ForeignData, index: usize) -> Result<i64, ForeignExecutionError> {
    match node(input, index)? {
        ForeignDataNode::Integer(value) => value
            .to_i64()
            .ok_or(ForeignExecutionError("SQLite integer outside native range")),
        _ => Err(ForeignExecutionError("SQLite input expected integer")),
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
            || module.operations.len() != 12
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
            "ColumnTypeMismatch",
            "ClosedOwner",
            "NullBytes",
            "BlobBytes",
            "BadPath",
            "BadSql",
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
                        match std::str::from_utf8(bytes(input, *payload)?) {
                            Ok(path) => path,
                            Err(_) => {
                                return Ok(ForeignAcquisition::Refused(
                                    Codec::new(module).input_error("OpenFailure", "BadPath")?,
                                ));
                            }
                        }
                    }
                    _ => return Err(ForeignExecutionError("SQLite open configuration mismatch")),
                };
                if path.as_bytes().contains(&0) {
                    return Ok(ForeignAcquisition::Refused(
                        Codec::new(module).input_error("OpenFailure", "BadPath")?,
                    ));
                }
                match Connection::open_observed(path, self.observations.clone()) {
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
                let sql = match std::str::from_utf8(bytes(input, fields[1])?) {
                    Ok(sql) => sql,
                    Err(_) => {
                        return Ok(ForeignAcquisition::Refused(
                            Codec::new(module).input_error("PrepareFailure", "BadSql")?,
                        ));
                    }
                };
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
                .diagnostic()
                .map_err(|_| ForeignExecutionError("SQLite diagnostic state contract failed"))?;
            let error = Error::Native(crate::NativeError {
                operation: "diagnostic",
                code: diagnostic.code,
                message: diagnostic.message,
            });
            let mut codec = Codec::new(module);
            let root = codec.error(&error)?;
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
                let index = usize::try_from(integer(input, fields[1])?)
                    .map_err(|_| ForeignExecutionError("SQLite index outside ABI"))?;
                let value = integer(input, fields[2])?;
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
                Err(error) => codec.report_error("StepError", &error),
            },
            3 | 6 => {
                let fields = tuple(input, input.root())?;
                if fields.len() != 2 {
                    return Err(ForeignExecutionError("SQLite column arity"));
                }
                let index = usize::try_from(integer(input, fields[1])?)
                    .map_err(|_| ForeignExecutionError("SQLite column outside ABI"))?;
                let value = match owner.column_copy(index) {
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
                    Ok(_) => return codec.report_error("Err", &Error::ColumnKind),
                    Err(error) => return codec.report_error("Err", &error),
                };
                let root = codec.constructor("Ok", Some(value))?;
                codec.finish(root)
            }
            5 => {
                let fields = tuple(input, input.root())?;
                if fields.len() != 3 {
                    return Err(ForeignExecutionError("SQLite bind bytes arity"));
                }
                let index = usize::try_from(integer(input, fields[1])?)
                    .map_err(|_| ForeignExecutionError("SQLite index outside ABI"))?;
                let result = match node(input, fields[2])? {
                    ForeignDataNode::Constructor(id, None)
                        if *id == constructor(module, "NullBytes")? =>
                    {
                        owner.bind_null(index)
                    }
                    ForeignDataNode::Constructor(id, Some(payload))
                        if *id == constructor(module, "BlobBytes")? =>
                    {
                        owner.bind_blob_copy(index, bytes(input, *payload)?)
                    }
                    _ => return Err(ForeignExecutionError("SQLite bytes-or-null codec mismatch")),
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
                if self.faults.retained_close {
                    self.observations
                        .0
                        .borrow_mut()
                        .try_reserve(1)
                        .map_err(|_| {
                            ForeignExecutionError("SQLite fault observation allocation failed")
                        })?;
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
                if self.faults.consumed_finalize {
                    // One actual finalize call and one separate injected event.
                    self.observations
                        .0
                        .borrow_mut()
                        .try_reserve(2)
                        .map_err(|_| {
                            ForeignExecutionError("SQLite fault observation allocation failed")
                        })?;
                }
                let statement = owner
                    .0
                    .get_mut()
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
