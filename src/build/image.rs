//! Matching-compiler private Pure Core construction records.
//!
//! This initial carrier deliberately refuses unsupported metadata. It contains
//! flat indices and bytes, never parser trees, recursive Type serialization or
//! validated capabilities. Restoration builds unchecked Core and invokes the
//! existing modular validator. These records are not a stable file format.

use std::{collections::HashMap, fmt, sync::Arc};

use crate::{
    core::{
        CoreBuilder, CoreMatchArm, CorePattern, CorePatternKind, NodeId, Primitive,
        PureComputation, PureExprKind, PureValue, ValidatedProgram,
    },
    integer::Integer,
    module::ModuleId,
    resolved::{
        BinderId, ResolvedConstructor, ResolvedNominalDeclarationKind, ResolvedNominalType,
        ResolvedRegistry,
    },
    source::{ByteRange, GeneratedReason, Origin, SourceFile, SourceId, Span},
    types::{ConstructorId, IterativeTypeOwner, NominalTypeId, Type, TypeWorkBudget},
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Unsupported {
    RegistryMetadata,
    MethodEvidence,
    Type,
    Intrinsic,
    ErasedTypeOperation,
    LargeIntegerLiteral,
}

#[derive(Debug)]
pub(crate) enum ImageFailure {
    Unsupported(Unsupported),
    Resource,
    InvalidRecord,
    UnsupportedFormat,
    InvalidEncoding,
    SourceAdmission,
    RegistryAdmission,
    CoreAdmission(crate::core::BuildError),
    Validation(crate::core::ValidationError),
}

impl From<crate::core::BuildError> for ImageFailure {
    fn from(error: crate::core::BuildError) -> Self {
        Self::CoreAdmission(error)
    }
}

impl fmt::Display for ImageFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unsupported(feature) => {
                write!(formatter, "Pure image does not support {feature:?}")
            }
            Self::Resource => formatter.write_str("Pure image work or storage admission refused"),
            Self::InvalidRecord => formatter.write_str("Pure image record is inconsistent"),
            Self::UnsupportedFormat => {
                formatter.write_str("Pure image format does not match this compiler")
            }
            Self::InvalidEncoding => {
                formatter.write_str("Pure image encoding is malformed or has trailing bytes")
            }
            Self::SourceAdmission => formatter.write_str("Pure image source admission refused"),
            Self::RegistryAdmission => formatter.write_str("Pure image registry admission refused"),
            Self::CoreAdmission(error) => {
                write!(formatter, "Pure image Core admission refused: {error}")
            }
            Self::Validation(error) => write!(formatter, "Pure image validation refused: {error}"),
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct Slice {
    start: u32,
    len: u32,
}

impl Slice {
    fn of<T>(records: &[T], start: usize) -> Result<Self, ImageFailure> {
        Ok(Self {
            start: index(start)?,
            len: index(
                records
                    .len()
                    .checked_sub(start)
                    .ok_or(ImageFailure::InvalidRecord)?,
            )?,
        })
    }

    fn get<T>(self, records: &[T]) -> Result<&[T], ImageFailure> {
        let start = usize::try_from(self.start).map_err(|_| ImageFailure::InvalidRecord)?;
        let len = usize::try_from(self.len).map_err(|_| ImageFailure::InvalidRecord)?;
        records
            .get(start..start.checked_add(len).ok_or(ImageFailure::InvalidRecord)?)
            .ok_or(ImageFailure::InvalidRecord)
    }
}

#[derive(Clone, Copy, Debug)]
struct SourceRecord {
    path: Slice,
    text: Slice,
}

#[derive(Clone, Copy, Debug)]
struct SpanRecord {
    source: u32,
    start: u32,
    end: u32,
}

#[derive(Clone, Copy, Debug)]
enum OriginRecord {
    Source(SpanRecord),
    Generated { cause: u32, reason: GeneratedReason },
    Related { primary: u32, related: Slice },
}

#[derive(Clone, Copy, Debug)]
struct NominalId {
    module: u32,
    local: u32,
}

#[derive(Clone, Copy, Debug)]
struct ConstructorIdentity {
    owner: NominalId,
    local: u32,
}

#[derive(Clone, Copy, Debug)]
enum BinderIdentity {
    Resolved { module: u32, local: u32 },
    Generated(u32),
}

#[derive(Clone, Copy, Debug)]
enum TypeTag {
    Int,
    Bool,
    Unit,
    Bytes,
    String,
    Nominal(NominalId),
    Function,
    Tuple,
}

#[derive(Clone, Copy, Debug)]
struct TypeRecord {
    tag: TypeTag,
    children: Slice,
}

#[derive(Clone, Copy, Debug)]
struct BinderRecord {
    id: BinderIdentity,
    ty: u32,
    origin: u32,
}

#[derive(Clone, Copy, Debug)]
enum PatternTag {
    Wildcard,
    Bool(bool),
    Unit,
    Binder(u32),
    Tuple,
    Constructor(ConstructorIdentity),
}

#[derive(Clone, Copy, Debug)]
struct PatternRecord {
    tag: PatternTag,
    children: Slice,
    ty: u32,
    origin: u32,
}

#[derive(Clone, Copy, Debug)]
struct ArmRecord {
    pattern: u32,
    body: u32,
    origin: u32,
}

#[derive(Clone, Copy, Debug)]
struct RecursiveMemberRecord {
    binder: u32,
    initializer: u32,
}

#[derive(Clone, Copy, Debug)]
enum NodeTag {
    Integer(i64),
    Bool(bool),
    Unit,
    String(Slice),
    Constructor(ConstructorIdentity),
    Variable(BinderIdentity),
    Function {
        parameter: u32,
        body: u32,
    },
    Bind {
        binder: u32,
        initializer: u32,
        body: u32,
    },
    RecursiveBind {
        members: Slice,
        body: u32,
    },
    Apply {
        function: u32,
        argument: u32,
    },
    Primitive {
        operation: Primitive,
        left: u32,
        right: u32,
    },
    Tuple(Slice),
    Match {
        scrutinee: u32,
        arms: Slice,
    },
}

#[derive(Clone, Copy, Debug)]
struct NodeRecord {
    tag: NodeTag,
    ty: u32,
    origin: u32,
}

#[derive(Clone, Copy, Debug)]
struct NominalRecord {
    id: NominalId,
    spelling: Slice,
    constructors: Slice,
    origin: u32,
}

#[derive(Clone, Copy, Debug)]
struct ConstructorRecord {
    id: ConstructorIdentity,
    spelling: Slice,
    payload: Option<u32>,
    origin: u32,
}

#[derive(Debug, Default)]
pub(crate) struct PureImage {
    bytes: Vec<u8>,
    sources: Vec<SourceRecord>,
    spans: Vec<SpanRecord>,
    origins: Vec<OriginRecord>,
    types: Vec<TypeRecord>,
    type_children: Vec<u32>,
    binders: Vec<BinderRecord>,
    patterns: Vec<PatternRecord>,
    pattern_children: Vec<u32>,
    arms: Vec<ArmRecord>,
    recursive_members: Vec<RecursiveMemberRecord>,
    nodes: Vec<NodeRecord>,
    node_children: Vec<u32>,
    nominals: Vec<NominalRecord>,
    constructors: Vec<ConstructorRecord>,
    nominal_constructors: Vec<ConstructorIdentity>,
    root: u32,
}

fn index(value: usize) -> Result<u32, ImageFailure> {
    u32::try_from(value).map_err(|_| ImageFailure::Resource)
}

fn charge(work: &mut TypeWorkBudget, amount: usize) -> Result<(), ImageFailure> {
    work.charge(amount).map_err(|()| ImageFailure::Resource)
}

fn push<T>(
    records: &mut Vec<T>,
    record: T,
    work: &mut TypeWorkBudget,
) -> Result<u32, ImageFailure> {
    let slot = index(records.len())?;
    index(records.len().checked_add(1).ok_or(ImageFailure::Resource)?)?;
    charge(work, 1)?;
    records.try_reserve(1).map_err(|_| ImageFailure::Resource)?;
    records.push(record);
    Ok(slot)
}

fn append<T: Copy>(
    records: &mut Vec<T>,
    values: &[T],
    work: &mut TypeWorkBudget,
) -> Result<Slice, ImageFailure> {
    let start = records.len();
    index(
        start
            .checked_add(values.len())
            .ok_or(ImageFailure::Resource)?,
    )?;
    charge(work, values.len())?;
    records
        .try_reserve(values.len())
        .map_err(|_| ImageFailure::Resource)?;
    records.extend_from_slice(values);
    Slice::of(records, start)
}

fn get<T>(records: &[T], slot: u32) -> Result<&T, ImageFailure> {
    records
        .get(usize::try_from(slot).map_err(|_| ImageFailure::InvalidRecord)?)
        .ok_or(ImageFailure::InvalidRecord)
}

struct Encoder<'a> {
    image: PureImage,
    modules: HashMap<ModuleId, u32>,
    sources: HashMap<SourceId, u32>,
    binders: HashMap<BinderId, u32>,
    remapped: Vec<Option<u32>>,
    work: &'a mut TypeWorkBudget,
}

pub(crate) fn encode(
    program: &ValidatedProgram,
    provenance: &[(ModuleId, Arc<SourceFile>)],
    work: &mut TypeWorkBudget,
) -> Result<PureImage, ImageFailure> {
    if !program
        .registry()
        .monomorphic_image_subset(work)
        .map_err(|_| ImageFailure::RegistryAdmission)?
    {
        return Err(ImageFailure::Unsupported(Unsupported::RegistryMetadata));
    }
    let registry = program.registry();
    let catalog = program.method_evidence();
    if !catalog.lexical_owners().is_empty()
        || !catalog.methods().is_empty()
        || !catalog.implementation_owners().is_empty()
        || !catalog.domains().is_empty()
        || !catalog.occurrences().is_empty()
        || !catalog.final_occurrence_owners().is_empty()
        || !catalog.adapters().is_empty()
        || !catalog.concrete_sources().is_empty()
        || !catalog.expectations().is_empty()
        || !program.method_evidence_anchors().is_empty()
    {
        return Err(ImageFailure::Unsupported(Unsupported::MethodEvidence));
    }
    let mut encoder = Encoder {
        image: PureImage::default(),
        modules: HashMap::new(),
        sources: HashMap::new(),
        binders: HashMap::new(),
        remapped: Vec::new(),
        work,
    };
    charge(
        encoder.work,
        provenance
            .len()
            .checked_mul(2)
            .ok_or(ImageFailure::Resource)?,
    )?;
    encoder
        .modules
        .try_reserve(provenance.len())
        .map_err(|_| ImageFailure::Resource)?;
    encoder
        .sources
        .try_reserve(provenance.len())
        .map_err(|_| ImageFailure::Resource)?;
    for (module, source) in provenance {
        // This first slice never converts a builtin role into ordinary authority.
        if module.is_builtin_cell()
            || module.is_builtin_native_buffer()
            || module.is_builtin_bytes()
            || module.is_builtin_string()
            || module.is_builtin_foreign()
        {
            return Err(ImageFailure::Unsupported(Unsupported::RegistryMetadata));
        }
        let path = append(
            &mut encoder.image.bytes,
            source.display_path().as_bytes(),
            encoder.work,
        )?;
        let text = append(
            &mut encoder.image.bytes,
            source.text().as_bytes(),
            encoder.work,
        )?;
        let slot = push(
            &mut encoder.image.sources,
            SourceRecord { path, text },
            encoder.work,
        )?;
        if encoder.modules.insert(*module, slot).is_some()
            || encoder.sources.insert(source.id(), slot).is_some()
        {
            return Err(ImageFailure::InvalidRecord);
        }
    }
    if provenance.is_empty() {
        return Err(ImageFailure::InvalidRecord);
    }
    encoder.encode_registry(registry)?;
    charge(encoder.work, program.node_count())?;
    encoder
        .remapped
        .try_reserve_exact(program.node_count())
        .map_err(|_| ImageFailure::Resource)?;
    encoder.remapped.resize(program.node_count(), None);
    let mut pending = Vec::new();
    push(&mut pending, (program.root(), false), encoder.work)?;
    while let Some((id, finish)) = pending.pop() {
        charge(encoder.work, 1)?;
        if encoder.node(id).is_ok() {
            continue;
        }
        let expression = program.node(id).ok_or(ImageFailure::InvalidRecord)?;
        if finish {
            let ty = encoder.encode_type(&expression.ty)?;
            let origin = encoder.encode_origin(&expression.origin)?;
            let tag = encoder.encode_node(&expression.kind)?;
            let slot = push(
                &mut encoder.image.nodes,
                NodeRecord { tag, ty, origin },
                encoder.work,
            )?;
            *encoder
                .remapped
                .get_mut(usize::try_from(id.value()).map_err(|_| ImageFailure::InvalidRecord)?)
                .ok_or(ImageFailure::InvalidRecord)? = Some(slot);
        } else {
            push(&mut pending, (id, true), encoder.work)?;
            let count = expression.kind.child_count();
            charge(encoder.work, count)?;
            for child in (0..count).rev() {
                push(
                    &mut pending,
                    (
                        expression
                            .kind
                            .child_at(child)
                            .ok_or(ImageFailure::InvalidRecord)?,
                        false,
                    ),
                    encoder.work,
                )?;
            }
        }
    }
    if encoder.image.nodes.len() != program.node_count() {
        return Err(ImageFailure::InvalidRecord);
    }
    encoder.image.root = encoder.node(program.root())?;
    Ok(encoder.image)
}

impl Encoder<'_> {
    fn module(&mut self, module: ModuleId) -> Result<u32, ImageFailure> {
        charge(self.work, 1)?;
        self.modules
            .get(&module)
            .copied()
            .ok_or(ImageFailure::InvalidRecord)
    }

    fn nominal(&mut self, nominal: NominalTypeId) -> Result<NominalId, ImageFailure> {
        if nominal.is_lexical() {
            return Err(ImageFailure::Unsupported(Unsupported::RegistryMetadata));
        }
        Ok(NominalId {
            module: self.module(nominal.module())?,
            local: nominal.declaration(),
        })
    }

    fn constructor(
        &mut self,
        constructor: ConstructorId,
    ) -> Result<ConstructorIdentity, ImageFailure> {
        Ok(ConstructorIdentity {
            owner: self.nominal(constructor.owner())?,
            local: constructor.constructor(),
        })
    }

    fn binder_id(&mut self, binder: BinderId) -> Result<BinderIdentity, ImageFailure> {
        Ok(match binder {
            BinderId::Resolved { module, local } => BinderIdentity::Resolved {
                module: self.module(module)?,
                local,
            },
            BinderId::Generated(local) => BinderIdentity::Generated(local),
        })
    }

    fn node(&self, node: NodeId) -> Result<u32, ImageFailure> {
        self.remapped
            .get(usize::try_from(node.value()).map_err(|_| ImageFailure::InvalidRecord)?)
            .copied()
            .flatten()
            .ok_or(ImageFailure::InvalidRecord)
    }

    fn span(&mut self, span: Span) -> Result<SpanRecord, ImageFailure> {
        charge(self.work, 1)?;
        Ok(SpanRecord {
            source: *self
                .sources
                .get(&span.source())
                .ok_or(ImageFailure::InvalidRecord)?,
            start: span.range().start(),
            end: span.range().end(),
        })
    }

    fn encode_origin(&mut self, origin: &Origin) -> Result<u32, ImageFailure> {
        let mut frames = Vec::new();
        let mut current = origin;
        let mut depth = 0;
        let mut result = loop {
            charge(self.work, 1)?;
            if depth > crate::core::CORE_PAYLOAD_DEPTH_LIMIT {
                return Err(ImageFailure::Resource);
            }
            match current {
                Origin::Source(span) => {
                    let span = self.span(*span)?;
                    break push(
                        &mut self.image.origins,
                        OriginRecord::Source(span),
                        self.work,
                    )?;
                }
                Origin::Generated { cause, reason } => {
                    push(&mut frames, (Some(*reason), None), self.work)?;
                    current = cause;
                }
                Origin::Related { primary, related } => {
                    push(&mut frames, (None, Some(related.as_slice())), self.work)?;
                    current = primary;
                }
            }
            depth += 1;
        };
        while let Some((reason, related)) = frames.pop() {
            let record = if let Some(reason) = reason {
                OriginRecord::Generated {
                    cause: result,
                    reason,
                }
            } else {
                let start = self.image.spans.len();
                for span in related.ok_or(ImageFailure::InvalidRecord)? {
                    let span = self.span(*span)?;
                    push(&mut self.image.spans, span, self.work)?;
                }
                OriginRecord::Related {
                    primary: result,
                    related: Slice::of(&self.image.spans, start)?,
                }
            };
            result = push(&mut self.image.origins, record, self.work)?;
        }
        Ok(result)
    }

    fn encode_type(&mut self, ty: &Type) -> Result<u32, ImageFailure> {
        enum Task<'a> {
            Visit(&'a Type, usize),
            Finish(TypeTag, usize),
        }
        let mut tasks = Vec::new();
        let mut results = Vec::new();
        push(&mut tasks, Task::Visit(ty, 0), self.work)?;
        while let Some(task) = tasks.pop() {
            charge(self.work, 1)?;
            match task {
                Task::Visit(ty, depth) => {
                    if depth > crate::core::CORE_PAYLOAD_DEPTH_LIMIT {
                        return Err(ImageFailure::Resource);
                    }
                    let (tag, count) = match ty {
                        Type::Int => (TypeTag::Int, 0),
                        Type::Bool => (TypeTag::Bool, 0),
                        Type::Unit => (TypeTag::Unit, 0),
                        Type::Bytes => (TypeTag::Bytes, 0),
                        Type::String => (TypeTag::String, 0),
                        Type::Nominal(id) => (TypeTag::Nominal(self.nominal(*id)?), 0),
                        Type::Function(_, _) => (TypeTag::Function, 2),
                        Type::Tuple(elements) => (TypeTag::Tuple, elements.len()),
                        _ => return Err(ImageFailure::Unsupported(Unsupported::Type)),
                    };
                    push(&mut tasks, Task::Finish(tag, count), self.work)?;
                    match ty {
                        Type::Function(domain, result) => {
                            push(&mut tasks, Task::Visit(result, depth + 1), self.work)?;
                            push(&mut tasks, Task::Visit(domain, depth + 1), self.work)?;
                        }
                        Type::Tuple(elements) => {
                            for element in elements.iter().rev() {
                                push(&mut tasks, Task::Visit(element, depth + 1), self.work)?;
                            }
                        }
                        _ => {}
                    }
                }
                Task::Finish(tag, count) => {
                    let start = results
                        .len()
                        .checked_sub(count)
                        .ok_or(ImageFailure::InvalidRecord)?;
                    let children =
                        append(&mut self.image.type_children, &results[start..], self.work)?;
                    results.truncate(start);
                    let result = push(
                        &mut self.image.types,
                        TypeRecord { tag, children },
                        self.work,
                    )?;
                    push(&mut results, result, self.work)?;
                }
            }
        }
        results
            .pop()
            .filter(|_| results.is_empty())
            .ok_or(ImageFailure::InvalidRecord)
    }

    fn encode_binder(&mut self, binder: &crate::core::TypedBinder) -> Result<u32, ImageFailure> {
        charge(self.work, 1)?;
        if let Some(slot) = self.binders.get(&binder.id()) {
            return Ok(*slot);
        }
        let id = self.binder_id(binder.id())?;
        let ty = self.encode_type(binder.ty())?;
        let origin = self.encode_origin(binder.origin())?;
        charge(self.work, 1)?;
        self.binders
            .try_reserve(1)
            .map_err(|_| ImageFailure::Resource)?;
        let slot = push(
            &mut self.image.binders,
            BinderRecord { id, ty, origin },
            self.work,
        )?;
        self.binders.insert(binder.id(), slot);
        Ok(slot)
    }

    fn encode_registry(&mut self, registry: &ResolvedRegistry) -> Result<(), ImageFailure> {
        for nominal in registry.nominals() {
            charge(self.work, 1)?;
            if nominal.declaration_kind != ResolvedNominalDeclarationKind::Data
                || nominal.representation.is_some()
                || nominal.representation_provenance.is_some()
            {
                return Err(ImageFailure::Unsupported(Unsupported::RegistryMetadata));
            }
            let id = self.nominal(nominal.id)?;
            let spelling = append(
                &mut self.image.bytes,
                nominal.spelling.as_bytes(),
                self.work,
            )?;
            let origin = self.encode_origin(&nominal.origin)?;
            let start = self.image.nominal_constructors.len();
            for constructor in &nominal.constructors {
                let constructor = self.constructor(*constructor)?;
                push(&mut self.image.nominal_constructors, constructor, self.work)?;
            }
            let constructors = Slice::of(&self.image.nominal_constructors, start)?;
            push(
                &mut self.image.nominals,
                NominalRecord {
                    id,
                    spelling,
                    constructors,
                    origin,
                },
                self.work,
            )?;
        }
        for constructor in registry.constructors() {
            charge(self.work, 1)?;
            let id = self.constructor(constructor.id)?;
            if constructor.owner != constructor.id.owner() {
                return Err(ImageFailure::InvalidRecord);
            }
            let spelling = append(
                &mut self.image.bytes,
                constructor.spelling.as_bytes(),
                self.work,
            )?;
            let payload = constructor
                .payload
                .as_ref()
                .map(|ty| self.encode_type(ty))
                .transpose()?;
            let origin = self.encode_origin(&constructor.origin)?;
            push(
                &mut self.image.constructors,
                ConstructorRecord {
                    id,
                    spelling,
                    payload,
                    origin,
                },
                self.work,
            )?;
        }
        Ok(())
    }

    fn encode_pattern(&mut self, pattern: &CorePattern) -> Result<u32, ImageFailure> {
        enum Task<'a> {
            Visit(&'a CorePattern, usize),
            Finish(&'a CorePattern, PatternTag, usize),
        }
        let mut tasks = Vec::new();
        let mut results = Vec::new();
        push(&mut tasks, Task::Visit(pattern, 0), self.work)?;
        while let Some(task) = tasks.pop() {
            charge(self.work, 1)?;
            match task {
                Task::Visit(pattern, depth) => {
                    if depth > crate::core::CORE_PATTERN_DEPTH_LIMIT {
                        return Err(ImageFailure::Resource);
                    }
                    let (tag, count) = match &pattern.kind {
                        CorePatternKind::Wildcard => (PatternTag::Wildcard, 0),
                        CorePatternKind::Boolean(value) => (PatternTag::Bool(*value), 0),
                        CorePatternKind::Unit => (PatternTag::Unit, 0),
                        CorePatternKind::Binder(binder) => {
                            (PatternTag::Binder(self.encode_binder(binder)?), 0)
                        }
                        CorePatternKind::Tuple(elements) => (PatternTag::Tuple, elements.len()),
                        CorePatternKind::Constructor {
                            constructor,
                            payload,
                        } => (
                            PatternTag::Constructor(self.constructor(*constructor)?),
                            usize::from(payload.is_some()),
                        ),
                    };
                    push(&mut tasks, Task::Finish(pattern, tag, count), self.work)?;
                    match &pattern.kind {
                        CorePatternKind::Tuple(elements) => {
                            for element in elements.iter().rev() {
                                push(&mut tasks, Task::Visit(element, depth + 1), self.work)?;
                            }
                        }
                        CorePatternKind::Constructor {
                            payload: Some(payload),
                            ..
                        } => {
                            push(&mut tasks, Task::Visit(payload, depth + 1), self.work)?;
                        }
                        _ => {}
                    }
                }
                Task::Finish(pattern, tag, count) => {
                    let start = results
                        .len()
                        .checked_sub(count)
                        .ok_or(ImageFailure::InvalidRecord)?;
                    let children = append(
                        &mut self.image.pattern_children,
                        &results[start..],
                        self.work,
                    )?;
                    results.truncate(start);
                    let ty = self.encode_type(&pattern.ty)?;
                    let origin = self.encode_origin(&pattern.origin)?;
                    let result = push(
                        &mut self.image.patterns,
                        PatternRecord {
                            tag,
                            children,
                            ty,
                            origin,
                        },
                        self.work,
                    )?;
                    push(&mut results, result, self.work)?;
                }
            }
        }
        results
            .pop()
            .filter(|_| results.is_empty())
            .ok_or(ImageFailure::InvalidRecord)
    }

    fn encode_node(&mut self, kind: &PureExprKind) -> Result<NodeTag, ImageFailure> {
        Ok(match kind {
            PureExprKind::Value(value) => match value {
                PureValue::Integer(value) => NodeTag::Integer(
                    value
                        .value()
                        .to_i64()
                        .ok_or(ImageFailure::Unsupported(Unsupported::LargeIntegerLiteral))?,
                ),
                PureValue::Boolean(value) => NodeTag::Bool(value.value()),
                PureValue::Unit(_) => NodeTag::Unit,
                PureValue::String(value) => {
                    NodeTag::String(append(&mut self.image.bytes, value.bytes(), self.work)?)
                }
                PureValue::Constructor(value) => {
                    NodeTag::Constructor(self.constructor(value.constructor())?)
                }
                PureValue::Function(function) => NodeTag::Function {
                    parameter: self.encode_binder(function.parameter())?,
                    body: self.node(function.body())?,
                },
                PureValue::Intrinsic(_) => {
                    return Err(ImageFailure::Unsupported(Unsupported::Intrinsic));
                }
            },
            PureExprKind::Variable(variable) => {
                NodeTag::Variable(self.binder_id(variable.binder())?)
            }
            PureExprKind::Computation(computation) => match computation {
                PureComputation::Bind(binding) => NodeTag::Bind {
                    binder: self.encode_binder(binding.binder())?,
                    initializer: self.node(binding.initializer())?,
                    body: self.node(binding.body())?,
                },
                PureComputation::Apply(application) => NodeTag::Apply {
                    function: self.node(application.function())?,
                    argument: self.node(application.argument())?,
                },
                PureComputation::Primitive(operation) => NodeTag::Primitive {
                    operation: operation.primitive(),
                    left: self.node(operation.left())?,
                    right: self.node(operation.right())?,
                },
                PureComputation::Tuple(tuple) => {
                    let start = self.image.node_children.len();
                    for child in tuple.elements() {
                        let child = self.node(*child)?;
                        push(&mut self.image.node_children, child, self.work)?;
                    }
                    NodeTag::Tuple(Slice::of(&self.image.node_children, start)?)
                }
                PureComputation::Match(expression) => {
                    let start = self.image.arms.len();
                    for arm in expression.arms() {
                        let pattern = self.encode_pattern(arm.pattern())?;
                        let body = self.node(arm.body())?;
                        let origin = self.encode_origin(arm.origin())?;
                        push(
                            &mut self.image.arms,
                            ArmRecord {
                                pattern,
                                body,
                                origin,
                            },
                            self.work,
                        )?;
                    }
                    NodeTag::Match {
                        scrutinee: self.node(expression.scrutinee())?,
                        arms: Slice::of(&self.image.arms, start)?,
                    }
                }
                PureComputation::RecursiveBind(group) => {
                    let start = self.image.recursive_members.len();
                    for member in group.members() {
                        let binder = self.encode_binder(member.binder())?;
                        let initializer = self.node(member.initializer())?;
                        push(
                            &mut self.image.recursive_members,
                            RecursiveMemberRecord {
                                binder,
                                initializer,
                            },
                            self.work,
                        )?;
                    }
                    NodeTag::RecursiveBind {
                        members: Slice::of(&self.image.recursive_members, start)?,
                        body: self.node(group.body())?,
                    }
                }
                PureComputation::NewtypeConversion(_)
                | PureComputation::LocalNominalScope(_)
                | PureComputation::TypeAbstraction(_)
                | PureComputation::TypeApplication(_) => {
                    return Err(ImageFailure::Unsupported(Unsupported::ErasedTypeOperation));
                }
            },
        })
    }
}

struct OriginOwner(Option<Origin>);

impl OriginOwner {
    fn take(mut self) -> Origin {
        self.0.take().expect("owned origin is live")
    }
}

impl Drop for OriginOwner {
    fn drop(&mut self) {
        if let Some(origin) = self.0.take() {
            crate::source::discard_origin_iteratively(origin);
        }
    }
}

struct PatternOwner(Option<CorePattern>);

impl PatternOwner {
    fn take(mut self) -> CorePattern {
        self.0.take().expect("owned pattern is live")
    }
}

impl Drop for PatternOwner {
    fn drop(&mut self) {
        if let Some(pattern) = self.0.take() {
            pattern.discard_iteratively();
        }
    }
}

struct NominalBuffer(Vec<ResolvedNominalType>);

impl NominalBuffer {
    fn into_vec(mut self) -> Vec<ResolvedNominalType> {
        std::mem::take(&mut self.0)
    }
}

impl Drop for NominalBuffer {
    fn drop(&mut self) {
        for nominal in self.0.drain(..) {
            if let Some(ty) = nominal.representation {
                crate::types::discard_type_iteratively(ty);
            }
            crate::source::discard_origin_iteratively(nominal.origin);
        }
    }
}

struct ConstructorBuffer(Vec<ResolvedConstructor>);

impl ConstructorBuffer {
    fn into_vec(mut self) -> Vec<ResolvedConstructor> {
        std::mem::take(&mut self.0)
    }
}

impl Drop for ConstructorBuffer {
    fn drop(&mut self) {
        for constructor in self.0.drain(..) {
            constructor.discard_iteratively();
        }
    }
}

struct Decoder<'a> {
    image: &'a PureImage,
    sources: Vec<SourceFile>,
    modules: Vec<ModuleId>,
    work: &'a mut TypeWorkBudget,
}

// A private layout marker for the matching compiler/runtime only. Neither the
// embedded byte sequence nor its numeric tags promise compatibility.
const PRIVATE_MAGIC: &[u8] = b"ash-private-pure\x02";

struct WireWriter<'a> {
    bytes: Vec<u8>,
    work: &'a mut TypeWorkBudget,
}

impl WireWriter<'_> {
    fn bytes(&mut self, bytes: &[u8]) -> Result<(), ImageFailure> {
        append(&mut self.bytes, bytes, self.work)?;
        Ok(())
    }

    fn table<T: Wire>(&mut self, records: &[T]) -> Result<(), ImageFailure> {
        index(records.len())?.write(self)?;
        for record in records {
            record.write(self)?;
        }
        Ok(())
    }
}

struct WireReader<'a> {
    bytes: &'a [u8],
    offset: usize,
    work: &'a mut TypeWorkBudget,
}

impl WireReader<'_> {
    fn bytes(&mut self, count: usize) -> Result<&[u8], ImageFailure> {
        charge(self.work, count)?;
        let end = self
            .offset
            .checked_add(count)
            .ok_or(ImageFailure::InvalidEncoding)?;
        let bytes = self
            .bytes
            .get(self.offset..end)
            .ok_or(ImageFailure::InvalidEncoding)?;
        self.offset = end;
        Ok(bytes)
    }

    fn array<const N: usize>(&mut self) -> Result<[u8; N], ImageFailure> {
        let mut result = [0; N];
        result.copy_from_slice(self.bytes(N)?);
        Ok(result)
    }

    fn count<T: Wire>(&mut self) -> Result<usize, ImageFailure> {
        let count = usize::try_from(u32::read(self)?).map_err(|_| ImageFailure::InvalidEncoding)?;
        let minimum = count
            .checked_mul(T::MINIMUM)
            .ok_or(ImageFailure::InvalidEncoding)?;
        if minimum > self.bytes.len().saturating_sub(self.offset) {
            return Err(ImageFailure::InvalidEncoding);
        }
        Ok(count)
    }

    fn table<T: Wire>(&mut self) -> Result<Vec<T>, ImageFailure> {
        let count = self.count::<T>()?;
        charge(self.work, count)?;
        let mut records = Vec::new();
        records
            .try_reserve_exact(count)
            .map_err(|_| ImageFailure::Resource)?;
        for _ in 0..count {
            records.push(T::read(self)?);
        }
        Ok(records)
    }

    fn byte_table(&mut self) -> Result<Vec<u8>, ImageFailure> {
        let count = self.count::<u8>()?;
        charge(self.work, count)?;
        let mut bytes = Vec::new();
        bytes
            .try_reserve_exact(count)
            .map_err(|_| ImageFailure::Resource)?;
        bytes.extend_from_slice(self.bytes(count)?);
        Ok(bytes)
    }
}

trait Wire: Sized {
    const MINIMUM: usize;
    fn write(&self, writer: &mut WireWriter<'_>) -> Result<(), ImageFailure>;
    fn read(reader: &mut WireReader<'_>) -> Result<Self, ImageFailure>;
}

impl Wire for u8 {
    const MINIMUM: usize = 1;
    fn write(&self, writer: &mut WireWriter<'_>) -> Result<(), ImageFailure> {
        writer.bytes(&[*self])
    }
    fn read(reader: &mut WireReader<'_>) -> Result<Self, ImageFailure> {
        Ok(reader.array::<1>()?[0])
    }
}

impl Wire for u32 {
    const MINIMUM: usize = 4;
    fn write(&self, writer: &mut WireWriter<'_>) -> Result<(), ImageFailure> {
        writer.bytes(&self.to_le_bytes())
    }
    fn read(reader: &mut WireReader<'_>) -> Result<Self, ImageFailure> {
        Ok(Self::from_le_bytes(reader.array()?))
    }
}

impl Wire for i64 {
    const MINIMUM: usize = 8;
    fn write(&self, writer: &mut WireWriter<'_>) -> Result<(), ImageFailure> {
        writer.bytes(&self.to_le_bytes())
    }
    fn read(reader: &mut WireReader<'_>) -> Result<Self, ImageFailure> {
        Ok(Self::from_le_bytes(reader.array()?))
    }
}

impl Wire for bool {
    const MINIMUM: usize = 1;
    fn write(&self, writer: &mut WireWriter<'_>) -> Result<(), ImageFailure> {
        u8::from(*self).write(writer)
    }
    fn read(reader: &mut WireReader<'_>) -> Result<Self, ImageFailure> {
        match u8::read(reader)? {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err(ImageFailure::InvalidEncoding),
        }
    }
}

impl<T: Wire> Wire for Option<T> {
    const MINIMUM: usize = 1;
    fn write(&self, writer: &mut WireWriter<'_>) -> Result<(), ImageFailure> {
        match self {
            None => 0u8.write(writer),
            Some(value) => {
                1u8.write(writer)?;
                value.write(writer)
            }
        }
    }
    fn read(reader: &mut WireReader<'_>) -> Result<Self, ImageFailure> {
        match u8::read(reader)? {
            0 => Ok(None),
            1 => Ok(Some(T::read(reader)?)),
            _ => Err(ImageFailure::InvalidEncoding),
        }
    }
}

macro_rules! wire_struct {
    ($name:ident, $minimum:expr, $($field:ident),+ $(,)?) => {
        impl Wire for $name {
            const MINIMUM: usize = $minimum;
            fn write(&self, writer: &mut WireWriter<'_>) -> Result<(), ImageFailure> {
                $(self.$field.write(writer)?;)+
                Ok(())
            }
            fn read(reader: &mut WireReader<'_>) -> Result<Self, ImageFailure> {
                Ok(Self { $($field: Wire::read(reader)?,)+ })
            }
        }
    };
}

wire_struct!(Slice, 8, start, len);
wire_struct!(SourceRecord, 16, path, text);
wire_struct!(SpanRecord, 12, source, start, end);
wire_struct!(NominalId, 8, module, local);
wire_struct!(ConstructorIdentity, 12, owner, local);
wire_struct!(TypeRecord, 9, tag, children);
wire_struct!(BinderRecord, 13, id, ty, origin);
wire_struct!(PatternRecord, 17, tag, children, ty, origin);
wire_struct!(ArmRecord, 12, pattern, body, origin);
wire_struct!(RecursiveMemberRecord, 8, binder, initializer);
wire_struct!(NodeRecord, 9, tag, ty, origin);
wire_struct!(NominalRecord, 28, id, spelling, constructors, origin);
wire_struct!(ConstructorRecord, 25, id, spelling, payload, origin);

impl Wire for GeneratedReason {
    const MINIMUM: usize = 1;
    fn write(&self, writer: &mut WireWriter<'_>) -> Result<(), ImageFailure> {
        let tag = match self {
            Self::FunctionLowering => 0u8,
            Self::BindingLowering => 1,
            Self::RecursiveBindingLowering => 2,
            Self::TypeChecking => 3,
            Self::ConstantFolding => 4,
        };
        tag.write(writer)
    }
    fn read(reader: &mut WireReader<'_>) -> Result<Self, ImageFailure> {
        Ok(match u8::read(reader)? {
            0 => Self::FunctionLowering,
            1 => Self::BindingLowering,
            2 => Self::RecursiveBindingLowering,
            3 => Self::TypeChecking,
            4 => Self::ConstantFolding,
            _ => return Err(ImageFailure::InvalidEncoding),
        })
    }
}

impl Wire for Primitive {
    const MINIMUM: usize = 1;
    fn write(&self, writer: &mut WireWriter<'_>) -> Result<(), ImageFailure> {
        let tag = match self {
            Self::Add => 0u8,
            Self::Multiply => 1,
            Self::Equal => 2,
        };
        tag.write(writer)
    }
    fn read(reader: &mut WireReader<'_>) -> Result<Self, ImageFailure> {
        Ok(match u8::read(reader)? {
            0 => Self::Add,
            1 => Self::Multiply,
            2 => Self::Equal,
            _ => return Err(ImageFailure::InvalidEncoding),
        })
    }
}

impl Wire for OriginRecord {
    const MINIMUM: usize = 6;
    fn write(&self, writer: &mut WireWriter<'_>) -> Result<(), ImageFailure> {
        match self {
            Self::Source(span) => {
                0u8.write(writer)?;
                span.write(writer)
            }
            Self::Generated { cause, reason } => {
                1u8.write(writer)?;
                cause.write(writer)?;
                reason.write(writer)
            }
            Self::Related { primary, related } => {
                2u8.write(writer)?;
                primary.write(writer)?;
                related.write(writer)
            }
        }
    }
    fn read(reader: &mut WireReader<'_>) -> Result<Self, ImageFailure> {
        Ok(match u8::read(reader)? {
            0 => Self::Source(Wire::read(reader)?),
            1 => Self::Generated {
                cause: Wire::read(reader)?,
                reason: Wire::read(reader)?,
            },
            2 => Self::Related {
                primary: Wire::read(reader)?,
                related: Wire::read(reader)?,
            },
            _ => return Err(ImageFailure::InvalidEncoding),
        })
    }
}

impl Wire for BinderIdentity {
    const MINIMUM: usize = 5;
    fn write(&self, writer: &mut WireWriter<'_>) -> Result<(), ImageFailure> {
        match self {
            Self::Generated(local) => {
                0u8.write(writer)?;
                local.write(writer)
            }
            Self::Resolved { module, local } => {
                1u8.write(writer)?;
                module.write(writer)?;
                local.write(writer)
            }
        }
    }
    fn read(reader: &mut WireReader<'_>) -> Result<Self, ImageFailure> {
        Ok(match u8::read(reader)? {
            0 => Self::Generated(Wire::read(reader)?),
            1 => Self::Resolved {
                module: Wire::read(reader)?,
                local: Wire::read(reader)?,
            },
            _ => return Err(ImageFailure::InvalidEncoding),
        })
    }
}

impl Wire for TypeTag {
    const MINIMUM: usize = 1;
    fn write(&self, writer: &mut WireWriter<'_>) -> Result<(), ImageFailure> {
        let tag = match self {
            Self::Int => 0u8,
            Self::Bool => 1,
            Self::Unit => 2,
            Self::Bytes => 3,
            Self::String => 4,
            Self::Nominal(_) => 5,
            Self::Function => 6,
            Self::Tuple => 7,
        };
        tag.write(writer)?;
        if let Self::Nominal(id) = self {
            id.write(writer)?;
        }
        Ok(())
    }
    fn read(reader: &mut WireReader<'_>) -> Result<Self, ImageFailure> {
        Ok(match u8::read(reader)? {
            0 => Self::Int,
            1 => Self::Bool,
            2 => Self::Unit,
            3 => Self::Bytes,
            4 => Self::String,
            5 => Self::Nominal(Wire::read(reader)?),
            6 => Self::Function,
            7 => Self::Tuple,
            _ => return Err(ImageFailure::InvalidEncoding),
        })
    }
}

impl Wire for PatternTag {
    const MINIMUM: usize = 1;
    fn write(&self, writer: &mut WireWriter<'_>) -> Result<(), ImageFailure> {
        match self {
            Self::Wildcard => 0u8.write(writer),
            Self::Unit => 1u8.write(writer),
            Self::Bool(value) => {
                2u8.write(writer)?;
                value.write(writer)
            }
            Self::Binder(slot) => {
                3u8.write(writer)?;
                slot.write(writer)
            }
            Self::Tuple => 4u8.write(writer),
            Self::Constructor(id) => {
                5u8.write(writer)?;
                id.write(writer)
            }
        }
    }
    fn read(reader: &mut WireReader<'_>) -> Result<Self, ImageFailure> {
        Ok(match u8::read(reader)? {
            0 => Self::Wildcard,
            1 => Self::Unit,
            2 => Self::Bool(Wire::read(reader)?),
            3 => Self::Binder(Wire::read(reader)?),
            4 => Self::Tuple,
            5 => Self::Constructor(Wire::read(reader)?),
            _ => return Err(ImageFailure::InvalidEncoding),
        })
    }
}

impl Wire for NodeTag {
    const MINIMUM: usize = 1;
    fn write(&self, writer: &mut WireWriter<'_>) -> Result<(), ImageFailure> {
        match self {
            Self::Unit => 0u8.write(writer),
            Self::Integer(value) => {
                1u8.write(writer)?;
                value.write(writer)
            }
            Self::Bool(value) => {
                2u8.write(writer)?;
                value.write(writer)
            }
            Self::String(range) => {
                3u8.write(writer)?;
                range.write(writer)
            }
            Self::Constructor(id) => {
                4u8.write(writer)?;
                id.write(writer)
            }
            Self::Variable(id) => {
                5u8.write(writer)?;
                id.write(writer)
            }
            Self::Function { parameter, body } => {
                6u8.write(writer)?;
                parameter.write(writer)?;
                body.write(writer)
            }
            Self::Bind {
                binder,
                initializer,
                body,
            } => {
                7u8.write(writer)?;
                binder.write(writer)?;
                initializer.write(writer)?;
                body.write(writer)
            }
            Self::Apply { function, argument } => {
                8u8.write(writer)?;
                function.write(writer)?;
                argument.write(writer)
            }
            Self::Primitive {
                operation,
                left,
                right,
            } => {
                9u8.write(writer)?;
                operation.write(writer)?;
                left.write(writer)?;
                right.write(writer)
            }
            Self::Tuple(range) => {
                10u8.write(writer)?;
                range.write(writer)
            }
            Self::Match { scrutinee, arms } => {
                11u8.write(writer)?;
                scrutinee.write(writer)?;
                arms.write(writer)
            }
            Self::RecursiveBind { members, body } => {
                12u8.write(writer)?;
                members.write(writer)?;
                body.write(writer)
            }
        }
    }
    fn read(reader: &mut WireReader<'_>) -> Result<Self, ImageFailure> {
        Ok(match u8::read(reader)? {
            0 => Self::Unit,
            1 => Self::Integer(Wire::read(reader)?),
            2 => Self::Bool(Wire::read(reader)?),
            3 => Self::String(Wire::read(reader)?),
            4 => Self::Constructor(Wire::read(reader)?),
            5 => Self::Variable(Wire::read(reader)?),
            6 => Self::Function {
                parameter: Wire::read(reader)?,
                body: Wire::read(reader)?,
            },
            7 => Self::Bind {
                binder: Wire::read(reader)?,
                initializer: Wire::read(reader)?,
                body: Wire::read(reader)?,
            },
            8 => Self::Apply {
                function: Wire::read(reader)?,
                argument: Wire::read(reader)?,
            },
            9 => Self::Primitive {
                operation: Wire::read(reader)?,
                left: Wire::read(reader)?,
                right: Wire::read(reader)?,
            },
            10 => Self::Tuple(Wire::read(reader)?),
            11 => Self::Match {
                scrutinee: Wire::read(reader)?,
                arms: Wire::read(reader)?,
            },
            12 => Self::RecursiveBind {
                members: Wire::read(reader)?,
                body: Wire::read(reader)?,
            },
            _ => return Err(ImageFailure::InvalidEncoding),
        })
    }
}

impl PureImage {
    pub(crate) fn encode_bytes(&self, work: &mut TypeWorkBudget) -> Result<Vec<u8>, ImageFailure> {
        let mut writer = WireWriter {
            bytes: Vec::new(),
            work,
        };
        writer.bytes(PRIVATE_MAGIC)?;
        index(self.bytes.len())?.write(&mut writer)?;
        writer.bytes(&self.bytes)?;
        writer.table(&self.sources)?;
        writer.table(&self.spans)?;
        writer.table(&self.origins)?;
        writer.table(&self.types)?;
        writer.table(&self.type_children)?;
        writer.table(&self.binders)?;
        writer.table(&self.patterns)?;
        writer.table(&self.pattern_children)?;
        writer.table(&self.arms)?;
        writer.table(&self.recursive_members)?;
        writer.table(&self.nodes)?;
        writer.table(&self.node_children)?;
        writer.table(&self.nominals)?;
        writer.table(&self.constructors)?;
        writer.table(&self.nominal_constructors)?;
        self.root.write(&mut writer)?;
        Ok(writer.bytes)
    }

    pub(crate) fn decode_bytes(
        bytes: &[u8],
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ImageFailure> {
        let mut reader = WireReader {
            bytes,
            offset: 0,
            work,
        };
        if reader.bytes(PRIVATE_MAGIC.len())? != PRIVATE_MAGIC {
            return Err(ImageFailure::UnsupportedFormat);
        }
        let image = Self {
            bytes: reader.byte_table()?,
            sources: reader.table()?,
            spans: reader.table()?,
            origins: reader.table()?,
            types: reader.table()?,
            type_children: reader.table()?,
            binders: reader.table()?,
            patterns: reader.table()?,
            pattern_children: reader.table()?,
            arms: reader.table()?,
            recursive_members: reader.table()?,
            nodes: reader.table()?,
            node_children: reader.table()?,
            nominals: reader.table()?,
            constructors: reader.table()?,
            nominal_constructors: reader.table()?,
            root: u32::read(&mut reader)?,
        };
        charge(reader.work, 1)?;
        if reader.offset != bytes.len() {
            return Err(ImageFailure::InvalidEncoding);
        }
        Ok(image)
    }
}

impl PureImage {
    /// Restores ordinary identities, builds unchecked Core, and validates it.
    /// No source loader, resolver, source checker or evaluator runs here.
    pub(crate) fn restore(
        &self,
        work: &mut TypeWorkBudget,
    ) -> Result<ValidatedProgram, ImageFailure> {
        let mut decoder = Decoder {
            image: self,
            sources: Vec::new(),
            modules: Vec::new(),
            work,
        };
        if self.sources.is_empty() {
            return Err(ImageFailure::InvalidRecord);
        }
        for source in &self.sources {
            charge(decoder.work, 1)?;
            let path = decoder.text(source.path)?;
            let text = decoder.text(source.text)?;
            let source = SourceFile::new_with_budget(path, text, decoder.work)
                .map_err(|_| ImageFailure::SourceAdmission)?;
            let module = ModuleId::from(source.id());
            push(&mut decoder.sources, source, decoder.work)?;
            push(&mut decoder.modules, module, decoder.work)?;
        }
        let registry = decoder.registry()?;
        let mut builder = CoreBuilder::with_registry(Arc::new(registry));
        builder.reserve_image_reconstruction_storage(
            self.nodes.len(),
            self.binders.len(),
            decoder.work,
        )?;
        let mut binder_ids = Vec::new();
        for binder in &self.binders {
            let id = decoder.binder_id(binder.id)?;
            push(&mut binder_ids, id, decoder.work)?;
        }
        builder.reserve_provider_draft_binders(&binder_ids, decoder.work)?;
        let mut nodes = Vec::new();
        charge(decoder.work, self.nodes.len())?;
        nodes
            .try_reserve_exact(self.nodes.len())
            .map_err(|_| ImageFailure::Resource)?;
        for (slot, record) in self.nodes.iter().enumerate() {
            charge(decoder.work, 1)?;
            let ty = decoder.ty(record.ty)?;
            let origin = decoder.origin(record.origin)?;
            let node = decoder.node(&mut builder, &nodes, record.tag, ty, origin)?;
            if nodes.len() != slot {
                return Err(ImageFailure::InvalidRecord);
            }
            nodes.push(node);
        }
        let root = *get(&nodes, self.root)?;
        let unchecked = builder.finish_provider_draft(root, decoder.work)?;
        let mut sources = Vec::new();
        let mut module_sources = Vec::new();
        for (module, source) in decoder.modules.iter().zip(&decoder.sources) {
            push(&mut sources, source, decoder.work)?;
            push(&mut module_sources, (*module, source.id()), decoder.work)?;
        }
        crate::core::validate::validate_modules_with_work(
            unchecked,
            &sources,
            &module_sources,
            decoder.work,
        )
        .map_err(ImageFailure::Validation)
    }
}

impl Decoder<'_> {
    fn text(&mut self, range: Slice) -> Result<String, ImageFailure> {
        let bytes = range.get(&self.image.bytes)?;
        // Charge both copying and the UTF-8 admission scan.
        charge(
            self.work,
            bytes.len().checked_mul(2).ok_or(ImageFailure::Resource)?,
        )?;
        let mut copy = Vec::new();
        copy.try_reserve_exact(bytes.len())
            .map_err(|_| ImageFailure::Resource)?;
        copy.extend_from_slice(bytes);
        String::from_utf8(copy).map_err(|_| ImageFailure::InvalidRecord)
    }

    fn nominal(&mut self, id: NominalId) -> Result<NominalTypeId, ImageFailure> {
        charge(self.work, 1)?;
        Ok(NominalTypeId::new(
            *get(&self.modules, id.module)?,
            id.local,
        ))
    }

    fn constructor(&mut self, id: ConstructorIdentity) -> Result<ConstructorId, ImageFailure> {
        Ok(ConstructorId::new(self.nominal(id.owner)?, id.local))
    }

    fn binder_id(&mut self, id: BinderIdentity) -> Result<BinderId, ImageFailure> {
        charge(self.work, 1)?;
        Ok(match id {
            BinderIdentity::Resolved { module, local } => BinderId::Resolved {
                module: *get(&self.modules, module)?,
                local,
            },
            BinderIdentity::Generated(local) => BinderId::Generated(local),
        })
    }

    fn span(&mut self, span: SpanRecord) -> Result<Span, ImageFailure> {
        charge(self.work, 1)?;
        get(&self.sources, span.source)?
            .span(ByteRange::new(span.start, span.end).map_err(|_| ImageFailure::InvalidRecord)?)
            .map_err(|_| ImageFailure::InvalidRecord)
    }

    fn origin(&mut self, root: u32) -> Result<OriginOwner, ImageFailure> {
        let mut frames = Vec::new();
        let mut current = root;
        let mut depth = 0;
        let mut origin = loop {
            charge(self.work, 1)?;
            if depth > crate::core::CORE_PAYLOAD_DEPTH_LIMIT {
                return Err(ImageFailure::Resource);
            }
            let record = *get(&self.image.origins, current)?;
            match record {
                OriginRecord::Source(span) => {
                    break OriginOwner(Some(Origin::Source(self.span(span)?)));
                }
                OriginRecord::Generated { cause, .. }
                | OriginRecord::Related { primary: cause, .. } => {
                    if cause >= current {
                        return Err(ImageFailure::InvalidRecord);
                    }
                    push(&mut frames, record, self.work)?;
                    current = cause;
                }
            }
            depth += 1;
        };
        while let Some(frame) = frames.pop() {
            let restored = match frame {
                OriginRecord::Generated { reason, .. } => Origin::Generated {
                    cause: Box::new(origin.take()),
                    reason,
                },
                OriginRecord::Related { related, .. } => {
                    let mut spans = Vec::new();
                    for record in related.get(&self.image.spans)? {
                        let span = self.span(*record)?;
                        push(&mut spans, span, self.work)?;
                    }
                    Origin::Related {
                        primary: Box::new(origin.take()),
                        related: spans,
                    }
                }
                OriginRecord::Source(_) => return Err(ImageFailure::InvalidRecord),
            };
            origin = OriginOwner(Some(restored));
        }
        Ok(origin)
    }

    fn ty(&mut self, root: u32) -> Result<IterativeTypeOwner, ImageFailure> {
        enum Task {
            Visit(u32, usize),
            Finish(TypeTag, usize),
        }
        let mut tasks = Vec::new();
        let mut results: Vec<IterativeTypeOwner> = Vec::new();
        push(&mut tasks, Task::Visit(root, 0), self.work)?;
        while let Some(task) = tasks.pop() {
            charge(self.work, 1)?;
            match task {
                Task::Visit(slot, depth) => {
                    if depth > crate::core::CORE_PAYLOAD_DEPTH_LIMIT {
                        return Err(ImageFailure::Resource);
                    }
                    let record = *get(&self.image.types, slot)?;
                    let children = record.children.get(&self.image.type_children)?;
                    let count = children.len();
                    if matches!(record.tag, TypeTag::Function) && count != 2
                        || matches!(record.tag, TypeTag::Tuple) && count < 2
                        || !matches!(record.tag, TypeTag::Function | TypeTag::Tuple) && count != 0
                    {
                        return Err(ImageFailure::InvalidRecord);
                    }
                    push(&mut tasks, Task::Finish(record.tag, count), self.work)?;
                    charge(self.work, count)?;
                    for child in children.iter().rev() {
                        if *child >= slot {
                            return Err(ImageFailure::InvalidRecord);
                        }
                        push(&mut tasks, Task::Visit(*child, depth + 1), self.work)?;
                    }
                }
                Task::Finish(tag, count) => {
                    let ty = match tag {
                        TypeTag::Int => Type::Int,
                        TypeTag::Bool => Type::Bool,
                        TypeTag::Unit => Type::Unit,
                        TypeTag::Bytes => Type::Bytes,
                        TypeTag::String => Type::String,
                        TypeTag::Nominal(id) => Type::Nominal(self.nominal(id)?),
                        TypeTag::Function => {
                            let result = results.pop().ok_or(ImageFailure::InvalidRecord)?;
                            let domain = results.pop().ok_or(ImageFailure::InvalidRecord)?;
                            Type::Function(
                                Box::new(domain.into_inner()),
                                Box::new(result.into_inner()),
                            )
                        }
                        TypeTag::Tuple => {
                            if results.len() < count {
                                return Err(ImageFailure::InvalidRecord);
                            }
                            charge(self.work, count)?;
                            let mut elements = Vec::new();
                            elements
                                .try_reserve_exact(count)
                                .map_err(|_| ImageFailure::Resource)?;
                            let start = results.len() - count;
                            for element in results.drain(start..) {
                                elements.push(element.into_inner());
                            }
                            Type::Tuple(elements.into_boxed_slice())
                        }
                    };
                    push(&mut results, IterativeTypeOwner::new(ty), self.work)?;
                }
            }
        }
        results
            .pop()
            .filter(|_| results.is_empty())
            .ok_or(ImageFailure::InvalidRecord)
    }

    fn binder(
        &mut self,
        builder: &mut CoreBuilder,
        slot: u32,
    ) -> Result<crate::core::TypedBinder, ImageFailure> {
        charge(self.work, 1)?;
        let record = *get(&self.image.binders, slot)?;
        let id = self.binder_id(record.id)?;
        let ty = self.ty(record.ty)?;
        let origin = self.origin(record.origin)?;
        builder
            .with_caller_type_work(self.work, |builder| {
                builder.resolved_binder(id, ty.into_inner(), origin.take())
            })
            .map_err(ImageFailure::from)
    }

    fn registry(&mut self) -> Result<ResolvedRegistry, ImageFailure> {
        let mut nominals = NominalBuffer(Vec::new());
        let mut constructors = ConstructorBuffer(Vec::new());
        for nominal in &self.image.nominals {
            charge(self.work, 1)?;
            let id = self.nominal(nominal.id)?;
            let spelling = self.text(nominal.spelling)?;
            let origin = self.origin(nominal.origin)?;
            let mut identities = Vec::new();
            for identity in nominal.constructors.get(&self.image.nominal_constructors)? {
                let identity = self.constructor(*identity)?;
                push(&mut identities, identity, self.work)?;
            }
            // Reserve before releasing the iterative origin owner.
            charge(self.work, 1)?;
            nominals
                .0
                .try_reserve(1)
                .map_err(|_| ImageFailure::Resource)?;
            nominals.0.push(ResolvedNominalType {
                id,
                declaration_kind: ResolvedNominalDeclarationKind::Data,
                spelling,
                constructors: identities.into_boxed_slice(),
                representation: None,
                representation_provenance: None,
                origin: origin.take(),
            });
        }
        for constructor in &self.image.constructors {
            charge(self.work, 1)?;
            let id = self.constructor(constructor.id)?;
            let spelling = self.text(constructor.spelling)?;
            let payload = constructor.payload.map(|ty| self.ty(ty)).transpose()?;
            let origin = self.origin(constructor.origin)?;
            charge(self.work, 1)?;
            constructors
                .0
                .try_reserve(1)
                .map_err(|_| ImageFailure::Resource)?;
            constructors.0.push(ResolvedConstructor {
                id,
                owner: id.owner(),
                spelling,
                payload: payload.map(IterativeTypeOwner::into_inner),
                origin: origin.take(),
            });
        }
        ResolvedRegistry::new_with_budget(nominals.into_vec(), constructors.into_vec(), self.work)
            .map_err(|_| ImageFailure::RegistryAdmission)
    }

    fn pattern(
        &mut self,
        builder: &mut CoreBuilder,
        root: u32,
    ) -> Result<PatternOwner, ImageFailure> {
        enum Task {
            Visit(u32, usize),
            Finish(PatternRecord, usize),
        }
        let mut tasks = Vec::new();
        let mut results: Vec<PatternOwner> = Vec::new();
        push(&mut tasks, Task::Visit(root, 0), self.work)?;
        while let Some(task) = tasks.pop() {
            charge(self.work, 1)?;
            match task {
                Task::Visit(slot, depth) => {
                    if depth > crate::core::CORE_PATTERN_DEPTH_LIMIT {
                        return Err(ImageFailure::Resource);
                    }
                    let record = *get(&self.image.patterns, slot)?;
                    let children = record.children.get(&self.image.pattern_children)?;
                    let count = children.len();
                    if matches!(record.tag, PatternTag::Tuple) && count < 2
                        || matches!(record.tag, PatternTag::Constructor(_)) && count > 1
                        || !matches!(record.tag, PatternTag::Tuple | PatternTag::Constructor(_))
                            && count != 0
                    {
                        return Err(ImageFailure::InvalidRecord);
                    }
                    push(&mut tasks, Task::Finish(record, count), self.work)?;
                    charge(self.work, count)?;
                    for child in children.iter().rev() {
                        if *child >= slot {
                            return Err(ImageFailure::InvalidRecord);
                        }
                        push(&mut tasks, Task::Visit(*child, depth + 1), self.work)?;
                    }
                }
                Task::Finish(record, count) => {
                    if results.len() < count {
                        return Err(ImageFailure::InvalidRecord);
                    }
                    let ty = self.ty(record.ty)?;
                    let origin = self.origin(record.origin)?;
                    let kind = match record.tag {
                        PatternTag::Wildcard => CorePatternKind::Wildcard,
                        PatternTag::Bool(value) => CorePatternKind::Boolean(value),
                        PatternTag::Unit => CorePatternKind::Unit,
                        PatternTag::Binder(slot) => {
                            CorePatternKind::Binder(self.binder(builder, slot)?)
                        }
                        PatternTag::Constructor(id) => {
                            let constructor = self.constructor(id)?;
                            let payload = if count == 0 {
                                None
                            } else {
                                Some(Box::new(
                                    results.pop().ok_or(ImageFailure::InvalidRecord)?.take(),
                                ))
                            };
                            CorePatternKind::Constructor {
                                constructor,
                                payload,
                            }
                        }
                        PatternTag::Tuple => {
                            charge(self.work, count)?;
                            let mut elements = Vec::new();
                            elements
                                .try_reserve_exact(count)
                                .map_err(|_| ImageFailure::Resource)?;
                            let start = results.len() - count;
                            for pattern in results.drain(start..) {
                                elements.push(pattern.take());
                            }
                            CorePatternKind::Tuple(elements.into_boxed_slice())
                        }
                    };
                    push(
                        &mut results,
                        PatternOwner(Some(CorePattern::new(ty.into_inner(), origin.take(), kind))),
                        self.work,
                    )?;
                }
            }
        }
        results
            .pop()
            .filter(|_| results.is_empty())
            .ok_or(ImageFailure::InvalidRecord)
    }

    fn node(
        &mut self,
        builder: &mut CoreBuilder,
        nodes: &[NodeId],
        record: NodeTag,
        ty: IterativeTypeOwner,
        origin: OriginOwner,
    ) -> Result<NodeId, ImageFailure> {
        let node = match record {
            NodeTag::Integer(value) => builder.with_caller_type_work(self.work, |builder| {
                builder.integer(Integer::from_i64(value), ty.into_inner(), origin.take())
            }),
            NodeTag::Bool(value) => builder.with_caller_type_work(self.work, |builder| {
                builder.boolean(value, ty.into_inner(), origin.take())
            }),
            NodeTag::Unit => builder.with_caller_type_work(self.work, |builder| {
                builder.unit(ty.into_inner(), origin.take())
            }),
            NodeTag::String(range) => {
                let bytes = range.get(&self.image.bytes)?;
                charge(self.work, bytes.len())?;
                let mut copy = Vec::new();
                copy.try_reserve_exact(bytes.len())
                    .map_err(|_| ImageFailure::Resource)?;
                copy.extend_from_slice(bytes);
                builder.with_caller_type_work(self.work, |builder| {
                    builder.string(copy, ty.into_inner(), origin.take())
                })
            }
            NodeTag::Constructor(id) => {
                let id = self.constructor(id)?;
                builder.with_caller_type_work(self.work, |builder| {
                    builder.constructor(id, ty.into_inner(), origin.take())
                })
            }
            NodeTag::Variable(id) => {
                let id = self.binder_id(id)?;
                builder.with_caller_type_work(self.work, |builder| {
                    builder.variable(id, ty.into_inner(), origin.take())
                })
            }
            NodeTag::Function { parameter, body } => {
                let body = *get(nodes, body)?;
                let parameter = self.binder(builder, parameter)?;
                builder.with_caller_type_work(self.work, |builder| {
                    builder.function(parameter, body, ty.into_inner(), origin.take())
                })
            }
            NodeTag::Bind {
                binder,
                initializer,
                body,
            } => {
                let initializer = *get(nodes, initializer)?;
                let body = *get(nodes, body)?;
                let binder = self.binder(builder, binder)?;
                builder.with_caller_type_work(self.work, |builder| {
                    builder.binding(binder, initializer, body, ty.into_inner(), origin.take())
                })
            }
            NodeTag::RecursiveBind { members, body } => {
                let body = *get(nodes, body)?;
                let records = members.get(&self.image.recursive_members)?;
                // Reserve the complete simultaneous group before reconstructing
                // binder payloads. TypedBinder's iterative Drop owns partial
                // cleanup if any later admission fails.
                charge(self.work, records.len())?;
                let mut restored = Vec::new();
                restored
                    .try_reserve_exact(records.len())
                    .map_err(|_| ImageFailure::Resource)?;
                for member in records {
                    charge(self.work, 1)?;
                    let initializer = *get(nodes, member.initializer)?;
                    let binder = self.binder(builder, member.binder)?;
                    restored.push((binder, initializer));
                }
                builder.with_caller_type_work(self.work, |builder| {
                    builder.recursive_binding(restored, body, ty.into_inner(), origin.take())
                })
            }
            NodeTag::Apply { function, argument } => {
                let function = *get(nodes, function)?;
                let argument = *get(nodes, argument)?;
                builder.with_caller_type_work(self.work, |builder| {
                    builder.application(function, argument, ty.into_inner(), origin.take())
                })
            }
            NodeTag::Primitive {
                operation,
                left,
                right,
            } => {
                let left = *get(nodes, left)?;
                let right = *get(nodes, right)?;
                builder.with_caller_type_work(self.work, |builder| {
                    builder.primitive(operation, left, right, ty.into_inner(), origin.take())
                })
            }
            NodeTag::Tuple(range) => {
                let mut elements = Vec::new();
                for child in range.get(&self.image.node_children)? {
                    let child = *get(nodes, *child)?;
                    push(&mut elements, child, self.work)?;
                }
                builder.with_caller_type_work(self.work, |builder| {
                    builder.tuple(elements, ty.into_inner(), origin.take())
                })
            }
            NodeTag::Match { scrutinee, arms } => {
                let scrutinee = *get(nodes, scrutinee)?;
                let mut restored_arms = Vec::new();
                for arm in arms.get(&self.image.arms)? {
                    charge(self.work, 1)?;
                    let body = *get(nodes, arm.body)?;
                    let pattern = self.pattern(builder, arm.pattern)?;
                    let arm_origin = self.origin(arm.origin)?;
                    push(
                        &mut restored_arms,
                        CoreMatchArm::new(pattern.take(), body, arm_origin.take()),
                        self.work,
                    )?;
                }
                builder.with_caller_type_work(self.work, |builder| {
                    builder.match_expression(
                        scrutinee,
                        restored_arms,
                        ty.into_inner(),
                        origin.take(),
                    )
                })
            }
        };
        node.map_err(ImageFailure::from)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::driver::{RunConfiguration, compile_path};
    use crate::module::ModuleRoots;
    use std::{
        fs,
        path::PathBuf,
        sync::atomic::{AtomicU64, Ordering},
    };

    static IDS: AtomicU64 = AtomicU64::new(0);

    struct SourceTree(PathBuf);
    impl SourceTree {
        fn new() -> Self {
            loop {
                let id = IDS.fetch_add(1, Ordering::Relaxed);
                let path = std::env::temp_dir().join(format!(
                    "ash-private-pure-image-{}-{id}",
                    std::process::id()
                ));
                match fs::create_dir(&path) {
                    Ok(()) => return Self(path),
                    Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                    Err(error) => panic!("image source fixture: {error}"),
                }
            }
        }
        fn write(&self, name: &str, text: &str) {
            fs::write(self.0.join(name), text).unwrap();
        }
        fn configuration(&self) -> RunConfiguration {
            RunConfiguration {
                entry: self.0.join("entry.ash"),
                roots: ModuleRoots::empty(),
            }
        }
    }
    impl Drop for SourceTree {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn recursive_groups_preserve_mutual_scope_and_definition_environment() {
        for (source, expected) in [
            (
                concat!(
                    "type Counter =\nStop\n| More(Counter)\n",
                    "countdown : Counter -> Int\n",
                    "countdown Stop = 42\n",
                    "countdown (More(rest)) = advance rest\n",
                    "advance : Counter -> Int\n",
                    "advance value = countdown value\n",
                    "main : Unit -> Int\n",
                    "main () = countdown(More(More(Stop)))\n",
                ),
                "42",
            ),
            (
                concat!(
                    "main : Unit -> Int\n",
                    "main () = {\n",
                    "    let captured = 42\n",
                    "    let rec read : Unit -> Int = fn(ignored) {\n",
                    "        captured\n",
                    "    }\n",
                    "    let caller : Unit -> Int = fn(ignored) {\n",
                    "        let captured = 0\n",
                    "        read ()\n",
                    "    }\n",
                    "    caller ()\n",
                    "}\n",
                ),
                "42",
            ),
            (
                concat!(
                    "type Stream = Next(Int, Stream)\n",
                    "main : Unit -> Stream\n",
                    "main () = {\n",
                    "    let rec ones : Stream = Next(1, ones)\n",
                    "    ones\n",
                    "}\n",
                ),
                "Next(1, <cycle>)",
            ),
        ] {
            let tree = SourceTree::new();
            tree.write("entry.ash", source);
            let compiled = compile_path(tree.configuration()).expect("recursive source compiles");
            let (program, provenance) = compiled.pure_build_input().unwrap();
            let mut work = TypeWorkBudget::default();
            let image = encode(program, provenance, &mut work).expect("recursive image encodes");
            let bytes = image.encode_bytes(&mut work).unwrap();
            drop(image);
            drop(compiled);
            drop(tree);
            let restored = PureImage::decode_bytes(&bytes, &mut work)
                .unwrap()
                .restore(&mut work)
                .expect("recursive image independently validates");
            let evaluation = crate::eval::evaluate(&restored).unwrap();
            assert_eq!(evaluation.value.to_string(), expected);
        }
    }

    #[test]
    fn imported_nominal_image_restores_independently_after_original_sources_disappear() {
        let tree = SourceTree::new();
        tree.write("dependency.ash", "pub type Count = Count(Int)\n");
        tree.write(
            "entry.ash",
            concat!(
                "import dependency as Dep\n",
                "extract : Dep.Count -> Int\n",
                "extract value = match value {\n",
                "    Dep.Count(payload) => payload + 1\n",
                "}\n",
                "main : Unit -> Int\n",
                "main () = extract (Dep.Count(41))\n",
            ),
        );
        let compiled = compile_path(tree.configuration()).expect("ordinary source Core compiles");
        let (program, provenance) = compiled
            .pure_build_input()
            .expect("retained Pure build input");
        let original_module = program.registry().nominals()[0].id.module();
        let original_work = *compiled.compilation_work();
        let mut encode_work = TypeWorkBudget::default();
        let image = encode(program, provenance, &mut encode_work).expect("flat image prepares");
        let encoded_cost = encode_work.used();
        assert!(
            encode(
                program,
                provenance,
                &mut TypeWorkBudget::with_limit(encoded_cost)
            )
            .is_ok()
        );
        assert!(matches!(
            encode(
                program,
                provenance,
                &mut TypeWorkBudget::with_limit(encoded_cost - 1)
            ),
            Err(ImageFailure::Resource),
        ));
        assert_eq!(compiled.compilation_work(), &original_work);
        let mut wire_work = TypeWorkBudget::default();
        let bytes = image
            .encode_bytes(&mut wire_work)
            .expect("private flat bytes encode");
        assert_eq!(wire_work.used(), bytes.len());
        assert_eq!(
            image
                .encode_bytes(&mut TypeWorkBudget::with_limit(wire_work.used()))
                .unwrap(),
            bytes
        );
        assert!(matches!(
            image.encode_bytes(&mut TypeWorkBudget::with_limit(wire_work.used() - 1)),
            Err(ImageFailure::Resource)
        ));
        drop(image);
        let mut decode_work = TypeWorkBudget::default();
        let image = PureImage::decode_bytes(&bytes, &mut decode_work)
            .expect("matching private bytes decode");
        assert_eq!(
            image.encode_bytes(&mut TypeWorkBudget::default()).unwrap(),
            bytes
        );
        assert!(
            PureImage::decode_bytes(&bytes, &mut TypeWorkBudget::with_limit(decode_work.used()))
                .is_ok()
        );
        assert!(matches!(
            PureImage::decode_bytes(
                &bytes,
                &mut TypeWorkBudget::with_limit(decode_work.used() - 1)
            ),
            Err(ImageFailure::Resource)
        ));
        let mut wrong_format = bytes.clone();
        wrong_format[PRIVATE_MAGIC.len() - 1] ^= 1;
        assert!(matches!(
            PureImage::decode_bytes(&wrong_format, &mut TypeWorkBudget::default()),
            Err(ImageFailure::UnsupportedFormat)
        ));
        let mut trailing = bytes.clone();
        trailing.push(0);
        assert!(matches!(
            PureImage::decode_bytes(&trailing, &mut TypeWorkBudget::default()),
            Err(ImageFailure::InvalidEncoding)
        ));
        assert!(matches!(
            PureImage::decode_bytes(&bytes[..bytes.len() - 1], &mut TypeWorkBudget::default()),
            Err(ImageFailure::InvalidEncoding)
        ));
        fs::remove_dir_all(&tree.0).unwrap();
        drop(compiled);
        let mut restored_cost = None;
        for _ in 0..2 {
            let mut restore_work =
                restored_cost.map_or_else(TypeWorkBudget::default, TypeWorkBudget::with_limit);
            let restored = image
                .restore(&mut restore_work)
                .expect("independent reconstruction validates");
            restored_cost = Some(restore_work.used());
            assert_ne!(
                restored.registry().nominals()[0].id.module(),
                original_module
            );
            assert_eq!(
                crate::eval::evaluate(&restored).unwrap().value.to_string(),
                "42"
            );
        }
        assert!(
            image
                .restore(&mut TypeWorkBudget::with_limit(restored_cost.unwrap() - 1))
                .is_err()
        );
        let cost = restored_cost.unwrap();
        let mut prefixed_work = TypeWorkBudget::with_limit(cost + 37);
        prefixed_work.charge(37).unwrap();
        image.restore(&mut prefixed_work).unwrap();
        assert_eq!(prefixed_work.used(), cost + 37);
        // A failed builder admission must also return its completed charges.
        // Reusing that same ledger cannot open another construction allowance.
        let mut refused_work = TypeWorkBudget::with_limit(2);
        refused_work.charge(1).unwrap();
        let mut builder = CoreBuilder::new();
        let source = SourceFile::new("refused-reconstruction.ash", "()").unwrap();
        let span = source.span(ByteRange::new(0, 2).unwrap()).unwrap();
        assert!(matches!(
            builder.with_caller_type_work(&mut refused_work, |builder| {
                builder.resolved_binder(BinderId::Generated(0), Type::Unit, Origin::Source(span))
            }),
            Err(crate::core::BuildError::UnreservedResolvedBinder)
        ));
        assert_eq!(refused_work.used(), 2);
        assert!(matches!(
            builder.with_caller_type_work(&mut refused_work, |builder| {
                builder.unit(Type::Unit, Origin::Source(span))
            }),
            Err(crate::core::BuildError::TypeWorkExceeded)
        ));
        assert_eq!(refused_work.used(), 2);
        assert!(original_work.source_checking.unwrap().completed);

        let mut work = TypeWorkBudget::with_limit(0);
        assert!(matches!(
            image.restore(&mut work),
            Err(ImageFailure::Resource)
        ));
        // Malformed structural claims reach the same independent validator;
        // no image API can construct a ValidatedProgram directly.
        let mut corrupt = image;
        let literal = corrupt
            .nodes
            .iter_mut()
            .find(|record| matches!(record.tag, NodeTag::Integer(_)))
            .unwrap();
        literal.ty = push(
            &mut corrupt.types,
            TypeRecord {
                tag: TypeTag::Bool,
                children: Slice { start: 0, len: 0 },
            },
            &mut TypeWorkBudget::default(),
        )
        .unwrap();
        assert!(matches!(
            corrupt.restore(&mut TypeWorkBudget::default()),
            Err(ImageFailure::Validation(_))
        ));
    }

    #[test]
    fn unsupported_registry_facts_are_refused_instead_of_dropped() {
        let tree = SourceTree::new();
        tree.write(
            "entry.ash",
            "type Boxed<A> = Boxed(A)\nmain : Unit -> Int\nmain () = 42\n",
        );
        let compiled =
            compile_path(tree.configuration()).expect("unused generic declaration is valid source");
        let (program, provenance) = compiled.pure_build_input().unwrap();
        assert!(matches!(
            encode(program, provenance, &mut TypeWorkBudget::default()),
            Err(ImageFailure::Unsupported(Unsupported::RegistryMetadata))
        ));
    }
}
